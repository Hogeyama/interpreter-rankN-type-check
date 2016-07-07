
module TypeCheck.TcMonad (
  -- The monad type constructor
  Tc(..),
  -- Environment manipulation
  getValEnv, getTyEnv,
  runTc, evalTc, lift, liftEither, check,
  extendTyEnv, extendTyEnvList, lookupVar,
  extendValEnv, extendValEnvList,
  localValEnv,
  getEnvTypes, getFreeTyVars, getMetaTyVars,
  -- Types and unification
  newTyVar,
  instantiate, skolemise, zonkType, quantify,
  unify, unifyFun, unifyList, unifyPair,
  -- Ref cells
  newTcRef, readTcRef, writeTcRef
  ) where

import Syntax
import qualified Data.Map as M
import Data.IORef
import Data.List ((\\), foldl')
import Control.Monad (ap)


--- ---------------------- ---
--- Monad & base functions ---
--- ---------------------- ---

data TcEnv =
  TcEnv { uniqs :: IORef Uniq,
          tyEnv :: M.Map Name Sigma,
          valEnv :: M.Map Name Value }

newtype Tc a = Tc (TcEnv -> IO (Either Error a))

unTc :: Tc a -> (TcEnv -> IO (Either Error a))
unTc (Tc a) = a

instance Functor Tc where
  fmap f m = Tc $ \env -> do
    r1 <- unTc m env
    case r1 of
        Right x  -> return $ Right (f x)
        Left err -> return $ Left err
instance Applicative Tc where
  pure x = Tc $ \_ -> return (Right x)
  (<*>) = ap
instance Monad Tc where
  return = pure
  fail err = Tc $ \_ -> return (Left (Failure err))
  m >>= k  = Tc $ \env -> do
    r1 <- unTc m env
    case r1 of
      Left err -> return (Left err)
      Right v -> unTc (k v) env

lift :: IO a -> Tc a
lift st = Tc $ \_ -> Right <$> st

liftEither :: Either Error a -> Tc a
liftEither (Right x) = Tc $ \env -> return $ Right x
liftEither (Left e)  = Tc $ \env -> return $ Left e

check :: Bool -> String -> Tc ()
check True _ = return ()
check False s = fail s

runTc :: ValEnv -> TyEnv -> Tc a -> IO (Either Error a)
runTc valenv tyenv (Tc tc) = do
  ref <- newIORef 0
  let env = TcEnv { uniqs = ref,
                    tyEnv = tyenv,
                    valEnv = valenv }
  tc env

evalTc :: ValEnv -> TyEnv -> Tc a -> IO (Either Error a)
evalTc = runTc

newTcRef :: a -> Tc (IORef a)
newTcRef v = lift (newIORef v)

readTcRef :: IORef a -> Tc a
readTcRef r = lift (readIORef r)

writeTcRef :: IORef a -> a -> Tc ()
writeTcRef r v = lift (writeIORef r v)

--- ----------- ---
--- Environment ---
--- ----------- ---

extendTyEnv :: Name -> Sigma -> Tc a -> Tc a
extendTyEnv var ty (Tc m) = Tc (\env -> m (extend env))
  where
    extend env = env { tyEnv = M.insert var ty (tyEnv env) }

extendTyEnvList :: [(Name, Sigma)] -> Tc a -> Tc a
extendTyEnvList binds (Tc m) = Tc $ \env -> m (extend env)
  where
    f env (var, ty) = M.insert var ty env
    extend env = env { tyEnv = foldl' f (tyEnv env) binds }

extendValEnv :: Name -> Value -> Tc a -> Tc a
extendValEnv var val (Tc m) = Tc (\env -> m (extend env))
  where
    extend env = env { valEnv = M.insert var val (valEnv env) }

extendValEnvList :: [(Name, Value)] -> Tc a -> Tc a
extendValEnvList binds (Tc m) = Tc $ \env -> m (extend env)
  where
    f env (var, ty) = M.insert var ty env
    extend env = env { valEnv = foldl' f (valEnv env) binds }

localValEnv :: ValEnv -> Tc a -> Tc a
localValEnv tmpValenv (Tc m) = Tc $ \env -> m (local env)
  where
    local env = env { valEnv = tmpValenv }

getValEnv :: Tc ValEnv
getValEnv = Tc (\env -> return (Right (valEnv env)))

getTyEnv :: Tc TyEnv
getTyEnv = Tc (\env -> return (Right (tyEnv env)))


lookupVar :: Name -> Tc Sigma -- May fail
lookupVar n = do
  env <- getTyEnv
  case M.lookup n env of
    Just ty -> return ty
    Nothing -> fail ("Not in scope: '" ++ show n ++ "'")


--- ------ ---
--- MetaTv ---
--- ------ ---


newTyVar :: Tc Tau
newTyVar = do tv <- newMetaTyVar
              return (MetaTv tv)

newMetaTyVar :: Tc MetaTv
newMetaTyVar = do uniq <- newUnique
                  tref <- newTcRef Nothing
                  return (Meta uniq tref)

newSkolemTyVar :: TyVar -> Tc TyVar
newSkolemTyVar tv = do uniq <- newUnique
                       return (SkolemTv (tyVarName tv) uniq)

readTv :: MetaTv -> Tc (Maybe Tau)
readTv (Meta _ ref) = readTcRef ref

writeTv :: MetaTv -> Tau -> Tc ()
writeTv (Meta _ ref) ty = writeTcRef ref (Just ty)

newUnique :: Tc Uniq
newUnique = Tc $ \(TcEnv {uniqs = ref}) -> do
  uniq <- readIORef ref
  modifyIORef ref (+1)
  return (Right uniq)


--- ------------- ---
--- Instantiation ---
--- ------------- ---

-- Instantiate the topmost for-alls of the argument type
-- with flexible type variables
instantiate :: Sigma -> Tc Rho
instantiate (Forall tvs ty) = do
  tvs' <- mapM (\_ -> newMetaTyVar) tvs
  return (substTy tvs (map MetaTv tvs') ty)
instantiate ty =
  return ty

-- pr(σ) = ∀ a.ρ なる a,ρを求める
-- Performs deep skolemisation, retuning the
-- skolem constants and the skolemised type
skolemise :: Sigma -> Tc ([TyVar], Rho)
-- Rule PRPOLY
skolemise (Forall tvs ty) = do
  sks1 <- mapM newSkolemTyVar tvs
  (sks2, ty') <- skolemise (substTy tvs (map TyVar sks1) ty)
  return (sks1 ++ sks2, ty')
-- Rule PRFUN
skolemise (Fun arg_ty res_ty) = do
  (sks, res_ty') <- skolemise res_ty
  return (sks, Fun arg_ty res_ty')
-- listとpairに拡張
skolemise (TyList ty) = do
  (sks, ty') <- skolemise ty
  return (sks, TyList ty')
skolemise (TyPair ty1 ty2) = do
  (sks1, ty1') <- skolemise ty1
  (sks2, ty2') <- skolemise ty2
  return (sks1++sks2, TyPair ty1' ty2')
-- Rule PRMONO
skolemise ty =
  return ([], ty)

--- -------------- ---
--- Quantification ---
--- -------------- ---

-- Quantify over the specified type variables (all flexible)
quantify :: [MetaTv] -> Rho -> Tc Sigma
quantify tvs ty = do
  mapM_ bind (tvs `zip` new_bndrs) -- 'bind' is just a cunning way
  ty' <- zonkType ty               -- of doing the substitution
  return $ Forall new_bndrs ty'
  where
    used_bndrs = tyVarBndrs ty -- Avoid quantified type variables in use
    new_bndrs = take (length tvs) (allBinders \\ used_bndrs)
    bind (tv, name) = writeTv tv (TyVar name)

allBinders :: [TyVar] -- a,b,..z, a1, b1,... z1, a2, b2,...
allBinders =
  [ BoundTv [x] | x <- ['a'..'z'] ] ++
  [ BoundTv (x : show i) | i <- [1 :: Integer ..], x <- ['a'..'z']]


--- ------------ ---
--- Getting ftvs ---
--- ------------ ---


-- Get the types mentioned in the environment
getEnvTypes :: Tc [Type]
getEnvTypes = do
  env <- getTyEnv;
  return (M.elems env)

-- This function takes account of zonking, and returns a set
-- (no duplicates) of unbound meta-type variables
getMetaTyVars :: [Type] -> Tc [MetaTv]
getMetaTyVars tys = do
  tys' <- mapM zonkType tys
  return $ metaTvs tys'

-- This function takes account of zonking, and returns a set
-- (no duplicates) of free type variables
getFreeTyVars :: [Type] -> Tc [TyVar]
getFreeTyVars tys = do
  tys' <- mapM zonkType tys
  return $ freeTyVars tys'

--- ------- ---
--- Zonking ---
--- ------- ---

zonkType :: Type -> Tc Type
zonkType (Forall ns ty) = do
  ty' <- zonkType ty
  return (Forall ns ty')
zonkType (Fun arg res) = do
  arg' <- zonkType arg
  res' <- zonkType res
  return (Fun arg' res')

zonkType TyInt  = return TyInt
zonkType TyBool = return TyBool
zonkType (TyVar n) = return (TyVar n)

zonkType (MetaTv tv) = do -- A mutable type variable
  mb_ty <- readTv tv
  case mb_ty of
    Nothing -> return (MetaTv tv)
    Just ty -> do ty' <- zonkType ty
                  writeTv tv ty' -- "Short out" multiple hops
                  return ty'
zonkType (TyList ty) = do
  ty' <- zonkType ty
  return (TyList ty')

zonkType (TyPair ty1 ty2) = do
  ty1' <- zonkType ty1
  ty2' <- zonkType ty2
  return (TyPair ty1' ty2')

--- ----------- ---
--- Unification ---
--- ----------- ---

unify :: Tau -> Tau -> Tc ()
unify ty1 ty2
  | badType ty1 || badType ty2 -- Compiler error
    = fail ("Panic! Unexpected types in unification: " ++ show ty1 ++ "," ++ show ty2)

unify (TyVar tv1) (TyVar tv2)   | tv1 == tv2 = return ()
unify (MetaTv tv1) (MetaTv tv2) | tv1 == tv2 = return ()
unify (MetaTv tv) ty = unifyVar tv ty
unify ty (MetaTv tv) = unifyVar tv ty

unify (Fun arg1 res1) (Fun arg2 res2) = do
  unify arg1 arg2
  unify res1 res2

unify TyInt  TyInt  = return ()
unify TyBool TyBool = return ()

unify sig1@(Forall tvs1 _) (Forall tvs2 ty2) -- Sigmaに拡張できる
  | length tvs1 == length tvs2 = do
      (sks1,ty1') <- skolemise sig1
      let ty2' = substTy tvs2 (map TyVar sks1) ty2
      unify ty1' ty2'

--unify (Forall [] ty1) ty2 =
--  unify ty1 ty2
--unify ty1 (Forall [] ty2) =
--  unify ty1 ty2

unify (TyList ty1) (TyList ty2) =
  unify ty1 ty2

unify (TyPair ty11 ty12) (TyPair ty21 ty22) = do
  unify ty11 ty21
  unify ty12 ty22

unify ty1 ty2 =
  fail ("Cannot unify types: " ++ show ty1 ++ "," ++ show ty2)

-- Invariant: tv1 is a flexible type variable
-- Check whether tv1 is boundPractical type inference for arbitrary-rank types
unifyVar :: MetaTv -> Tau -> Tc ()
unifyVar tv1 ty2 = do
  mb_ty1 <- readTv tv1
  case mb_ty1 of
    Just ty1 -> unify ty1 ty2
    Nothing -> unifyUnboundVar tv1 ty2

-- Invariant: the flexible type variable tv1 is not bound
unifyUnboundVar :: MetaTv -> Tau -> Tc ()

-- We know that tv1 /= tv2 (else the top case in unify would catch it)
unifyUnboundVar tv1 ty2@(MetaTv tv2) = do
  mb_ty2 <- readTv tv2
  case mb_ty2 of
    Just ty2' -> unify (MetaTv tv1) ty2'
    Nothing -> writeTv tv1 ty2

unifyUnboundVar tv1 ty2 = do
  tvs2 <- getMetaTyVars [ty2]
  if tv1 `elem` tvs2
     then occursCheckErr tv1 ty2
     else writeTv tv1 ty2


--(arg,res) <- unifyFun fun
--unifies 'fun' with '(arg -> res)'
--tcRhoの普遍条件によりresはRho
unifyFun :: Rho -> Tc (Sigma, Rho)
unifyFun (Fun arg res) = return (arg,res)
unifyFun tau = do
  arg_ty <- newTyVar
  res_ty <- newTyVar
  unify tau (Fun arg_ty res_ty)
  return (arg_ty, res_ty)

unifyList :: Rho -> Tc Sigma
unifyList (TyList tau) = return tau
unifyList tau = do
  ty <- newTyVar
  unify tau (TyList ty)
  return ty

unifyPair :: Rho -> Tc (Sigma, Sigma)
unifyPair (TyPair tau1 tau2) = return (tau1,tau2)
unifyPair tau = do
  tau1 <- newTyVar
  tau2 <- newTyVar
  unify tau (TyPair tau1 tau2)
  return (tau1,tau2)

-- Raise an occurs-check error
occursCheckErr :: MetaTv -> Tau -> Tc ()
occursCheckErr tv ty =
  fail $ "Occurs check for " ++ show tv ++ " in " ++ show ty

-- Tells which types should never be encountered during unification
badType :: Tau -> Bool
badType (TyVar (BoundTv _)) = True
badType _ = False



