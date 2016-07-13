
module TypeCheck.TcTerm where

import Syntax
import TypeCheck.TcMonad

import Data.IORef
import Data.List((\\))

--- --------------------- ---
--- The top-level wrapper ---
--- --------------------- ---

inferExpr :: Expr -> Tc Sigma
inferExpr e = do
  ty <- inferSigma e
  zonkType ty

--- ----------------- ---
--- The expected type ---
--- ----------------- ---

data Expected a = Infer (IORef a) | Check a

--- ----- ---
--- TcRho ---
--- ----- ---

checkRho :: Expr -> Type -> Tc ()
checkRho expr ty = tcRho expr (Check ty)

inferRho :: Expr -> Tc Rho
inferRho expr = do
  ref <- newTcRef (error "inferRho: empty result")
  tcRho expr (Infer ref)
  readTcRef ref

-- |-δ t:ρ
-- Invariant:
-- if the second argument is (Check rho),
-- then rho is in weak-prenex form
-- なぜなら(Check rho)で最初に呼び出されるのはEFunAnnot, EAnnotのところのみで
-- その時点でweak-prenex formに変換されるからである.
-- EAdd, EEq, EIfなどを追加してもこの性質は保たれる.
--
-- これが崩れている. (Check
tcRho :: Expr -> Expected Rho -> Tc ()
tcRho (EConstInt _)  exp_ty = instSigma TyInt  exp_ty
tcRho (EConstBool _) exp_ty = instSigma TyBool exp_ty
tcRho (EVar v) exp_ty = do
  v_sigma <- lookupVar v
  instSigma v_sigma exp_ty
tcRho (EApp fun arg) exp_ty = do
  fun_ty <- inferRho fun
  (arg_ty, res_ty) <- unifyFun fun_ty
  checkSigma arg arg_ty `catchE` \_ -> do
    sigma <- inferSigma arg
    fail $ "Couldn't match expected type `" ++ show arg_ty ++
           "` with acutual type `" ++ show sigma ++ "`"
  instSigma res_ty exp_ty
tcRho (EFun var body) (Check exp_ty) = do
  (var_ty, body_ty) <- unifyFun exp_ty
  extendTyEnv var var_ty (checkRho body body_ty)
tcRho (EFun var body) (Infer ref) = do
  var_ty <- newTyVar
  body_ty <- extendTyEnv var var_ty (inferRho body)
  writeTcRef ref (Fun var_ty body_ty)
tcRho (EFunAnnot var var_ty body) (Check exp_ty) = do
  (arg_ty, body_ty) <- unifyFun exp_ty
  subsCheck arg_ty var_ty
  extendTyEnv var var_ty (checkRho body body_ty)
tcRho (EFunAnnot var var_ty body) (Infer ref) = do
  body_ty <- extendTyEnv var var_ty (inferRho body)
  writeTcRef ref (Fun var_ty body_ty)
tcRho (ELet var rhs body) exp_ty = do
  var_ty <- inferSigma rhs
  extendTyEnv var var_ty (tcRho body exp_ty)
tcRho (EAnnot body ann_ty) exp_ty = do
  checkSigma body ann_ty
  instSigma ann_ty exp_ty

tcRho (EAdd e1 e2) exp_ty = do
  tcRho e1 (Check TyInt)
  tcRho e2 (Check TyInt)
  instSigma TyInt  exp_ty
tcRho (ESub e1 e2) exp_ty = do
  tcRho e1 (Check TyInt)
  tcRho e2 (Check TyInt)
  instSigma TyInt  exp_ty
tcRho (EMul e1 e2) exp_ty = do
  tcRho e1 (Check TyInt)
  tcRho e2 (Check TyInt)
  instSigma TyInt  exp_ty
tcRho (EDiv e1 e2) exp_ty = do
  tcRho e1 (Check TyInt)
  tcRho e2 (Check TyInt)
  instSigma TyInt  exp_ty

tcRho (ELt e1 e2) exp_ty = do
  ty <- newTyVar
  tcRho e1 (Check ty)
  tcRho e2 (Check ty)
  instSigma TyBool exp_ty
tcRho (EEq e1 e2) exp_ty = do
  ty <- newTyVar
  tcRho e1 (Check ty)
  tcRho e2 (Check ty)
  instSigma TyBool exp_ty

--p55 (1)の方法
tcRho (EIf e1 e2 e3) exp_ty = do --TODO
  tcRho e1 (Check TyBool)
  exp_ty' <- zapToMonoType exp_ty
  tcRho e2 exp_ty'
  tcRho e3 exp_ty'
--p55 (2)の方法
--tcRho (EIf e1 e2 e3) (Check exp_ty) = do
--  tcRho e1 (Check TyBool)
--  tcRho e2 (Check exp_ty)
--  tcRho e3 (Check exp_ty)
--tcRho (EIf e1 e2 e3) (Infer ref) = do
--  tcRho e1 (Check TyBool)
--  ty2 <- inferRho e2
--  ty3 <- inferRho e3
--  unify ty2 ty3
--  writeTcRef ref ty2

tcRho ENil (Check exp_ty) = do
  check (isTau exp_ty) "Impredicative type is not allowed"
  unifyList exp_ty
  return ()
tcRho ENil (Infer ref) = do
  ty <- newTyVar
  writeTcRef ref (TyList ty)
tcRho (ECons e1 e2) (Check exp_ty) = do
  ty <- unifyList exp_ty
  checkRho e1 ty
  checkRho e2 (TyList ty)
tcRho (ECons e1 e2) (Infer ref) = do
  ty <- newTyVar
  checkRho e1 ty
  checkRho e2 (TyList ty)
  writeTcRef ref (TyList ty)

tcRho (EPair e1 e2) (Check exp_ty) = do
  (ty1, ty2) <- unifyPair exp_ty
  checkSigma e1 ty1
  checkSigma e2 ty2
tcRho (EPair e1 e2) (Infer ref) = do
  ty1 <- inferRho e1
  ty2 <- inferRho e2
  writeTcRef ref (TyPair ty1 ty2)

-- EMatch e [(pat, body)] = EPLam pat body `EApp` e
tcRho (EMatch e l) (Infer ref) = do
  fun_tys <- mapM inferPLamRho l
  (arg_tys, res_ty:res_tys)<- unzip <$> mapM unifyFun fun_tys
  mapM_ (checkSigma e) arg_tys
  ret <- instantiate res_ty -- instSigma (Infer)の代わり(こっちのが短いので)
  mapM_ (`instSigma` Check ret) res_tys
  writeTcRef ref ret
tcRho (EMatch e l) (Check exp_ty) = do
  fun_tys <- mapM inferPLamRho l
  (arg_tys, res_tys)<- unzip <$> mapM unifyFun fun_tys
  mapM_ (checkSigma e) arg_tys
  mapM_ (`instSigma` (Check exp_ty)) res_tys
  return ()

--これだけ特別視するのは汚いのでELetRecAnnotを作るべき
tcRho (ELetRec f (EAnnot e1 sigma) e2) exp_ty = do
  checkSigma (EFix (EFun f e1)) sigma
  extendTyEnv f sigma (tcRho e2 exp_ty)
tcRho (ELetRec f e1 e2) exp_ty = do
  sigma <- inferSigma (EFix (EFun f e1))
  extendTyEnv f sigma (tcRho e2 exp_ty)

tcRho (EFix e1) (Infer ref) = do
  e1_ty <- inferRho e1
  e_ty <- unifyFix e1_ty
  writeTcRef ref e_ty
tcRho (EFix e1) (Check exp_ty) = do
  tcRho e1 (Check $ Fun exp_ty exp_ty)

tcPLamRho :: (Pattern, Expr) -> Expected Rho -> Tc ()
tcPLamRho (pat, body) (Infer ref) = do
  (binds, pat_ty) <- inferPat pat
  body_ty <- extendTyEnvList binds (inferRho body)
  writeTcRef ref (Fun pat_ty body_ty)
tcPLamRho (pat, body) (Check ty) = do
  (arg_ty, res_ty) <- unifyFun ty
  binds <- checkPat pat arg_ty
  extendTyEnvList binds (checkRho body res_ty)

inferPLamRho :: (Pattern, Expr) -> Tc Rho
inferPLamRho (pat, body) = do
  ref <- newTcRef (error "inferPLamRho: empty result")
  tcPLamRho (pat,body) (Infer ref)
  ret <- readTcRef ref
  return ret
checkPatRho :: (Pattern, Expr) -> Rho -> Tc ()
checkPatRho (pat,body) exp_ty = tcPLamRho (pat,body) (Check exp_ty)

zapToMonoType :: Expected Rho -> Tc (Expected Rho)
zapToMonoType (Check ty) = return (Check ty)
zapToMonoType (Infer ref) = do
  ty <- newTyVar
  writeTcRef ref ty
  return (Check ty)

--- ------------- ---
--- Pattern Match ---
--- ------------- ---

tcPat :: Pattern -> Expected Sigma -> Tc [(Name,Sigma)]
tcPat PWild exp_ty = return []

tcPat (PInt _) exp_ty = do
  instSigma TyInt exp_ty
  return []
tcPat (PBool _) exp_ty = do
  instSigma TyBool exp_ty
  return []

tcPat (PVar v) (Check ty) =
  return [(v, ty)]
tcPat (PVar v) (Infer ref) = do
  ty <- newTyVar
  writeTcRef ref ty
  return [(v,ty)]

tcPat (PPair p1 p2) exp_ty = do
  ty1 <- newTyVar
  ty2 <- newTyVar
  let res_ty = TyPair ty1 ty2
  env1 <- tcPat p1 (Check ty1)
  env2 <- tcPat p2 (Check ty2)
  instPatSigma res_ty exp_ty
  return $ env1++env2

tcPat PNil exp_ty = do
  ty <- TyList <$> newTyVar
  instPatSigma ty exp_ty
  return []

tcPat (PCons p1 p2) exp_ty = do
  ty1 <- newTyVar
  let res_ty = TyList ty1
  env1 <- tcPat p1 (Check ty1)
  env2 <- tcPat p2 (Check (TyList ty1))
  instPatSigma res_ty exp_ty
  return $ env1++env2

instPatSigma :: Sigma -> Expected Sigma -> Tc ()
instPatSigma pat_ty (Infer ref) = writeTcRef ref pat_ty
instPatSigma pat_ty (Check exp_ty) = subsCheck exp_ty pat_ty

inferPat :: Pattern -> Tc ([(Name,Sigma)], Sigma)
inferPat pat = do
  ty <- newTyVar
  ref <- newTcRef ty
  binds <- tcPat pat (Infer ref)
  ret <- readTcRef ref
  return (binds, ret)

checkPat :: Pattern -> Sigma -> Tc [(Name,Sigma)]
checkPat pat exp_ty = tcPat pat (Check exp_ty)

--- ----------------------- ---
--- inferSigma & checkSigma ---
--- ----------------------- ---

-- |- poly infer
inferSigma :: Expr -> Tc Sigma
inferSigma e = do
  exp_ty <- inferRho e
  env_tys <- getEnvTypes
  env_tvs <- getMetaTyVars env_tys
  res_tvs <- getMetaTyVars [exp_ty]
  let forall_tvs = res_tvs \\ env_tvs
  s <- quantify forall_tvs exp_ty
  return s

-- |- poly check
checkSigma :: Expr -> Sigma -> Tc ()
checkSigma expr sigma = do
  (skol_tvs, rho) <- skolemise sigma
  checkRho expr rho
  env_tys <- getEnvTypes
  esc_tvs <- getFreeTyVars (sigma : env_tys)
  let bad_tvs = filter (`elem` esc_tvs) skol_tvs
  check (null bad_tvs) "Type not polymorphic enough"

--- -------------------- ---
--- Subsumption checking ---
--- -------------------- ---

-- |- dsk
-- Rule DEEP-SKOL
-- (subsCheck args off exp) checks that
-- ’off’ is at least as polymorphic as ’args -> exp’
subsCheck :: Sigma -> Sigma -> Tc ()
subsCheck sigma1 sigma2 = do
  (skol_tvs, rho2) <- skolemise sigma2
  subsCheckRho sigma1 rho2
  esc_tvs <- getFreeTyVars [sigma1,sigma2]
  let bad_tvs = filter (`elem` esc_tvs) skol_tvs
  check (null bad_tvs) $
    "Subsumption check failed: " ++ show sigma1 ++
    "is not as polymorphic as " ++ show sigma2

-- |- dsk*
-- Invariant: the second argument is in weak-prenex form
-- 呼ばれるのはinstSigmaとsubsCheck内のみで, どちらも
-- Rho型を渡している.
subsCheckRho :: Sigma -> Rho -> Tc ()
subsCheckRho sigma rho = do
  check (not (isImpredicativeType sigma)
      && not (isImpredicativeType rho )) "Impredicative type is not allowed"
  case (sigma,rho) of
    (Forall{}, rho2) -> do --Rule SPEC
        rho1 <- instantiate sigma
        subsCheckRho rho1 rho2
    (rho1, Fun a2 r2) -> do --Rule FUN
        (a1,r1) <- unifyFun rho1
        subsCheckFun a1 r1 a2 r2
    (Fun a1 r1, rho2) -> do --Rule FUN
        (a2,r2) <- unifyFun rho2
        subsCheckFun a1 r1 a2 r2
    (TyPair a1 b1, rho2) -> do --Rule PAIR
        (a2,b2) <- unifyPair rho2
        subsCheckRho a1 a2
        subsCheckRho b1 b2
    (rho1, TyPair a2 b2) -> do --Rule PAIR
        (a1,b1) <- unifyPair rho1
        subsCheckRho a1 a2
        subsCheckRho b1 b2
    (tau1, tau2) -> do
        unify tau1 tau2

---- Rule SPEC
--subsCheckRho sigma1@(Forall _ _) rho2 = do
--  rho1 <- instantiate sigma1
--  subsCheckRho rho1 rho2
--
---- Rule FUN
--subsCheckRho rho1 (Fun a2 r2) = do
--  (a1,r1) <- unifyFun rho1
--  subsCheckFun a1 r1 a2 r2
--
---- Rule FUN
--subsCheckRho (Fun a1 r1) rho2 = do
--  (a2,r2) <- unifyFun rho2
--  subsCheckFun a1 r1 a2 r2
--
--subsCheckRho (TyPair a1 b1) rho2 = do
--  (a2, b2) <- unifyPair rho2
--  subsCheckRho a1 a2
--  subsCheckRho b1 b2
--
---- Rule MONO
--subsCheckRho tau1 tau2 = do
--  unify tau1 tau2

subsCheckFun :: Sigma -> Rho -> Sigma -> Rho -> Tc ()
subsCheckFun a1 r1 a2 r2 = do
  subsCheck a2 a1
  subsCheckRho r1 r2

-- |- intst δ
-- Invariant: if the second argument is (Check rho),
-- then rho is in weak-prenex form
-- tcRhoの性質をそのまま引く次ぐ.
-- tcRho (EMatch {}) の InferとCheckでそれぞれ
-- instSigmaのCheckが呼ばれているが, これもRho型なので問題ない
instSigma :: Sigma -> Expected Rho -> Tc ()
instSigma t1 (Check t2) = do
  subsCheckRho t1 t2
instSigma t1 (Infer r) = do
  t1' <- instantiate t1
  writeTcRef r t1'

isTau :: Type -> Bool
isTau ty = case ty of
    Forall [] ty -> isTau ty
    Forall _ _ -> False
    TyInt -> True
    TyBool -> True
    TyVar _ -> True
    TyPair ty1 ty2 -> isTau ty1 && isTau ty2
    TyList ty1 -> isTau ty1
    MetaTv _ -> True

isImpredicativeType :: Type -> Bool
isImpredicativeType ty = case ty of
    TyInt -> False
    TyBool -> False
    TyVar _ -> False
    MetaTv _ -> False
    Forall _ ty' -> isImpredicativeType ty'
    Fun ty1 ty2 -> isImpredicativeType ty1
                || isImpredicativeType ty2
    TyPair ty1 ty2 -> isImpredicativeType ty1
                   || isImpredicativeType ty2
    TyList ty' -> not $ isTau ty'




