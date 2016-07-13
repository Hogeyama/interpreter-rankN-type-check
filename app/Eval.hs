{-# LANGUAGE TupleSections #-}

module Eval where
import Syntax
import TypeCheck
import qualified Data.Map as M
import Data.Foldable (foldlM)
import TypeCheck.TcMonad (lift)

findMatch :: Pattern -> Value -> Maybe [(Name, Value)]
findMatch (PInt n) (VInt n')
    | n == n'   = Just []
    | otherwise = Nothing
findMatch (PBool b) (VBool b')
    | b == b'   = Just []
    | otherwise = Nothing
findMatch (PVar x) v = Just [(x,v)]
findMatch PWild _ = Just []
findMatch (PPair p1 p2) (VPair v1 v2) =
    (++) <$> findMatch p1 v1 <*> findMatch p2 v2
findMatch PNil VNil = Just []
findMatch (PCons p1 p2) (VCons v1 v2) =
    (++) <$> findMatch p1 v1 <*> findMatch p2 v2
findMatch (PAnnot p _) v =
    findMatch p v
findMatch _ _ = Nothing

lookupValEnv :: Name -> ValEnv -> Maybe Value
lookupValEnv = M.lookup

evalExpr :: Expr -> Tc Value
evalExpr e = case e of
    EConstInt  i -> return $ VInt i
    EConstBool b -> return $ VBool b
    EVar x -> do
      env <- getValEnv
      case lookupValEnv x env of
        Nothing -> fail $ "Unbound value: " ++ x
        Just v  -> return v
    EAdd e1 e2 -> do
      v1 <- evalExpr e1
      v2 <- evalExpr e2
      case (v1,v2) of
          (VInt i1, VInt i2) -> return $ VInt (i1+i2)
          _ -> fail $ "Type match error: (+)"
    ESub e1 e2 -> do
      v1 <- evalExpr e1
      v2 <- evalExpr e2
      case (v1,v2) of
          (VInt i1, VInt i2) -> return $ VInt (i1-i2)
          _ -> fail $ "Type match error: (-)"
    EMul e1 e2 -> do
      v1 <- evalExpr e1
      v2 <- evalExpr e2
      case (v1,v2) of
          (VInt i1, VInt i2) -> return $ VInt (i1*i2)
          _ -> fail $ "Type match error: (*)"
    EDiv e1 e2 -> do
      v1 <- evalExpr e1
      v2 <- evalExpr e2
      case (v1,v2) of
          (VInt i1, VInt i2) -> return $ VInt (i1 `div` i2)
          _ -> fail $ "Type match error: (/)"
    EEq e1 e2 -> do
      v1 <- evalExpr e1
      v2 <- evalExpr e2
      case (v1,v2) of
          (VInt  i1, VInt  i2) -> return $ VBool (i1 == i2)
          (VBool b1, VBool b2) -> return $ VBool (b1 == b2)
          _ -> fail $ "Type match error: (=)"
    ELt e1 e2 -> do
      v1 <- evalExpr e1
      v2 <- evalExpr e2
      case (v1,v2) of
          (VInt  i1, VInt  i2) -> return $ VBool (i1 < i2)
          (VBool b1, VBool b2) -> return $ VBool (b1 < b2)
          _ -> fail $ "Type match error: (<)"
    EIf e1 e2 e3 -> do
      v1 <- evalExpr e1
      case v1 of
          VBool b ->
              if b then evalExpr e2
                   else evalExpr e3
          _ -> fail $ "Type match error: (if)"
    EFunAnnot x _ e1 -> do
      env <- getValEnv
      return $ VFun x e1 env
    EFun x e1 -> do
      env <- getValEnv
      return $ VFun x e1 env
    ELet x e1 e2 -> do
      v <- evalExpr e1
      extendValEnv x v $ evalExpr e2
    ELetRec f (EFun x e1) e2 -> do
      env <- getValEnv
      extendValEnv f (VRecFun f x e1 env) (evalExpr e2)
    ELetRec f (EAnnot (EFun x e1) _) e2 -> do
      env <- getValEnv
      extendValEnv f (VRecFun f x e1 env) (evalExpr e2)
    ELetRec {} -> do
      fail $ "recursive definition of values is not implemented"
    EApp e1 e2 -> do
      v1 <- evalExpr e1
      v2 <- evalExpr e2
      case v1 of
        VFun x e' oenv ->
          localValEnv oenv $ extendValEnv x v2 $ evalExpr e'
          --逆順になることに注意. extend ~ $ local ~ $ ~ だと x unbound
        VRecFun f x e' oenv -> do
          localValEnv oenv $ extendValEnvList [(f,v1),(x,v2)] $ evalExpr e'
        _ -> fail $ "Eval Error: EApp"

    EPair e1 e2 -> do
      v1 <- evalExpr e1
      v2 <- evalExpr e2
      return $ VPair v1 v2
    ENil -> return VNil
    ECons e1 e2 -> do
      v1 <- evalExpr e1
      v2 <- evalExpr e2
      return $ VCons v1 v2
    EMatch e1 l -> do
      v1 <- evalExpr e1
      let f [] = fail $ "Pattern match"
          f ((p,e'):l) = case findMatch p v1 of
              Nothing  -> f l
              Just xvs -> extendValEnvList xvs (evalExpr e')
      f l
    EAnnot e _ ->
      evalExpr e
    EFix {} -> fail "Impossible"


anySameBy :: (a -> a -> Bool) -> [a] -> Maybe a
anySameBy eq l = f [] l
  where
    f xs []     = Nothing
    f xs (y:ys) | any (`eq`y) xs = Just y
                | otherwise      = f (y:xs) ys

evalDecl :: Declare -> Tc ([Name],[Type],[Value])
evalDecl (Decl l) =
  case anySameBy (\(x,_) (y,_) -> x==y) l of
    Just (x,_) ->
      fail $ "Variable `" ++ x ++ "` is bound several times in this matching"
    Nothing -> do
      let (xs,es) = unzip l
      tys <- mapM inferExpr es
      vs  <- mapM evalExpr es
      return $ (xs, tys, vs)
evalDecl (RecDecl [(f,e)]) =
  evalDecl (Decl [(f, ELetRec f e (EVar f))])
evalDecl (RecDecl l) =
  case anySameBy (\(x,_) (y,_) -> x==y) l of
    Just (x,_) ->
      fail $ "Variable `" ++ x ++ "` is bound several times in this matching"
    Nothing -> do
      fail $ "let rec and: not implemented"

evalCommand :: Command -> Tc Return
evalCommand (CExp e) = do
  sigma <- inferExpr e
  v <- evalExpr e
  return $ Exp sigma v
evalCommand (CDecl l) = do
  let f :: [(Name,Type,Value)] -> [Declare] -> Tc Return
      f l [] = do
        valenv <- getValEnv
        tyenv  <- getTyEnv
        return $ Dec l valenv tyenv
      f l (dec:decs) = do
        (xs,tys,vs) <- evalDecl dec
        let l' = l ++ zip3 xs tys vs
        extendTyEnvList (zip xs tys) $
          extendValEnvList (zip xs vs) $
            f l' decs
  f [] l
evalCommand (CDirect "use" [source]) =
  return $ Dir (Use source)
evalCommand (CDirect "use" _) =
  fail $ "多い"
evalCommand (CDirect s _) =
  fail $ "unknown direction s"





