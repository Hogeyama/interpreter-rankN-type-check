{-# LANGUAGE TupleSections #-}

module Eval where
import Syntax
import TypeCheck
import qualified Data.Map as M
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
    ELet x e1 e2 -> do
      v <- evalExpr e1
      extendValEnv x v $ evalExpr e2
    EFunAnnot x _ e1 -> do
      env <- getValEnv
      return $ VFun x e1 env
    EFun x e1 -> do
      env <- getValEnv
      return $ VFun x e1 env
    ELetRec f x e1 e2 -> do
      env <- getValEnv
      extendValEnv f (VRecFun f x e1 env) (evalExpr e2)
    EApp e1 e2 -> do
      v1 <- evalExpr e1
      v2 <- evalExpr e2
      case v1 of
        VFun x e' oenv ->
          localValEnv oenv $ extendValEnv x v2 $ evalExpr e'
          --逆順になることに注意. extend ~ $ local ~ $ ~ だと x unbound
        VRecFun f x e' oenv -> do
          lift $ print oenv
          localValEnv oenv $ extendValEnv f v1 $ extendValEnv x v2 $ evalExpr e'
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
      let f [] = error "Impossible"
          f ((p,e'):l) = case findMatch p v1 of
              Nothing  -> f l
              Just xvs -> extendValEnvList xvs (evalExpr e')
      f l
    EAnnot e _ ->
      evalExpr e

evalCommand :: Command -> Tc (Maybe String, Type, Value)
evalCommand (CExp e) = do
  sigma <- inferExpr e
  v <- evalExpr e
  return (Nothing, sigma, v)
evalCommand (CDecl x e) = do
  sigma <- inferExpr e
  v <- evalExpr e
  return (Just x, sigma, v)
evalCommand (CRecDecl f x e) = do
  evalCommand (CDecl f (ELetRec f x e (EVar f)))




