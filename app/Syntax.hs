
module Syntax where

import Data.IORef
import Data.List  (nub)
import Data.Maybe (fromMaybe)
import qualified Data.Map as M

-----Data Type-----
type Name = String-- {{{
-- }}}
data Error = Failure String-- {{{
           | Unify String
instance Show Error where
  show (Failure s) = "Failure: " ++ s
  show (Unify s)   = "Unification Error: " ++ s
-- }}}
type TyEnv = M.Map Name Type-- {{{
-- }}}
type ValEnv = M.Map Name Value-- {{{
-- }}}
data Pattern-- {{{
    = PInt Int
    | PBool Bool
    | PVar Name
    | PPair Pattern Pattern
    | PNil
    | PCons Pattern Pattern
    | PWild
    deriving (Show, Eq)
-- }}}
data Value-- {{{
    = VInt Int
    | VBool Bool
    | VFun Name Expr ValEnv
    | VRecFun Name Name Expr ValEnv
    | VPair Value Value
    | VNil
    | VCons Value Value
    deriving (Eq)
instance Show Value where
  show = showValue
-- }}}
data Expr-- {{{
    = EConstInt Int
    | EConstBool Bool
    | EVar Name
    | EApp Expr Expr
    | EFun Name Expr
    | EFunAnnot Name Type Expr
    | ELet    Name Expr Expr
    | ELetRec Name Expr Expr
    | EAnnot Expr Type
    | EAdd Expr Expr
    | ESub Expr Expr
    | EMul Expr Expr
    | EDiv Expr Expr
    | EEq  Expr Expr
    | ELt  Expr Expr
    | EIf  Expr Expr Expr
    | EPair Expr Expr
    | ENil
    | ECons  Expr Expr
    | EMatch Expr [(Pattern, Expr)]
    | EFix Expr
    deriving (Show, Eq)
infixl 4 `EApp`
-- }}}
data Command-- {{{
    = CExp Expr
    | CDecl [Declare]
    deriving (Show, Eq)
-- }}}
data Declare-- {{{
    = Decl [(Name,Expr)]
    | RecDecl [(Name,Expr)]
    deriving (Show, Eq)
-- }}}
data Return-- {{{
    = E Type Value
    | D [(Name,Type,Value)] ValEnv TyEnv
    deriving (Show,Eq)
-- }}}
type Sigma = Type-- {{{
-- }}}
type Rho = Type-- {{{
-- }}}
type Tau = Type-- {{{
-- }}}
data Type-- {{{
    = Forall [TyVar] Rho
    | Fun Type Type
    | TyInt
    | TyBool
    | TyVar TyVar
    | TyPair Type Type
    | TyList Type
    | MetaTv MetaTv
    deriving (Eq)
instance Show Type where
  show = showType . rmNonsenseForall
-- }}}
data TyVar = BoundTv String-- {{{
           | SkolemTv String Uniq
          deriving (Eq)
instance Show TyVar where
  show (BoundTv s) = s
  show (SkolemTv s n) = s ++ show n
-- }}}
data MetaTv = Meta Uniq TyRef-- {{{
instance Show MetaTv where
  show (Meta n _) = "$" ++ show n
instance Eq MetaTv where
  (Meta n _) == (Meta m _) = n == m
-- }}}
type Uniq = Int-- {{{
-- }}}
type TyRef = IORef (Maybe Tau)-- {{{
-- }}}

-----Initial Env-----
emptyTyEnv :: TyEnv-- {{{
emptyTyEnv = M.empty
-- }}}
emptyValEnv :: ValEnv-- {{{
emptyValEnv = M.empty
-- }}}

-----Free & Bound Variables-----
metaTvs :: [Type] -> [MetaTv]-- {{{
metaTvs tys = foldr go [] tys
  where
    go (MetaTv tv) acc
      | tv `elem` acc = acc
      | otherwise     = tv:acc
    go (TyVar _) acc = acc
    go TyInt     acc = acc
    go TyBool    acc = acc
    go (Fun arg res) acc = go arg (go res acc)
    go (Forall _ ty) acc = go ty acc
    go (TyList ty) acc = go ty acc
    go (TyPair ty1 ty2) acc = go ty1 (go ty2 acc)
-- }}}
freeTyVars :: [Type] -> [TyVar]-- {{{
freeTyVars tys = foldr (go []) [] tys
  where
    go :: [TyVar] -> Type -> [TyVar] -> [TyVar]
    go bound (TyVar tv) acc
      | tv `elem` bound = acc
      | tv `elem` acc   = acc
      | otherwise       = tv:acc
    go bound (MetaTv _) acc = acc
    go bound TyInt  acc = acc
    go bound TyBool acc = acc
    go bound (Fun arg res) acc = go bound arg (go bound res acc)
    go bound (Forall tvs ty) acc = go (tvs++bound) ty acc
    go bound (TyList ty) acc = go bound ty acc
    go bound (TyPair ty1 ty2) acc = go bound ty1 (go bound ty2 acc)
-- }}}
tyVarBndrs :: Rho -> [TyVar]-- {{{
tyVarBndrs ty = nub (bndrs ty)
  where
    bndrs (Forall tvs body) = tvs ++ bndrs body
    bndrs (Fun arg res)     = bndrs arg ++ bndrs res
    bndrs _ = []
-- }}}
tyVarName :: TyVar -> Name-- {{{
tyVarName (BoundTv s) = s
tyVarName (SkolemTv s _) = s
-- }}}

-----Subst------
substTy :: [TyVar] -> [Type] -> Type -> Type-- {{{
substTy tvs tys ty = subst_ty (tvs `zip` tys) ty
-- }}}
subst_ty :: [(TyVar,Type)] -> Type -> Type-- {{{
subst_ty env (Fun arg res) = Fun (subst_ty env arg) (subst_ty env res)
subst_ty env (TyVar a) = fromMaybe (TyVar a) (lookup a env)
subst_ty env (MetaTv tv) = MetaTv tv
subst_ty env TyInt = TyInt
subst_ty env TyBool = TyBool
subst_ty env (TyList ty) = TyList (subst_ty env ty)
subst_ty env (TyPair ty1 ty2) = TyPair (subst_ty env ty1) (subst_ty env ty2)
subst_ty env (Forall ns rho) = Forall ns (subst_ty env' rho)
  where env' = [ (n,ty') | (n,ty') <- env, n `notElem` ns ]
-- }}}

------Show------
showType :: Type -> String-- {{{
showType TyInt = "int"
showType TyBool = "bool"
showType (TyVar tv) = show tv
showType (MetaTv tv) = show tv
showType (Fun ty1 ty2) =
    let s1 = case ty1 of
               Forall l _ -> kakko $ show ty1
               Fun {}     -> kakko $ show ty1
               _ -> show ty1
        s2 = show ty2
    in s1 ++ " -> " ++ s2
showType (TyPair ty1 ty2) =
    let s1 = case ty1 of
               Forall l _ -> kakko $ show ty1
               TyPair {}  -> kakko $ show ty1
               Fun {}     -> kakko $ show ty1
               _ -> show ty1
        s2 = case ty2 of
               Forall l _ -> kakko $ show ty2
               TyPair {}  -> kakko $ show ty2
               Fun {}     -> kakko $ show ty2
               _ -> show ty2
    in s1 ++ " * " ++ s2
showType (TyList ty) =
    let s = case ty of
              Forall l _ -> kakko $ show ty
              TyPair {}  -> kakko $ show ty
              Fun {}     -> kakko $ show ty
              _ -> show ty
    in s ++ " list"
showType (Forall l ty) =
    let f [] = ""
        f [tv] = show tv
        f (tv:l) = show tv ++ " " ++ f l
    in "forall " ++ f l ++ ". " ++ show ty
-- }}}
rmNonsenseForall :: Type -> Type-- {{{
rmNonsenseForall ty = case ty of
    Forall [] ty1   -> rmNonsenseForall ty1
    Forall l  ty1   -> Forall l (rmNonsenseForall ty1)
    Fun ty1 ty2     -> Fun      (rmNonsenseForall ty1) (rmNonsenseForall ty2)
    TyPair ty1 ty2  -> TyPair   (rmNonsenseForall ty1) (rmNonsenseForall ty2)
    TyList ty1      -> TyList   (rmNonsenseForall ty1)
    TyInt           -> ty
    TyBool          -> ty
    TyVar _         -> ty
    MetaTv _        -> ty
-- }}}
kakko :: String -> String-- {{{
kakko s = "(" ++ s ++ ")"
-- }}}

showValue :: Value -> String-- {{{
showValue (VInt n) = show n
showValue (VBool True) = "true"
showValue (VBool False) = "false"
showValue (VFun {}) = "<fun>"
showValue (VRecFun {}) = "<fun>"
showValue (VPair v1 v2) = "(" ++ showValue v1 ++ ", " ++ showValue v2 ++ ")"
showValue (VNil) = "[]"
showValue (VCons v1 v2) =
    let f v1 VNil = showValue v1
        f v1 (VCons v21 v22) =
            showValue v1 ++ "; " ++ f v21 v22
        f v1 _ = error "show VCons"
    in "[" ++ f v1 v2 ++ "]"
-- }}}

