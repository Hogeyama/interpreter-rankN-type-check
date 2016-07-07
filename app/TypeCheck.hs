
module TypeCheck (
  Tc(..),
  runTc,
  evalTc,
  inferExpr,
  --lift,
  getTyEnv,
  extendTyEnv,
  extendTyEnvList,
  getValEnv,
  extendValEnv,
  extendValEnvList,
  localValEnv,
  ) where

import Syntax
import TypeCheck.TcMonad
import TypeCheck.TcTerm

inferExpr :: Expr -> Tc Type
inferExpr = typecheck

