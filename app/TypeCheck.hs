
module TypeCheck (
  Tc,
  runTc,
  inferExpr,

  getTyEnv,
  extendTyEnv,
  extendTyEnvList,

  getValEnv,
  extendValEnv,
  extendValEnvList,
  localValEnv,
  ) where

import TypeCheck.TcMonad
import TypeCheck.TcTerm

