{-# LANGUAGE MultiWayIf #-}

module Main where

import Eval
import Syntax
import TypeCheck
import Parser as P
import Lexer as L
import GHC.IO.Handle    (hFlush)
import GHC.IO.Handle.FD (stdout)
import Control.Exception.Base (catch, IOException)
import System.IO.Error (isEOFError)
import qualified Data.Map as M
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class (lift)

getLines :: IO String
getLines =
    let f cs@(';':';':_) = go (reverse cs)
        f cs = do
          c <- getChar
          f (c:cs)
        go cs = do
          c <- getChar
          if c=='\n' then return cs else go cs
    in f []

print' :: Show s => s -> IO ()
print' = putStr . show

mainPrint :: (Maybe String, Type, Value) -> IO ()
mainPrint (mx, sigma, v) = do
  case mx of
    Nothing -> putStr "-"
    Just x  -> putStr $ "val " ++ x
  putStr " : "
  print' sigma
  putStr " = "
  print v

repl :: ValEnv -> TyEnv -> IO ()
repl valenv tyenv =
  do putStr "# "
     hFlush stdout
     s <- getLines
     mret <- runExceptT $ do
       tokens <- ExceptT $ return $ scanTokens s
       cmd    <- ExceptT $ return $ parseCmd tokens
       ret    <- ExceptT $ evalTc valenv tyenv $ evalCommand cmd
       return ret
     case mret of
       Right ret@(Just x,ty,v) -> do
         mainPrint ret
         repl (M.insert x v valenv) (M.insert x ty tyenv)
       Right ret@(Nothing,ty,v) -> do
         mainPrint ret
         repl valenv tyenv
       Left (Failure s) -> do
         putStrLn s
         repl valenv tyenv
  `catch` \e -> if
     | isEOFError e -> return ()
     | otherwise    -> print (e::IOException) >> main

main :: IO ()
main = repl emptyValEnv emptyTyEnv

