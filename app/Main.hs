{-# LANGUAGE MultiWayIf #-}

module Main where

import Eval
import Syntax
import TypeCheck
import Parser as P
import Lexer as L
import GHC.IO.Handle    (hFlush)
import GHC.IO.Handle.FD (stdout)
import Control.Exception.Base (IOException)
import System.IO.Error (isEOFError)
import qualified Data.Map as M
import Control.Monad.Trans.Except
import Control.Monad.Trans.Class (lift)
import Control.Monad.Catch
import Data.List (nubBy)

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

mainPrint :: Return -> IO ()
mainPrint (E ty v) = do
  putStr "-"
  putStr " : "
  print' ty
  putStr " = "
  print v
mainPrint (D l _ _) = do
  let l' = reverse $ nubBy (\(x,_,_) (y,_,_) -> x==y) $ reverse l
  mapM_ f l'
  where
    f (x,ty,v) = do
      putStr $ "val " ++ x
      putStr " : "
      print' ty
      putStr " = "
      print v

--Ctrl.Monad.CatchIO
repl :: ValEnv -> TyEnv -> IO ()
repl valenv tyenv =
  do putStr "# "
     hFlush stdout
     s <- getLines
     mret <- runExceptT $ do
       tokens <- ExceptT $ return $ scanTokens s
       cmd    <- ExceptT $ return $ parseCmd tokens
       ret    <- ExceptT $ runTc valenv tyenv $ evalCommand cmd
       return ret
     case mret of
       Right ret@(D _ valenv tyenv) -> do
         mainPrint ret
         repl valenv tyenv
       Right ret@(E ty v) -> do
         mainPrint ret
         repl valenv tyenv
       Left e -> do
         print e
         repl valenv tyenv
  `catch` \e -> if
     | isEOFError e -> return ()
     | otherwise    -> print (e::IOException) >> main

main :: IO ()
main = repl emptyValEnv emptyTyEnv

