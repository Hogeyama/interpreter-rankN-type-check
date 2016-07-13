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
import System.IO (Handle, stdin, hGetChar, openFile, IOMode(..))

hGetLines :: Handle -> IO String
hGetLines handle =
    let f cs@(';':';':_) = go (reverse cs)
        f cs = do
          c <- hGetChar handle
          f (c:cs)
        go cs = do
          c <- hGetChar handle
          if c=='\n' then return cs else go cs
    in f []

print' :: Show s => s -> IO ()
print' = putStr . show

mainPrint :: Return -> IO ()
mainPrint (Exp ty v) = do
  putStr "-"
  putStr " : "
  print' ty
  putStr " = "
  print v
mainPrint (Dec l _ _) = do
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
repl :: Handle -> ValEnv -> TyEnv -> IO ()
repl handle valenv tyenv =
  do if handle==stdin then putStr "# " else return ()
     hFlush stdout
     s <- hGetLines handle
     mret <- runExceptT $ do
       tokens <- ExceptT $ return $ scanTokens s
       cmd    <- ExceptT $ return $ parseCmd tokens
       ret    <- ExceptT $ runTc valenv tyenv $ evalCommand cmd
       return ret
     case mret of
       Right ret@(Exp ty v) -> do
         mainPrint ret
         repl stdin valenv tyenv
       Right ret@(Dec _ valenv tyenv) -> do
         mainPrint ret
         repl stdin valenv tyenv
       Right ret@(Dir "use" [source]) -> do
         handle <- openFile source ReadMode
         repl handle emptyValEnv emptyTyEnv
       Left e -> do
         print e
         repl stdin valenv tyenv
  `catch` \e -> if
     | isEOFError e -> return ()
     | otherwise    -> print (e::IOException) >> main

main :: IO ()
main = repl stdin emptyValEnv emptyTyEnv

