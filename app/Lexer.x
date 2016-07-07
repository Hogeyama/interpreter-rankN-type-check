{
module Lexer where
import Syntax
}

%wrapper "basic"

$digit = 0-9
$alpha = [a-zA-Z]

tokens :-
  $white+                       ;
  \+                              { \s -> TokenPlus         }
  \*                              { \s -> TokenTimes        }
  \-                              { \s -> TokenMinus        }
  \/                              { \s -> TokenDiv          }
  \=                              { \s -> TokenEq           }
  \<                              { \s -> TokenLt           }
  let                             { \s -> TokenLet          }
  rec                             { \s -> TokenRec          }
  in                              { \s -> TokenIn           }
  and                             { \s -> TokenAnd          }
  if                              { \s -> TokenIf           }
  then                            { \s -> TokenThen         }
  else                            { \s -> TokenElse         }
  true                            { \s -> TokenBool True    }
  false                           { \s -> TokenBool False   }
  \(                              { \s -> TokenLParen       }
  \)                              { \s -> TokenRParen       }
  fun                             { \s -> TokenFun          }
  \-\>                            { \s -> TokenArrow        }
  \[                              { \s -> TokenLBracket     }
  \]                              { \s -> TokenRBracket     }
  \:\:                            { \s -> TokenCons         }
  \,                              { \s -> TokenComma        }
  match                           { \s -> TokenMatch        }
  with                            { \s -> TokenWith         }
  \|                              { \s -> TokenBar          }
  int                             { \s -> TokenIntT         }
  bool                            { \s -> TokenBoolT        }
  list                            { \s -> TokenListT        }
  forall                          { \s -> TokenFolall       }
  \:                              { \s -> TokenColon        }
  \.                              { \s -> TokenDot          }
  \_                              { \s -> TokenWild         }
  \;\;                            { \s -> TokenSemiSemi     }
  $digit+                         { \s -> TokenInt (read s) }
  $alpha [$alpha $digit \_ \']*   { \s -> TokenID s         }

{
-- The token type:
data Token = TokenPlus
           | TokenTimes
           | TokenMinus
           | TokenDiv
           | TokenEq
           | TokenLt
           | TokenLet
           | TokenRec
           | TokenIn
           | TokenIf
           | TokenFun
           | TokenArrow
           | TokenSemiSemi
           | TokenThen
           | TokenElse
           | TokenBool Bool
           | TokenLParen
           | TokenRParen
           | TokenInt Int
           | TokenID String
           | TokenLBracket
           | TokenRBracket
           | TokenCons
           | TokenComma
           | TokenMatch
           | TokenWith
           | TokenBar
           | TokenIntT
           | TokenBoolT
           | TokenFolall
           | TokenColon
           | TokenDot
           | TokenAnd
           | TokenWild
           | TokenListT
           | TokenEOF
           deriving (Eq,Show)

scanTokens :: String -> Either Error [Token]
scanTokens str = go ('\n',[],str)
  where
    go inp@(_,_bs,s) =
      case alexScan inp 0 of
        AlexEOF -> Right []
        AlexSkip  inp' len     -> go inp'
        AlexToken inp' len act -> do
            l' <- go inp'
            return $ act (take len s) : l'
        AlexError _ -> Left $ Failure "lexical error"

}
