{module Parser where
import Lexer
import Syntax
import Control.Exception.Base (throw, throwIO)

}

%name parseCmd
%tokentype { Token }
%monad { Either Error } { (>>=) } { return }
%error { parseError }

%token
    int    { TokenInt  $$  }
    bool   { TokenBool $$  }
    id     { TokenID   $$  }
    let    { TokenLet      }
    in     { TokenIn       }
    '+'    { TokenPlus     }
    '-'    { TokenMinus    }
    '*'    { TokenTimes    }
    '/'    { TokenDiv      }
    '='    { TokenEq       }
    '<'    { TokenLt       }
    if     { TokenIf       }
    then   { TokenThen     }
    else   { TokenElse     }
    '('    { TokenLParen   }
    ')'    { TokenRParen   }
    fun    { TokenFun      }
    '->'   { TokenArrow    }
    rec    { TokenRec      }
    ';;'   { TokenSemiSemi }
    '['    { TokenLBracket }
    ']'    { TokenRBracket }
    '::'   { TokenCons     }
    ','    { TokenComma    }
    match  { TokenMatch    }
    with   { TokenWith     }
    '|'    { TokenBar      }
    intT   { TokenIntT     }
    boolT  { TokenBoolT    }
    list   { TokenListT    }
    forall { TokenFolall   }
    ':'    { TokenColon    }
    '.'    { TokenDot      }
    '_'    { TokenWild     }
    and    { TokenAnd      }

%right in
%nonassoc '>' '<'
%left '+' '-'
%left '*' '/'

%%

TopLevel :: { Command }
TopLevel
    : Expr ';;' { CExp $1 }
    | let Var Args0 '=' Expr ';;'         { CDecl $2 (mkFun $3 $5) }
    | let rec Var Var Args0 '=' Expr ';;' { CRecDecl $3 $4 (mkFun $5 $7) }
    | let Var ':' Sigma '=' Expr ';;'     { CDecl $2 (EAnnot $6 $4) }

Expr :: { Expr }
Expr
    : let Var Args0 '=' Expr in Expr         { ELet $2 (mkFun $3 $5) $7       }
    | let Var ':' Sigma '=' Expr in Expr      { ELet $2 (EAnnot $6 $4) $8      }
    | let rec Var Var Args0 '=' Expr in Expr { ELetRec $3 $4 (mkFun $5 $7) $9 }
    | if Expr then Expr else Expr            { EIf $2 $4 $6                   }
    | fun Args1 '->' Expr                    { mkFun $2 $4                    }
    | ArithExpr '=' ArithExpr                { EEq $1 $3                      }
    | ArithExpr '<' ArithExpr                { ELt $1 $3                      }
    | match Expr with Cases                  { EMatch $2 $4                   }
    | match Expr with '|' Cases              { EMatch $2 $5                   }
    | ListExpr                               { $1                             }

Cases
    : Pattern '->' Expr           { [($1,$3)]  }
    | Pattern '->' Expr '|' Cases { ($1,$3):$5 }

Pattern
    : AtomicPattern '::' Pattern { PCons $1 $3 }
    | AtomicPattern              { $1          }

AtomicPattern
    : int                         { PInt $1     }
    | bool                        { PBool $1    }
    | Var                         { PVar $1     }
    | '(' Pattern ',' Pattern ')' { PPair $2 $4 }
    | '[' ']'                     { PNil        }
    | '(' Pattern ')'             { $2          }
    | '_'                         { PWild       }

ListExpr :: { Expr }
ListExpr
    : ArithExpr '::' ListExpr { ECons $1 $3 }
    | ArithExpr               { $1          }

ArithExpr :: { Expr }
ArithExpr
    : ArithExpr '+' ArithExpr { EAdd $1 $3 }
    | ArithExpr '-' ArithExpr { EAdd $1 $3 }
    | FactorExpr              { $1         }

FactorExpr :: { Expr }
FactorExpr
    : FactorExpr '*' FactorExpr { EMul $1 $3 }
    | FactorExpr '/' FactorExpr { EMul $1 $3 }
    | AppExpr                   { $1         }

AppExpr :: { Expr }
AppExpr
    : AppExpr AtomicExpr { EApp $1 $2 }
    | AtomicExpr         { $1         }

AtomicExpr :: { Expr }
AtomicExpr
    : int                   { EConstInt $1  }
    | bool                  { EConstBool $1 }
    | id                    { EVar $1       }
    | '(' Expr ')'          { $2            }
    | '[' ']'               { ENil          }
    | '(' Expr ',' Expr ')' { EPair $2 $4   }

Var :: { String }
Var
    : id { $1 }

Args0 :: { [(Name, Maybe Sigma)] }
Args0
    :           { []    }
    | Args1     { $1    }

Args1 :: { [(Name, Maybe Sigma)] }
Args1
    : Var Args0 { ($1,Nothing):$2 }
    | '(' Var ':' Sigma ')' Args0 { ($2, Just $4):$6}

TyVar :: { TyVar }
TyVar
    : id { BoundTv $1 }

TyVars :: { [TyVar] }
TyVars
    : id { [BoundTv $1] }
    | id TyVars { BoundTv $1 : $2 }

--Syntax.hsのSigmaとかとは関係ないです bad name ><
Sigma :: { Type }
Sigma
    : forall TyVars '.' Rho { Forall $2 $4 }
    | Rho                   { $1           }

Rho :: { Type }
Rho
    : Tau '->' Sigma   { Fun $1 $3 }
    | Tau              { $1        }

Tau :: { Type }
Tau
    : TauSub '->' Tau { Fun $1 $3 }
    | TauSub          { $1 }

TauSub
    : Tau '*' Tau   { TyPair $1 $3 } 
    | TauSubSub { $1 }

TauSubSub :: { Type }
    : intT          { TyInt        } 
    | boolT         { TyBool       } 
    | TyVar         { TyVar $1     } 
    | '(' Sigma ')' { $2           } 
    | Tau list      { TyList $1    } 

{

parseError :: [Token] -> Either Error a
parseError _ = Left $ Failure "Parse error"

mkFun :: [(Name, Maybe Type)] -> Expr -> Expr
mkFun argtys e =
    let f (arg, Nothing) e = EFun arg e
        f (arg, Just ty) e = EFunAnnot arg ty e
    in foldr f e argtys

}

