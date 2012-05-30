module Make
           (D : Dyadic.DYADIC)
: sig

  exception Error
  
  type token = 
    | VAR of (Syntax.Syntax(D).name)
    | USE
    | UNEQUAL
    | UMINUS
    | TTIMES
    | TSIGMA
    | TRUE
    | TREAL
    | TRACE
    | TIMES
    | TARROW
    | STRING of (string)
    | SEMICOLON2
    | RPAREN
    | RIGHT
    | RBRACK
    | RBRACE
    | QUOTIENT
    | QUIT
    | PROJECT of (int)
    | PRECISION
    | POWER
    | PLUS
    | PERIOD
    | OR
    | NATURAL of (int)
    | MINUS
    | LPAREN
    | LET
    | LESS
    | LEFT
    | LBRACK
    | LBRACE
    | INVERSE
    | INFINITY
    | IN
    | HNF
    | GREATER
    | FUN
    | FORALL
    | FALSE
    | EXP
    | EXISTS
    | EQUAL
    | EOF
    | END
    | DYADIC of (D.t)
    | DARROW
    | CUT
    | COMMA
    | COLON
    | AND
  
  
  val toplevel: (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.Syntax(D).toplevel_cmd list)

end
