%{
    module S = Syntax.Make(D)
    module I = Interval.Make(D)

    open S

    let equal r e1 e2 =
      let x = fresh_name () in
      let y = fresh_name () in
      let d = Binary (Minus, e1, e2) in
	Let (y, r,
	    Let (x, d,
		  And [Less (Unary (Opposite, Var y), Var x); Less (Var x, Var y)]))

    let apart e1 e2 =
      let x = fresh_name () in
      let y = fresh_name () in
	Let (x, e1,
	    Let (y, e2,
		  Or [Less (Var x, Var y); Less (Var y, Var x)]))
%}

%parameter <D : Dyadic.DYADIC>

%token TSIGMA TREAL
%token TTIMES TARROW
%token <Syntax.Make(D).name> VAR
%token <D.t> DYADIC
%token <int> NATURAL
%token <int> PROJECT
%token INFINITY
%token TRUE FALSE
%token AND OR
%token FORALL EXISTS
%token LET IN
%token CUT LEFT RIGHT
%token FUN DARROW
%token PLUS MINUS TIMES QUOTIENT INVERSE UMINUS POWER EXP
%token EQUAL LESS GREATER UNEQUAL
%token COLON COMMA PERIOD SEMICOLON2
%token LPAREN RPAREN
%token LBRACK RBRACK LBRACE RBRACE
%token USE QUIT TRACE PRECISION HNF
%token <string> STRING
%token EOF
%token END

%start toplevel
%type <Syntax.Make(D).toplevel_cmd list> toplevel

%nonassoc SEMICOLON2
%right TARROW
%right TTIMES
%nonassoc COMMA
%nonassoc FUN DARROW
%nonassoc CUT LEFT RIGHT
%nonassoc EXISTS FORALL LET IN
%left OR
%left AND
%nonassoc EQUAL LESS GREATER UNEQUAL
%left PLUS MINUS
%left TIMES QUOTIENT
%nonassoc UMINUS
%nonassoc INVERSE EXP
%left POWER
%left COLON

%%

toplevel:
  | EOF                             { [] }
  | command EOF                     { [$1] }
  | command SEMICOLON2 toplevel EOF { $1 :: $3 }

command:
  | pragma                     { $1 }
  | expr                       { Expr ($1, false) }
  | letdef                     { $1 }

pragma:
  | USE STRING EOF             { Use $2 }
  | TRACE expr                 { Expr ($2, true) }
  | PRECISION numconst         { Precision $2 }
  | HNF expr                   { Hnf $2 }
  | QUIT                       { Quit }

letdef:
  | LET VAR EQUAL expr       { Definition ($2, $4) }

expr:
  | or_expr                         { $1 }
  | CUT VAR COLON segment LEFT expr RIGHT expr { Cut ($2, $4, $6, $8) }
  | CUT VAR LEFT expr RIGHT expr    { Cut ($2, I.bottom, $4, $6) }
  | EXISTS VAR COLON segment COMMA expr  { Exists ($2, $4, $6) }
  | FORALL VAR COLON segment COMMA expr  { Forall ($2, $4, $6) }
  | LET VAR EQUAL expr IN expr      { Let ($2, $4, $6) }
  | FUN VAR COLON ty DARROW expr    { Lambda ($2, $4, $6) }

simple_expr:
  | VAR                             { Var $1 }
  | NATURAL                         { Dyadic (D.of_int ~round:D.down $1) }
  | DYADIC                          { Dyadic $1 }
  | TRUE                            { True }
  | FALSE                           { False }
  | simple_expr PROJECT             { Proj ($1, $2) }
  | LPAREN expr RPAREN              { $2 }
  | LPAREN expr_list RPAREN         { Tuple $2 }

apply_expr:
  | apply_expr simple_expr          { App ($1, $2) }
  | simple_expr                     { $1 }

pow_expr:
  | apply_expr                      { $1 }
  | pow_expr POWER NATURAL          { Power ($1, $3) }

unary_expr:
  | pow_expr                        { $1 }
  | MINUS pow_expr %prec UMINUS     { Unary (Opposite, $2) }
  | INVERSE pow_expr                { Unary (Inverse, $2) }

bin_expr:
  | unary_expr                      { $1 }
  | bin_expr PLUS bin_expr          { Binary (Plus, $1, $3) }
  | bin_expr MINUS bin_expr         { Binary (Minus, $1, $3) } 
  | bin_expr TIMES bin_expr         { Binary (Times, $1, $3) }
  | bin_expr QUOTIENT bin_expr      { Binary (Quotient, $1, $3) }
  | bin_expr EQUAL LBRACE expr RBRACE EQUAL bin_expr { equal $4 $1 $7 }
  | bin_expr UNEQUAL bin_expr       { apart $1 $3 }
  | bin_expr LESS bin_expr          { Less ($1, $3) }
  | bin_expr GREATER bin_expr       { Less ($3, $1) }

and_expr:
  | bin_expr                        { $1 }
  | bin_expr AND and_expr_list      { And ($1 :: $3) }

and_expr_list:
  | bin_expr                        { [$1] }
  | bin_expr AND and_expr_list      { $1 :: $3 }

or_expr:
  | and_expr                        { $1 }
  | and_expr OR or_expr_list        { Or ($1 :: $3) }

or_expr_list:
  | and_expr                        { [$1] }
  | and_expr OR or_expr_list        { $1 :: $3 }

expr_list:
  | expr COMMA expr                 { [$1; $3] }
  | expr COMMA expr_list            { $1 :: $3 }

ty_simple:
  | TSIGMA                           { Ty_Sigma }
  | TREAL                            { Ty_Real }
  | LPAREN ty RPAREN                 { $2 }

ty_prod:
  | ty_simple                        { $1 }
  | ty_simple TIMES ty_prod_list     { Ty_Tuple ($1 :: $3) }

ty_prod_list:
  | ty_simple                        { [$1] }
  | ty_simple TIMES ty_prod_list     { $1 :: $3 }

ty:
  | ty TARROW ty                     { Ty_Arrow ($1, $3) }
  | ty_prod                          { $1 }
      
segment:
  | TREAL                              { I.bottom }
  | left_endpoint COMMA right_endpoint { I.make $1 $3 }
	
left_endpoint:
  | LPAREN MINUS INFINITY            { D.negative_infinity }
  | LBRACK numconst                  { $2 }

right_endpoint:
  | INFINITY RPAREN                  { D.positive_infinity }
  | PLUS INFINITY RPAREN             { D.positive_infinity }
  | numconst RBRACK                  { $1 }

numconst:
  | NATURAL                         { D.of_int ~round:D.down $1 }
  | DYADIC                          { $1 }
