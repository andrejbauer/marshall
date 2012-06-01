module Make
           (D : Dyadic.DYADIC)
= struct

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
  
  and _menhir_env = {
    _menhir_lexer: Lexing.lexbuf -> token;
    _menhir_lexbuf: Lexing.lexbuf;
    mutable _menhir_token: token;
    mutable _menhir_startp: Lexing.position;
    mutable _menhir_endp: Lexing.position;
    mutable _menhir_shifted: int
  }
  
  and _menhir_state = 
    | MenhirState152
    | MenhirState147
    | MenhirState139
    | MenhirState137
    | MenhirState133
    | MenhirState127
    | MenhirState121
    | MenhirState108
    | MenhirState105
    | MenhirState103
    | MenhirState101
    | MenhirState98
    | MenhirState96
    | MenhirState94
    | MenhirState91
    | MenhirState88
    | MenhirState85
    | MenhirState82
    | MenhirState80
    | MenhirState78
    | MenhirState76
    | MenhirState74
    | MenhirState72
    | MenhirState70
    | MenhirState67
    | MenhirState62
    | MenhirState59
    | MenhirState57
    | MenhirState54
    | MenhirState49
    | MenhirState44
    | MenhirState41
    | MenhirState37
    | MenhirState32
    | MenhirState30
    | MenhirState28
    | MenhirState25
    | MenhirState21
    | MenhirState13
    | MenhirState12
    | MenhirState9
    | MenhirState8
    | MenhirState6
    | MenhirState0
  
    
    module S = Syntax.Syntax(D)
    module I = Interval.Interval(D)

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
let _eRR =
    Error
  
  let rec _menhir_goto_expr_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState9 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
              let _v : (S.expr) =                                     ( Tuple _2 ) in
              _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState127 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
          let _v : (S.expr list) =                                     ( _1 :: _3 ) in
          _menhir_goto_expr_list _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_run127 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | CUT ->
          _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState127
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _v
      | EXISTS ->
          _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState127
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState127
      | FORALL ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState127
      | FUN ->
          _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState127
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState127
      | LET ->
          _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState127
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState127
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState127
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState127
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState127 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState127
  
  and _menhir_run121 : _menhir_env -> (('ttv_tail * _menhir_state) * (Syntax.Syntax(D).name)) * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | CUT ->
          _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
      | EXISTS ->
          _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | FORALL ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | FUN ->
          _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | LET ->
          _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState121
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState121 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState121
  
  and _menhir_goto_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState62 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | RIGHT ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState67
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState67
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState67
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState67
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState67
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState67
              | LET ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState67
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState67
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState67
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState67
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState67 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState67)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState67 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((((_menhir_stack, _menhir_s), _2), _, _4), _, _6) = _menhir_stack in
          let _v : (S.expr) =                                     ( Cut (_2, I.bottom, _4, _6) ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState85 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | RBRACE ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | EQUAL ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | DYADIC _v ->
                      _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
                  | FALSE ->
                      _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                  | INVERSE ->
                      _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                  | LPAREN ->
                      _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                  | MINUS ->
                      _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                  | NATURAL _v ->
                      _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
                  | TRUE ->
                      _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState88
                  | VAR _v ->
                      _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState88 _v
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState88)
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s, _) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState103 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | RIGHT ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState105
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState105
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState105
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState105
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState105
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState105
              | LET ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState105
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState105
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState105
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState105
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState105 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState105)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState105 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let (((((_menhir_stack, _menhir_s), _2), _, _4), _, _6), _, _8) = _menhir_stack in
          let _v : (S.expr) =                                                ( Cut (_2, _4, _6, _8) ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState59 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((((_menhir_stack, _menhir_s), _2), _, _4), _, _6) = _menhir_stack in
          let _v : (S.expr) =                                          ( Exists (_2, _4, _6) ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState54 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((((_menhir_stack, _menhir_s), _2), _, _4), _, _6) = _menhir_stack in
          let _v : (S.expr) =                                          ( Forall (_2, _4, _6) ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState41 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((((_menhir_stack, _menhir_s), _2), _, _4), _, _6) = _menhir_stack in
          let _v : (S.expr) =                                     ( Lambda (_2, _4, _6) ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState12 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | IN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState121 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((((_menhir_stack, _menhir_s), _2), _, _4), _, _6) = _menhir_stack in
          let _v : (S.expr) =                                     ( Let (_2, _4, _6) ) in
          _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState9 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | COMMA ->
              _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
          | RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
              let _v : (S.expr) =                                     ( _2 ) in
              _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState127 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | COMMA ->
              _menhir_run127 _menhir_env (Obj.magic _menhir_stack)
          | RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
              let _v : (S.expr list) =                                     ( [_1; _3] ) in
              _menhir_goto_expr_list _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState6 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
          let _v : (S.toplevel_cmd) =                                ( Expr (_2, true) ) in
          _menhir_goto_pragma _menhir_env _menhir_stack _menhir_s _v
      | MenhirState137 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | IN ->
              _menhir_run121 _menhir_env (Obj.magic _menhir_stack)
          | EOF | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((_menhir_stack, _menhir_s), _2), _, _4) = _menhir_stack in
              let _v : (S.toplevel_cmd) =                              ( Definition (_2, _4) ) in
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_stack = Obj.magic _menhir_stack in
              let _1 = _v in
              let _v : (S.toplevel_cmd) =                                ( _1 ) in
              _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState139 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
          let _v : (S.toplevel_cmd) =                                ( Hnf _2 ) in
          _menhir_goto_pragma _menhir_env _menhir_stack _menhir_s _v
      | MenhirState152 | MenhirState147 | MenhirState0 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _v : (S.toplevel_cmd) =                                ( Expr (_1, false) ) in
          _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_or_expr_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      match _menhir_s with
      | MenhirState91 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let _3 = _v in
          let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _v : (S.expr) =                                     ( Or (_1 :: _3) ) in
          _menhir_goto_or_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState94 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let _3 = _v in
          let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _v : (S.expr list) =                                     ( _1 :: _3 ) in
          _menhir_goto_or_expr_list _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_or_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = Obj.magic _menhir_stack in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _1 = _v in
      let _v : (S.expr) =                                     ( _1 ) in
      _menhir_goto_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_goto_and_expr_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      match _menhir_s with
      | MenhirState98 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let _3 = _v in
          let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _v : (S.expr list) =                                     ( _1 :: _3 ) in
          _menhir_goto_and_expr_list _menhir_env _menhir_stack _menhir_s _v
      | MenhirState96 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let _3 = _v in
          let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _v : (S.expr) =                                     ( And (_1 :: _3) ) in
          _menhir_goto_and_expr _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_and_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState0 | MenhirState147 | MenhirState152 | MenhirState139 | MenhirState137 | MenhirState6 | MenhirState9 | MenhirState127 | MenhirState12 | MenhirState121 | MenhirState41 | MenhirState54 | MenhirState59 | MenhirState103 | MenhirState105 | MenhirState62 | MenhirState67 | MenhirState85 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | OR ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState91
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState91
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState91
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState91
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState91
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState91 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState91)
          | COMMA | EOF | IN | RBRACE | RIGHT | RPAREN | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
              let _v : (S.expr) =                                     ( _1 ) in
              _menhir_goto_or_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState94 | MenhirState91 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | OR ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState94
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState94
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState94
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState94
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState94
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState94 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState94)
          | COMMA | EOF | IN | RBRACE | RIGHT | RPAREN | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
              let _v : (S.expr list) =                                     ( [_1] ) in
              _menhir_goto_or_expr_list _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_run70 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState70
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState70
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState70
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState70
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState70
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState70 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState70
  
  and _menhir_run72 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState72
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState72
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState72
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState72
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState72
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState72 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState72
  
  and _menhir_run74 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState74
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState74
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState74
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState74
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState74
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState74 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState74
  
  and _menhir_run76 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState76
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState76
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState76
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState76
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState76
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState76 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState76
  
  and _menhir_run78 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState78
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState78
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState78
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState78
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState78
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState78 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState78
  
  and _menhir_run80 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState80
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState80
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState80
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState80
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState80
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState80 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState80
  
  and _menhir_run82 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState82
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState82
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState82
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState82
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState82
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState82 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState82
  
  and _menhir_run84 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | LBRACE ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | CUT ->
              _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState85
          | DYADIC _v ->
              _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
          | EXISTS ->
              _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState85
          | FALSE ->
              _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState85
          | FORALL ->
              _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState85
          | FUN ->
              _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState85
          | INVERSE ->
              _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState85
          | LET ->
              _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState85
          | LPAREN ->
              _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState85
          | MINUS ->
              _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState85
          | NATURAL _v ->
              _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
          | TRUE ->
              _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState85
          | VAR _v ->
              _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState85 _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState85)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run37 : _menhir_env -> 'ttv_tail * _menhir_state * (S.ty) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | LPAREN ->
          _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState37
      | TREAL ->
          _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState37
      | TSIGMA ->
          _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState37
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState37
  
  and _menhir_goto_bin_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState0 | MenhirState147 | MenhirState152 | MenhirState139 | MenhirState137 | MenhirState6 | MenhirState9 | MenhirState127 | MenhirState12 | MenhirState121 | MenhirState41 | MenhirState54 | MenhirState59 | MenhirState103 | MenhirState105 | MenhirState62 | MenhirState94 | MenhirState91 | MenhirState85 | MenhirState67 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | AND ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState96
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState96
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState96
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState96
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState96
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState96 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState96)
          | EQUAL ->
              _menhir_run84 _menhir_env (Obj.magic _menhir_stack)
          | GREATER ->
              _menhir_run82 _menhir_env (Obj.magic _menhir_stack)
          | LESS ->
              _menhir_run80 _menhir_env (Obj.magic _menhir_stack)
          | MINUS ->
              _menhir_run78 _menhir_env (Obj.magic _menhir_stack)
          | PLUS ->
              _menhir_run76 _menhir_env (Obj.magic _menhir_stack)
          | QUOTIENT ->
              _menhir_run74 _menhir_env (Obj.magic _menhir_stack)
          | TIMES ->
              _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
          | UNEQUAL ->
              _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
          | COMMA | EOF | IN | OR | RBRACE | RIGHT | RPAREN | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
              let _v : (S.expr) =                                     ( _1 ) in
              _menhir_goto_and_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState70 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | MINUS ->
              _menhir_run78 _menhir_env (Obj.magic _menhir_stack)
          | PLUS ->
              _menhir_run76 _menhir_env (Obj.magic _menhir_stack)
          | QUOTIENT ->
              _menhir_run74 _menhir_env (Obj.magic _menhir_stack)
          | TIMES ->
              _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
          | AND | COMMA | EOF | IN | OR | RBRACE | RIGHT | RPAREN | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
              let _v : (S.expr) =                                     ( apart _1 _3 ) in
              _menhir_goto_bin_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState72 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
          let _v : (S.expr) =                                     ( Binary (Times, _1, _3) ) in
          _menhir_goto_bin_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState74 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
          let _v : (S.expr) =                                     ( Binary (Quotient, _1, _3) ) in
          _menhir_goto_bin_expr _menhir_env _menhir_stack _menhir_s _v
      | MenhirState76 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | QUOTIENT ->
              _menhir_run74 _menhir_env (Obj.magic _menhir_stack)
          | TIMES ->
              _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
          | AND | COMMA | EOF | EQUAL | GREATER | IN | LESS | MINUS | OR | PLUS | RBRACE | RIGHT | RPAREN | SEMICOLON2 | UNEQUAL ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
              let _v : (S.expr) =                                     ( Binary (Plus, _1, _3) ) in
              _menhir_goto_bin_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState78 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | QUOTIENT ->
              _menhir_run74 _menhir_env (Obj.magic _menhir_stack)
          | TIMES ->
              _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
          | AND | COMMA | EOF | EQUAL | GREATER | IN | LESS | MINUS | OR | PLUS | RBRACE | RIGHT | RPAREN | SEMICOLON2 | UNEQUAL ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
              let _v : (S.expr) =                                     ( Binary (Minus, _1, _3) ) in
              _menhir_goto_bin_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState80 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | MINUS ->
              _menhir_run78 _menhir_env (Obj.magic _menhir_stack)
          | PLUS ->
              _menhir_run76 _menhir_env (Obj.magic _menhir_stack)
          | QUOTIENT ->
              _menhir_run74 _menhir_env (Obj.magic _menhir_stack)
          | TIMES ->
              _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
          | AND | COMMA | EOF | IN | OR | RBRACE | RIGHT | RPAREN | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
              let _v : (S.expr) =                                     ( Less (_1, _3) ) in
              _menhir_goto_bin_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState82 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | MINUS ->
              _menhir_run78 _menhir_env (Obj.magic _menhir_stack)
          | PLUS ->
              _menhir_run76 _menhir_env (Obj.magic _menhir_stack)
          | QUOTIENT ->
              _menhir_run74 _menhir_env (Obj.magic _menhir_stack)
          | TIMES ->
              _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
          | AND | COMMA | EOF | IN | OR | RBRACE | RIGHT | RPAREN | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
              let _v : (S.expr) =                                     ( Less (_3, _1) ) in
              _menhir_goto_bin_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState88 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | MINUS ->
              _menhir_run78 _menhir_env (Obj.magic _menhir_stack)
          | PLUS ->
              _menhir_run76 _menhir_env (Obj.magic _menhir_stack)
          | QUOTIENT ->
              _menhir_run74 _menhir_env (Obj.magic _menhir_stack)
          | TIMES ->
              _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
          | AND | COMMA | EOF | IN | OR | RBRACE | RIGHT | RPAREN | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (((_menhir_stack, _menhir_s, _1), _, _4), _, _7) = _menhir_stack in
              let _v : (S.expr) =                                                      ( equal _4 _1 _7 ) in
              _menhir_goto_bin_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState98 | MenhirState96 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | AND ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState98
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState98
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState98
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState98
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState98
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState98 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState98)
          | EQUAL ->
              _menhir_run84 _menhir_env (Obj.magic _menhir_stack)
          | GREATER ->
              _menhir_run82 _menhir_env (Obj.magic _menhir_stack)
          | LESS ->
              _menhir_run80 _menhir_env (Obj.magic _menhir_stack)
          | MINUS ->
              _menhir_run78 _menhir_env (Obj.magic _menhir_stack)
          | PLUS ->
              _menhir_run76 _menhir_env (Obj.magic _menhir_stack)
          | QUOTIENT ->
              _menhir_run74 _menhir_env (Obj.magic _menhir_stack)
          | TIMES ->
              _menhir_run72 _menhir_env (Obj.magic _menhir_stack)
          | UNEQUAL ->
              _menhir_run70 _menhir_env (Obj.magic _menhir_stack)
          | COMMA | EOF | IN | OR | RBRACE | RIGHT | RPAREN | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
              let _v : (S.expr list) =                                     ( [_1] ) in
              _menhir_goto_and_expr_list _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_ty : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.ty) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState28 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
              let _v : (S.ty) =                                      ( _2 ) in
              _menhir_goto_ty_simple _menhir_env _menhir_stack _menhir_s _v
          | TARROW ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState37 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | TARROW ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack)
          | DARROW | RPAREN ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
              let _v : (S.ty) =                                      ( Ty_Arrow (_1, _3) ) in
              _menhir_goto_ty _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState25 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | DARROW ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState41
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState41
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState41
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState41
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState41
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState41
              | LET ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState41
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState41
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState41
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState41
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState41 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState41)
          | TARROW ->
              _menhir_run37 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_unary_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = Obj.magic _menhir_stack in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _1 = _v in
      let _v : (S.expr) =                                     ( _1 ) in
      _menhir_goto_bin_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run19 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | NATURAL _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _ = _menhir_discard _menhir_env in
          let _menhir_stack = Obj.magic _menhir_stack in
          let _3 = _v in
          let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _v : (S.expr) =                                     ( Power (_1, _3) ) in
          _menhir_goto_pow_expr _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run148 : _menhir_env -> 'ttv_tail * _menhir_state * (S.toplevel_cmd) -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      _menhir_reduce57 _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_reduce58 : _menhir_env -> 'ttv_tail * _menhir_state * (S.toplevel_cmd) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v : (Syntax.Syntax(D).toplevel_cmd list) =                                     ( [_1] ) in
      _menhir_goto_toplevel _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_goto_ty_prod_list : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.ty list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      match _menhir_s with
      | MenhirState32 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let _3 = _v in
          let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _v : (S.ty list) =                                      ( _1 :: _3 ) in
          _menhir_goto_ty_prod_list _menhir_env _menhir_stack _menhir_s _v
      | MenhirState30 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let _3 = _v in
          let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _v : (S.ty) =                                      ( Ty_Tuple (_1 :: _3) ) in
          _menhir_goto_ty_prod _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_ty_prod : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.ty) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = Obj.magic _menhir_stack in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _1 = _v in
      let _v : (S.ty) =                                      ( _1 ) in
      _menhir_goto_ty _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_goto_pow_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState13 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | POWER ->
              _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
          | AND | COMMA | EOF | EQUAL | GREATER | IN | LESS | MINUS | OR | PLUS | QUOTIENT | RBRACE | RIGHT | RPAREN | SEMICOLON2 | TIMES | UNEQUAL ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
              let _v : (S.expr) =                                     ( Unary (Inverse, _2) ) in
              _menhir_goto_unary_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState152 | MenhirState147 | MenhirState0 | MenhirState139 | MenhirState137 | MenhirState6 | MenhirState127 | MenhirState9 | MenhirState121 | MenhirState12 | MenhirState41 | MenhirState54 | MenhirState59 | MenhirState105 | MenhirState103 | MenhirState98 | MenhirState96 | MenhirState94 | MenhirState91 | MenhirState88 | MenhirState85 | MenhirState82 | MenhirState80 | MenhirState78 | MenhirState76 | MenhirState74 | MenhirState72 | MenhirState70 | MenhirState67 | MenhirState62 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | POWER ->
              _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
          | AND | COMMA | EOF | EQUAL | GREATER | IN | LESS | MINUS | OR | PLUS | QUOTIENT | RBRACE | RIGHT | RPAREN | SEMICOLON2 | TIMES | UNEQUAL ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
              let _v : (S.expr) =                                     ( _1 ) in
              _menhir_goto_unary_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState8 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | POWER ->
              _menhir_run19 _menhir_env (Obj.magic _menhir_stack)
          | AND | COMMA | EOF | EQUAL | GREATER | IN | LESS | MINUS | OR | PLUS | QUOTIENT | RBRACE | RIGHT | RPAREN | SEMICOLON2 | TIMES | UNEQUAL ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
              let _v : (S.expr) =                                     ( Unary (Opposite, _2) ) in
              _menhir_goto_unary_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_right_endpoint : _menhir_env -> 'ttv_tail -> _menhir_state -> (D.t) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = Obj.magic _menhir_stack in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _3 = _v in
      let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v : (S.I.t) =                                        ( I.make _1 _3 ) in
      _menhir_goto_segment _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_goto_command : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.toplevel_cmd) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState0 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | EOF ->
              let _menhir_stack = Obj.magic _menhir_stack in
              _menhir_reduce58 _menhir_env (Obj.magic _menhir_stack)
          | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
              | EOF ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | HNF ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | LET ->
                  _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
              | PRECISION ->
                  _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | QUIT ->
                  _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | TRACE ->
                  _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | USE ->
                  _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState147
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState147 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState147)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState152 | MenhirState147 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | EOF ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              _menhir_reduce58 _menhir_env (Obj.magic _menhir_stack)
          | SEMICOLON2 ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
              | EOF ->
                  _menhir_run148 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | HNF ->
                  _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | LET ->
                  _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
              | PRECISION ->
                  _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | QUIT ->
                  _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | TRACE ->
                  _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | USE ->
                  _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState152
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState152 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState152)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_numconst : _menhir_env -> 'ttv_tail -> _menhir_state -> (D.t) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState49 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
          let _v : (D.t) =                                      ( _2 ) in
          _menhir_goto_left_endpoint _menhir_env _menhir_stack _menhir_s _v
      | MenhirState108 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | RBRACK ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
              let _v : (D.t) =                                      ( _1 ) in
              _menhir_goto_right_endpoint _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState133 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _, _2) = _menhir_stack in
          let _v : (S.toplevel_cmd) =                                ( Precision _2 ) in
          _menhir_goto_pragma _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_ty_simple : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.ty) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState25 | MenhirState37 | MenhirState28 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | TIMES ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | LPAREN ->
                  _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState30
              | TREAL ->
                  _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState30
              | TSIGMA ->
                  _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState30
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState30)
          | DARROW | RPAREN | TARROW ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
              let _v : (S.ty) =                                      ( _1 ) in
              _menhir_goto_ty_prod _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState32 | MenhirState30 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | TIMES ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | LPAREN ->
                  _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState32
              | TREAL ->
                  _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState32
              | TSIGMA ->
                  _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState32
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState32)
          | DARROW | RPAREN | TARROW ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
              let _v : (S.ty list) =                                      ( [_1] ) in
              _menhir_goto_ty_prod_list _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_reduce59 : _menhir_env -> ('ttv_tail * _menhir_state * (S.toplevel_cmd)) * _menhir_state * (Syntax.Syntax(D).toplevel_cmd list) -> 'ttv_return =
    fun _menhir_env _menhir_stack ->
      let ((_menhir_stack, _menhir_s, _1), _, _3) = _menhir_stack in
      let _v : (Syntax.Syntax(D).toplevel_cmd list) =                                     ( _1 :: _3 ) in
      _menhir_goto_toplevel _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_fail : unit -> 'a =
    fun () ->
      Printf.fprintf Pervasives.stderr "Internal failure -- please contact the parser generator's developers.\n%!";
      assert false
  
  and _menhir_goto_apply_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _menhir_stack = Obj.magic _menhir_stack in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState21
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState21
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState21
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState21 _v
      | AND | COMMA | EOF | EQUAL | GREATER | IN | LESS | MINUS | OR | PLUS | POWER | QUOTIENT | RBRACE | RIGHT | RPAREN | SEMICOLON2 | TIMES | UNEQUAL ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          let _v : (S.expr) =                                     ( _1 ) in
          _menhir_goto_pow_expr _menhir_env _menhir_stack _menhir_s _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState21
  
  and _menhir_run17 : _menhir_env -> 'ttv_tail * _menhir_state * (S.expr) -> (int) -> 'ttv_return =
    fun _menhir_env _menhir_stack _v ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _2 = _v in
      let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
      let _v : (S.expr) =                                     ( Proj (_1, _2) ) in
      _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_goto_segment : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.I.t) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState44 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState54
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState54
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState54
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState54
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState54
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState54
              | LET ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState54
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState54
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState54
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState54
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState54 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState54)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState57 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | COMMA ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState59
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState59
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState59
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState59
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState59
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState59
              | LET ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState59
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState59
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState59
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState59
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState59 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState59)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState101 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | LEFT ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState103
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _v
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState103
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState103
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState103
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState103
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState103
              | LET ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState103
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState103
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState103
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState103
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState103 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState103)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_left_endpoint : _menhir_env -> 'ttv_tail -> _menhir_state -> (D.t) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      let _menhir_stack = Obj.magic _menhir_stack in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | COMMA ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | DYADIC _v ->
              _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
          | INFINITY ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_s = MenhirState108 in
              let _menhir_stack = (_menhir_stack, _menhir_s) in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | RPAREN ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _ = _menhir_discard _menhir_env in
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s) = _menhir_stack in
                  let _v : (D.t) =                                      ( D.positive_infinity ) in
                  _menhir_goto_right_endpoint _menhir_env _menhir_stack _menhir_s _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | NATURAL _v ->
              _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState108 _v
          | PLUS ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _menhir_s = MenhirState108 in
              let _menhir_stack = (_menhir_stack, _menhir_s) in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | INFINITY ->
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let _tok = _menhir_discard _menhir_env in
                  (match _tok with
                  | RPAREN ->
                      let _menhir_stack = Obj.magic _menhir_stack in
                      let _ = _menhir_discard _menhir_env in
                      let _menhir_stack = Obj.magic _menhir_stack in
                      let (_menhir_stack, _menhir_s) = _menhir_stack in
                      let _v : (D.t) =                                      ( D.positive_infinity ) in
                      _menhir_goto_right_endpoint _menhir_env _menhir_stack _menhir_s _v
                  | _ ->
                      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                      _menhir_env._menhir_shifted <- (-1);
                      let _menhir_stack = Obj.magic _menhir_stack in
                      let (_menhir_stack, _menhir_s) = _menhir_stack in
                      _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  let _menhir_stack = Obj.magic _menhir_stack in
                  let (_menhir_stack, _menhir_s) = _menhir_stack in
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState108)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_goto_pragma : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.toplevel_cmd) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = Obj.magic _menhir_stack in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _1 = _v in
      let _v : (S.toplevel_cmd) =                                ( _1 ) in
      _menhir_goto_command _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run50 : _menhir_env -> 'ttv_tail -> _menhir_state -> (int) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _1 = _v in
      let _v : (D.t) =                                     ( D.of_int ~round:D.down _1 ) in
      _menhir_goto_numconst _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run51 : _menhir_env -> 'ttv_tail -> _menhir_state -> (D.t) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _1 = _v in
      let _v : (D.t) =                                     ( _1 ) in
      _menhir_goto_numconst _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run26 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (S.ty) =                                      ( Ty_Sigma ) in
      _menhir_goto_ty_simple _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run27 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (S.ty) =                                      ( Ty_Real ) in
      _menhir_goto_ty_simple _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run28 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | LPAREN ->
          _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState28
      | TREAL ->
          _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState28
      | TSIGMA ->
          _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState28
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState28
  
  and _menhir_goto_toplevel : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Syntax(D).toplevel_cmd list) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState0 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
          Obj.magic _1
      | MenhirState147 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | EOF ->
              let _menhir_stack = Obj.magic _menhir_stack in
              _menhir_reduce59 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState152 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | EOF ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              _menhir_reduce59 _menhir_env (Obj.magic _menhir_stack)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_goto_simple_expr : _menhir_env -> 'ttv_tail -> _menhir_state -> (S.expr) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _menhir_stack = (_menhir_stack, _menhir_s, _v) in
      match _menhir_s with
      | MenhirState152 | MenhirState147 | MenhirState0 | MenhirState139 | MenhirState137 | MenhirState6 | MenhirState8 | MenhirState127 | MenhirState9 | MenhirState121 | MenhirState12 | MenhirState41 | MenhirState54 | MenhirState59 | MenhirState105 | MenhirState103 | MenhirState98 | MenhirState96 | MenhirState94 | MenhirState91 | MenhirState88 | MenhirState85 | MenhirState82 | MenhirState80 | MenhirState78 | MenhirState76 | MenhirState74 | MenhirState72 | MenhirState70 | MenhirState67 | MenhirState62 | MenhirState13 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | PROJECT _v ->
              _menhir_run17 _menhir_env (Obj.magic _menhir_stack) _v
          | AND | COMMA | DYADIC _ | EOF | EQUAL | FALSE | GREATER | IN | LESS | LPAREN | MINUS | NATURAL _ | OR | PLUS | POWER | QUOTIENT | RBRACE | RIGHT | RPAREN | SEMICOLON2 | TIMES | TRUE | UNEQUAL | VAR _ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _1) = _menhir_stack in
              let _v : (S.expr) =                                     ( _1 ) in
              _menhir_goto_apply_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | MenhirState21 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          let _tok = _menhir_env._menhir_token in
          (match _tok with
          | PROJECT _v ->
              _menhir_run17 _menhir_env (Obj.magic _menhir_stack) _v
          | AND | COMMA | DYADIC _ | EOF | EQUAL | FALSE | GREATER | IN | LESS | LPAREN | MINUS | NATURAL _ | OR | PLUS | POWER | QUOTIENT | RBRACE | RIGHT | RPAREN | SEMICOLON2 | TIMES | TRUE | UNEQUAL | VAR _ ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s, _1), _, _2) = _menhir_stack in
              let _v : (S.expr) =                                     ( App (_1, _2) ) in
              _menhir_goto_apply_expr _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s, _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          _menhir_fail ()
  
  and _menhir_run10 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | VAR _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | EQUAL ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState12
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState12
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState12
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState12
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState12
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState12
              | LET ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState12
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState12
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState12
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState12
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState12 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState12)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run45 : _menhir_env -> 'ttv_tail * (Syntax.Syntax(D).name) -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (S.I.t) =                                        ( I.bottom ) in
      _menhir_goto_segment _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run46 : _menhir_env -> 'ttv_tail * (Syntax.Syntax(D).name) -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | MINUS ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | INFINITY ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s) = _menhir_stack in
              let _v : (D.t) =                                      ( D.negative_infinity ) in
              _menhir_goto_left_endpoint _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let (_menhir_stack, _menhir_s) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run49 : _menhir_env -> 'ttv_tail * (Syntax.Syntax(D).name) -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _v
      | NATURAL _v ->
          _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState49 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState49
  
  and _menhir_discard : _menhir_env -> token =
    fun _menhir_env ->
      let lexbuf = _menhir_env._menhir_lexbuf in
      let _tok = _menhir_env._menhir_lexer lexbuf in
      _menhir_env._menhir_token <- _tok;
      _menhir_env._menhir_startp <- lexbuf.Lexing.lex_start_p;
      _menhir_env._menhir_endp <- lexbuf.Lexing.lex_curr_p;
      let shifted = Pervasives.(+) _menhir_env._menhir_shifted 1 in
      if Pervasives.(>=) shifted 0 then
        _menhir_env._menhir_shifted <- shifted;
      _tok
  
  and _menhir_errorcase : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      match _menhir_s with
      | MenhirState152 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState147 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState139 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState137 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState133 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState127 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState121 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState108 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState105 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState103 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState101 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState98 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState96 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState94 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState91 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState88 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState85 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState82 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState80 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState78 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState76 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState74 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState72 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState70 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState67 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState62 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState59 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState57 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState54 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState49 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState44 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState41 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState37 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState32 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState30 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState28 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState25 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState21 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s, _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState13 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState12 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState9 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState8 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState6 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | MenhirState0 ->
          let _menhir_stack = Obj.magic _menhir_stack in
          raise _eRR
  
  and _menhir_run1 : _menhir_env -> 'ttv_tail -> _menhir_state -> (Syntax.Syntax(D).name) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _1 = _v in
      let _v : (S.expr) =                                     ( Var _1 ) in
      _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run2 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | STRING _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | EOF ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _ = _menhir_discard _menhir_env in
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _2) = _menhir_stack in
              let _v : (S.toplevel_cmd) =                                ( Use _2 ) in
              _menhir_goto_pragma _menhir_env _menhir_stack _menhir_s _v
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run5 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (S.expr) =                                     ( True ) in
      _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run6 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | CUT ->
          _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState6
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
      | EXISTS ->
          _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState6
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState6
      | FORALL ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState6
      | FUN ->
          _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState6
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState6
      | LET ->
          _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState6
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState6
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState6
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState6
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState6 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState6
  
  and _menhir_run132 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (S.toplevel_cmd) =                                ( Quit ) in
      _menhir_goto_pragma _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run133 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run51 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
      | NATURAL _v ->
          _menhir_run50 _menhir_env (Obj.magic _menhir_stack) MenhirState133 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState133
  
  and _menhir_run7 : _menhir_env -> 'ttv_tail -> _menhir_state -> (int) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _1 = _v in
      let _v : (S.expr) =                                     ( Dyadic (D.of_int ~round:D.down _1) ) in
      _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run8 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState8
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState8 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState8
  
  and _menhir_run9 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | CUT ->
          _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v
      | EXISTS ->
          _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | FORALL ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | FUN ->
          _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | LET ->
          _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState9
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState9 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState9
  
  and _menhir_run135 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | VAR _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | EQUAL ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState137
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState137
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState137
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState137
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState137
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState137
              | LET ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState137
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState137
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState137
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState137
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState137 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState137)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run13 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState13
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState13
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState13
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState13 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState13
  
  and _menhir_run139 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | CUT ->
          _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
      | EXISTS ->
          _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | FORALL ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | FUN ->
          _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | LET ->
          _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState139
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState139 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState139
  
  and _menhir_run23 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | VAR _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | COLON ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | LPAREN ->
                  _menhir_run28 _menhir_env (Obj.magic _menhir_stack) MenhirState25
              | TREAL ->
                  _menhir_run27 _menhir_env (Obj.magic _menhir_stack) MenhirState25
              | TSIGMA ->
                  _menhir_run26 _menhir_env (Obj.magic _menhir_stack) MenhirState25
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState25)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run42 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | VAR _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | COLON ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | LBRACK ->
                  _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState44
              | LPAREN ->
                  _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState44
              | TREAL ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState44
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState44)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_run14 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _v : (S.expr) =                                     ( False ) in
      _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run55 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | VAR _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | COLON ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | LBRACK ->
                  _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState57
              | LPAREN ->
                  _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState57
              | TREAL ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState57
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState57)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and _menhir_reduce57 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _v : (Syntax.Syntax(D).toplevel_cmd list) =                                     ( [] ) in
      _menhir_goto_toplevel _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run15 : _menhir_env -> 'ttv_tail -> _menhir_state -> (D.t) -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s _v ->
      let _ = _menhir_discard _menhir_env in
      let _menhir_stack = Obj.magic _menhir_stack in
      let _1 = _v in
      let _v : (S.expr) =                                     ( Dyadic _1 ) in
      _menhir_goto_simple_expr _menhir_env _menhir_stack _menhir_s _v
  
  and _menhir_run60 : _menhir_env -> 'ttv_tail -> _menhir_state -> 'ttv_return =
    fun _menhir_env _menhir_stack _menhir_s ->
      let _menhir_stack = (_menhir_stack, _menhir_s) in
      let _tok = _menhir_discard _menhir_env in
      match _tok with
      | VAR _v ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_stack = (_menhir_stack, _v) in
          let _tok = _menhir_discard _menhir_env in
          (match _tok with
          | COLON ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | LBRACK ->
                  _menhir_run49 _menhir_env (Obj.magic _menhir_stack) MenhirState101
              | LPAREN ->
                  _menhir_run46 _menhir_env (Obj.magic _menhir_stack) MenhirState101
              | TREAL ->
                  _menhir_run45 _menhir_env (Obj.magic _menhir_stack) MenhirState101
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState101)
          | LEFT ->
              let _menhir_stack = Obj.magic _menhir_stack in
              let _tok = _menhir_discard _menhir_env in
              (match _tok with
              | CUT ->
                  _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState62
              | DYADIC _v ->
                  _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
              | EXISTS ->
                  _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState62
              | FALSE ->
                  _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState62
              | FORALL ->
                  _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState62
              | FUN ->
                  _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState62
              | INVERSE ->
                  _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState62
              | LET ->
                  _menhir_run10 _menhir_env (Obj.magic _menhir_stack) MenhirState62
              | LPAREN ->
                  _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState62
              | MINUS ->
                  _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState62
              | NATURAL _v ->
                  _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
              | TRUE ->
                  _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState62
              | VAR _v ->
                  _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState62 _v
              | _ ->
                  assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
                  _menhir_env._menhir_shifted <- (-1);
                  _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState62)
          | _ ->
              assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
              _menhir_env._menhir_shifted <- (-1);
              let _menhir_stack = Obj.magic _menhir_stack in
              let ((_menhir_stack, _menhir_s), _) = _menhir_stack in
              _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s)
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          let _menhir_stack = Obj.magic _menhir_stack in
          let (_menhir_stack, _menhir_s) = _menhir_stack in
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) _menhir_s
  
  and toplevel : (Lexing.lexbuf -> token) -> Lexing.lexbuf -> (Syntax.Syntax(D).toplevel_cmd list) =
    fun lexer lexbuf ->
      let _menhir_env = let _tok = lexer lexbuf in
      {
        _menhir_lexer = lexer;
        _menhir_lexbuf = lexbuf;
        _menhir_token = _tok;
        _menhir_startp = lexbuf.Lexing.lex_start_p;
        _menhir_endp = lexbuf.Lexing.lex_curr_p;
        _menhir_shifted = 4611686018427387903;
        } in
      Obj.magic (let _menhir_stack = () in
      assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
      let _tok = _menhir_env._menhir_token in
      match _tok with
      | CUT ->
          _menhir_run60 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | DYADIC _v ->
          _menhir_run15 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
      | EOF ->
          let _menhir_stack = Obj.magic _menhir_stack in
          let _menhir_s = MenhirState0 in
          _menhir_reduce57 _menhir_env (Obj.magic _menhir_stack) _menhir_s
      | EXISTS ->
          _menhir_run55 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | FALSE ->
          _menhir_run14 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | FORALL ->
          _menhir_run42 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | FUN ->
          _menhir_run23 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | HNF ->
          _menhir_run139 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | INVERSE ->
          _menhir_run13 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | LET ->
          _menhir_run135 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | LPAREN ->
          _menhir_run9 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | MINUS ->
          _menhir_run8 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | NATURAL _v ->
          _menhir_run7 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
      | PRECISION ->
          _menhir_run133 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | QUIT ->
          _menhir_run132 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | TRACE ->
          _menhir_run6 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | TRUE ->
          _menhir_run5 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | USE ->
          _menhir_run2 _menhir_env (Obj.magic _menhir_stack) MenhirState0
      | VAR _v ->
          _menhir_run1 _menhir_env (Obj.magic _menhir_stack) MenhirState0 _v
      | _ ->
          assert (Pervasives.(<>) _menhir_env._menhir_shifted (-1));
          _menhir_env._menhir_shifted <- (-1);
          _menhir_errorcase _menhir_env (Obj.magic _menhir_stack) MenhirState0)
  
  



end
