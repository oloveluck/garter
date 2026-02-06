open Exprs

let wrap_natives (p : sourcespan program) : sourcespan program =
  match p with
  | Program (decls, expr, ss) ->
    let wrappers =
      [ [ DFun
            ( "print"
            , [ BName ("print_arg", false, ss) ]
            , EApp (EId ("print", ss), [ EId ("print_arg", ss) ], Native, ss)
            , ss )
        ]
      ; [ DFun
            ( "input"
            , [ BName ("input_arg", false, ss) ]
            , EApp (EId ("input", ss), [ EId ("input_arg", ss) ], Native, ss)
            , ss )
        ]
      ; [ DFun
            ( "isnum"
            , [ BName ("isnum_arg", false, ss) ]
            , EApp (EId ("isnum", ss), [ EId ("isnum_arg", ss) ], Prim, ss)
            , ss )
        ]
      ; [ DFun
            ( "isbool"
            , [ BName ("isbool_arg", false, ss) ]
            , EApp (EId ("isbool", ss), [ EId ("isbool_arg", ss) ], Prim, ss)
            , ss )
        ]
      ; [ DFun
            ( "istuple"
            , [ BName ("istup_arg", false, ss) ]
            , EApp (EId ("istuple", ss), [ EId ("istup_arg", ss) ], Prim, ss)
            , ss )
        ]
      ; [ DFun
            ( "printStack"
            , [ BName ("ps_arg", false, ss) ]
            , EApp (EId ("printStack", ss), [ EId ("ps_arg", ss) ], Native, ss)
            , ss )
        ]
      ]
    in
    Program (wrappers @ decls, expr, ss)
;;
