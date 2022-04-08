open Exprs
open Errors
open Phases
open Printf
open ExtLib

(* let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  let rec wf_E (e : sourcespan expr) (* other parameters may be needed here *) =
    Error [ NotYetImplemented "Implement well-formedness checking for expressions" ]
  and wf_D (d : sourcespan decl) (* other parameters may be needed here *) =
    Error [ NotYetImplemented "Implement well-formedness checking for definitions" ]
  in
  match p with
  | Program (decls, body, _) ->
    Error [ NotYetImplemented "Implement well-formedness checking for programs" ]
;; *)

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
