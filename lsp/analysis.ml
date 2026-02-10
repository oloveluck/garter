open Exprs
open Errors
module Lsp_types = Linol_lsp.Types

type analysis_result = {
  program : sourcespan program option;
  diagnostics : Lsp_types.Diagnostic.t list;
  type_env : Types.tyenv option;
  final_subst : Types.subst option;
}

let analyze ~(uri : string) ~(source : string) : analysis_result =
  (* Phase 1: Parse *)
  let parsed =
    try Ok (Runner.parse_string uri source)
    with e -> Error [e]
  in
  match parsed with
  | Error exns ->
    { program = None;
      diagnostics = List.map Span_utils.diagnostic_of_exn exns;
      type_env = None;
      final_subst = None }
  | Ok prog ->
    (* Phase 2: Well-formedness *)
    let wf_result =
      try
        match Compile.is_well_formed prog with
        | Ok p -> Ok (p, [])
        | Error exns -> Error exns
      with e -> Error [e]
    in
    match wf_result with
    | Error exns ->
      { program = Some prog;
        diagnostics = List.map Span_utils.diagnostic_of_exn exns;
        type_env = None;
        final_subst = None }
    | Ok (wf_prog, wf_warnings) ->
      (* Phase 3: Type inference *)
      let warning_diags = List.map Span_utils.diagnostic_of_exn wf_warnings in
      let tc_result =
        try Infer.type_check_program_with_env wf_prog
        with e -> Error [e]
      in
      (match tc_result with
       | Error exns ->
         { program = Some wf_prog;
           diagnostics = warning_diags @ List.map Span_utils.diagnostic_of_exn exns;
           type_env = None;
           final_subst = None }
       | Ok (_typed_prog, subst, env, tc_warnings) ->
         let tc_warning_diags = List.map Span_utils.diagnostic_of_exn tc_warnings in
         { program = Some wf_prog;
           diagnostics = warning_diags @ tc_warning_diags;
           type_env = Some env;
           final_subst = Some subst })
