open Exprs
open Errors
module Lsp_types = Linol_lsp.Types

(* Convert a sourcespan to an LSP Range.
   Garter pos_lnum is 1-indexed, LSP line is 0-indexed.
   Garter char = pos_cnum - pos_bol, LSP character is 0-indexed. *)
let sourcespan_to_range ((pstart, pend) : sourcespan) : Lsp_types.Range.t =
  Lsp_types.Range.create
    ~start:
      (Lsp_types.Position.create
         ~line:(pstart.Lexing.pos_lnum - 1)
         ~character:(pstart.Lexing.pos_cnum - pstart.Lexing.pos_bol))
    ~end_:
      (Lsp_types.Position.create
         ~line:(pend.Lexing.pos_lnum - 1)
         ~character:(pend.Lexing.pos_cnum - pend.Lexing.pos_bol))

(* Check whether an LSP Position falls inside a sourcespan *)
let position_in_span (pos : Lsp_types.Position.t) ((pstart, pend) : sourcespan) : bool =
  let line = pos.line in
  let char = pos.character in
  let start_line = pstart.Lexing.pos_lnum - 1 in
  let start_char = pstart.Lexing.pos_cnum - pstart.Lexing.pos_bol in
  let end_line = pend.Lexing.pos_lnum - 1 in
  let end_char = pend.Lexing.pos_cnum - pend.Lexing.pos_bol in
  (line > start_line || (line = start_line && char >= start_char))
  && (line < end_line || (line = end_line && char <= end_char))

(* Fallback range at file start for errors without source location *)
let dummy_range =
  Lsp_types.Range.create
    ~start:(Lsp_types.Position.create ~line:0 ~character:0)
    ~end_:(Lsp_types.Position.create ~line:0 ~character:0)

(* Convert a compiler exception to an LSP Diagnostic *)
let diagnostic_of_exn (e : exn) : Lsp_types.Diagnostic.t =
  let open Printf in
  let make_diag ?(severity = Lsp_types.DiagnosticSeverity.Error) range msg =
    Lsp_types.Diagnostic.create
      ~message:(`String msg) ~range ~severity ~source:"garter" ()
  in
  match e with
  | ParseError msg ->
    make_diag dummy_range msg
  | UnboundId (x, loc) ->
    make_diag (sourcespan_to_range loc)
      (sprintf "The identifier %s is not in scope" x)
  | UnboundFun (x, loc) ->
    make_diag (sourcespan_to_range loc)
      (sprintf "The function name %s is not in scope" x)
  | ShadowId (x, loc, _existing) ->
    make_diag ~severity:Lsp_types.DiagnosticSeverity.Warning
      (sourcespan_to_range loc)
      (sprintf "The identifier %s shadows a previous definition" x)
  | DuplicateId (x, loc, _existing) ->
    make_diag (sourcespan_to_range loc)
      (sprintf "The identifier %s is a duplicate definition" x)
  | DuplicateFun (x, loc, _existing) ->
    make_diag (sourcespan_to_range loc)
      (sprintf "The function name %s is a duplicate definition" x)
  | Overflow (num, loc) ->
    make_diag (sourcespan_to_range loc)
      (sprintf "Integer overflow: the number literal %Ld is too large" num)
  | Arity (expected, actual, loc) ->
    make_diag (sourcespan_to_range loc)
      (sprintf "Expected %d arguments but received %d" expected actual)
  | DeclArity (name, num_args, num_types, loc) ->
    make_diag (sourcespan_to_range loc)
      (sprintf "The function %s has %d arguments but %d types provided"
         name num_args num_types)
  | ShouldBeFunction (name, loc) ->
    make_diag (sourcespan_to_range loc)
      (sprintf "%s should be a function" name)
  | LetRecNonFunction (_bind, loc) ->
    make_diag (sourcespan_to_range loc)
      "Let-rec binding must be a lambda"
  | TypeError (msg, loc) ->
    make_diag (sourcespan_to_range loc)
      (sprintf "Type error: %s" msg)
  | TypeWarning (msg, loc) ->
    make_diag ~severity:Lsp_types.DiagnosticSeverity.Warning
      (sourcespan_to_range loc)
      (sprintf "Type warning: %s" msg)
  | Unsupported (msg, loc) ->
    make_diag (sourcespan_to_range loc)
      (sprintf "Unsupported: %s" msg)
  | NotYetImplemented msg ->
    make_diag dummy_range (sprintf "Not yet implemented: %s" msg)
  | InternalCompilerError msg ->
    make_diag dummy_range (sprintf "Internal compiler error: %s" msg)
  | _ ->
    make_diag dummy_range (Printexc.to_string e)
