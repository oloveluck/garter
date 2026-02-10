open Printf
open Exprs
open Errors
open Phases

(* ── ANSI color support ─────────────────────────────────────────── *)

type color_mode = Auto | Always | Never

let color_mode = ref Auto

let use_color () =
  match !color_mode with
  | Always -> true
  | Never -> false
  | Auto ->
    let no_color = try Sys.getenv "NO_COLOR" <> "" with Not_found -> false in
    if no_color then false
    else try Unix.isatty Unix.stderr with _ -> false

let ansi code s = if use_color () then sprintf "\027[%sm%s\027[0m" code s else s

let bold s = ansi "1" s
let red s = ansi "31" s
let yellow s = ansi "33" s
let blue s = ansi "34" s
let bold_red s = ansi "1;31" s
let bold_yellow s = ansi "1;33" s
let bold_blue s = ansi "1;34" s

(* ── Source utilities ────────────────────────────────────────────── *)

let source_lines (src : string) : string array =
  let lines = String.split_on_char '\n' src in
  Array.of_list lines

let get_line (lines : string array) (line_num : int) : string option =
  let idx = line_num - 1 in
  if idx >= 0 && idx < Array.length lines then Some lines.(idx)
  else None

(* ── Diagnostic types ────────────────────────────────────────────── *)

type severity = Error | Warning

type diagnostic = {
  severity : severity;
  message : string;
  primary_loc : sourcespan option;
  primary_label : string;
  notes : string list;
}

(* ── Error-to-diagnostic mapping ─────────────────────────────────── *)

let string_of_loc ((pstart, _) : sourcespan) : string =
  sprintf "%s:%d:%d" pstart.Lexing.pos_fname pstart.Lexing.pos_lnum
    (pstart.Lexing.pos_cnum - pstart.Lexing.pos_bol)

let error_to_diagnostic (e : exn) : diagnostic =
  match e with
  | ParseError msg ->
    { severity = Error; message = msg;
      primary_loc = None; primary_label = ""; notes = [] }
  | UnboundId (name, loc) ->
    { severity = Error;
      message = sprintf "The identifier `%s` is not in scope" name;
      primary_loc = Some loc; primary_label = "not found in this scope";
      notes = [] }
  | UnboundFun (name, loc) ->
    { severity = Error;
      message = sprintf "The function `%s` is not in scope" name;
      primary_loc = Some loc; primary_label = "not found in this scope";
      notes = [] }
  | ShadowId (name, loc, existing) ->
    { severity = Warning;
      message = sprintf "The identifier `%s` shadows a previous definition" name;
      primary_loc = Some loc; primary_label = "shadows previous definition";
      notes = [sprintf "previously defined at %s" (string_of_loc existing)] }
  | DuplicateId (name, loc, existing) ->
    { severity = Error;
      message = sprintf "The identifier `%s` is defined multiple times" name;
      primary_loc = Some loc; primary_label = "redefined here";
      notes = [sprintf "previously defined at %s" (string_of_loc existing)] }
  | DuplicateFun (name, loc, existing) ->
    { severity = Error;
      message = sprintf "The function `%s` is defined multiple times" name;
      primary_loc = Some loc; primary_label = "redefined here";
      notes = [sprintf "previously defined at %s" (string_of_loc existing)] }
  | Overflow (num, loc) ->
    { severity = Error;
      message = sprintf "Integer overflow: the number literal %Ld is too large" num;
      primary_loc = Some loc; primary_label = "value out of range";
      notes = [] }
  | Arity (expected, actual, loc) ->
    { severity = Error;
      message = sprintf "Arity mismatch: expected %d arguments, got %d" expected actual;
      primary_loc = Some loc;
      primary_label = sprintf "%d arguments provided" actual;
      notes = [] }
  | DeclArity (name, num_args, num_types, loc) ->
    { severity = Error;
      message = sprintf "The function `%s` has %d arguments but %d types provided"
        name num_args num_types;
      primary_loc = Some loc; primary_label = "mismatched declaration";
      notes = [] }
  | ShouldBeFunction (name, loc) ->
    { severity = Error;
      message = sprintf "`%s` should be a function" name;
      primary_loc = Some loc; primary_label = "expected function";
      notes = [] }
  | LetRecNonFunction (_, loc) ->
    { severity = Error;
      message = "Let-rec binding must be a lambda";
      primary_loc = Some loc; primary_label = "expected lambda binding";
      notes = [] }
  | TypeError (msg, loc) ->
    { severity = Error;
      message = sprintf "Type error: %s" msg;
      primary_loc = Some loc; primary_label = "type mismatch";
      notes = [] }
  | TypeWarning (msg, loc) ->
    { severity = Warning;
      message = sprintf "Type warning: %s" msg;
      primary_loc = Some loc; primary_label = "type warning";
      notes = [] }
  | Unsupported (msg, loc) ->
    { severity = Error;
      message = sprintf "Unsupported: %s" msg;
      primary_loc = Some loc; primary_label = "not supported";
      notes = [] }
  | NotYetImplemented msg ->
    { severity = Error;
      message = sprintf "Not yet implemented: %s" msg;
      primary_loc = None; primary_label = ""; notes = [] }
  | InternalCompilerError msg ->
    { severity = Error;
      message = sprintf "Internal compiler error: %s" msg;
      primary_loc = None; primary_label = "";
      notes = ["This is a bug in the compiler."] }
  | _ ->
    (* Catch UnifyError and anything else *)
    let msg = Printexc.to_string e in
    (* Try to extract sourcespan from UnifyError pattern *)
    { severity = Error; message = msg;
      primary_loc = None; primary_label = ""; notes = [] }

(* ── Renderer ────────────────────────────────────────────────────── *)

let render_diagnostic (lines : string array) (d : diagnostic) : string =
  let buf = Buffer.create 256 in
  let bprintf = Buffer.add_string buf in
  (* Header: "error: message" or "warning: message" *)
  let severity_str = match d.severity with
    | Error -> bold_red "error"
    | Warning -> bold_yellow "warning" in
  bprintf (sprintf "%s%s %s\n" severity_str (bold ":") (bold d.message));
  (* Source context *)
  (match d.primary_loc with
   | None -> ()
   | Some ((pstart, pend) : sourcespan) ->
     let file = pstart.Lexing.pos_fname in
     let start_line = pstart.Lexing.pos_lnum in
     let start_col = pstart.Lexing.pos_cnum - pstart.Lexing.pos_bol in
     let end_line = pend.Lexing.pos_lnum in
     let end_col = pend.Lexing.pos_cnum - pend.Lexing.pos_bol in
     (* Compute gutter width based on line number *)
     let max_line = if end_line > start_line then end_line else start_line in
     let gutter_width = max 1 (String.length (string_of_int max_line)) in
     let pad n =
       let s = string_of_int n in
       let padding = gutter_width - String.length s in
       String.make (max 0 padding) ' ' ^ s
     in
     let empty_gutter = String.make gutter_width ' ' in
     (* Location line *)
     bprintf (sprintf " %s %s %s:%d:%d\n"
       empty_gutter (bold_blue "-->") file start_line (start_col + 1));
     (* Empty gutter line *)
     bprintf (sprintf " %s %s\n" empty_gutter (bold_blue "|"));
     (* Source line *)
     (match get_line lines start_line with
      | Some src_line ->
        let max_display = 120 in
        let truncated, display_line, adjusted_start_col, underline_len =
          if String.length src_line > max_display then
            let display = String.sub src_line 0 max_display ^ "..." in
            let adj_col = min start_col (max_display - 1) in
            let ulen = if start_line = end_line
              then min (end_col - start_col) (max_display - adj_col)
              else max_display - adj_col in
            (true, display, adj_col, max 1 ulen)
          else
            let ulen = if start_line = end_line
              then max 1 (end_col - start_col)
              else max 1 (String.length src_line - start_col) in
            (false, src_line, start_col, ulen)
        in
        ignore truncated;
        bprintf (sprintf " %s %s %s\n"
          (bold_blue (pad start_line)) (bold_blue "|") display_line);
        (* Underline *)
        let spaces = String.make adjusted_start_col ' ' in
        let carets = String.make underline_len '^' in
        let colored_carets = match d.severity with
          | Error -> bold_red carets
          | Warning -> bold_yellow carets in
        let label = if d.primary_label <> ""
          then " " ^ (match d.severity with
            | Error -> bold_red d.primary_label
            | Warning -> bold_yellow d.primary_label)
          else "" in
        bprintf (sprintf " %s %s %s%s%s\n"
          empty_gutter (bold_blue "|") spaces colored_carets label);
        (* Multi-line span note *)
        if end_line > start_line then
          bprintf (sprintf " %s %s ... spans to line %d\n"
            empty_gutter (bold_blue "|") end_line)
      | None -> ());
     (* Closing gutter *)
     bprintf (sprintf " %s %s\n" empty_gutter (bold_blue "|")));
  (* Notes *)
  List.iter (fun note ->
    bprintf (sprintf " %s %s %s\n"
      (match d.primary_loc with
       | Some ((pstart, _) : sourcespan) ->
         String.make (max 1 (String.length (string_of_int pstart.Lexing.pos_lnum))) ' '
       | None -> " ")
      (bold_blue "= note:")
      note)
  ) d.notes;
  Buffer.contents buf

(* ── Public API ──────────────────────────────────────────────────── *)

let source_from_trace (trace : phase list) : string option =
  List.find_map (function Source s -> Some s | _ -> None) trace

let format_errors (source : string) (errs : exn list) : string =
  let lines = source_lines source in
  let buf = Buffer.create 512 in
  List.iter (fun e ->
    let d = error_to_diagnostic e in
    Buffer.add_string buf (render_diagnostic lines d);
    Buffer.add_char buf '\n'
  ) errs;
  Buffer.contents buf
