open Compile
open Runner
open Printf
open Lexing
open Exprs
open Errors
open Phases
open Pretty

let show_trace = ref false
let no_builtins = ref false
let filename_set = ref false
let filename : string ref = ref ""
let dump_parsed = ref false
let dump_anf = ref false
let dump_located = ref false

(* Find a specific phase in the trace *)
let find_phase_in_trace (trace : phase list) (matcher : phase -> 'a option) : 'a option =
  List.find_map matcher trace

let () =
  let speclist = [
      ("-t", Arg.Set show_trace, "Display the trace of compilation");
      ("-no-builtins", Arg.Set no_builtins, "Leave out all built-in functions");
      ("-d", Arg.Set show_debug_print, "Enable debug printing");
      ("--dump-parsed", Arg.Set dump_parsed, "Print parsed AST and exit");
      ("--dump-anf", Arg.Set dump_anf, "Print ANF representation and exit");
      ("--dump-located", Arg.Set dump_located, "Print located ANF with variable bindings and exit");
    ] in
  Arg.parse speclist (fun name ->
      if !filename_set then
        raise (Arg.Bad "Cannot compile more than one file name")
      else
        (filename_set := true;
         filename := name)
    ) "Compiler options:";
  let sep = "\n=================\n" in
  match compile_file_to_string ~no_builtins:!no_builtins (!filename) (!filename) with
  | Error (errs, trace) ->
     (if !show_trace then
        eprintf "%s%s" (ExtString.String.join sep (print_trace trace)) sep
      else ());
     eprintf "Errors:\n";
     eprintf "%s\n" (ExtString.String.join "\n" (print_errors errs))
  | Ok (program, trace) ->
     if !dump_parsed then
       let parsed = find_phase_in_trace trace (function
         | Parsed p -> Some p
         | _ -> None) in
       (match parsed with
        | Some p -> printf "%s\n" (string_of_program p)
        | None -> eprintf "Parsed phase not found in trace\n")
     else if !dump_anf then
       let anfed = find_phase_in_trace trace (function
         | ANFed p -> Some p
         | _ -> None) in
       (match anfed with
        | Some p -> printf "%s\n" (string_of_aprogram p)
        | None -> eprintf "ANF phase not found in trace\n")
     else if !dump_located then
       let located = find_phase_in_trace trace (function
         | Located (p, env) -> Some (p, env)
         | _ -> None) in
       (match located with
        | Some (p, env) ->
           printf "ANF:\n%s\n\nVariable Bindings:\n" (string_of_aprogram p);
           List.iter (fun (fname, bindings) ->
             printf "  %s:\n" fname;
             List.iter (fun (name, arg) ->
               printf "    %s => %s\n" name (Assembly.arg_to_asm arg)) bindings
           ) env
        | None -> eprintf "Located phase not found in trace\n")
     else if !show_trace then
       printf "%s\n" (ExtString.String.join sep (print_trace trace))
     else
       printf "%s\n" program;;
