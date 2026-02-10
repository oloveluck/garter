open Cmdliner
open Compile
open Runner
open Printf
open Exprs
open Errors
open Phases
open Pretty

(* Find a specific phase in the trace *)
let find_phase_in_trace (trace : phase list) (matcher : phase -> 'a option) :
    'a option =
  List.find_map matcher trace

(* Compile subcommand implementation *)
let compile_to_asm file trace no_builtins no_typecheck debug dump_parsed dump_anf
    dump_located =
  show_debug_print := debug;
  let sep = "\n=================\n" in
  match compile_file_to_string ~no_builtins ~no_typecheck file file with
  | Error (errs, trace_result) ->
    if trace
    then eprintf "%s%s" (ExtString.String.join sep (print_trace trace_result)) sep
    else ();
    let source = match Diagnostics.source_from_trace trace_result with
      | Some s -> s | None -> "" in
    eprintf "%s" (Diagnostics.format_errors source errs);
    1
  | Ok (program, trace_result) ->
    (* Display type warnings on stderr *)
    let type_warnings = Infer.get_warnings () in
    if type_warnings <> [] then begin
      let source = match Diagnostics.source_from_trace trace_result with
        | Some s -> s | None -> "" in
      eprintf "%s" (Diagnostics.format_errors source type_warnings)
    end;
    if dump_parsed
    then
      let parsed =
        find_phase_in_trace trace_result (function
          | Parsed p -> Some p
          | _ -> None)
      in
      match parsed with
      | Some p ->
        printf "%s\n" (string_of_program p);
        0
      | None ->
        eprintf "Parsed phase not found in trace\n";
        1
    else if dump_anf
    then
      let anfed =
        find_phase_in_trace trace_result (function
          | ANFed p -> Some p
          | _ -> None)
      in
      match anfed with
      | Some p ->
        printf "%s\n" (string_of_aprogram p);
        0
      | None ->
        eprintf "ANF phase not found in trace\n";
        1
    else if dump_located
    then
      let located =
        find_phase_in_trace trace_result (function
          | Located (p, env) -> Some (p, env)
          | _ -> None)
      in
      match located with
      | Some (p, env) ->
        printf "ANF:\n%s\n\nVariable Bindings:\n" (string_of_aprogram p);
        List.iter
          (fun (fname, bindings) ->
            printf "  %s:\n" fname;
            List.iter
              (fun (name, arg) ->
                printf "    %s => %s\n" name (Assembly.arg_to_asm arg))
              bindings)
          env;
        0
      | None ->
        eprintf "Located phase not found in trace\n";
        1
    else if trace
    then (
      printf "%s\n" (ExtString.String.join sep (print_trace trace_result));
      0)
    else (
      printf "%s\n" program;
      0)

(* Build subcommand implementation *)
let build_exe file output no_builtins =
  try
    let _ = Cli.build_exe ~no_builtins file output in
    0
  with
  | Failure msg ->
    eprintf "Build failed: %s\n" msg;
    1
  | exn ->
    eprintf "Build failed: %s\n" (Printexc.to_string exn);
    1

(* Run subcommand implementation *)
let run_program file args no_builtins =
  try Cli.run_program ~no_builtins file args with
  | Failure msg ->
    eprintf "Run failed: %s\n" msg;
    1
  | exn ->
    eprintf "Run failed: %s\n" (Printexc.to_string exn);
    1

(* Common arguments *)
let file_arg =
  Arg.(
    required
    & pos 0 (some file) None
    & info [] ~docv:"FILE" ~doc:"Source file to compile")

let trace_arg =
  Arg.(value & flag & info [ "t"; "trace" ] ~doc:"Display the trace of compilation")

let no_builtins_arg =
  Arg.(
    value & flag & info [ "no-builtins" ] ~doc:"Leave out all built-in functions")

let no_typecheck_arg =
  Arg.(
    value & flag & info [ "no-typecheck" ] ~doc:"Disable Hindley-Milner type checking")

let debug_arg =
  Arg.(value & flag & info [ "d"; "debug" ] ~doc:"Enable debug printing")

let dump_parsed_arg =
  Arg.(value & flag & info [ "dump-parsed" ] ~doc:"Print parsed AST and exit")

let dump_anf_arg =
  Arg.(value & flag & info [ "dump-anf" ] ~doc:"Print ANF representation and exit")

let dump_located_arg =
  Arg.(
    value & flag
    & info [ "dump-located" ]
        ~doc:"Print located ANF with variable bindings and exit")

(* Compile subcommand term *)
let compile_term =
  Term.(
    const compile_to_asm $ file_arg $ trace_arg $ no_builtins_arg
    $ no_typecheck_arg $ debug_arg $ dump_parsed_arg $ dump_anf_arg
    $ dump_located_arg)

let compile_cmd =
  let doc = "Compile a Garter source file to assembly" in
  let info = Cmd.info "compile" ~doc in
  Cmd.v info compile_term

(* Build subcommand *)
let build_term =
  let output_arg =
    Arg.(
      value
      & opt (some string) None
      & info [ "o"; "output" ] ~docv:"FILE" ~doc:"Output executable path")
  in
  Term.(const build_exe $ file_arg $ output_arg $ no_builtins_arg)

let build_cmd =
  let doc = "Compile a Garter source file to an executable" in
  let info = Cmd.info "build" ~doc in
  Cmd.v info build_term

(* Run subcommand *)
let run_term =
  let args_arg =
    Arg.(
      value
      & pos_right 0 string []
      & info [] ~docv:"ARGS" ~doc:"Arguments to pass to the program")
  in
  Term.(const run_program $ file_arg $ args_arg $ no_builtins_arg)

let run_cmd =
  let doc = "Compile and run a Garter source file" in
  let info = Cmd.info "run" ~doc in
  Cmd.v info run_term

(* Check if first arg looks like a subcommand *)
let is_subcommand arg =
  match arg with
  | "compile" | "build" | "run" -> true
  | _ -> false

(* Main command for backwards compatibility - when no subcommand is given *)
let main_compile_cmd =
  let doc = "Garter programming language compiler" in
  let man =
    [ `S Manpage.s_description
    ; `P
        "Compiles Garter source files to x86-64 assembly. Use subcommands for \
         additional functionality:"
    ; `P "$(b,garter compile) FILE - Output assembly to stdout (default)"
    ; `P "$(b,garter build) FILE - Compile to executable"
    ; `P "$(b,garter run) FILE - Compile and run"
    ]
  in
  let info = Cmd.info "garter" ~version:"1.0.0" ~doc ~man in
  Cmd.v info compile_term

(* Main command group with subcommands *)
let main_group_cmd =
  let doc = "Garter programming language compiler" in
  let man =
    [ `S Manpage.s_description
    ; `P
        "Compiles Garter source files to x86-64 assembly. Use subcommands for \
         additional functionality."
    ]
  in
  let info = Cmd.info "garter" ~version:"1.0.0" ~doc ~man in
  Cmd.group info [ compile_cmd; build_cmd; run_cmd ]

let () =
  (* Check if we have arguments and first arg looks like subcommand *)
  let argv = Sys.argv in
  let use_group =
    Array.length argv > 1 && is_subcommand argv.(1)
  in
  if use_group
  then Stdlib.exit (Cmd.eval' main_group_cmd)
  else Stdlib.exit (Cmd.eval' main_compile_cmd)
