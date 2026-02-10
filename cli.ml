(* cli.ml - Build orchestration for garter compiler *)

open Runner
open Errors

type platform = Darwin | Linux

let detect_platform () =
  let ic = Unix.open_process_in "uname" in
  let uname = input_line ic in
  close_in ic;
  match uname with
  | "Darwin" -> Darwin
  | "Linux" -> Linux
  | _ -> failwith ("Unsupported platform: " ^ uname)

let nasm_format = function
  | Darwin -> "macho64"
  | Linux -> "elf64"

let clang_flags = function
  | Darwin -> "-arch x86_64"
  | Linux -> "-m64"

let runtime_path () =
  (* Look for runtime relative to the executable, then fall back to cwd *)
  let exe_dir = Filename.dirname Sys.executable_name in
  let candidates =
    [ Filename.concat exe_dir
        "../runtime/target/x86_64-apple-darwin/release/libgarter_runtime.a"
    ; "runtime/target/x86_64-apple-darwin/release/libgarter_runtime.a"
    ; Filename.concat exe_dir
        "../runtime/target/x86_64-unknown-linux-gnu/release/libgarter_runtime.a"
    ; "runtime/target/x86_64-unknown-linux-gnu/release/libgarter_runtime.a"
    ]
  in
  match List.find_opt Sys.file_exists candidates with
  | Some path -> path
  | None -> failwith "Could not find garter runtime library"

let build_exe ~no_builtins file output =
  let platform = detect_platform () in
  let basename = Filename.remove_extension (Filename.basename file) in
  let asm_file = Filename.temp_file basename ".s" in
  let obj_file = Filename.temp_file basename ".o" in
  let exe_file =
    match output with
    | Some o -> o
    | None -> Filename.remove_extension file
  in
  (* Compile to assembly *)
  (match compile_file_to_string ~no_builtins file file with
  | Error (errs, trace) ->
    let source = match Diagnostics.source_from_trace trace with
      | Some s -> s | None -> "" in
    Printf.eprintf "%s" (Diagnostics.format_errors source errs);
    exit 1
  | Ok (asm, trace) ->
    (* Display type warnings on stderr *)
    let type_warnings = Infer.get_warnings () in
    if type_warnings <> [] then begin
      let source = match Diagnostics.source_from_trace trace with
        | Some s -> s | None -> "" in
      Printf.eprintf "%s" (Diagnostics.format_errors source type_warnings)
    end;
    let oc = open_out asm_file in
    output_string oc asm;
    close_out oc);
  (* Assemble *)
  let nasm_cmd =
    Printf.sprintf "nasm -f %s -o %s %s" (nasm_format platform) obj_file
      asm_file
  in
  if Sys.command nasm_cmd <> 0
  then (
    Printf.eprintf "Assembly failed\n";
    exit 1);
  (* Link *)
  let link_cmd =
    Printf.sprintf "clang %s -o %s %s %s -lpthread -ldl" (clang_flags platform)
      exe_file obj_file (runtime_path ())
  in
  if Sys.command link_cmd <> 0
  then (
    Printf.eprintf "Linking failed\n";
    exit 1);
  (* Cleanup *)
  Sys.remove asm_file;
  Sys.remove obj_file;
  exe_file

let run_program ~no_builtins file args =
  let exe = Filename.temp_file "garter" ".run" in
  let _ = build_exe ~no_builtins file (Some exe) in
  (* Make executable *)
  Unix.chmod exe 0o755;
  let cmd = String.concat " " (exe :: args) in
  let code = Sys.command cmd in
  Sys.remove exe;
  code
