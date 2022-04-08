open Errors
open Phases
open Exprs
open Assembly
open Find
open Freevars
open Printf
open ExtLib

type naive_stack_env = arg name_envt name_envt

let rec lookup (funname : string) (name : string) (env : naive_stack_env) =
  match List.find_opt (fun (f, _) -> funname = f) env with
  | Some (_, name_env) ->
    (match List.find_opt (fun (n, _) -> name = n) name_env with
    | Some (_, arg) -> arg
    | None ->
      if funname = "closure#0"
      then (
        printf
          "can't look up name: %s in func: %s in env: \n %s \n\n"
          name
          funname
          (dump env);
        raise (InternalCompilerError (sprintf "failed to lookup name %s " name)))
      else lookup "closure#0" name env)
  | None ->
    printf "can't look up name %s fun: %s in env: \n %s \n\n" name funname (dump env);
    (* lookup "closure#0" name env *)
    raise (InternalCompilerError (sprintf "failed to lookup function %s" funname))
;;

let rec lookup_env (funname : string) (env : naive_stack_env) =
  match List.find_opt (fun (f, _) -> funname = f) env with
  | Some (_, name_env) -> name_env
  | None ->
    (* lookup "closure#0" name env *)
    raise (InternalCompilerError (sprintf "failed to lookup function %s" funname))
;;

(* Returns the stack-index (in words) of the deepest stack index used for any 
   of the variables in this expression *)
let rec deepest_stack e (env : naive_stack_env) funname =
  let rec helpA e =
    match e with
    | ALet (name, bind, body, _) ->
      List.fold_left max 0 [ name_to_offset name; helpC bind; helpA body ]
    | ALetRec (binds, body, _) ->
      List.fold_left max (helpA body) (List.map (fun (_, bind) -> helpC bind) binds)
    | ASeq (first, rest, _) -> max (helpC first) (helpA rest)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (c, t, f, _) -> List.fold_left max 0 [ helpI c; helpA t; helpA f ]
    | CPrim1 (_, i, _) -> helpI i
    | CPrim2 (_, i1, i2, _) -> max (helpI i1) (helpI i2)
    | CApp (_, args, _, _) -> List.fold_left max 0 (List.map helpI args)
    | CTuple (vals, _) -> List.fold_left max 0 (List.map helpI vals)
    | CGetItem (t, _, _) -> helpI t
    | CSetItem (t, _, v, _) -> max (helpI t) (helpI v)
    | CLambda (args, body, tag) ->
      let env_name = sprintf "closure#%d" tag in
      let found_env = lookup_env env_name env in
      let new_env =
        List.mapi (fun i a -> a, RegOffset (word_size * (i + 3), RBP)) args @ found_env
      in
      let new_outer_env =
        List.map (fun (en, env) -> if en = env_name then en, new_env else en, env) env
      in
      deepest_stack body new_outer_env env_name
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNil _ -> 0
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId (name, _) -> name_to_offset name
  and name_to_offset name =
    match lookup funname name env with
    | RegOffset (bytes, RBP) ->
      bytes / (-1 * word_size) (* negative because stack direction *)
    | _ -> 0
  in
  max (helpA e) 0
;;

let rec add_to_fun_env
    (funname : string)
    (name : string)
    (arg : arg)
    (env : arg name_envt name_envt)
    : arg name_envt name_envt
  =
  match env with
  | [] -> [ funname, [ name, arg ] ]
  | (envname, l) :: rest ->
    if funname = envname
    then (envname, (name, arg) :: l) :: rest
    else (envname, l) :: add_to_fun_env funname name arg rest
;;

let rec get_next_function (expr : tag cexpr) : string =
  match expr with
  | CLambda (_, _, tag) -> sprintf "closure#%d" tag
  | _ -> ""
;;

let rec allocate_aexpr
    (expr : tag aexpr)
    (funname : string)
    (si : int)
    (env : naive_stack_env)
    : naive_stack_env
  =
  match expr with
  | ALet (name, rhs, body, tag) ->
    let new_env = add_to_fun_env funname name (RegOffset (~-si * 8, RBP)) env in
    let rhs_env = allocate_cexpr rhs funname (si + 1) new_env in
    let body_env = allocate_aexpr body funname (si + 1) rhs_env in
    body_env
  | ALetRec (bindings, body, _) ->
    let bindings_env = rec_bindings_to_env bindings funname env si in
    let body_env = allocate_aexpr body funname (List.length bindings + si) bindings_env in
    body_env
  | ACExpr expr -> allocate_cexpr expr funname si env
  | ASeq (first, rest, _) ->
    let first_env = allocate_cexpr first funname si env in
    allocate_aexpr rest funname si first_env
(* | _ -> [] *)

and rec_bindings_to_env
    (bindings : (string * tag cexpr) list)
    (funname : string)
    (env : naive_stack_env)
    (si : int)
    : naive_stack_env
  =
  match bindings with
  | (name, value) :: rest ->
    let closure_name = get_next_function value in
    let lhs_env = add_to_fun_env funname name (RegOffset (~-8 * si, RBP)) env in
    let funname_in_closure_env =
      add_to_fun_env closure_name name (RegOffset (16, RBP)) lhs_env
    in
    let rhs_env = allocate_cexpr value closure_name (si + 1) funname_in_closure_env in
    rec_bindings_to_env rest funname rhs_env (si + 1)
  | [] -> env

and lambda_args_to_env
    (args : string list)
    (funname : string)
    (index : int)
    (env : naive_stack_env)
  =
  match args with
  | name :: rest ->
    let new_env =
      add_to_fun_env funname name (RegOffset (8 + ((index + 2) * 8), RBP)) env
    in
    lambda_args_to_env rest funname (index + 1) new_env
  | [] -> env

and allocate_cexpr
    (expr : tag cexpr)
    (funname : string)
    (si : int)
    (env : naive_stack_env)
    : naive_stack_env
  =
  match expr with
  | CLambda (args, body, tag) ->
    let new_name = sprintf "closure#%d" tag in
    let args_env = lambda_args_to_env args new_name 0 env in
    let body_env = allocate_aexpr body new_name si args_env in
    body_env
  | CIf (_, t, e, _) ->
    let t_env = allocate_aexpr t funname si env in
    let e_env = allocate_aexpr e funname si t_env in
    e_env
  | _ -> env
;;

(* match expr with
  | CIf (_, cond, body, tag) -> 
    let new_env = allocate_aexpr cond current_funname si env_acc @ allocate_aexpr body current_funname si env_acc
    (current_funname, new_env) @ new_env
  | CLambda (args, body, tag) ->
    let name = sprintf "closure#%s" tag in
    let frees = free_vars body args @ free_env |> List.sort String.compare in
    let arg_bindings =
      List.mapi
        (fun (i : int) (name : string) -> name, RegOffset (8 + ((i + 2) * 8), RBP))
        args
    in
    let free_bindings =
      List.mapi
        (* (fun (i : int) (name : string) -> name, RegOffset (0, RBP)) *)
          (fun (i : int) (name : string) -> name, RegOffset (~-8 * (i + 1), RBP))
        frees
    in
    arg_bindings @ free_bindings @ allocate_aexpr body name (List.length frees * 8)
  | _ -> [] *)

let naive_stack_allocation (prog : tag aprogram) : tag aprogram * arg name_envt name_envt =
  match prog with
  | AProgram (expr, tag) ->
    let exp_envt = allocate_aexpr expr "closure#0" 1 [] in
    AProgram (expr, tag), exp_envt
;;

let count_vars e =
  let rec helpA e =
    match e with
    | ASeq (e1, e2, _) -> max (helpC e1) (helpA e2)
    | ALet (_, bind, body, _) -> 1 + max (helpC bind) (helpA body)
    | ALetRec (binds, body, _) ->
      List.length binds
      + List.fold_left max (helpA body) (List.map (fun (_, rhs) -> helpC rhs) binds)
    | ACExpr e -> helpC e
  and helpC e =
    match e with
    | CIf (_, t, f, _) -> max (helpA t) (helpA f)
    | _ -> 0
  in
  helpA e
;;
