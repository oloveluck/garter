open Errors
open Phases
open Exprs
open Assembly
open Find
open Freevars
open ExtLib

(* Returns the stack-index (in words) of the deepest stack index used for any 
   of the variables in this expression *)
let rec deepest_stack e env =
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
    | CLambda (args, body, _) ->
      let new_env =
        List.mapi (fun i a -> a, RegOffset (word_size * (i + 3), RBP)) args @ env
      in
      deepest_stack body new_env
    | CImmExpr i -> helpI i
  and helpI i =
    match i with
    | ImmNil _ -> 0
    | ImmNum _ -> 0
    | ImmBool _ -> 0
    | ImmId (name, _) -> name_to_offset name
  and name_to_offset name =
    match find env name with
    | RegOffset (bytes, RBP) ->
      bytes / (-1 * word_size) (* negative because stack direction *)
    | _ -> 0
  in
  max (helpA e) 0
;;

let rec add_to_fun_env (funname : string) (name : string) (arg: arg) (env : arg name_envt name_envt): arg name_envt name_envt = 
  match env with 
  | [] -> [funname, [name, arg]]
  | (envname, l)::rest -> 
    if funname = envname 
    then (envname, (name,arg)::l)::rest 
    else (envname, l):: add_to_fun_env funname name arg rest

let rec allocate_aexpr (expr : tag aexpr) (current_funname : string) (si : int) (env_acc : arg name_envt name_envt) : arg name_envt name_envt =
  match expr with
  | ALet (name, rhs, body, _) ->
    let arg = RegOffset (~-si * 8, RBP) in
    let arg_added_env = add_to_fun_env current_funname name arg env_acc in 
    let rhs_env = allocate_cexpr rhs (si + 1) [] current_funname arg_added_env in
    allocate_aexpr body current_funname (si + 1) rhs_env
  | ACExpr c -> allocate_cexpr c si [] current_funname env_acc
  | ASeq (first, rest, _) -> allocate_cexpr first si [] current_funname env_acc @ allocate_aexpr rest current_funname si env_acc
  (* make sure name is bound to the correct closure offset *)
  | ALetRec (bindings, body, _) ->
    let bindings_env =
      List.mapi
        (fun index (name, value) ->
          (* [ name, RegOffset (~-(si + index) * 8, RBP) ] *)
          let arg = 
          [ name, RegOffset (~-8 * (si + index), RBP) ]
          @ allocate_cexpr value (si + 1 + index) [ name ] current_funname env_acc)
        bindings
      |> List.flatten
    in
    let body_env = allocate_aexpr body current_funname si env_acc in
    []

and allocate_cexpr (expr : tag cexpr) (si : int) (free_env : string list) (current_funname: string) (env_acc arg name_envt name_envt) : arg name_envt name_envt =
  match expr with
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
  | _ -> []
;;

let naive_stack_allocation (prog : tag aprogram) : tag aprogram * arg name_envt name_envt =
  match prog with
  | AProgram (expr, tag) ->
    let exp_envt = allocate_aexpr expr 1 in
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
