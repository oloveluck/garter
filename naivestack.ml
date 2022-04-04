open Errors
open Phases
open Exprs
open Assembly
open Find
open Freevars

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

let rec allocate_aexpr (expr : tag aexpr) (si : int) : arg envt =
  match expr with
  | ALet (name, rhs, body, _) ->
    [ name, RegOffset (~-si * 8, RBP) ]
    @ allocate_cexpr rhs (si + 1) []
    @ allocate_aexpr body (si + 1)
  | ACExpr c -> allocate_cexpr c si []
  | ASeq (first, rest, _) -> allocate_cexpr first si [] @ allocate_aexpr rest si
  (* make sure name is bound to the correct closure offset *)
  | ALetRec (bindings, body, _) ->
    let bindings_env =
      List.mapi
        (fun index (name, value) ->
          (* [ name, RegOffset (~-(si + index) * 8, RBP) ] *)
          [ name, RegOffset (~-8 * (si + index), RBP) ]
          @ allocate_cexpr value (si + 1 + index) [ name ])
        bindings
      |> List.flatten
    in
    let body_env = allocate_aexpr body si in
    bindings_env @ body_env

and allocate_cexpr (expr : tag cexpr) (si : int) (free_env : string list) : arg envt =
  match expr with
  | CIf (_, t, e, _) -> allocate_aexpr t si @ allocate_aexpr e si
  | CLambda (args, body, _) ->
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
    arg_bindings @ free_bindings @ allocate_aexpr body (List.length frees * 8)
  | _ -> []
;;

let naive_stack_allocation (prog : tag aprogram) : tag aprogram * arg envt =
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
