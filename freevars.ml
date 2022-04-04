open Exprs
open Errors
module StringSet = Set.Make (String)
open Printf
open ExtLib

(* let free_vars (e : 'a aexpr) (env : string list) : string list =
  let rec helpA (e : 'a aexpr) (env : string list) : string list =
    match e with
    | ASeq (cexpr, rest, _) -> helpC cexpr env @ helpA rest env
    | ALet (name, value, body, _) -> helpC value env @ helpA body (env @ [ name ])
    (*rec name needs to be bound, not free*)
    | ALetRec (bindings, body, _) ->
      let binding_frees =
        List.map (fun (name, value) -> helpC value ([ name ] @ env)) bindings
        |> List.flatten
      in
      binding_frees @ helpA body env
    | ACExpr cexpr -> helpC cexpr env
  and helpI (e : 'a immexpr) (env : string list) : string list =
    match e with
    | ImmId (name, _) ->
      (match List.find_opt (fun s -> s = name) env with
      | Some _ -> []
      | None -> [ name ])
    | _ -> []
  and helpC (e : 'a cexpr) (env : string list) : string list =
    match e with
    | CIf (c, t, e, _) -> helpI c env @ helpA t env @ helpA e env
    | CPrim1 (op, imm, _) -> helpI imm env
    | CPrim2 (op, imm1, imm2, _) -> helpI imm1 env @ helpI imm2 env
    | CApp (func, args, _, _) ->
      helpI func env @ (List.map (fun a -> helpI a env) args |> List.flatten)
    | CImmExpr imm -> helpI imm env
    | CTuple (values, _) -> List.map (fun v -> helpI v env) values |> List.flatten
    | CGetItem (tup, num, _) -> helpI tup env @ helpI num env
    | CSetItem (tup, num, _new, _) -> helpI tup env @ helpI num env @ helpI _new env
    | CLambda (args, body, t) -> helpL (CLambda (args, body, t)) env
  and helpL (CLambda (binds, body, _) : 'a cexpr) (env : string list) : string list =
    helpA body binds @ env
  in
  StringSet.elements (StringSet.of_list (helpA e env))
;; *)
(* raise (NotYetImplemented "Implement free_vars for expressions") *)

let free_vars (e : 'a aexpr) (env : string list) : string list =
  let rec helpA (e : 'a aexpr) (env : StringSet.t) : StringSet.t =
    match e with
    | ASeq (first, rest, _) -> StringSet.union (helpC first env) (helpA rest env)
    | ALet (name, value, body, _) ->
      StringSet.union (helpC value env) (helpA body (StringSet.add name env))
    | ALetRec (bindings, body, _) ->
      let binding_frees =
        List.fold_right
          (fun a b -> StringSet.union a b)
          (List.map (fun (name, value) -> helpC value (StringSet.add name env)) bindings)
          StringSet.empty
      in
      helpA body (StringSet.union binding_frees env)
    | ACExpr c -> helpC c env
  and helpI (e : 'a immexpr) (env : StringSet.t) : StringSet.t =
    match e with
    | ImmId (id, _) ->
      (match StringSet.find_opt id env with
      | Some _ -> StringSet.empty
      | None -> StringSet.singleton id)
    | _ -> StringSet.empty
  and helpC (e : 'a cexpr) (env : StringSet.t) : StringSet.t =
    match e with
    | CIf (c, t, e, _) ->
      let frees_te = StringSet.union (helpA t env) (helpA e env) in
      StringSet.union (helpI c env) frees_te
    | CGetItem (tup, num, _) -> StringSet.union (helpI tup env) (helpI num env)
    | CSetItem (tup, num, _new, _) ->
      let tn_frees = StringSet.union (helpI tup env) (helpI num env) in
      StringSet.union tn_frees (helpI _new env)
    | CApp (_fun, args, _, _) ->
      StringSet.union
        (helpI _fun env)
        (List.fold_right
           (fun a b -> StringSet.union a b)
           (List.map (fun a -> helpI a env) args)
           StringSet.empty)
    | CLambda (args, body, _) ->
      printf "Getting Frees For Lambda with env: %s" (dump env);
      let args_env = StringSet.of_list args in
      helpA body args_env
    | CImmExpr i -> helpI i env
    | CPrim1 (_, exp, _) -> helpI exp env
    | CPrim2 (_, e1, e2, _) -> StringSet.union (helpI e1 env) (helpI e2 env)
    | CTuple (items, _) ->
      List.fold_right
        (fun a b -> StringSet.union a b)
        (List.map (fun a -> helpI a env) items)
        StringSet.empty
  in
  StringSet.elements (helpA e (StringSet.of_list env))
;;
