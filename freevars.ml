open Exprs
open Errors
module StringSet = Set.Make (String)
open Printf
open ExtLib

let rec free_vars (e : 'a aexpr) : string list = StringSet.elements (fv_A e)

and fv_A (e : 'a aexpr) : StringSet.t =
  match e with
  | ASeq (first, rest, _) -> StringSet.union (fv_C first) (fv_A rest)
  | ALet (name, value, body, _) ->
    StringSet.union (fv_C value) (StringSet.remove name (fv_A body))
  | ALetRec (bindings, body, _) ->
    let binds_env = StringSet.of_list (List.map (fun (b, _) -> b) bindings) in
    let bindings_frees = List.map (fun (_, value) -> fv_C value) bindings in
    let body_frees = fv_A body in
    let binding_frees_set =
      List.fold_right (fun a b -> StringSet.union b a) bindings_frees StringSet.empty
    in
    StringSet.diff (StringSet.union binding_frees_set body_frees) binds_env
  | ACExpr c -> fv_C c

and fv_I (e : 'a immexpr) : StringSet.t =
  match e with
  | ImmId (id, _) -> StringSet.singleton id
  | ImmNum _ | ImmBool _ | ImmNil _ | ImmString _ -> StringSet.empty

and fv_C (e : 'a cexpr) : StringSet.t =
  match e with
  | CIf (c, t, e, _) ->
    let frees_te = StringSet.union (fv_A t) (fv_A e) in
    StringSet.union (fv_I c) frees_te
  | CGetItem (tup, num, _) -> StringSet.union (fv_I tup) (fv_I num)
  | CSetItem (tup, num, _new, _) ->
    let tn_frees = StringSet.union (fv_I tup) (fv_I num) in
    StringSet.union tn_frees (fv_I _new)
  | CApp (_fun, args, _, _) ->
    StringSet.union
      (fv_I _fun)
      (List.fold_right
         (fun a b -> StringSet.union a b)
         (List.map (fun a -> fv_I a) args)
         StringSet.empty)
  | CLambda (args, body, _) ->
    let args_env = StringSet.of_list args in
    StringSet.diff (fv_A body) args_env
  | CImmExpr i -> fv_I i
  | CPrim1 (_, exp, _) -> fv_I exp
  | CPrim2 (_, e1, e2, _) -> StringSet.union (fv_I e1) (fv_I e2)
  | CTuple (items, _) ->
    List.fold_right
      (fun a b -> StringSet.union a b)
      (List.map (fun a -> fv_I a) items)
      StringSet.empty

and cache_I (immexpr : tag immexpr) : (tag * StringSet.t) immexpr =
  match immexpr with
  | ImmNum (n, tag) -> ImmNum (n, (tag, StringSet.empty))
  | ImmBool (b, tag) -> ImmBool (b, (tag, StringSet.empty))
  | ImmId (id, tag) -> ImmId (id, (tag, fv_I immexpr))
  | ImmNil tag -> ImmNil (tag, StringSet.empty)
  | ImmString (s, tag) -> ImmString (s, (tag, StringSet.empty))

and cache_C (expr : tag cexpr) : (tag * StringSet.t) cexpr =
  match expr with
  | CIf (immexpr, aexpr1, aexpr2, tag) ->
    CIf (cache_I immexpr, cache_A aexpr1, cache_A aexpr2, (tag, fv_C expr))
  | CApp (_fun, args, call_type, tag) ->
    CApp
      (cache_I _fun, List.map (fun arg -> cache_I arg) args, call_type, (tag, fv_C expr))
  | CLambda (args, body, tag) -> CLambda (args, cache_A body, (tag, fv_C expr))
  | CGetItem (imm1, imm2, tag) -> CGetItem (cache_I imm1, cache_I imm2, (tag, fv_C expr))
  | CSetItem (imm1, imm2, imm3, tag) ->
    CSetItem (cache_I imm1, cache_I imm2, cache_I imm3, (tag, fv_C expr))
  | CPrim1 (op, imm, tag) -> CPrim1 (op, cache_I imm, (tag, fv_C expr))
  | CPrim2 (op, imm1, imm2, tag) ->
    CPrim2 (op, cache_I imm1, cache_I imm2, (tag, fv_C expr))
  | CTuple (items, tag) ->
    CTuple (List.map (fun arg -> cache_I arg) items, (tag, fv_C expr))
  | CImmExpr imm -> CImmExpr (cache_I imm)

and cache_bindings (bindings : (string * tag cexpr) list)
    : (string * (tag * StringSet.t) cexpr) list
  =
  match bindings with
  | (name, cexpr) :: rest ->
    let cached_expr = cache_C cexpr in
    (name, cached_expr) :: cache_bindings rest
  | [] -> []

and cache_A (expr : tag aexpr) : (tag * StringSet.t) aexpr =
  match expr with
  | ALet (name, value, body, tag) ->
    ALet (name, cache_C value, cache_A body, (tag, fv_A expr))
  | ALetRec (bindings, body, tag) ->
    ALetRec (cache_bindings bindings, cache_A body, (tag, fv_A expr))
  | ACExpr c -> ACExpr (cache_C c)
  | ASeq (cexpr, aexpr, tag) -> ASeq (cache_C cexpr, cache_A aexpr, (tag, fv_A expr))
;;
