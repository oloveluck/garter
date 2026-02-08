open Types
open Printf

exception UnifyError of string * Exprs.sourcespan

let rec occurs_in (v : tyvar) (t : ty) : bool =
  match t with
  | TyInt | TyBool | TyString | TyNil -> false
  | TyVar v' -> v = v'
  | TyTuple tys -> List.exists (occurs_in v) tys
  | TyArrow (args, ret) -> List.exists (occurs_in v) args || occurs_in v ret

let compose_subst (s1 : subst) (s2 : subst) : subst =
  let s2_applied = List.map (fun (v, t) -> (v, apply_subst s1 t)) s2 in
  let s1_filtered =
    List.filter (fun (v, _) -> not (List.mem_assoc v s2)) s1
  in
  s1_filtered @ s2_applied

let rec unify (t1 : ty) (t2 : ty) (loc : Exprs.sourcespan) : subst =
  match (t1, t2) with
  | TyInt, TyInt | TyBool, TyBool | TyString, TyString | TyNil, TyNil ->
    []
  | TyVar v, t | t, TyVar v ->
    if TyVar v = t then []
    else if occurs_in v t then
      raise
        (UnifyError
           ( sprintf "Occurs check: %s occurs in %s" (string_of_ty (TyVar v))
               (string_of_ty t)
           , loc ))
    else [(v, t)]
  | TyTuple tys1, TyTuple tys2 ->
    if List.length tys1 <> List.length tys2 then
      raise
        (UnifyError
           ( sprintf "Cannot unify tuples of different lengths: %s and %s"
               (string_of_ty t1) (string_of_ty t2)
           , loc ))
    else unify_many tys1 tys2 loc
  | TyArrow (args1, ret1), TyArrow (args2, ret2) ->
    if List.length args1 <> List.length args2 then
      raise
        (UnifyError
           ( sprintf "Function expects %d arguments, got %d"
               (List.length args1) (List.length args2)
           , loc ))
    else
      let s1 = unify_many args1 args2 loc in
      let s2 = unify (apply_subst s1 ret1) (apply_subst s1 ret2) loc in
      compose_subst s2 s1
  | _ ->
    raise
      (UnifyError
         ( sprintf "Cannot unify %s with %s" (string_of_ty t1) (string_of_ty t2)
         , loc ))

and unify_many (tys1 : ty list) (tys2 : ty list) (loc : Exprs.sourcespan) :
    subst =
  match (tys1, tys2) with
  | [], [] -> []
  | t1 :: rest1, t2 :: rest2 ->
    let s1 = unify t1 t2 loc in
    let s2 =
      unify_many
        (List.map (apply_subst s1) rest1)
        (List.map (apply_subst s1) rest2)
        loc
    in
    compose_subst s2 s1
  | _ ->
    raise
      (UnifyError ("Mismatched number of types in unification", loc))
