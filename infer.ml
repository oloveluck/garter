open Exprs
open Types
open Unify
open Printf

(* Builtin type environment *)
let builtin_tyenv : tyenv =
  let a1 = fresh_tyvar () in
  let a2 = fresh_tyvar () in
  let a3 = fresh_tyvar () in
  let a4 = fresh_tyvar () in
  [ ("print", Forall ([a1], TyArrow ([TyVar a1], TyVar a1)))
  ; ("input", Forall ([], TyArrow ([TyInt], TyInt)))
  ; ("isnum", Forall ([a2], TyArrow ([TyVar a2], TyBool)))
  ; ("isbool", Forall ([a3], TyArrow ([TyVar a3], TyBool)))
  ; ("istuple", Forall ([a4], TyArrow ([TyVar a4], TyBool)))
  ]

let builtin_tyenv =
  let a5 = fresh_tyvar () in
  builtin_tyenv @ [("printStack", Forall ([a5], TyArrow ([TyVar a5], TyVar a5)))]

let builtin_names =
  List.map fst builtin_tyenv

(* Value restriction: only generalize syntactic values *)
let rec is_value (e : 'a expr) : bool =
  match e with
  | ENumber _ | EBool _ | EString _ | ENil _ | ELambda _ | EId _ -> true
  | ETuple (exprs, _) -> List.for_all is_value exprs
  | _ -> false

(* Instantiate: replace quantified variables with fresh ones *)
let instantiate (sc : scheme) : ty =
  let (Forall (vars, t)) = sc in
  let s = List.map (fun v -> (v, fresh_ty ())) vars in
  apply_subst s t

(* Generalize: quantify free variables not free in env *)
let generalize (env : tyenv) (t : ty) : scheme =
  let env_ftvs = ftv_env env in
  let ty_ftvs = ftv_ty t in
  let vars =
    List.sort_uniq compare
      (List.filter (fun v -> not (List.mem v env_ftvs)) ty_ftvs)
  in
  Forall (vars, t)

(* Extract name from a bind *)
let name_of_bind (b : 'a bind) : (string * 'a) option =
  match b with
  | BName (name, _, a) -> Some (name, a)
  | BBlank _ -> None
  | BTuple _ -> None

(* Infer type of a pattern, returning substitution, pattern type, and new bindings *)
let rec infer_pattern (env : tyenv) (s : subst) (pat : sourcespan pattern)
    : subst * ty * tyenv =
  match pat with
  | PWild _ ->
    let t = fresh_ty () in
    (s, t, [])
  | PVar (name, _) ->
    let t = fresh_ty () in
    (s, t, [(name, Forall ([], t))])
  | PNum (_, _) -> (s, TyInt, [])
  | PBool (_, _) -> (s, TyBool, [])
  | PString (_, _) -> (s, TyString, [])
  | PNil _ -> (s, TyNil, [])
  | PTuple (pats, _) ->
    let s', tys, bindings =
      List.fold_left
        (fun (s_acc, tys_acc, binds_acc) p ->
          let s', t, binds = infer_pattern env s_acc p in
          (s', tys_acc @ [t], binds_acc @ binds))
        (s, [], []) pats
    in
    (s', TyTuple tys, bindings)

(* Infer types for prim1 operations *)
let infer_prim1 (op : prim1) (arg_ty : ty) (loc : sourcespan) (s : subst) :
    subst * ty =
  match op with
  | Add1 | Sub1 ->
    let s' = unify (apply_subst s arg_ty) TyInt loc in
    (compose_subst s' s, TyInt)
  | Not ->
    let s' = unify (apply_subst s arg_ty) TyBool loc in
    (compose_subst s' s, TyBool)
  | Print | PrintStack ->
    (s, apply_subst s arg_ty)
  | IsNum | IsBool | IsTuple ->
    (s, TyBool)

(* Infer types for prim2 operations *)
let infer_prim2 (op : prim2) (t1 : ty) (t2 : ty) (loc : sourcespan)
    (s : subst) : subst * ty =
  match op with
  | Plus | Minus | Times | Div | Mod ->
    let s1 = unify (apply_subst s t1) TyInt loc in
    let s' = compose_subst s1 s in
    let s2 = unify (apply_subst s' t2) TyInt loc in
    let s'' = compose_subst s2 s' in
    (s'', TyInt)
  | And | Or ->
    let s1 = unify (apply_subst s t1) TyBool loc in
    let s' = compose_subst s1 s in
    let s2 = unify (apply_subst s' t2) TyBool loc in
    let s'' = compose_subst s2 s' in
    (s'', TyBool)
  | Greater | GreaterEq | Less | LessEq ->
    let s1 = unify (apply_subst s t1) TyInt loc in
    let s' = compose_subst s1 s in
    let s2 = unify (apply_subst s' t2) TyInt loc in
    let s'' = compose_subst s2 s' in
    (s'', TyBool)
  | Eq ->
    let s1 = unify (apply_subst s t1) (apply_subst s t2) loc in
    let s' = compose_subst s1 s in
    (s', TyBool)
  | CheckSize ->
    let s1 = unify (apply_subst s t2) TyInt loc in
    let s' = compose_subst s1 s in
    (s', TyBool)

(* Main inference function *)
let rec infer_expr (env : tyenv) (s : subst) (e : sourcespan expr) :
    subst * ty =
  match e with
  | ENumber (_, _) -> (s, TyInt)
  | EBool (_, _) -> (s, TyBool)
  | EString (_, _) -> (s, TyString)
  | ENil _ -> (s, TyNil)
  | EId (name, loc) ->
    (match List.assoc_opt name env with
     | Some sc -> (s, instantiate sc)
     | None ->
       raise (UnifyError (sprintf "Unbound identifier: %s" name, loc)))
  | EPrim1 (op, arg, loc) ->
    let s1, arg_ty = infer_expr env s arg in
    infer_prim1 op arg_ty loc s1
  | EPrim2 (op, e1, e2, loc) ->
    let s1, t1 = infer_expr env s e1 in
    let env1 = apply_subst_env s1 env in
    let s2, t2 = infer_expr env1 s1 e2 in
    infer_prim2 op t1 t2 loc s2
  | EIf (cond, thn, els, loc) ->
    let s1, cond_ty = infer_expr env s cond in
    let s2 = unify (apply_subst s1 cond_ty) TyBool loc in
    let s' = compose_subst s2 s1 in
    let env1 = apply_subst_env s' env in
    let s3, thn_ty = infer_expr env1 s' thn in
    let env2 = apply_subst_env s3 env1 in
    let s4, els_ty = infer_expr env2 s3 els in
    let s5 = unify (apply_subst s4 thn_ty) (apply_subst s4 els_ty) loc in
    let s_final = compose_subst s5 s4 in
    (s_final, apply_subst s_final thn_ty)
  | ELambda (binds, body, _) ->
    let arg_tys = List.map (fun _ -> fresh_ty ()) binds in
    let new_bindings =
      List.fold_left2
        (fun acc b t ->
          match name_of_bind b with
          | Some (name, _) -> (name, Forall ([], t)) :: acc
          | None -> acc)
        [] binds arg_tys
    in
    let env' = new_bindings @ env in
    let s1, body_ty = infer_expr env' s body in
    (s1, TyArrow (List.map (apply_subst s1) arg_tys, apply_subst s1 body_ty))
  | EApp (func, args, _, loc) ->
    let s1, func_ty = infer_expr env s func in
    let s2, arg_tys =
      List.fold_left
        (fun (s_acc, tys_acc) arg ->
          let env' = apply_subst_env s_acc env in
          let s', t = infer_expr env' s_acc arg in
          (s', tys_acc @ [t]))
        (s1, []) args
    in
    let ret_ty = fresh_ty () in
    let expected_func_ty = TyArrow (arg_tys, ret_ty) in
    let s3 =
      unify (apply_subst s2 func_ty) (apply_subst s2 expected_func_ty) loc
    in
    let s_final = compose_subst s3 s2 in
    (s_final, apply_subst s_final ret_ty)
  | ELet (bindings, body, _) -> infer_let env s bindings body
  | ELetRec (bindings, body, _) -> infer_letrec env s bindings body
  | ETuple (exprs, _) ->
    let s', tys =
      List.fold_left
        (fun (s_acc, tys_acc) e ->
          let env' = apply_subst_env s_acc env in
          let s', t = infer_expr env' s_acc e in
          (s', tys_acc @ [t]))
        (s, []) exprs
    in
    (s', TyTuple (List.map (apply_subst s') tys))
  | EGetItem (tup, idx, loc) ->
    let s1, tup_ty = infer_expr env s tup in
    let env1 = apply_subst_env s1 env in
    let s2, idx_ty = infer_expr env1 s1 idx in
    let s3 = unify (apply_subst s2 idx_ty) TyInt loc in
    let s' = compose_subst s3 s2 in
    (* Try to resolve statically if index is a literal and tuple type is known *)
    (match (idx, apply_subst s' tup_ty) with
     | ENumber (i, _), TyTuple elems ->
       let i = Int64.to_int i in
       if i >= 0 && i < List.length elems then
         (s', apply_subst s' (List.nth elems i))
       else
         raise
           (UnifyError
              ( sprintf "Tuple index %d out of bounds for %s" i
                  (string_of_ty (apply_subst s' tup_ty))
              , loc ))
     | _ -> (s', fresh_ty ()))
  | ESetItem (tup, idx, newval, loc) ->
    let s1, _tup_ty = infer_expr env s tup in
    let env1 = apply_subst_env s1 env in
    let s2, idx_ty = infer_expr env1 s1 idx in
    let s3 = unify (apply_subst s2 idx_ty) TyInt loc in
    let s' = compose_subst s3 s2 in
    let env2 = apply_subst_env s' env1 in
    let s4, newval_ty = infer_expr env2 s' newval in
    (s4, apply_subst s4 newval_ty)
  | ESeq (e1, e2, _) ->
    let s1, _ = infer_expr env s e1 in
    let env1 = apply_subst_env s1 env in
    infer_expr env1 s1 e2
  | EMatch (scrutinee, cases, loc) -> infer_match env s scrutinee cases loc

(* Infer let bindings with generalization and value restriction *)
and infer_let (env : tyenv) (s : subst) (bindings : sourcespan binding list)
    (body : sourcespan expr) : subst * ty =
  let s', env' =
    List.fold_left
      (fun (s_acc, env_acc) (bind, rhs, _) ->
        let env_applied = apply_subst_env s_acc env_acc in
        let s1, rhs_ty = infer_expr env_applied s_acc rhs in
        let rhs_ty = apply_subst s1 rhs_ty in
        let sc =
          if is_value rhs then generalize (apply_subst_env s1 env_applied) rhs_ty
          else Forall ([], rhs_ty)
        in
        let env_new =
          match name_of_bind bind with
          | Some (name, _) -> (name, sc) :: env_acc
          | None ->
            (* For BTuple bindings, add all contained names with fresh types *)
            let rec add_tuple_binds b ty env =
              match b with
              | BBlank _ -> env
              | BName (name, _, _) -> (name, Forall ([], ty)) :: env
              | BTuple (binds, _) ->
                (match ty with
                 | TyTuple tys when List.length tys = List.length binds ->
                   List.fold_left2
                     (fun env b t -> add_tuple_binds b t env)
                     env binds tys
                 | _ ->
                   (* Can't statically resolve tuple destructuring; give fresh types *)
                   List.fold_left
                     (fun env b -> add_tuple_binds b (fresh_ty ()) env)
                     env binds)
            in
            add_tuple_binds bind rhs_ty env_acc
        in
        (s1, env_new))
      (s, env) bindings
  in
  let env_applied = apply_subst_env s' env' in
  infer_expr env_applied s' body

(* Infer let-rec bindings (mutual recursion) *)
and infer_letrec (env : tyenv) (s : subst)
    (bindings : sourcespan binding list) (body : sourcespan expr) : subst * ty
    =
  (* Step 1: Create fresh type variables for each binding *)
  let fresh_vars =
    List.map
      (fun (bind, _, _) ->
        let t = fresh_ty () in
        match name_of_bind bind with
        | Some (name, _) -> (name, t)
        | None -> ("_", t))
      bindings
  in
  (* Step 2: Add monomorphic assumptions to env *)
  let env' =
    List.fold_left
      (fun env (name, t) -> (name, Forall ([], t)) :: env)
      env fresh_vars
  in
  (* Step 3: Infer each RHS in the extended env *)
  let s', inferred_tys =
    List.fold_left
      (fun (s_acc, tys_acc) (_, rhs, _) ->
        let env_applied = apply_subst_env s_acc env' in
        let s1, t = infer_expr env_applied s_acc rhs in
        (s1, tys_acc @ [t]))
      (s, []) bindings
  in
  (* Step 4: Unify fresh vars with inferred types *)
  let s'' =
    List.fold_left2
      (fun s_acc (_, fresh_t) inferred_t ->
        let s1 =
          unify (apply_subst s_acc fresh_t)
            (apply_subst s_acc inferred_t)
            (Lexing.dummy_pos, Lexing.dummy_pos)
        in
        compose_subst s1 s_acc)
      s' fresh_vars inferred_tys
  in
  (* Step 5: Generalize and add to env *)
  let env_generalized =
    List.fold_left
      (fun env (name, t) ->
        let t' = apply_subst s'' t in
        let sc = generalize (apply_subst_env s'' env) t' in
        (name, sc) :: env)
      env fresh_vars
  in
  let env_applied = apply_subst_env s'' env_generalized in
  infer_expr env_applied s'' body

(* Infer match expression with permissive pattern unification *)
and infer_match (env : tyenv) (s : subst) (scrutinee : sourcespan expr)
    (cases : (sourcespan pattern * sourcespan expr) list) (loc : sourcespan) :
    subst * ty =
  let s1, scrut_ty = infer_expr env s scrutinee in
  let result_ty = fresh_ty () in
  let s_final =
    List.fold_left
      (fun s_acc (pat, body) ->
        let env_acc = apply_subst_env s_acc env in
        let s2, pat_ty, new_bindings = infer_pattern env_acc s_acc pat in
        (* Permissive: try to unify pattern type with scrutinee, but don't fail *)
        let s3 =
          try
            let su =
              unify
                (apply_subst s2 pat_ty)
                (apply_subst s2 scrut_ty)
                loc
            in
            compose_subst su s2
          with UnifyError _ -> s2
        in
        let body_env =
          List.map
            (fun (name, Forall (vs, t)) ->
              (name, Forall (vs, apply_subst s3 t)))
            new_bindings
          @ apply_subst_env s3 env
        in
        let s4, body_ty = infer_expr body_env s3 body in
        (* All branches must agree on result type *)
        let s5 =
          unify
            (apply_subst s4 result_ty)
            (apply_subst s4 body_ty)
            loc
        in
        compose_subst s5 s4)
      s1 cases
  in
  (s_final, apply_subst s_final result_ty)

(* Infer a declaration group (treated as letrec) *)
let infer_decl_group (env : tyenv) (s : subst)
    (decls : sourcespan decl list) : subst * tyenv =
  (* Create fresh type variables for each function *)
  let fresh_vars =
    List.map
      (fun (DFun (name, _, _, _)) -> (name, fresh_ty ()))
      decls
  in
  (* Add monomorphic assumptions *)
  let env' =
    List.fold_left
      (fun env (name, t) -> (name, Forall ([], t)) :: env)
      env fresh_vars
  in
  (* Infer each function body *)
  let s', inferred_tys =
    List.fold_left
      (fun (s_acc, tys_acc) (DFun (_, args, body, _)) ->
        let arg_tys = List.map (fun _ -> fresh_ty ()) args in
        let new_bindings =
          List.fold_left2
            (fun acc b t ->
              match name_of_bind b with
              | Some (name, _) -> (name, Forall ([], t)) :: acc
              | None -> acc)
            [] args arg_tys
        in
        let env_body = new_bindings @ apply_subst_env s_acc env' in
        let s1, body_ty = infer_expr env_body s_acc body in
        let func_ty =
          TyArrow
            (List.map (apply_subst s1) arg_tys, apply_subst s1 body_ty)
        in
        (s1, tys_acc @ [func_ty]))
      (s, []) decls
  in
  (* Unify fresh vars with inferred types *)
  let s'' =
    List.fold_left2
      (fun s_acc (_, fresh_t) inferred_t ->
        let s1 =
          unify (apply_subst s_acc fresh_t)
            (apply_subst s_acc inferred_t)
            (Lexing.dummy_pos, Lexing.dummy_pos)
        in
        compose_subst s1 s_acc)
      s' fresh_vars inferred_tys
  in
  (* Generalize and build the extended env *)
  let env_result =
    List.fold_left
      (fun env (name, t) ->
        let t' = apply_subst s'' t in
        let sc = generalize (apply_subst_env s'' env) t' in
        (name, sc) :: env)
      env fresh_vars
  in
  (s'', env_result)

(* Type check a whole program *)
let type_check_program (prog : sourcespan program) :
    sourcespan program Phases.fallible =
  try
    let (Program (decl_groups, body, _)) = prog in
    (* Start with builtin environment *)
    let env = builtin_tyenv in
    (* Process declaration groups *)
    let s, env' =
      List.fold_left
        (fun (s_acc, env_acc) group ->
          (* Skip builtin wrapper declarations *)
          let non_builtin =
            List.filter
              (fun (DFun (name, _, _, _)) ->
                not (List.mem name builtin_names))
              group
          in
          if non_builtin = [] then (s_acc, env_acc)
          else infer_decl_group env_acc s_acc non_builtin)
        ([], env) decl_groups
    in
    (* Infer the body *)
    let env_applied = apply_subst_env s env' in
    let _s_final, _body_ty = infer_expr env_applied s body in
    Ok prog
  with
  | UnifyError (msg, loc) ->
    Error [Errors.TypeError (msg, loc)]

(* Type check a program, returning the substitution and type environment for LSP use *)
let type_check_program_with_env (prog : sourcespan program) :
    (sourcespan program * subst * tyenv, exn list) result =
  try
    let (Program (decl_groups, body, _)) = prog in
    let env = builtin_tyenv in
    let s, env' =
      List.fold_left
        (fun (s_acc, env_acc) group ->
          let non_builtin =
            List.filter
              (fun (DFun (name, _, _, _)) ->
                not (List.mem name builtin_names))
              group
          in
          if non_builtin = [] then (s_acc, env_acc)
          else infer_decl_group env_acc s_acc non_builtin)
        ([], env) decl_groups
    in
    let env_applied = apply_subst_env s env' in
    let s_final, _body_ty = infer_expr env_applied s body in
    let env_final = apply_subst_env s_final env' in
    Ok (prog, s_final, env_final)
  with
  | UnifyError (msg, loc) ->
    Error [Errors.TypeError (msg, loc)]
