open Printf

type tyvar = int

type ty =
  | TyInt
  | TyBool
  | TyString
  | TyNil
  | TyList of ty
  | TyTuple of ty list
  | TyArrow of ty list * ty
  | TyVar of tyvar

type scheme = Forall of tyvar list * ty
type subst = (tyvar * ty) list
type tyenv = (string * scheme) list

let tyvar_counter = ref 0

let fresh_tyvar () : tyvar =
  incr tyvar_counter;
  !tyvar_counter

let fresh_ty () : ty = TyVar (fresh_tyvar ())

let rec apply_subst (s : subst) (t : ty) : ty =
  match t with
  | TyInt | TyBool | TyString | TyNil -> t
  | TyVar v ->
    (match List.assoc_opt v s with
     | Some t' -> apply_subst s t'
     | None -> t)
  | TyList elem -> TyList (apply_subst s elem)
  | TyTuple tys -> TyTuple (List.map (apply_subst s) tys)
  | TyArrow (args, ret) ->
    TyArrow (List.map (apply_subst s) args, apply_subst s ret)

let apply_subst_scheme (s : subst) (sc : scheme) : scheme =
  let (Forall (vars, t)) = sc in
  let s' = List.filter (fun (v, _) -> not (List.mem v vars)) s in
  Forall (vars, apply_subst s' t)

let apply_subst_env (s : subst) (env : tyenv) : tyenv =
  List.map (fun (name, sc) -> (name, apply_subst_scheme s sc)) env

let rec ftv_ty (t : ty) : tyvar list =
  match t with
  | TyInt | TyBool | TyString | TyNil -> []
  | TyVar v -> [v]
  | TyList elem -> ftv_ty elem
  | TyTuple tys -> List.concat_map ftv_ty tys
  | TyArrow (args, ret) -> List.concat_map ftv_ty args @ ftv_ty ret

let ftv_scheme (sc : scheme) : tyvar list =
  let (Forall (vars, t)) = sc in
  List.filter (fun v -> not (List.mem v vars)) (ftv_ty t)

let ftv_env (env : tyenv) : tyvar list =
  List.concat_map (fun (_, sc) -> ftv_scheme sc) env

let rec string_of_ty (t : ty) : string =
  match t with
  | TyInt -> "Int"
  | TyBool -> "Bool"
  | TyString -> "String"
  | TyNil -> "Nil"
  | TyList elem -> sprintf "List(%s)" (string_of_ty elem)
  | TyVar v -> sprintf "'t%d" v
  | TyTuple tys ->
    sprintf "(%s)" (String.concat ", " (List.map string_of_ty tys))
  | TyArrow (args, ret) ->
    sprintf "(%s) -> %s"
      (String.concat ", " (List.map string_of_ty args))
      (string_of_ty ret)

let string_of_scheme (sc : scheme) : string =
  let (Forall (vars, t)) = sc in
  if vars = [] then string_of_ty t
  else
    sprintf "forall %s. %s"
      (String.concat " " (List.map (sprintf "'t%d") vars))
      (string_of_ty t)
