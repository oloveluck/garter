open Printf
open Pretty
open Phases
open Exprs
open Assembly
open Naivestack
open Freevars
open Errors
open ExtLib
open Wrapnatives
module StringSet = Set.Make (String)

type 'a name_envt = (string * 'a) list
type 'a tag_envt = (tag * 'a) list

let print_env env how =
  debug_printf "Env is\n";
  List.iter (fun (id, bind) -> debug_printf "  %s -> %s\n" id (how bind)) env
;;

let const_true = HexConst 0xFFFFFFFFFFFFFFFFL
let const_false = HexConst 0x7FFFFFFFFFFFFFFFL
let bool_mask = HexConst 0x8000000000000000L
let bool_tag = 0x0000000000000007L
let bool_tag_mask = 0x0000000000000007L
let num_tag = 0x0000000000000000L
let num_tag_mask = 0x0000000000000001L
let closure_tag = 0x0000000000000005L
let closure_tag_mask = 0x0000000000000007L
let tuple_tag = 0x0000000000000001L
let tuple_tag_mask = 0x0000000000000007L
let const_nil = HexConst tuple_tag
let err_COMP_NOT_NUM = 1L
let err_ARITH_NOT_NUM = 2L
let err_LOGIC_NOT_BOOL = 3L
let err_IF_NOT_BOOL = 4L
let err_OVERFLOW = 5L
let err_GET_NOT_TUPLE = 6L
let err_GET_LOW_INDEX = 7L
let err_GET_HIGH_INDEX = 8L
let err_NIL_DEREF = 9L
let err_OUT_OF_MEMORY = 10L
let err_SET_NOT_TUPLE = 11L
let err_SET_LOW_INDEX = 12L
let err_SET_HIGH_INDEX = 13L
let err_CALL_NOT_CLOSURE = 14L
let err_CALL_ARITY_ERR = 15L
let dummy_span = Lexing.dummy_pos, Lexing.dummy_pos
let first_six_args_registers = [ RDI; RSI; RDX; RCX; R8; R9 ]
let heap_reg = R15
let scratch_reg = R11

(* you can add any functions or data defined by the runtime here for future use *)
let initial_val_env = []
let prim_bindings = []
let native_fun_bindings = []
let initial_fun_env = prim_bindings @ native_fun_bindings

(* You may find some of these helpers useful *)
let error_code_to_str (code : int64) : string =
  if code = err_ARITH_NOT_NUM
  then "?err_arith_not_num"
  else if code = err_COMP_NOT_NUM
  then "?err_comp_not_num"
  else if code = err_LOGIC_NOT_BOOL
  then "?err_logic_not_bool"
  else if code = err_IF_NOT_BOOL
  then "?err_if_not_bool"
  else if code = err_OVERFLOW
  then "?err_overflow"
  else "?err_unexpected"
;;

let callee_end_function = [ IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet ]
let error_code_to_label (code : int64) : arg = Label (error_code_to_str code)

let check_is_bool (error_code : int64) =
  [ ITest (Reg RAX, HexConst bool_tag); IJz (error_code_to_label error_code) ]
;;

let check_is_number (error_code : int64) =
  [ IMov (Reg RSI, Reg RAX)
  ; IMov (Reg RAX, Const num_tag_mask)
  ; ITest (Reg RSI, Reg RAX)
  ]
  @ [ IJnz (error_code_to_label error_code) ]
  @ [ IMov (Reg RAX, Reg RSI) ]
;;

let is_bool_instructions (tag : tag) =
  (* [ IMov (Reg RSI, Reg RAX)
  ; IMov (Reg RAX, const_false)
  ; IMov (Reg RDI, Reg RAX)
  ; IMov (Reg RAX, Reg RSI)
  ; IShl (Reg RAX, Sized (BYTE_PTR, Const 63L))
  ; IOr (Reg RAX, Reg RDI)
  ]
   *)
  let d = sprintf "is_bool_done_%d" tag in
  [ IMov (Reg RSI, Reg RAX)
  ; IMov (Reg RAX, Const bool_tag_mask)
  ; IAnd (Reg RAX, Reg RSI)
  ; IMov (Reg RDI, Const 7L)
  ; ICmp (Reg RAX, Reg RDI)
  ; IMov (Reg RAX, const_true)
  ; IJe (Label d)
  ; IMov (Reg RAX, const_false)
  ; ILabel d
  ]
;;

let funv_to_op (funv : 'a immexpr) : prim1 =
  match funv with
  | ImmId ("add1", _) -> Add1
  | ImmId ("sub1", _) -> Sub1
  | ImmId ("isbool", _) -> IsBool
  | ImmId ("isnum", _) -> IsNum
  | ImmId ("istuple", _) -> IsTuple
  | ImmId (name, _) -> raise (InternalCompilerError (sprintf "tried to call %s" name))
  | _ -> raise (InternalCompilerError "tried to create operation function for non-id")
;;

let is_tuple_instructions (tag : tag) =
  let d = sprintf "is_tup_done_%d" tag in
  [ IMov (Reg RSI, Reg RAX)
  ; IMov (Reg RAX, Const 15L)
  ; IAnd (Reg RAX, Reg RSI)
  ; IMov (Reg RDI, Const 1L)
  ; ICmp (Reg RAX, Reg RDI)
  ; IMov (Reg RAX, const_true)
  ; IJe (Label d)
  ; IMov (Reg RAX, const_false)
  ; ILabel d
  ]
;;

let function_prelude (stack_depth : int) =
  [ IPush (Reg RBP) ]
  @ [ IMov (Reg RBP, Reg RSP) ]
  @ [ ISub (Reg RSP, Const (Int64.mul (Int64.of_int stack_depth) 8L)) ]
;;

let function_postlude = [ IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet ]

let error_codes =
  [ err_COMP_NOT_NUM
  ; err_ARITH_NOT_NUM
  ; err_LOGIC_NOT_BOOL
  ; err_IF_NOT_BOOL
  ; err_OVERFLOW
  ]
;;

let generate_error_instructions (error_codes : int64 list) : instruction list =
  let generate_error_label (error_code : int64) (labels : instruction list)
      : instruction list
    =
    let instructions =
      [ IMov (Reg RDI, Const error_code); ICall (Label "?error") ] @ callee_end_function
    in
    (ILabel (error_code_to_str error_code) :: instructions) @ labels
  in
  List.fold_right generate_error_label error_codes []
;;

let print_instructions =
  let instructions = [ IMov (Reg RDI, Reg RAX); ICall (Label "?print") ] in
  instructions
;;

let print_stack_instructions =
  let instructions =
    [ IMov (Reg RDI, Reg RAX)
    ; IMov (Reg RSI, Reg RSP)
    ; IMov (Reg RDX, Reg RBP)
    ; ICall (Label "?print_stack")
    ]
  in
  instructions
;;

let rec find ls x =
  match ls with
  | [] -> raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest -> if y = x then v else find rest x
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

let rec replicate x i = if i = 0 then [] else x :: replicate x (i - 1)

let rec find_decl (ds : 'a decl list) (name : string) : 'a decl option =
  match ds with
  | [] -> None
  | (DFun (fname, _, _, _) as d) :: ds_rest ->
    if name = fname then Some d else find_decl ds_rest name
;;

let rec find_one (l : 'a list) (elt : 'a) : bool =
  match l with
  | [] -> false
  | x :: xs -> elt = x || find_one xs elt
;;

let rec find_dup (l : 'a list) : 'a option =
  match l with
  | [] -> None
  | [ x ] -> None
  | x :: xs -> if find_one xs x then Some x else find_dup xs
;;

let rec find_opt (env : 'a name_envt) (elt : string) : 'a option =
  match env with
  | [] -> None
  | (x, v) :: rst -> if x = elt then Some v else find_opt rst elt
;;

(* Prepends a list-like env onto an name_envt *)
let merge_envs list_env1 list_env2 = list_env1 @ list_env2

(* Combines two name_envts into one, preferring the first one *)
let prepend env1 env2 =
  let rec help env1 env2 =
    match env1 with
    | [] -> env2
    | ((k, _) as fst) :: rst ->
      let rst_prepend = help rst env2 in
      if List.mem_assoc k env2 then rst_prepend else fst :: rst_prepend
  in
  help env1 env2
;;

let env_keys e = List.map fst e

(* Scope_info stores the location where something was defined,
   and if it was a function declaration, then its type arity and argument arity *)
type scope_info = sourcespan * int option * int option

let is_well_formed (p : sourcespan program) : sourcespan program fallible =
  let rec wf_E e (env : scope_info name_envt) =
    debug_printf "In wf_E: %s\n" (ExtString.String.join ", " (env_keys env));
    match e with
    | ESeq (e1, e2, _) -> wf_E e1 env @ wf_E e2 env
    | ETuple (es, _) -> List.concat (List.map (fun e -> wf_E e env) es)
    | EGetItem (e, idx, pos) -> wf_E e env @ wf_E idx env
    | ESetItem (e, idx, newval, pos) -> wf_E e env @ wf_E idx env @ wf_E newval env
    | ENil _ -> []
    | EBool _ -> []
    | ENumber (n, loc) ->
      if n > Int64.div Int64.max_int 2L || n < Int64.div Int64.min_int 2L
      then [ Overflow (n, loc) ]
      else []
    | EId (x, loc) -> if find_one (List.map fst env) x then [] else [ UnboundId (x, loc) ]
    | EPrim1 (_, e, _) -> wf_E e env
    | EPrim2 (_, l, r, _) -> wf_E l env @ wf_E r env
    | EIf (c, t, f, _) -> wf_E c env @ wf_E t env @ wf_E f env
    | ELet (bindings, body, _) ->
      let rec find_locs x (binds : 'a bind list) : 'a list =
        match binds with
        | [] -> []
        | BBlank _ :: rest -> find_locs x rest
        | BName (y, _, loc) :: rest ->
          if x = y then loc :: find_locs x rest else find_locs x rest
        | BTuple (binds, _) :: rest -> find_locs x binds @ find_locs x rest
      in
      let rec find_dupes (binds : 'a bind list) : exn list =
        match binds with
        | [] -> []
        | BBlank _ :: rest -> find_dupes rest
        | BName (x, _, def) :: rest ->
          List.map (fun use -> DuplicateId (x, use, def)) (find_locs x rest)
          @ find_dupes rest
        | BTuple (binds, _) :: rest -> find_dupes (binds @ rest)
      in
      let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) bindings) in
      let rec process_binds (rem_binds : 'a bind list) (env : scope_info name_envt) =
        match rem_binds with
        | [] -> env, []
        | BBlank _ :: rest -> process_binds rest env
        | BTuple (binds, _) :: rest -> process_binds (binds @ rest) env
        | BName (x, allow_shadow, xloc) :: rest ->
          let shadow =
            if allow_shadow
            then []
            else (
              match find_opt env x with
              | None -> []
              | Some (existing, _, _) -> [ ShadowId (x, xloc, existing) ])
          in
          let new_env = (x, (xloc, None, None)) :: env in
          let newer_env, errs = process_binds rest new_env in
          newer_env, shadow @ errs
      in
      let rec process_bindings bindings (env : scope_info name_envt) =
        match bindings with
        | [] -> env, []
        | (b, e, loc) :: rest ->
          let errs_e = wf_E e env in
          let env', errs = process_binds [ b ] env in
          let env'', errs' = process_bindings rest env' in
          env'', errs @ errs_e @ errs'
      in
      let env2, errs = process_bindings bindings env in
      dupeIds @ errs @ wf_E body env2
    | EApp (func, args, native, loc) ->
      let rec_errors = List.concat (List.map (fun e -> wf_E e env) (func :: args)) in
      (match func with
      | EId (funname, _) ->
        (match find_opt env funname with
        | Some (_, _, Some arg_arity) ->
          let actual = List.length args in
          if actual != arg_arity then [ Arity (arg_arity, actual, loc) ] else []
        | _ -> [])
      | _ -> [])
      @ rec_errors
    | ELetRec (binds, body, _) ->
      let nonfuns =
        List.find_all
          (fun b ->
            match b with
            | BName _, ELambda _, _ -> false
            | _ -> true)
          binds
      in
      let nonfun_errs =
        List.map (fun (b, _, where) -> LetRecNonFunction (b, where)) nonfuns
      in
      let rec find_locs x (binds : 'a bind list) : 'a list =
        match binds with
        | [] -> []
        | BBlank _ :: rest -> find_locs x rest
        | BName (y, _, loc) :: rest ->
          if x = y then loc :: find_locs x rest else find_locs x rest
        | BTuple (binds, _) :: rest -> find_locs x binds @ find_locs x rest
      in
      let rec find_dupes (binds : 'a bind list) : exn list =
        match binds with
        | [] -> []
        | BBlank _ :: rest -> find_dupes rest
        | BName (x, _, def) :: rest ->
          List.map (fun use -> DuplicateId (x, use, def)) (find_locs x rest)
        | BTuple (binds, _) :: rest -> find_dupes (binds @ rest)
      in
      let dupeIds = find_dupes (List.map (fun (b, _, _) -> b) binds) in
      let rec process_binds
          (rem_binds : sourcespan bind list)
          (env : scope_info name_envt)
        =
        match rem_binds with
        | [] -> env, []
        | BBlank _ :: rest -> process_binds rest env
        | BTuple (binds, _) :: rest -> process_binds (binds @ rest) env
        | BName (x, allow_shadow, xloc) :: rest ->
          let shadow =
            if allow_shadow
            then []
            else (
              match find_opt env x with
              | None -> []
              | Some (existing, _, _) ->
                if xloc = existing then [] else [ ShadowId (x, xloc, existing) ])
          in
          let new_env = (x, (xloc, None, None)) :: env in
          let newer_env, errs = process_binds rest new_env in
          newer_env, shadow @ errs
      in
      let env, bind_errs = process_binds (List.map (fun (b, _, _) -> b) binds) env in
      let rec process_bindings bindings env =
        match bindings with
        | [] -> env, []
        | (b, e, loc) :: rest ->
          let env, errs = process_binds [ b ] env in
          let errs_e = wf_E e env in
          let env', errs' = process_bindings rest env in
          env', errs @ errs_e @ errs'
      in
      let new_env, binding_errs = process_bindings binds env in
      let rhs_problems = List.map (fun (_, rhs, _) -> wf_E rhs new_env) binds in
      let body_problems = wf_E body new_env in
      nonfun_errs
      @ dupeIds
      @ bind_errs
      @ binding_errs
      @ List.flatten rhs_problems
      @ body_problems
    | ELambda (binds, body, _) ->
      let rec dupe x args =
        match args with
        | [] -> None
        | BName (y, _, loc) :: _ when x = y -> Some loc
        | BTuple (binds, _) :: rest -> dupe x (binds @ rest)
        | _ :: rest -> dupe x rest
      in
      let rec process_args rem_args =
        match rem_args with
        | [] -> []
        | BBlank _ :: rest -> process_args rest
        | BName (x, _, loc) :: rest ->
          (match dupe x rest with
          | None -> []
          | Some where -> [ DuplicateId (x, where, loc) ])
          @ process_args rest
        | BTuple (binds, loc) :: rest -> process_args (binds @ rest)
      in
      let rec flatten_bind (bind : sourcespan bind) : (string * scope_info) list =
        match bind with
        | BBlank _ -> []
        | BName (x, _, xloc) -> [ x, (xloc, None, None) ]
        | BTuple (args, _) -> List.concat (List.map flatten_bind args)
      in
      process_args binds
      @ wf_E body (merge_envs (List.concat (List.map flatten_bind binds)) env)
  and wf_D d (env : scope_info name_envt) (tyenv : StringSet.t) =
    match d with
    | DFun (_, args, body, _) ->
      let rec dupe x args =
        match args with
        | [] -> None
        | BName (y, _, loc) :: _ when x = y -> Some loc
        | BTuple (binds, _) :: rest -> dupe x (binds @ rest)
        | _ :: rest -> dupe x rest
      in
      let rec process_args rem_args =
        match rem_args with
        | [] -> []
        | BBlank _ :: rest -> process_args rest
        | BName (x, _, loc) :: rest ->
          (match dupe x rest with
          | None -> []
          | Some where -> [ DuplicateId (x, where, loc) ])
          @ process_args rest
        | BTuple (binds, loc) :: rest -> process_args (binds @ rest)
      in
      let rec arg_env args (env : scope_info name_envt) =
        match args with
        | [] -> env
        | BBlank _ :: rest -> arg_env rest env
        | BName (name, _, loc) :: rest -> (name, (loc, None, None)) :: arg_env rest env
        | BTuple (binds, _) :: rest -> arg_env (binds @ rest) env
      in
      process_args args @ wf_E body (arg_env args env)
  and wf_G (g : sourcespan decl list) (env : scope_info name_envt) (tyenv : StringSet.t) =
    let add_funbind (env : scope_info name_envt) d =
      match d with
      | DFun (name, args, _, loc) ->
        (name, (loc, Some (List.length args), Some (List.length args))) :: env
    in
    let env = List.fold_left add_funbind env g in
    let errs = List.concat (List.map (fun d -> wf_D d env tyenv) g) in
    errs, env
  in
  match p with
  | Program (decls, body, _) ->
    let initial_env = initial_val_env in
    let initial_env =
      List.fold_left
        (fun env (name, (_, arg_count)) ->
          (name, (dummy_span, Some arg_count, Some arg_count)) :: env)
        initial_fun_env
        initial_env
    in
    let rec find name (decls : 'a decl list) =
      match decls with
      | [] -> None
      | DFun (n, args, _, loc) :: rest when n = name -> Some loc
      | _ :: rest -> find name rest
    in
    let rec dupe_funbinds decls =
      match decls with
      | [] -> []
      | DFun (name, args, _, loc) :: rest ->
        (match find name rest with
        | None -> []
        | Some where -> [ DuplicateFun (name, where, loc) ])
        @ dupe_funbinds rest
    in
    let all_decls = List.flatten decls in
    let initial_tyenv = StringSet.of_list [ "Int"; "Bool" ] in
    let help_G (env, exns) g =
      let g_exns, funbinds = wf_G g env initial_tyenv in
      List.fold_left (fun xs x -> x :: xs) env funbinds, exns @ g_exns
    in
    let env, exns = List.fold_left help_G (initial_env, dupe_funbinds all_decls) decls in
    debug_printf "In wf_P: %s\n" (ExtString.String.join ", " (env_keys env));
    let exns = exns @ wf_E body env in
    (match exns with
    | [] -> Ok p
    | _ -> Error exns)
;;

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;; DESUGARING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

let desugar (p : sourcespan program) : sourcespan program =
  let gensym =
    let next = ref 0 in
    fun name ->
      next := !next + 1;
      sprintf "%s_%d" name !next
  in
  let rec helpP (p : sourcespan program) =
    match p with
    | Program (decls, body, tag) ->
      (* This particular desugaring will convert declgroups into ELetRecs *)
      let merge_sourcespans ((s1, _) : sourcespan) ((_, s2) : sourcespan) : sourcespan =
        s1, s2
      in
      let wrap_G g body =
        match g with
        | [] -> body
        | f :: r ->
          let span =
            List.fold_left merge_sourcespans (get_tag_D f) (List.map get_tag_D r)
          in
          ELetRec (helpG g, body, span)
      in
      Program ([], List.fold_right wrap_G decls (helpE body), tag)
  and helpG g = List.map helpD g
  and helpD d =
    match d with
    | DFun (name, args, body, tag) ->
      let helpArg a =
        match a with
        | BTuple (_, tag) ->
          let name = gensym "argtup" in
          let newbind = BName (name, false, tag) in
          newbind, [ a, EId (name, tag), tag ]
        | _ -> a, []
      in
      let newargs, argbinds = List.split (List.map helpArg args) in
      let newbody = ELet (List.flatten argbinds, body, tag) in
      BName (name, false, tag), ELambda (newargs, helpE newbody, tag), tag
  and helpBE bind =
    let b, e, btag = bind in
    let e = helpE e in
    match b with
    | BTuple (binds, ttag) ->
      (match e with
      | EId _ -> expandTuple binds ttag e
      | _ ->
        let newname = gensym "tup" in
        (BName (newname, false, ttag), e, btag)
        :: expandTuple binds ttag (EId (newname, ttag)))
    | _ -> [ b, e, btag ]
  and expandTuple binds tag source : sourcespan binding list =
    let tupleBind i b =
      match b with
      | BBlank btag -> []
      | BName (_, _, btag) ->
        [ b, EGetItem (source, ENumber (Int64.of_int i, dummy_span), tag), btag ]
      | BTuple (binds, tag) ->
        let newname = gensym "tup" in
        let newexpr = EId (newname, tag) in
        ( BName (newname, false, tag)
        , EGetItem (source, ENumber (Int64.of_int i, dummy_span), tag)
        , tag )
        :: expandTuple binds tag newexpr
    in
    let size_check =
      EPrim2
        ( CheckSize
        , source
        , ENumber (Int64.of_int (List.length binds), dummy_span)
        , dummy_span )
    in
    let size_check_bind = BBlank dummy_span, size_check, dummy_span in
    size_check_bind :: List.flatten (List.mapi tupleBind binds)
  and helpE e =
    match e with
    | ESeq (e1, e2, tag) -> ELet ([ BBlank tag, helpE e1, tag ], helpE e2, tag)
    | ETuple (exprs, tag) -> ETuple (List.map helpE exprs, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE e, helpE idx, tag)
    | ESetItem (e, idx, newval, tag) -> ESetItem (helpE e, helpE idx, helpE newval, tag)
    | EId (x, tag) -> EId (x, tag)
    | ENumber (n, tag) -> ENumber (n, tag)
    | EBool (b, tag) -> EBool (b, tag)
    | ENil (t, tag) -> ENil (t, tag)
    | EPrim1 (op, e, tag) -> EPrim1 (op, helpE e, tag)
    | EPrim2 (op, e1, e2, tag) -> EPrim2 (op, helpE e1, helpE e2, tag)
    | ELet (binds, body, tag) ->
      let newbinds = List.map helpBE binds in
      List.fold_right (fun binds body -> ELet (binds, body, tag)) newbinds (helpE body)
    | ELetRec (bindexps, body, tag) ->
      (* ASSUMES well-formed letrec, so only BName bindings *)
      let newbinds = List.map (fun (bind, e, tag) -> bind, helpE e, tag) bindexps in
      ELetRec (newbinds, helpE body, tag)
    | EIf (cond, thn, els, tag) -> EIf (helpE cond, helpE thn, helpE els, tag)
    | EApp (name, args, native, tag) -> EApp (helpE name, List.map helpE args, native, tag)
    | ELambda (binds, body, tag) ->
      let expandBind bind =
        match bind with
        | BTuple (_, btag) ->
          let newparam = gensym "tuparg" in
          BName (newparam, false, btag), helpBE (bind, EId (newparam, btag), btag)
        | _ -> bind, []
      in
      let params, newbinds = List.split (List.map expandBind binds) in
      let newbody =
        List.fold_right (fun binds body -> ELet (binds, body, tag)) newbinds (helpE body)
      in
      ELambda (params, newbody, tag)
  in
  helpP p
;;

(* ASSUMES desugaring is complete *)
let rename_and_tag (p : tag program) : tag program =
  let rec rename env p =
    match p with
    | Program (decls, body, tag) ->
      Program
        (List.map (fun group -> List.map (helpD env) group) decls, helpE env body, tag)
  and helpD env decl =
    match decl with
    | DFun (name, args, body, tag) ->
      let newArgs, env' = helpBS env args in
      DFun (name, newArgs, helpE env' body, tag)
  and helpB env b =
    match b with
    | BBlank tag -> b, env
    | BName (name, allow_shadow, tag) ->
      let name' = sprintf "%s_%d" name tag in
      BName (name', allow_shadow, tag), (name, name') :: env
    | BTuple (binds, tag) ->
      let binds', env' = helpBS env binds in
      BTuple (binds', tag), env'
  and helpBS env (bs : tag bind list) =
    match bs with
    | [] -> [], env
    | b :: bs ->
      let b', env' = helpB env b in
      let bs', env'' = helpBS env' bs in
      b' :: bs', env''
  and helpBG env (bindings : tag binding list) =
    match bindings with
    | [] -> [], env
    | (b, e, a) :: bindings ->
      let b', env' = helpB env b in
      let e' = helpE env e in
      let bindings', env'' = helpBG env' bindings in
      (b', e', a) :: bindings', env''
  and helpE env e =
    match e with
    | ESeq (e1, e2, tag) -> ESeq (helpE env e1, helpE env e2, tag)
    | ETuple (es, tag) -> ETuple (List.map (helpE env) es, tag)
    | EGetItem (e, idx, tag) -> EGetItem (helpE env e, helpE env idx, tag)
    | ESetItem (e, idx, newval, tag) ->
      ESetItem (helpE env e, helpE env idx, helpE env newval, tag)
    | EPrim1 (op, arg, tag) -> EPrim1 (op, helpE env arg, tag)
    | EPrim2 (op, left, right, tag) -> EPrim2 (op, helpE env left, helpE env right, tag)
    | EIf (c, t, f, tag) -> EIf (helpE env c, helpE env t, helpE env f, tag)
    | ENumber _ -> e
    | EBool _ -> e
    | ENil _ -> e
    | EId (name, tag) ->
      (try EId (find env name, tag) with
      | InternalCompilerError _ -> e)
    | EApp (func, args, native, tag) ->
      let func = helpE env func in
      let call_type =
        (* TODO: If you want, try to determine whether func is a known function name, and if so,
            whether it's a Snake function or a Native function *)
        Snake
      in
      EApp (func, List.map (helpE env) args, call_type, tag)
    | ELet (binds, body, tag) ->
      let binds', env' = helpBG env binds in
      let body' = helpE env' body in
      ELet (binds', body', tag)
    | ELetRec (bindings, body, tag) ->
      let revbinds, env =
        List.fold_left
          (fun (revbinds, env) (b, e, t) ->
            let b, env = helpB env b in
            (b, e, t) :: revbinds, env)
          ([], env)
          bindings
      in
      let bindings' =
        List.fold_left
          (fun bindings (b, e, tag) -> (b, helpE env e, tag) :: bindings)
          []
          revbinds
      in
      let body' = helpE env body in
      ELetRec (bindings', body', tag)
    | ELambda (binds, body, tag) ->
      let binds', env' = helpBS env binds in
      let body' = helpE env' body in
      ELambda (binds', body', tag)
  in
  rename [] p
;;

(* ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;; ANFING ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;; *)

type 'a anf_bind =
  | BSeq of 'a cexpr
  | BLet of string * 'a cexpr
  | BLetRec of (string * 'a cexpr) list

let anf (p : tag program) : unit aprogram =
  let rec helpP (p : tag program) : unit aprogram =
    match p with
    | Program ([], body, _) -> AProgram (helpA body, ())
    | Program _ -> raise (InternalCompilerError "decls should have been desugared away")
  and helpC (e : tag expr) : unit cexpr * unit anf_bind list =
    match e with
    | EPrim1 (op, arg, _) ->
      let arg_imm, arg_setup = helpI arg in
      CPrim1 (op, arg_imm, ()), arg_setup
    | EPrim2 (op, left, right, _) ->
      let left_imm, left_setup = helpI left in
      let right_imm, right_setup = helpI right in
      CPrim2 (op, left_imm, right_imm, ()), left_setup @ right_setup
    | EIf (cond, _then, _else, _) ->
      let cond_imm, cond_setup = helpI cond in
      CIf (cond_imm, helpA _then, helpA _else, ()), cond_setup
    | ELet ([], body, _) -> helpC body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
      let exp_ans, exp_setup = helpC exp in
      let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
      body_ans, exp_setup @ [ BSeq exp_ans ] @ body_setup
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
      let exp_ans, exp_setup = helpC exp in
      let body_ans, body_setup = helpC (ELet (rest, body, pos)) in
      body_ans, exp_setup @ [ BLet (bind, exp_ans) ] @ body_setup
    | ELetRec (binds, body, _) ->
      let processBind (bind, rhs, _) =
        match bind with
        | BName (name, _, _) -> name, helpC rhs
        | _ ->
          raise
            (InternalCompilerError
               (sprintf
                  "Encountered a non-simple binding in ANFing a let-rec: %s"
                  (string_of_bind bind)))
      in
      let names, new_binds_setup = List.split (List.map processBind binds) in
      let new_binds, new_setup = List.split new_binds_setup in
      let body_ans, body_setup = helpC body in
      body_ans, BLetRec (List.combine names new_binds) :: body_setup
    | ELambda (args, body, _) ->
      let processBind bind =
        match bind with
        | BName (name, _, _) -> name
        | _ ->
          raise
            (InternalCompilerError
               (sprintf
                  "Encountered a non-simple binding in ANFing a lambda: %s"
                  (string_of_bind bind)))
      in
      CLambda (List.map processBind args, helpA body, ()), []
    | ELet ((BTuple (binds, _), exp, _) :: rest, body, pos) ->
      raise (InternalCompilerError "Tuple bindings should have been desugared away")
    | EApp (func, args, native, _) ->
      let func_ans, func_setup = helpI func in
      let new_args, new_setup = List.split (List.map helpI args) in
      CApp (func_ans, new_args, native, ()), func_setup @ List.concat new_setup
    | ESeq (e1, e2, _) ->
      let e1_ans, e1_setup = helpC e1 in
      let e2_ans, e2_setup = helpC e2 in
      e2_ans, e1_setup @ [ BSeq e1_ans ] @ e2_setup
    | ETuple (args, _) ->
      let new_args, new_setup = List.split (List.map helpI args) in
      CTuple (new_args, ()), List.concat new_setup
    | EGetItem (tup, idx, _) ->
      let tup_imm, tup_setup = helpI tup in
      let idx_imm, idx_setup = helpI idx in
      CGetItem (tup_imm, idx_imm, ()), tup_setup @ idx_setup
    | ESetItem (tup, idx, newval, _) ->
      let tup_imm, tup_setup = helpI tup in
      let idx_imm, idx_setup = helpI idx in
      let new_imm, new_setup = helpI newval in
      CSetItem (tup_imm, idx_imm, new_imm, ()), tup_setup @ idx_setup @ new_setup
    | _ ->
      let imm, setup = helpI e in
      CImmExpr imm, setup
  and helpI (e : tag expr) : unit immexpr * unit anf_bind list =
    match e with
    | ENumber (n, _) -> ImmNum (n, ()), []
    | EBool (b, _) -> ImmBool (b, ()), []
    | EId (name, _) -> ImmId (name, ()), []
    | ENil _ -> ImmNil (), []
    | ESeq (e1, e2, _) ->
      let e1_imm, e1_setup = helpI e1 in
      let e2_imm, e2_setup = helpI e2 in
      e2_imm, e1_setup @ e2_setup
    | ETuple (args, tag) ->
      let tmp = sprintf "tup_%d" tag in
      let new_args, new_setup = List.split (List.map helpI args) in
      ImmId (tmp, ()), List.concat new_setup @ [ BLet (tmp, CTuple (new_args, ())) ]
    | EGetItem (tup, idx, tag) ->
      let tmp = sprintf "get_%d" tag in
      let tup_imm, tup_setup = helpI tup in
      let idx_imm, idx_setup = helpI idx in
      ( ImmId (tmp, ())
      , tup_setup @ idx_setup @ [ BLet (tmp, CGetItem (tup_imm, idx_imm, ())) ] )
    | ESetItem (tup, idx, newval, tag) ->
      let tmp = sprintf "set_%d" tag in
      let tup_imm, tup_setup = helpI tup in
      let idx_imm, idx_setup = helpI idx in
      let new_imm, new_setup = helpI newval in
      ( ImmId (tmp, ())
      , tup_setup
        @ idx_setup
        @ new_setup
        @ [ BLet (tmp, CSetItem (tup_imm, idx_imm, new_imm, ())) ] )
    | EPrim1 (op, arg, tag) ->
      let tmp = sprintf "unary_%d" tag in
      let arg_imm, arg_setup = helpI arg in
      ImmId (tmp, ()), arg_setup @ [ BLet (tmp, CPrim1 (op, arg_imm, ())) ]
    | EPrim2 (op, left, right, tag) ->
      let tmp = sprintf "binop_%d" tag in
      let left_imm, left_setup = helpI left in
      let right_imm, right_setup = helpI right in
      ( ImmId (tmp, ())
      , left_setup @ right_setup @ [ BLet (tmp, CPrim2 (op, left_imm, right_imm, ())) ] )
    | EIf (cond, _then, _else, tag) ->
      let tmp = sprintf "if_%d" tag in
      let cond_imm, cond_setup = helpI cond in
      ( ImmId (tmp, ())
      , cond_setup @ [ BLet (tmp, CIf (cond_imm, helpA _then, helpA _else, ())) ] )
    | EApp (func, args, native, tag) ->
      let tmp = sprintf "app_%d" tag in
      let new_func, func_setup = helpI func in
      let new_args, new_setup = List.split (List.map helpI args) in
      ( ImmId (tmp, ())
      , func_setup
        @ List.concat new_setup
        @ [ BLet (tmp, CApp (new_func, new_args, native, ())) ] )
    | ELet ([], body, _) -> helpI body
    | ELet ((BBlank _, exp, _) :: rest, body, pos) ->
      let exp_ans, exp_setup = helpC exp in
      let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
      body_ans, exp_setup @ [ BSeq exp_ans ] @ body_setup
    | ELetRec (binds, body, tag) ->
      let tmp = sprintf "lam_%d" tag in
      let processBind (bind, rhs, _) =
        match bind with
        | BName (name, _, _) -> name, helpC rhs
        | _ ->
          raise
            (InternalCompilerError
               (sprintf
                  "Encountered a non-simple binding in ANFing a let-rec: %s"
                  (string_of_bind bind)))
      in
      let names, new_binds_setup = List.split (List.map processBind binds) in
      let new_binds, new_setup = List.split new_binds_setup in
      let body_ans, body_setup = helpC body in
      ( ImmId (tmp, ())
      , List.concat new_setup
        @ [ BLetRec (List.combine names new_binds) ]
        @ body_setup
        @ [ BLet (tmp, body_ans) ] )
    | ELambda (args, body, tag) ->
      let tmp = sprintf "lam_%d" tag in
      let processBind bind =
        match bind with
        | BName (name, _, _) -> name
        | _ ->
          raise
            (InternalCompilerError
               (sprintf
                  "Encountered a non-simple binding in ANFing a lambda: %s"
                  (string_of_bind bind)))
      in
      ImmId (tmp, ()), [ BLet (tmp, CLambda (List.map processBind args, helpA body, ())) ]
    | ELet ((BName (bind, _, _), exp, _) :: rest, body, pos) ->
      let exp_ans, exp_setup = helpC exp in
      let body_ans, body_setup = helpI (ELet (rest, body, pos)) in
      body_ans, exp_setup @ [ BLet (bind, exp_ans) ] @ body_setup
    | ELet ((BTuple (binds, _), exp, _) :: rest, body, pos) ->
      raise (InternalCompilerError "Tuple bindings should have been desugared away")
  and helpA e : unit aexpr =
    let ans, ans_setup = helpC e in
    List.fold_right
      (fun bind body ->
        match bind with
        | BSeq exp -> ASeq (exp, body, ())
        | BLet (name, exp) -> ALet (name, exp, body, ())
        | BLetRec names -> ALetRec (names, body, ()))
      ans_setup
      (ACExpr ans)
  in
  helpP p
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

let rec replicate x i = if i = 0 then [] else x :: replicate x (i - 1)

and reserve size tag =
  let ok = sprintf "$memcheck_%d" tag in
  [ IInstrComment
      ( IMov (Reg RAX, LabelContents "?HEAP_END")
      , sprintf "Reserving %d words" (size / word_size) )
  ; ISub (Reg RAX, Const (Int64.of_int size))
  ; ICmp (Reg RAX, Reg heap_reg) (* ; IJge (Label ok) *)
  ]
  @ native_call
      (Label "?try_gc")
      [ Sized (QWORD_PTR, Reg heap_reg)
      ; (* alloc_ptr in C *)
        Sized (QWORD_PTR, Const (Int64.of_int size))
      ; (* bytes_needed in C *)
        Sized (QWORD_PTR, Reg RBP)
      ; (* first_frame in C *)
        Sized (QWORD_PTR, Reg RSP) (* stack_top in C *)
      ]
  @ [ IInstrComment
        ( IMov (Reg heap_reg, Reg RAX)
        , "assume gc success if returning here, so RAX holds the new heap_reg value" )
    ; ILabel ok
    ]

(* IMPLEMENT THIS FROM YOUR PREVIOUS ASSIGNMENT *)
(* Additionally, you are provided an initial environment of values that you may want to
   assume should take up the first few stack slots.  See the compiliation of Programs
   below for one way to use this ability... *)

and compile_fun
    (funname : string)
    (args : string list)
    (expr : 'a aexpr)
    (env : naive_stack_env)
    : instruction list * instruction list * instruction list
  =
  let closure = CLambda (args, expr, 0) in
  (* what do we put for the prologe and epiloge??*)
  (* printf "\nOUTER ENV: %s\n" (dump env);
  printf "\INNER ENV: %s\n" (dump inner_env);
  printf "\CURRENT FUNNAME: %s\n" funname; *)
  let prelude = function_prelude (deepest_stack expr env "closure#0") in
  ( prelude
  , compile_cexpr closure funname env (List.length args) "" false
    @ [ ICall (Label "temp_closure_0") ]
  , function_postlude )

and compile_aexpr
    (e : tag aexpr)
    (funname : string)
    (env : naive_stack_env)
    (num_args : int)
    (is_tail : bool)
    : instruction list
  =
  match e with
  | ALet (name, value, body, tag) ->
    compile_cexpr value funname env num_args "" is_tail
    @ [ IMov (lookup funname name env, Reg RAX) ]
    @ compile_aexpr body funname env num_args is_tail
  | ACExpr c -> compile_cexpr c funname env num_args "" is_tail
  | ALetRec (bindings, body, tag) ->
    (List.map
       (fun (name, value) ->
         compile_cexpr value funname env num_args name is_tail
         @ [ IMov (lookup funname name env, Reg RAX) ])
       bindings
    |> List.flatten)
    @ compile_aexpr body funname env num_args is_tail
  | ASeq (first, rest, tag) ->
    compile_cexpr first funname env num_args "" is_tail
    @ compile_aexpr rest funname env num_args is_tail

and lookup (funname : string) (name : string) (env : naive_stack_env) =
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

and compile_native_app
    (fun_id : tag immexpr)
    (funname : string)
    (args : tag immexpr list)
    (env : arg name_envt name_envt)
  =
  match fun_id with
  | ImmId (name, _) ->
    let arg_instrustions =
      List.mapi
        (fun index arg ->
          (* TODO NOT SURE WHAT TO DO HERE*)
          compile_imm arg name env
          @ [ IMov (Reg (List.nth first_six_args_registers index), Reg RAX) ])
        args
      |> List.flatten
    in
    arg_instrustions @ [ ICall (Label name) ]
  | _ -> raise (InternalCompilerError "invalid attempt to compile a native function")

and compile_prim1
    (p1 : prim1)
    (e : tag immexpr)
    (funname : string)
    (env : arg name_envt name_envt)
    (tag : tag)
  =
  match p1 with
  | IsBool -> compile_imm e funname env @ is_bool_instructions tag
  | IsNum ->
    compile_imm e funname env @ [ IShl (Reg RAX, Const 63L); IXor (Reg RAX, const_true) ]
  | Not ->
    compile_imm e funname env
    @ check_is_bool err_LOGIC_NOT_BOOL
    @ [ IMov (Reg RSI, Reg RAX); IMov (Reg RAX, const_true); IXor (Reg RAX, Reg RSI) ]
    @ [ IMov (Reg RSI, Reg RAX); IMov (Reg RAX, const_false); IOr (Reg RAX, Reg RSI) ]
  | Add1 ->
    compile_imm e funname env
    @ check_is_number err_ARITH_NOT_NUM
    @ [ IAdd (Reg RAX, Const 2L) ]
    @ [ IJo (error_code_to_label err_OVERFLOW) ]
  | Sub1 ->
    compile_imm e funname env
    @ check_is_number err_ARITH_NOT_NUM
    @ [ ISub (Reg RAX, Const 2L) ]
    @ [ IJo (error_code_to_label err_OVERFLOW) ]
  | Print -> compile_imm e funname env @ print_instructions
  | IsTuple -> is_tuple_instructions tag
  | PrintStack -> print_stack_instructions

and compile_prim2
    (p2 : prim2)
    (e1 : tag immexpr)
    (e2 : tag immexpr)
    (funname : string)
    (env : arg name_envt name_envt)
    (tag : tag)
  =
  match p2 with
  | CheckSize -> []
  | Plus ->
    compile_imm e1 funname env
    @ check_is_number err_ARITH_NOT_NUM
    @ [ IMov (Reg RDX, Reg RAX) ]
    @ compile_imm e2 funname env
    @ check_is_number err_ARITH_NOT_NUM
    @ [ IAdd (Reg RAX, Reg RDX) ]
    @ [ IJo (error_code_to_label err_OVERFLOW) ]
  | Minus ->
    compile_imm e1 funname env
    @ check_is_number err_ARITH_NOT_NUM
    @ [ IMov (Reg RDX, Reg RAX) ]
    @ compile_imm e2 funname env
    @ check_is_number err_ARITH_NOT_NUM
    @ [ ISub (Reg RDX, Reg RAX) ]
    @ [ IMov (Reg RAX, Reg RDX) ]
    @ [ IJo (error_code_to_label err_OVERFLOW) ]
  | Times ->
    compile_imm e1 funname env
    @ check_is_number err_ARITH_NOT_NUM
    @ [ IMov (Reg RDX, Reg RAX) ]
    @ compile_imm e2 funname env
    @ check_is_number err_ARITH_NOT_NUM
    @ [ ISar (Reg RAX, Const 1L) ]
    @ [ IMul (Reg RAX, Reg RDX) ]
    @ [ IJo (error_code_to_label err_OVERFLOW) ]
  | And ->
    let false_label = sprintf "false#%d" tag in
    let done_label = sprintf "done#%d" tag in
    compile_imm e1 funname env
    @ check_is_bool err_LOGIC_NOT_BOOL
    @ [ ISar (Reg RAX, Const 63L); ITest (Reg RAX, Const 0x1L); IJz (Label false_label) ]
    @ compile_imm e2 funname env
    @ check_is_bool err_LOGIC_NOT_BOOL
    @ [ ISar (Reg RAX, Const 63L)
      ; ITest (Reg RAX, Const 0x1L)
      ; IJz (Label false_label)
      ; IMov (Reg RDX, const_true)
      ; IJmp (Label done_label)
      ; ILabel false_label
      ; IMov (Reg RDX, const_false)
      ; ILabel done_label
      ; IMov (Reg RAX, Reg RDX)
      ]
  | Or ->
    let true_label = sprintf "true#%d" tag in
    let done_label = sprintf "done#%d" tag in
    compile_imm e1 funname env
    @ check_is_bool err_LOGIC_NOT_BOOL
    @ [ ISar (Reg RAX, Const 63L); ITest (Reg RAX, Const 0x1L); IJnz (Label true_label) ]
    @ compile_imm e2 funname env
    @ check_is_bool err_LOGIC_NOT_BOOL
    @ [ ISar (Reg RAX, Const 63L)
      ; ITest (Reg RAX, Const 0x1L)
      ; IJnz (Label true_label)
      ; IMov (Reg RDX, const_false)
      ; IJmp (Label done_label)
      ; ILabel true_label
      ; IMov (Reg RDX, const_true)
      ; ILabel done_label
      ; IMov (Reg RAX, Reg RDX)
      ]
  | Greater ->
    let greater_label = sprintf "greater#%d" tag in
    compile_imm e1 funname env
    @ check_is_number err_COMP_NOT_NUM
    @ [ IMov (Reg RDX, Reg RAX) ]
    @ compile_imm e2 funname env
    @ check_is_number err_COMP_NOT_NUM
    @ [ ICmp (Reg RDX, Reg RAX) ]
    @ [ IMov (Reg RAX, const_true) ]
    @ [ IJg (Label greater_label) ]
    @ [ IMov (Reg RAX, const_false) ]
    @ [ ILabel greater_label ]
  | GreaterEq ->
    let greater_eq_label = sprintf "greater_eq#%d" tag in
    compile_imm e1 funname env
    @ check_is_number err_COMP_NOT_NUM
    @ [ IMov (Reg RDX, Reg RAX) ]
    @ compile_imm e2 funname env
    @ check_is_number err_COMP_NOT_NUM
    @ [ ICmp (Reg RDX, Reg RAX) ]
    @ [ IMov (Reg RAX, const_true) ]
    @ [ IJge (Label greater_eq_label) ]
    @ [ IMov (Reg RAX, const_false) ]
    @ [ ILabel greater_eq_label ]
  | Less ->
    let less_label = sprintf "less#%d" tag in
    compile_imm e1 funname env
    @ check_is_number err_COMP_NOT_NUM
    @ [ IMov (Reg RDX, Reg RAX) ]
    @ compile_imm e2 funname env
    @ check_is_number err_COMP_NOT_NUM
    @ [ ICmp (Reg RDX, Reg RAX) ]
    @ [ IMov (Reg RAX, const_true) ]
    @ [ IJl (Label less_label) ]
    @ [ IMov (Reg RAX, const_false) ]
    @ [ ILabel less_label ]
  | LessEq ->
    let leq_label = sprintf "leq#%d" tag in
    compile_imm e1 funname env
    @ check_is_number err_COMP_NOT_NUM
    @ [ IMov (Reg RDX, Reg RAX) ]
    @ compile_imm e2 funname env
    @ check_is_number err_COMP_NOT_NUM
    @ [ ICmp (Reg RDX, Reg RAX) ]
    @ [ IMov (Reg RAX, const_true) ]
    @ [ IJle (Label leq_label) ]
    @ [ IMov (Reg RAX, const_false) ]
    @ [ ILabel leq_label ]
  | Eq ->
    compile_imm e1 funname env
    @ [ IMov (Reg RDI, Reg RAX) ]
    @ compile_imm e2 funname env
    @ [ IMov (Reg RSI, Reg RAX) ]
    @ [ ICall (Label "?equal") ]

and compile_cexpr
    (e : tag cexpr)
    (funname : string)
    (env : naive_stack_env)
    (num_args : int)
    (recname : string)
    (is_tail : bool)
    : instruction list
  =
  match e with
  | CIf (cond, _then, _else, tag) ->
    let else_label = sprintf "else#%d" tag in
    let done_label = sprintf "done#%d" tag in
    let c_then = compile_aexpr _then funname env num_args is_tail in
    let c_else = compile_aexpr _else funname env num_args is_tail in
    let c_cond = compile_imm cond funname env in
    c_cond
    @ check_is_bool err_IF_NOT_BOOL
    @ [ IShr (Reg RAX, Const 63L) ]
    @ [ ITest (Reg RAX, Const 0x1L) ]
    @ [ IJz (Label else_label) ]
    @ c_then
    @ [ IJmp (Label done_label) ]
    @ [ ILabel else_label ]
    @ c_else
    @ [ ILabel done_label ]
  | CPrim1 (op, e, tag) -> compile_prim1 op e funname env tag
  | CPrim2 (op, e1, e2, tag) -> compile_prim2 op e1 e2 funname env tag
  | CImmExpr immexpr -> compile_imm immexpr funname env
  | CTuple (values, tag) ->
    let len = List.length values in
    [ ILineComment "begin reserving tuple" ]
    @ reserve (8 * (len + 1)) tag
    @ [ IMov (Reg RDI, Reg R15) ]
    (* print_stack_instructions *)
    @ [ IMov (Reg RAX, Sized (QWORD_PTR, Const (Int64.of_int (2 * len))))
        (* [ IMov (Reg RAX, Sized (QWORD_PTR, Const 4L)) *)
      ; IMov (RegOffset (0, R15), Reg RAX)
      ; IAdd (Reg R15, Const 8L)
      ]
    @ (List.map
         (fun value ->
           compile_imm value funname env
           @ [ IMov (RegOffset (0, R15), Reg RAX); IAdd (Reg R15, Const 8L) ])
         values
      |> List.flatten)
    @ (if len mod 2 == 0
      then [ (* IMov (Reg R15, const_nil);  *) IAdd (Reg R15, Const 8L) ]
      else [])
    (* let r15_offset = 1 + len + if len mod 2 == 0 then 1 else 0 in *)
    @ [ IAdd (Reg RDI, Sized (QWORD_PTR, Const 1L)) ]
    @ [ IMov (Reg RAX, Reg RDI) ]
    (* [ IAdd (Reg RDI, Sized (QWORD_PTR, Const 7L)) ] @ [ IMov (Reg RAX, Reg RDI) ] *)
    (* [ IMov (Reg RAX, RegOffset (~-r15_offset * 8, R15)) ] *)
  | CSetItem (tup_expr, num_expr, value_expr, _) ->
    let tup = compile_imm tup_expr funname env in
    let num = compile_imm num_expr funname env in
    let value = compile_imm value_expr funname env in
    [ ILineComment "Compile index" ]
    @ num
    @ [ ISar (Reg RAX, Const 1L) ]
    (* @ check_is_number err_COMP_NOT_NUM *)
    (* bounds check *)
    @ [ IMov (Reg R11, Reg RAX) ]
    @ [ ILineComment "Compile Tuple" ]
    @ tup
    (*check is tuple*)
    @ [ ISub (Reg RAX, Sized (QWORD_PTR, Const 1L)) ]
    @ [ IMov (Reg RDI, Reg RAX) ]
    @ [ ILineComment "Compile value" ]
    @ value
    @ [ ILineComment "set the item" ]
    @ [ IMov (RegOffsetReg (RDI, R11, 8, 8), Reg RAX) ]
  | CGetItem (tup_expr, num_expr, tag) ->
    let high_label = sprintf "out_of_bounds_high#%d" tag in
    let low_label = sprintf "out_of_bounds_low#%d" tag in
    let test_low_label = sprintf "test_low_label#%d" tag in
    let test_high_label = sprintf "test_high_label#%d" tag in
    let nil_label = sprintf "nil_label#%d" tag in
    let done_label = sprintf "done#%d" tag in
    let tup = compile_imm tup_expr funname env in
    let num = compile_imm num_expr funname env in
    num
    @ [ ISar (Reg RAX, Const 1L) ]
    (* @ check_is_number err_COMP_NOT_NUM *)
    (* check bounds *)
    @ [ IMov (Reg R11, Reg RAX) ]
    @ tup
    @ [ IMov (Reg RDX, Const 1L) ]
    @ [ ICmp (Reg RAX, Reg RDX) ]
    @ [ IJe (Label nil_label) ]
    @ [ IJmp (Label test_high_label) ]
    @ [ ILabel nil_label ]
    @ [ IMov (Reg RSI, Reg RAX) ]
    @ [ IMov (Reg RDI, Const err_NIL_DEREF) ]
    @ [ ICall (Label "?error") ]
    @ [ ILabel test_high_label ]
    @ [ ISub (Reg RAX, Sized (QWORD_PTR, Const 1L)) ]
    @ [ ICmp (Reg R11, RegOffset (0, RAX))
      ; IJge (Label high_label)
      ; IJmp (Label test_low_label)
      ; ILabel high_label
      ; IMov (Reg RSI, RegOffset (0, RAX))
      ; IMov (Reg RDI, Const err_GET_HIGH_INDEX)
      ; ICall (Label "?error")
      ; ILabel test_low_label
      ; IMov (Reg RDX, Const 0L)
      ; ICmp (Reg R11, Reg RDX)
      ; IJl (Label low_label)
      ; IJmp (Label done_label)
      ; ILabel low_label
      ; IMov (Reg RSI, RegOffset (0, RAX))
      ; IMov (Reg RDI, Const err_GET_LOW_INDEX)
      ; ICall (Label "?error")
      ; ILabel done_label
      ]
    @ (* check is tuple *)
    [ IMov (Reg RAX, RegOffsetReg (RAX, R11, 8, 8)) ]
  | CLambda (binds, body, tag) ->
    let name = sprintf "temp_closure_%d" tag in
    let after = sprintf "after_%d" tag in
    let frees = free_vars body (binds @ [ recname ]) in
    let num_frees = List.length frees in
    let num_bindings = deepest_stack body env (sprintf "closure#%d" tag) in
    let heap_offset = 24 + (num_frees * 8) + if num_frees mod 2 = 0 then 8 else 0 in
    (* let env = allocate_cexpr e 1 in *)
    reserve (8 * (3 + num_frees)) tag
    @ [ IMov (Reg RDX, Reg R15) ]
    @ [ ILineComment (dump env) ]
    @ [ IJmp (Label after) ]
    @ [ ILabel name ]
    (* body preamble *)
    @ [ IPush (Reg RBP) ]
    @ [ IMov (Reg RBP, Reg RSP) ]
    (* allocate space for free vars *)
    @ [ ISub (Reg RSP, Const (Int64.of_int ((8 * num_bindings) + (8 * num_frees)))) ]
    (* move self arg into R11 *)
    @ [ IMov (Reg R11, RegOffset (16, RBP)) ]
    (* untag the self argument *)
    @ [ ISub (Reg R11, Const 5L) ]
    (* adding vars from heap into closure *)
    @ [ ILineComment "get closed over variables from the heap" ]
    @ [ ILineComment (sprintf "free variables: %s" (dump frees)) ]
    @ (List.mapi
         (fun index _ ->
           [ IMov (Reg RAX, RegOffset ((index * 8) + 24, R11)) ]
           @ [ IMov (RegOffset (~-8 * (index + 1), RBP), Reg RAX) ]
           (* [IMov (Reg RAX, RegOffset(24, R11))]
          IPush (Sized (QWORD_PTR, RegOffset ((index * 8) + 24, R11)))) *))
         frees
      |> List.flatten)
    (* / body preamble *)
    (* body *)
    @ [ ILineComment "body start" ]
    @ [ ILineComment (sprintf "env : %s" (dump env)) ]
    @ compile_aexpr body (sprintf "closure#%d" tag) env num_args is_tail
    @ [ ILineComment "body end" ]
    (* / body *)
    (* body postamble *)
    @ [ IMov (Reg RSP, Reg RBP) ]
    @ [ IPop (Reg RBP) ]
    @ [ IRet ]
    (* body postamble *)
    @ [ ILabel after ]
    (* move arity into first position *)
    @ [ IMov (Reg RDI, Const (Int64.of_int (List.length binds))) ]
    @ [ IShl (Reg RDI, Const 2L) ]
    @ [ IMov (RegOffset (0, R15), Reg RDI) ]
    (* move code_ptr into second pos*)
    @ [ IMov (Reg RDI, Label name) ]
    @ [ IMov (RegOffset (8, R15), Reg RDI) ]
    (* move num frees into third pos *)
    @ [ IMov (Reg RDI, Const (Int64.of_int (num_frees * 2))) ]
    @ [ IMov (RegOffset (16, R15), Reg RDI) ]
    (* move frees into spots 4-n *)
    @ [ ILineComment "move the closed over values onto heap offsets" ]
    @ (List.mapi
         (fun index name ->
           [ IMov (Reg RDI, lookup funname name env) ]
           @ [ IMov (RegOffset ((index * 8) + 24, R15), Reg RDI) ])
         frees
      |> List.flatten)
    (* put closure into RAX *)
    @ [ IMov (Reg RAX, Reg RDX) ]
    (* tag closure *)
    @ [ IAdd (Reg RAX, Const 5L) ]
    (* offset R15 *)
    @ [ IAdd (Reg R15, Const (Int64.of_int heap_offset)) ]
  | CApp (funv, args, call_type, tag) ->
    (match call_type with
    | Prim -> compile_prim1 (funv_to_op funv) (List.first args) funname env tag
    | Native -> compile_native_app funv funname args env
    | _ ->
      let is_fun = sprintf "is_fun#%d" tag in
      let eq_arity = sprintf "eq_arity#%d" tag in
      [ ILineComment "get function" ]
      @ compile_imm funv funname env
      (* check is fun & arity *)
      @ [ ILineComment "check fun" ]
      @ [ IMov (Reg RDX, Reg RAX) ]
      @ [ IMov (Reg RDI, Const bool_tag) ]
      @ [ IAnd (Reg RDX, Reg RDI) ]
      @ [ IMov (Reg RDI, Const 5L) ]
      @ [ ICmp (Reg RDX, Reg RDI) ]
      @ [ IJe (Label is_fun) ]
      @ [ IMov (Reg RSI, Reg RAX) ]
      @ [ IMov (Reg RDI, Const err_CALL_NOT_CLOSURE) ]
      @ [ ICall (Label "?error") ]
      @ [ ILabel is_fun ]
      @ [ ILineComment "check arity" ]
      @ [ IMov (Reg RSI, Const (Int64.of_int (List.length args))) ]
      @ [ IShl (Reg RSI, Const 2L) ]
      @ [ IMov (Reg RDX, RegOffset (~-5, RAX)) ]
      @ [ ICmp (Reg RSI, Reg RDX) ]
      @ [ IJe (Label eq_arity) ]
      @ [ IMov (Reg RDI, Const err_CALL_ARITY_ERR) ]
      @ [ ICall (Label "?error") ]
      (* push arguments onto stack *)
      @ [ ILabel eq_arity ]
      @ [ ILineComment "push args onto stack" ]
      @ (List.rev args
        |> List.map (fun arg -> compile_imm arg funname env @ [ IPush (Reg RAX) ])
        |> List.flatten)
      @ compile_imm funv funname env
      @ [ ILineComment "push RAX onto stack" ]
      @ [ IPush (Reg RAX) ]
      (* @ [ IAdd (Reg RAX, Const 3L) ] *)
      @ [ ILineComment "call function" ]
      @ [ ICall (RegOffset (3, RAX)) ]
      @ [ IAdd (Reg RSP, Const (Int64.of_int ((List.length args + 1) * 8))) ])

and compile_imm (e : tag immexpr) (funname : string) (env : naive_stack_env)
    : instruction list
  =
  match e with
  | ImmNum (n, _) -> [ IMov (Reg RAX, Const (Int64.shift_left n 1)) ]
  | ImmBool (true, _) -> [ IMov (Reg RAX, const_true) ]
  | ImmBool (false, _) -> [ IMov (Reg RAX, const_false) ]
  | ImmId (x, _) -> [ IMov (Reg RAX, lookup funname x env) ]
  | ImmNil _ -> [ IMov (Reg RAX, const_nil) ]

and args_help args regs =
  match args, regs with
  | arg :: args, reg :: regs ->
    IMov (Sized (QWORD_PTR, Reg reg), arg) :: args_help args regs
  | args, [] -> List.rev_map (fun arg -> IPush arg) args
  | [], _ -> []

and native_call label args =
  (* We know that on entry to every function, RSP is 16-byte aligned.
     We know that every frame is a multiple of 16 bytes.
     The call instruction pushes one return pointer onto the stack.
     The first thing we do is push RBP onto the stack
     So, we add 8 bytes of padding IFF the number of spilled args is *ODD*.
  *)
  let num_stack_args = max (List.length args - 6) 0 in
  let padding_needed = num_stack_args mod 2 <> 0 in
  let setup =
    (if padding_needed
    then
      [ IInstrComment (IPush (Sized (QWORD_PTR, Const 0L)), "Padding to 16-byte alignment")
      ]
    else [])
    @ args_help args first_six_args_registers
  in
  let teardown =
    (if num_stack_args = 0
    then []
    else
      [ IInstrComment
          ( IAdd (Reg RSP, Const (Int64.of_int (word_size * num_stack_args)))
          , sprintf "Popping %d arguments" num_stack_args )
      ])
    @
    if padding_needed
    then
      [ IInstrComment
          (IAdd (Reg RSP, Const (Int64.of_int word_size)), "Unpadding one word")
      ]
    else []
  in
  setup @ [ ICall label ] @ teardown

(* UPDATE THIS TO HANDLE FIRST-CLASS FUNCTIONS AS NEEDED -- THIS CODE WILL NOT WORK AS WRITTEN *)
and call (closure : arg) args =
  let setup =
    List.rev_map
      (fun arg ->
        match arg with
        | Sized _ -> IPush arg
        | _ -> IPush (Sized (DWORD_PTR, arg)))
      args
  in
  let teardown =
    let len = List.length args in
    if len = 0
    then []
    else
      [ IInstrComment
          ( IAdd (Reg RSP, Const (Int64.of_int (word_size * len)))
          , sprintf "Popping %d arguments" len )
      ]
  in
  setup @ [ ICall closure ] @ teardown
;;

(* This function can be used to take the native functions and produce DFuns whose bodies
   simply contain an EApp (with a Native call_type) to that native function.  Then,
   your existing compilation can turn these DFuns into ELambdas, which can then be called
   as in the rest of Fer-De-Lance, but the Native EApps will do the work of actually
   native_calling the runtime-provided functions. *)
let add_native_lambdas (p : sourcespan program) =
  let wrap_native name arity =
    let argnames = List.init arity (fun i -> sprintf "%s_arg_%d" name i) in
    [ DFun
        ( name
        , List.map (fun name -> BName (name, false, dummy_span)) argnames
        , EApp
            ( EId (name, dummy_span)
            , List.map (fun name -> EId (name, dummy_span)) argnames
            , Native
            , dummy_span )
        , dummy_span )
    ]
  in
  match p with
  | Program (declss, body, tag) ->
    Program
      ( List.fold_left
          (fun declss (name, (_, arity)) -> wrap_native name arity :: declss)
          declss
          native_fun_bindings
      , body
      , tag )
;;

let compile_prog (anfed, (env : arg name_envt name_envt)) =
  let prelude =
    "section .text\n\
     extern ?error\n\
     extern ?input\n\
     extern ?print\n\
     extern ?print_stack\n\
     extern ?equal\n\
     extern ?try_gc\n\
     extern ?naive_print_heap\n\
     extern ?HEAP\n\
     extern ?HEAP_END\n\
     extern ?set_stack_bottom\n\
     global ?our_code_starts_here"
  in
  let suffix =
    sprintf
      "\n\
       ?err_comp_not_num:%s\n\
       ?err_arith_not_num:%s\n\
       ?err_logic_not_bool:%s\n\
       ?err_if_not_bool:%s\n\
       ?err_overflow:%s\n\
       ?err_get_not_tuple:%s\n\
       ?err_get_low_index:%s\n\
       ?err_get_high_index:%s\n\
       ?err_nil_deref:%s\n\
       ?err_out_of_memory:%s\n\
       ?err_set_not_tuple:%s\n\
       ?err_set_low_index:%s\n\
       ?err_set_high_index:%s\n\
       ?err_call_not_closure:%s\n\
       ?err_call_arity_err:%s\n"
      (to_asm (native_call (Label "?error") [ Const err_COMP_NOT_NUM; Reg scratch_reg ]))
      (to_asm (native_call (Label "?error") [ Const err_ARITH_NOT_NUM; Reg scratch_reg ]))
      (to_asm
         (native_call (Label "?error") [ Const err_LOGIC_NOT_BOOL; Reg scratch_reg ]))
      (to_asm (native_call (Label "?error") [ Const err_IF_NOT_BOOL; Reg scratch_reg ]))
      (to_asm (native_call (Label "?error") [ Const err_OVERFLOW; Reg RAX ]))
      (to_asm (native_call (Label "?error") [ Const err_GET_NOT_TUPLE; Reg scratch_reg ]))
      (to_asm (native_call (Label "?error") [ Const err_GET_LOW_INDEX; Reg scratch_reg ]))
      (to_asm (native_call (Label "?error") [ Const err_GET_HIGH_INDEX ]))
      (to_asm (native_call (Label "?error") [ Const err_NIL_DEREF; Reg scratch_reg ]))
      (to_asm (native_call (Label "?error") [ Const err_OUT_OF_MEMORY; Reg scratch_reg ]))
      (to_asm (native_call (Label "?error") [ Const err_SET_NOT_TUPLE; Reg scratch_reg ]))
      (to_asm (native_call (Label "?error") [ Const err_SET_LOW_INDEX; Reg scratch_reg ]))
      (to_asm
         (native_call (Label "?error") [ Const err_SET_HIGH_INDEX; Reg scratch_reg ]))
      (to_asm
         (native_call (Label "?error") [ Const err_CALL_NOT_CLOSURE; Reg scratch_reg ]))
      (to_asm
         (native_call (Label "?error") [ Const err_CALL_ARITY_ERR; Reg scratch_reg ]))
  in
  match anfed with
  | AProgram (body, _) ->
    (* $heap and $size are mock parameter names, just so that compile_fun knows our_code_starts_here takes in 2 parameters *)
    let prologue, comp_main, epilogue =
      compile_fun "closure#0" [ "$heap"; "$size" ] body env
    in
    let heap_start =
      [ ILineComment "heap start"
      ; IInstrComment
          ( IMov
              (Sized (QWORD_PTR, Reg heap_reg), Reg (List.nth first_six_args_registers 0))
          , "Load heap_reg with our argument, the heap pointer" )
      ; IInstrComment
          ( IAdd (Sized (QWORD_PTR, Reg heap_reg), Const 15L)
          , "Align it to the nearest multiple of 16" )
      ; IMov (Reg scratch_reg, HexConst 0xFFFFFFFFFFFFFFF0L)
      ; IInstrComment
          ( IAnd (Sized (QWORD_PTR, Reg heap_reg), Reg scratch_reg)
          , "by adding no more than 15 to it" )
      ]
    in
    let set_stack_bottom =
      [ ILabel "?our_code_starts_here"; IMov (Reg R12, Reg RDI) ]
      @ native_call (Label "?set_stack_bottom") [ Reg RBP ]
      @ [ IMov (Reg RDI, Reg R12) ]
    in
    let main =
      prologue @ heap_start @ comp_main @ epilogue @ [ ICall (Label "temp_closure_0") ]
    in
    sprintf "%s%s%s%s\n" prelude (to_asm set_stack_bottom) (to_asm main) suffix
;;

let run_if should_run f = if should_run then f else no_op_phase

let compile_to_string ?(no_builtins = false) (prog : sourcespan program pipeline)
    : string pipeline
  =
  let init_prog =
    if no_builtins then prog else prog |> add_phase wrapped_natives wrap_natives
  in
  init_prog
  |> add_err_phase well_formed is_well_formed
  |> run_if (not no_builtins) (add_phase add_natives add_native_lambdas)
  |> add_phase desugared desugar
  |> add_phase tagged tag
  |> add_phase renamed rename_and_tag
  |> add_phase anfed (fun p -> atag (anf p))
  |> add_phase locate_bindings naive_stack_allocation
  |> add_phase result compile_prog
;;
