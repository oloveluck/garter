open Exprs
module Lsp_types = Linol_lsp.Types

type entry_kind = Var | Fun | Param | PatternBind

type entry = {
  name : string;
  kind : entry_kind;
  def_span : sourcespan;
  mutable use_spans : sourcespan list;
}

type index = {
  entries : entry list ref;
}

let create () : index = { entries = ref [] }

let add_entry (idx : index) (e : entry) =
  idx.entries := e :: !(idx.entries)

let find_entry_by_name (idx : index) (name : string) : entry option =
  (* Return most recently added entry with this name (innermost scope) *)
  List.find_opt (fun e -> e.name = name) !(idx.entries)

let add_use (idx : index) (name : string) (span : sourcespan) =
  match find_entry_by_name idx name with
  | Some entry -> entry.use_spans <- span :: entry.use_spans
  | None -> ()

(* Walk a bind, adding entries for bound names *)
let rec walk_bind (idx : index) (kind : entry_kind) (b : sourcespan bind) =
  match b with
  | BBlank _ -> ()
  | BName (name, _, tag) ->
    add_entry idx { name; kind; def_span = tag; use_spans = [] }
  | BTuple (binds, _) ->
    List.iter (walk_bind idx kind) binds

(* Walk a pattern, adding entries for pattern-bound variables *)
let rec walk_pattern (idx : index) (pat : sourcespan pattern) =
  match pat with
  | PWild _ | PNum _ | PBool _ | PString _ | PNil _ -> ()
  | PVar (name, tag) ->
    add_entry idx { name; kind = PatternBind; def_span = tag; use_spans = [] }
  | PTuple (pats, _) ->
    List.iter (walk_pattern idx) pats

(* Walk an expression, recording definitions and uses *)
let rec walk_expr (idx : index) (e : sourcespan expr) =
  match e with
  | EId (name, span) ->
    add_use idx name span
  | ENumber _ | EBool _ | EString _ | ENil _ -> ()
  | ESeq (e1, e2, _) ->
    walk_expr idx e1;
    walk_expr idx e2
  | ETuple (exprs, _) ->
    List.iter (walk_expr idx) exprs
  | EGetItem (tup, idxe, _) ->
    walk_expr idx tup;
    walk_expr idx idxe
  | ESetItem (tup, idxe, newval, _) ->
    walk_expr idx tup;
    walk_expr idx idxe;
    walk_expr idx newval
  | EPrim1 (_, arg, _) ->
    walk_expr idx arg
  | EPrim2 (_, e1, e2, _) ->
    walk_expr idx e1;
    walk_expr idx e2
  | EIf (cond, thn, els, _) ->
    walk_expr idx cond;
    walk_expr idx thn;
    walk_expr idx els
  | EApp (func, args, _, _) ->
    walk_expr idx func;
    List.iter (walk_expr idx) args
  | ELet (bindings, body, _) ->
    List.iter (fun (bind, rhs, _) ->
      walk_expr idx rhs;
      walk_bind idx Var bind
    ) bindings;
    walk_expr idx body
  | ELetRec (bindings, body, _) ->
    (* Add all bindings first (mutual recursion) *)
    List.iter (fun (bind, _, _) -> walk_bind idx Var bind) bindings;
    List.iter (fun (_, rhs, _) -> walk_expr idx rhs) bindings;
    walk_expr idx body
  | ELambda (binds, body, _) ->
    List.iter (walk_bind idx Param) binds;
    walk_expr idx body
  | EMatch (scrutinee, cases, _) ->
    walk_expr idx scrutinee;
    List.iter (fun (pat, body) ->
      walk_pattern idx pat;
      walk_expr idx body
    ) cases

let walk_decl (idx : index) (d : sourcespan decl) =
  let (DFun (name, args, body, span)) = d in
  add_entry idx { name; kind = Fun; def_span = span; use_spans = [] };
  List.iter (walk_bind idx Param) args;
  walk_expr idx body

let build_index (prog : sourcespan program) : index =
  let idx = create () in
  let (Program (decl_groups, body, _)) = prog in
  List.iter (fun group -> List.iter (walk_decl idx) group) decl_groups;
  walk_expr idx body;
  idx

(* Find the entry whose def_span or use_spans contain the given position *)
let find_at_position (idx : index) (pos : Lsp_types.Position.t) : entry option =
  let check_span span = Span_utils.position_in_span pos span in
  List.find_opt
    (fun entry ->
       check_span entry.def_span
       || List.exists check_span entry.use_spans)
    !(idx.entries)
