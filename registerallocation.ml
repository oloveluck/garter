open Errors
open Exprs
open Assembly
open Freevars
open Printf
open ExtLib
open Graph
open Compilehelpers

(* Re-export the type from compilehelpers for backward compatibility *)
type nonrec naive_stack_env = naive_stack_env

let rec cached_fvs_A (e : (tag * StringSet.t) aexpr) : StringSet.t =
  match e with
  | ALet (_, _, _, (_, f)) -> f
  | ALetRec (_, _, (_, f)) -> f
  | ASeq (_, _, (_, f)) ->
    debug_printf "fvs from seq: %s" (dump f);
    f
  | ACExpr c -> cached_fvs_C c

and cached_fvs_C (e : (tag * StringSet.t) cexpr) : StringSet.t =
  match e with
  | CLambda (_, _, (_, fvs)) -> fvs
  | CImmExpr i -> cached_fvs_I i
  | CApp (_, _, _, (_, f)) -> f
  | CGetItem (_, _, (_, f)) -> f
  | CSetItem (_, _, _, (_, f)) -> f
  | CTuple (_, (_, f)) -> f
  | CIf (_, _, _, (_, f)) ->
    debug_printf "free vars in if: %s" (dump f);
    f
  | CPrim1 (_, _, (_, f)) -> f
  | CPrim2 (_, _, _, (_, f)) -> f

and cached_fvs_I (i : (tag * StringSet.t) immexpr) : StringSet.t =
  match i with
  | ImmBool (_, (_, f)) -> f
  | ImmNum (_, (_, f)) -> f
  | ImmId (_, (_, f)) -> f
  | ImmNil _ -> StringSet.empty
  | ImmString _ -> StringSet.empty
;;

let add_fvs_edge (fvs : StringSet.t) : grapht =
  List.fold_right
    (fun fv1 graph ->
      List.fold_right (fun fv2 g -> add_edge g fv1 fv2) (StringSet.elements fvs) graph)
    (StringSet.elements fvs)
    Graph.empty
;;

let interfere (e : (tag * StringSet.t) aexpr) (live : StringSet.t) : grapht =
  let rec helpA (e : (tag * StringSet.t) aexpr) (live : StringSet.t) : grapht =
    match e with
    | ALet (name, value, body, (_, _fvs)) ->
      (* Get live variables in the body - these are what interfere with 'name' *)
      (* We need the body's free vars PLUS incoming live vars *)
      let body_live = StringSet.union live (cached_fvs_A body) in
      eprintf "ALet %s: body_live = {%s}\n" name (String.concat ", " (StringSet.elements body_live));
      (* name interferes with everything live in the body *)
      let value_graph = helpC value body_live in
      let body_graph = helpA body body_live in
      let fvs_edges =
        List.fold_right
          (fun fv graph -> add_edge graph fv name)
          (StringSet.elements body_live)
          body_graph
      in
      (* Also need to add name as a node even if it has no edges *)
      let fvs_edges_with_name = add_node fvs_edges name in
      let final_graph = graph_merge value_graph fvs_edges_with_name in
      eprintf "ALet %s final graph: %s\n" name (string_of_graph final_graph);
      final_graph
    | ALetRec (bindings, body, (_, _)) ->
      let binding_names = List.map (fun (n, _) -> n) bindings in
      eprintf "ALetRec bindings: %s\n" (String.concat ", " binding_names);
      let lambda_fvs =
        List.fold_right
          (fun set sets -> StringSet.union set sets)
          (List.map
             (fun (recname, lam) -> StringSet.remove recname (cached_fvs_C lam))
             bindings)
          StringSet.empty
      in
      let xs_to_frees =
        List.fold_right (* add edges from x# to lambda frees*)
          (fun x graph ->
            List.fold_right
              (fun fv graph -> add_edge graph x fv)
              (StringSet.elements lambda_fvs)
              graph)
          binding_names
          Graph.empty
      in
      let xs_to_xs =
        (* add edges between x#s*)
        List.fold_right
          (fun x1 graph ->
            List.fold_right (fun xn graph -> add_edge graph x1 xn) binding_names graph)
          binding_names
          xs_to_frees
      in
      eprintf "ALetRec graph (xs_to_xs): %s\n" (string_of_graph xs_to_xs);
      graph_merge (helpA body live) xs_to_xs
    | ACExpr c -> helpC c live
    | ASeq (c, a, _) ->
      graph_merge (helpC c (StringSet.union live (cached_fvs_A a))) (helpA a live)
  and helpC (e : (tag * StringSet.t) cexpr) (live : StringSet.t) : grapht =
    match e with
    | CLambda (_, _, (_, fvs)) ->
      let body_free_edges =
        List.fold_right
          (fun from graph ->
            StringSet.fold (fun _to graph -> add_edge graph _to from) fvs graph)
          (StringSet.elements fvs)
          Graph.empty
      in
      body_free_edges
    | CIf (_, lhs, rhs, _) ->
      let interfere_L = helpA lhs live in
      let interfere_R = helpA rhs live in
      graph_merge interfere_L interfere_R
    | _ -> Graph.empty
  in
  helpA e live
;;

module StringMap = Map.Make (String)

type color_mapping = int StringMap.t

let our_regs = [ Reg R10; Reg R12; Reg R13; Reg R14; Reg RBX ]

let color_graph (g : grapht) : arg name_envt =
  let rec smallest_deg_node (g : grapht) : (string * neighborst) * grapht =
    let smallest_elt_name, smallest_elt_value =
      Graph.fold
        (fun node_name node_neighbors (el_name, el_set) ->
          if NeighborSet.cardinal node_neighbors < NeighborSet.cardinal el_set
          then node_name, node_neighbors
          else el_name, el_set)
        g
        (Graph.choose g)
    in
    (smallest_elt_name, smallest_elt_value), Graph.remove smallest_elt_name g
  and get_worklist (g : grapht) (wl : (string * neighborst) list)
      : (string * neighborst) list
    =
    if Graph.is_empty g
    then wl
    else (
      let smallest_node, new_graph = smallest_deg_node g in
      get_worklist new_graph (smallest_node :: wl))
  and color_help (worklist : (string * neighborst) list) (color_mapping : color_mapping)
      : color_mapping
    =
    match worklist with
    | [] -> color_mapping
    | (node_name, node_neighbors) :: rest ->
      debug_printf
        "\n node neighbors: %s \n"
        (StringSet.fold (fun a b -> sprintf "%s %s" a b) node_neighbors "");
      let min_color = find_min_color node_neighbors color_mapping in
      debug_printf
        "\nmin color: %d for node: %s with neighbors: %s\n"
        min_color
        node_name
        (dump node_neighbors);
      let new_mapping = StringMap.add node_name min_color color_mapping in
      debug_printf "\n%s\n%s\n" (dump color_mapping) (dump new_mapping);
      color_help rest new_mapping
  and smallest_reg_in_range (start : int) (_end : int) (values : int list) =
    if start = _end
    then _end + 1
    else (
      match List.find_opt (fun x -> x = start) values with
      | Some _ -> smallest_reg_in_range (start + 1) _end values
      | None -> start)
  and find_min_color (neighbors : StringSet.t) (color_mapping : color_mapping) : int =
    let colored_neighbors =
      StringMap.filter
        (fun n _ -> StringSet.exists (fun e -> e = n) neighbors)
        color_mapping
    in
    let values = List.map (fun (_, v) -> v) (StringMap.bindings colored_neighbors) in
    if List.length values = 0
    then 0
    else (
      let sorted_values = List.sort ~cmp:Int.compare values in
      debug_printf "sorted values: %s" (dump sorted_values);
      let largest_reg = List.last sorted_values in
      smallest_reg_in_range 0 largest_reg sorted_values)
  and num_to_arg (num : int) : arg =
    let reg_length = List.length our_regs in
    if num < reg_length
    then List.nth our_regs num
    else RegOffset (~-((num - reg_length + 1) * 8), RBP)
  and color_map_to_env (color_map : color_mapping) : arg name_envt =
    let args_map = StringMap.map (fun color -> num_to_arg color) color_map in
    StringMap.fold (fun key value acc -> (key, value) :: acc) args_map []
  in
  let worklist = List.rev (get_worklist g []) in
  debug_printf "\nworklist: %s\n for graph: %s \n" (dump worklist) (string_of_graph g);
  let colored = color_help worklist StringMap.empty in
  let env = color_map_to_env colored in
  env
;;

let rec lookup (funname : string) (name : string) (env : naive_stack_env) =
  match List.find_opt (fun (f, _) -> funname = f) env with
  | Some (_, name_env) ->
    (match List.find_opt (fun (n, _) -> name = n) name_env with
    | Some (_, arg) -> arg
    | None ->
      if funname = "closure#0"
      then (
        debug_printf
          "can't look up name: %s in func: %s in env: \n %s \n\n"
          name
          funname
          (dump env);
        raise (InternalCompilerError (sprintf "failed to lookup name %s " name)))
      else lookup "closure#0" name env)
  | None ->
    debug_printf "can't look up name %s fun: %s in env: \n %s \n\n" name funname (dump env);
    raise (InternalCompilerError (sprintf "failed to lookup function %s" funname))
;;

let lookup_env (funname : string) (env : naive_stack_env) =
  match List.find_opt (fun (f, _) -> funname = f) env with
  | Some (_, name_env) -> name_env
  | None ->
    raise (InternalCompilerError (sprintf "failed to lookup function %s" funname))
;;

let get_next_function (expr : (tag * StringSet.t) cexpr) : string =
  match expr with
  | CLambda (_, _, (tag, _)) -> sprintf "closure#%d" tag
  | _ -> ""
;;

let rec allocate_A
    (expr : (tag * StringSet.t) aexpr)
    (env : arg name_envt name_envt)
    (funname : string)
    : arg name_envt name_envt
  =
  match expr with
  | ALet (_, cexpr, body, (_, free_vars)) ->
    debug_printf "\na let free vars: %s\n" (dump free_vars);
    allocate_A body (allocate_C cexpr env funname) funname
  | ACExpr c -> allocate_C c env funname
  | ASeq (c, a, _) ->
    let env1 = allocate_C c env funname in
    allocate_A a env1 funname
  | ALetRec (bindings, body, (_, _)) ->
    (*add name to fun's env at rbp+16*)
    (* For closure#0, the main entry point already allocated stack slots for all
       bindings. Don't overwrite them with color_graph results. *)
    let merged_env =
      if funname = "closure#0" then
        env  (* Keep the pre-computed stack allocations *)
      else begin
        let interfered = interfere expr StringSet.empty in
        debug_printf "\n aletrec graph: %s\n" (string_of_graph interfered);
        let outer_env = color_graph interfered in
        debug_printf "\n aletrec env: %s\n" (dump outer_env);
        (* Merge the new allocations into the current function's env *)
        add_or_replace_env funname outer_env env
      end
    in
    let lambda_envs =
      List.fold_right
        (fun (_, lambda) acc -> allocate_C lambda acc funname)
        bindings
        merged_env
    in
    let lambda_envs_with_recs =
      List.fold_right
        (fun (name, lambda) acc ->
          let lambda_tag =
            match lambda with
            | CLambda (_, _, (t, _)) -> t
            | _ -> failwith "well formedness violation"
          in
          let lambda_name = sprintf "closure#%d" lambda_tag in
          add_or_replace_arg lambda_name name (RegOffset (16, RBP)) acc)
        bindings
        lambda_envs
    in
    (* Also allocate body *)
    allocate_A body lambda_envs_with_recs funname

and add_or_replace_env
    (funname : string)
    (new_bindings : arg name_envt)
    (env : arg name_envt name_envt)
    : arg name_envt name_envt
  =
  (* Add or merge new_bindings into funname's environment *)
  let exists = List.exists (fun (f, _) -> f = funname) env in
  if exists then
    List.map
      (fun (ename, env2) ->
        if ename = funname
        then ename, List.fold_right (fun (n, v) e -> add_or_replace_help n v e) new_bindings env2
        else ename, env2)
      env
  else
    (funname, new_bindings) :: env

and add_or_replace_arg
    (funname : string)
    (argname : string)
    (newvalue : arg)
    (env : arg name_envt name_envt)
  =
  let exists = List.exists (fun (f, _) -> f = funname) env in
  if exists then
    List.map
      (fun (ename, env2) ->
        if ename = funname
        then ename, add_or_replace_help argname newvalue env2
        else ename, env2)
      env
  else
    (funname, [(argname, newvalue)]) :: env

and add_or_replace_help (argname : string) (newvalue : arg) (env : arg name_envt)
    : arg name_envt
  =
  match env with
  | [] -> [ argname, newvalue ]
  | (name, value) :: rest ->
    if argname = name
    then (name, newvalue) :: rest
    else (name, value) :: add_or_replace_help argname newvalue rest

and allocate_C
    (expr : (tag * StringSet.t) cexpr)
    (env : arg name_envt name_envt)
    (funname : string)
    : arg name_envt name_envt
  =
  match expr with
  | CLambda (binds, body, (tag, fvs)) ->
    let new_name = sprintf "closure#%d" tag in
    debug_printf "\nbegin closure: %s\n" new_name;
    let fvs_list = StringSet.elements fvs in
    let num_fvs = List.length fvs_list in
    (* Free variables have FIXED stack slots at [RBP-8], [RBP-16], etc.
       because compile.ml loads them there from the closure.
       So we DON'T include them in register allocation - just assign fixed slots. *)
    let fvs_env = List.mapi (fun i fv ->
      (fv, RegOffset (~-8 * (i + 1), RBP))) fvs_list in
    (* Build interference graph for body, excluding free variables *)
    let interfered_body = interfere body StringSet.empty in
    (* Remove free variables from the graph - they have fixed locations *)
    let interfered_body_no_fvs =
      List.fold_right (fun fv g -> Graph.remove fv g) fvs_list interfered_body in
    debug_printf "\n%s clambda graph (no fvs): \n%s\n" new_name (string_of_graph interfered_body_no_fvs);
    (* Color the remaining variables - these need slots AFTER the free variable slots *)
    let colored =
      if Graph.is_empty interfered_body_no_fvs then []
      else color_graph interfered_body_no_fvs in
    debug_printf "\n colored env (before offset): %s\n" (dump colored);
    (* Offset any stack allocations by the number of free variable slots *)
    let adjusted_env = List.map (fun (name, arg) ->
      match arg with
      | RegOffset (offset, RBP) when offset < 0 ->
        (* Stack slot - offset it by num_fvs slots *)
        (name, RegOffset (offset - (num_fvs * 8), RBP))
      | _ -> (name, arg)
    ) colored in
    debug_printf "\n adjusted env: %s\n" (dump adjusted_env);
    (* Combine: fvs_env + adjusted_env *)
    let new_env = fvs_env @ adjusted_env in
    debug_printf "\n new env: %s\n" (dump new_env);
    let args_env = List.mapi (fun i a -> a, RegOffset (word_size * (i + 3), RBP)) binds in
    let final_env =
      List.fold_right
        (fun (name, value) env -> add_or_replace_arg new_name name value env)
        args_env
        (allocate_A body ([ new_name, new_env ] @ env) new_name)
    in
    debug_printf "\n clambda final env: %s\n" (dump final_env);
    final_env
  | CIf (_, thn, els, _) ->
    let thn_env = allocate_A thn env funname in
    allocate_A els thn_env funname
  | _ -> env
;;

let register_allocation (prog : tag aprogram) : tag aprogram * arg name_envt name_envt =
  match prog with
  | AProgram (expr, prog_tag) ->
    (* For closure#0, use simple sequential stack allocation (like naive)
       because all bindings may be stored in closures and accessed later.
       For inner lambdas, we can use register allocation. *)
    let cached_expr = cache_A expr in
    (* Use naive-style sequential allocation for the main expression *)
    let rec allocate_main expr si =
      match expr with
      | ALet (name, value, body, _) ->
        let slot = RegOffset (~-si * 8, RBP) in
        (name, slot) :: allocate_main body (si + 1)
      | ALetRec (bindings, body, _) ->
        let binding_slots = List.mapi (fun i (name, _) ->
          (name, RegOffset (~-(si + i) * 8, RBP))) bindings in
        binding_slots @ allocate_main body (si + List.length bindings)
      | ASeq (_, rest, _) -> allocate_main rest si
      | ACExpr _ -> []
    in
    let outer_env = allocate_main cached_expr 1 in
    (* Allocate for nested lambdas using register allocation *)
    let exp_envt = allocate_A cached_expr [ "closure#0", outer_env ] "closure#0" in
    AProgram (expr, prog_tag), exp_envt
;;
