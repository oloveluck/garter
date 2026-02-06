open Assembly
open Exprs
open Printf
open Errors

let callee_end_function = [ IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet ]

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

let function_prelude (stack_depth : int) =
  [ IPush (Reg RBP) ]
  @ [ IMov (Reg RBP, Reg RSP) ]
  @ [ ISub (Reg RSP, Const (Int64.mul (Int64.of_int stack_depth) 8L)) ]
;;

let function_postlude = [ IMov (Reg RSP, Reg RBP); IPop (Reg RBP); IRet ]

let print_instructions =
  let instructions = [ IMov (Reg RDI, Reg RAX); ICall (Label "?print") ] in
  instructions
;;

let print_stack_instructions =
  let instructions =
    [ IMov (Reg RDI, Reg RAX)
    ; IMov (Reg RSI, Reg RSP)
    ; IMov (Reg RDX, Reg RBP)
    ; IMov (Reg RCX, Const 0L)
    ; ICall (Label "?print_stack")
    ]
  in
  instructions
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

(* Shared utility functions for stack environments *)
type 'a name_envt = (string * 'a) list
type naive_stack_env = arg name_envt name_envt

(* Count the number of stack slots needed for an aexpr *)
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

(* Add a variable binding to a function's environment *)
let rec add_to_fun_env
    (funname : string)
    (name : string)
    (arg : arg)
    (env : naive_stack_env)
    : naive_stack_env
  =
  match env with
  | [] -> [ funname, [ name, arg ] ]
  | (envname, l) :: rest ->
    if funname = envname
    then (envname, (name, arg) :: l) :: rest
    else (envname, l) :: add_to_fun_env funname name arg rest
;;

(* Insert a new function into the environment with an empty binding list *)
let rec insert_fun_in_env (funname : string) (env : naive_stack_env)
    : naive_stack_env
  =
  match env with
  | [] -> [ funname, [] ]
  | (envname, l) :: rest ->
    if funname = envname
    then (envname, l) :: rest
    else (envname, l) :: insert_fun_in_env funname rest
;;
