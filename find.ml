open Errors
open Printf
open Exprs
open ExtLib

let rec find ls x =
  match ls with
  | [] ->
    printf "\n %s IN: %s \n" x (dump ls);
    raise (InternalCompilerError (sprintf "Name %s not found" x))
  | (y, v) :: rest -> if y = x then v else find rest x
;;

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
