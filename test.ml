open Compile
open Runner
open Printf
open OUnit2
open Pretty
open Exprs
open Phases
open Errors

let t name program input expected =
  name >:: test_run ~args:[] ~std_input:input program name expected
;;

let ta name program input expected =
  name >:: test_run_anf ~args:[] ~std_input:input program name expected
;;

let tgc name heap_size program input expected =
  name
  >:: test_run ~args:[ string_of_int heap_size ] ~std_input:input program name expected
;;

let tvg name program input expected =
  name >:: test_run_valgrind ~args:[] ~std_input:input program name expected
;;

let tvgc name heap_size program input expected =
  name
  >:: test_run_valgrind
        ~args:[ string_of_int heap_size ]
        ~std_input:input
        program
        name
        expected
;;

let terr name program input expected =
  name >:: test_err ~args:[] ~std_input:input program name expected
;;

let tgcerr name heap_size program input expected =
  name
  >:: test_err ~args:[ string_of_int heap_size ] ~std_input:input program name expected
;;

let tanf name program input expected =
  name >:: fun _ -> assert_equal expected (anf (tag program)) ~printer:string_of_aprogram
;;

let tparse name program expected =
  name
  >:: fun _ ->
  assert_equal
    (untagP expected)
    (untagP (parse_string name program))
    ~printer:string_of_program
;;

let teq name actual expected =
  name >:: fun _ -> assert_equal expected actual ~printer:(fun s -> s)
;;

(* let tfvs name program expected = name>:: *)
(*   (fun _ -> *)
(*     let ast = parse_string name program in *)
(*     let anfed = anf (tag ast) in *)
(*     let vars = free_vars_P anfed [] in *)
(*     let c = Stdlib.compare in *)
(*     let str_list_print strs = "[" ^ (ExtString.String.join ", " strs) ^ "]" in *)
(*     assert_equal (List.sort c vars) (List.sort c expected) ~printer:str_list_print) *)
(* ;; *)

let builtins_size = 4 (* arity + 0 vars + codeptr + padding *) * 1
(* TODO FIXME (List.length Compile.native_fun_bindings) *)

let pair_tests =
  [ t
      "tup1"
      "let t = (4, (5, 6)) in\n\
      \            begin\n\
      \              t[0] := 7;\n\
      \              t\n\
      \            end"
      ""
      "(7, (5, 6))"
  ; t
      "tup2"
      "let t = (4, (5, nil)) in\n\
      \            begin\n\
      \              t[1] := nil;\n\
      \              t\n\
      \            end"
      ""
      "(4, nil)"
  ; t
      "tup3"
      "let t = (4, (5, nil)) in\n\
      \            begin\n\
      \              t[1] := t;\n\
      \              t\n\
      \            end"
      ""
      "(4, <cyclic tuple 1>)"
  ; t "tup4" "let t = (4, 6) in\n            (t, t)" "" "((4, 6), (4, 6))"
  ]
;;

let oom =
  [ tgcerr "oomgc1" (7 + builtins_size) "(1, (3, 4))" "" "Out of memory"
  ; tgc "oomgc2" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))"
  ; tvgc "oomgc3" (8 + builtins_size) "(1, (3, 4))" "" "(1, (3, 4))"
  ; tgc "oomgc4" (4 + builtins_size) "(3, 4)" "" "(3, 4)"
  ; tgcerr "oomgc5" (3 + builtins_size) "(1, 2, 3, 4, 5, 6, 7, 8, 9, 0)" "" "Allocation"
  ]
;;

let gc =
  [ tgc
      "gc_lam1"
      (10 + builtins_size)
      "let f = (lambda: (1, 2)) in\n\
      \       begin\n\
      \         f();\n\
      \         f();\n\
      \         f();\n\
      \         f()\n\
      \       end"
      ""
      "(1, 2)"
  ]
;;

let input = [ t "input1" "let x = input() in x + 2" "123" "125" ]

let reg_tests =
  [ t "test_is_bool1" "isbool(true)" "" "true"
  ; t "test_is_bool2" "isbool(false)" "" "true"
  ; t "test_is_bool3" "isbool(0)" "" "false"
  ; t "test_is_bool4" "isbool(123)" "" "false"
  ; t "test_is_bool5" "isbool((0,123))" "" "false"
  ; t "test_is_bool6" "isbool((true,123))" "" "false"
  ; t "test_is_bool7" "isbool((123,123))" "" "false"
  ; t "test_is_bool8" "isbool((false,123))" "" "false"
  ; t "test_is_tuple1" "istuple(true)" "" "false"
  ; t "test_is_tuple2" "istuple(false)" "" "false"
  ; t "test_is_tuple3" "istuple(0)" "" "false"
  ; t "test_is_tuple4" "istuple(123)" "" "false"
  ; t "test_is_tuple5" "istuple((0,123))" "" "true"
  ; t "test_is_tuple6" "istuple((true,123))" "" "true"
  ; t "test_is_tuple7" "istuple((123,123))" "" "true"
  ; t "test_is_tuple8" "istuple((false,123))" "" "true"
  ; t "test_is_num1" "isnum(true)" "" "false"
  ; t "test_is_num2" "isnum(false)" "" "false"
  ; t "test_is_num3" "isnum(0)" "" "true"
  ; t "test_is_num4" "isnum(123)" "" "true"
  ; t "test_is_num5" "isnum((0,123))" "" "false"
  ; t "test_is_num6" "isnum((true,123))" "" "false"
  ; t "test_is_num7" "isnum((123,123))" "" "false"
  ; t "test_is_num8" "isnum((false,123))" "" "false"
  ; t "tuple_0" "(0,1)" "" "(0, 1)"
  ; t
      "tup1"
      "let t = (4, (5, 6)) in\n\
      \            begin\n\
      \              t[0] := 7;\n\
      \              t\n\
      \            end"
      ""
      "(7, (5, 6))"
  ; t
      "tup_get"
      "let t = (4, 5) in\n            begin\n              t[1]\n\n                  end"
      ""
      "5"
  ; t
      "tup_set"
      "let t = (4, 5) in\n              let x = t[1] := 7 in \n              t[1]\n"
      ""
      "7"
  ; t
      "tup2"
      "let t = (4, (5, nil)) in\n\
      \            begin\n\
      \              t[1] := nil;\n\
      \              t\n\
      \            end"
      ""
      "(4, nil)"
  ; t "tup4" "let t = (4, 6) in\n            (t, t)" "" "((4, 6), (4, 6))"
  ; t
      "eq2"
      "let t = (4, 6) in\n\n              let u = (5, 6) in\n        t == u"
      ""
      "false"
  ; t "eq3" "1 == 1" "" "true"
  ; t "eq4" "1 == 2" "" "false"
  ; t
      "eq5"
      "let t = (4, 6, (7, 8)) in\n\n\
      \              let u = (4, 6, (7, 8)) in\n\
      \        t == u"
      ""
      "true"
  ; t "add1" "let x = 1 in x + x" "" "2"
  ; t "and2" "true && true" "" "true"
    (* ; terr "err_high" "let x = (1, 2, 3) in x [3]" "" "Error 8: get high index"
       ; terr "err_high2" "let x = (1, 2, 3) in x [4]" "" "Error: Error 8: Error: index too large to get, got 3"
       ; terr "err_low" "let x = (1, 2, 3) in x[-1]" "" "Error 7: get low index"
       ; terr "err_high3" "let x = () in x [0]" "" "Error 8: Error: index too large to get, got 3"
       ; terr "err_nil_deref" "let x = nil in x [0]" "" "Error 9: Error: get expected numeric index, got nil" *)
  ; t "destructure" "let (a, b) = (1, 2) in a" "" "1"
  ; t "destructure_2" "let (a, (b, c)) = (1, (2, 3)) in c" "" "3"
  ; (* Some useful if tests to start you off *)
    t "if1" "if 7 < 8: 5 else: 3" "" "5"
  ; t "if2" "if 0 > 1: 4 else: 2" "" "2"
  ; terr "overflow" "add1(5073741823000000000)" "" "overflow"
  ; t "l1" "let add = (lambda (x, y): x + y) in\nadd(5, 6)" "" "11"
  ; t "l2" "let z = 5 in let add = (lambda (x, y): x + y) in\nadd(5, 6)" "" "11"
    (* ; terr "calling_nonfunction1" "4(3)" "" "some" *)
    (* ; terr "calling_nonfunction2" "true(3)" "" "some" *)
    (* ; terr "calling_nonfunction3" "nil(3)" "" "some" *)
    (* ; terr
      "function scope"
      "func(3)"
      ""
      "The identifier func, used at <calling_nonfunction, 1:0-1:4>, is not in scope" *)
  ; t "l3" "let z = 1 in let add = (lambda (x, y): x + y + z) in\nadd(5, 6)" "" "12"
  ; t "fact" "def fact(n): if n < 2: 1 else: n * fact(n - 1)\n\nfact(5)" "" "120"
  ; t "print1" "print(2) + print(3)" "" "2\n3\n5"
  ; t "print2" "let x = (lambda(r): print(r)) in x(5)" "" "5\n5"
  ; t
      "print3"
      "let x = (lambda(r): print(r)) in\n let y = (lambda (s): x(s))\n in y(5)"
      ""
      "5\n5"
  ; t
      "pass1"
      "let app_to_5 = (lambda(x): x(5)) in \n\
       let print_a = (lambda(x): print(x)) in\n\
       app_to_5(print_a)\n"
      ""
      "5\n5"
  ]
;;

(* let suite = "unit_tests" >::: pair_tests @ oom @ gc @ input @ reg_tests *)
let suite = "unit_tests" >::: reg_tests
let () = run_test_tt_main ("all_tests" >::: [ suite; input_file_test_suite () ])
