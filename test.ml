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
  (* Tuple bounds checking tests - fixed *)
  ; terr "err_high" "let x = (1, 2, 3) in x[3]" "" "Tuple index 3 out of bounds"
  ; terr "err_low" "let x = (1, 2, 3) in x[-1]" "" "Tuple index -1 out of bounds"
  ; terr "err_nil_deref" "let x = nil in x[0]" "" "tried to access component of nil"
  ; terr "calling_nonfunction1" "4(3)" "" "Cannot unify Int with"
  ; terr "calling_nonfunction2" "true(3)" "" "Cannot unify Bool with"
  ; terr "calling_nonfunction3" "nil(3)" "" "Cannot unify Nil with"
  ; t "destructure" "let (a, b) = (1, 2) in a" "" "1"
  ; t "destructure_2" "let (a, (b, c)) = (1, (2, 3)) in c" "" "3"
  ; (* Some useful if tests to start you off *)
    t "if1" "if 7 < 8: 5 else: 3" "" "5"
  ; t "if2" "if 0 > 1: 4 else: 2" "" "2"
  ; terr "overflow" "add1(5073741823000000000)" "" "overflow"
  ; t "l1" "let add = (lambda (x, y): x + y) in\nadd(5, 6)" "" "11"
  ; t "l2" "let z = 5 in let add = (lambda (x, y): x + y) in\nadd(5, 6)" "" "11"
  ; terr "arity_mismatch" "(lambda(x): x)(1, 2)" "" "Function expects 1 arguments, got 2"
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
  (* Nested tuples *)
  ; t "nested_tuple1" "((1, 2), (3, 4))" "" "((1, 2), (3, 4))"
  ; t "nested_tuple2" "let t = ((1, 2), (3, 4)) in t[0][1]" "" "2"
  ; t "nested_tuple3" "let t = ((1, 2), (3, 4)) in t[1][0]" "" "3"
  (* Negative numbers *)
  ; t "neg1" "-5 + 3" "" "-2"
  ; t "neg2" "-10" "" "-10"
  ; t "neg3" "0 - 5" "" "-5"
  ; t "neg4" "-3 * -4" "" "12"
  (* Zero handling *)
  ; t "zero1" "0" "" "0"
  ; t "zero2" "0 + 0" "" "0"
  ; t "zero3" "5 * 0" "" "0"
  ; t "zero4" "0 == 0" "" "true"
  (* Multiple free variables in closures *)
  ; t "multi_free1" "let a = 1 in let b = 2 in let c = 3 in let f = (lambda(x): a + b + c) in f(0)" "" "6"
  ; t "multi_free2" "let x = 10 in let y = 20 in let f = (lambda(z): x + y + z) in f(5)" "" "35"
  (* Nested lambdas *)
  ; t "nested_lam1" "let f = (lambda(x): (lambda(y): x + y)) in f(3)(4)" "" "7"
  ; t "nested_lam2" "let add = (lambda(x): (lambda(y): x + y)) in let add5 = add(5) in add5(10)" "" "15"
  ; t "nested_lam3" "let f = (lambda(a): (lambda(b): (lambda(c): a + b + c))) in f(1)(2)(3)" "" "6"
  (* Boolean operations *)
  ; t "bool1" "true && false" "" "false"
  ; t "bool2" "true || false" "" "true"
  ; t "bool3" "!(true)" "" "false"
  ; t "bool4" "!(false)" "" "true"
  (* Comparison edge cases *)
  ; t "cmp1" "0 < 1" "" "true"
  ; t "cmp2" "0 > 1" "" "false"
  ; t "cmp3" "5 <= 5" "" "true"
  ; t "cmp4" "5 >= 5" "" "true"
  (* Type checking functions *)
  ; t "isnum_neg" "isnum(-5)" "" "true"
  ; t "isnum_zero" "isnum(0)" "" "true"
  ; t "isbool_and" "isbool(true && false)" "" "true"
  ; t "istuple_nil" "istuple(nil)" "" "false"
  (* Error: type errors in operations - now caught at compile time by type checker *)
  ; terr "type_err_plus" "1 + true" "" "Cannot unify Bool with Int"
  ; terr "type_err_minus" "true - 1" "" "Cannot unify Bool with Int"
  ; terr "type_err_times" "false * 2" "" "Cannot unify Bool with Int"
  ; terr "type_err_and" "1 && true" "" "Cannot unify Int with Bool"
  ; terr "type_err_or" "false || 5" "" "Cannot unify Int with Bool"
  ; terr "type_err_if" "if 1: 2 else: 3" "" "Cannot unify Int with Bool"
  ; terr "type_err_cmp" "1 < true" "" "Cannot unify Bool with Int"
  (* Division and modulo tests *)
  ; t "div1" "10 / 2" "" "5"
  ; t "div2" "17 / 5" "" "3"
  ; t "div3" "100 / 10" "" "10"
  ; t "div_neg1" "(-10) / 2" "" "-5"
  ; t "div_neg2" "10 / (-2)" "" "-5"
  ; t "div_neg3" "(-10) / (-2)" "" "5"
  ; t "mod1" "10 % 3" "" "1"
  ; t "mod2" "17 % 5" "" "2"
  ; t "mod3" "100 % 7" "" "2"
  ; t "mod_neg1" "(-10) % 3" "" "-1"
  ; t "divmod_expr" "let x = 17 in let y = 5 in (x / y, x % y)" "" "(3, 2)"
  ; terr "div_zero" "5 / 0" "" "division by zero"
  ; terr "mod_zero" "5 % 0" "" "division by zero"
  ; terr "div_type_err" "5 / true" "" "Cannot unify Bool with Int"
  ; terr "mod_type_err" "true % 3" "" "Cannot unify Bool with Int"
  ]
;;

let suite = "unit_tests" >::: pair_tests @ reg_tests
let () = run_test_tt_main ("all_tests" >::: [ suite; input_file_test_suite () ])
