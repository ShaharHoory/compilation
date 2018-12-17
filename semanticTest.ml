(* semanticTest.ml
 * Tests for semantic-analyser.ml
 * Programmer: Nitsan Soffair and Amir Abramovich, 2018
 *)

#use "semantic-analyser.ml";;

open Semantics;;
open Tag_Parser;;
open Reader;;
open PC;;

(* Colors for print *)
let red = "\027[38;5;196m";;
let grn = "\027[38;5;082m";;
let yel = "\027[38;5;226m";;
let mag = "\027[38;5;201m";;
let purple = "\027[0;35m";;
let cyan = "\027[0;36m";;
let reset = "\027[0m";;

(* Print # number of test that failed *)
let printFail failed = List.map (fun (n, b) -> Printf.printf "test %s %d %s failed\n" red n reset) failed;;

(* Got list of test that failed *)
let getFailed tests = List.filter (fun (n, e) -> e = false) tests;;

(* Print summary *)
let printSum color typ nfailed nsuccess = 
    (Printf.printf "\n%s%s tests: %s \nfailed- %s%d%s\npassed- %s%d%s\n\n" color typ reset red nfailed reset grn nsuccess reset);;

(* Helper function for test, print sum *)
let testSum color typ list = 
    let sum = List.length list in
    let failed = (getFailed list) in
    let nfailed = List.length failed in
    let nsuccess = sum - nfailed in
    (printSum color typ nfailed nsuccess);;

(* Helper function for test, print test that failed *)
let testFailed list = 
    let failed = (getFailed list) in
    (printFail failed);;

let allPassed color list = 
  let failed = (getFailed list) in
  if failed = [] then (Printf.printf "%sALL TESTS PASSED\n%s" color reset);;

(* Print message *)
let print color txt = (Printf.printf "%s*************************** %s *******************************%s\n" color txt reset);;

(* Compare expr', add support for Box *)
let rec expr'_eq e1 e2 =
  match e1, e2 with
    | Const' Void, Const' Void -> true
    | Const'(Sexpr s1), Const'(Sexpr s2) -> sexpr_eq s1 s2
    | Var'(VarFree v1), Var'(VarFree v2) -> String.equal v1 v2
    | Var'(VarParam (v1,mn1)), Var'(VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
    | Var'(VarBound (v1,mj1,mn1)), Var'(VarBound (v2,mj2,mn2)) -> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
    | Box' (VarFree v1), Box' (VarFree v2) | BoxGet' (VarFree v1), Box' (VarFree v2) ->  String.equal v1 v2
    | Box' (VarParam (v1,mn1)), Box' (VarParam (v2,mn2)) 
    | BoxGet' (VarParam (v1,mn1)), BoxGet' (VarParam (v2,mn2)) -> String.equal v1 v2 && mn1 = mn2
    | Box' (VarBound (v1,mj1,mn1)), Box' (VarBound (v2,mj2,mn2)) 
    | BoxGet' (VarBound (v1,mj1,mn1)), BoxGet'(VarBound (v2,mj2,mn2))-> String.equal v1 v2 && mj1 = mj2  && mn1 = mn2

    | BoxSet'(VarFree v1, e1), BoxSet'(VarFree v2, e2) -> expr'_eq e1 e2 && String.equal v1 v2
    | BoxSet'(VarParam (v1,mn1), e1), BoxSet'(VarParam (v2,mn2), e2) -> expr'_eq e1 e2 && String.equal v1 v2 && mn1 = mn2
    | BoxSet'(VarBound (v1,mj1,mn1), e1), BoxSet'(VarBound (v2,mj2,mn2), e2) -> 
      expr'_eq e1 e2 && String.equal v1 v2 && mj1 = mj2  && mn1 = mn2
    | If'(t1, th1, el1), If'(t2, th2, el2) -> (expr'_eq t1 t2) &&
                                              (expr'_eq th1 th2) &&
                                                (expr'_eq el1 el2)
    | (Seq'(l1), Seq'(l2)
    | Or'(l1), Or'(l2)) -> List.for_all2 expr'_eq l1 l2
    | (Set'(var1, val1), Set'(var2, val2)
    | Def'(var1, val1), Def'(var2, val2)) -> (expr'_eq var1 var2) &&
                                              (expr'_eq val1 val2)
    | LambdaSimple'(vars1, body1), LambdaSimple'(vars2, body2) ->
      (List.for_all2 String.equal vars1 vars2) &&
        (expr'_eq body1 body2)
    | LambdaOpt'(vars1, var1, body1), LambdaOpt'(vars2, var2, body2) ->
      (String.equal var1 var2) &&
        (List.for_all2 String.equal vars1 vars2) &&
          (expr'_eq body1 body2)
    | Applic'(e1, args1), Applic'(e2, args2)
    | ApplicTP'(e1, args1), ApplicTP'(e2, args2) ->
    (expr'_eq e1 e2) &&
      (List.for_all2 expr'_eq args1 args2)
    | _ -> false;;

print grn "START TESTS";;


(* Lexical address tests *)
let a1 = expr'_eq (annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x)
    (list (lambda () x)
          (lambda (y) 
            (set! x y))))"))) (  LambdaSimple' (["x"],
                                Applic' (Var' (VarFree "list"),
                                [LambdaSimple' ([], Var' (VarBound ("x", 0, 0)));
                                  LambdaSimple' (["y"],
                                  Set' (Var' (VarBound ("x", 0, 0)), Var' (VarParam ("y", 0))))])));;
                                  
let a2 = expr'_eq (annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y) (+ x y))"))) (  LambdaSimple' (["x"; "y"],
                                Applic' (Var' (VarFree "+"),
                                [Var' (VarParam ("x", 0)); Var' (VarParam ("y", 1))])));;

let a3 = expr'_eq (annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y z) (+ x y z))"))) (  LambdaSimple' (["x"; "y"; "z"],
                                Applic' (Var' (VarFree "+"),
                                [Var' (VarParam ("x", 0)); Var' (VarParam ("y", 1));
                                  Var' (VarParam ("z", 2))])));;

let a4 = expr'_eq (annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y z) (+ x y (lambda (z)(+ z 1))))"))) (LambdaSimple' (["x"; "y"; "z"],
                                                  Applic' (Var' (VarFree "+"),
                                                    [Var' (VarParam ("x", 0)); Var' (VarParam ("y", 1));
                                                    LambdaSimple' (["z"],
                                                      Applic' (Var' (VarFree "+"),
                                                      [Var' (VarParam ("z", 0)); Const' (Sexpr (Number (Int 1)))]))])));;

let a5 = expr'_eq (annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y z)
    (+ x y (lambda (z)
              (+ z x))))"))) (  LambdaSimple' (["x"; "y"; "z"],
                                                    Applic' (Var' (VarFree "+"),
                                                    [Var' (VarParam ("x", 0)); Var' (VarParam ("y", 1));
                                                      LambdaSimple' (["z"],
                                                      Applic' (Var' (VarFree "+"),
                                                        [Var' (VarParam ("z", 0)); Var' (VarBound ("x", 0, 0))]))])));;

let a6 = expr'_eq (annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y z) (+ x y (lambda (z)(+ z (lambda (z)(+ z y))))))"))) (  LambdaSimple' (["x"; "y"; "z"],
                                                                  Applic' (Var' (VarFree "+"),
                                                                  [Var' (VarParam ("x", 0)); Var' (VarParam ("y", 1));
                                                                    LambdaSimple' (["z"],
                                                                    Applic' (Var' (VarFree "+"),
                                                                      [Var' (VarParam ("z", 0));
                                                                      LambdaSimple' (["z"],
                                                                        Applic' (Var' (VarFree "+"),
                                                                        [Var' (VarParam ("z", 0)); Var' (VarBound ("y", 1, 1))]))]))])));;

let a7 = expr'_eq (annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y z) (+ x y (lambda (z)(+ z (lambda (x)(+ x y))))))"))) (  LambdaSimple' (["x"; "y"; "z"],
                                                                      Applic' (Var' (VarFree "+"),
                                                                      [Var' (VarParam ("x", 0)); Var' (VarParam ("y", 1));
                                                                        LambdaSimple' (["z"],
                                                                        Applic' (Var' (VarFree "+"),
                                                                          [Var' (VarParam ("z", 0));
                                                                          LambdaSimple' (["x"],
                                                                            Applic' (Var' (VarFree "+"),
                                                                            [Var' (VarParam ("x", 0)); Var' (VarBound ("y", 1, 1))]))]))])));;

let a8 = expr'_eq (annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y z) (+ x y (lambda (z)(+ z (lambda ()(+ x y))))))"))) (  LambdaSimple' (["x"; "y"; "z"],
                                                                    Applic' (Var' (VarFree "+"),
                                                                    [Var' (VarParam ("x", 0)); Var' (VarParam ("y", 1));
                                                                      LambdaSimple' (["z"],
                                                                      Applic' (Var' (VarFree "+"),
                                                                        [Var' (VarParam ("z", 0));
                                                                        LambdaSimple' ([],
                                                                          Applic' (Var' (VarFree "+"),
                                                                          [Var' (VarBound ("x", 1, 0)); Var' (VarBound ("y", 1, 1))]))]))])));;

let a9 = expr'_eq (annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y z) (+ x y (lambda (z)(+ x y z (lambda ()(+ x y z))))))"))) (  LambdaSimple' (["x"; "y"; "z"],
                                                                          Applic' (Var' (VarFree "+"),
                                                                          [Var' (VarParam ("x", 0)); Var' (VarParam ("y", 1));
                                                                            LambdaSimple' (["z"],
                                                                            Applic' (Var' (VarFree "+"),
                                                                              [Var' (VarBound ("x", 0, 0)); Var' (VarBound ("y", 0, 1));
                                                                              Var' (VarParam ("z", 0));
                                                                              LambdaSimple' ([],
                                                                                Applic' (Var' (VarFree "+"),
                                                                                [Var' (VarBound ("x", 1, 0)); Var' (VarBound ("y", 1, 1));
                                                                                  Var' (VarBound ("z", 0, 0))]))]))])));;

let annotate_test = [(1, a1); (2, a2); (3, a3); (4, a4); (5, a5); (6, a6); (7, a7); (8, a8); (9, a9); ];;
(testSum mag "Annotate lexical" annotate_test);;
(testFailed annotate_test);;


(* Tail calls tests *)
let t1 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x) (f (g (g x))))")))) (  LambdaSimple' (["x"],
                                  ApplicTP' (Var' (VarFree "f"),
                                  [Applic' (Var' (VarFree "g"),
                                    [Applic' (Var' (VarFree "g"), [Var' (VarParam ("x", 0))])])])));;

let t2 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x) (f (lambda (y) (g x y))))")))) (  LambdaSimple' (["x"],
                                              ApplicTP' (Var' (VarFree "f"),
                                              [LambdaSimple' (["y"],
                                                ApplicTP' (Var' (VarFree "g"),
                                                  [Var' (VarBound ("x", 0, 0)); Var' (VarParam ("y", 0))]))])));;

let t3 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y z w)(if (foo? x)(goo y)(boo (doo z))))")))) (  LambdaSimple' (["x"; "y"; "z"; "w"],
                                                          If' (Applic' (Var' (VarFree "foo?"), [Var' (VarParam ("x", 0))]),
                                                          ApplicTP' (Var' (VarFree "goo"), [Var' (VarParam ("y", 1))]),
                                                          ApplicTP' (Var' (VarFree "boo"),
                                                            [Applic' (Var' (VarFree "doo"), [Var' (VarParam ("z", 2))])]))));;

let t4 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y z)(f (if (g? x)(h y)(w z))))")))) (  LambdaSimple' (["x"; "y"; "z"],
                                                ApplicTP' (Var' (VarFree "f"),
                                                [If' (Applic' (Var' (VarFree "g?"), [Var' (VarParam ("x", 0))]),
                                                  Applic' (Var' (VarFree "h"), [Var' (VarParam ("y", 1))]),
                                                  Applic' (Var' (VarFree "w"), [Var' (VarParam ("z", 2))]))])));;

let t5 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (a b)(f a)(g a b)(display \"done!\\n\"))")))) (  LambdaSimple' (["a"; "b"],
                                                        Seq'
                                                        [Applic' (Var' (VarFree "f"), [Var' (VarParam ("a", 0))]);
                                                          Applic' (Var' (VarFree "g"),
                                                          [Var' (VarParam ("a", 0)); Var' (VarParam ("b", 1))]);
                                                          ApplicTP' (Var' (VarFree "display"),
                                                          [Const' (Sexpr (String "done!\n"))])]));;

let t6 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda () (and (f x) (g y) (h z)))")))) (  LambdaSimple' ([],
                                              If' (Applic' (Var' (VarFree "f"), [Var' (VarFree "x")]),
                                              If' (Applic' (Var' (VarFree "g"), [Var' (VarFree "y")]),
                                                ApplicTP' (Var' (VarFree "h"), [Var' (VarFree "z")]),
                                                Const' (Sexpr (Bool false))),
                                              Const' (Sexpr (Bool false)))));;

let t7 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda () (or (f (g x)) y))")))) (  LambdaSimple' ([],
                                      Or'
                                      [Applic' (Var' (VarFree "f"),
                                        [Applic' (Var' (VarFree "g"), [Var' (VarFree "x")])]);
                                        Var' (VarFree "y")]));;

let t8 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda () 
    (set! x (f y)))")))) (  LambdaSimple' ([],
                                      Set' (Var' (VarFree "x"),
                                      Applic' (Var' (VarFree "f"), [Var' (VarFree "y")]))));;

let t9 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda () 
    (set! x (f (lambda (y)
                  (g x y)))))")))) (  LambdaSimple' ([],
                                          Set' (Var' (VarFree "x"),
                                          Applic' (Var' (VarFree "f"),
                                            [LambdaSimple' (["y"],
                                              ApplicTP' (Var' (VarFree "g"),
                                              [Var' (VarFree "x"); Var' (VarParam ("y", 0))]))]))));;

let t10 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(lambda (x y z) 
    (cond ((f? x) (g y)) 
          ((g? x) (f x) (f y)) 
          (else (h x) (f y) (g (f x)))))")))) (LambdaSimple' (["x"; "y"; "z"],
                                                If' (Applic' (Var' (VarFree "f?"), 
                                                [Var' (VarParam ("x", 0))]),
                                                  ApplicTP' (Var' (VarFree "g"),
                                                    [Var' (VarParam ("y", 1))]),
                                                        If' (Applic' (Var' (VarFree "g?"),
                                                          [Var' (VarParam ("x", 0))]),
                                                            Seq' [Applic' (Var' (VarFree "f"), 
                                                            [Var' (VarParam ("x", 0))]);
                                                              ApplicTP' (Var' (VarFree "f"), 
                                                              [Var' (VarParam ("y", 1))])],
                                                              Seq' [Applic' 
                                                              (Var' (VarFree "h"),
                                                                  [Var' (VarParam ("x", 0))]);
                                                            Applic' (Var' (VarFree "f"),
                                                              [Var' (VarParam ("y", 1))]);
                                                            ApplicTP' (Var' (VarFree "g"),
                                                              [Applic' 
                                                              (Var' (VarFree "f"),
                                                              [Var' (VarParam ("x", 0))])])]))));;

let t11 = expr'_eq (annotate_tail_calls(annotate_lexical_addresses (tag_parse_expression (read_sexpr 
"(let ((x (f y))
      (y (g x))) 
        (goo (boo x) y))")))) (  Applic'
                                                    (LambdaSimple' (["x"; "y"],
                                                      ApplicTP' (Var' (VarFree "goo"),
                                                      [Applic' (Var' (VarFree "boo"), [Var' (VarParam ("x", 0))]);
                                                        Var' (VarParam ("y", 1))])),
                                                    [Applic' (Var' (VarFree "f"), [Var' (VarFree "y")]);
                                                    Applic' (Var' (VarFree "g"), [Var' (VarFree "x")])]));;

let tailcalls_test = [(1, t1); (2, t2); (3, t3); (4, t4); (5, t5); (6, t6); (7, t7); (8, t8); (9, t9); (10, t10); (11, t11);];;
(testSum cyan "Tail calls" tailcalls_test);;
(testFailed tailcalls_test);;


(* Box set tests *)
let b1 = (expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
          (define foo1 (lambda (x)
                          (list (lambda () x)
                                (lambda (y) 
                                  (set! x y)))))"))) 
          (Def' (Var' (VarFree "foo1"),
            LambdaSimple' (["x"],
              Seq'
              [Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
                ApplicTP' (Var' (VarFree "list"),
                [LambdaSimple' ([], BoxGet' (VarBound ("x", 0, 0)));
                  LambdaSimple' (["y"],
                  BoxSet' (VarBound ("x", 0, 0), Var' (VarParam ("y", 0))))])]))));;

let b2 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
          (define foo2 (lambda (x y)
                          (set! x (* x y))))")))
          (Def' (Var' (VarFree "foo2"),
            LambdaSimple' (["x"; "y"],
              Set' (Var' (VarParam ("x", 0)),
              Applic' (Var' (VarFree "*"),
                [Var' (VarParam ("x", 0)); Var' (VarParam ("y", 1))])))));;

let b3 =  expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
              (define foo3 (lambda (x y) 
                              (lambda () x) 
                              (lambda () y)
                              (lambda () (set! x y))))")))
                              (  Def' (Var' (VarFree "foo3"),
                              LambdaSimple' (["x"; "y"],
                               Seq'
                                [Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
                                 Seq'
                                  [LambdaSimple' ([], BoxGet' (VarBound ("x", 0, 0)));
                                   LambdaSimple' ([], Var' (VarBound ("y", 0, 1)));
                                   LambdaSimple' ([],
                                    BoxSet' (VarBound ("x", 0, 0), Var' (VarBound ("y", 0, 1))))]])));;
                        
let b4 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
          (define foo4 (lambda (x y)
                          (if x (lambda ()
                                  (set! y x))
                              (lambda (z) (set! x z)))))")))
          (Def' (Var' (VarFree "foo4"),
        LambdaSimple' (["x"; "y"],
          Seq'
          [Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
            If' (BoxGet' (VarParam ("x", 0)),
            LambdaSimple' ([],
              Set' (Var' (VarBound ("y", 0, 1)), BoxGet' (VarBound ("x", 0, 0)))),
            LambdaSimple' (["z"],
              BoxSet' (VarBound ("x", 0, 0), Var' (VarParam ("z", 0)))))])));;

let b5 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
          (define foo5
                (lambda (x y)
                  (list (lambda () 
                          (set! x (+ x 1)))
                    (lambda () y))))" )))
          ( Def' (Var' (VarFree "foo5"),
          LambdaSimple' (["x"; "y"],
          ApplicTP' (Var' (VarFree "list"),
            [LambdaSimple' ([],
              Set' (Var' (VarBound ("x", 0, 0)),
              Applic' (Var' (VarFree "+"),
                [Var' (VarBound ("x", 0, 0)); Const' (Sexpr (Number (Int 1)))])));
            LambdaSimple' ([], Var' (VarBound ("y", 0, 1)))]))));;

let b6 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
          (define foo6
            (lambda (x)
            (lambda (op)
            (cond ((eq? op 'read) (lambda () x))
            ((eq? op 'write) (lambda (val) (set! x val)))))))")))
            ( Def' (Var' (VarFree "foo6"),
            LambdaSimple' (["x"],
             LambdaSimple' (["op"],
              If'
               (Applic' (Var' (VarFree "eq?"),
                 [Var' (VarParam ("op", 0)); Const' (Sexpr (Symbol "read"))]),
               LambdaSimple' ([], Var' (VarBound ("x", 1, 0))),
               If'
                (Applic' (Var' (VarFree "eq?"),
                  [Var' (VarParam ("op", 0)); Const' (Sexpr (Symbol "write"))]),
                LambdaSimple' (["val"],
                 Set' (Var' (VarBound ("x", 1, 0)), Var' (VarParam ("val", 0)))),
                Const' Void))))));;

let b7 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
          (define foo7 ( lambda ( x)
            (let ((y 1)) 
            `(,(lambda () x) ,(set!  x y ))))) ")))
            (  Def' (Var' (VarFree "foo7"),
            LambdaSimple' (["x"],
             ApplicTP'
              (LambdaSimple' (["y"],
                ApplicTP' (Var' (VarFree "cons"),
                 [LambdaSimple' ([], Var' (VarBound ("x", 1, 0)));
                  Applic' (Var' (VarFree "cons"),
                   [Set' (Var' (VarBound ("x", 0, 0)), Var' (VarParam ("y", 0)));
                    Const' (Sexpr Nil)])])),
              [Const' (Sexpr (Number (Int 1)))]))));;

let b8 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr
      "(define foo8 (lambda (x y) 
                        (cons x (lambda () 
                                  (set! x y)))))")))
      (Def' (Var' (VarFree "foo8"),
          LambdaSimple' (["x"; "y"],
          Seq'
            [Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
            ApplicTP' (Var' (VarFree "cons"),
              [BoxGet' (VarParam ("x", 0));
              LambdaSimple' ([],
                BoxSet' (VarBound ("x", 0, 0), Var' (VarBound ("y", 0, 1))))])])));;

let b9 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
          (define foo9 (lambda (x y z)
                          (list (lambda ()
                                  (list (lambda (x) 
                                          (set! x z))
                                    (lambda ()
                                      (set! x z))
                                        x))
                              (lambda (y) 
                                (set! x y)))))")))
          (Def' (Var' (VarFree "foo9"),
          LambdaSimple' (["x"; "y"; "z"],
            Seq'
            [Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
              ApplicTP' (Var' (VarFree "list"),
              [LambdaSimple' ([],
                ApplicTP' (Var' (VarFree "list"),
                  [LambdaSimple' (["x"],
                    Set' (Var' (VarParam ("x", 0)), Var' (VarBound ("z", 1, 2))));
                  LambdaSimple' ([],
                    BoxSet' (VarBound ("x", 1, 0), Var' (VarBound ("z", 1, 2))));
                  BoxGet' (VarBound ("x", 0, 0))]));
                LambdaSimple' (["y"],
                BoxSet' (VarBound ("x", 0, 0), Var' (VarParam ("y", 0))))])])));;

let b10 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
            (lambda (x y)
              (list (lambda () x)
              (lambda () y)
              (lambda (z) (set! x z))))
            ")))
            (  LambdaSimple' (["x"; "y"],
            Seq'
             [Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
              ApplicTP' (Var' (VarFree "list"),
               [LambdaSimple' ([], BoxGet' (VarBound ("x", 0, 0)));
                LambdaSimple' ([], Var' (VarBound ("y", 0, 1)));
                LambdaSimple' (["z"],
                 BoxSet' (VarBound ("x", 0, 0), Var' (VarParam ("z", 0))))])]));;

let b11 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
            (lambda (x y)
              (list (lambda () x)
              (lambda (z) (set! y z))
              (lambda (z) (set! x z))))")))
            (LambdaSimple' (["x"; "y"],
            Seq'
             [Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
              ApplicTP' (Var' (VarFree "list"),
               [LambdaSimple' ([], BoxGet' (VarBound ("x", 0, 0)));
                LambdaSimple' (["z"],
                 Set' (Var' (VarBound ("y", 0, 1)), Var' (VarParam ("z", 0))));
                LambdaSimple' (["z"],
                 BoxSet' (VarBound ("x", 0, 0), Var' (VarParam ("z", 0))))])]));;

(* Due to Gilad comment, keep "x" & "y" in same Seq' *)
let b12 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
            (lambda (x y)
            (list (lambda () x) (lambda () y)
            (lambda (z) (set! y z))
            (lambda (z) (set! x z))))
            ")))
         (  LambdaSimple' (["x"; "y"],
         Seq'
          [Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
           Set' (Var' (VarParam ("y", 1)), Box' (VarParam ("y", 1)));
           ApplicTP' (Var' (VarFree "list"),
            [LambdaSimple' ([], BoxGet' (VarBound ("x", 0, 0)));
             LambdaSimple' ([], BoxGet' (VarBound ("y", 0, 1)));
             LambdaSimple' (["z"],
              BoxSet' (VarBound ("y", 0, 1), Var' (VarParam ("z", 0))));
             LambdaSimple' (["z"],
              BoxSet' (VarBound ("x", 0, 0), Var' (VarParam ("z", 0))))])]));;

let b13 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
      (define (func .  x)
                (list (lambda () x)
                      (lambda (z) (set! x z))
                (lambda (z) 
                  (set! x z))))")))
                  (Def' (Var' (VarFree "func"),
                  LambdaOpt' ([], "x",
                   Seq'
                    [Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
                     ApplicTP' (Var' (VarFree "list"),
                      [LambdaSimple' ([], BoxGet' (VarBound ("x", 0, 0)));
                       LambdaSimple' (["z"],
                        BoxSet' (VarBound ("x", 0, 0), Var' (VarParam ("z", 0))));
                       LambdaSimple' (["z"],
                        BoxSet' (VarBound ("x", 0, 0), Var' (VarParam ("z", 0))))])])));;

let b14 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
            (define (func .  x)
                      (lambda (sameRib)
                        (list (lambda () x)
                              (lambda (z)
                                  (set! x z)))))")))
                                  (Def' (Var' (VarFree "func"),
                                  LambdaOpt' ([], "x",
                                   LambdaSimple' (["samerib"],
                                    ApplicTP' (Var' (VarFree "list"),
                                     [LambdaSimple' ([], Var' (VarBound ("x", 1, 0)));
                                      LambdaSimple' (["z"],
                                       Set' (Var' (VarBound ("x", 1, 0)), Var' (VarParam ("z", 0))))])))));;

(* Due to Gilad comment, keep all vars in same Seq' *)
let b15 = expr'_eq (run_semantics (tag_parse_expression (read_sexpr "
          (define func (lambda (x y z w)
                          (list (lambda () x)
                                (lambda () y)
                                (lambda () z)
                                (lambda () w)
                                (lambda () (set! x 0))
                                (lambda () (set! y 1))
                                (lambda () (set! z 2))
                                (lambda () (set! w 3)))))")))
                 (  Def' (Var' (VarFree "func"),
                 LambdaSimple' (["x"; "y"; "z"; "w"],
                  Seq'
                   [Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
                    Set' (Var' (VarParam ("y", 1)), Box' (VarParam ("y", 1)));
                    Set' (Var' (VarParam ("z", 2)), Box' (VarParam ("z", 2)));
                    Set' (Var' (VarParam ("w", 3)), Box' (VarParam ("w", 3)));
                    ApplicTP' (Var' (VarFree "list"),
                     [LambdaSimple' ([], BoxGet' (VarBound ("x", 0, 0)));
                      LambdaSimple' ([], BoxGet' (VarBound ("y", 0, 1)));
                      LambdaSimple' ([], BoxGet' (VarBound ("z", 0, 2)));
                      LambdaSimple' ([], BoxGet' (VarBound ("w", 0, 3)));
                      LambdaSimple' ([],
                       BoxSet' (VarBound ("x", 0, 0), Const' (Sexpr (Number (Int 0)))));
                      LambdaSimple' ([],
                       BoxSet' (VarBound ("y", 0, 1), Const' (Sexpr (Number (Int 1)))));
                      LambdaSimple' ([],
                       BoxSet' (VarBound ("z", 0, 2), Const' (Sexpr (Number (Int 2)))));
                      LambdaSimple' ([],
                       BoxSet' (VarBound ("w", 0, 3), Const' (Sexpr (Number (Int 3)))))])])));;

let boxSet_test = [(1, b1); (2, b2); (3, b3); (4, b4); (5, b5); (6, b6); (7, b7); (8, b8); (9, b9); (10, b10); (11, b11); 
                   (12, b12); (13, b13); (14, b14); (15, b15)];;
(testSum purple "Box set" boxSet_test);;
(testFailed boxSet_test);;


(* All tests *)
let all_test = annotate_test @ tailcalls_test @ boxSet_test;;
(testSum yel "All" all_test);;
allPassed cyan all_test;;


print grn "END TESTS";;
