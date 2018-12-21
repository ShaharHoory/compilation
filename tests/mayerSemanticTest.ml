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
 
 (* Box set tests *)
 let b1 = (expr'_eq (run_semantics 
           (LambdaSimple ([], Const (Sexpr (Number (Int 1))))))) 
           (LambdaSimple' ([], Const' (Sexpr (Number (Int (1))))));;
 
 let b2 = expr'_eq (run_semantics (Const
 (Sexpr
   (Pair
     (Pair (Symbol "lambda",
       Pair (Nil,
        Pair
         (Pair (Symbol "lambda",
           Pair (Pair (Symbol "x", Nil),
            Pair (Symbol "x",
             Pair
              (Pair (Symbol "lambda",
                Pair (Nil,
                 Pair
                  (Pair (Symbol "set!",
                    Pair (Symbol "x", Pair (Number (Int 1), Nil))),
                  Nil))),
              Nil)))),
         Nil))),
     Nil)))))
     (Const' (Sexpr (Pair (Pair (Symbol "lambda",
      Pair (Nil, Pair (Pair (Symbol "lambda", Pair (Pair (Symbol "x", Nil), 
      Pair (Symbol "x", Pair (Pair (Symbol "lambda", Pair (Nil, Pair (Pair (Symbol "set!", 
      Pair (Symbol "x", Pair (Number (Int (1)), Nil))), Nil))), Nil)))), Nil))), Nil))));;
 
 (* Change due to "box with Seq" Q in Forum *)
 let b3 = expr'_eq (run_semantics (Applic
 (LambdaSimple (["x"],
   If (Applic (Var "x", [Const (Sexpr (Number (Int 1)))]),
    Applic (Var "x", [Const (Sexpr (Number (Int 2)))]),
    Applic
     (LambdaSimple (["x"], Set (Var "x", Const (Sexpr (Number (Int 0))))),
     [Const (Sexpr (Number (Int 3)))]))),
 [LambdaSimple (["x"], Var "x")])))
                               (Applic' (LambdaSimple' (["x"], Seq' ([Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));If' (Applic' (BoxGet' (VarParam ("x", 0)), [Const' (Sexpr (Number (Int (1))))]), ApplicTP' (BoxGet' (VarParam ("x", 0)), [Const' (Sexpr (Number (Int (2))))]), ApplicTP' (LambdaSimple' (["x"], Set' (Var' (VarParam ("x", 0)), Const' (Sexpr (Number (Int (0)))))), 
                               [Const' (Sexpr (Number (Int (3))))]))])), [LambdaSimple' (["x"], Var' (VarParam ("x", 0)))]));;
                         
 
 let b4 = expr'_eq (run_semantics (LambdaSimple (["x"],
 Or
  [Applic
    (LambdaOpt (["y"], "z",
      Applic
       (LambdaSimple ([],
         Applic (LambdaSimple ([], Applic (Var "+", [Var "x"; Var "z"])), [])),
       [])),
    [Var "x"; Const (Sexpr (Number (Int 1)))]);
   LambdaSimple ([], Set (Var "x", Var "w")); Applic (Var "w", [Var "w"])])))
           (LambdaSimple' (["x"], Seq' ([Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
           Or' ([Applic' (LambdaOpt' (["y"], "z", ApplicTP' (LambdaSimple' ([], ApplicTP' (LambdaSimple' ([], ApplicTP' (Var' (VarFree "+"), [BoxGet' (VarBound ("x", 2, 0));Var' (VarBound ("z", 1, 1))])), [])), [])), [BoxGet' (VarParam ("x", 0));Const' (Sexpr (Number (Int (1))))]);LambdaSimple' ([], BoxSet' (VarBound ("x", 0, 0), 
           Var' (VarFree "w")));ApplicTP' (Var' (VarFree "w"), [Var' (VarFree "w")])])])));;
 
 let b5 = expr'_eq (run_semantics (If (Applic (LambdaSimple (["y"], Var "x"), []),
 Applic
  (LambdaSimple (["x"],
    Seq
     [Set (Var "x", Var "y");
      LambdaSimple ([], Set (Var "x", Const (Sexpr (Number (Int 1)))))]),
  [Const (Sexpr (Symbol "a"))]),
 LambdaSimple (["x"], Set (Var "x", Var "y")))))
           ( If' (Applic' (LambdaSimple' (["y"], Var' (VarFree "x")), []),
            Applic' (LambdaSimple' (["x"], Seq' ([Set' (Var' (VarParam ("x", 0)), 
            Var' (VarFree "y"));LambdaSimple' ([], Set' (Var' (VarBound ("x", 0, 0)), 
            Const' (Sexpr (Number (Int (1))))))])), [Const' (Sexpr (Symbol "a"))]), 
            LambdaSimple' (["x"], Set' (Var' (VarParam ("x", 0)), Var' (VarFree "y")))));;
 
 let b6 = expr'_eq (run_semantics (
 LambdaOpt (["x"; "y"; "z"], "w",
 Seq
  [Var "z";
   Applic
    (LambdaSimple ([],
      Seq [Set (Var "w", Var "w"); Applic (Applic (Var "y", [Var "x"]), [])]),
    [])])))
             ( LambdaOpt' (["x";"y";"z"], "w", Seq' ([Var' (VarParam ("z", 2));ApplicTP' (LambdaSimple' ([], Seq' ([Set' (Var' (VarBound ("w", 0, 3)), Var' (VarBound ("w", 0, 3)));
             ApplicTP' (Applic' (Var' (VarBound ("y", 0, 1)), [Var' (VarBound ("x", 0, 0))]), [])])), [])])));;
 
 let b7 = expr'_eq (run_semantics (Def (Var "a",
 Applic
  (LambdaSimple ([],
    LambdaOpt ([], "x",
     Seq
      [Var "x";
       LambdaOpt ([], "y", Set (Var "y", Const (Sexpr (Number (Int 1)))))])),
  []))))
             (  Def' (Var' (VarFree "a"), Applic' (LambdaSimple' ([], LambdaOpt' ([], "x", Seq' ([Var' (VarParam ("x", 0));LambdaOpt' ([], "y", Set' (Var' (VarParam ("y", 0)), Const' (Sexpr (Number (Int (1))))))]))), [])));;
 
 let b8 = expr'_eq (run_semantics (LambdaSimple (["x"; "y"],
 Seq
  [Applic (Var "x", [Var "y"]);
   LambdaSimple ([],
    LambdaSimple ([],
     LambdaSimple ([],
      Set (Var "x",
       Applic (LambdaSimple (["z"], Set (Var "y", Var "x")), [Var "y"])))))])
))
       (LambdaSimple' (["x";"y"], Seq' ([Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));Set' (Var' (VarParam ("y", 1)), Box' (VarParam ("y", 1)));Seq' ([Applic' (BoxGet' (VarParam ("x", 0)), [BoxGet' (VarParam ("y", 1))]);LambdaSimple' ([], LambdaSimple' ([], LambdaSimple' ([], BoxSet' (VarBound ("x", 2, 0), Applic' (LambdaSimple' (["z"], BoxSet' (VarBound ("y", 3, 1), BoxGet' (VarBound ("x", 3, 0)))), [BoxGet' (VarBound ("y", 2, 1))])))))])])));;
 
 let b9 = expr'_eq (run_semantics (LambdaSimple ([],
 Seq
  [Applic (LambdaSimple ([], Var "x"), []);
   Applic
    (LambdaSimple (["x"],
      Seq
       [Set (Var "x", Const (Sexpr (Number (Int 1))));
        LambdaSimple ([], Var "x")]),
    [Const (Sexpr (Number (Int 2)))]);
   Applic (LambdaOpt ([], "x", Var "x"), [Const (Sexpr (Number (Int 3)))])])
))
           (LambdaSimple' ([], Seq' ([Applic' (LambdaSimple' ([], Var' (VarFree "x")), []);Applic' (LambdaSimple' (["x"], Seq' ([Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));Seq' ([BoxSet' (VarParam ("x", 0), Const' (Sexpr (Number (Int (1)))));LambdaSimple' ([], BoxGet' (VarBound ("x", 0, 0)))])])), [Const' (Sexpr (Number (Int (2))))]);ApplicTP' (LambdaOpt' ([], "x", Var' (VarParam ("x", 0))), [Const' (Sexpr (Number (Int (3))))])])));;
 
 let b10 = expr'_eq (run_semantics (LambdaSimple (["x"; "y"; "z"],
 Seq
  [LambdaSimple (["y"],
    Seq
     [Set (Var "x", Const (Sexpr (Number (Int 5))));
      Applic (Var "+", [Var "x"; Var "y"])]);
   Applic (Var "+", [Var "x"; Var "y"; Var "z"])])
))
             (  LambdaSimple' (["x";"y";"z"], Seq' ([Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));Seq' ([LambdaSimple' (["y"], Seq' ([BoxSet' (VarBound ("x", 0, 0), Const' (Sexpr (Number (Int (5)))));ApplicTP' (Var' (VarFree "+"), [BoxGet' (VarBound ("x", 0, 0));Var' (VarParam ("y", 0))])]));ApplicTP' (Var' (VarFree "+"), [BoxGet' (VarParam ("x", 0));Var' (VarParam ("y", 1));Var' (VarParam ("z", 2))])])])));;
 
 (* Change due to "box with Seq" Q in Forum *)
 let b11 = expr'_eq (run_semantics (LambdaSimple (["x"], Set (Var "x", Applic (LambdaSimple ([], Var "x"), [])))
 ))
             (LambdaSimple' (["x"], Seq' ([Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));BoxSet' (VarParam ("x", 0), Applic' (LambdaSimple' ([], BoxGet' (VarBound ("x", 0, 0))), []))])));;
 
 (* Change due to "box with Seq" Q in Forum *)
 let b12 = expr'_eq (run_semantics (Applic (Var "y",
 [LambdaSimple (["y"],
   Seq
    [Set (Var "a", LambdaSimple (["b"], Applic (Var "a", [Var "b"])));
     Set (Var "t",
      LambdaSimple (["x"],
       Seq
        [Set (Var "y",
          LambdaSimple (["j"], Applic (Var "x", [Var "j"; Var "x"])));
         Var "h"]));
     Applic (Var "y", [Var "a"])])])
))
             (Applic' (Var' (VarFree "y"), [LambdaSimple' (["y"], Seq' ([Set' (Var' (VarParam ("y", 0)), Box' (VarParam ("y", 0)));Seq' ([Set' (Var' (VarFree "a"), LambdaSimple' (["b"], ApplicTP' (Var' (VarFree "a"), [Var' (VarParam ("b", 0))])));Set' (Var' (VarFree "t"), LambdaSimple' (["x"], Seq' ([BoxSet' (VarBound ("y", 0, 0), LambdaSimple' (["j"], ApplicTP' (Var' (VarBound ("x", 0, 0)), [Var' (VarParam ("j", 0));Var' (VarBound ("x", 0, 0))])));Var' (VarFree "h")])));ApplicTP' (BoxGet' (VarParam ("y", 0)), [Var' (VarFree "a")])])]))]));;
 
 let b13 = expr'_eq (run_semantics (LambdaSimple (["x"],
 Seq
  [LambdaSimple (["x"], Set (Var "x", Var "x"));
   LambdaSimple (["x"], Set (Var "x", Var "x"))])
))
                   (LambdaSimple' (["x"], Seq' ([LambdaSimple' (["x"], Set' (Var' (VarParam ("x", 0)), Var' (VarParam ("x", 0))));LambdaSimple' (["x"], Set' (Var' (VarParam ("x", 0)), Var' (VarParam ("x", 0))))])));;
 
 let b14 = expr'_eq (run_semantics (LambdaSimple (["x"; "y"],
 Seq
  [LambdaSimple ([], Set (Var "x", Var "y"));
   LambdaSimple ([], Set (Var "y", Var "x"))])
))
    (LambdaSimple' (["x";"y"], Seq' ([Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));
    Set' (Var' (VarParam ("y", 1)), Box' (VarParam ("y", 1)));
    Seq' ([LambdaSimple' ([], BoxSet' (VarBound ("x", 0, 0), BoxGet' (VarBound ("y", 0, 1))));
    LambdaSimple' ([], BoxSet' (VarBound ("y", 0, 1), BoxGet' (VarBound ("x", 0, 0))))])])));;
 
 (* Change due to "box with Seq" Q in Forum *)                                      
 let b15 = expr'_eq (run_semantics (LambdaOpt ([], "x",
 Seq
  [LambdaSimple (["x"], Set (Var "x", Const (Sexpr (Number (Int 1)))));
   Applic (Var "car", [Var "x"])])
))
 (LambdaOpt' ([], "x", Seq' ([LambdaSimple' (["x"], Set' (Var' (VarParam ("x", 0)), Const' (Sexpr (Number (Int (1))))));
 ApplicTP' (Var' (VarFree "car"), [Var' (VarParam ("x", 0))])])));;
 

let b16 = expr'_eq (run_semantics (If (Var "x", Applic (Var "x", []), Var "x")
))
(If' (Var' (VarFree "x"), Applic' (Var' (VarFree "x"), []), Var' (VarFree "x")));;


let b17 = expr'_eq (run_semantics (LambdaSimple ([],
If (Var "x", Applic (Var "x", []), Applic (Var "not", [Var "x"])))))
 (LambdaSimple' ([], If' (Var' (VarFree "x"), ApplicTP' (Var' (VarFree "x"), []), ApplicTP' (Var' (VarFree "not"), [Var' (VarFree "x")]))));;

let b18 = expr'_eq (run_semantics (LambdaSimple (["a"; "b"; "c"; "d"; "e"],
Applic (Var "a",
 [Applic (Var "b", [Var "c"]); Applic (Var "c", [Var "b"; Var "d"]);
  Applic (Var "a",
   [Applic (Var "b", [Applic (Var "c", [Applic (Var "d", [Var "e"])])])])]))
))
(LambdaSimple' (["a";"b";"c";"d";"e"], ApplicTP' (Var' (VarParam ("a", 0)), [Applic' (Var' (VarParam ("b", 1)), [Var' (VarParam ("c", 2))]);Applic' (Var' (VarParam ("c", 2)), [Var' (VarParam ("b", 1));Var' (VarParam ("d", 3))]);Applic' (Var' (VarParam ("a", 0)), [Applic' (Var' (VarParam ("b", 1)), [Applic' (Var' (VarParam ("c", 2)), [Applic' (Var' (VarParam ("d", 3)), [Var' (VarParam ("e", 4))])])])])])));;

let b19 = expr'_eq (run_semantics (LambdaSimple (["x"],
Seq [Applic (Var "x", []); Set (Var "x", Applic (Var "x", []))])
))
   (LambdaSimple' (["x"], Seq' ([Applic' (Var' (VarParam ("x", 0)), []);Set' (Var' (VarParam ("x", 0)), Applic' (Var' (VarParam ("x", 0)), []))])));;
   
let b20 = expr'_eq (run_semantics (LambdaSimple (["x"],
Applic
 (LambdaSimple (["y"],
   Seq [Set (Var "x", Applic (Var "y", [])); Const (Sexpr (Number (Int 2)))]),
 []))
))
   (LambdaSimple' (["x"], ApplicTP' (LambdaSimple' (["y"], Seq' ([Set' (Var' (VarBound ("x", 0, 0)), Applic' (Var' (VarParam ("y", 0)), []));Const' (Sexpr (Number (Int (2))))])), [])));;
   
let b21 = expr'_eq (run_semantics (Const(Void)
))
   (Const' (Void));;

let b22= expr'_eq (run_semantics (LambdaSimple (["x"],
Seq
 [Var "x";
  LambdaSimple (["x"],
   Seq
    [Set (Var "x", Const (Sexpr (Number (Int 1))));
     LambdaSimple ([], Var "x")]);
  LambdaSimple ([], Set (Var "x", Var "x"))])
))
(LambdaSimple' (["x"], Seq' ([Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));Seq' ([BoxGet' (VarParam ("x", 0));LambdaSimple' (["x"], Seq' ([Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));Seq' ([BoxSet' (VarParam ("x", 0), Const' (Sexpr (Number (Int (1)))));LambdaSimple' ([], BoxGet' (VarBound ("x", 0, 0)))])]));LambdaSimple' ([], BoxSet' (VarBound ("x", 0, 0), BoxGet' (VarBound ("x", 0, 0))))])])));;
   
let b23 = expr'_eq (run_semantics (LambdaSimple (["x"],
Seq
 [Var "x";
  LambdaSimple (["x"],
   Seq
    [Set (Var "y", Var "x");
     LambdaSimple ([], Var "x")]);
  LambdaSimple ([], Set (Var "x", Var "x"))])
))
   (LambdaSimple' (["x"], Seq' ([Var' (VarParam ("x", 0));LambdaSimple' (["x"], Seq' ([Set' (Var' (VarFree "y"), Var' (VarParam ("x", 0)));LambdaSimple' ([], Var' (VarBound ("x", 0, 0)))]));LambdaSimple' ([], Set' (Var' (VarBound ("x", 0, 0)), Var' (VarBound ("x", 0, 0))))])));;


 let boxSet_test = [(1, b1); (2, b2); (3, b3); (4, b4); (5, b5); (6, b6); (7, b7); (8, b8); (9, b9); (10, b10); (11, b11); (12, b12);
                    (13, b13); (14,b14);(15,b15);(16,b16);(17,b17);(18,b18);(19,b19);(20,b20);(21,b21);(22,b22);(23,b23)];;
 (testSum purple "Box set" boxSet_test);;
 (testFailed boxSet_test);;
 
 (* All tests *)
 let all_test = annotate_test @ tailcalls_test @ boxSet_test;;
 (testSum yel "All" all_test);;
 allPassed cyan all_test;;
 
 print grn "END TESTS";;
 