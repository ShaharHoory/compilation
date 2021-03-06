#use "reader.ml";;

let rec sexp_to_string s = 
match s with
| Bool(b) -> string_of_bool b
| Nil -> "Nil"
| Number(n) -> (match n with |Int(i) -> string_of_int i |Float(f) -> string_of_float f)
| Char(c) -> String.make 1 c
| String(s) -> s
| Symbol(sym) -> sym
| Pair(s1,s2) -> "(" ^ sexp_to_string(s1) ^","^sexp_to_string(s2)^")"
| Vector(l) -> String.concat "" (List.map sexp_to_string l);;

let rec print_sexp_list sexpl = match sexpl with 
  |[] -> ()
  |sexp::rest -> (Printf.printf "%s\n" (sexp_to_string sexp));
  (print_sexp_list rest);;

exception X_test_failed of string;;
exception X_lists_in_different_size of string;;

let assertTrue exp msg = if exp = false then
  raise (X_test_failed msg);;

let assertFalse exp msg = if exp then
  raise (X_test_failed msg);;

  
let assertEquals sexp1 sexp2 =
  assertTrue (sexpr_eq sexp1 sexp2) (Printf.sprintf "expected to be: %s, but was: %s" (sexp_to_string sexp1) (sexp_to_string sexp2));;

let rec assertEqualsSameSizedLists sexpl1 sexpl2 = 
  match sexpl1, sexpl2 with
  | [], [] -> ()
  | sexp1::rest1, sexp2::rest2 -> (assertEquals sexp1 sexp2); (assertEqualsSameSizedLists rest1 rest2)
  | _, _ -> raise (X_lists_in_different_size "in assertEqualsSameSizedLists");;

let assertEqualsLists sexpl1 sexpl2 =
  if ((List.length sexpl1) != (List.length sexpl2))
    then (Printf.printf "%s" "sexps list in different sizes:\n";
    Printf.printf "%s" "First list:\n";
    print_sexp_list sexpl1;
    Printf.printf "%s" "Second list:\n";
    print_sexp_list sexpl2)
  else assertEqualsSameSizedLists sexpl1 sexpl2;;   




  (* Sanity tests for the testing funcs *)
assertTrue true "sanity check for assert true";;
assertFalse false "sanity check for assert false";;



(* char tests *)
assertEquals (Char('\000')) (Reader.read_sexpr "#\\nul");;
assertEquals (Char('\n')) (Reader.read_sexpr "#\\newline");;
assertEquals (Char('\013')) (Reader.read_sexpr "#\\return");;
assertEquals (Char('\009')) (Reader.read_sexpr "#\\tab");;
assertEquals (Char('\012')) (Reader.read_sexpr "#\\page");;
assertEquals (Char('\032')) (Reader.read_sexpr "#\\space");;
assertEquals (Char('a')) (Reader.read_sexpr "#\\a");;
assertEquals (Char('A')) (Reader.read_sexpr "#\\A");;
assertEquals (Char('?')) (Reader.read_sexpr "#\\?");;
assertEquals (Char('0')) (Reader.read_sexpr "#\\x30");;
assertEquals (Char('\n')) (Reader.read_sexpr "#\\xa");;

(* string tests *)
assertEquals (String("")) (Reader.read_sexpr "\"\"");;
assertEquals (String("moshe")) (Reader.read_sexpr "\"moshe\"");;
assertEquals (String("a string")) (Reader.read_sexpr "\"a string\"");;
assertEquals (String("This is a very long
string that spills across
several lines.")) (Reader.read_sexpr "\"This is a very long
string that spills across
several lines.\"");;
assertEquals (String("0")) (Reader.read_sexpr "\"\\x30;\"");;
assertEquals (String("\n")) (Reader.read_sexpr "\"\\xa;\"");;
assertEquals (String("\n 0 \204")) (Reader.read_sexpr "\"\\xa; \\x30; \\xCc;\"");;

(*
(* read_sexprs tests *)
assertEqualsLists ([Char('0');Char('0');Char('?');Char('?')]) (Reader.read_sexprs "#\\x30#\\x30#\\?#\\?");;
assertEqualsLists ([String("moshe");String("a string")]) (Reader.read_sexprs "\"moshe\"\"a string\"");;
assertEqualsLists ([Pair(String("a"),Nil);Pair(String("a"),Nil)]) (Reader.read_sexprs "#(\"a\")#(\"a\")");;
assertEqualsLists ([Pair(String("a"),Nil);Pair(String("a"),Nil)]) (Reader.read_sexprs "#(\"a\")(\"a\")");;
assertEqualsLists ([String("moshe");Pair(String("a"),Nil)]) (Reader.read_sexprs "\"moshe\"#(\"a\")");;
*)

(* list tests *)
assertEquals (Nil) (Reader.read_sexpr "()");;
assertEquals (Pair(String("a"),Nil)) (Reader.read_sexpr "(\"a\")");;
(*assertEquals (Pair(String("a"),String("a"))) (Reader.read_sexpr "(\"a\" \"a\")");;*) (*FAILS*)
(*assertEquals (Pair(String("a"),Pair(String("b"), String("c")))) (Reader.read_sexpr "(\"a\"\"b\"\"c\")");;*)   (*FAILS*)
(*assertEquals (Pair(Char('0'),Pair(Char('?'), String("a string")))) (Reader.read_sexpr "(#\\x30#\\?\"a string\")");;*)   (*FAILS*)

(* dotted list tests *)

assertEquals (Pair(String("a"),String("a"))) (Reader.read_sexpr "(\"a\".\"a\")");;
assertEquals (Pair(String("a"),Pair(String("b"), String("c")))) (Reader.read_sexpr "(\"a\"\"b\".\"c\")");;
assertEquals (Pair(Char('0'),Pair(Char('?'), String("a string")))) (Reader.read_sexpr "(#\\x30#\\?.\"a string\")");;


(*
(* vector tests *)
assertEquals (Nil) (Reader.read_sexpr "#()");;
assertEquals (Pair(String("a"),Nil)) (Reader.read_sexpr "#(\"a\")");;
assertEquals (Pair(String("a"),String("a"))) (Reader.read_sexpr "#(\"a\"\"a\")");;
assertEquals (Pair(String("a"),Pair(String("b"), String("c")))) (Reader.read_sexpr "#(\"a\"\"b\"\"c\")");;
assertEquals (Pair(Char('0'),Pair(Char('?'), String("a string")))) (Reader.read_sexpr "#(#\\x30#\\?\"a string\")");;
*)


(* Boolean parser tests *)
assertTrue (sexpr_eq (Bool(true)) (Reader.read_sexpr "#t")) "#t Should be true";;
assertTrue (sexpr_eq (Bool(true)) (Reader.read_sexpr "#T")) "#T Should be true";;
assertTrue (sexpr_eq (Bool(false)) (Reader.read_sexpr "#f")) "#f Should be false";;
assertTrue (sexpr_eq (Bool(false)) (Reader.read_sexpr "#F")) "#F Should be false";;

(* Number parser tests *)

(* Simple integer tests *)
assertTrue (sexpr_eq (Number(Int(123))) (Reader.read_sexpr "123")) "Should be 123";;
assertTrue (sexpr_eq (Number(Int(123))) (Reader.read_sexpr "+123")) "Should be 123";;
assertTrue (sexpr_eq (Number(Int(-123))) (Reader.read_sexpr "-123")) "Should be -123";;
assertTrue (sexpr_eq (Number(Int(0))) (Reader.read_sexpr "-0")) "Should be 0";;
assertTrue (sexpr_eq (Number(Int(0))) (Reader.read_sexpr "0")) "Should be 0";;
assertTrue (sexpr_eq (Number(Int(9523921))) (Reader.read_sexpr "009523921")) "Should be 9523921";;
assertTrue (sexpr_eq (Number(Int(-9523921))) (Reader.read_sexpr "-009523921")) "Should be -9523921";;
assertTrue (sexpr_eq (Number(Int(9523921))) (Reader.read_sexpr "+009523921")) "Should be 9523921";;

(* Float tests *)

assertTrue (sexpr_eq (Number(Float(12.0521))) (Reader.read_sexpr "12.0521")) "Should be 12.0521";;
assertTrue (sexpr_eq (Number(Float(12.0521))) (Reader.read_sexpr "+12.0521")) "Should be 12.0521";;
assertTrue (sexpr_eq (Number(Float(-12.0521))) (Reader.read_sexpr "-12.0521")) "Should be -12.0521";;
assertTrue (sexpr_eq (Number(Float(0.0))) (Reader.read_sexpr "+0.0")) "Should be 0.0";;
assertTrue (sexpr_eq (Number(Float(0.0))) (Reader.read_sexpr "-0.0")) "Should be 0.0";;
assertTrue (sexpr_eq (Number(Float(0.7))) (Reader.read_sexpr "0.7")) "Should be 0.7";;
assertTrue (sexpr_eq (Number(Float(0.5))) (Reader.read_sexpr "0.5")) "Should be 0.5";;
assertTrue (sexpr_eq (Number(Float(-0.5))) (Reader.read_sexpr "-0.5")) "Should be -0.5";;
assertTrue (sexpr_eq (Number(Float(12.0521))) (Reader.read_sexpr "0012.0521")) "Should be 12.0521";;
assertTrue (sexpr_eq (Number(Float(12.0521))) (Reader.read_sexpr "+00012.0521")) "Should be 12.0521";;
assertTrue (sexpr_eq (Number(Float(-12.0521))) (Reader.read_sexpr "-00000012.0521")) "Should be -12.0521";;


(* Simple HexInteger tests *)
assertTrue (sexpr_eq (Number(Int(291))) (Reader.read_sexpr "#X123")) "Should be 291";;
assertTrue (sexpr_eq (Number(Int(291))) (Reader.read_sexpr "#X+123")) "Should be 291";;
assertTrue (sexpr_eq (Number(Int(-291))) (Reader.read_sexpr "#x-123")) "Should be -291";;
assertTrue (sexpr_eq (Number(Int(255))) (Reader.read_sexpr "#xFF")) "Should be 255";;
assertTrue (sexpr_eq (Number(Int(255))) (Reader.read_sexpr "#xFf")) "Should be 255";;
assertTrue (sexpr_eq (Number(Int(255))) (Reader.read_sexpr "#xff")) "Should be 255";;
assertTrue (sexpr_eq (Number(Int(255))) (Reader.read_sexpr "#xfF")) "Should be 255";;
assertTrue (sexpr_eq (Number(Int(255))) (Reader.read_sexpr "#x+FF")) "Should be 255";;
assertTrue (sexpr_eq (Number(Int(255))) (Reader.read_sexpr "#X+Ff")) "Should be 255";;
assertTrue (sexpr_eq (Number(Int(255))) (Reader.read_sexpr "#x+ff")) "Should be 255";;
assertTrue (sexpr_eq (Number(Int(255))) (Reader.read_sexpr "#x+fF")) "Should be 255";;
assertTrue (sexpr_eq (Number(Int(-255))) (Reader.read_sexpr "#x-FF")) "Should be -255";;
assertTrue (sexpr_eq (Number(Int(-255))) (Reader.read_sexpr "#X-Ff")) "Should be -255";;
assertTrue (sexpr_eq (Number(Int(-255))) (Reader.read_sexpr "#x-ff")) "Should be -255";;
assertTrue (sexpr_eq (Number(Int(-255))) (Reader.read_sexpr "#x-fF")) "Should be -255";;
assertTrue (sexpr_eq (Number(Int(240))) (Reader.read_sexpr "#x00000F0")) "Should be 240";;
assertTrue (sexpr_eq (Number(Int(240))) (Reader.read_sexpr "#x0000f0")) "Should be 240";;
assertTrue (sexpr_eq (Number(Int(240))) (Reader.read_sexpr "#x+F0")) "Should be 240";;
assertTrue (sexpr_eq (Number(Int(240))) (Reader.read_sexpr "#X+f0")) "Should be 240";;
assertTrue (sexpr_eq (Number(Int(240))) (Reader.read_sexpr "#x+0F0")) "Should be 240";;
assertTrue (sexpr_eq (Number(Int(240))) (Reader.read_sexpr "#x+0f0")) "Should be 240";;
assertTrue (sexpr_eq (Number(Int(-240))) (Reader.read_sexpr "#x-F0")) "Should be -240";;
assertTrue (sexpr_eq (Number(Int(-240))) (Reader.read_sexpr "#x-f0")) "Should be -240";;

(* Simple HexFloat tests *)

assertTrue (sexpr_eq (Number(Float(0.99609375))) (Reader.read_sexpr "#x0.ff")) "Should be 0.99609375";;
assertTrue (sexpr_eq (Number(Float(-0.99609375))) (Reader.read_sexpr "#x-0.ff")) "Should be -0.99609375";;
assertTrue (sexpr_eq (Number(Float(0.99609375))) (Reader.read_sexpr "#X0.Ff")) "Should be 0.99609375";;
assertTrue (sexpr_eq (Number(Float(-0.99609375))) (Reader.read_sexpr "#x-0.fF")) "Should be -0.99609375";;
assertTrue (sexpr_eq (Number(Float(0.9375))) (Reader.read_sexpr "#x0.f")) "Should be 0.9375";;
assertTrue (sexpr_eq (Number(Float(0.9375))) (Reader.read_sexpr "#x0.f")) "Should be 0.9375";;
assertTrue (sexpr_eq (Number(Float(0.9375))) (Reader.read_sexpr "#X0.F")) "Should be 0.9375";;
assertTrue (sexpr_eq (Number(Float(0.9375))) (Reader.read_sexpr "#x0.F")) "Should be 0.9375";;
assertTrue (sexpr_eq (Number(Float(-0.9375))) (Reader.read_sexpr "#x-0.f")) "Should be -0.9375";;
assertTrue (sexpr_eq (Number(Float(-0.9375))) (Reader.read_sexpr "#x-0.f")) "Should be -0.9375";;
assertTrue (sexpr_eq (Number(Float(-0.9375))) (Reader.read_sexpr "#x-0.F")) "Should be -0.9375";;
assertTrue (sexpr_eq (Number(Float(-0.9375))) (Reader.read_sexpr "#X-0.F")) "Should be -0.9375";;


(* Simple test for symbol *)
assertTrue (sexpr_eq (Symbol("a$")) (Reader.read_sexpr "a$")) "Should be a$";;
assertTrue (sexpr_eq (Symbol("$*symbol!")) (Reader.read_sexpr "$*symbol!")) "Should be $*symbol!";;
assertTrue (sexpr_eq (Symbol("$*symbol!")) (Reader.read_sexpr "$*SymBoL!")) "Should be $*symbol!";;
assertTrue (sexpr_eq (Symbol("symbol")) (Reader.read_sexpr "symbol")) "Should be symbol";;
assertTrue (sexpr_eq (Symbol("symbol")) (Reader.read_sexpr "SymBoL")) "Should be symbol";;
assertTrue (sexpr_eq (Symbol("symbol")) (Reader.read_sexpr "Symbol")) "Should be symbol";;
assertTrue (sexpr_eq (Symbol("symbol")) (Reader.read_sexpr "symboL")) "Should be symbol";;
assertTrue (sexpr_eq (Symbol("symbol")) (Reader.read_sexpr "SymboL")) "Should be symbol";;
assertTrue (sexpr_eq (Symbol("abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz!$^*-_=+<>/?")) (Reader.read_sexpr "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz!$^*-_=+<>/?")) "Should be abcdefghijklmnopqrstuvwxyzabcdefghijklmnopqrstuvwxyz!$^*-_=+<>/?";;


(* Simple test for Pair brackets *) 
(* ---------------------------------------SHAHAR KNOWS THE IMPLEMENTATION ISN'T 100% FINISHED------
assertEquals (Nil) (Reader.read_sexpr "[]");;
assertEquals (Pair(String("a"),Nil)) (Reader.read_sexpr "[\"a\"]");;
assertEquals (Pair(String("a"),String("a"))) (Reader.read_sexpr "[\"a\"\"a\"]");;
assertEquals (Pair(String("a"),Pair(String("b"), String("c")))) (Reader.read_sexpr "[\"a\"[\"b\"\"c\"]]");;
assertEquals (Pair(Char('0'),Pair(Char('?'), String("a string")))) (Reader.read_sexpr "[#\\x30[#\\?\"a string\"]]");;
*)

(* Quotes and friends *)
assertEquals (Pair(Symbol("quote"), Pair(Bool(true), Nil))) (Reader.read_sexpr "'#T");;
assertEquals (Pair(Symbol("quote"), Pair(Bool(true), Nil))) (Reader.read_sexpr "'#t");;
assertEquals (Pair(Symbol("quote"), Pair(Bool(false), Nil))) (Reader.read_sexpr "'#f");;
assertEquals (Pair(Symbol("quasiquote"), Pair(Number(Int(1234)), Nil))) (Reader.read_sexpr "`1234");;
assertEquals (Pair(Symbol("quote"),Pair(Pair(Symbol("quasiquote"), Pair(Number(Int(4660)), Nil)), Nil))) (Reader.read_sexpr "'`#x1234");;
assertEquals (Pair(Symbol("unquote"), Pair(Number(Int(1234)), Nil))) (Reader.read_sexpr ",1234");;
assertEquals (Pair(Symbol("unquote-splicing"), Pair(Number(Int(1234)), Nil))) (Reader.read_sexpr ",@1234");;

(* Handling white spaces *)
assertTrue (sexpr_eq (Bool(true)) (Reader.read_sexpr " #t   ")) "#t Should be true";;
assertTrue (sexpr_eq (Bool(false)) (Reader.read_sexpr "#F     ")) "#F Should be false";;
assertTrue (sexpr_eq (Bool(false)) (Reader.read_sexpr "    #F     ")) "#F Should be false";;
assertTrue (sexpr_eq (Bool(false)) (Reader.read_sexpr "    #f")) "#F Should be false";;
assertTrue (sexpr_eq (Number(Int(-123))) (Reader.read_sexpr "   -123     ")) "Should be -123";;
assertTrue (sexpr_eq (Number(Int(0))) (Reader.read_sexpr "-0  ")) "Should be 0";;
(*                                    -------------------------------ONCE IMPLEMENTED READ_SEXPRS, UNCOMMENT THE TESTS___________________
assertEqualsLists ([Number(Int(1));Number(Int(2));Number(Int(-9))]) (Reader.read_sexprs "   1   2      -9     ");;
assertEqualsLists ([Number(Int(1));Number(Int(2));Number(Int(-9))]) (Reader.read_sexprs "1 2 -9");;
assertEqualsLists ([Bool(true);Number(Int(1));Number(Int(2)); Bool(false);Number(Int(-9))]) (Reader.read_sexprs "#t 1 2 #f -9");;
*)

assertEquals (Pair(Bool(true),  Nil)) (Reader.read_sexpr "(        #T  )");;

(*
(* Handling inline comments*)
assertEqualsLists [Number(Int(1));Number(Int(2));Number(Int(1));Number(Int(1))] (Reader.read_sexprs "1
  2       1
1");;

assertEqualsLists ([Number(Int(1));Number(Int(2));Number(Int(1))]) (Reader.read_sexprs "1
  2   ;    1
  1");;

assertEqualsLists ([Number(Int(1));Number(Int(2));Number(Int(1))]) (Reader.read_sexprs "1
  2   ;    1 ldsfskdlf ;l12i94j i9edjaskdm sknjdf1je§19j0w§!# !@#2140- 9§1; dfwe;dlf
  1");;

assertEqualsLists ([Number(Int(1));Number(Int(2))]) (Reader.read_sexprs "1
  2   ;    1 ldsfskdlf ;l12i94j i9edjaskdm sknjdf1je§19j0w§!# !@#2140- 9§1; dfwe;dlf");;

  (* Handling sexp comment *)
*)

  (* Nil support *)
assertEquals (Nil) (Reader.read_sexpr "()");;
assertEquals (Nil) (Reader.read_sexpr "     (          )      ");; 


(*
(* Sci notation *)                                             --------------check&fix----------
assertEquals (Number(Float(10.0))) (Reader.read_sexpr "1e1");;
assertEquals (Number(Float(10.0))) (Reader.read_sexpr "1E+1");;
assertEquals (Number(Float(3140000000.0))) (Reader.read_sexpr "3.14e+9");;
assertEquals (Number(Float(0.0))) (Reader.read_sexpr "3.14E-512");;
assertEquals (Number(Float(1230.0))) (Reader.read_sexpr "+000000012.3E00000002");;
assertEquals (Number(Float(-0.05))) (Reader.read_sexpr "-5.000000000e-2");;

(* auto completion *)                                 ---------------------------check me-----------------
assertEquals (Nil) (Reader.read_sexpr "[...");;
assertEquals (Pair(Nil,Nil)) (Reader.read_sexpr "[(...");;
assertEquals (Pair(Pair(Nil,Nil),Nil)) (Reader.read_sexpr "[(#(...");;
assertEquals (Pair((Pair(Symbol("a"),Pair(Symbol("b"),Nil))),Nil)) (Reader.read_sexpr "[(a b #(...");;
assertEquals (Pair(Pair(String("a"),Pair(String("b"), String("c"))),String("a"))) (Reader.read_sexpr "#((\"a\"\"b\"\"c\") \"a\"...");;
assertEquals (Pair(Pair(Nil,Nil),Nil)) (Reader.read_sexpr "[[[]...");;
assertEquals (Pair(Symbol("a"),Pair(Symbol("b"),Pair((Symbol("c")),Nil)))) (Reader.read_sexpr "[a[b[c...");;

*)

