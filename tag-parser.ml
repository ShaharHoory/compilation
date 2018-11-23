(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;
open PC
open Reader

type constant =
  | Sexpr of sexpr
  | Void

type expr =
  | Const of constant
  | Var of string
  | If of expr * expr * expr
  | Seq of expr list
  | Set of expr * expr
  | Def of expr * expr
  | Or of expr list
  | LambdaSimple of string list * expr
  | LambdaOpt of string list * string * expr
  | Applic of expr * (expr list);;

let rec expr_eq e1 e2 =
  match e1, e2 with
  | Const Void, Const Void -> true
  | Const(Sexpr s1), Const(Sexpr s2) -> sexpr_eq s1 s2
  | Var(v1), Var(v2) -> compare v1 v2 = 0 
  | If(t1, th1, el1), If(t2, th2, el2) -> (expr_eq t1 t2) &&
                                            (expr_eq th1 th2) &&
                                              (expr_eq el1 el2)
  | (Seq(l1), Seq(l2)
    | Or(l1), Or(l2)) -> List.for_all2 expr_eq l1 l2
  | (Set(var1, val1), Set(var2, val2)
    | Def(var1, val1), Def(var2, val2)) -> (expr_eq var1 var2) &&
                                             (expr_eq val1 val2)
  | LambdaSimple(vars1, body1), LambdaSimple(vars2, body2) ->
     (List.for_all2 String.equal vars1 vars2) &&
       (expr_eq body1 body2)
  | LambdaOpt(vars1, var1, body1), LambdaOpt(vars2, var2, body2) ->
     (String.equal var1 var2) &&
       (List.for_all2 String.equal vars1 vars2) &&
         (expr_eq body1 body2)
  | Applic(e1, args1), Applic(e2, args2) ->
     (expr_eq e1 e2) &&
       (List.for_all2 expr_eq args1 args2)
  | _ -> false;;

                       
exception X_syntax_error;;
exception X_list_error;;
exception X_list_2_error;;

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)
let pred word =  fun s-> (compare word s !=0);; (*word != s*)

let is_not_reserved_word word = 
	andmap (pred word) reserved_word_list;;


let rec isProperList arglist = 
	match arglist with
	|Pair (exp1, Nil)-> true
	|Pair (exp1, Pair(exp_1, exp_2)) -> isProperList (Pair(exp_1, exp_2))
	|Nil->true
	|_-> false ;;



let sexprToString symbolSexpr = 
	match symbolSexpr with
	|Symbol (s) -> s
	|_-> raise X_syntax_error;;

let rec makeStringList arglist = 
	match arglist with
	|Pair (exp1, Nil) -> (sexprToString exp1) :: []
	|Pair (exp1, exp2) -> [sexprToString exp1] @ (makeStringList exp2)
	| Nil -> []
	|_-> raise X_syntax_error;;

(*return array with uniq elements only*)
let rec uniq x =
  let rec uniq_help l n = 
    match l with
    | [] -> []
    | h :: t -> if n = h then uniq_help t n else h::(uniq_help t n) in
  match x with
  | [] -> []
  | h::t -> h::(uniq_help (uniq t) h);;

let isUniq x = List.length (uniq x) == List.length (x);;

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_syntax_error -> (nt2 s);;

let nt_none _ = raise X_syntax_error;;
  
let disj_list nts = List.fold_right disj nts nt_none;;


(*let helpers*)
let rec extractVarsFromLet sexpr = match sexpr with
	| Pair(Pair(Symbol(sym), Nil), ribs) -> raise X_syntax_error (*let (x) (body) with no assignment to x is illegal*)
	| Pair(Symbol(sym), Nil) -> raise X_syntax_error (*same reason*)
	| Pair(Pair(Symbol(sym), value), Nil) -> Pair(Symbol(sym), Nil)
	| Pair(Symbol(sym), value) -> Pair(Symbol(sym), Nil) (*improper list case of the above case*)
	| Pair(Pair(Symbol(sym), value), ribs) -> Pair(Symbol(sym), extractVarsFromLet ribs)
	| _ -> raise X_syntax_error

let rec extractSexprsFromLet sexpr = match sexpr with
	| Pair(Pair(Symbol(sym), Nil), ribs) -> raise X_syntax_error (*let (x) (body) with no assignment to x is illegal*)
	| Pair(Symbol(sym), Nil) -> raise X_syntax_error (*same reason*)
	| Pair(Pair(Symbol(sym), sexp), Nil) -> sexp
	| Pair(Symbol(sym), sexp) -> sexp (*improper list case of the above case*)
	| Pair(Pair(Symbol(sym), sexp), ribs) -> Pair(sexp, extractSexprsFromLet ribs)
	| _ -> raise X_syntax_error

let rec tag_parse sexpr = 
let parsers = (disj_list [constParsers; ifParsers; lambdaParser; varParser; orParser; applicationParser; explicitSeqParser; definitionParser; setBangParser; letParsers; letStarParsers]) in parsers sexpr 

and constParsers sexpr = match sexpr with 
	(*Pair(s, Nil) -> (tag_parse s) *)(*This is how we get rid of Nil - this treats the last item on proper lists*)
	| Bool(e) -> Const(Sexpr(Bool(e)))
	| Number(Int(e_int)) -> Const(Sexpr(Number(Int(e_int))))
	| Number(Float(e_float)) -> Const(Sexpr(Number(Float(e_float))))
	| Char(e_char) -> Const(Sexpr(Char(e_char)))
	| String(e_string) -> Const(Sexpr(String(e_string)))
	| Pair(Symbol("quote"), Pair(s, Nil)) -> Const(Sexpr(s))
	| _ -> raise X_syntax_error
	(*TODO: unquote ?*)

and ifParsers sexpr = match sexpr with
	| Pair(Symbol("if"), Pair(e_cond, Pair(e_then, Nil))) -> If((tag_parse e_cond), (tag_parse e_then), Const(Void))
	| Pair(Symbol("if"), Pair(e_cond, Pair(e_then, Pair(e_else, Nil)))) -> If((tag_parse e_cond), (tag_parse e_then), (tag_parse e_else))
	| _ -> raise X_syntax_error

and lambdaParser sexpr = match sexpr with
	| Pair(Symbol "lambda", Pair(arguments, body)) -> 
		let arglist = (makeStringList arguments) in
if ((isUniq arglist) && (isProperList arguments) && (andmap is_not_reserved_word arglist)) 
			then LambdaSimple(arglist, tag_parse(Pair(Symbol("begin"),body))) 
		else raise X_syntax_error
	| _ -> raise X_syntax_error

and varParser sexpr = match sexpr with
	| Symbol(e)->if (is_not_reserved_word e) then Var(e) else raise X_syntax_error
	| Pair(Symbol(e), Nil) when (is_not_reserved_word e) -> Var(e)
	| _ -> raise X_syntax_error

and orParser sexpr = match sexpr with
	| Pair(Symbol("or"), Nil) -> Const(Sexpr(Bool(false)))
	| Pair(Symbol("or"), Pair(oneArg, Nil)) -> tag_parse oneArg
	| Pair(Symbol("or"), Pair (car, cdr)) -> Or(orHelper sexpr) 
	| Pair(Symbol("or"), oneArg) -> tag_parse oneArg
	| _ -> raise X_syntax_error

and orHelper sexpr = match sexpr with 
	| Pair(Symbol("or"),Pair (car, Nil)) -> [tag_parse car]
	| Pair(Symbol("or"), Pair (car,cdr)) -> [tag_parse car] @ (orHelper (Pair(Symbol("or"), cdr)))
	| _ -> raise X_syntax_error

and applicationParser sexpr = match sexpr with
	| Pair(proc, args) -> Applic((tag_parse proc), (applicationHelper args))
	(*TO THINK: Can an applic expression on 0 arguments be like am improper list? like: (.(lambda () 1))
	 and if it does - HANDLE THIS! *)
	| _ -> raise X_syntax_error

and applicationHelper sexpr = match sexpr with
	| Pair(car, Nil) -> [tag_parse car]
	| Pair(car, cdr) -> [tag_parse car] @ (applicationHelper cdr)
	| Nil -> []
	| oneArg -> [tag_parse oneArg]
	| _ -> raise X_syntax_error

and explicitSeqParser sexpr = match sexpr with
	| Pair(Symbol("begin"), Nil) -> Const(Void)
	| Pair(Symbol("begin"), Pair(car, Nil)) -> tag_parse car
	| Pair(Symbol("begin"), Pair(car, cdr)) -> Seq(explicitSeqHelper sexpr)
	| _ -> raise X_syntax_error

and explicitSeqHelper sexpr = match sexpr with 
	| Pair(Symbol("begin"), Pair(car, Nil)) -> [tag_parse car]
	| Pair(Symbol("begin"), Pair(car, cdr)) -> [tag_parse car] @ (explicitSeqHelper (Pair(Symbol("begin"), cdr)))
	| _ -> raise X_list_error

and definitionParser sexpr = match sexpr with
	| Pair(Symbol("define"), Pair(Symbol(name), Pair(s, Nil))) -> Def(tag_parse (Symbol(name)), tag_parse s)
	| Pair(Symbol("define"), Pair(Symbol(name), s)) -> Def(tag_parse (Symbol(name)), tag_parse s)
	| _ -> raise X_syntax_error

and setBangParser sexpr = match sexpr with
	| Pair(Symbol("set!"), Pair(Symbol(name), Pair(s, Nil))) -> Set(tag_parse (Symbol(name)), tag_parse s)
	| Pair(Symbol("set!"), Pair(Symbol(name), s)) -> Set(tag_parse (Symbol(name)), tag_parse s)
	| _ -> raise X_syntax_error

and letParsers sexpr = match sexpr with
	| Pair(Symbol("let"), Pair(ribs, Nil)) -> raise X_syntax_error (*let without body is invalid*)
	| Pair(Symbol("let"), Pair(Nil, body)) -> tag_parse (Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil))
	(*| Pair(Symbol("let"), Pair(Nil, Pair(body, Nil))) -> tag_parse (Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil)) I THINK that
																								the above's case covers also this case*)
	| Pair(Symbol("let"), Pair(Pair(rib, ribs), body)) -> tag_parse (Pair(Pair(Symbol("lambda"), Pair(extractVarsFromLet (Pair(rib, ribs)), body)), extractSexprsFromLet (Pair(rib, ribs))))
	(*| Pair(Symbol("let"), Pair(Pair(rib, ribs), Pair(body, Nil))) -> tag_parse (Pair(Pair(Symbol("lambda"), Pair(extractVarsFromLet (Pair(rib, ribs)), body)), extractSexprsFromLet (Pair(rib, ribs))))
																											same comment for here too*)
	| _ -> raise X_syntax_error

and letStarParsers sexpr = match sexpr with
	| Pair(Symbol("let*"), Pair(ribs, Nil)) -> raise X_syntax_error (* let* without body is invalid*)
	| Pair(Symbol("let*"), Pair(Nil, body)) -> tag_parse (Pair(Symbol("let"), Pair(Nil, body)))
	| Pair(Symbol("let*"), Pair(Pair(rib, Nil), body)) -> tag_parse (Pair(Symbol("let"), Pair(Pair(rib, Nil), body))) (*MAYBE should be Pair(body, NIL) ??? *)
	| Pair(Symbol("let*"), Pair(Pair(rib, ribs), body)) -> tag_parse (Pair(Symbol("let"), Pair(Pair(rib, Nil), Pair(Pair(Symbol("let*"), Pair(ribs, body)), Nil))))
	| _ -> raise X_syntax_error


let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = raise X_not_yet_implemented;;

(*tests*)
let failure_info = ref "as not as expected"
let got = ref "Not A Real Got"
let expected = ref "Not A Real Expected"

let rec print_sexpr = fun sexprObj ->
  match sexprObj  with
    | Bool(true) -> "Bool(true)"
    | Bool(false) -> "Bool(false)"
    | Nil -> "Nil"
    | Number(Int(e)) -> Printf.sprintf "Number(Int(%d))" e
    | Number(Float(e)) -> Printf.sprintf "Number(Float(%f))" e
    | Char(e) -> Printf.sprintf "Char(%c)" e
    | String(e) -> Printf.sprintf "String(%s)" e
    | Symbol(e) -> Printf.sprintf "Symbol(%s)" e
    | Pair(e,s) -> Printf.sprintf "Pair(%s,%s)" (print_sexpr e) (print_sexpr s) 
    | Vector(list)-> Printf.sprintf "Vector(%s)" (print_sexprs list)

and 

print_sexprs = fun sexprList -> 
  match sexprList with
    | [] -> ""
    | head :: tail -> (print_sexpr head) ^ "," ^ (print_sexprs tail)

let print_sexprs_as_list = fun sexprList ->
  let sexprsString = print_sexprs sexprList in
    "[ " ^ sexprsString ^ " ]";;

(*OUR TESTS*)
let test_function sexpr expected_expr = 
	let check =  expr_eq (tag_parse sexpr) expected_expr in
	if check = false then print_string("problem with sexpr "^(print_sexpr sexpr)^"\n");;

let test_sexprs_equal sexpr expected_sexpr = 
	let check =  sexpr_eq sexpr expected_sexpr in
	if check = false then print_string("problem with sexpr "^(print_sexpr sexpr)^"\n");;

(*test const*)
test_function (Bool(true)) (Const(Sexpr(Bool(true))));;
test_function (Number(Int(3))) (Const(Sexpr(Number(Int(3)))));;
test_function (Number(Float(-3.0))) (Const(Sexpr(Number(Float(-3.0)))));;
test_function (Char('a')) (Const(Sexpr(Char('a'))));;
test_function (String("true")) (Const(Sexpr(String("true"))));;
test_function (Pair(Symbol("quote"), Pair(Bool(true), Nil))) (Const(Sexpr(Bool(true))));;
(*test variable*)
test_function (Symbol("hello")) (Var("hello"));;
(*tag_parse (Symbol("cond"));;*) (*expect for syntax error*)
test_function (Pair(Symbol("if"), Pair(Bool(true), Pair(String("a"), Pair(String("b"), Nil))))) 
				(If (Const(Sexpr(Bool(true))), Const(Sexpr(String("a"))), Const(Sexpr(String("b")))));;
test_function (Pair(Symbol("if"), Pair(Bool(true), Pair(String("a"), Nil)))) 
				(If (Const(Sexpr(Bool(true))), Const(Sexpr(String("a"))), Const(Void)));;

(*or test*)
test_function (Pair(Symbol "or", Pair(Pair(Symbol "quote", Pair(Symbol "a", Nil)), Nil))) (Const (Sexpr (Symbol "a")));;
(*'(or #t #f 'a')*)
test_function (Pair(Symbol "or", Pair(Bool true, Pair(Bool false, Pair(Pair(Symbol "quote", Pair(Char 'a', Nil)), Nil))))) 
	((Or [Const (Sexpr (Bool true)); Const (Sexpr (Bool false)); Const (Sexpr (Char 'a'))]));;
(*lambda simple tetsts*)
(* (lambda (x) 4) *)
test_function (Pair(Symbol "lambda", Pair(Pair(Symbol "x", Nil), Pair(Number(Int 4), Nil)))) (LambdaSimple(["x"], Const(Sexpr(Number(Int(4))))));;
test_function (Pair(Symbol "lambda", Pair(Nil, Pair(Number (Int 4), Nil)))) (LambdaSimple([], Const(Sexpr(Number(Int(4))))));;
test_function (Pair(Symbol "lambda", Pair(Nil, Pair(Symbol "e", Pair(Symbol "f", Nil))))) (LambdaSimple( [], Seq [Var "e"; Var "f"])) ;;
test_function (Pair(Symbol "lambda", Pair(Pair(Symbol "a", Pair(Symbol "b", Pair(Symbol "c", Nil))), Pair(Pair(Symbol "begin", Pair(Symbol "a", Pair(Symbol "b", Nil))), Nil))))
	(LambdaSimple (["a"; "b"; "c"], Seq [Var "a"; Var "b"]));;
test_function (Pair(Symbol("lambda"), Pair(Nil, Pair(Number (Int 1), Nil)))) (LambdaSimple([], Const(Sexpr(Number(Int(1))))));;


(*tests for let helpers*)
(*extractVarsFromLet*)
test_sexprs_equal (extractVarsFromLet (Pair(Symbol("x"), Pair(Number(Int 1), Nil)))) (Pair(Symbol("x"), Nil));;
test_sexprs_equal (extractVarsFromLet (Pair((Pair(Symbol("x"), Number(Int 1)), Pair(Symbol("y"), Pair(Number(Int(2)), Nil)))))) (Pair(Symbol("x"), Pair(Symbol("y"), Nil)));;
(*improper case*)
test_sexprs_equal (extractVarsFromLet (Pair((Pair(Symbol("x"), Number(Int 1)), Pair(Symbol("y"), Number(Int(2))))))) (Pair(Symbol("x"), Pair(Symbol("y"), Nil)));;

(*extractSexprsFromLet*)
test_sexprs_equal (extractSexprsFromLet (Pair(Symbol("x"), Pair(Number(Int 1), Nil)))) (Pair(Number(Int(1)), Nil));;
test_sexprs_equal (extractSexprsFromLet (Pair((Pair(Symbol("x"), Number(Int 1)), Pair(Symbol("y"), Pair(Number(Int(2)), Nil)))))) (Pair(Number(Int(1)), Pair(Number(Int(2)), Nil)));;
(*improper case*)
test_sexprs_equal (extractSexprsFromLet (Pair((Pair(Symbol("x"), Number(Int 1)), Pair(Symbol("y"), Number(Int(2))))))) (Pair(Number(Int(1)), Number(Int(2)))
);;

(*applic tests*)
test_function (Pair(Symbol("+"), Pair(Number(Int 1), Pair(Number(Int 2), Nil)))) (Applic(Var("+"), [Const(Sexpr(Number(Int(1)))); Const(Sexpr(Number(Int(2))))]));;
test_function (Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(Number (Int 1), Nil))), Nil)) (Applic(LambdaSimple([], Const(Sexpr(Number(Int(1))))), []));;


(*let tests*)
let letParsersToSexpr sexpr = 
	match sexpr with
		| Pair(Symbol("let"), Pair(ribs, Nil)) -> raise X_syntax_error (*let without body is invalid*)
		| Pair(Symbol("let"), Pair(Nil, body)) -> Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil)
		(*| Pair(Symbol("let"), Pair(Nil, Pair(body, Nil))) -> tag_parse (Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil)) I THINK that
																									the above's case covers also this case*)
		| Pair(Symbol("let"), Pair(Pair(rib, ribs), body)) -> Pair(Pair(Symbol("lambda"), Pair(extractVarsFromLet (Pair(rib, ribs)), body)), extractSexprsFromLet (Pair(rib, ribs)))
		(*| Pair(Symbol("let"), Pair(oneRib, body)) -> TODO*)
		(*| Pair(Symbol("let"), Pair(Pair(rib, ribs), Pair(body, Nil))) -> tag_parse (Pair(Pair(Symbol("lambda"), Pair(extractVarsFromLet (Pair(rib, ribs)), body)), extractSexprsFromLet (Pair(rib, ribs))))
																											same comment for here too*)
		| _ -> raise X_syntax_error;;
(*sexpression equality in let*)
test_sexprs_equal (letParsersToSexpr (Pair(Symbol("let"), Pair(Nil, Pair(Number (Int 1), Nil))))) (Pair(Pair(Symbol("lambda"), Pair(Nil, Pair(Number (Int 1), Nil))), Nil));;
test_sexprs_equal (letParsersToSexpr (Pair(Symbol("let"), Pair(Pair(Symbol("x"), Pair(Number(Int 1), Nil)), Symbol("x"))))) (Pair(Pair(Symbol("lambda"), Pair(Pair(Symbol("x"), Nil), Symbol("x"))), Pair(Number(Int 1), Nil)));;

(*real let tests*)
test_function (Pair(Symbol("let"), Pair(Nil, Pair(Number (Int 1), Nil)))) (Applic(LambdaSimple([], Const(Sexpr(Number(Int(1))))), []));;

(*let star tests*)
let letStarParsersToSexpr sexpr = match sexpr with
	| Pair(Symbol("let*"), Pair(ribs, Nil)) -> raise X_syntax_error (*let* without body is invalid*)
	| Pair(Symbol("let*"), Pair(Nil, body)) -> Pair(Symbol("let"), Pair(Nil, body))
	| Pair(Symbol("let*"), Pair(Pair(rib, Nil), body)) -> Pair(Symbol("let"), Pair(Pair(rib, Nil), body))
	| Pair(Symbol("let*"), Pair(Pair(rib, ribs), body)) -> Pair(Symbol("let"), Pair(Pair(rib, Nil), Pair(Symbol("let*"), Pair(ribs, body))))
	| _ -> raise X_syntax_error;;


(*TESTS FROM FACEBOOK*)

let _tag_string str =
  let sexp = (read_sexpr str) in
  tag_parse_expression sexp;;

exception X_test_mismatch;;

(*Test will fail if no X_syntax_error is raised with input str*)
let _assertX num str =
  try let sexpr = (tag_parse_expression (read_sexpr str)) in
      match sexpr with
      |_ ->
        (failwith
	(Printf.sprintf
	   "Failed %.1f: Expected syntax error with string '%s'"num str))
   with
  |X_no_match ->
     (failwith
	(Printf.sprintf
	   "Failed %.1f with X_no_match: Reader couldn't parse the string '%s'"num str))
  |X_syntax_error -> num
     
(*Test will fail if an exception is raised,
or the output of parsing str is different than the expression out*)
let _assert num str out =
  try let sexpr = (read_sexpr str) in
      (if not (expr_eq (tag_parse_expression sexpr) out)
       then raise X_test_mismatch
       else num)
  with
  |X_no_match ->
     (failwith
	(Printf.sprintf
	   "Failed %.2f with X_no_match: Reader couldn't parse the string '%s'"num str))
  |X_test_mismatch ->
    (failwith
       (Printf.sprintf
	  "Failed %.2f with mismatch: The input -- %s -- produced unexpected expression"num str))
  |X_syntax_error ->
     (failwith
	(Printf.sprintf
	   "Failed %.2f with X_syntax_error: Tag parser failed to resolve expression '%s'"num str));;

(*Boolean*)
_assert 1.0 "#t" ( Const (Sexpr (Bool true)));;
_assert 1.1 "#f" ( Const (Sexpr (Bool false)));;

(*Number*)
_assert 2.0 "123" ( Const (Sexpr (Number (Int 123))));;
_assert 2.1 "-123" ( Const (Sexpr (Number (Int (-123)))));;
_assert 2.2 "12.3" ( Const (Sexpr (Number (Float (12.3)))));;
_assert 2.3 "-12.3" ( Const (Sexpr (Number (Float (-12.3)))));;


(*Char*)
_assert 3.0 "#\\A" ( Const (Sexpr (Char 'A')));;
_assert 3.1 "#\\nul" ( Const (Sexpr (Char '\000')));;


(*String*)
_assert 4.0 "\"String\"" (Const (Sexpr (String "String")));;

(*Quote*)
_assert 5.0 "'quoting" (Const (Sexpr (Symbol "quoting")));;

(*Symbol*)
_assert 6.0 "symbol" (Var "symbol");;

(*If*)
_assert 7.0 "(if #t 2 \"abc\")"
  (If (Const (Sexpr (Bool true)), Const (Sexpr (Number (Int 2))),
       Const (Sexpr (String "abc"))));;
  
_assert 7.1 "(if #t 2)"
  (If (Const (Sexpr (Bool true)), Const (Sexpr (Number (Int 2))),
       (Const Void)));;

  (*SimpleLambda*)
_assert 8.0 "(lambda (a b c) d)" (LambdaSimple (["a"; "b"; "c"], Var "d"));;
_assert 8.1 "(lambda (a b c) (begin d))" (LambdaSimple (["a"; "b"; "c"], Var "d"));;
_assert 8.2 "(lambda (a b c) a b)" (LambdaSimple (["a"; "b"; "c"], Seq [Var "a"; Var "b"]));;
_assert 8.3 "(lambda (a b c) (begin a b))" (LambdaSimple (["a"; "b"; "c"], Seq [Var "a"; Var "b"]));;
_assert 8.4 "(lambda (a b c) (begin))" (LambdaSimple (["a"; "b"; "c"], Const Void));;
_assertX 8.5 "(lambda (a b c d d) e f)";;
_assert 8.6 "(lambda () e f)" (LambdaSimple( [], Seq [Var "e"; Var "f"])) ;;

(*Application*)
_assert 11.0 "(+ 1 2 3)"
  (Applic (Var "+", [Const (Sexpr (Number (Int 1)));
		     Const (Sexpr (Number (Int 2)));
		     Const (Sexpr (Number (Int 3)))]));;
_assert 11.1 "((lambda (v1 v2) c1 c2 c3) b1 b2)"
  (Applic
     (LambdaSimple (["v1"; "v2"],
		    Seq [Var "c1"; Var "c2"; Var "c3"]),
      [Var "b1"; Var "b2"]));;


(*Or*)
_assert 12.0 "(or #t #f #\\a)"
  (Or
     [Const (Sexpr (Bool true)); Const (Sexpr (Bool false));
      Const (Sexpr (Char 'a'))]);;

_assert 12.1 "(or 'a)"
      (Const (Sexpr (Symbol "a")));;

_assert 12.2 "(or)"
  (Const (Sexpr (Bool false)));;

 (*Define*)
_assert 13.0 "(define a b)" (Def (Var "a", Var "b"));;
_assert 13.1 "(define a 5)" (Def (Var "a", Const (Sexpr (Number (Int 5)))));;
_assertX 13.2 "(define 5 b)";;
_assertX 13.3 "(define if b)";;

(*Set*)
_assert 14.0 "(set! a 5)" (Set (Var "a", Const (Sexpr (Number (Int 5)))));;
_assertX 14.1 "(set! define 5)";;
_assertX 14.2 "(set! \"string\" 5)";;

(*Let*)
_assert 15.0 "(let ((v1 b1)(v2 b2)) c1 c2 c3)"
  (Applic (LambdaSimple (["v1"; "v2"], Seq [Var "c1"; Var "c2"; Var "c3"]), [Var "b1"; Var "b2"]));;
_assert 15.1 "(let () c1 c2)" (Applic (LambdaSimple ([], Seq [Var "c1"; Var "c2"]), []));;

(*Let* *)
_assert 17.0 "(let* () body)" (Applic (LambdaSimple ([], Var "body"), []));;
_assert 17.1 "(let* ((e1 v1)) body)" (Applic (LambdaSimple (["e1"], Var "body"), [Var "v1"]));;
_assert 17.2 "(let* ((e1 v1)(e2 v2)(e3 v3)) body)"
  (Applic (LambdaSimple (["e1"], Applic (LambdaSimple (["e2"], Applic (LambdaSimple (["e3"], Var "body"),
   [Var "v3"])), [Var "v2"])), [Var "v1"]));;

(*NOT YET IMPLEMENTED*)
(*
(*And*)
_assert 16.0 "(and)" (Const (Sexpr (Bool true)));;
_assert 16.1 "(and e1)" (Var "e1");;
_assert 16.2 "(and e1 e2 e3 e4)"
  (If (Var "e1",
       If (Var "e2", If (Var "e3", Var "e4", Const (Sexpr (Bool false))),
	   Const (Sexpr (Bool false))),
       Const (Sexpr (Bool false))));;

(*MIT define*)
_assert 18.0 "(define (var . arglst) . (body))" (Def (Var "var", LambdaOpt ([],"arglst", Applic (Var "body", []))));;


(*Letrec*)
_assert 19.0 "(letrec ((f1 e1)(f2 e2)(f3 e3)) body)"
  (_tag_string
     "(let ((f1 'whatever)(f2 'whatever)(f3 'whatever))
(set! f1 e1) (set! f2 e2) (set! f3 e3)
(let () body))");;

(*Quasiquote*)
_assert 20.0 "`,x" (_tag_string "x");;
_assertX 20.01 "`,@x";;
_assert 20.02 "`(a b)" (_tag_string "(cons 'a (cons 'b '()))");;
_assert 20.03 "`(,a b)" (_tag_string "(cons a (cons 'b '()))");;
_assert 20.04 "`(a ,b)" (_tag_string "(cons 'a (cons b '()))");;
_assert 20.05 "`(,@a b)" (_tag_string "(append a (cons 'b '()))");;
_assert 20.06 "`(a ,@b)" (_tag_string "(cons 'a (append b '()))");;
_assert 20.07 "`(,a ,@b)" (_tag_string "(cons a (append b '()))");;
_assert 20.08 "`(,@a ,@b)" (_tag_string "(append a (append b '()))");;
_assert 20.09 "`(,@a . ,b)" (_tag_string "(append a b)");;
_assert 20.10 "`(,a . ,@b)" (_tag_string "(cons a b)");;
_assert 20.11 "`(((,@a)))" (_tag_string "(cons (cons (append a '()) '()) '())");;
_assert 20.12 "`#(a ,b c ,d)" (_tag_string "(vector 'a b 'c d)");;

(*Cond*)
_assert 21.0 "(cond (a => b)(c => d))"
  (_tag_string
     "(let ((value a)(f (lambda () b)))
        (if value
          ((f) value)
          (let ((value c)(f (lambda () d)))
            (if value
             ((f) value)))))");;

_assert 21.1 "(cond (p1 e1 e2) (p2 e3 e4) (p3 e4 e5))"
  (_tag_string
     "(if p1
        (begin e1 e2)
        (if p2
          (begin e3 e4)
          (if p3
            (begin e4 e5))))");;

_assert 21.2 "(cond (p1 e1 e2) (p2 e3 e4) (else e5 e6) (BAD BAD BAD))"
  (_tag_string
     "(if p1
        (begin e1 e2)
        (if p2
          (begin e3 e4)
          (begin e5 e6)))");;

*)
end;; (* struct Tag_Parser *)
