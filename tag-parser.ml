(* tag-parser.ml
 * A compiler from Scheme to CISC
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "reader.ml";;
open PC

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


let tag_parse_expression sexpr = raise X_not_yet_implemented;;

let tag_parse_expressions sexpr = raise X_not_yet_implemented;;

let rec isProperList arglist = 
	match arglist with
	|Pair (exp1, Nil)-> true
	|Pair (exp1, Pair(exp_1, exp_2)) -> isProperList (Pair(exp_1, exp_2))
	|_-> false ;;

let sexprToString symbolSexpr = 
	match symbolSexpr with
	|Symbol (s) -> s
	|_-> raise X_syntax_error;;

(*let rec makeStringList arglist = 
	match arglist with
	|Pair (exp1, exp2) -> (sexprToString exp1) :: (makeStringList exp2):: []
	|Nil -> []
	|_-> (sexprToString _);;
*)


let rec tag_parse sexpr = 
	match sexpr with
	(*constants*)
	| Bool(e) -> Const(Sexpr(Bool(e)))
	| Number(Int(e_int))->Const(Sexpr(Number(Int(e_int))))
	| Number(Float(e_float))->Const(Sexpr(Number(Float(e_float))))
	| Char(e_char)->Const(Sexpr(Char(e_char)))
	| String(e_string)->Const(Sexpr(String(e_string)))
	| Pair(Symbol("quote"), e_sexpr)-> (tag_parse e_sexpr)
	(*variables*)
	| Symbol(e)->if (is_not_reserved_word e) then Var(e) else raise X_syntax_error
	(*if expr*)
	| Pair(Symbol("if"), Pair(e_cond, Pair(e_then, Pair(e_else, Nil)))) -> If((tag_parse e_cond), (tag_parse e_then), (tag_parse e_else))
	| Pair(Symbol("if"), Pair(e_cond, Pair(e_then, Nil))) -> If((tag_parse e_cond), (tag_parse e_then), Const(Void))
	(*lambdas*)
	(*|Pair(Symbol("lambda"), Pair (arglist, exprs)) -> *)
	(*or *)
	(*TO NAAMA - this is how i treat implicit sequences - i add "begin" and then they're being treated as sequences 
																			We should use this in lambdas etc.- TO NAAMA*)
	| Pair (Symbol("or"), Pair (car, cdr)) -> Or(tag_parse Pair(Symbol("begin"), Pair(car, cdr)))
	(*application*)
	| Pair(proc, argsSeq) -> Applic ((tag_parse proc), (tag_parse Pair(Symbol("begin"), argsSeq)))
	(*Explicit sequence*)
	| Pair(Symbol("begin"), Nil) -> Const(Void)
	| Pair(Symbol("begin"), Pair(s, Nil)) -> tag_parse s
	| Pair(Symbol("begin"), Pair (car, cdr)) -> Seq([(tag_parse car); (tag_parse Pair(Symbol("begin"), cdr))])
	(* TO NAAMA - 
		Im afraid it might create Seq(..., (Seq(..., ...)))), but i think this is
		how we should treat lists of exprs - with Seq (even according to Mayer)  - check this issue
	TO NAAMA *)
	| _ -> raise X_syntax_error;;



(*tests*)
let failure_info = ref "as not as expected"
let got = ref "Not A Real Got"
let expected = ref "Not A Real Expected"

let rec print_sexpr = fun sexprObj ->
  match sexprObj  with
    | Bool(true) -> "Bool(true)"
    | Bool(false) -> "Bool(false)"
    | Nil -> "Nill"
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




let test_function sexpr expected_expr = 
	let check =  expr_eq (tag_parse sexpr) expected_expr in
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
(*or tests*)
(* (or #t . #f) *)
test_function (Pair(Symbol("or"), Pair(Bool(true),Bool(false)))), (Or(Const(Sexpr(Bool(true))) :: Const(Sexpr(Bool(false))) :: []));;
(* (or #t  #f) *)
test_function (Pair(Symbol("or"), Pair(Bool(true), Pair(Bool(false), Nil)))), (Or(Const(Sexpr(Bool(true))) :: Const(Sexpr(Bool(false))) :: []));;
(* (or #t #t #t #f) *)
test_function (Pair(Symbol("or"), Pair(Bool(true), Pair(Bool(true), Pair(Bool(true), Pair(Bool(false), Nil)))))), (Or(Const(Sexpr(Bool(true))) :: Const(Sexpr(Bool(true))) :: Const(Sexpr(Bool(true))):: Const(Sexpr(Bool(false))) :: []));;
(* (or '(#t .#t) #t #f) *)
(*test_function (Pair(Symbol("or"), Pair(Pair(Bool(true), Bool(true)), Pair(Bool(true), Pair(Bool(false), Nil))))), (Or(Seq(Const(Sexpr(Bool(true))) :: Const(Sexpr(Bool(true))) :: []) :: Const(Sexpr(Bool(true))) :: Const(Sexpr(Bool(false))) :: []));;
*)
(* or '(1 2) 3 *)
test_function (Pair(Symbol ("or"), Pair(Pair(Symbol ("quote"), Pair(Pair(Number (Int 1), Pair(Number (Int 2), Nil)), Nil)), Pair(Number (Int 3), Nil)))) (Or(Seq(Const(Sexpr(Number(Int(1)))) :: Const(Sexpr(Number(Int(2)))) :: []) :: Const(Sexpr(Number(Int(3)))) :: []));;

end;; (* struct Tag_Parser *)
