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

let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_syntax_error -> (nt2 s);;

let nt_none _ = raise X_syntax_error;;
  
let disj_list nts = List.fold_right disj nts nt_none;;

let rec tag_parse sexpr = 
let parsers = (disj_list [constParsers; ifParsers; varParser; orParser; applicationParser; explicitSeqParser; definitionParser; setBangParser]) in parsers sexpr 

and constParsers sexpr = match sexpr with 
	| Pair(s, Nil) -> (tag_parse s) (*This is how we get rid of Nil - this treats the last item on proper lists*)
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

and varParser sexpr = match sexpr with
	| Symbol(e)->if (is_not_reserved_word e) then Var(e) else raise X_syntax_error
	| _ -> raise X_syntax_error

(* |Pair(Symbol("lambda"), Pair (arglist, exprs)) -> *)	
and orParser sexpr = match sexpr with
	| Pair (Symbol("or"), Pair (car, cdr)) -> Or(orHelper sexpr) 
	| Pair (Symbol("or"), oneArg) -> Or([tag_parse oneArg]) (*treats improper list of arguments with one arg as the Or input *)
	| _ -> raise X_syntax_error

and orHelper sexpr = match sexpr with 
	| Pair(Symbol("or"),Nil) -> [Const(Sexpr(Bool(false)))]
	| Pair(Symbol("or"),Pair (car, Nil)) -> [tag_parse car]
	| Pair(Symbol("or"), Pair (car,cdr)) -> [tag_parse car] @ (orHelper (Pair(Symbol("or"), cdr)))
	| _ -> raise X_syntax_error

and applicationParser sexpr = match sexpr with
	| Pair(proc, Pair(car, cdr)) -> Applic((tag_parse proc), (applicationHelper Pair(car, cdr)))
	| Pair(proc, oneArg) -> Applic((tag_parse proc), [tag_parse oneArg])	(*oneArg - a non-pair sexpr.
																			I think we need this because a lambda with one parameter
																			can be represented as Pair(proc, Pair(arg, Nil))
																			as well as Pair(proc, arg) *)
	| _ -> raise X_syntax_error

and applicationHelper sexpr = match sexpr with
	| sexp -> [tag_parse sexp]
	| Pair(car, Nil) -> [tag_parse car]
	| Pair(car, cdr) -> [tag_parse car @ (applicationHelper cdr)]
	| _ -> raise X_syntax_error

and explicitSeqParser sexpr = match sexpr with
	| Pair(Symbol("begin"), Pair(car, cdr)) -> Seq(explicitSeqHelper sexpr)
	| Pair(Symbol("begin"), oneArg) -> Seq([tag_parse oneArg])
	| _ -> raise X_syntax_error

and explicitSeqHelper sexpr = match sexpr with 
	| Pair(Symbol("begin"), Nil) -> [Const(Void)]
	| Pair(Symbol("begin"), Pair(car, Nil)) -> [tag_parse s]
	| Pair(Symbol("begin"), Pair(car, cdr)) -> [tag_parse car] @ (explicitSeqHelper (Pair(Symbol("begin"), cdr)))
	| _ -> raise X_syntax_error

and definitionParser sexpr = match sexpr with
	| Pair(Symbol("define"), Pair(Symbol(name), s)) -> Def(tag_parse (Symbol(name)), tag_parse s)
	| _ -> raise X_syntax_error

and setBangParser sexpr = match sexpr with
	| Pair(Symbol("set!"), Pair(Symbol(name), s)) -> Set(tag_parse (Symbol(name)), tag_parse s)
	| _ -> raise X_syntax_error

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

(*or test*)
test_function (Pair(Symbol "or", Pair(Pair(Symbol "quote", Pair(Symbol "a", Nil)), Nil))) (Or([Const (Sexpr (Symbol "a"))]));;
(*'(or #t #f 'a')*)
test_function (Pair(Symbol "or", Pair(Bool true, Pair(Bool false, Pair(Pair(Symbol "quote", Pair(Char 'a', Nil)), Nil))))) 
	((Or [Const (Sexpr (Bool true)); Const (Sexpr (Bool false)); Const (Sexpr (Char 'a'))]));;

end;; (* struct Tag_Parser *)
