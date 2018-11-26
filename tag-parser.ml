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

module type TAG_PARSER = sig
  val tag_parse_expression : sexpr -> expr
  val tag_parse_expressions : sexpr list -> expr list
end;; (* signature TAG_PARSER *)

module Tag_Parser : TAG_PARSER = struct

(* ----------------------- Utilities function ----------------------------------- *)
let disj nt1 nt2 =
  fun s ->
  try (nt1 s)
  with X_syntax_error -> (nt2 s);;

let nt_none _ = raise X_syntax_error;;
  
let disj_list nts = List.fold_right disj nts nt_none;;

let rec map f lst = match lst with
	| [] -> Nil
	| head :: tail -> Pair(f head, map f tail);;

let reserved_word_list =
  ["and"; "begin"; "cond"; "define"; "else";
   "if"; "lambda"; "let"; "let*"; "letrec"; "or";
   "quasiquote"; "quote"; "set!"; "unquote";
   "unquote-splicing"];;  

(* work on the tag parser starts here *)
let pred word =  fun s-> (compare word s !=0);; (*word != s*)

let is_not_reserved_word word = 
	andmap (pred word) reserved_word_list;;


let sexprToString symbolSexpr = 
	match symbolSexpr with
	|Symbol (s) -> s
	|_-> raise X_syntax_error;;

(*checks if the list is proper or improper and return the last element - when the list is improper *)
let rec isProperList_LastElement arglist = 
	match arglist with
	|Pair (exp1, Nil)-> ""
	|Pair (exp1, Pair(exp_1, exp_2)) -> isProperList_LastElement (Pair(exp_1, exp_2))
	|Pair (exp1, expr2) -> sexprToString expr2
	|Nil->""
	| _ -> raise X_syntax_error;;

let rec makeStringList arglist = 
	match arglist with
	|Pair (exp1, Nil) -> (sexprToString exp1) :: []
	|Pair (exp1, Pair(exp2, exp3)) -> [sexprToString exp1] @ (makeStringList (Pair(exp2, exp3)))
	|Pair (exp1, exp2) -> [sexprToString exp1; sexprToString exp2]
	|Nil -> []
	| _-> raise X_syntax_error;;

(*return the n mandatory elements *)
let rec mandatoryArgs arglist = 
	match arglist with
	|Pair (exp1, Nil) -> (sexprToString exp1) :: []
	|Pair (exp1, exp2) -> [sexprToString exp1] @ (mandatoryArgs exp2)
	|_ -> []

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
    | Vector(list)-> Printf.sprintf "vector(%s)" (print_sexprs list)

and 

print_sexprs = fun sexprList -> 
  match sexprList with
    | [] -> ""
    | head :: tail -> (print_sexpr head) ^ "," ^ (print_sexprs tail)

let print_sexprs_as_list = fun sexprList ->
  let sexprsString = print_sexprs sexprList in
    "[ " ^ sexprsString ^ " ]";;


(*let helpers*)
let rec extractVarsFromLet sexpr = match sexpr with
	| Pair(Pair(Symbol(sym), Nil), ribs) -> raise X_syntax_error (*let (x) (body) with no assignment to x is illegal*)
	| Pair(Symbol(sym), Nil) -> raise X_syntax_error (*same reason*)
	| Pair(Pair(Symbol(sym), value), Nil) -> Pair(Symbol(sym), Nil)
	| Pair(Symbol(sym), value) -> Pair(Symbol(sym), Nil) (*improper list case of the above case*)
	| Pair(Pair(Symbol(sym), value), ribs) -> Pair(Symbol(sym), extractVarsFromLet ribs)
	| _ -> raise X_syntax_error

(*GOAL - RETURN THIS AS PROPER LIST*)
(*Input: Pair(Pair(Symbol "s", Pair(Number (Int 4), Nil)), Pair(Pair(Symbol "y", Pair(String "s", Nil)), Nil)) *)
(*Expected output: Pair(Number(Int(4)), Pair(String(s), Nil)))*)
let rec extractSexprsFromLet sexpr = match sexpr with
	| Pair(Pair(Symbol(sym), Nil), ribs) -> raise X_syntax_error (*let (x) (body) with no assignment to x is illegal*)
	| Pair(Symbol(sym), Nil) -> raise X_syntax_error (*same reason*)
	| Pair(Pair(Symbol(sym), Pair(sexp, Nil)), Nil) -> Pair(sexp, Nil)
	| Pair(Symbol(sym), Pair(sexp, Nil)) -> sexp (*improper list case of the above case*)
	| Pair(Pair(Symbol(sym), Pair(sexp, Nil)), ribs) -> Pair(sexp, extractSexprsFromLet ribs)
	| _ -> raise X_syntax_error


(*Letrec helpers*)
let rec makeLetRecInitiations sexpr = match sexpr with
	| Pair(Pair(Symbol(sym), Nil), ribs) -> raise X_syntax_error (*letrec (x) (body) with no assignment to x is illegal*)
	| Pair(Symbol(sym), Nil) -> raise X_syntax_error (*same reason*)
	| Pair(Pair(Symbol(sym), value), Nil) -> Pair(Pair(Symbol(sym), Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)),Nil)
	| Pair(Symbol(sym), value) -> Pair(Pair(Symbol(sym), Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)) ,Nil)(*improper list case of the above case*)
	| Pair(Pair(Symbol(sym), value), ribs) -> Pair(Pair(Symbol(sym), Pair(Pair(Symbol("quote"), Pair(Symbol("whatever"), Nil)), Nil)), makeLetRecInitiations ribs)
	| _ -> raise X_syntax_error



let rec makeLetRecBody ribsPair body = match ribsPair with
	| Pair(Pair(Symbol(sym), Nil), ribs) -> raise X_syntax_error (*let (x) (body) with no assignment to x is illegal*)
	| Pair(Symbol(sym), Nil) -> raise X_syntax_error (*same reason*) 
	| Pair(Pair(Symbol(sym), Pair(sexp, Nil)), Nil) -> Pair(Pair(Symbol("set!"), Pair(Symbol(sym), Pair(sexp, Nil))), body)
	| Pair(Symbol(sym), Pair(sexp, Nil))-> Pair(Pair(Symbol("set!"), Pair(Symbol(sym), Pair(sexp, Nil))), body) (*improper list case of the above case*)
	| Pair(Pair(Symbol(sym), Pair(sexp, Nil)), ribs) -> Pair(Pair(Symbol("set!"), Pair(Symbol(sym), Pair(sexp, Nil))), (makeLetRecBody ribs body))
	| _ -> raise X_syntax_error

(*Expanders*)
let rec quasiQuote_expander sexpr = 
	match sexpr with 
	| Pair(Symbol "unquote", Pair(s, Nil)) -> s
	| Pair (Symbol "unquote-splicing", Pair(s,Nil)) -> raise X_syntax_error
	| Nil-> Pair(Symbol "quote", Pair(Nil, Nil)) (*empty list? *)
	| Symbol (s) -> Pair(Symbol "quote", Pair(Symbol(s), Nil))
	| Vector (s_list) -> Pair(Symbol "vector" ,(map quasiQuote_expander s_list))
	| Pair(Pair (Symbol "unquote-splicing", Pair(a_1,Nil)), b) -> 
		Pair(Symbol "append", Pair(a_1, Pair(quasiQuote_expander b, Nil)))
	| Pair(a, Pair (Symbol "unquote-splicing", Pair(b_1,Nil))) -> 
		Pair(Symbol "cons", Pair(quasiQuote_expander a, Pair(b_1,Nil)))
	| Pair (a,b) -> Pair(Symbol "cons", Pair(quasiQuote_expander a, Pair(quasiQuote_expander b, Nil)))
	| _ -> sexpr;;
 

let expand_letStar sexpr = match sexpr with
 	| Pair(Symbol("let*"), Pair(ribs, Nil)) -> raise X_syntax_error (* let* without body is invalid*)
	| Pair(Symbol("let*"), Pair(Nil, body)) -> Pair(Symbol("let"), Pair(Nil, body))
	| Pair(Symbol("let*"), Pair(Pair(rib, Nil), body)) -> Pair(Symbol("let"), Pair(Pair(rib, Nil), body)) (*MAYBE should be Pair(body, NIL) ??? *)
	| Pair(Symbol("let*"), Pair(Pair(rib, ribs), body)) -> Pair(Symbol("let"), Pair(Pair(rib, Nil), Pair(Pair(Symbol("let*"), Pair(ribs, body)), Nil)))
	| _ -> raise X_syntax_error;;

(*let rec condExpander sexpr = 
	match sexpr with
	| Pair(Pair(expr, Pair(Symbol "=>", expr_f)), Nil) -> 
		Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(expr, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(expr_f, Nil))), Nil)), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Nil))), Nil))), Nil))
	| Pair(Pair(expr, Pair(Symbol "=>", expr_f)), rest) -> 
		(* let (value = expr, f = lambda() expr_f) ==> if value ((f) value) else -> rest *)
		Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(expr, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(expr_f, Nil))), Nil)), Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, (condExpander rest))), Nil)), Nil))), Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil)))
	| Pair(Pair(Symbol "else", expr_n),rest) -> 
		(* begin else *)
		Pair(Symbol "begin", expr_n) (*was before: (Symbol "begin", Pair(expr_n,Nil) , also for 2 lines below*)
	| Pair(Pair(expr, expr_n), rest) -> 
		(* if expr then begin expr_n else --> rest *)
		Pair(Symbol "if", Pair(expr, Pair(Pair(Symbol "begin", expr_n), (condExpander rest))))
	| Nil -> Nil
	| _ -> raise X_no_match


let rec condExpander sexpr = 
	match sexpr with
	| Pair(Pair(expr, Pair(Symbol "=>", Pair(expr_f,Nil))), Nil) -> 
		Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(expr, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil,Pair(expr_f, Nil))), Nil)), Nil)),Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Nil))), Nil)))
	| Pair(Pair(expr, Pair(Symbol "=>", Pair(expr_f,Nil))), rest) -> 
		(* let (value = expr, f = lambda() expr_f) ==> if value ((f) value) else -> rest *)
		Pair(Symbol "let", Pair(Pair(Pair(Symbol "value", Pair(expr, Nil)), Pair(Pair(Symbol "f", Pair(Pair(Symbol "lambda", Pair(Nil, Pair(expr_f, Nil))), Nil)), Pair(Pair(Symbol "rest", Pair(Pair(Symbol "lambda", Pair(Nil, Pair((condExpander rest),Nil))), Nil)), Nil))),Pair(Pair(Symbol "if", Pair(Symbol "value", Pair(Pair(Pair(Symbol "f", Nil), Pair(Symbol "value", Nil)), Pair(Pair(Symbol "rest", Nil), Nil)))), Nil)))
	| Pair(Pair(Symbol "else", expr_n),rest) -> 
		(* begin else *)
		Pair(Symbol "begin", expr_n) (*was before: (Symbol "begin", Pair(expr_n,Nil) , also for 2 lines below*)
	| Pair(Pair(expr, expr_n), rest) -> 
		(* if expr then begin expr_n else --> rest *)
		Pair(Symbol "if", Pair(expr, Pair(Pair(Symbol "begin", expr_n), Pair((condExpander rest),Nil))))
	| Nil -> Nil
	| _ -> raise X_not_yet_implemented



let expand_and sexpr = match sexpr with
	| Pair(Symbol("and"), Nil) -> Bool(true)
	| Pair(Symbol("and"), Pair(sexp, Nil)) -> sexp
	| Pair(Symbol("and"), Pair(sexpr1, rest)) -> Pair(Symbol("if"), Pair(sexpr1, Pair(Pair(Symbol("and"), rest), Pair(Bool(false), Nil))))
	| _ -> raise X_syntax_error;;


(*let helpers*)

let rec extractVarsFromLet sexpr = match sexpr with
	| Pair(Pair(Symbol(sym), Nil), ribs) -> raise X_syntax_error (*let (x) (body) with no assignment to x is illegal*)
	| Pair(Symbol(sym), Nil) -> raise X_syntax_error (*same reason*)
	| Pair(Pair(Symbol(sym), value), Nil) -> Pair(Symbol(sym), Nil)
	| Pair(Symbol(sym), value) -> Pair(Symbol(sym), Nil) (*improper list case of the above case*)
	| Pair(Pair(Symbol(sym), value), ribs) -> Pair(Symbol(sym), extractVarsFromLet ribs)
	| _ -> raise X_syntax_error

let expand_MITdefine sexpr = match sexpr with
	| Pair(Symbol("define"), Pair(Pair(Symbol(var), arglist), Pair(Pair(body1, body2), Nil))) -> Pair(Symbol("define"), Pair(Symbol(var), Pair(Pair(Symbol("lambda"), Pair(arglist, Pair(body1, body2))), Nil)))
	| Pair(Symbol("define"), Pair(Pair(Symbol(var), arglist), Pair(onesexp, Nil))) -> Pair(Symbol("define"), Pair(Symbol(var), Pair(Pair(Symbol("lambda"), Pair(arglist, Pair(onesexp, Nil))), Nil)))
	| _ -> raise X_syntax_error


let expand_letRec sexpr = match sexpr with
 	| Pair(Symbol("letrec"), Pair(ribs, Nil)) -> raise X_syntax_error (* letrec without body is invalid*)
	| Pair(Symbol("letrec"), Pair(Nil, body)) -> Pair(Symbol("let"), Pair(Nil, body))
	(*| Pair(Symbol("letrec"), Pair(Pair(rib, Nil), body)) -> *)
	| Pair(Symbol("letrec"), Pair(Pair(rib, ribs), body)) -> Pair(Symbol("let"), Pair(makeLetRecInitiations (Pair(rib, ribs)), (makeLetRecBody (Pair(rib, ribs)) body)))
	| _ -> raise X_syntax_error;;

(* --------------------------------------tag parser -----------------------------------------------------------------  *)	

let rec tag_parse sexpr = 
let parsers = (disj_list [constParsers; setBangParser; letRecParsers; varParser;  letParsers; lambdaParser; ifParsers; condParser ; quasiquoteParser;  orParser;  explicitSeqParser; definitionParser; andParser; letStarParsers; mitDefine;  applicationParser;]) in parsers sexpr 

 

and quasiquoteParser sexpr = match sexpr with
	|Pair(Symbol "quasiquote", Pair(s,Nil)) -> tag_parse (quasiQuote_expander s)
	|_ -> raise X_syntax_error

and condParser sexpr = match sexpr with
	|Pair(Symbol "cond",ribs) -> tag_parse (condExpander ribs)
	|_ -> raise X_syntax_error

and constParsers sexpr = match sexpr with 
	| Bool(e) -> Const(Sexpr(Bool(e)))
	| Number(Int(e_int)) -> Const(Sexpr(Number(Int(e_int))))
	| Number(Float(e_float)) -> Const(Sexpr(Number(Float(e_float))))
	| Char(e_char) -> Const(Sexpr(Char(e_char)))
	| String(e_string) -> Const(Sexpr(String(e_string)))
	| Pair(Symbol("quote"), Pair(s, Nil)) -> Const(Sexpr(s))
	| _ -> raise X_syntax_error


and ifParsers sexpr = match sexpr with
	| Pair(Symbol("if"), Pair(e_cond, Pair(e_then, Pair(Nil, Nil)))) -> If((tag_parse e_cond), (tag_parse e_then), Const(Void))
	| Pair(Symbol("if"), Pair(e_cond, Pair(e_then, Nil))) -> If((tag_parse e_cond), (tag_parse e_then), Const(Void))
	| Pair(Symbol("if"), Pair(e_cond, Pair(e_then, Pair(e_else, Nil)))) -> If((tag_parse e_cond), (tag_parse e_then), (tag_parse e_else))
	(*This is in case we should support case when the else is improper CHECK THIS*)
	(*| Pair(Symbol("if"), Pair(e_cond, Pair(e_then, e_else))) -> If((tag_parse e_cond), (tag_parse e_then), (tag_parse e_else)) *)
	| _ -> raise X_syntax_error


and lambdaParser sexpr = match sexpr with
	| Pair (Symbol "lambda", Pair (Symbol(vs), body)) when body <> Nil -> 
		LambdaOpt ([], vs, tag_parse(Pair(Symbol("begin"),body)))
	| Pair(Symbol "lambda", Pair(arguments, body)) when body <> Nil->
		let arglist = (makeStringList arguments) in
		let lastElement = isProperList_LastElement arguments in 
		let isProper = (compare lastElement "") == 0 in
			if ((isUniq arglist) && isProper && (andmap is_not_reserved_word arglist)) 
				then LambdaSimple(arglist, tag_parse(Pair(Symbol("begin"),body)))
			else if ((isUniq arglist) && (andmap is_not_reserved_word arglist)) 
				then LambdaOpt((mandatoryArgs arguments), lastElement, tag_parse(Pair(Symbol("begin"),body)))
			else raise X_syntax_error
	| _ -> raise X_syntax_error

and varParser sexpr = match sexpr with
	| Symbol(e) -> if (is_not_reserved_word e) then Var(e) else raise X_syntax_error
	| _ -> raise X_syntax_error

and orParser sexpr = match sexpr with
	| Pair(Symbol("or"), Nil) -> Const(Sexpr(Bool(false)))
	| Pair(Symbol("or"), Pair(oneArg, Nil)) -> tag_parse oneArg
	| Pair(Symbol("or"), Pair (car, cdr)) -> Or(orHelper sexpr) 
	(*| Pair(Symbol("or"), oneArg) -> tag_parse oneArg I Think this is ilegal - CHECK*)
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
	(*| oneArg -> [tag_parse oneArg]*)
	| _ -> raise X_syntax_error 
and explicitSeqParser sexpr = match sexpr with
	| Pair(Symbol("begin"), Nil) -> Const(Void)
	| Pair(Symbol("begin"), Pair(car, Nil)) -> tag_parse car
	| Pair(Symbol("begin"), Pair(car, cdr)) -> Seq(explicitSeqHelper sexpr)
	(*TODO: check if we can get begin with one sexprs in improper list: pair(begin, sexp) and add this if needed!*)
	| _ -> raise X_syntax_error

and explicitSeqHelper sexpr = match sexpr with 
	| Pair(Symbol("begin"), Pair(car, Nil)) -> [tag_parse car]
	| Pair(Symbol("begin"), Pair(car, cdr)) -> [tag_parse car] @ (explicitSeqHelper (Pair(Symbol("begin"), cdr)))
	| _ -> raise X_syntax_error

and definitionParser sexpr = match sexpr with
	| Pair(Symbol("define"), Pair(name, Pair(s, Nil))) -> Def(varParser name, tag_parse s)
	(*| Pair(Symbol("define"), Pair(Symbol(name), s)) -> Def(tag_parse (Symbol(name)), tag_parse s) - i think this is ilegal - CHECK*)
	| _ -> raise X_syntax_error

and mitDefine sexpr = match sexpr with (*TODO: check that symbol(var) is Var (send to varParser)*)
	| Pair(Symbol("define"), Pair(Pair(Symbol(var), arglist), Pair(sexps, Nil))) -> tag_parse (expand_MITdefine sexpr)
	| _ -> raise X_syntax_error

and setBangParser sexpr = match sexpr with
	| Pair(Symbol("set!"), Pair(name, Pair(s, Nil))) -> Set(varParser name, tag_parse s)
	| Pair(Symbol("set!"), Pair(name, s)) -> Set(varParser name, tag_parse s)
	| _ -> raise X_syntax_error

(*Pair(Symbol(let),    Pair(Pair(Pair(Symbol(s),    Pair(Pair(Symbol(quote),     Pair(Symbol(whatever),    Nil)),Nil)),Nil),       Pair(Pair(Symbol(set!),    Pair(Symbol(s),    Pair(Number(Int(4)),Nil))),  Pair(Symbol(g),    Pair(Symbol(f),Nil))) ))
*)
and letParsers sexpr = match sexpr with
	| Pair(Symbol("let"), Pair(ribs, Nil)) -> raise X_syntax_error (*let without body is invalid*)
	| Pair(Symbol("let"), Pair(Nil, body)) ->  tag_parse (Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil))										(*I ADDED YTHIS NOW*)
	| Pair(Symbol("let"), Pair(Pair(rib, ribs), body)) -> tag_parse (Pair(Pair(Symbol("lambda"), Pair(extractVarsFromLet (Pair(rib, ribs)), body)), extractSexprsFromLet (Pair(rib, ribs))))																										
	| _ ->  raise X_syntax_error

and letStarParsers sexpr = match sexpr with
	| Pair(Symbol("let*"), rest) -> tag_parse (expand_letStar sexpr)
	| _ -> raise X_syntax_error

and letRecParsers sexpr = match sexpr with
	| Pair(Symbol("letrec"), rest) -> tag_parse (expand_letRec sexpr)
	| _ -> raise X_syntax_error

and andParser sexpr = match sexpr with
	| Pair(Symbol("and"), rest) -> tag_parse (expand_and sexpr)
	| _ -> raise X_syntax_error

let tag_parse_expression sexpr = tag_parse sexpr;;

let tag_parse_expressions sexpr = raise X_not_yet_implemented;;

(*tests*)

(*OUR TESTS*)
let test_function sexpr expected_expr = 
	let check =  expr_eq (tag_parse sexpr) expected_expr in
	if check = false then print_string("problem with sexpr "^(print_sexpr sexpr)^"\n");;

let test_sexprs_equal sexpr expected_sexpr = 
	let check =  sexpr_eq sexpr expected_sexpr in
	if check = false then print_string("problem with sexpr "^(print_sexpr sexpr)^"\n");;



(*let tests*)
let letParsersToSexpr sexpr = 
	match sexpr with
		| Pair(Symbol("let"), Pair(ribs, Nil)) -> raise X_syntax_error (*let without body is invalid*)
		| Pair(Symbol("let"), Pair(Nil, body)) -> Pair(Pair(Symbol("lambda"), Pair(Nil, body)), Nil)										(*I ADDED YTHIS NOW*)
		| Pair(Symbol("let"), Pair(Pair(rib, ribs), body)) -> Pair(Pair(Symbol("lambda"), Pair(extractVarsFromLet (Pair(rib, ribs)), body)), Pair(extractSexprsFromLet (Pair(rib, ribs)), Nil))																									
		| _ -> raise X_syntax_error;;


end;; (* struct Tag_Parser *)

