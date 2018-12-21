#use "semantic-analyser.ml";;

module type CODE_GEN = sig
  val make_consts_tbl : expr' list -> (constant * ('a * string)) list
  val make_fvars_tbl : expr' list -> (string * 'a) list
  val generate : (constant * ('a * string)) list -> (string * 'a) list -> expr' -> string
end;;

module Code_Gen : CODE_GEN = struct

let constant_eq s1 s2 = match s1, s2 with
	| Sexpr(s1), Sexpr(s2) -> sexpr_eq s1 s2
	| Void, Void -> true
	| _ -> false;;

  let removeDuplicatesConstList lst = 
  	let rec f origList reducedList = match origList with 
  		| [] -> reducedList
  		| car :: cdr -> if (List.exists (fun (sexp) -> constant_eq car sexp) reducedList) then f cdr reducedList  else f cdr (reducedList@[car]) in
  	f lst [];;

  (*makes the initial constatnt list -without duplicates- which is gonna be expanded to the consts table*)
  let make_consts_list exprTag_lst = 
  	let rec findConstsInExpr' exp' = 
  		let buildConstsList accList =
		  	match exp' with
		  		| Const'(Sexpr(sexp)) -> accList @ [Sexpr(sexp)]
		  		| Const'(Void) -> accList (*check this!*)
		  		| Var'(v) -> accList
				| Box'(v)-> accList
				| BoxGet'(v) -> accList
				| BoxSet'(v, setExp') -> accList @ findConstsInExpr' setExp' 
				| If' (test, dit, dif) -> accList @ ((findConstsInExpr' test) @ (findConstsInExpr' dit) @ (findConstsInExpr' dif))
				| Seq'(exprTags) -> accList @ (List.flatten (List.map findConstsInExpr' exprTags))
				| Set'(var, ex') -> accList @ ((findConstsInExpr' var) @ (findConstsInExpr' ex'))
				| Def'(var, ex') -> accList @ ((findConstsInExpr' var) @ (findConstsInExpr' ex'))
				| Or'(exprTags) -> accList @ (List.flatten (List.map findConstsInExpr' exprTags))
				| LambdaSimple'(params, body) -> accList @ (findConstsInExpr' body)
				| LambdaOpt'(params, opt, body) -> accList @ (findConstsInExpr' body)
				| Applic'(proc, argsList) -> accList @ (List.flatten (List.map findConstsInExpr' ([proc] @ argsList)))
				| ApplicTP'(proc, argsList) ->  accList @ (List.flatten (List.map findConstsInExpr' ([proc] @ argsList))) in
	buildConstsList [] in
  let sexpsList = List.flatten (List.map findConstsInExpr' exprTag_lst) in
  let withInitialConstants = [Void;Sexpr(Nil);Sexpr(Bool(false));Sexpr(Bool(true))] @ sexpsList in
	removeDuplicatesConstList withInitialConstants;;

(*the folding function of expandCOnstList*)
let rec expandConstant const accResult = match const with
	| Sexpr(Symbol(str)) -> [Sexpr(String(str));const] @ accResult
	| Sexpr(Pair(car, cdr)) -> expandConstant (Sexpr(car)) (expandConstant (Sexpr(cdr)) ([(Sexpr(car));(Sexpr(cdr));const] @ accResult))
	| Sexpr(Vector(lst)) -> (expandConstList (List.map (fun (a) -> Sexpr(a)) lst)) @ ([const] @ accResult) (*check if this brings the desired output!!!!!!!!!!!!!!!!!!!!!!!!!!1*)
	| _ -> [const] @ accResult

and expandConstList constList = removeDuplicatesConstList (List.fold_right expandConstant constList []);;

let sizeOfSexpr sexpr = match sexpr with
	| Nil -> 1
	| Char(c) -> 2
	| Bool(b) -> 2
	| Number(Int(a)) -> 9
	| Number(Float(a)) -> 9
	| String(str) -> 9 + (String.length str)
	| Symbol(s) -> 9
	| Vector(lst) -> 9 + ((List.length lst) * 8)
	| Pair(car, cdr) -> 1 + 8 + 8;;

let sizeOfConst const = match const with
	| Void -> 1
	| Sexpr(s) -> sizeOfSexpr s;;
(*TODO: complete this using sizeOfSexpr and getOffset(isn't written yet)*)
(* let populateConstList constList =
	let first = ((List.hd constList), 0, 
*)

(*---------print functions - only for tests - delete this----------*)
let rec print_sexpr = fun sexprObj ->
  match sexprObj  with
    | Bool(true) -> "Bool(true)"
    | Bool(false) -> "Bool(false)"
    | Nil -> "Nil"
    | Number(Int(e)) -> Printf.sprintf "Number(Int(%d))" e
    | Number(Float(e)) -> Printf.sprintf "Number(Float(%f))" e
    | Char(e) -> Printf.sprintf "Char(%c)" e
    | String(e) -> Printf.sprintf "String(\"%s\")" e
    | Symbol(e) -> Printf.sprintf "Symbol(\"%s\")" e
    | Pair(e,s) -> Printf.sprintf "Pair(%s,%s)" (print_sexpr e) (print_sexpr s) 
    | Vector(list)-> Printf.sprintf "Vector(%s)" (print_sexprs_as_list list)

and print_const = fun const ->
  match const with
    | Void -> "Void"
    | Sexpr(s) -> print_sexpr s

and print_sexprs = fun sexprList -> 
  match sexprList with
    | [] -> ""
    | head :: tail -> (print_sexpr head) ^ "," ^ (print_sexprs tail)

and print_consts = fun constsList -> 
  match constsList with
    | [] -> ""
    | head :: tail -> (print_const head) ^ "," ^ (print_consts tail)

and print_sexprs_as_list = fun sexprList ->
  let sexprsString = print_sexprs sexprList in
    "[ " ^ sexprsString ^ " ]"

and print_consts_as_list = fun constsList ->
  let constString = print_consts constsList in
    "[ " ^ constString ^ " ]"

and print_expr = fun exprObj ->
  match exprObj  with
    | Const'(Void) -> "Const(Void)"
    | Const'(Sexpr(x)) -> Printf.sprintf "Const(Sexpr(%s))" (print_sexpr x)
    | Var'(VarParam(x, indx)) -> Printf.sprintf "VarParam(\"%s\", %d)" x indx
    | Var'(VarBound(x, indx, level)) -> Printf.sprintf "VarBound(\"%s\" %d %d)" x indx level
    | Var'(VarFree(x)) -> Printf.sprintf "VarFree(\"%s\" )" x
    | If'(test,dit,dif) -> Printf.sprintf "If(%s,%s,%s)" (print_expr test) (print_expr dit) (print_expr dif)
    | Seq'(ls) -> Printf.sprintf "Seq(%s)" (print_exprs_as_list ls)
    | Set'(var,value) -> Printf.sprintf "Set(%s,%s)" (print_expr var) (print_expr value)
    | Def'(var,value) -> Printf.sprintf "Def(%s,%s)" (print_expr var) (print_expr value)
    | Or'(ls) -> Printf.sprintf "Or(%s)" (print_exprs_as_list ls)
    | LambdaSimple'(args,body) -> Printf.sprintf "LambdaSimple(%s,%s)" (print_strings_as_list args) (print_expr body)
    | LambdaOpt'(args,option_arg,body) -> Printf.sprintf "LambdaOpt(%s,%s,%s)" (print_strings_as_list args) option_arg (print_expr body)
    | Applic'(proc,params) -> Printf.sprintf "Applic(%s,%s)" (print_expr proc) (print_exprs_as_list params) 
    | ApplicTP'(proc,params) -> Printf.sprintf "ApplicTP(%s,%s)" (print_expr proc) (print_exprs_as_list params) 
    | Box'(variable) -> Printf.sprintf "Box'(\"%s\" )" (print_var variable)
    | BoxGet'(variable) -> Printf.sprintf "BoxGet'(\"%s\" )" (print_var variable)
    | BoxSet'(variable, expr) -> Printf.sprintf "BoxSet'(\"%s\", %s )" (print_var variable) (print_expr expr)

and print_var = fun x ->
	match x with
	| VarFree(str) -> Printf.sprintf "VarFree(%s)" str
	| VarParam(str, int1) -> Printf.sprintf "VarParam(%s)" str
	| VarBound(str, int1, int2) -> Printf.sprintf "VarBound(%s)" str
and 

print_exprs = fun exprList -> 
  match exprList with
    | [] -> ""
    | head :: [] -> (print_expr head) 
    | head :: tail -> (print_expr head) ^ "; " ^ (print_exprs tail)

and

print_exprs_as_list = fun exprList ->
  let exprsString = print_exprs exprList in
    "[ " ^ exprsString ^ " ]"

and

print_strings = fun stringList -> 
  match stringList with
    | [] -> ""
    | head :: [] -> head 
    | head :: tail -> head ^ "; " ^ (print_strings tail)

and

print_strings_as_list = fun stringList ->
  let stringList = print_strings stringList in
    "[ " ^ stringList ^ " ]";;

(*Mayers main functions*)
let make_consts_tbl asts = raise X_not_yet_implemented (*populateConstList(expandConstList (make_consts_list asts))*);;
let make_fvars_tbl asts = raise X_not_yet_implemented;;
let generate consts fvars e = raise X_not_yet_implemented;;

(*Tests*)
(* - make_const_list test *)

(print_string (print_consts_as_list (make_consts_list [Applic' (LambdaSimple' (["x"], Seq' ([Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0)));If' (Applic' (BoxGet' (VarParam ("x", 0)), [Const' (Sexpr (Number (Int (1))))]), ApplicTP' (BoxGet' (VarParam ("x", 0)), [Const' (Sexpr (Number (Int (2))))]), ApplicTP' (LambdaSimple' (["x"], Set' (Var' (VarParam ("x", 0)), Const' (Sexpr (Number (Int (0)))))), 
                               [Const' (Sexpr (Number (Int (3))))]))])), [LambdaSimple' (["x"], Var' (VarParam ("x", 0))) ; LambdaSimple' ([], Const' (Sexpr (Number (Int (1)))))])])));;
(print_string "\n");;


(print_string (print_consts_as_list (make_consts_list [Const'(Sexpr(Pair(Number (Int 1), Nil))); Const'(Sexpr(Pair(Bool true, Nil))); Const'(Sexpr(Pair(Number (Int 1), Nil)))])));;
(print_string "\n");;

(print_string (print_consts_as_list (make_consts_list [LambdaSimple' ([], Set' (Var' (VarParam ("x", 0)), Box' (VarParam ("x", 0))))])));;
(print_string "\n");;


(print_string (print_consts_as_list (expandConstList (make_consts_list [Applic' (Var' (VarFree "list"),
 [Const' (Sexpr (String "ab"));
  Const' (Sexpr (Pair (Number (Int 1), Pair (Number (Int 2), Nil))));
  Const' (Sexpr (Symbol "c")); Const' (Sexpr (Symbol "ab"))])]))));;
(print_string "\n");;

(* '#(1 '(5 6)) *)
(print_string (print_consts_as_list (expandConstList (make_consts_list [Const'
 (Sexpr
   (Vector
     [Number (Int 1);
      Pair (Symbol "quote",
       Pair (Pair (Number (Int 5), Pair (Number (Int 6), Nil)), Nil))]))]))));;
(print_string "\n");;


end;;

