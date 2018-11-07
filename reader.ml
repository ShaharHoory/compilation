
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

open PC

exception X_not_yet_implemented;;
exception X_this_should_not_happen;;
  
type number =
  | Int of int
  | Float of float;;
  
type sexpr =
  | Bool of bool
  | Nil
  | Number of number
  | Char of char
  | String of string
  | Symbol of string
  | Pair of sexpr * sexpr
  | Vector of sexpr list;;

let rec sexpr_eq s1 s2 =
  match s1, s2 with
  | Bool(b1), Bool(b2) -> b1 = b2
  | Nil, Nil -> true
  | Number(n1), Number(n2) -> n1 = n2
  | Char(c1), Char(c2) -> c1 = c2
  | String(s1), String(s2) -> s1 = s2
  | Symbol(s1), Symbol(s2) -> s1 = s2
  | Pair(car1, cdr1), Pair(car2, cdr2) -> (sexpr_eq car1 car2) && (sexpr_eq cdr1 cdr2)
  | Vector(l1), Vector(l2) -> List.for_all2 sexpr_eq l1 l2
  | _ -> false;;
  
module Reader: sig
  val read_sexpr : string -> sexpr
  val read_sexprs : string -> sexpr list
end
= struct
let normalize_scheme_symbol str =
  let s = string_to_list str in
  if (andmap
	(fun ch -> (ch = (Char.lowercase ch)))
	s) then str
  else Printf.sprintf "|%s|" str;;

let read_sexpr string = raise X_not_yet_implemented ;;

let read_sexprs string = raise X_not_yet_implemented;;
  
end;; (* struct Reader *)

(*boolean works!*)
let _boolean_parser_ =
  let parser =  PC.disj (PC.word_ci "#t") (PC.word_ci "#f") in 
  PC.pack parser (fun (b)->if (list_to_string b) = "#t" then Bool(true) else Bool(false));;

(*START char parsering*)
let _digit_  = PC.range '0' '9';;
let a_to_f_ = PC.range 'a' 'f';;
let a_to_F_ = PC.range 'A' 'F';;

let hexDigitParser = PC.disj _digit_ (PC.disj a_to_f_ a_to_F_);; 


let char_prefix = PC.word "#\\" ;; (* need to check this!!! problem with meta char "/" !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
let hex_prefix = PC.word "#x";;
let hex_natural = PC.plus hexDigitParser;;

let visibleSimpleCharParser =
  let simpleParser = PC.const (fun ch -> ch > ' ') in
  PC.pack simpleParser (fun (ch) -> Char(ch));;


let un_visibleSimpleCharParser =
  let simpleParser = PC.const (fun ch -> ch <= ' ') in
  PC.pack simpleParser (fun (ch) -> Char(ch));;

let _comment_parser = PC.caten (PC.caten (PC.char ';') (PC.star PC.nt_any)) PC.nt_end_of_input;;

(*identifies all the invisible chars - less than ' ' *)
let _whitespace_and_co_parser = PC.star un_visibleSimpleCharParser;;

(*need to add parser for commetns *)

let make_wrapped_with_junk p = 
let parser = PC.caten (PC.caten _whitespace_and_co_parser p)  _whitespace_and_co_parser in
PC.pack parser (fun ((jl,p),jr) -> p);;

(*problem with inputs like "TAB" fix this *)

(*let namedCharParser =
  let wordsParsersList = List.map (fun str -> word_ci str) ["newline"; "nul"; "page"; "return"; "tab"; "space"] in
  let disjParser = PC.disj_list wordsParsersList in
  PC.pack disjParser (fun (e) -> match e with
  | ['n'; 'u'; 'l'] -> Char('\000')
  | ['n'; 'e'; 'w'; 'l'; 'i'; 'n'; 'e'] -> Char('\012')
  | ['p'; 'a'; 'g'; 'e'] -> Char('\014')
  | ['r'; 'e'; 't'; 'u'; 'r'; 'n'] -> Char('\015')
  | ['t'; 'a'; 'b'] -> Char('\011')
  | ['s'; 'p'; 'a'; 'c'; 'e'] -> Char('\040')
  | _ -> Char('\000') (* I wanted to throw an exception but it didn't let me; anyway this case never happens *)
  );;



let hexCharParser =
  let parser = PC.caten (PC.char_ci 'x') (PC.plus hexDigitParser) in
  PC.pack parser (fun (x, ch) -> Char(Char.chr(int_of_string ("0x" ^ (list_to_string ch)))));;

let char_parser =
  let parser = PC.caten char_prefix (PC.disj_list [hexCharParser; namedCharParser; visibleSimpleCharParser]) in   
  PC.pack parser (fun (pref, ch) -> ch);;   (*No need to use Char constructor because in all the sub-parsers
					      we do this so ch is already Char*)
(*END char parsering*)
*)


let _natural_ = PC.plus _digit_;; 
let _plus_or_minus_ = PC.disj (PC.char '+') (PC.char '-') ;;

(*integer works!*)
let _integer_ = 
  let parser = PC.caten (PC.maybe _plus_or_minus_) _natural_ in 
      PC.pack parser (fun (s,n)->
	match s with
	| Some c -> if c = '-' 
	  then Number(Int(-1*(int_of_string (list_to_string n))))
	  else Number(Int(int_of_string (list_to_string n)))
	|None -> Number(Int(int_of_string (list_to_string n))));;

(*this is working, can be written cleaner.. & need to change execption instead last case*)
let _float_ = 
  let parser = PC.caten (PC.caten _integer_ (PC.char '.'))  _natural_ in
  PC.pack parser (fun ((i,d),n)-> match i with 
  | Number(Int(i_int)) ->
     if i_int >0 then  Number(Float((float_of_int i_int) +.10.0**(float_of_int(-1*(List.length n)))*.(float_of_int(int_of_string (list_to_string n)))))
     else  Number(Float((float_of_int i_int) +. -. 10.0**(float_of_int(-1*(List.length n)))*.(float_of_int(int_of_string (list_to_string n)))))
  | _ -> Number(Float(0.0)));;

(*hex_integer_ works!*)
let _hex_integer = 
  let parser = PC.caten (PC.caten hex_prefix  (PC.maybe _plus_or_minus_)) hex_natural in
  PC.pack parser (fun ((p,s),n)-> match s with
  | Some c -> if c = '-'
    then Number(Int(-1*(int_of_string ("0x" ^ (list_to_string n)))))
    else Number(Int(int_of_string ("0x" ^ (list_to_string n))))
  |None -> Number(Int(int_of_string ("0x" ^ (list_to_string n)))));;

(*hex_float works! need to change the exception *)
let _hex_float = 
  let parser = PC.caten (PC.caten _hex_integer (PC.char '.')) hex_natural in
  PC.pack parser (fun ((i,d),n) -> match i with
  |Number(Int(i_int))->
     if i_int >0 then Number(Float((float_of_int i_int) +. 10.0**(float_of_int(-1*(List.length n)))*.(float_of_int(int_of_string ("0x" ^ (list_to_string n))))))
     else Number(Float((float_of_int i_int) -. 10.0**(float_of_int(-1*(List.length n)))*.(float_of_int(int_of_string ("0x" ^ (list_to_string n))))))
  | _ -> Number(Float(0.0)));;

(*number works! *)
let _number_ = PC.disj (PC.disj (PC.disj _hex_float _float_) _hex_integer) _integer_ ;;

let _l_paren = PC.char '(';;
let _r_paren = PC.char ')';;
let _sexpr_ = PC.disj _number_ _boolean_parser_ ;;


let rec convert_to_nested_pair sexpr_list = match sexpr_list with
| [] -> Nil
| head::body -> 
Pair (head, (convert_to_nested_pair body));;

let _list_parser =
let parser = PC.caten (PC.caten  (make_wrapped_with_junk _l_paren)  (PC.star (make_wrapped_with_junk _sexpr_))) (make_wrapped_with_junk _r_paren) in
PC.pack parser (fun((l,s),r)-> convert_to_nested_pair s);;

let _dotted_list_parser =
let parser = PC.caten
(PC.caten
 (PC.caten
  (PC.caten  (make_wrapped_with_junk _l_paren)  (PC.plus (make_wrapped_with_junk _sexpr_))) (PC.char '.')) (make_wrapped_with_junk _sexpr_)) (make_wrapped_with_junk _r_paren) in
PC.pack parser (fun((((l,p),d),s),r)-> convert_to_nested_pair (p @ [s]));;

let vector_prefix = PC.word "#(";;
let _vector_parser =
let parser = PC.caten (PC.caten  (make_wrapped_with_junk vector_prefix)  (PC.star (make_wrapped_with_junk _sexpr_))) (make_wrapped_with_junk _r_paren) in
PC.pack parser (fun((l,s),r)->  Vector(s));;


(*tests*)

let (e, s) = _comment_parser (string_to_list  ";xfnxn\nabc");;
(*let result = Pair( (Bool(true)) ,(Pair (Bool(false)), (Pair ((Bool(true)), Nil))));;
      *)

print_string(list_to_string s);;
let result = Pair (Bool(false), Pair (Bool(true), Pair(Bool(false),  Nil)));;
let result2 = Vector(Bool(false) ::  Bool(true) :: Bool(false) :: []);;


let x = '#';;

(*let b = Bool(false);;
let x = Number(Int(5));;
print_string (string_of_bool (sexpr_eq b e));
*)


