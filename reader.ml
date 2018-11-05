
(* reader.ml
 * A compiler from Scheme to x86/64
 *
 * Programmer: Mayer Goldberg, 2018
 *)

#use "pc.ml";;

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


let char_prefix = PC.word "#/" ;; (* need to check this!!! problem with meta char "/" !!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!!! *)
let hex_prefix = PC.word "#x";;
let hex_natural = PC.plus hexDigitParser;;

let visibleSimpleCharParser =
  let simpleParser = PC.const (fun ch -> ch > ' ') in
  PC.pack simpleParser (fun (ch) -> Char(ch));;

(*problem with inputs like "TAB" fix this *)
let namedCharParser =
  let wordsParsersList = List.map (fun str -> PC.word_ci str) ["newline"; "nul"; "page"; "return"; "tab"; "space"] in
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

 (*TODO: add pack which transform this to Char*)

(*let char_parser =
  let parser = PC.caten char_prefix (PC.disj visibleSimpleCharParser (PC.disj namedCharParser hexCharParser)) in
  PC.pack parser (fun (pref, ch) -> Char((first ch)));; *)

let char_parser =
  let parser = PC.caten char_prefix (PC.disj_list [hexCharParser; namedCharParser; visibleSimpleCharParser]) in   
  PC.pack parser (fun (pref, ch) -> ch);;   (*No need to use Char constructor because in all the sub-parsers
					      we do this so ch is already Char*)

(*END char parsering*)

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


(*tests*)

(*let (e, s) = (PC.char 'a') (string_to_list "ab");;*)

let (e,s) = char_parser (string_to_list "#/TAB");;

(**print_string (list_to_string e);;**)


let x =  Char('\011');;
   print_string (string_of_bool (sexpr_eq x e));;

(*let x = namedCharParser "newline";;*)

(*print_string (e);;*)
(*let b = Bool(false);;
let x = Number(Int(5));;
  print_string (string_of_bool (sexpr_eq b e));*)



