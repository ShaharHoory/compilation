
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

(*problem with inputs like "TAB" fix this-update: i foext this, need to check*)
let namedCharParser =
  let wordsParsersList = List.map (fun str -> word_ci str) ["newline"; "nul"; "page"; "return"; "tab"; "space"] in
  let disjParser = PC.disj_list wordsParsersList in
  PC.pack disjParser (fun (e) -> match (list_to_string (List.map lowercase_ascii e)) with
  | "nul" -> Char('\000')
  | "newline"-> Char('\012')
  | "page" -> Char('\014')
  | "return" -> Char('\015')
  | "tab" -> Char('\011')
  | "space" -> Char('\040')
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

(*------Strings-------*)

(*symbol parser START*)
let _a_to_z = PC.range 'a' 'z';;
let _A_to_Z = PC.range 'A' 'Z';;
let symbolChar = PC.disj_list [_digit_; _a_to_z; _A_to_Z;
			       char '!';
			       char '$';
			       char '^';
			       char '*';
			       char '-';
			       char '_';
			       char '=';
			       char '+';
			       char '<';
			       char '>';
			       char '?';
			       char '/';
			       char ':'
			      ];;
let symbol_parser =
  let symbolCharsParser = PC.plus symbolChar in
  PC.pack symbolCharsParser (fun s -> Symbol(String.lowercase (list_to_string s)));;
(*symbol parser END*)

(*string parser START*)
let stringLiteralChar = const (fun c -> c <> '\\' && c <> '\"');; (*Check BOTH !!!!!!!!!!!!!!!!!!!!!*)
 

(* we return chars(really chars) and not Char (sexp chars) so that we can cuild the whole string from whose chars *)
let stringHexChar = 
  let backslashXParser = word_ci "\x" in (*TODO: check if word or word_ci*)
  let semiColonParser = char ';' in
  let parser = caten backslashXParser (caten (plus hexDigitParser) semiColonParser) in
  pack parser (fun (bs_x, (hexdigits, semicolon)) -> Char.chr(int_of_string ("0x" ^ (list_to_string hexdigits))));; (*converting
															  hexdigits to their
															  real char value 
															  from ascii table
														    *)

(* we return chars(really chars) and not Char (sexp chars) so that we can cuild the whole string from whose chars *)
let stringMetaChar =
  let list = List.map (fun str -> word_ci str) ["\\"; "\""; "\t"; "\nul"; "\f"; "\n"; "\r"] in (* CHEK doublebackslash and backslashquote
												  TODO: in the table 
												  in the assignment they
												  say that ther's also
												  \nul ???? CHECK *)
  let parser = disj_list list in
  pack parser (fun chlist -> match (list_to_string (List.map lowercase_ascii chlist)) with
  | "\\" -> Char.chr(92)
  | "\t" -> Char.chr(9)
  | "\nul" ->  Char.chr(0) (*again the same prob. like in namedCharParser NUL/nUL etc. - I FIXED IT, NEED TO CHECK CHECK!!!*)
  | "\"" ->  Char.chr(34)
  | "\f" ->  Char.chr(12)
  | "\n" ->  Char.chr(10)
  | "\r" ->  Char.chr(13)
  | _ -> Char.chr(0) (* I wanted to throw an exception but it didn't let me; anyway this case never happens *)
  );;

let stringCharParser = disj_list [stringLiteralChar; stringHexChar; stringMetaChar];; (*the result is already a Char
											because we packed each sub-parser*)
let string_parser =
  let quote = char '\"' in
  let parser = caten quote (caten (star stringCharParser) quote) in
  pack parser (fun (q1, (chars, q2)) -> String(list_to_string chars));;

(*let string_parser =
  let parser = star stringCharParser in
  pack parser (fun (e) -> String(list_to_string e));; *)

(*string paeser END*)

(*--------tests--------*)

(*regular string test*)
(*let str = Char.escaped('"') ^ "hello" ^ Char.escaped('"');;*)
let str2 = "\"hello\"";;
print_string str2;;
trace_pc "strings parser" string_parser (string_to_list "\"hello\"");;
(*let (e, s) = string_parser (string_to_list str);; (*there's no match because in "hello" the quotes  belong
							to ocaml but we need 2 more quotes: ""hello""
							(the second cpuple belongs to scheme input *)
let x = String("hello");;
  print_string (string_of_bool (sexpr_eq x e));;*)

(*hex string test*)
let (e, s) = string_parser (string_to_list "\x30");; 
let x = String("0");;
print_string (string_of_bool (sexpr_eq x e));;

(*hex string test - DOESN'T WORK!!!*)
let (e, s) = string_parser (string_to_list "\n");; 
let x = String(Char.escaped (Char.chr(10)));;
print_string (string_of_bool (sexpr_eq x e));;

(*---char tests---*)
(*let (e,s) = char_parser (string_to_list "#\a");;
  let x =  Char('a');;*)
(***print_string (string_of_bool (sexpr_eq x e));; COMMENT OUT FOR TESTING *)

(**print_string (list_to_string e);;**)

(*let x = namedCharParser "newline";;*)

(*print_string (e);;*)
(*let b = Bool(false);;
let x = Number(Int(5));;
  print_string (string_of_bool (sexpr_eq b e));*)



