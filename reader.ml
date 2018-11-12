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


(*Whitespaces parser*)
let whitespaces_parser = star nt_whitespace;;

(*symbol parser START*)
let _digit_  = PC.range '0' '9';;
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

(*symbol parser END*)


  
(*START char parsering*)
let a_to_f_ = PC.range 'a' 'f';;
let a_to_F_ = PC.range 'A' 'F';;

let hexDigitParser = PC.disj _digit_ (PC.disj a_to_f_ a_to_F_);; 

let char_prefix = PC.word "#\\";; 
let hex_prefix = PC.word_ci "#x";;
let hex_natural = PC.plus hexDigitParser;;

let visibleSimpleCharParser =
  let simpleParser = PC.const (fun ch -> ch > ' ') in
  PC.pack simpleParser (fun (ch) -> Char(ch));;

let newlineChar = '\n';;
let nullChar = '\000';;
let pageChar = '\012';;
let returnChar = '\r';;
let tabChar = '\t';;
let spaceChar = ' ';;

(*problem with inputs like "TAB" fix this-update: i foext this, need to check*)
let namedCharParser =
  let wordsParsersList = List.map (fun str -> word_ci str) ["newline"; "nul"; "page"; "return"; "tab"; "space"] in
  let disjParser = PC.disj_list wordsParsersList in
  PC.pack disjParser (fun (e) -> match (list_to_string (List.map lowercase_ascii e)) with
  | "nul" -> Char(nullChar)
  | "newline"-> Char(newlineChar)
  | "page" -> Char(pageChar)
  | "return" -> Char(returnChar)
  | "tab" -> Char(tabChar)
  | "space" -> Char(spaceChar)
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


let un_visibleSimpleCharParser =  PC.const (fun ch -> ch <= ' ') ;;

let packedEndOfInput =
  pack (nt_end_of_input) (fun (el1) -> ('\000'));;

let  _comment_parser  =
  let newLineChar = PC.char_ci '\n' in
  let oneLineChars = star (PC.diff PC.nt_any (PC.char_ci '\n')) in
  let endOfComment = disj newLineChar packedEndOfInput in
let parser = PC.caten (PC.caten (PC.char ';')  oneLineChars) endOfComment in
		    PC.pack parser (fun ((s,o),e)->s);;
		    

(*identifies all the invisible chars - less than ' ' *)
let _whitespace_and_co_parser = PC.disj un_visibleSimpleCharParser _comment_parser ;;


let make_wrapped_with_junk p = 
  let parser = PC.caten (PC.caten (PC.star _whitespace_and_co_parser) p)  (PC.star _whitespace_and_co_parser) in
  PC.pack parser (fun ((jl,p),jr) -> p);;

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
let _float_zero_ =
let parser = PC.caten (PC.word "-0.") _natural_ in
PC.pack parser (fun (i,n)-> Number(Float(float_of_string((list_to_string i) ^ (list_to_string n)))));;
		    
let _float_non_zero = 
  let parser = PC.caten (PC.caten _integer_ (PC.char '.'))  _natural_ in
  PC.pack parser (fun ((i,d),n)-> match i with 
  | Number(Int(i_int)) -> Number(Float(float_of_string ((string_of_int i_int) ^ "." ^ (list_to_string n))))
     (*else Number(Float(-1.0 *. (float_of_string ((string_of_int i_int) ^ "." ^ (list_to_string n)))))*)
  | _ -> raise X_no_match);;


let _float_ = disj _float_zero_ _float_non_zero;;


(*hex_integer_ works!*)
let _hex_integer = 
  let parser = PC.caten (PC.caten hex_prefix  (PC.maybe _plus_or_minus_)) hex_natural in
  PC.pack parser (fun ((p,s),n)-> match s with
  | Some c -> if c = '-'
    then Number(Int(-1*(int_of_string ("0x" ^ (list_to_string n)))))
    else Number(Int(int_of_string ("0x" ^ (list_to_string n))))
  |None -> Number(Int(int_of_string ("0x" ^ (list_to_string n)))));;

let _hex_float_non_zero = 
  let parser = PC.caten (PC.caten _hex_integer (PC.char '.')) hex_natural in
  PC.pack parser (fun ((i,d),n) -> match i with
  |Number(Int(i_int))-> 
if i_int > 0 then Number(Float((float_of_int i_int) +. float_of_string ("0x0." ^ (list_to_string n))))
else Number(Float((float_of_int i_int) -. float_of_string ( "0x0." ^ (list_to_string n))))
  | _ -> Number(Float(0.0)));;

let _hex_float_zero =
let parser = PC.caten (PC.word_ci "#x-0.") hex_natural in
PC.pack parser (fun (i,n)-> Number(Float(float_of_string("-0x0." ^ (list_to_string n)))));;

let _hex_float = disj _hex_float_zero _hex_float_non_zero;;


let _l_paren = PC.char '(';;
let _r_paren = PC.char ')';;

let rec convert_to_nested_pair sexpr_list = match sexpr_list with
| [] -> Nil
| head::body ->  Pair (head, (convert_to_nested_pair body));;

let rec convert_to_nested_pair_dotted_list sexpr_list sexpr_element = match sexpr_list with
| [] -> sexpr_element
|head::body -> Pair(head,(convert_to_nested_pair_dotted_list body sexpr_element));;

let vector_prefix = PC.word "#(";;


(*string parser START*)
let stringLiteralChar = const (fun c -> c <> '\\' && c <> '\"');;

(* we return chars(really chars) and not Char (sexp chars) so that we can cuild the whole string from whose chars *)
let stringHexChar = 
  let backslashXParser = word_ci "\\x" in (*TODO: check if word or word_ci*)
  let semiColonParser = char ';' in
  let parser = caten backslashXParser (caten (plus hexDigitParser) semiColonParser) in
  pack parser (fun (bs_x, (hexdigits, semicolon)) -> Char.chr(int_of_string ("0x" ^ (list_to_string hexdigits))));; (*converting
															  hexdigits to their
															  real char value 
															  from ascii table

														    *)

(* we return chars(really chars) and not Char (sexp chars) so that we can cuild the whole string from whose chars *)
let stringMetaChar =
  let list = List.map (fun str -> word_ci str) ["\\\\"; "\\\""; "\\t"; "\\f"; "\\n"; "\\r"] in (* CHEK doublebackslash and backslashquote*)
  let parser = disj_list list in
  pack parser (fun chlist -> match (list_to_string (List.map lowercase_ascii chlist)) with
  | "\\\\" -> '\\'
  | "\\t" -> '\t' (*again the same prob. like in namedCharParser TAB/tAB etc. - I FIXED IT, NEED TO CHECK CHECK!!!*)
  | "\\\"" ->  '\"'
  | "\\f" ->  Char.chr(12)
  | "\\n" ->  '\n'
  | "\\r" ->  '\r'
  | _ -> Char.chr(0) (* I wanted to throw an exception but it didn't let me; anyway this case never happens *)
  );;

let stringCharParser = disj_list [stringMetaChar; stringLiteralChar; stringHexChar];;


(*string paeser END*)


let spaced_parser p = 
let parser =  PC.not_followed_by p  (PC.diff (PC.diff PC.nt_any PC.nt_whitespace) _r_paren)  in
 make_wrapped_with_junk parser;;

let nt_r_paren_ = disj (PC.char ']') (PC.char ')');;
let nt_l_paren_ = disj (PC.char '(') (PC.char '[');;

(**********************************************************************************************************************************************************************)


let rec _sexpr_ s = 
let _all_parsers = PC.disj_list ( _three_dots_ ::   make_wrapped_with_junk _scientific_notation_ :: make_wrapped_with_junk _boolean_parser_ ::  make_wrapped_with_junk char_parser ::
				    make_wrapped_with_junk _number_ ::  make_wrapped_with_junk string_parser ::  make_wrapped_with_junk symbol_parser ::  make_wrapped_with_junk _dotted_list_parser :: make_wrapped_with_junk _squared_dotted_list_parser::
				    make_wrapped_with_junk  _list_parser :: make_wrapped_with_junk  _squared_list_parser :: make_wrapped_with_junk _vector_parser ::  make_wrapped_with_junk _quoted_ ::  make_wrapped_with_junk _quasi_quoted_ ::
				    make_wrapped_with_junk _unquote_spliced_ :: make_wrapped_with_junk _unquoted_ ::(*make_wrapped_with_junk  _squared_brackets_notation_ ::*)  [])
in _all_parsers s


and _all_ s = 
let parser = PC.disj_list ((PC.diff _sexpr_ _three_dots_) :: _dotted_list_maybe_ :: _list_maybe_ :: _vector_maybe_ :: []) in
parser s

and _three_dots_ s = 
let parser = PC.caten (PC.disj_list (_dotted_list_maybe_:: _list_maybe_ :: _vector_maybe_ :: [])) (PC.word "...") in
let _packed_ = PC.pack parser (fun (l,e)->l) in
_packed_  s


and _dotted_list_maybe_ s = 
let parser = PC.caten ( PC.caten (PC.caten (PC.caten nt_l_paren_  (plus _all_)) (PC.char '.'))  _all_ ) (maybe nt_r_paren_) in
let _packed_ = PC.pack parser (fun((((lp,plus_a),d),a),rp)->  (convert_to_nested_pair_dotted_list plus_a a)) in
_packed_  s


and _list_maybe_ s = 
let parser = PC.caten (PC.caten nt_l_paren_ (star _all_)) (maybe nt_r_paren_) in
let _packed_ = PC.pack parser (fun((lp,a),rp)-> convert_to_nested_pair a) in
_packed_  s

and _vector_maybe_ s = 
let parser = PC.caten (PC.caten (PC.caten (PC.char '#')  nt_l_paren_ ) (star _all_) )  (maybe nt_r_paren_)  in
let _packed_ = PC.pack parser (fun (((prefix, lp),star_a),rp)->Vector(star_a)) in
_packed_ s

and char_parser s =
  let parser = PC.caten char_prefix (PC.disj_list [hexCharParser; namedCharParser; visibleSimpleCharParser]) in   
  let _packed_ = PC.pack parser (fun (pref, ch) -> ch)   (*No need to use Char constructor because in all the sub-parsers
							      we do this so ch is already Char*)
  in _packed_ s

  
and _boolean_parser_ s =
  let boolDisj = disj (word_ci "#t") (word_ci "#f") in
  let _packed_ = PC.pack boolDisj (fun (b)->if (list_to_string (List.map lowercase_ascii b)) = "#t" then Bool(true) else Bool(false)) in
  _packed_ s

and _number_ s =
  let _packed_ = PC.disj (PC.disj (PC.disj _hex_float _float_) _hex_integer) _integer_  in
  _packed_ s


and string_parser s =
  let quote = char '\"' in
  let parser = caten (caten quote (star stringCharParser)) quote in
  let _packed_ = pack parser (fun ((q1, chars), q2) -> String(list_to_string chars)) in
  _packed_ s

and symbol_parser s =
  let symbolCharsParser = PC.plus symbolChar in
  let _packed_ = PC.pack symbolCharsParser (fun s -> Symbol((list_to_string (List.map lowercase_ascii s)))) in
  _packed_ s
  
and _list_parser s =
  let parser = PC.caten (PC.caten  (make_wrapped_with_junk _l_paren)  (PC.star (make_wrapped_with_junk _sexpr_)))
                        (make_wrapped_with_junk _r_paren) in
  let _packed_ = PC.pack parser (fun((l,s),r)-> convert_to_nested_pair s) in
  _packed_ s

and _squared_list_parser s =
  let parser = PC.caten (PC.caten  (make_wrapped_with_junk (char '['))  (PC.star (make_wrapped_with_junk _sexpr_)))
                        (make_wrapped_with_junk (char ']')) in
  let _packed_ = PC.pack parser (fun((l,s),r)-> convert_to_nested_pair s) in
  _packed_ s

and _dotted_list_parser s =
  let parser = PC.caten
    (PC.caten
       (PC.caten
	  (PC.caten  (make_wrapped_with_junk _l_paren)  (PC.plus (make_wrapped_with_junk _sexpr_))) (PC.char '.')) (make_wrapped_with_junk _sexpr_)) (make_wrapped_with_junk _r_paren) in
  let _packed_ = PC.pack parser (fun((((l,p),d),s),r)-> (convert_to_nested_pair_dotted_list p s)) in (*convert_to_nested_pair (p @ [s])) in*)
  _packed_ s

and _squared_dotted_list_parser s =
  let parser = PC.caten
    (PC.caten
       (PC.caten
	  (PC.caten  (make_wrapped_with_junk (char '['))  (PC.plus (make_wrapped_with_junk _sexpr_))) (PC.char '.')) (make_wrapped_with_junk _sexpr_)) (make_wrapped_with_junk (char ']')) in
  let _packed_ = PC.pack parser (fun((((l,p),d),s),r)-> (convert_to_nested_pair_dotted_list p s)) in (*convert_to_nested_pair (p @ [s])) in*)
  _packed_ s

and _vector_parser s =
  let parser = PC.caten (PC.caten  (make_wrapped_with_junk vector_prefix)  (PC.star (make_wrapped_with_junk _sexpr_)))
                        (make_wrapped_with_junk _r_paren) in
  let _packed_ = PC.pack parser (fun((l,s),r)->  Vector(s )) in
  _packed_ s
    
and  _quoted_ s = 
  let parser = PC.caten (PC.char '\'') _sexpr_ in
  let _packed_ = PC.pack parser (fun (c,e)-> Pair(Symbol("quote"), Pair(e, Nil))) in
  _packed_ s
    
and  _quasi_quoted_ s = 
  let parser = PC.caten (PC.char '`') _sexpr_ in
  let _packed_ = PC.pack parser (fun (c,e)-> Pair(Symbol("quasiquote"), Pair(e, Nil))) in
  _packed_ s                
    
and  _unquoted_ s = 
  let parser = PC.caten (PC.char ',') _sexpr_ in
  let _packed_ = PC.pack parser (fun (c,e)-> Pair(Symbol("unquote"), Pair(e, Nil))) in
  _packed_ s                
    
and _unquote_spliced_ s = 
  let parser = PC.caten (PC.word_ci ",@") _sexpr_ in
  let _packed_ = PC.pack parser (fun (c,e)-> Pair(Symbol("unquote-splicing"), Pair(e, Nil))) in
  _packed_ s

and _scientific_notation_ s =
  let intOrFloat = disj _float_ _integer_ in
  let eOrE = char_ci 'e' in
  let parser = caten (caten intOrFloat eOrE) _integer_ in
  let _packed_ = pack parser (fun (((base, e), exponent)) -> match base, exponent with
    | Number(Float(b)), Number(Int(e)) -> Number(Float(b *. (10.0 ** float_of_int(e))))
    | Number(Int(b)), Number(Int(e)) -> Number(Float(float_of_int(b) *. (10.0 ** float_of_int(e))))
    | _ -> raise X_no_match) in
  _packed_ s


(*and _squared_brackets_notation_ s = (*FIX THE SPACE AFTER AN SEXPR PROBLEM (SEE IN TESTS) *)
  let wrappedSexpr = make_wrapped_with_junk _sexpr_ in
  let emptyParser = pack (caten (char '[') (caten (star nt_whitespace) (char ']'))) (fun ((lb,(ws,rb))) -> convert_to_nested_pair []) in
  let singleParser = pack (caten (char '[') (caten wrappedSexpr (char ']'))) (fun ((lb, (sexpr, rb))) -> convert_to_nested_pair [sexpr]) in
  let coupleParser = pack (caten (char '[') (caten wrappedSexpr (caten wrappedSexpr (char ']'))))
                                                (fun ((lb, (sexpr1, (sexpr2, rb)))) -> convert_to_nested_pair [sexpr1; sexpr2]) in
  let _packed_ = disj_list [emptyParser; singleParser; coupleParser] in
  _packed_ s*);;

(*COMMENTS PARSEERS*)

 
				  
(*
let _sexpr_comment_parser_ =
  let prefix = caten (char ';') (char '#') in
  let parser = caten prefix _sexpr_ in
(*I DONT UNDERSTAND WHAT SEXPR COMMENT SHOULD RETURN :( *)
*)

let read_sexpr string =
  let (sexpr, charlist) = (not_followed_by _sexpr_ nt_any) (string_to_list string) in
  sexpr;;

let read_sexprs string =
  let (sexprList, charlist) = (star _sexpr_) (string_to_list string) in
  sexprList;;

(**********************************************************************************************************************************************************************)


(*--------tests--------*)
(*SQUARE BRACKETS NOTATION TESTS*)
(*
let e1 = read_sexpr "[]";;
let e2 = read_sexpr "[#t ]";; (*[#t] without the space doesnt work but it should!!! - FIX*)
let x2 = Pair(Bool(true), Nil);;
let e3 = read_sexpr "[#t 1 ]   ";;
let x3 = Pair(Bool(true), Pair(Number(Int(1)), Nil));;

let f e = match e with
| Number(Float(e_float)) -> print_float(e_float)
| _ ->print_float(0.0);;
*)
(*
let x = Number(Float(-1.0 *. (float_of_string "0x10.99")));;
let e = read_sexpr  "#x-10.99";;
print_string (string_of_bool (sexpr_eq e x));;
f e;;
*)






(*scientific notation tests*)
(*
let (e, s) = _scientific_notation_ (string_to_list "10.0E2");;
let x = Number(Float(1000.0));;
print_string (string_of_bool (sexpr_eq x e));;
*)

(*Boolean tests*)
(*
let (e, s) = _sexpr_ (string_to_list " #t");;
let x = Bool(true);;
print_string (string_of_bool (sexpr_eq x e));;
*)


(*regular string test*)
(*
let str2 = "\"hello\"";;
print_string str2;;
trace_pc "strings parser" string_parser (string_to_list "\"hello\"");;
(*let (e, s) = string_parser (string_to_list str);; 
*)

(*

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

*)

(*Symbol tests*)
(*
let (e,s) = symbol_parser (string_to_list "?C");;
 let x =  Symbol("?c ");;
print_string (string_of_bool (sexpr_eq x e));;(* COMMENT OUT FOR TESTING *)
*)

(*---char tests---*)
(*
let (e,s) = char_parser (string_to_list "#\\xa");;
  let x =  Char('\n');;
print_string (string_of_bool (sexpr_eq x e));;(* COMMENT OUT FOR TESTING *)

(**print_string (list_to_string e);;**)

(*let x = namedCharParser "newline";;*)

(*print_string (e);;*)
(*let b = Bool(false);;
let x = Number(Int(5));;
print_string (string_of_bool (sexpr_eq b e));
*)

*)

end;; (* struct Reader *) (*MOVE ME TO BEFORE TESTS*)
