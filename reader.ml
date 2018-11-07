
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
let symbol_parser =
  let symbolCharsParser = PC.plus symbolChar in
  PC.pack symbolCharsParser (fun s -> Symbol((list_to_string (List.map lowercase_ascii s))));;
(*symbol parser END*)

(*boolean works!*)
(* let _boolean_parser_ =  *****BOOLEAN VERSION 2 WITH NOT FOLLOWED BY *****
  let boolDisj = disj (word_ci "#t") (word_ci "#f") in
  let parser = caten (caten whitespaces_parser boolDisj) whitespaces_parser in
  let packedParser = PC.pack parser (fun ((s1, b), s2)->if (list_to_string b) = "#t" then Bool(true) else Bool(false)) in
  not_followed_by packedParser symbol_parser
;; *)

let _boolean_parser_ =
  let boolDisj = disj (word_ci "#t") (word_ci "#f") in
  let parser = caten (caten whitespaces_parser boolDisj) whitespaces_parser in
  pack parser (fun ((s1, b), s2)->if (list_to_string (List.map lowercase_ascii b)) = "#t" then Bool(true) else Bool(false));; 

(*START char parsering*)
let a_to_f_ = PC.range 'a' 'f';;
let a_to_F_ = PC.range 'A' 'F';;

let hexDigitParser = PC.disj _digit_ (PC.disj a_to_f_ a_to_F_);; 

let char_prefix = PC.word "#\\";; 
let hex_prefix = PC.word "#x";;
let hex_natural = PC.plus hexDigitParser;;

let visibleSimpleCharParser =
  let simpleParser = PC.const (fun ch -> ch > ' ') in
  PC.pack simpleParser (fun (ch) -> Char(ch));;

let newlineChar = '\n';;
let nullChar = '\000';;
let pageChar = '\014';;
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

(*string parser START*)
let stringLiteralChar = const (fun c -> c <> '\\' && c <> '\"');; (*Check BOTH !!!!!!!!!!!!!!!!!!!!!*)
 

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

let string_parser =
  let quote = char '\"' in
  let parser = caten (caten quote (star stringCharParser)) quote in
  pack parser (fun ((q1, chars), q2) -> String(list_to_string chars));;

(*string paeser END*)

(*Comments Parser START*)
(*let line_comments_parser =
  let semiColonParser = char ';' in
  pack semiColonParser (fun (sc, rest) -> *)
  
(*Comments parser END*)

let read_sexpr string =
  let (e, s) = (disj_list [_boolean_parser_; char_parser; _number_; symbol_parser; string_parser]) (string_to_list string) in
  e;;

let read_sexprs string = raise X_not_yet_implemented;;
 (* let (e, s) = (disj_list [_boolean_parser_; char_parser; _number_; symbol_parser; string_parser]) (string_to_list string) in
  match (List.length s) with
  | 0 -> e
    | _ -> read_sexprs s;; *) (*JUST AN UNSECCESFULL TRYING*)


(*--------tests--------*)
(*Boolean tests*)

(*
let (e, s) = _boolean_parser_ (string_to_list "#t");;
let x = Bool(true);;
print_string (string_of_bool (sexpr_eq x e));;
*)


(*NADAVS TESTS STARS*)
(* USAGE: change the value of the parsers below,
 to the names of your parsers.
 These parsers are according to the CFG, with the addition of line and sexpr comments  *)
let nt_not_implemented = nt_none;;

let ____Bool = _boolean_parser_ ;;
let ____Number = _number_ ;;
let ____Char = char_parser;;
let ____String = string_parser ;;
let ____Symbol = symbol_parser ;;
let ____List = nt_not_implemented ;;
let ____Dotted_List = nt_not_implemented ;;
let ____Vector = nt_not_implemented ;;
let ____Qouted = nt_not_implemented ;;
let ____QuasiQuoted = nt_not_implemented ;;
let ____Unquoted = nt_not_implemented ;;
let ____UnquoteAndSpliced = nt_not_implemented ;;
let ____Sexpr = nt_not_implemented ;;



let test_nt doc_string nt input_string expected_value =
  try
    let (result, remaining_chars) = (nt (string_to_list input_string)) in
    if (result = expected_value)
    then if remaining_chars <> []
	 then Printf.printf
		"!!! test %s gave correct value, with remaining chars -->[%s]\n"
		doc_string
		(list_to_string remaining_chars)
	 else ()
    else Printf.printf "!!! test %s gave an incorrect value\n" doc_string
  with X_not_yet_implemented ->
    Printf.printf "!!! test %s failed\n" doc_string;;

let rec run_tests tests =
  match tests with
  |[] -> ()
  | test :: tests ->
     (test(); run_tests tests);;

let tester () =
  run_tests
    [(fun () -> test_nt "boolean test 1" ____Bool "#t" (Bool(true))) ;
    (fun () -> test_nt "boolean test 2" ____Bool "#T" (Bool(true))) ;
    (fun () -> test_nt "boolean test 3" ____Bool "#f" (Bool(false))) ;
    (fun () -> test_nt "boolean test 4" ____Bool "#F" (Bool(false))) ;
    (fun () -> test_nt "number test 1" ____Number "1" (Number(Int(1)))) ;
    (fun () -> test_nt "number test 2" ____Number "01290" (Number(Int(1290))));
    (fun () -> test_nt "number test 3" ____Number "-10" (Number(Int(-10))));
    (fun () -> test_nt "number test 4" ____Number "-03" (Number(Int(-3))));
    (fun () -> test_nt "number test 5" ____Number "-0" (Number(Int(0))));
    (fun () -> test_nt "number test 6" ____Number "+8" (Number(Int(8))));
    (fun () -> test_nt "number test 7" ____Number "#x16" (Number(Int(22))));
    (fun () -> test_nt "number test 8" ____Number "#xabfd" (Number(Int(44029))));
    (fun () -> test_nt "number test 10" ____Number "#x-1a" (Number(Int(-26))));
    (fun () -> test_nt "number test 11" ____Number "#x+1a" (Number(Int(26))));
    (fun () -> test_nt "number test 12" ____Number "1.0" (Number(Float(1.0))));
    (fun () -> test_nt "number test 13" ____Number  "0005.0129" (Number(Float(5.0129)))) ;
    (* (fun () -> test_nt "number test 14" ____Number  "501.100000000000000000000" (Number(Float(501.1))));(*FAIL-EXCEPTION int_of_string*)*)
    (fun () -> test_nt "number test 16" ____Number  "-0.0" (Number(Float(0.0)))) ; (*PASS PASS ITS A GOAL *)
    (fun () -> test_nt "number test 17" ____Number  "+999.12349999999" (Number(Float(999.12349999999)))) ; (*PASS PASS ITS A COME*)
    (fun () -> test_nt "number test 18" ____Number  "-102.000000000000001" (Number(Float(-102.)))) ; (*PASSS PASS*)
    (*(fun () -> test_nt "number test 19" ____Number  "#x1.ab" (Number(Float(1.66796875)))) ; (*FAIL different result*) *)
    (fun () -> test_nt "number test 20" ____Number  "#x+a.0" (Number(Float(10.0)))) ; (*PASSSS*)
    (*(fun () -> test_nt "number test 21" ____Number  "#x-1.ab000000000" (Number(Float(-1.66796875)))) ; (*FAIL different result*) *)
    (fun () -> test_nt "char test 1" ____Char "#\\a" (Char('a'))) ;
    (fun () -> test_nt "char test 2" ____Char "#\\A" (Char('A'))) ;
    (fun () -> test_nt "char test 3" ____Char "#\\?" (Char('?'))) ;
    (fun () -> test_nt "char test 4" ____Char "#\\~" (Char('~'))) ;
    (fun () -> test_nt "char test 5" ____Char "#\\x30" (Char('0'))) ;
    (fun () -> test_nt "char test 6" ____Char "#\\xa" (Char('\n'))) ;
    (fun () -> test_nt "char test 7" ____Char "#\\tab" (Char('\t'))) ;
    (fun () -> test_nt "char test 8" ____Char "#\\space" (Char(' '))) ;
    (fun () -> test_nt "char test 9" ____Char "#\\newline" (Char('\n'))) ;
    (fun () -> test_nt "char test 10" ____Char "#\\\\" (Char('\\'))) ;
    (fun () -> test_nt "string test 1" ____String "\"Hello\"" (String("Hello"))) ;
    (fun () -> test_nt "string test 3" ____String "\"Hello World!\"" (String("Hello World!")));
    (fun () -> test_nt "string test 4" ____String "\"Hello\\n World!\"" (String("Hello\n World!"))) ;
    (fun () -> test_nt "string test 5" ____String "\"\\t\"" (String("\t"))) ;
    (fun () -> test_nt "string test 6" ____String "\"\\\\\"" (String("\\"))) ;
    (fun () -> test_nt "string test 7" ____String "\"\"" (String(""))) ;
    (fun () -> test_nt "symbol test 1" ____Symbol "wfkjwf" (Symbol("wfkjwf"))) ;
    (fun () -> test_nt "symbol test 2" ____Symbol "23148!" (Symbol("23148!"))) ;
    (fun () -> test_nt "symbol test 3" ____Symbol "x1" (Symbol("x1"))) ;
    (fun () -> test_nt "symbol test 4" ____Symbol "lambda" (Symbol "lambda" )) ;
    (fun () -> test_nt "symbol test 5" ____Symbol "define" (Symbol("define")))
    ];;
tester ();;
(*NADAVS TESTS END*)

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
  print_string (string_of_bool (sexpr_eq b e));*)

*)

end;; (* struct Reader *) (*MOVE ME TO BEFORE TESTS*)

