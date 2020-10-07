(* author: dennis kraft 
 *
 * parsers for lexicographic analysis *)

open Basic

structure Lexer : sig
	
	val alpha : unit -> char parser
	val digit : unit -> char parser
	val keyword : char list -> (char list) parser
	val identifier : unit -> string parser
	val number : unit -> int parser
	val constant : unit -> int parser
	val comment : unit -> char parser
	val space : unit -> (char list) parser
	val trim : 'a parser -> 'a parser
	val string : unit -> string parser
	val ltl : unit -> string parser
	val opr : (char list) -> (char list) parser
	val symbol : (char list) -> (char list) parser
	val block_start : unit -> (char list) parser
	val block_end : unit -> (char list) parser
	
end = struct

	
	(* --------------------------------------------------------------------------------------------
 	 * keywords
 	 * ------------------------------------------------------------------------------------------*)


	(* returns true if the given char list represents a keyword and false otherwise (a binary set 
	 * implementation might be more efficient than this pattern matching approach)*)
	fun isKeyword [#"a", #"c", #"t", #"i", #"v", #"e"] = true
		| isKeyword [#"a", #"s", #"s", #"e", #"r", #"t"] = true
		| isKeyword [#"a", #"t", #"o", #"m", #"i", #"c"] = true
		| isKeyword [#"b", #"i", #"t"] = true
		| isKeyword [#"b",#"o", #"o", #"l"] = true
		| isKeyword [#"b",#"r", #"e", #"a", #"k"] = true
		| isKeyword [#"b", #"y", #"t", #"e"] = true
		| isKeyword [#"c", #"h", #"a", #"n"] = true
		| isKeyword [#"D", #"_", #"p", #"r", #"o", #"c", #"t", #"y", #"p", #"e"] = true
		| isKeyword [#"d", #"_", #"s", #"t", #"e", #"p"] = true
		| isKeyword [#"d", #"o"] = true
		| isKeyword [#"e", #"l", #"s", #"e"] = true
		| isKeyword [#"e", #"m", #"p", #"t", #"y"] = true
		| isKeyword [#"e", #"n", #"a", #"b", #"l", #"e", #"d"] = true
		| isKeyword [#"e", #"v", #"a", #"l"] = true
		| isKeyword [#"f", #"a", #"l", #"s", #"e"] = true
		| isKeyword [#"f", #"i"] = true
		| isKeyword [#"f", #"o", #"r"] = true
		| isKeyword [#"f", #"u", #"l", #"l"] = true
		| isKeyword [#"g", #"e", #"t", #"_", #"p", #"r", #"i", #"o", #"r", #"i", #"t", #"y"] = true
		| isKeyword [#"g", #"o", #"t", #"o"] = true
		| isKeyword [#"h", #"i", #"d", #"d", #"e", #"n"] = true
		| isKeyword [#"i", #"f"] = true
		| isKeyword [#"i", #"n"] = true
		| isKeyword [#"i", #"n", #"i", #"t"] = true
		| isKeyword [#"i", #"n", #"l", #"i", #"n", #"e"] = true
		| isKeyword [#"i", #"n", #"t"] = true
		| isKeyword [#"l", #"e", #"n"] = true
		| isKeyword [#"l", #"t", #"l"] = true
		| isKeyword [#"m", #"t", #"y", #"p", #"e"] = true
		| isKeyword [#"n", #"e", #"m", #"p", #"t", #"y"] = true
		| isKeyword [#"n", #"e", #"v", #"e", #"r"] = true
		| isKeyword [#"n", #"f", #"u", #"l", #"l"] = true
		| isKeyword [#"n", #"o", #"t", #"r", #"a", #"c", #"e"] = true
		| isKeyword [#"n", #"p", #"_"] = true
		| isKeyword [#"o", #"d"] = true
		| isKeyword [#"o", #"f"] = true
		| isKeyword [#"p", #"c", #"_", #"v", #"a", #"l", #"u", #"e"] = true
		| isKeyword [#"p", #"i", #"d"] = true
		| isKeyword [#"p", #"r", #"i", #"n", #"t", #"f"] = true
		| isKeyword [#"p", #"r", #"i", #"n", #"t", #"m"] = true
		| isKeyword [#"p", #"r", #"i", #"o", #"r", #"i", #"t", #"y"] = true
		| isKeyword [#"p", #"r", #"o", #"c", #"t", #"y", #"p", #"e"] = true
		| isKeyword [#"p", #"r", #"o", #"v", #"i", #"d", #"e", #"d"] = true
		| isKeyword [#"r", #"u", #"n"] = true
		| isKeyword [#"s", #"e", #"t", #"_", #"p", #"r", #"i", #"o", #"r", #"i", #"t", #"y"] = true
		| isKeyword [#"s", #"e", #"l", #"e", #"c", #"t"] = true
		| isKeyword [#"s", #"h", #"o", #"r", #"t"] = true
		| isKeyword [#"s", #"h", #"o", #"w"] = true
		| isKeyword [#"s", #"k", #"i", #"p"] = true
		| isKeyword [#"t", #"i", #"m", #"e", #"o", #"u", #"t"] = true
		| isKeyword [#"t", #"r", #"a", #"c", #"e"] = true
		| isKeyword [#"t", #"r", #"u", #"e"] = true
		| isKeyword [#"t", #"y", #"p", #"e", #"d", #"e", #"f"] = true
		| isKeyword [#"u", #"n", #"l", #"e", #"s", #"s"] = true
		| isKeyword [#"u", #"n", #"s", #"i", #"g", #"n", #"e", #"d"] = true
		| isKeyword [#"x", #"r"] = true
		| isKeyword [#"x", #"s"] = true
		| isKeyword _ = false


	(* --------------------------------------------------------------------------------------------
	 * lexicographic parser
	 * ------------------------------------------------------------------------------------------*)


	(* consumes one alphabetical char *)
	fun alpha _ = satisfy (fn c => (Char.isAlpha c) orelse (c = #"_"))
	
	(* consumes one numeral char *)
	fun digit _ = satisfy Char.isDigit
	
	(* consumes the specified keyword and returns error message in case of fail *)
	fun keyword cs = try (bind (list (alpha ()))
			(fn cs' => if cs = cs' 
					then return cs' 
					else fail ("keyword " ^ implode cs ^ " expected")))
	
	(* consumes an identifier and returns error message in case of fail *)
	fun identifier _ = try (bind (or (alpha ()) (fail "identifier expected"))
			(fn c => bind (list (or (alpha ()) (digit ())))
			(fn cs => if isKeyword (c :: cs)
					then fail ("identifier expected but keyword '" ^ 
							implode (c :: cs) ^ "' found")
					else return (implode (c :: cs)))))
				
	(* consumes an integer number and returns error message in case of fail *)
	fun number _ = 
		let
			fun f acc nil = acc
				| f acc (c :: cs) = f (10 * acc + (Char.ord c - Char.ord #"0")) cs
		in
			bind (list (digit ())) 
			(fn nil => fail "number expected"
			 	| cs => return (f 0 cs))
		end
		
	(* consumes a constant and returns error message in case of fail *)
	fun constant _ = xmsg ("constant expected")
			(or (number ()) 
			(or (conv (fn _ => 1) (keyword [#"t", #"r", #"u", #"e"]))
			(or (conv (fn _ => 0) (keyword [#"f", #"a", #"l", #"s", #"e"]))
			(conv (fn _ => 1) (keyword [#"s", #"k", #"i", #"p"])))))
			
	(* consumes a comment and returns error message in case of fail *)
	fun comment _ =
		let
			fun p () = try (bind (list (satisfy (fn c => not (c = #"*"))))
					(fn _ => bind (item #"*")
					(fn _ => bind (or (item #"/") (p ()))
					(fn _ => return #" "))))
		in
			bind (items [#"/", #"*"]) (fn _ => or (p ()) (fail "open comment"))
		end
	
	(* consumes space chars and comments until non space char is reached *)
	fun space _ = list (or (satisfy Char.isSpace) (comment ()))

	(* applies specified parser and trims following space *)
	fun trim p = bind p 
			(fn a => bind (space ())
			(fn _ => return a))
			
	(* consumes a string enclosed in quotation marks and returns error message in case of fail *)
	fun string _ =
		let
			fun p () = try (bind (list (satisfy (fn c => not (c = #"\""))))
					(fn cs => bind (item #"\"")
					(fn _ => return (implode cs))))
		in
			bind (item #"\"") (fn _ => or (p ()) (fail "open string"))
		end

		
	(* consumes an ltl formula enclosed in Curly brackets and returns error message in case of fail *)
	fun ltl _ =
		let
			fun p () = try (bind (list (satisfy (fn c => not (c = #"}"))))
					(fn cs => bind (item #"}")
					(fn _ => return (implode cs))))
		in
			bind (item #"{") (fn _ => or (p ()) (fail "open ltl"))
		end

	(* consumes the specified operator and returns error message in case of fail (note that this 
	 * parser is designed to avoid ambiguity in case of operators starting with the same char) *)
	fun opr [#"&"] = xmsg ("operator '&' expected") (try (bind
						(or (items [#"&", #"&"])
						(items [#"&"]))
				(fn [#"&"] => return [#"&"]
					| _ => fail "")))
		| opr [#"|"] = xmsg ("operator '|' expected") (try (bind
						(or (items [#"|", #"|"])
						(items [#"|"]))
				(fn [#"|"] => return [#"|"]
					| _ => fail "")))
		| opr [#">"] = xmsg ("operator '>' expected") (try (bind
						(or (items [#">", #"="])
						(or (items [#">", #">"])
						(items [#">"])))
				(fn [#">"] => return [#">"]
					| _ => fail "")))
		| opr [#"<"] = xmsg ("operator '<' expected") (try (bind
						(or (items [#"<", #"="])
						(or (items [#"<", #"<"])
						(items [#"<"])))
				(fn [#"<"] => return [#"<"]
					| _ => fail "")))
		| opr [#"!"] = xmsg ("operator '!' expected") (try (bind
						(or (items [#"!", #"="])
						(or (items [#"!", #"!"])
						(items [#"!"])))
				(fn [#"!"] => return [#"!"]
					| _ => fail "")))
		| opr [#"-"] = xmsg ("operator '-' expected") (try (bind
						(or (items [#"-", #">"])
						(items [#"-"]))
				(fn [#"-"] => return [#"-"]
					| _ => fail "")))
		| opr cs = or (items cs) (fail ("'" ^ implode cs ^ "' expected"))

	(* consumes the specified special characters and returns error message in case of fail 
	 * (note that this parser is designed to avoid ambiguity in case of sequences starting
	 * with the same char) *)
	fun symbol [#"?", #"<"] = or (try (bind (trim (item #"?")) 
				(fn _ => bind (item #"<")
				(fn _ => return [#"?", #"<"]))))
				(fail "'?<' expected")
		| symbol [#"?", #"?", #"<"] = or (try (bind (trim (items [#"?", #"?"])) 
				(fn _ => bind (item #"<")
				(fn _ => return [#"?", #"?", #"<"]))))
				(fail "'??<' expected")
		| symbol [#"?", #"["] = or (try (bind (trim (item #"?")) 
				(fn _ => bind (item #"[")
				(fn _ => return [#"?", #"["]))))
				(fail "'?[' expected")
		| symbol [#"?", #"?", #"["] = or (try (bind (trim (items [#"?", #"?"])) 
				(fn _ => bind (item #"[")
				(fn _ => return [#"?", #"?", #"["]))))
				(fail "'??[' expected")
		| symbol [#"?", #"?"] = xmsg ("'??' expected") (try (bind 
						(or (symbol [#"?", #"?", #"<"])
						(or (symbol [#"?", #"?", #"["])
						(items [#"?", #"?"])))
				(fn [#"?", #"?"] => return [#"?", #"?"]
					| _ => fail "")))
		| symbol [#"?"] = xmsg ("'?' expected") (try (bind 
						(or (symbol [#"?", #"?", #"<"])
						(or (symbol [#"?", #"?", #"["])
						(or (symbol [#"?", #"?"])
						(or (symbol [#"?", #"["])
						(or (symbol [#"?", #"<"])
						(items [#"?"]))))))
				(fn [#"?"] => return [#"?"]
					| _ => fail "")))
		| symbol [#"!"] = xmsg ("'!' expected") (try (bind 
						(or (symbol [#"!", #"!"])
						(or (symbol [#"!", #"="])
						(items [#"!"])))
				(fn [#"!"] => return [#"!"]
						| _ => fail "")))
		| symbol [#"="] = xmsg ("'=' expected") (try (bind
						(or (items [#"=", #"="])
						(items [#"="]))
				(fn [#"="] => return [#"="]
					| _ => fail "")))
		| symbol [#":"] = xmsg ("':' expected") (try (bind
						(or (items [#":", #":"])
						(items [#":"]))
				(fn [#":"] => return [#":"]
					| _ => fail "")))
		| symbol [#"."] = xmsg ("'.' expected") (try (bind
						(or (items [#".", #"."])
						(items [#"."]))
				(fn [#"."] => return [#"."]
						| _ => fail "")))
		| symbol cs = or (items cs) (fail ("'" ^ implode cs ^ "' expected"))

	(* opening block *)
	fun block_start _ = trim (symbol [#"{"])

	(* closing block. also pushes a ';' *)
	fun block_end _ = bind (trim (symbol [#"}"]))
					  (fn s => bind (maybe (or (trim (symbol [#";"]))
											   (trim (symbol [#"-", #">"]))))
					  (fn _ => bind (pushback [#";"])
					  (fn _ => return s)))
end;
