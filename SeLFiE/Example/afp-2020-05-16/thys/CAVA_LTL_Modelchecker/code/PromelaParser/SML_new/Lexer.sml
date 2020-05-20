(* author: dennis kraft 
 * largely revised and infix operators: rené neumann
 *
 * parsers for lexicographic analysis *)

open Basic

structure Lexer : sig
	
	val alpha : char parser
	val digit : char parser
	val keyword : string -> string parser
    val $$ : string -> string parser
	val identifier : string parser
	val number : int parser
	val constant : int parser
	val comment : char parser
	val space : char list parser
	val trim : 'a parser -> 'a parser
	val string : string parser
	val ltl : string parser
	val opr : string -> string parser
	val symbol : string -> string parser
    val $ : string -> string parser
	val block_start : string parser
	val block_end : string parser
	
end = struct

	
	(* --------------------------------------------------------------------------------------------
 	 * keywords
 	 * ------------------------------------------------------------------------------------------*)


	(* returns true if the given char list represents a keyword and false otherwise (a binary set 
	 * implementation might be more efficient than this pattern matching approach)*)
	fun isKeyword "active" = true
		| isKeyword "assert" = true
		| isKeyword "atomic" = true
		| isKeyword "bit" = true
		| isKeyword "bool" = true
		| isKeyword "break" = true
		| isKeyword "byte" = true
		| isKeyword "chan" = true
		| isKeyword "D_proctype" = true
		| isKeyword "d_step" = true
		| isKeyword "do" = true
		| isKeyword "else" = true
		| isKeyword "empty" = true
		| isKeyword "enabled" = true
		| isKeyword "eval" = true
		| isKeyword "false" = true
		| isKeyword "fi" = true
		| isKeyword "for" = true
		| isKeyword "full" = true
		| isKeyword "get_priority" = true
		| isKeyword "goto" = true
		| isKeyword "hidden" = true
		| isKeyword "if" = true
		| isKeyword "in" = true
		| isKeyword "init" = true
		| isKeyword "inline" = true
		| isKeyword "int" = true
		| isKeyword "len" = true
		| isKeyword "ltl" = true
		| isKeyword "mtype" = true
		| isKeyword "nempty" = true
		| isKeyword "never" = true
		| isKeyword "nfull" = true
		| isKeyword "notrace" = true
		| isKeyword "np_" = true
		| isKeyword "od" = true
		| isKeyword "of" = true
		| isKeyword "pc_value" = true
		| isKeyword "pid" = true
		| isKeyword "printf" = true
		| isKeyword "printm" = true
		| isKeyword "priority" = true
		| isKeyword "proctype" = true
		| isKeyword "provided" = true
		| isKeyword "run" = true
		| isKeyword "set_priority" = true
		| isKeyword "select" = true
		| isKeyword "short" = true
		| isKeyword "show" = true
		| isKeyword "skip" = true
		| isKeyword "timeout" = true
		| isKeyword "trace" = true
		| isKeyword "true" = true
		| isKeyword "typedef" = true
		| isKeyword "unless" = true
		| isKeyword "unsigned" = true
		| isKeyword "xr" = true
		| isKeyword "xs" = true
		| isKeyword _ = false


	(* --------------------------------------------------------------------------------------------
	 * lexicographic parser
	 * ------------------------------------------------------------------------------------------*)


	(* consumes one alphabetical char *)
    val alpha = satisfy (fn c => (Char.isAlpha c) orelse (c = #"_"))
	
	(* consumes one numeral char *)
    val digit = satisfy Char.isDigit
	
	(* consumes the specified keyword and returns error message in case of fail *)
    fun keyword cs = try (
            list alpha ==> implode
            >>=	(fn cs' => 
                    if cs = cs'
					then return cs' 
				    else fail ("keyword " ^ cs ^ " expected")
                ))
	
	(* consumes an identifier and returns error message in case of fail *)
    val identifier = try (
            (alpha || fail "identifier expected")
            >>=	(fn c => list (alpha || digit)
			>>= (fn cs => let val kw = implode (c :: cs) in
                    if isKeyword kw
					then fail ("identifier expected but keyword '" ^ kw ^ "' found")
					else return kw end)))
				
	(* consumes an integer number and returns error message in case of fail *)
    val number = 
		let
			fun f acc nil = acc
				| f acc (c :: cs) = f (10 * acc + (Char.ord c - Char.ord #"0")) cs
		in
			list digit 
			>>= (fn nil => fail "number expected"
			 	   | cs => return (f 0 cs))
		end
		
	(* consumes a constant and returns error message in case of fail *)
    val constant = "constant expected" !!
			   number 
            || keyword "true" ==> K 1
            || keyword "false" ==> K 0
            || keyword "skip" ==> K 1
			
	(* consumes a comment and returns error message in case of fail *)
    val comment =
		let
            fun p () = try (
                list (satisfy (fn c => not (c = #"*")))
                >> item #"*"
                >>= (fn _ => item #"/" || p ())
                >> return #" ")
		in
			   items [#"/", #"*"] 
            >> (p () || fail "open comment")
		end
	
	(* consumes space chars and comments until non space char is reached *)
    val space = list (satisfy Char.isSpace || comment )

	(* applies specified parser and trims following space *)
	fun trim p = p -- space
    val	$$ = trim o keyword	
	(* consumes a string enclosed in quotation marks and returns error message in case of fail *)
	val string =
		let
            val p = try (
                 list (satisfy (fn c => not (c = #"\""))) -- item #"\""
                 ==> implode)
		in
			   item #"\"" 
            >> (p || fail "open string")
		end

		
	(* consumes an ltl formula enclosed in Curly brackets and returns error message in case of fail *)
    val ltl =
		let
            val p = try (
                    list (satisfy (fn c => not (c = #"}"))) -- item #"}"
                    ==> implode )
		in
			item #"{" >> (p || fail "open ltl")
		end

	(* consumes the specified operator and returns error message in case of fail (note that this 
	 * parser is designed to avoid ambiguity in case of operators starting with the same char) *)
	fun opr "&" = "operator '&' expected" !!
				  try (item #"&" >>! item #"&") ==> K "&"
		| opr "|" = "operator '|' expected" !!
					try (item #"|" >>! item #"|") ==> K "|"
		| opr ">" = "operator '>' expected" !!
                    try (item #">" >>! (item #"=" || item #">")) ==> K ">"
		| opr "<" = "operator '<' expected" !!
                    try (item #"<" >>! (item #"=" || item #"<")) ==> K "<"
		| opr "!" = "operator '!' expected" !!
                    try (item #"!" >>! (item #"=" || item #"!")) ==> K "!"
		| opr "-" = "operator '-' expected" !!
                    try (item #"-" >>! item #">") ==> K "-"
		| opr cs = "'" ^ cs ^ "' expected" !! 
                   try (items (explode cs) ==> implode)

	(* consumes the specified special characters and returns error message in case of fail 
	 * (note that this parser is designed to avoid ambiguity in case of sequences starting
	 * with the same char) *)
  fun symbol "?<" = "'?<' expected" !!
                    try (trim (item #"?") >> item #"<") ==> K "?<"
    | symbol "??<" = "'??<' expected" !!
                    try (trim (items [#"?", #"?"]) >> item #"<") ==> K "??<"
	| symbol "?[" = "'?[' expected" !!
                    try (trim (item #"?") >> item #"[") ==> K "?["
	| symbol "??[" = "'??[' expected" !!
                    try (trim (items [#"?", #"?"]) >> item #"[") ==> K "??["
	| symbol "??" = "'??' expected" !!  
                    try (trim (items [#"?", #"?"]) 
                          >>! ( item #"<" || item #"[" ))
                          ==> K "??"
	| symbol "?" = "'?' expected" !!
                   try (trim (item #"?" >>! item #"?")
                        >>! (item #"<" || item #"["))
                        ==> K "?"
	| symbol "!" = "'!' expected" !! opr "!"
	| symbol "=" = "'=' expected" !!
                   try (item #"="
                        >>! item #"=")
                        ==> K "="
	| symbol ":" = "':' expected" !!
                   try (item #":"
                        >>! item #":")
                        ==> K ":"
	| symbol "." = "'.' expected" !!
                  try (item #"."
                       >>! item #".")
                       ==> K "."
	| symbol cs = "'" ^ cs ^ "' expected" !!
                  try (items (explode cs))
                  ==> implode

    val $ = trim o symbol

	(* opening block *)
    val block_start = $ "{"

	(* closing block. also pushes a ';' *)
    val block_end = $ "}"
                    >> maybe ($ ";" || $ "->")
                    >> pushback [#";"]
                    ==> K "}"
end;
