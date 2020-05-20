(* author: dennis kraft 
 *
 * basic parsers and combinators *)

structure Basic : sig

	type 'a parser

	exception ParseException of string

	val return : 'a -> 'a parser
	val fail : string -> 'a parser
	val satisfy : (char -> bool) -> char parser
	val empty : unit -> unit parser
	val pushback : char list -> char list parser

	val bind : 'a parser -> ('a -> 'b parser) -> 'b parser
	val or : 'a parser -> 'a parser -> 'a parser
	val try : 'a parser -> 'a parser
	val jump : 'a parser -> 'a parser
	val xmsg : string -> 'a parser -> 'a parser

	val one : unit -> char parser
	val item : char -> char parser
	val items : char list -> (char list) parser
	val conv : ('a -> 'b) -> 'a parser -> 'b parser
	val listOne : 'a parser -> ('a list) parser
	val list : 'a parser -> ('a list) parser
    val sequence : 'a parser -> 'b parser -> ('b list) parser
	val maybe : 'a parser -> ('a option) parser
	
	val parse : 'a parser -> string -> 'a
	
end = struct	


	(* --------------------------------------------------------------------------------------------
 	 * data structures
 	 * ------------------------------------------------------------------------------------------*)

	(* position of parser *)
	type position = {ln: int, col: int}

	(* state of parser *)
	type 'a state = {cnm: bool, res: 'a option, sfx: char list, pos: position, msgs: string list}

	(* parser *)
	type 'a parser = char list -> 'a state

	(* exception caused by a failed parse providing a list of possible causes *)
	exception ParseException of string

	(* --------------------------------------------------------------------------------------------
	 * position functions
	 * ------------------------------------------------------------------------------------------*)


	fun initPos NONE = {ln = 1, col = 0}
		| initPos (SOME #"\n") = {ln = 2, col = 0}
		| initPos (SOME _) = {ln = 1, col = 1}

	fun addPos {ln = l1, col = c1} {ln = 1, col = c2} = {ln = l1, col = c1 + c2}
		| addPos {ln = l1, col = c1} {ln = l2, col = c2} = {ln = l1 + l2 - 1, col = c2}


	(* --------------------------------------------------------------------------------------------
	 * basic parsers
	 * ------------------------------------------------------------------------------------------*)


	(* parser returning the specified element without consuming input *)
	fun return a = fn cs => {cnm = false, res = SOME a, sfx = cs, pos = initPos NONE, msgs = nil}

	(* parser failing with the specified message without consuming input *)
	fun fail m = fn cs => {cnm = false, res = NONE, sfx = cs, pos = initPos NONE, msgs = [m]}

	(* parser consuming the first char of the input if it satisfies the specified predicate and 
	 * fails without consuming input otherwise
	 * in case of empty input the parser fails without consuming input *)
	fun satisfy f = fn nil => {cnm = false, res = NONE, sfx = nil, pos = initPos NONE, msgs = nil}
		| (c :: cs) => (case f c of
			true => {cnm = true, res = SOME c, sfx = cs, pos = initPos (SOME c), msgs = nil}
			| false => {cnm = false, res = NONE, sfx = (c :: cs), pos = initPos NONE, msgs = nil})
			
	(* parser failing if input is not empty (needed to check if parse is finished) *)
	fun	empty _ = fn nil => {cnm = false, res = SOME (), sfx = nil, pos = initPos NONE, msgs = nil}
		| cs => {cnm = false, res = NONE, sfx = nil, pos = initPos NONE, 
				msgs = nil}

	(* pushes back some string. always succeeds and returns the string itself *)
	fun pushback s = fn cs => 
	  {cnm = true, res = SOME cs, sfx = s@cs, pos = initPos NONE, msgs = nil}


	(* --------------------------------------------------------------------------------------------
	 * parser combinators
	 * ------------------------------------------------------------------------------------------*)


	(* applies first parser to the input and in case of success the second parser based on the
	 * ouput of the first one
	 * should the first parser fail its output is returned immediately *)
	fun bind p f = fn cs => (case p cs of
		{cnm = false, res = SOME a', sfx = cs', pos = p', msgs = ms'} => (case (f a') cs' of
			{cnm = c'', res = a'', sfx = cs'', pos = p'', msgs = ms''} =>
					{cnm = c'', res = a'', sfx = cs'', pos = addPos p' p'', msgs = ms''})
		| {cnm = false, res = NONE, sfx = cs', pos = p', msgs = ms'} =>
				{cnm = false, res = NONE, sfx = cs', pos = p', msgs = ms'}
		| {cnm = true, res = SOME a', sfx = cs', pos = p', msgs = _} => (case (f a') cs' of
			{cnm = _, res = a'', sfx = cs'', pos = p'', msgs = ms''} =>
					{cnm = true, res = a'', sfx = cs'', pos = addPos p' p'', msgs = ms''})
		| {cnm = true, res = NONE, sfx = cs', pos = p', msgs = ms'} => 
				{cnm = true, res = NONE, sfx = cs', pos = p', msgs = ms'})

	(* applies first parser to the input and if it does not consume any input also the second one
	 * should both parsers fail without consuming input then the error messages are combined *)
	fun or p q = fn cs => (case p cs of
		{cnm = false, res = SOME a', sfx = cs', pos = p', msgs = ms'} => (case q cs of
			{cnm = false, res = _, sfx = _, pos = _, msgs = _} =>
					{cnm = false, res = SOME a', sfx = cs', pos = p', msgs = ms'}
			| other => other)
		| {cnm = false, res = NONE, sfx = cs', pos = p', msgs = ms'} => (case q cs of
			{cnm = false, res = NONE, sfx = _, pos = _, msgs = ms''} =>
					{cnm = false, res = NONE, sfx = cs', pos = p', msgs = ms' @ ms''}
			| other => other)
		| other => other)

	(* tries the specified parser on the input and if it fails after consuming input a fail without
	 * consumed input is returned (this enables arbitrary lookahead) *)
	fun try p = fn cs => (case p cs of
		{cnm = true, res = NONE, sfx = _, pos = _, msgs = ms} =>
				{cnm = false, res = NONE, sfx = cs, pos = initPos NONE, msgs = ms}
		| other => other)
		
	(* marks the specified parser as not consumed (hack to ignore unnecessary ';') *)
	fun	jump p = fn cs => (case p cs of
		{cnm = true, res = r, sfx = cs', pos = p', msgs = ms} =>
				{cnm = false, res = r, sfx = cs', pos = p', msgs = ms}
		| other => other)

	(* replaces the messages in the parser by the specfied one in case of fail without 
	 * consumed input*)
	fun xmsg m p = fn cs => (case p cs of
		{cnm = false, res = NONE, sfx = cs', pos = p', msgs = ms'} =>
				{cnm = false, res = NONE, sfx = cs', pos = p', msgs = [m]}
		| other => other)

	(* --------------------------------------------------------------------------------------------
	 * useful parsers
	 * ------------------------------------------------------------------------------------------*)


	(* consumes one arbitrary char *)
	fun one _ = satisfy (fn _ => true)

	(* consumes the specified char*)
	fun item c = satisfy (fn c' => c = c')

	(* consumes the specified char list *)
	fun items nil = return nil
		| items (c :: cs) = try (bind (item c)
				(fn _ => bind (items cs) 
				(fn _ => return (c :: cs))))

	(* converts the result of a parser accoring to the specified function *)
	fun conv f p = bind p 
			(fn b => return (f b))

	(* applies a parser as long as possible but at least once*)
	fun listOne p = bind p 
			(fn b => bind (or (listOne p) (return nil))
			(fn bs => return (b :: bs)))

	(* applies a parser as long as possible *)
	fun list p = or (listOne p) (return nil)

    fun sequence s p = bind p
            (fn x => bind (list (bind s (fn _ => p )))
            (fn xs => return (x::xs)))

	(* tries to apply the specified parser and if it fails without consuming returns none *)
	fun maybe p = or (conv (fn a => SOME a) p) (return NONE)


	(* --------------------------------------------------------------------------------------------
	 * parse function
	 * ------------------------------------------------------------------------------------------*)


	(* apply a parser to a string and returns the result if the parser succeds*)
	fun parse p s = case p (explode s) of
		{cnm = _, res = SOME a, sfx = _, pos = _, msgs = _} => a
		| {cnm = _, res = NONE, sfx = cs, pos = {ln = l, col = c}, msgs = ms} => raise (ParseException
				("parser exception in line " ^ (Int.toString l) ^ ", column " ^ (Int.toString c) ^ 
				"\npossible causes are: " ^ (String.concatWith "\n" ms)))
	
end;
