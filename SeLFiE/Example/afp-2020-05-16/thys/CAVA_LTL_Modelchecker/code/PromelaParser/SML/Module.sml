(* author: dennis kraft 
 *
 * parser for modules and programs *)

open Basic
open Lexer
open Expression
open Statement
open Syntax

structure Module : sig
	
	val module : unit -> module parser
	
	val program : unit -> (module list) parser
	
	val moduleParsePrint : string -> unit
	val programParsePrint : string -> unit
	val fileParsePrint : string -> unit
	val fileParse : string -> module list
	val stringParse : string -> module list
	exception ParseException of string

end = struct
	(* exception caused by a failed parse providing a list of possible causes *)
	exception ParseException = Basic.ParseException


	(* --------------------------------------------------------------------------------------------
	 * module parsers
	 * ------------------------------------------------------------------------------------------*)


	(* consumes a module and returns error message in case of fail *)
	fun module _ = xmsg ("module expected")
			(or (bind (maybe (bind (trim (keyword [#"a", #"c", #"t", #"i", #"v", #"e"]))
							(fn _ => maybe (bind (trim (symbol [#"["]))
									(fn _ => bind (constant ())
									(fn x => bind (trim (symbol [#"]"]))
									(fn _ => return x)))))))
					(fn x => or (proctype x) (dproctype x)))
			(or (bind (trim (keyword [#"i", #"n", #"i", #"t"]))
					(fn _ => bind (maybe (priority ()))
					(fn x => bind (trim (symbol [#"{"]))
					(fn _ => bind (seq ())
					(fn sps => bind (trim (symbol [#"}"]))
					(fn _ => return (Init {prio = x, seq = sps})))))))
			(or (bind (trim (keyword [#"n", #"e", #"v", #"e", #"r"]))
					(fn _ => bind (trim (symbol [#"{"]))
					(fn _ => bind (seq ())
					(fn sps => bind (trim (symbol [#"}"]))
					(fn _ => return (Never sps))))))
			(or (bind (trim (keyword [#"t", #"r", #"a", #"c", #"e"]))
					(fn _ => bind (trim (symbol [#"{"]))
					(fn _ => bind (seq ())
					(fn sps => bind (trim (symbol [#"}"]))
					(fn _ => return (Trace sps))))))
			(or (bind (trim (keyword [#"n", #"o", #"t", #"r", #"a", #"c", #"e"]))
					(fn _ => bind (trim (symbol [#"{"]))
					(fn _ => bind (seq ())
					(fn sps => bind (trim (symbol [#"}"]))
					(fn _ => return (NoTrace sps))))))
			(or (bind (trim (keyword [#"i", #"n", #"l", #"i", #"n", #"e"]))
					(fn _ => bind (trim (identifier ()))
					(fn s => bind (trim (symbol [#"("]))
					(fn _ => bind (or
								(sequence (trim (symbol [#","])) (trim (identifier ())))
								(return nil))
					(fn args => bind (trim (symbol [#")"]))
					(fn e => bind (trim (symbol [#"{"]))
					(fn _ => bind (seq ())
					(fn sps => bind (trim (symbol [#"}"]))
					(fn _ => 
						return (Inline {name = s, args = args, seq = sps}))))))))))
			(or (bind (trim (keyword [#"t", #"y", #"p", #"e", #"d", #"e", #"f"]))
					(fn _ => bind (trim (identifier ()))
					(fn s => bind (trim (symbol [#"{"]))
					(fn _ => bind (decls ())
					(fn ds => bind (trim (symbol [#"}"]))
					(fn _ => return (TypeDef {name = s, decls = ds})))))))
			(or (bind (trim (keyword [#"m", #"t", #"y", #"p", #"e"]))
					(fn _ => or (bind (maybe (trim (symbol [#"="])))
									(fn _ => bind (trim (symbol [#"{"]))
									(fn _ => bind (sequence (trim (symbol [#","])) 
										(trim (identifier ())))
									(fn ss => bind (trim (symbol [#"}"]))
									(fn _ => return (MType ss))))))
							(bind (sequence (trim (symbol [#","])) (mtypeDecl ()))
									(fn ds => return (ModuDecl (Decl {vis = NONE, 
											sort = VarTypeMType, decl = ds}))))))
			(or (bind (trim (keyword [#"l", #"t", #"l"]))
					(fn _ => bind (trim (identifier ()))
					(fn s1 => bind (trim (ltl ()))
					(fn s2 => return (LTL {name = s1, formula = s2})))))
			(conv (fn d => ModuDecl d) (moduDecl ())))))))))))
					
	(* consumes a proctype definition given the activity (needed for 1 lookahead) *)
	and proctype' kw ty x1 = bind (trim (keyword kw))
			(fn _ => bind (trim (identifier ()))
			(fn s => bind (trim (symbol [#"("]))
			(fn _ => bind (or (decls ()) (return nil))
			(fn ds => bind (trim (symbol [#")"]))
			(fn _ => bind (maybe (priority ()))
			(fn x2 => bind (maybe (bind 
							(trim (keyword [#"p", #"r", #"o", #"v", #"i", #"d", #"e", #"d"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (expr ())
					(fn e => bind (trim (symbol [#")"]))
					(fn _ => return e))))))
			(fn e => bind (trim (symbol [#"{"]))
			(fn _ => bind (seq ())
			(fn sps => bind (trim (symbol [#"}"]))
			(fn _ => return (ty {active = x1, name = s, decls = ds, prio = x2, prov = e,
					seq = sps})))))))))))

	and proctype x1 = proctype' [#"p", #"r", #"o", #"c", #"t", #"y", #"p", #"e"] ProcType x1
	and dproctype x1 = proctype' [#"D", #"_", #"p", #"r", #"o", #"c", #"t",#"y", #"p", #"e"] DProcType x1
					
	(* consumes a list of declarations *)
	and decls _ = bind (moduDecl ())
			(fn d => bind (list (bind (jump (trim (symbol [#";"]))) (fn _ => moduDecl ())))
			(* allow an extra ';' at end of declaration list *)
			(fn ds => bind (maybe (trim (symbol [#";"])))
			(fn _ => return (d :: ds))))
		
	(* consumes a declaration *)
	and moduDecl _ = bind (maybe (trim (or 
					(conv (fn _ => false) (keyword [#"h", #"i", #"d", #"d", #"e", #"n"]))
					(conv (fn _ => true) (keyword [#"s", #"h", #"o", #"w"])))))
			(fn b => or (decl b) (bind (trim (identifier ())) (fn s => udecl b s)))		


	(* --------------------------------------------------------------------------------------------
	 * program parser
	 * ------------------------------------------------------------------------------------------*)


	fun program _ = bind (space ())
		(fn _ => bind (list (bind (module ())
				(* allow an extra ';' at end of module *)
				(fn m => bind (maybe (trim (symbol [#";"])))
				(fn _ => return m))))
		(* check if complete file is parsed*)
		(fn ms => bind (or (empty ()) (fail "module expected"))
		(fn _ => return ms)))


	(* --------------------------------------------------------------------------------------------
	 * module, program and file parse printer
	 * ------------------------------------------------------------------------------------------*)


	(* parses a module and prints the result *)
	fun moduleParsePrint s = print ((showModule (parse (module ()) s)) ^ "\n")
		handle (ParseException e) => print (e ^ "\n")
		
	(* parses a program and prints the result *)
	fun programParsePrint s = 
		let
			fun f nil = ""
				| f (m :: nil) = showModule m
				| f (m :: ms) = showModule m ^ "\n" ^ f ms
		in
			print ((f (parse (program ()) s)) ^ "\n")
					handle (ParseException e) => print (e ^ "\n")
		end

	fun fileToString f =
		let
			val ins = TextIO.openIn f
			fun getString ins = case TextIO.inputLine ins of
				SOME line => line ^ getString ins
				| NONE => ""
		in
			getString ins
		end
		
	(* parses a program from a text file and prints the result *)
	val fileParsePrint = programParsePrint o fileToString

	fun stringParse s = parse (program ()) s
	val fileParse = stringParse o fileToString

end;
