(* author: dennis kraft 
 * largely revised and infix operators: rené neumann
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

    (* consumes a declaration *)
    val moduDecl = maybe ($$"hidden" ==> K false || $$"show" ==> K true)
               >>= (fn b => decl b || trim identifier >>= udecl b)

    (* consumes a list of declarations *)
    val decls = sequence (jump ($";")) moduDecl
			    (* allow an extra ';' at end of declaration list *)
			    -- maybe ($";")


    (* consumes a proctype definition given the activity (needed for 1 lookahead) *)
    fun proctype act = 
                ($$ "proctype" ==> K ProcType || $$ "D_proctype" ==> K DProcType)
                >>= (fn ty => trim identifier
                >>= (fn s  => $"(" >> (decls || return nil) -- $")"
                >>= (fn ds => maybe (priority())
                >>= (fn p  => maybe ($$ "provided" >> $"(" >> expr() -- $")")
                >>= (fn e  => $"{" >> seq() -- $"}"
                ==> (fn ss => ty {active = act, name = s, decls = ds, prio = p,
                                  prov = e, seq = ss}))))))

	(* consumes a module and returns error message in case of fail *)
    fun module _ = "module expected" !!
            maybe ($$ "active" >> maybe ($"[" >> constant -- $"]")) 
            >>= proctype
         || $$ "init" >> maybe (priority ())
            >>| ($"{" >> seq() -- $"}")
            ==> (fn (p,sps) => Init {prio = p, seq = sps})
         || $$ "never" >> $"{" >> seq() -- $"}" ==> Never
         || $$ "trace" >> $"{" >> seq() -- $"}" ==> Trace
         || $$ "notrace" >> $"{" >> seq() -- $"}" ==> NoTrace
         || $$ "inline" 
            >>  trim identifier -- $"("
            >>= (fn s => (sequence ($",") (trim identifier) || return nil)
            >>= (fn args => $")" >> $"{" >> seq() -- $"}"
            ==> (fn steps => Inline {name = s, args = args, seq = steps})))
         || $$ "typedef" >> identifier
            >>| ($"{" >> decls -- $"}")
            ==> (fn (a,b) => TypeDef {name = a, decls = b})
         || $$ "mtype" >> (
               maybe ($"=") >> $"{" >> sequence ($",") (trim identifier) -- $"}" ==> MType
            || sequence ($",") (mtypeDecl()) 
               ==> (fn ds => ModuDecl (Decl {vis = NONE, sort = VarTypeMType, decl = ds})))
         || $$ "ltl" >> trim identifier >>| ltl ==> (fn (n,l) => LTL {name = n, formula = l})
         || moduDecl ==> ModuDecl
	
    (* --------------------------------------------------------------------------------------------
	 * program parser
	 * ------------------------------------------------------------------------------------------*)

    fun program _ = space 
                 >> list (module ()-- maybe ($";"))
                 -- (empty() || fail "module expected")


	(* --------------------------------------------------------------------------------------------
	 * module, program and file parse printer
	 * ------------------------------------------------------------------------------------------*)


	(* parses a module and prints the result *)
	fun moduleParsePrint s = print ((showModule (parse (module()) s)) ^ "\n")
		handle (ParseException e) => print (e ^ "\n")
		
	(* parses a program and prints the result *)
	fun programParsePrint s = 
		let
			fun f nil = ""
				| f (m :: nil) = showModule m
				| f (m :: ms) = showModule m ^ "\n" ^ f ms
		in
			print ((f (parse (program()) s)) ^ "\n")
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

	fun stringParse s = parse (program()) s
	val fileParse = stringParse o fileToString

end;
