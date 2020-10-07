(* author: dennis kraft 
 * largely revised and infix operators: rené neumann
 *
 * parser for statements, also includes a parser for send arguments, ranges, options, sequences, 
 * steps and declarations *)

open Basic
open Lexer
open Expression
open Syntax

structure Statement : sig
	
	val decl : bool option -> decl parser
	val udecl : bool option -> string -> decl parser
	val mtypeDecl : unit -> varDecl parser
	
	val seq : unit -> (step list) parser
  val step: unit -> step parser
	
	val stmnt : unit -> stmnt parser
  val stmntSRALE : string -> stmnt parser
	
	val stmntParsePrint : string -> unit
	
end = struct


	(* --------------------------------------------------------------------------------------------
 	 * various parsers
 	 * ------------------------------------------------------------------------------------------*)


	(* consumes a list of expressions in the form of send arguments *)
	fun sendArgs _ =
            expr ()
        >>| (    $"(" >> sequence ($",") (expr()) -- $")"
              || list ($"," >> expr())
            )
        ==> (op ::)

	(* consumes a range *)
    fun range _ = varRef ()
              >>= (fn v1 =>    $":" >> expr() -- $".." >>| expr() 
                                 ==> (fn (e1, e2) => RangeFromTo {var = v1, from = e1, to = e2})
                            || $$ "in" >> varRef () 
                                 ==> (fn v2 => RangeIn {var = v1, inside = v2}) )
	
	(* consumes a sequence of steps*)						
    fun seq _ = step ()
			>>| list (($"->" || jump ($";")) >> step())
			(* allow an extra ';' at end of sequence *)
            --  maybe ($";")
            ==> (op ::)
			
	(* consumes a sequence of options *)						
	and opts _ = "options expected" !! 
                 try (listOne ($"::" >> seq ()))

	(* --------------------------------------------------------------------------------------------
	 * declaration parsers
	 * ------------------------------------------------------------------------------------------*)


	(* consumes a declaration and returns error message in case of fail *)
	and decl b = "variable type expected" !!
                numVarType () 
            >>| sequence ($",") (numDecl()) 
            ==> (fn (t,ds) => Decl {vis = b, sort = t, decl = ds})
        ||  $$  "chan" 
            >>  sequence ($",") (chanDecl())
            ==> (fn ds => Decl {vis = b, sort = VarTypeChan, decl = ds})
        ||  $$  "unsigned"
            >>  sequence ($",") (unsignedDecl())
            ==> (fn ds => Decl {vis = b, sort = VarTypeUnsigned, decl = ds})
        ||  $$  "mtype"
            >>  sequence ($",") (mtypeDecl())
            ==> (fn ds => Decl {vis = b, sort = VarTypeMType, decl = ds})
					
	(* consumes a user defined variable declaration *)
	and udecl b s = sequence ($",") (numDecl()) 
                    ==> (fn ds => Decl {vis = b, sort = VarTypeCustom s, decl = ds})
	
	(* consumes a declaration of a numerical variable *)
	and numDecl _ = trim identifier
            >>= (fn s => maybe ($"[" >> constant -- $"]")
            >>= (fn x => maybe ($"=" >> expr ())
            ==> (fn e => VarDeclNum {name = s, size = x, init = e})))
	
	(* consumes a declaration of a channel variable *)
	and chanDecl _ = trim identifier
            >>= (fn s => maybe ($"[" >> constant -- $"]")
            >>= (fn x => maybe ($"=" >> $"[" >> constant -- $"]"
                                >>| ($$ "of" >> $"{" >>
                                     sequence ($",") (varType())
                                     -- $"}"))
            ==> (fn cap => VarDeclChan {name = s, size = x, capacityTypes = cap})))

	(* consumes a declaration of an unsigned varaible *)
	and unsignedDecl _ = trim identifier
            >>= (fn s => $":" >> constant
            >>= (fn x => maybe ($"=" >> expr ())
            ==> (fn e => VarDeclUnsigned {name = s, bits = x, init = e})))
			
	(* consumes a declaration of a numerical varaible *)
	and mtypeDecl _ = trim identifier
            >>= (fn s => maybe ($"[" >> constant -- $"]")
            >>= (fn x => maybe ($"=" >> trim identifier)
            ==> (fn e => VarDeclMType {name = s, size = x, init = e})))
			
	(* consumes a variable type and returns an error message in case of fail *)
	and varType _ = "variable type expected" !! trim (
               $$ "bit"   ==> K VarTypeBit
            || $$ "bool"  ==> K VarTypeBool
            || $$ "byte"  ==> K VarTypeByte
            || $$ "pid"   ==> K VarTypePid
            || $$ "short" ==> K VarTypeShort
            || $$ "int"   ==> K VarTypeInt
            || $$ "mtype" ==> K VarTypeMType
            || $$ "chan"  ==> K VarTypeChan
            || identifier ==> VarTypeCustom)

	(* consumes a numeral variable type and returns an error message in case of fail *)
	and numVarType _ = "numeral variable type expected" !! trim (
               $$ "bit"   ==> K VarTypeBit
            || $$ "bool"  ==> K VarTypeBool
            || $$ "byte"  ==> K VarTypeByte
            || $$ "pid"   ==> K VarTypePid
            || $$ "short" ==> K VarTypeShort
            || $$ "int"   ==> K VarTypeInt)


	(* --------------------------------------------------------------------------------------------
	 * step parser
	 * ------------------------------------------------------------------------------------------*)


	(* consumes a step and returns an error message in case of fail *)
	and step _ = "step expected" !!
            (   $$ "hidden" >> return (SOME false)
             || $$ "show"   >> return (SOME true)
             || return NONE)
            >>= (fn SOME b => decl (SOME b) ==> StepDecl
                           || (trim identifier >>= udecl (SOME b)) ==> StepDecl
                 |  NONE   => decl NONE ==> StepDecl
                           || trim identifier
                              >>= (fn s => udecl NONE s ==> StepDecl
                                        || stmntSRALE s
                                           >>| maybe ($$ "unless" >> stmnt())
                                           ==> (fn (st1,st2) => 
                                                StepStmnt {stmnt = st1, unless = st2})))
         || stmnt() >>| maybe ($$ "unless" >> stmnt()) 
            ==> (fn (st1,st2) => StepStmnt {stmnt = st1, unless = st2})
         || $$ "xr" >> sequence ($",") (varRef()) ==> StepXR
         || $$ "xs" >> sequence ($",") (varRef()) ==> StepXS

	(* --------------------------------------------------------------------------------------------
	 * statement parsers
	 * ------------------------------------------------------------------------------------------*)

	(* consumes a statement and returns an error message in case of fail *)
	and stmnt _ =  "statement expected" !!
               trim identifier >>= stmntSRALE
            || $$ "if" >>= (fn _ => opts () -- $$ "fi" ==> StmntIf)
            || $$ "do" >>= (fn _ => opts () -- $$ "od" ==> StmntDo)
            || $$ "for" >> $"(" >> range() -- $")"
               >>| (block_start >>= (fn _ => seq() -- block_end))
               ==> (fn (r,s) => StmntFor {range = r, steps = s})
            || $$ "atomic" >> block_start >>= (fn _ => seq() -- block_end
               ==> StmntAtomic)
            || $$ "d_step" >> block_start >>= (fn _ => seq() -- block_end
               ==> StmntDStep)
            || $$ "select" >> $"(" >> range() -- $")"
               ==> StmntSelect
            || block_start >>= (fn _ => seq() -- block_end
               ==> StmntSeq)
            || $$ "else" ==> K StmntElse
            || $$ "break" ==> K StmntBreak
            || $$ "goto" >> trim identifier ==> StmntGoTo
            || $$ "printf" >> $"(" >> trim string 
               >>| list ($"," >> expr()) -- $")"
               ==> (fn (s,es) => StmntPrintF {text = s, args =es})
            || $$ "printm" >> $"(" >> trim identifier -- $")"
               ==> StmntPrintM
            || $$  "run" 
               >>  trim identifier
               >>= (fn s => $"(" >> (exprArgs() || return nil)
               >>= (fn e => $")" >> maybe (priority())
               ==> (fn x => StmntRun {name = s, args = e, prio = x})))
            || $$ "assert" >> $"(" >> expr() -- $")" ==> StmntAssert
            || expr() ==> StmntCond
			
	(* consumes a send, receive, assign, label or expression statement given an initial identifier
	 * string (needed for 1 lookahead) *)
	and stmntSRALE s = 
                maybe ($"[" >> expr() -- $"]")
            >>| maybe ($"." >> varRef())
            >>= (fn (NONE,NONE) => stmntSend s NONE NONE
                                || stmntRecv s NONE NONE
                                || stmntAssign s NONE NONE
                                || stmntCall s
                                || stmntExpr s NONE NONE ==> StmntCond
                                || stmntLabel s
                  | (e,v) => stmntSend s e v
                          || stmntRecv s e v
                          || stmntAssign s e v
                          || stmntExpr s e v ==> StmntCond)
			
	(* consumes a send statement given an initial variable reference (needed for 1 lookahead) *)
	and stmntSend s e v2 = 
		let
          fun stmnt c es = c {var = VarRef {name = s, index = e, next = v2},
            args = es}
		in
            $"!!" >> sendArgs() ==> stmnt StmntSortSend
         || $"!" >> sendArgs() ==> stmnt StmntSend
		end

	(* consumes a receive statement given an initial variable reference (needed for 1 lookahead) *)
	and stmntRecv s e v2 = 
		let
          fun stmnt c es = c {var = VarRef {name = s, index = e, next = v2},
            args = es}
		in
            $"??<" >> recvArgs() -- $">" ==> stmnt StmntRndRecvX
         || $"?<" >> recvArgs() -- $">" ==> stmnt StmntRecvX
         || $"??" >> recvArgs() ==> stmnt StmntRndRecv
         || $"?" >> recvArgs() ==> stmnt StmntRecv
		end
		
	(* consumes an assign statement given an initial variable reference (needed for 1 lookahead) *)
	and stmntAssign s e1 v2 = 
		let
          val v1 = VarRef {name = s, index = e1, next = v2}
		in
			$"=" >> expr() ==> (fn e => StmntAssign {var = v1, expr = e})
         || $"++" ==> K (StmntIncr v1)
         || $"--" ==> K (StmntDecr v1)
		end

	(* consumes an label statement given an initial string (needed for 1 lookahead) *)
	and stmntLabel s = $":" >> stmnt() ==> (fn st => StmntLabeled {name = s, stmnt = st})

    (* consumes a call to an 'inline' macro given the macro's name (needed for 1
    * lookahead) *)
    and stmntCall s = $"(" >> (varArgs() || return nil) -- $")"
                  ==> (fn args => StmntCall {name = s, args = args})

	(* --------------------------------------------------------------------------------------------
	 * operator precedence hierarchy for statement expressions 
	 * ------------------------------------------------------------------------------------------*)

    and stmntSimple opStr opC nxt exp v = 
                    nxt v
                >>| list (trim (opr opStr) >> exp())
                =|> foldl (fn (e1, e2) =>
                       ExprBinOp {opr = opC, exprLeft = e2, exprRight = e1})

    and stmntMult v nxt exp opStrs opF =
        let
          val opP = foldl (fn (op1, op2) => op2 || opr op1) (opr (hd opStrs)) (tl opStrs)
        in
              nxt v
          >>| list (trim opP >>| exp())
          =|> foldl (fn ((opStr, e1), e2) => 
					 ExprBinOp {opr = opF opStr handle Match => raise UnexhaustivePatternMatch,
                                exprLeft = e2, exprRight = e1})
        end

	(* top level in precedence hierachy *)
	and stmntExpr s e v = stmntExprOr (VarRef {name = s, index = e, next = v})

	and stmntExprOr v = stmntSimple "||" BinOpOr stmntExprAnd exprAnd v
	and stmntExprAnd v = stmntSimple "&&" BinOpAnd stmntExprBitOr exprBitOr v
	and stmntExprBitOr v = stmntSimple "|" BinOpBitOr stmntExprBitXor exprBitXor v
	and stmntExprBitXor v = stmntSimple "^" BinOpBitXor stmntExprBitAnd exprBitAnd v
	and stmntExprBitAnd v = stmntSimple "&" BinOpBitAnd stmntExprEq exprEq v

	(* equality level in precedence hierachy *)
	and stmntExprEq v = stmntMult v stmntExprInEq exprInEq
                         ["==", "!="]
                         (fn "==" => BinOpEq
                           | "!=" => BinOpNEq)

	(* inequality level in precedence hierachy *)
	and stmntExprInEq v = stmntMult v stmntExprShift exprShift
                           ["<", "<=", ">=", ">"]
                           (fn "<" => BinOpLe
                             | "<=" => BinOpLEq
                             | ">=" => BinOpGEq
                             | ">" => BinOpGr)

	(* shift level in precedence hierachy *)
	and stmntExprShift v = stmntMult v stmntExprAdd exprAdd
                            ["<<", ">>"]
                            (fn "<<" => BinOpShiftL
                              | ">>" => BinOpShiftR)

	(* add level in precedence hierachy *)
	and stmntExprAdd v = stmntMult v stmntExprMul exprMul
                           ["+", "-"]
                           (fn "+" => BinOpAdd
                             | "-" => BinOpSub)

	(* inequality level in precedence hierachy *)
	and stmntExprMul v = stmntMult v
                           (fn VarRef {name = s, index = e, next = NONE} => exprVarPoll v || exprRemote s e
                             | _ => exprVarPoll v)
                           exprUn
                           ["*", "/", "%"]
                           (fn "*" => BinOpMul
                             | "/" => BinOpDiv
                             | "%" => BinOpMul)

	(* --------------------------------------------------------------------------------------------
	 * statement parse printer
	 * ------------------------------------------------------------------------------------------*)


	(* parses a statemnt and prints the result *)
	fun stmntParsePrint s = print ((showStmnt (parse (stmnt ()) s)) ^ "\n")
		handle (ParseException e) => print (e ^ "\n")

end;
