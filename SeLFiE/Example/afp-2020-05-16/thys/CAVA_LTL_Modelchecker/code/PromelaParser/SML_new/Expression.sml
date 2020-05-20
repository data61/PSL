(* author: dennis kraft 
 * largely revised and infix operators: rené neumann
 *
 * parser for expressions, also includes a parser for variable references, receive arguments 
 * and priorities *)

open Basic
open Lexer
open Syntax

structure Expression : sig
	
	exception UnexhaustivePatternMatch
	
	val varRef : unit -> varRef parser
	val varArgs : unit -> varRef list parser
	val exprArgs : unit -> expr list parser
	val recvArg : unit -> recvArg parser
	val recvArgs : unit -> recvArg list parser 
	val priority : unit -> int parser
	
	val expr : unit -> expr parser
	
	val exprOr : unit -> expr parser
	val exprAnd : unit -> expr parser
	val exprBitOr : unit -> expr parser
	val exprBitXor : unit -> expr parser
	val exprBitAnd : unit -> expr parser
	val exprEq : unit -> expr parser
	val exprInEq : unit -> expr parser
	val exprShift : unit -> expr parser
	val exprAdd : unit -> expr parser
	val exprMul : unit -> expr parser
	val exprUn : unit -> expr parser
	
	val exprVarPoll : varRef -> expr parser
	val exprRemote : string -> expr option -> expr parser
	
	val exprParsePrint : string -> unit
	
end = struct

	(* exception to supress unexhaustive patternmatch warning 
	(this should never be actually raised) *)
	exception UnexhaustivePatternMatch


	(* --------------------------------------------------------------------------------------------
 	 * various parsers
 	 * ------------------------------------------------------------------------------------------*)

    fun priority _ = $$ "priority" >> constant

	(* consumes a variable reference and returns error message in case of fail*)
    fun varRef _ = "variable reference expected" !!
                 trim identifier
                 >>= (fn id => maybe ($"[" >> expr () -- $"]" )
                 >>= (fn e  => maybe ($"." >> varRef ())
                 ==> (fn v  => VarRef {name = id, index = e, next = v})))
 
	(* consumes a list of variables *)
    and varArgs _ = sequence ($",") (varRef ())

	(* consumes a list of expressions *)		
    and exprArgs _ = sequence ($",") (expr ())

	(* consumes a receive argument and returns error message in case of fail *)
    and recvArg _ = "receive argument expected" !!
               varRef () ==> RecvArgVar
            || $$ "eval" 
               >> $"(" >> expr () -- $")"
               ==> RecvArgEval
            || trim (opr "-") 
               >> trim constant 
               ==> (RecvArgConst o op ~)
            || trim constant ==> RecvArgConst

	(* consumes a list of receive arguments *)		
	and recvArgs _ = 
                recvArg ()
                >>| (    $"(" >> sequence ($",") (recvArg ()) -- $")"
                      || list ($"," >> recvArg ()) )
                ==> (op ::)

	(* --------------------------------------------------------------------------------------------
	 * operator precedence hierarchy
	 * ------------------------------------------------------------------------------------------*)

	
    and exprSimple opStr opC nxt = 
                nxt ()
            >>| list (trim (opr opStr) >> nxt ())
            =|> foldl (fn (e1, e2) => 
					ExprBinOp {opr = opC, exprLeft = e2, exprRight = e1})

    and exprMult nxt opStrs opF =
        let
          val opP = foldl (fn (op1, op2) => op2 || opr op1) (opr (hd opStrs)) (tl opStrs)
        in
              nxt ()
          >>| list (trim opP >>| nxt())
          =|> foldl (fn ((opStr, e1), e2) => 
					 ExprBinOp {opr = opF opStr handle Match => raise UnexhaustivePatternMatch, 
                                exprLeft = e2, exprRight = e1})
        end

	(* consumes an expression *)
	and expr _ = exprOr ()

	and exprOr _ = exprSimple "||" BinOpOr exprAnd
	and exprAnd _ = exprSimple "&&" BinOpAnd exprBitOr
	and exprBitOr _ = exprSimple "|" BinOpBitOr exprBitXor
	and exprBitXor _ = exprSimple "^" BinOpBitXor exprBitAnd
	and exprBitAnd _ = exprSimple "&" BinOpBitAnd exprEq

	(* equality level in precedence hierachy *)
    and exprEq _ = exprMult exprInEq
                        ["==", "!="] 
                        (fn "==" => BinOpEq 
                          | "!=" => BinOpNEq)
					
	(* inequality level in precedence hierachy *)
	and exprInEq _ = exprMult exprShift
                          ["<", "<=", ">=", ">"]
                          (fn "<" => BinOpLe
                            | "<=" => BinOpLEq
                            | ">=" => BinOpGEq
                            | ">" => BinOpGr)

	(* shift level in precedence hierachy *)
	and exprShift _ = exprMult exprAdd
                           ["<<", ">>"]
                           (fn "<<" => BinOpShiftL
                             | ">>" => BinOpShiftR) 

	(* add level in precedence hierachy *)
	and exprAdd _ = exprMult exprMul
                            ["+", "-"]
                            (fn "+" => BinOpAdd
                              | "-" => BinOpSub)
		
	(* mult level in precedence hierachy *)
	and exprMul _ = exprMult exprUn
                            ["*", "/", "%"]
                            (fn "*" => BinOpMul
                              | "/" => BinOpDiv
                              | "%" => BinOpMod)
	
	(* unary operator level in precedence hierachy *)
	and exprUn _ = maybe (trim (opr "!" || opr "-" || opr "~")) >>=
			(fn SOME "!" => exprUn() ==> (fn e => ExprUnOp {opr = UnOpNeg, expr = e})
				| SOME "-" => exprUn() ==> (fn e => ExprUnOp {opr = UnOpMinus, expr = e})
				| SOME "~" => exprUn() ==> (fn e => ExprUnOp {opr = UnOpComp, expr = e})
				| NONE => exprBase ())

	
	(* --------------------------------------------------------------------------------------------
	 * basic expressions
	 * ------------------------------------------------------------------------------------------*)

	
	(* basic excpressions *)
	and exprBase _ = "expression expected" !!
                 $"("
             >>= (fn _ => expr ()
             >>| maybe ($"->" >> expr () >>| ($":" >> expr()))
             --  $")"
             ==> (fn (e1, SOME(e2,e3)) => ExprCond {cond = e1, exprTrue = e2, exprFalse = e3}
                    | (e1, NONE) => e1))
        ||       trim identifier
             >>= (fn id => maybe ($"[" >> expr () -- $"]")
             >>= (fn e  => maybe ($"." >> varRef ())
             >>= (fn SOME v => exprVarPoll (VarRef {name = id, index = e, next = SOME v})
                   | NONE =>   exprVarPoll (VarRef {name = id, index = e, next = NONE})
                            || exprRemote id e)))
		|| trim constant ==> ExprConst
        || $$ "len" >> $"(" >>= (fn _ => varRef () -- $")" ==> ExprLen)
        || $$ "nfull" >> $"(" >>= (fn _ => varRef () -- $")" ==> ExprNFull)
        || $$ "full" >> $"(" >>= (fn _ => varRef () -- $")" ==> ExprFull)
        || $$ "nempty" >> $"(" >>= (fn _ => varRef () -- $")" ==> ExprNEmpty)
        || $$ "empty" >> $"(" >>= (fn _ => varRef () -- $")" ==> ExprEmpty)
        || $$ "timeout" ==> K ExprTimeOut
        || $$ "np_" ==> K ExprNP
        || $$ "enabled" >> $"(" >>= (fn _ => expr() -- $")" ==> ExprEnabled)
        || $$ "pc_value" >> $"(" >>= (fn _ => expr() -- $")" ==> ExprPC)
        || $$ "get_priority" >> $"(" >>= (fn _ => exprChanPoll() -- $")" ==> ExprGetPrio)
        || $$ "set_priority" >> $"(" 
                >>= (fn _ => exprChanPoll() -- $","
                >>| exprChanPoll() -- $")"
                ==> (fn (e1,e2) => ExprSetPrio {expr = e1, prio = e2}))

	(* parses variable reference and poll (needed for 1 lookahead) *)
	and exprVarPoll v = 
            $"??[" >> recvArgs() -- $"]" ==> (fn rs => ExprRndPoll {var = v, args = rs}) 
		 || $"?["  >> recvArgs() -- $"]" ==> (fn rs => ExprPoll {var = v, args = rs})
		 || return (ExprVarRef v)
	
	(* parses remote reference (needed for lookahead) *)
	and exprRemote s1 e = 
            $"@" >> identifier
            ==> (fn s2 => ExprRemoteRef {name = s1, num = e, label = s2})


	(* --------------------------------------------------------------------------------------------
	 * chan poll expressions
	 * ------------------------------------------------------------------------------------------*)

	
	(* top level chan poll expression *)
	and exprChanPoll _ = exprChanPollOr ()
	
	and exprChanPollOr _ = exprSimple "||" BinOpOr exprChanPollAnd
	and exprChanPollAnd _ = exprSimple "&&" BinOpAnd exprChanPollBase
	
    (* base level in precedence hierachy *)
	and exprChanPollBase _ = "chan expression expected" !!
			$"(" >> exprChanPoll() -- $")"
         || $$ "full" >> $"(" >> varRef() -- $")" ==> ExprFull
         || $$ "nfull" >> $"(" >> varRef() -- $")" ==> ExprNFull
         || $$ "empty" >> $"(" >> varRef() -- $")" ==> ExprEmpty
         || $$ "nempty" >> $"(" >> varRef() -- $")" ==> ExprNEmpty
		 || exprBitOr ()


	(* --------------------------------------------------------------------------------------------
	 * expression parse printer
	 * ------------------------------------------------------------------------------------------*)

			
	(* parses an expression and prints the result *)
	fun exprParsePrint s = print ((showExpr (parse (expr ()) s)) ^ "\n")
		handle (ParseException e) => print (e ^ "\n")

end;
