(* author: dennis kraft 
 *
 * parser for expressions, also includes a parser for variable references, receive arguments 
 * and priorities *)

open Basic
open Lexer
open Syntax

structure Expression : sig
	
	exception UnexhaustivePatternMatch
	
	val varRef : unit -> varRef parser
	val varArgs : unit -> (varRef list) parser
	val exprArgs : unit -> (expr list) parser
	val recvArg : unit-> recvArg parser
	val recvArgs : unit -> (recvArg list) parser 
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


	(* consumes a variable reference and returns error message in case of fail*)
	fun varRef _ = xmsg "variable reference expected" 
			(bind (trim (identifier ()))
			(fn s => bind (maybe (bind (trim (symbol [#"["]))
					(fn _ => bind (expr ())
					(fn e => bind (trim (symbol [#"]"]))
					(fn _ => return e)))))
			(fn e => bind (maybe (bind (trim (symbol [#"."])) (fn _ => varRef ())))
			(fn v => return (VarRef {name = s, index = e, next = v})))))
 
	(* consumes a list of variables *)
	and varArgs _ = sequence (trim (symbol [#","])) (varRef ())

	(* consumes a list of expressions *)		
	and exprArgs _ = sequence (trim (symbol [#","])) (expr ())

	(* consumes a receive argument and returns error message in case of fail *)
	and recvArg _ = xmsg "receive argument expected"
			(or (conv (fn v => RecvArgVar v) (varRef ()))
			(or (bind (trim (keyword [#"e",#"v",#"a",#"l"]))
			 		(fn _ => bind (bind (trim (symbol [#"("]))
							(fn _ => bind (expr ())
							(fn e => bind (trim (symbol [#")"]))
							(fn _ => return e))))
					(fn e => return (RecvArgEval e))))
			(or (bind (trim (opr [#"-"]))
					(fn _ => bind (trim (constant ()))
					(fn x => return (RecvArgConst (~x)))))
			(conv (fn x => RecvArgConst x) (trim (constant ()))))))

	(* consumes a list of receive arguments *)		
	and recvArgs _ = 
		let
			fun p () = or (bind (trim (symbol [#"("]))
					(fn _ => bind (sequence (trim (symbol [#","])) (recvArg ()))
					(fn rs => bind (trim (symbol [#")"]))
					(fn _ => return rs))))
				(list (bind (trim (symbol [#","])) (fn _ => recvArg ())))
		in
			bind (recvArg ()) (fn r => bind (p ()) (fn rs => return (r :: rs)))
		end

	(* consumes a priority *)	
	and priority _ = bind (trim (keyword [#"p", #"r", #"i", #"o", #"r", #"i", #"t", #"y"]))
			(fn _ => trim (constant ()))


	(* --------------------------------------------------------------------------------------------
	 * operator precedence hierarchy
	 * ------------------------------------------------------------------------------------------*)

	
	(* consumes an expression *)
	and expr _ = exprOr ()
	
	(* or level in precedence hierachy *)
	and exprOr _ = bind (exprAnd ())
			(fn e => bind (list (bind (trim (opr [#"|", #"|"])) (fn _ => exprAnd ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpOr, exprLeft = e2, exprRight = e1}) e es)))

	(* and level in precedence hierachy *)
	and exprAnd _ = bind (exprBitOr ())
			(fn e => bind (list (bind (trim (opr [#"&", #"&"])) (fn _ => exprBitOr ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpAnd, exprLeft = e2, exprRight = e1}) e es)))
	
	(* bit or level in precedence hierachy *)
	and exprBitOr _ = bind (exprBitXor ())
			(fn e => bind (list (bind (trim (opr [#"|"])) (fn _ => exprBitXor ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpBitOr, exprLeft = e2, exprRight = e1}) e es)))

	(* bit xor level in precedence hierachy *)
	and exprBitXor _ = bind (exprBitAnd ())
			(fn e => bind (list (bind (trim (opr [#"^"])) (fn _ => exprBitAnd ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpBitXor, exprLeft = e2, exprRight = e1}) e es)))

	(* bit and level in precedence hierachy *)
	and exprBitAnd _ = bind (exprEq ())
			(fn e => bind (list (bind (trim (opr [#"&"])) (fn _ => exprEq ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpBitAnd, exprLeft = e2, exprRight = e1}) e es)))

	(* equality level in precedence hierachy *)
	and exprEq _ =
		let
			fun myfold e [] = e
				| myfold e1 (([#"=", #"="], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpEq, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#"!", #"="], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpNEq, exprLeft = e1, exprRight = e2}) es
				| myfold _ _ = raise UnexhaustivePatternMatch
		in
			bind (exprInEq ())
					(fn e => bind (list (bind (trim (or (opr [#"=", #"="]) (opr [#"!", #"="])))
							(fn cs => bind (exprInEq ())
							(fn e => return (cs, e)))))
					(fn ces => return (myfold e ces)))
		end
					
	(* inequality level in precedence hierachy *)
	and exprInEq _ =
		let
			fun myfold e [] = e
				| myfold e1 (([#"<"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpLe, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#"<", #"="], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpLEq, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#">", #"="], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpGEq, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#">"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpGr, exprLeft = e1, exprRight = e2}) es
				| myfold _ _ = raise UnexhaustivePatternMatch
		in
			bind (exprShift ())
					(fn e => bind (list (bind (trim (or (opr [#"<"]) 
									(or (opr [#"<", #"="])
									(or (opr [#">", #"="])
									(opr [#">"])))))
							(fn cs => bind (exprShift ())
							(fn e => return (cs, e)))))
					(fn ces => return (myfold e ces)))
		end

	(* shift level in precedence hierachy *)
	and exprShift _ =
		let
			fun myfold e [] = e
				| myfold e1 (([#"<", #"<"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpShiftL, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#">", #">"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpShiftR, exprLeft = e1, exprRight = e2}) es
				| myfold _ _ = raise UnexhaustivePatternMatch
		in
			bind (exprAdd ())
					(fn e => bind (list (bind (trim (or (opr [#"<", #"<"]) (opr [#">", #">"])))
							(fn cs => bind (exprAdd ())
							(fn e => return (cs, e)))))
					(fn ces => return (myfold e ces)))
		end

	(* add level in precedence hierachy *)
	and exprAdd _ =
		let
			fun myfold e [] = e
				| myfold e1 (([#"+"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpAdd, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#"-"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpSub, exprLeft = e1, exprRight = e2}) es
				| myfold _ _ = raise UnexhaustivePatternMatch
		in
			bind (exprMul ())
					(fn e => bind (list (bind (trim (or (opr [#"+"]) (opr [#"-"])))
							(fn cs => bind (exprMul ())
							(fn e => return (cs, e)))))
					(fn ces => return (myfold e ces)))
		end
		
	(* inequality level in precedence hierachy *)
	and exprMul _ =
		let
			fun myfold e [] = e
				| myfold e1 (([#"*"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpMul, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#"/"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpDiv, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#"%"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpMod, exprLeft = e1, exprRight = e2}) es
				| myfold _ _ = raise UnexhaustivePatternMatch
		in
			bind (exprUn ())
					(fn e => bind (list (bind (trim (or (opr [#"*"]) 
									(or (opr [#"/"])
									(opr [#"%"]))))
							(fn cs => bind (exprUn ())
							(fn e => return (cs, e)))))
					(fn ces => return (myfold e ces)))
		end	
	
	(* unary operator level in precedence hierachy *)
	and exprUn _ = bind (maybe (trim (or (opr [#"!"]) (or (opr [#"-"]) (opr [#"~"])))))
			(fn SOME [#"!"] => conv (fn e => ExprUnOp {opr = UnOpNeg, expr = e}) (exprUn ())
				| SOME [#"-"] => conv (fn e => ExprUnOp {opr = UnOpMinus, expr = e}) (exprUn ())
				| SOME [#"~"] => conv (fn e => ExprUnOp {opr = UnOpComp, expr = e}) (exprUn ())
				| NONE => exprBase ()
				| _ => raise UnexhaustivePatternMatch)

	
	(* --------------------------------------------------------------------------------------------
	 * basic expressions
	 * ------------------------------------------------------------------------------------------*)

	
	(* basic excpressions *)
	and exprBase _ = xmsg "expression expected"
			(or (bind (trim (symbol [#"("]))
					(fn _ => bind (expr ())
					(fn e1 => bind (maybe (bind (trim (symbol [#"-",#">"]))
							(fn _ => bind (expr ())
							(fn e2 => bind (trim (symbol [#":"]))
							(fn _ => bind (expr ())
							(fn e3 => return (e2, e3)))))))
					(fn SOME (e2, e3) => bind (trim (symbol [#")"]))
							(fn _ => return (ExprCond {cond = e1,exprTrue = e2,exprFalse = e3}))
						| NONE => bind (trim (symbol [#")"]))
							(fn _ => return e1)))))
			(or (bind (trim (identifier ()))
					(fn s => bind (maybe (bind (trim (symbol [#"["])) 
							(fn _ => bind (expr ())
							(fn e => bind (trim (symbol [#"]"]))
							(fn _ => return e)))))
					(fn e => bind (maybe (bind (trim (symbol [#"."])) (fn _ => varRef ())))
					(fn SOME v => exprVarPoll (VarRef {name = s, index = e, next = SOME v})
					 	| NONE => or (exprVarPoll (VarRef {name = s, index = e, next = NONE})) 
								(exprRemote s e)))))
			(or (conv (fn x => ExprConst x) (trim (constant ())))
			(or (bind (trim (keyword [#"l", #"e", #"n"]))
					(fn _ => bind (trim (symbol [#"("])) 
					(fn _ => bind (varRef ())
					(fn v => bind (trim (symbol [#")"])) 
					(fn _ => return (ExprLen v))))))
			(or (bind (trim (keyword [#"n", #"f", #"u", #"l", #"l"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (varRef ())
					(fn v => bind (trim (symbol [#")"])) 
					(fn _ => return (ExprNFull v))))))
			(or (bind (trim (keyword [#"f", #"u", #"l", #"l"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (varRef ())
					(fn v => bind (trim (symbol [#")"])) 
					(fn _ => return (ExprFull v))))))
			(or (bind (trim (keyword [#"n", #"e", #"m", #"p", #"t", #"y"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (varRef ())
					(fn v => bind (trim (symbol [#")"])) 
					(fn _ => return (ExprNEmpty v))))))
			(or (bind (trim (keyword [#"e", #"m", #"p", #"t", #"y"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (varRef ())
					(fn v => bind (trim (symbol [#")"])) 
					(fn _ => return (ExprEmpty v))))))
			(or (conv (fn _ => ExprTimeOut) 
					(trim (keyword [#"t", #"i", #"m", #"e", #"o", #"u", #"t"])))
			(or (conv (fn _ => ExprNP) (trim (keyword [#"n", #"p", #"_"])))
			(or (bind (trim (keyword [#"e", #"n", #"a", #"b", #"l", #"e", #"d"]))
					(fn _ => bind (trim (symbol [#"("])) 
					(fn _ => bind (expr ())
					(fn e => bind (trim (symbol [#")"])) 
					(fn _ => return (ExprEnabled e))))))
			(or (bind (trim (keyword [#"p", #"c", #"_", #"v", #"a", #"l", #"u", #"e"]))
					(fn _ => bind (trim (symbol [#"("])) 
					(fn _ => bind (expr ())
					(fn e => bind (trim (symbol [#")"])) 
					(fn _ => return (ExprPC e))))))
			(or (bind (trim (keyword [#"g", #"e", #"t", #"_", 
							#"p", #"r", #"i", #"o", #"r", #"i", #"t", #"y"]))
					(fn _ => bind (trim (symbol [#"("])) 
					(fn _ => bind (exprChanPoll ())
					(fn e => bind (trim (symbol [#")"])) 
					(fn _ => return (ExprGetPrio e))))))
			(bind (trim (keyword [#"s", #"e", #"t", #"_", 
							#"p", #"r", #"i", #"o", #"r", #"i", #"t", #"y"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (exprChanPoll ())
					(fn e1 => bind (trim (symbol [#","]))
					(fn _ => bind (exprChanPoll ())
					(fn e2 => bind (trim (symbol [#")"]))
					(fn _ => return (ExprSetPrio {expr = e1, prio = e2}))))))))
			)))))))))))))

	(* parses variable reference and poll (needed for 1 lookahead) *)
	and exprVarPoll v = or (bind (trim (symbol [#"?", #"?", #"["])) 
					(fn _ => bind (recvArgs ())
					(fn rs => bind (trim (symbol [#"]"]))
					(fn _ => return (ExprRndPoll {var = v, args = rs})))))
			(or (bind (trim (symbol [#"?", #"["])) 
					(fn _ => bind (recvArgs ())
					(fn rs => bind (trim (symbol [#"]"]))
					(fn _ => return (ExprPoll {var = v, args = rs})))))
			(return (ExprVarRef v)))
	
	(* parses remote reference (needed for lookahead) *)
	and exprRemote s1 e = bind (trim (symbol [#"@"]))
			(fn _ => bind (trim (identifier ()))
			(fn s2 => return (ExprRemoteRef {name = s1, num = e, label = s2})))


	(* --------------------------------------------------------------------------------------------
	 * chan poll expressions
	 * ------------------------------------------------------------------------------------------*)

	
	(* top level chan poll expression *)
	and exprChanPoll _ = exprChanPollOr ()
	
	(* or level in precedence hierachy *)
	and exprChanPollOr _ = bind (exprChanPollAnd ())
			(fn e => bind (list (bind (trim (opr [#"|", #"|"])) (fn _ => exprChanPollAnd ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpOr, exprLeft = e1, exprRight = e2}) e es)))
					
	(* or level in precedence hierachy *)
	and exprChanPollAnd _ = bind (exprChanPollBase ())
			(fn e => bind (list (bind (trim (opr [#"&", #"&"])) (fn _ => exprChanPollBase ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpAnd, exprLeft = e1, exprRight = e2}) e es)))
	
	(* base level in precedence hierachy *)
	and exprChanPollBase _ = xmsg "chan expression expected"
			(or (bind (trim (symbol [#"("])) 
					(fn _ => bind (exprChanPoll ())
					(fn e => bind (trim (symbol [#")"]))
					(fn _ => return e))))
			(or (bind (trim (keyword [#"f", #"u", #"l", #"l"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (varRef ())
					(fn v => bind (trim (symbol [#")"]))
					(fn _ => return (ExprFull v))))))
			(or (bind (trim (keyword [#"e", #"m", #"p", #"t", #"y"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (varRef ())
					(fn v => bind (trim (symbol [#")"]))
					(fn _ => return (ExprFull v))))))
			(or (bind (trim (keyword [#"n", #"f", #"u", #"l", #"l"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (varRef ())
					(fn v => bind (trim (symbol [#")"]))
					(fn _ => return (ExprFull v))))))
			(or (bind (trim (keyword [#"n", #"e", #"m", #"p", #"t", #"y"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (varRef ())
					(fn v => bind (trim (symbol [#")"]))
					(fn _ => return (ExprFull v))))))
			(exprBitOr ()))))))


	(* --------------------------------------------------------------------------------------------
	 * expression parse printer
	 * ------------------------------------------------------------------------------------------*)

			
	(* parses an expression and prints the result *)
	fun exprParsePrint s = print ((showExpr (parse (expr ()) s)) ^ "\n")
		handle (ParseException e) => print (e ^ "\n")

end;
