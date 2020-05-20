(* author: dennis kraft 
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
	
	val stmnt : unit -> stmnt parser
	
	val stmntParsePrint : string -> unit
	
end = struct


	(* --------------------------------------------------------------------------------------------
 	 * various parsers
 	 * ------------------------------------------------------------------------------------------*)


	(* consumes a list of expressions in the form of send arguments *)
	fun sendArgs _ = bind (expr ())
			(fn e => bind (or (bind (trim (symbol [#"("]))
							(fn _ => bind (expr ())
							(fn e => bind (list (bind (trim (symbol [#","])) (fn _ => expr ())))
							(fn es => bind (trim (symbol [#")"]))
							(fn _ => return (e :: es))))))
					(list (bind (trim (symbol [#","])) (fn _ => expr ()))))
			(fn es => return (e :: es)))

	(* consumes a range *)
	and range _ = bind (varRef ())
			(fn v1 => or (bind (trim (symbol [#":"]))
							(fn _ => bind (expr ())
							(fn e1 => bind (trim (symbol [#".", #"."]))
							(fn _ => bind (expr ())
							(fn e2 => return (RangeFromTo {var = v1, from = e1, to = e2}))))))
					(bind (trim (keyword [#"i", #"n"]))
							(fn _ => bind (varRef())
							(fn v2 => return (RangeIn {var = v1, inside = v2})))))
	
	(* consumes a sequence of steps*)						
	and seq _ = bind (step ())
			(fn sp => bind (list (bind (or (trim (symbol [#"-", #">"]))
							(jump (trim (symbol [#";"])))) (fn _ => step ())))
			(* allow an extra ';' at end of sequence *)
			(fn sps => bind (maybe (trim (symbol [#";"])))
			(fn _ => return (sp :: sps))))
			
	(* consumes a sequence of options *)						
	and opts _ = bind (list (bind (trim (symbol [#":", #":"])) (fn _ => seq ())))
		(fn nil => fail "options expected"
			| spss => return spss)


	(* --------------------------------------------------------------------------------------------
	 * declaration parsers
	 * ------------------------------------------------------------------------------------------*)


	(* consumes a declaration and returns error message in case of fail *)
	and decl b = xmsg "variable type expected"
			(or (bind (numVarType ())
					(fn t => bind (numDecl ())
					(fn d => bind (list (bind (trim (symbol [#","])) (fn _ => numDecl ())))
					(fn ds => return (Decl {vis = b, sort = t, decl = (d :: ds)})))))
			(or (bind (trim (keyword [#"c", #"h", #"a", #"n"]))
					(fn _ => bind (chanDecl ())
					(fn d => bind (list (bind (trim (symbol [#","])) (fn _ => chanDecl ())))
					(fn ds => return (Decl {vis = b, sort = VarTypeChan, decl = (d :: ds)})))))
			(or (bind (trim (keyword [#"u", #"n", #"s", #"i", #"g", #"n", #"e", #"d"]))
					(fn _ => bind (unsignedDecl ())
					(fn d => bind (list (bind (trim (symbol [#","])) (fn _ => unsignedDecl ())))
					(fn ds => return (Decl {vis = b, sort = VarTypeUnsigned, decl = (d :: ds)})))))
			(bind (trim (keyword [#"m", #"t", #"y", #"p", #"e"]))
					(fn _ => bind (mtypeDecl ())
					(fn d => bind (list (bind (trim (symbol [#","])) (fn _ => mtypeDecl ())))
					(fn ds => return (Decl {vis = b, sort = VarTypeMType, decl = (d :: ds)}))))))))
					
	(* consumes a user defined variable declaration *)
	and udecl b s = bind (numDecl ())
			(fn d => bind (list (bind (trim (symbol [#","])) (fn _ => numDecl ())))
			(fn ds => return (Decl {vis = b, sort = VarTypeCustom s, decl = (d :: ds)})))
	
	(* consumes a declaration of a numerical variable *)
	and numDecl _ = bind (trim (identifier ()))
			(fn s => bind (maybe (bind (trim (symbol [#"["]))
					(fn _ => bind (constant ())
					(fn x => bind (trim (symbol [#"]"]))
					(fn _ => return x)))))
			(fn x => bind (maybe (bind (trim (symbol [#"="]))
					(fn _ => expr ())))
			(fn e => return (VarDeclNum {name = s, size = x, init = e}))))
	
	(* consumes a declaration of a channel variable *)
	and chanDecl _ = bind (trim (identifier ()))
			(fn s => bind (maybe (bind (trim (symbol [#"["]))
					(fn _ => bind (constant ())
					(fn x => bind (trim (symbol [#"]"]))
					(fn _ => return x)))))
			(fn x => bind (maybe (bind (trim (symbol [#"="]))
					(fn _ => bind (trim (symbol [#"["]))
					(fn _ => bind (constant ())
					(fn x => bind (trim (symbol [#"]"]))
					(fn _ => bind (trim (keyword [#"o", #"f"]))
					(fn _ => bind (trim (symbol [#"{"]))
					(fn _ => bind (varType ())
					(fn t => bind (list (bind (trim (symbol [#","])) (fn _ => varType ())))
					(fn ts => bind (trim (symbol [#"}"]))
					(fn _ => return (x, (t :: ts)))))))))))))
			(fn xts => return (VarDeclChan {name = s, size = x, capacityTypes = xts}))))

	(* consumes a declaration of an unsigned varaible *)
	and unsignedDecl _ = bind (trim (identifier ()))
			(fn s => bind (trim (symbol [#":"]))
			(fn _ => bind (trim (constant ()))
			(fn x => bind (maybe (bind (trim (symbol [#"="]))
					(fn _ => expr ())))
			(fn e => return (VarDeclUnsigned {name = s, bits = x, init = e})))))
			
	(* consumes a declaration of a numerical varaible *)
	and mtypeDecl _ = bind (trim (identifier ()))
			(fn s1 => bind (maybe (bind (trim (symbol [#"["]))
					(fn _ => bind (constant ())
					(fn x => bind (trim (symbol [#"]"]))
					(fn _ => return x)))))
			(fn x => bind (maybe (bind (trim (symbol [#"="]))
					(fn _ => trim (identifier ()))))
			(fn s2 => return (VarDeclMType {name = s1, size = x, init = s2}))))
			
	(* consumes a variable type and returns an error message in case of fail *)
	and varType _ = xmsg ("variable type expected")
			(trim (or (conv (fn _ => VarTypeBit) (keyword [#"b", #"i", #"t"])) 
			(or (conv (fn _ => VarTypeBool) (keyword [#"b", #"o", #"o", #"l"]))
			(or (conv (fn _ => VarTypeByte) (keyword [#"b", #"y", #"t", #"e"]))
			(or (conv (fn _ => VarTypePid) (keyword [#"p", #"i", #"d"]))
			(or (conv (fn _ => VarTypeShort) (keyword [#"s", #"h", #"o", #"r", #"t"]))
			(or (conv (fn _ => VarTypeInt) (keyword [#"i", #"n", #"t"])) 
			(or (conv (fn _ => VarTypeMType) (keyword [#"m", #"t", #"y", #"p", #"e"]))
			(or (conv (fn _ => VarTypeChan) (keyword [#"c", #"h", #"a", #"n"]))
			(conv (fn s => VarTypeCustom s) (identifier ())))))))))))

	(* consumes a numeral variable type and returns an error message in case of fail *)
	and numVarType _ = xmsg ("numeral variable type expected")
			(trim (or (conv (fn _ => VarTypeBit) (keyword [#"b", #"i", #"t"])) 
			(or (conv (fn _ => VarTypeBool) (keyword [#"b", #"o", #"o", #"l"]))
			(or (conv (fn _ => VarTypeByte) (keyword [#"b", #"y", #"t", #"e"]))
			(or (conv (fn _ => VarTypePid) (keyword [#"p", #"i", #"d"]))
			(or (conv (fn _ => VarTypeShort) (keyword [#"s", #"h", #"o", #"r", #"t"]))
			(conv (fn _ => VarTypeInt) (keyword [#"i", #"n", #"t"]))))))))


	(* --------------------------------------------------------------------------------------------
	 * step parser
	 * ------------------------------------------------------------------------------------------*)


	(* consumes a step and returns an error message in case of fail *)
	and step _ = xmsg ("step expected")
			(or (bind (or (conv (fn _ => SOME false) 
									(trim (keyword [#"h", #"i", #"d", #"d", #"e", #"n"])))
							(or (conv (fn _ => SOME true) 
									(trim (keyword [#"s", #"h", #"o", #"w"])))
							(return NONE)))
					(fn SOME b => or (conv (fn d => StepDecl d) (decl (SOME b)))
							(bind (trim (identifier ()))
									(fn s => (conv (fn d => StepDecl d) (udecl (SOME b) s))))
						| NONE => or (conv (fn d => StepDecl d) (decl NONE))
							(bind (trim (identifier ()))
									(fn s => or (conv (fn d => StepDecl d) (udecl NONE s))
											(bind (stmntSRALE s)
													(fn st1 => bind (maybe (bind (trim (keyword 
															[#"u", #"n", #"l", #"e", #"s", #"s"]))
															(fn _ => stmnt())))
													(fn st2 => return (StepStmnt 
															{stmnt = st1, unless = st2}))))))))
			(or (bind (stmnt ())
					(fn st1 => bind (maybe (bind (trim (keyword 
							[#"u", #"n", #"l", #"e", #"s", #"s"])) (fn _ => stmnt())))
					(fn st2 => return (StepStmnt {stmnt = st1, unless = st2}))))
			(or (bind (trim (keyword [#"x", #"r"]))
					(fn _ => bind (varRef ())
					(fn v => bind (list (bind (trim (symbol [#","])) (fn _ => varRef ())))
					(fn vs => return (StepXR (v :: vs))))))
			(bind (trim (keyword [#"x", #"s"]))
					(fn _ => bind (varRef ())
					(fn v => bind (list (bind (trim (symbol [#","])) (fn _ => varRef ())))
					(fn vs => return (StepXS (v :: vs)))))))))
				

	(* --------------------------------------------------------------------------------------------
	 * statement parsers
	 * ------------------------------------------------------------------------------------------*)

	(* consumes a statement and returns an error message in case of fail *)
	and stmnt _ = xmsg "statement expected"
			(or (bind (trim (identifier ())) (fn s => stmntSRALE s))
			(or (bind (trim (keyword [#"i", #"f"]))
					(fn _ => bind (opts ())
					(fn spss => bind (trim (keyword [#"f", #"i"]))
					(fn _ => return (StmntIf spss)))))
			(or (bind (trim (keyword [#"d", #"o"]))
					(fn _ => bind (opts ())
					(fn spss => bind (trim (keyword [#"o", #"d"]))
					(fn _ => return (StmntDo spss)))))
			(or (bind (trim (keyword [#"f", #"o", #"r"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (range ())
					(fn r => bind (trim (symbol [#")"]))
					(fn _ => bind (block_start())
					(fn _ => bind (seq ())
					(fn sps => bind (block_end())
					(fn _ => return (StmntFor {range = r, steps = sps})))))))))
			(or (bind (trim (keyword [#"a", #"t", #"o", #"m", #"i", #"c"]))
					(fn _ => bind (block_start())
					(fn _ => bind (seq ())
					(fn sps => bind (block_end())
					(fn _ => return (StmntAtomic sps))))))
			(or (bind (trim (keyword [#"d", #"_", #"s", #"t", #"e", #"p"]))
					(fn _ => bind (block_start())
					(fn _ => bind (seq ())
					(fn sps => bind (block_end())
					(fn _ => return (StmntDStep sps))))))
			(or (bind (trim (keyword [#"s", #"e", #"l", #"e", #"c", #"t"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (range ())
					(fn r => bind (trim (symbol [#")"]))
					(fn _ => return (StmntSelect r))))))
			(or (bind (block_start())
					(fn _ => bind (seq ())
					(fn sps => bind (block_end())
					(fn _ => return (StmntSeq sps)))))
			(or (conv (fn _ => StmntElse) (trim (keyword [#"e", #"l", #"s", #"e"])))
			(or (conv (fn _ => StmntBreak) (trim (keyword [#"b", #"r", #"e", #"a", #"k"])))
			(or (bind (trim (keyword [#"g", #"o", #"t", #"o"]))
					(fn _ => bind (trim (identifier ()))
					(fn s => return (StmntGoTo s))))
			(or (bind (trim (keyword [#"p", #"r", #"i", #"n", #"t", #"f"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (trim (string ()))
					(fn s => bind (list (bind (trim (symbol [#","])) (fn _ => expr ())))
					(fn es => bind (trim (symbol [#")"]))
					(fn _ => return (StmntPrintF {text = s, args = es})))))))
			(or (bind (trim (keyword [#"p", #"r", #"i", #"n", #"t", #"m"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (trim (identifier ()))
					(fn s => bind (trim (symbol [#")"]))
					(fn _ => return (StmntPrintM s))))))
			(or (bind (trim (keyword [#"r", #"u", #"n"]))
					(fn _ => bind (trim (identifier ()))
					(fn s => bind (trim (symbol [#"("])) 
					(fn _ => bind (or (exprArgs ()) (return nil))
					(fn es => bind (trim (symbol [#")"]))
					(fn _ => bind (maybe (priority ()))
					(fn x => return (StmntRun {name = s, args = es, prio = x}))))))))
			(or (bind (trim (keyword [#"a", #"s", #"s", #"e", #"r", #"t"]))
					(fn _ => bind (trim (symbol [#"("]))
					(fn _ => bind (trim (expr ()))
					(fn e => bind (trim (symbol [#")"]))
					(fn _ => return (StmntAssert e))))))
			(conv StmntCond (expr ())))))))))))))))))
			
	(* consumes a send, receive, assign, lable or expression statement given an initial identifier
	 * string (needed for 1 lookahead) *)
	and stmntSRALE s = bind (maybe (bind (trim (symbol [#"["]))
					(fn _ => bind (expr ())
					(fn e => bind (trim (symbol [#"]"]))
					(fn _ => return e)))))
			(fn e => bind (maybe (bind (trim (symbol [#"."])) (fn _ => varRef ())))
			(fn v => (case (e, v) of
				(NONE, NONE) => or (stmntSend s e v)
					(or (stmntRecv s e v)
					(or (stmntAssign s e v)
                    (or (stmntCall s)
					(or (conv (fn e => StmntCond e) (stmntExpr s e v))
					(stmntLabel s)))))
				| (_, _) => or (stmntSend s e v)
					(or (stmntRecv s e v)
					(or (stmntAssign s e v)
					(conv (fn e => StmntCond e) (stmntExpr s e v)))))))
			
	(* consumes a send statement given an initial variable reference (needed for 1 lookahead) *)
	and stmntSend s e v2 = 
		let
			val v1 = VarRef {name = s, index = e, next = v2} 
		in
			or (bind (trim (symbol [#"!", #"!"]))
					(fn _ => bind (sendArgs ())
					(fn es => return (StmntSortSend {var = v1, args = es}))))
			(bind (trim (symbol [#"!"]))
					(fn _ => bind (sendArgs ())
					(fn es => return (StmntSend {var = v1, args = es}))))
		end

	(* consumes a receive statement given an initial variable reference (needed for 1 lookahead) *)
	and stmntRecv s e v2 = 
		let
			val v1 = VarRef {name = s, index = e, next = v2} 
		in
			or (bind (trim (symbol [#"?", #"?", #"<"]))
					(fn _ => bind (recvArgs ())
					(fn es => bind (trim (symbol [#">"]))
					(fn _ => return (StmntRndRecvX {var = v1, args = es})))))
			(or (bind (trim (symbol [#"?", #"<"]))
					(fn _ => bind (recvArgs ())
					(fn es => bind (trim (symbol [#">"]))
					(fn _ => return (StmntRecvX {var = v1, args = es})))))
			(or (bind (trim (symbol [#"?", #"?"]))
					(fn _ => bind (recvArgs ())
					(fn es => return (StmntRndRecv {var = v1, args = es}))))
			(bind (trim (symbol [#"?"]))
					(fn _ => bind (recvArgs ())
					(fn es => return (StmntRecv {var = v1, args = es}))))))
		end
		
	(* consumes an assign statement given an initial variable reference (needed for 1 lookahead) *)
	and stmntAssign s e1 v2 = 
		let
			val v1 = VarRef {name = s, index = e1, next = v2} 
		in
			or (bind (trim (symbol [#"="]))
					(fn _ => bind (expr ())
					(fn e2 => return (StmntAssign {var = v1, expr = e2}))))
			(or (conv (fn _ => StmntIncr v1) (trim (symbol [#"+", #"+"])))
			(conv (fn _ => StmntDecr v1) (trim (symbol [#"-", #"-"]))))
		end

	(* consumes an label statement given an initial string (needed for 1 lookahead) *)
	and stmntLabel s = bind (trim (symbol [#":"]))
		(fn _ => bind (stmnt ())
		(fn st => return (StmntLabeled {name = s, stmnt = st})))

    (* consumes a call to an 'inline' macro given the macro's name (needed for 1
    * lookahead) *)
    and stmntCall s = bind (trim (symbol [#"("]))
			(fn _ => bind (or (varArgs ()) (return nil))
			(fn args => bind (trim (symbol [#")"]))
			(fn _ => return (StmntCall {name = s, args = args}))))


	(* --------------------------------------------------------------------------------------------
	 * operator precedence hierarchy for statement expressions 
	 * ------------------------------------------------------------------------------------------*)


	(* top level in precedence hierachy *)
	and stmntExpr s e v = stmntExprOr (VarRef {name = s, index = e, next = v})

	(* or level in precedence hierachy *)
	and stmntExprOr v = bind (stmntExprAnd v)
			(fn e => bind (list (bind (trim (opr [#"|", #"|"])) (fn _ => exprAnd ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpOr, exprLeft = e2, exprRight = e1}) e es)))

	(* and level in precedence hierachy *)
	and stmntExprAnd v = bind (stmntExprBitOr v)
			(fn e => bind (list (bind (trim (opr [#"&", #"&"])) (fn _ => exprBitOr ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpAnd, exprLeft = e2, exprRight = e1}) e es)))

	(* bit or level in precedence hierachy *)
	and stmntExprBitOr v = bind (stmntExprBitXor v)
			(fn e => bind (list (bind (trim (opr [#"|"])) (fn _ => exprBitXor ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpBitOr, exprLeft = e2, exprRight = e1}) e es)))

	(* bit xor level in precedence hierachy *)
	and stmntExprBitXor v = bind (stmntExprBitAnd v)
			(fn e => bind (list (bind (trim (opr [#"^"])) (fn _ => exprBitAnd ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpBitXor, exprLeft = e2, exprRight = e1}) e es)))

	(* bit and level in precedence hierachy *)
	and stmntExprBitAnd v = bind (stmntExprEq v)
			(fn e => bind (list (bind (trim (opr [#"&"])) (fn _ => exprEq ())))
			(fn es => return (foldl (fn (e1, e2) => 
					ExprBinOp {opr = BinOpBitAnd, exprLeft = e2, exprRight = e1}) e es)))

	(* equality level in precedence hierachy *)
	and stmntExprEq v =
		let
			fun myfold e [] = e
				| myfold e1 (([#"=", #"="], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpEq, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#"!", #"="], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpNEq, exprLeft = e1, exprRight = e2}) es
				| myfold _ _ = raise UnexhaustivePatternMatch
		in
			bind (stmntExprInEq v)
					(fn e => bind (list (bind (trim (or (opr [#"=", #"="]) (opr [#"!", #"="])))
							(fn cs => bind (exprInEq ())
							(fn e => return (cs, e)))))
					(fn ces => return (myfold e ces)))
		end

	(* inequality level in precedence hierachy *)
	and stmntExprInEq v =
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
			bind (stmntExprShift v)
					(fn e => bind (list (bind (trim (or (opr [#"<"]) 
									(or (opr [#"<", #"="])
									(or (opr [#">", #"="])
									(opr [#">"])))))
							(fn cs => bind (exprShift ())
							(fn e => return (cs, e)))))
					(fn ces => return (myfold e ces)))
		end

	(* shift level in precedence hierachy *)
	and stmntExprShift v =
		let
			fun myfold e [] = e
				| myfold e1 (([#"<", #"<"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpShiftL, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#">", #">"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpShiftR, exprLeft = e1, exprRight = e2}) es
				| myfold _ _ = raise UnexhaustivePatternMatch
		in
			bind (stmntExprAdd v)
					(fn e => bind (list (bind (trim (or (opr [#"<", #"<"]) (opr [#">", #">"])))
							(fn cs => bind (exprAdd ())
							(fn e => return (cs, e)))))
					(fn ces => return (myfold e ces)))
		end

	(* add level in precedence hierachy *)
	and stmntExprAdd v =
		let
			fun myfold e [] = e
				| myfold e1 (([#"+"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpAdd, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#"-"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpSub, exprLeft = e1, exprRight = e2}) es
				| myfold _ _ = raise UnexhaustivePatternMatch
		in
			bind (stmntExprMul v)
					(fn e => bind (list (bind (trim (or (opr [#"+"]) (opr [#"-"])))
							(fn cs => bind (exprMul ())
							(fn e => return (cs, e)))))
					(fn ces => return (myfold e ces)))
		end

	(* inequality level in precedence hierachy *)
	and stmntExprMul v =
		let
			fun myfold e [] = e
				| myfold e1 (([#"*"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpMul, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#"/"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpDiv, exprLeft = e1, exprRight = e2}) es
				| myfold e1 (([#"%"], e2) :: es) = 
						myfold (ExprBinOp {opr = BinOpMod, exprLeft = e1, exprRight = e2}) es
				| myfold _ _ = raise UnexhaustivePatternMatch
			fun p _ = case v of
				(VarRef {name = s, index = e, next = NONE}) => or (exprVarPoll v) (exprRemote s e)
				| other => exprVarPoll v
		in	
			bind (p ())
					(fn e => bind (list (bind (trim (or (opr [#"*"]) 
									(or (opr [#"/"])
									(opr [#"%"]))))
							(fn cs => bind (exprUn ())
							(fn e => return (cs, e)))))
					(fn ces => return (myfold e ces)))
		end	


	(* --------------------------------------------------------------------------------------------
	 * statement parse printer
	 * ------------------------------------------------------------------------------------------*)


	(* parses a statemnt and prints the result *)
	fun stmntParsePrint s = print ((showStmnt (parse (stmnt ()) s)) ^ "\n")
		handle (ParseException e) => print (e ^ "\n")

end;
