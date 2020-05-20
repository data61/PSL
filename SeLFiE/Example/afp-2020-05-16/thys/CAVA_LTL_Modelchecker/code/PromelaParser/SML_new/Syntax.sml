(* author: dennis kraft 
 *
 * data structure for storig the parsed promela program *)

structure Syntax : sig

	datatype module = ProcType of {active : (int option) option, name : string, decls : decl list
			, prio : int option, prov : expr option, seq : step list}
		| DProcType of {active : (int option) option, name : string, decls : decl list
			, prio : int option, prov : expr option, seq : step list}
		| Init of {prio : int option, seq : step list}
		| Never of step list
		| Trace of step list
		| NoTrace of step list
		| Inline of {name : string, args: string list, seq: step list}
		| TypeDef of {name : string, decls : decl list}
		| MType of string list
		| ModuDecl of decl
		| LTL of {name : string, formula : string}

	and stmnt = StmntIf of (step list) list
	   | StmntDo of (step list) list
	   | StmntFor of {range : range, steps : step list}
	   | StmntAtomic of step list
	   | StmntDStep of step list
	   | StmntSelect of range
	   | StmntSeq of step list
	   | StmntSend of {var : varRef, args : expr list}
	   | StmntSortSend of {var : varRef, args : expr list}
	   | StmntRecv of {var : varRef, args : recvArg list}
	   | StmntRndRecv of {var : varRef, args : recvArg list}
	   | StmntRecvX of {var : varRef, args : recvArg list}
	   | StmntRndRecvX of {var : varRef, args : recvArg list}
	   | StmntAssign of {var : varRef, expr : expr}
	   | StmntIncr of varRef
	   | StmntDecr of varRef
	   | StmntElse
	   | StmntBreak
	   | StmntGoTo of string
	   | StmntLabeled of {name : string, stmnt : stmnt}
	   | StmntPrintF of {text : string, args : expr list}
	   | StmntPrintM of string
	   | StmntRun of {name : string, args : expr list, prio : int option}
	   | StmntAssert of expr
	   | StmntCond of expr
	   | StmntCall of {name: string, args : varRef list}
	
	and step = StepStmnt of {stmnt : stmnt, unless : stmnt option}
	   | StepDecl of decl
	   | StepXR of varRef list
	   | StepXS of varRef list
	
	and decl = Decl of {vis : bool option, sort : varType, decl : varDecl list}
	
	and varDecl = VarDeclNum of {name : string, size : int option, init : expr option}
	   | VarDeclChan of {name : string, size : int option, 
				capacityTypes : (int * varType list) option}
	   | VarDeclUnsigned of {name : string, bits : int, init : expr option}
	   | VarDeclMType of {name : string, size : int option, init : string option}
	
	and range = RangeFromTo of {var : varRef, from : expr, to : expr}
	   | RangeIn of {var : varRef, inside : varRef}

	and varType = VarTypeBit
		| VarTypeBool
		| VarTypeByte
		| VarTypePid
		| VarTypeShort
		| VarTypeInt
		| VarTypeMType
		| VarTypeChan
		| VarTypeUnsigned
		| VarTypeCustom of string

	and expr = ExprBinOp of {opr : binOp, exprLeft : expr, exprRight : expr}
		| ExprUnOp of {opr : unOp, expr : expr}
		| ExprCond of {cond : expr, exprTrue : expr, exprFalse : expr}
		| ExprLen of varRef
		| ExprPoll of {var : varRef, args : recvArg list}
		| ExprRndPoll of {var : varRef, args : recvArg list}
		| ExprVarRef of varRef
		| ExprConst of int
		| ExprTimeOut
		| ExprNP
		| ExprEnabled of expr
		| ExprPC of expr
		| ExprRemoteRef of {name : string, num : expr option, label : string}
		| ExprGetPrio of expr
		| ExprSetPrio of {expr : expr, prio : expr} 
		| ExprFull of varRef
		| ExprEmpty of varRef
		| ExprNFull of varRef
		| ExprNEmpty of varRef

	and varRef = VarRef of {name : string, index : expr option, next : varRef option}

	and recvArg = RecvArgVar of varRef
		| RecvArgEval of expr
		| RecvArgConst of int

	and unOp = UnOpComp
		| UnOpMinus
		| UnOpNeg

	and binOp = BinOpAdd
		| BinOpSub
		| BinOpMul
		| BinOpDiv
		| BinOpMod
		| BinOpBitAnd
		| BinOpBitXor
		| BinOpBitOr
		| BinOpGr
		| BinOpLe
		| BinOpGEq
		| BinOpLEq
		| BinOpEq
		| BinOpNEq
		| BinOpShiftL
		| BinOpShiftR
		| BinOpAnd
		| BinOpOr

	val showModule : module -> string
	val showStmnt : stmnt -> string
	val showStep : step -> string
	val showDecl : decl -> string
	val showVarDecl : varDecl -> string
	val showRange : range -> string
	val showVarType : varType -> string
	val showExpr : expr -> string
	val showVarRef : varRef -> string
	val showRecvArg : recvArg -> string
	val showUnOp : unOp -> string
	val showBinOp : binOp -> string
 
end = struct
	
	(* --------------------------------------------------------------------------------------------
	 * data types
	 * ------------------------------------------------------------------------------------------*)
	
	datatype module = ProcType of {active : (int option) option, name : string, decls : decl list
			, prio : int option, prov : expr option, seq : step list}
		| DProcType of {active : (int option) option, name : string, decls : decl list
			, prio : int option, prov : expr option, seq : step list}
		| Init of {prio : int option, seq : step list}
		| Never of step list
		| Trace of step list
		| NoTrace of step list
		| Inline of {name : string, args: string list, seq: step list}
		| TypeDef of {name : string, decls : decl list}
		| MType of string list
		| ModuDecl of decl
		| LTL of {name : string, formula : string}
	
	and stmnt = StmntIf of (step list) list
	   | StmntDo of (step list) list
	   | StmntFor of {range : range, steps : step list}
	   | StmntAtomic of step list
	   | StmntDStep of step list
	   | StmntSelect of range
	   | StmntSeq of step list
	   | StmntSend of {var : varRef, args : expr list}
	   | StmntSortSend of {var : varRef, args : expr list}
	   | StmntRecv of {var : varRef, args : recvArg list}
	   | StmntRndRecv of {var : varRef, args : recvArg list}
	   | StmntRecvX of {var : varRef, args : recvArg list}
	   | StmntRndRecvX of {var : varRef, args : recvArg list}
	   | StmntAssign of {var : varRef, expr : expr}
	   | StmntIncr of varRef
	   | StmntDecr of varRef
	   | StmntElse
	   | StmntBreak
	   | StmntGoTo of string
	   | StmntLabeled of {name : string, stmnt : stmnt}
	   | StmntPrintF of {text : string, args : expr list}
	   | StmntPrintM of string
	   | StmntRun of {name : string, args : expr list, prio : int option}
	   | StmntAssert of expr
	   | StmntCond of expr
	   | StmntCall of {name: string, args : varRef list}

	and step = StepStmnt of {stmnt : stmnt, unless : stmnt option}
	   | StepDecl of decl
	   | StepXR of varRef list
	   | StepXS of varRef list

	and decl = Decl of {vis : bool option, sort : varType, decl : varDecl list}

	and varDecl = VarDeclNum of {name : string, size : int option, init : expr option}
	   | VarDeclChan of {name : string, size : int option, 
				capacityTypes : (int * varType list) option}
	   | VarDeclUnsigned of {name : string, bits : int, init : expr option}
	   | VarDeclMType of {name : string, size : int option, init : string option}

	and range = RangeFromTo of {var : varRef, from : expr, to : expr}
	   | RangeIn of {var : varRef, inside : varRef}
	
	and varType = VarTypeBit
		| VarTypeBool
		| VarTypeByte
		| VarTypePid
		| VarTypeShort
		| VarTypeInt
		| VarTypeMType
		| VarTypeChan
		| VarTypeUnsigned
		| VarTypeCustom of string

	and expr = ExprBinOp of {opr : binOp, exprLeft : expr, exprRight : expr}
		| ExprUnOp of {opr : unOp, expr : expr}
		| ExprCond of {cond : expr, exprTrue : expr, exprFalse : expr}
		| ExprLen of varRef
		| ExprPoll of {var : varRef, args : recvArg list}
		| ExprRndPoll of {var : varRef, args : recvArg list}
		| ExprVarRef of varRef
		| ExprConst of int
		| ExprTimeOut
		| ExprNP
		| ExprEnabled of expr
		| ExprPC of expr
		| ExprRemoteRef of {name : string, num : expr option, label : string}
		| ExprGetPrio of expr
		| ExprSetPrio of {expr : expr, prio : expr} 
		| ExprFull of varRef
		| ExprEmpty of varRef
		| ExprNFull of varRef
		| ExprNEmpty of varRef

	and varRef = VarRef of {name : string, index : expr option, next : varRef option}

	and recvArg = RecvArgVar of varRef
		| RecvArgEval of expr
		| RecvArgConst of int

	and unOp = UnOpComp
		| UnOpMinus
		| UnOpNeg

	and binOp = BinOpAdd
		| BinOpSub
		| BinOpMul
		| BinOpDiv
		| BinOpMod
		| BinOpBitAnd
		| BinOpBitXor
		| BinOpBitOr
		| BinOpGr
		| BinOpLe
		| BinOpGEq
		| BinOpLEq
		| BinOpEq
		| BinOpNEq
		| BinOpShiftL
		| BinOpShiftR
		| BinOpAnd
		| BinOpOr

	(* --------------------------------------------------------------------------------------------
	 * show functions
	 * ------------------------------------------------------------------------------------------*)
	
	fun showModule (ProcType {active = x1, name = s, decls = ds, prio = x2, prov = e, seq = sps}) =
			let
				fun f NONE = ""
					| f (SOME NONE) = "active "
					| f (SOME (SOME x)) = "active[" ^ Int.toString x ^ "] "
				fun g NONE = ""
					| g (SOME x) = "priority " ^ Int.toString x ^ " "
				fun h NONE = ""
					| h (SOME e) = "provided (" ^ showExpr e ^ ") "
			in
				f x1 ^ "proctype " ^ s ^ "(" ^ showDeclList ds ^ ")" ^ g x2 ^ h e ^ 
				"{" ^ showStepList sps ^ "}"
			end
		| showModule (DProcType {active = x1, name = s, decls = ds, prio = x2, prov = e, 
				seq = sps}) =
			let
				fun f NONE = ""
					| f (SOME NONE) = "active "
					| f (SOME (SOME x)) = "active[" ^ Int.toString x ^ "] "
				fun g NONE = ""
					| g (SOME x) = "priority " ^ Int.toString x ^ " "
				fun h NONE = ""
					| h (SOME e) = "provided (" ^ showExpr e ^ ") "
			in
				f x1 ^ "D_proctype " ^ s ^ "(" ^ showDeclList ds ^ ")" ^ g x2 ^ h e ^ 
				"{" ^ showStepList sps ^ "}"
			end
		| showModule (Init {prio = NONE, seq = sps}) = "init {" ^ showStepList sps ^ "}"
		| showModule (Init {prio = SOME x, seq = sps}) = "init priority " ^ Int.toString x ^
				" {" ^ showStepList sps ^ "}"
		| showModule (Never sps) = "never {" ^ showStepList sps ^ "}"
		| showModule (Trace sps) = "trace {" ^ showStepList sps ^ "}"
		| showModule (NoTrace sps) = "notrace {" ^ showStepList sps ^ "}"
		| showModule (Inline {name = s, args = args, seq = sps}) = 
				"inline " ^ s ^ "(" ^ String.concatWith ", " args ^ ") {" ^
				showStepList sps ^ "}"
		| showModule (TypeDef {name = s, decls = ds}) = "typedef " ^ s ^ 
			" {" ^ showDeclList ds ^ ")"
		| showModule (MType ss) = "mtype {" ^ String.concatWith ", " ss ^ "}"
		| showModule (ModuDecl d) = showDecl d
		| showModule (LTL {name = s1, formula = s2}) = "ltl " ^ s1 ^ " {" ^ s2 ^ "}"
		
	and showStmnt (StmntIf spss) =
			let
				fun g nil = ""
					| g (sps :: spss) = "\n:: " ^ showStepList sps ^ g spss
			in
				"if" ^ g spss ^ "\nfi"
			end
		| showStmnt (StmntDo spss) = 
			let
				fun g nil = ""
					| g (sps :: spss) = "\n:: " ^ showStepList sps ^ g spss
			in
				"do" ^ g spss ^ "\nod"
			end
		| showStmnt (StmntFor {range = r, steps = sps}) =
				"for(" ^ showRange r ^ ") {" ^ showStepList sps ^ "}"
		| showStmnt (StmntAtomic sps) = "atomic {" ^ showStepList sps ^ "}"
		| showStmnt (StmntDStep sps) = "d_step {" ^ showStepList sps ^ "}"
		| showStmnt (StmntSelect r) = "select(" ^ showRange r ^ ")"
		| showStmnt (StmntSeq sps) = "{" ^ showStepList sps ^ "}"
		| showStmnt (StmntSend {var = v, args = es}) = showVarRef v ^ " ! " ^ showExprList es
		| showStmnt (StmntSortSend {var = v, args = es}) = showVarRef v ^ " !! " ^ showExprList es
		| showStmnt (StmntRecv {var = v, args = rs}) = showVarRef v ^ " ? " ^ showRecvArgList rs
		| showStmnt (StmntRndRecv {var = v, args = rs}) 
				= showVarRef v ^ " ?? " ^ showRecvArgList rs
		| showStmnt (StmntRecvX {var = v, args = rs}) 
				= showVarRef v ^ " ? <" ^ showRecvArgList rs ^ ">"
		| showStmnt (StmntRndRecvX {var = v, args = rs}) 
				= showVarRef v ^ " ?? <" ^ showRecvArgList rs ^ ">"
		| showStmnt (StmntAssign {var = v, expr = e}) = showVarRef v ^ " = " ^ showExpr e
		| showStmnt (StmntIncr v) = showVarRef v ^ "++"
		| showStmnt (StmntDecr v) = showVarRef v ^ "--"
		| showStmnt StmntElse = "else"
		| showStmnt StmntBreak = "break"
		| showStmnt (StmntGoTo s) = "goto " ^ s
		| showStmnt (StmntLabeled {name = s, stmnt = st}) = s ^ ": " ^ showStmnt st
		| showStmnt (StmntPrintF {text = s, args = nil}) = "printf(\"" ^ s ^ "\")"
		| showStmnt (StmntPrintF {text = s, args = es}) = 
				"printf(\"" ^ s ^ "\"," ^ showExprList es ^ ")"
		| showStmnt (StmntPrintM s) = "printm(\"" ^ s ^ "\")"
		| showStmnt (StmntRun {name = s, args = es, prio = NONE}) = 
				"run " ^ s ^ "(" ^ showExprList es ^ ")"
		| showStmnt (StmntRun {name = s, args = es, prio = SOME x}) = 
				"run " ^ s ^ "(" ^ showExprList es ^ ") priority " ^ Int.toString x
		| showStmnt (StmntAssert e) = "assert(" ^ showExpr e ^ ")"
		| showStmnt (StmntCond e) = showExpr e
		| showStmnt (StmntCall {name = s, args = args}) =
				s ^ "(" ^ showVarRefList args ^ ")"
		
	and showStepList nil = ""
		| showStepList (sp :: nil) = showStep sp
		| showStepList (sp :: sps) = showStep sp ^ "; " ^ showStepList sps

	and showStep (StepStmnt {stmnt = st1, unless = NONE}) = showStmnt st1
		| showStep (StepStmnt {stmnt = st1, unless = SOME st2}) = 
				showStmnt st1 ^ " unless " ^ showStmnt st1 
		| showStep (StepDecl d) = showDecl d
		| showStep (StepXR vs) = "xr " ^ showVarRefList vs
		| showStep (StepXS vs) = "xs " ^ showVarRefList vs

	and showDeclList nil = ""
		| showDeclList (d :: nil) = showDecl d
		| showDeclList (d :: ds) = showDecl d ^ "; " ^ showDeclList ds

	and showDecl (Decl {vis = b, sort = t, decl = ds}) =
		let
			fun f NONE = ""
				| f (SOME true) = "show "
				| f (SOME false) = "hidden "
			fun g nil = ""
				| g (d :: nil) = showVarDecl d
				| g (d :: ds) = showVarDecl d ^ ", " ^ g ds
			in
				f b ^ showVarType t ^ " " ^ g ds
		end

	and showVarDecl (VarDeclNum {name = s, size = NONE, init = NONE}) = s
		| showVarDecl (VarDeclNum {name = s, size = NONE, init = SOME e}) = s ^ " = " ^ showExpr e
		| showVarDecl (VarDeclNum {name = s, size = SOME x, init = NONE}) = 
				s ^ "[" ^ Int.toString x ^ "] "
		| showVarDecl (VarDeclNum {name = s, size = SOME x, init = SOME e}) = 
				s ^ "[" ^ Int.toString x ^ "] = " ^ showExpr e
		| showVarDecl (VarDeclChan {name = s, size = NONE, capacityTypes = NONE}) = s
		| showVarDecl (VarDeclChan {name = s, size = NONE, capacityTypes = SOME (x2, ts)}) =
				s ^ " = [" ^ Int.toString x2 ^ "] of {" ^ showVarTypeList ts ^ "}"
		| showVarDecl (VarDeclChan {name = s, size = SOME x1, capacityTypes = NONE}) =
				s ^ "[" ^ Int.toString x1 ^ "]"
		| showVarDecl (VarDeclChan {name = s, size = SOME x1, capacityTypes = SOME (x2, ts)}) =
				s ^ "[" ^ Int.toString x1 ^ "] = [" ^ Int.toString x2 ^ 
				"] of {" ^ showVarTypeList ts ^ "}"
		| showVarDecl (VarDeclUnsigned {name = s, bits = x, init = NONE}) = 
				s ^ ":" ^ Int.toString x
		| showVarDecl (VarDeclUnsigned {name = s, bits = x, init = SOME e}) = 
				s ^ ":" ^ Int.toString x ^ " = " ^ showExpr e
		| showVarDecl (VarDeclMType {name = s1, size = NONE, init = NONE}) = s1
		| showVarDecl (VarDeclMType {name = s1, size = NONE, init = SOME s2}) = s1 ^ " = " ^ s2
		| showVarDecl (VarDeclMType {name = s1, size = SOME x, init = NONE}) =
				s1 ^ "[" ^ Int.toString x ^ "]"
		| showVarDecl (VarDeclMType {name = s1, size = SOME x, init = SOME s2}) =
				s1 ^ "[" ^ Int.toString x ^ "] = " ^ s2

	and showRange (RangeFromTo {var = v, from = e1, to = e2}) = 
			showVarRef v ^ ": " ^ showExpr e1 ^ " .. " ^ showExpr e2
		| showRange (RangeIn {var = v1, inside = v2}) = showVarRef v1 ^ " in " ^ showVarRef v2
	
	and showVarTypeList nil = ""
		| showVarTypeList (t :: nil) = showVarType t
		| showVarTypeList (t :: ts) = showVarType t ^ ", " ^ showVarTypeList ts

	and showVarType VarTypeBit = "bit"
		| showVarType VarTypeBool = "bool"
		| showVarType VarTypeByte = "byte"
		| showVarType VarTypePid = "pid"
		| showVarType VarTypeShort = "short"
		| showVarType VarTypeInt = "int"
		| showVarType VarTypeMType = "mtype"
		| showVarType VarTypeChan = "chan"
		| showVarType VarTypeUnsigned = "unsigned"
		| showVarType (VarTypeCustom s) = s

	and showExprList nil = ""
			| showExprList (e :: nil) = showExpr e
			| showExprList (e :: es) = showExpr e ^ ", " ^ showExprList es

	and showExpr (ExprBinOp {opr = b, exprLeft = e1, exprRight = e2}) =
			"(" ^ showExpr e1 ^ " " ^ showBinOp b ^ " " ^ showExpr e2 ^ ")"
		| showExpr (ExprUnOp {opr = u, expr = e}) = 
			"(" ^ showUnOp u ^ " " ^ showExpr e ^ ")"
		| showExpr (ExprCond {cond = e1, exprTrue = e2, exprFalse = e3}) =
			"(" ^ showExpr e1 ^ " -> " ^ showExpr e2 ^ " : " ^ showExpr e3 ^ ")"
		| showExpr (ExprLen v) = "len(" ^ showVarRef v ^ ")"
		| showExpr (ExprPoll {var = v, args = rs}) =
				showVarRef v ^ " ? [" ^ showRecvArgList rs ^ "]"
		| showExpr (ExprRndPoll {var = v, args = rs}) = 
				showVarRef v ^ " ?? [" ^ showRecvArgList rs ^ "]"
		| showExpr (ExprVarRef v) = showVarRef v
		| showExpr (ExprConst x) = Int.toString x
		| showExpr ExprTimeOut = "timeout"
		| showExpr ExprNP = "np_"
		| showExpr (ExprEnabled e) = "enabled(" ^ showExpr e ^ ")"
		| showExpr (ExprPC e) = "pc_value(" ^ showExpr e ^ ")"
		| showExpr (ExprRemoteRef {name = s1, num = NONE, label = s2}) =
				s1 ^ " @ " ^ s2
		| showExpr (ExprRemoteRef {name = s1, num = SOME e, label = s2}) =
				s1 ^ "[" ^ showExpr e ^ "] @ " ^ s2
		| showExpr (ExprGetPrio e) = "get_priority(" ^ showExpr e ^ ")"
		| showExpr (ExprSetPrio {expr = e1, prio = e2}) =
			"set_priority(" ^ showExpr e1 ^ ", " ^ showExpr e2 ^ ")"
		| showExpr (ExprFull v) = "full(" ^ showVarRef v ^ ")"
		| showExpr (ExprEmpty v) = "empty(" ^ showVarRef v ^ ")"
		| showExpr (ExprNFull v) = "nfull(" ^ showVarRef v ^ ")"
		| showExpr (ExprNEmpty v) = "nempty(" ^ showVarRef v ^ ")"

	and showVarRefList nil = ""
		| showVarRefList (v :: nil) = showVarRef v
		| showVarRefList (v :: vs) = showVarRef v ^ ", " ^ showVarRefList vs

	and showVarRef (VarRef {name = s, index = NONE, next = NONE}) = s
		| showVarRef (VarRef {name = s, index = NONE, next = SOME var}) = s ^ "." ^ showVarRef var
		| showVarRef (VarRef {name = s, index = SOME expr, next = NONE}) 
				= s ^ "[" ^ showExpr expr ^ "]"
		| showVarRef (VarRef {name = s, index = SOME expr, next = SOME var}) =
				s ^ "[" ^ showExpr expr ^ "]." ^ showVarRef var

	and showRecvArgList nil = ""
		| showRecvArgList (r :: nil) = showRecvArg r
		| showRecvArgList (r :: rs) = showRecvArg r ^ ", " ^ showRecvArgList rs

	and showRecvArg (RecvArgVar var) = showVarRef var
		| showRecvArg (RecvArgEval expr) = "eval(" ^ showExpr expr ^ ")"
		| showRecvArg (RecvArgConst x) = Int.toString x

	and showUnOp UnOpComp = "~"
		| showUnOp UnOpMinus = "-"
		| showUnOp UnOpNeg = "!"
		
	and showBinOp BinOpAdd = "+"
		| showBinOp BinOpSub = "-"
		| showBinOp BinOpMul = "*"
		| showBinOp BinOpDiv = "/"
		| showBinOp BinOpMod = "%"
		| showBinOp BinOpBitAnd = "&"
		| showBinOp BinOpBitXor = "^"
		| showBinOp BinOpBitOr = "|" 
		| showBinOp BinOpGr = ">"
		| showBinOp BinOpLe = "<"
		| showBinOp BinOpGEq = ">="
		| showBinOp BinOpLEq = "<="
		| showBinOp BinOpEq = "=="
		| showBinOp BinOpNEq = "!="
		| showBinOp BinOpShiftL = "<<"
		| showBinOp BinOpShiftR = ">>"
		| showBinOp BinOpAnd = "&&"
		| showBinOp BinOpOr = "||"
end;
