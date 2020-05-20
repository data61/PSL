(* Convert from the structure used by the parser into the one as spat out by
* Isabelle.
*
* Most notable differences: 
*   - Tuples instead of records
*   - LTL -> Ltl 
*)

signature PROMELA_SYNTAX = 
sig
    datatype module = ProcType of (*active*) (int option) option *
                                  (*name*)   string *
                                  (*decls*)  decl list *
                                  (*prio*)   int option *
                                  (*prov*)   expr option *
                                  (*seq*)    step list
        | DProcType of (*active*) (int option) option *
                       (*name*)   string *
                       (*decls*)  decl list *
                       (*prio*)   int option *
                       (*prov*)   expr option * 
                       (*seq*)    step list
        | Init of (*prio*) int option * 
                   (*seq*) step list
        | Never of step list
        | Trace of step list
        | NoTrace of step list
        | TypeDef of (*name*) string * 
                    (*decls*) decl list 
        | Inline of (*name*) string *
                    (*args*) string list *
                    (*seq*)  step list
        | MType of string list
        | ModuDecl of decl
        | Ltl of (*name*) string * 
              (*formula*) string

    and stmnt = StmntIf of (step list) list
       | StmntDo of (step list) list
       | StmntFor of (*range*) range *
                     (*steps*) step list
       | StmntAtomic of step list
       | StmntDStep of step list 
       | StmntSelect of range
       | StmntSeq of step list
       | StmntSend of (*var*) varRef *
                     (*args*) expr list
       | StmntSortSend of (*var*) varRef *
                         (*args*) expr list
       | StmntRecv of (*var*) varRef *
                     (*args*) recvArg list
       | StmntRndRecv of (*var*) varRef *
                        (*args*) recvArg list
       | StmntRecvX of (*var*) varRef *
                      (*args*) recvArg list
       | StmntRndRecvX of (*var*) varRef *
                         (*args*) recvArg list
       | StmntAssign of (*var*) varRef *
                       (*expr*) expr
       | StmntIncr of varRef
       | StmntDecr of varRef
       | StmntElse
       | StmntBreak
       | StmntGoTo of string
       | StmntLabeled of (*name*) string *
                         (*stmnt*) stmnt
       | StmntPrintF of (*text*) string *
                        (*args*) expr list
       | StmntPrintM of string
       | StmntRun of (*name*) string *
                     (*args*) expr list *
                     (*prio*) int option
       | StmntAssert of expr
       | StmntCall of (*name*) string *
                      (*args*) varRef list
       | StmntCond of expr
    
    and step = StepStmnt of (*stmnt*) stmnt * 
                            (*unless*) stmnt option
       | StepDecl of decl
       | StepXR of varRef list
       | StepXS of varRef list
    
    and decl = Decl of (*vis*) bool option *
                       (*sort*) varType *
                       (*decl*) varDecl list
    
    and varDecl = VarDeclNum of (*name*) string *
                                (*size*) int option *
                                (*init*) expr option
       | VarDeclChan of (*name*) string *
                        (*size*) int option *
               (*capacityTypes*) (int * varType list) option
       | VarDeclUnsigned of (*name*) string *
                            (*bits*) int *
                            (*init*) expr option
       | VarDeclMType of (*name*) string *
                         (*size*) int option *
                         (*init*) string option
    
    and range = RangeFromTo of (*var*) varRef *
                              (*from*) expr *
                               (*to*)  expr
       | RangeIn of (*var*) varRef *
                 (*inside*) varRef

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

    and expr = ExprBinOp of (*opr*) binOp *
                       (*exprLeft*) expr *
                      (*exprRight*) expr
        | ExprUnOp of (*opr*) unOp *
                     (*expr*) expr
        | ExprCond of (*cond*) expr *
                  (*exprTrue*) expr *
                 (*exprFalse*) expr
        | ExprLen of varRef
        | ExprPoll of (*var*) varRef *
                     (*args*) recvArg list
        | ExprRndPoll of (*var*) varRef *
                        (*args*) recvArg list
        | ExprVarRef of varRef
        | ExprConst of int
        | ExprTimeOut
        | ExprNP
        | ExprEnabled of expr
        | ExprPC of expr
        | ExprRemoteRef of (*name*) string *
                            (*num*) expr option *
                          (*label*) string
        | ExprGetPrio of expr
        | ExprSetPrio of (*expr*) expr *
                         (*prio*) expr
        | ExprFull of varRef
        | ExprEmpty of varRef
        | ExprNFull of varRef
        | ExprNEmpty of varRef

    and varRef = VarRef of (*name*) string *
                          (*index*) expr option *
                           (*next*) varRef option

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
end

functor SyntaxConverter (PS : PROMELA_SYNTAX): sig
  val convert : Syntax.module -> PS.module

  val convertBinOp : Syntax.binOp -> PS.binOp
  val convertUnOp : Syntax.unOp -> PS.unOp
  val convertRecvArg : Syntax.recvArg -> PS.recvArg
  val convertVarRef : Syntax.varRef -> PS.varRef
  val convertExpr : Syntax.expr -> PS.expr
  val convertVarType : Syntax.varType -> PS.varType
  val convertRange : Syntax.range -> PS.range
  val convertVarDecl : Syntax.varDecl -> PS.varDecl
  val convertDecl : Syntax.decl -> PS.decl
  val convertStep : Syntax.step -> PS.step
  val convertStmnt : Syntax.stmnt -> PS.stmnt
end = struct
  open PS
  structure S = Syntax

  fun convertBinOp S.BinOpAdd = BinOpAdd
    | convertBinOp S.BinOpSub = BinOpSub
    | convertBinOp S.BinOpMul = BinOpMul
    | convertBinOp S.BinOpDiv = BinOpDiv
    | convertBinOp S.BinOpMod = BinOpMod
    | convertBinOp S.BinOpBitAnd = BinOpBitAnd
    | convertBinOp S.BinOpBitXor = BinOpBitXor
    | convertBinOp S.BinOpBitOr = BinOpBitOr
    | convertBinOp S.BinOpGr = BinOpGr
    | convertBinOp S.BinOpLe = BinOpLe
    | convertBinOp S.BinOpGEq = BinOpGEq
    | convertBinOp S.BinOpLEq = BinOpLEq
    | convertBinOp S.BinOpEq = BinOpEq
    | convertBinOp S.BinOpNEq = BinOpNEq
    | convertBinOp S.BinOpShiftL = BinOpShiftL
    | convertBinOp S.BinOpShiftR = BinOpShiftR
    | convertBinOp S.BinOpAnd = BinOpAnd
    | convertBinOp S.BinOpOr = BinOpOr

  fun convertUnOp S.UnOpComp = UnOpComp
    | convertUnOp S.UnOpMinus = UnOpMinus
    | convertUnOp S.UnOpNeg = UnOpNeg

  fun convertRecvArg (S.RecvArgVar vr) = RecvArgVar (convertVarRef vr)
    | convertRecvArg (S.RecvArgEval e) =  RecvArgEval (convertExpr e)
    | convertRecvArg (S.RecvArgConst i) = RecvArgConst i

  and convertVarRef (S.VarRef {name = n, index = i, next = x}) = 
    VarRef (n, Option.map convertExpr i, Option.map convertVarRef x)

  and convertExpr (S.ExprBinOp {opr = opr, exprLeft = exprL, exprRight = exprR})
    = ExprBinOp (convertBinOp opr, convertExpr exprL, convertExpr exprR)
    | convertExpr (S.ExprUnOp {opr = opr, expr = expr})
    = ExprUnOp (convertUnOp opr, convertExpr expr)
    | convertExpr (S.ExprCond {cond = cond, exprTrue = exprT, exprFalse = exprF})
    = ExprCond (convertExpr cond, convertExpr exprT, convertExpr exprF)
    | convertExpr (S.ExprLen varRef) = ExprLen (convertVarRef varRef)
    | convertExpr (S.ExprPoll {var = var, args = args})
    = ExprPoll (convertVarRef var, List.map convertRecvArg args)
    | convertExpr (S.ExprRndPoll {var = var, args = args})
    = ExprRndPoll (convertVarRef var, List.map convertRecvArg args)
    | convertExpr (S.ExprVarRef varRef) = ExprVarRef (convertVarRef varRef)
    | convertExpr (S.ExprConst i) = ExprConst i
    | convertExpr S.ExprTimeOut = ExprTimeOut
    | convertExpr S.ExprNP = ExprNP
    | convertExpr (S.ExprEnabled expr) = ExprEnabled (convertExpr expr)
    | convertExpr (S.ExprPC expr) = ExprPC (convertExpr expr)
    | convertExpr (S.ExprRemoteRef {name = name, num = num, label = label})
    = ExprRemoteRef (name, Option.map convertExpr num, label)
    | convertExpr (S.ExprGetPrio expr) = ExprGetPrio (convertExpr expr)
    | convertExpr (S.ExprSetPrio { expr = e, prio = p })
    = ExprSetPrio (convertExpr e, convertExpr p)
    | convertExpr (S.ExprFull varRef) = ExprFull (convertVarRef varRef)
    | convertExpr (S.ExprEmpty varRef) = ExprEmpty (convertVarRef varRef)
    | convertExpr (S.ExprNFull varRef) = ExprNFull (convertVarRef varRef)
    | convertExpr (S.ExprNEmpty varRef) = ExprNEmpty (convertVarRef varRef)

  fun convertVarType S.VarTypeBit = VarTypeBit
    | convertVarType S.VarTypeBool = VarTypeBool
    | convertVarType S.VarTypeByte = VarTypeByte
    | convertVarType S.VarTypePid = VarTypePid
    | convertVarType S.VarTypeShort = VarTypeShort
    | convertVarType S.VarTypeInt = VarTypeInt
    | convertVarType S.VarTypeMType = VarTypeMType
    | convertVarType S.VarTypeChan = VarTypeChan
    | convertVarType S.VarTypeUnsigned = VarTypeUnsigned
    | convertVarType (S.VarTypeCustom c) = VarTypeCustom c

  fun convertRange (S.RangeFromTo {var = var, from = from, to = to})
    = RangeFromTo (convertVarRef var, convertExpr from, convertExpr to)
    | convertRange (S.RangeIn {var = var, inside = inside})
    = RangeIn (convertVarRef var, convertVarRef inside)

  fun convertVarDecl (S.VarDeclNum {name = n, size = s, init = i})
    = VarDeclNum (n, s, Option.map convertExpr i)
    | convertVarDecl (S.VarDeclChan {name = n, size = s, capacityTypes = cs})
    = VarDeclChan (n, s, Option.map (fn (i,vs) => (i, List.map convertVarType vs)) cs)
    | convertVarDecl (S.VarDeclUnsigned {name = n, bits = b, init = i})
    = VarDeclUnsigned (n, b, Option.map convertExpr i)
    | convertVarDecl (S.VarDeclMType {name = n, size = s, init = i})
    = VarDeclMType (n, s, i)

  fun convertDecl (S.Decl {vis = vis, sort = s, decl = ds})
    = Decl (vis, convertVarType s, List.map convertVarDecl ds)

  fun convertStep (S.StepStmnt {stmnt = s, unless = u})
    = StepStmnt (convertStmnt s, Option.map convertStmnt u)
    | convertStep (S.StepDecl d) = StepDecl (convertDecl d)
    | convertStep (S.StepXR vs) = StepXR (List.map convertVarRef vs)
    | convertStep (S.StepXS vs) = StepXS (List.map convertVarRef vs)
  
  and convertStmnt (S.StmntIf sss) = StmntIf (List.map (List.map convertStep) sss)
    | convertStmnt (S.StmntDo sss) = StmntDo (List.map (List.map convertStep) sss)
    | convertStmnt (S.StmntFor {range = r, steps = ss})
    = StmntFor (convertRange r, List.map convertStep ss)
    | convertStmnt (S.StmntAtomic ss) = StmntAtomic (List.map convertStep ss)
    | convertStmnt (S.StmntDStep ss) = StmntDStep (List.map convertStep ss)
    | convertStmnt (S.StmntSelect r) = StmntSelect (convertRange r)
    | convertStmnt (S.StmntSeq ss) = StmntSeq (List.map convertStep ss)
    | convertStmnt (S.StmntSend {var = v, args = args})
    = StmntSend (convertVarRef v, List.map convertExpr args)
    | convertStmnt (S.StmntSortSend {var = v, args = args})
    = StmntSortSend (convertVarRef v, List.map convertExpr args)
    | convertStmnt (S.StmntRecv {var = v, args = args})
    = StmntRecv (convertVarRef v, List.map convertRecvArg args)
    | convertStmnt (S.StmntRndRecv {var = v, args = args})
    = StmntRndRecv (convertVarRef v, List.map convertRecvArg args)
    | convertStmnt (S.StmntRecvX {var = v, args = args})
    = StmntRecvX (convertVarRef v, List.map convertRecvArg args)
    | convertStmnt (S.StmntRndRecvX {var = v, args = args})
    = StmntRndRecvX (convertVarRef v, List.map convertRecvArg args)
    | convertStmnt (S.StmntAssign {var = v, expr = e})
    = StmntAssign (convertVarRef v, convertExpr e)
    | convertStmnt (S.StmntIncr v) = StmntIncr (convertVarRef v)
    | convertStmnt (S.StmntDecr v) = StmntDecr (convertVarRef v)
    | convertStmnt S.StmntElse = StmntElse
    | convertStmnt S.StmntBreak = StmntBreak
    | convertStmnt (S.StmntGoTo s) = StmntGoTo s
    | convertStmnt (S.StmntLabeled {name = n, stmnt = s})
    = StmntLabeled (n, convertStmnt s)
    | convertStmnt (S.StmntPrintF {text = t, args = args})
    = StmntPrintF (t, List.map convertExpr args)
    | convertStmnt (S.StmntPrintM s) = StmntPrintM s
    | convertStmnt (S.StmntRun {name = name, args = args, prio = prio})
    = StmntRun (name, List.map convertExpr args, prio)
    | convertStmnt (S.StmntAssert e) = StmntAssert (convertExpr e)
    | convertStmnt (S.StmntCall {name = name, args = args})
    = StmntCall (name, List.map convertVarRef args)
    | convertStmnt (S.StmntCond e) = StmntCond (convertExpr e)


  fun convert (S.ProcType {active = act, name = n, decls = ds, prio = p, 
    prov = pr, seq = ss}) 
    = ProcType (act, n, List.map convertDecl ds, p, Option.map convertExpr pr,
    List.map convertStep ss)
    | convert (S.DProcType {active = act, name = n, decls = ds, prio = p, 
    prov = pr, seq = ss})
    = DProcType (act, n, List.map convertDecl ds, p, Option.map convertExpr pr, 
    List.map convertStep ss)
    | convert (S.Init {prio = p, seq = seq})
    = Init (p, List.map convertStep seq)
    | convert (S.Never s) = Never (List.map convertStep s)
    | convert (S.Trace s) = Trace (List.map convertStep s)
    | convert (S.NoTrace s) = NoTrace (List.map convertStep s)
    | convert (S.Inline {name = name, args = args, seq = seq})
    = Inline (name, args, List.map convertStep seq)
    | convert (S.TypeDef {name = n, decls = ds})
    = TypeDef (n, List.map convertDecl ds)
    | convert (S.MType s) = MType s
    | convert (S.ModuDecl d) = ModuDecl (convertDecl d)
    | convert (S.LTL {name = n, formula = f}) = Ltl (n,f)
end
