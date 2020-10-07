section "Data structures as used in Promela"
theory PromelaDatastructures
imports
  CAVA_Base.CAVA_Base
  "../CAVA_Automata/CAVA_Base/Lexord_List"
  PromelaAST
  "HOL-Library.IArray"
  Deriving.Compare_Instances
  CAVA_Base.CAVA_Code_Target
begin

(*<*)
no_notation test_bit (infixl "!!" 100)
(*>*)

subsection \<open>Abstract Syntax Tree \emph{after} preprocessing\<close>

text \<open>
  From the plain AST stemming from the parser, we'd like to have one containing more information while also removing duplicated constructs. This is achieved in the preprocessing step.

  The additional information contains:
  \begin{itemize}
    \item variable type (including whether it represents a channel or not)
    \item global vs local variable
  \end{itemize}

  Also certain constructs are expanded (like for-loops) or different nodes in the
  AST are collapsed into one parametrized node (e.g.\ the different send-operations).

  This preprocessing phase also tries to detect certain static errors and will bail out with an exception if such is encountered.
\<close>

datatype binOp = BinOpAdd
               | BinOpSub
               | BinOpMul
               | BinOpDiv
               | BinOpMod
               | BinOpGr
               | BinOpLe
               | BinOpGEq
               | BinOpLEq
               | BinOpEq
               | BinOpNEq
               | BinOpAnd
               | BinOpOr

datatype unOp = UnOpMinus
              | UnOpNeg

datatype expr = ExprBinOp binOp (*left*) expr (*right*) expr
              | ExprUnOp unOp expr
              | ExprCond (*cond*) expr (*exprTrue*) expr (*exprFalse*) expr
              | ExprLen chanRef
              | ExprVarRef varRef
              | ExprConst integer
              | ExprMConst integer String.literal (* MType replaced by constant *)
              | ExprTimeOut
              | ExprFull chanRef
              | ExprEmpty chanRef
              | ExprPoll chanRef "recvArg list" bool (* sorted *)

   and varRef = VarRef (*global*) bool 
                       (*name*) String.literal 
                       (*index*) "expr option"
   and chanRef = ChanRef varRef \<comment> \<open>explicit type for channels\<close>
   and recvArg = RecvArgVar varRef
               | RecvArgEval expr
               | RecvArgConst integer
               | RecvArgMConst integer String.literal

datatype varType = VTBounded integer integer
                 | VTChan

text \<open>Variable declarations at the beginning of a proctype or at global level.\<close>
datatype varDecl = VarDeclNum (*bounds*) integer integer
                              (*name*) String.literal
                              (*size*) "integer option"
                              (*init*) "expr option"
                 | VarDeclChan (*name*) String.literal
                               (*size*) "integer option"
                               (*capacityTypes*) "(integer * varType list) option"

text \<open>Variable declarations during a proctype.\<close>
datatype procVarDecl = ProcVarDeclNum  (*bounds*) integer integer
                                       (*name*) String.literal
                                       (*size*) "integer option"
                                       (*init*) "expr option"
                     | ProcVarDeclChan (*name*) String.literal
                                       (*size*) "integer option"

datatype procArg = ProcArg varType String.literal

datatype stmnt = StmntIf "(step list) list"
               | StmntDo "(step list) list"
               | StmntAtomic "step list"
               | StmntSeq "step list"
               | StmntSend chanRef "expr list" bool (*sorted*)
               | StmntRecv chanRef "recvArg list" bool (*sorted*) bool (*remove?*)
               | StmntAssign varRef expr
               | StmntElse
               | StmntBreak
               | StmntSkip
               | StmntGoTo String.literal
               | StmntLabeled String.literal stmnt
               | StmntRun (*name*) String.literal
                          (*args*) "expr list"
               | StmntCond expr
               | StmntAssert expr
        
  and step = StepStmnt stmnt (*unless*) "stmnt option"
           | StepDecl "procVarDecl list"
           | StepSkip

datatype proc = ProcType (*active*) "(integer option) option"
                           (*name*)   String.literal
                           (*args*)  "procArg list"
                           (*decls*) "varDecl list"
                           (*seq*)    "step list"
              | Init "varDecl list" "step list"

type_synonym ltl = "\<comment> \<open>name:\<close> String.literal \<times> \<comment> \<open>formula:\<close> String.literal"
type_synonym promela = "varDecl list \<times> proc list \<times> ltl list"

subsection \<open>Preprocess the AST of the parser into our variant\<close>

text \<open>We setup some functionality for printing warning or even errors.

All those constants are logically @{term undefined}, but replaced by the parser
for something meaningful.\<close>
consts 
  warn :: "String.literal \<Rightarrow> unit"

abbreviation "with_warn msg e \<equiv> let _ = warn msg in e"
abbreviation "the_warn opt msg \<equiv> case opt of None \<Rightarrow> () | _ \<Rightarrow> warn msg"

text \<open>\<open>usc\<close>: "Unsupported Construct"\<close>
definition [code del]: "usc (c :: String.literal) \<equiv> undefined"

definition  [code del]: "err (e :: String.literal) = undefined"
abbreviation "errv e v \<equiv> err (e + v)"

definition [simp, code del]: "abort (msg :: String.literal) f = f ()"
abbreviation "abortv msg v f \<equiv> abort (msg + v) f"

code_printing
  code_module PromelaUtils \<rightharpoonup> (SML) \<open>
    structure PromelaUtils = struct
      exception UnsupportedConstruct of string
      exception StaticError of string
      exception RuntimeError of string
      fun warn msg = TextIO.print ("Warning: " ^ msg ^ "\n")
      fun usc  c   = raise (UnsupportedConstruct c)
      fun err  e   = raise (StaticError e)
      fun abort msg _ = raise (RuntimeError msg)
    end\<close>
| constant warn \<rightharpoonup> (SML) "PromelaUtils.warn"
| constant usc \<rightharpoonup> (SML) "PromelaUtils.usc"
| constant err \<rightharpoonup> (SML) "PromelaUtils.err"
| constant abort \<rightharpoonup> (SML) "PromelaUtils.abort"
code_reserved SML PromelaUtils


(*<*)
ML_val \<open>@{code hd}\<close> (* Test code-printing setup. If this fails, the setup is skewed. *)
(*>*)

text \<open>The preprocessing is done for each type on its own.\<close>

primrec ppBinOp :: "AST.binOp \<Rightarrow> binOp"
where
  "ppBinOp AST.BinOpAdd = BinOpAdd"
| "ppBinOp AST.BinOpSub = BinOpSub"
| "ppBinOp AST.BinOpMul = BinOpMul"
| "ppBinOp AST.BinOpDiv = BinOpDiv"
| "ppBinOp AST.BinOpMod = BinOpMod"
| "ppBinOp AST.BinOpGr = BinOpGr"
| "ppBinOp AST.BinOpLe = BinOpLe"
| "ppBinOp AST.BinOpGEq = BinOpGEq"
| "ppBinOp AST.BinOpLEq = BinOpLEq"
| "ppBinOp AST.BinOpEq = BinOpEq"
| "ppBinOp AST.BinOpNEq = BinOpNEq"
| "ppBinOp AST.BinOpAnd = BinOpAnd"
| "ppBinOp AST.BinOpOr = BinOpOr"
| "ppBinOp AST.BinOpBitAnd = usc STR ''BinOpBitAnd''"
| "ppBinOp AST.BinOpBitXor = usc STR ''BinOpBitXor''"
| "ppBinOp AST.BinOpBitOr = usc STR ''BinOpBitOr''"
| "ppBinOp AST.BinOpShiftL = usc STR ''BinOpShiftL''"
| "ppBinOp AST.BinOpShiftR = usc STR ''BinOpShiftR''"

primrec ppUnOp :: "AST.unOp \<Rightarrow> unOp"
where
  "ppUnOp AST.UnOpMinus = UnOpMinus"
| "ppUnOp AST.UnOpNeg = UnOpNeg"
| "ppUnOp AST.UnOpComp = usc STR ''UnOpComp''"

text \<open>The data structure holding all information on variables we found so far.\<close>
type_synonym var_data = "
     (String.literal, (integer option \<times> bool)) lm \<comment> \<open>channels\<close>
     \<times> (String.literal, (integer option \<times> bool)) lm \<comment> \<open>variables\<close>
     \<times> (String.literal, integer) lm \<comment> \<open>mtypes\<close>
     \<times> (String.literal, varRef) lm \<comment> \<open>aliases (used for inlines)\<close>"

definition dealWithVar 
  :: "var_data \<Rightarrow> String.literal
      \<Rightarrow> (String.literal \<Rightarrow> integer option \<times> bool \<Rightarrow> expr option \<Rightarrow> 'a) 
      \<Rightarrow> (String.literal \<Rightarrow> integer option \<times> bool \<Rightarrow> expr option \<Rightarrow> 'a) 
      \<Rightarrow> (integer \<Rightarrow> 'a) \<Rightarrow> 'a"
where
  "dealWithVar cvm n fC fV fM \<equiv> ( 
    let (c,v,m,a) = cvm in
    let (n, idx) = case lm.lookup n a of 
                     None \<Rightarrow> (n, None) 
                   | Some (VarRef _ name idx) \<Rightarrow> (name, idx) 
    in
    case lm.lookup n m of 
      Some i \<Rightarrow> (case idx of None \<Rightarrow> fM i 
                           | _ \<Rightarrow> err STR ''Array subscript used on MType (via alias).'')
    | None \<Rightarrow> (case lm.lookup n v of
               Some g \<Rightarrow> fV n g idx
             | None \<Rightarrow> (case lm.lookup n c of
                   Some g \<Rightarrow> fC n g idx
                 | None \<Rightarrow> err (STR ''Unknown variable referenced: '' + n))))"

primrec enforceChan :: "varRef + chanRef \<Rightarrow> chanRef" where
  "enforceChan (Inl _) = err STR ''Channel expected. Got normal variable.''"
| "enforceChan (Inr c) = c"

fun liftChan :: "varRef + chanRef \<Rightarrow> varRef" where
  "liftChan (Inl v) = v"
| "liftChan (Inr (ChanRef v)) = v"

fun resolveIdx :: "expr option \<Rightarrow> expr option \<Rightarrow> expr option"
where
  "resolveIdx None None = None"
| "resolveIdx idx  None = idx"
| "resolveIdx None aliasIdx = aliasIdx"
| "resolveIdx _   _     = err STR ''Array subscript used twice (via alias).''"

fun ppExpr :: "var_data \<Rightarrow> AST.expr \<Rightarrow> expr"
and ppVarRef :: "var_data \<Rightarrow> AST.varRef \<Rightarrow> varRef + chanRef"
and ppRecvArg :: "var_data \<Rightarrow> AST.recvArg \<Rightarrow> recvArg"
where
  "ppVarRef cvm (AST.VarRef name idx None) = dealWithVar cvm name
                    (\<lambda>name (_,g) aIdx. let idx = map_option (ppExpr cvm) idx in 
                         Inr (ChanRef (VarRef g name (resolveIdx idx aIdx))))
                    (\<lambda>name (_,g) aIdx. let idx = map_option (ppExpr cvm) idx in 
                         Inl (VarRef g name (resolveIdx idx aIdx)))
                    (\<lambda>_. err STR ''Variable expected. Got MType.'')"
| "ppVarRef cvm (AST.VarRef _ _ (Some _)) = 
     usc STR ''next operation on variables''"

| "ppExpr cvm AST.ExprTimeOut = ExprTimeOut"
| "ppExpr cvm (AST.ExprConst c) = ExprConst c"

| "ppExpr cvm (AST.ExprBinOp bo l r) = 
     ExprBinOp (ppBinOp bo) (ppExpr cvm l) (ppExpr cvm r)"
| "ppExpr cvm (AST.ExprUnOp uo e) = 
     ExprUnOp (ppUnOp uo) (ppExpr cvm e)"
| "ppExpr cvm (AST.ExprCond c t f) = 
     ExprCond (ppExpr cvm c) (ppExpr cvm t) (ppExpr cvm f)"

| "ppExpr cvm (AST.ExprLen v) = 
     ExprLen (enforceChan (ppVarRef cvm v))"
| "ppExpr cvm (AST.ExprFull v) = 
     ExprFull (enforceChan (ppVarRef cvm v))"
| "ppExpr cvm (AST.ExprEmpty v) = 
     ExprEmpty (enforceChan (ppVarRef cvm v))"
(* the following two are special constructs in Promela for helping Partial Order Reductions
   we don't have such things (yet), so use simple negation *)
| "ppExpr cvm (AST.ExprNFull v) = 
     ExprUnOp UnOpNeg (ExprFull (enforceChan (ppVarRef cvm v)))"
| "ppExpr cvm (AST.ExprNEmpty v) = 
     ExprUnOp UnOpNeg (ExprEmpty (enforceChan (ppVarRef cvm v)))"

| "ppExpr cvm (AST.ExprVarRef v) = (
          let to_exp = \<lambda>_. ExprVarRef (liftChan (ppVarRef cvm v)) in
          case v of 
              AST.VarRef name None None \<Rightarrow> 
                 dealWithVar cvm name 
                     (\<lambda>_ _ _. to_exp())
                     (\<lambda>_ _ _. to_exp())
                     (\<lambda>i. ExprMConst i name)
             | _ \<Rightarrow> to_exp())"

| "ppExpr cvm (AST.ExprPoll v es) = 
     ExprPoll (enforceChan (ppVarRef cvm v)) (map (ppRecvArg cvm) es) False"
| "ppExpr cvm (AST.ExprRndPoll v es) = 
     ExprPoll (enforceChan (ppVarRef cvm v)) (map (ppRecvArg cvm) es) True"

| "ppExpr cvm AST.ExprNP = usc STR ''ExprNP''"
| "ppExpr cvm (AST.ExprEnabled _) = usc STR ''ExprEnabled''"
| "ppExpr cvm (AST.ExprPC _) = usc STR ''ExprPC''"
| "ppExpr cvm (AST.ExprRemoteRef _ _ _) = usc STR ''ExprRemoteRef''"
| "ppExpr cvm (AST.ExprGetPrio _) = usc STR ''ExprGetPrio''"
| "ppExpr cvm (AST.ExprSetPrio _ _) = usc STR ''ExprSetPrio''"

| "ppRecvArg cvm (AST.RecvArgVar v) = (
          let to_ra = \<lambda>_. RecvArgVar (liftChan (ppVarRef cvm v)) in
          case v of 
              AST.VarRef name None None \<Rightarrow> 
                 dealWithVar cvm name 
                     (\<lambda>_ _ _. to_ra())
                     (\<lambda>_ _ _. to_ra())
                     (\<lambda>i. RecvArgMConst i name)
             | _ \<Rightarrow> to_ra())"
| "ppRecvArg cvm (AST.RecvArgEval e) = RecvArgEval (ppExpr cvm e)"
| "ppRecvArg cvm (AST.RecvArgConst c) = RecvArgConst c"

primrec ppVarType :: "AST.varType \<Rightarrow> varType" where
  "ppVarType AST.VarTypeBit = VTBounded 0 1"
| "ppVarType AST.VarTypeBool = VTBounded 0 1"
| "ppVarType AST.VarTypeByte = VTBounded 0 255"
| "ppVarType AST.VarTypePid = VTBounded 0 255"
| "ppVarType AST.VarTypeShort = VTBounded (-(2^15)) ((2^15) - 1)"
| "ppVarType AST.VarTypeInt = VTBounded (-(2^31)) ((2^31) - 1)"
| "ppVarType AST.VarTypeMType = VTBounded 1 255"
| "ppVarType AST.VarTypeChan = VTChan"
| "ppVarType AST.VarTypeUnsigned = usc STR ''VarTypeUnsigned''"
| "ppVarType (AST.VarTypeCustom _) = usc STR ''VarTypeCustom''"

fun ppVarDecl 
  :: "var_data \<Rightarrow> varType \<Rightarrow> bool \<Rightarrow> AST.varDecl \<Rightarrow> var_data \<times> varDecl" 
where
  "ppVarDecl (c,v,m,a) (VTBounded l h) g 
                       (AST.VarDeclNum name sze init) = (
     case lm.lookup name v of 
        Some _ \<Rightarrow> errv STR ''Duplicate variable '' name
       | _ \<Rightarrow> (case lm.lookup name a of 
               Some _ \<Rightarrow> errv
                         STR ''Variable name clashes with alias: '' name
               | _ \<Rightarrow> ((c, lm.update name (sze,g) v, m, a), 
                        VarDeclNum l h name sze 
                          (map_option (ppExpr (c,v,m,a)) init))))"
| "ppVarDecl _ _ g (AST.VarDeclNum name sze init) = 
     err STR ''Assiging num to non-num''"

| "ppVarDecl (c,v,m,a) VTChan g 
                       (AST.VarDeclChan name sze cap) = (
     let cap' = map_option (apsnd (map ppVarType)) cap in
     case lm.lookup name c of 
        Some _ \<Rightarrow> errv STR ''Duplicate variable '' name
       | _ \<Rightarrow> (case lm.lookup name a of 
               Some _ \<Rightarrow> errv 
                         STR ''Variable name clashes with alias: '' name
              | _ \<Rightarrow> ((lm.update name (sze, g) c, v, m, a), 
                     VarDeclChan name sze cap')))"
| "ppVarDecl _ _ g (AST.VarDeclChan name sze init) = 
     err STR ''Assiging chan to non-chan''"

| "ppVarDecl (c,v,m,a) (VTBounded l h) g 
                       (AST.VarDeclMType name sze init) = (
     let init = map_option (\<lambda>mty. 
     case lm.lookup mty m of 
        None \<Rightarrow> errv STR ''Unknown MType '' mty
      | Some mval \<Rightarrow> ExprMConst mval mty) init in
            case lm.lookup name c of 
              Some _ \<Rightarrow> errv STR ''Duplicate variable '' name
             | _ \<Rightarrow> (case lm.lookup name a of Some _ 
                       \<Rightarrow> errv STR ''Variable name clashes with alias: '' name
             | _ \<Rightarrow> ((c, lm.update name (sze,g) v, m, a), 
                    VarDeclNum l h name sze init)))"

| "ppVarDecl _ _ g (AST.VarDeclMType name sze init) = 
     err STR ''Assiging num to non-num''"

| "ppVarDecl _ _ _ (AST.VarDeclUnsigned _ _ _) = 
     usc STR ''VarDeclUnsigned''"

definition ppProcVarDecl 
  :: "var_data \<Rightarrow> varType \<Rightarrow> bool \<Rightarrow> AST.varDecl \<Rightarrow> var_data \<times> procVarDecl"
where
  "ppProcVarDecl cvm ty g v = (case ppVarDecl cvm ty g v of
       (cvm, VarDeclNum l h name sze init) \<Rightarrow> (cvm, ProcVarDeclNum l h name sze init)
     | (cvm, VarDeclChan name sze None) \<Rightarrow> (cvm, ProcVarDeclChan name sze)
     | _ \<Rightarrow> err STR ''Channel initilizations only allowed at the beginning of proctypes.'')"

fun ppProcArg 
  :: "var_data \<Rightarrow> varType \<Rightarrow> bool \<Rightarrow> AST.varDecl \<Rightarrow> var_data \<times> procArg"
where
  "ppProcArg (c,v,m,a) (VTBounded l h) g 
                       (AST.VarDeclNum name None None) = (
     case lm.lookup name v of 
        Some _ \<Rightarrow> errv STR ''Duplicate variable '' name
      | _ \<Rightarrow> (case lm.lookup name a of 
               Some _ \<Rightarrow> errv 
                          STR ''Variable name clashes with alias: '' name
             | _ \<Rightarrow> ((c, lm.update name (None, g) v, m, a), 
                    ProcArg (VTBounded l h) name)))"
| "ppProcArg _ _ _ (AST.VarDeclNum _ _ _) = 
     err STR ''Invalid proctype arguments''"

| "ppProcArg (c,v,m,a) VTChan g 
                       (AST.VarDeclChan name None None) = (
     case lm.lookup name c of 
        Some _ \<Rightarrow> errv STR ''Duplicate variable '' name
      | _ \<Rightarrow> (case lm.lookup name a of 
               Some _ \<Rightarrow> errv
                          STR ''Variable name clashes with alias: '' name
             | _ \<Rightarrow> ((lm.update name (None, g) c, v, m, a), ProcArg VTChan name)))"
| "ppProcArg _ _ _ (AST.VarDeclChan _ _ _) = 
     err STR ''Invalid proctype arguments''"

| "ppProcArg (c,v,m,a) (VTBounded l h) g 
                       (AST.VarDeclMType name None None) = (
     case lm.lookup name v of 
        Some _ \<Rightarrow> errv STR ''Duplicate variable '' name
       | _ \<Rightarrow> (case lm.lookup name a of 
               Some _ \<Rightarrow> errv
                          STR ''Variable name clashes with alias: '' name
              | _ \<Rightarrow> ((c, lm.update name (None, g) v, m, a), 
                     ProcArg (VTBounded l h) name)))"
| "ppProcArg _ _ _ (AST.VarDeclMType _ _ _) = 
     err STR ''Invalid proctype arguments''"

| "ppProcArg _ _ _ (AST.VarDeclUnsigned _ _ _) = usc STR ''VarDeclUnsigned''"

text \<open>Some preprocessing functions enrich the @{typ var_data} argument and hence return
a new updated one. When chaining multiple calls to such functions after another, we need to make
sure, the @{typ var_data} is passed accordingly. @{term cvm_fold} does exactly that for such a
function @{term g} and a list of nodes @{term ss}.\<close>

definition cvm_fold where
  "cvm_fold g cvm ss = foldl (\<lambda>(cvm,ss) s. apsnd (\<lambda>s'. ss@[s']) (g cvm s)) 
                             (cvm, []) ss"

lemma cvm_fold_cong[fundef_cong]:
  assumes "cvm = cvm'"
  and "stepss = stepss'"
  and "\<And>x d. x \<in> set stepss \<Longrightarrow> g d x = g' d x"
  shows "cvm_fold g cvm stepss = cvm_fold g' cvm' stepss'"
unfolding cvm_fold_def 
using assms
by (fastforce intro: foldl_cong split: prod.split)

fun liftDecl where
  "liftDecl f g cvm (AST.Decl vis t decls) = (
     let _ = the_warn vis STR ''Visibility in declarations not supported. Ignored.'' in
     let t = ppVarType t in
     cvm_fold (\<lambda>cvm. f cvm t g) cvm decls)"

definition ppDecl 
  :: "bool \<Rightarrow> var_data \<Rightarrow> AST.decl \<Rightarrow> var_data \<times> varDecl list" 
where
  "ppDecl = liftDecl ppVarDecl"

definition ppDeclProc 
  :: "var_data \<Rightarrow> AST.decl \<Rightarrow> var_data \<times> procVarDecl list"
where
  "ppDeclProc = liftDecl ppProcVarDecl False"

definition ppDeclProcArg 
  :: "var_data \<Rightarrow> AST.decl \<Rightarrow> var_data \<times> procArg list"
where
  "ppDeclProcArg = liftDecl ppProcArg False"

(* increment *)
definition incr :: "varRef \<Rightarrow> stmnt" where
  "incr v = StmntAssign v (ExprBinOp BinOpAdd (ExprVarRef v) (ExprConst 1))"

(* decrement *)
definition decr :: "varRef \<Rightarrow> stmnt" where
  "decr v = StmntAssign v (ExprBinOp BinOpSub (ExprVarRef v) (ExprConst 1))"

text \<open>
   Transforms
     \verb+for (i : lb .. ub) steps+
   into 
\begin{verbatim} {
   i = lb;
   do
     :: i =< ub -> steps; i++
     :: else -> break
   od
} \end{verbatim}
\<close>
definition forFromTo :: "varRef \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> step list \<Rightarrow> stmnt" where
  "forFromTo i lb ub steps = (
      let
        \<comment> \<open>\<open>i = lb\<close>\<close>
        loop_pre = StepStmnt (StmntAssign i lb) None;
        \<comment> \<open>\<open>i \<le> ub\<close>\<close>
        loop_cond = StepStmnt (StmntCond 
                                  (ExprBinOp BinOpLEq (ExprVarRef i) ub))
                                  None;
        \<comment> \<open>\<open>i++\<close>\<close>
        loop_incr = StepStmnt (incr i) None;
        \<comment> \<open>\<open>i \<le> ub -> ...; i++\<close>\<close>
        loop_body = loop_cond # steps @ [loop_incr];
        \<comment> \<open>\<open>else -> break\<close>\<close>
        loop_abort = [StepStmnt StmntElse None, StepStmnt StmntBreak None];
        \<comment> \<open>\<open>do :: i \<le> ub -> ... :: else -> break od\<close>\<close>
        loop = StepStmnt (StmntDo [loop_body, loop_abort]) None
      in
        StmntSeq [loop_pre, loop])"

text \<open>
   Transforms (where @{term a} is an array with @{term N} entries)
     \verb+for (i in a) steps+
   into
\begin{verbatim}{
   i = 0;
   do
     :: i < N -> steps; i++
     :: else -> break
   od
}\end{verbatim}
\<close>
definition forInArray :: "varRef \<Rightarrow> integer \<Rightarrow> step list \<Rightarrow> stmnt" where
  "forInArray i N steps = (
      let
        \<comment> \<open>\<open>i = 0\<close>\<close>
        loop_pre = StepStmnt (StmntAssign i (ExprConst 0)) None;
        \<comment> \<open>\<open>i < N\<close>\<close>
        loop_cond = StepStmnt (StmntCond 
                                 (ExprBinOp BinOpLe (ExprVarRef i) 
                                    (ExprConst N))) 
                                 None;
        \<comment> \<open>\<open>i++\<close>\<close>
        loop_incr = StepStmnt (incr i) None;
        \<comment> \<open>\<open>i < N -> ...; i++\<close>\<close>
        loop_body = loop_cond # steps @ [loop_incr];
        \<comment> \<open>\<open>else -> break\<close>\<close>
        loop_abort = [StepStmnt StmntElse None, StepStmnt StmntBreak None];
        \<comment> \<open>\<open>do :: i < N -> ... :: else -> break od\<close>\<close>
        loop = StepStmnt (StmntDo [loop_body, loop_abort]) None
      in
        StmntSeq [loop_pre, loop])"

text \<open>
   Transforms (where @{term c} is a channel)
     \verb+for (msg in c) steps+
   into 
\begin{verbatim}{
   byte :tmp: = 0;
   do
     :: :tmp: < len(c) -> 
          c?msg; c!msg;
          steps; 
          :tmp:++
     :: else -> break
   od
}\end{verbatim}
\<close>
definition forInChan :: "varRef \<Rightarrow> chanRef \<Rightarrow> step list \<Rightarrow> stmnt" where
  "forInChan msg c steps = (
      let  
        \<comment> \<open>\<open>byte :tmp: = 0\<close>\<close>
        tmpStr = STR '':tmp:'';
        loop_pre = StepDecl 
                    [ProcVarDeclNum 0 255 tmpStr None (Some (ExprConst 0))];
        tmp = VarRef False tmpStr None; 
        \<comment> \<open>\<open>:tmp: < len(c)\<close>\<close>
        loop_cond = StepStmnt (StmntCond 
                                 (ExprBinOp BinOpLe (ExprVarRef tmp) 
                                    (ExprLen c))) 
                              None;
        \<comment> \<open>\<open>:tmp:++\<close>\<close>
        loop_incr = StepStmnt (incr tmp) None;
        \<comment> \<open>\<open>c?msg\<close>\<close>
        recv = StepStmnt (StmntRecv c [RecvArgVar msg] False True) None;
        \<comment> \<open>\<open>c!msg\<close>\<close>
        send = StepStmnt (StmntSend c [ExprVarRef msg] False) None;
        \<comment> \<open>\<open>:tmp: < len(c) -> c?msg; c!msg; ...; :tmp:++\<close>\<close>
        loop_body = [loop_cond, recv, send] @ steps @ [loop_incr];
        \<comment> \<open>\<open>else -> break\<close>\<close>
        loop_abort = [StepStmnt StmntElse None, StepStmnt StmntBreak None];
        \<comment> \<open>\<open>do :: :tmp: < len(c) -> ... :: else -> break od\<close>\<close>
        loop = StepStmnt (StmntDo [loop_body, loop_abort]) None
      in
        StmntSeq [loop_pre, loop])"

text \<open>
   Transforms
     \verb+select (i : lb .. ub)+
   into 
\begin{verbatim}{
   i = lb;
   do
     :: i < ub -> i++
     :: break
   od
}\end{verbatim}
\<close>
definition select :: "varRef \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> stmnt" where
  "select i lb ub = (
      let
        \<comment> \<open>\<open>i = lb\<close>\<close>
        pre = StepStmnt (StmntAssign i lb) None;
        \<comment> \<open>\<open>i < ub\<close>\<close>
        cond = StepStmnt (StmntCond (ExprBinOp BinOpLe (ExprVarRef i) ub)) 
                         None;
        \<comment> \<open>\<open>i++\<close>\<close>
        incr = StepStmnt (incr i) None;
        \<comment> \<open>\<open>i < ub -> i++\<close>\<close>
        loop_body = [cond, incr];
        \<comment> \<open>\<open>break\<close>\<close>
        loop_abort = [StepStmnt StmntBreak None];
        \<comment> \<open>\<open>do :: i < ub -> ... :: break od\<close>\<close>
        loop = StepStmnt (StmntDo [loop_body, loop_abort]) None
      in
        StmntSeq [pre, loop])"

type_synonym inlines = 
  "(String.literal, String.literal list \<times> (var_data \<Rightarrow> var_data \<times> step list)) lm"
type_synonym stmnt_data = 
  " bool \<times> varDecl list \<times> inlines \<times> var_data"

fun ppStep :: "stmnt_data \<Rightarrow> AST.step \<Rightarrow> stmnt_data * step"
and ppStmnt :: "stmnt_data \<Rightarrow> AST.stmnt \<Rightarrow> stmnt_data * stmnt"
where
  "ppStep cvm (AST.StepStmnt s u) = (
     let (cvm', s') = ppStmnt cvm s in
     case u of None \<Rightarrow> (cvm', StepStmnt s' None) 
             | Some u \<Rightarrow> let (cvm'',u') = ppStmnt cvm' u in
                            (cvm'', StepStmnt s' (Some u')))"
| "ppStep (False, ps, i, cvm) (AST.StepDecl d) = 
     map_prod (\<lambda>cvm. (False, ps, i, cvm)) StepDecl (ppDeclProc cvm d)"
| "ppStep (True, ps, i, cvm) (AST.StepDecl d) = (
             let (cvm', ps') = ppDecl False cvm d 
             in ((True, ps@ps', i, cvm'), StepSkip))"
| "ppStep (_,cvm) (AST.StepXR _) = 
     with_warn STR ''StepXR not supported. Ignored.'' ((False,cvm), StepSkip)"
| "ppStep (_,cvm) (AST.StepXS _) = 
     with_warn STR ''StepXS not supported. Ignored.'' ((False,cvm), StepSkip)"

| "ppStmnt (_,cvm) (AST.StmntBreak) = ((False,cvm), StmntBreak)"
| "ppStmnt (_,cvm) (AST.StmntElse) = ((False,cvm), StmntElse)"
| "ppStmnt (_,cvm) (AST.StmntGoTo l) = ((False,cvm), StmntGoTo l)"
| "ppStmnt (_,cvm) (AST.StmntLabeled l s) = 
     apsnd (StmntLabeled l) (ppStmnt (False,cvm) s)"
| "ppStmnt (_,ps,i,cvm) (AST.StmntCond e) = 
     ((False,ps,i,cvm), StmntCond (ppExpr cvm e))"
| "ppStmnt (_,ps,i,cvm) (AST.StmntAssert e) = 
     ((False,ps,i,cvm), StmntAssert (ppExpr cvm e))"
| "ppStmnt (_,ps,i,cvm) (AST.StmntAssign v e) = 
     ((False,ps,i,cvm), StmntAssign (liftChan (ppVarRef cvm v)) (ppExpr cvm e))"
| "ppStmnt (_,ps,i,cvm) (AST.StmntSend v es) = 
     ((False,ps,i,cvm), StmntSend (enforceChan (ppVarRef cvm v)) 
                                  (map (ppExpr cvm) es) False)"
| "ppStmnt (_,ps,i,cvm) (AST.StmntSortSend v es) = 
     ((False,ps,i,cvm), StmntSend (enforceChan (ppVarRef cvm v)) 
                                  (map (ppExpr cvm) es) True)"
| "ppStmnt (_,ps,i,cvm) (AST.StmntRecv v rs) = 
     ((False,ps,i,cvm), StmntRecv (enforceChan (ppVarRef cvm v)) 
                                  (map (ppRecvArg cvm) rs) False True)"
| "ppStmnt (_,ps,i,cvm) (AST.StmntRecvX v rs) = 
     ((False,ps,i,cvm), StmntRecv (enforceChan (ppVarRef cvm v)) 
                                  (map (ppRecvArg cvm) rs) False False)"
| "ppStmnt (_,ps,i,cvm) (AST.StmntRndRecv v rs) = 
     ((False,ps,i,cvm), StmntRecv (enforceChan (ppVarRef cvm v)) 
                                  (map (ppRecvArg cvm) rs) True True)"
| "ppStmnt (_,ps,i,cvm) (AST.StmntRndRecvX v rs) = 
     ((False,ps,i,cvm), StmntRecv (enforceChan (ppVarRef cvm v)) 
                                  (map (ppRecvArg cvm) rs) True False)"
| "ppStmnt (_,ps,i,cvm) (AST.StmntRun n es p) = ( 
     let _ = the_warn p STR ''Priorities for 'run' not supported. Ignored.'' in
    ((False,ps,i,cvm), StmntRun n (map (ppExpr cvm) es)))"
| "ppStmnt (_,cvm) (AST.StmntSeq ss) = 
     apsnd StmntSeq (cvm_fold ppStep (False,cvm) ss)"
| "ppStmnt (_,cvm) (AST.StmntAtomic ss) = 
     apsnd StmntAtomic (cvm_fold ppStep (False,cvm) ss)"
| "ppStmnt (_,cvm) (AST.StmntIf sss) = 
     apsnd StmntIf (cvm_fold (cvm_fold ppStep) (False,cvm) sss)"
| "ppStmnt (_,cvm) (AST.StmntDo sss) = 
     apsnd StmntDo (cvm_fold (cvm_fold ppStep) (False,cvm) sss)"

(* Replace i++ and i-- by i = i + 1 / i = i - 1 *)
| "ppStmnt (_,ps,i,cvm) (AST.StmntIncr v) = 
     ((False,ps,i,cvm), incr (liftChan (ppVarRef cvm v)))"
| "ppStmnt (_,ps,i,cvm) (AST.StmntDecr v) = 
     ((False,ps,i,cvm), decr (liftChan (ppVarRef cvm v)))"

| "ppStmnt (_,cvm) (AST.StmntPrintF _ _) = 
     with_warn STR ''PrintF ignored'' ((False,cvm), StmntSkip)"
| "ppStmnt (_,cvm) (AST.StmntPrintM _) = 
     with_warn STR ''PrintM ignored'' ((False,cvm), StmntSkip)"

| "ppStmnt (_,ps,inl,cvm) (AST.StmntFor 
                              (AST.RangeFromTo i lb ub) 
                              steps) = (
     let 
       i = liftChan (ppVarRef cvm i);
       (lb,ub) = (ppExpr cvm lb, ppExpr cvm ub)
     in
       apsnd (forFromTo i lb ub) (cvm_fold ppStep (False,ps,inl,cvm) steps))"
| "ppStmnt (_,ps,inl,cvm) (AST.StmntFor 
                              (AST.RangeIn i v) 
                              steps) = (
     let
        i = liftChan (ppVarRef cvm i);
        (cvm',steps) = cvm_fold ppStep (False,ps,inl,cvm) steps
     in
        case ppVarRef cvm v of
         Inr c \<Rightarrow> (cvm', forInChan i c steps)
       | Inl (VarRef _ _ (Some _)) \<Rightarrow> err STR ''Iterating over array-member.''
       | Inl (VarRef _ name None) \<Rightarrow> (
             let (_,v,_) = cvm in
             case fst (the (lm.lookup name v)) of
              None \<Rightarrow> err STR ''Iterating over non-array variable.''
            | Some N \<Rightarrow> (cvm', forInArray i N steps)))"

| "ppStmnt (_,ps,inl,cvm) (AST.StmntSelect 
                              (AST.RangeFromTo i lb ub)) = (
     let
       i = liftChan (ppVarRef cvm i);
       (lb, ub) = (ppExpr cvm lb, ppExpr cvm ub)
     in
       ((False,ps,inl,cvm), select i lb ub))"
| "ppStmnt (_,cvm) (AST.StmntSelect (AST.RangeIn _ _)) = 
     err STR ''\"in\" not allowed in select''"

| "ppStmnt (_,ps,inl,cvm) (AST.StmntCall macro args) = (
     let 
       args = map (liftChan \<circ> ppVarRef cvm) args;
       (c,v,m,a) = cvm
     in
       case lm.lookup macro inl of
        None \<Rightarrow> errv STR ''Calling unknown macro '' macro
      | Some (names,sF) \<Rightarrow>
          if length names \<noteq> length args then 
             (err STR ''Called macro with wrong number of arguments.'') 
          else
             let a' = foldl (\<lambda>a (k,v). lm.update k v a) a (zip names args) in
             let ((c,v,m,_),steps) = sF (c,v,m,a') in
             ((False,ps,inl,c,v,m,a), StmntSeq steps))"
         
| "ppStmnt cvm (AST.StmntDStep _) = usc STR ''StmntDStep''"

fun ppModule 
  :: "var_data \<times> inlines \<Rightarrow> AST.module 
      \<Rightarrow> var_data \<times> inlines \<times> (varDecl list + proc + ltl)"
where
  "ppModule (cvm, inl) (AST.ProcType act name args prio prov steps) = (
     let 
        _ = the_warn prio STR ''Priorities for procs not supported. Ignored.'';
        _ = the_warn prov STR ''Priov (??) for procs not supported. Ignored.'';
        (cvm', args) = cvm_fold ppDeclProcArg cvm args;
        ((_, vars, _, _), steps) = cvm_fold ppStep (True,[],inl,cvm') steps
     in
        (cvm, inl, Inr (Inl (ProcType act name (concat args) vars steps))))"

| "ppModule (cvm,inl) (AST.Init prio steps) = (
     let _ = the_warn prio STR ''Priorities for procs not supported. Ignored.'' in
     let ((_, vars, _, _), steps) = cvm_fold ppStep (True,[],inl,cvm) steps in
     (cvm, inl, Inr (Inl (Init vars steps))))"

| "ppModule (cvm,inl) (AST.Ltl name formula) = 
     (cvm, inl, Inr (Inr (name, formula)))"

| "ppModule (cvm,inl) (AST.ModuDecl decl) = 
     apsnd (\<lambda>ds. (inl,Inl ds)) (ppDecl True cvm decl)"

| "ppModule (cvm,inl) (AST.MType mtys) = (
     let (c,v,m,a) = cvm in
     let num = integer_of_nat (lm.size m) + 1 in
     let (m',_) = foldr (\<lambda>mty (m,num). 
                    let m' = lm.update mty num m 
                    in (m',num+1)) mtys (m,num)
     in
         ((c,v,m',a), inl, Inl []))"

| "ppModule (cvm,inl) (AST.Inline name args steps) = (
     let stepF = (\<lambda>cvm. let ((_,_,_,cvm),steps) = 
                          cvm_fold ppStep (False,[],inl,cvm) steps 
                        in (cvm,steps))
     in let inl = lm.update name (args, stepF) inl
     in (cvm,inl, Inl[]))"

| "ppModule cvm (AST.DProcType _ _ _ _ _ _) = usc STR ''DProcType''"
| "ppModule cvm (AST.Never _) = usc STR ''Never''"
| "ppModule cvm (AST.Trace _) = usc STR ''Trace''"
| "ppModule cvm (AST.NoTrace _) = usc STR ''NoTrace''"
| "ppModule cvm (AST.TypeDef _ _) = usc STR ''TypeDef''"

definition preprocess :: "AST.module list \<Rightarrow> promela" where
  "preprocess ms = (
     let 
       dflt_vars = [(STR ''_pid'', (None, False)), 
                    (STR ''__assert__'', (None, True)), 
                    (STR ''_'', (None, True))];
       cvm = (lm.empty(), lm.to_map dflt_vars, lm.empty(), lm.empty());
       (_,_,pr) = (foldl (\<lambda>(cvm,inl,vs,ps,ls) m.
                            let (cvm', inl', m') = ppModule (cvm,inl) m in
                            case m' of
                              Inl v \<Rightarrow> (cvm',inl',vs@v,ps,ls)
                            | Inr (Inl p) \<Rightarrow> (cvm',inl',vs,ps@[p],ls)
                            | Inr (Inr l) \<Rightarrow> (cvm',inl',vs,ps,ls@[l])) 
                          (cvm, lm.empty(),[],[],[]) ms)
       in
         pr)"

fun extractLTL
  :: "AST.module \<Rightarrow> ltl option"
where
  "extractLTL (AST.Ltl name formula) = Some (name, formula)"
| "extractLTL _ = None"

primrec extractLTLs
  :: "AST.module list \<Rightarrow> (String.literal, String.literal) lm"
where
  "extractLTLs [] = lm.empty()"
| "extractLTLs (m#ms) = (case extractLTL m of 
                           None \<Rightarrow> extractLTLs ms
                         | Some (n,f) \<Rightarrow> lm.update n f (extractLTLs ms))"

definition lookupLTL
  :: "AST.module list \<Rightarrow> String.literal \<Rightarrow> String.literal option"
  where "lookupLTL ast k = lm.lookup k (extractLTLs ast)"

subsection \<open>The transition system\<close>

text \<open>
  The edges in our transition system consist of a condition (evaluated under the current environment) and an effect (modifying the current environment). 
  Further they may be atomic, \ie a whole row of such edges is taken before yielding a new state. 
  Additionally, they carry a priority: the edges are checked from highest to lowest priority, and if one edge on a higher level can be taken, the lower levels are ignored.

  The states of the system do not carry any information.
\<close>

datatype edgeCond = ECElse 
                  | ECTrue
                  | ECFalse 
                  | ECExpr expr 
                  | ECRun String.literal 
                  | ECSend chanRef
                  | ECRecv chanRef "recvArg list" bool (* sorted *)

datatype edgeEffect = EEEnd 
                    | EEId 
                    | EEGoto
                    | EEAssert expr 
                    | EEAssign varRef expr 
                    | EEDecl procVarDecl
                    | EERun String.literal "expr list"
                    | EESend chanRef "expr list" bool (*sorted*)
                    | EERecv chanRef "recvArg list" bool (*sorted*) bool (*remove*)

datatype edgeIndex = Index nat | LabelJump String.literal "nat option"
datatype edgeAtomic = NonAtomic | Atomic | InAtomic

record edge = 
  cond   :: edgeCond
  effect :: edgeEffect
  target :: edgeIndex
  prio   :: integer
  atomic :: edgeAtomic

definition isAtomic :: "edge \<Rightarrow> bool" where
  "isAtomic e = (case atomic e of Atomic \<Rightarrow> True | _ \<Rightarrow> False)"

definition inAtomic :: "edge \<Rightarrow> bool" where
  "inAtomic e = (case atomic e of NonAtomic \<Rightarrow> False | _ \<Rightarrow> True)"

subsection \<open>State\<close>

datatype variable = Var varType integer
                  | VArray varType nat "integer iarray"

datatype channel = Channel integer "varType list" "integer list list"
                 | HSChannel "varType list" (* handshake channel *)
                 | InvChannel (* Invalid / closed channel *)

type_synonym var_dict = "(String.literal, variable) lm"
type_synonym labels   = "(String.literal, nat) lm"
type_synonym ltls     = "(String.literal, String.literal) lm"
type_synonym states   = "(\<comment> \<open>prio:\<close> integer \<times> edge list) iarray"
type_synonym channels = "channel list"

type_synonym process  = 
  "nat \<comment> \<open>offset\<close>
 \<times> edgeIndex \<comment> \<open>start\<close>
 \<times> procArg list \<comment> \<open>args\<close>
 \<times> varDecl list \<comment> \<open>top decls\<close>"

record program =
  processes :: "process iarray"
  labels :: "labels iarray"
  states :: "states iarray"
  proc_names :: "String.literal iarray"
  proc_data :: "(String.literal, nat) lm"

record pState = \<comment> \<open>State of a process\<close>
  pid      :: nat             \<comment> \<open>Process identifier\<close>
  vars     :: var_dict        \<comment> \<open>Dictionary of variables\<close>
  pc       :: nat             \<comment> \<open>Program counter\<close>
  channels :: "integer list"  \<comment> \<open>List of channels created in the process. Used to close them on finalization.\<close>
  idx :: nat                  \<comment> \<open>Offset into the arrays of @{type program}\<close>

hide_const (open) idx

record gState = \<comment> \<open>Global state\<close>
  vars      :: var_dict      \<comment> \<open>Global variables\<close>
  channels  :: channels      \<comment> \<open>Channels are by construction part of the global state, even when created in a process.\<close>
  timeout   :: bool          \<comment> \<open>Set to True if no process can take a transition.\<close>
  procs     :: "pState list" \<comment> \<open>List of all running processes. A process is removed from it, when there is no running one
                                 with a higher index.\<close>

record gState\<^sub>I = gState + \<comment> \<open>Additional internal infos\<close>
  handshake :: nat
  hsdata    :: "integer list " \<comment> \<open>Data transferred via a handshake.\<close>
  exclusive :: nat     \<comment> \<open>Set to the PID of the process, which is in an exclusive (= atomic) state.\<close>
  else      :: bool    \<comment> \<open>Set to True for each process, if it can not take a transition. Used before timeout.\<close>

subsection \<open>Printing\<close>

primrec printBinOp :: "binOp \<Rightarrow> string" where
  "printBinOp BinOpAdd = ''+''"
| "printBinOp BinOpSub = ''-''"
| "printBinOp BinOpMul = ''*''"
| "printBinOp BinOpDiv = ''/''"
| "printBinOp BinOpMod = ''mod''"
| "printBinOp BinOpGr = ''>''"
| "printBinOp BinOpLe = ''<''"
| "printBinOp BinOpGEq = ''>=''"
| "printBinOp BinOpLEq = ''=<''"
| "printBinOp BinOpEq = ''==''"
| "printBinOp BinOpNEq = ''!=''"
| "printBinOp BinOpAnd = ''&&''"
| "printBinOp BinOpOr = ''||''"

primrec printUnOp :: "unOp \<Rightarrow> string" where
  "printUnOp UnOpMinus = ''-''"
| "printUnOp UnOpNeg = ''!''"

definition printList :: "('a \<Rightarrow> string) \<Rightarrow> 'a list \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string \<Rightarrow> string"
where
  "printList f xs l r sep = (
                     let f' = (\<lambda>str x. if str = [] then f x
                                       else str @ sep @ f x)
                     in l @ (foldl f' [] xs) @ r)"

lemma printList_cong [fundef_cong]:
  assumes "xs = xs'"
  and "l = l'"
  and "r = r'"
  and "sep = sep'"
  and "\<And>x. x \<in> set xs \<Longrightarrow> f x = f' x"
  shows "printList f xs l r sep = printList f' xs' l' r' sep'"
  unfolding printList_def
  using assms
  by (auto intro: foldl_cong)

fun printExpr :: "(integer \<Rightarrow> string) \<Rightarrow> expr \<Rightarrow> string"
and printFun ::  "(integer \<Rightarrow> string) \<Rightarrow> string \<Rightarrow> chanRef \<Rightarrow> string"
and printVarRef :: "(integer \<Rightarrow> string) \<Rightarrow> varRef \<Rightarrow> string"
and printChanRef :: "(integer \<Rightarrow> string) \<Rightarrow> chanRef \<Rightarrow> string"
and printRecvArg :: "(integer \<Rightarrow> string) \<Rightarrow> recvArg \<Rightarrow> string" where
  "printExpr f ExprTimeOut = ''timeout''"
| "printExpr f (ExprBinOp binOp left right) = 
     printExpr f left @ '' '' @ printBinOp binOp @ '' '' @ printExpr f right"
| "printExpr f (ExprUnOp unOp e) = printUnOp unOp @ printExpr f e"
| "printExpr f (ExprVarRef varRef) = printVarRef f varRef"
| "printExpr f (ExprConst i) = f i"
| "printExpr f (ExprMConst i m) = String.explode m"
| "printExpr f (ExprCond c l r) = 
     ''( (( '' @ printExpr f c @ '' )) -> '' 
     @ printExpr f l @ '' : '' 
     @ printExpr f r @ '' )''"
| "printExpr f (ExprLen chan) = printFun f ''len'' chan"
| "printExpr f (ExprEmpty chan) = printFun f ''empty'' chan"
| "printExpr f (ExprFull chan) = printFun f ''full'' chan"
| "printExpr f (ExprPoll chan es srt) = (
     let p = if srt then ''??'' else ''?'' in
     printChanRef f chan @ p 
     @ printList (printRecvArg f) es ''['' '']'' '', '')"

| "printVarRef _ (VarRef _ name None) = String.explode name"
| "printVarRef f (VarRef _ name (Some indx)) = 
     String.explode name @ ''['' @ printExpr f indx @ '']''"

| "printChanRef f (ChanRef v) = printVarRef f v"

| "printFun f fun var = fun @ ''('' @ printChanRef f var @ '')''"

| "printRecvArg f (RecvArgVar v) = printVarRef f v"
| "printRecvArg f (RecvArgConst c) = f c"
| "printRecvArg f (RecvArgMConst _ m) = String.explode m"
| "printRecvArg f (RecvArgEval e) = ''eval('' @ printExpr f e @ '')''"

fun printVarDecl :: "(integer \<Rightarrow> string) \<Rightarrow> procVarDecl \<Rightarrow> string" where
  "printVarDecl f (ProcVarDeclNum _ _ n None None) = 
    String.explode n @ '' = 0''"
| "printVarDecl f (ProcVarDeclNum _ _ n None (Some e)) = 
    String.explode n @ '' = '' @ printExpr f e"
| "printVarDecl f (ProcVarDeclNum _ _ n (Some i) None) = 
    String.explode n @ ''['' @ f i @ ''] = 0''"
| "printVarDecl f (ProcVarDeclNum _ _ n (Some i) (Some e)) = 
    String.explode n @ ''[''@ f i @ ''] = '' @ printExpr f e"
| "printVarDecl f (ProcVarDeclChan n None) = 
    ''chan '' @ String.explode n"
| "printVarDecl f (ProcVarDeclChan n (Some i)) = 
    ''chan '' @ String.explode n @ ''['' @ f i @ '']''"

primrec printCond :: "(integer \<Rightarrow> string) \<Rightarrow> edgeCond \<Rightarrow> string" where
  "printCond f ECElse = ''else''"
| "printCond f ECTrue = ''true''"
| "printCond f ECFalse = ''false''"
| "printCond f (ECRun n) = ''run '' @ String.explode n @ ''(...)''"
| "printCond f (ECExpr e) = printExpr f e"
| "printCond f (ECSend c) = printChanRef f c @ ''! ...''"
| "printCond f (ECRecv c _ _) = printChanRef f c @ ''? ...''"

primrec printEffect :: "(integer \<Rightarrow> string) \<Rightarrow> edgeEffect \<Rightarrow> string" where
  "printEffect f EEEnd = ''-- end --''"
| "printEffect f EEId = ''ID''"
| "printEffect f EEGoto = ''goto''"
| "printEffect f (EEAssert e) = ''assert('' @ printExpr f e @'')''"
| "printEffect f (EERun n _) = ''run '' @ String.explode n @ ''(...)''"
| "printEffect f (EEAssign v expr) = 
     printVarRef f v @ '' = '' @ printExpr f expr"
| "printEffect f (EEDecl d) = printVarDecl f d"
| "printEffect f (EESend v es srt) = (
     let s = if srt then ''!!'' else ''!'' in 
     printChanRef f v @ s @ printList (printExpr f) es ''('' '')'' '', '')"
| "printEffect f (EERecv v rs srt rem) = (
     let p = if srt then ''??'' else ''?'' in
     let (l,r) = if rem then (''('', '')'') else (''<'', ''>'') in
     printChanRef f v @ p @ printList (printRecvArg f) rs l r '', '')"

primrec printIndex :: "(integer \<Rightarrow> string) \<Rightarrow> edgeIndex \<Rightarrow> string" where
  "printIndex f (Index pos) = f (integer_of_nat pos)"
| "printIndex _ (LabelJump l _) = String.explode l"

definition printEdge :: "(integer \<Rightarrow> string) \<Rightarrow> nat \<Rightarrow> edge \<Rightarrow> string" where
  "printEdge f indx e = (
     let
       tStr = printIndex f (target e);
       pStr = if prio e < 0 then '' Prio: '' @ f (prio e) else [];
       atom = if isAtomic e then \<lambda>x. x @ '' {A}'' else id;
       pEff = \<lambda>_. atom (printEffect f (effect e));
       contStr = case (cond e) of 
                  ECTrue \<Rightarrow> pEff ()
                | ECFalse \<Rightarrow> pEff ()
                | ECSend _ \<Rightarrow> pEff()
                | ECRecv _ _ _\<Rightarrow> pEff()
                | _ \<Rightarrow>  atom (''(( '' @ printCond f (cond e) @ '' ))'')
     in
       f (integer_of_nat indx) @ '' ---> '' @ tStr @ '' => '' @ contStr @ pStr)"

definition printEdges :: "(integer \<Rightarrow> string) \<Rightarrow> states \<Rightarrow> string list" where
  "printEdges f es = concat (map (\<lambda>n. map (printEdge f n) (snd (es !! n))) 
                                 (rev [0..<IArray.length es]))"

definition printLabels :: "(integer \<Rightarrow> string) \<Rightarrow> labels \<Rightarrow> string list" where
  "printLabels f ls = lm.iterate ls (\<lambda>(k,l) res. 
                                      (''Label '' @ String.explode k @ '': '' 
                                       @ f (integer_of_nat l)) # res) []"

fun printProcesses :: "(integer \<Rightarrow> string) \<Rightarrow> program \<Rightarrow> string list" where
  "printProcesses f prog = lm.iterate (proc_data prog) 
     (\<lambda>(k,idx) res.
            let (_,start,_,_) = processes prog !! idx in 
            [] # (''Process '' @ String.explode k) # [] # printEdges f (states prog !! idx)
            @ [''START ---> '' @ printIndex f start, []] 
            @ printLabels f (labels prog !! idx) @ res) []"

(*<*)
(*section {* Instantiations *}
text {* Here instantiations for classes @{class linorder} and @{class hashable} are given for our datatypes.
As we include other structures, which sometime also lack those instantiations, this is done here too. *}
subsection {* Others *}
text {* The following lemmas are needed to make our hashing and linorder sound.

NB: It cannot be proven that 
@{prop "Assoc_List.update k v (Assoc_List.update k2 v2 ls) = Assoc_List.update k2 v2 (Assoc_List.update k v ls)"}

Hence our implementation becomes unsound when order of insertion is not fix. *}*)

lemma AL_update_idem:
  assumes "Assoc_List.lookup ls k = Some v"
  shows "Assoc_List.update k v ls = ls"
proof -
  obtain lsl where lsl: "lsl = Assoc_List.impl_of ls" by blast

  with assms have "map_of lsl k = Some v" by (simp add: Assoc_List.lookup_def)
  hence "AList.update_with_aux v k (\<lambda>_. v) lsl = lsl" by (induct lsl) auto
  with lsl show ?thesis by (simp add: Assoc_List.update_def Assoc_List.update_with_def Assoc_List_impl_of)
qed

lemma AL_update_update_idem:
  assumes "Assoc_List.lookup ls k = Some v"
  shows "Assoc_List.update k v (Assoc_List.update k v2 ls) = ls"
proof -
  obtain lsl where lsl: "lsl = Assoc_List.impl_of ls" by blast

  with assms have "map_of lsl k = Some v" by (simp add: Assoc_List.lookup_def)
  hence "AList.update_with_aux v k (\<lambda>_. v) (AList.update_with_aux v2 k (\<lambda>_. v2) lsl) = lsl" by (induct lsl) auto
  with lsl show ?thesis by (metis Assoc_List.update_def Assoc_List_impl_of impl_of_update_with) 
qed

lemma AL_update_delete_idem:
  assumes "Assoc_List.lookup ls k = None"
  shows "Assoc_List.delete k (Assoc_List.update k v ls) = ls"
proof -
  obtain lsl where lsl: "lsl = Assoc_List.impl_of ls" by blast

  with assms have "map_of lsl k = None" by (simp add: Assoc_List.lookup_def)
  hence "AList.delete_aux k (AList.update_with_aux v k (\<lambda>_. v) lsl) = lsl" by (induct lsl) auto
  with lsl show ?thesis by (simp add: Assoc_List.delete_def Assoc_List.update_def assoc_list.impl_of_inverse impl_of_update_with)
qed

instantiation assoc_list :: (hashable,hashable) hashable
begin
  definition "def_hashmap_size (_::('a,'b) assoc_list itself) \<equiv> (10 :: nat)"
  definition [simp]: "hashcode \<equiv> hashcode \<circ> Assoc_List.impl_of"
  instance 
    by standard (simp_all add: def_hashmap_size_assoc_list_def)
end

(*
instantiation XXX :: (hashable_uint, hashable_uint) hashable
begin
  definition hashcode_XXX :: "('a, 'b) XXX \<Rightarrow> nat" 
    where "hashcode_XXX \<equiv> hashcode_nat"

  definition bounded_hashcode_XXX :: "nat \<Rightarrow> ('a, 'b) XXX \<Rightarrow> nat" 
    where "bounded_hashcode_XXX = bounded_hashcode_nat"

  definition def_hashmap_size_XXX :: "('a, 'b) XXX itself \<Rightarrow> nat" 
    where "def_hashmap_size_XXX \<equiv> def_hashmap_size_uint"

  instance
    apply standard
    unfolding def_hashmap_size_XXX_def bounded_hashcode_XXX_def
    using hashable_from_hashable_uint by auto
end
*)

instantiation assoc_list :: (linorder,linorder) linorder
begin
  definition [simp]: "less_eq_assoc_list (a :: ('a,'b) assoc_list) (b :: ('a,'b) assoc_list) \<longleftrightarrow> lexlist (Assoc_List.impl_of a) \<le> lexlist (Assoc_List.impl_of b)"
  definition [simp]: "less_assoc_list (a :: ('a,'b) assoc_list) (b :: ('a,'b) assoc_list) \<longleftrightarrow> lexlist (Assoc_List.impl_of a) < lexlist (Assoc_List.impl_of b)"

  instance 
    apply standard 
    apply (auto)
    apply (metis assoc_list_ext lexlist_ext lexlist_def)
    done
end

(* Other instantiations for types from Main *)
(*instantiation iarray :: (linorder) linorder
begin
  definition [simp]: "less_eq_iarray (a :: 'a iarray) (b :: 'a iarray) \<longleftrightarrow> lexlist (IArray.list_of a) \<le> lexlist (IArray.list_of b)"
  definition [simp]: "less_iarray (a :: 'a iarray) (b :: 'a iarray) \<longleftrightarrow> lexlist (IArray.list_of a) < lexlist (IArray.list_of b)"

  instance 
    apply standard 
    apply auto
    apply (metis iarray.exhaust list_of.simps lexlist_ext lexlist_def)
    done
end*)
derive linorder iarray

instantiation lexlist :: (hashable) hashable
begin
  definition "def_hashmap_size_lexlist = (\<lambda>_ :: 'a lexlist itself. 2 * def_hashmap_size TYPE('a))"

  definition "hashcode_lexlist = hashcode o unlex"
  instance
  proof
    from def_hashmap_size[where ?'a = "'a"]
    show "1 < def_hashmap_size TYPE('a lexlist)"
      by(simp add: def_hashmap_size_lexlist_def)
  qed
end

text \<open>Instead of operating on the list representation of an @{const IArray}, we walk it directly,
using the indices.\<close>

primrec walk_iarray' :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a iarray \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'b" where
  "walk_iarray' _ _ x 0 _ = x"
| "walk_iarray' f a x (Suc l) p = (let y = f x (a !! p)
                                  in walk_iarray' f a y l (p + 1))"

lemma walk_iarray'_Cons:
  "walk_iarray' f (IArray (a#xs)) x l (Suc p) = walk_iarray' f (IArray xs) x l p"
  by (induct l arbitrary: p x) simp_all

definition walk_iarray :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a iarray \<Rightarrow> 'b \<Rightarrow> 'b" where
 "walk_iarray f a x = walk_iarray' f a x (IArray.length a) 0"

lemma walk_iarray_Cons:
  "walk_iarray f (IArray (a#xs)) b = walk_iarray f (IArray xs) (f b a)"
  by (simp add: walk_iarray_def walk_iarray'_Cons)

lemma walk_iarray_append:
  "walk_iarray f (IArray (xs@[x])) b = f (walk_iarray f (IArray xs) b) x"
  by (induct xs arbitrary: b) (simp add: walk_iarray_def, simp add: walk_iarray_Cons)

lemma walk_iarray_foldl':
   "walk_iarray f (IArray xs) x = foldl f x xs"
  by (induction xs rule: rev_induct) (simp add: walk_iarray_def, simp add: walk_iarray_append)

lemma walk_iarray_foldl:
  "walk_iarray f a x = foldl f x (IArray.list_of a)"
by (cases a) (simp add: walk_iarray_foldl')

instantiation iarray :: (hashable) hashable
begin
  definition [simp]: "hashcode a = foldl (\<lambda>h v. h * 33 + hashcode v) 0 (IArray.list_of a)"
  definition "def_hashmap_size = (\<lambda>_ :: 'a iarray itself. 10)"
  instance by standard (simp_all add: def_hashmap_size_iarray_def)

  lemma [code]: "hashcode a = walk_iarray (\<lambda>h v. h * 33 + hashcode v) a 0"
    by (simp add: walk_iarray_foldl)
end

(* Other instantiations for types from Main *)
instantiation array :: (linorder) linorder
begin

  definition [simp]: "less_eq_array (a :: 'a array) (b :: 'a array) \<longleftrightarrow> lexlist (list_of_array a) \<le> lexlist (list_of_array b)"
  definition [simp]: "less_array (a :: 'a array) (b :: 'a array) \<longleftrightarrow> lexlist (list_of_array a) < lexlist (list_of_array b)"

  instance 
    apply standard 
    apply auto
    apply (metis array.exhaust list_of_array.simps lexlist_ext lexlist_def)
    done
end

text \<open>Same for arrays from the ICF.\<close>
primrec walk_array' :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a array \<Rightarrow> 'b \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'b" where
  "walk_array' _ _ x 0 _ = x"
| "walk_array' f a x (Suc l) p = (let y = f x (array_get a p)
                                  in walk_array' f a y l (p + 1))"

lemma walk_array'_Cons:
  "walk_array' f (Array (a#xs)) x l (Suc p) = walk_array' f (Array xs) x l p"
  by (induct l arbitrary: p x) simp_all

definition walk_array :: "('b \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a array \<Rightarrow> 'b \<Rightarrow> 'b" where
 "walk_array f a x = walk_array' f a x (array_length a) 0"

lemma walk_array_Cons:
  "walk_array f (Array (a#xs)) b = walk_array f (Array xs) (f b a)"
  by (simp add: walk_array_def walk_array'_Cons)

lemma walk_array_append:
  "walk_array f (Array (xs@[x])) b = f (walk_array f (Array xs) b) x"
  by (induct xs arbitrary: b) (simp add: walk_array_def, simp add: walk_array_Cons)

lemma walk_array_foldl':
   "walk_array f (Array xs) x = foldl f x xs"
  by (induction xs rule: rev_induct) (simp add: walk_array_def, simp add: walk_array_append)

lemma walk_array_foldl:
  "walk_array f a x = foldl f x (list_of_array a)"
by (cases a) (simp add: walk_array_foldl')

(* TODO: Move to array.thy *)
instantiation array :: (hashable) hashable
begin
  definition [simp]: "hashcode a = foldl (\<lambda>h v. h * 33 + hashcode v) 0 (list_of_array a)"
  definition "def_hashmap_size = (\<lambda>_ :: 'a array itself. 10)"
  instance by standard (simp_all add: def_hashmap_size_array_def)

  lemma [code]: "hashcode a = walk_array (\<lambda>h v. h * 33 + hashcode v) a 0"
    by (simp add: walk_array_foldl)
end

(*subsection {* Ours *}*)

derive linorder varType
derive linorder variable

instantiation varType :: hashable
begin

  definition "def_hashmap_size_varType (_::varType itself) \<equiv> (10::nat)"
  
  fun hashcode_varType where 
    "hashcode_varType (VTBounded i1 i2) = hashcode (i1,i2)" |
    "hashcode_varType VTChan = 23"

  instance by standard (simp add: def_hashmap_size_varType_def)
end

instantiation variable :: hashable
begin
  
  definition "def_hashmap_size_variable (_::variable itself) \<equiv> (10::nat)"

  fun hashcode_variable where 
    "hashcode_variable (Var i1 i2) = hashcode (i1,i2)" |
    "hashcode_variable (VArray i1 i2 ia) = hashcode (i1,i2,ia)"

  instance by standard (simp add: def_hashmap_size_variable_def)
end

fun channel_to_tuple where
  "channel_to_tuple (Channel io vs iss) = (3::nat,io,lexlist vs, lexlist (map lexlist iss))"
| "channel_to_tuple (HSChannel vs) = (2,0,lexlist vs, lexlist [])"
| "channel_to_tuple InvChannel = (1,0,lexlist [], lexlist [])"

instantiation channel :: linorder
begin
  definition [simp]: "less_eq_channel xs ys \<longleftrightarrow> channel_to_tuple xs \<le> channel_to_tuple ys"
  definition [simp]: "less_channel xs ys \<longleftrightarrow> channel_to_tuple xs < channel_to_tuple ys"

  instance
    apply standard
    apply (auto)
    apply (case_tac x)
    apply (case_tac [!] y)
    apply (auto dest!: map_inj_on 
                intro!: inj_onI lexlist_ext 
                simp: Lex_inject lexlist_def)
    done
end

instantiation channel :: hashable
begin
  
  definition "def_hashmap_size_channel (_::channel itself) \<equiv> (10::nat)"

  fun hashcode_channel where 
    "hashcode_channel (Channel io vs iss) = hashcode (io, vs, iss)"
  | "hashcode_channel (HSChannel vs) = 42 * hashcode vs"
  | "hashcode_channel InvChannel = 4711"

  instance by standard (simp add: def_hashmap_size_channel_def)
end

function pState2HASH where
  "pState2HASH \<lparr> pid = p, vars = v, pc = c, channels = ch, idx = s, \<dots> = m \<rparr> = (p, v, c, lexlist ch, s, m)"
by (metis pState.surjective) force
termination by lexicographic_order

lemma pState2HASH_eq:
  "pState2HASH x = pState2HASH y \<Longrightarrow> x = y"
by (cases x, cases y) (auto intro: lexlist_ext simp: lexlist_def)

instantiation pState_ext :: (linorder) linorder
begin
  definition [simp]: "less_eq_pState_ext (a :: 'a pState_ext) (b :: 'a pState_ext) \<longleftrightarrow> pState2HASH a \<le> pState2HASH b"
  definition [simp]: "less_pState_ext (a :: 'a pState_ext) (b :: 'a pState_ext) \<longleftrightarrow> pState2HASH a < pState2HASH b"

  instance by standard (auto simp: pState2HASH_eq)
end

instantiation pState_ext :: (hashable) hashable
begin
  definition "def_hashmap_size_pState_ext (_::'a pState_ext itself) \<equiv> (10::nat)"
  definition [simp]: "hashcode \<equiv> hashcode \<circ> pState2HASH"

  instance by standard (simp_all add: def_hashmap_size_pState_ext_def)
end

function gState2HASH where
  "gState2HASH \<lparr> gState.vars = v, channels = ch, timeout = t, procs = p, \<dots> = m \<rparr> = (v, lexlist ch, t, lexlist p, m)"
by (metis gState.surjective) force
termination by lexicographic_order

lemma gState2HASH_eq:
  "gState2HASH x = gState2HASH y \<Longrightarrow> x = y"
by (cases x, cases y) (auto intro: lexlist_ext simp: lexlist_def)

instantiation gState_ext :: (linorder) linorder
begin
  definition [simp]: "less_eq_gState_ext (a :: 'a gState_ext) (b :: 'a gState_ext) \<longleftrightarrow> gState2HASH a \<le> gState2HASH b"
  definition [simp]: "less_gState_ext (a :: 'a gState_ext) (b :: 'a gState_ext) \<longleftrightarrow> gState2HASH a < gState2HASH b"

  instance by standard (auto simp: gState2HASH_eq)
end

instantiation gState_ext :: (hashable) hashable
begin
  definition "def_hashmap_size_gState_ext (_::'a gState_ext itself) \<equiv> (10::nat)"
  definition [simp]: "hashcode \<equiv> hashcode \<circ> gState2HASH"

  instance by standard (simp_all add: def_hashmap_size_gState_ext_def)
end

(*>*)
end
