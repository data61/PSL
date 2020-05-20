------------------------------------------------------------------------
-- 
-- Module: PromelaParser.Syntax
-- Author: Dennis Kraft
--
-- data structure for storing a promela program
-- 
------------------------------------------------------------------------


module Syntax where


data Module = ProcType
      { procActive :: Maybe (Maybe Integer)
      , procName :: String
      , procDecls :: [Decl]
      , procPriority :: Maybe Integer
      , procProvided :: Maybe Expr
      , procSeq :: [Step] }
   | DProcType
      { dProcActive :: Maybe (Maybe Integer)
      , dProcName :: String
      , dProcDecls :: [Decl]
      , dProcPriority :: Maybe Integer
      , dProcProvided :: Maybe Expr
      , dProcSeq :: [Step] }
   | Init
      { initPriority :: Maybe Integer
      , initSteq :: [Step] }
   | Never [Step]
   | Trace [Step]
   | NoTrace [Step]
   | TypeDef
      { typeDefName :: String
      , typeDefDecls :: [Decl] }
   | MType [String]
   | ModuDecl Decl
   deriving (Eq)


instance Show Module
   where show m = case m of
               ProcType act name decls prio prov seq ->
                  f act ++ "proctype " ++ name ++ "(" ++ g decls ++ 
                  ") " ++ h prio ++ i prov ++ "{" ++ j seq ++ "}"
               DProcType act name decls prio prov seq ->
                  f act ++ "D_proctype " ++ name ++ "(" ++ g decls ++ 
                  ") " ++ h prio ++ i prov ++ "{" ++ j seq ++ "} "
               Init prio seq ->
                  "init " ++ h prio ++ "{" ++ j seq ++ "}"
               Never seq -> "never {" ++ j seq ++ "}"
               Trace seq -> "trace {" ++ j seq ++ "}"
               NoTrace seq -> "notrace {" ++ j seq ++ "}"
               TypeDef name decls -> 
                  "typedef " ++ name ++ " {" ++ g decls ++ "}"
               MType ids -> "mtype {" ++ k ids ++ "}"
               ModuDecl decl -> show decl
            where f Nothing = ""
                  f (Just Nothing) = "active "
                  f (Just (Just x)) = "active[" ++ show x ++ "] "
                  g [] = ""
                  g [decl] = show decl
                  g (decl : decls) = show decl ++ "; " ++ g decls
                  h Nothing = ""
                  h (Just x) = "priority " ++ show x ++ " "
                  i Nothing = ""
                  i (Just expr) = "provided(" ++ show expr ++ ") "
                  j [] = ""
                  j [step] = show step
                  j (step : steps) = show step ++ "; " ++ j steps
                  k [] = ""
                  k [id] = id
                  k (id : ids) = id ++ ", " ++ k ids


data Type = TypeBit
   | TypeBool
   | TypeByte
   | TypePid
   | TypeShort
   | TypeInt
   | TypeMType
   | TypeChan
   | TypeUnsigned
   | TypeCustom String
   deriving (Eq)


instance Show Type
   where show TypeBit = "bit"
         show TypeBool = "bool"
         show TypeByte = "byte"
         show TypePid = "pid"
         show TypeShort = "short"
         show TypeInt = "int"
         show TypeMType = "mtype"
         show TypeChan = "chan"
         show TypeUnsigned = "unsigned"
         show (TypeCustom name) = name


data VarRef = VarRef
      { varRefName :: String
      , varRefIndex :: Maybe Expr
      , varRefNext :: Maybe  VarRef }
   deriving (Eq)


instance Show VarRef
   where show (VarRef name index next) = name ++ f index ++ g next
            where f Nothing = ""
                  f (Just e) = "[" ++ show e ++ "]"
                  g Nothing = ""
                  g (Just v) = "." ++ show v


data RecvArg = RecvArgVar VarRef
   | RecvArgEval Expr
   | RecvArgConst Integer
   deriving (Eq)


instance Show RecvArg
   where show (RecvArgVar var) = show var
         show (RecvArgEval expr) = "eval(" ++ show expr ++ ")"
         show (RecvArgConst x) = show x 


data Decl = Decl
      { declVisible :: Maybe Bool
      , declType :: Type
      , declVars :: [VarDecl] }
   deriving (Eq)


instance Show Decl
   where show (Decl vis t vdecls) = f vis ++ show t ++ " " ++ g vdecls
            where f Nothing = ""
                  f (Just True) = "show "
                  f (Just False) = "hidden "
                  g [] = ""
                  g [vdecl] = show vdecl
                  g (vdecl : vdecls) = show vdecl ++ ", " ++ g vdecls 


data VarDecl = VarDeclInt
      { intName :: String
      , intArraysize :: Maybe Integer
      , intVal :: Maybe Expr }
   | VarDeclChan
      { chanName :: String
      , chanArraysize :: Maybe Integer
      , chanCapAndType :: Maybe (Integer, [Type]) }
   | VarDeclUnsigned
      { unsigName :: String
      , unsigBits :: Integer
      , unsigVal :: Maybe Expr }
   | VarDeclMType
      { mTypeName :: String
      , mTypeArraysize :: Maybe Integer
      , mTypeVal :: Maybe String }
   deriving (Eq)


instance Show VarDecl
   where show (VarDeclInt name array val) = 
            name ++ f array ++ g val
            where f Nothing = ""
                  f (Just x) = "[" ++ show x ++ "]"
                  g Nothing = ""
                  g (Just e) = " = " ++ show e
         show (VarDeclChan name array val) = 
            name ++ f array ++ g val
            where f Nothing = ""
                  f (Just x) = "[" ++ show x ++ "]"
                  g Nothing = ""
                  g (Just (x, ts)) = " = [" ++ show x ++ 
                     "] of {" ++ g' ts ++ "}"
                     where g' [] = ""
                           g' [t] = show t
                           g' (t : ts) = show t ++ ", " ++ g' ts
         show (VarDeclUnsigned name bitnum val) = 
            name ++ ":" ++ show bitnum ++ f val
            where f Nothing = ""
                  f (Just e) = " = " ++ show e
         show (VarDeclMType name array val) = 
            name ++ f array ++ g val
            where f Nothing = ""
                  f (Just x) = "[" ++ show x ++ "]"
                  g Nothing = ""
                  g (Just id) = " = " ++ show id


data Step = StepStmnt Stmnt (Maybe Stmnt)
   | StepDecl Decl
   | StepXR [VarRef]
   | StepXS [VarRef]
   deriving (Eq)


instance Show Step
   where show (StepStmnt stmnt1 Nothing) = show stmnt1
         show (StepStmnt stmnt1 (Just stmnt2)) = show stmnt1 ++ " unless " ++ show stmnt2
         show (StepDecl decl) = show decl
         show x = case x of
               StepXR vs -> "xr " ++ f vs
               StepXS vs -> "xs " ++ f vs
            where f [] = ""
                  f [v] = show v
                  f (v : vs) = show v ++ ", " ++ f vs
 

data Range = RangeFromTo
      { rangeVar :: VarRef
      , rangeFrom :: Expr
      , rangeTo :: Expr }
   | RangeIn VarRef VarRef
   deriving (Eq)


instance Show Range
   where show (RangeFromTo v e1 e2) = show v ++ ": " ++ show e1 ++ " .. " ++ show e2
         show (RangeIn v1 v2) = show v1 ++ " in " ++ show v2
 

data Stmnt = StmntIf [[Step]]
   | StmntDo [[Step]]
   | StmntFor
      { forRange :: Range
      , forSteps :: [Step] }
   | StmntAtomic [Step]
   | StmntDStep [Step]
   | StmntSelect Range
   | StmntSeq [Step]
   | StmntSend
      { sendVar :: VarRef
      , sendArgs :: [Expr] }
   | StmntSortSend
      { sortSendVar :: VarRef
      , sortSendArgs :: [Expr] }
   | StmntRecv
      { recvVar :: VarRef
      , recvArgs :: [RecvArg] }
   | StmntRndRecv
      { rndRecvVar :: VarRef
      , rndRecvArgs :: [RecvArg] }
   | StmntRecvX
      { recvXVar :: VarRef
      , recvXArgs :: [RecvArg] }
   | StmntRndRecvX
      { rndRecvXVar :: VarRef
      , rndRecvXArgs :: [RecvArg] }
   | StmntAssign
      { assignVar :: VarRef
      , assignExpr :: Expr }
   | StmntIncr VarRef
   | StmntDecr VarRef
   | StmntElse
   | StmntBreak
   | StmntGoTo String
   | StmntLabeled
      { labelName :: String
      , labelStmnt :: Stmnt }
   | StmntPrintF
      { printText :: String
      , printArgs :: [Expr] }
   | StmntPrintM String
   | StmntAssert Expr
   | StmntCond Expr
   deriving (Eq)

instance Show Stmnt
   where show stmnt = case stmnt of
               StmntIf opts -> "if" ++ (concat (map (("\n:: " ++) . f) opts)) ++ "\nfi"
               StmntDo opts -> "do" ++ (concat (map (("\n:: " ++) . f) opts)) ++ "\nod"
               StmntFor range steps -> "for(" ++ show range ++ ") {" ++ f steps ++ "}"
               StmntAtomic steps -> "atomic {" ++ f steps ++ "}"
               StmntDStep steps -> "d_step {" ++ f steps ++ "}"
               StmntSelect range -> "select(" ++ show range ++ ")"
               StmntSeq steps -> "{" ++ f steps ++ "}"
               StmntSend v exprs -> show v ++ " ! " ++ g exprs
               StmntSortSend v exprs -> show v ++ " !! " ++ g exprs
               StmntRecv v recvArgs -> show v ++ " ? " ++ h recvArgs
               StmntRndRecv v recvArgs -> show v ++ " ?? " ++ h recvArgs
               StmntRecvX v recvArgs -> show v ++ " ? <" ++ h recvArgs ++ ">"
               StmntRndRecvX v recvArgs -> show v ++ " ?? <" ++ h recvArgs ++ ">"
               StmntAssign v expr -> show v ++ " = " ++ show expr
               StmntIncr v -> show v ++ "++"
               StmntDecr v -> show v ++ "--"
               StmntElse -> "else"
               StmntBreak -> "break"
               StmntGoTo id -> "goto " ++ id
               StmntLabeled id stmnt -> id ++ ": " ++ show stmnt
               StmntPrintF s exprs -> "printf(\"" ++  s ++ "\"" ++ (case exprs of
                  [] -> ""
                  exprs -> ", " ++ g exprs) ++ ")"
               StmntPrintM id -> "printm(" ++ id ++ ")"
               StmntAssert expr -> "assert(" ++ show expr ++ ")"
               StmntCond expr -> show expr
            where f [] = ""
                  f [step] = show step
                  f (step : steps) = show step ++ "; " ++ f steps
                  g [] = ""
                  g [expr] = show expr
                  g (expr : exprs) = show expr ++ ", " ++ g exprs
                  h [] = ""
                  h [recvArg] = show recvArg
                  h (recvArg : recvArgs) = show recvArg ++ ", " ++ h recvArgs


data BinOp = BinOpAdd
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
   deriving (Eq)


instance Show BinOp
   where show BinOpAdd = "+"
         show BinOpSub = "-"
         show BinOpMul = "*"
         show BinOpDiv = "/"
         show BinOpMod = "%"
         show BinOpBitAnd = "&"
         show BinOpBitXor = "^"
         show BinOpBitOr = "|"
         show BinOpGr = ">"
         show BinOpLe = "<"
         show BinOpGEq = ">="
         show BinOpLEq = "<="
         show BinOpEq = "=="
         show BinOpNEq = "!="
         show BinOpShiftL = "<<"
         show BinOpShiftR = ">>"
         show BinOpAnd = "&&"
         show BinOpOr = "||"


data UnOp = UnOpComp
   | UnOpMinus
   | UnOpNeg
   deriving (Eq)


instance Show UnOp
   where show UnOpNeg = "!"
         show UnOpMinus = "-"
         show UnOpComp = "~"


data Expr = ExprBinOp BinOp Expr Expr
   | ExprUnOp UnOp Expr
   | ExprCond
      { cond :: Expr
      , condTCase :: Expr
      , condFCase :: Expr }
   | ExprLen  VarRef
   | ExprPoll
      { pollVarRef ::  VarRef
      , pollArgs :: [RecvArg] }
   | ExprRndPoll
      { rndPollVarRef ::  VarRef
      , rndPollArgs :: [RecvArg] }
   | ExprVarRef VarRef
   | ExprConst Integer
   | ExprTimeout
   | ExprNP
   | ExprEnabled Expr
   | ExprPC Expr
   | ExprRemoteRef
      { remoteName :: String
      , remoteInstNum :: Maybe Expr
      , remoteLabel :: String }
   | ExprRun
      { runName :: String
      , runArgs :: [Expr]
      , runPriority :: Maybe Integer }
   | ExprGetPriority Expr
   | ExprSetPriority Expr Expr
   | ExprFull  VarRef
   | ExprEmpty  VarRef
   | ExprNFull  VarRef
   | ExprNEmpty  VarRef
   deriving (Eq)


instance Show Expr
   where show (ExprBinOp op expr1 expr2) = 
          "(" ++ show expr1 ++ " " ++ show op ++ " " ++ show expr2 ++ ")"
         show (ExprUnOp op expr) = "(" ++ show op ++ show expr ++ ")"
         show (ExprCond expr1 expr2 expr3) = "(" ++ show expr1 ++ " -> " ++ show expr2 ++
            " : " ++ show expr3 ++ ")"
         show (ExprLen v) = "len(" ++ show v ++ ")"
         show (ExprPoll v recvArgs) = show v ++ " ? [" ++ f recvArgs ++ "]"
            where f [] = ""
                  f [recvArg] = show recvArg
                  f (recvArg : recvArgs) = show recvArg ++ ", " ++ f recvArgs
         show (ExprRndPoll v recvArgs) = show v ++ " ?? [" ++ f recvArgs ++ "]"
            where f [] = ""
                  f [recvArg] = show recvArg
                  f (recvArg : recvArgs) = show recvArg ++ ", " ++ f recvArgs
         show (ExprVarRef v) = show v
         show (ExprConst x) = show x
         show ExprTimeout = "timeout"
         show ExprNP = "np_"
         show (ExprEnabled expr) = "enabled(" ++ show expr ++ ")"
         show (ExprPC expr) = "pc_value(" ++ show expr ++ ")"
         show (ExprRemoteRef id instnum lable) = id ++ f instnum ++ " @ " ++ lable
            where f Nothing = ""
                  f (Just x) = "[" ++ show x ++ "]"
         show (ExprRun id exprs prio) = "run " ++ id ++ "(" ++ f exprs ++ ")" ++ g prio
            where f [] = ""
                  f [expr] = show expr
                  f (expr : exprs) = show expr ++ ", " ++ f exprs
                  g Nothing = ""
                  g (Just x) = " priority " ++ show x
         show (ExprGetPriority expr) = "get_priority(" ++ show expr ++ ")"
         show (ExprSetPriority expr1 expr2) = 
            "set_priority(" ++ show expr1 ++ ", "  ++ show expr2 ++ ")"
         show (ExprFull v) = "full(" ++ show v ++ ")"
         show (ExprEmpty v) = "empty(" ++ show v ++ ")"
         show (ExprNFull v) = "nfull(" ++ show v ++ ")"
         show (ExprNEmpty v) = "nempty(" ++ show v ++ ")"

