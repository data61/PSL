------------------------------------------------------------------------
-- 
-- Module: PromelaParser.Statement
-- Author: Dennis Kraft
--
-- parser for statements
--
-- also includes a parser for send arguments, ranges, options, sequences, 
-- steps and declarations
-- 
------------------------------------------------------------------------


module Statement where


import Prelude hiding (seq)
import Basic
import Lexer
import Expression
import Syntax hiding (recvArgs, sendArgs)


-- various parsers -----------------------------------------------------


sendArgs :: Parser [Expr]
sendArgs = do
   arg <- expr
   args <- enclose (trim (symbol "(")) (trim (symbol ")")) (do
         arg <- expr
         args <- list (trim (symbol ",") >> expr)
         return (arg : args)) <|>
      list (trim (symbol ",") >> expr)
   return (arg : args)


range :: Parser Range
range = do
   v <- varRef
   (do
         trim (symbol ":")
         e1 <- expr
         trim (symbol "..")
         e2 <- expr
         return (RangeFromTo v e1 e2)) <|>
      (do
         trim (keyword "in")
         v' <- varRef
         return (RangeIn v v'))


-- steps and declarations ----------------------------------------------


opts :: Parser [[Step]]
opts = listOne (trim (symbol "::") >> seq)


seq :: Parser [Step]
seq = do
   s <- step
   ss <- list ((trim (symbol "->") <|> jump ( trim (symbol ";"))) >> step)
-- allow an extra ";" at the end of a sequence
   perhaps (trim (symbol ";"))
   return (s : ss)


step :: Parser Step
step = ((do
      hs <- perhaps (trim (keyword "hidden" <|> keyword "show"))
      convert StepDecl (decl hs) <|>
         (do
            s <- trim identifier
            case hs of
               Nothing -> convert StepDecl (udecl hs s) <|> 
                  (do
                     stmnt1 <- stmntSRALE s
                     stmnt2 <- perhaps (trim (keyword "unless") >> stmnt)
                     return (StepStmnt stmnt1 stmnt2))
               Just _ -> convert StepDecl (udecl hs s))) <||>
   fail "declaration expected") <|>
   ((do
      stmnt1 <- stmnt
      stmnt2 <- perhaps (trim (keyword "unless") >> stmnt)
      return (StepStmnt stmnt1 stmnt2)) <||>
   fail "statement expected") <|>
   (do
      trim (keyword "xr")
      v <- varRef
      vs <- list (trim (symbol ",") >> varRef)
      return (StepXR (v : vs))) <|>
   (do
      trim (keyword "xs")
      v <- varRef
      vs <- list (trim (symbol ",") >> varRef)
      return (StepXS (v : vs)))


udecl :: Maybe String -> String -> Parser Decl     
udecl hs s = do
      decl <- intDecl
      decls <- list (trim (symbol ",") >> intDecl)
      return (Decl (convert' hs) (TypeCustom s) (decl : decls))
   where convert' Nothing = Nothing
         convert' (Just "hidden") = Just False
         convert' (Just "show") = Just True


decl :: Maybe String -> Parser Decl     
decl hs = (do
      t <- trim intTypename
      decl <- intDecl
      decls <- list (trim (symbol ",") >> intDecl)
      return (Decl (convert' hs) t (decl : decls))) <|>
   (do
      t <- (trim (keyword "chan") >> return TypeChan)
      decl <- chanDecl
      decls <- list (trim (symbol ",") >> chanDecl)
      return (Decl (convert' hs) t (decl : decls))) <|>
   (do
      t <- (trim (keyword "unsigned") >> return TypeUnsigned)
      decl <- unsignedDecl
      decls <- list (trim (symbol ",") >> unsignedDecl)
      return (Decl (convert' hs) t (decl : decls))) <|>
   (do
      t <- (trim (keyword "mtype") >> return TypeMType)
      decl <- mtypeDecl
      decls <- list (trim (symbol ",") >> mtypeDecl)
      return (Decl (convert' hs) t (decl : decls)))
   where convert' Nothing = Nothing
         convert' (Just "hidden") = Just False
         convert' (Just "show") = Just True


intDecl :: Parser VarDecl
intDecl = do
   s <- trim identifier
   x <- perhaps (enclose (trim (symbol "[")) (trim (symbol "]")) (trim constant))
   e <- perhaps (trim (symbol "=") >> expr)
   return (VarDeclInt s x e)


chanDecl :: Parser VarDecl
chanDecl = do
   s <- trim identifier
   x <- perhaps (enclose (trim (symbol "[")) (trim (symbol "]")) (trim constant))
   ct <- perhaps (do
      trim (symbol "=")
      x <- enclose (trim (symbol "[")) (trim (symbol "]")) (trim constant)
      trim (keyword "of")
      trim (symbol "{")
      t <- trim typename
      ts <- list (trim (symbol ",") >> trim typename)
      trim (symbol "}")
      return (x, (t : ts)))
   return (VarDeclChan s x ct)


unsignedDecl :: Parser VarDecl
unsignedDecl = do
   s <- trim identifier
   trim (symbol ":")
   x <- trim constant
   e <- perhaps (trim (symbol "=") >> expr)
   return (VarDeclUnsigned s x e)


mtypeDecl :: Parser VarDecl
mtypeDecl = do
   s <- trim identifier
   x <- perhaps (enclose (trim (symbol "[")) (trim (symbol "]")) (trim constant))
   s' <- perhaps (trim (symbol "=") >> trim identifier)
   return (VarDeclMType s x s')


-- statements ----------------------------------------------------------


stmnt :: Parser Stmnt
stmnt = ((do
      s <- trim identifier
      stmntSRALE s) <||>
   fail "assignment expected" <|>
   fail "send expected" <|>
   fail "receive expected" <|>
   fail "labeled statement expected") <|>
   convert StmntIf (enclose (trim (keyword "if")) (trim (keyword "fi")) opts) <|>
   convert StmntDo (enclose (trim (keyword "do")) (trim (keyword "od")) opts) <|>
   (do
      trim (keyword "for")
      r <- enclose (trim (symbol "(")) (trim (symbol ")")) range
      seq' <- enclose (trim (symbol "{")) (trim (symbol "}")) seq
      return (StmntFor r seq')) <|>
   (do
      trim (keyword "atomic")
      seq' <- enclose (trim (symbol "{")) (trim (symbol "}")) seq
      return (StmntAtomic seq')) <|>
   (do
      trim (keyword "d_step")
      seq' <- enclose (trim (symbol "{")) (trim (symbol "}")) seq
      return (StmntDStep seq')) <|>
   (do
      trim (keyword "select")
      r <- enclose (trim (symbol "(")) (trim (symbol ")")) range
      return (StmntSelect r)) <|>
   convert StmntSeq (enclose (trim (symbol "{")) (trim (symbol "}")) seq) <|>
   (trim (keyword "else") >> return StmntElse) <|>
   (trim (keyword "break") >> return StmntBreak) <|>
   (do
      trim (keyword "goto")
      s <- identifier
      return (StmntGoTo s)) <|>
   (do
      trim (keyword "printf")
      trim (symbol "(")
      s <- trim string
      es <- list (trim (symbol ",") >> expr)
      trim (symbol ")")
      return (StmntPrintF s es)) <|>
   (do
      trim (keyword "printm")
      s <- enclose (trim (symbol "(")) (trim (symbol ")")) (trim identifier)
      return (StmntPrintM s)) <|>
   (do
      trim (keyword "assert") 
      e <- enclose (trim (symbol "(")) (trim (symbol ")")) expr
      return (StmntAssert e)) <|>
   ((convert StmntCond expr) <||> fail "expression expected")


stmntSRALE :: String -> Parser Stmnt
stmntSRALE s = do
   e <- perhaps (enclose (trim (symbol "[")) (trim (symbol "]")) expr)
   v <- perhaps (trim (symbol ".") >> varRef)
   case (e, v) of
      (Nothing, Nothing) -> stmntSend s e v <|> stmntRecv s e v <|> 
         stmntAssign s e v <|> convert StmntCond (stmntExprOr s e v) <|>
         stmntLabel s
      (e, v) -> stmntSend s e v <|> stmntRecv s e v <|> 
         stmntAssign s e v <|> convert StmntCond (stmntExprOr s e v)


stmntSend :: String -> Maybe Expr -> Maybe VarRef -> Parser Stmnt
stmntSend s e v = do
   (do
         trim (symbol "!!")
         args <- sendArgs
         return (StmntSortSend (VarRef s e v) args)) <|>
      (do
         trim (symbol "!")
         args <- sendArgs
         return (StmntSend (VarRef s e v) args))


stmntRecv :: String -> Maybe Expr -> Maybe VarRef -> Parser Stmnt
stmntRecv s e v = do
   (do
         args <- enclose (trim (symbol "??<")) (trim (symbol ">")) recvArgs
         return (StmntRndRecvX (VarRef s e v) args)) <|>
      (do
         args <- enclose (trim (symbol "?<")) (trim (symbol ">")) recvArgs
         return (StmntRecvX (VarRef s e v) args)) <|>
      (do
         trim (symbol "??")
         args <- recvArgs
         return (StmntRndRecv (VarRef s e v) args)) <|>
      (do
         trim (symbol "?")
         args <- recvArgs
         return (StmntRecv (VarRef s e v) args))


stmntAssign :: String -> Maybe Expr -> Maybe VarRef -> Parser Stmnt
stmntAssign s e v = do
   (do
         trim (symbol "=")
         e' <- expr
         return (StmntAssign (VarRef s e v) e')) <|>
      (do
         trim (symbol "++")
         return (StmntIncr (VarRef s e v))) <|>
      (do
         trim (symbol "--")
         return (StmntDecr (VarRef s e v)))


stmntLabel :: String -> Parser Stmnt
stmntLabel s = do
   trim (symbol ":")
   stmnt' <- stmnt
   return (StmntLabeled s stmnt')


-- operator precedence hierarchy for statement expression --------------


stmntExprOr :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
stmntExprOr s e v = do
   e' <- stmntExprAnd s e v
   es <- list (do
      trim (op "||")
      exprAnd)
   return (foldl (ExprBinOp BinOpOr) e' es)


stmntExprAnd :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
stmntExprAnd s e v = do
   e' <- stmntExprBitOr s e v
   es <- list (do
      trim (op "&&")
      exprBitOr)
   return (foldl (ExprBinOp BinOpAnd) e' es)


stmntExprBitOr :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
stmntExprBitOr s e v = do
   e' <- stmntExprBitXor s e v
   es <- list (do
      trim (op "|")
      exprBitXor)
   return (foldl (ExprBinOp BinOpBitOr) e' es)


stmntExprBitXor :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
stmntExprBitXor s e v = do
   e' <- stmntExprBitAnd s e v
   es <- list (do
      trim (op "^")
      exprBitAnd)
   return (foldl (ExprBinOp BinOpBitXor) e' es)


stmntExprBitAnd :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
stmntExprBitAnd s e v = do
   e' <- stmntExprEq s e v
   es <- list (do
      trim (op "&")
      exprEq)
   return (foldl (ExprBinOp BinOpBitAnd) e' es)


stmntExprEq :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
stmntExprEq s e v = do
   e' <- stmntExprGL s e v
   es <- list (do
      s <- trim (op "==" <|> op "!=")
      e'' <- exprGL
      return (s, e''))
   return (myfoldl e' es)
   where myfoldl e [] = e
         myfoldl e (("==", e') : es) = myfoldl (ExprBinOp BinOpEq e e') es
         myfoldl e (("!=", e') : es) = myfoldl (ExprBinOp BinOpNEq e e') es


stmntExprGL :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
stmntExprGL s e v = do
   e' <- stmntExprShift s e v
   es <- list (do
      s <- trim (op "<" <|> op "<=" <|> op ">=" <|> op ">")
      e'' <- exprShift
      return (s, e''))
   return (myfoldl e' es)
   where myfoldl e [] = e
         myfoldl e (("<", e') : es) = myfoldl (ExprBinOp BinOpLe e e') es
         myfoldl e (("<=", e') : es) = myfoldl (ExprBinOp BinOpLEq e e') es
         myfoldl e ((">=", e') : es) = myfoldl (ExprBinOp BinOpGEq e e') es
         myfoldl e ((">", e') : es) = myfoldl (ExprBinOp BinOpGr e e') es


stmntExprShift :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
stmntExprShift s e v = do
   e' <- stmntExprAdd s e v
   es <- list (do
      s <- trim (op "<<" <|> op ">>")
      e'' <- exprAdd
      return (s, e''))
   return (myfoldl e' es)
   where myfoldl e [] = e
         myfoldl e (("<<", e') : es) = myfoldl (ExprBinOp BinOpShiftL e e') es
         myfoldl e ((">>", e') : es) = myfoldl (ExprBinOp BinOpShiftR e e') es


stmntExprAdd :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
stmntExprAdd s e v = do
   e' <- stmntExprMul s e v
   es <- list (do
      s <- trim (op "+" <|> op "-")
      e'' <- exprMul
      return (s, e''))
   return (myfoldl e' es)
   where myfoldl e [] = e
         myfoldl e (("+", e') : es) = myfoldl (ExprBinOp BinOpAdd e e') es
         myfoldl e (("-", e') : es) = myfoldl (ExprBinOp BinOpSub e e') es


stmntExprMul :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
stmntExprMul s e v = do
   e' <- exprVarPoll s e v <|> case v of
      Nothing -> exprRemote s e
      _ -> fail ""
   es <- list (do
      s <- trim (op "*" <|> op "/" <|> op "%")
      e'' <- exprUn
      return (s, e''))
   return (myfoldl e' es)
   where myfoldl e [] = e
         myfoldl e (("*", e') : es) = myfoldl (ExprBinOp BinOpMul e e') es
         myfoldl e (("/", e') : es) = myfoldl (ExprBinOp BinOpDiv e e') es
         myfoldl e (("%", e') : es) = myfoldl (ExprBinOp BinOpMod e e') es

