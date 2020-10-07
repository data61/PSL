------------------------------------------------------------------------
-- 
-- Module: PromelaParser.Expression
-- Author: Dennis Kraft
--
-- parser for expressions
--
-- also includes a parser for variable references, receive arguments
-- and priorities
-- 
------------------------------------------------------------------------


module Expression where


import Prelude
import Basic
import Lexer
import Syntax hiding (recvArgs)


expr :: Parser Expr
expr = exprOr


-- various parsers -----------------------------------------------------


varRef :: Parser VarRef
varRef = (do
   s <- trim identifier
   e <- perhaps (enclose (trim (symbol "[")) (trim (symbol "]")) expr)
   v <- perhaps (trim (symbol ".") >> varRef)
   return (VarRef s e v)) <||> fail "variable reference expected"


args :: Parser [Expr]
args = do
   e <- expr
   es <- list (trim (symbol ",") >> expr)
   return (e : es)


recvArg :: Parser RecvArg
recvArg = convert RecvArgVar varRef <|>
   (do
      trim (keyword "eval")
      e <- enclose (trim (symbol "(")) (trim (symbol ")")) expr
      return (RecvArgEval e)) <|>
   (do
      trim (op "-")
      x <- trim constant
      return (RecvArgConst (-x))) <|>
   convert RecvArgConst (trim constant) <||>
   fail "receive argument expected"


recvArgs :: Parser [RecvArg]
recvArgs = do
   arg <- recvArg
   args <- enclose (trim (symbol "(")) (trim (symbol ")")) (do
         arg <- recvArg
         args <- list (trim (symbol ",") >> recvArg)
         return (arg : args)) <|>
      list (trim (symbol ",") >> recvArg)
   return (arg : args)


priority :: Parser Integer
priority = (trim (keyword "priority") >> trim constant)


-- operator precedence hierarchy ---------------------------------------


exprOr :: Parser Expr
exprOr = do
   e <- exprAnd
   es <- list (do
      trim (op "||")
      exprAnd)
   return (foldl (ExprBinOp BinOpOr) e es)


exprAnd :: Parser Expr
exprAnd = do
   e <- exprBitOr
   es <- list (do
      trim (op "&&")
      exprBitOr)
   return (foldl (ExprBinOp BinOpAnd) e es)


exprBitOr :: Parser Expr
exprBitOr = do
   e <- exprBitXor
   es <- list (do
      trim (op "|")
      exprBitXor)
   return (foldl (ExprBinOp BinOpBitOr) e es)


exprBitXor :: Parser Expr
exprBitXor = do
   e <- exprBitAnd
   es <- list (do
      trim (op "^")
      exprBitAnd)
   return (foldl (ExprBinOp BinOpBitXor) e es)


exprBitAnd :: Parser Expr
exprBitAnd = do
   e <- exprEq
   es <- list (do
      trim (op "&")
      exprEq)
   return (foldl (ExprBinOp BinOpBitAnd) e es)


exprEq :: Parser Expr
exprEq = do
   e <- exprGL
   es <- list (do
      s <- trim (op "==" <|> op "!=")
      e' <- exprGL
      return (s, e'))
   return (myfoldl e es)
   where myfoldl e [] = e
         myfoldl e (("==", e') : es) = myfoldl (ExprBinOp BinOpEq e e') es
         myfoldl e (("!=", e') : es) = myfoldl (ExprBinOp BinOpNEq e e') es


exprGL :: Parser Expr
exprGL = do
   e <- exprShift
   es <- list (do
      s <- trim (op "<" <|> op "<=" <|> op ">=" <|> op ">")
      e' <- exprShift
      return (s, e'))
   return (myfoldl e es)
   where myfoldl e [] = e
         myfoldl e (("<", e') : es) = myfoldl (ExprBinOp BinOpLe e e') es
         myfoldl e (("<=", e') : es) = myfoldl (ExprBinOp BinOpLEq e e') es
         myfoldl e ((">=", e') : es) = myfoldl (ExprBinOp BinOpGEq e e') es
         myfoldl e ((">", e') : es) = myfoldl (ExprBinOp BinOpGr e e') es


exprShift :: Parser Expr
exprShift = do
   e <- exprAdd
   es <- list (do
      s <- trim (op "<<" <|> op ">>")
      e' <- exprAdd
      return (s, e'))
   return (myfoldl e es)
   where myfoldl e [] = e
         myfoldl e (("<<", e') : es) = myfoldl (ExprBinOp BinOpShiftL e e') es
         myfoldl e ((">>", e') : es) = myfoldl (ExprBinOp BinOpShiftR e e') es


exprAdd :: Parser Expr
exprAdd = do
   e <- exprMul
   es <- list (do
      s <- trim (op "+" <|> op "-")
      e' <- exprMul
      return (s, e'))
   return (myfoldl e es)
   where myfoldl e [] = e
         myfoldl e (("+", e') : es) = myfoldl (ExprBinOp BinOpAdd e e') es
         myfoldl e (("-", e') : es) = myfoldl (ExprBinOp BinOpSub e e') es


exprMul :: Parser Expr
exprMul = do
   e <- exprUn
   es <- list (do
      s <- trim (op "*" <|> op "/" <|> op "%")
      e' <- exprUn
      return (s, e'))
   return (myfoldl e es)
   where myfoldl e [] = e
         myfoldl e (("*", e') : es) = myfoldl (ExprBinOp BinOpMul e e') es
         myfoldl e (("/", e') : es) = myfoldl (ExprBinOp BinOpDiv e e') es
         myfoldl e (("%", e') : es) = myfoldl (ExprBinOp BinOpMod e e') es


exprUn :: Parser Expr
exprUn = convert (ExprUnOp UnOpNeg) (trim (op "!") >> exprUn) <|>
   convert (ExprUnOp UnOpMinus) (trim (op "-") >> exprUn) <|>
   convert (ExprUnOp UnOpComp) (trim (op "~") >> exprUn) <||>
   exprBase


-- basic expressions ---------------------------------------------------


exprBase :: Parser Expr
exprBase = (enclose (trim (symbol "(")) (trim (symbol ")")) (do
      e1 <- expr
      cond <- perhaps (do
         trim (symbol "->")
         e2 <- expr
         trim (symbol ":")
         e3 <- expr
         return (e2, e3))
      case cond of
         Nothing -> return e1
         Just (e2, e3) -> return (ExprCond e1 e2 e3)) <||>
   fail "expression expected" <|> 
   fail "conditional expression expected") <|>
   ((do
      s <- trim identifier
      e <- perhaps (enclose (trim (symbol "[")) (trim (symbol "]")) expr)
      v <- perhaps (trim (symbol ".") >> varRef)
      exprVarPoll s e v <|> case v of
         Nothing -> exprRemote s e
         _ -> fail "") <||>
   fail "variable reference expected" <|> 
   fail "poll expected" <|>
   fail "remote reference expected") <|>
   convert ExprConst (trim constant) <|>
   (do
      trim (keyword "len")
      v <- enclose (trim (symbol "(")) (trim (symbol ")")) varRef
      return (ExprLen v)) <|>
   (trim (keyword "timeout") >> return ExprTimeout) <|>
   (trim (keyword "np_") >> return ExprNP) <|>
   (do
      trim (keyword "enabled")
      e <- enclose (trim (symbol "(")) (trim (symbol ")")) expr
      return (ExprEnabled e)) <|>
   (do
      trim (keyword "pc_value")
      e <- enclose (trim (symbol "(")) (trim (symbol ")")) expr
      return (ExprPC e)) <|>
   (do
      trim (keyword "run")
      s <- trim identifier
      args <- enclose (trim (symbol "(")) (trim (symbol ")")) (args <|> return [])
      p <- perhaps priority
      return (ExprRun s args p)) <|>
   (do
      trim (keyword "get_priority")
      e <- enclose (trim (symbol "(")) (trim (symbol ")")) chanPollExpr
      return (ExprGetPriority e)) <|>
   (do
      trim (keyword "set_priority")
      trim (trim (symbol "("))
      e1 <- chanPollExpr
      trim (trim (symbol ","))
      e2 <- chanPollExpr
      trim (trim (symbol ")"))
      return (ExprSetPriority e1 e2))


exprVarPoll :: String -> Maybe Expr -> Maybe VarRef -> Parser Expr
exprVarPoll s e v = do
   (do
         args <- enclose (trim (symbol "??[")) (trim (symbol "]")) recvArgs
         return (ExprRndPoll (VarRef s e v) args)) <|>
      (do
         args <- enclose (trim (symbol "?[")) (trim (symbol "]")) recvArgs
         return (ExprPoll (VarRef s e v) args)) <|>
      return (ExprVarRef (VarRef s e v))


exprRemote :: String -> Maybe Expr -> Parser Expr
exprRemote s e = do
   trim (symbol "@")
   label <- trim identifier
   return (ExprRemoteRef s e label)


-- chan poll expressions -----------------------------------------------


chanPollExpr :: Parser Expr
chanPollExpr = chanPollExprOr


chanPollExprOr :: Parser Expr
chanPollExprOr = do
   e <- chanPollExprAnd
   es <- list (do
      trim (op "||")
      chanPollExprAnd)
   return (foldl (ExprBinOp BinOpOr) e es)


chanPollExprAnd :: Parser Expr
chanPollExprAnd = do
   e <- chanPollExprBase
   es <- list (do
      trim (op "&&")
      chanPollExprBase)
   return (foldl (ExprBinOp BinOpAnd) e es)


chanPollExprBase :: Parser Expr
chanPollExprBase = (enclose (trim (symbol "(")) (trim (symbol ")")) chanPollExpr <||>
   fail "channel poll expression expected") <|>
   (do
      trim (keyword "full")
      v <- enclose (trim (symbol "(")) (trim (symbol ")")) varRef
      return (ExprFull  v)) <|>
   (do
      trim (keyword "empty")
      v <- enclose (trim (symbol "(")) (trim (symbol ")")) varRef
      return (ExprEmpty  v)) <|>
   (do
      trim (keyword "nfull")
      v <- enclose (trim (symbol "(")) (trim (symbol ")")) varRef
      return (ExprNFull  v)) <|>
   (do
      trim (keyword "nempty")
      v <- enclose (trim (symbol "(")) (trim (symbol ")")) varRef
      return (ExprNEmpty  v)) <|>
   exprBitOr

