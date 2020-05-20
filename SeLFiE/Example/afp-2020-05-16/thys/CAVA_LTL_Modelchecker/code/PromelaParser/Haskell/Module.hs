------------------------------------------------------------------------
-- 
-- Module: PromelaParser.Module
-- Author: Dennis Kraft
--
-- parser for modules
-- 
------------------------------------------------------------------------


module Module where


import Prelude hiding (seq)
import Basic
import Lexer
import Expression
import Statement
import Syntax hiding (recvArgs, sendArgs)


-- module parsers ------------------------------------------------------


program :: Parser [Module]
program = do
   space
   listAll (do
      m <- modu
-- allow an extra ";" at the end of a module
      perhaps (trim (symbol ";"))
      return m)


modu :: Parser Module
modu = (do
      a <- perhaps (do
         (trim (keyword "active"))
         perhaps (enclose (trim (symbol "[")) (trim (symbol "]")) (trim constant)))
      proctype a <|> dproctype a) <|>
   (do
      trim (keyword "init")
      p <- perhaps priority
      seq' <- enclose (trim (symbol "{")) (trim (symbol "}")) seq
      return (Init p seq')) <|>
   (do
      trim (keyword "never")
      seq' <- enclose (trim (symbol "{")) (trim (symbol "}")) seq
      return (Never seq')) <|>
   (do
      trim (keyword "trace")
      seq' <- enclose (trim (symbol "{")) (trim (symbol "}")) seq
      return (Trace seq')) <|>
   (do
      trim (keyword "notrace")
      seq' <- enclose (trim (symbol "{")) (trim (symbol "}")) seq
      return (NoTrace seq')) <|>
   (do
      trim (keyword "typedef")
      s <- trim identifier
      ds <- enclose (trim (symbol "{")) (trim (symbol "}")) decls
      return (TypeDef s ds)) <|>
   (do
      trim (keyword "mtype")
      perhaps (trim (symbol "="))
      trim (symbol "{")
      s <- trim identifier
      ss <- list (trim (symbol ",") >> trim identifier)
      trim (symbol "}")
      return (MType (s : ss))) <|>
   convert ModuDecl moduDecl


proctype :: Maybe (Maybe Integer) -> Parser Module
proctype a = do
      trim (keyword "proctype")
      s <- trim identifier
      ds <- enclose (trim (symbol "(")) (trim (symbol ")")) (decls <|> return [])
      p <- perhaps priority
      e <- perhaps (do
         trim (keyword "provided")
         enclose (trim (symbol "(")) (trim (symbol ")")) expr)
      seq' <- enclose (trim (symbol "{")) (trim (symbol "}")) seq
      return (ProcType a s ds p e seq')


dproctype :: Maybe (Maybe Integer) -> Parser Module
dproctype a = do
      trim (keyword "D_proctype")
      s <- trim identifier
      ds <- enclose (trim (symbol "(")) (trim (symbol ")")) (decls <|> return [])
      p <- perhaps priority
      e <- perhaps (do
         trim (keyword "provided")
         enclose (trim (symbol "(")) (trim (symbol ")")) expr)
      seq' <- enclose (trim (symbol "{")) (trim (symbol "}")) seq
      return (DProcType a s ds p e seq')


decls :: Parser [Decl]
decls = (do
      d <- moduDecl
      ds <- list ( jump ( trim (symbol ";")) >> moduDecl)
-- allow an extra ";" at the end of a declaration list
      perhaps (trim (symbol ";"))
      return (d : ds)) <||>
   fail "declaration list expected"


moduDecl :: Parser Decl
moduDecl = (do
      hs <- perhaps (trim (keyword "hidden" <|> keyword "show"))
      decl hs <|>
         (do
            s <- trim identifier
            udecl hs s)) <||> 
   fail "declaration expected"

