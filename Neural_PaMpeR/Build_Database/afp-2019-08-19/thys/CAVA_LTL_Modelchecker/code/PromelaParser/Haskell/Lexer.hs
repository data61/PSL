------------------------------------------------------------------------
-- 
-- Module: PromelaParser.Lexer
-- Author: Dennis Kraft
--
-- parser for lexicographic analysis
-- 
------------------------------------------------------------------------


module Lexer where


import Prelude
import Data.Char
import Data.Set
import Basic
import Syntax


-- keyword set ---------------------------------------------------------


keywordSet :: Set String
keywordSet = fromList ["active",
   "assert", 
   "atomic",
   "bit",
   "bool",
   "break",
   "byte",
   "chan",
   "D_proctype",
   "d_step",
   "do",
   "else",
   "empty",
   "enabled",
   "eval",
   "false",
   "fi",
   "for",
   "full",
   "get_priority",
   "goto",
   "hidden",
   "if",
   "in",
   "init",
   "int",
   "len",
   "mtype",
   "nempty",
   "never",
   "nfull",
   "notrace",
   "np_",
   "od",
   "of",
   "pc_value",
   "pid",
   "printf",
   "printm",
   "priority",
   "proctype",
   "provided",
   "run",
   "set_priority",
   "select",
   "short",
   "show",
   "skip",
   "timeout",
   "trace",
   "true",
   "typedef",
   "unless",
   "unsigned",
   "xr",
   "xs"]


-- lexicographic parsers -----------------------------------------------


alpha :: Parser Char
alpha = satisfy (\c -> isAlpha c || c == '_')


digit :: Parser Char
digit = satisfy isDigit


keyword :: String -> Parser String
keyword s = try ((do
      cs <- listOne alpha
      if s == cs 
         then return s 
         else fail ("keyword '" ++ s ++ "' expected")) <|>
   fail ("keyword '" ++ s ++ "' expected"))


identifier :: Parser String
identifier = try ((do
      c <- alpha
      cs <- list (alpha <|> digit)
      if member (c : cs) keywordSet 
         then fail ("identifier expected but keyword '" ++ (c : cs) ++ "' found")
         else return (c : cs)) <|> 
   fail "identifier expected")


number :: Parser Integer
number = convert (f 0) (listOne digit) <|> fail "number expected"
   where f acc [] = acc
         f acc (c : cs) = f (10 * acc + (toInteger $ digitToInt c)) cs


constant :: Parser Integer
constant = number <|> 
   (keyword "true" >> return 1) <|> 
   (keyword "false" >> return 0) <|> 
   (keyword "skip" >> return 1) <||>
   fail "constant expected"


space :: Parser Char
space = list (satisfy isSpace <|> comment) >> return ' '


comment :: Parser Char
comment = items "/*" >> ((p >> return ' ') <|> fail "open comment")
   where p = try (do
            list (satisfy (not . (== '*')) <|> try (do
               listOne (item '*')
               satisfy (not . (== '/'))
               return ' '))
            do
               listOne (item '*')
               item '/'
               return ' '
            return ' ')


trim :: Parser a -> Parser a
trim p = do
   a <- p
   space
   return a


string :: Parser String
string = (do
   symbol "\""
   cs <- try (do
      cs <- list (satisfy (not . (== '\"')))
      symbol "\""
      return cs) <||> (fail "open string")
   return cs)


typename :: Parser Type
typename = (keyword "bit" >> return TypeBit) <|> 
   (keyword "bool" >> return TypeBool) <|>
   (keyword "byte" >> return TypeByte) <|>
   (keyword "pid" >> return TypePid) <|>
   (keyword "int" >> return TypeInt) <|>
   (keyword "mtype" >> return TypeMType) <|>
   (keyword "chan" >> return TypeChan)


intTypename :: Parser Type
intTypename = (keyword "bit" >> return TypeBit) <|> 
   (keyword "bool" >> return TypeBool) <|>
   (keyword "byte" >> return TypeByte) <|>
   (keyword "pid" >> return TypePid) <|>
   (keyword "int" >> return TypeInt)


-- avoid ambiguity in case of missing space character

op :: String -> Parser String
op "&" = try (do
   s <- items "&&" <|> items "&" <|> fail ("operator '&' expected")
   if s == "&"
      then return "&"
      else fail ("operator '&' expected"))
op "|" = try (do
   s <- items "||" <|> items "|" <|> fail ("operator '|' expected")
   if s == "|"
      then return "|"
      else fail ("operator '|' expected"))
op ">" = try (do
   s <- items ">=" <|> items ">>" <|> items ">" <|> fail ("operator '>' expected")
   if s == ">"
      then return ">"
      else fail ("operator '>' expected"))
op "<" = try (do
   s <- items "<=" <|> items "<<" <|> items "<" <|> fail ("operator '<' expected")
   if s == "<"
      then return "<"
      else fail ("operator '<' expected"))
op "!" = try (do
   s <- items "!=" <|> items "!" <|> fail ("operator '!' expected")
   if s == "!"
      then return "!"
      else fail ("operator '!' expected"))
op "-" = try (do
   s <- items "->" <|> items "-" <|> fail ("operator '-' expected")
   if s == "-"
      then return "-"
      else fail ("operator '-' expected"))
op s = items s <|> fail ("operator '" ++ s ++ "' expected")


-- avoid ambiguity in case of missing space character

symbol :: String -> Parser String
symbol "?<" = try (do
   trim (item '?')
   item '<'
   return "?<")
symbol "??<" = try (do
   trim (items "??")
   item '<'
   return "??<")
symbol "?[" = try (do
   trim (item '?')
   item '['
   return "?[")
symbol "??[" = try (do
   trim (items "??")
   item '['
   return "??[")
symbol "?" = try (do
   s <- symbol "??<" <|> symbol "??[" <|> symbol "?<" <|> symbol "?[" <|>
      items "?" <|> fail ("'?' expected")
   if s == "?"
      then return "?"
      else fail ("'?' expected"))
symbol "??" = try (do
   s <- symbol "??<" <|> symbol "??[" <|> items "??" <|> fail ("'??' expected")
   if s == "??"
      then return "??"
      else fail ("'??' expected"))
symbol "=" = try (do
   s <- items "==" <|> items "=" <|> fail ("'=' expected")
   if s == "="
      then return "="
      else fail ("'=' expected"))
symbol ":" = try (do
   s <- items "::" <|> items ":" <|> fail ("':' expected")
   if s == ":"
      then return ":"
      else fail ("':' expected"))
symbol "." = try (do
   s <- items ".." <|> items "." <|> fail ("'.' expected")
   if s == "."
      then return "."
      else fail ("'.' expected"))
symbol s = items s <|> fail ("'" ++ s ++ "' expected")