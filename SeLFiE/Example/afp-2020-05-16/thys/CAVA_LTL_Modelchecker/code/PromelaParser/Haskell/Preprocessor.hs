------------------------------------------------------------------------
-- 
-- Module: PromelaParser.Preprocessor
-- Author: Dennis Kraft
-- 
-- preprocessor for promela code
-- 
------------------------------------------------------------------------


module Preprocessor where


import Prelude hiding (lookup)
import Data.Char
import Data.Map
import Basic
import Lexer


------------------------------------------------------------------------

preproc :: Parser String
preproc = preproc' empty
   where preproc' m = do
            (s, m') <- def m <|> udef m <|> rep m
            s' <- (do
                  item '\n'
                  s'' <- preproc' m'
                  return ('\n' : s'')) <|> 
               return ""
            return (s ++ s')


def :: Map String String -> Parser (String, Map String String)
def m = do
   try (do
      space'
      items "#define")
   spaceOne'
   k <- identifier
   spaceOne'
   v <- list (spaceOne' <|> satisfy (not . (=='\n')))
   return ("", insert k v m)


ifdef :: Map String String -> Parser (String, Map String String)
ifdef m = do
      try (do
         space'
         items "#ifdef")
      spaceOne'
      k <- identifier
      space'
      item '\n'
      s <- ifblock m
   where ifblock m = do
            try (do
               space'
               items "#endif")
            
   v <- list (spaceOne' <|> satisfy (not . (=='\n')))
   return ("", insert k v m)


udef :: Map String String -> Parser (String, Map String String)
udef m = do
   try (do
      space'
      items "#undef")
   spaceOne'
   k <- identifier
   space'
   return ("", delete k m)


rep :: Map String String -> Parser (String, Map String String)
rep m = do 
      ss <- list (identifier' <|> 
         convert (\c -> [c]) (satisfy (not . (=='\n'))))
      return (concat ss, m)
   where identifier' = do
            k <- identifier
            return (case lookup k m of
               Just v -> v
               Nothing -> k)
   
          


------------------------------------------------------------------------


space' :: Parser Char
space' = list (satisfy (\c -> isSpace c && not (c =='\n')) <|> comment) 
   >> return ' '


spaceOne' :: Parser Char
spaceOne' = listOne (satisfy (\c -> isSpace c && not (c =='\n')) <|> comment) 
   >> return ' '
