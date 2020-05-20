------------------------------------------------------------------------
-- 
-- Module: PromelaParser.Main
-- Author: Dennis Kraft
--
-- input and output functions
-- 
------------------------------------------------------------------------


module Main where


import Prelude
import System.IO
import Data.Char
import Syntax
import Basic
import Lexer
import Module

  
main = do  
    content <- readFile "test.txt"
    program <- return (parse content)
    putStrLn (concatMap (\m -> (show m) ++ "\n") program) 


parse :: String -> [Module]
parse s = case parser program s of
      Consumed (Ok as _ _ _) -> as
      Consumed (Fail cs pos ms) -> f cs pos ms
      Empty (Ok as _ _ _) -> as
      Empty (Fail cs pos ms) -> f cs pos ms
   where f cs (x, y) ms = error ("parse error in line: " ++ 
            show x ++ " character: " ++ show y ++ 
            "\nnear: " ++ take 30 (spaceTrim cs) ++ 
            "\npossible causes for the error are:\n" ++ 
            concatMap (\m -> "\t-" ++ m ++ "\n") ms)


spaceTrim :: String -> String
spaceTrim [] = []
spaceTrim [c] | isSpace c = " "
              | otherwise = [c]
spaceTrim (c : cs) | isSpace c = ' ' : spaceTrim (dropWhile isSpace cs)
                   | otherwise = c : spaceTrim cs

