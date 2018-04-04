{-# LANGUAGE RecordWildCards, PatternGuards #-}

module HOL(parseHOL) where

import Type
import Data.List
import Data.Char
import Language.Haskell.Exts.Annotated(SrcLoc(..))


parseHOL :: FilePath -> IO [Lemma]
parseHOL file = do
    src <- readFile file
    return $ isabelleTheorems file src


-- Extract theorems out of Isabelle code (HLint.thy)
isabelleTheorems :: FilePath -> String -> [Lemma]
isabelleTheorems file = find . lexer 1
    where
        find ((i,"lemma"):(_,'\"':lemma):rest) = Lemma [HOL $ SrcLoc file i 1] lemma Proved : find rest
        find ((i,"lemma"):(_,name):(_,":"):(_,'\"':lemma):rest) = Lemma [HOL $ SrcLoc file i 1] lemma Proved : find rest
        find ((i,"lemma"):(_,"assumes"):(_,'\"':assumes):(_,"shows"):(_,'\"':lemma):rest) =
            Lemma [HOL $ SrcLoc file i 1] (assumes ++ " \\<Longrightarrow> " ++ lemma) Proved : find rest

        find ((i,"lemma"):rest) = Lemma [HOL $ SrcLoc file i 1] "Unsupported lemma format" Error : find rest
        find (x:xs) = find xs
        find [] = []

        lexer i x
            | i `seq` False = []
            | Just x <- stripPrefix "(*" x, (a,b) <- breaks "*)" x = lexer (add a i) b
            | Just x <- stripPrefix "\"" x, (a,b) <- breaks "\"" x = (i,'\"':a) : lexer (add a i) b -- NOTE: drop the final "
            | x:xs <- x, isSpace x = lexer (add [x] i) xs
            | (a@(_:_),b) <- span (\y -> y == '_' || isAlpha y) x = (i,a) : lexer (add a i) b
        lexer i (x:xs) = (i,[x]) : lexer (add [x] i) xs
        lexer i [] = []

        add s i = length (filter (== '\n') s) + i

        breaks s x | Just x <- stripPrefix s x = ("",x)
        breaks s (x:xs) = let (a,b) = breaks s xs in (x:a,b)
        breaks s [] = ([],[])
