{-# LANGUAGE DeriveDataTypeable, RecordWildCards #-}

module Main(main) where

import System.Console.CmdArgs
import Parse
import HOL
import Translate
import Type
import Classify
import Data.List
import Data.Function
import Data.Maybe


data Args = Args
    {code :: [String]
    ,files :: [FilePath]
    ,hol :: [FilePath]
    ,report :: Maybe FilePath
    }
    deriving (Data,Typeable,Show)

myArgs = cmdArgsMode $ Args
    {code = [] &= help "Inline code to process"
    ,files = [] &= args
    ,hol = [] &= typFile &= help "HOL files to check"
    ,report = Nothing &= opt "report.txt" &= help "Write out a report"
    }


main :: IO ()
main = do
    Args{..} <- cmdArgsRun myArgs
    a <- fmap concat $ mapM parseFragment code
    b <- fmap concat $ mapM parseFile files
    c <- fmap concat $ mapM parseHOL hol
    let sources = merge $ map translate (a ++ b) ++ c
    let output = unlines $ display sources
    case report of
        Nothing -> putStrLn output
        Just file -> do
            writeFile file output
            putStrLn $ "Report written to " ++ file


merge :: [Lemma] -> [Lemma]
merge = map f . groupBy ((==) `on` lemma) . sortBy (compare `on` lemma)
    where f xs = Lemma (concatMap input xs) (lemma $ head xs) (maximum $ map status xs)

display :: [Lemma] -> [String]
display xs = ["* " ++ show (status x) ++ " (" ++ show (length xs) ++ ")" | xs@(x:_) <- ys] ++ "" : concatMap f ys
    where
        ys = groupBy ((==) `on` status) $ sortBy (compare `on` status) xs
    
        f xs@(x:_) = ("== " ++ show (status x) ++ " (" ++ show (length xs) ++ ") ==") :
                     "" : concatMap g xs ++ [""]

        g Lemma{..} = showLemma lemma : map showInput input ++ [""]
