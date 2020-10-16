{-# LANGUAGE RecordWildCards, PatternGuards #-}

module Classify(classify) where

import Type
import Data.Generics.Uniplate.Data
import Data.Maybe
import Language.Haskell.Exts.Annotated


-- | Guess if a lemma cannot be proven
classify :: Exp_ -> Status
classify x
    | _:_ <- [v :: Exp_ | v@Case{} <- universeBi x] = Unsupported "case"
    | _:_ <- [v :: Exp_ | v@ListComp{} <- universeBi x] = Unsupported "list-comp"
    | v:_ <- mapMaybe (`lookup` missingFuncs) [prettyPrint (v :: Name SrcSpanInfo) | v <- universeBi x] = Unsupported v
classify _ = Provable


missingFuncs = let a*b = [(b,a) | b <- words b] in concat
    ["IO" * "putChar putStr print putStrLn getLine getChar getContents hReady hPrint stdin"
    ,"Exit" * "exitSuccess"
    ,"Ord" * "(>) (<=) (>=) (<) compare minimum maximum sort sortBy"
    ,"Show" * "show shows showIntAtBase"
    ,"Read" * "reads read"
    ,"String" * "lines unlines words unwords"
    ,"Monad" * "mapM mapM_ sequence sequence_ msum mplus mzero liftM when unless return evaluate join void (>>=) (<=<) (>=>) forever ap"
    ,"Functor" * "fmap"
    ,"Numeric" * "(+) (*) fromInteger fromIntegral negate log (/) (-) (*) (^^) (^) subtract sqrt even odd"
    ,"Char" * "isControl isPrint isUpper isLower isAlpha isDigit"
    ,"Arrow" * "second first (***) (&&&)"
    ,"Applicative+" * "traverse for traverse_ for_ pure (<|>) (<**>)"
    ,"Exception" * "catch handle catchJust bracket error toException"
    ,"WeakPtr" * "mkWeak"
    ]


