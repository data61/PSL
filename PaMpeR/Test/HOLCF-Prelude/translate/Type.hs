{-# LANGUAGE RecordWildCards, PatternGuards, DeriveDataTypeable #-}

module Type(
    Decl_, Exp_,
    Input(..), HintInput(..), Note(..),
    Lemma(..), Status(..),
    showLemma, showInput
    ) where

import Language.Haskell.Exts.Annotated
import Data.Data
import System.FilePath


type Exp_ = Exp SrcSpanInfo
type Decl_ = Decl SrcSpanInfo

prettyPrintOneLine = prettyPrintStyleMode (Style OneLineMode 1 1) defaultMode 


showLemma :: String -> String
showLemma x = "lemma " ++ show x


data Input
    = HOL SrcLoc
    | Hint HintInput
    deriving Show

data HintInput = HintInput
    {hintOriginal :: Decl_
    ,hintLHS :: Exp_
    ,hintRHS :: Exp_
    ,hintNotes :: [Note]
    ,hintSide :: Maybe Exp_
    }
    deriving Show

data Note
    = IncreasesLaziness
    | DecreasesLaziness
    | RemovesError
    | ValidInstance String String -- ValidInstance "Eq" "x"
    deriving (Eq,Ord,Show)


showInput :: Input -> String
showInput (Hint HintInput{..}) = "Hint " ++ showSrcLoc (getPointLoc $ ann hintOriginal) ++ ": " ++ prettyPrintOneLine hintOriginal
showInput (HOL x) = "HOL " ++ showSrcLoc x

showSrcLoc :: SrcLoc -> String
showSrcLoc SrcLoc{..} = takeFileName srcFilename ++ ":" ++ show srcLine


data Lemma = Lemma
    {input :: [Input]
    ,lemma :: String
    ,status :: Status
    }
    deriving Show

data Status
    = Error
    | Provable
    | Unsupported String
    | Trivial
    | Proved
    deriving (Eq,Ord)

instance Show Status where
    show Error = "Error"
    show Provable = "Provable"
    show (Unsupported x) = "Unsupported " ++ x
    show Trivial = "Trivial"
    show Proved = "Proved"
