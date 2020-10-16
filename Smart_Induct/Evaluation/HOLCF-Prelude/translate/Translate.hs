{-# LANGUAGE RecordWildCards, PatternGuards, FlexibleContexts #-}

module Translate(translate) where

import Language.Haskell.Exts.Annotated hiding (paren)
import Data.Generics.Uniplate.Data
import Data.List
import Control.Monad.State
import Type
import Classify


reparen :: Exp_ -> Exp_
reparen x = if isLambda x || isIf x || badInfix x then Paren (ann x) x else x
    where badInfix (InfixApp _ _ op _) = prettyPrint op `elem` words "|| && ."
          badInfix _ = False


translate :: HintInput -> Lemma
translate hint@HintInput{..} =
    let a = exp1 $ typeclasses hintNotes hintLHS; b = exp1 hintRHS in
    Lemma [Hint hint] (maybe "" assumes hintSide ++ relationship hintNotes a b)
        (if a == b then Trivial else classify hintLHS `max` classify hintRHS)
    where
        exp1 = exp . transformBi unqual . reparen

        subs xs = flip lookup [(reverse b, reverse a) | x <- words xs, let (a,'=':b) = break (== '=') $ reverse x]
        funs = subs "id=ID not=neg or=the_or and=the_and (||)=tror (&&)=trand (++)=append (==)=eq (/=)=neq ($)=dollar"
        ops = subs "||=orelse &&=andalso .=oo ===eq /==neq ++=++ !!=!! $=dollar $!=dollarBang"
        pre = flip elem $ words "eq neq dollar dollarBang"
        cons = subs "True=TT False=FF"

        typeclasses notes x = foldr f x notes
            where
                f (ValidInstance cls var) x = evalState (transformM g x) True
                    where g v@Var{} | v ~= var = do
                                b <- get; put False
                                return $ if b then Paren an $ Var an $ UnQual an $ Ident an $ prettyPrint v ++ "::'a::" ++ cls ++ "_sym" else v
                          g v = return v :: State Bool Exp_
                f _  x = x

        relationship notes a b | any lazier notes = a ++ " \\<sqsubseteq> " ++ b
                               | DecreasesLaziness `elem` notes = b ++ " \\<sqsubseteq> " ++ a
                               | otherwise = a ++ " = " ++ b
            where lazier IncreasesLaziness = True
                  lazier RemovesError{} = True
                  lazier _ = False

        assumes (App _ op var)
            | op ~= "isNat" = "le\\<cdot>0\\<cdot>" ++ prettyPrint var ++ " \\<noteq> FF \\<Longrightarrow> "
            | op ~= "isNegZero" = "gt\\<cdot>0\\<cdot>" ++ prettyPrint var ++ " \\<noteq> FF \\<Longrightarrow> "
        assumes (App _ op var) | op ~= "isWHNF" = prettyPrint var ++ " \\<noteq> \\<bottom> \\<Longrightarrow> "
        assumes _ = ""

        -- Syntax translations
        exp :: Exp_ -> String
        exp (App _ a b) = exp a ++ "\\<cdot>" ++ exp b
        exp (Paren _ x) = "(" ++ exp x ++ ")"
        exp (Var _ x) | Just x <- funs $ prettyPrint x = x
        exp (Con _ (Special _ (TupleCon _ _ i))) = "\\<langle>" ++ replicate (i-1) ',' ++ "\\<rangle>"
        exp (Con _ x) | Just x <- cons $ prettyPrint x = x
        exp (Tuple _ xs) = "\\<langle>" ++ intercalate ", " (map exp xs) ++ "\\<rangle>"
        exp (If _ a b c) = "If " ++ exp a ++ " then " ++ exp b ++ " else " ++ exp c
        exp (Lambda _ xs y) = "\\<Lambda> " ++ unwords (map pat xs) ++ ". " ++ exp y
        exp (InfixApp _ x op y) | Just op <- ops $ prettyPrint op =
            if pre op then op ++ "\\<cdot>" ++ exp (paren x) ++ "\\<cdot>" ++ exp (paren y) else exp x ++ " " ++ op ++ " " ++ exp y

        -- Translations from the Haskell 2010 report
        exp (InfixApp l a (QVarOp _ b) c) = exp $ App l (App l (Var l b) a) c -- S3.4
        exp x@(LeftSection l e op) = let v = fresh x in exp $ Paren l $ Lambda l [PVar l $ Ident l v] $ InfixApp l e op (Var l $ UnQual l $ Ident l v) -- S3.5
        exp x@(RightSection l op e) = let v = fresh x in exp $ Paren l $ Lambda l [PVar l $ Ident l v] $ InfixApp l (Var l $ UnQual l $ Ident l v) op e -- S3.5
        exp x = prettyPrint x

        pat (PTuple _ xs) = "\\<langle>" ++ intercalate ", " (map pat xs) ++ "\\<rangle>"
        pat x = prettyPrint x

        fresh x = head $ ("z":["v" ++ show i | i <- [1..]]) \\ vars x



vars :: Biplate a Exp_ => a -> [String]
vars xs = [prettyPrint x | Var _ (UnQual _ x) <- universeS xs]

universeS :: Biplate x (f SrcSpanInfo) => x -> [f SrcSpanInfo]
universeS = universeBi

a ~= b = prettyPrint a == b

isLambda Lambda{} = True; isLambda _ = False
isIf If{} = True; isIf _ = False

unqual :: QName SrcSpanInfo -> QName SrcSpanInfo
unqual (Qual an _ x) = UnQual an x
unqual x = x

paren x = if isAtom x then x else Paren (ann x) x

isAtom x = case x of
    Paren{} -> True
    Tuple{} -> True
    List{} -> True
    LeftSection{} -> True
    RightSection{} -> True
    TupleSection{} -> True
    RecConstr{} -> True
    ListComp{} -> True
    EnumFrom{} -> True
    EnumFromTo{} -> True
    EnumFromThen{} -> True
    EnumFromThenTo{} -> True
    _ -> isLexeme x

isLexeme Var{} = True
isLexeme Con{} = True
isLexeme Lit{} = True
isLexeme _ = False

nullSrcLoc :: SrcLoc
nullSrcLoc = SrcLoc "" 0 0

an :: SrcSpanInfo
an = toSrcInfo nullSrcLoc [] nullSrcLoc

