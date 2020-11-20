{-# LANGUAGE RecordWildCards, PatternGuards, ViewPatterns #-}

module Parse(parseFile, parseFragment) where

import Type
import Data.Maybe
import Data.Char
import Data.List
import qualified Language.Haskell.Exts.Annotated as HSE
import Language.Haskell.Exts.Annotated hiding (parseFile)
import Data.Generics.Uniplate.Data


hseMode = defaultParseMode{fixities = Just $ infix_ (-1) ["==>"] ++ baseFixities}

parseFile :: FilePath -> IO [HintInput]
parseFile file = do
    res <- HSE.parseFileWithMode hseMode{parseFilename=file} file
    return $ concatMap hlint $ childrenBi $ fromParseResult res

parseFragment :: String -> IO [HintInput]
parseFragment x = return $ hlint $ fromParseResult $ parseDeclWithMode hseMode x


---------------------------------------------------------------------
-- HLINT SPECIFIC



hlint :: Decl_ -> [HintInput]
hlint = readSetting


---------------------------------------------------------------------
-- READ A SETTINGS FILE

isSeverity :: String -> Bool
isSeverity x = x `elem` words "ignore warn warning error hint"

readSetting :: Decl_ -> [HintInput]
readSetting src@(FunBind _ [Match _ (Ident _ (isSeverity -> True)) pats (UnGuardedRhs _ bod) bind])
    | InfixApp _ lhs op rhs <- bod, prettyPrint op == "==>" =
        let (a,b) = readSide $ childrenBi bind in
        [HintInput src (fromParen lhs) (fromParen rhs) b a]
    | otherwise = []

readSetting x | "test" `isPrefixOf` map toLower (fromNamed x) = []
readSetting x@AnnPragma{} = []
readSetting (PatBind an (PVar _ name) _ bod bind) = readSetting $ FunBind an [Match an name [] bod bind]
readSetting (FunBind an xs) | length xs /= 1 = concatMap (readSetting . FunBind an . return) xs
readSetting (SpliceDecl an (App _ (Var _ x) (Lit _ y))) = readSetting $ FunBind an [Match an (fromQual x) [PLit an y] (UnGuardedRhs an $ Lit an $ String an "" "") Nothing]
readSetting x@InfixDecl{} = []
readSetting x = errorOn x "bad hint"


readSide :: [Decl_] -> (Maybe Exp_, [Note])
readSide = foldl f (Nothing,[])
    where f (Nothing,notes) (PatBind _ PWildCard{} Nothing (UnGuardedRhs _ side) Nothing) = (Just side, notes)
          f (Nothing,notes) (PatBind _ (fromNamed -> "side") Nothing (UnGuardedRhs _ side) Nothing) = (Just side, notes)
          f (side,[]) (PatBind _ (fromNamed -> "note") Nothing (UnGuardedRhs _ note) Nothing) = (side,g note)
          f _ x = errorOn x "bad side condition"

          g (Lit _ (String _ x _)) = []
          g (List _ xs) = concatMap g xs
          g x = case fromApps x of
              [con -> Just "IncreasesLaziness"] -> [IncreasesLaziness]
              [con -> Just "DecreasesLaziness"] -> [DecreasesLaziness]
              [con -> Just "RemovesError",str -> Just a] -> [RemovesError]
              [con -> Just "ValidInstance",str -> Just a,var -> Just b] -> [ValidInstance a b]
              _ -> errorOn x "bad note"

          con :: Exp_ -> Maybe String
          con c@Con{} = Just $ prettyPrint c; con _ = Nothing
          var c@Var{} = Just $ prettyPrint c; var _ = Nothing
          str (Lit _ (String _ _ x)) = Just x; str _ = Nothing


errorOn :: (Annotated ast, Pretty (ast SrcSpanInfo)) => ast SrcSpanInfo -> String -> b
errorOn val msg = error $
    show (ann val) ++
    ": Error while reading hint file, " ++ msg ++ "\n" ++
    prettyPrint val

fromApps :: Exp_ -> [Exp_]
fromApps (App _ x y) = fromApps x ++ [y]
fromApps x = [x]

fromNamed :: Pretty a => a -> String
fromNamed = prettyPrint

fromParen :: Exp_ -> Exp_
fromParen (Paren _ x) = fromParen x
fromParen x = x

fromQual :: QName a -> Name a
fromQual (Qual _ _ x) = x
fromQual (UnQual _ x) = x
