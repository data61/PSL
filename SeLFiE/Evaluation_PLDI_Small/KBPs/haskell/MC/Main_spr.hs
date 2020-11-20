{-

Turn a trie into a DFA and reduce it under bisimulation.

Run the DFS on the example, copy the result into MC_spr.hs

Initial states for Child0:

:t [ (s, SPRViewDet.spr_simInit envInit envObsC envObs Child0 (envObs Child0 s)) | s <- envInit ]

-}
module Main where

import MC_spr

import Prelude
import Control.Monad ( foldM, when )
import Data.Map ( Map )
import qualified Data.Map as Map
import Data.DFA as DFA

cToNum :: (Num i, Integral e) => e -> i
cToNum  = fromIntegral . toInteger

update_map k m =
  case Map.lookup k m of
    Just i -> (m, i)
    Nothing -> let v = cToNum (Map.size m)
                in (Map.insert k v m, v)

traverse_trieM :: Monad m => [k] -> Trie k v -> a -> ([k] -> a -> v -> m a) -> m a
traverse_trieM ks (Trie v ls) a f =
  do a' <- case v of
             Nothing -> return a
             Just b -> f (reverse ks) a b
     foldM (\a'' (k, t) -> traverse_trieM (k : ks) t a'' f) a' ls

tat dfa t =
  traverse_trieM [] t a0 $ \k a v ->
    traverse_trieM [] v a $ \k' a' v' ->
      traverse_trieM [] v' a' $ \k'' a'' v'' ->
        traverse_trieM [] v'' a'' $ \k''' (sm, lm, lim) (Mapping v''') ->
          do let srcKey = (zip k k', zip k'' k''')
                 (sm0, i) = update_map srcKey sm
                 f (sm', lm', lim') (obs, (ODList x0, ODList x1)) =
                   do let (sm'', j) = update_map (x0, x1) sm'
                          (lm'', k) = update_map obs lm'
                          ((ca0, (ca1, ca2)), _) = obs
                          lim'' = Map.insert k (show ca0 ++ " " ++ show ca1 ++ " " ++ show ca2) lim'
                      addTransition dfa (i, k, j)
                      return (sm'', lm'', lim'')
             when (null v''') $ putStrLn $ "No successors for state " ++ show srcKey
             foldM f (sm0, lm, lim) v'''
  where
    a0 = (Map.empty, Map.empty, Map.empty)

taa dfa sm t =
  traverse_trieM [] t a0 $ \k a v ->
    traverse_trieM [] v a $ \k' a' v' ->
      traverse_trieM [] v' a' $ \k'' a'' v'' ->
        traverse_trieM [] v'' a'' $ \k''' a''' v''' ->
          do let srcKey = (zip k k', zip k'' k''')
                 f act =
                   case act of
                     SayIKnow -> setSatBit dfa (Map.findWithDefault (error "FIXME") srcKey sm)
                     SayNothing -> return ()
             mapM_ f v'''
  where
    a0 = ()

ti dfa sm = foldM f
  where
    f (i, lim) (s, (ODList k1, ODList k2)) =
      do let BEState_ext ((c0,(c1,c2)),_) _ _ = s
             str = show c0 ++ show c1 ++ show c2
             lim' = Map.insert i str lim
         DFA.addInitialTransition dfa (i, Map.findWithDefault (error $ "ti: " ++ show (k1,k2)) (k1, k2) sm)
         return (i + 1, lim')

AlgState_ext aActs aTrans _ = mc_dfs_output

main :: IO ()
main =
  do dfa <- DFA.initialize
     (sm, lm, lim) <- tat dfa aTrans
--      mapM_ print $ Map.toList sm
--      putStrLn $ "Number of states: " ++ show (Map.size sm)
--      numStates dfa >>= \n -> putStrLn $ " DFA: " ++ show n
     putStrLn $ "num initial states: " ++ show (length mc_init)
     taa dfa sm aActs
     -- FIXME: we just care about the label inverse map here.
     (_, lim') <- ti dfa sm (cToNum (Map.size lm), lim) mc_init
     minimize dfa
     let llim l = Map.findWithDefault (error $ "FIXME: lim: " ++ show l) l lim'
     writeDotToFile dfa "mc_spr.dot" llim
     return ()
