{-# OPTIONS_GHC -fglasgow-exts #-}

module Main where {

import qualified System;
import Nat;
import Ta;

import Pt_examples;


-- instance Read Nat where {
--   readsPrec p s = map (\(a,b) -> (Nat a,b)) (filter (\(a,b) -> a>=0) ((readsPrec::Int -> ReadS Integer) p s))
-- };


createFta (states, rules) =
  foldl (\fta r -> htai_add_rule r fta) (foldl (\fta q -> htai_add_qi q fta) (htai_empty ()) states) rules;

ftaPairs = map (\(a1,a2) -> (createFta a1, createFta a2)) allTests;

intersect_witness (a1, a2) = (hta_is_empty_witness (hta_prod a1 a2));
intersect_witnessWR (a1, a2) = (hta_is_empty_witness (hta_prodWR a1 a2));



-- test = createFta (read "[1,2,3]") (read "[]");
-- 
-- readFta file = do {s <- readFile file;
--                   let (states,rules) = read s in return (createFta states rules)};

-- main = do {fta1 <- readFta "/tmp/fta1.fta";
--           fta2 <- readFta "/tmp/fta2.fta";
--           print (hta_is_empty_witness (hta_prod fta1 fta2))}

main = do  
         args <- System.getArgs
         if args == ["-wr"] then
             print (map intersect_witnessWR ftaPairs)
           else
             print (map intersect_witness ftaPairs)


}
