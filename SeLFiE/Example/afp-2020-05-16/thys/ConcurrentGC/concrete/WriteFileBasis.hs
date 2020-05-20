{-
 - Copyright 2015, NICTA
 -
 - This software may be distributed and modified according to the terms of
 - the BSD 2-Clause license. Note that NO WARRANTY is provided.
 - See "LICENSE_BSD2.txt" for details.
 -
 - @TAG(NICTA_BSD)
 -}

module WriteFileBasis where

{-
 - WriteFileBasis provides the basic functionalities that are used
 - by both WriteThyFile.hs and WriteDotFile.hs.
 -}

get_mut_part' :: [String] -> [String]
get_mut_part' xs = takeWhile (\x -> (head $ words x) /= "--") xs;

-- extract the mutator part from the input string.
get_mut_part :: String -> String
get_mut_part xs = unlines $ get_mut_part' $ lines xs;

get_obj_part' :: [String] -> [String]
get_obj_part' xs =
  tail $ dropWhile (\x -> (head $ words x) /= "--") xs;

-- extract the object part from the input string.
get_obj_part :: String -> String
get_obj_part xs = unlines $ get_obj_part' $ lines xs;
