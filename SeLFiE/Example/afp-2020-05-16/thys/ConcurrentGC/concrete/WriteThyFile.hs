{-
 - Copyright 2015, NICTA
 -
 - This software may be distributed and modified according to the terms of
 - the BSD 2-Clause license. Note that NO WARRANTY is provided.
 - See "LICENSE_BSD2.txt" for details.
 -
 - @TAG(NICTA_BSD)
 -}

module WriteThyFile ( write_thy_file ) where

import WriteFileBasis

intersperse :: a -> [a] -> [a]
intersperse sep xxs =
  case xxs of
    [] -> []
    x : xs -> x : prependToAll xs
  where
    prependToAll xxs =
      case xxs of
        [] -> []
        x : xs -> sep : x : prependToAll xs

{-
 - WriteThyFile provides functions that allow to write isabelle
 - files from its input file whose extension is .txt.
 -}

-- the header of the output file.
-- FIXME in general the type synonyms are a function of the input.
header :: String -> String
header inp = unlines
  [ "theory Concrete_heap"
  , "imports"
  , "  \"~~/src/HOL/Library/Saturated\""
  , "  \"../Proofs\""
  , "begin"
  , ""
  , "type_synonym field = \"3\""
  , "type_synonym mut = \"2\""
  , "type_synonym ref = \"5\""
  , ""
  , "type_synonym concrete_local_state = \"(field, mut, ref) local_state\""
  , "type_synonym clsts = \"(field, mut, ref) lsts\""
  , ""
  , "abbreviation mut_common_init_state :: concrete_local_state where"
  , "  \"mut_common_init_state \\<equiv> undefined\\<lparr> ghost_handshake_phase := hp_IdleMarkSweep, ghost_honorary_grey := {}, ghost_honorary_root := {}, roots := {}, W := {} \\<rparr>\""
  , ""
  , "context gc_system"
  , "begin"
  , ""
  ]

write_mut :: [String] -> String
write_mut [] = ""
write_mut (m : ms) = unlines
  [ "abbreviation mut_init_state" ++ m ++ " :: concrete_local_state where"
  , "  \"mut_init_state" ++ m ++ " \\<equiv> " ++ "mut_common_init_state \\<lparr> "
      ++ "roots := {" ++ concat (intersperse ", " ms)
      ++ "} \\<rparr>\""
  , ""
  ]

write_muts :: [[String]] -> String
write_muts [] = ""
write_muts (m : ms) = write_mut m ++ write_muts ms

write_mut_part :: String -> String
write_mut_part = write_muts . map words . lines . get_mut_part

write_refs' :: [String] -> [String]
write_refs' [] = []
write_refs' (x1:x2:xs) = x1 : "\\<mapsto>" : x2 : write_refs' xs

put_commas ::  [String] -> [String]
put_commas [] = [];
put_commas (x:[]) = [];
put_commas (x:y:[]) = [];
put_commas (x:y:z:[]) = x : y : z : [];
put_commas (x:y:z:ws) = x : y : z : "," : put_commas ws;

write_refs :: [String] -> String
write_refs [] = [];
write_refs xs =
  concat $ intersperse " " $ put_commas $ write_refs' xs;

write_obj :: [String] -> String
write_obj [] = []
write_obj (o : os) = concat
  [ "   " ++ o ++ " \\<mapsto> \\<lparr> obj_mark = initial_mark,\n"
  , "           obj_fields = "
  , if os == [] then "Map.empty"
                else "[ " ++ write_refs os ++ " ]"
  , " \\<rparr>"
  ]

write_obj_part :: String -> String
write_obj_part cs = unlines
  [ "abbreviation sys_init_heap :: \"ref \\<Rightarrow> (field, ref) object option\" where"
  , "  \"sys_init_heap \\<equiv>"
  , "  [" ++ concat (intersperse ",\n   " (map (write_obj . words) $ lines $ get_obj_part cs))
  , "  ]\""
  , ""
  ]

footer :: String
footer = unlines
  [ "end"
  , ""
  , "end"
  ]

write_thy_file :: String -> String
write_thy_file inp =
  header inp ++ write_obj_part inp ++ write_mut_part inp ++ footer
