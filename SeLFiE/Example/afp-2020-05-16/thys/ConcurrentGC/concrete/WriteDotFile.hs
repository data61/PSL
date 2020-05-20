{-
 - Copyright 2015, NICTA
 -
 - This software may be distributed and modified according to the terms of
 - the BSD 2-Clause license. Note that NO WARRANTY is provided.
 - See "LICENSE_BSD2.txt" for details.
 -
 - @TAG(NICTA_BSD)
 -}

module WriteDotFile ( write_dot_file ) where

import WriteFileBasis

{-
 - WriteDotFile provides functions that allow to write .dot files
 - from its input file whose extension is .txt.
 -}

-- the header of the output file.
header :: String
header =
  "digraph g {\n" ++
  "  graph [rankdir = \"LR\"];\n" ++
  "  node [fontsize = \"10.5\" shape = \"ellipse\"];\n" ++
  "  edge [];";

-- returns a string that describes one mutator node in the output file.
write_mut :: String -> String
write_mut m =
  "  mut" ++ m ++ " [label = \"<f> mut" ++ m ++
  "\" shape = \"record\"];\n";

-- returns a string that describes all the mutator nodes in the output file.
write_muts :: [[String]] -> String
write_muts [] = "";
write_muts (m:ms) = (write_mut $ head m) ++ write_muts ms;

-- returns a string that describes the subgraph for mutators.
subgraph_mut :: String -> String
subgraph_mut contents =
  "\n\nsubgraph clusterA{\n\n" ++
  (write_muts $ map words $ lines $ get_mut_part contents) ++ "\n}\n";

-- auxiliary functions to draw fields in objects
take_eventh :: [String] -> [String]
take_eventh [] = [];
take_eventh (x:[]) = [];
take_eventh (x1:x2:xs) = x2:(take_eventh xs);

-- returns a string that describes all the fields in one object.
fields :: [String] -> String
fields [] = []
fields (f:fs) = " | <f" ++ f ++ "> " ++ f ++ (fields fs);

-- returns a string that describes one object in the .dot file.
write_obj :: [String] -> String
write_obj os =
  "  obj" ++ (head os) ++ " [label = \"<f> obj" ++
  (head os) ++ (fields $ take_eventh os) ++
  "\" shape = \"record\"];\n";

-- returns a string that describes all the objects in the .dot file.
write_objs :: [[String]] -> String
write_objs [] = "";
write_objs (o:os) = (write_obj o) ++ write_objs os;

-- returns a string that describes all the objects in the .dot file.
subgraph_obj :: String -> String
subgraph_obj contents =
  "\n\nsubgraph clusterB{\n\n" ++
  (write_objs $ map words $ lines $ get_obj_part contents) ++
  "\n}\n";

-- returns a string that describe one line starting from a mutator.
write_mut_1_line :: String -> String -> String
write_mut_1_line from to =
  "\"mut" ++ from ++ "\":f -> \"obj" ++ to ++ "\":f;\n";

-- returns a string that describes all the lines starting from a mutator.
write_mut_line :: [String] -> String
write_mut_line [] = [];
write_mut_line (l:[]) = [];
write_mut_line (l1:l2:ls) =
  write_mut_1_line l1 l2 ++ write_mut_line (l1:ls);

-- returns a string that describes all the lines starting from all the mutators.
write_mut_lines :: [[String]] -> String
write_mut_lines [] = "";
write_mut_lines (l:ls) = write_mut_line l ++ write_mut_lines ls;

{-
 - returns a string that describes all the lines starting from
 - all the  mutators.
 -}
lines_from_mut :: String -> String
lines_from_mut contents = "\n" ++
  (write_mut_lines $ map words $ lines contents);

-- returns a string that describes one line starting from a object.
write_obj_1_line :: String -> String -> String -> String
write_obj_1_line from_obj from_field to_obj =
  "\"obj" ++ from_obj ++ "\":f" ++ from_field ++
  " -> \"obj" ++ to_obj ++ "\":f;\n";

-- returns a string that describes all the line starting from a object.
write_obj_line :: [String] -> String
write_obj_line [] = [];
write_obj_line (l:[]) = [];
write_obj_line (l1:l2:[]) = [];
write_obj_line (l1:l2:l3:ls) =
  write_obj_1_line l1 l2 l3 ++ write_obj_line (l1:ls);

-- returns a string that describes all the line starting from all the object.
write_obj_lines :: [[String]] -> String
write_obj_lines [] = "";
write_obj_lines (l:ls) = write_obj_line l ++ write_obj_lines ls;

{-
 - returns a string that describess all the lines starting from
 - all the  mutators.
 -}
lines_from_obj :: String -> String
lines_from_obj contents = "\n" ++
  (write_obj_lines $ map words $ lines contents);

 -- .returns a string that describes all the lines specified in the input file.
draw_lines :: String -> String
draw_lines cs =
  (lines_from_mut $ get_mut_part cs) ++
  (lines_from_obj $ get_obj_part cs);

footer :: String
footer = "}";

write_dot_file :: String -> String
write_dot_file inp =
  header ++ subgraph_mut inp ++ subgraph_obj inp ++
  draw_lines inp ++ footer;
