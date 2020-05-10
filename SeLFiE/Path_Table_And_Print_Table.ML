(*  Title:      PSL/SeLFiE/src/Preprocessor/Path_Table_And_Print_Table.thy
    Author:     Yutaka Nagashima, Czech Technical University in Prague, the University of Innsbruck
*)

(*** structure: Inner_Path_Table ***)
(*inner_path_ord: This definition is more or less arbitrary.*)
fun inner_path_ord ([],    []   ) = EQUAL
  | inner_path_ord (_,     []   ) = GREATER
  | inner_path_ord ([],     _   ) = LESS
  | inner_path_ord (x::xs, y::ys) = case Int.compare (x, y) of
      EQUAL => inner_path_ord (xs, ys)
    | diff  => diff;

structure Inner_Path_Table = Table (type key = UN.inner_path  val ord = inner_path_ord): TABLE;

(*** structure: Outer_Path_Table  ***)
datatype location = Subgoal of int | Chained_Fact of int;

type outer_path = location * UN.inner_path;
type outer_paths = outer_path list;

(*This definition is more or less arbitrary.*)
fun outer_path_ord ((Subgoal n, inner_path1), (Subgoal m, inner_path2)) =
    (case Int.compare (n, m) of EQUAL => inner_path_ord (inner_path1, inner_path2) | diff  => diff)
  | outer_path_ord ((Chained_Fact n, inner_path1), (Chained_Fact m, inner_path2)) =
    (case Int.compare (n, m) of EQUAL => inner_path_ord (inner_path1, inner_path2) | diff  => diff)
  | outer_path_ord ((Subgoal      _, _), (Chained_Fact _, _)) = GREATER
  | outer_path_ord ((Chained_Fact _, _), (Subgoal      _, _)) = LESS

fun outer_path_eq (full_p1:outer_path, full_p2:outer_path) = case outer_path_ord (full_p1, full_p2) of
  EQUAL => true | _ => false;

structure Outer_Path_Table  = Table (type key = outer_path  val ord = outer_path_ord): TABLE;

(*** structure: Print_Table  ***)
structure Print_Table = Symtab: TABLE;