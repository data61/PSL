(*** Path_Table and Print_Table ***)

(* inner_path_ord: This definition is more or less arbitrary. *)
fun inner_path_ord ([],    []   ) = EQUAL
  | inner_path_ord (_,     []   ) = GREATER
  | inner_path_ord ([],     _   ) = LESS
  | inner_path_ord (x::xs, y::ys) = case Int.compare (x, y) of
      EQUAL => inner_path_ord (xs, ys)
    | diff  => diff;

fun prnt_ord (SeLFiE_Util.Print p1, SeLFiE_Util.Print p2) = String.compare (p1, p2);

structure Inner_Path_Table = Table (type key = SeLFiE_Util.inner_path  val ord = inner_path_ord): TABLE;
structure Print_Table      = Table (type key = SeLFiE_Util.print       val ord = prnt_ord      ): TABLE;