structure Product_Type : sig
  val fst : 'a * 'b -> 'a
  val snd : 'a * 'b -> 'b
end = struct

fun fst (x1, x2) = x1;

fun snd (x1, x2) = x2;

end; (*struct Product_Type*)

structure HOL : sig
  type 'a equal
  val equal : 'a equal -> 'a -> 'a -> bool
  val eq : 'a equal -> 'a -> 'a -> bool
end = struct

type 'a equal = {equal : 'a -> 'a -> bool};
val equal = #equal : 'a equal -> 'a -> 'a -> bool;

fun eq A_ a b = equal A_ a b;

end; (*struct HOL*)

structure Lista : sig
  val member : 'a HOL.equal -> 'a list -> 'a -> bool
end = struct

fun member A_ [] y = false
  | member A_ (x :: xs) y = HOL.eq A_ x y orelse member A_ xs y;

end; (*struct Lista*)

structure Arith : sig
  type int
end = struct

datatype num = One | Bit0 of num | Bit1 of num;

datatype int = Zero_int | Pos of num | Neg of num;

end; (*struct Arith*)

structure DFS : sig
  type node
  val dfs : (node * node) list -> node list -> node list -> node list
  val dfs2 : (node * node) list -> node list -> node list -> node list
end = struct

datatype node = Node of Arith.int;

fun equal_nodea _ _ = raise Fail "DFS.equal_node_inst.equal_node";

val equal_node = {equal = equal_nodea} : node HOL.equal;

fun nexts [] n = []
  | nexts (e :: es) n =
    (if equal_nodea (Product_Type.fst e) n then Product_Type.snd e :: nexts es n
      else nexts es n);

fun dfs g [] ys = ys
  | dfs g (x :: xs) ys =
    (if Lista.member equal_node ys x then dfs g xs ys
      else dfs g (nexts g x @ xs) (x :: ys));

fun dfs2 g [] ys = ys
  | dfs2 g (x :: xs) ys =
    (if Lista.member equal_node ys x then dfs2 g xs ys
      else dfs2 g xs (dfs2 g (nexts g x) (x :: ys)));

end; (*struct DFS*)
