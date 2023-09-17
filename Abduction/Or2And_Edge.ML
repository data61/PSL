(*
 * Or2And_Edge.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
signature OR2AND_EDGE =

sig

(** or2and_edge and functions on or2and_edge **)
datatype how_to_get_andnodes_from_ornode = Tactic of strings | Conjecture;
val how_to_get_andnodes_from_ornode_of: how_to_get_andnodes_from_ornode -> strings;
val proof_is_from_tactic: how_to_get_andnodes_from_ornode -> bool;

type or2and_edge;
val or2and_edge_to_proof: or2and_edge -> strings;
val or2and_edge_to_importance: or2and_edge -> real;

end;

structure Or2And_Edge: OR2AND_EDGE =
struct

(** or2and_edge and functions on or2and_edge **)
(* how_to_get_andnodes_from_ornode *)
datatype how_to_get_andnodes_from_ornode = Tactic of strings | Conjecture;

(* how_to_get_andnodes_from_ornode_of *)
fun how_to_get_andnodes_from_ornode_of  Conjecture     = []
  | how_to_get_andnodes_from_ornode_of (Tactic strings) = strings;

(* proof_is_from_tactic *)
fun proof_is_from_tactic (Tactic _) = true
  | proof_is_from_tactic _ = false;

(* or2and_edge *)
type or2and_edge = {
  how_to_get_andnodes_from_ornode: how_to_get_andnodes_from_ornode,
  proof_of_ornode_assmng_andnodes: strings,
  importance                     : real}

(* or2and_edge_to_proof *)
fun or2and_edge_to_proof ({proof_of_ornode_assmng_andnodes, ...}:or2and_edge) = proof_of_ornode_assmng_andnodes;

(* or2and_edge_to_importance *)
fun or2and_edge_to_importance ({importance,...}:or2and_edge) = importance: real;

end;