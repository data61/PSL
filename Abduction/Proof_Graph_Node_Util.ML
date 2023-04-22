(*
 * Proof_Graph_Node_Util.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)

(*** PROOF_GRAPH_NODE ***)
signature PROOF_GRAPH_NODE_UTIL =
sig

type ornode     = Proof_Graph_Node.ornode;
type andnode    = Proof_Graph_Node.andnode;
type proof_node = Proof_Graph_Node.proof_node;

(* update of proof_node *)
val update_gg_parent_not_finished: bool -> proof_node -> proof_node;
val update_proved_completely     : proof_node -> proof_node;
val update_proof_n_proof_id      : string -> proof_node -> proof_node;
val update_refuted               : proof_node -> proof_node;
val update_branch                : proof_node -> proof_node;

end;

(*** Proof_Graph_Node_Util ***)
structure Proof_Graph_Node_Util: PROOF_GRAPH_NODE_UTIL =
struct

open Proof_Graph_Node;

(** update of proof_node **)
(* update_gg_parent_not_finished *)
fun update_gg_parent_not_finished b (Or_Node ornode) = Or_Node.update_gg_parent_not_finished ornode b |> Or_Node
  | update_gg_parent_not_finished _  and_or_edge     = and_or_edge;

(* update_proved_completely *)
fun update_proved_completely (Or_Node  ornode ) = Or_Node.update_proved_completely ornode |> Or_Node
  | update_proved_completely (And_Node andnode) = And_Node.update_proved_completely andnode |> And_Node
  | update_proved_completely (Or_To_And      _) = error "update_proved_completely failed.";

(* update_proof_n_proof_id *)
fun update_proof_n_proof_id proof (Or_Node ornode) = Or_Node.update_proof_n_proof_id proof ornode |> Or_Node
  | update_proof_n_proof_id _      and_or_edge     = and_or_edge;

(* update_refuted *)
fun update_refuted (Or_Node  ornode ) = Or_Node.update_refuted  ornode  |> Or_Node
  | update_refuted (And_Node andnode) = And_Node.update_refuted andnode |> And_Node
  | update_refuted _                  = error "update_refuted failed. Or_To_And edge!";

(* update_branch *)
fun update_branch (Or_Node ornode) = Or_Node.update_branch ornode |> Or_Node
  | update_branch _                = error "update_branch failed!";

end;