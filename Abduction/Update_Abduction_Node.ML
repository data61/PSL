(*
 * Update_Abduction_Node.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)

(*** UPDATE_ABDUCTION_NODE ***)
signature UPDATE_ABDUCTION_NODE =
sig

type ornode;
type andnode;
type abduction_node;

(* update of abduction_node *)
val update_gg_parent_not_finished: bool -> abduction_node -> abduction_node;
val update_proved_completely     : abduction_node -> abduction_node;
val update_proof_n_proof_id      : string -> abduction_node -> abduction_node;
val update_refuted               : abduction_node -> abduction_node;
val update_branch                : abduction_node -> abduction_node;

end;

(*** Update_Abduction_Node ***)
structure Update_Abduction_Node: UPDATE_ABDUCTION_NODE =
struct

open Abduction_Node;

(** update of abduction_node **)
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