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
type update_abduction_node;

(* update of abduction_node *)
val update_gg_parent_not_finished: bool -> update_abduction_node;
val update_proved_completely     : update_abduction_node;
val update_proof_n_proof_id      : strings -> update_abduction_node;
val update_is_branch             : update_abduction_node;
val update_importance            : real -> update_abduction_node;
val update_imp_if_this_is_larger : real -> update_abduction_node;

end;

(*** Update_Abduction_Node ***)
structure Update_Abduction_Node: UPDATE_ABDUCTION_NODE =
struct

open Abduction_Node;

type update_abduction_node = abduction_node -> abduction_node;

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

(* update_branch *)
fun update_is_branch (Or_Node ornode) = Or_Node.update_is_branch ornode |> Or_Node
  | update_is_branch _                = error "update_branch failed!";

(* update_importance *)
fun update_importance (imp:real) (Or_Node ornode) = Or_Node.update_importance imp ornode |> Or_Node
  | update_importance  _          _               = error "update_importance failed!";

(* update_imp_if_this_is_larger *)
fun update_imp_if_this_is_larger (imp:real) (Or_Node ornode) = Or_Node.update_imp_if_this_is_larger imp ornode |> Or_Node
  | update_imp_if_this_is_larger  _          _               = error "update_importance failed!";

end;