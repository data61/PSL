(*
 * Abduction_Node.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** ABDUCTION_NODE ***)
signature ABDUCTION_NODE =
sig

type ornode;
type andnode;
type or2and_edge;

(** proof_node **)
datatype abduction_node =
  Or_Node   of ornode  (*Edgs from Or_Node are alternative steps to prove this node, one of which we have to complete.*)
| And_Node  of andnode (*sub-goals, all of which we have to prove.*)
| Or_To_And of or2and_edge;

(* query on abduction_node *)
val is_ornode                                    : abduction_node -> bool;
val is_andnode                                   : abduction_node -> bool;
val is_or2and_edge                               : abduction_node -> bool;
val importance                                   : abduction_node -> real;

(* query on abduction_node for ornode and andnode *)
val is_proved_completely                         : abduction_node -> bool;

(* query on abduction_node for ornode *)
val proof_id_of                                  : abduction_node -> int option;
val proof_of                                     : abduction_node -> strings option;
val is_branch                                    : abduction_node -> bool;
val is_final_goal                                : abduction_node -> bool;
val lemma_name_of                                : abduction_node -> string;
val is_template_based                            : abduction_node -> bool;
val is_worth_proving                             : Proof.context -> abduction_node -> bool;

(* query on abduction_node for or2and_edge *)
val or2and_edge_to_proof                         : abduction_node -> strings;

(* destructors of abduction_node *)
val dest_Or_Node  : abduction_node -> ornode;
val dest_And_Node : abduction_node -> andnode;
val dest_Or_To_And: abduction_node -> or2and_edge;

(* creation of abduction_node *)
type is_final_goal = bool;
val mk_ornode: Proof.context -> is_final_goal -> string -> term -> abduction_node;
val mk_andnode: terms -> abduction_node;

end;


(*** Abduction_Node ***)
structure Abduction_Node: ABDUCTION_NODE =
struct

open Or_Node;
open And_Node;
open Or2And_Edge;

(** abduction_node **)
datatype abduction_node =
  Or_Node   of ornode  (*Edges from Or_Node are alternative steps to prove this node, one of which we have to complete.*)
| And_Node  of andnode (*sub-goals, all of which we have to prove.*)
| Or_To_And of or2and_edge;

(** query on abduction_node **)
(* is_ornode *)
fun is_ornode (Or_Node _) = true
  | is_ornode _ = false;

(* is_andnode *)
fun is_andnode (And_Node _) = true
  | is_andnode _ = false;

(* is_or2and_edge *)
fun is_or2and_edge (Or_To_And _) = true
  | is_or2and_edge _ = false;

(* importance *)
fun importance (Or_To_And {importance,...}) = importance
  | importance (Or_Node   {importance,...}) = (case importance of
      NONE => (warning "Importance is not defined for this Or_Node!"; 0.0)
    | SOME imp => imp)
  | importance _ = error "importance in Abduction_Node failed. And_Node does not carry importance explicilty";

(* is_proved_completely *)
fun is_proved_completely (Or_Node  nd) = #proved_completely nd
  | is_proved_completely (And_Node nd) = #proved_completely nd
  | is_proved_completely (Or_To_And _) = error "is_proved_completely failed."

(* is_worth_proving *)
fun is_worth_proving ctxt (Or_Node  or_nd) = Or_Node.is_worth_proving ctxt or_nd
  | is_worth_proving _    (And_Node     _) = error "is_worth_proving failed. This is And_Node."
  | is_worth_proving _    (Or_To_And    _) = error "is_worth_proving failed. This is Or_To_And.";

fun proof_id_of (Or_Node or_nd) = #proof_id or_nd
  | proof_id_of  _              = error "proof_id_of. This is not Or_Node."

(* proof_of *)
fun proof_of (Or_Node or_nd) = #proof or_nd
  | proof_of  _              = error "proof_of failed. This is not Or_Node."

(* is_branch *)
fun is_branch (Or_Node or_nd) = #is_branch or_nd
  | is_branch _ = error "is_branch failed. This is not Or_Node."

(* is_final_goal *)
fun is_final_goal (Or_Node or_nd) = #final_goal or_nd
  | is_final_goal  _              = error "is_final_goal. This is not Or_Node."

(* or2and_edge_to_proof *)
fun or2and_edge_to_proof (Or_To_And or2and_edge:abduction_node) = Or2And_Edge.or2and_edge_to_proof or2and_edge
  | or2and_edge_to_proof _ = error "or2and_edge_to_proof failed. This is not or2and_edge."

(* lemma_name_of *)
fun lemma_name_of (Or_Node or_nd) = #lemma_name or_nd
  | lemma_name_of _ = error "lemma_name_of failed. Not an Or_Node."

(* is_template_based *)
fun is_template_based (Or_Node ornode) = Or_Node.is_template_based ornode
  | is_template_based _ = error "is_template_based in Abduction_Node.ML failed";

(** destructors on abduction_node **)
(* dest_Or_Node *)
fun dest_Or_Node (Or_Node or_b) = or_b
  | dest_Or_Node _ = error "dest_Or_Node failed.";

(* dest_And_Node *)
fun dest_And_Node (And_Node and_b) = and_b
  | dest_And_Node _ = error "dest_And_Node failed.";

(* dest_Or_To_And *)
fun dest_Or_To_And (Or_To_And edge) = edge
  | dest_Or_To_And _ = error "dest_Or_To_And_failed";

(* creation of abduction_node *)
type is_final_goal = bool;

(* mk_ornode *)
fun mk_ornode (ctxt:Proof.context) (is_final_goal:is_final_goal) (lemma_name:string) (goal:term) =
    Or_Node (Or_Node.mk_ornode ctxt is_final_goal lemma_name goal): abduction_node;

(* mk_andnode *)
fun mk_andnode (subgoals:terms) = And_Node (And_Node.mk_andnode subgoals);

end;