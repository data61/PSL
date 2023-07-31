(*
 * Update_Abduction_Graph.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)

(*** UPDATE_ABDUCTION_GRAPH ***)
signature UPDATE_ABDUCTION_GRAPH =
sig

type abduction_node;
type abduction_graph;
type update_abduction_graph;
type key;
type keys;

(* update of abduction_graph *)
val update_gg_parent_not_finished     : update_abduction_graph;
val update_is_branch                  : key -> update_abduction_graph;(*TODO: no need to expose?*)
val update_proved_wo_assmng_cnjctr    : key -> update_abduction_graph;
val update_after_proving_ornode       : (*proof*)strings -> (*or*)key -> Proof.context -> update_abduction_graph;
val add_andnode                       : terms -> abduction_graph -> keys * abduction_graph;
val add_edges_from_andnode_to_ornodes : (*and*)key -> update_abduction_graph;
val add_child_ornode                  : (string * term) -> update_abduction_graph;

end;

(*** Update_Abduction_Graph ***)
structure Update_Abduction_Graph: UPDATE_ABDUCTION_GRAPH =
struct

open Abduction_Node;
open Abduction_Graph;

type update_abduction_graph = abduction_graph -> abduction_graph;

(* update_branch *)
fun update_is_branch (key:key) (graph:abduction_graph) =
    PGraph.map_node key Update_Abduction_Node.update_is_branch graph: abduction_graph;

local

fun update_gg_parent_not_finished_of_or_key (key as (Or_N, _):key) (gr:abduction_graph): abduction_graph =
    let
      val does_need_proof = not (all_gg_parents_are_proved gr key)                             : bool;
      val update          = Update_Abduction_Node.update_gg_parent_not_finished does_need_proof: abduction_node -> abduction_node;
    in
      PGraph.map_node key update gr
    end
  | update_gg_parent_not_finished_of_or_key _ _ = error "update_gg_parent_not_finished_of_or_key failed. Not an or-key.";

in

(* update_gg_parent_not_finished *)
(* update_gg_parent_not_finished assumes that the graph is already updated by
 * update_proved_completely_of_graph_because_orleaf_is_proved. *)
(* There is no point in updating gg_parent_not_finished for a particular node:
 * proving one ornode may change proved_completely of any node in the graph. *)
fun update_gg_parent_not_finished (graph:abduction_graph) =
    let
      val keys    = PGraph.keys graph    : keys;
      val or_keys = filter is_ornode keys: keys;

    in
      fold update_gg_parent_not_finished_of_or_key or_keys graph
    end;

end;

local

(* update_proof_n_proof_id *)
fun update_proof_n_proof_id (proof:strings) (key:key) (graph:abduction_graph) =
    PGraph.map_node key (Update_Abduction_Node.update_proof_n_proof_id proof) graph: abduction_graph;

(* update_proved_completely *)
fun update_proved_completely_of_node (key:key) (graph:abduction_graph) =
    PGraph.map_node key Update_Abduction_Node.update_proved_completely graph: abduction_graph;

(* forall_at_least_one *)
fun forall_at_least_one assertion xs = forall assertion xs andalso (length xs > 0);

val children = PGraph.immediate_succs;
val parents  = PGraph.immediate_preds;

in

(* update_proved_wo_assmng_cnjctr_of_graph and update_branch *)
fun update_proved_wo_assmng_cnjctr (key as (Or_N, _)) (graph:abduction_graph) =
    if not (is_branch graph key)(*If this or-node is a leaf, we do not have to care about the effects of its children.*)
    then
      let
        val graph_w_one_node_updated = update_proved_completely_of_node key graph                               : abduction_graph;
        val parents_keys             = parents graph_w_one_node_updated key                                     : keys;
        val result                   = fold update_proved_wo_assmng_cnjctr parents_keys graph_w_one_node_updated: abduction_graph;
      in
        result: abduction_graph
      end
    else
      update_branch key graph exists parents grand_children (* Root ~ And -> OR -> Edge -> And ~ Leaf *)
  | update_proved_wo_assmng_cnjctr (key as (And_N, trms)) (graph:abduction_graph) =
    update_branch key graph forall_at_least_one grand_parents children (* Root ~ OR -> Edge -> And -> OR ~ Leaf *)
  | update_proved_wo_assmng_cnjctr (O2A_E _, _) _ = error "update_proved_wo_assmng_cnjctr failed! O2A_E!"
and update_branch key graph (forall_or_exists) (parent_or_grand_parent) (child_or_grand_child) =
    let
      val children_keys = child_or_grand_child graph key: keys;

      val this_node_is_newly_proved_wo_assmng_cnjctr =
            is_proved_completely graph key |> not(*This node was not proved yet*)
          andalso
            (*for or-node:  this node is now proved because one grandchild (and-node) is proved.*)
            (*for and-node: this node is now proved because all children   (or-node) are proved.*)
            forall_or_exists (fn key => is_proved_completely graph key) children_keys: bool;

      val some_grandchild_of_ornode_that_proved_completely: key option =
          if   is_ornode key andalso this_node_is_newly_proved_wo_assmng_cnjctr
          then (
            let
              val proved_grandchildren = filter (fn key => is_proved_completely graph key) children_keys: keys;
            in
              SOME (hd proved_grandchildren: key)
            end
            )
          else NONE;

      val graph_w_one_node_updated' =
          if   this_node_is_newly_proved_wo_assmng_cnjctr
          then update_proved_completely_of_node key graph
          else graph;

      val graph_w_one_node_updated =
          if   is_some some_grandchild_of_ornode_that_proved_completely (*key is ornode*)
          then (
            let
              val grandchild_of_ornode_that_proved_completely = the some_grandchild_of_ornode_that_proved_completely: key;
              val to_and_edges           = PGraph.immediate_preds graph_w_one_node_updated' grandchild_of_ornode_that_proved_completely;
              val from_or_edges          = PGraph.immediate_succs graph_w_one_node_updated' key
              val inter_edges            = inter equal_keys to_and_edges from_or_edges;
              val or2edge                = if length inter_edges > 0 then hd inter_edges else error "graph_w_one_node_updated failed!";
              val script_to_prove_ornode = or2and_edge_to_proof graph_w_one_node_updated' or2edge: strings;
            in
              update_proof_n_proof_id script_to_prove_ornode key graph_w_one_node_updated'
            end
          )
          else graph_w_one_node_updated'

      val parents_keys = parent_or_grand_parent graph_w_one_node_updated key: keys;

      val result =
          if   this_node_is_newly_proved_wo_assmng_cnjctr
          (*for or-node:  we have to update its parents       (and-node).*)
          (*for and-node: we have to update its grand parents ( or-node).*)
          then fold update_proved_wo_assmng_cnjctr parents_keys graph_w_one_node_updated
          else graph;

    in
      result
    end;

(*Important tricky part!*)
fun update_after_proving_ornode (proof:strings) (or_key as (Or_N, _): key) (ctxt:Proof.context) (g:abduction_graph) =
  let
    val updated1 = update_proof_n_proof_id proof or_key g;
    val updated2 = update_proved_wo_assmng_cnjctr or_key updated1;
    val updated3 = update_gg_parent_not_finished updated2
  in
    updated3: abduction_graph
  end
 | update_after_proving_ornode _ _ _ _ = error "update_after_proving_ornode failed. Not an or-node key."

end;

fun add_nodes (key_value_pairs: (key * abduction_node) list) (graph: abduction_graph) (or_and:string) =
    let
      fun new_node (k, v) (acc, g:abduction_graph): (keys * abduction_graph) =
          (k :: acc, PGraph.new_node (k, v) g) handle PGraph.DUP _ => (k :: acc, g);
      val (newly_added_keys, resulting_graph) = fold new_node key_value_pairs ([], graph): keys * abduction_graph;
    in
     (newly_added_keys, resulting_graph)
    end;

(* add_andnode *)
fun add_andnode (subgoals:terms) (graph: abduction_graph): (keys * abduction_graph) =
    add_nodes [mk_andnode subgoals] graph "and";

(* add_edges_from_andnode_to_ornodes *)
fun add_edges_from_andnode_to_ornodes (and_key as (And_N, terms):key) (graph_w_child_ornodes:abduction_graph) =
  let
    val ornode_keys             = map (fn trm => (Or_N, [trm])) terms                                                            : keys;
    val graph_w_and_to_or_edges = fold (fn target_key => PGraph.add_edge (and_key, target_key)) ornode_keys graph_w_child_ornodes: abduction_graph;
  in
    graph_w_and_to_or_edges
  end
 | add_edges_from_andnode_to_ornodes _ _ = error "add_edges_from_andnode_to_ornodes failed.";

(* add_ornodes *)
fun add_ornodes (key_value_pairs: (key * abduction_node) list) (graph: abduction_graph) =
    add_nodes key_value_pairs graph "or";

(* add_child_ornode *)
fun add_child_ornode (lemma_name:string, goal:term) (graph:abduction_graph) =
    let
      val (child_or_key, child_or_val) = Abduction_Graph.mk_ornode false lemma_name goal: (key * abduction_node);
      val (_, graph_w_ornodes) = add_ornodes [(child_or_key, child_or_val)] graph: keys * abduction_graph;
    in
      graph_w_ornodes
    end;

end;