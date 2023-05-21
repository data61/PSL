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
val update_branch                       : key -> update_abduction_graph;(*TODO: no need to expose?*)
val update_after_proving_ornode         : (*proof*)string -> (*or*)key -> Proof.context -> update_abduction_graph;
val add_andnodes                        : (key * abduction_node) list -> abduction_graph -> keys * abduction_graph;
val add_ornodes                         : (key * abduction_node) list -> abduction_graph -> keys * abduction_graph;
val add_edge_acyclic_if_possible        : key -> key -> update_abduction_graph;
val add_edges_from_andnodes_to_ornodes  : keys -> update_abduction_graph;
val find_counterexample_update          : Proof.state -> key -> update_abduction_graph;
val process_andkey_and_add_child_ornodes: Proof.state -> key -> update_abduction_graph;

end;

(*** Update_Abduction_Graph ***)
structure Update_Abduction_Graph: UPDATE_ABDUCTION_GRAPH =
struct

open Abduction_Node;
open Abduction_Graph;

type update_abduction_graph = abduction_graph -> abduction_graph;

(* update_branch *)
fun update_branch (key:key) (graph:abduction_graph) =
    PGraph.map_node key Update_Abduction_Node.update_branch graph: abduction_graph;

local

fun update_gg_parent_not_finished_of_or_key (key as (Or_N, _):key) (gr:abduction_graph): abduction_graph =
    let
      val does_need_proof = not (all_gg_parents_are_proved gr key)                             : bool;
      val update          = Update_Abduction_Node.update_gg_parent_not_finished does_need_proof: abduction_node -> abduction_node;
    in
      PGraph.map_node key update gr
    end
  | update_gg_parent_not_finished_of_or_key _ _ = error "update_gg_parent_not_finished_of_or_key failed. Not an or-key.";

(* update_gg_parent_not_finished_in_abduction_graph *)
(* update_gg_parent_not_finished_in_abduction_graph assumes that the graph is already updated by
 * update_proved_completely_of_graph_because_orleaf_is_proved. *)
(* There is no point in updating gg_parent_not_finished for a particular node:
 * proving one ornode may change proved_completely of any node in the graph. *)
fun update_gg_parent_not_finished_in_abduction_graph (graph:abduction_graph) =
    let
      val keys    = PGraph.keys graph    : keys;
      val or_keys = filter is_ornode keys: keys;

    in
      fold update_gg_parent_not_finished_of_or_key or_keys graph
    end;

(* update_proof_n_proof_id *)
fun update_proof_n_proof_id (proof:string) (key:key) (graph:abduction_graph) =
    PGraph.map_node key (Update_Abduction_Node.update_proof_n_proof_id proof) graph: abduction_graph;

(* update_proved_completely *)
fun update_proved_completely (key:key) (graph:abduction_graph) =
    PGraph.map_node key Update_Abduction_Node.update_proved_completely graph: abduction_graph;

(* forall_at_least_one *)
fun forall_at_least_one assertion xs = forall assertion xs andalso (length xs > 0);

val children = PGraph.immediate_succs;
val parents  = PGraph.immediate_preds;

(* update_proved_wo_assmng_cnjctr_of_graph and update_branch *)
fun update_proved_wo_assmng_cnjctr_of_graph (key as (Or_N, trms)) (graph:abduction_graph) =
    if not (is_branch graph key)(*If this or-node is a leaf, we do not have to care about the effects of its children.*)
    then
      let
        val graph_w_one_node_updated = update_proved_completely key graph                                                : abduction_graph;
        val parents_keys             = parents graph_w_one_node_updated key                                              : keys;
        val result                   = fold update_proved_wo_assmng_cnjctr_of_graph parents_keys graph_w_one_node_updated: abduction_graph;
      in
        result: abduction_graph
      end
    else
      update_branch key graph exists parents grand_children (* Root ~ And -> OR -> Edge -> And ~ Leaf *)
  | update_proved_wo_assmng_cnjctr_of_graph (key as (And_N, trms)) (graph:abduction_graph) =
    update_branch key graph forall_at_least_one grand_parents children (* Root ~ OR -> Edge -> And -> OR ~ Leaf *)
  | update_proved_wo_assmng_cnjctr_of_graph (O2A_E _, _) _ = error "update_proved_wo_assmng_cnjctr_of_graph failed! O2A_E!"
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
              val proved_grandchildren = filter (fn key => is_proved_completely graph key) children_keys
            in
              SOME (hd proved_grandchildren)
            end
            )
          else NONE;

      val graph_w_one_node_updated' =
          if   this_node_is_newly_proved_wo_assmng_cnjctr
          then update_proved_completely key graph
          else graph;

      val graph_w_one_node_updated =
          if   is_some some_grandchild_of_ornode_that_proved_completely
          then (
            let
              val grandchild_of_ornode_that_proved_completely = the some_grandchild_of_ornode_that_proved_completely;
              val to_and_edges           = PGraph.immediate_preds graph_w_one_node_updated' grandchild_of_ornode_that_proved_completely;
              val from_or_edges          = PGraph.immediate_succs graph_w_one_node_updated' key
              val inter_edges            = inter equal_keys to_and_edges from_or_edges;
              val or2edge                = if length inter_edges > 0 then hd inter_edges else error "graph_w_one_node_updated failed!";
              val script_to_prove_ornode = or2and_edge_to_proof graph_w_one_node_updated' or2edge: string;
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
          then fold update_proved_wo_assmng_cnjctr_of_graph parents_keys graph_w_one_node_updated
          else graph;

    in
      result
    end;

(* update_proved_completely_of_graph_because_orleaf_is_proved *)
fun update_proved_completely_of_graph_because_orleaf_is_proved (_:Proof.context(*only for tracing*)) (key as (Or_N, _): key) (graph:abduction_graph): abduction_graph =
    (* TODO: We have to update proof_id of ancestors.
     * PGraph.topological_order, ignore PGraph.isolated, compare the difference, map update_proof_id_of_abduction_node
     * We can ignore this issue for now, at the cost of strictly sticking to the dependency imposed by the graph
     * and not allowing sledgehammer to use lemmas that are not immediate successors.*)
    update_proved_wo_assmng_cnjctr_of_graph key graph
  | update_proved_completely_of_graph_because_orleaf_is_proved _ _ _ =
    error "update_proved_completely_of_graph_because_orleaf_is_proved failed.";

in

(*Important tricky part!*)
fun update_after_proving_ornode (proof:string) (or_key:key) (ctxt:Proof.context) (g:abduction_graph) =
  let
    val updated1 = update_proof_n_proof_id proof or_key g;
    val updated2 = update_proved_completely_of_graph_because_orleaf_is_proved ctxt or_key updated1;
    val updated3 = update_gg_parent_not_finished_in_abduction_graph updated2;
  in
    updated3: abduction_graph
  end;

end;

fun add_nodes (key_value_pairs: (key * abduction_node) list) (graph: abduction_graph) (or_and:string) =
    let
      val numb_of_created_keys = length key_value_pairs: int;
(*
      val _ = if or_and = "or" then tracing ("Number of newly produced " ^ or_and ^ "-nodes: " ^ Int.toString numb_of_created_keys ^ ".") else ();
*)
      fun new_node (k, v) (acc, g:abduction_graph): (keys * abduction_graph) =
          (k :: acc, PGraph.new_node (k, v) g)
          handle PGraph.DUP _ => ((*tracing ("Duplicated " ^ or_and ^ "-node. We use the existing one, which may have been proved_wo_assmng_cnjctr.");*) (k :: acc, g));
      val (newly_added_keys, resulting_graph) = fold new_node key_value_pairs ([], graph): keys * abduction_graph;
      val number_of_duplicated_keys = numb_of_created_keys - length newly_added_keys;
(*
      val _ = if or_and = "or" then tracing ("Number of discarded "^ or_and ^"-nodes due to duplication: " ^ Int.toString number_of_duplicated_keys ^ ".") else ();
*)
    in
     (newly_added_keys, resulting_graph)
    end;

(* add_andnodes *)
fun add_andnodes (key_value_pairs: (key * abduction_node) list) (graph: abduction_graph) =
    add_nodes key_value_pairs graph "and";

(* add_ornodes *)
fun add_ornodes (key_value_pairs: (key * abduction_node) list) (graph: abduction_graph) =
    add_nodes key_value_pairs graph "or";

(* add_edge_acyclic_if_possible *)
fun add_edge_acyclic_if_possible source_key target_key g =
  PGraph.add_edge_acyclic (source_key, target_key) g handle PGraph.CYCLES _ => (tracing "CYCLES detected!"; g): abduction_graph;

local

(* add_edges_from_andnode_to_ornodes *)
fun add_edges_from_andnode_to_ornodes (and_key as (And_N, terms):key) (graph:abduction_graph) =
  let
    val ornode_keys = map (fn trm => (Or_N, [trm])) terms: keys;
    val non_refuted_ornode_keys = filter_out (Abduction_Graph.is_refuted graph) ornode_keys: keys;
    val graph_w_and_to_or_edges = fold (add_edge_acyclic_if_possible and_key) non_refuted_ornode_keys graph: abduction_graph;
  in
    graph_w_and_to_or_edges
  end
 | add_edges_from_andnode_to_ornodes _ _ = error "add_edges_from_andnode_to_ornodes failed.";

in

(* add_edges_from_andnodes_to_ornodes *)
fun add_edges_from_andnodes_to_ornodes (and_keys:keys) (graph:abduction_graph) =
    fold add_edges_from_andnode_to_ornodes and_keys graph: abduction_graph;

end;

(* find_counterexample_update *)
fun find_counterexample_update (pst:Proof.state) (orkey:key) (graph:abduction_graph) =
  let
    val found_counter_example = exists (Shared_State.is_refuted pst) (snd orkey): bool;
  in
    if   found_counter_example
    then PGraph.map_node orkey Update_Abduction_Node.update_refuted graph(*TODO: We need update_refuted in Proof_Graph.ML*)
    else graph
  end;

(* process_andkey_and_add_child_ornodes *)
fun process_andkey_and_add_child_ornodes (pst:Proof.state) (and_key as (And_N, subgoals):key) (graph:abduction_graph) =
    let
      val pairs_to_mk_ornodes             = map (mk_ornode false) subgoals                                           : (key * abduction_node) list;
      val (new_or_keys, graph_w_ornodes)  = add_ornodes pairs_to_mk_ornodes graph                                    : keys * abduction_graph;
      (*expensive*)
      val graph_w_quickchecked_ornodes    = fold (find_counterexample_update pst) new_or_keys graph_w_ornodes        : abduction_graph;
      val graph_w_edges                   = add_edges_from_andnodes_to_ornodes [and_key] graph_w_quickchecked_ornodes: abduction_graph;
    in
      graph_w_edges
    end
  | process_andkey_and_add_child_ornodes _ _ _ = error "work_on_andnode failed! Not an And_N key!";

end;