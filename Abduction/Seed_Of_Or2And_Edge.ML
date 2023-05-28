(*
 * Seed_Of_Or2And_Edge.ML 
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** SEED_OF_OR2AND_EDGE ***)
signature SEED_OF_OR2AND_EDGE =
sig

type abduction_graph;
type key;
type how_to_get_andnodes_from_ornode;
type abduction_node
type seed_of_or2and_edge =
     {new_goals: terms,
      proof    : how_to_get_andnodes_from_ornode,
      state    : Proof.state};
type seeds_of_or2and_edge;

val print_seed_of_or2and_edge             : Proof.context -> seed_of_or2and_edge -> unit list;
val seed_is_from_tactic                   : seed_of_or2and_edge -> bool;
val apply_PSL_to_get_seeds_of_or2and_edges: Proof.state -> seeds_of_or2and_edge;
val filter_out_bad_seeds_of_or2and_edge   : term (*parental or-node*) -> Proof.state -> abduction_graph -> seeds_of_or2and_edge -> seeds_of_or2and_edge
val conjectures_to_seeds_of_or2and_edge   : (Proof.state (*default pst*) * Proof.state (*chained pst to proved the parental ornode*)) -> (string * term) list -> seeds_of_or2and_edge;
val seed_has_counterexample               : Proof.state -> seed_of_or2and_edge -> bool;
val seeds_to_updated_graph                : key -> seeds_of_or2and_edge -> Update_Abduction_Graph.update_abduction_graph;

end;

(*** Seed_Of_Or2And_Edge ***)
structure Seed_Of_Or2And_Edge: SEED_OF_OR2AND_EDGE =
struct

open Abduction_Graph;
structure UAG = Update_Abduction_Graph;

type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;

type seed_of_or2and_edge =
     {new_goals: terms,
      proof    : how_to_get_andnodes_from_ornode,
      state    : Proof.state};

type seeds_of_or2and_edge = seed_of_or2and_edge list;

fun print_seed_of_or2and_edge ctxt ({new_goals,...}: seed_of_or2and_edge) = (
  tracing "== print_seed_of_or2and_edge:  ==";
  map (tracing o Isabelle_Utils.trm_to_string ctxt) new_goals
);

fun seed_is_from_tactic ({proof, ...}) = Or2And_Edge.proof_is_from_tactic proof: bool;

(* apply_Extend_Leaf_to_pst_get_records_to_mk_andnodes *)
(*TODO: handle the case where we actually finish to prove this.*)
fun apply_PSL_to_get_seeds_of_or2and_edges (pst:Proof.state) =
  let
    val ctxt          = Proof.context_of pst;
    val extend_str    = PSL_Interface.lookup ctxt "Extend_Leaf" |> the                     : PSL_Interface.strategy;
    val timeouts      = {overall = 60.0, hammer = 5.0, quickcheck = 1.0, nitpick = 2.0}    : TBC_Utils.timeouts;
    val result_seq    = TBC_Utils.psl_strategy_to_monadic_tactic timeouts extend_str pst []: (Dynamic_Utils.log * Proof.state) Seq.seq;
    val result_list   = Seq.list_of result_seq                                             : (Dynamic_Utils.log * Proof.state) list;
    val script_n_psts = map (apfst Dynamic_Utils.mk_apply_script) result_list              : (string * Proof.state) list;
    fun mk_proof_key_value (pscript, pst) =
        let
          val subgs              = Isabelle_Utils.pst_to_subgs pst
          val subgs_wo_meta_uni  = map strip_outermost_meta_quantifiers subgs: terms;
          val standardized_subgs = map Top_Down_Util.standardize_vnames subgs_wo_meta_uni: terms;
          fun check_print_read ctxt term = term
           |> Syntax.check_term ctxt
           |> Isabelle_Utils.trm_to_string ctxt
           |> Syntax.read_term ctxt
           |> Top_Down_Util.standardize_vnames;
  
          fun check_print_read_terms ctxt terms = map (check_print_read ctxt) terms: terms;
          fun pass_check_print_read_terms ctxt terms = try (check_print_read_terms ctxt) terms |> is_some;
  
          val nonempty_subgs =
            if length subgs = 0 orelse not (pass_check_print_read_terms ctxt standardized_subgs)
            then [@{prop "True"}]
            else standardized_subgs: terms;

        in
          {proof = Or2And_Edge.Tactic pscript, new_goals = nonempty_subgs, state = pst}: seed_of_or2and_edge
        end;
  in
    map mk_proof_key_value script_n_psts: seeds_of_or2and_edge
  end;

fun condition_to_filter_out (parent_or:term) (pst:Proof.state) (ag:abduction_graph) (seed:seed_of_or2and_edge) =
    let
      val final_goal      = get_final_goal_key ag |> snd |> hd: term;
(*
      val final_goal_size = Term.size_of_term final_goal |> Real.fromInt: real;
      val factor = case #proof seed of Or2And_Edge.Tactic _ => 5.0 | _ => 3.0: real;
      val upper_limit     = Real.min (factor * final_goal_size, 45.0): real;
*)
      val upper_limit = 45.0
      fun concl_is_alpha_eq_to trm imp =
        let
          val cncl = Logic.strip_imp_concl imp |> remove_Trueprop: term;
        in
          Top_Down_Util.alpha_eq_over_fvar trm cncl
        end;

      val trms                        = #new_goals seed                                                           : terms;
      val trms_empty                  = null trms                                                                 : bool;
      fun too_large _                 = exists (fn trm => Real.fromInt (Term.size_of_term trm) > upper_limit) trms: bool;
      fun eq_to_final_goal _          = exists (Top_Down_Util.alpha_eq_over_fvar final_goal) trms                 : bool;
      fun concl_is_eq_to_final_goal _ = exists (concl_is_alpha_eq_to final_goal) trms                             : bool;
      fun has_func_with_three_occs_in_a_row _ = exists
        (fn trm => SeLFiE_for_Top_Down.run_assertion (Top_Down_Util.mk_pst_to_prove_from_term (Proof.context_of pst) trm) SeLFiE_for_Top_Down.has_func_with_three_occs_in_a_row trm) trms;
      fun has_counter_example_in_prems (pst:Proof.state) (term:term) =
        let
          val prems = Logic.strip_imp_prems term: terms;
        in
           Shared_State.any_of_these_is_refuted pst prems: bool
        end;
      fun terms_have_counter_example_in_prems (pst:Proof.state) (terms:terms) =
          exists (has_counter_example_in_prems pst) terms: bool;
    in
      trms_empty orelse too_large () orelse
      eq_to_final_goal () andalso seed_is_from_tactic seed orelse
      concl_is_eq_to_final_goal () (*andalso seed_is_from_tactic seed*) orelse
      has_func_with_three_occs_in_a_row () orelse
      terms_have_counter_example_in_prems pst trms
    end;

fun filter_out_bad_seeds_of_or2and_edge (parent_or:term) (pst:Proof.state) (graph:abduction_graph) (seeds:seeds_of_or2and_edge) =
  filter_out (condition_to_filter_out parent_or pst graph) seeds: seeds_of_or2and_edge;

fun conjectures_to_seed_of_or2and_edge (pst:Proof.state) (cnjctr:term): seed_of_or2and_edge =
  {new_goals   = [cnjctr]              : terms,
   proof       = Or2And_Edge.Conjecture: how_to_get_andnodes_from_ornode,
   state       = pst                   : Proof.state};

fun conjectures_to_seeds_of_or2and_edge (pst:Proof.state, pst_to_prove_ornode:Proof.state) (cnjctrs_w_name: (string * term) list) =
  let
    val ctxt                      = Proof.context_of pst                                                                      : Proof.context;
    fun get_ctxt_w_proof_goal trm = Proof.context_of (Top_Down_Util.mk_pst_to_prove_from_term ctxt trm)                       : Proof.context;
    fun check_prop (trm:term)     = try (Syntax.check_prop (get_ctxt_w_proof_goal trm)) trm                                   : term option;
    val cnjctrs                   = map snd cnjctrs_w_name                                                                    : terms;
    val checked_cnjctrs           = List.mapPartial check_prop cnjctrs                                                        : terms;
    val result                    = map (fn trm => conjectures_to_seed_of_or2and_edge pst_to_prove_ornode trm) checked_cnjctrs: seeds_of_or2and_edge;
  in
    result
  end;

fun seed_has_counterexample (pst:Proof.state) ({new_goals,...}:seed_of_or2and_edge) =
    Shared_State.any_of_these_is_refuted pst new_goals;

fun add_or2and_edge_and_connect_it_to_parental_ornode
     (parent_or_key as (Or_N, _): key)(*parent node*)
     ({new_goals            : terms,
       proof                : how_to_get_andnodes_from_ornode,
       state(*chained*)     : Proof.state, ...}: seed_of_or2and_edge)(*child nodes*)
     (graph:abduction_graph): (key option * (string * term) list * abduction_graph) =
   let
     val ctxt                 = Proof.context_of state;
     val name_term_pairs      = map (fn and_trm => (Shared_State.get_lemma_name ctxt and_trm, and_trm)) new_goals   : (string * term) list;
     val pst_w_or_terms_assmd = Top_Down_Util.assume_cnjctrs_in_pst name_term_pairs state       : Proof.state;
     (*TODO: maybe we should assume or-nodes that have been already proved completely in the abduction_graph.*)
     val timeouts             = {overall = 30.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}: TBC_Utils.timeouts;
     (*very expensive*)
     val script_opt_gen       = TBC_Utils.pst_to_proofscript_opt timeouts "Finish_Goal_After_Assuming_Subgoals_And_Conjectures" pst_w_or_terms_assmd <$> fst: string option;
     val proved_parent_or     = is_some script_opt_gen: bool;
   in
     if proved_parent_or
     then
       let
         val how_we_got_andnode    = Or2And_Edge.how_to_get_andnodes_from_ornode_of proof                        : string;
         val script_to_prove_andnd = the script_opt_gen                                                          : string;
         val script_to_prove_ornd  = how_we_got_andnode ^ script_to_prove_andnd                                  : string;
         val or2and_edge_val       = Abduction_Node.Or_To_And {
                                      how_to_get_andnodes_from_ornode = proof,
                                      proof_of_ornode_assmng_andnodes = script_to_prove_ornd}                    : abduction_node;
         val or2and_edge_key      = ((O2A_E (serial())), [])                                                     : key;
         val thy                  = Proof.theory_of state                                                        : theory;
         val used_cnjctr_names    = Top_Down_Util.get_lemma_names_from_sh_output thy script_to_prove_andnd       : strings;
         val used_name_term_pairs = filter (fn (name, _) => member (op =) used_cnjctr_names name) name_term_pairs: (string * term) list;
         val relevant_name_term_pairs = if   Or2And_Edge.how_to_get_andnodes_from_ornode_of proof = "" (*if this is the result of tactic application*)
                                        then used_name_term_pairs
                                        else name_term_pairs;

         (* updating abduction_graph *)
         val graph_w_ornode_to_or2and_edge = graph
          |> PGraph.new_node (or2and_edge_key, or2and_edge_val)
          |> Update_Abduction_Graph.add_edge_acyclic_if_possible parent_or_key or2and_edge_key: abduction_graph;
       in
         (SOME or2and_edge_key, relevant_name_term_pairs, graph_w_ornode_to_or2and_edge)
       end
     else (NONE, [], graph)
   end
 | add_or2and_edge_and_connect_it_to_parental_ornode _ _ _ = error "how_to_prove_ornode_assmng_subgs_of_andnode failed.";

(*
 * 0. We have an or-node to expand.
 * 1. add an or2and-edge.
 * 2. connect the or2and-edge to its parental or-node.
 * 3. prove the parental or-node using the sub-goals or some conjectures.
 * 4. add an and-node that consists of the sub-goals or used conjectures.
 * 5. connect the and-node to its parental or2and-edge.
 * 6. add child-or-nodes that correspond to the sub-goals or used conjectures in the and-node.
 * 7. connect the child-or-nodes to the and-node.
 *)
fun add_then_connect_or2and_edge_andnd_ornds (parent_ornd:key) (seed: seed_of_or2and_edge) (graph:abduction_graph): abduction_graph =
  let
    val graph_w_ornode_is_now_branch        = UAG.update_is_branch parent_ornd graph                                 : abduction_graph;
    (*add an or2and_ege and connect them to their parental or-node if we can prove the or-node assuming the and-node.*)
    val (or2and_edge_opt, used_and_node_name_term_pairs, graph_w_connected_or2add_edges) =
       add_or2and_edge_and_connect_it_to_parental_ornode parent_ornd seed graph_w_ornode_is_now_branch: (key option * (string * term) list * abduction_graph);
    val parent_ornd_is_proved_assmng_seed   = is_some or2and_edge_opt: bool;
  in
    if   parent_ornd_is_proved_assmng_seed
    then
      let
        val and_node_terms = map snd used_and_node_name_term_pairs: terms;
        (*length added_andnode_keys should be 1.*)
        val (added_andnode_keys, graph_w_addnodes) = UAG.add_andnode and_node_terms graph_w_connected_or2add_edges                       : (key list * abduction_graph);
        val _                                      = if length added_andnode_keys = 1 then () else error "length added_andnode_keys != 1"
        val or2and_edge_key                        = the or2and_edge_opt                                                                 : key;
        val added_andnode_key                      = hd added_andnode_keys                                                               : key;
        val graph_w_connected_andnode              = UAG.add_edge_acyclic_if_possible or2and_edge_key added_andnode_key graph_w_addnodes : abduction_graph;
        val graph_w_child_ornode                   = fold UAG.add_child_ornode used_and_node_name_term_pairs graph_w_connected_andnode   : abduction_graph;
        val graph_w_connected_child_ornode         = UAG.add_edges_from_andnode_to_ornodes added_andnode_key graph_w_child_ornode        : abduction_graph
      in
        graph_w_connected_child_ornode
      end
    else graph
  end;

fun seeds_to_updated_graph (parent_ornd:key) (seeds: seeds_of_or2and_edge) (graph:abduction_graph) =
  fold (add_then_connect_or2and_edge_andnd_ornds parent_ornd) seeds graph: abduction_graph;

end;