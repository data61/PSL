(*
 * Proof_By_Abduction_Util.ML 
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** PROOF_BY_ABDUCTION_UTIL ***)
signature PROOF_BY_ABDUCTION_UTIL =
sig

type proof_graph;
type key;
type how_to_get_andnodes_from_ornode;
type andnode;
type proof_node
type seed_of_andnode =
     {andnode_key: key,
      proof      : how_to_get_andnodes_from_ornode,
      value      : proof_node,
      state      : Proof.state};
type seeds_of_andnode;

val print_seed_of_andnode: Proof.context -> seed_of_andnode -> unit list;
val seed_is_from_tactic: seed_of_andnode -> bool;

val find_counterexample_update                       : Proof.state -> key -> proof_graph -> proof_graph;
val find_counterexample_update'                      : Proof.state -> (key * bool) -> proof_graph -> proof_graph;
val mk_pst_to_prove_from_key                         : Proof.state -> key -> Proof.state;
val prove_orkey_completely                           : key -> proof_graph -> Proof.state -> (Proof.state * string) option;
(*TODO: apply_Extend_Leaf_to_pst_to_get_seeds_of_andnodes is called only once. No need to export it.*)
val apply_Extend_Leaf_to_pst_to_get_seeds_of_andnodes: Proof.state -> seed_of_andnode list;
val add_or2and_edge                                  : key -> seed_of_andnode -> proof_graph -> proof_graph;

val filter_out_bad_seeds_of_andnode: term (*parental or-node*) -> Proof.state -> proof_graph -> seeds_of_andnode -> seeds_of_andnode
val conjectures_to_seeds_of_andnode: (Proof.state (*default pst*) * Proof.state (*chained pst to proved the parental ornode*)) -> terms -> seeds_of_andnode;

end;

(*** Proof_By_Abduction ***)
structure Proof_By_Abduction_Util: PROOF_BY_ABDUCTION_UTIL =
struct

structure PGraph = Proof_Graph.PGraph;

type proof_graph                     = Proof_Graph.proof_graph;
type key                             = Proof_Graph.key;
type keys                            = Proof_Graph.keys;
type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;
type andnode                         = And_Node.andnode;
type proof_node                      = Proof_Graph_Node.proof_node;

type seed_of_andnode =
     {andnode_key: key,
      proof      : how_to_get_andnodes_from_ornode,
      value      : proof_node,
      state      : Proof.state};

type seeds_of_andnode = seed_of_andnode list;

fun print_seed_of_andnode ctxt ({andnode_key,...}: seed_of_andnode) = (
  tracing "== print_seed_of_andnode:  ==";
  map (tracing o Isabelle_Utils.trm_to_string ctxt) (snd andnode_key)
);

fun seed_is_from_tactic ({proof, ...}) = Or2And_Edge.proof_is_from_tactic proof: bool;

(* apply_Extend_Leaf_to_pst_get_records_to_mk_andnodes *)
(*TODO: handle the case where we actually finish to prove this.*)
fun apply_Extend_Leaf_to_pst_to_get_seeds_of_andnodes (pst:Proof.state) =
    let
      val ctxt          = Proof.context_of pst;
      val extend_str    = PSL_Interface.lookup ctxt "Extend_Leaf" |> the                     : PSL_Interface.strategy;
      val timeouts      = {overall = 60.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}   : TBC_Utils.timeouts;
      val result_seq    = TBC_Utils.psl_strategy_to_monadic_tactic timeouts extend_str pst []: (Dynamic_Utils.log * Proof.state) Seq.seq;
      val result_list   = Seq.list_of result_seq                                             : (Dynamic_Utils.log * Proof.state) list;
      val script_n_psts = map (apfst Dynamic_Utils.mk_apply_script) result_list              : (string * Proof.state) list;
      fun mk_proof_key_value (pscript, pst) =
          let
            val subgs = Isabelle_Utils.pst_to_subgs pst
(*
val _ = tracing "------"
val _ = map (Isabelle_Utils.trm_to_string ctxt) subgs |> map tracing
*)
            val subgs_wo_meta_uni = map strip_outermost_meta_quantifiers subgs: terms;
            fun check_print_read ctxt term = term
             |> Syntax.check_term ctxt
             |> Isabelle_Utils.trm_to_string ctxt
             |> Syntax.read_term ctxt
             |> Top_Down_Util.standardize_vnames;

            fun check_print_read_terms ctxt terms = map (check_print_read ctxt) terms: terms;
            fun pass_check_print_read_terms ctxt terms = try (check_print_read_terms ctxt) terms |> is_some;

            val nonempty_subgs =
              if length subgs = 0 orelse not (pass_check_print_read_terms ctxt subgs_wo_meta_uni)
              then [@{prop "True"}]
              else subgs_wo_meta_uni: terms;

            val key   = (Proof_Graph.And_N, nonempty_subgs): key;
            val value = Proof_Graph_Node.And_Node
                   ({subgoals          = nonempty_subgs,
                     proved_completely = false,
                     refuted           = false}: andnode): proof_node;
          in
            {proof = Or2And_Edge.Tactic pscript, andnode_key = key, value = value, state = pst}: seed_of_andnode
          end;
    in
      map mk_proof_key_value script_n_psts: seeds_of_andnode
    end;

(* find_counterexample_update *)
(*TODO: To be removed?*)
(*TODO: for andnodes we can get the result quickly if we use its children (ornodes) -> Maybe it is better to *)
fun find_counterexample_update (pst:Proof.state) (key:key) (graph:proof_graph) =
  let
    val found_counter_example = exists (fn trm => TBC_Utils.term_has_counterexample_in_pst trm pst) (snd key)
  in
    if   found_counter_example
    then PGraph.map_node key Proof_Graph_Node_Util.update_refuted graph(*TODO: We need update_refuted in Proof_Graph.ML*)
    else graph
  end;

fun find_counterexample_update' (pst:Proof.state) (key:key, has_counterexample: bool) (graph:proof_graph) =
    if   has_counterexample
    then PGraph.map_node key Proof_Graph_Node_Util.update_refuted graph(*TODO: We need update_refuted in Proof_Graph.ML*)
    else graph;

(* mk_pst_to_prove_from_key *)
(*TODO: Don't ignore local assumptions.*)
fun mk_pst_to_prove_from_key (pst:Proof.state) (Proof_Graph.Or_N, [term]) =
    let
      val prop = if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] (Proof.context_of pst): Proof.state
    end
  | mk_pst_to_prove_from_key (pst:Proof.state) (Proof_Graph.And_N, [term]) =
    let
      val prop = if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] (Proof.context_of pst): Proof.state
    end
  | mk_pst_to_prove_from_key _ _ = error "mk_pst_to_prove_from_key failed!";

(* prove_orkey_completely *)
fun prove_orkey_completely (or_key as (Proof_Graph.Or_N:Proof_Graph.node_type, [lemma_term]):key) (graph:proof_graph) (pst:Proof.state) =
    let
      val lemma_name            = Proof_Graph.lemma_name_of graph or_key                                    : string;
      val pst_to_prove          = mk_pst_to_prove_from_key pst or_key                                       : Proof.state;
      val timeouts              = {overall = 30.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}          : TBC_Utils.timeouts;
      val maybe_result          = TBC_Utils.pst_to_proofscript_opt timeouts "Attack_On_Or_Node" pst_to_prove: (string * Proof.state) option;
      val cheated_pst           = TBC_Utils.cheat_lemma_term_in_pst lemma_name lemma_term pst
      fun mk_result (script, _) = Option.map (rpair script) cheated_pst;
      val result                = Option.mapPartial mk_result maybe_result: (Proof.state * string) option
    in
      result
    end
  | prove_orkey_completely _ _ _ = error "try_to_prove_orkey_completely failed!";

(* add_or2and_edge *)
fun add_or2and_edge
     (or_key as (Proof_Graph.Or_N, [ornode_term]):key)(*parent node*)
     ({andnode_key: key,
       proof      : how_to_get_andnodes_from_ornode,
       state      : Proof.state, ...}: seed_of_andnode)(*child nodes*)
   (graph:proof_graph): proof_graph =
   let
     val _ = tracing "start add_or2and";
     val or_leave_keys = PGraph.immediate_succs graph andnode_key: keys;(*these or_leave_keys are gg_children of or_key*)
     (*TODO: move it to Proof_Graph.ML*)
     fun or_key_to_term (Proof_Graph.Or_N, [orleaf_term]) = orleaf_term
       | or_key_to_term  _                                = error "or_key_to_term failed.";
     fun mk_name_term_pair (orleaf_key:key) = (Proof_Graph.lemma_name_of graph orleaf_key, or_key_to_term orleaf_key): (string * term);
     val name_term_pairs      = map mk_name_term_pair or_leave_keys                                     : (string * term) list;
     val pst_w_or_terms_assmd = Proof.map_context (TBC_Utils.assume_terms_in_ctxt name_term_pairs) state: Proof.state;(*TODO: FIXME:*)
     val timeouts             = {overall = 30.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}        : TBC_Utils.timeouts;
     val how_we_got_andnode   = Or2And_Edge.how_to_get_andnodes_from_ornode_of proof                    : string;
(*     
     val _ = tracing "-"
     val _ = tracing "finish_goal_after_assuming_subgoals_n_conjectures. ";
     val _ = tracing "or-node is: "
     val _ = (Proof_Graph.print_key (Proof.context_of state) or_key)
     val _ = tracing "and-node is: "
     val _ = (Proof_Graph.print_key (Proof.context_of state) andnode_key)
*)
(*TODO: FIXME: \<rightarrow> No need to fix?*)
(*
 * The use of pst_w_or_term_assmd is wrong here.
 * We use a Proof.state to attack the (remaining) of or-node.
 * But this state is for the and-node.
 * We should send a proof state that is associated with or-node.
 *)
     val script_opt_gen = TBC_Utils.pst_to_proofscript_opt timeouts "finish_goal_after_assuming_subgoals_n_conjectures" pst_w_or_terms_assmd <$> fst: string option;
     fun mk_script_opt_for_tactic (tactic_script:string) = how_we_got_andnode ^ tactic_script: string;
     val script_opt: string option =
          if how_we_got_andnode = "" (*explicit conjecturing*)
          then                                                                                     
            script_opt_gen
          else
            Option.map mk_script_opt_for_tactic script_opt_gen(*TODO: We have to check if we can prove the remaining goals.*)
     (*TODO: or2and_edge_val is a function on proof_node. It should be encapsulated in Proof_Node.ML.*)
     val or2and_edge_val     = Proof_Graph_Node.Or_To_And {
                                 how_to_get_andnodes_from_ornode = proof,
                                 proof_of_ornode_assmng_andnodes = script_opt}: proof_node;
     val or2and_edge_key     = ((Proof_Graph.O2A_E (serial())), []): key;
     val graph_w_or2and_edge = PGraph.new_node (or2and_edge_key, or2and_edge_val) graph: proof_graph;
     val graph_w_or2and_edge_connected = graph_w_or2and_edge
                                      |> Proof_Graph_Util.add_edge_acyclic_if_possible or_key or2and_edge_key
                                      |> Proof_Graph_Util.add_edge_acyclic_if_possible or2and_edge_key andnode_key: proof_graph;
     (*This cuts the edge that connects or2and_edge_key and andnode.*)
     fun cut_edge_to_andnode_if_no_parental_ornode_can_be_proved_assmng_subgoals (or2and_edge_key:key) (graph:proof_graph): proof_graph =
       (* If connecting the labelled-edge and and-node would make the graph cyclic, *)
       (* we should not have added an edge between the labelled-edge and and-node.  *)
       if PGraph.is_edge graph (andnode_key, or2and_edge_key)
       then
         let
           val and_keys = PGraph.immediate_succs graph or2and_edge_key: keys;
           val _        = if length and_keys = 1 then () else error "cut_edge_from_andnode_to_ornode_if_no_parental_ornode_can_be_proved_assmng_subgoals failed. Zero or more than one and_keys.";
           val and_key  = hd and_keys: key;
           val parental_ornode_can_be_proved_assmng_subgoals = Proof_Graph.ornode_proved_assmng_andnodes graph or2and_edge_key: bool;
         in
           if parental_ornode_can_be_proved_assmng_subgoals
           then graph
           else PGraph.del_edge (or2and_edge_key, and_key) graph
         end
       else graph;
     val result = cut_edge_to_andnode_if_no_parental_ornode_can_be_proved_assmng_subgoals or2and_edge_key graph_w_or2and_edge_connected;
   in
     if is_some script_opt then result else graph
   end
 | add_or2and_edge _ _ _ = error "how_to_prove_ornode_assmng_subgs_of_andnode failed."

val tracing' = if true then tracing else K ();

fun condition_to_filter_out (parent_or:term) (pst:Proof.state) (pg:proof_graph) (seed:seed_of_andnode) =
    let
      val final_goal      = Proof_Graph.get_final_goal pg |> snd |> hd: term;
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

      val trms       = snd (#andnode_key seed)                                    : terms;
      val trms_empty = null trms
      fun too_large _ = exists (fn trm => Real.fromInt (Term.size_of_term trm) > upper_limit) trms: bool;
      fun eq_to_final_goal _ = exists (Top_Down_Util.alpha_eq_over_fvar final_goal) trms: bool;
      fun concl_is_eq_to_final_goal _ = exists (concl_is_alpha_eq_to final_goal) trms: bool;
      fun has_func_with_three_occs_in_a_row _ = exists
      (fn trm => SeLFiE_for_Top_Down.run_assertion (Top_Down_Util.mk_pst_to_prove_from_term (Proof.context_of pst) trm) SeLFiE_for_Top_Down.has_func_with_three_occs_in_a_row trm) trms;
    in
      trms_empty orelse too_large () orelse
      (eq_to_final_goal () andalso seed_is_from_tactic seed) orelse
      (concl_is_eq_to_final_goal () andalso seed_is_from_tactic seed) orelse
      has_func_with_three_occs_in_a_row ()
    end;

fun filter_out_bad_seeds_of_andnode (parent_or:term) (pst:Proof.state) (graph:proof_graph) (seeds:seeds_of_andnode) =
  filter_out (condition_to_filter_out parent_or pst graph) seeds: seeds_of_andnode;
                                                                                      
fun conjectures_to_seed_of_andnode (pst:Proof.state) (cnjctr:term): seed_of_andnode =
  let
    val (key, proof_node) = Proof_Graph.mk_andnode [cnjctr]
  in
     {andnode_key = key                   : key,
      proof       = Or2And_Edge.Conjecture: how_to_get_andnodes_from_ornode,
      value       = proof_node            : proof_node,
      state       = pst                   : Proof.state}
  end;

(*TODO: code-duplication with mk_pst_to_prove_from_key*)
fun mk_pst_to_prove_from_term (pst:Proof.state) (term:term) =
    let
      val prop = if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term;
    in
      Proof.theorem NONE (K I) [[(prop, [])]] (Proof.context_of pst): Proof.state
    end;

fun conjectures_to_seeds_of_andnode (pst:Proof.state, pst_to_prove_ornode:Proof.state) (cnjctrs:terms) =
let
  fun check_prop (trm:term) = try (Syntax.check_prop (Proof.context_of (mk_pst_to_prove_from_term pst trm))) trm: term option;
  val checked_cnjctrs = List.mapPartial check_prop cnjctrs
  val result = map (fn trm => conjectures_to_seed_of_andnode pst_to_prove_ornode trm) checked_cnjctrs
in
  result
end;
(*
     map (try (Syntax.check_term (Proof.context_of pst))) cnjctrs
  |> Utils.somes
  |> map (conjectures_to_seed_of_andnode pst): seeds_of_andnode;
*)
end;