(*
 * Seed_Of_And_Node.ML 
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** SEED_OF_AND_NODE ***)
signature SEED_OF_AND_NODE =
sig

type abduction_graph;
type key;
type how_to_get_andnodes_from_ornode;
type abduction_node
type seed_of_andnode =
     {andnode_key: key,
      proof      : how_to_get_andnodes_from_ornode,
      value      : abduction_node,
      state      : Proof.state};
type seeds_of_andnode;

val print_seed_of_andnode: Proof.context -> seed_of_andnode -> unit list;
val seed_is_from_tactic  : seed_of_andnode -> bool;

val apply_Extend_Leaf_to_pst_to_get_seeds_of_andnodes: Proof.state -> seed_of_andnode list;
val add_or2and_edge_connected_to_parental_ornode: key -> seed_of_andnode -> abduction_graph ->
    ((*or2edge*)key option * (*used and_nodes*)(string * term) list *  abduction_graph);

val filter_out_bad_seeds_of_andnode: term (*parental or-node*) -> Proof.state -> abduction_graph -> seeds_of_andnode -> seeds_of_andnode
val conjectures_to_seeds_of_andnode: (Proof.state (*default pst*) * Proof.state (*chained pst to proved the parental ornode*)) -> terms -> seeds_of_andnode;

val seed_of_andnode_has_counterexample: Proof.state -> seed_of_andnode -> bool;

end;

(*** Seed_Of_And_Node ***)
structure Seed_Of_And_Node: SEED_OF_AND_NODE =
struct

open Abduction_Graph;

type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;

type seed_of_andnode =
     {andnode_key: key,
      proof      : how_to_get_andnodes_from_ornode,
      value      : abduction_node,
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
  
          val key   = (And_N, nonempty_subgs): key;
          val value = Abduction_Node.And_Node
                 ({subgoals          = nonempty_subgs,
                   proved_completely = false}: And_Node.andnode): abduction_node;
        in
          {proof = Or2And_Edge.Tactic pscript, andnode_key = key, value = value, state = pst}: seed_of_andnode
        end;
  in
    map mk_proof_key_value script_n_psts: seeds_of_andnode
  end;

(* add_or2and_edge *)
(*
(*TODO: rename this function to emphasize that it also cuts edges to and-nodes (and or-nodes).*)
fun add_or2and_edge
     (or_key as (Or_N, [ornode_term]):key)(*parent node*)
     ({andnode_key: key,
       proof      : how_to_get_andnodes_from_ornode,
       state      : Proof.state, ...}: seed_of_andnode)(*child nodes*)
   (graph:abduction_graph): abduction_graph =
   let
     val _ = tracing "start add_or2and";
     fun mk_name_term_pair (orleaf_key:key) = (lemma_name_of graph orleaf_key, orkey_to_term orleaf_key): (string * term);
     val or_leave_keys        = PGraph.immediate_succs graph andnode_key                                : keys;(*these or_leave_keys are gg_children of or_key*)
     val name_term_pairs      = map mk_name_term_pair or_leave_keys                                     : (string * term) list;
     val pst_w_or_terms_assmd = Top_Down_Util.assume_cnjctrs_in_pst name_term_pairs state               : Proof.state;
     val timeouts             = {overall = 30.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}        : TBC_Utils.timeouts;

     (*very expensive*)
     val script_opt_gen       = TBC_Utils.pst_to_proofscript_opt timeouts "finish_goal_after_assuming_subgoals_n_conjectures" pst_w_or_terms_assmd <$> fst: string option;

     val how_we_got_andnode   = Or2And_Edge.how_to_get_andnodes_from_ornode_of proof         : string;
     val script_opt           = Option.map (fn script => how_we_got_andnode ^ script) script_opt_gen;
     val or2and_edge_val      = Abduction_Node.Or_To_And {
                                 how_to_get_andnodes_from_ornode = proof,
                                 proof_of_ornode_assmng_andnodes = script_opt}: abduction_node;
     val or2and_edge_key      = ((O2A_E (serial())), []): key;

     (* updating abduction_graph *)
     val graph_w_or2and_edge_connected = graph
      |> PGraph.new_node (or2and_edge_key, or2and_edge_val)
      |> Update_Abduction_Graph.add_edge_acyclic_if_possible or_key or2and_edge_key
      |> Update_Abduction_Graph.add_edge_acyclic_if_possible or2and_edge_key andnode_key: abduction_graph;

     (*TODO: call cut_edge_from_or2and_edge_to_andnode_if_no_parental_ornode_can_be_proved_assmng_subgoals not here
              but in seed_to_updated_graph in Proof_By_Abduction.ML*)
     val result = cut_edge_from_or2and_edge_to_andnode_if_no_parental_ornode_can_be_proved_assmng_subgoals
                  andnode_key or2and_edge_key graph_w_or2and_edge_connected;
   in
     if is_some script_opt then result else graph
   end
 | add_or2and_edge _ _ _ = error "how_to_prove_ornode_assmng_subgs_of_andnode failed."
*)

fun add_or2and_edge_connected_to_parental_ornode
     (parent_or_key as (Or_N, _): key)(*parent node*)
     ({andnode_key as (And_N, and_trms): key,
       proof            : how_to_get_andnodes_from_ornode,
       state(*chained*) : Proof.state, ...}: seed_of_andnode)(*child nodes*)
     (graph:abduction_graph): (key option * (string * term) list * abduction_graph) =
   let
     val _ = tracing "start add_or2and";
     fun mk_temp_name (trm:term) =
       let
         val child_or_key             = (Or_N, [trm]) : key;
         val maybe_child_or_val       = try (PGraph.get_node graph) child_or_key: abduction_node option;
         val child_or_already_exists  = is_some (maybe_child_or_val): bool;
       in
         if child_or_already_exists
         then
           lemma_name_of graph child_or_key: string
         else
           Top_Down_Util.mk_new_lemma_name (Proof.context_of state)
       end;
     val name_term_pairs      = map (fn and_trm => (mk_temp_name and_trm, and_trm)) and_trms    : (string * term) list;
     val pst_w_or_terms_assmd = Top_Down_Util.assume_cnjctrs_in_pst name_term_pairs state       : Proof.state;
     (*TODO: maybe we should assume or-nodes that have been already proved completely in the abduction_graph.*)
     val timeouts             = {overall = 30.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}: TBC_Utils.timeouts;
     (*very expensive*)
     val script_opt_gen       = TBC_Utils.pst_to_proofscript_opt timeouts "finish_goal_after_assuming_subgoals_n_conjectures" pst_w_or_terms_assmd <$> fst: string option;
     val proved_parent_or     = is_some script_opt_gen: bool;
   in
     if proved_parent_or
     then
       let
         val how_we_got_andnode    = Or2And_Edge.how_to_get_andnodes_from_ornode_of proof: string;
         val script_to_prove_andnd = the script_opt_gen                                  : string;
         val script_to_prove_ornd  = how_we_got_andnode ^ script_to_prove_andnd          : string;
         val or2and_edge_val       = Abduction_Node.Or_To_And {
                                      how_to_get_andnodes_from_ornode = proof,
                                      (*TODO: Should we really need to use the option type here?*)
                                      proof_of_ornode_assmng_andnodes = SOME script_to_prove_ornd}               : abduction_node;
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
 | add_or2and_edge_connected_to_parental_ornode _ _ _ = error "how_to_prove_ornode_assmng_subgs_of_andnode failed."

fun condition_to_filter_out (parent_or:term) (pst:Proof.state) (ag:abduction_graph) (seed:seed_of_andnode) =
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

      val trms               = snd (#andnode_key seed): terms;
      val trms_empty         = null trms              : bool;
      fun too_large _        = exists (fn trm => Real.fromInt (Term.size_of_term trm) > upper_limit) trms: bool;
      fun eq_to_final_goal _ = exists (Top_Down_Util.alpha_eq_over_fvar final_goal) trms: bool;
      fun concl_is_eq_to_final_goal _ = exists (concl_is_alpha_eq_to final_goal) trms: bool;
      fun has_func_with_three_occs_in_a_row _ = exists
      (fn trm => SeLFiE_for_Top_Down.run_assertion (Top_Down_Util.mk_pst_to_prove_from_term (Proof.context_of pst) trm) SeLFiE_for_Top_Down.has_func_with_three_occs_in_a_row trm) trms;
      fun has_counter_example_in_prems (pst:Proof.state) (term:term) =
        let
          val prems = Logic.strip_imp_prems term: terms;
        in
           exists (Shared_State.is_refuted pst) prems: bool
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

fun filter_out_bad_seeds_of_andnode (parent_or:term) (pst:Proof.state) (graph:abduction_graph) (seeds:seeds_of_andnode) =
  filter_out (condition_to_filter_out parent_or pst graph) seeds: seeds_of_andnode;
                                                                                      
fun conjectures_to_seed_of_andnode (pst:Proof.state) (cnjctr:term): seed_of_andnode =
  let
    val (key, abduction_node) = mk_andnode [cnjctr]
  in
     {andnode_key = key                   : key,
      proof       = Or2And_Edge.Conjecture: how_to_get_andnodes_from_ornode,
      value       = abduction_node        : abduction_node,
      state       = pst                   : Proof.state}
  end;

fun conjectures_to_seeds_of_andnode (pst:Proof.state, pst_to_prove_ornode:Proof.state) (cnjctrs:terms) =
  let
    (*TODO: Why do we need two Proof.states?*)
    val ctxt                      = Proof.context_of pst                                               : Proof.context;
    fun get_ctxt_w_proof_goal trm = Proof.context_of (Top_Down_Util.mk_pst_to_prove_from_term ctxt trm): Proof.context;
    fun check_prop (trm:term)     = try (Syntax.check_prop (get_ctxt_w_proof_goal trm)) trm            : term option;
    val checked_cnjctrs           = List.mapPartial check_prop cnjctrs
    val result                    = map (fn trm => conjectures_to_seed_of_andnode pst_to_prove_ornode trm) checked_cnjctrs
  in
    result
  end;

fun seed_of_andnode_has_counterexample (pst:Proof.state) ({andnode_key,...}:seed_of_andnode) =
  case andnode_key of
    (And_N, cnjctrs) => Shared_State.any_of_these_is_refuted pst cnjctrs
  | _ => error "seed_of_andnode_has_counterexample failed. Not a seed_of_andnode."

end;