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
val add_or2and_edge                                  : key -> seed_of_andnode -> abduction_graph -> abduction_graph;

val filter_out_bad_seeds_of_andnode: term (*parental or-node*) -> Proof.state -> abduction_graph -> seeds_of_andnode -> seeds_of_andnode
val conjectures_to_seeds_of_andnode: (Proof.state (*default pst*) * Proof.state (*chained pst to proved the parental ornode*)) -> terms -> seeds_of_andnode;

end;

(*** Seed_Of_And_Node ***)
structure Seed_Of_And_Node: SEED_OF_AND_NODE =
struct

structure PGraph = Abduction_Graph.PGraph;

type abduction_graph                 = Abduction_Graph.abduction_graph;
type key                             = Abduction_Graph.key;
type keys                            = Abduction_Graph.keys;
type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;
type abduction_node                  = Abduction_Node.abduction_node;

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
    val timeouts      = {overall = 60.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}   : TBC_Utils.timeouts;
    val result_seq    = TBC_Utils.psl_strategy_to_monadic_tactic timeouts extend_str pst []: (Dynamic_Utils.log * Proof.state) Seq.seq;
    val result_list   = Seq.list_of result_seq                                             : (Dynamic_Utils.log * Proof.state) list;
    val script_n_psts = map (apfst Dynamic_Utils.mk_apply_script) result_list              : (string * Proof.state) list;
    fun mk_proof_key_value (pscript, pst) =
        let
          val subgs = Isabelle_Utils.pst_to_subgs pst
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
  
          val key   = (Abduction_Graph.And_N, nonempty_subgs): key;
          val value = Abduction_Node.And_Node
                 ({subgoals          = nonempty_subgs,
                   proved_completely = false,
                   refuted           = false}: And_Node.andnode): abduction_node;
        in
          {proof = Or2And_Edge.Tactic pscript, andnode_key = key, value = value, state = pst}: seed_of_andnode
        end;
  in
    map mk_proof_key_value script_n_psts: seeds_of_andnode
  end;

(* add_or2and_edge *)
fun add_or2and_edge
     (or_key as (Abduction_Graph.Or_N, [ornode_term]):key)(*parent node*)
     ({andnode_key: key,
       proof      : how_to_get_andnodes_from_ornode,
       state      : Proof.state, ...}: seed_of_andnode)(*child nodes*)
   (graph:abduction_graph): abduction_graph =
   let
     val _ = tracing "start add_or2and";
     val or_leave_keys = PGraph.immediate_succs graph andnode_key: keys;(*these or_leave_keys are gg_children of or_key*)
     (*TODO: move it to Proof_Graph.ML*)
     fun or_key_to_term (Abduction_Graph.Or_N, [orleaf_term]) = orleaf_term
       | or_key_to_term  _                                    = error "or_key_to_term failed.";
     fun mk_name_term_pair (orleaf_key:key) = (Abduction_Graph.lemma_name_of graph orleaf_key, or_key_to_term orleaf_key): (string * term);
     val name_term_pairs      = map mk_name_term_pair or_leave_keys                                                      : (string * term) list;
     val pst_w_or_terms_assmd = Proof.map_context (TBC_Utils.assume_terms_in_ctxt name_term_pairs) state                 : Proof.state;(*TODO: FIXME:*)
     val timeouts             = {overall = 30.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}                         : TBC_Utils.timeouts;
     (*TODO: FIXME: \<rightarrow> No need to fix?*)
     (*
      * The use of pst_w_or_term_assmd is wrong here.
      * We use a Proof.state to attack the (remaining) of or-node.
      * But this state is for the and-node.
      * We should send a proof state that is associated with or-node.
      *)
     (*very expensive*)
     val script_opt_gen       = TBC_Utils.pst_to_proofscript_opt timeouts "finish_goal_after_assuming_subgoals_n_conjectures" pst_w_or_terms_assmd <$> fst: string option;

     val how_we_got_andnode   = Or2And_Edge.how_to_get_andnodes_from_ornode_of proof                    : string;
     fun mk_script_opt_for_tactic (tactic_script:string) = how_we_got_andnode ^ tactic_script: string;
     val script_opt: string option =
          if how_we_got_andnode = "" (*explicit conjecturing*)
          then                                                                                     
            script_opt_gen
          else
            Option.map mk_script_opt_for_tactic script_opt_gen;
     (*TODO: or2and_edge_val is a function on abduction_node. It should be encapsulated in Proof_Node.ML.*)
     val or2and_edge_val     = Abduction_Node.Or_To_And {
                                 how_to_get_andnodes_from_ornode = proof,
                                 proof_of_ornode_assmng_andnodes = script_opt}: abduction_node;
     val or2and_edge_key     = ((Abduction_Graph.O2A_E (serial())), []): key;

     (* updating abduction_graph *)
     (* TODOL These 3 functions should be executed atomically with Mutex.*)
     val graph_w_or2and_edge = PGraph.new_node (or2and_edge_key, or2and_edge_val) graph: abduction_graph;
     val graph_w_or2and_edge_connected = graph_w_or2and_edge
                                      |> Update_Abduction_Graph.add_edge_acyclic_if_possible or_key or2and_edge_key
                                      |> Update_Abduction_Graph.add_edge_acyclic_if_possible or2and_edge_key andnode_key: abduction_graph;
     (*This cuts the edge that connects or2and_edge_key and andnode.*)
     fun cut_edge_to_andnode_if_no_parental_ornode_can_be_proved_assmng_subgoals (or2and_edge_key:key) (graph:abduction_graph): abduction_graph =
       (* If connecting the labelled-edge and and-node would make the graph cyclic, *)
       (* we should not have added an edge between the labelled-edge and and-node.  *)
       if PGraph.is_edge graph (andnode_key, or2and_edge_key)
       then
         let
           val and_keys = PGraph.immediate_succs graph or2and_edge_key: keys;
           val _        = if length and_keys = 1 then () else error "cut_edge_from_andnode_to_ornode_if_no_parental_ornode_can_be_proved_assmng_subgoals failed. Zero or more than one and_keys.";
           val and_key  = hd and_keys: key;
           val parental_ornode_can_be_proved_assmng_subgoals = Abduction_Graph.ornode_proved_assmng_andnodes graph or2and_edge_key: bool;
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

fun condition_to_filter_out (parent_or:term) (pst:Proof.state) (pg:abduction_graph) (seed:seed_of_andnode) =
    let
      val final_goal      = Abduction_Graph.get_final_goal pg |> snd |> hd: term;
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

fun filter_out_bad_seeds_of_andnode (parent_or:term) (pst:Proof.state) (graph:abduction_graph) (seeds:seeds_of_andnode) =
  filter_out (condition_to_filter_out parent_or pst graph) seeds: seeds_of_andnode;
                                                                                      
fun conjectures_to_seed_of_andnode (pst:Proof.state) (cnjctr:term): seed_of_andnode =
  let
    val (key, abduction_node) = Abduction_Graph.mk_andnode [cnjctr]
  in
     {andnode_key = key                   : key,
      proof       = Or2And_Edge.Conjecture: how_to_get_andnodes_from_ornode,
      value       = abduction_node        : abduction_node,
      state       = pst                   : Proof.state}
  end;

fun conjectures_to_seeds_of_andnode (pst:Proof.state, pst_to_prove_ornode:Proof.state) (cnjctrs:terms) =
  let
    val ctxt                      = Proof.context_of pst                                               : Proof.context;
    fun get_ctxt_w_proof_goal trm = Proof.context_of (Top_Down_Util.mk_pst_to_prove_from_term ctxt trm): Proof.context;
    fun check_prop (trm:term)     = try (Syntax.check_prop (get_ctxt_w_proof_goal trm)) trm            : term option;
    val checked_cnjctrs = List.mapPartial check_prop cnjctrs
    val result          = map (fn trm => conjectures_to_seed_of_andnode pst_to_prove_ornode trm) checked_cnjctrs
  in
    result
  end;

end;