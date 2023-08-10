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
type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;
type abduction_node;
type seed_of_or2and_edge =
     {new_goals: (string * term) list,
      proof    : how_to_get_andnodes_from_ornode};
type seeds_of_or2and_edge;

val print_seed_of_or2and_edge             : Proof.context -> seed_of_or2and_edge -> unit list;
val seed_is_from_tactic                   : seed_of_or2and_edge -> bool;
val apply_PSL_to_get_seeds_of_or2and_edges: Shared_State.synched_term2string_table -> Proof.state -> seeds_of_or2and_edge;
val condition_to_filter_out_cnjctr        : term -> Shared_State.synched_term2bool_table -> Proof.state -> abduction_graph -> bool (*from_tactic*) -> term (*cnjctr*) -> bool;
val filter_out_bad_seeds_from_tactic      : term (*parental or-node*) -> Shared_State.synched_term2bool_table -> Proof.state -> abduction_graph -> seeds_of_or2and_edge -> seeds_of_or2and_edge
val conjectures_to_seed_of_or2and_edge    : Shared_State.synched_term2string_table -> Proof.state -> (string * term) list -> seed_of_or2and_edge;
val seed_has_counterexample               : Shared_State.synched_term2bool_table -> Proof.state -> seed_of_or2and_edge -> bool;
val seeds_to_updated_graph                : Proof.state -> key -> seeds_of_or2and_edge -> Shared_State.synched_abduction_graph -> unit;
val decremental_abduction                 : Proof.state -> key -> seed_of_or2and_edge -> Shared_State.synched_term2string_table -> Shared_State.synched_abduction_graph -> unit;

end;

(*** Seed_Of_Or2And_Edge ***)
structure Seed_Of_Or2And_Edge: SEED_OF_OR2AND_EDGE =
struct

open Abduction_Graph;
structure UAG = Update_Abduction_Graph;
structure SS  = Shared_State;

type how_to_get_andnodes_from_ornode = Or2And_Edge.how_to_get_andnodes_from_ornode;

type seed_of_or2and_edge =
     {new_goals: (string * term) list,
      proof    : how_to_get_andnodes_from_ornode};

type seeds_of_or2and_edge = seed_of_or2and_edge list;

fun tracing' mssg = tracing mssg;

fun print_seed_of_or2and_edge ctxt ({new_goals,...}: seed_of_or2and_edge) = (
  (*tracing' "== print_seed_of_or2and_edge:  ==";*)
  map (fn goal => tracing' (fst goal ^ " | " ^ Isabelle_Utils.trm_to_string ctxt (snd goal))) new_goals
);

fun seed_is_from_tactic ({proof, ...}) = Or2And_Edge.proof_is_from_tactic proof: bool;

(* apply_Extend_Leaf_to_pst_get_records_to_mk_andnodes *)
(* The return type of this function should be seeds_of_or2and_edge because we need the resulting
 * proof states. *)
fun apply_PSL_to_get_seeds_of_or2and_edges (synched_term2string:SS.synched_term2string_table) (pst:Proof.state) =
  let
    fun tracing' mssg = ()(*tracing mssg*);
    val _ = tracing' "\nGGGGGGGG apply_PSL_to_get_seeds_of_or2and_edges";
    val ctxt          = Proof.context_of pst;
    val extend_str    = PSL_Interface.lookup ctxt "Extend_Leaf" |> the                      : PSL_Interface.strategy;
    val timeouts      = {overall = 60.0, hammer = 5.0, quickcheck = 1.0, nitpick = 2.0}     : TBC_Utils.timeouts;
    val result_seq    = TBC_Utils.psl_strategy_to_monadic_tactic timeouts extend_str pst [] : (Dynamic_Utils.log * Proof.state) Seq.seq;
    val result_list   = Seq.list_of result_seq                                              : (Dynamic_Utils.log * Proof.state) list;
    val _ = tracing' "\n YEYEYEYE"
    val _ = map (fn result => (tracing' "\n one result:"; (tracing' o Dynamic_Utils.mk_apply_script o fst) result)) result_list
    val script_n_psts = map (apfst Dynamic_Utils.mk_apply_scripts_for_abduction) result_list: (strings * Proof.state) list;
    fun mk_proof_key_value (pscript, pst) =
        let
          val _ = tracing' "\nGFGFGFGFGF mk_proof_key_value"
          val subgs              = Isabelle_Utils.pst_to_subgs pst
          val subgs_wo_meta_uni  = map strip_outermost_meta_quantifiers subgs: terms;
          val standardized_subgs = map Top_Down_Util.standardize_vnames subgs_wo_meta_uni: terms;
          val standardized_props = map (fn term => if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term) standardized_subgs: terms;
          val _ = map (tracing' o (Isabelle_Utils.trm_to_string ctxt)) standardized_props: unit list;

          fun check_print_read ctxt term = term
           |> (fn x => (tracing' ("checking " ^ Isabelle_Utils.trm_to_string ctxt term); x))
           |> Isabelle_Utils.trm_to_string ctxt
           |> (fn x => (tracing' "STEP 1"; x))
           |> Syntax.read_term ctxt
           |> (fn x => (tracing' "STEP 2"; x))
           |> Isabelle_Utils.strip_atyp
           |> (fn x => (tracing' "STEP 3"; x))
           |> Syntax.check_term ctxt
           |> (fn x => (tracing' "STEP 4"; x))
           |> Top_Down_Util.standardize_vnames;


          fun check_print_read_terms ctxt terms      = map (check_print_read ctxt) terms: terms;
          fun pass_check_print_read_terms ctxt terms = try (check_print_read_terms ctxt) terms |> is_some;
          val mk_lemma_name                          = SS.get_lemma_name synched_term2string: Proof.context -> term -> string;

           val _ = if length subgs = 0 then tracing' "FFFFFF length subgs = 0" else tracing' "NOT FFFFFF length subgs = 0";
           val _ = if not (pass_check_print_read_terms ctxt standardized_props) 
                   then tracing' "FFFFF not (pass_check_print_read_terms ctxt standardized_props)" 
                   else tracing' "FFFFFF (pass_check_print_read_terms ctxt standardized_props)";
  
          val nonempty_subgs =
            if length subgs = 0 (*orelse not (pass_check_print_read_terms ctxt standardized_props)*)
            then [(mk_lemma_name ctxt @{prop "True"}, @{prop "True"})]
            else (tracing' "SUCCESS!";
              map (mk_lemma_name ctxt) standardized_props ~~ standardized_props: (string * term) list
              );

          val result = if length subgs = 0 (*orelse not (pass_check_print_read_terms ctxt standardized_props)*)
                       then NONE
                       else SOME {proof = Or2And_Edge.Tactic pscript, new_goals = nonempty_subgs}

        in
          result: seed_of_or2and_edge option
        end;
  in
    List.mapPartial mk_proof_key_value script_n_psts: seeds_of_or2and_edge
  end;


fun condition_to_filter_out_cnjctr (_(*parent_or*):term) (refutation:SS.synched_term2bool_table) (pst:Proof.state) (ag:abduction_graph) (from_tactic:bool) (cnjctr:term) =
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
          val cncl = Logic.strip_imp_concl imp |> Top_Down_Util.remove_Trueprop: term;
        in
          Top_Down_Util.alpha_eq_over_fvar trm cncl
        end;

      fun too_large _                 = Real.fromInt (Term.size_of_term cnjctr) > upper_limit;
      fun eq_to_final_goal _          = Top_Down_Util.alpha_eq_over_fvar final_goal cnjctr: bool;
      fun concl_is_eq_to_final_goal _ = concl_is_alpha_eq_to final_goal cnjctr            : bool;
      fun has_func_with_three_occs_in_a_row _ =
          SeLFiE_For_Top_Down.run_assertion pst cnjctr SeLFiE_For_Top_Down.has_func_with_three_occs_in_a_row;
      fun has_counter_example_in_prems (pst:Proof.state) (term:term) =
        let
          val prems = Logic.strip_imp_prems term: terms;
        in
           SS.any_of_these_is_refuted refutation pst prems: bool
        end;
    in
      too_large () orelse
      eq_to_final_goal () andalso from_tactic orelse
      concl_is_eq_to_final_goal () (*andalso seed_is_from_tactic seed*) orelse
      has_func_with_three_occs_in_a_row () orelse
      has_counter_example_in_prems pst cnjctr
    end;

datatype conjecture_typ = Explicit_Conjecturing | Implicit_Conjecturing (*tactic application*);

fun condition_to_filter_out_seed_from_tactic (parent_or:term) (refutation:SS.synched_term2bool_table) (pst:Proof.state) (ag:abduction_graph) (seed:seed_of_or2and_edge): bool =
  let
    val subgoals   = #new_goals seed |> map snd: terms;
    val no_subgoal = null subgoals: bool;
  in
    no_subgoal orelse exists (condition_to_filter_out_cnjctr parent_or refutation pst ag true) subgoals 
  end;

fun filter_out_bad_seeds_from_tactic (parent_or:term) (refutation:SS.synched_term2bool_table) (pst:Proof.state) (graph:abduction_graph) (seeds:seeds_of_or2and_edge) =
  filter_out (condition_to_filter_out_seed_from_tactic parent_or refutation pst graph) seeds: seeds_of_or2and_edge;

fun conjecture_to_seed_of_or2and_edge (cnjctrs:(string * term) list): seed_of_or2and_edge =
  {new_goals = cnjctrs: (string * term) list,
   proof     = Or2And_Edge.Conjecture: how_to_get_andnodes_from_ornode};

fun conjectures_to_seed_of_or2and_edge (term2name:SS.synched_term2string_table) (pst:Proof.state) (cnjctrs_w_name: (string * term) list) =
  let
    fun get_ctxt_w_proof_goal trm = Proof.context_of (mk_pst_to_prove_from_term pst trm)        : Proof.context;
    fun mk_prop term = if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term    : term;
    fun check_prop (trm:term)     = try (Syntax.check_prop (get_ctxt_w_proof_goal trm)) trm     : term option;
    val cnjctrs                   = map snd cnjctrs_w_name                                      : terms;
    val cnjctrs_as_props          = map mk_prop cnjctrs                                         : terms;
    val checked_cnjctrs           = List.mapPartial check_prop cnjctrs_as_props                 : terms;
(*
val _ = tracing "++ 2: conjectures_to_seed_of_or2and_edge ++"
val _ = checked_cnjctrs |> map (tracing o Isabelle_Utils.trm_to_string (Proof.context_of pst));
*)
    val ctxt                      = Proof.context_of pst                                                                : Proof.context;
    val name_cnjctr_pairs         = map (fn cnjctr => (SS.get_lemma_name term2name ctxt cnjctr, cnjctr)) checked_cnjctrs: (string * term) list;
    val result                    = conjecture_to_seed_of_or2and_edge name_cnjctr_pairs                                 : seed_of_or2and_edge;

  in
    result: seed_of_or2and_edge
  end;

fun seed_has_counterexample (refutation:SS.synched_term2bool_table) (pst:Proof.state) ({new_goals,...}:seed_of_or2and_edge) =
  let
    val conjectures = map snd new_goals;
  in
    SS.any_of_these_is_refuted refutation pst conjectures
  end;

(*
 * 0. We have an or-node to expand.
 * 1. add an or2and-edge.
 * 2. connect the or2and-edge to its parental or-node.
 * 3. prove the parental or-node using the sub-goals or some conjectures.
 *)
fun add_or2and_edge_and_connect_it_to_parental_ornode
     (pst:Proof.state)
     (parent_orkey as (Or_N, [orterm]): key)(*parent node*)
     ({new_goals: (string * term) list, proof: how_to_get_andnodes_from_ornode}: seed_of_or2and_edge)(*child nodes*)
     (synched_agraph:SS.synched_abduction_graph): (key option * (string * term) list) =
   let
     fun tracing' mssg = ();
     val _ = tracing' "\n--------- Try to prove this:";
     val _ = tracing' "--------- assuming these:";
     val _ = map (tracing' o (Isabelle_Utils.trm_to_string (Proof.context_of pst)) o snd) new_goals;
     val _ = if Or2And_Edge.proof_is_from_tactic proof 
             then tracing' ("--------- because they are the result of applying this induction: " ^ space_implode " " (Or2And_Edge.how_to_get_andnodes_from_ornode_of proof))
             else tracing'  "--------- because they are the result of explicit conjecturing";

     fun cnjctr_to_thm (ctxt:Proof.context) (cnjctr:term) =
       let
         val prop       = if Top_Down_Util.is_prop cnjctr then cnjctr else HOLogic.mk_Trueprop cnjctr;
         val fvar_names = Isabelle_Utils.get_free_var_names_in_trm prop |> distinct (op =): strings;
         val thm        = Goal.prove ctxt fvar_names [] cnjctr (fn _ => ALLGOALS (Skip_Proof.cheat_tac ctxt)): thm;
       in
         thm
       end;

     fun register_proved_thm_in_lthy (name:string) (thm:thm) (lthy:local_theory): local_theory =
       Local_Theory.note ((Binding.name name, []), [thm]) lthy |> snd: local_theory;

     fun assm_cnjctr_in_pst (name:string, cnjctr:term) (pst:Proof.state) =
       let
         val ctxt          = Proof.context_of pst                                                  : Proof.context;
         val cnjctr_as_thm = cnjctr_to_thm ctxt cnjctr                                             : thm;
         val pst_w_cnjctr_opt = try (Proof.map_context (register_proved_thm_in_lthy name cnjctr_as_thm)) pst: Proof.state option;
         val pst_w_cnjctr     = case pst_w_cnjctr_opt of SOME no_dup_pst => no_dup_pst | _ => pst
       in
         pst_w_cnjctr
       end;

     val pst_with_new_goals_assmed = fold assm_cnjctr_in_pst new_goals pst                     : Proof.state;
     val pst_to_apply_tactics      = mk_pst_to_prove_from_term pst_with_new_goals_assmed orterm: Proof.state;

     (*apply_proof considers the first result only.*)
     fun apply_proof (proof:string) (pst_tobe_proved:Proof.state) =
     let
       val sh_result = Subtools.tool_output_n_timeout_to_logtac proof 5.0 pst_tobe_proved;
       val result_pst = Seq.pull sh_result <$> fst <$>  snd |> the: Proof.state;
     in
       result_pst
     end;

     fun apply_proofs (proofs:strings) (pst_tobe_proved:Proof.state) = fold apply_proof proofs pst_tobe_proved: Proof.state;

     val proof_to_get_here = Or2And_Edge.how_to_get_andnodes_from_ornode_of proof: strings;
     val pst_after_applying_how_to_get_andnodes_from_ornode = apply_proofs proof_to_get_here pst_to_apply_tactics: Proof.state;

     val timeouts             = {overall = 30.0, hammer = 10.0, quickcheck = 1.0, nitpick = 2.0}: TBC_Utils.timeouts;
     (*very expensive*)
     val script_opt_gen       = TBC_Utils.pst_to_proofscript_opt timeouts "Finish_Goal_After_Assuming_Subgoals_And_Conjectures" pst_after_applying_how_to_get_andnodes_from_ornode
                            <$> fst: string option;
     val proved_parent_or     = is_some script_opt_gen: bool;
   in
     if proved_parent_or
     then
       let
         val how_we_got_andnode    = Or2And_Edge.how_to_get_andnodes_from_ornode_of proof                        : strings;
         val script_to_prove_andnd = the script_opt_gen                                                          : string;

         val _ = tracing' "\nscript_to_prove_andnd"
         val _ = tracing' script_to_prove_andnd
         val _ = tracing' "how_to_get_andnodes_from_ornode"
         val _ = map tracing' (Or2And_Edge.how_to_get_andnodes_from_ornode_of proof)

         val script_to_prove_ornd  = how_we_got_andnode @ single script_to_prove_andnd                           : strings;
         val or2and_edge_val       = Abduction_Node.Or_To_And {
                                      how_to_get_andnodes_from_ornode = proof,
                                      proof_of_ornode_assmng_andnodes = script_to_prove_ornd}                    : abduction_node;
         val or2and_edge_key      = ((O2A_E (serial())), [])                                                     : key;
         val thy                  = Proof.theory_of pst                                                          : theory;
         val used_cnjctr_names    = Top_Down_Util.get_lemma_names_from_sh_output thy script_to_prove_andnd       : strings;
         val used_new_goals       = filter (fn (name, _) => member (op =) used_cnjctr_names name) new_goals      : (string * term) list;

         val _ = tracing' "\n used_new_goals"
         val _ = map (tracing' o Isabelle_Utils.trm_to_string (Proof.context_of pst) o snd) used_new_goals;

         val relevant_new_goals   = if   Or2And_Edge.proof_is_from_tactic proof (*if this is the result of tactic application*)
                                    then (tracing' "\nDDD Relevant_new_golas are new_goals because from tactics"; new_goals)
                                    else (tracing' "\nDDD Relevant_new_golas are used_new_goals because from explict conjecturing"; used_new_goals);

         val _ = tracing' "\n relevant_new_goals are:"
         val _ = map (tracing' o fst) relevant_new_goals;
         val _ = map (tracing' o Isabelle_Utils.trm_to_string (Proof.context_of pst) o snd) relevant_new_goals;
         (* updating abduction_graph *)
         val _ = SS.new_node (or2and_edge_key, or2and_edge_val) synched_agraph: unit;
         val _ = SS.add_edge (parent_orkey, or2and_edge_key) synched_agraph: unit;
       in
         (SOME or2and_edge_key, relevant_new_goals)
       end
     else (NONE, [])
   end
 | add_or2and_edge_and_connect_it_to_parental_ornode _ _ _ _ = error "how_to_prove_ornode_assmng_subgs_of_andnode failed.";

(*
 * step 0. We have an or-node to expand.
 * step 1. add an or2and-edge.
 * step 2. connect the or2and-edge to its parental or-node.
 * step 3. prove the parental or-node using some conjectures.
 * step 4. add an and-node that consists of used conjectures.
 * step 5. connect the and-node to its parental or2and-edge.
 * step 6. add child-or-nodes that correspond to the sub-goals or used conjectures in the and-node.
 * step 7. connect the child-or-nodes to the and-node.
 *)
fun one_step (pst:Proof.state) (parent_ornd:key) (synched_agraph:SS.synched_abduction_graph) (seed: seed_of_or2and_edge): (string * term) list =
  let
    fun tracing' mssg = ();
    val _ = SS.update_is_branch parent_ornd synched_agraph: unit;
    (*add an or2and_ege and connect them to their parental or-node if we can prove the or-node assuming the and-node.*)
    (*step 1, step 2, step 3*)
    val (or2and_edge_opt,
         used_andnd_name_term_pairs) =
         add_or2and_edge_and_connect_it_to_parental_ornode pst parent_ornd seed synched_agraph;
    val parent_ornd_is_proved_assmng_seed   = is_some or2and_edge_opt: bool;
  in
    if   parent_ornd_is_proved_assmng_seed
    then
      let
        val and_node_terms = map snd used_andnd_name_term_pairs: terms;
        (*length added_andnode_keys should be 1.*)
        (*step 4*)
        val added_andnode_keys = SS.add_andnodes and_node_terms synched_agraph                                       : keys;
        val _                  = if length added_andnode_keys = 1 then () else error "length added_andnode_keys != 1"
        val or2and_edge_key    = the or2and_edge_opt                                                                 : key;
        val added_andnode_key  = hd added_andnode_keys                                                               : key;
        (*step 5*)
        val _                  = SS.add_edge (or2and_edge_key, added_andnode_key) synched_agraph                     : unit;
        (*step 6*)
        val ctxt               = Proof.context_of pst;
        val add_child_ornode   = SS.add_child_ornode ctxt synched_agraph                                             : string * term -> unit;
        val _                  = map add_child_ornode used_andnd_name_term_pairs                                     : unit list;
        (*step 7*)
        val _                  = SS.add_edges_from_andnode_to_ornodes added_andnode_key synched_agraph                 : unit;
        val connected_orkeys   = map (fn or_term => (Or_N, [or_term])) and_node_terms                                  : keys;
        val _                  = SS.update_after_connecting_andnd_to_existing_ornd ctxt synched_agraph connected_orkeys: unit list;
        val _ = tracing' ("=== Used cnjctrs are: ")
        val _ = map tracing' (map (fn (str, trm) => str ^ " | " ^ Isabelle_Utils.trm_to_string (Proof.context_of pst) trm) used_andnd_name_term_pairs)
      in
        used_andnd_name_term_pairs
      end
    else
      ([])
  end;

(*implicit conjecturing*)
fun seeds_to_updated_graph (pst:Proof.state) (parent_ornd:key) (seeds: seeds_of_or2and_edge) (sagraph:SS.synched_abduction_graph) =
  let
    val _ = map (one_step pst parent_ornd sagraph) seeds;
  in () end;

type cnjctrs = (string * term) list;

fun eq_cnjctrs (pairs1:cnjctrs, pairs2:cnjctrs): bool =
  let
    val goal_names1 = map fst pairs1;
    val goal_names2 = map fst pairs2;
  in
    eq_set (op =) (goal_names1, goal_names2)
  end;

(*explicit conjecturing*)
fun decremental  _            (pst:Proof.state) (_          :key) ([]            :cnjctrs list)    (_      :cnjctrs list) (_             :SS.synched_abduction_graph)  _                        = ()
  | decremental (counter:int) (pst:Proof.state) (parent_ornd:key) (cnjctrs::cnjctrss:cnjctrs list) (checked:cnjctrs list) (synched_agraph:SS.synched_abduction_graph) (failed_set:cnjctrs list) =
    if counter > 0
    then
      let
        (*1  apply one_step. identify used conjectures.*)
        val seed                       = conjecture_to_seed_of_or2and_edge cnjctrs                                     : seed_of_or2and_edge;
        val used_andnd_name_term_pairs = one_step pst parent_ornd synched_agraph seed                                  : cnjctrs;

        (*2 identify used conjectures that are not proved.*)
        val abduction_graph            = Synchronized.value synched_agraph                                             : SS.abduction_graph;(*TODO: maybe we should avoid this?*)
        fun is_completely_proved (_, term) = is_proved_completely abduction_graph (Or_N, [term])                       : bool;
        val unproved_used_andnd_name_term_pairs = filter_out is_completely_proved used_andnd_name_term_pairs           : cnjctrs;


        val (new_failed_set, new_candidates): (cnjctrs list * cnjctrs list) =
          (if null used_andnd_name_term_pairs
           then
            (*3. register the conjectures inside seed as a set of failed attempt.*)
             let
               val new_failed_set = distinct eq_cnjctrs (cnjctrs::failed_set)
             in
               (new_failed_set, cnjctrss)
             end
           else
            (*4 make sets of conjectures from seeds, so that each member of the set lacks exactly one conjecture that was used but not proved.*)
             let
               val mk_new_cnjctr_set_by_removing_one_of = map (remove (op =)) unproved_used_andnd_name_term_pairs: (cnjctrs -> cnjctrs) list;
               fun mk_new_goals_wo_one_used_goal (those_sent_to_one_step:cnjctrs) =
                   Utils.map_arg those_sent_to_one_step mk_new_cnjctr_set_by_removing_one_of: cnjctrs list;
               (*fun mk_new_goals_wo_used_proved_goals (cnjncts) = subtract (fn (p1,p2) => fst p1 = fst p2) unproved_used_andnd_name_term_pairs cnjncts: cnjctrs;*)
               val new_cnjctrss = map mk_new_goals_wo_one_used_goal (cnjctrs::cnjctrss)
                               |> flat
                               |> distinct eq_cnjctrs
                               |> distinct eq_cnjctrs
                               |> sort length_ord |> rev; (*We want to check seeds with more conjectures first because they tend to be more powerful.*)
             in
               (failed_set, new_cnjctrss)
             end
          );
        val newly_checked = cnjctrs :: checked: cnjctrs list;
        fun eq_to_one_of_checked (cnjctrs:cnjctrs) = exists (curry eq_cnjctrs cnjctrs) newly_checked: bool;
        val genuinely_new_candidates = filter_out eq_to_one_of_checked new_candidates: cnjctrs list;
        fun is_subset_of (sub:cnjctrs) (sup:cnjctrs) = subset (op =) (sub, sup);
        fun is_subset_of_any_failed_cnjctrs (sub:cnjctrs) = exists (is_subset_of sub) new_failed_set;
        val promising_candidates = filter_out is_subset_of_any_failed_cnjctrs genuinely_new_candidates;
      in
        decremental (counter - 1) pst parent_ornd promising_candidates newly_checked synched_agraph new_failed_set
      end
    else ();

fun decremental_abduction (pst:Proof.state) (parent_ornd:key) (seed:seed_of_or2and_edge)
  (term2name:SS.synched_term2string_table) (synched_agraph: SS.synched_abduction_graph) =
  let
    fun tracing' mssg = ();
    val _ = tracing "\n ** Trying to prove **:";
    val _ = tracing (SS.get_orkey_name term2name (Proof.context_of pst) parent_ornd);
    val _ = Abduction_Graph.print_key (Proof.context_of pst) parent_ornd;
    val _ = tracing " decremental abduction starts";
    val _ = map snd (#new_goals seed) |> map (tracing' o Isabelle_Utils.trm_to_string (Proof.context_of pst));
    val max_number = if (Abduction_Graph.is_final_goal (Synchronized.value synched_agraph) parent_ornd) then 5 else 1;
    val _ = decremental max_number pst parent_ornd [#new_goals seed] [] synched_agraph []: unit;
    val _ = tracing " decremental abduction ends";
  in
    ()
  end;

end;