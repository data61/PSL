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

(* decremental abduction*)
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
fun one_step (pst:Proof.state) (parent_ornd:key) (synched_agraph:SS.synched_abduction_graph) (seed: seed_of_or2and_edge): seeds_of_or2and_edge =
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
        (*=from here only for explicit conjecturing not for implicit conjecturing=*)
        val mk_new_goals_wo_one_used_goal = map (remove (op =)) used_andnd_name_term_pairs: ((string * term) list -> (string * term) list) list;
        val old_goals                     = #new_goals seed                     : (string * term) list;
        val _ = tracing ("=== Inside one_step.");
        val _ = tracing ("=== The number of used conjectures are " ^ (Int.toString (length used_andnd_name_term_pairs)));
        val _ = tracing ("=== They are: ")
        val _ = map tracing (map (fn (str, trm) => str ^ " | " ^ Isabelle_Utils.trm_to_string (Proof.context_of pst) trm) used_andnd_name_term_pairs)
        val new_goals_wo_one_used_goal    = Utils.map_arg old_goals mk_new_goals_wo_one_used_goal
                                          |> distinct (op =)
                                          |> map (distinct (op =)): (string * term) list list;
        val new_seeds                     = map conjecture_to_seed_of_or2and_edge new_goals_wo_one_used_goal: seeds_of_or2and_edge;
        (*=till here only for explicit conjecturing not for implicit conjecturing=*)
      in
        new_seeds
      end
    else []
  end;

(*implicit conjecturing*)
fun seeds_to_updated_graph (pst:Proof.state) (parent_ornd:key) (seeds: seeds_of_or2and_edge) (sagraph:SS.synched_abduction_graph) =
  let
    val _ = map (one_step pst parent_ornd sagraph) seeds;
  in () end;

fun eq_seed_modulo_reordering (seed1:seed_of_or2and_edge, seed2:seed_of_or2and_edge) =
  let
    val new_goals1 = #new_goals seed1: (string * term) list;
    val new_goals2 = #new_goals seed2: (string * term) list;
    val goal_names1 = map fst new_goals1: strings;
    val goal_names2 = map fst new_goals2: strings;
  in
    eq_set (op =) (goal_names1, goal_names2)
  end;

(*explicit conjecturing*)
fun decremental (pst:Proof.state) (_          :key) ([]         :seeds_of_or2and_edge) (_            :seeds_of_or2and_edge) (_             :SS.synched_abduction_graph) = ()
  | decremental (pst:Proof.state) (parent_ornd:key) (seed::seeds:seeds_of_or2and_edge) (checked_seeds:seeds_of_or2and_edge) (synched_agraph:SS.synched_abduction_graph) =
    let
      val _ = tracing "\n====== inside decremental =="     
      val _ = tracing ("=== The number of seeds are: " ^ Int.toString (length (seed::seeds)))
      val _ = tracing "===  seed to judge is:"
      val _ = print_seed_of_or2and_edge @{context} seed

      val new_seeds       = one_step pst parent_ornd synched_agraph seed: seeds_of_or2and_edge;

      val _ = tracing ("=== The number of new seeds are: " ^ Int.toString (length new_seeds))
      val _ =  tracing "===  new seeds are:"
      val _ = map (fn seed => (print_seed_of_or2and_edge @{context} seed; tracing "-")) new_seeds

      (* I only compare the name of conjectures. It seems that in some cases we have similar conjectures of the same name.
       * This is probably caused by the inconsistent use of the conversion from term to prop. *)
      val unchecked_seeds = filter_out (fn new_seed => member eq_seed_modulo_reordering checked_seeds new_seed) new_seeds
      val distinct_seeds  = distinct eq_seed_modulo_reordering (unchecked_seeds @ seeds)

      val _ = tracing ("=== The number of distinct_seeds are: " ^ Int.toString (length distinct_seeds))
(*
      val _ =  tracing "--new distinct seeds are:"
      val _ = map (fn seed => (print_seed_of_or2and_edge @{context} seed; tracing "-")) distinct_seeds
*)
    in
      decremental pst parent_ornd (distinct_seeds) (seed :: checked_seeds) synched_agraph
    end;

fun decremental_abduction (pst:Proof.state) (parent_ornd:key) (seed:seed_of_or2and_edge)
  (term2name:SS.synched_term2string_table) (synched_agraph: SS.synched_abduction_graph) =
  let
    fun tracing' mssg = ();
    val _ = tracing "\n ** Trying to prove **:";
    val _ = tracing (SS.get_orkey_name term2name (Proof.context_of pst) parent_ornd);
    val _ = Abduction_Graph.print_key (Proof.context_of pst) parent_ornd;
    val _ = tracing " decremental abduction starts";
    val _ = map snd (#new_goals seed) |> map (tracing' o Isabelle_Utils.trm_to_string (Proof.context_of pst));
    val _ = decremental pst parent_ornd [seed] [] synched_agraph: unit;
    val _ = tracing " decremental abduction ends";
  in
    ()
  end;

end;