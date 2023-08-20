(*
 * Proof_By_Abduction.ML 
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** PROOF_BY_ABDUCTION ***)
signature PROOF_BY_ABDUCTION =
sig

val proof_by_abduction: Proof.state -> Timing.start -> term -> bool;

end;

(*** Proof_By_Abduction ***)
structure Proof_By_Abduction: PROOF_BY_ABDUCTION  =
struct

type state = Proof.state;

open Abduction_Graph;

structure SOOE = Seed_Of_Or2And_Edge;
structure SS   = Shared_State;
structure AG   = Abduction_Graph;
structure TDU  = Top_Down_Util;
structure ATDC = All_Top_Down_Conjecturing;

(** functions to expand ornode leaves **)

(* record_to_mk_andnode *)
type seed_of_or2and_edge  = SOOE.seed_of_or2and_edge;
type seeds_of_or2and_edge = SOOE.seeds_of_or2and_edge;

(* expand_ornode *)
fun prove_standard_simp_rules
  (pst:state,
   synched_agraph: SS.synched_abduction_graph,
   refutation    : SS.synched_term2bool_table,
   term2name     : SS.synched_term2string_table,
   proved_ors    : SS.synched_proved_simps)
  (lemma_term:term): unit =
    let
      (*top-down explicit conjecturing*)
      val ctxt = Proof.context_of pst: Proof.context;
      val graph                      = Synchronized.value synched_agraph                                                  : abduction_graph;
      val condition_to_filter_out    = SOOE.condition_to_filter_out_conjecture lemma_term refutation pst graph false o snd: string * term -> bool;
      val explicit_conjectures       = ATDC.template_based_conjecture_for_simplification term2name ctxt lemma_term        : (string * term) list;
      val filtered_explicit          = parallel_filter_out condition_to_filter_out explicit_conjectures                   : (string * term) list;
      val refute                     = Shared_State.is_refuted refutation pst o snd                                       : (string * term) -> bool;
      val explicit_wo_counterexample = parallel_filter_out refute filtered_explicit                                       : (string * term) list;

val _ = tracing "explicit_wo_counterexample are:"
val _ = map (tracing o Isabelle_Utils.trm_to_string (Proof.context_of pst) o snd) explicit_wo_counterexample: unit list;

      fun prove_save_in_graph (lem_name:string, lem_term:term) =
        let
          (*expensive*)
          val _ = tracing lem_name;
          val maybe_prf = prove_term_completely pst lem_term: strings option;
val _ = if is_some maybe_prf then (tracing o Isabelle_Utils.trm_to_string ctxt) lem_term else () 
        in
          if is_none maybe_prf then (tracing ("DID NOT PROVE: " ^ Isabelle_Utils.trm_to_string ctxt lem_term))
          else SS.add_proved_simp proved_ors (lem_name, lem_term)
               (*Synchronized.change proved_ors (fn alist => (lem_name, lem_term)::alist)*)
        end;

      val _ = Par_List.map prove_save_in_graph explicit_wo_counterexample: unit list;

    in
      ()
    end;

(* expand_ornode *)
fun expand_ornode_if_original_goral_is_unproved
  (pst:state,
   synched_agraph: SS.synched_abduction_graph,
   refutation    : SS.synched_term2bool_table,
   term2name     : SS.synched_term2string_table,
   proved_ors    : SS.synched_proved_simps)
  (or_key as (Or_N, [lemma_term]):key): bool =
    let
       (*very expensive*)
       val graph       = Synchronized.value synched_agraph      : abduction_graph;
       val maybe_proof = prove_orkey_completely or_key graph pst: strings option;
    in
      if is_some maybe_proof (*ornode was proved completely.*)
      then
        let
          val proof      = the maybe_proof: strings;
          val _          = SS.update_after_proving_ornode proof or_key (Proof.context_of pst) synched_agraph;
        in
           SS.final_goal_proved_completely synched_agraph
        end
      else (*if we cannot prove the ornode completely, expand it using Extend_Leaf and conjecturing*)
        let
          (*top-down explicit conjecturing*)
          val explicit_conjectures         = All_Top_Down_Conjecturing.top_down_conjectures term2name pst lemma_term               : (string * term) list;
          val condition_to_filter_out      = SOOE.condition_to_filter_out_conjecture lemma_term refutation pst graph false o snd   : string * term -> bool;
          val filtered_explicit            = parallel_filter_out condition_to_filter_out explicit_conjectures: (string * term) list: (string * term) list;
          val explicit_wo_counterexample   = parallel_filter_out (Shared_State.is_refuted refutation pst o snd) filtered_explicit  : (string * term) list;
          val seed_from_explicit           = SOOE.conjectures_to_seed_of_or2and_edge term2name pst explicit_wo_counterexample      : seed_of_or2and_edge;
          val explicit_cnjnctrs            = #new_goals seed_from_explicit                                                         : SOOE.conjectures;
          val _                            = SOOE.abduction_for_explicit_conjectures pst or_key explicit_cnjnctrs (term2name, synched_agraph) proved_ors: unit;
          (*tactic application as conjecturing. A little expensive*)
          val pst_to_prove                 = mk_pst_to_prove_from_term pst lemma_term                                              : state;
          val seeds_from_tactics           = SOOE.apply_PSL_to_get_seeds_of_or2and_edges term2name pst_to_prove                    : seeds_of_or2and_edge;
          val graph_extended_by_conjecture = Synchronized.value synched_agraph                                                     : abduction_graph;
          val filtered_seeds_from_tactics  = SOOE.filter_out_bad_seeds_from_tactic lemma_term refutation pst graph_extended_by_conjecture seeds_from_tactics
                                          |> filter_out (SOOE.seed_has_counterexample refutation pst)                              : seeds_of_or2and_edge;
          val _                            = SOOE.abduction_for_tactic_based_conjectures pst or_key filtered_seeds_from_tactics synched_agraph: unit;
        in
          (*seeds_to_updated_graph is very expensive*)
          SS.final_goal_proved_completely synched_agraph
        end
    end
  | expand_ornode_if_original_goral_is_unproved _ _ = error "expand_ornode failed. Not an Or_N.";

fun get_timeout (pst:Proof.state) = Config.get (Proof.context_of pst) Top_Down_Util.timeout_config: real;
fun current_time (start:Timing.start) = Time.toReal (#elapsed (Timing.result start)): real;
fun still_has_time (start:Timing.start) (pst:Proof.state) = current_time start < get_timeout pst: bool;

fun expand_ornode_if_original_goral_is_unproved_w_timeout (start:Timing.start)
      (pst:state, synched_agraph, refutation, term2name, proved_ors) (or_key as (Or_N, [_]):key): bool =
    if   Time.toReal (#elapsed (Timing.result start)) < get_timeout pst
    then expand_ornode_if_original_goral_is_unproved (pst, synched_agraph, refutation, term2name, proved_ors) or_key
    else false
| expand_ornode_if_original_goral_is_unproved_w_timeout _ _ _ = error "expand_ornode_if_original_goral_is_unproved_w_timeout failed.";

(* loop *)
fun loop (counter:int) (max_depth:int) (start:Timing.start)
    (pst:state,
     synched_agraph: SS.synched_abduction_graph,
     refutation:SS.synched_term2bool_table,
     term2name:SS.synched_term2string_table,
     proved_ors:SS.synched_proved_simps) =
    if counter < 8 andalso still_has_time start pst
    then
      let
        val _                      = tracing ("==== In loop. The depth is: " ^ Int.toString counter ^ " =====");
        val ctxt                   = Proof.context_of pst;
        val abduction_graph        = Synchronized.value synched_agraph: Abduction_Graph.abduction_graph;
        val orkeys_worth_expanding = orkeys_tobe_expanded_in ctxt abduction_graph: keys;
        val _                      = tracing ("The number of keys worth expanding is:" ^ Int.toString (length orkeys_worth_expanding));
        val _                      = tracing "They are:"
        val _                      = map (print_key ctxt) orkeys_worth_expanding
        val some_orkey             = Par_List.find_some (expand_ornode_if_original_goral_is_unproved_w_timeout start (pst, synched_agraph, refutation, term2name, proved_ors)) orkeys_worth_expanding: key option;
        val solved                 = is_some some_orkey: bool;
        val _                      = tracing ("We have " ^ (if solved then "already solved" else "not solve") ^ " the final goal.");
      in
        (if solved then solved else loop (counter + 1) max_depth start (pst, synched_agraph, refutation, term2name, proved_ors))
      end
    else
      false;

type string2term_table = term Symtab.table;

fun insert_into_string2term (name:string, term:term) (string2term:string2term_table): string2term_table =
  Symtab.insert (op =) (name, term) string2term handle Symtab.DUP _ => string2term;

fun abduction_graph_to_string2term_table (ag:abduction_graph): string2term_table =
  let
    val or_keys     = keys ag |> filter is_ornode: keys;
    fun key_to_pair (key as (Or_N, [term])) = (lemma_name_of ag key, term)
      | key_to_pair _                       = error "abduction_graph_to_string2term_table failed.";
    val pairs       = map key_to_pair or_keys: (string * term) list;
    val string2term = fold insert_into_string2term pairs Symtab.empty: string2term_table;
  in
    string2term
  end;

(*rose tree to print proofs*)
datatype print_proof_tree = PPTree of (string * print_proof_tree list);

fun get_print_proof_tree (pst:Proof.state) (ag:abduction_graph) (name2term:string2term_table) (lemma_name:string) =
    let
      val lemma_term_opt = Symtab.lookup name2term lemma_name: term option;
    in
      if is_none lemma_term_opt
      then
        PPTree (lemma_name, []) (*The lemma was proved before calling our tool.*)
      else
        let
          val lemma_term       = the lemma_term_opt;
          val orkey            = (Or_N, [lemma_term]): Abduction_Graph.key;
          val proof            = Abduction_Graph.proof_of ag orkey |> String.concatWith " ": string;
          val thy              = Proof.theory_of pst: theory;
          val used_lemma_names = Top_Down_Util.get_lemma_names_from_sh_output thy proof: strings;
          val result           = PPTree (lemma_name, map (get_print_proof_tree pst ag name2term) used_lemma_names)
        in
          result
        end
    end;

fun order_pptree' (PPTree (lem_name, []  )) = [lem_name]: strings
  | order_pptree' (PPTree (lem_name, kids)) = flat (map order_pptree' kids) @ [lem_name];

(*note that "distinct" preserves the order*)
fun order_pptree (pptree:print_proof_tree) = order_pptree' pptree |> distinct (op =);

fun print_necessary_proofs_only (pst:Proof.state) (ag:abduction_graph) (name2term:string2term_table) (goal_name:string) =
let
  val pptree      = get_print_proof_tree pst ag name2term goal_name: print_proof_tree;
  val lemma_names = order_pptree pptree: strings;
  val lemma_terms = map (Symtab.lookup name2term) lemma_names |> Utils.somes: terms;
  val orkeys      = map (fn trm => (Or_N, [trm])) lemma_terms: keys;
  val ctxt        = Proof.context_of pst: Proof.context;
  val proofs      = "\n" :: map (print_lemma_and_proof_of_key ctxt ag) orkeys |> String.concatWith "\n";
  val whole_proof = Active.sendback_markup_properties [Markup.padding_command] proofs;
  val _           = tracing whole_proof;
in
  whole_proof
end;

(* proof_by_abduction *)
fun proof_by_abduction (pst:Proof.state) (start:Timing.start) (term:term) =
    let
      val max_depth                = 5;
      val standardized_term        = Top_Down_Util.standardize_vnames term;
      val ctxt                     = Proof.context_of pst;
      val synched_agraph           = SS.mk_synched_abduction_graph ctxt standardized_term: SS.synched_abduction_graph;
      val synched_refutation_table = SS.mk_term2bool_table ();
      val synched_lemma_name_table = SS.mk_term2string_table ();
      val synched_proved_simps     = SS.mk_synched_proved_simps ();
      val quadruple                = (pst, synched_agraph, synched_refutation_table, synched_lemma_name_table, synched_proved_simps);
      val _                        = prove_standard_simp_rules quadruple standardized_term: unit;
val _ = tracing "--- the  number of elems in the association list is: "
val _ = Synchronized.value synched_proved_simps |> length |> Int.toString |> tracing;
      val solved                   = loop 0 max_depth start quadruple;
      val final_graph              = Synchronized.value synched_agraph: Abduction_Graph.abduction_graph;
      val lemma_name2term          = abduction_graph_to_string2term_table final_graph: string2term_table;
      val final_goal_name          = lemma_name_of final_graph (Or_N, [standardized_term]): string;
      val _                        = if   solved
                                     then print_necessary_proofs_only pst final_graph lemma_name2term final_goal_name
                                     else ""
    in
      solved
    end;

end;
(*TODO: I should apply simplification using proved lemmas here not in top_down_conjectures.*)
(*
    val agraph = Synchronized.value synched_agraph;
    val ctxt = Proof.context_of pst
    fun is_already_in_graph (simplified:term) =
        let
          val orkey          = (Abduction_Graph.Or_N, [simplified]): AG.key;
          val already_exists = try (Abduction_Graph.PGraph.get_node agraph) orkey |> is_some;
          val is_True        = simplified = @{term True};
          val _ = if already_exists then tracing ("already_exists: " ^ Isabelle_Utils.trm_to_string ctxt simplified) else ();
        in
          already_exists orelse is_True
        end: bool;
    val keys   = AG.keys agraph: AG.keys;
    val orkeys = filter AG.is_ornode keys: AG.keys;
    val completely_proved_orkeys = filter (AG.is_proved_completely agraph) orkeys: AG.keys;
    val completely_proved_terms:terms = map AG.orkey_to_term completely_proved_orkeys: terms;
    val completely_proved_lemmas:thms = map (TDU.term_to_thm ctxt) completely_proved_terms: thms;
    fun mk_simplifier (added:thm) (tobe_simplified:thm) = (added, Basic_Simplifier.asm_full_simplify (Simplifier.add_simp added ctxt) tobe_simplified): (thm * thm);
    val simplifiers = map (mk_simplifier) completely_proved_lemmas: (thm -> (thm *thm)) list;
    fun simplify_conjecture_using_proved_lemma (conjecture:term) =
        let
val _ = tracing "Conjecture is:"
val _ = tracing (Isabelle_Utils.trm_to_string ctxt conjecture);
          val conjecture_as_thm  = TDU.term_to_thm ctxt conjecture;
          val thm_pairs      = Utils.map_arg conjecture_as_thm simplifiers: (thm * thm) list;(*(used_proved_lemma * simplified_result) list*)
          val term_pairs     = map (apply2 Thm.full_prop_of) thm_pairs: (term * term) list;
val _ = tracing ("The length of term_pairs is: " ^ Int.toString (length term_pairs))
val _ = tracing "They are:"
val _ = map (fn (_, trm) => tracing (Isabelle_Utils.trm_to_string ctxt trm)) term_pairs
(*We only care if we can simplify the conjecture using already proved lemmas.*)
          val filtered       = filter_out (fn (_, simplified:term) => conjecture = simplified) term_pairs: (term * term) list;
val _ = tracing ("The length of filtered is: " ^ Int.toString (length filtered))
          val used_lemmas    = map fst filtered: terms;
          val distinct_pairs = distinct (op =) filtered: (term * term) list;
        in
          distinct_pairs (*already completely proved lemmas that are used to reduce the conjecture to an or-term in the abduction graph.*) 
        end;

    fun replace_conjecture_if_we_can_simplify_it_to_term_in_graph (string:string, conjecture:term) =
        let
          val used_and_existing_lemma_pairs = simplify_conjecture_using_proved_lemma conjecture;
          val used_and_existing_lemmas = map Utils.pair_to_list used_and_existing_lemma_pairs |> flat |> distinct (op =): terms;
          val result_terms = if null used_and_existing_lemmas then [conjecture] else used_and_existing_lemmas;
val _ = if null used_and_existing_lemmas then () else tracing "NOT NULL";
          val w_string     = map (pair string) result_terms: (string * term) list;
        in
          w_string: (string * term) list
        end;

          val explicit_wo_counterexample = explicit_wo_counterexample |> Par_List.map replace_conjecture_if_we_can_simplify_it_to_term_in_graph |> flat |> distinct (op =)
*)