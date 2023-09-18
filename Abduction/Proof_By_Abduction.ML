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
    val filtered_explicit          = TDU.parallel_filter_out condition_to_filter_out explicit_conjectures               : (string * term) list;
    val refute                     = Shared_State.is_refuted refutation pst o snd                                       : (string * term) -> bool;
    val explicit_wo_counterexample = TDU.parallel_filter_out refute filtered_explicit                                   : (string * term) list;
    fun prove_save_in_graph (lem_name:string, lem_term:term) =
      let
        (*expensive*)
        val maybe_prf = prove_term_completely pst lem_term: strings option;
      in
        if is_none maybe_prf then ()
        else SS.add_proved_simp proved_ors (lem_name, lem_term)
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
          val explicit_conjectures       = All_Top_Down_Conjecturing.top_down_conjectures term2name pst lemma_term                   : (string * term) list;
          val condition_to_filter_out    = SOOE.condition_to_filter_out_conjecture lemma_term refutation pst graph false o snd       : string * term -> bool;
          val filtered_explicit          = TDU.parallel_filter_out condition_to_filter_out explicit_conjectures: (string * term) list: (string * term) list;
          val explicit_wo_counterexample = TDU.parallel_filter_out (Shared_State.is_refuted refutation pst o snd) filtered_explicit  : (string * term) list;
          val seed_from_explicit         = SOOE.conjectures_to_seed_of_or2and_edge term2name pst explicit_wo_counterexample          : seed_of_or2and_edge;
          val explicit_cnjnctrs          = #new_goals seed_from_explicit                                                             : SOOE.conjectures;
          val ctxt                       = Proof.context_of pst                                                                      : Proof.context;
          fun simp_explicit_conjecture (simp as (_:string, simp_term:term)) (cnjctr as (_:string, cnjctr_term:term)): SOOE.conjectures =
            let
              val simp_thm = TDU.term_to_thm ctxt simp_term: thm;
              val ctxt_w_simp = Simplifier.add_simp simp_thm ctxt: Proof.context;
              val simplifier = Basic_Simplifier.simplify ctxt_w_simp: thm -> thm;(*asm_full_simplify*)
              val simplifier_w_timeout = try (Isabelle_Utils.timeout_apply (Time.fromSeconds 1) simplifier): thm -> thm option;
              val cnjctr_thm = TDU.term_to_thm ctxt cnjctr_term: thm;
              val simped_cnjctr = simplifier_w_timeout cnjctr_thm: thm option;
              fun schematic_to_free (Var ((str, i), typ)) =(*TODO: Can I do something better than this?*)
                let
                  val vname = space_explode "." str |> hd
                in Free (vname, typ)
                end
                | schematic_to_free aterm = aterm;
              fun remove_schematic (term:term) = (map_aterms schematic_to_free term);
            in
              if   is_none simped_cnjctr
              then [cnjctr]
              else
                let
                  val rm_Trueprop = Top_Down_Util.remove_Trueprop o Isabelle_Utils.strip_atyp;
                  val simped_cnjctr_term = the simped_cnjctr |> Thm.full_prop_of
                     |> remove_schematic
                  val simped_cnjctr_name = SS.get_lemma_name term2name ctxt simped_cnjctr_term: string;
                  val size_of_simped_cnjctr = Term.size_of_term (rm_Trueprop simped_cnjctr_term): int;
                  val size_of_orig_cnjctr   = Term.size_of_term (rm_Trueprop cnjctr_term): int;
                in
                  if size_of_simped_cnjctr >= size_of_orig_cnjctr (*orelse simped_cnjctr_term = @{term True}*)
                     (*orelse rm_Trueprop simped_cnjctr_term = rm_Trueprop lemma_term*)
                  then [cnjctr]
                  else [simp, (simped_cnjctr_name, simped_cnjctr_term)](*TODO: not efficient.*)
                end
            end;
          fun simp_explicit_conjectures_for_one_rule (simp:SOOE.conjecture) (cnjctrs:SOOE.conjectures): SOOE.conjectures =
              map (simp_explicit_conjecture simp) cnjctrs |> flat |> distinct (op =);
          fun simp_explicit_conjectures_for_many_rules (cnjctrs:SOOE.conjectures) (simps:SOOE.conjectures)=
              fold simp_explicit_conjectures_for_one_rule simps cnjctrs: SOOE.conjectures;
          val simps                        = Synchronized.value proved_ors: SS.proved_simps;
          val simped_explicit_conjectures  = simp_explicit_conjectures_for_many_rules explicit_cnjnctrs simps                      : SOOE.conjectures;
          val _                            = SOOE.abduction_for_explicit_conjectures pst or_key simped_explicit_conjectures (term2name, synched_agraph) proved_ors: unit;
          (*tactic application as conjecturing. A little expensive*)
          val pst_to_prove                 = TDU.mk_pst_to_prove_from_term pst lemma_term                                          : state;
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
      val _                      = tracing ("==== In loop. The depth is: " ^ Int.toString counter ^ ". =====");
      val ctxt                   = Proof.context_of pst;
      val abduction_graph        = Synchronized.value synched_agraph: Abduction_Graph.abduction_graph;
      val orkeys_worth_expanding = orkeys_tobe_expanded_in ctxt abduction_graph: keys;
      val sorted_orkeys          = sort_orkeys_based_on_importance abduction_graph orkeys_worth_expanding: keys;
      val _                      = tracing ("The number of keys worth expanding is:" ^ Int.toString (length sorted_orkeys) ^ ".");
      val _                      = tracing "They are:"
      val _                      = map (print_key ctxt) sorted_orkeys
      val expand_ornode          = expand_ornode_if_original_goral_is_unproved_w_timeout start (pst, synched_agraph, refutation, term2name, proved_ors): Abduction_Graph.key -> bool;
      val top_ornodes            = take 15 sorted_orkeys: keys;(*TODO: magic number*)
      val some_orkey             = Par_List.find_some expand_ornode top_ornodes: key option;
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
    val ctxt                     = Proof.context_of pst;
    val standardized_term        = Top_Down_Util.standardize_vnames term |> Isabelle_Utils.strip_atyp |> Syntax.check_term ctxt;
    val synched_agraph           = SS.mk_synched_abduction_graph ctxt standardized_term: SS.synched_abduction_graph;
    val synched_refutation_table = SS.mk_term2bool_table ();
    val synched_lemma_name_table = SS.mk_term2string_table ();
    val synched_proved_simps     = SS.mk_synched_proved_simps ();
    val quadruple                = (pst, synched_agraph, synched_refutation_table, synched_lemma_name_table, synched_proved_simps);
    val _                        = prove_standard_simp_rules quadruple standardized_term: unit;
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