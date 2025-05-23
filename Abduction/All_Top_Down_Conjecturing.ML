(*
 * Top_Down_Conjecturing.ML
 *
 * Authors:
 *   Yutaka Nagashima, Daniel Goc Sebastian
 *   Huawei Technologies Research & Development (UK) Limited.
 *)
(*** structure All_Top_Down_Conjecturing ***)
structure All_Top_Down_Conjecturing(*: TOP_DOWN_CONJECTURING*) =
struct

structure IU  = Isabelle_Utils;
structure TDU = Top_Down_Util;

fun is_composite trm = IU.is_Abs trm orelse IU.is_App trm: bool;

fun has_no_multiple_occ_of_composite_subtrm (ctxt:Proof.context) (trm:term) =
let
  val p2u_table = Inner_Path_To_Unode.pst_n_trm_to_path_to_unode_table (Proof.init ctxt) trm: Inner_Path_To_Unode.path_to_unode_table;
  val p2p_table = Print_To_Inner_Paths.path_to_unode_table_to_print_to_paths_table p2u_table: Print_To_Inner_Paths.print_to_paths_table;
  val prints = Print_To_Inner_Paths.print_to_paths_table_to_prints p2p_table: strings;
  fun print_has_multiple_paths (print:string) =
    let
      val paths = Print_Table.lookup_list p2p_table print;
      val has_multi = not (length paths = 1): bool;
    in
      has_multi
    end;
  val duplicated_prints     = filter print_has_multiple_paths prints: strings;
  fun checker printed_term  = IU.read_term_then_check_term ctxt printed_term is_composite: bool;
  val duplicated_composites = filter checker duplicated_prints: strings;
  val has_dupulicates       = null duplicated_composites: bool;
in
  has_dupulicates: bool
end;

fun template_conjectures (ctxt:Proof.context) (trm:term): (string * term) list =
  let
    val (_, relevant_binary_funcs, relevant_unary_funcs) = TBC_Utils.get_relevant_constants ctxt trm;
    fun ctxt_n_const_to_all_conjecture_term context tm =
        Template_Based_Conjecturing.ctxt_n_const_to_all_conjecture_term context tm
     |> map (apfst Template_Based_Conjecturing.property_as_string);
    val result = map (ctxt_n_const_to_all_conjecture_term ctxt) (relevant_unary_funcs @ relevant_binary_funcs) |> flat
      : (string * term) list;
  in
    result
  end;

structure S4TD = SeLFiE_For_Top_Down;
structure SS   = Shared_State;
structure AG   = Abduction_Graph;
structure TBC  = Template_Based_Conjecturing;

fun template_based_conjecture_for_simplification term2name (ctxt:Proof.context) (trm): (string * term) list =
  let
    val (_, relevant_binary_funcs, relevant_unary_funcs) = TBC_Utils.get_relevant_constants ctxt trm;
    fun ctxt_n_const_to_all_conjecture_term context tm =
         (TBC.ctxt_n_const_to_identity     ctxt tm
        @ TBC.ctxt_n_const_to_idempotence  ctxt tm
        @ TBC.ctxt_n_const_to_zero_element ctxt tm
        @ TBC.ctxt_n_consts_to_idempotence ctxt tm
        @ TBC.ctxt_n_consts_to_involution  ctxt tm)
       |> map (apfst Template_Based_Conjecturing.property_as_string)
       |> map (fn (lemma_typ, term) => (SS.get_lemma_name term2name ctxt lemma_typ term, term));;
    val result = map (ctxt_n_const_to_all_conjecture_term ctxt) (relevant_unary_funcs @ relevant_binary_funcs)
              |> flat: (string * term) list;
  in
    result
  end;

fun top_down_conjectures (term2name: SS.synched_term2string_table) (pst:Proof.state) (trm:term) =
  let
    val ctxt = Proof.context_of pst: Proof.context;
    fun tracing' mssg = ();
    val _ = tracing' "[[[[[[[[[[[top_down_conjecture starts]]]]]]]]]]": unit;
    val standardized_trm = TDU.standardize_vnames trm
    val results = (
      (*It is important to have template_conjectures as the first because
       * - we remove duplication based on the term.
       * - we do not apply simplification for the conjectures produced by template-based conjecturing.*)
      template_conjectures ctxt standardized_trm)
    @ Remove_Outermost_Assumption.top_down_conjectures term2name pst standardized_trm
    @ Generalise_By_Renaming.top_down_conjectures term2name pst standardized_trm
    @ (Generalise_Then_Extend.top_down_conjectures term2name pst standardized_trm |> filter (fn (_, trm) => has_no_multiple_occ_of_composite_subtrm ctxt trm))
    @ Remove_Function.top_down_conjectures term2name pst standardized_trm
    @ Abstract_Same_Term.top_down_conjectures term2name pst standardized_trm
    @ Replace_Imp_With_Eq.top_down_conjectures term2name pst standardized_trm
      |> Par_List.map (apsnd (TDU.simp_non_prop_term ctxt))
      |> Par_List.map (apsnd TDU.standardize_vnames)
      |> map (fn (name, term) => (name, Syntax.check_term ctxt term))(*necessary to apply TDU.is_prop in some cases*)
      |> map (fn (name, term) => (name, if TDU.is_prop term then term else HOLogic.mk_Trueprop term))
      |> distinct (fn (f, s) => snd f = snd s)
    (*|> parallel_filter_out (fn (_, trm) => eq_over_same_func ctxt trm)*)
      |> TDU.parallel_filter_out (fn (_, cnjctr_trm) => cnjctr_trm = trm)
      |> TDU.parallel_filter_out (fn (_, trm) => S4TD.run_assertion pst trm S4TD.has_func_with_three_occs_in_a_row)
      |> TDU.parallel_filter     (fn (_, trm) => S4TD.run_assertion pst trm S4TD.fvars_in_prem_should_appear_in_concl)
      |> TDU.parallel_filter     (fn (_, trm) => S4TD.run_assertion pst trm S4TD.does_not_have_trivial_equality)
      |> TDU.parallel_filter_out (fn (_, trm) => S4TD.run_assertion pst trm S4TD.nested_eq)
      |> TDU.parallel_filter_out (fn (_, trm) => S4TD.run_assertion pst trm S4TD.var_appears_many_times_but_always_in_the_same_subtrm)
      |> map (fn (lemma_typ:string, term) => (SS.get_lemma_name term2name ctxt lemma_typ term, term));
    val _ = tracing' "[[[[[[[[[[[top_down_conjecture ends]]]]]]]]]]": unit;
  in
    results
  end;

end;