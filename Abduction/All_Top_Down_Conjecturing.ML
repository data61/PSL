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

fun is_composite trm = Isabelle_Utils.is_Abs trm orelse Isabelle_Utils.is_App trm: bool;

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
  fun checker printed_term  = Isabelle_Utils.read_term_then_check_term ctxt printed_term is_composite: bool;
  val duplicated_composites = filter checker duplicated_prints: strings;
  val has_dupulicates       = null duplicated_composites: bool;
in
  has_dupulicates: bool
end;

(* Prod31 for example needs this congruence(?).
fun eq_over_same_func (ctxt:Proof.context) (trm:term) =
  let
    val trm_wo_Trueprop = Isabelle_Utils.remove_Trueprop trm;
    val trm_w_prnt  = Unique_Node.trm_to_trm_w_prnt ctxt trm_wo_Trueprop;
    val utrm_w_prnt = Unique_Node.trm_w_prnt_to_utrm_w_prnt trm_w_prnt;
    val result = case utrm_w_prnt of
        Unique_Node.UA_Prnt (Unique_Node.UC_Prnt ("HOL.eq", _, "HOL.eq"),
          [Unique_Node.UA_Prnt (func1, _, _),
           Unique_Node.UA_Prnt (func2, _, _)], _) => func1 = func2
      | _ => false
  in
    result
  end;
*)


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
        @ TBC.ctxt_n_consts_to_projection  ctxt tm
        @ TBC.ctxt_n_consts_to_square      ctxt tm)
       |> map (apfst Template_Based_Conjecturing.property_as_string)
       |> map (fn (_,    term) => (SS.get_lemma_name term2name ctxt term, term));;
    val result = map (ctxt_n_const_to_all_conjecture_term ctxt) (relevant_unary_funcs @ relevant_binary_funcs) |> flat
      : (string * term) list;
  in
    result
  end;
(*
   (TBC.ctxt_n_const_to_identity     ctxt func
  @ TBC.ctxt_n_const_to_idempotence  ctxt func
  @ TBC.ctxt_n_const_to_zero_element ctxt func
  @ TBC.ctxt_n_consts_to_projection  ctxt func
  @ TBC.ctxt_n_consts_to_square      ctxt func)
 |> map (apfst Template_Based_Conjecturing.property_as_string)
| template_based_conjecture_for_simplification _ _ = [];
*)

fun top_down_conjectures (term2name: SS.synched_term2string_table) (pst:Proof.state) (trm:term) =
  let
    val ctxt = Proof.context_of pst: Proof.context;
    fun tracing' mssg = ();
    val _ = tracing' "[[[[[[[[[[[top_down_conjecture starts]]]]]]]]]]": unit;
    val standardized_trm = Top_Down_Util.standardize_vnames trm
    val results = (
      Remove_Outermost_Assumption.top_down_conjectures term2name pst standardized_trm
    (*@ Generalise_By_Renaming.top_down_conjectures pst standardized_trm*)
    @ (Generalise_Then_Extend.top_down_conjectures term2name pst standardized_trm
    |> filter (fn (_, trm) => has_no_multiple_occ_of_composite_subtrm ctxt trm))
    @ Remove_Function.top_down_conjectures term2name pst standardized_trm
    @ Abstract_Same_Term.top_down_conjectures term2name pst standardized_trm
    @ Replace_Imp_With_Eq.top_down_conjectures term2name pst standardized_trm
    @ template_conjectures ctxt standardized_trm)
      |> Par_List.map (apsnd (simp_non_prop_term ctxt))
      |> Par_List.map (apsnd Top_Down_Util.standardize_vnames)
      |> map (fn (name, term) => (name, if Top_Down_Util.is_prop term then term else HOLogic.mk_Trueprop term))
      |> distinct (fn (f, s) => snd f = snd s)
(*
      |> parallel_filter_out (fn (_, trm) => eq_over_same_func ctxt trm)
*)
      |> parallel_filter_out (fn (_, cnjctr_trm) => cnjctr_trm = trm)
      |> parallel_filter_out (fn (_, trm) => S4TD.run_assertion pst trm S4TD.has_func_with_three_occs_in_a_row)
      |> parallel_filter     (fn (_, trm) => S4TD.run_assertion pst trm S4TD.fvars_in_prem_should_appear_in_concl)
      |> parallel_filter     (fn (_, trm) => S4TD.run_assertion pst trm S4TD.does_not_have_trivial_equality)
      |> parallel_filter_out (fn (_, trm) => S4TD.run_assertion pst trm S4TD.nested_eq)
      |> parallel_filter_out (fn (_, trm) => S4TD.run_assertion pst trm S4TD.var_appears_many_times_but_always_in_the_same_subtrm)
      |> map (fn (_,    term) => (SS.get_lemma_name term2name ctxt term, term));
    val _ = tracing' "[[[[[[[[[[[top_down_conjecture ends]]]]]]]]]]": unit;
  in
    results
  end;

end;