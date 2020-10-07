(*
  File: Order_Thms.thy
  Author: Bohua Zhan

  Setup for proof steps related to ordering.
*)

section \<open>Setup for ordering\<close>

theory Order_Thms
  imports Logic_Thms HOL.Rat
begin

ML_file \<open>util_arith.ML\<close>
setup \<open>Consts.add_const_data ("NUMC", UtilArith.is_numc)\<close>

subsection \<open>Results in class order or preorder\<close>

setup \<open>add_forward_prfstep_cond @{thm Orderings.order_class.order.trans} [with_filt (not_type_filter "a" natT)]\<close>
setup \<open>add_forward_prfstep_cond @{thm Orderings.order_class.order.strict_trans} [with_filt (not_type_filter "a" natT)]\<close>
setup \<open>add_forward_prfstep_cond @{thm Orderings.order_le_less_trans} [with_filt (not_type_filter "x" natT)]\<close>
setup \<open>add_forward_prfstep_cond @{thm Orderings.order_less_le_trans} [with_filt (not_type_filter "x" natT)]\<close>
setup \<open>add_resolve_prfstep @{thm Orderings.order_class.order.irrefl}\<close>
setup \<open>add_forward_prfstep_cond @{thm Orderings.le_neq_trans} [with_cond "?a \<noteq> ?b"]\<close>
setup \<open>add_forward_prfstep_cond @{thm Orderings.order_antisym} [with_filt (order_filter "x" "y"), with_cond "?x \<noteq> ?y"]\<close>

subsection \<open>Rewriting of negation, in linorder\<close>

setup \<open>fold add_gen_prfstep [
  ("not_less",
   [WithProp @{term_pat "\<not> (?x::(?'a::linorder)) < ?y"},
    GetFact (@{term_pat "?y \<le> (?x::(?'a::linorder))"}, equiv_forward_th @{thm linorder_not_less}),
    WithScore 1]),
  ("not_le",
   [WithProp @{term_pat "\<not> (?x::(?'a::linorder)) \<le> ?y"},
    GetFact (@{term_pat "?y < (?x::(?'a::linorder))"}, equiv_forward_th @{thm linorder_not_le}),
    WithScore 1])]
\<close>

subsection \<open>Properties of max and min (in linorder)\<close>

setup \<open>add_rewrite_rule @{thm min.commute}\<close>
setup \<open>add_rewrite_rule @{thm min.idem}\<close>
setup \<open>add_forward_prfstep_cond @{thm min.cobounded1} [with_term "min ?a ?b"]\<close>
setup \<open>add_forward_prfstep_cond @{thm min.cobounded2} [with_term "min ?a ?b"]\<close>
setup \<open>add_backward2_prfstep @{thm min.boundedI}\<close>
setup \<open>add_backward2_prfstep @{thm min.mono}\<close>
setup \<open>add_rewrite_rule @{thm min.absorb1}\<close>
setup \<open>add_rewrite_rule @{thm min.absorb2}\<close>

setup \<open>add_rewrite_rule @{thm max.commute}\<close>
setup \<open>add_rewrite_rule @{thm max.idem}\<close>
setup \<open>add_forward_prfstep_cond @{thm max.cobounded1} [with_term "max ?a ?b"]\<close>
setup \<open>add_forward_prfstep_cond @{thm max.cobounded2} [with_term "max ?a ?b"]\<close>
setup \<open>add_backward2_prfstep @{thm max.boundedI}\<close>
setup \<open>add_backward2_prfstep @{thm max.mono}\<close>
setup \<open>add_rewrite_rule @{thm max.absorb1}\<close>
setup \<open>add_rewrite_rule @{thm max.absorb2}\<close>

subsection \<open>Min\<close>

setup \<open>add_backward_prfstep @{thm Min_in}\<close>
setup \<open>add_backward_prfstep @{thm Min_le}\<close>
setup \<open>add_backward2_prfstep @{thm Min_eqI}\<close>

subsection \<open>Existence of numbers satisfying inequalities\<close>

theorem exists_ge [resolve]: "\<exists>k. k \<ge> (i::('a::order))" by auto
setup \<open>fold add_resolve_prfstep [@{thm lt_ex}, @{thm gt_ex}]\<close>
setup \<open>add_backward_prfstep @{thm dense}\<close>

end
