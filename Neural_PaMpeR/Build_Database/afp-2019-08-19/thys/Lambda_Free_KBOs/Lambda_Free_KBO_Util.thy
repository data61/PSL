(*  Title:       Utilities for Knuth-Bendix Orders for Lambda-Free Higher-Order Terms
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>Utilities for Knuth--Bendix Orders for Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_KBO_Util
imports Lambda_Free_RPOs.Lambda_Free_Term Lambda_Free_RPOs.Extension_Orders Polynomials.Polynomials
begin

locale kbo_basic_basis = gt_sym "(>\<^sub>s)"
    for gt_sym :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix ">\<^sub>s" 50) +
  fixes
    wt_sym :: "'s \<Rightarrow> nat" and
    \<epsilon> :: nat and
    ground_heads_var :: "'v \<Rightarrow> 's set" and
    extf :: "'s \<Rightarrow> (('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm list \<Rightarrow> ('s, 'v) tm list \<Rightarrow>
      bool"
  assumes
    \<epsilon>_gt_0: "\<epsilon> > 0" and
    wt_sym_ge_\<epsilon>: "wt_sym f \<ge> \<epsilon>" and
    ground_heads_var_nonempty: "ground_heads_var x \<noteq> {}" and
    extf_ext_irrefl_before_trans: "ext_irrefl_before_trans (extf f)" and
    extf_ext_compat_list_strong: "ext_compat_list_strong (extf f)" and
    extf_ext_hd_or_tl: "ext_hd_or_tl (extf f)"
begin

lemma wt_sym_gt_0: "wt_sym f > 0"
  by (rule less_le_trans[OF \<epsilon>_gt_0 wt_sym_ge_\<epsilon>])

end

locale kbo_std_basis = ground_heads "(>\<^sub>s)" arity_sym arity_var
    for
      gt_sym :: "'s \<Rightarrow> 's \<Rightarrow> bool" (infix ">\<^sub>s" 50) and
      arity_sym :: "'s \<Rightarrow> enat" and
      arity_var :: "'v \<Rightarrow> enat" +
  fixes
    wt_sym :: "'s \<Rightarrow> 'n::{ord,semiring_1}" and
    \<epsilon> :: nat and
    \<delta> :: nat and
    extf :: "'s \<Rightarrow> (('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool) \<Rightarrow> ('s, 'v) tm list \<Rightarrow> ('s, 'v) tm list \<Rightarrow>
      bool"
  assumes
    \<epsilon>_gt_0: "\<epsilon> > 0" and
    \<delta>_le_\<epsilon>: "\<delta> \<le> \<epsilon>" and
    arity_hd_ne_infinity_if_\<delta>_gt_0: "\<delta> > 0 \<Longrightarrow> arity_hd \<zeta> \<noteq> \<infinity>" and
    wt_sym_ge: "wt_sym f \<ge> of_nat (\<epsilon> - the_enat (of_nat \<delta> * arity_sym f))" and
    unary_wt_sym_0_gt: "arity_sym f = 1 \<Longrightarrow> wt_sym f = 0 \<Longrightarrow> f >\<^sub>s g \<or> g = f" and
    unary_wt_sym_0_imp_\<delta>_eq_\<epsilon>: "arity_sym f = 1 \<Longrightarrow> wt_sym f = 0 \<Longrightarrow> \<delta> = \<epsilon>" and
    extf_ext_irrefl_before_trans: "ext_irrefl_before_trans (extf f)" and
    extf_ext_compat_list_strong: "ext_compat_list_strong (extf f)" and
    extf_ext_hd_or_tl: "ext_hd_or_tl (extf f)" and
    extf_ext_snoc_if_\<delta>_eq_\<epsilon>: "\<delta> = \<epsilon> \<Longrightarrow> ext_snoc (extf f)"
begin

lemma arity_sym_ne_infinity_if_\<delta>_gt_0: "\<delta> > 0 \<Longrightarrow> arity_sym f \<noteq> \<infinity>"
  by (metis arity_hd.simps(2) arity_hd_ne_infinity_if_\<delta>_gt_0)

lemma arity_var_ne_infinity_if_\<delta>_gt_0: "\<delta> > 0 \<Longrightarrow> arity_var x \<noteq> \<infinity>"
  by (metis arity_hd.simps(1) arity_hd_ne_infinity_if_\<delta>_gt_0)

lemma arity_ne_infinity_if_\<delta>_gt_0: "\<delta> > 0 \<Longrightarrow> arity s \<noteq> \<infinity>"
  unfolding arity_def
  by (induct s rule: tm_induct_apps)
    (metis arity_hd_ne_infinity_if_\<delta>_gt_0 enat.distinct(2) enat.exhaust idiff_enat_enat)

lemma extf_ext_irrefl: "ext_irrefl (extf f)"
  by (rule ext_irrefl_before_trans.axioms(1)[OF extf_ext_irrefl_before_trans])

lemma extf_ext: "ext (extf f)"
  by (rule ext_irrefl.axioms(1)[OF extf_ext_irrefl])

lemma
  extf_ext_compat_cons: "ext_compat_cons (extf f)" and
  extf_ext_compat_snoc: "ext_compat_snoc (extf f)" and
  extf_ext_singleton: "ext_singleton (extf f)"
  by (rule ext_compat_list_strong.axioms[OF extf_ext_compat_list_strong])+

lemma extf_ext_compat_list: "ext_compat_list (extf f)"
  using extf_ext_compat_list_strong
  by (simp add: ext_compat_list_axioms_def ext_compat_list_def ext_compat_list_strong.compat_list
    ext_compat_list_strong_def ext_singleton.axioms(1))

lemma extf_ext_wf_bounded: "ext_wf_bounded (extf f)"
  unfolding ext_wf_bounded_def using extf_ext_irrefl_before_trans extf_ext_hd_or_tl by simp

lemmas extf_mono_strong = ext.mono_strong[OF extf_ext]
lemmas extf_mono = ext.mono[OF extf_ext, mono]
lemmas extf_map = ext.map[OF extf_ext]
lemmas extf_irrefl = ext_irrefl.irrefl[OF extf_ext_irrefl]
lemmas extf_trans_from_irrefl =
  ext_irrefl_before_trans.trans_from_irrefl[OF extf_ext_irrefl_before_trans]
lemmas extf_compat_cons = ext_compat_cons.compat_cons[OF extf_ext_compat_cons]
lemmas extf_compat_append_left = ext_compat_cons.compat_append_left[OF extf_ext_compat_cons]
lemmas extf_compat_append_right = ext_compat_snoc.compat_append_right[OF extf_ext_compat_snoc]
lemmas extf_compat_list = ext_compat_list.compat_list[OF extf_ext_compat_list]
lemmas extf_singleton = ext_singleton.singleton[OF extf_ext_singleton]
lemmas extf_wf_bounded = ext_wf_bounded.wf_bounded[OF extf_ext_wf_bounded]

lemmas extf_snoc_if_\<delta>_eq_\<epsilon> = ext_snoc.snoc[OF extf_ext_snoc_if_\<delta>_eq_\<epsilon>]

lemma extf_singleton_nil_if_\<delta>_eq_\<epsilon>: "\<delta> = \<epsilon> \<Longrightarrow> extf f gt [s] []"
  by (rule extf_snoc_if_\<delta>_eq_\<epsilon>[of _ _ "[]", simplified])

end

sublocale kbo_basic_basis < kbo_std_basis _ _ "\<lambda>_. \<infinity>" "\<lambda>_. \<infinity>" _ _ 0
  unfolding kbo_std_basis_def kbo_std_basis_axioms_def
  by (auto simp: wt_sym_gt_0 \<epsilon>_gt_0 wt_sym_ge_\<epsilon> less_not_refl2 ground_heads_var_nonempty
    gt_sym_axioms ground_heads_def ground_heads_axioms_def extf_ext_irrefl_before_trans
    extf_ext_compat_list_strong extf_ext_hd_or_tl)

end
