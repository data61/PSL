(*  Title:       The Graceful Transfinite Knuth-Bendix Order with Subterm Coefficients for Lambda-Free Higher-Order Terms
    Author:      Heiko Becker <heikobecker92@gmail.com>, 2016
    Author:      Jasmin Blanchette <jasmin.blanchette at inria.fr>, 2016
    Author:      Uwe Waldmann <waldmann at mpi-inf.mpg.de>, 2016
    Author:      Daniel Wand <dwand at mpi-inf.mpg.de>, 2016
    Maintainer:  Jasmin Blanchette <jasmin.blanchette at inria.fr>
*)

section \<open>The Graceful Transfinite Knuth--Bendix Order with Subterm Coefficients for
  Lambda-Free Higher-Order Terms\<close>

theory Lambda_Free_TKBO_Coefs
imports Lambda_Free_KBO_Util Nested_Multisets_Ordinals.Signed_Syntactic_Ordinal
abbrevs "=p" = "=\<^sub>p"
  and ">p" = ">\<^sub>p"
  and "\<ge>p" = "\<ge>\<^sub>p"
  and ">t" = ">\<^sub>t"
  and "\<ge>t" = "\<ge>\<^sub>t"
  and "!h" = "\<^sub>h"
begin

text \<open>
This theory defines the graceful transfinite Knuth--Bendix order (KBO) with
subterm coefficients for \<open>\<lambda>\<close>-free higher-order terms. The proof was
developed by copying that of the standard KBO and generalizing it along two
axes:\ subterm coefficients and ordinals. Both features complicate the
definitions and proofs substantially.
\<close>


subsection \<open>Setup\<close>

hide_const (open) Complex.arg

locale tkbo_coefs = kbo_std_basis _ _ arity_sym arity_var wt_sym
    for
      arity_sym :: "'s \<Rightarrow> enat" and
      arity_var :: "'v \<Rightarrow> enat" and
      wt_sym :: "'s \<Rightarrow> hmultiset" +
  fixes coef_sym :: "'s \<Rightarrow> nat \<Rightarrow> hmultiset"
  assumes coef_sym_gt_0: "coef_sym f i > 0"
begin

abbreviation \<delta>\<^sub>h :: hmultiset where
  "\<delta>\<^sub>h \<equiv> of_nat \<delta>"

abbreviation \<epsilon>\<^sub>h :: hmultiset where
  "\<epsilon>\<^sub>h \<equiv> of_nat \<epsilon>"

abbreviation arity_sym\<^sub>h :: "'s \<Rightarrow> hmultiset" where
  "arity_sym\<^sub>h f \<equiv> hmset_of_enat (arity_sym f)"

abbreviation arity_var\<^sub>h :: "'v \<Rightarrow> hmultiset" where
  "arity_var\<^sub>h f \<equiv> hmset_of_enat (arity_var f)"

abbreviation arity_hd\<^sub>h :: "('s, 'v) hd \<Rightarrow> hmultiset" where
  "arity_hd\<^sub>h f \<equiv> hmset_of_enat (arity_hd f)"

abbreviation arity\<^sub>h :: "('s, 'v) tm \<Rightarrow> hmultiset" where
  "arity\<^sub>h s \<equiv> hmset_of_enat (arity s)"

lemma arity\<^sub>h_conv: "arity\<^sub>h s = arity_hd\<^sub>h (head s) - of_nat (num_args s)"
  unfolding arity_def by simp

lemma arity\<^sub>h_App[simp]: "arity\<^sub>h (App s t) = arity\<^sub>h s - 1"
  by (simp add: one_enat_def)

lemmas wary_App\<^sub>h[intro] = wary_App[folded of_nat_lt_hmset_of_enat_iff]
lemmas wary_AppE\<^sub>h = wary_AppE[folded of_nat_lt_hmset_of_enat_iff]
lemmas wary_num_args_le_arity_head\<^sub>h =
  wary_num_args_le_arity_head[folded of_nat_le_hmset_of_enat_iff]
lemmas wary_apps\<^sub>h = wary_apps[folded of_nat_le_hmset_of_enat_iff]
lemmas wary_cases_apps\<^sub>h[consumes 1, case_names apps] =
  wary_cases_apps[folded of_nat_le_hmset_of_enat_iff]

lemmas ground_heads_arity\<^sub>h = ground_heads_arity[folded hmset_of_enat_le]
lemmas some_ground_head_arity\<^sub>h = some_ground_head_arity[folded hmset_of_enat_le]
lemmas \<epsilon>\<^sub>h_gt_0 = \<epsilon>_gt_0[folded of_nat_less_hmset, unfolded of_nat_0]
lemmas \<delta>\<^sub>h_le_\<epsilon>\<^sub>h = \<delta>_le_\<epsilon>[folded of_nat_le_hmset]
lemmas arity_hd\<^sub>h_lt_\<omega>_if_\<delta>\<^sub>h_gt_0 = arity_hd_ne_infinity_if_\<delta>_gt_0
  [folded of_nat_less_hmset, unfolded of_nat_0, folded hmset_of_enat_lt_iff_ne_infinity]

lemma wt_sym_ge\<^sub>h: "wt_sym f \<ge> \<epsilon>\<^sub>h - \<delta>\<^sub>h * arity_sym\<^sub>h f"
proof -
  have "of_nat (the_enat (of_nat \<delta> * arity_sym f)) = \<delta>\<^sub>h * arity_sym\<^sub>h f"
  by (cases "arity_sym f", simp add: of_nat_eq_enat,
    metis arity_sym_ne_infinity_if_\<delta>_gt_0 gr_zeroI mult_eq_0_iff of_nat_0 the_enat_0)
  thus ?thesis
    using wt_sym_ge[unfolded of_nat_minus_hmset] by metis
qed

lemmas unary_wt_sym_0_gt\<^sub>h = unary_wt_sym_0_gt[folded hmset_of_enat_inject, unfolded hmset_of_enat_1]
lemmas unary_wt_sym_0_imp_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h = unary_wt_sym_0_imp_\<delta>_eq_\<epsilon>
  [folded of_nat_inject_hmset, unfolded of_nat_0]
lemmas extf_ext_snoc_if_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h = extf_ext_snoc_if_\<delta>_eq_\<epsilon>[folded of_nat_inject_hmset]
lemmas extf_snoc_if_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h = ext_snoc.snoc[OF extf_ext_snoc_if_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h]
lemmas arity_sym\<^sub>h_lt_\<omega>_if_\<delta>\<^sub>h_gt_0 = arity_sym_ne_infinity_if_\<delta>_gt_0
  [folded of_nat_less_hmset hmset_of_enat_lt_iff_ne_infinity, unfolded of_nat_0]
lemmas arity_var\<^sub>h_lt_\<omega>_if_\<delta>\<^sub>h_gt_0 = arity_var_ne_infinity_if_\<delta>_gt_0
  [folded of_nat_less_hmset hmset_of_enat_lt_iff_ne_infinity, unfolded of_nat_0]
lemmas arity\<^sub>h_lt_\<omega>_if_\<delta>\<^sub>h_gt_0 = arity_ne_infinity_if_\<delta>_gt_0
  [folded of_nat_less_hmset hmset_of_enat_lt_iff_ne_infinity, unfolded of_nat_0]
lemmas warywary_subst_subst\<^sub>h_conv = wary_subst_def[folded hmset_of_enat_le]
lemmas extf_singleton_nil_if_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h = extf_singleton_nil_if_\<delta>_eq_\<epsilon>[folded of_nat_inject_hmset]

lemma arity_sym\<^sub>h_if_\<delta>\<^sub>h_gt_0_E:
  assumes \<delta>_gt_0: "\<delta>\<^sub>h > 0"
  obtains n where "arity_sym\<^sub>h f = of_nat n"
  using arity_sym\<^sub>h_lt_\<omega>_if_\<delta>\<^sub>h_gt_0 assms lt_\<omega>_imp_ex_of_nat by blast

lemma arity_var\<^sub>h_if_\<delta>\<^sub>h_gt_0_E:
  assumes \<delta>_gt_0: "\<delta>\<^sub>h > 0"
  obtains n where "arity_var\<^sub>h f = of_nat n"
  using arity_var\<^sub>h_lt_\<omega>_if_\<delta>\<^sub>h_gt_0 assms lt_\<omega>_imp_ex_of_nat by blast


subsection \<open>Weights and Subterm Coefficients\<close>

abbreviation zhmset_of_tpoly :: "('a, hmultiset) tpoly \<Rightarrow> ('a, zhmultiset) tpoly" where
  "zhmset_of_tpoly \<equiv> map_tpoly (\<lambda>x. x) zhmset_of"

abbreviation eval_ztpoly :: "('a \<Rightarrow> zhmultiset) \<Rightarrow> ('a, hmultiset) tpoly \<Rightarrow> zhmultiset" where
  "eval_ztpoly A p \<equiv> eval_tpoly A (zhmset_of_tpoly p)"

lemma eval_tpoly_eq_eval_ztpoly[simp]:
  "zhmset_of (eval_tpoly A p) = eval_ztpoly (\<lambda>v. zhmset_of (A v)) p"
  by (induct p, simp_all add: zhmset_of_sum_list zhmset_of_prod_list o_def,
    simp_all cong: map_cong)

definition min_ground_head :: "('s, 'v) hd \<Rightarrow> 's" where
  "min_ground_head \<zeta> =
   (SOME f. f \<in> ground_heads \<zeta> \<and>
      (\<forall>g \<in> ground_heads \<zeta>. wt_sym g + \<delta>\<^sub>h * arity_sym\<^sub>h g \<ge> wt_sym f + \<delta>\<^sub>h * arity_sym\<^sub>h f))"

datatype 'va pvar =
  PWt 'va
| PCoef 'va nat

primrec min_passign :: "'v pvar \<Rightarrow> hmultiset" where
  "min_passign (PWt x) = wt_sym (min_ground_head (Var x))"
| "min_passign (PCoef _ _) = 1"

abbreviation min_zpassign :: "'v pvar \<Rightarrow> zhmultiset" where
  "min_zpassign v \<equiv> zhmset_of (min_passign v)"

lemma min_zpassign_simps[simp]:
  "min_zpassign (PWt x) = zhmset_of (wt_sym (min_ground_head (Var x)))"
  "min_zpassign (PCoef x i) = 1"
  by (simp_all add: zhmset_of_1)

definition legal_passign :: "('v pvar \<Rightarrow> hmultiset) \<Rightarrow> bool" where
  "legal_passign A \<longleftrightarrow> (\<forall>x. A x \<ge> min_passign x)"

definition legal_zpassign :: "('v pvar \<Rightarrow> zhmultiset) \<Rightarrow> bool" where
  "legal_zpassign A \<longleftrightarrow> (\<forall>x. A x \<ge> min_zpassign x)"

lemma legal_min_passign: "legal_passign min_passign"
  unfolding legal_passign_def by simp

lemma legal_min_zpassign: "legal_zpassign min_zpassign"
  unfolding legal_zpassign_def by simp

lemma assign_ge_0[intro]: "legal_zpassign A \<Longrightarrow> A x \<ge> 0"
  unfolding legal_zpassign_def by (auto intro: dual_order.trans)

definition
  eq_tpoly :: "('v pvar, hmultiset) tpoly \<Rightarrow> ('v pvar, hmultiset) tpoly \<Rightarrow> bool" (infix "=\<^sub>p" 50)
where
  "q =\<^sub>p p \<longleftrightarrow> (\<forall>A. legal_zpassign A \<longrightarrow> eval_ztpoly A q = eval_ztpoly A p)"

definition
  ge_tpoly :: "('v pvar, hmultiset) tpoly \<Rightarrow> ('v pvar, hmultiset) tpoly \<Rightarrow> bool" (infix "\<ge>\<^sub>p" 50)
where
  "q \<ge>\<^sub>p p \<longleftrightarrow> (\<forall>A. legal_zpassign A \<longrightarrow> eval_ztpoly A q \<ge> eval_ztpoly A p)"

definition
  gt_tpoly :: "('v pvar, hmultiset) tpoly \<Rightarrow> ('v pvar, hmultiset) tpoly \<Rightarrow> bool" (infix ">\<^sub>p" 50)
where
  "q >\<^sub>p p \<longleftrightarrow> (\<forall>A. legal_zpassign A \<longrightarrow> eval_ztpoly A q > eval_ztpoly A p)"

lemma gt_tpoly_imp_ge[intro]: "q >\<^sub>p p \<Longrightarrow> q \<ge>\<^sub>p p"
  unfolding ge_tpoly_def gt_tpoly_def by (simp add: le_less)

lemma eq_tpoly_refl[simp]: "p =\<^sub>p p"
  unfolding eq_tpoly_def by simp

lemma ge_tpoly_refl[simp]: "p \<ge>\<^sub>p p"
  unfolding ge_tpoly_def by simp

lemma gt_tpoly_irrefl: "\<not> p >\<^sub>p p"
  unfolding gt_tpoly_def legal_zpassign_def by fast

lemma
  eq_eq_tpoly_trans: "r =\<^sub>p q \<Longrightarrow> q =\<^sub>p p \<Longrightarrow> r =\<^sub>p p" and
  eq_ge_tpoly_trans: "r =\<^sub>p q \<Longrightarrow> q \<ge>\<^sub>p p \<Longrightarrow> r \<ge>\<^sub>p p" and
  eq_gt_tpoly_trans: "r =\<^sub>p q \<Longrightarrow> q >\<^sub>p p \<Longrightarrow> r >\<^sub>p p" and
  ge_eq_tpoly_trans: "r \<ge>\<^sub>p q \<Longrightarrow> q =\<^sub>p p \<Longrightarrow> r \<ge>\<^sub>p p" and
  ge_ge_tpoly_trans: "r \<ge>\<^sub>p q \<Longrightarrow> q \<ge>\<^sub>p p \<Longrightarrow> r \<ge>\<^sub>p p" and
  ge_gt_tpoly_trans: "r \<ge>\<^sub>p q \<Longrightarrow> q >\<^sub>p p \<Longrightarrow> r >\<^sub>p p" and
  gt_eq_tpoly_trans: "r >\<^sub>p q \<Longrightarrow> q =\<^sub>p p \<Longrightarrow> r >\<^sub>p p" and
  gt_ge_tpoly_trans: "r >\<^sub>p q \<Longrightarrow> q \<ge>\<^sub>p p \<Longrightarrow> r >\<^sub>p p" and
  gt_gt_tpoly_trans: "r >\<^sub>p q \<Longrightarrow> q >\<^sub>p p \<Longrightarrow> r >\<^sub>p p"
  unfolding eq_tpoly_def ge_tpoly_def gt_tpoly_def
  by (auto intro: order.trans less_trans less_le_trans le_less_trans)+

primrec coef_hd :: "('s, 'v) hd \<Rightarrow> nat \<Rightarrow> ('v pvar, hmultiset) tpoly" where
  "coef_hd (Var x) i = PVar (PCoef x i)"
| "coef_hd (Sym f) i = PNum (coef_sym f i)"

lemma coef_hd_gt_0:
  assumes legal: "legal_zpassign A"
  shows "eval_ztpoly A (coef_hd \<zeta> i) > 0"
  unfolding legal_zpassign_def
proof (cases \<zeta>)
  case (Var x1)
  thus ?thesis
    using legal[unfolded legal_zpassign_def, rule_format, of "PCoef x i" for x]
    by (auto simp: coef_sym_gt_0 zhmset_of_1 intro: dual_order.strict_trans1 zero_less_one)
next
  case (Sym x2)
  thus ?thesis
    using legal[unfolded legal_zpassign_def, rule_format, of "PWt x" for x]
    by simp (metis coef_sym_gt_0 zhmset_of_0 zhmset_of_less)
qed

primrec coef :: "('s, 'v) tm \<Rightarrow> nat \<Rightarrow> ('v pvar, hmultiset) tpoly" where
  "coef (Hd \<zeta>) i = coef_hd \<zeta> i"
| "coef (App s _) i = coef s (i + 1)"

lemma coef_apps[simp]: "coef (apps s ss) i = coef s (i + length ss)"
  by (induct ss arbitrary: s i) auto

lemma coef_gt_0: "legal_zpassign A \<Longrightarrow> eval_ztpoly A (coef s i) > 0"
   by (induct s arbitrary: i) (auto intro: coef_hd_gt_0)

lemma exists_min_ground_head:
  "\<exists>f. f \<in> ground_heads \<zeta> \<and>
     (\<forall>g \<in> ground_heads \<zeta>. wt_sym g + \<delta>\<^sub>h * arity_sym\<^sub>h g \<ge> wt_sym f + \<delta>\<^sub>h * arity_sym\<^sub>h f)"
proof -
  let ?R = "{(f, g). f \<in> ground_heads \<zeta> \<and> g \<in> ground_heads \<zeta> \<and>
    wt_sym g + \<delta>\<^sub>h * arity_sym\<^sub>h g > wt_sym f + \<delta>\<^sub>h * arity_sym\<^sub>h f}"

  have wf_R: "wf ?R"
    using wf_app[of "{(M, N). M < N}" "\<lambda>f. wt_sym f + \<delta>\<^sub>h * arity_sym\<^sub>h f", OF wf]
    by (auto intro: wf_subset)
  have "\<exists>f. f \<in> ground_heads \<zeta>"
    by (meson ground_heads_nonempty subsetI subset_empty)
  thus ?thesis
    using wf_eq_minimal[THEN iffD1, OF wf_R] by force
qed

lemma min_ground_head_Sym[simp]: "min_ground_head (Sym f) = f"
  unfolding min_ground_head_def by auto

lemma min_ground_head_in_ground_heads: "min_ground_head \<zeta> \<in> ground_heads \<zeta>"
  unfolding min_ground_head_def using someI_ex[OF exists_min_ground_head] by blast

lemma min_ground_head_min:
  "f \<in> ground_heads \<zeta> \<Longrightarrow>
   wt_sym f + \<delta>\<^sub>h * arity_sym\<^sub>h f \<ge> wt_sym (min_ground_head \<zeta>) + \<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<zeta>)"
  unfolding min_ground_head_def using someI_ex[OF exists_min_ground_head] by blast

lemma min_ground_head_antimono:
  "ground_heads \<zeta> \<subseteq> ground_heads \<xi> \<Longrightarrow>
   wt_sym (min_ground_head \<zeta>) + \<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<zeta>)
   \<ge> wt_sym (min_ground_head \<xi>) + \<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<xi>)"
  using min_ground_head_in_ground_heads min_ground_head_min by blast

primrec wt0 :: "('s, 'v) hd \<Rightarrow> ('v pvar, hmultiset) tpoly" where
  "wt0 (Var x) = PVar (PWt x)"
| "wt0 (Sym f) = PNum (wt_sym f)"

lemma wt0_ge_min_ground_head:
  "legal_zpassign A \<Longrightarrow> eval_ztpoly A (wt0 \<zeta>) \<ge> zhmset_of (wt_sym (min_ground_head \<zeta>))"
  by (cases \<zeta>, simp_all, metis legal_zpassign_def min_zpassign_simps(1))

lemma eval_ztpoly_nonneg: "legal_zpassign A \<Longrightarrow> eval_ztpoly A p \<ge> 0"
  by (induct p) (auto cong: map_cong intro!: sum_list_nonneg prod_list_nonneg)

lemma in_zip_imp_size_lt_apps: "(s, y) \<in> set (zip ss ys) \<Longrightarrow> size s < size (apps (Hd \<zeta>) ss)"
  by (auto dest!: set_zip_leftD simp: size_in_args)

function wt :: "('s, 'v) tm \<Rightarrow> ('v pvar, hmultiset) tpoly" where
  "wt (apps (Hd \<zeta>) ss) =
   PSum ([wt0 \<zeta>, PNum (\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss)))] @
     map (\<lambda>(s, i). PMult [coef_hd \<zeta> i, wt s]) (zip ss [0..<length ss]))"
  by (erule tm_exhaust_apps) simp
termination
  by (lexicographic_order simp: in_zip_imp_size_lt_apps)

definition
  wt_args :: "nat \<Rightarrow> ('v pvar \<Rightarrow> zhmultiset) \<Rightarrow> ('s, 'v) hd \<Rightarrow> ('s, 'v) tm list \<Rightarrow> zhmultiset"
where
  "wt_args i A \<zeta> ss = sum_list
     (map (eval_ztpoly A \<circ> (\<lambda>(s, i). PMult [coef_hd \<zeta> i, wt s])) (zip ss [i..<i + length ss]))"

lemma wt_Hd[simp]: "wt (Hd \<zeta>) = PSum [wt0 \<zeta>, PNum (\<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<zeta>))]"
  by (rule wt.simps[of _ "[]", simplified])

lemma coef_hd_cong:
  "(\<forall>x \<in> vars_hd \<zeta>. \<forall>i. A (PCoef x i) = B (PCoef x i)) \<Longrightarrow>
   eval_ztpoly A (coef_hd \<zeta> i) = eval_ztpoly B (coef_hd \<zeta> i)"
  by (cases \<zeta>) auto

lemma wt0_cong:
  assumes pwt_eq: "\<forall>x \<in> vars_hd \<zeta>. A (PWt x) = B (PWt x)"
  shows "eval_ztpoly A (wt0 \<zeta>) = eval_ztpoly B (wt0 \<zeta>)"
  using pwt_eq by (cases \<zeta>) auto

lemma wt_cong:
  assumes
    "\<forall>x \<in> vars s. A (PWt x) = B (PWt x)" and
    "\<forall>x \<in> vars s. \<forall>i. A (PCoef x i) = B (PCoef x i)"
  shows "eval_ztpoly A (wt s) = eval_ztpoly B (wt s)"
  using assms
proof (induct s rule: tm_induct_apps)
  case (apps \<zeta> ss)
  note ih = this(1) and pwt_eq = this(2) and pcoef_eq = this(3)

  have ih': "eval_ztpoly A (wt s) = eval_ztpoly B (wt s)" if s_in: "s \<in> set ss" for s
  proof (rule ih[OF s_in])
    show "\<forall>x \<in> vars s. A (PWt x) = B (PWt x)"
      using pwt_eq s_in by force
    show "\<forall>x \<in> vars s. \<forall>i. A (PCoef x i) = B (PCoef x i)"
      using pcoef_eq s_in by force
  qed

  have wt0_eq: "eval_ztpoly A (wt0 \<zeta>) = eval_ztpoly B (wt0 \<zeta>)"
    by (rule wt0_cong) (simp add: pwt_eq)
  have coef_\<zeta>_eq: "eval_ztpoly A (coef_hd \<zeta> i) = eval_ztpoly B (coef_hd \<zeta> i)" for i
    by (rule coef_hd_cong) (simp add: pcoef_eq)

  show ?case
    using ih' wt0_eq coef_\<zeta>_eq by (auto dest!: set_zip_leftD intro!: arg_cong[of _ _ sum_list])
qed

lemma ground_eval_ztpoly_wt_eq: "ground s \<Longrightarrow> eval_ztpoly A (wt s) = eval_ztpoly B (wt s)"
  by (rule wt_cong) auto

lemma exists_wt_sym:
  assumes legal: "legal_zpassign A"
  shows "\<exists>f \<in> ground_heads \<zeta>. eval_ztpoly A (wt (Hd \<zeta>)) \<ge> zhmset_of (wt_sym f + \<delta>\<^sub>h * arity_sym\<^sub>h f)"
  unfolding eq_tpoly_def
proof (cases \<zeta>)
  case Var
  thus ?thesis
    using legal[unfolded legal_zpassign_def]
    by simp (metis add_le_cancel_right ground_heads.simps(1) min_ground_head_in_ground_heads
      min_zpassign_simps(1) zhmset_of_plus)
next
  case Sym
  thus ?thesis
    by (simp add: zhmset_of_plus)
qed

lemma wt_ge_\<epsilon>\<^sub>h:
  assumes legal: "legal_zpassign A"
  shows "eval_ztpoly A (wt s) \<ge> zhmset_of \<epsilon>\<^sub>h"
proof (induct s rule: tm_induct_apps)
  case (apps \<zeta> ss)
  note ih = this(1)

  {
    assume ss_eq_nil: "ss = []"

    have "\<epsilon>\<^sub>h \<le> wt_sym (min_ground_head \<zeta>) + \<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<zeta>)"
      using wt_sym_ge\<^sub>h[of "min_ground_head \<zeta>"]
      by (metis add_diff_cancel_left' leD leI le_imp_minus_plus_hmset le_minus_plus_same_hmset
        less_le_trans)
    hence "zhmset_of \<epsilon>\<^sub>h
      \<le> zhmset_of (wt_sym (min_ground_head \<zeta>)) + zhmset_of (\<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<zeta>))"
      by (metis zhmset_of_le zhmset_of_plus)
    also have "\<dots>
      \<le> eval_tpoly A (map_tpoly (\<lambda>x. x) zhmset_of (wt0 \<zeta>))
        + zhmset_of (\<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<zeta>))"
      using wt0_ge_min_ground_head[OF legal] by simp
    finally have ?case
      using ss_eq_nil by simp
  }
  moreover
  {
    let ?arg_wt =
      "eval_tpoly A \<circ> (map_tpoly (\<lambda>x. x) zhmset_of \<circ> (\<lambda>(s, i). PMult [coef_hd \<zeta> i, wt s]))"

    assume ss_ne_nil: "ss \<noteq> []"
    hence "zhmset_of \<epsilon>\<^sub>h
      \<le> eval_tpoly A (map_tpoly (\<lambda>x. x) zhmset_of (PMult [coef_hd \<zeta> 0, wt (hd ss)]))"
      by (simp add: ih coef_hd_gt_0[OF legal] nonneg_le_mult_right_mono_zhmset)
    also have "\<dots> = hd (map ?arg_wt (zip ss [0..<length ss]))"
      using ss_ne_nil by (simp add: hd_map zip_nth_conv hd_conv_nth)
    also have "\<dots> \<le> sum_list (map ?arg_wt (zip ss [0..<length ss]))"
      by (rule hd_le_sum_list,
        metis (no_types, lifting) length_greater_0_conv list.collapse list.simps(3) list.simps(9)
          ss_ne_nil upt_conv_Cons zip_Cons_Cons,
        simp add: eval_ztpoly_nonneg legal)
    also have "\<dots>
      \<le> eval_tpoly A (map_tpoly (\<lambda>x. x) zhmset_of (wt0 \<zeta>)) +
        (zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss))) +
         sum_list (map ?arg_wt (zip ss [0..<length ss])))"
    proof -
      have "0 \<le> eval_tpoly A (map_tpoly (\<lambda>p. p) zhmset_of (wt0 \<zeta>))"
        using legal eval_ztpoly_nonneg by blast
      then show ?thesis
        by (meson leD leI le_add_same_cancel2 less_le_trans zhmset_of_nonneg)
    qed
    finally have ?case
      by simp
  }
  ultimately show ?case
    by linarith
qed

lemma wt_args_ge_length_times_\<epsilon>\<^sub>h:
  assumes legal: "legal_zpassign A"
  shows "wt_args i A \<zeta> ss \<ge> of_nat (length ss) * zhmset_of \<epsilon>\<^sub>h"
  unfolding wt_args_def
  by (rule sum_list_ge_length_times[unfolded wt_args_def,
      of "map (eval_ztpoly A \<circ> (\<lambda>(s, i). PMult [coef_hd \<zeta> i, wt s])) (zip ss [i..<i + length ss])",
      simplified],
    auto intro!: mult_le_mono_hmset[of 1, simplified] nonneg_le_mult_right_mono_zhmset coef_hd_gt_0
      simp: legal zero_less_iff_1_le_hmset[symmetric] coef_hd_gt_0 wt_ge_\<epsilon>\<^sub>h)

lemma wt_ge_\<delta>\<^sub>h: "legal_zpassign A \<Longrightarrow> eval_ztpoly A (wt s) \<ge> zhmset_of \<delta>\<^sub>h"
  using \<delta>\<^sub>h_le_\<epsilon>\<^sub>h[folded zhmset_of_le] order.trans wt_ge_\<epsilon>\<^sub>h zhmset_of_le by blast

lemma wt_gt_0: "legal_zpassign A \<Longrightarrow> eval_ztpoly A (wt s) > 0"
  using \<epsilon>\<^sub>h_gt_0[folded zhmset_of_less, unfolded zhmset_of_0] wt_ge_\<epsilon>\<^sub>h by (blast intro: less_le_trans)

lemma wt_gt_\<delta>\<^sub>h_if_superunary:
  assumes
    legal: "legal_zpassign A" and
    superunary: "arity_hd\<^sub>h (head s) > 1"
  shows "eval_ztpoly A (wt s) > zhmset_of \<delta>\<^sub>h"
proof (cases "\<delta>\<^sub>h = \<epsilon>\<^sub>h")
  case \<delta>_ne_\<epsilon>: False
  show ?thesis
    using order.not_eq_order_implies_strict[OF \<delta>_ne_\<epsilon> \<delta>\<^sub>h_le_\<epsilon>\<^sub>h, folded zhmset_of_less]
      wt_ge_\<epsilon>\<^sub>h[OF legal] by (blast intro: less_le_trans)
next
  case \<delta>_eq_\<epsilon>: True
  show ?thesis
    using superunary
  proof (induct s rule: tm_induct_apps)
    case (apps \<zeta> ss)
    have "arity_hd\<^sub>h \<zeta> > 1"
      using apps(2) by simp
    hence min_gr_ary: "arity_sym\<^sub>h (min_ground_head \<zeta>) > 1"
      using ground_heads_arity\<^sub>h less_le_trans min_ground_head_in_ground_heads by blast

    have "zhmset_of \<delta>\<^sub>h < eval_ztpoly A (wt0 \<zeta>) + zhmset_of (\<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<zeta>))"
      unfolding \<delta>_eq_\<epsilon>
      by (rule add_strict_increasing2[OF eval_ztpoly_nonneg[OF legal]], unfold zhmset_of_less,
        rule gt_0_lt_mult_gt_1_hmset[OF \<epsilon>\<^sub>h_gt_0 min_gr_ary])
    also have "\<dots> \<le> eval_ztpoly A (wt0 \<zeta>)
      + zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss)))
        + zhmset_of (of_nat (length ss) * \<epsilon>\<^sub>h)"
      by (auto simp: \<epsilon>\<^sub>h_gt_0 \<delta>_eq_\<epsilon> zmset_of_le zhmset_of_plus[symmetric] algebra_simps
            simp del: ring_distribs simp: ring_distribs[symmetric])
        (metis add.commute le_minus_plus_same_hmset)
    also have "\<dots> \<le> eval_ztpoly A (wt0 \<zeta>)
      + zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss))) + wt_args 0 A \<zeta> ss"
      using wt_args_ge_length_times_\<epsilon>\<^sub>h[OF legal] by (simp add: zhmset_of_times of_nat_zhmset)
    finally show ?case
      by (simp add: wt_args_def add_ac(1) comp_def)
  qed
qed

lemma wt_App_plus_\<delta>\<^sub>h_ge:
  "eval_ztpoly A (wt (App s t)) + zhmset_of \<delta>\<^sub>h
   \<ge> eval_ztpoly A (wt s) + eval_ztpoly A (coef s 0) * eval_ztpoly A (wt t)"
proof (cases s rule: tm_exhaust_apps)
  case s: (apps \<zeta> ss)
  show ?thesis
  proof (cases "arity_sym\<^sub>h (min_ground_head \<zeta>) = \<omega>")
    case ary_eq_\<omega>: True
    show ?thesis
      unfolding ary_eq_\<omega> s App_apps wt.simps
      by (auto simp: diff_diff_add_hmset[symmetric] add.assoc)
  next
    case False
    show ?thesis
      unfolding s App_apps wt.simps
      by (simp add: algebra_simps zhmset_of_plus[symmetric] zmset_of_le,
        simp del: diff_diff_add_hmset add: add.commute[of 1] le_minus_plus_same_hmset
          distrib_left[of _ "1 :: hmultiset", unfolded mult.right_neutral, symmetric]
          diff_diff_add_hmset[symmetric])
  qed
qed

lemma wt_App_fun_\<delta>\<^sub>h:
  assumes
    legal: "legal_zpassign A" and
    wt_st: "eval_ztpoly A (wt (App s t)) = eval_ztpoly A (wt t)"
  shows "eval_ztpoly A (wt s) = zhmset_of \<delta>\<^sub>h"
proof -
  have "eval_ztpoly A (wt (App s t)) = eval_ztpoly A (wt t)"
    using wt_st by simp
  hence wt_s_t_le_\<delta>_t: "eval_ztpoly A (wt s) + eval_ztpoly A (coef s 0) * eval_ztpoly A (wt t)
     \<le> zhmset_of \<delta>\<^sub>h + eval_ztpoly A (wt t)"
    using wt_App_plus_\<delta>\<^sub>h_ge by (metis add.commute)
  also have "\<dots> \<le> eval_ztpoly A (wt s) + eval_ztpoly A (wt t)"
    using wt_ge_\<delta>\<^sub>h[OF legal] by simp
  finally have "eval_ztpoly A (coef s 0) * eval_ztpoly A (wt t) \<le> eval_ztpoly A (wt t)"
    by simp
  hence "eval_ztpoly A (coef s 0) = 1"
    using eval_ztpoly_nonneg[OF legal]
    by (metis (no_types, lifting) coef_gt_0 dual_order.order_iff_strict leD legal mult_cancel_right1
      nonneg_le_mult_right_mono_zhmset wt_gt_0)
  thus ?thesis
    using wt_s_t_le_\<delta>_t by (simp add: add.commute antisym wt_ge_\<delta>\<^sub>h[OF legal])
qed

lemma wt_App_arg_\<delta>\<^sub>h:
  assumes
    legal: "legal_zpassign A" and
    wt_st: "eval_ztpoly A (wt (App s t)) = eval_ztpoly A (wt s)"
  shows "eval_ztpoly A (wt t) = zhmset_of \<delta>\<^sub>h"
proof -
  have "eval_ztpoly A (wt (App s t)) + zhmset_of \<delta>\<^sub>h = eval_ztpoly A (wt s) + zhmset_of \<delta>\<^sub>h"
    using wt_st by simp
  hence "eval_ztpoly A (coef s 0) * eval_ztpoly A (wt t) \<le> zhmset_of \<delta>\<^sub>h" (is "?k * ?w \<le> _")
    by (metis add_le_cancel_left wt_App_plus_\<delta>\<^sub>h_ge)
  hence "?k * ?w = zhmset_of \<delta>\<^sub>h"
    using wt_ge_\<delta>\<^sub>h[OF legal] coef_gt_0[OF legal, unfolded zero_less_iff_1_le_hmset]
    by (simp add: antisym nonneg_le_mult_right_mono_zhmset)
  hence "?w \<le> zhmset_of \<delta>\<^sub>h"
    by (metis coef_gt_0[OF legal] dual_order.order_iff_strict eval_ztpoly_nonneg[OF legal]
      nonneg_le_mult_right_mono_zhmset)
  thus ?thesis
    by (simp add: antisym wt_ge_\<delta>\<^sub>h[OF legal])
qed

lemma wt_App_ge_fun: "wt (App s t) \<ge>\<^sub>p wt s"
  unfolding ge_tpoly_def
proof clarify
  fix A
  assume legal: "legal_zpassign A"

  have "zhmset_of \<delta>\<^sub>h \<le> eval_ztpoly A (coef s 0) * eval_ztpoly A (wt t)"
    by (simp add: coef_gt_0 legal nonneg_le_mult_right_mono_zhmset wt_ge_\<delta>\<^sub>h)
  hence "eval_ztpoly A (wt s) + zhmset_of \<delta>\<^sub>h \<le> eval_ztpoly A (wt (App s t)) + zhmset_of \<delta>\<^sub>h"
    by (metis add_le_cancel_right add_less_le_mono not_le wt_App_plus_\<delta>\<^sub>h_ge)
  thus "eval_ztpoly A (wt s) \<le> eval_ztpoly A (wt (App s t))"
    by simp
qed

lemma wt_App_ge_arg: "wt (App s t) \<ge>\<^sub>p wt t"
  unfolding ge_tpoly_def
  by (cases s rule: tm_exhaust_apps, simp, unfold App_apps wt.simps)
    (auto simp: comp_def coef_hd_gt_0 eval_ztpoly_nonneg nonneg_le_mult_right_mono_zhmset
       intro!: sum_list_nonneg eval_ztpoly_nonneg add_increasing)

lemma wt_\<delta>\<^sub>h_imp_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h:
  assumes
    legal: "legal_zpassign A" and
    wt_s_eq_\<delta>: "eval_ztpoly A (wt s) = zhmset_of \<delta>\<^sub>h"
  shows "\<delta>\<^sub>h = \<epsilon>\<^sub>h"
  using \<delta>\<^sub>h_le_\<epsilon>\<^sub>h wt_ge_\<epsilon>\<^sub>h[OF legal, of s, unfolded wt_s_eq_\<delta> zhmset_of_le] by (rule antisym)

lemma wt_ge_vars: "wt t \<ge>\<^sub>p wt s \<Longrightarrow> vars t \<supseteq> vars s"
proof (induct s)
  case t: (Hd \<zeta>)
  note wt_ge_\<zeta> = this(1)
  show ?case
  proof (cases \<zeta>)
    case \<zeta>: (Var x)

    {
      assume z_ni_t: "x \<notin> vars t"

      let ?A = min_zpassign
      let ?B = "\<lambda>v. if v = PWt x then eval_ztpoly ?A (wt t) + ?A v + 1 else ?A v"

      have legal_B: "legal_zpassign ?B"
        unfolding legal_zpassign_def
        by (auto simp: legal_min_zpassign intro!: add_increasing eval_ztpoly_nonneg)

      have eval_B_eq_A: "eval_ztpoly ?B (wt t) = eval_ztpoly ?A (wt t)"
        by (rule wt_cong) (auto simp: z_ni_t)
      have "eval_ztpoly ?B (wt (Hd (Var x))) > eval_ztpoly ?B (wt t)"
        by (auto simp: eval_B_eq_A zero_less_iff_1_le_zhmset zhmset_of_plus[symmetric]
          algebra_simps)
      hence False
        using wt_ge_\<zeta> \<zeta> unfolding ge_tpoly_def
        by (blast dest: leD intro: legal_B legal_min_zpassign)
    }
    thus ?thesis
      by (auto simp: \<zeta>)
  qed simp
next
  case (App s1 s2)
  note ih1 = this(1) and ih2 = this(2) and wt_t_ge_wt_s1s2 = this(3)

  have "vars s1 \<subseteq> vars t"
    using ih1 wt_t_ge_wt_s1s2 wt_App_ge_fun order_trans unfolding ge_tpoly_def by blast
  moreover have "vars s2 \<subseteq> vars t"
    using ih2 wt_t_ge_wt_s1s2 wt_App_ge_arg order_trans unfolding ge_tpoly_def by blast
  ultimately show ?case
    by simp
qed

lemma sum_coefs_ge_num_args_if_\<delta>\<^sub>h_eq_0:
  assumes
    legal: "legal_passign A" and
    \<delta>_eq_0: "\<delta>\<^sub>h = 0" and
    wary_s: "wary s"
  shows "sum_coefs (eval_tpoly A (wt s)) \<ge> num_args s"
proof (cases s rule: tm_exhaust_apps)
  case s: (apps \<zeta> ss)
  show ?thesis
    unfolding s
  proof (induct ss rule: rev_induct)
    case (snoc sa ss)
    note ih = this

    let ?Az = "\<lambda>v. zhmset_of (A v)"

    have legalz: "legal_zpassign ?Az"
      using legal unfolding legal_passign_def legal_zpassign_def zhmset_of_le by assumption

    have "eval_ztpoly ?Az (coef_hd \<zeta> (length ss)) > 0"
      using legal coef_hd_gt_0 eval_tpoly_eq_eval_ztpoly
      by (simp add: coef_hd_gt_0[OF legalz])
    hence k: "eval_tpoly A (coef_hd \<zeta> (length ss)) > 0" (is "?k > _")
      unfolding eval_tpoly_eq_eval_ztpoly[symmetric] zhmset_of_less[symmetric] zhmset_of_0
      by assumption

    have "eval_ztpoly ?Az (wt sa) > 0" (is "?w > _")
      by (simp add: wt_gt_0[OF legalz])
    hence w: "eval_tpoly A (wt sa) > 0" (is "?w > _")
      unfolding eval_tpoly_eq_eval_ztpoly[symmetric] zhmset_of_less[symmetric] zhmset_of_0
      by assumption

    have "?k * ?w > 0"
      using k w by simp
    hence "sum_coefs (?k * ?w) > 0"
      by (rule sum_coefs_gt_0[THEN iffD2])
    thus ?case
      using ih by (simp del: apps_append add: s \<delta>_eq_0)
  qed simp
qed


subsection \<open>Inductive Definitions\<close>

inductive gt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t" 50) where
  gt_wt: "wt t >\<^sub>p wt s \<Longrightarrow> t >\<^sub>t s"
| gt_unary: "wt t \<ge>\<^sub>p wt s \<Longrightarrow> \<not> head t \<le>\<ge>\<^sub>h\<^sub>d head s \<Longrightarrow> num_args t = 1 \<Longrightarrow>
    (\<exists>f \<in> ground_heads (head t). arity_sym f = 1 \<and> wt_sym f = 0) \<Longrightarrow> arg t >\<^sub>t s \<or> arg t = s \<Longrightarrow>
    t >\<^sub>t s"
| gt_diff: "wt t \<ge>\<^sub>p wt s \<Longrightarrow> head t >\<^sub>h\<^sub>d head s \<Longrightarrow> t >\<^sub>t s"
| gt_same: "wt t \<ge>\<^sub>p wt s \<Longrightarrow> head t = head s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)) \<Longrightarrow> t >\<^sub>t s"

abbreviation ge :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix "\<ge>\<^sub>t" 50) where
  "t \<ge>\<^sub>t s \<equiv> t >\<^sub>t s \<or> t = s"

inductive gt_wt :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_wtI: "wt t >\<^sub>p wt s \<Longrightarrow> gt_wt t s"

inductive gt_unary :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_unaryI: "wt t \<ge>\<^sub>p wt s \<Longrightarrow> \<not> head t \<le>\<ge>\<^sub>h\<^sub>d head s \<Longrightarrow> num_args t = 1 \<Longrightarrow>
    (\<exists>f \<in> ground_heads (head t). arity_sym f = 1 \<and> wt_sym f = 0) \<Longrightarrow> arg t \<ge>\<^sub>t s \<Longrightarrow> gt_unary t s"

inductive gt_diff :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_diffI: "wt t \<ge>\<^sub>p wt s \<Longrightarrow> head t >\<^sub>h\<^sub>d head s \<Longrightarrow> gt_diff t s"

inductive gt_same :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" where
  gt_sameI: "wt t \<ge>\<^sub>p wt s \<Longrightarrow> head t = head s \<Longrightarrow>
    (\<forall>f \<in> ground_heads (head t). extf f (>\<^sub>t) (args t) (args s)) \<Longrightarrow> gt_same t s"

lemma gt_iff_wt_unary_diff_same: "t >\<^sub>t s \<longleftrightarrow> gt_wt t s \<or> gt_unary t s \<or> gt_diff t s \<or> gt_same t s"
  by (subst gt.simps) (auto simp: gt_wt.simps gt_unary.simps gt_diff.simps gt_same.simps)

lemma gt_imp_wt: "t >\<^sub>t s \<Longrightarrow> wt t \<ge>\<^sub>p wt s"
  by (blast elim: gt.cases)

lemma gt_imp_vars: "t >\<^sub>t s \<Longrightarrow> vars t \<supseteq> vars s"
  by (erule wt_ge_vars[OF gt_imp_wt])


subsection \<open>Irreflexivity\<close>

theorem gt_irrefl: "wary s \<Longrightarrow> \<not> s >\<^sub>t s"
proof (induct "size s" arbitrary: s rule: less_induct)
  case less
  note ih = this(1) and wary_s = this(2)

  show ?case
  proof
    assume s_gt_s: "s >\<^sub>t s"
    show False
      using s_gt_s
    proof (cases rule: gt.cases)
      case gt_same
      then obtain f where f: "extf f (>\<^sub>t) (args s) (args s)"
        by fastforce
      thus False
        using wary_s ih by (metis wary_args extf_irrefl size_in_args)
    qed (auto simp: comp_hd_def gt_tpoly_irrefl gt_hd_irrefl)
  qed
qed


subsection \<open>Transitivity\<close>

lemma not_extf_gt_nil_singleton_if_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h:
  assumes wary_s: "wary s" and \<delta>_eq_\<epsilon>: "\<delta>\<^sub>h = \<epsilon>\<^sub>h"
  shows "\<not> extf f (>\<^sub>t) [] [s]"
proof
  assume nil_gt_s: "extf f (>\<^sub>t) [] [s]"
  note s_gt_nil = extf_singleton_nil_if_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h[OF \<delta>_eq_\<epsilon>, of f gt s]
  have "\<not> extf f (>\<^sub>t) [] []"
    by (rule extf_irrefl) simp
  moreover have "extf f (>\<^sub>t) [] []"
    using extf_trans_from_irrefl[of "{s}", OF _ _ _ _ _ _ nil_gt_s s_gt_nil] gt_irrefl[OF wary_s]
    by fastforce
  ultimately show False
    by sat
qed

lemma gt_sub_arg: "wary (App s t) \<Longrightarrow> App s t >\<^sub>t t"
proof (induct t arbitrary: s rule: measure_induct_rule[of size])
  case (less t)
  note ih = this(1) and wary_st = this(2)

  {
    fix A
    assume
      legal: "legal_zpassign A" and
      wt_st: "eval_ztpoly A (wt (App s t)) = eval_ztpoly A (wt t)"

    have \<delta>_eq_\<epsilon>: "\<delta>\<^sub>h = \<epsilon>\<^sub>h"
      using wt_App_fun_\<delta>\<^sub>h[OF legal] wt_\<delta>\<^sub>h_imp_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h[OF legal] wt_st by blast
    hence \<delta>_gt_0: "\<delta>\<^sub>h > 0"
      using \<epsilon>\<^sub>h_gt_0 by simp

    have wt_s: "eval_ztpoly A (wt s) = zhmset_of \<delta>\<^sub>h"
      by (rule wt_App_fun_\<delta>\<^sub>h[OF legal wt_st])

    have wary_t: "wary t"
      by (rule wary_AppE\<^sub>h[OF wary_st])
    have nargs_lt: "of_nat (num_args s) < arity_hd\<^sub>h (head s)"
      by (rule wary_AppE\<^sub>h[OF wary_st])

    have ary_hd_s: "arity_hd\<^sub>h (head s) = 1"
      by (metis gr_implies_not_zero_hmset legal lt_1_iff_eq_0_hmset nargs_lt neq_iff
        wt_gt_\<delta>\<^sub>h_if_superunary wt_s)
    hence nargs_s: "num_args s = 0"
      by (metis less_one nargs_lt of_nat_1 of_nat_less_hmset)
    hence s_eq_hd: "s = Hd (head s)"
      by (simp add: Hd_head_id)
    obtain f where
      f_in: "f \<in> ground_heads (head s)" and
      wt_f_etc: "wt_sym f + \<delta>\<^sub>h * arity_sym\<^sub>h f = \<delta>\<^sub>h"
    proof -
      assume a: "\<And>f. \<lbrakk>f \<in> local.ground_heads (head s); wt_sym f + \<delta>\<^sub>h * arity_sym\<^sub>h f = \<delta>\<^sub>h\<rbrakk> \<Longrightarrow> thesis"
      have "\<And>f. \<delta>\<^sub>h - \<delta>\<^sub>h * arity_sym\<^sub>h f \<le> wt_sym f"
        using wt_s by (metis legal wt_\<delta>\<^sub>h_imp_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h wt_sym_ge\<^sub>h)
      hence "\<And>s. \<not> \<delta>\<^sub>h * arity_sym\<^sub>h s + wt_sym s < \<delta>\<^sub>h"
        by (metis add_diff_cancel_left' le_imp_minus_plus_hmset leD le_minus_plus_same_hmset
            less_le_trans)
      thus thesis
        using a wt_s s_eq_hd
        by (metis exists_wt_sym legal add.commute order.not_eq_order_implies_strict zhmset_of_le)
    qed

    have ary_f_1: "arity_sym f = 1"
      by (metis \<delta>_gt_0 add_diff_cancel_left' ary_hd_s diff_le_self_hmset dual_order.order_iff_strict
        f_in ground_heads_arity\<^sub>h gt_0_lt_mult_gt_1_hmset hmset_of_enat_1 hmset_of_enat_inject leD
        wt_f_etc)
    hence wt_f_0: "wt_sym f = 0"
      using wt_f_etc by simp

    {
      assume hd_s_ncmp_t: "\<not> head s \<le>\<ge>\<^sub>h\<^sub>d head t"
      have ?case
        by (rule gt_unary[OF wt_App_ge_arg])
          (auto simp: hd_s_ncmp_t nargs_s intro: f_in ary_f_1 wt_f_0)
    }
    moreover
    {
      assume hd_s_gt_t: "head s >\<^sub>h\<^sub>d head t"
      have ?case
        by (rule gt_diff[OF wt_App_ge_arg]) (simp add: hd_s_gt_t)
    }
    moreover
    {
      assume "head t >\<^sub>h\<^sub>d head s"
      hence False
        using ary_f_1 wt_f_0 f_in gt_hd_irrefl gt_sym_antisym unary_wt_sym_0_gt\<^sub>h hmset_of_enat_1
        unfolding gt_hd_def by metis
    }
    moreover
    {
      assume hd_t_eq_s: "head t = head s"
      hence nargs_t_le: "num_args t \<le> 1"
        using ary_hd_s wary_num_args_le_arity_head\<^sub>h[OF wary_t] of_nat_le_hmset by fastforce

      have extf: "extf f (>\<^sub>t) [t] (args t)" for f
      proof (cases "args t")
        case Nil
        thus ?thesis
          by (simp add: extf_singleton_nil_if_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h[OF \<delta>_eq_\<epsilon>])
      next
        case args_t: (Cons ta ts)
        hence ts: "ts = []"
          using ary_hd_s[folded hd_t_eq_s] wary_num_args_le_arity_head\<^sub>h[OF wary_t] of_nat_le_hmset
            nargs_t_le by simp
        have ta: "ta = arg t"
          by (metis apps.simps(1) apps.simps(2) args_t tm.sel(6) tm_collapse_apps ts)
        hence t: "t = App (fun t) ta"
          by (metis args.simps(1) args_t not_Cons_self2 tm.exhaust_sel ts)
        have "t >\<^sub>t ta"
          by (rule ih[of ta "fun t", folded t, OF _ wary_t]) (metis ta size_arg_lt t tm.disc(2))
        thus ?thesis
          unfolding args_t ts by (metis extf_singleton gt_irrefl wary_t)
      qed
      have ?case
        by (rule gt_same[OF wt_App_ge_arg])
          (simp_all add: hd_t_eq_s length_0_conv[THEN iffD1, OF nargs_s] extf)
    }
    ultimately have ?case
      unfolding comp_hd_def by metis
  }
  thus ?case
    using gt_wt by (metis ge_tpoly_def gt_tpoly_def wt_App_ge_arg order.not_eq_order_implies_strict)
qed

lemma gt_arg: "wary s \<Longrightarrow> is_App s \<Longrightarrow> s >\<^sub>t arg s"
  by (cases s) (auto intro: gt_sub_arg)

theorem gt_trans: "wary u \<Longrightarrow> wary t \<Longrightarrow> wary s \<Longrightarrow> u >\<^sub>t t \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> u >\<^sub>t s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(u, t, s). {#size u, size t, size s#}"
        "\<lambda>(u, t, s). wary u \<longrightarrow> wary t \<longrightarrow> wary s \<longrightarrow> u >\<^sub>t t \<longrightarrow> t >\<^sub>t s \<longrightarrow> u >\<^sub>t s" "(u, t, s)",
      simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix u t s
  assume
    ih: "\<And>ua ta sa. {#size ua, size ta, size sa#} < {#size u, size t, size s#} \<Longrightarrow>
      wary ua \<Longrightarrow> wary ta \<Longrightarrow> wary sa \<Longrightarrow> ua >\<^sub>t ta \<Longrightarrow> ta >\<^sub>t sa \<Longrightarrow> ua >\<^sub>t sa" and
    wary_u: "wary u" and wary_t: "wary t" and wary_s: "wary s" and
    u_gt_t: "u >\<^sub>t t" and t_gt_s: "t >\<^sub>t s"

  have wt_u_ge_t: "wt u \<ge>\<^sub>p wt t" and wt_t_ge_s: "wt t \<ge>\<^sub>p wt s"
    using gt_imp_wt u_gt_t t_gt_s by auto
  hence wt_u_ge_s: "wt u \<ge>\<^sub>p wt s"
    by (rule ge_ge_tpoly_trans)

  have wary_arg_u: "wary (arg u)"
    by (rule wary_arg[OF wary_u])
  have wary_arg_t: "wary (arg t)"
    by (rule wary_arg[OF wary_t])
  have wary_arg_s: "wary (arg s)"
    by (rule wary_arg[OF wary_s])

  show "u >\<^sub>t s"
    using t_gt_s
  proof cases
    case gt_wt_t_s: gt_wt
    hence "wt u >\<^sub>p wt s"
      using wt_u_ge_t ge_gt_tpoly_trans by blast
    thus ?thesis
      by (rule gt_wt)
  next
    case gt_unary_t_s: gt_unary

    have t_app: "is_App t"
      by (metis args_Nil_iff_is_Hd gt_unary_t_s(3) length_greater_0_conv less_numeral_extra(1))
    hence nargs_fun_t: "num_args (fun t) < arity_hd (head (fun t))"
      by (metis tm.collapse(2) wary_AppE wary_t)

    have \<delta>_eq_\<epsilon>: "\<delta>\<^sub>h = \<epsilon>\<^sub>h"
      using gt_unary_t_s(4) unary_wt_sym_0_imp_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h by blast

    show ?thesis
      using u_gt_t
    proof cases
      case gt_wt_u_t: gt_wt
      hence "wt u >\<^sub>p wt s"
        using wt_t_ge_s gt_ge_tpoly_trans by blast
      thus ?thesis
        by (rule gt_wt)
    next
      case gt_unary_u_t: gt_unary
      have u_app: "is_App u"
        by (metis args_Nil_iff_is_Hd gt_unary_u_t(3) length_greater_0_conv less_numeral_extra(1))
      hence nargs_fun_u: "num_args (fun u) = 0"
        by (metis args.simps(1) gt_unary_u_t(3) list.size(3) one_arg_imp_Hd tm.collapse(2))

      have arg_u_gt_s: "arg u >\<^sub>t s"
        using ih[of "arg u" t s] u_app gt_unary_u_t(5) t_gt_s size_arg_lt wary_arg_u wary_s wary_t
        by force
      hence arg_u_ge_s: "arg u \<ge>\<^sub>t s"
        by sat

      {
        assume "size (arg u) < size t"
        hence "{#size u, size (arg u), size s#} < {#size u, size t, size s#}"
          by simp
        hence ?thesis
          using ih[of u "arg u" s] arg_u_gt_s gt_arg u_app wary_s wary_u by blast
      }
      moreover
      {
        assume "size (arg t) < size s"
        hence "u >\<^sub>t arg t"
          using ih[of u t "arg t"] args_Nil_iff_is_Hd gt_arg gt_unary_t_s(3) u_gt_t wary_t wary_u
          by force
        hence ?thesis
          using ih[of u "arg t" s] args_Nil_iff_is_Hd gt_unary_t_s(3,5) size_arg_lt wary_arg_t
            wary_s wary_u by force
      }
      moreover
      {
        assume sz_u_gt_t: "size u > size t" and sz_t_gt_s: "size t > size s"

        {
          assume hd_u_eq_s: "head u = head s"
          hence ary_hd_s: "arity_hd (head s) = 1"
            using ground_heads_arity gt_unary_u_t(3,4) hd_u_eq_s one_enat_def
              wary_num_args_le_arity_head wary_u by fastforce

          have extf: "extf f (>\<^sub>t) (args u) (args s)" for f
          proof (cases "args s")
            case Nil
            thus ?thesis
              by (metis \<delta>_eq_\<epsilon> args.elims args_Nil_iff_is_Hd extf_snoc_if_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h length_0_conv
                nargs_fun_u tm.sel(4) u_app)
          next
            case args_s: (Cons sa ss)
            hence ss: "ss = []"
              by (cases s, simp, metis One_nat_def antisym_conv ary_hd_s diff_Suc_1
                enat_ord_simps(1) le_add2 length_0_conv length_Cons list.size(4) one_enat_def
                wary_num_args_le_arity_head wary_s)
            have sa: "sa = arg s"
              by (metis apps.simps(1) apps.simps(2) args_s tm.sel(6) tm_collapse_apps ss)

            have s_app: "is_App s"
              using args_Nil_iff_is_Hd args_s by force
            have args_u: "args u = [arg u]"
              by (metis append_Nil args.simps(2) args_Nil_iff_is_Hd gt_unary_u_t(3) length_0_conv
                nargs_fun_u tm.collapse(2) zero_neq_one)

            have max_sz_arg_u_t_arg_t: "Max {size (arg t), size t, size (arg u)} < size u"
              using size_arg_lt sz_u_gt_t t_app u_app by fastforce

            have "{#size (arg u), size t, size (arg t)#} < {#size u, size t, size s#}"
              using max_sz_arg_u_t_arg_t by (auto intro!: Max_lt_imp_lt_mset)
            hence arg_u_gt_arg_t: "arg u >\<^sub>t arg t"
              using ih[OF _ wary_arg_u wary_t wary_arg_t] args_Nil_iff_is_Hd gt_arg
                gt_unary_t_s(3) gt_unary_u_t(5) wary_t by force

            have max_sz_arg_s_s_arg_t: "Max {size (arg s), size s, size (arg t)} < size u"
              using s_app t_app size_arg_lt sz_t_gt_s sz_u_gt_t by force

            have "{#size (arg t), size s, size (arg s)#} < {#size u, size t, size s#}"
              using max_sz_arg_s_s_arg_t by (auto intro!: Max_lt_imp_lt_mset)
            hence arg_t_gt_arg_s: "arg t >\<^sub>t arg s"
              using ih[OF _ wary_arg_t wary_s wary_arg_s]
                gt_unary_t_s(5) gt_arg args_Nil_iff_is_Hd args_s wary_s by force

            have "{#size (arg u), size (arg t), size (arg s)#} < {#size u, size t, size s#}"
              by (auto intro!: add_mset_lt_lt_lt simp: size_arg_lt u_app t_app s_app)
            hence "arg u >\<^sub>t arg s"
              using ih[of "arg u" "arg t" "arg s"] arg_u_gt_arg_t arg_t_gt_arg_s wary_arg_s
                wary_arg_t wary_arg_u by blast
            thus ?thesis
              unfolding args_u args_s ss sa by (metis extf_singleton gt_irrefl wary_arg_u)
          qed

          have ?thesis
            by (rule gt_same[OF wt_u_ge_s hd_u_eq_s]) (simp add: extf)
        }
        moreover
        {
          assume "head u >\<^sub>h\<^sub>d head s"
          hence ?thesis
            by (rule gt_diff[OF wt_u_ge_s])
        }
        moreover
        {
          assume "head s >\<^sub>h\<^sub>d head u"
          hence False
            using gt_hd_def gt_hd_irrefl gt_sym_antisym gt_unary_u_t(4) unary_wt_sym_0_gt by blast
        }
        moreover
        {
          assume "\<not> head u \<le>\<ge>\<^sub>h\<^sub>d head s"
          hence ?thesis
            by (rule gt_unary[OF wt_u_ge_s _ gt_unary_u_t(3,4) arg_u_ge_s])
        }
        ultimately have ?thesis
          unfolding comp_hd_def by sat
      }
      ultimately show ?thesis
        by (meson less_le_trans linorder_not_le size_arg_lt t_app u_app)
    next
      case gt_diff_u_t: gt_diff
      have False
        using gt_diff_u_t(2) gt_hd_def gt_hd_irrefl gt_sym_antisym gt_unary_t_s(4) unary_wt_sym_0_gt
        by blast
      thus ?thesis
        by sat
    next
      case gt_same_u_t: gt_same

      have hd_u_ncomp_s: "\<not> head u \<le>\<ge>\<^sub>h\<^sub>d head s"
        by (rule gt_unary_t_s(2)[folded gt_same_u_t(2)])

      have "\<exists>f \<in> ground_heads (head u). arity_sym f = 1 \<and> wt_sym f = 0"
        by (rule gt_unary_t_s(4)[folded gt_same_u_t(2)])
      hence "arity_hd (head u) = 1"
        by (metis dual_order.order_iff_strict gr_implies_not_zero_hmset ground_heads_arity
          gt_same_u_t(2) head_fun hmset_of_enat_1 hmset_of_enat_less lt_1_iff_eq_0_hmset
          nargs_fun_t)
      hence "num_args u \<le> 1"
        using of_nat_le_hmset wary_num_args_le_arity_head\<^sub>h wary_u by fastforce
      hence nargs_u: "num_args u = 1"
        by (cases "args u",
          metis Hd_head_id \<delta>_eq_\<epsilon> append_Nil args.simps(2)
            ex_in_conv[THEN iffD2, OF ground_heads_nonempty] gt_same_u_t(2,3) gt_unary_t_s(3)
            head_fun list.size(3) not_extf_gt_nil_singleton_if_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h one_arg_imp_Hd
            tm.collapse(2)[OF t_app] wary_arg_t,
          simp)
      hence u_app: "is_App u"
        by (cases u) auto

      have "arg u >\<^sub>t arg t"
        by (metis extf_singleton[THEN iffD1] append_Nil args.simps args_Nil_iff_is_Hd comp_hd_def
          gt_hd_def gt_irrefl gt_same_u_t(2,3) gt_unary_t_s(2,3) head_fun length_0_conv nargs_u
          one_arg_imp_Hd t_app tm.collapse(2) u_gt_t wary_u)
      moreover have "{#size (arg u), size (arg t), size s#} < {#size u, size t, size s#}"
        by (auto intro!: add_mset_lt_lt_lt simp: size_arg_lt u_app t_app)
      ultimately have "arg u >\<^sub>t s"
        using ih[OF _ wary_arg_u wary_arg_t wary_s] gt_unary_t_s(5) by blast
      hence arg_u_ge_s: "arg u \<ge>\<^sub>t s"
        by sat
      show ?thesis
        by (rule gt_unary[OF wt_u_ge_s hd_u_ncomp_s nargs_u _ arg_u_ge_s])
          (simp add: gt_same_u_t(2) gt_unary_t_s(4))
    qed
  next
    case gt_diff_t_s: gt_diff
    show ?thesis
      using u_gt_t
    proof cases
      case gt_wt_u_t: gt_wt
      hence "wt u >\<^sub>p wt s"
        using wt_t_ge_s gt_ge_tpoly_trans by blast
      thus ?thesis
        by (rule gt_wt)
    next
      case gt_unary_u_t: gt_unary
      have u_app: "is_App u"
        by (metis args_Nil_iff_is_Hd gt_unary_u_t(3) length_greater_0_conv less_numeral_extra(1))
      hence "arg u >\<^sub>t s"
        using ih[of "arg u" t s] gt_unary_u_t(5) t_gt_s size_arg_lt wary_arg_u wary_s wary_t
        by force
      hence arg_u_ge_s: "arg u \<ge>\<^sub>t s"
        by sat

      {
        assume "head u = head s"
        hence False
          using gt_diff_t_s(2) gt_unary_u_t(2) unfolding comp_hd_def by force
      }
      moreover
      {
        assume "head s >\<^sub>h\<^sub>d head u"
        hence False
          using gt_hd_def gt_hd_irrefl gt_sym_antisym gt_unary_u_t(4) unary_wt_sym_0_gt by blast
      }
      moreover
      {
        assume "head u >\<^sub>h\<^sub>d head s"
        hence ?thesis
          by (rule gt_diff[OF wt_u_ge_s])
      }
      moreover
      {
        assume "\<not> head u \<le>\<ge>\<^sub>h\<^sub>d head s"
        hence ?thesis
          by (rule gt_unary[OF wt_u_ge_s _ gt_unary_u_t(3,4) arg_u_ge_s])
      }
      ultimately show ?thesis
        unfolding comp_hd_def by sat
    next
      case gt_diff_u_t: gt_diff
      have "head u >\<^sub>h\<^sub>d head s"
        using gt_diff_u_t(2) gt_diff_t_s(2) gt_hd_trans by blast
      thus ?thesis
        by (rule gt_diff[OF wt_u_ge_s])
    next
      case gt_same_u_t: gt_same
      have "head u >\<^sub>h\<^sub>d head s"
        using gt_diff_t_s(2) gt_same_u_t(2) by simp
      thus ?thesis
        by (rule gt_diff[OF wt_u_ge_s])
    qed
  next
    case gt_same_t_s: gt_same
    show ?thesis
      using u_gt_t
    proof cases
      case gt_wt_u_t: gt_wt
      hence "wt u >\<^sub>p wt s"
        using wt_t_ge_s gt_ge_tpoly_trans by blast
      thus ?thesis
        by (rule gt_wt)
    next
      case gt_unary_u_t: gt_unary
      have "is_App u"
        by (metis args_Nil_iff_is_Hd gt_unary_u_t(3) length_greater_0_conv less_numeral_extra(1))
      hence "arg u >\<^sub>t s"
        using ih[of "arg u" t s] gt_unary_u_t(5) t_gt_s size_arg_lt wary_arg_u wary_s wary_t
        by force
      hence arg_u_ge_s: "arg u \<ge>\<^sub>t s"
        by sat

      have "\<not> head u \<le>\<ge>\<^sub>h\<^sub>d head s"
        using gt_same_t_s(2) gt_unary_u_t(2) by simp
      thus ?thesis
        by (rule gt_unary[OF wt_u_ge_s _ gt_unary_u_t(3,4) arg_u_ge_s])
    next
      case gt_diff_u_t: gt_diff
      have "head u >\<^sub>h\<^sub>d head s"
        using gt_diff_u_t(2) gt_same_t_s(2) by simp
      thus ?thesis
        by (rule gt_diff[OF wt_u_ge_s])
    next
      case gt_same_u_t: gt_same
      have hd_u_s: "head u = head s"
        by (simp only: gt_same_t_s(2) gt_same_u_t(2))

      let ?S = "set (args u) \<union> set (args t) \<union> set (args s)"

      have gt_trans_args: "\<forall>ua \<in> ?S. \<forall>ta \<in> ?S. \<forall>sa \<in> ?S. ua >\<^sub>t ta \<longrightarrow> ta >\<^sub>t sa \<longrightarrow> ua >\<^sub>t sa"
      proof clarify
        fix sa ta ua
        assume
          ua_in: "ua \<in> ?S" and ta_in: "ta \<in> ?S" and sa_in: "sa \<in> ?S" and
          ua_gt_ta: "ua >\<^sub>t ta" and ta_gt_sa: "ta >\<^sub>t sa"
        have wary_sa: "wary sa" and wary_ta: "wary ta" and wary_ua: "wary ua"
          using wary_args ua_in ta_in sa_in wary_u wary_t wary_s by blast+
        show "ua >\<^sub>t sa"
          by (auto intro!: ih[OF Max_lt_imp_lt_mset wary_ua wary_ta wary_sa ua_gt_ta ta_gt_sa])
            (meson ua_in ta_in sa_in Un_iff max.strict_coboundedI1 max.strict_coboundedI2
               size_in_args)+
      qed
      have "\<forall>f \<in> ground_heads (head u). extf f (>\<^sub>t) (args u) (args s)"
        by (clarify, rule extf_trans_from_irrefl[of ?S _ "args t", OF _ _ _ _ _ gt_trans_args])
          (auto simp: gt_same_u_t(2,3) gt_same_t_s(3) wary_args wary_u wary_t wary_s gt_irrefl)
      thus ?thesis
        by (rule gt_same[OF wt_u_ge_s hd_u_s])
    qed
  qed
qed

lemma gt_antisym: "wary s \<Longrightarrow> wary t \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> \<not> s >\<^sub>t t"
  using gt_irrefl gt_trans by blast


subsection \<open>Subterm Property\<close>

lemma gt_sub_fun: "App s t >\<^sub>t s"
proof (cases "wt (App s t) >\<^sub>p wt s")
  case True
  thus ?thesis
    using gt_wt by simp
next
  case False
  hence \<delta>_eq_\<epsilon>: "\<delta>\<^sub>h = \<epsilon>\<^sub>h"
    using wt_App_ge_fun dual_order.order_iff_strict wt_App_arg_\<delta>\<^sub>h wt_\<delta>\<^sub>h_imp_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h
    unfolding gt_tpoly_def ge_tpoly_def by fast

  have hd_st: "head (App s t) = head s"
    by auto
  have extf: "\<forall>f \<in> ground_heads (head (App s t)). extf f (>\<^sub>t) (args (App s t)) (args s)"
    by (simp add: \<delta>_eq_\<epsilon> extf_snoc_if_\<delta>\<^sub>h_eq_\<epsilon>\<^sub>h)
  show ?thesis
    by (rule gt_same[OF wt_App_ge_fun hd_st extf])
qed

theorem gt_proper_sub: "wary t \<Longrightarrow> proper_sub s t \<Longrightarrow> t >\<^sub>t s"
  by (induct t) (auto intro: gt_sub_fun gt_sub_arg gt_trans sub.intros wary_sub)


subsection \<open>Compatibility with Functions\<close>

lemma gt_compat_fun:
  assumes
    wary_t: "wary t" and
    t'_gt_t: "t' >\<^sub>t t"
  shows "App s t' >\<^sub>t App s t"
proof (rule gt_same; clarify?)
  show "wt (App s t') \<ge>\<^sub>p wt (App s t)"
    using gt_imp_wt[OF t'_gt_t, unfolded ge_tpoly_def]
    by (cases s rule: tm_exhaust_apps,
      auto simp del: apps_append simp: ge_tpoly_def App_apps eval_ztpoly_nonneg
        intro: ordered_comm_semiring_class.comm_mult_left_mono)
next
  fix f
  have "extf f (>\<^sub>t) (args s @ [t']) (args s @ [t])"
    using t'_gt_t by (metis extf_compat_list gt_irrefl[OF wary_t])
  thus "extf f (>\<^sub>t) (args (App s t')) (args (App s t))"
    by simp
qed simp

theorem gt_compat_fun_strong:
  assumes
    wary_t: "wary t" and
    t'_gt_t: "t' >\<^sub>t t"
  shows "apps s (t' # us) >\<^sub>t apps s (t # us)"
proof (induct us rule: rev_induct)
  case Nil
  show ?case
    using t'_gt_t by (auto intro!: gt_compat_fun[OF wary_t])
next
  case (snoc u us)
  note ih = snoc

  let ?v' = "apps s (t' # us @ [u])"
  let ?v = "apps s (t # us @ [u])"

  have "wt ?v' \<ge>\<^sub>p wt ?v"
    using gt_imp_wt[OF ih]
    by (cases s rule: tm_exhaust_apps,
      simp del: apps_append add: App_apps apps_append[symmetric] ge_tpoly_def,
      subst (1 2) zip_eq_butlast_last, simp+)
  moreover have "head ?v' = head ?v"
    by simp
  moreover have "\<forall>f \<in> ground_heads (head ?v'). extf f (>\<^sub>t) (args ?v') (args ?v)"
    by (metis args_apps extf_compat_list gt_irrefl[OF wary_t] t'_gt_t)
  ultimately show ?case
    by (rule gt_same)
qed


subsection \<open>Compatibility with Arguments\<close>

theorem gt_compat_arg_weak:
  assumes
    wary_st: "wary (App s t)" and
    wary_s't: "wary (App s' t)" and
    coef_s'_0_ge_s: "coef s' 0 \<ge>\<^sub>p coef s 0" and
    s'_gt_s: "s' >\<^sub>t s"
  shows "App s' t >\<^sub>t App s t"
proof -
  obtain \<zeta> ss where s: "s = apps (Hd \<zeta>) ss"
    by (metis tm_exhaust_apps)
  obtain \<zeta>' ss' where s': "s' = apps (Hd \<zeta>') ss'"
    by (metis tm_exhaust_apps)

  have len_ss_lt: "of_nat (length ss) < arity_sym\<^sub>h (min_ground_head \<zeta>)"
    using wary_st[unfolded s] ground_heads_arity\<^sub>h less_le_trans min_ground_head_in_ground_heads
    by (metis (no_types) tm_collapse_apps tm_inject_apps wary_AppE\<^sub>h)

  have \<delta>_etc:
    "\<delta>\<^sub>h + \<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss) - 1) =
     \<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss))"
    if wary: "wary (App (apps (Hd \<zeta>) ss) t)" for \<zeta> ss
  proof (cases "\<delta>\<^sub>h > 0")
    case True
    then obtain n where n: "of_nat n = arity_sym\<^sub>h (min_ground_head \<zeta>)"
      by (metis arity_sym\<^sub>h_if_\<delta>\<^sub>h_gt_0_E)

    have "of_nat (length ss) < arity_sym\<^sub>h (min_ground_head \<zeta>)"
      using wary
      by (metis (no_types) wary_AppE\<^sub>h ground_heads_arity\<^sub>h le_less_trans
        min_ground_head_in_ground_heads not_le tm_collapse_apps tm_inject_apps)
    thus ?thesis
      by (fold n, subst of_nat_1[symmetric], fold of_nat_minus_hmset, simp,
        metis Suc_diff_Suc mult_Suc_right of_nat_add of_nat_mult)
  qed simp

  have coef_\<zeta>'_ge_\<zeta>: "coef_hd \<zeta>' (length ss') \<ge>\<^sub>p coef_hd \<zeta> (length ss)"
    by (rule coef_s'_0_ge_s[unfolded s s', simplified])

  have wt_s'_ge_s: "wt s' \<ge>\<^sub>p wt s"
    by (rule gt_imp_wt[OF s'_gt_s])

  have \<zeta>_tms_len_ss_tms_wt_t_le:
    "eval_ztpoly A (coef_hd \<zeta> (length ss)) * eval_ztpoly A (wt t)
     \<le> eval_ztpoly A (coef_hd \<zeta>' (length ss')) * eval_ztpoly A (wt t)"
    if legal: "legal_zpassign A" for A
    using legal coef_\<zeta>'_ge_\<zeta>[unfolded ge_tpoly_def]
    by (simp add: eval_ztpoly_nonneg mult_right_mono)

  have wt_s't_ge_st: "wt (App s' t) \<ge>\<^sub>p wt (App s t)"
    unfolding s s'
    by (clarsimp simp del: apps_append simp: App_apps ge_tpoly_def add_ac(1)[symmetric]
          intro!: add_mono[OF _ \<zeta>_tms_len_ss_tms_wt_t_le],
      rule add_le_imp_le_left[of "zhmset_of \<delta>\<^sub>h"],
      unfold add_ac(1)[symmetric] add.commute[of 1] diff_diff_add[symmetric],
      subst (1 3) ac_simps(3)[unfolded add_ac(1)[symmetric]], subst (1 3) add_ac(1),
      simp only: zhmset_of_plus[symmetric] \<delta>_etc[OF wary_st[unfolded s]]
        \<delta>_etc[OF wary_s't[unfolded s']] add_ac(1)
        wt_s'_ge_s[unfolded s s', unfolded ge_tpoly_def add_ac(1)[symmetric], simplified])
  show ?thesis
    using s'_gt_s
  proof cases
    case gt_wt_s'_s: gt_wt

    have "wt (App s' t) >\<^sub>p wt (App s t)"
      unfolding s s'
      by (clarsimp simp del: apps_append simp: App_apps gt_tpoly_def add_ac(1)[symmetric]
            intro!: add_less_le_mono[OF _ \<zeta>_tms_len_ss_tms_wt_t_le],
        rule add_less_imp_less_left[of "zhmset_of \<delta>\<^sub>h"],
        unfold add_ac(1)[symmetric] add.commute[of 1] diff_diff_add[symmetric],
        subst (1 3) ac_simps(3)[unfolded add_ac(1)[symmetric]],
        subst (1 3) add_ac(1),
        simp only: zhmset_of_plus[symmetric] \<delta>_etc[OF wary_st[unfolded s]]
          \<delta>_etc[OF wary_s't[unfolded s']] add_ac(1)
          gt_wt_s'_s[unfolded s s', unfolded gt_tpoly_def add_ac(1)[symmetric], simplified])
    thus ?thesis
      by (rule gt_wt)
  next
    case gt_unary_s'_s: gt_unary
    have False
      by (metis ground_heads_arity\<^sub>h gt_unary_s'_s(3) gt_unary_s'_s(4) hmset_of_enat_1 leD of_nat_1
        wary_AppE\<^sub>h wary_s't)
    thus ?thesis
      by sat
  next
    case gt_diff_s'_s: gt_diff
    show ?thesis
      by (rule gt_diff[OF wt_s't_ge_st]) (simp add: gt_diff_s'_s(2))
  next
    case gt_same_s'_s: gt_same
    have hd_s't: "head (App s' t) = head (App s t)"
      by (simp add: gt_same_s'_s(2))
    have "\<forall>f \<in> ground_heads (head (App s' t)). extf f (>\<^sub>t) (args (App s' t)) (args (App s t))"
      using gt_same_s'_s(3) by (auto intro: extf_compat_append_right)
    thus ?thesis
      by (rule gt_same[OF wt_s't_ge_st hd_s't])
  qed
qed


subsection \<open>Stability under Substitution\<close>

primrec
  subst_zpassign :: "('v \<Rightarrow> ('s, 'v) tm) \<Rightarrow> ('v pvar \<Rightarrow> zhmultiset) \<Rightarrow> 'v pvar \<Rightarrow> zhmultiset"
where
  "subst_zpassign \<rho> A (PWt x) =
   eval_ztpoly A (wt (\<rho> x)) - zhmset_of (\<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head (Var x)))"
| "subst_zpassign \<rho> A (PCoef x i) = eval_ztpoly A (coef (\<rho> x) i)"

lemma legal_subst_zpassign:
  assumes
    legal: "legal_zpassign A" and
    wary_\<rho>: "wary_subst \<rho>"
  shows "legal_zpassign (subst_zpassign \<rho> A)"
  unfolding legal_zpassign_def
proof
  fix v
  show "subst_zpassign \<rho> A v \<ge> min_zpassign v"
  proof (cases v)
    case v: (PWt x)
    obtain \<zeta> ss where \<rho>x: "\<rho> x = apps (Hd \<zeta>) ss"
      by (rule tm_exhaust_apps)

    have ghd_\<zeta>: "ground_heads \<zeta> \<subseteq> ground_heads_var x"
      using wary_\<rho>[unfolded wary_subst_def, rule_format, of x, unfolded \<rho>x] by simp

    have "zhmset_of (wt_sym (min_ground_head (Var x)) + \<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head (Var x)))
      \<le> eval_ztpoly A (wt0 \<zeta>) + zhmset_of (\<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<zeta>))"
    proof -
      have mgh_x_min:
        "zhmset_of (wt_sym (min_ground_head (Var x)) + \<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head (Var x)))
         \<le> zhmset_of (wt_sym (min_ground_head \<zeta>) + \<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<zeta>))"
        by (simp add: zmset_of_le zhmset_of_le ghd_\<zeta> min_ground_head_antimono)
      have wt_mgh_le_wt0: "zhmset_of (wt_sym (min_ground_head \<zeta>)) \<le> eval_ztpoly A (wt0 \<zeta>)"
        using wt0_ge_min_ground_head[OF legal] by blast
      show ?thesis
        by (rule order_trans[OF mgh_x_min]) (simp add: zhmset_of_plus wt_mgh_le_wt0)
    qed
    also have "\<dots> \<le> eval_ztpoly A (wt0 \<zeta>)
      + zhmset_of ((\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss)))
        + of_nat (length ss) * \<delta>\<^sub>h)"
    proof -
      have "zhmset_of (\<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head \<zeta>))
        \<le> zhmset_of (\<delta>\<^sub>h * (of_nat (length ss)
          + (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss))))"
        by (metis add.commute le_minus_plus_same_hmset mult_le_mono2_hmset zhmset_of_le)
      thus ?thesis
        by (simp add: add.commute add.left_commute distrib_left mult.commute)
    qed
    also have "\<dots> \<le> eval_ztpoly A (wt0 \<zeta>)
      + zhmset_of ((\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss)))
        + of_nat (length ss) * \<epsilon>\<^sub>h)"
      using \<delta>\<^sub>h_le_\<epsilon>\<^sub>h zhmset_of_le by auto
    also have "\<dots> \<le> eval_ztpoly A (wt0 \<zeta>)
      + zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss))) + wt_args 0 A \<zeta> ss"
      using wt_args_ge_length_times_\<epsilon>\<^sub>h[OF legal]
      by (simp add: algebra_simps zhmset_of_plus zhmset_of_times of_nat_zhmset)
    finally have wt_x_le_\<zeta>ssts:
      "zhmset_of (wt_sym (min_ground_head (Var x)) + \<delta>\<^sub>h * arity_sym\<^sub>h (min_ground_head (Var x)))
       \<le> eval_ztpoly A (wt0 \<zeta>)
         + zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<zeta>) - of_nat (length ss)))
         + wt_args 0 A \<zeta> ss"
      by assumption

    show ?thesis
      using wt_x_le_\<zeta>ssts[unfolded wt_args_def]
      by (simp add: v \<rho>x comp_def le_diff_eq add.assoc[symmetric] ZHMSet_plus[symmetric]
        zmset_of_plus[symmetric] hmsetmset_plus[symmetric] zmset_of_le)
  next
    case (PCoef x i)
    thus ?thesis
      using coef_gt_0[OF legal, unfolded zero_less_iff_1_le_hmset]
      by (simp add: zhmset_of_1 zero_less_iff_1_le_zhmset)
  qed
qed

lemma wt_subst:
  assumes
    legal: "legal_zpassign A" and
    wary_\<rho>: "wary_subst \<rho>"
  shows "wary s \<Longrightarrow> eval_ztpoly A (wt (subst \<rho> s)) = eval_ztpoly (subst_zpassign \<rho> A) (wt s)"
proof (induct s rule: tm_induct_apps)
  case (apps \<zeta> ss)
  note ih = this(1) and wary_\<zeta>ss = this(2)

  have wary_nth_ss: "\<And>i. i < length ss \<Longrightarrow> wary (ss ! i)"
    using wary_args[OF _ wary_\<zeta>ss] by force

  show ?case
  proof (cases \<zeta>)
    case \<zeta>: (Var x)
    show ?thesis
    proof (cases "\<rho> x" rule: tm_exhaust_apps)
      case \<rho>x: (apps \<xi> ts)

      have wary_\<rho>x: "wary (\<rho> x)"
        using wary_\<rho> wary_subst_def by blast

      have coef_subst: "\<And>i. eval_tpoly A (zhmset_of_tpoly (coef_hd \<xi> (i + length ts))) =
        eval_tpoly (subst_zpassign \<rho> A) (zhmset_of_tpoly (coef_hd (Var x) i))"
        by (simp add: \<rho>x)

      have tedious_ary_arith:
        "arity_sym\<^sub>h (min_ground_head (Var x))
         + (arity_sym\<^sub>h (min_ground_head \<xi>) - (of_nat (length ss) + of_nat (length ts))) =
         arity_sym\<^sub>h (min_ground_head \<xi>) - of_nat (length ts)
         + (arity_sym\<^sub>h (min_ground_head (Var x)) - of_nat (length ss))"
        if \<delta>_gt_0: "\<delta>\<^sub>h > 0"
      proof -
        obtain m where m: "of_nat m = arity_sym\<^sub>h (min_ground_head (Var x))"
          by (metis arity_sym\<^sub>h_if_\<delta>\<^sub>h_gt_0_E[OF \<delta>_gt_0])
        obtain n where n: "of_nat n = arity_sym\<^sub>h (min_ground_head \<xi>)"
          by (metis arity_sym\<^sub>h_if_\<delta>\<^sub>h_gt_0_E[OF \<delta>_gt_0])

        have "m \<ge> length ss"
          unfolding of_nat_le_hmset[symmetric] m using wary_\<zeta>ss[unfolded \<zeta>]
          by (cases rule: wary_cases_apps\<^sub>h, clarsimp,
            metis arity_hd.simps(1) enat_ile enat_ord_simps(1) ground_heads_arity
              hmset_of_enat_inject hmset_of_enat_of_nat le_trans m min_ground_head_in_ground_heads
              of_nat_eq_enat of_nat_le_hmset_of_enat_iff)
        moreover have n_ge_len_ss_ts: "n \<ge> length ss + length ts"
        proof -
          have "of_nat (length ss) + of_nat (length ts) \<le> arity_hd\<^sub>h \<zeta> + of_nat (length ts)"
            using wary_\<zeta>ss wary_cases_apps\<^sub>h by fastforce
          also have "\<dots> = arity_var\<^sub>h x + of_nat (length ts)"
            by (simp add: \<zeta>)
          also have "\<dots> \<le> arity\<^sub>h (\<rho> x) + of_nat (length ts)"
            using wary_\<rho> wary_subst_def by auto
          also have "\<dots> = arity\<^sub>h (apps (Hd \<xi>) ts) + of_nat (length ts)"
            by (simp add: \<rho>x)
          also have "\<dots> = arity_hd\<^sub>h \<xi>"
            using wary_\<rho>x[unfolded \<rho>x]
            by (cases rule: wary_cases_apps\<^sub>h, cases "arity_hd \<xi>",
              simp add: of_nat_add[symmetric] of_nat_minus_hmset[symmetric],
              metis \<delta>_gt_0 arity_hd_ne_infinity_if_\<delta>_gt_0 of_nat_0 of_nat_less_hmset)
          also have "\<dots> \<le> arity_sym\<^sub>h (min_ground_head \<xi>)"
            using ground_heads_arity\<^sub>h min_ground_head_in_ground_heads by blast
          finally show ?thesis
            unfolding of_nat_le_hmset[symmetric] n by simp
        qed
        moreover have "n \<ge> length ts"
          using n_ge_len_ss_ts by simp
        ultimately show ?thesis
          by (fold m n of_nat_add of_nat_minus_hmset, unfold of_nat_inject_hmset, fastforce)
      qed

      have "eval_tpoly A (zhmset_of_tpoly (wt (subst \<rho> (apps (Hd (Var x)) ss)))) =
        eval_tpoly A (zhmset_of_tpoly (wt0 \<xi>))
        + zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<xi>)
          - (of_nat (length ts) + of_nat (length ss))))
        + wt_args 0 A \<xi> (ts @ map (subst \<rho>) ss)"
        by (simp del: apps_append add: apps_append[symmetric] \<rho>x wt_args_def comp_def)
      also have "\<dots> = eval_tpoly A (zhmset_of_tpoly (wt0 \<xi>))
        + zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<xi>)
          - (of_nat (length ts) + of_nat (length ss))))
        + wt_args 0 A \<xi> ts + wt_args (length ts) A \<xi> (map (subst \<rho>) ss)"
        by (simp add: wt_args_def zip_append_0_upt[of ts "map (subst \<rho>) ss", simplified])
      also have "\<dots> = eval_tpoly A (zhmset_of_tpoly (wt0 \<xi>))
        + zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head \<xi>)
          - (of_nat (length ts) + of_nat (length ss))))
        + wt_args 0 A \<xi> ts + wt_args 0 (subst_zpassign \<rho> A) (Var x) ss"
        by (auto intro!: arg_cong[of _ _ sum_list] nth_map_conv
          simp: wt_args_def coef_subst add.commute zhmset_of_times ih[OF nth_mem wary_nth_ss])
      also have "\<dots> = eval_tpoly (subst_zpassign \<rho> A) (zhmset_of_tpoly (wt0 (Var x)))
        + zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h (min_ground_head (Var x)) - of_nat (length ss)))
        + wt_args 0 (subst_zpassign \<rho> A) (Var x) ss"
        by (simp add: \<rho>x wt_args_def comp_def algebra_simps ring_distribs(1)[symmetric]
              zhmset_of_times zhmset_of_plus[symmetric] zhmset_of_0[symmetric])
          (use tedious_ary_arith in fastforce)
      also have "\<dots> = eval_tpoly (subst_zpassign \<rho> A) (zhmset_of_tpoly (wt (apps (Hd (Var x)) ss)))"
        by (simp add: wt_args_def comp_def)
      finally show ?thesis
        unfolding \<zeta> by assumption
    qed
  next
    case \<zeta>: (Sym f)

    have "eval_tpoly A (zhmset_of_tpoly (wt (subst \<rho> (apps (Hd (Sym f)) ss)))) =
      zhmset_of (wt_sym f) + zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h f - of_nat (length ss)))
      + wt_args 0 A (Sym f) (map (subst \<rho>) ss)"
      by (simp add: wt_args_def comp_def)
    also have "\<dots> = zhmset_of (wt_sym f) + zhmset_of (\<delta>\<^sub>h * (arity_sym\<^sub>h f - of_nat (length ss)))
      + wt_args 0 (subst_zpassign \<rho> A) (Sym f) ss"
      by (auto simp: wt_args_def ih[OF _ wary_nth_ss] intro!: arg_cong[of _ _ sum_list]
        nth_map_conv)
    also have "\<dots> = eval_tpoly (subst_zpassign \<rho> A) (zhmset_of_tpoly (wt (apps (Hd (Sym f)) ss)))"
      by (simp add: wt_args_def comp_def)
    finally show ?thesis
      unfolding \<zeta> by assumption
  qed
qed

theorem gt_subst:
  assumes wary_\<rho>: "wary_subst \<rho>"
  shows "wary t \<Longrightarrow> wary s \<Longrightarrow> t >\<^sub>t s \<Longrightarrow> subst \<rho> t >\<^sub>t subst \<rho> s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(t, s). {#size t, size s#}"
        "\<lambda>(t, s). wary t \<longrightarrow> wary s \<longrightarrow> t >\<^sub>t s \<longrightarrow> subst \<rho> t >\<^sub>t subst \<rho> s" "(t, s)",
      simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix t s
  assume
    ih: "\<And>ta sa. {#size ta, size sa#} < {#size t, size s#} \<Longrightarrow> wary ta \<Longrightarrow> wary sa \<Longrightarrow> ta >\<^sub>t sa \<Longrightarrow>
      subst \<rho> ta >\<^sub>t subst \<rho> sa" and
    wary_t: "wary t" and wary_s: "wary s" and t_gt_s: "t >\<^sub>t s"

  show "subst \<rho> t >\<^sub>t subst \<rho> s"
    using t_gt_s
  proof cases
    case gt_wt_t_s: gt_wt

    have "wt (subst \<rho> t) >\<^sub>p wt (subst \<rho> s)"
      by (auto simp: gt_tpoly_def wary_s wary_t wt_subst[OF _ wary_\<rho>]
        intro: gt_wt_t_s[unfolded gt_tpoly_def, rule_format]
        elim: legal_subst_zpassign[OF _ wary_\<rho>])
    thus ?thesis
      by (rule gt_wt)
  next
    assume wt_t_ge_s: "wt t \<ge>\<^sub>p wt s"

    have wt_\<rho>t_ge_\<rho>s: "wt (subst \<rho> t) \<ge>\<^sub>p wt (subst \<rho> s)"
      by (auto simp: ge_tpoly_def wary_s wary_t wt_subst[OF _ wary_\<rho>]
        intro: wt_t_ge_s[unfolded ge_tpoly_def, rule_format]
        elim: legal_subst_zpassign[OF _ wary_\<rho>])

    {
      case gt_unary

      have wary_\<rho>t: "wary (subst \<rho> t)"
        by (simp add: wary_subst_wary wary_t wary_\<rho>)

      show ?thesis
      proof (cases t)
        case Hd
        hence False
          using gt_unary(3) by simp
        thus ?thesis
          by sat
      next
        case t: (App t1 t2)
        hence t2: "t2 = arg t"
          by simp
        hence wary_t2: "wary t2"
          using wary_t by blast

        show ?thesis
        proof (cases "t2 = s")
          case True
          moreover have "subst \<rho> t >\<^sub>t subst \<rho> t2"
            using gt_sub_arg wary_\<rho>t unfolding t by simp
          ultimately show ?thesis
            by simp
        next
          case t2_ne_s: False
          hence t2_gt_s: "t2 >\<^sub>t s"
            using gt_unary(5) t2 by blast

          have "subst \<rho> t2 >\<^sub>t subst \<rho> s"
            by (rule ih[OF _ wary_t2 wary_s t2_gt_s]) (simp add: t)
          thus ?thesis
            by (metis gt_sub_arg gt_trans subst.simps(2) t wary_\<rho> wary_\<rho>t wary_s wary_subst_wary
              wary_t2)
        qed
      qed
    }
    {
      case _: gt_diff
      note hd_t_gt_hd_s = this(2)

      have "head (subst \<rho> t) >\<^sub>h\<^sub>d head (subst \<rho> s)"
        by (meson hd_t_gt_hd_s wary_subst_ground_heads gt_hd_def rev_subsetD wary_\<rho>)
      thus ?thesis
        by (rule gt_diff[OF wt_\<rho>t_ge_\<rho>s])
    }
    {
      case _: gt_same
      note hd_s_eq_hd_t = this(2) and extf = this(3)

      have hd_\<rho>t: "head (subst \<rho> t) = head (subst \<rho> s)"
        by (simp add: hd_s_eq_hd_t)

      {
        fix f
        assume f_in_grs: "f \<in> ground_heads (head (subst \<rho> t))"

        let ?S = "set (args t) \<union> set (args s)"

        have extf_args_s_t: "extf f (>\<^sub>t) (args t) (args s)"
          using extf f_in_grs wary_subst_ground_heads wary_\<rho> by blast
        have "extf f (>\<^sub>t) (map (subst \<rho>) (args t)) (map (subst \<rho>) (args s))"
        proof (rule extf_map[of ?S, OF _ _ _ _ _ _ extf_args_s_t])
          show "\<forall>x \<in> ?S. \<not> subst \<rho> x >\<^sub>t subst \<rho> x"
            using gt_irrefl wary_t wary_s wary_args wary_\<rho> wary_subst_wary by fastforce
        next
          show "\<forall>z \<in> ?S. \<forall>y \<in> ?S. \<forall>x \<in> ?S. subst \<rho> z >\<^sub>t subst \<rho> y \<longrightarrow> subst \<rho> y >\<^sub>t subst \<rho> x \<longrightarrow>
            subst \<rho> z >\<^sub>t subst \<rho> x"
            using gt_trans wary_t wary_s wary_args wary_\<rho> wary_subst_wary by (metis Un_iff)
        next
          have sz_a: "\<forall>ta \<in> ?S. \<forall>sa \<in> ?S. {#size ta, size sa#} < {#size t, size s#}"
            by (fastforce intro: Max_lt_imp_lt_mset dest: size_in_args)
          show "\<forall>y \<in> ?S. \<forall>x \<in> ?S. y >\<^sub>t x \<longrightarrow> subst \<rho> y >\<^sub>t subst \<rho> x"
            using ih sz_a size_in_args wary_t wary_s wary_args wary_\<rho> wary_subst_wary by fastforce
        qed auto
        hence "extf f (>\<^sub>t) (args (subst \<rho> t)) (args (subst \<rho> s))"
          by (auto simp: hd_s_eq_hd_t intro: extf_compat_append_left)
      }
      hence "\<forall>f \<in> ground_heads (head (subst \<rho> t)).
        extf f (>\<^sub>t) (args (subst \<rho> t)) (args (subst \<rho> s))"
        by blast
      thus ?thesis
        by (rule gt_same[OF wt_\<rho>t_ge_\<rho>s hd_\<rho>t])
    }
  qed
qed


subsection \<open>Totality on Ground Terms\<close>

lemma wt_total_ground:
  assumes
    gr_t: "ground t" and
    gr_s: "ground s"
  shows "wt t >\<^sub>p wt s \<or> wt s >\<^sub>p wt t \<or> wt t =\<^sub>p wt s"
  unfolding gt_tpoly_def eq_tpoly_def
  by (subst (1 2 3) ground_eval_ztpoly_wt_eq[OF gr_t, of _ undefined],
    subst (1 2 3) ground_eval_ztpoly_wt_eq[OF gr_s, of _ undefined], auto)


theorem gt_total_ground:
  assumes extf_total: "\<And>f. ext_total (extf f)"
  shows "ground t \<Longrightarrow> ground s \<Longrightarrow> t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s"
proof (simp only: atomize_imp,
    rule measure_induct_rule[of "\<lambda>(t, s). {# size t, size s #}"
      "\<lambda>(t, s). ground t \<longrightarrow> ground s \<longrightarrow> t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s" "(t, s)", simplified prod.case],
    simp only: split_paired_all prod.case atomize_imp[symmetric])
  fix t s :: "('s, 'v) tm"
  assume
    ih: "\<And>ta sa. {# size ta, size sa #} < {# size t, size s #} \<Longrightarrow> ground ta \<Longrightarrow> ground sa \<Longrightarrow>
      ta >\<^sub>t sa \<or> sa >\<^sub>t ta \<or> ta = sa" and
    gr_t: "ground t" and gr_s: "ground s"

  let ?case = "t >\<^sub>t s \<or> s >\<^sub>t t \<or> t = s"

  {
    assume "wt t >\<^sub>p wt s"
    hence "t >\<^sub>t s"
      by (rule gt_wt)
  }
  moreover
  {
    assume "wt s >\<^sub>p wt t"
    hence "s >\<^sub>t t"
      by (rule gt_wt)
  }
  moreover
  {
    assume "wt t =\<^sub>p wt s"
    hence wt_t_ge_s: "wt t \<ge>\<^sub>p wt s" and wt_s_ge_t: "wt s \<ge>\<^sub>p wt t"
      by (simp add: eq_tpoly_def ge_tpoly_def)+

    obtain g where \<xi>: "head t = Sym g"
      by (metis ground_head[OF gr_t] hd.collapse(2))
    obtain f where \<zeta>: "head s = Sym f"
      by (metis ground_head[OF gr_s] hd.collapse(2))

    {
      assume g_gt_f: "g >\<^sub>s f"
      have "t >\<^sub>t s"
        by (rule gt_diff[OF wt_t_ge_s]) (simp add: \<xi> \<zeta> g_gt_f gt_hd_def)
    }
    moreover
    {
      assume f_gt_g: "f >\<^sub>s g"
      have "s >\<^sub>t t"
        by (rule gt_diff[OF wt_s_ge_t]) (simp add: \<xi> \<zeta> f_gt_g gt_hd_def)
    }
    moreover
    {
      assume g_eq_f: "g = f"
      hence hd_t: "head t = head s"
        using \<xi> \<zeta> by force
      note hd_s = hd_t[symmetric]

      let ?ts = "args t"
      let ?ss = "args s"

      have gr_ts: "\<forall>t \<in> set ?ts. ground t"
        using gr_t ground_args by auto
      have gr_ss: "\<forall>s \<in> set ?ss. ground s"
        using gr_s ground_args by auto

      have ?case
      proof (cases "?ts = ?ss")
        case ts_eq_ss: True
        show ?thesis
          using \<xi> \<zeta> g_eq_f ts_eq_ss by (simp add: tm_expand_apps)
      next
        case False
        hence "extf g (>\<^sub>t) ?ts ?ss \<or> extf g (>\<^sub>t) ?ss ?ts"
          using ih gr_ss gr_ts less_multiset_doubletons
            ext_total.total[OF extf_total, rule_format, of "set ?ts \<union> set ?ss" "(>\<^sub>t)" ?ts ?ss g]
          by (metis Un_commute Un_iff in_lists_iff_set size_in_args sup_ge2)
        moreover
        {
          assume extf: "extf g (>\<^sub>t) ?ts ?ss"
          have "t >\<^sub>t s"
            by (rule gt_same[OF wt_t_ge_s hd_t]) (simp add: extf \<xi>)
        }
        moreover
        {
          assume extf: "extf g (>\<^sub>t) ?ss ?ts"
          have "s >\<^sub>t t"
            by (rule gt_same[OF wt_s_ge_t hd_s]) (simp add: extf[unfolded g_eq_f] \<zeta>)
        }
        ultimately show ?thesis
          by sat
      qed
    }
    ultimately have ?case
      using gt_sym_total by blast
  }
  ultimately show ?case
    using wt_total_ground[OF gr_t gr_s] by fast
qed


subsection \<open>Well-foundedness\<close>

abbreviation gtw :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t\<^sub>w" 50) where
  "(>\<^sub>t\<^sub>w) \<equiv> \<lambda>t s. wary t \<and> wary s \<and> t >\<^sub>t s"

abbreviation gtwg :: "('s, 'v) tm \<Rightarrow> ('s, 'v) tm \<Rightarrow> bool" (infix ">\<^sub>t\<^sub>w\<^sub>g" 50) where
  "(>\<^sub>t\<^sub>w\<^sub>g) \<equiv> \<lambda>t s. ground t \<and> t >\<^sub>t\<^sub>w s"

lemma ground_gt_unary:
  assumes gr_t: "ground t"
  shows "\<not> gt_unary t s"
proof
  assume gt_unary_t_s: "gt_unary t s"
  hence "t >\<^sub>t s"
    using gt_iff_wt_unary_diff_same by blast
  hence gr_s: "ground s"
    using gr_t gt_imp_vars by blast

  have ngr_t_or_s: "\<not> ground t \<or> \<not> ground s"
    using gt_unary_t_s by cases (blast dest: ground_head not_comp_hd_imp_Var)

  show False
    using gr_t gr_s ngr_t_or_s by sat
qed

theorem gt_wf: "wfP (\<lambda>s t. t >\<^sub>t\<^sub>w s)"
proof -
  have ground_wfP: "wfP (\<lambda>s t. t >\<^sub>t\<^sub>w\<^sub>g s)"
    unfolding wfP_iff_no_inf_chain
  proof
    assume "\<exists>f. inf_chain (>\<^sub>t\<^sub>w\<^sub>g) f"
    then obtain t where t_bad: "bad (>\<^sub>t\<^sub>w\<^sub>g) t"
      unfolding inf_chain_def bad_def by blast

    let ?ff = "worst_chain (>\<^sub>t\<^sub>w\<^sub>g) (\<lambda>t s. size t > size s)"
    let ?A = min_passign

    note wf_sz = wf_app[OF wellorder_class.wf, of size, simplified]

    have ffi_ground: "\<And>i. ground (?ff i)" and ffi_wary: "\<And>i. wary (?ff i)"
      using worst_chain_bad[OF wf_sz t_bad, unfolded inf_chain_def] by fast+

    have "inf_chain (>\<^sub>t\<^sub>w\<^sub>g) ?ff"
      by (rule worst_chain_bad[OF wf_sz t_bad])
    hence bad_wt_diff_same:
      "inf_chain (\<lambda>t s. ground t \<and> (gt_wt t s \<or> gt_diff t s \<or> gt_same t s)) ?ff"
      unfolding inf_chain_def using gt_iff_wt_unary_diff_same ground_gt_unary by blast

    have wf_wt: "wf {(s, t). ground t \<and> gt_wt t s}"
      by (rule wf_subset[OF wf_app[of _ "eval_tpoly ?A \<circ> wt", OF wf_less_hmultiset]],
        simp add: gt_wt.simps gt_tpoly_def, fold zhmset_of_less,
        auto simp: legal_min_zpassign gt_wt.simps gt_tpoly_def)

    have wt_O_diff_same: "{(s, t). ground t \<and> gt_wt t s}
        O {(s, t). ground t \<and> wt t =\<^sub>p wt s \<and>  (gt_diff t s \<or> gt_same t s)}
      \<subseteq> {(s, t). ground t \<and> gt_wt t s}"
      unfolding gt_wt.simps gt_diff.simps gt_same.simps by (auto intro: ge_gt_tpoly_trans)

    have wt_diff_same_as_union:
      "{(s, t). ground t \<and> (gt_wt t s \<or> gt_diff t s \<or> gt_same t s)} =
       {(s, t). ground t \<and> gt_wt t s}
       \<union> {(s, t). ground t \<and> wt t =\<^sub>p wt s \<and> (gt_diff t s \<or> gt_same t s)}"
      using gt_ge_tpoly_trans gt_tpoly_irrefl wt_ge_vars wt_total_ground
      by (fastforce simp: gt_wt.simps gt_diff.simps gt_same.simps)

    obtain k1 where bad_diff_same:
      "inf_chain (\<lambda>t s. ground t \<and> wt t =\<^sub>p wt s \<and> (gt_diff t s \<or> gt_same t s)) (\<lambda>i. ?ff (i + k1))"
      using wf_infinite_down_chain_compatible[OF wf_wt _ wt_O_diff_same, of ?ff] bad_wt_diff_same
      unfolding inf_chain_def wt_diff_same_as_union[symmetric] by auto

    have "wf {(s, t). ground s \<and> ground t \<and> wt t =\<^sub>p wt s \<and> sym (head t) >\<^sub>s sym (head s)}"
      using gt_sym_wf unfolding wfP_def wf_iff_no_infinite_down_chain by fast
    moreover have "{(s, t). ground t \<and> wt t =\<^sub>p wt s \<and> gt_diff t s}
      \<subseteq> {(s, t). ground s \<and> ground t \<and> wt t =\<^sub>p wt s \<and> sym (head t) >\<^sub>s sym (head s)}"
    proof (clarsimp, intro conjI)
      fix s t
      assume gr_t: "ground t" and gt_diff_t_s: "gt_diff t s"
      thus gr_s: "ground s"
        using gt_iff_wt_unary_diff_same gt_imp_vars by fastforce
      show "sym (head t) >\<^sub>s sym (head s)"
        using gt_diff_t_s by cases (simp add: gt_hd_def gr_s gr_t ground_hd_in_ground_heads)
    qed
    ultimately have wf_diff: "wf {(s, t). ground t \<and> wt t =\<^sub>p wt s \<and> gt_diff t s}"
      by (rule wf_subset)

    have diff_O_same:
      "{(s, t). ground t \<and> wt t =\<^sub>p wt s \<and> gt_diff t s}
         O {(s, t). ground t \<and> wt t =\<^sub>p wt s \<and> gt_same t s}
       \<subseteq> {(s, t). ground t \<and> wt t =\<^sub>p wt s \<and> gt_diff t s}"
      unfolding gt_diff.simps gt_same.simps by (auto intro: ge_ge_tpoly_trans simp: eq_tpoly_def)

    have diff_same_as_union:
      "{(s, t). ground t \<and> wt t =\<^sub>p wt s \<and> (gt_diff t s \<or> gt_same t s)} =
       {(s, t). ground t \<and> wt t =\<^sub>p wt s \<and> gt_diff t s}
       \<union> {(s, t). ground t \<and> wt t =\<^sub>p wt s \<and> gt_same t s}"
      by auto

    obtain k2 where
      bad_same: "inf_chain (\<lambda>t s. ground t \<and> wt t =\<^sub>p wt s \<and> gt_same t s) (\<lambda>i. ?ff (i + k2))"
      using wf_infinite_down_chain_compatible[OF wf_diff _ diff_O_same, of "\<lambda>i. ?ff (i + k1)"]
        bad_diff_same
      unfolding inf_chain_def diff_same_as_union[symmetric] by (auto simp: add.assoc)
    hence hd_sym: "\<And>i. is_Sym (head (?ff (i + k2)))"
      unfolding inf_chain_def by (simp add: ground_head)

    define f where "f = sym (head (?ff k2))"
    define w where "w = eval_tpoly ?A (wt (?ff k2))"

    have "head (?ff (i + k2)) = Sym f \<and> eval_tpoly ?A (wt (?ff (i + k2))) = w" for i
    proof (induct i)
      case 0
      thus ?case
        by (auto simp: f_def w_def hd.collapse(2)[OF hd_sym, of 0, simplified])
    next
      case (Suc ia)
      thus ?case
        using bad_same unfolding inf_chain_def gt_same.simps zhmset_of_inject[symmetric]
        by (simp add: eq_tpoly_def legal_min_zpassign)
    qed
    note hd_eq_f = this[THEN conjunct1] and wt_eq_w = this[THEN conjunct2]

    define max_args where
      "max_args = (if \<delta>\<^sub>h = 0 then sum_coefs w else the_enat (arity_sym f))"

    have nargs_le_max_args: "num_args (?ff (i + k2)) \<le> max_args" for i
    proof (cases "\<delta>\<^sub>h = 0")
      case \<delta>_ne_0: False
      hence ary_f_ne_inf: "arity_sym f \<noteq> \<infinity>"
        using arity_sym_ne_infinity_if_\<delta>_gt_0 of_nat_0 by blast
      have "enat (num_args (worst_chain (\<lambda>t s. ground t \<and> t >\<^sub>t\<^sub>w s) (\<lambda>t s. size s < size t) (i + k2))) \<le> arity_sym f"
        using wary_num_args_le_arity_head[OF ffi_wary[of "i + k2"]] by (simp add: hd_eq_f)
      with \<delta>_ne_0 show ?thesis
        by (simp del: enat_ord_simps add: max_args_def  enat_ord_simps(1)[symmetric] enat_the_enat_iden[OF ary_f_ne_inf])
    next
      case \<delta>_eq_0: True
      show ?thesis
        using sum_coefs_ge_num_args_if_\<delta>\<^sub>h_eq_0[OF legal_min_passign \<delta>_eq_0 ffi_wary[of "i + k2"]]
        by (simp add: max_args_def \<delta>_eq_0 wt_eq_w)
    qed

    let ?U_of = "\<lambda>i. set (args (?ff (i + k2)))"

    define U where "U = (\<Union>i. ?U_of i)"

    have gr_u: "\<And>u. u \<in> U \<Longrightarrow> ground u"
      unfolding U_def by (blast dest: ground_args[OF _ ffi_ground])
    have wary_u: "\<And>u. u \<in> U \<Longrightarrow> wary u"
      unfolding U_def by (blast dest: wary_args[OF _ ffi_wary])

    have "\<not> bad (>\<^sub>t\<^sub>w\<^sub>g) u" if u_in: "u \<in> ?U_of i" for u i
    proof
      assume u_bad: "bad (>\<^sub>t\<^sub>w\<^sub>g) u"
      have sz_u: "size u < size (?ff (i + k2))"
        by (rule size_in_args[OF u_in])

      show False
      proof (cases "i + k2")
        case 0
        thus False
          using sz_u min_worst_chain_0[OF wf_sz u_bad] by simp
      next
        case Suc
        hence gt: "?ff (i + k2 - 1) >\<^sub>t\<^sub>w ?ff (i + k2)"
          using worst_chain_pred[OF wf_sz t_bad] by auto
        moreover have "?ff (i + k2) >\<^sub>t\<^sub>w u"
          using gt gt_proper_sub sub_args sz_u u_in wary_args by auto
        ultimately have "?ff (i + k2 - 1) >\<^sub>t\<^sub>w u"
          using gt_trans by blast
        thus False
          using Suc sz_u min_worst_chain_Suc[OF wf_sz u_bad] ffi_ground by fastforce
      qed
    qed
    hence u_good: "\<And>u. u \<in> U \<Longrightarrow> \<not> bad (>\<^sub>t\<^sub>w\<^sub>g) u"
      unfolding U_def by blast

    let ?gtwu = "\<lambda>t s. t \<in> U \<and> t >\<^sub>t\<^sub>w s"

    have gtwu_irrefl: "\<And>x. \<not> ?gtwu x x"
      using gt_irrefl by auto

    have "\<And>i j. \<forall>t \<in> set (args (?ff (i + k2))). \<forall>s \<in> set (args (?ff (j + k2))). t >\<^sub>t s \<longrightarrow>
      t \<in> U \<and> t >\<^sub>t\<^sub>w s"
      using wary_u unfolding U_def by blast
    moreover have "\<And>i. extf f (>\<^sub>t) (args (?ff (i + k2))) (args (?ff (Suc i + k2)))"
      using bad_same hd_eq_f unfolding inf_chain_def gt_same.simps by auto
    ultimately have "\<And>i. extf f ?gtwu (args (?ff (i + k2))) (args (?ff (Suc i + k2)))"
      by (rule extf_mono_strong)
    hence "inf_chain (extf f ?gtwu) (\<lambda>i. args (?ff (i + k2)))"
      unfolding inf_chain_def by blast
    hence nwf_ext:
      "\<not> wfP (\<lambda>xs ys. length ys \<le> max_args \<and> length xs \<le> max_args \<and> extf f ?gtwu ys xs)"
      unfolding inf_chain_def wfP_def wf_iff_no_infinite_down_chain using nargs_le_max_args by fast

    have gtwu_le_gtwg: "?gtwu \<le> (>\<^sub>t\<^sub>w\<^sub>g)"
      by (auto intro!: gr_u)

    have "wfP (\<lambda>s t. ?gtwu t s)"
      unfolding wfP_iff_no_inf_chain
    proof (intro notI, elim exE)
      fix f
      assume bad_f: "inf_chain ?gtwu f"
      hence bad_f0: "bad ?gtwu (f 0)"
        by (rule inf_chain_bad)
      hence "f 0 \<in> U"
        using bad_f unfolding inf_chain_def by blast
      hence "\<not> bad (>\<^sub>t\<^sub>w\<^sub>g) (f 0)"
        using u_good by blast
      hence "\<not> bad ?gtwu (f 0)"
        using bad_f inf_chain_bad inf_chain_subset[OF _ gtwu_le_gtwg] by blast
      thus False
        using bad_f0 by sat
    qed
    hence wf_ext: "wfP (\<lambda>xs ys. length ys \<le> max_args \<and> length xs \<le> max_args \<and> extf f ?gtwu ys xs)"
      using extf_wf_bounded[of ?gtwu] gtwu_irrefl by blast

    show False
      using nwf_ext wf_ext by blast
  qed

  let ?subst = "subst grounding_\<rho>"

  have "wfP (\<lambda>s t. ?subst t >\<^sub>t\<^sub>w\<^sub>g ?subst s)"
    by (rule wfP_app[OF ground_wfP])
  hence "wfP (\<lambda>s t. ?subst t >\<^sub>t\<^sub>w ?subst s)"
    by (simp add: ground_grounding_\<rho>)
  thus ?thesis
    by (auto intro: wfP_subset wary_subst_wary[OF wary_grounding_\<rho>] gt_subst[OF wary_grounding_\<rho>])
qed

end

end
