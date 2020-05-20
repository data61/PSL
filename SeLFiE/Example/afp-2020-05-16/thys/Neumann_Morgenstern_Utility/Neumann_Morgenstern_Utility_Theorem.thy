(* License: LGPL *)
(* Author: Julian Parsert *)


theory Neumann_Morgenstern_Utility_Theorem
  imports
    "HOL-Probability.Probability"
    "First_Welfare_Theorem.Utility_Functions"
    Lotteries
begin


section \<open> Properties of Preferences \<close>

subsection \<open> Independent Preferences\<close>

text \<open> Independence is sometimes called substitution \<close>


text \<open> Notice how r is "added" to the right of mix-pmf and the element to the left q/p changes \<close>
definition independent_vnm
  where
    "independent_vnm C P =
    (\<forall>p \<in> C. \<forall>q \<in> C. \<forall>r \<in> C. \<forall>(\<alpha>::real) \<in> {0<..1}. p \<succeq>[P] q \<longleftrightarrow> mix_pmf \<alpha> p r \<succeq>[P] mix_pmf \<alpha> q r)"

lemma independent_vnmI1:
  assumes "(\<forall>p \<in> C. \<forall>q \<in> C. \<forall>r \<in> C. \<forall>\<alpha> \<in> {0<..1}. p \<succeq>[P] q \<longleftrightarrow> mix_pmf \<alpha> p r \<succeq>[P] mix_pmf \<alpha> q r)"
  shows "independent_vnm C P"
  using assms independent_vnm_def by blast

lemma independent_vnmI2:
  assumes "\<And>p q r \<alpha>. p \<in> C \<Longrightarrow> q \<in> C \<Longrightarrow> r \<in> C \<Longrightarrow> \<alpha> \<in> {0<..1} \<Longrightarrow> p \<succeq>[P] q \<longleftrightarrow> mix_pmf \<alpha> p r \<succeq>[P] mix_pmf \<alpha> q r"
  shows "independent_vnm C P"
  by (rule independent_vnmI1, standard, standard, standard, 
      standard, simp add: assms) (meson assms greaterThanAtMost_iff)

lemma independent_vnm_alt_def:
  shows "independent_vnm C P \<longleftrightarrow> (\<forall>p \<in> C. \<forall>q \<in> C. \<forall>r \<in> C. \<forall>\<alpha> \<in> {0<..<1}. 
  p \<succeq>[P] q \<longleftrightarrow> mix_pmf \<alpha> p r \<succeq>[P] mix_pmf \<alpha> q r)" (is "?L \<longleftrightarrow> ?R")
proof (rule iffI)
  assume a: "?R"
  have "independent_vnm C P" 
    by(rule independent_vnmI2, simp add: a) (metis a greaterThanLessThan_iff 
        linorder_neqE_linordered_idom not_le pmf_mix_1)
  then show "?L" by auto
qed (simp add: independent_vnm_def)

lemma independece_dest_alt: 
  assumes "independent_vnm C P"
  shows "(\<forall>p \<in> C. \<forall>q \<in> C. \<forall>r \<in> C. \<forall>(\<alpha>::real) \<in> {0<..1}. p \<succeq>[P] q \<longleftrightarrow> mix_pmf \<alpha> p r \<succeq>[P] mix_pmf \<alpha> q r)"
proof (standard, standard, standard, standard)
  fix p q r \<alpha>
  assume as1: "p \<in> C" 
  assume as2: "q \<in> C"
  assume as3: "r \<in> C"
  assume as4: "(\<alpha>::real) \<in> {0<..1}"
  then show "p \<succeq>[P] q = mix_pmf \<alpha> p r \<succeq>[P] mix_pmf \<alpha> q r"
    using as1 as2 as3 assms(1) independent_vnm_def by blast
qed

lemma independent_vnmD1:
  assumes "independent_vnm C P"
  shows "(\<forall>p \<in> C. \<forall>q \<in> C. \<forall>r \<in> C. \<forall>\<alpha> \<in> {0<..1}. p \<succeq>[P] q \<longleftrightarrow> mix_pmf \<alpha> p r \<succeq>[P] mix_pmf \<alpha> q r)"
  using assms independent_vnm_def by blast

lemma independent_vnmD2:
  fixes p q r \<alpha>
  assumes "\<alpha> \<in> {0<..1}"
    and "p \<in> C"
    and "q \<in> C"
    and "r \<in> C"
  assumes "independent_vnm C P"
  assumes "p \<succeq>[P] q"
  shows "mix_pmf \<alpha> p r \<succeq>[P] mix_pmf \<alpha> q r"
  using assms independece_dest_alt  by blast

lemma independent_vnmD3:
  fixes p q r \<alpha>
  assumes "\<alpha> \<in> {0<..1}"
    and "p \<in> C"
    and "q \<in> C"
    and "r \<in> C"
  assumes "independent_vnm C P" 
  assumes "mix_pmf \<alpha> p r \<succeq>[P] mix_pmf \<alpha> q r"
  shows "p \<succeq>[P] q"
  using assms independece_dest_alt by blast

lemma independent_vnmD4:
  assumes "independent_vnm C P"
  assumes "refl_on C P"
  assumes "p \<in> C" 
    and "q \<in> C" 
    and "r \<in> C"
    and "\<alpha> \<in> {0..1}" 
    and "p \<succeq>[P] q" 
  shows "mix_pmf \<alpha> p r \<succeq>[P] mix_pmf \<alpha> q r"
  using assms
  by (cases "\<alpha> = 0 \<or> \<alpha> \<in> {0<..1}",metis assms(1,2,3,4) 
      independece_dest_alt pmf_mix_0 refl_onD, auto)

lemma approx_indep_ge:
  assumes "x \<approx>[\<R>] y"
  assumes "\<alpha> \<in> {0..(1::real)}"
  assumes rpr: "rational_preference (lotteries_on outcomes) \<R>"
    and ind: "independent_vnm (lotteries_on outcomes) \<R>"
  shows "\<forall>r \<in> lotteries_on outcomes. (mix_pmf \<alpha> y r) \<succeq>[\<R>] (mix_pmf \<alpha> x r)"
proof
  fix r
  assume a: "r \<in> lotteries_on outcomes" (is "r \<in> ?lo")
  have clct: "y \<succeq>[\<R>] x \<and> independent_vnm ?lo \<R> \<and> y \<in> ?lo \<and> x \<in> ?lo \<and> r \<in> ?lo"
    by (meson  a assms(1) assms(2) atLeastAtMost_iff greaterThanAtMost_iff 
        ind preference_def rational_preference_def rpr)
  then have in_lo: "mix_pmf \<alpha> y r \<in> ?lo" "(mix_pmf \<alpha> x r) \<in> ?lo"
    by (metis  assms(2) atLeastAtMost_iff greaterThanLessThan_iff
        less_eq_real_def mix_pmf_in_lotteries pmf_mix_0 pmf_mix_1 a)+
  have "0 = \<alpha> \<or> 0 < \<alpha>"
    using assms by auto
  then show "mix_pmf \<alpha> y r \<succeq>[\<R>] mix_pmf \<alpha> x r"
    using in_lo(2) rational_preference.compl rpr
    by (auto,blast) (meson assms(2) atLeastAtMost_iff clct
        greaterThanAtMost_iff independent_vnmD2)
qed

lemma approx_imp_approx_ind:
  assumes "x \<approx>[\<R>] y"
  assumes "\<alpha> \<in> {0..(1::real)}"
  assumes rpr: "rational_preference (lotteries_on outcomes) \<R>"
    and ind: "independent_vnm (lotteries_on outcomes) \<R>"
  shows "\<forall>r \<in> lotteries_on outcomes. (mix_pmf \<alpha> y r) \<approx>[\<R>] (mix_pmf \<alpha> x r)"
  using approx_indep_ge assms(1) assms(2) ind rpr by blast

lemma geq_imp_mix_geq_right:
  assumes "x \<succeq>[\<R>] y"
  assumes rpr: "rational_preference (lotteries_on outcomes) \<R>"
  assumes ind: "independent_vnm (lotteries_on outcomes) \<R>"
  assumes "\<alpha> \<in> {0..(1::real)}"
  shows "(mix_pmf \<alpha> x y) \<succeq>[\<R>] y"
proof -
  have xy_p: "x \<in> (lotteries_on outcomes)" "y \<in> (lotteries_on outcomes)"
    by (meson assms(1) preference.not_outside rational_preference_def rpr)
      (meson assms(1) preference_def rational_preference_def rpr)
  have "(mix_pmf \<alpha> x y) \<in> (lotteries_on outcomes)" (is "?mpf \<in> ?lot")
    using mix_pmf_in_lotteries [of x outcomes y \<alpha>] xy_p assms(2)
    by (meson approx_indep_ge assms(4) ind preference.not_outside 
        rational_preference.compl rational_preference_def)
  have all: "\<forall>r \<in> ?lot. (mix_pmf \<alpha> x r) \<succeq>[\<R>] (mix_pmf \<alpha> y r)"
    by (metis assms assms(2) atLeastAtMost_iff greaterThanAtMost_iff independece_dest_alt 
        less_eq_real_def pmf_mix_0 rational_preference.compl rpr ind xy_p)
  thus ?thesis      
    by (metis all assms(4) set_pmf_mix_eq xy_p(2))
qed

lemma geq_imp_mix_geq_left:
  assumes "x \<succeq>[\<R>] y"
  assumes rpr: "rational_preference (lotteries_on outcomes) \<R>"
  assumes ind: "independent_vnm (lotteries_on outcomes) \<R>"
  assumes "\<alpha> \<in> {0..(1::real)}"
  shows "(mix_pmf \<alpha> y x) \<succeq>[\<R>] y"
proof -
  define \<beta> where
    b: "\<beta> = 1 - \<alpha>"
  have "\<beta> \<in> {0..1}"
    using assms(4) b by auto
  then have "mix_pmf \<beta> x y \<succeq>[\<R>] y" 
    using geq_imp_mix_geq_right[OF assms] assms(1) geq_imp_mix_geq_right ind rpr by blast
  moreover have "mix_pmf \<beta> x y = mix_pmf \<alpha> y x"
    by (metis assms(4) b pmf_inverse_switch_eqals)
  ultimately show ?thesis 
    by simp
qed

lemma sg_imp_mix_sg:
  assumes "x \<succ>[\<R>] y"
  assumes rpr: "rational_preference (lotteries_on outcomes) \<R>"
  assumes ind: "independent_vnm (lotteries_on outcomes) \<R>"
  assumes "\<alpha> \<in> {0<..(1::real)}"
  shows "(mix_pmf \<alpha> x y) \<succ>[\<R>] y"
proof -
  have xy_p: "x \<in> (lotteries_on outcomes)" "y \<in> (lotteries_on outcomes)"
    by (meson assms(1) preference.not_outside rational_preference_def rpr)
      (meson assms(1) preference_def rational_preference_def rpr)
  have "(mix_pmf \<alpha> x y) \<in> (lotteries_on outcomes)" (is "?mpf \<in> ?lot")
    using mix_pmf_in_lotteries [of x outcomes y \<alpha>] xy_p assms(2)
    using assms(4) by fastforce
  have all: "\<forall>r \<in> ?lot. (mix_pmf \<alpha> x r) \<succeq>[\<R>] (mix_pmf \<alpha> y r)"
    by (metis assms(1,3,4)  independece_dest_alt ind xy_p)
  have "(mix_pmf \<alpha> x y) \<succeq>[\<R>] y"
    by (metis all assms(4) atLeastAtMost_iff greaterThanAtMost_iff 
        less_eq_real_def set_pmf_mix_eq xy_p(2))
  have all2: "\<forall>r \<in> ?lot. (mix_pmf \<alpha> x r) \<succ>[\<R>] (mix_pmf \<alpha> y r)"
    using assms(1) assms(4) ind independece_dest_alt xy_p(1) xy_p(2) by blast
  then show ?thesis 
    by (metis assms(4) atLeastAtMost_iff greaterThanAtMost_iff 
        less_eq_real_def set_pmf_mix_eq xy_p(2))
qed



subsection \<open> Continuity \<close>

text \<open> Continuity is sometimes called Archimedean Axiom\<close>
definition continuous_vnm
  where
    "continuous_vnm C P = (\<forall>p \<in> C. \<forall>q \<in> C. \<forall>r \<in> C. p \<succeq>[P] q \<and> q \<succeq>[P] r \<longrightarrow> 
    (\<exists>\<alpha> \<in> {0..1}. (mix_pmf \<alpha> p r) \<approx>[P] q))"

lemma continuous_vnmD:
  assumes "continuous_vnm C P"
  shows "(\<forall>p \<in> C. \<forall>q \<in> C. \<forall>r \<in> C. p \<succeq>[P] q \<and> q \<succeq>[P] r \<longrightarrow>
    (\<exists>\<alpha> \<in> {0..1}. (mix_pmf \<alpha> p r) \<approx>[P] q))"
  using continuous_vnm_def assms by blast

lemma continuous_vnmI:
  assumes "\<And>p q r. p \<in> C \<Longrightarrow> q \<in> C \<Longrightarrow> r \<in> C \<Longrightarrow> p \<succeq>[P] q \<and> q \<succeq>[P] r \<Longrightarrow> 
    \<exists>\<alpha> \<in> {0..1}. (mix_pmf \<alpha> p r) \<approx>[P] q"
  shows "continuous_vnm C P"
  by (simp add: assms continuous_vnm_def)

lemma mix_in_lot:
  assumes "x \<in> lotteries_on outcomes"
    and "y \<in> lotteries_on outcomes"
    and "\<alpha> \<in> {0..1}"
  shows "(mix_pmf \<alpha> x y) \<in> lotteries_on outcomes"
  using assms(1) assms(2) assms(3) less_eq_real_def mix_pmf_in_lotteries by fastforce


lemma non_unique_continuous_unfolding:
  assumes cnt: "continuous_vnm (lotteries_on outcomes) \<R>"
  assumes "rational_preference (lotteries_on outcomes) \<R>"
  assumes "p \<succeq>[\<R>] q"
    and "q \<succeq>[\<R>] r"
    and "p \<succ>[\<R>] r"
  shows "\<exists>\<alpha> \<in> {0..1}. q \<approx>[\<R>] mix_pmf \<alpha> p r"
  using assms(1) assms(2) cnt continuous_vnmD assms
proof -
  have "\<forall>p q. p\<in> (lotteries_on outcomes) \<and> q \<in> (lotteries_on outcomes) \<longleftrightarrow> p \<succeq>[\<R>] q \<or> q \<succeq>[\<R>] p"
    using assms rational_preference.compl[of "lotteries_on outcomes" \<R>]
    by (metis (no_types, hide_lams) preference_def rational_preference_def)
  then show ?thesis
    using continuous_vnmD[OF assms(1)] by (metis assms(3) assms(4))
qed


section \<open> System U start, as per vNM\<close>

text \<open> These are the first two assumptions which we use to derive the first results.
       We assume rationality and independence. In this system U the von-Neumann-Morgenstern 
        Utility Theorem is proven. \<close>
context
  fixes outcomes :: "'a set"
  fixes \<R>
  assumes rpr: "rational_preference (lotteries_on outcomes) \<R>"
  assumes ind: "independent_vnm (lotteries_on outcomes) \<R>"
begin

abbreviation "\<P> \<equiv> lotteries_on outcomes"

lemma relation_in_carrier:
  "x \<succeq>[\<R>] y \<Longrightarrow> x \<in> \<P> \<and> y \<in> \<P>"
  by (meson preference_def rational_preference_def rpr)

lemma mix_pmf_preferred_independence:
  assumes "r \<in> \<P>"
    and "\<alpha> \<in> {0..1}"
  assumes "p \<succeq>[\<R>] q"
  shows "mix_pmf \<alpha> p r \<succeq>[\<R>] mix_pmf \<alpha> q r"
  using ind by (metis relation_in_carrier antisym_conv1 assms atLeastAtMost_iff 
      greaterThanAtMost_iff independece_dest_alt pmf_mix_0 
      rational_preference.no_better_thansubset_rel rpr subsetI)

lemma mix_pmf_strict_preferred_independence:
  assumes "r \<in> \<P>"
    and "\<alpha> \<in> {0<..1}"
  assumes "p \<succ>[\<R>] q"
  shows "mix_pmf \<alpha> p r \<succ>[\<R>] mix_pmf \<alpha> q r"
  by (meson assms(1) assms(2) assms(3) ind independent_vnmD2 
      independent_vnmD3 relation_in_carrier)

lemma mix_pmf_preferred_independence_rev:
  assumes "p \<in> \<P>"
    and "q \<in> \<P>"
    and "r \<in> \<P>"
    and "\<alpha> \<in> {0<..1}"
  assumes "mix_pmf \<alpha> p r \<succeq>[\<R>] mix_pmf \<alpha> q r"
  shows "p \<succeq>[\<R>] q"
proof -
  have "mix_pmf \<alpha> p r \<in> \<P>"
    using assms mix_in_lot relation_in_carrier by blast
  moreover have "mix_pmf \<alpha> q r \<in> \<P>"
    using assms mix_in_lot assms(2) relation_in_carrier by blast
  ultimately show ?thesis 
    using ind independent_vnmD3[of \<alpha> p \<P> q r \<R>] assms by blast
qed

lemma x_sg_y_sg_mpmf_right:
  assumes "x \<succ>[\<R>] y"
  assumes "b \<in> {0<..(1::real)}"
  shows "x \<succ>[\<R>] mix_pmf b y x"
proof -
  consider "b = 1" | "b \<noteq> 1"
    by blast
  then show ?thesis 
  proof (cases)
    case 2
    have sg: "(mix_pmf b x y) \<succ>[\<R>] y"
      using assms(1) assms(2) assms ind rpr sg_imp_mix_sg "2" by fastforce
    have "mix_pmf b x y \<in> \<P>"
      by (meson sg preference_def rational_preference_def rpr)
    have "mix_pmf b x x \<in> \<P>"
      using relation_in_carrier assms(2) mix_in_lot assms by fastforce
    have "b \<in> {0<..<1}"
      using "2" assms(2)  by auto
    have "mix_pmf b x x \<succ>[\<R>] mix_pmf b y x"
      using mix_pmf_preferred_independence[of x b] assms
      by (meson \<open>b \<in> {0<..<1}\<close> greaterThanAtMost_iff greaterThanLessThan_iff ind 
          independece_dest_alt less_eq_real_def preference_def 
          rational_preference.axioms(1) relation_in_carrier rpr)
    then show ?thesis
      using mix_pmf_preferred_independence
      by (metis assms(2) atLeastAtMost_iff greaterThanAtMost_iff less_eq_real_def set_pmf_mix_eq)
  qed (simp add: assms(1))
qed

lemma neumann_3B_b:
  assumes "u \<succ>[\<R>] v"
  assumes "\<alpha> \<in> {0<..<1}"
  shows "u \<succ>[\<R>] mix_pmf \<alpha> u v"
proof -
  have *: "preorder_on \<P> \<R> \<and> rational_preference_axioms \<P> \<R>"
    by (metis (no_types) preference_def rational_preference_def rpr)
  have "1 - \<alpha> \<in> {0<..1}"
    using assms(2) by auto
  then show ?thesis
    using * assms by (metis atLeastAtMost_iff greaterThanLessThan_iff 
        less_eq_real_def pmf_inverse_switch_eqals x_sg_y_sg_mpmf_right)
qed

lemma neumann_3B_b_non_strict:
  assumes "u \<succeq>[\<R>] v"
  assumes "\<alpha> \<in> {0..1}"
  shows "u \<succeq>[\<R>] mix_pmf \<alpha> u v"
proof -
  have f2: "mix_pmf \<alpha> (u::'a pmf) v = mix_pmf (1 - \<alpha>) v u"
    using pmf_inverse_switch_eqals assms(2) by auto
  have "1 - \<alpha> \<in> {0..1}"
    using assms(2) by force
  then show ?thesis
    using f2 relation_in_carrier 
    by (metis (no_types) assms(1) mix_pmf_preferred_independence set_pmf_mix_eq)
qed

lemma greater_mix_pmf_greater_step_1_aux: 
  assumes "v \<succ>[\<R>] u"
  assumes "\<alpha> \<in> {0<..<(1::real)}"
    and "\<beta> \<in> {0<..<(1::real)}"
  assumes "\<beta> > \<alpha>"
  shows "(mix_pmf \<beta> v u) \<succ>[\<R>] (mix_pmf \<alpha> v u)"
proof -
  define t where
    t: "t = mix_pmf \<beta> v u"
  obtain \<gamma> where
    g: "\<alpha> = \<beta> * \<gamma>"
    by (metis assms(2) assms(4) greaterThanLessThan_iff 
        mult.commute nonzero_eq_divide_eq not_less_iff_gr_or_eq)
  have g1: "\<gamma> > 0 \<and> \<gamma> < 1"
    by (metis (full_types) assms(2) assms(4) g greaterThanLessThan_iff 
        less_trans mult.right_neutral mult_less_cancel_left_pos not_le 
        sgn_le_0_iff sgn_pos zero_le_one zero_le_sgn_iff zero_less_mult_iff)
  have t_in: "mix_pmf \<beta> v u \<in> \<P>"
    by (meson assms(1) assms(3) mix_pmf_in_lotteries preference_def rational_preference_def rpr)
  have "v \<succ>[\<R>] mix_pmf (1 - \<beta>) v u"
    using x_sg_y_sg_mpmf_right[of u v "1-\<beta>"] assms
    by (metis atLeastAtMost_iff greaterThanAtMost_iff greaterThanLessThan_iff 
        less_eq_real_def pmf_inverse_switch_eqals x_sg_y_sg_mpmf_right)
  have "t \<succ>[\<R>] u"
    using assms(1) assms(3) ind rpr sg_imp_mix_sg t by fastforce
  hence t_s: "t \<succ>[\<R>] (mix_pmf \<gamma> t u)" 
  proof -
    have "(mix_pmf \<gamma> t u) \<in> \<P>"
      by (metis assms(1) assms(3) atLeastAtMost_iff g1 mix_in_lot mix_pmf_in_lotteries 
          not_less order.asym preference_def rational_preference_def rpr t)
    have "t \<succ>[\<R>] mix_pmf \<gamma> (mix_pmf \<beta> v u) u"
      using neumann_3B_b[of t u \<gamma>] assms t g1
      by (meson greaterThanAtMost_iff greaterThanLessThan_iff 
          ind less_eq_real_def rpr sg_imp_mix_sg)
    thus ?thesis
      using t by blast
  qed
  from product_mix_pmf_prob_distrib[of _ \<beta> v u] assms
  have "mix_pmf \<beta> v u \<succ>[\<R>] mix_pmf \<alpha> v u"
    by (metis t_s atLeastAtMost_iff g g1 greaterThanLessThan_iff less_eq_real_def mult.commute t)
  then show ?thesis by blast
qed

section \<open> This lemma is in called step 1 in literature. 
In Von Neumann and Morgenstern's book this is A:A (albeit more general) \<close>

lemma step_1_most_general:
  assumes "x \<succ>[\<R>] y"
  assumes "\<alpha> \<in> {0..(1::real)}"
    and "\<beta> \<in> {0..(1::real)}"
  assumes "\<alpha> > \<beta>"
  shows "(mix_pmf \<alpha> x y) \<succ>[\<R>] (mix_pmf \<beta> x y)"
proof -
  consider (ex) "\<alpha> = 1 \<and> \<beta> = 0" | (m) "\<alpha> \<noteq> 1 \<or> \<beta> \<noteq> 0"
    by blast
  then show ?thesis
  proof (cases)
    case m
    consider  "\<beta> = 0" |  "\<beta> \<noteq> 0"
      by blast
    then show ?thesis
    proof (cases)
      case 1
      then show ?thesis
        using assms(1) assms(2) assms(4) ind rpr sg_imp_mix_sg by fastforce
    next
      case 2
      let ?d = "(\<beta>/\<alpha>)"
      have sg: "(mix_pmf \<alpha> x y) \<succ>[\<R>] y"
        using assms(1) assms(2) assms(3) assms(4) ind rpr sg_imp_mix_sg by fastforce
      have a: "\<alpha> > 0"
        using assms(3) assms(4) by auto
      then have div_in: "?d \<in> {0<..1}"
        using assms(3) assms(4) 2 by auto
      have mx_p: "(mix_pmf \<alpha> x y) \<in> \<P>"
        by (meson sg preference_def rational_preference_def rpr)
      have y_P: "y \<in> \<P>"
        by (meson assms(1) preference_def rational_preference_def rpr)
      hence "(mix_pmf ?d (mix_pmf \<alpha> x y) y) \<in> \<P>"
        using div_in mx_p by (simp add: mix_in_lot)
      have " mix_pmf \<beta> (mix_pmf \<alpha> x y) y \<succ>[\<R>] y"
        using sg_imp_mix_sg[of "(mix_pmf \<alpha> x y)" y \<R> outcomes \<beta>] sg div_in rpr ind
          a assms(2) "2" assms(3) by auto
      have al1: "\<forall>r \<in> \<P>. (mix_pmf \<alpha> x r) \<succ>[\<R>] (mix_pmf \<alpha> y r)"
        by (meson a assms(1) assms(2) atLeastAtMost_iff greaterThanAtMost_iff ind 
            independece_dest_alt preference.not_outside rational_preference_def rpr y_P)
      then show ?thesis 
        using greater_mix_pmf_greater_step_1_aux assms
        by (metis a div_in divide_less_eq_1_pos greaterThanAtMost_iff 
            greaterThanLessThan_iff mix_pmf_comp_with_dif_equiv neumann_3B_b sg)
    qed 
  qed (simp add: assms(1))
qed


text \<open> Kreps refers to this lemma as 5.6 c. 
       The lemma after that is also significant.\<close>
lemma approx_remains_after_same_comp:
  assumes "p \<approx>[\<R>] q"
    and "r \<in> \<P>"
    and "\<alpha> \<in> {0..1}"
  shows "mix_pmf \<alpha> p r \<approx>[\<R>] mix_pmf \<alpha> q r"
  using approx_indep_ge assms(1) assms(2) assms(3) ind rpr by blast

text \<open> This lemma is the symmetric version of the previous lemma. 
       This lemma is never mentioned in literature anywhere. 
       Even though it looks trivial now, due to the asymmetric nature of the 
       independence axiom, it is not so trivial, and definitely worth mentioning. \<close>
lemma approx_remains_after_same_comp_left:
  assumes "p \<approx>[\<R>] q"
    and "r \<in> \<P>"
    and "\<alpha> \<in> {0..1}"
  shows "mix_pmf \<alpha> r p \<approx>[\<R>] mix_pmf \<alpha> r q"
proof -
  have 1: "\<alpha> \<le> 1 \<and> \<alpha> \<ge> 0" "1 - \<alpha> \<in> {0..1}"
    using assms(3) by auto+
  have fst: "mix_pmf \<alpha> r p \<approx>[\<R>] mix_pmf (1-\<alpha>) p r"
    using assms  by (metis mix_in_lot pmf_inverse_switch_eqals 
    rational_preference.compl relation_in_carrier rpr)
  moreover have "mix_pmf \<alpha> r p \<approx>[\<R>] mix_pmf \<alpha> r q"
    using approx_remains_after_same_comp[of _ _ _ \<alpha>] pmf_inverse_switch_eqals[of \<alpha> p q] 1 
      pmf_inverse_switch_eqals rpr mix_pmf_preferred_independence[of _ \<alpha> _ _]
    by (metis assms(1) assms(2) assms(3) mix_pmf_preferred_independence)
  thus ?thesis
    by blast
qed

lemma mix_of_preferred_is_preferred:
  assumes "p \<succeq>[\<R>] w"
  assumes "q \<succeq>[\<R>] w"
  assumes "\<alpha> \<in> {0..1}"
  shows "mix_pmf \<alpha> p q \<succeq>[\<R>] w"
proof -
  consider "p \<succeq>[\<R>] q" | "q \<succeq>[\<R>] p"
    using rpr assms(1) assms(2) rational_preference.compl relation_in_carrier by blast
  then show ?thesis
  proof (cases)
    case 1
    have "mix_pmf \<alpha> p q \<succeq>[\<R>] q"
      using "1" assms(3) geq_imp_mix_geq_right ind rpr by blast
    moreover have "q \<succeq>[\<R>] w" 
      using assms by auto
    ultimately show ?thesis using rpr preference.transitivity[of \<P> \<R>]
      by (meson rational_preference_def transE)
  next
    case 2
    have "mix_pmf \<alpha> p q \<succeq>[\<R>] p"      
      using "2" assms geq_imp_mix_geq_left ind rpr by blast
    moreover have "p \<succeq>[\<R>] w" 
      using assms by auto
    ultimately show ?thesis using rpr preference.transitivity[of \<P> \<R>]
      by (meson rational_preference_def transE)
  qed
qed

lemma mix_of_not_preferred_is_not_preferred:
  assumes "w \<succeq>[\<R>] p"
  assumes "w \<succeq>[\<R>] q"
  assumes "\<alpha> \<in> {0..1}"
  shows "w \<succeq>[\<R>] mix_pmf \<alpha> p q"
proof -
  consider "p \<succeq>[\<R>] q" | "q \<succeq>[\<R>] p"
    using rpr assms(1) assms(2) rational_preference.compl relation_in_carrier by blast
  then show ?thesis
  proof (cases)
    case 1
    moreover have "p \<succeq>[\<R>] mix_pmf \<alpha> p q"
      using assms(3) neumann_3B_b_non_strict calculation by blast
    moreover show ?thesis
      using rpr preference.transitivity[of \<P> \<R>]
      by (meson assms(1) calculation(2) rational_preference_def transE)
  next
    case 2
    moreover have "q \<succeq>[\<R>] mix_pmf \<alpha> p q"
      using assms(3) neumann_3B_b_non_strict calculation
      by (metis mix_pmf_preferred_independence relation_in_carrier set_pmf_mix_eq)
    moreover show ?thesis
      using rpr preference.transitivity[of \<P> \<R>]
      by (meson assms(2) calculation(2) rational_preference_def transE)
  qed
qed

private definition degenerate_lotteries where
  "degenerate_lotteries = {x \<in> \<P>. card (set_pmf x) = 1}"

private definition best where
  "best = {x \<in> \<P>. (\<forall>y \<in> \<P>. x \<succeq>[\<R>] y)}"

private definition worst where
  "worst = {x \<in> \<P>. (\<forall>y \<in> \<P>. y \<succeq>[\<R>] x)}"

lemma degenerate_total: 
  "\<forall>e \<in> degenerate_lotteries. \<forall>m \<in> \<P>. e \<succeq>[\<R>] m \<or> m \<succeq>[\<R>] e"
  using degenerate_lotteries_def rational_preference.compl rpr by fastforce

lemma degen_outcome_cardinalities:
  "card degenerate_lotteries = card outcomes"
  using card_degen_lotteries_equals_outcomes degenerate_lotteries_def by auto

lemma degenerate_lots_subset_all: "degenerate_lotteries \<subseteq> \<P>"
  by (simp add: degenerate_lotteries_def)

lemma alt_definition_of_degenerate_lotteries[iff]:
  "{return_pmf x |x. x\<in> outcomes} = degenerate_lotteries"
proof (standard, goal_cases)
  case 1
  have "\<forall>x \<in> {return_pmf x |x. x \<in> outcomes}. x \<in> degenerate_lotteries"
  proof
    fix x
    assume a: "x \<in> {return_pmf x |x. x \<in> outcomes}"
    then have "card (set_pmf x) = 1"
      by auto
    moreover have "set_pmf x \<subseteq> outcomes"
      using a set_pmf_subset_singleton by auto
    moreover have "x \<in> \<P>"
      by (simp add: lotteries_on_def calculation)
    ultimately show "x \<in> degenerate_lotteries"
      by (simp add: degenerate_lotteries_def)
  qed
  then show ?case by blast
next
  case 2
  have "\<forall>x \<in> degenerate_lotteries. x \<in> {return_pmf x |x. x \<in> outcomes}"
  proof
    fix x
    assume a: "x \<in> degenerate_lotteries"
    hence "card (set_pmf x) = 1"
      using degenerate_lotteries_def by blast
    moreover have "set_pmf x \<subseteq> outcomes"
      by (meson a degenerate_lots_subset_all subset_iff support_in_outcomes)
    moreover obtain e where "{e} = set_pmf x"
      using calculation
      by (metis card_1_singletonE)
    moreover have "e \<in> outcomes"
      using calculation(2) calculation(3) by blast
    moreover have "x = return_pmf e"
      using calculation(3) set_pmf_subset_singleton by fastforce
    ultimately show "x \<in> {return_pmf x |x. x \<in> outcomes}"
      by blast
  qed
  then show ?case by blast
qed

lemma best_indifferent:
  "\<forall>x \<in> best. \<forall>y \<in> best. x \<approx>[\<R>] y"
  by (simp add: best_def)

lemma worst_indifferent:
  "\<forall>x \<in> worst. \<forall>y \<in> worst. x \<approx>[\<R>] y"
  by (simp add: worst_def)

lemma best_worst_indiff_all_indiff:
  assumes "b \<in> best"
    and "w \<in> worst"
    and "b \<approx>[\<R>] w"
  shows "\<forall>e \<in> \<P>. e \<approx>[\<R>] w" "\<forall>e \<in> \<P>. e \<approx>[\<R>] b"
proof -
  show "\<forall>e \<in> \<P>. e \<approx>[\<R>] w"
  proof (standard)
    fix e 
    assume a: "e \<in> \<P>"
    then have "b \<succeq>[\<R>] e"
      using a best_def assms  by blast
    moreover have "e \<succeq>[\<R>] w"
      using a assms worst_def by auto
    moreover have "b \<succeq>[\<R>] e"
      by (simp add: calculation(1))
    moreover show "e \<approx>[\<R>] w"
    proof (rule ccontr)
      assume "\<not> e \<approx>[\<R>] w"
      then consider "e \<succ>[\<R>] w" | "w \<succ>[\<R>] e"
        by (simp add: calculation(2))
      then show False 
      proof (cases)
        case 2
        then show ?thesis
          using calculation(2) by blast
      qed (meson assms(3) calculation(1) 
          rational_preference.strict_is_neg_transitive relation_in_carrier rpr)
    qed
  qed
  then show "\<forall>e\<in>local.\<P>. e \<approx>[\<R>] b"
    using assms  by (meson rational_preference.compl 
        rational_preference.strict_is_neg_transitive relation_in_carrier rpr)
qed  

text \<open> Like Step 1 most general but with IFF. \<close>
lemma mix_pmf_pref_iff_more_likely [iff]: 
  assumes "b \<succ>[\<R>] w"
  assumes "\<alpha> \<in> {0..1}"
    and "\<beta> \<in> {0..1}"
  shows "\<alpha> > \<beta> \<longleftrightarrow> mix_pmf \<alpha> b w \<succ>[\<R>] mix_pmf \<beta> b w" (is "?L \<longleftrightarrow> ?R")
  using assms step_1_most_general[of b w \<alpha> \<beta>]
  by (metis linorder_neqE_linordered_idom step_1_most_general)

lemma better_worse_good_mix_preferred[iff]: 
  assumes "b \<succeq>[\<R>] w"
  assumes "\<alpha> \<in> {0..1}"
    and "\<beta> \<in> {0..1}"
  assumes "\<alpha> \<ge> \<beta>" 
  shows "mix_pmf \<alpha> b w \<succeq>[\<R>] mix_pmf \<beta> b w"
proof-
  have "(0::real) \<le> 1"
    by simp
  then show ?thesis
    by (metis (no_types) assms assms(1) assms(2) assms(3) atLeastAtMost_iff 
        less_eq_real_def mix_of_not_preferred_is_not_preferred 
        mix_of_preferred_is_preferred mix_pmf_preferred_independence 
        pmf_mix_0 relation_in_carrier step_1_most_general)
qed

subsection \<open> Add finiteness and non emptyness of outcomes \<close>
context
  assumes fnt: "finite outcomes"
  assumes nempty: "outcomes \<noteq> {}"
begin

lemma finite_degenerate_lotteries: 
  "finite degenerate_lotteries"
  using degen_outcome_cardinalities fnt nempty by fastforce

lemma degenerate_has_max_preferred:
  "{x \<in> degenerate_lotteries. (\<forall>y \<in> degenerate_lotteries. x \<succeq>[\<R>] y)} \<noteq> {}" (is "?l \<noteq> {}")
proof
  assume a: "?l = {}"
  let ?DG = "degenerate_lotteries"
  obtain R where
    R: "rational_preference ?DG R" "R \<subseteq> \<R>"
    using degenerate_lots_subset_all rational_preference.all_carrier_ex_sub_rel rpr by blast
  then have "\<exists>e \<in> ?DG. \<forall>e' \<in> ?DG. e \<succeq>[\<R>] e'"
    by (metis R(1) R(2) card_0_eq degen_outcome_cardinalities 
        finite_degenerate_lotteries fnt nempty subset_eq
        rational_preference.finite_nonempty_carrier_has_maximum )
  then show False
    using a by auto
qed

lemma degenerate_has_min_preferred:
  "{x \<in> degenerate_lotteries. (\<forall>y \<in> degenerate_lotteries. y \<succeq>[\<R>] x)} \<noteq> {}" (is "?l \<noteq> {}")
proof
  assume a: "?l = {}"
  let ?DG = "degenerate_lotteries"
  obtain R where
    R: "rational_preference ?DG R" "R \<subseteq> \<R>"
    using degenerate_lots_subset_all rational_preference.all_carrier_ex_sub_rel rpr by blast
  have "\<exists>e \<in> ?DG. \<forall>e' \<in> ?DG. e' \<succeq>[\<R>] e"
    by (metis R(1) R(2) card_0_eq degen_outcome_cardinalities 
        finite_degenerate_lotteries fnt nempty subset_eq
        rational_preference.finite_nonempty_carrier_has_minimum )
  then show False
    using a by auto
qed

lemma exists_best_degenerate:
  "\<exists>x \<in> degenerate_lotteries. \<forall>y \<in> degenerate_lotteries. x \<succeq>[\<R>] y"
  using degenerate_has_max_preferred by blast

lemma exists_worst_degenerate:
  "\<exists>x \<in> degenerate_lotteries. \<forall>y \<in> degenerate_lotteries. y \<succeq>[\<R>] x"
  using degenerate_has_min_preferred by blast

lemma best_degenerate_in_best_overall: 
  "\<exists>x \<in> degenerate_lotteries. \<forall>y \<in> \<P>. x \<succeq>[\<R>] y"
proof -
  obtain b where
    b: "b \<in> degenerate_lotteries" "\<forall>y \<in> degenerate_lotteries. b \<succeq>[\<R>] y"
    using exists_best_degenerate by blast
  have asm: "finite outcomes" "set_pmf b \<subseteq> outcomes"
    by (simp add: fnt) (meson b(1) degenerate_lots_subset_all subset_iff support_in_outcomes)
  obtain B where B: "set_pmf b = {B}"
    using b card_1_singletonE degenerate_lotteries_def by blast
  have deg: "\<forall>d\<in>outcomes. b \<succeq>[\<R>] return_pmf d"
    using alt_definition_of_degenerate_lotteries b(2) by blast
  define P where
    "P = (\<lambda>p. p \<in> \<P> \<longrightarrow> return_pmf B \<succeq>[\<R>] p)"
  have "P p" for p
  proof -
    consider "set_pmf p \<subseteq> outcomes" | "\<not>set_pmf p \<subseteq> outcomes"
      by blast
    then show ?thesis 
    proof (cases)
      case 1
      have "finite outcomes" "set_pmf p \<subseteq> outcomes"
        by (auto simp: 1 asm) 
      then show ?thesis
      proof (induct  rule: pmf_mix_induct')
        case (degenerate x)
        then show ?case
          using B P_def deg set_pmf_subset_singleton by fastforce
      qed (simp add: P_def lotteries_on_def mix_of_not_preferred_is_not_preferred
               mix_of_not_preferred_is_not_preferred[of b p q a])
    qed  (simp add: lotteries_on_def P_def)
  qed
  moreover have "\<forall>e \<in> \<P>. b \<succeq>[\<R>] e"
    using calculation B P_def set_pmf_subset_singleton by fastforce
  ultimately show ?thesis
    using b degenerate_lots_subset_all by blast
qed

lemma worst_degenerate_in_worst_overall: 
  "\<exists>x \<in> degenerate_lotteries. \<forall>y \<in> \<P>. y \<succeq>[\<R>] x"
proof -
  obtain b where
    b: "b \<in> degenerate_lotteries" "\<forall>y \<in> degenerate_lotteries. y \<succeq>[\<R>] b"
    using exists_worst_degenerate by blast
  have asm: "finite outcomes" "set_pmf b \<subseteq> outcomes"
    by (simp add: fnt) (meson b(1) degenerate_lots_subset_all subset_iff support_in_outcomes)
  obtain B where B: "set_pmf b = {B}"
    using b card_1_singletonE degenerate_lotteries_def by blast
  have deg: "\<forall>d\<in>outcomes. return_pmf d \<succeq>[\<R>] b"
    using alt_definition_of_degenerate_lotteries b(2) by blast
  define P where
    "P = (\<lambda>p. p \<in> \<P> \<longrightarrow> p \<succeq>[\<R>] return_pmf B)"
  have "P p" for p
  proof -
    consider "set_pmf p \<subseteq> outcomes" | "\<not>set_pmf p \<subseteq> outcomes"
      by blast
    then show ?thesis 
    proof (cases)
      case 1
      have "finite outcomes" "set_pmf p \<subseteq> outcomes"
        by (auto simp: 1 asm) 
      then show ?thesis
      proof (induct rule: pmf_mix_induct')
        case (degenerate x)
        then show ?case
          using B P_def deg set_pmf_subset_singleton by fastforce
      next
      qed (simp add: P_def lotteries_on_def mix_of_preferred_is_preferred
          mix_of_not_preferred_is_not_preferred[of b p])
    qed (simp add: lotteries_on_def P_def)
  qed
  moreover have "\<forall>e \<in> \<P>. e \<succeq>[\<R>] b"
    using calculation B P_def set_pmf_subset_singleton by fastforce
  ultimately show ?thesis
    using b degenerate_lots_subset_all by blast
qed 

lemma overall_best_nonempty:
  "best \<noteq> {}"
  using best_def best_degenerate_in_best_overall degenerate_lots_subset_all by blast

lemma overall_worst_nonempty:
  "worst \<noteq> {}"
  using degenerate_lots_subset_all worst_def worst_degenerate_in_worst_overall by auto


lemma trans_approx:
  assumes "x\<approx>[\<R>] y" 
    and " y \<approx>[\<R>] z" 
  shows "x \<approx>[\<R>] z"
  using preference.indiff_trans[of \<P> \<R> x y z] assms rpr rational_preference_def by blast


text \<open> First EXPLICIT use of the axiom of choice \<close>

private definition some_best where
  "some_best = (SOME x. x \<in> degenerate_lotteries \<and> x \<in> best)"

private definition some_worst where
  "some_worst = (SOME x. x \<in> degenerate_lotteries \<and> x \<in> worst)"

private definition my_U :: "'a pmf \<Rightarrow> real"
  where
    "my_U p = (SOME \<alpha>. \<alpha>\<in>{0..1} \<and> p \<approx>[\<R>] mix_pmf \<alpha> some_best some_worst)"

lemma exists_best_and_degenerate: "degenerate_lotteries \<inter> best \<noteq> {}"
  using best_def best_degenerate_in_best_overall degenerate_lots_subset_all by blast


lemma exists_worst_and_degenerate: "degenerate_lotteries \<inter> worst \<noteq> {}"
  using worst_def worst_degenerate_in_worst_overall degenerate_lots_subset_all by blast

lemma some_best_in_best: "some_best \<in> best"
  using exists_best_and_degenerate some_best_def
  by (metis (mono_tags, lifting) Int_emptyI some_eq_ex)

lemma some_worst_in_worst: "some_worst \<in> worst"
  using exists_worst_and_degenerate some_worst_def
  by (metis (mono_tags, lifting) Int_emptyI some_eq_ex)


lemma best_always_at_least_as_good_mix:
  assumes "\<alpha> \<in> {0..1}"
    and "p \<in> \<P>"
  shows "mix_pmf \<alpha> some_best p \<succeq>[\<R>] p"
  using assms(1) assms(2) best_def mix_of_preferred_is_preferred 
    rational_preference.compl rpr some_best_in_best by fastforce

lemma geq_mix_imp_weak_pref:
  assumes "\<alpha> \<in> {0..1}"
    and "\<beta> \<in> {0..1}"
  assumes "\<alpha> \<ge> \<beta>"
  shows "mix_pmf \<alpha> some_best some_worst \<succeq>[\<R>] mix_pmf \<beta> some_best some_worst"
  using assms(1) assms(2) assms(3) best_def some_best_in_best some_worst_in_worst worst_def by auto

lemma gamma_inverse:
  assumes "\<alpha> \<in> {0<..<1}"
    and "\<beta> \<in> {0<..<1}"
  shows "(1::real) - (\<alpha> - \<beta>) / (1 - \<beta>) = (1 - \<alpha>) / (1 - \<beta>)"
proof - 
  have "1 - (\<alpha> - \<beta>) / (1 - \<beta>) =  (1 - \<beta>)/(1 - \<beta>) - (\<alpha> - \<beta>) / (1 - \<beta>)"
    using assms(2) by auto
  also have "... = (1 - \<beta> - (\<alpha> - \<beta>)) / (1 - \<beta>)"
    by (metis diff_divide_distrib)
  also have "... = (1 - \<alpha>) / (1 - \<beta>)"
    by simp
  finally show ?thesis .
qed

lemma all_mix_pmf_indiff_indiff_best_worst:
  assumes "l \<in> \<P>"
  assumes "b \<in> best"
  assumes "w \<in> worst"
  assumes "b \<approx>[\<R>] w"
  shows "\<forall>\<alpha> \<in>{0..1}. l \<approx>[\<R>] mix_pmf \<alpha> b w"
  by (meson assms best_worst_indiff_all_indiff(1) mix_of_preferred_is_preferred
      best_worst_indiff_all_indiff(2) mix_of_not_preferred_is_not_preferred)

lemma indiff_imp_same_utility_value:
  assumes "some_best \<succ>[\<R>] some_worst"
  assumes "\<alpha> \<in> {0..1}"
  assumes "\<beta> \<in> {0..1}"
  assumes "mix_pmf \<beta> some_best some_worst \<approx>[\<R>] mix_pmf \<alpha> some_best some_worst"
  shows "\<beta> = \<alpha>"
  using assms(1) assms(2) assms(3) assms(4) linorder_neqE_linordered_idom by blast

lemma leq_mix_imp_weak_inferior:
  assumes "some_best \<succ>[\<R>] some_worst"
  assumes "\<alpha> \<in> {0..1}"
    and "\<beta> \<in> {0..1}"
  assumes "mix_pmf \<beta> some_best some_worst \<succeq>[\<R>] mix_pmf \<alpha> some_best some_worst"
  shows "\<beta> \<ge> \<alpha>"
proof -
  have *: "mix_pmf \<beta> some_best some_worst \<approx>[\<R>] mix_pmf \<alpha> some_best some_worst \<Longrightarrow> \<alpha> \<le> \<beta>"
    using assms(1) assms(2) assms(3) indiff_imp_same_utility_value by blast
  consider "mix_pmf \<beta> some_best some_worst \<succ>[\<R>] mix_pmf \<alpha> some_best some_worst" |
    "mix_pmf \<beta> some_best some_worst \<approx>[\<R>] mix_pmf \<alpha> some_best some_worst"
    using assms(4) by blast
  then show ?thesis
    by(cases) (meson assms(2) assms(3) geq_mix_imp_weak_pref le_cases *)+
qed

lemma ge_mix_pmf_preferred:
  assumes "x \<succ>[\<R>] y"
  assumes "\<alpha> \<in> {0..1}"
    and "\<beta> \<in> {0..1}"
  assumes "\<alpha> \<ge> \<beta>"
  shows "(mix_pmf \<alpha> x y) \<succeq>[\<R>] (mix_pmf \<beta> x y)"
  using assms(1) assms(2) assms(3) assms(4) by blast



subsection \<open> Add continuity to assumptions \<close>
context
  assumes cnt: "continuous_vnm (lotteries_on outcomes) \<R>"
begin


text \<open> In Literature this is referred to as step 2. \<close>
lemma step_2_unique_continuous_unfolding:
  assumes "p \<succeq>[\<R>] q"
    and "q \<succeq>[\<R>] r"
    and "p \<succ>[\<R>] r"
  shows "\<exists>!\<alpha> \<in> {0..1}. q \<approx>[\<R>] mix_pmf \<alpha> p r"
proof (rule ccontr)
  assume neg_a: "\<nexists>!\<alpha>. \<alpha> \<in> {0..1} \<and> q \<approx>[\<R>] mix_pmf \<alpha> p r"
  have "\<exists>\<alpha> \<in> {0..1}. q \<approx>[\<R>] mix_pmf \<alpha> p r"
    using non_unique_continuous_unfolding[of outcomes \<R> p q r] 
      assms cnt rpr by blast
  then obtain \<alpha> \<beta> :: real where
    a_b: "\<alpha>\<in>{0..1}" "\<beta> \<in>{0..1}" "q \<approx>[\<R>] mix_pmf \<alpha> p r" "q \<approx>[\<R>] mix_pmf \<beta> p r" "\<alpha> \<noteq> \<beta>"
    using neg_a by blast
  consider "\<alpha> > \<beta>" | "\<beta> > \<alpha>"
    using a_b by linarith
  then show False
  proof (cases)
    case 1
    with step_1_most_general[of p r \<alpha> \<beta>] assms 
    have "mix_pmf \<alpha> p r \<succ>[\<R>] mix_pmf \<beta> p r"
      using a_b(1) a_b(2) by blast
    then show ?thesis using a_b
      by (meson rational_preference.strict_is_neg_transitive relation_in_carrier rpr)
  next
    case 2
    with step_1_most_general[of p r \<beta> \<alpha>] assms have "mix_pmf \<beta> p r \<succ>[\<R>]mix_pmf \<alpha> p r"
      using a_b(1) a_b(2) by blast
    then show ?thesis using a_b
      by (meson rational_preference.strict_is_neg_transitive relation_in_carrier rpr)
  qed
qed

text \<open> These folowing two lemmas are referred to sometimes called step 2. \<close>
lemma create_unique_indiff_using_distinct_best_worst:
  assumes "l \<in> \<P>"
  assumes "b \<in> best"
  assumes "w \<in> worst"
  assumes "b \<succ>[\<R>] w"
  shows "\<exists>!\<alpha> \<in>{0..1}. l \<approx>[\<R>] mix_pmf \<alpha> b w"
proof -
  have "b \<succeq>[\<R>] l" 
    using best_def
    using assms by blast
  moreover have "l \<succeq>[\<R>] w"
    using worst_def assms by blast
  ultimately show "\<exists>!\<alpha>\<in>{0..1}. l \<approx>[\<R>] mix_pmf \<alpha> b w"
    using step_2_unique_continuous_unfolding[of b l w] assms by linarith
qed

lemma exists_element_bw_mix_is_approx:
  assumes "l \<in> \<P>"
  assumes "b \<in> best"
  assumes "w \<in> worst"
  shows "\<exists>\<alpha> \<in>{0..1}. l \<approx>[\<R>] mix_pmf \<alpha> b w"
proof -
  consider "b \<succ>[\<R>] w" | "b \<approx>[\<R>] w"
    using assms(2) assms(3) best_def worst_def by auto
  then show ?thesis
  proof (cases)
    case 1
    then show ?thesis 
      using create_unique_indiff_using_distinct_best_worst assms by blast  
  qed (auto simp: all_mix_pmf_indiff_indiff_best_worst assms)
qed

lemma my_U_is_defined:
  assumes "p \<in> \<P>"
  shows "my_U p \<in> {0..1}" "p \<approx>[\<R>] mix_pmf (my_U p) some_best some_worst"
proof -
  have "some_best \<in> best" 
    by (simp add: some_best_in_best)
  moreover have "some_worst \<in> worst"
    by (simp add: some_worst_in_worst)
  with exists_element_bw_mix_is_approx[of p "some_best" "some_worst"] calculation assms
  have e: "\<exists>\<alpha>\<in>{0..1}. p \<approx>[\<R>] mix_pmf \<alpha> some_best some_worst" by blast
  then show "my_U p \<in> {0..1}"
    by (metis (mono_tags, lifting) my_U_def someI_ex)
  show "p \<approx>[\<R>] mix_pmf (my_U p) some_best some_worst" 
    by (metis (mono_tags, lifting) e my_U_def someI_ex)
qed 

lemma weak_pref_mix_with_my_U_weak_pref:
  assumes "p \<succeq>[\<R>] q"
  shows "mix_pmf (my_U p) some_best some_worst \<succeq>[\<R>] mix_pmf (my_U q) some_best some_worst"
  by (meson assms my_U_is_defined(2) relation_in_carrier rpr 
      rational_preference.weak_is_transitive)

lemma preferred_greater_my_U: 
  assumes "p \<in> \<P>"
    and "q \<in> \<P>"
  assumes "mix_pmf (my_U p) some_best some_worst \<succ>[\<R>] mix_pmf (my_U q) some_best some_worst"
  shows "my_U p > my_U q"
proof (rule ccontr)
  assume "\<not> my_U p > my_U q"
  then consider "my_U p = my_U q" | "my_U p < my_U q"
    by linarith
  then show False 
  proof (cases)
    case 1
    then have "mix_pmf (my_U p) some_best some_worst \<approx>[\<R>] mix_pmf (my_U q) some_best some_worst"
      using assms by auto
    then show ?thesis using assms by blast
  next
    case 2
    moreover have "my_U q \<in> {0..1}"
      using assms(2) my_U_is_defined(1) by blast
    moreover have "my_U p \<in> {0..1}"
      using assms(1) my_U_is_defined(1) by blast
    moreover have "mix_pmf (my_U q) some_best some_worst \<succeq>[\<R>] mix_pmf (my_U p) some_best some_worst"
      using calculation geq_mix_imp_weak_pref by auto
    then show ?thesis using assms by blast
  qed
qed

lemma geq_my_U_imp_weak_preference:
  assumes "p \<in> \<P>" 
    and "q \<in> \<P>" 
  assumes "some_best \<succ>[\<R>] some_worst"
  assumes "my_U p \<ge> my_U q"
  shows "p \<succeq>[\<R>] q"
proof -
  have p_q: "my_U p \<in> {0..1}" "my_U q \<in> {0..1}"
    using assms my_U_is_defined(1) by blast+
  with ge_mix_pmf_preferred[of "some_best" "some_worst" "my_U p" "my_U q"] 
    p_q assms(1) assms(3) assms(4)
  have "mix_pmf (my_U p) some_best some_worst \<succeq>[\<R>] mix_pmf (my_U q) some_best some_worst"  by blast
  consider "my_U p = my_U q" | "my_U p > my_U q"
    using assms by linarith
  then show ?thesis
  proof (cases)
    case 2
    then show ?thesis
      by (meson assms(1) assms(2) assms(3) p_q(1) p_q(2) rational_preference.compl 
          rpr step_1_most_general weak_pref_mix_with_my_U_weak_pref)
  qed (metis assms(1) assms(2) my_U_is_defined(2) trans_approx)
qed

lemma my_U_represents_pref:
  assumes "some_best \<succ>[\<R>] some_worst"
  assumes "p \<in> \<P>" 
    and "q \<in> \<P>" 
  shows "p \<succeq>[\<R>] q \<longleftrightarrow> my_U p \<ge> my_U q" (is "?L \<longleftrightarrow> ?R")
proof -
  have p_def: "my_U p\<in> {0..1}" "my_U q \<in> {0..1}"
    using assms my_U_is_defined by blast+
  show ?thesis
  proof
    assume a: ?L
    hence "mix_pmf (my_U p) some_best some_worst \<succeq>[\<R>] mix_pmf (my_U q) some_best some_worst"
      using weak_pref_mix_with_my_U_weak_pref by auto
    then show ?R using leq_mix_imp_weak_inferior[of "my_U p" "my_U q"] p_def a
        assms(1) leq_mix_imp_weak_inferior by blast
  next 
    assume ?R
    then show ?L using geq_my_U_imp_weak_preference
      using assms(1) assms(2) assms(3) by blast
  qed
qed

lemma first_iff_u_greater_strict_preff:
  assumes "p \<in> \<P>"
    and "q \<in> \<P>"
  assumes "some_best \<succ>[\<R>] some_worst"
  shows "my_U p > my_U q \<longleftrightarrow> mix_pmf (my_U p) some_best some_worst \<succ>[\<R>] mix_pmf (my_U q) some_best some_worst"
proof
  assume a: "my_U p > my_U q"
  have "my_U p \<in> {0..1}" "my_U q \<in> {0..1}"
    using assms my_U_is_defined(1) by blast+
  then show "mix_pmf (my_U p) some_best some_worst \<succ>[\<R>] mix_pmf (my_U q) some_best some_worst" 
    using a assms(3) by blast
next
  assume a: "mix_pmf (my_U p) some_best some_worst \<succ>[\<R>] mix_pmf (my_U q) some_best some_worst"
  have "my_U p \<in> {0..1}" "my_U q \<in> {0..1}"
    using assms my_U_is_defined(1) by blast+
  then show "my_U p > my_U q "
    using preferred_greater_my_U[of p q] assms a by blast
qed

lemma second_iff_calib_mix_pref_strict_pref:
  assumes "p \<in> \<P>"
    and "q \<in> \<P>"
  assumes "some_best \<succ>[\<R>] some_worst"
  shows "mix_pmf (my_U p) some_best some_worst \<succ>[\<R>] mix_pmf (my_U q) some_best some_worst \<longleftrightarrow> p \<succ>[\<R>] q"
proof
  assume a: "mix_pmf (my_U p) some_best some_worst \<succ>[\<R>] mix_pmf (my_U q) some_best some_worst"
  have "my_U p \<in> {0..1}" "my_U q \<in> {0..1}"
    using assms my_U_is_defined(1) by blast+
  then show "p \<succ>[\<R>] q" 
    using a assms(3) assms(1) assms(2) geq_my_U_imp_weak_preference 
      leq_mix_imp_weak_inferior weak_pref_mix_with_my_U_weak_pref by blast
next
  assume a: "p \<succ>[\<R>] q"
  have "my_U p \<in> {0..1}" "my_U q \<in> {0..1}"
    using assms my_U_is_defined(1) by blast+
  then show "mix_pmf (my_U p) some_best some_worst \<succ>[\<R>] mix_pmf (my_U q) some_best some_worst"
    using a assms(1) assms(2) assms(3) leq_mix_imp_weak_inferior my_U_represents_pref by blast
qed

lemma my_U_is_linear_function:
  assumes "p \<in> \<P>"
    and "q \<in> \<P>"
    and "\<alpha> \<in> {0..1}"
  assumes "some_best \<succ>[\<R>] some_worst" 
  shows "my_U (mix_pmf \<alpha> p q) = \<alpha> * my_U p + (1 - \<alpha>) * my_U q"
proof - 
  define B where B: "B = some_best"
  define W where W:"W = some_worst"
  define Up where Up: "Up = my_U p"
  define Uq where Uq: "Uq = my_U q"
  have long_in: "(\<alpha> * Up + (1 - \<alpha>) * Uq) \<in> {0..1}"
  proof -
    have "Up \<in> {0..1}"
      using assms Up my_U_is_defined(1) by blast
    moreover have "Uq \<in> {0..1}"
      using assms Uq my_U_is_defined(1) by blast
    moreover have "\<alpha> * Up \<in> {0..1}"
      using \<open>Up \<in> {0..1}\<close> assms(3) mult_le_one by auto
    moreover have "1-\<alpha> \<in> {0..1}"
      using assms(3) by auto
    moreover  have "(1 - \<alpha>) * Uq \<in> {0..1}"
      using mult_le_one[of "1-\<alpha>" Uq] calculation(2) calculation(4) by auto
    ultimately show ?thesis
      using add_nonneg_nonneg[of "\<alpha> * Up" "(1 - \<alpha>) * Uq"] 
        convex_bound_le[of Up 1 Uq \<alpha> "1-\<alpha>"] by simp
  qed
  have fst: "p \<approx>[\<R>] (mix_pmf Up B W)"
    using assms my_U_is_defined[of p] B W Up by simp
  have snd: "q \<approx>[\<R>] (mix_pmf Uq B W)"
    using assms my_U_is_defined[of q] B W Uq by simp
  have mp_in: "(mix_pmf Up B W) \<in> \<P>"
    using fst relation_in_carrier by blast
  have f2: "mix_pmf \<alpha> p q \<approx>[\<R>] mix_pmf \<alpha> (mix_pmf Up B W) q"
    using fst assms(2) assms(3) mix_pmf_preferred_independence by blast
  have **: "mix_pmf \<alpha> (mix_pmf Up B W) (mix_pmf Uq B W) = 
            mix_pmf (\<alpha> * Up + (1-\<alpha>) * Uq) B W" (is "?L = ?R")
  proof -
    let ?mixPQ = "(mix_pmf (\<alpha> * Up + (1 - \<alpha>) * Uq) B W)"
    have "\<forall>e\<in>set_pmf ?L. pmf (?L) e = pmf ?mixPQ e"
    proof 
      fix e 
      assume asm: "e \<in> set_pmf ?L"
      have i1: "pmf (?L) e = \<alpha> * pmf (mix_pmf Up B W) e + 
        pmf (mix_pmf Uq B W) e - \<alpha> * pmf (mix_pmf Uq B W) e" 
        using pmf_mix_deeper[of \<alpha> "mix_pmf Up B W" "(mix_pmf Uq B W)" e] assms(3) by blast
      have i3: "... = \<alpha> * Up * pmf B e + \<alpha> * pmf W e - \<alpha> * Up * pmf W e + Uq * pmf B e + 
        pmf W e - Uq * pmf W e - \<alpha> * Uq * pmf B e - \<alpha> * pmf W e + \<alpha> * Uq * pmf W e"
        using left_diff_distrib' pmf_mix_deeper[of Up B W e] pmf_mix_deeper[of Uq B W e]
          assms Up Uq my_U_is_defined(1) by (simp add: distrib_left right_diff_distrib)
      have j4: "pmf ?mixPQ e = (\<alpha> * Up + (1 - \<alpha>) * Uq) * pmf B e + 
        pmf W e - (\<alpha> * Up + (1 - \<alpha>) * Uq) * pmf W e" 
        using pmf_mix_deeper[of "(\<alpha> * Up + (1 - \<alpha>) * Uq)" B W e] long_in by blast
      then show "pmf (?L) e = pmf ?mixPQ e"
        by (simp add: i1 i3 mult.commute right_diff_distrib' ring_class.ring_distribs(1))
    qed
    then show ?thesis using pmf_equiv_intro1 by blast
  qed
  have "mix_pmf \<alpha> (mix_pmf Up B W) q \<approx>[\<R>] ?L"
    using approx_remains_after_same_comp_left assms(3) mp_in snd by blast
  hence *: "mix_pmf \<alpha> p q \<approx>[\<R>] mix_pmf \<alpha> (mix_pmf (my_U p) B W) (mix_pmf (my_U q) B W)"
    using Up Uq f2 trans_approx by blast
  have "mix_pmf \<alpha> (mix_pmf (my_U p) B W) (mix_pmf (my_U q) B W) = ?R"
    using Up Uq ** by blast
  hence "my_U (mix_pmf \<alpha> p q) = \<alpha> * Up + (1-\<alpha>) * Uq"
    by (metis * B W assms(4) indiff_imp_same_utility_value long_in 
        my_U_is_defined(1) my_U_is_defined(2) my_U_represents_pref relation_in_carrier)
  then show ?thesis
    using Up Uq by blast
qed


text \<open> Now we define a more general Utility 
       function that also takes the degenerate case into account \<close>
private definition general_U 
  where
    "general_U p = (if some_best \<approx>[\<R>] some_worst then 1 else my_U p)"

lemma general_U_is_linear_function:
  assumes "p \<in> \<P>"
    and "q \<in> \<P>"
    and "\<alpha> \<in> {0..1}"
  shows "general_U (mix_pmf \<alpha> p q) = \<alpha> * (general_U p) + (1 - \<alpha>) * (general_U q)"
proof -
  consider "some_best \<succ>[\<R>] some_worst" | "some_best \<approx>[\<R>] some_worst"
    using best_def some_best_in_best some_worst_in_worst worst_def by auto
  then show ?thesis
  proof (cases, goal_cases)
    case 1
    then show ?case
      using assms(1) assms(2) assms(3) general_U_def my_U_is_linear_function by auto
  next
    case 2
    then show ?case 
      using assms(1) assms(2) assms(3) general_U_def by auto
  qed
qed

lemma general_U_ordinal_Utility:
  shows "ordinal_utility \<P> \<R> general_U"
proof (standard, goal_cases)
  case (1 x y)
  consider (a) "some_best \<succ>[\<R>] some_worst" | (b) "some_best \<approx>[\<R>] some_worst"
    using best_def some_best_in_best some_worst_in_worst worst_def by auto
  then show ?case
  proof (cases, goal_cases)
    case a
    have "some_best \<succ>[\<R>] some_worst"
      using a by auto
    then show "x \<succeq>[\<R>] y = (general_U y \<le> general_U x)"
      using 1 my_U_represents_pref[of x y] general_U_def by simp
  next
    case b
    have "general_U x = 1" "general_U y = 1"
      by (simp add: b general_U_def)+
    moreover have "x \<approx>[\<R>] y" using b
      by (meson "1"(1) "1"(2) best_worst_indiff_all_indiff(1) 
          some_best_in_best some_worst_in_worst trans_approx)
    ultimately show "x \<succeq>[\<R>] y = (general_U y \<le> general_U x)"
      using general_U_def by linarith
  qed
next
  case (2 x y)
  then show ?case
    using relation_in_carrier by blast
next
  case (3 x y)
  then show ?case
    using relation_in_carrier by blast
qed

text \<open>  Proof of the linearity of general-U. 
        If we consider the definition of expected utility 
        functions from Maschler, Solan, Zamir we are done. \<close>

theorem is_linear:
  assumes "p \<in> \<P>"
    and "q \<in> \<P>"
    and "\<alpha> \<in> {0..1}"
  shows "\<exists>u. u (mix_pmf \<alpha> p q) = \<alpha> * (u p) + (1-\<alpha>) * (u q)"
proof
  let ?u = "general_U"
  consider "some_best \<succ>[\<R>] some_worst" | "some_best \<approx>[\<R>] some_worst"
    using best_def some_best_in_best some_worst_in_worst worst_def by auto
  then show "?u (mix_pmf \<alpha> p q) = \<alpha> * ?u p + (1 - \<alpha>) * ?u q"
  proof (cases)
    case 1
    then show ?thesis
      using assms(1) assms(2) assms(3) general_U_def my_U_is_linear_function by auto
  next
    case 2
    then show ?thesis
      by (simp add: general_U_def)
  qed
qed


text \<open> Now I define a Utility function that assigns a utility to all outcomes. 
       These are only finitely many \<close>
private definition ocU 
  where
    "ocU p = general_U (return_pmf p)"

lemma geral_U_is_expected_value_of_ocU:
  assumes "set_pmf p \<subseteq> outcomes"
  shows "general_U p = measure_pmf.expectation p ocU"
  using fnt assms
proof (induct rule: pmf_mix_induct')
  case (mix p q a)
  hence "general_U (mix_pmf a p q) = a * general_U p + (1-a) * general_U q"
    using general_U_is_linear_function[of p q a] mix.hyps assms lotteries_on_def mix.hyps by auto
  also have "... = a * measure_pmf.expectation p ocU + (1-a) * measure_pmf.expectation q ocU"
    by (simp add: mix.hyps(4) mix.hyps(5))
  also have "... = measure_pmf.expectation (mix_pmf a p q) ocU"
    using general_U_is_linear_function expected_value_mix_pmf_distrib fnt infinite_super mix.hyps(1)
    by (metis fnt mix.hyps(2) mix.hyps(3))
  finally show ?case .
qed (auto simp: support_in_outcomes assms fnt integral_measure_pmf_real ocU_def)

lemma ordinal_utility_expected_value:
  "ordinal_utility \<P> \<R> (\<lambda>x. measure_pmf.expectation x ocU)"
proof (standard, goal_cases)
  case (1 x y)
  have ocs: "set_pmf x \<subseteq> outcomes" "set_pmf y \<subseteq> outcomes"
    by (meson "1" subsetI support_in_outcomes)+
  have "x \<succeq>[\<R>] y \<Longrightarrow> (measure_pmf.expectation y ocU \<le> measure_pmf.expectation x ocU)"
  proof -
    assume "x \<succeq>[\<R>] y"
    have "general_U x \<ge> general_U y"
      by (meson \<open>x \<succeq>[\<R>] y\<close> general_U_ordinal_Utility ordinal_utility_def)
    then show "(measure_pmf.expectation y ocU \<le> measure_pmf.expectation x ocU)"
      using geral_U_is_expected_value_of_ocU ocs by auto
  qed
  moreover have "(measure_pmf.expectation y ocU \<le> measure_pmf.expectation x ocU) \<Longrightarrow> x \<succeq>[\<R>] y"
  proof - 
    assume "(measure_pmf.expectation y ocU \<le> measure_pmf.expectation x ocU)"
    then have "general_U x \<ge> general_U y"
      by (simp add:  geral_U_is_expected_value_of_ocU ocs(1) ocs(2))
    then show "x \<succeq>[\<R>] y"
      by (meson "1"(1) "1"(2) general_U_ordinal_Utility ordinal_utility.util_def)
  qed
  ultimately show ?case 
    by blast
next
  case (2 x y)
  then show ?case
    using relation_in_carrier by blast
next
  case (3 x y)
  then show ?case
    using relation_in_carrier by auto
qed

lemma ordinal_utility_expected_value':
  "\<exists>u. ordinal_utility \<P> \<R> (\<lambda>x. measure_pmf.expectation x u)"
  using ordinal_utility_expected_value by blast

lemma ocU_is_expected_utility_bernoulli:
  shows "\<forall>x \<in> \<P>. \<forall>y \<in> \<P>. x \<succeq>[\<R>] y \<longleftrightarrow> 
  measure_pmf.expectation x ocU \<ge> measure_pmf.expectation y ocU"
  using ordinal_utility_expected_value by (meson ordinal_utility.util_def)


end  (* continuous *)

end(* finite outcomes *)

end (* system U *)


lemma expected_value_is_utility_function:
  assumes fnt: "finite outcomes" and "outcomes \<noteq> {}"
  assumes "x \<in> lotteries_on outcomes" and "y \<in> lotteries_on outcomes"
  assumes "ordinal_utility (lotteries_on outcomes) \<R> (\<lambda>x. measure_pmf.expectation x u)"
  shows "measure_pmf.expectation x u \<ge> measure_pmf.expectation y u \<longleftrightarrow> x \<succeq>[\<R>] y" (is "?L \<longleftrightarrow> ?R")
  using assms(3) assms(4) assms(5) ordinal_utility.util_def_conf 
    ordinal_utility.ordinal_utility_left iffI  by (metis (no_types, lifting))


lemma system_U_implies_vNM_utility:
  assumes fnt: "finite outcomes" and "outcomes \<noteq> {}"
  assumes rpr: "rational_preference (lotteries_on outcomes) \<R>"
  assumes ind: "independent_vnm (lotteries_on outcomes) \<R>"
  assumes cnt: "continuous_vnm (lotteries_on outcomes) \<R>"
  shows "\<exists>u. ordinal_utility (lotteries_on outcomes) \<R> (\<lambda>x. measure_pmf.expectation x u)"
  using ordinal_utility_expected_value'[of outcomes \<R>] assms by blast

lemma vNM_utility_implies_rationality:
  assumes fnt: "finite outcomes" and "outcomes \<noteq> {}"
  assumes "\<exists>u. ordinal_utility (lotteries_on outcomes) \<R> (\<lambda>x. measure_pmf.expectation x u)"
  shows "rational_preference (lotteries_on outcomes) \<R>"
  using assms(3) ordinal_util_imp_rat_prefs by blast

theorem vNM_utility_implies_independence:
  assumes fnt: "finite outcomes" and "outcomes \<noteq> {}"
  assumes "\<exists>u. ordinal_utility (lotteries_on outcomes) \<R> (\<lambda>x. measure_pmf.expectation x u)"
  shows "independent_vnm (lotteries_on outcomes) \<R>"
proof (rule independent_vnmI2)
  fix p  q r 
    and \<alpha>::real
  assume a1: "p \<in> \<P> outcomes" 
  assume a2: "q \<in> \<P> outcomes" 
  assume a3: "r \<in> \<P> outcomes" 
  assume a4: "\<alpha> \<in> {0<..1}"
  have in_lots: "mix_pmf \<alpha> p r \<in> lotteries_on outcomes" "mix_pmf \<alpha> q r \<in> lotteries_on outcomes" 
    using a1 a3 a4 mix_in_lot apply fastforce
    using a2 a3 a4 mix_in_lot by fastforce
  have fnts: "finite (set_pmf p)" "finite (set_pmf q)" "finite (set_pmf r)"
    using a1 a2 a3 fnt infinite_super lotteries_on_def by blast+
  obtain u where
    u: "ordinal_utility (lotteries_on outcomes) \<R> (\<lambda>x. measure_pmf.expectation x u)"
    using assms by blast
  have "p \<succeq>[\<R>] q \<Longrightarrow> mix_pmf \<alpha> p r \<succeq>[\<R>] mix_pmf \<alpha> q r"
  proof -
    assume "p \<succeq>[\<R>] q"
    hence f: "measure_pmf.expectation p u \<ge> measure_pmf.expectation q u"
      using u a1 a2 ordinal_utility.util_def by fastforce
    have "measure_pmf.expectation (mix_pmf \<alpha> p r) u \<ge> measure_pmf.expectation (mix_pmf \<alpha> q r) u"
    proof -
      have "measure_pmf.expectation (mix_pmf \<alpha> p r) u = 
        \<alpha> * measure_pmf.expectation p u + (1 - \<alpha>) * measure_pmf.expectation r u"
        using expected_value_mix_pmf_distrib[of p r \<alpha> u] assms fnts a4 by fastforce
      moreover have "measure_pmf.expectation (mix_pmf \<alpha> q r) u = 
        \<alpha> * measure_pmf.expectation q u + (1 - \<alpha>) * measure_pmf.expectation r u"
        using expected_value_mix_pmf_distrib[of q r \<alpha> u] assms fnts a4 by fastforce
      ultimately show ?thesis using f using a4 by auto
    qed
    then show "mix_pmf \<alpha> p r \<succeq>[\<R>] mix_pmf \<alpha> q r"
      using u ordinal_utility_expected_value' ocU_is_expected_utility_bernoulli in_lots
      by (simp add: in_lots ordinal_utility_def)
  qed
  moreover have "mix_pmf \<alpha> p r \<succeq>[\<R>] mix_pmf \<alpha> q r \<Longrightarrow> p \<succeq>[\<R>] q" 
  proof -
    assume "mix_pmf \<alpha> p r \<succeq>[\<R>] mix_pmf \<alpha> q r"
    hence f:"measure_pmf.expectation (mix_pmf \<alpha> p r) u \<ge> measure_pmf.expectation (mix_pmf \<alpha> q r) u" 
      using ordinal_utility.ordinal_utility_left u by fastforce
    hence "measure_pmf.expectation p u \<ge> measure_pmf.expectation q u"
    proof -
      have "measure_pmf.expectation (mix_pmf \<alpha> p r) u = 
        \<alpha> * measure_pmf.expectation p u + (1 - \<alpha>) * measure_pmf.expectation r u"
        using expected_value_mix_pmf_distrib[of p r \<alpha> u] assms fnts a4 by fastforce
      moreover have "measure_pmf.expectation (mix_pmf \<alpha> q r) u = 
        \<alpha> * measure_pmf.expectation q u + (1 - \<alpha>) * measure_pmf.expectation r u"
        using expected_value_mix_pmf_distrib[of q r \<alpha> u] assms fnts a4 by fastforce
      ultimately show ?thesis using f using a4 by auto
    qed
    then show "p \<succeq>[\<R>] q"
      using a1 a2 ordinal_utility.util_def_conf u by fastforce
  qed
  ultimately show "p \<succeq>[\<R>] q = mix_pmf \<alpha> p r \<succeq>[\<R>] mix_pmf \<alpha> q r"
    by blast
qed

lemma exists_weight_for_equality:
  assumes "a > c" and "a \<ge> b" and "b \<ge> c"
  shows   "\<exists>(e::real) \<in> {0..1}. (1-e) * a + e * c = b"
proof -
  from assms have "b \<in> closed_segment a c"
    by (simp add: closed_segment_eq_real_ivl)
  thus ?thesis by (auto simp: closed_segment_def)
qed

lemma vNM_utilty_implies_continuity:
  assumes fnt: "finite outcomes" and "outcomes \<noteq> {}"
  assumes "\<exists>u. ordinal_utility (lotteries_on outcomes) \<R> (\<lambda>x. measure_pmf.expectation x u)"
  shows "continuous_vnm (lotteries_on outcomes) \<R>"
proof (rule continuous_vnmI)
  fix p q r
  assume a1: "p \<in> \<P> outcomes" 
  assume a2: "q \<in> \<P> outcomes" 
  assume a3: "r \<in> \<P> outcomes " 
  assume a4: "p \<succeq>[\<R>] q \<and> q \<succeq>[\<R>] r"
  then have g: "p \<succeq>[\<R>] r"
    by (meson assms(3) ordinal_utility.util_imp_trans transD)
  obtain u where 
    u: "ordinal_utility (lotteries_on outcomes) \<R> (\<lambda>x. measure_pmf.expectation x u)"
    using assms by blast
  have geqa: "measure_pmf.expectation p u \<ge> measure_pmf.expectation q u" 
    "measure_pmf.expectation q u \<ge> measure_pmf.expectation r u"
    using a4 u by (meson ordinal_utility.ordinal_utility_left)+
  have fnts: "finite p" "finite q" "finite r"
    using a1 a2 a3 fnt infinite_super lotteries_on_def by auto+
  consider "p \<succ>[\<R>] r" | "p \<approx>[\<R>] r"
    using g by auto
  then show "\<exists>\<alpha>\<in>{0..1}. mix_pmf \<alpha> p r \<approx>[\<R>] q"
  proof (cases)
    case 1
    define a where a: "a = measure_pmf.expectation p u"
    define b where b: "b = measure_pmf.expectation r u"
    define c where c: "c = measure_pmf.expectation q u"
    have "a > b"
      using "1" a1 a2 a3 a b ordinal_utility.util_def_conf u by force
    have "c \<le> a" "b \<le> c"
      using geqa a b c by blast+
    then obtain e ::real where
      e: "e \<in> {0..1}" "(1-e) * a + e * b = c"
      using exists_weight_for_equality[of b a c] \<open>b < a\<close> by blast
    have *:"1-e \<in> {0..1}"
      using e(1) by auto
    hence "measure_pmf.expectation (mix_pmf (1-e) p r) u = 
     (1-e) * measure_pmf.expectation p u + e * measure_pmf.expectation r u"
      using expected_value_mix_pmf_distrib[of p r "1-e" u] fnts by fastforce
    also have "... = (1-e) * a + e * b"
      using a b by auto
    also have "... = c"
      using c e by auto
    finally have f: "measure_pmf.expectation (mix_pmf (1-e) p r) u =  measure_pmf.expectation q u"
      using c by blast
    hence "mix_pmf (1-e) p r \<approx>[\<R>] q"
      using expected_value_is_utility_function[of outcomes "mix_pmf (1-e) p r" q \<R> u] *
    proof -
      have "mix_pmf (1 - e) p r \<in> \<P> outcomes"
        using \<open>1 - e \<in> {0..1}\<close> a1 a3 mix_in_lot by blast
      then show ?thesis
        using f a2 ordinal_utility.util_def u by fastforce
    qed 
    then show ?thesis
      using exists_weight_for_equality expected_value_mix_pmf_distrib * by blast
  next
    case 2
    have "r \<approx>[\<R>] q"
      by (meson "2" a4 assms(3) ordinal_utility.util_imp_trans transD)
    then show ?thesis  by force
  qed
qed

theorem Von_Neumann_Morgenstern_Utility_Theorem:
  assumes fnt: "finite outcomes" and "outcomes \<noteq> {}"
  shows "rational_preference (lotteries_on outcomes) \<R> \<and> 
         independent_vnm (lotteries_on outcomes) \<R> \<and> 
         continuous_vnm (lotteries_on outcomes) \<R> \<longleftrightarrow> 
   (\<exists>u. ordinal_utility (lotteries_on outcomes) \<R> (\<lambda>x. measure_pmf.expectation x u))"
  using vNM_utility_implies_independence[OF assms, of \<R>] 
    system_U_implies_vNM_utility[OF assms, of \<R>]
    vNM_utilty_implies_continuity[OF assms, of \<R>]
    ordinal_util_imp_rat_prefs[of "lotteries_on outcomes" \<R>] by auto


end
