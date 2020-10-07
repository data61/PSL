(* License: LGPL *)
(*
Author: Julian Parsert <julian.parsert@gmail.com>
Author: Cezary Kaliszyk
*)


section \<open> Utility Functions \<close>

text \<open> Utility functions and results involving them. \<close>

theory Utility_Functions
  imports
    Syntax
    Preferences
    "HOL-Analysis.Analysis"
begin


subsection "Ordinal utility functions"

text \<open> Ordinal utility function locale \<close>

locale ordinal_utility =
  fixes carrier :: "'a set"
  fixes relation :: "'a relation"
  fixes u :: "'a \<Rightarrow> real"
  assumes util_def[iff]: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> x \<succeq>[relation] y \<longleftrightarrow> u x \<ge> u y"
  assumes not_outside: "x \<succeq>[relation] y \<Longrightarrow> x \<in> carrier"
    and "x \<succeq>[relation] y \<Longrightarrow> y \<in> carrier"
begin

lemma util_def_conf: "x \<in> carrier \<Longrightarrow> y \<in> carrier \<Longrightarrow> u x \<ge> u y \<longleftrightarrow> x \<succeq>[relation] y"
  using util_def by blast

lemma relation_subset_crossp:
  "relation \<subseteq> carrier \<times> carrier"
proof
  fix x
  assume "x \<in> relation"
  have "\<forall>(a,b) \<in> relation. a \<in> carrier \<and> b \<in> carrier"
    by (metis (no_types, lifting) case_prod_conv ordinal_utility_axioms ordinal_utility_def surj_pair)
  then show "x \<in> carrier \<times> carrier"
    using \<open>x \<in> relation\<close> by auto
qed

text \<open> Utility function implies totality of relation \<close>
lemma util_imp_total: "total_on carrier relation"
proof
  fix x and y
  assume x_inc: "x \<in> carrier" and y_inc : "y \<in> carrier"
  have fst : "u x \<ge> u y \<or> u y \<ge> u x"
    using util_def by auto
  then show  "x \<succeq>[relation] y \<or> y \<succeq>[relation] x"
    by (simp add: x_inc y_inc)
qed

lemma x_y_in_carrier: "x \<succeq>[relation] y \<Longrightarrow> x \<in> carrier \<and> y \<in> carrier"
  by (meson ordinal_utility_axioms ordinal_utility_def)

text \<open> Utility function implies transitivity of relation. \<close>

lemma util_imp_trans: "trans relation"
proof (rule transI)
  fix x and y and z
  assume x_y: "x \<succeq>[relation] y"
  assume y_z: "y \<succeq>[relation] z"
  have x_ge_y: "x \<succeq>[relation] y"
    using x_y by auto
  then have x_y: "u x \<ge> u y"
    by (meson x_y_in_carrier ordinal_utility_axioms util_def x_y)
  have "u y \<ge> u z"
    by (meson y_z ordinal_utility_axioms ordinal_utility_def)
  have "x \<in> carrier"
    using x_y_in_carrier[of x y] x_ge_y  by simp
  then have "u x \<ge> u z"
    using \<open>u z \<le> u y\<close> order_trans x_y by blast
  hence "x \<succeq>[relation] z"
    by (meson \<open>x \<in> carrier\<close> ordinal_utility_axioms ordinal_utility_def y_z)
  then show "x \<succeq>[relation] z" .
qed

lemma util_imp_refl: "refl_on carrier relation"
  by (simp add: refl_on_def relation_subset_crossp)

lemma affine_trans_is_u:
  shows "\<forall>\<alpha>>0. (\<forall>\<beta>. ordinal_utility  carrier relation (\<lambda>x. u(x)*\<alpha> + \<beta>))"
proof (rule allI, rule impI, rule allI)
  fix \<alpha>::real and \<beta>
  assume *:"\<alpha> > 0"
  show "ordinal_utility carrier relation (\<lambda>x. u x * \<alpha> + \<beta>)"
  proof (subst ordinal_utility_def, rule conjI, goal_cases)
    case 1
    then show ?case
      by (metis * add.commute add_le_cancel_left not_le real_mult_less_iff1 util_def_conf)
  next
    case 2
    then show ?case 
      by (meson refl_on_domain util_imp_refl)
  qed
qed

text \<open> This utility function definition is ordinal.
        Hence they are only unique up to a monotone transformation. \<close>

lemma ordinality_of_utility_function :
  fixes f :: "real \<Rightarrow> real"
  assumes monot: "monotone (>) (>) f"
  shows "(f \<circ> u) x > (f \<circ> u) y \<longleftrightarrow> u x > u y"
proof -
  let ?func = "(\<lambda>x. f(u x))"
  have "\<forall>m n . u m \<ge> u n \<longleftrightarrow> ?func m \<ge> ?func n"
    by (metis le_less monot monotone_def not_less)
  hence "u x > u y \<longleftrightarrow> ?func x > ?func y"
    using not_le by blast
  thus ?thesis  by auto
qed

corollary utility_prefs_corresp :
  fixes f :: "real \<Rightarrow> real"
  assumes monotonicity : "monotone (>) (>) f"
  shows "\<forall>x\<in>carrier. \<forall>y\<in>carrier. (x,y) \<in> relation \<longleftrightarrow> (f \<circ> u) x \<ge> (f \<circ> u) y"
  by (meson monotonicity not_less ordinality_of_utility_function util_def_conf)

corollary monotone_comp_is_utility:
  fixes f :: "real \<Rightarrow> real"
  assumes monot: "monotone (>) (>) f"
  shows "ordinal_utility carrier relation (f \<circ> u)"
proof (rule ordinal_utility.intro, goal_cases)
case (1 x y)
  then show ?case
    using monot utility_prefs_corresp by blast
next
  case (2 x y)
  then show ?case
    using not_outside by blast
next
  case (3 x y)
  then show ?case
    using x_y_in_carrier by blast
qed

lemma ordinal_utility_left:
  assumes "x \<succeq>[relation] y"
  shows "u x \<ge> u y"
  using assms x_y_in_carrier by blast

lemma add_right:
  assumes "\<And>x y. x \<succeq>[relation] y \<Longrightarrow> f x \<ge> f y"
  shows   "ordinal_utility carrier relation (\<lambda>x. u x + f x)"
proof (rule ordinal_utility.intro, goal_cases)
  case (1 x y)
  assume xy: "x \<in> carrier" "y \<in> carrier"
  then show ?case
  proof -
    have "u x \<le> u y \<longrightarrow> (\<exists>r. ((x, y) \<notin> relation \<and> \<not> r \<le> u x + f x) \<and> r \<le> u y + f y) \<or> u y \<le> u x"
      by (metis (no_types) add_le_cancel_left add_le_cancel_right assms util_def xy(1) xy(2))
    moreover show ?thesis
      by (meson add_mono assms calculation le_cases order_trans util_def xy(1) xy(2))
  qed
next
  case (2 x y)
  then show ?case
    using not_outside by blast
next
  case (3 x y)
  then show ?case
    using x_y_in_carrier by blast
qed

lemma add_left:
  assumes "\<And>x y. x \<succeq>[relation] y \<Longrightarrow> f x \<ge> f y"
  shows "ordinal_utility carrier relation (\<lambda>x. f x + u x)"
proof -
  have "ordinal_utility carrier relation (\<lambda>x. u x + f x)"
    by (simp add: add_right assms)
  thus ?thesis using Groups.ab_semigroup_add_class.add.commute
    by (simp add: add.commute)
qed


lemma ordinal_utility_scale_transl:
  assumes "(c::real) > 0"
  shows "ordinal_utility carrier relation (\<lambda>x. c * (u x) + d)"
proof -
  have "monotone (>) (>) (\<lambda>x. c * x + d)" (is "monotone (>) (>) ?fn" )
    by (simp add: assms monotone_def)
  with monotone_comp_is_utility have "ordinal_utility carrier relation (?fn \<circ> u)"
    by blast
  moreover have "?fn \<circ> u =  (\<lambda>x. c * (u x) + d)"
    by auto
  finally show ?thesis
    by auto
qed

lemma strict_prefernce_iff_strict_utility:
  assumes "x \<in> carrier"
  assumes "y \<in> carrier"
  shows "x \<succ>[relation] y \<longleftrightarrow> u x > u y"
  by (meson assms(1) assms(2) less_eq_real_def not_less util_def)

end

text \<open> A utility function implies a rational preference relation.
      Hence a utility function contains exactly the same amount of information as a RPR \<close>

sublocale ordinal_utility \<subseteq> rational_preference carrier relation
proof
  fix x and y
  assume xy: "x \<succeq>[relation] y"
  then show "x \<in> carrier"
    and "y \<in> carrier"
    using not_outside by (simp)
      (meson xy refl_onD2 util_imp_refl)
next
  show "preorder_on carrier relation"
  proof-
    have "trans relation" using util_imp_trans by auto
    then have "preorder_on carrier relation"
      by (simp add: preorder_on_def util_imp_refl)
    then show ?thesis .
  qed
next
  show "total_on carrier relation"
    by (simp add: util_imp_total)
qed


text \<open> Given a finite carrier set. We can guarantee that given a rational preference
       relation, there must also exist a utility function representing this relation.
       Construction of witness roughly follows from.\<close>

theorem fnt_carrier_exists_util_fun:
  assumes "finite carrier"
  assumes "rational_preference carrier relation"
  shows "\<exists>u. ordinal_utility carrier relation u"
proof-
  define f where
    f: "f = (\<lambda>x. card (no_better_than x carrier relation))"
  have "ordinal_utility carrier relation f"
  proof
    fix x y
    assume x_c: "x \<in> carrier"
    assume y_c: "y \<in> carrier"
    show "x \<succeq>[relation] y \<longleftrightarrow> (real (f y) \<le> real (f x))"
    proof
      assume asm: "x \<succeq>[relation] y"
      define yn where
        yn: "yn = no_better_than y carrier relation"
      define xn where
        xn: "xn = no_better_than x carrier relation"
      then have "yn \<subseteq> xn"
        by (simp add: asm yn assms(2) rational_preference.no_better_subset_pref)
      then have "card yn \<le> card xn"
        by (simp add: x_c y_c asm assms(1) assms(2) rational_preference.card_leq_pref xn yn)
      then show "(real (f y) \<le> real (f x))"
        using  f xn yn by simp
    next
      assume "real (f y) \<le> real (f x)"
      then show "x \<succeq>[relation] y"
        using assms(1) assms(2) f rational_preference.card_leq_pref x_c y_c by fastforce
    qed
  next
    fix x y
    assume asm: "x \<succeq>[relation] y"
    show "x \<in> carrier"
      by (meson asm assms(2) preference.not_outside rational_preference.axioms(1))
    show "y \<in> carrier"
      by (meson asm assms(2) preference_def rational_preference_def)
  qed
  then show ?thesis
    by blast
qed

corollary obt_u_fnt_carrier:
  assumes "finite carrier"
  assumes "rational_preference carrier relation"
  obtains u where "ordinal_utility carrier relation u"
  using assms(1) assms(2) fnt_carrier_exists_util_fun by blast

theorem ordinal_util_imp_rat_prefs:
  assumes "ordinal_utility carrier relation u"
  shows "rational_preference carrier relation"
  by (metis (full_types) assms order_on_defs(1) ordinal_utility.util_imp_refl 
      ordinal_utility.util_imp_total ordinal_utility.util_imp_trans ordinal_utility_def 
      preference.intro rational_preference.intro rational_preference_axioms_def)

subsection \<open> Utility function on  Euclidean Space \<close>

locale eucl_ordinal_utility = ordinal_utility carrier relation u
  for carrier :: "('a::euclidean_space) set"
  and relation :: "'a relation"
  and u :: "'a \<Rightarrow> real"

sublocale eucl_ordinal_utility \<subseteq> rational_preference carrier relation
  using rational_preference_axioms by blast


lemma ord_eucl_utility_imp_rpr: "eucl_ordinal_utility s rel u \<longrightarrow> real_vector_rpr s rel"
  using eucl_ordinal_utility.axioms ordinal_util_imp_rat_prefs real_vector_rpr.intro by blast

context eucl_ordinal_utility
begin

text \<open> Local non-satiation on utility functions \<close>

lemma lns_pref_lns_util [iff]:
  "local_nonsatiation carrier relation \<longleftrightarrow>
  (\<forall>x\<in>carrier. \<forall>e > 0. \<exists>y\<in>carrier.
  norm (y - x) \<le> e \<and> u y > u x)" (is "_ \<longleftrightarrow> ?alt")
proof
  assume lns: "local_nonsatiation carrier relation"
  have "\<forall>a b. a \<succ> b \<longrightarrow> u a > u b"
    by (metis less_eq_real_def util_def x_y_in_carrier)
  then show "?alt"
    by (meson lns local_nonsatiation_def)
next
  assume lns: "?alt"
  show "local_nonsatiation carrier relation"
  proof(rule lns_normI)
    fix x and e::real
    assume x_in: "x \<in> carrier"
    assume e: "e > 0"
    have "\<forall>x \<in> carrier. \<forall>e>0. \<exists>y\<in>carrier. norm (y - x) \<le> e \<and> y \<succ> x"
      by (meson less_eq_real_def linorder_not_less lns util_def)
    have "\<exists>y\<in>carrier. norm (y - x) \<le> e \<and> u y > u x"
      using e x_in lns by blast
    then show "\<exists>y\<in>carrier. norm (y - x) \<le> e \<and> y \<succ> x"
      by (meson compl not_less util_def x_in)
  qed
qed

end

lemma finite_carrier_rpr_iff_u:
  assumes "finite carrier"
    and "(relation::'a relation) \<subseteq> carrier \<times> carrier"
  shows "rational_preference carrier relation \<longleftrightarrow> (\<exists>u. ordinal_utility carrier relation u)"
proof
  assume "rational_preference carrier relation" 
  then show "\<exists>u. ordinal_utility carrier relation u"
    by (simp add: assms(1) fnt_carrier_exists_util_fun)
next
  assume "\<exists>u. ordinal_utility carrier relation u"
  then show "rational_preference carrier relation" 
    by (metis (full_types) order_on_defs(1) ordinal_utility.util_imp_refl 
        ordinal_utility.util_imp_total ordinal_utility.util_imp_trans ordinal_utility_def 
        preference.intro rational_preference_axioms_def rational_preference_def)
qed


end