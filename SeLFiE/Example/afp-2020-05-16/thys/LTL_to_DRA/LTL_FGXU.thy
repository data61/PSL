(*
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>LTL (in Negation-Normal-Form, FGXU-Syntax)\<close>

theory LTL_FGXU
  imports Main "HOL-Library.Omega_Words_Fun"
begin

text \<open>Inspired/Based on schimpf/LTL\<close>

subsection \<open>Syntax\<close>

datatype (vars: 'a) ltl  =
    LTLTrue                       ("true")
  | LTLFalse                      ("false")
  | LTLProp 'a                    ("p'(_')")
  | LTLPropNeg 'a                 ("np'(_')" [86] 85)
  | LTLAnd "'a ltl" "'a ltl"      ("_ and _" [83,83] 82)
  | LTLOr "'a ltl" "'a ltl"       ("_ or _" [82,82] 81)
  | LTLNext "'a ltl"              ("X _" [88] 87)
  | LTLGlobal (theG: "'a ltl")    ("G _" [85] 84)
  | LTLFinal "'a ltl"             ("F _" [84] 83)
  | LTLUntil "'a ltl" "'a ltl"    ("_ U _" [87,87] 86)


subsection \<open>Semantics\<close>

fun ltl_semantics :: "['a set word, 'a ltl] \<Rightarrow> bool" (infix "\<Turnstile>" 80)
where
  "w \<Turnstile> true = True"
| "w \<Turnstile> false = False"
| "w \<Turnstile> p(q) = (q \<in> w 0)"
| "w \<Turnstile> np(q) = (q \<notin> w 0)"
| "w \<Turnstile> \<phi> and \<psi> = (w \<Turnstile> \<phi> \<and> w \<Turnstile> \<psi>)"
| "w \<Turnstile> \<phi> or \<psi> = (w \<Turnstile> \<phi> \<or> w \<Turnstile> \<psi>)"
| "w \<Turnstile> X \<phi> = (suffix 1 w \<Turnstile> \<phi>)"
| "w \<Turnstile> G \<phi> = (\<forall>k. suffix k w \<Turnstile> \<phi>)"
| "w \<Turnstile> F \<phi> = (\<exists>k. suffix k w \<Turnstile> \<phi>)"
| "w \<Turnstile> \<phi> U \<psi> = (\<exists>k. suffix k w \<Turnstile> \<psi> \<and> (\<forall>j < k. suffix j w \<Turnstile> \<phi>))"

fun ltl_prop_entailment :: "['a ltl set, 'a ltl] \<Rightarrow> bool" (infix "\<Turnstile>\<^sub>P" 80)
where
  "\<A> \<Turnstile>\<^sub>P true = True"
| "\<A> \<Turnstile>\<^sub>P false = False"
| "\<A> \<Turnstile>\<^sub>P \<phi> and \<psi> = (\<A> \<Turnstile>\<^sub>P \<phi> \<and> \<A> \<Turnstile>\<^sub>P \<psi>)"
| "\<A> \<Turnstile>\<^sub>P \<phi> or \<psi> = (\<A> \<Turnstile>\<^sub>P \<phi> \<or> \<A> \<Turnstile>\<^sub>P \<psi>)"
| "\<A> \<Turnstile>\<^sub>P \<phi> = (\<phi> \<in> \<A>)"

subsubsection \<open>Properties\<close>

lemma LTL_G_one_step_unfolding:
  "w \<Turnstile> G \<phi> \<longleftrightarrow> (w \<Turnstile> \<phi> \<and> w \<Turnstile> X (G \<phi>))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  hence "w \<Turnstile> \<phi>"
    using suffix_0[of w] ltl_semantics.simps(8)[of w \<phi>] by metis
  moreover
  from \<open>?lhs\<close> have "w \<Turnstile> X (G \<phi>)"
    by simp
  ultimately
  show ?rhs by simp
next
  assume ?rhs
  hence "w \<Turnstile> X (G \<phi>)" by simp
  hence "\<forall>k. suffix (k + 1) w \<Turnstile> \<phi>" by force
  hence "\<forall>k > 0. suffix k w \<Turnstile> \<phi>"
    by (metis Suc_eq_plus1 gr0_implies_Suc)
  moreover
  from \<open>?rhs\<close> have "(suffix 0 w) \<Turnstile> \<phi>" by simp
  ultimately
  show ?lhs
    using neq0_conv ltl_semantics.simps(8)[of w \<phi>] by blast
qed

lemma LTL_F_one_step_unfolding:
  "w \<Turnstile> F \<phi> \<longleftrightarrow> (w \<Turnstile> \<phi> \<or> w \<Turnstile> X (F \<phi>))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain k where "suffix k w \<Turnstile> \<phi>" by fastforce
  thus ?rhs by (cases k) auto
next
  assume ?rhs
  thus ?lhs
    using suffix_0[of w] suffix_suffix[of _ 1 w] by (metis ltl_semantics.simps(7) ltl_semantics.simps(9))
qed

lemma LTL_U_one_step_unfolding:
  "w \<Turnstile> \<phi> U \<psi> \<longleftrightarrow> (w \<Turnstile> \<psi> \<or> (w \<Turnstile> \<phi> \<and> w \<Turnstile> X (\<phi> U \<psi>)))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain k where "suffix k w \<Turnstile> \<psi>" and "\<forall>j<k. suffix j w \<Turnstile> \<phi>"
    by force
  thus ?rhs
    by (cases k) auto
next
  assume ?rhs
  thus ?lhs
  proof (cases "w \<Turnstile> \<psi>")
    case False
      hence "w \<Turnstile> \<phi> \<and> w \<Turnstile> X (\<phi> U \<psi>)"
        using \<open>?rhs\<close> by blast
      obtain k where "suffix k (suffix 1 w) \<Turnstile> \<psi>" and "\<forall>j<k. suffix j (suffix 1 w) \<Turnstile> \<phi>"
        using False \<open>?rhs\<close> by force
      moreover
      {
        fix j assume "j < 1 + k"
        hence "suffix j w \<Turnstile> \<phi>"
          using \<open>w \<Turnstile> \<phi> \<and> w \<Turnstile> X (\<phi> U \<psi>)\<close> \<open>\<forall>j<k. suffix j (suffix 1 w) \<Turnstile> \<phi>\<close>[unfolded suffix_suffix]
          by (cases j) simp+
      }
      ultimately
      show ?thesis
        by auto
  qed force
qed

lemma LTL_GF_infinitely_many_suffixes:
  "w \<Turnstile> G (F \<phi>) = (\<exists>\<^sub>\<infinity>i. suffix i w \<Turnstile> \<phi>)"
  (is "?lhs = ?rhs")
proof
  let ?S = "{i | i j. suffix (i + j) w \<Turnstile> \<phi>}"
  let ?S' = "{i + j | i j. suffix (i + j) w \<Turnstile> \<phi>}"

  assume ?lhs
  hence "infinite ?S"
    by auto
  moreover
  have "\<forall>s \<in> ?S. \<exists>s' \<in> ?S'. s \<le> s'"
    by fastforce
  ultimately
  have "infinite ?S'"
    using infinite_nat_iff_unbounded_le le_trans by meson
  moreover
  have "?S' = {k | k. suffix k w \<Turnstile> \<phi>}"
    using monoid_add_class.add.left_neutral by metis
  ultimately
  have "infinite {k | k. suffix k w \<Turnstile> \<phi>}"
    by metis
  thus ?rhs unfolding Inf_many_def by force
next
  assume ?rhs
  {
    fix i
    from \<open>?rhs\<close> obtain k where "i \<le> k" and "suffix k w \<Turnstile> \<phi>"
      using INFM_nat_le[of "\<lambda>n. suffix n w \<Turnstile> \<phi>"] by blast
    then obtain j where "k = i + j"
      using le_iff_add[of i k] by fast
    hence "suffix j (suffix i w) \<Turnstile> \<phi>"
      using \<open>suffix k w \<Turnstile> \<phi>\<close> suffix_suffix by fastforce
    hence "suffix i w \<Turnstile> F \<phi>" by auto
  }
  thus ?lhs by auto
qed

lemma LTL_FG_almost_all_suffixes:
  "w \<Turnstile> F G \<phi> = (\<forall>\<^sub>\<infinity>i. suffix i w \<Turnstile> \<phi>)"
  (is "?lhs = ?rhs")
proof
  let ?S = "{k. \<not> suffix k w \<Turnstile> \<phi>}"

  assume ?lhs
  then obtain i where "suffix i w \<Turnstile> G \<phi>"
    by fastforce
  hence "\<And>j. j \<ge> i \<Longrightarrow> (suffix j w \<Turnstile> \<phi>)"
    using le_iff_add[of i] by auto
  hence "\<And>j. \<not>suffix j w \<Turnstile> \<phi> \<Longrightarrow> j < i"
    using le_less_linear by blast
  hence "?S \<subseteq> {k. k < i}"
    by blast
  hence "finite ?S"
    using finite_subset by fast
  thus ?rhs
    unfolding Alm_all_def Inf_many_def by presburger
next
  assume ?rhs
  obtain S where S_def: "S = {k. \<not> suffix k w \<Turnstile> \<phi>}" by blast
  hence "finite S"
    using \<open>?rhs\<close> unfolding Alm_all_def Inf_many_def by fast
  then obtain i where "i = Max S" by blast
  {
    fix j
    assume "i < j"
    hence "j \<notin> S"
      using \<open>i = Max S\<close> Max.coboundedI[OF \<open>finite S\<close>] less_le_not_le by blast
    hence "suffix j w \<Turnstile> \<phi>" using S_def by fast
  }
  hence "\<forall>j > i. (suffix j w \<Turnstile> \<phi>)" by simp
  hence "suffix (Suc i) w \<Turnstile> G \<phi>" by auto
  thus ?lhs
    using ltl_semantics.simps(9)[of w "G \<phi>"] by blast
qed

lemma LTL_FG_suffix:
  "(suffix i w) \<Turnstile> F (G \<phi>) = w \<Turnstile> F (G \<phi>)"
proof -
  have "(\<exists>m. \<forall>n\<ge>m. suffix n w \<Turnstile> \<phi>) = (\<exists>m. \<forall>n\<ge>m. suffix n (suffix i w) \<Turnstile> \<phi>)" (is "?l = ?r")
  proof
    assume ?r
    then obtain m where "\<forall>n\<ge>m. suffix n (suffix i w) \<Turnstile> \<phi>"
      by blast
    hence "\<forall>n\<ge>i+m. suffix n w \<Turnstile> \<phi>"
      unfolding suffix_suffix by (metis le_iff_add add_leE add_le_cancel_left)
    thus ?l
      by auto
  qed (metis suffix_suffix trans_le_add2)
  thus ?thesis
    unfolding LTL_FG_almost_all_suffixes MOST_nat_le ..
qed

lemma LTL_GF_suffix:
  "(suffix i w) \<Turnstile> G (F \<phi>) = w \<Turnstile> G (F \<phi>)"
proof -
  have "(\<forall>m. \<exists>n\<ge>m. suffix n w \<Turnstile> \<phi>) = (\<forall>m. \<exists>n\<ge>m. suffix n (suffix i w) \<Turnstile> \<phi>)" (is "?l = ?r")
  proof
    assume ?l
    thus ?r
      by (metis suffix_suffix add_leE add_le_cancel_left le_Suc_ex)
  qed (metis suffix_suffix trans_le_add2)
  thus ?thesis
    unfolding LTL_GF_infinitely_many_suffixes INFM_nat_le ..
qed

lemma LTL_suffix_G:
  "w \<Turnstile> G \<phi> \<Longrightarrow> suffix i w \<Turnstile> G \<phi>"
  using suffix_0 suffix_suffix by (induction i) simp_all

lemma LTL_prop_entailment_monotonI[intro]:
  "S \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> S' \<Turnstile>\<^sub>P \<phi>"
  by (induction rule: ltl_prop_entailment.induct) auto

lemma ltl_models_equiv_prop_entailment:
  "w \<Turnstile> \<phi> = {\<chi>. w \<Turnstile> \<chi>} \<Turnstile>\<^sub>P \<phi>"
  by (induction \<phi>) auto

subsubsection \<open>Limit Behaviour of the G-operator\<close>

abbreviation Only_G
where
  "Only_G S \<equiv> \<forall>x \<in> S. \<exists>y. x = G y"

lemma ltl_G_stabilize:
  assumes "finite \<G>"
  assumes "Only_G \<G>"
  obtains i where "\<And>\<chi> j. \<chi> \<in> \<G> \<Longrightarrow> suffix i w \<Turnstile> \<chi> = suffix (i + j) w \<Turnstile> \<chi>"
proof -
  have "finite \<G> \<Longrightarrow> Only_G \<G> \<Longrightarrow> \<exists>i. \<forall>\<chi> \<in> \<G>. \<forall>j. suffix i w \<Turnstile> \<chi> = suffix (i + j) w \<Turnstile> \<chi>"
  proof (induction rule: finite_induct)
    case (insert \<chi> \<G>)
      then obtain i\<^sub>1  where "\<And>\<chi> j. \<chi> \<in> \<G> \<Longrightarrow> suffix i\<^sub>1 w \<Turnstile> \<chi> = suffix (i\<^sub>1 + j) w \<Turnstile> \<chi>"
        by blast
      moreover
      from insert obtain \<psi> where "\<chi> = G \<psi>"
        by blast
      have "\<exists>i. \<forall>j. suffix i w \<Turnstile> G \<psi> = suffix (i + j) w \<Turnstile> G \<psi>"
        by (metis LTL_suffix_G plus_nat.add_0 suffix_0 suffix_suffix)
      then obtain i\<^sub>2 where "\<And>j. suffix i\<^sub>2 w \<Turnstile> \<chi> = suffix (i\<^sub>2 + j) w \<Turnstile> \<chi>"
        unfolding \<open>\<chi> = G \<psi>\<close> by blast
      ultimately
      have "\<And>\<chi>' j. \<chi>' \<in> \<G> \<union> {\<chi>} \<Longrightarrow> suffix (i\<^sub>1 + i\<^sub>2) w \<Turnstile> \<chi>' = suffix (i\<^sub>1 + i\<^sub>2 + j) w \<Turnstile> \<chi>'"
        unfolding Un_iff singleton_iff by (metis add.commute add.left_commute)
      thus ?case
        by blast
  qed simp
  with assms obtain i where "\<And>\<chi> j. \<chi> \<in> \<G> \<Longrightarrow> suffix i w \<Turnstile> \<chi> = suffix (i + j) w \<Turnstile> \<chi>"
    by blast
  thus ?thesis
    using that by blast
qed

lemma ltl_G_stabilize_property:
  assumes "finite \<G>"
  assumes "Only_G \<G>"
  assumes "\<And>\<chi> j. \<chi> \<in> \<G> \<Longrightarrow> suffix i w \<Turnstile> \<chi> = suffix (i + j) w \<Turnstile> \<chi>"
  assumes "G \<psi> \<in> \<G> \<inter> {\<chi>. w \<Turnstile> F \<chi>}"
  shows "suffix i w \<Turnstile> G \<psi>"
proof -
  obtain j where "suffix j w \<Turnstile> G \<psi>"
    using assms by fastforce
  thus "suffix i w \<Turnstile> G \<psi>"
    by (cases "i \<le> j", insert assms, unfold le_iff_add, blast,
        metis (erased, lifting) LTL_suffix_G \<open>suffix j w \<Turnstile> G \<psi>\<close> le_add_diff_inverse nat_le_linear suffix_suffix)
qed

subsection \<open>Subformulae\<close>

subsubsection \<open>Propositions\<close>

fun propos :: "'a ltl \<Rightarrow>'a ltl set"
where
  "propos true = {}"
| "propos false = {}"
| "propos (\<phi> and \<psi>) = propos \<phi> \<union> propos \<psi>"
| "propos (\<phi> or \<psi>) = propos \<phi> \<union> propos \<psi>"
| "propos \<phi> = {\<phi>}"

fun nested_propos :: "'a ltl \<Rightarrow>'a ltl set"
where
  "nested_propos true = {}"
| "nested_propos false = {}"
| "nested_propos (\<phi> and \<psi>) = nested_propos \<phi> \<union> nested_propos \<psi>"
| "nested_propos (\<phi> or \<psi>) = nested_propos \<phi> \<union> nested_propos \<psi>"
| "nested_propos (F \<phi>) = {F \<phi>} \<union> nested_propos \<phi>"
| "nested_propos (G \<phi>) = {G \<phi>} \<union> nested_propos \<phi>"
| "nested_propos (X \<phi>) = {X \<phi>} \<union> nested_propos \<phi>"
| "nested_propos (\<phi> U \<psi>) = {\<phi> U \<psi>} \<union> nested_propos \<phi> \<union> nested_propos \<psi>"
| "nested_propos \<phi> = {\<phi>}"

lemma finite_propos:
  "finite (propos \<phi>)" "finite (nested_propos \<phi>)"
  by (induction \<phi>) simp+

lemma propos_subset:
  "propos \<phi> \<subseteq> nested_propos \<phi>"
  by (induction \<phi>) auto

lemma LTL_prop_entailment_restrict_to_propos:
  "S \<Turnstile>\<^sub>P \<phi> = (S \<inter> propos \<phi>) \<Turnstile>\<^sub>P \<phi>"
  by (induction \<phi>) auto

lemma propos_foldl:
  assumes "\<And>x y. propos (f x y) = propos x \<union> propos y"
  shows "\<Union>{propos y |y. y = i \<or> y \<in> set xs} = propos (foldl f i xs)"
proof (induction xs rule: rev_induct)
  case (snoc x xs)
    have "\<Union>{propos y |y. y = i \<or> y \<in> set (xs@[x])} = \<Union>{propos y |y. y = i \<or> y \<in> set xs} \<union> propos x"
      by auto
    also
    have "\<dots> = propos (foldl f i xs) \<union> propos x"
      using snoc by auto
    also
    have "\<dots> = propos (foldl f i (xs@[x]))"
      using assms by simp
    finally
    show ?case .
qed simp

subsubsection \<open>G-Subformulae\<close>

text \<open>Notation for paper: mathds{G}\<close>

fun G_nested_propos :: "'a ltl \<Rightarrow>'a ltl set" ("\<^bold>G")
where
  "\<^bold>G (\<phi> and \<psi>) = \<^bold>G \<phi> \<union> \<^bold>G \<psi>"
| "\<^bold>G (\<phi> or \<psi>) = \<^bold>G \<phi> \<union> \<^bold>G \<psi>"
| "\<^bold>G (F \<phi>) = \<^bold>G \<phi>"
| "\<^bold>G (G \<phi>) = \<^bold>G \<phi> \<union> {G \<phi>}"
| "\<^bold>G (X \<phi>) = \<^bold>G \<phi>"
| "\<^bold>G (\<phi> U \<psi>) = \<^bold>G \<phi> \<union> \<^bold>G \<psi>"
| "\<^bold>G \<phi> = {}"

lemma G_nested_finite:
  "finite (\<^bold>G \<phi>)"
  by (induction \<phi>) auto

lemma G_nested_propos_alt_def:
  "\<^bold>G \<phi> = nested_propos \<phi> \<inter> {\<psi>. (\<exists>x. \<psi> = G x)}"
  by (induction \<phi>) auto

lemma G_nested_propos_Only_G:
  "Only_G (\<^bold>G \<phi>)"
  unfolding G_nested_propos_alt_def by blast

lemma G_not_in_G:
  "G \<phi> \<notin> \<^bold>G \<phi>"
proof -
  have "\<And>\<chi>. \<chi> \<in> \<^bold>G \<phi> \<Longrightarrow> size \<phi> \<ge> size \<chi>"
    by (induction \<phi>) fastforce+
  thus ?thesis
    by fastforce
qed

lemma G_subset_G:
  "\<psi> \<in> \<^bold>G \<phi> \<Longrightarrow> \<^bold>G \<psi> \<subseteq> \<^bold>G \<phi>"
  "G \<psi> \<in> \<^bold>G \<phi> \<Longrightarrow> \<^bold>G \<psi> \<subseteq> \<^bold>G \<phi>"
  by (induction \<phi>) auto

lemma \<G>_properties:
  assumes "\<G> \<subseteq> \<^bold>G \<phi>"
  shows \<G>_finite: "finite \<G>" and \<G>_elements: "Only_G \<G>"
  using assms G_nested_finite G_nested_propos_alt_def by (blast dest: finite_subset)+

subsection \<open>Propositional Implication and Equivalence\<close>

definition ltl_prop_implies :: "['a ltl, 'a ltl] \<Rightarrow> bool" (infix "\<longrightarrow>\<^sub>P" 75)
where
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<equiv> \<forall>\<A>. \<A> \<Turnstile>\<^sub>P \<phi> \<longrightarrow> \<A> \<Turnstile>\<^sub>P \<psi>"

definition ltl_prop_equiv :: "['a ltl, 'a ltl] \<Rightarrow> bool" (infix "\<equiv>\<^sub>P" 75)
where
  "\<phi> \<equiv>\<^sub>P \<psi> \<equiv> \<forall>\<A>. \<A> \<Turnstile>\<^sub>P \<phi> \<longleftrightarrow> \<A> \<Turnstile>\<^sub>P \<psi>"

lemma ltl_prop_implies_equiv:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<and> \<psi> \<longrightarrow>\<^sub>P \<phi> \<longleftrightarrow> \<phi> \<equiv>\<^sub>P \<psi>"
  unfolding ltl_prop_implies_def ltl_prop_equiv_def by meson

lemma ltl_prop_equiv_equivp:
  "equivp (\<equiv>\<^sub>P)"
  by (blast intro: equivpI[of "(\<equiv>\<^sub>P)", simplified transp_def symp_def reflp_def ltl_prop_equiv_def])

lemma [trans]:
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> \<psi> \<equiv>\<^sub>P \<chi> \<Longrightarrow> \<phi> \<equiv>\<^sub>P \<chi>"
  using ltl_prop_equiv_equivp[THEN equivp_transp] .

subsubsection \<open>Quotient Type for Propositional Equivalence\<close>

quotient_type 'a ltl_prop_equiv_quotient = "'a ltl" / "(\<equiv>\<^sub>P)"
  morphisms Rep Abs
  by (simp add: ltl_prop_equiv_equivp)

type_synonym 'a ltl\<^sub>P = "'a ltl_prop_equiv_quotient"

instantiation ltl_prop_equiv_quotient :: (type) equal begin

lift_definition ltl_prop_equiv_quotient_eq_test :: "'a ltl\<^sub>P \<Rightarrow> 'a ltl\<^sub>P \<Rightarrow> bool" is "\<lambda>x y. x \<equiv>\<^sub>P y"
  by (metis ltl_prop_equiv_quotient.abs_eq_iff)

definition
  eq: "equal_class.equal \<equiv> ltl_prop_equiv_quotient_eq_test"

instance
  by (standard; simp add: eq ltl_prop_equiv_quotient_eq_test.rep_eq, metis Quotient_ltl_prop_equiv_quotient Quotient_rel_rep)

end

lemma ltl\<^sub>P_abs_rep: "Abs (Rep \<phi>) = \<phi>"
  by (meson Quotient3_abs_rep Quotient3_ltl_prop_equiv_quotient)

lift_definition ltl_prop_entails_abs :: "'a ltl set \<Rightarrow> 'a ltl\<^sub>P \<Rightarrow> bool" ("_ \<up>\<Turnstile>\<^sub>P _") is "(\<Turnstile>\<^sub>P)"
  by (simp add: ltl_prop_equiv_def)

lift_definition ltl_prop_implies_abs :: "'a ltl\<^sub>P \<Rightarrow> 'a ltl\<^sub>P \<Rightarrow> bool" ("_ \<up>\<longrightarrow>\<^sub>P _") is "(\<longrightarrow>\<^sub>P)"
  by (simp add: ltl_prop_equiv_def ltl_prop_implies_def)

subsubsection \<open>Propositional Equivalence implies LTL Equivalence\<close>

lemma ltl_prop_implication_implies_ltl_implication:
  "w \<Turnstile> \<phi> \<Longrightarrow> \<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> w \<Turnstile> \<psi>"
  using [[unfold_abs_def = false]]
  unfolding ltl_prop_implies_def ltl_models_equiv_prop_entailment by simp

lemma ltl_prop_equiv_implies_ltl_equiv:
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> w \<Turnstile> \<phi> = w \<Turnstile> \<psi>"
  using ltl_prop_implication_implies_ltl_implication ltl_prop_implies_equiv by blast

subsection \<open>Substitution\<close>

fun subst :: "'a ltl \<Rightarrow> ('a ltl \<rightharpoonup> 'a ltl) \<Rightarrow> 'a ltl"
where
  "subst true m = true"
| "subst false m = false"
| "subst (\<phi> and \<psi>) m = subst \<phi> m and subst \<psi> m"
| "subst (\<phi> or \<psi>) m = subst \<phi> m or subst \<psi> m"
| "subst \<phi> m = (case m \<phi> of Some \<phi>' \<Rightarrow> \<phi>' | None \<Rightarrow> \<phi>)"

text \<open>Based on Uwe Schoening's Translation Lemma (Logic for CS, p. 54)\<close>

lemma ltl_prop_equiv_subst_S:
  "S \<Turnstile>\<^sub>P subst \<phi> m = ((S - dom m) \<union> {\<chi> | \<chi> \<chi>'. \<chi> \<in> dom m \<and> m \<chi> = Some \<chi>' \<and> S \<Turnstile>\<^sub>P \<chi>'}) \<Turnstile>\<^sub>P \<phi>"
  by (induction \<phi>) (auto split: option.split)

lemma subst_respects_ltl_prop_entailment:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> subst \<phi> m \<longrightarrow>\<^sub>P subst \<psi> m"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> subst \<phi> m \<equiv>\<^sub>P subst \<psi> m"
  unfolding ltl_prop_equiv_def ltl_prop_implies_def ltl_prop_equiv_subst_S by blast+

lemma subst_respects_ltl_prop_entailment_generalized:
  "(\<And>\<A>. (\<And>x. x \<in> S \<Longrightarrow> \<A> \<Turnstile>\<^sub>P x) \<Longrightarrow> \<A> \<Turnstile>\<^sub>P y) \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> \<A> \<Turnstile>\<^sub>P subst x m) \<Longrightarrow> \<A> \<Turnstile>\<^sub>P subst y m"
  unfolding ltl_prop_equiv_subst_S by simp

lemma decomposable_function_subst:
  "\<lbrakk>f true = true; f false = false; \<And>\<phi> \<psi>. f (\<phi> and \<psi>) = f \<phi> and f \<psi>; \<And>\<phi> \<psi>. f (\<phi> or \<psi>) = f \<phi> or f \<psi>\<rbrakk> \<Longrightarrow> f \<phi> = subst \<phi> (\<lambda>\<chi>. Some (f \<chi>))"
  by (induction \<phi>) auto

subsection \<open>Additional Operators\<close>

subsubsection \<open>And\<close>

lemma foldl_LTLAnd_prop_entailment:
  "S \<Turnstile>\<^sub>P foldl LTLAnd i xs = (S \<Turnstile>\<^sub>P i \<and> (\<forall>y \<in> set xs. S \<Turnstile>\<^sub>P y))"
  by (induction xs arbitrary: i) auto

fun And :: "'a ltl list \<Rightarrow> 'a ltl"
where
  "And [] = true"
| "And (x#xs) = foldl LTLAnd x xs"

lemma And_prop_entailment:
  "S \<Turnstile>\<^sub>P And xs = (\<forall>x \<in> set xs. S \<Turnstile>\<^sub>P x)"
  using foldl_LTLAnd_prop_entailment by (cases xs) auto

lemma And_propos:
  "propos (And xs) = \<Union>{propos x| x. x \<in> set xs}"
proof (cases xs)
  case Nil
    thus ?thesis by simp
next
  case (Cons x xs)
    thus ?thesis
      using propos_foldl[of LTLAnd x] by auto
qed

lemma And_semantics:
  "w \<Turnstile> And xs = (\<forall>x \<in> set xs. w \<Turnstile> x)"
proof -
  have And_propos': "\<And>x. x \<in> set xs \<Longrightarrow> propos x \<subseteq> propos (And xs)"
    using And_propos by blast

  have "w \<Turnstile> And xs = {\<chi>. \<chi> \<in> propos (And xs) \<and> w \<Turnstile> \<chi>} \<Turnstile>\<^sub>P (And xs)"
    using ltl_models_equiv_prop_entailment LTL_prop_entailment_restrict_to_propos by blast
  also
  have "\<dots> = (\<forall>x \<in> set xs. {\<chi>. \<chi> \<in> propos (And xs) \<and> w \<Turnstile> \<chi>} \<Turnstile>\<^sub>P x)"
    using And_prop_entailment by auto
  also
  have "\<dots> = (\<forall>x \<in> set xs. {\<chi>. \<chi> \<in> propos x \<and> w \<Turnstile> \<chi>} \<Turnstile>\<^sub>P x)"
    using LTL_prop_entailment_restrict_to_propos And_propos' by blast
  also
  have "\<dots> = (\<forall>x \<in> set xs. w \<Turnstile> x)"
    using ltl_models_equiv_prop_entailment LTL_prop_entailment_restrict_to_propos by blast
  finally
  show ?thesis .
qed

lemma And_append_syntactic:
  "xs \<noteq> [] \<Longrightarrow> And (xs @ ys) = And ((And xs)#ys)"
  by (induction xs rule: list_nonempty_induct) simp+

lemma And_append_S:
  "S \<Turnstile>\<^sub>P And (xs @ ys) = S \<Turnstile>\<^sub>P And xs and And ys"
  using And_prop_entailment[of S] by auto

lemma And_append:
  "And (xs @ ys) \<equiv>\<^sub>P And xs and And ys"
  unfolding ltl_prop_equiv_def using And_append_S by blast

subsubsection \<open>Lifted Variant\<close>

lift_definition and_abs :: "'a ltl\<^sub>P \<Rightarrow> 'a ltl\<^sub>P \<Rightarrow> 'a ltl\<^sub>P" ("_ \<up>and _") is "\<lambda>x y. x and y"
  unfolding ltl_prop_equiv_def by simp

fun And_abs :: "'a ltl\<^sub>P list \<Rightarrow> 'a ltl\<^sub>P" ("\<up>And")
where
  "\<up>And xs = foldl and_abs (Abs true) xs"

lemma foldl_LTLAnd_prop_entailment_abs:
  "S \<up>\<Turnstile>\<^sub>P foldl and_abs i xs = (S \<up>\<Turnstile>\<^sub>P i \<and> (\<forall>y\<in>set xs. S \<up>\<Turnstile>\<^sub>P y))"
  by (induction xs arbitrary: i)
     (simp_all add: and_abs_def ltl_prop_entails_abs.abs_eq, metis ltl_prop_entails_abs.rep_eq)

lemma And_prop_entailment_abs:
  "S \<up>\<Turnstile>\<^sub>P \<up>And xs = (\<forall>x \<in> set xs. S \<up>\<Turnstile>\<^sub>P x)"
  by (simp add: foldl_LTLAnd_prop_entailment_abs ltl_prop_entails_abs.abs_eq)

lemma and_abs_conjunction:
  "S \<up>\<Turnstile>\<^sub>P \<phi> \<up>and \<psi> \<longleftrightarrow> S \<up>\<Turnstile>\<^sub>P \<phi> \<and> S \<up>\<Turnstile>\<^sub>P \<psi>"
  by (metis and_abs.abs_eq ltl\<^sub>P_abs_rep ltl_prop_entailment.simps(3) ltl_prop_entails_abs.abs_eq)

subsubsection \<open>Or\<close>

lemma foldl_LTLOr_prop_entailment:
  "S \<Turnstile>\<^sub>P foldl LTLOr i xs = (S \<Turnstile>\<^sub>P i \<or> (\<exists>y \<in> set xs. S \<Turnstile>\<^sub>P y))"
  by (induction xs arbitrary: i) auto

fun Or :: "'a ltl list \<Rightarrow> 'a ltl"
where
  "Or [] = false"
| "Or (x#xs) = foldl LTLOr x xs"

lemma Or_prop_entailment:
  "S \<Turnstile>\<^sub>P Or xs = (\<exists>x \<in> set xs. S \<Turnstile>\<^sub>P x)"
  using foldl_LTLOr_prop_entailment by (cases xs) auto

lemma Or_propos:
  "propos (Or xs) = \<Union>{propos x| x. x \<in> set xs}"
proof (cases xs)
  case Nil
    thus ?thesis by simp
next
  case (Cons x xs)
    thus ?thesis
      using propos_foldl[of LTLOr x] by auto
qed

lemma Or_semantics:
  "w \<Turnstile> Or xs = (\<exists>x \<in> set xs. w \<Turnstile> x)"
proof -
  have Or_propos': "\<And>x. x \<in> set xs \<Longrightarrow> propos x \<subseteq> propos (Or xs)"
    using Or_propos by blast

  have "w \<Turnstile> Or xs = {\<chi>. \<chi> \<in> propos (Or xs) \<and> w \<Turnstile> \<chi>} \<Turnstile>\<^sub>P (Or xs)"
    using ltl_models_equiv_prop_entailment LTL_prop_entailment_restrict_to_propos by blast
  also
  have "\<dots> = (\<exists>x \<in> set xs. {\<chi>. \<chi> \<in> propos (Or xs) \<and> w \<Turnstile> \<chi>} \<Turnstile>\<^sub>P x)"
    using Or_prop_entailment by auto
  also
  have "\<dots> = (\<exists>x \<in> set xs. {\<chi>. \<chi> \<in> propos x \<and> w \<Turnstile> \<chi>} \<Turnstile>\<^sub>P x)"
    using LTL_prop_entailment_restrict_to_propos Or_propos' by blast
  also
  have "\<dots> = (\<exists>x \<in> set xs. w \<Turnstile> x)"
    using ltl_models_equiv_prop_entailment LTL_prop_entailment_restrict_to_propos by blast
  finally
  show ?thesis .
qed

lemma Or_append_syntactic:
  "xs \<noteq> [] \<Longrightarrow> Or (xs @ ys) = Or ((Or xs)#ys)"
  by (induction xs rule: list_nonempty_induct) simp+

lemma Or_append_S:
  "S \<Turnstile>\<^sub>P Or (xs @ ys) = S \<Turnstile>\<^sub>P Or xs or Or ys"
  using Or_prop_entailment[of S] by auto

lemma Or_append:
  "Or (xs @ ys) \<equiv>\<^sub>P Or xs or Or ys"
  unfolding ltl_prop_equiv_def using Or_append_S by blast

subsubsection \<open>$eval_G$\<close>

\<comment> \<open>Partly evaluate a formula by only considering G-subformulae\<close>

fun eval\<^sub>G
where
  "eval\<^sub>G S (\<phi> and \<psi>) = eval\<^sub>G S \<phi> and eval\<^sub>G S \<psi>"
| "eval\<^sub>G S (\<phi> or \<psi>) = eval\<^sub>G S \<phi> or eval\<^sub>G S \<psi>"
| "eval\<^sub>G S (G \<phi>) = (if G \<phi> \<in> S then true else false)"
| "eval\<^sub>G S \<phi> = \<phi>"

\<comment> \<open>Syntactic Properties\<close>

lemma eval\<^sub>G_And_map:
  "eval\<^sub>G S (And xs) = And (map (eval\<^sub>G S) xs)"
proof (induction xs rule: rev_induct)
  case (snoc x xs)
    thus ?case
      by (cases xs) simp+
qed simp

lemma eval\<^sub>G_Or_map:
  "eval\<^sub>G S (Or xs) = Or (map (eval\<^sub>G S) xs)"
proof (induction xs rule: rev_induct)
  case (snoc x xs)
    thus ?case
      by (cases xs) simp+
qed simp

lemma eval\<^sub>G_G_nested:
  "\<^bold>G (eval\<^sub>G \<G> \<phi>) \<subseteq> \<^bold>G \<phi>"
  by (induction \<phi>) (simp_all, blast+)

lemma eval\<^sub>G_subst:
  "eval\<^sub>G S \<phi> = subst \<phi> (\<lambda>\<chi>. Some (eval\<^sub>G S \<chi>))"
  by (induction \<phi>) simp_all

\<comment> \<open>Semantic Properties\<close>

lemma eval\<^sub>G_prop_entailment:
  "S \<Turnstile>\<^sub>P eval\<^sub>G S \<phi> \<longleftrightarrow> S \<Turnstile>\<^sub>P \<phi>"
  by (induction \<phi>, auto)

lemma eval\<^sub>G_respectfulness:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> eval\<^sub>G S \<phi> \<longrightarrow>\<^sub>P eval\<^sub>G S \<psi>"
  "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> eval\<^sub>G S \<phi> \<equiv>\<^sub>P eval\<^sub>G S \<psi>"
  using subst_respects_ltl_prop_entailment eval\<^sub>G_subst by metis+

lemma eval\<^sub>G_respectfulness_generalized:
  "(\<And>\<A>. (\<And>x. x \<in> S \<Longrightarrow> \<A> \<Turnstile>\<^sub>P x) \<Longrightarrow> \<A> \<Turnstile>\<^sub>P y) \<Longrightarrow> (\<And>x. x \<in> S \<Longrightarrow> \<A> \<Turnstile>\<^sub>P eval\<^sub>G P x) \<Longrightarrow> \<A> \<Turnstile>\<^sub>P eval\<^sub>G P y"
  using subst_respects_ltl_prop_entailment_generalized[of S y \<A>] eval\<^sub>G_subst[of P] by metis

lift_definition eval\<^sub>G_abs :: "'a ltl set \<Rightarrow> 'a ltl\<^sub>P \<Rightarrow> 'a ltl\<^sub>P" ("\<up>eval\<^sub>G") is eval\<^sub>G
  by (insert eval\<^sub>G_respectfulness(2))

subsection \<open>Finite Quotient Set\<close>

text \<open>If we restrict formulas to a finite set of propositions, the set of quotients of these is finite\<close>

lemma Rep_Abs_prop_entailment[simp]:
  "A \<Turnstile>\<^sub>P Rep (Abs \<phi>) = A \<Turnstile>\<^sub>P \<phi>"
  using Quotient3_ltl_prop_equiv_quotient[THEN rep_abs_rsp]
  by (auto simp add: ltl_prop_equiv_def)

fun sat_models :: "'a ltl_prop_equiv_quotient \<Rightarrow> 'a ltl set set"
where
  "sat_models a = {A. A \<Turnstile>\<^sub>P Rep(a)}"

lemma sat_models_invariant:
  "A \<in> sat_models (Abs \<phi>) = A \<Turnstile>\<^sub>P \<phi>"
  using Rep_Abs_prop_entailment by auto

lemma sat_models_inj:
  "inj sat_models"
  using Quotient3_ltl_prop_equiv_quotient[THEN Quotient3_rel_rep]
  by (auto simp add: ltl_prop_equiv_def inj_on_def)

lemma sat_models_finite_image:
  assumes "finite P"
  shows "finite (sat_models ` {Abs \<phi> | \<phi>. nested_propos \<phi> \<subseteq> P})"
proof -
  have "sat_models (Abs \<phi>) = {A \<union> B | A B. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi> \<and> B \<subseteq> UNIV - P}" (is "?lhs = ?rhs")
    if "nested_propos \<phi> \<subseteq> P" for \<phi>
  proof
    have "\<And>A B. A \<in> sat_models (Abs \<phi>) \<Longrightarrow> A \<union> B \<in> sat_models (Abs \<phi>)"
      unfolding sat_models_invariant by blast
    moreover
    have "{A | A. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi>} \<subseteq> sat_models (Abs \<phi>)"
      using sat_models_invariant by fast
    ultimately
    show "?rhs \<subseteq> ?lhs"
      by blast
  next
    have "propos \<phi> \<subseteq> P"
      using that propos_subset by blast
    have "A \<in> {A \<union> B | A B. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi> \<and> B \<subseteq> UNIV - P}"
      if "A \<in> sat_models (Abs \<phi>)" for A
    proof (standard, goal_cases prems)
      case prems
        then have "A \<Turnstile>\<^sub>P \<phi>"
          using that sat_models_invariant by blast
        then obtain C D where "C = (A \<inter> P)" and "D = A - P" and "A = C \<union> D"
          by blast
        then have "C \<Turnstile>\<^sub>P \<phi>" and "C \<subseteq> P" and "D \<subseteq> UNIV - P"
          using \<open>A \<Turnstile>\<^sub>P \<phi>\<close> LTL_prop_entailment_restrict_to_propos \<open>propos \<phi> \<subseteq> P\<close> by blast+
        then have "C \<union> D \<in> {A \<union> B | A B. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi> \<and> B \<subseteq> UNIV - P}"
          by blast
        thus ?case
          using \<open>A = C \<union> D\<close> by simp
    qed
    thus "?lhs \<subseteq> ?rhs"
      by blast
  qed
  hence Equal: "{sat_models (Abs \<phi>) | \<phi>. nested_propos \<phi> \<subseteq> P} = {{A \<union> B | A B. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi> \<and> B \<subseteq> UNIV - P} | \<phi>. nested_propos \<phi> \<subseteq> P}"
    by (metis (lifting, no_types))

  have Finite: "finite {{A \<union> B | A B. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi> \<and> B \<subseteq> UNIV - P} | \<phi>. nested_propos \<phi> \<subseteq> P}"
  proof -
    let ?map = "\<lambda>P S. {A \<union> B | A B. A \<in> S \<and> B \<subseteq> UNIV - P}"
    obtain S' where S'_def: "S' = {{A \<union> B | A B. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi> \<and> B \<subseteq> UNIV - P} | \<phi>. nested_propos \<phi> \<subseteq> P}"
      by blast
    obtain S where S_def: "S = {{A | A. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi>} | \<phi>. nested_propos \<phi> \<subseteq> P}"
      by blast

    \<comment> \<open>Prove S and ?map applied to it is finite\<close>
    hence "S \<subseteq> Pow (Pow P)"
      by blast
    hence "finite S"
      using \<open>finite P\<close> finite_Pow_iff infinite_super by fast
    hence "finite {?map P A | A. A \<in> S}"
      by fastforce

    \<comment> \<open>Prove that S' can be embedded into S using ?map\<close>

    have "S' \<subseteq> {?map P A | A. A \<in> S}"
    proof
      fix A
      assume "A \<in> S'"
      then obtain \<phi> where "nested_propos \<phi> \<subseteq> P"
        and "A = {A \<union> B | A B. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi> \<and> B \<subseteq> UNIV - P}"
        using S'_def by blast
      then have "?map P {A | A. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi>} = A"
        by simp
      moreover
      have "{A | A. A \<subseteq> P \<and> A \<Turnstile>\<^sub>P \<phi>} \<in> S"
        using \<open>nested_propos \<phi> \<subseteq> P\<close> S_def by auto
      ultimately
      show "A \<in> {?map P A | A. A \<in> S}"
        by blast
    qed

    show ?thesis
      using rev_finite_subset[OF \<open>finite {?map P A | A. A \<in> S}\<close> \<open>S' \<subseteq> {?map P A | A. A \<in> S}\<close>]
      unfolding S'_def .
  qed

  have Finite2: "finite {sat_models (Abs \<phi>) | \<phi>. nested_propos \<phi> \<subseteq> P}"
    unfolding Equal using Finite by blast
  have Equal2: "sat_models ` {Abs \<phi> | \<phi>. nested_propos \<phi> \<subseteq> P} = {sat_models (Abs \<phi>) | \<phi>. nested_propos \<phi> \<subseteq> P}"
    by blast

  show ?thesis
    unfolding Equal2 using Finite2 by blast
qed

lemma ltl_prop_equiv_quotient_restricted_to_P_finite:
  assumes "finite P"
  shows "finite {Abs \<phi> | \<phi>. nested_propos \<phi> \<subseteq> P}"
proof -
  have "inj_on sat_models {Abs \<phi> |\<phi>. nested_propos \<phi> \<subseteq> P}"
    using sat_models_inj subset_inj_on by auto
  thus ?thesis
    using finite_imageD[OF sat_models_finite_image[OF assms]] by fast
qed

locale lift_ltl_transformer =
  fixes
    f :: "'a ltl \<Rightarrow> 'b \<Rightarrow> 'a ltl"
  assumes
    respectfulness: "\<phi> \<equiv>\<^sub>P \<psi> \<Longrightarrow> f \<phi> \<nu> \<equiv>\<^sub>P f \<psi> \<nu>"
  assumes
    nested_propos_bounded: "nested_propos (f \<phi> \<nu>) \<subseteq> nested_propos \<phi>"
begin

lift_definition f_abs :: "'a ltl\<^sub>P \<Rightarrow> 'b \<Rightarrow> 'a ltl\<^sub>P" is f
  using respectfulness .

lift_definition f_foldl_abs :: "'a ltl\<^sub>P \<Rightarrow> 'b list \<Rightarrow> 'a ltl\<^sub>P" is "foldl f"
proof -
  fix \<phi> \<psi> :: "'a ltl" fix w :: "'b list" assume "\<phi> \<equiv>\<^sub>P \<psi>"
  thus "foldl f \<phi> w \<equiv>\<^sub>P foldl f \<psi> w"
    using respectfulness by (induction w arbitrary: \<phi> \<psi>) simp+
qed

lemma f_foldl_abs_alt_def:
  "f_foldl_abs (Abs \<phi>) w = foldl f_abs (Abs \<phi>) w"
  by (induction w rule: rev_induct) (unfold f_foldl_abs.abs_eq foldl.simps foldl_append, (metis f_abs.abs_eq)+)

definition abs_reach :: "'a ltl_prop_equiv_quotient \<Rightarrow> 'a ltl_prop_equiv_quotient set"
where
  "abs_reach \<Phi> = {foldl f_abs \<Phi> w |w. True}"

lemma finite_abs_reach:
  "finite (abs_reach (Abs \<phi>))"
proof -
  {
    fix w
    have "nested_propos (foldl f \<phi> w) \<subseteq> nested_propos \<phi>"
      by (induction w arbitrary: \<phi>) (simp, metis foldl_Cons nested_propos_bounded subset_trans)
  }
  hence "abs_reach (Abs \<phi>) \<subseteq> {Abs \<chi> | \<chi>. nested_propos \<chi> \<subseteq> nested_propos \<phi>}"
    unfolding abs_reach_def f_foldl_abs_alt_def[symmetric] f_foldl_abs.abs_eq by blast
  thus ?thesis
    using ltl_prop_equiv_quotient_restricted_to_P_finite finite_propos
    by (blast dest: finite_subset)
qed

end

end
