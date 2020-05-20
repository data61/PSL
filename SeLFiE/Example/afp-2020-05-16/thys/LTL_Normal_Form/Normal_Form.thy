(*
    Author:   Salomon Sickert
    License:  BSD
*)

section \<open>A Normal Form for Linear Temporal Logic\<close>

theory Normal_Form imports
  LTL_Master_Theorem.Master_Theorem
begin

subsection \<open>LTL Equivalences\<close>

text \<open>Several valid laws of LTL relating strong and weak operators that are useful later.\<close>

lemma ltln_strong_weak_2:
  "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi> and\<^sub>n F\<^sub>n \<psi>) W\<^sub>n \<psi>" (is "?thesis1")
  "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi> R\<^sub>n (\<psi> and\<^sub>n F\<^sub>n \<phi>)" (is "?thesis2")
proof -
  have "\<exists>j. suffix (i + j) w \<Turnstile>\<^sub>n \<psi>"
    if "suffix j w \<Turnstile>\<^sub>n \<psi>" and "\<forall>j\<le>i. \<not> suffix j w \<Turnstile>\<^sub>n \<psi>" for i j
  proof
    from that have "j > i"
      by (cases "j > i") auto
    thus "suffix (i + (j - i)) w \<Turnstile>\<^sub>n \<psi>"
      using that by auto
  qed
  thus ?thesis1
    unfolding ltln_strong_weak by auto
next 
  have "\<exists>j. suffix (i + j) w \<Turnstile>\<^sub>n \<phi>"
    if "suffix j w \<Turnstile>\<^sub>n \<phi>" and "\<forall>j<i. \<not> suffix j w \<Turnstile>\<^sub>n \<phi>" for i j
  proof
    from that have "j \<ge> i"
      by (cases "j \<ge> i") auto
    thus "suffix (i + (j - i)) w \<Turnstile>\<^sub>n \<phi>"
      using that by auto
  qed
  thus ?thesis2
    unfolding ltln_strong_weak by auto
qed

lemma ltln_weak_strong_2:
  "w \<Turnstile>\<^sub>n \<phi> W\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi> U\<^sub>n (\<psi> or\<^sub>n G\<^sub>n \<phi>)" (is "?thesis1")
  "w \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi> or\<^sub>n G\<^sub>n \<psi>) M\<^sub>n \<psi>" (is "?thesis2")
proof -
  have "suffix j w \<Turnstile>\<^sub>n \<phi>"
    if "\<And>j. j < i \<Longrightarrow> suffix j w \<Turnstile>\<^sub>n \<phi>" and "\<And>j. suffix (i + j) w \<Turnstile>\<^sub>n \<phi>" for i j
    using that(1)[of j] that(2)[of "j - i"] by (cases "j < i") simp_all
  thus ?thesis1
    unfolding ltln_weak_strong unfolding semantics_ltln.simps suffix_suffix by blast
next
  have "suffix j w \<Turnstile>\<^sub>n \<psi>"
    if "\<And>j. j \<le> i \<Longrightarrow> suffix j w \<Turnstile>\<^sub>n \<psi>" and "\<And>j. suffix (i + j) w \<Turnstile>\<^sub>n \<psi>" for i j
    using that(1)[of j] that(2)[of "j - i"] by (cases "j \<le> i") simp_all
  thus ?thesis2
    unfolding ltln_weak_strong unfolding semantics_ltln.simps suffix_suffix by blast
qed

subsection \<open>$\evalnu{\psi}{M}$, $\evalmu{\psi}{N}$, $\flatten{\psi}{M}$, and $\flattentwo{\psi}{N}$\<close>

text \<open>The following four functions use "promise sets", named $M$ or $N$, to rewrite arbitrary 
  formulas into formulas from the class $\Sigma_1$-, $\Sigma_2$-, $\Pi_1$-, and $\Pi_2$, 
  respectively. In general the obtained formulas are not  equivalent, but under some conditions 
  (as outlined below) they are.\<close>

no_notation FG_advice ("_[_]\<^sub>\<mu>" [90,60] 89)
no_notation GF_advice ("_[_]\<^sub>\<nu>" [90,60] 89)

notation FG_advice ("_[_]\<^sub>\<Sigma>\<^sub>1" [90,60] 89)
notation GF_advice ("_[_]\<^sub>\<Pi>\<^sub>1" [90,60] 89)

fun flatten_sigma_2:: "'a ltln \<Rightarrow> 'a ltln set \<Rightarrow> 'a ltln" ("_[_]\<^sub>\<Sigma>\<^sub>2")
where
  "(\<phi> U\<^sub>n \<psi>)[M]\<^sub>\<Sigma>\<^sub>2 = (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) U\<^sub>n (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)"
| "(\<phi> W\<^sub>n \<psi>)[M]\<^sub>\<Sigma>\<^sub>2 = (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) U\<^sub>n ((\<psi>[M]\<^sub>\<Sigma>\<^sub>2) or\<^sub>n (G\<^sub>n \<phi>[M]\<^sub>\<Pi>\<^sub>1))"
| "(\<phi> M\<^sub>n \<psi>)[M]\<^sub>\<Sigma>\<^sub>2 = (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) M\<^sub>n (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)"
| "(\<phi> R\<^sub>n \<psi>)[M]\<^sub>\<Sigma>\<^sub>2 = ((\<phi>[M]\<^sub>\<Sigma>\<^sub>2) or\<^sub>n (G\<^sub>n \<psi>[M]\<^sub>\<Pi>\<^sub>1)) M\<^sub>n (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)"
| "(\<phi> and\<^sub>n \<psi>)[M]\<^sub>\<Sigma>\<^sub>2 = (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) and\<^sub>n (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)"
| "(\<phi> or\<^sub>n \<psi>)[M]\<^sub>\<Sigma>\<^sub>2 = (\<phi>[M]\<^sub>\<Sigma>\<^sub>2) or\<^sub>n (\<psi>[M]\<^sub>\<Sigma>\<^sub>2)"
| "(X\<^sub>n \<phi>)[M]\<^sub>\<Sigma>\<^sub>2 = X\<^sub>n (\<phi>[M]\<^sub>\<Sigma>\<^sub>2)"
| "\<phi>[M]\<^sub>\<Sigma>\<^sub>2 = \<phi>"

fun flatten_pi_2 :: "'a ltln \<Rightarrow> 'a ltln set \<Rightarrow> 'a ltln" ("_[_]\<^sub>\<Pi>\<^sub>2")
where
  "(\<phi> W\<^sub>n \<psi>)[N]\<^sub>\<Pi>\<^sub>2 = (\<phi>[N]\<^sub>\<Pi>\<^sub>2) W\<^sub>n (\<psi>[N]\<^sub>\<Pi>\<^sub>2)"
| "(\<phi> U\<^sub>n \<psi>)[N]\<^sub>\<Pi>\<^sub>2 = (\<phi>[N]\<^sub>\<Pi>\<^sub>2 and\<^sub>n (F\<^sub>n \<psi>[N]\<^sub>\<Sigma>\<^sub>1)) W\<^sub>n (\<psi>[N]\<^sub>\<Pi>\<^sub>2)"
| "(\<phi> R\<^sub>n \<psi>)[N]\<^sub>\<Pi>\<^sub>2 = (\<phi>[N]\<^sub>\<Pi>\<^sub>2) R\<^sub>n (\<psi>[N]\<^sub>\<Pi>\<^sub>2)"
| "(\<phi> M\<^sub>n \<psi>)[N]\<^sub>\<Pi>\<^sub>2 = (\<phi>[N]\<^sub>\<Pi>\<^sub>2) R\<^sub>n ((\<psi>[N]\<^sub>\<Pi>\<^sub>2) and\<^sub>n (F\<^sub>n \<phi>[N]\<^sub>\<Sigma>\<^sub>1))"
| "(\<phi> and\<^sub>n \<psi>)[N]\<^sub>\<Pi>\<^sub>2 = (\<phi>[N]\<^sub>\<Pi>\<^sub>2) and\<^sub>n (\<psi>[N]\<^sub>\<Pi>\<^sub>2)"
| "(\<phi> or\<^sub>n \<psi>)[N]\<^sub>\<Pi>\<^sub>2 = (\<phi>[N]\<^sub>\<Pi>\<^sub>2) or\<^sub>n (\<psi>[N]\<^sub>\<Pi>\<^sub>2)"
| "(X\<^sub>n \<phi>)[N]\<^sub>\<Pi>\<^sub>2 = X\<^sub>n (\<phi>[N]\<^sub>\<Pi>\<^sub>2)"
| "\<phi>[N]\<^sub>\<Pi>\<^sub>2 = \<phi>"

lemma GF_advice_restriction:
  "\<phi>[\<G>\<F> (\<phi> W\<^sub>n \<psi>) w]\<^sub>\<Pi>\<^sub>1 = \<phi>[\<G>\<F> \<phi> w]\<^sub>\<Pi>\<^sub>1"
  "\<psi>[\<G>\<F> (\<phi> R\<^sub>n \<psi>) w]\<^sub>\<Pi>\<^sub>1 = \<psi>[\<G>\<F> \<psi> w]\<^sub>\<Pi>\<^sub>1"
  by (metis (no_types, lifting) \<G>\<F>_semantics' inf_commute inf_left_commute inf_sup_absorb subformulas\<^sub>\<mu>.simps(6) GF_advice_inter_subformulas) 
     (metis (no_types, lifting) GF_advice_inter \<G>\<F>.simps(5) \<G>\<F>_semantics' \<G>\<F>_subformulas\<^sub>\<mu> inf.commute sup.boundedE)

lemma FG_advice_restriction: 
  "\<psi>[\<F>\<G> (\<phi> U\<^sub>n \<psi>) w]\<^sub>\<Sigma>\<^sub>1 = \<psi>[\<F>\<G> \<psi> w]\<^sub>\<Sigma>\<^sub>1"
  "\<phi>[\<F>\<G> (\<phi> M\<^sub>n \<psi>) w]\<^sub>\<Sigma>\<^sub>1 = \<phi>[\<F>\<G> \<phi> w]\<^sub>\<Sigma>\<^sub>1"  
  by (metis (no_types, lifting) FG_advice_inter \<F>\<G>.simps(4) \<F>\<G>_semantics' \<F>\<G>_subformulas\<^sub>\<nu> inf.commute sup.boundedE) 
     (metis (no_types, lifting) FG_advice_inter \<F>\<G>.simps(7) \<F>\<G>_semantics' \<F>\<G>_subformulas\<^sub>\<nu> inf.right_idem inf_commute sup.cobounded1) 

lemma flatten_sigma_2_intersection:
  "M \<inter> subformulas\<^sub>\<mu> \<phi> \<subseteq> S \<Longrightarrow> \<phi>[M \<inter> S]\<^sub>\<Sigma>\<^sub>2 = \<phi>[M]\<^sub>\<Sigma>\<^sub>2"
  by (induction \<phi>) (simp; blast intro: GF_advice_inter)+

lemma flatten_sigma_2_intersection_eq:
  "M \<inter> subformulas\<^sub>\<mu> \<phi> = M' \<Longrightarrow> \<phi>[M']\<^sub>\<Sigma>\<^sub>2 = \<phi>[M]\<^sub>\<Sigma>\<^sub>2"
  using flatten_sigma_2_intersection by auto

lemma flatten_sigma_2_monotone: 
  "w \<Turnstile>\<^sub>n \<phi>[M]\<^sub>\<Sigma>\<^sub>2 \<Longrightarrow> M \<subseteq> M' \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>[M']\<^sub>\<Sigma>\<^sub>2"
  by (induction \<phi> arbitrary: w)
     (simp; blast dest: GF_advice_monotone)+

lemma flatten_pi_2_intersection:
  "N \<inter> subformulas\<^sub>\<nu> \<phi> \<subseteq> S \<Longrightarrow> \<phi>[N \<inter> S]\<^sub>\<Pi>\<^sub>2 = \<phi>[N]\<^sub>\<Pi>\<^sub>2"
  by (induction \<phi>) (simp; blast intro: FG_advice_inter)+

lemma flatten_pi_2_intersection_eq:
  "N \<inter> subformulas\<^sub>\<nu> \<phi> = N' \<Longrightarrow> \<phi>[N']\<^sub>\<Pi>\<^sub>2 = \<phi>[N]\<^sub>\<Pi>\<^sub>2"
  using flatten_pi_2_intersection by auto

lemma flatten_pi_2_monotone: 
  "w \<Turnstile>\<^sub>n \<phi>[N]\<^sub>\<Pi>\<^sub>2 \<Longrightarrow> N \<subseteq> N' \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>[N']\<^sub>\<Pi>\<^sub>2"
  by (induction \<phi> arbitrary: w)
     (simp; blast dest: FG_advice_monotone)+

lemma ltln_weak_strong_stable_words_1:
  "w \<Turnstile>\<^sub>n (\<phi> W\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi> U\<^sub>n (\<psi> or\<^sub>n (G\<^sub>n \<phi>[\<G>\<F> \<phi> w]\<^sub>\<Pi>\<^sub>1))" (is "?lhs \<longleftrightarrow> ?rhs") 
proof 
  assume ?lhs
  
  moreover

  {
    assume assm: "w \<Turnstile>\<^sub>n G\<^sub>n \<phi>"
    moreover
    obtain i where "\<And>j. \<F> \<phi> (suffix i w) \<subseteq> \<G>\<F> \<phi> w"
      by (metis MOST_nat_le \<G>\<F>_suffix \<mu>_stable_def order_refl suffix_\<mu>_stable)
    hence "\<And>j. \<F> \<phi> (suffix i (suffix j w)) \<subseteq> \<G>\<F> \<phi> w"
      by (metis \<F>_suffix \<G>\<F>_\<F>_subset \<G>\<F>_suffix semiring_normalization_rules(24) subset_Un_eq suffix_suffix sup.orderE)
    ultimately
    have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<phi>[\<G>\<F> \<phi> w]\<^sub>\<Pi>\<^sub>1)"
      using GF_advice_a1[OF \<open>\<And>j. \<F> \<phi> (suffix i (suffix j w)) \<subseteq> \<G>\<F> \<phi> w\<close>]
      by (simp add: add.commute)
    hence "?rhs"
      using assm by auto 
  }

  moreover

  have "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> \<Longrightarrow> ?rhs"
    by auto
  
  ultimately

  show ?rhs
    using ltln_weak_to_strong(1) by blast
next
  assume ?rhs
  thus ?lhs
    unfolding ltln_weak_strong_2 unfolding semantics_ltln.simps
    by (metis \<G>\<F>_suffix order_refl GF_advice_a2)
qed

lemma ltln_weak_strong_stable_words_2:
  "w \<Turnstile>\<^sub>n (\<phi> R\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi> or\<^sub>n (G\<^sub>n \<psi>[\<G>\<F> \<psi> w]\<^sub>\<Pi>\<^sub>1)) M\<^sub>n \<psi>" (is "?lhs \<longleftrightarrow> ?rhs") 
proof 
  assume ?lhs
  
  moreover

  {
    assume assm: "w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
    moreover
    obtain i where "\<And>j. \<F> \<psi> (suffix i w) \<subseteq> \<G>\<F> \<psi> w"
      by (metis MOST_nat_le \<G>\<F>_suffix \<mu>_stable_def order_refl suffix_\<mu>_stable)
    hence "\<And>j. \<F> \<psi> (suffix i (suffix j w)) \<subseteq> \<G>\<F> \<psi> w"
      by (metis \<F>_suffix \<G>\<F>_\<F>_subset \<G>\<F>_suffix semiring_normalization_rules(24) subset_Un_eq suffix_suffix sup.orderE)
    ultimately
    have "suffix i w \<Turnstile>\<^sub>n G\<^sub>n (\<psi>[\<G>\<F> \<psi> w]\<^sub>\<Pi>\<^sub>1)"
      using GF_advice_a1[OF \<open>\<And>j. \<F> \<psi> (suffix i (suffix j w)) \<subseteq> \<G>\<F> \<psi> w\<close>]
      by (simp add: add.commute)
    hence "?rhs"
      using assm by auto 
  }

  moreover

  have "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> \<Longrightarrow> ?rhs"
    by auto
  
  ultimately

  show ?rhs
    using ltln_weak_to_strong by blast
next
  assume ?rhs
  thus ?lhs
    unfolding ltln_weak_strong_2 unfolding semantics_ltln.simps
    by (metis GF_advice_a2 \<G>\<F>_suffix order_refl)
qed

lemma ltln_weak_strong_stable_words:
  "w \<Turnstile>\<^sub>n (\<phi> W\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi> U\<^sub>n (\<psi> or\<^sub>n (G\<^sub>n \<phi>[\<G>\<F> (\<phi> W\<^sub>n \<psi>) w]\<^sub>\<Pi>\<^sub>1))"
  "w \<Turnstile>\<^sub>n (\<phi> R\<^sub>n \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi> or\<^sub>n (G\<^sub>n \<psi>[\<G>\<F> (\<phi> R\<^sub>n \<psi>) w]\<^sub>\<Pi>\<^sub>1)) M\<^sub>n \<psi>"
  unfolding ltln_weak_strong_stable_words_1 ltln_weak_strong_stable_words_2 GF_advice_restriction by simp+

lemma flatten_sigma_2_IH_lifting: 
  assumes "\<psi> \<in> subfrmlsn \<phi>"
  assumes "suffix i w \<Turnstile>\<^sub>n \<psi>[\<G>\<F> \<psi> (suffix i w)]\<^sub>\<Sigma>\<^sub>2 = suffix i w \<Turnstile>\<^sub>n \<psi>"
  shows "suffix i w \<Turnstile>\<^sub>n \<psi>[\<G>\<F> \<phi> w]\<^sub>\<Sigma>\<^sub>2 = suffix i w \<Turnstile>\<^sub>n \<psi>" 
  by (metis (no_types, lifting) inf.absorb_iff2 inf_assoc inf_commute assms(2) \<G>\<F>_suffix flatten_sigma_2_intersection_eq[of "\<G>\<F> \<phi> w" \<psi> "\<G>\<F> \<psi> w"] \<G>\<F>_semantics' subformulas\<^sub>\<mu>_subset[OF assms(1)])
  
lemma flatten_sigma_2_correct:
  "w \<Turnstile>\<^sub>n \<phi>[\<G>\<F> \<phi> w]\<^sub>\<Sigma>\<^sub>2 \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof (induction \<phi> arbitrary: w)
  case (And_ltln \<phi>1 \<phi>2)
  then show ?case 
    using flatten_sigma_2_IH_lifting[of _ "\<phi>1 and\<^sub>n \<phi>2" 0] by simp
next
  case (Or_ltln \<phi>1 \<phi>2)
  then show ?case 
    using flatten_sigma_2_IH_lifting[of _ "\<phi>1 or\<^sub>n \<phi>2" 0] by simp
next
  case (Next_ltln \<phi>)
  then show ?case 
    using flatten_sigma_2_IH_lifting[of _ "X\<^sub>n \<phi>" 1] by fastforce
next
  case (Until_ltln \<phi>1 \<phi>2)
  then show ?case
    using flatten_sigma_2_IH_lifting[of _ "\<phi>1 U\<^sub>n \<phi>2"] by fastforce
next
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding ltln_weak_strong_stable_words
    using flatten_sigma_2_IH_lifting[of _ "\<phi>1 R\<^sub>n \<phi>2"] by fastforce
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding ltln_weak_strong_stable_words
    using flatten_sigma_2_IH_lifting[of _ "\<phi>1 W\<^sub>n \<phi>2"] by fastforce
next
case (StrongRelease_ltln \<phi>1 \<phi>2)
  then show ?case
    using flatten_sigma_2_IH_lifting[of _ "\<phi>1 M\<^sub>n \<phi>2"] by fastforce
qed auto

lemma ltln_strong_weak_stable_words_1:
  "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi> and\<^sub>n (F\<^sub>n \<psi>[\<F>\<G> \<psi> w]\<^sub>\<Sigma>\<^sub>1)) W\<^sub>n \<psi>" (is "?lhs \<longleftrightarrow> ?rhs") 
proof 
  assume ?rhs

  moreover

  obtain i where "\<nu>_stable \<psi> (suffix i w)"
    by (metis MOST_nat less_Suc_eq suffix_\<nu>_stable)
  hence "\<forall>\<psi> \<in> \<F>\<G> \<psi> w. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
    using \<F>\<G>_suffix \<G>_elim \<nu>_stable_def by blast

  {
    assume assm: "w \<Turnstile>\<^sub>n G\<^sub>n (\<phi> and\<^sub>n (F\<^sub>n \<psi>[\<F>\<G> \<psi> w]\<^sub>\<Sigma>\<^sub>1))"
    hence "suffix i w \<Turnstile>\<^sub>n (F\<^sub>n \<psi>)[\<F>\<G> \<psi> w]\<^sub>\<Sigma>\<^sub>1"
      by simp
    hence "suffix i w \<Turnstile>\<^sub>n F\<^sub>n \<psi>"
      by (blast dest: FG_advice_b2_helper[OF \<open>\<forall>\<psi> \<in> \<F>\<G> \<psi> w. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>\<close>])
    hence "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi>"
      using assm by auto
  }

  ultimately
  
  show ?lhs
    by (meson ltln_weak_to_strong(1) semantics_ltln.simps(5) until_and_left_distrib)
next 
  assume ?lhs 

  moreover

  have "\<And>i. suffix i w \<Turnstile>\<^sub>n \<psi> \<Longrightarrow> suffix i w \<Turnstile>\<^sub>n \<psi>[\<F>\<G> \<psi> w]\<^sub>\<Sigma>\<^sub>1"
    using \<F>\<G>_suffix by (blast intro: FG_advice_b1)

  ultimately

  show "?rhs"
    unfolding ltln_strong_weak_2 by fastforce
qed

lemma ltln_strong_weak_stable_words_2:
  "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi> R\<^sub>n (\<psi> and\<^sub>n (F\<^sub>n \<phi>[\<F>\<G> \<phi> w]\<^sub>\<Sigma>\<^sub>1))" (is "?lhs \<longleftrightarrow> ?rhs") 
proof 
  assume ?rhs

  moreover

  obtain i where "\<nu>_stable \<phi> (suffix i w)"
    by (metis MOST_nat less_Suc_eq suffix_\<nu>_stable)
  hence "\<forall>\<psi> \<in> \<F>\<G> \<phi> w. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>"
    using \<F>\<G>_suffix \<G>_elim \<nu>_stable_def by blast

  {
    assume assm: "w \<Turnstile>\<^sub>n G\<^sub>n (\<psi> and\<^sub>n (F\<^sub>n \<phi>[\<F>\<G> \<phi> w]\<^sub>\<Sigma>\<^sub>1))"
    hence "suffix i w \<Turnstile>\<^sub>n (F\<^sub>n \<phi>)[\<F>\<G> \<phi> w]\<^sub>\<Sigma>\<^sub>1"
      by simp
    hence "suffix i w \<Turnstile>\<^sub>n F\<^sub>n \<phi>"
      by (blast dest: FG_advice_b2_helper[OF \<open>\<forall>\<psi> \<in> \<F>\<G> \<phi> w. suffix i w \<Turnstile>\<^sub>n G\<^sub>n \<psi>\<close>])
    hence "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi>"
      using assm by auto
  }

  ultimately
  
  show ?lhs
    using ltln_weak_to_strong(3) semantics_ltln.simps(5) strong_release_and_right_distrib by blast
next 
  assume ?lhs 

  moreover

  have "\<And>i. suffix i w \<Turnstile>\<^sub>n \<phi> \<Longrightarrow> suffix i w \<Turnstile>\<^sub>n \<phi>[\<F>\<G> \<phi> w]\<^sub>\<Sigma>\<^sub>1"
    using \<F>\<G>_suffix by (blast intro: FG_advice_b1)

  ultimately

  show "?rhs"
    unfolding ltln_strong_weak_2 by fastforce
qed

lemma ltln_strong_weak_stable_words:
  "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n (\<phi> and\<^sub>n (F\<^sub>n \<psi>[\<F>\<G> (\<phi> U\<^sub>n \<psi>) w]\<^sub>\<Sigma>\<^sub>1)) W\<^sub>n \<psi>"
  "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi> R\<^sub>n (\<psi> and\<^sub>n (F\<^sub>n \<phi>[\<F>\<G> (\<phi> M\<^sub>n \<psi>) w]\<^sub>\<Sigma>\<^sub>1))"
  unfolding ltln_strong_weak_stable_words_1 ltln_strong_weak_stable_words_2 FG_advice_restriction by simp+

lemma flatten_pi_2_IH_lifting: 
  assumes "\<psi> \<in> subfrmlsn \<phi>"
  assumes "suffix i w \<Turnstile>\<^sub>n \<psi>[\<F>\<G> \<psi> (suffix i w)]\<^sub>\<Pi>\<^sub>2 = suffix i w \<Turnstile>\<^sub>n \<psi>"
  shows "suffix i w \<Turnstile>\<^sub>n \<psi>[\<F>\<G> \<phi> w]\<^sub>\<Pi>\<^sub>2 = suffix i w \<Turnstile>\<^sub>n \<psi>" 
  by (metis (no_types, lifting) inf.absorb_iff2 inf_assoc inf_commute assms(2) \<F>\<G>_suffix flatten_pi_2_intersection_eq[of "\<F>\<G> \<phi> w" \<psi> "\<F>\<G> \<psi> w"] \<F>\<G>_semantics' subformulas\<^sub>\<nu>_subset[OF assms(1)])

lemma flatten_pi_2_correct:
  "w \<Turnstile>\<^sub>n \<phi>[\<F>\<G> \<phi> w]\<^sub>\<Pi>\<^sub>2 \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof (induction \<phi> arbitrary: w)
  case (And_ltln \<phi>1 \<phi>2)
  then show ?case 
    using flatten_pi_2_IH_lifting[of _ "\<phi>1 and\<^sub>n \<phi>2" 0] by simp
next
  case (Or_ltln \<phi>1 \<phi>2)
  then show ?case 
    using flatten_pi_2_IH_lifting[of _ "\<phi>1 or\<^sub>n \<phi>2" 0] by simp
next
  case (Next_ltln \<phi>)
  then show ?case 
    using flatten_pi_2_IH_lifting[of _ "X\<^sub>n \<phi>" 1] by fastforce
next
  case (Until_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding ltln_strong_weak_stable_words
    using flatten_pi_2_IH_lifting[of _ "\<phi>1 U\<^sub>n \<phi>2"] by fastforce
next
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
    using flatten_pi_2_IH_lifting[of _ "\<phi>1 R\<^sub>n \<phi>2"] by fastforce
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  then show ?case
    using flatten_pi_2_IH_lifting[of _ "\<phi>1 W\<^sub>n \<phi>2"] by fastforce
next
case (StrongRelease_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding ltln_strong_weak_stable_words
    using flatten_pi_2_IH_lifting[of _ "\<phi>1 M\<^sub>n \<phi>2"] by fastforce
qed auto

subsection \<open>Main Theorem\<close>

text \<open>Using the four previously defined functions we obtain our normal form.\<close>

theorem normal_form_with_flatten_sigma_2:
  "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> 
    (\<exists>M \<subseteq> subformulas\<^sub>\<mu> \<phi>. \<exists>N \<subseteq> subformulas\<^sub>\<nu> \<phi>.
      w \<Turnstile>\<^sub>n \<phi>[M]\<^sub>\<Sigma>\<^sub>2 \<and> (\<forall>\<psi> \<in> M. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[N]\<^sub>\<Sigma>\<^sub>1)) \<and> (\<forall>\<psi> \<in> N. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[M]\<^sub>\<Pi>\<^sub>1)))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have "w \<Turnstile>\<^sub>n \<phi>[\<G>\<F> \<phi> w]\<^sub>\<Sigma>\<^sub>2"
    using flatten_sigma_2_correct by blast
  then show ?rhs
    using \<G>\<F>_subformulas\<^sub>\<mu> \<F>\<G>_subformulas\<^sub>\<nu> \<G>\<F>_implies_GF \<F>\<G>_implies_FG by metis 
next
  assume ?rhs
  then obtain M N where "w \<Turnstile>\<^sub>n \<phi>[M]\<^sub>\<Sigma>\<^sub>2" and "M \<subseteq> \<G>\<F> \<phi> w" and "N \<subseteq> \<F>\<G> \<phi> w"
    using X_\<G>\<F>_Y_\<F>\<G> by blast
  then have "w \<Turnstile>\<^sub>n \<phi>[\<G>\<F> \<phi> w]\<^sub>\<Sigma>\<^sub>2"
    using flatten_sigma_2_monotone by blast
  then show ?lhs
    using flatten_sigma_2_correct by blast
qed

theorem normal_form_with_flatten_pi_2:
  "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> 
    (\<exists>M \<subseteq> subformulas\<^sub>\<mu> \<phi>. \<exists>N \<subseteq> subformulas\<^sub>\<nu> \<phi>.
      w \<Turnstile>\<^sub>n \<phi>[N]\<^sub>\<Pi>\<^sub>2 \<and> (\<forall>\<psi> \<in> M. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[N]\<^sub>\<Sigma>\<^sub>1)) \<and> (\<forall>\<psi> \<in> N. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[M]\<^sub>\<Pi>\<^sub>1)))" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then have "w \<Turnstile>\<^sub>n \<phi>[\<F>\<G> \<phi> w]\<^sub>\<Pi>\<^sub>2"
    using flatten_pi_2_correct by blast
  then show ?rhs
    using \<G>\<F>_subformulas\<^sub>\<mu> \<F>\<G>_subformulas\<^sub>\<nu> \<G>\<F>_implies_GF \<F>\<G>_implies_FG by metis 
next
  assume ?rhs
  then obtain M N where "w \<Turnstile>\<^sub>n \<phi>[N]\<^sub>\<Pi>\<^sub>2" and "M \<subseteq> \<G>\<F> \<phi> w" and "N \<subseteq> \<F>\<G> \<phi> w"
    using X_\<G>\<F>_Y_\<F>\<G> by metis
  then have "w \<Turnstile>\<^sub>n \<phi>[\<F>\<G> \<phi> w]\<^sub>\<Pi>\<^sub>2"
    using flatten_pi_2_monotone by metis
  then show ?lhs
    using flatten_pi_2_correct by blast
qed

end