(*
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Advice functions\<close>

theory Advice
imports
  LTL.LTL LTL.Equivalence_Relations
  Syntactic_Fragments_and_Stability After
begin

subsection \<open>The GF and FG Advice Functions\<close>

fun GF_advice :: "'a ltln \<Rightarrow> 'a ltln set \<Rightarrow> 'a ltln" ("_[_]\<^sub>\<nu>" [90,60] 89)
  where
  "(X\<^sub>n \<psi>)[X]\<^sub>\<nu> = X\<^sub>n (\<psi>[X]\<^sub>\<nu>)"
| "(\<psi>\<^sub>1 and\<^sub>n \<psi>\<^sub>2)[X]\<^sub>\<nu> = (\<psi>\<^sub>1[X]\<^sub>\<nu>) and\<^sub>n (\<psi>\<^sub>2[X]\<^sub>\<nu>)"
| "(\<psi>\<^sub>1 or\<^sub>n \<psi>\<^sub>2)[X]\<^sub>\<nu> = (\<psi>\<^sub>1[X]\<^sub>\<nu>) or\<^sub>n (\<psi>\<^sub>2[X]\<^sub>\<nu>)"
| "(\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2)[X]\<^sub>\<nu> = (\<psi>\<^sub>1[X]\<^sub>\<nu>) W\<^sub>n (\<psi>\<^sub>2[X]\<^sub>\<nu>)"
| "(\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2)[X]\<^sub>\<nu> = (\<psi>\<^sub>1[X]\<^sub>\<nu>) R\<^sub>n (\<psi>\<^sub>2[X]\<^sub>\<nu>)"
| "(\<psi>\<^sub>1 U\<^sub>n \<psi>\<^sub>2)[X]\<^sub>\<nu> = (if (\<psi>\<^sub>1 U\<^sub>n \<psi>\<^sub>2) \<in> X then (\<psi>\<^sub>1[X]\<^sub>\<nu>) W\<^sub>n (\<psi>\<^sub>2[X]\<^sub>\<nu>) else false\<^sub>n)"
| "(\<psi>\<^sub>1 M\<^sub>n \<psi>\<^sub>2)[X]\<^sub>\<nu> = (if (\<psi>\<^sub>1 M\<^sub>n \<psi>\<^sub>2) \<in> X then (\<psi>\<^sub>1[X]\<^sub>\<nu>) R\<^sub>n (\<psi>\<^sub>2[X]\<^sub>\<nu>) else false\<^sub>n)"
| "\<phi>[_]\<^sub>\<nu> = \<phi>"

fun FG_advice :: "'a ltln \<Rightarrow> 'a ltln set \<Rightarrow> 'a ltln" ("_[_]\<^sub>\<mu>" [90,60] 89)
where
  "(X\<^sub>n \<psi>)[Y]\<^sub>\<mu> = X\<^sub>n (\<psi>[Y]\<^sub>\<mu>)"
| "(\<psi>\<^sub>1 and\<^sub>n \<psi>\<^sub>2)[Y]\<^sub>\<mu> = (\<psi>\<^sub>1[Y]\<^sub>\<mu>) and\<^sub>n (\<psi>\<^sub>2[Y]\<^sub>\<mu>)"
| "(\<psi>\<^sub>1 or\<^sub>n \<psi>\<^sub>2)[Y]\<^sub>\<mu> = (\<psi>\<^sub>1[Y]\<^sub>\<mu>) or\<^sub>n (\<psi>\<^sub>2[Y]\<^sub>\<mu>)"
| "(\<psi>\<^sub>1 U\<^sub>n \<psi>\<^sub>2)[Y]\<^sub>\<mu> = (\<psi>\<^sub>1[Y]\<^sub>\<mu>) U\<^sub>n (\<psi>\<^sub>2[Y]\<^sub>\<mu>)"
| "(\<psi>\<^sub>1 M\<^sub>n \<psi>\<^sub>2)[Y]\<^sub>\<mu> = (\<psi>\<^sub>1[Y]\<^sub>\<mu>) M\<^sub>n (\<psi>\<^sub>2[Y]\<^sub>\<mu>)"
| "(\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2)[Y]\<^sub>\<mu> = (if (\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2) \<in> Y then true\<^sub>n else (\<psi>\<^sub>1[Y]\<^sub>\<mu>) U\<^sub>n (\<psi>\<^sub>2[Y]\<^sub>\<mu>))"
| "(\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2)[Y]\<^sub>\<mu> = (if (\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2) \<in> Y then true\<^sub>n else (\<psi>\<^sub>1[Y]\<^sub>\<mu>) M\<^sub>n (\<psi>\<^sub>2[Y]\<^sub>\<mu>))"
| "\<phi>[_]\<^sub>\<mu> = \<phi>"

lemma GF_advice_\<nu>LTL:
  "\<phi>[X]\<^sub>\<nu> \<in> \<nu>LTL"
  "\<phi> \<in> \<nu>LTL \<Longrightarrow> \<phi>[X]\<^sub>\<nu> = \<phi>"
  by (induction \<phi>) auto

lemma FG_advice_\<mu>LTL:
  "\<phi>[X]\<^sub>\<mu> \<in> \<mu>LTL"
  "\<phi> \<in> \<mu>LTL \<Longrightarrow> \<phi>[X]\<^sub>\<mu> = \<phi>"
  by (induction \<phi>) auto


lemma GF_advice_subfrmlsn:
  "subfrmlsn (\<phi>[X]\<^sub>\<nu>) \<subseteq> {\<psi>[X]\<^sub>\<nu> | \<psi>. \<psi> \<in> subfrmlsn \<phi>}"
  by (induction \<phi>) force+

lemma FG_advice_subfrmlsn:
  "subfrmlsn (\<phi>[Y]\<^sub>\<mu>) \<subseteq> {\<psi>[Y]\<^sub>\<mu> | \<psi>. \<psi> \<in> subfrmlsn \<phi>}"
  by (induction \<phi>) force+

lemma GF_advice_subfrmlsn_card:
  "card (subfrmlsn (\<phi>[X]\<^sub>\<nu>)) \<le> card (subfrmlsn \<phi>)"
proof -
  have "card (subfrmlsn (\<phi>[X]\<^sub>\<nu>)) \<le> card {\<psi>[X]\<^sub>\<nu> | \<psi>. \<psi> \<in> subfrmlsn \<phi>}"
    by (simp add: subfrmlsn_finite GF_advice_subfrmlsn card_mono)

  also have "\<dots> \<le> card (subfrmlsn \<phi>)"
    by (metis Collect_mem_eq card_image_le image_Collect subfrmlsn_finite)

  finally show ?thesis .
qed

lemma FG_advice_subfrmlsn_card:
  "card (subfrmlsn (\<phi>[Y]\<^sub>\<mu>)) \<le> card (subfrmlsn \<phi>)"
proof -
  have "card (subfrmlsn (\<phi>[Y]\<^sub>\<mu>)) \<le> card {\<psi>[Y]\<^sub>\<mu> | \<psi>. \<psi> \<in> subfrmlsn \<phi>}"
    by (simp add: subfrmlsn_finite FG_advice_subfrmlsn card_mono)

  also have "\<dots> \<le> card (subfrmlsn \<phi>)"
    by (metis Collect_mem_eq card_image_le image_Collect subfrmlsn_finite)

  finally show ?thesis .
qed



subsection \<open>Advice Functions on Nested Propositions\<close>

definition nested_prop_atoms\<^sub>\<nu> :: "'a ltln \<Rightarrow> 'a ltln set \<Rightarrow> 'a ltln set"
where
  "nested_prop_atoms\<^sub>\<nu> \<phi> X = {\<psi>[X]\<^sub>\<nu> | \<psi>. \<psi> \<in> nested_prop_atoms \<phi>}"

definition nested_prop_atoms\<^sub>\<mu> :: "'a ltln \<Rightarrow> 'a ltln set \<Rightarrow> 'a ltln set"
where
  "nested_prop_atoms\<^sub>\<mu> \<phi> X = {\<psi>[X]\<^sub>\<mu> | \<psi>. \<psi> \<in> nested_prop_atoms \<phi>}"

lemma nested_prop_atoms\<^sub>\<nu>_finite:
  "finite (nested_prop_atoms\<^sub>\<nu> \<phi> X)"
  by (simp add: nested_prop_atoms\<^sub>\<nu>_def nested_prop_atoms_finite)

lemma nested_prop_atoms\<^sub>\<mu>_finite:
  "finite (nested_prop_atoms\<^sub>\<mu> \<phi> X)"
  by (simp add: nested_prop_atoms\<^sub>\<mu>_def nested_prop_atoms_finite)

lemma nested_prop_atoms\<^sub>\<nu>_card:
  "card (nested_prop_atoms\<^sub>\<nu> \<phi> X) \<le> card (nested_prop_atoms \<phi>)"
  unfolding nested_prop_atoms\<^sub>\<nu>_def
  by (metis Collect_mem_eq card_image_le image_Collect nested_prop_atoms_finite)

lemma nested_prop_atoms\<^sub>\<mu>_card:
  "card (nested_prop_atoms\<^sub>\<mu> \<phi> X) \<le> card (nested_prop_atoms \<phi>)"
  unfolding nested_prop_atoms\<^sub>\<mu>_def
  by (metis Collect_mem_eq card_image_le image_Collect nested_prop_atoms_finite)

lemma GF_advice_nested_prop_atoms\<^sub>\<nu>:
  "nested_prop_atoms (\<phi>[X]\<^sub>\<nu>) \<subseteq> nested_prop_atoms\<^sub>\<nu> \<phi> X"
  by (induction \<phi>) (unfold nested_prop_atoms\<^sub>\<nu>_def, force+)

lemma FG_advice_nested_prop_atoms\<^sub>\<mu>:
  "nested_prop_atoms (\<phi>[Y]\<^sub>\<mu>) \<subseteq> nested_prop_atoms\<^sub>\<mu> \<phi> Y"
  by (induction \<phi>) (unfold nested_prop_atoms\<^sub>\<mu>_def, force+)

lemma GF_advice_nested_prop_atoms_card:
  "card (nested_prop_atoms (\<phi>[X]\<^sub>\<nu>)) \<le> card (nested_prop_atoms \<phi>)"
proof -
  have "card (nested_prop_atoms (\<phi>[X]\<^sub>\<nu>)) \<le> card (nested_prop_atoms\<^sub>\<nu> \<phi> X)"
    by (simp add: nested_prop_atoms\<^sub>\<nu>_finite GF_advice_nested_prop_atoms\<^sub>\<nu> card_mono)

  then show ?thesis
    using nested_prop_atoms\<^sub>\<nu>_card le_trans by blast
qed

lemma FG_advice_nested_prop_atoms_card:
  "card (nested_prop_atoms (\<phi>[Y]\<^sub>\<mu>)) \<le> card (nested_prop_atoms \<phi>)"
proof -
  have "card (nested_prop_atoms (\<phi>[Y]\<^sub>\<mu>)) \<le> card (nested_prop_atoms\<^sub>\<mu> \<phi> Y)"
    by (simp add: nested_prop_atoms\<^sub>\<mu>_finite FG_advice_nested_prop_atoms\<^sub>\<mu> card_mono)

  then show ?thesis
    using nested_prop_atoms\<^sub>\<mu>_card le_trans by blast
qed



subsection \<open>Intersecting the Advice Set\<close>

lemma GF_advice_inter:
  "X \<inter> subformulas\<^sub>\<mu> \<phi> \<subseteq> S \<Longrightarrow> \<phi>[X \<inter> S]\<^sub>\<nu> = \<phi>[X]\<^sub>\<nu>"
  by (induction \<phi>) auto

lemma GF_advice_inter_subformulas:
  "\<phi>[X \<inter> subformulas\<^sub>\<mu> \<phi>]\<^sub>\<nu> = \<phi>[X]\<^sub>\<nu>"
  using GF_advice_inter by blast

lemma GF_advice_minus_subformulas:
  "\<psi> \<notin> subformulas\<^sub>\<mu> \<phi> \<Longrightarrow> \<phi>[X - {\<psi>}]\<^sub>\<nu> = \<phi>[X]\<^sub>\<nu>"
proof -
  assume "\<psi> \<notin> subformulas\<^sub>\<mu> \<phi>"
  then have "subformulas\<^sub>\<mu> \<phi> \<inter> X \<subseteq> X - {\<psi>}"
    by blast
  then show "\<phi>[X - {\<psi>}]\<^sub>\<nu> = \<phi>[X]\<^sub>\<nu>"
    by (metis GF_advice_inter Diff_subset Int_absorb1 inf.commute)
qed

lemma GF_advice_minus_size:
  "\<lbrakk>size \<phi> \<le> size \<psi>; \<phi> \<noteq> \<psi>\<rbrakk> \<Longrightarrow> \<phi>[X - {\<psi>}]\<^sub>\<nu> = \<phi>[X]\<^sub>\<nu>"
  using subfrmlsn_size subformulas\<^sub>\<mu>_subfrmlsn GF_advice_minus_subformulas
  by fastforce


lemma FG_advice_inter:
  "Y \<inter> subformulas\<^sub>\<nu> \<phi> \<subseteq> S \<Longrightarrow> \<phi>[Y \<inter> S]\<^sub>\<mu> = \<phi>[Y]\<^sub>\<mu>"
  by (induction \<phi>) auto

lemma FG_advice_inter_subformulas:
  "\<phi>[Y \<inter> subformulas\<^sub>\<nu> \<phi>]\<^sub>\<mu> = \<phi>[Y]\<^sub>\<mu>"
  using FG_advice_inter by blast

lemma FG_advice_minus_subformulas:
  "\<psi> \<notin> subformulas\<^sub>\<nu> \<phi> \<Longrightarrow> \<phi>[Y - {\<psi>}]\<^sub>\<mu> = \<phi>[Y]\<^sub>\<mu>"
proof -
  assume "\<psi> \<notin> subformulas\<^sub>\<nu> \<phi>"
  then have "subformulas\<^sub>\<nu> \<phi> \<inter> Y \<subseteq> Y - {\<psi>}"
    by blast
  then show "\<phi>[Y - {\<psi>}]\<^sub>\<mu>  = \<phi>[Y]\<^sub>\<mu>"
    by (metis FG_advice_inter Diff_subset Int_absorb1 inf.commute)
qed

lemma FG_advice_minus_size:
  "\<lbrakk>size \<phi> \<le> size \<psi>; \<phi> \<noteq> \<psi>\<rbrakk> \<Longrightarrow> \<phi>[Y - {\<psi>}]\<^sub>\<mu> = \<phi>[Y]\<^sub>\<mu>"
  using subfrmlsn_size subformulas\<^sub>\<nu>_subfrmlsn FG_advice_minus_subformulas
  by fastforce

lemma FG_advice_insert:
  "\<lbrakk>\<psi> \<notin> Y; size \<phi> < size \<psi>\<rbrakk> \<Longrightarrow> \<phi>[insert \<psi> Y]\<^sub>\<mu> = \<phi>[Y]\<^sub>\<mu>"
  by (metis FG_advice_minus_size Diff_insert_absorb less_imp_le neq_iff)



subsection \<open>Correctness GF-advice function\<close>

lemma GF_advice_a1:
  "\<lbrakk>\<F> \<phi> w \<subseteq> X; w \<Turnstile>\<^sub>n \<phi>\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu>"
proof (induction \<phi> arbitrary: w)
  case (Next_ltln \<phi>)
  then show ?case
    using \<F>_suffix by simp blast
next
  case (Until_ltln \<phi>1 \<phi>2)

  have "\<F> (\<phi>1 W\<^sub>n \<phi>2) w \<subseteq> \<F> (\<phi>1 U\<^sub>n \<phi>2) w"
    by fastforce
  then have "\<F> (\<phi>1 W\<^sub>n \<phi>2) w \<subseteq> X" and "w \<Turnstile>\<^sub>n \<phi>1 W\<^sub>n \<phi>2"
    using Until_ltln.prems ltln_strong_to_weak by blast+
  then have "w \<Turnstile>\<^sub>n \<phi>1[X]\<^sub>\<nu> W\<^sub>n \<phi>2[X]\<^sub>\<nu>"
    using Until_ltln.IH
    by simp (meson \<F>_suffix subset_trans sup.boundedE)

  moreover

  have "w \<Turnstile>\<^sub>n \<phi>1 U\<^sub>n \<phi>2"
    using Until_ltln.prems by simp
  then have "\<phi>1 U\<^sub>n \<phi>2 \<in> \<F> (\<phi>1 U\<^sub>n \<phi>2) w"
    by force
  then have "\<phi>1 U\<^sub>n \<phi>2 \<in> X"
    using Until_ltln.prems by fast

  ultimately show ?case
    by auto
next
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
    by simp (meson \<F>_suffix subset_trans sup.boundedE)
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  then show ?case
    by simp (meson \<F>_suffix subset_trans sup.boundedE)
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)

  have "\<F> (\<phi>1 R\<^sub>n \<phi>2) w \<subseteq> \<F> (\<phi>1 M\<^sub>n \<phi>2) w"
    by fastforce
  then have "\<F> (\<phi>1 R\<^sub>n \<phi>2) w \<subseteq> X" and "w \<Turnstile>\<^sub>n \<phi>1 R\<^sub>n \<phi>2"
    using StrongRelease_ltln.prems ltln_strong_to_weak by blast+
  then have "w \<Turnstile>\<^sub>n \<phi>1[X]\<^sub>\<nu> R\<^sub>n \<phi>2[X]\<^sub>\<nu>"
    using StrongRelease_ltln.IH
    by simp (meson \<F>_suffix subset_trans sup.boundedE)

  moreover

  have "w \<Turnstile>\<^sub>n \<phi>1 M\<^sub>n \<phi>2"
    using StrongRelease_ltln.prems by simp
  then have "\<phi>1 M\<^sub>n \<phi>2 \<in> \<F> (\<phi>1 M\<^sub>n \<phi>2) w"
    by force
  then have "\<phi>1 M\<^sub>n \<phi>2 \<in> X"
    using StrongRelease_ltln.prems by fast

  ultimately show ?case
    by auto
qed auto

lemma GF_advice_a2_helper:
  "\<lbrakk>\<forall>\<psi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>); w \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu>\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof (induction \<phi> arbitrary: w)
  case (Next_ltln \<phi>)
  then show ?case
    unfolding GF_advice.simps semantics_ltln.simps(7)
    using GF_suffix by blast
next
  case (Until_ltln \<phi>1 \<phi>2)

  then have "\<phi>1 U\<^sub>n \<phi>2 \<in> X"
    using ccontr[of "\<phi>1 U\<^sub>n \<phi>2 \<in> X"] by force
  then have "w \<Turnstile>\<^sub>n F\<^sub>n \<phi>2"
    using Until_ltln.prems by fastforce

  moreover

  have "w \<Turnstile>\<^sub>n (\<phi>1 U\<^sub>n \<phi>2)[X]\<^sub>\<nu>"
    using Until_ltln.prems by simp
  then have "w \<Turnstile>\<^sub>n (\<phi>1[X]\<^sub>\<nu>) W\<^sub>n (\<phi>2[X]\<^sub>\<nu>)"
    unfolding GF_advice.simps using `\<phi>1 U\<^sub>n \<phi>2 \<in> X` by simp
  then have "w \<Turnstile>\<^sub>n \<phi>1 W\<^sub>n \<phi>2"
    unfolding GF_advice.simps semantics_ltln.simps(10)
    by (metis GF_suffix Until_ltln.IH Until_ltln.prems(1))

  ultimately show ?case
    using ltln_weak_to_strong by blast
next
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding GF_advice.simps semantics_ltln.simps(9)
    by (metis GF_suffix Release_ltln.IH Release_ltln.prems(1))
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding GF_advice.simps semantics_ltln.simps(10)
    by (metis GF_suffix)
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)

  then have "\<phi>1 M\<^sub>n \<phi>2 \<in> X"
    using ccontr[of "\<phi>1 M\<^sub>n \<phi>2 \<in> X"] by force
  then have "w \<Turnstile>\<^sub>n F\<^sub>n \<phi>1"
    using StrongRelease_ltln.prems by fastforce

  moreover

  have "w \<Turnstile>\<^sub>n (\<phi>1 M\<^sub>n \<phi>2)[X]\<^sub>\<nu>"
    using StrongRelease_ltln.prems by simp
  then have "w \<Turnstile>\<^sub>n (\<phi>1[X]\<^sub>\<nu>) R\<^sub>n (\<phi>2[X]\<^sub>\<nu>)"
    unfolding GF_advice.simps using `\<phi>1 M\<^sub>n \<phi>2 \<in> X` by simp
  then have "w \<Turnstile>\<^sub>n \<phi>1 R\<^sub>n \<phi>2"
    unfolding GF_advice.simps semantics_ltln.simps(9)
    by (metis GF_suffix StrongRelease_ltln.IH StrongRelease_ltln.prems(1))

  ultimately show ?case
    using ltln_weak_to_strong by blast
qed auto

lemma GF_advice_a2:
  "\<lbrakk>X \<subseteq> \<G>\<F> \<phi> w; w \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu>\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  by (metis GF_advice_a2_helper \<G>\<F>_elim subset_eq)

lemma GF_advice_a3:
  "\<lbrakk>X = \<F> \<phi> w; X = \<G>\<F> \<phi> w\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu>"
  using GF_advice_a1 GF_advice_a2 by fastforce



subsection \<open>Correctness FG-advice function\<close>

lemma FG_advice_b1:
  "\<lbrakk>\<F>\<G> \<phi> w \<subseteq> Y; w \<Turnstile>\<^sub>n \<phi>\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>[Y]\<^sub>\<mu>"
proof (induction \<phi> arbitrary: w)
  case (Next_ltln \<phi>)
  then show ?case
    using \<F>\<G>_suffix by simp blast
next
  case (Until_ltln \<phi>1 \<phi>2)
  then show ?case
    by simp (metis \<F>\<G>_suffix)
next
  case (Release_ltln \<phi>1 \<phi>2)

  show ?case
  proof (cases "\<phi>1 R\<^sub>n \<phi>2 \<in> Y")
    case False
    then have "\<phi>1 R\<^sub>n \<phi>2 \<notin> \<F>\<G> (\<phi>1 R\<^sub>n \<phi>2) w"
      using Release_ltln.prems by blast
    then have "\<not> w \<Turnstile>\<^sub>n G\<^sub>n \<phi>2"
      by fastforce
    then have "w \<Turnstile>\<^sub>n \<phi>1 M\<^sub>n \<phi>2"
      using Release_ltln.prems ltln_weak_to_strong by blast

    moreover

    have "\<F>\<G> (\<phi>1 M\<^sub>n \<phi>2) w \<subseteq> \<F>\<G> (\<phi>1 R\<^sub>n \<phi>2) w"
      by fastforce
    then have "\<F>\<G> (\<phi>1 M\<^sub>n \<phi>2) w \<subseteq> Y"
      using Release_ltln.prems by blast

    ultimately show ?thesis
      using Release_ltln.IH by simp (metis \<F>\<G>_suffix)
  qed simp
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)

  show ?case
  proof (cases "\<phi>1 W\<^sub>n \<phi>2 \<in> Y")
    case False
    then have "\<phi>1 W\<^sub>n \<phi>2 \<notin> \<F>\<G> (\<phi>1 W\<^sub>n \<phi>2) w"
      using WeakUntil_ltln.prems by blast
    then have "\<not> w \<Turnstile>\<^sub>n G\<^sub>n \<phi>1"
      by fastforce
    then have "w \<Turnstile>\<^sub>n \<phi>1 U\<^sub>n \<phi>2"
      using WeakUntil_ltln.prems ltln_weak_to_strong by blast

    moreover

    have "\<F>\<G> (\<phi>1 U\<^sub>n \<phi>2) w \<subseteq> \<F>\<G> (\<phi>1 W\<^sub>n \<phi>2) w"
      by fastforce
    then have "\<F>\<G> (\<phi>1 U\<^sub>n \<phi>2) w \<subseteq> Y"
      using WeakUntil_ltln.prems by blast

    ultimately show ?thesis
      using WeakUntil_ltln.IH by simp (metis \<F>\<G>_suffix)
  qed simp
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)
  then show ?case
    by simp (metis \<F>\<G>_suffix)
qed auto

lemma FG_advice_b2_helper:
  "\<lbrakk>\<forall>\<psi> \<in> Y. w \<Turnstile>\<^sub>n G\<^sub>n \<psi>; w \<Turnstile>\<^sub>n \<phi>[Y]\<^sub>\<mu>\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof (induction \<phi> arbitrary: w)
  case (Until_ltln \<phi>1 \<phi>2)
  then show ?case
    by simp (metis (no_types, lifting) suffix_suffix)
next
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
  proof (cases "\<phi>1 R\<^sub>n \<phi>2 \<in> Y")
    case True
    then show ?thesis
      using Release_ltln.prems by force
  next
    case False
    then have "w \<Turnstile>\<^sub>n (\<phi>1[Y]\<^sub>\<mu>) M\<^sub>n (\<phi>2[Y]\<^sub>\<mu>)"
      using Release_ltln.prems by simp
    then have "w \<Turnstile>\<^sub>n \<phi>1 M\<^sub>n \<phi>2"
      using Release_ltln
      by simp (metis (no_types, lifting) suffix_suffix)
    then show ?thesis
      using ltln_strong_to_weak by fast
  qed
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  then show ?case
  proof (cases "\<phi>1 W\<^sub>n \<phi>2 \<in> Y")
    case True
    then show ?thesis
      using WeakUntil_ltln.prems by force
  next
    case False
    then have "w \<Turnstile>\<^sub>n (\<phi>1[Y]\<^sub>\<mu>) U\<^sub>n (\<phi>2[Y]\<^sub>\<mu>)"
      using WeakUntil_ltln.prems by simp
    then have "w \<Turnstile>\<^sub>n \<phi>1 U\<^sub>n \<phi>2"
      using WeakUntil_ltln
      by simp (metis (no_types, lifting) suffix_suffix)
    then show ?thesis
      using ltln_strong_to_weak by fast
  qed
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)
  then show ?case
    by simp (metis (no_types, lifting) suffix_suffix)
qed auto

lemma FG_advice_b2:
  "\<lbrakk>Y \<subseteq> \<G> \<phi> w; w \<Turnstile>\<^sub>n \<phi>[Y]\<^sub>\<mu>\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  by (metis FG_advice_b2_helper \<G>_elim subset_eq)

lemma FG_advice_b3:
  "\<lbrakk>Y = \<F>\<G> \<phi> w; Y = \<G> \<phi> w\<rbrakk> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>[Y]\<^sub>\<mu>"
  using FG_advice_b1 FG_advice_b2 by fastforce



subsection \<open>Advice functions and the after function\<close>

lemma GF_advice_af_letter:
  "(x ## w) \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu> \<Longrightarrow> w \<Turnstile>\<^sub>n (af_letter \<phi> x)[X]\<^sub>\<nu>"
proof (induction \<phi>)
  case (Until_ltln \<phi>1 \<phi>2)

  then have "w \<Turnstile>\<^sub>n af_letter ((\<phi>1 U\<^sub>n \<phi>2)[X]\<^sub>\<nu>) x"
    using af_letter_build by blast

  then show ?case
    using Until_ltln.IH af_letter_build by fastforce
next
  case (Release_ltln \<phi>1 \<phi>2)

  then have "w \<Turnstile>\<^sub>n af_letter ((\<phi>1 R\<^sub>n \<phi>2)[X]\<^sub>\<nu>) x"
    using af_letter_build by blast

  then show ?case
    using Release_ltln.IH af_letter_build by auto
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)

  then have "w \<Turnstile>\<^sub>n af_letter ((\<phi>1 W\<^sub>n \<phi>2)[X]\<^sub>\<nu>) x"
    using af_letter_build by blast

  then show ?case
    using WeakUntil_ltln.IH af_letter_build by auto
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)

  then have "w \<Turnstile>\<^sub>n af_letter ((\<phi>1 M\<^sub>n \<phi>2)[X]\<^sub>\<nu>) x"
    using af_letter_build by blast

  then show ?case
    using StrongRelease_ltln.IH af_letter_build by force
qed auto

lemma GF_advice_af:
  "(w \<frown> w') \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu> \<Longrightarrow> w' \<Turnstile>\<^sub>n (af \<phi> w)[X]\<^sub>\<nu>"
  by (induction w arbitrary: \<phi>) (simp, insert GF_advice_af_letter, fastforce)



subsection \<open>Advice Functions and Propositional Entailment\<close>

lemma GF_advice_prop_entailment:
  "\<A> \<Turnstile>\<^sub>P \<phi>[X]\<^sub>\<nu> \<Longrightarrow> {\<psi>. \<psi>[X]\<^sub>\<nu> \<in> \<A>} \<Turnstile>\<^sub>P \<phi>"
  "false\<^sub>n \<notin> \<A> \<Longrightarrow> {\<psi>. \<psi>[X]\<^sub>\<nu> \<in> \<A>} \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<A> \<Turnstile>\<^sub>P \<phi>[X]\<^sub>\<nu>"
  by (induction \<phi>) (auto, meson, meson)

lemma GF_advice_iff_prop_entailment:
  "false\<^sub>n \<notin> \<A> \<Longrightarrow> \<A> \<Turnstile>\<^sub>P \<phi>[X]\<^sub>\<nu> \<longleftrightarrow> {\<psi>. \<psi>[X]\<^sub>\<nu> \<in> \<A>} \<Turnstile>\<^sub>P \<phi>"
  by (metis GF_advice_prop_entailment)

lemma FG_advice_prop_entailment:
  "true\<^sub>n \<in> \<A> \<Longrightarrow> \<A> \<Turnstile>\<^sub>P \<phi>[Y]\<^sub>\<mu> \<Longrightarrow> {\<psi>. \<psi>[Y]\<^sub>\<mu> \<in> \<A>} \<Turnstile>\<^sub>P \<phi>"
  "{\<psi>. \<psi>[Y]\<^sub>\<mu> \<in> \<A>} \<Turnstile>\<^sub>P \<phi> \<Longrightarrow> \<A> \<Turnstile>\<^sub>P \<phi>[Y]\<^sub>\<mu>"
  by (induction \<phi>) auto

lemma FG_advice_iff_prop_entailment:
  "true\<^sub>n \<in> \<A> \<Longrightarrow> \<A> \<Turnstile>\<^sub>P \<phi>[X]\<^sub>\<mu> \<longleftrightarrow> {\<psi>. \<psi>[X]\<^sub>\<mu> \<in> \<A>} \<Turnstile>\<^sub>P \<phi>"
  by (metis FG_advice_prop_entailment)

lemma GF_advice_subst:
  "\<phi>[X]\<^sub>\<nu> = subst \<phi> (\<lambda>\<psi>. Some (\<psi>[X]\<^sub>\<nu>))"
  by (induction \<phi>) auto

lemma FG_advice_subst:
  "\<phi>[X]\<^sub>\<mu> = subst \<phi> (\<lambda>\<psi>. Some (\<psi>[X]\<^sub>\<mu>))"
  by (induction \<phi>) auto

lemma GF_advice_prop_congruent:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> \<phi>[X]\<^sub>\<nu> \<longrightarrow>\<^sub>P \<psi>[X]\<^sub>\<nu>"
  "\<phi> \<sim>\<^sub>P \<psi> \<Longrightarrow> \<phi>[X]\<^sub>\<nu> \<sim>\<^sub>P \<psi>[X]\<^sub>\<nu>"
  by (metis GF_advice_subst subst_respects_ltl_prop_entailment)+

lemma FG_advice_prop_congruent:
  "\<phi> \<longrightarrow>\<^sub>P \<psi> \<Longrightarrow> \<phi>[X]\<^sub>\<mu> \<longrightarrow>\<^sub>P \<psi>[X]\<^sub>\<mu>"
  "\<phi> \<sim>\<^sub>P \<psi> \<Longrightarrow> \<phi>[X]\<^sub>\<mu> \<sim>\<^sub>P \<psi>[X]\<^sub>\<mu>"
  by (metis FG_advice_subst subst_respects_ltl_prop_entailment)+

locale GF_advice_congruent = ltl_equivalence +
  assumes
    GF_advice_congruent: "\<phi> \<sim> \<psi> \<Longrightarrow> \<phi>[X]\<^sub>\<nu> \<sim> \<psi>[X]\<^sub>\<nu>"
begin

end

interpretation prop_GF_advice_compatible: GF_advice_congruent "(\<sim>\<^sub>P)"
  by unfold_locales (simp add: GF_advice_prop_congruent(2))

end
