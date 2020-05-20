(*
    Author:   Benedikt Seidl
    Author:   Salomon Sickert
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

lemma GF_advice_monotone:
  "X \<subseteq> Y \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>[Y]\<^sub>\<nu>"
proof (induction \<phi> arbitrary: w)
  case (Until_ltln \<phi> \<psi>)
  then show ?case
    by (cases "\<phi> U\<^sub>n \<psi> \<in> X") (simp_all, blast)
next
  case (Release_ltln \<phi> \<psi>)
  then show ?case by (simp, blast)
next
  case (WeakUntil_ltln \<phi> \<psi>)
  then show ?case by (simp, blast)
next
  case (StrongRelease_ltln \<phi> \<psi>)
  then show ?case
    by (cases "\<phi> M\<^sub>n \<psi> \<in> X") (simp_all, blast)
qed auto

lemma FG_advice_monotone:
  "X \<subseteq> Y \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<mu> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>[Y]\<^sub>\<mu>"
proof (induction \<phi> arbitrary: w)
  case (Until_ltln \<phi> \<psi>)
  then show ?case by (simp, blast)
next
  case (Release_ltln \<phi> \<psi>)
  then show ?case
    by (cases "\<phi> R\<^sub>n \<psi> \<in> X") (auto, blast)
next
  case (WeakUntil_ltln \<phi> \<psi>)
  then show ?case
    by (cases "\<phi> W\<^sub>n \<psi> \<in> X") (auto, blast)
next
  case (StrongRelease_ltln \<phi> \<psi>)
  then show ?case by (simp, blast)
qed auto

lemma GF_advice_ite_simps[simp]:
  "(if P then true\<^sub>n else false\<^sub>n)[X]\<^sub>\<nu> = (if P then true\<^sub>n else false\<^sub>n)"
  "(if P then false\<^sub>n else true\<^sub>n)[X]\<^sub>\<nu> = (if P then false\<^sub>n else true\<^sub>n)"
  by simp_all

lemma FG_advice_ite_simps[simp]:
  "(if P then true\<^sub>n else false\<^sub>n)[Y]\<^sub>\<mu> = (if P then true\<^sub>n else false\<^sub>n)"
  "(if P then false\<^sub>n else true\<^sub>n)[Y]\<^sub>\<mu> = (if P then false\<^sub>n else true\<^sub>n)"
  by simp_all

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

lemma nested_prop_atoms\<^sub>\<nu>_subset:
  "nested_prop_atoms \<phi> \<subseteq> nested_prop_atoms \<psi> \<Longrightarrow> nested_prop_atoms\<^sub>\<nu> \<phi> X \<subseteq> nested_prop_atoms\<^sub>\<nu> \<psi> X"
  unfolding nested_prop_atoms\<^sub>\<nu>_def by blast

lemma nested_prop_atoms\<^sub>\<mu>_subset:
  "nested_prop_atoms \<phi> \<subseteq> nested_prop_atoms \<psi> \<Longrightarrow> nested_prop_atoms\<^sub>\<mu> \<phi> Y \<subseteq> nested_prop_atoms\<^sub>\<mu> \<psi> Y"
  unfolding nested_prop_atoms\<^sub>\<mu>_def by blast

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



subsection \<open>Advice Functions and the ``after'' Function\<close>

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

lemma FG_advice_af_letter:
  "w \<Turnstile>\<^sub>n (af_letter \<phi> x)[Y]\<^sub>\<mu> \<Longrightarrow> (x ## w) \<Turnstile>\<^sub>n \<phi>[Y]\<^sub>\<mu>"
proof (induction \<phi>)
  case (Prop_ltln a)
  then show ?case
    using semantics_ltln.simps(3) by fastforce
next
  case (Until_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding af_letter.simps FG_advice.simps semantics_ltln.simps(5,6)
    using af_letter_build apply (cases "w \<Turnstile>\<^sub>n af_letter \<phi>2 x[Y]\<^sub>\<mu>") apply force
    by (metis af_letter.simps(8) semantics_ltln.simps(5) semantics_ltln.simps(6))
next
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
    apply (cases "\<phi>1 R\<^sub>n \<phi>2 \<in> Y")
    apply simp
    unfolding af_letter.simps FG_advice.simps semantics_ltln.simps(5,6)
    using af_letter_build  apply (cases "w \<Turnstile>\<^sub>n af_letter \<phi>1 x[Y]\<^sub>\<mu>") apply force
    by (metis (full_types) af_letter.simps(11) semantics_ltln.simps(5) semantics_ltln.simps(6))
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  then show ?case
    apply (cases "\<phi>1 W\<^sub>n \<phi>2 \<in> Y")
    apply simp
    unfolding af_letter.simps FG_advice.simps semantics_ltln.simps(5,6)
    using af_letter_build  apply (cases "w \<Turnstile>\<^sub>n af_letter \<phi>2 x[Y]\<^sub>\<mu>") apply force
    by (metis (full_types) af_letter.simps(8) semantics_ltln.simps(5) semantics_ltln.simps(6))
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)
  then show ?case
    unfolding af_letter.simps FG_advice.simps semantics_ltln.simps(5,6)
    using af_letter_build apply (cases "w \<Turnstile>\<^sub>n af_letter \<phi>1 x[Y]\<^sub>\<mu>") apply force
    by (metis af_letter.simps(11) semantics_ltln.simps(5) semantics_ltln.simps(6))
qed auto

lemma GF_advice_af:
  "(w \<frown> w') \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu> \<Longrightarrow> w' \<Turnstile>\<^sub>n (af \<phi> w)[X]\<^sub>\<nu>"
  by (induction w arbitrary: \<phi>) (simp, insert GF_advice_af_letter, fastforce)

lemma FG_advice_af:
  "w' \<Turnstile>\<^sub>n (af \<phi> w)[X]\<^sub>\<mu> \<Longrightarrow> (w \<frown> w') \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<mu>"
  by (induction w arbitrary: \<phi>) (simp, insert FG_advice_af_letter, fastforce)

lemma GF_advice_af_2:
  "w \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu> \<Longrightarrow> suffix i w \<Turnstile>\<^sub>n (af \<phi> (prefix i w))[X]\<^sub>\<nu>"
  using GF_advice_af by force

lemma FG_advice_af_2:
  "suffix i w \<Turnstile>\<^sub>n (af \<phi> (prefix i w))[X]\<^sub>\<mu> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<mu>"
  using FG_advice_af by force

(* TODO move to Omega_Words_Fun.thy ?? *)
lemma prefix_suffix_subsequence: "prefix i (suffix j w) = (w [j \<rightarrow> i + j])"
  by (simp add: add.commute)

text \<open>We show this generic lemma to prove the following theorems:\<close>

lemma GF_advice_sync:
  fixes index :: "nat \<Rightarrow> nat"
  fixes formula :: "nat \<Rightarrow> 'a ltln"
  assumes "\<And>i. i < n \<Longrightarrow> \<exists>j. suffix ((index i) + j) w \<Turnstile>\<^sub>n af (formula i) (w [index i \<rightarrow> (index i) + j])[X]\<^sub>\<nu>"
  shows "\<exists>k. (\<forall>i < n. k \<ge> index i \<and> suffix k w \<Turnstile>\<^sub>n af (formula i) (w [index i \<rightarrow> k])[X]\<^sub>\<nu>)"
  using assms
proof (induction n)
  case (Suc n)

  obtain k1 where leq1: "\<And>i. i < n \<Longrightarrow> k1 \<ge> index i"
    and suffix1: "\<And>i. i < n \<Longrightarrow> suffix k1 w \<Turnstile>\<^sub>n af (formula i) (w [(index i) \<rightarrow> k1])[X]\<^sub>\<nu>"
    using Suc less_SucI by blast

  obtain k2 where leq2: "k2 \<ge> index n"
    and suffix2: "suffix k2 w \<Turnstile>\<^sub>n af (formula n) (w [index n \<rightarrow> k2])[X]\<^sub>\<nu>"
    using le_add1 Suc.prems by blast

  define k where "k \<equiv> k1 + k2"

  have "\<And>i. i < Suc n \<Longrightarrow> k \<ge> index i"
    unfolding k_def by (metis leq1 leq2 less_SucE trans_le_add1 trans_le_add2)

  moreover

  {
    have "\<And>i. i < n \<Longrightarrow> suffix k w \<Turnstile>\<^sub>n af (formula i) (w [(index i) \<rightarrow> k])[X]\<^sub>\<nu>"
      unfolding k_def
      by (metis GF_advice_af_2[OF suffix1, unfolded suffix_suffix prefix_suffix_subsequence] af_subsequence_append leq1 add.commute le_add1)

    moreover

    have "suffix k w \<Turnstile>\<^sub>n af (formula n) (w [index n \<rightarrow> k])[X]\<^sub>\<nu>"
      unfolding k_def
      by (metis GF_advice_af_2[OF suffix2, unfolded suffix_suffix prefix_suffix_subsequence] af_subsequence_append leq2 add.commute le_add1)

    ultimately

    have "\<And>i. i \<le> n \<Longrightarrow> suffix k w \<Turnstile>\<^sub>n af (formula i) (w [(index i) \<rightarrow> k])[X]\<^sub>\<nu>"
      using nat_less_le by blast
  }

  ultimately

  show ?case
    by (meson less_Suc_eq_le)
qed simp

lemma GF_advice_sync_and:
  assumes "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>"
  assumes "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<psi> (prefix i w)[X]\<^sub>\<nu>"
  shows "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu> \<and> suffix i w \<Turnstile>\<^sub>n af \<psi> (prefix i w)[X]\<^sub>\<nu>"
proof -
  let ?formula = "\<lambda>i :: nat. (if (i = 0) then \<phi> else \<psi>)"

  have assms: "\<And>i. i < 2 \<Longrightarrow> \<exists>j. suffix j w \<Turnstile>\<^sub>n af (?formula i) (w [0 \<rightarrow> j])[X]\<^sub>\<nu>"
    using assms by simp
  obtain k where k_def: "\<And>i :: nat. i < 2 \<Longrightarrow> suffix k w \<Turnstile>\<^sub>n af (if i = 0 then \<phi> else \<psi>) (prefix k w)[X]\<^sub>\<nu>"
    using GF_advice_sync[of "2" "\<lambda>i. 0" w ?formula, simplified, OF assms, simplified] by blast
  show ?thesis
    using k_def[of 0] k_def[of 1] by auto
qed

lemma GF_advice_sync_less:
  assumes "\<And>i. i < n \<Longrightarrow> \<exists>j. suffix (i + j) w \<Turnstile>\<^sub>n af \<phi> (w [i \<rightarrow> j + i])[X]\<^sub>\<nu>"
  assumes "\<exists>j. suffix (n + j) w \<Turnstile>\<^sub>n af \<psi> (w [n \<rightarrow> j + n])[X]\<^sub>\<nu>"
  shows "\<exists>k \<ge> n. (\<forall>j < n. suffix k w \<Turnstile>\<^sub>n af \<phi> (w [j \<rightarrow> k])[X]\<^sub>\<nu>) \<and> suffix k w \<Turnstile>\<^sub>n af \<psi> (w [n \<rightarrow> k])[X]\<^sub>\<nu>"
proof -
  let ?index = "\<lambda>i. min i n"
  let ?formula = "\<lambda>i. if (i < n) then \<phi> else \<psi>"

  {
    fix i
    assume "i < Suc n"
    then have min_def: "min i n = i"
      by simp
    have "\<exists>j. suffix ((?index i) + j) w \<Turnstile>\<^sub>n af (?formula i) (w [?index i \<rightarrow> (?index i) + j])[X]\<^sub>\<nu>"
      unfolding min_def
      by (cases "i < n")
         (metis (full_types) assms(1) add.commute, metis (full_types) assms(2) \<open>i < Suc n\<close> add.commute  less_SucE)
  }

  then obtain k where leq: "(\<And>i. i < Suc n \<Longrightarrow> min i n \<le> k)"
    and suffix: "\<And>i. i < Suc n \<Longrightarrow> suffix k w \<Turnstile>\<^sub>n af (if i < n then \<phi> else \<psi>) (w [min i n \<rightarrow> k])[X]\<^sub>\<nu>"
    using GF_advice_sync[of "Suc n" ?index w ?formula X] by metis

  have "\<forall>j < n. suffix k w \<Turnstile>\<^sub>n af \<phi> (w [j \<rightarrow> k])[X]\<^sub>\<nu>"
    using suffix by (metis (full_types) less_SucI min.strict_order_iff)

  moreover

  have "suffix k w \<Turnstile>\<^sub>n af \<psi> (w [n \<rightarrow> k])[X]\<^sub>\<nu>"
    using suffix[of n, simplified] by blast

  moreover

  have "k \<ge> n"
    using leq by presburger

  ultimately
  show ?thesis
    by auto
qed

lemma GF_advice_sync_lesseq:
  assumes "\<And>i. i \<le> n \<Longrightarrow> \<exists>j. suffix (i + j) w \<Turnstile>\<^sub>n af \<phi> (w [i \<rightarrow> j + i])[X]\<^sub>\<nu>"
  assumes "\<exists>j. suffix (n + j) w \<Turnstile>\<^sub>n af \<psi> (w [n \<rightarrow> j + n])[X]\<^sub>\<nu>"
  shows "\<exists>k \<ge> n. (\<forall>j \<le> n. suffix k w \<Turnstile>\<^sub>n af \<phi> (w [j \<rightarrow> k])[X]\<^sub>\<nu>) \<and> suffix k w \<Turnstile>\<^sub>n af \<psi> (w [n \<rightarrow> k])[X]\<^sub>\<nu>"
proof -
  let ?index = "\<lambda>i. min i n"
  let ?formula = "\<lambda>i. if (i \<le> n) then \<phi> else \<psi>"

  {
    fix i
    assume "i < Suc (Suc n)"
    hence "\<exists>j. suffix ((?index i) + j) w \<Turnstile>\<^sub>n af (?formula i) (w [?index i \<rightarrow> (?index i) + j])[X]\<^sub>\<nu>"
    proof (cases "i < Suc n")
      case True
      then have min_def: "min i n = i"
        by simp
      show ?thesis
        unfolding min_def by (metis (full_types) assms(1) Suc_leI Suc_le_mono True add.commute)
    next
      case False
      then have i_def: "i = Suc n"
        using \<open>i < Suc (Suc n)\<close> less_antisym by blast
      have min_def: "min i n = n"
        unfolding i_def by simp
      show ?thesis
        using assms(2) False
        by (simp add: min_def add.commute)
    qed
  }

  then obtain k where leq: "(\<And>i. i \<le> Suc n \<Longrightarrow> min i n \<le> k)"
    and suffix: "\<And>i :: nat. i < Suc (Suc n) \<Longrightarrow> suffix k w \<Turnstile>\<^sub>n af (if i \<le> n then \<phi> else \<psi>) (w [min i n \<rightarrow> k])[X]\<^sub>\<nu>"
    using GF_advice_sync[of "Suc (Suc n)" ?index w ?formula X]
    by (metis (no_types, hide_lams) less_Suc_eq min_le_iff_disj)

  have "\<forall>j \<le> n. suffix k w \<Turnstile>\<^sub>n af \<phi> (w [j \<rightarrow> k])[X]\<^sub>\<nu>"
    using suffix by (metis (full_types) le_SucI less_Suc_eq_le min.orderE)

  moreover

  have "suffix k w \<Turnstile>\<^sub>n af \<psi> (w [n \<rightarrow> k])[X]\<^sub>\<nu>"
    using suffix[of "Suc n", simplified] by linarith

  moreover

  have "k \<ge> n"
    using leq by presburger

  ultimately
  show ?thesis
    by auto
qed

lemma af_subsequence_U_GF_advice:
  assumes "i \<le> n"
  assumes "suffix n w \<Turnstile>\<^sub>n ((af \<psi> (w [i \<rightarrow> n]))[X]\<^sub>\<nu>)"
  assumes "\<And>j. j < i \<Longrightarrow> suffix n w \<Turnstile>\<^sub>n ((af \<phi> (w [j \<rightarrow> n]))[X]\<^sub>\<nu>)"
  shows "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> U\<^sub>n \<psi>) (prefix (Suc n) w))[X]\<^sub>\<nu>"
  using assms
proof (induction i arbitrary: w n)
  case 0
  then have A: "suffix n w \<Turnstile>\<^sub>n ((af \<psi> (w [0 \<rightarrow> n]))[X]\<^sub>\<nu>)"
    by blast
  then have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<psi> (w [0 \<rightarrow> Suc n]))[X]\<^sub>\<nu>"
    using GF_advice_af_2[OF A, of 1] by simp
  then show ?case
    unfolding GF_advice.simps af_subsequence_U semantics_ltln.simps by blast
next
  case (Suc i)
  have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<phi> (prefix (Suc n) w))[X]\<^sub>\<nu>"
    using Suc.prems(3)[OF zero_less_Suc, THEN GF_advice_af_2, unfolded suffix_suffix, of 1]
    by simp
  moreover
  have B: "(Suc (n - 1)) = n"
    using Suc by simp
  note Suc.IH[of "n - 1" "suffix 1 w", unfolded suffix_suffix] Suc.prems
  then have "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> U\<^sub>n \<psi>) (w [1 \<rightarrow> (Suc n)]))[X]\<^sub>\<nu>"
    by (metis B One_nat_def Suc_le_mono Suc_mono plus_1_eq_Suc subsequence_shift)
  ultimately
  show ?case
    unfolding af_subsequence_U semantics_ltln.simps GF_advice.simps by blast
qed

lemma af_subsequence_M_GF_advice:
  assumes "i \<le> n"
  assumes "suffix n w \<Turnstile>\<^sub>n ((af \<phi> (w [i \<rightarrow> n]))[X]\<^sub>\<nu>)"
  assumes "\<And>j. j \<le> i \<Longrightarrow> suffix n w \<Turnstile>\<^sub>n ((af \<psi> (w [j \<rightarrow> n]))[X]\<^sub>\<nu>)"
  shows "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> M\<^sub>n \<psi>) (prefix (Suc n) w))[X]\<^sub>\<nu>"
  using assms
proof (induction i arbitrary: w n)
  case 0
  then have A: "suffix n w \<Turnstile>\<^sub>n ((af \<psi> (w [0 \<rightarrow> n]))[X]\<^sub>\<nu>)"
    by blast
  have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<psi> (w [0 \<rightarrow> Suc n]))[X]\<^sub>\<nu>"
    using GF_advice_af_2[OF A, of 1] by simp
  moreover
  have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<phi> (w [0 \<rightarrow> Suc n]))[X]\<^sub>\<nu>"
    using GF_advice_af_2[OF "0.prems"(2), of 1, unfolded suffix_suffix] by auto
  ultimately
  show ?case
    unfolding af_subsequence_M GF_advice.simps semantics_ltln.simps by blast
next
  case (Suc i)
  have "suffix 1 (suffix n w) \<Turnstile>\<^sub>n af (af \<psi> (prefix n w)) [suffix n w 0][X]\<^sub>\<nu>"
    by (metis (no_types) GF_advice_af_2 Suc.prems(3) plus_1_eq_Suc subsequence_singleton suffix_0 suffix_suffix zero_le)
  then have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<psi> (prefix (Suc n) w))[X]\<^sub>\<nu>"
    using Suc.prems(3)[THEN GF_advice_af_2, unfolded suffix_suffix, of 1] by simp
  moreover
  have B: "(Suc (n - 1)) = n"
    using Suc by simp
  note Suc.IH[of _ "suffix 1 w", unfolded subsequence_shift suffix_suffix]
  then have "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> M\<^sub>n \<psi>) (w [1 \<rightarrow> (Suc n)]))[X]\<^sub>\<nu>"
    by (metis B One_nat_def Suc_le_mono plus_1_eq_Suc Suc.prems)
  ultimately
  show ?case
    unfolding af_subsequence_M semantics_ltln.simps GF_advice.simps by blast
qed

lemma af_subsequence_R_GF_advice:
  assumes "i \<le> n"
  assumes "suffix n w \<Turnstile>\<^sub>n ((af \<phi> (w [i \<rightarrow> n]))[X]\<^sub>\<nu>)"
  assumes "\<And>j. j \<le> i \<Longrightarrow> suffix n w \<Turnstile>\<^sub>n ((af \<psi> (w [j \<rightarrow> n]))[X]\<^sub>\<nu>)"
  shows "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> R\<^sub>n \<psi>) (prefix (Suc n) w))[X]\<^sub>\<nu>"
  using assms
proof (induction i arbitrary: w n)
  case 0
  then have A: "suffix n w \<Turnstile>\<^sub>n ((af \<psi> (w [0 \<rightarrow> n]))[X]\<^sub>\<nu>)"
    by blast
  have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<psi> (w [0 \<rightarrow> Suc n]))[X]\<^sub>\<nu>"
    using GF_advice_af_2[OF A, of 1] by simp
  moreover
  have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<phi> (w [0 \<rightarrow> Suc n]))[X]\<^sub>\<nu>"
    using GF_advice_af_2[OF "0.prems"(2), of 1, unfolded suffix_suffix] by auto
  ultimately
  show ?case
    unfolding af_subsequence_R GF_advice.simps semantics_ltln.simps by blast
next
  case (Suc i)
  have "suffix 1 (suffix n w) \<Turnstile>\<^sub>n af (af \<psi> (prefix n w)) [suffix n w 0][X]\<^sub>\<nu>"
    by (metis (no_types) GF_advice_af_2 Suc.prems(3) plus_1_eq_Suc subsequence_singleton suffix_0 suffix_suffix zero_le)
  then have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<psi> (prefix (Suc n) w))[X]\<^sub>\<nu>"
    using Suc.prems(3)[THEN GF_advice_af_2, unfolded suffix_suffix, of 1] by simp
  moreover
  have B: "(Suc (n - 1)) = n"
    using Suc by simp
  note Suc.IH[of _ "suffix 1 w", unfolded subsequence_shift suffix_suffix]
  then have "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> R\<^sub>n \<psi>) (w [1 \<rightarrow> (Suc n)]))[X]\<^sub>\<nu>"
    by (metis B One_nat_def Suc_le_mono plus_1_eq_Suc Suc.prems)
  ultimately
  show ?case
    unfolding af_subsequence_R semantics_ltln.simps GF_advice.simps by blast
qed

lemma af_subsequence_W_GF_advice:
  assumes "i \<le> n"
  assumes "suffix n w \<Turnstile>\<^sub>n ((af \<psi> (w [i \<rightarrow> n]))[X]\<^sub>\<nu>)"
  assumes "\<And>j. j < i \<Longrightarrow> suffix n w \<Turnstile>\<^sub>n ((af \<phi> (w [j \<rightarrow> n]))[X]\<^sub>\<nu>)"
  shows "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> W\<^sub>n \<psi>) (prefix (Suc n) w))[X]\<^sub>\<nu>"
  using assms
proof (induction i arbitrary: w n)
  case 0
  then have A: "suffix n w \<Turnstile>\<^sub>n ((af \<psi> (w [0 \<rightarrow> n]))[X]\<^sub>\<nu>)"
    by blast
  have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<psi> (w [0 \<rightarrow> Suc n]))[X]\<^sub>\<nu>"
    using GF_advice_af_2[OF A, of 1] by simp
  then show ?case
    unfolding af_subsequence_W GF_advice.simps semantics_ltln.simps by blast
next
  case (Suc i)
  have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<phi> (prefix (Suc n) w))[X]\<^sub>\<nu>"
    using Suc.prems(3)[OF zero_less_Suc, THEN GF_advice_af_2, unfolded suffix_suffix, of 1]
    by simp
  moreover
  have B: "(Suc (n - 1)) = n"
    using Suc by simp
  note Suc.IH[of "n - 1" "suffix 1 w", unfolded suffix_suffix] Suc.prems
  then have "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> W\<^sub>n \<psi>) (w [1 \<rightarrow> (Suc n)]))[X]\<^sub>\<nu>"
    by (metis B One_nat_def Suc_le_mono Suc_mono plus_1_eq_Suc subsequence_shift)
  ultimately
  show ?case
    unfolding af_subsequence_W unfolding semantics_ltln.simps GF_advice.simps by simp
qed

lemma af_subsequence_R_GF_advice_connect:
  assumes "i \<le> n"
  assumes "suffix n w \<Turnstile>\<^sub>n af (\<phi> R\<^sub>n \<psi>) (w [i \<rightarrow> n])[X]\<^sub>\<nu>"
  assumes "\<And>j. j \<le> i \<Longrightarrow> suffix n w \<Turnstile>\<^sub>n ((af \<psi> (w [j \<rightarrow> n]))[X]\<^sub>\<nu>)"
  shows "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> R\<^sub>n \<psi>) (prefix (Suc n) w))[X]\<^sub>\<nu>"
  using assms
proof (induction i arbitrary: w n)
  case 0
  then have A: "suffix n w \<Turnstile>\<^sub>n ((af \<psi> (w [0 \<rightarrow> n]))[X]\<^sub>\<nu>)"
    by blast
  have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<psi> (w [0 \<rightarrow> Suc n]))[X]\<^sub>\<nu>"
    using GF_advice_af_2[OF A, of 1] by simp
  moreover
  have "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> R\<^sub>n \<psi>) (w [0 \<rightarrow> Suc n]))[X]\<^sub>\<nu>"
    using GF_advice_af_2[OF "0.prems"(2), of 1, unfolded suffix_suffix] by simp
  ultimately
  show ?case
    unfolding af_subsequence_R GF_advice.simps semantics_ltln.simps by blast
next
  case (Suc i)
  have "suffix 1 (suffix n w) \<Turnstile>\<^sub>n af (af \<psi> (prefix n w)) [suffix n w 0][X]\<^sub>\<nu>"
    by (metis (no_types) GF_advice_af_2 Suc.prems(3) plus_1_eq_Suc subsequence_singleton suffix_0 suffix_suffix zero_le)
  then have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<psi> (prefix (Suc n) w))[X]\<^sub>\<nu>"
    using Suc.prems(3)[THEN GF_advice_af_2, unfolded suffix_suffix, of 1] by simp
  moreover
  have B: "(Suc (n - 1)) = n"
    using Suc by simp
  note Suc.IH[of _ "suffix 1 w", unfolded subsequence_shift suffix_suffix]
  then have "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> R\<^sub>n \<psi>) (w [1 \<rightarrow> (Suc n)]))[X]\<^sub>\<nu>"
    by (metis B One_nat_def Suc_le_mono plus_1_eq_Suc Suc.prems)
  ultimately
  show ?case
    unfolding af_subsequence_R semantics_ltln.simps GF_advice.simps by blast
qed

lemma af_subsequence_W_GF_advice_connect:
  assumes "i \<le> n"
  assumes "suffix n w \<Turnstile>\<^sub>n af (\<phi> W\<^sub>n \<psi>) (w [i \<rightarrow> n])[X]\<^sub>\<nu>"
  assumes "\<And>j. j < i \<Longrightarrow> suffix n w \<Turnstile>\<^sub>n ((af \<phi> (w [j \<rightarrow> n]))[X]\<^sub>\<nu>)"
  shows "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> W\<^sub>n \<psi>) (prefix (Suc n) w))[X]\<^sub>\<nu>"
  using assms
proof (induction i arbitrary: w n)
  case 0
  have "suffix (Suc n) w \<Turnstile>\<^sub>n af_letter (af (\<phi> W\<^sub>n \<psi>) (prefix n w)) (w n)[X]\<^sub>\<nu>"
    by (simp add: "0.prems"(2) GF_advice_af_letter)
  moreover
  have "prefix (Suc n) w = prefix n w @ [w n]"
    using subseq_to_Suc by blast
  ultimately show ?case
    by (metis (no_types) foldl.simps(1) foldl.simps(2) foldl_append)
next
  case (Suc i)
  have "suffix (Suc n) w \<Turnstile>\<^sub>n (af \<phi> (prefix (Suc n) w))[X]\<^sub>\<nu>"
    using Suc.prems(3)[OF zero_less_Suc, THEN GF_advice_af_2, unfolded suffix_suffix, of 1] by simp
  moreover
  have "n > 0" and B: "(Suc (n - 1)) = n"
    using Suc by simp+
  note Suc.IH[of "n - 1" "suffix 1 w", unfolded suffix_suffix] Suc.prems
  then have "suffix (Suc n) w \<Turnstile>\<^sub>n (af (\<phi> W\<^sub>n \<psi>) (w [1 \<rightarrow> (Suc n)]))[X]\<^sub>\<nu>"
    by (metis B One_nat_def Suc_le_mono Suc_mono plus_1_eq_Suc subsequence_shift)
  ultimately
  show ?case
    unfolding af_subsequence_W unfolding semantics_ltln.simps GF_advice.simps by simp
qed


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


subsection \<open>GF-advice with Equivalence Relations\<close>

locale GF_advice_congruent = ltl_equivalence +
  fixes
    normalise :: "'a ltln \<Rightarrow> 'a ltln"
  assumes
    normalise_eq: "\<phi> \<sim> normalise \<phi>"
  assumes
    normalise_monotonic: "w \<Turnstile>\<^sub>n \<phi>[X]\<^sub>\<nu> \<Longrightarrow> w \<Turnstile>\<^sub>n (normalise \<phi>)[X]\<^sub>\<nu>"
  assumes
    normalise_eventually_equivalent:
      "w \<Turnstile>\<^sub>n (normalise \<phi>)[X]\<^sub>\<nu> \<Longrightarrow> (\<exists>i. suffix i w \<Turnstile>\<^sub>n (af \<phi> (prefix i w))[X]\<^sub>\<nu>)"
  assumes
    GF_advice_congruent: "\<phi> \<sim> \<psi> \<Longrightarrow> (normalise \<phi>)[X]\<^sub>\<nu> \<sim> (normalise \<psi>)[X]\<^sub>\<nu>"
begin

lemma normalise_language_equivalent[simp]:
  "w \<Turnstile>\<^sub>n normalise \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  using normalise_eq ltl_lang_equiv_def eq_implies_lang by blast

end

interpretation prop_GF_advice_compatible: GF_advice_congruent "(\<sim>\<^sub>P)" "id"
  by unfold_locales (simp add: GF_advice_af GF_advice_prop_congruent(2))+

end
