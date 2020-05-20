(*
    Author:   Salomon Sickert
    Author:   Benedikt Seidl
    License:  BSD
*)

section \<open>Master Theorem with Reduced Subformulas\<close>

theory Restricted_Master_Theorem
imports
  Master_Theorem
begin

subsection \<open>Restricted Set of Subformulas\<close>

fun restricted_subformulas_inner :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "restricted_subformulas_inner (\<phi> and\<^sub>n \<psi>) = restricted_subformulas_inner \<phi> \<union> restricted_subformulas_inner \<psi>"
| "restricted_subformulas_inner (\<phi> or\<^sub>n \<psi>) = restricted_subformulas_inner \<phi> \<union> restricted_subformulas_inner \<psi>"
| "restricted_subformulas_inner (X\<^sub>n \<phi>) = restricted_subformulas_inner \<phi>"
| "restricted_subformulas_inner (\<phi> U\<^sub>n \<psi>) = subformulas\<^sub>\<nu> (\<phi> U\<^sub>n \<psi>) \<union> subformulas\<^sub>\<mu> (\<phi> U\<^sub>n \<psi>)"
| "restricted_subformulas_inner (\<phi> R\<^sub>n \<psi>) = restricted_subformulas_inner \<phi> \<union> restricted_subformulas_inner \<psi>"
| "restricted_subformulas_inner (\<phi> W\<^sub>n \<psi>) = restricted_subformulas_inner \<phi> \<union> restricted_subformulas_inner \<psi>"
| "restricted_subformulas_inner (\<phi> M\<^sub>n \<psi>) = subformulas\<^sub>\<nu> (\<phi> M\<^sub>n \<psi>) \<union> subformulas\<^sub>\<mu> (\<phi> M\<^sub>n \<psi>)"
| "restricted_subformulas_inner _ = {}"

fun restricted_subformulas :: "'a ltln \<Rightarrow> 'a ltln set"
where
  "restricted_subformulas (\<phi> and\<^sub>n \<psi>) = restricted_subformulas \<phi> \<union> restricted_subformulas \<psi>"
| "restricted_subformulas (\<phi> or\<^sub>n \<psi>) = restricted_subformulas \<phi> \<union> restricted_subformulas \<psi>"
| "restricted_subformulas (X\<^sub>n \<phi>) = restricted_subformulas \<phi>"
| "restricted_subformulas (\<phi> U\<^sub>n \<psi>) = restricted_subformulas \<phi> \<union> restricted_subformulas \<psi>"
| "restricted_subformulas (\<phi> R\<^sub>n \<psi>) = restricted_subformulas \<phi> \<union> restricted_subformulas_inner \<psi>"
| "restricted_subformulas (\<phi> W\<^sub>n \<psi>) = restricted_subformulas_inner \<phi> \<union> restricted_subformulas \<psi>"
| "restricted_subformulas (\<phi> M\<^sub>n \<psi>) = restricted_subformulas \<phi> \<union> restricted_subformulas \<psi>"
| "restricted_subformulas _ = {}"

lemma GF_advice_restricted_subformulas_inner:
  "restricted_subformulas_inner (\<phi>[X]\<^sub>\<nu>) = {}"
  by (induction \<phi>) simp_all

lemma GF_advice_restricted_subformulas:
  "restricted_subformulas (\<phi>[X]\<^sub>\<nu>) = {}"
  by (induction \<phi>) (simp_all add: GF_advice_restricted_subformulas_inner)

lemma restricted_subformulas_inner_subset:
  "restricted_subformulas_inner \<phi> \<subseteq> subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<mu> \<phi>"
  by (induction \<phi>) auto

lemma restricted_subformulas_subset':
  "restricted_subformulas \<phi> \<subseteq> restricted_subformulas_inner \<phi>"
  by (induction \<phi>) (insert restricted_subformulas_inner_subset, auto)

lemma restricted_subformulas_subset:
  "restricted_subformulas \<phi> \<subseteq> subformulas\<^sub>\<nu> \<phi> \<union> subformulas\<^sub>\<mu> \<phi>"
  using restricted_subformulas_inner_subset restricted_subformulas_subset' by auto

lemma restricted_subformulas_size:
  "\<psi> \<in> restricted_subformulas \<phi> \<Longrightarrow> size \<psi> < size \<phi>"
proof -
  have "\<And>\<phi>. restricted_subformulas_inner \<phi> \<subseteq> subfrmlsn \<phi>"
    using restricted_subformulas_inner_subset subformulas\<^sub>\<mu>\<^sub>\<nu>_subfrmlsn by blast

  then have inner: "\<And>\<psi> \<phi>. \<psi> \<in> restricted_subformulas_inner \<phi> \<Longrightarrow> size \<psi> \<le> size \<phi>"
    using subfrmlsn_size dual_order.strict_implies_order
    by blast

  show "\<psi> \<in> restricted_subformulas \<phi> \<Longrightarrow> size \<psi> < size \<phi>"
    by (induction \<phi> arbitrary: \<psi>) (fastforce dest: inner)+
qed

lemma restricted_subformulas_notin:
  "\<phi> \<notin> restricted_subformulas \<phi>"
  using restricted_subformulas_size by auto

lemma restricted_subformulas_superset:
  "\<psi> \<in> restricted_subformulas \<phi> \<Longrightarrow> subformulas\<^sub>\<nu> \<psi> \<union> subformulas\<^sub>\<mu> \<psi> \<subseteq> restricted_subformulas \<phi>"
proof -
  assume "\<psi> \<in> restricted_subformulas \<phi>"

  then obtain \<chi> x where
    "\<psi> \<in> restricted_subformulas_inner \<chi>" and "(x R\<^sub>n \<chi>) \<in> subformulas\<^sub>\<nu> \<phi> \<or> (\<chi> W\<^sub>n x) \<in> subformulas\<^sub>\<nu> \<phi> "
    by (induction \<phi>) auto

  moreover

  have "\<And>\<psi>\<^sub>1 \<psi>\<^sub>2. (\<psi>\<^sub>1 R\<^sub>n \<psi>\<^sub>2) \<in> subformulas\<^sub>\<nu> \<phi> \<Longrightarrow> restricted_subformulas_inner \<psi>\<^sub>2 \<subseteq> restricted_subformulas \<phi>"
    "\<And>\<psi>\<^sub>1 \<psi>\<^sub>2. (\<psi>\<^sub>1 W\<^sub>n \<psi>\<^sub>2) \<in> subformulas\<^sub>\<nu> \<phi> \<Longrightarrow> restricted_subformulas_inner \<psi>\<^sub>1 \<subseteq> restricted_subformulas \<phi>"
    by (induction \<phi>) (simp_all; insert restricted_subformulas_subset', blast)+

  moreover

  have "subformulas\<^sub>\<nu> \<psi> \<union> subformulas\<^sub>\<mu> \<psi> \<subseteq>  restricted_subformulas_inner \<chi>"
    using `\<psi> \<in> restricted_subformulas_inner \<chi>`
  proof (induction \<chi>)
    case (Until_ltln \<chi>1 \<chi>2)
    then show ?case
      apply (cases "\<psi> = \<chi>1 U\<^sub>n \<chi>2")
       apply auto[1]
      apply simp
      apply (cases "\<psi> \<in> subformulas\<^sub>\<nu> \<chi>1")
       apply (meson le_supI1 le_supI2 subformulas\<^sub>\<mu>_subset subformulas\<^sub>\<nu>_subfrmlsn subformulas\<^sub>\<nu>_subset subset_eq subset_insertI2)
      apply (cases "\<psi> \<in> subformulas\<^sub>\<nu> \<chi>2")
       apply (meson le_supI1 le_supI2 subformulas\<^sub>\<mu>_subset subformulas\<^sub>\<nu>_subfrmlsn subformulas\<^sub>\<nu>_subset subset_eq subset_insertI2)
      apply (cases "\<psi> \<in> subformulas\<^sub>\<mu> \<chi>1")
       apply (metis (no_types, hide_lams) Un_insert_right subformulas\<^sub>\<mu>_subfrmlsn subformulas\<^sub>\<mu>_subset subformulas\<^sub>\<nu>_subset subsetD sup.coboundedI2 sup_commute)
      apply simp
      by (metis (no_types, hide_lams) Un_insert_right subformulas\<^sub>\<mu>_subfrmlsn subformulas\<^sub>\<mu>_subset subformulas\<^sub>\<nu>_subset subsetD sup.coboundedI2 sup_commute)
  next
    case (Release_ltln \<chi>1 \<chi>2)
    then show ?case by simp blast
  next
    case (WeakUntil_ltln \<chi>1 \<chi>2)
    then show ?case by simp blast
  next
    case (StrongRelease_ltln \<chi>1 \<chi>2)
    then show ?case
      apply (cases "\<psi> = \<chi>1 M\<^sub>n \<chi>2")
       apply auto[1]
      apply simp
      apply (cases "\<psi> \<in> subformulas\<^sub>\<nu> \<chi>1")
       apply (meson le_supI1 le_supI2 subformulas\<^sub>\<mu>_subset subformulas\<^sub>\<nu>_subfrmlsn subformulas\<^sub>\<nu>_subset subset_eq subset_insertI2)
      apply (cases "\<psi> \<in> subformulas\<^sub>\<nu> \<chi>2")
       apply (meson le_supI1 le_supI2 subformulas\<^sub>\<mu>_subset subformulas\<^sub>\<nu>_subfrmlsn subformulas\<^sub>\<nu>_subset subset_eq subset_insertI2)
      apply (cases "\<psi> \<in> subformulas\<^sub>\<mu> \<chi>1")
       apply (metis (no_types, hide_lams) Un_insert_right subformulas\<^sub>\<mu>_subfrmlsn subformulas\<^sub>\<mu>_subset subformulas\<^sub>\<nu>_subset subsetD sup.coboundedI2 sup_commute)
      apply simp
      by (metis (no_types, hide_lams) Un_insert_right subformulas\<^sub>\<mu>_subfrmlsn subformulas\<^sub>\<mu>_subset subformulas\<^sub>\<nu>_subset subsetD sup.coboundedI2 sup_commute)
  qed auto

  ultimately

  show "subformulas\<^sub>\<nu> \<psi> \<union> subformulas\<^sub>\<mu> \<psi> \<subseteq> restricted_subformulas \<phi>"
    by blast
qed

lemma restricted_subformulas_W_\<mu>:
  "subformulas\<^sub>\<mu> \<phi> \<subseteq> restricted_subformulas (\<phi> W\<^sub>n \<psi>)"
  by (induction \<phi>) auto

lemma restricted_subformulas_R_\<mu>:
  "subformulas\<^sub>\<mu> \<psi> \<subseteq> restricted_subformulas (\<phi> R\<^sub>n \<psi>)"
  by (induction \<psi>) auto

lemma restrict_af_letter:
  "restricted_subformulas (af_letter \<phi> \<sigma>) = restricted_subformulas \<phi>"
proof (induction \<phi>)
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
    using restricted_subformulas_subset' by simp blast
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)
  then show ?case
    using restricted_subformulas_subset' by simp blast
qed auto

lemma restrict_af:
  "restricted_subformulas (af \<phi> w) = restricted_subformulas \<phi>"
  by (induction w rule: rev_induct) (auto simp: restrict_af_letter)


subsection \<open>Restricted Master Theorem / Lemmas\<close>

lemma delay_2:
  assumes "\<mu>_stable \<phi> w"
  assumes "w \<Turnstile>\<^sub>n \<phi>"
  shows "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>]\<^sub>\<nu>"
  using assms
proof (induction \<phi> arbitrary: w)
  case (Prop_ltln x)
  then show ?case
    by (metis GF_advice.simps(10) GF_advice_af prefix_suffix)
next
  case (Nprop_ltln x)
  then show ?case
    by (metis GF_advice.simps(11) GF_advice_af prefix_suffix)
next
  case (And_ltln \<phi>1 \<phi>2)

  let ?X  = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas (\<phi>1 and\<^sub>n \<phi>2)"
  let ?X1 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>1"
  let ?X2 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>2"

  have "?X1 \<subseteq> ?X" and "?X2 \<subseteq> ?X"
    by auto

  moreover

  obtain i j where "suffix i w \<Turnstile>\<^sub>n af \<phi>1 (prefix i w)[?X1]\<^sub>\<nu>"
    and "suffix j w \<Turnstile>\<^sub>n af \<phi>2 (prefix j w)[?X2]\<^sub>\<nu>"
    using \<mu>_stable_subfrmlsn[OF \<open>\<mu>_stable (\<phi>1 and\<^sub>n \<phi>2) w\<close>] And_ltln by fastforce

  ultimately

  obtain k where "suffix k w \<Turnstile>\<^sub>n af \<phi>1 (prefix k w)[?X]\<^sub>\<nu>"
    and "suffix k w \<Turnstile>\<^sub>n af \<phi>2 (prefix k w)[?X]\<^sub>\<nu>"
    using GF_advice_sync_and GF_advice_monotone by blast

  thus ?case
    unfolding af_decompose semantics_ltln.simps(5) GF_advice.simps by blast
next
  case (Or_ltln \<phi>1 \<phi>2)
  let ?X  = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas (\<phi>1 and\<^sub>n \<phi>2)"
  let ?X1 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>1"
  let ?X2 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>2"

  have "?X1 \<subseteq> ?X" and "?X2 \<subseteq> ?X"
    by auto

  moreover

  obtain i j where "suffix i w \<Turnstile>\<^sub>n af \<phi>1 (prefix i w)[?X1]\<^sub>\<nu> \<or> suffix j w \<Turnstile>\<^sub>n af \<phi>2 (prefix j w)[?X2]\<^sub>\<nu>"
    using \<mu>_stable_subfrmlsn[OF \<open>\<mu>_stable (\<phi>1 or\<^sub>n \<phi>2) w\<close>] Or_ltln by fastforce

  ultimately

  obtain k where "suffix k w \<Turnstile>\<^sub>n af \<phi>1 (prefix k w)[?X]\<^sub>\<nu> \<or> suffix k w \<Turnstile>\<^sub>n af \<phi>2 (prefix k w)[?X]\<^sub>\<nu>"
    using GF_advice_monotone by blast

  thus ?case
    unfolding af_decompose semantics_ltln.simps(6) GF_advice.simps by auto
next
  case (Next_ltln \<phi>)
  then have stable: "\<mu>_stable \<phi> (suffix 1 w)"
    and suffix: "suffix 1 w \<Turnstile>\<^sub>n \<phi>"
    using \<F>_suffix \<G>\<F>_\<F>_subset \<G>\<F>_suffix
    by (simp_all add: \<mu>_stable_def) fast
  show ?case
    by (metis (no_types, lifting) Next_ltln.IH[OF stable suffix, unfolded suffix_suffix prefix_suffix_subsequence GF_suffix] One_nat_def add.commute af_simps(3) foldl_Nil foldl_append restricted_subformulas.simps(3) subsequence_append subsequence_singleton)
next
  case (Until_ltln \<phi>1 \<phi>2)
  let ?X  = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas (\<phi>1 U\<^sub>n \<phi>2)"
  let ?X1 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>1"
  let ?X2 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>2"

  have stable_1: "\<And>i. \<mu>_stable \<phi>1 (suffix i w)"
    and stable_2: "\<And>i. \<mu>_stable \<phi>2 (suffix i w)"
    using \<mu>_stable_subfrmlsn[OF Until_ltln.prems(1)] by (simp add: \<mu>_stable_suffix)+

  obtain i where "\<And>j. j < i \<Longrightarrow> suffix j w \<Turnstile>\<^sub>n \<phi>1" and "suffix i w \<Turnstile>\<^sub>n \<phi>2"
    using Until_ltln by auto

  then have "\<And>j. j < i \<Longrightarrow> \<exists>k. suffix (j + k) w \<Turnstile>\<^sub>n af \<phi>1 (w [j \<rightarrow> k + j])[?X1]\<^sub>\<nu>"
    and "\<exists>k. suffix (i + k) w \<Turnstile>\<^sub>n af \<phi>2 (w [i \<rightarrow> k + i])[?X2]\<^sub>\<nu>"
    using Until_ltln.IH(1)[OF stable_1, unfolded suffix_suffix prefix_suffix_subsequence GF_suffix]
    using Until_ltln.IH(2)[OF stable_2, unfolded suffix_suffix prefix_suffix_subsequence GF_suffix]
    by blast+

  moreover

  have "?X1 \<subseteq> ?X"
    and "?X2 \<subseteq> ?X"
    by auto

  ultimately

  obtain k where "k \<ge> i"
    and "suffix k w \<Turnstile>\<^sub>n af \<phi>2 (w [i \<rightarrow> k])[?X]\<^sub>\<nu>"
    and "\<And>j. j < i \<Longrightarrow> suffix k w \<Turnstile>\<^sub>n af \<phi>1 (w [j \<rightarrow> k])[?X]\<^sub>\<nu>"
    using GF_advice_sync_less[of i w \<phi>1 ?X \<phi>2] GF_advice_monotone[of _ ?X] by meson

  hence "suffix (Suc k) w \<Turnstile>\<^sub>n af (\<phi>1 U\<^sub>n \<phi>2) (prefix (Suc k) w)[?X]\<^sub>\<nu>"
    by (rule af_subsequence_U_GF_advice)

  then show ?case
    by blast
next
  case (WeakUntil_ltln \<phi>1 \<phi>2)

  let ?X  = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas (\<phi>1 W\<^sub>n \<phi>2)"
  let ?X1 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>1"
  let ?X2 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>2"

  have stable_1: "\<And>i. \<mu>_stable \<phi>1 (suffix i w)"
    and stable_2: "\<And>i. \<mu>_stable \<phi>2 (suffix i w)"
    using \<mu>_stable_subfrmlsn[OF WeakUntil_ltln.prems(1)] by (simp add: \<mu>_stable_suffix)+

  {
    assume Until_ltln: "w \<Turnstile>\<^sub>n \<phi>1 U\<^sub>n \<phi>2"
    then obtain i where "\<And>j. j < i \<Longrightarrow> suffix j w \<Turnstile>\<^sub>n \<phi>1" and "suffix i w \<Turnstile>\<^sub>n \<phi>2"
      by auto

    then have "\<And>j. j < i \<Longrightarrow> \<exists>k. suffix (j + k) w \<Turnstile>\<^sub>n af \<phi>1 (w [j \<rightarrow> k + j])[?X1]\<^sub>\<nu>"
      and "\<exists>k. suffix (i + k) w \<Turnstile>\<^sub>n af \<phi>2 (w [i \<rightarrow> k + i])[?X2]\<^sub>\<nu>"
      using WeakUntil_ltln.IH(1)[OF stable_1, unfolded suffix_suffix prefix_suffix_subsequence GF_suffix]
      using WeakUntil_ltln.IH(2)[OF stable_2, unfolded suffix_suffix prefix_suffix_subsequence GF_suffix]
      by blast+

    moreover

    have "?X1 \<subseteq> ?X"
      and "?X2 \<subseteq> ?X"
      using restricted_subformulas_subset' by force+

    ultimately

    obtain k where "k \<ge> i"
      and "suffix k w \<Turnstile>\<^sub>n af \<phi>2 (w [i \<rightarrow> k])[?X]\<^sub>\<nu>"
      and "\<And>j. j < i \<Longrightarrow> suffix k w \<Turnstile>\<^sub>n af \<phi>1 (w [j \<rightarrow> k])[?X]\<^sub>\<nu>"
      using GF_advice_sync_less[of i w \<phi>1 ?X \<phi>2] GF_advice_monotone[of _ ?X] by meson

    hence "suffix (Suc k) w \<Turnstile>\<^sub>n af (\<phi>1 W\<^sub>n \<phi>2) (prefix (Suc k) w)[?X]\<^sub>\<nu>"
      by (rule af_subsequence_W_GF_advice)
    hence ?case
      by blast
  }
  moreover
  {
    assume Globally_ltln: "w \<Turnstile>\<^sub>n G\<^sub>n \<phi>1"

    {
      fix j
      have "suffix j w \<Turnstile>\<^sub>n \<phi>1"
        using Globally_ltln by simp
      then have "suffix j w \<Turnstile>\<^sub>n \<phi>1[{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)}]\<^sub>\<nu>"
        by (metis stable_1 GF_advice_a1 \<G>\<F>_suffix \<mu>_stable_def \<G>\<F>_elim mem_Collect_eq subsetI)
      then have "suffix j w \<Turnstile>\<^sub>n \<phi>1[?X]\<^sub>\<nu>"
        by (metis GF_advice_inter restricted_subformulas_W_\<mu> le_infI2)
    }

    then have "w \<Turnstile>\<^sub>n (\<phi>1 W\<^sub>n \<phi>2)[?X]\<^sub>\<nu>"
      by simp
    then have ?case
      using GF_advice_af_2 by blast
  }
  ultimately
  show ?case
    using WeakUntil_ltln.prems(2) ltln_weak_to_strong(1) by blast
next
  case (Release_ltln \<phi>1 \<phi>2)

  let ?X  = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas (\<phi>1 R\<^sub>n \<phi>2)"
  let ?X1 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>1"
  let ?X2 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>2"

  have stable_1: "\<And>i. \<mu>_stable \<phi>1 (suffix i w)"
    and stable_2: "\<And>i. \<mu>_stable \<phi>2 (suffix i w)"
    using \<mu>_stable_subfrmlsn[OF Release_ltln.prems(1)] by (simp add: \<mu>_stable_suffix)+

  {
    assume Until_ltln: "w \<Turnstile>\<^sub>n \<phi>1 M\<^sub>n \<phi>2"
    then obtain i where "\<And>j. j \<le> i \<Longrightarrow> suffix j w \<Turnstile>\<^sub>n \<phi>2" and "suffix i w \<Turnstile>\<^sub>n \<phi>1"
      by auto

    then have "\<And>j. j \<le> i \<Longrightarrow> \<exists>k. suffix (j + k) w \<Turnstile>\<^sub>n af \<phi>2 (w [j \<rightarrow> k + j])[?X2]\<^sub>\<nu>"
      and "\<exists>k. suffix (i + k) w \<Turnstile>\<^sub>n af \<phi>1 (w [i \<rightarrow> k + i])[?X1]\<^sub>\<nu>"
      using Release_ltln.IH(1)[OF stable_1, unfolded suffix_suffix prefix_suffix_subsequence GF_suffix]
      using Release_ltln.IH(2)[OF stable_2, unfolded suffix_suffix prefix_suffix_subsequence GF_suffix]
      by blast+

    moreover

    have "?X1 \<subseteq> ?X"
      and "?X2 \<subseteq> ?X"
      using restricted_subformulas_subset' by force+

    ultimately

    obtain k where "k \<ge> i"
      and "suffix k w \<Turnstile>\<^sub>n af \<phi>1 (w [i \<rightarrow> k])[?X]\<^sub>\<nu>"
      and "\<And>j. j \<le> i \<Longrightarrow> suffix k w \<Turnstile>\<^sub>n af \<phi>2 (w [j \<rightarrow> k])[?X]\<^sub>\<nu>"
      using GF_advice_sync_lesseq[of i w \<phi>2 ?X \<phi>1] GF_advice_monotone[of _ ?X] by meson

    hence "suffix (Suc k) w \<Turnstile>\<^sub>n af (\<phi>1 R\<^sub>n \<phi>2) (prefix (Suc k) w)[?X]\<^sub>\<nu>"
      by (rule af_subsequence_R_GF_advice)
    hence ?case
      by blast
  }
  moreover
  {
    assume Globally_ltln: "w \<Turnstile>\<^sub>n G\<^sub>n \<phi>2"

    {
      fix j
      have "suffix j w \<Turnstile>\<^sub>n \<phi>2"
        using Globally_ltln by simp
      then have "suffix j w \<Turnstile>\<^sub>n \<phi>2[{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)}]\<^sub>\<nu>"
        by (metis stable_2 GF_advice_a1 \<G>\<F>_suffix \<mu>_stable_def \<G>\<F>_elim mem_Collect_eq subsetI)
      then have "suffix j w \<Turnstile>\<^sub>n \<phi>2[?X]\<^sub>\<nu>"
        by (metis GF_advice_inter restricted_subformulas_R_\<mu> le_infI2)
    }

    then have "w \<Turnstile>\<^sub>n (\<phi>1 R\<^sub>n \<phi>2)[?X]\<^sub>\<nu>"
      by simp
    then have ?case
      using GF_advice_af_2 by blast
  }
  ultimately
  show ?case
    using Release_ltln.prems(2) ltln_weak_to_strong(3) by blast
next
  case (StrongRelease_ltln \<phi>1 \<phi>2)

  let ?X  = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas (\<phi>1 M\<^sub>n \<phi>2)"
  let ?X1 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>1"
  let ?X2 = "{\<psi>. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>)} \<inter> restricted_subformulas \<phi>2"

  have stable_1: "\<And>i. \<mu>_stable \<phi>1 (suffix i w)"
    and stable_2: "\<And>i. \<mu>_stable \<phi>2 (suffix i w)"
    using \<mu>_stable_subfrmlsn[OF StrongRelease_ltln.prems(1)] by (simp add: \<mu>_stable_suffix)+

  obtain i where "\<And>j. j \<le> i \<Longrightarrow> suffix j w \<Turnstile>\<^sub>n \<phi>2" and "suffix i w \<Turnstile>\<^sub>n \<phi>1"
    using StrongRelease_ltln by auto

  then have "\<And>j. j \<le> i \<Longrightarrow> \<exists>k. suffix (j + k) w \<Turnstile>\<^sub>n af \<phi>2 (w [j \<rightarrow> k + j])[?X2]\<^sub>\<nu>"
    and "\<exists>k. suffix (i + k) w \<Turnstile>\<^sub>n af \<phi>1 (w [i \<rightarrow> k + i])[?X1]\<^sub>\<nu>"
    using StrongRelease_ltln.IH(1)[OF stable_1, unfolded suffix_suffix prefix_suffix_subsequence GF_suffix]
    using StrongRelease_ltln.IH(2)[OF stable_2, unfolded suffix_suffix prefix_suffix_subsequence GF_suffix]
    by blast+

  moreover

  have "?X1 \<subseteq> ?X"
    and "?X2 \<subseteq> ?X"
    by auto

  ultimately

  obtain k where "k \<ge> i"
    and "suffix k w \<Turnstile>\<^sub>n af \<phi>1 (w [i \<rightarrow> k])[?X]\<^sub>\<nu>"
    and "\<And>j. j \<le> i \<Longrightarrow> suffix k w \<Turnstile>\<^sub>n af \<phi>2 (w [j \<rightarrow> k])[?X]\<^sub>\<nu>"
    using GF_advice_sync_lesseq[of i w \<phi>2 ?X \<phi>1] GF_advice_monotone[of _ ?X] by meson

  hence "suffix (Suc k) w \<Turnstile>\<^sub>n af (\<phi>1 M\<^sub>n \<phi>2) (prefix (Suc k) w)[?X]\<^sub>\<nu>"
    by (rule af_subsequence_M_GF_advice)

  then show ?case
    by blast
qed simp+

theorem master_theorem_restricted:
  "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow>
    (\<exists>X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<inter> restricted_subformulas \<phi>.
       (\<exists>Y \<subseteq> subformulas\<^sub>\<nu> \<phi> \<inter> restricted_subformulas \<phi>.
         (\<exists>i. (suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>)
          \<and> (\<forall>\<psi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[Y]\<^sub>\<mu>))
          \<and> (\<forall>\<psi> \<in> Y. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[X]\<^sub>\<nu>)))))"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs

  obtain i where "\<mu>_stable \<phi> (suffix i w)"
   by (metis MOST_nat less_Suc_eq suffix_\<mu>_stable)

  hence stable: "\<mu>_stable (af \<phi> (prefix i w)) (suffix i w)"
    by (simp add: \<F>_af \<G>\<F>_af \<mu>_stable_def)

  let ?\<phi>' = "af \<phi> (prefix i w)"
  let ?X' = "\<G>\<F> \<phi> w \<inter> restricted_subformulas \<phi>"
  let ?Y' = "\<F>\<G> \<phi> w \<inter> restricted_subformulas \<phi>"

  have 1: "suffix i w \<Turnstile>\<^sub>n ?\<phi>'"
    using `?lhs` af_ltl_continuation by force

  have 2: "\<And>j. af (af \<phi> (prefix i w)) (prefix j (suffix i w)) = af \<phi> (prefix (i + j) w)"
    by (simp add: subsequence_append)

  have 3: "\<G>\<F> \<phi> w = \<G>\<F> \<phi> (suffix i w)"
    using \<G>\<F>_af \<G>\<F>_suffix by blast

  have "\<exists>j. suffix (i + j) w \<Turnstile>\<^sub>n af (?\<phi>') (prefix j (suffix i w))[?X']\<^sub>\<nu>"
    using delay_2[OF stable 1] unfolding suffix_suffix 2 restrict_af 3 unfolding \<G>\<F>_semantics'
    by (metis (no_types, lifting) GF_advice_inter_subformulas af_subformulas\<^sub>\<mu> inf_assoc inf_commute)

  hence "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[?X']\<^sub>\<nu>"
    using 2 by auto

  moreover

  {
    fix \<psi>
    have "\<And>X. \<psi> \<in> restricted_subformulas \<phi> \<Longrightarrow> \<psi>[X \<inter> restricted_subformulas \<phi>]\<^sub>\<mu> = \<psi>[X]\<^sub>\<mu>"
      by (metis le_supE restricted_subformulas_superset FG_advice_inter inf.coboundedI2)
    hence "\<psi> \<in> ?X' \<Longrightarrow>  w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[?Y']\<^sub>\<mu>)"
      using \<G>\<F>_implies_GF by force
  }

  moreover

  {
    fix \<psi>
    have "\<And>X. \<psi> \<in> restricted_subformulas \<phi> \<Longrightarrow> \<psi>[X \<inter> restricted_subformulas \<phi>]\<^sub>\<nu> = \<psi>[X]\<^sub>\<nu>"
      by (metis le_supE restricted_subformulas_superset GF_advice_inter inf.coboundedI2)
    hence "\<psi> \<in> ?Y' \<Longrightarrow> w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[?X']\<^sub>\<nu>)"
      using \<F>\<G>_implies_FG by force
  }

  moreover

  have "?X' \<subseteq> subformulas\<^sub>\<mu> \<phi> \<inter> restricted_subformulas \<phi>"
    using \<G>\<F>_subformulas\<^sub>\<mu> by blast

  moreover

  have "?Y' \<subseteq> subformulas\<^sub>\<nu> \<phi> \<inter> restricted_subformulas \<phi>"
    using \<F>\<G>_subformulas\<^sub>\<nu> by blast

  ultimately show ?rhs
    by meson
qed (insert master_theorem, fast)


corollary master_theorem_restricted_language:
  "language_ltln \<phi> = \<Union> {L\<^sub>1 \<phi> X \<inter> L\<^sub>2 X Y \<inter> L\<^sub>3 X Y | X Y. X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<inter> restricted_subformulas \<phi> \<and> Y \<subseteq> subformulas\<^sub>\<nu> \<phi> \<inter> restricted_subformulas \<phi>}"
proof safe
  fix w
  assume "w \<in> language_ltln \<phi>"

  then have "w \<Turnstile>\<^sub>n \<phi>"
    unfolding language_ltln_def by simp

  then obtain X Y where
        1: "X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<inter> restricted_subformulas \<phi>"
    and 2: "Y \<subseteq> subformulas\<^sub>\<nu> \<phi> \<inter> restricted_subformulas \<phi>"
    and "\<exists>i. suffix i w \<Turnstile>\<^sub>n af \<phi> (prefix i w)[X]\<^sub>\<nu>"
    and "\<forall>\<psi> \<in> X. w \<Turnstile>\<^sub>n G\<^sub>n (F\<^sub>n \<psi>[Y]\<^sub>\<mu>)"
    and "\<forall>\<psi> \<in> Y. w \<Turnstile>\<^sub>n F\<^sub>n (G\<^sub>n \<psi>[X]\<^sub>\<nu>)"
    using master_theorem_restricted by metis

  then have "w \<in> L\<^sub>1 \<phi> X" and "w \<in> L\<^sub>2 X Y" and "w \<in> L\<^sub>3 X Y"
    unfolding L\<^sub>1_def L\<^sub>2_def L\<^sub>3_def by simp+

  then show "w \<in> \<Union> {L\<^sub>1 \<phi> X \<inter> L\<^sub>2 X Y \<inter> L\<^sub>3 X Y | X Y. X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<inter> restricted_subformulas \<phi> \<and> Y \<subseteq> subformulas\<^sub>\<nu> \<phi> \<inter> restricted_subformulas \<phi>}"
    using 1 2 by blast
next
  fix w X Y
  assume "X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<inter> restricted_subformulas \<phi>" and "Y \<subseteq> subformulas\<^sub>\<nu> \<phi> \<inter> restricted_subformulas \<phi>"
    and "w \<in> L\<^sub>1 \<phi> X" and "w \<in> L\<^sub>2 X Y" and "w \<in> L\<^sub>3 X Y"

  then show "w \<in> language_ltln \<phi>"
    unfolding language_ltln_def L\<^sub>1_def L\<^sub>2_def L\<^sub>3_def
    using master_theorem_restricted by blast
qed


subsection \<open>Definitions with Lists for Code Export\<close>

definition restricted_advice_sets :: "'a ltln \<Rightarrow> ('a ltln list \<times> 'a ltln list) list"
where
  "restricted_advice_sets \<phi> = List.product (subseqs (List.filter (\<lambda>x. x \<in> restricted_subformulas \<phi>) (subformulas\<^sub>\<mu>_list \<phi>))) (subseqs (List.filter (\<lambda>x. x \<in> restricted_subformulas \<phi>) (subformulas\<^sub>\<nu>_list \<phi>)))"

lemma subseqs_subformulas\<^sub>\<mu>_restricted_list:
  "X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<inter> restricted_subformulas \<phi> \<longleftrightarrow> (\<exists>xs. X = set xs \<and> xs \<in> set (subseqs (List.filter (\<lambda>x. x \<in> restricted_subformulas \<phi>) (subformulas\<^sub>\<mu>_list \<phi>))))"
  by (metis in_set_subseqs inf_commute inter_set_filter subformulas\<^sub>\<mu>_list_set subset_subseq)

lemma subseqs_subformulas\<^sub>\<nu>_restricted_list:
  "Y \<subseteq> subformulas\<^sub>\<nu> \<phi> \<inter> restricted_subformulas \<phi> \<longleftrightarrow> (\<exists>ys. Y = set ys \<and> ys \<in> set (subseqs (List.filter (\<lambda>x. x \<in> restricted_subformulas \<phi>) (subformulas\<^sub>\<nu>_list \<phi>))))"
  by (metis in_set_subseqs inf_commute inter_set_filter subformulas\<^sub>\<nu>_list_set subset_subseq)

lemma restricted_advice_sets_subformulas:
  "X \<subseteq> subformulas\<^sub>\<mu> \<phi> \<inter> restricted_subformulas \<phi> \<and> Y \<subseteq> subformulas\<^sub>\<nu> \<phi> \<inter> restricted_subformulas \<phi> \<longleftrightarrow> (\<exists>xs ys. X = set xs \<and> Y = set ys \<and> (xs, ys) \<in> set (restricted_advice_sets \<phi>))"
  unfolding restricted_advice_sets_def set_product subseqs_subformulas\<^sub>\<mu>_restricted_list subseqs_subformulas\<^sub>\<nu>_restricted_list by blast

lemma restricted_advice_sets_not_empty:
  "restricted_advice_sets \<phi> \<noteq> []"
  unfolding restricted_advice_sets_def using subseqs_not_empty product_not_empty by blast

end
