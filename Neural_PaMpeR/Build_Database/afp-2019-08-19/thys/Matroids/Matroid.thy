(*
  File:     Matroid.thy
  Author:   Jonas Keinholz
*)
section \<open>Matroids\<close>
theory Matroid
  imports Indep_System
begin

lemma card_subset_ex:
  assumes "finite A" "n \<le> card A"
  shows "\<exists>B \<subseteq> A. card B = n"
using assms
proof (induction A arbitrary: n rule: finite_induct)
  case (insert x A)
  show ?case
  proof (cases n)
    case 0
    then show ?thesis using card_empty by blast
  next
    case (Suc k)
    then have "\<exists>B \<subseteq> A. card B = k" using insert by auto
    then obtain B where "B \<subseteq> A" "card B = k" by auto
    moreover from this have "finite B" using insert.hyps finite_subset by auto
    ultimately have "card (insert x B) = n"
      using Suc insert.hyps card_insert_disjoint by fastforce
    then show ?thesis using \<open>B \<subseteq> A\<close> by blast
  qed
qed auto

locale matroid = indep_system +
  assumes augment_aux:
    "indep X \<Longrightarrow> indep Y \<Longrightarrow> card X = Suc (card Y) \<Longrightarrow> \<exists>x \<in> X - Y. indep (insert x Y)"
begin

lemma augment:
  assumes "indep X" "indep Y" "card Y < card X"
  shows "\<exists>x \<in> X - Y. indep (insert x Y)"
proof -
  obtain X' where "X' \<subseteq> X" "card X' = Suc (card Y)"
    using assms card_subset_ex[of X "Suc (card Y)"] indep_finite by auto
  then obtain x where "x \<in> X' - Y"  "indep (insert x Y)"
    using assms augment_aux[of X' Y] indep_subset by auto
  then show ?thesis using \<open>X' \<subseteq> X\<close> by auto
qed

lemma augment_psubset:
  assumes "indep X" "indep Y" "Y \<subset> X"
  shows "\<exists>x \<in> X - Y. indep (insert x Y)"
  using assms augment psubset_card_mono indep_finite by blast

subsection \<open>Minors\<close>

text \<open>
  A subset of the ground set induces a matroid.
\<close>

lemma matroid_subset [simp, intro]:
  assumes "\<E> \<subseteq> carrier"
  shows "matroid \<E> (indep_in \<E>)"
  unfolding matroid_def matroid_axioms_def
proof (safe, goal_cases indep_system augment)
  case indep_system
  then show ?case using indep_system_subset[OF assms] .
next
  case (augment X Y)
  then show ?case using augment_aux[of X Y] unfolding indep_in_def by auto
qed

context
  fixes \<E>
  assumes "\<E> \<subseteq> carrier"
begin

interpretation \<E>: matroid \<E> "indep_in \<E>"
  using \<open>\<E> \<subseteq> carrier\<close> by auto

lemmas augment_aux_indep_in = \<E>.augment_aux
lemmas augment_indep_in = \<E>.augment
lemmas augment_psubset_indep_in = \<E>.augment_psubset

end

subsection \<open>Bases\<close>

lemma basis_card:
  assumes "basis B\<^sub>1"
  assumes "basis B\<^sub>2"
  shows "card B\<^sub>1 = card B\<^sub>2"
proof (rule ccontr, goal_cases False)
  case False
  then have "card B\<^sub>1 < card B\<^sub>2 \<or> card B\<^sub>2 < card B\<^sub>1" by auto
  moreover {
    fix B\<^sub>1 B\<^sub>2
    assume "basis B\<^sub>1" "basis B\<^sub>2" "card B\<^sub>1 < card B\<^sub>2"
    then obtain x where "x \<in> B\<^sub>2 - B\<^sub>1" "indep (insert x B\<^sub>1)"
      using augment basisD by blast
    then have "x \<in> carrier - B\<^sub>1"
      using \<open>basis B\<^sub>1\<close> basisD indep_subset_carrier by blast
    then have "\<not> indep (insert x B\<^sub>1)" using \<open>basis B\<^sub>1\<close> basisD by auto
    then have "False" using \<open>indep (insert x B\<^sub>1)\<close> by auto
  }
  ultimately show ?case using assms by auto
qed

lemma basis_indep_card:
  assumes "indep X"
  assumes "basis B"
  shows "card X \<le> card B"
proof -
  obtain B' where "basis B'" "X \<subseteq> B'" using assms indep_imp_subset_basis by auto
  then show ?thesis using assms basis_finite basis_card[of B B'] by (auto intro: card_mono)
qed

lemma basis_augment:
  assumes "basis B\<^sub>1" "basis B\<^sub>2" "x \<in> B\<^sub>1 - B\<^sub>2"
  shows "\<exists>y \<in> B\<^sub>2 - B\<^sub>1. basis (insert y (B\<^sub>1 - {x}))"
proof -
  let ?B\<^sub>1 = "B\<^sub>1 - {x}"
  have "card ?B\<^sub>1 < card B\<^sub>2"
    using assms basis_card[of B\<^sub>1 B\<^sub>2] card_Diff1_less[OF basis_finite, of B\<^sub>1] by auto
  moreover have "indep ?B\<^sub>1" using assms basis_indep[of B\<^sub>1] indep_subset[of B\<^sub>1 ?B\<^sub>1] by auto
  ultimately obtain y where y: "y \<in> B\<^sub>2 - ?B\<^sub>1" "indep (insert y ?B\<^sub>1)"
    using assms augment[of B\<^sub>2 ?B\<^sub>1] basis_indep by auto
  let ?B\<^sub>1' = "insert y ?B\<^sub>1"
  have "basis ?B\<^sub>1'" using \<open>indep ?B\<^sub>1'\<close>
  proof (rule basisI, goal_cases "insert")
    case (insert x)
    have "card (insert x ?B\<^sub>1') > card B\<^sub>1"
    proof -
      have "card (insert x ?B\<^sub>1') = Suc (card ?B\<^sub>1')"
        using insert card_insert[OF indep_finite, of ?B\<^sub>1'] y by auto
      also have "\<dots> = Suc (Suc (card ?B\<^sub>1))"
        using card_insert[OF indep_finite, of ?B\<^sub>1] \<open>indep ?B\<^sub>1\<close> y by auto
      also have "\<dots> = Suc (card B\<^sub>1)"
        using assms basis_finite[of B\<^sub>1] card.remove[of B\<^sub>1] by auto
      finally show ?thesis by auto
    qed
    then have "\<not>indep (insert x (insert y ?B\<^sub>1))"
      using assms basis_indep_card[of "insert x (insert y ?B\<^sub>1)" B\<^sub>1] by auto
    moreover have "insert x (insert y ?B\<^sub>1) \<subseteq> carrier"
      using assms insert y basis_finite indep_subset_carrier by auto
    ultimately show ?case by auto
  qed
  then show ?thesis using assms y by auto
qed

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: matroid \<E> "indep_in \<E>"
  using \<open>\<E> \<subseteq> carrier\<close> by auto

lemmas basis_in_card = \<E>.basis_card[OF basis_inD_aux[OF *] basis_inD_aux[OF *]]
lemmas basis_in_indep_in_card = \<E>.basis_indep_card[OF _ basis_inD_aux[OF *]]

lemma basis_in_augment:
  assumes "basis_in \<E> B\<^sub>1" "basis_in \<E> B\<^sub>2" "x \<in> B\<^sub>1 - B\<^sub>2"
  shows "\<exists>y \<in> B\<^sub>2 - B\<^sub>1. basis_in \<E> (insert y (B\<^sub>1 - {x}))"
  using assms \<E>.basis_augment unfolding basis_in_def by auto

end

subsection \<open>Circuits\<close>

lemma circuit_elim:
  assumes "circuit C\<^sub>1" "circuit C\<^sub>2" "C\<^sub>1 \<noteq> C\<^sub>2" "x \<in> C\<^sub>1 \<inter> C\<^sub>2"
  shows "\<exists>C\<^sub>3 \<subseteq> (C\<^sub>1 \<union> C\<^sub>2) - {x}. circuit C\<^sub>3"
proof -
  let ?C = "(C\<^sub>1 \<union> C\<^sub>2) - {x}"
  let ?carrier = "C\<^sub>1 \<union> C\<^sub>2"

  have assms': "circuit_in carrier C\<^sub>1" "circuit_in carrier C\<^sub>2"
    using assms circuit_imp_circuit_in by auto

  have "?C \<subseteq> carrier" using assms circuit_subset_carrier by auto
  show ?thesis
  proof (cases "indep ?C")
    case False
    then show ?thesis using dep_iff_supset_circuit \<open>?C \<subseteq> carrier\<close> by auto
  next
    case True
    then have "indep_in ?carrier ?C" using \<open>?C \<subseteq> carrier\<close> by (auto intro: indep_inI)

    have *: "?carrier \<subseteq> carrier" using assms circuit_subset_carrier by auto
    obtain y where y: "y \<in> C\<^sub>2" "y \<notin> C\<^sub>1" using assms circuit_subset_eq by blast
    then have "indep_in ?carrier (C\<^sub>2 - {y})"
      using assms' circuit_in_min_dep_in[OF * circuit_in_supI[OF *, of C\<^sub>2]] by auto
    then obtain B where B: "basis_in ?carrier B" "C\<^sub>2 - {y} \<subseteq> B"
      using * assms indep_in_imp_subset_basis_in[of ?carrier "C\<^sub>2 - {y}"] by auto

    have "y \<notin> B"
    proof (rule ccontr, goal_cases False)
      case False
      then have "C\<^sub>2 \<subseteq> B" using B by auto
      moreover have "circuit_in ?carrier C\<^sub>2" using * assms' circuit_in_supI by auto
      ultimately have "\<not> indep_in ?carrier B"
        using B basis_in_subset_carrier[OF *] supset_circuit_in_imp_dep_in[OF *] by auto
      then show False using assms B basis_in_indep_in[OF *] by auto
    qed

    have "C\<^sub>1 - B \<noteq> {}"
    proof (rule ccontr, goal_cases False)
      case False
      then have "C\<^sub>1 - (C\<^sub>1 \<inter> B) = {}" by auto
      then have "C\<^sub>1 = C\<^sub>1 \<inter> B" using assms circuit_subset_eq by auto
      moreover have "indep (C\<^sub>1 \<inter> B)"
        using assms B basis_in_indep_in[OF *] indep_in_subset[OF *, of B "C\<^sub>1 \<inter> B"] indep_in_indep
        by auto
      ultimately show ?case using assms circuitD by auto
    qed
    then obtain z where z: "z \<in> C\<^sub>1" "z \<notin> B" by auto

    have "y \<noteq> z" using y z by auto
    have "x \<in> C\<^sub>1" "x \<in> C\<^sub>2" using assms by auto

    have "finite ?carrier" using assms carrier_finite finite_subset by auto
    have "card B \<le> card (?carrier - {y, z})"
    proof (rule card_mono)
      show "finite (C\<^sub>1 \<union> C\<^sub>2 - {y, z})" using \<open>finite ?carrier\<close> by auto
    next
      show "B \<subseteq> C\<^sub>1 \<union> C\<^sub>2 - {y, z}"
        using B basis_in_subset_carrier[OF *, of B] \<open>y \<notin> B\<close> \<open>z \<notin> B\<close> by auto
    qed
    also have "\<dots> = card ?carrier - 2"
      using \<open>finite ?carrier\<close> \<open>y \<in> C\<^sub>2\<close> \<open>z \<in> C\<^sub>1\<close> \<open>y \<noteq> z\<close> card_Diff_subset_Int by auto
    also have "\<dots> < card ?carrier - 1"
    proof -
      have "card ?carrier = card C\<^sub>1 + card C\<^sub>2 - card (C\<^sub>1 \<inter> C\<^sub>2)"
        using assms \<open>finite ?carrier\<close> card_Un_Int[of C\<^sub>1 C\<^sub>2] by auto
      also have "\<dots> = card C\<^sub>1 + (card C\<^sub>2 - card (C\<^sub>1 \<inter> C\<^sub>2))"
        using assms \<open>finite ?carrier\<close> card_mono[of C\<^sub>2] by auto
      also have "\<dots> = card C\<^sub>1 + card (C\<^sub>2 - C\<^sub>1)"
      proof -
        have "card (C\<^sub>2 - C\<^sub>1) = card C\<^sub>2 - card (C\<^sub>2 \<inter> C\<^sub>1)"
          using assms \<open>finite ?carrier\<close> card_Diff_subset_Int[of C\<^sub>2 C\<^sub>1] by auto
        also have "\<dots> = card C\<^sub>2 - card (C\<^sub>1 \<inter> C\<^sub>2)" by (simp add: inf_commute)
        finally show ?thesis by auto
      qed
      finally have "card (C\<^sub>1 \<union> C\<^sub>2) = card C\<^sub>1 + card (C\<^sub>2 - C\<^sub>1)" .
      moreover have "card C\<^sub>1 > 0" using assms circuit_nonempty \<open>finite ?carrier\<close> by auto
      moreover have "card (C\<^sub>2 - C\<^sub>1) > 0" using assms \<open>finite ?carrier\<close> \<open>y \<in> C\<^sub>2\<close> \<open>y \<notin> C\<^sub>1\<close> by auto
      ultimately show ?thesis by auto
    qed
    also have "\<dots> = card ?C"
      using \<open>finite ?carrier\<close> card_Diff_singleton \<open>x \<in> C\<^sub>1\<close> \<open>x \<in> C\<^sub>2\<close> by auto
    finally have "card B < card ?C" .
    then have False
      using basis_in_indep_in_card[OF *, of ?C B] B \<open>indep_in ?carrier ?C\<close> by auto
    then show ?thesis by auto
  qed
qed

lemma min_dep_imp_supset_circuit:
  assumes "indep X"
  assumes "circuit C"
  assumes "C \<subseteq> insert x X"
  shows "x \<in> C"
proof (rule ccontr)
  assume "x \<notin> C"
  then have "C \<subseteq> X" using assms by auto
  then have "indep C" using assms indep_subset by auto
  then show False using assms circuitD by auto
qed

lemma min_dep_imp_ex1_supset_circuit:
  assumes "x \<in> carrier"
  assumes "indep X"
  assumes "\<not> indep (insert x X)"
  shows "\<exists>!C. circuit C \<and> C \<subseteq> insert x X"
proof -
  obtain C where C: "circuit C" "C \<subseteq> insert x X"
    using assms indep_subset_carrier dep_iff_supset_circuit by auto

  show ?thesis
  proof (rule ex1I, goal_cases ex unique)
    show "circuit C \<and> C \<subseteq> insert x X" using C by auto
  next
    {
      fix C'
      assume C': "circuit C'" "C' \<subseteq> insert x X"
      have "C' = C"
      proof (rule ccontr)
        assume "C' \<noteq> C"
        moreover have "x \<in> C' \<inter> C" using C C' assms min_dep_imp_supset_circuit by auto
        ultimately have "\<not> indep (C' \<union> C - {x})"
          using circuit_elim[OF C(1) C'(1), of x] supset_circuit_imp_dep[of _ "C' \<union> C - {x}"] by auto
        moreover have "C' \<union> C - {x} \<subseteq> X" using C C' by auto
        ultimately show False using assms indep_subset by auto
      qed
    }
    then show "\<And>C'. circuit C' \<and> C' \<subseteq> insert x X \<Longrightarrow> C' = C"
      by auto
  qed
qed

lemma basis_ex1_supset_circuit:
  assumes "basis B"
  assumes "x \<in> carrier - B"
  shows "\<exists>!C. circuit C \<and> C \<subseteq> insert x B"
  using assms min_dep_imp_ex1_supset_circuit basisD by auto

definition fund_circuit :: "'a \<Rightarrow> 'a set \<Rightarrow> 'a set" where
  "fund_circuit x B \<equiv> (THE C. circuit C \<and> C \<subseteq> insert x B)"

lemma circuit_iff_fund_circuit:
  "circuit C \<longleftrightarrow> (\<exists>x B. x \<in> carrier - B \<and> basis B \<and> C = fund_circuit x B)"
proof (safe, goal_cases LTR RTL)
  case LTR
  then obtain x where "x \<in> C" using circuit_nonempty by auto
  then have "indep (C - {x})" using LTR unfolding circuit_def by auto
  then obtain B where B: "basis B" "C - {x} \<subseteq> B" using indep_imp_subset_basis by auto
  then have "x \<in> carrier" using LTR circuit_subset_carrier \<open>x \<in> C\<close> by auto
  moreover have "x \<notin> B"
  proof (rule ccontr, goal_cases False)
    case False
    then have "C \<subseteq> B" using \<open>C - {x} \<subseteq> B\<close> by auto
    then have "\<not> indep B" using LTR B basis_subset_carrier supset_circuit_imp_dep by auto
    then show ?case using B basis_indep by auto
  qed
  ultimately show ?case
    unfolding fund_circuit_def
    using LTR B theI_unique[OF basis_ex1_supset_circuit[of B x], of C] by auto
next
  case (RTL x B)
  then have "\<exists>!C. circuit C \<and> C \<subseteq> insert x B"
    using min_dep_imp_ex1_supset_circuit basisD[of B] by auto
  then show ?case
    unfolding fund_circuit_def
    using theI[of "\<lambda>C. circuit C \<and> C \<subseteq> insert x B"] by fastforce
qed

lemma fund_circuitI:
  assumes "basis B"
  assumes "x \<in> carrier - B"
  assumes "circuit C"
  assumes "C \<subseteq> insert x B"
  shows "fund_circuit x B = C"
  unfolding fund_circuit_def
  using assms theI_unique[OF basis_ex1_supset_circuit, of B x C] by auto

definition fund_circuit_in where "fund_circuit_in \<E> x B \<equiv> matroid.fund_circuit \<E> (indep_in \<E>) x B"

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: matroid \<E> "indep_in \<E>"
  using \<open>\<E> \<subseteq> carrier\<close> by auto

lemma fund_circuit_inI_aux: "\<E>.fund_circuit x B = fund_circuit_in \<E> x B"
  unfolding fund_circuit_in_def by auto

lemma circuit_in_elim:
  assumes "circuit_in \<E> C\<^sub>1" "circuit_in \<E> C\<^sub>2" "C\<^sub>1 \<noteq> C\<^sub>2" "x \<in> C\<^sub>1 \<inter> C\<^sub>2"
  shows "\<exists>C\<^sub>3 \<subseteq> (C\<^sub>1 \<union> C\<^sub>2) - {x}. circuit_in \<E> C\<^sub>3"
  using assms \<E>.circuit_elim unfolding circuit_in_def by auto

lemmas min_dep_in_imp_supset_circuit_in = \<E>.min_dep_imp_supset_circuit[OF _ circuit_inD_aux[OF *]]

lemma min_dep_in_imp_ex1_supset_circuit_in:
  assumes "x \<in> \<E>"
  assumes "indep_in \<E> X"
  assumes "\<not> indep_in \<E> (insert x X)"
  shows "\<exists>!C. circuit_in \<E> C \<and> C \<subseteq> insert x X"
  using assms \<E>.min_dep_imp_ex1_supset_circuit unfolding circuit_in_def by auto

lemma basis_in_ex1_supset_circuit_in:
  assumes "basis_in \<E> B"
  assumes "x \<in> \<E> - B"
  shows "\<exists>!C. circuit_in \<E> C \<and> C \<subseteq> insert x B"
  using assms \<E>.basis_ex1_supset_circuit unfolding circuit_in_def basis_in_def by auto

lemma fund_circuit_inI:
  assumes "basis_in \<E> B"
  assumes "x \<in> \<E> - B"
  assumes "circuit_in \<E> C"
  assumes "C \<subseteq> insert x B"
  shows "fund_circuit_in \<E> x B = C"
  using assms \<E>.fund_circuitI
  unfolding basis_in_def circuit_in_def fund_circuit_in_def by auto

end

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: matroid \<E> "indep_in \<E>"
  using \<open>\<E> \<subseteq> carrier\<close> by auto

lemma fund_circuit_in_sub_cong:
  assumes "\<E>' \<subseteq> \<E>"
  assumes "x \<in> \<E>' - B"
  assumes "basis_in \<E>' B"
  shows "\<E>.fund_circuit_in \<E>' x B = fund_circuit_in \<E>' x B"
proof -
  obtain C where C: "circuit_in \<E>' C" "C \<subseteq> insert x B"
    using * assms basis_in_ex1_supset_circuit_in[of \<E>' B x] by auto
  then have "fund_circuit_in \<E>' x B = C"
    using * assms fund_circuit_inI by auto
  also have "\<dots> = \<E>.fund_circuit_in \<E>' x B"
    using * assms C \<E>.fund_circuit_inI basis_in_sub_cong[of \<E>] circuit_in_sub_cong[of \<E>] by auto
  finally show ?thesis by auto
qed

end

subsection \<open>Ranks\<close>

abbreviation rank_of where "rank_of \<equiv> lower_rank_of"

lemmas rank_of_def = lower_rank_of_def
lemmas rank_of_sub_cong = lower_rank_of_sub_cong
lemmas rank_of_le = lower_rank_of_le

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: matroid \<E> "indep_in \<E>"
  using * by auto

lemma lower_rank_of_eq_upper_rank_of: "lower_rank_of \<E> = upper_rank_of \<E>"
proof -
  obtain B where "basis_in \<E> B" using basis_in_ex[OF *] by auto
  then have "{card B | B. basis_in \<E> B} = {card B}"
    by safe (auto dest: basis_in_card[OF *])
  then show ?thesis unfolding lower_rank_of_def upper_rank_of_def by auto
qed

lemma rank_of_eq_card_basis_in:
  assumes "basis_in \<E> B"
  shows "rank_of \<E> = card B"
proof -
  have "{card B | B. basis_in \<E> B} = {card B}" using assms by safe (auto dest: basis_in_card[OF *])
  then show ?thesis unfolding rank_of_def by auto
qed

lemma rank_of_indep_in_le:
  assumes "indep_in \<E> X"
  shows "card X \<le> rank_of \<E>"
proof -
  {
    fix B
    assume "basis_in \<E> B"
    moreover obtain B' where "basis_in \<E> B'" "X \<subseteq> B'"
      using assms indep_in_imp_subset_basis_in[OF *] by auto
    ultimately have "card X \<le> card B"
      using card_mono[OF basis_in_finite[OF *]] basis_in_card[OF *, of B B'] by auto
  }
  moreover have "finite {card B | B. basis_in \<E> B}"
    using collect_basis_in_finite[OF *] by auto
  ultimately show ?thesis
    unfolding rank_of_def using basis_in_ex[OF *] by auto
qed

end

lemma rank_of_mono:
  assumes "X \<subseteq> Y"
  assumes "Y \<subseteq> carrier"
  shows "rank_of X \<le> rank_of Y"
proof -
  obtain B\<^sub>X where B\<^sub>X: "basis_in X  B\<^sub>X" using assms basis_in_ex[of X] by auto
  moreover obtain B\<^sub>Y where B\<^sub>Y: "basis_in Y B\<^sub>Y" using assms basis_in_ex[of Y] by auto
  moreover have "card B\<^sub>X \<le> card B\<^sub>Y"
    using assms basis_in_indep_in_card[OF _ _ B\<^sub>Y] basis_in_indep_in[OF _ B\<^sub>X] indep_in_subI_subset
    by auto
  ultimately show ?thesis using assms rank_of_eq_card_basis_in by auto
qed

lemma rank_of_insert_le:
  assumes "X \<subseteq> carrier"
  assumes "x \<in> carrier"
  shows "rank_of (insert x X) \<le> Suc (rank_of X)"
proof -
  obtain B where B: "basis_in X B" using assms basis_in_ex[of X] by auto
  have "basis_in (insert x X) B \<or> basis_in (insert x X) (insert x B)"
  proof -
    obtain B' where B': "B' \<subseteq> insert x X - X" "basis_in (insert x X) (B \<union> B')"
      using assms B basis_in_subI[of "insert x X" X B] by auto
    then have "B' = {} \<or> B' = {x}" by auto
    then show ?thesis
    proof
      assume "B' = {}"
      then have "basis_in (insert x X) B" using B' by auto
      then show ?thesis by auto
    next
      assume "B' = {x}"
      then have "basis_in (insert x X) (insert x B)" using B' by auto
      then show ?thesis by auto
    qed
  qed
  then show ?thesis
  proof
    assume "basis_in (insert x X) B"
    then show ?thesis
      using assms B rank_of_eq_card_basis_in by auto
  next
    assume "basis_in (insert x X) (insert x B)"
    then have "rank_of (insert x X) = card (insert x B)"
      using assms rank_of_eq_card_basis_in by auto
    also have "\<dots> = Suc (card (B - {x}))"
      using assms card_insert[of B x] using B basis_in_finite by auto
    also have "\<dots> \<le> Suc (card B)"
      using assms B basis_in_finite card_Diff1_le[of B] by auto
    also have "\<dots> = Suc (rank_of X)"
      using assms B rank_of_eq_card_basis_in by auto
    finally show ?thesis .
  qed
qed

lemma rank_of_Un_Int_le:
  assumes "X \<subseteq> carrier"
  assumes "Y \<subseteq> carrier"
  shows "rank_of (X \<union> Y) + rank_of (X \<inter> Y) \<le> rank_of X + rank_of Y"
proof -
  obtain B_Int where B_Int: "basis_in (X \<inter> Y) B_Int" using assms basis_in_ex[of "X \<inter> Y"] by auto
  then have "indep_in (X \<union> Y) B_Int"
    using assms indep_in_subI_subset[OF _ basis_in_indep_in[of "X \<inter> Y" B_Int], of "X \<union> Y"] by auto
  then obtain B_Un where B_Un: "basis_in (X \<union> Y) B_Un" "B_Int \<subseteq> B_Un"
    using assms indep_in_imp_subset_basis_in[of "X \<union> Y" B_Int] by auto

  have "card (B_Un \<inter> (X \<union> Y)) + card (B_Un \<inter> (X \<inter> Y)) = card ((B_Un \<inter> X) \<union> (B_Un \<inter> Y)) + card ((B_Un \<inter> X) \<inter> (B_Un \<inter> Y))"
    by (simp add: inf_assoc inf_left_commute inf_sup_distrib1)
  also have "\<dots> = card (B_Un \<inter> X) + card (B_Un \<inter> Y)"
  proof -
    have "finite (B_Un \<inter> X)" "finite (B_Un \<inter> Y)"
      using assms finite_subset[OF _ carrier_finite] by auto
    then show ?thesis using card_Un_Int[of "B_Un \<inter> X" "B_Un \<inter> Y"] by auto
  qed
  also have "\<dots> \<le> rank_of X + rank_of Y"
  proof -
    have "card (B_Un \<inter> X) \<le> rank_of X"
    proof -
      have "indep_in X (B_Un \<inter> X)" using assms basis_in_indep_in[OF _ B_Un(1)] indep_in_subI by auto
      then show ?thesis using assms rank_of_indep_in_le by auto
    qed
    moreover have "card (B_Un \<inter> Y) \<le> rank_of Y"
    proof -
      have "indep_in Y (B_Un \<inter> Y)" using assms basis_in_indep_in[OF _ B_Un(1)] indep_in_subI by auto
      then show ?thesis using assms rank_of_indep_in_le by auto
    qed
    ultimately show ?thesis by auto
  qed
  finally have "rank_of X + rank_of Y \<ge> card (B_Un \<inter> (X \<union> Y)) + card (B_Un \<inter> (X \<inter> Y))" .
  moreover have "B_Un \<inter> (X \<union> Y) = B_Un" using assms basis_in_subset_carrier[OF _ B_Un(1)] by auto
  moreover have "B_Un \<inter> (X \<inter> Y) = B_Int"
  proof -
    have "card (B_Un \<inter> (X \<inter> Y)) \<le> card B_Int"
    proof -
      have "indep_in (X \<inter> Y) (B_Un \<inter> (X \<inter> Y))"
        using assms basis_in_indep_in[OF _ B_Un(1)] indep_in_subI by auto
      then show ?thesis using assms basis_in_indep_in_card[of "X \<inter> Y" _ B_Int] B_Int by auto
    qed
    moreover have "finite (B_Un \<inter> (X \<inter> Y))"
      using assms carrier_finite finite_subset[of "B_Un \<inter> (X \<inter> Y)"] by auto
    moreover have "B_Int \<subseteq> B_Un \<inter> (X \<inter> Y)"
      using assms B_Un B_Int basis_in_subset_carrier[of "X \<inter> Y" B_Int] by auto
    ultimately show ?thesis using card_seteq by blast
  qed
  ultimately have "rank_of X + rank_of Y \<ge> card B_Un + card B_Int" by auto
  moreover have "card B_Un = rank_of (X \<union> Y)"
    using assms rank_of_eq_card_basis_in[OF _ B_Un(1)] by auto
  moreover have "card B_Int = rank_of (X \<inter> Y)"
    using assms rank_of_eq_card_basis_in[OF _ B_Int] by fastforce
  ultimately show "rank_of X + rank_of Y \<ge> rank_of (X \<union> Y) + rank_of (X \<inter> Y)" by auto
qed

lemma rank_of_Un_absorbI:
  assumes "X \<subseteq> carrier" "Y \<subseteq> carrier"
  assumes "\<And>y. y \<in> Y - X \<Longrightarrow> rank_of (insert y X) = rank_of X"
  shows "rank_of (X \<union> Y) = rank_of X"
proof -
  have "finite (Y - X)" using finite_subset[OF \<open>Y \<subseteq> carrier\<close>] carrier_finite by auto
  then show ?thesis using assms
  proof (induction "Y - X" arbitrary: Y rule: finite_induct )
    case empty
    then have "X \<union> Y = X" by auto
    then show ?case by auto
  next
    case (insert y F)
    have "rank_of (X \<union> Y) + rank_of X \<le> rank_of X + rank_of X"
    proof -
      have "rank_of (X \<union> Y) + rank_of X = rank_of ((X \<union> (Y - {y})) \<union> (insert y X)) + rank_of ((X \<union> (Y - {y})) \<inter> (insert y X))"
      proof -
        have "X \<union> Y = (X \<union> (Y - {y})) \<union> (insert y X)" "X = (X \<union> (Y - {y})) \<inter> (insert y X)" using insert by auto
        then show ?thesis by auto
      qed
      also have "\<dots> \<le> rank_of (X \<union> (Y - {y})) +  rank_of (insert y X)"
      proof (rule rank_of_Un_Int_le)
        show "X \<union> (Y - {y}) \<subseteq> carrier" using insert by auto
      next
        show "insert y X \<subseteq> carrier" using insert by auto
      qed
      also have "\<dots> = rank_of (X \<union> (Y - {y})) + rank_of X"
      proof -
        have "y \<in> Y - X" using insert by auto
        then show ?thesis using insert by auto
      qed
      also have "\<dots> = rank_of X + rank_of X"
      proof -
        have "F = (Y - {y}) - X" "Y - {y} \<subseteq> carrier" using insert by auto
        then show ?thesis using insert insert(3)[of "Y - {y}"] by auto
      qed
      finally show ?thesis .
    qed
    moreover have "rank_of (X \<union> Y) + rank_of X \<ge> rank_of X + rank_of X"
      using insert rank_of_mono by auto
    ultimately show ?case by auto
  qed
qed

lemma indep_iff_rank_of:
  assumes "X \<subseteq> carrier"
  shows "indep X \<longleftrightarrow> rank_of X = card X"
proof (standard, goal_cases LTR RTL)
  case LTR
  then have "indep_in X X" by (auto intro: indep_inI)
  then have "basis_in X X" by (auto intro: basis_inI[OF assms])
  then show ?case using rank_of_eq_card_basis_in[OF assms] by auto
next
  case RTL
  obtain B where B: "basis_in X B" using basis_in_ex[OF assms] by auto
  then have "card B = card X" using RTL rank_of_eq_card_basis_in[OF assms] by auto
  then have "B = X"
    using basis_in_subset_carrier[OF assms B] card_seteq[OF finite_subset[OF assms carrier_finite]]
    by auto
  then show ?case using basis_in_indep_in[OF assms B] indep_in_indep by auto
qed

lemma basis_iff_rank_of:
  assumes "X \<subseteq> carrier"
  shows "basis X \<longleftrightarrow> rank_of X = card X \<and> rank_of X = rank_of carrier"
proof (standard, goal_cases LTR RTL)
  case LTR
  then have "rank_of X = card X" using assms indep_iff_rank_of basis_indep by auto
  moreover have "\<dots> = rank_of carrier"
    using LTR rank_of_eq_card_basis_in[of carrier X] basis_iff_basis_in by auto
  ultimately show ?case by auto
next
  case RTL
  show ?case
  proof (rule basisI)
    show "indep X" using assms RTL indep_iff_rank_of by blast
  next
    fix x
    assume x: "x \<in> carrier - X"
    show "\<not> indep (insert x X)"
    proof (rule ccontr, goal_cases False)
      case False
      then have "card (insert x X) \<le> rank_of carrier"
        using assms x indep_inI rank_of_indep_in_le by auto
      also have "\<dots> = card X" using RTL by auto
      finally show ?case using finite_subset[OF assms carrier_finite] x by auto
    qed
  qed
qed

lemma circuit_iff_rank_of:
  assumes "X \<subseteq> carrier"
  shows "circuit X \<longleftrightarrow> X \<noteq> {} \<and> (\<forall>x \<in> X. rank_of (X - {x}) = card (X - {x}) \<and> card (X - {x}) = rank_of X)"
proof (standard, goal_cases LTR RTL)
  case LTR
  then have "X \<noteq> {}" using circuit_nonempty by auto
  moreover have indep_remove: "\<And>x. x \<in> X \<Longrightarrow> rank_of (X - {x}) = card (X - {x})"
  proof -
    fix x
    assume "x \<in> X"
    then have "indep (X - {x})" using circuit_min_dep[OF LTR] by auto
    moreover have "X - {x} \<subseteq> carrier" using assms by auto
    ultimately show "rank_of (X - {x}) = card (X - {x})" using indep_iff_rank_of by auto
  qed
  moreover have "\<And>x. x \<in> X \<Longrightarrow> rank_of (X - {x}) = rank_of X"
  proof -
    fix x
    assume *: "x \<in> X"
    have "rank_of X \<le> card X" using assms rank_of_le by auto
    moreover have "rank_of X \<noteq> card X" using assms LTR circuitD indep_iff_rank_of[of X] by auto
    ultimately have "rank_of X < card X" by auto
    then have "rank_of X \<le> card (X - {x})" using * finite_subset[OF assms] carrier_finite by auto
    also have "\<dots> = rank_of (X - {x})" using indep_remove \<open>x \<in> X\<close> by auto
    finally show "rank_of (X - {x}) = rank_of X" using assms rank_of_mono[of "X - {x}" X] by auto
  qed
  ultimately show ?case by auto
next
  case RTL
  then have "X \<noteq> {}"
    and indep_remove: "\<And>x. x \<in> X \<Longrightarrow> rank_of (X - {x}) = card (X - {x})"
    and dep: "\<And>x. x \<in> X \<Longrightarrow> rank_of (X - {x}) = rank_of X"
    by auto
  show ?case using assms
  proof (rule circuitI)
    obtain x where x: "x \<in> X" using \<open>X \<noteq> {}\<close> by auto
    then have "rank_of X = card (X - {x})" using dep indep_remove by auto
    also have "\<dots> < card X" using card_Diff1_less[OF finite_subset[OF assms carrier_finite] x] .
    finally show "\<not> indep X" using indep_iff_rank_of[OF assms] by auto
  next
    fix x
    assume "x \<in> X"
    then show "indep (X - {x})" using assms indep_remove[of x] indep_iff_rank_of[of "X - {x}"]
      by auto
  qed
qed

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: matroid \<E> "indep_in \<E>"
  using * by auto

lemma indep_in_iff_rank_of:
  assumes "X \<subseteq> \<E>"
  shows "indep_in \<E> X \<longleftrightarrow> rank_of X = card X"
  using assms \<E>.indep_iff_rank_of rank_of_sub_cong[OF * assms] by auto

lemma basis_in_iff_rank_of:
  assumes "X \<subseteq> \<E>"
  shows "basis_in \<E> X \<longleftrightarrow> rank_of X = card X \<and> rank_of X = rank_of \<E>"
  using \<E>.basis_iff_rank_of[OF assms] rank_of_sub_cong[OF *] assms
  unfolding basis_in_def by auto

lemma circuit_in_iff_rank_of:
  assumes "X \<subseteq> \<E>"
  shows "circuit_in \<E> X \<longleftrightarrow> X \<noteq> {} \<and> (\<forall>x \<in> X. rank_of (X - {x}) = card (X - {x}) \<and> card (X - {x}) = rank_of X)"
proof -
  have "circuit_in \<E> X \<longleftrightarrow> \<E>.circuit X" unfolding circuit_in_def ..
  also have "\<dots> \<longleftrightarrow>  X \<noteq> {} \<and> (\<forall>x \<in> X. \<E>.rank_of (X - {x}) = card (X - {x}) \<and> card (X - {x}) = \<E>.rank_of X)"
    using \<E>.circuit_iff_rank_of[OF assms] .
  also have "\<dots> \<longleftrightarrow> X \<noteq> {} \<and> (\<forall>x \<in> X. rank_of (X - {x}) = card (X - {x}) \<and> card (X - {x}) = rank_of X)"
  proof -
    {
      fix x
      have "\<E>.rank_of (X - {x}) = rank_of (X - {x})" "\<E>.rank_of X = rank_of X"
        using assms rank_of_sub_cong[OF *, of "X - {x}"] rank_of_sub_cong[OF *, of X] by auto
      then have "\<E>.rank_of (X - {x}) = card (X - {x}) \<and> card (X - {x}) = \<E>.rank_of X \<longleftrightarrow> rank_of (X - {x}) = card (X - {x}) \<and> card (X - {x}) = rank_of X"
        by auto
    }
    then show ?thesis by auto
  qed
  finally show ?thesis .
qed

end

subsection \<open>Closure\<close>

definition cl :: "'a set \<Rightarrow> 'a set" where
  "cl X \<equiv> {x \<in> carrier. rank_of (insert x X) = rank_of X}"

lemma clI:
  assumes "x \<in> carrier"
  assumes "rank_of (insert x X) = rank_of X"
  shows "x \<in> cl X"
  unfolding cl_def using assms by auto

lemma cl_altdef:
  assumes "X \<subseteq> carrier"
  shows "cl X = \<Union>{Y \<in> Pow carrier. X \<subseteq> Y \<and> rank_of Y = rank_of X}"
proof -
  {
    fix x
    assume *: "x \<in> cl X"
    have "x \<in> \<Union>{Y \<in> Pow carrier. X \<subseteq> Y \<and> rank_of Y = rank_of X}"
    proof
      show "insert x X \<in> {Y \<in> Pow carrier. X \<subseteq> Y \<and> rank_of Y = rank_of X}"
        using assms * unfolding cl_def by auto
    qed auto
  }
  moreover {
    fix x
    assume *: "x \<in> \<Union>{Y \<in> Pow carrier. X \<subseteq> Y \<and> rank_of Y = rank_of X}"
    then obtain Y where Y: "x \<in> Y" "Y \<subseteq> carrier" "X \<subseteq> Y" "rank_of Y = rank_of X" by auto
    have "rank_of (insert x X) = rank_of X"
    proof -
      have "rank_of (insert x X) \<le> rank_of X"
      proof -
        have "insert x X \<subseteq> Y" using Y by auto
        then show ?thesis using rank_of_mono[of "insert x X" Y] Y by auto
      qed
      moreover have "rank_of X \<le> rank_of (insert x X)" using Y by (auto intro: rank_of_mono)
      ultimately show ?thesis by auto
    qed
    then have "x \<in> cl X" using * unfolding cl_def by auto
  }
  ultimately show ?thesis by blast
qed


lemma cl_rank_of: "x \<in> cl X \<Longrightarrow> rank_of (insert x X) = rank_of X"
  unfolding cl_def by auto

lemma cl_subset_carrier: "cl X \<subseteq> carrier"
  unfolding cl_def by auto

lemmas clD = cl_rank_of cl_subset_carrier

lemma cl_subset:
  assumes "X \<subseteq> carrier"
  shows "X \<subseteq> cl X"
  using assms using insert_absorb[of _ X] by (auto intro!: clI)

lemma cl_mono:
  assumes "X \<subseteq> Y"
  assumes "Y \<subseteq> carrier"
  shows "cl X \<subseteq> cl Y"
proof
  fix x
  assume "x \<in> cl X"
  then have "x \<in> carrier" using cl_subset_carrier by auto

  have "insert x X \<subseteq> carrier"
    using assms \<open>x \<in> cl X\<close> cl_subset_carrier[of X] by auto
  then interpret X_insert: matroid "insert x X" "indep_in (insert x X)" by auto

  have "insert x Y \<subseteq> carrier"
    using assms \<open>x \<in> cl X\<close> cl_subset_carrier[of X] by auto
  then interpret Y_insert: matroid "insert x Y" "indep_in (insert x Y)" by auto

  show "x \<in> cl Y" using \<open>x \<in> carrier\<close>
  proof (rule clI, cases "x \<in> X")
    case True
    then show "rank_of (insert x Y) = rank_of Y" using assms insert_absorb[of x Y] by auto
  next
    case False
    obtain B\<^sub>X where B\<^sub>X: "basis_in X B\<^sub>X" using assms basis_in_ex[of X] by auto

    have "basis_in (insert x X) B\<^sub>X"
    proof -
      have "rank_of B\<^sub>X = card B\<^sub>X \<and> rank_of B\<^sub>X = rank_of (insert x X)"
      proof -
        have "rank_of B\<^sub>X = card B\<^sub>X \<and> rank_of B\<^sub>X = rank_of X"
          using assms B\<^sub>X
            basis_in_subset_carrier[where \<E> = X and X = B\<^sub>X]
            basis_in_iff_rank_of[where \<E> = X and X = B\<^sub>X]
          by blast
        then show ?thesis using cl_rank_of[OF \<open>x \<in> cl X\<close>] by auto
      qed
      then show ?thesis
        using assms basis_in_subset_carrier[OF _ B\<^sub>X] \<open>x \<in> carrier\<close> basis_in_iff_rank_of[of "insert x X" B\<^sub>X]
        by auto
    qed

    have "indep_in (insert x Y) B\<^sub>X"
      using assms basis_in_indep_in[OF _ B\<^sub>X] indep_in_subI_subset[of X "insert x Y"] by auto
    then obtain B\<^sub>Y where B\<^sub>Y: "basis_in (insert x Y) B\<^sub>Y" "B\<^sub>X \<subseteq> B\<^sub>Y"
      using assms \<open>x \<in> carrier\<close> indep_in_iff_subset_basis_in[of "insert x Y" B\<^sub>X] by auto

    have "basis_in Y B\<^sub>Y"
    proof -
      have "x \<notin> B\<^sub>Y"
      proof (rule ccontr, goal_cases False)
        case False
        then have "insert x B\<^sub>X \<subseteq> B\<^sub>Y" using \<open>B\<^sub>X \<subseteq> B\<^sub>Y\<close> by auto
        then have "indep_in (insert x Y) (insert x B\<^sub>X)"
          using assms \<open>x \<in> carrier\<close>
            B\<^sub>Y basis_in_indep_in[where \<E> = "insert x Y" and X = B\<^sub>Y]
            indep_in_subset[where \<E> = "insert x Y" and X = B\<^sub>Y and Y = "insert x B\<^sub>X"]
          by auto
        then have "indep_in (insert x X) (insert x B\<^sub>X)"
          using assms B\<^sub>X
            basis_in_subset_carrier[where \<E> = X and X = B\<^sub>X]
            indep_in_supI[where \<E> = "insert x Y" and \<E>' = "insert x X" and X = "insert x B\<^sub>X"]
          by auto
        moreover have "x \<in> insert x X - B\<^sub>X"
          using assms \<open>x \<notin> X\<close> B\<^sub>X basis_in_subset_carrier[where \<E> = X and X = B\<^sub>X] by auto
        ultimately show ?case
          using assms \<open>x \<in> carrier\<close> \<open>basis_in (insert x X) B\<^sub>X\<close>
            basis_in_max_indep_in[where \<E> = "insert x X" and X = B\<^sub>X and x = x]
          by auto
      qed
      then show ?thesis
      using assms \<open>x \<in> carrier\<close> B\<^sub>Y basis_in_subset_carrier[of "insert x Y" B\<^sub>Y]
        basis_in_supI[where \<E> = "insert x Y" and \<E>' = Y and B = B\<^sub>Y] by auto
    qed

    show "rank_of (insert x Y) = rank_of Y"
    proof -
      have "rank_of (insert x Y) = card B\<^sub>Y"
        using assms \<open>x \<in> carrier\<close> \<open>basis_in (insert x Y) B\<^sub>Y\<close> basis_in_subset_carrier
        using basis_in_iff_rank_of[where \<E> = "insert x Y" and X = B\<^sub>Y]
        by auto
      also have "\<dots> = rank_of Y"
        using assms \<open>x \<in> carrier\<close> \<open>basis_in Y B\<^sub>Y\<close> basis_in_subset_carrier
        using basis_in_iff_rank_of[where \<E> = Y and X = B\<^sub>Y]
        by auto
      finally show ?thesis .
    qed
  qed
qed

lemma cl_insert_absorb:
  assumes "X \<subseteq> carrier"
  assumes "x \<in> cl X"
  shows "cl (insert x X) = cl X"
proof
  show "cl (insert x X) \<subseteq> cl X"
  proof (standard, goal_cases elem)
    case (elem y)
    then have *: "x \<in> carrier" "y \<in> carrier" using assms cl_subset_carrier by auto

    have "rank_of (insert y X) = rank_of (insert y (insert x X))"
    proof -
      have "rank_of (insert y X) \<le> rank_of (insert y (insert x X))"
        using assms * by (auto intro: rank_of_mono)
      moreover have "rank_of (insert y (insert x X)) = rank_of (insert y X)"
      proof -
        have "insert y (insert x X) = insert x (insert y X)" by auto
        then have "rank_of (insert y (insert x X)) = rank_of (insert x (insert y X))" by auto
        also have "\<dots> = rank_of (insert y X)"
        proof -
          have "cl X \<subseteq> cl (insert y X)" by (rule cl_mono) (auto simp add: assms \<open>y \<in> carrier\<close>)
          then have "x \<in> cl (insert y X)" using assms by auto
          then show ?thesis unfolding cl_def by auto
        qed
        finally show ?thesis .
      qed
      ultimately show ?thesis by auto
    qed
    also have "\<dots> = rank_of (insert x X)" using elem using cl_rank_of by auto
    also have "\<dots> = rank_of X" using assms cl_rank_of by auto
    finally show "y \<in> cl X" using * by (auto intro: clI)
  qed
next
  have "insert x X \<subseteq> carrier" using assms cl_subset_carrier by auto
  moreover have "X \<subseteq> insert x X" using assms by auto
  ultimately show "cl X \<subseteq> cl (insert x X)" using assms cl_subset_carrier cl_mono by auto
qed

lemma cl_cl_absorb:
  assumes "X \<subseteq> carrier"
  shows "cl (cl X) = cl X"
proof
  show "cl (cl X) \<subseteq> cl X"
  proof (standard, goal_cases elem)
    case (elem x)
    then have "x \<in> carrier" using cl_subset_carrier by auto
    then show ?case
    proof (rule clI)
      have "rank_of (insert x X) \<ge> rank_of X"
        using assms \<open>x \<in> carrier\<close> rank_of_mono[of X "insert x X"] by auto
      moreover have "rank_of (insert x X) \<le> rank_of X"
      proof -
        have "rank_of (insert x X) \<le> rank_of (insert x (cl X))"
          using assms \<open>x \<in> carrier\<close> cl_subset_carrier cl_subset[of X]
                rank_of_mono[of "insert x X" "insert x (cl X)"] by auto
        also have "\<dots> = rank_of (cl X)" using elem cl_rank_of by auto
        also have "\<dots> = rank_of (X \<union> (cl X - X))"
          using Diff_partition[OF cl_subset[OF assms]] by auto
        also have "\<dots> = rank_of X" using \<open>X \<subseteq> carrier\<close>
        proof (rule rank_of_Un_absorbI)
          show "cl X - X \<subseteq> carrier" using assms cl_subset_carrier by auto
        next
          fix y
          assume "y \<in> cl X - X - X"
          then show "rank_of (insert y X) = rank_of X" unfolding cl_def by auto
        qed
        finally show ?thesis .
      qed
      ultimately show "rank_of (insert x X) = rank_of X" by auto
    qed
  qed
next
  show "cl X \<subseteq> cl (cl X)" using cl_subset[OF cl_subset_carrier] by auto
qed

lemma cl_augment:
  assumes "X \<subseteq> carrier"
  assumes "x \<in> carrier"
  assumes "y \<in> cl (insert x X) - cl X"
  shows "x \<in> cl (insert y X)"
  using \<open>x \<in> carrier\<close>
proof (rule clI)
  have "rank_of (insert y X) \<le> rank_of (insert x (insert y X))"
    using assms cl_subset_carrier by (auto intro: rank_of_mono)
  moreover have "rank_of (insert x (insert y X)) \<le> rank_of (insert y X)"
  proof -
    have "rank_of (insert x (insert y X)) = rank_of (insert y (insert x X))"
    proof -
      have "insert x (insert y X) = insert y (insert x X)" by auto
      then show ?thesis by auto
    qed
    also have "rank_of (insert y (insert x X)) = rank_of (insert x X)"
      using assms cl_def by auto
    also have "\<dots> \<le> Suc (rank_of X)"
      using assms cl_subset_carrier by (auto intro: rank_of_insert_le)
    also have "\<dots> = rank_of (insert y X)"
    proof -
      have "rank_of (insert y X) \<le> Suc (rank_of X)"
        using assms cl_subset_carrier by (auto intro: rank_of_insert_le)
      moreover have "rank_of (insert y X) \<noteq> rank_of X"
        using assms cl_def by auto
      moreover have "rank_of X \<le> rank_of (insert y X)"
        using assms cl_subset_carrier by (auto intro: rank_of_mono)
      ultimately show ?thesis by auto
    qed
    finally show ?thesis .
  qed
  ultimately show "rank_of (insert x (insert y X)) = rank_of (insert y X)" by auto
qed

lemma clI_insert:
  assumes "x \<in> carrier"
  assumes "indep X"
  assumes "\<not> indep (insert x X)"
  shows "x \<in> cl X"
  using \<open>x \<in> carrier\<close>
proof (rule clI)
  have *: "X \<subseteq> carrier" using assms indep_subset_carrier by auto
  then have **: "insert x X \<subseteq> carrier" using assms by auto

  have "indep_in (insert x X) X" using assms by (auto intro: indep_inI)
  then obtain B where B: "basis_in (insert x X) B" "X \<subseteq> B"
    using assms indep_in_iff_subset_basis_in[OF **] by auto
  have "x \<notin> B"
  proof (rule ccontr, goal_cases False)
    case False
    then have "indep_in (insert x X) (insert x X)"
      using B indep_in_subset[OF ** basis_in_indep_in[OF **]] by auto
    then show ?case using assms indep_in_indep by auto
  qed

  have "basis_in X B" using *
  proof (rule basis_inI, goal_cases indep max_indep)
    case indep
    show ?case
    proof (rule indep_in_supI[where \<E> = "insert x X"])
      show "B \<subseteq> X" using B basis_in_subset_carrier[OF **] \<open>x \<notin> B\<close> by auto
    next
      show "indep_in (insert x X) B" using basis_in_indep_in[OF ** B(1)] .
    qed auto
  next
    case (max_indep y)
    then have "\<not> indep_in (insert x X) (insert y B)"
      using B basis_in_max_indep_in[OF **] by auto
    then show ?case by (auto intro: indep_in_subI_subset)
  qed
  then show "rank_of (insert x X) = rank_of X"
    using B rank_of_eq_card_basis_in[OF *] rank_of_eq_card_basis_in[OF **] by auto
qed

lemma indep_in_carrier [simp]: "indep_in carrier = indep"
  using indep_subset_carrier by (auto simp: indep_in_def fun_eq_iff)

context
  fixes I
  defines "I \<equiv> (\<lambda>X. X \<subseteq> carrier \<and> (\<forall>x\<in>X. x \<notin> cl (X - {x})))"
begin

lemma I_mono: "I Y" if "Y \<subseteq> X" "I X" for X Y :: "'a set"
proof -
  have "\<forall>x\<in>Y. x \<notin> cl (Y - {x})"
  proof (intro ballI)
    fix x assume x: "x \<in> Y"
    with that have "cl (Y - {x}) \<subseteq> cl (X - {x})"
      by (intro cl_mono) (auto simp: I_def)
    with that and x show "x \<notin> cl (Y - {x})" by (auto simp: I_def)
  qed
  with that show ?thesis by (auto simp: I_def)
qed

lemma clI':
  assumes "I X" "x \<in> carrier" "\<not>I (insert x X)"
  shows   "x \<in> cl X"
proof -
  from assms have x: "x \<notin> X" by (auto simp: insert_absorb)
  from assms obtain y where y: "y \<in> insert x X" "y \<in> cl (insert x X - {y})"
    by (force simp: I_def)
  show "x \<in> cl X"
  proof (cases "x = y")
    case True
    thus ?thesis using assms x y by (auto simp: I_def)
  next
    case False
    have "y \<in> cl (insert x X - {y})" by fact
    also from False have "insert x X - {y} = insert x (X - {y})" by auto
    finally have "y \<in> cl (insert x (X - {y})) - cl (X - {y})"
      using assms False y unfolding I_def by blast
    hence "x \<in> cl (insert y (X - {y}))"
      using cl_augment[of "X - {y}" x y] assms False y by (auto simp: I_def)
    also from y and False have "insert y (X - {y}) = X" by auto
    finally show ?thesis .
  qed
qed


lemma matroid_I: "matroid carrier I"
proof (unfold_locales, goal_cases)
  show "finite carrier" by (rule carrier_finite)
next
  case (4 X Y)
  have "\<forall>x\<in>Y. x \<notin> cl (Y - {x})"
  proof (intro ballI)
    fix x assume x: "x \<in> Y"
    with 4 have "cl (Y - {x}) \<subseteq> cl (X - {x})"
      by (intro cl_mono) (auto simp: I_def)
    with 4 and x show "x \<notin> cl (Y - {x})" by (auto simp: I_def)
  qed
  with 4 show ?case by (auto simp: I_def)
next
  case (5 X Y)
  have "~(\<exists>X Y. I X \<and> I Y \<and> card X < card Y \<and> (\<forall>x\<in>Y-X. \<not>I (insert x X)))"
  proof
    assume *: "\<exists>X Y. I X \<and> I Y \<and> card X < card Y \<and> (\<forall>x\<in>Y-X. \<not>I (insert x X))" (is "\<exists>X Y. ?P X Y")
    define n where "n = Max ((\<lambda>(X, Y). card (X \<inter> Y)) ` {(X, Y). ?P X Y})"
    have "{(X, Y). ?P X Y} \<subseteq> Pow carrier \<times> Pow carrier"
      by (auto simp: I_def)
    hence finite: "finite {(X, Y). ?P X Y}"
      by (rule finite_subset) (insert carrier_finite, auto)
    hence "n \<in> ((\<lambda>(X, Y). card (X \<inter> Y)) ` {(X, Y). ?P X Y})"
      unfolding n_def using * by (intro Max_in finite_imageI) auto
    then obtain X Y where XY: "?P X Y" "n = card (X \<inter> Y)"
      by auto
    hence finite': "finite X" "finite Y"
      using finite_subset[OF _ carrier_finite] XY by (auto simp: I_def)
    from XY finite' have "~(Y \<subseteq> X)"
      using card_mono[of X Y] by auto
    then obtain y where y: "y \<in> Y - X" by blast

    have False
    proof (cases "X \<subseteq> cl (Y - {y})")
      case True
      from y XY have [simp]: "y \<in> carrier" by (auto simp: I_def)
      assume "X \<subseteq> cl (Y - {y})"
      hence "cl X \<subseteq> cl (cl (Y - {y}))"
        by (intro cl_mono cl_subset_carrier)
      also have "\<dots> = cl (Y - {y})"
        using XY by (intro cl_cl_absorb) (auto simp: I_def)
      finally have "cl X \<subseteq> cl (Y - {y})" .
      moreover have "y \<notin> cl (Y - {y})"
        using y I_def XY(1) by blast
      ultimately have "y \<notin> cl X" by blast
      thus False unfolding I_def
        using XY y clI' \<open>y \<in> carrier\<close> by blast
    next
      case False
      with y XY have [simp]: "y \<in> carrier" by (auto simp: I_def)
      assume "\<not>(X \<subseteq> cl (Y - {y}))"
      then obtain t where t: "t \<in> X" "t \<notin> cl (Y - {y})"
        by auto
      with XY have [simp]: "t \<in> carrier" by (auto simp: I_def)

      have "t \<in> X - Y"
        using t y clI[of t "Y - {y}"] by (cases "t = y") (auto simp: insert_absorb)
      moreover have "I  (Y - {y})" using XY(1) I_mono[of "Y - {y}" Y] by blast
      ultimately have *: "I (insert t (Y - {y}))"
        using clI'[of "Y - {y}" t] t by auto

      from XY have "finite Y"
        by (intro finite_subset[OF _ carrier_finite]) (auto simp: I_def)
      moreover from y have "Y \<noteq> {}" by auto
      ultimately have [simp]: "card (insert t (Y - {y})) = card Y" using \<open>t \<in> X - Y\<close> y
        by (simp add: Suc_diff_Suc card_gt_0_iff)

      have "\<exists>x\<in>Y - X. I (insert x X)"
      proof (rule ccontr)
        assume "\<not>?thesis"
        hence "?P X (insert t (Y - {y}))" using XY * \<open>t \<in> X - Y\<close>
          by auto
        hence "card (X \<inter> insert t (Y - {y})) \<le> n"
          unfolding n_def using finite by (intro Max_ge) auto
        also have "X \<inter> insert t (Y - {y}) = insert t ((X \<inter> Y) - {y})"
          using y \<open>t \<in> X - Y\<close> by blast
        also have "card \<dots> = Suc (card (X \<inter> Y))"
          using y \<open>t \<in> X - Y\<close> \<open>finite Y\<close> by (simp add: card_insert)
        finally show False using XY by simp
      qed
      with XY show False by blast
    qed
    thus False .
  qed
  with 5 show ?case by auto
qed (auto simp: I_def)

end

definition cl_in where "cl_in \<E> X = matroid.cl \<E> (indep_in \<E>) X"

lemma cl_eq_cl_in:
  assumes "X \<subseteq> carrier"
  shows "cl X = cl_in carrier X"
proof -
  interpret \<E>: matroid carrier "indep_in carrier"
    by (intro matroid_subset) auto
  have "cl X = {x \<in> carrier. rank_of (insert x X) = rank_of X}"
    unfolding cl_def by auto
  also have "\<dots> = {x \<in> carrier. \<E>.rank_of (insert x X) = \<E>.rank_of X}"
    using rank_of_sub_cong[of carrier] assms by auto
  also have "\<dots> = cl_in carrier X"
    unfolding cl_in_def \<E>.cl_def by auto
  finally show ?thesis .
qed

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: matroid \<E> "indep_in \<E>"
  using * by auto

lemma cl_inI_aux: "x \<in> \<E>.cl X \<Longrightarrow> x \<in> cl_in \<E> X"
  unfolding cl_in_def by auto

lemma cl_inD_aux: "x \<in> cl_in \<E> X \<Longrightarrow> x \<in> \<E>.cl X"
  unfolding cl_in_def by auto

lemma cl_inI:
  assumes "X \<subseteq> \<E>"
  assumes "x \<in> \<E>"
  assumes "rank_of (insert x X) = rank_of X"
  shows "x \<in> cl_in \<E> X"
proof -
  have "\<E>.rank_of (insert x X) = rank_of (insert x X)" "\<E>.rank_of X = rank_of X"
    using assms rank_of_sub_cong[OF *] by auto
  then show ?thesis unfolding cl_in_def using assms by (auto intro: \<E>.clI)
qed

lemma cl_in_altdef:
  assumes "X \<subseteq> \<E>"
  shows "cl_in \<E> X = \<Union>{Y \<in> Pow \<E>. X \<subseteq> Y \<and> rank_of Y = rank_of X}"
  unfolding cl_in_def
proof (safe, goal_cases LTR RTL)
  case (LTR x)
  then have "x \<in> \<Union>{Y \<in> Pow \<E>. X \<subseteq> Y \<and> \<E>.rank_of Y = \<E>.rank_of X}"
    using \<E>.cl_altdef[OF assms] by auto
  then obtain Y where Y: "x \<in> Y" "Y \<in> Pow \<E>" "X \<subseteq> Y" "\<E>.rank_of Y = \<E>.rank_of X" by auto
  then show ?case using rank_of_sub_cong[OF *] by auto
next
  case (RTL x Y)
  then have "x \<in> \<Union>{Y \<in> Pow \<E>. X \<subseteq> Y \<and> \<E>.rank_of Y = \<E>.rank_of X}"
     using rank_of_sub_cong[OF *, of X] rank_of_sub_cong[OF *, of Y] by auto
  then show ?case using \<E>.cl_altdef[OF assms] by auto
qed

lemma cl_in_subset_carrier: "cl_in \<E> X \<subseteq> \<E>"
  using \<E>.cl_subset_carrier unfolding cl_in_def .

lemma cl_in_rank_of:
  assumes "X \<subseteq> \<E>"
  assumes "x \<in> cl_in \<E> X"
  shows "rank_of (insert x X) = rank_of X"
proof -
  have "\<E>.rank_of (insert x X) = \<E>.rank_of X"
    using assms \<E>.cl_rank_of unfolding cl_in_def by auto
  moreover have "\<E>.rank_of (insert x X) = rank_of (insert x X)"
    using assms rank_of_sub_cong[OF *, of "insert x X"] cl_in_subset_carrier by auto
  moreover have "\<E>.rank_of X = rank_of X"
    using assms rank_of_sub_cong[OF *] by auto
  ultimately show ?thesis by auto
qed

lemmas cl_inD = cl_in_rank_of cl_in_subset_carrier

lemma cl_in_subset:
  assumes "X \<subseteq> \<E>"
  shows "X \<subseteq> cl_in \<E> X"
  using \<E>.cl_subset[OF assms] unfolding cl_in_def .

lemma cl_in_mono:
  assumes "X \<subseteq> Y"
  assumes "Y \<subseteq> \<E>"
  shows "cl_in \<E> X \<subseteq> cl_in \<E> Y"
  using \<E>.cl_mono[OF assms] unfolding cl_in_def .

lemma cl_in_insert_absorb:
  assumes "X \<subseteq> \<E>"
  assumes "x \<in> cl_in \<E> X"
  shows "cl_in \<E> (insert x X) = cl_in \<E> X"
  using assms \<E>.cl_insert_absorb unfolding cl_in_def by auto

lemma cl_in_augment:
  assumes "X \<subseteq> \<E>"
  assumes "x \<in> \<E>"
  assumes "y \<in> cl_in \<E> (insert x X) - cl_in \<E> X"
  shows "x \<in> cl_in \<E> (insert y X)"
  using assms \<E>.cl_augment unfolding cl_in_def by auto

lemmas cl_inI_insert = cl_inI_aux[OF \<E>.clI_insert]

end

lemma cl_in_subI:
  assumes "X \<subseteq> \<E>'" "\<E>' \<subseteq> \<E>" "\<E> \<subseteq> carrier"
  shows "cl_in \<E>' X \<subseteq> cl_in \<E> X"
proof (safe, goal_cases elem)
  case (elem x)
  then have "x \<in> \<E>'" "rank_of (insert x X) = rank_of X"
    using assms cl_inD[where \<E> = \<E>' and X = X] by auto
  then show "x \<in> cl_in \<E> X" using assms by (auto intro: cl_inI)
qed

context
  fixes \<E>
  assumes *: "\<E> \<subseteq> carrier"
begin

interpretation \<E>: matroid \<E> "indep_in \<E>"
  using * by auto

lemma cl_in_sub_cong:
  assumes "X \<subseteq> \<E>'" "\<E>' \<subseteq> \<E>"
  shows "\<E>.cl_in \<E>' X = cl_in \<E>' X"
proof (safe, goal_cases LTR RTL)
  case (LTR x)
  then have "x \<in> \<E>'" "\<E>.rank_of (insert x X) = \<E>.rank_of X"
    using assms
      \<E>.cl_in_rank_of[where \<E> = \<E>' and X = X and x = x]
      \<E>.cl_in_subset_carrier[where \<E> = \<E>']
    by auto
  moreover have "\<E>.rank_of X = rank_of X"
    using assms rank_of_sub_cong[OF *] by auto
  moreover have "\<E>.rank_of (insert x X) = rank_of (insert x X)"
    using assms rank_of_sub_cong[OF *, of "insert x X"] \<open>x \<in> \<E>'\<close> by auto
  ultimately show ?case using assms * by (auto intro: cl_inI)
next
  case (RTL x)
  then have "x \<in> \<E>'" "rank_of (insert x X) = rank_of X"
    using * assms cl_inD[where \<E> = \<E>' and X = X] by auto
  moreover have "\<E>.rank_of X = rank_of X"
    using assms rank_of_sub_cong[OF *] by auto
  moreover have "\<E>.rank_of (insert x X) = rank_of (insert x X)"
    using assms rank_of_sub_cong[OF *, of "insert x X"] \<open>x \<in> \<E>'\<close> by auto
  ultimately show ?case using assms by (auto intro: \<E>.cl_inI)
qed

end
end
end