(* ---------------------------------------------------------------------------- *)
subsection \<open>Library Aditions for Set Cardinality\<close>
(* ---------------------------------------------------------------------------- *)

text \<open>In this sections some additional simple lemmas about set cardinality are proved.\<close>

theory More_Set
imports Main
begin

text \<open>Every infinite set has at least two different elements\<close>
lemma infinite_contains_2_elems:
  assumes "infinite A"
  shows "\<exists> x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A"
proof(rule ccontr)
  assume *: " \<nexists>x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A"
  have "\<exists> x. x \<in> A "
    using assms
    by (simp add: ex_in_conv infinite_imp_nonempty)
  hence "card A = 1"
    using *
    by (metis assms ex_in_conv finite_insert infinite_imp_nonempty insertCI mk_disjoint_insert)
  thus False
    using assms
    by simp
qed

text \<open>Every infinite set has at least three different elements\<close>
lemma infinite_contains_3_elems:
  assumes "infinite A"
  shows "\<exists> x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A"
proof(rule ccontr)
  assume " \<nexists>x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A"
  hence "card A = 2"
    by (smt DiffE assms finite_insert infinite_contains_2_elems insert_Diff insert_iff)
  thus False
    using assms
    by simp
qed

text \<open>Every set with cardinality greater than 1 has at least two different elements\<close>
lemma card_geq_2_iff_contains_2_elems:
  shows "card A \<ge> 2 \<longleftrightarrow> finite A \<and> (\<exists> x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A)"
proof
  assume *: "finite A \<and> (\<exists> x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A)"
  thus "card A \<ge> 2"
  proof -
    obtain a :: 'a and b :: 'a where
      f1: "a \<noteq> b \<and> a \<in> A \<and> b \<in> A"
      using *
      by blast
    then have "0 < card (A - {b})"
      by (metis * card_eq_0_iff ex_in_conv finite_insert insertE insert_Diff neq0_conv)
    then show ?thesis
      using f1 by (simp add: *)
  qed
next
  assume *: " 2 \<le> card A"
  hence "finite A"
    using card_infinite
    by force
  moreover
  have "\<exists>x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A"
  proof(rule ccontr)
    assume " \<nexists>x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A"
    hence "card A \<le> 1"
      by (metis One_nat_def card.empty card.insert card_mono finite.emptyI finite_insert insertCI le_SucI subsetI)
    thus False
      using *
      by auto
  qed
  ultimately
  show "finite A \<and> (\<exists> x y. x \<noteq> y \<and> x \<in> A \<and> y \<in> A)"
    by simp
qed

text \<open>Set cardinality is at least 3 if and only if it contains three different elements\<close>
lemma card_geq_3_iff_contains_3_elems:
  shows "card A \<ge> 3 \<longleftrightarrow> finite A \<and> (\<exists> x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A)"
proof
  assume *: "card A \<ge> 3"
  hence "finite A"
    using card_infinite
    by force
  moreover
  have "\<exists> x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A"
  proof(rule ccontr)
    assume "\<nexists>x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A"
    hence "card A \<le> 2"
      by (smt DiffE Suc_leI card.remove card_geq_2_iff_contains_2_elems insert_iff le_cases not_le)
    thus False
      using *
      by auto
  qed
  ultimately
  show "finite A \<and> (\<exists> x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A)"
    by simp
next
  assume *: "finite A \<and> (\<exists> x y z. x \<noteq> y \<and> x \<noteq> z \<and> y \<noteq> z \<and> x \<in> A \<and> y \<in> A \<and> z \<in> A)"
  thus "card A \<ge> 3"
    by (smt "*" Suc_eq_numeral Suc_le_mono card.remove card_geq_2_iff_contains_2_elems finite_insert insert_Diff insert_iff pred_numeral_simps(3))
qed

text \<open>Set cardinality of A is equal to 2 if and only if A={x, y} for two different elements x and y\<close>
lemma card_eq_2_iff_doubleton: "card A = 2 \<longleftrightarrow> (\<exists> x y. x \<noteq> y \<and> A = {x, y})"
  using card_geq_2_iff_contains_2_elems[of A]
  using card_geq_3_iff_contains_3_elems[of A]
  by auto (rule_tac x=x in exI, rule_tac x=y in exI, auto)

lemma card_eq_2_doubleton:
  assumes "card A = 2" and "x \<noteq> y" and "x \<in> A" and "y \<in> A"
  shows "A = {x, y}"
  using assms
  using card_eq_2_iff_doubleton[of A]
  by auto

text \<open>Bijections map singleton to singleton sets\<close>

lemma bij_image_singleton:
  shows "\<lbrakk>f ` A = {b}; f a = b; bij f\<rbrakk> \<Longrightarrow> A = {a}"
  by (metis (mono_tags) bij_betw_imp_inj_on image_empty image_insert inj_vimage_image_eq)

end