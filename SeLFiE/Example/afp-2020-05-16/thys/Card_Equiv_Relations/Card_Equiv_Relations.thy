(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Cardinality of Equivalence Relations\<close>

theory Card_Equiv_Relations
imports
  Card_Partitions.Card_Partitions
  Bell_Numbers_Spivey.Bell_Numbers
begin

subsection \<open>Bijection between Equivalence Relations and Set Partitions\<close>

subsubsection \<open>Possibly Interesting Theorem for @{theory HOL.Equiv_Relations}\<close>

text \<open>This theorem was historically useful in this theory, but
is now after some proof refactoring not needed here anymore.
Possibly it is an interesting fact about equivalence relations, though.
\<close>

lemma equiv_quotient_eq_quotient_on_UNIV:
  assumes "equiv A R"
  shows "A // R = (UNIV // R) - {{}}"
proof
  show "UNIV // R - {{}} \<subseteq> A // R"
  proof
    fix X
    assume "X \<in> UNIV // R - {{}}"
    from this obtain x where "X = R `` {x}" and "X \<noteq> {}"
      by (auto elim!: quotientE)
    from this have "x \<in> A"
      using \<open>equiv A R\<close> equiv_class_eq_iff by fastforce
    from this \<open>X = R `` {x}\<close> show "X \<in> A // R"
      by (auto intro!: quotientI)
  qed
next
  show "A // R \<subseteq> UNIV // R - {{}}"
  proof
    fix X
    assume "X \<in> A // R"
    from this have "X \<noteq> {}"
      using \<open>equiv A R\<close> in_quotient_imp_non_empty by auto
    moreover from \<open>X \<in> A // R\<close> have "X \<in> UNIV // R"
      by (metis UNIV_I assms proj_Eps proj_preserves)
    ultimately show "X \<in> UNIV // R - {{}}" by simp
  qed
qed

subsubsection \<open>Dedicated Facts for Bijection Proof\<close>

(* TODO: rename to fit Disjoint_Sets' naming scheme and move to Disjoint_Sets *)
lemma equiv_relation_of_partition_of:
  assumes "equiv A R"
  shows "{(x, y). \<exists>X\<in>A // R. x \<in> X \<and> y \<in> X} = R"
proof
  show "{(x, y). \<exists>X\<in>A // R. x \<in> X \<and> y \<in> X} \<subseteq> R"
  proof
    fix xy
    assume "xy \<in> {(x, y). \<exists>X\<in>A // R. x \<in> X \<and> y \<in> X}"
    from this obtain x y and X where "xy = (x, y)"
      and "X \<in> A // R" and "x \<in> X" "y \<in> X"
      by auto
    from \<open>X \<in> A // R\<close> obtain z where "X = R `` {z}"
      by (auto elim: quotientE)
    show "xy \<in> R"
      using \<open>xy = (x, y)\<close> \<open>X = R `` {z}\<close> \<open>x \<in> X\<close> \<open>y \<in> X\<close> \<open>equiv A R\<close>
      by (simp add: equiv_class_eq_iff)
  qed
next
  show "R \<subseteq> {(x, y). \<exists>X\<in>A // R. x \<in> X \<and> y \<in> X}"
  proof
    fix xy
    assume "xy \<in> R"
    obtain x y where "xy = (x, y)" by fastforce
    from \<open>xy \<in> R\<close> have "(x, y) \<in> R"
      using \<open>xy = (x, y)\<close> by simp
    have "R `` {x} \<in> A // R"
      using \<open>equiv A R\<close> \<open>(x, y) \<in> R\<close>
      by (simp add: equiv_class_eq_iff quotientI)
    moreover have "x \<in> R `` {x}"
      using \<open>(x, y) \<in> R\<close> \<open>equiv A R\<close>
      by (meson equiv_class_eq_iff equiv_class_self)
    moreover have "y \<in> R `` {x}"
      using \<open>(x, y) \<in> R\<close> \<open>equiv A R\<close> by simp
    ultimately have "(x, y) \<in> {(x, y). \<exists>X\<in>A // R. x \<in> X \<and> y \<in> X}"
      by auto
    from this show "xy \<in> {(x, y). \<exists>X\<in>A // R. x \<in> X \<and> y \<in> X}"
      using \<open>xy = (x, y)\<close> by simp
  qed
qed

subsubsection \<open>Bijection Proof\<close>

lemma bij_betw_partition_of:
  "bij_betw (\<lambda>R. A // R) {R. equiv A R} {P. partition_on A P}"
proof (rule bij_betw_byWitness[where f'="\<lambda>P. {(x, y). \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"])
  show "\<forall>R\<in>{R. equiv A R}. {(x, y). \<exists>X\<in>A // R. x \<in> X \<and> y \<in> X} = R"
    by (simp add: equiv_relation_of_partition_of)
  show "\<forall>P\<in>{P. partition_on A P}. A // {(x, y). \<exists>X\<in>P. x \<in> X \<and> y \<in> X} = P"
    by (simp add: partition_on_eq_quotient)
  show "(\<lambda>R. A // R) ` {R. equiv A R} \<subseteq> {P. partition_on A P}"
    using partition_on_quotient by auto
  show "(\<lambda>P. {(x, y). \<exists>X\<in>P. x \<in> X \<and> y \<in> X}) ` {P. partition_on A P} \<subseteq> {R. equiv A R}"
    using equiv_partition_on by auto
qed

lemma bij_betw_partition_of_equiv_with_k_classes:
  "bij_betw (\<lambda>R. A // R) {R. equiv A R \<and> card (A // R) = k} {P. partition_on A P \<and> card P = k}"
proof (rule bij_betw_byWitness[where f'="\<lambda>P. {(x, y). \<exists>X\<in>P. x \<in> X \<and> y \<in> X}"])
  show "\<forall>R\<in>{R. equiv A R \<and> card (A // R) = k}. {(x, y). \<exists>X\<in>A // R. x \<in> X \<and> y \<in> X} = R"
    by (auto simp add: equiv_relation_of_partition_of)
  show "\<forall>P\<in>{P. partition_on A P \<and> card P = k}. A // {(x, y). \<exists>X\<in>P. x \<in> X \<and> y \<in> X} = P"
    by (auto simp add: partition_on_eq_quotient)
  show "(\<lambda>R. A // R) ` {R. equiv A R \<and> card (A // R) = k} \<subseteq> {P. partition_on A P \<and> card P = k}"
    using partition_on_quotient by auto
  show "(\<lambda>P. {(x, y). \<exists>X\<in>P. x \<in> X \<and> y \<in> X}) ` {P. partition_on A P \<and> card P = k} \<subseteq> {R. equiv A R \<and> card (A // R) = k}"
    using equiv_partition_on by (auto simp add: partition_on_eq_quotient)
qed

subsection \<open>Finiteness of Equivalence Relations\<close>

lemma finite_equiv:
  assumes "finite A"
  shows "finite {R. equiv A R}"
proof -
  have "bij_betw (\<lambda>R. A // R) {R. equiv A R} {P. partition_on A P}"
    by (rule bij_betw_partition_of)
  from this show "finite {R. equiv A R}"
    using \<open>finite A\<close> finitely_many_partition_on by (simp add: bij_betw_finite)
qed

subsection \<open>Cardinality of Equivalence Relations\<close>

theorem card_equiv_rel_eq_card_partitions:
  "card {R. equiv A R} = card {P. partition_on A P}"
proof -
  have "bij_betw (\<lambda>R. A // R) {R. equiv A R} {P. partition_on A P}"
    by (rule bij_betw_partition_of)
  from this show "card {R. equiv A R} = card {P. partition_on A P}"
    by (rule bij_betw_same_card)
qed

corollary card_equiv_rel_eq_Bell:
  assumes "finite A"
  shows "card {R. equiv A R} = Bell (card A)"
using assms Bell_altdef card_equiv_rel_eq_card_partitions by force

corollary card_equiv_rel_eq_sum_Stirling:
  assumes "finite A"
  shows "card {R. equiv A R} = sum (Stirling (card A)) {..card A}"
using assms card_equiv_rel_eq_Bell Bell_Stirling_eq by simp

theorem card_equiv_k_classes_eq_card_partitions_k_parts:
  "card {R. equiv A R \<and> card (A // R) = k} = card {P. partition_on A P \<and> card P = k}"
proof -
  have "bij_betw (\<lambda>R. A // R) {R. equiv A R \<and> card (A // R) = k} {P. partition_on A P \<and> card P = k}"
    by (rule bij_betw_partition_of_equiv_with_k_classes)
  from this show "card {R. equiv A R \<and> card (A // R) = k} = card {P. partition_on A P \<and> card P = k}"
    by (rule bij_betw_same_card)
qed

corollary
  assumes "finite A"
  shows "card {R. equiv A R \<and> card (A // R) = k} = Stirling (card A) k"
using card_equiv_k_classes_eq_card_partitions_k_parts
  card_partition_on[OF \<open>finite A\<close>] by metis

end
