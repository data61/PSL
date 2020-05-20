(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Injections from A to B\<close>

theory Twelvefold_Way_Entry2
imports Twelvefold_Way_Entry1
begin

text \<open>
Note that the cardinality theorems of both structures, distinct lists
and finite injective functions, are already available. Hence, this
development creates the bijection between those two structures and
transfers the one cardinality theorem to the other structures and vice
versa, although not strictly needed as both cardinality theorems were
already available.
\<close>

subsection \<open>Properties for Bijections\<close>

lemma inj_on_implies_distinct:
  assumes "bij_betw enum {0..<card A} A"
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  assumes "inj_on f A"
  shows "distinct (sequence_of A enum f)"
proof -
  {
    fix i j
    assume bounds: "i < length (sequence_of A enum f)" "j < length (sequence_of A enum f)"
    assume "i \<noteq> j"
    from bounds assms(1, 2) have bounds': "i < card A" "j < card A"
      using length_sequence_of by fastforce+
    from this assms(1) have in_A: "enum i \<in> A" "enum j \<in> A"
      using bij_betwE by fastforce+
    from \<open>i \<noteq> j\<close>  bounds' assms(1) have "enum i \<noteq> enum j"
      by (metis bij_betw_inv_into_left lessThan_iff atLeast0LessThan)
    from this have "f (enum i) \<noteq> f (enum j)"
      using assms(3) in_A inj_onD by fastforce
    from this bounds' have "sequence_of A enum f ! i \<noteq> sequence_of A enum f ! j"
      by (simp add: nth_sequence_of)
  }
  from this show ?thesis
    by (auto simp add: distinct_conv_nth)
qed

lemma distinct_implies_inj_on:
  assumes "bij_betw enum {0..<card A} A"
  assumes "length xs = card A"
  assumes "distinct xs"
  shows "inj_on (function_of A enum xs) A"
proof (rule inj_onI)
  let ?idx_of = "\<lambda>x. inv_into {0..<length xs} enum x"
  fix x y
  assume "x \<in> A" "y \<in> A" "function_of A enum xs x = function_of A enum xs y"
  from this have "xs ! ?idx_of x = xs ! ?idx_of y"
    unfolding function_of_def by simp
  have "?idx_of x = ?idx_of y"
  proof -
    have "?idx_of x < length xs"
      using \<open>x \<in> A\<close> assms(1,2)
      by (metis atLeast0LessThan bij_betw_imp_surj_on inv_into_into lessThan_iff)
    moreover have "?idx_of y < length xs"
      using \<open>y \<in> A\<close> assms(1,2)
      by (metis atLeast0LessThan bij_betw_imp_surj_on inv_into_into lessThan_iff)
    moreover note \<open>xs ! ?idx_of x = xs ! ?idx_of y\<close> \<open>distinct xs\<close>
    ultimately show ?thesis
      by (auto dest: nth_eq_iff_index_eq[where i="?idx_of x" and j="?idx_of y"])
  qed
  from this \<open>bij_betw _ _ _\<close> show "x = y"
    by (metis \<open>x \<in> A\<close> \<open>y \<in> A\<close> \<open>length xs = card A\<close> bij_betw_inv_into_right)
qed

lemma image_sequence_of_inj:
  assumes "bij_betw enum {0..<card A} A"
  shows "sequence_of A enum ` {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} \<subseteq> {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs}"
proof
  fix xs
  assume "xs \<in> sequence_of A enum ` {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
  from this obtain f where xs: "xs = sequence_of A enum f" and f: "f \<in> A \<rightarrow>\<^sub>E B" "inj_on f A" by auto
  moreover from xs f \<open>bij_betw _ _ _\<close> have "set xs \<subseteq> B"
    using set_sequence_of subsetCE by blast
  moreover from xs f \<open>bij_betw _ _ _\<close> have "length xs = card A"
    using length_sequence_of by auto
  moreover from xs f \<open>bij_betw _ _ _\<close> have "distinct xs"
    using inj_on_implies_distinct by simp
  ultimately show "xs \<in> {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs}" by auto
qed

lemma image_function_of_distinct:
  assumes "bij_betw enum {0..<card A} A"
  shows "function_of A enum ` {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
proof
  fix f
  assume f: "f \<in> function_of A enum ` {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs}"
  from f assms have "f \<in> A \<rightarrow>\<^sub>E B"
    using function_of_in_extensional_funcset by blast
  moreover from f assms have "inj_on f A"
    by (auto simp add: assms distinct_implies_inj_on)
  ultimately show "f \<in> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}" by auto
qed

subsection \<open>Bijections\<close>

lemma bij_betw_sequence_of:
  assumes "bij_betw enum {0..<card A} A"
  shows "bij_betw (sequence_of A enum) {f. f \<in> A \<rightarrow>\<^sub>E B \<and> inj_on f A} {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs}"
proof (rule bij_betw_byWitness[where f'="function_of A enum"])
  show "\<forall>f\<in>{f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}. function_of A enum (sequence_of A enum f) = f"
    using assms by (auto simp add: function_of_sequence_of)
  show "\<forall>xs\<in>{xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs}. sequence_of A enum (function_of A enum xs) = xs"
    using assms by (auto simp add: sequence_of_function_of)
  show "sequence_of A enum ` {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} \<subseteq> {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs}"
    using assms by (simp add: image_sequence_of_inj)
  show "function_of A enum ` {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
    using assms by (simp add: image_function_of_distinct)
qed

lemma bij_betw_function_of:
  assumes "bij_betw enum {0..<card A} A"
  shows "bij_betw (function_of A enum) {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs} {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
proof (rule bij_betw_byWitness[where f'="sequence_of A enum"])
  show "\<forall>f\<in>{f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}. function_of A enum (sequence_of A enum f) = f"
    using assms by (auto simp add: function_of_sequence_of)
  show "\<forall>xs\<in>{xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs}. sequence_of A enum (function_of A enum xs) = xs"
    using assms by (auto simp add: sequence_of_function_of)
  show "sequence_of A enum ` {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} \<subseteq> {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs}"
    using assms by (simp add: image_sequence_of_inj)
  show "function_of A enum ` {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs} \<subseteq> {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
    using assms by (simp add: image_function_of_distinct)
qed

subsection \<open>Cardinality\<close>

lemma
  assumes "finite A" "finite B" "card A \<le> card B"
  shows "card {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} = \<Prod>{card B - card A + 1..card B}"
proof -
  obtain enum where "bij_betw enum {0..<card A} A"
    using \<open>finite A\<close> ex_bij_betw_nat_finite by blast
  have "bij_betw (sequence_of A enum) {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs}"
    using \<open>bij_betw enum {0..<card A} A\<close> by (rule bij_betw_sequence_of)
  from this have "card {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} = card {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs}"
    by (rule bij_betw_same_card)
  also have "card {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs} = card {xs. length xs = card A \<and> distinct xs \<and> set xs \<subseteq> B}"
    by meson
  also have "card {xs. length xs = card A \<and> distinct xs \<and> set xs \<subseteq> B} = \<Prod>{card B - card A + 1..card B}"
    using \<open>finite B\<close> \<open>card A \<le> card B\<close> by (rule List.card_lists_distinct_length_eq)
  finally show ?thesis .
qed

lemma card_sequences:
  assumes "finite A" "finite B" "card A \<le> card B"
  shows "card {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs} = fact (card B) div fact (card B - card A)"
proof -
  obtain enum where "bij_betw enum {0..<card A} A"
    using \<open>finite A\<close> ex_bij_betw_nat_finite by blast
  have "bij_betw (function_of A enum) {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs} {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
    using \<open>bij_betw enum {0..<card A} A\<close> by (rule bij_betw_function_of)
  from this have "card {xs. set xs \<subseteq> B \<and> length xs = card A \<and> distinct xs} = card {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
    by (rule bij_betw_same_card)
  also have "card {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} = fact (card B) div fact (card B - card A)"
    using \<open>finite A\<close> \<open>finite B\<close> \<open>card A \<le> card B\<close> by (rule card_extensional_funcset_inj_on)
  finally show ?thesis .
qed

end
