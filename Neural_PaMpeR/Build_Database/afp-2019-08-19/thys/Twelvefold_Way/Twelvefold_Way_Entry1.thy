(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Functions from A to B\<close>

theory Twelvefold_Way_Entry1
imports Preliminaries
begin

text \<open>
Note that the cardinality theorems of both structures, lists and finite
functions, are already available. Hence, this development creates the
bijection between those two structures and transfers the one cardinality
theorem to the other structures and vice versa, although not strictly
needed as both cardinality theorems were already available.
\<close>

subsection \<open>Definition of Bijections\<close>

definition sequence_of :: "'a set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b list"
where
  "sequence_of A enum f = map (\<lambda>n. f (enum n)) [0..<card A]"

definition function_of :: "'a set \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> 'b list \<Rightarrow> ('a \<Rightarrow> 'b)"
where
  "function_of A enum xs = (\<lambda>a. if a \<in> A then xs ! inv_into {0..<length xs} enum a else undefined)"

subsection \<open>Properties for Bijections\<close>

lemma nth_sequence_of:
  assumes "i < card A"
  shows "(sequence_of A enum f) ! i = f (enum i)"
using assms unfolding sequence_of_def by auto

lemma nth_sequence_of_inv_into:
  assumes "bij_betw enum {0..<card A} A"
  assumes "a \<in> A"
  shows "(sequence_of A enum f) ! (inv_into {0..<card A} enum a) = f a"
proof -
  have "inv_into {0..<card A} enum a \<in> {0..<card A}"
    using assms bij_betwE bij_betw_inv_into by blast
  from this assms show "(sequence_of A enum f) ! (inv_into {0..<card A} enum a) = f a"
    unfolding sequence_of_def by (simp add: bij_betw_inv_into_right)
qed

lemma set_sequence_of:
  assumes "bij_betw enum {0..<card A} A"
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "set (sequence_of A enum f) \<subseteq> B"
using PiE bij_betwE assms
unfolding sequence_of_def by fastforce

lemma length_sequence_of:
  assumes "bij_betw enum {0..<card A} A"
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "length (sequence_of A enum f) = card A"
using assms unfolding sequence_of_def by simp

lemma function_of_enum:
  assumes "bij_betw enum {0..<card A} A"
  assumes "length xs = card A"
  assumes "i < card A"
  shows "function_of A enum xs (enum i) = xs ! i"
using assms unfolding function_of_def
by (auto simp add: bij_betw_inv_into_left bij_betwE)

lemma function_of_in_extensional_funcset:
  assumes "bij_betw enum {0..<card A} A"
  assumes "set xs \<subseteq> B" "length xs = card A"
  shows "function_of A enum xs \<in> A \<rightarrow>\<^sub>E B"
proof
  fix x
  assume "x \<in> A"
  have "inv_into {0..<length xs} enum x \<in> {0..<length xs}"
    using \<open>x \<in> A\<close> assms(1, 3) by (metis bij_betw_def inv_into_into)
  from this have "xs ! inv_into {0..<length xs} enum x \<in> set xs" by simp
  from this \<open>set xs \<subseteq> B\<close> show "function_of A enum xs x \<in> B"
    using \<open>x \<in> A\<close> unfolding function_of_def by auto
next
  fix x
  assume "x \<notin> A"
  from this show "function_of A enum xs x = undefined"
    unfolding function_of_def by simp
qed

lemma sequence_of_function_of:
  assumes "bij_betw enum {0..<card A} A"
  assumes "set xs \<subseteq> B" "length xs = card A"
  shows "sequence_of A enum (function_of A enum xs) = xs"
proof (rule nth_equalityI)
  have "function_of A enum xs \<in> A \<rightarrow>\<^sub>E B"
    using assms by (rule function_of_in_extensional_funcset)
  from this show "length (sequence_of A enum (function_of A enum xs)) = length xs"
    using assms(1,3) by (simp add: length_sequence_of)
  from this show "\<And>i. i < length (sequence_of A enum (function_of A enum xs)) \<Longrightarrow> sequence_of A enum (function_of A enum xs) ! i = xs ! i"
    using assms by (auto simp add: nth_sequence_of function_of_enum)
qed

lemma function_of_sequence_of:
  assumes "bij_betw enum {0..<card A} A"
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "function_of A enum (sequence_of A enum f) = f"
proof
  fix x
  show "function_of A enum (sequence_of A enum f) x = f x"
    using assms unfolding function_of_def
    by (auto simp add: length_sequence_of nth_sequence_of_inv_into)
qed

subsection \<open>Bijections\<close>

lemma bij_betw_sequence_of:
  assumes "bij_betw enum {0..<card A} A"
  shows "bij_betw (sequence_of A enum) (A \<rightarrow>\<^sub>E B) {xs. set xs \<subseteq> B \<and> length xs = card A}"
proof (rule bij_betw_byWitness[where f'="function_of A enum"])
  show "\<forall>f\<in>A \<rightarrow>\<^sub>E B. function_of A enum (sequence_of A enum f) = f"
    using assms by (simp add: function_of_sequence_of)
  show "\<forall>xs\<in>{xs. set xs \<subseteq> B \<and> length xs = card A}. sequence_of A enum (function_of A enum xs) = xs"
    using assms by (auto simp add: sequence_of_function_of)
  show "sequence_of A enum ` (A \<rightarrow>\<^sub>E B) \<subseteq> {xs. set xs \<subseteq> B \<and> length xs = card A}"
    using assms set_sequence_of[OF assms] length_sequence_of by auto
  show "function_of A enum ` {xs. set xs \<subseteq> B \<and> length xs = card A} \<subseteq> A \<rightarrow>\<^sub>E B"
    using assms function_of_in_extensional_funcset by blast
qed

lemma bij_betw_function_of:
  assumes "bij_betw enum {0..<card A} A"
  shows "bij_betw (function_of A enum) {xs. set xs \<subseteq> B \<and> length xs = card A} (A \<rightarrow>\<^sub>E B)"
proof (rule bij_betw_byWitness[where f'="sequence_of A enum"])
  show "\<forall>f\<in>A \<rightarrow>\<^sub>E B. function_of A enum (sequence_of A enum f) = f"
    using assms by (simp add: function_of_sequence_of)
  show "\<forall>xs\<in>{xs. set xs \<subseteq> B \<and> length xs = card A}. sequence_of A enum (function_of A enum xs) = xs"
    using assms by (auto simp add: sequence_of_function_of)
  show "sequence_of A enum ` (A \<rightarrow>\<^sub>E B) \<subseteq> {xs. set xs \<subseteq> B \<and> length xs = card A}"
    using assms set_sequence_of[OF assms] length_sequence_of by auto
  show "function_of A enum ` {xs. set xs \<subseteq> B \<and> length xs = card A} \<subseteq> A \<rightarrow>\<^sub>E B"
    using assms function_of_in_extensional_funcset by blast
qed

subsection \<open>Cardinality\<close>

lemma
  assumes "finite A"
  shows "card (A \<rightarrow>\<^sub>E B) = card B ^ card A"
proof -
  obtain enum where "bij_betw enum {0..<card A} A"
    using \<open>finite A\<close> ex_bij_betw_nat_finite by blast
  have "bij_betw (sequence_of A enum) (A \<rightarrow>\<^sub>E B) {xs. set xs \<subseteq> B \<and> length xs = card A}"
    using \<open>bij_betw enum {0..<card A} A\<close> by (rule bij_betw_sequence_of)
  from this have "card (A \<rightarrow>\<^sub>E B) = card {xs. set xs \<subseteq> B \<and> length xs = card A}"
    by (rule bij_betw_same_card)
  also have "card {xs. set xs \<subseteq> B \<and> length xs = card A} = card B ^ card A"
    by (rule card_lists_length_eq)
  finally show ?thesis .
qed

lemma card_sequences:
  assumes "finite A"
  shows "card {xs. set xs \<subseteq> B \<and> length xs = card A} = card B ^ card A"
proof -
  obtain enum where "bij_betw enum {0..<card A} A"
    using \<open>finite A\<close> ex_bij_betw_nat_finite by blast
  have "bij_betw (function_of A enum) {xs. set xs \<subseteq> B \<and> length xs = card A} (A \<rightarrow>\<^sub>E B)"
    using \<open>bij_betw enum {0..<card A} A\<close> by (rule bij_betw_function_of)
  from this have "card {xs. set xs \<subseteq> B \<and> length xs = card A} = card (A \<rightarrow>\<^sub>E B)"
    by (rule bij_betw_same_card)
  also have "card (A \<rightarrow>\<^sub>E B) = card B ^ card A"
    using \<open>finite A\<close> by (rule card_extensional_funcset)
  finally show ?thesis .
qed

lemma
  shows "card {xs. set xs \<subseteq> A \<and> length xs = n} = card A ^ n"
proof -
  have "card {xs. set xs \<subseteq> A \<and> length xs = n} = card {xs. set xs \<subseteq> A \<and> length xs = card {0..<n}}"
    by auto
  also have "\<dots> = card A ^ card {0..<n}" by (subst card_sequences) auto
  also have "\<dots> = card A ^ n" by auto
  finally show ?thesis .
qed

end
