(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Cardinality of Bijections\<close>

theory Card_Bijections
imports
  Twelvefold_Way_Entry2
  Twelvefold_Way_Entry3
  Twelvefold_Way_Entry5
  Twelvefold_Way_Entry6
  Twelvefold_Way_Entry8
  Twelvefold_Way_Entry9
  Twelvefold_Way_Entry11
  Twelvefold_Way_Entry12
begin

subsection \<open>Bijections from A to B\<close>

lemma bij_betw_set_is_empty:
  assumes "finite A" "finite B"
  assumes "card A \<noteq> card B"
  shows "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} = {}"
using assms bij_betw_same_card by blast

lemma card_bijections_eq_zero:
  assumes "finite A" "finite B"
  assumes "card A \<noteq> card B"
  shows "card {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} = 0"
using bij_betw_set_is_empty[OF assms] by (simp only: card_empty)

text \<open>Two alternative proofs for the cardinality of bijections up to a permutation on A.\<close>

lemma
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} = fact (card B)"
proof -
  have "card {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} = card {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A}"
    using \<open>finite B\<close> \<open>card A = card B\<close> by (metis bij_betw_implies_inj_on_and_card_eq)
  also have "\<dots> = fact (card B)"
    using \<open>finite A\<close> \<open>finite B\<close> \<open>card A = card B\<close> by (simp add: card_extensional_funcset_inj_on)
  finally show ?thesis .
qed

lemma card_bijections:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} = fact (card B)"
proof -
  have "card {f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} = card {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B}"
    using \<open>finite A\<close> \<open>card A = card B\<close>
    by (metis bij_betw_implies_surj_on_and_card_eq)
  also have "\<dots> = fact (card B)"
    using \<open>finite A\<close> \<open>finite B\<close> \<open>card A = card B\<close>
    by (simp add: card_extensional_funcset_surj_on)
  finally show ?thesis .
qed

subsection \<open>Bijections from A to B up to a Permutation on A\<close>

lemma bij_betw_quotient_domain_permutation_eq_empty:
  assumes "card A \<noteq> card B"
  shows "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B = {}"
using \<open>card A \<noteq> card B\<close> bij_betw_same_card by auto

lemma card_bijections_domain_permutation_eq_0:
  assumes "card A \<noteq> card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B) = 0"
using bij_betw_quotient_domain_permutation_eq_empty[OF assms] by (simp only: card_empty)

text \<open>Two alternative proofs for the cardinality of bijections up to a permutation on A.\<close>

lemma
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B) = 1"
proof -
  from assms have "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B
    = {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_permutation A B"
    by (metis (no_types, lifting) PiE_cong bij_betw_implies_inj_on_and_card_eq)
  from this show ?thesis
    using assms by (simp add: card_injective_functions_domain_permutation)
qed

lemma card_bijections_domain_permutation_eq_1:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B) = 1"
proof -
  from assms have "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B
    = {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_permutation A B"
    by (metis (no_types, lifting) PiE_cong bij_betw_implies_surj_on_and_card_eq)
  from this show ?thesis
    using assms by (simp add: card_surjective_functions_domain_permutation)
qed

lemma card_bijections_domain_permutation:
  assumes "finite A" "finite B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_permutation A B) = iverson (card A = card B)"
using assms card_bijections_domain_permutation_eq_0 card_bijections_domain_permutation_eq_1
unfolding iverson_def by auto

subsection \<open>Bijections from A to B up to a Permutation on B\<close>

lemma bij_betw_quotient_range_permutation_eq_empty:
  assumes "card A \<noteq> card B"
  shows "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B = {}"
using \<open>card A \<noteq> card B\<close> bij_betw_same_card by auto

lemma card_bijections_range_permutation_eq_0:
  assumes "card A \<noteq> card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B) = 0"
using bij_betw_quotient_range_permutation_eq_empty[OF assms] by (simp only: card_empty)

text \<open>Two alternative proofs for the cardinality of bijections up to a permutation on B.\<close>

lemma
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B) = 1"
proof -
  from assms have "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B =
    {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // range_permutation A B"
    by (metis (no_types, lifting) PiE_cong bij_betw_implies_inj_on_and_card_eq)
  from this show ?thesis
    using assms by (simp add: iverson_def card_injective_functions_range_permutation)
qed

lemma card_bijections_range_permutation_eq_1:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B) = 1"
proof -
  from assms have "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B =
    {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // range_permutation A B"
    by (metis (no_types, lifting) PiE_cong bij_betw_implies_surj_on_and_card_eq)
  from this show ?thesis
    using assms by (simp add: card_surjective_functions_range_permutation)
qed

lemma card_bijections_range_permutation:
  assumes "finite A" "finite B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // range_permutation A B) = iverson (card A = card B)"
using assms card_bijections_range_permutation_eq_0 card_bijections_range_permutation_eq_1
unfolding iverson_def by auto

subsection \<open>Bijections from A to B up to a Permutation on A and B\<close>

lemma bij_betw_quotient_domain_and_range_permutation_eq_empty:
  assumes "card A \<noteq> card B"
  shows "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B = {}"
using \<open>card A \<noteq> card B\<close> bij_betw_same_card by auto

lemma card_bijections_domain_and_range_permutation_eq_0:
  assumes "card A \<noteq> card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B) = 0"
using bij_betw_quotient_domain_and_range_permutation_eq_empty[OF assms] by (simp only: card_empty)

text \<open>Two alternative proofs for the cardinality of bijections up to a permutation on A and B.\<close>

lemma
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B) = 1"
proof -
  from assms have "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B =
    {f \<in> A \<rightarrow>\<^sub>E B. inj_on f A} // domain_and_range_permutation A B"
    by (metis (no_types, lifting) PiE_cong bij_betw_implies_inj_on_and_card_eq)
  from this show ?thesis
    using assms by (simp add: iverson_def card_injective_functions_domain_and_range_permutation)
qed

lemma card_bijections_domain_and_range_permutation_eq_1:
  assumes "finite A" "finite B"
  assumes "card A = card B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B) = 1"
proof -
  from assms have "{f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B =
    {f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_and_range_permutation A B"
    by (metis (no_types, lifting) PiE_cong bij_betw_implies_surj_on_and_card_eq)
  from this show ?thesis
    using assms by (simp add: card_surjective_functions_domain_and_range_permutation Partition_diag)
qed

lemma card_bijections_domain_and_range_permutation:
  assumes "finite A" "finite B"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. bij_betw f A B} // domain_and_range_permutation A B) = iverson (card A = card B)"
using assms card_bijections_domain_and_range_permutation_eq_0 card_bijections_domain_and_range_permutation_eq_1
unfolding iverson_def by auto

end
