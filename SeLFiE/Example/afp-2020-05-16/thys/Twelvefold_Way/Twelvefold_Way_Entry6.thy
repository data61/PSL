(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Surjections from A to B up to a Permutation on A\<close>

theory Twelvefold_Way_Entry6
imports Twelvefold_Way_Entry4
begin

subsection \<open>Properties for Bijections\<close>

lemma set_mset_eq_implies_surj_on:
  assumes "finite A"
  assumes "size M = card A" "set_mset M = B"
  assumes "f \<in> functions_of A M"
  shows   "f ` A = B"
proof -
  from \<open>f \<in> functions_of A M\<close> have "image_mset f (mset_set A) = M"
    unfolding functions_of_def by auto
  from \<open>image_mset f (mset_set A) = M\<close> show "f ` A = B"
    using \<open>set_mset M = B\<close> \<open>finite A\<close> finite_set_mset_mset_set set_image_mset by force
qed

lemma surj_on_implies_set_mset_eq:
  assumes "finite A"
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B"
  assumes "univ (\<lambda>f. f ` A = B) F"
  shows "set_mset (msubset_of A F) = B"
proof -
  from \<open>F \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B\<close> obtain f where "f \<in> A \<rightarrow>\<^sub>E B"
    and F_eq: "F = domain_permutation A B `` {f}" using quotientE by blast
  have "msubset_of A F = univ (\<lambda>f. image_mset f (mset_set A)) F"
    unfolding msubset_of_def ..
  also have "\<dots> = univ (\<lambda>f. image_mset f (mset_set A)) (domain_permutation A B `` {f})"
    unfolding F_eq ..
  also have "\<dots> = image_mset f (mset_set A)"
    using equiv_domain_permutation image_mset_respects_domain_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') auto
  finally have eq: "msubset_of A F = image_mset f (mset_set A)" .
  from iffD1[OF univ_commute', OF equiv_domain_permutation, OF surjective_respects_domain_permutation, OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>]
    \<open>univ (\<lambda>f. f ` A = B) F\<close> have "f ` A = B" by (simp add: F_eq)
  have "set_mset (image_mset f (mset_set A)) = B"
  proof
    show "set_mset (image_mset f (mset_set A)) \<subseteq> B"
      using \<open>finite A\<close> \<open>f ` A = B\<close> by auto
  next
    show "B \<subseteq> set_mset (image_mset f (mset_set A))"
      using \<open>finite A\<close> by (simp add: \<open>f ` A = B\<close>[symmetric] in_image_mset)
  qed
  from this show "set_mset (msubset_of A F) = B"
    unfolding eq .
qed

lemma functions_of_is_surj_on:
  assumes "finite A"
  assumes "size M = card A" "set_mset M = B"
  shows "univ (\<lambda>f. f ` A = B) (functions_of A M)"
proof -
  have "functions_of A M \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B"
    using functions_of \<open>finite A\<close> \<open>size M = card A\<close> \<open>set_mset M = B\<close>  by fastforce
  from this obtain f where eq_f: "functions_of A M = domain_permutation A B `` {f}" and "f \<in> A \<rightarrow>\<^sub>E B"
    using quotientE by blast
  from eq_f have "f \<in> functions_of A M"
    using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> equiv_domain_permutation equiv_class_self by fastforce
  have "f ` A = B"
    using \<open>f \<in> functions_of A M\<close> assms set_mset_eq_implies_surj_on by fastforce
  from this show ?thesis
    unfolding eq_f using equiv_domain_permutation surjective_respects_domain_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') assumption+
qed

subsection \<open>Bijections\<close>

lemma bij_betw_msubset_of:
  assumes "finite A"
  shows "bij_betw (msubset_of A) ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_permutation A B)
    {M. set_mset M = B \<and> size M = card A}"
    (is "bij_betw _ ?FSet ?MSet")
proof (rule bij_betw_byWitness[where f'="\<lambda>M. functions_of A M"])
  have quotient_eq: "?FSet = {F \<in> ((A \<rightarrow>\<^sub>E B) // domain_permutation A B). univ (\<lambda>f. f ` A = B) F}"
    using equiv_domain_permutation[of A B] surjective_respects_domain_permutation[of A B]
    by (simp only: univ_preserves_predicate)
  show "\<forall>f\<in>?FSet. functions_of A (msubset_of A f) = f"
    using \<open>finite A\<close> by (auto simp only: quotient_eq functions_of_msubset_of)
  show "\<forall>M\<in>?MSet. msubset_of A (functions_of A M) = M"
    using \<open>finite A\<close> msubset_of_functions_of by blast
  show "msubset_of A ` ?FSet \<subseteq> ?MSet"
    using \<open>finite A\<close> by (auto simp add: quotient_eq surj_on_implies_set_mset_eq msubset_of)
  show "functions_of A ` ?MSet \<subseteq> ?FSet"
    using \<open>finite A\<close> by (auto simp add: quotient_eq intro: functions_of functions_of_is_surj_on)
qed

subsection \<open>Cardinality\<close>

lemma card_surjective_functions_domain_permutation:
  assumes "finite A" "finite B"
  assumes "card B \<le> card A"
  shows "card ({f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_permutation A B) = (card A - 1) choose (card A - card B)"
proof -
  let ?FSet = "{f \<in> A \<rightarrow>\<^sub>E B. f ` A = B} // domain_permutation A B"
  and ?MSet = "{M. set_mset M = B \<and> size M = card A}"
  have "bij_betw (msubset_of A) ?FSet ?MSet"
    using \<open>finite A\<close> by (rule bij_betw_msubset_of)
  from this have "card ?FSet = card ?MSet"
    by (rule bij_betw_same_card)
  also have "card ?MSet = (card A - 1) choose (card A - card B)"
    using \<open>finite B\<close> \<open>card B \<le> card A\<close> by (rule card_multisets_covering_set)
  finally show ?thesis .
qed

end
