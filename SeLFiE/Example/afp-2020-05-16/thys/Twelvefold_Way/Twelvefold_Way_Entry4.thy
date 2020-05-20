(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Functions from A to B, up to a Permutation of A\<close>

theory Twelvefold_Way_Entry4
imports Equiv_Relations_on_Functions
begin

subsection \<open>Definition of Bijections\<close>

definition msubset_of :: "'a set \<Rightarrow> ('a  \<Rightarrow> 'b) set \<Rightarrow> 'b multiset"
where
  "msubset_of A F = univ (\<lambda>f. image_mset f (mset_set A)) F"

definition functions_of :: "'a set \<Rightarrow> 'b multiset \<Rightarrow> ('a \<Rightarrow> 'b) set"
where
  "functions_of A B = {f \<in> A \<rightarrow>\<^sub>E set_mset B. image_mset f (mset_set A) = B}"

subsection \<open>Properties for Bijections\<close>

lemma msubset_of:
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B"
  shows "size (msubset_of A F) = card A"
  and "set_mset (msubset_of A F) \<subseteq> B"
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
  finally have msubset_of_eq: "msubset_of A F = image_mset f (mset_set A)" .
  show "size (msubset_of A F) = card A"
  proof -
    have "size (msubset_of A F) = size (image_mset f (mset_set A))"
      unfolding msubset_of_eq ..
    also have "\<dots> = card A"
      by (cases \<open>finite A\<close>) auto
    finally show ?thesis .
  qed
  show "set_mset (msubset_of A F) \<subseteq> B"
  proof -
    have "set_mset (msubset_of A F) = set_mset (image_mset f (mset_set A))"
      unfolding msubset_of_eq ..
    also have "\<dots> \<subseteq> B"
      using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> by (cases "finite A") auto
    finally show ?thesis .
  qed
qed

lemma functions_of:
  assumes "finite A"
  assumes "set_mset M \<subseteq> B"
  assumes "size M = card A"
  shows "functions_of A M \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B"
proof -
  obtain f where "f \<in> A \<rightarrow>\<^sub>E set_mset M" and "image_mset f (mset_set A) = M"
    using obtain_function_on_ext_funcset \<open>finite A\<close> \<open>size M = card A\<close> by blast
  from \<open>f \<in> A \<rightarrow>\<^sub>E set_mset M\<close> have "f \<in> A \<rightarrow>\<^sub>E B"
    using \<open>set_mset M \<subseteq> B\<close> PiE_iff subset_eq by blast
  have "functions_of A M = (domain_permutation A B) `` {f}"
  proof
    show "functions_of A M \<subseteq> domain_permutation A B `` {f}"
    proof
      fix f'
      assume "f' \<in> functions_of A M"
      from this have "M = image_mset f' (mset_set A)" and "f' \<in> A \<rightarrow>\<^sub>E f' ` A"
        using \<open>finite A\<close> unfolding functions_of_def by auto
      from this assms(1, 2) have "f' \<in> A \<rightarrow>\<^sub>E B"
        by (simp add: PiE_iff image_subset_iff)
      obtain p where "p permutes A \<and> (\<forall>x\<in>A. f x = f' (p x))"
        using \<open>finite A\<close> \<open>image_mset f (mset_set A) = M\<close> \<open>M = image_mset f' (mset_set A)\<close>
          image_mset_eq_implies_permutes by blast
      from this show "f' \<in> domain_permutation A B `` {f}"
        using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close>
        unfolding domain_permutation_def by auto
    qed
  next
    show "domain_permutation A B `` {f} \<subseteq> functions_of A M"
    proof
      fix f'
      assume "f' \<in> domain_permutation A B `` {f}"
      from this have "(f, f') \<in> domain_permutation A B" by auto
      from this \<open>image_mset f (mset_set A) = M\<close> have "image_mset f' (mset_set A) = M"
        using congruentD[OF image_mset_respects_domain_permutation] by metis
      moreover from this \<open>(f, f') \<in> domain_permutation A B\<close> have "f' \<in> A \<rightarrow>\<^sub>E set_mset M"
        using \<open>finite A\<close> unfolding domain_permutation_def by auto
      ultimately show "f' \<in> functions_of A M"
        unfolding functions_of_def by auto
    qed
  qed
  from this \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> show ?thesis by (auto intro: quotientI)
qed

lemma functions_of_msubset_of:
  assumes "finite A"
  assumes "F \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B"
  shows "functions_of A (msubset_of A F) = F"
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
  finally have msubset_of_eq: "msubset_of A F = image_mset f (mset_set A)" .
  show ?thesis
  proof
    show "functions_of A (msubset_of A F) \<subseteq> F"
    proof
      fix f'
      assume "f' \<in> functions_of A (msubset_of A F)"
      from this have f': "f' \<in> A \<rightarrow>\<^sub>E f ` set_mset (mset_set A)"
      "image_mset f' (mset_set A) = image_mset f (mset_set A)"
        unfolding functions_of_def by (auto simp add: msubset_of_eq)
      from \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> have "f ` A \<subseteq> B" by auto
      note \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
      moreover from f'(1) \<open>finite A\<close> \<open>f ` A \<subseteq> B\<close> have "f' \<in> A \<rightarrow>\<^sub>E B" by auto
      moreover obtain p where "p permutes A \<and> (\<forall>x\<in>A. f x = f' (p x))"
        using \<open>finite A\<close> \<open>image_mset f' (mset_set A) = image_mset f (mset_set A)\<close>
          by (metis image_mset_eq_implies_permutes)
      ultimately show "f' \<in> F"
        unfolding F_eq domain_permutation_def by auto
    qed
  next
    show "F \<subseteq> functions_of A (msubset_of A F)"
    proof
      fix f'
      assume "f' \<in> F"
      from this have "f' \<in> A \<rightarrow>\<^sub>E B"
        unfolding F_eq domain_permutation_def by auto
      from \<open>f' \<in> F\<close> obtain p where "p permutes A \<and> (\<forall>x\<in>A. f x = f' (p x))"
        unfolding F_eq domain_permutation_def by auto
      from this have eq: "image_mset f' (mset_set A) = image_mset f (mset_set A)"
        using permutes_implies_image_mset_eq by blast
      moreover have "f' \<in> A \<rightarrow>\<^sub>E set_mset (image_mset f (mset_set A))"
        using \<open>finite A\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> eq[symmetric] by auto
      ultimately show "f' \<in> functions_of A (msubset_of A F)"
        unfolding functions_of_def msubset_of_eq by auto
    qed
  qed
qed

lemma msubset_of_functions_of:
  assumes "set_mset M \<subseteq> B" "size M = card A" "finite A"
  shows "msubset_of A (functions_of A M) = M"
proof -
  from assms have "functions_of A M \<in> (A \<rightarrow>\<^sub>E B) // domain_permutation A B"
    using functions_of by fastforce
  from this obtain f where "f \<in> A \<rightarrow>\<^sub>E B" and "functions_of A M = domain_permutation A B `` {f}"
    by (rule quotientE)
  from this have "f \<in> functions_of A M"
    using equiv_domain_permutation equiv_class_self by fastforce
  have "msubset_of A (functions_of A M) = univ (\<lambda>f. image_mset f (mset_set A)) (functions_of A M)"
    unfolding msubset_of_def ..
  also have "\<dots> = univ (\<lambda>f. image_mset f (mset_set A)) (domain_permutation A B `` {f})"
    unfolding \<open>functions_of A M = domain_permutation A B `` {f}\<close> ..
  also have "\<dots> = image_mset f (mset_set A)"
    using equiv_domain_permutation image_mset_respects_domain_permutation \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>
    by (subst univ_commute') auto
  also have "image_mset f (mset_set A) = M"
    using \<open>f \<in> functions_of A M\<close> unfolding functions_of_def by simp
  finally show ?thesis .
qed

subsection \<open>Bijections\<close>

lemma bij_betw_msubset_of:
  assumes "finite A"
  shows "bij_betw (msubset_of A) ((A \<rightarrow>\<^sub>E B) // domain_permutation A B) {M. set_mset M \<subseteq> B \<and> size M = card A}"
proof (rule bij_betw_byWitness[where f'="\<lambda>M. functions_of A M"])
  show "\<forall>F\<in>(A \<rightarrow>\<^sub>E B) // domain_permutation A B. functions_of A (msubset_of A F) = F"
    using \<open>finite A\<close> by (auto simp add: functions_of_msubset_of)
  show "\<forall>M\<in>{M. set_mset M \<subseteq> B \<and> size M = card A}. msubset_of A (functions_of A M) = M"
    using \<open>finite A\<close> by (auto simp add: msubset_of_functions_of)
  show "msubset_of A ` ((A \<rightarrow>\<^sub>E B) // domain_permutation A B) \<subseteq> {M. set_mset M \<subseteq> B \<and> size M = card A}"
    using msubset_of by blast
  show "functions_of A ` {M. set_mset M \<subseteq> B \<and> size M = card A} \<subseteq> (A \<rightarrow>\<^sub>E B) // domain_permutation A B"
    using functions_of \<open>finite A\<close> by blast
qed

subsection \<open>Cardinality\<close>

lemma
  assumes "finite A" "finite B"
  shows "card ((A \<rightarrow>\<^sub>E B) // domain_permutation A B) = card B + card A - 1 choose card A"
proof -
  have "bij_betw (msubset_of A) ((A \<rightarrow>\<^sub>E B) // domain_permutation A B) {M. set_mset M \<subseteq> B \<and> size M = card A}"
    using \<open>finite A\<close> by (rule bij_betw_msubset_of)
  from this have "card ((A \<rightarrow>\<^sub>E B) // domain_permutation A B) = card {M. set_mset M \<subseteq> B \<and> size M = card A}"
    by (rule bij_betw_same_card)
  also have "card {M. set_mset M \<subseteq> B \<and> size M = card A} = card B + card A - 1 choose card A"
    using \<open>finite B\<close> by (rule card_multisets)
  finally show ?thesis .
qed

end
