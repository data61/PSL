(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Cardinality of Multisets\<close>

theory Card_Multisets
imports
  "HOL-Library.Multiset"
begin

subsection \<open>Additions to Multiset Theory\<close>

lemma mset_set_set_mset_subseteq:
  "mset_set (set_mset M) \<subseteq># M"
proof (induct M)
  case empty
  show ?case by simp
next
  case (add x M)
  from this show ?case
  proof (cases "x \<in># M")
    assume "x \<in># M"
    from this have "mset_set (set_mset (M + {#x#})) = mset_set (set_mset M)"
      by (simp add: insert_absorb)
    from this add.hyps show ?thesis
      using subset_mset.order.trans by fastforce
  next
    assume "\<not> x \<in># M"
    from this add.hyps have "{#x#} + mset_set (set_mset M) \<subseteq># M + {#x#}"
      by (simp add: insert_subset_eq_iff)
    from this \<open>\<not> x \<in># M\<close> show ?thesis by simp
  qed
qed

lemma size_mset_set_eq_card:
  assumes "finite A"
  shows "size (mset_set A) = card A"
using assms by (induct A) auto

lemma card_set_mset_leq:
  "card (set_mset M) \<le> size M"
by (induct M) (auto simp add: card_insert_le_m1)

subsection \<open>Lemma to Enumerate Sets of Multisets\<close>

lemma set_of_multisets_eq:
  assumes "x \<notin> A"
  shows "{M. set_mset M \<subseteq> insert x A \<and> size M = Suc k} =
    {M. set_mset M \<subseteq> A \<and> size M = Suc k} \<union>
    (\<lambda>M. M + {#x#}) ` {M. set_mset M \<subseteq> insert x A \<and> size M = k}"
proof -
  from \<open>x \<notin> A\<close> have "{M. set_mset M \<subseteq> insert x A \<and> size M = Suc k} =
    {M. set_mset M \<subseteq> A \<and> size M = Suc k} \<union>
    {M. set_mset M \<subseteq> insert x A \<and> size M = Suc k \<and> x \<in># M}"
    by auto
  moreover have "{M. set_mset M \<subseteq> insert x A \<and> size M = Suc k \<and> x \<in># M} =
    (\<lambda>M. M + {#x#}) ` {M. set_mset M \<subseteq> insert x A \<and> size M = k}" (is "?S = ?T")
  proof
    show "?S \<subseteq> ?T"
    proof
      fix M
      assume "M \<in> ?S"
      from this have "M = M - {#x#} + {#x#}" by auto
      moreover have "M - {#x#} \<in> {M. set_mset M \<subseteq> insert x A \<and> size M = k}"
      proof -
        have "set_mset (M - {#x#} + {#x#}) \<subseteq> insert x A"
          using \<open>M \<in> ?S\<close> by force
        moreover have "size (M - {#x#} + {#x#}) = Suc k \<and> x \<in># M - {#x#} + {#x#}"
          using \<open>M \<in> ?S\<close> by force
        ultimately show ?thesis by force
      qed
      ultimately show "M \<in> ?T" by auto
    qed
  next
    show "?T \<subseteq> ?S" by force
  qed
  ultimately show ?thesis by auto
qed

subsection \<open>Derivation of Suitable Induction Rule\<close>

context
begin

private inductive R :: "'a set \<Rightarrow> nat \<Rightarrow> bool"
where
  "finite A \<Longrightarrow> R A 0"
| "R {} k"
| "finite A \<Longrightarrow> x \<notin> A \<Longrightarrow> R A (Suc k) \<Longrightarrow> R (insert x A) k \<Longrightarrow> R (insert x A) (Suc k)"

private lemma R_eq_finite:
  "R A k \<longleftrightarrow> finite A"
proof
  assume "R A k"
  from this show "finite A" by cases auto
next
  assume "finite A"
  from this show "R A k"
  proof (induct A)
    case empty
    from this show ?case by (rule R.intros(2))
  next
    case insert
    from this show ?case
    proof (induct k)
      case 0
      from this show ?case
        by (intro R.intros(1) finite.insertI)
    next
      case Suc
      from this show ?case
        by (metis R.simps Zero_neq_Suc diff_Suc_1)
    qed
  qed
qed

lemma finite_set_and_nat_induct[consumes 1, case_names zero empty step]:
  assumes "finite A"
  assumes "\<And>A. finite A \<Longrightarrow> P A 0"
  assumes "\<And>k. P {} k"
  assumes "\<And>A k x. finite A \<Longrightarrow> x \<notin> A \<Longrightarrow> P A (Suc k) \<Longrightarrow> P (insert x A) k \<Longrightarrow> P (insert x A) (Suc k)"
  shows "P A k"
proof -
  from \<open>finite A\<close> have "R A k" by (subst R_eq_finite)
  from this assms(2-4) show ?thesis by (induct A k) auto
qed

end

subsection \<open>Finiteness of Sets of Multisets\<close>

lemma finite_multisets:
  assumes "finite A"
  shows "finite {M. set_mset M \<subseteq> A \<and> size M = k}"
using assms
proof (induct A k rule: finite_set_and_nat_induct)
  case zero
  from this show ?case by auto
next
  case empty
  from this show ?case by auto
next
  case (step A k x)
  from this show ?case
    using set_of_multisets_eq[OF \<open>x \<notin> A\<close>] by simp
qed

subsection \<open>Cardinality of Multisets\<close>

lemma card_multisets:
  assumes "finite A"
  shows "card {M. set_mset M \<subseteq> A \<and> size M = k} = (card A + k - 1) choose k"
using assms
proof (induct A k rule: finite_set_and_nat_induct)
  case (zero A)
  assume "finite (A :: 'a set)"
  have "{M. set_mset M \<subseteq> A \<and> size M = 0} = {{#}}" by auto
  from this show "card {M. set_mset M \<subseteq> A \<and> size M = 0} = card A + 0 - 1 choose 0"
    by simp
next
  case (empty k)
  show "card {M. set_mset M \<subseteq> {} \<and> size M = k} = card {} + k - 1 choose k"
    by (cases k) (auto simp add: binomial_eq_0)
next
  case (step A k x)
  let ?S\<^sub>1 = "{M. set_mset M \<subseteq> A \<and> size M = Suc k}"
  and ?S\<^sub>2 = "{M. set_mset M \<subseteq> insert x A \<and> size M = k}"
  assume hyps1: "card ?S\<^sub>1 = card A + Suc k - 1 choose Suc k"
  assume hyps2: "card ?S\<^sub>2 = card (insert x A) + k - 1 choose k"
  have finite_sets: "finite ?S\<^sub>1" "finite ((\<lambda>M. M + {#x#}) ` ?S\<^sub>2)"
    using \<open>finite A\<close> by (auto simp add: finite_multisets)
  have inj: "inj_on (\<lambda>M. M + {#x#}) ?S\<^sub>2" by (rule inj_onI) auto
  have "card {M. set_mset M \<subseteq> insert x A \<and> size M = Suc k} =
    card (?S\<^sub>1 \<union> (\<lambda>M. M + {#x#}) ` ?S\<^sub>2)"
    using set_of_multisets_eq \<open>x \<notin> A\<close> by fastforce
  also have "\<dots> = card ?S\<^sub>1 + card ((\<lambda>M. M + {#x#}) ` ?S\<^sub>2)"
    using finite_sets \<open>x \<notin> A\<close> by (subst card_Un_disjoint) auto
  also have "\<dots> = card ?S\<^sub>1 + card ?S\<^sub>2"
    using inj by (auto intro: card_image)
  also have "\<dots> = card A + Suc k - 1 choose Suc k + (card (insert x A) + k - 1 choose k)"
    using hyps1 hyps2 by simp
  also have "\<dots> = card (insert x A) + Suc k - 1 choose Suc k"
    using \<open>x \<notin> A\<close> \<open>finite A\<close> by simp
  finally show ?case .
qed

lemma card_too_small_multisets_covering_set:
  assumes "finite A"
  assumes "k < card A"
  shows "card {M. set_mset M = A \<and> size M = k} = 0"
proof -
  from \<open>k < card A\<close> have eq: "{M. set_mset M = A \<and> size M = k} = {}"
    using card_set_mset_leq Collect_empty_eq leD by auto
  from this show ?thesis by (metis card_empty)
qed

lemma card_multisets_covering_set:
  assumes "finite A"
  assumes "card A \<le> k"
  shows "card {M. set_mset M = A \<and> size M = k} = (k - 1) choose (k - card A)"
proof -
  have "{M. set_mset M = A \<and> size M = k} = (\<lambda>M. M + mset_set A) `
    {M. set_mset M \<subseteq> A \<and> size M = k - card A}" (is "?S = ?f ` ?T")
  proof
    show "?S \<subseteq> ?f ` ?T"
    proof
      fix M
      assume "M \<in> ?S"
      from this have "M = M - mset_set A + mset_set A"
        by (auto simp add: mset_set_set_mset_subseteq subset_mset.diff_add)
      moreover from \<open>M \<in> ?S\<close> have "M - mset_set A \<in> ?T"
        by (auto simp add: mset_set_set_mset_subseteq size_Diff_submset size_mset_set_eq_card in_diffD)
      ultimately show "M \<in> ?f ` ?T" by auto
    qed
  next
    from \<open>finite A\<close> \<open>card A \<le> k\<close> show "?f ` ?T \<subseteq> ?S"
      by (auto simp add: size_mset_set_eq_card)+
  qed
  moreover have "inj_on ?f ?T" by (rule inj_onI) auto
  ultimately have "card ?S = card ?T" by (simp add: card_image)
  also have "\<dots> = card A + (k - card A) - 1 choose (k - card A)"
    using \<open>finite A\<close> by (simp only: card_multisets)
  also have "\<dots> = (k - 1) choose (k - card A)"
    using \<open>card A \<le> k\<close> by auto
  finally show ?thesis .
qed

end
