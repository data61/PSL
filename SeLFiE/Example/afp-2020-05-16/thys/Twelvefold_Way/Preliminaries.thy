(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Preliminaries\<close>

theory Preliminaries
imports
  Main
  "HOL-Library.Multiset"
  "HOL-Library.FuncSet"
  "HOL-Library.Permutations"
  "HOL-ex.Birthday_Paradox"
  Card_Partitions.Card_Partitions
  Bell_Numbers_Spivey.Bell_Numbers
  Card_Multisets.Card_Multisets
  Card_Number_Partitions.Card_Number_Partitions
begin

subsection \<open>Additions to Finite Set Theory\<close>

lemma subset_with_given_card_exists:
  assumes "n \<le> card A"
  shows "\<exists>B \<subseteq> A. card B = n"
using assms proof (induct n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  from this obtain B where "B \<subseteq> A" "card B = n" by auto
  from this \<open>B \<subseteq> A\<close> \<open>card B = n\<close> have "card B < card A"
    using Suc.prems by linarith
  from \<open>Suc n \<le> card A\<close> card_infinite have "finite A" by force
  from this \<open>B \<subseteq> A\<close> finite_subset have "finite B" by blast
  from \<open>card B < card A\<close> \<open>B \<subseteq> A\<close> obtain a where "a \<in> A" "a \<notin> B"
    by (metis less_irrefl subsetI subset_antisym)
  have "insert a B \<subseteq> A" "card (insert a B) = Suc n"
    using \<open>finite B\<close> \<open>a \<in> A\<close> \<open>a \<notin> B\<close> \<open>B \<subseteq> A\<close> \<open>card B = n\<close> by auto
  then show ?case by blast
qed

subsection \<open>Additions to Equiv Relation Theory\<close>

lemmas univ_commute' = univ_commute[unfolded Equiv_Relations.proj_def]

lemma univ_predicate_impl_forall:
  assumes "equiv A R"
  assumes "P respects R"
  assumes "X \<in> A // R"
  assumes "univ P X"
  shows "\<forall>x\<in>X. P x"
proof -
  from assms(1,3) obtain x where "x \<in> X"
    by (metis equiv_class_self quotientE)
  from \<open>x \<in> X\<close> assms(1,3) have "X = R `` {x}"
    by (metis Image_singleton_iff equiv_class_eq quotientE)
  from assms(1,2,4) this show ?thesis
    using equiv_class_eq_iff univ_commute' by fastforce
qed

lemma univ_preserves_predicate:
  assumes "equiv A r"
  assumes "P respects r"
  shows "{x \<in> A. P x} // r = {X \<in> A // r. univ P X}"
proof
  show "{x \<in> A. P x} // r \<subseteq> {X \<in> A // r. univ P X}"
  proof
    fix X
    assume "X \<in> {x \<in> A. P x} // r"
    from this obtain x where "x \<in> {x \<in> A. P x}" and "X = r `` {x}"
      using quotientE by blast
    have "X \<in> A // r"
      using \<open>X = r `` {x}\<close> \<open>x \<in> {x \<in> A. P x}\<close>
      by (auto intro: quotientI)
    moreover have "univ P X"
      using \<open>X = r `` {x}\<close> \<open>x \<in> {x \<in> A. P x}\<close> assms
      by (simp add: proj_def[symmetric] univ_commute)
    ultimately show "X \<in> {X \<in> A // r. univ P X}" by auto
  qed
next
  show "{X \<in> A // r. univ P X} \<subseteq> {x \<in> A. P x} // r"
  proof
    fix X
    assume "X \<in> {X \<in> A // r. univ P X}"
    from this have "X \<in> A // r" and "univ P X" by auto
    from \<open>X \<in> A // r\<close> obtain x where "x \<in> A" and "X = r `` {x}"
      using quotientE by blast
    have "x \<in> {x \<in> A. P x}"
      using \<open>x \<in> A\<close> \<open>X = r `` {x}\<close> \<open>univ P X\<close> assms
      by (simp add: proj_def[symmetric] univ_commute)
    from this show "X \<in> {x \<in> A. P x} // r"
      using \<open>X = r `` {x}\<close> by (auto intro: quotientI)
  qed
qed

lemma Union_quotient_restricted:
  assumes "equiv A r"
  assumes "P respects r"
  shows "\<Union>({x \<in> A. P x} // r) = {x \<in> A. P x}"
proof
  show "\<Union>({x \<in> A. P x} // r) \<subseteq> {x \<in> A. P x}"
  proof
    fix x
    assume "x \<in> \<Union>({x \<in> A. P x} // r)"
    from this obtain X where "x \<in> X" and "X \<in> {x \<in> A. P x} // r" by blast
    from this obtain x' where "X = r `` {x'}" and "x' \<in> {x \<in> A. P x}"
      using quotientE by blast
    from this \<open>x \<in> X\<close> have "x \<in> A"
      using \<open>equiv A r\<close> by (simp add: equiv_class_eq_iff)
    moreover from \<open>X = r `` {x'}\<close> \<open>x \<in> X\<close> \<open>x' \<in> {x \<in> A. P x}\<close> have "P x"
      using \<open>P respects r\<close> congruentD by fastforce
    ultimately show "x \<in> {x \<in> A. P x}" by auto
  qed
next
  show "{x \<in> A. P x} \<subseteq> \<Union>({x \<in> A. P x} // r)"
  proof
    fix x
    assume "x \<in> {x \<in> A. P x}"
    from this have "x \<in> r `` {x}"
      using \<open>equiv A r\<close> equiv_class_self by fastforce
    from \<open>x \<in> {x \<in> A. P x}\<close> have "r `` {x} \<in> {x \<in> A. P x} // r"
      by (auto intro: quotientI)
    from this \<open>x \<in> r `` {x}\<close> show "x \<in> \<Union>({x \<in> A. P x} // r)" by auto
  qed
qed

lemma finite_equiv_implies_finite_carrier:
  assumes "equiv A R"
  assumes "finite (A // R)"
  assumes "\<forall>X \<in> A // R. finite X"
  shows "finite A"
proof -
  from \<open>equiv A R\<close> have "A = \<Union>(A // R)"
    by (simp add: Union_quotient)
  from this \<open>finite (A // R)\<close> \<open>\<forall>X \<in> A // R. finite X\<close> show "finite A"
    using finite_Union by fastforce
qed

lemma finite_quotient_iff:
  assumes "equiv A R"
  shows "finite A \<longleftrightarrow> (finite (A // R) \<and> (\<forall>X \<in> A // R. finite X))"
using assms by (meson equiv_type finite_equiv_class finite_equiv_implies_finite_carrier finite_quotient)

subsubsection \<open>Counting Sets by Splitting into Equivalence Classes\<close>

lemma card_equiv_class_restricted:
  assumes "finite {x \<in> A. P x}"
  assumes "equiv A R"
  assumes "P respects R"
  shows "card {x \<in> A. P x} = sum card ({x \<in> A. P x} // R)"
proof -
  have "card {x \<in> A. P x} = card (\<Union>({x \<in> A. P x} // R))"
    using \<open>equiv A R\<close> \<open>P respects R\<close> by (simp add: Union_quotient_restricted)
  also have "card (\<Union>({x \<in> A. P x} // R)) = (\<Sum>C\<in>{x \<in> A. P x} // R. card C)"
  proof -
    from \<open>finite {x \<in> A. P x}\<close> have "finite ({x \<in> A. P x} // R)"
      using \<open>equiv A R\<close> by (metis finite_imageI proj_image)
    moreover from \<open>finite {x \<in> A. P x}\<close> have "\<forall>C\<in>{x \<in> A. P x} // R. finite C"
      using \<open>equiv A R\<close> \<open>P respects R\<close> Union_quotient_restricted
        Union_upper finite_subset by fastforce
    moreover have "\<forall>C1 \<in> {x \<in> A. P x} // R. \<forall>C2 \<in> {x \<in> A. P x} // R. C1 \<noteq> C2 \<longrightarrow> C1 \<inter> C2 = {}"
      using \<open>equiv A R\<close> quotient_disj
      by (metis (no_types, lifting) mem_Collect_eq quotientE quotientI)
    ultimately show ?thesis
      by (subst card_Union_disjoint) (auto simp: pairwise_def disjnt_def)
  qed
  finally show ?thesis .
qed

lemma card_equiv_class_restricted_same_size:
  assumes "equiv A R"
  assumes "P respects R"
  assumes "\<And>F. F \<in> {x \<in> A. P x} // R \<Longrightarrow> card F = k"
  shows "card {x \<in> A. P x} = k * card ({x \<in> A. P x} // R)"
proof cases
  assume "finite {x \<in> A. P x}"
  have "card {x \<in> A. P x} = sum card ({x \<in> A. P x} // R)"
    using \<open>finite {x \<in> A. P x}\<close> \<open>equiv A R\<close> \<open>P respects R\<close>
    by (simp add: card_equiv_class_restricted)
  also have "sum card ({x \<in> A. P x} // R) = k * card ({x \<in> A. P x} // R)"
    by (simp add: \<open>\<And>F. F \<in> {x \<in> A. P x} // R \<Longrightarrow> card F = k\<close>)
  finally show ?thesis .
next
  assume "infinite {x \<in> A. P x}"
  from this have "infinite (\<Union>({a \<in> A. P a} // R))"
    using \<open>equiv A R\<close> \<open>P respects R\<close> by (simp add: Union_quotient_restricted)
  from this have "infinite ({x \<in> A. P x} // R) \<or> (\<exists>X \<in> {x \<in> A. P x} // R. infinite X)"
    by auto
  from this show ?thesis
  proof
    assume "infinite ({x \<in> A. P x} // R)"
    from this \<open>infinite {x \<in> A. P x}\<close> show ?thesis by simp
  next
    assume "\<exists>X \<in> {x \<in> A. P x} // R. infinite X"
    from this \<open>infinite {x \<in> A. P x}\<close> show ?thesis
      using \<open>\<And>F. F \<in> {x \<in> A. P x} // R \<Longrightarrow> card F = k\<close> card_infinite by auto
  qed
qed

lemma card_equiv_class:
  assumes "finite A"
  assumes "equiv A R"
  shows "card A = sum card (A // R)"
proof -
  have "(\<lambda>x. True) respects R" by (simp add: congruentI)
  from \<open>finite A\<close> \<open>equiv A R\<close> this show ?thesis
    using card_equiv_class_restricted[where P="\<lambda>x. True"] by auto
qed

lemma card_equiv_class_same_size:
  assumes "equiv A R"
  assumes "\<And>F. F \<in> A // R \<Longrightarrow> card F = k"
  shows "card A = k * card (A // R)"
proof -
  have "(\<lambda>x. True) respects R" by (simp add: congruentI)
  from \<open>equiv A R\<close> \<open>\<And>F. F \<in> A // R \<Longrightarrow> card F = k\<close> this show ?thesis
    using card_equiv_class_restricted_same_size[where P="\<lambda>x. True"] by auto
qed

subsection \<open>Additions to FuncSet Theory\<close>

lemma finite_same_card_bij_on_ext_funcset:
  assumes "finite A" "finite B" "card A = card B"
  shows "\<exists>f. f \<in> A \<rightarrow>\<^sub>E B \<and> bij_betw f A B"
proof -
  from assms obtain f' where f': "bij_betw f' A B"
    using finite_same_card_bij by auto
  define f where "\<And>x. f x = (if x \<in> A then f' x else undefined)"
  have "f \<in> A \<rightarrow>\<^sub>E B"
    using f' unfolding f_def by (auto simp add: bij_betwE)
  moreover have "bij_betw f A B"
  proof -
    have "bij_betw f' A B \<longleftrightarrow> bij_betw f A B"
      unfolding f_def by (auto intro!: bij_betw_cong)
    from this \<open>bij_betw f' A B\<close> show ?thesis by auto
  qed
  ultimately show ?thesis by auto
qed

lemma card_extensional_funcset:
  assumes "finite A"
  shows "card (A \<rightarrow>\<^sub>E B) = card B ^ card A"
using assms by (simp add: card_PiE prod_constant)

lemma bij_betw_implies_inj_on_and_card_eq:
  assumes "finite B"
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "bij_betw f A B \<longleftrightarrow> inj_on f A \<and> card A = card B"
proof
  assume "bij_betw f A B"
  from this show "inj_on f A \<and> card A = card B"
    by (simp add: bij_betw_imp_inj_on bij_betw_same_card)
next
  assume "inj_on f A \<and> card A = card B"
  from this have "inj_on f A" and "card A = card B" by auto
  from \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> have "f ` A \<subseteq> B" by auto
  from \<open>inj_on f A\<close> have "card (f ` A) = card A" by (simp add: card_image)
  from \<open>f ` A \<subseteq> B\<close> \<open>card A = card B\<close> this have "f ` A = B"
    by (simp add: \<open>finite B\<close> card_subset_eq)
  from \<open>inj_on f A\<close> this show "bij_betw f A B" by (rule bij_betw_imageI)
qed

lemma bij_betw_implies_surj_on_and_card_eq:
  assumes "finite A"
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  shows "bij_betw f A B \<longleftrightarrow> f ` A = B \<and> card A = card B"
proof
  assume "bij_betw f A B"
  show "f ` A = B \<and> card A = card B"
    using \<open>bij_betw f A B\<close> bij_betw_imp_surj_on bij_betw_same_card by blast
next
  assume "f ` A = B \<and> card A = card B"
  from this have "f ` A = B" and "card A = card B" by auto
  from this have "inj_on f A"
    by (simp add: \<open>finite A\<close> inj_on_iff_eq_card)
  from this \<open>f ` A = B\<close> show "bij_betw f A B" by (rule bij_betw_imageI)
qed

subsection \<open>Additions to Permutations Theory\<close>

lemma
  assumes "f \<in> A \<rightarrow>\<^sub>E B" "f ` A = B"
  assumes "p permutes B" "(\<forall>x. f' x = p (f x))"
  shows "(\<lambda>b. {x\<in>A. f x = b}) ` B = (\<lambda>b. {x\<in>A. f' x = b}) ` B"
proof
  show "(\<lambda>b. {x \<in> A. f x = b}) ` B \<subseteq> (\<lambda>b. {x \<in> A. f' x = b}) ` B"
  proof
    fix X
    assume "X \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B"
    from this obtain b where X_eq: "X = {x \<in> A. f x = b}" and "b \<in> B" by blast
    from assms(3, 4) have "\<And>x. f x = b \<longleftrightarrow> f' x = p b" by (metis permutes_def)
    from \<open>p permutes B\<close> X_eq this have "X = {x \<in> A. f' x = p b}"
      using Collect_cong by auto
    moreover from \<open>b \<in> B\<close> \<open>p permutes B\<close> have "p b \<in> B"
      by (simp add: permutes_in_image)
    ultimately show "X \<in> (\<lambda>b. {x \<in> A. f' x = b}) ` B" by blast
  qed
next
  show "(\<lambda>b. {x \<in> A. f' x = b}) ` B \<subseteq> (\<lambda>b. {x \<in> A. f x = b}) ` B"
  proof
    fix X
    assume "X \<in> (\<lambda>b. {x \<in> A. f' x = b}) ` B"
    from this obtain b where X_eq: "X = {x \<in> A. f' x = b}" and "b \<in> B" by blast
    from assms(3, 4) have "\<And>x. f' x = b \<longleftrightarrow> f x = inv p b"
      by (auto simp add: permutes_inverses(1, 2))
    from \<open>p permutes B\<close> X_eq this have "X = {x \<in> A. f x = inv p b}"
      using Collect_cong by auto
    moreover from \<open>b \<in> B\<close> \<open>p permutes B\<close> have "inv p b \<in> B"
      by (simp add: permutes_in_image permutes_inv)
    ultimately show "X \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B" by blast
  qed
qed

subsection \<open>Additions to List Theory\<close>

text \<open>
The theorem @{thm [source] card_lists_length_eq} contains the superfluous assumption @{term "finite A"}.
Here, we derive that fact without that unnecessary assumption.
\<close>

lemma lists_length_eq_Suc_eq_image_Cons:
  "{xs. set xs \<subseteq> A \<and> length xs = Suc n} = (\<lambda>(x, xs). x#xs) ` (A \<times> {xs. set xs \<subseteq> A \<and> length xs = n})"
  (is "?A = ?B")
proof
  show "?A \<subseteq> ?B"
  proof
    fix xs
    assume "xs \<in> ?A"
    from this show "xs \<in> ?B" by (cases xs) auto
  qed
next
  show "?B \<subseteq> ?A" by auto
qed

lemma lists_length_eq_Suc_eq_empty_iff:
  "{xs. set xs \<subseteq> A \<and> length xs = Suc n} = {} \<longleftrightarrow> A = {}"
proof (induct n)
  case 0
  have "{xs. set xs \<subseteq> A \<and> length xs = Suc 0} = {x#[] |x. x \<in> A}"
  proof
    show "{[x] |x. x \<in> A} \<subseteq> {xs. set xs \<subseteq> A \<and> length xs = Suc 0}" by auto
  next
    show "{xs. set xs \<subseteq> A \<and> length xs = Suc 0} \<subseteq> {[x] |x. x \<in> A}"
    proof
      fix xs
      assume "xs \<in> {xs. set xs \<subseteq> A \<and> length xs = Suc 0}"
      from this have "set xs \<subseteq> A \<and> length xs = Suc 0" by simp
      from this have "\<exists>x. xs = [x] \<and> x \<in> A"
        by (metis Suc_length_conv insert_subset length_0_conv list.set(2))
      from this show "xs \<in> {[x] |x. x \<in> A}" by simp
    qed
  qed
  then show ?case by simp
next
  case (Suc n)
  from this show ?case by (auto simp only: lists_length_eq_Suc_eq_image_Cons)
qed

lemma lists_length_eq_eq_empty_iff:
  "{xs. set xs \<subseteq> A \<and> length xs = n} = {} \<longleftrightarrow> (A = {} \<and> n > 0)"
proof (cases n)
  case 0
  then show ?thesis by auto
next
  case (Suc n)
  then show ?thesis by (auto simp only: lists_length_eq_Suc_eq_empty_iff)
qed

lemma finite_lists_length_eq_iff:
  "finite {xs. set xs \<subseteq> A \<and> length xs = n} \<longleftrightarrow> (finite A \<or> n = 0)"
proof
  assume "finite {xs. set xs \<subseteq> A \<and> length xs = n}"
  from this show "finite A \<or> n = 0"
  proof (induct n)
    case 0
    then show ?case by simp
  next
    case (Suc n)
    have "inj (\<lambda>(x, xs). x#xs)"
      by (auto intro: inj_onI)
    from this Suc(2) have "finite (A \<times> {xs. set xs \<subseteq> A \<and> length xs = n})"
      using finite_imageD inj_on_subset subset_UNIV lists_length_eq_Suc_eq_image_Cons[of A n]
      by fastforce
    from this have "finite A"
      by (cases "A = {}")
        (auto simp only: lists_length_eq_eq_empty_iff dest: finite_cartesian_productD1)
    from this show ?case by auto
  qed
next
  assume "finite A \<or> n = 0"
  from this show "finite {xs. set xs \<subseteq> A \<and> length xs = n}"
    by (auto intro: finite_lists_length_eq)
qed

lemma card_lists_length_eq:
  shows "card {xs. set xs \<subseteq> B \<and> length xs = n} = card B ^ n"
proof cases
  assume "finite B"
  then show ?thesis by (rule card_lists_length_eq)
next
  assume "infinite B"
  then show ?thesis
  proof cases
    assume "n = 0"
    from this have "{xs. set xs \<subseteq> B \<and> length xs = n} = {[]}" by auto
    from this \<open>n = 0\<close> show ?thesis by simp
  next
    assume "n \<noteq> 0"
    from this \<open>infinite B\<close> have "infinite {xs. set xs \<subseteq> B \<and> length xs = n}"
      by (simp add: finite_lists_length_eq_iff)
    from this \<open>infinite B\<close> show ?thesis by auto
  qed
qed

subsection \<open>Additions to Disjoint Set Theory\<close>

lemma bij_betw_congI:
  assumes "bij_betw f A A'"
  assumes "\<forall>a \<in> A. f a = g a"
  shows "bij_betw g A A'"
using assms bij_betw_cong by fastforce

lemma disjoint_family_onI[intro]:
  assumes "\<And>m n. m \<in> S \<Longrightarrow> n \<in> S \<Longrightarrow> m \<noteq> n \<Longrightarrow> A m \<inter> A n = {}"
  shows "disjoint_family_on A S"
using assms unfolding disjoint_family_on_def by simp

text \<open>
The following lemma is not needed for this development, but is useful
and could be moved to Disjoint Set theory or Equiv Relation theory if
translated from set partitions to equivalence relations.
\<close>

lemma infinite_partition_on:
  assumes "infinite A"
  shows "infinite {P. partition_on A P}"
proof -
  from \<open>infinite A\<close> obtain x where "x \<in> A"
    by (meson finite.intros(1) finite_subset subsetI)
  from \<open>infinite A\<close> have "infinite (A - {x})"
    by (simp add: infinite_remove)
  define singletons_except_one
    where "singletons_except_one = (\<lambda>a'. (\<lambda>a. if a = a' then {a, x} else {a}) ` (A - {x}))"
  have "infinite (singletons_except_one ` (A - {x}))"
  proof -
    have "inj_on singletons_except_one (A - {x})"
      unfolding singletons_except_one_def by (rule inj_onI) auto
    from \<open>infinite (A - {x})\<close> this show ?thesis
      using finite_imageD by blast
  qed
  moreover have "singletons_except_one ` (A - {x}) \<subseteq> {P. partition_on A P}"
  proof
    fix P
    assume "P \<in> singletons_except_one ` (A - {x})"
    from this obtain a' where "a' \<in> A - {x}" and P: "P = singletons_except_one a'" by blast
    have "partition_on A ((\<lambda>a. if a = a' then {a, x} else {a}) ` (A - {x}))"
      using \<open>x \<in> A\<close> \<open>a' \<in> A - {x}\<close> by (auto intro: partition_onI)
    from this have "partition_on A P"
      unfolding P singletons_except_one_def .
    from this show "P \<in> {P. partition_on A P}" ..
  qed
  ultimately show ?thesis by (simp add: infinite_super)
qed

lemma finitely_many_partition_on_iff:
  "finite {P. partition_on A P} \<longleftrightarrow> finite A"
using finitely_many_partition_on infinite_partition_on by blast

subsection \<open>Additions to Multiset Theory\<close>

lemma mset_set_subseteq_mset_set:
  assumes "finite B" "A \<subseteq> B"
  shows "mset_set A \<subseteq># mset_set B"
proof -
  from \<open>A \<subseteq> B\<close> \<open>finite B\<close> have "finite A" using finite_subset by blast
  {
    fix x
    have "count (mset_set A) x \<le> count (mset_set B) x"
      using \<open>finite A\<close> \<open>finite B\<close> \<open>A \<subseteq> B\<close>
      by (metis count_mset_set(1, 3) eq_iff subsetCE zero_le_one)
  }
  from this show "mset_set A \<subseteq># mset_set B"
    using mset_subset_eqI by blast
qed

lemma mset_set_set_mset:
  assumes "M \<subseteq># mset_set A"
  shows "mset_set (set_mset M) = M"
proof -
  {
    fix x
    from \<open>M \<subseteq># mset_set A\<close> have "count M x \<le> count (mset_set A) x"
      by (simp add: mset_subset_eq_count)
    from this have "count (mset_set (set_mset M)) x = count M x"
      by (metis count_eq_zero_iff count_greater_eq_one_iff count_mset_set
        dual_order.antisym dual_order.trans finite_set_mset)
  }
  from this show ?thesis by (simp add: multiset_eq_iff)
qed

lemma mset_set_set_mset':
  assumes "\<forall>x. count M x \<le> 1"
  shows "mset_set (set_mset M) = M"
proof -
  {
    fix x
    from assms have "count M x = 0 \<or> count M x = 1" by (auto elim: le_SucE)
    from this have "count (mset_set (set_mset M)) x = count M x"
      by (metis count_eq_zero_iff count_mset_set(1,3) finite_set_mset)
  }
  from this show ?thesis by (simp add: multiset_eq_iff)
qed

lemma card_set_mset:
  assumes "M \<subseteq># mset_set A"
  shows "card (set_mset M) = size M"
using assms
by (metis mset_set_set_mset size_mset_set)

lemma card_set_mset':
  assumes "\<forall>x. count M x \<le> 1"
  shows "card (set_mset M) = size M"
using assms
by (metis mset_set_set_mset' size_mset_set)

lemma count_mset_set_leq:
  assumes "finite A"
  shows "count (mset_set A) x \<le> 1"
using assms by (metis count_mset_set(1,3) eq_iff zero_le_one)

lemma count_mset_set_leq':
  assumes "finite A"
  shows "count (mset_set A) x \<le> Suc 0"
using assms count_mset_set_leq by fastforce

lemma msubset_mset_set_iff:
  assumes "finite A"
  shows "set_mset M \<subseteq> A \<and> (\<forall>x. count M x \<le> 1) \<longleftrightarrow> (M \<subseteq># mset_set A)"
proof
  assume "set_mset M \<subseteq> A \<and> (\<forall>x. count M x \<le> 1)"
  from this assms show "M \<subseteq># mset_set A"
    by (metis count_inI count_mset_set(1) le0 mset_subset_eqI subsetCE)
next
  assume "M \<subseteq># mset_set A"
  from this assms have "set_mset M \<subseteq> A"
    using mset_subset_eqD by fastforce
  moreover {
    fix x
    from \<open>M \<subseteq># mset_set A\<close> have "count M x \<le> count (mset_set A) x"
      by (simp add: mset_subset_eq_count)
    from this \<open>finite A\<close> have "count M x \<le> 1"
      by (meson count_mset_set_leq le_trans)
  }
  ultimately show "set_mset M \<subseteq> A \<and> (\<forall>x. count M x \<le> 1)" by simp
qed

lemma image_mset_fun_upd:
  assumes "x \<notin># M"
  shows "image_mset (f(x := y)) M = image_mset f M"
using assms by (induct M) auto

subsection \<open>Additions to Number Partitions Theory\<close>

lemma Partition_diag:
  shows "Partition n n = 1"
by (cases n) (auto simp only: Partition_diag Partition.simps(1))

subsection \<open>Cardinality Theorems with Iverson Function\<close>

definition iverson :: "bool \<Rightarrow> nat"
where
  "iverson b = (if b then 1 else 0)"

lemma card_partition_on_size1_eq_iverson:
  assumes "finite A"
  shows "card {P. partition_on A P \<and> card P \<le> k \<and> (\<forall>X\<in>P. card X = 1)} = iverson (card A \<le> k)"
proof (cases "card A \<le> k")
  case True
  from this \<open>finite A\<close> show ?thesis
    unfolding iverson_def
    using card_partition_on_size1_eq_1 by fastforce
next
  case False
  from this \<open>finite A\<close> show ?thesis
    unfolding iverson_def
    using card_partition_on_size1_eq_0 by fastforce
qed

lemma card_number_partitions_with_only_parts_1:
  "card {N. (\<forall>n. n\<in># N \<longrightarrow> n = 1) \<and> number_partition n N \<and> size N \<le> x} = iverson (n \<le> x)"
proof -
  show ?thesis
  proof cases
    assume "n \<le> x"
    from this show ?thesis
      using card_number_partitions_with_only_parts_1_eq_1
      unfolding iverson_def by auto
  next
    assume "\<not> n \<le> x"
    from this show ?thesis
      using card_number_partitions_with_only_parts_1_eq_0
      unfolding iverson_def by auto
  qed
qed

end
