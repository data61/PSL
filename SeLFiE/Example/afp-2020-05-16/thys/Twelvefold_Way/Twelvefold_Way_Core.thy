(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Main Observations on Operations and Permutations\<close>

theory Twelvefold_Way_Core
imports Preliminaries
begin

subsection \<open>Range Multiset\<close>

subsubsection \<open>Existence of a Suitable Finite Function\<close>

lemma obtain_function:
  assumes "finite A"
  assumes "size M = card A"
  shows "\<exists>f. image_mset f (mset_set A) = M"
using assms
proof (induct arbitrary: M rule: finite_induct)
  case empty
  from this show ?case by simp
next
  case (insert x A)
  from insert(1,2,4) have "size M > 0"
    by (simp add: card_gt_0_iff)
  from this obtain y where "y \<in># M"
    using gr0_implies_Suc size_eq_Suc_imp_elem by blast
  from insert(1,2,4) this have "size (M - {#y#}) = card A"
    by (simp add: Diff_insert_absorb card_Diff_singleton_if insertI1 size_Diff_submset)
  from insert.hyps this obtain f' where "image_mset f' (mset_set A) = M - {#y#}" by blast
  from this have "image_mset (f'(x := y)) (mset_set (insert x A)) = M"
    using \<open>finite A\<close> \<open>x \<notin> A\<close> \<open>y \<in># M\<close> by (simp add: image_mset_fun_upd)
  from this show ?case by blast
qed

lemma obtain_function_on_ext_funcset:
  assumes "finite A"
  assumes "size M = card A"
  shows "\<exists>f \<in> A \<rightarrow>\<^sub>E set_mset M. image_mset f (mset_set A) = M"
proof -
  obtain f where range_eq_M: "image_mset f (mset_set A) = M"
    using obtain_function \<open>finite A\<close> \<open>size M = card A\<close> by blast
  let ?f = "\<lambda>x. if x \<in> A then f x else undefined"
  have "?f \<in> A \<rightarrow>\<^sub>E set_mset M"
    using range_eq_M \<open>finite A\<close> by auto
  moreover have "image_mset ?f (mset_set A) = M"
    using range_eq_M \<open>finite A\<close> by (auto intro: multiset.map_cong0)
  ultimately show ?thesis by auto
qed

subsubsection \<open>Existence of Permutation\<close>

lemma image_mset_eq_implies_bij_betw:
  fixes f :: "'a1 \<Rightarrow> 'b" and f' :: "'a2 \<Rightarrow> 'b"
  assumes "finite A" "finite A'"
  assumes mset_eq: "image_mset f (mset_set A) = image_mset f' (mset_set A')"
  obtains bij where "bij_betw bij A A'" and "\<forall>x\<in>A. f x = f' (bij x)"
proof -
  from \<open>finite A\<close> have [simp]: "finite {a \<in> A. f a = (b::'b)}" for b by auto
  from \<open>finite A'\<close> have [simp]: "finite {a \<in> A'. f' a = (b::'b)}" for b by auto
  have "f ` A = f' ` A'"
  proof -
    have "f ` A = f ` (set_mset (mset_set A))" using \<open>finite A\<close> by simp
    also have "\<dots> = f' ` (set_mset (mset_set A'))"
      by (metis mset_eq multiset.set_map)
    also have "\<dots> = f' ` A'" using \<open>finite A'\<close> by simp
    finally show ?thesis .
  qed
  have "\<forall>b\<in>(f ` A). \<exists>bij. bij_betw bij {a \<in> A. f a = b} {a \<in> A'. f' a = b}"
  proof
    fix b
    from mset_eq have
      "count (image_mset f (mset_set A)) b = count (image_mset f' (mset_set A')) b" by simp
    from this have "card {a \<in> A. f a = b} = card {a \<in> A'. f' a = b}"
      using \<open>finite A\<close> \<open>finite A'\<close>
      by (simp add: count_image_mset_eq_card_vimage)
    from this show "\<exists>bij. bij_betw bij {a \<in> A. f a = b} {a \<in> A'. f' a = b}"
      by (intro finite_same_card_bij) simp_all
  qed
  hence "\<exists>bij. \<forall>b\<in>f ` A. bij_betw (bij b) {a \<in> A. f a = b} {a \<in> A'. f' a = b}"
    by (rule bchoice)
  then guess bij .. note bij = this
  define bij' where "bij' = (\<lambda>a. bij (f a) a)"
  have "bij_betw bij' A A'"
  proof -
    have "disjoint_family_on (\<lambda>i. {a \<in> A'. f' a = i}) (f ` A)"
      unfolding disjoint_family_on_def by auto
    moreover have "bij_betw (\<lambda>a. bij (f a) a) {a \<in> A. f a = b} {a \<in> A'. f' a = b}" if b: "b \<in> f ` A" for b
      using bij b by (subst bij_betw_cong[where g="bij b"]) auto
    ultimately have "bij_betw (\<lambda>a. bij (f a) a) (\<Union>b\<in>f ` A. {a \<in> A. f a = b}) (\<Union>b\<in>f ` A. {a \<in> A'. f' a = b})"
      by (rule bij_betw_UNION_disjoint)
    moreover have "(\<Union>b\<in>f ` A. {a \<in> A. f a = b}) = A" by auto
    moreover have "(\<Union>b\<in>f ` A. {a \<in> A'. f' a = b}) = A'" using \<open>f ` A = f' ` A'\<close> by auto
    ultimately show "bij_betw bij' A A'"
      unfolding bij'_def by (subst bij_betw_cong[where g="(\<lambda>a. bij (f a) a)"]) auto
  qed
  moreover from bij have "\<forall>x\<in>A. f x = f' (bij' x)"
    unfolding bij'_def using bij_betwE by fastforce
  ultimately show ?thesis by (rule that)
qed

lemma image_mset_eq_implies_permutes:
  fixes f :: "'a \<Rightarrow> 'b"
  assumes "finite A"
  assumes mset_eq: "image_mset f (mset_set A) = image_mset f' (mset_set A)"
  obtains p where "p permutes A" and "\<forall>x\<in>A. f x = f' (p x)"
proof -
  from assms obtain b where "bij_betw b A A" and "\<forall>x\<in>A. f x = f' (b x)"
    using image_mset_eq_implies_bij_betw by blast
  define p where "p = (\<lambda>a. if a \<in> A then b a else a)"
  have "p permutes A"
  proof (rule bij_imp_permutes)
    show "bij_betw p A A"
      unfolding p_def by (simp add: \<open>bij_betw b A A\<close> bij_betw_cong)
  next
    fix x
    assume "x \<notin> A"
    from this show "p x = x"
      unfolding p_def by simp
  qed
  moreover from \<open>\<forall>x\<in>A. f x = f' (b x)\<close> have "\<forall>x\<in>A. f x = f' (p x)"
    unfolding p_def by simp
  ultimately show ?thesis by (rule that)
qed

subsection \<open>Domain Partition\<close>

subsubsection \<open>Existence of a Suitable Finite Function\<close>

lemma obtain_function_with_partition:
  assumes "finite A" "finite B"
  assumes "partition_on A P"
  assumes "card P \<le> card B"
  shows "\<exists>f \<in> A \<rightarrow>\<^sub>E B. (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = P"
proof -
  obtain g' where "bij_betw g' P (g' ` P)" and "g' ` P \<subseteq> B"
    by (meson assms card_le_inj finite_elements inj_on_imp_bij_betw)
  define f where "\<And>a. f a = (if a \<in> A then g' (THE X. a \<in> X \<and> X \<in> P) else undefined)"
  have "f \<in> A \<rightarrow>\<^sub>E B"
  unfolding f_def
  using \<open>g' ` P \<subseteq> B\<close> assms(3) partition_on_the_part_mem by fastforce
  moreover have "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = P"
  proof
    show "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} \<subseteq> P"
    proof
      fix X
      assume X:"X \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
      from this obtain b where "b \<in> B" and "X = {x' \<in> A. f x' = b}" by auto
      from this X obtain a where "a \<in> A" and "a \<in> X" and "f a = b" by blast
      have "(THE X. a \<in> X \<and> X \<in> P) \<in> P"
        using \<open>a \<in> A\<close> \<open>partition_on A P\<close> by (simp add: partition_on_the_part_mem)
      from \<open>X = {x' \<in> A. f x' = b}\<close> have X_eq1: "X = {x' \<in> A. g' (THE X. x' \<in> X \<and> X \<in> P) = b}"
        unfolding f_def by auto
      also have "\<dots> = {x' \<in> A. (THE X. x' \<in> X \<and> X \<in> P) = inv_into P g' b}"
      proof -
        {
          fix x'
          assume "x' \<in> A"
          have "(THE X. x' \<in> X \<and> X \<in> P) \<in> P"
            using \<open>partition_on A P\<close> \<open>x' \<in> A\<close> by (simp add: partition_on_the_part_mem)
          from X_eq1 \<open>a \<in> X\<close> have "g' (THE X. a \<in> X \<and> X \<in> P) = b"
            unfolding f_def by auto
          from this \<open>(THE X. a \<in> X \<and> X \<in> P) \<in> P\<close> have "b \<in> g' ` P" by auto
          have "(g' (THE X. x' \<in> X \<and> X \<in> P) = b) \<longleftrightarrow> ((THE X. x' \<in> X \<and> X \<in> P) = inv_into P g' b)"
          proof -
            from \<open>(THE X. x' \<in> X \<and> X \<in> P) \<in> P\<close>
            have "(g' (THE X. x' \<in> X \<and> X \<in> P) = b) \<longleftrightarrow> (inv_into P g' (g' (THE X. x' \<in> X \<and> X \<in> P)) = inv_into P g' b)"
              using \<open>b \<in> g' ` P\<close> by (auto intro: inv_into_injective)
            moreover have "inv_into P g' (g' (THE X. x' \<in> X \<and> X \<in> P)) = (THE X. x' \<in> X \<and> X \<in> P)"
              using \<open>bij_betw g' P (g' ` P)\<close> \<open>(THE X. x' \<in> X \<and> X \<in> P) \<in> P\<close>
              by (simp add: bij_betw_inv_into_left)
            ultimately show ?thesis by simp
          qed
        }
        from this show ?thesis by auto
      qed
      finally have X_eq: "X = {x' \<in> A. (THE X. x' \<in> X \<and> X \<in> P) = inv_into P g' b}" .
      moreover have "inv_into P g' b \<in> P"
      proof -
        from X_eq have eq: "inv_into P g' b = (THE X. a \<in> X \<and> X \<in> P)"
          using \<open>a \<in> X\<close> \<open>a \<in> A\<close> by auto
        from this show ?thesis
          using \<open>(THE X. a \<in> X \<and> X \<in> P) \<in> P\<close> by simp
      qed
      ultimately have "X = inv_into P g' b"
        using partition_on_all_in_part_eq_part[OF \<open>partition_on A P\<close>] by blast
      from this \<open>inv_into P g' b \<in> P\<close> show "X \<in> P" by blast
    qed
  next
    show "P \<subseteq> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
    proof
      fix X
      assume "X \<in> P"
      from assms(3) this have "X \<noteq> {}"
        by (auto elim: partition_onE)
      moreover have "X \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B"
      proof
        show "g' X \<in> B"
          using \<open>X \<in> P\<close> \<open>g' ` P \<subseteq> B\<close> by blast
        show "X = {x \<in> A. f x = g' X}"
        proof
          show "X \<subseteq> {x \<in> A. f x = g' X}"
          proof
            fix x
            assume "x \<in> X"
            from this have "x \<in> A"
              using \<open>X \<in> P\<close> assms(3) by (fastforce elim: partition_onE)
            have "(THE X. x \<in> X \<and> X \<in> P) = X"
              using \<open>X \<in> P\<close> \<open>x \<in> X\<close> assms(3) partition_on_the_part_eq by fastforce
            from this \<open>x \<in> A\<close> have "f x = g' X"
              unfolding f_def by auto
            from this \<open>x \<in> A\<close> show "x \<in> {x \<in> A. f x = g' X}" by auto
          qed
        next
          show "{x \<in> A. f x = g' X} \<subseteq> X"
          proof
            fix x
            assume "x \<in> {x \<in> A. f x = g' X}"
            from this have "x \<in> A" and g_eq: "g' (THE X. x \<in> X \<and> X \<in> P) = g' X"
              unfolding f_def by auto
            from \<open>x \<in> A\<close> have "(THE X. x \<in> X \<and> X \<in> P) \<in> P"
              using assms(3) by (simp add: partition_on_the_part_mem)
            from this g_eq have "(THE X. x \<in> X \<and> X \<in> P) = X"
              using \<open>X \<in> P\<close> \<open>bij_betw g' P (g' ` P)\<close>
              by (metis bij_betw_inv_into_left)
            from this \<open>x \<in> A\<close> assms(3) show "x \<in> X"
              using partition_on_in_the_unique_part by fastforce
          qed
        qed
      qed
      ultimately show "X \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
        by auto
    qed
  qed
  ultimately show ?thesis by blast
qed

subsubsection \<open>Equality under Permutation Application\<close>

lemma permutes_implies_inv_image_on_eq:
  assumes "p permutes B"
  shows "(\<lambda>b. {x \<in> A. p (f x) = b}) ` B = (\<lambda>b. {x \<in> A. f x = b}) ` B"
proof -
  have "\<forall>b \<in> B. \<forall>x \<in> A. p (f x) = b \<longleftrightarrow> f x = inv p b"
    using \<open>p permutes B\<close> by (auto simp add: permutes_inverses)
  from this have "(\<lambda>b. {x \<in> A. p (f x) = b}) ` B = (\<lambda>b. {x \<in> A. f x = inv p b}) ` B"
    using image_cong by blast
  also have "\<dots> = (\<lambda>b. {x \<in> A. f x = b}) ` inv p ` B"
    by (auto simp add: image_comp)
  also have "\<dots> = (\<lambda>b. {x \<in> A. f x = b}) ` B"
    by (simp add: \<open>p permutes B\<close> permutes_inv permutes_image)
  finally show ?thesis .
qed

subsubsection \<open>Existence of Permutation\<close>

lemma the_elem:
  assumes "f \<in> A \<rightarrow>\<^sub>E B" "f' \<in> A \<rightarrow>\<^sub>E B"
  assumes partitions_eq: "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}"
  assumes "x \<in> A"
  shows "the_elem (f ` {xa \<in> A. f' xa = f' x}) = f x"
proof -
  from \<open>x \<in> A\<close> have x: "x \<in> {x' \<in> A. f' x' = f' x}" by blast
  have "f' x \<in> B"
    using \<open>x \<in> A\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> by blast
  from this have "{x' \<in> A. f' x' = f' x} \<in> (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}"
    using \<open>x \<in> A\<close> by blast
  from this have "{x' \<in> A. f' x' = f' x} \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
    using partitions_eq by blast
  from this obtain b where eq: "{x' \<in> A. f' x' = f' x} = {x' \<in> A. f x' = b}" by blast
  also from x this show "the_elem (f ` {x' \<in> A. f' x' = f' x}) = f x"
    by (metis (mono_tags, lifting) empty_iff mem_Collect_eq the_elem_image_unique)
qed

lemma the_elem_eq:
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  assumes "b \<in> f ` A"
  shows "the_elem (f ` {x' \<in> A. f x' = b}) = b"
proof -
  from \<open>b \<in> f ` A\<close> obtain a where "a \<in> A" and "b = f a" by blast
  from this show "the_elem (f ` {x' \<in> A. f x' = b}) = b"
    using the_elem[OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>] by simp
qed

lemma partitions_eq_implies:
  assumes "f \<in> A \<rightarrow>\<^sub>E B" "f' \<in> A \<rightarrow>\<^sub>E B"
  assumes partitions_eq: "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}"
  assumes "x \<in> A" "x' \<in> A"
  assumes "f x = f x'"
  shows "f' x = f' x'"
proof -
  have "f x \<in> B" and "x \<in> {a \<in> A. f a = f x}" and "x' \<in> {a \<in> A. f a = f x}"
    using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>x \<in> A\<close> \<open>x' \<in> A\<close> \<open>f x = f x'\<close> by auto
  moreover have "{a \<in> A. f a = f x} \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
    using \<open>f x \<in> B\<close> \<open>x \<in> {a \<in> A. f a = f x}\<close> by auto
  ultimately obtain b where "x \<in> {a \<in> A. f' a = b}" and "x' \<in> {a \<in> A. f' a = b}"
    using partitions_eq by (metis (no_types, lifting) Diff_iff imageE)
  from this show "f' x = f' x'" by auto
qed

lemma card_domain_partitions:
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  assumes "finite B"
  shows "card ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) = card (f ` A)"
proof -
  note [simp] = the_elem_eq[OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close>]
  have "bij_betw (\<lambda>X. the_elem (f ` X)) ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) (f ` A)"
  proof (rule bij_betw_imageI)
    show "inj_on (\<lambda>X. the_elem (f ` X)) ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})"
    proof (rule inj_onI)
      fix X X'
      assume X: "X \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
      assume X': "X' \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
      assume eq: "the_elem (f ` X) = the_elem (f ` X')"
      from X obtain b where "b \<in> B" and X_eq: "X = {x \<in> A. f x = b}" by blast
      from X this have "b \<in> f ` A"
        using Collect_empty_eq Diff_iff image_iff insertCI by auto
      from X' obtain b' where "b' \<in> B" and X'_eq: "X' = {x \<in> A. f x = b'}" by blast
      from X' this have "b' \<in> f ` A"
        using Collect_empty_eq Diff_iff image_iff insertCI by auto
      from X_eq X'_eq eq \<open>\<And>b. b \<in> f ` A \<Longrightarrow> the_elem (f ` {x' \<in> A. f x' = b}) = b\<close> \<open>b \<in> f ` A\<close> \<open>b' \<in> f ` A\<close>
        have "b = b'" by auto
      from this show "X = X'"
        using X_eq X'_eq by simp
    qed
    show "(\<lambda>X. the_elem (f ` X)) ` ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) = f ` A"
    proof
      show "(\<lambda>X. the_elem (f ` X)) ` ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}) \<subseteq> f ` A"
        using \<open>\<And>b. b \<in> f ` A \<Longrightarrow> the_elem (f ` {x' \<in> A. f x' = b}) = b\<close> by auto 
    next
      show "f ` A \<subseteq> (\<lambda>X. the_elem (f ` X)) ` ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})"
      proof
        fix b
        assume "b \<in> f ` A"
        from this have "b = the_elem (f ` {x \<in> A. f x = b})"
          using \<open>\<And>b. b \<in> f ` A \<Longrightarrow> the_elem (f ` {x' \<in> A. f x' = b}) = b\<close> by auto
        moreover from \<open>b \<in> f ` A\<close> have " {x \<in> A. f x = b} \<in> (\<lambda>b. {x \<in> A. f x = b}) ` B - {{}}"
          using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> by auto
        ultimately show "b \<in> (\<lambda>X. the_elem (f ` X)) ` ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})" ..
      qed
    qed
  qed
  from this show ?thesis by (rule bij_betw_same_card)
qed

lemma partitions_eq_implies_permutes:
  assumes "f \<in> A \<rightarrow>\<^sub>E B" "f' \<in> A \<rightarrow>\<^sub>E B"
  assumes "finite B"
  assumes partitions_eq: "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}"
  shows "\<exists>p. p permutes B \<and> (\<forall>x\<in>A. f x = p (f' x))"
proof -
  have card_eq: "card (f' ` A) = card (f ` A)"
    using card_domain_partitions[OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>finite B\<close>]
    using card_domain_partitions[OF \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> \<open>finite B\<close>]
    using partitions_eq by simp
  have "f' ` A \<subseteq> B" "f ` A \<subseteq> B"
    using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> by auto
  from this card_eq have "card (B - f' ` A) = card (B - f ` A)"
    using \<open>finite B\<close> by (auto simp add: card_Diff_subset finite_subset)
  from this obtain p' where "bij_betw p' (B - f' ` A) (B - f ` A)"
    using \<open>finite B\<close> by (metis finite_same_card_bij finite_Diff)
  from this have "p' ` (B - f' ` A) = (B - f ` A)"
    by (simp add: bij_betw_imp_surj_on)
  define p where "\<And>b. p b = (if b \<in> B then
    (if b \<in> f' ` A then the_elem (f ` {x \<in> A. f' x = b}) else p' b) else b)"
  have "\<forall>x\<in>A. f x = p (f' x)"
  proof
    fix x
    assume "x \<in> A"
    from this partitions_eq have "the_elem (f ` {xa \<in> A. f' xa = f' x}) = f x"
      using the_elem[OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close>] by auto
    from this show "f x = p (f' x)"
      using \<open>x \<in> A\<close> p_def \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> by auto
  qed
  moreover have "p permutes B"
  proof (rule bij_imp_permutes)
    let ?invp = "\<lambda>b. if b \<in> f ` A then the_elem (f' ` {x \<in> A. f x = b}) else b"
    note [simp] = the_elem[OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> partitions_eq]
    show "bij_betw p B B"
    proof (rule bij_betw_imageI)
      show "p ` B = B"
      proof
        have "(\<lambda>b. the_elem (f ` {x \<in> A. f' x = b})) ` (f' ` A) \<subseteq> B"
          using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> by auto
        from \<open>p' ` (B - f' ` A) = (B - f ` A)\<close> this show "p ` B \<subseteq> B"
          unfolding p_def \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> by force
      next
        show "B \<subseteq> p ` B"
        proof
          fix b
          assume "b \<in> B"
          show "b \<in> p ` B"
          proof (cases "b \<in> f ` A")
            assume "b \<notin> f ` A"
            note \<open>p' ` (B - f' ` A) = (B - f ` A)\<close>
            from this \<open>b \<in> B\<close> \<open>b \<notin> f ` A\<close> show ?thesis
              unfolding p_def by auto
          next
            assume "b \<in> f ` A"
            from this \<open>\<forall>x\<in>A. f x = p (f' x)\<close> \<open>b \<in> B\<close> show ?thesis
              using \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> by auto
          qed
        qed
      qed
    next
      show "inj_on p B"
      proof (rule inj_onI)
        fix b b'
        assume "b \<in> B" "b' \<in> B" "p b = p b'"
        have "b \<in> f' ` A \<longleftrightarrow> b' \<in> f' ` A"
        proof -
          have "b \<in> f' ` A \<longleftrightarrow> p b \<in> f ` A"
            unfolding p_def using \<open>b \<in> B\<close> \<open>p' ` (B - f' ` A) = B - f ` A\<close> by auto
          also have "p b \<in> f ` A \<longleftrightarrow> p b' \<in> f ` A"
            using \<open>p b = p b'\<close> by simp
          also have "p b' \<in> f ` A \<longleftrightarrow> b' \<in> f' ` A"
            unfolding p_def using \<open>b' \<in> B\<close> \<open>p' ` (B - f' ` A) = B - f ` A\<close> by auto
          finally show ?thesis .
        qed
        from this have "(b \<in> f' ` A \<and> b' \<in> f' ` A) \<or> (b \<notin> f' ` A \<and> b' \<notin> f' ` A)" by blast
        from this show "b = b'"
        proof
          assume "b \<in> f' ` A \<and> b' \<in> f' ` A"
          from this obtain a a' where "a \<in> A" "b = f' a" and "a' \<in> A" "b' = f' a'" by auto
          from this \<open>b \<in> B\<close> \<open>b' \<in> B\<close> have "p b = f a" "p b' = f a'"
            unfolding p_def by auto
          from this \<open>p b = p b'\<close> have "f a = f a'" by simp
          from this have "f' a = f' a'"
            using partitions_eq_implies[OF \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> partitions_eq]
            using \<open>a \<in> A\<close> \<open>a' \<in> A\<close> by blast
          from this show "b = b'"
            using \<open>b' = f' a'\<close> \<open>b = f' a\<close> by simp
        next
          assume "b \<notin> f' ` A \<and> b' \<notin> f' ` A"
          from this \<open>b \<in> B\<close> \<open>b' \<in> B\<close> have "p b' = p' b'" "p b = p' b"
            unfolding p_def by auto
          from this \<open>p b = p b'\<close> have "p' b = p' b'" by simp
          moreover have "b \<in> B - f' ` A" "b' \<in> B - f' ` A"
            using \<open>b \<in> B\<close> \<open>b' \<in> B\<close> \<open>b \<notin> f' ` A \<and> b' \<notin> f' ` A\<close> by auto
          ultimately show "b = b'"
            using \<open>bij_betw p' _ _\<close> by (metis bij_betw_inv_into_left)
        qed
      qed
    qed
  next
    fix x
    assume "x \<notin> B"
    from this show "p x = x"
      using \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> p_def by auto
  qed
  ultimately show ?thesis by blast
qed

subsection \<open>Number Partition of Range\<close>

subsubsection \<open>Existence of a Suitable Finite Function\<close>

lemma obtain_partition:
  assumes "finite A"
  assumes "number_partition (card A) N"
  shows "\<exists>P. partition_on A P \<and> image_mset card (mset_set P) = N"
using assms
proof (induct N arbitrary: A)
  case empty
  from this have "A = {}"
    unfolding number_partition_def by auto
  from this have "partition_on A {}" by (simp add: partition_on_empty)
  moreover have "image_mset card (mset_set {}) = {#}" by simp
  ultimately show ?case by blast
next
  case (add x N)
  from add.prems(2) have "0 \<notin># add_mset x N" and "sum_mset (add_mset x N) = card A"
    unfolding number_partition_def by auto
  from this have "x \<le> card A" by auto
  from this obtain X where "X \<subseteq> A" and "card X = x"
    using subset_with_given_card_exists by auto
  from this have "X \<noteq> {}"
    using \<open>0 \<notin># add_mset x N\<close> \<open>finite A\<close> by auto
  have "sum_mset N = card (A - X)"
    using \<open>sum_mset (add_mset x N) = card A\<close> \<open>card X = x\<close> \<open>X \<subseteq> A\<close>
    by (metis add.commute add.prems(1) add_diff_cancel_right' card_Diff_subset infinite_super sum_mset.add_mset)
  from this \<open>0 \<notin># add_mset x N\<close> have "number_partition (card (A - X)) N"
    unfolding number_partition_def by auto
  from this obtain P where "partition_on (A - X) P" and eq_N: "image_mset card (mset_set P) = N"
    using add.hyps \<open>finite A\<close> by auto
  from \<open>partition_on (A - X) P\<close> have "finite P"
    using \<open>finite A\<close> finite_elements by blast
  from \<open>partition_on (A - X) P\<close> have "X \<notin> P"
    using \<open>X \<noteq> {}\<close> partition_onD1 by fastforce
  have "partition_on A (insert X P)"
    using \<open>partition_on (A - X) P\<close> \<open>X \<subseteq> A\<close> \<open>X \<noteq> {}\<close>
    by (rule partition_on_insert')
  moreover have "image_mset card (mset_set (insert X P)) = add_mset x N"
    using eq_N \<open>card X = x\<close> \<open>finite P\<close> \<open>X \<notin> P\<close> by simp
  ultimately show ?case by blast
qed

lemma obtain_extensional_function_from_number_partition:
  assumes "finite A" "finite B"
  assumes "number_partition (card A) N"
  assumes "size N \<le> card B"
  shows "\<exists>f\<in>A \<rightarrow>\<^sub>E B. image_mset (\<lambda>X. card X) (mset_set (((\<lambda>b. {x \<in> A. f x = b})) ` B - {{}})) = N"
proof -
  obtain P where "partition_on A P" and eq_N: "image_mset card (mset_set P) = N"
    using assms obtain_partition by blast
  from eq_N[symmetric] \<open>size N \<le> card B\<close> have "card P \<le> card B" by simp
  from \<open>partition_on A P\<close> this obtain f where "f \<in> A \<rightarrow>\<^sub>E B"
    and eq_P: "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = P"
    using obtain_function_with_partition[OF \<open>finite A\<close> \<open>finite B\<close>] by blast
  have "image_mset (\<lambda>X. card X) (mset_set (((\<lambda>b. {x \<in> A. f x = b})) ` B - {{}})) = N"
    using eq_P eq_N by simp
  from this \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> show ?thesis by auto
qed

subsubsection \<open>Equality under Permutation Application\<close>

lemma permutes_implies_multiset_of_partition_cards_eq:
  assumes "p\<^sub>A permutes A" "p\<^sub>B permutes B"
  shows "image_mset card (mset_set ((\<lambda>b. {x \<in> A. p\<^sub>B (f' (p\<^sub>A x)) = b}) ` B - {{}})) = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}))"
proof -
  have "inj_on ((`) (inv p\<^sub>A)) ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}})"
    by (meson \<open>p\<^sub>A permutes A\<close> inj_image_eq_iff inj_onI permutes_surj surj_imp_inj_inv)
  have "image_mset card (mset_set ((\<lambda>b. {x \<in> A. p\<^sub>B (f' (p\<^sub>A x)) = b}) ` B - {{}})) =
    image_mset card (mset_set ((\<lambda>X. inv p\<^sub>A ` X) ` ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}})))"
  proof -
    have "(\<lambda>b. {x \<in> A. p\<^sub>B (f' (p\<^sub>A x)) = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. f' (p\<^sub>A x) = b}) ` B - {{}}"
      using permutes_implies_inv_image_on_eq[OF \<open>p\<^sub>B permutes B\<close>] by metis
    also have "\<dots> = (\<lambda>b. inv p\<^sub>A ` {x \<in> A. f' x = b}) ` B - {{}}"
    proof -
      have "{x \<in> A. f' (p\<^sub>A x) = b} = inv p\<^sub>A ` {x \<in> A. f' x = b}" for b
      proof
        show "{x \<in> A. f' (p\<^sub>A x) = b} \<subseteq> inv p\<^sub>A ` {x \<in> A. f' x = b}"
        proof
          fix x
          assume "x \<in> {x \<in> A. f' (p\<^sub>A x) = b}"
          from this have "x \<in> A" "f' (p\<^sub>A x) = b" by auto
          moreover from this \<open>p\<^sub>A permutes A\<close> have "p\<^sub>A x \<in> A" by (simp add: permutes_in_image)
          moreover from \<open>p\<^sub>A permutes A\<close> have "x = inv p\<^sub>A (p\<^sub>A x)"
            using permutes_inverses(2) by fastforce
          ultimately show "x \<in> inv p\<^sub>A ` {x \<in> A. f' x = b}" by auto
        qed
      next
        show "inv p\<^sub>A ` {x \<in> A. f' x = b} \<subseteq> {x \<in> A. f' (p\<^sub>A x) = b}"
        proof
          fix x
          assume "x \<in> inv p\<^sub>A ` {x \<in> A. f' x = b}"
          from this obtain x' where x: "x = inv p\<^sub>A x'" "x' \<in> A" "f' x' = b" by auto
          from this \<open>p\<^sub>A permutes A\<close> have "x \<in> A" by (simp add: permutes_in_image permutes_inv)
          from \<open>x = inv p\<^sub>A x'\<close> \<open>f' x' = b\<close> have "f' (p\<^sub>A x) = b"
            using \<open>p\<^sub>A permutes A\<close> permutes_inverses(1) by fastforce
          from this \<open>x \<in> A\<close> show "x \<in> {x \<in> A. f' (p\<^sub>A x) = b}" by auto
        qed
      qed
      from this show ?thesis by blast
    qed
    also have "\<dots> = (\<lambda>X. inv p\<^sub>A ` X) ` ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}})" by auto
    finally show ?thesis by simp
  qed
  also have "\<dots> = image_mset (\<lambda>X. card (inv p\<^sub>A ` X)) (mset_set ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}))"
    using \<open>inj_on ((`) (inv p\<^sub>A)) ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}})\<close>
    by (simp only: image_mset_mset_set[symmetric] image_mset.compositionality) (meson comp_apply)
  also have "\<dots> = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}))"
    using \<open>p\<^sub>A permutes A\<close> by (simp add: card_image inj_on_inv_into permutes_surj)
  finally show ?thesis .
qed

subsubsection \<open>Existence of Permutation\<close>

lemma partition_implies_permutes:
  assumes "finite A"
  assumes "partition_on A P" "partition_on A P'"
  assumes "image_mset card (mset_set P') = image_mset card (mset_set P)"
  obtains p where "p permutes A" "P' = (\<lambda>X. p ` X) ` P"
proof -
  from \<open>partition_on A P\<close> \<open>partition_on A P'\<close> have "finite P" "finite P'"
    using \<open>finite A\<close> finite_elements by blast+
  from this \<open>image_mset card (mset_set P') = image_mset card (mset_set P)\<close>
  obtain bij where "bij_betw bij P P'" and "\<forall>X\<in>P. card X = card (bij X)"
    using image_mset_eq_implies_bij_betw by metis
  have "\<forall>X\<in>P. \<exists>p'. bij_betw p' X (bij X)"
  proof
    fix X
    assume "X \<in> P"
    from this have "X \<subseteq> A"
      using \<open>partition_on A P\<close> partition_onD1 by fastforce
    from this have "finite X"
      using \<open>finite A\<close> rev_finite_subset by blast
    from \<open>X \<in> P\<close> have "bij X \<in> P'"
      using \<open>bij_betw bij P P'\<close> bij_betwE by blast
    from this have "bij X \<subseteq> A"
      using \<open>partition_on A P'\<close> partition_onD1 by fastforce
    from this have "finite (bij X)"
      using \<open>finite A\<close> rev_finite_subset by blast
    from \<open>X \<in> P\<close> have "card X = card (bij X)"
      using \<open>\<forall>X\<in>P. card X = card (bij X)\<close> by blast
    from this show "\<exists>p'. bij_betw p' X (bij X)"
      using \<open>finite (bij X)\<close> \<open>finite X\<close> finite_same_card_bij by blast
  qed
  from this have "\<exists>p'. \<forall>X\<in>P. bij_betw (p' X) X (bij X)" by metis
  from this obtain p' where p': "\<forall>X\<in>P. bij_betw (p' X) X (bij X)" ..
  define p where "\<And>a. p a = (if a \<in> A then p' (THE X. a \<in> X \<and> X \<in> P) a else a)"
  have "p permutes A"
  proof -
    have "bij_betw p A A"
    proof -
      have "disjoint_family_on bij P"
      proof
        fix X X'
        assume XX': "X \<in> P" "X' \<in> P" "X \<noteq> X'"
        from this have "bij X \<in> P'" "bij X' \<in> P'"
          using \<open>bij_betw bij P P'\<close> bij_betwE by blast+
        moreover from XX' have "bij X \<noteq> bij X'"
          using \<open>bij_betw bij P P'\<close> by (metis bij_betw_inv_into_left)
        ultimately show "bij X \<inter> bij X' = {}"
          using \<open>partition_on A P'\<close> by (meson partition_onE)
      qed
      moreover have "bij_betw (\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) X (bij X)" if "X \<in> P" for X
      proof -
        from \<open>X \<in> P\<close> have "bij_betw (p' X) X (bij X)"
          using \<open>\<forall>X\<in>P. bij_betw (p' X) X (bij X)\<close> by blast
        moreover from \<open>X \<in> P\<close> have "\<forall>a\<in>X. (THE X. a \<in> X \<and> X \<in> P) = X"
          using \<open>partition_on A P\<close> partition_on_the_part_eq by fastforce
        ultimately show ?thesis by (auto intro: bij_betw_congI)
      qed
      ultimately have "bij_betw (\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) (\<Union>X\<in>P. X) (\<Union>X\<in>P. bij X)"
        by (rule bij_betw_UNION_disjoint)
      moreover have "(\<Union>X\<in>P. X) = A" "(\<Union>X\<in>P'. X) = A"
        using \<open>partition_on A P\<close> \<open>partition_on A P'\<close> partition_onD1 by auto
      moreover have "(\<Union>X\<in>P. bij X) = (\<Union>X\<in>P'. X)"
        using \<open>bij_betw bij P P'\<close> bij_betw_imp_surj_on by force
      ultimately have "bij_betw (\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) A A" by simp
      moreover have "\<forall>a \<in> A. p' (THE X. a \<in> X \<and> X \<in> P) a = p a"
        unfolding p_def by auto
      ultimately show ?thesis by (rule bij_betw_congI)
    qed
    moreover have "p x = x" if "x \<notin> A" for x
      using \<open>x \<notin> A\<close> p_def by auto
    ultimately show ?thesis by (rule bij_imp_permutes)
  qed
  moreover have "P' = (\<lambda>X. p ` X) ` P"
  proof
    show "P' \<subseteq> (\<lambda>X. p ` X) ` P"
    proof
      fix X
      assume "X \<in> P'"
      have in_P: "the_inv_into P bij X \<in> P"
        using \<open>X \<in> P'\<close> \<open>bij_betw bij P P'\<close> bij_betwE bij_betw_the_inv_into by blast
      have eq_X: "bij (the_inv_into P bij X) = X"
        using \<open>X \<in> P'\<close> \<open>bij_betw bij P P'\<close>
        by (meson f_the_inv_into_f_bij_betw)
      have "X = p ` (the_inv_into P bij X)"
      proof
        from in_P have "the_inv_into P bij X \<subseteq> A"
          using \<open>partition_on A P\<close> partition_onD1 by fastforce
        have "(\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` the_inv_into P bij X = X"
        proof
          show "(\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` the_inv_into P bij X \<subseteq> X"
          proof
            fix x
            assume "x \<in> (\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` the_inv_into P bij X"
            from this obtain a where a_in: "a \<in> the_inv_into P bij X"
              and x_eq: "x = p' (THE X. a \<in> X \<and> X \<in> P) a" by blast
            have "(THE X. a \<in> X \<and> X \<in> P) = the_inv_into P bij X"
              using a_in in_P \<open>partition_on A P\<close> partition_on_the_part_eq
              by fastforce
            from this x_eq have x_eq: "x = p' (the_inv_into P bij X) a"
              by auto
            from this have "x \<in> bij (the_inv_into P bij X)"
              using a_in in_P bij_betwE p' by blast
            from this eq_X show "x \<in> X" by blast
          qed
        next
          show "X \<subseteq> (\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` the_inv_into P bij X"
          proof
            fix x
            assume "x \<in> X"
            let ?X' = "the_inv_into P bij X"
            define x' where "x' = the_inv_into ?X' (p' ?X') x"
            from in_P p' eq_X have bij_betw: "bij_betw (p' ?X') ?X' X" by auto
            from bij_betw \<open>x \<in> X\<close> have "x' \<in> ?X'"
              unfolding x'_def
              using bij_betwE bij_betw_the_inv_into by blast
            from this in_P have "(THE X. x' \<in> X \<and> X \<in> P) = ?X'"
              using \<open>partition_on A P\<close> partition_on_the_part_eq by fastforce
            from this \<open>x \<in> X\<close> have "x = p' (THE X. x' \<in> X \<and> X \<in> P) x'"
              unfolding x'_def
              using bij_betw f_the_inv_into_f_bij_betw by fastforce
            from this \<open>x' \<in> ?X'\<close> show "x \<in> (\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` the_inv_into P bij X" ..
          qed
        qed
        from this \<open>the_inv_into P bij X \<subseteq> A\<close> show "X \<subseteq> p ` the_inv_into P bij X"
          unfolding p_def by auto
      next
        show "p ` the_inv_into P bij X \<subseteq> X"
        proof
          fix x
          assume "x \<in> p ` the_inv_into P bij X"
          from this obtain x' where "x = p x'" and "x' \<in> the_inv_into P bij X"
            by auto
          have "x' \<in> A"
            using \<open>x' \<in> the_inv_into P bij X\<close> assms(2) in_P partition_onD1 by fastforce
          have eq: "(THE X. x' \<in> X \<and> X \<in> P) = the_inv_into P bij X"
            using \<open>x' \<in> the_inv_into P bij X\<close> assms(2) in_P partition_on_the_part_eq by fastforce
          have p': "p' (the_inv_into P bij X) x' \<in> X"
            using \<open>x' \<in> the_inv_into P bij X\<close> bij_betwE eq_X in_P p' by blast
          from \<open>x = p x'\<close> \<open>x' \<in> A\<close> eq p' show "x \<in> X"
            unfolding p_def by auto
        qed
      qed
      moreover from \<open>X \<in> P'\<close> \<open>bij_betw bij P P'\<close> have "the_inv_into P bij X \<in> P"
        using bij_betwE bij_betw_the_inv_into by blast
      ultimately show "X \<in> (\<lambda>X. p ` X) ` P" ..
    qed
  next
    show "(\<lambda>X. p ` X) ` P \<subseteq> P'"
    proof
      fix X'
      assume "X' \<in> (\<lambda>X. p ` X) ` P"
      from this obtain X where X'_eq: "X' = p ` X" and "X \<in> P" ..
      from \<open>X \<in> P\<close> have "X \<subseteq> A"
        using assms(2) partition_onD1 by force
      from \<open>X \<in> P\<close> p' have bij: "bij_betw (p' X) X (bij X)" by auto
      have "p ` X \<in> P'"
      proof -
        from \<open>X \<in> P\<close> \<open>bij_betw bij P P'\<close> have "bij X \<in> P'"
          using bij_betwE by blast
        moreover have "(\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` X = bij X"
        proof
          show "(\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` X \<subseteq> bij X"
          proof
            fix x'
            assume "x' \<in> (\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` X"
            from this obtain x where "x \<in> X" and x'_eq: "x' = p' (THE X. x \<in> X \<and> X \<in> P) x" ..
            from \<open>X \<in> P\<close> \<open>x \<in> X\<close> have eq_X: "(THE X. x \<in> X \<and> X \<in> P) = X"
              using assms(2) partition_on_the_part_eq by fastforce
            from bij \<open>x \<in> X\<close> x'_eq eq_X show "x' \<in> bij X"
              using bij_betwE by blast
          qed
        next
          show "bij X \<subseteq> (\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` X"
          proof
            fix x'
            assume "x' \<in> bij X"
            let ?x = "inv_into X (p' X) x'"
            from \<open>x' \<in> bij X\<close> bij have "?x \<in> X"
              by (metis  bij_betw_imp_surj_on inv_into_into)
            from this \<open>X \<in> P\<close> have "(THE X. ?x \<in> X \<and> X \<in> P) = X"
              using assms(2) partition_on_the_part_eq by fastforce
            from this \<open>x' \<in> bij X\<close> bij have "x' = p' (THE X. ?x \<in> X \<and> X \<in> P) ?x"
              using bij_betw_inv_into_right by fastforce
            moreover from \<open>x' \<in> bij X\<close> bij have "?x \<in> X"
              by (metis bij_betw_imp_surj_on inv_into_into)
            ultimately show "x' \<in> (\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` X" ..
          qed
        qed
        ultimately have "(\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` X \<in> P'" by simp
        have "(\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` X = (\<lambda>a. if a \<in> A then p' (THE X. a \<in> X \<and> X \<in> P) a else a) ` X "
          using \<open>X \<subseteq> A\<close> by (auto intro: image_cong)
        from this show ?thesis
         using \<open>(\<lambda>a. p' (THE X. a \<in> X \<and> X \<in> P) a) ` X \<in> P'\<close> unfolding p_def by auto
      qed
      from this X'_eq show "X' \<in> P'" by simp
    qed
  qed
  ultimately show thesis using that by blast
qed

lemma permutes_domain_partition_eq:
  assumes "f \<in> A \<rightarrow> B"
  assumes "p\<^sub>A permutes A"
  assumes "b \<in> B"
  shows "p\<^sub>A ` {x \<in> A. f x = b} = {x \<in> A. f (inv p\<^sub>A x) = b}"
proof
  show "p\<^sub>A ` {x \<in> A. f x = b} \<subseteq> {x \<in> A. f (inv p\<^sub>A x) = b}"
    using \<open>p\<^sub>A permutes A\<close> permutes_in_image permutes_inverses(2) by fastforce
next
  show "{x \<in> A. f (inv p\<^sub>A x) = b} \<subseteq> p\<^sub>A ` {x \<in> A. f x = b}"
  proof
    fix x
    assume "x \<in> {x \<in> A. f (inv p\<^sub>A x) = b}"
    from this have "x \<in> A" "f (inv p\<^sub>A x) = b" by auto
    from \<open>x \<in> A\<close> have "x = p\<^sub>A (inv p\<^sub>A x)"
      using \<open>p\<^sub>A permutes A\<close> permutes_inverses(1) by fastforce
    moreover from \<open>f (inv p\<^sub>A x) = b\<close> \<open>x \<in> A\<close> have "inv p\<^sub>A x \<in> {x \<in> A. f x = b}"
      by (simp add: \<open>p\<^sub>A permutes A\<close> permutes_in_image permutes_inv)
    ultimately show "x \<in> p\<^sub>A ` {x \<in> A. f x = b}" ..
  qed
qed

lemma image_domain_partition_eq:
  assumes "f \<in> A \<rightarrow>\<^sub>E B"
  assumes "p\<^sub>A permutes A"
  shows "(\<lambda>X. p\<^sub>A ` X) ` ((\<lambda>b. {x \<in> A. f x = b}) ` B) = (\<lambda>b. {x \<in> A. f (inv p\<^sub>A x) = b}) ` B"
proof
  from \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> have "f \<in> A \<rightarrow> B" by auto
  note eq = permutes_domain_partition_eq[OF \<open>f \<in> A \<rightarrow> B\<close> \<open>p\<^sub>A permutes A\<close>]
  show "(\<lambda>X. p\<^sub>A ` X) ` (\<lambda>b. {x \<in> A. f x = b}) ` B \<subseteq> (\<lambda>b. {x \<in> A. f (inv p\<^sub>A x) = b}) ` B"
  proof
    fix X
    assume "X \<in> (\<lambda>X. p\<^sub>A ` X) ` (\<lambda>b. {x \<in> A. f x = b}) ` B"
    from this obtain b where "b \<in> B" and X_eq: "X = p\<^sub>A ` {x \<in> A. f x = b}" by auto
    from this eq have "X = {x \<in> A. f (inv p\<^sub>A x) = b}" by simp
    from this \<open>b \<in> B\<close> show "X \<in> (\<lambda>b. {x \<in> A. f (inv p\<^sub>A x) = b}) ` B" ..
  qed
next
  from \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> have "f \<in> A \<rightarrow> B" by auto
  note eq = permutes_domain_partition_eq[OF \<open>f \<in> A \<rightarrow> B\<close> \<open>p\<^sub>A permutes A\<close>, symmetric]
  show "(\<lambda>b. {x \<in> A. f (inv p\<^sub>A x) = b}) ` B \<subseteq> (\<lambda>X. p\<^sub>A ` X) ` (\<lambda>b. {x \<in> A. f x = b}) ` B"
  proof
    fix X
    assume "X \<in> (\<lambda>b. {x \<in> A. f (inv p\<^sub>A x) = b}) ` B"
    from this obtain b where "b \<in> B" and X_eq: "X = {x \<in> A. f (inv p\<^sub>A x) = b}" by auto
    from this eq have "X = p\<^sub>A ` {x \<in> A. f x = b}" by simp
    from this \<open>b \<in> B\<close> show "X \<in> (\<lambda>X. p\<^sub>A ` X) ` (\<lambda>b. {x \<in> A. f x = b}) ` B" by auto
  qed
qed

lemma multiset_of_partition_cards_eq_implies_permutes:
  assumes "finite A" "finite B" "f \<in> A \<rightarrow>\<^sub>E B" "f' \<in> A \<rightarrow>\<^sub>E B"
  assumes eq: "image_mset card (mset_set ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})) = image_mset card (mset_set ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}))"
  obtains p\<^sub>A p\<^sub>B where "p\<^sub>A permutes A" "p\<^sub>B permutes B" "\<forall>x\<in>A. f x = p\<^sub>B (f' (p\<^sub>A x))"
proof -
  have "partition_on A ((\<lambda>b. {x \<in> A. f x = b}) ` B - {{}})"
    using \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> by (auto intro!: partition_onI)
  moreover have "partition_on A ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}})"
    using \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> by (auto intro!: partition_onI)
  moreover note partition_implies_permutes[OF \<open>finite A\<close> _ _ eq]
  ultimately obtain p\<^sub>A where "p\<^sub>A permutes A" and
    inv_image_eq: "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} =
      (`) p\<^sub>A ` ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}})" by blast
  from \<open>p\<^sub>A permutes A\<close> have "inj ((`) p\<^sub>A)"
    by (meson injI inj_image_eq_iff permutes_inj)
  have inv_image_eq': "(\<lambda>b. {x \<in> A. f x = b}) ` B - {{}} = (\<lambda>b. {x \<in> A. f' (inv p\<^sub>A x) = b}) ` B - {{}}"
  proof -
    note inv_image_eq
    also have "(\<lambda>X. p\<^sub>A ` X) ` ((\<lambda>b. {x \<in> A. f' x = b}) ` B - {{}}) = (\<lambda>b. {x \<in> A. f' (inv p\<^sub>A x) = b}) ` B - {{}}"
      using image_domain_partition_eq[OF \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> \<open>p\<^sub>A permutes A\<close>]
      by (simp add: image_set_diff[OF \<open>inj ((`) p\<^sub>A)\<close>])
    finally show ?thesis .
  qed
  from \<open>p\<^sub>A permutes A\<close> have "inv p\<^sub>A permutes A"
    using permutes_inv by blast
  have "(\<lambda>x. f' (inv p\<^sub>A x)) \<in> A \<rightarrow>\<^sub>E B"
    using \<open>f' \<in> A \<rightarrow>\<^sub>E B\<close> \<open>inv p\<^sub>A permutes A\<close> permutes_in_image by fastforce
  from \<open>f \<in> A \<rightarrow>\<^sub>E B\<close> this \<open>finite B\<close> obtain p\<^sub>B
    where "p\<^sub>B permutes B" and eq'': "\<forall>x\<in>A. f x = p\<^sub>B (f' (inv p\<^sub>A x))"
    using partitions_eq_implies_permutes[OF _ _ _ inv_image_eq'] by blast
  from \<open>inv p\<^sub>A permutes A\<close> \<open>p\<^sub>B permutes B\<close> eq'' that show thesis by blast
qed

subsection \<open>Bijections on Same Domain and Range\<close>

subsubsection \<open>Existence of Domain Permutation\<close>

lemma obtain_domain_permutation_for_two_bijections:
  assumes "bij_betw f A B" "bij_betw f' A B"
  obtains p where "p permutes A" and "\<forall>a\<in>A. f a = f' (p a)"
proof -
  let ?p = "\<lambda>a. if a \<in> A then the_inv_into A f' (f a) else a"
  have "?p permutes A"
  proof (rule bij_imp_permutes)
    show "bij_betw ?p A A"
    proof (rule bij_betw_imageI)
      show "inj_on ?p A"
      proof (rule inj_onI)
        fix a a'
        assume "a \<in> A" "a' \<in> A" "?p a = ?p a'"
        from this have "the_inv_into A f' (f a) = the_inv_into A f' (f a')"
          using \<open>a \<in> A\<close> \<open>a' \<in> A\<close> by simp
        from this have "f a = f a'"
          using \<open>a \<in> A\<close> \<open>a' \<in> A\<close> assms
          by (metis bij_betwE f_the_inv_into_f_bij_betw)
        from this show "a = a'"
          using \<open>a \<in> A\<close> \<open>a' \<in> A\<close> assms
          by (metis bij_betw_inv_into_left)
      qed
    next
      show "?p ` A = A"
      proof
        show "?p ` A \<subseteq> A"
        proof
          fix a
          assume "a \<in> ?p ` A"
          from this obtain a' where "a' \<in> A" and "a = the_inv_into A f' (f a')" by auto
          from this assms show "a \<in> A"
            by (metis bij_betwE bij_betw_imp_inj_on bij_betw_imp_surj_on subset_iff the_inv_into_into)
        qed
      next
        show "A \<subseteq> ?p ` A"
        proof
          fix a
          assume "a \<in> A"
          from this assms have "the_inv_into A f (f' a) \<in> A"
            by (meson bij_betwE bij_betw_the_inv_into)
          moreover from  \<open>a \<in> A\<close> assms have "a = the_inv_into A f' (f (the_inv_into A f (f' a)))"
            by (metis bij_betwE bij_betw_imp_inj_on f_the_inv_into_f_bij_betw the_inv_into_f_eq)
          ultimately show "a \<in> ?p ` A" by auto
        qed
      qed
    qed
  next
    fix a
    assume "a \<notin> A"
    from this show "?p a = a" by auto
  qed
  moreover have "\<forall>a\<in>A. f a = f' (?p a)"
    using \<open>bij_betw f A B\<close> \<open>bij_betw f' A B\<close>
    using bij_betwE f_the_inv_into_f_bij_betw by fastforce
  moreover note that
  ultimately show thesis by auto
qed

subsubsection \<open>Existence of Range Permutation\<close>

lemma obtain_range_permutation_for_two_bijections:
  assumes "bij_betw f A B" "bij_betw f' A B"
  obtains p where "p permutes B" and "\<forall>a\<in>A. f a = p (f' a)"
proof -
  let ?p = "\<lambda>b. if b \<in> B then f (inv_into A f' b) else b"
  have "?p permutes B"
  proof (rule bij_imp_permutes)
    show "bij_betw ?p B B"
    proof (rule bij_betw_imageI)
      show "inj_on ?p B"
      proof (rule inj_onI)
        fix b b'
        assume "b \<in> B" "b' \<in> B" "?p b = ?p b'"
        from this have "f (inv_into A f' b) = f (inv_into A f' b')"
          using \<open>b \<in> B\<close> \<open>b' \<in> B\<close> by simp
        from this have "inv_into A f' b = inv_into A f' b'"
          using \<open>b \<in> B\<close> \<open>b' \<in> B\<close> assms
          by (metis bij_betw_imp_surj_on bij_betw_inv_into_left inv_into_into)
        from this show "b = b'"
          using \<open>b \<in> B\<close> \<open>b' \<in> B\<close> assms(2)
          by (metis bij_betw_inv_into_right)
      qed
    next
      show "?p ` B = B"
      proof
        from assms show "?p ` B \<subseteq> B"
          by (auto simp add: bij_betwE bij_betw_def inv_into_into)
      next
        show "B \<subseteq> ?p ` B"
        proof
          fix b
          assume "b \<in> B"
          from this assms have "f' (inv_into A f b) \<in> B"
            by (metis bij_betwE bij_betw_imp_surj_on inv_into_into)
          moreover have "b = ?p (f' (inv_into A f b))"
            using assms \<open>f' (inv_into A f b) \<in> B\<close> \<open>b \<in> B\<close>
            by (auto simp add: bij_betw_imp_surj_on bij_betw_inv_into_left bij_betw_inv_into_right inv_into_into)
          ultimately show "b \<in> ?p ` B" by auto
        qed
      qed
    qed
  next
    fix b
    assume "b \<notin> B"
    from this show "?p b = b" by auto
  qed
  moreover have "\<forall>a\<in>A. f a = ?p (f' a)"
    using \<open>bij_betw f' A B\<close> bij_betw_inv_into_left bij_betwE by fastforce
  moreover note that
  ultimately show thesis by auto
qed

end
