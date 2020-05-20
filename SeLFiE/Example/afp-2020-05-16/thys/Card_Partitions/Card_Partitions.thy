(*  Author: Lukas Bulwahn <lukas.bulwahn-at-gmail.com> *)

section \<open>Cardinality of Set Partitions\<close>

theory Card_Partitions
imports
  "HOL-Library.Stirling"
  Set_Partition
  Injectivity_Solver
begin

lemma set_partition_on_insert_with_fixed_card_eq:
  assumes "finite A"
  assumes "a \<notin> A"
  shows "{P. partition_on (insert a A) P \<and> card P = Suc k} = (do {
     P <- {P. partition_on A P \<and> card P = Suc k};
     p <- P;
     {insert (insert a p) (P - {p})}
  })
  \<union> (do {
    P <- {P. partition_on A P \<and> card P = k};
    {insert {a} P}
  })" (is "?S = ?T")
proof
  show "?S \<subseteq> ?T"
  proof
    fix P
    assume "P \<in> {P. partition_on (insert a A) P \<and> card P = Suc k}"
    from this have "partition_on (insert a A) P" and "card P = Suc k" by auto
    show "P \<in> ?T"
    proof cases
      assume "{a} \<in> P"
      have "partition_on A (P - {{a}})"
        using \<open>{a} \<in> P\<close> \<open>partition_on (insert a A) P\<close>[THEN partition_on_Diff, of "{{a}}"] \<open>a \<notin> A\<close>
        by auto
      moreover from \<open>{a} \<in> P\<close> \<open>card P = Suc k\<close> have "card (P - {{a}}) = k"
        by (subst card_Diff_singleton) (auto intro: card_ge_0_finite)
      moreover from \<open>{a} \<in> P\<close> have "P = insert {a} (P - {{a}})" by auto
      ultimately have "P \<in> {P. partition_on A P \<and> card P = k} \<bind> (\<lambda>P. {insert {a} P})"
        by auto
      from this show ?thesis by auto
    next
      assume "{a} \<notin> P"
      let ?p' = "(THE X. a \<in> X \<and> X \<in> P)"
      let ?p = "(THE X. a \<in> X \<and> X \<in> P) - {a}"
      let ?P' = "insert ?p (P - {?p'})"
      from \<open>partition_on (insert a A) P\<close> have "a \<in> (THE X. a \<in> X \<and> X \<in> P)"
        using partition_on_in_the_unique_part by fastforce
      from \<open>partition_on (insert a A) P\<close> have "(THE X. a \<in> X \<and> X \<in> P) \<in> P"
        using partition_on_the_part_mem by fastforce
      from this \<open>partition_on (insert a A) P\<close> have "(THE X. a \<in> X \<and> X \<in> P) - {a} \<notin> P"
        using partition_subset_imp_notin \<open>a \<in> (THE X. a \<in> X \<and> X \<in> P)\<close> by blast
      have "(THE X. a \<in> X \<and> X \<in> P) \<noteq> {a}"
        using \<open>(THE X. a \<in> X \<and> X \<in> P) \<in> P\<close> \<open>{a} \<notin> P\<close> by auto
      from \<open>partition_on (insert a A) P\<close> have "(THE X. a \<in> X \<and> X \<in> P) \<subseteq> insert a A"
        using \<open>(THE X. a \<in> X \<and> X \<in> P) \<in> P\<close> partition_onD1 by fastforce
      note facts_on_the_part_of = \<open>a \<in> (THE X. a \<in> X \<and> X \<in> P)\<close> \<open>(THE X. a \<in> X \<and> X \<in> P) \<in> P\<close>
        \<open>(THE X. a \<in> X \<and> X \<in> P) - {a} \<notin> P\<close> \<open>(THE X. a \<in> X \<and> X \<in> P) \<noteq> {a}\<close>
        \<open>(THE X. a \<in> X \<and> X \<in> P) \<subseteq> insert a A\<close>
      from \<open>partition_on (insert a A) P\<close> \<open>finite A\<close> have "finite P"
        by (meson finite.insertI finite_elements)
      from \<open>partition_on (insert a A) P\<close> \<open>a \<notin> A\<close> have "partition_on (A - ?p) (P - {?p'})"
        using facts_on_the_part_of by (auto intro: partition_on_remove_singleton)
      from this have "partition_on A ?P'"
        using facts_on_the_part_of by (auto intro: partition_on_insert simp add: disjnt_iff)
      moreover have "card ?P' = Suc k"
      proof -
        from \<open>card P = Suc k\<close> have "card (P - {THE X. a \<in> X \<and> X \<in> P}) = k"
          using \<open>finite P\<close> \<open>(THE X. a \<in> X \<and> X \<in> P) \<in> P\<close> by simp
        from this show ?thesis
          using \<open>finite P\<close> \<open>(THE X. a \<in> X \<and> X \<in> P) - {a} \<notin> P\<close> by (simp add: card_insert_if)
      qed
      moreover have "?p \<in> ?P'" by auto
      moreover have "P = insert (insert a ?p) (?P' - {?p})"
        using facts_on_the_part_of by (auto simp add: insert_absorb)
      ultimately have "P \<in> {P. partition_on A P \<and> card P = Suc k} \<bind> (\<lambda>P. P \<bind> (\<lambda>p. {insert (insert a p) (P - {p})}))"
        by auto
      then show ?thesis by auto
    qed
  qed
next
  show "?T \<subseteq> ?S"
  proof
    fix P
    assume "P \<in> ?T" (is "_ \<in> ?subexpr1 \<union> ?subexpr2")
    from this show "P \<in> ?S"
    proof
      assume "P \<in> ?subexpr1"
      from this obtain p P' where "P = insert (insert a p) (P' - {p})"
        and "partition_on A P'" and "card P' = Suc k" and "p \<in> P'"  by auto
      from \<open>p \<in> P'\<close> \<open>partition_on A P'\<close> have "partition_on (A - p) (P' - {p})"
        by (simp add: partition_on_remove_singleton)
      from \<open>partition_on A P'\<close> \<open>finite A\<close> have "finite P"
        using \<open>P = _\<close> finite_elements by auto
      from \<open>partition_on A P'\<close> \<open>a \<notin> A\<close> have "insert a p \<notin> P' - {p}"
        using partition_onD1 by fastforce
      from \<open>P = _\<close> this \<open>card P' = Suc k\<close> \<open>finite P\<close> \<open>p \<in> P'\<close>
      have "card P = Suc k" by auto
      moreover have "partition_on (insert a A) P"
        using \<open>partition_on (A - p) (P' - {p})\<close> \<open>a \<notin> A\<close> \<open>p \<in> P'\<close> \<open>partition_on A P'\<close> \<open>P = _\<close>
        by (auto intro!: partition_on_insert dest: partition_onD1 simp add: disjnt_iff)
      ultimately show "P \<in> ?S" by auto
    next
      assume "P \<in> ?subexpr2"
      from this obtain P' where "P = insert {a} P'" and "partition_on A P'" and "card P' = k" by auto
      from \<open>partition_on A P'\<close> \<open>finite A\<close> have "finite P"
        using \<open>P = insert {a} P'\<close> finite_elements by auto
      from \<open>partition_on A P'\<close> \<open>a \<notin> A\<close> have "{a} \<notin> P'"
        using partition_onD1 by fastforce
      from \<open>P = insert {a} P'\<close> \<open>card P' = k\<close> this \<open>finite P\<close> have "card P = Suc k" by auto
      moreover from \<open>partition_on A P'\<close> \<open>a \<notin> A\<close> have "partition_on (insert a A) P"
        using \<open>P = insert {a} P'\<close> by (simp add: partition_on_insert_singleton)
      ultimately show "P \<in> ?S" by auto
    qed
  qed
qed

lemma injectivity_subexpr1:
  assumes "a \<notin> A"
  assumes "X \<in> P \<and> X' \<in> P'"
  assumes "insert (insert a X) (P - {X}) = insert (insert a X') (P' - {X'})"
  assumes "(partition_on A P \<and> card P = Suc k') \<and> (partition_on A P' \<and> card P' = Suc k')"
  shows "P = P'" and "X = X'"
proof -
  from assms(1, 2, 4) have "a \<notin> X" "a \<notin> X'"
    using partition_onD1 by auto
  from assms(1, 4) have "insert a X \<notin> P" "insert a X' \<notin> P'"
    using partition_onD1 by auto
  from assms(1, 3, 4) have "insert a X = insert a X'"
    by (metis Diff_iff insertE insertI1 mem_simps(9) partition_onD1)
  from this \<open>a \<notin> X'\<close> \<open>a \<notin> X\<close> show "X = X'"
    by (meson insert_ident)
  from assms(2, 3) show "P = P'"
    using \<open>insert a X = insert a X'\<close> \<open>insert a X \<notin> P\<close> \<open>insert a X' \<notin> P'\<close>
    by (metis insert_Diff insert_absorb insert_commute insert_ident)
qed

lemma injectivity_subexpr2:
  assumes "a \<notin> A"
  assumes "insert {a} P = insert {a} P'"
  assumes "(partition_on A P \<and> card P = k') \<and> partition_on A P' \<and> card P' = k'"
  shows "P = P'"
proof -
  from assms(1, 3) have "{a} \<notin> P" and "{a} \<notin> P'"
    using partition_onD1 by auto
  from \<open>{a} \<notin> P\<close> have "P = insert {a} P - {{a}}" by simp
  also from \<open>insert {a} P = insert {a} P'\<close> have "\<dots> = insert {a} P' - {{a}}" by simp
  also from \<open>{a} \<notin> P'\<close> have "\<dots> = P'" by simp
  finally show ?thesis .
qed

theorem card_partition_on:
  assumes "finite A"
  shows "card {P. partition_on A P \<and> card P = k} = Stirling (card A) k"
using assms
proof (induct A arbitrary: k)
  case empty
    have eq: "{P. P = {} \<and> card P = 0} = {{}}" by auto
    show ?case by (cases k) (auto simp add: partition_on_empty eq)
next
  case (insert a A)
  from this show ?case
  proof (cases k)
    case 0
    from insert(1) have empty: "{P. partition_on (insert a A) P \<and> card P = 0} = {}"
      unfolding partition_on_def by (auto simp add: card_eq_0_iff finite_UnionD)
    from 0 insert show ?thesis by (auto simp add: empty)
  next
    case (Suc k')
    let ?subexpr1 = "do {
      P <- {P. partition_on A P \<and> card P = Suc k'};
      p <- P;
      {insert (insert a p) (P - {p})}
    }"
    let ?subexpr2 = "do {
      P <- {P. partition_on A P \<and> card P = k'};
      {insert {a} P}
    }"
    let ?expr = "?subexpr1 \<union> ?subexpr2"
    have "card {P. partition_on (insert a A) P \<and> card P = k} = card ?expr"
      using \<open>finite A\<close> \<open>a \<notin> A\<close> \<open>k = Suc k'\<close> by (simp add: set_partition_on_insert_with_fixed_card_eq)
    also have "card ?expr = Stirling (card A) k' + Stirling (card A) (Suc k') * Suc k'"
    proof -
      have "finite ?subexpr1 \<and> card ?subexpr1 = Stirling (card A) (Suc k') * Suc k'"
      proof -
        from \<open>finite A\<close> have "finite {P. partition_on A P \<and> card P = Suc k'}"
          by (simp add: finitely_many_partition_on)
        moreover have "\<forall>X\<in>{P. partition_on A P \<and> card P = Suc k'}. finite (X \<bind> (\<lambda>p. {insert (insert a p) (X - {p})}))"
          using finite_elements \<open>finite A\<close> finite_bind
          by (metis (no_types, lifting) finite.emptyI finite_insert mem_Collect_eq)
        moreover have "disjoint_family_on (\<lambda>P. P \<bind> (\<lambda>p. {insert (insert a p) (P - {p})})) {P. partition_on A P \<and> card P = Suc k'}"
          by (injectivity_solver rule: injectivity_subexpr1(1)[OF \<open>a \<notin> A\<close>])
        moreover have "card (P \<bind> (\<lambda>p. {insert (insert a p) (P - {p})})) = Suc k'"
          if "P \<in> {P. partition_on A P \<and> card P = Suc k'}" for P
        proof -
          from that \<open>finite A\<close> have "finite P"
            using finite_elements by blast
          moreover have "inj_on (\<lambda>p. insert (insert a p) (P - {p})) P"
            using that injectivity_subexpr1(2)[OF \<open>a \<notin> A\<close>] by (simp add: inj_onI)
          moreover from that have "card P = Suc k'" by simp
          ultimately show ?thesis by (simp add: card_bind_singleton)
        qed
        ultimately have "card ?subexpr1 = card {P. partition_on A P \<and> card P = Suc k'} * Suc k'"
          by (subst card_bind_constant) simp+
        from this have "card ?subexpr1 = Stirling (card A) (Suc k') * Suc k'"
          using insert.hyps(3) by simp
        moreover have "finite ?subexpr1"
          using \<open>finite {P. partition_on A P \<and> card P = Suc k'}\<close>
          \<open>\<forall>X\<in>{P. partition_on A P \<and> card P = Suc k'}. finite (X \<bind> (\<lambda>p. {insert (insert a p) (X - {p})}))\<close>
          by (auto intro: finite_bind)
        ultimately show ?thesis by blast
      qed
      moreover have "finite ?subexpr2 \<and> card ?subexpr2 = Stirling (card A) k'"
      proof -
        from \<open>finite A\<close> have "finite {P. partition_on A P \<and> card P = k'}"
          by (simp add: finitely_many_partition_on)
        moreover have " inj_on (insert {a}) {P. partition_on A P \<and> card P = k'}"
          using injectivity_subexpr2[OF \<open>a \<notin> A\<close>] by (simp add: inj_on_def)
        ultimately have "card ?subexpr2 = card {P. partition_on A P \<and> card P = k'}"
          by (simp add: card_bind_singleton)
        also have "\<dots> = Stirling (card A) k'"
          using insert.hyps(3) .
        finally have "card ?subexpr2 = Stirling (card A) k'" .
        moreover have "finite ?subexpr2"
          by (simp add: \<open>finite {P. partition_on A P \<and> card P = k'}\<close> finite_bind)
        ultimately show ?thesis by blast
      qed
      moreover have "?subexpr1 \<inter> ?subexpr2 = {}"
      proof -
        have "\<forall>P\<in>?subexpr1. {a} \<notin> P"
          using insert.hyps(2) by (force elim!: partition_onE)
        moreover have "\<forall>P\<in>?subexpr2. {a} \<in> P" by auto
        ultimately show "?subexpr1 \<inter> ?subexpr2 = {}" by blast
      qed
      ultimately show ?thesis
        by (simp add: card_Un_disjoint)
    qed
    also have "\<dots> = Stirling (card (insert a A)) k"
      using insert(1, 2) \<open>k = Suc k'\<close> by simp
    finally show ?thesis .
  qed
qed

theorem card_partition_on_at_most_size:
  assumes "finite A"
  shows "card {P. partition_on A P \<and> card P \<le> k} = (\<Sum>j\<le>k. Stirling (card A) j)"
proof -
  have "card {P. partition_on A P \<and> card P \<le> k} = card (\<Union>j\<le>k. {P. partition_on A P \<and> card P = j})"
    by (rule arg_cong[where f="card"]) auto
  also have "\<dots> = (\<Sum>j\<le>k. card {P. partition_on A P \<and> card P = j})"
    by (subst card_UN_disjoint) (auto simp add: \<open>finite A\<close> finitely_many_partition_on)
  also have "(\<Sum>j\<le>k. card {P. partition_on A P \<and> card P = j}) = (\<Sum>j\<le>k. Stirling (card A) j)"
    using \<open>finite A\<close> by (simp add: card_partition_on)
  finally show ?thesis .
qed

theorem partition_on_size1:
  assumes "finite A"
  shows "{P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)} = {(\<lambda>a. {a}) ` A}"
proof
  show "{P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)} \<subseteq> {(\<lambda>a. {a}) ` A}"
  proof
    fix P
    assume P: "P \<in> {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}"
    have "P = (\<lambda>a. {a}) ` A"
    proof
      show "P \<subseteq> (\<lambda>a. {a}) ` A"
      proof
        fix X
        assume "X \<in> P"
        from P this obtain x where "X = {x}"
           by (auto simp add: card_Suc_eq)
        from this \<open>X \<in> P\<close> have "x \<in> A"
          using P unfolding partition_on_def by blast
        from this \<open>X = {x}\<close> show "X \<in>(\<lambda>a. {a}) ` A" by auto
      qed
    next
      show "(\<lambda>a. {a}) ` A \<subseteq> P"
      proof
        fix X
        assume "X \<in> (\<lambda>a. {a}) ` A"
        from this obtain x where X: "X = {x}" "x \<in> A" by auto
        have "\<Union>P = A"
          using P unfolding partition_on_def by blast
        from this \<open>x \<in> A\<close> obtain X' where "x \<in> X'" and "X' \<in> P"
          using UnionE by blast
        from \<open>X' \<in> P\<close> have "card X' = 1"
          using P unfolding partition_on_def by auto
        from this \<open>x \<in> X'\<close> have "X' = {x}"
          using card_1_singletonE by blast
        from this X(1) \<open>X' \<in> P\<close> show "X \<in> P" by auto
      qed
    qed
    from this show "P \<in> {(\<lambda>a. {a}) ` A}" by auto
  qed
next
  show "{(\<lambda>a. {a}) ` A} \<subseteq> {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}"
  proof
    fix P
    assume "P \<in> {(\<lambda>a. {a}) ` A}"
    from this have P: "P = (\<lambda>a. {a}) ` A" by auto
    from this have "partition_on A P" by (auto intro: partition_onI)
    from P this show "P \<in> {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}" by auto
  qed
qed

theorem card_partition_on_size1:
  assumes "finite A"
  shows "card {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)} = 1"
using assms partition_on_size1 by fastforce

lemma card_partition_on_size1_eq_1:
  assumes "finite A"
  assumes "card A \<le> k"
  shows "card {P. partition_on A P \<and> card P \<le> k \<and> (\<forall>X\<in>P. card X = 1)} = 1"
proof -
  {
    fix P
    assume "partition_on A P" "\<forall>X\<in>P. card X = 1"
    from this have "P \<in> {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}" by simp
    from this have "P \<in> {(\<lambda>a. {a}) ` A}"
      using partition_on_size1 \<open>finite A\<close> by auto
    from this have "P = (\<lambda>a. {a}) ` A" by auto
    moreover from this have "card P = card A"
      by (auto intro: card_image)
  }
  from this have "{P. partition_on A P \<and> card P \<le> k \<and> (\<forall>X\<in>P. card X = 1)} = {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}"
    using \<open>card A \<le> k\<close> by auto
  from this show ?thesis
    using \<open>finite A\<close> by (simp only: card_partition_on_size1)
qed

lemma card_partition_on_size1_eq_0:
  assumes "finite A"
  assumes "k < card A"
  shows "card {P. partition_on A P \<and> card P \<le> k \<and> (\<forall>X\<in>P. card X = 1)} = 0"
proof -
  {
    fix P
    assume "partition_on A P" "\<forall>X\<in>P. card X = 1"
    from this have "P \<in> {P. partition_on A P \<and> (\<forall>X\<in>P. card X = 1)}" by simp
    from this have "P \<in> {(\<lambda>a. {a}) ` A}"
      using partition_on_size1 \<open>finite A\<close> by auto
    from this have "P = (\<lambda>a. {a}) ` A" by auto
    from this have "card P = card A"
      by (auto intro: card_image)
  }
  from this assms(2) have "{P. partition_on A P \<and> card P \<le> k \<and> (\<forall>X\<in>P. card X = 1)} = {}"
    using Collect_empty_eq leD by fastforce
  from this show ?thesis by (simp only: card_empty)
qed

end
