(*
Author:  Christian Sternagel <c.sternagel@gmail.com>
Author:  René Thiemann <rene.thiemann@uibk.ac.at>
License: LGPL
*)
subsection \<open>Results on Bijections\<close>

theory Fun_More imports Main begin

lemma finite_card_eq_imp_bij_betw:
  assumes "finite A"
    and "card (f ` A) = card A"
  shows "bij_betw f A (f ` A)"
  using \<open>card (f ` A) = card A\<close>
  unfolding inj_on_iff_eq_card [OF \<open>finite A\<close>, symmetric]
  by (rule inj_on_imp_bij_betw)

text \<open>Every bijective function between two subsets of a set can be turned
into a compatible renaming (with finite domain) on the full set.\<close>
lemma bij_betw_extend:
  assumes *: "bij_betw f A B"
    and "A \<subseteq> V"
    and "B \<subseteq> V"
    and "finite A"
  shows "\<exists>g. finite {x. g x \<noteq> x} \<and>
    (\<forall>x\<in>UNIV - (A \<union> B). g x = x) \<and>
    (\<forall>x\<in>A. g x = f x) \<and>
    bij_betw g V V"
proof -
  have "finite B" using assms by (metis bij_betw_finite)
  have [simp]: "card A = card B" by (metis * bij_betw_same_card)
  have "card (A - B) = card (B - A)"
  proof -
    have "card (A - B) = card A - card (A \<inter> B)"
      by (metis \<open>finite A\<close> card_Diff_subset_Int finite_Int)
    moreover have "card (B - A) = card B - card (A \<inter> B)"
      by (metis \<open>finite A\<close> card_Diff_subset_Int finite_Int inf_commute)
    ultimately show ?thesis by simp
  qed
  then obtain g where **: "bij_betw g (B - A) (A - B)"
    by (metis \<open>finite A\<close> \<open>finite B\<close> bij_betw_iff_card finite_Diff)
  define h where "h = (\<lambda>x. if x \<in> A then f x else if x \<in> B - A then g x else x)"
  have "bij_betw h A B"
    by (metis (full_types) * bij_betw_cong h_def)
  moreover have "bij_betw h (V - (A \<union> B)) (V - (A \<union> B))"
    by (auto simp: bij_betw_def h_def inj_on_def)
  moreover have "B \<inter> (V - (A \<union> B)) = {}" by blast
  ultimately have "bij_betw h (A \<union> (V - (A \<union> B))) (B \<union> (V - (A \<union> B)))"
    by (rule bij_betw_combine)
  moreover have "A \<union> (V - (A \<union> B)) = V - (B - A)"
    and "B \<union> (V - (A \<union> B)) = V - (A - B)"
    using \<open>A \<subseteq> V\<close> and \<open>B \<subseteq> V\<close> by blast+
  ultimately have "bij_betw h (V - (B - A)) (V - (A - B))" by simp
  moreover have "bij_betw h (B - A) (A - B)"
    using ** by (auto simp: bij_betw_def h_def inj_on_def)
  moreover have "(V - (A - B)) \<inter> (A - B) = {}" by blast
  ultimately have "bij_betw h ((V - (B - A)) \<union> (B - A)) ((V - (A - B)) \<union> (A - B))"
    by (rule bij_betw_combine)
  moreover have "(V - (B - A)) \<union> (B - A) = V"
    and "(V - (A - B)) \<union> (A - B) = V"
    using \<open>A \<subseteq> V\<close> and \<open>B \<subseteq> V\<close> by auto
  ultimately have "bij_betw h V V" by simp
  moreover have "\<forall>x\<in>A. h x = f x" by (auto simp: h_def)
  moreover have "finite {x. h x \<noteq> x}"
  proof -
    have "finite (A \<union> (B - A))" using \<open>finite A\<close> and \<open>finite B\<close> by auto
    moreover have "{x. h x \<noteq> x} \<subseteq> (A \<union> (B - A))" by (auto simp: h_def)
    ultimately show ?thesis by (metis finite_subset)
  qed
  moreover have "\<forall>x\<in>UNIV - (A \<union> B). h x = x" by (simp add: h_def)
  ultimately show ?thesis by blast
qed


subsection \<open>Merging Functions\<close>
(* Copied and canonized from IsaFoR's Term theory and Polynomial Factorization in the AFP. *)
definition fun_merge :: "('a \<Rightarrow> 'b)list \<Rightarrow> 'a set list \<Rightarrow> 'a \<Rightarrow> 'b"
  where
    "fun_merge fs as a = (fs ! (LEAST i. i < length as \<and> a \<in> as ! i)) a"

lemma fun_merge_eq_nth:
  assumes i: "i < length as"
    and a: "a \<in> as ! i"
    and ident: "\<And> i j a. i < length as \<Longrightarrow> j < length as \<Longrightarrow> a \<in> as ! i \<Longrightarrow> a \<in> as ! j \<Longrightarrow> (fs ! i) a = (fs ! j) a"
  shows "fun_merge fs as a = (fs ! i) a"
proof -
  let ?p = "\<lambda> i. i < length as \<and> a \<in> as ! i"
  let ?l = "LEAST i. ?p i"
  have p: "?p ?l"
    by (rule LeastI, insert i a, auto)
  show ?thesis unfolding fun_merge_def
    by (rule ident[OF _ i _ a], insert p, auto)
qed

lemma fun_merge_part:
  assumes "\<forall>i<length as.\<forall>j<length as. i \<noteq> j \<longrightarrow> as ! i \<inter> as ! j = {}"
    and "i < length as"
    and "a \<in> as ! i"
  shows "fun_merge fs as a = (fs ! i) a"
proof(rule fun_merge_eq_nth [OF assms(2, 3)])
  fix i j a
  assume "i < length as" and "j < length as" and "a \<in> as ! i" and "a \<in> as ! j"
  then have "i = j" using assms by (cases "i = j") auto
  then show "(fs ! i) a = (fs ! j) a" by simp
qed

lemma fun_merge:
  assumes part: "\<forall>i<length Xs.\<forall>j<length Xs. i \<noteq> j \<longrightarrow> Xs ! i \<inter> Xs ! j = {}"
  shows "\<exists>\<sigma>. \<forall>i<length Xs. \<forall>x\<in> Xs ! i. \<sigma> x = \<tau> i x"
proof -
  let ?\<tau> = "map \<tau> [0 ..< length Xs]"
  let ?\<sigma> = "fun_merge ?\<tau> Xs"
  show ?thesis
    by (rule exI[of _ ?\<sigma>], intro allI impI ballI,
      insert fun_merge_part[OF part, of _ _ ?\<tau>], auto)
qed

end