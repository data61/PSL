(*  Title:      InfiniteSet2.thy
    Date:       Aug 2008
    Author:     David Trachtenherz
*)

section \<open>Set operations with results of type enat\<close>

theory InfiniteSet2
imports SetInterval2
begin

subsection \<open>Set operations with @{typ enat}\<close>

subsubsection \<open>Basic definitions\<close>

definition icard :: "'a set \<Rightarrow> enat"
  where "icard A \<equiv> if finite A then enat (card A) else \<infinity>"


subsection \<open>Results for \<open>icard\<close>\<close>

lemma icard_UNIV_nat: "icard (UNIV::nat set) = \<infinity>"
by (simp add: icard_def)

lemma icard_finite_conv: "(icard A = enat (card A)) = finite A"
by (case_tac "finite A", simp_all add: icard_def)
lemma icard_infinite_conv: "(icard A = \<infinity>) = infinite A"
by (case_tac "finite A", simp_all add: icard_def)

corollary icard_finite: "finite A \<Longrightarrow> icard A = enat (card A)"
by (rule icard_finite_conv[THEN iffD2])
corollary icard_infinite[simp]: "infinite A \<Longrightarrow> icard A = \<infinity>"
by (rule icard_infinite_conv[THEN iffD2])

lemma icard_eq_enat_imp: "icard A = enat n \<Longrightarrow> finite A"
by (case_tac "finite A", simp_all)
lemma icard_eq_Infty_imp: "icard A = \<infinity> \<Longrightarrow> infinite A"
by (rule icard_infinite_conv[THEN iffD1])

lemma icard_the_enat: "finite A \<Longrightarrow> the_enat (icard A) = card A"
by (simp add: icard_def)

lemma icard_eq_enat_imp_card: "icard A = enat n \<Longrightarrow> card A = n"
by (frule icard_eq_enat_imp, simp add: icard_finite)

lemma icard_eq_enat_card_conv: "0 < n \<Longrightarrow> (icard A = enat n) = (card A = n)"
apply (rule iffI)
 apply (simp add: icard_eq_enat_imp_card)
apply (drule sym, simp)
apply (frule card_gr0_imp_finite)
apply (rule icard_finite, assumption)
done

lemma icard_empty[simp]: "icard {} = 0"
by (simp add: icard_finite[OF finite.emptyI])
lemma icard_empty_iff: "(icard A = 0) = (A = {})"
apply (unfold zero_enat_def)
apply (rule iffI)
 apply (frule icard_eq_enat_imp)
 apply (simp add: icard_finite)
apply simp
done
lemmas icard_empty_iff_enat = icard_empty_iff[unfolded zero_enat_def]

lemma icard_not_empty_iff: "(0 < icard A) = (A \<noteq> {})"
by (simp add: icard_empty_iff[symmetric])
lemmas icard_not_empty_iff_enat = icard_not_empty_iff[unfolded zero_enat_def]

lemma icard_singleton: "icard {a} = eSuc 0"
by (simp add: icard_finite eSuc_enat)
lemmas icard_singleton_enat[simp] = icard_singleton[unfolded zero_enat_def]
lemma icard_1_imp_singleton: "icard A = eSuc 0 \<Longrightarrow> \<exists>a. A = {a}"
apply (simp add: eSuc_enat)
apply (frule icard_eq_enat_imp)
apply (simp add: icard_finite card_1_imp_singleton)
done
lemma icard_1_singleton_conv: "(icard A = eSuc 0) = (\<exists>a. A = {a})"
apply (rule iffI)
 apply (simp add: icard_1_imp_singleton)
apply fastforce
done

lemma icard_insert_disjoint: "x \<notin> A \<Longrightarrow> icard (insert x A) = eSuc (icard A)"
apply (case_tac "finite A")
 apply (simp add: icard_finite eSuc_enat card_insert_disjoint)
apply (simp add: infinite_insert)
done

lemma icard_insert_if: "icard (insert x A) = (if x \<in> A then icard A else eSuc (icard A))"
apply (case_tac "x \<in> A")
 apply (simp add: insert_absorb)
apply (simp add: icard_insert_disjoint)
done

lemmas icard_0_eq = icard_empty_iff

lemma icard_Suc_Diff1: "x \<in> A \<Longrightarrow> eSuc (icard (A - {x})) = icard A"
apply (case_tac "finite A")
 apply (simp add: icard_finite eSuc_enat in_imp_not_empty not_empty_card_gr0_conv[THEN iffD1])
apply (simp add: Diff_infinite_finite[OF singleton_finite])
done

lemma icard_Diff_singleton: "x \<in> A \<Longrightarrow> icard (A - {x}) = icard A - 1"
apply (rule eSuc_inject[THEN iffD1])
apply (frule in_imp_not_empty, drule icard_not_empty_iff[THEN iffD2])
apply (simp add: icard_Suc_Diff1 eSuc_pred_enat one_eSuc)
done

lemma icard_Diff_singleton_if: "icard (A - {x}) = (if x \<in> A then icard A - 1 else icard A)"
by (simp add: icard_Diff_singleton)

lemma icard_insert: "icard (insert x A) = eSuc (icard (A - {x}))"
by (metis icard_Diff_singleton_if icard_Suc_Diff1 icard_insert_disjoint insert_absorb)

lemma icard_insert_le: "icard A \<le> icard (insert x A)"
by (simp add: icard_insert_if)

lemma icard_mono: "A \<subseteq> B \<Longrightarrow> icard A \<le> icard B"
apply (case_tac "finite B")
 apply (frule subset_finite_imp_finite, simp)
 apply (simp add: icard_finite card_mono)
apply simp
done

lemma not_icard_seteq: "\<exists>(A::nat set) B. (A \<subseteq> B \<and> icard B \<le> icard A \<and> \<not> A = B)"
apply (rule_tac x="{1..}" in exI)
apply (rule_tac x="{0..}" in exI)
apply (fastforce simp add: infinite_atLeast)
done

lemma not_psubset_icard_mono: "\<exists>(A::nat set) B. A \<subset> B \<and> \<not> icard A < icard B"
apply (rule_tac x="{1..}" in exI)
apply (rule_tac x="{0..}" in exI)
apply (fastforce simp add: infinite_atLeast)
done

lemma icard_Un_Int: "icard A + icard B = icard (A \<union> B) + icard (A \<inter> B)"
apply (case_tac "finite A", case_tac "finite B")
 apply (simp add: icard_finite card_Un_Int[of A])
apply simp_all
done

lemma icard_Un_disjoint: "A \<inter> B = {} \<Longrightarrow> icard (A \<union> B) = icard A + icard B"
by (simp add: icard_Un_Int[of A])

lemma not_icard_Diff_subset: "\<exists>(A::nat set) B. B \<subseteq> A \<and> \<not> icard (A - B) = icard A - icard B"
apply (rule_tac x="{0..}" in exI)
apply (rule_tac x="{1..}" in exI)
apply (simp add: set_diff_eq linorder_not_le icard_UNIV_nat eSuc_enat)
done

lemma not_icard_Diff1_less: "\<exists>(A::nat set)x. x \<in> A \<and> \<not> icard (A - {x}) < icard A"
by (rule_tac x="{0..}" in exI, simp)

lemma not_icard_Diff2_less: "\<exists>(A::nat set)x y. x \<in> A \<and> y \<in> A \<and> \<not> icard (A - {x} - {y}) < icard A"
by (rule_tac x="{0..}" in exI, simp)

lemma icard_Diff1_le: "icard (A - {x}) \<le> icard A"
by (rule icard_mono, rule Diff_subset)

lemma icard_psubset: "\<lbrakk> A \<subseteq> B; icard A < icard B \<rbrakk> \<Longrightarrow> A \<subset> B"
by (metis less_le psubset_eq)

lemma icard_partition: "
  \<lbrakk> \<And>c. c \<in> C \<Longrightarrow> icard c = k; \<And>c1 c2. \<lbrakk>c1 \<in> C; c2 \<in> C; c1 \<noteq> c2\<rbrakk> \<Longrightarrow> c1 \<inter> c2 = {} \<rbrakk> \<Longrightarrow>
  icard (\<Union>C) = k * icard C"
apply (case_tac "C = {}", simp)
apply (case_tac "k = 0")
 apply (simp add: icard_empty_iff_enat)
apply simp
apply (case_tac k, rename_tac k1)
 apply (subgoal_tac "0 < k1")
  prefer 2
  apply simp
 apply (case_tac "finite C")
  apply (simp add: icard_finite)
  apply (subgoal_tac "\<And>c. c \<in> C \<Longrightarrow> card c = k1")
   prefer 2
   apply (rule icard_eq_enat_imp_card, simp)
  apply (frule_tac C=C and k=k1 in SetInterval2.card_partition, simp+)
  apply (subgoal_tac "finite (\<Union>C)")
   prefer 2
   apply (rule card_gr0_imp_finite)
   apply (simp add: not_empty_card_gr0_conv)
  apply (simp add: icard_finite)
 apply simp
 apply (rule icard_infinite)
 apply (rule ccontr, simp)
 apply (drule finite_UnionD, simp)
apply (frule icard_not_empty_iff[THEN iffD2])
apply (simp add: icard_infinite_conv)
apply (frule not_empty_imp_ex, erule exE, rename_tac c)
apply (frule Union_upper)
apply (rule infinite_super, assumption)
apply simp
done

lemma icard_image_le: "icard (f ` A) \<le> icard A"
apply (case_tac "finite A")
 apply (simp add: icard_finite card_image_le)
apply simp
done

lemma icard_image: "inj_on f A \<Longrightarrow> icard (f ` A) = icard A"
apply (case_tac "finite A")
 apply (simp add: icard_finite card_image)
apply (simp add: icard_infinite_conv inj_on_imp_infinite_image)
done

lemma not_eq_icard_imp_inj_on: "\<exists>(f::nat\<Rightarrow>nat) (A::nat set). icard (f ` A) = icard A \<and> \<not> inj_on f A"
apply (rule_tac x="\<lambda>n. (if n = 0 then Suc 0 else n)" in exI)
apply (rule_tac x="{0..}" in exI)
apply (rule conjI)
 apply (rule subst[of "{1..}" "((\<lambda>n. if n = 0 then Suc 0 else n) ` {0..})"])
  apply (simp add: set_eq_iff)
  apply (rule allI, rename_tac n)
  apply (case_tac "n = 0", simp)
  apply simp
 apply (simp only: icard_infinite[OF infinite_atLeast])
apply (simp add: inj_on_def)
apply blast
done

lemma not_inj_on_iff_eq_icard: "\<exists>(f::nat\<Rightarrow>nat) (A::nat set). \<not> (inj_on f A = (icard (f ` A) = icard A))"
by (insert not_eq_icard_imp_inj_on, blast)

lemma icard_inj_on_le: "\<lbrakk> inj_on f A; f ` A \<subseteq> B \<rbrakk> \<Longrightarrow> icard A \<le> icard B"
apply (case_tac "finite B")
 apply (metis icard_image icard_mono)
apply simp
done

lemma icard_bij_eq: "
  \<lbrakk> inj_on f A; f ` A \<subseteq> B; inj_on g B; g ` B \<subseteq> A \<rbrakk> \<Longrightarrow>
  icard A = icard B"
by (simp add: order_eq_iff icard_inj_on_le)

lemma icard_cartesian_product: "icard (A \<times> B) = icard A * icard B"
apply (case_tac "A = {} \<or> B = {}", fastforce)
apply clarsimp
apply (case_tac "finite A \<and> finite B")
 apply (simp add: icard_finite)
apply (simp only: de_Morgan_conj, erule disjE)
apply (simp_all add:
  icard_not_empty_iff[symmetric]
  cartesian_product_infiniteL_imp_infinite cartesian_product_infiniteR_imp_infinite)
done

lemma icard_cartesian_product_singleton: "icard ({x} \<times> A) = icard A"
by (simp add: icard_cartesian_product mult_eSuc)

lemma icard_cartesian_product_singleton_right: "icard (A \<times> {x}) = icard A"
by (simp add: icard_cartesian_product mult_eSuc_right)

lemma
  icard_lessThan: "icard {..<u} = enat u" and
  icard_atMost: "icard {..u} = enat (Suc u)" and
  icard_atLeastLessThan: "icard {l..<u} = enat (u - l)" and
  icard_atLeastAtMost: "icard {l..u} = enat (Suc u - l)" and
  icard_greaterThanAtMost: "icard {l<..u} = enat (u - l)" and
  icard_greaterThanLessThan: "icard {l<..<u} = enat (u - Suc l)"
by (simp_all add: icard_finite)

lemma icard_atLeast: "icard {(u::nat)..} = \<infinity>"
by (simp add: infinite_atLeast)

lemma icard_greaterThan: "icard {(u::nat)<..} = \<infinity>"
by (simp add: infinite_greaterThan)

lemma
  icard_atLeastZeroLessThan_int: "icard {0..<u} = enat (nat u)" and
  icard_atLeastLessThan_int: "icard {l..<u} = enat (nat (u - l))" and
  icard_atLeastAtMost_int: "icard {l..u} = enat (nat (u - l + 1))" and
  icard_greaterThanAtMost_int: "icard {l<..u} = enat (nat (u - l))"
by (simp_all add: icard_finite)

lemma icard_atLeast_int: "icard {(u::int)..} = \<infinity>"
by (simp add: infinite_atLeast_int)

lemma icard_greaterThan_int: "icard {(u::int)<..} = \<infinity>"
by (simp add: infinite_greaterThan_int)

lemma icard_atMost_int: "icard {..(u::int)} = \<infinity>"
by (simp add: infinite_atMost_int)

lemma icard_lessThan_int: "icard {..<(u::int)} = \<infinity>"
by (simp add: infinite_lessThan_int)

end
