(* Title: Resampling.thy
   Author: Andreas Lochbihler, ETH Zurich *)

theory Resampling imports
  While_SPMF
begin

lemma ord_spmf_lossless:
  assumes "ord_spmf (=) p q" "lossless_spmf p"
  shows "p = q"
  unfolding pmf.rel_eq[symmetric] using assms(1)
  by(rule pmf.rel_mono_strong)(use assms(2) in \<open>auto elim!: ord_option.cases simp add: lossless_iff_set_pmf_None\<close>)

context notes [[function_internals]] begin

partial_function (spmf) resample :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a spmf" where
  "resample A B = bind_spmf (spmf_of_set A) (\<lambda>x. if x \<in> B then return_spmf x else resample A B)"

end

lemmas resample_fixp_induct[case_names adm bottom step] = resample.fixp_induct

context
  fixes A :: "'a set"
  and B :: "'a set"
begin

interpretation loop_spmf "\<lambda>x. x \<notin> B" "\<lambda>_. spmf_of_set A" .

lemma resample_conv_while: "resample A B = bind_spmf (spmf_of_set A) while"
proof(induction rule: parallel_fixp_induct_2_1[OF partial_function_definitions_spmf partial_function_definitions_spmf resample.mono while.mono resample_def while_def, case_names adm bottom step])
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step resample' while') then show ?case by(simp add: z3_rule(33) cong del: if_cong)
qed

context
  assumes A: "finite A"
    and B: "B \<subseteq> A" "B \<noteq> {}"
begin

private lemma A_nonempty: "A \<noteq> {}"
  using B by blast

private lemma B_finite: "finite B"
  using A B by(blast intro: finite_subset)

lemma lossless_resample: "lossless_spmf (resample A B)"
proof -
  from B have [simp]: "A \<inter> B \<noteq> {}" by auto
  have "lossless_spmf (while x)" for x
    by(rule termination_0_1_immediate[where p="card (A \<inter> B) / card A"])
      (simp_all add: spmf_map vimage_def measure_spmf_of_set field_simps A_nonempty A not_le card_gt_0_iff B)
  then show ?thesis by(clarsimp simp add: resample_conv_while A A_nonempty)
qed

lemma resample_le_sample:
  "ord_spmf (=) (resample A B) (spmf_of_set B)"
proof(induction rule: resample_fixp_induct)
  case adm show ?case by simp
  case bottom show ?case by simp
  case (step resample')
  note [simp] = B_finite A
  show ?case
  proof(rule ord_pmf_increaseI)
    fix x
    let ?f = "\<lambda>x. if x \<in> B then return_spmf x else resample' A B"
    have "spmf (bind_spmf (spmf_of_set A) ?f) x =
      (\<Sum>n\<in>B \<union> (A - B). if n \<in> B then (if n = x then 1 else 0) / card A else spmf (resample' A B) x / card A)"
      using B
      by(auto simp add: spmf_bind integral_spmf_of_set sum_divide_distrib if_distrib[where f="\<lambda>p. spmf p _ / _"] cong: if_cong intro!: sum.cong split: split_indicator_asm)
    also have "\<dots> = (\<Sum>n\<in>B. (if n = x then 1 else 0) / card A) + (\<Sum>n\<in>A - B. spmf (resample' A B) x / card A)"
      by(subst sum.union_disjoint)(auto)
    also have "\<dots> = (if x \<in> B then 1 / card A else 0) + card (A - B) / card A * spmf (resample' A B) x"
      by(simp cong: sum.cong add: if_distrib[where f="\<lambda>x. x / _"] cong: if_cong)
    also have "\<dots> \<le> (if x \<in> B then 1 / card A else 0) + card (A - B) / card A * spmf (spmf_of_set B) x"
      by(intro add_left_mono mult_left_mono step.IH[THEN ord_spmf_eq_leD]) simp
    also have "\<dots> = spmf (spmf_of_set B) x" using B
      by(simp add: spmf_of_set field_simps A_nonempty card_Diff_subset card_mono of_nat_diff)
    finally show "spmf (bind_spmf (spmf_of_set A) ?f) x \<le> \<dots>" .
  qed simp
qed

lemma resample_eq_sample: "resample A B = spmf_of_set B"
  using resample_le_sample lossless_resample by(rule ord_spmf_lossless)

end

end

end