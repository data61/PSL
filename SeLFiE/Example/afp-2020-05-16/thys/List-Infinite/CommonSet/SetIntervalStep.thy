(*  Title:      SetIntervalStep.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Stepping through sets of natural numbers\<close>

theory SetIntervalStep
imports SetIntervalCut
begin

subsection \<open>Function \<open>inext\<close> and \<open>iprev\<close> for stepping through natural sets\<close>

definition inext :: "nat \<Rightarrow> nat set \<Rightarrow> nat"
where
  "inext n I \<equiv> (
    if (n \<in> I \<and> (I \<down>> n \<noteq> {}))
    then iMin (I \<down>> n)
    else n)"

definition iprev :: "nat \<Rightarrow> nat set \<Rightarrow> nat"
where
  "iprev n I \<equiv> (
    if (n \<in> I \<and> (I \<down>< n \<noteq> {}))
    then Max (I \<down>< n)
    else n)"

text \<open>\<open>inext\<close> and \<open>iprev\<close> can be viewed as generalisations of \<open>Suc\<close> and \<open>prev\<close>\<close>

lemma inext_UNIV: "inext n UNIV = Suc n"
apply (simp add: inext_def cut_greater_def, safe)
apply (rule iMin_equality)
apply fastforce+
done
lemma iprev_UNIV: "iprev n UNIV = n - Suc 0"
apply (simp add: iprev_def cut_less_def, safe)
apply (rule Max_equality)
apply fastforce+
done

lemma inext_empty: "inext n {} = n"
unfolding inext_def by simp
lemma iprev_empty: "iprev n {} = n"
unfolding iprev_def by simp

lemma not_in_inext_fix: "n \<notin> I \<Longrightarrow> inext n I = n"
unfolding inext_def by simp
lemma not_in_iprev_fix: "n \<notin> I \<Longrightarrow> iprev n I = n"
unfolding iprev_def by simp


lemma inext_all_le_fix: "\<forall>x\<in>I. x \<le> n \<Longrightarrow> inext n I = n"
unfolding inext_def by force
lemma iprev_all_ge_fix: "\<forall>x\<in>I. n \<le> x \<Longrightarrow> iprev n I = n"
unfolding iprev_def by force

lemma inext_Max: "finite I \<Longrightarrow> inext (Max I) I = Max I"
unfolding inext_def cut_greater_def by (fastforce dest: Max_ge)
lemma iprev_iMin: "iprev (iMin I) I = iMin I"
unfolding iprev_def cut_less_def by fastforce

lemma inext_ge_Max: "\<lbrakk> finite I; Max I \<le> n \<rbrakk> \<Longrightarrow> inext n I = n"
unfolding inext_def cut_greater_def by (fastforce dest: Max_ge)

lemma iprev_le_iMin: "n \<le> iMin I \<Longrightarrow> iprev n I = n"
unfolding iprev_def cut_less_def by fastforce

lemma inext_singleton: "inext n {a} = n"
unfolding inext_def by fastforce

lemma iprev_singleton: "iprev n {a} = n"
unfolding iprev_def by fastforce

lemma inext_closed: "n \<in> I \<Longrightarrow> inext n I \<in> I"
apply (clarsimp simp: inext_def)
apply (rule subsetD[OF cut_greater_subset])
apply (rule iMinI_ex2, assumption)
done

lemma iprev_closed: "n \<in> I \<Longrightarrow> iprev n I \<in> I"
apply (clarsimp simp: iprev_def)
apply (rule subsetD[of "I \<down>< n"], fastforce)
by (rule Max_in[OF nat_cut_less_finite])

lemma inext_in_imp_in: "inext n I \<in> I \<Longrightarrow> n \<in> I"
by (case_tac "n \<in> I", simp_all add: not_in_inext_fix)

lemma inext_in_iff: "(inext n I \<in> I) = (n \<in> I)"
apply (rule iffI)
apply (rule inext_in_imp_in, assumption)
apply (rule inext_closed, assumption)
done

lemma subset_inext_closed: "\<lbrakk> n \<in> B; A \<subseteq> B \<rbrakk> \<Longrightarrow> inext n A \<in> B"
apply (case_tac "n \<in> A")
 apply (fastforce simp: inext_closed)
apply (simp add: not_in_inext_fix)
done
lemma subset_inext_in_imp_in: "\<lbrakk> inext n A \<in> B; A \<subseteq> B \<rbrakk> \<Longrightarrow> n \<in> B"
apply (case_tac "n \<in> A")
 apply fastforce
apply (simp add: not_in_inext_fix)
done
lemma subset_inext_in_iff: "A \<subseteq> B \<Longrightarrow> (inext n A \<in> B) = (n \<in> B)"
apply (rule iffI)
apply (rule subset_inext_in_imp_in, assumption+)
apply (rule subset_inext_closed, assumption+)
done

lemma iprev_in_imp_in: "iprev n I \<in> I \<Longrightarrow> n \<in> I"
apply (case_tac "n \<in> I")
apply (simp_all add: not_in_iprev_fix)
done

lemma iprev_in_iff: "(iprev n I \<in> I) = (n \<in> I)"
apply (rule iffI)
apply (rule iprev_in_imp_in, assumption)
apply (rule iprev_closed, assumption)
done

lemma subset_iprev_closed: "\<lbrakk> n \<in> B; A \<subseteq> B \<rbrakk> \<Longrightarrow> iprev n A \<in> B"
apply (case_tac "n \<in> A")
 apply (fastforce simp: iprev_closed)
apply (simp add: not_in_iprev_fix)
done

lemma subset_iprev_in_imp_in: "\<lbrakk> iprev n A \<in> B; A \<subseteq> B \<rbrakk> \<Longrightarrow> n \<in> B"
apply (case_tac "n \<in> A")
 apply fastforce
apply (simp add: not_in_iprev_fix)
done

lemma subset_iprev_in_iff: "A \<subseteq> B \<Longrightarrow> (iprev n A \<in> B) = (n \<in> B)"
apply (rule iffI)
apply (rule subset_iprev_in_imp_in, assumption+)
apply (rule subset_iprev_closed, assumption+)
done

lemma inext_mono: "n \<le> inext n I"
by (simp add: inext_def i_cut_defs iMin_ge_iff)

corollary inext_neq_imp_less: "n \<noteq> inext n I \<Longrightarrow> n < inext n I"
by (insert inext_mono[of n I], simp)

lemma inext_mono2: "\<lbrakk> n \<in> I; \<exists>x\<in>I. n < x \<rbrakk> \<Longrightarrow> n < inext n I"
by (fastforce simp add: inext_def i_cut_defs iMin_gr_iff)

lemma inext_mono2_infin: "\<lbrakk> n \<in> I; infinite I \<rbrakk> \<Longrightarrow> n < inext n I"
apply (simp add: inext_def i_cut_defs iMin_gr_iff)
apply (fastforce simp: infinite_nat_iff_unbounded)
done

lemma inext_mono2_fin: "\<lbrakk> n \<in> I; finite I; n \<noteq> Max I \<rbrakk> \<Longrightarrow> n < inext n I"
apply (simp add: inext_def i_cut_defs iMin_gr_iff)
apply (blast intro: Max_ge Max_in)
done

lemma inext_mono2_infin_fin: "
  \<lbrakk> n \<in> I; n \<noteq> Max I \<or> infinite I \<rbrakk> \<Longrightarrow> n < inext n I"
by (blast intro: inext_mono2_infin inext_mono2_fin)

lemma inext_neq_iMin: "\<exists>x\<in>I. n < x \<Longrightarrow> inext n I \<noteq> iMin I"
apply (case_tac "n \<in> I")
 prefer 2
 apply (simp add: not_in_inext_fix)
 apply (blast dest: iMinI)
apply (rule not_sym, rule less_imp_neq)
by (rule le_less_trans[OF iMin_le[of n], OF _ inext_mono2])

lemma inext_neq_iMin_infin: "infinite I \<Longrightarrow> inext n I \<noteq> iMin I"
apply (rule inext_neq_iMin)
apply (blast dest: infinite_nat_iff_unbounded[THEN iffD1])
done

lemma Max_le_iMin_imp_singleton: "\<lbrakk> finite I; I \<noteq> {}; Max I \<le> iMin I \<rbrakk> \<Longrightarrow> I = {iMin I}"
by (simp add: iMin_Min_conv Max_le_Min_imp_singleton)

lemma inext_neq_iMin_not_singleton: "
  \<lbrakk> I \<noteq> {}; \<not>(\<exists>a. I = {a}) \<rbrakk> \<Longrightarrow> inext n I \<noteq> iMin I"
apply (case_tac "finite I")
 prefer 2
 apply (simp add: inext_neq_iMin_infin)
apply (case_tac "n \<in> I")
 prefer 2
 apply (simp add: not_in_inext_fix)
 apply (blast intro: iMinI_ex2)
by (metis Max_le_iMin_imp_singleton iMin_le_Max inext_Max inext_mono2_infin_fin not_less_iMin)
corollary inext_neq_iMin_not_card_1: "
  \<lbrakk> I \<noteq> {}; card I \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> inext n I \<noteq> iMin I"
by (simp add: inext_neq_iMin_not_singleton card_1_singleton_conv)

lemma inext_neq_imp_Max: "n \<noteq> inext n I \<Longrightarrow> n < Max I \<or> infinite I"
by (rule ccontr, clarsimp simp: inext_ge_Max)

lemma inext_less_conv: "(n \<in> I \<and> (n < Max I \<or> infinite I)) = (n < inext n I)"
apply (rule iffI)
 apply (blast intro: inext_mono2_infin_fin)
apply (rule conjI)
 apply (rule ccontr)
 apply (simp add: not_in_inext_fix)
apply (blast dest: inext_neq_imp_Max less_imp_neq)
done

lemma inext_min_step: "\<lbrakk> n < k; k < inext n I \<rbrakk> \<Longrightarrow> k \<notin> I"
apply (case_tac "n \<in> I")
 prefer 2
 apply (simp add: inext_def)
apply (rule contrapos_pn[of "k < inext n I" "k \<in> I"], simp)
apply (simp add: inext_def i_cut_defs)
apply (case_tac "\<exists>x. x \<in> I \<and> n < x")
 apply simp
 apply (blast dest: not_less_iMin)
apply blast
done

corollary inext_min_step2: "\<not>(\<exists>k\<in>I. n < k \<and> k < inext n I)"
by (clarsimp simp add: inext_min_step)

lemma min_step_inext[rule_format]: "
  \<lbrakk> x < y; x \<in> I; y \<in> I; \<And>k. \<lbrakk> x < k; k < y \<rbrakk> \<Longrightarrow> k \<notin> I \<rbrakk> \<Longrightarrow>
  inext x I = y"
apply (rule ccontr)
apply (simp add: nat_neq_iff, safe)
apply (blast dest: inext_closed inext_mono2)
apply (simp add: inext_min_step)
done

corollary min_step_inext2[rule_format]: "
  \<lbrakk> x < y; x \<in> I; y \<in> I; \<not>(\<exists>k \<in> I. x < k \<and> k < y) \<rbrakk> \<Longrightarrow>
  inext x I = y"
by (blast intro: min_step_inext)
lemma between_empty_imp_inext_eq: "
  \<lbrakk> n \<in> A; n < inext n A; n \<in> B; inext n A \<in> B; B \<down>> n \<down>< (inext n A) = {} \<rbrakk> \<Longrightarrow>
  inext n B = inext n A"
by (blast intro: min_step_inext2)




lemma inext_le_mono: "\<lbrakk> a \<le> b; a \<in> I; b \<in> I \<rbrakk> \<Longrightarrow> inext a I \<le> inext b I"
apply (drule order_le_less[THEN iffD1], erule disjE)
 prefer 2
 apply simp
apply (rule order_trans[of _ b])
 apply (rule ccontr, simp add: linorder_not_le)
 apply (blast dest: inext_min_step)
by (rule inext_mono)

lemma inext_less_mono: "
  \<lbrakk> a < b; a \<in> I; b \<in> I; \<exists>x\<in>I. b < x \<rbrakk> \<Longrightarrow> inext a I < inext b I"
apply (rule le_less_trans[of _ b])
 apply (rule ccontr, simp add: linorder_not_le)
 apply (blast dest: inext_min_step)
by (rule inext_mono2)

lemma inext_less_mono_fin: "
  \<lbrakk> a < b; a \<in> I; b \<in> I; finite I; b \<noteq> Max I \<rbrakk> \<Longrightarrow> inext a I < inext b I"
by (blast intro: inext_less_mono Max_in)

lemma inext_less_mono_infin: "
  \<lbrakk> a < b; a \<in> I; b \<in> I; infinite I \<rbrakk> \<Longrightarrow> inext a I < inext b I"
apply (rule inext_less_mono, assumption+)
apply (blast dest: infinite_imp_asc_chain)
done

lemma inext_less_mono_infin_fin: "
  \<lbrakk> a < b; a \<in> I; b \<in> I; b \<noteq> Max I \<or> infinite I \<rbrakk> \<Longrightarrow> inext a I < inext b I"
by (blast intro: inext_less_mono_infin inext_less_mono_fin)


lemma inext_le_mono_rev: "
  \<lbrakk> inext a I \<le> inext b I; a \<in> I; b \<in> I; \<exists>x\<in>I. inext a I < x \<rbrakk> \<Longrightarrow> a \<le> b"
apply (rule ccontr, simp add: linorder_not_le)
apply (frule inext_less_mono, assumption+)
 apply (blast intro: le_less_trans inext_mono)
apply simp
done

lemma inext_le_mono_fin_rev: "
  \<lbrakk> inext a I \<le> inext b I; a \<in> I; b \<in> I; finite I; inext a I \<noteq> Max I\<rbrakk> \<Longrightarrow> a \<le> b"
by (metis inext_in_iff inext_le_mono_rev inext_mono2_infin_fin)

lemma inext_le_mono_infin_rev: "
  \<lbrakk> inext a I \<le> inext b I; a \<in> I; b \<in> I; infinite I \<rbrakk> \<Longrightarrow> a \<le> b"
by (metis inext_in_iff inext_le_mono_rev inext_mono2_infin_fin)

lemma inext_le_mono_infin_fin_rev: "
  \<lbrakk> inext a I \<le> inext b I; a \<in> I; b \<in> I; inext a I \<noteq> Max I \<or> infinite I \<rbrakk> \<Longrightarrow> a \<le> b"
by (blast intro: inext_le_mono_infin_rev inext_le_mono_fin_rev)

lemma inext_less_mono_rev: "
  \<lbrakk> inext a I < inext b I; a \<in> I; b \<in> I \<rbrakk> \<Longrightarrow> a < b"
by (metis inext_le_mono not_le)

lemma less_imp_inext_le: "\<lbrakk> a < b; a \<in> I; b \<in> I \<rbrakk> \<Longrightarrow> inext a I \<le> b"
by (metis inext_min_step not_le)

lemma iprev_mono: "iprev n I \<le> n"
unfolding iprev_def i_cut_defs by simp
corollary iprev_neq_imp_greater: "n \<noteq> iprev n I \<Longrightarrow> iprev n I < n"
by (insert iprev_mono[of n I], simp)

lemma iprev_mono2: "\<lbrakk> n \<in> I; \<exists>x\<in>I. x < n\<rbrakk> \<Longrightarrow> iprev n I < n"
apply (unfold iprev_def i_cut_defs, clarsimp)
apply (blast intro: finite_nat_iff_bounded)+
done

lemma iprev_mono2_if_neq_iMin: "\<lbrakk> n \<in> I; iMin I \<noteq> n\<rbrakk> \<Longrightarrow> iprev n I < n"
by (blast intro: iMinI iprev_mono2)

lemma iprev_neq_Max: "\<lbrakk> finite I; \<exists>x\<in>I. x < n \<rbrakk>  \<Longrightarrow> iprev n I \<noteq> Max I"
apply (case_tac "n \<in> I")
 prefer 2
 apply (simp add: not_in_iprev_fix)
 apply (blast dest: Max_in)
apply (rule less_imp_neq)
by (rule less_le_trans[OF iprev_mono2 Max_ge])

lemma iprev_neq_Max_not_singleton: "
  \<lbrakk> finite I; I \<noteq> {}; \<not>(\<exists>a. I = {a}) \<rbrakk> \<Longrightarrow> iprev n I \<noteq> Max I"
apply (case_tac "n \<in> I")
 prefer 2
 apply (simp add: not_in_iprev_fix)
 apply (blast intro: Max_in)
apply (case_tac "n = iMin I")
 apply (metis Max_le_Min_conv_singleton iMin_Min_conv iMin_le_Max iprev_iMin)
apply (metis iprev_mono2_if_neq_iMin not_greater_Max)
done
corollary iprev_neq_Max_not_card_1: "
  \<lbrakk> finite I; I \<noteq> {}; card I \<noteq> Suc 0 \<rbrakk> \<Longrightarrow> iprev n I \<noteq> Max I"
apply (rule iprev_neq_Max_not_singleton, assumption+)
apply (simp add: card_1_singleton_conv)
done

lemma iprev_neq_imp_iMin: "iprev n I \<noteq> n \<Longrightarrow> iMin I < n"
by (rule ccontr, clarsimp simp: iprev_le_iMin)

lemma iprev_greater_conv: "(n \<in> I \<and> iMin I < n) = (iprev n I < n)"
apply (rule iffI)
 apply (blast intro: iprev_mono2_if_neq_iMin)
apply (rule conjI)
 apply (rule ccontr)
 apply (simp add: not_in_iprev_fix)
apply (blast dest: iprev_neq_imp_iMin less_imp_neq)
done

lemma inext_fix_iff: "(n \<notin> I \<or> (finite I \<and> Max I = n)) = (inext n I = n)"
apply (case_tac "n \<notin> I", simp add: not_in_inext_fix)
by (metis inext_Max inext_min_step2 inext_mono2_infin_fin)

lemma iprev_fix_iff: "(n \<notin> I \<or> iMin I = n) = (iprev n I = n)"
apply (case_tac "n \<notin> I", simp add: not_in_iprev_fix)
by (metis iprev_iMin iprev_mono2_if_neq_iMin less_not_refl3)

lemma iprev_min_step: "\<lbrakk> iprev n I < k; k < n \<rbrakk> \<Longrightarrow> k \<notin> I"
apply (case_tac "n \<in> I")
 prefer 2
 apply (simp add: iprev_def)
apply (rule contrapos_pn[of "iprev n I < k" "k \<in> I"], simp)
apply (unfold iprev_def i_cut_defs, simp)
apply (split if_split_asm)
apply (cut_tac Max_ge[of "{x \<in> I. x < n}" k])
apply fastforce+
done

corollary iprev_min_step2: "\<not>(\<exists>x\<in>I. iprev n I < x \<and> x < n)"
by (clarsimp simp add: iprev_min_step)

lemma min_step_iprev: "
  \<lbrakk> x < y; x \<in> I; y \<in> I; \<And>k. \<lbrakk> x < k; k < y \<rbrakk> \<Longrightarrow> k \<notin> I \<rbrakk> \<Longrightarrow>
  iprev y I = x"
apply (rule ccontr)
apply (simp add: nat_neq_iff, elim disjE)
 apply (simp add: iprev_min_step)
apply (blast dest: iprev_closed iprev_mono2 iprev_min_step)
done

corollary min_step_iprev2[rule_format]: "
  \<lbrakk> x < y; x \<in> I; y \<in> I; \<not>(\<exists>k \<in> I. x < k \<and> k < y) \<rbrakk> \<Longrightarrow>
  iprev y I = x"
by (blast intro: min_step_iprev)

lemma between_empty_imp_iprev_eq: "
  \<lbrakk> n \<in> A; iprev n A < n; n \<in> B; iprev n A \<in> B; B \<down>> (iprev n A) \<down>< n = {} \<rbrakk> \<Longrightarrow>
  iprev n B = iprev n A"
by (blast intro: min_step_iprev2)



lemma iprev_le_mono: "\<lbrakk> a \<le> b; a \<in> I; b \<in> I \<rbrakk> \<Longrightarrow> iprev a I \<le> iprev b I"
apply (drule order_le_less[THEN iffD1], erule disjE)
 prefer 2
 apply simp
apply (rule order_trans[OF iprev_mono])
 apply (rule ccontr, simp add: linorder_not_le)
by (blast dest: iprev_min_step)

lemma iprev_less_mono: "
  \<lbrakk> a < b; a \<in> I; b \<in> I; \<exists>x\<in>I. x < a \<rbrakk> \<Longrightarrow> iprev a I < iprev b I"
apply (rule less_le_trans[of _ a])
 apply (blast intro: iprev_mono2)
apply (rule ccontr, simp add: linorder_not_le)
by (blast dest: iprev_min_step)

lemma iprev_less_mono_if_neq_iMin: "
  \<lbrakk> a < b; a \<in> I; b \<in> I; iMin I \<noteq> a \<rbrakk> \<Longrightarrow> iprev a I < iprev b I"
by (metis iprev_in_iff iprev_less_mono iprev_mono2_if_neq_iMin)

lemma iprev_le_mono_rev: "
  \<lbrakk> iprev a I \<le> iprev b I; a \<in> I; b \<in> I; iMin I \<noteq> iprev b I \<rbrakk> \<Longrightarrow> a \<le> b"
apply (rule ccontr, simp add: linorder_not_le)
by (metis iprev_fix_iff iprev_less_mono_if_neq_iMin less_le_not_le)

lemma iprev_less_mono_rev: "
  \<lbrakk> iprev a I < iprev b I; a \<in> I; b \<in> I \<rbrakk> \<Longrightarrow> a < b"
apply (rule ccontr, simp add: linorder_not_less)
by (metis iprev_le_mono less_le_not_le)



lemma set_restriction_inext_eq: "
  \<lbrakk> set_restriction interval_fun; n \<in> interval_fun I; inext n I \<in> interval_fun I \<rbrakk> \<Longrightarrow>
  inext n (interval_fun I) = inext n I"
apply (subgoal_tac "n \<in> I")
 prefer 2
 apply (blast intro: set_restriction_in_imp)
apply (case_tac "inext n I = n")
 apply simp
 apply (frule inext_fix_iff[THEN iffD2], clarsimp)
 apply (frule set_restriction_finite, assumption)
 apply (subgoal_tac "Max (interval_fun I) = Max I")
  prefer 2
  apply (blast intro: Max_equality Max_ge set_restriction_in_imp)
 apply (blast intro: inext_fix_iff[THEN iffD1])
apply (drule le_neq_implies_less[OF inext_mono, OF not_sym])
apply (rule between_empty_imp_inext_eq, assumption+)
apply (simp add: not_ex_in_conv[symmetric] i_cut_mem_iff)
by (metis inext_min_step2 set_restriction_in_imp)

lemma set_restriction_inext_singleton_eq: "
  \<lbrakk> set_restriction interval_fun; n \<in> interval_fun I; inext n I \<in> interval_fun I \<rbrakk> \<Longrightarrow>
  {inext n (interval_fun I)} = interval_fun {inext n I}"
apply (case_tac "n \<notin> I")
 apply (blast dest: set_restriction_not_in_imp)
apply (frule set_restrictionD, erule exE, rename_tac P)
apply (simp add: singleton_iff set_eq_iff)
by (metis set_restriction_inext_eq)



lemma inext_iprev: "iMin I \<noteq> n \<Longrightarrow> inext (iprev n I) I = n"
apply (case_tac "n \<notin> I")
 apply (simp add: inext_def iprev_def)
apply simp
apply (frule iMin_neq_imp_greater[OF _ not_sym], assumption)
apply (blast dest: iMinI iprev_min_step intro: min_step_inext iprev_mono2 iprev_closed)
done

lemma iprev_inext_infin: "infinite I \<Longrightarrow> iprev (inext n I) I = n"
apply (case_tac "n \<notin> I")
 apply (simp add: inext_def iprev_def)
apply simp
by (metis inext_in_iff inext_min_step2 inext_mono2_infin_fin min_step_iprev2)

lemma iprev_inext_fin: "
  \<lbrakk> finite I; n \<noteq> Max I \<rbrakk> \<Longrightarrow> iprev (inext n I) I = n"
apply (case_tac "n \<notin> I")
 apply (simp add: inext_def iprev_def)
apply simp
by (metis inext_in_iff inext_min_step2 inext_mono2_infin_fin min_step_iprev2)

lemma iprev_inext: "
  n \<noteq> Max I \<or> infinite I \<Longrightarrow> iprev (inext n I) I = n"
by (blast intro: iprev_inext_infin iprev_inext_fin)

lemma inext_eq_infin: "
  \<lbrakk> inext a I = inext b I; infinite I \<rbrakk> \<Longrightarrow> a = b"
apply (drule arg_cong[where f="\<lambda>x. iprev x I"])
apply (simp add: iprev_inext_infin)
done

lemma inext_eq_fin: "
  \<lbrakk> inext a I = inext b I; finite I; a \<noteq> Max I; b \<noteq> Max I \<rbrakk> \<Longrightarrow> a = b"
apply (drule arg_cong[where f="\<lambda>x. iprev x I"])
apply (simp add: iprev_inext_fin)
done

lemma inext_eq_infin_fin: "
  \<lbrakk> inext a I = inext b I; a \<noteq> Max I \<and> b \<noteq> Max I \<or> infinite I \<rbrakk> \<Longrightarrow> a = b"
by (blast intro: inext_eq_fin inext_eq_infin)+

lemma inext_eq: "
  \<lbrakk> inext a I = inext b I; \<exists>x\<in>I. a < x; \<exists>x\<in>I. b < x \<rbrakk> \<Longrightarrow> a = b"
by (metis iprev_inext not_le wellorder_Max_lemma)

lemma iprev_eq_if_neq_iMin: "
  \<lbrakk> iprev a I = iprev b I; iMin I \<noteq> a; iMin I \<noteq> b \<rbrakk> \<Longrightarrow> a = b"
apply (drule arg_cong[where f="\<lambda>x. inext x I"])
apply (simp add: inext_iprev)
done

lemma iprev_eq: "
  \<lbrakk> iprev a I = iprev b I; \<exists>x\<in>I. x < a; \<exists>x\<in>I. x < b \<rbrakk> \<Longrightarrow> a = b"
by (metis iprev_eq_if_neq_iMin not_less_iMin)

lemma greater_imp_iprev_ge: "\<lbrakk> b < a; a \<in> I; b \<in> I \<rbrakk> \<Longrightarrow> b \<le> iprev a I"
apply (rule ccontr, simp add: linorder_not_le)
apply (blast dest: iprev_min_step)
done


lemma inext_cut_less_conv: "inext n I < t \<Longrightarrow> inext n (I \<down>< t) = inext n I"
apply (frule le_less_trans[OF inext_mono])
apply (case_tac "n \<in> I")
 apply (simp add: inext_def)
 apply (simp add: i_cut_commute_disj[of "(\<down><)" "(\<down>>)"] cut_less_mem_iff)
 apply (case_tac "I \<down>> n \<noteq> {}")
  apply simp
  apply (metis cut_less_Min_eq cut_less_Min_not_empty)
 apply (simp add: i_cut_empty)
apply (simp add: not_in_inext_fix cut_less_not_in_imp)
done

lemma inext_cut_le_conv: "inext n I \<le> t \<Longrightarrow> inext n (I \<down>\<le> t) = inext n I"
by (simp add: nat_cut_le_less_conv inext_cut_less_conv)

lemma inext_cut_greater_conv: "t < n \<Longrightarrow> inext n (I \<down>> t) = inext n I"
apply (case_tac "n \<in> I")
 apply (frule cut_greater_mem_iff[THEN iffD2, OF conjI], simp)
 apply (simp add: inext_def i_cut_commute_disj[of "(\<down>>)" "(\<down>>)"] cut_cut_greater max_def)
apply (simp add: not_in_inext_fix cut_greater_not_in_imp)
done

lemma inext_cut_ge_conv: "t \<le> n \<Longrightarrow> inext n (I \<down>\<ge> t) = inext n I"
apply (case_tac "t = 0")
 apply (simp add: cut_ge_0_all)
apply (simp add: nat_cut_greater_ge_conv[symmetric] inext_cut_greater_conv)
done

lemmas inext_cut_conv =
  inext_cut_less_conv inext_cut_le_conv
  inext_cut_greater_conv inext_cut_ge_conv



lemma iprev_cut_greater_conv: "t < iprev n I \<Longrightarrow> iprev n (I \<down>> t) = iprev n I"
apply (frule less_le_trans[OF _ iprev_mono])
apply (case_tac "n \<in> I")
 apply (simp add: iprev_def)
 apply (simp add: i_cut_commute_disj[of "(\<down>>)" "(\<down><)"] cut_greater_mem_iff)
 apply (case_tac "I \<down>< n \<noteq> {}")
  apply simp
  apply (metis cut_greater_Max_eq cut_greater_Max_not_empty nat_cut_less_finite)
 apply (simp add: i_cut_empty)
apply (simp add: not_in_iprev_fix cut_greater_not_in_imp)
done

lemma iprev_cut_ge_conv: "t \<le> iprev n I \<Longrightarrow> iprev n (I \<down>\<ge> t) = iprev n I"
apply (case_tac "t = 0")
 apply (simp add: cut_ge_0_all)
apply (simp add: nat_cut_greater_ge_conv[symmetric] iprev_cut_greater_conv)
done

lemma iprev_cut_less_conv: "n < t \<Longrightarrow> iprev n (I \<down>< t) = iprev n I"
apply (case_tac "n \<in> I")
 apply (frule cut_less_mem_iff[THEN iffD2, OF conjI], simp)
 apply (simp add: iprev_def i_cut_commute_disj[of "(\<down><)" "(\<down><)"] cut_cut_less min_def)
apply (simp add: not_in_iprev_fix cut_less_not_in_imp)
done

lemma iprev_cut_le_conv: "n \<le> t \<Longrightarrow> iprev n (I \<down>\<le> t) = iprev n I"
by (simp add: nat_cut_le_less_conv iprev_cut_less_conv)

lemmas iprev_cut_conv =
  iprev_cut_less_conv iprev_cut_le_conv
  iprev_cut_greater_conv iprev_cut_ge_conv

lemma inext_cut_less_fix: "t \<le> inext n I \<Longrightarrow> inext n (I \<down>< t) = n"
apply (case_tac "n \<in> I")
 prefer 2
 apply (frule contra_subsetD[OF cut_less_subset[of _ t]])
 apply (simp add: not_in_inext_fix)
apply (case_tac "t \<le> n")
 apply (metis cut_less_mem_iff not_in_inext_fix not_le)
apply (rule_tac t=n and s="Max (I \<down>< t)" in subst)
 apply (rule Max_equality[OF _ nat_cut_less_finite])
  apply (simp add: cut_less_mem_iff)
 apply (rule ccontr)
 apply (clarsimp simp: cut_less_mem_iff linorder_not_le)
 apply (simp add: inext_min_step)
apply (blast intro: inext_Max nat_cut_less_finite)
done

lemma inext_cut_le_fix: "t < inext n I \<Longrightarrow> inext n (I \<down>\<le> t) = n"
by (simp add: nat_cut_le_less_conv inext_cut_less_fix)

lemma iprev_cut_greater_fix: "iprev n I \<le> t \<Longrightarrow> iprev n (I \<down>> t) = n"
apply (case_tac "n \<in> I")
 prefer 2
 apply (frule contra_subsetD[OF cut_greater_subset[of _ t]])
 apply (simp add: not_in_iprev_fix)
apply (case_tac "n \<le> t")
 apply (metis cut_greater_mem_iff not_in_iprev_fix not_le)
apply (rule_tac t=n and s="iMin (I \<down>> t)" in subst)
 apply (rule iMin_equality)
  apply (simp add: cut_greater_mem_iff)
 apply (metis cut_greater_mem_iff iprev_min_step2 not_le_imp_less order_le_less_trans)
apply (rule iprev_iMin)
done

lemma iprev_cut_ge_fix: "iprev n I < t \<Longrightarrow> iprev n (I \<down>\<ge> t) = n"
apply (case_tac "t = 0")
 apply (simp add: cut_ge_0_all)
apply (simp add: nat_cut_greater_ge_conv[symmetric] iprev_cut_greater_fix)
done

definition
  CommuteWithIntervalCut4 :: "(('a::linorder) set \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "CommuteWithIntervalCut4 fun \<equiv>
  \<forall>t fun2 I.
  (fun2 = (\<lambda>I. I \<down>< t) \<or> fun2 = (\<lambda>I. I \<down>\<le> t) \<or> fun2 = (\<lambda>I. I \<down>> t) \<or> fun2 = (\<lambda>I. I \<down>\<ge> t) ) \<longrightarrow>
  fun (fun2 I) = fun2 (fun I)"
definition CommuteWithIntervalCut2 :: "(('a::linorder) set \<Rightarrow> 'a set) \<Rightarrow> bool"
where
  "CommuteWithIntervalCut2 fun \<equiv>
  \<forall>t fun2 I.
  (fun2 = (\<lambda>I. I \<down>< t) \<or> fun2 = (\<lambda>I. I \<down>> t)) \<longrightarrow>
  fun (fun2 I) = fun2 (fun I)"

lemma CommuteWithIntervalCut4_imp_2: "CommuteWithIntervalCut4 fun \<Longrightarrow> CommuteWithIntervalCut2 fun"
unfolding CommuteWithIntervalCut2_def CommuteWithIntervalCut4_def by blast

lemma nat_CommuteWithIntervalCut2_4_eq: "
  CommuteWithIntervalCut4 (fun::nat set \<Rightarrow> nat set) = CommuteWithIntervalCut2 fun"
apply (unfold CommuteWithIntervalCut2_def CommuteWithIntervalCut4_def)
apply (rule iffI)
 apply blast
apply clarify
apply (case_tac "fun2 = (\<lambda>I. I \<down>< t)", simp)
apply (case_tac "fun2 = (\<lambda>I. I \<down>> t)", simp)
apply simp
apply (erule disjE)
 apply (simp add: nat_cut_le_less_conv)
apply (case_tac "t = 0")
 apply (simp add: cut_ge_0_all)
apply (simp add: nat_cut_greater_ge_conv[symmetric])
done

lemma
  cut_less_CommuteWithIntervalCut4:    "CommuteWithIntervalCut4 (\<lambda>I. I \<down>< t)" and
  cut_le_CommuteWithIntervalCut4:      "CommuteWithIntervalCut4 (\<lambda>I. I \<down>\<le> t)" and
  cut_greater_CommuteWithIntervalCut4: "CommuteWithIntervalCut4 (\<lambda>I. I \<down>> t)" and
  cut_ge_CommuteWithIntervalCut4:      "CommuteWithIntervalCut4 (\<lambda>I. I \<down>\<ge> t)"
unfolding CommuteWithIntervalCut4_def by (simp_all add: i_cut_commute_disj)

lemmas i_cut_CommuteWithIntervalCut4 =
  cut_less_CommuteWithIntervalCut4 cut_le_CommuteWithIntervalCut4
  cut_greater_CommuteWithIntervalCut4 cut_ge_CommuteWithIntervalCut4

lemma inext_image: "
  \<lbrakk> n \<in> I; strict_mono_on f I \<rbrakk> \<Longrightarrow> inext (f n) (f ` I) = f (inext n I)"
apply (case_tac "\<exists>x\<in>I. n < x")
 apply (frule inext_mono2, assumption)
 apply (frule cut_greater_not_empty_iff[THEN iffD2])
 apply (simp add: inext_def image_iff)
 apply (subgoal_tac "\<exists>x\<in>I. f n = f x")
  prefer 2
  apply blast
 apply (simp add: cut_greater_image)
 apply (blast intro: strict_mono_on_subset iMin_mono_on2 strict_mono_on_imp_mono_on)
apply (drule strict_mono_on_imp_mono_on)
apply (simp add: inext_all_le_fix linorder_not_less mono_on_def)
done

lemma iprev_image: "
  \<lbrakk> n \<in> I; strict_mono_on f I \<rbrakk> \<Longrightarrow> iprev (f n) (f ` I) = f (iprev n I)"
apply (case_tac "\<exists>x\<in>I. x < n")
 apply (frule iprev_mono2, assumption)
 apply (frule cut_less_not_empty_iff[THEN iffD2])
 apply (simp add: iprev_def image_iff)
 apply (subgoal_tac "\<exists>x\<in>I. f n = f x")
  prefer 2
  apply blast
 apply (simp add: cut_less_image)
 apply (blast intro: strict_mono_on_subset Max_mono_on2 strict_mono_on_imp_mono_on nat_cut_less_finite)
apply (drule strict_mono_on_imp_mono_on)
apply (simp add: iprev_all_ge_fix linorder_not_less mono_on_def)
done

lemma inext_image2: "
  strict_mono f \<Longrightarrow> inext (f n) (f ` I) = f (inext n I)"
apply (case_tac "n \<in> I")
 apply (blast intro: strict_mono_imp_strict_mono_on inext_image)
apply (simp add: not_in_inext_fix inj_image_mem_iff strict_mono_imp_inj)
done

lemma iprev_image2: "
  strict_mono f \<Longrightarrow> iprev (f n) (f ` I) = f (iprev n I)"
apply (case_tac "n \<in> I")
 apply (blast intro: strict_mono_imp_strict_mono_on iprev_image)
apply (simp add: not_in_iprev_fix inj_image_mem_iff strict_mono_imp_inj)
done


lemma inext_imirror_iprev_conv: "
  \<lbrakk> finite I; n \<le> iMin I + Max I \<rbrakk> \<Longrightarrow>
  inext (mirror_elem n I) (imirror I) = mirror_elem (iprev n I) I"
apply (case_tac "n \<in> I")
 prefer 2
 apply (simp add: not_in_iprev_fix not_in_inext_fix imirror_mem_conv)
apply (frule in_imp_not_empty[of _ I])
apply (frule in_imp_mirror_elem_in[of _ n], assumption)
apply (simp add: inext_def iprev_def)
apply (case_tac "n = iMin I")
 apply (simp add: cut_less_Min_empty mirror_elem_Min)
 apply (subst imirror_Max[symmetric], assumption)
 apply (simp add: cut_greater_Max_empty imirror_finite)
apply (frule iMin_le[of n I])
apply (intro conjI impI)
  apply (simp add: imirror_cut_greater')
  apply (simp add: imirror_bounds_iMin nat_cut_less_finite cut_less_Min_eq)
  apply (simp add: mirror_elem_def nat_mirror_def)
 apply (simp add: imirror_cut_greater')
 apply (simp add: imirror_bounds_def)
apply (simp add: cut_less_Min_not_empty)
done

corollary inext_imirror_iprev_conv': "
  \<lbrakk> finite I; n \<in> I \<rbrakk> \<Longrightarrow>
  inext (mirror_elem n I) (imirror I) = mirror_elem (iprev n I) I"
by (simp add: inext_imirror_iprev_conv trans_le_add2)

lemma iprev_imirror_inext_conv: "
  \<lbrakk> finite I; n \<le> iMin I + Max I \<rbrakk> \<Longrightarrow>
  iprev (mirror_elem n I) (imirror I) = mirror_elem (inext n I) I"
apply (case_tac "n \<in> I")
 prefer 2
 apply (simp add: not_in_iprev_fix not_in_inext_fix imirror_mem_conv)
apply (frule in_imp_not_empty[of _ I])
apply (frule in_imp_mirror_elem_in[of _ n], assumption)
apply (simp add: inext_def iprev_def)
apply (case_tac "n = Max I")
 apply (simp add: cut_greater_Max_empty mirror_elem_Max)
 apply (subst imirror_iMin[symmetric], assumption)
 apply (simp add: cut_less_Min_empty imirror_finite)
apply (frule Max_ge[of I n], assumption)
apply (drule le_neq_trans, assumption)
apply (intro conjI impI)
  apply (simp add: imirror_cut_less)
  apply (simp add: imirror_bounds_Max cut_greater_finite cut_greater_Max_eq del: Max_le_iff)
  apply (simp add: mirror_elem_def nat_mirror_def)
 apply (simp add: imirror_cut_less)
 apply (simp add: imirror_bounds_def)
apply (simp add: cut_greater_Max_not_empty)
done

corollary iprev_imirror_inext_conv': "
  \<lbrakk> finite I; n \<in> I \<rbrakk> \<Longrightarrow>
  iprev (mirror_elem n I) (imirror I) = mirror_elem (inext n I) I"
by (simp add: iprev_imirror_inext_conv trans_le_add2)

lemma inext_insert_ge_Max: "
  \<lbrakk> finite I; I \<noteq> {}; Max I \<le> a \<rbrakk> \<Longrightarrow> inext (Max I) (insert a I) = a"
apply (case_tac "a = Max I")
 apply (simp add: insert_absorb inext_Max)
apply (drule le_neq_trans, simp)
apply (rule min_step_inext2)
apply (simp, simp, simp)
apply (simp_all, blast?) (* blast is optional for the case, that the last goal could be solved by the simplifier in a future version, making the blast command superfluous. *)
done

lemma iprev_insert_le_iMin: "
  \<lbrakk> finite I; I \<noteq> {}; a \<le> iMin I \<rbrakk> \<Longrightarrow> iprev (iMin I) (insert a I) = a"
apply (case_tac "a = iMin I")
 apply (simp add: iMinI_ex2 insert_absorb iprev_iMin)
apply (drule le_neq_trans, simp)
apply (rule min_step_iprev2)
apply (simp_all add: iMin_Min_conv, blast?)
done

lemma cut_less_le_iprev_conv: "
  \<lbrakk> t \<in> I; t \<noteq> iMin I \<rbrakk> \<Longrightarrow> I \<down>< t = I \<down>\<le> (iprev t I)"
apply (unfold iprev_def)
apply (rule set_eqI, safe)
 apply (simp add: i_cut_defs)
apply simp
apply (split if_split_asm)
 apply (simp add: Max_ge_iff nat_cut_less_finite)
 apply (blast intro: le_less_trans)
apply (frule iMin_neq_imp_greater, assumption)
apply (blast intro: iMin_in)
done

lemma neq_Max_imp_inext_neq_iMin: "
  \<lbrakk> t \<in> I; t \<noteq> Max I \<or> infinite I \<rbrakk> \<Longrightarrow> inext t I \<noteq> iMin I"
apply (case_tac "finite I")
 apply (metis inext_mono2_infin_fin not_less_iMin)
apply (blast dest: inext_neq_iMin_infin)
done

corollary neq_Max_imp_inext_gr_iMin: "
  \<lbrakk> t \<in> I; t \<noteq> Max I \<or> infinite I\<rbrakk> \<Longrightarrow> iMin I < inext t I"
apply (frule neq_Max_imp_inext_neq_iMin[THEN not_sym], assumption)
apply (drule neq_le_trans)
 apply (blast dest: inext_closed)
apply simp
done

lemma cut_le_less_inext_conv: "
  \<lbrakk> t \<in> I; t \<noteq> Max I \<or> infinite I\<rbrakk> \<Longrightarrow> I \<down>\<le> t = I \<down>< (inext t I)"
apply (cut_tac cut_less_le_iprev_conv[of "inext t I" I])
apply (cut_tac iprev_inext[of t I], simp)
apply assumption
apply (rule inext_closed, assumption)
apply (rule neq_Max_imp_inext_neq_iMin, assumption+)
done

lemma cut_ge_greater_iprev_conv: "
  \<lbrakk> t \<in> I; t \<noteq> iMin I \<rbrakk> \<Longrightarrow> I \<down>\<ge> t = I \<down>> (iprev t I)"
apply (frule iMin_neq_imp_greater, simp+)
apply (unfold iprev_def)
apply (rule set_eqI, safe)
 apply (simp add: i_cut_defs linorder_not_less)
 apply (drule iMinI, fastforce)
apply (split if_split_asm)
 apply (rule ccontr)
 apply (simp add: nat_cut_less_finite linorder_not_le)
 apply blast
apply simp
done

lemma cut_greater_ge_inext_conv: "
  \<lbrakk> t \<in> I; t \<noteq> Max I \<or> infinite I \<rbrakk> \<Longrightarrow> I \<down>> t = I \<down>\<ge> (inext t I)"
apply (cut_tac cut_ge_greater_iprev_conv[of "inext t I" I])
apply (cut_tac iprev_inext[of t I], simp)
apply blast
apply (rule inext_closed, assumption)
apply (rule neq_Max_imp_inext_neq_iMin, assumption+)
done

lemma inext_append: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; Max A < iMin B \<rbrakk> \<Longrightarrow>
  inext n (A \<union> B) = (if n \<in> B then inext n B else (if n = Max A then iMin B else inext n A))"
apply (case_tac "n \<in> A \<union> B")
 prefer 2
 apply (simp add: not_in_inext_fix)
 apply (blast dest: Max_in)
apply (frule Max_less_iMin_imp_disjoint, assumption)
apply (drule Un_iff[THEN iffD1], elim disjE)
 apply (drule disjoint_iff_in_not_in1[THEN iffD1])
 apply simp
 apply (intro conjI impI)
  apply (simp add: inext_def cut_greater_Un cut_greater_Max_empty cut_greater_Min_all)
 apply (frule Max_neq_imp_less[of A], simp+)
 apply (simp add: inext_def cut_greater_Un cut_greater_Min_all)
 apply (subgoal_tac "A \<down>> n \<noteq> {}")
  prefer 2
  apply (simp add: cut_greater_not_empty_iff)
  apply (blast intro: Max_in)
 apply (simp add: iMin_Un)
 apply (drule iMin_in[THEN cut_greater_in_imp])
 apply (rule min_eqL)
 apply (rule less_imp_le)
 apply blast
apply (drule disjoint_iff_in_not_in2[THEN iffD1])
apply simp
apply (subgoal_tac "A \<down>> n = {}")
 prefer 2
 apply (simp add: cut_greater_empty_iff)
 apply fastforce
apply (simp add: inext_def cut_greater_Un)
done
corollary inext_append_eq1: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; Max A < iMin B; n \<in> A; n \<noteq> Max A \<rbrakk> \<Longrightarrow>
  inext n (A \<union> B) = inext n A"
apply (frule Max_less_iMin_imp_disjoint, assumption)
apply (drule disjoint_iff_in_not_in1[THEN iffD1])
apply (simp add: inext_append Max_less_iMin_imp_disjoint)
done
corollary inext_append_eq2: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; Max A < iMin B; n \<in> B \<rbrakk> \<Longrightarrow>
  inext n (A \<union> B) = inext n B"
by (simp add: inext_append)
corollary inext_append_eq3: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; Max A < iMin B \<rbrakk> \<Longrightarrow>
  inext (Max A) (A \<union> B) = iMin B"
by (simp add: inext_append not_less_iMin)

lemma iprev_append: "\<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; Max A < iMin B \<rbrakk> \<Longrightarrow>
  iprev n (A \<union> B) = (if n \<in> A then iprev n A else (if n = iMin B then Max A else iprev n B))"
apply (case_tac "n \<in> A \<union> B")
 prefer 2
 apply (simp add: not_in_iprev_fix)
 apply (blast intro: iMin_in)
apply (frule Max_less_iMin_imp_disjoint, assumption)
apply (drule Un_iff[THEN iffD1], elim disjE)
 apply (drule disjoint_iff_in_not_in1[THEN iffD1])
 apply simp
 apply (subgoal_tac "B \<down>< n = {}")
  prefer 2
  apply (simp add: cut_less_empty_iff)
  apply fastforce
 apply (simp add: iprev_def cut_less_Un)
apply (drule disjoint_iff_in_not_in2[THEN iffD1])
apply simp
apply (intro conjI impI)
 apply (simp add: iprev_def cut_less_Un cut_less_Min_empty cut_less_Max_all)
apply (frule iMin_neq_imp_greater[of _ B], simp+)
apply (simp add: iprev_def cut_less_Un)
apply (subgoal_tac "A \<down>< n = A")
 prefer 2
 apply (simp add: cut_less_all_iff)
 apply fastforce
apply (subgoal_tac "B \<down>< n \<noteq> {}")
 prefer 2
 apply (simp add: cut_less_not_empty_iff)
 apply (blast intro: iMin_in)
apply (simp add: Max_Un nat_cut_less_finite)
apply (rule max_eqR)
apply (rule less_imp_le)
apply (drule Max_in[OF nat_cut_less_finite, THEN cut_less_in_imp])
apply (blast intro: iMin_le Max_in order_less_le_trans)
done

corollary iprev_append_eq1: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; Max A < iMin B; n \<in> A \<rbrakk> \<Longrightarrow>
  iprev n (A \<union> B) = iprev n A"
by (simp add: iprev_append)

corollary iprev_append_eq2: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; Max A < iMin B; n \<in> B; n \<noteq> iMin B \<rbrakk> \<Longrightarrow>
  iprev n (A \<union> B) = iprev n B"
apply (frule Max_less_iMin_imp_disjoint, assumption)
apply (drule disjoint_iff_in_not_in2[THEN iffD1])
apply (simp add: iprev_append)
done

corollary iprev_append_eq3: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; Max A < iMin B \<rbrakk> \<Longrightarrow>
  iprev (iMin B) (A \<union> B) = Max A"
by (simp add: iprev_append not_greater_Max[of _ "iMin B"])




lemma inext_predicate_change_exists_aux: "\<And>a.
  \<lbrakk> c = card (I \<down>\<ge> a \<down>< b); a < b; a \<in> I; b \<in> I; \<not> P a; P b \<rbrakk> \<Longrightarrow>
  \<exists>n \<in> (I \<down>\<ge> a \<down>< b). \<not> P n \<and> P (inext n I)"
apply (subgoal_tac "0 < c")
 prefer 2
 apply clarify
 apply (rule_tac x=a in not_empty_card_gr0_conv[OF nat_cut_less_finite, THEN iffD1, OF in_imp_not_empty, rule_format])
 apply (simp add: i_cut_mem_iff)
apply (induct c)
 apply simp
apply (subgoal_tac "a < inext a I")
 prefer 2
 apply (blast intro: inext_mono2)
apply (drule_tac x="inext a I" in meta_spec)
apply (frule less_imp_inext_le[of _ b I], assumption+)
apply (case_tac "inext a I < b")
 prefer 2
 apply simp
 apply (subgoal_tac "I \<down>\<ge> a \<down>< b = {a}")
  prefer 2
  apply (simp add: set_eq_iff i_cut_mem_iff, clarify)
  apply (rule iffI)
   prefer 2
   apply simp
  apply clarify
  apply (case_tac "a < x")
   apply (simp add: inext_min_step)
  apply simp+
apply (subgoal_tac "I \<down>\<ge> inext a I = I \<down>> a")
 prefer 2
 apply (rule cut_greater_ge_inext_conv[symmetric], assumption)
 apply (case_tac "finite I")
  apply (simp, rule less_imp_neq)
  apply (simp add: Max_gr_iff in_imp_not_empty)
  apply (blast intro: inext_closed)
 apply simp
apply (simp add: inext_closed)
apply (subgoal_tac "a \<notin> (I \<down>> a \<down>< b)")
 prefer 2
 apply blast
apply (subgoal_tac "(I \<down>\<ge> a \<down>< b) = insert a (I \<down>> a \<down>< b)")
 prefer 2
 apply (simp add:
   i_cut_commute_disj[of "(\<down>\<ge>)" "(\<down><)"] i_cut_commute_disj[of "(\<down>>)" "(\<down><)"])
 apply (simp add: cut_ge_greater_conv_if i_cut_mem_iff)
apply (simp add: card_insert_disjoint[OF nat_cut_less_finite])
apply (case_tac "P (inext a I)")
 apply blast
apply (case_tac "card (I \<down>> a \<down>< b) = 0")
 apply (drule card_0_eq[OF nat_cut_less_finite, THEN iffD1])
 apply (simp add: cut_less_empty_iff)
 apply (drule_tac x="inext a I" in bspec)
  apply (blast intro: inext_closed)
 apply simp
apply simp
done

lemma inext_predicate_change_exists: "
  \<lbrakk> a \<le> b; a \<in> I; b \<in> I; \<not> P a; P b \<rbrakk> \<Longrightarrow>
  \<exists>n\<in>I. a \<le> n \<and> n < b \<and> \<not> P n \<and> P (inext n I)"
apply (drule order_le_less[THEN iffD1], erule disjE)
 prefer 2
 apply blast
apply (drule inext_predicate_change_exists_aux[OF refl], assumption+)
apply blast
done

lemma iprev_predicate_change_exists: "
  \<lbrakk> a \<le> b; a \<in> I; b \<in> I; \<not> P b; P a \<rbrakk> \<Longrightarrow>
  \<exists>n\<in>I. a < n \<and> n \<le> b \<and> \<not> P n \<and> P (iprev n I)"
apply (frule inext_predicate_change_exists[of a b I "\<lambda>x. \<not> P x"], simp+)
apply clarify
apply (rule_tac x="inext n I" in bexI)
 prefer 2
 apply (blast intro: inext_closed)
apply (subgoal_tac "n < inext n I")
 prefer 2
 apply (blast intro: inext_mono2)
apply (frule_tac x=a and z="inext n I" in le_less_trans, assumption)
apply (frule less_imp_inext_le, assumption+)
apply (cut_tac n=n and I=I in iprev_inext)
 apply (case_tac "finite I")
  apply simp
  apply (rule less_imp_neq)
  apply (blast intro: inext_closed Max_ge order_less_le_trans)
apply simp+
done

corollary nat_Suc_predicate_change_exists: "
  \<lbrakk> a \<le> b; \<not> P a; P b \<rbrakk> \<Longrightarrow> \<exists>n\<ge>a. n < b \<and> \<not> P n \<and> P (Suc n)"
apply (drule inext_predicate_change_exists[OF _ UNIV_I UNIV_I], assumption+)
apply (simp add: inext_UNIV)
done

corollary nat_pred_predicate_change_exists: "
  \<lbrakk> a \<le> b; \<not> P b; P a \<rbrakk> \<Longrightarrow> \<exists>n\<le>b. a < n \<and> \<not> P n \<and> P (n - Suc 0)"
apply (drule iprev_predicate_change_exists[OF _ UNIV_I UNIV_I], assumption+)
apply (fastforce simp add: iprev_UNIV)
done



lemma inext_predicate_change_exists2_all: "
  \<lbrakk> (a::nat) \<le> b; a \<in> I; b \<in> I; \<not> P a; \<forall>k \<in> I \<down>\<ge> b. P k \<rbrakk> \<Longrightarrow>
  \<exists>n\<in>I. a \<le> n \<and> n < b \<and> \<not> P n \<and> (\<forall>k \<in> I \<down>> n. P k)"
apply (drule order_le_less[THEN iffD1], erule disjE)
 prefer 2
 apply blast
apply (frule inext_predicate_change_exists[OF less_imp_le,
  of a b I "\<lambda>n. if (n = a) then P n else (\<forall>k\<in>I\<down>\<ge>n. P k)"])
 apply simp+
apply clarify
apply (rule_tac x=n in bexI)
 prefer 2
 apply assumption
apply (case_tac "a < n")
 prefer 2
 apply simp
 apply (split if_split_asm)
  apply (subgoal_tac "I \<down>> n = {}", simp+)
 apply (drule not_sym)
 apply (rule ssubst[OF cut_greater_ge_inext_conv])
  apply assumption
  apply (case_tac "finite I")
   prefer 2
   apply simp
  apply simp
  apply (rule less_imp_neq)
  apply (drule inext_neq_imp_less)
  apply (rule less_le_trans[OF _ Max_ge])
  apply assumption+
apply (subgoal_tac "a < inext n I")
 prefer 2
 apply (blast intro: inext_mono order_less_le_trans)
apply (subgoal_tac "I \<down>\<ge> inext n I = I \<down>> n")
 prefer 2
 apply (rule cut_greater_ge_inext_conv[symmetric], assumption)
 apply (case_tac "finite I")
  apply simp
  apply (rule less_imp_neq)
  apply (blast intro: inext_closed Max_ge order_less_le_trans)
 apply simp
apply simp
apply (simp add: cut_greater_ge_conv_if)
apply blast
done

corollary inext_predicate_change_exists2: "
  \<lbrakk> (a::nat) \<le> b; a \<in> I; b \<in> I; \<not> P a; P b \<rbrakk> \<Longrightarrow>
  \<exists>n\<in>I. a \<le> n \<and> n < b \<and> \<not> P n \<and> (\<forall>k\<in>I. n < k \<and> k \<le> b \<longrightarrow> P k)"
apply (frule inext_predicate_change_exists2_all[of a b "I \<down>\<le> b"])
 apply (simp add: i_cut_mem_iff)+
 apply fastforce
apply blast
done

corollary nat_Suc_predicate_change_exists2_all: "
  \<lbrakk> (a::nat) \<le> b; \<not> P a; \<forall>k\<ge>b. P k \<rbrakk> \<Longrightarrow>
  \<exists>n\<ge>a. n < b \<and> \<not> P n \<and> (\<forall>k>n. P k)"
apply (drule inext_predicate_change_exists2_all[rule_format, OF _ UNIV_I UNIV_I])
apply (simp add: i_cut_mem_iff Ball_def)+
done

corollary nat_Suc_predicate_change_exists2: "
  \<lbrakk> (a::nat) \<le> b; \<not> P a; P b \<rbrakk> \<Longrightarrow>
  \<exists>n\<ge>a. n < b \<and> \<not> P n \<and> (\<forall>k\<le>b. n < k \<longrightarrow> P k)"
apply (drule inext_predicate_change_exists2[of a b UNIV])
apply simp+
apply blast
done

lemma iprev_predicate_change_exists2_all: "
  \<lbrakk> (a::nat) \<le> b; a \<in> I; b \<in> I; \<not> P b; \<forall>k\<in>I\<down>\<le>a. P k \<rbrakk> \<Longrightarrow>
  \<exists>n\<in>I. a < n \<and> n \<le> b \<and> \<not> P n \<and> (\<forall>k\<in>I\<down><n. P k)"
apply (drule order_le_less[THEN iffD1], erule disjE)
 prefer 2
 apply blast
apply (frule iprev_predicate_change_exists[OF less_imp_le,
  of a b I "\<lambda>n. if (n = b) then P n else (\<forall>k\<in>I\<down>\<le>n. P k)"])
 apply simp+
apply clarify
apply (rule_tac x=n in bexI)
 prefer 2
 apply assumption
apply (case_tac "a < n")
 prefer 2
 apply simp
apply simp
apply (subgoal_tac "iMin I < n")
 prefer 2
 apply (blast intro: order_le_less_trans)
apply (split if_split_asm)
 apply clarsimp
 apply (split if_split_asm)
  apply simp
 apply (simp add: cut_less_le_iprev_conv[symmetric])
 apply blast
apply (split if_split_asm)
 apply simp
apply (simp add: cut_less_le_iprev_conv[symmetric])
apply (clarsimp, rename_tac x)
apply (case_tac "x < n")
 apply blast
apply simp
done


corollary iprev_predicate_change_exists2: "
  \<lbrakk> (a::nat) \<le> b; a \<in> I; b \<in> I; \<not> P b; P a \<rbrakk> \<Longrightarrow>
  \<exists>n\<in>I. a < n \<and> n \<le> b \<and> \<not> P n \<and> (\<forall>k\<in>I. a \<le> k \<and> k < n \<longrightarrow> P k)"
apply (frule iprev_predicate_change_exists2_all[of a b "I \<down>\<ge> a"])
 apply (simp add: i_cut_mem_iff)+
 apply fastforce
apply blast
done

corollary nat_pred_predicate_change_exists2_all: "
  \<lbrakk> (a::nat) \<le> b; \<not> P b; \<forall>k\<le>a. P k \<rbrakk> \<Longrightarrow>
  \<exists>n>a. n \<le> b \<and> \<not> P n \<and> (\<forall>k<n. P k)"
apply (drule iprev_predicate_change_exists2_all[rule_format, OF _ UNIV_I UNIV_I])
apply (simp add: i_cut_mem_iff Ball_def)+
done

corollary nat_pred_predicate_change_exists2: "
  \<lbrakk> (a::nat) \<le> b; \<not> P b; P a \<rbrakk> \<Longrightarrow>
  \<exists>n>a. n \<le> b \<and> \<not> P n \<and> (\<forall>k\<ge>a. k < n \<longrightarrow> P k)"
apply (drule iprev_predicate_change_exists2[of a b UNIV])
apply simp+
apply blast
done


subsection \<open>\<open>inext_nth\<close> and \<open>iprev_nth\<close> -- nth element of a natural set\<close>

primrec inext_nth :: "nat set \<Rightarrow> nat \<Rightarrow> nat"   ("(_ \<rightarrow> _)" [100, 100] 60)
where
  "I \<rightarrow> 0 = iMin I"
| "I \<rightarrow> Suc n = inext (inext_nth I n) I"

lemma inext_nth_closed: "I \<noteq> {} \<Longrightarrow> I \<rightarrow> n \<in> I"
apply (induct n)
 apply (simp add: iMinI_ex2)
apply (simp add: inext_closed)
done

lemma inext_nth_image: "
  \<lbrakk> I \<noteq> {}; strict_mono_on f I \<rbrakk> \<Longrightarrow> (f ` I) \<rightarrow> n = f (I \<rightarrow> n)"
apply (induct n)
 apply (simp add: iMin_mono_on2 strict_mono_on_imp_mono_on)
apply (simp add: inext_image inext_nth_closed)
done

lemma inext_nth_Suc_mono: "I \<rightarrow> n \<le> I \<rightarrow> Suc n"
by (simp add: inext_mono)

lemma inext_nth_mono: "a \<le> b \<Longrightarrow> I \<rightarrow> a \<le> I \<rightarrow> b"
apply (induct b)
 apply simp
apply (drule le_Suc_eq[THEN iffD1], erule disjE)
apply (rule_tac y="I \<rightarrow> b" in order_trans)
 apply simp
 apply (rule inext_nth_Suc_mono)
apply simp
done

lemma inext_nth_Suc_mono2: "\<exists>x\<in>I. I \<rightarrow> n < x \<Longrightarrow> I \<rightarrow> n < I \<rightarrow> Suc n"
apply simp
apply (rule inext_mono2)
apply (blast intro: inext_nth_closed inext_mono2)+
done

lemma inext_nth_mono2: "\<exists>x\<in>I. I \<rightarrow> a < x \<Longrightarrow> (I \<rightarrow> a < I \<rightarrow> b) = (a < b)"
apply (subgoal_tac "I \<noteq> {}")
 prefer 2
 apply blast
apply (rule iffI)
 apply (rule ccontr)
 apply (simp add: linorder_not_less)
 apply (drule inext_nth_mono[of _ _ I])
 apply simp
apply clarify
apply (induct b)
 apply blast
apply (drule less_Suc_eq[THEN iffD1], erule disjE)
 apply (blast intro: order_less_le_trans inext_nth_Suc_mono)
apply (blast intro: inext_nth_Suc_mono2)
done

lemma inext_nth_mono2_infin: "
  infinite I \<Longrightarrow> (I \<rightarrow> a < I \<rightarrow> b) = (a < b)"
apply (drule infinite_nat_iff_unbounded[THEN iffD1])
apply (rule inext_nth_mono2)
apply blast
done

lemma inext_nth_Max_fix: "
  \<lbrakk> finite I; I \<noteq> {}; I \<rightarrow> a = Max I; a \<le> b \<rbrakk> \<Longrightarrow> I \<rightarrow> b = Max I"
apply (induct b)
 apply simp
apply (drule le_Suc_eq[THEN iffD1], erule disjE)
 apply (simp add: inext_Max)
apply blast
done


lemma inext_nth_cut_less_conv: "
  \<And>I. I \<rightarrow> n < t \<Longrightarrow> (I \<down>< t) \<rightarrow> n = I \<rightarrow> n"
apply (case_tac "I = {}")
 apply (simp add: cut_less_empty)
apply (induct n)
 apply (simp add: cut_less_Min_eq cut_less_Min_not_empty)
apply simp
apply (frule order_le_less_trans[OF inext_mono])
apply (simp add: inext_cut_less_conv)
done

lemma remove_Min_inext_nth_Suc_conv: "\<And>I.
  Suc 0 < card I \<or> infinite I \<Longrightarrow>
  (I - {iMin I}) \<rightarrow> n = I \<rightarrow> Suc n"
(*apply (frule card_gt_0_iff[THEN iffD1, OF gr_implies_gr0], clarify)*)
apply (subgoal_tac "I \<noteq> {}")
 prefer 2
 apply (blast dest: card_gr0_imp_not_empty[OF gr_implies_gr0])
apply (subgoal_tac "I - {iMin I} \<noteq> {}")
 prefer 2
 apply (rule ccontr, simp)
 apply (erule disjE)
  apply (drule card_mono[OF singleton_finite])
  apply simp
 apply (simp add: subset_singleton_conv)
 apply (blast dest: infinite_imp_nonempty infinite_imp_not_singleton)
apply (induct n)
 apply (simp add: cut_greater_Min_eq_Diff[symmetric] inext_def iMinI_ex2)
apply simp
apply (rule_tac n="(inext (I \<rightarrow> n) I)" in ssubst[OF inext_def[THEN meta_eq_to_obj_eq], rule_format])
apply (rule_tac n="(inext (I \<rightarrow> n) I)" in ssubst[OF inext_def[THEN meta_eq_to_obj_eq], rule_format])
apply (simp add: inext_closed inext_nth_closed)
apply (subgoal_tac "inext (I \<rightarrow> n) I \<noteq> iMin I")
 prefer 2
 apply (erule disjE)
 apply (simp add: inext_neq_iMin_not_card_1 inext_neq_iMin_infin)+
apply (subgoal_tac "iMin I < (I \<rightarrow> Suc n)")
 prefer 2
 apply (drule_tac n="Suc n" in iMin_le[OF inext_nth_closed, rule_format])
 apply simp
apply (simp add: cut_greater_Diff cut_greater_singleton)
done

corollary remove_Min_inext_nth_Suc_conv_finite: "Suc 0 < card I \<Longrightarrow> (I - {iMin I}) \<rightarrow> n = I \<rightarrow> Suc n"
by (simp add: remove_Min_inext_nth_Suc_conv)
corollary remove_Min_inext_nth_Suc_conv_infinite: "infinite I \<Longrightarrow> (I - {iMin I}) \<rightarrow> n = I \<rightarrow> Suc n"
by (simp add: remove_Min_inext_nth_Suc_conv)


lemma remove_Max_eq: "\<lbrakk> finite I; I \<noteq> {}; n \<noteq> Max I \<rbrakk> \<Longrightarrow> Max (I - {n}) = Max I"
by (rule Max_equality, simp+)
lemma remove_iMin_eq: "\<lbrakk> I \<noteq> {}; n \<noteq> iMin I \<rbrakk> \<Longrightarrow> iMin (I - {n}) = iMin I"
by (rule iMin_equality, simp_all add: iMinI_ex2 iMin_le)
lemma remove_Min_eq: "\<lbrakk> finite I; I \<noteq> {}; n \<noteq> Min I \<rbrakk> \<Longrightarrow> Min (I - {n}) = Min I"
by (rule Min_eqI, simp+)
lemma Max_le_iMin_conv_singleton: "\<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> (Max I \<le> iMin I) = (\<exists>x. I = {x})"
by (simp add: iMin_Min_conv Max_le_Min_conv_singleton del: Max_le_iff Min_ge_iff)


lemma inext_nth_card_less_Max: "
  \<And>I. Suc n < card I \<Longrightarrow> I \<rightarrow> n < Max I"
apply (frule card_gr0_imp_not_empty[OF less_trans[OF zero_less_Suc]])
apply (frule card_gr0_imp_finite[OF less_trans[OF zero_less_Suc]])
apply (induct n)
 apply (rule ccontr)
 apply (simp add: linorder_not_less iMin_Min_conv del: Max_le_iff Min_ge_iff)
 apply (drule Max_le_Min_conv_singleton[THEN iffD1], assumption+)
 apply clarsimp
apply (drule_tac x="I - {iMin I}" in meta_spec)
apply (simp add: remove_Min_inext_nth_Suc_conv)
apply (subgoal_tac "\<not> I \<subseteq> {iMin I}")
 prefer 2
 apply (rule ccontr, simp)
 apply (drule card_mono[OF singleton_finite])
 apply simp
apply (simp add: card_Diff_singleton iMin_in Suc_less_pred_conv)
apply (subgoal_tac "Max I \<noteq> iMin I")
 prefer 2
 apply (rule ccontr, simp)
 apply (frule Max_le_iMin_conv_singleton[THEN iffD1], clarsimp+)
apply (simp add: remove_Max_eq Max_le_iMin_conv_singleton)
done

lemma inext_nth_card_less_Max': "
  n < card I - Suc 0 \<Longrightarrow> I \<rightarrow> n < Max I"
by (simp add: inext_nth_card_less_Max)


lemma inext_nth_card_Max_aux: "
  \<And>I. card I = Suc n \<Longrightarrow> I \<rightarrow> n = Max I"
apply (frule card_gr0_imp_not_empty[OF less_le_trans[OF zero_less_Suc, OF eq_imp_le[OF sym]]])
apply (frule card_gr0_imp_finite[OF less_le_trans[OF zero_less_Suc, OF eq_imp_le[OF sym]]])
apply (induct n)
 apply (clarsimp simp: card_1_singleton_conv)
apply simp
apply (cut_tac I=I and t="Max I" in nat_cut_less_finite)
apply (subgoal_tac "card (I \<down>< Max I) = Suc n")
 prefer 2
 apply (simp add: cut_less_le_conv cut_le_Max_all)
apply (frule_tac n=n in card_gr0_imp_not_empty[OF less_le_trans[OF zero_less_Suc, OF eq_imp_le[OF sym]], rule_format])
apply (subgoal_tac "Max (I \<down>< Max I) < iMin {Max I}")
 prefer 2
 apply (simp, blast)
apply (subgoal_tac "inext_nth I n < Max I")
 prefer 2
 apply (simp add: inext_nth_card_less_Max)
apply (frule inext_nth_cut_less_conv[symmetric])
apply simp
apply (rule min_step_inext)
 apply simp
 apply (rule subsetD, rule cut_less_subset, rule Max_in, assumption+)
 apply simp
apply (frule_tac A="I \<down>< Max I" and k=k in not_greater_Max, assumption)
apply (simp add: cut_less_mem_iff)
done

lemma inext_nth_card_Max_aux': "
  \<And>I. \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> I \<rightarrow> (card I - Suc 0) = Max I"
by (simp add: inext_nth_card_Max_aux not_empty_card_gr0_conv)

lemma inext_nth_card_Max: "
  \<lbrakk> finite I; I \<noteq> {}; card I \<le> Suc n \<rbrakk> \<Longrightarrow> I \<rightarrow> n = Max I"
apply (rule inext_nth_Max_fix[of _ "card I - Suc 0"], assumption+)
apply (simp add: inext_nth_card_Max_aux')
apply simp
done

lemma inext_nth_card_Max': "
  \<lbrakk> finite I; I \<noteq> {}; card I - Suc 0 \<le> n \<rbrakk> \<Longrightarrow> I \<rightarrow> n = Max I"
by (simp add: inext_nth_card_Max)

lemma inext_nth_singleton: "{a} \<rightarrow> n = a"
by (simp add: inext_nth_Max_fix[OF singleton_finite singleton_not_empty _ le0])

lemma inext_nth_eq_Min_conv: "
  I \<noteq> {} \<Longrightarrow> (I \<rightarrow> n = iMin I) = (n = 0 \<or> (\<exists>a. I = {a}))"
apply (rule iffI)
 apply (case_tac n, simp)
 apply (rename_tac n')
 apply (rule ccontr)
 apply (drule_tac n="I \<rightarrow> n'" in  inext_neq_iMin_not_singleton, simp)
 apply simp
apply (erule disjE, simp)
apply (clarsimp simp: inext_nth_singleton)
done

lemma inext_nth_gr_Min_conv: "
  I \<noteq> {} \<Longrightarrow> (iMin I < I \<rightarrow> n) = (0 < n \<and> \<not>(\<exists>a. I = {a}))"
apply (rule subst[of "iMin I \<noteq> I \<rightarrow> n" "iMin I < I \<rightarrow> n"])
 apply (frule iMin_le[OF inext_nth_closed[of _ n]])
 apply (simp add: linorder_neq_iff)
apply (subst neq_commute[of "iMin I"])
apply (simp add: inext_nth_eq_Min_conv)
done

lemma inext_nth_gr_Min_conv_infinite: "
  infinite I \<Longrightarrow> (iMin I < I \<rightarrow> n) = (0 < n)"
by (simp add: inext_nth_gr_Min_conv infinite_imp_nonempty infinite_imp_not_singleton)


lemma inext_nth_cut_ge_inext_nth: "\<And>I b.
  I \<noteq> {} \<Longrightarrow> I \<down>\<ge> (I \<rightarrow> a) \<rightarrow> b = I \<rightarrow> (a + b)"
apply (induct a)
 apply (simp add: cut_ge_Min_all)
apply (case_tac "card I = Suc 0")
 apply (drule card_1_imp_singleton, clarify)
 apply (simp add: inext_nth_singleton inext_singleton cut_ge_Min_all)
apply (subgoal_tac "Suc 0 < card I \<or> infinite I")
 prefer 2
 apply (rule ccontr, clarsimp simp: linorder_not_less not_empty_card_gr0_conv)
apply (case_tac "I - {iMin I} = {}")
 apply (rule_tac t=I and s="{iMin I}" in subst, blast)
 apply (simp (no_asm) add: inext_nth_singleton inext_singleton cut_ge_Min_all)
apply (simp add: subset_singleton_conv)
apply (drule_tac x="I - {iMin I}" in meta_spec)
apply (drule_tac x=b in meta_spec)
apply (drule meta_mp, blast)
apply (simp add: remove_Min_inext_nth_Suc_conv)
apply (simp add: cut_ge_Diff cut_ge_singleton)
apply (subgoal_tac "iMin I < inext (I \<rightarrow> a) I", simp)
apply (rule le_neq_trans[OF _ not_sym])
 apply (simp add: iMin_le inext_closed inext_nth_closed)
apply (erule disjE)
apply (simp add: inext_neq_iMin_not_card_1 inext_neq_iMin_infin)+
done

lemma inext_nth_append_eq1: "
  \<lbrakk> finite A; A \<noteq> {}; Max A < iMin B; A \<rightarrow> n \<noteq> Max A \<rbrakk> \<Longrightarrow>
  (A \<union> B) \<rightarrow> n = A \<rightarrow> n"
apply (case_tac "B = {}", simp)
apply (induct n)
 apply (simp add: iMin_Un del: Max_less_iff)
 apply (rule min_eq)
 apply (blast intro: order_less_imp_le order_le_less_trans iMin_le_Max)
apply (frule_tac n="Suc n" in Max_ge[OF _ inext_nth_closed, rule_format], assumption)
apply (drule order_le_neq_trans, simp+)
apply (drule order_le_less_trans[OF inext_mono])
apply (simp add: inext_append_eq1 inext_nth_closed)
done

lemma inext_nth_card_append_eq1: "
  \<And>A B.\<lbrakk> Max A < iMin B; n < card A \<rbrakk> \<Longrightarrow>
  (A \<union> B) \<rightarrow> n = A \<rightarrow> n"
apply (case_tac "B = {}", simp)
apply (frule card_gr0_imp_finite[OF le_less_trans[OF le0]])
apply (frule card_gr0_imp_not_empty[OF le_less_trans[OF le0]])
apply (drule Suc_leI[of n], drule order_le_less[THEN iffD1], erule disjE)
 apply (rule inext_nth_append_eq1, assumption+)
 apply (simp add: inext_nth_card_less_Max less_imp_neq)
apply (simp add: inext_nth_card_Max[OF _ _ eq_imp_le[OF sym]] del: Max_less_iff)
apply (induct n)
 apply (frule card_1_imp_singleton[OF sym], erule exE)
 apply (simp add: iMin_insert)
apply simp
apply (subgoal_tac "inext_nth A n < Max A")
 prefer 2
 apply (rule inext_nth_card_less_Max, simp)
apply (simp add: inext_nth_append_eq1)
apply (rule min_step_inext)
apply (simp add: inext_nth_closed)+
apply (rule conjI)
 apply (subgoal_tac "k < A \<rightarrow> Suc n")
  prefer 2
  apply (subgoal_tac "A \<rightarrow> Suc n = Max A")
   prefer 2
   apply (rule inext_nth_card_Max)
   apply simp+
 apply (rule_tac n="A \<rightarrow> n" and k=k in inext_min_step, simp+)
apply (rule not_less_iMin)
apply (rule_tac y="Max A" in order_less_trans)
apply simp+
done

lemma inext_nth_card_append_eq3: "
  \<lbrakk> finite A; B \<noteq> {}; Max A < iMin B \<rbrakk> \<Longrightarrow>
  (A \<union> B) \<rightarrow> (card A) = iMin B"
apply (case_tac "A = {}", simp)
apply (frule not_empty_card_gr0_conv[THEN iffD1], assumption)
apply (rule subst[OF Suc_pred, of "card A"], assumption)
apply (simp only: inext_nth.simps) (* just "simp" wouldn't work, because it would revert "Suc (card A - Suc 0)" to "card A" instead of applying inext_nth.simps *)
apply (simp add: inext_nth_card_append_eq1 inext_nth_card_Max' inext_append_eq3)
done

lemma inext_nth_card_append_eq2: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; Max A < iMin B; card A \<le> n \<rbrakk> \<Longrightarrow>
  (A \<union> B) \<rightarrow> n = B \<rightarrow> (n - card A)"
apply (rule_tac t="(A \<union> B) \<rightarrow> n" and s="(A \<union> B) \<rightarrow> (card A + (n - card A))" in subst, simp)
apply (subst inext_nth_cut_ge_inext_nth[symmetric], simp)
apply (subst inext_nth_card_append_eq3, assumption+)
apply (simp add: cut_ge_Un cut_ge_Max_empty cut_ge_Min_all del: Max_less_iff)
done

lemma inext_nth_card_append: "
  \<lbrakk> finite A; A \<noteq> {}; B \<noteq> {}; Max A < iMin B \<rbrakk> \<Longrightarrow>
  (A \<union> B) \<rightarrow> n = (if n < card A then A \<rightarrow> n else B \<rightarrow> (n - card A))"
by (simp add: inext_nth_card_append_eq1 inext_nth_card_append_eq2)

lemma inext_nth_insert_Suc: "
  \<lbrakk> I \<noteq> {}; a < iMin I \<rbrakk> \<Longrightarrow> (insert a I) \<rightarrow> Suc n = I \<rightarrow> n"
apply (frule not_less_iMin)
apply (rule_tac t="I \<rightarrow> n" and s="(insert a I - {iMin (insert a I)}) \<rightarrow> n" in subst)
 apply (simp add: iMin_insert min_eqL)
apply (subst remove_Min_inext_nth_Suc_conv)
apply (case_tac "finite I")
apply (simp add: not_empty_card_gr0_conv)+
done

lemma inext_nth_cut_less_eq: "
  n < card (I \<down>< t) \<Longrightarrow> (I \<down>< t) \<rightarrow> n = I \<rightarrow> n"
apply (rule_tac t="I \<rightarrow> n" and s="(I \<down>< t \<union> I \<down>\<ge> t) \<rightarrow> n" in subst)
 apply (simp add: cut_less_cut_ge_ident)
apply (case_tac "I \<down>\<ge> t = {}", simp)
apply (rule sym, rule inext_nth_card_append_eq1)
 apply (drule card_gt_0_iff[THEN iffD1, OF gr_implies_gr0], clarify)
 apply (simp add: Ball_def i_cut_mem_iff iMin_gr_iff)
apply simp
done

lemma less_card_cut_less_imp_inext_nth_less: "
  n < card (I \<down>< t) \<Longrightarrow> I \<rightarrow> n < t"
apply (case_tac "I \<down>< t = {}", simp)
apply (rule subst[OF inext_nth_cut_less_eq], assumption)
apply (rule cut_less_bound[OF inext_nth_closed], assumption)
done

lemma inext_nth_less_less_card_conv: "
  I \<down>\<ge> t \<noteq> {} \<Longrightarrow> (I \<rightarrow> n < t) = (n < card (I \<down>< t))"
apply (case_tac "I = {}", blast)
apply (case_tac "I \<down>< t = {}")
 apply (simp add: linorder_not_less)
 apply (simp add: cut_less_empty_iff inext_nth_closed)
apply (rule iffI)
 apply (rule ccontr, simp add: linorder_not_less)
 apply (subgoal_tac "Max (I \<down>< t) < iMin (I \<down>\<ge> t)")
  prefer 2
  apply (simp add: nat_cut_less_finite iMin_gr_iff Ball_def i_cut_mem_iff)
 apply (drule ssubst[OF cut_less_cut_ge_ident[OF order_refl], of "\<lambda>x. x \<rightarrow> n < t" _ t])
 apply (drule inext_nth_card_append_eq2[OF nat_cut_less_finite, of I t "I \<down>\<ge> t" n], assumption+)
 apply (simp add: inext_nth_card_append_eq2 nat_cut_less_finite)
 apply (subgoal_tac "\<And>x. I \<down>\<ge> t \<rightarrow> x \<ge> t")
  prefer 2
  apply (rule cut_ge_bound[OF inext_nth_closed], assumption)
 apply (simp add: linorder_not_le[symmetric])
apply (rule subst[OF inext_nth_cut_less_eq], assumption)
apply (rule cut_less_bound[OF inext_nth_closed], assumption)
done


lemma cut_less_inext_nth_card_eq1: "
  n < card I \<or> infinite I \<Longrightarrow> card (I \<down>< (I \<rightarrow> n)) = n"
apply (case_tac "I = {}", simp)
apply (induct n)
 apply (simp add: card_eq_0_iff nat_cut_less_finite cut_less_Min_empty)
apply (subgoal_tac "n < card I \<or> infinite I")
 prefer 2
 apply fastforce
apply simp
apply (subgoal_tac "I \<rightarrow> n \<noteq> Max I \<or> infinite I")
 prefer 2
 apply (blast dest: inext_nth_card_less_Max less_imp_neq)
apply (rule subst[OF cut_le_less_inext_conv[OF inext_nth_closed]], assumption+)
apply (simp add: cut_le_less_conv_if inext_nth_closed cut_less_mem_iff card_insert_if nat_cut_less_finite)
done

lemma cut_less_inext_nth_card_eq2: "
  \<lbrakk> finite I; card I \<le> Suc n \<rbrakk> \<Longrightarrow> card (I \<down>< (I \<rightarrow> n)) = card I - Suc 0"
apply (case_tac "I = {}", simp add: cut_less_empty)
apply (simp add: inext_nth_card_Max cut_less_Max_eq_Diff)
done

lemma cut_less_inext_nth_card_if: "
  card (I \<down>< (I \<rightarrow> n)) = (
  if (n < card I \<or> infinite I) then n else card I - Suc 0)"
by (simp add: cut_less_inext_nth_card_eq1 cut_less_inext_nth_card_eq2)

lemma cut_le_inext_nth_card_eq1: "
  n < card I \<or> infinite I \<Longrightarrow> card (I \<down>\<le> (I \<rightarrow> n)) = Suc n"
apply (case_tac "I = {}", simp)
apply (simp add: cut_le_less_conv_if inext_nth_closed card_insert_if nat_cut_less_finite cut_less_mem_iff cut_less_inext_nth_card_eq1)
done

lemma cut_le_inext_nth_card_eq2: "
  \<lbrakk> finite I; card I \<le> Suc n \<rbrakk> \<Longrightarrow> card (I \<down>\<le> (I \<rightarrow> n)) = card I"
apply (case_tac "I = {}", simp add: cut_le_empty)
apply (simp add: inext_nth_card_Max cut_le_Max_all)
done

lemma cut_le_inext_nth_card_if: "
  card (I \<down>\<le> (I \<rightarrow> n)) = (
  if (n < card I \<or> infinite I) then Suc n else card I)"
by (simp add: cut_le_inext_nth_card_eq1 cut_le_inext_nth_card_eq2)


primrec iprev_nth :: "nat set \<Rightarrow> nat \<Rightarrow> nat"  ("(_ \<leftarrow> _)" [100, 100] 60)
where
  "I \<leftarrow> 0 = Max I"
| "I \<leftarrow> Suc n = iprev (iprev_nth I n) I"

lemma iprev_nth_closed: "\<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow> I \<leftarrow> n \<in> I"
apply (induct n)
 apply simp
apply (simp add: iprev_closed)
done

lemma iprev_nth_image: "
  \<lbrakk> finite I; I \<noteq> {}; strict_mono_on f I \<rbrakk> \<Longrightarrow> (f ` I) \<leftarrow> n = f (I \<leftarrow> n)"
apply (induct n)
 apply (simp add: Max_mono_on2 strict_mono_on_imp_mono_on)
apply (simp add: iprev_image iprev_nth_closed)
done

lemma iprev_nth_Suc_mono: "I \<leftarrow> (Suc n) \<le> I \<leftarrow> n"
by (simp add: iprev_mono)

lemma iprev_nth_mono: "a \<le> b \<Longrightarrow> I \<leftarrow> b \<le> I \<leftarrow> a"
apply (induct b)
 apply simp
apply (drule le_Suc_eq[THEN iffD1], erule disjE)
 apply (rule_tac y="iprev_nth I b" in order_trans)
 apply (rule iprev_nth_Suc_mono)
 apply simp
apply simp
done

lemma iprev_nth_Suc_mono2:
  "\<lbrakk> finite I; \<exists>x\<in>I. x < I \<leftarrow> n \<rbrakk> \<Longrightarrow> I \<leftarrow> (Suc n) < I \<leftarrow> n"
apply simp
apply (rule iprev_mono2)
apply (blast intro: iprev_nth_closed)+
done

lemma iprev_nth_mono2: "
  \<lbrakk> finite I; \<exists>x\<in>I. x < I \<leftarrow> a \<rbrakk> \<Longrightarrow> (I \<leftarrow> b < I \<leftarrow> a) = (a < b)"
apply (subgoal_tac "I \<noteq> {}")
 prefer 2
 apply blast
apply (rule iffI)
 apply (rule ccontr)
 apply (simp add: linorder_not_less)
 apply (drule iprev_nth_mono[of _ _ I])
 apply simp
apply clarify
apply (induct b)
 apply blast
apply (drule less_Suc_eq[THEN iffD1], erule disjE)
 apply (blast intro: order_le_less_trans iprev_nth_Suc_mono)
apply (blast intro: iprev_nth_Suc_mono2)
done

lemma iprev_nth_iMin_fix: "
  \<lbrakk> I \<noteq> {}; I \<leftarrow> a = iMin I; a \<le> b \<rbrakk> \<Longrightarrow> I \<leftarrow> b = iMin I"
apply (induct b)
 apply simp
apply (drule le_Suc_eq[THEN iffD1], erule disjE)
 apply (simp add: iprev_iMin)
apply blast
done

lemma iprev_nth_singleton: "{a} \<leftarrow> n= a"
by (simp add: iprev_nth_iMin_fix[OF singleton_not_empty _ le0])


subsection \<open>Induction over arbitrary natural sets using the functions \<open>inext\<close> and \<open>iprev\<close>\<close>

lemma inext_nth_surj_aux1:"
  {x \<in> I. \<not>(\<exists>n. I \<rightarrow> n = x)} = {}"
  (is "?S = {}"
   is "{ x \<in> I. ?P x} = {}")
apply (case_tac "I = {}", blast)
proof (rule ccontr)
  assume as_S_not_empty: "?S \<noteq> {}"

  obtain S where s_S: "S = ?S" by blast
  hence S_not_empty: "S \<noteq> {}"
    using as_S_not_empty by blast

  have s_not_ex: "\<And>x. \<lbrakk> x \<in> I; ?P x \<rbrakk> \<Longrightarrow> x \<in> S"
    using s_S by blast

  have s_subset:"S \<subseteq> I"
    using s_S by blast
  have i_not_empty: "I \<noteq> {}"
    using as_S_not_empty by blast

  have s_iMin_S: "iMin S \<in> S"
    using S_not_empty by (simp add: iMinI_ex2)
  hence s_iMin_i: "iMin S \<in> I"
    using s_subset by blast

  show False
  proof cases
    assume as:"iMin I < iMin S"

    obtain prev where s_prev: "prev = iprev (iMin S) I" by blast
    have s_prev_in: "prev \<in> I"
      apply (simp add: s_prev)
      apply (rule iprev_closed)
      apply (rule s_iMin_i)
      done

    have s_prev_next_min: "inext prev I = iMin S"
      apply (simp add: s_prev)
      apply (rule inext_iprev)
      apply (insert as, simp)
      done

    have s_prev_min_1: "prev < iMin S"
      apply (simp only: s_prev)
      apply (rule iprev_mono2[of "iMin S" ])
      apply (rule s_iMin_i)
      apply (rule_tac x="iMin I" in bexI)
      apply (rule as)
      apply (simp add: iMinI_ex2 i_not_empty)
      done
    hence prev_not_in_s: "prev \<notin> S"
      by (simp add: not_less_iMin)
    have "\<exists>n. I \<rightarrow> n = prev"
      by (insert prev_not_in_s s_not_ex[of prev] s_prev_in, blast)
    then obtain nPrev where s_nPrev: "I \<rightarrow> nPrev = prev" by blast
    hence "I \<rightarrow> (Suc nPrev) = inext prev I" by simp
    hence "I \<rightarrow> (Suc nPrev) = iMin S"
      using s_prev_next_min by simp
    hence "\<exists>n. I \<rightarrow> n = iMin S" by blast
    hence "iMin S \<notin> S"
      using s_iMin_i s_S by blast
    thus False
      using s_iMin_S by blast
  next
    assume as:"\<not>(iMin I < iMin S)"

    have "iMin S = iMin I"
      apply (insert s_subset S_not_empty as)
      apply (frule_tac A=S and B=I in iMin_subset)
      by simp_all
    hence "\<exists>n. I \<rightarrow> n \<in> S"
      apply (rule_tac x=0 in exI)
      apply (insert s_iMin_S)
      apply simp
      done
    thus False
      using s_S by blast
  qed
qed

lemma inext_nth_surj_on:"surj_on (\<lambda>n. I \<rightarrow> n) UNIV I"
apply (simp add: surj_on_conv)
by (insert inext_nth_surj_aux1[of I], blast)

corollary in_imp_ex_inext_nth: "x \<in> I \<Longrightarrow> \<exists>n. x = I \<rightarrow> n"
apply (rule surj_onD[where A=UNIV, simplified])
apply (rule inext_nth_surj_on)
apply assumption
done

lemma inext_induct: "
  \<lbrakk> P (iMin I); \<And>n. \<lbrakk> n \<in> I; P n \<rbrakk> \<Longrightarrow> P (inext n I); n \<in> I \<rbrakk> \<Longrightarrow> P n"
apply (rule_tac f="\<lambda>n. I \<rightarrow> n" and I=I in image_nat_induct)
apply (simp add: inext_nth_closed[OF in_imp_not_empty] inext_nth_surj_on)+
done

lemma iprev_nth_surj_aux1:"
  finite I \<Longrightarrow> { x \<in> I. \<not>(\<exists>n. I \<leftarrow> n = x)} = {}"
apply (case_tac "I = {}", blast)
proof (rule ccontr)
  assume as_finite_i: "finite I"
  let ?S = "{x \<in> I. \<not> (\<exists>n. I \<leftarrow> n = x)}"
  assume as_S_not_empty: "?S \<noteq> {}"

  obtain S where s_S: "S = ?S" by blast
  hence S_not_empty: "S \<noteq> {}"
    using as_S_not_empty by blast

  have s_not_ex: "\<And>x. \<lbrakk> x \<in> I; \<not>(\<exists>n. I \<leftarrow> n = x) \<rbrakk> \<Longrightarrow> x \<in> S"
    using s_S by blast

  have s_subset:"S \<subseteq> I"
    using s_S by blast
  have i_not_empty: "I \<noteq> {}"
    using as_S_not_empty by blast

  from as_finite_i
  have S_finite: "finite S"
    using s_subset by (blast intro: finite_subset)

  have s_Max_S: "Max S \<in> S"
    using S_not_empty S_finite by simp
  hence s_Max_i: "Max S \<in> I"
    using s_subset by blast

  show False
  proof cases
    assume as:"Max S < Max I"

    obtain next' where s_next: "next' = inext (Max S) I" by blast
    have s_next_in: "next' \<in> I"
      by (simp add: s_next inext_closed s_Max_i)

    have s_next_prev_max: "iprev next' I = Max S"
      apply (simp add: s_next)
      apply (rule iprev_inext)
      apply (insert as, simp)
      done

    have s_next_max_1: "Max S < next'"
      apply (simp add: s_next)
      apply (rule inext_mono2[of "Max S" I])
      apply (rule s_Max_i)
      apply (rule_tac x="Max I" in bexI)
      apply (rule as)
      apply (simp add: as_finite_i i_not_empty)
      done
    hence next_not_in_s: "next' \<notin> S"
      using S_finite S_not_empty
      apply clarify
      apply (drule Max_ge[of _ next'])
      apply simp_all
      done
    have "\<exists>n. I \<leftarrow> n = next'"
      by (insert next_not_in_s s_not_ex[of next'] s_next_in, blast)
    then obtain nNext where s_nNext: "I \<leftarrow> nNext = next'" by blast
    hence "I \<leftarrow> (Suc nNext) = iprev next' I" by simp
    hence "I \<leftarrow> (Suc nNext) = Max S"
      using s_next_prev_max by simp
    hence "\<exists>n. I \<leftarrow> n = Max S" by blast
    hence "Max S \<notin> S"
      using s_Max_i s_S by blast
    thus False
      using s_Max_S by blast+
  next
    assume as:"\<not>(Max S < Max I)"

    have "Max S = Max I"
      apply (insert s_subset S_not_empty as_finite_i as)
      apply (drule Max_subset[of _ I])
      by simp_all
    hence "\<exists>n. I \<leftarrow> n \<in> S"
      apply (rule_tac x=0 in exI)
      apply (insert s_Max_S)
      apply simp
      done
    thus False
      using s_S by blast
  qed
qed

lemma iprev_nth_surj_on: "finite I \<Longrightarrow> surj_on (\<lambda>n. I \<leftarrow> n) UNIV I"
apply (simp add: surj_on_def)
by (insert iprev_nth_surj_aux1[of I], blast)

corollary in_imp_ex_iprev_nth: "
  \<lbrakk> finite I;  x \<in> I \<rbrakk> \<Longrightarrow> \<exists>n. x = I \<leftarrow> n"
apply (rule surj_onD[of _ UNIV I, simplified])
apply (rule iprev_nth_surj_on)
apply assumption+
done

lemma iprev_induct: "
  \<lbrakk> P (Max I); \<And>n. \<lbrakk> n \<in> I; P n \<rbrakk> \<Longrightarrow> P (iprev n I); finite I; n \<in> I \<rbrakk> \<Longrightarrow> P n"
apply (rule_tac f="\<lambda>n. I \<leftarrow> n" and I=I in image_nat_induct)
apply (simp add: iprev_nth_closed[OF _ in_imp_not_empty] iprev_nth_surj_on)+
done


subsection \<open>Natural intervals with \<open>inext\<close> and \<open>iprev\<close>\<close>

lemma inext_atLeast: "n \<le> t \<Longrightarrow> inext t {n..} = Suc t"
apply (unfold inext_def)
apply (subgoal_tac "Suc t \<in> {n..} \<down>> t")
 prefer 2
 apply (simp add: cut_greater_mem_iff)
apply (simp add: in_imp_not_empty)
apply (rule iMin_equality, assumption)
apply (simp add: cut_greater_mem_iff)
done

lemma iprev_atLeast': "n \<le> t \<Longrightarrow> iprev (Suc t) {n..} = t"
apply (rule subst[OF inext_atLeast], assumption)
apply (rule iprev_inext_infin[OF infinite_atLeast])
done

lemma iprev_atLeast: "n < t  \<Longrightarrow> iprev t {n..} = t - Suc 0"
by (insert iprev_atLeast'[of n "t - Suc 0"], simp)

lemma inext_atMost: "t < n \<Longrightarrow> inext t {..n} = Suc t"
apply (unfold inext_def)
apply (subgoal_tac "Suc t \<in> {..n} \<down>> t")
 prefer 2
 apply (simp add: cut_greater_mem_iff)
apply (simp add: in_imp_not_empty)
apply (rule iMin_equality, assumption)
apply (simp add: cut_greater_mem_iff)
done

lemma iprev_atMost: "t \<le> n \<Longrightarrow> iprev t {..n} = t - Suc 0"
apply (case_tac t)
 apply simp
 apply (rule subst[OF iMin_atMost[of n]])
 apply (rule iprev_iMin)
apply simp
apply (drule Suc_le_lessD)
apply (rule subst[OF inext_atMost], assumption)
apply (simp add: Max_atMost iprev_inext_fin)
done

lemma inext_lessThan: "Suc t < n \<Longrightarrow> inext t {..<n} = Suc t"
apply (rule subst[OF Suc_pred, of n], simp)
apply (subst lessThan_Suc_atMost)
apply (simp add: inext_atMost)
done
lemma iprev_lessThan: "t < n \<Longrightarrow> iprev t {..<n} = t - Suc 0"
apply (case_tac n, simp)
apply (simp add: lessThan_Suc_atMost iprev_atMost)
done

lemma inext_atLeastAtMost: "\<lbrakk> m \<le> t; t < n \<rbrakk> \<Longrightarrow> inext t {m..n} = Suc t"
by (simp add: atLeastAtMost_def cut_le_Int_conv[symmetric] inext_atLeast inext_cut_le_conv)
lemma iprev_atLeastAtMost: "\<lbrakk> m < t; t \<le> n \<rbrakk> \<Longrightarrow> iprev t {m..n} = t - Suc 0"
by (simp add: atLeastAtMost_def cut_le_Int_conv[symmetric] iprev_atLeast iprev_cut_le_conv)
lemma iprev_atLeastAtMost': "\<lbrakk> m \<le> t; t < n \<rbrakk> \<Longrightarrow> iprev (Suc t) {m..n} = t"
by (simp add: iprev_atLeastAtMost[of _ "Suc t"])

lemma inext_nth_atLeast : "{n..} \<rightarrow> a = n + a"
apply (induct a, simp add: iMin_atLeast)
apply (simp add: inext_atLeast)
done
lemma inext_nth_atLeastAtMost: "\<lbrakk> a \<le> n - m; m \<le> n \<rbrakk> \<Longrightarrow> {m..n} \<rightarrow> a = m + a"
apply (induct a, simp add: iMin_atLeastAtMost)
apply (simp add: inext_atLeastAtMost)
done
lemma iprev_nth_atLeastAtMost: "\<lbrakk> a \<le> n - m; m \<le> n \<rbrakk> \<Longrightarrow> {m..n} \<leftarrow> a = n - a"
apply (induct a, simp add: Max_atLeastAtMost)
apply (simp add: iprev_atLeastAtMost)
done
lemma inext_nth_atMost: "a \<le> n \<Longrightarrow> {..n} \<rightarrow> a = a"
apply (insert inext_nth_atLeastAtMost[of a n 0])
apply (simp add: atMost_atLeastAtMost_0_conv)
done
lemma iprev_nth_atMost: "a \<le> n \<Longrightarrow> {..n} \<leftarrow> a = n - a"
apply (insert iprev_nth_atLeastAtMost[of a n 0])
apply (simp add: atMost_atLeastAtMost_0_conv)
done

lemma inext_nth_lessThan : "a < n \<Longrightarrow> {..<n} \<rightarrow> a = a"
apply (case_tac n, simp)
apply (simp add: lessThan_Suc_atMost inext_nth_atMost)
done
lemma iprev_nth_lessThan: "a < n \<Longrightarrow> {..<n} \<leftarrow> a = n - Suc a"
apply (case_tac n, simp)
apply (simp add: lessThan_Suc_atMost iprev_nth_atMost)
done

lemma inext_nth_UNIV: "UNIV \<rightarrow> a = a"
by (simp add: inext_nth_atLeast del: atLeast_0 add: atLeast_0[symmetric])


subsection \<open>Further result for \<open>inext_nth\<close> and \<open>iprev_nth\<close>\<close>

lemma inext_iprev_nth_Suc: "
  iMin I \<noteq> I \<leftarrow> n \<Longrightarrow> inext (I \<leftarrow> Suc n) I = I \<leftarrow> n"
by (simp add: inext_iprev)

lemma inext_iprev_nth_pred: "
  \<lbrakk> finite I; iMin I \<noteq> I \<leftarrow> (n - Suc 0) \<rbrakk> \<Longrightarrow>
  inext (I \<leftarrow> n) I = I \<leftarrow> (n - Suc 0)"
apply (case_tac n)
 apply (simp add: inext_Max)
apply (simp add: inext_iprev)
done

lemma iprev_inext_nth_Suc: "
  I \<rightarrow> n \<noteq> Max I \<or> infinite I \<Longrightarrow> iprev (I \<rightarrow> Suc n) I = I \<rightarrow> n"
by (simp add: iprev_inext)
lemma iprev_inext_nth_pred: "
  I \<rightarrow> (n - Suc 0) \<noteq> Max I \<or> infinite I \<Longrightarrow>
  iprev (I \<rightarrow> n) I = I \<rightarrow> (n - Suc 0)"
apply (case_tac n)
 apply (simp add: iprev_iMin)
apply (simp add: iprev_inext)
done

lemma inext_nth_imirror_iprev_nth_conv: "
  \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow>
  (imirror I) \<rightarrow> n = mirror_elem (I \<leftarrow> n) I"
apply (induct n)
 apply (simp add: imirror_iMin mirror_elem_Max)
apply (simp add: inext_imirror_iprev_conv' iprev_nth_closed)
done

corollary inext_nth_imirror_iprev_nth_conv2: "
  \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow>
  mirror_elem ((imirror I) \<leftarrow> n) I = I \<rightarrow> n"
apply (frule inext_nth_imirror_iprev_nth_conv[OF imirror_finite imirror_not_empty, of _ n], assumption)
apply (simp add: imirror_imirror_ident mirror_elem_imirror)
done


lemma iprev_nth_imirror_inext_nth_conv: "
  \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow>
  (imirror I) \<leftarrow> n = mirror_elem (I \<rightarrow> n) I"
apply (induct n)
 apply (simp add: imirror_Max mirror_elem_Min)
apply (simp add: iprev_imirror_inext_conv' inext_nth_closed)
done

corollary iprev_nth_imirror_inext_nth_conv2: "
  \<lbrakk> finite I; I \<noteq> {} \<rbrakk> \<Longrightarrow>
  mirror_elem ((imirror I) \<rightarrow> n) I = (I \<leftarrow> n)"
apply (frule iprev_nth_imirror_inext_nth_conv[OF imirror_finite imirror_not_empty, of _ n], assumption)
apply (simp add: imirror_imirror_ident mirror_elem_imirror)
done

lemma iprev_nth_card_greater_iMin: "Suc n < card I \<Longrightarrow> iMin I < I \<leftarrow> n"
apply (subgoal_tac "I \<noteq> {}" "finite I")
 prefer 2
 apply (rule card_gr0_imp_finite, simp)
 prefer 2
 apply (rule card_gr0_imp_not_empty, simp)
apply (subst iprev_nth_imirror_inext_nth_conv2[symmetric], assumption+)
apply (subst mirror_elem_Max[symmetric], assumption+)
apply (subst mirror_elem_imirror[symmetric], assumption)
apply (subst mirror_elem_imirror[symmetric], assumption)
apply (frule imirror_finite, frule imirror_not_empty)
apply (rule mirror_elem_less_conv[THEN iffD2])
 apply assumption
 apply (rule inext_nth_closed, assumption)
 apply (rule subst[OF imirror_Max], assumption)
 apply (rule Max_in, assumption+)
apply (rule subst[OF imirror_Max], assumption)
apply (simp add: inext_nth_card_less_Max imirror_card)
done

lemma iprev_nth_card_iMin: "
  \<lbrakk> finite I; I \<noteq> {}; card I \<le> Suc n \<rbrakk> \<Longrightarrow> I \<leftarrow> n = iMin I"
apply (subst iprev_nth_imirror_inext_nth_conv2[symmetric], assumption+)
apply (subst mirror_elem_Max[symmetric], assumption+)
apply (subst mirror_elem_imirror[symmetric], assumption)
apply (subst mirror_elem_imirror[symmetric], assumption)
apply (rule subst[OF imirror_Max], assumption)
apply (frule imirror_finite, frule imirror_not_empty)
apply (simp add: mirror_elem_eq_conv' inext_nth_closed inext_nth_card_Max imirror_card)
done

lemma iprev_nth_card_iMin': "
  \<lbrakk> finite I; I \<noteq> {}; card I - Suc 0 \<le> n \<rbrakk> \<Longrightarrow> I \<leftarrow> n = iMin I"
by (simp add: iprev_nth_card_iMin)

end
