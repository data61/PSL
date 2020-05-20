(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Veblen Hierarchies\<close>

theory OrdinalVeblen
imports OrdinalOmega
begin

subsection \<open>Closed, unbounded sets\<close>

locale normal_set =
fixes A :: "ordinal set"
assumes closed:    "\<And>g. \<forall>n. g n \<in> A \<Longrightarrow> oLimit g \<in> A"
    and unbounded: "\<And>x. \<exists>y\<in>A. x < y"

lemma (in normal_set) less_next: "x < (LEAST z. z \<in> A \<and> x < z)"
 apply (rule LeastI2_ex)
 apply (fold Bex_def, rule unbounded)
 apply (erule conjunct2)
done

lemma (in normal_set) mem_next: "(LEAST z. z \<in> A \<and> x < z) \<in> A"
 apply (rule LeastI2_ex)
 apply (fold Bex_def, rule unbounded)
 apply (erule conjunct1)
done

lemma (in normal) normal_set_range: "normal_set (range F)"
 apply (rule normal_set.intro)
  apply (simp add: image_def)
  apply (rule_tac x="oLimit (\<lambda>n. LEAST x. g n = F x)" in exI)
  apply (simp only: oLimit)
  apply (rule_tac f=oLimit in arg_cong)
  apply (rule ext)
  apply (rule LeastI_ex)
  apply (erule spec)
 apply (rule_tac x="F (oSuc x)" in bexI)
  apply (rule order_le_less_trans [OF increasing])
  apply (simp add: cancel_less)
 apply (rule rangeI)
done

lemma oLimit_mem_INTER:
"\<lbrakk>\<forall>n. normal_set (A n); \<forall>n. A (Suc n) \<subseteq> A n;
  \<forall>n. f n \<in> A n; mono f\<rbrakk>
  \<Longrightarrow> oLimit f \<in> (\<Inter>n. A n)"
 apply (clarsimp, rename_tac k)
 apply (subgoal_tac "oLimit (\<lambda>n. f (n + k)) \<in> A k")
  apply (simp add: oLimit_shift_mono)
 apply (rule normal_set.closed [rule_format], erule spec)
 apply (rule_tac A="A (n + k)" in subsetD)
  apply (induct_tac n, simp, rename_tac m)
  apply (rule_tac B="A (m + k)" in subset_trans, simp, simp)
 apply (erule spec)
done

lemma normal_set_INTER:
"\<lbrakk>\<forall>n. normal_set (A n); \<forall>n. A (Suc n) \<subseteq> A n\<rbrakk> \<Longrightarrow> normal_set (\<Inter>n. A n)"
 apply (rule normal_set.intro)
  apply (clarsimp simp add: normal_set.closed)
 apply (rule_tac x="oLimit (\<lambda>n. LEAST y. y \<in> A n \<and> x < y)" in bexI)
  apply (rule_tac y="LEAST y. y \<in> A n \<and> x < y" in order_less_le_trans)
   apply (simp only: normal_set.less_next)
  apply (rule le_oLimit)
 apply (rule oLimit_mem_INTER, assumption+)
  apply (simp add: normal_set.mem_next)
 apply (rule mono_natI)
 apply (rule Least_le)
 apply (rule conjI)
  apply (rule subsetD, erule spec)
  apply (simp only: normal_set.mem_next)
 apply (simp only: normal_set.less_next)
done


subsection \<open>Ordering functions\<close>

text "There is a one-to-one correspondence between closed,
unbounded sets of ordinals and normal functions on ordinals."

definition
  ordering  :: "(ordinal set) \<Rightarrow> (ordinal \<Rightarrow> ordinal)" where
  "ordering A = ordinal_rec (LEAST z. z \<in> A) (\<lambda>p x. LEAST z. z \<in> A \<and> x < z)"

lemma ordering_0:
"ordering A 0 = (LEAST z. z \<in> A)"
by (simp add: ordering_def)

lemma ordering_oSuc:
"ordering A (oSuc x) = (LEAST z. z \<in> A \<and> ordering A x < z)"
by (simp add: ordering_def)

lemma (in normal_set) normal_ordering: "normal (ordering A)"
 apply (unfold ordering_def)
 apply (rule normal_ordinal_rec [rule_format])
 apply (rule less_next)
done

lemma (in normal_set) ordering_oLimit:
"ordering A (oLimit f) = oLimit (\<lambda>n. ordering A (f n))"
 apply (rule normal.oLimit)
 apply (rule normal_ordering)
done

lemma (in normal) ordering_range: "ordering (range F) = F"
 apply (rule ext, rule_tac a=x in oLimit_induct)
   apply (simp add: ordering_0)
   apply (rule Least_equality)
    apply (rule rangeI)
   apply (clarsimp simp add: cancel_le)
  apply (simp add: ordering_oSuc)
  apply (rule Least_equality)
   apply (simp add: cancel_less)
  apply (clarsimp simp add: cancel_le cancel_less oSuc_leI)
 apply (subst normal_set.ordering_oLimit)
  apply (rule normal_set_range)
 apply (simp add: oLimit)
done

lemma (in normal_set) ordering_mem: "ordering A x \<in> A"
 apply (rule_tac a=x in oLimit_induct)
   apply (subst ordering_0)
   apply (rule LeastI_ex)
   apply (cut_tac unbounded, force)
  apply (subst ordering_oSuc)
  apply (rule mem_next)
 apply (subst ordering_oLimit)
 apply (erule closed)
done

lemma (in normal_set) range_ordering_lemma:
"\<forall>y. y \<in> A \<longrightarrow> y < ordering A x \<longrightarrow> y \<in> range (ordering A)"
 apply (simp add: image_def)
 apply (rule_tac a=x in oLimit_induct, safe)
   apply (simp add: ordering_0)
   apply (drule not_less_Least, simp)
  apply (simp add: ordering_oSuc)
  apply (drule not_less_Least, simp)
  apply (force simp add: linorder_not_less order_le_less)
 apply (simp add: ordering_oLimit)
 apply (drule less_oLimitD, clarsimp)
done

lemma (in normal_set) range_ordering: "range (ordering A) = A"
 apply (safe intro!: ordering_mem)
 apply (erule_tac x="oSuc x" in range_ordering_lemma[rule_format])
 apply (rule order_less_le_trans[OF less_oSuc])
 apply (rule normal.increasing[OF normal_ordering])
done

lemma ordering_INTER_0:
"\<lbrakk>\<forall>n. normal_set (A n); \<forall>n. A (Suc n) \<subseteq> A n\<rbrakk>
 \<Longrightarrow> ordering (\<Inter>n. A n) 0 = oLimit (\<lambda>n. ordering (A n) 0)"
 apply (subst ordering_0)
 apply (rule Least_equality)
  apply (rule oLimit_mem_INTER, assumption+)
   apply (simp add: normal_set.ordering_mem)
  apply (rule mono_natI)
  apply (simp add: ordering_0)
  apply (rule Least_le)
  apply (rule subsetD, erule spec)
  apply (drule_tac x="Suc n" in spec)
  apply (drule normal_set.unbounded, clarify)
  apply (erule LeastI)
 apply (rule oLimit_leI[rule_format])
 apply (simp add: ordering_0)
 apply (rule Least_le)
 apply (erule spec)
done


subsection \<open>Critical ordinals\<close>

definition
  critical_set :: "ordinal set \<Rightarrow> ordinal \<Rightarrow> ordinal set" where
  "critical_set A =
     ordinal_rec0 A (\<lambda>p x. x \<inter> range (oDeriv (ordering x))) (\<lambda>f. \<Inter>n. f n)"

lemma critical_set_0:
"critical_set A 0 = A"
by (unfold critical_set_def, rule ordinal_rec0_0)

lemma critical_set_oSuc_lemma:
"critical_set A (oSuc n) =
  critical_set A n \<inter> range (oDeriv (ordering (critical_set A n)))"
by (unfold critical_set_def, rule ordinal_rec0_oSuc)

lemma omega_complete_INTER:
"omega_complete (\<lambda>x y. y \<subseteq> x) (\<lambda>f. \<Inter> (range f))"
 apply (rule omega_complete.intro)
  apply (rule porder.flip)
  apply (rule porder_order)
 apply (rule omega_complete_axioms.intro)
  apply fast
 apply fast
done

lemma critical_set_oLimit:
"critical_set A (oLimit f) = (\<Inter>n. critical_set A (f n))"
 apply (unfold critical_set_def)
 apply (rule omega_complete.ordinal_rec0_oLimit)
  apply (rule omega_complete_INTER)
 apply fast
done

lemma critical_set_mono:
"x \<le> y \<Longrightarrow> critical_set A y \<subseteq> critical_set A x"
 apply (unfold critical_set_def)
 apply (rule omega_complete.ordinal_rec0_mono
          [OF omega_complete_INTER])
  apply fast
 apply assumption
done

lemma (in normal_set) range_oDeriv_subset:
"range (oDeriv (ordering A)) \<subseteq> A"
 apply (clarsimp, rename_tac x)
 apply (cut_tac n=x in oDeriv_fixed[OF normal_ordering])
 apply (erule subst)
 apply (rule ordering_mem)
done

lemma normal_set_critical_set:
"normal_set A \<Longrightarrow> normal_set (critical_set A x)"
 apply (rule_tac a=x in oLimit_induct)
   apply (simp only: critical_set_0)
  apply (simp only: critical_set_oSuc_lemma)
  apply (subst Int_absorb1)
   apply (erule normal_set.range_oDeriv_subset)
  apply (rule normal.normal_set_range)
  apply (rule normal_oDeriv)
 apply (simp only: critical_set_oLimit)
 apply (erule normal_set_INTER)
 apply (rule allI, rule critical_set_mono)
 apply (simp add: strict_mono_monoD)
done

lemma critical_set_oSuc: 
"normal_set A
 \<Longrightarrow> critical_set A (oSuc x) = range (oDeriv (ordering (critical_set A x)))"
 apply (simp only: critical_set_oSuc_lemma)
 apply (rule Int_absorb1)
 apply (rule normal_set.range_oDeriv_subset)
 apply (erule normal_set_critical_set)
done


subsection \<open>Veblen hierarchy over a normal function\<close>

definition
  oVeblen :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> ordinal \<Rightarrow> ordinal \<Rightarrow> ordinal" where
  "oVeblen F = (\<lambda>x. ordering (critical_set (range F) x))"

lemma (in normal) oVeblen_0: "oVeblen F 0 = F"
 apply (unfold oVeblen_def)
 apply (subst critical_set_0)
 apply (rule ordering_range)
done

lemma (in normal) oVeblen_oSuc:
"oVeblen F (oSuc x) = oDeriv (oVeblen F x)"
 apply (unfold oVeblen_def)
 apply (subst critical_set_oSuc)
  apply (rule normal_set_range)
 apply (rule normal.ordering_range)
 apply (rule normal_oDeriv)
done

lemma (in normal) oVeblen_oLimit:
"oVeblen F (oLimit f) = ordering (\<Inter>n. range (oVeblen F (f n)))"
 apply (unfold oVeblen_def)
 apply (subst critical_set_oLimit)
 apply (cut_tac normal_set_range)
 apply (simp add: normal_set.range_ordering[OF normal_set_critical_set])
done

lemma (in normal) normal_oVeblen:
"normal (oVeblen F x)"
 apply (unfold oVeblen_def)
 apply (rule normal_set.normal_ordering)
 apply (rule normal_set_critical_set)
 apply (rule normal_set_range)
done

lemma (in normal) continuous_oVeblen_0:
"continuous (\<lambda>x. oVeblen F x 0)"
 apply (rule continuousI)
  apply (simp add: oVeblen_def critical_set_oLimit)
  apply (rule ordering_INTER_0[rule_format])
   apply (rule normal_set_critical_set)
   apply (rule normal_set_range)
  apply (rule critical_set_mono)
  apply (simp add: strict_mono_monoD)
 apply (simp only: oVeblen_oSuc)
 apply (rule oDeriv_increasing)
 apply (rule normal.continuous)
 apply (rule normal_oVeblen)
done

lemma (in normal) oVeblen_oLimit_0:
"oVeblen F (oLimit f) 0 = oLimit (\<lambda>n. oVeblen F (f n) 0)"
by (rule continuousD[OF continuous_oVeblen_0])

lemma (in normal) normal_oVeblen_0:
"0 < F 0 \<Longrightarrow> normal (\<lambda>x. oVeblen F x 0)"
 apply (rule normalI)
  apply (rule oVeblen_oLimit_0)
 apply (simp only: oVeblen_oSuc)
 apply (subst oDeriv_fixed[OF normal_oVeblen, symmetric])
 apply (rule normal.strict_monoD[OF normal_oVeblen])
 apply (simp add: zero_less_oFix_eq)
 apply (erule order_less_le_trans)
 apply (subgoal_tac "oVeblen F 0 0 \<le> oVeblen F x 0")
  apply (simp add: oVeblen_0)
 apply (rule continuous.monoD[OF _ ordinal_0_le])
 apply (rule continuous_oVeblen_0)
done

lemma (in normal) range_oVeblen:
"range (oVeblen F x) = critical_set (range F) x"
 apply (unfold oVeblen_def)
 apply (rule normal_set.range_ordering)
 apply (rule normal_set_critical_set)
 apply (rule normal_set_range)
done

lemma (in normal) range_oVeblen_subset:
"x \<le> y \<Longrightarrow> range (oVeblen F y) \<subseteq> range (oVeblen F x)"
 apply (simp only: range_oVeblen)
 apply (erule critical_set_mono)
done

lemma (in normal) oVeblen_fixed:
"\<forall>x<y. \<forall>a. oVeblen F x (oVeblen F y a) = oVeblen F y a"
 apply (rule_tac a=y in oLimit_induct)
   apply simp
  apply (clarsimp simp only: oVeblen_oSuc)
  apply (erule less_oSucE)
   apply (drule spec, drule mp, assumption)
   apply (drule_tac x="oDeriv (oVeblen F x) a" in spec)
   apply (simp add: oDeriv_fixed normal_oVeblen)
  apply simp
  apply (rule oDeriv_fixed)
  apply (rule normal_oVeblen)
 apply clarsimp
 apply (erule less_oLimitE)
 apply (drule spec, drule spec, drule mp, assumption)
 apply (subgoal_tac "oVeblen F (oLimit f) a \<in> range (oVeblen F (f n))")
  apply clarsimp
 apply (rule_tac A="range (oVeblen F (oLimit f))" in subsetD)
  apply (rule range_oVeblen_subset)
  apply (rule le_oLimit)
 apply (rule rangeI)
done

lemma (in normal) critical_set_fixed:
"0 < z \<Longrightarrow> range (oVeblen F z) = {x. \<forall>y<z. oVeblen F y x = x}"
 apply (rule equalityI)
  apply (clarsimp simp add: oVeblen_fixed)
 apply (erule rev_mp)
 apply (rule_tac a=z in oLimit_induct)
   apply simp
  apply clarsimp
  apply (simp add: oVeblen_oSuc range_oDeriv normal_oVeblen)
 apply clarsimp
 apply (simp add: range_oVeblen)
 apply (clarsimp simp add: critical_set_oLimit)
 apply (rule_tac A="critical_set (range F) (f (Suc xa))" in subsetD)
  apply (rule critical_set_mono)
  apply (simp add: strict_mono_monoD)
 apply (drule_tac x="Suc xa" in spec, drule mp)
  apply (rule_tac y="f xa" in order_le_less_trans, simp)
  apply (erule OrdinalInduct.strict_monoD, simp)
 apply (erule subsetD, clarsimp)
 apply (drule spec, erule mp)
 apply (erule order_less_le_trans)
 apply (rule le_oLimit)
done

subsection \<open>Veblen hierarchy over $\lambda x.\ 1 + x$\<close>

lemma oDeriv_id: "oDeriv id = id"
 apply (rule ext, rule_tac a=x in oLimit_induct)
   apply (simp add: oFix_eq_self)
  apply (simp add: oFix_eq_self)
 apply simp
done

lemma oFix_plus: "oFix (\<lambda>x. a + x) 0 = a * \<omega>"
 apply (simp add: oFix_def omega_def)
 apply (rule_tac f=oLimit in arg_cong)
 apply (rule ext, induct_tac n, simp)
 apply (simp, rename_tac n)
 apply (induct_tac n, simp)
 apply (simp add: ordinal_plus_assoc[symmetric])
done

lemma oDeriv_plus: "oDeriv ((+) a) = ((+) (a * \<omega>))"
 apply (rule ext, rule_tac a=x in oLimit_induct)
   apply (simp add: oFix_plus)
  apply (simp add: oFix_eq_self
                   ordinal_plus_assoc[symmetric]
                   ordinal_plus_times_omega)
 apply simp
done

lemma oVeblen_1_plus: "oVeblen ((+) 1) x = ((+) (\<omega> ** x))"
 apply (rule_tac a=x in wf_induct[OF wf], simp)
 apply (rule_tac a=x in ordinal_cases)
   apply (simp add: normal.oVeblen_0[OF normal_plus])
  apply (simp add: normal.oVeblen_oSuc[OF normal_plus])
  apply (simp add: oDeriv_plus)
 apply clarsimp
 apply (rule normal_range_eq)
   apply (rule normal.normal_oVeblen[OF normal_plus])
  apply (rule normal_plus)
 apply (subst normal.critical_set_fixed[OF normal_plus])
  apply (rule_tac y="f 0" in order_le_less_trans, simp)
  apply (simp add: strict_mono_less_oLimit)
 apply safe
  apply (simp add: image_def)
  apply (rule exI, rule ordinal_plus_minus2[symmetric])
  apply (rule oLimit_leI[rule_format])
  apply (subgoal_tac "\<omega> ** f n + x = x", erule subst, simp)
  apply (drule_tac x="f n" in spec)
  apply (simp add: strict_mono_less_oLimit)
 apply simp
 apply (simp only: ordinal_exp_oLimit[symmetric] zero_less_omega)
 apply (simp only: ordinal_plus_assoc[symmetric])
 apply (simp only: absorb_omega_exp2)
done

end
