(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Continuity\<close>

theory OrdinalCont
imports OrdinalInduct
begin

subsection \<open>Continuous functions\<close>

locale continuous =
  fixes F :: "ordinal \<Rightarrow> ordinal"
  assumes cont: "F (oLimit f) = oLimit (\<lambda>n. F (f n))"

lemmas continuousD = continuous.cont

lemma (in continuous) mono: "mono F"
 apply (rule monoI)
 apply (cut_tac f="case_nat x (\<lambda>n. y)" in cont)
 apply (subgoal_tac "\<forall>x y. oLimit (case_nat x (\<lambda>n. y)) = max x y")
  apply (subgoal_tac "\<forall>x y n. F (case n of 0 \<Rightarrow> x | Suc n \<Rightarrow> y)
                          = (case n of 0 \<Rightarrow> F x | Suc n \<Rightarrow> F y)")
   apply (simp add: max_def)
   apply (erule ssubst, simp)
  apply (simp split: nat.split)
 apply (clarify, rule order_antisym)
  apply (rule oLimit_leI)
  apply (simp split: nat.split add: max.cobounded1 max.cobounded2)
 apply (simp, safe)
  apply (rule_tac n=0 in le_oLimitI, simp)
 apply (rule_tac n=1 in le_oLimitI, simp)
done

lemma (in continuous) monoD: "x \<le> y \<Longrightarrow> F x \<le> F y"
by (erule monoD[OF mono])

lemma continuousI:
assumes lim: "\<And>f. strict_mono f \<Longrightarrow> F (oLimit f) = oLimit (\<lambda>n. F (f n))"
assumes suc: "\<And>x. F x \<le> F (oSuc x)"
shows "continuous F"
 apply (subgoal_tac "mono F")
  apply (rule continuous.intro)
  apply (case_tac "\<forall>n. f n < oLimit f")
   apply (subgoal_tac "oLimit (\<lambda>n. f (make_mono f n)) = oLimit f")
    apply (erule subst)
    apply (rule trans[OF lim])
     apply (erule strict_mono_f_make_mono)
    apply (rule oLimit_eqI)
     apply (rule exI, rule order_refl)
   apply (rule_tac x=n in exI)
    apply (erule monoD)
    apply (rule le_f_make_mono, assumption)
    apply (induct_tac n, simp)
    apply (simp add: Suc_le_eq)
    apply (erule order_le_less_trans)
    apply (erule make_mono_less)
   apply (erule oLimit_make_mono_eq)
  apply (clarsimp simp add: linorder_not_less)
  apply (drule order_antisym[OF _ le_oLimit], simp)
  apply (rule order_antisym[OF le_oLimit])
  apply (rule oLimit_leI[rule_format])
  apply (erule monoD)
  apply (erule subst)
  apply (rule le_oLimit)
 apply (subgoal_tac "\<forall>y x. x \<le> y \<longrightarrow> F x \<le> F y")
  apply (rule monoI, simp)
 apply (rule allI, rule_tac a=y in oLimit_induct)
   apply simp
  apply (clarsimp, erule le_oSucE)
   apply (drule spec, drule mp, assumption)
   apply (erule order_trans, rule suc)
  apply simp
 apply (clarsimp simp add: lim, erule le_oLimitE)
  apply (drule_tac x=n in spec)
  apply (drule_tac x=x in  spec, drule mp, assumption)
  apply (erule order_trans)
  apply (rule le_oLimit)
 apply (simp add: lim)
done


subsection \<open>Normal functions\<close>

locale normal = continuous +
  assumes strict: "strict_mono F"

lemma (in normal) mono: "mono F"
by (rule mono)

lemma (in normal) continuous: "continuous F"
by (rule continuous.intro, rule cont)

lemma (in normal) monoD: "x \<le> y \<Longrightarrow> F x \<le> F y"
by (rule monoD)

lemma (in normal) strict_monoD: "x < y \<Longrightarrow> F x < F y"
by (erule strict_monoD[OF strict])

lemma (in normal) cancel_eq: "(F x = F y) = (x = y)"
by (rule strict_mono_cancel_eq[OF strict])

lemma (in normal) cancel_less: "(F x < F y) = (x < y)"
by (rule strict_mono_cancel_less[OF strict])

lemma (in normal) cancel_le: "(F x \<le> F y) = (x \<le> y)"
by (rule strict_mono_cancel_le[OF strict])

lemma (in normal) oLimit: "F (oLimit f) = oLimit (\<lambda>n. F (f n))"
by (rule cont)

lemma (in normal) increasing: "x \<le> F x"
 apply (rule_tac a=x in oLimit_induct)
   apply simp
  apply (rule oSuc_leI)
  apply (erule order_le_less_trans)
  apply (rule strict_monoD[OF less_oSuc])
 apply (simp add: oLimit)
 apply (rule oLimit_leI, clarify)
 apply (rule order_trans, erule spec)
 apply (rule le_oLimit)
done

lemma normalI:
assumes lim: "\<And>f. strict_mono f \<Longrightarrow> F (oLimit f) = oLimit (\<lambda>n. F (f n))"
assumes suc: "\<And>x. F x < F (oSuc x)"
shows "normal F"
 apply (rule normal.intro[OF _ normal_axioms.intro])
  apply (simp add: continuousI order_less_imp_le suc lim)
 apply (subgoal_tac "\<forall>y x. x < y \<longrightarrow> F x < F y")
  apply (rule strict_monoI, simp)
 apply (rule allI, rule_tac a=y in oLimit_induct)
   apply simp
  apply (clarsimp, erule less_oSucE)
   apply (drule spec, drule mp, assumption)
   apply (erule order_less_trans, rule suc)
  apply (simp add: suc)
 apply (clarsimp simp add: lim, erule less_oLimitE)
 apply (drule spec, drule spec, drule mp, assumption)
 apply (erule order_less_le_trans)
 apply (rule le_oLimit)
done

lemma normal_range_le:
"\<lbrakk>normal F; normal G; range G \<subseteq> range F\<rbrakk> \<Longrightarrow> F x \<le> G x"
 apply (rule_tac a=x in oLimit_induct)
   apply (subgoal_tac "G 0 \<in> range F")
    apply (clarsimp simp add: normal.cancel_le)
   apply (erule subsetD, rule rangeI)
  apply (subgoal_tac "G (oSuc x) \<in> range F")
   apply (clarsimp simp add: normal.cancel_le)
   apply (rename_tac y)
   apply (rule oSuc_leI)
   apply (subgoal_tac "F x < F y", simp add: normal.cancel_less)
   apply (erule order_le_less_trans)
   apply (erule subst)
   apply (simp add: normal.cancel_less)
  apply (erule subsetD, rule rangeI)
 apply (simp only: normal.oLimit)
 apply (rule oLimit_leI[rule_format])
 apply (rule_tac n=n in le_oLimitI)
 apply (erule spec)
done

lemma normal_range_eq:
"\<lbrakk>normal F; normal G; range F = range G\<rbrakk> \<Longrightarrow> F = G"
 apply (rule ext, rule order_antisym)
  apply (simp add: normal_range_le)
 apply (simp add: normal_range_le)
done


end
