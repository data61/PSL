(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Fixed-points\<close>

theory OrdinalFix
imports OrdinalInverse
begin

primrec iter :: "nat \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a)"
where
  "iter 0       F x = x"
| "iter (Suc n) F x = F (iter n F x)"

definition
  oFix :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> ordinal \<Rightarrow> ordinal" where
  "oFix F a = oLimit (\<lambda>n. iter n F a)"

lemma oFix_fixed:
"\<lbrakk>continuous F; a \<le> F a\<rbrakk> \<Longrightarrow> F (oFix F a) = oFix F a"
 apply (unfold oFix_def)
 apply (simp only: continuousD)
 apply (rule order_antisym)
  apply (rule oLimit_leI, clarify)
  apply (rule_tac n="Suc n" in le_oLimitI, simp)
 apply (rule oLimit_leI, clarify)
 apply (rule_tac n=n in le_oLimitI)
 apply (induct_tac n, simp)
 apply (simp add: continuous.monoD)
done

lemma oFix_least:
"\<lbrakk>mono F; F x = x; a \<le> x\<rbrakk> \<Longrightarrow> oFix F a \<le> x"
 apply (unfold oFix_def)
 apply (rule oLimit_leI, clarify)
 apply (induct_tac n, simp_all)
 apply (erule subst)
 apply (erule monoD, assumption)
done

lemma mono_oFix: "mono F \<Longrightarrow> mono (oFix F)"
 apply (rule monoI, unfold oFix_def)
 apply (subgoal_tac "\<forall>n. iter n F x \<le> iter n F y")
  apply (rule oLimit_leI, clarify)
  apply (rule_tac n=n in le_oLimitI, erule spec)
 apply (rule allI, induct_tac n)
  apply simp
 apply (simp add: monoD)
done

lemma less_oFixD:
"\<lbrakk>x < oFix F a; mono F; F x = x\<rbrakk> \<Longrightarrow> x < a"
 apply (simp add: linorder_not_le[symmetric])
 apply (erule contrapos_nn)
by (rule oFix_least)

lemma less_oFixI: "a < F a \<Longrightarrow> a < oFix F a"
 apply (unfold oFix_def)
 apply (erule order_less_le_trans)
 apply (rule_tac n=1 in le_oLimitI)
 apply simp
done

lemma le_oFix: "a \<le> oFix F a"
 apply (unfold oFix_def)
 apply (rule_tac n=0 in le_oLimitI)
 apply simp
done

lemma le_oFix1: "F a \<le> oFix F a"
 apply (unfold oFix_def)
 apply (rule_tac n=1 in le_oLimitI)
 apply simp
done

lemma less_oFix_0D:
"\<lbrakk>x < oFix F 0; mono F\<rbrakk> \<Longrightarrow> x < F x"
 apply (unfold oFix_def, drule less_oLimitD, clarify)
 apply (erule_tac P="x < iter n F 0" in rev_mp)
 apply (induct_tac n, auto simp add: linorder_not_less)
 apply (erule order_less_le_trans)
 apply (erule monoD, assumption)
done

lemma zero_less_oFix_eq: "(0 < oFix F 0) = (0 < F 0)"
 apply (safe)
  apply (erule contrapos_pp)
  apply (simp only: linorder_not_less oFix_def)
  apply (rule oLimit_leI[rule_format])
  apply (induct_tac n, simp, simp)
 apply (erule less_oFixI)
done

lemma oFix_eq_self: "F a = a \<Longrightarrow> oFix F a = a"
 apply (unfold oFix_def)
 apply (subgoal_tac "\<forall>n. iter n F a = a", simp)
 apply (rule allI, induct_tac n, simp_all)
done


subsection \<open>Derivatives of ordinal functions\<close>

text "The derivative of F enumerates all the fixed-points of F"

definition
  oDeriv :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> ordinal \<Rightarrow> ordinal" where
  "oDeriv F = ordinal_rec (oFix F 0) (\<lambda>p x. oFix F (oSuc x))"

lemma oDeriv_0 [simp]:
"oDeriv F 0 = oFix F 0"
by (simp add: oDeriv_def)

lemma oDeriv_oSuc [simp]:
"oDeriv F (oSuc x) = oFix F (oSuc (oDeriv F x))"
by (simp add: oDeriv_def)

lemma oDeriv_oLimit [simp]:
"oDeriv F (oLimit f) = oLimit (\<lambda>n. oDeriv F (f n))"
 apply (unfold oDeriv_def)
 apply (rule ordinal_rec_oLimit, clarify)
 apply (rule order_trans[OF order_less_imp_le[OF less_oSuc]])
 apply (rule le_oFix)
done

lemma oDeriv_fixed:
"normal F \<Longrightarrow> F (oDeriv F n) = oDeriv F n"
 apply (rule_tac a=n in oLimit_induct, simp_all)
   apply (rule oFix_fixed)
    apply (erule normal.continuous)
   apply simp
  apply (rule oFix_fixed)
   apply (erule normal.continuous)
  apply (erule normal.increasing)
 apply (simp add: normal.oLimit)
done

lemma oDeriv_fixedD:
"\<lbrakk>oDeriv F x = x; normal F\<rbrakk> \<Longrightarrow> F x = x"
by (erule subst, erule oDeriv_fixed)

lemma normal_oDeriv:
"normal (oDeriv F)"
 apply (rule normalI, simp_all)
 apply (rule order_less_le_trans[OF less_oSuc])
 apply (rule le_oFix)
done

lemma oDeriv_increasing:
"continuous F \<Longrightarrow> F x \<le> oDeriv F x"
 apply (rule_tac a=x in oLimit_induct)
   apply (simp add: le_oFix1)
  apply simp
  apply (rule order_trans[OF _ le_oFix1])
  apply (erule continuous.monoD)
  apply simp
  apply (rule normal.increasing)
  apply (rule normal_oDeriv)
 apply (simp add: continuousD)
 apply (rule oLimit_leI[rule_format])
 apply (rule_tac n=n in le_oLimitI)
 apply (erule spec)
done

lemma oDeriv_total:
"\<lbrakk>normal F; F x = x\<rbrakk> \<Longrightarrow> \<exists>n. x = oDeriv F n"
 apply (subgoal_tac "\<exists>n. oDeriv F n \<le> x \<and> x < oDeriv F (oSuc n)")
  apply clarsimp
  apply (drule less_oFixD)
    apply (erule normal.mono)
   apply assumption
  apply (rule_tac x=n in exI, simp add: less_oSuc_eq_le)
 apply (rule normal.oInv_ex[OF normal_oDeriv])
 apply (simp add: oFix_least normal.mono)
done

lemma range_oDeriv:
"normal F \<Longrightarrow> range (oDeriv F) = {x. F x = x}"
by (auto intro: oDeriv_fixed dest: oDeriv_total)

end

