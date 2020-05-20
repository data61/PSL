(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Inverse Functions\<close>

theory OrdinalInverse
imports OrdinalArith
begin

lemma (in normal) oInv_ex:
"F 0 \<le> a \<Longrightarrow> \<exists>q. F q \<le> a \<and> a < F (oSuc q)"
 apply (subgoal_tac "\<forall>z. a < F z \<longrightarrow> (\<exists>q<z. F q \<le> a \<and> a < F (oSuc q))")
  apply (drule_tac x="oSuc a" in spec, drule mp)
   apply (rule_tac y="F a" in order_le_less_trans)
    apply (rule increasing)
   apply (rule strict_monoD[OF less_oSuc])
  apply force
 apply (rule allI, rule_tac a=z in oLimit_induct)
   apply simp
  apply clarsimp
  apply (case_tac "a < F x")
   apply clarsimp
   apply (rule_tac x=q in exI)
   apply (simp add: order_less_trans[OF _ less_oSuc])
  apply (rule_tac x=x in exI, simp)
 apply (clarsimp simp add: oLimit)
 apply (drule less_oLimitD, clarify)
 apply (drule spec, drule mp, assumption)
 apply (clarify, rule_tac x=q in exI)
 apply (simp add: order_less_le_trans[OF _ le_oLimit])
done

lemma oInv_uniq:
"\<lbrakk>mono (F::ordinal \<Rightarrow> ordinal);
  F x \<le> a \<and> a < F (oSuc x); F y \<le> a \<and> a < F (oSuc y)\<rbrakk>
 \<Longrightarrow> x = y"
 apply clarify
 apply (rule_tac x=x and y=y in linorder_cases)
   apply (subgoal_tac "a < a", simp)
   apply (erule_tac y="F (oSuc x)" in order_less_le_trans)
   apply (rule_tac y="F y" in order_trans)
    apply (erule monoD, erule oSuc_leI)
   apply assumption
  apply assumption
 apply (subgoal_tac "a < a", simp)
 apply (erule_tac y="F (oSuc y)" in order_less_le_trans)
 apply (rule_tac y="F x" in order_trans)
  apply (erule monoD, erule oSuc_leI)
 apply assumption
done

definition
  oInv :: "(ordinal \<Rightarrow> ordinal) \<Rightarrow> ordinal \<Rightarrow> ordinal" where
  "oInv F a = (if F 0 \<le> a then (THE x. F x \<le> a \<and> a < F (oSuc x)) else 0)"

lemma (in normal) oInv_bounds:
"F 0 \<le> a \<Longrightarrow> F (oInv F a) \<le> a \<and> a < F (oSuc (oInv F a))"
 apply (simp add: oInv_def)
 apply (rule theI')
 apply (rule ex_ex1I)
  apply (simp add: oInv_ex)
 apply (simp add: oInv_uniq[OF mono])
done

lemma (in normal) oInv_bound1:
"F 0 \<le> a \<Longrightarrow> F (oInv F a) \<le> a"
by (rule oInv_bounds[THEN conjunct1])

lemma (in normal) oInv_bound2:
"a < F (oSuc (oInv F a))"
 apply (case_tac "F 0 \<le> a")
  apply (simp only: oInv_bounds[THEN conjunct2])
 apply (simp add: oInv_def, simp add: linorder_not_le)
 apply (erule order_less_le_trans)
 apply (simp add: cancel_le)
done

lemma (in normal) oInv_equality:
"\<lbrakk>F x \<le> a; a < F (oSuc x)\<rbrakk> \<Longrightarrow> oInv F a = x"
 apply (subgoal_tac "F 0 \<le> a")
  apply (simp add: oInv_def)
  apply (rule the_equality)
   apply simp
  apply (simp add: oInv_uniq[OF mono])
 apply (rule_tac y="F x" in order_trans)
  apply (simp add: cancel_le)
 apply assumption
done

lemma (in normal) oInv_inverse: "oInv F (F x) = x"
by (rule oInv_equality, simp_all add: cancel_less)

lemma (in normal) oInv_equality': "a = F x \<Longrightarrow> oInv F a = x"
by (simp add: oInv_inverse)

lemma (in normal) oInv_eq_0: "a \<le> F 0 \<Longrightarrow> oInv F a = 0"
 apply (case_tac "F 0 \<le> a")
  apply (rule oInv_equality')
  apply (simp only: order_antisym)
 apply (simp add: oInv_def)
done

lemma (in normal) oInv_less:
"\<lbrakk>F 0 \<le> a; a < F z\<rbrakk> \<Longrightarrow> oInv F a < z"
 apply (subst cancel_less[symmetric])
 apply (simp only: order_le_less_trans[OF oInv_bound1])
done

lemma (in normal) le_oInv:
"F z \<le> a \<Longrightarrow> z \<le> oInv F a"
 apply (subst less_oSuc_eq_le[symmetric])
 apply (subst cancel_less[symmetric])
 apply (erule order_le_less_trans)
 apply (rule oInv_bound2)
done

lemma (in normal) less_oInvD:
"x < oInv F a \<Longrightarrow> F (oSuc x) \<le> a"
 apply (case_tac "F 0 \<le> a")
  apply (rule order_trans[OF _ oInv_bound1])
   apply (simp add: cancel_le oSuc_leI)
  apply assumption
 apply (simp add: oInv_def)
done

lemma (in normal) oInv_le:
"a < F (oSuc x) \<Longrightarrow> oInv F a \<le> x"
 apply (erule contrapos_pp)
 apply (simp add: linorder_not_less linorder_not_le less_oInvD)
done

lemma (in normal) mono_oInv: "mono (oInv F)"
proof
  fix x y :: ordinal
  assume "x \<le> y"
  show "oInv F x \<le> oInv F y"
  proof (rule linorder_le_cases [of x "F 0"])
    assume "x \<le> F 0" then show ?thesis by (simp add: oInv_eq_0)
  next
    assume "F 0 \<le> x" show ?thesis
      by (rule le_oInv, simp only: \<open>x \<le> y\<close> \<open>F 0 \<le> x\<close> order_trans [OF oInv_bound1])
  qed
qed

lemma (in normal) oInv_decreasing:
"F 0 \<le> x \<Longrightarrow> oInv F x \<le> x"
 apply (subst cancel_le[symmetric])
 apply (rule_tac y=x in order_trans)
  apply (erule oInv_bound1)
 apply (rule increasing)
done


subsection \<open>Division\<close>

instantiation ordinal :: modulo
begin

definition
  div_ordinal_def:
   "x div y = (if 0 < y then oInv ((*) y) x else 0)"

definition
  mod_ordinal_def: 
   "x mod y = ((x::ordinal) - y * (x div y))"

instance ..

end

lemma ordinal_divI: "\<lbrakk>x = y * q + r; r < y\<rbrakk> \<Longrightarrow> x div y = (q::ordinal)"
 apply (simp add: div_ordinal_def, safe)
 apply (simp add: normal.oInv_equality[OF normal_times])
done

lemma ordinal_times_div_le: "y * (x div y) \<le> (x::ordinal)"
 apply (simp add: div_ordinal_def, safe)
 apply (erule normal.oInv_bound1[OF normal_times])
 apply simp
done

lemma ordinal_less_times_div_plus:
"0 < y \<Longrightarrow> x < y * (x div y) + (y::ordinal)"
 apply (simp add: div_ordinal_def)
 apply (subst ordinal_times_oSuc[symmetric])
 apply (erule normal.oInv_bound2[OF normal_times])
done

lemma ordinal_modI: "\<lbrakk>x = y * q + r; r < y\<rbrakk> \<Longrightarrow> x mod y = (r::ordinal)"
 apply (unfold mod_ordinal_def)
 apply (rule ordinal_minusI)
 apply (simp add: ordinal_divI)
done

lemma ordinal_mod_less: "0 < y \<Longrightarrow> x mod y < (y::ordinal)"
 apply (unfold mod_ordinal_def)
 apply (simp add: ordinal_times_div_le)
 apply (simp add: div_ordinal_def)
 apply (subst ordinal_times_oSuc[symmetric])
 apply (erule normal.oInv_bound2[OF normal_times])
done

lemma ordinal_div_plus_mod: "y * (x div y) + (x mod y) = (x::ordinal)"
 apply (simp add: mod_ordinal_def)
 apply (rule ordinal_plus_minus2)
 apply (rule ordinal_times_div_le)
done

lemma ordinal_div_less: "x < y * z \<Longrightarrow> x div y < (z::ordinal)"
 apply (auto simp add: div_ordinal_def)
 apply (simp add: normal.oInv_less[OF normal_times])
done

lemma ordinal_le_div: "\<lbrakk>0 < y; y * z \<le> x\<rbrakk> \<Longrightarrow> (z::ordinal) \<le> x div y"
 apply (auto simp add: div_ordinal_def)
 apply (simp add: normal.le_oInv[OF normal_times])
done

lemma ordinal_mono_div: "mono (\<lambda>x. x div y::ordinal)"
 apply (case_tac "y = 0")
  apply (simp add: div_ordinal_def monoI)
 apply (simp add: div_ordinal_def normal.mono_oInv[OF normal_times])
done

lemma ordinal_div_monoL: "x \<le> x' \<Longrightarrow> x div y \<le> x' div (y::ordinal)"
by (erule monoD[OF ordinal_mono_div])

lemma ordinal_div_decreasing: "(x::ordinal) div y \<le> x"
 apply (auto simp add: div_ordinal_def)
 apply (simp add: normal.oInv_decreasing[OF normal_times])
done

lemma ordinal_div_0: "x div 0 = (0::ordinal)"
by (simp add: div_ordinal_def)

lemma ordinal_mod_0: "x mod 0 = (x::ordinal)"
by (simp add: mod_ordinal_def)


subsection \<open>Derived properties of division\<close>

lemma ordinal_div_1 [simp]: "x div oSuc 0 = x"
by (rule_tac r=0 in ordinal_divI, simp_all)

lemma ordinal_mod_1 [simp]: "x mod oSuc 0 = 0"
by (rule_tac q=x in ordinal_modI, simp_all)

lemma ordinal_div_self [simp]: "0 < x \<Longrightarrow> x div x = (1::ordinal)"
by (rule_tac r=0 in ordinal_divI, simp_all)

lemma ordinal_mod_self [simp]: "x mod x = (0::ordinal)"
 apply (case_tac "x=0", simp add: ordinal_mod_0, simp)
 apply (rule_tac q=1 in ordinal_modI, simp_all)
done

lemma ordinal_div_greater [simp]: "x < y \<Longrightarrow> x div y = (0::ordinal)"
by (rule_tac r=x in ordinal_divI, simp_all)

lemma ordinal_mod_greater [simp]: "x < y \<Longrightarrow> x mod y = (x::ordinal)"
by (rule_tac q=0 in ordinal_modI, simp_all)

lemma ordinal_0_div [simp]: "0 div x = (0::ordinal)"
by (case_tac "x=0", simp add: ordinal_div_0, simp)

lemma ordinal_0_mod [simp]: "0 mod x = (0::ordinal)"
by (case_tac "x=0", simp add: ordinal_mod_0, simp)

lemma ordinal_1_dvd [simp]: "oSuc 0 dvd x"
by (rule_tac k=x in dvdI, simp)

lemma ordinal_dvd_mod: "y dvd x = (x mod y = (0::ordinal))"
 apply safe
  apply (erule dvdE)
  apply (case_tac "y=0", simp add: ordinal_mod_0, simp)
  apply (rule ordinal_modI, simp, simp)
 apply (cut_tac x=x and y=y in ordinal_div_plus_mod)
 apply (rule_tac k="x div y" in dvdI, simp)
done

lemma ordinal_dvd_times_div:
"y dvd x \<Longrightarrow> y * (x div y) = (x::ordinal)"
 apply (cut_tac x=x and y=y in ordinal_div_plus_mod)
 apply (simp add: ordinal_dvd_mod)
done

lemma ordinal_dvd_oLimit: "\<forall>n. x dvd f n \<Longrightarrow> x dvd oLimit f"
 apply (rule_tac k="oLimit (\<lambda>n. f n div x)" in dvdI)
 apply (simp add: ordinal_dvd_times_div)
done


subsection \<open>Logarithms\<close>

definition
  oLog :: "ordinal \<Rightarrow> ordinal \<Rightarrow> ordinal" where
  "oLog b = (\<lambda>x. if 1 < b then oInv ((**) b) x else 0)"

lemma ordinal_oLogI:
"\<lbrakk>b ** y \<le> x; x < b ** y * b\<rbrakk> \<Longrightarrow> oLog b x = y"
 apply (rule_tac x=1 and y=b in linorder_cases, simp_all)
 apply (simp add: oLog_def normal.oInv_equality[OF normal_exp])
done

lemma ordinal_exp_oLog_le:
"\<lbrakk>0 < x; oSuc 0 < b\<rbrakk> \<Longrightarrow> b ** (oLog b x) \<le> x"
 apply (simp add: oLog_def)
 apply (frule_tac order_less_trans[OF less_oSuc])
 apply (simp add: normal.oInv_bound1[OF normal_exp] oSuc_leI)
done

lemma ordinal_less_exp_oLog:
"oSuc 0 < b \<Longrightarrow> x < b ** (oLog b x) * b"
 apply (simp add: oLog_def)
 apply (subst ordinal_exp_oSuc[symmetric])
 apply (erule normal.oInv_bound2[OF normal_exp])
done

lemma ordinal_oLog_less:
"\<lbrakk>0 < x; oSuc 0 < b; x < b ** y\<rbrakk> \<Longrightarrow> oLog b x < y"
 apply (simp add: oLog_def)
 apply (frule_tac order_less_trans[OF less_oSuc])
 apply (simp add: normal.oInv_less[OF normal_exp] oSuc_leI)
done

lemma ordinal_le_oLog:
"\<lbrakk>oSuc 0 < b; b ** y \<le> x\<rbrakk> \<Longrightarrow> y \<le> oLog b x"
by (simp add: oLog_def normal.le_oInv[OF normal_exp])

lemma ordinal_oLogI2:
"\<lbrakk>oSuc 0 < b; x = b ** y * q + r; 0 < q; q < b; r < b ** y\<rbrakk> \<Longrightarrow> oLog b x = y"
 apply simp
 apply (rule ordinal_oLogI)
  apply (rule_tac y="b ** y * q" in order_trans, simp, simp)
 apply (rule order_less_le_trans)
  apply (erule ordinal_plus_strict_monoR)
 apply (subst ordinal_times_oSuc[symmetric])
 apply (rule ordinal_times_monoR)
 apply (erule oSuc_leI)
done

lemma ordinal_div_exp_oLog_less:
"oSuc 0 < b \<Longrightarrow> x div (b ** oLog b x) < b"
 apply (frule_tac order_less_trans[OF less_oSuc])
 apply (case_tac "x=0", simp_all)
 apply (rule ordinal_div_less)
by (rule ordinal_less_exp_oLog)

lemma ordinal_oLog_base_0: "oLog 0 x = 0"
by (simp add: oLog_def)

lemma ordinal_oLog_base_1: "oLog (oSuc 0) x = 0"
by (simp add: oLog_def)

lemma ordinal_oLog_0: "oLog b 0 = 0"
by (simp add: oLog_def normal.oInv_eq_0[OF normal_exp])

lemma ordinal_oLog_exp: "oSuc 0 < b \<Longrightarrow> oLog b (b ** x) = x"
by (simp add: oLog_def normal.oInv_inverse[OF normal_exp])

lemma ordinal_oLog_self: "oSuc 0 < b \<Longrightarrow> oLog b b = oSuc 0"
 apply (subgoal_tac "oLog b (b ** oSuc 0) = oSuc 0")
  apply (simp only: ordinal_exp_1)
 apply (simp only: ordinal_oLog_exp)
done

lemma ordinal_mono_oLog: "mono (oLog b)"
 apply (case_tac "oSuc 0 < b")
  apply (simp add: oLog_def normal.mono_oInv[OF normal_exp])
 apply (simp add: oLog_def monoI)
done

lemma ordinal_oLog_monoR: "x \<le> y \<Longrightarrow> oLog b x \<le> oLog b y"
by (erule monoD[OF ordinal_mono_oLog])

lemma ordinal_oLog_decreasing: "oLog b x \<le> x"
 apply (rule_tac x=b and y=1 in linorder_cases)
   apply (simp add: ordinal_oLog_base_0)
  apply (simp add: ordinal_oLog_base_1)
 apply (case_tac "x = 0")
  apply (simp add: ordinal_oLog_0)
 apply (simp add: oLog_def)
 apply (simp add: normal.oInv_decreasing[OF normal_exp] oSuc_leI)
done

end
