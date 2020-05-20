(*  Title:       Countable Ordinals

    Author:      Brian Huffman, 2005
    Maintainer:  Brian Huffman <brianh at cse.ogi.edu>
*)

section \<open>Ordinal Arithmetic\<close>

theory OrdinalArith
imports OrdinalRec
begin

subsection \<open>Addition\<close>

instantiation ordinal :: plus
begin

definition
  "(+) = (\<lambda>x. ordinal_rec x (\<lambda>p. oSuc))"

instance ..

end

lemma normal_plus: "normal ((+) x)"
by (simp add: plus_ordinal_def normal_ordinal_rec)

lemma ordinal_plus_0 [simp]: "x + 0 = (x::ordinal)"
by (simp add: plus_ordinal_def)

lemma ordinal_plus_oSuc [simp]: "x + oSuc y = oSuc (x + y)"
by (simp add: plus_ordinal_def)

lemma ordinal_plus_oLimit [simp]: "x + oLimit f = oLimit (\<lambda>n. x + f n)"
by (simp add: normal.oLimit normal_plus)

lemma ordinal_0_plus [simp]: "0 + x = (x::ordinal)"
by (rule_tac a=x in oLimit_induct, simp_all)

lemma ordinal_plus_assoc:
"(x + y) + z = x + (y + z::ordinal)"
by (rule_tac a=z in oLimit_induct, simp_all)

lemma ordinal_plus_monoL [rule_format]:
"\<forall>x x'. x \<le> x' \<longrightarrow> x + y \<le> x' + (y::ordinal)"
 apply (rule_tac a=y in oLimit_induct, simp_all)
 apply clarify
 apply (rule oLimit_leI, clarify)
 apply (rule_tac n=n in le_oLimitI)
 apply simp
done

lemma ordinal_plus_monoR: "y \<le> y' \<Longrightarrow> x + y \<le> x + (y'::ordinal)"
by (rule normal.monoD[OF normal_plus])

lemma ordinal_plus_mono:
"\<lbrakk>x \<le> x'; y \<le> y'\<rbrakk> \<Longrightarrow> x + y \<le> x' + (y'::ordinal)"
by (rule order_trans[OF ordinal_plus_monoL ordinal_plus_monoR])

lemma ordinal_plus_strict_monoR: "y < y' \<Longrightarrow> x + y < x + (y'::ordinal)"
by (rule normal.strict_monoD[OF normal_plus])

lemma ordinal_le_plusL [simp]: "y \<le> x + (y::ordinal)"
by (cut_tac ordinal_plus_monoL[OF ordinal_0_le], simp)

lemma ordinal_le_plusR [simp]: "x \<le> x + (y::ordinal)"
by (cut_tac ordinal_plus_monoR[OF ordinal_0_le], simp)

lemma ordinal_less_plusR: "0 < y \<Longrightarrow> x < x + (y::ordinal)"
by (drule_tac ordinal_plus_strict_monoR, simp)

lemma ordinal_plus_left_cancel [simp]:
"(w + x = w + y) = (x = (y::ordinal))"
by (rule normal.cancel_eq[OF normal_plus])

lemma ordinal_plus_left_cancel_le [simp]:
"(w + x \<le> w + y) = (x \<le> (y::ordinal))"
by (rule normal.cancel_le[OF normal_plus])

lemma ordinal_plus_left_cancel_less [simp]:
"(w + x < w + y) = (x < (y::ordinal))"
by (rule normal.cancel_less[OF normal_plus])

lemma ordinal_plus_not_0: "(0 < x + y) = (0 < x \<or> 0 < (y::ordinal))"
 apply safe
   apply simp
  apply (erule order_less_le_trans, rule ordinal_le_plusR)
 apply (erule order_less_le_trans, rule ordinal_le_plusL)
done

lemma not_inject: "(\<not> P) = (\<not> Q) \<Longrightarrow> P = Q"
by auto

lemma ordinal_plus_eq_0:
"((x::ordinal) + y = 0) = (x = 0 \<and> y = 0)"
by (rule not_inject, simp add: ordinal_plus_not_0)


subsection \<open>Subtraction\<close>

instantiation ordinal :: minus
begin

definition
  minus_ordinal_def:
    "x - y = ordinal_rec 0 (\<lambda>p w. if y \<le> p then oSuc w else w) x"

instance ..

end

lemma continuous_minus: "continuous (\<lambda>x. x - y)"
 apply (unfold minus_ordinal_def)
 apply (rule continuous_ordinal_rec)
 apply (simp add: order_less_imp_le)
done

lemma ordinal_0_minus [simp]: "0 - x = (0::ordinal)"
by (simp add: minus_ordinal_def)

lemma ordinal_oSuc_minus [simp]: "y \<le> x \<Longrightarrow> oSuc x - y = oSuc (x - y)"
by (simp add: minus_ordinal_def)

lemma ordinal_oLimit_minus [simp]: "oLimit f - y = oLimit (\<lambda>n. f n - y)"
by (rule continuousD[OF continuous_minus])

lemma ordinal_minus_0 [simp]: "x - 0 = (x::ordinal)"
by (rule_tac a=x in oLimit_induct, simp_all)

lemma ordinal_oSuc_minus2: "x < y \<Longrightarrow> oSuc x - y = x - y"
by (simp add: minus_ordinal_def linorder_not_le[symmetric])

lemma ordinal_minus_eq_0 [rule_format, simp]:
"x \<le> y \<longrightarrow> x - y = (0::ordinal)"
 apply (rule_tac a=x in oLimit_induct)
   apply simp
  apply (simp add: ordinal_oSuc_minus2 order_less_imp_le oSuc_le_eq_less)
 apply (simp add: order_trans[OF le_oLimit])
done

lemma ordinal_plus_minus1 [simp]: "(x + y) - x = (y::ordinal)"
by (rule_tac a=y in oLimit_induct, simp_all)

lemma ordinal_plus_minus2 [simp]: "x \<le> y \<Longrightarrow> x + (y - x) = (y::ordinal)"
 apply (subgoal_tac "\<forall>z. y < x + z \<longrightarrow> x + (y - x) = y")
  apply (drule_tac x="oSuc y" in spec, erule mp)
  apply (rule order_less_le_trans[OF less_oSuc], simp)
 apply (rule allI, rule_tac a=z in oLimit_induct)
   apply (simp add: linorder_not_less[symmetric])
  apply (clarsimp simp add: less_oSuc_eq_le)
 apply (clarsimp, drule less_oLimitD, clarsimp)
done

lemma ordinal_minusI: "x = y + z \<Longrightarrow> x - y = (z::ordinal)"
by simp

lemma ordinal_minus_less_eq [simp]:
"(y::ordinal) \<le> x \<Longrightarrow> (x - y < z) = (x < y + z)"
 apply (subgoal_tac "(x - y < z) = (y + (x - y) < y + z)", simp)
 apply (simp only: ordinal_plus_left_cancel_less)
done

lemma ordinal_minus_le_eq [simp]:
"(x - y \<le> z) = (x \<le> y + (z::ordinal))"
 apply (rule_tac x=x and y=y in linorder_le_cases)
  apply (simp, erule order_trans, simp)
 apply (subgoal_tac "(x - y \<le> z) = (y + (x - y) \<le> y + z)", simp)
 apply (simp only: ordinal_plus_left_cancel_le)
done

lemma ordinal_minus_monoL: "x \<le> y \<Longrightarrow> x - z \<le> y - (z::ordinal)"
by (erule continuous.monoD[OF continuous_minus])

lemma ordinal_minus_monoR: "x \<le> y \<Longrightarrow> z - y \<le> z - (x::ordinal)"
 apply (rule_tac x=y and y=z in linorder_le_cases)
  apply (subst ordinal_minus_le_eq)
  apply (subgoal_tac "x + (z - x) \<le> y + (z - x)")
   apply (drule order_trans, assumption, simp)
  apply (erule ordinal_plus_monoL)
 apply simp
done


subsection \<open>Multiplication\<close>

instantiation ordinal :: times
begin

definition
  times_ordinal_def: "(*) = (\<lambda>x. ordinal_rec 0 (\<lambda>p w. w + x))"

instance ..

end

lemma continuous_times: "continuous ((*) x)"
by (simp add: times_ordinal_def continuous_ordinal_rec)

lemma normal_times: "0 < x \<Longrightarrow> normal ((*) x)"
 apply (unfold times_ordinal_def)
 apply (rule normal_ordinal_rec[rule_format], rename_tac y)
 apply (subgoal_tac "y + 0 < y + x", simp)
 apply (simp only: ordinal_plus_left_cancel_less)
done

lemma ordinal_times_0 [simp]: "x * 0 = (0::ordinal)"
by (simp add: times_ordinal_def)

lemma ordinal_times_oSuc [simp]: "x * oSuc y = (x * y) + x"
by (simp add: times_ordinal_def)

lemma ordinal_times_oLimit [simp]: "x * oLimit f = oLimit (\<lambda>n. x * f n)"
by (simp add: times_ordinal_def ordinal_rec_oLimit)

lemma ordinal_0_times [simp]: "0 * x = (0::ordinal)"
by (rule_tac a=x in oLimit_induct, simp_all)

lemma ordinal_1_times [simp]: "oSuc 0 * x = (x::ordinal)"
by (rule_tac a=x in oLimit_induct, simp_all)

lemma ordinal_times_1 [simp]: "x * oSuc 0 = (x::ordinal)"
by simp

lemma ordinal_times_distrib:
"x * (y + z) = (x * y) + (x * z::ordinal)"
by (rule_tac a=z in oLimit_induct, simp_all add: ordinal_plus_assoc)

lemma ordinal_times_assoc:
"(x * y::ordinal) * z = x * (y * z)"
by (rule_tac a=z in oLimit_induct, simp_all add: ordinal_times_distrib)

lemma ordinal_times_monoL [rule_format]:
"\<forall>x x'. x \<le> x' \<longrightarrow> x * y \<le> x' * (y::ordinal)"
 apply (rule_tac a=y in oLimit_induct)
   apply simp
  apply clarify
  apply (simp add: ordinal_plus_mono)
 apply clarsimp
 apply (rule oLimit_leI, clarify)
 apply (rule_tac n=n in le_oLimitI)
 apply simp
done

lemma ordinal_times_monoR: "y \<le> y' \<Longrightarrow> x * y \<le> x * (y'::ordinal)"
by (rule continuous.monoD[OF continuous_times])

lemma ordinal_times_mono:
"\<lbrakk>x \<le> x'; y \<le> y'\<rbrakk> \<Longrightarrow> x * y \<le> x' * (y'::ordinal)"
by (rule order_trans[OF ordinal_times_monoL ordinal_times_monoR])

lemma ordinal_times_strict_monoR:
"\<lbrakk>y < y'; 0 < x\<rbrakk> \<Longrightarrow> x * y < x * (y'::ordinal)"
by (rule normal.strict_monoD[OF normal_times])

lemma ordinal_le_timesL [simp]: "0 < x \<Longrightarrow> y \<le> x * (y::ordinal)"
by (drule ordinal_times_monoL[OF oSuc_leI], simp)

lemma ordinal_le_timesR [simp]: "0 < y \<Longrightarrow> x \<le> x * (y::ordinal)"
by (drule ordinal_times_monoR[OF oSuc_leI], simp)

lemma ordinal_less_timesR: "\<lbrakk>0 < x; oSuc 0 < y\<rbrakk> \<Longrightarrow> x < x * (y::ordinal)"
by (drule ordinal_times_strict_monoR, assumption, simp)

lemma ordinal_times_left_cancel [simp]:
"0 < w \<Longrightarrow> (w * x = w * y) = (x = (y::ordinal))"
by (rule normal.cancel_eq[OF normal_times])

lemma ordinal_times_left_cancel_le [simp]:
"0 < w \<Longrightarrow> (w * x \<le> w * y) = (x \<le> (y::ordinal))"
by (rule normal.cancel_le[OF normal_times])

lemma ordinal_times_left_cancel_less [simp]:
"0 < w \<Longrightarrow> (w * x < w * y) = (x < (y::ordinal))"
by (rule normal.cancel_less[OF normal_times])

lemma ordinal_times_eq_0:
"((x::ordinal) * y = 0) = (x = 0 \<or> y = 0)"
 apply (rule iffI)
  apply (erule contrapos_pp, clarsimp)
  apply (drule oSuc_leI)
  apply (erule order_less_le_trans)
  apply (drule ordinal_times_monoL, simp)
 apply auto
done

lemma ordinal_times_not_0 [simp]:
"((0::ordinal) < x * y) = (0 < x \<and> 0 < y)"
by (rule not_inject, simp add: ordinal_times_eq_0)


subsection \<open>Exponentiation\<close>

definition
  exp_ordinal :: "[ordinal, ordinal] \<Rightarrow> ordinal" (infixr "**" 75) where
  "(**) = (\<lambda>x. if 0 < x then ordinal_rec 1 (\<lambda>p w. w * x)
                         else (\<lambda>y. if y = 0 then 1 else 0))"

lemma continuous_exp: "0 < x \<Longrightarrow> continuous ((**) x)"
by (simp add: exp_ordinal_def continuous_ordinal_rec)

lemma ordinal_exp_0 [simp]: "x ** 0 = (1::ordinal)"
by (simp add: exp_ordinal_def)

lemma ordinal_exp_oSuc [simp]: "x ** oSuc y = (x ** y) * x"
by (simp add: exp_ordinal_def)

lemma ordinal_exp_oLimit [simp]:
"0 < x \<Longrightarrow> x ** oLimit f = oLimit (\<lambda>n. x ** f n)"
by (rule continuousD[OF continuous_exp])

lemma ordinal_0_exp [simp]: "0 ** x = (if x = 0 then 1 else 0)"
by (simp add: exp_ordinal_def)

lemma ordinal_1_exp [simp]: "oSuc 0 ** x = oSuc 0"
by (rule_tac a=x in oLimit_induct, simp_all)

lemma ordinal_exp_1 [simp]: "x ** oSuc 0 = x"
by simp

lemma ordinal_exp_distrib:
"x ** (y + z) = (x ** y) * (x ** (z::ordinal))"
 apply (case_tac "x = 0", simp_all add: ordinal_plus_not_0)
 apply (rule_tac a=z in oLimit_induct, simp_all add: ordinal_times_assoc)
done

lemma ordinal_exp_not_0 [simp]: "(0 < x ** y) = (0 < x \<or> y = 0)"
 apply auto
  apply (erule contrapos_pp, simp)
 apply (rule_tac a=y in oLimit_induct, simp_all)
 apply (rule less_oLimitI, erule spec)
done

lemma ordinal_exp_eq_0 [simp]: "(x ** y = 0) = (x = 0 \<and> 0 < y)"
by (rule not_inject, simp)

lemma ordinal_exp_assoc:
"(x ** y) ** z = x ** (y * z)"
 apply (case_tac "x = 0", simp_all)
 apply (rule_tac a=z in oLimit_induct, simp_all add: ordinal_exp_distrib)
done

lemma ordinal_exp_monoL [rule_format]:
"\<forall>x x'. x \<le> x' \<longrightarrow> x ** y \<le> x' ** (y::ordinal)"
 apply (rule_tac a=y in oLimit_induct)
   apply simp
  apply (simp add: ordinal_times_mono)
 apply clarsimp
 apply (case_tac "x = 0", simp)
 apply (case_tac "x' = 0", simp_all)
 apply (rule oLimit_leI, clarify)
 apply (rule_tac n=n in le_oLimitI)
 apply simp
done

lemma normal_exp: "oSuc 0 < x \<Longrightarrow> normal ((**) x)"
 apply (frule_tac order_less_trans[OF less_oSuc])
 apply (rule normalI, simp, rename_tac y)
 apply (subgoal_tac "x ** y * 1 < x ** y * x", simp)
 apply (subst ordinal_times_left_cancel_less)
  apply simp
 apply simp
done

lemma ordinal_exp_monoR:
"\<lbrakk>0 < x; y \<le> y'\<rbrakk> \<Longrightarrow> x ** y \<le> x ** (y'::ordinal)"
by (rule continuous.monoD[OF continuous_exp])

lemma ordinal_exp_mono:
"\<lbrakk>0 < x'; x \<le> x'; y \<le> y'\<rbrakk> \<Longrightarrow> x ** y \<le> x' ** (y'::ordinal)"
by (rule order_trans[OF ordinal_exp_monoL ordinal_exp_monoR])

lemma ordinal_exp_strict_monoR:
"\<lbrakk>oSuc 0 < x; y < y'\<rbrakk> \<Longrightarrow> x ** y < x ** (y'::ordinal)"
by (rule normal.strict_monoD[OF normal_exp])

lemma ordinal_le_expR [simp]: "0 < y \<Longrightarrow> x \<le> x ** (y::ordinal)"
 apply (subgoal_tac "x ** oSuc 0 \<le> x ** y")
  apply (simp del: ordinal_exp_oSuc)
 apply (case_tac "x = 0", simp)
 apply (rule ordinal_exp_monoR, simp_all add: oSuc_leI)
done

lemma ordinal_exp_left_cancel [simp]:
"oSuc 0 < w \<Longrightarrow> (w ** x = w ** y) = (x = y)"
by (rule normal.cancel_eq[OF normal_exp])

lemma ordinal_exp_left_cancel_le [simp]:
"oSuc 0 < w \<Longrightarrow> (w ** x \<le> w ** y) = (x \<le> y)"
by (rule normal.cancel_le[OF normal_exp])

lemma ordinal_exp_left_cancel_less [simp]:
"oSuc 0 < w \<Longrightarrow> (w ** x < w ** y) = (x < y)"
by (rule normal.cancel_less[OF normal_exp])

end
