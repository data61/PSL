(*  Title:      Util_Nat.thy
    Date:       Oct 2006
    Author:     David Trachtenherz
*)

section \<open>Results for natural arithmetics\<close>

theory Util_Nat
imports Main
begin

subsection \<open>Some convenience arithmetic lemmata\<close>

lemma add_1_Suc_conv: "m + 1 = Suc m" by simp
lemma sub_Suc0_sub_Suc_conv: "b - a - Suc 0 = b - Suc a" by simp

lemma Suc_diff_Suc: "m < n \<Longrightarrow> Suc (n - Suc m) = n - m"
apply (rule subst[OF sub_Suc0_sub_Suc_conv])
apply (rule Suc_pred)
apply (simp only: zero_less_diff)
done

lemma nat_grSuc0_conv: "(Suc 0 < n) = (n \<noteq> 0 \<and> n \<noteq> Suc 0)"
by fastforce

lemma nat_geSucSuc0_conv: "(Suc (Suc 0) \<le> n) = (n \<noteq> 0 \<and> n \<noteq> Suc 0)"
by fastforce

lemma nat_lessSucSuc0_conv: "(n < Suc (Suc 0)) = (n = 0 \<or> n = Suc 0)"
by fastforce

lemma nat_leSuc0_conv: "(n \<le> Suc 0) = (n = 0 \<or> n = Suc 0)"
by fastforce

lemma mult_pred: "(m - Suc 0) * n = m * n - n"
by (simp add: diff_mult_distrib)

lemma mult_pred_right: "m * (n - Suc 0) = m * n - m"
by (simp add: diff_mult_distrib2)

lemma gr_implies_gr0: "m < (n::nat) \<Longrightarrow> 0 < n" by simp

corollary mult_cancel1_gr0: "
  (0::nat) < k \<Longrightarrow> (k * m = k * n) = (m = n)" by simp
corollary mult_cancel2_gr0: "
  (0::nat) < k \<Longrightarrow> (m * k = n * k) = (m = n)" by simp

corollary mult_le_cancel1_gr0: "
  (0::nat) < k \<Longrightarrow> (k * m \<le> k * n) = (m \<le> n)" by simp
corollary mult_le_cancel2_gr0: "
  (0::nat) < k \<Longrightarrow> (m * k \<le> n * k) = (m \<le> n)" by simp

lemma gr0_imp_self_le_mult1: "0 < (k::nat) \<Longrightarrow> m \<le> m * k"
by (drule Suc_leI, drule mult_le_mono[OF order_refl], simp)

lemma gr0_imp_self_le_mult2: "0 < (k::nat) \<Longrightarrow> m \<le> k * m"
by (subst mult.commute, rule gr0_imp_self_le_mult1)

lemma less_imp_Suc_mult_le: "m < n \<Longrightarrow> Suc m * k \<le> n * k"
by (rule mult_le_mono1, simp)

lemma less_imp_Suc_mult_pred_less: "\<lbrakk> m < n; 0 < k \<rbrakk> \<Longrightarrow> Suc m * k - Suc 0 < n * k"
apply (rule Suc_le_lessD)
apply (simp only: Suc_pred[OF nat_0_less_mult_iff[THEN iffD2, OF conjI, OF zero_less_Suc]])
apply (rule less_imp_Suc_mult_le, assumption)
done

lemma ord_zero_less_diff: "(0 < (b::'a::ordered_ab_group_add) - a) = (a < b)"
by (simp add: less_diff_eq)

lemma ord_zero_le_diff: "(0 \<le> (b::'a::ordered_ab_group_add) - a) = (a \<le> b)"
by (simp add: le_diff_eq)

text \<open>\<open>diff_diff_right\<close> in rule format\<close>
lemmas diff_diff_right = Nat.diff_diff_right[rule_format]


lemma less_add1: "(0::nat) < j \<Longrightarrow> i < i + j" by simp
lemma less_add2: "(0::nat) < j \<Longrightarrow> i < j + i" by simp

lemma add_lessD2: "i + j < (k::nat) \<Longrightarrow> j < k" by simp

lemma add_le_mono2: "i \<le> (j::nat) \<Longrightarrow> k + i \<le> k + j" by simp

lemma add_less_mono2: "i < (j::nat) \<Longrightarrow> k + i < k + j" by simp


lemma diff_less_self: "\<lbrakk> (0::nat) < i;  0 < j \<rbrakk> \<Longrightarrow> i - j < i" by simp

lemma
  ge_less_neq_conv: "((a::'a::linorder) \<le> n) = (\<forall>x. x < a \<longrightarrow> n \<noteq> x)" and
  le_greater_neq_conv: "(n \<le> (a::'a::linorder)) = (\<forall>x. a < x \<longrightarrow> n \<noteq> x)"
by (subst linorder_not_less[symmetric], blast)+
lemma
  greater_le_neq_conv: "((a::'a::linorder) < n) = (\<forall>x. x \<le> a \<longrightarrow> n \<noteq> x)" and
  less_ge_neq_conv: "(n < (a::'a::linorder)) = (\<forall>x. a \<le> x \<longrightarrow> n \<noteq> x)"
by (subst linorder_not_le[symmetric], blast)+



text \<open>Lemmas for @term{abs} function\<close>

lemma leq_pos_imp_abs_leq: "\<lbrakk> 0 \<le> (a::'a::ordered_ab_group_add_abs); a \<le> b \<rbrakk> \<Longrightarrow> \<bar>a\<bar> \<le> \<bar>b\<bar>"
by simp
lemma leq_neg_imp_abs_geq: "\<lbrakk> (a::'a::ordered_ab_group_add_abs) \<le> 0; b \<le> a \<rbrakk> \<Longrightarrow> \<bar>a\<bar> \<le> \<bar>b\<bar>"
by simp
lemma abs_range: "\<lbrakk> 0 \<le> (a::'a::{ordered_ab_group_add_abs,abs_if}); -a \<le> x; x \<le> a \<rbrakk> \<Longrightarrow> \<bar>x\<bar> \<le> a"
apply (clarsimp simp: abs_if)
apply (rule neg_le_iff_le[THEN iffD1], simp)
done



text \<open>Lemmas for @term{sgn} function\<close>

lemma sgn_abs:"(x::'a::linordered_idom) \<noteq> 0 \<Longrightarrow> \<bar>sgn x\<bar> = 1"
by (case_tac "x < 0", simp+)
lemma sgn_mult_abs:"\<bar>x\<bar> * \<bar>sgn (a::'a::linordered_idom)\<bar> = \<bar>x * sgn a\<bar>"
by (fastforce simp add: sgn_if abs_if)
lemma abs_imp_sgn_abs: "\<bar>a\<bar> = \<bar>b\<bar> \<Longrightarrow> \<bar>sgn (a::'a::linordered_idom)\<bar> = \<bar>sgn b\<bar>"
by (fastforce simp add: abs_if)
lemma sgn_mono: "a \<le> b \<Longrightarrow> sgn (a::'a::{linordered_idom,linordered_semidom}) \<le> sgn b"
by (auto simp add: sgn_if)


subsection \<open>Additional facts about inequalities\<close>

lemma add_diff_le: "k \<le> n \<Longrightarrow> m + k - n \<le> (m::nat)"
by (case_tac "m + k < n", simp_all)

lemma less_add_diff: "k < (n::nat) \<Longrightarrow> m < n + m - k"

by (rule add_less_imp_less_right[of _ k], simp)

lemma add_diff_less: "\<lbrakk> k < n; 0 < m \<rbrakk> \<Longrightarrow> m + k - n < (m::nat)"
by (case_tac "m + k < n", simp_all)


lemma add_le_imp_le_diff1: "i + k \<le> j \<Longrightarrow> i \<le> j - (k::nat)"
by (case_tac "k \<le> j", simp_all)

lemma add_le_imp_le_diff2: "k + i \<le> j \<Longrightarrow> i \<le> j - (k::nat)" by simp

lemma diff_less_imp_less_add: "j - (k::nat) < i \<Longrightarrow> j < i + k" by simp

lemma diff_less_conv: "0 < i \<Longrightarrow> (j - (k::nat) < i) = (j < i + k)"
by (safe, simp_all)

lemma le_diff_swap: "\<lbrakk> i \<le> (k::nat); j \<le> k \<rbrakk> \<Longrightarrow> (k - j \<le> i) = (k - i \<le> j)"
by (safe, simp_all)

lemma diff_less_imp_swap: "\<lbrakk> 0 < (i::nat); k - i < j \<rbrakk> \<Longrightarrow> (k - j < i)" by simp
lemma diff_less_swap: "\<lbrakk> 0 < (i::nat); 0 < j \<rbrakk> \<Longrightarrow> (k - j < i) = (k - i < j)"
by (blast intro: diff_less_imp_swap)

lemma less_diff_imp_less: "(i::nat) < j - m \<Longrightarrow> i < j" by simp
lemma le_diff_imp_le: "(i::nat) \<le> j - m \<Longrightarrow> i \<le> j" by simp

lemma less_diff_le_imp_less: "\<lbrakk> (i::nat) < j - m; n \<le> m \<rbrakk> \<Longrightarrow> i < j - n" by simp
lemma le_diff_le_imp_le: "\<lbrakk> (i::nat) \<le> j - m; n \<le> m \<rbrakk> \<Longrightarrow> i \<le> j - n" by simp

lemma le_imp_diff_le: "(j::nat) \<le> k \<Longrightarrow> j - n \<le> k" by simp


subsection \<open>Inequalities for Suc and pred\<close>

corollary less_eq_le_pred: "0 < (n::nat) \<Longrightarrow> (m < n) = (m \<le> n - Suc 0)"
by (safe, simp_all)

corollary less_imp_le_pred: "m < n \<Longrightarrow> m \<le> n - Suc 0" by simp
corollary le_pred_imp_less: "\<lbrakk> 0 < n; m \<le> n - Suc 0 \<rbrakk> \<Longrightarrow> m < n" by simp

corollary pred_less_eq_le: "0 < m \<Longrightarrow> (m - Suc 0 < n) = (m \<le> n)"
by (safe, simp_all)
corollary pred_less_imp_le: "m - Suc 0 < n \<Longrightarrow> m \<le> n" by simp
corollary le_imp_pred_less: "\<lbrakk> 0 < m; m \<le> n \<rbrakk> \<Longrightarrow> m - Suc 0 < n" by simp

lemma diff_add_inverse_Suc: "n < m \<Longrightarrow> n + (m - Suc n) = m - Suc 0" by simp

lemma pred_mono: "\<lbrakk> m < n; 0 < m \<rbrakk> \<Longrightarrow> m - Suc 0 < n - Suc 0" by simp
corollary pred_Suc_mono: "\<lbrakk> m < Suc n; 0 < m \<rbrakk> \<Longrightarrow> m - Suc 0 < n" by simp

lemma Suc_less_pred_conv: "(Suc m < n) = (m < n - Suc 0)" by (safe, simp_all)
lemma Suc_le_pred_conv: "0 < n \<Longrightarrow> (Suc m \<le> n) = (m \<le> n - Suc 0)" by (safe, simp_all)
lemma Suc_le_imp_le_pred: "Suc m \<le> n \<Longrightarrow> m \<le> n - Suc 0" by simp


subsection \<open>Additional facts about cancellation in (in-)equalities\<close>

lemma diff_cancel_imp_eq: "\<lbrakk> 0 < (n::nat);  n + i - j = n \<rbrakk> \<Longrightarrow> i = j" by simp

lemma nat_diff_left_cancel_less: "k - m < k - (n::nat) \<Longrightarrow> n < m" by simp
lemma nat_diff_right_cancel_less: "n - k < (m::nat) - k \<Longrightarrow> n < m" by simp

lemma nat_diff_left_cancel_le1: "\<lbrakk> k - m \<le> k - (n::nat); m < k \<rbrakk> \<Longrightarrow> n \<le> m" by simp
lemma nat_diff_left_cancel_le2: "\<lbrakk> k - m \<le> k - (n::nat); n \<le> k \<rbrakk> \<Longrightarrow> n \<le> m" by simp

lemma nat_diff_right_cancel_le1: "\<lbrakk> m - k \<le> n - (k::nat); k < m \<rbrakk> \<Longrightarrow> m \<le> n" by simp
lemma nat_diff_right_cancel_le2: "\<lbrakk> m - k \<le> n - (k::nat); k \<le> n \<rbrakk> \<Longrightarrow> m \<le> n" by simp

lemma nat_diff_left_cancel_eq1: "\<lbrakk> k - m = k - (n::nat); m < k \<rbrakk> \<Longrightarrow> m = n" by simp
lemma nat_diff_left_cancel_eq2: "\<lbrakk> k - m = k - (n::nat); n < k \<rbrakk> \<Longrightarrow> m = n" by simp

lemma nat_diff_right_cancel_eq1: "\<lbrakk> m - k = n - (k::nat); k < m \<rbrakk> \<Longrightarrow> m = n" by simp
lemma nat_diff_right_cancel_eq2: "\<lbrakk> m - k = n - (k::nat); k < n \<rbrakk> \<Longrightarrow> m = n" by simp

lemma eq_diff_left_iff: "\<lbrakk> (m::nat) \<le> k; n \<le> k\<rbrakk> \<Longrightarrow> (k - m = k - n) = (m = n)"
by (safe, simp_all)

lemma eq_imp_diff_eq: "m = (n::nat) \<Longrightarrow> m - k = n - k" by simp


text \<open>List of definitions and lemmas\<close>

thm
  Nat.add_Suc_right
  add_1_Suc_conv
  sub_Suc0_sub_Suc_conv

thm
  Nat.mult_cancel1
  Nat.mult_cancel2
  mult_cancel1_gr0
  mult_cancel2_gr0

thm
  Nat.add_lessD1
  add_lessD2

thm
  Nat.zero_less_diff
  ord_zero_less_diff
  ord_zero_le_diff

thm
  Nat.le_add_diff
  add_diff_le
  less_add_diff
  add_diff_less

thm
  Nat.le_diff_conv Nat.le_diff_conv2
  Nat.less_diff_conv
  diff_less_imp_less_add
  diff_less_conv

thm
  le_diff_swap
  diff_less_imp_swap
  diff_less_swap

thm
  less_diff_imp_less
  le_diff_imp_le

thm
  less_diff_le_imp_less
  le_diff_le_imp_le

thm
  Nat.less_imp_diff_less
  le_imp_diff_le

thm
  Nat.less_Suc_eq_le
  less_eq_le_pred
  less_imp_le_pred
  le_pred_imp_less

thm
  Nat.Suc_le_eq
  pred_less_eq_le
  pred_less_imp_le
  le_imp_pred_less

thm
  diff_cancel_imp_eq
thm
  diff_add_inverse_Suc
thm
  Nat.nat_add_left_cancel_less
  Nat.nat_add_left_cancel_le
  Nat.nat_add_right_cancel
  Nat.nat_add_left_cancel
  Nat.eq_diff_iff
  Nat.less_diff_iff
  Nat.le_diff_iff
thm
  nat_diff_left_cancel_less
  nat_diff_right_cancel_less
thm
  nat_diff_left_cancel_le1
  nat_diff_left_cancel_le2
  nat_diff_right_cancel_le1
  nat_diff_right_cancel_le2
thm
  nat_diff_left_cancel_eq1
  nat_diff_left_cancel_eq2
  nat_diff_right_cancel_eq1
  nat_diff_right_cancel_eq2

thm
  Nat.eq_diff_iff
  eq_diff_left_iff

thm
  Nat.nat_add_right_cancel Nat.nat_add_left_cancel
  Nat.diff_le_mono
  eq_imp_diff_eq

end
