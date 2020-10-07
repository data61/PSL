(*
  File: Arith_Thms.thy
  Author: Bohua Zhan

  Setup for proof steps related to arithmetic, mostly on natural numbers.
*)

section \<open>Setup for arithmetic\<close>

theory Arith_Thms
  imports Order_Thms HOL.Binomial
begin

(* Reducing inequality on natural numbers. *)
theorem reduce_le_plus_consts: "(x::nat) + n1 \<le> y + n2 \<Longrightarrow> x \<le> y + (n2-n1)" by simp
theorem reduce_le_plus_consts': "n1 \<ge> n2 \<Longrightarrow> (x::nat) + n1 \<le> y + n2 \<Longrightarrow> x + (n1-n2) \<le> y" by simp
theorem reduce_less_plus_consts: "(x::nat) + n1 < y + n2 \<Longrightarrow> x < y + (n2-n1)" by simp
theorem reduce_less_plus_consts': "n1 \<ge> n2 \<Longrightarrow> (x::nat) + n1 < y + n2 \<Longrightarrow> x + (n1-n2) < y" by simp

(* To normal form. *)
theorem norm_less_lminus: "(x::nat) - n < y \<Longrightarrow> x \<le> y + (n-1)" by simp
theorem norm_less_lplus:  "(x::nat) + n < y \<Longrightarrow> x + (n+1) \<le> y" by simp
theorem norm_less_rminus: "(x::nat) < y - n \<Longrightarrow> x + (n+1) \<le> y" by simp
theorem norm_less_rplus:  "(x::nat) < y + n \<Longrightarrow> x \<le> y + (n-1)" by simp
theorem norm_less:        "(x::nat) < y     \<Longrightarrow> x + 1 \<le> y"     by simp
theorem norm_le_lminus: "(x::nat) - n \<le> y \<Longrightarrow> x \<le> y + n"  by simp
theorem norm_le_rminus: "(x::nat) \<le> y - n \<Longrightarrow> x \<le> y + 0"  by simp
theorem norm_le: "(x::nat) \<le> y \<Longrightarrow> x \<le> y + 0" by simp
theorem norm_le_lplus0: "(x::nat) + 0 \<le> y \<Longrightarrow> x \<le> y + 0" by simp

(* Transitive resolve. *)
theorem trans_resolve1: "n1 > 0 \<Longrightarrow> (x::nat) + n1 \<le> y \<Longrightarrow> (y::nat) + n2 \<le> x \<Longrightarrow> False" by simp
theorem trans_resolve2: "n1 > n2 \<Longrightarrow> (x::nat) + n1 \<le> y \<Longrightarrow> (y::nat) \<le> x + n2 \<Longrightarrow> False" by simp

(* Transitive. *)
theorem trans1: "(x::nat) + n1 \<le> y \<Longrightarrow> y + n2 \<le> z \<Longrightarrow> x + (n1+n2) \<le> z" by simp
theorem trans2: "(x::nat) \<le> y + n1 \<Longrightarrow> y \<le> z + n2 \<Longrightarrow> x \<le> z + (n1+n2)" by simp
theorem trans3: "(x::nat) + n1 \<le> y \<Longrightarrow> y \<le> z + n2 \<Longrightarrow> x \<le> z + (n2-n1)" by simp
theorem trans4: "n1 > n2 \<Longrightarrow> (x::nat) + n1 \<le> y \<Longrightarrow> y \<le> z + n2 \<Longrightarrow> x + (n1-n2) \<le> z" by simp
theorem trans5: "(x::nat) \<le> y + n1 \<Longrightarrow> y + n2 \<le> z \<Longrightarrow> x \<le> z + (n1-n2)" by simp
theorem trans6: "n2 > n1 \<Longrightarrow> (x::nat) \<le> y + n1 \<Longrightarrow> y + n2 \<le> z \<Longrightarrow> x + (n2-n1) \<le> z" by simp

(* Resolve. *)
theorem single_resolve: "n > 0 \<Longrightarrow> (x::nat) + n \<le> x \<Longrightarrow> False" by simp
theorem single_resolve_const: "n > 0 \<Longrightarrow> (x::nat) + n \<le> 0 \<Longrightarrow> False" by simp

(* Comparison with constants. *)
theorem cv_const1: "(x::nat) + n \<le> y \<Longrightarrow> 0 + (x+n) \<le> y" by simp  (* x is const *)
theorem cv_const2: "(x::nat) + n \<le> y \<Longrightarrow> x \<le> 0 + (y-n)" by simp  (* y is const *)
theorem cv_const3: "y < n \<Longrightarrow> (x::nat) + n \<le> y \<Longrightarrow> x + (n-y) \<le> 0" by simp  (* y is const (contradiction with 0 \<le> x) *)
theorem cv_const4: "(x::nat) \<le> y + n \<Longrightarrow> 0 + (x-n) \<le> y" by simp  (* x is const *)
theorem cv_const5: "(x::nat) \<le> y + n \<Longrightarrow> 0 \<le> y + (n-x)" by simp  (* x is const (trivial) *)
theorem cv_const6: "(x::nat) \<le> y + n \<Longrightarrow> x \<le> 0 + (y+n)" by simp  (* y is const *)

(* Misc *)
theorem nat_eq_to_ineqs: "(x::nat) = y + n \<Longrightarrow> x \<le> y + n \<and> x \<ge> y + n" by simp
theorem nat_ineq_impl_not_eq: "(x::nat) + n \<le> y \<Longrightarrow> n > 0 \<Longrightarrow> x \<noteq> y" by simp
theorem eq_to_ineqs: "(x::nat) \<equiv> y \<Longrightarrow> x \<le> y \<and> y \<le> x" by simp
theorem ineq_to_eqs1: "(x::nat) \<le> y + 0 \<Longrightarrow> y \<le> x + 0 \<Longrightarrow> x = y" by simp

ML_file \<open>arith.ML\<close>
ML_file \<open>order.ML\<close>
ML_file \<open>order_test.ML\<close>

setup \<open>register_wellform_data ("(a::nat) - b", ["a \<ge> b"])\<close>
setup \<open>add_prfstep_check_req ("(a::nat) - b", "(a::nat) \<ge> b")\<close>

(* Normalize any expression to "a - b" form. *)
lemma nat_sub_norm:
  "(a::nat) = a - 0 \<and> a \<ge> 0" by simp

(* Adding and subtracting two normalized expressions. *)
lemma nat_sub1:
  "(a::nat) \<ge> b \<Longrightarrow> c \<ge> d \<Longrightarrow> (a - b) + (c - d) = (a + c) - (b + d) \<and> a + c \<ge> b + d" by simp

lemma nat_sub2:
  "(a::nat) \<ge> b \<Longrightarrow> c \<ge> d \<Longrightarrow> a - b \<ge> c - d \<Longrightarrow> (a - b) - (c - d) = (a + d) - (b + c) \<and> a + d \<ge> b + c" by simp

lemma nat_sub3:
  "(a::nat) \<ge> b \<Longrightarrow> c \<ge> d \<Longrightarrow> (a - b) * (c - d) = (a * c + b * d) - (a * d + b * c) \<and> a * c + b * d \<ge> a * d + b * c"
  by (smt diff_mult_distrib mult.commute mult_le_mono1 nat_sub2)

(* Cancel identical terms on two sides, yielding a normalized expression. *)
lemma nat_sub_combine:
  "(a::nat) + b \<ge> c + b \<Longrightarrow> (a + b) - (c + b) = a - c \<and> a \<ge> c" by simp

lemma nat_sub_combine2:
  "n \<ge> m \<Longrightarrow> (a::nat) + b * n \<ge> c + b * m \<Longrightarrow> (a + b * n) - (c + b * m) = (a + b * (n - m)) - c \<and> a + b * (n - m) \<ge> c \<and> n \<ge> m"
  by (simp add: add.commute right_diff_distrib')

lemma nat_sub_combine3:
  "n \<le> m \<Longrightarrow> (a::nat) + b * n \<ge> c + b * m \<Longrightarrow> (a + b * n) - (c + b * m) = a - (c + b * (m - n)) \<and> a \<ge> c + b * (m - n) \<and> m \<ge> n"
  by (smt add.commute mult.commute nat_diff_add_eq2 nat_le_add_iff1)

ML_file \<open>nat_sub.ML\<close>
ML_file \<open>nat_sub_test.ML\<close>

(* Ordering on Nats. *)
lemma le_neq_implies_less' [forward]: "(m::nat) \<noteq> n \<Longrightarrow> m \<le> n \<Longrightarrow> m < n" by simp
lemma le_zero_to_equal_zero [forward]: "(n::nat) \<le> 0 \<Longrightarrow> n = 0" by simp
lemma less_one_to_equal_zero [forward]: "(n::nat) < 1 \<Longrightarrow> n = 0" by simp
setup \<open>add_backward_prfstep_cond @{thm Nat.mult_le_mono1} [with_cond "?k \<noteq> 1"]\<close>
setup \<open>add_resolve_prfstep @{thm Nat.not_add_less1}\<close>
lemma not_minus_less [resolve]: "\<not>(i::nat) < (i - j)" by simp
lemma nat_le_prod_with_same [backward]: "m \<noteq> 0 \<Longrightarrow> (n::nat) \<le> m * n" by simp
lemma nat_le_prod_with_le [backward1]: "k \<noteq> 0 \<Longrightarrow> (n::nat) \<le> m \<Longrightarrow> (n::nat) \<le> k * m"
  using le_trans nat_le_prod_with_same by blast
lemma nat_plus_le_to_less [backward1]: "b \<noteq> 0 \<Longrightarrow> (a::nat) + b \<le> c \<Longrightarrow> a < c" by simp
lemma nat_plus_le_to_less2 [backward1]: "a \<noteq> 0 \<Longrightarrow> (a::nat) + b \<le> c \<Longrightarrow> b < c" by simp
setup \<open>add_forward_prfstep @{thm add_right_imp_eq}\<close>
setup \<open>add_forward_prfstep @{thm add_left_imp_eq}\<close>

setup \<open>add_rewrite_rule_cond @{thm Nat.le_diff_conv2} [with_term "?i + ?k"]\<close>
lemma nat_less_diff_conv: "(i::nat) < j - k \<Longrightarrow> i + k < j" by simp
setup \<open>add_forward_prfstep_cond @{thm nat_less_diff_conv} [with_cond "?k \<noteq> ?NUMC", with_term "?i + ?k"]\<close>
lemma Nat_le_diff_conv2_same [forward]: "i \<ge> j \<Longrightarrow> (i::nat) \<le> i - j \<Longrightarrow> j = 0" by simp
lemma nat_gt_zero [forward]: "b - a > 0 \<Longrightarrow> b > (a::nat)" by simp
lemma n_minus_1_less_n: "(n::nat) \<ge> 1 \<Longrightarrow> n - 1 < n" by simp
setup \<open>add_forward_prfstep_cond @{thm n_minus_1_less_n} [with_term "?n - 1"]\<close>
  
(* Monotonicity of ordering *)
setup \<open>add_backward_prfstep @{thm Nat.diff_le_mono}\<close>
setup \<open>add_backward2_prfstep @{thm Nat.diff_less_mono}\<close>
setup \<open>add_backward_prfstep @{thm Nat.mult_le_mono2}\<close>
setup \<open>add_resolve_prfstep @{thm Nat.le_add1}\<close>
setup \<open>add_resolve_prfstep @{thm Nat.le_add2}\<close>
setup \<open>add_backward_prfstep @{thm add_left_mono}\<close>
setup \<open>add_backward_prfstep @{thm add_right_mono}\<close>
lemma add_mono_neutr [backward]: "(0::'a::linordered_ring) \<le> b \<Longrightarrow> a \<le> a + b" by simp
lemma add_mono_neutl [backward]: "(0::'a::linordered_ring) \<le> b \<Longrightarrow> a \<le> b + a" by simp
setup \<open>add_forward_prfstep @{thm add_less_imp_less_left}\<close>
lemma sum_le_zero1 [forward]: "(a::'a::linordered_ring) + b < 0 \<Longrightarrow> a \<ge> 0 \<Longrightarrow> b < 0" by (meson add_less_same_cancel1 less_le_trans)
lemma less_sum1 [backward]: "b > 0 \<Longrightarrow> a < a + (b::nat)" by auto
setup \<open>add_backward_prfstep @{thm Nat.trans_less_add2}\<close>
setup \<open>add_backward_prfstep @{thm Nat.add_less_mono1}\<close>
setup \<open>add_backward1_prfstep @{thm Nat.add_less_mono}\<close>
setup \<open>add_backward1_prfstep @{thm Nat.add_le_mono}\<close>
setup \<open>add_backward1_prfstep @{thm add_increasing2}\<close>
setup \<open>add_backward1_prfstep @{thm add_mono}\<close>
setup \<open>add_backward_prfstep @{thm add_strict_left_mono}\<close>
setup \<open>add_backward1_prfstep @{thm Nat.mult_le_mono}\<close>

(* Addition. *)
theorem nat_add_eq_self_zero [forward]: "(m::nat) = m + n \<Longrightarrow> n = 0" by simp
theorem nat_add_eq_self_zero' [forward]: "(m::nat) = n + m \<Longrightarrow> n = 0" by simp
theorem nat_mult_2: "(a::nat) + a = 2 * a" by simp
setup \<open>add_rewrite_rule_cond @{thm nat_mult_2} [with_cond "?a \<noteq> 0"]\<close>
theorem plus_one_non_zero [resolve]: "\<not>(n::nat) + 1 = 0" by simp

(* Diff. *)
lemma nat_same_minus_ge [forward]: "(c::nat) - a \<ge> c - b \<Longrightarrow> a \<le> c \<Longrightarrow> a \<le> b" by arith
lemma diff_eq_zero [forward]: "(k::nat) \<le> j \<Longrightarrow> j - k = 0 \<Longrightarrow> j = k" by simp
lemma diff_eq_zero' [forward]: "(k::nat) \<le> j \<Longrightarrow> j - k + i = j \<Longrightarrow> k = i" by simp

(* Divides. *)
theorem dvd_defD1 [resolve]: "(a::nat) dvd b \<Longrightarrow> \<exists>k. b = a * k" using dvdE by blast
theorem dvd_defD2 [resolve]: "(a::nat) dvd b \<Longrightarrow> \<exists>k. b = k * a" by (metis dvd_mult_div_cancel mult.commute)
setup \<open>add_forward_prfstep @{thm Nat.dvd_imp_le}\<close>
theorem dvd_ineq2 [forward]: "(k::nat) dvd n \<Longrightarrow> n > 0 \<Longrightarrow> k \<ge> 1" by (simp add: Suc_leI dvd_pos_nat)

setup \<open>add_forward_prfstep_cond @{thm dvd_trans} (with_conds ["?a \<noteq> ?b", "?b \<noteq> ?c", "?a \<noteq> ?c"])\<close>
setup \<open>add_forward_prfstep_cond @{thm Nat.dvd_antisym} [with_cond "?m \<noteq> ?n"]\<close>
theorem dvd_cancel [backward1]: "c > 0 \<Longrightarrow> (a::nat) * c dvd b * c \<Longrightarrow> a dvd b" by simp
setup \<open>add_forward_prfstep (equiv_forward_th @{thm dvd_add_right_iff})\<close>

(* Divisibility: existence. *)
setup \<open>add_resolve_prfstep @{thm dvd_refl}\<close>
theorem exists_n_dvd_n [backward]: "P (n::nat) \<Longrightarrow> \<exists>k. k dvd n \<and> P k" using dvd_refl by blast
setup \<open>add_resolve_prfstep @{thm one_dvd}\<close>

theorem any_n_dvd_0 [forward]: "\<not> (\<exists> k. k dvd (0::nat) \<and> P k) \<Longrightarrow> \<not> (\<exists> k. P k)" by simp

theorem n_dvd_one: "(n::nat) dvd 1 \<Longrightarrow> n = 1" by simp
setup \<open>add_forward_prfstep_cond @{thm n_dvd_one} [with_cond "?n \<noteq> 1"]\<close>

(* Products. *)
setup \<open>add_rewrite_rule @{thm mult_zero_left}\<close>
lemma prod_ineqs1 [forward]: "(m::nat) * k > 0 \<Longrightarrow> m > 0 \<and> k > 0" by simp
lemma prod_ineqs2 [backward]: "(k::nat) > 0 \<Longrightarrow> m \<le> m * k" by simp

theorem prod_cancel: "(a::nat) * b = a * c \<Longrightarrow> a > 0 \<Longrightarrow> b = c" by auto
setup \<open>add_forward_prfstep_cond @{thm prod_cancel} [with_cond "?b \<noteq> ?c"]\<close>

theorem mult_n1n: "(n::nat) = m * n \<Longrightarrow> n > 0 \<Longrightarrow> m = 1" by auto
setup \<open>add_forward_prfstep_cond @{thm mult_n1n} [with_cond "?m \<noteq> 1"]\<close>

theorem prod_is_one [forward]: "(x::nat) * y = 1 \<Longrightarrow> x = 1" by simp

theorem prod_dvd_intro [backward]: "(k::nat) dvd m \<or> k dvd n \<Longrightarrow> k dvd m * n"
  using dvd_mult dvd_mult2 by blast

(* Definition of gcd. *)
setup \<open>add_forward_prfstep_cond @{thm gcd_dvd1} [with_term "gcd ?a ?b"]\<close>
setup \<open>add_forward_prfstep_cond @{thm gcd_dvd2} [with_term "gcd ?a ?b"]\<close>

(* Coprimality. *)
setup \<open>add_rewrite_rule_bidir @{thm coprime_iff_gcd_eq_1}\<close>
lemma coprime_exp [backward]: "coprime d a \<Longrightarrow> coprime (d::nat) (a ^ n)" by simp
setup \<open>add_backward_prfstep @{thm coprime_exp}\<close>
setup \<open>add_rewrite_rule @{thm gcd.commute}\<close>
lemma coprime_dvd_mult [backward1]: "coprime (a::nat) b \<Longrightarrow> a dvd c * b \<Longrightarrow> a dvd c"
  by (metis coprime_dvd_mult_left_iff)
lemma coprime_dvd_mult' [backward1]: "coprime (a::nat) b \<Longrightarrow> a dvd b * c \<Longrightarrow> a dvd c"
  by (metis coprime_dvd_mult_right_iff)

theorem coprime_dvd [forward]:
  "coprime (a::nat) b \<Longrightarrow> p dvd a \<Longrightarrow> p > 1 \<Longrightarrow> \<not> p dvd b"
  using coprime_common_divisor_nat by blast

(* Powers. *)
setup \<open>add_rewrite_rule @{thm power_0}\<close>
theorem power_ge_0 [rewrite]: "m \<noteq> 0 \<Longrightarrow> p ^ m = p * (p ^ (m - 1))" by (simp add: power_eq_if)
setup \<open>add_rewrite_rule_cond @{thm power_one} [with_cond "?n \<noteq> 0"]\<close>
setup \<open>add_rewrite_rule_cond @{thm power_one_right} [with_cond "?a \<noteq> 1"]\<close>
setup \<open>add_gen_prfstep ("power_case_intro",
  [WithTerm @{term_pat "?p ^ (?FREE::nat)"}, CreateCase @{term_pat "(?FREE::nat) = 0"}])\<close>

lemma one_is_power_of_any [resolve]: "\<exists>i. (1::nat) = a ^ i" by (metis power.simps(1))

setup \<open>add_rewrite_rule @{thm power_Suc}\<close>

theorem power_dvd [forward]: "(p::nat)^n dvd a \<Longrightarrow> n \<noteq> 0 \<Longrightarrow> p dvd a" using dvd_power dvd_trans by blast

theorem power_eq_one: "(b::nat) ^ n = 1 \<Longrightarrow> b = 1 \<or> n = 0"
  by (metis One_nat_def Suc_lessI nat_zero_less_power_iff power_0 power_inject_exp)
setup \<open>add_forward_prfstep_cond @{thm power_eq_one} (with_conds ["?b \<noteq> 1", "?n \<noteq> 0"])\<close>

(* Factorial. *)
theorem fact_ge_1_nat: "fact (n::nat) \<ge> (1::nat)" by simp
setup \<open>add_forward_prfstep_cond @{thm fact_ge_1_nat} [with_term "fact ?n"]\<close>
setup \<open>add_backward1_prfstep @{thm dvd_fact}\<close>

(* Successor function. *)
setup \<open>add_rewrite_rule @{thm Nat.Suc_eq_plus1}\<close>
setup \<open>add_backward_prfstep @{thm Nat.gr0_implies_Suc}\<close>

(* Cases *)
setup \<open>fold add_rewrite_rule @{thms Nat.nat.case}\<close>

(* Induction. *)
lemma nat_cases: "P 0 \<Longrightarrow> (\<And>n. P (Suc n)) \<Longrightarrow> P n" using nat_induct by auto

(* div *)
declare times_div_less_eq_dividend [resolve]

setup \<open>
  add_var_induct_rule @{thm nat_induct} #>
  add_strong_induct_rule @{thm nat_less_induct} #>
  add_cases_rule @{thm nat_cases}
\<close>

end
