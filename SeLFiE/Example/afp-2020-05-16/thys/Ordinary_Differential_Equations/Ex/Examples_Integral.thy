theory
Examples_Integral
imports
  "HOL-ODE-Numerics.ODE_Numerics"
begin

text \<open>Examples taken from Mahboubi, Sibut-Pinote: Formally Verified Approximations of Definite Integrals.
  \<^url>\<open>https://link.springer.com/chapter/10.1007/978-3-319-43144-4_17\<close>\<close>

lemma mk_ode_ops_ne_None: "mk_ode_ops e f \<noteq> None"
  if "max_Var_floatariths e \<le> length e"
    "open_form f"
    "max_Var_form f \<le> length e"
  using that
  including ode_ops.lifting
  by transfer auto

subsection \<open>Example 1\<close>

lemma ex1_3: "\<bar>integral {0 .. 1} (\<lambda>x. 1 / (1 + x*x::real)) - pi/4\<bar> \<le> 1 / 10^3"
  by (rule abs_minus_leI) (tactic \<open>integral_bnds_tac 1 30 5 6 13 "-" [] @{context} 1\<close>)

lemma ex1_6: "\<bar>integral {0 .. 1} (\<lambda>x. 1 / (1 + x*x::real)) - pi/4\<bar> \<le> 1 / 10^6"
  by (rule abs_minus_leI) (tactic \<open>integral_bnds_tac 1 30 5 6 25 "" [] @{context} 1\<close>)

lemma ex1_9: "\<bar>integral {0 .. 1} (\<lambda>x. 1 / (1 + x*x::real)) - pi/4\<bar> \<le> 1 / 10^9"
  by (rule abs_minus_leI) (tactic \<open>integral_bnds_tac 1 50 5 6 40 "" [] @{context} 1\<close>)


subsection \<open>Example 2\<close>

lemma add_nonneg_pos_ne_zero: "a \<ge> 0 \<Longrightarrow> b > 0 \<Longrightarrow> a + b \<noteq> 0" for a b::real by arith
lemmas pow_gt_zero = add_nonneg_pos add_nonneg_pos_ne_zero

lemma ex2_3: "\<bar>integral {0 .. 1} (\<lambda>x::real. arctan (sqrt (x\<^sup>2 + 2)) / (sqrt (x\<^sup>2 + 2) * (x\<^sup>2 + 1))) - 5*pi\<^sup>2/96\<bar> \<le> 1 / 10^3"
  by (rule abs_minus_leI) (tactic \<open>integral_bnds_tac 1 30 10 6 12 "" @{thms pow_gt_zero} @{context} 1\<close>)

lemma ex2_6: "\<bar>integral {0 .. 1} (\<lambda>x::real. arctan (sqrt (x\<^sup>2 + 2)) / (sqrt (x\<^sup>2 + 2) * (x\<^sup>2 + 1))) - 5*pi\<^sup>2/96\<bar> \<le> 1 / 10^6"
  by (rule abs_minus_leI) (tactic \<open>integral_bnds_tac 1 40 10 6 26 "" @{thms pow_gt_zero} @{context} 1\<close>)


subsection \<open>Example 3\<close>

lemma pi_bounds_nonneg[simp]: "0 \<le> real_of_float (ub_pi p)"
  using pi_boundaries[of p]
  by (auto intro: pi_ge_zero[le])

lemma ex3_3: "\<bar>integral {0 .. pi} (\<lambda>x::real. (x * sin x) / (1 + (cos x)\<^sup>2)) - pi\<^sup>2/4\<bar> \<le> 1 / 10^3"
  by (rule abs_minus_leI) (tactic \<open>integral_bnds_tac 1 30 10 6 15 "" [] @{context} 1\<close>)

lemma ex3_6: "\<bar>integral {0 .. pi} (\<lambda>x::real. (x * sin x) / (1 + (cos x)\<^sup>2)) - pi\<^sup>2/4\<bar> \<le> 1 / 10^6"
  by (rule abs_minus_leI) (tactic \<open>integral_bnds_tac 1 40 10 6 30 "" [] @{context} 1\<close>)


subsection \<open>Example 4\<close>

text \<open>Absolute Value...\<close>


subsection \<open>Example 5\<close>

lemma
  "\<bar>integral {-1 .. 1} (\<lambda>x::real. (2048*x^12 - 6144*x^10 + 6912*x^8 - 3584*x^6 + 840*x^4 - 72*x\<^sup>2 +1) *
      exp (-((x - 3/4)\<^sup>2)) * sqrt(1 - x\<^sup>2)) -
    real_divl 80 (-32555895745) (10^16)\<bar> \<le> 1 / 10^1"
  oops

text \<open>@{term "sqrt(1 - x\<^sup>2)"} not differentiable @{term "at 0"}\<close>

subsection \<open>Example 6\<close>

lemma
  "\<bar>integral {0 .. 8} (\<lambda>x::real. sin (x + exp x)) - 0.3474\<bar> \<le> 1 / 10^1"
  by (rule abs_minus_leI) (tactic \<open>integral_bnds_tac 1 40 3 6 15 "" [] @{context} 1\<close>)\<comment> \<open>slow: 700s\<close>

lemma
  "\<bar>integral {0 .. 8} (\<lambda>x::real. sin (x + exp x)) - 0.3474\<bar> \<le> 1 / 10^2"
  oops (*
  by (rule abs_minus_leI) (tactic \<open>integral_bnds_tac 1 40 3 6 20 "" @{context} 1\<close>) *)

end
