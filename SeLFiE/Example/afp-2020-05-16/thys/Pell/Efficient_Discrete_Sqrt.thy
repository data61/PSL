(*
  File:    Efficient_Discrete_Sqrt.thy
  Author:  Markus Großer, Manuel Eberl

  A reasonably efficient algorithm to compute the square root of a natural number (rounded down)
  and to test if a natural number is a perfect square.
*)
theory Efficient_Discrete_Sqrt
imports
  Complex_Main
  "HOL-Computational_Algebra.Computational_Algebra"
  "HOL-Library.Discrete"
  "HOL-Library.Tree"
  "HOL-Library.IArray"
begin
section \<open>Efficient Algorithms for the Square Root on \<open>\<nat>\<close>\<close>

(*
  TODO: This could perhaps be moved somewhere else. Thre is also probably some overlap
  with Sqrt_Babylonian
*)

subsection \<open>A Discrete Variant of Heron's Algorithm\<close>

text \<open>
  An algorithm for calculating the discrete square root, taken from 
  Cohen~\cite{cohen2010algebraic}. This algorithm is essentially a discretised variant of
  Heron's method or Newton's method specialised to the square root function.
\<close>

lemma sqrt_eq_floor_sqrt: "Discrete.sqrt n = nat \<lfloor>sqrt n\<rfloor>"
proof -
  have "real ((nat \<lfloor>sqrt n\<rfloor>)\<^sup>2) = (real (nat \<lfloor>sqrt n\<rfloor>))\<^sup>2"
    by simp
  also have "\<dots> \<le> sqrt (real n) ^ 2"
    by (intro power_mono) auto
  also have "\<dots> = real n" by simp
  finally have "(nat \<lfloor>sqrt n\<rfloor>)\<^sup>2 \<le> n"
    by (simp only: of_nat_le_iff)
  moreover have "n < (Suc (nat \<lfloor>sqrt n\<rfloor>))\<^sup>2" proof -
    have "(1 + \<lfloor>sqrt n\<rfloor>)\<^sup>2 > n"
      using floor_correct[of "sqrt n"] real_le_rsqrt[of "1 + \<lfloor>sqrt n\<rfloor>" n]
        of_int_less_iff[of n "(1 + \<lfloor>sqrt n\<rfloor>)\<^sup>2"] not_le
      by fastforce
    then show ?thesis
      using le_nat_floor[of "Suc (nat \<lfloor>sqrt n\<rfloor>)" "sqrt n"]
        of_nat_le_iff[of "(Suc (nat \<lfloor>sqrt n\<rfloor>))\<^sup>2" n] real_le_rsqrt[of _ n] not_le
      by fastforce
  qed
  ultimately show ?thesis using sqrt_unique by fast
qed

fun newton_sqrt_aux :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "newton_sqrt_aux x n =
     (let y = (x + n div x) div 2
      in if y < x then newton_sqrt_aux y n else x)"

declare newton_sqrt_aux.simps [simp del]

lemma newton_sqrt_aux_simps:
  "(x + n div x) div 2 < x \<Longrightarrow> newton_sqrt_aux x n = newton_sqrt_aux ((x + n div x) div 2) n"
  "(x + n div x) div 2 \<ge> x \<Longrightarrow> newton_sqrt_aux x n = x"
  by (subst newton_sqrt_aux.simps; simp add: Let_def)+

lemma heron_step_real: "\<lbrakk>t > 0; n \<ge> 0\<rbrakk> \<Longrightarrow> (t + n/t) / 2 \<ge> sqrt n"
  using arith_geo_mean_sqrt[of t "n/t"] by simp

lemma heron_step_div_eq_floored:
  "(t::nat) > 0 \<Longrightarrow> (t + (n::nat) div t) div 2 = nat \<lfloor>(t + n/t) / 2\<rfloor>"
proof -
  assume "t > 0"
  then have "\<lfloor>(t + n/t) / 2\<rfloor> = \<lfloor>(t*t + n) / (2*t)\<rfloor>"
    by (simp add: mult_divide_mult_cancel_right[of t "t + n/t" 2, symmetric]
        algebra_simps)
  also have "\<dots> = (t*t + n) div (2*t)"
    using floor_divide_of_nat_eq by blast
  also have "\<dots> = (t*t + n) div t div 2"
    by (simp add: Divides.div_mult2_eq mult.commute)
  also have "\<dots> = (t + n div t) div 2"
    by (simp add: \<open>0 < t\<close> power2_eq_square)
  finally show ?thesis by simp
qed

lemma heron_step: "t > 0 \<Longrightarrow> (t + n div t) div 2 \<ge> Discrete.sqrt n"
proof -
  assume "t > 0"
  have "Discrete.sqrt n = nat \<lfloor>sqrt n\<rfloor>" by (rule sqrt_eq_floor_sqrt)
  also have "\<dots> \<le> nat \<lfloor>(t + n/t) / 2\<rfloor>"
    using heron_step_real[of t n] \<open>t > 0\<close> by linarith
  also have "\<dots> = (t + n div t) div 2"
    using heron_step_div_eq_floored[OF \<open>t > 0\<close>] by simp
  finally show ?thesis .
qed

lemma newton_sqrt_aux_correct:
  assumes "x \<ge> Discrete.sqrt n"
  shows   "newton_sqrt_aux x n = Discrete.sqrt n"
  using assms
proof (induction x n rule: newton_sqrt_aux.induct)
  case (1 x n)
  show ?case
  proof (cases "x = Discrete.sqrt n")
    case True
    then have "(x ^ 2) div x \<le> n div x" by (intro div_le_mono) simp_all
    also have "(x ^ 2) div x = x" by (simp add: power2_eq_square)
    finally have "(x + n div x) div 2 \<ge> x" by linarith
    with True show ?thesis by (auto simp: newton_sqrt_aux_simps)
  next
    case False
    with "1.prems" have x_gt_sqrt: "x > Discrete.sqrt n" by auto
    with Discrete.le_sqrt_iff[of x n] have "n < x ^ 2" by simp
    have "x * (n div x) \<le> n" using mult_div_mod_eq[of x n] by linarith
    also have "\<dots> < x ^ 2" using Discrete.le_sqrt_iff[of x n] and x_gt_sqrt by simp
    also have "\<dots> = x * x" by (simp add: power2_eq_square)
    finally have "n div x < x" by (subst (asm) mult_less_cancel1) auto
    then have step_decreasing: "(x + n div x) div 2 < x" by linarith
    with x_gt_sqrt have step_ge_sqrt: "(x + n div x) div 2 \<ge> Discrete.sqrt n"
      by (simp add: heron_step)
    from step_decreasing have "newton_sqrt_aux x n = newton_sqrt_aux ((x + n div x) div 2) n"
      by (simp add: newton_sqrt_aux_simps)
    also have "\<dots> = Discrete.sqrt n"
      by (intro "1.IH" step_decreasing step_ge_sqrt) simp_all
    finally show ?thesis .
  qed
qed

definition newton_sqrt :: "nat \<Rightarrow> nat" where
  "newton_sqrt n = newton_sqrt_aux n n"

declare Discrete.sqrt_code [code del]

theorem Discrete_sqrt_eq_newton_sqrt [code]: "Discrete.sqrt n = newton_sqrt n"
  unfolding newton_sqrt_def by (simp add: newton_sqrt_aux_correct Discrete.sqrt_le)


subsection \<open>Square Testing\<close>

text \<open>
  Next, we implement an algorithm to determine whether a given natural number is a perfect square,
  as described by Cohen~\cite{cohen2010algebraic}. Essentially, the number first determines whether
  the number is a square. Essentially
\<close>

definition q11 :: "nat set"
  where "q11 = {0, 1, 3, 4, 5, 9}"
definition q63 :: "nat set"
  where "q63 = {0, 1, 4, 7, 9, 16, 28, 18, 22, 25, 36, 58, 46, 49, 37, 43}"
definition q64 :: "nat set"
  where "q64 = {0, 1, 4, 9, 16, 17, 25, 36, 33, 49, 41, 57}"
definition q65 :: "nat set"
  where "q65 = {0, 1, 4, 10, 14, 9, 16, 26, 30, 25, 29, 40, 56, 36, 49, 61, 35, 51, 39, 55, 64}"


definition q11_array where
  "q11_array = IArray [True,True,False,True,True,True,False,False,False,True,False]"

definition q63_array where
  "q63_array = IArray [True,True,False,False,True,False,False,True,False,True,False,False,
     False,False,False,False,True,False,True,False,False,False,True,False,False,True,False,
     False,True,False,False,False,False,False,False,False,True,True,False,False,False,False,
     False,True,False,False,True,False,False,True,False,False,False,False,False,False,False,
     False,True,False,False,False,False,False]"

definition q64_array where
  "q64_array = IArray [True,True,False,False,True,False,False,False,False,True,False,False,
     False,False,False,False,True,True,False,False,False,False,False,False,False,True,False,
     False,False,False,False,False,False,True,False,False,True,False,False,False,False,True,
     False,False,False,False,False,False,False,True,False,False,False,False,False,False,
     False,True,False,False,False,False,False,False, False]"

definition q65_array where
  "q65_array = IArray [True,True,False,False,True,False,False,False,False,True,True,False,
     False,False,True,False,True,False,False,False,False,False,False,False,False,True,True,
     False,False,True,True,False,False,False,False,True,True,False,False,True,True,False,
     False,False,False,False,False,False,False,True,False,True,False,False,False,True,True
     ,False,False,False,False,True,False,False,True,False]"

lemma sub_q11_array: "i \<in> {..<11} \<Longrightarrow> IArray.sub q11_array i \<longleftrightarrow> i \<in> q11"
  by (simp add: lessThan_nat_numeral lessThan_Suc q11_def q11_array_def, elim disjE; simp)

lemma sub_q63_array: "i \<in> {..<63} \<Longrightarrow> IArray.sub q63_array i \<longleftrightarrow> i \<in> q63"
  by (simp add: lessThan_nat_numeral lessThan_Suc q63_def q63_array_def, elim disjE; simp)

lemma sub_q64_array: "i \<in> {..<64} \<Longrightarrow> IArray.sub q64_array i \<longleftrightarrow> i \<in> q64"
  by (simp add: lessThan_nat_numeral lessThan_Suc q64_def q64_array_def, elim disjE; simp)

lemma sub_q65_array: "i \<in> {..<65} \<Longrightarrow> IArray.sub q65_array i \<longleftrightarrow> i \<in> q65"
  by (simp add: lessThan_nat_numeral lessThan_Suc q65_def q65_array_def, elim disjE; simp)


lemma in_q11_code: "x mod 11 \<in> q11 \<longleftrightarrow> IArray.sub q11_array (x mod 11)"
  by (subst sub_q11_array) auto

lemma in_q63_code: "x mod 63 \<in> q63 \<longleftrightarrow> IArray.sub q63_array (x mod 63)"
  by (subst sub_q63_array) auto

lemma in_q64_code: "x mod 64 \<in> q64 \<longleftrightarrow> IArray.sub q64_array (x mod 64)"
  by (subst sub_q64_array) auto

lemma in_q65_code: "x mod 65 \<in> q65 \<longleftrightarrow> IArray.sub q65_array (x mod 65)"
  by (subst sub_q65_array) auto


definition square_test :: "nat \<Rightarrow> bool" where
  "square_test n =
    (n mod 64 \<in> q64 \<and> (let r = n mod 45045 in
      r mod 63 \<in> q63 \<and> r mod 65 \<in> q65 \<and> r mod 11 \<in> q11 \<and> n = (Discrete.sqrt n)\<^sup>2))"

lemma square_test_code [code]:
  "square_test n =
    (IArray.sub q64_array (n mod 64) \<and> (let r = n mod 45045 in
           IArray.sub q63_array (r mod 63) \<and> 
           IArray.sub q65_array (r mod 65) \<and>
           IArray.sub q11_array (r mod 11) \<and> n = (Discrete.sqrt n)\<^sup>2))"
    using in_q11_code [symmetric] in_q63_code [symmetric] 
          in_q64_code [symmetric] in_q65_code [symmetric]
  by (simp add: Let_def square_test_def)

lemma square_mod_lower: "m > 0 \<Longrightarrow> (q\<^sup>2 :: nat) mod m = a \<Longrightarrow> \<exists>q' < m. q'\<^sup>2 mod m = a"
  using mod_less_divisor mod_mod_trivial power_mod by blast

lemma q11_upto_def: "q11 = (\<lambda>k. k\<^sup>2 mod 11) ` {..<11}"
  by (simp add: q11_def lessThan_nat_numeral lessThan_Suc insert_commute)

lemma q11_infinite_def: "q11 = (\<lambda>k. k\<^sup>2 mod 11) ` {0..}"
  unfolding q11_upto_def image_def proof (auto, goal_cases)
  case (1 xa)
  show ?case
    using square_mod_lower[of 11 xa "xa\<^sup>2 mod 11"]
      ex_nat_less_eq[of 11 "\<lambda>x. xa\<^sup>2 mod 11 = x\<^sup>2 mod 11"]
    by auto
qed

lemma q63_upto_def: "q63 = (\<lambda>k. k\<^sup>2 mod 63) ` {..<63}"
  by (simp add: q63_def lessThan_nat_numeral lessThan_Suc insert_commute)

lemma q63_infinite_def: "q63 = (\<lambda>k. k\<^sup>2 mod 63) ` {0..}"
  unfolding q63_upto_def image_def proof (auto, goal_cases)
  case (1 xa)
  show ?case
    using square_mod_lower[of 63 xa "xa\<^sup>2 mod 63"]
      ex_nat_less_eq[of 63 "\<lambda>x. xa\<^sup>2 mod 63 = x\<^sup>2 mod 63"]
    by auto
qed

lemma q64_upto_def: "q64 = (\<lambda>k. k\<^sup>2 mod 64) ` {..<64}"
  by (simp add: q64_def lessThan_nat_numeral lessThan_Suc insert_commute)

lemma q64_infinite_def: "q64 = (\<lambda>k. k\<^sup>2 mod 64) ` {0..}"
  unfolding q64_upto_def image_def proof (auto, goal_cases)
  case (1 xa)
  show ?case
    using square_mod_lower[of 64 xa "xa\<^sup>2 mod 64"]
      ex_nat_less_eq[of 64 "\<lambda>x. xa\<^sup>2 mod 64 = x\<^sup>2 mod 64"]
    by auto
qed

lemma q65_upto_def: "q65 = (\<lambda>k. k\<^sup>2 mod 65) ` {..<65}"
  by (simp add: q65_def lessThan_nat_numeral lessThan_Suc insert_commute)

lemma q65_infinite_def: "q65 = (\<lambda>k. k\<^sup>2 mod 65) ` {0..}"
  unfolding q65_upto_def image_def proof (auto, goal_cases)
  case (1 xa)
  show ?case
    using square_mod_lower[of 65 xa "xa\<^sup>2 mod 65"]
      ex_nat_less_eq[of 65 "\<lambda>x. xa\<^sup>2 mod 65 = x\<^sup>2 mod 65"]
    by auto
qed

lemma square_mod_existence:
  fixes n k :: nat
  assumes "\<exists>q. q\<^sup>2 = n"
  shows "\<exists>q. n mod k = q\<^sup>2 mod k"
  using assms by auto

theorem square_test_correct: "square_test n \<longleftrightarrow> is_square n"
proof cases
  assume "is_square n"
  hence  rhs: "\<exists>q. q\<^sup>2 = n" by (auto elim: is_nth_powerE)
  note sq_mod = square_mod_existence[OF this]
  have q64_member: "n mod 64 \<in> q64" using sq_mod[of 64]
    unfolding q64_infinite_def image_def by simp
  let ?r = "n mod 45045"
  have "11 dvd (45045::nat)" "63 dvd (45045::nat)" "65 dvd (45045::nat)" by force+
  then have mod_45045: "?r mod 11 = n mod 11" "?r mod 63 = n mod 63" "?r mod 65 = n mod 65"
    using mod_mod_cancel[of _ 45045 n] by presburger+
  then have "?r mod 11 \<in> q11" "?r mod 63 \<in> q63" "?r mod 65 \<in> q65"
    using sq_mod[of 11] sq_mod[of 63] sq_mod[of 65]
    unfolding q11_infinite_def q63_infinite_def q65_infinite_def image_def mod_45045
    by fast+
  then show ?thesis unfolding square_test_def Let_def using q64_member rhs by auto
next
  assume not_rhs: "\<not>is_square n"
  hence "\<nexists>q. q\<^sup>2 = n" by auto
  then have "(Discrete.sqrt n)\<^sup>2 \<noteq> n" by simp
  then show ?thesis unfolding square_test_def by (auto simp: is_nth_power_def)
qed


definition get_nat_sqrt :: "nat \<Rightarrow> nat option" 
  where "get_nat_sqrt n = (if is_square n then Some (Discrete.sqrt n) else None)"

lemma get_nat_sqrt_code [code]:
  "get_nat_sqrt n = 
    (if IArray.sub q64_array (n mod 64) \<and> (let r = n mod 45045 in
           IArray.sub q63_array (r mod 63) \<and> 
           IArray.sub q65_array (r mod 65) \<and>
           IArray.sub q11_array (r mod 11)) then
       (let x = Discrete.sqrt n in if x\<^sup>2 = n then Some x else None) else None)"
  unfolding get_nat_sqrt_def square_test_correct [symmetric] square_test_def
  using in_q11_code [symmetric] in_q63_code [symmetric] 
        in_q64_code [symmetric] in_q65_code [symmetric]
  by (auto split: if_splits simp: Let_def )

end