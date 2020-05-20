(* ----------------------------------------------------------------- *)
subsection \<open>Quadratic equations\<close>
(* ----------------------------------------------------------------- *)

text \<open>In this section some simple properties of quadratic equations and their roots are derived.
Quadratic equations over reals and over complex numbers, but also systems of quadratic equations and
systems of quadratic and linear equations are analysed.\<close>

theory Quadratic
  imports More_Complex "HOL-Library.Quadratic_Discriminant"
begin

(* ----------------------------------------------------------------- *)
subsubsection \<open>Real quadratic equations, Viette rules\<close>
(* ----------------------------------------------------------------- *)

lemma viette2_monic:
  fixes b c \<xi>1 \<xi>2 :: real
  assumes "b\<^sup>2 - 4*c \<ge> 0" and "\<xi>1\<^sup>2 + b*\<xi>1 + c = 0" and "\<xi>2\<^sup>2 + b*\<xi>2 + c = 0" and "\<xi>1 \<noteq> \<xi>2"
  shows "\<xi>1*\<xi>2 = c"
  using assms
  by algebra

lemma viette2:
  fixes a b c \<xi>1 \<xi>2 :: real
  assumes "a \<noteq> 0" and "b\<^sup>2 - 4*a*c \<ge> 0" and "a*\<xi>1\<^sup>2 + b*\<xi>1 + c = 0" and "a*\<xi>2\<^sup>2 + b*\<xi>2 + c = 0" and "\<xi>1 \<noteq> \<xi>2"
  shows "\<xi>1*\<xi>2 = c/a"
proof (rule viette2_monic[of "b/a" "c/a" \<xi>1 \<xi>2])
  have "(b / a)\<^sup>2 - 4 * (c / a) = (b\<^sup>2 - 4*a*c) / a\<^sup>2"
    using \<open>a \<noteq> 0\<close>
    by (auto simp add: power2_eq_square field_simps)
  thus "0 \<le> (b / a)\<^sup>2 - 4 * (c / a)"
    using \<open>b\<^sup>2 - 4*a*c \<ge> 0\<close>
    by simp
next
  show "\<xi>1\<^sup>2 + b / a * \<xi>1 + c / a = 0" "\<xi>2\<^sup>2 + b / a * \<xi>2 + c / a = 0"
    using assms
    by (auto simp add: power2_eq_square field_simps)
next
  show "\<xi>1 \<noteq> \<xi>2"
    by fact
qed

lemma viette2'_monic:
  fixes b c \<xi> :: real
  assumes "b\<^sup>2 - 4*c = 0" and "\<xi>\<^sup>2 + b*\<xi> + c = 0"
  shows "\<xi>*\<xi> = c"
  using assms
  by algebra

lemma viette2':
  fixes a b c \<xi> :: real
  assumes "a \<noteq> 0" and "b\<^sup>2 - 4*a*c = 0" and "a*\<xi>\<^sup>2 + b*\<xi> + c = 0"
  shows "\<xi>*\<xi> = c/a"
proof (rule viette2'_monic)
  have "(b / a)\<^sup>2 - 4 * (c / a) = (b\<^sup>2 - 4*a*c) / a\<^sup>2"
    using \<open>a \<noteq> 0\<close>
    by (auto simp add: power2_eq_square field_simps)
  thus "(b / a)\<^sup>2 - 4 * (c / a) = 0"
    using \<open>b\<^sup>2 - 4*a*c = 0\<close>
    by simp
next
  show "\<xi>\<^sup>2 + b / a * \<xi> + c / a = 0"
    using assms
    by (auto simp add: power2_eq_square field_simps)
qed

(* ----------------------------------------------------------------- *)
subsubsection \<open>Complex quadratic equations\<close>
(* ----------------------------------------------------------------- *)

lemma complex_quadratic_equation_monic_only_two_roots:
  fixes \<xi> :: complex
  assumes "\<xi>\<^sup>2 + b * \<xi> + c = 0"
  shows "\<xi> = (-b + ccsqrt(b\<^sup>2 - 4*c)) / 2 \<or> \<xi> = (-b - ccsqrt(b\<^sup>2 - 4*c)) / 2"
using assms
proof-
  from assms have "(2 * (\<xi> + b/2))\<^sup>2 = b\<^sup>2 - 4*c"
    by (simp add: power2_eq_square field_simps)
       (metis (no_types, lifting) distrib_right_numeral mult.assoc mult_zero_left)
  hence "2 * (\<xi> + b/2) = ccsqrt (b\<^sup>2 - 4*c) \<or> 2 * (\<xi> + b/2) = - ccsqrt (b\<^sup>2 - 4*c)"
    using ccsqrt[of "(2 * (\<xi> + b / 2))" "b\<^sup>2 - 4 * c"]
    by (simp add: power2_eq_square)
  thus ?thesis
    using mult_cancel_right[of "b + \<xi> * 2" 2 "ccsqrt (b\<^sup>2 - 4*c)"]
    using mult_cancel_right[of "b + \<xi> * 2" 2 "-ccsqrt (b\<^sup>2 - 4*c)"]
    by (auto simp add: field_simps) (metis add_diff_cancel diff_minus_eq_add minus_diff_eq)
qed

lemma complex_quadratic_equation_monic_roots:
  fixes \<xi> :: complex
  assumes "\<xi> = (-b + ccsqrt(b\<^sup>2 - 4*c)) / 2 \<or>
           \<xi> = (-b - ccsqrt(b\<^sup>2 - 4*c)) / 2"
  shows  "\<xi>\<^sup>2 + b * \<xi> + c = 0"
using assms
proof
  assume *: "\<xi> = (- b + ccsqrt (b\<^sup>2 - 4 * c)) / 2"
  show ?thesis
    by ((subst *)+) (subst power_divide, subst power2_sum, simp add: field_simps, simp add: power2_eq_square)
next
  assume *: "\<xi> = (- b - ccsqrt (b\<^sup>2 - 4 * c)) / 2"
  show ?thesis
    by ((subst *)+, subst power_divide, subst power2_diff, simp add: field_simps, simp add: power2_eq_square)
qed

lemma complex_quadratic_equation_monic_distinct_roots:
  fixes b c :: complex
  assumes "b\<^sup>2 - 4*c \<noteq> 0"
  shows "\<exists> k\<^sub>1 k\<^sub>2. k\<^sub>1 \<noteq> k\<^sub>2 \<and> k\<^sub>1\<^sup>2 + b*k\<^sub>1 + c = 0 \<and> k\<^sub>2\<^sup>2 + b*k\<^sub>2 + c = 0"
proof-
  let ?\<xi>1 = "(-b + ccsqrt(b\<^sup>2 - 4*c)) / 2"
  let ?\<xi>2 = "(-b - ccsqrt(b\<^sup>2 - 4*c)) / 2"
  show ?thesis
    apply (rule_tac x="?\<xi>1" in exI)
    apply (rule_tac x="?\<xi>2" in exI)
    using assms 
    using complex_quadratic_equation_monic_roots[of ?\<xi>1 b c]
    using complex_quadratic_equation_monic_roots[of ?\<xi>2 b c]
    by simp
qed

lemma complex_quadratic_equation_two_roots:
  fixes \<xi> :: complex
  assumes "a \<noteq> 0" and "a*\<xi>\<^sup>2 + b * \<xi> + c = 0"
  shows "\<xi> = (-b + ccsqrt(b\<^sup>2 - 4*a*c)) / (2*a) \<or>
         \<xi> = (-b - ccsqrt(b\<^sup>2 - 4*a*c)) / (2*a)"
proof-
  from assms have "\<xi>\<^sup>2 + (b/a) * \<xi> + (c/a) = 0"
    by (simp add: field_simps)
  hence "\<xi> = (-(b/a) + ccsqrt((b/a)\<^sup>2 - 4*(c/a))) / 2 \<or> \<xi> = (-(b/a) - ccsqrt((b/a)\<^sup>2 - 4*(c/a))) / 2"
    using complex_quadratic_equation_monic_only_two_roots[of \<xi> "b/a" "c/a"]
    by simp
  hence "\<exists> k. \<xi> = (-(b/a) + (-1)^k * ccsqrt((b/a)\<^sup>2 - 4*(c/a))) / 2"
    by safe (rule_tac x="2" in exI, simp, rule_tac x="1" in exI, simp)
  then obtain k1 where "\<xi> = (-(b/a) + (-1)^k1 * ccsqrt((b/a)\<^sup>2 - 4*(c/a))) / 2"
    by auto
  moreover
  have "(b / a)\<^sup>2 - 4 * (c / a) = (b\<^sup>2 - 4 * a * c) * (1 / a\<^sup>2)"
    using \<open>a \<noteq> 0\<close>
    by (simp add: field_simps power2_eq_square)
  hence "ccsqrt ((b / a)\<^sup>2 - 4 * (c / a)) = ccsqrt (b\<^sup>2 - 4 * a * c) * ccsqrt (1/a\<^sup>2) \<or>
         ccsqrt ((b / a)\<^sup>2 - 4 * (c / a)) = - ccsqrt (b\<^sup>2 - 4 * a * c) * ccsqrt (1/a\<^sup>2)"
    using ccsqrt_mult[of "b\<^sup>2 - 4 * a * c" "1/a\<^sup>2"]
    by auto
  hence "\<exists> k.  ccsqrt ((b / a)\<^sup>2 - 4 * (c / a)) = (-1)^k * ccsqrt (b\<^sup>2 - 4 * a * c) * ccsqrt (1 / a\<^sup>2)"
    by safe (rule_tac x="2" in exI, simp, rule_tac x="1" in exI, simp)
  then obtain k2 where "ccsqrt ((b / a)\<^sup>2 - 4 * (c / a)) = (-1)^k2 * ccsqrt (b\<^sup>2 - 4 * a * c) * ccsqrt (1 / a\<^sup>2)"
    by auto
  moreover
  have "ccsqrt (1 / a\<^sup>2) = 1/a \<or> ccsqrt (1 / a\<^sup>2) = -1/a"
    using ccsqrt[of "1/a" "1 / a\<^sup>2"]
    by (auto simp add: power2_eq_square)
  hence "\<exists> k. ccsqrt (1 / a\<^sup>2) = (-1)^k * 1/a"
    by safe (rule_tac x="2" in exI, simp, rule_tac x="1" in exI, simp)
  then obtain k3 where "ccsqrt (1 / a\<^sup>2) = (-1)^k3 * 1/a"
    by auto
  ultimately
  have "\<xi> = (- (b / a) + ((-1) ^ k1 * (-1) ^ k2 * (-1) ^ k3) * ccsqrt (b\<^sup>2 - 4 * a * c) * 1/a) / 2"
    by simp
  moreover
  have "(-(1::complex)) ^ k1 * (-1) ^ k2 * (-1) ^ k3 = 1 \<or> (-(1::complex)) ^ k1 * (-1) ^ k2 * (-1) ^ k3 = -1"
    using neg_one_even_power[of "k1 + k2 + k3"]
    using neg_one_odd_power[of "k1 + k2 + k3"]
    by (smt power_add)
  ultimately
  have "\<xi> = (- (b / a) + ccsqrt (b\<^sup>2 - 4 * a * c) * 1 / a) / 2 \<or> \<xi> = (- (b / a) - ccsqrt (b\<^sup>2 - 4 * a * c) * 1 / a) / 2"
    by auto
  thus ?thesis
    using \<open>a \<noteq> 0\<close>
    by (simp add: field_simps)
qed

lemma complex_quadratic_equation_only_two_roots:
  fixes x :: complex
  assumes "a \<noteq> 0"
  assumes "qf = (\<lambda> x. a*x\<^sup>2 + b*x + c)"
          "qf x1 = 0" and "qf x2 = 0" and "x1 \<noteq> x2"
          "qf x = 0"
  shows "x = x1 \<or> x = x2"
  using assms
  using complex_quadratic_equation_two_roots
  by blast


(* ----------------------------------------------------------------- *)
subsubsection \<open>Intersections of linear and quadratic forms\<close>
(* ----------------------------------------------------------------- *)
(* These lemmas are not used *)

lemma quadratic_linear_at_most_2_intersections_help:
  fixes x y :: complex
  assumes "(a11, a12, a22) \<noteq> (0, 0, 0)" and "k2 \<noteq> 0"
          "qf = (\<lambda> x y. a11*x\<^sup>2 + 2*a12*x*y + a22*y\<^sup>2 + b1*x + b2*y + c)" and "lf = (\<lambda> x y. k1*x + k2*y + n)"
          "qf x y = 0" and "lf x y = 0"
          "pf = (\<lambda> x. (a11 - 2*a12*k1/k2 + a22*k1\<^sup>2/k2\<^sup>2)*x\<^sup>2 + (-2*a12*n/k2  + b1 + a22*2*n*k1/k2\<^sup>2 - b2*k1/k2)*x + a22*n\<^sup>2/k2\<^sup>2 - b2*n/k2 + c)"
          "yf = (\<lambda> x. (-n - k1*x) / k2)"
  shows "pf x = 0" and "y = yf x"
proof -
  show "y = yf x"
    using assms
    by (simp add:field_simps eq_neg_iff_add_eq_0)
next
  have "2*a12*x*(-n - k1*x)/k2 = (-2*a12*n/k2)*x - (2*a12*k1/k2)*x\<^sup>2"
    by algebra
  have "a22*((-n - k1*x)/k2)\<^sup>2 = a22*n\<^sup>2/k2\<^sup>2 + (a22*2*n*k1/k2\<^sup>2)*x + (a22*k1\<^sup>2/k2\<^sup>2)*x\<^sup>2"
    by (simp add: power_divide) algebra
  have "2*a12*x*(-n - k1*x)/k2 = (-2*a12*n/k2)*x - (2*a12*k1/k2)*x\<^sup>2"
    by algebra
  have "b2*(-n - k1*x)/k2 = -b2*n/k2 - (b2*k1/k2)*x"
    by algebra

  have *: "y = (-n - k1*x)/k2"
    using assms(2, 4, 6)
    by (simp add:field_simps eq_neg_iff_add_eq_0)

  have "0 = a11*x\<^sup>2 + 2*a12*x*y + a22*y\<^sup>2 + b1*x + b2*y + c"
    using assms
    by simp
  hence "0 = a11*x\<^sup>2 + 2*a12*x*(-n - k1*x)/k2 + a22*((-n - k1*x)/k2)\<^sup>2 + b1*x + b2*(-n - k1*x)/k2 + c"
    by (subst (asm) *, subst (asm) *, subst (asm) *) auto
  also have "... = (a11 - 2*a12*k1/k2 + a22*k1\<^sup>2/k2\<^sup>2)*x\<^sup>2 + (-2*a12*n/k2  + b1 + a22*2*n*k1/k2\<^sup>2 - b2*k1/k2)*x + a22*n\<^sup>2/k2\<^sup>2 -b2*n/k2 + c"
    using \<open>2*a12*x*(-n - k1*x)/k2 = (-2*a12*n/k2)*x - (2*a12*k1/k2)*x\<^sup>2\<close>
    using \<open>a22*((-n - k1*x)/k2)\<^sup>2 = a22*n\<^sup>2/k2\<^sup>2 + (a22*2*n*k1/k2\<^sup>2)*x + (a22*k1\<^sup>2/k2\<^sup>2)*x\<^sup>2\<close>
    using \<open>b2*(-n - k1*x)/k2 = -b2*n/k2 - (b2*k1/k2)*x\<close>
    by (simp add:field_simps)
  finally show "pf x = 0"
    using assms(7)
    by auto
qed

lemma quadratic_linear_at_most_2_intersections_help':
  fixes x y :: complex
  assumes "qf = (\<lambda> x y. a11*x\<^sup>2 + 2*a12*x*y + a22*y\<^sup>2 + b1*x + b2*y + c)"
          "x = -n/k1" and "k1 \<noteq> 0" and "qf x y = 0"
          "yf = (\<lambda> y. k1\<^sup>2*a22*y\<^sup>2 + (-2*a12*n*k1 + b2*k1\<^sup>2)*y + a11*n\<^sup>2 - b1*n*k1 + c*k1\<^sup>2)"
  shows "yf y = 0"
proof-
  have "0 = a11*n\<^sup>2/k1\<^sup>2 - 2*a12*n*y/k1 + a22*y\<^sup>2 - b1*n/k1 + b2*y + c"
    using assms(1, 2, 4)
    by (simp add: power_divide)
  hence "0 = a11*n\<^sup>2 - 2*a12*n*k1*y + a22*y\<^sup>2*k1\<^sup>2 - b1*n*k1 + b2*y*k1\<^sup>2 + c*k1\<^sup>2"
    using assms(3)
    apply (simp add:field_simps power2_eq_square)
    by algebra
  thus ?thesis
    using assms(1, 4, 5)
    by (simp add:field_simps)
qed

lemma quadratic_linear_at_most_2_intersections:
  fixes x y x1 y1 x2 y2 :: complex
  assumes "(a11, a12, a22) \<noteq> (0, 0, 0)" and "(k1, k2) \<noteq> (0, 0)"
  assumes "a11*k2\<^sup>2 - 2*a12*k1*k2 + a22*k1\<^sup>2 \<noteq> 0"
  assumes "qf = (\<lambda> x y. a11*x\<^sup>2 + 2*a12*x*y + a22*y\<^sup>2 + b1*x + b2*y + c)" and "lf = (\<lambda> x y. k1*x + k2*y + n)"
          "qf x1 y1 = 0" and "lf x1 y1 = 0"
          "qf x2 y2 = 0" and "lf x2 y2 = 0"
          "(x1, y1) \<noteq> (x2, y2)"
          "qf x y = 0" and "lf x y = 0"
  shows "(x, y) = (x1, y1) \<or> (x, y) = (x2, y2)"
proof(cases "k2 = 0")
  case True
  hence "k1 \<noteq> 0"
    using assms(2)
    by simp

  have "a22*k1\<^sup>2 \<noteq> 0"
    using assms(3) True
    by auto

  have "x1 = -n/k1"
    using \<open>k1 \<noteq> 0\<close> assms(5, 7) True
    by (metis add.right_neutral add_eq_0_iff2 mult_zero_left nonzero_mult_div_cancel_left)
  have "x2 = -n/k1"
    using \<open>k1 \<noteq> 0\<close> assms(5, 9) True
    by (metis add.right_neutral add_eq_0_iff2 mult_zero_left nonzero_mult_div_cancel_left)
  have "x = -n/k1"
    using \<open>k1 \<noteq> 0\<close> assms(5, 12) True
    by (metis add.right_neutral add_eq_0_iff2 mult_zero_left nonzero_mult_div_cancel_left)

  let ?yf =  "(\<lambda> y. k1\<^sup>2*a22*y\<^sup>2 + (-2*a12*n*k1 + b2*k1\<^sup>2)*y + a11*n\<^sup>2 - b1*n*k1 + c*k1\<^sup>2)"

  have "?yf y = 0"
    using quadratic_linear_at_most_2_intersections_help'[of qf a11 a12 a22 b1 b2 c x n k1 y ?yf]
    using assms(4, 11) \<open>k1 \<noteq> 0\<close> \<open>x = -n/k1\<close>
    by auto
  have "?yf y1 = 0"
    using quadratic_linear_at_most_2_intersections_help'[of qf a11 a12 a22 b1 b2 c x1 n k1 y1 ?yf]
    using assms(4, 6) \<open>k1 \<noteq> 0\<close> \<open>x1 = -n/k1\<close>
    by auto
  have "?yf y2 = 0"
    using quadratic_linear_at_most_2_intersections_help'[of qf a11 a12 a22 b1 b2 c x2 n k1 y2 ?yf]
    using assms(4, 8) \<open>k1 \<noteq> 0\<close> \<open>x2 = -n/k1\<close>
    by auto

  have "y1 \<noteq> y2"
    using assms(10) \<open>x1 = -n/k1\<close> \<open>x2 = -n/k1\<close>
    by blast

  have "y = y1 \<or> y = y2"
    using complex_quadratic_equation_only_two_roots[of "a22*k1\<^sup>2" ?yf "-2*a12*n*k1 + b2*k1\<^sup>2" "a11*n\<^sup>2 - b1*n*k1 + c*k1\<^sup>2"
                                                        y1 y2 y]
    using \<open>a22*k1\<^sup>2 \<noteq> 0\<close> \<open>?yf y1 = 0\<close> \<open>y1 \<noteq> y2\<close> \<open>?yf y2 = 0\<close> \<open>?yf y = 0\<close>
    by fastforce

  thus ?thesis
    using \<open>x1 = -n/k1\<close> \<open>x2 = -n/k1\<close>  \<open>x = -n/k1\<close>
    by auto
next
  case False

  let ?py = "(\<lambda> x. (-n - k1*x)/k2)"
  let ?pf = "(\<lambda> x. (a11 - 2*a12*k1/k2 + a22*k1\<^sup>2/k2\<^sup>2)*x\<^sup>2 + (-2*a12*n/k2  + b1 + a22*2*n*k1/k2\<^sup>2 - b2*k1/k2)*x + a22*n\<^sup>2/k2\<^sup>2 -b2*n/k2 + c)"
  have "?pf x1 = 0" "y1 = ?py x1"
    using quadratic_linear_at_most_2_intersections_help[of a11 a12 a22 k2 qf b1 b2 c lf k1 n x1 y1]
    using assms(1, 4, 5, 6, 7) False
    by auto
  have "?pf x2 = 0" "y2 = ?py x2"
    using quadratic_linear_at_most_2_intersections_help[of a11 a12 a22 k2 qf b1 b2 c lf k1 n x2 y2]
    using assms(1, 4, 5, 8, 9) False
    by auto
  have "?pf x = 0" "y = ?py x"
    using quadratic_linear_at_most_2_intersections_help[of a11 a12 a22 k2 qf b1 b2 c lf k1 n x y]
    using assms(1, 4, 5, 11, 12) False
    by auto

  have "x1 \<noteq> x2"
    using assms(10) \<open>y1 = ?py x1\<close> \<open>y2 = ?py x2\<close>
    by auto

  have "a11 - 2*a12*k1/k2 + a22*k1\<^sup>2/k2\<^sup>2 = (a11 * k2\<^sup>2 - 2 * a12 * k1 * k2 + a22 * k1\<^sup>2)/k2\<^sup>2"
    by (simp add: False power2_eq_square add_divide_distrib diff_divide_distrib)
  also have "...  \<noteq> 0"
    using False assms(3)
    by simp
  finally have "a11 - 2*a12*k1/k2 + a22*k1\<^sup>2/k2\<^sup>2 \<noteq> 0"
    .

  have "x = x1 \<or> x = x2"
    using complex_quadratic_equation_only_two_roots[of "a11 - 2*a12*k1/k2 + a22*k1\<^sup>2/k2\<^sup>2" ?pf
                                                       "(- 2 * a12 * n / k2 + b1 + a22 * 2 * n * k1 / k2\<^sup>2 - b2 * k1 / k2)"
                                                       "a22 * n\<^sup>2 / k2\<^sup>2 - b2 * n / k2 + c" x1 x2 x]
    using \<open>?pf x2 = 0\<close> \<open>?pf x1 = 0\<close> \<open>?pf x = 0\<close>
    using \<open>a11 - 2 * a12 * k1 / k2 + a22 * k1\<^sup>2 / k2\<^sup>2 \<noteq> 0\<close>
    using \<open>x1 \<noteq> x2\<close>
    by fastforce

  thus ?thesis
    using \<open>y = ?py x\<close> \<open>y1 = ?py x1\<close> \<open>y2 = ?py x2\<close>
    by (cases "x = x1", auto)
qed

lemma quadratic_quadratic_at_most_2_intersections':
  fixes x y x1 y1 x2 y2 :: complex
  assumes "b2 \<noteq> B2 \<or> b1 \<noteq> B1"
          "(b2 - B2)\<^sup>2 + (b1 - B1)\<^sup>2 \<noteq> 0"
  assumes "qf1 = (\<lambda> x y. x\<^sup>2 + y\<^sup>2 + b1*x + b2*y + c)"
          "qf2 = (\<lambda> x y. x\<^sup>2 + y\<^sup>2 + B1*x + B2*y + C)"
          "qf1 x1 y1 = 0" "qf2 x1 y1 = 0"
          "qf1 x2 y2 = 0" "qf2 x2 y2 = 0"
          "(x1, y1) \<noteq> (x2, y2)"
          "qf1 x y = 0" "qf2 x y = 0"
  shows "(x, y) = (x1, y1) \<or> (x, y) = (x2, y2)"
proof-
  have "x\<^sup>2 + y\<^sup>2 + b1*x + b2*y + c = 0"
    using assms by auto
  have "x\<^sup>2 + y\<^sup>2 + B1*x + B2*y + C = 0"
    using assms by auto
  hence "0 = x\<^sup>2 + y\<^sup>2 + b1*x + b2*y + c - (x\<^sup>2 + y\<^sup>2 + B1*x + B2*y + C)"
    using \<open>x\<^sup>2 + y\<^sup>2 + b1*x + b2*y + c = 0\<close>
    by auto
  hence "0 = (b1 - B1)*x + (b2 - B2)*y + c - C"
    by (simp  add:field_simps) 
  
  have "x1\<^sup>2 + y1\<^sup>2 + b1*x1 + b2*y1 + c = 0"
    using assms  by auto
  have "x1\<^sup>2 + y1\<^sup>2 + B1*x1 + B2*y1 + C = 0"
    using assms by auto
  hence "0 = x1\<^sup>2 + y1\<^sup>2 + b1*x1 + b2*y1 + c - (x1\<^sup>2 + y1\<^sup>2 + B1*x1 + B2*y1 + C)"
    using \<open>x1\<^sup>2 + y1\<^sup>2 + b1*x1 + b2*y1 + c = 0\<close>
    by auto
  hence "0 = (b1 - B1)*x1 + (b2 - B2)*y1 + c - C"
    by (simp  add:field_simps) 

  have "x2\<^sup>2 + y2\<^sup>2 + b1*x2 + b2*y2 + c = 0"
    using assms  by auto
  have "x2\<^sup>2 + y2\<^sup>2 + B1*x2 + B2*y2 + C = 0"
    using assms  by auto
  hence "0 = x2\<^sup>2 + y2\<^sup>2 + b1*x2 + b2*y2 + c - (x2\<^sup>2 + y2\<^sup>2 + B1*x2 + B2*y2 + C)"
    using \<open>x2\<^sup>2 + y2\<^sup>2 + b1*x2 + b2*y2 + c = 0\<close>
    by auto
  hence "0 = (b1 - B1)*x2 + (b2 - B2)*y2 + c - C"
    by (simp  add:field_simps)  

  have "(b1 - B1, b2 - B2) \<noteq> (0, 0)"
    using assms(1) by auto

  let ?lf = "(\<lambda> x y. (b1 - B1)*x + (b2 - B2)*y + c - C)"

  have "?lf x y = 0" "?lf x1 y1 = 0" "?lf x2 y2 = 0"
    using \<open>0 = (b1 - B1)*x2 + (b2 - B2)*y2 + c - C\<close>
          \<open>0 = (b1 - B1)*x1 + (b2 - B2)*y1 + c - C\<close>
          \<open>0 = (b1 - B1)*x + (b2 - B2)*y + c - C\<close>
    by auto

  thus ?thesis
    using quadratic_linear_at_most_2_intersections[of 1 0 1 "b1 - B1" "b2 - B2" qf1 b1 b2 c ?lf "c - C" x1 y1 x2 y2 x y]
    using \<open>(b1 - B1, b2 - B2) \<noteq> (0, 0)\<close>
    using assms \<open>(b1 - B1, b2 - B2) \<noteq> (0, 0)\<close>
    using \<open>(b1 - B1) * x + (b2 - B2) * y + c - C = 0\<close> \<open>(b1 - B1) * x1 + (b2 - B2) * y1 + c - C = 0\<close>
    by (simp add: add_diff_eq)
qed

lemma quadratic_change_coefficients:
  fixes x y :: complex
  assumes "A1 \<noteq> 0" 
  assumes "qf = (\<lambda> x y. A1*x\<^sup>2 + A1*y\<^sup>2 + b1*x + b2*y + c)"
          "qf x y = 0"
          "qf_1 = (\<lambda> x y. x\<^sup>2 + y\<^sup>2 + (b1/A1)*x + (b2/A1)*y + c/A1)"
  shows "qf_1 x y = 0"
proof-
  have "0 = A1*x\<^sup>2 + A1*y\<^sup>2 + b1*x + b2*y + c"
    using assms by auto
  hence "0/A1 = (A1*x\<^sup>2 + A1*y\<^sup>2 + b1*x + b2*y + c)/A1"
    using assms(1) by auto
  also have "... = A1*x\<^sup>2/A1 + A1*y\<^sup>2/A1 + b1*x/A1 + b2*y/A1 + c/A1"
    by (simp add: add_divide_distrib)
  also have "... = x\<^sup>2 + y\<^sup>2 + (b1/A1)*x + (b2/A1)*y + c/A1"
    using assms(1)
    by (simp add:field_simps)
  finally have "0 = x\<^sup>2 + y\<^sup>2 + (b1/A1)*x + (b2/A1)*y + c/A1"
    by simp
  thus ?thesis
    using assms
    by simp
qed

lemma quadratic_quadratic_at_most_2_intersections:
  fixes x y x1 y1 x2 y2 :: complex
  assumes "A1 \<noteq> 0" and "A2 \<noteq> 0"
  assumes "qf1 = (\<lambda> x y. A1*x\<^sup>2 + A1*y\<^sup>2 + b1*x + b2*y + c)" and
          "qf2 = (\<lambda> x y. A2*x\<^sup>2 + A2*y\<^sup>2 + B1*x + B2*y + C)" and
          "qf1 x1 y1 = 0" and "qf2 x1 y1 = 0" and
          "qf1 x2 y2 = 0" and "qf2 x2 y2 = 0" and
          "(x1, y1) \<noteq> (x2, y2)" and
          "qf1 x y = 0" and "qf2 x y = 0"
  assumes "(b2*A2 - B2*A1)\<^sup>2 + (b1*A2 - B1*A1)\<^sup>2 \<noteq> 0" and
          "b2*A2 \<noteq> B2*A1 \<or> b1*A2 \<noteq> B1*A1"
  shows "(x, y) = (x1, y1) \<or> (x, y) = (x2, y2)"
proof-
  have *: "b2 / A1 \<noteq> B2 / A2 \<or> b1 / A1 \<noteq> B1 / A2"
    using assms(1, 2) assms(13)
    by (simp add:field_simps)
  have **: "(b2 / A1 - B2 / A2)\<^sup>2 + (b1 / A1 - B1 / A2)\<^sup>2 \<noteq> 0"
    using assms(1, 2) assms(12)
    by (simp add:field_simps)

  let ?qf_1 = "(\<lambda> x y. x\<^sup>2 + y\<^sup>2 + (b1/A1)*x + (b2/A1)*y + c/A1)"
  let ?qf_2 = "(\<lambda> x y. x\<^sup>2 + y\<^sup>2 + (B1/A2)*x + (B2/A2)*y + C/A2)"

  have "?qf_1 x1 y1 = 0" "?qf_1 x2 y2 = 0" "?qf_1 x y = 0"
       "?qf_2 x1 y1 = 0" "?qf_2 x2 y2 = 0" "?qf_2 x y = 0"
    using assms quadratic_change_coefficients[of A1 qf1 b1 b2 c x2 y2 ?qf_1]
          quadratic_change_coefficients[of A1 qf1 b1 b2 c x1 y1 ?qf_1]
          quadratic_change_coefficients[of A2 qf2 B1 B2 C x1 y1 ?qf_2]
          quadratic_change_coefficients[of A2 qf2 B1 B2 C x2 y2 ?qf_2]
          quadratic_change_coefficients[of A1 qf1 b1 b2 c x y ?qf_1]
          quadratic_change_coefficients[of A2 qf2 B1 B2 C x y ?qf_2]
    by auto

  thus ?thesis
    using quadratic_quadratic_at_most_2_intersections'
              [of "b2 / A1" "B2 / A2" "b1 / A1" "B1 / A2" ?qf_1 "c / A1" ?qf_2 "C / A2" x1 y1 x2 y2 x y]
    using * ** \<open>(x1, y1) \<noteq> (x2, y2)\<close>
    by fastforce
qed

end
