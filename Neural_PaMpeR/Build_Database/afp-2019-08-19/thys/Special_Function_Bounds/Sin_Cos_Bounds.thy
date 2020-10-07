chapter \<open>Sine and Cosine Upper and Lower Bounds\<close>

theory Sin_Cos_Bounds
imports Bounds_Lemmas

begin

section\<open>Simple base cases\<close>

text\<open>Upper bound for @{term"x\<ge>0"}\<close>
lemma sin_le_arg:
  fixes x :: real
    shows "0 \<le> x \<Longrightarrow> sin x \<le> x"
  by (fact sin_x_le_x)

lemma cos_ge_1_arg:
  fixes x :: real
  assumes "0 \<le> x"
    shows "1 - x \<le> cos x"
  apply (rule gen_lower_bound_increasing [OF assms])
  apply (intro derivative_eq_intros, auto)
  done

lemmas sin_Taylor_0_upper_bound_pos = sin_le_arg \<comment> \<open>MetiTarski bound\<close>

lemma cos_Taylor_1_lower_bound:
  fixes x :: real
  assumes "0 \<le> x"
    shows "(1 - x^2 / 2) \<le> cos x"
  apply (rule gen_lower_bound_increasing [OF assms])
  apply (intro derivative_eq_intros)
  apply (rule refl | simp add: sin_le_arg)+
  done

lemma sin_Taylor_1_lower_bound:
  fixes x :: real
  assumes "0 \<le> x"
    shows "(x - x ^ 3 / 6) \<le> sin x"
  apply (rule gen_lower_bound_increasing [OF assms])
  apply (intro derivative_eq_intros)
  apply (rule refl | simp add: cos_Taylor_1_lower_bound)+
  done

section\<open>Taylor series approximants\<close>

definition sinpoly :: "[nat,real] \<Rightarrow> real"
  where "sinpoly n = (\<lambda>x. \<Sum>k<n. sin_coeff k * x ^ k)"

definition cospoly :: "[nat,real] \<Rightarrow> real"
  where "cospoly n = (\<lambda>x. \<Sum>k<n. cos_coeff k * x ^ k)"

(*sin upper bounds have the form 4*n+2; lower bounds, 4*n
sinpoly 2 x = x                                      (upper)
sinpoly 4 x = x - (x^3)/6                            (lower)
sinpoly 6 x = x - (x^3)/6 + (x^5)/120                (upper)
sinpoly 8 x = x - (x^3)/6 + (x^5)/120 - (x^7)/5040   (lower)

cos upper bounds have the form 4*n+1; lower bounds, 4*n+3
cospoly 1 x = 1                                                             (upper)
cospoly 3 x = 1 - (x^2)/2                                                   (lower)
cospoly 5 x = 1 - (x^2)/2 + (x^4)/24 - x^6/720 + x^8/40320                  (upper)
cospoly 7 x = 1 - (x^2)/2 + (x^4)/24 - x^6/720 + x^8/40320 - x^10/3628800   (lower)
*)

lemma sinpoly_Suc: "sinpoly (Suc n) = (\<lambda>x. sinpoly n x + sin_coeff n * x ^ n)"
  by (simp add: sinpoly_def)

lemma cospoly_Suc: "cospoly (Suc n) = (\<lambda>x. cospoly n x + cos_coeff n * x ^ n)"
  by (simp add: cospoly_def)

lemma sinpoly_minus [simp]: "sinpoly n (-x) = - sinpoly n x"
  by (induct n) (auto simp: sinpoly_def sin_coeff_def)

lemma cospoly_minus [simp]: "cospoly n (-x) = cospoly n x"
  by (induct n) (auto simp: cospoly_def cos_coeff_def)

lemma d_sinpoly_cospoly:
    "(sinpoly (Suc n) has_field_derivative cospoly n x) (at x)"
proof (induction n)
  case 0 show ?case
    by (simp add: sinpoly_def cospoly_def)
next
  case (Suc n) show ?case
  proof (cases "n=0")
    case True then show ?thesis
      by (simp add: sinpoly_def sin_coeff_def cospoly_def)
  next
    case False then
    have xn: "x ^ (n - Suc 0) * x = x ^ n"
      by (metis Suc_pred mult.commute not_gr0 power_Suc)
    show ?thesis using Suc False
      apply (simp add: sinpoly_Suc [of "Suc n"] cospoly_def)
      apply (intro derivative_eq_intros | simp)+
      apply (simp add: xn mult.assoc sin_coeff_def cos_coeff_def divide_simps del: fact_Suc)
      apply (simp add: algebra_simps)
      done
  qed
qed

lemma d_cospoly_sinpoly:
    "(cospoly (Suc n) has_field_derivative -sinpoly n x) (at x)"
proof (induction n)
  case 0 show ?case
    by (simp add: sinpoly_def cospoly_def)
next
  case (Suc n) show ?case
  proof (cases "n=0")
    case True then show ?thesis
      by (simp add: sinpoly_def cospoly_def cos_coeff_def)
  next
    case False then
    have xn: "x ^ (n - Suc 0) * x = x ^ n"
      by (metis Suc_pred mult.commute not_gr0 power_Suc)
    have m1: "odd n \<Longrightarrow> (-1 :: real) ^ ((n - Suc 0) div 2) = - ((-1) ^ (Suc n div 2))"
      by (cases n) simp_all
    show ?thesis using Suc False
      apply (simp add: cospoly_Suc [of "Suc n"] sinpoly_def)
      apply (intro derivative_eq_intros | simp)+
      apply (simp add: xn mult.assoc sin_coeff_def cos_coeff_def m1 divide_simps del: fact_Suc)
      apply (simp add: algebra_simps)
      done
  qed
qed


section\<open>Inductive proof of sine inequalities\<close>

lemma sinpoly_lb_imp_cospoly_ub:
  assumes x0: "0 \<le> x" and k0: "k>0" and "\<And>x. 0 \<le> x \<Longrightarrow> sinpoly (k - 1) x \<le> sin x"
    shows "cos x \<le> cospoly k x"
  apply (rule gen_lower_bound_increasing [OF x0])
  apply (intro derivative_eq_intros | simp)+
  using d_cospoly_sinpoly [of "k - 1"] assms
  apply auto
  apply (simp add: cospoly_def)
  done

lemma cospoly_ub_imp_sinpoly_ub:
  assumes x0: "0 \<le> x" and k0: "k>0" and "\<And>x. 0 \<le> x \<Longrightarrow> cos x \<le> cospoly (k - 1) x"
    shows "sin x \<le> sinpoly k x"
  apply (rule gen_lower_bound_increasing [OF x0])
  apply (intro derivative_eq_intros | simp)+
  using d_sinpoly_cospoly [of "k - 1"] assms
  apply auto
  apply (simp add: sinpoly_def)
  done

lemma sinpoly_ub_imp_cospoly_lb:
  assumes x0: "0 \<le> x" and k0: "k>0" and "\<And>x. 0 \<le> x \<Longrightarrow> sin x \<le> sinpoly (k - 1) x"
    shows "cospoly k x \<le> cos x"
  apply (rule gen_lower_bound_increasing [OF x0])
  apply (intro derivative_eq_intros | simp)+
  using d_cospoly_sinpoly [of "k - 1"] assms
  apply auto
  apply (simp add: cospoly_def)
  done

lemma cospoly_lb_imp_sinpoly_lb:
  assumes x0: "0 \<le> x" and k0: "k>0" and "\<And>x. 0 \<le> x \<Longrightarrow> cospoly (k - 1) x \<le> cos x"
    shows "sinpoly k x \<le> sin x"
  apply (rule gen_lower_bound_increasing [OF x0])
  apply (intro derivative_eq_intros | simp)+
  using d_sinpoly_cospoly [of "k - 1"] assms
  apply auto
  apply (simp add: sinpoly_def)
  done

lemma
  assumes "0 \<le> x"
    shows sinpoly_lower_nonneg: "sinpoly (4 * Suc n) x \<le> sin x"        (is ?th1)
      and sinpoly_upper_nonneg: "sin x \<le> sinpoly (Suc (Suc (4*n))) x"  (is ?th2)
proof -
  have "sinpoly (4 * Suc n) x \<le> sin x  \<and>  sin x \<le> sinpoly (Suc (Suc (4*n))) x"
    using assms
    apply (induction n arbitrary: x)
    apply (simp add: sinpoly_def sin_coeff_def sin_Taylor_1_lower_bound sin_Taylor_0_upper_bound_pos lessThan_nat_numeral fact_numeral)
    apply (auto simp: cospoly_lb_imp_sinpoly_lb sinpoly_ub_imp_cospoly_lb cospoly_ub_imp_sinpoly_ub sinpoly_lb_imp_cospoly_ub)
    done
  then show ?th1 ?th2
    using assms
    by auto
qed


section\<open>Collecting the results\<close>

corollary sinpoly_upper_nonpos:
     "x \<le> 0 \<Longrightarrow> sin x \<le> sinpoly (4 * Suc n) x"
  using sinpoly_lower_nonneg [of "-x" n]
  by simp

corollary sinpoly_lower_nonpos:
     "x \<le> 0 \<Longrightarrow> sinpoly (Suc (Suc (4*n))) x \<le> sin x"
  using sinpoly_upper_nonneg [of "-x" n]
  by simp

corollary cospoly_lower_nonneg:
     "0 \<le> x \<Longrightarrow> cospoly (Suc (Suc (Suc (4*n)))) x \<le> cos x"
by (auto simp: sinpoly_upper_nonneg sinpoly_ub_imp_cospoly_lb)

lemma cospoly_lower:
     "cospoly (Suc (Suc (Suc (4*n)))) x \<le> cos x"
proof (cases rule: le_cases [of 0 x])
  case le then show ?thesis
    by (simp add: cospoly_lower_nonneg)
next
  case ge then show ?thesis using cospoly_lower_nonneg [of "-x"]
    by simp
qed

lemma cospoly_upper_nonneg:
  assumes "0 \<le> x"
    shows "cos x \<le> cospoly (Suc (4*n)) x"
proof (cases n)
  case 0 then show ?thesis
    by (simp add: cospoly_def)
next
  case (Suc m)
  then show ?thesis
    using sinpoly_lower_nonneg [of _ m] assms
    by (auto simp: sinpoly_lb_imp_cospoly_ub)
qed

lemma cospoly_upper:
  "cos x \<le> cospoly (Suc (4*n)) x"
proof (cases rule: le_cases [of 0 x])
  case le then show ?thesis
    by (simp add: cospoly_upper_nonneg)
next
  case ge then show ?thesis using cospoly_upper_nonneg [of "-x"]
    by simp
qed

end

