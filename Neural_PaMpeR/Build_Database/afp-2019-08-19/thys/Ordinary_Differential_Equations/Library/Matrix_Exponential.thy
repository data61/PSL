section \<open>Matrix Exponential\<close>
theory Matrix_Exponential
imports
  "../ODE_Numerics"
begin

lemma field_differentiable_bound:\<comment> \<open>TODO: generalize @{thm field_differentiable_bound}\<close>
  fixes s :: "'a::real_normed_field set"
  assumes cvs: "convex s"
      and df:  "\<And>z. z \<in> s \<Longrightarrow> (f has_field_derivative f' z) (at z within s)"
      and dn:  "\<And>z. z \<in> s \<Longrightarrow> norm (f' z) \<le> B"
      and "x \<in> s"  "y \<in> s"
    shows "norm(f x - f y) \<le> B * norm(x - y)"
  apply (rule differentiable_bound [OF cvs])
  apply (rule ballI, erule df [unfolded has_field_derivative_def])
  apply (rule ballI, rule onorm_le, simp add: norm_mult mult_right_mono dn)
  apply fact
  apply fact
  done

lemma field_Taylor:\<comment> \<open>TODO: generalize @{thm complex_Taylor}\<close>
  assumes s: "convex s"
      and f: "\<And>i x. x \<in> s \<Longrightarrow> i \<le> n \<Longrightarrow> (f i has_field_derivative f (Suc i) x) (at x within s)"
      and B: "\<And>x. x \<in> s \<Longrightarrow> norm (f (Suc n) x) \<le> B"
      and w: "w \<in> s"
      and z: "z \<in> s"
    shows "norm(f 0 z - (\<Sum>i\<le>n. f i w * (z-w) ^ i / (fact i)))
          \<le> B * norm(z - w)^(Suc n) / fact n"
proof -
  have wzs: "closed_segment w z \<subseteq> s" using assms
    by (metis convex_contains_segment)
  { fix u
    assume "u \<in> closed_segment w z"
    then have "u \<in> s"
      by (metis wzs subsetD)
    have "(\<Sum>i\<le>n. f i u * (- of_nat i * (z-u)^(i - 1)) / (fact i) +
                      f (Suc i) u * (z-u)^i / (fact i)) =
              f (Suc n) u * (z-u) ^ n / (fact n)"
    proof (induction n)
      case 0 show ?case by simp
    next
      case (Suc n)
      have "(\<Sum>i\<le>Suc n. f i u * (- of_nat i * (z-u) ^ (i - 1)) / (fact i) +
                             f (Suc i) u * (z-u) ^ i / (fact i)) =
           f (Suc n) u * (z-u) ^ n / (fact n) +
           f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n) / (fact (Suc n)) -
           f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n) / (fact (Suc n))"
        using Suc by simp
      also have "... = f (Suc (Suc n)) u * (z-u) ^ Suc n / (fact (Suc n))"
      proof -
        have "(fact(Suc n)) *
             (f(Suc n) u *(z-u) ^ n / (fact n) +
               f(Suc(Suc n)) u *((z-u) *(z-u) ^ n) / (fact(Suc n)) -
               f(Suc n) u *((1 + of_nat n) *(z-u) ^ n) / (fact(Suc n))) =
            ((fact(Suc n)) *(f(Suc n) u *(z-u) ^ n)) / (fact n) +
            ((fact(Suc n)) *(f(Suc(Suc n)) u *((z-u) *(z-u) ^ n)) / (fact(Suc n))) -
            ((fact(Suc n)) *(f(Suc n) u *(of_nat(Suc n) *(z-u) ^ n))) / (fact(Suc n))"
          by (simp add: algebra_simps del: fact_Suc)
        also have "... = ((fact (Suc n)) * (f (Suc n) u * (z-u) ^ n)) / (fact n) +
                         (f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)) -
                         (f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n))"
          by (simp del: fact_Suc)
        also have "... = (of_nat (Suc n) * (f (Suc n) u * (z-u) ^ n)) +
                         (f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)) -
                         (f (Suc n) u * ((1 + of_nat n) * (z-u) ^ n))"
          by (simp only: fact_Suc of_nat_mult ac_simps) simp
        also have "... = f (Suc (Suc n)) u * ((z-u) * (z-u) ^ n)"
          by (simp add: algebra_simps)
        finally show ?thesis
        by (simp add: mult_left_cancel [where c = "(fact (Suc n))", THEN iffD1] del: fact_Suc)
      qed
      finally show ?case .
    qed
    then have "((\<lambda>v. (\<Sum>i\<le>n. f i v * (z - v)^i / (fact i)))
                has_field_derivative f (Suc n) u * (z-u) ^ n / (fact n))
               (at u within s)"
      apply (intro derivative_eq_intros)
      apply (blast intro: assms \<open>u \<in> s\<close>)
      apply (rule refl)+
      apply (auto simp: field_simps)
      done
  } note sum_deriv = this
  { fix u
    assume u: "u \<in> closed_segment w z"
    then have us: "u \<in> s"
      by (metis wzs subsetD)
    have "norm (f (Suc n) u) * norm (z - u) ^ n \<le> norm (f (Suc n) u) * norm (u - z) ^ n"
      by (metis norm_minus_commute order_refl)
    also have "... \<le> norm (f (Suc n) u) * norm (z - w) ^ n"
      by (metis mult_left_mono norm_ge_zero power_mono segment_bound [OF u])
    also have "... \<le> B * norm (z - w) ^ n"
      by (metis norm_ge_zero zero_le_power mult_right_mono  B [OF us])
    finally have "norm (f (Suc n) u) * norm (z - u) ^ n \<le> B * norm (z - w) ^ n" .
  } note cmod_bound = this
  have "(\<Sum>i\<le>n. f i z * (z - z) ^ i / (fact i)) = (\<Sum>i\<le>n. (f i z / (fact i)) * 0 ^ i)"
    by simp
  also have "\<dots> = f 0 z / (fact 0)"
    by (subst sum_zero_power) simp
  finally have "norm (f 0 z - (\<Sum>i\<le>n. f i w * (z - w) ^ i / (fact i)))
                \<le> norm ((\<Sum>i\<le>n. f i w * (z - w) ^ i / (fact i)) -
                        (\<Sum>i\<le>n. f i z * (z - z) ^ i / (fact i)))"
    by (simp add: norm_minus_commute)
  also have "... \<le> B * norm (z - w) ^ n / (fact n) * norm (w - z)"
    apply (rule field_differentiable_bound
      [where f' = "\<lambda>w. f (Suc n) w * (z - w)^n / (fact n)"
         and s = "closed_segment w z", OF convex_closed_segment])
    apply (auto simp: ends_in_segment DERIV_subset [OF sum_deriv wzs]
                  norm_divide norm_mult norm_power divide_le_cancel cmod_bound)
    done
  also have "...  \<le> B * norm (z - w) ^ Suc n / (fact n)"
    by (simp add: algebra_simps norm_minus_commute)
  finally show ?thesis .
qed

lemma Taylor_exp:\<comment> \<open>TODO: generalize @{thm Taylor_exp}\<close>
  fixes z::"'a::{banach,real_normed_field}"
  shows "norm (exp z - (\<Sum>i\<le>n. z ^ i / fact i)) \<le> exp (norm z) * (norm z * norm z ^ n) / fact n"
proof (rule field_Taylor[of _ n "\<lambda>k. exp" "exp (norm z)" 0 z, simplified])
  show "convex (closed_segment 0 z)"
    by (rule convex_closed_segment [of 0 z])
next
  fix k x
  assume "x \<in> closed_segment 0 z" "k \<le> n"
  show "(exp has_field_derivative exp x) (at x within closed_segment 0 z)"
    using DERIV_exp DERIV_subset by blast
next
  fix x
  assume x: "x \<in> closed_segment 0 z"
  have "norm (exp x) \<le> exp (norm x)"
    by (rule norm_exp)
  also have "norm x \<le> norm z"
    using x by (auto simp: closed_segment_def intro!: mult_left_le_one_le)
  finally show "norm (exp x) \<le> exp (norm z)"
    by simp
next
  show "0 \<in> closed_segment 0 z"
    by (auto simp: closed_segment_def)
next
  show "z \<in> closed_segment 0 z"
    apply (simp add: closed_segment_def scaleR_conv_of_real)
    using of_real_1 zero_le_one by blast
qed

lemma norm_blinop_componentwise:
  fixes A::"'a::euclidean_space blinop"
  shows "norm A \<le> (\<Sum>i\<in>Basis. norm (A i))"
  apply transfer
  including blinfun.lifting
  apply transfer
  apply (rule onorm_componentwise, assumption)
  done

end
