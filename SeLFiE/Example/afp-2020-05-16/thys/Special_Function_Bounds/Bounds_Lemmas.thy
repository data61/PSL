chapter \<open>General Lemmas for Proving Function Inequalities\<close>

theory Bounds_Lemmas
imports Complex_Main

begin

text\<open>These are for functions that are differentiable over a closed interval.\<close>

lemma gen_lower_bound_increasing:
  fixes a :: real
  assumes "a \<le> x"
      and "\<And>y. a \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> ((\<lambda>x. fl x - f x) has_real_derivative g y) (at y)"
      and "\<And>y. a \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> g y \<le> 0"
      and "fl a = f a"
    shows "fl x \<le> f x"
proof -
  have "fl x - f x \<le> fl a - f a"
    apply (rule DERIV_nonpos_imp_nonincreasing [where f = "\<lambda>x. fl x - f x"])
    apply (rule assms)
    apply (intro allI impI exI conjI)
    apply (rule assms | simp)+
    done
  also have "... = 0"
    by (simp add: assms)
  finally show ?thesis
    by simp
qed

lemma gen_lower_bound_decreasing:
  fixes a :: real
  assumes "x \<le> a"
      and "\<And>y. x \<le> y \<Longrightarrow> y \<le> a \<Longrightarrow> ((\<lambda>x. fl x - f x) has_real_derivative g y) (at y)"
      and "\<And>y. x \<le> y \<Longrightarrow> y \<le> a \<Longrightarrow> g y \<ge> 0"
      and "fl a = f a"
    shows "fl x \<le> f x"
proof -
  have "fl (- (-x)) \<le> f (- (-x))"
    apply (rule gen_lower_bound_increasing [of "-a" "-x" _ _ "\<lambda>u. - g (-u)"])
    apply (auto simp: assms)
    apply (subst DERIV_mirror [symmetric])
    apply (simp add: assms)
    done
  then show ?thesis
    by simp
qed

lemma gen_upper_bound_increasing:
  fixes a :: real
  assumes "a \<le> x"
      and "\<And>y. a \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> ((\<lambda>x. fu x - f x) has_real_derivative g y) (at y)"
      and "\<And>y. a \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> g y \<ge> 0"
      and "fu a = f a"
    shows "f x \<le> fu x"
apply (rule gen_lower_bound_increasing [of a x f fu  "\<lambda>u. - g u"])
using assms DERIV_minus [where f = "\<lambda>x. fu x - f x"]
apply auto
done

lemma gen_upper_bound_decreasing:
  fixes a :: real
  assumes "x \<le> a"
      and "\<And>y. x \<le> y \<Longrightarrow> y \<le> a \<Longrightarrow> ((\<lambda>x. fu x - f x) has_real_derivative g y) (at y)"
      and "\<And>y. x \<le> y \<Longrightarrow> y \<le> a \<Longrightarrow> g y \<le> 0"
      and "fu a = f a"
    shows "f x \<le> fu x"
apply (rule gen_lower_bound_decreasing [of x a _ _  "\<lambda>u. - g u"])
using assms DERIV_minus [where f = "\<lambda>x. fu x - f x"]
apply auto
done

end

