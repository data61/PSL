section\<open>Lemmas possibly destined for future Isabelle releases\<close>

theory Fourier_Aux2
  imports "HOL-Analysis.Analysis" 
begin
    
lemma integral_sin_Z [simp]:
  assumes "n \<in> \<int>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin(x * n)) = 0"
  proof (subst lebesgue_integral_eq_integral)
  show "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. sin (x * n))"
    by (intro continuous_imp_integrable_real continuous_intros)
  show "integral {-pi..pi} (\<lambda>x. sin (x * n)) = 0"
    using assms Ints_cases integral_sin_nx by blast
qed auto

lemma integral_sin_Z' [simp]:
  assumes "n \<in> \<int>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. sin(n * x)) = 0"
  by (metis assms integral_sin_Z mult_commute_abs)
    
lemma integral_cos_Z [simp]:
  assumes "n \<in> \<int>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(x * n)) = (if n = 0 then 2 * pi else 0)"
  proof (subst lebesgue_integral_eq_integral)
  show "integrable (lebesgue_on {-pi..pi}) (\<lambda>x. cos (x * n))"
    by (intro continuous_imp_integrable_real continuous_intros)
  show "integral {-pi..pi} (\<lambda>x. cos (x * n)) = (if n = 0 then 2 * pi else 0)"
    by (metis Ints_cases assms integral_cos_nx of_int_0_eq_iff)
qed auto

lemma integral_cos_Z' [simp]:
  assumes "n \<in> \<int>"
  shows "integral\<^sup>L (lebesgue_on {-pi..pi}) (\<lambda>x. cos(n * x)) = (if n = 0 then 2 * pi else 0)"
  by (metis assms integral_cos_Z mult_commute_abs)

lemma odd_even_cases [case_names 0 odd even]:
  assumes "P 0" and odd: "\<And>n. P(Suc (2 * n))" and even: "\<And>n. P(2 * n + 2)"
  shows "P n"
  by (metis nat_induct2 One_nat_def Suc_1 add_Suc_right assms(1) dvdE even odd oddE)

end
