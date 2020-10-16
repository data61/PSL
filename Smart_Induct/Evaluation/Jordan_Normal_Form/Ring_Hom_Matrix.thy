(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Matrix Conversions\<close>

text \<open>Essentially, the idea is to use the JNF results to estimate the growth rates of 
  matrices. Since the results in JNF are only applicable for real normed fields,
  we cannot directly use them for matrices over the integers or the rational numbers.
  To this end, we define a homomorphism which allows us to first convert all numbers
  to real numbers, and then do the analysis.\<close>

theory Ring_Hom_Matrix
imports 
  Matrix
  Polynomial_Interpolation.Ring_Hom
begin

locale ord_ring_hom = idom_hom hom for 
  hom :: "'a :: linordered_idom \<Rightarrow> 'b :: floor_ceiling" +
  assumes hom_le: "hom x \<le> z \<Longrightarrow> x \<le> of_int \<lceil>z\<rceil>"

text \<open>Now a class based variant especially for homomorphisms into the reals.\<close>
class real_embedding = linordered_idom + 
  fixes real_of :: "'a \<Rightarrow> real"
  assumes
    real_add: "real_of ((x :: 'a) + y) = real_of x + real_of y" and
    real_mult: "real_of (x * y) = real_of x * real_of y" and
    real_zero: "real_of 0 = 0" and
    real_one: "real_of 1 = 1" and
    real_le: "real_of x \<le> z \<Longrightarrow> x \<le> of_int \<lceil>z\<rceil>"

interpretation real_embedding: ord_ring_hom "(real_of :: 'a :: real_embedding \<Rightarrow> real)"
  by (unfold_locales; fact real_add real_mult real_zero real_one real_le)

instantiation real :: real_embedding
begin
definition real_of_real :: "real \<Rightarrow> real" where
  "real_of_real x = x"

instance
  by (intro_classes, auto simp: real_of_real_def, linarith)
end

instantiation int :: real_embedding
begin

definition real_of_int :: "int \<Rightarrow> real" where
  "real_of_int x = x"

instance
  by (intro_classes, auto simp: real_of_int_def, linarith)
end

lemma real_of_rat_ineq: assumes "real_of_rat x \<le> z"
  shows "x \<le> of_int \<lceil>z\<rceil>"
proof -
  have "z \<le> of_int \<lceil>z\<rceil>" by linarith
  from order_trans[OF assms this] 
  have "real_of_rat x \<le> real_of_rat (of_int \<lceil>z\<rceil>)" by auto
  thus "x \<le> of_int \<lceil>z\<rceil>" using of_rat_less_eq by blast
qed

instantiation rat :: real_embedding
begin
definition real_of_rat :: "rat \<Rightarrow> real" where
  "real_of_rat x = of_rat x"

instance
  by (intro_classes, auto simp: real_of_rat_def of_rat_add of_rat_mult real_of_rat_ineq)
end

abbreviation mat_real ("mat\<^sub>\<real>") where "mat\<^sub>\<real> \<equiv> map_mat (real_of :: 'a :: real_embedding \<Rightarrow> real)"

end
