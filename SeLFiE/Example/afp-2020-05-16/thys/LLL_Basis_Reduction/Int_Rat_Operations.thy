(*
    Authors:    René Thiemann
    License:    BSD
*)
section \<open>Optimized Code for Integer-Rational Operations\<close>

theory Int_Rat_Operations
imports 
  Sqrt_Babylonian.Sqrt_Babylonian_Auxiliary
  Norms
begin

definition int_times_rat :: "int \<Rightarrow> rat \<Rightarrow> rat" where "int_times_rat i x = of_int i * x" 

declare int_times_rat_def[simp]

lemma int_times_rat_code[code abstract]: "quotient_of (int_times_rat i x) =
  (case quotient_of x of (n,d) \<Rightarrow> Rat.normalize (i * n, d))"  
  unfolding int_times_rat_def rat_times_code by auto

definition square_rat :: "rat \<Rightarrow> rat" where [simp]: "square_rat x = x * x" 

lemma quotient_of_square: assumes "quotient_of x = (a,b)"
  shows "quotient_of (x * x) = (a * a, b * b)"
proof -
  have b0: "b > 0" "b \<noteq> 0" using quotient_of_denom_pos[OF assms] by auto
  hence b: "(b * b > 0) = True" by auto
  show ?thesis
    unfolding rat_times_code assms Let_def split Rat.normalize_def fst_conv snd_conv b if_True
    using quotient_of_coprime[OF assms] b0 by simp
qed

lemma square_rat_code[code abstract]: "quotient_of (square_rat x) = (case quotient_of x of (n,d)
  \<Rightarrow> (n * n, d * d))" using quotient_of_square[of x] unfolding square_rat_def 
  by (cases "quotient_of x", auto)


definition scalar_prod_int_rat :: "int vec \<Rightarrow> rat vec \<Rightarrow> rat" (infix "\<bullet>i" 70) where
  "x \<bullet>i y = (y \<bullet> map_vec rat_of_int x)"

lemma scalar_prod_int_rat_code[code]: "v \<bullet>i w = (\<Sum>i = 0..<dim_vec v. int_times_rat (v $ i) (w $ i))"  
  unfolding scalar_prod_int_rat_def Let_def scalar_prod_def int_times_rat_def
  by (rule sum.cong, auto)

lemma scalar_prod_int_rat[simp]: "dim_vec x = dim_vec y \<Longrightarrow> x \<bullet>i y = map_vec of_int x \<bullet> y" 
  unfolding scalar_prod_int_rat_def by (intro comm_scalar_prod[of _ "dim_vec x"], auto intro: carrier_vecI) 

definition sq_norm_vec_rat :: "rat vec \<Rightarrow> rat" where [simp]: "sq_norm_vec_rat x = sq_norm_vec x" 

lemma sq_norm_vec_rat_code[code]: "sq_norm_vec_rat x = (\<Sum>x\<leftarrow>list_of_vec x. square_rat x)" 
  unfolding sq_norm_vec_rat_def sq_norm_vec_def square_rat_def by auto

end
