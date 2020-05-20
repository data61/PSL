(* Author: Andreas Lochbihler, ETH Zurich *)

theory Applicative_Vector imports
  Applicative
  "HOL-Analysis.Finite_Cartesian_Product"
  "HOL-Library.Adhoc_Overloading"
begin

definition pure_vec :: "'a \<Rightarrow> ('a, 'b :: finite) vec"
where "pure_vec x = (\<chi> _ . x)"

definition ap_vec :: "('a \<Rightarrow> 'b, 'c :: finite) vec \<Rightarrow> ('a, 'c) vec \<Rightarrow> ('b, 'c) vec"
where "ap_vec f x = (\<chi> i. (f $ i) (x $ i))"

adhoc_overloading Applicative.ap ap_vec

applicative vec (K, W)
for
  pure: pure_vec
  ap: ap_vec
by(auto simp add: pure_vec_def ap_vec_def vec_nth_inverse)

lemma pure_vec_nth [simp]: "pure_vec x $ i = x"
by(simp add: pure_vec_def)

lemma ap_vec_nth [simp]: "ap_vec f x $ i  = (f $ i) (x $ i)"
by(simp add: ap_vec_def)

end
