(* Author: Andreas Lochbihler, ETH Zurich *)

section \<open>Examples of applicative lifting\<close>

subsection \<open>Algebraic operations for the environment functor\<close>

theory Applicative_Environment_Algebra imports
  Applicative_Environment
  "HOL-Library.Function_Division"
begin

text \<open> Link between applicative instance of the environment functor with the pointwise operations
  for the algebraic type classes \<close>

context includes applicative_syntax
begin

lemma plus_fun_af [applicative_unfold]: "f + g = pure (+) \<diamondop> f \<diamondop> g"
unfolding plus_fun_def const_def apf_def ..

lemma zero_fun_af [applicative_unfold]: "0 = pure 0"
unfolding zero_fun_def const_def ..

lemma times_fun_af [applicative_unfold]: "f * g = pure (*) \<diamondop> f \<diamondop> g"
unfolding times_fun_def const_def apf_def ..

lemma one_fun_af [applicative_unfold]: "1 = pure 1"
unfolding one_fun_def const_def ..

lemma of_nat_fun_af [applicative_unfold]: "of_nat n = pure (of_nat n)"
unfolding of_nat_fun const_def ..

lemma inverse_fun_af [applicative_unfold]: "inverse f = pure inverse \<diamondop> f"
unfolding inverse_fun_def o_def const_def apf_def ..

lemma divide_fun_af [applicative_unfold]: "divide f g = pure divide \<diamondop> f \<diamondop> g"
unfolding divide_fun_def const_def apf_def ..

end

end
