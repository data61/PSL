(*
  File:    Pochhammer_Polynomials.thy
  Author:  Manuel Eberl, TU München
*)
section \<open>Falling factorial as a polynomial\<close>
theory Pochhammer_Polynomials
imports
  Complex_Main
  "HOL-Library.Stirling" 
  "HOL-Computational_Algebra.Polynomial" 
begin

definition pochhammer_poly :: "nat \<Rightarrow> 'a :: {comm_semiring_1} poly" where
  "pochhammer_poly n = Poly [of_nat (stirling n k). k \<leftarrow> [0..<Suc n]]"

lemma pochhammer_poly_code [code abstract]:
  "coeffs (pochhammer_poly n) = map of_nat (stirling_row n)"
  by (simp add: pochhammer_poly_def stirling_row_def Let_def)

lemma coeff_pochhammer_poly: "coeff (pochhammer_poly n) k = of_nat (stirling n k)"
  by (simp add: pochhammer_poly_def nth_default_def del: upt_Suc)

lemma degree_pochhammer_poly [simp]: "degree (pochhammer_poly n) = n"
  by (simp add: degree_eq_length_coeffs pochhammer_poly_def)

lemma pochhammer_poly_0 [simp]: "pochhammer_poly 0 = 1"
  by (simp add: pochhammer_poly_def)

lemma pochhammer_poly_Suc: "pochhammer_poly (Suc n) = [:of_nat n,1:] * pochhammer_poly n"
  by (cases "n = 0") (simp_all add: poly_eq_iff coeff_pochhammer_poly coeff_pCons split: nat.split)

lemma pochhammer_poly_altdef: "pochhammer_poly n = (\<Prod>i<n. [:of_nat i,1:])"
  by (induction n) (simp_all add: pochhammer_poly_Suc)

lemma eval_pochhammer_poly: "poly (pochhammer_poly n) k = pochhammer k n"
  by (cases n) (auto simp add: pochhammer_poly_altdef poly_prod add_ac lessThan_Suc_atMost 
                               pochhammer_Suc_prod atLeast0AtMost)

lemma pochhammer_poly_Suc':
    "pochhammer_poly (Suc n) = pCons 0 (pcompose (pochhammer_poly n) [:1,1:])"
  by (simp add: pochhammer_poly_altdef prod.lessThan_Suc_shift pcompose_prod pcompose_pCons add_ac del: prod.lessThan_Suc)
 
end
