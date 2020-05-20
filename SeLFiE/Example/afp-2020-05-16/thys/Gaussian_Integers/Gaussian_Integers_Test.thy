(*
  File:     Gaussian_Integers_Test.thy
  Author:   Manuel Eberl, TU München

  Test of code generation for executable factorisation algorithm for Gaussian integers
*)
theory Gaussian_Integers_Test
imports
  Gaussian_Integers
  "Polynomial_Factorization.Prime_Factorization"
  "HOL-Library.Code_Target_Numeral"
begin

text \<open>
  Lastly, we apply our factorisation algorithm to some simple examples:
\<close>

(*<*)
context
  includes gauss_int_notation
begin
(*>*)

value "(1234 + 5678 * \<i>\<^sub>\<int>) mod (321 + 654 * \<i>\<^sub>\<int>)"
value "prime_factors (1 + 3 * \<i>\<^sub>\<int>)"
value "prime_factors (4830 + 1610 * \<i>\<^sub>\<int>)"

(*<*)
end
(*>*)

end