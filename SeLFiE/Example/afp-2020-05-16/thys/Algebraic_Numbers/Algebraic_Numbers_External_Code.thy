(*  
    Author:      René Thiemann 
    License:     BSD
*)
section \<open>Explicit Constants for External Code\<close>

theory Algebraic_Numbers_External_Code
  imports Algebraic_Number_Tests
begin

text \<open>We define constants for most operations on real- and complex- algebraic numbers, so that
  they are easily accessible in target languages. In particular, we use target languages 
  integers, pairs of integers, strings, and integer lists, resp., 
  in order to represent the Isabelle types @{typ int}/@{typ nat}, @{typ rat}, @{typ string},
  and @{typ "int poly"}, resp.\<close>

definition "decompose_rat = map_prod integer_of_int integer_of_int o quotient_of" 

subsection \<open>Operations on Real Algebraic Numbers\<close>

definition "zero_ra = (0 :: real_alg)"
definition "one_ra = (1 :: real_alg)" 
definition "of_integer_ra = (of_int o int_of_integer :: integer \<Rightarrow> real_alg)" 
definition "of_rational_ra = ((\<lambda> (num, denom). of_rat_real_alg (Rat.Fract (int_of_integer num) (int_of_integer denom))) 
  :: integer \<times> integer \<Rightarrow> real_alg)" 
definition "plus_ra = ((+) :: real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg)" 
definition "minus_ra = ((-) :: real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg)" 
definition "uminus_ra = (uminus :: real_alg \<Rightarrow> real_alg)" 
definition "times_ra = ((*) :: real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg)"
definition "divide_ra = ((/) :: real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg)"
definition "inverse_ra = (inverse :: real_alg \<Rightarrow> real_alg)"
definition "abs_ra = (abs :: real_alg \<Rightarrow> real_alg)"
definition "floor_ra = (integer_of_int o floor :: real_alg \<Rightarrow> integer)"
definition "ceiling_ra = (integer_of_int o ceiling :: real_alg \<Rightarrow> integer)"
definition "minimum_ra = (min :: real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg)"
definition "maximum_ra = (max :: real_alg \<Rightarrow> real_alg \<Rightarrow> real_alg)"
definition "equals_ra = ((=) :: real_alg \<Rightarrow> real_alg \<Rightarrow> bool)"
definition "less_ra = ((<) :: real_alg \<Rightarrow> real_alg \<Rightarrow> bool)"
definition "less_equal_ra = ((\<le>) :: real_alg \<Rightarrow> real_alg \<Rightarrow> bool)"
definition "compare_ra = (compare :: real_alg \<Rightarrow> real_alg \<Rightarrow> order)"
definition "roots_of_poly_ra = (roots_of_real_alg o poly_of_list o map int_of_integer :: integer list \<Rightarrow> real_alg list)" 
definition "root_ra = (root_real_alg o nat_of_integer :: integer \<Rightarrow> real_alg \<Rightarrow> real_alg)" 
definition "show_ra = ((String.implode o show) :: real_alg \<Rightarrow> String.literal)" 
definition "is_rational_ra = (is_rat_real_alg :: real_alg \<Rightarrow> bool)" 
definition "to_rational_ra = (decompose_rat o to_rat_real_alg :: real_alg \<Rightarrow> integer \<times> integer)" 
definition "sign_ra = (fst o to_rational_ra o sgn :: real_alg \<Rightarrow> integer)" 
definition "decompose_ra = (map_sum decompose_rat (map_prod (map integer_of_int o coeffs) integer_of_nat) o info_real_alg
  :: real_alg \<Rightarrow> integer \<times> integer + integer list \<times> integer)" 


subsection \<open>Operations on Complex Algebraic Numbers\<close>

definition "zero_ca = (0 :: complex)" 
definition "one_ca = (1 :: complex)" 
definition "imag_unit_ca = (\<i> :: complex)" 
definition "of_integer_ca = (of_int o int_of_integer :: integer \<Rightarrow> complex)" 
definition "of_rational_ca = ((\<lambda> (num, denom). of_rat (Rat.Fract (int_of_integer num) (int_of_integer denom))) 
  :: integer \<times> integer \<Rightarrow> complex)" 
definition "of_real_imag_ca = ((\<lambda> (real, imag). Complex (real_of real) (real_of imag)) :: real_alg \<times> real_alg \<Rightarrow> complex)" 
definition "plus_ca = ((+) :: complex \<Rightarrow> complex \<Rightarrow> complex)" 
definition "minus_ca = ((-) :: complex \<Rightarrow> complex \<Rightarrow> complex)" 
definition "uminus_ca = (uminus :: complex \<Rightarrow> complex)" 
definition "times_ca = ((*) :: complex \<Rightarrow> complex \<Rightarrow> complex)"
definition "divide_ca = ((/) :: complex \<Rightarrow> complex \<Rightarrow> complex)"
definition "inverse_ca = (inverse :: complex \<Rightarrow> complex)"
definition "equals_ca = ((=) :: complex \<Rightarrow> complex \<Rightarrow> bool)"
definition "roots_of_poly_ca = (complex_roots_of_int_poly o poly_of_list o map int_of_integer :: integer list \<Rightarrow> complex list)" 
definition "csqrt_ca = (csqrt :: complex \<Rightarrow> complex)" 
definition "show_ca = ((String.implode o show) :: complex \<Rightarrow> String.literal)" 
definition "real_of_ca = (real_alg_of_real o Re :: complex \<Rightarrow> real_alg)" 
definition "imag_of_ca = (real_alg_of_real o Im :: complex \<Rightarrow> real_alg)" 

subsection \<open>Export Constants in Haskell\<close>

export_code 
  (* preliminary operations *)
  order.Eq order.Lt order.Gt \<comment> \<open>for comparison\<close>
  Inl Inr \<comment> \<open>make disjoint sums available for decomposition information\<close>

  (* real algebraic operations *)
  zero_ra
  one_ra
  of_integer_ra
  of_rational_ra
  plus_ra
  minus_ra
  uminus_ra
  times_ra
  divide_ra
  inverse_ra
  abs_ra
  floor_ra
  ceiling_ra
  minimum_ra
  maximum_ra
  equals_ra
  less_ra
  less_equal_ra
  compare_ra  
  roots_of_poly_ra
  root_ra
  show_ra
  is_rational_ra
  to_rational_ra
  sign_ra
  decompose_ra

  (* complex algebraic operations *)
  zero_ca
  one_ca
  imag_unit_ca
  of_integer_ca
  of_rational_ca
  of_real_imag_ca
  plus_ca
  minus_ca
  uminus_ca
  times_ca
  divide_ca
  inverse_ca
  equals_ca
  roots_of_poly_ca
  csqrt_ca
  show_ca
  real_of_ca
  imag_of_ca
  
in Haskell module_name Algebraic_Numbers (* file \<open>~/Code/Algebraic_Numbers\<close> *)

end
