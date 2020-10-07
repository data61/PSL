(*  Title:       Computing Square Roots using the Babylonian Method
    Author:      René Thiemann       <rene.thiemann@uibk.ac.at>
    Maintainer:  René Thiemann
    License:     LGPL
*)

(*
Copyright 2009-2014 René Thiemann

This file is part of IsaFoR/CeTA.

IsaFoR/CeTA is free software: you can redistribute it and/or modify it under the
terms of the GNU Lesser General Public License as published by the Free Software
Foundation, either version 3 of the License, or (at your option) any later
version.

IsaFoR/CeTA is distributed in the hope that it will be useful, but WITHOUT ANY
WARRANTY; without even the implied warranty of MERCHANTABILITY or FITNESS FOR A
PARTICULAR PURPOSE.  See the GNU Lesser General Public License for more details.

You should have received a copy of the GNU Lesser General Public License along
with IsaFoR/CeTA. If not, see <http://www.gnu.org/licenses/>.
*)
section \<open>Auxiliary lemmas which might be moved into the Isabelle distribution.\<close>

theory Sqrt_Babylonian_Auxiliary
imports 
  Complex_Main
begin

lemma mod_div_equality_int: "(n :: int) div x * x = n - n mod x"
  using div_mult_mod_eq[of n x] by arith

lemma log_pow_cancel[simp]: "a > 0 \<Longrightarrow> a \<noteq> 1 \<Longrightarrow> log a (a ^ b) = b" 
  by (metis monoid_mult_class.mult.right_neutral log_eq_one log_nat_power)

lemma real_of_rat_floor[simp]: "floor (real_of_rat x) = floor x"
  by (metis Ratreal_def real_floor_code)

lemma abs_of_rat[simp]: "\<bar>real_of_rat x\<bar> = real_of_rat \<bar>x\<bar>" 
proof (cases "x \<ge> 0")
  case False
  define y where "y = - x"
  from False have y: "y \<ge> 0" "x = - y" by (auto simp: y_def)
  thus ?thesis by (auto simp: of_rat_minus)
qed auto

lemma real_of_rat_ceiling[simp]: "ceiling (real_of_rat x) = ceiling x"
  unfolding ceiling_def by (metis of_rat_minus real_of_rat_floor)

lemma div_is_floor_divide_rat: "n div y = \<lfloor>rat_of_int n / rat_of_int y\<rfloor>"
  unfolding Fract_of_int_quotient[symmetric] floor_Fract by simp

lemma div_is_floor_divide_real: "n div y = \<lfloor>real_of_int n / of_int y\<rfloor>"
  unfolding div_is_floor_divide_rat[of n y]
  by (metis Ratreal_def of_rat_divide of_rat_of_int_eq real_floor_code)

lemma floor_div_pos_int: 
  fixes r :: "'a :: floor_ceiling"
  assumes n: "n > 0" 
  shows "\<lfloor>r / of_int n\<rfloor> = \<lfloor>r\<rfloor> div n" (is "?l = ?r")
proof -
  let ?of_int = "of_int :: int \<Rightarrow> 'a"
  define rhs where "rhs = \<lfloor>r\<rfloor> div n"
  let ?n = "?of_int n"
  define m where "m = \<lfloor>r\<rfloor> mod n"
  let ?m = "?of_int m"
  from div_mult_mod_eq[of "floor r" n] have dm: "rhs * n + m = \<lfloor>r\<rfloor>" unfolding rhs_def m_def by simp
  have mn: "m < n" and m0: "m \<ge> 0" using n m_def by auto
  define e where "e = r - ?of_int \<lfloor>r\<rfloor>"
  have e0: "e \<ge> 0" unfolding e_def 
    by (metis diff_self eq_iff floor_diff_of_int zero_le_floor)
  have e1: "e < 1" unfolding e_def 
    by (metis diff_self dual_order.refl floor_diff_of_int floor_le_zero)
  have "r = ?of_int \<lfloor>r\<rfloor> + e" unfolding e_def by simp
  also have "\<lfloor>r\<rfloor> = rhs * n + m" using dm by simp
  finally have "r = ?of_int (rhs * n + m) + e" .
  hence "r / ?n = ?of_int (rhs * n) / ?n + (e + ?m) / ?n" using n by (simp add: field_simps)
  also have "?of_int (rhs * n) / ?n = ?of_int rhs" using n by auto
  finally have *: "r / ?of_int n = (e + ?of_int m) / ?of_int n + ?of_int rhs" by simp
  have "?l = rhs + floor ((e + ?m) / ?n)" unfolding * by simp
  also have "floor ((e + ?m) / ?n) = 0"
  proof (rule floor_unique)
    show "?of_int 0 \<le> (e + ?m) / ?n" using e0 m0 n 
      by (metis add_increasing2 divide_nonneg_pos of_int_0 of_int_0_le_iff of_int_0_less_iff)
    show "(e + ?m) / ?n < ?of_int 0 + 1"
    proof (rule ccontr)
      from n have n': "?n > 0" "?n \<ge> 0" by simp_all
      assume "\<not> ?thesis"
      hence "(e + ?m) / ?n \<ge> 1" by auto
      from mult_right_mono[OF this n'(2)]
      have "?n \<le> e + ?m" using n'(1) by simp
      also have "?m \<le> ?n - 1" using mn 
        by (metis of_int_1 of_int_diff of_int_le_iff zle_diff1_eq)
      finally have "?n \<le> e + ?n - 1" by auto
      with e1 show False by arith
    qed
  qed
  finally show ?thesis unfolding rhs_def by simp
qed


lemma floor_div_neg_int: 
  fixes r :: "'a :: floor_ceiling"
  assumes n: "n < 0" 
  shows "\<lfloor>r / of_int n\<rfloor> = \<lceil>r\<rceil> div n"
proof -
  from n have n': "- n > 0" by auto
  have "\<lfloor>r / of_int n\<rfloor> = \<lfloor> - r / of_int (- n)\<rfloor>" using n
    by (metis floor_of_int floor_zero less_int_code(1) minus_divide_left minus_minus nonzero_minus_divide_right of_int_minus)
  also have "\<dots> = \<lfloor> - r \<rfloor> div (- n)" by (rule floor_div_pos_int[OF n'])
  also have "\<dots> = \<lceil> r \<rceil> div n" using n 
  by (metis ceiling_def div_minus_right)
  finally show ?thesis .
qed

lemma divide_less_floor1: "n / y < of_int (floor (n / y)) + 1" 
  by (metis floor_less_iff less_add_one of_int_1 of_int_add)

context linordered_idom
begin

lemma sgn_int_pow_if [simp]:
  "sgn x ^ p = (if even p then 1 else sgn x)" if "x \<noteq> 0"
  using that by (induct p) simp_all

lemma compare_pow_le_iff: "p > 0 \<Longrightarrow> (x :: 'a) \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> (x ^ p \<le> y ^ p) = (x \<le> y)"
  by (metis eq_iff linear power_eq_imp_eq_base power_mono)

lemma compare_pow_less_iff: "p > 0 \<Longrightarrow> (x :: 'a) \<ge> 0 \<Longrightarrow> y \<ge> 0 \<Longrightarrow> (x ^ p < y ^ p) = (x < y)"
  by (metis power_less_imp_less_base power_strict_mono)
    
end

lemma quotient_of_int[simp]: "quotient_of (of_int i) = (i,1)" 
  by (metis Rat.of_int_def quotient_of_int)

lemma quotient_of_nat[simp]: "quotient_of (of_nat i) = (int i,1)" 
  by (metis Rat.of_int_def Rat.quotient_of_int of_int_of_nat_eq)

lemma square_lesseq_square: "\<And> x y. 0 \<le> (x :: 'a :: linordered_field) \<Longrightarrow> 0 \<le> y \<Longrightarrow> (x * x \<le> y * y) = (x \<le> y)"
  by (metis mult_mono mult_strict_mono' not_less)

lemma square_less_square: "\<And> x y. 0 \<le> (x :: 'a :: linordered_field) \<Longrightarrow> 0 \<le> y \<Longrightarrow> (x * x < y * y) = (x < y)"
  by (metis mult_mono mult_strict_mono' not_less)

lemma sqrt_sqrt[simp]: "x \<ge> 0 \<Longrightarrow> sqrt x * sqrt x = x"
  by (metis real_sqrt_pow2 power2_eq_square)

lemma abs_lesseq_square: "abs (x :: real) \<le> abs y \<longleftrightarrow> x * x \<le> y * y"
  using square_lesseq_square[of "abs x" "abs y"] by auto

end
