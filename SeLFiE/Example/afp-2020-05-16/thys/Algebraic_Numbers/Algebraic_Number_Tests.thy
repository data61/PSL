(*  
    Author:      René Thiemann 
                 Akihisa Yamada
    License:     BSD
*)
section \<open>Algebraic Number Tests\<close>

text \<open>We provide a sequence of examples which demonstrate what can be done with 
  the implementation of algebraic numbers.\<close>

theory Algebraic_Number_Tests
imports
  Jordan_Normal_Form.Char_Poly
  Jordan_Normal_Form.Determinant_Impl
  Show.Show_Complex
  "HOL-Library.Code_Target_Nat"
  "HOL-Library.Code_Target_Int"
  Berlekamp_Zassenhaus.Factorize_Rat_Poly 
  Real_Factorization
  Show_Real_Precise  
begin

subsection \<open>Stand-Alone Examples\<close>

abbreviation (input) "show_lines x \<equiv> shows_lines x Nil"

fun show_factorization :: "'a :: {semiring_1,show} \<times> (('a poly \<times> nat)list) \<Rightarrow> string" where
  "show_factorization (c,[]) = show c" 
| "show_factorization (c,((p,i) # ps)) = show_factorization (c,ps) @ '' * ('' @ show p @ '')'' @
  (if i = 1 then [] else ''^'' @ show i)"

definition show_sf_factorization :: "'a :: {semiring_1,show} \<times> (('a poly \<times> nat)list) \<Rightarrow> string" where
  "show_sf_factorization x = show_factorization (map_prod id (map (map_prod id Suc)) x)
     " 

text \<open>Determine the roots over the rational, real, and complex numbers.\<close>

definition "testpoly = [:5/2, -7/2, 1/2, -5, 7, -1, 5/2, -7/2, 1/2:]"
definition "test = show_lines (   real_roots_of_rat_poly testpoly)"

value [code] "show_lines (        roots_of_rat_poly testpoly)"
value [code] "show_lines (   real_roots_of_rat_poly testpoly)"
value [code] "show_lines (complex_roots_of_rat_poly testpoly)"


text \<open>Factorize polynomials over the rational, real, and complex numbers.\<close>

value [code] "show_sf_factorization (factorize_rat_poly testpoly)" 
value [code] "show_factorization (the (factorize_real_poly testpoly))"
value [code] "show_factorization (the (factorize_complex_poly testpoly))"

text \<open>If the input is not a rational polynomial, factorization can fail.\<close>

value [code] "factorize_real_poly [:sqrt 2,1,3,1:]" text \<open>fails\\\<close>
value [code] "factorize_real_poly [:sqrt 2,1,3:]" text \<open>does not fail, reveals internal representation\\\<close>
value [code] "show (factorize_real_poly [:sqrt 2,1,3:])" text \<open>does not fail, pretty printed\<close>


text \<open>A sequence of calculations.\<close>

value [code] "show (- sqrt 2 - sqrt 3)"
lemma "root 3 4 > sqrt (root 4 3) + \<lfloor>1/10 * root 3 7\<rfloor>" by eval
lemma "csqrt (4 + 3 * \<i>) \<notin> \<real>" by eval
value [code] "show (csqrt (4 + 3 * \<i>))"
value [code] "show (csqrt (1 + \<i>))"

subsection \<open>Example Application: Compute Norms of Eigenvalues\<close>

text \<open>For complexity analysis of some matrix $A$ it is important to compute the spectral
  radius of a matrix, i.e., the maximal norm of all complex eigenvalues, 
  since the spectral radius determines
  the growth rates of matrix-powers $A^n$, cf.~\cite{JNF-AFP} for a formalized statement
  of this fact.\<close>

definition eigenvalues :: "rat mat \<Rightarrow> complex list" where
  "eigenvalues A = complex_roots_of_rat_poly (char_poly A)"

definition "testmat = mat_of_rows_list 3 [
  [1,-4,2],
  [1/5,7,9],
  [7,1,5 :: rat]
  ]"

definition "spectral_radius_test = show (Max (set [ norm ev. ev \<leftarrow> eigenvalues testmat]))"
value [code] "char_poly testmat"
value [code] spectral_radius_test

end
