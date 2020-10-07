(* 
    Title:      Code_Cayley_Hamilton.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Code Cayley Hamilton\<close>

theory Code_Cayley_Hamilton
  imports 
  "HOL-Computational_Algebra.Polynomial"
  Cayley_Hamilton_Compatible
  Gauss_Jordan.Code_Matrix
begin

subsection\<open>Code equations for the definitions presented in the Cayley-Hamilton development\<close>

definition "scalar_matrix_mult_row c A i = (\<chi> j. c * (A $ i $ j))"

lemma scalar_matrix_mult_row_code [code abstract]:
  "vec_nth (scalar_matrix_mult_row c A i) =(% j. c * (A $ i $ j))"
  by(simp add: scalar_matrix_mult_row_def fun_eq_iff)

lemma scalar_matrix_mult_code [code abstract]: "vec_nth (c *k A)  = scalar_matrix_mult_row c A"
  unfolding matrix_scalar_mult_def scalar_matrix_mult_row_def[abs_def]
  using vec_lambda_beta by auto


definition "minorM_row A i j k=  vec_lambda (%l. if k = i \<and> l = j then 1 else
  if k = i \<or> l = j then 0 else A$k$l)"

lemma minorM_row_code [code abstract]:
  "vec_nth (minorM_row A i j k) =(%l. if k = i \<and> l = j then 1 else
  if k = i \<or> l = j then 0 else A$k$l)"
  by(simp add: minorM_row_def fun_eq_iff)

lemma minorM_code [code abstract]: "vec_nth (minorM A i j) = minorM_row A i j"
  unfolding minorM_def by transfer (auto simp: vec_eq_iff fun_eq_iff minorM_row_def)

definition "cofactorM_row A i = vec_lambda (\<lambda>j. cofactorM A $ i $ j)"

lemma cofactorM_row_code [code abstract]: "vec_nth (cofactorM_row A i) = cofactor A i"
  by (simp add: fun_eq_iff cofactorM_row_def cofactor_def cofactorM_def)

lemma cofactorM_code [code abstract]: "vec_nth (cofactorM A) = cofactorM_row A"
  by (simp add: fun_eq_iff cofactorM_row_def vec_eq_iff)

lemmas cofactor_def[code_unfold]

definition mat2matofpoly_row
  where "mat2matofpoly_row A i = vec_lambda (\<lambda>j. [: A $ i $ j :])"

lemma mat2matofpoly_row_code [code abstract]:
  "vec_nth (mat2matofpoly_row A i) = (%j. [: A $ i $ j :])" 
  unfolding mat2matofpoly_row_def by auto

lemma [code abstract]: "vec_nth (mat2matofpoly k) = mat2matofpoly_row k"
  unfolding mat2matofpoly_def unfolding mat2matofpoly_row_def[abs_def] by auto

primrec matpow :: "'a::semiring_1^'n^'n \<Rightarrow> nat \<Rightarrow> 'a^'n^'n" where
  matpow_0:   "matpow A 0 = mat 1" |
  matpow_Suc: "matpow A (Suc n) = A ** (matpow A n)"

definition evalmat :: "'a::comm_ring_1 poly \<Rightarrow> 'a^'n^'n \<Rightarrow> 'a^'n^'n" where
  "evalmat P A = (\<Sum> i \<in> { n::nat . n \<le> ( degree P ) } . (coeff P i) *k (matpow A i) )"

lemma evalmat_unfold:
  "evalmat P A = (\<Sum>i = 0..degree P. coeff P i *k matpow A i)"
  by (simp add: evalmat_def atMost_def [symmetric] atMost_atLeast0)

lemma evalmat_code[code]:
  "evalmat P A = (\<Sum>i\<leftarrow>[0..int (degree P)]. coeff P (nat i) *k matpow A (nat i))" (is "_ = ?rhs")
proof -
  let ?t = "\<lambda>n. coeff P n *k matpow A n"
  have "(\<Sum>i = 0..degree P. coeff P i *k matpow A i) = (\<Sum>i\<in>{0..int (degree P)}. coeff P (nat i) *k matpow A (nat i))"
    by (rule sum.reindex_cong [of nat])
      (auto simp add: eq_nat_nat_iff image_iff intro: inj_onI, presburger)
  also have "\<dots> = ?rhs"
    by (simp add: sum_set_upto_conv_sum_list_int [symmetric])
  finally show ?thesis
    by (simp add: evalmat_unfold)
qed

definition coeffM_zero :: "'a poly^'n^'n \<Rightarrow> 'a::zero^'n^'n" where
  "coeffM_zero A = (\<chi> i j. (coeff (A $ i $ j) 0))"

definition "coeffM_zero_row A i = (\<chi> j. (coeff (A $ i $ j) 0))"

definition coeffM :: "'a poly^'n^'n \<Rightarrow> nat \<Rightarrow> 'a::zero^'n^'n" where
  "coeffM A n = (\<chi> i j. coeff (A $ i $ j) n)"

lemma coeffM_zero_row_code [code abstract]:
  "vec_nth (coeffM_zero_row A i) = (% j. (coeff (A $ i $ j) 0))"
  by(simp add: coeffM_zero_row_def fun_eq_iff)

lemma coeffM_zero_code [code abstract]: "vec_nth (coeffM_zero A) = coeffM_zero_row A"
  unfolding coeffM_zero_def coeffM_zero_row_def[abs_def]
  using vec_lambda_beta by auto

definition
  "coeffM_row A n i = (\<chi> j. coeff (A $ i $ j) n)"

lemma coeffM_row_code [code abstract]:
  "vec_nth (coeffM_row A n i) = (% j. coeff (A $ i $ j) n)"
  by(simp add: coeffM_row_def coeffM_def fun_eq_iff)

lemma coeffM_code [code abstract]: "vec_nth (coeffM A n) = coeffM_row A n"
  unfolding coeffM_def coeffM_row_def[abs_def]
  using vec_lambda_beta by auto

end
