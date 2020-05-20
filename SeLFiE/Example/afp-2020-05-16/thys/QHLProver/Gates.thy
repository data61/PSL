section \<open>Standard gates\<close>

theory Gates
  imports Complex_Matrix
begin

text \<open>Pauli matrices\<close>
definition sigma_x :: "complex mat" where
  "sigma_x = mat_of_rows_list 2 [[0, 1], [1, 0]]"

definition sigma_y :: "complex mat" where
  "sigma_y = mat_of_rows_list 2 [[0, -\<i>], [\<i>, 0]]"

definition sigma_z :: "complex mat" where
  "sigma_z = mat_of_rows_list 2 [[1, 0], [0, -1]]"

text \<open>Hadamard matrices\<close>
definition hadamard :: "complex mat" where
  "hadamard = mat 2 2 (\<lambda>(i, j). if (i = 0 \<or> j = 0) then 1 / csqrt 2 else - 1 / sqrt 2)"

lemma hadamard_dim:
  "hadamard \<in> carrier_mat 2 2" 
  unfolding hadamard_def mat_of_rows_list_def by auto

lemma hermitian_hadamard:
  "hermitian hadamard"
  unfolding hermitian_def hadamard_def
  apply (rule eq_matI) by (auto simp add: adjoint_eval adjoint_dim)

lemma csqrt_2_sq:
  "complex_of_real (sqrt 2) * complex_of_real (sqrt 2) = 2"
  by (smt of_real_add of_real_hom.hom_one of_real_power one_add_one power2_eq_square real_sqrt_pow2)

lemma sum_le_2:
  "\<And>(f::nat\<Rightarrow>complex). sum f {0..<2} = f 0 + f 1"
  by (simp add: numeral_2_eq_2)

lemma unitary_hadamard:
  "unitary hadamard"
  unfolding unitary_def apply (rule)
  subgoal using carrier_matD[OF hadamard_dim] hadamard_def by auto
  apply (subst hermitian_hadamard[unfolded hermitian_def])
  unfolding inverts_mat_def
  apply (rule eq_matI) unfolding hadamard_def
    apply (auto simp add: carrier_matD[OF hadamard_dim] scalar_prod_def)
  by (auto simp add: sum_le_2 csqrt_2_sq)

text \<open>The matrix
  [0 0 .. 0 1
   1 0 .. 0 0
   0 1 .. 0 0
   . . .. . .
   0 0 .. 1 0]
  implements i := i + 1 in the last variable.
\<close>
definition mat_incr :: "nat \<Rightarrow> complex mat" where
  "mat_incr n = mat n n (\<lambda>(i,j). if i = 0 then (if j = n - 1 then 1 else 0) else (if i = j + 1 then 1 else 0))"

lemma mat_incr_dim:
  "mat_incr n \<in> carrier_mat n n"
  unfolding mat_incr_def by auto

lemma adjoint_mat_incr:
  "adjoint (mat_incr n) = mat n n (\<lambda>(i,j). if j = 0 then (if i = n - 1 then 1 else 0) else (if j = i + 1 then 1 else 0))"
  apply (rule eq_matI) unfolding mat_incr_def
  by (auto simp add: adjoint_eval)

lemma mat_incr_mult_adjoint_mat_incr:
  shows "mat_incr n * (adjoint (mat_incr n)) = 1\<^sub>m n"
  apply (rule eq_matI, simp)
    apply (auto simp add: carrier_matD[OF mat_incr_dim] scalar_prod_def)
  unfolding adjoint_mat_incr unfolding mat_incr_def
   apply (simp_all)
  apply (case_tac "j = 0") 
  subgoal for j by (simp add: sum_only_one_neq_0[of _ "n - Suc 0"])
  subgoal for j by (simp add: sum_only_one_neq_0[of _ "j - 1"])
  done

lemma unitary_mat_incr:
  "unitary (mat_incr n)"
  unfolding unitary_def inverts_mat_def
  using carrier_matD[OF mat_incr_dim] mat_incr_mult_adjoint_mat_incr by auto

end
