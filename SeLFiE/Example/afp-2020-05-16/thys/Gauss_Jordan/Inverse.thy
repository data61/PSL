(*  
    Title:      Inverse.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Inverse of a matrix using the Gauss Jordan algorithm\<close>

theory Inverse
imports
  Gauss_Jordan_PA
begin

subsection\<open>Several properties\<close>

text\<open>Properties about Gauss Jordan algorithm, reduced row echelon form, rank, identity matrix and invertibility\<close>

lemma rref_id_implies_invertible:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
assumes Gauss_mat_1: "Gauss_Jordan A = mat 1"
shows "invertible A"
proof -
obtain P where P: "invertible P" and PA: "Gauss_Jordan A = P ** A" using invertible_Gauss_Jordan[of A] by blast
have "A = mat 1 ** A" unfolding matrix_mul_lid ..
also have "... = (matrix_inv P ** P) ** A" using P invertible_def matrix_inv_unique by metis
also have "... = (matrix_inv P) ** (P ** A)" by (metis PA assms calculation matrix_eq matrix_vector_mul_assoc matrix_vector_mul_lid)
also have "... = (matrix_inv P) ** mat 1" unfolding PA[symmetric] Gauss_mat_1 ..
also have "... = (matrix_inv P)" unfolding matrix_mul_rid ..
finally have "A = (matrix_inv P)" .
thus ?thesis using P unfolding invertible_def using matrix_inv_unique by blast
qed

text\<open>In the following case, nrows is equivalent to ncols due to we are working with a square matrix\<close>
lemma full_rank_implies_invertible:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
assumes rank_n: "rank A = nrows A"
shows "invertible A"
proof (unfold invertible_left_inverse[of A] matrix_left_invertible_ker, clarify)
fix x
assume Ax: "A *v x = 0"
have rank_eq_card_n: "rank A = CARD('n)" using rank_n unfolding nrows_def .
have "vec.dim (null_space A)=0" unfolding dim_null_space unfolding rank_eq_card_n dimension_vector by simp
hence "null_space A = {0}" using vec.dim_zero_eq using Ax null_space_def by auto
thus "x = 0" unfolding null_space_def using Ax by blast
qed


lemma invertible_implies_full_rank:
  fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
  assumes inv_A: "invertible A"
  shows "rank A = nrows A"
proof -
  have "(\<forall>x. A *v x = 0 \<longrightarrow> x = 0)" using inv_A unfolding  invertible_left_inverse[unfolded matrix_left_invertible_ker] .
  hence null_space_eq_0: "(null_space A) = {0}" unfolding null_space_def using matrix_vector_mult_0_right by fast
  have dim_null_space: "vec.dim (null_space A) = 0" unfolding vec.dim_def
    by (metis (no_types) null_space_eq_0 vec.dim_def vec.dim_zero_eq')
  show ?thesis using rank_nullity_theorem_matrices[of A] unfolding dim_null_space rank_eq_dim_col_space nrows_def
    unfolding col_space_eq unfolding ncols_def by simp
qed


definition id_upt_k :: "'a::{zero, one}^'n::{mod_type}^'n::{mod_type} \<Rightarrow> nat => bool"
where "id_upt_k A k = (\<forall>i j. to_nat i < k \<and> to_nat j < k \<longrightarrow> ((i = j \<longrightarrow> A $ i $ j = 1) \<and> (i \<noteq> j \<longrightarrow> A $ i $ j = 0)))"

lemma id_upt_nrows_mat_1:
assumes "id_upt_k A (nrows A)"
shows "A = mat 1"
unfolding mat_def apply vector using assms unfolding id_upt_k_def nrows_def
using to_nat_less_card[where ?'a='b]
by presburger

subsection\<open>Computing the inverse of a matrix using the Gauss Jordan algorithm\<close>

text\<open>This lemma is essential to demonstrate that the Gauss Jordan form of an invertible matrix is the identity. 
  The proof is made by induction and it is explained in 
  @{url "http://www.unirioja.es/cu/jodivaso/Isabelle/Gauss-Jordan-2013-2-Generalized/Demonstration_invertible.pdf"}\<close>

lemma id_upt_k_Gauss_Jordan:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
assumes inv_A: "invertible A"
shows "id_upt_k (Gauss_Jordan A) k"
proof (induct k)
case 0
show ?case unfolding id_upt_k_def by fast
next
case (Suc k)
note id_k=Suc.hyps
have rref_k: "reduced_row_echelon_form_upt_k (Gauss_Jordan A) k"  using rref_implies_rref_upt[OF rref_Gauss_Jordan] .
have rref_suc_k: "reduced_row_echelon_form_upt_k (Gauss_Jordan A) (Suc k)"  using rref_implies_rref_upt[OF rref_Gauss_Jordan] .
have inv_gj: "invertible (Gauss_Jordan A)" by (metis inv_A invertible_Gauss_Jordan invertible_mult)
show "id_upt_k (Gauss_Jordan A) (Suc k)"
proof (unfold id_upt_k_def, auto)
fix j::'n
assume j_less_suc: "to_nat j < Suc k"
\<comment> \<open>First of all we prove a property which will be useful later\<close>
have greatest_prop: "j \<noteq> 0 \<Longrightarrow> to_nat j = k \<Longrightarrow> (GREATEST m. \<not> is_zero_row_upt_k m k (Gauss_Jordan A)) = j - 1"
proof (rule Greatest_equality)
assume j_not_zero: "j \<noteq> 0" and j_eq_k: "to_nat j = k"
 have j_minus_1: "to_nat (j - 1) < k" by (metis (full_types) Suc_le' diff_add_cancel j_eq_k j_not_zero to_nat_mono)
          show "\<not> is_zero_row_upt_k (j - 1) k (Gauss_Jordan A)"
            unfolding is_zero_row_upt_k_def
            proof (auto, rule exI[of _ "j - 1"], rule conjI)
               show "to_nat (j - 1) < k" using j_minus_1 .
               show "Gauss_Jordan A $ (j - 1) $ (j - 1) \<noteq> 0" using id_k unfolding id_upt_k_def using j_minus_1 by simp
            qed
            fix a::'n
            assume not_zero_a: "\<not> is_zero_row_upt_k a k (Gauss_Jordan A)"
            show "a \<le> j - 1"
              proof (rule ccontr)
                assume " \<not> a \<le> j - 1"
                hence a_greater_i_minus_1: "a > j - 1" by simp
                have "is_zero_row_upt_k a k (Gauss_Jordan A)"
                  unfolding is_zero_row_upt_k_def
                    proof (clarify)
                    fix b::'n assume a: "to_nat b < k"
                    have Least_eq: "(LEAST n. Gauss_Jordan A $ b $ n \<noteq> 0) = b"
                      proof (rule Least_equality)
                        show "Gauss_Jordan A $ b $ b \<noteq> 0" by (metis a id_k id_upt_k_def zero_neq_one)
                        show "\<And>y. Gauss_Jordan A $ b $ y \<noteq> 0 \<Longrightarrow> b \<le> y"
                          by (metis (hide_lams, no_types) a not_less_iff_gr_or_eq id_k id_upt_k_def less_trans not_less to_nat_mono)
                      qed
                    moreover have "\<not> is_zero_row_upt_k b k (Gauss_Jordan A)"
                      unfolding is_zero_row_upt_k_def apply auto apply (rule exI[of _ b]) using a id_k unfolding id_upt_k_def by simp
                    moreover have "a \<noteq> b"
                      proof -
                       have "b < from_nat k" by (metis a from_nat_to_nat_id j_eq_k not_less_iff_gr_or_eq to_nat_le)
                       also have "... = j" using j_eq_k to_nat_from_nat by auto
                       also have "... \<le> a" using a_greater_i_minus_1 by (metis diff_add_cancel le_Suc)
                       finally show ?thesis by simp
                      qed
                    ultimately show "Gauss_Jordan A $ a $ b = 0" using rref_upt_condition4[OF rref_k] by auto
                    qed
                thus "False" using not_zero_a by contradiction
              qed
              qed

show Gauss_jj_1: "Gauss_Jordan A $ j $ j = 1"
proof (cases "j=0")
\<comment> \<open>In case that j be zero, the result is trivial\<close>
case True show ?thesis
  proof (unfold True, rule rref_first_element)
     show "reduced_row_echelon_form (Gauss_Jordan A)" by (rule rref_Gauss_Jordan)
     show "column 0 (Gauss_Jordan A) \<noteq> 0" by (metis det_zero_column inv_gj invertible_det_nz)
  qed
next
case False note j_not_zero = False
show ?thesis
proof (cases "to_nat j < k")
  case True thus ?thesis using id_k unfolding id_upt_k_def by presburger  \<comment> \<open>Easy due to the inductive hypothesis\<close>
  next
  case False
  hence j_eq_k: "to_nat j = k" using j_less_suc by auto
  have j_minus_1: "to_nat (j - 1) < k" by (metis (full_types) Suc_le' diff_add_cancel j_eq_k j_not_zero to_nat_mono)
  have "(GREATEST m. \<not> is_zero_row_upt_k m k (Gauss_Jordan A)) = j - 1" by (rule greatest_prop[OF j_not_zero j_eq_k])
        hence zero_j_k: "is_zero_row_upt_k j k (Gauss_Jordan A)"
                by (metis not_le greatest_ge_nonzero_row j_eq_k j_minus_1 to_nat_mono')
              show ?thesis
                proof (rule ccontr, cases "Gauss_Jordan A $ j $ j = 0")
                case False
                note gauss_jj_not_0 = False
                assume gauss_jj_not_1: "Gauss_Jordan A $ j $ j \<noteq> 1"
                have "(LEAST n. Gauss_Jordan A $ j $ n \<noteq> 0) = j"
                  proof (rule Least_equality)
                     show "Gauss_Jordan A $ j $ j \<noteq> 0" using gauss_jj_not_0 .
                     show "\<And>y. Gauss_Jordan A $ j $ y \<noteq> 0 \<Longrightarrow> j \<le> y" by (metis le_less_linear is_zero_row_upt_k_def j_eq_k to_nat_mono zero_j_k)
                  qed
                hence "Gauss_Jordan A $ j $ (LEAST n. Gauss_Jordan A $ j $ n \<noteq> 0) \<noteq> 1" using gauss_jj_not_1 by auto \<comment> \<open>Contradiction with the second condition of rref\<close>
                thus False by (metis gauss_jj_not_0 is_zero_row_upt_k_def j_eq_k lessI rref_suc_k rref_upt_condition2)             
                next
                  case True
                  note gauss_jj_0 = True
                  have zero_j_suc_k: "is_zero_row_upt_k j (Suc k) (Gauss_Jordan A)" 
                    by (rule is_zero_row_upt_k_suc[OF zero_j_k], metis gauss_jj_0 j_eq_k to_nat_from_nat)                  
                    have "\<not> (\<exists>B. B ** (Gauss_Jordan A) = mat 1)" \<comment> \<open>This will be a contradiction\<close>
                    proof (unfold matrix_left_invertible_independent_columns, simp, 
                        rule exI[of _ "\<lambda>i. (if i < j then column j (Gauss_Jordan A) $ i else if i=j then -1 else 0)"], rule conjI)
                      show "(\<Sum>i\<in>UNIV. (if i < j then column j (Gauss_Jordan A) $ i else if i=j then -1 else 0) *s column i (Gauss_Jordan A)) = 0"                        
                        proof (unfold vec_eq_iff sum_component, auto)
                          \<comment> \<open>We write the column j in a linear combination of the previous ones, which is a contradiction (the matrix wouldn't be invertible)\<close>
                            let ?f="\<lambda>i. (if i < j then column j (Gauss_Jordan A) $ i else if i=j then -1 else 0)"
                            fix i
                            let ?g="(\<lambda>x. ?f x * column x (Gauss_Jordan A) $ i)"
                            show "sum ?g UNIV = 0"
                              proof (cases "i<j")
                              case True note i_less_j = True
                              have sum_rw: "sum ?g (UNIV - {i}) = ?g j + sum ?g ((UNIV - {i}) - {j})"
                                proof (rule sum.remove)
                                   show "finite (UNIV - {i})" using finite_code by simp
                                   show "j \<in> UNIV - {i}" using True by blast
                                qed                                
                              have sum_g0: "sum ?g (UNIV - {i} - {j}) = 0"
                                proof (rule sum.neutral, auto)
                                fix a
                                assume a_not_j: "a \<noteq> j" and a_not_i: "a \<noteq> i" and a_less_j: "a < j" and column_a_not_zero: "column a (Gauss_Jordan A) $ i \<noteq> 0"
                                have "Gauss_Jordan A $ i $ a = 0" using id_k unfolding id_upt_k_def using a_less_j j_eq_k using i_less_j a_not_i to_nat_mono by blast
                                thus "column j (Gauss_Jordan A) $ a = 0" using column_a_not_zero unfolding column_def by simp \<comment> \<open>Contradiction\<close>
                                qed
                              have "sum ?g UNIV = ?g i + sum ?g (UNIV - {i})" by (rule sum.remove, simp_all)
                              also have "... = ?g i + ?g j + sum ?g (UNIV - {i} - {j})" unfolding sum_rw by auto
                              also have "... = ?g i + ?g j" unfolding sum_g0 by simp
                              also have "... = 0" using True unfolding column_def 
                                by (simp, metis id_k id_upt_k_def j_eq_k to_nat_mono)
                              finally show ?thesis .
                              next
                              case False
                              have zero_i_suc_k: "is_zero_row_upt_k i (Suc k) (Gauss_Jordan A)"
                                    by (metis False zero_j_suc_k linorder_cases rref_suc_k rref_upt_condition1)
                              show ?thesis
                                proof (rule sum.neutral, auto)              
                                  show "column j (Gauss_Jordan A) $ i = 0"
                                    using zero_i_suc_k unfolding column_def is_zero_row_upt_k_def
                                    by (metis j_eq_k lessI vec_lambda_beta)
                                  next
                                  fix a
                                  assume a_not_j: "a \<noteq> j" and a_less_j: "a < j" and column_a_i: "column a (Gauss_Jordan A) $ i \<noteq> 0"
                                  have "Gauss_Jordan A $ i $ a = 0" using zero_i_suc_k unfolding is_zero_row_upt_k_def
                                    by (metis (full_types) a_less_j j_eq_k less_SucI to_nat_mono)
                                  thus "column j (Gauss_Jordan A) $ a = 0" using column_a_i unfolding column_def by simp                                  
                        qed
                    qed
                    qed
                    next
                    show "\<exists>i. (if i < j then column j (Gauss_Jordan A) $ i else if i = j then -1 else 0) \<noteq> 0"
                      by (metis False j_eq_k neg_equal_0_iff_equal to_nat_mono zero_neq_one)
                    qed                    
                    thus False using inv_gj unfolding invertible_def by simp
                    qed
                    qed 
                   qed
                    fix i::'n
                    assume i_less_suc: "to_nat i < Suc k" and i_not_j: "i \<noteq> j"
                    show "Gauss_Jordan A $ i $ j = 0" \<comment> \<open>This result is proved making use of the 4th condition of rref\<close>
                      proof (cases "to_nat i < k \<and> to_nat j < k")
                        case True thus ?thesis using id_k i_not_j unfolding id_upt_k_def by blast \<comment> \<open>Easy due to the inductive hypothesis\<close>
                        next
                        case False note i_or_j_ge_k = False
                        show ?thesis
                        proof (cases "to_nat i < k")
                          case True
                          hence j_eq_k: "to_nat j = k" using i_or_j_ge_k j_less_suc by simp
                          have j_noteq_0: "j \<noteq> 0" by (metis True j_eq_k less_nat_zero_code to_nat_0)
                          have j_minus_1: "to_nat (j - 1) < k" by (metis (full_types) Suc_le' diff_add_cancel j_eq_k j_noteq_0 to_nat_mono)
                          have "(GREATEST m. \<not> is_zero_row_upt_k m k (Gauss_Jordan A)) = j - 1" by (rule greatest_prop[OF j_noteq_0 j_eq_k])
                          hence zero_j_k: "is_zero_row_upt_k j k (Gauss_Jordan A)" 
                            by (metis (lifting, mono_tags) less_linear less_asym j_eq_k j_minus_1 not_greater_Greatest to_nat_mono)
                          have Least_eq_j: "(LEAST n. Gauss_Jordan A $ j $ n \<noteq> 0) = j"
                            proof (rule Least_equality)
                               show "Gauss_Jordan A $ j $ j \<noteq> 0" using Gauss_jj_1 by simp
                               show "\<And>y. Gauss_Jordan A $ j $ y \<noteq> 0 \<Longrightarrow> j \<le> y" 
                               by (metis True le_cases from_nat_to_nat_id i_or_j_ge_k is_zero_row_upt_k_def j_less_suc less_Suc_eq_le less_le to_nat_le zero_j_k)
                            qed
                          moreover have "\<not> is_zero_row_upt_k j (Suc k) (Gauss_Jordan A)" unfolding is_zero_row_upt_k_def by (metis Gauss_jj_1 j_less_suc zero_neq_one)                          
                          ultimately show ?thesis using rref_upt_condition4[OF rref_suc_k] i_not_j by fastforce
                          next
                          case False
                          hence i_eq_k: "to_nat i = k" by (metis \<open>to_nat i < Suc k\<close> less_SucE)
                          hence j_less_k: "to_nat j < k" by (metis i_not_j j_less_suc less_SucE to_nat_from_nat)
                          have "(LEAST n. Gauss_Jordan A $ j $ n \<noteq> 0) = j"
                            proof (rule Least_equality)
                               show "Gauss_Jordan A $ j $ j \<noteq> 0" by (metis Gauss_jj_1 zero_neq_one)
                               show "\<And>y. Gauss_Jordan A $ j $ y \<noteq> 0 \<Longrightarrow> j \<le> y"
                                  by (metis le_cases id_k id_upt_k_def j_less_k less_trans not_less to_nat_mono)
                            qed
                          moreover have "\<not> is_zero_row_upt_k j k (Gauss_Jordan A)" by (metis (full_types) Gauss_jj_1 is_zero_row_upt_k_def j_less_k zero_neq_one)
                          ultimately show ?thesis  using rref_upt_condition4[OF rref_k] i_not_j by fastforce
                         qed
                         qed
qed
qed


lemma invertible_implies_rref_id:
  fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
  assumes inv_A: "invertible A"
  shows "Gauss_Jordan A = mat 1"
  using id_upt_k_Gauss_Jordan[OF inv_A, of "nrows (Gauss_Jordan A)"]
  using id_upt_nrows_mat_1
  by fast


lemma matrix_inv_Gauss:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
assumes inv_A: "invertible A" and Gauss_eq: "Gauss_Jordan A = P ** A"
shows "matrix_inv A = P"
proof (unfold matrix_inv_def, rule some1_equality)
 show "\<exists>!A'. A ** A' = mat 1 \<and> A' ** A = mat 1" by (metis inv_A invertible_def matrix_inv_unique matrix_left_right_inverse)
 show "A ** P = mat 1 \<and> P ** A = mat 1" by (metis Gauss_eq inv_A invertible_implies_rref_id matrix_left_right_inverse)
qed


lemma matrix_inv_Gauss_Jordan_PA:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
assumes inv_A: "invertible A"
shows "matrix_inv A = fst (Gauss_Jordan_PA A)"
by (metis Gauss_Jordan_PA_eq fst_Gauss_Jordan_PA inv_A matrix_inv_Gauss)


lemma invertible_eq_full_rank[code_unfold]:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "invertible A = (rank A = nrows A)"
by (metis full_rank_implies_invertible invertible_implies_full_rank)

definition "inverse_matrix A = (if invertible A then Some (matrix_inv A) else None)"

lemma the_inverse_matrix:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
assumes "invertible A"
shows "the (inverse_matrix A) = P_Gauss_Jordan A"
  by (metis P_Gauss_Jordan_def assms inverse_matrix_def matrix_inv_Gauss_Jordan_PA option.sel)

lemma inverse_matrix:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "inverse_matrix A = (if invertible A then Some (P_Gauss_Jordan A) else None)"
  by (metis inverse_matrix_def option.sel the_inverse_matrix)

lemma inverse_matrix_code[code_unfold]:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "inverse_matrix A = (let GJ = Gauss_Jordan_PA A;
                                rank_A = (if A = 0 then 0 else to_nat (GREATEST a. row a (snd GJ) \<noteq> 0) + 1) in 
                                if nrows A = rank_A then Some (fst(GJ)) else None)"
unfolding inverse_matrix
unfolding invertible_eq_full_rank
unfolding rank_Gauss_Jordan_code
unfolding P_Gauss_Jordan_def
unfolding Let_def Gauss_Jordan_PA_eq by presburger

end



