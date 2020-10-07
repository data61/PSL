(*  
    Title:      Determinants_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Computing determinants of matrices using the Gauss Jordan algorithm over nested IArrays\<close>

theory Determinants_IArrays
imports 
    Determinants2
    Gauss_Jordan_IArrays
begin

subsection\<open>Definitions\<close>

definition "Gauss_Jordan_in_ij_det_P_iarrays A i j = (let n = least_non_zero_position_of_vector_from_index (column_iarray j A) i 
  in (if i = n then 1 / A !! i !! j else - 1 / A !! n !! j, Gauss_Jordan_in_ij_iarrays A i j))"

definition "Gauss_Jordan_column_k_det_P_iarrays A' k = (let det_P = fst A'; i = fst (snd A'); A = snd (snd A')
 in if vector_all_zero_from_index (i, column_iarray k A) \<or> i = nrows_iarray A then (det_P, i, A)
    else let gauss = Gauss_Jordan_in_ij_det_P_iarrays A i k in (fst gauss * det_P, i + 1, snd gauss))"

definition "Gauss_Jordan_upt_k_det_P_iarrays A k = (let foldl = foldl Gauss_Jordan_column_k_det_P_iarrays (1, 0, A) [0..<Suc k] in (fst foldl, snd (snd foldl)))"
definition "Gauss_Jordan_det_P_iarrays A = Gauss_Jordan_upt_k_det_P_iarrays A (ncols_iarray A - 1)"

subsection\<open>Proofs\<close>

text\<open>A more efficient equation for @{term "Gauss_Jordan_in_ij_det_P_iarrays A i j"}.\<close>

lemma Gauss_Jordan_in_ij_det_P_iarrays_code[code]: "Gauss_Jordan_in_ij_det_P_iarrays A i j 
    = (let n = least_non_zero_position_of_vector_from_index (column_iarray j A) i;
           interchange_A = interchange_rows_iarray A i n;
           A' = mult_row_iarray interchange_A i (1 / interchange_A !! i !! j)
       in (if i = n then 1 / A !! i !! j else - 1 / A !! n !! j, IArray.of_fun (\<lambda>s. if s = i then A' !! s else row_add_iarray A' s i (- interchange_A !! s !! j) !! s) (nrows_iarray A)))"
unfolding Gauss_Jordan_in_ij_det_P_iarrays_def Gauss_Jordan_in_ij_iarrays_def Let_def ..


lemma matrix_to_iarray_fst_Gauss_Jordan_in_ij_det_P:
assumes ex_n: "\<exists>n. A $ n $ j \<noteq> 0 \<and> i \<le> n"
shows "fst (Gauss_Jordan_in_ij_det_P A i j) = fst (Gauss_Jordan_in_ij_det_P_iarrays (matrix_to_iarray A) (to_nat i) (to_nat j))"
proof -
have least_n_eq: "least_non_zero_position_of_vector_from_index (vec_to_iarray (column j A)) (to_nat i) = to_nat (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)"
by (rule vec_to_iarray_least_non_zero_position_of_vector_from_index'[unfolded matrix_vector_all_zero_from_index[symmetric]], metis ex_n)
show ?thesis
unfolding Gauss_Jordan_in_ij_det_P_def Gauss_Jordan_in_ij_det_P_iarrays_def Let_def fst_conv
 unfolding  least_n_eq[unfolded vec_to_iarray_column] unfolding matrix_to_iarray_nth by auto
qed

corollary matrix_to_iarray_fst_Gauss_Jordan_in_ij_det_P':
assumes "\<not> (vector_all_zero_from_index (to_nat i, vec_to_iarray (column j A)))"
shows "fst (Gauss_Jordan_in_ij_det_P A i j) = fst (Gauss_Jordan_in_ij_det_P_iarrays (matrix_to_iarray A) (to_nat i) (to_nat j))"
using matrix_to_iarray_fst_Gauss_Jordan_in_ij_det_P assms unfolding matrix_vector_all_zero_from_index[symmetric]
by auto

lemma matrix_to_iarray_snd_Gauss_Jordan_in_ij_det_P:
assumes ex_n: "\<exists>n. A $ n $ j \<noteq> 0 \<and> i \<le> n"
shows "matrix_to_iarray (snd (Gauss_Jordan_in_ij_det_P A i j)) = snd (Gauss_Jordan_in_ij_det_P_iarrays (matrix_to_iarray A) (to_nat i) (to_nat j))"
unfolding Gauss_Jordan_in_ij_det_P_def Gauss_Jordan_in_ij_det_P_iarrays_def Let_def snd_conv
by (rule matrix_to_iarray_Gauss_Jordan_in_ij, simp add: matrix_vector_all_zero_from_index[symmetric], metis ex_n)


lemma matrix_to_iarray_fst_Gauss_Jordan_column_k_det_P:
assumes i: "i\<le>nrows A" and k: "k<ncols A"
shows "fst (Gauss_Jordan_column_k_det_P (n, i, A) k) = fst (Gauss_Jordan_column_k_det_P_iarrays (n, i, matrix_to_iarray A) k)"
proof (cases "i<nrows A")
case True
show ?thesis
unfolding Gauss_Jordan_column_k_det_P_def Gauss_Jordan_column_k_det_P_iarrays_def Let_def snd_conv fst_conv 
unfolding matrix_to_iarray_nrows matrix_vector_all_zero_from_index
using matrix_to_iarray_fst_Gauss_Jordan_in_ij_det_P'[of "from_nat i" "from_nat k" A]
unfolding vec_to_iarray_column
unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
unfolding to_nat_from_nat_id[OF k[unfolded ncols_def]]
by auto
next
case False
hence "i=nrows A" using i by simp
thus ?thesis
unfolding Gauss_Jordan_column_k_det_P_def Gauss_Jordan_column_k_det_P_iarrays_def Let_def snd_conv fst_conv unfolding matrix_to_iarray_nrows by force
qed


lemma matrix_to_iarray_fst_snd_Gauss_Jordan_column_k_det_P:
assumes i: "i\<le>nrows A" and k: "k<ncols A"
shows "fst (snd (Gauss_Jordan_column_k_det_P (n, i, A) k)) = fst (snd (Gauss_Jordan_column_k_det_P_iarrays (n, i, matrix_to_iarray A) k))"
proof (cases "i<nrows A")
case True
show ?thesis
unfolding Gauss_Jordan_column_k_det_P_def Gauss_Jordan_column_k_det_P_iarrays_def Let_def snd_conv fst_conv
unfolding matrix_to_iarray_nrows matrix_vector_all_zero_from_index
unfolding vec_to_iarray_column
unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
unfolding to_nat_from_nat_id[OF k[unfolded ncols_def]] by auto
next
case False
thus ?thesis
using assms
unfolding Gauss_Jordan_column_k_det_P_def Gauss_Jordan_column_k_det_P_iarrays_def Let_def snd_conv fst_conv
unfolding matrix_to_iarray_nrows matrix_vector_all_zero_from_index by auto
qed

lemma matrix_to_iarray_snd_snd_Gauss_Jordan_column_k_det_P:
assumes i: "i\<le>nrows A" and k: "k<ncols A"
shows "matrix_to_iarray (snd (snd (Gauss_Jordan_column_k_det_P (n, i, A) k))) = snd (snd (Gauss_Jordan_column_k_det_P_iarrays (n, i, matrix_to_iarray A) k))"
proof (cases "i<nrows A")
case True
show ?thesis
unfolding Gauss_Jordan_column_k_det_P_def Gauss_Jordan_column_k_det_P_iarrays_def Let_def fst_conv snd_conv 
unfolding matrix_to_iarray_nrows matrix_vector_all_zero_from_index
using matrix_to_iarray_snd_Gauss_Jordan_in_ij_det_P[of A "from_nat k" "from_nat i"]
using matrix_vector_all_zero_from_index[of "from_nat i" A "from_nat k"]
unfolding vec_to_iarray_column
unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
unfolding to_nat_from_nat_id[OF k[unfolded ncols_def]]
by auto
next
case False
thus ?thesis
using assms
unfolding Gauss_Jordan_column_k_det_P_def Gauss_Jordan_column_k_det_P_iarrays_def Let_def fst_conv snd_conv 
unfolding matrix_to_iarray_nrows matrix_vector_all_zero_from_index by auto
qed


lemma fst_snd_Gauss_Jordan_column_k_det_P_le_nrows:
assumes i: "i\<le>nrows A"
shows "fst (snd (Gauss_Jordan_column_k_det_P (n, i, A) k)) \<le> nrows A"
unfolding fst_snd_Gauss_Jordan_column_k_det_P_eq_fst_snd_Gauss_Jordan_column_k_PA[unfolded fst_snd_Gauss_Jordan_column_k_PA_eq]
by (rule fst_Gauss_Jordan_column_k[OF i])

text\<open>The proof of the following theorem is very similar to the ones of \<open>foldl_Gauss_Jordan_column_k_eq\<close>, 
      \<open>rref_and_index_Gauss_Jordan_upt_k\<close> and \<open>foldl_Gauss_Jordan_column_k_det_P\<close>.\<close>

lemma 
assumes "k<ncols A"
shows matrix_to_iarray_fst_Gauss_Jordan_upt_k_det_P: "fst (Gauss_Jordan_upt_k_det_P A k) = fst (Gauss_Jordan_upt_k_det_P_iarrays (matrix_to_iarray A) k)"
and matrix_to_iarray_snd_Gauss_Jordan_upt_k_det_P: "matrix_to_iarray (snd (Gauss_Jordan_upt_k_det_P A k)) = snd (Gauss_Jordan_upt_k_det_P_iarrays (matrix_to_iarray A) k)"
and "fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k])) \<le> nrows A"
and "fst (snd (foldl Gauss_Jordan_column_k_det_P_iarrays (1, 0, matrix_to_iarray A) [0..<Suc k])) = fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k]))"
using assms
proof (induct k)
show "fst (Gauss_Jordan_upt_k_det_P A 0) = fst (Gauss_Jordan_upt_k_det_P_iarrays (matrix_to_iarray A) 0)"
unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_det_P_iarrays_def Let_def fst_conv
by (simp, rule matrix_to_iarray_fst_Gauss_Jordan_column_k_det_P, simp_all add: ncols_def)
show "matrix_to_iarray (snd (Gauss_Jordan_upt_k_det_P A 0)) = snd (Gauss_Jordan_upt_k_det_P_iarrays (matrix_to_iarray A) 0)"
unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_det_P_iarrays_def Let_def fst_conv snd_conv
by (simp, rule matrix_to_iarray_snd_snd_Gauss_Jordan_column_k_det_P, simp_all add: ncols_def)
show "fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc 0])) \<le> nrows A"
unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_det_P_iarrays_def Let_def fst_conv snd_conv
by (simp, rule fst_snd_Gauss_Jordan_column_k_det_P_le_nrows, simp add: nrows_def)
show "fst (snd (foldl Gauss_Jordan_column_k_det_P_iarrays (1, 0, matrix_to_iarray A) [0..<Suc 0])) = fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc 0]))"
unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_det_P_iarrays_def Let_def fst_conv snd_conv
by (simp, rule matrix_to_iarray_fst_snd_Gauss_Jordan_column_k_det_P[symmetric], simp_all add: ncols_def)
next
fix k
assume "(k < ncols A \<Longrightarrow> fst (Gauss_Jordan_upt_k_det_P A k) = fst (Gauss_Jordan_upt_k_det_P_iarrays (matrix_to_iarray A) k))" 
        and "(k < ncols A \<Longrightarrow> matrix_to_iarray (snd (Gauss_Jordan_upt_k_det_P A k)) = snd (Gauss_Jordan_upt_k_det_P_iarrays (matrix_to_iarray A) k))"
        and "(k < ncols A \<Longrightarrow> fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k])) \<le> nrows A)"
        and "(k < ncols A \<Longrightarrow> fst (snd (foldl Gauss_Jordan_column_k_det_P_iarrays (1, 0, matrix_to_iarray A) [0..<Suc k])) = fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k])))"
        and Suc_k_less_ncols: "Suc k < ncols A"
hence hyp1: "fst (Gauss_Jordan_upt_k_det_P A k) = fst (Gauss_Jordan_upt_k_det_P_iarrays (matrix_to_iarray A) k)"
and hyp2: "matrix_to_iarray (snd (Gauss_Jordan_upt_k_det_P A k)) = snd (Gauss_Jordan_upt_k_det_P_iarrays (matrix_to_iarray A) k)"
and hyp3: "fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k])) \<le> nrows A"
and hyp4: "(fst (snd (foldl Gauss_Jordan_column_k_det_P_iarrays (1, 0, matrix_to_iarray A) [0..<Suc k])) = fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k])))"
  by auto
have list_rw: "[0..<Suc (Suc k)] = [0..<(Suc k)] @ [Suc k]" by simp
define f where "f = foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k]"
define g where "g = foldl Gauss_Jordan_column_k_det_P_iarrays (1, 0, matrix_to_iarray A) [0..<Suc k]"
have f_rw: "f = (fst f, fst (snd f), snd (snd f))" by simp
have g_rw: "g = (fst g, fst (snd g), snd (snd g))" by simp
have fst_rw: "fst g = fst f" unfolding f_def g_def using hyp1[unfolded Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_det_P_iarrays_def Let_def fst_conv] ..
have fst_snd_rw: "fst (snd g) = fst (snd f)" unfolding f_def g_def using hyp4 .
have snd_snd_rw: "snd (snd g) = matrix_to_iarray (snd (snd f))" 
  unfolding f_def g_def using hyp2[unfolded Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_det_P_iarrays_def Let_def snd_conv] ..
have fst_snd_f_le_nrows: "fst (snd f) \<le> nrows (snd (snd f))"  unfolding f_def g_def using hyp3 unfolding nrows_def .
have Suc_k_less_ncols': "Suc k < ncols (snd (snd f))"  using Suc_k_less_ncols unfolding ncols_def .
show "fst (Gauss_Jordan_upt_k_det_P A (Suc k)) = fst (Gauss_Jordan_upt_k_det_P_iarrays (matrix_to_iarray A) (Suc k))"
unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_det_P_iarrays_def Let_def fst_conv
unfolding list_rw foldl_append
unfolding List.foldl.simps
unfolding f_def[symmetric] g_def[symmetric]
by (subst f_rw, subst g_rw, unfold fst_rw fst_snd_rw snd_snd_rw, rule matrix_to_iarray_fst_Gauss_Jordan_column_k_det_P[OF fst_snd_f_le_nrows Suc_k_less_ncols'])
show "matrix_to_iarray (snd (Gauss_Jordan_upt_k_det_P A (Suc k))) = snd (Gauss_Jordan_upt_k_det_P_iarrays (matrix_to_iarray A) (Suc k))"
unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_det_P_iarrays_def Let_def snd_conv
unfolding list_rw foldl_append
unfolding List.foldl.simps
unfolding f_def[symmetric] g_def[symmetric]
by (subst f_rw, subst g_rw, unfold fst_rw fst_snd_rw snd_snd_rw, rule matrix_to_iarray_snd_snd_Gauss_Jordan_column_k_det_P[OF fst_snd_f_le_nrows Suc_k_less_ncols'])
show "fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc (Suc k)])) \<le> nrows A"
unfolding list_rw foldl_append List.foldl.simps
unfolding f_def[symmetric] g_def[symmetric]
apply (subst f_rw)
using fst_snd_Gauss_Jordan_column_k_det_P_le_nrows[OF fst_snd_f_le_nrows]
unfolding nrows_def .
show "fst (snd (foldl Gauss_Jordan_column_k_det_P_iarrays (1, 0, matrix_to_iarray A) [0..<Suc (Suc k)])) = fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc (Suc k)]))"
unfolding list_rw foldl_append List.foldl.simps
unfolding f_def[symmetric] g_def[symmetric]
by (subst f_rw, subst g_rw, unfold fst_rw fst_snd_rw snd_snd_rw,rule matrix_to_iarray_fst_snd_Gauss_Jordan_column_k_det_P[symmetric, OF fst_snd_f_le_nrows Suc_k_less_ncols'])
qed


lemma matrix_to_iarray_fst_Gauss_Jordan_det_P:
shows "fst (Gauss_Jordan_det_P A) = fst (Gauss_Jordan_det_P_iarrays (matrix_to_iarray A))"
unfolding Gauss_Jordan_det_P_def Gauss_Jordan_det_P_iarrays_def
using matrix_to_iarray_fst_Gauss_Jordan_upt_k_det_P
by (metis diff_less matrix_to_iarray_ncols ncols_not_0 neq0_conv zero_less_one)

lemma matrix_to_iarray_snd_Gauss_Jordan_det_P:
shows "matrix_to_iarray (snd (Gauss_Jordan_det_P A)) = snd (Gauss_Jordan_det_P_iarrays (matrix_to_iarray A))"
unfolding Gauss_Jordan_det_P_def Gauss_Jordan_det_P_iarrays_def
using matrix_to_iarray_snd_Gauss_Jordan_upt_k_det_P
by (metis diff_less matrix_to_iarray_ncols ncols_not_0 neq0_conv zero_less_one)

subsection\<open>Code equations\<close>
definition "det_iarrays A = (let A' = Gauss_Jordan_det_P_iarrays A in prod_list (map (\<lambda>i. (snd A') !! i !! i) [0..<nrows_iarray A]) / fst A')"

lemma matrix_to_iarray_det[code_unfold]:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "det A = det_iarrays (matrix_to_iarray A)"
proof -
let ?f="(\<lambda>i. snd (Gauss_Jordan_det_P_iarrays (matrix_to_iarray A)) !! i !! i)"
have *: "fst (Gauss_Jordan_det_P A) = fst (Gauss_Jordan_det_P_iarrays (matrix_to_iarray A))" 
  unfolding matrix_to_iarray_fst_Gauss_Jordan_det_P ..
  have "prod_list (map ?f [0..<nrows_iarray (matrix_to_iarray A)]) = prod ?f (set [0..<nrows_iarray (matrix_to_iarray A)])"
    by (metis (no_types, lifting) distinct_upt prod.distinct_set_conv_list)
also have "... = (\<Prod>i\<in>UNIV. snd (Gauss_Jordan_det_P A) $ i $ i)"
  proof (rule prod.reindex_cong[of "to_nat::('n=>nat)"])
    show "inj (to_nat::('n=>nat))" by (metis strict_mono_imp_inj_on strict_mono_to_nat)
    show "set [0..<nrows_iarray (matrix_to_iarray A)] = range (to_nat::'n=>nat)"
    unfolding nrows_eq_card_rows using bij_to_nat[where ?'a='n]
    unfolding bij_betw_def 
    unfolding atLeast0LessThan atLeast_upt by auto
    fix x 
    show "snd (Gauss_Jordan_det_P_iarrays (matrix_to_iarray A)) !! to_nat x !! to_nat x = snd (Gauss_Jordan_det_P A) $ x $ x"
    unfolding matrix_to_iarray_snd_Gauss_Jordan_det_P[symmetric]
    unfolding matrix_to_iarray_nth ..
    qed
  finally have "(\<Prod>i\<in>UNIV. snd (Gauss_Jordan_det_P A) $ i $ i) 
  = prod_list (map (\<lambda>i. snd (Gauss_Jordan_det_P_iarrays (matrix_to_iarray A)) !! i !! i) [0..<nrows_iarray (matrix_to_iarray A)])" ..
  thus ?thesis using * unfolding det_code_equation det_iarrays_def Let_def  by presburger
qed

end
