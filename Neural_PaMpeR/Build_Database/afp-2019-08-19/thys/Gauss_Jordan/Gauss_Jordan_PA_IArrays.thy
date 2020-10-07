(*  
    Title:      Gauss_Jordan_PA_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Obtaining explicitly the invertible matrix which transforms a matrix to its reduced row echelon form over nested iarrays\<close>

theory Gauss_Jordan_PA_IArrays
imports 
  Gauss_Jordan_PA
  Gauss_Jordan_IArrays
begin

subsection\<open>Definitions\<close>

definition "Gauss_Jordan_in_ij_iarrays_PA A' i j =
(let  P = fst A'; A = snd A'; n = least_non_zero_position_of_vector_from_index (column_iarray j A) i; interchange_A = interchange_rows_iarray A i n;
 interchange_P = interchange_rows_iarray P i n; P' = mult_row_iarray interchange_P i (1 / interchange_A !! i !! j)
 in (IArray.of_fun (\<lambda>s. if s = i then P' !! s else row_add_iarray P' s i (- interchange_A !! s !! j) !! s) (nrows_iarray A), Gauss_Jordan_in_ij_iarrays A i j))"

definition Gauss_Jordan_column_k_iarrays_PA :: "('a::{field} iarray iarray \<times> nat \<times> 'a::{field} iarray iarray) => nat => ('a iarray iarray \<times> nat \<times> 'a iarray iarray)"
  where "Gauss_Jordan_column_k_iarrays_PA A' k=(let P = fst A'; i = fst (snd A'); A = snd (snd A') in 
  if (vector_all_zero_from_index (i, (column_iarray k A))) \<or> i = (nrows_iarray A) then (P,i,A) else let Gauss = Gauss_Jordan_in_ij_iarrays_PA (P, A) i k
    in (fst Gauss, i + 1, snd Gauss))"

definition Gauss_Jordan_upt_k_iarrays_PA :: "'a::{field} iarray iarray => nat => ('a::{field} iarray iarray \<times> 'a iarray iarray)"
  where "Gauss_Jordan_upt_k_iarrays_PA A k = (let foldl = foldl Gauss_Jordan_column_k_iarrays_PA (mat_iarray 1 (nrows_iarray A), 0, A) [0..<Suc k] in (fst foldl, snd (snd foldl)))"

definition Gauss_Jordan_iarrays_PA :: "'a::{field} iarray iarray => ('a iarray iarray  \<times> 'a iarray iarray)"
  where "Gauss_Jordan_iarrays_PA A = Gauss_Jordan_upt_k_iarrays_PA A (ncols_iarray A - 1)"

subsection\<open>Proofs\<close>

subsubsection\<open>Properties of @{term "Gauss_Jordan_in_ij_iarrays_PA"}\<close>

lemma Gauss_Jordan_in_ij_iarrays_PA_def'[code]: 
"Gauss_Jordan_in_ij_iarrays_PA A' i j =
(let  P = fst A'; A = snd A'; n = least_non_zero_position_of_vector_from_index (column_iarray j A) i; 
  interchange_A = interchange_rows_iarray A i n; A' = mult_row_iarray interchange_A i (1 / interchange_A !! i !! j);
  interchange_P = interchange_rows_iarray P i n; P' = mult_row_iarray interchange_P i (1 / interchange_A !! i !! j)
 in (IArray.of_fun (\<lambda>s. if s = i then P' !! s else row_add_iarray P' s i (- interchange_A !! s !! j) !! s) (nrows_iarray A),
    (IArray.of_fun (\<lambda>s. if s = i then A' !! s else row_add_iarray A' s i (- interchange_A !! s !! j) !! s) (nrows_iarray A))))" 
unfolding Gauss_Jordan_in_ij_iarrays_PA_def Gauss_Jordan_in_ij_iarrays_def Let_def ..


lemma snd_Gauss_Jordan_in_ij_iarrays_PA:
 shows "snd (Gauss_Jordan_in_ij_iarrays_PA (P, A) i j) = Gauss_Jordan_in_ij_iarrays A i j"
unfolding Gauss_Jordan_in_ij_iarrays_PA_def Gauss_Jordan_in_ij_iarrays_def Let_def snd_conv ..

lemma matrix_to_iarray_snd_Gauss_Jordan_in_ij_iarrays_PA:
 assumes "\<not> vector_all_zero_from_index (to_nat i, vec_to_iarray (column j A))"
 shows "matrix_to_iarray (snd (Gauss_Jordan_in_ij_PA (P,A) i j)) = snd (Gauss_Jordan_in_ij_iarrays_PA (matrix_to_iarray P,matrix_to_iarray A) (to_nat i) (to_nat j))"
by (metis assms matrix_to_iarray_Gauss_Jordan_in_ij snd_Gauss_Jordan_in_ij_PA_eq snd_Gauss_Jordan_in_ij_iarrays_PA)


lemma matrix_to_iarray_fst_Gauss_Jordan_in_ij_iarrays_PA:
 assumes not_all_zero: "\<not> vector_all_zero_from_index (to_nat i, vec_to_iarray (column j A))"
 shows "matrix_to_iarray (fst (Gauss_Jordan_in_ij_PA (P,A) i j)) = fst (Gauss_Jordan_in_ij_iarrays_PA (matrix_to_iarray P,matrix_to_iarray A) (to_nat i) (to_nat j))" 
proof (unfold Gauss_Jordan_in_ij_PA_def Gauss_Jordan_in_ij_iarrays_PA_def Let_def fst_conv snd_conv, rule matrix_to_iarray_eq_of_fun, auto simp del: IArray.length_def IArray.sub_def)
show "vec_to_iarray (mult_row (interchange_rows P i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j) $ i) =
    mult_row_iarray (interchange_rows_iarray (matrix_to_iarray P) (to_nat i)
       (least_non_zero_position_of_vector_from_index (column_iarray (to_nat j) (matrix_to_iarray A)) (to_nat i))) (to_nat i)
     (1 / interchange_rows_iarray (matrix_to_iarray A) (to_nat i)
           (least_non_zero_position_of_vector_from_index (column_iarray (to_nat j) (matrix_to_iarray A)) (to_nat i)) !! to_nat i !! to_nat j) !! to_nat i"
    unfolding vec_to_iarray_column[symmetric]
    unfolding vec_to_iarray_least_non_zero_position_of_vector_from_index'[OF not_all_zero]
    unfolding matrix_to_iarray_interchange_rows[symmetric]
    unfolding matrix_to_iarray_mult_row[symmetric] 
    unfolding matrix_to_iarray_nth
    unfolding interchange_rows_i
    unfolding vec_matrix ..
next
fix ia
show "vec_to_iarray (row_add (mult_row (interchange_rows P i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j)) ia i
            (- interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ ia $ j) $ ia) =
         row_add_iarray (mult_row_iarray (interchange_rows_iarray (matrix_to_iarray P) (to_nat i)
              (least_non_zero_position_of_vector_from_index (column_iarray (to_nat j) (matrix_to_iarray A)) (to_nat i))) (to_nat i)
            (1 / interchange_rows_iarray (matrix_to_iarray A) (to_nat i)
                  (least_non_zero_position_of_vector_from_index (column_iarray (to_nat j) (matrix_to_iarray A)) (to_nat i)) !!
                 to_nat i !! to_nat j)) (to_nat ia) (to_nat i)
          (- interchange_rows_iarray (matrix_to_iarray A) (to_nat i)
              (least_non_zero_position_of_vector_from_index (column_iarray (to_nat j) (matrix_to_iarray A)) (to_nat i)) !!
             to_nat ia !! to_nat j) !! to_nat ia"
    unfolding vec_to_iarray_column[symmetric]
    unfolding vec_to_iarray_least_non_zero_position_of_vector_from_index'[OF not_all_zero]
    unfolding matrix_to_iarray_interchange_rows[symmetric]
    unfolding matrix_to_iarray_mult_row[symmetric]
    unfolding matrix_to_iarray_nth
    unfolding interchange_rows_i
    unfolding matrix_to_iarray_row_add[symmetric]
    unfolding vec_matrix ..
next
show "nrows_iarray (matrix_to_iarray A) = IArray.length (matrix_to_iarray
       (\<chi> s. if s = i then mult_row (interchange_rows P i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j) $ s
             else row_add (mult_row (interchange_rows P i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j)) s i
             (- interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ s $ j) $ s))"
unfolding length_eq_card_rows nrows_eq_card_rows ..
qed


subsubsection\<open>Properties about @{term "Gauss_Jordan_column_k_iarrays_PA"}\<close>

lemma matrix_to_iarray_fst_Gauss_Jordan_column_k_PA:
assumes i: "i\<le>nrows A" and k: "k<ncols A"
shows "matrix_to_iarray (fst (Gauss_Jordan_column_k_PA (P,i,A) k)) = fst (Gauss_Jordan_column_k_iarrays_PA (matrix_to_iarray P, i, matrix_to_iarray A) k)"
proof (cases "i<nrows A")
case True
show ?thesis
unfolding Gauss_Jordan_column_k_PA_def Gauss_Jordan_column_k_iarrays_PA_def Let_def
unfolding snd_conv fst_conv
unfolding matrix_vector_all_zero_from_index
unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
unfolding matrix_to_iarray_nrows
using matrix_to_iarray_fst_Gauss_Jordan_in_ij_iarrays_PA[of "from_nat i" "from_nat k" A P]
using matrix_to_iarray_snd_Gauss_Jordan_in_ij_iarrays_PA[of "from_nat i" "from_nat k" A  P]
unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
unfolding to_nat_from_nat_id[OF k[unfolded ncols_def]]
unfolding vec_to_iarray_column'[OF k] by auto
next
case False
hence i_eq_nrows:"i=nrows A" using i by simp
thus ?thesis 
unfolding Gauss_Jordan_column_k_PA_def Gauss_Jordan_column_k_iarrays_PA_def Let_def
unfolding snd_conv fst_conv unfolding matrix_to_iarray_nrows by fastforce
qed


lemma matrix_to_iarray_snd_Gauss_Jordan_column_k_PA:
assumes i: "i\<le>nrows A" and k: "k<ncols A"
shows "(fst (snd (Gauss_Jordan_column_k_PA (P,i,A) k))) = fst (snd (Gauss_Jordan_column_k_iarrays_PA (matrix_to_iarray P, i, matrix_to_iarray A) k))"
using matrix_to_iarray_Gauss_Jordan_column_k_1[OF k i]
unfolding Gauss_Jordan_column_k_def Gauss_Jordan_column_k_iarrays_def
unfolding Gauss_Jordan_column_k_PA_def Gauss_Jordan_column_k_iarrays_PA_def snd_conv fst_conv Let_def
unfolding snd_Gauss_Jordan_in_ij_iarrays_PA
unfolding snd_if_conv
unfolding snd_Gauss_Jordan_in_ij_PA_eq
by fastforce

lemma matrix_to_iarray_third_Gauss_Jordan_column_k_PA:
assumes i: "i\<le>nrows A" and k: "k<ncols A"
shows "matrix_to_iarray (snd (snd (Gauss_Jordan_column_k_PA (P,i,A) k))) = snd (snd (Gauss_Jordan_column_k_iarrays_PA (matrix_to_iarray P, i, matrix_to_iarray A) k))"
using matrix_to_iarray_Gauss_Jordan_column_k_2[OF k i]
unfolding Gauss_Jordan_column_k_def Gauss_Jordan_column_k_iarrays_def
unfolding Gauss_Jordan_column_k_PA_def Gauss_Jordan_column_k_iarrays_PA_def snd_conv fst_conv Let_def
unfolding snd_Gauss_Jordan_in_ij_iarrays_PA
unfolding snd_if_conv snd_Gauss_Jordan_in_ij_PA_eq by fast


subsubsection\<open>Properties about @{term "Gauss_Jordan_upt_k_iarrays_PA"}\<close>

lemma
assumes "k<ncols A"
shows matrix_to_iarray_fst_Gauss_Jordan_upt_k_PA: "matrix_to_iarray (fst (Gauss_Jordan_upt_k_PA A k)) = fst (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) k)"
and matrix_to_iarray_snd_Gauss_Jordan_upt_k_PA: "matrix_to_iarray (snd (Gauss_Jordan_upt_k_PA A k)) = (snd (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) k))"
and "fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k])) =
    fst (snd (foldl Gauss_Jordan_column_k_iarrays_PA (mat_iarray 1 (nrows_iarray (matrix_to_iarray A)), 0, matrix_to_iarray A) [0..<Suc k]))"
and "fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k])) \<le> nrows A"
using assms
proof (induct k)
assume zero_less_ncols: "0 < ncols A"
show " matrix_to_iarray (fst (Gauss_Jordan_upt_k_PA A 0)) = fst (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) 0)"
unfolding Gauss_Jordan_upt_k_PA_def Gauss_Jordan_upt_k_iarrays_PA_def Let_def fst_conv apply auto
unfolding nrows_eq_card_rows unfolding matrix_to_iarray_mat[symmetric]
by (rule matrix_to_iarray_fst_Gauss_Jordan_column_k_PA, auto simp add: zero_less_ncols)
show "matrix_to_iarray (snd (Gauss_Jordan_upt_k_PA A 0)) = snd (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) 0)"
unfolding Gauss_Jordan_upt_k_PA_def Gauss_Jordan_upt_k_iarrays_PA_def Let_def fst_conv snd_conv apply auto
unfolding nrows_eq_card_rows unfolding matrix_to_iarray_mat[symmetric]
by (rule matrix_to_iarray_third_Gauss_Jordan_column_k_PA, auto simp add: zero_less_ncols)
show "fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc 0])) =
    fst (snd (foldl Gauss_Jordan_column_k_iarrays_PA (mat_iarray 1 (nrows_iarray (matrix_to_iarray A)), 0, matrix_to_iarray A) [0..<Suc 0]))"
apply simp unfolding nrows_eq_card_rows unfolding matrix_to_iarray_mat[symmetric]
by (rule matrix_to_iarray_snd_Gauss_Jordan_column_k_PA, auto simp add: zero_less_ncols)
show "fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc 0])) \<le> nrows A" 
by (simp add: fst_snd_Gauss_Jordan_column_k_PA_eq fst_Gauss_Jordan_column_k)
next
fix k assume "(k < ncols A \<Longrightarrow> matrix_to_iarray (fst (Gauss_Jordan_upt_k_PA A k)) = fst (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) k))"
and "(k < ncols A \<Longrightarrow> matrix_to_iarray (snd (Gauss_Jordan_upt_k_PA A k)) = snd (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) k))"
and "(k < ncols A \<Longrightarrow> fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k])) =
         fst (snd (foldl Gauss_Jordan_column_k_iarrays_PA (mat_iarray 1 (nrows_iarray (matrix_to_iarray A)), 0, matrix_to_iarray A) [0..<Suc k])))"
and "(k < ncols A \<Longrightarrow> fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k])) \<le> nrows A)"
and Suc_k: "Suc k < ncols A"
hence hyp1: "matrix_to_iarray (fst (Gauss_Jordan_upt_k_PA A k)) = fst (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) k)"
and hyp2: "matrix_to_iarray (snd (Gauss_Jordan_upt_k_PA A k)) = snd (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) k)"
and hyp3: "fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k])) =
         fst (snd (foldl Gauss_Jordan_column_k_iarrays_PA (mat_iarray 1 (nrows_iarray (matrix_to_iarray A)), 0, matrix_to_iarray A) [0..<Suc k]))"
and hyp4: "fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k])) \<le> nrows A"
by linarith+

have suc_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [Suc k]" by simp
define A' where "A' = foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k]"
define B where "B = foldl Gauss_Jordan_column_k_iarrays_PA (mat_iarray 1 (nrows_iarray (matrix_to_iarray A)), 0, matrix_to_iarray A) [0..<Suc k]"
have A'_eq: "A' = (fst A', fst (snd A'), snd (snd A'))" by auto

have fst_A': "matrix_to_iarray (fst A') = fst B" unfolding A'_def B_def by (rule hyp1[unfolded Gauss_Jordan_upt_k_PA_def Gauss_Jordan_upt_k_iarrays_PA_def Let_def fst_conv])
have fst_snd_A': "fst (snd A') = fst (snd B)" unfolding A'_def B_def by (rule hyp3[unfolded Gauss_Jordan_upt_k_PA_def Gauss_Jordan_upt_k_iarrays_PA_def ])
have snd_snd_A': "matrix_to_iarray (snd (snd A')) = (snd (snd B))"
unfolding A'_def B_def
by (rule hyp2[unfolded Gauss_Jordan_upt_k_PA_def Gauss_Jordan_upt_k_iarrays_PA_def Let_def fst_conv snd_conv])

show "matrix_to_iarray (fst (Gauss_Jordan_upt_k_PA A (Suc k))) = fst (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) (Suc k))"
proof -
have "matrix_to_iarray (fst (Gauss_Jordan_upt_k_PA A (Suc k))) = matrix_to_iarray (fst (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc (Suc k)]))" 
unfolding Gauss_Jordan_upt_k_PA_def Let_def fst_conv ..
also have "... = matrix_to_iarray (fst (Gauss_Jordan_column_k_PA (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k]) (Suc k)))"
unfolding suc_rw foldl_append unfolding List.foldl.simps ..
also have "... = matrix_to_iarray (fst (Gauss_Jordan_column_k_PA (fst A',fst (snd A'), snd (snd A')) (Suc k)))" unfolding A'_def by simp
also have "... = fst (Gauss_Jordan_column_k_iarrays_PA (matrix_to_iarray (fst A'), fst (snd A'), matrix_to_iarray (snd (snd A'))) (Suc k))"
proof (rule matrix_to_iarray_fst_Gauss_Jordan_column_k_PA)
 show "fst (snd A') \<le> nrows (snd (snd A'))" using hyp4 unfolding nrows_def A'_def .
 show  "Suc k < ncols (snd (snd A'))" using Suc_k unfolding ncols_def .  
qed
also have "... =  fst (Gauss_Jordan_column_k_iarrays_PA (fst B, fst (snd B), snd (snd B)) (Suc k))"
unfolding fst_A' fst_snd_A' snd_snd_A' ..
also have "... = fst (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) (Suc k))" 
unfolding Gauss_Jordan_upt_k_iarrays_PA_def Let_def fst_conv
unfolding suc_rw foldl_append unfolding List.foldl.simps B_def by fastforce
finally show ?thesis .
qed

show "matrix_to_iarray (snd (Gauss_Jordan_upt_k_PA A (Suc k))) = snd (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) (Suc k))"
proof -
  have "matrix_to_iarray (snd (Gauss_Jordan_upt_k_PA A (Suc k))) =  matrix_to_iarray (snd (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc (Suc k)])))" 
  unfolding Gauss_Jordan_upt_k_PA_def Let_def snd_conv ..
also have "... =  matrix_to_iarray (snd (snd (Gauss_Jordan_column_k_PA (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k]) (Suc k))))"
unfolding suc_rw foldl_append unfolding List.foldl.simps ..
also have "... = matrix_to_iarray (snd (snd (Gauss_Jordan_column_k_PA (fst A',fst (snd A'), snd (snd A')) (Suc k))))" unfolding A'_def by simp
also have "... =  snd (snd (Gauss_Jordan_column_k_iarrays_PA (matrix_to_iarray (fst A'), fst (snd A'), matrix_to_iarray (snd (snd A'))) (Suc k)))"
proof (rule matrix_to_iarray_third_Gauss_Jordan_column_k_PA)
 show "fst (snd A') \<le> nrows (snd (snd A'))" using hyp4 unfolding nrows_def A'_def .
 show  "Suc k < ncols (snd (snd A'))" using Suc_k unfolding ncols_def .  
qed
also have "... = snd (snd (Gauss_Jordan_column_k_iarrays_PA (fst B, fst (snd B), snd (snd B)) (Suc k)))"
unfolding fst_A' fst_snd_A' snd_snd_A' ..
also have "... = snd (Gauss_Jordan_upt_k_iarrays_PA (matrix_to_iarray A) (Suc k))" 
unfolding Gauss_Jordan_upt_k_iarrays_PA_def Let_def fst_conv
unfolding suc_rw foldl_append unfolding List.foldl.simps B_def by fastforce
finally show ?thesis .
qed

show "fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc (Suc k)])) =
        fst (snd (foldl Gauss_Jordan_column_k_iarrays_PA (mat_iarray 1 (nrows_iarray (matrix_to_iarray A)), 0, matrix_to_iarray A) [0..<Suc (Suc k)]))"
proof -
have "fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc (Suc k)])) = 
  fst (snd (Gauss_Jordan_column_k_PA (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k]) (Suc k)))"
unfolding suc_rw foldl_append unfolding List.foldl.simps ..
also have "... = fst (snd (Gauss_Jordan_column_k_PA (fst A',fst (snd A'), snd (snd A')) (Suc k)))"
unfolding A'_def by simp
also have "... = fst (snd (Gauss_Jordan_column_k_iarrays_PA (matrix_to_iarray (fst A'),fst (snd A'), matrix_to_iarray (snd (snd A'))) (Suc k)))"
proof (rule matrix_to_iarray_snd_Gauss_Jordan_column_k_PA)
 show "fst (snd A') \<le> nrows (snd (snd A'))" using hyp4 unfolding nrows_def A'_def .
 show "Suc k < ncols (snd (snd A'))" using Suc_k unfolding ncols_def .
qed
also have  "\<dots> = fst (snd (Gauss_Jordan_column_k_iarrays_PA (fst B,fst (snd B), snd (snd B)) (Suc k)))"
unfolding fst_A' fst_snd_A' snd_snd_A' ..
also have "... = fst (snd (foldl Gauss_Jordan_column_k_iarrays_PA (mat_iarray 1 (nrows_iarray (matrix_to_iarray A)), 0, matrix_to_iarray A) [0..<Suc (Suc k)]))"
unfolding B_def unfolding nrows_eq_card_rows unfolding matrix_to_iarray_mat[symmetric] by auto
finally show ?thesis .
qed
show "fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc (Suc k)])) \<le> nrows A"
by (metis snd_foldl_Gauss_Jordan_column_k_eq Suc_k fst_foldl_Gauss_Jordan_column_k_less)
qed

subsubsection\<open>Properties about @{term "Gauss_Jordan_iarrays_PA"}\<close>

lemma matrix_to_iarray_fst_Gauss_Jordan_PA: 
shows "matrix_to_iarray (fst (Gauss_Jordan_PA A)) = fst (Gauss_Jordan_iarrays_PA (matrix_to_iarray A))"
  unfolding Gauss_Jordan_PA_def Gauss_Jordan_iarrays_PA_def 
  using matrix_to_iarray_fst_Gauss_Jordan_upt_k_PA[of "ncols A - 1" A]
  by (simp add: ncols_def ncols_eq_card_columns)



lemma matrix_to_iarray_snd_Gauss_Jordan_PA: 
shows "matrix_to_iarray (snd (Gauss_Jordan_PA A)) = snd (Gauss_Jordan_iarrays_PA (matrix_to_iarray A))"
  unfolding Gauss_Jordan_PA_def Gauss_Jordan_iarrays_PA_def 
  using matrix_to_iarray_snd_Gauss_Jordan_upt_k_PA[of "ncols A - 1" A]
  by (simp add: ncols_def ncols_eq_card_columns)

lemma Gauss_Jordan_iarrays_PA_mult:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "snd (Gauss_Jordan_iarrays_PA (matrix_to_iarray A)) = fst (Gauss_Jordan_iarrays_PA (matrix_to_iarray A)) **i (matrix_to_iarray A)"
proof -
have "snd (Gauss_Jordan_PA A) = fst (Gauss_Jordan_PA A) ** A" using fst_Gauss_Jordan_PA[of A] ..
hence "matrix_to_iarray (snd (Gauss_Jordan_PA A)) = matrix_to_iarray (fst (Gauss_Jordan_PA A) ** A)" by simp
thus ?thesis unfolding matrix_to_iarray_snd_Gauss_Jordan_PA matrix_to_iarray_matrix_matrix_mult matrix_to_iarray_fst_Gauss_Jordan_PA .
qed


lemma snd_snd_Gauss_Jordan_column_k_iarrays_PA_eq: 
shows "snd (snd (Gauss_Jordan_column_k_iarrays_PA (P,i,A) k)) = snd (Gauss_Jordan_column_k_iarrays (i,A) k)"
unfolding Gauss_Jordan_column_k_iarrays_PA_def Gauss_Jordan_column_k_iarrays_def unfolding Let_def snd_conv fst_conv unfolding snd_Gauss_Jordan_in_ij_iarrays_PA by auto


lemma fst_snd_Gauss_Jordan_column_k_iarrays_PA_eq: 
shows "fst (snd (Gauss_Jordan_column_k_iarrays_PA (P,i,A) k)) = fst (Gauss_Jordan_column_k_iarrays (i,A) k)"
unfolding Gauss_Jordan_column_k_iarrays_PA_def Gauss_Jordan_column_k_iarrays_def unfolding Let_def snd_conv fst_conv by auto


lemma foldl_Gauss_Jordan_column_k_iarrays_eq:
"snd (foldl Gauss_Jordan_column_k_iarrays_PA (B, 0, A) [0..<k]) = foldl Gauss_Jordan_column_k_iarrays (0, A) [0..<k]"
proof (induct k)
case 0
show ?case by simp
case (Suc k)
have suc_rw: "[0..<Suc k] = [0..<k] @ [k]" by simp
show ?case 
unfolding suc_rw foldl_append unfolding List.foldl.simps 
by (metis Suc.hyps fst_snd_Gauss_Jordan_column_k_iarrays_PA_eq snd_snd_Gauss_Jordan_column_k_iarrays_PA_eq surjective_pairing)
qed

lemma snd_Gauss_Jordan_upt_k_iarrays_PA:
shows "snd (Gauss_Jordan_upt_k_iarrays_PA A k) = (Gauss_Jordan_upt_k_iarrays A k)"
unfolding Gauss_Jordan_upt_k_iarrays_PA_def Gauss_Jordan_upt_k_iarrays_def Let_def
using foldl_Gauss_Jordan_column_k_iarrays_eq[of "mat_iarray 1 (nrows_iarray A)" A "Suc k"] by simp

lemma snd_Gauss_Jordan_iarrays_PA_eq: "snd (Gauss_Jordan_iarrays_PA A) = Gauss_Jordan_iarrays A"
unfolding Gauss_Jordan_iarrays_def Gauss_Jordan_iarrays_PA_def
using snd_Gauss_Jordan_upt_k_iarrays_PA by auto


end
