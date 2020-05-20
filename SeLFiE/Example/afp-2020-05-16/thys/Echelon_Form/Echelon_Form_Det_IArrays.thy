(*  
    Title:      Echelon_Form_Det_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Determinant of matrices computed using immutable arrays\<close>

theory Echelon_Form_Det_IArrays
imports 
  Echelon_Form_Det
  Echelon_Form_IArrays
begin

subsection\<open>Definitions\<close>

definition echelon_form_of_column_k_det_iarrays :: 
          "'a::{bezout_ring} \<times> 'a iarray iarray \<times> nat \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) 
          \<Rightarrow> nat 
          \<Rightarrow> 'a \<times> 'a iarray iarray \<times> nat \<times> ('a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a)"
 where  
 "echelon_form_of_column_k_det_iarrays A' k = 
    (let (det_P, A, i, bezout) = A'
      in if ((i \<noteq> nrows_iarray A) \<and> (A !! i !! k = 0) 
            \<and> (\<not> vector_all_zero_from_index (i + 1, (column_iarray k A)))) 
         then (-1 * det_P, echelon_form_of_column_k_iarrays (A, i, bezout) k) 
         else (det_P,echelon_form_of_column_k_iarrays (A,i,bezout) k))"

definition "echelon_form_of_upt_k_det_iarrays A' k bezout = 
      (let A = snd A'; 
           f = foldl echelon_form_of_column_k_det_iarrays (1, A, 0, bezout) [0..<Suc k] 
       in (fst f, fst (snd f)))"

definition echelon_form_of_det_iarrays :: 
  "'a::{bezout_ring} iarray iarray 
    \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a \<times> 'a \<times> 'a \<times> 'a) 
    \<Rightarrow> ('a \<times> ('a iarray iarray))"
  where 
  "echelon_form_of_det_iarrays A bezout = 
      echelon_form_of_upt_k_det_iarrays (1::'a, A) (ncols_iarray A - 1) bezout"

definition "det_iarrays_rings A = 
    (let A' = echelon_form_of_det_iarrays A euclid_ext2 
     in 1 div (fst A') * prod_list (map (\<lambda>i. (snd A') !! i !! i) [0..<nrows_iarray A]))"

subsection\<open>Properties\<close>

subsubsection\<open>Echelon Form of column k\<close>

lemma vector_all_zero_from_index3:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  shows "(\<exists>m>i. A $ m $ k \<noteq> 0) 
  = (\<not> vector_all_zero_from_index (to_nat i + 1, vec_to_iarray (column k A)))"
  using matrix_vector_all_zero_from_index2 
proof -
  have "(\<forall>m>i. A $ m $ k = 0) = (vector_all_zero_from_index (to_nat i + 1, vec_to_iarray (column k A)))"
    using matrix_vector_all_zero_from_index2[of i A k] by auto
  hence "(\<not> (\<forall>m>i. A $ m $ k = 0)) 
    = (\<not>(vector_all_zero_from_index (to_nat i + 1, vec_to_iarray (column k A))))"
    by auto
  thus ?thesis by auto
qed

lemma fst_matrix_to_iarray_echelon_form_of_column_k_det:
  assumes k: "k<ncols A" and i: "i\<le>nrows A"
  shows "fst ((echelon_form_of_column_k_det bezout) (det_P, A, i) k)
  = fst (echelon_form_of_column_k_det_iarrays (det_P, matrix_to_iarray A, i, bezout) k)"
proof (cases "i<nrows A")
  case True
  have ex_rw: "(\<exists>m>from_nat i. A $ m $ from_nat k \<noteq> 0) 
    = (\<not> vector_all_zero_from_index (i + 1, column_iarray k (matrix_to_iarray A)))"
    using vector_all_zero_from_index3[of "from_nat i" A "from_nat k"] 
    unfolding vec_to_iarray_column
    unfolding to_nat_from_nat_id[OF k[unfolded ncols_def]]
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]] .
  have Aik: "matrix_to_iarray A !! i !! k = A $ (from_nat i) $ (from_nat k)"
    by (metis True k matrix_to_iarray_nth ncols_def nrows_def to_nat_from_nat_id)
  show ?thesis
    unfolding echelon_form_of_column_k_det_iarrays_def echelon_form_of_column_k_det_def
    unfolding Let_def 
    unfolding split_beta
    unfolding fst_conv snd_conv 
    unfolding matrix_to_iarray_nrows
    unfolding ex_rw Aik by auto
next
  case False
  hence i2: "i=nrows A" using i by simp
  thus ?thesis
    unfolding echelon_form_of_column_k_det_iarrays_def echelon_form_of_column_k_det_def
    unfolding Let_def fst_conv snd_conv 
    unfolding matrix_to_iarray_nrows
    unfolding i2 unfolding matrix_to_iarray_nrows by auto
qed

lemma snd_echelon_form_of_column_k_det:
  shows "(snd (echelon_form_of_column_k_det_iarrays (det_P, A, i, bezout) k))
  = echelon_form_of_column_k_iarrays (A,i,bezout) k"
  unfolding echelon_form_of_column_k_det_iarrays_def Let_def by auto


lemma fst_snd_echelon_form_of_column_k_le_nrows: 
  assumes "i\<le>nrows A"
  shows "snd ((echelon_form_of_column_k bezout) (A, i) k) \<le> nrows A"
  using assms 
  unfolding echelon_form_of_column_k_def Let_def fst_conv snd_conv
  unfolding nrows_def by auto

lemma fst_snd_snd_echelon_form_of_column_k_det_le_nrows:
  assumes "i\<le>nrows A"
  shows "snd (snd ((echelon_form_of_column_k_det bezout) (n, A, i) k)) \<le> nrows A"
  unfolding echelon_form_of_column_k_det_def Let_def fst_conv snd_conv
  by (simp add: assms fst_snd_echelon_form_of_column_k_le_nrows)

subsubsection\<open>Echelon Form up to column k\<close>

lemma snd_snd_snd_foldl_echelon_form_of_column_k_det_iarrays:
  "snd (snd (snd (foldl echelon_form_of_column_k_det_iarrays (n, A, 0, bezout) [0..<k]))) = bezout"
proof (induct k)
  case 0
  show ?case by auto
next
  case (Suc k)
  show ?case 
    apply auto 
    apply (simp only: echelon_form_of_column_k_det_iarrays_def Let_def)
    apply (auto simp add: split_beta echelon_form_of_column_k_iarrays_def Let_def Suc.hyps)
    done
qed

(*lemma snd_snd_snd_echelon_form_of_column_k_det:
  "snd (snd (snd (foldl echelon_form_of_column_k_det (n, A, 0, bezout) [0..<k]))) = bezout"
  by (metis snd_foldl_ef_det_eq snd_snd_foldl_echelon_form_of_column_k)*)

lemma matrix_to_iarray_echelon_form_of_column_k_det:
  assumes "k<ncols A" and "i\<le>nrows A"
  shows "matrix_to_iarray (fst (snd ((echelon_form_of_column_k_det bezout) (n, A, i) k))) 
  = (fst (snd (echelon_form_of_column_k_det_iarrays (n, matrix_to_iarray A, i, bezout) k)))"
  unfolding snd_echelon_form_of_column_k_det 
  unfolding echelon_form_of_column_k_det_def Let_def fst_conv snd_conv 
  using assms matrix_to_iarray_echelon_form_of_column_k by auto


lemma fst_snd_snd_echelon_form_of_column_k_det:
  assumes "k < ncols A"
  and "i \<le> nrows A"
  shows "snd (snd ((echelon_form_of_column_k_det bezout) (n,A,i) k)) 
  = fst (snd (snd (echelon_form_of_column_k_det_iarrays (n,matrix_to_iarray A, i, bezout) k)))"
  unfolding snd_echelon_form_of_column_k_det_eq
  unfolding snd_echelon_form_of_column_k_det
  by (rule fst_snd_matrix_to_iarray_echelon_form_of_column_k[OF assms])

lemma 
  fixes A::"'a::{bezout_domain}^'cols::{mod_type}^'rows::{mod_type}"
  assumes "k<ncols A"
  shows matrix_to_iarray_fst_echelon_form_of_upt_k_det: 
  "fst ((echelon_form_of_upt_k_det bezout) (1::'a,A) k) 
  = fst (echelon_form_of_upt_k_det_iarrays (1::'a,matrix_to_iarray A) k bezout)"
  and matrix_to_iarray_snd_echelon_form_of_upt_k_det:
  "matrix_to_iarray ((snd ((echelon_form_of_upt_k_det bezout) (1::'a,A) k))) 
  = (snd (echelon_form_of_upt_k_det_iarrays (1::'a, matrix_to_iarray A) k bezout))"
  and "snd (snd (foldl (echelon_form_of_column_k_det bezout) (1::'a,A,0) [0..<Suc k])) \<le> nrows A"
  and "fst (snd (snd (foldl echelon_form_of_column_k_det_iarrays 
  (1::'a,matrix_to_iarray A,0,bezout) [0..<Suc k]))) = snd (snd 
  (foldl (echelon_form_of_column_k_det bezout) (1::'a,A,0) [0..<Suc k]))"
  using assms
proof (induct k)
  show "fst ((echelon_form_of_upt_k_det bezout) (1, A) 0) 
    = fst (echelon_form_of_upt_k_det_iarrays (1, matrix_to_iarray A) 0 bezout)"
    unfolding echelon_form_of_upt_k_det_def echelon_form_of_upt_k_det_iarrays_def Let_def
    by (auto, metis fst_matrix_to_iarray_echelon_form_of_column_k_det le0 ncols_not_0 neq0_conv)
  show "matrix_to_iarray (snd ((echelon_form_of_upt_k_det bezout) (1, A) 0)) =
    snd (echelon_form_of_upt_k_det_iarrays (1, matrix_to_iarray A) 0 bezout)"
    unfolding echelon_form_of_upt_k_det_def echelon_form_of_upt_k_det_iarrays_def Let_def
    by (auto, metis le0 matrix_to_iarray_echelon_form_of_column_k ncols_not_0 neq0_conv 
      snd_echelon_form_of_column_k_det snd_echelon_form_of_column_k_det_eq)
  show "snd (snd (foldl (echelon_form_of_column_k_det bezout)(1, A, 0) [0..<Suc 0])) \<le> nrows A"
    by (simp add: fst_snd_snd_echelon_form_of_column_k_det_le_nrows)
  show "fst (snd (snd (foldl echelon_form_of_column_k_det_iarrays (1, matrix_to_iarray A, 0, bezout) [0..<Suc 0]))) =
    snd (snd (foldl (echelon_form_of_column_k_det bezout) (1, A, 0) [0..<Suc 0]))"
    by (auto, metis fst_snd_matrix_to_iarray_echelon_form_of_column_k le0 ncols_not_0 neq0_conv 
      snd_echelon_form_of_column_k_det snd_echelon_form_of_column_k_det_eq)
next
  fix k
  assume "(k < ncols A \<Longrightarrow> fst ((echelon_form_of_upt_k_det bezout) (1::'a, A) k) 
    = fst (echelon_form_of_upt_k_det_iarrays (1::'a, matrix_to_iarray A) k bezout))"
    and "(k < ncols A \<Longrightarrow>
    matrix_to_iarray (snd ((echelon_form_of_upt_k_det bezout) (1::'a, A) k)) 
    = snd (echelon_form_of_upt_k_det_iarrays (1::'a, matrix_to_iarray A) k bezout))"
    and "(k < ncols A \<Longrightarrow> 
    snd (snd (foldl (echelon_form_of_column_k_det bezout) (1::'a, A, 0) [0..<Suc k])) \<le> nrows A)"
    and "(k < ncols A \<Longrightarrow>
    fst (snd (snd (foldl echelon_form_of_column_k_det_iarrays (1::'a, matrix_to_iarray A, 0, bezout) [0..<Suc k]))) =
    snd (snd (foldl (echelon_form_of_column_k_det bezout) (1::'a, A, 0) [0..<Suc k])))" 
    and S: "Suc k < ncols A"
  hence hyp1: "fst ((echelon_form_of_upt_k_det bezout) (1::'a, A) k) 
    = fst (echelon_form_of_upt_k_det_iarrays (1::'a, matrix_to_iarray A) k bezout)"
    and hyp2: "matrix_to_iarray (snd ((echelon_form_of_upt_k_det bezout) (1::'a, A) k)) 
    = snd (echelon_form_of_upt_k_det_iarrays (1::'a, matrix_to_iarray A) k bezout)" 
    and hyp3: "snd (snd (foldl (echelon_form_of_column_k_det bezout) (1::'a, A, 0) [0..<Suc k])) 
    \<le> nrows A"
    and hyp4: "fst (snd (snd (foldl echelon_form_of_column_k_det_iarrays 
    (1::'a, matrix_to_iarray A, 0, bezout) [0..<Suc k])))
    = snd (snd (foldl (echelon_form_of_column_k_det bezout) (1::'a, A, 0) [0..<Suc k]))"
    by auto
  have list_rw: "[0..<Suc (Suc k)] = [0..<(Suc k)] @ [Suc k]" by simp
  let ?f = "foldl (echelon_form_of_column_k_det bezout) (1, A, 0) [0..<Suc k]"
  have f_rw: "?f= (fst ?f, fst (snd ?f), snd (snd ?f))" by simp
  let ?g="(foldl echelon_form_of_column_k_det_iarrays (1, matrix_to_iarray A, 0, bezout) [0..<Suc k])"
  have g_rw: "?g = (fst ?g, fst (snd ?g), fst (snd (snd ?g)), snd (snd (snd ?g)))" by simp
  have rw1: "fst ?g = fst ?f" 
    using hyp1[unfolded echelon_form_of_upt_k_det_def echelon_form_of_upt_k_det_iarrays_def Let_def 
      fst_conv snd_conv] ..
  have rw2: "fst (snd ?g) = matrix_to_iarray (fst (snd ?f))" 
    using hyp2[unfolded echelon_form_of_upt_k_det_def 
      echelon_form_of_upt_k_det_iarrays_def Let_def snd_conv] ..
  have rw3: "fst (snd (snd ?g)) = snd (snd ?f)" 
    using hyp4 .
  (*have rw4: "snd (snd (snd ?g)) = snd (snd (snd ?f))" 
    unfolding snd_snd_snd_foldl_echelon_form_of_column_k_det_iarrays
    unfolding snd_snd_snd_echelon_form_of_column_k_det ..*)
  show "fst ((echelon_form_of_upt_k_det bezout) (1, A) (Suc k)) 
    = fst (echelon_form_of_upt_k_det_iarrays (1, matrix_to_iarray A) (Suc k) bezout)"
    unfolding echelon_form_of_upt_k_det_iarrays_def echelon_form_of_upt_k_det_def Let_def fst_conv snd_conv
    unfolding list_rw foldl_append
    unfolding List.foldl.simps
    apply (subst f_rw)
    apply (subst g_rw)
    unfolding rw1[symmetric] rw2 rw3
    unfolding snd_snd_snd_foldl_echelon_form_of_column_k_det_iarrays
  proof (rule fst_matrix_to_iarray_echelon_form_of_column_k_det)
    show "Suc k < ncols (fst (snd ?f))" using S unfolding ncols_def .
    show " snd (snd (foldl (echelon_form_of_column_k_det bezout) (1, A, 0) [0..<Suc k]))
    \<le> nrows (fst (snd (foldl (echelon_form_of_column_k_det bezout) (1, A, 0) [0..<Suc k])))"
    by (metis hyp3 nrows_def)
  qed
  show "matrix_to_iarray (snd ((echelon_form_of_upt_k_det bezout) (1, A) (Suc k))) =
    snd (echelon_form_of_upt_k_det_iarrays (1, matrix_to_iarray A) (Suc k) bezout)"
    unfolding echelon_form_of_upt_k_det_iarrays_def echelon_form_of_upt_k_det_def Let_def fst_conv snd_conv
    unfolding list_rw foldl_append
    unfolding List.foldl.simps
    apply (subst f_rw)
    apply (subst g_rw)
    unfolding rw1[symmetric] rw2 rw3 unfolding snd_snd_snd_foldl_echelon_form_of_column_k_det_iarrays
  proof (rule matrix_to_iarray_echelon_form_of_column_k_det)
    show "Suc k < ncols (fst (snd ?f))" using S unfolding ncols_def .
    show "snd (snd (foldl (echelon_form_of_column_k_det bezout) (1, A, 0) [0..<Suc k]))
    \<le> nrows (fst (snd (foldl (echelon_form_of_column_k_det bezout) (1, A, 0) [0..<Suc k])))"
    by (metis hyp3 nrows_def)
  qed
  show "snd (snd (foldl (echelon_form_of_column_k_det bezout) (1, A, 0) [0..<Suc (Suc k)])) \<le> nrows A"
    unfolding list_rw foldl_append List.foldl.simps
    apply (subst f_rw) 
    using fst_snd_snd_echelon_form_of_column_k_det_le_nrows
    by (metis hyp3 nrows_def)
  show "fst (snd (snd (foldl echelon_form_of_column_k_det_iarrays 
    (1, matrix_to_iarray A, 0, bezout) [0..<Suc (Suc k)]))) 
    = snd (snd (foldl (echelon_form_of_column_k_det bezout) (1, A, 0) [0..<Suc (Suc k)]))"
    unfolding echelon_form_of_upt_k_det_iarrays_def echelon_form_of_upt_k_det_def Let_def fst_conv snd_conv
    unfolding list_rw foldl_append
    unfolding List.foldl.simps
    apply (subst f_rw)
    apply (subst g_rw)
    unfolding rw1[symmetric] rw2 rw3 
     unfolding snd_snd_snd_foldl_echelon_form_of_column_k_det_iarrays
  proof (rule fst_snd_snd_echelon_form_of_column_k_det[symmetric])
    show "Suc k < ncols (fst (snd ?f))" using S unfolding ncols_def .
    show "snd (snd (foldl (echelon_form_of_column_k_det bezout) (1, A, 0) [0..<Suc k]))
    \<le> nrows (fst (snd (foldl (echelon_form_of_column_k_det bezout) (1, A, 0) [0..<Suc k])))"
    by (metis hyp3 nrows_def)
  qed
qed

subsubsection\<open>Echelon Form\<close>

lemma matrix_to_iarray_echelon_form_of_det[code_unfold]:
  "matrix_to_iarray (snd (echelon_form_of_det A bezout)) 
  = snd (echelon_form_of_det_iarrays (matrix_to_iarray A) bezout)"
  unfolding echelon_form_of_det_def echelon_form_of_det_iarrays_def
  unfolding matrix_to_iarray_ncols[symmetric]
  by (rule matrix_to_iarray_snd_echelon_form_of_upt_k_det, simp add: ncols_def)

lemma fst_echelon_form_of_det[code_unfold]:
  "(fst (echelon_form_of_det A bezout)) 
  = fst (echelon_form_of_det_iarrays (matrix_to_iarray A) bezout)"
  unfolding echelon_form_of_det_def echelon_form_of_det_iarrays_def
  unfolding matrix_to_iarray_ncols[symmetric]
  by (rule matrix_to_iarray_fst_echelon_form_of_upt_k_det, simp add: ncols_def)

subsubsection\<open>Computing the determinant\<close>

lemma det_echelon_form_of_euclidean_iarrays[code]:
  fixes A::"'a::{euclidean_ring_gcd}^'n::{mod_type}^'n::{mod_type}"
  shows "det A = (let A' = echelon_form_of_det_iarrays (matrix_to_iarray A) euclid_ext2 
  in 1 div (fst A') 
  * prod_list (map (\<lambda>i. (snd A') !! i !! i) [0..<nrows_iarray (matrix_to_iarray A)]))"
proof -
  let ?f="(\<lambda>i. snd (echelon_form_of_det_iarrays (matrix_to_iarray A) euclid_ext2) !! i !! i)"
  have "prod_list (map ?f [0..<nrows_iarray (matrix_to_iarray A)]) 
    = prod ?f (set [0..<nrows_iarray (matrix_to_iarray A)])" 
    by (metis (mono_tags, lifting) distinct_upt prod.distinct_set_conv_list)  
  also have "... = prod (\<lambda>i. snd (echelon_form_of_det A euclid_ext2) $ i $ i) (UNIV:: 'n set)"
  proof (rule prod.reindex_cong[of "to_nat::('n=>nat)"])
    show "inj (to_nat::('n=>nat))" by (metis strict_mono_imp_inj_on strict_mono_to_nat)
    show "set [0..<nrows_iarray (matrix_to_iarray A)] = range (to_nat::'n=>nat)"
      unfolding nrows_eq_card_rows using bij_to_nat[where ?'a='n]
      unfolding bij_betw_def 
      unfolding atLeast0LessThan atLeast_upt  by auto
    fix x 
    show "snd (echelon_form_of_det_iarrays (matrix_to_iarray A) euclid_ext2) !! to_nat x !! to_nat x
      = snd (echelon_form_of_det A euclid_ext2) $ x $ x"
      unfolding matrix_to_iarray_echelon_form_of_det[symmetric]
      unfolding matrix_to_iarray_nth ..
  qed
  finally have *:"prod_list (map (\<lambda>i. snd (echelon_form_of_det_iarrays 
    (matrix_to_iarray A) euclid_ext2) !! i !! i) [0..<nrows_iarray (matrix_to_iarray A)]) =
    (\<Prod>i\<in>UNIV. snd (echelon_form_of_det A euclid_ext2) $ i $ i)" .  
  have "det A = 1 div (fst (echelon_form_of_det A euclid_ext2)) 
    * prod (\<lambda>i. snd (echelon_form_of_det A euclid_ext2) $ i $ i) (UNIV:: 'n set)"
    unfolding det_echelon_form_of_euclidean ..
  also have "... = (let A' = echelon_form_of_det_iarrays (matrix_to_iarray A) euclid_ext2
    in 1 div (fst A') 
    * prod_list (map (\<lambda>i. (snd A') !! i !! i) [0..<nrows_iarray (matrix_to_iarray A)]))"
    unfolding Let_def unfolding * fst_echelon_form_of_det ..
  finally show ?thesis .
qed


corollary matrix_to_iarray_det_euclidean_ring:
  fixes A::"'a::{euclidean_ring_gcd}^'n::{mod_type}^'n::{mod_type}"
  shows "det A = det_iarrays_rings (matrix_to_iarray A)"
  unfolding det_echelon_form_of_euclidean_iarrays det_iarrays_rings_def ..


subsubsection\<open>Computing the characteristic polynomial of a matrix\<close>

definition "mat2matofpoly_iarrays A 
  = tabulate2 (nrows_iarray A) (ncols_iarray A)  (\<lambda>i j. [:A !! i !! j:])"

lemma matrix_to_iarray_mat2matofpoly[code_unfold]: 
  "matrix_to_iarray (mat2matofpoly A) = mat2matofpoly_iarrays (matrix_to_iarray A)"
  unfolding mat2matofpoly_def mat2matofpoly_iarrays_def tabulate2_def 
proof (rule matrix_to_iarray_eq_of_fun, auto)
  show "nrows_iarray (matrix_to_iarray A) = length (IArray.list_of (matrix_to_iarray (\<chi> i j. [:A $ i $ j:])))"
    unfolding nrows_iarray_def matrix_to_iarray_def by simp
  fix i 
  show "vec_to_iarray (\<chi> j. [:A $ i $ j:]) =
    IArray (map (\<lambda>j. [:IArray.list_of (IArray.list_of (matrix_to_iarray A) ! mod_type_class.to_nat i) ! j:])
    [0..<ncols_iarray (matrix_to_iarray A)])"
    unfolding vec_to_iarray_def
    unfolding matrix_to_iarray_ncols[symmetric] unfolding ncols_def
    by (auto, metis IArray.sub_def vec_matrix vec_to_iarray_nth)
qed

text\<open>The following two lemmas must be added to the file \<open>Matrix_To_IArray\<close> 
  of the AFP Gauss-Jordan development.\<close>

lemma vec_to_iarray_minus[code_unfold]: "vec_to_iarray (a - b) 
  = (vec_to_iarray a) - (vec_to_iarray b)"
  unfolding vec_to_iarray_def
  unfolding minus_iarray_def by auto

lemma matrix_to_iarray_minus[code_unfold]: "matrix_to_iarray (A - B) 
  = (matrix_to_iarray A) - (matrix_to_iarray B)"
  unfolding matrix_to_iarray_def o_def
  by (simp add: minus_iarray_def Let_def vec_to_iarray_minus)

definition "charpoly_iarrays A 
  = det_iarrays_rings (mat_iarray (monom 1 (Suc 0)) (nrows_iarray A) - mat2matofpoly_iarrays A)"

lemma matrix_to_iarray_charpoly[code]: "charpoly A = charpoly_iarrays (matrix_to_iarray A)"
  unfolding charpoly_def charpoly_iarrays_def
  unfolding matrix_to_iarray_mat2matofpoly[symmetric]
  unfolding matrix_to_iarray_nrows[symmetric] nrows_def
  unfolding matrix_to_iarray_mat[symmetric]
  unfolding matrix_to_iarray_minus[symmetric]
  unfolding det_iarrays_rings_def
  unfolding det_echelon_form_of_euclidean_iarrays ..

end
