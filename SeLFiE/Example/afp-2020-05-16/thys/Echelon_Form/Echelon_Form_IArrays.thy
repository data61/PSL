(*  
    Title:      Echelon_Form_IArrays.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Echelon Form refined to immutable arrays\<close>

theory Echelon_Form_IArrays
imports
  Echelon_Form
  Gauss_Jordan.Gauss_Jordan_IArrays
begin

subsection\<open>The algorithm over immutable arrays\<close>

definition
  "bezout_matrix_iarrays A a b j bezout =
    tabulate2 (nrows_iarray A) (nrows_iarray A) 
      (let (p, q, u, v, d) = bezout (A !! a !! j) (A !! b !! j)      
        in (%x y. if x = a \<and> y = a then p else 
              if x = a \<and> y = b then q else 
              if x = b \<and> y = a then u else 
              if x = b \<and> y = b then v else 
              if x = y then 1 else 0))"

primrec 
  bezout_iterate_iarrays :: "'a::{bezout_ring} iarray iarray \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat
                              \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a)) 
                              \<Rightarrow> 'a iarray iarray"
where "bezout_iterate_iarrays A 0 i j bezout = A"
      | "bezout_iterate_iarrays A (Suc n) i j bezout = 
        (if (Suc n) \<le> i 
          then A 
          else bezout_iterate_iarrays (bezout_matrix_iarrays A i (Suc n) j bezout **i A) n i j bezout)"

definition
  "echelon_form_of_column_k_iarrays A' k = 
    (let (A, i, bezout) =  A'; 
          nrows_A = nrows_iarray A;
          column_Ak = column_iarray k A;
          all_zero_below_i = vector_all_zero_from_index (i+1, column_Ak)
      in if i = nrows_A \<or> (A !! i !! k = 0) \<and> all_zero_below_i 
            then (A, i, bezout) else 
         if all_zero_below_i
            then (A, i + 1, bezout) else
                let n = least_non_zero_position_of_vector_from_index column_Ak i; 
                    interchange_A = interchange_rows_iarray A i n
                in
          (bezout_iterate_iarrays interchange_A (nrows_A - 1) i k bezout, i + 1, bezout))"

definition "echelon_form_of_upt_k_iarrays A k bezout 
  = fst (foldl echelon_form_of_column_k_iarrays (A,0,bezout) [0..<Suc k])"

definition "echelon_form_of_iarrays A bezout 
  = echelon_form_of_upt_k_iarrays A (ncols_iarray A - 1) bezout"

subsection\<open>Properties\<close>

subsubsection\<open>Bezout Matrix for immutable arrays\<close>

lemma matrix_to_iarray_bezout_matrix:
  shows "matrix_to_iarray (bezout_matrix A a b j bezout) 
  = bezout_matrix_iarrays (matrix_to_iarray A) (to_nat a) (to_nat b) (to_nat j) bezout"
  (is "?lhs = ?rhs")
proof -
  have n: "nrows_iarray (IArray (map (vec_to_iarray \<circ> ($) A \<circ> from_nat) [0..<CARD('b)])) 
    = CARD('b)" unfolding nrows_iarray_def vec_to_iarray_def o_def by auto
  have rw1:"(map (\<lambda>x. IArray.of_fun 
    (\<lambda>i. A $ from_nat x $ from_nat i) CARD('c)) [0..<CARD('b)] ! to_nat a !! to_nat j) = A $ a $ j"
    by (metis (erased, lifting) from_nat_to_nat_id length_upt minus_nat.diff_0 nth_map 
      nth_upt of_fun_nth plus_nat.add_0 to_nat_less_card)
  have rw2: "(map (\<lambda>x. IArray.of_fun 
    (\<lambda>i. A $ from_nat x $ from_nat i) CARD('c)) [0..<CARD('b)] ! to_nat b !! to_nat j) = (A $ b $ j)"
    by (metis (erased, lifting) from_nat_to_nat_id length_upt minus_nat.diff_0 nth_map 
      nth_upt of_fun_nth plus_nat.add_0 to_nat_less_card)
  have rw3: "IArray (map (\<lambda>x. IArray.of_fun 
    (\<lambda>i. A $ from_nat x $ from_nat i) CARD('c)) [0..<CARD('b)]) !! to_nat a !! to_nat j = A $ a $ j"
    by (metis IArray.sub_def list_of.simps rw1)
  have rw4: "IArray (map (\<lambda>x. IArray.of_fun
    (\<lambda>i. A $ from_nat x $ from_nat i) CARD('c)) [0..<CARD('b)]) !! to_nat b !! to_nat j = A $ b $ j"
    by (metis IArray.sub_def list_of.simps rw2) 
  show ?thesis
    unfolding matrix_to_iarray_def bezout_matrix_iarrays_def tabulate2_def 
    apply auto unfolding n apply (rule map_ext, auto simp add: bezout_matrix_def Let_def)
    unfolding o_def vec_to_iarray_def  Let_def 
    unfolding IArray.sub_def[symmetric] rw1 rw2 rw3 rw4
    unfolding IArray.of_fun_def iarray.inject
    apply (rule map_ext) unfolding vec_lambda_beta
  proof
    fix x xa 
    assume x: "x < CARD('b)"
    assume "xa \<in> set [0..<CARD('b)]"
    hence xa: "xa < CARD('b)" using atLeast_upt by blast
    have rw5: "(from_nat x = a) = (x = to_nat a)"
      using x from_nat_not_eq from_nat_to_nat_id by blast
    have rw6: "(from_nat x = b) = (x = to_nat b)"
        by (metis x from_nat_to_nat_id to_nat_from_nat_id)
    have rw7: "(from_nat xa = b) = (xa = to_nat b)" 
        by (metis xa from_nat_to_nat_id to_nat_from_nat_id)
    have rw8: "((from_nat x::'b) = (from_nat xa::'b)) = (x = xa)"
        by (metis from_nat_not_eq x xa)
    have rw9: "(from_nat xa = a) = (xa = to_nat a)"
        by (metis from_nat_to_nat_id to_nat_from_nat_id xa)
    have cond01: "(from_nat x = a \<and> from_nat xa = a) == (x = to_nat a \<and> xa = to_nat a)"
      using rw5 rw9 by simp
    have cond02: "(from_nat x = a \<and> from_nat xa = b) == (x = to_nat a \<and> xa = to_nat b)"
      using rw5 rw7 by simp
    have cond03: "(from_nat x = b \<and> from_nat xa = a) == (x = to_nat b \<and> xa = to_nat a)"
      using rw6 rw9 by simp
    have cond04: "(from_nat x = b \<and> from_nat xa = b) == (x = to_nat b \<and> xa = to_nat b)"
      using rw6 rw7 by simp
    have cond05: "((from_nat x::'b) = (from_nat xa::'b)) == (x = xa)"
      using rw8 by simp
    show "(case bezout (A $ a $ j) (A $ b $ j) of
             (p, q, u, v, d) \<Rightarrow>
               if from_nat x = a \<and> from_nat xa = a then p
               else if from_nat x = a \<and> from_nat xa = b then q
                    else if from_nat x = b \<and> from_nat xa = a then u
                         else if from_nat x = b \<and> from_nat xa = b then v
                              else if (from_nat x::'b) = from_nat xa then 1 else 0) =
            (case bezout (A $ a $ j) (A $ b $ j) of
             (p, q, u, v, d) \<Rightarrow>
               \<lambda>x y. if x = to_nat a \<and> y = to_nat a then p
                     else if x = to_nat a \<and> y = to_nat b then q
                          else if x = to_nat b \<and> y = to_nat a then u
                               else if x = to_nat b \<and> y = to_nat b then v
                                    else if x = y then 1 else 0)
             x xa" 
             proof (cases "bezout (A $ a $ j) (A $ b $ j)")
             fix p q u v d
             assume b: "bezout (A $ a $ j) (A $ b $ j) = (p, q, u, v, d)"
             show ?thesis 
              unfolding b
              apply clarify
              unfolding cond01 
              unfolding cond02
              unfolding cond03
              unfolding cond04
              unfolding cond05 by (rule refl)
    qed
  qed
qed

subsubsection\<open>Bezout Iterate for immutable arrays\<close>

lemma matrix_to_iarray_bezout_iterate:
  assumes n: "n<nrows A"
  shows "matrix_to_iarray (bezout_iterate A n i j bezout) 
  = bezout_iterate_iarrays (matrix_to_iarray A) n (to_nat i) (to_nat j) bezout"
  using n
proof (induct n arbitrary: A)
  case 0
  thus ?case unfolding bezout_iterate_iarrays.simps bezout_iterate.simps by simp
next
  case (Suc n)
  show ?case
  proof (cases "Suc n \<le> to_nat i")
    case True
    show ?thesis 
      unfolding bezout_iterate.simps bezout_iterate_iarrays.simps
      using True by auto
  next
    case False
    let ?B="(bezout_matrix_iarrays (matrix_to_iarray A) (to_nat i) (Suc n) (to_nat j) bezout 
      **i matrix_to_iarray A)"
    let ?B2="matrix_to_iarray (bezout_matrix A i (from_nat (Suc n)) j bezout ** A)"
    have "matrix_to_iarray (bezout_iterate A (Suc n) i j bezout) 
      = matrix_to_iarray (bezout_iterate (bezout_matrix A i (from_nat (Suc n)) j bezout ** A) n i j bezout)"
      unfolding bezout_iterate.simps using False by auto
    also have "... = bezout_iterate_iarrays ?B2 n (to_nat i) (to_nat j) bezout"
    proof (rule Suc.hyps) 
      show "n < nrows (bezout_matrix A i (from_nat (Suc n)) j bezout ** A)"
        using Suc.prems unfolding nrows_def by simp
    qed
    also have "... = bezout_iterate_iarrays ?B n (to_nat i) (to_nat j) bezout"
      unfolding matrix_to_iarray_matrix_matrix_mult
      unfolding matrix_to_iarray_bezout_matrix[of A i "from_nat (Suc n)" j bezout]
      unfolding to_nat_from_nat_id[OF Suc.prems[unfolded nrows_def]] ..
    also have "... = bezout_iterate_iarrays (matrix_to_iarray A) (Suc n) (to_nat i) (to_nat j) bezout"
      unfolding bezout_iterate_iarrays.simps using False by auto
    finally show ?thesis .
  qed
qed


lemma matrix_vector_all_zero_from_index2:
  fixes A::"'a::{zero}^'columns::{mod_type}^'rows::{mod_type}"
  shows "(\<forall>m>i. A $ m $ k = 0) = vector_all_zero_from_index ((to_nat i)+1, vec_to_iarray (column k A))"
proof (cases "to_nat i = nrows A - 1")
  case True
  have "(\<forall>m>i. A $ m $ k = 0) = True" 
    by (metis One_nat_def Suc_pred True not_less_eq nrows_def to_nat_0 to_nat_less_card to_nat_mono)
  also have "... = vector_all_zero_from_index ((to_nat i)+1, vec_to_iarray (column k A))"
    unfolding vector_all_zero_from_index_def Let_def
    unfolding vec_to_iarray_def column_def
    by (auto, metis True nrows_def One_nat_def Suc_pred not_le zero_less_card_finite)
  finally show ?thesis .
next
  case False
  have i_le: "i<i+1"
    by (metis False Suc_le' add_diff_cancel_right' nrows_def suc_not_zero)
  hence "(\<forall>m>i. A $ m $ k = 0) = (\<forall>m\<ge>i+1. A $ m $ k = 0)" using i_le le_Suc by auto 
  also have "... = vector_all_zero_from_index ((to_nat i)+1, vec_to_iarray (column k A))"
    unfolding matrix_vector_all_zero_from_index
    by (metis (mono_tags, hide_lams) from_nat_suc from_nat_to_nat_id i_le not_less0 
      to_nat_0 to_nat_from_nat_id to_nat_mono to_nat_plus_one_less_card)
  finally show ?thesis .
qed

subsubsection\<open>Echelon form of column k for immutable arrays\<close>

lemma matrix_to_iarray_echelon_form_of_column_k:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  and i: "i\<le>nrows A"
  shows "matrix_to_iarray (fst ((echelon_form_of_column_k bezout) (A,i) k)) 
  = fst (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k)"
proof (cases "i<nrows A")
  case False
  have i_eq: "i=nrows A" by (metis False le_imp_less_or_eq i)
  show "matrix_to_iarray (fst ((echelon_form_of_column_k bezout) (A,i) k)) 
    = fst (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k)"
    unfolding echelon_form_of_column_k_efficient echelon_form_of_column_k_def Let_def
    unfolding echelon_form_of_column_k_iarrays_def Let_def snd_conv fst_conv
    unfolding matrix_to_iarray_nrows
    unfolding i_eq matrix_to_iarray_nrows by auto
next
  case True
  let ?interchange="(interchange_rows A (from_nat i) 
    (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n))"
  have all_zero: "(\<forall>m\<ge>mod_type_class.from_nat i. A $ m $ mod_type_class.from_nat k = 0) 
    = vector_all_zero_from_index (i, column_iarray k (matrix_to_iarray A))"
    unfolding matrix_vector_all_zero_from_index
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
    unfolding vec_to_iarray_column'[OF k] ..
  have all_zero2: " (\<forall>m>from_nat i. A $ m $ mod_type_class.from_nat k = 0) 
    = (vector_all_zero_from_index (i + 1, column_iarray k (matrix_to_iarray A)))"
    unfolding matrix_vector_all_zero_from_index2
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
    unfolding vec_to_iarray_column'[OF k] ..
  have n: "(nrows_iarray (matrix_to_iarray A) - Suc 0) < nrows ?interchange"
    unfolding matrix_to_iarray_nrows[symmetric]
    unfolding nrows_def by simp
  show ?thesis
    using True
    unfolding echelon_form_of_column_k_efficient echelon_form_of_column_k_def Let_def split_beta
    unfolding echelon_form_of_column_k_iarrays_def Let_def snd_conv fst_conv
    unfolding matrix_to_iarray_nrows
    unfolding all_zero all_zero2 apply auto
    unfolding matrix_to_iarray_bezout_iterate[OF n]
    unfolding matrix_to_iarray_interchange_rows
    using vec_to_iarray_least_non_zero_position_of_vector_from_index'[of "from_nat i" "from_nat k" A]
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
    unfolding to_nat_from_nat_id[OF k[unfolded ncols_def]]
    unfolding vec_to_iarray_column'[OF k]
    by (auto, metis Suc_eq_plus1 all_zero all_zero2 less_le)
qed

lemma snd_matrix_to_iarray_echelon_form_of_column_k:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  and i: "i\<le>nrows A"
  shows "snd ((echelon_form_of_column_k bezout) (A,i) k) 
  = fst (snd (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k))"
proof (cases "i<nrows A")
  case False
  have i_eq: "i=nrows A" by (metis False le_imp_less_or_eq i)
  show "snd ((echelon_form_of_column_k bezout) (A,i) k) 
    = fst (snd (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k))"
    unfolding echelon_form_of_column_k_efficient echelon_form_of_column_k_def Let_def
    unfolding echelon_form_of_column_k_iarrays_def Let_def snd_conv fst_conv
    unfolding i_eq matrix_to_iarray_nrows by auto
next
  case True
  let ?interchange="(interchange_rows A (from_nat i) 
    (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n))"
  have all_zero: "(\<forall>m\<ge>mod_type_class.from_nat i. A $ m $ mod_type_class.from_nat k = 0) 
    = vector_all_zero_from_index (i, column_iarray k (matrix_to_iarray A))"
    unfolding matrix_vector_all_zero_from_index
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
    unfolding vec_to_iarray_column'[OF k] ..
  have all_zero2: " (\<forall>m>from_nat i. A $ m $ mod_type_class.from_nat k = 0) 
    = (vector_all_zero_from_index (i + 1, column_iarray k (matrix_to_iarray A)))"
    unfolding matrix_vector_all_zero_from_index2
    unfolding to_nat_from_nat_id[OF True[unfolded nrows_def]]
    unfolding vec_to_iarray_column'[OF k] ..
    have Aik: "A $ from_nat i $ from_nat k = matrix_to_iarray A !! i !! k" 
      by (metis True k matrix_to_iarray_nth ncols_def nrows_def to_nat_from_nat_id)
  show ?thesis
    using True Aik
    unfolding echelon_form_of_column_k_efficient
    unfolding echelon_form_of_column_k_efficient_def Let_def split_beta
    unfolding echelon_form_of_column_k_iarrays_def Let_def snd_conv fst_conv
    unfolding all_zero all_zero2
    unfolding matrix_to_iarray_nrows by auto
qed

corollary fst_snd_matrix_to_iarray_echelon_form_of_column_k:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  and i: "i\<le>nrows A"
  shows "snd ((echelon_form_of_column_k bezout) (A,i) k)
  = fst (snd (echelon_form_of_column_k_iarrays (matrix_to_iarray A, i, bezout) k))"
  using snd_matrix_to_iarray_echelon_form_of_column_k[OF assms] by simp

subsubsection\<open>Echelon form up to column k for immutable arrays\<close>

lemma snd_snd_foldl_echelon_form_of_column_k_iarrays:
  "snd (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<k])) 
  = bezout"
proof (induct k)
  case 0 thus ?case by auto
next
  case (Suc k)
  show ?case
    using Suc.hyps
    unfolding echelon_form_of_column_k_iarrays_def
    unfolding Let_def unfolding split_beta by auto
qed

lemma foldl_echelon_form_column_k_eq:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A"
  shows matrix_to_iarray_echelon_form_of_upt_k[code_unfold]: 
  "matrix_to_iarray (echelon_form_of_upt_k A k bezout)
  = echelon_form_of_upt_k_iarrays (matrix_to_iarray A) k bezout"
  and fst_foldl_ef_k_eq: "fst (snd (foldl echelon_form_of_column_k_iarrays 
  (matrix_to_iarray A,0,bezout) [0..<Suc k])) 
  = snd (foldl (echelon_form_of_column_k bezout) (A,0) [0..<Suc k])"
  and fst_foldl_ef_k_less:
  "snd (foldl (echelon_form_of_column_k bezout) (A,0) [0..<Suc k]) \<le> nrows A"
  using assms
proof (induct k)
  show "matrix_to_iarray (echelon_form_of_upt_k A 0 bezout) 
    = echelon_form_of_upt_k_iarrays (matrix_to_iarray A) 0 bezout"
    unfolding echelon_form_of_upt_k_def echelon_form_of_upt_k_iarrays_def
    by (simp, metis le0 matrix_to_iarray_echelon_form_of_column_k ncols_not_0 neq0_conv)
  show "fst (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<Suc 0]))
    = snd (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc 0])"
    by (simp, metis le0 ncols_not_0 not_gr0 snd_matrix_to_iarray_echelon_form_of_column_k)
  show "snd (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc 0]) \<le> nrows A"
    apply simp
    unfolding echelon_form_of_column_k_def Let_def snd_conv fst_conv 
    unfolding nrows_def by auto
next
  fix k
  assume "(k < ncols A \<Longrightarrow> matrix_to_iarray (echelon_form_of_upt_k A k bezout) 
    = echelon_form_of_upt_k_iarrays (matrix_to_iarray A) k bezout)"
    and  "(k < ncols A \<Longrightarrow>
    fst (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<Suc k])) =
    snd (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k]))"
    and hyp3: "(k < ncols A \<Longrightarrow> snd (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k]) \<le> nrows A)"
    and Suc_k_less_card: "Suc k < ncols A"
  hence hyp1: "matrix_to_iarray (echelon_form_of_upt_k A k bezout) 
    = echelon_form_of_upt_k_iarrays (matrix_to_iarray A) k bezout"
    and hyp2: "fst (snd (foldl echelon_form_of_column_k_iarrays 
    (matrix_to_iarray A, 0, bezout) [0..<Suc k]))
    = snd (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k])"
    and hyp3: "snd (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k]) \<le> nrows A"
    by auto
  hence hyp1_unfolded: "matrix_to_iarray (fst (foldl (echelon_form_of_column_k bezout) (A,0) [0..<Suc k])) 
    = fst (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A,0,bezout) [0..<Suc k])" 
    using hyp1 unfolding echelon_form_of_upt_k_def echelon_form_of_upt_k_iarrays_def by simp
  have upt_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [(Suc k)]" by auto
  let ?f = "foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<Suc k]"
  let ?f2 = "foldl (echelon_form_of_column_k bezout) (A,0) [0..<(Suc k)]"
  have fold_rw: "?f = (fst ?f, fst (snd ?f), snd (snd ?f))" by simp
  have fold_rw': "?f2 = (fst ?f2, snd ?f2)" by simp
  have rw: "snd (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k])
    = fst (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<Suc k]))" 
    using hyp2 by auto
  show "fst (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) 
    [0..<Suc (Suc k)])) = snd (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc (Suc k)])"
    unfolding upt_rw foldl_append unfolding List.foldl.simps apply (subst fold_rw) 
    apply (subst fold_rw') unfolding hyp2 unfolding hyp1_unfolded[symmetric]
    unfolding rw 
    unfolding snd_snd_foldl_echelon_form_of_column_k_iarrays  
    proof (rule fst_snd_matrix_to_iarray_echelon_form_of_column_k [symmetric])
      show "Suc k < ncols (fst ?f2)" using Suc_k_less_card unfolding ncols_def .
      show "fst (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<Suc k]))
    \<le> nrows (fst (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k]))"
      by (metis hyp2 hyp3 nrows_def)      
  qed
  show "matrix_to_iarray (echelon_form_of_upt_k A (Suc k) bezout) 
    = echelon_form_of_upt_k_iarrays (matrix_to_iarray A) (Suc k) bezout"
    unfolding echelon_form_of_upt_k_def echelon_form_of_upt_k_iarrays_def
      upt_rw foldl_append List.foldl.simps apply (subst fold_rw) apply (subst fold_rw') 
    unfolding hyp2 hyp1_unfolded[symmetric]
    unfolding rw
    unfolding snd_snd_foldl_echelon_form_of_column_k_iarrays
  proof (rule matrix_to_iarray_echelon_form_of_column_k)
    show "Suc k < ncols (fst ?f2)" using Suc_k_less_card unfolding ncols_def .
    show "fst (snd (foldl echelon_form_of_column_k_iarrays (matrix_to_iarray A, 0, bezout) [0..<Suc k]))
    \<le> nrows (fst (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k]))"
    by (metis hyp2 hyp3 nrows_def)
  qed
  show "snd (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc (Suc k)]) \<le> nrows A"
    using [[unfold_abs_def = false]]
    unfolding upt_rw foldl_append unfolding List.foldl.simps apply (subst fold_rw')
    unfolding echelon_form_of_column_k_def Let_def
    using hyp3 le_antisym not_less_eq_eq unfolding nrows_def by fastforce
qed

subsubsection\<open>Echelon form up to column k for immutable arrays\<close>

lemma matrix_to_iarray_echelon_form_of[code_unfold]:
  "matrix_to_iarray (echelon_form_of A bezout) 
    = echelon_form_of_iarrays (matrix_to_iarray A) bezout"
  unfolding echelon_form_of_def echelon_form_of_iarrays_def
  by (metis (poly_guards_query) One_nat_def diff_less lessI matrix_to_iarray_echelon_form_of_upt_k 
    ncols_def ncols_eq_card_columns zero_less_card_finite)

end
