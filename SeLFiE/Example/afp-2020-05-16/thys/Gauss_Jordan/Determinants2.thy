(*  
    Title:      Determinants2.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Computing determinants of matrices using the Gauss Jordan algorithm\<close>

theory Determinants2
imports
  Gauss_Jordan_PA
begin

subsection\<open>Some previous properties\<close>

subsubsection\<open>Relationships between determinants and elementary row operations\<close>

lemma det_interchange_rows:
shows "det (interchange_rows A i j) = of_int (if i = j then 1 else -1) * det A"
proof -
  have "(interchange_rows A i j) = (\<chi> a. A $ (Fun.swap i j id) a)" unfolding interchange_rows_def Fun.swap_def by vector
  hence "det(interchange_rows A i j) = det(\<chi> a. A$(Fun.swap i j id) a)" by simp
  also have "... = of_int (sign (Fun.swap i j id)) * det A" by (rule det_permute_rows[of "Fun.swap i j id" A], simp add: permutes_swap_id)
  finally show ?thesis unfolding sign_swap_id .
qed

corollary det_interchange_different_rows:
assumes i_not_j: "i \<noteq> j"
shows "det (interchange_rows A i j) = - det A" unfolding det_interchange_rows using i_not_j by simp

corollary det_interchange_same_rows:
assumes i_eq_j: "i = j"
shows "det (interchange_rows A i j) = det A" unfolding det_interchange_rows using i_eq_j by simp

lemma det_mult_row:
shows "det (mult_row A a k) = k * det A"
proof -
have A_rw: "(\<chi> i. if i = a then A$a else A$i) = A" by vector
have "(mult_row A a k) = (\<chi> i. if i = a then k *s A $ a else A $ i)" unfolding mult_row_def by vector
hence "det(mult_row A a k) = det(\<chi> i. if i = a then k *s A $ a else A $ i)" by simp
also have "... =  k * det(\<chi> i. if i = a then A$a else A$i)" unfolding det_row_mul ..
also have "... = k * det A" unfolding A_rw ..
finally show ?thesis .
qed

(*The name det_row_add is already used in the Determinants.thy file of the standard library*)
lemma det_row_add':
assumes i_not_j: "i \<noteq> j"
shows "det (row_add A i j q) = det A"
proof -
have "(row_add A i j q) = (\<chi> k. if k = i then row i A + q *s row j A else row k A)"
unfolding row_add_def row_def by vector
hence "det(row_add A i j q) = det(\<chi> k. if k = i then row i A + q *s row j A else row k A)" by simp
also have "... = det A" unfolding det_row_operation[OF i_not_j] ..
finally show ?thesis .
qed


subsubsection\<open>Relationships between determinants and elementary column operations\<close>

lemma det_interchange_columns:
shows "det (interchange_columns A i j) = of_int (if i = j then 1 else -1) * det A"
proof - 
have "(interchange_columns A i j) = (\<chi> a b. A $ a $ (Fun.swap i j id) b)" unfolding interchange_columns_def Fun.swap_def by vector
hence "det(interchange_columns A i j) = det(\<chi> a b. A $ a $ (Fun.swap i j id) b)" by simp
also have "... = of_int (sign (Fun.swap i j id)) * det A" by (rule det_permute_columns[of "Fun.swap i j id" A], simp add: permutes_swap_id)
finally show ?thesis unfolding sign_swap_id .
qed

corollary det_interchange_different_columns:
assumes i_not_j: "i \<noteq> j"
shows "det (interchange_columns A i j) = - det A" unfolding det_interchange_columns using i_not_j by simp

corollary det_interchange_same_columns:
assumes i_eq_j: "i = j"
shows "det (interchange_columns A i j) = det A" unfolding det_interchange_columns using i_eq_j by simp

lemma det_mult_columns:
shows "det (mult_column A a k) = k * det A"
proof -
have "mult_column A a k = transpose (mult_row (transpose A) a k)" unfolding transpose_def mult_row_def mult_column_def by vector
hence "det (mult_column A a k) = det (transpose (mult_row (transpose A) a k))" by simp
also have "... = det (mult_row (transpose A) a k)" unfolding det_transpose ..
also have "... = k * det (transpose A)" unfolding det_mult_row ..
also have "... = k * det A" unfolding det_transpose ..
finally show ?thesis .
qed

lemma det_column_add:
assumes i_not_j: "i \<noteq> j"
shows "det (column_add A i j q) = det A"
proof -
have "(column_add A i j q) = (transpose (row_add (transpose A) i j q))" unfolding transpose_def column_add_def row_add_def by vector
hence "det (column_add A i j q) = det (transpose (row_add (transpose A) i j q))" by simp
also have "... = det (row_add (transpose A) i j q)" unfolding det_transpose ..
also have "... = det A" unfolding det_row_add'[OF i_not_j] det_transpose ..
finally show ?thesis .
qed

subsection\<open>Proving that the determinant can be computed by means of the Gauss Jordan algorithm\<close>

subsubsection\<open>Previous properties\<close>

lemma det_row_add_iterate_upt_n:
fixes A::"'a::{comm_ring_1}^'n::{mod_type}^'n::{mod_type}"
assumes n: "n<nrows A"
shows "det (row_add_iterate A n i j) = det A"
using n
proof (induct n arbitrary: A)
case 0
show ?case unfolding row_add_iterate.simps using det_row_add'[of 0 i A] by auto
next
case (Suc n)
show ?case  unfolding row_add_iterate.simps
proof (auto)
show "det (row_add_iterate A n i j) = det A" using Suc.hyps Suc.prems by simp
assume Suc_n_not_i: "Suc n \<noteq> to_nat i"
have "det (row_add_iterate (row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)) n i j) 
= det (row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j))"
proof (rule Suc.hyps, unfold nrows_def)
show " n < CARD('n)" using Suc.prems unfolding nrows_def by auto
qed
also have "... = det A"
  proof (rule det_row_add',rule ccontr, simp)
    assume "from_nat (Suc n) = i"
      hence "to_nat (from_nat (Suc n)::'n) = to_nat i" by simp
      hence "(Suc n) = to_nat i" unfolding to_nat_from_nat_id[OF Suc.prems[unfolded nrows_def]] .
      thus False using Suc_n_not_i by contradiction
    qed
finally show "det (row_add_iterate (row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)) n i j) = det A" .
qed
qed


corollary det_row_add_iterate:
fixes A::"'a::{comm_ring_1}^'n::{mod_type}^'n::{mod_type}"
shows "det (row_add_iterate A (nrows A - 1) i j) = det A"
by (metis det_row_add_iterate_upt_n diff_less neq0_conv nrows_not_0 zero_less_one)



lemma det_Gauss_Jordan_in_ij:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}" and i j::"'n"
defines A': "A'== mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) $ i $ j)"
shows "det (Gauss_Jordan_in_ij A i j) = det A' "
proof -
have nrows_eq: "nrows A' = nrows A" unfolding nrows_def by simp
have "row_add_iterate A' (nrows A - 1) i j  =  Gauss_Jordan_in_ij A i j" using row_add_iterate_eq_Gauss_Jordan_in_ij  unfolding A' .
hence "det (Gauss_Jordan_in_ij A i j) = det (row_add_iterate A' (nrows A - 1) i j)" by simp
also have "... = det A'" by (rule det_row_add_iterate[of A', unfolded nrows_eq])
finally show ?thesis .
qed


lemma det_Gauss_Jordan_in_ij_1:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}" and i j::"'n"
defines A': "A'== mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) $ i $ j)"
assumes i: "(LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) = i"
shows "det (Gauss_Jordan_in_ij A i j) = 1/(A$i$j) * det A"
proof -
have "det (Gauss_Jordan_in_ij A i j) = det A' " using det_Gauss_Jordan_in_ij unfolding A' by auto
also have "... = 1/(A$i$j) * det A" unfolding A' det_mult_row unfolding i det_interchange_rows by auto
finally show ?thesis .
qed


lemma det_Gauss_Jordan_in_ij_2:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}" and i j::"'n"
defines A': "A'== mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) $ i $ j)"
assumes i: "(LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) \<noteq> i"
shows "det (Gauss_Jordan_in_ij A i j) = - 1/(A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j) * det A"
proof -
have "det (Gauss_Jordan_in_ij A i j) = det A' " using det_Gauss_Jordan_in_ij unfolding A' by auto
also have "... = - 1/(A$ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $j) * det A" unfolding A' det_mult_row unfolding det_interchange_rows using i by auto
finally show ?thesis .
qed

subsubsection\<open>Definitions\<close>

text\<open>The following definitions allow the computation of the determinant of a matrix using the Gauss-Jordan algorithm. In the first component the determinant of each transformation
is accumulated and the second component contains the matrix transformed into a reduced row echelon form matrix\<close>

definition Gauss_Jordan_in_ij_det_P :: "'a::{semiring_1, inverse, one, uminus}^'m^'n::{finite, ord}=> 'n=>'m=>('a \<times> ('a^'m^'n::{finite, ord}))"
  where "Gauss_Jordan_in_ij_det_P A i j = (let n = (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) in (if i = n then 1/(A $ i $ j) else - 1/(A $ n $ j), Gauss_Jordan_in_ij A i j))"

definition Gauss_Jordan_column_k_det_P where "Gauss_Jordan_column_k_det_P A' k =
(let det_P= fst A'; i = fst (snd A'); A = snd (snd A'); from_nat_i = from_nat i; from_nat_k = from_nat k
 in if (\<forall>m\<ge>from_nat_i. A $ m $ from_nat_k = 0) \<or> i = nrows A then (det_P, i, A)
    else let gauss = Gauss_Jordan_in_ij_det_P A (from_nat_i) (from_nat_k) in (fst gauss * det_P, i + 1, snd gauss))"

definition Gauss_Jordan_upt_k_det_P 
  where "Gauss_Jordan_upt_k_det_P A k = (let foldl = foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k] in (fst foldl, snd (snd foldl)))"
definition Gauss_Jordan_det_P 
  where "Gauss_Jordan_det_P A = Gauss_Jordan_upt_k_det_P A (ncols A - 1)"

subsubsection\<open>Proofs\<close>

text\<open>This is an equivalent definition created to achieve a more efficient computation.\<close>
lemma Gauss_Jordan_in_ij_det_P_code[code]:
shows "Gauss_Jordan_in_ij_det_P A i j = 
    (let n = (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n);
         interchange_A = interchange_rows A i n;
         A' = mult_row interchange_A i (1 / interchange_A $ i $ j) in (if i = n then 1/(A $ i $ j) else - 1/(A $ n $ j), Gauss_Jordan_wrapper i j A' interchange_A))"
         unfolding Gauss_Jordan_in_ij_det_P_def Gauss_Jordan_in_ij_def Gauss_Jordan_wrapper_def Let_def by auto


lemma det_Gauss_Jordan_in_ij_det_P:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}" and i j::"'n"
shows "(fst (Gauss_Jordan_in_ij_det_P A i j)) * det A  = det (snd (Gauss_Jordan_in_ij_det_P A i j))"
unfolding Gauss_Jordan_in_ij_det_P_def Let_def fst_conv snd_conv
using det_Gauss_Jordan_in_ij_1[of A j i]
using det_Gauss_Jordan_in_ij_2[of A j i] by auto


lemma det_Gauss_Jordan_column_k_det_P:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
assumes det: "det_P * det B = det A"
shows "(fst (Gauss_Jordan_column_k_det_P (det_P,i,A) k)) * det B = det (snd (snd (Gauss_Jordan_column_k_det_P (det_P,i,A) k)))"
proof (unfold Gauss_Jordan_column_k_det_P_def Let_def, auto simp add: assms)
fix m
assume i_not_nrows: "i \<noteq> nrows A"
and i_less_m: "from_nat i \<le> m"
and Amk_not_0: "A $ m $ from_nat k \<noteq> 0"
show  "fst (Gauss_Jordan_in_ij_det_P A (from_nat i) (from_nat k)) * det_P * det B =
        det (snd (Gauss_Jordan_in_ij_det_P A (from_nat i) (from_nat k)))" unfolding mult.assoc det 
        unfolding det_Gauss_Jordan_in_ij_det_P ..
qed


lemma det_Gauss_Jordan_upt_k_det_P:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "(fst (Gauss_Jordan_upt_k_det_P A k)) * det A = det (snd (Gauss_Jordan_upt_k_det_P A k))"
proof (induct k)
case 0
show ?case
unfolding Gauss_Jordan_upt_k_det_P_def Let_def unfolding fst_conv snd_conv by (simp add:det_Gauss_Jordan_column_k_det_P)
next
case (Suc k)
have suc_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [Suc k]" by simp
have fold_expand: "(foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k]) 
= (fst (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k]), fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k])),
  snd (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k])))" by simp
show ?case unfolding Gauss_Jordan_upt_k_det_P_def Let_def 
unfolding suc_rw foldl_append List.foldl.simps fst_conv snd_conv
by(subst (1 2) fold_expand, rule det_Gauss_Jordan_column_k_det_P, rule Suc.hyps[unfolded Gauss_Jordan_upt_k_det_P_def Let_def fst_conv snd_conv])
qed


lemma det_Gauss_Jordan_det_P:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "(fst (Gauss_Jordan_det_P A)) * det A = det (snd (Gauss_Jordan_det_P A))"
using det_Gauss_Jordan_upt_k_det_P unfolding Gauss_Jordan_det_P_def by simp


definition upper_triangular_upt_k where "upper_triangular_upt_k A k = (\<forall>i j. j<i \<and> to_nat j < k \<longrightarrow> A $ i $ j = 0)"
definition upper_triangular where "upper_triangular A = (\<forall>i j. j<i \<longrightarrow> A $ i $ j = 0)"

lemma upper_triangular_upt_imp_upper_triangular:
assumes "upper_triangular_upt_k A (nrows A)"
shows "upper_triangular A"
using assms unfolding upper_triangular_upt_k_def upper_triangular_def nrows_def
using to_nat_less_card[where ?'a='b] by blast

lemma rref_imp_upper_triagular_upt:
fixes A::"'a::{one, zero}^'n::{mod_type}^'n::{mod_type}"
assumes "reduced_row_echelon_form A"
shows "upper_triangular_upt_k A k"
proof (induct k)
case 0
show ?case unfolding upper_triangular_upt_k_def by simp
next
case (Suc k)
show ?case unfolding upper_triangular_upt_k_def proof (clarify)
fix i j::'n
assume j_less_i: "j < i" and j_less_suc_k: "to_nat j < Suc k"
show "A $ i $ j = 0"
  proof (cases "to_nat j < k")
  case True
  thus ?thesis using Suc.hyps unfolding upper_triangular_upt_k_def using j_less_i True by auto
  next
  case False
  hence j_eq_k: "to_nat j = k" using j_less_suc_k by simp
  have rref_suc: "reduced_row_echelon_form_upt_k A (Suc k)" by (metis assms rref_implies_rref_upt)
 
  show ?thesis
    proof (cases "A $ i $ from_nat k = 0")
      case True
      have "from_nat k = j" by (metis from_nat_to_nat_id j_eq_k)
      thus ?thesis using True by simp
      next
      case False
      have zero_i_k: "is_zero_row_upt_k i k A" unfolding is_zero_row_upt_k_def
      by (metis (hide_lams, mono_tags) Suc.hyps leD le_less_linear less_imp_le j_eq_k j_less_i le_trans to_nat_mono' upper_triangular_upt_k_def)
      have not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) A" unfolding is_zero_row_upt_k_def using False by (metis j_eq_k lessI to_nat_from_nat)      
      have Least_eq: "(LEAST n. A $ i $ n \<noteq> 0) = from_nat k"
        proof (rule Least_equality)
           show "A $ i $ from_nat k \<noteq> 0" using False by simp
           show "\<And>y. A $ i $ y \<noteq> 0 \<Longrightarrow> from_nat k \<le> y" by (metis (full_types) is_zero_row_upt_k_def not_le_imp_less to_nat_le zero_i_k)
        qed
      have i_not_k: "i \<noteq> from_nat k" by (metis less_irrefl from_nat_to_nat_id j_eq_k j_less_i)
      show ?thesis using rref_upt_condition4_explicit[OF rref_suc not_zero_i_suc_k i_not_k] unfolding Least_eq 
      using rref_upt_condition1_explicit[OF rref_suc]
      using Suc.hyps unfolding upper_triangular_upt_k_def 
      by (metis (mono_tags) leD not_le_imp_less is_zero_row_upt_k_def is_zero_row_upt_k_suc j_eq_k j_less_i not_zero_i_suc_k to_nat_from_nat to_nat_mono')  
qed
qed
qed
qed

lemma rref_imp_upper_triagular:
assumes "reduced_row_echelon_form A"
shows "upper_triangular A" 
by (metis assms rref_imp_upper_triagular_upt upper_triangular_upt_imp_upper_triangular)


lemma det_Gauss_Jordan[code_unfold]:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "det (Gauss_Jordan A) = prod (\<lambda>i. (Gauss_Jordan A)$i$i) (UNIV:: 'n set)"
using det_upperdiagonal rref_imp_upper_triagular[OF rref_Gauss_Jordan[of A]] unfolding upper_triangular_def by blast


lemma snd_Gauss_Jordan_in_ij_det_P_is_snd_Gauss_Jordan_in_ij_PA:
shows "snd (Gauss_Jordan_in_ij_det_P A i j) = snd (Gauss_Jordan_in_ij_PA (P,A) i j)"
unfolding Gauss_Jordan_in_ij_det_P_def Gauss_Jordan_in_ij_PA_def 
unfolding  Gauss_Jordan_in_ij_def Let_def snd_conv fst_conv ..


lemma snd_Gauss_Jordan_column_k_det_P_is_snd_Gauss_Jordan_column_k_PA:
shows "snd (Gauss_Jordan_column_k_det_P (n,i,A) k) = snd (Gauss_Jordan_column_k_PA (P,i,A) k)"
unfolding Gauss_Jordan_column_k_det_P_def Gauss_Jordan_column_k_PA_def Let_def snd_conv unfolding fst_conv
using snd_Gauss_Jordan_in_ij_det_P_is_snd_Gauss_Jordan_in_ij_PA by auto


lemma det_fst_row_add_iterate_PA:
fixes A::"'a::{comm_ring_1}^'n::{mod_type}^'n::{mod_type}"
assumes n: "n<nrows A"
shows "det (fst (row_add_iterate_PA (P,A) n i j)) = det P"
using n
proof (induct n arbitrary: P A)
case 0
show ?case unfolding row_add_iterate_PA.simps using det_row_add'[of 0 i P] by simp
next
case (Suc n)
have n: "n<nrows A" using Suc.prems by simp
show ?case
proof (cases "Suc n = to_nat i")
case True show ?thesis unfolding row_add_iterate_PA.simps if_P[OF True] using Suc.hyps[OF n] .
next
case False 
define P' where "P' = row_add P (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
define A' where "A' = row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
have n2: "n< nrows A'" using n unfolding nrows_def .
have "det (fst (row_add_iterate_PA (P, A) (Suc n) i j)) = det (fst (row_add_iterate_PA (P', A') n i j))" unfolding row_add_iterate_PA.simps if_not_P[OF False] P'_def A'_def ..
also have "... = det P'" using Suc.hyps[OF n2] .
also have "... = det P" unfolding P'_def 
proof (rule det_row_add', rule ccontr, simp)
    assume "from_nat (Suc n) = i"
      hence "to_nat (from_nat (Suc n)::'n) = to_nat i" by simp
      hence "(Suc n) = to_nat i" unfolding to_nat_from_nat_id[OF Suc.prems[unfolded nrows_def]] .
      thus False using False by contradiction
    qed
finally show ?thesis .
qed
qed



lemma det_fst_Gauss_Jordan_in_ij_PA_eq_fst_Gauss_Jordan_in_ij_det_P:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "fst (Gauss_Jordan_in_ij_det_P A i j) * det P = det (fst (Gauss_Jordan_in_ij_PA (P,A) i j))"
proof -
define P' where "P' = mult_row (interchange_rows P i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j)"
define A' where "A' = mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j)"
have "det (fst (Gauss_Jordan_in_ij_PA (P,A) i j)) = det (fst (row_add_iterate_PA (P',A') (nrows A - 1) i j))"
unfolding fst_row_add_iterate_PA_eq_fst_Gauss_Jordan_in_ij_PA[symmetric] A'_def P'_def ..
also have "...= det P'" by (rule det_fst_row_add_iterate_PA, simp add: nrows_def)
also have "... = (if i = (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) then 1 / A $ i $ j else - 1 / A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j) * det P"
proof (cases "i = (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)")
case True show ?thesis 
unfolding if_P[OF True] P'_def unfolding True[symmetric] unfolding interchange_same_rows unfolding det_mult_row ..
next
case False
show ?thesis unfolding if_not_P[OF False] P'_def unfolding det_mult_row unfolding det_interchange_different_rows[OF False] by simp
qed
also have "... = fst (Gauss_Jordan_in_ij_det_P A i j) * det P"
unfolding Gauss_Jordan_in_ij_det_P_def by simp
finally show ?thesis ..
qed


lemma det_fst_Gauss_Jordan_column_k_PA_eq_fst_Gauss_Jordan_column_k_det_P:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "fst (Gauss_Jordan_column_k_det_P (det P,i,A) k) = det (fst (Gauss_Jordan_column_k_PA (P,i,A) k))"
unfolding Gauss_Jordan_column_k_det_P_def Gauss_Jordan_column_k_PA_def Let_def snd_conv fst_conv
using det_fst_Gauss_Jordan_in_ij_PA_eq_fst_Gauss_Jordan_in_ij_det_P by auto


lemma fst_snd_Gauss_Jordan_column_k_det_P_eq_fst_snd_Gauss_Jordan_column_k_PA:
shows "fst (snd (Gauss_Jordan_column_k_det_P (n,i,A) k)) = fst (snd (Gauss_Jordan_column_k_PA (P,i,A) k))"
unfolding Gauss_Jordan_column_k_det_P_def Gauss_Jordan_column_k_PA_def Let_def snd_conv fst_conv
by auto


text\<open>The way of proving the following lemma is very similar to the demonstration of @{thm "rref_and_index_Gauss_Jordan_upt_k"}.\<close>

lemma foldl_Gauss_Jordan_column_k_det_P:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows det_fst_Gauss_Jordan_upt_k_PA_eq_fst_Gauss_Jordan_upt_k_det_P: "fst (Gauss_Jordan_upt_k_det_P A k) = det (fst (Gauss_Jordan_upt_k_PA A k))"
and snd_Gauss_Jordan_upt_k_det_P_is_snd_Gauss_Jordan_upt_k_PA: "snd (Gauss_Jordan_upt_k_det_P A k) = snd (Gauss_Jordan_upt_k_PA A k)"
and fst_snd_foldl_Gauss_det_P_PA: "fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k])) = fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k]))"
proof (induct k)
case 0
show "fst (Gauss_Jordan_upt_k_det_P A 0) = det (fst (Gauss_Jordan_upt_k_PA A 0))"
unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_PA_def Let_def
by (simp, metis det_fst_Gauss_Jordan_column_k_PA_eq_fst_Gauss_Jordan_column_k_det_P det_I)
show "snd (Gauss_Jordan_upt_k_det_P A 0) = snd (Gauss_Jordan_upt_k_PA A 0)"
unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_PA_def Let_def snd_conv
apply auto using snd_Gauss_Jordan_column_k_det_P_is_snd_Gauss_Jordan_column_k_PA by metis
show "fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc 0])) = fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc 0]))"
using [[unfold_abs_def = false]]
unfolding Gauss_Jordan_column_k_det_P_def Gauss_Jordan_column_k_PA_def apply auto
using fst_snd_Gauss_Jordan_column_k_det_P_eq_fst_snd_Gauss_Jordan_column_k_PA by metis
next
fix k
assume hyp1: "fst (Gauss_Jordan_upt_k_det_P A k) = det (fst (Gauss_Jordan_upt_k_PA A k))"
and hyp2: "snd (Gauss_Jordan_upt_k_det_P A k) = snd (Gauss_Jordan_upt_k_PA A k)"
and hyp3: "fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k])) = fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k]))"
have list_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [Suc k]" by simp
have det_mat_nn: "det (mat 1::'a^'n::{mod_type}^'n::{mod_type}) = 1" using det_I by simp
define f where "f = foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k]"
define g where "g = foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k]"
have f_rw: "f = (fst f, fst (snd f), snd(snd f))" by simp
have g_rw: "g = (fst g, fst (snd g), snd(snd g))" by simp
have fst_snd: "fst (snd f) = fst (snd g)" unfolding f_def g_def using hyp3 unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_PA_def Let_def fst_conv snd_conv .
have snd_snd: "snd (snd f) = snd (snd g)" unfolding f_def g_def using hyp2 unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_PA_def Let_def fst_conv snd_conv .
have fst_det: "fst f = det (fst g)" unfolding f_def g_def using hyp1 unfolding Gauss_Jordan_upt_k_det_P_def Gauss_Jordan_upt_k_PA_def Let_def fst_conv by simp
show "fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc k])) = fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k])) \<Longrightarrow>
        fst (Gauss_Jordan_upt_k_det_P A (Suc k)) = det (fst (Gauss_Jordan_upt_k_PA A (Suc k)))"
unfolding Gauss_Jordan_upt_k_det_P_def  
unfolding Gauss_Jordan_upt_k_PA_def Let_def fst_conv
unfolding list_rw foldl_append unfolding List.foldl.simps
unfolding f_def[symmetric] g_def[symmetric]
apply (subst f_rw)
apply (subst g_rw)
unfolding fst_snd snd_snd fst_det
by (rule det_fst_Gauss_Jordan_column_k_PA_eq_fst_Gauss_Jordan_column_k_det_P)
show "snd (Gauss_Jordan_upt_k_det_P A (Suc k)) = snd (Gauss_Jordan_upt_k_PA A (Suc k))"
unfolding Gauss_Jordan_upt_k_det_P_def  
unfolding Gauss_Jordan_upt_k_PA_def Let_def fst_conv
unfolding list_rw foldl_append unfolding List.foldl.simps
unfolding f_def[symmetric] g_def[symmetric]
apply (subst f_rw)
apply (subst g_rw)
unfolding fst_snd snd_snd fst_det
by (metis fst_snd prod.collapse snd_Gauss_Jordan_column_k_det_P_is_snd_Gauss_Jordan_column_k_PA snd_eqD snd_snd)
show "fst (snd (foldl Gauss_Jordan_column_k_det_P (1, 0, A) [0..<Suc (Suc k)])) = fst (snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc (Suc k)]))"
unfolding Gauss_Jordan_upt_k_det_P_def  
unfolding Gauss_Jordan_upt_k_PA_def Let_def fst_conv
unfolding list_rw foldl_append unfolding List.foldl.simps
unfolding f_def[symmetric] g_def[symmetric]
apply (subst f_rw)
apply (subst g_rw)
unfolding fst_snd snd_snd fst_det by (rule fst_snd_Gauss_Jordan_column_k_det_P_eq_fst_snd_Gauss_Jordan_column_k_PA)
qed



lemma snd_Gauss_Jordan_det_P_is_Gauss_Jordan:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "snd (Gauss_Jordan_det_P A) = (Gauss_Jordan A)"
unfolding Gauss_Jordan_det_P_def Gauss_Jordan_def unfolding snd_Gauss_Jordan_upt_k_det_P_is_snd_Gauss_Jordan_upt_k_PA 
snd_Gauss_Jordan_upt_k_PA ..


lemma det_snd_Gauss_Jordan_det_P[code_unfold]:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "det (snd (Gauss_Jordan_det_P A)) = prod (\<lambda>i. (snd (Gauss_Jordan_det_P A))$i$i) (UNIV:: 'n set)"
unfolding snd_Gauss_Jordan_det_P_is_Gauss_Jordan det_Gauss_Jordan ..


lemma det_fst_Gauss_Jordan_PA_eq_fst_Gauss_Jordan_det_P:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "fst (Gauss_Jordan_det_P A) = det (fst (Gauss_Jordan_PA A))"
by (unfold Gauss_Jordan_det_P_def Gauss_Jordan_PA_def, rule det_fst_Gauss_Jordan_upt_k_PA_eq_fst_Gauss_Jordan_upt_k_det_P)


lemma fst_Gauss_Jordan_det_P_not_0:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "fst (Gauss_Jordan_det_P A) \<noteq> 0"
unfolding det_fst_Gauss_Jordan_PA_eq_fst_Gauss_Jordan_det_P 
by (metis (mono_tags) det_I det_mul invertible_fst_Gauss_Jordan_PA matrix_inv_right mult_zero_left zero_neq_one)


lemma det_code_equation[code_unfold]:
fixes A::"'a::{field}^'n::{mod_type}^'n::{mod_type}"
shows "det A = (let A' = Gauss_Jordan_det_P A in prod (\<lambda>i. (snd (A'))$i$i) (UNIV::'n set)/(fst (A')))"
unfolding Let_def using det_Gauss_Jordan_det_P[of A]
unfolding det_snd_Gauss_Jordan_det_P
by (simp add: fst_Gauss_Jordan_det_P_not_0 nonzero_eq_divide_eq ac_simps)

end
