(*  
    Title:      Gauss_Jordan_PA.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Obtaining explicitly the invertible matrix which transforms a matrix to its reduced row echelon form\<close>

theory Gauss_Jordan_PA
imports
 Gauss_Jordan
 Rank_Nullity_Theorem.Miscellaneous
 Linear_Maps (*Really, this file is not necessary, but it contains interesting properties about linear maps.*)
begin

subsection\<open>Definitions\<close>

text\<open>The following algorithm is similar to @{term "Gauss_Jordan"},
but in this case we will also return the P matrix which makes @{term "Gauss_Jordan A = P ** A"}. If A is invertible, this matrix P will be the inverse of it.\<close>

definition Gauss_Jordan_in_ij_PA :: "(('a::{semiring_1, inverse, one, uminus}^'rows::{finite, ord}^'rows::{finite, ord}) \<times> ('a^'cols^'rows::{finite, ord})) => 'rows=>'cols
  =>(('a^'rows::{finite, ord}^'rows::{finite, ord}) \<times> ('a^'cols^'rows::{finite, ord}))"
where "Gauss_Jordan_in_ij_PA A' i j = (let P=fst A'; A=snd A';
                                        n = (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n);
                                        interchange_A = (interchange_rows A i n);
                                        interchange_P = (interchange_rows P i n);
                                        P' = mult_row interchange_P i (1/interchange_A$i$j)
                                        in                                        
                                       (vec_lambda(% s. if s=i then P' $ s else (row_add P' s i (-(interchange_A$s$j))) $ s), Gauss_Jordan_in_ij A i j))"

definition Gauss_Jordan_column_k_PA  
where "Gauss_Jordan_column_k_PA A' k =
    (let P = fst A';
         i = fst (snd A');
         A = snd (snd A');
         from_nat_i=from_nat i;
         from_nat_k=from_nat k
         in 
         if (\<forall>m\<ge>from_nat_i. A $ m $ from_nat_k = 0) \<or> i = nrows A then (P, i, A)
         else (let Gauss = Gauss_Jordan_in_ij_PA (P,A) (from_nat_i) (from_nat_k) in (fst Gauss, i + 1, snd Gauss)))"

definition "Gauss_Jordan_upt_k_PA A k = (let foldl=(foldl Gauss_Jordan_column_k_PA (mat 1,0, A) [0..<Suc k]) in (fst foldl, snd (snd foldl)))"
definition "Gauss_Jordan_PA A = Gauss_Jordan_upt_k_PA A (ncols A - 1)"

subsection\<open>Proofs\<close>

subsubsection\<open>Properties about @{term "Gauss_Jordan_in_ij_PA"}\<close>

text\<open>The following lemmas are very important in order to improve the efficience of the code\<close>
text\<open>We define the following function to obtain an efficient code for @{term "Gauss_Jordan_in_ij_PA A i j"}.\<close>

definition "Gauss_Jordan_wrapper i j A B = vec_lambda(%s. if s=i then A $ s else (row_add A s i (-(B$s$j))) $ s)"

lemma Gauss_Jordan_wrapper_code[code abstract]:
  "vec_nth (Gauss_Jordan_wrapper i j A B) = (%s. if s=i then A $ s else (row_add A s i (-(B$s$j))) $ s)"
  unfolding Gauss_Jordan_wrapper_def by force

lemma Gauss_Jordan_in_ij_PA_def'[code]:
   "Gauss_Jordan_in_ij_PA A' i j = (let P=fst A'; A=snd A';
                                        n = (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n);
                                        interchange_A = (interchange_rows A i n);
                                        A' = mult_row interchange_A i (1/interchange_A$i$j);
                                        interchange_P = (interchange_rows P i n);
                                        P' = mult_row interchange_P i (1/interchange_A$i$j)
                                        in                                       
                                       (Gauss_Jordan_wrapper i j P' interchange_A, 
                                        Gauss_Jordan_wrapper i j A' interchange_A))"
unfolding Gauss_Jordan_in_ij_PA_def Gauss_Jordan_in_ij_def Let_def Gauss_Jordan_wrapper_def by auto


text\<open>The second component is equal to @{term "Gauss_Jordan_in_ij"}\<close>
lemma snd_Gauss_Jordan_in_ij_PA_eq[code_unfold]: "snd (Gauss_Jordan_in_ij_PA (P,A) i j) = Gauss_Jordan_in_ij A i j"
  unfolding Gauss_Jordan_in_ij_PA_def Let_def snd_conv ..

lemma fst_Gauss_Jordan_in_ij_PA:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
assumes PB_A: "P ** B = A"
shows "fst (Gauss_Jordan_in_ij_PA (P,A) i j) ** B = snd (Gauss_Jordan_in_ij_PA (P,A) i j)"
proof (unfold Gauss_Jordan_in_ij_PA_def' Gauss_Jordan_wrapper_def Let_def fst_conv snd_conv, subst (1 2 3 4 5 6 7 8 9 10) interchange_rows_mat_1[symmetric], subst vec_eq_iff, auto)
show "((\<chi> s. if s = i then mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** P) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j) $ s
              else row_add (mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** P) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j)) s i
              (- (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ s $ j) $ s) ** B) $ i =
              mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j) $ i"
proof (unfold matrix_matrix_mult_def, vector, auto)
fix ia
have "mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** P) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j)
** B = mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j)"
by(subst (5) PB_A[symmetric], subst (1 2) mult_row_mat_1[symmetric], unfold matrix_mul_assoc, rule refl)
thus "(\<Sum>k\<in>UNIV. mult_row (\<chi> ia ja. \<Sum>k\<in>UNIV. interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ ia $ k * P $ k $ ja) i
                     (1 / (\<Sum>k\<in>UNIV. mat 1 $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ k * A $ k $ j)) $ i $ k * B $ k $ ia) =
                     mult_row (\<chi> ia ja. \<Sum>k\<in>UNIV. interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ ia $ k * A $ k $ ja) i
                     (1 / (\<Sum>k\<in>UNIV. mat 1 $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ k * A $ k $ j)) $ i $ ia"
unfolding matrix_matrix_mult_def
unfolding vec_lambda_beta unfolding interchange_rows_i using sum.cong
by (metis (lifting, no_types) vec_lambda_beta)
qed
next
fix ia assume ia_not_i: "ia \<noteq> i"
have "((\<chi> s. if s = i then mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** P) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j) $
             s else row_add (mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** P) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j)) s
             i (- (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ s $ j) $ s) ** B) $ ia =
((\<chi> s. row_add (mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** P) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j)) s
             i (- (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ s $ j) $ s) ** B) $ ia"
unfolding row_matrix_matrix_mult[symmetric]
using ia_not_i by auto
also have "... = row_add (mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** P) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j)) ia i
     (- (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ ia $ j) $ ia v* B"
     by (subst (3) row_matrix_matrix_mult[symmetric], simp)
also have "... = row_add (mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j)) ia i
             (- (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ ia $ j) $ ia"
apply (subst (7) PB_A[symmetric])
apply (subst (1 2) mult_row_mat_1[symmetric])
apply (subst (1 2) row_add_mat_1[symmetric])
unfolding matrix_mul_assoc
unfolding row_matrix_matrix_mult ..
finally show "((\<chi> s. if s = i then mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** P) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j) $ s
        else row_add (mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** P) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j)) s i
              (- (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ s $ j) $ s) ** B) $ ia =
  row_add (mult_row (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) i (1 / (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ i $ j)) ia i
   (- (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** A) $ ia $ j) $ ia" .
qed


subsubsection\<open>Properties about @{term "Gauss_Jordan_column_k_PA"}\<close>
lemma fst_Gauss_Jordan_column_k: 
assumes "i\<le>nrows A"
shows "fst (Gauss_Jordan_column_k (i, A) k) \<le> nrows A"
using assms unfolding Gauss_Jordan_column_k_def Let_def by auto

lemma fst_Gauss_Jordan_column_k_PA:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
assumes PB_A: "P ** B = A"
shows "fst (Gauss_Jordan_column_k_PA (P,i,A) k) ** B = snd (snd (Gauss_Jordan_column_k_PA (P,i,A) k))"
unfolding Gauss_Jordan_column_k_PA_def unfolding Let_def
unfolding fst_conv snd_conv by (auto intro: assms fst_Gauss_Jordan_in_ij_PA)

lemma snd_snd_Gauss_Jordan_column_k_PA_eq: 
shows "snd (snd (Gauss_Jordan_column_k_PA (P,i,A) k)) = snd (Gauss_Jordan_column_k (i,A) k)"
unfolding Gauss_Jordan_column_k_PA_def Gauss_Jordan_column_k_def unfolding Let_def snd_conv fst_conv unfolding snd_Gauss_Jordan_in_ij_PA_eq by auto

lemma fst_snd_Gauss_Jordan_column_k_PA_eq: 
shows "fst (snd (Gauss_Jordan_column_k_PA (P,i,A) k)) = fst (Gauss_Jordan_column_k (i,A) k)"
unfolding Gauss_Jordan_column_k_PA_def Gauss_Jordan_column_k_def unfolding Let_def snd_conv fst_conv by auto

subsubsection\<open>Properties about @{term "Gauss_Jordan_upt_k_PA"}\<close>

lemma fst_Gauss_Jordan_upt_k_PA:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "fst (Gauss_Jordan_upt_k_PA A k) ** A = snd (Gauss_Jordan_upt_k_PA A k)"
proof (induct k)
show "fst (Gauss_Jordan_upt_k_PA A 0) ** A = snd (Gauss_Jordan_upt_k_PA A 0)" unfolding Gauss_Jordan_upt_k_PA_def Let_def fst_conv snd_conv
apply auto unfolding snd_snd_Gauss_Jordan_column_k_PA_eq by (metis fst_Gauss_Jordan_column_k_PA matrix_mul_lid snd_snd_Gauss_Jordan_column_k_PA_eq)
next
case (Suc k)
have suc_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [Suc k]" by simp
show ?case 
unfolding Gauss_Jordan_upt_k_PA_def Let_def fst_conv snd_conv
unfolding suc_rw unfolding foldl_append unfolding List.foldl.simps using Suc.hyps[unfolded Gauss_Jordan_upt_k_PA_def Let_def fst_conv snd_conv]
by (metis fst_Gauss_Jordan_column_k_PA prod.collapse)
qed

lemma snd_foldl_Gauss_Jordan_column_k_eq:
"snd (foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<k]) = foldl Gauss_Jordan_column_k (0, A) [0..<k]"
proof (induct k)
case 0
show ?case by simp
case (Suc k)
have suc_rw: "[0..<Suc k] = [0..<k] @ [k]" by simp
show ?case 
unfolding suc_rw foldl_append unfolding List.foldl.simps by (metis Suc.hyps fst_snd_Gauss_Jordan_column_k_PA_eq snd_snd_Gauss_Jordan_column_k_PA_eq surjective_pairing)
qed

lemma snd_Gauss_Jordan_upt_k_PA:
shows "snd (Gauss_Jordan_upt_k_PA A k) = (Gauss_Jordan_upt_k A k)"
unfolding Gauss_Jordan_upt_k_PA_def Gauss_Jordan_upt_k_def Let_def
using snd_foldl_Gauss_Jordan_column_k_eq[of A "Suc k"] by simp

subsubsection\<open>Properties about @{term "Gauss_Jordan_PA"}\<close>

lemma fst_Gauss_Jordan_PA:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
shows "fst (Gauss_Jordan_PA A) ** A = snd (Gauss_Jordan_PA A)"
unfolding Gauss_Jordan_PA_def using fst_Gauss_Jordan_upt_k_PA by simp

lemma Gauss_Jordan_PA_eq:
shows "snd (Gauss_Jordan_PA A)= (Gauss_Jordan A)"
by (metis Gauss_Jordan_PA_def Gauss_Jordan_def snd_Gauss_Jordan_upt_k_PA)

subsubsection\<open>Proving that the transformation has been carried out by means of elementary operations\<close>
text\<open>This function is very similar to @{term "row_add_iterate"} one. It allows us to prove that @{term "fst (Gauss_Jordan_PA A)"} is an invertible matrix.
Concretly, it has been defined to demonstrate that @{term "fst (Gauss_Jordan_PA A)"} has been obtained by means of elementary operations applied to the identity matrix\<close>

fun row_add_iterate_PA :: "(('a::{semiring_1, uminus}^'m::{mod_type} ^'m::{mod_type}) \<times> ('a^'n^'m::{mod_type}))=> nat => 'm => 'n => 
    (('a^'m::{mod_type} ^'m::{mod_type}) \<times> ('a^'n^'m::{mod_type}))"
    where "row_add_iterate_PA (P,A) 0 i j = (if i=0 then (P,A) else (row_add P 0 i (-A $ 0 $ j), row_add A 0 i (-A $ 0 $ j)))"
         | "row_add_iterate_PA (P,A) (Suc n) i j = (if (Suc n = to_nat i) then row_add_iterate_PA (P,A) n i j
                  else row_add_iterate_PA ((row_add P (from_nat (Suc n)) i (- A $ (from_nat (Suc n)) $ j)), (row_add A (from_nat (Suc n)) i (- A $ (from_nat (Suc n)) $ j))) n i j)"

lemma fst_row_add_iterate_PA_preserves_greater_than_n:
  assumes n: "n<nrows A"
  and a: "to_nat a > n"
  shows "fst (row_add_iterate_PA (P,A) n i j) $ a $ b = P $ a $ b"
  using assms
proof (induct n arbitrary: A P)
  case 0
  show ?case unfolding row_add_iterate.simps
  proof (auto)
    assume "i \<noteq> 0"
    hence "a \<noteq> 0" by (metis "0.prems"(2) less_numeral_extra(3) to_nat_0)
    thus "row_add P 0 i (- A $ 0 $ j) $ a $ b = P $ a $ b" unfolding row_add_def by auto
  qed
next
  case (Suc n)  
  have row_add_iterate_A: "fst (row_add_iterate_PA (P,A) n i j) $ a $ b = P $ a $ b" using Suc.hyps Suc.prems by auto
  show ?case
  proof (cases "Suc n = to_nat i")
    case True
    show "fst (row_add_iterate_PA (P, A) (Suc n) i j) $ a $ b = P $ a $ b" unfolding row_add_iterate_PA.simps if_P[OF True] using row_add_iterate_A .
  next
    case False
    define A' where "A' = row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
    define P' where "P' = row_add P (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
    have row_add_iterate_A': "fst (row_add_iterate_PA (P',A') n i j) $ a $ b = P' $ a $ b" using Suc.hyps Suc.prems unfolding nrows_def by auto
    have from_nat_not_a: "from_nat (Suc n) \<noteq> a" by (metis less_not_refl Suc.prems to_nat_from_nat_id nrows_def)
    show "fst (row_add_iterate_PA (P, A) (Suc n) i j) $ a $ b = P $ a $ b" unfolding row_add_iterate_PA.simps if_not_P[OF False] row_add_iterate_A'[unfolded A'_def P'_def]
      unfolding row_add_def using from_nat_not_a by simp
  qed
qed



lemma snd_row_add_iterate_PA_eq_row_add_iterate:
shows "snd (row_add_iterate_PA (P,A) n i j)  = row_add_iterate A n i j"
proof (induct n arbitrary: P A)
case 0
show ?case unfolding row_add_iterate_PA.simps row_add_iterate.simps by simp
next
case (Suc n)
show ?case unfolding row_add_iterate_PA.simps row_add_iterate.simps by (simp add: Suc.hyps)
qed

lemma row_add_iterate_PA_preserves_pivot_row:
  assumes n: "n<nrows A"
  and a: "to_nat i \<le> n"
  shows "fst (row_add_iterate_PA (P,A) n i j) $ i $ b = P $ i $ b"
using assms
proof (induct n arbitrary: P A)
case 0
show ?case by (metis "0.prems"(2) fst_conv le_0_eq row_add_iterate_PA.simps(1) to_nat_eq_0)
next
case (Suc n)
show ?case
proof (cases "Suc n = to_nat i")
case True show ?thesis unfolding row_add_iterate_PA.simps if_P[OF True]
  proof (rule fst_row_add_iterate_PA_preserves_greater_than_n)
     show "n < nrows A" by (metis Suc.prems(1) Suc_lessD)
     show "n < to_nat i" by (metis True lessI)
  qed
next
case False
define P' where "P' = row_add P (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
define A' where "A' = row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
have from_nat_noteq_i: "from_nat (Suc n) \<noteq> i"  using False Suc.prems(1) from_nat_not_eq unfolding nrows_def by blast
have hyp: "fst (row_add_iterate_PA (P', A') n i j) $ i $ b = P' $ i $ b"
proof (rule Suc.hyps)
show "n < nrows A'" using Suc.prems(1) unfolding nrows_def by simp
show "to_nat i \<le> n" using Suc.prems(2) False by simp
qed
show ?thesis unfolding row_add_iterate_PA.simps unfolding if_not_P[OF False] unfolding hyp[unfolded A'_def P'_def]
unfolding row_add_def using from_nat_noteq_i by auto
qed
qed


lemma fst_row_add_iterate_PA_eq_row_add:
  fixes A::"'a::{ring_1}^'n^'m::{mod_type}"
  assumes a_not_i: "a \<noteq> i"
  and n: "n<nrows A"
  and "to_nat a \<le> n"
  shows "fst (row_add_iterate_PA (P,A) n i j) $ a $ b = (row_add P a i (- A $ a $ j)) $ a $ b" 
  using assms
proof (induct n arbitrary: A P)
case 0 show ?case by (metis "0.prems"(3) a_not_i fst_conv le_0_eq row_add_iterate_PA.simps(1) to_nat_eq_0)
next
case (Suc n)
show ?case 
proof (cases " Suc n = to_nat i")
case True
show ?thesis
unfolding row_add_iterate_PA.simps if_P[OF True]
proof (rule Suc.hyps[OF a_not_i])
show "n < nrows A" by (metis Suc.prems(2) Suc_lessD)
show "to_nat a \<le> n" by (metis Suc.prems(3) True a_not_i le_SucE to_nat_eq)
qed
next
case False note Suc_n_not_i=False
    show ?thesis  
    proof (cases "to_nat a = Suc n") 
case True
show "fst (row_add_iterate_PA (P, A) (Suc n) i j) $ a $ b = row_add P a i (- A $ a $ j) $ a $ b"
unfolding row_add_iterate_PA.simps if_not_P[OF False]
by (metis Suc_le_lessD True order_refl less_imp_le fst_row_add_iterate_PA_preserves_greater_than_n Suc.prems(2) to_nat_from_nat nrows_def)
next
case False
define A' where "A' = row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
define P' where "P' = row_add P (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
      have rw: "fst (row_add_iterate_PA (P',A') n i j) $ a $ b = row_add P' a i (- A' $ a $ j) $ a $ b"
      proof (rule Suc.hyps)
        show "a \<noteq> i" using Suc.prems(1) by simp
        show "n < nrows A'" using Suc.prems(2) unfolding nrows_def by auto
        show "to_nat a \<le> n" using False Suc.prems(3) by simp
      qed

      have rw1: "P' $ a $ b = P $ a $ b"
        unfolding P'_def row_add_def using False Suc.prems unfolding nrows_def by (auto simp add: to_nat_from_nat_id)
      have rw2: "A' $ a $ j = A $ a $ j"
          unfolding A'_def row_add_def using False Suc.prems unfolding nrows_def by (auto simp add: to_nat_from_nat_id)
      have rw3: "P' $ i $ b = P $ i $ b"
          unfolding P'_def row_add_def using False Suc.prems Suc_n_not_i unfolding nrows_def  by (auto simp add: to_nat_from_nat_id)
show "fst (row_add_iterate_PA (P, A) (Suc n) i j) $ a $ b = row_add P a i (- A $ a $ j) $ a $ b" 
unfolding row_add_iterate_PA.simps if_not_P[OF Suc_n_not_i] unfolding rw[unfolded P'_def A'_def]
  unfolding A'_def[symmetric] P'_def[symmetric] unfolding row_add_def apply auto
unfolding rw1 rw2 rw3 ..
    qed
  qed
qed




lemma fst_row_add_iterate_PA_eq_fst_Gauss_Jordan_in_ij_PA:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
and i::"'rows" and j::"'cols"
and P::"'a::{field}^'rows::{mod_type}^'rows::{mod_type}"
defines A': "A'== mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) $ i $ j)"
defines P': "P'== mult_row (interchange_rows P i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) $ i $ j)"
shows "fst (row_add_iterate_PA (P',A') (nrows A - 1) i j)  = fst (Gauss_Jordan_in_ij_PA (P,A) i j)"
proof (unfold Gauss_Jordan_in_ij_PA_def Let_def, vector, auto)
fix ia
have interchange_rw: "interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j = A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j"
using interchange_rows_j[symmetric, of A "(LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)"] by auto
show "fst (row_add_iterate_PA (P', A') (nrows A - Suc 0) i j) $ i $ ia =
         mult_row (interchange_rows P i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j) $ i $ ia"
unfolding A' P' interchange_rw
proof (rule row_add_iterate_PA_preserves_pivot_row, unfold nrows_def)
show "CARD('rows) - Suc 0 < CARD('rows)" by auto
show "to_nat i \<le> CARD('rows) - Suc 0" by (metis Suc_pred leD not_less_eq_eq to_nat_less_card zero_less_card_finite)
qed
next
  fix ia iaa
 have interchange_rw: "A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j = interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j"
   using interchange_rows_j[symmetric, of A "(LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)"] by auto
  assume ia_not_i: "ia \<noteq> i"
  have rw: "(- interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ ia $ j) 
    = - mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j) $ ia $ j"
    unfolding interchange_rows_def mult_row_def using ia_not_i by auto  
show "fst (row_add_iterate_PA (P', A') (nrows A - Suc 0) i j) $ ia $ iaa 
    = row_add (mult_row (interchange_rows P i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j)) ia i
    (- interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ ia $ j) $ ia $ iaa"  unfolding interchange_rw unfolding A' P' unfolding rw
proof (rule fst_row_add_iterate_PA_eq_row_add, unfold nrows_def)
 show "ia \<noteq> i" using ia_not_i .
 show "CARD('rows) - Suc 0 < CARD('rows)" using zero_less_card_finite by auto
 show "to_nat ia \<le> CARD('rows) - Suc 0" by (metis Suc_pred leD not_less_eq_eq to_nat_less_card zero_less_card_finite)
qed
qed


lemma invertible_fst_row_add_iterate_PA:
  fixes A::"'a::{ring_1}^'n^'m::{mod_type}"
  assumes n: "n<nrows A"
  and inv_P: "invertible P"
  shows "invertible (fst (row_add_iterate_PA (P,A) n i j))"
  using n inv_P
  proof (induct n arbitrary: A P)
  case 0
  show ?case 
    proof (unfold row_add_iterate_PA.simps, auto simp add: "0.prems")
      assume i_not_0: "i \<noteq> 0"
      have "row_add P 0 i (- A $ 0 $ j) = row_add (mat 1) 0 i (- A $ 0 $ j) ** P" unfolding row_add_mat_1 ..
      show "invertible (row_add P 0 i (- A $ 0 $ j))"
        by (subst row_add_mat_1[symmetric], rule invertible_mult, auto simp add: invertible_row_add[of 0 i "(- A $ 0 $ j)"] i_not_0 "0.prems")
    qed
    next
    case (Suc n)
    show ?case
      proof (cases "Suc n = to_nat i")
        case True
        show ?thesis unfolding row_add_iterate_PA.simps if_P[OF True] using Suc.hyps Suc.prems by simp
        next
        case False
        show ?thesis 
          proof (unfold row_add_iterate_PA.simps if_not_P[OF False], rule Suc.hyps, unfold nrows_def)
             show "n < CARD('m)" using Suc.prems(1) unfolding nrows_def by simp
             show "invertible (row_add P (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j))"
                proof (subst row_add_mat_1[symmetric], rule invertible_mult, rule invertible_row_add)
                   show "from_nat (Suc n) \<noteq> i" using False Suc.prems(1) from_nat_not_eq unfolding nrows_def by blast
                   show "invertible P" using Suc.prems(2) .
                qed
          qed
      qed
qed


lemma invertible_fst_Gauss_Jordan_in_ij_PA:
fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
assumes inv_P: "invertible P"
and not_all_zero: "\<not> (\<forall>m\<ge>i. A $ m $ j = 0)"
shows "invertible (fst (Gauss_Jordan_in_ij_PA (P,A) i j))" 
proof (unfold fst_row_add_iterate_PA_eq_fst_Gauss_Jordan_in_ij_PA[symmetric], rule invertible_fst_row_add_iterate_PA, simp add: nrows_def, 
subst interchange_rows_mat_1[symmetric], subst mult_row_mat_1[symmetric], rule invertible_mult)
show "invertible (mult_row (mat 1) i (1 / interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j))"
    proof (rule invertible_mult_row')
      have "interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j = A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j" by simp
      also have "... \<noteq> 0" by (metis (lifting, mono_tags) LeastI_ex not_all_zero)
      finally show "1 / interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j \<noteq> 0"
      unfolding inverse_eq_divide[symmetric] using nonzero_imp_inverse_nonzero by blast
    qed
show "invertible (interchange_rows (mat 1) i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) ** P)"
  by (rule invertible_mult, rule invertible_interchange_rows, rule inv_P)
qed


lemma invertible_fst_Gauss_Jordan_column_k_PA:
fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
assumes inv_P: "invertible P"
shows "invertible (fst (Gauss_Jordan_column_k_PA (P,i,A) k))" 
proof (unfold Gauss_Jordan_column_k_PA_def Let_def snd_conv fst_conv, auto simp add: inv_P)
fix m
assume i_less_m: "from_nat i \<le> m" and Amk_not_0: "A $ m $ from_nat k \<noteq> 0"
show "invertible (fst (Gauss_Jordan_in_ij_PA (P, A) (from_nat i) (from_nat k)))"
by (rule invertible_fst_Gauss_Jordan_in_ij_PA[OF inv_P], auto intro!: i_less_m Amk_not_0)
qed

lemma invertible_fst_Gauss_Jordan_upt_k_PA:
fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
shows "invertible (fst (Gauss_Jordan_upt_k_PA A k))"
proof (induct k)
case 0
show ?case unfolding Gauss_Jordan_upt_k_PA_def Let_def fst_conv by (simp add: invertible_fst_Gauss_Jordan_column_k_PA invertible_mat_1)
next
case (Suc k)
have list_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [Suc k]" by simp
define f where "f = foldl Gauss_Jordan_column_k_PA (mat 1, 0, A) [0..<Suc k]"
have f_rw: "f = (fst f, fst (snd f), snd (snd f))" by simp
show ?case unfolding Gauss_Jordan_upt_k_PA_def Let_def fst_conv
unfolding list_rw unfolding foldl_append unfolding List.foldl.simps using invertible_fst_Gauss_Jordan_column_k_PA
by (metis (mono_tags) Gauss_Jordan_upt_k_PA_def Suc.hyps fst_conv prod.collapse)
qed

lemma invertible_fst_Gauss_Jordan_PA:
fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
shows "invertible (fst (Gauss_Jordan_PA A))" 
by (unfold Gauss_Jordan_PA_def, rule invertible_fst_Gauss_Jordan_upt_k_PA)

definition "P_Gauss_Jordan A = fst (Gauss_Jordan_PA A)"

end
