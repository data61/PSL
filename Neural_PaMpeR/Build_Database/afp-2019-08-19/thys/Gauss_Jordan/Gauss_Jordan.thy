(*  
    Title:      Gauss_Jordan.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Gauss Jordan algorithm over abstract matrices\<close>

theory Gauss_Jordan
imports
  Rref
  Elementary_Operations
  Rank  
begin

subsection\<open>The Gauss-Jordan Algorithm\<close>

text\<open>Now, a computable version of the Gauss-Jordan algorithm is presented. The output will be a matrix in reduced row echelon form.
We present an algorithm in which the reduction is applied by columns\<close>

text\<open>Using this definition, zeros are made in the column j of a matrix A placing the pivot entry (a nonzero element) in the position (i,j).
For that, a suitable row interchange is made to achieve a non-zero entry in position (i,j). Then, this pivot entry is multiplied by its inverse
to make the pivot entry equals to 1. After that, are other entries of the j-th column are eliminated by subtracting suitable multiples of the
i-th row from the other rows.\<close>

definition Gauss_Jordan_in_ij :: "'a::{semiring_1, inverse, one, uminus}^'m^'n::{finite, ord}=> 'n=>'m=>'a^'m^'n::{finite, ord}"
where "Gauss_Jordan_in_ij A i j = (let n = (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n); 
                                interchange_A = (interchange_rows A i n); 
                                A' = mult_row interchange_A i (1/interchange_A$i$j) in 
                                vec_lambda(% s. if s=i then A' $ s else (row_add A' s i (-(interchange_A$s$j))) $ s))"

lemma Gauss_Jordan_in_ij_unfold:
  assumes "\<exists>n. A $ n $ j \<noteq> 0 \<and> i \<le> n"
  obtains n :: "'n::{finite, wellorder}" and interchange_A and A'
  where
    "(LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) = n"
    and "A $ n $ j \<noteq> 0"
    and "i \<le> n"
    and "interchange_A = interchange_rows A i n"
    and "A' = mult_row interchange_A i (1 / interchange_A $ i $ j)"
    and "Gauss_Jordan_in_ij A i j = vec_lambda (\<lambda>s. if s = i then A' $ s 
      else (row_add A' s i (- (interchange_A $ s $ j))) $ s)"
proof -
  from assms obtain m where Anj: "A $ m $ j \<noteq> 0 \<and> i \<le> m" ..
  moreover define n where "n = (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)"
  then have P1: "(LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) = n" by simp
  ultimately have P2: "A $ n $ j \<noteq> 0" and P3: "i \<le> n"
    using LeastI [of "\<lambda>n. A $ n $ j \<noteq> 0 \<and> i \<le> n" m] by simp_all
  define interchange_A where "interchange_A = interchange_rows A i n"
  then have P4: "interchange_A = interchange_rows A i n" by simp
  define A' where "A' = mult_row interchange_A i (1 / interchange_A $ i $ j)"
  then have P5: "A' = mult_row interchange_A i (1 / interchange_A $ i $ j)" by simp
  have P6: "Gauss_Jordan_in_ij A i j = vec_lambda (\<lambda>s. if s = i then A' $ s 
    else (row_add A' s i (- (interchange_A $ s $ j))) $ s)"
    by (simp only: Gauss_Jordan_in_ij_def P1 P4 [symmetric] P5 [symmetric] Let_def)
  from P1 P2 P3 P4 P5 P6 that show thesis by blast
qed
                                
text\<open>The following definition makes the step of Gauss-Jordan in a column. This function receives two input parameters: the column k
where the step of Gauss-Jordan must be applied and a pair (which consists of the row where the pivot should be placed in the column k and the original matrix).\<close>

definition Gauss_Jordan_column_k :: "(nat \<times> ('a::{zero,inverse,uminus,semiring_1}^'m::{mod_type}^'n::{mod_type})) 
=> nat => (nat \<times> ('a^'m::{mod_type}^'n::{mod_type}))"
where "Gauss_Jordan_column_k A' k = (let i=fst A'; A=(snd A'); from_nat_i=(from_nat i::'n); from_nat_k=(from_nat k::'m) in 
        if (\<forall>m\<ge>(from_nat_i). A $ m $(from_nat_k)=0) \<or> (i = nrows A) then (i,A) else (i+1, (Gauss_Jordan_in_ij A (from_nat_i) (from_nat_k))))"

text\<open>The following definition applies the Gauss-Jordan step from the first column up to the k one (included).\<close>

definition Gauss_Jordan_upt_k :: "'a::{inverse,uminus,semiring_1}^'columns::{mod_type}^'rows::{mod_type} => nat 
=> 'a^'columns::{mod_type}^'rows::{mod_type}"
 where "Gauss_Jordan_upt_k A k = snd (foldl Gauss_Jordan_column_k (0,A) [0..<Suc k])"

text\<open>Gauss-Jordan is to apply the @{term "Gauss_Jordan_column_k"} in all columns.\<close>
definition Gauss_Jordan :: "'a::{inverse,uminus,semiring_1}^'columns::{mod_type}^'rows::{mod_type}  
=> 'a^'columns::{mod_type}^'rows::{mod_type}"
 where "Gauss_Jordan A = Gauss_Jordan_upt_k A ((ncols A) - 1)"


subsection\<open>Properties about rref and the greatest nonzero row.\<close>

lemma greatest_plus_one_eq_0:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) = nrows A"
  shows "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 = 0"
proof -
  have "to_nat (GREATEST R. \<not> is_zero_row_upt_k R k A) + 1 = card (UNIV::'rows set)"
    using assms unfolding nrows_def by fastforce
  thus "(GREATEST n. \<not> is_zero_row_upt_k n k A) + (1::'rows) = (0::'rows)"
    using to_nat_plus_one_less_card by fastforce
qed

lemma from_nat_to_nat_greatest:
  fixes A::"'a::{zero}^'columns::{mod_type}^'rows::{mod_type}"
  shows "from_nat (Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A))) = (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
  unfolding Suc_eq_plus1
  unfolding to_nat_1[where ?'a='rows, symmetric]
  unfolding add_to_nat_def ..

lemma greatest_less_zero_row:
  fixes A::"'a::{one, zero}^'n::{mod_type}^'m::{finite,one,plus,linorder}"
  assumes r: "reduced_row_echelon_form_upt_k A k"
  and zero_i: "is_zero_row_upt_k i k A"
  and not_all_zero: "\<not> (\<forall>a. is_zero_row_upt_k a k A)"
  shows "(GREATEST m. \<not> is_zero_row_upt_k m k A) < i"
proof (rule ccontr)
  assume not_less_i: "\<not> (GREATEST m. \<not> is_zero_row_upt_k m k A) < i"
  have i_less_greatest: "i < (GREATEST m. \<not> is_zero_row_upt_k m k A)"
    by (metis (mono_tags, lifting) GreatestI neqE not_all_zero not_less_i zero_i) 
  have "is_zero_row_upt_k (GREATEST m. \<not> is_zero_row_upt_k m k A) k A"
    using r zero_i i_less_greatest unfolding reduced_row_echelon_form_upt_k_def by blast
  thus False using GreatestI_ex not_all_zero by fast
qed

lemma rref_suc_if_zero_below_greatest:
  fixes A::"'a::{one, zero}^'n::{mod_type}^'m::{finite,one,plus,linorder}"
  assumes r: "reduced_row_echelon_form_upt_k A k"
  and not_all_zero: "\<not> (\<forall>a. is_zero_row_upt_k a k A)" (*This premisse is necessary to assure the existence of the Greatest*)
  and all_zero_below_greatest: "\<forall>a. a>(GREATEST m. \<not> is_zero_row_upt_k m k A) \<longrightarrow> is_zero_row_upt_k a (Suc k) A"
  shows "reduced_row_echelon_form_upt_k A (Suc k)"
proof (rule reduced_row_echelon_form_upt_k_intro, auto)
  fix i j assume zero_i_suc: "is_zero_row_upt_k i (Suc k) A" and i_le_j: "i < j"
  have zero_i: "is_zero_row_upt_k i k A" using zero_i_suc unfolding is_zero_row_upt_k_def by simp
  have "i>(GREATEST m. \<not> is_zero_row_upt_k m k A)" by (rule greatest_less_zero_row[OF r zero_i not_all_zero])
  hence "j>(GREATEST m. \<not> is_zero_row_upt_k m k A)" using i_le_j by simp
  thus "is_zero_row_upt_k j (Suc k) A" using all_zero_below_greatest by fast
next
  fix i assume not_zero_i: "\<not> is_zero_row_upt_k i (Suc k) A"
  show "A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1" 
    using  greatest_less_zero_row[OF r _ not_all_zero] not_zero_i r all_zero_below_greatest
    unfolding reduced_row_echelon_form_upt_k_def 
    by fast
next
  fix i
  assume i: "i < i + 1" and not_zero_i: "\<not> is_zero_row_upt_k i (Suc k) A" and not_zero_suc_i: "\<not> is_zero_row_upt_k (i + 1) (Suc k) A"
  have not_zero_i_k: "\<not> is_zero_row_upt_k i k A"
  using all_zero_below_greatest greatest_less_zero_row[OF r _ not_all_zero] not_zero_i by blast
  have not_zero_suc_i: "\<not> is_zero_row_upt_k (i+1) k A"
     using all_zero_below_greatest greatest_less_zero_row[OF r _ not_all_zero] not_zero_suc_i by blast
  have aux:"(\<forall>i j. i + 1 = j \<and> i < j \<and> \<not> is_zero_row_upt_k i k A \<and> \<not> is_zero_row_upt_k j k A \<longrightarrow> (LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0))"
    using r unfolding reduced_row_echelon_form_upt_k_def by fast
  show "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)" using aux not_zero_i_k not_zero_suc_i i by simp
next
  fix i j assume "\<not> is_zero_row_upt_k i (Suc k) A" and "i \<noteq> j"
  thus "A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0"
    using all_zero_below_greatest greatest_less_zero_row not_all_zero r rref_upt_condition4 by blast
qed

lemma rref_suc_if_all_rows_not_zero:
  fixes A::"'a::{one, zero}^'n::{mod_type}^'m::{finite,one,plus,linorder}"
  assumes r: "reduced_row_echelon_form_upt_k A k"
  and all_not_zero: "\<forall>n. \<not> is_zero_row_upt_k n k A"
  shows "reduced_row_echelon_form_upt_k A (Suc k)"
proof (rule rref_suc_if_zero_below_greatest)
  show "reduced_row_echelon_form_upt_k A k" using r .
  show "\<not> (\<forall>a. is_zero_row_upt_k a k A)" using all_not_zero by auto
  show "\<forall>a>GREATEST m. \<not> is_zero_row_upt_k m k A. is_zero_row_upt_k a (Suc k) A"
    using all_not_zero not_greater_Greatest by blast
qed


lemma greatest_ge_nonzero_row:
  fixes A::"'a::{zero}^'n::{mod_type}^'m::{finite,linorder}"
  assumes "\<not> is_zero_row_upt_k i k A"
  shows "i \<le> (GREATEST m. \<not> is_zero_row_upt_k m k A)" using Greatest_ge[of "(\<lambda>m. \<not> is_zero_row_upt_k m k A)", OF assms] .

lemma greatest_ge_nonzero_row':
  fixes A::"'a::{zero, one}^'n::{mod_type}^'m::{finite, linorder, one, plus}"
  assumes r: "reduced_row_echelon_form_upt_k A k"
  and i: "i \<le> (GREATEST m. \<not> is_zero_row_upt_k m k A)"
  and not_all_zero: "\<not> (\<forall>a. is_zero_row_upt_k a k A)"
  shows "\<not> is_zero_row_upt_k i k A"
  using greatest_less_zero_row[OF r] i not_all_zero by fastforce

corollary row_greater_greatest_is_zero:
  fixes A::"'a::{zero}^'n::{mod_type}^'m::{finite,linorder}"
  assumes "(GREATEST m. \<not> is_zero_row_upt_k m k A) < i"
  shows "is_zero_row_upt_k i k A" using greatest_ge_nonzero_row assms by fastforce

subsection\<open>The proof of its correctness\<close>

text\<open>Properties of @{term "Gauss_Jordan_in_ij"}\<close>

lemma Gauss_Jordan_in_ij_1:
  fixes A::"'a::{field}^'m^'n::{finite, ord, wellorder}"
  assumes ex: "\<exists>n. A $ n $ j \<noteq> 0 \<and> i \<le> n"
  shows "(Gauss_Jordan_in_ij A i j) $ i $ j = 1"
proof (unfold Gauss_Jordan_in_ij_def Let_def mult_row_def interchange_rows_def, vector)
  obtain n where Anj: "A $ n $ j \<noteq> 0 \<and> i \<le> n" using ex by blast
  show "A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j \<noteq> 0" using LeastI[of "\<lambda>n. A $ n $ j \<noteq> 0 \<and> i \<le> n" n, OF Anj] by simp 
qed

lemma Gauss_Jordan_in_ij_0:
  fixes A::"'a::{field}^'m^'n::{finite, ord, wellorder}"
  assumes ex: "\<exists>n. A $ n $ j \<noteq> 0 \<and> i \<le> n" and a: "a \<noteq> i"
  shows "(Gauss_Jordan_in_ij A i j) $ a $ j = 0"
using ex apply (rule Gauss_Jordan_in_ij_unfold) using a by (simp add: mult_row_def interchange_rows_def row_add_def)

corollary Gauss_Jordan_in_ij_0':
  fixes A::"'a::{field}^'m^'n::{finite, ord, wellorder}"
  assumes ex: "\<exists>n. A $ n $ j \<noteq> 0 \<and> i \<le> n"
  shows "\<forall>a. a \<noteq> i \<longrightarrow> (Gauss_Jordan_in_ij A i j) $ a $ j = 0" using assms Gauss_Jordan_in_ij_0 by blast

lemma Gauss_Jordan_in_ij_preserves_previous_elements:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  assumes r: "reduced_row_echelon_form_upt_k A k"
  and not_zero_a: "\<not> is_zero_row_upt_k a k A"
  and exists_m: "\<exists>m. A $ m $ (from_nat k) \<noteq> 0 \<and> (GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> m"
  and Greatest_plus_1: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<noteq> 0"
  and j_le_k: "to_nat j < k"
  shows "Gauss_Jordan_in_ij A ((GREATEST m. \<not> is_zero_row_upt_k m k A) + 1) (from_nat k) $ i $ j = A $ i $ j"
proof (unfold Gauss_Jordan_in_ij_def Let_def interchange_rows_def mult_row_def row_add_def, auto)
  define last_nonzero_row where "last_nonzero_row = (GREATEST m. \<not> is_zero_row_upt_k m k A)"
  have "last_nonzero_row < (last_nonzero_row + 1)" by (rule  Suc_le'[of last_nonzero_row], auto simp add: last_nonzero_row_def Greatest_plus_1)  
  hence zero_row: "is_zero_row_upt_k (last_nonzero_row + 1) k A"
    using not_le greatest_ge_nonzero_row last_nonzero_row_def by fastforce
  hence A_greatest_0: "A $ (last_nonzero_row + 1) $ j = 0" unfolding is_zero_row_upt_k_def last_nonzero_row_def using j_le_k by auto
  then show "A $ (last_nonzero_row + 1) $ j / A $ (last_nonzero_row + 1) $ from_nat k = A $ (last_nonzero_row + 1) $ j"
    by simp
  show zero: "A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> n) $ j = 0"
  proof -
    define least_n where "least_n = (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> n)"
    have "\<exists>n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> n" by (metis exists_m)
    from this obtain n where n1: "A $ n $ from_nat k \<noteq> 0"  and n2: "(GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> n" by blast
    have "(GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> least_n"
      by (metis (lifting, full_types) LeastI_ex least_n_def n1 n2)
    hence "is_zero_row_upt_k least_n k A" using last_nonzero_row_def less_le rref_upt_condition1[OF r] zero_row by metis
    thus "A $ least_n $ j = 0" unfolding is_zero_row_upt_k_def using j_le_k by simp
  qed
  show "A $ ((GREATEST m. \<not> is_zero_row_upt_k m k A) + 1) $ j -
    A $ ((GREATEST m. \<not> is_zero_row_upt_k m k A) + 1) $ from_nat k *
    A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> n) $ j /
    A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> n) $ from_nat k =
    A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> n) $ j"
    unfolding last_nonzero_row_def[symmetric] unfolding A_greatest_0 unfolding last_nonzero_row_def unfolding zero by fastforce
  show "A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> n) $ j /
    A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<le> n) $ from_nat k =
    A $ ((GREATEST m. \<not> is_zero_row_upt_k m k A) + 1) $ j" unfolding zero using A_greatest_0 unfolding last_nonzero_row_def by simp
qed



lemma Gauss_Jordan_in_ij_preserves_previous_elements':
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  assumes all_zero: "\<forall>n. is_zero_row_upt_k n k A"
  and j_le_k: "to_nat j < k"
  and A_nk_not_zero: "A $ n $ (from_nat k) \<noteq> 0"
  shows "Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ j = A $ i $ j"
proof (unfold Gauss_Jordan_in_ij_def Let_def mult_row_def interchange_rows_def row_add_def, auto)
  have A_0_j: "A $ 0 $ j = 0"  using all_zero is_zero_row_upt_k_def j_le_k by blast
  then show "A $ 0 $ j / A $ 0 $ from_nat k = A $ 0 $ j" by simp
  show A_least_j: "A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> 0 \<le> n) $ j = 0" using all_zero is_zero_row_upt_k_def j_le_k by blast
  show "A $ 0 $ j -
    A $ 0 $ from_nat k * A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> 0 \<le> n) $ j /
    A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> 0 \<le> n) $ from_nat k =
    A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> 0 \<le> n) $ j" unfolding A_0_j A_least_j by fastforce
  show "A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> 0 \<le> n) $ j / A $ (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> 0 \<le> n) $ from_nat k = A $ 0 $ j"
    unfolding A_least_j A_0_j by simp
qed

lemma is_zero_after_Gauss:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  assumes zero_a: "is_zero_row_upt_k a k A"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and r: "reduced_row_echelon_form_upt_k A k"
  and greatest_less_ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
  and A_ma_k_not_zero: "A $ ma $ from_nat k \<noteq> 0"
  shows "is_zero_row_upt_k a k (Gauss_Jordan_in_ij A ((GREATEST m. \<not> is_zero_row_upt_k m k A) + 1) (from_nat k))"
proof (subst is_zero_row_upt_k_def, clarify)
  fix j::'n assume j_less_k: "to_nat j < k"
  have not_zero_g: "(GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<noteq> 0"
  proof (rule ccontr, simp)
    assume "(GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 = 0"
    hence "(GREATEST m. \<not> is_zero_row_upt_k m k A) = -1" using a_eq_minus_1 by blast
    hence "a\<le>(GREATEST m. \<not> is_zero_row_upt_k m k A)" using Greatest_is_minus_1 by auto
    hence "\<not> is_zero_row_upt_k a k A" using greatest_less_zero_row[OF r] not_zero_m by fastforce
    thus False using zero_a by contradiction
  qed
  have "Gauss_Jordan_in_ij A ((GREATEST m. \<not> is_zero_row_upt_k m k A) + 1) (from_nat k) $ a $ j = A $ a $ j"
    by (rule Gauss_Jordan_in_ij_preserves_previous_elements[OF r not_zero_m _ not_zero_g j_less_k], auto intro!: A_ma_k_not_zero greatest_less_ma)
  also have "... = 0" 
    using zero_a j_less_k unfolding is_zero_row_upt_k_def by blast
  finally show "Gauss_Jordan_in_ij A ((GREATEST m. \<not> is_zero_row_upt_k m k A) + 1) (from_nat k) $ a $ j = 0" .
qed


lemma all_zero_imp_Gauss_Jordan_column_not_zero_in_row_0:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes all_zero: "\<forall>n. is_zero_row_upt_k n k A"
  and not_zero_i: "\<not> is_zero_row_upt_k i (Suc k) B"
  and Amk_zero: "A $ m $ from_nat k \<noteq> 0"
  shows "i=0"
proof (rule ccontr)
  assume i_not_0: "i \<noteq> 0"
  have ia2: "ia = 0" using ia all_zero by simp
  have B_eq_Gauss: "B = Gauss_Jordan_in_ij A 0 (from_nat k)"
    unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2 
    using all_zero Amk_zero least_mod_type unfolding from_nat_0 nrows_def by auto
  also have "...$ i $ (from_nat k) = 0" proof (rule Gauss_Jordan_in_ij_0)
    show "\<exists>n. A $ n $ from_nat k \<noteq> 0 \<and> 0 \<le> n" using Amk_zero least_mod_type by blast
    show "i \<noteq> 0" using i_not_0 .
  qed
  finally have "B $ i $ from_nat k = 0" .
  hence "is_zero_row_upt_k i (Suc k) B"
    unfolding B_eq_Gauss
    using Gauss_Jordan_in_ij_preserves_previous_elements'[OF all_zero _ Amk_zero]
    by (metis all_zero is_zero_row_upt_k_def less_SucE to_nat_from_nat)
  thus False using not_zero_i by contradiction
qed

text\<open>Here we start to prove that 
      the output of @{term "Gauss Jordan A"} is a matrix in reduced row echelon form.\<close>

lemma condition_1_part_1:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes zero_column_k: "\<forall>m\<ge>from_nat 0. A $ m $ from_nat k = 0"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"
  shows "is_zero_row_upt_k j (Suc k) A"
  unfolding is_zero_row_upt_k_def apply clarify
proof -
  fix ja::'columns assume ja_less_suc_k: "to_nat ja < Suc k"
  show "A $ j $ ja = 0"
  proof (cases "to_nat ja < k")
    case True thus ?thesis using all_zero unfolding is_zero_row_upt_k_def by blast
  next
    case False hence ja_eq_k: "k = to_nat ja " using ja_less_suc_k by simp
    show ?thesis using zero_column_k unfolding ja_eq_k from_nat_to_nat_id from_nat_0 using least_mod_type by blast
  qed
qed

lemma condition_1_part_2:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes j_not_zero: "j \<noteq> 0"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A" 
  and Amk_not_zero: "A $ m $ from_nat k \<noteq> 0"
  shows "is_zero_row_upt_k j (Suc k) (Gauss_Jordan_in_ij A (from_nat 0) (from_nat k))"
proof (unfold is_zero_row_upt_k_def, clarify)
  fix ja::'columns
  assume ja_less_suc_k: "to_nat ja < Suc k"
  show "Gauss_Jordan_in_ij A (from_nat 0) (from_nat k) $ j $ ja = 0"
  proof (cases "to_nat ja < k")
    case True 
    have "Gauss_Jordan_in_ij A (from_nat 0) (from_nat k) $ j $ ja = A $ j $ ja"
      unfolding from_nat_0 using Gauss_Jordan_in_ij_preserves_previous_elements'[OF all_zero True Amk_not_zero] .
    also have "... = 0" using all_zero True unfolding is_zero_row_upt_k_def by blast
    finally show ?thesis .
  next
    case False hence k_eq_ja: "k = to_nat ja"
      using ja_less_suc_k by simp
    show "Gauss_Jordan_in_ij A (from_nat 0) (from_nat k) $ j $ ja = 0"
      unfolding k_eq_ja from_nat_to_nat_id
    proof (rule Gauss_Jordan_in_ij_0)
      show "\<exists>n. A $ n $ ja \<noteq> 0 \<and> from_nat 0 \<le> n"
        using least_mod_type Amk_not_zero
        unfolding k_eq_ja from_nat_to_nat_id from_nat_0 by blast
      show "j \<noteq> from_nat 0" using j_not_zero unfolding from_nat_0 .
    qed
  qed
qed

lemma condition_1_part_3:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B \<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and i_less_j: "i<j"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and zero_below_greatest: "\<forall>m\<ge>(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1. A $ m $ from_nat k = 0"
  and zero_i_suc_k: "is_zero_row_upt_k i (Suc k) B"
  shows "is_zero_row_upt_k j (Suc k) A"
proof (unfold is_zero_row_upt_k_def, auto)
  fix ja::'columns
  assume ja_less_suc_k: "to_nat ja < Suc k"
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_A: "B=A"
    unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2
    apply simp
    unfolding from_nat_to_nat_greatest using zero_below_greatest by blast
  have zero_ikA: "is_zero_row_upt_k i k A" using zero_i_suc_k unfolding B_eq_A is_zero_row_upt_k_def by fastforce
  hence zero_jkA: "is_zero_row_upt_k j k A" using rref_upt_condition1[OF rref] i_less_j by blast
  show "A $ j $ ja = 0"
  proof (cases "to_nat ja < k")
    case True
    thus ?thesis using zero_jkA unfolding is_zero_row_upt_k_def by blast
  next
    case False
    hence k_eq_ja:"k = to_nat ja" using ja_less_suc_k by auto
    have "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> j"
    proof (rule le_Suc, rule GreatestI2)
      show "\<not> is_zero_row_upt_k m k A" using not_zero_m .
      fix x assume not_zero_xkA: "\<not> is_zero_row_upt_k x k A" show "x < j"
        using rref_upt_condition1[OF rref] not_zero_xkA zero_jkA neq_iff by blast
    qed     
    thus ?thesis using zero_below_greatest unfolding k_eq_ja from_nat_to_nat_id is_zero_row_upt_k_def by blast
  qed
qed

lemma condition_1_part_4:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B \<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and zero_i_suc_k: "is_zero_row_upt_k i (Suc k) B" 
  and i_less_j: "i<j"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and greatest_eq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) = nrows A"
  shows "is_zero_row_upt_k j (Suc k) A"
proof -
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_A: "B=A"
    unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2
    unfolding from_nat_to_nat_greatest using greatest_eq_card nrows_def by force
  have rref_Suc: "reduced_row_echelon_form_upt_k A (Suc k)" 
  proof (rule rref_suc_if_zero_below_greatest[OF rref])
    show "\<forall>a>GREATEST m. \<not> is_zero_row_upt_k m k A. is_zero_row_upt_k a (Suc k) A"
      using greatest_eq_card not_less_eq to_nat_less_card to_nat_mono nrows_def by metis
    show "\<not> (\<forall>a. is_zero_row_upt_k a k A)" using not_zero_m by fast
  qed
  show ?thesis using zero_i_suc_k unfolding B_eq_A using rref_upt_condition1[OF rref_Suc] i_less_j by fast
qed


lemma condition_1_part_5:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B \<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and zero_i_suc_k: "is_zero_row_upt_k i (Suc k) B" 
  and i_less_j: "i<j"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and greatest_not_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
  and greatest_less_ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
  and A_ma_k_not_zero: "A $ ma $ from_nat k \<noteq> 0"
  shows "is_zero_row_upt_k j (Suc k) (Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k))"
proof (subst (1) is_zero_row_upt_k_def, clarify)
  fix ja::'columns assume ja_less_suc_k: "to_nat ja < Suc k"
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_Gauss_ij: "B = Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k)"
    unfolding B Gauss_Jordan_column_k_def 
    unfolding ia2 Let_def fst_conv snd_conv
    using greatest_not_card greatest_less_ma A_ma_k_not_zero
    by (auto simp add: from_nat_to_nat_greatest nrows_def)
  have zero_ikA: "is_zero_row_upt_k i k A" 
  proof (unfold is_zero_row_upt_k_def, clarify)
    fix a::'columns
    assume a_less_k: "to_nat a < k"
    have "A $ i $ a = Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ a" 
    proof (rule Gauss_Jordan_in_ij_preserves_previous_elements[symmetric])
      show "reduced_row_echelon_form_upt_k A k" using rref .
      show "\<not> is_zero_row_upt_k m k A" using not_zero_m .
      show "\<exists>n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> n" using A_ma_k_not_zero greatest_less_ma by blast
      show "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<noteq> 0" using suc_not_zero greatest_not_card unfolding nrows_def by simp
      show "to_nat a < k" using a_less_k .
    qed
    also have "... = 0" unfolding B_eq_Gauss_ij[symmetric] using zero_i_suc_k a_less_k unfolding is_zero_row_upt_k_def by simp
    finally show "A $ i $ a = 0" .
  qed
  hence zero_jkA: "is_zero_row_upt_k j k A" using rref_upt_condition1[OF rref] i_less_j by blast
  show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ j $ ja = 0"
  proof (cases "to_nat ja < k")
    case True
    have "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ j $ ja = A $ j $ ja" 
    proof (rule Gauss_Jordan_in_ij_preserves_previous_elements)
      show "reduced_row_echelon_form_upt_k A k" using rref .
      show "\<not> is_zero_row_upt_k m k A" using not_zero_m .
      show "\<exists>n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> n" using A_ma_k_not_zero greatest_less_ma by blast
      show "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<noteq> 0" using suc_not_zero greatest_not_card unfolding nrows_def by simp       
      show "to_nat ja < k" using True .
    qed
    also have "... = 0" using zero_jkA True unfolding is_zero_row_upt_k_def by fast
    finally show ?thesis .
  next
    case False hence k_eq_ja: "k = to_nat ja" using ja_less_suc_k by simp
    show ?thesis 
    proof (unfold k_eq_ja from_nat_to_nat_id, rule Gauss_Jordan_in_ij_0)
      show "\<exists>n. A $ n $ ja \<noteq> 0 \<and> (GREATEST n. \<not> is_zero_row_upt_k n (to_nat ja) A) + 1 \<le> n"
        using A_ma_k_not_zero greatest_less_ma k_eq_ja to_nat_from_nat by auto
      show "j \<noteq> (GREATEST n. \<not> is_zero_row_upt_k n (to_nat ja) A) + 1" 
      proof (unfold k_eq_ja[symmetric], rule ccontr)
        assume "\<not> j \<noteq> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
        hence j_eq: "j = (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" by fast
        hence "i < (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" using i_less_j by force
        hence i_le_greatest: "i \<le> (GREATEST n. \<not> is_zero_row_upt_k n k A)" using le_Suc not_less by auto
        hence "\<not> is_zero_row_upt_k i k A" using greatest_ge_nonzero_row'[OF rref] not_zero_m by fast
        thus "False" using zero_ikA by contradiction
      qed
    qed
  qed
qed


lemma condition_1:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and zero_i_suc_k: "is_zero_row_upt_k i (Suc k) B" and i_less_j: "i < j"
  shows "is_zero_row_upt_k j (Suc k) B"
proof (unfold B Gauss_Jordan_column_k_def ia Let_def fst_conv snd_conv, auto, unfold from_nat_to_nat_greatest)
  assume zero_k: "\<forall>m\<ge>from_nat 0. A $ m $ from_nat k = 0"  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"
  show "is_zero_row_upt_k j (Suc k) A"
    using condition_1_part_1[OF zero_k all_zero] .
next
  fix m
  assume all_zero: "\<forall>m. is_zero_row_upt_k m k A" and Amk_not_zero: "A $ m $ from_nat k \<noteq> 0"
  have j_not_0: "j \<noteq> 0" using i_less_j least_mod_type not_le by blast
  show "is_zero_row_upt_k j (Suc k) (Gauss_Jordan_in_ij A (from_nat 0) (from_nat k))"
    using condition_1_part_2[OF j_not_0 all_zero Amk_not_zero] .
next
  fix m assume not_zero_mkA: "\<not> is_zero_row_upt_k m k A"
    and zero_below_greatest: "\<forall>m\<ge>(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1. A $ m $ from_nat k = 0"
  show "is_zero_row_upt_k j (Suc k) A" using condition_1_part_3[OF rref i_less_j not_zero_mkA zero_below_greatest] zero_i_suc_k
    unfolding B ia .
next
  fix m assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and greatest_eq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) =  nrows A"
  show "is_zero_row_upt_k j (Suc k) A"
    using condition_1_part_4[OF rref _ i_less_j not_zero_m greatest_eq_card] zero_i_suc_k unfolding B ia nrows_def .
next
  fix m ma
  assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and greatest_not_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
and greatest_less_ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
    and A_ma_k_not_zero: "A $ ma $ from_nat k \<noteq> 0"
  show "is_zero_row_upt_k j (Suc k) (Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k))"
    using condition_1_part_5[OF rref _ i_less_j not_zero_m greatest_not_card greatest_less_ma A_ma_k_not_zero]
    using zero_i_suc_k
    unfolding B ia .
qed



lemma condition_2_part_1:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"
  and all_zero_k: "\<forall>m. A $ m $ from_nat k = 0"
  shows "A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1"
proof -
  have ia2: "ia = 0" using ia all_zero by simp
  have B_eq_A: "B=A" unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2 using all_zero_k by fastforce
  show ?thesis  using all_zero_k condition_1_part_1[OF _ all_zero] not_zero_i_suc_k unfolding B_eq_A by presburger
qed


lemma condition_2_part_2:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"
  and Amk_not_zero: "A $ m $ from_nat k \<noteq> 0"
  shows "Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ (LEAST ka. Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ ka \<noteq> 0) = 1"
proof -
  have ia2: "ia = 0" unfolding ia using all_zero by simp
  have B_eq: "B = Gauss_Jordan_in_ij A 0 (from_nat k)" unfolding B Gauss_Jordan_column_k_def unfolding ia2 Let_def fst_conv snd_conv
    using Amk_not_zero least_mod_type unfolding from_nat_0 nrows_def by auto
  have i_eq_0: "i=0" using Amk_not_zero B_eq all_zero condition_1_part_2 from_nat_0 not_zero_i_suc_k by metis
  have Least_eq: "(LEAST ka. Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ ka \<noteq> 0) = from_nat k"
  proof (rule Least_equality)
    have "Gauss_Jordan_in_ij A 0 (from_nat k) $ 0 $ from_nat k = 1" using Gauss_Jordan_in_ij_1 Amk_not_zero least_mod_type by blast
    thus "Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ from_nat k \<noteq> 0" unfolding i_eq_0 by simp
    fix y assume not_zero_gauss: "Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ y \<noteq> 0"
    show "from_nat k \<le> y"
    proof (rule ccontr)
      assume "\<not> from_nat k \<le> y" hence y: "y < from_nat k" by force
      have "Gauss_Jordan_in_ij A 0 (from_nat k) $ 0 $ y = A $ 0 $ y"
        by (rule Gauss_Jordan_in_ij_preserves_previous_elements'[OF all_zero to_nat_le[OF y] Amk_not_zero])
      also have "... = 0" using all_zero to_nat_le[OF y] unfolding is_zero_row_upt_k_def by blast
      finally show "False" using not_zero_gauss unfolding i_eq_0 by contradiction
    qed
  qed
  show ?thesis unfolding Least_eq unfolding i_eq_0 by (rule Gauss_Jordan_in_ij_1, auto intro!: Amk_not_zero least_mod_type)
qed




lemma condition_2_part_3:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and zero_below_greatest: "\<forall>m\<ge>(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1. A $ m $ from_nat k = 0"
  shows "A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1"
proof -
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_A: "B=A"
    unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2
    apply simp
    unfolding from_nat_to_nat_greatest using zero_below_greatest by blast
  show ?thesis
  proof (cases "to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 < CARD('rows)")
    case True
    have "\<not> is_zero_row_upt_k i k A"
    proof -
      have "i<(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
      proof (rule ccontr)
        assume "\<not> i < (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
        hence i: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> i" by simp
        hence "(GREATEST n. \<not> is_zero_row_upt_k n k A) < i" using le_Suc' True by simp
        hence zero_i: "is_zero_row_upt_k i k A" using not_greater_Greatest by blast
        hence "is_zero_row_upt_k i (Suc k) A" 
        proof (unfold is_zero_row_upt_k_def, clarify)
          fix j::'columns 
          assume "to_nat j < Suc k"
          thus "A $ i $ j = 0"
            using zero_i unfolding is_zero_row_upt_k_def using zero_below_greatest i 
            by (metis from_nat_to_nat_id le_neq_implies_less not_le not_less_eq_eq)
        qed        
        thus False using not_zero_i_suc_k unfolding B_eq_A by contradiction
      qed
      hence "i\<le>(GREATEST n. \<not> is_zero_row_upt_k n k A)" using not_le le_Suc by metis
      thus ?thesis using greatest_ge_nonzero_row'[OF rref] not_zero_m by fast
    qed
    thus ?thesis using rref_upt_condition2[OF rref] by blast
  next
    case False
    have greatest_plus_one_eq_0: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 = 0"
      using to_nat_plus_one_less_card False by blast
    have "\<not> is_zero_row_upt_k i k A"
    proof (rule not_is_zero_row_upt_suc)
      show "\<not> is_zero_row_upt_k i (Suc k) A" using not_zero_i_suc_k unfolding B_eq_A .
      show "\<forall>i. A $ i $ from_nat k = 0"
        using zero_below_greatest
        unfolding greatest_plus_one_eq_0 using least_mod_type by blast
    qed
    thus ?thesis using rref_upt_condition2[OF rref] by blast
  qed
qed

lemma condition_2_part_4:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and greatest_eq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) = nrows A"
  shows "A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1"
proof -
  have "\<not> is_zero_row_upt_k i k A"
  proof (rule ccontr, simp)
    assume zero_i: "is_zero_row_upt_k i k A"
    hence zero_minus_1: "is_zero_row_upt_k (-1) k A"
      using rref_upt_condition1[OF rref]
      using Greatest_is_minus_1 neq_le_trans by metis 
    have "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 = 0" using greatest_plus_one_eq_0[OF greatest_eq_card] .
    hence greatest_eq_minus_1: "(GREATEST n. \<not> is_zero_row_upt_k n k A) = -1" using a_eq_minus_1 by fast
    have "\<not> is_zero_row_upt_k (GREATEST n. \<not> is_zero_row_upt_k n k A) k A"
      by (rule greatest_ge_nonzero_row'[OF rref _ ], auto intro!: not_zero_m)
    thus "False" using zero_minus_1 unfolding greatest_eq_minus_1 by contradiction
  qed
  thus ?thesis using rref_upt_condition2[OF rref] by blast
qed


lemma condition_2_part_5:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and greatest_noteq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
  and greatest_less_ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
  and A_ma_k_not_zero: "A $ ma $ from_nat k \<noteq> 0"
  shows "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $
  (LEAST ka. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ ka \<noteq> 0) = 1"
proof -
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_Gauss: "B=Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k)"
    unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2
    apply simp
    unfolding from_nat_to_nat_greatest using greatest_noteq_card A_ma_k_not_zero greatest_less_ma by blast
  have greatest_plus_one_not_zero: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<noteq> 0"
    using suc_not_zero greatest_noteq_card unfolding nrows_def by auto
  show ?thesis
  proof (cases "is_zero_row_upt_k i k A")
    case True
    hence not_zero_iB: "is_zero_row_upt_k i k B" unfolding is_zero_row_upt_k_def unfolding B_eq_Gauss
      using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_m _ greatest_plus_one_not_zero]
      using A_ma_k_not_zero greatest_less_ma by fastforce
    hence Gauss_Jordan_i_not_0: "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ (from_nat k) \<noteq> 0"
      using not_zero_i_suc_k unfolding B_eq_Gauss unfolding is_zero_row_upt_k_def using from_nat_to_nat_id less_Suc_eq by (metis (lifting, no_types))
    have "i = ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
    proof (rule ccontr)
      assume i_not_greatest: "i \<noteq> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
      have "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ (from_nat k) = 0"
      proof (rule Gauss_Jordan_in_ij_0)
        show "\<exists>n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> n" using A_ma_k_not_zero greatest_less_ma by blast
        show "i \<noteq> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" using i_not_greatest .
      qed
      thus False using Gauss_Jordan_i_not_0 by contradiction
    qed
    hence Gauss_Jordan_i_1: "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ (from_nat k) = 1"
      using Gauss_Jordan_in_ij_1 using A_ma_k_not_zero greatest_less_ma by blast
    have Least_eq_k: "(LEAST ka. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ ka \<noteq> 0) = from_nat k"
    proof (rule Least_equality)
      show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ from_nat k \<noteq> 0" using Gauss_Jordan_i_not_0 .
      show  "\<And>y. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ y \<noteq> 0 \<Longrightarrow> from_nat k \<le> y"
        using B_eq_Gauss is_zero_row_upt_k_def not_less not_zero_iB to_nat_le by fast
    qed
    show ?thesis using Gauss_Jordan_i_1 unfolding Least_eq_k .
  next
    case False
    obtain j where Aij_not_0: "A $ i $ j \<noteq> 0" and j_le_k: "to_nat j < k" using False unfolding is_zero_row_upt_k_def by auto
    have least_le_k: "to_nat (LEAST ka. A $ i $ ka \<noteq> 0) < k"
      by (metis (lifting, mono_tags) Aij_not_0 j_le_k less_trans linorder_cases not_less_Least to_nat_mono)
    have least_le_j: "(LEAST ka. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ ka \<noteq> 0) \<le> j"
      using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_m _ greatest_plus_one_not_zero j_le_k] using A_ma_k_not_zero greatest_less_ma
      using Aij_not_0 False not_le_imp_less not_less_Least by (metis (mono_tags))
    have Least_eq: "(LEAST ka. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ ka \<noteq> 0) 
      = (LEAST ka. A $ i $ ka \<noteq> 0)"
    proof (rule Least_equality)
      show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ (LEAST ka. A $ i $ ka \<noteq> 0) \<noteq> 0" 
        using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref False _ greatest_plus_one_not_zero] least_le_k False rref_upt_condition2[OF rref]
        using  A_ma_k_not_zero B_eq_Gauss greatest_less_ma zero_neq_one by fastforce
      fix y assume Gauss_Jordan_y:"Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ y \<noteq> 0"
      show "(LEAST ka. A $ i $ ka \<noteq> 0) \<le> y"
      proof (cases "to_nat y < k")
        case False 
        thus ?thesis
          using least_le_k less_trans not_le_imp_less to_nat_from_nat to_nat_le by metis
      next
        case True
        have "A $ i $ y \<noteq> 0" using Gauss_Jordan_y using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_m _ greatest_plus_one_not_zero True]
          using A_ma_k_not_zero greatest_less_ma by fastforce
        thus ?thesis using Least_le by fastforce
      qed
    qed
    have "A $ i $ (LEAST ka. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ ka \<noteq> 0) = 1"
      using False using rref_upt_condition2[OF rref] unfolding Least_eq by blast   
    thus ?thesis unfolding Least_eq using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref False _ greatest_plus_one_not_zero]
      using least_le_k A_ma_k_not_zero greatest_less_ma by fastforce
  qed
qed


lemma condition_2:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  shows "B $ i $ (LEAST k. B $ i $ k \<noteq> 0) = 1"
proof (unfold B Gauss_Jordan_column_k_def ia Let_def fst_conv snd_conv, auto, unfold from_nat_to_nat_greatest from_nat_0)
  assume all_zero: "\<forall>m. is_zero_row_upt_k m k A" and all_zero_k: "\<forall>m\<ge>0. A $ m $ from_nat k = 0"
  show "A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1"
    using condition_2_part_1[OF _ all_zero] not_zero_i_suc_k all_zero_k least_mod_type unfolding B ia by blast
next
  fix m assume all_zero: "\<forall>m. is_zero_row_upt_k m k A"
    and Amk_not_zero: "A $ m $ from_nat k \<noteq> 0"
  show "Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ (LEAST ka. Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ ka \<noteq> 0) = 1"
    using condition_2_part_2[OF _ all_zero Amk_not_zero] not_zero_i_suc_k unfolding B ia .
next
  fix m
  assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and zero_below_greatest: "\<forall>m\<ge>(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1. A $ m $ from_nat k = 0" 
  show "A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1" using condition_2_part_3[OF rref _ not_zero_m zero_below_greatest] not_zero_i_suc_k unfolding B ia .
next
  fix m 
  assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and greatest_eq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) = nrows A"
  show "A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1" using condition_2_part_4[OF rref not_zero_m greatest_eq_card] .
next
  fix m ma
  assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and greatest_noteq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
    and greatest_less_ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
    and A_ma_k_not_zero: "A $ ma $ from_nat k \<noteq> 0"
  show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i 
    $ (LEAST ka. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ ka \<noteq> 0) = 1"
    using condition_2_part_5[OF rref _ not_zero_m greatest_noteq_card greatest_less_ma A_ma_k_not_zero] not_zero_i_suc_k unfolding B ia .
qed


lemma condition_3_part_1:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"
  and all_zero_k: "\<forall>m. A $ m $ from_nat k = 0"
  shows "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)"
proof -
  have ia2: "ia = 0" using ia all_zero by simp
  have B_eq_A: "B=A" unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2 using all_zero_k by fastforce
  have "is_zero_row_upt_k i (Suc k) B"  using all_zero all_zero_k unfolding B_eq_A is_zero_row_upt_k_def by (metis less_SucE to_nat_from_nat)
  thus ?thesis using not_zero_i_suc_k by contradiction
qed



lemma condition_3_part_2:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes i_le: "i < i + 1"
  and not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and not_zero_suc_i_suc_k: "\<not> is_zero_row_upt_k (i + 1) (Suc k) B"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"
  and Amk_notzero: "A $ m $ from_nat k \<noteq> 0"
  shows "(LEAST n. Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ n \<noteq> 0) < (LEAST n. Gauss_Jordan_in_ij A 0 (from_nat k) $ (i + 1) $ n \<noteq> 0)"
proof -
  have ia2: "ia = 0" using ia all_zero by simp
  have B_eq_Gauss: "B = Gauss_Jordan_in_ij A 0 (from_nat k)"
    unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2 
    using all_zero Amk_notzero least_mod_type unfolding from_nat_0 by auto
  have "i=0" using all_zero_imp_Gauss_Jordan_column_not_zero_in_row_0[OF all_zero _ Amk_notzero] not_zero_i_suc_k unfolding B ia .
  moreover have "i+1=0" using all_zero_imp_Gauss_Jordan_column_not_zero_in_row_0[OF all_zero _ Amk_notzero] not_zero_suc_i_suc_k unfolding B ia .
  ultimately show ?thesis using i_le by auto
qed



lemma condition_3_part_3:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and i_le: "i < i + 1"
  and not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and not_zero_suc_i_suc_k: "\<not> is_zero_row_upt_k (i + 1) (Suc k) B"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and zero_below_greatest: "\<forall>m\<ge>(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1. A $ m $ from_nat k = 0"
  shows "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)"
proof -
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_A: "B=A"
    unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2
    apply simp
    unfolding from_nat_to_nat_greatest using zero_below_greatest by blast
  have rref_suc: "reduced_row_echelon_form_upt_k A (Suc k)"
  proof (rule rref_suc_if_zero_below_greatest)
    show "reduced_row_echelon_form_upt_k A k" using rref .
    show "\<not> (\<forall>a. is_zero_row_upt_k a k A)" using not_zero_m by fast
    show "\<forall>a>GREATEST m. \<not> is_zero_row_upt_k m k A. is_zero_row_upt_k a (Suc k) A"
    proof (clarify)
      fix a::'rows assume greatest_less_a:  "(GREATEST m. \<not> is_zero_row_upt_k m k A) < a"
      show "is_zero_row_upt_k a (Suc k) A"
      proof (rule is_zero_row_upt_k_suc)
        show "is_zero_row_upt_k a k A" using greatest_less_a row_greater_greatest_is_zero by fast
        show "A $ a $ from_nat k = 0" using  le_Suc[OF greatest_less_a] zero_below_greatest by fast
      qed    
    qed
  qed
  show ?thesis using rref_upt_condition3[OF rref_suc] i_le not_zero_i_suc_k not_zero_suc_i_suc_k unfolding B_eq_A by blast
qed



lemma condition_3_part_4:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k" and i_le: "i < i + 1"
  and not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and not_zero_suc_i_suc_k: "\<not> is_zero_row_upt_k (i + 1) (Suc k) B"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and greatest_eq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) = nrows A"
  shows "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)"
proof -
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_A: "B=A"
    unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2
    unfolding from_nat_to_nat_greatest using greatest_eq_card by simp
  have greatest_eq_minus_1: "(GREATEST n. \<not> is_zero_row_upt_k n k A) = -1"
    using a_eq_minus_1 greatest_eq_card to_nat_plus_one_less_card unfolding nrows_def by fastforce
  have rref_suc: "reduced_row_echelon_form_upt_k A (Suc k)"
  proof (rule rref_suc_if_all_rows_not_zero)
    show "reduced_row_echelon_form_upt_k A k" using rref .
    show "\<forall>n. \<not> is_zero_row_upt_k n k A" using Greatest_is_minus_1 greatest_eq_minus_1 greatest_ge_nonzero_row'[OF rref _] not_zero_m by metis
  qed
  show ?thesis using rref_upt_condition3[OF rref_suc] i_le not_zero_i_suc_k not_zero_suc_i_suc_k unfolding B_eq_A by blast
qed

lemma condition_3_part_5:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and i_le: "i < i + 1"
  and not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and not_zero_suc_i_suc_k: "\<not> is_zero_row_upt_k (i + 1) (Suc k) B"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and greatest_not_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
  and greatest_less_ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
  and A_ma_k_not_zero: "A $ ma $ from_nat k \<noteq> 0"
  shows "(LEAST n. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ n \<noteq> 0)
  < (LEAST n. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i + 1) $ n \<noteq> 0)"
proof -
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_Gauss: "B = Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k)"
    unfolding B Gauss_Jordan_column_k_def 
    unfolding ia2 Let_def fst_conv snd_conv
    using greatest_not_card greatest_less_ma A_ma_k_not_zero
    by (auto simp add: from_nat_to_nat_greatest)
  have suc_greatest_not_zero: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<noteq> 0"
    using Suc_eq_plus1 suc_not_zero greatest_not_card unfolding nrows_def by auto
  show ?thesis
  proof (cases "is_zero_row_upt_k (i + 1) k A")
    case True
    have zero_i_plus_one_k_B: "is_zero_row_upt_k (i+1) k B" 
      by (unfold B_eq_Gauss, rule is_zero_after_Gauss[OF True not_zero_m rref greatest_less_ma A_ma_k_not_zero])
    hence Gauss_Jordan_i_not_0: "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i+1) $ (from_nat k) \<noteq> 0"
      using not_zero_suc_i_suc_k unfolding B_eq_Gauss using is_zero_row_upt_k_suc by blast
    have i_plus_one_eq: "i + 1 = ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
    proof (rule ccontr)
      assume i_not_greatest: "i + 1 \<noteq> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
      have "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i + 1) $ (from_nat k) = 0"
      proof (rule Gauss_Jordan_in_ij_0)
        show "\<exists>n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> n" using greatest_less_ma A_ma_k_not_zero by blast
        show "i + 1 \<noteq> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" using i_not_greatest .
      qed
      thus False using Gauss_Jordan_i_not_0 by contradiction
    qed
    hence i_eq_greatest: "i=(GREATEST n. \<not> is_zero_row_upt_k n k A)" using add_right_cancel by simp
    have Least_eq_k: "(LEAST ka. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i+1) $ ka \<noteq> 0) = from_nat k"
    proof (rule Least_equality)
      show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i+1) $ from_nat k \<noteq> 0" by (metis Gauss_Jordan_i_not_0)
      fix y assume "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i+1) $ y \<noteq> 0"
      thus "from_nat k \<le> y" using zero_i_plus_one_k_B  unfolding i_eq_greatest B_eq_Gauss by (metis is_zero_row_upt_k_def not_less to_nat_le)   
    qed
    have not_zero_i_A: "\<not> is_zero_row_upt_k i k A" using greatest_less_zero_row[OF rref] not_zero_m unfolding i_eq_greatest by fast
    from this obtain j where Aij_not_0: "A $ i $ j \<noteq> 0" and j_le_k: "to_nat j < k" unfolding is_zero_row_upt_k_def by blast
    have least_le_k: "to_nat (LEAST ka. A $ i $ ka \<noteq> 0) < k"
      by (metis (lifting, mono_tags) Aij_not_0 j_le_k less_trans linorder_cases not_less_Least to_nat_mono)
    have Least_eq: " (LEAST n. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ n \<noteq> 0) = 
      (LEAST n. A $ i $ n \<noteq> 0)"
    proof (rule Least_equality)
      show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ (LEAST ka. A $ i $ ka \<noteq> 0) \<noteq> 0" 
        using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_i_A _ suc_greatest_not_zero least_le_k] greatest_less_ma A_ma_k_not_zero
        using rref_upt_condition2[OF rref] not_zero_i_A by fastforce        
      fix y assume Gauss_Jordan_y:"Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ y \<noteq> 0"
      show "(LEAST ka. A $ i $ ka \<noteq> 0) \<le> y"
      proof (cases "to_nat y < k")
        case False thus ?thesis by (metis not_le least_le_k less_trans to_nat_mono)
      next
        case True
        have "A $ i $ y \<noteq> 0" using Gauss_Jordan_y using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_m _ suc_greatest_not_zero True]
          using A_ma_k_not_zero greatest_less_ma by fastforce
        thus ?thesis using Least_le by fastforce
      qed
    qed
    also have "... < from_nat k" by (metis is_zero_row_upt_k_def is_zero_row_upt_k_suc le_less_linear le_less_trans least_le_k not_zero_suc_i_suc_k to_nat_mono' zero_i_plus_one_k_B) 
    finally show ?thesis unfolding Least_eq_k .
  next
    case False
    have not_zero_i_A: "\<not> is_zero_row_upt_k i k A" using rref_upt_condition1[OF rref] False i_le by blast 
    from this obtain j where Aij_not_0: "A $ i $ j \<noteq> 0" and j_le_k: "to_nat j < k" unfolding is_zero_row_upt_k_def by blast
    have least_le_k: "to_nat (LEAST ka. A $ i $ ka \<noteq> 0) < k"
      by (metis (lifting, mono_tags) Aij_not_0 j_le_k less_trans linorder_cases not_less_Least to_nat_mono)
    have Least_i_eq: "(LEAST n. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ n \<noteq> 0)
      = (LEAST n. A $ i $ n \<noteq> 0)"
    proof (rule Least_equality)
      show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ (LEAST ka. A $ i $ ka \<noteq> 0) \<noteq> 0" 
        using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_i_A _ suc_greatest_not_zero least_le_k] greatest_less_ma A_ma_k_not_zero
        using rref_upt_condition2[OF rref] not_zero_i_A by fastforce
      fix y assume Gauss_Jordan_y:"Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ y \<noteq> 0"
      show "(LEAST ka. A $ i $ ka \<noteq> 0) \<le> y"
      proof (cases "to_nat y < k")
        case False thus ?thesis by (metis not_le not_less_iff_gr_or_eq le_less_trans least_le_k to_nat_mono)
      next
        case True
        have "A $ i $ y \<noteq> 0" using Gauss_Jordan_y using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_m _ suc_greatest_not_zero True]
          using A_ma_k_not_zero greatest_less_ma by fastforce
        thus ?thesis using Least_le by fastforce
      qed
    qed
    from False obtain s where Ais_not_0: "A $ (i+1) $ s \<noteq> 0" and s_le_k: "to_nat s < k" unfolding is_zero_row_upt_k_def by blast
    have least_le_k: "to_nat (LEAST ka. A $ (i+1) $ ka \<noteq> 0) < k" 
      by (metis (lifting, mono_tags) Ais_not_0 s_le_k neq_iff less_trans not_less_Least to_nat_mono) 
    have Least_i_plus_one_eq: "(LEAST n. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i+1) $ n \<noteq> 0)
      = (LEAST n. A $ (i+1) $ n \<noteq> 0)"
    proof (rule Least_equality)
      show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i+1) $ (LEAST ka. A $ (i+1) $ ka \<noteq> 0) \<noteq> 0" 
        using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_i_A _ suc_greatest_not_zero least_le_k] greatest_less_ma A_ma_k_not_zero
        using rref_upt_condition2[OF rref] False by fastforce
      fix y assume Gauss_Jordan_y:"Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i+1) $ y \<noteq> 0"
      show "(LEAST ka. A $ (i+1) $ ka \<noteq> 0) \<le> y"
      proof (cases "to_nat y < k")
        case False thus ?thesis by (metis (mono_tags) le_less_linear least_le_k less_trans to_nat_mono)
      next
        case True
        have "A $ (i+1) $ y \<noteq> 0" using Gauss_Jordan_y using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_m _ suc_greatest_not_zero True]
          using A_ma_k_not_zero greatest_less_ma by fastforce
        thus ?thesis using Least_le by fastforce
      qed
    qed
    show ?thesis unfolding Least_i_plus_one_eq Least_i_eq using rref_upt_condition3[OF rref] i_le False not_zero_i_A by blast
  qed
qed

lemma condition_3:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and i_le: "i < i + 1"
  and not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and not_zero_suc_i_suc_k: "\<not> is_zero_row_upt_k (i + 1) (Suc k) B"
  shows "(LEAST n. B $ i $ n \<noteq> 0) < (LEAST n. B $ (i + 1) $ n \<noteq> 0)"
proof (unfold B Gauss_Jordan_column_k_def ia Let_def fst_conv snd_conv, auto, unfold from_nat_to_nat_greatest from_nat_0)
  assume all_zero: "\<forall>m. is_zero_row_upt_k m k A"
    and all_zero_k: "\<forall>m\<ge>0. A $ m $ from_nat k = 0"
  show "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)"
    using condition_3_part_1[OF _ all_zero] using all_zero_k least_mod_type not_zero_i_suc_k unfolding B ia by fast
next
  fix m assume all_zero: "\<forall>m. is_zero_row_upt_k m k A"
    and Amk_notzero: "A $ m $ from_nat k \<noteq> 0"
  show "(LEAST n. Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ n \<noteq> 0) < (LEAST n. Gauss_Jordan_in_ij A 0 (from_nat k) $ (i + 1) $ n \<noteq> 0)"
    using condition_3_part_2[OF i_le _ _ all_zero Amk_notzero] using not_zero_i_suc_k not_zero_suc_i_suc_k unfolding B ia .
next
  fix m
  assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and zero_below_greatest: "\<forall>m\<ge>(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1. A $ m $ from_nat k = 0"
  show "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)"
    using condition_3_part_3[OF rref i_le _ _ not_zero_m zero_below_greatest] using not_zero_i_suc_k not_zero_suc_i_suc_k unfolding B ia .
next
  fix m
  assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and greatest_eq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) = nrows A"
  show "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)"
    using condition_3_part_4[OF rref i_le _ _ not_zero_m greatest_eq_card] using not_zero_i_suc_k not_zero_suc_i_suc_k unfolding B ia .
next
  fix m ma
  assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and greatest_not_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
    and greatest_less_ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
    and A_ma_k_not_zero: "A $ ma $ from_nat k \<noteq> 0"
  show "(LEAST n. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ n \<noteq> 0) 
    < (LEAST n. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i + 1) $ n \<noteq> 0)"
    using condition_3_part_5[OF rref i_le _ _ not_zero_m greatest_not_card greatest_less_ma A_ma_k_not_zero]
    using not_zero_i_suc_k not_zero_suc_i_suc_k unfolding B ia .
qed


lemma condition_4_part_1:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes not_zero_i_suc_k:  "\<not> is_zero_row_upt_k i (Suc k) B"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"
  and all_zero_k: "\<forall>m. A $ m $ from_nat k = 0"
  shows "A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0"
proof -
  have ia2: "ia = 0" using ia all_zero by simp
  have B_eq_A: "B=A" unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2 using all_zero_k by fastforce
  show ?thesis using B_eq_A all_zero all_zero_k is_zero_row_upt_k_suc not_zero_i_suc_k by blast
qed


lemma condition_4_part_2:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes not_zero_i_suc_k: "\<not> is_zero_row_upt_k i (Suc k) B"
  and i_not_j: "i \<noteq> j"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"
  and Amk_not_zero: "A $ m $ from_nat k \<noteq> 0"
  shows "Gauss_Jordan_in_ij A 0 (from_nat k) $ j $ (LEAST n. Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ n \<noteq> 0) = 0"
proof -
  have i_eq_0: "i=0" using all_zero_imp_Gauss_Jordan_column_not_zero_in_row_0[OF all_zero _ Amk_not_zero] not_zero_i_suc_k unfolding B ia .
  have least_eq_k: "(LEAST n. Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ n \<noteq> 0) = from_nat k"
  proof (rule Least_equality)
    show "Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ from_nat k \<noteq> 0" unfolding i_eq_0 using Amk_not_zero Gauss_Jordan_in_ij_1 least_mod_type zero_neq_one by fastforce
    fix y assume Gauss_Jordan_y_not_0: "Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ y \<noteq> 0"
    show "from_nat k \<le> y"
    proof (rule ccontr)
      assume "\<not> from_nat k \<le> y"
      hence "y < (from_nat k)" by simp
      hence to_nat_y_less_k: "to_nat y < k" using to_nat_le by auto
      have "Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ y = 0" 
        using Gauss_Jordan_in_ij_preserves_previous_elements'[OF all_zero to_nat_y_less_k Amk_not_zero] all_zero to_nat_y_less_k
        unfolding is_zero_row_upt_k_def  by fastforce
      thus False using Gauss_Jordan_y_not_0 by contradiction
    qed
  qed
  show ?thesis unfolding least_eq_k apply (rule Gauss_Jordan_in_ij_0) using i_eq_0 i_not_j Amk_not_zero least_mod_type by blast+
qed


lemma condition_4_part_3:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and not_zero_i_suc_k:  "\<not> is_zero_row_upt_k i (Suc k) B"
  and i_not_j: "i \<noteq> j"
  and not_zero_m: " \<not> is_zero_row_upt_k m k A"
  and zero_below_greatest: "\<forall>m\<ge>(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1. A $ m $ from_nat k = 0" 
  shows "A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0"
proof -
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_A: "B=A"
    unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2
    apply simp
    unfolding from_nat_to_nat_greatest using zero_below_greatest by blast
  have rref_suc: "reduced_row_echelon_form_upt_k A (Suc k)"
  proof (rule rref_suc_if_zero_below_greatest[OF rref], auto intro!: not_zero_m)
    fix a
    assume greatest_less_a: "(GREATEST m. \<not> is_zero_row_upt_k m k A) < a"
    show "is_zero_row_upt_k a (Suc k) A"
    proof (rule is_zero_row_upt_k_suc)  
      show "is_zero_row_upt_k a k A" using row_greater_greatest_is_zero[OF greatest_less_a] .
      show "A $ a $ from_nat k = 0" using zero_below_greatest  le_Suc[OF greatest_less_a] by blast
    qed
  qed
  show ?thesis using rref_upt_condition4[OF rref_suc] not_zero_i_suc_k i_not_j unfolding B_eq_A by blast
qed   

lemma condition_4_part_4:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and not_zero_i_suc_k:  "\<not> is_zero_row_upt_k i (Suc k) B"
  and i_not_j: "i \<noteq> j"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and greatest_eq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) = nrows A"
  shows "A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0"
proof -
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_A: "B=A"
    unfolding B Gauss_Jordan_column_k_def Let_def fst_conv snd_conv ia2
    unfolding from_nat_to_nat_greatest using greatest_eq_card by simp
  have greatest_eq_minus_1: "(GREATEST n. \<not> is_zero_row_upt_k n k A) = -1"
    using a_eq_minus_1 greatest_eq_card to_nat_plus_one_less_card unfolding nrows_def by fastforce
  have rref_suc: "reduced_row_echelon_form_upt_k A (Suc k)"
  proof (rule rref_suc_if_all_rows_not_zero)
    show "reduced_row_echelon_form_upt_k A k" using rref .
    show "\<forall>n. \<not> is_zero_row_upt_k n k A" using Greatest_is_minus_1 greatest_eq_minus_1 greatest_ge_nonzero_row'[OF rref _] not_zero_m by metis
  qed
  show ?thesis using rref_upt_condition4[OF rref_suc] using not_zero_i_suc_k i_not_j unfolding B_eq_A i_not_j by blast
qed

lemma condition_4_part_5:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and not_zero_i_suc_k:  "\<not> is_zero_row_upt_k i (Suc k) B"
  and i_not_j: "i \<noteq> j"
  and not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and greatest_not_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
  and greatest_less_ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
  and A_ma_k_not_zero: "A $ ma $ from_nat k \<noteq> 0"
  shows "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ j $ 
  (LEAST n. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ n \<noteq> 0) = 0"
proof -
  have ia2: "ia=to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" unfolding ia using not_zero_m by presburger
  have B_eq_Gauss: "B = Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k)"
    unfolding B Gauss_Jordan_column_k_def 
    unfolding ia2 Let_def fst_conv snd_conv
    using greatest_not_card greatest_less_ma A_ma_k_not_zero
    by (auto simp add: from_nat_to_nat_greatest)
  have suc_greatest_not_zero: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<noteq> 0"
    using Suc_eq_plus1 suc_not_zero greatest_not_card unfolding nrows_def by auto
  show ?thesis
  proof (cases "is_zero_row_upt_k i k A")
    case True
    have zero_i_k_B: "is_zero_row_upt_k i k B" unfolding B_eq_Gauss by (rule is_zero_after_Gauss[OF True not_zero_m rref greatest_less_ma A_ma_k_not_zero])
    hence Gauss_Jordan_i_not_0: "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ (i) $ (from_nat k) \<noteq> 0"
      using not_zero_i_suc_k unfolding B_eq_Gauss using is_zero_row_upt_k_suc by blast
    have i_eq_greatest: "i = ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
    proof (rule ccontr)
      assume i_not_greatest: "i \<noteq> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
      have "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ (from_nat k) = 0"
      proof (rule Gauss_Jordan_in_ij_0)
        show "\<exists>n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> n" using greatest_less_ma A_ma_k_not_zero by blast
        show "i \<noteq> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" using i_not_greatest .
      qed
      thus False using Gauss_Jordan_i_not_0 by contradiction
    qed    
    have Gauss_Jordan_i_1: "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ (from_nat k) = 1"
      unfolding i_eq_greatest using Gauss_Jordan_in_ij_1 greatest_less_ma A_ma_k_not_zero by blast
    have Least_eq_k: "(LEAST ka. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ ka \<noteq> 0) = from_nat k"
    proof (rule Least_equality)
      show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ from_nat k \<noteq> 0" using Gauss_Jordan_i_not_0 .
      fix y assume "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ y \<noteq> 0"
      thus "from_nat k \<le> y" using zero_i_k_B  unfolding i_eq_greatest B_eq_Gauss by (metis is_zero_row_upt_k_def not_less to_nat_le)   
    qed
    show ?thesis using A_ma_k_not_zero Gauss_Jordan_in_ij_0' Least_eq_k greatest_less_ma i_eq_greatest i_not_j by force
  next
    case False
    obtain n where Ain_not_0: "A $ i $ n \<noteq> 0" and j_le_k: "to_nat n < k" using False unfolding is_zero_row_upt_k_def by auto
    have least_le_k: "to_nat (LEAST ka. A $ i $ ka \<noteq> 0) < k" 
      by (metis (lifting, mono_tags) Ain_not_0 neq_iff j_le_k less_trans not_less_Least to_nat_mono)
    have Least_eq: "(LEAST ka. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ ka \<noteq> 0) 
      = (LEAST ka. A $ i $ ka \<noteq> 0)"
    proof (rule Least_equality)
      show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ (LEAST ka. A $ i $ ka \<noteq> 0) \<noteq> 0" 
        using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref False _ suc_greatest_not_zero least_le_k] using greatest_less_ma A_ma_k_not_zero 
        using rref_upt_condition2[OF rref] False by fastforce
      fix y assume Gauss_Jordan_y:"Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ y \<noteq> 0"
      show "(LEAST ka. A $ i $ ka \<noteq> 0) \<le> y"
      proof (cases "to_nat y < k")
        case False show ?thesis by (metis (mono_tags) False least_le_k less_trans not_le_imp_less to_nat_from_nat to_nat_le)
      next
        case True
        have "A $ i $ y \<noteq> 0"
          using Gauss_Jordan_y using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_m _ suc_greatest_not_zero True]
          using A_ma_k_not_zero greatest_less_ma by fastforce
        thus ?thesis by (rule Least_le)
      qed
    qed
    have Gauss_Jordan_eq_A: "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ j $ (LEAST n. A $ i $ n \<noteq> 0) =
      A $ j $ (LEAST n. A $ i $ n \<noteq> 0)"
      using Gauss_Jordan_in_ij_preserves_previous_elements[OF rref not_zero_m _ suc_greatest_not_zero least_le_k]
      using A_ma_k_not_zero greatest_less_ma by fastforce    
    show ?thesis unfolding Least_eq using rref_upt_condition4[OF rref] 
      using False Gauss_Jordan_eq_A i_not_j by presburger
  qed
qed


lemma condition_4:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  and not_zero_i_suc_k:  "\<not> is_zero_row_upt_k i (Suc k) B"
  and i_not_j: "i \<noteq> j"
  shows "B $ j $ (LEAST n. B $ i $ n \<noteq> 0) = 0"
proof (unfold B Gauss_Jordan_column_k_def ia Let_def fst_conv snd_conv, auto, unfold from_nat_to_nat_greatest from_nat_0)
  assume all_zero: "\<forall>m. is_zero_row_upt_k m k A"
    and all_zero_k: "\<forall>m\<ge>0. A $ m $ from_nat k = 0"
  show "A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0" using condition_4_part_1[OF _ all_zero] using all_zero_k not_zero_i_suc_k least_mod_type unfolding B ia by blast
next
  fix m
  assume all_zero: "\<forall>m. is_zero_row_upt_k m k A"
    and Amk_not_zero: "A $ m $ from_nat k \<noteq> 0"
  show "Gauss_Jordan_in_ij A 0 (from_nat k) $ j $ (LEAST n. Gauss_Jordan_in_ij A 0 (from_nat k) $ i $ n \<noteq> 0) = 0"
    using condition_4_part_2[OF _ i_not_j all_zero Amk_not_zero] using  not_zero_i_suc_k unfolding B ia .
next
  fix m assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and zero_below_greatest: "\<forall>m\<ge>(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1. A $ m $ from_nat k = 0"
  show "A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0"
    using condition_4_part_3[OF rref _ i_not_j not_zero_m zero_below_greatest] using not_zero_i_suc_k unfolding B ia .
next
  fix m
  assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and greatest_eq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) = nrows A"
  show "A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0"
    using  condition_4_part_4[OF rref _ i_not_j not_zero_m greatest_eq_card] using not_zero_i_suc_k unfolding B ia .
next
  fix m ma
  assume not_zero_m: "\<not> is_zero_row_upt_k m k A"
    and greatest_not_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
    and greatest_less_ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
    and A_ma_k_not_zero: "A $ ma $ from_nat k \<noteq> 0"
  show "Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ j $ 
    (LEAST n. Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) $ i $ n \<noteq> 0) = 0"
    using  condition_4_part_5[OF rref _ i_not_j not_zero_m greatest_not_card greatest_less_ma A_ma_k_not_zero] using not_zero_i_suc_k unfolding B ia .
qed


lemma reduced_row_echelon_form_upt_k_Gauss_Jordan_column_k:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  defines ia:"ia\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)"
  defines B:"B\<equiv>(snd (Gauss_Jordan_column_k (ia,A) k))"
  assumes rref: "reduced_row_echelon_form_upt_k A k"
  shows "reduced_row_echelon_form_upt_k B (Suc k)"
proof (rule reduced_row_echelon_form_upt_k_intro, auto)
  show "\<And>i j. is_zero_row_upt_k i (Suc k) B \<Longrightarrow> i < j \<Longrightarrow> is_zero_row_upt_k j (Suc k) B" using condition_1 assms by blast
  show "\<And>i. \<not> is_zero_row_upt_k i (Suc k) B \<Longrightarrow> B $ i $ (LEAST k. B $ i $ k \<noteq> 0) = 1" using condition_2 assms by blast
  show "\<And>i. i < i + 1 \<Longrightarrow> \<not> is_zero_row_upt_k i (Suc k) B \<Longrightarrow> \<not> is_zero_row_upt_k (i + 1) (Suc k) B \<Longrightarrow> (LEAST n. B $ i $ n \<noteq> 0) < (LEAST n. B $ (i + 1) $ n \<noteq> 0)" using condition_3 assms by blast
  show "\<And>i j. \<not> is_zero_row_upt_k i (Suc k) B \<Longrightarrow> i \<noteq> j \<Longrightarrow> B $ j $ (LEAST n. B $ i $ n \<noteq> 0) = 0" using condition_4 assms by blast
qed


lemma foldl_Gauss_condition_1:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes "\<forall>m. is_zero_row_upt_k m k A"
  and "\<forall>m\<ge>0. A $ m $ from_nat k = 0"
  shows "is_zero_row_upt_k m (Suc k) A" 
  by (rule is_zero_row_upt_k_suc, auto simp add: assms least_mod_type)


lemma foldl_Gauss_condition_2:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes k: "k < ncols A"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"
  and Amk_not_zero: "A $ m $ from_nat k \<noteq> 0"
  shows "\<exists>m. \<not> is_zero_row_upt_k m (Suc k) (Gauss_Jordan_in_ij A 0 (from_nat k))"
proof -
  have to_nat_from_nat_k_suc: "to_nat (from_nat k::'columns) < (Suc k)"  using to_nat_from_nat_id[OF k[unfolded ncols_def]] by simp
  have A0k_eq_1: "(Gauss_Jordan_in_ij A 0 (from_nat k)) $ 0 $ (from_nat k) = 1"
    by (rule Gauss_Jordan_in_ij_1, auto intro!: Amk_not_zero least_mod_type)
  have "\<not> is_zero_row_upt_k 0 (Suc k) (Gauss_Jordan_in_ij A 0 (from_nat k))"
    unfolding is_zero_row_upt_k_def
    using A0k_eq_1 to_nat_from_nat_k_suc by force
  thus ?thesis by blast
qed


lemma foldl_Gauss_condition_3:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes k: "k < ncols A"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"           
  and Amk_not_zero: "A $ m $ from_nat k \<noteq> 0"
  and "\<not> is_zero_row_upt_k ma (Suc k) (Gauss_Jordan_in_ij A 0 (from_nat k))"
  shows "to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (Gauss_Jordan_in_ij A 0 (from_nat k))) = 0"
proof (unfold to_nat_eq_0, rule Greatest_equality)
  have to_nat_from_nat_k_suc: "to_nat (from_nat k::'columns) < Suc (k)"  using to_nat_from_nat_id[OF k[unfolded ncols_def]] by simp
  have A0k_eq_1: "(Gauss_Jordan_in_ij A 0 (from_nat k)) $ 0 $ (from_nat k) = 1"
    by (rule Gauss_Jordan_in_ij_1, auto intro!: Amk_not_zero least_mod_type)
  show "\<not> is_zero_row_upt_k 0 (Suc k) (Gauss_Jordan_in_ij A 0 (from_nat k))"
    unfolding is_zero_row_upt_k_def
    using A0k_eq_1 to_nat_from_nat_k_suc by force
  fix y
  assume not_zero_y: "\<not> is_zero_row_upt_k y (Suc k) (Gauss_Jordan_in_ij A 0 (from_nat k))"
  have y_eq_0: "y=0"
  proof (rule ccontr)
    assume y_not_0: "y \<noteq> 0"
    have "is_zero_row_upt_k y (Suc k) (Gauss_Jordan_in_ij A 0 (from_nat k))" unfolding is_zero_row_upt_k_def
    proof (clarify)
      fix j::"'columns" assume j: "to_nat j < Suc k"
      show "Gauss_Jordan_in_ij A 0 (from_nat k) $ y $ j = 0"
      proof (cases "to_nat j = k")
        case True show ?thesis unfolding to_nat_from_nat[OF True]
          by (rule Gauss_Jordan_in_ij_0[OF _ y_not_0], unfold to_nat_from_nat[OF True, symmetric], auto intro!:  y_not_0 least_mod_type Amk_not_zero)
      next
        case False hence j_less_k: "to_nat j < k" by (metis j less_SucE)
        show ?thesis using Gauss_Jordan_in_ij_preserves_previous_elements'[OF all_zero j_less_k Amk_not_zero]
          using all_zero j_less_k unfolding is_zero_row_upt_k_def by presburger
      qed
    qed
    thus "False" using not_zero_y by contradiction
  qed
  thus "y\<le>0" using least_mod_type by simp
qed


lemma foldl_Gauss_condition_5:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes rref_A: "reduced_row_echelon_form_upt_k A k"
  and not_zero_a:"\<not> is_zero_row_upt_k a k A"
  and all_zero_below_greatest: "\<forall>m\<ge>(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1. A $ m $ from_nat k = 0"
  shows "(GREATEST n. \<not> is_zero_row_upt_k n k A) = (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A)"
proof -
  have "\<And>n. (is_zero_row_upt_k n (Suc k) A) = (is_zero_row_upt_k n k A)"
  proof 
    fix n assume "is_zero_row_upt_k n (Suc k) A"
    thus "is_zero_row_upt_k n k A" using is_zero_row_upt_k_le by fast
  next
    fix n assume zero_n_k: "is_zero_row_upt_k n k A"
    have "n>(GREATEST n. \<not> is_zero_row_upt_k n k A)" by (rule greatest_less_zero_row[OF rref_A zero_n_k], auto intro!: not_zero_a)
    hence n_ge_gratest: "n \<ge> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" using le_Suc by blast
    hence A_nk_zero: "A $ n $ (from_nat k) = 0" using all_zero_below_greatest by fast
    show "is_zero_row_upt_k n (Suc k) A" by (rule is_zero_row_upt_k_suc[OF zero_n_k A_nk_zero])
  qed
  thus "(GREATEST n. \<not> is_zero_row_upt_k n k A) = (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A)" by simp
qed


lemma foldl_Gauss_condition_6:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and eq_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) = nrows A"
  shows "nrows A = Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A))"
proof -
  have "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 = 0" using greatest_plus_one_eq_0[OF eq_card] .
  hence greatest_k_eq_minus_1: "(GREATEST n. \<not> is_zero_row_upt_k n k A) = -1" using a_eq_minus_1 by blast
  have "(GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A) = -1"
  proof (rule Greatest_equality)
    show "\<not> is_zero_row_upt_k (- 1) (Suc k) A" 
      using GreatestI_ex greatest_k_eq_minus_1 is_zero_row_upt_k_le not_zero_m by force
    show "\<And>y. \<not> is_zero_row_upt_k y (Suc k) A \<Longrightarrow> y \<le> -1" using Greatest_is_minus_1 by fast
  qed
  thus "nrows A = Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A))" using eq_card greatest_k_eq_minus_1 by fastforce
qed



lemma foldl_Gauss_condition_8:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes k: "k < ncols A"
  and not_zero_m: " \<not> is_zero_row_upt_k m k A" 
  and A_ma_k: " A $ ma $ from_nat k \<noteq> 0" 
  and ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
  shows "\<exists>m. \<not> is_zero_row_upt_k m (Suc k) (Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k))"
proof -
  define Greatest_plus_one where "Greatest_plus_one = (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
  have to_nat_from_nat_k_suc: "to_nat (from_nat k::'columns) < (Suc k)"  using to_nat_from_nat_id[OF k[unfolded ncols_def]] by simp
  have Gauss_eq_1: "(Gauss_Jordan_in_ij A Greatest_plus_one (from_nat k)) $ Greatest_plus_one $ (from_nat k) = 1" 
    by (unfold Greatest_plus_one_def, rule Gauss_Jordan_in_ij_1, auto intro!: A_ma_k ma)
  show "\<exists>m. \<not> is_zero_row_upt_k m (Suc k) (Gauss_Jordan_in_ij A (Greatest_plus_one) (from_nat k))"
    by (rule exI[of _ "Greatest_plus_one"], unfold is_zero_row_upt_k_def, auto, rule exI[of _ "from_nat k"], simp add: Gauss_eq_1 to_nat_from_nat_k_suc)
qed

lemma foldl_Gauss_condition_9:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes k: "k < ncols A"
  and rref_A: "reduced_row_echelon_form_upt_k A k"
  assumes not_zero_m: "\<not> is_zero_row_upt_k m k A"
  and suc_greatest_not_card: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
  and greatest_less_ma: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> ma"
  and A_ma_k: "A $ ma $ from_nat k \<noteq> 0"
  shows "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) =
  to_nat(GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k)))"
proof -
  define Greatest_plus_one where "Greatest_plus_one = (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
  have to_nat_from_nat_k_suc: "to_nat (from_nat k::'columns) < (Suc k)"  using to_nat_from_nat_id[OF k[unfolded ncols_def]] by simp
  have greatest_plus_one_not_zero: "Greatest_plus_one \<noteq> 0"
  proof -
    have "to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) < nrows A" using to_nat_less_card unfolding nrows_def by blast
    hence "to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 < nrows A" using suc_greatest_not_card by linarith
    show ?thesis unfolding Greatest_plus_one_def by (rule suc_not_zero[OF suc_greatest_not_card[unfolded Suc_eq_plus1 nrows_def]])
  qed
  have greatest_eq: "Greatest_plus_one = (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (Gauss_Jordan_in_ij A Greatest_plus_one (from_nat k)))"
  proof (rule Greatest_equality[symmetric])
    have "(Gauss_Jordan_in_ij A Greatest_plus_one (from_nat k)) $ (Greatest_plus_one) $ (from_nat k) = 1"
      by (unfold Greatest_plus_one_def, rule Gauss_Jordan_in_ij_1, auto intro!: greatest_less_ma A_ma_k)
    thus "\<not> is_zero_row_upt_k Greatest_plus_one (Suc k) (Gauss_Jordan_in_ij A Greatest_plus_one (from_nat k))"
      using to_nat_from_nat_k_suc
      unfolding is_zero_row_upt_k_def by fastforce    
    fix y
    assume not_zero_y: "\<not> is_zero_row_upt_k y (Suc k) (Gauss_Jordan_in_ij A Greatest_plus_one (from_nat k))"
    show "y \<le> Greatest_plus_one"
    proof (cases "y<Greatest_plus_one")
      case True thus ?thesis by simp
    next
      case False hence y_ge_greatest: "y\<ge>Greatest_plus_one" by simp
      have "y=Greatest_plus_one"
      proof (rule ccontr)
        assume y_not_greatest: "y \<noteq> Greatest_plus_one" 
        have "(GREATEST n. \<not> is_zero_row_upt_k n k A) < y" using greatest_plus_one_not_zero 
          using Suc_le' less_le_trans y_ge_greatest unfolding Greatest_plus_one_def by auto
        hence zero_row_y_upt_k: "is_zero_row_upt_k y k A" using not_greater_Greatest[of "\<lambda>n. \<not> is_zero_row_upt_k n k A" y] unfolding Greatest_plus_one_def by fast
        have "is_zero_row_upt_k y (Suc k) (Gauss_Jordan_in_ij A Greatest_plus_one (from_nat k))" unfolding is_zero_row_upt_k_def
        proof (clarify)
          fix j::'columns assume j: "to_nat j < Suc k"
          show "Gauss_Jordan_in_ij A Greatest_plus_one (from_nat k) $ y $ j = 0"
          proof (cases "j=from_nat k")
            case True
            show ?thesis
            proof (unfold True, rule Gauss_Jordan_in_ij_0[OF _ y_not_greatest], rule exI[of _ ma], rule conjI)
              show "A $ ma $ from_nat k \<noteq> 0" using A_ma_k .
              show "Greatest_plus_one \<le> ma" using greatest_less_ma unfolding Greatest_plus_one_def .
            qed
          next
            case False hence j_le_suc_k: "to_nat j < Suc k" using j by simp
            have "Gauss_Jordan_in_ij A Greatest_plus_one (from_nat k) $ y $ j = A $ y $ j" unfolding Greatest_plus_one_def
            proof (rule Gauss_Jordan_in_ij_preserves_previous_elements)
              show "reduced_row_echelon_form_upt_k A k" using rref_A .
              show "\<not> is_zero_row_upt_k m k A" using not_zero_m .
              show "\<exists>n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> n" using A_ma_k greatest_less_ma by blast
              show "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<noteq> 0" using greatest_plus_one_not_zero unfolding Greatest_plus_one_def .
              show "to_nat j < k" using False from_nat_to_nat_id j_le_suc_k less_antisym by fastforce
            qed
            also have "... = 0" using zero_row_y_upt_k unfolding is_zero_row_upt_k_def
              using  False le_imp_less_or_eq from_nat_to_nat_id j_le_suc_k less_Suc_eq_le by fastforce          
            finally show "Gauss_Jordan_in_ij A Greatest_plus_one (from_nat k) $ y $ j = 0" .
          qed
        qed
        thus "False" using not_zero_y by contradiction
      qed
      thus "y \<le> Greatest_plus_one" using y_ge_greatest by blast
    qed
  qed
  show "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) =
    to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (Gauss_Jordan_in_ij A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k)))"
    unfolding greatest_eq[unfolded Greatest_plus_one_def, symmetric]
    unfolding add_to_nat_def
    unfolding to_nat_1
    using to_nat_from_nat_id to_nat_plus_one_less_card
    using greatest_plus_one_not_zero[unfolded Greatest_plus_one_def]
    by force
qed


text\<open>The following lemma is one of most important ones in the verification of the Gauss-Jordan algorithm.
The aim is to prove two statements about @{thm "Gauss_Jordan_upt_k_def"} (one about the result is on rref and another about the index).
The reason of doing that way is because both statements need them mutually to be proved.
As the proof is made using induction, two base cases and two induction steps appear.
\<close>
lemma rref_and_index_Gauss_Jordan_upt_k:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}" and k::nat
  assumes  "k < ncols A"
  shows rref_Gauss_Jordan_upt_k: "reduced_row_echelon_form_upt_k (Gauss_Jordan_upt_k A k) (Suc k)"
  and snd_Gauss_Jordan_upt_k: 
  "foldl Gauss_Jordan_column_k (0, A) [0..<Suc k] =
  (if \<forall>m. is_zero_row_upt_k m (Suc k) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])) then 0
  else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))) + 1,
  snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))"
  using assms
proof (induct k)
    \<comment> \<open>Two base cases, one for each show\<close>
    \<comment> \<open>The first one\<close>
  show "reduced_row_echelon_form_upt_k (Gauss_Jordan_upt_k A 0) (Suc 0)"
    unfolding Gauss_Jordan_upt_k_def apply auto
    using reduced_row_echelon_form_upt_k_Gauss_Jordan_column_k[OF rref_upt_0, of A] using is_zero_row_utp_0'[of A] by simp
      \<comment> \<open>The second base case\<close>
  have rw_upt: "[0..<Suc 0] = [0]" by simp
  show "foldl Gauss_Jordan_column_k (0, A) [0..<Suc 0] =
    (if \<forall>m. is_zero_row_upt_k m (Suc 0) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc 0])) then 0
    else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc 0) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc 0]))) + 1,
    snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc 0]))"
    unfolding rw_upt
    unfolding foldl.simps
    unfolding Gauss_Jordan_column_k_def Let_def from_nat_0 fst_conv snd_conv
    unfolding is_zero_row_upt_k_def
    apply (auto simp add: least_mod_type to_nat_eq_0)
    apply (metis Gauss_Jordan_in_ij_1 least_mod_type zero_neq_one)
    by (metis (lifting, mono_tags) Gauss_Jordan_in_ij_0 GreatestI_ex least_mod_type)
next
    \<comment> \<open>Now we begin with the proof of the induction step of the first show. We will make use the induction hypothesis of the second show\<close>
  fix k
  assume "(k < ncols A \<Longrightarrow> reduced_row_echelon_form_upt_k (Gauss_Jordan_upt_k A k) (Suc k))"
    and "(k < ncols A \<Longrightarrow>
    foldl Gauss_Jordan_column_k (0, A) [0..<Suc k] =
    (if \<forall>m. is_zero_row_upt_k m (Suc k) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])) then 0
    else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))) + 1,
    snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])))"
    and k: "Suc k < ncols A" 
  hence hyp_rref: "reduced_row_echelon_form_upt_k (Gauss_Jordan_upt_k A k) (Suc k)"
    and hyp_foldl: "foldl Gauss_Jordan_column_k (0, A) [0..<Suc k] =
    (if \<forall>m. is_zero_row_upt_k m (Suc k) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])) then 0
    else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))) + 1,
    snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))"
    by simp+
  have rw: "[0..<Suc (Suc k)]= [0..<(Suc k)] @ [(Suc k)]" by auto
  have rw2: "(foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]) = 
    (if \<forall>m. is_zero_row_upt_k m (Suc k) (Gauss_Jordan_upt_k A k) then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (Gauss_Jordan_upt_k A k)) + 1,
    Gauss_Jordan_upt_k A k)" unfolding Gauss_Jordan_upt_k_def using hyp_foldl by fast
  show "reduced_row_echelon_form_upt_k (Gauss_Jordan_upt_k A (Suc k)) (Suc (Suc k))"
    unfolding Gauss_Jordan_upt_k_def unfolding rw unfolding foldl_append unfolding foldl.simps unfolding rw2
    by (rule reduced_row_echelon_form_upt_k_Gauss_Jordan_column_k[OF hyp_rref])
      \<comment> \<open>Making use of the same hypotheses of above proof, we begin with the proof of the induction step of the second show.\<close>
  have fst_foldl: "fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]) =
    fst (if \<forall>m. is_zero_row_upt_k m (Suc k) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])) then 0
    else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))) + 1,
    snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k]))" using hyp_foldl by simp
  show "foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)] =
    (if \<forall>m. is_zero_row_upt_k m (Suc (Suc k)) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)])) then 0
    else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)]))) + 1,
    snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)]))" 
  proof (rule prod_eqI)
    show "snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)]) =
      snd (if \<forall>m. is_zero_row_upt_k m (Suc (Suc k)) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)])) then 0
      else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)]))) + 1,
      snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)]))"
      unfolding Gauss_Jordan_upt_k_def by force
    define A' where "A' = snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])"
    have ncols_eq: "ncols A = ncols A'" unfolding A'_def ncols_def ..
    have rref_A': "reduced_row_echelon_form_upt_k A' (Suc k)"  using hyp_rref unfolding A'_def Gauss_Jordan_upt_k_def .
    show "fst (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)]) =
      fst (if \<forall>m. is_zero_row_upt_k m (Suc (Suc k)) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)])) then 0
      else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) (snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)]))) + 1,
      snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc (Suc k)]))"
      apply (simp only: rw)
      apply (simp only: foldl_append)
      apply (simp only: foldl.simps)
      apply (simp only: Gauss_Jordan_column_k_def Let_def fst_foldl)
      apply (simp only: A'_def[symmetric])
      apply auto
      apply (simp_all only: from_nat_0 from_nat_to_nat_greatest)
    proof -
      fix m assume "\<forall>m. is_zero_row_upt_k m (Suc k) A'" and "\<forall>m\<ge>0. A' $ m $ from_nat (Suc k) = 0"
      thus "is_zero_row_upt_k m (Suc (Suc k)) A'" using foldl_Gauss_condition_1 by blast
    next
      fix m
      assume "\<forall>m. is_zero_row_upt_k m (Suc k) A'"
        and "A' $ m $ from_nat (Suc k) \<noteq> 0"
      thus "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) (Gauss_Jordan_in_ij A' 0 (from_nat (Suc k)))"
        using foldl_Gauss_condition_2 k ncols_eq by simp
    next
      fix m ma
      assume "\<forall>m. is_zero_row_upt_k m (Suc k) A'"
        and "A' $ m $ from_nat (Suc k) \<noteq> 0"
        and "\<not> is_zero_row_upt_k ma (Suc (Suc k)) (Gauss_Jordan_in_ij A' 0 (from_nat (Suc k)))"
      thus "to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) (Gauss_Jordan_in_ij A' 0 (from_nat (Suc k)))) = 0"
        using foldl_Gauss_condition_3  k ncols_eq by simp
    next
      fix m assume "\<not> is_zero_row_upt_k m (Suc k) A' "
      thus "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'" and "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'" using is_zero_row_upt_k_le by blast+
    next
      fix m
      assume not_zero_m: "\<not> is_zero_row_upt_k m (Suc k) A'"
        and zero_below_greatest: "\<forall>m\<ge>(GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A') + 1. A' $ m $ from_nat (Suc k) = 0"
      show "(GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A') = (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A')"
        by (rule foldl_Gauss_condition_5[OF rref_A' not_zero_m zero_below_greatest])
    next
      fix m assume "\<not> is_zero_row_upt_k m (Suc k) A'" and "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A')) = nrows A'"
      thus "nrows A' = Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A'))"
        using foldl_Gauss_condition_6 by blast
    next
      fix m ma
      assume "\<not> is_zero_row_upt_k m (Suc k) A'"
        and "(GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A') + 1 \<le> ma"
        and "A' $ ma $ from_nat (Suc k) \<noteq> 0"
      thus "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) (Gauss_Jordan_in_ij A' ((GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A') + 1) (from_nat (Suc k)))"
        using foldl_Gauss_condition_8 using k ncols_eq by simp
    next
      fix m ma mb
      assume "\<not> is_zero_row_upt_k m (Suc k) A'" and
        "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A')) \<noteq> nrows A'"
        and "(GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A') + 1 \<le> ma"
        and "A' $ ma $ from_nat (Suc k) \<noteq> 0"
        and "\<not> is_zero_row_upt_k mb (Suc (Suc k)) (Gauss_Jordan_in_ij A' ((GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A') + 1) (from_nat (Suc k)))"
      thus "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A')) =
        to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) (Gauss_Jordan_in_ij A' ((GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A') + 1) (from_nat (Suc k))))"
        using foldl_Gauss_condition_9[OF k[unfolded ncols_eq] rref_A'] unfolding nrows_def by blast
    qed
  qed
qed


corollary rref_Gauss_Jordan:
  fixes A::"'a::{field}^'columns::{mod_type}^'rows::{mod_type}"
  shows "reduced_row_echelon_form (Gauss_Jordan A)"
proof -
  have "CARD('columns) - 1 < CARD('columns)" by fastforce
  thus "reduced_row_echelon_form (Gauss_Jordan A)"
    unfolding reduced_row_echelon_form_def unfolding Gauss_Jordan_def
    using rref_Gauss_Jordan_upt_k unfolding ncols_def
    by (metis (mono_tags) diff_Suc_1 lessE)
qed


lemma independent_not_zero_rows_rref:
  fixes A::"'a::{field}^'m::{mod_type}^'n::{finite,one,plus,ord}"
  assumes rref_A: "reduced_row_echelon_form A"
  shows "vec.independent {row i A |i. row i A \<noteq> 0}"
proof
  define R where "R = {row i A |i. row i A \<noteq> 0}"
  assume dep: "vec.dependent R"
  from this obtain a where a_in_R: "a\<in>R" and a_in_span: "a \<in> vec.span (R - {a})" unfolding vec.dependent_def by fast
  from a_in_R obtain i where a_eq_row_i_A: "a=row i A" unfolding R_def by blast
  hence a_eq_Ai: "a = A $ i" unfolding row_def unfolding vec_nth_inverse .
  have row_i_A_not_zero: "\<not> is_zero_row i A" using a_in_R 
  unfolding R_def is_zero_row_def is_zero_row_upt_ncols row_def vec_nth_inverse
  unfolding vec_lambda_unique zero_vec_def mem_Collect_eq using a_eq_Ai by force
  define least_n where "least_n = (LEAST n. A $ i $ n \<noteq> 0)"
  have span_rw: "vec.span (R - {a}) = range (\<lambda>u. \<Sum>v\<in>R - {a}. u v *s v)"
  proof (rule vec.span_finite)
    show "finite (R - {a})" using finite_rows[of A] unfolding rows_def R_def by simp
  qed
  from this obtain f where f: "(\<Sum>v\<in>(R - {a}). f v *s v) = a" using a_in_span
    by (metis (no_types, lifting) imageE)
  have "1 = a $ least_n"  using rref_condition2[OF rref_A] row_i_A_not_zero unfolding least_n_def a_eq_Ai by presburger
  also have"... = (\<Sum>v\<in>(R - {a}). f v *s v) $ least_n" using f by auto
  also have "... = (\<Sum>v\<in>(R - {a}). (f v *s v) $ least_n)" unfolding sum_component ..
  also have "... = (\<Sum>v\<in>(R - {a}). (f v) * (v $ least_n))" unfolding vector_smult_component ..
  also have "... = (\<Sum>v\<in>(R - {a}). 0)"
  proof (rule sum.cong)
    fix x assume x: "x \<in> R - {a}"
    from this obtain j where x_eq_row_j_A: "x=row j A" unfolding R_def by auto
    hence i_not_j: "i \<noteq> j" using a_eq_row_i_A x by auto
    have x_least_is_zero: "x $ least_n = 0" using rref_condition4[OF rref_A] i_not_j row_i_A_not_zero 
      unfolding x_eq_row_j_A least_n_def row_def vec_nth_inverse by blast
    show "f x * x $ least_n = 0" unfolding x_least_is_zero by auto
  qed rule
  also have "... = 0" unfolding sum.neutral_const ..
  finally show False by simp
qed







text\<open>Here we start to prove that the transformation from the original matrix to its reduced row echelon form has been carried out by means of elementary operations.\<close>
text\<open>The following function eliminates all entries of the j-th column using the non-zero element situated in the position (i,j).
It is introduced to make easier the proof that each Gauss-Jordan step consists in applying suitable elementary operations.\<close>

primrec row_add_iterate :: "'a::{semiring_1, uminus}^'n^'m::{mod_type} => nat => 'm => 'n => 'a^'n^'m::{mod_type}"
  where "row_add_iterate A 0 i j = (if i=0 then A else row_add A 0 i (-A $ 0 $ j))"
  | "row_add_iterate A (Suc n) i j = (if (Suc n = to_nat i) then row_add_iterate A n i j
     else row_add_iterate (row_add A (from_nat (Suc n)) i (- A $ (from_nat (Suc n)) $ j)) n i j)"

lemma invertible_row_add_iterate:
  fixes A::"'a::{ring_1}^'n^'m::{mod_type}"
  assumes n: "n<nrows A"
  shows "\<exists>P. invertible P \<and> row_add_iterate A n i j = P**A"
  using n
proof (induct n arbitrary: A)
  fix A::"'a::{ring_1}^'n^'m::{mod_type}"
  show "\<exists>P. invertible P \<and> row_add_iterate A 0 i j = P ** A"
  proof (cases "i=0")
    case True show ?thesis
      unfolding row_add_iterate.simps by (metis True invertible_def matrix_mul_lid)
  next
    case False
    show ?thesis by (metis False invertible_row_add row_add_iterate.simps(1) row_add_mat_1) 
  qed
  fix n and A::"'a::{ring_1}^'n^'m::{mod_type}"
  define A' where "A' = row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
  assume  hyp: "\<And>A::'a::{ring_1}^'n^'m::{mod_type}. n < nrows A \<Longrightarrow> \<exists>P. invertible P \<and> row_add_iterate A n i j = P ** A" and Suc_n: "Suc n < nrows A"
  hence "\<exists>P. invertible P \<and> row_add_iterate A' n i j = P ** A'" unfolding nrows_def by auto
  from this obtain P where inv_P: "invertible P"  and P: "row_add_iterate A' n i j = P ** A'" by auto
  show "\<exists>P. invertible P \<and> row_add_iterate A (Suc n) i j = P ** A" 
    unfolding row_add_iterate.simps
  proof (cases "Suc n = to_nat i")
    case True
    show "\<exists>P. invertible P \<and>
      (if Suc n = to_nat i then row_add_iterate A n i j
      else row_add_iterate (row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)) n i j) =
      P ** A"
      unfolding if_P[OF True] using hyp Suc_n by simp
  next
    case False
    show "\<exists>P. invertible P \<and>
      (if Suc n = to_nat i then row_add_iterate A n i j
      else row_add_iterate (row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)) n i j) =
      P ** A"
      unfolding if_not_P[OF False]
      unfolding P[unfolded A'_def]
    proof (rule exI[of _ "P ** (row_add (mat 1) (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j))"], rule conjI)
      show "invertible (P ** row_add (mat 1) (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j))"
        by (metis False Suc_n inv_P invertible_mult invertible_row_add to_nat_from_nat_id nrows_def)
      show "P ** row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j) =
        P ** row_add (mat 1) (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j) ** A" 
        using matrix_mul_assoc row_add_mat_1[of "from_nat (Suc n)" i " (- A $ from_nat (Suc n) $ j)"] 
        by metis
    qed
  qed
qed

lemma row_add_iterate_preserves_greater_than_n:
  fixes A::"'a::{ring_1}^'n^'m::{mod_type}"
  assumes n: "n<nrows A"
  and a: "to_nat a > n"
  shows "(row_add_iterate A n i j) $ a $ b = A $ a $ b"
  using assms
proof (induct n arbitrary: A)
  case 0
  show ?case unfolding row_add_iterate.simps
  proof (auto)
    assume "i \<noteq> 0"
    hence "a \<noteq> 0" by (metis "0.prems"(2) less_numeral_extra(3) to_nat_0)
    thus "row_add A 0 i (- A $ 0 $ j) $ a $ b = A $ a $ b" unfolding row_add_def by auto
  qed
next
  fix n and A::"'a::{ring_1}^'n^'m::{mod_type}" 
  assume hyp: "(\<And>A::'a::{ring_1}^'n^'m::{mod_type}. n < nrows A \<Longrightarrow> n < to_nat a \<Longrightarrow> row_add_iterate A n i j $ a $ b = A $ a $ b)"
    and suc_n_less_card: "Suc n < nrows A" and suc_n_kess_a: "Suc n < to_nat a" 
  hence row_add_iterate_A: "row_add_iterate A n i j $ a $ b = A $ a $ b" by auto
  show "row_add_iterate A (Suc n) i j $ a $ b = A $ a $ b"
  proof (cases "Suc n = to_nat i")
    case True
    show "row_add_iterate A (Suc n) i j $ a $ b = A $ a $ b" unfolding row_add_iterate.simps if_P[OF True] using row_add_iterate_A .
  next
    case False
    define A' where "A' = row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
    have row_add_iterate_A': "row_add_iterate A' n i j $ a $ b = A' $ a $ b" using hyp suc_n_less_card suc_n_kess_a unfolding nrows_def by auto
    have from_nat_not_a: "from_nat (Suc n) \<noteq> a" by (metis less_not_refl suc_n_kess_a suc_n_less_card to_nat_from_nat_id nrows_def)
    show "row_add_iterate A (Suc n) i j $ a $ b = A $ a $ b" unfolding row_add_iterate.simps if_not_P[OF False] row_add_iterate_A'[unfolded A'_def]
      unfolding row_add_def using from_nat_not_a by simp
  qed
qed


lemma row_add_iterate_preserves_pivot_row:
  fixes A::"'a::{ring_1}^'n^'m::{mod_type}"
  assumes n: "n<nrows A"
  and a: "to_nat i \<le> n"
  shows "(row_add_iterate A n i j) $ i $ b = A $ i $ b"
  using assms
proof (induct n arbitrary: A)
  case 0
  show ?case by (metis "0.prems"(2) le_0_eq least_mod_type row_add_iterate.simps(1) to_nat_eq to_nat_mono')
next
  fix n and A::"'a::{ring_1}^'n^'m::{mod_type}"
  assume hyp: "\<And>A::'a::{ring_1}^'n^'m::{mod_type}. n < nrows A \<Longrightarrow> to_nat i \<le> n \<Longrightarrow> row_add_iterate A n i j $ i $ b = A $ i $ b"
    and Suc_n_less_card: "Suc n < nrows A" and i_less_suc: "to_nat i \<le> Suc n"
  show "row_add_iterate A (Suc n) i j $ i $ b = A $ i $ b"
  proof (cases "Suc n = to_nat i")
    case True
    show ?thesis unfolding row_add_iterate.simps if_P[OF True] apply (rule row_add_iterate_preserves_greater_than_n) using Suc_n_less_card True lessI by linarith+
  next
    case False
    define A' where "A' = row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
    have row_add_iterate_A': "row_add_iterate A' n i j $ i $ b = A' $ i $ b" using hyp Suc_n_less_card i_less_suc False unfolding nrows_def by auto
    have from_nat_noteq_i: "from_nat (Suc n) \<noteq> i"  using False Suc_n_less_card from_nat_not_eq unfolding nrows_def by blast
    show ?thesis unfolding row_add_iterate.simps if_not_P[OF False] row_add_iterate_A'[unfolded A'_def]
      unfolding row_add_def using from_nat_noteq_i by simp
  qed
qed

lemma row_add_iterate_eq_row_add:
  fixes A::"'a::{ring_1}^'n^'m::{mod_type}"
  assumes a_not_i: "a \<noteq> i"
  and n: "n<nrows A"
  and "to_nat a \<le> n"
  shows "(row_add_iterate A n i j) $ a $ b = (row_add A a i (- A $ a $ j)) $ a $ b" 
  using assms
proof (induct n arbitrary: A)
  case 0
  show ?case unfolding row_add_iterate.simps using "0.prems"(3) a_not_i to_nat_eq_0 least_mod_type by force
next
  fix n and A::"'a::{ring_1}^'n^'m::{mod_type}"
  assume hyp: "(\<And>A::'a::{ring_1}^'n^'m::{mod_type}. a \<noteq> i \<Longrightarrow> n < nrows A  \<Longrightarrow> to_nat a \<le> n 
    \<Longrightarrow> row_add_iterate A n i j $ a $ b = row_add A a i (- A $ a $ j) $ a $ b)"
    and a_not_i: "a \<noteq> i"
    and suc_n_less_card: "Suc n < nrows A"
    and a_le_suc_n: "to_nat a \<le> Suc n"
  show "row_add_iterate A (Suc n) i j $ a $ b = row_add A a i (- A $ a $ j) $ a $ b"
  proof (cases "Suc n = to_nat i")
    case True
    show "row_add_iterate A (Suc n) i j $ a $ b = row_add A a i (- A $ a $ j) $ a $ b" unfolding row_add_iterate.simps if_P[OF True]
    apply (rule hyp[OF a_not_i], auto simp add: Suc_lessD suc_n_less_card) by (metis True a_le_suc_n a_not_i le_SucE to_nat_eq)
  next
    case False note Suc_n_not_i=False
    show ?thesis unfolding row_add_iterate.simps if_not_P[OF False]
    proof (cases "to_nat a = Suc n") case True
      show "row_add_iterate (row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)) n i j $ a $ b = row_add A a i (- A $ a $ j) $ a $ b"
        by (metis Suc_le_lessD True order_refl less_imp_le row_add_iterate_preserves_greater_than_n suc_n_less_card to_nat_from_nat nrows_def)
    next
      case False
      define A' where "A' = row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j)"
      have rw: "row_add_iterate A' n i j $ a $ b = row_add A' a i (- A' $ a $ j) $ a $ b"
      proof (rule hyp)
        show "a \<noteq> i" using a_not_i .
        show "n < nrows A'" using suc_n_less_card unfolding nrows_def by auto
        show "to_nat a \<le> n" using False a_le_suc_n by simp
      qed
      have rw1: "row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j) $ a $ b = A $ a $ b"
        unfolding row_add_def using False suc_n_less_card unfolding nrows_def by (auto simp add: to_nat_from_nat_id)
      have rw2: "row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j) $ a $ j = A $ a $ j"
        unfolding row_add_def using False suc_n_less_card unfolding nrows_def by (auto simp add: to_nat_from_nat_id)
      have rw3: "row_add A (from_nat (Suc n)) i (- A $ from_nat (Suc n) $ j) $ i $ b = A $ i $ b"
        unfolding row_add_def using Suc_n_not_i suc_n_less_card unfolding nrows_def by (auto simp add: to_nat_from_nat_id)
      show  "row_add_iterate A' n i j $ a $ b = row_add A a i (- A $ a $ j) $ a $ b"
        unfolding rw row_add_def apply simp
        unfolding A'_def rw1 rw2 rw3 ..
    qed
  qed
qed


lemma row_add_iterate_eq_Gauss_Jordan_in_ij:
  fixes A::"'a::{field}^'n^'m::{mod_type}" and i::"'m" and j::"'n"
  defines A': "A'== mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) $ i $ j)"
  shows "row_add_iterate A' (nrows A - 1) i j = Gauss_Jordan_in_ij A i j"
proof (unfold Gauss_Jordan_in_ij_def Let_def, vector, auto)
  fix ia
  have interchange_rw: "A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j = interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j"
   using interchange_rows_j[symmetric, of A "(LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)"] by auto
  show "row_add_iterate A' (nrows A - Suc 0) i j $ i $ ia = 
    mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j) $ i $ ia"
    unfolding interchange_rw unfolding A'
    proof (rule row_add_iterate_preserves_pivot_row, unfold nrows_def)
    show "CARD('m) - Suc 0 < CARD('m)" by simp
    have "to_nat i < CARD('m)" using bij_to_nat[where ?'a='m] unfolding bij_betw_def by auto
    thus "to_nat i \<le> CARD('m) - Suc 0" by auto
  qed
next
  fix ia iaa
  have interchange_rw: "A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j = interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j"
   using interchange_rows_j[symmetric, of A "(LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)"] by auto
  assume ia_not_i: "ia \<noteq> i"
  have rw: "(- interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ ia $ j) 
    = - mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ i $ j) $ ia $ j"
    unfolding interchange_rows_def mult_row_def using ia_not_i by auto  
  show "row_add_iterate A' (nrows A - Suc 0) i j $ ia $ iaa =
             row_add (mult_row (interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n)) i (1 / A $ (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ j)) ia i
              (- interchange_rows A i (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n) $ ia $ j) $
             ia $
             iaa"
    unfolding interchange_rw A' rw
  proof (rule row_add_iterate_eq_row_add[of ia i "(nrows A - Suc 0)" _ j iaa], unfold nrows_def)
    show "ia \<noteq> i" using ia_not_i .
    show "CARD('m) - Suc 0 < CARD('m)" by simp
    have "to_nat ia < CARD('m)" using bij_to_nat[where ?'a='m] unfolding bij_betw_def by auto
    thus "to_nat ia \<le> CARD('m) - Suc 0" by simp
  qed
qed



lemma invertible_Gauss_Jordan_column_k:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}" and k::nat
  shows "\<exists>P. invertible P \<and> (snd (Gauss_Jordan_column_k (i,A) k)) = P**A"
  unfolding Gauss_Jordan_column_k_def Let_def
proof (auto)
  show "\<exists>P. invertible P \<and> A = P ** A" and "\<exists>P. invertible P \<and> A = P ** A" using invertible_mat_1 matrix_mul_lid[of A] by auto
next
  fix m
  assume i: "i \<noteq> nrows A"
    and i_le_m: "from_nat i \<le> m" and Amk_not_zero: "A $ m $ from_nat k \<noteq> 0"
  define A_interchange where "A_interchange = interchange_rows A (from_nat i) (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (from_nat i) \<le> n)"
  define A_mult where "A_mult = mult_row A_interchange (from_nat i) (1 / (A_interchange $ (from_nat i) $ from_nat k))"
  obtain P where inv_P: "invertible P" and PA: "A_interchange = P**A" 
    unfolding A_interchange_def
    using interchange_rows_mat_1[of "from_nat i" "(LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n)" A]
    using invertible_interchange_rows[of "from_nat i" "(LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n)"]
    by fastforce
  define Q :: "'a^'m::{mod_type}^'m::{mod_type}"
    where "Q = mult_row (mat 1) (from_nat i) (1 / (A_interchange $ (from_nat i) $ from_nat k))"
  have Q_A_interchange: "A_mult = Q**A_interchange" unfolding A_mult_def A_interchange_def Q_def unfolding mult_row_mat_1 ..
  have inv_Q: "invertible Q"
  proof (unfold Q_def, rule invertible_mult_row', unfold A_interchange_def, rule LeastI2_ex)
    show "\<exists>a. A $ a $ from_nat k \<noteq> 0 \<and> (from_nat i) \<le> a" using i_le_m Amk_not_zero by blast
    show "\<And>x. A $ x $ from_nat k \<noteq> 0 \<and> (from_nat i) \<le> x \<Longrightarrow> 1 / interchange_rows A (from_nat i) x $ (from_nat i) $ from_nat k \<noteq> 0"
      using interchange_rows_i mult_zero_left nonzero_divide_eq_eq zero_neq_one by fastforce
  qed
  obtain Pa where inv_Pa: "invertible Pa" and Pa: "row_add_iterate (Q ** (P ** A)) (nrows A - 1) (from_nat i) (from_nat k) = Pa ** (Q ** (P ** A))"
    using invertible_row_add_iterate by (metis (full_types) diff_less nrows_def zero_less_card_finite zero_less_one)
  show "\<exists>P. invertible P \<and> Gauss_Jordan_in_ij A (from_nat i) (from_nat k) = P ** A"
  proof (rule exI[of _ "Pa**Q**P"], rule conjI)
    show "invertible (Pa ** Q ** P)" using inv_P inv_Pa inv_Q invertible_mult by auto
    have "Gauss_Jordan_in_ij A (from_nat i) (from_nat k) = row_add_iterate A_mult (nrows A - 1) (from_nat i) (from_nat k)"
      unfolding row_add_iterate_eq_Gauss_Jordan_in_ij[symmetric]  A_mult_def A_interchange_def ..
    also have "... = Pa ** (Q ** (P ** A))" using Pa unfolding PA[symmetric] Q_A_interchange[symmetric] .
    also have "... = Pa ** Q ** P ** A" unfolding matrix_mul_assoc ..
    finally show "Gauss_Jordan_in_ij A (from_nat i) (from_nat k) = Pa ** Q ** P ** A" .
  qed
qed


lemma invertible_Gauss_Jordan_up_to_k:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "\<exists>P. invertible P \<and> (Gauss_Jordan_upt_k A k) = P**A"
proof (induct k)
  case 0
  have rw: "[0..<Suc 0] = [0]" by fastforce
  show ?case
    unfolding Gauss_Jordan_upt_k_def rw foldl.simps
    using invertible_Gauss_Jordan_column_k .
  case (Suc k)
  have rw2: "[0..<Suc (Suc k)] = [0..< Suc k] @ [(Suc k)]" by simp
  obtain P' where inv_P': "invertible P'" and Gk_eq_P'A: "Gauss_Jordan_upt_k A k = P' ** A" using Suc.hyps by force
  have g: "Gauss_Jordan_upt_k A k = snd (foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])" unfolding Gauss_Jordan_upt_k_def by auto
  show ?case unfolding Gauss_Jordan_upt_k_def unfolding rw2 foldl_append foldl.simps
    apply (subst prod.collapse[symmetric, of "(foldl Gauss_Jordan_column_k (0, A) [0..<Suc k])", unfolded g[symmetric]]) 
    using invertible_Gauss_Jordan_column_k
    using Suc.hyps using invertible_mult matrix_mul_assoc by metis
qed


lemma inj_index_independent_rows:
  fixes A::"'a::{field}^'m::{mod_type}^'n::{finite,one,plus,ord}"
  assumes rref_A: "reduced_row_echelon_form A"
  and x: "row x A \<in> {row i A |i. row i A \<noteq> 0}"
  and eq: "A $ x = A $ y"
  shows "x = y"
proof (rule ccontr)
  assume x_not_y: "x \<noteq> y"  
  have not_zero_x: "\<not> is_zero_row x A" 
    using x unfolding is_zero_row_def unfolding is_zero_row_upt_k_def unfolding row_def vec_eq_iff 
    ncols_def
    by auto
  hence not_zero_y: "\<not> is_zero_row y A" using eq unfolding is_zero_row_def' by simp
  have Ax: "A $ x $ (LEAST k. A $ x $ k \<noteq> 0) = 1" using not_zero_x rref_condition2[OF rref_A] by simp
  have Ay: "A $ x $ (LEAST k. A $ y $ k \<noteq> 0) = 0" using not_zero_y x_not_y rref_condition4[OF rref_A] by fast
  show False using Ax Ay unfolding eq by simp
qed

text\<open>The final results:\<close>

lemma invertible_Gauss_Jordan:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "\<exists>P. invertible P \<and> (Gauss_Jordan A) = P**A" unfolding Gauss_Jordan_def using invertible_Gauss_Jordan_up_to_k .
  
lemma Gauss_Jordan:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "\<exists>P. invertible P \<and> (Gauss_Jordan A) = P**A \<and> reduced_row_echelon_form (Gauss_Jordan A)"
  by (simp add: invertible_Gauss_Jordan rref_Gauss_Jordan)
  
text\<open>Some properties about the rank of a matrix, obtained thanks to the Gauss-Jordan algorithm and
  the reduced row echelon form.\<close>  

lemma rref_rank:
  fixes A::"'a::{field}^'m::{mod_type}^'n::{finite,one,plus,ord}"
  assumes rref_A: "reduced_row_echelon_form A"
  shows "rank A = card {row i A |i. row i A \<noteq> 0}"
  unfolding rank_def row_rank_def
proof (rule vec.dim_unique[of "{row i A | i. row i A \<noteq> 0}"])
  show "{row i A |i. row i A \<noteq> 0} \<subseteq> row_space A"
  proof (auto, unfold row_space_def rows_def)
    fix i assume "row i A \<noteq> 0" show "row i A \<in> vec.span {row i A |i. i \<in> UNIV}"
      by (rule vec.span_base, auto)
  qed
  show "row_space A \<subseteq> vec.span {row i A |i. row i A \<noteq> 0}"
  proof (unfold row_space_def rows_def, cases "\<exists>i. row i A = 0")
    case True
    have set_rw: "{row i A |i. i \<in> UNIV} = insert 0 {row i A |i. row i A \<noteq> 0}" using True by auto
    have "vec.span {row i A |i. i \<in> UNIV} = vec.span {row i A |i. row i A \<noteq> 0}" unfolding set_rw using vec.span_insert_0 .
    thus "vec.span {row i A |i. i \<in> UNIV} \<subseteq> vec.span {row i A |i. row i A \<noteq> 0}" by simp
  next
    case False show "vec.span {row i A |i. i \<in> UNIV} \<subseteq> vec.span {row i A |i. row i A \<noteq> 0}" using False by simp
  qed
  show "vec.independent {row i A |i. row i A \<noteq> 0}" by (rule independent_not_zero_rows_rref[OF rref_A])
  show "card {row i A |i. row i A \<noteq> 0} = card {row i A |i. row i A \<noteq> 0}" ..
qed

lemma column_leading_coefficient_component_eq:
  fixes A::"'a::{field}^'m::{mod_type}^'n::{finite,one,plus,ord}"
  assumes rref_A: "reduced_row_echelon_form A"
  and v: "v \<in> {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}" 
  and vx: "v $ x \<noteq> 0"
  and vy: "v $ y \<noteq> 0"
  shows "x = y"
proof -
obtain b where b: "v = column (LEAST n. A $ b $ n \<noteq> 0) A" and row_b: "row b A \<noteq> 0" using v by blast
have vb_not_zero: "v $ b \<noteq> 0" unfolding b column_def by (auto, metis is_zero_row_eq_row_zero row_b rref_A rref_condition2 zero_neq_one)
have b_eq_x: "b = x"
 proof (rule ccontr)
  assume b_not_x: "b\<noteq>x"
  have "A $ x $ (LEAST n. A $ b $ n \<noteq> 0) = 0" 
    by (rule rref_condition4_explicit[OF rref_A _ b_not_x], simp add: is_zero_row_eq_row_zero row_b)
  thus False using vx unfolding b column_def by auto
 qed
moreover have b_eq_y: "b = y"
 proof (rule ccontr)
  assume b_not_y: "b\<noteq>y"
  have "A $ y $ (LEAST n. A $ b $ n \<noteq> 0) = 0" 
    by (rule rref_condition4_explicit[OF rref_A _ b_not_y], simp add: is_zero_row_eq_row_zero row_b)
  thus False using vy unfolding b column_def by auto
 qed
ultimately show ?thesis by simp
qed


lemma column_leading_coefficient_component_1:
  fixes A::"'a::{field}^'m::{mod_type}^'n::{finite,one,plus,ord}"
  assumes rref_A: "reduced_row_echelon_form A"
  and v: "v \<in> {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}" 
  and vx: "v $ x \<noteq> 0"
  shows "v $ x = 1"
proof -
obtain b where b: "v = column (LEAST n. A $ b $ n \<noteq> 0) A" and row_b: "row b A \<noteq> 0" using v by blast
have vb_not_zero: "v $ b \<noteq> 0" unfolding b column_def by (auto, metis is_zero_row_eq_row_zero row_b rref_A rref_condition2 zero_neq_one)
have b_eq_x: "b = x" 
  by (metis b column_def is_zero_row_eq_row_zero row_b rref_A rref_condition4 transpose_row_code transpose_row_def vx)
show?thesis
 using rref_condition2_explicit[OF rref_A, of b] row_b
 unfolding b column_def is_zero_row_def' 
 by (metis (mono_tags) \<open>\<not> is_zero_row b A \<Longrightarrow> A $ b $ (LEAST k. A $ b $ k \<noteq> 0) = 1\<close>
          b_eq_x is_zero_row_eq_row_zero vec_lambda_beta) 
qed


lemma column_leading_coefficient_component_0:
  fixes A::"'a::{field}^'m::{mod_type}^'n::{finite,one,plus,ord}"
  assumes rref_A: "reduced_row_echelon_form A"
  and v: "v \<in> {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}" 
  and vx: "v $ x \<noteq> 0"
  and x_not_y: "x \<noteq> y"
  shows "v $ y = 0" using column_leading_coefficient_component_eq[OF rref_A v vx] x_not_y by auto

lemma rref_col_rank:
  fixes A::"'a::{field}^'m::{mod_type}^'n::{mod_type}"
  assumes rref_A: "reduced_row_echelon_form A"
  shows "col_rank A = card {column (LEAST n. A $ i $ n \<noteq> 0) A | i. row i A \<noteq> 0}"
proof (unfold col_rank_def, rule vec.dim_unique[of "{column (LEAST n. A $ i $ n \<noteq> 0) A | i. row i A \<noteq> 0}"])
  show "{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0} \<subseteq> col_space A" 
  by (auto simp add: col_space_def, rule vec.span_base, unfold columns_def, auto)
  show "vec.independent {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}"
    proof (rule vec.independent_if_scalars_zero, auto)
      fix f i
      let ?x = "column (LEAST n. A $ i $ n \<noteq> 0) A"
      have sum0: "(\<Sum>x\<in>{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0} - {?x}. f x * (x $ i)) = 0"
        proof (rule sum.neutral, rule ballI)
        fix x assume x: "x \<in> {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0} - {?x}"
        obtain j where x_eq: "x=column (LEAST n. A $ j $ n \<noteq> 0) A" and row_j_not_0: "row j A \<noteq> 0" 
          and j_not_i: "j\<noteq>i" using x by auto
        have "x$i=0" unfolding x_eq column_def 
          by (auto, metis is_zero_row_eq_row_zero j_not_i row_j_not_0 rref_A rref_condition4_explicit)
        thus "f x * x $ i = 0" by simp
        qed
      assume eq_0: "(\<Sum>x\<in>{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}. f x *s x) = 0"
        and i: "row i A \<noteq> 0"
      have xi_1: "(?x $ i) = 1" unfolding column_def by (auto, metis i is_zero_row_eq_row_zero rref_A rref_condition2_explicit)
      have "0 = (\<Sum>x\<in>{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}. f x *s x) $ i" 
        using eq_0 by auto
      also have "... = (\<Sum>x\<in>{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}. f x * (x $ i))"
        unfolding sum_component vector_smult_component ..
     also have "... = f ?x * (?x $ i) 
      + (\<Sum>x\<in>{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0} - {?x}. f x * (x $ i))"
      by (rule sum.remove, auto, rule exI[of _ i], simp add: i)
     also have "... = f ?x * (?x $ i)" unfolding sum0 by simp
     also have "... = f (column (LEAST n. A $ i $ n \<noteq> 0) A)" unfolding xi_1 by simp
     finally show "f (column (LEAST n. A $ i $ n \<noteq> 0) A) = 0" by simp
     qed
  show "col_space A \<subseteq> vec.span {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}"
  unfolding col_space_def 
  proof (rule vec.span_mono[of "(columns A)" 
        "vec.span {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}", unfolded vec.span_span], auto)
  fix x assume x: "x \<in> columns A"
  have f: "finite {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}" by simp
  let ?f="\<lambda>v. x $ (THE i. v $ i \<noteq> 0)"
  show "x \<in> vec.span {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}"
    unfolding vec.span_finite[OF f] image_iff bex_UNIV
  proof (rule exI[of _ ?f], subst (1) vec_eq_iff, clarify)
    fix i
    show "x $ i = (\<Sum>v\<in>{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}. x $ (THE i. v $ i \<noteq> 0) *s v) $ i"
    proof (cases "\<exists>v. v \<in> {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0} \<and> v $ i \<noteq> 0")
      case False
      have xi_0: "x $ i = 0"
      proof (rule ccontr)
        assume xi_not_0: "x $ i \<noteq> 0"
        hence row_iA_not_zero: "row i A \<noteq> 0" using x unfolding columns_def column_def row_def by (vector, metis vec_lambda_unique)
        let ?v="column (LEAST n. A $ i $ n \<noteq> 0) A"
        have "?v \<in> {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}" using row_iA_not_zero by auto
        moreover have "?v $ i = 1" unfolding column_def by (auto, metis is_zero_row_eq_row_zero row_iA_not_zero rref_A rref_condition2)
        ultimately show False using False by auto
      qed
      show ?thesis
        unfolding xi_0
      proof (unfold sum_component vector_smult_component, rule sum.neutral[symmetric], rule ballI)
        fix xa assume xa: "xa \<in> {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}"
        have "xa $ i = 0" using False xa by auto
        thus "x $ (THE i. xa $ i \<noteq> 0) * xa $ i = 0" by simp
      qed
    next
      case True
      obtain v where v: "v \<in> {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}" and vi: "v $ i \<noteq> 0"
        using True by blast
      obtain b where b: "v = column (LEAST n. A $ b $ n \<noteq> 0) A" and row_b: "row b A \<noteq> 0" using v by blast
      have vb: "v $ b \<noteq> 0" unfolding b column_def by (auto, metis is_zero_row_eq_row_zero row_b rref_A rref_condition2 zero_neq_one)
      have b_eq_i: "b = i" by (rule column_leading_coefficient_component_eq[OF rref_A v vb vi])     
      have the_vi: "(THE a. v $ a \<noteq> 0) = i"
      proof (rule the_equality, rule vi)
        fix a assume va: "v $ a \<noteq> 0" show "a=i" by (rule column_leading_coefficient_component_eq[OF rref_A v va vi])
      qed     
      have vi_1: "v $ i = 1"  by (rule column_leading_coefficient_component_1[OF rref_A v vi])
      have sum0: "(\<Sum>v\<in>{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0} - {v}. x $ (THE a. v $ a \<noteq> 0) * (v $ i)) = 0"
      proof (rule sum.neutral, rule ballI)
        fix xa assume xa: "xa \<in> {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0} - {v}"
        obtain y where y: "xa = column (LEAST n. A $ y $ n \<noteq> 0) A" and row_b: "row y A \<noteq> 0" using xa by blast
        have xa_in_V: "xa \<in> {column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}" using xa by simp
        have "xa $ i = 0"
        proof (rule column_leading_coefficient_component_0[OF rref_A xa_in_V])
          show "xa $ y \<noteq> 0" unfolding y column_def
            by (auto, metis (lifting, full_types) LeastI2_ex is_zero_row_def' is_zero_row_eq_row_zero row_b)
          have "y \<noteq> b" by (metis (mono_tags) Diff_iff b mem_Collect_eq singleton_conv2 xa y)
          thus "y \<noteq> i" unfolding b_eq_i[symmetric] .
        qed
        thus "x $ (THE a. xa $ a \<noteq> 0) * xa $ i = 0" by simp
      qed
      have "(\<Sum>v\<in>{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}. x $ (THE a. v $ a \<noteq> 0) *s v) $ i =
          (\<Sum>v\<in>{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0}. x $ (THE a. v $ a \<noteq> 0) * (v $ i))"
        unfolding sum_component vector_smult_component ..
      also have "... = x $ (THE a. v $ a \<noteq> 0) * (v $ i)
          + (\<Sum>v\<in>{column (LEAST n. A $ i $ n \<noteq> 0) A |i. row i A \<noteq> 0} - {v}. x $ (THE a. v $ a \<noteq> 0) * (v $ i))"
        by (simp add: sum.remove[OF _ v])
      also have "... = x $ (THE a. v $ a \<noteq> 0) * (v $ i)" unfolding sum0 by simp
      also have "... = x $ (THE a. v $ a \<noteq> 0)" unfolding vi_1 by simp
      also have "... = x $ i" unfolding the_vi ..
      finally show ?thesis by simp
    qed
  qed
qed
qed (simp)


lemma rref_row_rank:
  fixes A::"'a::{field}^'m::{mod_type}^'n::{finite,one,plus,ord}"
  assumes rref_A: "reduced_row_echelon_form A"
  shows "row_rank A = card {column (LEAST n. A $ i $ n \<noteq> 0) A | i. row i A \<noteq> 0}"
  proof - 
  let ?f="\<lambda>x. column ((LEAST n. x $ n \<noteq> 0)) A"
  show ?thesis
  unfolding rref_rank[OF rref_A, unfolded rank_def]
  proof (rule bij_betw_same_card[of ?f], unfold bij_betw_def, auto)
    show "inj_on (\<lambda>x. column (LEAST n. x $ n \<noteq> 0) A) {row i A |i. row i A \<noteq> 0}"
      unfolding inj_on_def
      proof (auto)
        fix i ia
        assume i: "row i A \<noteq> 0" and ia: "row ia A \<noteq> 0"
         and c_eq: "column (LEAST n. row i A $ n \<noteq> 0) A = column (LEAST n. row ia A $ n \<noteq> 0) A"
         show "row i A = row ia A"
        using c_eq unfolding column_def unfolding row_def vec_nth_inverse
        proof -
          have "transpose_row A (LEAST R. A $ ia $ R \<noteq> 0) = transpose_row A (LEAST R. A $ i $ R \<noteq> 0)"
           by (metis c_eq column_def row_def transpose_row_def vec_nth_inverse)
          hence f1: "\<And>x\<^sub>1. A $ x\<^sub>1 $ (LEAST R. A $ ia $ R \<noteq> 0) = A $ x\<^sub>1 $ (LEAST R. A $ i $ R \<noteq> 0)"
            by (metis (no_types) transpose_row_def vec_lambda_beta)
          have f2: "is_zero_row ia A = False"
            using ia is_zero_row_eq_row_zero by auto
          have f3: "\<not> is_zero_row i A"
            using i is_zero_row_eq_row_zero by auto
          have "A $ ia $ (LEAST R. A $ i $ R \<noteq> 0) = 1"
            using f1 f2 rref_A rref_condition2 by fastforce
          thus "A $ i = A $ ia"
            using f3 rref_A rref_condition4_explicit by fastforce
         qed
        qed
      next
    fix i
    assume i: "row i A \<noteq> 0"
    show "\<exists>ia. column (LEAST n. row i A $ n \<noteq> 0) A = column (LEAST n. A $ ia $ n \<noteq> 0) A \<and> row ia A \<noteq> 0"
      by (rule exI[of _ "i"], simp add: row_def vec_lambda_eta)
         (metis i is_zero_row_def' is_zero_row_eq_row_zero zero_index)
      next
      fix i
      assume i: "row i A \<noteq> 0"
      show "column (LEAST n. A $ i $ n \<noteq> 0) A \<in> (\<lambda>x. column (LEAST n. x $ n \<noteq> 0) A) ` {row i A |i. row i A \<noteq> 0}"
      unfolding column_def row_def image_def
      by (auto, metis i row_def vec_lambda_eta)
      qed
qed



lemma row_rank_eq_col_rank_rref:
  fixes A::"'a::{field}^'m::{mod_type}^'n::{mod_type}"
assumes r: "reduced_row_echelon_form A"
shows "row_rank A = col_rank A"
  unfolding rref_row_rank[OF r] rref_col_rank[OF r] ..

lemma row_rank_eq_col_rank:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "row_rank A = col_rank A"
proof -
obtain P where inv_P: "invertible P" and G_PA: "(Gauss_Jordan A) = P**A"
  and rref_G: "reduced_row_echelon_form (Gauss_Jordan A)"
  using invertible_Gauss_Jordan rref_Gauss_Jordan by blast
have "row_rank A = row_rank (Gauss_Jordan A)"
  by (metis row_space_is_preserved invertible_Gauss_Jordan row_rank_def)
moreover have "col_rank A = col_rank (Gauss_Jordan A)"
  by (metis invertible_Gauss_Jordan crk_is_preserved)
moreover have "col_rank (Gauss_Jordan A) = row_rank (Gauss_Jordan A)"
  using row_rank_eq_col_rank_rref[OF rref_G] by simp
ultimately show ?thesis by simp
qed
  

theorem rank_col_rank:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "rank A = col_rank A" unfolding rank_def row_rank_eq_col_rank ..

theorem rank_eq_dim_image:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "rank A = vec.dim (range (\<lambda>x. A *v x))"
  unfolding rank_col_rank col_rank_def col_space_eq' ..

theorem rank_eq_dim_col_space:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "rank A = vec.dim (col_space A)" using rank_col_rank unfolding col_rank_def .

lemma rank_transpose: 
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows  "rank (transpose A) = rank A"
  by (metis rank_def rank_eq_dim_col_space row_rank_def row_space_eq_col_space_transpose)

lemma rank_le_nrows:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "rank A \<le> nrows A"
  unfolding rank_eq_dim_col_space nrows_def
  by (metis top_greatest vec.dim_subset vec_dim_card) 

lemma rank_le_ncols:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "rank A \<le> ncols A"
  unfolding rank_def row_rank_def ncols_def 
  by (metis top_greatest vec.dim_subset vec_dim_card)

lemma rank_Gauss_Jordan:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "rank A = rank (Gauss_Jordan A)"
  by (metis Gauss_Jordan_def invertible_Gauss_Jordan_up_to_k 
      row_rank_eq_col_rank rank_def crk_is_preserved)

text\<open>Other interesting properties:\<close>

lemma A_0_imp_Gauss_Jordan_0:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  assumes "A=0"
  shows "Gauss_Jordan A = 0"
proof -
obtain P where PA: "Gauss_Jordan A = P ** A" using invertible_Gauss_Jordan by blast
also have "... = 0" unfolding assms by (metis eq_add_iff matrix_add_ldistrib)
finally show "Gauss_Jordan A = 0" .
qed

lemma rank_0: "rank 0 = 0"
unfolding rank_def row_rank_def row_space_def rows_def row_def
by (simp add: vec.dim_span vec.dim_zero_eq' vec_nth_inverse)


lemma rank_greater_zero:
  assumes "A \<noteq> 0"
  shows "rank A > 0"
proof (rule ccontr, simp)
  assume "rank A = 0"
  hence "row_space A = {} \<or> row_space A = {0}" unfolding rank_def row_rank_def using vec.dim_zero_eq by blast
  hence "row_space A = {0}" unfolding row_space_def using vec.span_zero by auto
  hence "rows A = {} \<or> rows A = {0}" unfolding row_space_def using vec.span_0_imp_set_empty_or_0 by auto
  hence "rows A = {0}" unfolding rows_def row_def by force
  hence "A = 0" unfolding rows_def row_def vec_nth_inverse
    by (auto, metis (mono_tags) mem_Collect_eq singleton_iff vec_lambda_unique zero_index)
  thus False using assms by contradiction
qed

lemma Gauss_Jordan_not_0:
fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
assumes "A \<noteq> 0"
shows "Gauss_Jordan A \<noteq> 0"
by (metis assms less_not_refl3 rank_0 rank_Gauss_Jordan rank_greater_zero)

lemma rank_eq_suc_to_nat_greatest:
assumes A_not_0: "A \<noteq> 0"
shows "rank A = to_nat (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A)) + 1"
proof -
have rref: "reduced_row_echelon_form_upt_k (Gauss_Jordan A) (ncols (Gauss_Jordan A))"
  using rref_Gauss_Jordan unfolding reduced_row_echelon_form_def
  by auto
have not_all_zero: "\<not> (\<forall>a. is_zero_row_upt_k a (ncols (Gauss_Jordan A)) (Gauss_Jordan A))"
unfolding is_zero_row_def[symmetric] using Gauss_Jordan_not_0[OF A_not_0] unfolding is_zero_row_def' by (metis vec_eq_iff zero_index)
have "rank A = card {row i (Gauss_Jordan A) |i. row i (Gauss_Jordan A) \<noteq> 0}"
unfolding rank_Gauss_Jordan[of A] unfolding rref_rank[OF rref_Gauss_Jordan] ..
also have "... = card {i. i\<le>(GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))}"
  proof (rule bij_betw_same_card[symmetric, of "\<lambda>i. row i (Gauss_Jordan A)"], unfold bij_betw_def, rule conjI)
    show "inj_on (\<lambda>i. row i (Gauss_Jordan A)) {i. i \<le> (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))}"
        proof (unfold inj_on_def, auto, rule ccontr)
         fix x y
         assume x: "x \<le> (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))" and y: "y \<le> (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))"
         and xy_eq_row: "row x (Gauss_Jordan A) = row y (Gauss_Jordan A)" and x_not_y: "x \<noteq> y"
         show False
          proof (cases "x<y")
            case True
              have "(LEAST n. (Gauss_Jordan A) $ x $ n \<noteq> 0) < (LEAST n. (Gauss_Jordan A) $ y $ n \<noteq> 0)"
                proof (rule rref_condition3_equiv[OF rref_Gauss_Jordan True])
                  show "\<not> is_zero_row x (Gauss_Jordan A)"
                  by (unfold is_zero_row_def, 
                    rule greatest_ge_nonzero_row'[OF rref x[unfolded is_zero_row_def] not_all_zero])
                  show "\<not> is_zero_row y (Gauss_Jordan A)" by (unfold is_zero_row_def, rule greatest_ge_nonzero_row'[OF rref y[unfolded is_zero_row_def] not_all_zero])
               qed
              thus ?thesis by (metis less_irrefl row_def vec_nth_inverse xy_eq_row)
            next
            case False
            hence x_ge_y: "x>y" using x_not_y by simp
            have "(LEAST n. (Gauss_Jordan A) $ y $ n \<noteq> 0) < (LEAST n. (Gauss_Jordan A) $ x $ n \<noteq> 0)"
              proof (rule rref_condition3_equiv[OF rref_Gauss_Jordan x_ge_y])
                  show "\<not> is_zero_row x (Gauss_Jordan A)"
                  by (unfold is_zero_row_def, rule greatest_ge_nonzero_row'[OF rref x[unfolded is_zero_row_def] not_all_zero])
                  show "\<not> is_zero_row y (Gauss_Jordan A)" by (unfold is_zero_row_def, rule greatest_ge_nonzero_row'[OF rref y[unfolded is_zero_row_def] not_all_zero])
               qed
            thus ?thesis by (metis less_irrefl row_def vec_nth_inverse xy_eq_row)
      qed
      qed
    show "(\<lambda>i. row i (Gauss_Jordan A)) ` {i. i \<le> (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))} = {row i (Gauss_Jordan A) |i. row i (Gauss_Jordan A) \<noteq> 0}"
    proof (unfold image_def, auto)
      fix xa
      assume  xa: "xa \<le> (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))"
      show "\<exists>i. row xa (Gauss_Jordan A) = row i (Gauss_Jordan A) \<and> row i (Gauss_Jordan A) \<noteq> 0"
          proof (rule exI[of _ xa], simp)
              have "\<not> is_zero_row xa (Gauss_Jordan A)" 
                by (unfold is_zero_row_def, rule greatest_ge_nonzero_row'[OF rref xa[unfolded is_zero_row_def] not_all_zero])                  
              thus "row xa (Gauss_Jordan A) \<noteq> 0" unfolding row_def is_zero_row_def' by (metis vec_nth_inverse zero_index)
              qed
next
  fix i
  assume  "row i (Gauss_Jordan A) \<noteq> 0"
  hence "\<not> is_zero_row i (Gauss_Jordan A)" unfolding row_def is_zero_row_def' by (metis vec_eq_iff vec_nth_inverse zero_index)
  hence "i \<le> (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))" using Greatest_ge by fast
  thus "\<exists>x\<le>GREATEST a. \<not> is_zero_row a (Gauss_Jordan A). row i (Gauss_Jordan A) = row x (Gauss_Jordan A)"
    by blast
qed
qed
also have "... = card {i. i \<le> to_nat (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))}"
proof (rule bij_betw_same_card[of "\<lambda>i. to_nat i"], unfold bij_betw_def, rule conjI)
  show "inj_on to_nat {i. i \<le> (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))}" using bij_to_nat by (metis bij_betw_imp_inj_on subset_inj_on top_greatest)
  show "to_nat ` {i. i \<le> (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))} = {i. i \<le> to_nat (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))}"    
    proof (unfold image_def, auto simp add: to_nat_mono')
    fix x
    assume x: "x \<le> to_nat (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))"
    hence "from_nat x \<le> (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))"
    by (metis (full_types) leD not_le_imp_less to_nat_le)
    moreover have "x < CARD('c)" using x bij_to_nat[where ?'a='b] unfolding bij_betw_def  by (metis less_le_trans not_le to_nat_less_card)
    ultimately show "\<exists>xa\<le>GREATEST a. \<not> is_zero_row a (Gauss_Jordan A). x = to_nat xa" using to_nat_from_nat_id by fastforce
    qed
    qed
    also have "... = to_nat (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A)) + 1" unfolding card_Collect_le_nat by simp
    finally show ?thesis .
qed


lemma rank_less_row_i_imp_i_is_zero:
assumes rank_less_i: "to_nat i \<ge> rank A"
shows "Gauss_Jordan A $ i = 0"
proof (cases "A=0")
case True thus ?thesis by (metis A_0_imp_Gauss_Jordan_0 zero_index)
next
case False
have "to_nat i \<ge> to_nat (GREATEST a. \<not> is_zero_row a (Gauss_Jordan A)) + 1" using rank_less_i unfolding rank_eq_suc_to_nat_greatest[OF False] .
hence "i>(GREATEST a. \<not> is_zero_row a (Gauss_Jordan A))"
  by (metis One_nat_def add.commute add_strict_increasing 
    add_strict_increasing2 le0 lessI neq_iff not_le to_nat_mono)
hence "is_zero_row i (Gauss_Jordan A)" using not_greater_Greatest by auto
thus ?thesis unfolding is_zero_row_def' vec_eq_iff by auto
qed

lemma rank_Gauss_Jordan_eq:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "rank A = (let A'=(Gauss_Jordan A) in card {row i A' |i. row i A' \<noteq> 0})"
  by (metis (mono_tags) rank_Gauss_Jordan rref_Gauss_Jordan rref_rank)

subsection\<open>Lemmas for code generation and rank computation\<close>

lemma [code abstract]: 
shows "vec_nth (Gauss_Jordan_in_ij A i j) = (let n = (LEAST n. A $ n $ j \<noteq> 0 \<and> i \<le> n); 
  interchange_A = (interchange_rows A i n); 
  A' = mult_row interchange_A i (1/interchange_A$i$j) in 
  (% s. if s=i then A' $ s else (row_add A' s i (-(interchange_A$s$j))) $ s))"
  unfolding Gauss_Jordan_in_ij_def Let_def by fastforce

lemma rank_Gauss_Jordan_code[code]:
  fixes A::"'a::{field}^'n::{mod_type}^'m::{mod_type}"
  shows "rank A = (if A = 0 then 0 else (let A'=(Gauss_Jordan A) in to_nat (GREATEST a. row a A' \<noteq> 0) + 1))"
  proof (cases "A = 0")
    case True show ?thesis unfolding if_P[OF True] unfolding True  rank_0 ..
    next
    case False
    show ?thesis unfolding if_not_P[OF False]
    unfolding rank_eq_suc_to_nat_greatest[OF False] Let_def is_zero_row_eq_row_zero ..
qed

lemma dim_null_space[code_unfold]:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  shows "vec.dim (null_space A) = (vec.dimension TYPE('a) TYPE('cols)) - rank (A)"
  apply (rule add_implies_diff) 
  using rank_nullity_theorem_matrices  
  unfolding rank_eq_dim_col_space[of A]
  unfolding dimension_vector ncols_def ..

lemma rank_eq_dim_col_space'[code_unfold]:
 fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
 shows "vec.dim (col_space A) = rank A" unfolding  rank_eq_dim_col_space ..

lemma dim_left_null_space[code_unfold]:
  fixes A::"'a::{field}^'cols::{mod_type}^'rows::{mod_type}"
  shows "vec.dim (left_null_space A) = (vec.dimension TYPE('a) TYPE('rows)) - rank (A)"
  unfolding left_null_space_eq_null_space_transpose
  unfolding dim_null_space unfolding rank_transpose ..

lemmas rank_col_rank[symmetric, code_unfold]
lemmas rank_def[symmetric, code_unfold]
lemmas row_rank_def[symmetric, code_unfold]
lemmas col_rank_def[symmetric, code_unfold]
lemmas DIM_cart[code_unfold]
lemmas DIM_real[code_unfold]

end

