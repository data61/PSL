(*  
    Title:      Echelon_Form.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Echelon Form\<close>

theory Echelon_Form
imports 
  Rings2
  Gauss_Jordan.Determinants2
  Cayley_Hamilton_Compatible
begin


subsection\<open>Definition of Echelon Form\<close>

text\<open>Echelon form up to column k (NOT INCLUDED).\<close>

definition 
  echelon_form_upt_k :: "'a::{bezout_ring}^'cols::{mod_type}^'rows::{finite, ord} \<Rightarrow> nat \<Rightarrow> bool" 
  where 
  "echelon_form_upt_k A k = (
    (\<forall>i. is_zero_row_upt_k i k A 
          \<longrightarrow> \<not> (\<exists>j. j>i \<and> \<not> is_zero_row_upt_k j k A)) 
    \<and>  
    (\<forall>i j. i<j \<and> \<not> (is_zero_row_upt_k i k A) \<and> \<not> (is_zero_row_upt_k j k A) 
          \<longrightarrow> ((LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0))))"
  
definition "echelon_form A = echelon_form_upt_k A (ncols A)"

text\<open>Some properties of matrices in echelon form.\<close>

lemma echelon_form_upt_k_intro:
  assumes "(\<forall>i. is_zero_row_upt_k i k A \<longrightarrow> \<not> (\<exists>j. j>i \<and> \<not> is_zero_row_upt_k j k A))"
  and "(\<forall>i j. i<j \<and> \<not> (is_zero_row_upt_k i k A) \<and> \<not> (is_zero_row_upt_k j k A) 
  \<longrightarrow> ((LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)))"
  shows "echelon_form_upt_k A k" using assms unfolding echelon_form_upt_k_def by fast

lemma echelon_form_upt_k_condition1:
  assumes "echelon_form_upt_k A k" "is_zero_row_upt_k i k A"
  shows "\<not> (\<exists>j. j>i \<and> \<not> is_zero_row_upt_k j k A)"
  using assms unfolding echelon_form_upt_k_def by auto

lemma echelon_form_upt_k_condition1':
  assumes "echelon_form_upt_k A k" "is_zero_row_upt_k i k A" and "i<j"
  shows "is_zero_row_upt_k j k A"
  using assms unfolding echelon_form_upt_k_def by auto

lemma echelon_form_upt_k_condition2:
  assumes "echelon_form_upt_k A k" "i<j"
  and  "\<not> (is_zero_row_upt_k i k A)" "\<not> (is_zero_row_upt_k j k A)"
  shows "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)"
  using assms unfolding echelon_form_upt_k_def by auto

lemma echelon_form_upt_k_if_equal:
  assumes e: "echelon_form_upt_k A k"
  and eq: "\<forall>a. \<forall>b<from_nat k. A $ a $ b = B $ a $ b"
  and k: "k < ncols A"
  shows "echelon_form_upt_k B k"
  unfolding echelon_form_upt_k_def
proof (auto)
  fix i j assume zero_iB: "is_zero_row_upt_k i k B" and ij: "i < j" 
  have zero_iA: "is_zero_row_upt_k i k A" 
  proof (unfold is_zero_row_upt_k_def, clarify)
    fix ja::'b assume ja_k: "to_nat ja < k"
    have ja_k2: "ja < from_nat k" 
      by (metis (full_types) add_to_nat_def k from_nat_mono 
        ja_k monoid_add_class.add.right_neutral ncols_def to_nat_0)
    have "A $ i $ ja = B $ i $ ja" using eq ja_k2 by auto
    also have "... = 0" using zero_iB ja_k unfolding is_zero_row_upt_k_def by simp    
    finally show "A $ i $ ja = 0" .
  qed
  hence zero_jA: "is_zero_row_upt_k j k A" by (metis e echelon_form_upt_k_condition1 ij)
  show "is_zero_row_upt_k j k B"
  proof (unfold is_zero_row_upt_k_def, clarify)
    fix ja::'b assume ja_k: "to_nat ja < k"
    have ja_k2: "ja < from_nat k" 
      by (metis (full_types) add_to_nat_def k from_nat_mono 
        ja_k monoid_add_class.add.right_neutral ncols_def to_nat_0)
    have "B $ j $ ja = A $ j $ ja" using eq ja_k2 by auto
    also have "... = 0" using zero_jA ja_k unfolding is_zero_row_upt_k_def by simp    
    finally show "B $ j $ ja = 0" .
  qed
next
  fix i j
  assume ij: "i < j"
    and not_zero_iB: "\<not> is_zero_row_upt_k i k B" 
    and not_zero_jB: "\<not> is_zero_row_upt_k j k B"
  obtain a where Bia: "B $ i $ a \<noteq> 0" and ak: "a<from_nat k" 
    using not_zero_iB k unfolding is_zero_row_upt_k_def ncols_def
    by (metis add_to_nat_def from_nat_mono monoid_add_class.add.right_neutral to_nat_0)
  have Aia: "A $ i $ a \<noteq> 0" by (metis ak Bia eq)
  obtain b where Bjb: "B $ j $ b \<noteq> 0" and bk: "b<from_nat k" 
    using not_zero_jB k unfolding is_zero_row_upt_k_def ncols_def
    by (metis add_to_nat_def from_nat_mono monoid_add_class.add.right_neutral to_nat_0)
  have Ajb: "A $ j $ b \<noteq> 0" by (metis bk Bjb eq)
  have not_zero_iA: "\<not> is_zero_row_upt_k i k A" 
    by (metis (full_types) Aia ak is_zero_row_upt_k_def to_nat_le)
  have not_zero_jA: "\<not> is_zero_row_upt_k j k A" 
    by (metis (full_types) Ajb bk is_zero_row_upt_k_def to_nat_le)
  have "(LEAST n. A $ i $ n \<noteq> 0) = (LEAST n. B $ i $ n \<noteq> 0)"
  proof (rule Least_equality)
    have "(LEAST n. B $ i $ n \<noteq> 0) \<le> a" by (rule Least_le, simp add: Bia)
    hence least_bi_less: "(LEAST n. B $ i $ n \<noteq> 0) < from_nat k" using ak by simp
    thus "A $ i $ (LEAST n. B $ i $ n \<noteq> 0) \<noteq> 0" 
      by (metis (mono_tags, lifting) LeastI  eq is_zero_row_upt_k_def not_zero_iB)
    fix y assume "A $ i $ y \<noteq> 0"
    thus "(LEAST n. B $ i $ n \<noteq> 0) \<le> y"
      by (metis (mono_tags, lifting) Least_le  dual_order.strict_trans2 eq least_bi_less linear) 
  qed
  moreover have "(LEAST n. A $ j $ n \<noteq> 0) = (LEAST n. B $ j $ n \<noteq> 0)"
  proof (rule Least_equality)
    have "(LEAST n. B $ j $ n \<noteq> 0) \<le> b" by (rule Least_le, simp add: Bjb)
    hence least_bi_less: "(LEAST n. B $ j $ n \<noteq> 0) < from_nat k" using bk by simp
    thus "A $ j $ (LEAST n. B $ j $ n \<noteq> 0) \<noteq> 0" 
      by (metis (mono_tags, lifting) LeastI eq is_zero_row_upt_k_def not_zero_jB)
    fix y assume "A $ j $ y \<noteq> 0"
    thus "(LEAST n. B $ j $ n \<noteq> 0) \<le> y"
      by (metis (mono_tags, lifting) Least_le  dual_order.strict_trans2 eq least_bi_less linear) 
  qed
  moreover have "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)" 
    by (rule echelon_form_upt_k_condition2[OF e ij not_zero_iA not_zero_jA])  
  ultimately show "(LEAST n. B $ i $ n \<noteq> 0) < (LEAST n. B $ j $ n \<noteq> 0)" by auto
qed

lemma echelon_form_upt_k_0: "echelon_form_upt_k A 0"
  unfolding echelon_form_upt_k_def is_zero_row_upt_k_def by auto

lemma echelon_form_condition1:
  assumes r: "echelon_form A"
  shows "(\<forall>i. is_zero_row i A \<longrightarrow> \<not> (\<exists>j. j>i \<and> \<not> is_zero_row j A))" 
  using r unfolding echelon_form_def 
  by (metis echelon_form_upt_k_condition1' is_zero_row_def)

lemma echelon_form_condition2:
  assumes r: "echelon_form A"
  shows "(\<forall>i. i<j \<and> \<not> (is_zero_row i A) \<and> \<not> (is_zero_row j A) 
  \<longrightarrow> ((LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)))"
  using r unfolding echelon_form_def 
  by (metis echelon_form_upt_k_condition2 is_zero_row_def)


lemma echelon_form_condition2_explicit:
  assumes rref_A: "echelon_form A"
  and i_le: "i < j"
  and "\<not> is_zero_row i A" and "\<not> is_zero_row j A"
  shows "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)"
  using echelon_form_condition2 assms by blast

lemma echelon_form_intro:
  assumes 1: "(\<forall>i. is_zero_row i A \<longrightarrow> \<not> (\<exists>j. j>i \<and> \<not> is_zero_row j A))"
  and 2: "(\<forall>i j. i<j \<and> \<not> (is_zero_row i A) \<and> \<not> (is_zero_row j A) 
  \<longrightarrow> ((LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)))"
  shows "echelon_form A"  
proof (unfold echelon_form_def, rule echelon_form_upt_k_intro, auto) 
  fix i j assume "is_zero_row_upt_k i (ncols A) A" and "i < j"
  thus "is_zero_row_upt_k j (ncols A) A"
    using 1 is_zero_row_imp_is_zero_row_upt by (metis is_zero_row_def)
next
  fix i j
  assume "i < j" and "\<not> is_zero_row_upt_k i (ncols A) A" and "\<not> is_zero_row_upt_k j (ncols A) A"
  thus "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)"
    using 2 by (metis is_zero_row_imp_is_zero_row_upt)
qed

lemma echelon_form_implies_echelon_form_upt:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes rref: "echelon_form A"
  shows "echelon_form_upt_k A k"
proof (rule echelon_form_upt_k_intro)
  show "\<forall>i. is_zero_row_upt_k i k A \<longrightarrow> \<not> (\<exists>j>i. \<not> is_zero_row_upt_k j k A)"
  proof (auto, rule ccontr)
    fix i j assume zero_i_k: "is_zero_row_upt_k i k A" and i_less_j: "i < j"
      and not_zero_j_k:"\<not> is_zero_row_upt_k j k A"
    have not_zero_j: "\<not> is_zero_row j A"
      using is_zero_row_imp_is_zero_row_upt not_zero_j_k by blast
    hence not_zero_i: "\<not> is_zero_row i A"
      using echelon_form_condition1[OF rref] i_less_j by blast
    have Least_less: "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)"
      by (rule echelon_form_condition2_explicit[OF rref i_less_j not_zero_i not_zero_j])
    moreover have "(LEAST n. A $ j $ n \<noteq> 0) < (LEAST n. A $ i $ n \<noteq> 0)"
    proof (rule LeastI2_ex)   
      show "\<exists>a. A $ i $ a \<noteq> 0"
        using not_zero_i unfolding is_zero_row_def is_zero_row_upt_k_def by fast
      fix x assume Aix_not_0: "A $ i $ x \<noteq> 0"
      have k_less_x: "k \<le> to_nat x" 
        using zero_i_k Aix_not_0 unfolding is_zero_row_upt_k_def by force
      hence k_less_ncols: "k < ncols A"
        unfolding ncols_def using to_nat_less_card[of x] by simp
      obtain s where Ajs_not_zero: "A $ j $ s \<noteq> 0" and s_less_k: "to_nat s < k"
        using not_zero_j_k unfolding is_zero_row_upt_k_def by blast
      have "(LEAST n. A $ j $ n \<noteq> 0) \<le> s" using Ajs_not_zero Least_le by fast
      also have "... = from_nat (to_nat s)" unfolding from_nat_to_nat_id ..
      also have "... < from_nat k"
        by (rule from_nat_mono[OF s_less_k k_less_ncols[unfolded ncols_def]])
      also have "... \<le> x" using k_less_x leD not_le_imp_less to_nat_le by fast
      finally show "(LEAST n. A $ j $ n \<noteq> 0) < x" .
    qed
    ultimately show False by fastforce
  qed
  show "\<forall>i j. i < j \<and> \<not> is_zero_row_upt_k i k A \<and> \<not> is_zero_row_upt_k j k A 
    \<longrightarrow> (LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)"
    using echelon_form_condition2[OF rref] is_zero_row_imp_is_zero_row_upt by blast
qed

lemma upper_triangular_upt_k_def':
  assumes "\<forall>i j. to_nat j \<le> k \<and> A $ i $ j \<noteq> 0 \<longrightarrow> j\<ge>i"
  shows "upper_triangular_upt_k A k"
  using assms 
  unfolding upper_triangular_upt_k_def
  by (metis leD linear) 


lemma echelon_form_imp_upper_triagular_upt:
  fixes A::"'a::{bezout_ring}^'n::{mod_type}^'n::{mod_type}"
  assumes "echelon_form A"
  shows "upper_triangular_upt_k A k"
proof (induct k)
  case 0
  show ?case unfolding upper_triangular_upt_k_def by simp
next
  case (Suc k)
  show ?case
    unfolding upper_triangular_upt_k_def 
  proof (clarify)
    fix i j::'n assume j_less_i: "j < i" and j_less_suc_k: "to_nat j < Suc k"
    show "A $ i $ j = 0"
    proof (cases "to_nat j < k")
      case True
      thus ?thesis 
        using Suc.hyps
        unfolding upper_triangular_upt_k_def using j_less_i True by auto
    next
      case False
      hence j_eq_k: "to_nat j = k" using j_less_suc_k by simp
      hence j_eq_k2: "from_nat k = j" by (metis from_nat_to_nat_id)
      have rref_suc: "echelon_form_upt_k A (Suc k)"
        by (metis assms echelon_form_implies_echelon_form_upt)   
      have zero_j_k: "is_zero_row_upt_k j k A" 
        unfolding is_zero_row_upt_k_def
        by (metis (hide_lams, mono_tags) Suc.hyps leD le_less_linear 
          j_eq_k to_nat_mono' upper_triangular_upt_k_def)
      hence zero_i_k: "is_zero_row_upt_k i k A" 
        by (metis (poly_guards_query) assms echelon_form_implies_echelon_form_upt 
          echelon_form_upt_k_condition1' j_less_i)
      show ?thesis
      proof (cases "A $ j $ j = 0")
        case True
        have "is_zero_row_upt_k j (Suc k) A"
          by (rule is_zero_row_upt_k_suc[OF zero_j_k], simp add: True j_eq_k2)
        hence "is_zero_row_upt_k i (Suc k) A" 
          by (metis echelon_form_upt_k_condition1' j_less_i rref_suc)
        thus ?thesis by (metis is_zero_row_upt_k_def j_eq_k lessI)
      next
        case False note Ajj_not_zero=False
        hence not_zero_j:"\<not> is_zero_row_upt_k j (Suc k) A" 
          by (metis is_zero_row_upt_k_def j_eq_k lessI)
        show ?thesis
        proof (rule ccontr)
          assume Aij_not_zero: "A $ i $ j \<noteq> 0"
          hence not_zero_i: "\<not> is_zero_row_upt_k i (Suc k) A" 
            by (metis is_zero_row_upt_k_def j_eq_k lessI)
          have Least_eq: "(LEAST n. A $ i $ n \<noteq> 0) = from_nat k"
          proof (rule Least_equality)
            show "A $ i $ from_nat k \<noteq> 0" using Aij_not_zero j_eq_k2 by simp
            show "\<And>y. A $ i $ y \<noteq> 0 \<Longrightarrow> from_nat k \<le> y" 
              by (metis (full_types) is_zero_row_upt_k_def not_le_imp_less to_nat_le zero_i_k)
          qed
          moreover have Least_eq2: "(LEAST n. A $ j $ n \<noteq> 0) = from_nat k"
          proof (rule Least_equality)
            show "A $ j $ from_nat k \<noteq> 0" using Ajj_not_zero j_eq_k2 by simp
            show "\<And>y. A $ j $ y \<noteq> 0 \<Longrightarrow> from_nat k \<le> y" 
              by (metis (full_types) is_zero_row_upt_k_def not_le_imp_less to_nat_le zero_j_k)
          qed
          ultimately show False 
            using echelon_form_upt_k_condition2[OF rref_suc j_less_i not_zero_j not_zero_i]
            by simp
        qed
      qed
    qed
  qed
qed

text\<open>A matrix in echelon form is upper triangular.\<close>
lemma echelon_form_imp_upper_triagular:
  fixes A::"'a::{bezout_ring}^'n::{mod_type}^'n::{mod_type}"
  assumes "echelon_form A"
  shows "upper_triangular A"
  using echelon_form_imp_upper_triagular_upt[OF assms] 
  by (metis upper_triangular_upt_imp_upper_triangular)


lemma echelon_form_upt_k_interchange:
  fixes A::"'a::{bezout_ring}^'c::{mod_type}^'b::{mod_type}"
  assumes e: "echelon_form_upt_k A k"
  and zero_ikA: "is_zero_row_upt_k (from_nat i) k A"
  and Amk_not_0: "A $ m $ from_nat k \<noteq> 0"
  and i_le_m: "(from_nat i)\<le>m"
  and k: "k<ncols A"
  shows "echelon_form_upt_k (interchange_rows A (from_nat i) 
  (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (from_nat i) \<le> n)) k"
proof (rule echelon_form_upt_k_if_equal[OF e _ k], auto)
  fix a and b::'c
  assume b: "b < from_nat k"
  let ?least = "(LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (from_nat i) \<le> n)"
  let ?interchange = "(interchange_rows A (from_nat i) ?least)"
  have "(from_nat i)\<le>?least" by (metis (mono_tags, lifting) Amk_not_0 LeastI_ex i_le_m)
  hence zero_leastkA: "is_zero_row_upt_k ?least k A"
    using echelon_form_upt_k_condition1[OF e zero_ikA] 
    by (metis (poly_guards_query) dual_order.strict_iff_order zero_ikA)
  show "A $ a $ b = ?interchange $ a $ b"
  proof (cases "a=from_nat i")
    case True
    hence "?interchange $ a $ b = A $ ?least $ b" unfolding interchange_rows_def by auto
    also have "... = 0" using zero_leastkA unfolding is_zero_row_upt_k_def 
      by (metis (mono_tags) b to_nat_le)
    finally have "?interchange $ a $ b = 0" .
    moreover have "A $ a $ b = 0" 
      by (metis True b is_zero_row_upt_k_def to_nat_le zero_ikA)
    ultimately show ?thesis by simp
  next
    case False note a_not_i=False
    show ?thesis
    proof (cases "a=?least")
      case True
      hence "?interchange $ a $ b = A $ (from_nat i) $ b" unfolding interchange_rows_def by auto
      also have "... = 0" using zero_ikA  unfolding is_zero_row_upt_k_def 
        by (metis (poly_guards_query) b to_nat_le)
      finally have "?interchange $ a $ b = 0" .
      moreover have "A $ a $ b = 0" by (metis True b is_zero_row_upt_k_def to_nat_le zero_leastkA)
      ultimately show ?thesis by simp
    next
      case False
      thus ?thesis using a_not_i unfolding interchange_rows_def by auto
    qed
  qed
qed


text\<open>There are similar theorems to the following ones in the Gauss-Jordan developments, but
for matrices in reduced row echelon form. It is possible to prove that reduced row echelon form 
implies echelon form. Then the theorems in the Gauss-Jordan development could be 
obtained with ease.\<close>

lemma greatest_less_zero_row:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{finite, wellorder}"
  assumes r: "echelon_form_upt_k A k"
  and zero_i: "is_zero_row_upt_k i k A"
  and not_all_zero: "\<not> (\<forall>a. is_zero_row_upt_k a k A)"
  shows "(GREATEST m. \<not> is_zero_row_upt_k m k A) < i"
proof (rule ccontr)
  assume not_less_i: "\<not> (GREATEST m. \<not> is_zero_row_upt_k m k A) < i"
  have i_less_greatest: "i < (GREATEST m. \<not> is_zero_row_upt_k m k A)"
    by (metis not_less_i neq_iff GreatestI not_all_zero zero_i)
  have "is_zero_row_upt_k (GREATEST m. \<not> is_zero_row_upt_k m k A) k A"
    using r zero_i i_less_greatest unfolding echelon_form_upt_k_def by blast
  thus False using GreatestI_ex not_all_zero by fast
qed

lemma greatest_ge_nonzero_row':
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes r: "echelon_form_upt_k A k"
  and i: "i \<le> (GREATEST m. \<not> is_zero_row_upt_k m k A)"
  and not_all_zero: "\<not> (\<forall>a. is_zero_row_upt_k a k A)"
  shows "\<not> is_zero_row_upt_k i k A"
  using greatest_less_zero_row[OF r] i not_all_zero by fastforce

lemma rref_imp_ef: 
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes rref: "reduced_row_echelon_form A"
  shows "echelon_form A"
proof (rule echelon_form_intro)
  show "\<forall>i. is_zero_row i A \<longrightarrow> \<not> (\<exists>j>i. \<not> is_zero_row j A)"
    by (simp add: rref rref_condition1)
  show "\<forall>i j. i < j \<and> \<not> is_zero_row i A \<and> \<not> is_zero_row j A 
    \<longrightarrow> (LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)"
    by (simp add: rref_condition3_equiv rref)
qed

subsection\<open>Computing the echelon form of a matrix\<close>

subsubsection\<open>Demonstration over principal ideal rings\<close>
       
text\<open>Important remark:

We want to prove that there exist the echelon form of any matrix whose elements belong to a bezout 
domain. In addition, we want to compute the echelon form, so we will need computable gcd 
and bezout operations which is possible over euclidean domains. 
Our approach consists of demonstrating the correctness over bezout domains
and executing over euclidean domains.

To do that, we have studied several options:

\begin{enumerate}
  \item We could define a gcd in bezout rings (\<open>bezout_ring_gcd\<close>) as follows:
  \<open>gcd_bezout_ring a b = (SOME d. d dvd a \<and> d dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d))\<close>

  And then define an algorithm that computes the Echelon Form using such a definition to the gcd.
  This would allow us to prove the correctness over bezout rings, but we would not be able
  to execute over euclidean rings because it is not possible to demonstrate a (code) lemma 
  stating that \<open>(gcd_bezout_ring a b) = gcd_eucl a b\<close> (the gcd is not unique over 
  bezout rings and GCD rings).
  
  \item Create a \<open>bezout_ring_norm\<close> class and define a gcd normalized over bezout rings:
  \<open>definition gcd_bezout_ring_norm a b = gcd_bezout_ring a b div normalisation_factor (gcd_bezout_ring a b)\<close>

  Then, one could demonstrate a (code) lemma stating that: \<open>(gcd_bezout_ring_norm a b) 
  = gcd_eucl a b\<close>
  This allows us to execute the gcd function, but with bezout it is not possible.

  \item The third option (and the chosen one) consists of defining the algorithm over bezout domains 
  and parametrizing the algorithm by a \<open>bezout\<close> operation which must satisfy 
  suitable properties (i.e @{term "is_bezout_ext bezout"}). Then we can prove the correctness over 
  bezout domains and we will execute over euclidean domains, since we can prove that the 
  operation  @{term "euclid_ext2"} is an executable operation which satisfies 
  @{term "is_bezout_ext euclid_ext2"}.
\end{enumerate}
\<close>

subsubsection\<open>Definition of the algorithm\<close>

context bezout_ring
begin

definition 
  bezout_matrix :: "'a^'cols^'rows \<Rightarrow> 'rows \<Rightarrow> 'rows \<Rightarrow> 'cols 
                    \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a)) \<Rightarrow> 'a^'rows^'rows"
  where 
  "bezout_matrix A a b j bezout = (\<chi> x y. 
      (let 
        (p, q, u, v, d) = bezout (A $ a $ j) (A $ b $ j) 
       in
         if x = a \<and> y = a then p else
         if x = a \<and> y = b then q else
         if x = b \<and> y = a then u else
         if x = b \<and> y = b then v else
         if x = y then 1 else 0))"

end

primrec
  bezout_iterate :: "'a::{bezout_ring}^'cols^'rows::{mod_type} 
                     \<Rightarrow> nat \<Rightarrow> 'rows::{mod_type} 
                     \<Rightarrow> 'cols \<Rightarrow> ('a \<Rightarrow>'a \<Rightarrow> ('a \<times> 'a \<times> 'a \<times> 'a \<times> 'a)) \<Rightarrow> 'a^'cols^'rows::{mod_type}"
where "bezout_iterate A 0 i j bezout = A"
    | "bezout_iterate A (Suc n) i j bezout = 
        (if (Suc n) \<le> to_nat i then A else 
              bezout_iterate (bezout_matrix A i (from_nat (Suc n)) j bezout ** A) n i j bezout)"

text\<open>If every element in column @{term "k::nat"} over index @{term "i::nat"} are equal to zero,
      the same input is returned. If every element over @{term "i::nat"} 
      is equal to zero, except the pivot, the algorithm does nothing, but pivot @{term "i::nat"}
      is increased in a unit. Finally, if there is a position @{term "n::nat"} 
      whose coefficient is different from zero, its row is interchanged with row 
      @{term "i::nat"} and the bezout coefficients are used to produce a zero in its position.\<close>


definition 
  "echelon_form_of_column_k bezout A' k = 
    (let (A, i) = A' 
     in if (\<forall>m\<ge>from_nat i. A $ m $ from_nat k = 0) \<or> (i = nrows A) then (A, i) else 
        if (\<forall>m>from_nat i. A $ m $ from_nat k = 0) then (A, i + 1) else
            let n = (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n); 
                interchange_A = interchange_rows A (from_nat i) n
           in
            (bezout_iterate (interchange_A) (nrows A - 1) (from_nat i) (from_nat k) bezout, i + 1))"

definition "echelon_form_of_upt_k A k bezout = (fst (foldl (echelon_form_of_column_k bezout) (A,0) [0..<Suc k]))"
definition "echelon_form_of A bezout = echelon_form_of_upt_k A (ncols A - 1) bezout"

subsubsection\<open>The executable definition:\<close>

context euclidean_space
begin

definition [code_unfold]: "echelon_form_of_euclidean A = echelon_form_of A euclid_ext2"

end

subsubsection\<open>Properties of the bezout matrix\<close>

lemma bezout_matrix_works1:
  assumes ib: "is_bezout_ext bezout"
  and a_not_b: "a \<noteq> b"
  shows "(bezout_matrix A a b j bezout ** A) $ a $ j = snd (snd (snd (snd (bezout (A $ a $ j) (A $ b $ j)))))"
proof (unfold matrix_matrix_mult_def bezout_matrix_def Let_def, simp)
  let ?a = "(A $ a $ j)"
  let ?b = "(A $ b $ j)"
  let ?z = "bezout (A $ a $ j) (A $ b $ j)"
  obtain p q u v d where bz: "(p, q, u, v, d) = ?z" by (cases ?z, auto)
  from ib have foo: "(\<And>a b. let (p, q, u, v, gcd_a_b) = bezout a b
           in p * a + q * b = gcd_a_b \<and>
              gcd_a_b dvd a \<and>
              gcd_a_b dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd gcd_a_b) \<and> gcd_a_b * u = - b \<and> gcd_a_b * v = a)"
           using is_bezout_ext_def [of bezout] by simp
  have foo: "p * ?a + q * ?b = d \<and> d dvd ?a \<and>
            d dvd ?b \<and> (\<forall>d'. d' dvd ?a \<and> d' dvd ?b \<longrightarrow> d' dvd d) \<and> d * u = - ?b \<and> d * v = ?a" 
            using ib using is_bezout_ext_def using bz [symmetric]
            using foo [of ?a ?b] by fastforce
  have pa_bq_d: "p * ?a + ?b * q = d" using foo by (auto simp add: mult.commute)
  define f where "f k = (if k = a then p
              else if a = a \<and> k = b then q
              else if a = b \<and> k = a then u
              else if a = b \<and> k = b then v
              else if a = k then 1 else 0) * A $ k $ j" for k
  have UNIV_rw: "UNIV = insert b (insert a (UNIV - {a} - {b}))" by auto
  have sum_rw: "sum f (insert a (UNIV - {a} - {b})) = f a + sum f (UNIV - {a} - {b})"
    by (rule sum.insert, auto)
  have sum0: "sum f (UNIV - {a} - {b}) = 0" by (rule sum.neutral, simp add: f_def)
  have "(\<Sum>k\<in>UNIV.
       (case bezout (A $ a $ j) (A $ b $ j) of
        (p, q, u, v, d) \<Rightarrow>
          if k = a then p
          else if a = a \<and> k = b then q
               else if a = b \<and> k = a then u else if a = b \<and> k = b then v else if a = k then 1 else 0) *
       A $ k $ j) = (\<Sum>k\<in>UNIV.
       (if k = a then p
          else if a = a \<and> k = b then q
               else if a = b \<and> k = a then u else if a = b \<and> k = b then v else if a = k then 1 else 0) *
       A $ k $ j)" unfolding bz [symmetric] by auto
  also have "... = sum f UNIV" unfolding f_def ..
  also have "sum f UNIV = sum f (insert b (insert a (UNIV - {a} - {b})))" using UNIV_rw by simp
  also have "... = f b + sum f (insert a (UNIV - {a} - {b}))"
    by (rule sum.insert, auto, metis a_not_b)
  also have "... = f b + f a" unfolding sum_rw sum0 by simp
  also have "... = d"
    unfolding f_def using a_not_b bz [symmetric] by (auto, metis add.commute mult.commute pa_bq_d)
  also have "... = snd (snd (snd (snd (bezout (A $ a $ j) (A $ b $ j)))))"
    using bz by (metis snd_conv)
  finally show "(\<Sum>k\<in>UNIV.
       (case bezout (A $ a $ j) (A $ b $ j) of
        (p, q, u, v, d) \<Rightarrow>
          if k = a then p
          else if a = a \<and> k = b then q
               else if a = b \<and> k = a then u else if a = b \<and> k = b then v else if a = k then 1 else 0) *
       A $ k $ j) =
    snd (snd (snd (snd (bezout (A $ a $ j) (A $ b $ j)))))" unfolding f_def by simp
qed

lemma bezout_matrix_not_zero:
  assumes ib: "is_bezout_ext bezout"
  and a_not_b: "a \<noteq> b"
  and Aaj: "A $ a $ j \<noteq> 0"
  shows "(bezout_matrix A a b j bezout ** A) $ a $ j \<noteq> 0"
proof -
  have "(bezout_matrix A a b j bezout ** A) $ a $ j = snd (snd (snd(snd (bezout (A $ a $ j) (A $ b $ j)))))"
    using bezout_matrix_works1[OF ib a_not_b] .
  also have "... = (\<lambda>a b. (case bezout a b of (_, _,_ ,_,gcd') \<Rightarrow> (gcd'))) (A $ a $ j) (A $ b $ j)"
    by (simp add: split_beta)
  also have "... \<noteq> 0" using gcd'_zero[OF is_gcd_is_bezout_ext[OF ib]] Aaj by simp
  finally show ?thesis .
qed

lemma ua_vb_0:
  fixes a::"'a::bezout_domain"
  assumes ib: "is_bezout_ext bezout" and nz: "snd (snd (snd (snd (bezout a b)))) \<noteq> 0"
  shows "fst (snd (snd (bezout a b))) * a + fst (snd (snd (snd (bezout a b)))) * b = 0"
proof-
  obtain p q u v d where bz: "(p, q, u, v, d) = bezout a b" by (cases "bezout a b", auto)
  from ib have foo: "(\<And>a b. let (p, q, u, v, gcd_a_b) = bezout a b
           in p * a + q * b = gcd_a_b \<and>
              gcd_a_b dvd a \<and>
              gcd_a_b dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd gcd_a_b) \<and> gcd_a_b * u = - b \<and> gcd_a_b * v = a)"
           using is_bezout_ext_def [of bezout] by simp
  have "p * a + q * b = d \<and> d dvd a \<and>
            d dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd d) \<and> d * u = - b \<and> d * v = a" 
            using foo [of a b] using bz by fastforce
  hence dub: "d * u = - b" and dva: "d * v = a" by (simp_all)
  hence "d * u * a + d * v * b = 0" 
    using eq_neg_iff_add_eq_0 mult.commute mult_minus_left by auto
  hence "u * a + v * b = 0"
    by (metis (no_types, lifting) dub dva minus_minus mult_minus_left 
          neg_eq_iff_add_eq_0 semiring_normalization_rules(18) semiring_normalization_rules(7))
  thus ?thesis using bz [symmetric]
  by simp 
qed

lemma bezout_matrix_works2:
  fixes A::"'a::bezout_domain^'cols^'rows"
  assumes ib: "is_bezout_ext bezout"
  and a_not_b: "a \<noteq> b"
  and not_0: "A $ a $ j \<noteq> 0 \<or> A $ b $ j \<noteq> 0"
  shows "(bezout_matrix A a b j bezout ** A) $ b $ j = 0"
proof (unfold matrix_matrix_mult_def bezout_matrix_def Let_def, auto)
  let ?a = "(A $ a $ j)"
  let ?b = "(A $ b $ j)"
  let ?z = "bezout (A $ a $ j) (A $ b $ j)"
  from ib have foo: "(\<And>a b. let (p, q, u, v, gcd_a_b) = bezout a b
           in p * a + q * b = gcd_a_b \<and>
              gcd_a_b dvd a \<and>
              gcd_a_b dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd gcd_a_b) \<and> gcd_a_b * u = - b \<and> gcd_a_b * v = a)"
           using is_bezout_ext_def [of bezout] by simp
  obtain p q u v d where bz: "(p, q, u, v, d) = ?z" by (cases ?z, auto)
  hence pib: "p * ?a + q * ?b = d \<and> d dvd ?a \<and>
            d dvd ?b \<and> (\<forall>d'. d' dvd ?a \<and> d' dvd ?b \<longrightarrow> d' dvd d) \<and> d * u = - ?b \<and> d * v = ?a" 
            using foo [of ?a ?b] by fastforce
  hence pa_bq_d: "p * ?a + ?b * q = d" by (simp add: mult.commute)
  have d_dvd_a: "d dvd ?a" using pib by auto
  have d_dvd_b: "d dvd -?b" using pib by auto
  have pa_bq_d: "p * ?a + ?b * q = d" using pa_bq_d by (simp add: mult.commute)
  define f where "f k = (if b = a \<and> k = a then p
                 else if b = a \<and> k = b then q
                      else if b = b \<and> k = a then u
                           else if b = b \<and> k = b then v else if b = k then 1 else 0) *
                A $ k $ j" for k
  have UNIV_rw: "UNIV = insert b (insert a (UNIV - {a} - {b}))" by auto
  have sum_rw: "sum f (insert a (UNIV - {a} - {b})) = f a + sum f (UNIV - {a} - {b})"
    by (rule sum.insert, auto)
  have sum0: "sum f (UNIV - {a} - {b}) = 0" by (rule sum.neutral, simp add: f_def)
  have "(\<Sum>k\<in>UNIV.
       (case bezout (A $ a $ j) (A $ b $ j) of
        (p, q, u, v, d) \<Rightarrow>
          if b = a \<and> k = a then p
          else if b = a \<and> k = b then q
               else if b = b \<and> k = a then u else if b = b \<and> k = b then v else if b = k then 1 else 0) *
       A $ k $ j) = sum f UNIV" unfolding f_def bz [symmetric] by simp
  also have "sum f UNIV = sum f (insert b (insert a (UNIV - {a} - {b})))" using UNIV_rw by simp
  also have "... = f b + sum f (insert a (UNIV - {a} - {b}))"
    by (rule sum.insert, auto, metis a_not_b)
  also have "... = f b + f a" unfolding sum_rw sum0 by simp
  also have "... = v * ?b + u * ?a" unfolding f_def using a_not_b by auto
  also have "... = u * ?a + v * ?b" by auto
  also have "... = 0"
    using ua_vb_0 [OF ib] bz
    by (metis fst_conv minus_minus minus_zero mult_eq_0_iff pib snd_conv)
  finally show "(\<Sum>k\<in>UNIV.
       (case bezout (A $ a $ j) (A $ b $ j) of
        (p, q, u, v, d) \<Rightarrow>
          if b = a \<and> k = a then p
          else if b = a \<and> k = b then q
               else if b = b \<and> k = a then u else if b = b \<and> k = b then v else if b = k then 1 else 0) *
       A $ k $ j) =
       0" .
qed

lemma bezout_matrix_preserves_previous_columns:
  assumes ib: "is_bezout_ext bezout"
  and i_not_j: "i \<noteq> j"
  and Aik: "A $ i $ k \<noteq> 0"
  and b_k: "b<k"
  and i: "is_zero_row_upt_k i (to_nat k) A" and j: "is_zero_row_upt_k j (to_nat k) A"
  shows "(bezout_matrix A i j k bezout ** A) $ a $ b = A $ a $ b"
  unfolding matrix_matrix_mult_def unfolding bezout_matrix_def Let_def 
proof (auto)
  let ?B = "bezout_matrix A i j k bezout"
  let ?i = "(A $ i $ k)"
  let ?j = "(A $ j $ k)"
  let ?z = "bezout (A $ i $ k) (A $ j $ k)"
  from ib have foo: "(\<And>a b. let (p, q, u, v, gcd_a_b) = bezout a b
           in p * a + q * b = gcd_a_b \<and>
              gcd_a_b dvd a \<and>
              gcd_a_b dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd gcd_a_b) \<and> gcd_a_b * u = - b \<and> gcd_a_b * v = a)"
           using is_bezout_ext_def [of bezout] by simp
  obtain p q u v d where bz: "(p, q, u, v, d) = ?z" by (cases ?z, auto)
  have Aib: "A $ i $ b = 0" by (metis b_k i is_zero_row_upt_k_def to_nat_mono)
  have Ajb: "A $ j $ b = 0" by (metis b_k j is_zero_row_upt_k_def to_nat_mono)
  define f where "f ka = (if a = i \<and> ka = i then p
                  else if a = i \<and> ka = j then q
                  else if a = j \<and> ka = i then u
                  else if a = j \<and> ka = j then v else if a = ka then 1 else 0) * A $ ka $ b" for ka
  show "(\<Sum>ka\<in>UNIV.
       (case bezout (A $ i $ k) (A $ j $ k) of
        (p, q, u, v, d) \<Rightarrow>
          if a = i \<and> ka = i then p
          else if a = i \<and> ka = j then q
               else if a = j \<and> ka = i then u else if a = j \<and> ka = j then v else if a = ka then 1 else 0) *
       A $ ka $ b) =
    A $ a $ b"
  proof (cases "a=i")
    case True
    have "(\<Sum>ka\<in>UNIV.
       (case bezout (A $ i $ k) (A $ j $ k) of
        (p, q, u, v, d) \<Rightarrow>
          if a = i \<and> ka = i then p
          else if a = i \<and> ka = j then q
               else if a = j \<and> ka = i then u else if a = j \<and> ka = j then v else if a = ka then 1 else 0) *
       A $ ka $ b) = sum f UNIV" unfolding f_def bz [symmetric] by simp
    also have "sum f UNIV = 0" by (rule sum.neutral, auto simp add: Aib Ajb f_def True i_not_j)
    also have "... = A $ a $ b" unfolding True using Aib by simp
    finally show ?thesis .
  next
    case False note a_not_i=False
    show ?thesis
    proof (cases "a=j")
      case True 
      have "(\<Sum>ka\<in>UNIV.
       (case bezout (A $ i $ k) (A $ j $ k) of
        (p, q, u, v, d) \<Rightarrow>
          if a = i \<and> ka = i then p
          else if a = i \<and> ka = j then q
               else if a = j \<and> ka = i then u else if a = j \<and> ka = j then v else if a = ka then 1 else 0) *
       A $ ka $ b) = sum f UNIV" unfolding f_def bz [symmetric] by simp
    also have "sum f UNIV = 0" by (rule sum.neutral, auto simp add: Aib Ajb f_def True i_not_j)
      also have "... = A $ a $ b" unfolding True using Ajb by simp
      finally show ?thesis .
    next
      case False 
      have UNIV_rw: "UNIV = insert j (insert i (UNIV - {i} - {j}))" by auto
      have UNIV_rw2: "UNIV - {i} - {j} = insert a (UNIV - {i} - {j}-{a})"
        using False a_not_i by auto
      have sum0: "sum f (UNIV - {i} - {j} - {a}) = 0"
        by (rule sum.neutral, simp add: f_def)
      have "(\<Sum>ka\<in>UNIV.
       (case bezout (A $ i $ k) (A $ j $ k) of
        (p, q, u, v, d) \<Rightarrow>
          if a = i \<and> ka = i then p
          else if a = i \<and> ka = j then q
               else if a = j \<and> ka = i then u else if a = j \<and> ka = j then v else if a = ka then 1 else 0) *
       A $ ka $ b) = sum f UNIV" unfolding f_def bz [symmetric] by simp
      also have "sum f UNIV = sum f (insert j (insert i (UNIV - {i} - {j})))"
        using UNIV_rw by simp
      also have "... = f j + sum f (insert i (UNIV - {i} - {j}))"
        by (rule sum.insert, auto, metis i_not_j)
      also have "... = sum f (insert i (UNIV - {i} - {j}))"
        unfolding f_def using False a_not_i by auto
      also have "... = f i + sum f (UNIV - {i} - {j})"  by (rule sum.insert, auto)
      also have "... = sum f (UNIV - {i} - {j})" unfolding f_def using False a_not_i by auto
      also have "... = sum f (insert a (UNIV - {i} - {j} - {a}))" using UNIV_rw2 by simp
      also have "... = f a + sum f (UNIV - {i} - {j} - {a})" by (rule sum.insert, auto)
      also have "... = f a" unfolding sum0 by simp
      also have "... = A $ a $ b" unfolding f_def using False a_not_i by auto
      finally show ?thesis .
    qed
  qed
qed

lemma det_bezout_matrix:
  fixes A::"'a::{bezout_domain}^'cols^'rows::{finite,wellorder}"
  assumes ib: "is_bezout_ext bezout"
  and a_less_b: "a < b"
  and aj: "A $ a $ j \<noteq> 0"
  shows "det (bezout_matrix A a b j bezout) = 1"
proof -
  let ?B = "bezout_matrix A a b j bezout"
  let ?a = "(A $ a $ j)"
  let ?b = "(A $ b $ j)"
  let ?z = "bezout ?a ?b"
  from ib have foo: "(\<And>a b. let (p, q, u, v, gcd_a_b) = bezout a b
           in p * a + q * b = gcd_a_b \<and>
              gcd_a_b dvd a \<and>
              gcd_a_b dvd b \<and> (\<forall>d'. d' dvd a \<and> d' dvd b \<longrightarrow> d' dvd gcd_a_b) \<and> gcd_a_b * u = - b \<and> gcd_a_b * v = a)"
           using is_bezout_ext_def [of bezout] by simp
  obtain p q u v d where bz: "(p, q, u, v, d) = ?z" by (cases ?z, auto)
  hence pib: "p * ?a + q * ?b = d \<and> d dvd ?a \<and>
            d dvd ?b \<and> (\<forall>d'. d' dvd ?a \<and> d' dvd ?b \<longrightarrow> d' dvd d) \<and> d * u = - ?b \<and> d * v = ?a" 
            using foo [of ?a ?b] by fastforce
  hence pa_bq_d: "p * ?a + ?b * q = d" by (simp add: mult.commute)
  have a_not_b: "a \<noteq> b" using a_less_b by auto
  have d_dvd_a: "d dvd ?a" using pib by auto
  have UNIV_rw: "UNIV = insert b (insert a (UNIV - {a} - {b}))" by auto
  show ?thesis
  proof (cases "p = 0")
    case True note p0=True
    have q_not_0: "q \<noteq> 0"
    proof (rule ccontr, simp)
      assume q: "q = 0"
      have "d = 0" using pib
        by (metis True q add.right_neutral mult.commute mult_zero_right)
      hence "A $ a $ j = 0 \<and> A $ b $ j = 0"
        by (metis aj d_dvd_a dvd_0_left_iff)
      thus False using aj by auto
    qed
    have d_not_0: "d \<noteq> 0"
      by (metis aj d_dvd_a dvd_0_left_iff)
    have qb_not_0: "q *(-?b) \<noteq> 0"
      by (metis d_not_0 mult_cancel_left1 neg_equal_0_iff_equal 
          no_zero_divisors p0 pa_bq_d q_not_0 right_minus)
    have "det (interchange_rows ?B a b) = (\<Prod>i\<in>UNIV. (interchange_rows ?B a b) $ i $ i)"
    proof (rule det_upperdiagonal)
      fix i ja::'rows assume ja_i: "ja<i"
      show "interchange_rows (bezout_matrix A a b j bezout) a b $ i $ ja = 0"    
        unfolding interchange_rows_def using a_less_b ja_i p0 a_not_b 
        using bz [symmetric]
        unfolding bezout_matrix_def Let_def by auto
    qed
    also have "\<dots> = -1" 
    proof -
      define f where "f i = interchange_rows (bezout_matrix A a b j bezout) a b $ i $ i" for i
      have prod_rw: "prod f (insert a (UNIV - {a} - {b})) 
        =  f a * prod f (UNIV - {a} - {b})"
        by (rule prod.insert, simp_all)
      have prod1: "prod f (UNIV - {a} - {b}) = 1"
        by (rule prod.neutral) 
            (simp add: f_def interchange_rows_def bezout_matrix_def Let_def)
      have "prod f UNIV = prod f (insert b (insert a (UNIV - {a} - {b})))" 
        using UNIV_rw by simp
      also have "... = f b * prod f (insert a (UNIV - {a} - {b}))"
      proof (rule prod.insert, simp)
        show "b \<notin> insert a (UNIV - {a} - {b})" using a_not_b by auto
      qed
      also have "... = f b * f a" unfolding prod_rw prod1 by auto
      also have "... = q * u" 
        using a_not_b 
        using bz [symmetric]
        unfolding f_def interchange_rows_def bezout_matrix_def Let_def by auto
      also have "... = -1"
      proof -
        let ?r = "q * u"
        have du_b: " d * u = -?b" using pib by auto
        hence "q * (-?b) = d * ?r" by (metis mult.left_commute)
        also have "... = (p * ?a + ?b * q) * ?r" unfolding pa_bq_d by auto
        also have "... = ?b * q * ?r" using True by auto
        also have "... = q * (-?b) * (-?r)" by auto
        finally show ?thesis using qb_not_0 
          unfolding mult_cancel_left1 by (metis minus_minus)
      qed
      finally show ?thesis unfolding f_def .
    qed
    finally have det_inter_1: "det (interchange_rows ?B a b) = - 1" .
    have "det (bezout_matrix A a b j bezout) = - 1 * det (interchange_rows ?B a b)"
      unfolding det_interchange_rows using a_not_b by auto
    thus ?thesis unfolding det_inter_1 by simp
  next
    case False
    define mult_b_dp where "mult_b_dp = mult_row ?B b (d * p)"
    define sum_ab where "sum_ab = row_add mult_b_dp b a ?b"
    have "det (sum_ab) = prod (\<lambda>i. sum_ab $ i $ i) UNIV"
    proof (rule det_upperdiagonal)
      fix i j::'rows 
      assume j_less_i: "j < i"
      have "d * p * u + ?b * p = 0"
        using pib
        by (metis eq_neg_iff_add_eq_0 mult_minus_left semiring_normalization_rules(16))
      thus "sum_ab $ i $ j = 0"
        unfolding sum_ab_def mult_b_dp_def unfolding row_add_def
        unfolding mult_row_def bezout_matrix_def
        using a_not_b j_less_i a_less_b 
        unfolding bz [symmetric] by auto
    qed
    also have "... = d * p"
    proof -
      define f where "f i = sum_ab $ i $ i" for i
      have prod_rw: "prod f (insert a (UNIV - {a} - {b})) 
        =  f a * prod f (UNIV - {a} - {b})"
        by (rule prod.insert, simp_all)
      have prod1: "prod f (UNIV - {a} - {b}) = 1"
        by (rule prod.neutral) (simp add: f_def sum_ab_def row_add_def 
          mult_b_dp_def mult_row_def bezout_matrix_def Let_def)
      have ap_bq_d: "A $ a $ j * p + A $ b $ j * q = d" by (metis mult.commute pa_bq_d)
      have "prod f UNIV = prod f (insert b (insert a (UNIV - {a} - {b})))"
        using UNIV_rw by simp
      also have "... = f b * prod f (insert a (UNIV - {a} - {b}))"
      proof (rule prod.insert, simp)
        show "b \<notin> insert a (UNIV - {a} - {b})" using a_not_b by auto
      qed
      also have "... = f b * f a" unfolding prod_rw prod1 by auto
      also have "... = (d * p * v + ?b * q) * p" 
        unfolding f_def sum_ab_def row_add_def mult_b_dp_def mult_row_def bezout_matrix_def
        unfolding bz [symmetric]
        using a_not_b by auto
      also have "... = d * p" 
        using pib ap_bq_d semiring_normalization_rules(16) by auto
      finally show ?thesis unfolding f_def .
    qed
    finally have "det (sum_ab) = d * p" .
    moreover have "det (sum_ab) = d * p * det ?B"
      unfolding sum_ab_def
      unfolding det_row_add'[OF not_sym[OF a_not_b]]
      unfolding mult_b_dp_def unfolding det_mult_row ..
    ultimately show ?thesis
      by (metis (erased, hide_lams) False aj d_dvd_a dvd_0_left_iff mult_cancel_left1 mult_eq_0_iff)
  qed
qed

lemma invertible_bezout_matrix:
  fixes A::"'a::{bezout_ring_div}^'cols^'rows::{finite,wellorder}"
  assumes ib: "is_bezout_ext bezout"
  and a_less_b: "a < b"
  and aj: "A $ a $ j \<noteq> 0"
  shows "invertible (bezout_matrix A a b j bezout)"
  unfolding invertible_iff_is_unit
  unfolding det_bezout_matrix[OF assms]
  by simp

lemma echelon_form_upt_k_bezout_matrix:
  fixes A k and i::"'b::mod_type"
  assumes e: "echelon_form_upt_k A k"
  and ib: "is_bezout_ext bezout"
  and Aik_0: "A $ i $ from_nat k \<noteq> 0"
  and zero_i: "is_zero_row_upt_k i k A" 
  and i_less_n: "i<n"
  and k: "k<ncols A"
  shows "echelon_form_upt_k (bezout_matrix A i n (from_nat k) bezout ** A) k"
proof -
  let ?B="(bezout_matrix A i n (from_nat k) bezout ** A)"
  have i_not_n: "i \<noteq> n" using i_less_n by simp
  have zero_n: "is_zero_row_upt_k n k A" 
    by (metis assms(5) e echelon_form_upt_k_condition1 zero_i)
  have zero_i2: "is_zero_row_upt_k i (to_nat (from_nat k::'c)) A" 
    using zero_i 
    by (metis k ncols_def to_nat_from_nat_id)
  have zero_n2: "is_zero_row_upt_k n (to_nat (from_nat k::'c)) A"
    using zero_n by (metis k ncols_def to_nat_from_nat_id)
  show ?thesis
    unfolding echelon_form_upt_k_def
  proof (auto)
    fix ia j
    assume ia: "is_zero_row_upt_k ia k ?B"
      and ia_j: "ia < j"
    have ia_A: "is_zero_row_upt_k ia k A"
    proof (unfold is_zero_row_upt_k_def, clarify)
      fix j::'c assume j_less_k: "to_nat j < k"
      have "A $ ia $ j = ?B $ ia $ j"
      proof (rule bezout_matrix_preserves_previous_columns
          [symmetric, OF ib i_not_n Aik_0 _ zero_i2 zero_n2])
        show "j < from_nat k" using j_less_k k 
          by (metis from_nat_mono from_nat_to_nat_id ncols_def)
      qed
      also have "... = 0" by (metis ia is_zero_row_upt_k_def j_less_k)
      finally show "A $ ia $ j = 0" .
    qed
    show "is_zero_row_upt_k j k ?B" 
    proof (unfold is_zero_row_upt_k_def, clarify)
      fix ja::'c assume ja_less_k: "to_nat ja < k" 
      have "?B $ j $ ja = A $ j $ ja"
      proof (rule bezout_matrix_preserves_previous_columns[OF ib i_not_n Aik_0 _ zero_i2 zero_n2])
        show "ja < from_nat k" using ja_less_k k 
          by (metis from_nat_mono from_nat_to_nat_id ncols_def)
      qed
      also have "... = 0" 
        by (metis e echelon_form_upt_k_condition1 ia_A ia_j is_zero_row_upt_k_def ja_less_k)
     finally show "?B $ j $ ja = 0" .
   qed
 next
   fix ia j
   assume ia_j: "ia < j"
     and not_zero_ia_B: "\<not> is_zero_row_upt_k ia k ?B"
     and not_zero_j_B: "\<not> is_zero_row_upt_k j k ?B"
   obtain na where na: "to_nat na < k" and Biana: "?B $ ia $ na \<noteq> 0" 
     using not_zero_ia_B unfolding is_zero_row_upt_k_def by auto
   obtain na2 where na2: "to_nat na2 < k" and Bjna2: "?B $ j $ na2 \<noteq> 0" 
     using not_zero_j_B unfolding is_zero_row_upt_k_def by auto
   have na_less_fn: "na < from_nat k" by (metis from_nat_mono from_nat_to_nat_id k na ncols_def)
   have "A $ ia $ na = ?B $ ia $ na"
     by (rule bezout_matrix_preserves_previous_columns
     [symmetric, OF ib i_not_n Aik_0 na_less_fn zero_i2 zero_n2])
   also have "... \<noteq> 0" using Biana by simp
   finally have A: "A $ ia $ na \<noteq> 0" .
   have na_less_fn2: "na2 < from_nat k" by (metis from_nat_mono from_nat_to_nat_id k na2 ncols_def)
   have "A $ j $ na2 = ?B $ j $ na2"
     by (rule bezout_matrix_preserves_previous_columns
     [symmetric, OF ib i_not_n Aik_0 na_less_fn2 zero_i2 zero_n2])
   also have "... \<noteq> 0" using Bjna2 by simp
   finally have A2: "A $ j $ na2 \<noteq> 0" .
   have not_zero_ia_A: "\<not> is_zero_row_upt_k ia k A"
     unfolding is_zero_row_upt_k_def using na A by auto
   have not_zero_j_A: "\<not> is_zero_row_upt_k j k A"
     unfolding is_zero_row_upt_k_def using na2 A2 by auto
   obtain na where A: "A $ ia $ na \<noteq> 0" and na_less_k: "to_nat na<k" 
     using not_zero_ia_A unfolding is_zero_row_upt_k_def by auto
   have na_less_fn: "na<from_nat k" using na_less_k
    by (metis from_nat_mono from_nat_to_nat_id k ncols_def)
   obtain na2 where A2: "A $ j $ na2 \<noteq> 0" and na2_less_k: "to_nat na2<k" 
     using not_zero_j_A unfolding is_zero_row_upt_k_def by auto
   have na_less_fn2: "na2<from_nat k" using na2_less_k
    by (metis from_nat_mono from_nat_to_nat_id k ncols_def)
   have least_eq: "(LEAST na. ?B $ ia $ na \<noteq> 0) = (LEAST na. A $ ia $ na \<noteq> 0)"
   proof (rule Least_equality)
     have "?B $ ia $ (LEAST na. A $ ia $ na \<noteq> 0) = A $ ia $ (LEAST na. A $ ia $ na \<noteq> 0)"
     proof (rule bezout_matrix_preserves_previous_columns[OF ib i_not_n Aik_0 _ zero_i2 zero_n2])
       show "(LEAST na. A $ ia $ na \<noteq> 0) < from_nat k" using Least_le A na_less_fn by fastforce
     qed
     also have "... \<noteq> 0" by (metis (mono_tags) A LeastI)
     finally show "?B $ ia $ (LEAST na. A $ ia $ na \<noteq> 0) \<noteq> 0" .
     fix y
     assume B_ia_y: "?B $ ia $ y \<noteq> 0"
     show "(LEAST na. A $ ia $ na \<noteq> 0) \<le> y"
     proof (cases "y<from_nat k")
       case True
       show ?thesis
       proof (rule Least_le)
         have "A $ ia $ y = ?B $ ia $ y"
           by (rule bezout_matrix_preserves_previous_columns[symmetric, 
             OF ib i_not_n Aik_0 True zero_i2 zero_n2])
         also have "... \<noteq> 0" using B_ia_y .
         finally show "A $ ia $ y \<noteq> 0" .
       qed
     next
       case False
       show ?thesis using False
         by (metis (mono_tags) A Least_le dual_order.strict_iff_order
            le_less_trans na_less_fn not_le)
     qed
   qed
   have least_eq2: "(LEAST na. ?B $ j $ na \<noteq> 0) = (LEAST na. A $ j $ na \<noteq> 0)"
   proof (rule Least_equality)
     have "?B $ j $ (LEAST na. A $ j $ na \<noteq> 0) = A $ j $ (LEAST na. A $ j $ na \<noteq> 0)"
     proof (rule bezout_matrix_preserves_previous_columns[OF ib i_not_n Aik_0 _ zero_i2 zero_n2])
       show "(LEAST na. A $ j $ na \<noteq> 0) < from_nat k" using Least_le A2 na_less_fn2 by fastforce
     qed
     also have "... \<noteq> 0" by (metis (mono_tags) A2 LeastI)
     finally show "?B $ j $ (LEAST na. A $ j $ na \<noteq> 0) \<noteq> 0" .
     fix y
     assume B_ia_y: "?B $ j $ y \<noteq> 0"
     show "(LEAST na. A $ j $ na \<noteq> 0) \<le> y" 
     proof (cases "y<from_nat k")
       case True
       show ?thesis
       proof (rule Least_le)
         have "A $ j $ y = ?B $ j $ y"
           by (rule bezout_matrix_preserves_previous_columns[symmetric, 
            OF ib i_not_n Aik_0 True zero_i2 zero_n2])
         also have "... \<noteq> 0" using B_ia_y .
         finally show "A $ j $ y \<noteq> 0" .
       qed
     next
       case False
       show ?thesis using False
         by (metis (mono_tags) A2 Least_le dual_order.strict_iff_order
            le_less_trans na_less_fn2 not_le)
     qed
   qed   
   show "(LEAST na. ?B $ ia $ na \<noteq> 0) < (LEAST na. ?B $ j $ na \<noteq> 0)" unfolding least_eq least_eq2
     by (rule echelon_form_upt_k_condition2[OF e ia_j not_zero_ia_A not_zero_j_A])
 qed
qed

lemma bezout_matrix_preserves_rest:
  assumes ib: "is_bezout_ext bezout"
  and a_not_n: "a\<noteq>n"
  and i_not_n: "i\<noteq>n"
  and a_not_i: "a\<noteq>i"
  and Aik_0: "A $ i $ k \<noteq> 0"
  and zero_ikA: "is_zero_row_upt_k i (to_nat k) A"
  shows "(bezout_matrix A i n k bezout ** A) $ a $ b = A $ a $ b"
  unfolding matrix_matrix_mult_def unfolding bezout_matrix_def Let_def 
proof (auto simp add: a_not_n i_not_n a_not_i)
  have UNIV_rw: "UNIV = insert a (UNIV - {a})" by auto
  let ?f="(\<lambda>k. (if a = k then 1 else 0) * A $ k $ b)"
  have sum0: "sum ?f (UNIV - {a}) = 0" by (rule sum.neutral, auto)
  have "sum ?f UNIV = sum ?f (insert a (UNIV - {a}))" using UNIV_rw by simp
  also have "... = ?f a + sum ?f (UNIV - {a})" by (rule sum.insert, simp_all)
  also have "... = ?f a" using sum0 by auto
  also have "... = A $ a $ b" by simp
  finally show "sum ?f UNIV = A $ a $ b" .
qed

text\<open>Code equations to execute the bezout matrix\<close>

definition "bezout_matrix_row A a b j bezout x
  = (let (p, q, u, v, d) = bezout (A $ a $ j) (A $ b $ j) 
      in
         vec_lambda (\<lambda>y. if x = a \<and> y = a then p else
                         if x = a \<and> y = b then q else
                         if x = b \<and> y = a then u else
                         if x = b \<and> y = b then v else
                         if x = y then 1 else 0))"

lemma bezout_matrix_row_code [code abstract]:
  "vec_nth (bezout_matrix_row A a b j bezout x) = 
      (let (p, q, u, v, d) = bezout (A $ a $ j) (A $ b $ j)
        in
          (\<lambda>y. if x = a \<and> y = a then p else
               if x = a \<and> y = b then q else
               if x = b \<and> y = a then u else
               if x = b \<and> y = b then v else
               if x = y then 1 else 0))" unfolding bezout_matrix_row_def 
               by (cases "bezout (A $ a $ j) (A $ b $ j)") auto

lemma [code abstract]: "vec_nth (bezout_matrix A a b j bezout) = bezout_matrix_row A a b j bezout"
  unfolding bezout_matrix_def unfolding bezout_matrix_row_def[abs_def] Let_def 
  by (cases "bezout (A $ a $ j) (A $ b $ j)") auto

subsubsection\<open>Properties of the bezout iterate function\<close>

lemma bezout_iterate_not_zero:
  assumes Aik_0: "A $ i $ from_nat k \<noteq> 0"
  and n: "n<nrows A"
  and a: "to_nat i \<le> n"
  and ib: "is_bezout_ext bezout"
  shows "bezout_iterate A n i (from_nat k) bezout $ i $ from_nat k \<noteq> 0"
  using Aik_0 n a
proof (induct n arbitrary: A)
  case 0
  have "to_nat i = 0" by (metis "0.prems"(3) le_0_eq)
  hence i0: "i=0" by (metis to_nat_eq_0)
  show ?case using "0.prems"(1) unfolding i0 by auto
next
  case (Suc n)
  show ?case
  proof (cases "Suc n = to_nat i")
    case True show ?thesis unfolding bezout_iterate.simps using True Suc.prems(1) by simp
  next
    case False
    let ?B="(bezout_matrix A i (from_nat (Suc n)) (from_nat k) bezout ** A)"
    have i_le_n: "to_nat i < Suc n" using Suc.prems(3) False by auto
    have "bezout_iterate A (Suc n) i (from_nat k) bezout $ i $ from_nat k 
      = bezout_iterate ?B n i (from_nat k) bezout $ i $ from_nat k" 
      unfolding bezout_iterate.simps using i_le_n by auto
    also have "... \<noteq> 0"
    proof (rule Suc.hyps, rule bezout_matrix_not_zero[OF ib])
      show "i \<noteq> from_nat (Suc n)" by (metis False Suc.prems(2) nrows_def to_nat_from_nat_id)
      show "A $ i $ from_nat k \<noteq> 0" by (rule Suc.prems(1))
      show "n < nrows ?B" by (metis Suc.prems(2) Suc_lessD nrows_def)
      show "to_nat i \<le> n" using i_le_n by auto
    qed
    finally show ?thesis .
  qed
qed



lemma bezout_iterate_preserves:
  fixes A k and i::"'b::mod_type"
  assumes e: "echelon_form_upt_k A k"
  and ib: "is_bezout_ext bezout"
  and Aik_0: "A $ i $ from_nat k \<noteq> 0"
  and n: "n<nrows A"
  and "b < from_nat k"
  and i_le_n: "to_nat i \<le> n"
  and k: "k<ncols A"
  and zero_upt_k_i: "is_zero_row_upt_k i k A" 
  shows "bezout_iterate A n i (from_nat k) bezout $ a $ b = A $ a $ b"
  using Aik_0 n i_le_n k zero_upt_k_i  e
proof (induct n arbitrary: A)
  case 0
  show ?case unfolding bezout_iterate.simps ..
next
  case (Suc n)
  show ?case
  proof (cases "Suc n = to_nat i")
    case True show ?thesis unfolding bezout_iterate.simps using True  by simp
  next
    case False
    have i_not_fn:" i \<noteq> from_nat (Suc n)"
      by (metis False Suc.prems(2) nrows_def to_nat_from_nat_id)
    let ?B="(bezout_matrix A i (from_nat (Suc n)) (from_nat k) bezout ** A)"
    have i_le_n: "to_nat i < Suc n" by (metis False Suc.prems(3) le_imp_less_or_eq)
    have "bezout_iterate A (Suc n) i (from_nat k) bezout $ a $ b 
      = bezout_iterate ?B n i (from_nat k) bezout $ a $ b"
      unfolding bezout_iterate.simps using i_le_n by auto
    also have "... = ?B $ a $ b"
    proof (rule Suc.hyps)
      show "?B $ i $ from_nat k \<noteq> 0" 
        by (metis False Suc.prems(1) Suc.prems(2) bezout_matrix_not_zero 
            ib nrows_def to_nat_from_nat_id)   
      show "n < nrows ?B" by (metis Suc.prems(2) Suc_lessD nrows_def)
      show "k < ncols ?B" by (metis Suc.prems(4) ncols_def)
      show "to_nat i \<le> n" using i_le_n by auto
      show "is_zero_row_upt_k i k ?B"
      proof (unfold is_zero_row_upt_k_def, clarify)
        fix j::'c assume j_k: "to_nat j < k"
        have j_k2: "j < from_nat k" by (metis from_nat_mono from_nat_to_nat_id j_k k ncols_def)
        have "?B $ i $ j = A $ i $ j" 
        proof (rule bezout_matrix_preserves_previous_columns[OF ib i_not_fn Suc.prems(1) j_k2], 
            unfold to_nat_from_nat_id[OF Suc.prems(4)[unfolded ncols_def]])
          show "is_zero_row_upt_k i k A" by (rule Suc.prems(5))
          show "is_zero_row_upt_k (from_nat (Suc n)) k A" 
            using echelon_form_upt_k_condition1[OF Suc.prems(6) Suc.prems(5)] 
            by (metis Suc.prems(2) from_nat_mono from_nat_to_nat_id i_le_n nrows_def)
        qed
        also have "... = 0" by (metis Suc.prems(5) is_zero_row_upt_k_def j_k)
        finally show "?B $ i $ j = 0" .
      qed
      show "echelon_form_upt_k ?B k" 
      proof (rule echelon_form_upt_k_bezout_matrix)
        show "echelon_form_upt_k A k" by (metis Suc.prems(6))
        show "is_bezout_ext bezout" by (rule ib)
        show "A $ i $ from_nat k \<noteq> 0" by (rule Suc.prems(1))
        show "is_zero_row_upt_k i k A" by (rule Suc.prems(5))
        have "(from_nat (to_nat i)::'b)\<le>from_nat (Suc n)"
          by (rule from_nat_mono'[OF Suc.prems(3) Suc.prems(2)[unfolded nrows_def]])
        thus "i < from_nat (Suc n)" using i_not_fn by auto
        show "k < ncols A" by (rule Suc.prems(4))
      qed
    qed
    also have "... = A $ a $ b"
    proof (rule bezout_matrix_preserves_previous_columns[OF ib])
      show "i \<noteq> from_nat (Suc n)" by (metis False Suc.prems(2) nrows_def to_nat_from_nat_id)
      show "A $ i $ from_nat k \<noteq> 0" by (rule Suc.prems(1))
      show "b < from_nat k" by (rule assms(5))
      show "is_zero_row_upt_k i (to_nat (from_nat k::'c)) A"
        unfolding to_nat_from_nat_id[OF Suc.prems(4)[unfolded ncols_def]] by (rule Suc.prems(5))
      show "is_zero_row_upt_k (from_nat (Suc n)) (to_nat (from_nat k::'c)) A"
        unfolding to_nat_from_nat_id[OF Suc.prems(4)[unfolded ncols_def]]
        by (metis Suc.prems(2) Suc.prems(5) Suc.prems(6) add_to_nat_def
          echelon_form_upt_k_condition1 from_nat_mono i_le_n monoid_add_class.add.right_neutral 
          nrows_def to_nat_0)
    qed
    finally show ?thesis .
  qed
qed




lemma bezout_iterate_preserves_below_n:
  assumes e: "echelon_form_upt_k A k"
  and ib: "is_bezout_ext bezout"
  and Aik_0: "A $ i $ from_nat k \<noteq> 0"
  and n: "n<nrows A"
  and n_less_a: "n < to_nat a"
  and k: "k<ncols A"
  and i_le_n: "to_nat i \<le> n"
  and zero_upt_k_i: "is_zero_row_upt_k i k A"
  shows "bezout_iterate A n i (from_nat k) bezout $ a $ b = A $ a $ b"
  using Aik_0 n i_le_n k zero_upt_k_i e n_less_a
proof (induct n arbitrary: A)
  case 0
  show ?case unfolding bezout_iterate.simps ..
next
  case (Suc n)
  show ?case
  proof (cases "Suc n = to_nat i")
    case True show ?thesis unfolding bezout_iterate.simps using True  by simp
  next
    case False
    have i_not_fn:" i \<noteq> from_nat (Suc n)"
      by (metis False Suc.prems(2) nrows_def to_nat_from_nat_id)
    let ?B="(bezout_matrix A i (from_nat (Suc n)) (from_nat k) bezout ** A)"
    have i_le_n: "to_nat i < Suc n" by (metis False Suc.prems(3) le_imp_less_or_eq)
    have zero_ikB: "is_zero_row_upt_k i k ?B"
    proof (unfold is_zero_row_upt_k_def, clarify)
      fix j::'b assume j_k: "to_nat j < k"
      have j_k2: "j < from_nat k" by (metis from_nat_mono from_nat_to_nat_id j_k k ncols_def)
      have "?B $ i $ j = A $ i $ j" 
      proof (rule bezout_matrix_preserves_previous_columns[OF ib i_not_fn Suc.prems(1) j_k2], 
          unfold to_nat_from_nat_id[OF Suc.prems(4)[unfolded ncols_def]])
        show "is_zero_row_upt_k i k A" by (rule Suc.prems(5))
        show "is_zero_row_upt_k (from_nat (Suc n)) k A" 
          using echelon_form_upt_k_condition1[OF Suc.prems(6) Suc.prems(5)] 
          by (metis Suc.prems(2) from_nat_mono from_nat_to_nat_id i_le_n nrows_def)
      qed
      also have "... = 0" by (metis Suc.prems(5) is_zero_row_upt_k_def j_k)
      finally show "?B $ i $ j = 0" .
    qed
    have "bezout_iterate A (Suc n) i (from_nat k) bezout $ a $ b 
      = bezout_iterate ?B n i (from_nat k) bezout $ a $ b"
      unfolding bezout_iterate.simps using i_le_n by auto
    also have "... = ?B $ a $ b"
    proof (rule Suc.hyps)
      show "?B $ i $ from_nat k \<noteq> 0" by (metis Suc.prems(1) bezout_matrix_not_zero i_not_fn ib)
      show "n < nrows ?B" by (metis Suc.prems(2) Suc_lessD nrows_def)
      show "to_nat i \<le> n" by (metis i_le_n less_Suc_eq_le)
      show "k < ncols ?B" by (metis Suc.prems(4) ncols_def)
      show "is_zero_row_upt_k i k ?B" by (rule zero_ikB)
      show "echelon_form_upt_k ?B k" 
      proof (rule echelon_form_upt_k_bezout_matrix[OF Suc.prems(6) ib 
          Suc.prems(1) Suc.prems(5) _ Suc.prems(4)]) 
        show "i < from_nat (Suc n)" 
          by (metis (no_types) Suc.prems(7) add_to_nat_def dual_order.strict_iff_order from_nat_mono
            i_le_n le_less_trans monoid_add_class.add.right_neutral to_nat_0 to_nat_less_card)
      qed
      show "n < to_nat a" by (metis Suc.prems(7) Suc_lessD)
    qed
    also have "... = A $ a $ b"
    proof (rule bezout_matrix_preserves_rest[OF ib _ _ _ Suc.prems(1)])
      show "a \<noteq> from_nat (Suc n)" 
        by (metis Suc.prems(7) add_to_nat_def from_nat_mono less_irrefl
          monoid_add_class.add.right_neutral to_nat_0 to_nat_less_card)
      show "i \<noteq> from_nat (Suc n)" by (rule i_not_fn)
      show "a \<noteq> i" by (metis assms(7) n_less_a not_le)
      show "is_zero_row_upt_k i (to_nat (from_nat k::'b)) A"
        by (metis Suc.prems(4) Suc.prems(5) ncols_def to_nat_from_nat_id)
    qed
    finally show ?thesis .
  qed
qed

lemma bezout_iterate_zero_column_k:
  fixes A::"'a::bezout_domain^'cols::{mod_type}^'rows::{mod_type}"
  assumes e: "echelon_form_upt_k A k"
  and ib: "is_bezout_ext bezout"
  and Aik_0: "A $ i $ from_nat k \<noteq> 0"
  and n: "n<nrows A"
  and i_le_a: "i<a"
  and k: "k<ncols A"
  and a_n: "to_nat a\<le>n"
  and zero_upt_k_i: "is_zero_row_upt_k i k A"
  shows "bezout_iterate A n i (from_nat k) bezout $ a $ from_nat k = 0"
  using e Aik_0 n k a_n zero_upt_k_i
proof (induct n arbitrary: A)
  case 0
  show ?case unfolding bezout_iterate.simps
    using "0.prems"(5) i_le_a to_nat_from_nat to_nat_le by auto
next
  case (Suc n)
  show ?case
  proof (cases "Suc n = to_nat i")
    case True show ?thesis unfolding bezout_iterate.simps using True 
      by (metis Suc.prems(5) i_le_a leD to_nat_mono)
  next
    case False
    have i_not_fn:" i \<noteq> from_nat (Suc n)"
      by (metis False Suc.prems(3) nrows_def to_nat_from_nat_id)
    let ?B="(bezout_matrix A i (from_nat (Suc n)) (from_nat k) bezout ** A)"
    have i_le_n: "to_nat i < Suc n" by (metis Suc.prems(5) i_le_a le_less_trans not_le to_nat_mono)
    have zero_ikB: "is_zero_row_upt_k i k ?B" 
    proof (unfold is_zero_row_upt_k_def, clarify)
      fix j::'cols assume j_k: "to_nat j < k"
      have j_k2: "j < from_nat k" 
        using from_nat_mono[OF j_k Suc.prems(4)[unfolded ncols_def]]
        unfolding from_nat_to_nat_id .
      have "?B $ i $ j = A $ i $ j" 
      proof (rule bezout_matrix_preserves_previous_columns[OF ib i_not_fn Suc.prems(2) j_k2],
          unfold to_nat_from_nat_id[OF Suc.prems(4)[unfolded ncols_def]])
        show "is_zero_row_upt_k i k A" by (rule Suc.prems(6))
        show "is_zero_row_upt_k (from_nat (Suc n)) k A" 
          using echelon_form_upt_k_condition1[OF Suc.prems(1)]
          by (metis (mono_tags) Suc.prems(3) Suc.prems(6) add_to_nat_def 
            from_nat_mono i_le_n monoid_add_class.add.right_neutral nrows_def to_nat_0)
      qed
      also have "... = 0" by (metis Suc.prems(6) is_zero_row_upt_k_def j_k)
      finally show "?B $ i $ j = 0" .
    qed
    have "bezout_iterate A (Suc n) i (from_nat k) bezout $ a $ (from_nat k) 
      = bezout_iterate ?B n i (from_nat k) bezout $ a $ (from_nat k)"
      unfolding bezout_iterate.simps using i_le_n by auto
    also have "... = 0"
    proof (cases "to_nat a = Suc n")
      case True
      have "bezout_iterate ?B n i (from_nat k) bezout $ a $ (from_nat k) = ?B $ a $ from_nat k" 
      proof (rule bezout_iterate_preserves_below_n[OF _ ib])
        show "echelon_form_upt_k ?B k"
          by (metis (erased, hide_lams) Suc.prems(1) Suc.prems(2) Suc.prems(4) Suc.prems(6) True
            echelon_form_upt_k_bezout_matrix from_nat_to_nat_id i_le_a ib)
        show "?B $ i $ from_nat k \<noteq> 0" 
          by (metis Suc.prems(2) bezout_matrix_not_zero i_not_fn ib)
        show "n < nrows ?B" by (metis Suc.prems(3) Suc_lessD nrows_def)
        show "n < to_nat a" by (metis True lessI)
        show "k < ncols ?B" by (metis Suc.prems(4) ncols_def)
        show "to_nat i \<le> n" by (metis i_le_n less_Suc_eq_le)
        show "is_zero_row_upt_k i k ?B" by (rule zero_ikB)
      qed
      also have "... = 0"
        by (metis Suc.prems(2) True bezout_matrix_works2 
           i_not_fn ib to_nat_from_nat)
      finally show ?thesis .
    next
      case False
      show ?thesis  
      proof (rule Suc.hyps)
        show "echelon_form_upt_k ?B k" 
        proof (rule echelon_form_upt_k_bezout_matrix
          [OF Suc.prems(1) ib Suc.prems(2) Suc.prems(6) _ Suc.prems(4)])
          show "i < from_nat (Suc n)"
            by (metis (mono_tags) Suc.prems(3) from_nat_mono from_nat_to_nat_id i_le_n nrows_def)
        qed
        show "?B $ i $ from_nat k \<noteq> 0" by (metis Suc.prems(2) bezout_matrix_not_zero i_not_fn ib)
        show "n < nrows ?B" by (metis Suc.prems(3) Suc_lessD nrows_def)
        show "k < ncols ?B" by (metis Suc.prems(4) ncols_def)
        show "to_nat a \<le> n" by (metis False Suc.prems(5) le_SucE)
        show "is_zero_row_upt_k i k ?B" by (rule zero_ikB)
      qed
    qed
    finally show ?thesis .
  qed
qed

subsubsection\<open>Proving the correctness\<close>

lemma condition1_index_le_zero_row: 
  fixes A k
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0
    else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  assumes e: "echelon_form_upt_k A k"
  and "is_zero_row_upt_k a (Suc k) A"
  shows "from_nat i\<le>a"
proof (rule ccontr)
  have zero_ik: "is_zero_row_upt_k a k A" by (metis assms(3) is_zero_row_upt_k_le) 
  assume a: "\<not> from_nat i \<le> (a::'a)" hence ai: "a < from_nat i" by simp
  show False
  proof (cases "(from_nat i::'a)=0")
    case True thus ?thesis using ai least_mod_type[of a] unfolding True from_nat_0 by auto
  next
    case False
    from a have "a \<le> from_nat i - 1" by (intro leI) (auto dest: le_Suc)
    also from False have "i \<noteq> 0" by (intro notI) (simp_all add: from_nat_0)
    hence "i = (i - 1) + 1" by simp
    also have "from_nat \<dots> = from_nat (i - 1) + 1" by (rule from_nat_suc)
    finally have ai2: "a \<le> from_nat (i - 1)" by simp
    have "i = to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1" using i False
      by (metis from_nat_0)
    hence "i - 1 = to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)" by simp
    hence "from_nat (i - 1) = (GREATEST n. \<not> is_zero_row_upt_k n k A)"
      using from_nat_to_nat_id by auto
    hence "\<not> is_zero_row_upt_k (from_nat (i - 1)) k A" using False GreatestI_ex i
      by (metis from_nat_to_nat_id to_nat_0)
    moreover have "is_zero_row_upt_k (from_nat (i - 1)) k A" 
      using echelon_form_upt_k_condition1[OF e zero_ik]
      using ai2 zero_ik by (cases "a = from_nat (i - 1)", auto)
    ultimately show False by contradiction
  qed
qed



lemma condition1_part1: 
  fixes A k
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 
    else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  assumes e: "echelon_form_upt_k A k"
  and a: "is_zero_row_upt_k a (Suc k) A"
  and ab: "a < b"
  and all_zero: "\<forall>m\<ge>from_nat i. A $ m $ from_nat k = 0"
  shows "is_zero_row_upt_k b (Suc k) A"
proof (rule is_zero_row_upt_k_suc)
  have zero_ik: "is_zero_row_upt_k a k A" by (metis assms(3) is_zero_row_upt_k_le)
  show "is_zero_row_upt_k b k A"
    using echelon_form_upt_k_condition1[OF e zero_ik] using ab by auto
  have "from_nat i\<le>a"
    using condition1_index_le_zero_row[OF e a] all_zero unfolding i by auto
  thus "A $ b $ from_nat k = 0" using all_zero ab by auto
qed



lemma condition1_part2: 
  fixes A k
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 
  else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  assumes e: "echelon_form_upt_k A k"
  and a: "is_zero_row_upt_k a (Suc k) A"
  and ab: "a < b"
  and i_last: "i = nrows A"
  and all_zero: "\<forall>m>from_nat (nrows A). A $ m $ from_nat k = 0"
  shows "is_zero_row_upt_k b (Suc k) A"
proof -
  have zero_ik: "is_zero_row_upt_k a k A" by (metis assms(3) is_zero_row_upt_k_le)
  have i_le_a: "from_nat i\<le>a" using condition1_index_le_zero_row[OF e a] unfolding i .
  have "(from_nat (nrows A)::'a) = 0" unfolding nrows_def using from_nat_CARD .
  thus ?thesis using ab i_last i_le_a
    by (metis all_zero e echelon_form_upt_k_condition1 is_zero_row_upt_k_suc le_less_trans zero_ik)
qed


lemma condition1_part3:
  fixes A k bezout
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 
  else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  defines B: "B \<equiv> fst ((echelon_form_of_column_k bezout) (A,i) k)"
  assumes e: "echelon_form_upt_k A k" and ib: "is_bezout_ext bezout"
  and a: "is_zero_row_upt_k a (Suc k) B"
  and "a < b"
  and all_zero: "\<forall>m>from_nat i. A $ m $ from_nat k = 0"
  and i_not_last: "i \<noteq> nrows A"
  and i_le_m: "from_nat i \<le> m"
  and Amk_not_0: "A $ m $ from_nat k \<noteq> 0"
  shows "is_zero_row_upt_k b (Suc k) A"
proof (rule is_zero_row_upt_k_suc)
  have AB: "A = B" unfolding B echelon_form_of_column_k_def Let_def using all_zero by auto
  have i_le_a: "from_nat i\<le>a"
    using condition1_index_le_zero_row[OF e a[unfolded AB[symmetric]]] unfolding i .
  show "A $ b $ from_nat k = 0" by (metis i_le_a all_zero assms(6) le_less_trans)
  show "is_zero_row_upt_k b k A"
    by (metis (poly_guards_query) AB a assms(6) e 
        echelon_form_upt_k_condition1 is_zero_row_upt_k_le)
qed

lemma condition1_part4:
  fixes A k bezout i
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 
  else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  defines B: "B\<equiv> fst ((echelon_form_of_column_k bezout) (A,i) k)"
  assumes e: "echelon_form_upt_k A k"
  assumes a: "is_zero_row_upt_k a (Suc k) A"
  and i_nrows: "i = nrows A"
  shows "is_zero_row_upt_k b (Suc k) A"
proof -
  have eq_G: "from_nat (i - 1) = (GREATEST n. \<not> is_zero_row_upt_k n k A)"
    by (metis One_nat_def Suc_eq_plus1 i_nrows diff_Suc_Suc 
        diff_zero from_nat_to_nat_id i nrows_not_0)
  hence a_le: "a\<le>from_nat (i - 1)"
    by (metis One_nat_def Suc_pred i_nrows lessI not_less not_less_eq nrows_def 
      to_nat_from_nat_id to_nat_less_card to_nat_mono zero_less_card_finite)
  have not_zero_G: "\<not> is_zero_row_upt_k (from_nat(i - 1)) k A"
    unfolding eq_G 
    by (metis (mono_tags) GreatestI_ex i_nrows i nrows_not_0)
  hence "\<not> is_zero_row_upt_k a k A" 
    by (metis a_le dual_order.strict_iff_order e echelon_form_upt_k_condition1)
  hence "\<not> is_zero_row_upt_k a (Suc k) A" 
    by (metis is_zero_row_upt_k_le)
  thus ?thesis using a by contradiction
qed


lemma condition1_part5:
  fixes A::"'a::bezout_domain^'cols::{mod_type}^'rows::{mod_type}"
  and k bezout
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 
    else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  defines B: "B \<equiv> fst((echelon_form_of_column_k bezout) (A,i) k)"
  assumes ib: "is_bezout_ext bezout" and e: "echelon_form_upt_k A k"
  assumes zero_a_B: "is_zero_row_upt_k a (Suc k) B"
  and ab: "a < b"
  and im: "from_nat i < m"
  and Amk_not_0: "A $ m $ from_nat k \<noteq> 0"
  and not_last_row: "i \<noteq> nrows A"
  and k: "k<ncols A"
  shows "is_zero_row_upt_k b (Suc k) (bezout_iterate 
  (interchange_rows A (from_nat i) (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (from_nat i) \<le> n)) 
  (nrows A - Suc 0) (from_nat i) (from_nat k) bezout)"
proof (rule is_zero_row_upt_k_suc)
  let ?least="(LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n)"
  let ?interchange="(interchange_rows A (from_nat i) ?least)"
  let ?bezout_iterate="(bezout_iterate ?interchange 
    (nrows A - Suc 0) (from_nat i) (from_nat k) bezout)"
  have B_eq: "B = ?bezout_iterate" unfolding B echelon_form_of_column_k_def
    Let_def fst_conv snd_conv using im Amk_not_0 not_last_row by auto
  have zero_ikA: "is_zero_row_upt_k (from_nat i) k A"
  proof (cases "\<forall>m. is_zero_row_upt_k m k A")
    case True
    thus ?thesis by simp
  next
    case False
    hence i_eq: "i=to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1" unfolding i by auto
    show ?thesis
    proof (rule row_greater_greatest_is_zero, simp add: i_eq from_nat_to_nat_greatest,rule Suc_le')
      show " (GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<noteq> 0"
      proof -
        have "\<And>x\<^sub>1. \<not> x\<^sub>1 < i \<or> \<not> to_nat (GREATEST R. \<not> is_zero_row_upt_k R k A) < x\<^sub>1" 
          using i_eq by linarith
        thus "(GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 \<noteq> 0"
          by (metis One_nat_def add_Suc_right neq_iff 
            from_nat_to_nat_greatest i_eq monoid_add_class.add.right_neutral 
            nat.distinct(1) not_last_row nrows_def to_nat_0 to_nat_from_nat_id to_nat_less_card)
      qed
    qed 
  qed
  have zero_interchange: "is_zero_row_upt_k (from_nat i) k ?interchange"
  proof (unfold is_zero_row_upt_k_def, clarify)
    fix j::'cols assume j_less_k: "to_nat j < k"
    have i_le_least: "from_nat i\<le>?least" 
      by (metis (mono_tags, lifting) Amk_not_0 LeastI2_wellorder less_imp_le im)
    hence zero_least_kA: "is_zero_row_upt_k ?least k A" 
      using echelon_form_upt_k_condition1[OF e zero_ikA] 
      by (metis (poly_guards_query) dual_order.strict_iff_order zero_ikA)
    have "?interchange $ from_nat i $ j = A $ ?least $ j" by simp
    also have "... = 0" using zero_least_kA j_less_k unfolding is_zero_row_upt_k_def by simp
    finally show "?interchange $ from_nat i $ j = 0" .
  qed
  have zero_a_k: "is_zero_row_upt_k a k A"
  proof (unfold is_zero_row_upt_k_def, clarify)
    fix j::'cols assume j_less_k: "to_nat j < k"
    have "?interchange $ a $ j = ?bezout_iterate $ a $ j"
    proof (rule bezout_iterate_preserves[symmetric])
      show "echelon_form_upt_k ?interchange k" 
      proof (rule echelon_form_upt_k_interchange[OF e zero_ikA Amk_not_0 _ k])
        show "from_nat i \<le> m" using im by auto
      qed
      show "is_bezout_ext bezout" using ib .
      show "?interchange $ (from_nat i) $ from_nat k \<noteq> 0" 
        by (metis (mono_tags, lifting) Amk_not_0 LeastI_ex dual_order.strict_iff_order 
          im interchange_rows_i)
      show "nrows A - Suc 0 < nrows ?interchange" unfolding nrows_def by simp
      show "j < from_nat k" by (metis from_nat_mono from_nat_to_nat_id j_less_k k ncols_def)
      show "to_nat (from_nat i::'rows) \<le> nrows A - Suc 0"
        by (metis Suc_eq_plus1 Suc_le_mono Suc_pred 
          discrete nrows_def to_nat_less_card zero_less_card_finite)
      show "k < ncols ?interchange" using k unfolding ncols_def by auto
      show "is_zero_row_upt_k (from_nat i) k ?interchange" using zero_interchange .
    qed
    also have "... = 0" using zero_a_B j_less_k unfolding B_eq is_zero_row_upt_k_def by auto
    finally have *: "?interchange $ a $ j = 0" .
    show "A $ a $ j = 0"
    proof (cases "a=from_nat i")
      case True
      show ?thesis unfolding True using zero_ikA j_less_k unfolding is_zero_row_upt_k_def by auto
    next
      case False note a_not_i=False
      show ?thesis
      proof (cases "a=?least")
        case True
        show ?thesis 
          using zero_interchange unfolding True is_zero_row_upt_k_def using j_less_k by auto
      next
        case False note a_not_least=False
        have "?interchange $ a $ j = A $ a $ j" using a_not_least a_not_i 
          by (metis (erased, lifting) interchange_rows_preserves)
        thus ?thesis unfolding * ..
      qed 
    qed               
  qed
  hence zero_b_k: "is_zero_row_upt_k b k A"
    by (metis ab e echelon_form_upt_k_condition1)
  have i_le_a: "from_nat i\<le>a" 
    unfolding i
  proof (auto simp add: from_nat_to_nat_greatest from_nat_0)
    show "0 \<le> a" by (metis least_mod_type)
    fix m assume m: "\<not> is_zero_row_upt_k m k A"
    have "(GREATEST n. \<not> is_zero_row_upt_k n k A) < a" 
      by (metis (no_types, lifting) GreatestI_ex neq_iff 
        e echelon_form_upt_k_condition1 m zero_a_k)
    thus "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> a" by (metis le_Suc)
  qed 
  have i_not_b: "from_nat i \<noteq> b" using i_le_a ab by simp
  show "is_zero_row_upt_k b k ?bezout_iterate"
  proof (unfold is_zero_row_upt_k_def, clarify)
    fix j::'cols assume j_less_k: "to_nat j < k"
    have "?bezout_iterate $ b $ j = ?interchange $ b $ j"
    proof (rule bezout_iterate_preserves)
      show "echelon_form_upt_k ?interchange k"
      proof (rule echelon_form_upt_k_interchange[OF e zero_ikA Amk_not_0 _ k])
        show "from_nat i \<le> m" using im by auto
      qed
      show "is_bezout_ext bezout" using ib .
      show "?interchange $ from_nat i $ from_nat k \<noteq> 0"
        by (metis (mono_tags, lifting) Amk_not_0 LeastI_ex 
          dual_order.strict_iff_order im interchange_rows_i)
      show "nrows A - Suc 0 < nrows ?interchange" unfolding nrows_def by simp
      show "j < from_nat k" by (metis from_nat_mono from_nat_to_nat_id j_less_k k ncols_def)
      show "to_nat (from_nat i::'rows) \<le> nrows A - Suc 0"
        by (metis Suc_eq_plus1 Suc_le_mono Suc_pred 
          discrete nrows_def to_nat_less_card zero_less_card_finite)
      show "k < ncols ?interchange" using k unfolding ncols_def by auto
      show "is_zero_row_upt_k (from_nat i) k ?interchange" by (rule zero_interchange)
    qed
    also have "... = A $ b $ j"
    proof (cases "b=?least")
      case True
      have "?interchange $ b $ j = A $ (from_nat i) $ j" using True by auto
      also have "... = A $ b $ j" 
        using zero_b_k zero_ikA j_less_k unfolding is_zero_row_upt_k_def by auto
      finally show ?thesis .
    next
      case False
      show ?thesis using False using interchange_rows_preserves[OF i_not_b] 
        by (metis (no_types, lifting))
    qed        
    also have "... = 0" using zero_b_k j_less_k unfolding is_zero_row_upt_k_def by auto 
    finally show "?bezout_iterate $ b $ j = 0" .
  qed
  show "?bezout_iterate $ b $ from_nat k = 0"
  proof (rule bezout_iterate_zero_column_k[OF _ ib])
    show "echelon_form_upt_k ?interchange k"
    proof (rule echelon_form_upt_k_interchange[OF e zero_ikA Amk_not_0 _ k])
      show "from_nat i \<le> m" using im by auto
    qed
    show "?interchange $ from_nat i $ from_nat k \<noteq> 0"
      by (metis (mono_tags, lifting) Amk_not_0 LeastI_ex 
        dual_order.strict_iff_order im interchange_rows_i) 
    show "nrows A - Suc 0 < nrows ?interchange" unfolding nrows_def by simp
    show "from_nat i < b" by (metis ab i_le_a le_less_trans)
    show "k < ncols ?interchange" by (metis (full_types, lifting) k ncols_def)
    show "to_nat b \<le> nrows A - Suc 0" 
      by (metis Suc_pred leD not_less_eq_eq nrows_def to_nat_less_card zero_less_card_finite)
    show "is_zero_row_upt_k (from_nat i) k ?interchange" by (rule zero_interchange)
  qed
qed


lemma condition2_part1:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}" and k bezout i
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 
    else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  defines B:"B \<equiv> fst ((echelon_form_of_column_k bezout) (A,i) k)"
  assumes e: "echelon_form_upt_k A k"
  and ab: "a < b" and not_zero_aB: "\<not> is_zero_row_upt_k a (Suc k) B" 
  and not_zero_bB: "\<not> is_zero_row_upt_k b (Suc k) B"
  and all_zero: "\<forall>m\<ge>from_nat i. A $ m $ from_nat k = 0" 
  shows "(LEAST n. A $ a $ n \<noteq> 0) < (LEAST n. A $ b $ n \<noteq> 0)"
proof -
  have B_eq_A: "B=A" 
    unfolding B echelon_form_of_column_k_def Let_def fst_conv snd_conv
    using all_zero by auto
  show ?thesis
  proof (cases "\<forall>m. is_zero_row_upt_k m k A")
    case True
    have i0: "i = 0" unfolding i using True by simp
    have "is_zero_row_upt_k a k B" using True unfolding B_eq_A by auto
    moreover have "B $ a $ from_nat k = 0" using all_zero unfolding i0 from_nat_0 
      by (metis B_eq_A least_mod_type)  
    ultimately have "is_zero_row_upt_k a (Suc k) B" by (rule is_zero_row_upt_k_suc)
    thus ?thesis using not_zero_aB by contradiction
  next
    case False note not_all_zero=False
    have i2: "i = to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1" 
      unfolding i using False by auto
    have not_zero_aA: "\<not> is_zero_row_upt_k a k A"
      by (metis (erased, lifting) B_eq_A GreatestI_ex add_to_nat_def all_zero neq_iff e 
        echelon_form_upt_k_condition1 i2 is_zero_row_upt_k_suc le_Suc 
        not_all_zero not_zero_aB to_nat_1)
    moreover have not_zero_bA: "\<not> is_zero_row_upt_k b k A"
      by (metis (erased, lifting) B_eq_A GreatestI_ex add_to_nat_def all_zero neq_iff e 
        echelon_form_upt_k_condition1 i2 is_zero_row_upt_k_suc le_Suc 
        not_all_zero not_zero_bB to_nat_1)
    ultimately show ?thesis using echelon_form_upt_k_condition2[OF e ab] by simp
  qed
qed

lemma condition2_part2: 
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}" and k bezout i
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 else 
  to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  assumes e: "echelon_form_upt_k A k"
  and ab: "a < b"
  and all_zero: "\<forall>m>from_nat (nrows A). A $ m $ from_nat k = 0" 
  and i_nrows: "i = nrows A"
  shows "(LEAST n. A $ a $ n \<noteq> 0) < (LEAST n. A $ b $ n \<noteq> 0)"
proof -
  have not_all_zero: "\<not> (\<forall>m. is_zero_row_upt_k m k A)" 
    by (metis i i_nrows nrows_not_0)
  have "(GREATEST m. \<not> is_zero_row_upt_k m k A) + 1 = 0"
    by (metis (mono_tags, lifting) add_0_right One_nat_def Suc_le' add_Suc_right i i_nrows 
      less_not_refl less_trans_Suc nrows_def to_nat_less_card to_nat_mono zero_less_card_finite)
  hence g_minus_1: "(GREATEST m. \<not> is_zero_row_upt_k m k A) = - 1" by (simp add: a_eq_minus_1)
  have "\<not> is_zero_row_upt_k a k A" 
  proof (rule greatest_ge_nonzero_row'[OF e _ not_all_zero])    
    show "a \<le> (GREATEST m. \<not> is_zero_row_upt_k m k A)"
      by (simp add: Greatest_is_minus_1 g_minus_1)
  qed
  moreover have "\<not> is_zero_row_upt_k b k A" 
  proof (rule greatest_ge_nonzero_row'[OF e _ not_all_zero])    
    show "b \<le> (GREATEST m. \<not> is_zero_row_upt_k m k A)"
      by (simp add: Greatest_is_minus_1 g_minus_1)
  qed
  ultimately show ?thesis using echelon_form_upt_k_condition2[OF e ab] by simp
qed

lemma condition2_part3:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}" and k bezout i
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 
    else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  defines B:"B \<equiv> fst ((echelon_form_of_column_k bezout) (A,i) k)"
  assumes e: "echelon_form_upt_k A k" and k: "k<ncols A"
  and ab: "a < b" and not_zero_aB: "\<not> is_zero_row_upt_k a (Suc k) B" 
  and not_zero_bB: "\<not> is_zero_row_upt_k b (Suc k) B"
  and all_zero: "\<forall>m>from_nat i. A $ m $ from_nat k = 0"
  and i_ma: "from_nat i \<le> ma" and A_ma_k: "A $ ma $ from_nat k \<noteq> 0"
  shows "(LEAST n. A $ a $ n \<noteq> 0) < (LEAST n. A $ b $ n \<noteq> 0)"
proof -
  have B_eq_A: "B=A" 
    unfolding B echelon_form_of_column_k_def Let_def fst_conv snd_conv
    using all_zero by simp
  have not_all_zero: "\<not> (\<forall>m. is_zero_row_upt_k m k A)"
    by (metis B_eq_A ab all_zero from_nat_0 i is_zero_row_upt_k_suc 
      le_less_trans least_mod_type not_zero_bB)
  have i2: "i = to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1" 
    unfolding i using not_all_zero by auto
  have not_zero_aA: "\<not> is_zero_row_upt_k a k A"  
  proof -
    have "\<And>x\<^sub>1 x\<^sub>2. from_nat (to_nat (x\<^sub>1::'rows) + 1) \<le> x\<^sub>2 \<or> \<not> x\<^sub>1 < x\<^sub>2" 
      by (metis (no_types) add_to_nat_def le_Suc to_nat_1)
    moreover
    { assume "\<not> is_zero_row_upt_k b k A"
      hence "\<not> is_zero_row_upt_k a k A" using ab e echelon_form_upt_k_condition1 by blast }
    ultimately show "\<not> is_zero_row_upt_k a k A" 
      by (metis B_eq_A greatest_less_zero_row ab all_zero le_imp_less_or_eq e i2 
        is_zero_row_upt_k_suc not_all_zero not_zero_aB not_zero_bB)
  qed   
  show ?thesis
  proof (cases "\<not> is_zero_row_upt_k b k A")
    case True
    thus ?thesis using not_zero_aA echelon_form_upt_k_condition2[OF e ab] by simp
  next
    case False note zero_bA=False
    obtain v where Aav: "A $ a $ v \<noteq> 0" and v: "v<from_nat k" 
      using not_zero_aA unfolding is_zero_row_upt_k_def 
      by (metis from_nat_mono from_nat_to_nat_id k ncols_def)
    have least_v: "(LEAST n. A $ a $ n \<noteq> 0) \<le> v" by (rule Least_le, simp add: Aav)
    have b_ge_greatest: "b>(GREATEST n. \<not> is_zero_row_upt_k n k A)" 
      using False by (simp add: greatest_less_zero_row e not_all_zero)
    have i_eq_b: "from_nat i = b"
    proof (rule ccontr, cases "from_nat i < b")
      case True
      hence Abk_0: "A $ b $ from_nat k = 0" using all_zero by auto
      have "is_zero_row_upt_k b (Suc k) B" 
      proof (rule is_zero_row_upt_k_suc)
        show "is_zero_row_upt_k b k B" using zero_bA unfolding B_eq_A by simp
        show "B $ b $ from_nat k = 0" using Abk_0 unfolding B_eq_A by simp
      qed
      thus False using not_zero_bB by contradiction
    next
      case False
      assume i_not_b: "from_nat i \<noteq> b"
      hence b_less_i: "from_nat i > b" using False by simp
      thus False using b_ge_greatest unfolding i
        by (metis (no_types, lifting) False Suc_less add_to_nat_def i2 i_not_b to_nat_1)
    qed
    have Abk_not_0: "A $ b $ from_nat k \<noteq> 0"
      using False not_zero_bB unfolding B_eq_A is_zero_row_upt_k_def 
      by (metis B_eq_A False is_zero_row_upt_k_suc not_zero_bB)
    have "(LEAST n. A $ b $ n \<noteq> 0) = from_nat k" 
    proof (rule Least_equality)
      show "A $ b $ from_nat k \<noteq> 0" by (rule Abk_not_0)
      show "\<And>y. A $ b $ y \<noteq> 0 \<Longrightarrow> from_nat k \<le> y" 
        by (metis False is_zero_row_upt_k_def k ncols_def not_less to_nat_from_nat_id to_nat_mono)
    qed
    thus ?thesis using least_v v by auto
  qed
qed

lemma condition2_part4:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}" and k bezout i
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 
  else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  assumes  e: "echelon_form_upt_k A k"
  and ab: "a < b" 
  and i_nrows: "i = nrows A"
  shows "(LEAST n. A $ a $ n \<noteq> 0) < (LEAST n. A $ b $ n \<noteq> 0)"
proof -
  have not_all_zero: "\<not> (\<forall>m. is_zero_row_upt_k m k A)" by (metis i_nrows i nrows_not_0)
  then have "i = to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1" by (simp add: i)
  then have "nrows A = to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1" by (simp add: i_nrows)
  then have "CARD('rows) = mod_type_class.to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
    unfolding nrows_def .
  then have "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 = 0"
    using to_nat_plus_one_less_card by auto
  hence g: "(GREATEST n. \<not> is_zero_row_upt_k n k A) = -1" by (simp add: a_eq_minus_1)
  have "\<not> is_zero_row_upt_k a k A" 
  proof (rule greatest_ge_nonzero_row'[OF e _ not_all_zero])
    show "a \<le> (GREATEST m. \<not> is_zero_row_upt_k m k A)" by (simp add: Greatest_is_minus_1 g)
  qed
  moreover have "\<not> is_zero_row_upt_k b k A" 
  proof (rule greatest_ge_nonzero_row'[OF e _ not_all_zero])
    show "b \<le> (GREATEST m. \<not> is_zero_row_upt_k m k A)" by (simp add: Greatest_is_minus_1 g)
  qed
  ultimately show ?thesis using echelon_form_upt_k_condition2[OF e ab] by simp
qed

lemma condition2_part5:
  fixes A::"'a::{bezout_domain}^'cols::{mod_type}^'rows::{mod_type}" and k bezout i
  defines i:"i\<equiv>(if \<forall>m. is_zero_row_upt_k m k A then 0 
  else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  defines B:"B \<equiv> fst ((echelon_form_of_column_k bezout) (A,i) k)"
  assumes ib: "is_bezout_ext bezout" and e: "echelon_form_upt_k A k" and k: "k<ncols A"
  and ab: "a < b" and not_zero_aB: "\<not> is_zero_row_upt_k a (Suc k) B" 
  and not_zero_bB: "\<not> is_zero_row_upt_k b (Suc k) B"
  and i_m:"from_nat i < m"
  and A_mk: "A $ m $ from_nat k \<noteq> 0"
  and i_not_nrows: "i \<noteq> nrows A"
  shows "(LEAST n. B $ a $ n \<noteq> 0) < (LEAST n. B $ b $ n \<noteq> 0)"
proof -
  have B_eq: "B = bezout_iterate (interchange_rows A (from_nat i)
    (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n)) 
    (nrows A - Suc 0) (from_nat i) (from_nat k) bezout"
    unfolding B echelon_form_of_column_k_def Let_def fst_conv snd_conv
    using i_m A_mk i_not_nrows by auto
  let ?least="(LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n)"
  let ?interchange="interchange_rows A (from_nat i) ?least"
  let ?greatest="(GREATEST n. \<not> is_zero_row_upt_k n k A)"
  have nrows_less: "nrows A - Suc 0 < nrows ?interchange" unfolding nrows_def by auto
  have interchange_ik_not_zero: "?interchange $ from_nat i $ from_nat k \<noteq> 0" 
    by (metis (mono_tags, lifting) A_mk LeastI_ex dual_order.strict_iff_order 
      i_m interchange_rows_i)
  have k2: "k < ncols ?interchange" using k unfolding ncols_def by simp
  have to_nat_b: "to_nat b \<le> nrows A - Suc 0" 
    by (metis Suc_pred leD not_less_eq_eq nrows_def to_nat_less_card zero_less_card_finite)
  have to_nat_from_nat_i: "to_nat (from_nat i::'rows) \<le> nrows A - Suc 0"
    using i_not_nrows unfolding nrows_def
    by (metis Suc_pred less_Suc_eq_le to_nat_less_card zero_less_card_finite)    
  have not_all_zero: "\<not> (\<forall>m. is_zero_row_upt_k m k A)"
  proof (rule ccontr)
    assume all_zero: "\<not>\<not>(\<forall>m. is_zero_row_upt_k m k A)"
    hence zero_aA: "is_zero_row_upt_k a k A" and zero_bA: "is_zero_row_upt_k b k A" by auto
    have echelon_interchange: "echelon_form_upt_k ?interchange k"
    proof (rule echelon_form_upt_k_interchange[OF e _ A_mk _ k])
      show "is_zero_row_upt_k (from_nat i) k A" using all_zero by auto
      show "from_nat i \<le> m" using i_m by auto
    qed
    have zero_i_interchange: "is_zero_row_upt_k (from_nat i) k ?interchange" 
      using all_zero unfolding is_zero_row_upt_k_def by auto
    have zero_bB: "is_zero_row_upt_k b k B"
    proof (unfold is_zero_row_upt_k_def, clarify)
      fix j::'cols assume j: "to_nat j < k"
      have "B $ b $ j = ?interchange $ b $ j"
      proof (unfold B_eq, rule bezout_iterate_preserves
          [OF echelon_interchange ib interchange_ik_not_zero nrows_less _ 
            to_nat_from_nat_i k2 zero_i_interchange])  
        show "j < from_nat k" using j by (metis from_nat_mono from_nat_to_nat_id k ncols_def)
      qed
      also have "... = 0" 
        using all_zero j
        unfolding is_zero_row_upt_k_def interchange_rows_def by auto
      finally show "B $ b $ j = 0" .
    qed
    have i_not_b: "from_nat i \<noteq> b" 
      using i all_zero ab least_mod_type by (metis leD from_nat_0)
    have "B $ b $ from_nat k \<noteq> 0"  by (metis is_zero_row_upt_k_suc not_zero_bB zero_bB)
    moreover have "B $ b $ from_nat k = 0"
    proof (unfold B_eq, rule bezout_iterate_zero_column_k
        [OF echelon_interchange ib interchange_ik_not_zero nrows_less 
          _ k2 to_nat_b zero_i_interchange])
      show "from_nat i < b" 
        by (metis all_zero antisym_conv1 from_nat_0 i i_not_b least_mod_type)
    qed   
    ultimately show False by contradiction
  qed
  have i2: "i = to_nat (?greatest) + 1"
    unfolding i using not_all_zero by auto
  have g_rw: "(from_nat (to_nat ?greatest + 1))
    = ?greatest + 1" by (metis add_to_nat_def to_nat_1)
  have zero_least_kA: "is_zero_row_upt_k ?least k A" 
  proof (rule row_greater_greatest_is_zero)
    have "?greatest < from_nat i"
      by (metis Suc_eq_plus1 Suc_le' add_to_nat_def neq_iff from_nat_0 from_nat_mono 
        i2 i_not_nrows not_less_eq nrows_def to_nat_1 to_nat_less_card zero_less_Suc)
    also have "... \<le> ?least"
      by (metis (mono_tags, lifting) A_mk LeastI_ex dual_order.strict_iff_order i_m)
    finally show "?greatest < ?least" .
  qed

  have zero_ik_interchange: "is_zero_row_upt_k (from_nat i) k ?interchange"
    by (metis (no_types, lifting) interchange_rows_i is_zero_row_upt_k_def zero_least_kA)
  have echelon_form_interchange: "echelon_form_upt_k ?interchange k"
  proof (rule echelon_form_upt_k_interchange[OF e _ A_mk _ k])
    show "is_zero_row_upt_k (from_nat i) k A"
      by (metis (mono_tags) greatest_ge_nonzero_row' Greatest_is_minus_1 Suc_le' 
        a_eq_minus_1 e g_rw i2 row_greater_greatest_is_zero zero_least_kA)
    show "from_nat i \<le> m" using i_m by simp
  qed
  have b_le_i: "b \<le> from_nat i"
  proof (rule ccontr)
    assume "\<not> b \<le> from_nat i"
    hence b_gr_i: "b > from_nat i" by simp
    have "is_zero_row_upt_k b (Suc k) B"
    proof (rule is_zero_row_upt_k_suc)
      show "B $ b $ from_nat k = 0" 
        by (unfold B_eq, rule bezout_iterate_zero_column_k[OF echelon_form_interchange ib 
          interchange_ik_not_zero nrows_less b_gr_i k2 to_nat_b zero_ik_interchange])
      show "is_zero_row_upt_k b k B"
      proof (unfold is_zero_row_upt_k_def, clarify)
        fix j::'cols 
        assume j_k: "to_nat j < k"
        have "B $ b $ j = ?interchange $ b $ j"
        proof (unfold B_eq, rule bezout_iterate_preserves[OF echelon_form_interchange ib 
            interchange_ik_not_zero nrows_less _ to_nat_from_nat_i k2 zero_ik_interchange])
          show "j < from_nat k" by (metis from_nat_mono from_nat_to_nat_id j_k k ncols_def)
        qed
        also have "... = 0"
          by (metis (erased, lifting) b_gr_i echelon_form_interchange echelon_form_upt_k_condition1 
            is_zero_row_upt_k_def j_k zero_ik_interchange)
        finally show "B $ b $ j = 0" .
      qed
    qed
    thus False using not_zero_bB by contradiction
  qed
  hence a_less_i: "a < from_nat i" using ab by simp
  have not_zero_aA: "\<not> is_zero_row_upt_k a k A"
  proof (rule greatest_ge_nonzero_row'[OF e _ not_all_zero])
    show " a \<le> (GREATEST m. \<not> is_zero_row_upt_k m k A)"
      using a_less_i unfolding i2 g_rw
      by (metis le_Suc not_le)
  qed
  have least_eq1:"(LEAST n. B $ a $ n \<noteq> 0) = (LEAST n. A $ a $ n \<noteq> 0)"
  proof (rule Least_equality)
    have "B $ a $ (LEAST n. A $ a $ n \<noteq> 0) = ?interchange $ a $ (LEAST n. A $ a $ n \<noteq> 0)"
    proof (unfold B_eq, rule bezout_iterate_preserves[OF echelon_form_interchange ib 
        interchange_ik_not_zero nrows_less _ to_nat_from_nat_i k2 zero_ik_interchange])
      obtain j::'cols where j: "to_nat j < k" and Aaj: "A $ a $ j \<noteq> 0"
        using not_zero_aA unfolding is_zero_row_upt_k_def by auto
      have "(LEAST n. A $ a $ n \<noteq> 0) \<le> j" by (rule Least_le, simp add: Aaj)
      also have "... < from_nat k"
        by (metis (full_types) from_nat_mono from_nat_to_nat_id j k ncols_def)
      finally show "(LEAST n. A $ a $ n \<noteq> 0) < from_nat k" .      
    qed
    also have "... = A $ a $ (LEAST n. A $ a $ n \<noteq> 0)"
      by (metis (no_types, lifting) ab b_le_i interchange_rows_preserves 
        leD not_zero_aA zero_least_kA)
    also have "... \<noteq> 0"
      by (metis (mono_tags) LeastI is_zero_row_def' is_zero_row_imp_is_zero_row_upt not_zero_aA)
    finally show "B $ a $ (LEAST n. A $ a $ n \<noteq> 0) \<noteq> 0" .
    fix y assume Bay:"B $ a $ y \<noteq> 0"
    show "(LEAST n. A $ a $ n \<noteq> 0) \<le> y"
    proof (cases "y<from_nat k")
      case True
      have "B $ a $ y = ?interchange $ a $ y"
        by (unfold B_eq, rule bezout_iterate_preserves[OF echelon_form_interchange ib
          interchange_ik_not_zero nrows_less True to_nat_from_nat_i k2 zero_ik_interchange])
      also have "... = A $ a $ y"
        by (metis (no_types, lifting) ab b_le_i interchange_rows_preserves 
          leD not_zero_aA zero_least_kA)
      finally have "A $ a $ y \<noteq> 0" using Bay by simp
      thus ?thesis using Least_le by fast
    next
      case False
      obtain j::'cols where j: "to_nat j < k" and Aaj: "A $ a $ j \<noteq> 0"
        using not_zero_aA unfolding is_zero_row_upt_k_def by auto
      have "(LEAST n. A $ a $ n \<noteq> 0) \<le> j" by (rule Least_le, simp add: Aaj)
      also have "... < from_nat k"
        by (metis (full_types) from_nat_mono from_nat_to_nat_id j k ncols_def)
      also have "...\<le> y" using False by auto
      finally show ?thesis by simp
    qed
  qed
  show ?thesis
  proof (cases "b=from_nat i")
    case True
    have zero_bB: "is_zero_row_upt_k b k B"
    proof (unfold is_zero_row_upt_k_def, clarify)
      fix j::'cols assume jk:"to_nat j < k"
      have jk2: "j < from_nat k" by (metis from_nat_mono from_nat_to_nat_id jk k ncols_def)
      have "B $ b $ j = ?interchange $ b $ j"
        by (unfold B_eq, rule bezout_iterate_preserves[OF echelon_form_interchange ib
          interchange_ik_not_zero nrows_less jk2 to_nat_from_nat_i k2 zero_ik_interchange])
      also have "... = A $ ?least $ j" unfolding True by auto
      also have "... = 0" using zero_least_kA jk unfolding is_zero_row_upt_k_def by simp
      finally show "B $ b $ j = 0" .
    qed
    have least_eq2: "(LEAST n. B $ b $ n \<noteq> 0) = from_nat k"
    proof (rule Least_equality)
      show "B $ b $ from_nat k \<noteq> 0"
        unfolding B_eq True
        by (rule bezout_iterate_not_zero[OF interchange_ik_not_zero 
            nrows_less to_nat_from_nat_i ib])
      show "\<And>y. B $ b $ y \<noteq> 0 \<Longrightarrow> from_nat k \<le> y"
        by (metis is_zero_row_upt_k_def le_less_linear to_nat_le zero_bB)
    qed
    obtain j::'cols where j: "to_nat j < k" and Abj: "A $ a $ j \<noteq> 0"
      using not_zero_aA unfolding is_zero_row_upt_k_def by auto
    have "(LEAST n. A $ a $ n \<noteq> 0) \<le> j" by (rule Least_le, simp add: Abj)
    also have "... < from_nat k"
      by (metis (full_types) from_nat_mono from_nat_to_nat_id j k ncols_def)
    finally show ?thesis unfolding least_eq1 least_eq2 .   
  next
    case False note b_not_i=False
    hence b_less_i: "b < from_nat i" using b_le_i by simp
    have not_zero_bA: "\<not> is_zero_row_upt_k b k A"  
    proof (rule greatest_ge_nonzero_row'[OF e _ not_all_zero])
      show " b \<le> (GREATEST m. \<not> is_zero_row_upt_k m k A)"
        using b_less_i unfolding i2 g_rw
        by (metis le_Suc not_le)
    qed
    have least_eq2: "(LEAST n. B $ b $ n \<noteq> 0) = (LEAST n. A $ b $ n \<noteq> 0)"
    proof (rule Least_equality)
      have "B $ b $ (LEAST n. A $ b $ n \<noteq> 0) = ?interchange $ b $ (LEAST n. A $ b $ n \<noteq> 0)"
      proof (unfold B_eq, rule bezout_iterate_preserves[OF echelon_form_interchange ib 
          interchange_ik_not_zero nrows_less _ to_nat_from_nat_i k2 zero_ik_interchange])
        obtain j::'cols where j: "to_nat j < k" and Abj: "A $ b $ j \<noteq> 0"
          using not_zero_bA unfolding is_zero_row_upt_k_def by auto
        have "(LEAST n. A $ b $ n \<noteq> 0) \<le> j" by (rule Least_le, simp add: Abj)
        also have "... < from_nat k"
          by (metis (full_types) from_nat_mono from_nat_to_nat_id j k ncols_def)
        finally show "(LEAST n. A $ b $ n \<noteq> 0) < from_nat k" .      
      qed
      also have "... = A $ b $ (LEAST n. A $ b $ n \<noteq> 0)"
        by (metis (mono_tags) b_not_i interchange_rows_preserves not_zero_bA zero_least_kA)
      also have "... \<noteq> 0"
        by (metis (mono_tags) LeastI is_zero_row_def' is_zero_row_imp_is_zero_row_upt not_zero_bA)
      finally show "B $ b $ (LEAST n. A $ b $ n \<noteq> 0) \<noteq> 0" .     
      fix y assume Bby:"B $ b $ y \<noteq> 0"
      show "(LEAST n. A $ b $ n \<noteq> 0) \<le> y"
      proof (cases "y<from_nat k")
        case True
        have "B $ b $ y = ?interchange $ b $ y"
          by (unfold B_eq, rule bezout_iterate_preserves[OF echelon_form_interchange ib
            interchange_ik_not_zero nrows_less True to_nat_from_nat_i k2 zero_ik_interchange])
        also have "... = A $ b $ y"
          by (metis (mono_tags) b_not_i interchange_rows_preserves not_zero_bA zero_least_kA)
        finally have "A $ b $ y \<noteq> 0" using Bby by simp
        thus ?thesis using Least_le by fast
      next
        case False
        obtain j::'cols where j: "to_nat j < k" and Abj: "A $ b $ j \<noteq> 0"
          using not_zero_bA unfolding is_zero_row_upt_k_def by auto
        have "(LEAST n. A $ b $ n \<noteq> 0) \<le> j" by (rule Least_le, simp add: Abj)
        also have "... < from_nat k"
          by (metis (full_types) from_nat_mono from_nat_to_nat_id j k ncols_def)
        also have "...\<le> y" using False by auto
        finally show ?thesis by simp
      qed
    qed
    show ?thesis
      unfolding least_eq1 least_eq2 
      by (rule echelon_form_upt_k_condition2[OF e ab not_zero_aA not_zero_bA])
  qed 
qed

lemma echelon_echelon_form_column_k:
  fixes A::"'a::{bezout_domain}^'cols::{mod_type}^'rows::{mod_type}" and k bezout
  defines i:"i \<equiv> (if \<forall>m. is_zero_row_upt_k m k A then 0 
  else to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A)) + 1)"
  defines B: "B \<equiv> fst ((echelon_form_of_column_k bezout) (A,i) k)"
  assumes ib: "is_bezout_ext bezout" and e: "echelon_form_upt_k A k" and k: "k<ncols A"
  shows "echelon_form_upt_k B (Suc k)"
  unfolding echelon_form_upt_k_def echelon_form_of_column_k_def Let_def 
proof auto
  fix a b
  let ?B2="(fst (if \<forall>m\<ge>from_nat i. A $ m $ from_nat k = 0 then (A, i)
    else if \<forall>m>from_nat i. A $ m $ from_nat k = 0 then (A, i + 1)
    else (bezout_iterate
    (interchange_rows A (from_nat i) (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n))
    (nrows A - 1) (from_nat i) (from_nat k) bezout, i + 1)))"
  show "is_zero_row_upt_k a (Suc k) B \<Longrightarrow> a < b \<Longrightarrow> is_zero_row_upt_k b (Suc k) B" 
  proof (unfold B echelon_form_of_column_k_def Let_def fst_conv snd_conv, auto)
    assume 1: "is_zero_row_upt_k a (Suc k) A" and 2: "a < b" 
      and 3: "\<forall>m\<ge>from_nat i. A $ m $ from_nat k = 0"
    show "is_zero_row_upt_k b (Suc k) A" by (rule condition1_part1[OF e 1 2 3[unfolded i]])
  next
    assume 1: "is_zero_row_upt_k a (Suc k) A" and 2: "a < b"
      and 3: "i = nrows A " and 4: "\<forall>m>from_nat (nrows A). A $ m $ from_nat k = 0"
    show "is_zero_row_upt_k b (Suc k) A" by (rule condition1_part2[OF e 1 2 3[unfolded i] 4])
  next
    fix m
    assume 1: "is_zero_row_upt_k a (Suc k) ?B2"
      and 2: "a < b" and 3: "\<forall>m>from_nat i. A $ m $ from_nat k = 0"
      and 4: "i \<noteq> nrows A" and 5: "from_nat i \<le> m" 
      and 6: "A $ m $ from_nat k \<noteq> 0" 
    show "is_zero_row_upt_k b (Suc k) A"
      using condition1_part3[OF e ib _ 2 _ _ _ 6]
      using 1 3 4 5 unfolding i echelon_form_of_column_k_def Let_def fst_conv snd_conv by auto
  next
    fix m::'c assume 1: "is_zero_row_upt_k a (Suc k) A" and 2: "i = nrows A"
    show "is_zero_row_upt_k b (Suc k) A" by (rule condition1_part4[OF e 1 2[unfolded i]])
  next
    let ?B2="(fst (if \<forall>m\<ge>from_nat i. A $ m $ from_nat k = 0 then (A, i)
      else if \<forall>m>from_nat i. A $ m $ from_nat k = 0 then (A, i + 1)
      else (bezout_iterate
      (interchange_rows A (from_nat i)
      (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n))
      (nrows A - 1) (from_nat i) (from_nat k) bezout,
      i + 1)))"
    fix m     
    assume 1: "is_zero_row_upt_k a (Suc k) ?B2"                 
      and 2: "a < b"
      and 3: "from_nat i < m"
      and 4: "A $ m $ from_nat k \<noteq> 0"
      and 5: "i \<noteq> nrows A"
    show "is_zero_row_upt_k b (Suc k)
      (bezout_iterate
      (interchange_rows A (from_nat i) (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n))
      (nrows A - Suc 0) (from_nat i) (from_nat k) bezout)" 
      using condition1_part5[OF ib e _ 2 _ 4 _ k]
      using 1 3 5 unfolding i echelon_form_of_column_k_def Let_def fst_conv snd_conv 
      by auto               
  qed
next
  fix a b assume ab: "a < b" and not_zero_aB: "\<not> is_zero_row_upt_k a (Suc k) B" 
    and not_zero_bB: "\<not> is_zero_row_upt_k b (Suc k) B"
  show "(LEAST n. B $ a $ n \<noteq> 0) < (LEAST n. B $ b $ n \<noteq> 0)"
  proof (unfold B echelon_form_of_column_k_def Let_def fst_conv snd_conv, auto)
    assume all_zero: "\<forall>m\<ge>from_nat i. A $ m $ from_nat k = 0"
    show "(LEAST n. A $ a $ n \<noteq> 0) < (LEAST n. A $ b $ n \<noteq> 0)"
      using condition2_part1[OF e ab] not_zero_aB not_zero_bB all_zero
      unfolding B i by simp
  next
    assume 1: "\<forall>m>from_nat (nrows A). A $ m $ from_nat k = 0" and 2: "i = nrows A"
    show "(LEAST n. A $ a $ n \<noteq> 0) < (LEAST n. A $ b $ n \<noteq> 0)"
      using condition2_part2[OF e ab 1] 2 unfolding i by simp
  next
    fix ma
    assume 1: "\<forall>m>from_nat i. A $ m $ from_nat k = 0"
      and 2: "from_nat i \<le> ma" and 3: "A $ ma $ from_nat k \<noteq> 0"
    show "(LEAST n. A $ a $ n \<noteq> 0) < (LEAST n. A $ b $ n \<noteq> 0)"
      using condition2_part3[OF e k ab _ _ _ _ 3] 
      using 1 2 not_zero_aB not_zero_bB unfolding i B
      by auto
  next
    assume "i = nrows A"
    thus "(LEAST n. A $ a $ n \<noteq> 0) < (LEAST n. A $ b $ n \<noteq> 0)"
      using condition2_part4[OF e ab] unfolding i by simp
  next
    let ?B2="bezout_iterate (interchange_rows A (from_nat i) 
      (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n)) 
      (nrows A - Suc 0) (from_nat i) (from_nat k) bezout"
    fix m
    assume 1: "from_nat i < m"
      and 2: "A $ m $ from_nat k \<noteq> 0"
      and 3: "i \<noteq> nrows A"
    have B_eq: "B=?B2" unfolding B echelon_form_of_column_k_def Let_def using 1 2 3 by auto
    show "(LEAST n. ?B2 $ a $ n \<noteq> 0) < (LEAST n. ?B2 $ b $ n \<noteq> 0)"
      using condition2_part5[OF ib e k ab _ _ _ 2] 1 3 not_zero_aB not_zero_bB 
      unfolding i[symmetric] B[symmetric] unfolding B_eq by auto
  qed
qed



lemma echelon_foldl_condition1:
  assumes ib: "is_bezout_ext bezout"
  and "A $ ma $ from_nat (Suc k) \<noteq> 0"
  and k: "k<ncols A"
  shows "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k))
  (bezout_iterate (interchange_rows A 0 (LEAST n. A $ n $ from_nat (Suc k) \<noteq> 0)) 
  (nrows A - Suc 0) 0 (from_nat (Suc k)) bezout)"
proof (rule exI[of _ 0], unfold is_zero_row_upt_k_def, 
    auto, rule exI[of _ "from_nat (Suc k)"], rule conjI)
  show "to_nat (from_nat (Suc k)) < Suc (Suc k)"
    by (metis from_nat_mono from_nat_to_nat_id less_irrefl not_less_eq to_nat_less_card)
  show "bezout_iterate (interchange_rows A 0 (LEAST n. A $ n $ from_nat (Suc k) \<noteq> 0)) 
    (nrows A - Suc 0) 0 (from_nat (Suc k)) bezout $ 0 $ from_nat (Suc k) \<noteq> 0"
  proof (rule bezout_iterate_not_zero[OF _ _ _ ib])
    show "interchange_rows A 0 (LEAST n. A $ n $ from_nat (Suc k) \<noteq> 0) $ 0 $ from_nat (Suc k) \<noteq> 0"
      by (metis (mono_tags, lifting) LeastI_ex assms(2) interchange_rows_i) 
    show "nrows A - Suc 0 < nrows (interchange_rows A 0 (LEAST n. A $ n $ from_nat (Suc k) \<noteq> 0))"
      unfolding nrows_def by simp
    show "to_nat 0 \<le> nrows A - Suc 0" unfolding to_nat_0 nrows_def by simp
  qed
qed

lemma echelon_foldl_condition2:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes n: "\<not> is_zero_row_upt_k ma k A"
  and all_zero: "\<forall>m\<ge> (GREATEST n. \<not> is_zero_row_upt_k n k A)+1. A $ m $ from_nat k = 0"
  shows "(GREATEST n. \<not> is_zero_row_upt_k n k A) = (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A)"
proof (rule Greatest_equality[symmetric])
  show "\<not> is_zero_row_upt_k (GREATEST n. \<not> is_zero_row_upt_k n k A) (Suc k) A"
    by (metis GreatestI_ex n is_zero_row_upt_k_le)
  fix y assume y: "\<not> is_zero_row_upt_k y (Suc k) A"
  show "y \<le> (GREATEST n. \<not> is_zero_row_upt_k n k A)"
  proof (rule ccontr)
    assume " \<not> y \<le> (GREATEST n. \<not> is_zero_row_upt_k n k A)" 
    hence y2: "y > (GREATEST n. \<not> is_zero_row_upt_k n k A)" by simp
    hence "is_zero_row_upt_k y k A" by (metis row_greater_greatest_is_zero)
    moreover have "A $ y $ from_nat k = 0" 
      by (metis (no_types, lifting)  all_zero le_Suc y2) 
    ultimately have "is_zero_row_upt_k y (Suc k) A" by (rule is_zero_row_upt_k_suc)
    thus False using y by contradiction
  qed
qed

lemma echelon_foldl_condition3:
  fixes A::"'a::{bezout_domain}^'cols::{mod_type}^'rows::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  and Am0: "A $ m $ from_nat k \<noteq> 0"
  and all_zero: "\<forall>m. is_zero_row_upt_k m k A"
  and e: "echelon_form_upt_k A k"
  and k: "k < ncols A"
  shows "to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k)
  (bezout_iterate (interchange_rows A 0 (LEAST n. A $ n $ from_nat k \<noteq> 0)) 
  (nrows A - (Suc 0)) 0 (from_nat k) bezout)) = 0"
proof (unfold to_nat_eq_0, rule Greatest_equality)
  let ?interchange="(interchange_rows A 0 (LEAST n. A $ n $ from_nat k \<noteq> 0))"
  let ?b="(bezout_iterate ?interchange (nrows A - (Suc 0)) 0 (from_nat k) bezout)"
  have b0k: "?b $ 0 $ from_nat k \<noteq> 0"
  proof (rule bezout_iterate_not_zero[OF _ _ _ ib])
    show "interchange_rows A 0 (LEAST n. A $ n $ from_nat k \<noteq> 0) $ 0 $ from_nat k \<noteq> 0"
      by (metis (mono_tags, lifting) LeastI Am0 interchange_rows_i)
    show "nrows A - (Suc 0) < nrows (interchange_rows A 0 (LEAST n. A $ n $ from_nat k \<noteq> 0))"
      unfolding nrows_def by simp
    show "to_nat 0 \<le> nrows A - (Suc 0)" unfolding to_nat_0 nrows_def by simp
  qed
  have least_eq: "(LEAST n. A $ n $ from_nat k \<noteq> 0) 
    = (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> 0 \<le> n)"
    by (metis least_mod_type)  
  have all_zero_below: "\<forall>a>0. ?b $ a $ from_nat k = 0"
  proof (auto)
    fix a::'rows
    assume a: "0 < a"
    show "bezout_iterate (interchange_rows A 0 (LEAST n. A $ n $ from_nat k \<noteq> 0)) 
      (nrows A - Suc 0) 0 (from_nat k) bezout $ a $ from_nat k = 0"    
    proof (rule bezout_iterate_zero_column_k[OF _ ib _ _ a])
      show "echelon_form_upt_k (interchange_rows A 0 (LEAST n. A $ n $ from_nat k \<noteq> 0)) k"
      proof(unfold from_nat_0[symmetric] least_eq, 
          rule echelon_form_upt_k_interchange[OF e _ Am0 _ k])
        show "is_zero_row_upt_k (from_nat 0) k A" by (metis all_zero)
        show "from_nat 0 \<le> m" unfolding from_nat_0 by (metis least_mod_type)
      qed
      show "interchange_rows A 0 (LEAST n. A $ n $ from_nat k \<noteq> 0) $ 0 $ from_nat k \<noteq> 0"
        by (metis (mono_tags, lifting) Am0 LeastI interchange_rows_i)
      show "nrows A - Suc 0 < nrows (interchange_rows A 0 (LEAST n. A $ n $ from_nat k \<noteq> 0))"
        unfolding nrows_def by simp
      show "k < ncols (interchange_rows A 0 (LEAST n. A $ n $ from_nat k \<noteq> 0))"
        using k unfolding ncols_def by simp
      show "to_nat a \<le> nrows A - Suc 0"
        by (metis (erased, hide_lams) One_nat_def Suc_leI Suc_le_D diff_Suc_eq_diff_pred 
          not_le nrows_def to_nat_less_card zero_less_diff)
      show "is_zero_row_upt_k 0 k (interchange_rows A 0 (LEAST n. A $ n $ from_nat k \<noteq> 0))"
        by (metis all_zero interchange_rows_i is_zero_row_upt_k_def)
    qed
  qed
  show "\<not> is_zero_row_upt_k 0 (Suc k) ?b"
    by (metis b0k is_zero_row_upt_k_def k lessI ncols_def to_nat_from_nat_id) 
  fix y assume  y: "\<not> is_zero_row_upt_k y (Suc k) ?b"
  show "y \<le> 0"
  proof (rule ccontr)
    assume "\<not> y \<le> 0" hence y2: "y>0" by simp
    have "is_zero_row_upt_k y (Suc k) ?b"
    proof (rule is_zero_row_upt_k_suc)
      show "is_zero_row_upt_k y k ?b"
      proof (unfold is_zero_row_upt_k_def, clarify)
        fix j::'cols assume j: "to_nat j < k"
        have "?b $ y $ j = ?interchange $ y $ j"
        proof (rule bezout_iterate_preserves[OF _ ib])
          show "echelon_form_upt_k ?interchange k" 
          proof (unfold least_eq from_nat_0[symmetric], 
              rule echelon_form_upt_k_interchange[OF e _ Am0 _ k])
            show "is_zero_row_upt_k (from_nat 0) k A"
              by (metis all_zero)
            show "from_nat 0 \<le> m"
              by (metis from_nat_0 least_mod_type)
          qed
          show "?interchange $ 0 $ from_nat k \<noteq> 0"
            by (metis (mono_tags, lifting) Am0 LeastI interchange_rows_i)              
          show "nrows A - Suc 0 < nrows ?interchange" unfolding nrows_def by simp
          show "j < from_nat k" 
            by (metis (full_types) j from_nat_mono from_nat_to_nat_id k ncols_def)
          show "to_nat 0 \<le> nrows A - Suc 0" 
            by (metis le0 to_nat_0)
          show "k < ncols ?interchange" using k unfolding ncols_def by simp
          show "is_zero_row_upt_k 0 k ?interchange"
            by (metis all_zero interchange_rows_i is_zero_row_upt_k_def) 
        qed 
        also have "... = 0"
          by (metis all_zero dual_order.strict_iff_order interchange_rows_j 
            interchange_rows_preserves is_zero_row_upt_k_def j y2)
        finally show "?b $ y $ j = 0" .
      qed
      show "?b $ y $ from_nat k = 0" using all_zero_below using y2 by auto
    qed
    thus False using y by contradiction
  qed
qed


lemma echelon_foldl_condition4:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes all_zero: "\<forall>m>(GREATEST n. \<not> is_zero_row_upt_k n k A)+1.
  A $ m $ from_nat k = 0"
  and greatest_nrows: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
  and le_mb: "(GREATEST n. \<not> is_zero_row_upt_k n k A)+1 \<le> mb"
  and A_mb_k: "A $ mb $ from_nat k \<noteq> 0"
  shows "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) =
  to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A)"
proof -
  let ?greatest = "(GREATEST n. \<not> is_zero_row_upt_k n k A)"
  have mb_eq: "mb=(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" 
    by (metis all_zero le_mb A_mb_k le_less )
  have "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 
    = (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A)"
  proof (rule Greatest_equality[symmetric])
    show "\<not> is_zero_row_upt_k (?greatest + 1) (Suc k) A"
      by (metis (no_types, lifting) A_mb_k is_zero_row_upt_k_def less_Suc_eq less_trans 
        mb_eq not_less_eq to_nat_from_nat_id to_nat_less_card)
    fix y
    assume y: "\<not> is_zero_row_upt_k y (Suc k) A"
    show "y \<le> ?greatest + 1"
    proof (rule ccontr)
      assume "\<not> y \<le> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
      hence y_greatest: "y >  ?greatest + 1" by simp
      have "is_zero_row_upt_k y (Suc k) A"
      proof (rule is_zero_row_upt_k_suc)
        show "is_zero_row_upt_k y k A"
        proof (rule row_greater_greatest_is_zero)
          show "?greatest < y" 
            using y_greatest greatest_nrows unfolding nrows_def
            by (metis Suc_eq_plus1 dual_order.strict_implies_order 
              le_Suc' suc_not_zero to_nat_plus_one_less_card') 
        qed
        show "A $ y $ from_nat k = 0"
          using all_zero y_greatest 
          unfolding from_nat_to_nat_greatest by auto
      qed
      thus False using y by contradiction
    qed
  qed
  thus ?thesis
    by (metis (mono_tags, lifting) Suc_eq_plus1 Suc_lessI add_to_nat_def greatest_nrows 
      nrows_def to_nat_1 to_nat_from_nat_id to_nat_less_card)
qed

lemma echelon_foldl_condition5:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"        
  assumes mb: "\<not> is_zero_row_upt_k mb k A"
  and nrows: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) = nrows A"
  shows "nrows A = Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A))"
  by (metis (no_types, lifting) GreatestI Suc_lessI Suc_less_eq mb nrows from_nat_mono 
    from_nat_to_nat_id is_zero_row_upt_k_le not_greater_Greatest nrows_def to_nat_less_card) 


lemma echelon_foldl_condition6:
  fixes A::"'a::{bezout_ring}^'cols::{mod_type}^'rows::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  and g_mc: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> mc"
  and A_mc_k: "A $ mc $ from_nat k \<noteq> 0"
  shows "\<exists>m. \<not> is_zero_row_upt_k m (Suc k)
  (bezout_iterate (interchange_rows A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)
  (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> n))
  (nrows A - Suc 0) ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) bezout)"
proof -
  let ?greatest="(GREATEST n. \<not> is_zero_row_upt_k n k A)"
  let ?interchange="interchange_rows A (?greatest + 1) 
    (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> ?greatest + 1 \<le> n)"
  let ?B="(bezout_iterate ?interchange (nrows A - Suc 0) (?greatest + 1) (from_nat k) bezout)"
  have "?B $ (?greatest + 1) $ from_nat k \<noteq> 0"
  proof (rule bezout_iterate_not_zero[OF _ _ _ ib])
    show "?interchange $ (?greatest + 1) $ from_nat k \<noteq> 0"
      by (metis (mono_tags, lifting) LeastI_ex g_mc A_mc_k interchange_rows_i)
    show "nrows A - Suc 0 < nrows ?interchange" unfolding nrows_def by simp
    show "to_nat (?greatest + 1) \<le> nrows A - Suc 0" 
      by (metis Suc_pred less_Suc_eq_le nrows_def to_nat_less_card zero_less_card_finite)
  qed
  thus ?thesis 
    by (metis (no_types, lifting) from_nat_mono from_nat_to_nat_id is_zero_row_upt_k_def 
      less_irrefl not_less_eq to_nat_less_card) 
qed


lemma echelon_foldl_condition7:
  fixes A::"'a::{bezout_domain}^'cols::{mod_type}^'rows::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  and e: "echelon_form_upt_k A k"
  and k: "k<ncols A"
  and mb: "\<not> is_zero_row_upt_k mb k A"
  and not_nrows: "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) \<noteq> nrows A"
  and g_mc: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> mc"
  and A_mc_k: "A $ mc $ from_nat k \<noteq> 0"
  shows "Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n k A)) =
  to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (bezout_iterate
  (interchange_rows A ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)
  (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 \<le> n))
  (nrows A - Suc 0) ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) (from_nat k) bezout))"
proof -
  let ?greatest="(GREATEST n. \<not> is_zero_row_upt_k n k A)"
  let ?interchange="interchange_rows A (?greatest + 1) 
    (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> ?greatest + 1 \<le> n)"
  let ?B="(bezout_iterate ?interchange (nrows A - Suc 0) (?greatest + 1) (from_nat k) bezout)"
  have g_rw: "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1 
    = from_nat (to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1))"
    unfolding from_nat_to_nat_id ..
  have B_gk:"?B $ (?greatest + 1) $ from_nat k \<noteq> 0"
  proof (rule bezout_iterate_not_zero[OF _ _ _ ib])
    show "?interchange $ ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) $ from_nat k \<noteq> 0"
      by (metis (mono_tags, lifting) LeastI_ex g_mc A_mc_k interchange_rows_i)      
    show "nrows A - Suc 0 < nrows (?interchange)" unfolding nrows_def by simp
    show "to_nat (?greatest + 1) \<le> nrows A - Suc 0"
      by (metis Suc_pred less_Suc_eq_le nrows_def to_nat_less_card 
        zero_less_card_finite)
  qed
  have "(GREATEST n. \<not> is_zero_row_upt_k n (Suc k) ?B) = ?greatest + 1"
  proof (rule Greatest_equality)
    show "\<not> is_zero_row_upt_k (?greatest + 1) (Suc k) ?B"
      by (metis (no_types, lifting) B_gk from_nat_mono from_nat_to_nat_id 
        is_zero_row_upt_k_def less_irrefl not_less_eq to_nat_less_card)
    fix y
    assume y: "\<not> is_zero_row_upt_k y (Suc k) ?B"
    show "y \<le> ?greatest + 1"
    proof (rule ccontr)
      assume " \<not> y \<le> (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1"
      hence y_gr: " y > (GREATEST n. \<not> is_zero_row_upt_k n k A) + 1" by simp
      hence y_gr2: "y > (GREATEST n. \<not> is_zero_row_upt_k n k A)"
        by (metis (erased, lifting) Suc_eq_plus1 leI le_Suc' less_irrefl less_trans 
          not_nrows nrows_def suc_not_zero to_nat_plus_one_less_card') 
      have echelon_interchange: "echelon_form_upt_k ?interchange k"
      proof (subst (1 2) from_nat_to_nat_id
          [of "(GREATEST n. \<not> is_zero_row_upt_k n k A) + 1", symmetric], 
            rule echelon_form_upt_k_interchange[OF e _ A_mc_k _ k])
        show "is_zero_row_upt_k 
          (from_nat (to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1))) k A"
          by (metis Suc_eq_plus1 Suc_le' g_rw not_nrows nrows_def 
            row_greater_greatest_is_zero suc_not_zero)
        show "from_nat (to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1)) \<le> mc"
          by (metis g_mc g_rw)
      qed        
      have i: "?interchange $ (?greatest + 1) $ from_nat k \<noteq> 0" 
        by (metis (mono_tags, lifting) A_mc_k LeastI_ex g_mc interchange_rows_i)
      have zero_greatest: "is_zero_row_upt_k (?greatest + 1) k A" 
        by (metis Suc_eq_plus1 Suc_le' not_nrows nrows_def 
          row_greater_greatest_is_zero suc_not_zero)
      {
        fix j::'cols assume "to_nat j < k"
        have "?greatest < ?greatest + 1"
          by (metis greatest_less_zero_row e mb zero_greatest) 
        also have "... \<le>(LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (?greatest + 1) \<le> n)"
          by (metis (mono_tags, lifting) A_mc_k LeastI_ex g_mc)
        finally have least_less: "?greatest 
          < (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (?greatest + 1) \<le> n)" .
        have "is_zero_row_upt_k (LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> (?greatest + 1) \<le> n) k A"
          by (rule row_greater_greatest_is_zero[OF least_less])
      }
      hence zero_g1: "is_zero_row_upt_k (?greatest + 1) k ?interchange"
        unfolding is_zero_row_upt_k_def by auto
      hence zero_y: "is_zero_row_upt_k y k ?interchange" 
        by (metis (erased, lifting) echelon_form_upt_k_condition1' echelon_interchange y_gr) 
      have "is_zero_row_upt_k y (Suc k) ?B"
      proof (rule is_zero_row_upt_k_suc)
        show "?B $ y $ from_nat k = 0"
        proof (rule bezout_iterate_zero_column_k[OF echelon_interchange ib i _ y_gr _ _ zero_g1])
          show "nrows A - Suc 0 < nrows ?interchange" unfolding nrows_def by simp
          show "k < ncols ?interchange" using k unfolding ncols_def by simp
          show "to_nat y \<le> nrows A - Suc 0"
            by (metis One_nat_def Suc_eq_plus1 Suc_leI nrows_def 
              le_diff_conv2 to_nat_less_card zero_less_card_finite)            
        qed
        show "is_zero_row_upt_k y k ?B"
        proof (subst is_zero_row_upt_k_def, clarify)
          fix j::'cols assume j: "to_nat j < k"
          have "?B $ y $ j = ?interchange $ y $ j"
          proof (rule bezout_iterate_preserves[OF echelon_interchange ib i _ _ _ _ zero_g1])
            show "nrows A - Suc 0 < nrows ?interchange" unfolding nrows_def by simp
            show "j < from_nat k" using j 
              by (metis (poly_guards_query) from_nat_mono from_nat_to_nat_id k ncols_def)
            show "to_nat ((GREATEST n. \<not> is_zero_row_upt_k n k A) + 1) \<le> nrows A - Suc 0"
              by (metis Suc_pred less_Suc_eq_le nrows_def to_nat_less_card zero_less_card_finite)
            show "k < ncols ?interchange" using k unfolding ncols_def .
          qed
          also have "... = 0" using zero_y unfolding is_zero_row_upt_k_def using j by simp
          finally show "?B $ y $ j = 0" .
        qed
      qed
      thus False using y by contradiction
    qed
  qed
  thus ?thesis
    by (metis (erased, lifting) Suc_eq_plus1 add_to_nat_def not_nrows nrows_def suc_not_zero 
      to_nat_1 to_nat_from_nat_id to_nat_plus_one_less_card')
qed


lemma
  fixes A::"'a::{bezout_domain}^'cols::{mod_type}^'rows::{mod_type}"
  assumes k: "k<ncols A" and ib: "is_bezout_ext bezout"
  shows echelon_echelon_form_of_upt_k:
  "echelon_form_upt_k (echelon_form_of_upt_k A k bezout) (Suc k)"
  and "foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k] =
  (fst (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k]), 
  if \<forall>m. is_zero_row_upt_k m (Suc k) 
  (fst (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k])) then 0
  else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) 
  (fst (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k]))) + 1)"
using k
proof (induct k)
  let ?interchange="interchange_rows A 0 (LEAST n. A $ n $ 0 \<noteq> 0)"
  have i_rw: "(if \<forall>m. is_zero_row_upt_k m 0 A then 0 
    else to_nat (GREATEST n. \<not> is_zero_row_upt_k n 0 A) + 1) = 0"
    unfolding is_zero_row_upt_k_def by auto
  show "echelon_form_upt_k (echelon_form_of_upt_k A 0 bezout) (Suc 0)"
    unfolding echelon_form_of_upt_k_def 
    by (auto, subst i_rw[symmetric], rule echelon_echelon_form_column_k[OF ib echelon_form_upt_k_0], 
      simp add: ncols_def)
  have rw_upt: "[0..<Suc 0] = [0]" by simp
  show "foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc 0] =
    (fst (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc 0]),
    if \<forall>m. is_zero_row_upt_k m (Suc 0) (fst (foldl (echelon_form_of_column_k bezout) 
    (A, 0) [0..<Suc 0])) then 0 else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc 0) 
    (fst (foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc 0]))) + 1)"
    unfolding rw_upt
    unfolding foldl.simps
    unfolding echelon_form_of_column_k_def
    unfolding Let_def 
    unfolding split_beta
    unfolding from_nat_0 fst_conv snd_conv
    unfolding is_zero_row_upt_k_def
    apply (auto simp add: least_mod_type to_nat_eq_0)
    apply (metis (mono_tags, lifting) GreatestI least_mod_type less_le)
  proof -
    fix m mb assume"A $ m $ 0 \<noteq> 0"
      and all_zero: "\<forall>m. bezout_iterate ?interchange (nrows A - Suc 0) 0 0 bezout $ m $ 0 = 0"
    have "bezout_iterate ?interchange (nrows A - Suc 0) 0 0 bezout $ 0 $ 0 = 
      bezout_iterate ?interchange (nrows A - Suc 0) 0 (from_nat 0) bezout $ 0 $ from_nat 0"
      using from_nat_0 by metis 
    also have "... \<noteq> 0" 
    proof (rule bezout_iterate_not_zero[OF _ _ _ ib], simp_all add: nrows_def)
      show "A $ (LEAST n. A $ n $ 0 \<noteq> 0) $ from_nat 0 \<noteq> 0"
        by (metis (mono_tags) LeastI \<open>A $ m $ 0 \<noteq> 0\<close> from_nat_0)
      show "to_nat 0 \<le> CARD('rows) - Suc 0" by (metis le0 to_nat_0)
    qed
    finally have " bezout_iterate ?interchange (nrows A - Suc 0) 0 0 bezout $ 0 $ 0 \<noteq> 0" .
    thus "A $ mb $ 0 = 0" using all_zero by auto
  next
    fix m assume Am0: "A $ m $ 0 \<noteq> 0"
      and all_zero: "\<forall>m>0. A $ m $ 0 = 0" thus "(GREATEST n. A $ n $ 0 \<noteq> 0) = 0"
      by (metis (mono_tags, lifting) GreatestI neq_iff not_less0 to_nat_0 to_nat_mono)
  next
    fix m ma mb
    assume "A $ m $ 0 \<noteq> 0" and "bezout_iterate (interchange_rows A 0 (LEAST n. A $ n $ 0 \<noteq> 0)) 
      (nrows A - Suc 0) 0 0 bezout $ ma $ 0 \<noteq> 0"
    have "bezout_iterate ?interchange (nrows A - Suc 0) 0 0 bezout $ 0 $ 0 = 
      bezout_iterate ?interchange (nrows A - Suc 0) 0 (from_nat 0) bezout $ 0 $ from_nat 0"
      using from_nat_0 by metis 
    also have "... \<noteq> 0" 
    proof (rule bezout_iterate_not_zero[OF _ _ _ ib], simp_all add: nrows_def)
      show "A $ (LEAST n. A $ n $ 0 \<noteq> 0) $ from_nat 0 \<noteq> 0"
        by (metis (mono_tags) LeastI \<open>A $ m $ 0 \<noteq> 0\<close> from_nat_0)
      show "to_nat 0 \<le> CARD('rows) - Suc 0" by (metis le0 to_nat_0)
    qed
    finally have 1: "bezout_iterate ?interchange (nrows A - Suc 0) 0 0 bezout $ 0 $ 0 \<noteq> 0" .
    have 2: "\<forall>m>0. bezout_iterate ?interchange (nrows A - Suc 0) 0 0 bezout $ m $ 0 = 0"
    proof (auto)
      fix b::'rows
      assume b: "0<b" 
      have "bezout_iterate ?interchange (nrows A - Suc 0) 0 0 bezout $ b $ 0 
        = bezout_iterate ?interchange (nrows A - Suc 0) 0 (from_nat 0) bezout $ b $ from_nat 0"
        using from_nat_0 by metis
      also have "... = 0"
      proof (rule bezout_iterate_zero_column_k[OF _ ib])
        show "echelon_form_upt_k (?interchange) 0" by (metis echelon_form_upt_k_0)   
        show "?interchange $ 0 $ from_nat 0 \<noteq> 0" 
          by (metis (mono_tags, lifting) LeastI_ex \<open>A $ m $ 0 \<noteq> 0\<close> from_nat_0 interchange_rows_i)
        show "nrows A - Suc 0 < nrows (?interchange)" unfolding nrows_def by simp
        show "0 < b" using b .
        show "0 < ncols (?interchange)" unfolding ncols_def by auto
        show "to_nat b \<le> nrows A - Suc 0"
          by (metis Suc_eq_plus1 discrete less_one add.left_neutral not_le 
            nrows_def nrows_not_0 le_diff_conv2 to_nat_less_card)
        show "is_zero_row_upt_k 0 0 (?interchange)" by (metis is_zero_row_utp_0)
      qed
      finally show "bezout_iterate (interchange_rows A 0 (LEAST n. A $ n $ 0 \<noteq> 0)) 
        (nrows A - Suc 0) 0 0 bezout $ b $ 0 = 0" .      
    qed
    show "(GREATEST n. bezout_iterate (interchange_rows A 0 (LEAST n. A $ n $ 0 \<noteq> 0)) 
      (nrows A - Suc 0) 0 0 bezout $ n $ 0 \<noteq> 0) = 0" 
      apply (rule Greatest_equality, simp add: 1)
      using 2 by force
  qed
next
  fix k
  let ?fold="(foldl (echelon_form_of_column_k bezout)(A, 0) [0..<Suc (Suc k)])"
  let ?fold2="(foldl (echelon_form_of_column_k bezout) (A, 0) [0..<(Suc k)])"
  assume "(k < ncols A \<Longrightarrow> echelon_form_upt_k (echelon_form_of_upt_k A k bezout) (Suc k))" and
    "(k < ncols A \<Longrightarrow> foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k] =
    (fst ?fold2, if \<forall>m. is_zero_row_upt_k m (Suc k) (fst ?fold2) then 0
    else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (fst ?fold2)) + 1))"
    and Suc_k: "Suc k < ncols A"
  hence hyp_foldl: "foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k] =
    (fst ?fold2, if \<forall>m. is_zero_row_upt_k m (Suc k) (fst ?fold2) then 0
    else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (fst ?fold2)) + 1)" 
    and hyp_echelon: "echelon_form_upt_k (echelon_form_of_upt_k A k bezout) (Suc k)" by auto
  have rw: "[0..<Suc (Suc k)]= [0..<(Suc k)] @ [(Suc k)]" by auto
  have rw2: "?fold2 = (echelon_form_of_upt_k A k bezout, if \<forall>m. is_zero_row_upt_k m (Suc k) 
    (echelon_form_of_upt_k A k bezout) then 0 else
    to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (echelon_form_of_upt_k A k bezout)) + 1)" 
      unfolding echelon_form_of_upt_k_def using hyp_foldl by fast
  show "echelon_form_upt_k (echelon_form_of_upt_k A (Suc k) bezout) (Suc (Suc k))"
    unfolding echelon_form_of_upt_k_def 
    unfolding rw unfolding foldl_append unfolding foldl.simps unfolding rw2
  proof (rule echelon_echelon_form_column_k[OF ib hyp_echelon])
    show "Suc k < ncols (echelon_form_of_upt_k A k bezout)" using Suc_k unfolding ncols_def .
  qed
  show "foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc (Suc k)] =
    (fst ?fold,
    if \<forall>m. is_zero_row_upt_k m (Suc (Suc k)) 
    (fst ?fold) then 0
    else to_nat
    (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) 
    (fst ?fold)) + 1)"
  proof (rule prod_eqI, metis fst_conv)
    define A' where "A' = fst ?fold2"
    let ?greatest="(GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A')"
    have k: "k < ncols A'" using Suc_k unfolding ncols_def by auto
    have k2: "Suc k < ncols A'" using Suc_k unfolding ncols_def by auto
    have fst_snd_foldl: "snd ?fold2 = snd (fst ?fold2,
      if \<forall>m. is_zero_row_upt_k m (Suc k) (fst ?fold2) then 0
      else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc k) (fst ?fold2)) + 1)"
      using hyp_foldl by simp
    have ncols_eq: "ncols A = ncols A'" unfolding A'_def ncols_def ..
    have rref_A': "echelon_form_upt_k A' (Suc k)"
      using hyp_echelon unfolding A'_def echelon_form_of_upt_k_def .
    show "snd ?fold = snd (fst ?fold, if \<forall>m. is_zero_row_upt_k m (Suc (Suc k)) (fst ?fold) then 0
      else to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) (fst ?fold)) + 1)"
        using [[unfold_abs_def = false]]
        unfolding fst_conv snd_conv unfolding rw 
        unfolding foldl_append unfolding foldl.simps
        unfolding echelon_form_of_column_k_def Let_def split_beta fst_snd_foldl 
        unfolding A'_def[symmetric]
      proof (auto simp add: least_mod_type from_nat_0 from_nat_to_nat_greatest)
        fix m assume "A' $ m $ from_nat (Suc k) \<noteq> 0"
        thus "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'" 
          and "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'"
          and "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'"
          and "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'"
          and "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'"
          and "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'"
          and "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'"
          and "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'"
          unfolding is_zero_row_upt_k_def
          by (metis add_to_nat_def from_nat_mono less_irrefl 
            monoid_add_class.add.right_neutral not_less_eq to_nat_0 to_nat_less_card)+
      next
        fix m
        assume "\<not> is_zero_row_upt_k m (Suc k) A'"
        thus "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'" 
          and "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) A'"
          by (metis is_zero_row_upt_k_le)+
      next
        fix m
        assume "\<forall>ma. is_zero_row_upt_k ma (Suc k) A'" and "\<forall>mb. A' $ mb $ from_nat (Suc k) = 0"
        thus "is_zero_row_upt_k m (Suc (Suc k)) A'" 
          by (metis is_zero_row_upt_k_suc)
      next
        fix ma
        assume "\<forall>m>0. A' $ m $ from_nat (Suc k) = 0"
          and "\<forall>m. is_zero_row_upt_k m (Suc k) A'"
          and "\<not> is_zero_row_upt_k ma (Suc (Suc k)) A'" 
        thus "to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A') = 0" 
          and "to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A') = 0"
          by (metis (erased, lifting) GreatestI_ex le_less
            is_zero_row_upt_k_suc least_mod_type to_nat_0)+
      next
        fix m
        assume "\<forall>m>0. A' $ m $ from_nat (Suc k) = 0"
          and "\<not> is_zero_row_upt_k m (Suc k) A'"
          and "\<forall>m\<ge>?greatest+1. A' $ m $ from_nat (Suc k) = 0"
        thus "?greatest 
          = (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A')"
          by (metis (mono_tags, lifting) echelon_form_upt_k_condition1 from_nat_0 
            is_zero_row_upt_k_le is_zero_row_upt_k_suc less_nat_zero_code neq_iff rref_A' to_nat_le)
      next
        fix m ma
        assume "\<forall>m>?greatest+1. 
          A' $ m $ from_nat (Suc k) = 0"
          and "\<forall>m>0. A' $ m $ from_nat (Suc k) = 0"
          and"Suc (to_nat ?greatest) \<noteq> nrows A'"
          and "?greatest + 1 \<le> ma"
          and "A' $ ma $ from_nat (Suc k) \<noteq> 0"
        thus "Suc (to_nat ?greatest) = to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A')"
          by (metis (mono_tags) Suc_eq_plus1 less_linear 
            leD least_mod_type nrows_def suc_not_zero)
      next
        fix m ma
        assume "\<forall>m>?greatest + 1. A' $ m $ from_nat (Suc k) = 0"
          and "\<forall>m>0. A' $ m $ from_nat (Suc k) = 0"
          and "\<not> is_zero_row_upt_k m (Suc k) A'"
          and "Suc (to_nat ?greatest) = nrows A'"
          and "\<not> is_zero_row_upt_k ma (Suc (Suc k)) A'"
        thus "nrows A' = Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A'))"
          by (metis echelon_foldl_condition5)
      next
        fix ma assume 1: "A' $ ma $ from_nat (Suc k) \<noteq> 0"
        show "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k))
          (bezout_iterate (interchange_rows A' 0 (LEAST n. A' $ n $ from_nat (Suc k) \<noteq> 0)) 
          (nrows A' - Suc 0) 0 (from_nat (Suc k)) bezout)"
          and "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k))
          (bezout_iterate (interchange_rows A' 0 (LEAST n. A' $ n $ from_nat (Suc k) \<noteq> 0))
          (nrows A' - Suc 0) 0 (from_nat (Suc k)) bezout)"
          by (rule echelon_foldl_condition1[OF ib 1 k])+
      next
        fix m ma mb
        assume 1: "\<not> is_zero_row_upt_k ma (Suc k) A'"
          and 2:"\<forall>m\<ge>?greatest + 1. A' $ m $ from_nat (Suc k) = 0"
        show "?greatest 
          = (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A')"
          by (rule echelon_foldl_condition2[OF 1 2])
      next
        fix m 
        assume 1: "A' $ m $ from_nat (Suc k) \<noteq> 0"
          and 2: "\<forall>m. is_zero_row_upt_k m (Suc k) A'"
        show "to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k))
          (bezout_iterate (interchange_rows A' 0 (LEAST n. A' $ n $ from_nat (Suc k) \<noteq> 0)) 
          (nrows A' - Suc 0) 0 (from_nat (Suc k)) bezout)) = 0" 
          and "to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k))
          (bezout_iterate (interchange_rows A' 0 (LEAST n. A' $ n $ from_nat (Suc k) \<noteq> 0)) 
          (nrows A' - Suc 0) 0 (from_nat (Suc k)) bezout)) = 0" 
          by (rule echelon_foldl_condition3[OF ib 1 2 rref_A'], metis ncols_def Suc_k)+
      next
        fix m assume "\<forall>m>?greatest + 1. 
          A' $ m $ from_nat (Suc k) = 0"
          and "0 < m"
          and "A' $ m $ from_nat (Suc k) \<noteq> 0"
          and "Suc (to_nat ?greatest) = nrows A'"
        thus "nrows A' = Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A'))" 
          by (metis (mono_tags) Suc_eq_plus1 Suc_le' from_nat_suc 
            from_nat_to_nat_id not_less_eq nrows_def to_nat_less_card to_nat_mono)
      next
        fix mb
        assume 1: "\<forall>m>?greatest+1.
          A' $ m $ from_nat (Suc k) = 0"
          and 2: "Suc (to_nat ?greatest) \<noteq> nrows A'"
          and 3: "?greatest+1 \<le> mb"
          and 4: "A' $ mb $ from_nat (Suc k) \<noteq> 0"
        show "Suc (to_nat ?greatest) =
          to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A')"
          by (rule echelon_foldl_condition4[OF 1 2 3 4])
      next
        fix m
        assume "?greatest + 1 < m"
          and "A' $ m $ from_nat (Suc k) \<noteq> 0"
          and "\<forall>m>0. A' $ m $ from_nat (Suc k) = 0 "
        thus "nrows A' = Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A'))"
          by (metis le_less_trans least_mod_type)
      next
        fix m
        assume "?greatest + 1 < m"
          and "A' $ m $ from_nat (Suc k) \<noteq> 0"
          and "\<forall>m>0. A' $ m $ from_nat (Suc k) = 0"
        thus "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k)) (bezout_iterate
          (interchange_rows A' (?greatest + 1) (LEAST n. A' $ n $ from_nat (Suc k) \<noteq> 0 
          \<and> ?greatest + 1 \<le> n)) (nrows A' - Suc 0) (?greatest + 1) (from_nat (Suc k)) bezout)"
          by (metis le_less_trans least_mod_type)
      next
        fix mb
        assume "\<not> is_zero_row_upt_k mb (Suc k) A'"
          and "Suc (to_nat ?greatest) = nrows A'"
        thus " nrows A' = Suc (to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k)) A'))"
          by (rule echelon_foldl_condition5)
      next
        fix m
        assume "(GREATEST n. \<not> is_zero_row_upt_k n (Suc k) A') + 1 < m"
          and "A' $ m $ from_nat (Suc k) \<noteq> 0"
          and "\<forall>m>0. A' $ m $ from_nat (Suc k) = 0"
        thus "Suc (to_nat ?greatest) =
          to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k))
          (bezout_iterate (interchange_rows A' (?greatest + 1)
          (LEAST n. A' $ n $ from_nat (Suc k) \<noteq> 0 \<and> ?greatest + 1 \<le> n))
          (nrows A' - Suc 0) (?greatest + 1) (from_nat (Suc k)) bezout))"
          by (metis le_less_trans least_mod_type)
      next
        fix mc
        assume "?greatest + 1 \<le> mc"
          and "A' $ mc $ from_nat (Suc k) \<noteq> 0"
        thus "\<exists>m. \<not> is_zero_row_upt_k m (Suc (Suc k))
          (bezout_iterate (interchange_rows A' (?greatest + 1)
          (LEAST n. A' $ n $ from_nat (Suc k) \<noteq> 0 \<and> ?greatest + 1 \<le> n))
          (nrows A' - Suc 0) (?greatest + 1) (from_nat (Suc k)) bezout)"
          using echelon_foldl_condition6[OF ib] by blast
      next
        fix mb mc
        assume 1: "\<not> is_zero_row_upt_k mb (Suc k) A'"
          and 2: "Suc (to_nat ?greatest) \<noteq> nrows A'"
          and 3: "?greatest + 1 \<le> mc"
          and 4:"A' $ mc $ from_nat (Suc k) \<noteq> 0"
        show " Suc (to_nat ?greatest) = to_nat (GREATEST n. \<not> is_zero_row_upt_k n (Suc (Suc k))
          (bezout_iterate (interchange_rows A' (?greatest + 1)
          (LEAST n. A' $ n $ from_nat (Suc k) \<noteq> 0 \<and> ?greatest + 1 \<le> n))
          (nrows A' - Suc 0) (?greatest + 1) (from_nat (Suc k)) bezout))"
          by (rule echelon_foldl_condition7[OF ib rref_A' k2 1 2 3 4 ])
     qed
  qed
qed

subsubsection\<open>Proving the existence of invertible matrices which do the transformations\<close>

lemma bezout_iterate_invertible:
  fixes A::"'a::{bezout_domain}^'cols^'rows::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  assumes "n<nrows A"
  and "to_nat i\<le>n"
  and "A $ i $ j \<noteq> 0"
  shows "\<exists>P. invertible P \<and> P**A = bezout_iterate A n i j bezout"
  using assms
proof (induct n arbitrary: A)
  case 0
  show ?case 
    unfolding bezout_iterate.simps 
    by (simp add: exI[of _ "mat 1"] matrix_mul_lid invertible_def) 
next
  case (Suc n)
  show ?case
  proof (cases "Suc n = to_nat i")
    case True show ?thesis unfolding bezout_iterate.simps using True Suc.prems(1) 
      by (simp add: exI[of _ "mat 1"] matrix_mul_lid invertible_def) 
  next
    case False
    have i_le_n: "to_nat i < Suc n" using Suc.prems(3) False by auto
    let ?B="(bezout_matrix A i (from_nat (Suc n)) j bezout ** A)"
    have b: "bezout_iterate A (Suc n) i j bezout = bezout_iterate ?B n i j bezout"
      unfolding bezout_iterate.simps using i_le_n by auto
    have "\<exists>P. invertible P \<and> P**?B = bezout_iterate ?B n i j bezout"
    proof (rule Suc.hyps[OF ib _])
      show "n < nrows ?B" using Suc.prems (2) unfolding nrows_def by simp
      show "to_nat i \<le> n" using i_le_n by auto
      show "?B $ i $ j \<noteq> 0" 
        by (metis False Suc.prems(2) Suc.prems(4) bezout_matrix_not_zero 
          ib nrows_def to_nat_from_nat_id)
    qed
    from this obtain P where inv_P: "invertible P" and P: "P**?B = bezout_iterate ?B n i j bezout"
      by blast
    show ?thesis
    proof (rule exI[of _ "P ** bezout_matrix A i (from_nat (Suc n)) j bezout"], 
        rule conjI, rule invertible_mult)
      show "P ** bezout_matrix A i (from_nat (Suc n)) j bezout ** A 
        = bezout_iterate A (Suc n) i j bezout" using P unfolding b by (metis matrix_mul_assoc)
      have "det (bezout_matrix A i (from_nat (Suc n)) j bezout) = 1" 
      proof (rule det_bezout_matrix[OF ib])
        show "i < from_nat (Suc n)"
          using i_le_n from_nat_mono[of "to_nat i" "Suc n"] Suc.prems(2)
          unfolding nrows_def by (metis from_nat_to_nat_id)
        show "A $ i $ j \<noteq> 0" by (rule Suc.prems(4))
      qed
      thus "invertible (bezout_matrix A i (mod_type_class.from_nat (Suc n)) j bezout)"
        unfolding invertible_iff_is_unit by simp
      show "invertible P" using inv_P .
    qed
  qed
qed

lemma echelon_form_of_column_k_invertible:
  fixes A::"'a::{bezout_domain}^'cols::{mod_type}^'rows::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  shows "\<exists>P. invertible P \<and> P ** A = fst ((echelon_form_of_column_k bezout) (A,i) k)"  
proof -
  have "\<exists>P. invertible P \<and> P ** A = A" 
    by (simp add: exI[of _ "mat 1"] matrix_mul_lid invertible_def) 
  thus ?thesis
  proof (unfold echelon_form_of_column_k_def Let_def, auto)
    fix P m ma
    let ?least = "(LEAST n. A $ n $ from_nat k \<noteq> 0 \<and> from_nat i \<le> n)"
    let ?interchange ="(interchange_rows A (from_nat i) ?least)"
    assume i: "i \<noteq> nrows A" 
      and i2: "mod_type_class.from_nat i \<le> ma"
      and ma: "A $ ma $ mod_type_class.from_nat k \<noteq> 0"
    have "\<exists>P. invertible P \<and>
      P ** ?interchange =
      bezout_iterate ?interchange (nrows A - Suc 0) (from_nat i) (from_nat k) bezout"
    proof (rule bezout_iterate_invertible[OF ib])
      show "nrows A - Suc 0 < nrows ?interchange" unfolding nrows_def by simp
      show "to_nat (from_nat i::'rows) \<le> nrows A - Suc 0"
        by (metis Suc_leI Suc_le_mono Suc_pred nrows_def to_nat_less_card zero_less_card_finite)
      show "?interchange $ from_nat i $ from_nat k \<noteq> 0" 
        by (metis (mono_tags, lifting) LeastI_ex i2 ma interchange_rows_i)
    qed
    from this obtain P where inv_P: "invertible P" and P: "P ** ?interchange =
      bezout_iterate ?interchange (nrows A - Suc 0) (from_nat i) (from_nat k) bezout"
      by blast
    show "\<exists>P. invertible P \<and> P ** A 
      = bezout_iterate ?interchange (nrows A - Suc 0) (from_nat i) (from_nat k) bezout" 
    proof (rule exI[of _ "P ** interchange_rows (mat 1) (from_nat i) ?least"], 
        rule conjI, rule invertible_mult)
      show "P ** interchange_rows (mat 1) (from_nat i) ?least ** A =
        bezout_iterate ?interchange (nrows A - Suc 0) (from_nat i) (from_nat k) bezout"
        using P by (metis (no_types, lifting) interchange_rows_mat_1 matrix_mul_assoc) 
      show "invertible P" by (rule inv_P)
      show "invertible (interchange_rows (mat 1) (from_nat i) ?least)" 
        by (simp add: invertible_interchange_rows)
    qed
  qed
qed

lemma echelon_form_of_upt_k_invertible:
  fixes A::"'a::{bezout_domain}^'cols::{mod_type}^'rows::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  shows "\<exists>P. invertible P \<and> P**A = (echelon_form_of_upt_k A k bezout)"
proof (induct k)
  case 0
  show ?case
    unfolding echelon_form_of_upt_k_def
    by (simp add: echelon_form_of_column_k_invertible[OF ib])
next
  case (Suc k)
  have set_rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [Suc k]" by simp
  let ?foldl = "foldl (echelon_form_of_column_k bezout) (A, 0) [0..<Suc k]"
  obtain P where invP: "invertible P" 
    and P: "P ** A = fst ?foldl"
    using Suc.hyps unfolding echelon_form_of_upt_k_def by auto
  obtain Q where invQ: "invertible Q" and Q: 
    "Q ** fst ?foldl = fst ((echelon_form_of_column_k bezout) (fst ?foldl, snd ?foldl) (Suc k))"
    using echelon_form_of_column_k_invertible [OF ib] by blast
  show ?case 
  proof (rule exI[of _ "Q**P"], rule conjI)
    show "invertible (Q**P)" by (metis invP invQ invertible_mult)
    show "Q ** P ** A = echelon_form_of_upt_k A (Suc k) bezout"
      unfolding echelon_form_of_upt_k_def 
      unfolding set_rw unfolding foldl_append unfolding foldl.simps
      unfolding matrix_mul_assoc[symmetric]
      unfolding P Q by auto
  qed
qed

subsubsection\<open>Final results\<close>

lemma echelon_form_echelon_form_of:
  fixes A::"'a::{bezout_domain}^'cols::{mod_type}^'rows::{mod_type}"
  assumes ib: "is_bezout_ext bezout"
  shows "echelon_form (echelon_form_of A bezout)"
proof -
  have n: "ncols A - 1 < ncols A" unfolding ncols_def by auto
  show ?thesis
    unfolding echelon_form_def echelon_form_of_def 
    using echelon_echelon_form_of_upt_k[OF n ib]
    unfolding ncols_def by simp
qed

lemma echelon_form_of_invertible:
  fixes A::"'a::{bezout_domain}^'cols::{mod_type}^'rows::{mod_type}"
  assumes ib: "is_bezout_ext (bezout)"
  shows "\<exists>P. invertible P 
            \<and> P ** A = (echelon_form_of A bezout) 
            \<and> echelon_form (echelon_form_of A bezout)"
  using echelon_form_of_upt_k_invertible[OF ib] echelon_form_echelon_form_of[OF ib]
  unfolding echelon_form_of_def by fast

text\<open>Executable version\<close>
 
corollary echelon_form_echelon_form_of_euclidean:
  fixes A::"'a::{euclidean_ring_gcd}^'cols::{mod_type}^'rows::{mod_type}"
  shows "echelon_form (echelon_form_of_euclidean A)"
  using echelon_form_echelon_form_of is_bezout_ext_euclid_ext2 
  unfolding echelon_form_of_euclidean_def
  by auto

corollary echelon_form_of_euclidean_invertible:
  fixes A::"'a::{euclidean_ring_gcd}^'cols::{mod_type}^'rows::{mod_type}"
  shows "\<exists>P. invertible P \<and> P**A = (echelon_form_of A euclid_ext2) 
         \<and> echelon_form (echelon_form_of A euclid_ext2)"
  using echelon_form_of_invertible[OF is_bezout_ext_euclid_ext2] .

subsection\<open>More efficient code equations\<close>

definition
  "echelon_form_of_column_k_efficient bezout A' k =
    (let (A, i) = A';
         from_nat_k = from_nat k;
         from_nat_i = from_nat i;
         all_zero_below_i = (\<forall>m>from_nat_i. A $ m $ from_nat_k = 0)
     in if  (i = nrows A) \<or> (A $ from_nat_i $ from_nat_k = 0) \<and> all_zero_below_i  then (A, i)
           else if all_zero_below_i then (A, i + 1)
           else
            let n = (LEAST n. A $ n $ from_nat_k \<noteq> 0 \<and> from_nat_i \<le> n);
               interchange_A = interchange_rows A (from_nat_i) n
            in
              (bezout_iterate (interchange_A) (nrows A - 1) (from_nat_i) (from_nat_k) bezout, i + 1))"

lemma echelon_form_of_column_k_efficient[code]: 
  "(echelon_form_of_column_k bezout) (A,i) k
    = (echelon_form_of_column_k_efficient bezout) (A,i) k"
  unfolding echelon_form_of_column_k_def echelon_form_of_column_k_efficient_def
  unfolding Let_def by force

end


(*********** Possible future work: ***********)
(* 
  - Other kind of Echelon Forms (minimal Echelon, Howell...) and more applications: 
    ranks, system of equations...

  - Hermite Normal Form and its uniqueness. HNF is unique over PID (not in PIR) with respect to 
    a given complete set of associates and a given complete set of residues.
    In general terms, with the integers we use the positive integers, 
    in F[x] we use monic polynomials...

  - Smith Normal Form and its uniqueness.
*)
