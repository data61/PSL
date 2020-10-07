(*  
    Title:      Rref.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>Reduced row echelon form\<close>

theory Rref
imports
  Rank_Nullity_Theorem.Mod_Type
  Rank_Nullity_Theorem.Miscellaneous
begin

subsection\<open>Defining the concept of Reduced Row Echelon Form\<close>

subsubsection\<open>Previous definitions and properties\<close>
text\<open>This function returns True if each position lesser than k in a column contains a zero.\<close>
definition is_zero_row_upt_k :: "'rows => nat =>'a::{zero}^'columns::{mod_type}^'rows => bool"
  where "is_zero_row_upt_k i k A = (\<forall>j::'columns. (to_nat j) < k \<longrightarrow> A $ i $ j = 0)"

definition is_zero_row :: "'rows =>'a::{zero}^'columns::{mod_type}^'rows => bool"
  where "is_zero_row i A = is_zero_row_upt_k i (ncols A) A"

lemma is_zero_row_upt_ncols:
  fixes A::"'a::{zero}^'columns::{mod_type}^'rows"
  shows "is_zero_row_upt_k i (ncols A) A = (\<forall>j::'columns. A $ i $ j = 0)" unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def by auto

corollary is_zero_row_def':
  fixes A::"'a::{zero}^'columns::{mod_type}^'rows"
  shows "is_zero_row i A = (\<forall>j::'columns. A $ i $ j = 0)" using is_zero_row_upt_ncols unfolding is_zero_row_def ncols_def .

lemma is_zero_row_eq_row_zero: "is_zero_row a A = (row a A = 0)"
  unfolding is_zero_row_def' row_def
  unfolding vec_nth_inverse
  unfolding vec_eq_iff zero_index ..

lemma not_is_zero_row_upt_suc:
  assumes "\<not> is_zero_row_upt_k i (Suc k) A"
  and "\<forall>i. A $ i $ (from_nat k) = 0"
  shows "\<not> is_zero_row_upt_k i k A"
  using assms from_nat_to_nat_id 
  using is_zero_row_upt_k_def less_SucE 
  by metis

lemma is_zero_row_upt_k_suc:
  assumes "is_zero_row_upt_k i k A"
  and "A $ i $ (from_nat k) = 0"
  shows "is_zero_row_upt_k i (Suc k) A"
  using assms unfolding is_zero_row_upt_k_def using less_SucE to_nat_from_nat by metis

lemma is_zero_row_utp_0:
  shows "is_zero_row_upt_k m 0 A" unfolding is_zero_row_upt_k_def by fast

lemma is_zero_row_utp_0':
  shows "\<forall>m. is_zero_row_upt_k m 0 A" unfolding is_zero_row_upt_k_def by fast

lemma is_zero_row_upt_k_le:
  assumes "is_zero_row_upt_k i (Suc k) A"
  shows "is_zero_row_upt_k i k A"
  using assms unfolding is_zero_row_upt_k_def by simp

lemma is_zero_row_imp_is_zero_row_upt:
assumes "is_zero_row i A"
shows "is_zero_row_upt_k i k A"
using assms unfolding  is_zero_row_def is_zero_row_upt_k_def ncols_def by simp

subsubsection\<open>Definition of reduced row echelon form up to a column\<close>

text\<open>This definition returns True if a matrix is in reduced row echelon form up to the column k (not included), otherwise False.\<close>

(*In the third condition, i<i+1 is assumed to avoid that row i can be the last row (in that case, i+1 would be the first row):*)

definition reduced_row_echelon_form_upt_k :: "'a::{zero, one}^'m::{mod_type}^'n::{finite, ord, plus, one} => nat => bool"
  where "reduced_row_echelon_form_upt_k A k = 
  (
    (\<forall>i. is_zero_row_upt_k i k A \<longrightarrow> \<not> (\<exists>j. j>i \<and> \<not> is_zero_row_upt_k j k A)) \<and>
    (\<forall>i. \<not> (is_zero_row_upt_k i k A) \<longrightarrow> A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1) \<and>
    (\<forall>i. i<i+1 \<and> \<not> (is_zero_row_upt_k i k A) \<and> \<not> (is_zero_row_upt_k (i+1) k A) \<longrightarrow> ((LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i+1) $ n \<noteq> 0))) \<and> 
    (\<forall>i. \<not> (is_zero_row_upt_k i k A) \<longrightarrow> (\<forall>j. i \<noteq> j \<longrightarrow> A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0))
  )"


lemma rref_upt_0: "reduced_row_echelon_form_upt_k A 0"
  unfolding reduced_row_echelon_form_upt_k_def is_zero_row_upt_k_def by auto

lemma rref_upt_condition1:
  assumes r: "reduced_row_echelon_form_upt_k A k"
  shows "(\<forall>i. is_zero_row_upt_k i k A \<longrightarrow> \<not> (\<exists>j. j>i \<and> \<not> is_zero_row_upt_k j k A))"
  using r unfolding reduced_row_echelon_form_upt_k_def by simp

lemma rref_upt_condition2:
  assumes r: "reduced_row_echelon_form_upt_k A k"
  shows "(\<forall>i. \<not> (is_zero_row_upt_k i k A) \<longrightarrow> A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1)"
  using r unfolding reduced_row_echelon_form_upt_k_def by simp

lemma rref_upt_condition3:
  assumes r: "reduced_row_echelon_form_upt_k A k"
  shows "(\<forall>i. i<i+1 \<and> \<not> (is_zero_row_upt_k i k A) \<and> \<not> (is_zero_row_upt_k (i+1) k A) \<longrightarrow> ((LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i+1) $ n \<noteq> 0)))"
  using r unfolding reduced_row_echelon_form_upt_k_def by simp

lemma rref_upt_condition4:
  assumes r: "reduced_row_echelon_form_upt_k A k"
  shows " (\<forall>i. \<not> (is_zero_row_upt_k i k A) \<longrightarrow> (\<forall>j. i \<noteq> j \<longrightarrow> A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0))"
  using r unfolding reduced_row_echelon_form_upt_k_def by simp

text\<open>Explicit lemmas for each condition\<close>

lemma rref_upt_condition1_explicit:
assumes "reduced_row_echelon_form_upt_k A k"
and "is_zero_row_upt_k i k A"
and "j>i"
shows "is_zero_row_upt_k j k A"
using assms rref_upt_condition1 by blast

lemma rref_upt_condition2_explicit:
assumes rref_A: "reduced_row_echelon_form_upt_k A k"
and "\<not> is_zero_row_upt_k i k A"
shows "A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1"
using rref_upt_condition2 assms by blast

lemma rref_upt_condition3_explicit:
assumes "reduced_row_echelon_form_upt_k A k"
and "i < i + 1"  
and "\<not> is_zero_row_upt_k i k A"
and "\<not> is_zero_row_upt_k (i + 1) k A "
shows "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)"
using assms rref_upt_condition3 by blast

lemma rref_upt_condition4_explicit:
assumes "reduced_row_echelon_form_upt_k A k"
and "\<not> is_zero_row_upt_k i k A"
and "i \<noteq> j"
shows "A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0"
using assms rref_upt_condition4 by auto

text\<open>Intro lemma and general properties\<close>

lemma reduced_row_echelon_form_upt_k_intro:
  assumes "(\<forall>i. is_zero_row_upt_k i k A \<longrightarrow> \<not> (\<exists>j. j>i \<and> \<not> is_zero_row_upt_k j k A))"
  and "(\<forall>i. \<not> (is_zero_row_upt_k i k A) \<longrightarrow> A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1)"
  and "(\<forall>i. i<i+1 \<and> \<not> (is_zero_row_upt_k i k A) \<and> \<not> (is_zero_row_upt_k (i+1) k A) \<longrightarrow> ((LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i+1) $ n \<noteq> 0)))"
  and "(\<forall>i. \<not> (is_zero_row_upt_k i k A) \<longrightarrow> (\<forall>j. i \<noteq> j \<longrightarrow> A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0))"
  shows "reduced_row_echelon_form_upt_k A k"
  unfolding reduced_row_echelon_form_upt_k_def using assms by fast

lemma rref_suc_imp_rref:
  fixes A::"'a::{semiring_1}^'n::{mod_type}^'m::{mod_type}"
  assumes r: "reduced_row_echelon_form_upt_k A (Suc k)"
  and k_le_card: "Suc k < ncols A"
  shows "reduced_row_echelon_form_upt_k A k"
proof (rule reduced_row_echelon_form_upt_k_intro)
  show "\<forall>i. \<not> is_zero_row_upt_k i k A \<longrightarrow> A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1" 
    using rref_upt_condition2[OF r] less_SucI unfolding is_zero_row_upt_k_def by blast
  show "\<forall>i. i < i + 1 \<and> \<not> is_zero_row_upt_k i k A \<and> \<not> is_zero_row_upt_k (i + 1) k A \<longrightarrow> (LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)"
    using rref_upt_condition3[OF r] less_SucI unfolding is_zero_row_upt_k_def by blast
  show "\<forall>i. \<not> is_zero_row_upt_k i k A \<longrightarrow> (\<forall>j. i \<noteq> j \<longrightarrow> A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0)"
    using rref_upt_condition4[OF r] less_SucI unfolding is_zero_row_upt_k_def by blast
  show "\<forall>i. is_zero_row_upt_k i k A \<longrightarrow> \<not> (\<exists>j>i. \<not> is_zero_row_upt_k j k A)"
  proof (clarify, rule ccontr)
    fix i j
    assume zero_i: "is_zero_row_upt_k i k A"
      and i_less_j: "i < j"
      and not_zero_j: "\<not> is_zero_row_upt_k j k A"
    have not_zero_j_suc: "\<not> is_zero_row_upt_k j (Suc k) A"
      using not_zero_j unfolding is_zero_row_upt_k_def by fastforce
    hence not_zero_i_suc: "\<not> is_zero_row_upt_k i (Suc k) A"
      using rref_upt_condition1[OF r] i_less_j by fast
    have not_zero_i_plus_suc: "\<not> is_zero_row_upt_k (i+1) (Suc k) A"
    proof (cases "j=i+1")
      case True thus ?thesis using not_zero_j_suc by simp
    next
      case False
      have "i+1<j" by (rule Suc_less[OF i_less_j False[symmetric]])
      thus ?thesis  using rref_upt_condition1[OF r] not_zero_j_suc by blast
    qed
    from this obtain n where a: "A $ (i+1) $ n \<noteq> 0" and n_less_suc: "to_nat n < Suc k"
      unfolding is_zero_row_upt_k_def by blast
    have "(LEAST n. A $ (i+1) $ n \<noteq> 0) \<le> n" by (rule Least_le, simp add: a)
    also have "... \<le> from_nat k" by (metis Suc_lessD from_nat_mono' from_nat_to_nat_id k_le_card less_Suc_eq_le n_less_suc ncols_def)
    finally have least_le: "(LEAST n. A $ (i + 1) $ n \<noteq> 0) \<le> from_nat k" .
    have least_eq_k: "(LEAST n. A $ i $ n \<noteq> 0) = from_nat k"
    proof (rule Least_equality)
      show "A $ i $ from_nat k \<noteq> 0" using not_zero_i_suc zero_i unfolding is_zero_row_upt_k_def by (metis from_nat_to_nat_id less_SucE)
      show "\<And>y. A $ i $ y \<noteq> 0 \<Longrightarrow> from_nat k \<le> y" by (metis is_zero_row_upt_k_def not_le_imp_less to_nat_le zero_i)
    qed
    have i_less: "i<i+1"
    proof (rule Suc_le', rule ccontr)
      assume "\<not> i + 1 \<noteq> 0" hence "i+1=0" by simp
      hence "i=-1" using diff_0 diff_add_cancel diff_minus_eq_add by metis
      hence "j <= i" using Greatest_is_minus_1 by blast
      thus False using i_less_j by fastforce
    qed
    have "from_nat k < (LEAST n. A $ (i+1) $ n \<noteq> 0)"
      using rref_upt_condition3[OF r] i_less not_zero_i_suc not_zero_i_plus_suc least_eq_k by fastforce
    thus False using least_le by simp
  qed
qed

lemma reduced_row_echelon_if_all_zero:
  assumes all_zero: "\<forall>n. is_zero_row_upt_k n k A"
  shows "reduced_row_echelon_form_upt_k A k"
  using assms unfolding reduced_row_echelon_form_upt_k_def is_zero_row_upt_k_def by auto

subsubsection\<open>The definition of reduced row echelon form\<close>

text\<open>Definition of reduced row echelon form, based on \<open>reduced_row_echelon_form_upt_k_def\<close>\<close>
definition reduced_row_echelon_form :: "'a::{zero, one}^'m::{mod_type}^'n::{finite, ord, plus, one} => bool"
  where "reduced_row_echelon_form A = reduced_row_echelon_form_upt_k A (ncols A)"

text\<open>Equivalence between our definition of reduced row echelon form and the one presented
in Steven Roman's book: Advanced Linear Algebra.\<close>

lemma reduced_row_echelon_form_def': 
"reduced_row_echelon_form A = 
  (
    (\<forall>i. is_zero_row i A \<longrightarrow> \<not> (\<exists>j. j>i \<and> \<not> is_zero_row j A)) \<and>
    (\<forall>i. \<not> (is_zero_row i A) \<longrightarrow> A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1) \<and>
    (\<forall>i. i<i+1 \<and> \<not> (is_zero_row i A) \<and> \<not> (is_zero_row (i+1) A) \<longrightarrow> ((LEAST k. A $ i $ k \<noteq> 0) < (LEAST k. A $ (i+1) $ k \<noteq> 0))) \<and>
    (\<forall>i. \<not> (is_zero_row i A) \<longrightarrow> (\<forall>j. i \<noteq> j \<longrightarrow> A $ j $ (LEAST k. A $ i $ k \<noteq> 0) = 0))
  )" unfolding reduced_row_echelon_form_def reduced_row_echelon_form_upt_k_def is_zero_row_def ..

subsection\<open>Properties of the reduced row echelon form of a matrix\<close>

lemma rref_condition1:
  assumes r: "reduced_row_echelon_form A"
  shows "(\<forall>i. is_zero_row i A \<longrightarrow> \<not> (\<exists>j. j>i \<and> \<not> is_zero_row j A))" using r unfolding reduced_row_echelon_form_def' by simp

lemma rref_condition2:
  assumes r: "reduced_row_echelon_form A"
  shows " (\<forall>i. \<not> (is_zero_row i A) \<longrightarrow> A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1)" using r unfolding reduced_row_echelon_form_def' by simp

lemma rref_condition3:
  assumes r: "reduced_row_echelon_form A"
  shows "(\<forall>i. i<i+1 \<and> \<not> (is_zero_row i A) \<and> \<not> (is_zero_row (i+1) A) \<longrightarrow> ((LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i+1) $ n \<noteq> 0)))"
  using r unfolding reduced_row_echelon_form_def' by simp

lemma rref_condition4:
  assumes r: "reduced_row_echelon_form A"
  shows " (\<forall>i. \<not> (is_zero_row i A) \<longrightarrow> (\<forall>j. i \<noteq> j \<longrightarrow> A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0))"
  using r unfolding reduced_row_echelon_form_def' by simp

text\<open>Explicit lemmas for each condition\<close>

lemma rref_condition1_explicit:
assumes rref_A: "reduced_row_echelon_form A"
and "is_zero_row i A" 
shows "\<forall>j>i. is_zero_row j A"
using rref_condition1 assms by blast

lemma rref_condition2_explicit:
assumes rref_A: "reduced_row_echelon_form A"
and "\<not> is_zero_row i A"
shows "A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1"
using rref_condition2 assms by blast

lemma rref_condition3_explicit:
assumes rref_A: "reduced_row_echelon_form A"
and i_le: "i < i + 1"
and "\<not> is_zero_row i A" and "\<not> is_zero_row (i + 1) A"
shows "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)"
using rref_condition3 assms by blast

lemma rref_condition4_explicit:
assumes rref_A: "reduced_row_echelon_form A"
and "\<not> is_zero_row i A" 
and "i \<noteq> j"
shows "A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0"
using rref_condition4 assms by blast

text\<open>Other properties and equivalences\<close>

lemma rref_condition3_equiv1:
fixes A::"'a::{one, zero}^'cols::{mod_type}^'rows::{mod_type}"
assumes rref: "reduced_row_echelon_form A"
and i_less_j: "i<j"
and j_less_nrows: "j<nrows A"
and not_zero_i: "\<not> is_zero_row (from_nat i) A"
and not_zero_j: "\<not> is_zero_row (from_nat j) A"
shows "(LEAST n. A $ (from_nat i) $ n \<noteq> 0) < (LEAST n. A $ (from_nat j) $ n \<noteq> 0)"
using i_less_j not_zero_j j_less_nrows
proof (induct j)
case 0
show ?case using "0.prems"(1) by simp
next
fix j
assume hyp: "i < j \<Longrightarrow> \<not> is_zero_row (from_nat j) A \<Longrightarrow> j < nrows A \<Longrightarrow> (LEAST n. A $ from_nat i $ n \<noteq> 0) < (LEAST n. A $ from_nat j $ n \<noteq> 0)"
and i_less_suc_j: "i < Suc j"
and not_zero_suc_j: "\<not> is_zero_row (from_nat (Suc j)) A"
and Suc_j_less_nrows: "Suc j < nrows A"
have j_less: "(from_nat j::'rows) < from_nat (j+1)" by (rule from_nat_mono, auto simp add: Suc_j_less_nrows[unfolded nrows_def])
hence not_zero_j: "\<not> is_zero_row (from_nat j) A" using rref_condition1[OF rref] not_zero_suc_j unfolding Suc_eq_plus1 by blast
show "(LEAST n. A $ from_nat i $ n \<noteq> 0) < (LEAST n. A $ from_nat (Suc j) $ n \<noteq> 0)"
proof (cases "i=j")
case True 
show ?thesis 
 proof (unfold True Suc_eq_plus1 from_nat_suc, rule rref_condition3_explicit)
     show "reduced_row_echelon_form A" using rref .
     show "(from_nat j::'rows) < from_nat j + 1" using j_less unfolding from_nat_suc .
     show "\<not> is_zero_row (from_nat j) A" using not_zero_j .
     show "\<not> is_zero_row (from_nat j + 1) A" using not_zero_suc_j unfolding Suc_eq_plus1 from_nat_suc .
  qed
next
case False 
have "(LEAST n. A $ from_nat i $ n \<noteq> 0) < (LEAST n. A $ from_nat j $ n \<noteq> 0)"
  proof (rule hyp)
     show "i < j" using False i_less_suc_j by simp
     show "\<not> is_zero_row (from_nat j) A" using not_zero_j .
     show "j < nrows A" using Suc_j_less_nrows by simp
  qed
also have "... < (LEAST n. A $ from_nat (j+1) $ n \<noteq> 0)"
  proof (unfold from_nat_suc, rule rref_condition3_explicit)
     show "reduced_row_echelon_form A" using rref .
     show "(from_nat j::'rows) < from_nat j + 1" using j_less unfolding from_nat_suc .
     show "\<not> is_zero_row (from_nat j) A" using not_zero_j .
     show "\<not> is_zero_row (from_nat j + 1) A" using not_zero_suc_j unfolding Suc_eq_plus1 from_nat_suc .
  qed
finally show "(LEAST n. A $ from_nat i $ n \<noteq> 0) < (LEAST n. A $ from_nat (Suc j) $ n \<noteq> 0)" unfolding Suc_eq_plus1 .
qed 
qed

corollary rref_condition3_equiv:
fixes A::"'a::{one, zero}^'cols::{mod_type}^'rows::{mod_type}"
assumes rref: "reduced_row_echelon_form A"
and i_less_j: "i<j"
and i: "\<not> is_zero_row i A"
and j: "\<not> is_zero_row j A"
shows "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)"
proof (rule rref_condition3_equiv1[of A "to_nat i" "to_nat j", unfolded from_nat_to_nat_id])
 show "reduced_row_echelon_form A" using rref .
 show "to_nat i < to_nat j" by (rule to_nat_mono[OF i_less_j])
 show "to_nat j < nrows A" using to_nat_less_card unfolding nrows_def .
 show "\<not> is_zero_row i A" using i .
 show "\<not> is_zero_row j A" using j .
qed


lemma rref_implies_rref_upt:
fixes A::"'a::{one,zero}^'cols::{mod_type}^'rows::{mod_type}"
assumes rref: "reduced_row_echelon_form A"
shows "reduced_row_echelon_form_upt_k A k"
proof (rule reduced_row_echelon_form_upt_k_intro)
  show "\<forall>i. \<not> is_zero_row_upt_k i k A \<longrightarrow> A $ i $ (LEAST k. A $ i $ k \<noteq> 0) = 1"
    using rref_condition2[OF rref] is_zero_row_imp_is_zero_row_upt by blast
  show "\<forall>i. i < i + 1 \<and> \<not> is_zero_row_upt_k i k A \<and> \<not> is_zero_row_upt_k (i + 1) k A \<longrightarrow> (LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ (i + 1) $ n \<noteq> 0)"
    using rref_condition3[OF rref] is_zero_row_imp_is_zero_row_upt by blast
  show "\<forall>i. \<not> is_zero_row_upt_k i k A \<longrightarrow> (\<forall>j. i \<noteq> j \<longrightarrow> A $ j $ (LEAST n. A $ i $ n \<noteq> 0) = 0)"
    using rref_condition4[OF rref] is_zero_row_imp_is_zero_row_upt by blast
show "\<forall>i. is_zero_row_upt_k i k A \<longrightarrow> \<not> (\<exists>j>i. \<not> is_zero_row_upt_k j k A)"
proof (auto, rule ccontr)
fix i j assume zero_i_k: "is_zero_row_upt_k i k A" and i_less_j: "i < j"
and not_zero_j_k:"\<not> is_zero_row_upt_k j k A"
have not_zero_j: "\<not> is_zero_row j A" using is_zero_row_imp_is_zero_row_upt not_zero_j_k by blast
hence not_zero_i: "\<not> is_zero_row i A" using rref_condition1[OF rref] i_less_j by blast
have Least_less: "(LEAST n. A $ i $ n \<noteq> 0) < (LEAST n. A $ j $ n \<noteq> 0)" by (rule rref_condition3_equiv[OF rref i_less_j not_zero_i not_zero_j])
moreover have "(LEAST n. A $ j $ n \<noteq> 0) < (LEAST n. A $ i $ n \<noteq> 0)"
  proof (rule LeastI2_ex)   
     show "\<exists>a. A $ i $ a \<noteq> 0" using not_zero_i unfolding is_zero_row_def is_zero_row_upt_k_def by fast
     fix x assume Aix_not_0: "A $ i $ x \<noteq> 0"
     have k_less_x: "k \<le> to_nat x"  using zero_i_k Aix_not_0 unfolding is_zero_row_upt_k_def by force
     hence k_less_ncols: "k < ncols A" unfolding ncols_def using to_nat_less_card[of x] by simp
     obtain s where Ajs_not_zero: "A $ j $ s \<noteq> 0" and s_less_k: "to_nat s < k" using not_zero_j_k unfolding is_zero_row_upt_k_def by blast
     have "(LEAST n. A $ j $ n \<noteq> 0) \<le> s" using Ajs_not_zero Least_le by fast
     also have "... = from_nat (to_nat s)" unfolding from_nat_to_nat_id ..
     also have "... < from_nat k" by (rule from_nat_mono[OF s_less_k k_less_ncols[unfolded ncols_def]])
     also have "... \<le> x" using k_less_x leD not_le_imp_less to_nat_le by fast
     finally show "(LEAST n. A $ j $ n \<noteq> 0) < x" .
  qed
ultimately show False by fastforce
qed
qed


lemma rref_first_position_zero_imp_column_0:
fixes A::"'a::{one,zero}^'cols::{mod_type}^'rows::{mod_type}"
assumes rref: "reduced_row_echelon_form A"
and A_00: "A $ 0 $ 0 = 0"
shows "column 0 A = 0"
proof (unfold column_def, vector, clarify)
fix i
have "is_zero_row_upt_k 0 1 A" unfolding is_zero_row_upt_k_def using A_00 by (metis One_nat_def less_Suc0 to_nat_eq_0)
hence "is_zero_row_upt_k i 1 A" using rref_upt_condition1[OF rref_implies_rref_upt[OF rref]] using least_mod_type less_le by metis
thus "A $ i $ 0 = 0" unfolding is_zero_row_upt_k_def using to_nat_eq_0 by blast
qed


lemma rref_first_element:
fixes A::"'a::{one,zero}^'cols::{mod_type}^'rows::{mod_type}"
assumes rref: "reduced_row_echelon_form A"
and column_not_0: "column 0 A \<noteq> 0"
shows "A $ 0 $ 0 = 1"
proof (rule ccontr)
have A_00_not_0: "A $ 0 $ 0 \<noteq> 0"
  proof (rule ccontr, simp)
    assume A_00: "A $ 0 $ 0 = 0"
    from this obtain i where Ai0: "A $ i $ 0 \<noteq> 0" and i: "i>0" using column_not_0 unfolding column_def by (metis column_def rref rref_first_position_zero_imp_column_0)
    have "is_zero_row_upt_k 0 1 A" unfolding is_zero_row_upt_k_def using A_00 by (metis One_nat_def less_Suc0 to_nat_eq_0)
    moreover have "\<not> is_zero_row_upt_k i 1 A" using Ai0 by (metis is_zero_row_upt_k_def to_nat_0 zero_less_one)
    ultimately have "\<not> reduced_row_echelon_form A" by (metis A_00 column_not_0 rref_first_position_zero_imp_column_0)
    thus False using rref by contradiction
qed
assume A_00_not_1: "A $ 0 $ 0 \<noteq> 1"
have Least_eq_0: "(LEAST n. A $ 0 $ n \<noteq> 0) = 0"
  proof (rule Least_equality)
     show "A $ 0 $ 0 \<noteq> 0" by (rule A_00_not_0)
     show "\<And>y. A $ 0 $ y \<noteq> 0 \<Longrightarrow> 0 \<le> y" using least_mod_type .
  qed
moreover have "\<not> is_zero_row 0 A" unfolding is_zero_row_def is_zero_row_upt_k_def ncols_def using A_00_not_0 by auto
ultimately have "A $ 0 $ (LEAST n. A $ 0 $ n \<noteq> 0) = 1" using rref_condition2[OF rref] by fast
thus False unfolding Least_eq_0 using A_00_not_1 by contradiction
qed

end
