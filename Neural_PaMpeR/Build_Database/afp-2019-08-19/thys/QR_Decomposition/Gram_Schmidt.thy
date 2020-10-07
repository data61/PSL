(*  
    Title:      Gram_Schmidt.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>The Gram-Schmidt algorithm\<close>

theory Gram_Schmidt
imports
 Miscellaneous_QR
 Projections
begin

subsection\<open>Gram-Schmidt algorithm\<close>

text\<open>
The algorithm is used to orthogonalise a set of vectors. The Gram-Schmidt process takes a set of vectors \<open>S\<close>
and generates another orthogonal set that spans the same subspace as \<open>S\<close>.

We present three ways to compute the Gram-Schmidt algorithm.

\begin{enumerate}
\item The fist one has been developed thinking about the simplicity of its formalisation.
    Given a list of vectors, the output is another list of orthogonal vectors with the same span.
    Such a list is constructed following the Gram-Schmidt process presented in any book, but in 
    the reverse order (starting the process from the last element of the input list).

\item Based on previous formalization, another function has been defined
  to compute the process of the Gram-Schmidt algorithm in the natural order 
  (starting from the first element of the input list).

\item The third way has as input and output a matrix. The algorithm is applied to the columns of a
  matrix, obtaining a matrix whose columns are orthogonal and where the column space is kept. 
  This will be a previous step to compute the QR decomposition.
\end{enumerate}

Every function can be executed with arbitrary precision (using rational numbers).
\<close>

subsubsection\<open>First way\<close>

definition Gram_Schmidt_step :: "('a::{real_inner}^'b) => ('a^'b) list => ('a^'b) list"
  where "Gram_Schmidt_step a ys = ys @ [(a - proj_onto a (set ys))]"

definition "Gram_Schmidt xs = foldr Gram_Schmidt_step xs []"

lemma Gram_Schmidt_cons:
  "Gram_Schmidt (a#xs) = Gram_Schmidt_step a (Gram_Schmidt xs)"
  unfolding Gram_Schmidt_def by auto

lemma basis_orthogonal':
  fixes xs::"('a::{real_inner}^'b) list"
  shows "length (Gram_Schmidt xs) = length (xs) \<and>
        span (set (Gram_Schmidt xs)) = span (set xs) \<and>
        pairwise orthogonal (set (Gram_Schmidt xs))"
proof (induct xs)
  case Nil
  show ?case unfolding Gram_Schmidt_def pairwise_def by fastforce
next
  case (Cons a xs)
  have l: "length (Gram_Schmidt xs) = length xs"
    and s: "span (set (Gram_Schmidt xs)) = span (set xs)"
    and p: "pairwise orthogonal (set (Gram_Schmidt xs))" using Cons.hyps by auto
  show "length (Gram_Schmidt (a # xs)) = length (a # xs) \<and>
    span (set (Gram_Schmidt (a # xs))) = span (set (a # xs))
    \<and> pairwise orthogonal (set (Gram_Schmidt (a # xs)))"
  proof 
    show "length (Gram_Schmidt (a # xs)) = length (a # xs)"
      unfolding Gram_Schmidt_cons unfolding Gram_Schmidt_step_def using l by auto 
    show "span (set (Gram_Schmidt (a # xs))) 
      = span (set (a # xs)) \<and> pairwise orthogonal (set (Gram_Schmidt (a # xs)))"
    proof
      have set_rw1: "set (a # xs) = insert a (set xs)" by simp
      have set_rw2: "set (Gram_Schmidt (a # xs)) 
        = (insert (a - (\<Sum>x\<in>set (Gram_Schmidt xs). (a \<bullet> x / (x \<bullet> x)) *\<^sub>R x)) (set (Gram_Schmidt xs)))"
        unfolding Gram_Schmidt_cons Gram_Schmidt_step_def proj_onto_def proj_def[abs_def] by auto
      define C where "C = set (Gram_Schmidt xs)"
      have finite_C: "finite C" unfolding C_def by auto
      {   
        fix x k
        have th0: "!!(a::'a^'b) b c. a - (b - c) = c + (a - b)"
          by (simp add: field_simps)
        have "x - k *\<^sub>R (a - (\<Sum>x\<in>C. (a \<bullet> x / (x \<bullet>  x)) *\<^sub>R x)) \<in> span C 
          \<longleftrightarrow> x - k *\<^sub>R a \<in> span C"
          apply (simp only: scaleR_right_diff_distrib th0)
          apply (rule span_add_eq)
          apply (rule span_mul)
          apply (rule span_sum)
          apply (rule span_mul)
          apply (rule span_base)
          apply assumption
          done
      }
      then show "span (set (Gram_Schmidt (a # xs))) = span (set (a # xs))"
        unfolding set_eq_iff set_rw2 set_rw1 span_breakdown_eq C_def s[symmetric]
        by auto
      with p show "pairwise orthogonal (set (Gram_Schmidt (a # xs)))"
        using pairwise_orthogonal_proj_set[OF finite_C]
        unfolding set_rw2 unfolding C_def proj_def[symmetric] proj_onto_def[symmetric] by simp
    qed
  qed
qed


lemma card_Gram_Schmidt:
  fixes xs::"('a::{real_inner}^'b) list"
  assumes "distinct xs"
  shows "card(set (Gram_Schmidt xs)) \<le> card (set (xs))"
  using assms
proof (induct xs)
  case Nil show ?case unfolding Gram_Schmidt_def by simp
next
  case (Cons x xs)
  define b where "b = (\<Sum>xa\<in>set (Gram_Schmidt xs). (x \<bullet> xa / (xa \<bullet> xa)) *\<^sub>R xa)"
  have distinct_xs: "distinct xs" using Cons.prems by auto
  show ?case
  proof (cases "x - b \<notin> set (Gram_Schmidt xs)")
    case True
    have "card (set (Gram_Schmidt (x # xs))) = card (insert (x - b) (set (Gram_Schmidt xs)))"
      unfolding Gram_Schmidt_cons Gram_Schmidt_step_def b_def 
      unfolding proj_onto_def proj_def[abs_def] by simp
    also have "... = Suc (card (set (Gram_Schmidt xs)))"
    proof (rule card_insert_disjoint)
      show "finite (set (Gram_Schmidt xs))" by simp
      show "x - b \<notin> set (Gram_Schmidt xs)" using True .
    qed
    also have "... \<le> Suc (card (set xs))" using Cons.hyps[OF distinct_xs]  by simp
    also have "... = Suc (length (remdups xs))" unfolding List.card_set ..
    also have "... \<le> (length (remdups (x # xs)))"
      by (metis Cons.prems distinct_xs impossible_Cons not_less_eq_eq remdups_id_iff_distinct)
    also have "... \<le> (card (set (x # xs)))" 
      by (metis dual_order.refl length_remdups_card_conv)
    finally show ?thesis .
  next
    case False
    have x_b_in: "x - b \<in> set (Gram_Schmidt xs)" using False by simp
    have "card (set (Gram_Schmidt (x # xs))) = card (insert (x - b) (set (Gram_Schmidt xs)))"
      unfolding Gram_Schmidt_cons Gram_Schmidt_step_def b_def
      unfolding proj_onto_def proj_def[abs_def] by simp
    also have "... = (card (set (Gram_Schmidt xs)))" by (metis False insert_absorb)
    also have "... \<le> (card (set xs))" using Cons.hyps[OF distinct_xs] .
    also have "... \<le> (card (set (x # xs)))" unfolding List.card_set by simp
    finally show ?thesis .
  qed
qed

lemma orthogonal_basis_exists:
  fixes V :: "(real^'b) list"
  assumes B: "is_basis (set V)"
  and d: "distinct V"
  shows "vec.independent (set (Gram_Schmidt V)) \<and> (set V) \<subseteq> vec.span (set (Gram_Schmidt V)) 
  \<and> (card (set (Gram_Schmidt V)) = vec.dim (set V)) \<and> pairwise orthogonal (set (Gram_Schmidt V))"
proof -
  have "(set V) \<subseteq> vec.span (set (Gram_Schmidt V))"
    using basis_orthogonal'[of V]
    using vec.span_superset[where ?'a=real, where ?'b='b]
    by (auto simp: span_vec_eq)
  moreover have "pairwise orthogonal (set (Gram_Schmidt V))"
    using basis_orthogonal'[of V] by blast
  moreover have c: "(card (set (Gram_Schmidt V)) = vec.dim (set V))"
  proof -
    have card_eq_dim: "card (set V) = vec.dim (set V)" 
      by (metis B independent_is_basis vec.dim_span vec.indep_card_eq_dim_span)
    have "vec.dim (set V) \<le> (card (set (Gram_Schmidt V)))" using B unfolding is_basis_def
      using vec.independent_span_bound[of "(set (Gram_Schmidt V))" "set V"]
      using basis_orthogonal'[of V]
      by (simp add: calculation(1) local.card_eq_dim)
    moreover have "(card (set (Gram_Schmidt V))) \<le> vec.dim (set V)"
      using card_Gram_Schmidt[OF d] card_eq_dim by auto
    ultimately show ?thesis by auto
  qed
  moreover have "vec.independent (set (Gram_Schmidt V))"
  proof (rule vec.card_le_dim_spanning[of _ "UNIV::(real^'b) set"])
    show "set (Gram_Schmidt V) \<subseteq> (UNIV::(real^'b) set)" by simp
    show "UNIV \<subseteq> vec.span (set (Gram_Schmidt V))"
      using basis_orthogonal'[of V] using B unfolding is_basis_def
      by (simp add: span_vec_eq)
    show "finite (set (Gram_Schmidt V))" by simp
    show "card (set (Gram_Schmidt V)) \<le> vec.dim (UNIV::(real^'b) set)"
      by (metis c top_greatest vec.dim_subset)
  qed
  ultimately show ?thesis by simp
qed


corollary orthogonal_basis_exists':
  fixes V :: "(real^'b) list"
  assumes B: "is_basis (set V)"
  and d: "distinct V"
  shows "is_basis (set (Gram_Schmidt V)) 
  \<and> distinct (Gram_Schmidt V) \<and> pairwise orthogonal (set (Gram_Schmidt V))"
  using B orthogonal_basis_exists basis_orthogonal' card_distinct d 
    vec.dim_unique distinct_card is_basis_def subset_refl
  by (metis span_vec_eq)


subsubsection\<open>Second way\<close>

text\<open>This definition applies the Gram Schmidt process starting from the first element of the list.\<close>

definition "Gram_Schmidt2 xs = Gram_Schmidt (rev xs)"

lemma basis_orthogonal2:
  fixes xs::"('a::{real_inner}^'b) list"
  shows "length (Gram_Schmidt2 xs) = length (xs)
  \<and> span (set (Gram_Schmidt2 xs)) = span (set xs)
  \<and> pairwise orthogonal (set (Gram_Schmidt2 xs))"
  by (metis Gram_Schmidt2_def basis_orthogonal' length_rev set_rev)

lemma card_Gram_Schmidt2:
  fixes xs::"('a::{real_inner}^'b) list"
  assumes "distinct xs"
  shows "card(set (Gram_Schmidt2 xs)) \<le> card (set (xs))"
  by (metis Gram_Schmidt2_def assms card_Gram_Schmidt distinct_rev set_rev)

lemma orthogonal_basis_exists2:
  fixes V :: "(real^'b) list"
  assumes B: "is_basis (set V)"
  and d: "distinct V"
  shows "vec.independent (set (Gram_Schmidt2 V)) \<and> (set V) \<subseteq> vec.span (set (Gram_Schmidt2 V)) 
  \<and> (card (set (Gram_Schmidt2 V)) = vec.dim (set V)) \<and> pairwise orthogonal (set (Gram_Schmidt2 V))"
  by (metis Gram_Schmidt.orthogonal_basis_exists Gram_Schmidt2_def distinct_rev set_rev
      B basis_orthogonal2 d)

subsubsection\<open>Third way\<close>

text\<open>The following definitions applies the Gram Schmidt process in the columns of a given matrix.
  It is previous step to the computation of the QR decomposition.\<close>

definition Gram_Schmidt_column_k :: "'a::{real_inner}^'cols::{mod_type}^'rows \<Rightarrow> nat 
  \<Rightarrow> 'a^'cols::{mod_type}^'rows" 
  where "Gram_Schmidt_column_k A k 
  = (\<chi> a. (\<chi> b. (if b = from_nat k 
  then (column b A - (proj_onto (column b A) {column i A|i. i < b})) 
  else (column b A)) $ a))"

definition "Gram_Schmidt_upt_k A k = foldl Gram_Schmidt_column_k A [0..<(Suc k)]"
definition "Gram_Schmidt_matrix A = Gram_Schmidt_upt_k A (ncols A - 1)"

text\<open>Some definitions and lemmas in order to get execution.\<close>

definition "Gram_Schmidt_column_k_row A k a = 
  vec_lambda(\<lambda>b. (if b = from_nat k then 
  (column b A - (\<Sum>x\<in>{column i A|i. i < b}. ((column b A) \<bullet> x / (x \<bullet> x)) *\<^sub>R x)) 
  else (column b A)) $ a)"

lemma Gram_Schmidt_column_k_row_code[code abstract]:
  "vec_nth (Gram_Schmidt_column_k_row A k a) 
  = (%b. (if b = from_nat k 
  then (column b A - (\<Sum>x\<in>{column i A|i. i < b}. ((column b A) \<bullet> x / (x \<bullet> x)) *\<^sub>R x)) 
  else (column b A)) $ a)"
  unfolding Gram_Schmidt_column_k_row_def
  by (metis (lifting) vec_lambda_beta)

lemma Gram_Schmidt_column_k_code[code abstract]:
  "vec_nth (Gram_Schmidt_column_k A k) = Gram_Schmidt_column_k_row A k"
  unfolding Gram_Schmidt_column_k_def unfolding Gram_Schmidt_column_k_row_def[abs_def]
  unfolding proj_onto_def proj_def[abs_def]
  by fastforce

text\<open>Proofs\<close>

lemma Gram_Schmidt_upt_k_suc: 
  "Gram_Schmidt_upt_k A (Suc k) = (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k))"
proof -
  have rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [(Suc k)]" by simp
  show ?thesis unfolding Gram_Schmidt_upt_k_def 
    unfolding rw unfolding foldl_append unfolding foldl.simps ..
qed

lemma column_Gram_Schmidt_upt_k_preserves:
  fixes A::"'a::{real_inner}^'cols::{mod_type}^'rows"
  assumes i_less_suc: "to_nat i<(Suc k)"
  and suc_less_card: "Suc k < CARD ('cols)"
  shows "column i (Gram_Schmidt_upt_k A (Suc k)) = column i (Gram_Schmidt_upt_k A k)"
proof -
  have "column i (Gram_Schmidt_upt_k A (Suc k)) 
    = column i (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k))"
    unfolding Gram_Schmidt_upt_k_suc ..
  also have "... = column i (Gram_Schmidt_upt_k A k)" unfolding Gram_Schmidt_column_k_def
    column_def using i_less_suc by (auto simp add: to_nat_from_nat_id[OF suc_less_card])
  finally show ?thesis .
qed

lemma column_set_Gram_Schmidt_upt_k:
  fixes A::"'a::{real_inner}^'cols::{mod_type}^'rows"
  assumes k: "Suc k < CARD ('cols)"
  shows "{column i (Gram_Schmidt_upt_k A (Suc k)) |i. to_nat i\<le>(Suc k)} =
  {column i (Gram_Schmidt_upt_k A k) |i. to_nat i\<le>k} \<union> {column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k)
  - (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A k) |i. to_nat i\<le>k}. (x \<bullet> (column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k)) / (x \<bullet> x)) *\<^sub>R x)}" 
proof -
  have set_rw: "{\<chi> ia. Gram_Schmidt_upt_k A k $ ia $ i |i.
    i < from_nat (Suc k)} = {\<chi> ia. Gram_Schmidt_upt_k A k $ ia $ i |i. to_nat i \<le> k}"
  proof (auto, vector, metis less_Suc_eq_le to_nat_le)
    fix i::'cols
    assume "to_nat i \<le> k"
    hence "to_nat i < Suc k" by simp
    hence i_less_suc: "i < from_nat (Suc k)" using from_nat_le[OF _ k] by simp
    show "\<exists>l. (\<lambda>j. Gram_Schmidt_upt_k A k $ j $ i) = (\<lambda>j'. Gram_Schmidt_upt_k A k $ j' $ l) \<and>  l < mod_type_class.from_nat (Suc k)"
      by (rule exI[of _ i], simp add: i_less_suc)
  qed
  have rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [(Suc k)]" by simp
  have "{column i (Gram_Schmidt_upt_k A (Suc k)) |i. to_nat i\<le>(Suc k)} 
    = {column i (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k)) |i. to_nat i \<le> Suc k}"
    unfolding Gram_Schmidt_upt_k_def 
    unfolding rw unfolding foldl_append unfolding foldl.simps ..
  also have "... = {column i (Gram_Schmidt_upt_k A k) |i. to_nat i\<le>k} \<union> {column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k)
    - (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A k) |i. to_nat i\<le>k}. (x \<bullet> (column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k)) / (x \<bullet> x)) *\<^sub>R x)}"
  proof (auto)
    fix i::'cols
    assume ik: "to_nat i \<le> k"
    show "\<exists>ia. column i (Gram_Schmidt_upt_k A k) 
      = column ia (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k)) \<and> to_nat ia \<le> Suc k"
    proof (rule exI[of _ i], rule conjI)
      have i_less_suc: "to_nat i < Suc k" using ik by auto
      thus "to_nat i \<le> Suc k" by simp
      show  "column i (Gram_Schmidt_upt_k A k) = column i (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k))"
        using column_Gram_Schmidt_upt_k_preserves[OF i_less_suc k, of A]
        unfolding Gram_Schmidt_upt_k_suc ..
    qed
  next
    show "\<exists>a. column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) -
      (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A k) |i.
      to_nat i \<le> k}. (x \<bullet> column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) / (x \<bullet> x)) *\<^sub>R x) =
      column a (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k)) \<and>
      to_nat a \<le> Suc k"
    proof (rule exI[of _ "from_nat (Suc k)::'cols"], rule conjI)

      show "to_nat (from_nat (Suc k)::'cols) \<le> Suc k" unfolding to_nat_from_nat_id[OF k] ..
      show "column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) -
        (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A k) |i.
        to_nat i \<le> k}. (x \<bullet> column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) / (x \<bullet> x)) *\<^sub>R x) =
        column (from_nat (Suc k)) (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k))"
        unfolding Gram_Schmidt_column_k_def column_def apply auto unfolding set_rw 
        unfolding vector_scaleR_component[symmetric]
        unfolding sum_component[symmetric]
        unfolding proj_onto_def proj_def[abs_def]
        unfolding proj_onto_sum_rw
        by vector 
    qed
  next
    fix i
    assume col_not_eq: "column i (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k)) \<noteq>
      column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) -
      (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A k) |i.
      to_nat i \<le> k}. (x \<bullet> column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) / (x \<bullet> x)) *\<^sub>R x)"
      and i: "to_nat i \<le> Suc k"
    have i_not_suc_k: "i \<noteq> from_nat (Suc k)"
    proof (rule ccontr, simp)
      assume i2: "i = from_nat (Suc k)"
      have "column i (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k)) =
        column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) -
        (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A k) |i.
        to_nat i \<le> k}. (x \<bullet> column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) / (x \<bullet> x)) *\<^sub>R x)"
        unfolding i2  Gram_Schmidt_column_k_def column_def 
        apply auto
        unfolding set_rw
        unfolding vector_scaleR_component[symmetric]
        unfolding sum_component[symmetric]
        unfolding proj_onto_def proj_def[abs_def]
        unfolding proj_onto_sum_rw
        by vector
      thus False using col_not_eq by contradiction
    qed
    show "\<exists>ia. column i (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k)) 
      = column ia (Gram_Schmidt_upt_k A k) \<and> to_nat ia \<le> k"
    proof (rule exI[of _ i], rule conjI, unfold Gram_Schmidt_upt_k_suc[symmetric], rule column_Gram_Schmidt_upt_k_preserves)
      show "to_nat i < Suc k" using i i_not_suc_k by (metis le_imp_less_or_eq from_nat_to_nat_id)
      thus "to_nat i \<le> k" using less_Suc_eq_le by simp
      show "Suc k < CARD('cols)" using k .
    qed
  qed
  finally show ?thesis .
qed


lemma orthogonal_Gram_Schmidt_upt_k:
  assumes s: "k < ncols A"
  shows "pairwise orthogonal ({column i (Gram_Schmidt_upt_k A k) |i. to_nat i\<le>k})"
  using s
proof (induct k)
  case 0
  have set_rw: "{column i (Gram_Schmidt_upt_k A 0) |i. to_nat i \<le> 0} =  {column 0 (Gram_Schmidt_upt_k A 0)}"
    by (simp add: to_nat_eq_0)
  show ?case unfolding set_rw unfolding pairwise_def by auto
next
  case (Suc k)
  have rw: "[0..<Suc (Suc k)] = [0..<Suc k] @ [(Suc k)]" by simp
  show ?case
    unfolding column_set_Gram_Schmidt_upt_k[OF Suc.prems[unfolded ncols_def], of A]
    unfolding proj_onto_sum_rw
    by (auto simp add: proj_def[symmetric] proj_onto_def[symmetric])
       (rule pairwise_orthogonal_proj_set, auto simp add: Suc.hyps Suc.prems Suc_lessD)
qed


lemma columns_Gram_Schmidt_matrix_rw: 
  "{column i (Gram_Schmidt_matrix A) |i. i \<in> UNIV} 
  = {column i (Gram_Schmidt_upt_k A (ncols A - 1)) |i. to_nat i\<le> (ncols A - 1)}"
proof (auto)
  fix i
  show "\<exists>ia. column i (Gram_Schmidt_matrix A) 
    = column ia (Gram_Schmidt_upt_k A (ncols A - Suc 0)) \<and> to_nat ia \<le> ncols A - Suc 0"
    apply (rule exI[of _ i]) unfolding Gram_Schmidt_matrix_def using to_nat_less_card[of i]
    unfolding ncols_def by fastforce
  show "\<exists>ia. column i (Gram_Schmidt_upt_k A (ncols A - Suc 0)) = column ia (Gram_Schmidt_matrix A)"
    unfolding Gram_Schmidt_matrix_def by auto
qed


corollary orthogonal_Gram_Schmidt_matrix:
  shows "pairwise orthogonal ({column i (Gram_Schmidt_matrix A) |i. i \<in> UNIV})"
  unfolding columns_Gram_Schmidt_matrix_rw
  by (rule orthogonal_Gram_Schmidt_upt_k, simp add: ncols_def)

corollary orthogonal_Gram_Schmidt_matrix2:
  shows "pairwise orthogonal (columns (Gram_Schmidt_matrix A))"
  unfolding columns_def using orthogonal_Gram_Schmidt_matrix .

lemma column_Gram_Schmidt_column_k:
  fixes A::"'a::{real_inner}^'n::{mod_type}^'m::{mod_type}"
  shows "column k (Gram_Schmidt_column_k A (to_nat k)) = 
  (column k A) - (\<Sum>x\<in>{column i A|i. i < k}. (x \<bullet> (column k A) / (x \<bullet> x)) *\<^sub>R x)"
  unfolding Gram_Schmidt_column_k_def column_def
  unfolding from_nat_to_nat_id 
  unfolding proj_onto_def proj_def[abs_def]
  unfolding proj_onto_sum_rw
  by vector


lemma column_Gram_Schmidt_column_k':
  fixes A::"'a::{real_inner}^'n::{mod_type}^'m::{mod_type}"
  assumes i_not_k: "i\<noteq>k"
  shows "column i (Gram_Schmidt_column_k A (to_nat k)) = (column i A)"
  using i_not_k
  unfolding Gram_Schmidt_column_k_def column_def
  unfolding from_nat_to_nat_id by vector


definition "cols_upt_k A k = {column i A|i. i\<le>from_nat k}"

lemma cols_upt_k_insert:
  fixes A::"'a^'n::{mod_type}^'m::{mod_type}"
  assumes k: "(Suc k)<ncols A"
  shows "cols_upt_k A (Suc k) = (insert (column (from_nat (Suc k)) A) (cols_upt_k A k))"
proof (unfold cols_upt_k_def, auto)
  fix i::'n
  assume i: "i \<le> from_nat (Suc k)" and "column i A \<noteq> column (from_nat (Suc k)) A"
  hence i_not_suc_k: "i \<noteq> from_nat (Suc k)" by auto
  have i_le:  "i \<le> from_nat k"
  proof -
    have "i < from_nat (Suc k)" by (metis le_imp_less_or_eq i i_not_suc_k)
    thus ?thesis by (metis Suc_eq_plus1 from_nat_suc le_Suc not_less)
  qed
  thus "\<exists>ia. column i A = column ia A \<and> ia \<le> from_nat k" by auto
next
  fix i::'n
  assume i: "i \<le> from_nat k"
  also have "... < from_nat (Suc k)"
    by (rule from_nat_mono[OF _ k[unfolded ncols_def]], simp)
  finally have "i \<le> from_nat (Suc k)" by simp
  thus "\<exists>ia. column i A = column ia A \<and> ia \<le> from_nat (Suc k)" by auto
qed


lemma columns_eq_cols_upt_k:
  fixes A::"'a^'cols::{mod_type}^'rows::{mod_type}"
  shows "cols_upt_k A (ncols A - 1) = columns A"
proof (unfold cols_upt_k_def columns_def, auto)
  fix i 
  show "\<exists>ia. column i A = column ia A \<and> ia \<le> from_nat (ncols A - Suc 0)"
  proof (rule exI[of _ i], simp)
    have "to_nat i < ncols A" using to_nat_less_card[of i] unfolding ncols_def by simp
    hence "to_nat i \<le> (ncols A - 1)" by simp
    hence "to_nat i \<le> to_nat (from_nat (ncols A - 1)::'cols)"
      using to_nat_from_nat_id[of "ncols A - 1", where ?'a='cols] unfolding ncols_def by simp
    thus "i \<le> from_nat (ncols A - Suc 0)" 
      by (metis One_nat_def less_le_not_le linear to_nat_mono)
  qed
qed


lemma span_cols_upt_k_Gram_Schmidt_column_k:
  fixes A::"'a::{real_inner}^'n::{mod_type}^'m::{mod_type}"
  assumes "k < ncols A"
  and "j < ncols A"
  shows "span (cols_upt_k A k) = span (cols_upt_k (Gram_Schmidt_column_k A j) k)"
  using assms
proof (induct k)
  case 0
  have set_rw: "{\<chi> ia. A $ ia $ i |i. i < 0} = {}" using least_mod_type not_less by auto
  have set_rw2: "{column i (Gram_Schmidt_column_k A j) |i. i \<le> 0} = {column 0 (Gram_Schmidt_column_k A j)}"
    by (auto, metis eq_iff least_mod_type)
  have set_rw3: "{column i A |i. i \<le> 0} ={column 0 A}"  by (auto, metis eq_iff least_mod_type)
  have col_0_eq: "column 0 (Gram_Schmidt_column_k A j) = column 0 A"
    unfolding Gram_Schmidt_column_k_def column_def
    unfolding proj_onto_def proj_def[abs_def]
    by (simp add: set_rw)
  show ?case unfolding cols_upt_k_def from_nat_0 unfolding set_rw2 set_rw3 unfolding col_0_eq ..
next
  case (Suc k)
  have hyp: "span (cols_upt_k A k) = span (cols_upt_k (Gram_Schmidt_column_k A j) k)" 
    using Suc.prems Suc.hyps by auto
  have set_rw1: "(cols_upt_k A (Suc k)) = insert (column (from_nat (Suc k)) A) (cols_upt_k A k)"
    using cols_upt_k_insert
    by (auto intro!: cols_upt_k_insert[OF Suc.prems(1)])
  have set_rw2: "(cols_upt_k (Gram_Schmidt_column_k A j) (Suc k)) = 
    insert (column (from_nat (Suc k)) (Gram_Schmidt_column_k A j)) (cols_upt_k (Gram_Schmidt_column_k A j) k)"
    using cols_upt_k_insert  Suc.prems(1) unfolding ncols_def by auto
  show ?case
  proof (cases "j=Suc k")
    case False
    have suc_not_k: "from_nat (Suc k) \<noteq> (from_nat j::'n)"
    proof (rule ccontr, simp)
      assume "from_nat (Suc k) = (from_nat j::'n)"
      hence "Suc k = j" apply (rule from_nat_eq_imp_eq) using Suc.prems unfolding ncols_def .
      thus False using False by simp
    qed
    have tnfnj: "to_nat (from_nat j::'n) = j" using to_nat_from_nat_id[OF Suc.prems(2)[unfolded ncols_def]] .
    let ?a_suc_k = "column (from_nat (Suc k)) A"
    have col_eq: "column (from_nat (Suc k)) (Gram_Schmidt_column_k A j) = ?a_suc_k"
      using column_Gram_Schmidt_column_k'[OF suc_not_k] unfolding tnfnj .
    have k: "k<CARD('n)" using Suc.prems(1)[unfolded ncols_def] by simp
    show ?thesis unfolding set_rw1 set_rw2 col_eq unfolding span_insert unfolding hyp ..
  next
    case True
    define C where "C = cols_upt_k A k"
    define B where "B = cols_upt_k (Gram_Schmidt_column_k A j) k"
    define a where "a = column (from_nat (Suc k)) A"
    let ?a="a - sum (\<lambda>x. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x) C"
    let ?C="insert ?a C"
    have col_rw: "{column i A |i. i \<le> from_nat k} = {column i A |i. i < from_nat (Suc k)}" 
    proof (auto)
      fix i::'n assume i: "i \<le> from_nat k"
      also have "... < from_nat (Suc k)" by (rule from_nat_mono[OF _ Suc.prems(1)[unfolded ncols_def]], simp)
      finally show "\<exists>ia. column i A = column ia A \<and> ia < from_nat (Suc k)" by auto
    next
      fix i::'n
      assume i: "i < from_nat (Suc k)"
      hence "i\<le> from_nat k" unfolding Suc_eq_plus1 unfolding from_nat_suc by (metis le_Suc not_less)
      thus " \<exists>ia. column i A = column ia A \<and> ia \<le> from_nat k" by auto
    qed
    have rw: "column (from_nat (Suc k)) (Gram_Schmidt_column_k A j) = (a - (\<Sum>x\<in>cols_upt_k A k. (x \<bullet> a / (x \<bullet> x)) *\<^sub>R x))"
      unfolding Gram_Schmidt_column_k_def True  unfolding cols_upt_k_def a_def C_def
      unfolding  column_def apply auto 
      unfolding column_def[symmetric] col_rw minus_vec_def
      unfolding column_def vec_lambda_beta
      unfolding proj_onto_def proj_def[abs_def]
      unfolding proj_onto_sum_rw
      by auto
    have finite_C: "finite C" unfolding C_def cols_upt_k_def by auto
    {
      fix x b
      have th0: "!!(a::'a^'m::{mod_type}) b c. a - (b - c) = c + (a - b)"
        by (simp add: field_simps)
      have "x - b *\<^sub>R  (a - (\<Sum>x\<in>C. (x \<bullet> a / (x \<bullet> x))  *\<^sub>R  x)) \<in> span C \<longleftrightarrow> x - b  *\<^sub>R  a \<in> span C"
        apply (simp only: scaleR_right_diff_distrib th0)
        apply (rule span_add_eq)
        apply (rule span_mul)
        apply (rule span_sum)
        apply (rule span_mul)
        apply (rule span_base)
        apply assumption
        done
    } 
    thus ?thesis unfolding set_eq_iff
      unfolding C_def B_def unfolding set_rw1 unfolding set_rw2
      unfolding span_breakdown_eq unfolding hyp
      by (metis (mono_tags) B_def a_def rw)
  qed
qed


corollary span_Gram_Schmidt_column_k:
  fixes A::"'a::{real_inner}^'n::{mod_type}^'m::{mod_type}"
  assumes "k<ncols A"
  shows "span (columns A) = span (columns (Gram_Schmidt_column_k A k))"
  unfolding columns_eq_cols_upt_k[symmetric] 
  using span_cols_upt_k_Gram_Schmidt_column_k[of "ncols A - 1" A k]
  using assms unfolding ncols_def by auto


corollary span_Gram_Schmidt_upt_k:
  fixes A::"'a::{real_inner}^'n::{mod_type}^'m::{mod_type}"
  assumes "k<ncols A"
  shows "span (columns A) = span (columns (Gram_Schmidt_upt_k A k))"
  using assms
proof (induct k)
  case 0
  have "columns (Gram_Schmidt_column_k A 0) = columns A"    
  proof (unfold columns_def, auto)
    fix i 
    have set_rw: "{\<chi> ia. A $ ia $ i |i. i < from_nat 0} = {}"
      by (auto, metis less_le_not_le least_mod_type from_nat_0)
    thus "\<exists>ia. column i (Gram_Schmidt_column_k A 0) = column ia A" 
      unfolding Gram_Schmidt_column_k_def column_def
      unfolding proj_onto_def proj_def[abs_def] by auto
    show "\<exists>ia. column i A = column ia (Gram_Schmidt_column_k A 0)"
      using set_rw unfolding Gram_Schmidt_column_k_def column_def 
      unfolding from_nat_0 
      unfolding proj_onto_def proj_def[abs_def]
      by force
  qed
  thus ?case unfolding Gram_Schmidt_upt_k_def by auto
next
  case (Suc k)
  have hyp: "span (columns A) = span (columns (Gram_Schmidt_upt_k A k))" 
    using Suc.prems Suc.hyps by auto
  have "span (columns (Gram_Schmidt_upt_k A (Suc k))) 
    = span (columns (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k)))"
    unfolding Gram_Schmidt_upt_k_suc ..
  also have "... = span (columns (Gram_Schmidt_upt_k A k))"
    using span_Gram_Schmidt_column_k[of "Suc k" "(Gram_Schmidt_upt_k A k)"]
    using Suc.prems unfolding ncols_def by auto
  finally show ?case using hyp by auto
qed

corollary span_Gram_Schmidt_matrix:
  fixes A::"'a::{real_inner}^'n::{mod_type}^'m::{mod_type}"
  shows "span (columns A) = span (columns (Gram_Schmidt_matrix A))"
  unfolding Gram_Schmidt_matrix_def
  by (simp add: span_Gram_Schmidt_upt_k ncols_def)

lemma is_basis_columns_Gram_Schmidt_matrix:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes b: "is_basis (columns A)"
  and c: "card (columns A) = ncols A"
  shows "is_basis (columns (Gram_Schmidt_matrix A)) 
  \<and> card (columns (Gram_Schmidt_matrix A)) = ncols A"
proof -
  have span_UNIV: "vec.span (columns (Gram_Schmidt_matrix A)) = (UNIV::(real^'m::{mod_type}) set)" 
    using span_Gram_Schmidt_matrix b unfolding is_basis_def
    by (metis span_vec_eq)
  moreover have c_eq: "card (columns (Gram_Schmidt_matrix A)) = ncols A" 
  proof -
    have "card (columns A) \<le> card (columns (Gram_Schmidt_matrix A))"
      by (metis b is_basis_def finite_columns vec.independent_span_bound span_UNIV top_greatest)
    thus ?thesis using c using card_columns_le_ncols by (metis le_antisym ncols_def)
  qed
  moreover have "vec.independent (columns (Gram_Schmidt_matrix A))"
  proof (rule vec.card_le_dim_spanning[of _ "UNIV::(real^'m::{mod_type}) set"])
    show "columns (Gram_Schmidt_matrix A) \<subseteq> UNIV" by simp
    show "UNIV \<subseteq> vec.span (columns (Gram_Schmidt_matrix A))" using span_UNIV by auto
    show "finite (columns (Gram_Schmidt_matrix A))" using finite_columns .
    show "card (columns (Gram_Schmidt_matrix A)) \<le> vec.dim (UNIV::(real^'m::{mod_type}) set)"
      by (metis b c c_eq eq_iff is_basis_def vec.dim_span_eq_card_independent)
  qed
  ultimately show ?thesis unfolding is_basis_def by simp
qed


text\<open>From here on, we present some lemmas that will be useful for the formalisation of the QR
  decomposition.\<close> 

lemma column_gr_k_Gram_Schmidt_upt:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes "i>k"
  and i: "i<ncols A"
  shows "column (from_nat i) (Gram_Schmidt_upt_k A k) = column (from_nat i) A"
  using assms(1)
proof (induct k)
  assume "0 < i"
  hence "(from_nat i::'n) \<noteq> 0" 
    unfolding from_nat_0[symmetric] using bij_from_nat[where ?'a='n] unfolding bij_betw_def
    by (metis from_nat_eq_imp_eq gr_implies_not0 i ncols_def neq0_conv)
  thus "column (from_nat i) (Gram_Schmidt_upt_k A 0) = column (from_nat i) A"
    unfolding Gram_Schmidt_upt_k_def 
    by (simp add: Gram_Schmidt_column_k_def from_nat_0 column_def)  
next
  case (Suc k)
  have hyp: "column (from_nat i) (Gram_Schmidt_upt_k A k) = column (from_nat i) A"
    using Suc.hyps Suc.prems by auto
  have to_nat_from_nat_suc_k: "(to_nat (from_nat (Suc k)::'n)) = Suc k"
    by (metis Suc.prems dual_order.strict_trans from_nat_not_eq i ncols_def)
  have "column (from_nat i) (Gram_Schmidt_upt_k A (Suc k)) 
    = column (from_nat i) (Gram_Schmidt_column_k (Gram_Schmidt_upt_k A k) (Suc k))"
    unfolding Gram_Schmidt_upt_k_suc .. 
  also have "... =  column (from_nat i) (Gram_Schmidt_upt_k A k)"
  proof (rule column_Gram_Schmidt_column_k'
      [of "from_nat i" "from_nat (Suc k)" " (Gram_Schmidt_upt_k A k)", unfolded to_nat_from_nat_suc_k])
    show "from_nat i \<noteq> (from_nat (Suc k)::'n)" 
      by (metis Suc.prems not_less_iff_gr_or_eq
        from_nat_not_eq i ncols_def to_nat_from_nat_suc_k)
  qed
  finally show ?case unfolding hyp .
qed

lemma columns_Gram_Schmidt_upt_k_rw:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes k: "Suc k < ncols A"
  shows "{column i (Gram_Schmidt_upt_k A (Suc k)) |i. i < from_nat (Suc k)} 
  = {column i (Gram_Schmidt_upt_k A k) |i. i < from_nat (Suc k)}"
proof (auto)
  fix i::'n assume i: "i < from_nat (Suc k)"
  have to_nat_from_nat_k: "to_nat (from_nat (Suc k)::'n) = Suc k" 
    using to_nat_from_nat_id k unfolding ncols_def by auto
  show "\<exists>ia. column i (Gram_Schmidt_upt_k A (Suc k)) = column ia (Gram_Schmidt_upt_k A k) \<and> ia < from_nat (Suc k)"
    by (metis column_Gram_Schmidt_upt_k_preserves i k ncols_def to_nat_le)
  show "\<exists>ia. column i (Gram_Schmidt_upt_k A k) = column ia (Gram_Schmidt_upt_k A (Suc k)) \<and> ia < from_nat (Suc k)"
    by (metis column_Gram_Schmidt_upt_k_preserves i k ncols_def to_nat_le)
qed


lemma column_Gram_Schmidt_upt_k:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes "k<ncols A"
  shows "column (from_nat k) (Gram_Schmidt_upt_k A k) = 
  (column (from_nat k) A) - (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A k)|i. i < (from_nat k)}. (x \<bullet> (column (from_nat k) A) / (x \<bullet> x)) *\<^sub>R x)"
  using assms
proof (induct k, unfold from_nat_0)
  have set_rw: "{column i (Gram_Schmidt_upt_k A 0) |i. i < 0} = {}" by (auto, metis least_mod_type not_le)
  have set_rw2: "{column i A |i. i < 0} = {}"  by (auto, metis least_mod_type not_le)
  have col_rw: "column 0 A = column 0 (Gram_Schmidt_upt_k A 0)"
    unfolding Gram_Schmidt_upt_k_def apply auto unfolding Gram_Schmidt_column_k_def from_nat_0
    unfolding column_def
    using set_rw2 unfolding proj_onto_def proj_def[abs_def]
    by vector
  show "column 0 (Gram_Schmidt_upt_k A 0) 
    = column 0 A - (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A 0) |i. i < 0}. (x \<bullet> column 0 A / (x \<bullet> x)) *\<^sub>R x)"
    unfolding set_rw col_rw by simp
next
  case (Suc k)
  let ?ak="column (from_nat k) A"
  let ?uk="column (from_nat k) (Gram_Schmidt_upt_k A k)"
  let ?a_suck= "column (from_nat (Suc k)) A"
  let ?u_suck="column (from_nat (Suc k)) (Gram_Schmidt_upt_k A (Suc k))"
  have to_nat_from_nat_k: "to_nat (from_nat (Suc k)::'n) = (Suc k)" 
    using to_nat_from_nat_id Suc.prems unfolding ncols_def by auto
  have a_suc_rw: "column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) = ?a_suck"
    by (rule column_gr_k_Gram_Schmidt_upt, auto simp add: Suc.prems)
  have set_rw: "{column i (Gram_Schmidt_upt_k A (Suc k)) |i. i < from_nat (Suc k)} 
    = {column i (Gram_Schmidt_upt_k A k) |i. i < from_nat (Suc k)}"
    by (rule columns_Gram_Schmidt_upt_k_rw[OF Suc.prems])
  have "?u_suck = column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) -
    (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A k) |i.
    i < from_nat (Suc k)}. (x \<bullet> column (from_nat (Suc k)) (Gram_Schmidt_upt_k A k) / (x \<bullet> x)) *\<^sub>R x)" 
    unfolding Gram_Schmidt_upt_k_suc
    using column_Gram_Schmidt_column_k[of "from_nat (Suc k)" "(Gram_Schmidt_upt_k A k)"]
    unfolding to_nat_from_nat_k by auto
  also have "... = ?a_suck -
    (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A k) |i.
    i < from_nat (Suc k)}. (x \<bullet> ?a_suck / (x \<bullet> x)) *\<^sub>R x)" unfolding a_suc_rw ..
  finally show "?u_suck = ?a_suck - (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A (Suc k)) |i.
    i < from_nat (Suc k)}. (x \<bullet> ?a_suck / (x \<bullet> x)) *\<^sub>R x)" 
    unfolding set_rw .
qed



lemma column_Gram_Schmidt_upt_k_preserves2:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes "a\<le>(from_nat i)"
  and "i \<le> j"
  and "j<ncols A"
  shows "column a (Gram_Schmidt_upt_k A i) = column a (Gram_Schmidt_upt_k A j)"
  using assms
proof (induct j)
  case 0
  show "column a (Gram_Schmidt_upt_k A i) = column a (Gram_Schmidt_upt_k A 0)" by (metis "0.prems"(2) le_0_eq)
next
  case (Suc j)
  show ?case
  proof (cases "a=from_nat (Suc j)")
    case False note a_not_suc_j=False
    have rw1: "(to_nat (from_nat (Suc j)::'n)) = Suc j"
      using to_nat_from_nat_id Suc.prems unfolding ncols_def by auto
    show ?thesis unfolding Gram_Schmidt_upt_k_suc using column_Gram_Schmidt_column_k'[OF a_not_suc_j] unfolding rw1
      by (metis Gram_Schmidt_upt_k_suc Suc.hyps Suc.prems(2) Suc.prems(3) Suc_le_lessD assms(1) le_Suc_eq nat_less_le)
  next
    case True
    have "(from_nat i::'n) \<le> from_nat (Suc j)" by (rule from_nat_mono'[OF Suc.prems(2) Suc.prems(3)[unfolded ncols_def]])
    hence "from_nat i = (from_nat (Suc j)::'n)" using Suc.prems(1) unfolding True by simp
    hence i_eq_suc: "i=Suc j" apply (rule from_nat_eq_imp_eq) using Suc.prems unfolding ncols_def by auto
    show ?thesis unfolding True i_eq_suc ..
  qed
qed



lemma set_columns_Gram_Schmidt_matrix: 
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  shows "{column i (Gram_Schmidt_matrix A)|i. i < k} = {column i (Gram_Schmidt_upt_k A (to_nat k))|i. i < k}"
proof (auto)
  fix i assume i: "i<k"
  show "\<exists>ia. column i (Gram_Schmidt_matrix A) = column ia (Gram_Schmidt_upt_k A (to_nat k)) \<and> ia < k"
  proof (rule exI[of _ i], rule conjI)
    show "column i (Gram_Schmidt_matrix A) = column i (Gram_Schmidt_upt_k A (to_nat k))"
      unfolding Gram_Schmidt_matrix_def 
    proof (rule column_Gram_Schmidt_upt_k_preserves2[symmetric])
      show "i \<le> from_nat (to_nat k)" using i unfolding from_nat_to_nat_id by auto
      show "to_nat k \<le> ncols A - 1" unfolding ncols_def using to_nat_less_card[of k] by auto
      show "ncols A - 1 < ncols A" unfolding ncols_def by simp
    qed
    show "i < k" using i .
  qed
  show "\<exists>ia. column i (Gram_Schmidt_upt_k A (to_nat k)) = column ia (Gram_Schmidt_matrix A) \<and> ia < k"
  proof (rule exI[of _ i], rule conjI)
    show "column i (Gram_Schmidt_upt_k A (to_nat k)) = column i (Gram_Schmidt_matrix A)"
      unfolding Gram_Schmidt_matrix_def 
    proof (rule column_Gram_Schmidt_upt_k_preserves2)
      show "i \<le> from_nat (to_nat k)" using i unfolding from_nat_to_nat_id by auto
      show "to_nat k \<le> ncols A - 1" unfolding ncols_def using to_nat_less_card[of k] by auto
      show "ncols A - 1 < ncols A" unfolding ncols_def by simp
    qed
    show "i < k" using i .
  qed
qed



lemma column_Gram_Schmidt_matrix:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  shows "column k (Gram_Schmidt_matrix A) 
  = (column k A) - (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A)|i. i < k}. (x \<bullet> (column k A) / (x \<bullet> x)) *\<^sub>R x)"
proof -
  have k: "to_nat k < ncols A" using to_nat_less_card[of k] unfolding ncols_def by simp
  have "column k (Gram_Schmidt_matrix A) = column k (Gram_Schmidt_upt_k A (ncols A - 1))"
    unfolding Gram_Schmidt_matrix_def ..
  also have "... = column k (Gram_Schmidt_upt_k A (to_nat k))"
  proof (rule column_Gram_Schmidt_upt_k_preserves2[symmetric])
    show "k \<le> from_nat (to_nat k)" unfolding from_nat_to_nat_id ..
    show "to_nat k \<le> ncols A - 1" unfolding ncols_def using to_nat_less_card[where ?'a='n]
      by (metis Nat.le_diff_conv2 add_leE less_diff_conv less_imp_le_nat  less_le_not_le
        nat_le_linear suc_not_zero to_nat_plus_one_less_card')
    show "ncols A - 1 < ncols A" unfolding ncols_def by auto
  qed
  also have "... = column k A - (\<Sum>x\<in>{column i (Gram_Schmidt_upt_k A (to_nat k)) |i. i < k}. (x \<bullet> column k A / (x \<bullet> x)) *\<^sub>R x)"
    using column_Gram_Schmidt_upt_k[OF k] unfolding from_nat_to_nat_id by auto
  also have "... = column k A - (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i. i < k}. (x \<bullet> column k A / (x \<bullet> x)) *\<^sub>R x)"
    unfolding set_columns_Gram_Schmidt_matrix[symmetric] ..
  finally show ?thesis .
qed


corollary column_Gram_Schmidt_matrix2:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  shows "(column k A) = column k (Gram_Schmidt_matrix A) 
  + (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A)|i. i < k}. (x \<bullet> (column k A) / (x \<bullet> x)) *\<^sub>R x)"
  using column_Gram_Schmidt_matrix[of k A] by simp



lemma independent_columns_Gram_Schmidt_matrix:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes b: "vec.independent (columns A)"
  and c: "card (columns A) = ncols A"
  shows "vec.independent (columns (Gram_Schmidt_matrix A)) \<and> card (columns (Gram_Schmidt_matrix A)) = ncols A"
  using  b c card_columns_le_ncols vec.card_eq_dim_span_indep vec.dim_span eq_iff finite_columns 
    vec.independent_span_bound ncols_def span_Gram_Schmidt_matrix
  by (metis (no_types, lifting) vec.card_ge_dim_independent vec.dim_span_eq_card_independent span_vec_eq)


lemma column_eq_Gram_Schmidt_matrix:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  and c: "column i (Gram_Schmidt_matrix A) = column ia (Gram_Schmidt_matrix A)"
  shows "i = ia"
proof (rule ccontr)
  assume i_not_ia: "i \<noteq> ia"
  have "columns (Gram_Schmidt_matrix A) = (\<lambda>x. column x (Gram_Schmidt_matrix A))` (UNIV::('n::{mod_type}) set)"
    unfolding columns_def by auto
  also have "... = (\<lambda>x. column x (Gram_Schmidt_matrix A))` ((UNIV::('n::{mod_type}) set)-{ia})"
  proof (unfold image_def, auto)  
    fix xa
    show "\<exists>x\<in>UNIV - {ia}. column xa (Gram_Schmidt_matrix A) = column x (Gram_Schmidt_matrix A)"
    proof (cases "xa = ia")
      case True thus ?thesis using c i_not_ia by (metis DiffI UNIV_I empty_iff insert_iff)
    next
      case False thus ?thesis by auto
    qed
  qed
  finally have columns_rw: "columns (Gram_Schmidt_matrix A) = (\<lambda>x. column x (Gram_Schmidt_matrix A)) ` (UNIV - {ia})" .
  have "ncols A = card (columns (Gram_Schmidt_matrix A))"
    by (metis full_rank_imp_is_basis2 independent_columns_Gram_Schmidt_matrix r)
  also have "... \<le> card (UNIV - {ia})" unfolding columns_rw by (rule card_image_le, simp)
  also have "... = card (UNIV::'n set) - 1" by (simp add: card_Diff_singleton)
  finally show False unfolding ncols_def
    by (metis Nat.add_0_right Nat.le_diff_conv2 One_nat_def Suc_n_not_le_n add_Suc_right one_le_card_finite)
qed

lemma scaleR_columns_Gram_Schmidt_matrix:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes "i \<noteq> j"
  and "rank A = ncols A"
  shows "column j (Gram_Schmidt_matrix A) \<bullet> column i (Gram_Schmidt_matrix A) = 0"
proof -
  have "column j (Gram_Schmidt_matrix A) \<noteq> column i (Gram_Schmidt_matrix A)"
    using column_eq_Gram_Schmidt_matrix assms by auto
  thus ?thesis using orthogonal_Gram_Schmidt_matrix2 unfolding pairwise_def orthogonal_def columns_def
    by blast
qed


subsubsection\<open>Examples of execution\<close>

text\<open>Code lemma\<close>
lemmas Gram_Schmidt_step_def[unfolded proj_onto_def proj_def[abs_def],code]

value "let a = map (list_to_vec::real list=> real^4) [[4,-2,-1,2], 
  [-6,3,4,-8], [5,-5,-3,-4]] in 
  map vec_to_list (Gram_Schmidt a)"

value "let a = map (list_to_vec::real list=> real^4) [[4,-2,-1,2], 
  [-6,3,4,-8], [5,-5,-3,-4]] in 
  map vec_to_list (Gram_Schmidt2 a)"

value "let A = list_of_list_to_matrix [[4,-2,-1,2], 
  [-6,3,4,-8], [5,-5,-3,-4]]::real^4^3 in 
  matrix_to_list_of_list (Gram_Schmidt_matrix A)"


end
