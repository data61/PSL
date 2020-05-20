(*  
    Title:      QR_Decomposition.thy
    Author:     Jose Divasón <jose.divasonm at unirioja.es>
    Author:     Jesús Aransay <jesus-maria.aransay at unirioja.es>
*)

section\<open>QR Decomposition\<close>

theory QR_Decomposition
imports Gram_Schmidt
begin
 
subsection\<open>The QR Decomposition of a matrix\<close>

text\<open>
First of all, it's worth noting what an orthogonal matrix is. In linear algebra, 
an orthogonal matrix is a square matrix with real entries whose columns and rows are orthogonal 
unit vectors.

Although in some texts the QR decomposition is presented over square matrices, it can be applied to any matrix.
There are some variants of the algorithm, depending on the properties that the output matrices 
satisfy (see for instance, @{url "http://inst.eecs.berkeley.edu/~ee127a/book/login/l_mats_qr.html"}). 
We present two of them below.

Let A be a matrix with m rows and n columns (A is \<open>m \<times> n\<close>).

Case 1: Starting with a matrix whose column rank is maximum. We can define the QR decomposition
to obtain:

\begin{itemize}
  \item @{term "A = Q ** R"}.
  \item Q has m rows and n columns. Its columns are orthogonal unit vectors 
        and @{term "(transpose Q) * Q = mat 1"}. In addition, if A is a square matrix, then Q
        will be an orthonormal matrix.
  \item R is \<open>n \<times> n\<close>, invertible and upper triangular.
\end{itemize}

Case 2: The called full QR decomposition. We can obtain:
\begin{itemize}
 \item @{term "A = Q ** R"}
 \item Q is an orthogonal matrix (Q is \<open>m \<times> m\<close>).
 \item R is \<open>m \<times> n\<close> and upper triangular, but it isn't invertible.
\end{itemize}

We have decided to formalise the first one, because it's the only useful for solving 
the linear least squares problem (@{url "http://math.mit.edu/linearalgebra/ila0403.pdf"}).

If we have an unsolvable system \<open>A *v x = b\<close>, we can try to find an approximate solution.
A plausible choice (not the only one) is to seek an \<open>x\<close> with the property that
\<open>\<parallel>A ** x - y\<parallel>\<close> (the magnitude of the error) is as small as possible. That \<open>x\<close>
is the least squares approximation.

We will demostrate that the best approximation (the solution for the linear least squares problem)
is the \<open>x\<close> that satisfies:

\<open>(transpose A) ** A *v x = (transpose A) *v b\<close>

Now we want to compute that x.

If we are working with the first case, \<open>A\<close> can be substituted by \<open>Q**R\<close> and then
obtain the solution of the least squares approximation by means of the QR decomposition:

\<open>x = (inverse R)**(transpose Q) *v b\<close>

On the contrary, if we are working with the second case after 
substituting \<open>A\<close> by \<open>Q**R\<close> we obtain:

\<open>(transpose R) ** R *v x = (transpose R) ** (transpose Q) *v b\<close>

But the \<open>R\<close> matrix is not invertible (so neither is \<open>transpose R\<close>). The left part
of the equation \<open>(transpose R) ** R\<close> is not going to be an upper triangular matrix, 
so it can't either be solved using backward-substitution.
\<close>


subsubsection\<open>Divide a vector by its norm\<close>

text\<open>An orthogonal matrix is a matrix whose rows (and columns) are orthonormal vectors. So, in order to 
obtain the QR decomposition, we have to normalise (divide by the norm) 
the vectors obtained with the Gram-Schmidt algorithm.\<close>

definition "divide_by_norm A  = (\<chi> a b. normalize (column b A) $ a)"

text\<open>Properties\<close>

lemma norm_column_divide_by_norm:
  fixes A::"'a::{real_inner}^'cols^'rows"
  assumes a: "column a A \<noteq> 0"
  shows "norm (column a (divide_by_norm A)) = 1"
proof -
  have not_0: "norm (\<chi> i. A $ i $ a) \<noteq> 0" by (metis a column_def norm_eq_zero)
  have "column a (divide_by_norm A) = (\<chi> i. (1 / norm (\<chi> i. A $ i $ a)) *\<^sub>R A $ i $ a)" 
    unfolding divide_by_norm_def column_def normalize_def by auto
  also have "... =  (1 / norm (\<chi> i. A $ i $ a)) *\<^sub>R (\<chi> i.  A $ i $ a)"
    unfolding vec_eq_iff by auto
  finally have "norm (column a (divide_by_norm A)) = norm ((1 / norm (\<chi> i. A $ i $ a)) *\<^sub>R (\<chi> i.  A $ i $ a))"
    by simp
  also have "... = \<bar>1 / norm (\<chi> i. A $ i $ a)\<bar> * norm (\<chi> i. A $ i $ a)"
    unfolding norm_scaleR ..
  also have "... = (1 / norm (\<chi> i. A $ i $ a)) * norm (\<chi> i. A $ i $ a)"
    by auto
  also have "... = 1" using not_0 by auto
  finally show ?thesis .
qed

lemma span_columns_divide_by_norm:
  shows "span (columns A) = span (columns (divide_by_norm A))"
  unfolding real_vector.span_eq
proof (auto)
  fix x assume x: "x \<in> columns (divide_by_norm A)"
  from this obtain i where x_col_i: "x=column i (divide_by_norm A)" unfolding columns_def by blast
  also have "... = (1/norm (column i  A)) *\<^sub>R (column i A)" 
    unfolding divide_by_norm_def column_def normalize_def by vector
  finally have x_eq: "x=(1/norm (column i A)) *\<^sub>R (column i A)" .
  show "x \<in> span (columns A)"
    by (unfold x_eq, rule span_mul, rule span_base, auto simp add: columns_def)
next
  fix x
  assume x: "x \<in> columns A"
  show "x \<in> span (columns (divide_by_norm A))"
  proof (cases "x=0")
    case True show ?thesis by (metis True span_0)
  next
    case False
    from x obtain i where x_col_i: "x=column i A" unfolding columns_def by blast
    have "x=column i A" using x_col_i .
    also have "... = norm (column i A) *\<^sub>R column i (divide_by_norm A)"
      using False unfolding x_col_i columns_def divide_by_norm_def column_def normalize_def by vector
    finally have x_eq: "x = norm (column i A) *\<^sub>R column i (divide_by_norm A)" .
    show "x \<in> span (columns (divide_by_norm A))"
      by (unfold x_eq, rule span_mul, rule span_base,
        auto simp add: columns_def Let_def)
  qed
qed

text\<open>Code lemmas\<close>

definition "divide_by_norm_row A a = vec_lambda(% b. ((1 / norm (column b A)) *\<^sub>R column b A) $ a)"

lemma divide_by_norm_row_code[code abstract]:
  "vec_nth (divide_by_norm_row A a) = (% b. ((1 / norm (column b A)) *\<^sub>R column b A) $ a)"
  unfolding divide_by_norm_row_def by (metis (lifting) vec_lambda_beta)

lemma divide_by_norm_code [code abstract]:
  "vec_nth (divide_by_norm A) = divide_by_norm_row A"
  unfolding divide_by_norm_def unfolding divide_by_norm_row_def[abs_def]
  unfolding normalize_def
  by fastforce

subsubsection\<open>The QR Decomposition\<close>

text\<open>The QR decomposition. Given a real matrix @{term "A"}, the algorithm will return a pair @{term "(Q,R)"}
  where @{term "Q"} is an matrix whose columns are orthogonal unit vectors, @{term "R"} 
  is upper triangular and @{term "A=Q**R"}.\<close>

definition "QR_decomposition A = (let Q = divide_by_norm (Gram_Schmidt_matrix A) in (Q, (transpose Q) ** A))"

lemma is_basis_columns_fst_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes b: "is_basis (columns A)"
  and c: "card (columns A) = ncols A"
  shows "is_basis (columns (fst (QR_decomposition A))) 
  \<and> card (columns (fst (QR_decomposition A))) = ncols A"
proof (rule conjI, unfold is_basis_def, rule conjI)
  have "vec.span (columns (fst (QR_decomposition A))) = vec.span (columns (Gram_Schmidt_matrix A))"
    unfolding vec.span_eq
  proof (auto)
    fix x show "x \<in> vec.span (columns (Gram_Schmidt_matrix A))"
      using assms(1) assms(2) is_basis_columns_Gram_Schmidt_matrix is_basis_def by auto
  next
    fix x
    assume x: "x \<in> columns (Gram_Schmidt_matrix A)"
    from this obtain i where x_col_i: "x=column i (Gram_Schmidt_matrix A)" unfolding columns_def by blast
    have zero_not_in: "x \<noteq> 0" using is_basis_columns_Gram_Schmidt_matrix[OF b c] unfolding is_basis_def
      using vec.dependent_zero[of "(columns (Gram_Schmidt_matrix A))"] x by auto
    have "x=column i (Gram_Schmidt_matrix A)" using x_col_i .
    also have "... = norm (column i (Gram_Schmidt_matrix A)) *\<^sub>R column i (divide_by_norm (Gram_Schmidt_matrix A))"
      using zero_not_in unfolding x_col_i columns_def divide_by_norm_def column_def normalize_def by vector
    finally have x_eq: "x = norm (column i (Gram_Schmidt_matrix A)) *\<^sub>R column i (divide_by_norm (Gram_Schmidt_matrix A))" .
    show "x \<in> vec.span (columns (fst (QR_decomposition A)))"
      unfolding x_eq span_vec_eq
      apply (rule subspace_mul)
      apply (auto simp add: columns_def QR_decomposition_def Let_def subspace_span intro: span_superset)
      using span_superset by force
  qed
  thus s: "vec.span (columns (fst (QR_decomposition A))) = (UNIV::(real^'m::{mod_type}) set)"
    using is_basis_columns_Gram_Schmidt_matrix[OF b c] unfolding is_basis_def by simp
  thus "card (columns (fst (QR_decomposition A))) = ncols A"
    by (metis (hide_lams, mono_tags) b c card_columns_le_ncols vec.card_le_dim_spanning 
      finite_columns vec.indep_card_eq_dim_span is_basis_def ncols_def top_greatest)
  thus "vec.independent (columns (fst (QR_decomposition A)))"
    by (metis s b c vec.card_eq_dim_span_indep finite_columns vec.indep_card_eq_dim_span is_basis_def)
qed


lemma orthogonal_fst_QR_decomposition:
  shows "pairwise orthogonal (columns (fst (QR_decomposition A)))"
  unfolding pairwise_def columns_def
proof (auto)
  fix i ia
  assume col_not_eq: "column i (fst (QR_decomposition A)) \<noteq> column ia (fst (QR_decomposition A))"
  hence i_not_ia: "i \<noteq> ia" by auto
  from col_not_eq obtain a 
    where "(fst (QR_decomposition A)) $ a $ i \<noteq> (fst (QR_decomposition A)) $ a $ ia"
    unfolding column_def by force
  hence col_not_eq2: " (column i (Gram_Schmidt_matrix A)) \<noteq> (column ia (Gram_Schmidt_matrix A))"
    using col_not_eq unfolding QR_decomposition_def Let_def fst_conv 
    by (metis (lifting) divide_by_norm_def vec_lambda_beta)
  have d1: "column i (fst (QR_decomposition A))
    = (1 / norm (\<chi> ia. Gram_Schmidt_matrix A $ ia $ i)) *\<^sub>R (column i (Gram_Schmidt_matrix A))"
    unfolding QR_decomposition_def Let_def fst_conv
    unfolding divide_by_norm_def column_def normalize_def unfolding vec_eq_iff by auto
  have d2: "column ia (fst (QR_decomposition A))
    = (1 / norm (\<chi> i. Gram_Schmidt_matrix A $ i $ ia)) *\<^sub>R (column ia (Gram_Schmidt_matrix A))"
    unfolding QR_decomposition_def Let_def fst_conv
    unfolding divide_by_norm_def column_def normalize_def unfolding vec_eq_iff by auto
  show "orthogonal (column i (fst (QR_decomposition A))) (column ia (fst (QR_decomposition A)))"
    unfolding d1 d2 apply (rule orthogonal_mult) using orthogonal_Gram_Schmidt_matrix[of A]
    unfolding pairwise_def using col_not_eq2 by auto
qed


lemma qk_uk_norm:
  "(1/(norm (column k ((Gram_Schmidt_matrix A))))) *\<^sub>R (column k ((Gram_Schmidt_matrix A))) 
  = column k (fst(QR_decomposition A))"
  unfolding QR_decomposition_def Let_def fst_conv divide_by_norm_def
  unfolding column_def normalize_def by vector


lemma norm_columns_fst_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes "rank A = ncols A"
  shows "norm (column i (fst (QR_decomposition A))) = 1"
proof -
  have "vec.independent (columns (Gram_Schmidt_matrix A))"
    by (metis assms full_rank_imp_is_basis2 independent_columns_Gram_Schmidt_matrix)
  hence "column i (Gram_Schmidt_matrix A) \<noteq> 0" 
    using vec.dependent_zero[of "columns (Gram_Schmidt_matrix A)"]
    unfolding columns_def by auto
  thus "norm (column i (fst (QR_decomposition A))) = 1"
    unfolding QR_decomposition_def Let_def fst_conv 
    by (rule norm_column_divide_by_norm)
qed



corollary span_fst_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  shows "vec.span (columns A) = vec.span (columns (fst (QR_decomposition A)))"
  unfolding span_Gram_Schmidt_matrix[of A]
  unfolding QR_decomposition_def Let_def fst_conv
  by (metis \<open>span (columns A) = span (columns (Gram_Schmidt_matrix A))\<close> span_columns_divide_by_norm span_vec_eq)

corollary col_space_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  shows "col_space A = col_space (fst (QR_decomposition A))"
  unfolding col_space_def using span_fst_QR_decomposition
  by auto


lemma independent_columns_fst_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes b: "vec.independent (columns A)"
  and c: "card (columns A) = ncols A"
  shows "vec.independent (columns (fst (QR_decomposition A))) 
  \<and> card (columns (fst (QR_decomposition A))) = ncols A"
proof -
  have r: "rank A = ncols A" thm is_basis_imp_full_rank
  proof -
    have "rank A = col_rank A" unfolding rank_col_rank ..
    also have "... = vec.dim (col_space A)" unfolding col_rank_def ..
    also have "... = card (columns A)"
      unfolding col_space_def using b
      by (rule vec.dim_span_eq_card_independent)
    also have "... = ncols A" using c .
    finally show ?thesis .
  qed
  have "vec.independent (columns (fst (QR_decomposition A)))" 
    by (metis b c col_rank_def col_space_QR_decomposition col_space_def 
      full_rank_imp_is_basis2 vec.indep_card_eq_dim_span ncols_def rank_col_rank)
  moreover have "card (columns (fst (QR_decomposition A))) = ncols A" 
    by (metis col_space_QR_decomposition full_rank_imp_is_basis2 ncols_def r rank_eq_dim_col_space')
  ultimately show ?thesis by simp
qed


lemma orthogonal_matrix_fst_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "transpose (fst (QR_decomposition A)) ** (fst (QR_decomposition A)) = mat 1"
proof (unfold vec_eq_iff, clarify, unfold mat_1_fun, auto)
  define Q where "Q = fst (QR_decomposition A)"
  have n: "\<forall>i. norm (column i Q) = 1" unfolding Q_def using norm_columns_fst_QR_decomposition[OF r] by auto
  have c: "card (columns Q) = ncols A" unfolding Q_def
    by (metis full_rank_imp_is_basis2 independent_columns_fst_QR_decomposition r)
  have p: "pairwise orthogonal (columns Q)" by (metis Q_def orthogonal_fst_QR_decomposition)
  fix ia
  have "(transpose Q ** Q) $ ia $ ia = column ia Q \<bullet> column ia Q"
    unfolding matrix_matrix_mult_inner_mult unfolding row_transpose ..
  also have "... = 1" using n norm_eq_1 by blast
  finally show "(transpose Q ** Q) $ ia $ ia = 1" .
  fix i
  assume i_not_ia: "i \<noteq> ia"
  have column_i_not_ia: "column i Q \<noteq> column ia Q"
  proof (rule ccontr, simp)
    assume col_i_ia: "column i Q = column ia Q"
    have rw: "(\<lambda>i. column i Q)` (UNIV-{ia}) = {column i Q|i. i\<noteq>ia}" unfolding columns_def by auto
    have "card (columns Q) = card ({column i Q|i. i\<noteq>ia})"
      by (rule bij_betw_same_card[of id], unfold bij_betw_def columns_def, auto, metis col_i_ia i_not_ia)
    also have "... = card ((\<lambda>i. column i Q)` (UNIV-{ia}))" unfolding rw ..
    also have "... \<le> card (UNIV - {ia})" by (metis card_image_le finite_code)
    also have "... < CARD ('n)" by simp
    finally show False using c unfolding ncols_def by simp
  qed
  hence oia: "orthogonal (column i Q) (column ia Q)"
    using p unfolding pairwise_def unfolding columns_def by auto
  have "(transpose Q ** Q) $ i $ ia = column i Q \<bullet> column ia Q"
    unfolding matrix_matrix_mult_inner_mult unfolding row_transpose ..
  also have "... = 0" using oia unfolding orthogonal_def .
  finally show "(transpose Q ** Q) $ i $ ia = 0" .
qed

corollary orthogonal_matrix_fst_QR_decomposition':
  fixes A::"real^'n::{mod_type}^'n::{mod_type}"
  assumes "rank A = ncols A"
  shows "orthogonal_matrix (fst (QR_decomposition A))"
  by (metis assms orthogonal_matrix orthogonal_matrix_fst_QR_decomposition)


lemma column_eq_fst_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  and c: "column i (fst (QR_decomposition A)) = column ia (fst (QR_decomposition A))"
  shows "i = ia"
proof (rule ccontr)
  assume i_not_ia: "i \<noteq> ia"
  have "columns  (fst (QR_decomposition A)) = (\<lambda>x. column x  (fst (QR_decomposition A)))` (UNIV::('n::{mod_type}) set)"
    unfolding columns_def by auto
  also have "... = (\<lambda>x. column x  (fst (QR_decomposition A)))` ((UNIV::('n::{mod_type}) set)-{ia})"
  proof (unfold image_def, auto)  
    fix xa
    show "\<exists>x\<in>UNIV - {ia}. column xa  (fst (QR_decomposition A)) = column x  (fst (QR_decomposition A))"
    proof (cases "xa = ia")
      case True thus ?thesis using c i_not_ia by (metis DiffI UNIV_I empty_iff insert_iff)
    next
      case False thus ?thesis by auto
    qed
  qed
  finally have columns_rw: "columns  (fst (QR_decomposition A)) 
    = (\<lambda>x. column x  (fst (QR_decomposition A))) ` (UNIV - {ia})" .
  have "ncols A = card (columns  (fst (QR_decomposition A)))"
    by (metis full_rank_imp_is_basis2 independent_columns_fst_QR_decomposition r)
  also have "... \<le> card (UNIV - {ia})" unfolding columns_rw by (rule card_image_le, simp)
  also have "... = card (UNIV::'n set) - 1" by (simp add: card_Diff_singleton)
  finally show False unfolding ncols_def
    by (metis Nat.add_0_right Nat.le_diff_conv2 One_nat_def Suc_n_not_le_n add_Suc_right one_le_card_finite)
qed

corollary column_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "column k ((Gram_Schmidt_matrix A)) 
  = (column k A) - (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i < k}. (x \<bullet> (column k A) / (x \<bullet> x)) *\<^sub>R x)"
proof -
  let ?uk="column k ((Gram_Schmidt_matrix A))"
  let ?qk="column k (fst(QR_decomposition A))"
  let ?ak="(column k A)"
  define f where "f x = (1/norm x) *\<^sub>R x" for x :: "real^'m::{mod_type}"
  let ?g="\<lambda>x::real^'m::{mod_type}. (x \<bullet> (column k A) / (x \<bullet> x)) *\<^sub>R x"
  have set_rw: "{column i (fst (QR_decomposition A))|i. i < k} = f`{column i (Gram_Schmidt_matrix A)|i. i < k}"
  proof (auto)
    fix i 
    assume i: "i < k"
    have col_rw: "column i (fst (QR_decomposition A)) = 
      (1/norm (column i (Gram_Schmidt_matrix A))) *\<^sub>R (column i (Gram_Schmidt_matrix A))"
      unfolding QR_decomposition_def Let_def fst_conv divide_by_norm_def column_def normalize_def by vector
    thus "column i (fst (QR_decomposition A)) \<in> f ` {column i (Gram_Schmidt_matrix A) |i. i < k}"
      unfolding f_def using i
      by auto
    show "\<exists>ia. f (column i (Gram_Schmidt_matrix A)) = column ia (fst (QR_decomposition A)) \<and> ia < k"
      by (rule exI[of _ i], simp add: f_def col_rw i)
  qed
  have "(\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x) 
    = (\<Sum>x\<in>(f`{column i (Gram_Schmidt_matrix A)|i. i < k}). (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)" 
    unfolding set_rw ..
  also have "... = sum (?g  \<circ> f) {column i (Gram_Schmidt_matrix A)|i. i < k}"
  proof (rule sum.reindex, unfold inj_on_def, auto)
    fix i ia assume i: "i < k" and ia: "ia < k"
      and f_eq: "f (column i (Gram_Schmidt_matrix A)) = f (column ia (Gram_Schmidt_matrix A))"
    have fi: "f (column i (Gram_Schmidt_matrix A)) = column i (fst (QR_decomposition A))"
      unfolding f_def QR_decomposition_def Let_def fst_conv divide_by_norm_def column_def normalize_def
      by vector
    have fia: "f (column ia (Gram_Schmidt_matrix A)) = column ia (fst (QR_decomposition A))"
      unfolding f_def QR_decomposition_def Let_def fst_conv divide_by_norm_def column_def normalize_def
      by vector
    have "i = ia" using column_eq_fst_QR_decomposition[OF r] f_eq unfolding fi fia by simp
    thus "column i (Gram_Schmidt_matrix A) = column ia (Gram_Schmidt_matrix A)" by simp
  qed
  also have "... =  (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i.
    i < k}. ((1 / norm x) *\<^sub>R x \<bullet> ?ak / ((1 / norm x) *\<^sub>R x \<bullet> (1 / norm x) *\<^sub>R x)) *\<^sub>R (1 / norm x) *\<^sub>R x)" unfolding o_def f_def ..
  also have "... =  (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i.
    i < k}. ((1 / norm x) *\<^sub>R x \<bullet> ?ak)  *\<^sub>R (1 / norm x) *\<^sub>R x)"
  proof (rule sum.cong, simp)
    fix x assume x: "x \<in> {column i (Gram_Schmidt_matrix A) |i. i < k}"
    have "vec.independent {column i (Gram_Schmidt_matrix A) |i. i < k}"
    proof (rule vec.independent_mono[of "columns (Gram_Schmidt_matrix A)"])
      show "vec.independent (columns (Gram_Schmidt_matrix A))"
        using full_rank_imp_is_basis2[of "(Gram_Schmidt_matrix A)"]
        by (metis full_rank_imp_is_basis2 independent_columns_Gram_Schmidt_matrix r)
      show "{column i (Gram_Schmidt_matrix A) |i. i < k} \<subseteq> columns (Gram_Schmidt_matrix A)"
        unfolding columns_def by auto
    qed
    hence "x \<noteq> 0" using vec.dependent_zero[of " {column i (Gram_Schmidt_matrix A) |i. i < k}"] x
      by blast
    hence "((1 / norm x) *\<^sub>R x \<bullet> (1 / norm x) *\<^sub>R x) = 1" by (metis inverse_eq_divide norm_eq_1 norm_sgn sgn_div_norm)
    thus "((1 / norm x) *\<^sub>R x \<bullet> ?ak / ((1 / norm x) *\<^sub>R x \<bullet> (1 / norm x) *\<^sub>R x)) *\<^sub>R (1 / norm x) *\<^sub>R x =
      ((1 / norm x) *\<^sub>R x \<bullet> column k A) *\<^sub>R (1 / norm x) *\<^sub>R x" by auto
  qed
  also have "... = (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i. i < k}. (((x \<bullet> ?ak)) / (x \<bullet> x)) *\<^sub>R x)"
  proof (rule sum.cong, simp)
    fix x
    assume x: "x \<in> {column i (Gram_Schmidt_matrix A) |i. i < k}"
    show "((1 / norm x) *\<^sub>R x \<bullet> column k A) *\<^sub>R (1 / norm x) *\<^sub>R x = (x \<bullet> column k A / (x \<bullet> x)) *\<^sub>R x"
      by (metis (hide_lams, no_types) mult.right_neutral inner_commute inner_scaleR_right 
        norm_cauchy_schwarz_eq scaleR_one scaleR_scaleR times_divide_eq_right times_divide_times_eq)
  qed
  finally have "?ak - (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)
    = ?ak - (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i. i < k}. (((x \<bullet> ?ak)) / (x \<bullet> x)) *\<^sub>R x)" by auto
  also have "... = ?uk" using column_Gram_Schmidt_matrix[of k A] by auto
  finally show ?thesis ..
qed

lemma column_QR_decomposition':
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "(column k A) = column k ((Gram_Schmidt_matrix A)) 
  + (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i < k}. (x \<bullet> (column k A) / (x \<bullet> x)) *\<^sub>R x)"
  using column_QR_decomposition[OF r] by simp


lemma norm_uk_eq:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "norm (column k ((Gram_Schmidt_matrix A))) = ((column k (fst(QR_decomposition A))) \<bullet> (column k A))"
proof -
  let ?uk="column k ((Gram_Schmidt_matrix A))"
  let ?qk="column k (fst(QR_decomposition A))"
  let ?ak="(column k A)"
  have sum_rw: "(?uk \<bullet> (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)) = 0"
  proof -
    have "(?uk \<bullet> (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x))
      = ((\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i. i < k}. ?uk \<bullet> ((x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)))" 
      unfolding inner_sum_right ..
    also have "... = (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i. i < k}. ((x \<bullet> ?ak / (x \<bullet> x)) * (?uk \<bullet> x)))"
      unfolding inner_scaleR_right ..
    also have "... = 0"
    proof (rule sum.neutral, clarify)
      fix x i assume "i<k" 
      hence "?uk \<bullet> column i (Gram_Schmidt_matrix A) = 0" 
        by (metis less_irrefl r scaleR_columns_Gram_Schmidt_matrix)
      thus "column i (Gram_Schmidt_matrix A) \<bullet> ?ak / (column i (Gram_Schmidt_matrix A) \<bullet> column i (Gram_Schmidt_matrix A)) *
        (?uk \<bullet> column i (Gram_Schmidt_matrix A)) = 0" by auto
    qed
    finally show ?thesis .
  qed
  have "?qk \<bullet> ?ak = ((1/(norm ?uk)) *\<^sub>R ?uk) \<bullet> ?ak" unfolding qk_uk_norm ..
  also have "... = (1/(norm ?uk)) * (?uk \<bullet> ?ak)" unfolding inner_scaleR_left ..
  also have "... = 
    (1/(norm ?uk)) * (?uk \<bullet> (?uk + (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)))"
    using column_Gram_Schmidt_matrix2[of k A] by auto
  also have "... = (1/(norm ?uk)) * ((?uk \<bullet> ?uk) + (?uk \<bullet> (\<Sum>x\<in>{column i (Gram_Schmidt_matrix A) |i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)))"
    unfolding inner_add_right ..
  also have "... = (1/(norm ?uk)) * (?uk \<bullet> ?uk)" unfolding sum_rw by auto
  also have "... = norm ?uk"
    by (metis abs_of_nonneg divide_eq_imp div_by_0 inner_commute inner_ge_zero inner_real_def 
      norm_mult_vec real_inner_1_right real_norm_def times_divide_eq_right)
  finally show ?thesis ..
qed

corollary column_QR_decomposition2:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "(column k A) 
  = (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i \<le> k}. (x \<bullet> (column k A)) *\<^sub>R x)"
proof -
  let ?uk="column k ((Gram_Schmidt_matrix A))"
  let ?qk="column k (fst(QR_decomposition A))"
  let ?ak="(column k A)"
  have set_rw: "{column i (fst (QR_decomposition A))|i. i \<le> k} 
    = insert (column k (fst (QR_decomposition A))) {column i (fst (QR_decomposition A))|i. i < k}"
    by (auto, metis less_linear not_less)
  have uk_norm_uk_qk: "?uk = norm ?uk *\<^sub>R ?qk"
  proof -
    have "vec.independent (columns (Gram_Schmidt_matrix A))"
      by (metis full_rank_imp_is_basis2 independent_columns_Gram_Schmidt_matrix r)
    moreover have "?uk \<in> columns (Gram_Schmidt_matrix A)" unfolding columns_def by auto
    ultimately have "?uk \<noteq> 0"
      using vec.dependent_zero[of "columns (Gram_Schmidt_matrix A)"] unfolding columns_def by auto    
    hence norm_not_0: "norm ?uk \<noteq> 0" unfolding norm_eq_zero .
    have "norm (?uk) *\<^sub>R ?qk = (norm ?uk) *\<^sub>R ((1 / norm ?uk) *\<^sub>R ?uk)" using qk_uk_norm[of k A] by simp
    also have "... = ((norm ?uk) * (1 / norm ?uk)) *\<^sub>R ?uk" unfolding scaleR_scaleR ..
    also have "... = ?uk" using norm_not_0 by auto
    finally show ?thesis ..
  qed
  have norm_qk_1: "?qk  \<bullet> ?qk = 1" 
    using norm_eq_1 norm_columns_fst_QR_decomposition[OF r]
    by auto
  have "?ak = ?uk + (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)"
    using column_QR_decomposition'[OF r] by auto
  also have "... = (norm ?uk *\<^sub>R ?qk)  + (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)"
    using uk_norm_uk_qk by simp
  also have "... = ((?qk \<bullet> ?ak) *\<^sub>R ?qk)  
    + (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)"
    unfolding norm_uk_eq[OF r] ..
  also have "... = ((?qk \<bullet> ?ak)/(?qk \<bullet> ?qk)) *\<^sub>R ?qk
    + (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)" using norm_qk_1 by fastforce
  also have "... = (\<Sum>x\<in>insert ?qk {column i (fst (QR_decomposition A))|i. i < k}. (x \<bullet> ?ak / (x \<bullet> x)) *\<^sub>R x)"
  proof (rule sum.insert[symmetric])
    show "finite {column i (fst (QR_decomposition A)) |i. i < k}" by simp
    show "column k (fst (QR_decomposition A)) \<notin> {column i (fst (QR_decomposition A)) |i. i < k}"
    proof (rule ccontr, simp)
      assume "\<exists>i. column k (fst (QR_decomposition A)) = column i (fst (QR_decomposition A)) \<and> i < k"
      from this obtain i where col_eq: "column k (fst (QR_decomposition A)) = column i (fst (QR_decomposition A))"
        and i_less_k: "i < k" by blast
      show False using column_eq_fst_QR_decomposition[OF r col_eq] i_less_k by simp
    qed
  qed
  also have "... = (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i \<le> k}. (x \<bullet> (column k A)) *\<^sub>R x)"
  proof (rule sum.cong, simp add: set_rw)
    fix x assume x: "x \<in> {column i (fst (QR_decomposition A)) |i. i \<le> k}"
    from this obtain i where i: "x=column i (fst (QR_decomposition A))" by blast
    hence "(x \<bullet> x) = 1" using norm_eq_1 norm_columns_fst_QR_decomposition[OF r]
      by auto
    thus "(x \<bullet> column k A / (x \<bullet> x)) *\<^sub>R x = (x \<bullet> column k A) *\<^sub>R x" by simp
  qed
  finally show ?thesis .
qed


lemma orthogonal_columns_fst_QR_decomposition:
  assumes i_not_ia: "(column i (fst (QR_decomposition A))) \<noteq> (column ia (fst (QR_decomposition A)))"
  shows "(column i (fst (QR_decomposition A)) \<bullet> column ia (fst (QR_decomposition A))) = 0"
proof -
  have i: "column i (fst (QR_decomposition A)) \<in> columns (fst (QR_decomposition A))" unfolding columns_def by auto
  have ia: "column ia (fst (QR_decomposition A)) \<in> columns (fst (QR_decomposition A))" unfolding columns_def by auto
  show ?thesis
    using orthogonal_fst_QR_decomposition[of A] i ia i_not_ia unfolding pairwise_def orthogonal_def
    by auto
qed

lemma scaler_column_fst_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes i: "i>j"
  and r: "rank A = ncols A"
  shows "column i (fst (QR_decomposition A)) \<bullet> column j A = 0"
proof -
  have "column i (fst(QR_decomposition A)) \<bullet> column j A 
    = column i (fst (QR_decomposition A)) \<bullet> (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i \<le> j}. (x \<bullet> (column j A)) *\<^sub>R x)"
    using column_QR_decomposition2[OF r] by presburger
  also have "... = (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i \<le> j}. 
    column i (fst (QR_decomposition A)) \<bullet> (x \<bullet> (column j A)) *\<^sub>R x)" unfolding real_inner_class.inner_sum_right ..
  also have "... = (\<Sum>x\<in>{column i (fst (QR_decomposition A))|i. i \<le> j}. 
    (x \<bullet> (column j A)) *(column i (fst (QR_decomposition A)) \<bullet> x))" unfolding real_inner_class.inner_scaleR_right ..
  also have "... = 0"
  proof (rule sum.neutral, clarify)
    fix ia assume ia: "ia \<le> j"
    have i_not_ia: "i \<noteq> ia" using i ia by simp
    hence "(column i (fst (QR_decomposition A)) \<noteq> column ia (fst (QR_decomposition A)))"
      by (metis column_eq_fst_QR_decomposition r)
    hence "(column i (fst (QR_decomposition A)) \<bullet> column ia (fst (QR_decomposition A))) = 0" 
      by (rule orthogonal_columns_fst_QR_decomposition)
    thus "column ia (fst (QR_decomposition A)) \<bullet> column j A * (column i (fst (QR_decomposition A)) \<bullet> column ia (fst (QR_decomposition A))) = 0"
      by auto
  qed
  finally show ?thesis .
qed

lemma R_Qi_Aj:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  shows "(snd (QR_decomposition A)) $ i $ j = column i (fst (QR_decomposition A)) \<bullet> column j A"
  unfolding QR_decomposition_def Let_def snd_conv matrix_matrix_mult_inner_mult 
  unfolding row_transpose by auto

lemma sums_columns_Q_0:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "(\<Sum>x\<in>{column i (fst (QR_decomposition A)) |i. i>b}. x \<bullet> column b A * x $ a) = 0"
proof (rule sum.neutral, auto) 
  fix i assume "b<i"
  thus "column i (fst (QR_decomposition A)) \<bullet> column b A = 0"
    by (rule scaler_column_fst_QR_decomposition, simp add: r)
qed

lemma QR_decomposition_mult:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "A = (fst (QR_decomposition A)) ** (snd (QR_decomposition A))"
proof -
  have "\<forall>b. column b A = column b ((fst (QR_decomposition A)) ** (snd (QR_decomposition A)))"
  proof (clarify)
    fix b
    have "(fst (QR_decomposition A) ** snd (QR_decomposition A))  
      =  (\<chi> i j. \<Sum>k\<in>UNIV. fst (QR_decomposition A) $ i $ k * (column k (fst (QR_decomposition A)) \<bullet> column j A))"
      unfolding matrix_matrix_mult_def R_Qi_Aj by auto
    hence "column b ((fst (QR_decomposition A) ** snd (QR_decomposition A))) = 
      column b ((\<chi> i j. \<Sum>k\<in>UNIV. fst (QR_decomposition A) $ i $ k * (column k (fst (QR_decomposition A)) \<bullet> column j A)))"
      by auto
    also have "... = (\<Sum>x\<in>{column i (fst (QR_decomposition A)) |i. i \<le> b}. (x \<bullet> column b A) *\<^sub>R x)"
    proof (subst column_def, subst vec_eq_iff, auto)
      fix a 
      define f where "f i = column i (fst (QR_decomposition A))" for i
      define g where "g x = (THE i. x = column i (fst (QR_decomposition A)))" for x
      have f_eq: "f`UNIV = {column i (fst (QR_decomposition A)) |i. i\<in>UNIV}" unfolding f_def by auto
      have inj_f: "inj f"
        by (metis inj_on_def f_def column_eq_fst_QR_decomposition r)
      have "(\<Sum>x\<in>{column i (fst (QR_decomposition A)) |i. i \<le> b}. x \<bullet> column b A * x $ a) 
        = (\<Sum>x\<in>{column i (fst (QR_decomposition A)) |i. i\<in>UNIV}. x \<bullet> column b A * x $ a)"
      proof -
        let ?c= "{column i (fst (QR_decomposition A)) |i. i\<in>UNIV}"
        let ?d= "{column i (fst (QR_decomposition A)) |i. i\<le>b}"
        let ?f = "{column i (fst (QR_decomposition A)) |i. i>b}"
        have set_rw: "?c = ?d \<union> ?f" by force
        have "(\<Sum>x\<in>?c. x \<bullet> column b A * x $ a) 
          = (\<Sum>x\<in>(?d \<union> ?f). x \<bullet> column b A * x $ a)" using set_rw by simp
        also have "... = (\<Sum>x\<in>?d. x \<bullet> column b A * x $ a) + (\<Sum>x\<in>?f. x \<bullet> column b A * x $ a)" 
          by (rule sum.union_disjoint, auto, metis f_def inj_eq inj_f not_le)
        also have "... = (\<Sum>x\<in>?d. x \<bullet> column b A * x $ a)" using sums_columns_Q_0[OF r] by auto
        finally show ?thesis ..
      qed
      also have "... = (\<Sum>x\<in>f`UNIV. x \<bullet> column b A * x $ a)" using f_eq by auto
      also have "... = (\<Sum>k\<in>UNIV. fst (QR_decomposition A) $ a $ k * (column k (fst (QR_decomposition A)) \<bullet> column b A))"
        unfolding sum.reindex[OF inj_f] unfolding f_def column_def by (rule sum.cong, simp_all)
      finally show " (\<Sum>k\<in>UNIV. fst (QR_decomposition A) $ a $ k * (column k (fst (QR_decomposition A)) \<bullet> column b A)) =
        (\<Sum>x\<in>{column i (fst (QR_decomposition A)) |i. i \<le> b}. x \<bullet> column b A * x $ a)" ..
    qed
    also have "... = column b A"
      using column_QR_decomposition2[OF r] by simp
    finally show "column b A = column b (fst (QR_decomposition A) ** snd (QR_decomposition A))" ..
  qed
  thus ?thesis unfolding column_def vec_eq_iff by auto
qed


lemma upper_triangular_snd_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "upper_triangular (snd (QR_decomposition A))"
proof (unfold upper_triangular_def, auto)
  fix i j::'n
  assume j_less_i: "j < i"
  have "snd (QR_decomposition A) $ i $ j = column i (fst (QR_decomposition A)) \<bullet> column j A"
    unfolding QR_decomposition_def Let_def fst_conv snd_conv
    unfolding matrix_matrix_mult_inner_mult row_transpose ..
  also have "... = 0" using scaler_column_fst_QR_decomposition[OF j_less_i r] .
  finally show "snd (QR_decomposition A) $ i $ j = 0" by auto
qed


lemma upper_triangular_invertible:
  fixes A :: "real^'n::{finite,wellorder}^'n::{finite,wellorder}"
  assumes u: "upper_triangular A"
  and d: "\<forall>i. A $ i $ i \<noteq> 0" 
  shows "invertible A"
proof -
  have det_R: "det A = (prod (\<lambda>i. A$i$i) (UNIV::'n set))"
    using det_upperdiagonal u unfolding upper_triangular_def by blast
  also have "... \<noteq> 0" using d by auto
  finally show ?thesis by (metis invertible_det_nz)
qed


lemma invertible_snd_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "invertible (snd (QR_decomposition A))"
proof (rule upper_triangular_invertible)
  show "upper_triangular (snd (QR_decomposition A))"
    using upper_triangular_snd_QR_decomposition[OF r] .
  show "\<forall>i. snd (QR_decomposition A) $ i $ i \<noteq> 0"
  proof (rule allI)
    fix i
    have ind: "vec.independent (columns (Gram_Schmidt_matrix A))"
      by (metis full_rank_imp_is_basis2
        independent_columns_Gram_Schmidt_matrix r)
    hence zero_not_in: "0 \<notin> (columns (Gram_Schmidt_matrix A))" by (metis vec.dependent_zero)
    hence c:"column i (Gram_Schmidt_matrix A) \<noteq> 0" unfolding columns_def by simp
    have "snd (QR_decomposition A) $ i $ i = column i (fst (QR_decomposition A)) \<bullet> column i A"
      unfolding QR_decomposition_def Let_def snd_conv fst_conv
      unfolding matrix_matrix_mult_inner_mult
      unfolding row_transpose ..
    also have "... = norm (column i (Gram_Schmidt_matrix A))"
      unfolding norm_uk_eq[OF r, symmetric] ..
    also have "... \<noteq> 0" by (rule ccontr, simp add: c)
    finally show "snd (QR_decomposition A) $ i $ i \<noteq> 0" .
  qed
qed

lemma QR_decomposition:
  fixes A::"real^'n::{mod_type}^'m::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "A = fst (QR_decomposition A) ** snd (QR_decomposition A) \<and>
  pairwise orthogonal (columns (fst (QR_decomposition A))) \<and> 
  (\<forall>i. norm (column i (fst (QR_decomposition A))) = 1) \<and>
  (transpose (fst (QR_decomposition A))) ** (fst (QR_decomposition A)) = mat 1 \<and>
  vec.independent (columns (fst (QR_decomposition A))) \<and> 
  col_space A = col_space (fst (QR_decomposition A)) \<and>
  card (columns A) = card (columns (fst (QR_decomposition A))) \<and>
  invertible (snd (QR_decomposition A)) \<and>
  upper_triangular (snd (QR_decomposition A))"
  by (metis QR_decomposition_mult col_space_def full_rank_imp_is_basis2 
    independent_columns_fst_QR_decomposition invertible_snd_QR_decomposition 
    norm_columns_fst_QR_decomposition orthogonal_fst_QR_decomposition 
    orthogonal_matrix_fst_QR_decomposition r span_fst_QR_decomposition 
    upper_triangular_snd_QR_decomposition)


lemma QR_decomposition_square:
  fixes A::"real^'n::{mod_type}^'n::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "A = fst (QR_decomposition A) ** snd (QR_decomposition A) \<and>
  orthogonal_matrix (fst (QR_decomposition A)) \<and>
  upper_triangular (snd (QR_decomposition A)) \<and>
  invertible (snd (QR_decomposition A)) \<and>    
  pairwise orthogonal (columns (fst (QR_decomposition A))) \<and> 
  (\<forall>i. norm (column i (fst (QR_decomposition A))) = 1) \<and>      
  vec.independent (columns (fst (QR_decomposition A))) \<and> 
  col_space A = col_space (fst (QR_decomposition A)) \<and>
  card (columns A) = card (columns (fst (QR_decomposition A)))"
  by (metis QR_decomposition orthogonal_matrix_fst_QR_decomposition' r)


text\<open>QR for computing determinants\<close>

lemma det_QR_decomposition:
  fixes A::"real^'n::{mod_type}^'n::{mod_type}"
  assumes r: "rank A = ncols A"
  shows "\<bar>det A\<bar> = \<bar>(prod (\<lambda>i. snd(QR_decomposition A)$i$i) (UNIV::'n set))\<bar>"
proof -
  let ?Q="fst(QR_decomposition A)"
  let ?R="snd(QR_decomposition A)"
  have det_R: "det ?R = (prod (\<lambda>i. snd(QR_decomposition A)$i$i) (UNIV::'n set))"
    apply (rule det_upperdiagonal)
    using upper_triangular_snd_QR_decomposition[OF r]
    unfolding upper_triangular_def by simp
  have "\<bar>det A\<bar> = \<bar>det ?Q * det ?R\<bar>" by (metis QR_decomposition_mult det_mul r)
  also have "... = \<bar>det ?Q\<bar> * \<bar>det ?R\<bar>" unfolding abs_mult ..
  also have "... = 1 * \<bar>det ?R\<bar>" using det_orthogonal_matrix[OF orthogonal_matrix_fst_QR_decomposition'[OF r]]
    by auto
  also have "... = \<bar>det ?R\<bar>" by simp
  also have "... = \<bar>(prod (\<lambda>i. snd(QR_decomposition A)$i$i) (UNIV::'n set))\<bar>" unfolding det_R ..
  finally show ?thesis .  
qed

end
