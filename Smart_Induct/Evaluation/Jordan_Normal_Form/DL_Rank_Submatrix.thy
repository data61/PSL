(* Author: Alexander Bentkamp, Universität des Saarlandes
*)

section \<open>Rank and Submatrices\<close>

theory DL_Rank_Submatrix
imports DL_Rank DL_Submatrix Matrix
begin

lemma row_submatrix_UNIV:
assumes "i < card {i. i < dim_row A \<and> i \<in> I}"
shows "row (submatrix A I UNIV) i = row A (pick I i)"
proof (rule eq_vecI)
  show dim_eq:"dim_vec (row (submatrix A I UNIV) i) = dim_vec (row A (pick I i))"
    unfolding carrier_vecD[OF row_carrier] dim_submatrix by auto
  fix j assume "j < dim_vec (row A (pick I i))"
  then have "j < dim_col (submatrix A I UNIV)" "j < dim_col A" "j < card {j. j < dim_col A \<and> j \<in> UNIV}" using dim_eq by auto
  show "row (submatrix A I UNIV) i $ j = row A (pick I i) $ j"
    unfolding row_def index_vec[OF \<open>j < dim_col (submatrix A I UNIV)\<close>] index_vec[OF \<open>j < dim_col A\<close>]
    using submatrix_index[OF assms \<open>j < card {j. j < dim_col A \<and> j \<in> UNIV}\<close>] using pick_UNIV by auto
qed

lemma distinct_cols_submatrix_UNIV:
assumes "distinct (cols (submatrix A I UNIV))"
shows "distinct (cols A)"
using assms proof (rule contrapos_pp)
  assume "\<not> distinct (cols A)"
  then obtain i j where "i < dim_col A" "j < dim_col A" "(cols A)!i = (cols A)!j" "i\<noteq>j"
    using distinct_conv_nth cols_length by metis
  have "i < dim_col (submatrix A I UNIV)" "j < dim_col (submatrix A I UNIV)"
    unfolding dim_submatrix using \<open>i < dim_col A\<close> \<open>j < dim_col A\<close>by simp_all
  then have "i < length (cols (submatrix A I UNIV))" "j < length (cols (submatrix A I UNIV))"
    unfolding cols_length by simp_all
  have "(cols (submatrix A I UNIV))!i = (cols (submatrix A I UNIV))!j"
  proof (rule eq_vecI)
    show "dim_vec (cols (submatrix A I UNIV) ! i) = dim_vec (cols (submatrix A I UNIV) ! j)"
      by (simp add: \<open>i < dim_col (submatrix A I UNIV)\<close> \<open>j < dim_col (submatrix A I UNIV)\<close>)
    fix k assume "k < dim_vec (cols (submatrix A I UNIV) ! j)"
    then have "k < dim_row (submatrix A I UNIV)"
      using \<open>j < length (cols (submatrix A I UNIV))\<close>  by auto
    then have  "k < card {j. j < dim_row A \<and> j \<in> I}"  using dim_submatrix(1) by metis
    have i_transfer:"cols (submatrix A I UNIV) ! i $ k = (cols A) ! i $ (pick I k)"
      unfolding cols_nth[OF \<open>i < dim_col (submatrix A I UNIV)\<close>] col_def index_vec[OF \<open>k < dim_row (submatrix A I UNIV)\<close>]
      unfolding submatrix_index[OF \<open>k < card {j. j < dim_row A \<and> j \<in> I}\<close> \<open>i < dim_col (submatrix A I UNIV)\<close>[unfolded dim_submatrix]]
      unfolding pick_UNIV cols_nth[OF \<open>i < dim_col A\<close>] col_def index_vec[OF pick_le[OF \<open>k < card {j. j < dim_row A \<and> j \<in> I}\<close>]]
      by metis
    have j_transfer:"cols (submatrix A I UNIV) ! j $ k = (cols A) ! j $ (pick I k)"
      unfolding cols_nth[OF \<open>j < dim_col (submatrix A I UNIV)\<close>] col_def index_vec[OF \<open>k < dim_row (submatrix A I UNIV)\<close>]
      unfolding submatrix_index[OF \<open>k < card {j. j < dim_row A \<and> j \<in> I}\<close> \<open>j < dim_col (submatrix A I UNIV)\<close>[unfolded dim_submatrix]]
      unfolding pick_UNIV cols_nth[OF \<open>j < dim_col A\<close>] col_def index_vec[OF pick_le[OF \<open>k < card {j. j < dim_row A \<and> j \<in> I}\<close>]]
      by metis
    show "cols (submatrix A I UNIV) ! i $ k = cols (submatrix A I UNIV) ! j $ k"
      using \<open>cols A ! i = cols A ! j\<close> i_transfer j_transfer by auto
  qed
  then show "\<not> distinct (cols (submatrix A I UNIV))" unfolding distinct_conv_nth
    using \<open>i < length (cols (submatrix A I UNIV))\<close> \<open>j < length (cols (submatrix A I UNIV))\<close> \<open>i \<noteq> j\<close> by blast
qed

lemma cols_submatrix_subset: "set (cols (submatrix A UNIV J)) \<subseteq> set (cols A)"
proof
  fix c assume "c \<in> set (cols (submatrix A UNIV J))"
  then obtain j where "j < length (cols (submatrix A UNIV J))" "cols (submatrix A UNIV J) ! j = c"
    by (meson in_set_conv_nth)
  then have "j < dim_col (submatrix A UNIV J)" by simp
  then have "j < card {j. j < dim_col A \<and> j \<in> J}" by (simp add: dim_submatrix(2))
  have "cols (submatrix A UNIV J) ! j = cols A ! (pick J j)"
    unfolding cols_nth[OF \<open>j < dim_col (submatrix A UNIV J)\<close>] cols_nth[OF pick_le[OF \<open>j < card {j. j < dim_col A \<and> j \<in> J}\<close>]]
  proof (rule eq_vecI)
    show "dim_vec (col (submatrix A UNIV J) j) = dim_vec (col A (pick J j))" unfolding dim_col dim_submatrix by auto
    fix i assume "i < dim_vec (col A (pick J j))"
    then have "i < dim_row A" by simp
    then have "i < dim_row (submatrix A UNIV J)" using \<open>dim_vec (col (submatrix A UNIV J) j) = dim_vec (col A (pick J j))\<close> by auto
    show "col (submatrix A UNIV J) j $ i = col A (pick J j) $ i"
      unfolding col_def index_vec[OF \<open>i < dim_row (submatrix A UNIV J)\<close>] index_vec[OF \<open>i < dim_row A\<close>]
      using submatrix_index by (metis (no_types, lifting) \<open>dim_vec (col (submatrix A UNIV J) j) = dim_vec (col A (pick J j))\<close>
      \<open>i < dim_vec (col A (pick J j))\<close> \<open>j < dim_col (submatrix A UNIV J)\<close> dim_col dim_submatrix(1) dim_submatrix(2) pick_UNIV)
  qed
  then show "c \<in> set (cols A)"
    using \<open>cols (submatrix A UNIV J) ! j = c\<close>
    using pick_le[OF \<open>j < card {j. j < dim_col A \<and> j \<in> J}\<close>] by (metis cols_length nth_mem)
qed

lemma (in vec_space) lin_dep_submatrix_UNIV:
assumes "A \<in> carrier_mat n nc"
assumes "lin_dep (set (cols A))"
assumes "distinct (cols (submatrix A I UNIV))"
shows "LinearCombinations.module.lin_dep class_ring (module_vec TYPE('a) (card {i. i < n \<and> i \<in> I})) (set (cols (submatrix A I UNIV)))"
  (is "LinearCombinations.module.lin_dep class_ring ?M (set ?S')")
proof -
  obtain v where 2:"v \<in> carrier_vec nc" and 3:"v \<noteq> 0\<^sub>v nc" and "A *\<^sub>v v = 0\<^sub>v n"
    using vec_space.lin_depE[OF assms(1) assms(2) distinct_cols_submatrix_UNIV[OF assms(3)]] by auto
  have 1: "submatrix A I UNIV \<in> carrier_mat (card {i. i < n \<and> i \<in> I}) nc"
    apply (rule carrier_matI) unfolding dim_submatrix using \<open>A \<in> carrier_mat n nc\<close> by auto
  have 4:"submatrix A I UNIV *\<^sub>v v = 0\<^sub>v (card {i. i < n \<and> i \<in> I})"
  proof (rule eq_vecI)
    show dim_eq:"dim_vec (submatrix A I UNIV *\<^sub>v v) = dim_vec (0\<^sub>v (card {i. i < n \<and> i \<in> I}))" using "1" by auto
    fix i assume "i < dim_vec (0\<^sub>v (card {i. i < n \<and> i \<in> I}))"
    then have i_le:"i < card {i. i < n \<and> i \<in> I}" by auto
    have "(submatrix A I UNIV *\<^sub>v v) $ i = row (submatrix A I UNIV) i \<bullet> v" using dim_eq i_le by auto
    also have "... = row A (pick I i) \<bullet> v" using row_submatrix_UNIV
      by (metis (no_types, lifting)  dim_eq dim_mult_mat_vec dim_submatrix(1) \<open>i < dim_vec (0\<^sub>v (card {i. i < n \<and> i \<in> I}))\<close>)
    also have "... = 0"
      using \<open>A *\<^sub>v v = 0\<^sub>v n\<close> i_le[THEN pick_le] by (metis assms(1) index_mult_mat_vec carrier_matD(1) index_zero_vec(1))
    also have "... = 0\<^sub>v (card {i. i < n \<and> i \<in> I}) $ i" by (simp add: i_le)
    finally show "(submatrix A I UNIV *\<^sub>v v) $ i = 0\<^sub>v (card {i. i < n \<and> i \<in> I}) $ i" by metis
  qed
  show ?thesis using vec_space.lin_depI[OF 1 2 3 4] using assms(3) by auto
qed

lemma (in vec_space) rank_gt_minor:
assumes "A \<in> carrier_mat n nc"
assumes "det (submatrix A I J) \<noteq> 0"
shows "card {j. j < nc \<and> j \<in> J} \<le> rank A"
proof -
  have square:"dim_row (submatrix A I J) = dim_col (submatrix A I J)"
   using det_def \<open>det (submatrix A I J) \<noteq> 0\<close> by metis
  then have full_rank:"vec_space.rank (dim_row (submatrix A I J)) (submatrix A I J) = dim_row (submatrix A I J)"
   using vec_space.low_rank_det_zero assms(2) carrier_matI by auto
  then have distinct:"distinct (cols (submatrix A I J))" 
    using vec_space.non_distinct_low_rank square less_irrefl carrier_matI by metis
  then have indpt:"LinearCombinations.module.lin_indpt class_ring (module_vec TYPE('a) (dim_row (submatrix A I J))) (set (cols (submatrix A I J)))"
     using vec_space.full_rank_lin_indpt[OF _ full_rank distinct] square by fastforce

  have distinct2: "distinct (cols (submatrix (submatrix A UNIV J) I UNIV))" using submatrix_split distinct by metis
  have indpt2:"LinearCombinations.module.lin_indpt class_ring (module_vec TYPE('a) (card {i. i < n \<and> i \<in> I})) (set (cols (submatrix (submatrix A UNIV J) I UNIV)))"
    using submatrix_split dim_submatrix(1) indpt by (metis (full_types) assms(1) carrier_matD(1))

  have "submatrix A UNIV J \<in> carrier_mat n (dim_col (submatrix A UNIV J))"
    apply (rule carrier_matI) unfolding dim_submatrix(1) using \<open>A \<in> carrier_mat n nc\<close> carrier_matD by simp_all
  have "lin_indpt (set (cols (submatrix A UNIV J)))"
    using indpt2 vec_space.lin_dep_submatrix_UNIV[OF \<open>submatrix A UNIV J \<in> carrier_mat n (dim_col (submatrix A UNIV J))\<close> _ distinct2] by blast
  have distinct3:"distinct (cols (submatrix A UNIV J))" by (metis distinct distinct_cols_submatrix_UNIV submatrix_split)
  show ?thesis using
    rank_ge_card_indpt[OF \<open>A \<in> carrier_mat n nc\<close> cols_submatrix_subset \<open>lin_indpt (set (cols (submatrix A UNIV J)))\<close>,
    unfolded distinct_card[OF distinct3, unfolded cols_length dim_submatrix], unfolded carrier_matD(2)[OF \<open>A \<in> carrier_mat n nc\<close>]]
    by blast
qed

end
