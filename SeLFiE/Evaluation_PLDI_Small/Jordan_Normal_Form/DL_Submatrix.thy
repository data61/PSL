(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Submatrices\<close>

theory DL_Submatrix
imports Matrix DL_Missing_Sublist
begin


section "Submatrix"

definition submatrix :: "'a mat \<Rightarrow> nat set \<Rightarrow> nat set \<Rightarrow> 'a mat" where
"submatrix A I J = mat (card {i. i<dim_row A \<and> i\<in>I}) (card {j. j<dim_col A \<and> j\<in>J}) (\<lambda>(i,j). A $$ (pick I i, pick J j))"

lemma dim_submatrix: "dim_row (submatrix A I J) = card {i. i<dim_row A \<and> i\<in>I}"
                     "dim_col (submatrix A I J) = card {j. j<dim_col A \<and> j\<in>J}"
  unfolding submatrix_def by simp_all

lemma submatrix_index:
assumes "i<card {i. i<dim_row A \<and> i\<in>I}"
assumes "j<card {j. j<dim_col A \<and> j\<in>J}"
shows "submatrix A I J $$ (i,j) = A $$ (pick I i, pick J j)"
  unfolding submatrix_def by (simp add: assms(1) assms(2))

lemma set_le_in:"{a. a < n \<and> a \<in> I} = {a \<in> I. a < n}" by meson

lemma submatrix_index_card:
assumes "i<dim_row A" "j<dim_col A" "i\<in>I" "j\<in>J"
shows "submatrix A I J $$ (card {a\<in>I. a < i}, card {a\<in>J. a < j}) = A $$ (i, j)"
proof -
  have "i = pick I (card {a\<in>I. a < i})"
       "j = pick J (card {a\<in>J. a < j})" using pick_card_in_set assms by auto
  have "{a\<in>I. a < i} \<subset> {i. i < dim_row A \<and> i \<in> I}"
       "{a\<in>J. a < j} \<subset> {j. j < dim_col A \<and> j \<in> J}"
    unfolding set_le_in using \<open>i<dim_row A\<close> \<open>j<dim_col A\<close> Collect_mono less_imp_le less_le_trans \<open>i\<in>I\<close> \<open>j\<in>J\<close> by auto
  then have "card {a\<in>I. a < i} < card {i. i < dim_row A \<and> i \<in> I}"
            "card {a\<in>J. a < j} < card {j. j < dim_col A \<and> j \<in> J}" by (simp_all add: psubset_card_mono)
  then show ?thesis
    using \<open>i = pick I (card {a \<in> I. a < i})\<close> \<open>j = pick J (card {a \<in> J. a < j})\<close> submatrix_index by fastforce
qed

lemma submatrix_split: "submatrix A I J = submatrix (submatrix A UNIV J) I UNIV"
proof (rule eq_matI)
  show "dim_row (submatrix A I J) = dim_row (submatrix (submatrix A UNIV J) I UNIV)"
    by (simp add: dim_submatrix(1))
  show "dim_col (submatrix A I J) = dim_col (submatrix (submatrix A UNIV J) I UNIV)"
    by (simp add: dim_submatrix(2))
  fix i j assume ij_le:"i < dim_row (submatrix (submatrix A UNIV J) I UNIV)" "j < dim_col (submatrix (submatrix A UNIV J) I UNIV)"
  then have ij_le1:"i<card {i. i < dim_row A \<and> i \<in> I}" "j<card {i. i < dim_col A \<and> i \<in> J}"
    by (simp_all add: dim_submatrix)
  then have ij_le2:"i<card {i. i < dim_row (submatrix A UNIV J) \<and> i \<in> I}" "j<card {i. i < dim_col (submatrix A UNIV J) \<and> i \<in> UNIV}"
    by (simp_all add: dim_submatrix)
  then have i_le3:"pick I i<card {i. i < dim_row A \<and> i \<in> UNIV}"
    using ij_le1(1) pick_le by auto
  have j_le3: "pick UNIV j<card {i. i < dim_col A \<and> i \<in> J}" unfolding pick_UNIV by (simp add: ij_le1(2))
  then show "submatrix A I J $$ (i, j) = submatrix (submatrix A UNIV J) I UNIV $$ (i, j)"
    unfolding submatrix_index[OF ij_le1] submatrix_index[OF ij_le2] submatrix_index[OF i_le3 j_le3]
    unfolding pick_UNIV by metis
qed

end
