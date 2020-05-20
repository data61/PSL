(* Title:      Matrices over Bounded Linear Orders
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Matrices over Bounded Linear Orders\<close>

text \<open>
In this theory we characterise relation-algebraic properties of matrices over bounded linear orders (for example, extended real numbers) in terms of the entries in the matrices.
We consider, in particular, the following properties: univalent, injective, total, surjective, mapping, bijective, vector, covector, point, arc, reflexive, coreflexive, irreflexive, symmetric, antisymmetric, asymmetric.
We also consider the effect of composition with the matrix of greatest elements and with coreflexives (tests).
\<close>

theory Linear_Order_Matrices

imports Matrix_Relation_Algebras

begin

class non_trivial_linorder_stone_relation_algebra_expansion = linorder_stone_relation_algebra_expansion + non_trivial
begin

subclass non_trivial_bounded_order ..

end

text \<open>
Before we look at matrices, we generalise selectivity to finite suprema.
\<close>

lemma linorder_finite_sup_selective:
  fixes f :: "'a::finite \<Rightarrow> 'b::linorder_stone_algebra_expansion"
  shows "\<exists>i . (\<Squnion>\<^sub>k f k) = f i"
  apply (induct rule: comp_inf.one_sup_induct)
  apply blast
  using sup_selective by fastforce

lemma linorder_top_finite_sup:
  fixes f :: "'a::finite \<Rightarrow> 'b::linorder_stone_algebra_expansion"
  assumes "\<forall>k . f k \<noteq> top"
    shows "(\<Squnion>\<^sub>k f k) \<noteq> top"
  by (metis assms linorder_finite_sup_selective)

text \<open>
The following results show the effect of composition with the \<open>top\<close> matrix from the left and from the right.
\<close>

lemma comp_top_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "(f \<odot> mtop) (i,j) = (\<Squnion>\<^sub>k f (i,k))"
  apply (unfold times_matrix_def top_matrix_def)
  by (metis (no_types, lifting) case_prod_conv comp_right_one one_def sup_monoid.sum.cong)

lemma top_comp_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "(mtop \<odot> f) (i,j) = (\<Squnion>\<^sub>k f (k,j))"
  apply (unfold times_matrix_def top_matrix_def)
  by (metis (no_types, lifting) case_prod_conv comp_left_one one_def sup_monoid.sum.cong)

text \<open>
We characterise univalent matrices: in each row, at most one entry may be different from \<open>bot\<close>.
\<close>

lemma univalent_linorder_matrix_1:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_stone_relation_algebra.univalent f"
      and "f (i,j) \<noteq> bot"
      and "f (i,k) \<noteq> bot"
    shows "j = k"
proof -
  have "(f\<^sup>t \<odot> f) (j,k) = (\<Squnion>\<^sub>l (f\<^sup>t) (j,l) * f (l,k))"
    by (simp add: times_matrix_def)
  also have "... = (\<Squnion>\<^sub>l (f (l,j))\<^sup>T * f (l,k))"
    by (simp add: conv_matrix_def)
  also have "... = (\<Squnion>\<^sub>l f (l,j) * f (l,k))"
    by simp
  also have "... \<ge> f (i,j) * f (i,k)"
    using comp_inf.ub_sum by fastforce
  finally have "(f\<^sup>t \<odot> f) (j,k) \<noteq> bot"
    using assms(2,3) bot.extremum_uniqueI times_dense by fastforce
  hence "mone (j,k) \<noteq> (bot::'b)"
    by (metis assms(1) bot.extremum_uniqueI less_eq_matrix_def)
  thus ?thesis
    by (metis (mono_tags, lifting) case_prod_conv one_matrix_def)
qed

lemma univalent_linorder_matrix_2:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "\<forall>i j k . f (i,j) \<noteq> bot \<and> f (i,k) \<noteq> bot \<longrightarrow> j = k"
    shows "matrix_stone_relation_algebra.univalent f"
proof -
  show "f\<^sup>t \<odot> f \<preceq> mone"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix j k
    show "(f\<^sup>t \<odot> f) (j,k) \<le> mone (j,k)"
    proof (cases "j = k")
      assume "j = k"
      thus ?thesis
        by (simp add: one_matrix_def)
    next
      assume "j \<noteq> k"
      hence "(\<Squnion>\<^sub>i f (i,j) * f (i,k)) = bot"
        by (metis (no_types, lifting) assms semiring.mult_not_zero sup_monoid.sum.neutral)
      thus ?thesis
        by (simp add: times_matrix_def conv_matrix_def)
    qed
  qed
qed

lemma univalent_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.univalent f \<longleftrightarrow> (\<forall>i j k . f (i,j) \<noteq> bot \<and> f (i,k) \<noteq> bot \<longrightarrow> j = k)"
  using univalent_linorder_matrix_1 univalent_linorder_matrix_2 by auto

text \<open>
Injective matrices can then be characterised by applying converse: in each column, at most one entry may be different from \<open>bot\<close>.
\<close>

lemma injective_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.injective f \<longleftrightarrow> (\<forall>i j k . f (j,i) \<noteq> bot \<and> f (k,i) \<noteq> bot \<longrightarrow> j = k)"
  by (unfold matrix_stone_relation_algebra.injective_conv_univalent univalent_linorder_matrix) (simp add: conv_matrix_def)

text \<open>
Next come total matrices: each row has a \<open>top\<close> entry.
\<close>

lemma total_linorder_matrix_1:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_stone_relation_algebra.total_var f"
    shows "\<exists>j . f (i,j) = top"
proof -
  have "mone (i,i) \<le> (f \<odot> f\<^sup>t) (i,i)"
    using assms less_eq_matrix_def by blast
  hence "top = (f \<odot> f\<^sup>t) (i,i)"
    by (simp add: one_matrix_def top.extremum_unique)
  also have "... = (\<Squnion>\<^sub>j f (i,j) * (f\<^sup>t) (j,i))"
    by (simp add: times_matrix_def)
  also have "... = (\<Squnion>\<^sub>j f (i,j) * f (i,j))"
    by (simp add: conv_matrix_def)
  also have "... = (\<Squnion>\<^sub>j f (i,j))"
    by simp
  finally show ?thesis
    by (metis linorder_top_finite_sup)
qed

lemma total_linorder_matrix_2:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "\<forall>i . \<exists>j . f (i,j) = top"
    shows "matrix_stone_relation_algebra.total_var f"
proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
  fix j k
  show "mone (j,k) \<le> (f \<odot> f\<^sup>t) (j,k)"
  proof (cases "j = k")
    assume "j = k"
    hence "(\<Squnion>\<^sub>i f (j,i) * (f\<^sup>t) (i,k)) = (\<Squnion>\<^sub>i f (j,i))"
      by (simp add: conv_matrix_def)
    also have "... = top"
      by (metis (no_types) assms comp_inf.ub_sum sup.absorb2 sup_top_left)
    finally show ?thesis
      by (simp add: times_matrix_def)
  next
    assume "j \<noteq> k"
    thus ?thesis
      by (simp add: one_matrix_def)
  qed
qed

lemma total_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_bounded_idempotent_semiring.total f \<longleftrightarrow> (\<forall>i . \<exists>j . f (i,j) = top)"
  using total_linorder_matrix_1 total_linorder_matrix_2 matrix_stone_relation_algebra.total_var by auto

text \<open>
Surjective matrices are again characterised by applying converse: each column has a \<open>top\<close> entry.
\<close>

lemma surjective_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_bounded_idempotent_semiring.surjective f \<longleftrightarrow> (\<forall>j . \<exists>i . f (i,j) = top)"
  by (unfold matrix_stone_relation_algebra.surjective_conv_total total_linorder_matrix) (simp add: conv_matrix_def)

text \<open>
A mapping therefore means that each row has exactly one \<open>top\<close> entry and all others are \<open>bot\<close>.
\<close>

lemma mapping_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.mapping f \<longleftrightarrow> (\<forall>i . \<exists>j . f (i,j) = top \<and> (\<forall>k . j \<noteq> k \<longrightarrow> f (i,k) = bot))"
  by (unfold total_linorder_matrix univalent_linorder_matrix) (metis (mono_tags, hide_lams) comp_inf.mult_1_right comp_inf.mult_right_zero)

lemma mapping_linorder_matrix_unique:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.mapping f \<longleftrightarrow> (\<forall>i . \<exists>!j . f (i,j) = top \<and> (\<forall>k . j \<noteq> k \<longrightarrow> f (i,k) = bot))"
  apply (unfold mapping_linorder_matrix)
  using bot_not_top by auto

text \<open>
Conversely, bijective means that each column has exactly one \<open>top\<close> entry and all others are \<open>bot\<close>.
\<close>

lemma bijective_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.bijective f \<longleftrightarrow> (\<forall>j . \<exists>i . f (i,j) = top \<and> (\<forall>k . i \<noteq> k \<longrightarrow> f (k,j) = bot))"
  by (unfold matrix_stone_relation_algebra.bijective_conv_mapping mapping_linorder_matrix) (simp add: conv_matrix_def)

lemma bijective_linorder_matrix_unique:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.bijective f \<longleftrightarrow> (\<forall>j . \<exists>!i . f (i,j) = top \<and> (\<forall>k . i \<noteq> k \<longrightarrow> f (k,j) = bot))"
  by (unfold matrix_stone_relation_algebra.bijective_conv_mapping mapping_linorder_matrix_unique) (simp add: conv_matrix_def)

text \<open>
We derive algebraic characterisations of matrices in which each row has an entry that is different from \<open>bot\<close>.
\<close>

lemma pp_total_linorder_matrix_1:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  assumes "\<ominus>(f \<odot> mtop) = mbot"
    shows "\<exists>j . f (i,j) \<noteq> bot"
proof -
  have "\<not>(\<exists>j . f (i,j) \<noteq> bot) \<Longrightarrow> \<ominus>(f \<odot> mtop) \<noteq> mbot"
  proof -
    assume "\<not>(\<exists>j . f (i,j) \<noteq> bot)"
    hence "top = -(f \<odot> mtop) (i,i)"
      by (simp add: comp_top_linorder_matrix linorder_finite_sup_selective)
    also have "... = (\<ominus>(f \<odot> mtop)) (i,i)"
      by (simp add: uminus_matrix_def)
    finally show "\<ominus>(f \<odot> mtop) \<noteq> mbot"
      by (metis bot_matrix_def bot_not_top)
  qed
  thus ?thesis
    using assms by blast
qed

lemma pp_total_linorder_matrix_2:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "\<forall>i . \<exists>j . f (i,j) \<noteq> bot"
    shows "\<ominus>(f \<odot> mtop) = mbot"
proof (rule ext, rule prod_cases)
  fix i j
  have "(\<ominus>(f \<odot> mtop)) (i,j) = -(\<Squnion>\<^sub>k f (i,k))"
    by (simp add: comp_top_linorder_matrix uminus_matrix_def)
  also have "... = bot"
    by (metis antisym assms bot.extremum comp_inf.ub_sum uminus_def)
  finally show "(\<ominus>(f \<odot> mtop)) (i,j) = mbot (i,j)"
    by (simp add: bot_matrix_def)
qed

lemma pp_total_linorder_matrix_3:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "\<ominus>(f \<odot> mtop) = mbot \<longleftrightarrow> (\<forall>i . \<exists>j . f (i,j) \<noteq> bot)"
  using pp_total_linorder_matrix_1 pp_total_linorder_matrix_2 by auto

lemma pp_total_linorder_matrix:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_bounded_idempotent_semiring.total (\<ominus>\<ominus>f) \<longleftrightarrow> (\<forall>i . \<exists>j . f (i,j) \<noteq> bot)"
  using matrix_stone_relation_algebra.pp_total pp_total_linorder_matrix_1 pp_total_linorder_matrix_2 by auto

lemma pp_mapping_linorder_matrix:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.pp_mapping f \<longleftrightarrow> (\<forall>i . \<exists>j . f (i,j) \<noteq> bot \<and> (\<forall>k . j \<noteq> k \<longrightarrow> f (i,k) = bot))"
  by (metis (mono_tags, hide_lams) pp_total_linorder_matrix univalent_linorder_matrix_1 univalent_linorder_matrix_2)

lemma pp_mapping_linorder_matrix_unique:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.pp_mapping f \<longleftrightarrow> (\<forall>i . \<exists>!j . f (i,j) \<noteq> bot \<and> (\<forall>k . j \<noteq> k \<longrightarrow> f (i,k) = bot))"
  apply (rule iffI)
  using pp_mapping_linorder_matrix apply blast
  by (metis pp_total_linorder_matrix univalent_linorder_matrix)

text \<open>
Next follow matrices in which each column has an entry that is different from \<open>bot\<close>.
\<close>

lemma pp_surjective_linorder_matrix_1:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "\<ominus>(mtop \<odot> f) = mbot \<longleftrightarrow> (\<forall>j . \<exists>i . f (i,j) \<noteq> bot)"
proof -
  have "\<ominus>(mtop \<odot> f) = mbot \<longleftrightarrow> (\<ominus>(mtop \<odot> f))\<^sup>t = mbot\<^sup>t"
    by (metis matrix_stone_relation_algebra.conv_involutive)
  also have "... \<longleftrightarrow> \<ominus>(f\<^sup>t \<odot> mtop) = mbot"
    by (simp add: matrix_stone_relation_algebra.conv_complement matrix_stone_relation_algebra.conv_dist_comp)
  also have "... \<longleftrightarrow> (\<forall>i . \<exists>j . (f\<^sup>t) (i,j) \<noteq> bot)"
    using pp_total_linorder_matrix_3 by auto
  also have "... \<longleftrightarrow> (\<forall>j . \<exists>i . f (i,j) \<noteq> bot)"
    by (simp add: conv_matrix_def)
  finally show ?thesis
    .
qed

lemma pp_surjective_linorder_matrix:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_bounded_idempotent_semiring.surjective (\<ominus>\<ominus>f) \<longleftrightarrow> (\<forall>j . \<exists>i . f (i,j) \<noteq> bot)"
  using matrix_stone_relation_algebra.pp_surjective pp_surjective_linorder_matrix_1 by auto

lemma pp_bijective_linorder_matrix:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.pp_bijective f \<longleftrightarrow> (\<forall>j . \<exists>i . f (i,j) \<noteq> bot \<and> (\<forall>k . i \<noteq> k \<longrightarrow> f (k,j) = bot))"
  by (unfold matrix_stone_relation_algebra.pp_bijective_conv_mapping pp_mapping_linorder_matrix) (simp add: conv_matrix_def)

lemma pp_bijective_linorder_matrix_unique:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.pp_bijective f \<longleftrightarrow> (\<forall>j . \<exists>!i . f (i,j) \<noteq> bot \<and> (\<forall>k . i \<noteq> k \<longrightarrow> f (k,j) = bot))"
  by (unfold matrix_stone_relation_algebra.pp_bijective_conv_mapping pp_mapping_linorder_matrix_unique) (simp add: conv_matrix_def)

text \<open>
The regular matrices are those which contain only \<open>bot\<close> or \<open>top\<close> entries.
\<close>

lemma regular_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_p_algebra.regular f \<longleftrightarrow> (\<forall>e . f e = bot \<or> f e = top)"
proof -
  have "matrix_p_algebra.regular f \<longleftrightarrow> (\<ominus>\<ominus>f = f)"
    by auto
  also have "... \<longleftrightarrow> (\<forall>e . --f e = f e)"
    by (metis uminus_matrix_def ext)
  also have "... \<longleftrightarrow> (\<forall>e . f e = bot \<or> f e = top)"
    by force
  finally show ?thesis
    .
qed

text \<open>
Vectors are precisely the row-constant matrices.
\<close>

lemma vector_linorder_matrix_0:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_bounded_idempotent_semiring.vector f"
    shows "f (i,j) = (\<Squnion>\<^sub>k f (i,k))"
  by (metis assms comp_top_linorder_matrix)

lemma vector_linorder_matrix_1:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_bounded_idempotent_semiring.vector f"
    shows "f (i,j) = f (i,k)"
  by (metis assms vector_linorder_matrix_0)

lemma vector_linorder_matrix_2:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "\<forall>i j k . f (i,j) = f (i,k)"
    shows "matrix_bounded_idempotent_semiring.vector f"
proof (rule ext, rule prod_cases)
  fix i j
  have "(f \<odot> mtop) (i,j) = (\<Squnion>\<^sub>k f (i,k))"
    by (simp add: comp_top_linorder_matrix)
  also have "... = f (i,j)"
    by (metis assms linorder_finite_sup_selective)
  finally show "(f \<odot> mtop) (i,j) = f (i,j)"
    .
qed

lemma vector_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_bounded_idempotent_semiring.vector f \<longleftrightarrow> (\<forall>i j k . f (i,j) = f (i,k))"
  using vector_linorder_matrix_1 vector_linorder_matrix_2 by auto

text \<open>
Hence covectors are precisely the column-constant matrices.
\<close>

lemma covector_linorder_matrix_0:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_bounded_idempotent_semiring.covector f"
    shows "f (i,j) = (\<Squnion>\<^sub>k f (k,j))"
  by (metis assms top_comp_linorder_matrix)

lemma covector_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_bounded_idempotent_semiring.covector f \<longleftrightarrow> (\<forall>i j k . f (i,j) = f (k,j))"
  by (unfold matrix_stone_relation_algebra.covector_conv_vector vector_linorder_matrix) (metis (no_types, lifting) case_prod_conv conv_matrix_def conv_def)

text \<open>
A point is a matrix that has exactly one row, which is constant \<open>top\<close>, and all other rows are constant \<open>bot\<close>.
\<close>

lemma point_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.point f \<longleftrightarrow> (\<exists>i . \<forall>j . f (i,j) = top \<and> (\<forall>k . i \<noteq> k \<longrightarrow> f (k,j) = bot))"
  apply (unfold vector_linorder_matrix bijective_linorder_matrix)
  apply (rule iffI)
  apply metis
  by metis

lemma point_linorder_matrix_unique:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.point f \<longleftrightarrow> (\<exists>!i . \<forall>j . f (i,j) = top \<and> (\<forall>k . i \<noteq> k \<longrightarrow> f (k,j) = bot))"
  apply (unfold vector_linorder_matrix bijective_linorder_matrix)
  apply (rule iffI)
  apply (metis bot_not_top)
  by metis

lemma pp_point_linorder_matrix:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.pp_point f \<longleftrightarrow> (\<exists>i . \<forall>j . f (i,j) \<noteq> bot \<and> (\<forall>k . f (i,j) = f (i,k)) \<and> (\<forall>k . i \<noteq> k \<longrightarrow> f (k,j) = bot))"
  apply (unfold vector_linorder_matrix pp_bijective_linorder_matrix)
  apply (rule iffI)
  apply metis
  by metis

lemma pp_point_linorder_matrix_unique:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.pp_point f \<longleftrightarrow> (\<exists>!i . \<forall>j . f (i,j) \<noteq> bot \<and> (\<forall>k . f (i,j) = f (i,k)) \<and> (\<forall>k . i \<noteq> k \<longrightarrow> f (k,j) = bot))"
  apply (unfold vector_linorder_matrix pp_bijective_linorder_matrix)
  apply (rule iffI)
  apply metis
  by metis

text \<open>
An arc is a matrix that has exactly one \<open>top\<close> entry and all other entries are \<open>bot\<close>.
\<close>

lemma arc_linorder_matrix_1:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_stone_relation_algebra.arc f"
    shows "\<exists>e . f e = top \<and> (\<forall>d . e \<noteq> d \<longrightarrow> f d = bot)"
proof -
  have "matrix_stone_relation_algebra.point (f \<odot> mtop)"
    by (simp add: assms matrix_bounded_idempotent_semiring.vector_mult_closed)
  from this obtain i where 1: "\<forall>j . (f \<odot> mtop) (i,j) = top \<and> (\<forall>k . i \<noteq> k \<longrightarrow> (f \<odot> mtop) (k,j) = bot)"
    using point_linorder_matrix by blast
  have "matrix_stone_relation_algebra.point (f\<^sup>t \<odot> mtop)"
    by (simp add: assms matrix_bounded_idempotent_semiring.vector_mult_closed)
  from this obtain j where "\<forall>i . (f\<^sup>t \<odot> mtop) (j,i) = top \<and> (\<forall>k . j \<noteq> k \<longrightarrow> (f\<^sup>t \<odot> mtop) (k,i) = bot)"
    using point_linorder_matrix by blast
  hence 2: "\<forall>i . (mtop \<odot> f) (i,j) = top \<and> (\<forall>k . j \<noteq> k \<longrightarrow> (mtop \<odot> f) (i,k) = bot)"
    by (metis (no_types) old.prod.case conv_matrix_def conv_def matrix_stone_relation_algebra.conv_dist_comp matrix_stone_relation_algebra.conv_top)
  have 3: "\<forall>i k . j \<noteq> k \<longrightarrow> f (i,k) = bot"
  proof (intro allI, rule impI)
    fix i k
    assume "j \<noteq> k"
    hence "(\<Squnion>\<^sub>l f (l,k)) = bot"
      using 2 by (simp add: top_comp_linorder_matrix)
    thus "f (i,k) = bot"
      by (metis bot.extremum_uniqueI comp_inf.ub_sum)
  qed
  have "(\<Squnion>\<^sub>k f (i,k)) = top"
    using 1 by (simp add: comp_top_linorder_matrix)
  hence 4: "f (i,j) = top"
    using 3 by (metis bot_not_top linorder_finite_sup_selective)
  have "\<forall>k l . k \<noteq> i \<or> l \<noteq> j \<longrightarrow> f (k,l) = bot"
  proof (intro allI, unfold imp_disjL, rule conjI)
    fix k l
    show "k \<noteq> i \<longrightarrow> f (k,l) = bot"
    proof
      assume "k \<noteq> i"
      hence "(\<Squnion>\<^sub>m f (k,m)) = bot"
        using 1 by (simp add: comp_top_linorder_matrix)
      thus "f (k,l) = bot"
        by (metis bot.extremum_uniqueI comp_inf.ub_sum)
    qed
    show "l \<noteq> j \<longrightarrow> f (k,l) = bot"
      using 3 by simp
  qed
  thus ?thesis using 4
    by (metis old.prod.exhaust)
qed

lemma pp_arc_linorder_matrix_2:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "\<exists>e . f e \<noteq> bot \<and> (\<forall>d . e \<noteq> d \<longrightarrow> f d = bot)"
    shows "matrix_stone_relation_algebra.pp_arc f"
proof (unfold matrix_stone_relation_algebra.pp_arc_expanded, intro conjI)
  show "f \<odot> mtop \<odot> f\<^sup>t \<preceq> mone"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j
    show "(f \<odot> mtop \<odot> f\<^sup>t) (i,j) \<le> mone (i,j)"
    proof (cases "i = j")
      assume "i = j"
      thus ?thesis
        by (simp add: one_matrix_def)
    next
      assume "i \<noteq> j"
      hence 1: "\<forall>k l . f (i,k) * f (j,l) = bot"
        by (metis assms Pair_inject semiring.mult_not_zero)
      have "(f \<odot> mtop \<odot> f\<^sup>t) (i,j) = (\<Squnion>\<^sub>l (f \<odot> mtop) (i,l) * (f\<^sup>t) (l,j))"
        by (simp add: times_matrix_def)
      also have "... = (\<Squnion>\<^sub>l (f \<odot> mtop) (i,l) * f (j,l))"
        by (simp add: conv_matrix_def)
      also have "... = (\<Squnion>\<^sub>l (\<Squnion>\<^sub>k f (i,k)) * f (j,l))"
        by (simp add: comp_top_linorder_matrix)
      also have "... = (\<Squnion>\<^sub>l \<Squnion>\<^sub>k f (i,k) * f (j,l))"
        by (metis comp_right_dist_sum)
      also have "... = bot"
        using 1 linorder_finite_sup_selective by simp
      finally show ?thesis
        by simp
    qed
  qed
next
  show "f\<^sup>t \<odot> mtop \<odot> f \<preceq> mone"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j
    show "(f\<^sup>t \<odot> mtop \<odot> f) (i,j) \<le> mone (i,j)"
    proof (cases "i = j")
      assume "i = j"
      thus ?thesis
        by (simp add: one_matrix_def)
    next
      assume "i \<noteq> j"
      hence 2: "\<forall>k l . f (k,i) * f (l,j) = bot"
        by (metis assms Pair_inject semiring.mult_not_zero)
      have "(f\<^sup>t \<odot> mtop \<odot> f) (i,j) = (\<Squnion>\<^sub>l (f\<^sup>t \<odot> mtop) (i,l) * f (l,j))"
        by (simp add: times_matrix_def)
      also have "... = (\<Squnion>\<^sub>l (\<Squnion>\<^sub>k (f\<^sup>t) (i,k)) * f (l,j))"
        by (simp add: comp_top_linorder_matrix)
      also have "... = (\<Squnion>\<^sub>l (\<Squnion>\<^sub>k f (k,i)) * f (l,j))"
        by (simp add: conv_matrix_def)
      also have "... = (\<Squnion>\<^sub>l \<Squnion>\<^sub>k f (k,i) * f (l,j))"
        by (metis comp_right_dist_sum)
      also have "... = bot"
        using 2 linorder_finite_sup_selective by simp
      finally show ?thesis
        by simp
    qed
  qed
next
  show "mtop \<odot> \<ominus>\<ominus>f \<odot> mtop = mtop"
  proof (rule ext, rule prod_cases)
    fix i j
    from assms obtain k l where "f (k,l) \<noteq> bot"
      using prod.collapse by auto
    hence "top = --f (k,l)"
      by simp
    also have "... \<le> (\<Squnion>\<^sub>k --f (k,l))"
      using comp_inf.ub_sum by metis
    also have "... \<le> (\<Squnion>\<^sub>l \<Squnion>\<^sub>k --f (k,l))"
      using comp_inf.ub_sum by simp
    finally have 3: "top \<le> (\<Squnion>\<^sub>l \<Squnion>\<^sub>k --f (k,l))"
      by simp
    have "(mtop \<odot> \<ominus>\<ominus>f \<odot> mtop) (i,j) = (\<Squnion>\<^sub>l (\<Squnion>\<^sub>k top * --f (k,l)) * top)"
      by (simp add: times_matrix_def top_matrix_def uminus_matrix_def)
    also have "... = (\<Squnion>\<^sub>l \<Squnion>\<^sub>k --f (k,l))"
      by (metis (no_types, lifting) sup_monoid.sum.cong comp_inf.mult_1_left times_inf comp_inf.mult_1_right)
    also have "... = top"
      using 3 top.extremum_unique by blast
    finally show "(mtop \<odot> \<ominus>\<ominus>f \<odot> mtop) (i,j) = mtop (i,j)"
      by (simp add: top_matrix_def)
  qed
qed

lemma arc_linorder_matrix_2:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  assumes "\<exists>e . f e = top \<and> (\<forall>d . e \<noteq> d \<longrightarrow> f d = bot)"
    shows "matrix_stone_relation_algebra.arc f"
proof (unfold matrix_stone_relation_algebra.arc_expanded, intro conjI)
  show "f \<odot> mtop \<odot> f\<^sup>t \<preceq> mone"
    by (metis (no_types, lifting) assms bot_not_top matrix_stone_relation_algebra.pp_arc_expanded pp_arc_linorder_matrix_2)
next
  show "f\<^sup>t \<odot> mtop \<odot> f \<preceq> mone"
    by (metis (no_types, lifting) assms bot_not_top matrix_stone_relation_algebra.pp_arc_expanded pp_arc_linorder_matrix_2)
next
  show "mtop \<odot> f \<odot> mtop = mtop"
  proof (rule ext, rule prod_cases)
    fix i j
    from assms obtain k l where "f (k,l) = top"
      using prod.collapse by auto
    hence "(\<Squnion>\<^sub>k f (k,l)) = top"
      by (metis (mono_tags) comp_inf.ub_sum top_unique)
    hence 3: "top \<le> (\<Squnion>\<^sub>l \<Squnion>\<^sub>k f (k,l))"
      by (metis (no_types) comp_inf.ub_sum)
    have "(mtop \<odot> f \<odot> mtop) (i,j) = (\<Squnion>\<^sub>l (\<Squnion>\<^sub>k top * f (k,l)) * top)"
      by (simp add: times_matrix_def top_matrix_def)
    also have "... = (\<Squnion>\<^sub>l \<Squnion>\<^sub>k f (k,l))"
      by (metis (no_types, lifting) sup_monoid.sum.cong comp_inf.mult_1_left times_inf comp_inf.mult_1_right)
    also have "... = top"
      using 3 top.extremum_unique by blast
    finally show "(mtop \<odot> f \<odot> mtop) (i,j) = mtop (i,j)"
      by (simp add: top_matrix_def)
  qed
qed

lemma arc_linorder_matrix:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.arc f \<longleftrightarrow> (\<exists>e . f e = top \<and> (\<forall>d . e \<noteq> d \<longrightarrow> f d = bot))"
  using arc_linorder_matrix_1 arc_linorder_matrix_2 by blast

lemma arc_linorder_matrix_unique:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.arc f \<longleftrightarrow> (\<exists>!e . f e = top \<and> (\<forall>d . e \<noteq> d \<longrightarrow> f d = bot))"
  apply (rule iffI)
  apply (metis (no_types, hide_lams) arc_linorder_matrix bot_not_top)
  using arc_linorder_matrix by blast

lemma pp_arc_linorder_matrix_1:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_stone_relation_algebra.pp_arc f"
    shows "\<exists>e . f e \<noteq> bot \<and> (\<forall>d . e \<noteq> d \<longrightarrow> f d = bot)"
proof -
  have "matrix_stone_relation_algebra.pp_point (f \<odot> mtop)"
    by (simp add: assms matrix_bounded_idempotent_semiring.vector_mult_closed)
  from this obtain i where 1: "\<forall>j . (f \<odot> mtop) (i,j) \<noteq> bot \<and> (\<forall>k . (f \<odot> mtop) (i,j) = (f \<odot> mtop) (i,k)) \<and> (\<forall>k . i \<noteq> k \<longrightarrow> (f \<odot> mtop) (k,j) = bot)"
    by (metis pp_point_linorder_matrix)
  have "matrix_stone_relation_algebra.pp_point (f\<^sup>t \<odot> mtop)"
    by (simp add: assms matrix_bounded_idempotent_semiring.vector_mult_closed)
  from this obtain j where "\<forall>i . (f\<^sup>t \<odot> mtop) (j,i) \<noteq> bot \<and> (\<forall>k . (f\<^sup>t \<odot> mtop) (j,i) = (f\<^sup>t \<odot> mtop) (j,k)) \<and> (\<forall>k . j \<noteq> k \<longrightarrow> (f\<^sup>t \<odot> mtop) (k,i) = bot)"
    by (metis pp_point_linorder_matrix)
  hence 2: "\<forall>i . (mtop \<odot> f) (i,j) \<noteq> bot \<and> (\<forall>k . (mtop \<odot> f) (i,j) = (mtop \<odot> f) (k,j)) \<and> (\<forall>k . j \<noteq> k \<longrightarrow> (mtop \<odot> f) (i,k) = bot)"
    by (metis (no_types) old.prod.case conv_matrix_def conv_def matrix_stone_relation_algebra.conv_dist_comp matrix_stone_relation_algebra.conv_top)
  have 3: "\<forall>i k . j \<noteq> k \<longrightarrow> f (i,k) = bot"
  proof (intro allI, rule impI)
    fix i k
    assume "j \<noteq> k"
    hence "(\<Squnion>\<^sub>l f (l,k)) = bot"
      using 2 by (simp add: top_comp_linorder_matrix)
    thus "f (i,k) = bot"
      by (metis bot.extremum_uniqueI comp_inf.ub_sum)
  qed
  have "(\<Squnion>\<^sub>k f (i,k)) \<noteq> bot"
    using 1 by (simp add: comp_top_linorder_matrix)
  hence 4: "f (i,j) \<noteq> bot"
    using 3 by (metis linorder_finite_sup_selective)
  have "\<forall>k l . k \<noteq> i \<or> l \<noteq> j \<longrightarrow> f (k,l) = bot"
  proof (intro allI, unfold imp_disjL, rule conjI)
    fix k l
    show "k \<noteq> i \<longrightarrow> f (k,l) = bot"
    proof
      assume "k \<noteq> i"
      hence "(\<Squnion>\<^sub>m f (k,m)) = bot"
        using 1 by (simp add: comp_top_linorder_matrix)
      thus "f (k,l) = bot"
        by (metis bot.extremum_uniqueI comp_inf.ub_sum)
    qed
    show "l \<noteq> j \<longrightarrow> f (k,l) = bot"
      using 3 by simp
  qed
  thus ?thesis using 4
    by (metis old.prod.exhaust)
qed

lemma pp_arc_linorder_matrix:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.pp_arc f \<longleftrightarrow> (\<exists>e . f e \<noteq> bot \<and> (\<forall>d . e \<noteq> d \<longrightarrow> f d = bot))"
  using pp_arc_linorder_matrix_1 pp_arc_linorder_matrix_2 by blast

lemma pp_arc_linorder_matrix_unique:
  fixes f :: "('a::finite,'b::non_trivial_linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.pp_arc f \<longleftrightarrow> (\<exists>!e . f e \<noteq> bot \<and> (\<forall>d . e \<noteq> d \<longrightarrow> f d = bot))"
  apply (rule iffI)
  apply (metis (no_types, hide_lams) pp_arc_linorder_matrix)
  using pp_arc_linorder_matrix by blast

text \<open>
Reflexive matrices are those with a constant \<open>top\<close> diagonal.
\<close>

lemma reflexive_linorder_matrix_1:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_idempotent_semiring.reflexive f"
    shows "f (i,i) = top"
proof -
  have "(top::'b) = mone (i,i)"
    by (simp add: one_matrix_def)
  also have "... \<le> f (i,i)"
    using assms less_eq_matrix_def by blast
  finally show ?thesis
    by (simp add: top.extremum_unique)
qed

lemma reflexive_linorder_matrix_2:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "\<forall>i . f (i,i) = top"
    shows "matrix_idempotent_semiring.reflexive f"
proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
  fix i j
  show "mone (i,j) \<le> f (i,j)"
  proof (cases "i = j")
    assume "i = j"
    thus ?thesis
      by (simp add: assms)
  next
    assume "i \<noteq> j"
    hence "(bot::'b) = mone (i,j)"
      by (simp add: one_matrix_def)
    thus ?thesis
      by simp
  qed
qed

lemma reflexive_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_idempotent_semiring.reflexive f \<longleftrightarrow> (\<forall>i . f (i,i) = top)"
  using reflexive_linorder_matrix_1 reflexive_linorder_matrix_2 by auto

text \<open>
Coreflexive matrices are those in which all non-diagonal entries are \<open>bot\<close>.
\<close>

lemma coreflexive_linorder_matrix_1:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_idempotent_semiring.coreflexive f"
      and "i \<noteq> j"
    shows "f (i,j) = bot"
proof -
  have "f (i,j) \<le> mone (i,j)"
    using assms less_eq_matrix_def by blast
  also have "... = bot"
    by (simp add: assms one_matrix_def)
  finally show ?thesis
    by (simp add: bot.extremum_unique)
qed

lemma coreflexive_linorder_matrix_2:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "\<forall>i j . i \<noteq> j \<longrightarrow> f (i,j) = bot"
    shows "matrix_idempotent_semiring.coreflexive f"
proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
  fix i j
  show "f (i,j) \<le> mone (i,j)"
  proof (cases "i = j")
    assume "i = j"
    hence "(top::'b) = mone (i,j)"
      by (simp add: one_matrix_def)
    thus ?thesis
      by simp
  next
    assume "i \<noteq> j"
    thus ?thesis
      by (simp add: assms)
  qed
qed

lemma coreflexive_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_idempotent_semiring.coreflexive f \<longleftrightarrow> (\<forall>i j . i \<noteq> j \<longrightarrow> f (i,j) = bot)"
  using coreflexive_linorder_matrix_1 coreflexive_linorder_matrix_2 by auto

text \<open>
Irreflexive matrices are those with a constant \<open>bot\<close> diagonal.
\<close>

lemma irreflexive_linorder_matrix_1:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_stone_relation_algebra.irreflexive f"
    shows "f (i,i) = bot"
proof -
  have "(top::'b) = mone (i,i)"
    by (simp add: one_matrix_def)
  hence "(bot::'b) = (\<ominus>mone) (i,i)"
    by (simp add: uminus_matrix_def)
  hence "f (i,i) \<le> bot"
    by (metis assms less_eq_matrix_def)
  thus ?thesis
    by (simp add: bot.extremum_unique)
qed

lemma irreflexive_linorder_matrix_2:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "\<forall>i . f (i,i) = bot"
    shows "matrix_stone_relation_algebra.irreflexive f"
proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
  fix i j
  show "f (i,j) \<le> (\<ominus>mone) (i,j)"
  proof (cases "i = j")
    assume "i = j"
    thus ?thesis
      by (simp add: assms)
  next
    assume "i \<noteq> j"
    hence "(bot::'b) = mone (i,j)"
      by (simp add: one_matrix_def)
    hence "(top::'b) = (\<ominus>mone) (i,j)"
      by (simp add: uminus_matrix_def)
    thus ?thesis
      by simp
  qed
qed

lemma irreflexive_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.irreflexive f \<longleftrightarrow> (\<forall>i . f (i,i) = bot)"
  using irreflexive_linorder_matrix_1 irreflexive_linorder_matrix_2 by auto

text \<open>
As usual, symmetric matrices are those which do not change under transposition.
\<close>

lemma symmetric_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.symmetric f \<longleftrightarrow> (\<forall>i j . f (i,j) = f (j,i))"
  by (metis (mono_tags, lifting) case_prod_conv cond_case_prod_eta conv_matrix_def conv_def)

text \<open>
Antisymmetric matrices are characterised as follows: each entry not on the diagonal or its mirror entry across the diagonal must be \<open>bot\<close>.
\<close>

lemma antisymmetric_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.antisymmetric f \<longleftrightarrow> (\<forall>i j . i \<noteq> j \<longrightarrow> f (i,j) = bot \<or> f (j,i) = bot)"
proof -
  have "matrix_stone_relation_algebra.antisymmetric f \<longleftrightarrow> (\<forall>i j . i \<noteq> j \<longrightarrow> f (i,j) \<sqinter> f (j,i) \<le> bot)"
    by (simp add: conv_matrix_def inf_matrix_def less_eq_matrix_def one_matrix_def)
  thus ?thesis
    by (metis (no_types, hide_lams) inf.absorb_iff1 inf.cobounded1 inf_bot_right inf_dense)
qed

text \<open>
For asymmetric matrices the diagonal is included: each entry or its mirror entry across the diagonal must be \<open>bot\<close>.
\<close>

lemma asymmetric_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_stone_relation_algebra.asymmetric f \<longleftrightarrow> (\<forall>i j . f (i,j) = bot \<or> f (j,i) = bot)"
proof -
  have "matrix_stone_relation_algebra.asymmetric f \<longleftrightarrow> (\<forall>i j . f (i,j) \<sqinter> f (j,i) \<le> bot)"
    apply (unfold conv_matrix_def inf_matrix_def conv_def id_def bot_matrix_def)
    by (metis (mono_tags, lifting) bot.extremum bot.extremum_uniqueI case_prod_conv old.prod.exhaust)
  thus ?thesis
    by (metis (no_types, hide_lams) inf.absorb_iff1 inf.cobounded1 inf_bot_right inf_dense)
qed

text \<open>
In a transitive matrix, the weight of one of the edges on an indirect route must be below the weight of the direct edge.
\<close>

lemma transitive_linorder_matrix:
  fixes f :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  shows "matrix_idempotent_semiring.transitive f \<longleftrightarrow> (\<forall>i j k . f (i,k) \<le> f (i,j) \<or> f (k,j) \<le> f (i,j))"
proof -
  have "matrix_idempotent_semiring.transitive f \<longleftrightarrow> (\<forall>i j . (\<Squnion>\<^sub>k f (i,k) * f (k,j)) \<le> f (i,j))"
    by (simp add: times_matrix_def less_eq_matrix_def)
  also have "... \<longleftrightarrow> (\<forall>i j k . f (i,k) * f (k,j) \<le> f (i,j))"
    by (simp add: lub_sum_iff)
  also have "... \<longleftrightarrow> (\<forall>i j k . f (i,k) \<le> f (i,j) \<or> f (k,j) \<le> f (i,j))"
    using inf_less_eq by fastforce
  finally show ?thesis
    .
qed

text \<open>
We finally show the effect of composing with a coreflexive (test) from the left and from the right.
This amounts to a restriction of each row or column to the entry on the diagonal of the coreflexive.
In this case, restrictions are formed by meets.
\<close>

lemma coreflexive_comp_linorder_matrix:
  fixes f g :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_idempotent_semiring.coreflexive f"
    shows "(f \<odot> g) (i,j) = f (i,i) \<sqinter> g (i,j)"
proof -
  have 1: "\<forall>k . i \<noteq> k \<longrightarrow> f (i,k) = bot"
    using assms coreflexive_linorder_matrix by auto
  have "(\<Squnion>\<^sub>k f (i,k)) = f (i,i) \<squnion> (\<Squnion>\<^bsub>k\<in>UNIV-{i}\<^esub> f (i,k))"
    by (metis (no_types) UNIV_def brouwer.inf_bot_right finite_UNIV insert_def sup_monoid.sum.insert_remove)
  hence 2: "(\<Squnion>\<^sub>k f (i,k)) = f (i,i)"
    using 1 by (metis (no_types) linorder_finite_sup_selective sup_not_bot)
  have "(f \<odot> g) (i,j) = (f \<odot> mtop \<otimes> g) (i,j)"
    by (metis assms matrix_stone_relation_algebra.coreflexive_comp_top_inf)
  also have "... = (\<Squnion>\<^sub>k f (i,k)) \<sqinter> g (i,j)"
    by (metis inf_matrix_def comp_top_linorder_matrix)
  finally show ?thesis
    using 2 by simp
qed

lemma comp_coreflexive_linorder_matrix:
  fixes f g :: "('a::finite,'b::linorder_stone_relation_algebra_expansion) square"
  assumes "matrix_idempotent_semiring.coreflexive g"
    shows "(f \<odot> g) (i,j) = f (i,j) \<sqinter> g (j,j)"
proof -
  have "(f \<odot> g) (i,j) = ((f \<odot> g)\<^sup>t) (j,i)"
    by (simp add: conv_matrix_def)
  also have "... = (g \<odot> f\<^sup>t) (j,i)"
    by (simp add: assms matrix_stone_relation_algebra.conv_dist_comp matrix_stone_relation_algebra.coreflexive_symmetric)
  also have "... = g (j,j) \<sqinter> (f\<^sup>t) (j,i)"
    by (simp add: assms coreflexive_comp_linorder_matrix)
  also have "... = f (i,j) \<sqinter> g (j,j)"
    by (metis (no_types, lifting) conv_def old.prod.case conv_matrix_def inf_commute)
  finally show ?thesis
    .
qed

end

