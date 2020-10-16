(* Author: Alexander Bentkamp, Universität des Saarlandes
*)
section \<open>Matrix Rank\<close>

theory DL_Rank
imports VS_Connect DL_Missing_List
 Determinant
 Missing_VectorSpace
begin

lemma (in vectorspace) full_dim_span:
assumes "S \<subseteq> carrier V"
and "finite S"
and "vectorspace.dim K (span_vs S) = card S"
shows "lin_indpt S"
proof -
  have "vectorspace K (span_vs S)"
    using field.field_axioms vectorspace_def submodule_is_module[OF span_is_submodule[OF assms(1)]] by metis
  have "S \<subseteq> carrier (span_vs S)"  by (simp add: assms(1) in_own_span)
  have "LinearCombinations.module.span K (vs (span S)) S = carrier (vs (span S))"
    using module.span_li_not_depend[OF _ span_is_submodule[OF assms(1)]]
    by (simp add: assms(1) in_own_span)
  have "vectorspace.basis K (vs (span S)) S"
    using vectorspace.dim_gen_is_basis[OF \<open>vectorspace K (span_vs S)\<close> \<open>finite S\<close> \<open>S \<subseteq> carrier (span_vs S)\<close>
     \<open>LinearCombinations.module.span K (vs (span S)) S = carrier (vs (span S))\<close>]  \<open>vectorspace.dim K (span_vs S) = card S\<close>
    by simp
  then have "LinearCombinations.module.lin_indpt K (vs (span S)) S"
    using vectorspace.basis_def[OF \<open>vectorspace K (span_vs S)\<close>] by blast
  then show ?thesis using module.span_li_not_depend[OF _ span_is_submodule[OF assms(1)]]
    by (simp add: assms(1) in_own_span)
qed

lemma (in vectorspace) dim_span:
assumes "S \<subseteq> carrier V"
and "finite S"
and "maximal U (\<lambda>T. T \<subseteq> S \<and> lin_indpt T)"
shows "vectorspace.dim K (span_vs S) = card U"
proof -
  have "lin_indpt U" "U \<subseteq> S" by (metis assms(3) maximal_def)+
  then have "U \<subseteq> span S" using in_own_span[OF assms(1)] by blast
  then have lin_indpt: "LinearCombinations.module.lin_indpt K (span_vs S) U"
    using module.span_li_not_depend(2)[OF \<open>U \<subseteq> span S\<close>] \<open>lin_indpt U\<close> assms(1) span_is_submodule by blast
  have "span U = span S"
  proof (rule ccontr)
    assume "span U \<noteq> span S"
    have "span U \<subseteq> span S" using span_is_monotone \<open>U\<subseteq>S\<close> by metis
    then have "\<not> S \<subseteq> span U" by (meson \<open>U \<subseteq> S\<close> \<open>span U \<noteq> span S\<close> assms(1) span_is_submodule
      span_is_subset subset_antisym subset_trans)
    then obtain s where "s\<in>S" "s \<notin> span U" by blast
    then have "lin_indpt (U\<union>{s})" using lindep_span
      by (meson \<open>U \<subseteq> S\<close> \<open>lin_indpt U\<close> assms(1) lin_dep_iff_in_span rev_subsetD span_mem subset_trans)
    have "s\<notin>U" using \<open>U \<subseteq> S\<close> \<open>s \<notin> span U\<close> assms(1) span_mem by auto
    then have "(U\<union>{s}) \<subseteq> S \<and> lin_indpt (U\<union>{s})" using \<open>U \<subseteq> S\<close> \<open>lin_indpt (U \<union> {s})\<close> \<open>s \<in> S\<close> by auto
    then have "\<not>maximal U (\<lambda>T. T \<subseteq> S \<and> lin_indpt T)"
      unfolding maximal_def using Un_subset_iff \<open>s \<notin> U\<close> insert_subset  order_refl by auto
    then show False using assms by metis
  qed
  then have span:"LinearCombinations.module.span K (vs (span S)) U = span S"
    using module.span_li_not_depend[OF \<open>U \<subseteq> span S\<close>]
    by (simp add: LinearCombinations.module.span_is_submodule assms(1) module_axioms)
  have "vectorspace K (vs (span S))"
    using field.field_axioms vectorspace_def submodule_is_module[OF span_is_submodule[OF assms(1)]] by metis
  then have "vectorspace.basis K (vs (span S)) U" using vectorspace.basis_def[OF \<open>vectorspace K (vs (span S))\<close>]
    by (simp add: span \<open>U \<subseteq> span S\<close> lin_indpt)
  then show ?thesis
    using \<open>U \<subseteq> S\<close> \<open>vectorspace K (vs (span S))\<close> assms(2) infinite_super vectorspace.dim_basis by blast
qed

definition (in vec_space) rank ::"'a mat \<Rightarrow> nat"
where "rank A = vectorspace.dim class_ring (span_vs (set (cols A)))"

lemma (in vec_space) rank_card_indpt:
assumes "A \<in> carrier_mat n nc"
assumes "maximal S (\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)"
shows "rank A = card S"
proof -
  have "set (cols A) \<subseteq> carrier_vec n" using cols_dim assms(1) by blast
  have "finite (set (cols A))" by blast
  show ?thesis using dim_span[OF \<open>set (cols A) \<subseteq> carrier_vec n\<close> \<open>finite (set (cols A))\<close> assms(2)]
    unfolding rank_def by blast
qed

lemma maximal_exists_superset:
  assumes "finite S"
  assumes maxc: "\<And>A. P A \<Longrightarrow> A \<subseteq> S" and "P B"
  shows "\<exists>A. finite A \<and> maximal A P \<and> B \<subseteq> A"
proof -
  have "finite (S-B)" using assms(1) assms(3) infinite_super maxc by blast
  then show ?thesis using \<open>P B\<close>
  proof (induction "S-B" arbitrary:B rule: finite_psubset_induct)
    case (psubset B)
    then show ?case
    proof (cases "maximal B P")
      case True
      then show ?thesis using order_refl psubset.hyps by (metis assms(1) maxc psubset.prems rev_finite_subset)
    next
      case False
      then obtain B' where "B \<subset> B'" "P B'" using maximal_def psubset.prems by (metis dual_order.order_iff_strict)
      then have "B' \<subseteq> S" "B \<subseteq> S" using maxc \<open>P B\<close> by auto
      then have "S - B' \<subset> S - B" using \<open>B \<subset> B'\<close> by blast
      then show ?thesis using psubset(2)[OF \<open>S - B' \<subset> S - B\<close> \<open>P B'\<close>] using \<open>B \<subset> B'\<close> by fast
    qed
  qed
qed

lemma (in vec_space) rank_ge_card_indpt:
assumes "A \<in> carrier_mat n nc"
assumes "U \<subseteq> set (cols A)"
assumes "lin_indpt U"
shows "rank A \<ge> card U"
proof -
  obtain S where "maximal S (\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)" "U\<subseteq>S" "finite S"
    using maximal_exists_superset[of "set (cols A)" "(\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)" U]
    using List.finite_set assms(2) assms(3) maximal_exists_superset by blast
  then show ?thesis
    unfolding rank_card_indpt[OF \<open>A \<in> carrier_mat n nc\<close> \<open>maximal S (\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)\<close>]
    using card_mono by blast
qed

lemma (in vec_space) lin_indpt_full_rank:
assumes "A \<in> carrier_mat n nc"
assumes "distinct (cols A)"
assumes "lin_indpt (set (cols A))"
shows "rank A = nc"
proof -
  have "maximal (set (cols A)) (\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)"
    by (simp add: assms(3) maximal_def subset_antisym)
  then have "rank A = card (set (cols A))" using assms(1) vec_space.rank_card_indpt by blast
  then show ?thesis using assms(1) assms(2) distinct_card by fastforce
qed

lemma (in vec_space) rank_le_nc:
assumes "A \<in> carrier_mat n nc"
shows "rank A \<le> nc"
proof -
  obtain S where "maximal S (\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)"
    using maximal_exists[of "(\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)" "card (set (cols A))" "{}"]
    by (meson List.finite_set card_mono empty_iff empty_subsetI finite_lin_indpt2 rev_finite_subset)
  then have "card S \<le> card (set (cols A))" by (simp add: card_mono maximal_def)
  then have "card S \<le> nc"
    using assms(1) cols_length card_length carrier_matD(2) by (metis dual_order.trans)
  then show ?thesis
    using rank_card_indpt[OF \<open>A \<in> carrier_mat n nc\<close> \<open>maximal S (\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)\<close>]
    by simp
qed

lemma (in vec_space) full_rank_lin_indpt:
assumes "A \<in> carrier_mat n nc"
assumes "rank A = nc"
assumes "distinct (cols A)"
shows "lin_indpt (set (cols A))"
proof -
  have 1:"set (cols A) \<subseteq> carrier_vec n" using assms(1) cols_dim by blast
  have 2:"finite (set (cols A))" by simp
  have "card (set (cols A)) = nc"
    using assms(1) assms(3) distinct_card by fastforce
  have 3:"vectorspace.dim class_ring (span_vs (set (cols A))) = card (set (cols A))"
    using \<open>rank A = nc\<close>[unfolded rank_def]
    using assms(1) assms(3) distinct_card by fastforce
  show ?thesis using full_dim_span[OF 1 2 3] .
qed


lemma (in vec_space) mat_mult_eq_lincomb:
assumes "A \<in> carrier_mat n nc"
assumes "distinct (cols A)"
shows "A *\<^sub>v (vec nc (\<lambda>i. a (col A i))) = lincomb a (set (cols A))"
proof (rule eq_vecI)
  have "finite (set (cols A))" using assms(1) by simp
  then show "dim_vec (A *\<^sub>v (vec nc (\<lambda>i. a (col A i)))) = dim_vec (lincomb a (set (cols A)))"
    using assms cols_dim vec_space.lincomb_dim by (metis dim_mult_mat_vec carrier_matD(1))
  fix i assume "i < dim_vec (lincomb a (set (cols A)))"
  then have "i < n" using \<open>dim_vec (A *\<^sub>v (vec nc (\<lambda>i. a (col A i)))) = dim_vec (lincomb a (set (cols A)))\<close> assms by auto
  have "set (cols A) \<subseteq> carrier_vec n" using cols_dim \<open>A \<in> carrier_mat n nc\<close> carrier_matD(1) by blast
  have "bij_betw (nth (cols A)) {..<length (cols A)} (set (cols A))"
    unfolding bij_betw_def by (rule conjI, simp add: inj_on_nth \<open>distinct (cols A)\<close>;
    metis subset_antisym in_set_conv_nth lessThan_iff rev_image_eqI subsetI
    image_subsetI lessThan_iff nth_mem)
  then have " (\<Sum>x\<in>set (cols A). a x * x $ i) =
    (\<Sum>j\<in>{..<length (cols A)}. a (cols A ! j) * (cols A ! j) $ i)"
    using bij_betw_imp_surj_on bij_betw_imp_inj_on by (metis (no_types, lifting) sum.reindex_cong)
  also have "... = (\<Sum>j\<in>{..<length (cols A)}. a (col A j) * (cols A ! j) $ i)"
    using assms(1) assms(2) find_first_unique[OF \<open>distinct (cols A)\<close>] \<open>i < n\<close> by auto
  also have "... = (\<Sum>j\<in>{..<length (cols A)}. (cols A ! j) $ i * a (col A j))" by (metis mult_commute_abs)
  also have "... = (\<Sum>j\<in>{..<length (cols A)}. row A i $ j * a (col A j))" using \<open>i < n\<close> assms(1) assms(2) by auto
  finally show "(A *\<^sub>v (vec nc (\<lambda>i. a (col A i)))) $ i = lincomb a (set (cols A)) $ i"
    unfolding lincomb_index[OF \<open>i < n\<close> \<open>set (cols A) \<subseteq> carrier_vec n\<close>]
    unfolding mult_mat_vec_def scalar_prod_def
    using \<open>i < n\<close> assms(1) atLeast0LessThan lessThan_def carrier_matD(1) index_vec sum.cong by auto
qed

lemma (in vec_space) lincomb_eq_mat_mult:
assumes "A \<in> carrier_mat n nc"
assumes "v \<in> carrier_vec nc"
assumes "distinct (cols A)"
shows "lincomb (\<lambda>a. v $ find_first a (cols A)) (set (cols A)) = (A *\<^sub>v v)"
proof -
  have "\<And>i. i < nc \<Longrightarrow> find_first (col A i) (cols A) = i"
    using assms(1) assms(3) find_first_unique by fastforce
  then have "vec nc (\<lambda>i. v $ find_first (col A i) (cols A)) = v"
    using assms(2) by auto
  then show ?thesis
    using mat_mult_eq_lincomb[where a = "(\<lambda>a. v $ find_first a (cols A))", OF assms(1) assms(3)] by auto
qed

lemma (in vec_space) lin_depI:
assumes "A \<in> carrier_mat n nc"
assumes "v \<in> carrier_vec nc" "v \<noteq> 0\<^sub>v nc" "A *\<^sub>v v = 0\<^sub>v n"
assumes "distinct (cols A)"
shows "lin_dep (set (cols A))"
proof -
  have 1: "finite (set (cols A))" by simp
  have 2: "set (cols A) \<subseteq> set (cols A)" by auto
  have 3: "(\<lambda>a. v $ find_first a (cols A)) \<in> set (cols A) \<rightarrow> UNIV" by simp
  obtain i where "v $ i \<noteq> 0" "i < nc"
    using \<open>v \<noteq> 0\<^sub>v nc\<close>
    by (metis assms(2) dim_vec carrier_vecD vec_eq_iff zero_vec_def index_zero_vec(1))
  then have "i < dim_col A" using assms(1) by blast
  have 4:"col A i \<in> set (cols A)"
    using cols_nth[OF \<open>i < dim_col A\<close>] \<open>i < dim_col A\<close> in_set_conv_nth by fastforce
  have 5:"v $ find_first (col A i) (cols A) \<noteq> 0"
    using find_first_unique[OF \<open>distinct (cols A)\<close>] cols_nth[OF \<open>i < dim_col A\<close>] \<open>i < nc\<close> \<open>v $ i \<noteq> 0\<close>
    assms(1) by auto
  have 6:"lincomb (\<lambda>a. v $ find_first a (cols A)) (set (cols A)) = 0\<^sub>v n"
    using assms(1) assms(2) assms(4) assms(5) lincomb_eq_mat_mult by auto
  show ?thesis using lin_dep_crit[OF 1 2 _ 4 5 6] by metis
qed

lemma (in vec_space) lin_depE:
assumes "A \<in> carrier_mat n nc"
assumes "lin_dep (set (cols A))"
assumes "distinct (cols A)"
obtains v where "v \<in> carrier_vec nc" "v \<noteq> 0\<^sub>v nc" "A *\<^sub>v v = 0\<^sub>v n"
proof -
  have "finite (set (cols A))" by simp
  obtain a w where "a \<in> set (cols A) \<rightarrow> UNIV" "lincomb a (set (cols A)) = 0\<^sub>v n" "w \<in> set (cols A)" "a w \<noteq> 0"
    using finite_lin_dep[OF \<open>finite (set (cols A))\<close> \<open>lin_dep (set (cols A))\<close>]
    using assms(1) cols_dim carrier_matD(1) by blast
  define v where "v = vec nc (\<lambda>i. a (col A i))"
  have 1:"v \<in> carrier_vec nc" by (simp add: v_def)
  have 2:"v \<noteq> 0\<^sub>v nc"
  proof -
    obtain i where "w = col A i" "i < length (cols A)"
      by (metis \<open>w \<in> set (cols A)\<close> cols_length cols_nth in_set_conv_nth)
    have "v $ i \<noteq> 0"
      unfolding v_def
      using \<open>a w \<noteq> 0\<close>[unfolded \<open>w = col A i\<close>] index_vec[OF \<open>i < length (cols A)\<close>]
      assms(1) cols_length carrier_matD(2) by (metis (no_types) \<open>A \<in> carrier_mat n nc\<close>
      \<open>\<And>f. vec (length (cols A)) f $ i = f i\<close> \<open>a (col A i) \<noteq> 0\<close> cols_length carrier_matD(2))
    then show ?thesis using \<open>i < length (cols A)\<close> assms(1) by auto
  qed
  have 3:"A *\<^sub>v v = 0\<^sub>v n" unfolding v_def
    using \<open>lincomb a (set (cols A)) = 0\<^sub>v n\<close> mat_mult_eq_lincomb[OF \<open>A \<in> carrier_mat n nc\<close> \<open>distinct (cols A)\<close>] by auto
  show thesis using 1 2 3 by (simp add: that)
qed

lemma (in vec_space) non_distinct_low_rank:
assumes "A \<in> carrier_mat n n"
and "\<not> distinct (cols A)"
shows "rank A < n"
proof -
  obtain S where "maximal S (\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)"
    using maximal_exists[of "(\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)" "card (set (cols A))" "{}"]
    by (meson List.finite_set card_mono empty_iff empty_subsetI finite_lin_indpt2 rev_finite_subset)
  then have "card S \<le> card (set (cols A))" by (simp add: card_mono maximal_def)
  then have "card S < n"
    using assms(1) cols_length card_length \<open>\<not> distinct (cols A)\<close> card_distinct carrier_matD(2) nat_less_le
    by (metis dual_order.antisym dual_order.trans)
  then show ?thesis
    using rank_card_indpt[OF \<open>A \<in> carrier_mat n n\<close> \<open>maximal S (\<lambda>T. T \<subseteq> set (cols A) \<and> lin_indpt T)\<close>]
    by simp
qed

text \<open>The theorem "det non-zero $\longleftrightarrow$ full rank" is practically proven in det\_0\_iff\_vec\_prod\_zero\_field,
but without an actual definition of the rank.\<close>

lemma (in vec_space) det_zero_low_rank:
assumes "A \<in> carrier_mat n n"
and "det A = 0"
shows "rank A < n"
proof (rule ccontr)
  assume "\<not> rank A < n"
  then have "rank A = n" using rank_le_nc assms le_neq_implies_less by blast
  obtain v where "v \<in> carrier_vec n" "v \<noteq> 0\<^sub>v n" "A *\<^sub>v v = 0\<^sub>v n"
    using det_0_iff_vec_prod_zero_field[OF assms(1)] assms(2) by blast
  then show False
  proof (cases "distinct (cols A)")
    case True
    then have "lin_indpt (set (cols A))" using full_rank_lin_indpt using \<open>rank A = n\<close> assms(1) by auto
    then show False using lin_depI[OF assms(1) \<open>v \<in> carrier_vec n\<close> \<open>v \<noteq> 0\<^sub>v n\<close> \<open>A *\<^sub>v v = 0\<^sub>v n\<close>] True by blast
  next
    case False
    then show False using non_distinct_low_rank \<open>rank A = n\<close> \<open>\<not> rank A < n\<close> assms(1) by blast
  qed
qed

lemma det_identical_cols:
  assumes A: "A \<in> carrier_mat n n"
    and ij: "i \<noteq> j"
    and i: "i < n" and j: "j < n"
    and r: "col A i = col A j"
  shows "det A = 0"
  using det_identical_rows det_transpose
  by (metis A i ij j carrier_matD(2) transpose_carrier_mat r row_transpose)

lemma (in vec_space) low_rank_det_zero:
assumes "A \<in> carrier_mat n n"
and "det A \<noteq> 0"
shows "rank A = n"
proof -
  have "distinct (cols A)"
  proof (rule ccontr)
    assume "\<not> distinct (cols A)"
    then obtain i j where "i\<noteq>j" "(cols A) ! i = (cols A) ! j" "i<length (cols A)" "j<length (cols A)"
      using distinct_conv_nth by blast
    then have "col A i = col A j" "i<n" "j<n" using assms(1) by auto
    then have "det A = 0"  using det_identical_cols using \<open>i \<noteq> j\<close> assms(1) by blast
    then show False using \<open>det A \<noteq> 0\<close> by auto
  qed
  have "\<And>v. v \<in> carrier_vec n \<Longrightarrow> v \<noteq> 0\<^sub>v n \<Longrightarrow> A *\<^sub>v v \<noteq> 0\<^sub>v n"
    using det_0_iff_vec_prod_zero_field[OF assms(1)] assms(2) by auto
  then have "lin_indpt (set (cols A))" using lin_depE[OF assms(1) _ \<open>distinct (cols A)\<close>] by auto
  then show ?thesis using lin_indpt_full_rank[OF assms(1) \<open>distinct (cols A)\<close>] by metis
qed

lemma (in vec_space) det_rank_iff:
assumes "A \<in> carrier_mat n n"
shows "det A \<noteq> 0 \<longleftrightarrow> rank A = n"
  using assms det_zero_low_rank low_rank_det_zero by force

section "Subadditivity of rank"

text \<open>Subadditivity is the property of rank, that rank (A + B) <= rank A + rank B.\<close>

lemma (in Module.module) lincomb_add:
assumes "finite (b1 \<union> b2)"
assumes "b1 \<union> b2 \<subseteq> carrier M"
assumes "x1 = lincomb a1 b1" "a1\<in> (b1\<rightarrow>carrier R)"
assumes "x2 = lincomb a2 b2" "a2\<in> (b2\<rightarrow>carrier R)"
assumes "x = x1 \<oplus>\<^bsub>M\<^esub> x2"
shows "lincomb (\<lambda>v. (\<lambda>v. if v \<in> b1 then a1 v else \<zero>) v \<oplus> (\<lambda>v. if v \<in> b2 then a2 v else \<zero>) v) (b1 \<union> b2) = x"
proof -
  have "finite (b1 \<union> (b2-b1))" "finite (b2 \<union> (b1-b2))"
       "b1 \<union> (b2 - b1) \<subseteq> carrier M" "b2 \<union> (b1-b2) \<subseteq> carrier M"
       "b1 \<inter> (b2 - b1) = {}" "b2 \<inter> (b1 - b2) = {}"
       "(\<lambda>b. \<zero>\<^bsub>R\<^esub>) \<in> b2 - b1 \<rightarrow> carrier R" "(\<lambda>b. \<zero>\<^bsub>R\<^esub>) \<in> b1 - b2 \<rightarrow> carrier R"
    using \<open>finite (b1 \<union> b2)\<close> \<open>b1 \<union> b2 \<subseteq> carrier M\<close> \<open>a2\<in> (b2\<rightarrow>carrier R)\<close> by auto
  have "lincomb (\<lambda>b. \<zero>\<^bsub>R\<^esub>) (b2 - b1) = \<zero>\<^bsub>M\<^esub>" "lincomb (\<lambda>b. \<zero>\<^bsub>R\<^esub>) (b1 - b2) = \<zero>\<^bsub>M\<^esub>"
    unfolding lincomb_def using M.finsum_all0 assms(2) lmult_0 subset_iff
    by (metis (no_types, lifting) Un_Diff_cancel2 inf_sup_aci(5) le_sup_iff)+
  then have "x1 = lincomb (\<lambda>v. if v \<in> b1 then a1 v else \<zero>) (b1 \<union> b2)"
            "x2 = lincomb (\<lambda>v. if v \<in> b2 then a2 v else \<zero>) (b1 \<union> b2)"
    using lincomb_union2[OF \<open>finite (b1 \<union> (b2-b1))\<close> \<open>b1 \<union> (b2 - b1) \<subseteq> carrier M\<close> \<open>b1 \<inter> (b2 - b1) = {}\<close> \<open>a1\<in> (b1\<rightarrow>carrier R)\<close> \<open>(\<lambda>b. \<zero>\<^bsub>R\<^esub>) \<in> b2 - b1 \<rightarrow> carrier R\<close>]
          lincomb_union2[OF \<open>finite (b2 \<union> (b1-b2))\<close> \<open>b2 \<union> (b1-b2) \<subseteq> carrier M\<close> \<open>b2 \<inter> (b1 - b2) = {}\<close> \<open>a2\<in> (b2\<rightarrow>carrier R)\<close> \<open>(\<lambda>b. \<zero>\<^bsub>R\<^esub>) \<in> b1 - b2 \<rightarrow> carrier R\<close>]
    using assms(2) assms(3) assms(4)  assms(5)  assms(6) by (simp_all add:Un_commute)
  have "(\<lambda>v. if v \<in> b1 then a1 v else \<zero>) \<in> (b1 \<union> b2) \<rightarrow> carrier R"
       "(\<lambda>v. if v \<in> b2 then a2 v else \<zero>) \<in> (b1 \<union> b2) \<rightarrow> carrier R" using assms(4) assms(6) by auto
  show "lincomb (\<lambda>v. (\<lambda>v. if v \<in> b1 then a1 v else \<zero>) v \<oplus> (\<lambda>v. if v \<in> b2 then a2 v else \<zero>) v) (b1 \<union> b2) = x"
    using lincomb_sum[OF \<open>finite (b1 \<union> b2)\<close> \<open>b1 \<union> b2 \<subseteq> carrier M\<close>
    \<open>(\<lambda>v. if v \<in> b1 then a1 v else \<zero>) \<in> (b1 \<union> b2) \<rightarrow> carrier R\<close> \<open>(\<lambda>v. if v \<in> b2 then a2 v else \<zero>) \<in> (b1 \<union> b2) \<rightarrow> carrier R\<close>]
    \<open>x1 = lincomb (\<lambda>v. if v \<in> b1 then a1 v else \<zero>) (b1 \<union> b2)\<close> \<open>x2 = lincomb (\<lambda>v. if v \<in> b2 then a2 v else \<zero>) (b1 \<union> b2)\<close> assms(7) by blast
qed

lemma (in vectorspace) dim_subadditive:
assumes "subspace K W1 V"
and "vectorspace.fin_dim K (vs W1)"
assumes "subspace K W2 V"
and "vectorspace.fin_dim K (vs W2)"
shows "vectorspace.dim K (vs (subspace_sum W1 W2)) \<le> vectorspace.dim K (vs W1) + vectorspace.dim K (vs W2)"
proof -
  have "vectorspace K (vs W1)" "vectorspace K (vs W2)" "submodule K W1 V" "submodule K W2 V"
    by (simp add: \<open>subspace K W1 V\<close> \<open>subspace K W2 V\<close> subspace_is_vs)+
  obtain b1 b2 where "vectorspace.basis K (vs W1) b1" "vectorspace.basis K (vs W2) b2" "finite b1" "finite b2"
    using vectorspace.finite_basis_exists[OF \<open>vectorspace K (vs W1)\<close> \<open>vectorspace.fin_dim K (vs W1)\<close>]
    using vectorspace.finite_basis_exists[OF \<open>vectorspace K (vs W2)\<close> \<open>vectorspace.fin_dim K (vs W2)\<close>]
    by blast
  then have "LinearCombinations.module.gen_set K (vs W1) b1" "LinearCombinations.module.gen_set K (vs W2) b2"
    using \<open>vectorspace K (vs W1)\<close> \<open>vectorspace K (vs W2)\<close> vectorspace.basis_def by blast+
  then have "span b1 = W1" "span b2 = W2"
    using module.span_li_not_depend(1) \<open>submodule K W1 V\<close>  \<open>submodule K W2 V\<close>
    \<open>vectorspace K (vs W1)\<close> \<open>vectorspace.basis K (vs W1) b1\<close> \<open>vectorspace K (vs W2)\<close>
    \<open>vectorspace.basis K (vs W2) b2\<close> vectorspace.basis_def by force+
  have "W1 \<subseteq> carrier V" "W2 \<subseteq> carrier V" using \<open>subspace K W1 V\<close> \<open>subspace K W2 V\<close> subspace_def submodule_def by metis+
  have "b1 \<subseteq> carrier V"
    using \<open>vectorspace.basis K (vs W1) b1\<close> \<open>vectorspace K (vs W1)\<close> vectorspace.basis_def
    \<open>W1 \<subseteq> carrier V\<close> by fastforce
  have "b2 \<subseteq> carrier V"
    using \<open>vectorspace.basis K (vs W2) b2\<close> \<open>vectorspace K (vs W2)\<close> vectorspace.basis_def
    \<open>W2 \<subseteq> carrier V\<close> by fastforce
  have "finite (b1 \<union> b2)" "b1 \<union> b2 \<subseteq> carrier V"
    by (simp_all add: \<open>finite b1\<close> \<open>finite b2\<close> \<open>b2 \<subseteq> carrier V\<close> \<open>b1 \<subseteq> carrier V\<close>)
  have "subspace_sum W1 W2 \<subseteq> span (b1\<union>b2)"
  proof (rule subsetI)
    fix x assume "x \<in> subspace_sum W1 W2"
    obtain x1 x2 where  "x1 \<in> W1" "x2 \<in> W2" "x = x1 \<oplus>\<^bsub>V\<^esub> x2"
      using imageE[OF \<open>x \<in> subspace_sum W1 W2\<close>[unfolded submodule_sum_def]]
      by (metis (no_types, lifting) BNF_Def.Collect_case_prodD split_def)
    obtain a1 where "x1 = lincomb a1 b1" "a1\<in> (b1\<rightarrow>carrier K)"
      using \<open>span b1 = W1\<close> finite_span[OF \<open>finite b1\<close> \<open>b1 \<subseteq> carrier V\<close>] \<open>x1 \<in> W1\<close> by auto
    obtain a2 where "x2 = lincomb a2 b2" "a2\<in> (b2\<rightarrow>carrier K)"
      using \<open>span b2 = W2\<close> finite_span[OF \<open>finite b2\<close> \<open>b2 \<subseteq> carrier V\<close>] \<open>x2 \<in> W2\<close> by auto
    obtain a where "x = lincomb a (b1 \<union> b2)" using lincomb_add[OF \<open>finite (b1 \<union> b2)\<close> \<open>b1 \<union> b2 \<subseteq> carrier V\<close>
      \<open>x1 = lincomb a1 b1\<close> \<open>a1\<in> (b1\<rightarrow>carrier K)\<close>  \<open>x2 = lincomb a2 b2\<close> \<open>a2\<in> (b2\<rightarrow>carrier K)\<close> \<open>x = x1 \<oplus>\<^bsub>V\<^esub> x2\<close>] by blast
    then show "x \<in> span (b1 \<union> b2)" using finite_span[OF \<open>finite (b1 \<union> b2)\<close> \<open>(b1 \<union> b2) \<subseteq> carrier V\<close>]
      using \<open>b1 \<subseteq> carrier V\<close> \<open>b2 \<subseteq> carrier V\<close> \<open>span b1 = W1\<close> \<open>span b2 = W2\<close> \<open>x \<in> subspace_sum W1 W2\<close> span_union_is_sum by auto
  qed
  have "b1 \<subseteq> W1" "b2 \<subseteq> W2"
    using \<open>vectorspace K (vs W1)\<close> \<open>vectorspace K (vs W2)\<close> \<open>vectorspace.basis K (vs W1) b1\<close>
    \<open>vectorspace.basis K (vs W2) b2\<close> vectorspace.basis_def local.carrier_vs_is_self by blast+
  then have "b1\<union>b2 \<subseteq> subspace_sum W1 W2" using \<open>submodule K W1 V\<close> \<open>submodule K W2 V\<close> in_sum
    by (metis assms(1) assms(3) dual_order.trans sup_least vectorspace.vsum_comm vectorspace_axioms)
  have "subspace_sum W1 W2 = LinearCombinations.module.span K (vs (subspace_sum W1 W2)) (b1\<union>b2)"
  proof (rule subset_antisym)
    have "submodule K (subspace_sum W1 W2) V" by (simp add: \<open>submodule K W1 V\<close> \<open>submodule K W2 V\<close> sum_is_submodule)
    show "subspace_sum W1 W2 \<subseteq> LinearCombinations.module.span K (vs (subspace_sum W1 W2)) (b1\<union>b2)"
      using module.span_li_not_depend(1)[OF \<open>b1\<union>b2 \<subseteq> subspace_sum W1 W2\<close> \<open>submodule K (subspace_sum W1 W2) V\<close>]
      by (simp add: \<open>subspace_sum W1 W2 \<subseteq> span (b1 \<union> b2)\<close>)
    show "subspace_sum W1 W2 \<supseteq> LinearCombinations.module.span K (vs (subspace_sum W1 W2)) (b1\<union>b2)"
      using \<open>b1\<union>b2 \<subseteq> subspace_sum W1 W2\<close> by (metis (full_types) LinearCombinations.module.span_is_subset2
      LinearCombinations.module.submodule_is_module \<open>submodule K (subspace_sum W1 W2) V\<close> local.carrier_vs_is_self submodule_def)
  qed
  have "vectorspace K (vs (subspace_sum W1 W2))" using assms(1) assms(3) subspace_def sum_is_subspace vectorspace.subspace_is_vs by blast
  then have "vectorspace.dim K (vs (subspace_sum W1 W2)) \<le> card (b1 \<union> b2)"
    using vectorspace.gen_ge_dim[OF \<open>vectorspace K (vs (subspace_sum W1 W2))\<close> \<open>finite (b1 \<union> b2)\<close>]
    \<open>b1 \<union> b2 \<subseteq> subspace_sum W1 W2\<close>
    \<open>subspace_sum W1 W2 = LinearCombinations.module.span K (vs (subspace_sum W1 W2)) (b1 \<union> b2)\<close>
    local.carrier_vs_is_self by blast
  also have "... \<le> card b1 + card b2" by (simp add: card_Un_le)
  also have "... = vectorspace.dim K (vs W1) + vectorspace.dim K (vs W2)"
    by (metis \<open>finite b1\<close> \<open>finite b2\<close> \<open>vectorspace K (vs W1)\<close> \<open>vectorspace K (vs W2)\<close>
    \<open>vectorspace.basis K (vs W1) b1\<close> \<open>vectorspace.basis K (vs W2) b2\<close> vectorspace.dim_basis)
  finally show ?thesis by auto
qed

lemma (in Module.module) nested_submodules:
assumes "submodule R W M"
assumes "submodule R X M"
assumes "X \<subseteq> W"
shows "submodule R X (md W)"
  unfolding submodule_def
  using \<open>X \<subseteq> W\<close> submodule_is_module[OF \<open>submodule R W M\<close>] using \<open>submodule R X M\<close>[unfolded submodule_def] by auto

lemma (in vectorspace) nested_subspaces:
assumes "subspace K W V"
assumes "subspace K X V"
assumes "X \<subseteq> W"
shows "subspace K X (vs W)"
  using assms nested_submodules subspace_def subspace_is_vs by blast

lemma (in vectorspace) subspace_dim:
assumes "subspace K X V" "fin_dim" "vectorspace.fin_dim K (vs X)"
shows "vectorspace.dim K (vs X) \<le> dim"
proof -
  have "vectorspace K (vs X)" using assms(1) subspace_is_vs by auto
  then obtain b where "vectorspace.basis K (vs X) b" using vectorspace.finite_basis_exists
    using assms(3) by blast
  then have "b \<subseteq> carrier V" "LinearCombinations.module.lin_indpt K (vs X) b"
    using vectorspace.basis_def[OF \<open>vectorspace K (vs X)\<close>] \<open>subspace K X V\<close>[unfolded subspace_def submodule_def] by auto
  then have "lin_indpt b"
    by (metis LinearCombinations.module.span_li_not_depend(2) \<open>vectorspace K (vs X)\<close> \<open>vectorspace.basis K (vs X) b\<close>
    assms(1) is_module local.carrier_vs_is_self submodule_def vectorspace.basis_def)
  show ?thesis using li_le_dim(2)[OF \<open>fin_dim\<close> \<open>b \<subseteq> carrier V\<close> \<open>lin_indpt b\<close>]
    using \<open>b \<subseteq> carrier V\<close> \<open>lin_indpt b\<close> \<open>vectorspace K (vs X)\<close> \<open>vectorspace.basis K (vs X) b\<close> assms(2)
    fin_dim_li_fin vectorspace.dim_basis by fastforce
qed

lemma (in vectorspace) fin_dim_subspace_sum:
assumes "subspace K W1 V"
assumes "subspace K W2 V"
assumes "vectorspace.fin_dim K (vs W1)" "vectorspace.fin_dim K (vs W2)"
shows "vectorspace.fin_dim K (vs (subspace_sum W1 W2))"
proof -
  obtain b1 where "finite b1" "b1 \<subseteq> W1" "LinearCombinations.module.gen_set K (vs W1) b1"
    using assms vectorspace.fin_dim_def subspace_is_vs by force
  obtain b2 where "finite b2" "b2 \<subseteq> W2" "LinearCombinations.module.gen_set K (vs W2) b2"
    using assms vectorspace.fin_dim_def subspace_is_vs by force
  have 1:"finite (b1 \<union> b2)" by (simp add: \<open>finite b1\<close> \<open>finite b2\<close>)
  have 2:"b1 \<union> b2 \<subseteq> subspace_sum W1 W2"
    by (metis (no_types, lifting) \<open>b1 \<subseteq> W1\<close> \<open>b2 \<subseteq> W2\<close> assms(1) assms(2)
    le_sup_iff subset_Un_eq vectorspace.in_sum_vs vectorspace.vsum_comm vectorspace_axioms)
  have 3:"LinearCombinations.module.gen_set K (vs (subspace_sum W1 W2)) (b1 \<union> b2)"
  proof (rule subset_antisym)
    have 0:"LinearCombinations.module.span K (vs (subspace_sum W1 W2)) (b1 \<union> b2) = span (b1 \<union> b2)"
      using span_li_not_depend(1)[OF \<open>b1 \<union> b2 \<subseteq> subspace_sum W1 W2\<close>] sum_is_subspace[OF assms(1) assms(2)] by auto
    then show "LinearCombinations.module.span K (vs (subspace_sum W1 W2)) (b1 \<union> b2) \<subseteq> carrier (vs (subspace_sum W1 W2))"
      using \<open>b1 \<union> b2 \<subseteq> subspace_sum W1 W2\<close> span_is_subset sum_is_subspace[OF assms(1) assms(2)] by auto
    show "carrier (vs (subspace_sum W1 W2)) \<subseteq> LinearCombinations.module.span K (vs (subspace_sum W1 W2)) (b1 \<union> b2)"
     unfolding 0
    proof
      fix x assume assumption:"x \<in> carrier (vs (subspace_sum W1 W2))"
      then have "x\<in>subspace_sum W1 W2" by auto
      then obtain x1 x2 where "x = x1 \<oplus>\<^bsub>V\<^esub> x2" "x1\<in>W1" "x2\<in>W2"
        using imageE[OF \<open>x \<in> subspace_sum W1 W2\<close>[unfolded submodule_sum_def]]
        by (metis (no_types, lifting) BNF_Def.Collect_case_prodD split_def)
      have "x1\<in>span b1"  "x2\<in>span b2"
        using \<open>LinearCombinations.module.span K (vs W1) b1 = carrier (vs W1)\<close> \<open>b1 \<subseteq> W1\<close> \<open>x1 \<in> W1\<close>
              \<open>LinearCombinations.module.span K (vs W2) b2 = carrier (vs W2)\<close> \<open>b2 \<subseteq> W2\<close> \<open>x2 \<in> W2\<close>
        assms(1) assms(2) span_li_not_depend(1) by auto
      then have "x1\<in>span (b1 \<union> b2)" "x2\<in>span (b1 \<union> b2)" by (meson le_sup_iff subsetD span_is_monotone subsetI)+
      then show "x \<in> span (b1 \<union> b2)" unfolding \<open>x = x1 \<oplus>\<^bsub>V\<^esub> x2\<close>
        by (meson \<open>b1 \<union> b2 \<subseteq> subspace_sum W1 W2\<close> assms(1) assms(2) is_module submodule.subset
        subset_trans sum_is_submodule vectorspace.span_add1 vectorspace_axioms)
    qed
  qed
  show ?thesis using 1 2 3 vectorspace.fin_dim_def
    by (metis assms(1) assms(2) local.carrier_vs_is_self subspace_def sum_is_subspace vectorspace.subspace_is_vs)
qed

lemma (in vec_space) rank_subadditive:
assumes "A \<in> carrier_mat n nc"
assumes "B \<in> carrier_mat n nc"
shows "rank (A + B) \<le> rank A + rank B"
proof -
  define W1 where "W1 = span (set (cols A))"
  define W2 where "W2 = span (set (cols B))"
  have "set (cols (A + B)) \<subseteq> subspace_sum W1 W2"
  proof
    fix x assume "x \<in> set (cols (A + B))"
    obtain i where "x = col (A + B) i" "i < length (cols (A + B))"
      using \<open>x \<in> set (cols (A + B))\<close> nth_find_first cols_nth find_first_le by (metis cols_length)
    then have "x = col A i + col B i" using \<open>i < length (cols (A + B))\<close> assms(1) assms(2) by auto
    have "col A i \<in> span (set (cols A))" "col B i \<in> span (set (cols B))"
      using \<open>i < length (cols (A + B))\<close> assms(1) assms(2) in_set_conv_nth
      by (metis cols_dim cols_length cols_nth carrier_matD(1) carrier_matD(2) index_add_mat(3) span_mem)+
    then show "x \<in> subspace_sum W1 W2"
      unfolding W1_def W2_def \<open>x = col A i + col B i\<close> submodule_sum_def by blast
  qed
  have "subspace class_ring (subspace_sum W1 W2) V"
    by (metis W1_def W2_def assms(1) assms(2) cols_dim carrier_matD(1) span_is_submodule subspace_def sum_is_submodule vec_vs)
  then have "span (set (cols (A + B))) \<subseteq> subspace_sum W1 W2"
    by (simp add: \<open>set (cols (A + B)) \<subseteq> subspace_sum W1 W2\<close> span_is_subset)
  have "subspace class_ring (span (set (cols (A + B)))) V" by (metis assms(2) cols_dim add_carrier_mat carrier_matD(1) span_is_subspace)
  have subspace:"subspace class_ring (span (set (cols (A + B)))) (vs (subspace_sum W1 W2))"
    using nested_subspaces[OF \<open>subspace class_ring (subspace_sum W1 W2) V\<close> \<open>subspace class_ring (span (set (cols (A + B)))) V\<close>
    \<open>span (set (cols (A + B))) \<subseteq> subspace_sum W1 W2\<close>] .
  have "vectorspace.fin_dim class_ring (vs W1)" "vectorspace.fin_dim class_ring (vs W2)"
       "subspace class_ring W1 V" "subspace class_ring W2 V"
    using span_is_subspace W1_def W2_def assms(1) assms(2) cols_dim carrier_matD fin_dim_span_cols by auto
  then have fin_dim: "vectorspace.fin_dim class_ring (vs (subspace_sum W1 W2))" using fin_dim_subspace_sum by auto
  have "vectorspace.fin_dim class_ring (span_vs (set (cols (A + B))))" using assms(2) add_carrier_mat vec_space.fin_dim_span_cols by blast
  then have "rank (A + B) \<le> vectorspace.dim class_ring (vs (subspace_sum W1 W2))" unfolding rank_def
    using vectorspace.subspace_dim[OF subspace_is_vs[OF \<open>subspace class_ring (subspace_sum W1 W2) V\<close>] subspace fin_dim] by auto
  also have "vectorspace.dim class_ring (vs (subspace_sum W1 W2)) \<le> rank A + rank B" unfolding rank_def
    using W1_def W2_def \<open>subspace class_ring W1 V\<close> \<open>subspace class_ring W2 V\<close> \<open>vectorspace.fin_dim class_ring (vs W1)\<close>
    \<open>vectorspace.fin_dim class_ring (vs W2)\<close> subspace_def vectorspace.dim_subadditive by blast
  finally show ?thesis by auto
qed

lemma (in vec_space) span_zero: "span {zero V} = {zero V}"
  by (metis (no_types, lifting) empty_subsetI in_own_span span_is_submodule span_is_subset
  span_is_subset2 subset_antisym vectorspace.span_empty vectorspace_axioms)

lemma (in vec_space) dim_zero_vs: "vectorspace.dim class_ring (span_vs {}) = 0"
proof -
  have "vectorspace class_ring (span_vs {})" using field.field_axioms span_is_submodule submodule_is_module vectorspace_def by auto
  have "{} \<subseteq> carrier_vec n \<and> lin_indpt {}"
    by (metis (no_types) empty_subsetI fin_dim finite_basis_exists subset_li_is_li vec_vs vectorspace.basis_def)
  then have "vectorspace.basis class_ring (span_vs {}) {}" using vectorspace.basis_def
    by (simp add: \<open>vectorspace class_ring (vs (span {}))\<close> span_is_submodule span_li_not_depend(1) span_li_not_depend(2) vectorspace.basis_def)
  then show ?thesis using \<open>vectorspace class_ring (vs (span {}))\<close> vectorspace.dim_basis by fastforce
qed

lemma (in vec_space) rank_0I: "rank (0\<^sub>m n nc) = 0"
proof -
  have "set (cols (0\<^sub>m n nc)) \<subseteq> {0\<^sub>v n}"
    by (metis col_zero cols_length cols_nth in_set_conv_nth insertCI index_zero_mat(3) subsetI)
  have "set (cols (0\<^sub>m n nc::'a mat)) = {} \<or> set (cols (0\<^sub>m n nc)) = {0\<^sub>v n::'a vec}"
    by (meson \<open>set (cols (0\<^sub>m n nc)) \<subseteq> {0\<^sub>v n}\<close> subset_singletonD)
  then have "span (set (cols (0\<^sub>m n nc))) = {0\<^sub>v n}"
    by (metis (no_types) span_empty span_zero vectorspace.span_empty vectorspace_axioms)
  then show ?thesis unfolding rank_def \<open>span (set (cols (0\<^sub>m n nc))) = {0\<^sub>v n}\<close>
    using span_empty dim_zero_vs by simp
qed


lemma (in vec_space) rank_le_1_product_entries:
fixes f g::"nat \<Rightarrow> 'a"
assumes "A \<in> carrier_mat n nc"
assumes "\<And>r c. r<dim_row A \<Longrightarrow> c<dim_col A \<Longrightarrow> A $$ (r,c) = f r * g c"
shows "rank A \<le> 1"
proof -
  have "set (cols A) \<subseteq> span {vec n f}"
  proof
    fix v assume "v \<in> set (cols A)"
    then obtain c where "c < dim_col A" "v = col A c" by (metis cols_length cols_nth in_set_conv_nth)
    have "g c \<cdot>\<^sub>v vec n f = v"
    proof (rule eq_vecI)
      show "dim_vec (g c \<cdot>\<^sub>v Matrix.vec n f) = dim_vec v" using \<open>v = col A c\<close> assms(1) by auto
      fix r assume "r < dim_vec v"
      then have "r < dim_vec (Matrix.vec n f)" using \<open>dim_vec (g c \<cdot>\<^sub>v Matrix.vec n f) = dim_vec v\<close> by auto
      then have "r < n" "r < dim_row A"using index_smult_vec(2) \<open>A \<in> carrier_mat n nc\<close> by auto
      show "(g c \<cdot>\<^sub>v Matrix.vec n f) $ r = v $ r"
        unfolding \<open>v = col A c\<close> col_def index_smult_vec(1)[OF \<open>r < dim_vec (Matrix.vec n f)\<close>]
        index_vec[OF \<open>r < n\<close>] index_vec[OF \<open>r < dim_row A\<close>] by (simp add: \<open>c < dim_col A\<close> \<open>r < dim_row A\<close> assms(2))
    qed
    then show "v \<in> span {vec n f}" using submodule.smult_closed[OF span_is_submodule]
      using UNIV_I empty_subsetI insert_subset span_self dim_vec module_vec_simps(4) by auto
  qed
  have "vectorspace class_ring (vs (span {Matrix.vec n f}))" using span_is_subspace[THEN subspace_is_vs, of "{vec n f}"] by auto
  have "submodule class_ring (span {Matrix.vec n f}) V" by (simp add: span_is_submodule)
  have "subspace class_ring(span (set (cols A))) (vs (span {Matrix.vec n f}))"
    using vectorspace.span_is_subspace[OF \<open>vectorspace class_ring (vs (span {Matrix.vec n f}))\<close>, of "set (cols A)", unfolded
    span_li_not_depend(1)[OF \<open>set (cols A) \<subseteq> span {vec n f}\<close> \<open>submodule class_ring (span {Matrix.vec n f}) V\<close>]]
    \<open>set (cols A) \<subseteq> span {vec n f}\<close> by auto
  have fin_dim:"vectorspace.fin_dim class_ring (vs (span {Matrix.vec n f}))"
       "vectorspace.fin_dim class_ring (vs (span {Matrix.vec n f})\<lparr>carrier := span (set (cols A))\<rparr>)"
    using fin_dim_span fin_dim_span_cols \<open>A \<in> carrier_mat n nc\<close> by auto
  have "vectorspace.dim class_ring (vs (span {Matrix.vec n f})) \<le> 1"
    using vectorspace.dim_le1I[OF \<open>vectorspace class_ring (vs (span {Matrix.vec n f}))\<close>]
    span_mem span_li_not_depend(1)[OF _ \<open>submodule class_ring (span {Matrix.vec n f}) V\<close>] by simp
  then show ?thesis unfolding rank_def using  "vectorspace.subspace_dim"[OF
    \<open>vectorspace class_ring (vs (span {Matrix.vec n f}))\<close> \<open>subspace class_ring (span (set (cols A))) (vs (span {Matrix.vec n f}))\<close>
    fin_dim(1) fin_dim(2)] by simp
qed

end
