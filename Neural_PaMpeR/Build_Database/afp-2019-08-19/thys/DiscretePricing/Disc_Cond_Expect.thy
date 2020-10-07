(*  Title:      Disc_Cond_Expect.thy
    Author:     Mnacho Echenim, Univ. Grenoble Alpes
*)

section \<open>Discrete Conditional Expectation\<close>

theory Disc_Cond_Expect imports "HOL-Probability.Probability" Generated_Subalgebra

begin

subsection \<open>Preliminary measurability results\<close>

text \<open>These are some useful results, in particular when working with functions that have a countable
codomain.\<close>

definition disc_fct  where
  "disc_fct f \<equiv> countable (range f)"

definition  point_measurable where
  "point_measurable M S f \<equiv> (f`(space M)\<subseteq> S) \<and> (\<forall>  r \<in> (range f) \<inter> S . f-`{r} \<inter> (space M) \<in> sets M)"


lemma singl_meas_if:
  assumes "f \<in> space M \<rightarrow> space N"
  and "\<forall>r\<in> range f\<inter> space N. \<exists>A\<in> sets N. range f\<inter> A = {r}"
shows "point_measurable (fct_gen_subalgebra M N f) (space N) f" unfolding point_measurable_def
proof
  show "f`space (fct_gen_subalgebra M N f)\<subseteq> space N" using assms
    by (simp add: Pi_iff fct_gen_subalgebra_space image_subsetI)
  show "(\<forall>r\<in>range f \<inter> space N. f -` {r} \<inter> space (fct_gen_subalgebra M N f) \<in> sets (fct_gen_subalgebra M N f))"
  proof
    fix r
    assume "r\<in> range f \<inter> space N"
    hence "\<exists>A\<in> sets N. range f\<inter> A = {r}" using assms by blast
    from this obtain A where "A\<in> sets N" and "range f \<inter> A = {r}" by auto note Aprops = this
    hence "f-`A = f-`{r}" by auto
    hence "f-`A \<inter> space M = f-`{r} \<inter> space (fct_gen_subalgebra M N f)" by (simp add: fct_gen_subalgebra_space)
    thus "f -` {r} \<inter> space (fct_gen_subalgebra M N f) \<in> sets (fct_gen_subalgebra M N f)"
      using Aprops fct_gen_subalgebra_sets_mem[of A N f M] by simp
  qed
qed

lemma  meas_single_meas:
  assumes "f\<in> measurable M N"
  and "\<forall>r\<in> range f\<inter> space N. \<exists>A\<in> sets N. range f\<inter> A = {r}"
shows "point_measurable M (space N) f"
proof -
  have "subalgebra M (fct_gen_subalgebra M N f) " using assms fct_gen_subalgebra_is_subalgebra by blast
  hence "sets (fct_gen_subalgebra M N f) \<subseteq> sets M" by (simp add: subalgebra_def)
  moreover have "point_measurable (fct_gen_subalgebra M N f) (space N) f" using assms singl_meas_if
    by (metis (no_types, lifting) Pi_iff measurable_space)
  ultimately show ?thesis
  proof -
    obtain bb :: "'a measure \<Rightarrow> 'b set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b" where
      f1: "\<forall>m B f. (\<not> point_measurable m B f \<or> f ` space m \<subseteq> B \<and> (\<forall>b. b \<notin> range f \<inter> B \<or> f -` {b} \<inter> space m \<in> sets m)) \<and> (\<not> f ` space m \<subseteq> B \<or> bb m B f \<in> range f \<inter> B \<and> f -` {bb m B f} \<inter> space m \<notin> sets m \<or> point_measurable m B f)"
      by (metis (no_types) point_measurable_def)
    moreover
    { assume "f -` {bb M (space N) f} \<inter> space (fct_gen_subalgebra M N f) \<in> sets (fct_gen_subalgebra M N f)"
      then have "f -` {bb M (space N) f} \<inter> space M \<in> sets (fct_gen_subalgebra M N f)"
        by (metis \<open>subalgebra M (fct_gen_subalgebra M N f)\<close> subalgebra_def)
      then have "f -` {bb M (space N) f} \<inter> space M \<in> sets M"
        using \<open>sets (fct_gen_subalgebra M N f) \<subseteq> sets M\<close> by blast
      then have "f ` space M \<subseteq> space N \<and> f -` {bb M (space N) f} \<inter> space M \<in> sets M"
        using f1 by (metis \<open>point_measurable (fct_gen_subalgebra M N f) (space N) f\<close> \<open>subalgebra M (fct_gen_subalgebra M N f)\<close> subalgebra_def)
      then have ?thesis
        using f1 by metis }
    ultimately show ?thesis
      by (metis (no_types) \<open>point_measurable (fct_gen_subalgebra M N f) (space N) f\<close> \<open>subalgebra M (fct_gen_subalgebra M N f)\<close> subalgebra_def)
  qed
qed



definition countable_preimages where
"countable_preimages B Y = (\<lambda>n. if ((infinite B) \<or> (finite B \<and> n < card B)) then Y -` {(from_nat_into B) n} else {})"

lemma  count_pre_disj:
  fixes i::nat
  assumes "countable B"
  and "i \<noteq> j"
shows "(countable_preimages B Y) i \<inter> (countable_preimages B Y) j = {}"
proof (cases  "(countable_preimages B Y) i = {} \<or> (countable_preimages B Y) j = {}")
  case True
  thus ?thesis by auto
next
  case False
  hence "Y -` {(from_nat_into B) i} \<noteq> {} \<and> Y -` {(from_nat_into B) j} \<noteq> {}"  unfolding countable_preimages_def by meson
  have "(infinite B) \<or> (finite B \<and> i < card B \<and> j < card B)" using False unfolding countable_preimages_def
    by meson
  have "(from_nat_into B) i \<noteq> (from_nat_into B) j"
    by (metis False assms(1) assms(2) bij_betw_def countable_preimages_def from_nat_into_inj from_nat_into_inj_infinite lessThan_iff to_nat_on_finite)
  thus ?thesis
  proof -
    have f1: "\<forall>A f n. if infinite A \<or> finite A \<and> n < card A then countable_preimages A f n = f -` {from_nat_into A n::'a} else countable_preimages A f n = ({}::'b set)"
      by (meson countable_preimages_def)
    then have f2: "infinite B \<or> finite B \<and> i < card B"
      by (metis (no_types) False)
    have "infinite B \<or> finite B \<and> j < card B"
      using f1 by (meson False)
    then show ?thesis
      using f2 f1 \<open>from_nat_into B i \<noteq> from_nat_into B j\<close> by fastforce
  qed
qed

lemma count_pre_surj:
  assumes "countable B"
  and "w \<in> Y -`B"
shows "\<exists>i. w \<in> (countable_preimages B Y) i"
proof (cases "finite B")
  case True
    have "\<exists> i < card B. (from_nat_into B) i = Y w"
      by (metis True assms(1) assms(2) bij_betw_def from_nat_into_to_nat_on image_eqI lessThan_iff
          to_nat_on_finite vimageE)
    from this obtain i where "i< card B" and "(from_nat_into B) i = Y w" by blast
    hence "w \<in> (countable_preimages B Y) i"
      by (simp add: countable_preimages_def)
    thus "\<exists>i. w \<in> (countable_preimages B Y) i" by auto
  next
  case False
    hence "\<exists> i. (from_nat_into B) i = Y w"
      by (meson assms(1) assms(2) from_nat_into_to_nat_on vimageE)
    from this obtain i where  "(from_nat_into B) i = Y w" by blast
    hence "w \<in> (countable_preimages B Y) i"
      by (simp add: False countable_preimages_def)
    thus "\<exists>i. w \<in> (countable_preimages B Y) i" by auto
qed


lemma count_pre_img:
  assumes "x \<in> (countable_preimages B Y) n"
  shows "Y x = (from_nat_into B) n"
proof -
  have "x\<in> Y -` {(from_nat_into B) n}" using assms unfolding countable_preimages_def
    by (meson empty_iff)
  thus ?thesis by simp
qed


lemma count_pre_union_img:
  assumes "countable B"
  shows "Y -`B = (\<Union> i. (countable_preimages B Y) i)"
proof (cases "B = {}")
  case False
  have "Y -`B \<subseteq> (\<Union> i. (countable_preimages B Y) i)"
    by (simp add: assms count_pre_surj subset_eq)
  moreover have "(\<Union> i. (countable_preimages B Y) i) \<subseteq> Y -`B"
  proof -
    have f1: "\<forall>b A f n. (b::'b) \<notin> countable_preimages A f n \<or> (f b::'a) = from_nat_into A n"
      by (meson count_pre_img)
    have "range (from_nat_into B) = B"
      by (meson False assms range_from_nat_into)
    then show ?thesis
      using f1 by blast
  qed
  ultimately show ?thesis by simp
next
  case True
  hence "\<forall> i. (countable_preimages B Y) i = {}" unfolding countable_preimages_def by simp
  hence "(\<Union> i. (countable_preimages B Y) i) = {}" by auto
  moreover have "Y -`B = {}" using True by simp
  ultimately show ?thesis by simp
qed

lemma  count_pre_meas:
  assumes "point_measurable M (space N) Y"
  and "B\<subseteq> space N"
  and "countable B"
  shows "\<forall>i. (countable_preimages B Y) i \<inter> space M \<in> sets M"
proof
  fix i
  have "Y -`B = (\<Union> i. (countable_preimages B Y) i)" using assms
    by (simp add: count_pre_union_img)
  show "countable_preimages B Y i \<inter> space M \<in> sets M"
  proof (cases "countable_preimages B Y i = {}")
    case True
    thus ?thesis by simp
  next
    case False
    from this obtain y where "y \<in> countable_preimages B Y i" by auto
    hence "countable_preimages B Y i = Y -`{Y y}"
      by (metis False count_pre_img countable_preimages_def)
    have "Y y = from_nat_into B i"
      by (meson \<open>y \<in> countable_preimages B Y i\<close> count_pre_img)
    hence "Y y \<in> space N"
      by (metis UNIV_I UN_I \<open>y \<in> countable_preimages B Y i\<close> \<open>Y -`B = (\<Union> i. (countable_preimages B Y) i)\<close> assms(2)  empty_iff from_nat_into subsetCE vimage_empty)
    moreover have "Y y \<in> range Y" by simp
    thus ?thesis
      by (metis IntI \<open>countable_preimages B Y i = Y -` {Y y}\<close> assms(1) calculation point_measurable_def)
  qed
qed


lemma  disct_fct_point_measurable:
assumes "disc_fct f"
and "point_measurable M (space N) f"
shows "f\<in> measurable M N" unfolding measurable_def
proof
  show "f \<in> space M \<rightarrow> space N \<and> (\<forall>y\<in>sets N. f -` y \<inter> space M \<in> sets M)"
  proof
    show "f \<in> space M \<rightarrow> space N" using assms unfolding point_measurable_def by auto
    show "\<forall>y\<in>sets N. f -` y \<inter> space M \<in> sets M"
    proof
      fix y
      assume "y\<in> sets N"
      let ?imY = "range f \<inter> y"
      have "f-`y = f-`?imY" by auto
      moreover have "countable ?imY" using assms unfolding disc_fct_def by auto
      ultimately have "f -`y = (\<Union> i. (countable_preimages ?imY f) i)" using assms count_pre_union_img by metis
      hence yeq: "f -` y \<inter> space M = (\<Union> i. ((countable_preimages ?imY f) i) \<inter> space M)" by auto
      have "\<forall>i. countable_preimages ?imY f i \<inter> space M \<in> sets M"
        by (metis \<open>countable (range f \<inter> y)\<close> \<open>y \<in> sets N\<close> assms(2) inf_le2 le_inf_iff count_pre_meas  sets.Int_space_eq1)
      hence "(\<Union> i. ((countable_preimages ?imY f) i) \<inter> space M) \<in> sets M" by blast
      thus "f -` y \<inter> space M \<in> sets M" using yeq by simp
    qed
  qed
qed


lemma  set_point_measurable:
  assumes "point_measurable M (space N) Y"
  and "B \<subseteq> space N"
  and "countable B"
shows "(Y -`B) \<inter> space M \<in> sets M"
proof -
  have "Y -`B = (\<Union> i. (countable_preimages B Y) i)" using assms
    by (simp add: count_pre_union_img)
  hence "Y -`B \<inter> space M = (\<Union> i. ((countable_preimages B Y) i \<inter> space M))"
    by auto
  have "\<forall>i. (countable_preimages B Y) i \<inter> space M \<in> sets M" using assms by (simp add: count_pre_meas)
  hence "(\<Union> i. ((countable_preimages B Y) i \<inter> space M)) \<in> sets M" by blast
  show ?thesis
    using \<open>(\<Union>i. countable_preimages B Y i \<inter> space M) \<in> sets M\<close> \<open>Y -` B \<inter> space M = (\<Union>i. countable_preimages B Y i \<inter> space M)\<close> by auto
qed


subsection \<open>Definition of explicit conditional expectation\<close>

text \<open>This section is devoted to an explicit computation of a conditional expectation for random variables
that have a countable codomain. More precisely, the computed random variable is almost everywhere equal to a conditional
expectation of the random variable under consideration.\<close>

definition  img_dce where
  "img_dce M Y X = (\<lambda> y. if measure M ((Y -` {y}) \<inter> space M) = 0 then 0 else
    ((integral\<^sup>L M (\<lambda>w. ((X w) * (indicator ((Y -`{y})\<inter> space M) w))))/(measure M ((Y -` {y}) \<inter> space M))))"

definition  expl_cond_expect where
  "expl_cond_expect M Y X = (img_dce M Y X) \<circ> Y"

lemma  nn_expl_cond_expect_pos:
  assumes "\<forall>w \<in> space M. 0 \<le> X w"
shows "\<forall> w\<in> space M. 0 \<le> (expl_cond_expect M Y X) w"
proof
  fix w
  assume space: "w\<in> space M"
  show "0 \<le> (expl_cond_expect M Y X) w"
  proof (cases "measure M ((Y -` {Y w})\<inter> space M) = 0")
    case True
    thus "0 \<le> (expl_cond_expect M Y X) w" unfolding expl_cond_expect_def img_dce_def by simp
  next
    case False
    hence "Y -`{Y w} \<inter> space M \<in> sets M" using measure_notin_sets by blast
    let ?indA = "((\<lambda> x. indicator ((Y -`{Y w})\<inter> space M) x))"
    have "\<forall>w \<in> space M. 0 \<le> (X w) * (?indA w)" by (simp add: assms)
    hence  "0 \<le> (integral\<^sup>L M (\<lambda>w. ((X w) * (?indA w))))" by simp
    moreover have "(expl_cond_expect M Y X) w = (integral\<^sup>L M (\<lambda>w. ((X w) * (?indA w)))) / (measure M ((Y -` {Y w})\<inter> space M))"
      unfolding expl_cond_expect_def img_dce_def using False by simp
    moreover have "0 < measure M ((Y -` {Y w}) \<inter> space M)" using False by (simp add: zero_less_measure_iff)
    ultimately show "0 \<le> (expl_cond_expect M Y X) w" by simp
  qed
qed



lemma  expl_cond_expect_const:
  assumes "Y w = Y y"
  shows "expl_cond_expect M Y X w = expl_cond_expect M Y X y"
    unfolding expl_cond_expect_def img_dce_def
    by (simp add: assms)


lemma  expl_cond_exp_cong:
  assumes "\<forall>w\<in>space M. X w = Z w"
shows "\<forall>w\<in> space M. expl_cond_expect M Y X w = expl_cond_expect M Y Z w" unfolding expl_cond_expect_def img_dce_def
  by (metis (no_types, lifting) Bochner_Integration.integral_cong assms(1) o_apply)

(* example of a proof that IMO takes too long in Isabelle *)
lemma  expl_cond_exp_add:
  assumes "integrable M X"
  and "integrable M Z"
shows "\<forall>w\<in> space M. expl_cond_expect M Y (\<lambda>x. X x + Z x) w = expl_cond_expect M Y X w + expl_cond_expect M Y Z w"
proof
  fix w
  assume "w\<in> space M"
  define prY where "prY = measure M ((Y -` {Y w}) \<inter> space M)"
  show "expl_cond_expect M Y (\<lambda>x. X x + Z x) w = expl_cond_expect M Y X w + expl_cond_expect M Y Z w"
  proof (cases "prY = 0")
    case True
    thus ?thesis unfolding expl_cond_expect_def img_dce_def prY_def by simp
  next
    case False
    hence "(Y -` {Y w}) \<inter> space M \<in> sets M" unfolding prY_def using measure_notin_sets by blast
    let ?indA = "indicator ((Y -` {Y w}) \<inter> space M)::('a\<Rightarrow>real)"
    have "integrable M (\<lambda>x. X x * ?indA x)"
      using \<open>Y -` {Y w} \<inter> space M \<in> sets M\<close> assms(1) integrable_real_mult_indicator by blast
    moreover have "integrable M (\<lambda>x. Z x * ?indA x)"
      using \<open>Y -` {Y w} \<inter> space M \<in> sets M\<close> assms(2) integrable_real_mult_indicator by blast
    ultimately have "integral\<^sup>L M (\<lambda>x. X x * ?indA x + Z x * ?indA x) = integral\<^sup>L M (\<lambda>x. X x * ?indA x) + integral\<^sup>L M (\<lambda>x. Z x * ?indA x)"
      using Bochner_Integration.integral_add by blast
    moreover have "\<forall>x\<in> space M. X x * ?indA x + Z x * ?indA x = (X x + Z x) * ?indA x"
      by (simp add: indicator_def)
    ultimately have fsteq: "integral\<^sup>L M (\<lambda>x. (X x + Z x) * ?indA x) = integral\<^sup>L M (\<lambda>x. X x * ?indA x) + integral\<^sup>L M (\<lambda>x. Z x * ?indA x)"
      by (metis (no_types, lifting) Bochner_Integration.integral_cong)
    have "integral\<^sup>L M (\<lambda>x. (X x + Z x) * ?indA x/prY) = integral\<^sup>L M (\<lambda>x. (X x + Z x) * ?indA x)/prY"
      by simp
    also have "... = integral\<^sup>L M (\<lambda>x. X x * ?indA x)/prY + integral\<^sup>L M (\<lambda>x. Z x * ?indA x)/prY" using fsteq
      by (simp add: add_divide_distrib)
    also have "... = integral\<^sup>L M (\<lambda>x. X x * ?indA x/prY) + integral\<^sup>L M (\<lambda>x. Z x * ?indA x/prY)" by auto
    finally have "integral\<^sup>L M (\<lambda>x. (X x + Z x) * ?indA x/prY) = integral\<^sup>L M (\<lambda>x. X x * ?indA x/prY) + integral\<^sup>L M (\<lambda>x. Z x * ?indA x/prY)" .
    thus ?thesis using False unfolding expl_cond_expect_def img_dce_def
      by (simp add: add_divide_distrib fsteq)
  qed
qed


lemma expl_cond_exp_diff:
  assumes "integrable M X"
  and "integrable M Z"
shows "\<forall>w\<in> space M. expl_cond_expect M Y (\<lambda>x. X x - Z x) w = expl_cond_expect M Y X w - expl_cond_expect M Y Z w"
proof
  fix w
  assume "w\<in> space M"
  define prY where "prY = measure M ((Y -` {Y w}) \<inter> space M)"
  show "expl_cond_expect M Y (\<lambda>x. X x - Z x) w = expl_cond_expect M Y X w - expl_cond_expect M Y Z w"
  proof (cases "prY = 0")
    case True
    thus ?thesis unfolding expl_cond_expect_def img_dce_def prY_def by simp
  next
    case False
    hence "(Y -` {Y w}) \<inter> space M \<in> sets M" unfolding prY_def using measure_notin_sets by blast
    let ?indA = "indicator ((Y -` {Y w}) \<inter> space M)::('a\<Rightarrow>real)"
    have "integrable M (\<lambda>x. X x * ?indA x)"
      using \<open>Y -` {Y w} \<inter> space M \<in> sets M\<close> assms(1) integrable_real_mult_indicator by blast
    moreover have "integrable M (\<lambda>x. Z x * ?indA x)"
      using \<open>Y -` {Y w} \<inter> space M \<in> sets M\<close> assms(2) integrable_real_mult_indicator by blast
    ultimately have "integral\<^sup>L M (\<lambda>x. X x * ?indA x - Z x * ?indA x) = integral\<^sup>L M (\<lambda>x. X x * ?indA x) - integral\<^sup>L M (\<lambda>x. Z x * ?indA x)"
      using Bochner_Integration.integral_diff by blast
    moreover have "\<forall>x\<in> space M. X x * ?indA x - Z x * ?indA x = (X x - Z x) * ?indA x"
      by (simp add: indicator_def)
    ultimately have fsteq: "integral\<^sup>L M (\<lambda>x. (X x - Z x) * ?indA x) = integral\<^sup>L M (\<lambda>x. X x * ?indA x) - integral\<^sup>L M (\<lambda>x. Z x * ?indA x)"
      by (metis (no_types, lifting) Bochner_Integration.integral_cong)
    have "integral\<^sup>L M (\<lambda>x. (X x - Z x) * ?indA x/prY) = integral\<^sup>L M (\<lambda>x. (X x - Z x) * ?indA x)/prY"
      by simp
    also have "... = integral\<^sup>L M (\<lambda>x. X x * ?indA x)/prY - integral\<^sup>L M (\<lambda>x. Z x * ?indA x)/prY" using fsteq
      by (simp add: diff_divide_distrib)
    also have "... = integral\<^sup>L M (\<lambda>x. X x * ?indA x/prY) - integral\<^sup>L M (\<lambda>x. Z x * ?indA x/prY)" by auto
    finally have "integral\<^sup>L M (\<lambda>x. (X x - Z x) * ?indA x/prY) = integral\<^sup>L M (\<lambda>x. X x * ?indA x/prY) - integral\<^sup>L M (\<lambda>x. Z x * ?indA x/prY)" .
    thus ?thesis using False unfolding expl_cond_expect_def img_dce_def
      by (simp add: diff_divide_distrib fsteq)
  qed
qed

lemma  expl_cond_expect_prop_sets:
  assumes "disc_fct Y"
  and "point_measurable M (space N) Y"
  and "D = {w\<in> space M. Y w \<in> space N \<and> (P (expl_cond_expect M Y X w))}"
shows "D\<in> sets M"
proof -
  let ?C = "{y \<in> (Y`(space M)) \<inter> (space N). P (img_dce M Y X y)}"
  have "space M \<subseteq> UNIV" by simp
  hence "Y`(space M) \<subseteq> range Y" by auto
  hence "countable (Y`(space M))" using assms countable_subset unfolding disc_fct_def  by auto
  hence "countable ?C" using assms unfolding disc_fct_def by auto
  have eqset: "D = (\<Union> b\<in> ?C. Y-`{b})\<inter> space M"
  proof
    show "D\<subseteq> (\<Union> b\<in> ?C. Y-`{b})\<inter> space M"
    proof
      fix w
      assume "w\<in> D"
      hence "w\<in> space M \<and> Y w \<in> (space N) \<and> (P (expl_cond_expect M Y X w))"
        by (simp add: assms)
      hence "P (img_dce M Y X (Y w))" by (simp add: expl_cond_expect_def)
      hence "Y w \<in> ?C" using \<open>w \<in> space M \<and> Y w \<in> space N \<and> P (expl_cond_expect M Y X w)\<close> by blast
      thus "w\<in> (\<Union> b\<in> ?C. Y-`{b})\<inter> space M"
        using \<open>w \<in> space M \<and> Y w \<in> space N \<and> P (expl_cond_expect M Y X w)\<close> by blast
    qed
    show "(\<Union> b\<in> ?C. Y-`{b})\<inter> space M \<subseteq> D"
    proof
      fix w
      assume "w\<in> (\<Union> b\<in> ?C. Y-`{b})\<inter> space M"
      from this obtain b where "b\<in> ?C \<and> w\<in> Y-`{b}" by auto note bprops = this
      hence "Y w = b" by auto
      hence "Y w\<in> space N" using bprops by simp
      show "w \<in> D"
        by (metis (mono_tags, lifting) IntE \<open>Y w = b\<close> \<open>w \<in> (\<Union>b\<in>?C. Y -` {b}) \<inter> space M\<close> assms(3)
            bprops mem_Collect_eq o_apply expl_cond_expect_def)
    qed
  qed
  also have "... = (\<Union> b\<in> ?C. Y-`{b}\<inter> space M)" by blast
  finally have "D = (\<Union> b\<in> ?C. Y-`{b}\<inter> space M)".
  have "\<forall>b\<in> ?C. Y-`{b} \<inter> space M \<in> sets M" using assms unfolding point_measurable_def by auto
  hence "(\<Union> b\<in> ?C. Y-`{b}\<inter> space M) \<in> sets M" using \<open>countable ?C\<close> by blast
  thus ?thesis
    using \<open>D = (\<Union>b\<in>?C. Y -` {b} \<inter> space M)\<close> by blast
qed

lemma  expl_cond_expect_prop_sets2:
  assumes "disc_fct Y"
  and "point_measurable (fct_gen_subalgebra M N Y) (space N) Y"
  and "D = {w\<in> space M. Y w \<in> space N \<and> (P (expl_cond_expect M Y X w))}"
shows "D\<in> sets (fct_gen_subalgebra M N Y)"
proof -
  let ?C = "{y \<in> (Y`(space M)) \<inter> (space N). P (img_dce M Y X y)}"
  have "space M \<subseteq> UNIV" by simp
  hence "Y`(space M) \<subseteq> range Y" by auto
  hence "countable (Y`(space M))" using assms countable_subset unfolding disc_fct_def  by auto
  hence "countable ?C" using assms unfolding disc_fct_def by auto
  have eqset: "D = (\<Union> b\<in> ?C. Y-`{b})\<inter> space M"
  proof
    show "D\<subseteq> (\<Union> b\<in> ?C. Y-`{b})\<inter> space M"
    proof
      fix w
      assume "w\<in> D"
      hence "w\<in> space M \<and> Y w \<in> (space N) \<and> (P (expl_cond_expect M Y X w))"
        by (simp add: assms)
      hence "P (img_dce M Y X (Y w))" by (simp add: expl_cond_expect_def)
      hence "Y w \<in> ?C" using \<open>w \<in> space M \<and> Y w \<in> space N \<and> P (expl_cond_expect M Y X w)\<close> by blast
      thus "w\<in> (\<Union> b\<in> ?C. Y-`{b})\<inter> space M"
        using \<open>w \<in> space M \<and> Y w \<in> space N \<and> P (expl_cond_expect M Y X w)\<close> by blast
    qed
    show "(\<Union> b\<in> ?C. Y-`{b})\<inter> space M \<subseteq> D"
    proof
      fix w
      assume "w\<in> (\<Union> b\<in> ?C. Y-`{b})\<inter> space M"
      from this obtain b where "b\<in> ?C \<and> w\<in> Y-`{b}" by auto note bprops = this
      hence "Y w = b" by auto
      hence "Y w\<in> space N" using bprops by simp
      show "w \<in> D"
        by (metis (mono_tags, lifting) IntE \<open>Y w = b\<close> \<open>w \<in> (\<Union>b\<in>?C. Y -` {b}) \<inter> space M\<close> assms(3)
            bprops mem_Collect_eq o_apply expl_cond_expect_def)
    qed
  qed
  also have "... = (\<Union> b\<in> ?C. Y-`{b}\<inter> space M)" by blast
  finally have "D = (\<Union> b\<in> ?C. Y-`{b}\<inter> space M)".
  have "space M = space (fct_gen_subalgebra M N Y)"
    by (simp add: fct_gen_subalgebra_space)
  hence "\<forall>b\<in> ?C. Y-`{b} \<inter> space M \<in> sets (fct_gen_subalgebra M N Y)" using assms unfolding point_measurable_def by auto
  hence "(\<Union> b\<in> ?C. Y-`{b}\<inter> space M) \<in> sets (fct_gen_subalgebra M N Y)" using \<open>countable ?C\<close> by blast
  thus ?thesis
    using \<open>D = (\<Union>b\<in>?C. Y -` {b} \<inter> space M)\<close> by blast
qed





lemma  expl_cond_expect_disc_fct:
  assumes "disc_fct Y"
  shows "disc_fct (expl_cond_expect M Y X)"
   using assms unfolding disc_fct_def expl_cond_expect_def
    by (metis countable_image image_comp)







lemma  expl_cond_expect_point_meas:
  assumes "disc_fct Y"
  and "point_measurable M (space N) Y"
shows "point_measurable M UNIV (expl_cond_expect M Y X)"
proof -
  have "disc_fct (expl_cond_expect M Y X)" using assms by (simp add: expl_cond_expect_disc_fct)
  show ?thesis unfolding point_measurable_def
  proof
    show "(expl_cond_expect M Y X)`space M \<subseteq> UNIV" by simp
    show "\<forall>r\<in>range (expl_cond_expect M Y X) \<inter> UNIV. expl_cond_expect M Y X -` {r} \<inter> space M \<in> sets M"
      proof
      fix r
      assume "r\<in> range (expl_cond_expect M Y X) \<inter> UNIV"
      let ?D = "{w \<in> space M. Y w \<in> space N \<and> (expl_cond_expect M Y X w) = r}"
      have "?D \<in> sets M" using expl_cond_expect_prop_sets[of Y M N ?D "\<lambda>x. x = r" X] using assms by simp
      moreover have "expl_cond_expect M Y X -`{r}\<inter> space M = ?D"
      proof
        show "expl_cond_expect M Y X -`{r}\<inter> space M \<subseteq> ?D"
        proof
          fix w
          assume "w\<in> expl_cond_expect M Y X -`{r}\<inter> space M"
          hence "Y w \<in> space N"
            by (meson IntD2 assms(1) assms(2) disct_fct_point_measurable measurable_space)
          thus "w \<in> ?D"
            using \<open>w \<in> expl_cond_expect M Y X -` {r} \<inter> space M\<close> by blast
        qed
        show "?D \<subseteq> expl_cond_expect M Y X -`{r}\<inter> space M"
        proof
          fix w
          assume "w\<in> ?D"
          thus "w\<in> expl_cond_expect M Y X -`{r}\<inter> space M" by blast
        qed
      qed
      ultimately show "expl_cond_expect M Y X -` {r} \<inter> space M \<in> sets M" by simp
    qed
  qed
qed

lemma  expl_cond_expect_borel_measurable:
  assumes "disc_fct Y"
  and "point_measurable M (space N) Y"
shows "(expl_cond_expect M Y X) \<in> borel_measurable M" using expl_cond_expect_point_meas[of Y M] assms
          disct_fct_point_measurable[of "expl_cond_expect M Y X"]
        by (simp add: expl_cond_expect_disc_fct)



lemma  expl_cond_exp_borel:
  assumes "Y \<in> space M \<rightarrow> space N"
  and "disc_fct Y"
  and "\<forall>r\<in> range Y\<inter> space N. \<exists>A\<in> sets N. range Y\<inter> A = {r}"
  shows "(expl_cond_expect M Y X) \<in> borel_measurable (fct_gen_subalgebra M N Y)"
proof (intro borel_measurableI)
  fix S::"real set"
  assume "open S"
  show "expl_cond_expect M Y X -` S \<inter> space (fct_gen_subalgebra M N Y) \<in> sets (fct_gen_subalgebra M N Y)"
  proof (rule expl_cond_expect_prop_sets2)
    show "disc_fct Y" using assms by simp
    show "point_measurable (fct_gen_subalgebra M N Y) (space N) Y" using  assms
      by (simp add: singl_meas_if)
    show "expl_cond_expect M Y X -` S \<inter> space (fct_gen_subalgebra M N Y) = {w \<in> space M. Y w \<in> space N \<and> (expl_cond_expect M Y X w) \<in> S}"
    proof
      show " expl_cond_expect M Y X -` S \<inter> space (fct_gen_subalgebra M N Y) \<subseteq> {w \<in> space M. Y w \<in> space N \<and> expl_cond_expect M Y X w \<in> S}"
      proof
        fix x
        assume asm: "x \<in> expl_cond_expect M Y X -` S \<inter> space (fct_gen_subalgebra M N Y)"
        hence "expl_cond_expect M Y X x \<in> S" by auto
        moreover have  "x\<in> space M" using asm by (simp add:fct_gen_subalgebra_space)
        ultimately show "x \<in>{w \<in> space M. Y w \<in> space N \<and> expl_cond_expect M Y X w \<in> S}" using assms by auto
      qed
      show "{w \<in> space M. Y w \<in> space N \<and> expl_cond_expect M Y X w \<in> S} \<subseteq> expl_cond_expect M Y X -` S \<inter> space (fct_gen_subalgebra M N Y)"
      proof
        fix x
        assume asm2: "x \<in> {w \<in> space M. Y w \<in> space N \<and> expl_cond_expect M Y X w \<in> S}"
        hence "x\<in> space (fct_gen_subalgebra M N Y)" by (simp add:fct_gen_subalgebra_space)
        moreover have "x \<in> expl_cond_expect M Y X -`S" using asm2 by simp
        ultimately show "x \<in> expl_cond_expect M Y X -` S \<inter> space (fct_gen_subalgebra M N Y)" by simp
      qed
    qed
  qed
qed





lemma  expl_cond_expect_indic_borel_measurable:
  assumes "disc_fct Y"
  and "point_measurable M (space N) Y"
  and "B\<subseteq> space N"
  and "countable B"
  shows "(\<lambda>w. expl_cond_expect M Y X w * indicator (countable_preimages B Y n \<inter> space M) w)\<in> borel_measurable M"
proof -
  have "countable_preimages B Y n \<inter> space M \<in> sets M" using  assms by (auto simp add: count_pre_meas)
  have "(expl_cond_expect M Y X)\<in> borel_measurable M" using expl_cond_expect_point_meas[of Y M N X] assms
      disct_fct_point_measurable[of "expl_cond_expect M Y X"]
    by (simp add: expl_cond_expect_disc_fct)
  moreover have "(indicator (countable_preimages B Y n \<inter> space M))\<in> borel_measurable M"
    using \<open>countable_preimages B Y n \<inter> space M \<in> sets M\<close> borel_measurable_indicator by blast
  ultimately show ?thesis
    using borel_measurable_times by blast
qed


lemma (in finite_measure) dce_prod:
  assumes "point_measurable M (space N) Y"
   and "integrable M X"
   and "\<forall> w\<in> space M. 0 \<le> X w"
shows "\<forall> w. (Y w) \<in> space N \<longrightarrow> (expl_cond_expect M Y X) w * measure M ((Y -` {Y w})\<inter> space M) = integral\<^sup>L M (\<lambda>y. (X y) * (indicator ((Y -`{Y w})\<inter> space M) y))"
proof (intro allI impI)
  fix w
  assume "Y w\<in> space N"
  let ?indY = "(\<lambda>y. indicator ((Y -`{Y w})\<inter> space M) y)::'a \<Rightarrow> real"
  show "expl_cond_expect M Y X w * measure M ((Y -` {Y w})\<inter> space M) = integral\<^sup>L M (\<lambda>y. (X y) * ?indY y) "
  proof (cases "AE y in M. ?indY y = 0")
    case True
    (* Very long proof, Sledgehammer was lost. Everything had to be detailed *)
    hence "emeasure M ((Y -` {Y w})\<inter> space M) = 0"
    proof -
      have "AE y in M. y \<notin>  Y -` {Y w} \<inter> space M"
        using True eventually_elim2 by auto
      hence "\<exists>N\<in> null_sets M.{x\<in> space M. \<not>(x\<notin> Y -` {Y w} \<inter> space M)} \<subseteq> N"
        using eventually_ae_filter[of "\<lambda>x. x \<notin> Y -` {Y w} \<inter> space M" M] by simp
      hence "\<exists>N\<in> null_sets M. {x\<in> space M. x\<in> Y -` {Y w} \<inter> space M} \<subseteq> N" by simp
      from this obtain N where "N\<in> null_sets M" and "{x\<in> space M. x\<in> Y -` {Y w} \<inter> space M} \<subseteq> N" by auto
          note Nprops = this
      have "{x\<in> space M. x\<in> Y -` {Y w}} \<subseteq> N" using Nprops by auto
      hence "emeasure M {x\<in> space M. x\<in> Y -` {Y w}} \<le> emeasure M N"
        by (simp add: emeasure_mono Nprops(1) null_setsD2)
      thus ?thesis
        by (metis (no_types, lifting) Collect_cong Int_def Nprops(1) le_zero_eq null_setsD1)
    qed
    hence "enn2real (emeasure M ((Y -` {Y w})\<inter> space M)) = 0" by simp
    hence "measure M ((Y -` {Y w})\<inter> space M) = 0" unfolding measure_def by simp
    hence lhs: "expl_cond_expect M Y X w = 0" unfolding expl_cond_expect_def img_dce_def by simp
    have  zer: "AE y in M. (X y) * ?indY y = (\<lambda>y. 0) y" using True by auto
    hence rhs: "integral\<^sup>L M  (\<lambda>y. (X y) * ?indY y) = 0"
    proof -
      have "\<forall> w\<in> space M. 0 \<le> X w * ?indY w" using assms by simp
      have "integrable M (\<lambda>y. (X y) * ?indY y)" using assms
        by (metis (mono_tags, lifting) IntI UNIV_I \<open>Y w \<in> space N\<close> image_eqI integrable_cong integrable_real_mult_indicator point_measurable_def)
      hence "(\<lambda>y. (X y) * ?indY y) \<in> borel_measurable M" by blast
      thus ?thesis using zer integral_cong_AE[of "(\<lambda>y. (X y) * ?indY y)" M "\<lambda>y. 0"] by simp
    qed
    thus "expl_cond_expect M Y X w*measure M ((Y -` {Y w})\<inter> space M) = integral\<^sup>L M (\<lambda>y. (X y) * ?indY y)" using lhs rhs by simp
  next
    case False
    hence "\<not>(AE y in M. y \<notin> (Y -`{Y w})\<inter> space M)"
      by (simp add: indicator_eq_0_iff)
    hence "emeasure M ((Y -` {Y w})\<inter> space M) \<noteq> 0"
    proof -
      have "(Y -` {Y w})\<inter> space M\<in> sets M"
        by (meson IntI UNIV_I \<open>Y w \<in> space N\<close> assms(1) image_eqI point_measurable_def)
      have "(Y -` {Y w})\<inter> space M \<notin> null_sets M"
        using \<open>\<not> (AE y in M. y \<notin> Y -` {Y w} \<inter> space M)\<close> eventually_ae_filter by blast
      thus ?thesis
        using \<open>Y -` {Y w} \<inter> space M \<in> sets M\<close> by blast
    qed
    hence "measure M ((Y -` {Y w})\<inter> space M) \<noteq> 0"
      by (simp add: emeasure_eq_measure)
    thus "expl_cond_expect M Y X w* measure M ((Y -` {Y w})\<inter> space M) = integral\<^sup>L M (\<lambda>y. (X y) * ?indY y)" unfolding expl_cond_expect_def img_dce_def
      using o_apply by auto
  qed
qed



lemma  expl_cond_expect_const_exp:
  shows "integral\<^sup>L M (\<lambda>y. expl_cond_expect M Y X w * (indicator (Y -` {Y w} \<inter> space M)) y) =
    integral\<^sup>L M (\<lambda>y. expl_cond_expect M Y X y * (indicator (Y -` {Y w} \<inter> space M)) y)"
proof -
  let ?ind = "(indicator (Y -` {Y w} \<inter> space M))"
  have "\<forall> y\<in> space M. expl_cond_expect M Y X w * ?ind y = expl_cond_expect M Y X y * ?ind y"
  proof
    fix y
    assume "y\<in> space M"
    show "expl_cond_expect M Y X w * ?ind y = expl_cond_expect M Y X y * ?ind y"
    proof (cases "y\<in> Y -` {Y w} \<inter> space M")
      case False
      thus ?thesis by simp
    next
      case True
      hence "Y w = Y y" by auto
      hence "expl_cond_expect M Y X w = expl_cond_expect M Y X y"
        using expl_cond_expect_const[of Y w y M X] by simp
      thus ?thesis by simp
    qed
  qed
  thus ?thesis
    by (meson Bochner_Integration.integral_cong)
qed

lemma  nn_expl_cond_expect_const_exp:
  assumes "\<forall>w\<in> space M. 0 \<le> X w"
  shows "integral\<^sup>N M (\<lambda>y. expl_cond_expect M Y X w * (indicator (Y -` {Y w} \<inter> space M)) y) =
    integral\<^sup>N M (\<lambda>y. expl_cond_expect M Y X y * (indicator (Y -` {Y w} \<inter> space M)) y)"
proof -
  let ?ind = "(indicator (Y -` {Y w} \<inter> space M))"
  have forall: "\<forall> y\<in> space M. expl_cond_expect M Y X w * ?ind y = expl_cond_expect M Y X y * ?ind y"
  proof
    fix y
    assume "y\<in> space M"
    show "expl_cond_expect M Y X w * ?ind y = expl_cond_expect M Y X y * ?ind y"
    proof (cases "y\<in> Y -` {Y w} \<inter> space M")
      case False
      thus ?thesis by simp
    next
      case True
      hence "Y w = Y y" by auto
      hence "expl_cond_expect M Y X w = expl_cond_expect M Y X y"
        using expl_cond_expect_const[of Y] by blast
      thus ?thesis by simp
    qed
  qed
  show ?thesis
    by (metis (no_types, lifting) forall nn_integral_cong)
qed


lemma (in finite_measure) nn_expl_cond_bounded:
  assumes "\<forall>w\<in> space M. 0 \<le> X w"
  and "integrable M X"
  and "point_measurable M (space N) Y"
  and "w\<in> space M"
  and "Y w\<in> space N"
  shows "integral\<^sup>N M (\<lambda>y. expl_cond_expect M Y X y * (indicator (Y -` {Y w} \<inter> space M)) y) < \<infinity>"
proof -
  let ?ind = "(indicator (Y -` {Y w} \<inter> space M))::'a\<Rightarrow>real"
  have "0 \<le> expl_cond_expect M Y X w" using assms nn_expl_cond_expect_pos[of M X Y] by simp
  have "integrable M (\<lambda>y. expl_cond_expect M Y X w * ?ind y)"
  proof -
    have eq: "(Y -`{Y w} \<inter> space M) \<inter> space M = (Y -`{Y w} \<inter> space M)" by auto
    have "(Y -` {Y w} \<inter> space M) \<in> sets M" using assms
      by (simp add: point_measurable_def)
    moreover have "emeasure M (Y -`{Y w} \<inter> space M) < \<infinity>" by (simp add: inf.strict_order_iff)
    ultimately have "integrable M (\<lambda>y. ?ind y)"
      using integrable_indicator_iff[of M "(Y -`{Y w} \<inter> space M)"] by simp
    thus ?thesis using integrable_mult_left_iff[of M "expl_cond_expect M Y X w" "?ind"] by blast
  qed
  have "\<forall>y\<in> space M. 0 \<le> expl_cond_expect M Y X w * ?ind y"
    using \<open>0 \<le> expl_cond_expect M Y X w\<close> mult_nonneg_nonneg by blast
  hence "\<forall>y\<in> space M. expl_cond_expect M Y X w * ?ind y = norm (expl_cond_expect M Y X w * ?ind y)" by auto
  hence inf: "integral\<^sup>N M (\<lambda>y. expl_cond_expect M Y X w * ?ind y) < \<infinity>"
    using integrable_iff_bounded[of M "(\<lambda>y. expl_cond_expect M Y X w * ?ind y)"]
      \<open>0 \<le> expl_cond_expect M Y X w\<close>  real_norm_def nn_integral_cong
    by (metis (no_types, lifting) \<open>integrable M (\<lambda>y. expl_cond_expect M Y X w * indicator (Y -` {Y w} \<inter> space M) y)\<close>)
  have "integral\<^sup>N M (\<lambda>y. expl_cond_expect M Y X y * ?ind y) =
    integral\<^sup>N M (\<lambda>y. expl_cond_expect M Y X w * ?ind y)" using assms
    by (simp add: nn_expl_cond_expect_const_exp)
  also have "... < \<infinity>"  using inf by simp
  finally show ?thesis .
qed


lemma (in finite_measure)  count_prod:
  fixes Y::"'a\<Rightarrow>'b"
  assumes "B\<subseteq> space N"
  and "point_measurable M (space N) Y"
  and "integrable M X"
  and "\<forall> w \<in> space M. 0 \<le> X w"
shows "\<forall>i. integral\<^sup>L M (\<lambda>y. (X y) * (indicator (countable_preimages B Y i \<inter> space M)) y) =
  integral\<^sup>L M (\<lambda>y. (expl_cond_expect M Y X y) * (indicator (countable_preimages B Y i \<inter> space M)) y)"
proof
  fix i
  show "integral\<^sup>L M (\<lambda>y. X y * indicator (countable_preimages B Y i \<inter> space M) y) =
         integral\<^sup>L M (\<lambda>y. expl_cond_expect M Y X y * indicator (countable_preimages B Y i \<inter> space M) y)"
  proof (cases "countable_preimages B Y i \<inter> space M = {}")
    case True
    thus ?thesis by simp
  next
    case False
    from this obtain w where "w\<in> countable_preimages B Y i" by auto
    hence "Y w = (from_nat_into B) i" by (meson count_pre_img)
    hence "Y w \<in> B"
    proof (cases "infinite B")
      case True
      thus ?thesis
        by (simp add: \<open>Y w = from_nat_into B i\<close> from_nat_into infinite_imp_nonempty)
    next
      case False
      thus ?thesis
        by (metis Finite_Set.card_0_eq \<open>Y w = from_nat_into B i\<close> \<open>w \<in> countable_preimages B Y i\<close> countable_preimages_def equals0D from_nat_into gr_implies_not0)
    qed
    let ?ind = "(indicator (Y -` {Y w} \<inter> space M))::'a\<Rightarrow>real"
    have "integral\<^sup>L M (\<lambda>y. (X y) * (indicator (countable_preimages B Y i \<inter> space M)) y) = integral\<^sup>L M (\<lambda>y. X y * ?ind y)"
      by (metis (no_types, hide_lams) \<open>Y w = from_nat_into B i\<close> \<open>\<And>thesis. (\<And>w. w \<in> countable_preimages B Y i \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> countable_preimages_def empty_iff)
    also have "... =
      expl_cond_expect M Y X w * measure M (Y -` {Y w} \<inter> space M)"  using dce_prod[of N Y X]
       by (metis (no_types, lifting) \<open>Y w \<in> B\<close> assms subsetCE)
    also have "... = expl_cond_expect M Y X w * (integral\<^sup>L M ?ind)"
       by auto
    also have "... = integral\<^sup>L M (\<lambda>y. expl_cond_expect M Y X w * ?ind y)"
       by auto
    also have "... = integral\<^sup>L M (\<lambda>y. expl_cond_expect M Y X y * ?ind y)"
    proof -
      have "\<forall> y\<in> space M. expl_cond_expect M Y X w * ?ind y = expl_cond_expect M Y X y * ?ind y"
      proof
        fix y
        assume "y\<in> space M"
        show "expl_cond_expect M Y X w * ?ind y = expl_cond_expect M Y X y * ?ind y"
        proof (cases "y\<in> Y -` {Y w} \<inter> space M")
          case False
          thus ?thesis by simp
        next
          case True
          hence "Y w = Y y" by auto
          hence "expl_cond_expect M Y X w = expl_cond_expect M Y X y"
            using expl_cond_expect_const[of Y] by blast
          thus ?thesis by simp
        qed
      qed
      thus ?thesis
        by (meson Bochner_Integration.integral_cong)
    qed
    also have "... = integral\<^sup>L M (\<lambda>y. expl_cond_expect M Y X y * indicator (countable_preimages B Y i \<inter> space M) y)"
      by (metis (no_types, hide_lams) \<open>Y w = from_nat_into B i\<close> \<open>\<And>thesis. (\<And>w. w \<in> countable_preimages B Y i \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> countable_preimages_def empty_iff)
    finally show ?thesis .
  qed
qed



lemma (in finite_measure) count_pre_integrable:
  assumes "point_measurable M (space N) Y"
  and "disc_fct Y"
  and "B\<subseteq> space N"
  and "countable B"
  and "integrable M X"
  and "\<forall> w \<in> space M. 0 \<le> X w"
shows "integrable M (\<lambda>w. expl_cond_expect M Y X w * indicator (countable_preimages B Y n \<inter> space M) w)"
proof-
  have "integral\<^sup>L M (\<lambda>y. (X y) * (indicator (countable_preimages B Y n \<inter> space M)) y) =
  integral\<^sup>L M (\<lambda>y. (expl_cond_expect M Y X y) * (indicator (countable_preimages B Y n \<inter> space M)) y)" using assms count_prod
    by blast
  have "\<forall>w \<in> space M. 0 \<le> (expl_cond_expect M Y X w) * (indicator (countable_preimages B Y n \<inter> space M)) w"
    by (simp add: assms nn_expl_cond_expect_pos)
  have "countable_preimages B Y n \<inter> space M \<in> sets M" using count_pre_meas[of M] assms by auto
  hence "integrable M (\<lambda>w. X w * indicator (countable_preimages B Y n \<inter> space M) w)"
    using assms integrable_real_mult_indicator by blast
  show ?thesis
  proof (rule integrableI_nonneg)
    show "(\<lambda>w. expl_cond_expect M Y X w * indicator (countable_preimages B Y n \<inter> space M) w)\<in> borel_measurable M"
    proof -
      have "(expl_cond_expect M Y X)\<in> borel_measurable M" using expl_cond_expect_point_meas[of Y M N X] assms
          disct_fct_point_measurable[of "expl_cond_expect M Y X"]
        by (simp add: expl_cond_expect_disc_fct)
      moreover have "(indicator (countable_preimages B Y n \<inter> space M))\<in> borel_measurable M"
        using \<open>countable_preimages B Y n \<inter> space M \<in> sets M\<close> borel_measurable_indicator by blast
      ultimately show ?thesis
        using borel_measurable_times by blast
    qed
    show "AE x in M. 0 \<le> expl_cond_expect M Y X x * indicator (countable_preimages B Y n \<inter> space M) x"
      by (simp add: \<open>\<forall>w\<in>space M. 0 \<le> expl_cond_expect M Y X w * indicator (countable_preimages B Y n \<inter> space M) w\<close>)
    show "(\<integral>\<^sup>+ x. ennreal (expl_cond_expect M Y X x * indicator (countable_preimages B Y n \<inter> space M) x) \<partial>M) < \<infinity>"
    proof (cases "countable_preimages B Y n \<inter> space M = {}")
      case True
      thus ?thesis by simp
    next
      case False
      from this obtain w where "w\<in> countable_preimages B Y n\<inter> space M" by auto
      hence "countable_preimages B Y n = Y -`{Y w}"
        by (metis IntD1 count_pre_img countable_preimages_def equals0D)
      have "w\<in> space M" using False
        using \<open>w \<in> countable_preimages B Y n \<inter> space M\<close> by blast
      moreover have "Y w \<in> space N"
        by (meson \<open>w \<in> space M\<close> assms(1) assms(2) disct_fct_point_measurable measurable_space)
      ultimately show ?thesis using assms nn_expl_cond_bounded[of X N Y]
        using \<open>countable_preimages B Y n = Y -` {Y w}\<close> by presburger
    qed
  qed
qed





lemma (in finite_measure) nn_cond_expl_is_cond_exp_tmp:
  assumes "\<forall> w\<in> space M. 0 \<le> X w"
  and "integrable M X"
  and "disc_fct  Y"
  and "point_measurable M (space M') Y"
shows "\<forall> A \<in> sets M'. integrable M (\<lambda>w. ((expl_cond_expect M Y X) w) * (indicator ((Y -`A)\<inter> (space M)) w)) \<and>
  integral\<^sup>L M (\<lambda>w. (X w) * (indicator ((Y -`A)\<inter> (space M)) w)) =
  integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y X) w) * (indicator ((Y -`A) \<inter> (space M))) w)"
proof
  fix A
  assume "A \<in> sets M'"
  let ?imA = "A \<inter> (range Y)"
  have "countable ?imA" using assms disc_fct_def by blast
  have "Y -`A = Y -`?imA" by auto
  define prY where "prY = countable_preimages ?imA Y"
  have un: "Y -`?imA = (\<Union> i. prY i)" using \<open>countable ?imA\<close>
    by (metis count_pre_union_img prY_def)
   have "(Y -`?imA) \<inter> (space M) = (\<Union> i. prY i) \<inter> (space M)" using \<open>Y -`A = Y -`?imA\<close> un  by simp
   also have "... = (\<Union> i. (prY i) \<inter> (space M))" by blast
   finally have eq2: "(Y -`?imA) \<inter> (space M) = (\<Union> i. (prY i) \<inter> (space M))".
   define indpre::"nat \<Rightarrow> 'a \<Rightarrow> real" where "indpre = (\<lambda> i x. (indicator ((prY i) \<inter> (space M))) x)"
   have "\<forall> i. indpre i \<in> borel_measurable M"
   proof
     fix i
     show "indpre i \<in> borel_measurable M" unfolding indpre_def prY_def
     proof (rule borel_measurable_indicator, cases "countable_preimages (A \<inter> range Y) Y i \<inter> space M = {}")
       case True
       thus "countable_preimages (A \<inter> range Y) Y i \<inter> space M \<in> sets M" by simp
     next
       case False
       from this obtain x where "x\<in> countable_preimages (A \<inter> range Y) Y i \<inter> space M" by blast
           hence "Y x \<in> space M'"
             by (metis Int_iff UN_I \<open>A \<in> sets M'\<close> \<open>prY \<equiv> countable_preimages (A \<inter> range Y) Y\<close> imageE
                 rangeI sets.sets_into_space subset_eq un vimage_eq)
           thus "countable_preimages (A \<inter> range Y) Y i \<inter> space M \<in> sets M"
             by (metis IntE IntI \<open>x \<in> countable_preimages (A \<inter> range Y) Y i \<inter> space M\<close> assms(4)
                 count_pre_img countable_preimages_def empty_iff point_measurable_def rangeI)
     qed
   qed
   have "\<forall>i. integrable M (\<lambda>w. (X w) * indpre i w)"
   proof
     fix i
     show "integrable M (\<lambda>w. (X w) * indpre i w)" unfolding indpre_def prY_def
     proof (rule integrable_real_mult_indicator)
       show "countable_preimages (A \<inter> range Y) Y i \<inter> space M \<in> sets M"
       proof (cases "countable_preimages (A \<inter> range Y) Y i = {}")
         case True
         thus "countable_preimages (A \<inter> range Y) Y i \<inter> space M \<in> sets M"  by (simp add: True)
       next
         case False
         hence "Y -` {(from_nat_into (A \<inter> range Y)) i} \<noteq> {}"  unfolding countable_preimages_def by meson
         have "(infinite (A \<inter> range Y)) \<or> (finite (A \<inter> range Y) \<and> i < card (A \<inter> range Y))" using False unfolding countable_preimages_def
           by meson
         show ?thesis
           by (metis \<open>A \<in> sets M'\<close> \<open>countable (A \<inter> range Y)\<close> assms(4) count_pre_meas le_inf_iff
               range_from_nat_into sets.Int_space_eq1 sets.empty_sets sets.sets_into_space subset_range_from_nat_into)
       qed
       show "integrable M X" using assms by simp
     qed
   qed
   hence prod_bm: "\<forall> i. (\<lambda>w. (X w) * indpre i w) \<in> borel_measurable M"
     by (simp add: assms(2) borel_measurable_integrable borel_measurable_times)
   have posprod: "\<forall> i w. 0 \<le> (X w) * indpre i w"
   proof (intro allI)
     fix i
     fix w
     show "0 \<le> (X w) * indpre i w"
       by (metis IntE assms(1) indicator_pos_le indicator_simps(2) indpre_def mult_eq_0_iff mult_sign_intros(1))
   qed
   let ?indA = "indicator ((Y -`(A \<inter> range Y))\<inter> (space M))::'a\<Rightarrow>real"

   have "\<forall> i j. i \<noteq> j \<longrightarrow> ((prY i) \<inter> (space M)) \<inter> ((prY j) \<inter> (space M)) = {}"
     by (simp add: \<open>countable (A \<inter> range Y)\<close> \<open>prY \<equiv> countable_preimages (A \<inter> range Y) Y\<close> count_pre_disj inf_commute inf_sup_aci(3))
   hence sumind: "\<forall>x. (\<lambda>i. indpre i x) sums ?indA x" using \<open>countable ?imA\<close> eq2 unfolding prY_def indpre_def
     by (metis indicator_sums)
   hence sumxlim: "\<forall>x. (\<lambda>i. (X x) * indpre i x::real) sums ((X x) * indicator ((Y -`?imA) \<inter> (space M)) x)" using \<open>countable ?imA\<close> unfolding prY_def
     using sums_mult by blast
   hence sum: "\<forall>x. (\<Sum> i.((X x) * indpre i x)::real) = (X x) * indicator ((Y -`?imA) \<inter> (space M)) x"  by (metis sums_unique)
   hence b: "\<forall> w. 0 \<le> (\<Sum> i.((X w) * indpre i w))" using suminf_nonneg
     by (metis \<open>\<forall>x. (\<lambda>i. X x * indpre i x) sums (X x * indicator (Y -` (A \<inter> range Y) \<inter> space M) x)\<close> posprod summable_def)
   have sumcondlim: "\<forall>x. (\<lambda>i. (expl_cond_expect M Y X x) * indpre i x::real) sums ((expl_cond_expect M Y X x) * ?indA x)" using \<open>countable ?imA\<close> unfolding prY_def
     using sums_mult sumind by blast

   have "integrable M (\<lambda>w. (X w) * ?indA w)"
   proof (rule integrable_real_mult_indicator)
     show "Y -` (A\<inter> range Y) \<inter> space M \<in> sets M"
       using \<open>A \<in> sets M'\<close> assms(3) assms(4) disct_fct_point_measurable measurable_sets
       by (metis \<open>Y -` A = Y -` (A \<inter> range Y)\<close>)
     show "integrable M X" using assms by simp
   qed
   hence intsum: "integrable M (\<lambda>w. (\<Sum>i. ((X w) * indpre i w)))" using sum
       integrable_cong[of M M "\<lambda> w.(X w) * (indicator ((Y -`A)\<inter> (space M)) w)" "\<lambda>w. (\<Sum> i.((X w) * indpre i w))"]
     using \<open>Y -` A = Y -` (A \<inter> range Y)\<close> by presburger
   have "integral\<^sup>L M (\<lambda>w. (X w) * ?indA w) = integral\<^sup>L M (\<lambda>w. (\<Sum> i.((X w) * indpre i w)))"
     using \<open>Y -` A = Y -` (A \<inter> range Y)\<close> sum by auto
   also have "... =
      \<integral>\<^sup>+ w.   ((\<Sum> i. ((X w) * indpre i w))) \<partial>M" using nn_integral_eq_integral
     by (metis (mono_tags, lifting) AE_I2 intsum b  nn_integral_cong)
   also have "(\<integral>\<^sup>+ w.   ((\<Sum> i. ((X w) * indpre i w))) \<partial>M) =  \<integral>\<^sup>+ w.   ((\<Sum> i. ennreal ((X w) * indpre i w))) \<partial>M" using suminf_ennreal2 summable_def posprod sum sumxlim
   proof -
     { fix aa :: 'a
       have "\<forall>a. ennreal (\<Sum>n. X a * indpre n a) = (\<Sum>n. ennreal (X a * indpre n a))"
         by (metis (full_types) posprod suminf_ennreal2 summable_def sumxlim)
       then have "(\<integral>\<^sup>+ a. ennreal (\<Sum>n. X a * indpre n a) \<partial>M) = (\<integral>\<^sup>+ a. (\<Sum>n. ennreal (X a * indpre n a)) \<partial>M) \<or> ennreal (\<Sum>n. X aa * indpre n aa) = (\<Sum>n. ennreal (X aa * indpre n aa))"
         by metis }
     then show ?thesis
       by presburger
   qed
   also have "... = (\<Sum>i. integral\<^sup>N M ((\<lambda>i w. (X w) * indpre i w) i))"
   proof (intro nn_integral_suminf)
     fix i
     show "(\<lambda>x. ennreal (X x * indpre i x))\<in> borel_measurable M"
       using measurable_compose_rev measurable_ennreal prod_bm by blast
   qed
   also have "... = (\<Sum>i. integral\<^sup>N M ((\<lambda>i w. (expl_cond_expect M Y X w) * indpre i w) i))"
   proof (intro suminf_cong)
     fix n
     have "A \<inter> range Y \<subseteq> space M'"
       using \<open>A \<in> sets M'\<close> sets.Int_space_eq1 by auto
     have "integral\<^sup>N M (\<lambda>w. (X w) * indpre n w) = integral\<^sup>L M (\<lambda>w. (X w) * indpre n w)"
       using nn_integral_eq_integral[of M "\<lambda>w. (X w) * indpre n w"]
       by (simp add: \<open>\<forall>i. integrable M (\<lambda>w. X w * indpre i w)\<close> posprod)
     also have "... = integral\<^sup>L M (\<lambda>w. (expl_cond_expect M Y X) w * indpre n w)"
     proof -
       have "integral\<^sup>L M (\<lambda>w. X w * indicator (countable_preimages (A \<inter> range Y) Y n \<inter> space M) w) =
         integral\<^sup>L M (\<lambda>w. expl_cond_expect M Y X w * indicator (countable_preimages (A \<inter> range Y) Y n \<inter> space M) w)"
         using count_prod[of "A\<inter> range Y" "M'" Y X ] assms \<open>A \<inter> range Y \<subseteq> space M'\<close> by blast
       thus ?thesis
         using \<open>indpre \<equiv> \<lambda>i. indicator (prY i \<inter> space M)\<close> prY_def by presburger
     qed
     also have "... = integral\<^sup>N M (\<lambda>w. (expl_cond_expect M Y X) w * indpre n w)"
     proof -
       have "integrable M (\<lambda>w. (expl_cond_expect M Y X) w * indpre n w)" unfolding indpre_def prY_def
       using count_pre_integrable assms \<open>A \<inter> range Y \<subseteq> space M'\<close> \<open>countable (A \<inter> range Y)\<close> by blast
       moreover have "AE w in M. 0 \<le> (expl_cond_expect M Y X) w * indpre n w"
         by (simp add: \<open>indpre \<equiv> \<lambda>i. indicator (prY i \<inter> space M)\<close> assms(1) nn_expl_cond_expect_pos)
       ultimately show ?thesis by (simp add:nn_integral_eq_integral)
     qed
     finally show "integral\<^sup>N M (\<lambda>w. (X w) * indpre n w) = integral\<^sup>N M (\<lambda>w. (expl_cond_expect M Y X) w * indpre n w)" .
   qed
   also have "... = integral\<^sup>N M (\<lambda>w. \<Sum>i. ((expl_cond_expect M Y X w) * indpre i w))"
   proof -
     have "(\<lambda>x. (\<Sum>i. ennreal (expl_cond_expect M Y X x * indpre i x))) =
      (\<lambda>x. ennreal (\<Sum>i. (expl_cond_expect M Y X x * indpre i x)))"
     proof-
       have posex: "\<forall> i x. 0 \<le> (expl_cond_expect M Y X x) * (indpre i x)"
         by (metis IntE \<open>indpre \<equiv> \<lambda>i. indicator (prY i \<inter> space M)\<close> assms(1) indicator_pos_le indicator_simps(2) mult_eq_0_iff mult_sign_intros(1) nn_expl_cond_expect_pos)
       have "\<forall>x. (\<Sum>i. ennreal (expl_cond_expect M Y X x * indpre i x)) =  (ennreal (\<Sum>i. (expl_cond_expect M Y X x * indpre i x)))"
       proof
         fix x
         show "(\<Sum>i. ennreal (expl_cond_expect M Y X x * indpre i x)) =  (ennreal (\<Sum>i. (expl_cond_expect M Y X x * indpre i x)))"
           using suminf_ennreal2[of "\<lambda>i. (expl_cond_expect M Y X x * indpre i x)"] sumcondlim summable_def posex
         proof -
           have f1: "summable (\<lambda>n. expl_cond_expect M Y X x * indpre n x)"
             using sumcondlim summable_def by blast
           obtain nn :: nat where
             "\<not> 0 \<le> expl_cond_expect M Y X x * indpre nn x \<or> \<not> summable (\<lambda>n. expl_cond_expect M Y X x * indpre n x) \<or> ennreal (\<Sum>n. expl_cond_expect M Y X x * indpre n x) = (\<Sum>n. ennreal (expl_cond_expect M Y X x * indpre n x))"
             by (metis (full_types) \<open>\<lbrakk>\<And>i. 0 \<le> expl_cond_expect M Y X x * indpre i x; summable (\<lambda>i. expl_cond_expect M Y X x * indpre i x)\<rbrakk> \<Longrightarrow> (\<Sum>i. ennreal (expl_cond_expect M Y X x * indpre i x)) = ennreal (\<Sum>i. expl_cond_expect M Y X x * indpre i x)\<close>)
           then show ?thesis
             using f1 posex by presburger
         qed
       qed
       thus ?thesis by simp
     qed
     have "\<forall>i. (\<lambda>w. (expl_cond_expect M Y X w) * indpre i w) \<in> borel_measurable M"
     proof -
       show ?thesis
         using \<open>\<forall>i. (indpre i)\<in> borel_measurable M\<close> assms(3) assms(4) borel_measurable_times expl_cond_expect_borel_measurable by blast
     qed
     hence "\<And>i. (\<lambda>x. ennreal (expl_cond_expect M Y X x * indpre i x))\<in> borel_measurable M"
       using measurable_compose_rev measurable_ennreal by blast
     thus ?thesis using nn_integral_suminf[of "(\<lambda>i w.  (expl_cond_expect M Y X w) * indpre i w)" M, symmetric]
       using \<open>(\<lambda>x. \<Sum>i. ennreal (expl_cond_expect M Y X x * indpre i x)) = (\<lambda>x. ennreal (\<Sum>i. expl_cond_expect M Y X x * indpre i x))\<close> by auto
   qed
   also have "... = integral\<^sup>N M (\<lambda>w. (expl_cond_expect M Y X w) * ?indA w)"
     using sumcondlim
     by (metis (no_types, lifting) sums_unique)
   also have "... = integral\<^sup>L M (\<lambda>w. (expl_cond_expect M Y X w) * ?indA w)"
   proof -
     have scdint: "integrable M (\<lambda>w. (expl_cond_expect M Y X w) * ?indA w)"
     proof -
       have rv: "(\<lambda>w. (expl_cond_expect M Y X w) * indicator ((Y -`?imA) \<inter> (space M)) w) \<in> borel_measurable M"
       proof -
         have "expl_cond_expect M Y X \<in> borel_measurable M" using expl_cond_expect_borel_measurable
           using assms by blast
         moreover have "(Y -`?imA) \<inter> (space M) \<in> sets M"
           by (metis \<open>A \<in> sets M'\<close> \<open>Y -` A = Y -` (A \<inter> range Y)\<close> assms(3) assms(4) disct_fct_point_measurable measurable_sets)
         ultimately show ?thesis
           using borel_measurable_indicator_iff borel_measurable_times  by blast
       qed
       moreover have born:  "integral\<^sup>N M (\<lambda>w. ennreal (norm (expl_cond_expect M Y X w * ?indA w))) < \<infinity>"
       proof -
         have "integral\<^sup>N M (\<lambda>w. ennreal (norm (expl_cond_expect M Y X w * ?indA w))) =
            integral\<^sup>N M (\<lambda>w. ennreal (expl_cond_expect M Y X w * ?indA w))"
         proof -
           have "\<forall>w\<in> space M. norm (expl_cond_expect M Y X w * ?indA w) = expl_cond_expect M Y X w * ?indA w"
             using nn_expl_cond_expect_pos by (simp add: nn_expl_cond_expect_pos assms(1))
           thus ?thesis by (metis (no_types, lifting) nn_integral_cong)
         qed
         thus ?thesis
           by (metis (no_types, lifting)
             \<open>(\<Sum>i. \<integral>\<^sup>+ x. ennreal (X x * indpre i x) \<partial>M) = (\<Sum>i. \<integral>\<^sup>+ x. ennreal (expl_cond_expect M Y X x * indpre i x) \<partial>M)\<close>
             \<open>(\<Sum>i. \<integral>\<^sup>+ x. ennreal (expl_cond_expect M Y X x * indpre i x) \<partial>M) = (\<integral>\<^sup>+ x. ennreal (\<Sum>i. expl_cond_expect M Y X x * indpre i x) \<partial>M)\<close>
             \<open>(\<integral>\<^sup>+ w. (\<Sum>i. ennreal (X w * indpre i w)) \<partial>M) = (\<Sum>i. \<integral>\<^sup>+ x. ennreal (X x * indpre i x) \<partial>M)\<close>
             \<open>(\<integral>\<^sup>+ x. ennreal (\<Sum>i. X x * indpre i x) \<partial>M) = (\<integral>\<^sup>+ w. (\<Sum>i. ennreal (X w * indpre i w)) \<partial>M)\<close>
             \<open>(\<integral>\<^sup>+ x. ennreal (\<Sum>i. expl_cond_expect M Y X x * indpre i x) \<partial>M) = (\<integral>\<^sup>+ x. ennreal (expl_cond_expect M Y X x * indicator (Y -` (A \<inter> range Y) \<inter> space M) x) \<partial>M)\<close>
             \<open>ennreal (integral\<^sup>L M (\<lambda>w. \<Sum>i. X w * indpre i w)) = (\<integral>\<^sup>+ x. ennreal (\<Sum>i. X x * indpre i x) \<partial>M)\<close>
             ennreal_less_top infinity_ennreal_def)
         qed
       show "integrable M (\<lambda>w. (expl_cond_expect M Y X w) * ?indA w)"
       proof (rule iffD2[OF integrable_iff_bounded])
         show "((\<lambda>w. expl_cond_expect M Y X w * indicator (Y -` (A \<inter> range Y) \<inter> space M) w) \<in> borel_measurable M) \<and>
          ((\<integral>\<^sup>+ x. (ennreal (norm (expl_cond_expect M Y X x * indicator (Y -` (A \<inter> range Y) \<inter> space M) x))) \<partial>M) < \<infinity>)"
         proof
           show "(\<lambda>w. expl_cond_expect M Y X w * indicator (Y -` (A \<inter> range Y) \<inter> space M) w)\<in> borel_measurable M"
             using rv by simp
           show "(\<integral>\<^sup>+ x. ennreal (norm (expl_cond_expect M Y X x * indicator (Y -` (A \<inter> range Y) \<inter> space M) x)) \<partial>M) < \<infinity>"
             using born by simp
         qed
       qed
     qed
     moreover have "\<forall>w\<in> space M. 0 \<le> (expl_cond_expect M Y X w) * indicator ((Y -`?imA) \<inter> (space M)) w"
       by (simp add: assms(1) nn_expl_cond_expect_pos)
     ultimately show ?thesis using nn_integral_eq_integral
       by (metis (mono_tags, lifting) AE_I2 nn_integral_cong)
   qed
   finally have myeq: "ennreal (integral\<^sup>L M (\<lambda>w. (X w) * ?indA w)) = integral\<^sup>L M (\<lambda>w. (expl_cond_expect M Y X w) * ?indA w)" .

    thus "integrable M (\<lambda>w. expl_cond_expect M Y X w * indicator (Y -` A \<inter> space M) w) \<and> integral\<^sup>L M (\<lambda>w. X w * indicator (Y -` A \<inter> space M) w) =
         integral\<^sup>L M  (\<lambda>w. expl_cond_expect M Y X w * indicator (Y -` A \<inter> space M) w)"
    proof -
      have "0 \<le> integral\<^sup>L M (\<lambda>w. X w * indicator (Y -` A \<inter> space M) w)"
        using \<open>Y -` A = Y -` (A \<inter> range Y)\<close> b sum by fastforce
      moreover have "0 \<le> integral\<^sup>L M (\<lambda>w. expl_cond_expect M Y X w * indicator (Y -` A \<inter> space M) w)"
        by (simp add:  assms(1) nn_expl_cond_expect_pos)
      ultimately have expeq: "integral\<^sup>L M (\<lambda>w. X w * indicator (Y -` A \<inter> space M) w) =
         integral\<^sup>L M  (\<lambda>w. expl_cond_expect M Y X w * indicator (Y -` A \<inter> space M) w)"
        by (metis (mono_tags, lifting) Bochner_Integration.integral_cong \<open>Y -` A = Y -` (A \<inter> range Y)\<close> ennreal_inj myeq)
      have "integrable M (\<lambda>w. (expl_cond_expect M Y X w) * ?indA w)"
       proof -
         have rv: "(\<lambda>w. (expl_cond_expect M Y X w) * indicator ((Y -`?imA) \<inter> (space M)) w) \<in> borel_measurable M"
         proof -
           have "expl_cond_expect M Y X \<in> borel_measurable M" using expl_cond_expect_borel_measurable
             using assms by blast
           moreover have "(Y -`?imA) \<inter> (space M) \<in> sets M"
             by (metis \<open>A \<in> sets M'\<close> \<open>Y -` A = Y -` (A \<inter> range Y)\<close> assms(3) assms(4) disct_fct_point_measurable measurable_sets)
           ultimately show ?thesis
             using borel_measurable_indicator_iff borel_measurable_times  by blast
         qed
         moreover have born:  "integral\<^sup>N M (\<lambda>w. ennreal (norm (expl_cond_expect M Y X w * ?indA w))) < \<infinity>"
         proof -
           have "integral\<^sup>N M (\<lambda>w. ennreal (norm (expl_cond_expect M Y X w * ?indA w))) =
              integral\<^sup>N M (\<lambda>w. ennreal (expl_cond_expect M Y X w * ?indA w))"
           proof -
             have "\<forall>w\<in> space M. norm (expl_cond_expect M Y X w * ?indA w) = expl_cond_expect M Y X w * ?indA w"
               using nn_expl_cond_expect_pos by (simp add: nn_expl_cond_expect_pos assms(1))
             thus ?thesis by (metis (no_types, lifting) nn_integral_cong)
           qed
           thus ?thesis
             by (metis (no_types, lifting)
               \<open>(\<Sum>i. \<integral>\<^sup>+ x. ennreal (X x * indpre i x) \<partial>M) = (\<Sum>i. \<integral>\<^sup>+ x. ennreal (expl_cond_expect M Y X x * indpre i x) \<partial>M)\<close>
               \<open>(\<Sum>i. \<integral>\<^sup>+ x. ennreal (expl_cond_expect M Y X x * indpre i x) \<partial>M) = (\<integral>\<^sup>+ x. ennreal (\<Sum>i. expl_cond_expect M Y X x * indpre i x) \<partial>M)\<close>
               \<open>(\<integral>\<^sup>+ w. (\<Sum>i. ennreal (X w * indpre i w)) \<partial>M) = (\<Sum>i. \<integral>\<^sup>+ x. ennreal (X x * indpre i x) \<partial>M)\<close>
               \<open>(\<integral>\<^sup>+ x. ennreal (\<Sum>i. X x * indpre i x) \<partial>M) = (\<integral>\<^sup>+ w. (\<Sum>i. ennreal (X w * indpre i w)) \<partial>M)\<close>
               \<open>(\<integral>\<^sup>+ x. ennreal (\<Sum>i. expl_cond_expect M Y X x * indpre i x) \<partial>M) = (\<integral>\<^sup>+ x. ennreal (expl_cond_expect M Y X x * indicator (Y -` (A \<inter> range Y) \<inter> space M) x) \<partial>M)\<close>
               \<open>ennreal (integral\<^sup>L M (\<lambda>w. \<Sum>i. X w * indpre i w)) = (\<integral>\<^sup>+ x. ennreal (\<Sum>i. X x * indpre i x) \<partial>M)\<close>
               ennreal_less_top infinity_ennreal_def)
           qed
         show "integrable M (\<lambda>w. (expl_cond_expect M Y X w) * ?indA w)"
         proof (rule iffD2[OF integrable_iff_bounded])
           show "((\<lambda>w. expl_cond_expect M Y X w * indicator (Y -` (A \<inter> range Y) \<inter> space M) w) \<in> borel_measurable M) \<and>
            ((\<integral>\<^sup>+ x. (ennreal (norm (expl_cond_expect M Y X x * indicator (Y -` (A \<inter> range Y) \<inter> space M) x))) \<partial>M) < \<infinity>)"
           proof
             show "(\<lambda>w. expl_cond_expect M Y X w * indicator (Y -` (A \<inter> range Y) \<inter> space M) w)\<in> borel_measurable M"
               using rv by simp
             show "(\<integral>\<^sup>+ x. ennreal (norm (expl_cond_expect M Y X x * indicator (Y -` (A \<inter> range Y) \<inter> space M) x)) \<partial>M) < \<infinity>"
               using born by simp
           qed
         qed
       qed
       hence "integrable M (\<lambda>w. expl_cond_expect M Y X w * indicator (Y -` A \<inter> space M) w)"
         using \<open>Y -` A = Y -` (A \<inter> range Y)\<close> by presburger
      thus ?thesis  using expeq by simp
    qed
  qed



lemma (in finite_measure) nn_expl_cond_exp_integrable:
  assumes "\<forall> w\<in> space M. 0 \<le> X w"
  and "integrable M X"
  and "disc_fct  Y"
  and "point_measurable M (space N) Y"
shows "integrable M (expl_cond_expect M Y X)"
proof -
  have "Y-`space N \<inter> space M = space M"
    by (meson assms(3) assms(4) disct_fct_point_measurable inf_absorb2 measurable_space subsetI vimageI)
  let ?indA = "indicator ((Y -`space N)\<inter> (space M))::'a\<Rightarrow>real"
  have "\<forall>w\<in> space M. (?indA w)= (1::real)" by (simp add: \<open>Y -` space N \<inter> space M = space M\<close>)
  hence "\<forall>w\<in> space M. ((expl_cond_expect M Y X) w) * (?indA w) = (expl_cond_expect M Y X) w" by simp
  moreover have "integrable M (\<lambda>w. ((expl_cond_expect M Y X) w) * (?indA w))" using assms
      nn_cond_expl_is_cond_exp_tmp[of X Y N] by blast
  ultimately show ?thesis by (metis (no_types, lifting) integrable_cong)
qed

lemma (in finite_measure) nn_cond_expl_is_cond_exp:
  assumes "\<forall> w\<in> space M. 0 \<le> X w"
  and "integrable M X"
  and "disc_fct  Y"
  and "point_measurable M (space N) Y"
shows "\<forall> A \<in> sets N. integral\<^sup>L M (\<lambda>w. (X w) * (indicator ((Y -`A)\<inter> (space M)) w)) =
  integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y X) w) * (indicator ((Y -`A) \<inter> (space M))) w)"
  by (metis (mono_tags, lifting) assms nn_cond_expl_is_cond_exp_tmp)

lemma (in finite_measure) expl_cond_exp_integrable:
  assumes "integrable M X"
    and "disc_fct Y"
    and "point_measurable M (space N) Y"
  shows "integrable M (expl_cond_expect M Y X)"
proof -
  let ?zer = "\<lambda>w. 0"
  let ?Xp = "\<lambda>w. max (?zer w) (X w)"
  let ?Xn = "\<lambda>w. max (?zer 0) (-X w)"
  have "\<forall>w. X w = ?Xp w - ?Xn w" by auto
  have ints: "integrable M ?Xp" "integrable M ?Xn" using integrable_max assms by auto
  hence "integrable M (expl_cond_expect M Y ?Xp)" using assms nn_expl_cond_exp_integrable
    by (metis max.cobounded1)
  moreover have "integrable M (expl_cond_expect M Y ?Xn)" using ints assms nn_expl_cond_exp_integrable
    by (metis max.cobounded1)
  ultimately have integr: "integrable M (\<lambda>w. (expl_cond_expect M Y ?Xp) w - (expl_cond_expect M Y ?Xn) w)" by auto
  have "\<forall>w\<in> space M. (expl_cond_expect M Y ?Xp) w - (expl_cond_expect M Y ?Xn) w = (expl_cond_expect M Y X) w"
  proof
    fix w
    assume "w\<in> space M"
    hence "(expl_cond_expect M Y ?Xp) w - (expl_cond_expect M Y ?Xn) w = (expl_cond_expect M Y (\<lambda>x. ?Xp x - ?Xn x)) w"
      using ints by (simp add: expl_cond_exp_diff)
    also have "... = expl_cond_expect M Y X w" using expl_cond_exp_cong \<open>\<forall>w. X w = ?Xp w - ?Xn w\<close> by auto
    finally show "(expl_cond_expect M Y ?Xp) w - (expl_cond_expect M Y ?Xn) w = expl_cond_expect M Y X w" .
  qed
  thus ?thesis using integr
    by (metis (mono_tags, lifting) integrable_cong)
qed


lemma (in finite_measure) is_cond_exp:
  assumes "integrable M X"
  and "disc_fct  Y"
  and "point_measurable M (space N) Y"
shows "\<forall> A \<in> sets N. integral\<^sup>L M (\<lambda>w. (X w) * (indicator ((Y -`A)\<inter> (space M)) w)) =
  integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y X) w) * (indicator ((Y -`A) \<inter> (space M))) w)"
proof -
  let ?zer = "\<lambda>w. 0"
  let ?Xp = "\<lambda>w. max (?zer w) (X w)"
  let ?Xn = "\<lambda>w. max (?zer 0) (-X w)"
  have "\<forall>w. X w = ?Xp w - ?Xn w" by auto
  have ints: "integrable M ?Xp" "integrable M ?Xn" using integrable_max assms by auto
  hence posint: "integrable M (expl_cond_expect M Y ?Xp)" using assms nn_expl_cond_exp_integrable
    by (metis max.cobounded1)
  have negint: "integrable M (expl_cond_expect M Y ?Xn)" using ints assms nn_expl_cond_exp_integrable
    by (metis max.cobounded1)
  have eqp: "\<forall> A \<in> sets N. integral\<^sup>L M (\<lambda>w. (?Xp w) * (indicator ((Y -`A)\<inter> (space M)) w)) =
    integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y ?Xp) w) * (indicator ((Y -`A) \<inter> (space M))) w)"
    using nn_cond_expl_is_cond_exp[of ?Xp Y N] assms  by auto
  have eqn: "\<forall> A \<in> sets N. integral\<^sup>L M (\<lambda>w. (?Xn w) * (indicator ((Y -`A)\<inter> (space M)) w)) =
    integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y ?Xn) w) * (indicator ((Y -`A) \<inter> (space M))) w)"
    using nn_cond_expl_is_cond_exp[of ?Xn Y N] assms  by auto

  show "\<forall> A \<in> sets N. integral\<^sup>L M (\<lambda>w. (X w) * (indicator ((Y -`A)\<inter> (space M)) w)) =
    integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y X) w) * (indicator ((Y -`A) \<inter> (space M))) w)"
  proof
    fix A
    assume "A\<in> sets N"
    let ?imA = "A \<inter> (range Y)"
    have "countable ?imA" using assms disc_fct_def by blast
    have "Y -`A = Y -`?imA" by auto
    have yev: "Y -` (A\<inter> range Y) \<inter> space M \<in> sets M"
        using \<open>A \<in> sets N\<close> assms(3) assms(2) disct_fct_point_measurable measurable_sets
        by (metis \<open>Y -` A = Y -` (A \<inter> range Y)\<close>)
    let ?indA = "indicator ((Y -`(A \<inter> range Y))\<inter> (space M))::'a\<Rightarrow>real"
    have intp: "integrable M (\<lambda>w. (?Xp w) * ?indA w)"
    proof (rule integrable_real_mult_indicator)
      show "Y -` (A\<inter> range Y) \<inter> space M \<in> sets M" using yev by simp
      show "integrable M ?Xp" using assms by simp
    qed
    have intn: "integrable M (\<lambda>w. (?Xn w) * ?indA w)"
    proof (rule integrable_real_mult_indicator)
      show "Y -` (A\<inter> range Y) \<inter> space M \<in> sets M" using yev by simp
      show "integrable M ?Xn" using assms by simp
    qed
    have exintp: "integrable M (\<lambda>w. (expl_cond_expect M Y ?Xp w) * ?indA w)"
    proof (rule integrable_real_mult_indicator)
      show "Y -` (A\<inter> range Y) \<inter> space M \<in> sets M" using yev by simp
      show "integrable M (expl_cond_expect M Y ?Xp)" using posint by simp
    qed
    have exintn: "integrable M (\<lambda>w. (expl_cond_expect M Y ?Xn w) * ?indA w)"
    proof (rule integrable_real_mult_indicator)
      show "Y -` (A\<inter> range Y) \<inter> space M \<in> sets M" using yev by simp
      show "integrable M (expl_cond_expect M Y ?Xn)" using negint by simp
    qed
    have "integral\<^sup>L M (\<lambda>w. X w * indicator (Y -` A \<inter> space M) w) =
      integral\<^sup>L M (\<lambda>w. (?Xp w - ?Xn w) * indicator (Y -` A \<inter> space M) w)"
      using \<open>\<forall>w. X w =?Xp w - ?Xn w\<close> by auto
    also have "... =   integral\<^sup>L M (\<lambda>w. (?Xp w * indicator (Y -` A \<inter> space M) w) - ?Xn w * indicator (Y -` A \<inter> space M) w)"
      by (simp add: left_diff_distrib)
    also have "... = integral\<^sup>L M (\<lambda>w. (?Xp w * indicator (Y -` A \<inter> space M) w)) -
      integral\<^sup>L M (\<lambda>w. ?Xn w * indicator (Y -` A \<inter> space M) w)"
      using \<open>Y -` A = Y -` (A \<inter> range Y)\<close> intp intn by auto
    also have "... = integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y ?Xp) w) * (indicator ((Y -`A) \<inter> (space M))) w) -
      integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y ?Xn) w) * (indicator ((Y -`A) \<inter> (space M))) w)"
      using eqp eqn by (simp add: \<open>A \<in> sets N\<close>)
    also have "... = integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y ?Xp) w) * (indicator ((Y -`A) \<inter> (space M))) w -
      ((expl_cond_expect M Y ?Xn) w) * (indicator ((Y -`A) \<inter> (space M))) w)"
      using \<open>Y -` A = Y -` (A \<inter> range Y)\<close> exintn exintp by auto
    also have "... = integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y ?Xp) w - (expl_cond_expect M Y ?Xn) w) * (indicator ((Y -`A) \<inter> (space M))) w)"
      by (simp add: left_diff_distrib)
    also have "... = integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y (\<lambda>x. ?Xp x - ?Xn x) w) * (indicator ((Y -`A) \<inter> (space M))) w))"
      using expl_cond_exp_diff[of M ?Xp ?Xn Y] ints by (metis (mono_tags, lifting) Bochner_Integration.integral_cong)
    also have "... = integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y X w) * (indicator ((Y -`A) \<inter> (space M))) w))"
      using \<open>\<forall>w. X w = ?Xp w - ?Xn w\<close> expl_cond_exp_cong[of M X "\<lambda>x. ?Xp x - ?Xn x" Y] by presburger
    finally show "integral\<^sup>L M (\<lambda>w. X w * indicator (Y -` A \<inter> space M) w) = integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y X w) * (indicator ((Y -`A) \<inter> (space M))) w))" .
  qed
qed


lemma (in finite_measure) charact_cond_exp:
  assumes "disc_fct Y"
    and "integrable M X"
    and "point_measurable M (space N) Y"
    and "Y \<in> space M \<rightarrow> space N"
    and "\<forall>r\<in> range Y\<inter> space N. \<exists>A\<in> sets N. range Y\<inter> A = {r}"
  shows "AE w in M. real_cond_exp M (fct_gen_subalgebra M N Y) X w = expl_cond_expect M Y X w"
proof (rule sigma_finite_subalgebra.real_cond_exp_charact)
  have "Y\<in> measurable M N"
    by (simp add: assms(1) assms(3) disct_fct_point_measurable)
  have "point_measurable M (space N) Y" by (simp add: assms(3))
  show "sigma_finite_subalgebra M (fct_gen_subalgebra M N Y)" unfolding sigma_finite_subalgebra_def
  proof
    show "subalgebra M (fct_gen_subalgebra M N Y)" using \<open>Y\<in> measurable M N\<close> by (simp add: fct_gen_subalgebra_is_subalgebra)
    show "sigma_finite_measure (restr_to_subalg M (fct_gen_subalgebra M N Y))" unfolding sigma_finite_measure_def
    proof (intro exI conjI)
      let ?A = "{space M}"
      show "countable ?A" by simp
      show "?A \<subseteq> sets (restr_to_subalg M (fct_gen_subalgebra M N Y))"
        by (metis empty_subsetI insert_subset sets.top space_restr_to_subalg)
      show "\<Union> ?A = space (restr_to_subalg M (fct_gen_subalgebra M N Y))"
        by (simp add: space_restr_to_subalg)
      show "\<forall>a\<in>{space M}. emeasure (restr_to_subalg M (fct_gen_subalgebra M N Y)) a \<noteq> \<infinity>"
        by (metis \<open>subalgebra M (fct_gen_subalgebra M N Y)\<close> emeasure_finite emeasure_restr_to_subalg infinity_ennreal_def sets.top singletonD subalgebra_def)
    qed
  qed
  show "integrable M X" using assms by simp
  show "expl_cond_expect M Y X \<in> borel_measurable (fct_gen_subalgebra M N Y)" using assms by (simp add:expl_cond_exp_borel)
  show "integrable M (expl_cond_expect M Y X)"
    using assms expl_cond_exp_integrable  by blast
  have "\<forall>A\<in> sets M. integral\<^sup>L M (\<lambda>w. (X w) * (indicator A w)) = set_lebesgue_integral M A X"
    by (metis (no_types, lifting) Bochner_Integration.integral_cong mult_commute_abs real_scaleR_def set_lebesgue_integral_def)
   have "\<forall>A\<in> sets M. integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y X) w) * (indicator A w)) = set_lebesgue_integral M A (expl_cond_expect M Y X)"
    by (metis (no_types, lifting) Bochner_Integration.integral_cong mult_commute_abs real_scaleR_def set_lebesgue_integral_def)
  have "\<forall>A\<in> sets (fct_gen_subalgebra M N Y). integral\<^sup>L M (\<lambda>w. (X w) * (indicator A w)) =
  integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y X) w) * (indicator A w))"
  proof
    fix A
    assume "A \<in> sets (fct_gen_subalgebra M N Y)"
    hence "A \<in> {Y -` B \<inter> space M |B. B \<in> sets N}" using assms by (simp add:fct_gen_subalgebra_sigma_sets)
    hence "\<exists>B \<in> sets N. A = Y -`B \<inter> space M" by auto
    from this obtain B where "B\<in> sets N" and "A = Y -`B\<inter> space M" by auto
    thus "integral\<^sup>L M (\<lambda>w. (X w) * (indicator A w)) =
      integral\<^sup>L M (\<lambda>w. ((expl_cond_expect M Y X) w) * (indicator A w))" using is_cond_exp
      using Bochner_Integration.integral_cong \<open>point_measurable M (space N) Y\<close> assms(1) assms(2) by blast
  qed
  thus "\<And>A. A \<in> sets (fct_gen_subalgebra M N Y) \<Longrightarrow> set_lebesgue_integral M A X = set_lebesgue_integral M A (expl_cond_expect M Y X)"
    by (smt Bochner_Integration.integral_cong Groups.mult_ac(2) real_scaleR_def set_lebesgue_integral_def)
qed


lemma (in finite_measure) charact_cond_exp':
  assumes "disc_fct Y"
    and "integrable M X"
    and "Y\<in> measurable M N"
    and "\<forall>r\<in> range Y\<inter> space N. \<exists>A\<in> sets N. range Y\<inter> A = {r}"
  shows "AE w in M. real_cond_exp M (fct_gen_subalgebra M N Y) X w = expl_cond_expect M Y X w"
proof (rule charact_cond_exp)
  show "disc_fct Y" using assms by simp
  show "integrable M X" using assms by simp
  show "\<forall>r\<in>range Y \<inter> space N. \<exists>A\<in>sets N. range Y \<inter> A = {r}" using assms by simp
  show "Y\<in> space M \<rightarrow> space N"
    by (meson Pi_I assms(3) measurable_space)
  show "point_measurable M (space N) Y" using assms by (simp add: meas_single_meas)
qed



end
