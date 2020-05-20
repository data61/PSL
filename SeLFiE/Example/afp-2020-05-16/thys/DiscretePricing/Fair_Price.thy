(*  Title:      Fair_Price.thy
    Author:     Mnacho Echenim, Univ. Grenoble Alpes
*)

section \<open>Fair Prices\<close>

text  \<open>This section contains the formalization of financial notions, such as markets, price processes, portfolios,
arbitrages, fair prices, etc. It also defines risk-neutral probability spaces, and proves the main result about the fair
price of a derivative in a risk-neutral probability space, namely that this fair price is equal to the expectation of
the discounted value of the derivative's payoff.\<close>

theory Fair_Price imports Filtration Martingale Geometric_Random_Walk
begin

subsection \<open>Preliminary results\<close>

lemma (in prob_space) finite_borel_measurable_integrable:
  assumes "f\<in> borel_measurable M"
  and "finite (f`(space M))"
  shows "integrable M f"
proof -
  have "simple_function M f" using assms by (simp add: simple_function_borel_measurable)
  moreover have "emeasure M {y \<in> space M. f y \<noteq> 0} \<noteq> \<infinity>" by simp
  ultimately have "Bochner_Integration.simple_bochner_integrable M f"
    using Bochner_Integration.simple_bochner_integrable.simps by blast
  hence "has_bochner_integral M f (Bochner_Integration.simple_bochner_integral M f)"
    using has_bochner_integral_simple_bochner_integrable by auto
  thus ?thesis using integrable.simps by auto
qed


subsubsection \<open>On the almost everywhere filter\<close>

lemma AE_eq_trans[trans]:
  assumes "AE x in M. A x = B x"
  and "AE x in M. B x = C x"
  shows "AE x in M. A x = C x"
  using assms  by auto


abbreviation AEeq where "AEeq M X Y \<equiv> AE w in M. X w = Y w"



lemma AE_add:
  assumes "AE w in M. f w = g w"
  and "AE w in M. f' w = g' w"
shows "AE w in M. f w + f' w = g w + g' w" using assms by auto


lemma AE_sum:
  assumes "finite I"
  and  "\<forall> i\<in>I. AE w in M. f i w = g i w"
  shows "AE w in M. (\<Sum>i\<in> I. f i w) = (\<Sum>i\<in> I. g i w)" using assms(1) subset_refl[of I]
proof (induct rule: finite_subset_induct)
  case empty
  then show ?case by simp
next
  case (insert a F)
  have "AEeq M (f a) (g a)" using assms(2) insert.hyps(2) by auto
  have "AE w in M. (\<Sum>i\<in> insert a F. f i w) = f a w + (\<Sum>i\<in> F. f i w)"
    by (simp add: insert.hyps(1) insert.hyps(3))
  also have "AE w in M. f a w + (\<Sum>i\<in> F. f i w) = g a w + (\<Sum>i\<in> F. f i w)"
    using \<open>AEeq M (f a) (g a)\<close> by auto
  also have "AE w in M. g a w + (\<Sum>i\<in> F. f i w) = g a w + (\<Sum>i\<in> F. g i w)"
    using insert.hyps(4) by auto
  also have "AE w in M. g a w + (\<Sum>i\<in> F. g i w) = (\<Sum>i\<in> insert a F. g i w)"
    by (simp add: insert.hyps(1) insert.hyps(3))
  finally show ?case by auto
qed


lemma AE_eq_cst:
  assumes "AE w in M. (\<lambda>w. c) w = (\<lambda>w. d) w"
  and "emeasure M (space M) \<noteq> 0"
  shows "c = d"
proof (rule ccontr)
  assume "c \<noteq> d"
  from \<open>AE w in M. (\<lambda>w. c) w = (\<lambda>w. d) w\<close> obtain N where Nprops: "{w\<in> space M. \<not>(\<lambda>w. c) w = (\<lambda>w. d) w} \<subseteq> N" "N\<in> sets M" "emeasure M N = 0"
    by (force elim:AE_E)
  have "\<forall>w\<in> space M. (\<lambda>w. c) w \<noteq> (\<lambda>w. d) w" using \<open>c\<noteq> d\<close> by simp
  hence "{w\<in> space M. (\<lambda>w. c) w \<noteq> (\<lambda>w. d) w} = space M" by auto
  hence "space M\<subseteq> N" using Nprops by auto
  thus False using \<open>emeasure M N = 0\<close> assms
    by (meson Nprops(2) \<open>emeasure M (space M) \<noteq> 0\<close> \<open>emeasure M N = 0\<close> \<open>space M \<subseteq> N\<close> emeasure_eq_0)
qed

subsubsection \<open>On conditional expectations\<close>

lemma (in prob_space) subalgebra_sigma_finite:
  assumes "subalgebra M N"
  shows "sigma_finite_subalgebra M N" unfolding sigma_finite_subalgebra_def by (simp add: assms prob_space_axioms prob_space_imp_sigma_finite prob_space_restr_to_subalg)



lemma (in prob_space) trivial_subalg_cond_expect_AE:
  assumes "subalgebra M N"
  and "sets N = {{}, space M}"
  and "integrable M f"
shows "AE x in M. real_cond_exp M N f x = (\<lambda>x. expectation f) x"
proof (intro sigma_finite_subalgebra.real_cond_exp_charact)
  show "sigma_finite_subalgebra M N" by (simp add: assms(1) subalgebra_sigma_finite)
  show "integrable M f" using assms by simp
  show "integrable M (\<lambda>x. expectation f)" by auto
  show "(\<lambda>x. expectation f) \<in> borel_measurable N" by simp
  show "\<And>A. A \<in> sets N \<Longrightarrow> set_lebesgue_integral M A f = \<integral>x\<in>A. expectation f\<partial>M"
  proof -
    fix A
    assume "A \<in> sets N"
    show "set_lebesgue_integral M A f = \<integral>x\<in>A. expectation f\<partial>M"
    proof (cases "A = {}")
      case True
      thus ?thesis by (simp add: set_lebesgue_integral_def)
    next
      case False
      hence "A = space M" using assms \<open>A\<in> sets N\<close> by auto
      have "set_lebesgue_integral M A f = expectation f" using \<open>A = space M\<close>
        by (metis (mono_tags, lifting) Bochner_Integration.integral_cong indicator_simps(1)
                  scaleR_one set_lebesgue_integral_def)
      also have "... =\<integral>x\<in>A. expectation f\<partial>M" using \<open>A = space M\<close>
        by (auto simp add:prob_space set_lebesgue_integral_def)
      finally show ?thesis .
    qed
  qed
qed

lemma (in prob_space) triv_subalg_borel_eq:
  assumes "subalgebra M F"
  and "sets F = {{}, space M}"
  and "AE x in M. f x = (c::'b::{t2_space})"
  and "f\<in> borel_measurable F"
shows "\<forall>x\<in> space M. f x = c"
proof
  fix x
  assume "x\<in> space M"
  have "space M = space F" using assms by (simp add:subalgebra_def)
  hence "x\<in> space F" using \<open>x\<in> space M\<close> by simp
  have "space M \<noteq> {}" by (simp add:not_empty)
  hence "\<exists>d. \<forall>y\<in> space F. f y = d" by (metis assms(1) assms(2) assms(4) subalgebra_def triv_measurable_cst)
  from this obtain d where "\<forall>y \<in>space F. f y = d" by auto
  hence "f x = d" using \<open>x\<in> space F\<close> by simp
  also have "... = c"
  proof (rule ccontr)
    assume "d\<noteq> c"
    from \<open>AE x in M. f x= c\<close> obtain N where Nprops: "{x\<in> space M. \<not>f x = c} \<subseteq> N" "N\<in> sets M" "emeasure M N = 0"
      by (force elim:AE_E)
    have "space M \<subseteq> {x\<in> space M. \<not>f x = c}" using \<open>\<forall>y \<in>space F. f y = d\<close> \<open>space M = space F\<close> \<open>d\<noteq> c\<close> by auto
    hence "space M\<subseteq> N" using Nprops by auto
    thus False using \<open>emeasure M N = 0\<close> emeasure_space_1  Nprops(2) emeasure_mono by fastforce
  qed
  finally show "f x = c" .
qed



lemma (in prob_space) trivial_subalg_cond_expect_eq:
  assumes "subalgebra M N"
  and "sets N = {{}, space M}"
  and "integrable M f"
shows "\<forall>x\<in> space M. real_cond_exp M N f x = expectation f"
proof (rule triv_subalg_borel_eq)
  show "subalgebra M N" "sets N = {{}, space M}" using assms by auto
  show "real_cond_exp M N f \<in> borel_measurable N" by simp
  show "AE x in M. real_cond_exp M N f x = expectation f"
    by (rule trivial_subalg_cond_expect_AE, (auto simp add:assms))
qed



lemma (in sigma_finite_subalgebra) real_cond_exp_cong':
  assumes "\<forall>w \<in> space M. f w = g w"
  and "f\<in> borel_measurable M"
shows "AE w in M. real_cond_exp M F f w = real_cond_exp M F g w"
proof (rule real_cond_exp_cong)
  show "AE w in M. f w = g w" using assms by simp
  show "f\<in> borel_measurable M" using assms by simp
  show "g\<in> borel_measurable M" using assms by (metis measurable_cong)
qed

lemma (in sigma_finite_subalgebra) real_cond_exp_bsum :
  fixes f::"'b \<Rightarrow> 'a \<Rightarrow> real"
  assumes [measurable]: "\<And>i. i\<in>I \<Longrightarrow> integrable M (f i)"
  shows "AE x in M. real_cond_exp M F (\<lambda>x. \<Sum>i\<in>I. f i x) x = (\<Sum>i\<in>I. real_cond_exp M F (f i) x)"
proof (rule real_cond_exp_charact)
  fix A assume [measurable]: "A \<in> sets F"
  then have A_meas [measurable]: "A \<in> sets M" by (meson subsetD subalg subalgebra_def)

  have *: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. indicator A x * f i x)"
    using integrable_mult_indicator[OF \<open>A \<in> sets M\<close> assms(1)]  by auto
  have **: "\<And>i. i \<in> I \<Longrightarrow> integrable M (\<lambda>x. indicator A x * real_cond_exp M F (f i) x)"
    using integrable_mult_indicator[OF \<open>A \<in> sets M\<close> real_cond_exp_int(1)[OF assms(1)]]  by auto
  have inti: "\<And>i. i \<in> I \<Longrightarrow>(\<integral>x. indicator A x * f i x \<partial>M) = (\<integral>x. indicator A x * real_cond_exp M F (f i) x \<partial>M)" using
      real_cond_exp_intg(2)[symmetric,of "indicator A" ]
    using "*" \<open>A \<in> sets F\<close> assms borel_measurable_indicator by blast
  have "(\<integral>x\<in>A. (\<Sum>i\<in>I. f i x)\<partial>M) = (\<integral>x. (\<Sum>i\<in>I. indicator A x * f i x)\<partial>M)"
    by (simp add: sum_distrib_left set_lebesgue_integral_def)
  also have "... = (\<Sum>i\<in>I. (\<integral>x. indicator A x * f i x \<partial>M))" using Bochner_Integration.integral_sum[of I M "\<lambda>i x. indicator A x * f i x"] *
    by simp
  also have "... = (\<Sum>i\<in>I. (\<integral>x. indicator A x * real_cond_exp M F (f i) x \<partial>M))"
    using inti by auto
  also have "... = (\<integral>x. (\<Sum>i\<in>I. indicator A x * real_cond_exp M F (f i) x)\<partial>M)"
    by (rule Bochner_Integration.integral_sum[symmetric], simp add: **)
  also have "... = (\<integral>x\<in>A. (\<Sum>i\<in>I. real_cond_exp M F (f i) x)\<partial>M)"
    by (simp add: sum_distrib_left set_lebesgue_integral_def)
  finally show "(\<integral>x\<in>A. (\<Sum>i\<in>I. f i x)\<partial>M) = (\<integral>x\<in>A. (\<Sum>i\<in>I. real_cond_exp M F (f i) x)\<partial>M)" by auto
qed (auto simp add: assms real_cond_exp_int(1)[OF assms(1)])

subsection \<open>Financial formalizations\<close>

subsubsection \<open>Markets\<close>



definition stk_strict_subs::"'c set \<Rightarrow> bool" where
"stk_strict_subs S \<longleftrightarrow> S \<noteq> UNIV"

typedef ('a,'c) discrete_market = "{(s::('c set), a::'c \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real)). stk_strict_subs s}" unfolding stk_strict_subs_def by fastforce

definition prices where
  "prices Mkt = (snd (Rep_discrete_market Mkt))"

definition assets where

  "assets Mkt = UNIV"


definition stocks where
  "stocks Mkt = (fst (Rep_discrete_market Mkt))"

definition discrete_market_of
where
  "discrete_market_of S A =
    Abs_discrete_market (if (stk_strict_subs S) then S else {}, A)"

lemma prices_of:
  shows "prices (discrete_market_of S A) = A"
proof -
  have "stk_strict_subs (if (stk_strict_subs S) then S else {})"
  proof (cases "stk_strict_subs S")
    case True thus ?thesis by simp
  next
    case False thus ?thesis unfolding stk_strict_subs_def by simp
  qed
  hence fct: "((if (stk_strict_subs S) then S else {}), A) \<in> {(s, a). stk_strict_subs s}" by simp
  have "discrete_market_of S A = Abs_discrete_market (if (stk_strict_subs S) then S else {}, A)" unfolding discrete_market_of_def by simp
  hence "Rep_discrete_market (discrete_market_of S A) = (if (stk_strict_subs S) then S else {},A)"
    using Abs_discrete_market_inverse[of "(if (stk_strict_subs S) then S else {}, A)"] fct  by simp
  thus ?thesis unfolding prices_def by simp
qed

lemma stocks_of:
  assumes "UNIV \<noteq> S"
  shows "stocks (discrete_market_of S A) = S"
proof -
  have "stk_strict_subs S" using assms unfolding stk_strict_subs_def by simp
  hence fct: "((if (stk_strict_subs S) then S else {}), A) \<in> {(s, a). stk_strict_subs s}" by simp
  have "discrete_market_of S A = Abs_discrete_market (if (stk_strict_subs S) then S else {}, A)" unfolding discrete_market_of_def by simp
  hence "Rep_discrete_market (discrete_market_of S A) = (if (stk_strict_subs S) then S else {},A)"
    using Abs_discrete_market_inverse[of "(if (stk_strict_subs S) then S else {}, A)"] fct  by simp
  thus ?thesis unfolding stocks_def using \<open>stk_strict_subs S\<close> by simp
qed

lemma mkt_stocks_assets:
  shows "stk_strict_subs (stocks Mkt)" unfolding stocks_def prices_def
  by (metis Rep_discrete_market mem_Collect_eq split_beta')

subsubsection \<open>Quantity processes and portfolios\<close>
text \<open>These are functions that assign quantities to assets; each quantity is a stochastic process. Basic
operations are defined on these processes.\<close>

paragraph \<open>Basic operations\<close>

definition qty_empty where
  "qty_empty = (\<lambda> (x::'a) (n::nat) w. 0::real)"

definition qty_single where
  "qty_single asset qt_proc = (qty_empty(asset := qt_proc))"

definition qty_sum::"('b \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('b \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('b \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real)"  where
  "qty_sum pf1 pf2 = (\<lambda>x n w. pf1 x n w + pf2 x n w)"

definition qty_mult_comp::"('b \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> ('b \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real)"  where
  "qty_mult_comp pf1 qty = (\<lambda>x n w. (pf1 x n w) * (qty n w))"

definition qty_rem_comp::"('b \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'b \<Rightarrow> ('b \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real)"  where
  "qty_rem_comp pf1 x = pf1(x:=(\<lambda>n w. 0))"

definition qty_replace_comp where
  "qty_replace_comp pf1 x pf2 = qty_sum (qty_rem_comp pf1 x) (qty_mult_comp pf2 (pf1 x))"


paragraph \<open>Support sets\<close>

text \<open>If p x n w is different from 0, this means that this quantity is held on interval ]n-1, n].\<close>
definition support_set::"('b \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'b set" where
  "support_set p = {x. \<exists> n w. p x n w \<noteq> 0}"

lemma qty_empty_support_set:
  shows "support_set qty_empty = {}" unfolding support_set_def qty_empty_def by simp							
lemma sum_support_set:
  shows "support_set (qty_sum pf1 pf2) \<subseteq> (support_set pf1) \<union> (support_set pf2)"
proof (intro subsetI, rule ccontr)
  fix x
  assume "x\<in> support_set (qty_sum pf1 pf2)" and "x \<notin> support_set pf1 \<union> support_set pf2" note xprops = this
  hence "\<exists> n w. (qty_sum pf1 pf2) x n w \<noteq> 0" by (simp add: support_set_def)
  from this obtain n w where "(qty_sum pf1 pf2) x n w \<noteq> 0" by auto note nwprops = this
  have "pf1 x n w = 0" "pf2 x n w = 0" using xprops by (auto simp add:support_set_def)
  hence "(qty_sum pf1 pf2) x n w = 0" unfolding qty_sum_def by simp
  thus False using nwprops by simp
qed

lemma mult_comp_support_set:
shows "support_set (qty_mult_comp pf1 qty) \<subseteq> (support_set pf1)"
proof (intro subsetI, rule ccontr)
  fix x
  assume "x\<in> support_set (qty_mult_comp pf1 qty)" and "x \<notin> support_set pf1" note xprops = this
  hence "\<exists> n w. (qty_mult_comp pf1 qty) x n w \<noteq> 0" by (simp add: support_set_def)
  from this obtain n w where "qty_mult_comp pf1 qty x n w \<noteq> 0" by auto note nwprops = this
  have "pf1 x n w = 0" using xprops by (simp add:support_set_def)
  hence "(qty_mult_comp pf1 qty) x n w = 0" unfolding qty_mult_comp_def by simp
  thus False using nwprops by simp
qed

lemma remove_comp_support_set:
shows "support_set (qty_rem_comp pf1 x) \<subseteq> ((support_set pf1) - {x})"
proof (intro subsetI, rule ccontr)
  fix y
  assume "y\<in> support_set (qty_rem_comp pf1 x)" and "y \<notin> support_set pf1 - {x}" note xprops = this
  hence "y\<notin> support_set pf1 \<or> y = x" by simp
  have "\<exists> n w. (qty_rem_comp pf1 x) y n w \<noteq> 0" using xprops by (simp add: support_set_def)
  from this obtain n w where "(qty_rem_comp pf1 x) y n w \<noteq> 0" by auto note nwprops = this
  show False
  proof (cases "y\<notin> support_set pf1")
    case True
    hence "pf1 y n w = 0" using xprops by (simp add:support_set_def)
    hence "(qty_rem_comp pf1 x) x n w = 0" unfolding qty_rem_comp_def by simp
    thus ?thesis using nwprops by (metis \<open>pf1 y n w = 0\<close> fun_upd_apply qty_rem_comp_def)
  next
    case False
    hence "y = x" using \<open>y\<notin> support_set pf1 \<or> y = x\<close> by simp
    hence "(qty_rem_comp pf1 x) x n w = 0" unfolding qty_rem_comp_def by simp
    thus ?thesis using nwprops by (simp add: \<open>y = x\<close>)
  qed
qed

lemma replace_comp_support_set:
  shows "support_set (qty_replace_comp pf1 x pf2) \<subseteq> (support_set pf1 - {x}) \<union> support_set pf2"
proof -
  have "support_set (qty_replace_comp pf1 x pf2) \<subseteq> support_set (qty_rem_comp pf1 x) \<union> support_set (qty_mult_comp pf2 (pf1 x))"
    unfolding qty_replace_comp_def by (simp add:sum_support_set)
  also have "... \<subseteq> (support_set pf1 - {x}) \<union> support_set pf2" using remove_comp_support_set mult_comp_support_set
    by (metis sup.mono)
  finally show ?thesis .
qed

lemma single_comp_support:
  shows "support_set (qty_single asset qty) \<subseteq> {asset}"
proof
  fix x
  assume "x\<in> support_set (qty_single asset qty)"
  show "x\<in> {asset}"
  proof (rule ccontr)
    assume "x\<notin> {asset}"
    hence "x\<noteq> asset" by auto
    have "\<exists> n w. qty_single asset qty x n w \<noteq> 0" using \<open>x\<in> support_set (qty_single asset qty)\<close>
      by (simp add:support_set_def)
    from this obtain n w where "qty_single asset qty x n w \<noteq> 0" by auto
    thus False using \<open>x\<noteq>asset\<close> by (simp add: qty_single_def qty_empty_def)
  qed
qed

lemma single_comp_nz_support:
  assumes "\<exists> n w. qty n w\<noteq> 0"
  shows "support_set (qty_single asset qty) = {asset}"
proof
  show "support_set (qty_single asset qty) \<subseteq> {asset}" by (simp add: single_comp_support)
  have "asset\<in> support_set (qty_single asset qty)" using assms unfolding support_set_def qty_single_def by simp
  thus "{asset} \<subseteq> support_set (qty_single asset qty)" by auto
qed

paragraph \<open>Portfolios\<close>

definition portfolio where
  "portfolio p \<longleftrightarrow> finite (support_set p)"




definition stock_portfolio :: "('a, 'b) discrete_market \<Rightarrow> ('b \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "stock_portfolio Mkt p \<longleftrightarrow> portfolio p \<and> support_set p \<subseteq> stocks Mkt"

lemma sum_portfolio:
  assumes "portfolio pf1"
  and "portfolio pf2"
shows "portfolio (qty_sum pf1 pf2)" unfolding portfolio_def
proof -
  have "support_set (qty_sum pf1 pf2) \<subseteq> (support_set pf1) \<union> (support_set pf2)"  by (simp add: sum_support_set)
  thus "finite (support_set (qty_sum pf1 pf2))" using assms unfolding portfolio_def using infinite_super by auto
qed

lemma sum_basic_support_set:
  assumes "stock_portfolio Mkt pf1"
  and "stock_portfolio Mkt pf2"
shows "stock_portfolio Mkt (qty_sum pf1 pf2)" using assms sum_support_set[of pf1 pf2] unfolding stock_portfolio_def
  by (metis Diff_subset_conv gfp.leq_trans subset_Un_eq sum_portfolio)

lemma mult_comp_portfolio:
  assumes "portfolio pf1"
shows "portfolio (qty_mult_comp pf1 qty)" unfolding portfolio_def
proof -
  have "support_set (qty_mult_comp pf1 qty) \<subseteq> (support_set pf1)"  by (simp add: mult_comp_support_set)
  thus "finite (support_set (qty_mult_comp pf1 qty))" using assms unfolding portfolio_def using infinite_super by auto
qed

lemma mult_comp_basic_support_set:
  assumes "stock_portfolio Mkt pf1"
shows "stock_portfolio Mkt (qty_mult_comp pf1 qty)" using assms mult_comp_support_set[of pf1] unfolding stock_portfolio_def
  using mult_comp_portfolio by blast



lemma remove_comp_portfolio:
  assumes "portfolio pf1"
shows "portfolio (qty_rem_comp pf1 x)" unfolding portfolio_def
proof -
  have "support_set (qty_rem_comp pf1 x) \<subseteq> (support_set pf1)" using remove_comp_support_set[of pf1 x] by blast
  thus "finite (support_set (qty_rem_comp pf1 x))" using assms unfolding portfolio_def using infinite_super by auto
qed

lemma remove_comp_basic_support_set:
  assumes "stock_portfolio Mkt pf1"
shows "stock_portfolio Mkt (qty_mult_comp pf1 qty)" using assms mult_comp_support_set[of pf1] unfolding stock_portfolio_def
  using mult_comp_portfolio by blast

lemma replace_comp_portfolio:
  assumes "portfolio pf1"
  and "portfolio pf2"
shows "portfolio (qty_replace_comp pf1 x pf2)" unfolding portfolio_def
proof -
  have "support_set (qty_replace_comp pf1 x pf2) \<subseteq> (support_set pf1) \<union> (support_set pf2)" using replace_comp_support_set[of pf1 x pf2] by blast
  thus "finite (support_set (qty_replace_comp pf1 x pf2))" using assms unfolding portfolio_def using infinite_super by auto
qed

lemma replace_comp_stocks:
  assumes "support_set pf1 \<subseteq> stocks Mkt \<union> {x}"
  and "support_set pf2 \<subseteq> stocks Mkt"
shows "support_set (qty_replace_comp pf1 x pf2) \<subseteq> stocks Mkt"
proof -
  have "support_set (qty_rem_comp pf1 x) \<subseteq> stocks Mkt" using assms(1) remove_comp_support_set by fastforce
  moreover have "support_set (qty_mult_comp pf2 (pf1 x)) \<subseteq> stocks Mkt" using assms mult_comp_support_set by fastforce
  ultimately show ?thesis unfolding qty_replace_comp_def using sum_support_set by fastforce
qed



lemma single_comp_portfolio:
  shows "portfolio (qty_single asset qty)"
  by (meson finite.emptyI finite.insertI finite_subset portfolio_def single_comp_support)

paragraph \<open>Value processes\<close>

definition val_process where
  "val_process Mkt p = (if (\<not> (portfolio p)) then (\<lambda> n w. 0)
    else (\<lambda> n w . (sum (\<lambda>x. ((prices Mkt) x n w) * (p x (Suc n) w)) (support_set p))))"



lemma subset_val_process':
  assumes "finite A"
  and "support_set p \<subseteq> A"
shows "val_process Mkt p n w = (sum (\<lambda>x. ((prices Mkt) x n w) * (p x (Suc n) w)) A)"
proof -
  have "portfolio p" using assms unfolding portfolio_def using finite_subset by auto
  have "\<exists>C. (support_set p) \<inter> C = {} \<and> (support_set p) \<union> C = A" using assms(2) by auto
  from this obtain C where "(support_set p) \<inter> C = {}" and "(support_set p) \<union> C = A" by auto note Cprops = this
  have "finite C" using assms \<open>(support_set p) \<union> C = A\<close> by auto
  have "\<forall>x\<in> C. p x (Suc n) w = 0" using Cprops(1) support_set_def by fastforce
  hence "(\<Sum>x\<in> C. ((prices Mkt) x n w) * (p x (Suc n) w)) = 0" by simp
  hence "val_process Mkt p n w = (\<Sum>x\<in> (support_set p). ((prices Mkt) x n w) * (p x (Suc n) w))
    + (\<Sum>x\<in> C. ((prices Mkt) x n w) * (p x (Suc n) w))" unfolding val_process_def using \<open>portfolio p\<close> by simp
  also have "... = (\<Sum> x\<in> A. ((prices Mkt) x n w) * (p x (Suc n) w))"
    using \<open>portfolio p\<close> \<open>finite C\<close> Cprops portfolio_def sum_union_disjoint' by (metis (no_types, lifting))
  finally show "val_process Mkt p n w = (\<Sum> x\<in> A. ((prices Mkt) x n w) * (p x (Suc n) w))" .
qed


lemma sum_val_process:
  assumes "portfolio pf1"
  and "portfolio pf2"
shows "\<forall>n w. val_process Mkt (qty_sum pf1 pf2) n w = (val_process Mkt pf1) n w + (val_process Mkt pf2) n w"
proof (intro allI)
  fix n w
  have vp1: "val_process Mkt pf1 n w = (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2). ((prices Mkt) x n w) * (pf1 x (Suc n) w))"
  proof -
    have "finite (support_set pf1 \<union> support_set pf2) \<and> support_set pf1 \<subseteq> support_set pf1 \<union> support_set pf2"
      by (meson assms(1) assms(2) finite_Un portfolio_def sup.cobounded1)
    then show ?thesis
      by (simp add: subset_val_process')
  qed
  have vp2: "val_process Mkt pf2 n w = (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2). ((prices Mkt) x n w) * (pf2 x (Suc n) w))"
  proof -
    have "finite (support_set pf1 \<union> support_set pf2) \<and> support_set pf2 \<subseteq> support_set pf2 \<union> support_set pf1"
      by (meson assms(1) assms(2) finite_Un portfolio_def sup.cobounded1)
    then show ?thesis
      by (simp add: subset_val_process')
  qed
  have pf:"portfolio (qty_sum pf1 pf2)" using assms by (simp add:sum_portfolio)
  have fin:"finite (support_set pf1 \<union> support_set pf2)" using assms finite_Un unfolding portfolio_def by auto
  have "(val_process Mkt pf1) n w + (val_process Mkt pf2) n w =
    (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2). ((prices Mkt) x n w) * (pf1 x (Suc n) w)) +
    (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2). ((prices Mkt) x n w) * (pf2 x (Suc n) w))"
    using vp1 vp2 by simp
  also have "... = (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2).
    (((prices Mkt) x n w) * (pf1 x (Suc n) w)) + ((prices Mkt) x n w) * (pf2 x (Suc n) w))"
    by (simp add: sum.distrib)
  also have "... = (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2).
    ((prices Mkt) x n w) * ((pf1 x (Suc n) w) + (pf2 x (Suc n) w)))" by (simp add: distrib_left)
  also have "... = (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2).
    ((prices Mkt) x n w) * ((qty_sum pf1 pf2) x (Suc n) w))" by (simp add: qty_sum_def)
  also have "... = (\<Sum> x\<in> (support_set (qty_sum pf1 pf2)).
    ((prices Mkt) x n w) * ((qty_sum pf1 pf2) x (Suc n) w))" using sum_support_set[of pf1 pf2]
    subset_val_process'[of "support_set pf1\<union> support_set pf2" "qty_sum pf1 pf2"] pf fin unfolding val_process_def by simp
  also have "... = val_process Mkt (qty_sum pf1 pf2) n w" by (metis (no_types, lifting) pf sum.cong val_process_def)
  finally have "(val_process Mkt pf1) n w + (val_process Mkt pf2) n w = val_process Mkt (qty_sum pf1 pf2) n w" .
  thus "val_process Mkt (qty_sum pf1 pf2) n w = (val_process Mkt pf1) n w + (val_process Mkt pf2) n w" ..
qed


lemma mult_comp_val_process:
  assumes "portfolio pf1"
shows "\<forall>n w. val_process Mkt (qty_mult_comp pf1 qty) n w = ((val_process Mkt pf1) n w) * (qty (Suc n) w)"
proof (intro allI)
  fix n w
  have pf:"portfolio (qty_mult_comp pf1 qty)" using assms by (simp add:mult_comp_portfolio)
  have fin:"finite (support_set pf1)" using assms unfolding portfolio_def by auto
  have "((val_process Mkt pf1) n w) * (qty (Suc n) w) =
    (\<Sum> x\<in> (support_set pf1). ((prices Mkt) x n w) * (pf1 x (Suc n) w))*(qty (Suc n) w)"
    unfolding val_process_def using assms by simp
  also have "... = (\<Sum> x\<in> (support_set pf1).
    (((prices Mkt) x n w) * (pf1 x (Suc n) w) * (qty (Suc n) w)))" using sum_distrib_right by auto
  also have "... = (\<Sum> x\<in> (support_set pf1).
    ((prices Mkt) x n w) * ((qty_mult_comp pf1 qty) x (Suc n) w))" unfolding qty_mult_comp_def
    by (simp add: mult.commute mult.left_commute)
  also have "... = (\<Sum> x\<in> (support_set (qty_mult_comp pf1 qty)).
    ((prices Mkt) x n w) * ((qty_mult_comp pf1 qty) x (Suc n) w))" using mult_comp_support_set[of pf1]
    subset_val_process'[of "support_set pf1" "qty_mult_comp pf1 qty"] pf fin unfolding val_process_def by simp
  also have "... = val_process Mkt (qty_mult_comp pf1 qty) n w" by (metis (no_types, lifting) pf sum.cong val_process_def)
  finally have "(val_process Mkt pf1) n w * (qty (Suc n) w) = val_process Mkt (qty_mult_comp pf1 qty) n w" .
  thus "val_process Mkt (qty_mult_comp pf1 qty) n w = (val_process Mkt pf1) n w * (qty (Suc n) w)" ..
qed





lemma remove_comp_values:
  assumes "x \<noteq> y"
  shows "\<forall>n w. pf1 x n w = (qty_rem_comp pf1 y) x n w"
proof (intro allI)
  fix n w
  show "pf1 x n w = (qty_rem_comp pf1 y) x n w" by (simp add: assms qty_rem_comp_def)
qed




lemma remove_comp_val_process:
  assumes "portfolio pf1"
shows "\<forall>n w. val_process Mkt (qty_rem_comp pf1 y) n w = ((val_process Mkt pf1) n w) - (prices Mkt y n w)* (pf1 y (Suc n) w)"
proof (intro allI)
  fix n w
  have pf:"portfolio (qty_rem_comp pf1 y)" using assms by (simp add:remove_comp_portfolio)
  have fin:"finite (support_set pf1)" using assms unfolding portfolio_def by auto
  hence fin2: "finite (support_set pf1 - {y})" by simp
  have "((val_process Mkt pf1) n w)  =
    (\<Sum> x\<in> (support_set pf1). ((prices Mkt) x n w) * (pf1 x (Suc n) w))"
    unfolding val_process_def using assms by simp
  also have "... = (\<Sum> x\<in> (support_set pf1 - {y}).
    (((prices Mkt) x n w) * (pf1 x (Suc n) w))) + (prices Mkt y n w)* (pf1 y (Suc n) w)"
  proof (cases "y\<in> support_set pf1")
    case True
    thus ?thesis by (simp add: fin sum_diff1)
  next
    case False
    hence "pf1 y (Suc n) w = 0" unfolding support_set_def by simp
    thus ?thesis by (simp add: fin sum_diff1)
  qed
  also have "... = (\<Sum> x\<in> (support_set pf1 - {y}).
    ((prices Mkt) x n w) * ((qty_rem_comp pf1 y) x (Suc n) w)) + (prices Mkt y n w)* (pf1 y (Suc n) w)"
  proof -
    have "(\<Sum> x\<in> (support_set pf1 - {y}). (((prices Mkt) x n w) * (pf1 x (Suc n) w))) =
      (\<Sum> x\<in> (support_set pf1 - {y}). ((prices Mkt) x n w) * ((qty_rem_comp pf1 y) x (Suc n) w))"
    proof (rule sum.cong,simp)
      fix x
      assume "x\<in> support_set pf1 - {y}"
      show "prices Mkt x n w * pf1 x (Suc n) w = prices Mkt x n w * qty_rem_comp pf1 y x (Suc n) w" using remove_comp_values
        by (metis DiffD2 \<open>x \<in> support_set pf1 - {y}\<close> singletonI)
    qed
    thus ?thesis by simp
  qed
  also have "... = (val_process Mkt (qty_rem_comp pf1 y) n w) + (prices Mkt y n w)* (pf1 y (Suc n) w)"
    using subset_val_process'[of "support_set pf1 - {y}" "qty_rem_comp pf1 y"] fin2
    by (simp add: remove_comp_support_set)
  finally have "(val_process Mkt pf1) n w =
    (val_process Mkt (qty_rem_comp pf1 y) n w) + (prices Mkt y n w)* (pf1 y (Suc n) w)" .
  thus  "val_process Mkt (qty_rem_comp pf1 y) n w = ((val_process Mkt pf1) n w) - (prices Mkt y n w)* (pf1 y (Suc n) w)" by simp
qed




lemma replace_comp_val_process:
  assumes "\<forall>n w. prices Mkt x n w = val_process Mkt pf2 n w"
  and "portfolio pf1"
  and "portfolio pf2"
  shows "\<forall>n w. val_process Mkt (qty_replace_comp pf1 x pf2) n w = val_process Mkt pf1 n w"
proof (intro allI)
  fix n w
  have "val_process Mkt (qty_replace_comp pf1 x pf2) n w = val_process Mkt (qty_rem_comp pf1 x) n w +
    val_process Mkt (qty_mult_comp pf2 (pf1 x)) n w" unfolding qty_replace_comp_def using assms
    sum_val_process[of "qty_rem_comp pf1 x" "qty_mult_comp pf2 (pf1 x)"]
    by (simp add: mult_comp_portfolio remove_comp_portfolio)
  also have "... = val_process Mkt pf1 n w - (prices Mkt x n w * pf1 x (Suc n) w) + val_process Mkt pf2 n w * pf1 x (Suc n) w"
    by (simp add: assms(2) assms(3) mult_comp_val_process remove_comp_val_process)
  also have "... = val_process Mkt pf1 n w" using assms by simp
  finally show "val_process Mkt (qty_replace_comp pf1 x pf2) n w = val_process Mkt pf1 n w" .
qed

lemma qty_single_val_process:
shows "val_process Mkt (qty_single asset qty) n w =
    prices Mkt asset n w * qty (Suc n) w"
proof -
  have "val_process Mkt (qty_single asset qty) n w =
    (sum (\<lambda>x. ((prices Mkt) x n w) * ((qty_single asset qty) x (Suc n) w)) {asset})"
  proof (rule subset_val_process')
    show "finite {asset}" by simp
    show "support_set (qty_single asset qty) \<subseteq> {asset}" by (simp add: single_comp_support)
  qed
  also have "... = prices Mkt asset n w * qty (Suc n) w" unfolding qty_single_def by simp
  finally show ?thesis .
qed



subsubsection \<open>Trading strategies\<close>





locale disc_equity_market = triv_init_disc_filtr_prob_space +
  fixes Mkt::"('a,'b) discrete_market"


paragraph \<open>Discrete predictable processes\<close>



paragraph \<open>Trading strategy\<close>

definition (in disc_filtr_prob_space) trading_strategy
where
  "trading_strategy p \<longleftrightarrow> portfolio p \<and> (\<forall>asset \<in> support_set p. borel_predict_stoch_proc F (p asset))"

definition (in disc_filtr_prob_space) support_adapt:: "('a, 'b) discrete_market \<Rightarrow> ('b \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "support_adapt Mkt pf \<longleftrightarrow> (\<forall> asset \<in> support_set pf. borel_adapt_stoch_proc F (prices Mkt asset))"

lemma (in disc_filtr_prob_space) quantity_adapted:
  assumes "\<forall> asset \<in> support_set p. p asset (Suc n) \<in> borel_measurable (F n)"
  "\<forall>asset \<in> support_set p. prices Mkt asset n \<in> borel_measurable (F n)"
shows "val_process Mkt p n \<in> borel_measurable (F n)"
proof (cases "portfolio p")
case False
  have "val_process Mkt p = (\<lambda> n w. 0)" unfolding val_process_def using False by simp
  thus "?thesis" by simp
next
  case True
  hence "val_process Mkt p n = (\<lambda>w. \<Sum>x\<in>support_set p. prices Mkt x n w * p x (Suc n) w)"
    unfolding val_process_def using True by simp
  moreover have "(\<lambda>w. \<Sum>x\<in>support_set p. prices Mkt x n w * p x (Suc n) w) \<in> borel_measurable (F n)"
  proof (rule borel_measurable_sum)
    fix asset
    assume "asset\<in> support_set p"
    hence "p asset (Suc n) \<in> borel_measurable (F n)" using assms unfolding trading_strategy_def adapt_stoch_proc_def by simp
    moreover have "prices Mkt asset n \<in> borel_measurable (F n)"
      using \<open>asset \<in> support_set p\<close>  assms(2) unfolding support_adapt_def by (simp add: adapt_stoch_proc_def)
    ultimately show "(\<lambda>x. prices Mkt asset n x * p asset (Suc n) x) \<in> borel_measurable (F n)" by simp
  qed
  ultimately show "val_process Mkt p n \<in> borel_measurable (F n)" by simp
qed



lemma (in disc_filtr_prob_space) trading_strategy_adapted:
  assumes "trading_strategy p"
  and "support_adapt Mkt p"
  shows "borel_adapt_stoch_proc F (val_process Mkt p)" unfolding support_adapt_def
proof (cases "portfolio p")
case False
  have "val_process Mkt p = (\<lambda> n w. 0)" unfolding val_process_def using False by simp
  thus "borel_adapt_stoch_proc F (val_process Mkt p)"
    by (simp add: constant_process_borel_adapted)
next
case True
  show ?thesis unfolding adapt_stoch_proc_def
  proof
    fix n
    have "val_process Mkt p n = (\<lambda>w. \<Sum>x\<in>support_set p. prices Mkt x n w * p x (Suc n) w)"
      unfolding val_process_def using True by simp
    moreover have "(\<lambda>w. \<Sum>x\<in>support_set p. prices Mkt x n w * p x (Suc n) w) \<in> borel_measurable (F n)"
    proof (rule borel_measurable_sum)
      fix asset
      assume "asset\<in> support_set p"
      hence "p asset (Suc n) \<in> borel_measurable (F n)" using assms unfolding trading_strategy_def predict_stoch_proc_def by simp
      moreover have "prices Mkt asset n \<in> borel_measurable (F n)"
        using \<open>asset \<in> support_set p\<close>  assms(2) unfolding support_adapt_def  by (simp add:adapt_stoch_proc_def)
      ultimately show "(\<lambda>x. prices Mkt asset n x * p asset (Suc n) x) \<in> borel_measurable (F n)" by simp
    qed
    ultimately show "val_process Mkt p n \<in> borel_measurable (F n)" by simp
  qed
qed




lemma (in disc_equity_market) ats_val_process_adapted:
  assumes "trading_strategy p"
and "support_adapt Mkt p"
  shows "borel_adapt_stoch_proc F (val_process Mkt p)" unfolding support_adapt_def
  by (meson assms(1) assms(2)  subsetCE trading_strategy_adapted)



lemma (in disc_equity_market) trading_strategy_init:
  assumes "trading_strategy p"
and "support_adapt Mkt p"
  shows "\<exists>c. \<forall>w \<in> space M. val_process Mkt p 0 w = c" using assms adapted_init ats_val_process_adapted by simp


definition (in disc_equity_market) initial_value where
  "initial_value pf = constant_image (val_process Mkt pf 0)"

lemma (in disc_equity_market) initial_valueI:
  assumes "trading_strategy pf"
and "support_adapt Mkt pf"
  shows "\<forall>w\<in> space M. val_process Mkt pf 0 w = initial_value pf" unfolding initial_value_def
proof (rule constant_imageI)
  show "\<exists>c. \<forall>w\<in>space M. val_process Mkt pf 0 w = c" using trading_strategy_init assms by simp
qed


lemma (in disc_equity_market) inc_predict_support_trading_strat:
  assumes "trading_strategy pf1"
  shows "\<forall> asset \<in> support_set pf1 \<union> B. borel_predict_stoch_proc F (pf1 asset)"
proof
  fix asset
  assume "asset \<in> support_set pf1 \<union> B"
  show "borel_predict_stoch_proc F (pf1 asset)"
  proof (cases "asset \<in> support_set pf1")
    case True
    thus ?thesis using assms unfolding trading_strategy_def by simp
  next
    case False
    hence "\<forall>n w. pf1 asset n w = 0" unfolding support_set_def by simp
    show ?thesis unfolding predict_stoch_proc_def
    proof
      show "pf1 asset 0 \<in> measurable (F 0) borel" using \<open>\<forall>n w. pf1 asset n w = 0\<close>
        by (simp add: borel_measurable_const measurable_cong)
    next
      show "\<forall>n. pf1 asset (Suc n) \<in> borel_measurable (F n)"
      proof
        fix n
        have "\<forall>w. pf1 asset (Suc n) w = 0" using \<open>\<forall>n w. pf1 asset n w = 0\<close> by simp
        have "0\<in> space borel" by simp
        thus "pf1 asset (Suc n) \<in> measurable (F n) borel" using measurable_const[of 0 borel "F n"]
          by (metis \<open>0 \<in> space borel \<Longrightarrow> (\<lambda>x. 0) \<in> borel_measurable (F n)\<close> \<open>0 \<in> space borel\<close>
              \<open>\<forall>n w. pf1 asset n w = 0\<close> measurable_cong)
      qed
    qed
  qed
qed

lemma (in disc_equity_market) inc_predict_support_trading_strat':
  assumes "trading_strategy pf1"
  and "asset \<in> support_set pf1\<union> B"
  shows "borel_predict_stoch_proc F (pf1 asset)"
proof (cases "asset \<in> support_set pf1")
  case True
  thus ?thesis using assms unfolding trading_strategy_def by simp
next
  case False
  hence "\<forall>n w. pf1 asset n w = 0" unfolding support_set_def by simp
  show ?thesis unfolding predict_stoch_proc_def
  proof
    show "pf1 asset 0 \<in> measurable (F 0) borel" using \<open>\<forall>n w. pf1 asset n w = 0\<close>
      by (simp add: borel_measurable_const measurable_cong)
  next
    show "\<forall>n. pf1 asset (Suc n) \<in> borel_measurable (F n)"
    proof
      fix n
      have "\<forall>w. pf1 asset (Suc n) w = 0" using \<open>\<forall>n w. pf1 asset n w = 0\<close> by simp
      have "0\<in> space borel" by simp
      thus "pf1 asset (Suc n) \<in> measurable (F n) borel" using measurable_const[of 0 borel "F n"]
        by (metis \<open>0 \<in> space borel \<Longrightarrow> (\<lambda>x. 0) \<in> borel_measurable (F n)\<close> \<open>0 \<in> space borel\<close>
            \<open>\<forall>n w. pf1 asset n w = 0\<close> measurable_cong)
    qed
  qed
qed



lemma (in disc_equity_market) inc_support_trading_strat:
  assumes "trading_strategy pf1"
  shows "\<forall> asset \<in> support_set pf1 \<union> B. borel_adapt_stoch_proc F (pf1 asset)" using assms
  by (simp add: inc_predict_support_trading_strat predict_imp_adapt)

lemma (in disc_equity_market) qty_empty_trading_strat:
  shows "trading_strategy qty_empty" unfolding trading_strategy_def 
proof (intro conjI ballI)
  show "portfolio qty_empty"
    by (metis fun_upd_triv qty_single_def single_comp_portfolio) 
  show "\<And>asset. asset \<in> support_set qty_empty \<Longrightarrow> borel_predict_stoch_proc F (qty_empty asset)"
    using qty_empty_support_set by auto
qed													  

lemma (in disc_equity_market) sum_trading_strat:
  assumes "trading_strategy pf1"
  and "trading_strategy pf2"
shows "trading_strategy (qty_sum pf1 pf2)"
proof -
  have "\<forall> asset \<in> support_set pf1 \<union> support_set pf2. borel_predict_stoch_proc F (pf1 asset)"
    using assms by (simp add: inc_predict_support_trading_strat)
  have "\<forall> asset \<in> support_set pf2 \<union> support_set pf1. borel_predict_stoch_proc F (pf2 asset)"
    using assms by (simp add: inc_predict_support_trading_strat)
  have "\<forall> asset \<in> support_set pf1 \<union> support_set pf2. borel_predict_stoch_proc F ((qty_sum pf1 pf2) asset)"
  proof
    fix asset
    assume "asset \<in> support_set pf1 \<union> support_set pf2"
    show "borel_predict_stoch_proc F (qty_sum pf1 pf2 asset)" unfolding predict_stoch_proc_def qty_sum_def
    proof
      show "(\<lambda>w. pf1 asset 0 w + pf2 asset 0 w) \<in> borel_measurable (F 0)"
      proof -
        have "(\<lambda>w. pf1 asset 0 w) \<in> borel_measurable (F 0)"
        using \<open>\<forall>asset\<in>support_set pf1 \<union> support_set pf2. borel_predict_stoch_proc F (pf1 asset)\<close>
        \<open>asset \<in> support_set pf1 \<union> support_set pf2\<close> predict_stoch_proc_def by blast
        moreover have "(\<lambda>w. pf2 asset 0 w) \<in> borel_measurable (F 0)"
          using \<open>\<forall>asset\<in>support_set pf2 \<union> support_set pf1. borel_predict_stoch_proc F (pf2 asset)\<close>
          \<open>asset \<in> support_set pf1 \<union> support_set pf2\<close> predict_stoch_proc_def by blast
        ultimately show ?thesis by simp
      qed
    next
      show "\<forall>n. (\<lambda>w. pf1 asset (Suc n) w + pf2 asset (Suc n) w) \<in> borel_measurable (F n)"
      proof
        fix n
        have "(\<lambda>w. pf1 asset (Suc n) w) \<in> borel_measurable (F n)"
          using \<open>\<forall>asset\<in>support_set pf1 \<union> support_set pf2. borel_predict_stoch_proc F (pf1 asset)\<close>
          \<open>asset \<in> support_set pf1 \<union> support_set pf2\<close> predict_stoch_proc_def by blast
        moreover have "(\<lambda>w. pf2 asset (Suc n) w) \<in> borel_measurable (F n)"
          using \<open>\<forall>asset\<in>support_set pf2 \<union> support_set pf1. borel_predict_stoch_proc F (pf2 asset)\<close>
          \<open>asset \<in> support_set pf1 \<union> support_set pf2\<close> predict_stoch_proc_def by blast
        ultimately show "(\<lambda>w. pf1 asset (Suc n) w + pf2 asset (Suc n) w) \<in> borel_measurable (F n)" by simp
      qed
    qed
  qed
  thus ?thesis unfolding trading_strategy_def using sum_support_set[of pf1 pf2]
    by (meson assms(1) assms(2) subsetCE sum_portfolio trading_strategy_def)
qed

lemma (in disc_equity_market) mult_comp_trading_strat:
  assumes "trading_strategy pf1"
  and "borel_predict_stoch_proc F qty"
shows "trading_strategy (qty_mult_comp pf1 qty)"
proof -
  have "\<forall> asset \<in> support_set pf1. borel_predict_stoch_proc F (pf1 asset)"
    using assms unfolding trading_strategy_def by simp
  have "\<forall> asset \<in> support_set pf1. borel_predict_stoch_proc F (qty_mult_comp pf1 qty asset)"
    unfolding predict_stoch_proc_def qty_mult_comp_def
  proof (intro ballI conjI)
    fix asset
    assume "asset \<in> support_set pf1"
    show "(\<lambda>w. pf1 asset 0 w * qty 0 w) \<in> borel_measurable (F 0)"
    proof -
      have "(\<lambda>w. pf1 asset 0 w) \<in> borel_measurable (F 0)"
        using \<open>\<forall>asset\<in>support_set pf1. borel_predict_stoch_proc F (pf1 asset)\<close>
        \<open>asset \<in> support_set pf1\<close> predict_stoch_proc_def by auto
      moreover have "(\<lambda>w. qty 0 w) \<in> borel_measurable (F 0)" using assms predict_stoch_proc_def by auto
      ultimately show "(\<lambda>w. pf1 asset 0 w * qty 0 w) \<in> borel_measurable (F 0)" by simp
    qed
    show "\<forall>n. (\<lambda>w. pf1 asset (Suc n) w * qty (Suc n) w) \<in> borel_measurable (F n)"
    proof
      fix n
      have "(\<lambda>w. pf1 asset (Suc n) w) \<in> borel_measurable (F n)"
        using \<open>\<forall>asset\<in>support_set pf1. borel_predict_stoch_proc F (pf1 asset)\<close>
        \<open>asset \<in> support_set pf1\<close> predict_stoch_proc_def by blast
      moreover have "(\<lambda>w. qty (Suc n) w) \<in> borel_measurable (F n)" using assms predict_stoch_proc_def by blast
      ultimately show "(\<lambda>w. pf1 asset (Suc n) w * qty (Suc n) w) \<in> borel_measurable (F n)" by simp
    qed
  qed
  thus ?thesis unfolding trading_strategy_def using mult_comp_support_set[of pf1 qty]
    by (meson assms(1) mult_comp_portfolio subsetCE trading_strategy_def)
qed

lemma (in disc_equity_market) remove_comp_trading_strat:
  assumes "trading_strategy pf1"
shows "trading_strategy (qty_rem_comp pf1 x)"
proof -
  have "\<forall> asset \<in> support_set pf1. borel_predict_stoch_proc F (pf1 asset)"
    using assms unfolding trading_strategy_def by simp
  have "\<forall> asset \<in> support_set pf1. borel_predict_stoch_proc F (qty_rem_comp pf1 x asset)"
    unfolding predict_stoch_proc_def qty_rem_comp_def
  proof (intro ballI conjI)
    fix asset
    assume "asset \<in> support_set pf1"
    show "(pf1(x := \<lambda>n w. 0)) asset 0 \<in> borel_measurable (F 0)"
    proof -
      show "(\<lambda>w. (pf1(x := \<lambda>n w. 0)) asset 0 w) \<in> borel_measurable (F 0)"
      proof (cases "asset = x")
        case True
        thus ?thesis by simp
      next
        case False
        thus "(\<lambda>w. (pf1(x := \<lambda>n w. 0)) asset 0 w) \<in> borel_measurable (F 0)"
          using \<open>\<forall>asset\<in>support_set pf1. borel_predict_stoch_proc F (pf1 asset)\<close>
          \<open>asset \<in> support_set pf1\<close> by (simp add: predict_stoch_proc_def)
      qed
    qed
    show "\<forall>n. (\<lambda>w. (pf1(x := \<lambda>n w. 0)) asset (Suc n) w) \<in> borel_measurable (F n)"
    proof
      fix n
      show "(\<lambda>w. (pf1(x := \<lambda>n w. 0)) asset (Suc n) w) \<in> borel_measurable (F n)"
      proof (cases "asset = x")
        case True
        thus ?thesis by simp
      next
        case False
        thus "(\<lambda>w. (pf1(x := \<lambda>n w. 0)) asset (Suc n) w) \<in> borel_measurable (F n)"
          using \<open>\<forall>asset\<in>support_set pf1. borel_predict_stoch_proc F (pf1 asset)\<close>
          \<open>asset \<in> support_set pf1\<close> by (simp add: predict_stoch_proc_def)
      qed
    qed
  qed
  thus ?thesis unfolding trading_strategy_def using remove_comp_support_set[of pf1 x]
    by (metis Diff_empty assms remove_comp_portfolio subsetCE subset_Diff_insert trading_strategy_def)
qed


lemma (in disc_equity_market) replace_comp_trading_strat:
  assumes "trading_strategy pf1"
  and "trading_strategy pf2"
shows "trading_strategy (qty_replace_comp pf1 x pf2)" unfolding qty_replace_comp_def
proof (rule sum_trading_strat)
  show "trading_strategy (qty_rem_comp pf1 x)" using assms by (simp add: remove_comp_trading_strat)
  show "trading_strategy (qty_mult_comp pf2 (pf1 x))"
  proof (cases "x\<in> support_set pf1")
    case True
    hence "borel_predict_stoch_proc F (pf1 x)" using assms unfolding trading_strategy_def by simp
    thus ?thesis using assms by (simp add: mult_comp_trading_strat)
  next
    case False
    thus ?thesis
    proof -
      obtain nn :: "'c \<Rightarrow> ('c \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> nat" and aa :: "'c \<Rightarrow> ('c \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> 'a" where
        "\<forall>x0 x1. (\<exists>v2 v3. x1 x0 v2 v3 \<noteq> 0) = (x1 x0 (nn x0 x1) (aa x0 x1) \<noteq> 0)"
        by moura
      then have "\<forall>f c. (c \<notin> {c. \<exists>n a. f c n a \<noteq> 0} \<or> f c (nn c f) (aa c f) \<noteq> 0) \<and> (c \<in> {c. \<exists>n a. f c n a \<noteq> 0} \<or> (\<forall>n a. f c n a = 0))"
        by auto
      then show ?thesis
      proof -
        have "\<And>f c n a. qty_mult_comp f (pf1 x) (c::'c) n a = 0"
          by (metis False \<open>\<forall>f c. (c \<notin> {c. \<exists>n a. f c n a \<noteq> 0} \<or> f c (nn c f) (aa c f) \<noteq> 0) \<and> (c \<in> {c. \<exists>n a. f c n a \<noteq> 0} \<or> (\<forall>n a. f c n a = 0))\<close> mult.commute mult_zero_left qty_mult_comp_def support_set_def)
        then show ?thesis
          by (metis (no_types) \<open>\<forall>f c. (c \<notin> {c. \<exists>n a. f c n a \<noteq> 0} \<or> f c (nn c f) (aa c f) \<noteq> 0) \<and> (c \<in> {c. \<exists>n a. f c n a \<noteq> 0} \<or> (\<forall>n a. f c n a = 0))\<close> assms(2) mult_comp_portfolio support_set_def trading_strategy_def)
      qed
    qed
  qed
qed



subsubsection \<open>Self-financing portfolios\<close>

paragraph \<open>Closing value process\<close>

fun up_cl_proc where
  "up_cl_proc Mkt p 0 = val_process Mkt p 0" |
  "up_cl_proc Mkt p (Suc n) = (\<lambda>w. \<Sum>x\<in>support_set p. prices Mkt x (Suc n) w * p x (Suc n) w)"


definition cls_val_process where
"cls_val_process Mkt p = (if (\<not> (portfolio p)) then (\<lambda> n w. 0)
    else (\<lambda> n w . up_cl_proc Mkt p n w))"



lemma (in disc_filtr_prob_space) quantity_updated_borel:
  assumes "\<forall>n. \<forall> asset \<in> support_set p. p asset (Suc n) \<in> borel_measurable (F n)"
and "\<forall>n. \<forall>asset \<in> support_set p. prices Mkt asset n \<in> borel_measurable (F n)"
shows "\<forall>n. cls_val_process Mkt p n \<in> borel_measurable (F n)"
proof (cases "portfolio p")
case False
  have "cls_val_process Mkt p = (\<lambda> n w. 0)" unfolding cls_val_process_def using False by simp
  thus "?thesis" by simp
next
  case True
  show "\<forall>n. cls_val_process Mkt p n \<in> borel_measurable (F n)"
  proof
    fix n
    show "cls_val_process Mkt p n \<in> borel_measurable (F n)"
    proof (cases "n = 0")
      case False
      hence "\<exists>m. n = Suc m" using old.nat.exhaust by auto
      from this obtain m where "n = Suc m" by auto
      have "cls_val_process Mkt p (Suc m) = (\<lambda>w. \<Sum>x\<in>support_set p. prices Mkt x (Suc m) w * p x (Suc m) w)"
        unfolding cls_val_process_def using True by simp
      moreover have "(\<lambda>w. \<Sum>x\<in>support_set p. prices Mkt x (Suc m) w * p x (Suc m) w) \<in> borel_measurable (F (Suc m))"
      proof (rule borel_measurable_sum)
        fix asset
        assume "asset\<in> support_set p"
        hence "p asset (Suc m) \<in> borel_measurable (F m)" using assms unfolding trading_strategy_def adapt_stoch_proc_def by simp
        hence "p asset (Suc m) \<in> borel_measurable (F (Suc m))"
          using Suc_n_not_le_n increasing_measurable_info nat_le_linear by blast
        moreover have "prices Mkt asset (Suc m) \<in> borel_measurable (F (Suc m))"
          using \<open>asset \<in> support_set p\<close>  assms(2) unfolding support_adapt_def adapt_stoch_proc_def by blast
        ultimately show "(\<lambda>x. prices Mkt asset (Suc m) x * p asset (Suc m) x) \<in> borel_measurable (F (Suc m))" by simp
      qed
      ultimately have "cls_val_process Mkt p (Suc m) \<in> borel_measurable (F (Suc m))" by simp
      thus ?thesis using \<open>n = Suc m\<close> by simp
    next
      case True
      thus "cls_val_process Mkt p n \<in> borel_measurable (F n)"
        by (metis (no_types, lifting) assms(1) assms(2)  quantity_adapted up_cl_proc.simps(1)
            cls_val_process_def val_process_def)
    qed
  qed
qed


lemma (in disc_equity_market) cls_val_process_adapted:
  assumes "trading_strategy p"
and "support_adapt Mkt p"
  shows "borel_adapt_stoch_proc F (cls_val_process Mkt p)"
proof (cases "portfolio p")
  case False
    have "cls_val_process Mkt p = (\<lambda> n w. 0)" unfolding cls_val_process_def using False by simp
    thus "borel_adapt_stoch_proc F (cls_val_process Mkt p)"
      by (simp add: constant_process_borel_adapted)
next
  case True
  show ?thesis unfolding adapt_stoch_proc_def
  proof
    fix n
    show "cls_val_process Mkt p n \<in> borel_measurable (F n)"
    proof (cases "n = 0")
    case True
      thus "cls_val_process Mkt p n \<in> borel_measurable (F n)"
        using up_cl_proc.simps(1) assms
        by (metis (no_types, lifting) adapt_stoch_proc_def ats_val_process_adapted cls_val_process_def
            val_process_def)
    next
    case False
      hence "\<exists>m. Suc m = n" using not0_implies_Suc by blast
      from this obtain m where "Suc m = n" by auto
      hence "cls_val_process Mkt p n = up_cl_proc Mkt p n" unfolding cls_val_process_def using True by simp
      also have "... = (\<lambda>w. \<Sum>x\<in>support_set p. prices Mkt x n w * p x n w)"
        using up_cl_proc.simps(2) \<open>Suc m = n\<close> by auto
      finally have "cls_val_process Mkt p n = (\<lambda>w. \<Sum>x\<in>support_set p. prices Mkt x n w * p x n w)" .
    moreover have "(\<lambda>w. \<Sum>x\<in>support_set p. prices Mkt x n w * p x n w) \<in> borel_measurable (F n)"
    proof (rule borel_measurable_sum)
      fix asset
      assume "asset\<in> support_set p"
      hence "p asset n \<in> borel_measurable (F n)" using assms unfolding trading_strategy_def predict_stoch_proc_def
        using Suc_n_not_le_n \<open>Suc m = n\<close> increasing_measurable_info nat_le_linear by blast
      moreover have "prices Mkt asset n \<in> borel_measurable (F n)" using  assms \<open>asset \<in> support_set p\<close> unfolding support_adapt_def adapt_stoch_proc_def
        using stock_portfolio_def by blast
      ultimately show "(\<lambda>x. prices Mkt asset n x * p asset n x) \<in> borel_measurable (F n)" by simp
    qed
    ultimately show "cls_val_process Mkt p n \<in> borel_measurable (F n)" by simp
    qed
  qed
qed

lemma subset_cls_val_process:
  assumes "finite A"
  and "support_set p \<subseteq> A"
shows "\<forall>n w. cls_val_process Mkt p (Suc n) w = (sum (\<lambda>x. ((prices Mkt) x (Suc n) w) * (p x (Suc n) w)) A)"
proof (intro allI)
  fix n::nat
  fix w::'b
  have "portfolio p" using assms unfolding portfolio_def using finite_subset by auto
  have "\<exists>C. (support_set p) \<inter> C = {} \<and> (support_set p) \<union> C = A" using assms(2) by auto
  from this obtain C where "(support_set p) \<inter> C = {}" and "(support_set p) \<union> C = A" by auto note Cprops = this
  have "finite C" using assms \<open>(support_set p) \<union> C = A\<close> by auto
  have "\<forall>x\<in> C. p x (Suc n) w = 0" using Cprops(1) support_set_def by fastforce
  hence "(\<Sum>x\<in> C. ((prices Mkt) x (Suc n) w) * (p x (Suc n) w)) = 0" by simp
  hence "cls_val_process Mkt p (Suc n) w = (\<Sum>x\<in> (support_set p). ((prices Mkt) x (Suc n) w) * (p x (Suc n) w))
    + (\<Sum>x\<in> C. ((prices Mkt) x (Suc n) w) * (p x (Suc n) w))" unfolding cls_val_process_def
    using \<open>portfolio p\<close> up_cl_proc.simps(2)[of Mkt p n] by simp
  also have "... = (\<Sum> x\<in> A. ((prices Mkt) x (Suc n) w) * (p x (Suc n) w))"
    using \<open>portfolio p\<close> \<open>finite C\<close> Cprops portfolio_def sum_union_disjoint' by (metis (no_types, lifting))
  finally show "cls_val_process Mkt p (Suc n) w = (\<Sum> x\<in> A. ((prices Mkt) x (Suc n) w) * (p x (Suc n) w))" .
qed

lemma subset_cls_val_process':
  assumes "finite A"
  and "support_set p \<subseteq> A"
shows "cls_val_process Mkt p (Suc n) w = (sum (\<lambda>x. ((prices Mkt) x (Suc n) w) * (p x (Suc n) w)) A)"
proof -
  have "portfolio p" using assms unfolding portfolio_def using finite_subset by auto
  have "\<exists>C. (support_set p) \<inter> C = {} \<and> (support_set p) \<union> C = A" using assms(2) by auto
  from this obtain C where "(support_set p) \<inter> C = {}" and "(support_set p) \<union> C = A" by auto note Cprops = this
  have "finite C" using assms \<open>(support_set p) \<union> C = A\<close> by auto
  have "\<forall>x\<in> C. p x (Suc n) w = 0" using Cprops(1) support_set_def by fastforce
  hence "(\<Sum>x\<in> C. ((prices Mkt) x (Suc n) w) * (p x (Suc n) w)) = 0" by simp
  hence "cls_val_process Mkt p (Suc n) w = (\<Sum>x\<in> (support_set p). ((prices Mkt) x (Suc n) w) * (p x (Suc n) w))
    + (\<Sum>x\<in> C. ((prices Mkt) x (Suc n) w) * (p x (Suc n) w))" unfolding cls_val_process_def
    using \<open>portfolio p\<close> up_cl_proc.simps(2)[of Mkt p n] by simp
  also have "... = (\<Sum> x\<in> A. ((prices Mkt) x (Suc n) w) * (p x (Suc n) w))"
    using \<open>portfolio p\<close> \<open>finite C\<close> Cprops portfolio_def sum_union_disjoint' by (metis (no_types, lifting))
  finally show "cls_val_process Mkt p (Suc n) w = (\<Sum> x\<in> A. ((prices Mkt) x (Suc n) w) * (p x (Suc n) w))" .
qed



lemma sum_cls_val_process_Suc:
  assumes "portfolio pf1"
  and "portfolio pf2"
shows "\<forall>n w. cls_val_process Mkt (qty_sum pf1 pf2) (Suc n) w =
  (cls_val_process Mkt pf1) (Suc n) w + (cls_val_process Mkt pf2) (Suc n) w"
proof (intro allI)
  fix n w
  have vp1: "cls_val_process Mkt pf1 (Suc n) w =
    (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2). ((prices Mkt) x (Suc n) w) * (pf1 x (Suc n) w))"
  proof -
    have "finite (support_set pf1 \<union> support_set pf2) \<and> support_set pf1 \<subseteq> support_set pf1 \<union> support_set pf2"
      by (meson assms(1) assms(2) finite_Un portfolio_def sup.cobounded1)
    then show ?thesis
      by (simp add: subset_cls_val_process)
  qed
  have vp2: "cls_val_process Mkt pf2 (Suc n) w = (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2). ((prices Mkt) x (Suc n) w) * (pf2 x (Suc n) w))"
  proof -
    have "finite (support_set pf1 \<union> support_set pf2) \<and> support_set pf2 \<subseteq> support_set pf2 \<union> support_set pf1"
      by (meson assms(1) assms(2) finite_Un portfolio_def sup.cobounded1)
    then show ?thesis by (auto simp add: subset_cls_val_process)
  qed
  have pf:"portfolio (qty_sum pf1 pf2)" using assms by (simp add:sum_portfolio)
  have fin:"finite (support_set pf1 \<union> support_set pf2)" using assms finite_Un unfolding portfolio_def by auto
  have "(cls_val_process Mkt pf1) (Suc n) w + (cls_val_process Mkt pf2) (Suc n) w =
    (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2). ((prices Mkt) x (Suc n) w) * (pf1 x (Suc n) w)) +
    (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2). ((prices Mkt) x (Suc n) w) * (pf2 x (Suc n) w))"
    using vp1 vp2 by simp
  also have "... = (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2).
    (((prices Mkt) x (Suc n) w) * (pf1 x (Suc n) w)) + ((prices Mkt) x (Suc n) w) * (pf2 x (Suc n) w))"
    by (simp add: sum.distrib)
  also have "... = (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2).
    ((prices Mkt) x (Suc n) w) * ((pf1 x (Suc n) w) + (pf2 x (Suc n) w)))" by (simp add: distrib_left)
  also have "... = (\<Sum> x\<in> (support_set pf1)\<union> (support_set pf2).
    ((prices Mkt) x (Suc n) w) * ((qty_sum pf1 pf2) x (Suc n) w))" by (simp add: qty_sum_def)
  also have "... = (\<Sum> x\<in> (support_set (qty_sum pf1 pf2)).
    ((prices Mkt) x (Suc n) w) * ((qty_sum pf1 pf2) x (Suc n) w))" using sum_support_set[of pf1 pf2]
    subset_cls_val_process[of "support_set pf1\<union> support_set pf2" "qty_sum pf1 pf2"] pf fin
    unfolding cls_val_process_def by simp
  also have "... = cls_val_process Mkt (qty_sum pf1 pf2) (Suc n) w"
    by (metis (no_types, lifting) pf sum.cong up_cl_proc.simps(2) cls_val_process_def)
  finally have "(cls_val_process Mkt pf1) (Suc n) w + (cls_val_process Mkt pf2) (Suc n) w =
    cls_val_process Mkt (qty_sum pf1 pf2) (Suc n) w" .
  thus "cls_val_process Mkt (qty_sum pf1 pf2) (Suc n) w =
    (cls_val_process Mkt pf1) (Suc n) w + (cls_val_process Mkt pf2) (Suc n) w" ..
qed

lemma sum_cls_val_process0:
  assumes "portfolio pf1"
  and "portfolio pf2"
shows "\<forall>w. cls_val_process Mkt (qty_sum pf1 pf2) 0 w =
  (cls_val_process Mkt pf1) 0 w + (cls_val_process Mkt pf2) 0 w" unfolding cls_val_process_def
  by (simp add: sum_val_process assms(1) assms(2) sum_portfolio)

lemma sum_cls_val_process:
  assumes "portfolio pf1"
  and "portfolio pf2"
shows "\<forall>n w. cls_val_process Mkt (qty_sum pf1 pf2) n w =
  (cls_val_process Mkt pf1) n w + (cls_val_process Mkt pf2) n w"
  by (metis (no_types, lifting) assms(1) assms(2) sum_cls_val_process0 sum_cls_val_process_Suc up_cl_proc.elims)

lemma mult_comp_cls_val_process0:
  assumes "portfolio pf1"
  shows "\<forall>w. cls_val_process Mkt (qty_mult_comp pf1 qty) 0 w =
  ((cls_val_process Mkt pf1) 0 w) * (qty (Suc 0) w)" unfolding cls_val_process_def
  by (simp add: assms mult_comp_portfolio mult_comp_val_process)

lemma mult_comp_cls_val_process_Suc:
  assumes "portfolio pf1"
  shows "\<forall>n w. cls_val_process Mkt (qty_mult_comp pf1 qty) (Suc n) w =
  ((cls_val_process Mkt pf1) (Suc n) w) * (qty (Suc n) w)"
proof (intro allI)
  fix n w
  have pf:"portfolio (qty_mult_comp pf1 qty)" using assms by (simp add:mult_comp_portfolio)
  have fin:"finite (support_set pf1)" using assms unfolding portfolio_def by auto
  have "((cls_val_process Mkt pf1) (Suc n) w) * (qty (Suc n) w) =
    (\<Sum> x\<in> (support_set pf1). ((prices Mkt) x (Suc n) w) * (pf1 x (Suc n) w))*(qty (Suc n) w)"
    unfolding cls_val_process_def using assms by simp
  also have "... = (\<Sum> x\<in> (support_set pf1).
    (((prices Mkt) x (Suc n) w) * (pf1 x (Suc n) w) * (qty (Suc n) w)))" using sum_distrib_right by auto
  also have "... = (\<Sum> x\<in> (support_set pf1).
    ((prices Mkt) x (Suc n) w) * ((qty_mult_comp pf1 qty) x (Suc n) w))" unfolding qty_mult_comp_def
    by (simp add: mult.commute mult.left_commute)
  also have "... = (\<Sum> x\<in> (support_set (qty_mult_comp pf1 qty)).
    ((prices Mkt) x (Suc n) w) * ((qty_mult_comp pf1 qty) x (Suc n) w))" using mult_comp_support_set[of pf1 qty]
    subset_cls_val_process[of "support_set pf1" "qty_mult_comp pf1 qty"] pf fin up_cl_proc.simps(2)
    unfolding cls_val_process_def by simp
  also have "... = cls_val_process Mkt (qty_mult_comp pf1 qty) (Suc n) w"   by (metis (no_types, lifting) pf sum.cong cls_val_process_def up_cl_proc.simps(2))
  finally have "(cls_val_process Mkt pf1) (Suc n) w * (qty (Suc n) w) = cls_val_process Mkt (qty_mult_comp pf1 qty) (Suc n) w" .
  thus "cls_val_process Mkt (qty_mult_comp pf1 qty) (Suc n) w = (cls_val_process Mkt pf1) (Suc n) w * (qty (Suc n) w)" ..
qed




lemma remove_comp_cls_val_process0:
  assumes "portfolio pf1"
  shows "\<forall>w. cls_val_process Mkt (qty_rem_comp pf1 y) 0 w =
  ((cls_val_process Mkt pf1) 0 w) - (prices Mkt y 0 w)* (pf1 y (Suc 0) w)" unfolding cls_val_process_def
  by (simp add: assms remove_comp_portfolio remove_comp_val_process)


lemma remove_comp_cls_val_process_Suc:
  assumes "portfolio pf1"
  shows "\<forall>n w. cls_val_process Mkt (qty_rem_comp pf1 y) (Suc n) w =
  ((cls_val_process Mkt pf1) (Suc n) w) - (prices Mkt y (Suc n) w)* (pf1 y (Suc n) w)"
proof (intro allI)
  fix n w
  have pf:"portfolio (qty_rem_comp pf1 y)" using assms by (simp add:remove_comp_portfolio)
  have fin:"finite (support_set pf1)" using assms unfolding portfolio_def by auto
  hence fin2: "finite (support_set pf1 - {y})" by simp
  have "((cls_val_process Mkt pf1) (Suc n) w)  =
    (\<Sum> x\<in> (support_set pf1). ((prices Mkt) x (Suc n) w) * (pf1 x (Suc n) w))"
    unfolding cls_val_process_def using assms by simp
  also have "... = (\<Sum> x\<in> (support_set pf1 - {y}).
    (((prices Mkt) x (Suc n) w) * (pf1 x (Suc n) w))) + (prices Mkt y (Suc n) w)* (pf1 y (Suc n) w)"
  proof (cases "y\<in> support_set pf1")
    case True
    thus ?thesis by (simp add: fin sum_diff1)
  next
    case False
    hence "pf1 y (Suc n) w = 0" unfolding support_set_def by simp
    thus ?thesis by (simp add: fin sum_diff1)
  qed
  also have "... = (\<Sum> x\<in> (support_set pf1 - {y}).
    ((prices Mkt) x (Suc n) w) * ((qty_rem_comp pf1 y) x (Suc n) w)) + (prices Mkt y (Suc n) w)* (pf1 y (Suc n) w)"
  proof -
    have "(\<Sum> x\<in> (support_set pf1 - {y}). (((prices Mkt) x (Suc n) w) * (pf1 x (Suc n) w))) =
      (\<Sum> x\<in> (support_set pf1 - {y}). ((prices Mkt) x (Suc n) w) * ((qty_rem_comp pf1 y) x (Suc n) w))"
    proof (rule sum.cong,simp)
      fix x
      assume "x\<in> support_set pf1 - {y}"
      show "prices Mkt x (Suc n) w * pf1 x (Suc n) w = prices Mkt x (Suc n) w * qty_rem_comp pf1 y x (Suc n) w" using remove_comp_values
        by (metis DiffD2 \<open>x \<in> support_set pf1 - {y}\<close> singletonI)
    qed
    thus ?thesis by simp
  qed
  also have "... = (cls_val_process Mkt (qty_rem_comp pf1 y) (Suc n) w) + (prices Mkt y (Suc n) w)* (pf1 y (Suc n) w)"
    using subset_cls_val_process[of "support_set pf1 - {y}" "qty_rem_comp pf1 y"] fin2
    by (simp add: remove_comp_support_set)
  finally have "(cls_val_process Mkt pf1) (Suc n) w =
    (cls_val_process Mkt (qty_rem_comp pf1 y) (Suc n) w) + (prices Mkt y (Suc n) w)* (pf1 y (Suc n) w)" .
  thus  "cls_val_process Mkt (qty_rem_comp pf1 y) (Suc n) w =
    ((cls_val_process Mkt pf1) (Suc n) w) - (prices Mkt y (Suc n) w)* (pf1 y (Suc n) w)" by simp
qed



lemma replace_comp_cls_val_process0:
  assumes "\<forall>w. prices Mkt x 0 w = cls_val_process Mkt pf2 0 w"
  and "portfolio pf1"
  and "portfolio pf2"
shows "\<forall>w. cls_val_process Mkt (qty_replace_comp pf1 x pf2) 0 w = cls_val_process Mkt pf1 0 w"
proof
  fix w
  have "cls_val_process Mkt (qty_replace_comp pf1 x pf2) 0 w = cls_val_process Mkt (qty_rem_comp pf1 x) 0 w +
    cls_val_process Mkt (qty_mult_comp pf2 (pf1 x)) 0 w" unfolding qty_replace_comp_def using assms
    sum_cls_val_process0[of "qty_rem_comp pf1 x" "qty_mult_comp pf2 (pf1 x)"]
    by (simp add: mult_comp_portfolio remove_comp_portfolio)
  also have "... = cls_val_process Mkt pf1 0 w - (prices Mkt x 0 w * pf1 x (Suc 0) w) +
    cls_val_process Mkt pf2 0 w * pf1 x (Suc 0) w"
    by (simp add: assms(2) assms(3) mult_comp_cls_val_process0 remove_comp_cls_val_process0)
  also have "... = cls_val_process Mkt pf1 0 w" using assms by simp
  finally show "cls_val_process Mkt (qty_replace_comp pf1 x pf2) 0 w = cls_val_process Mkt pf1 0 w" .
qed


lemma replace_comp_cls_val_process_Suc:
  assumes "\<forall>n w. prices Mkt x (Suc n) w = cls_val_process Mkt pf2 (Suc n) w"
  and "portfolio pf1"
  and "portfolio pf2"
  shows "\<forall>n w. cls_val_process Mkt (qty_replace_comp pf1 x pf2) (Suc n) w = cls_val_process Mkt pf1 (Suc n) w"
proof (intro allI)
  fix n w
  have "cls_val_process Mkt (qty_replace_comp pf1 x pf2) (Suc n) w = cls_val_process Mkt (qty_rem_comp pf1 x) (Suc n) w +
    cls_val_process Mkt (qty_mult_comp pf2 (pf1 x)) (Suc n) w" unfolding qty_replace_comp_def using assms
    sum_cls_val_process_Suc[of "qty_rem_comp pf1 x" "qty_mult_comp pf2 (pf1 x)"]
    by (simp add: mult_comp_portfolio remove_comp_portfolio)
  also have "... = cls_val_process Mkt pf1 (Suc n) w - (prices Mkt x (Suc n) w * pf1 x (Suc n) w) +
    cls_val_process Mkt pf2 (Suc n) w * pf1 x (Suc n) w"
    by (simp add: assms(2) assms(3) mult_comp_cls_val_process_Suc remove_comp_cls_val_process_Suc)
  also have "... = cls_val_process Mkt pf1 (Suc n) w" using assms by simp
  finally show "cls_val_process Mkt (qty_replace_comp pf1 x pf2) (Suc n) w = cls_val_process Mkt pf1 (Suc n) w" .
qed


lemma replace_comp_cls_val_process:
  assumes "\<forall>n w. prices Mkt x n w = cls_val_process Mkt pf2 n w"
  and "portfolio pf1"
  and "portfolio pf2"
  shows "\<forall>n w. cls_val_process Mkt (qty_replace_comp pf1 x pf2) n w = cls_val_process Mkt pf1 n w"
  by (metis (no_types, lifting) assms replace_comp_cls_val_process0 replace_comp_cls_val_process_Suc up_cl_proc.elims)


lemma qty_single_updated:
  shows "cls_val_process Mkt (qty_single asset qty) (Suc n) w =
    prices Mkt asset (Suc n) w * qty (Suc n) w"
proof -
  have "cls_val_process Mkt (qty_single asset qty) (Suc n) w =
    (sum (\<lambda>x. ((prices Mkt) x (Suc n) w) * ((qty_single asset qty) x (Suc n) w)) {asset})"
  proof (rule subset_cls_val_process')
    show "finite {asset}" by simp
    show "support_set (qty_single asset qty) \<subseteq> {asset}" by (simp add: single_comp_support)
  qed
  also have "... = prices Mkt asset (Suc n) w * qty (Suc n) w" unfolding qty_single_def by simp
  finally show ?thesis .
qed



paragraph \<open>Self-financing\<close>

definition self_financing where
  "self_financing Mkt p \<longleftrightarrow> (\<forall>n. val_process Mkt p (Suc n) = cls_val_process Mkt p (Suc n))"


lemma self_financingE:
  assumes "self_financing Mkt p"
  shows "\<forall>n. val_process Mkt p n = cls_val_process Mkt p n"
proof
  fix n
  show "val_process Mkt p n = cls_val_process Mkt p n"
  proof (cases "n = 0")
    case False
    thus ?thesis using assms unfolding self_financing_def
      by (metis up_cl_proc.elims)
  next
    case True
    thus ?thesis by (simp add: cls_val_process_def val_process_def)
  qed
qed




lemma static_portfolio_self_financing:
  assumes "\<forall> x \<in> support_set p. (\<forall>w i. p x i w = p x (Suc i) w)"
  shows "self_financing Mkt p"
unfolding self_financing_def
proof (intro allI impI)
  fix n
  show "val_process Mkt p (Suc n) = cls_val_process Mkt p (Suc n)"
  proof (cases "portfolio p")
    case False
    thus ?thesis unfolding val_process_def cls_val_process_def by simp
  next
    case True
    have "\<forall>w. (\<Sum>x\<in> support_set p. prices Mkt x (Suc n) w * p x (Suc (Suc n)) w) =
         cls_val_process Mkt p (Suc n) w"
    proof
      fix w
      show "(\<Sum>x\<in> support_set p. prices Mkt x (Suc n) w * p x (Suc (Suc n)) w) =
           cls_val_process Mkt p (Suc n) w"
      proof -
        have "(\<Sum>x\<in> support_set p. prices Mkt x (Suc n) w * p x (Suc (Suc n)) w) =
            (\<Sum>x\<in> support_set p. prices Mkt x (Suc n) w * p x (Suc n) w)"
        proof (rule sum.cong, simp)
          fix x
          assume "x\<in> support_set p"
          hence "p x (Suc n) w = p x (Suc (Suc n)) w" using assms by blast
          thus "prices Mkt x (Suc n) w * p x (Suc (Suc n)) w = prices Mkt x (Suc n) w * p x (Suc n) w" by simp
        qed
        also have "... = cls_val_process Mkt p (Suc n) w"
           using up_cl_proc.simps(2)[of Mkt p n] by (metis True cls_val_process_def)
        finally show ?thesis .
      qed
    qed
    moreover have "\<forall>w. val_process Mkt p (Suc n) w = (\<Sum>x\<in> support_set p. prices Mkt x (Suc n) w * p x (Suc (Suc n)) w)"
      unfolding val_process_def using True by simp
    ultimately show ?thesis by auto
  qed
qed



lemma sum_self_financing:
  assumes "portfolio pf1"
  and "portfolio pf2"
  and "self_financing Mkt pf1"
  and "self_financing Mkt pf2"
shows "self_financing Mkt (qty_sum pf1 pf2)"
proof -
  have "\<forall> n w. val_process Mkt (qty_sum pf1 pf2) (Suc n) w =
    cls_val_process Mkt (qty_sum pf1 pf2) (Suc n) w"
  proof (intro allI)
    fix n w
    have "val_process Mkt (qty_sum pf1 pf2) (Suc n) w = val_process Mkt pf1 (Suc n) w + val_process Mkt pf2 (Suc n) w"
      using assms by (simp add:sum_val_process)
    also have "... = cls_val_process Mkt pf1 (Suc n) w + val_process Mkt pf2 (Suc n) w" using assms
      unfolding self_financing_def by simp
    also have "... = cls_val_process Mkt pf1 (Suc n) w + cls_val_process Mkt pf2 (Suc n) w"
      using assms unfolding self_financing_def by simp
    also have "... = cls_val_process Mkt (qty_sum pf1 pf2) (Suc n) w" using assms by (simp add: sum_cls_val_process)
    finally show "val_process Mkt (qty_sum pf1 pf2) (Suc n) w =
      cls_val_process Mkt (qty_sum pf1 pf2) (Suc n) w" .
  qed
  thus ?thesis unfolding self_financing_def by auto
qed

lemma mult_time_constant_self_financing:
  assumes "portfolio pf1"
  and "self_financing Mkt pf1"
  and "\<forall>n w. qty n w = qty (Suc n) w"
shows "self_financing Mkt (qty_mult_comp pf1 qty)"
proof -
  have "\<forall> n w. val_process Mkt (qty_mult_comp pf1 qty) (Suc n) w =
    cls_val_process Mkt (qty_mult_comp pf1 qty) (Suc n) w"
  proof (intro allI)
    fix n w
    have "val_process Mkt (qty_mult_comp pf1 qty) (Suc n) w = val_process Mkt pf1 (Suc n) w * qty (Suc n) w"
      using assms by (simp add:mult_comp_val_process)
    also have "... = cls_val_process Mkt pf1 (Suc n) w * qty (Suc n) w" using assms
      unfolding self_financing_def by simp
    also have "... = cls_val_process Mkt (qty_mult_comp pf1 qty) (Suc n) w" using assms
       by (auto simp add: mult_comp_cls_val_process_Suc)
    finally show "val_process Mkt (qty_mult_comp pf1 qty) (Suc n) w =
      cls_val_process Mkt (qty_mult_comp pf1 qty) (Suc n) w" .
  qed
  thus ?thesis unfolding self_financing_def by auto
qed



lemma replace_comp_self_financing:
  assumes "\<forall>n w. prices Mkt x n w = cls_val_process Mkt pf2 n w"
  and "portfolio pf1"
  and "portfolio pf2"
  and "self_financing Mkt pf1"
  and "self_financing Mkt pf2"
shows "self_financing Mkt (qty_replace_comp pf1 x pf2)"
proof -
  have sfeq: "\<forall>n w. prices Mkt x n w = val_process Mkt pf2 n w" using assms by (simp add: self_financingE)
  have "\<forall> n w. cls_val_process Mkt (qty_replace_comp pf1 x pf2) (Suc n) w =
    val_process Mkt (qty_replace_comp pf1 x pf2) (Suc n) w"
  proof (intro allI)
    fix n w
    have "cls_val_process Mkt (qty_replace_comp pf1 x pf2) (Suc n) w = cls_val_process Mkt pf1 (Suc n) w"
      using assms by (simp add:replace_comp_cls_val_process)
    also have "... = val_process Mkt pf1 (Suc n) w" using assms unfolding self_financing_def by simp
    also have "... = val_process Mkt (qty_replace_comp pf1 x pf2) (Suc n) w"
      using assms sfeq by (simp add: replace_comp_val_process self_financing_def)
    finally show "cls_val_process Mkt (qty_replace_comp pf1 x pf2) (Suc n) w =
      val_process Mkt (qty_replace_comp pf1 x pf2) (Suc n) w" .
  qed
  thus ?thesis unfolding self_financing_def by auto
qed




paragraph \<open>Make a portfolio self-financing\<close>

fun  remaining_qty where
  init: "remaining_qty Mkt v pf asset 0 = (\<lambda>w. 0)" |
  first:  "remaining_qty Mkt v pf asset (Suc 0) = (\<lambda>w. (v - val_process Mkt pf 0 w)/(prices Mkt asset 0 w))" |
  step: "remaining_qty Mkt v pf asset (Suc (Suc n)) = (\<lambda>w. (remaining_qty Mkt v pf asset (Suc n) w) +
    (cls_val_process Mkt pf (Suc n) w - val_process Mkt pf (Suc n) w)/(prices Mkt asset (Suc n) w))"

lemma (in disc_equity_market) remaining_qty_predict':
  assumes "borel_adapt_stoch_proc F (prices Mkt asset)"
  and "trading_strategy pf"
and "support_adapt Mkt pf"
shows "remaining_qty Mkt v pf asset (Suc n) \<in> borel_measurable (F n)"
proof (induct n)
  case 0
  have "(\<lambda>w. (v - val_process Mkt pf 0 w)/(prices Mkt asset 0 w))\<in> borel_measurable (F 0)"
  proof (rule borel_measurable_divide)
    have "val_process Mkt pf 0 \<in> borel_measurable (F 0)" using assms
      ats_val_process_adapted by (simp add:adapt_stoch_proc_def)
    thus "(\<lambda>x. v - val_process Mkt pf 0 x) \<in> borel_measurable (F 0)" by simp
    show "prices Mkt asset 0 \<in> borel_measurable (F 0)" using assms unfolding adapt_stoch_proc_def by simp
  qed
  thus ?case by simp
next
  case (Suc n)
  have "(\<lambda>w. (cls_val_process Mkt pf (Suc n) w - val_process Mkt pf (Suc n) w)/
    (prices Mkt asset (Suc n) w)) \<in> borel_measurable (F (Suc n))"
  proof (rule borel_measurable_divide)
    show "(\<lambda>w. (cls_val_process Mkt pf (Suc n) w - val_process Mkt pf (Suc n) w)) \<in> borel_measurable (F (Suc n))"
    proof (rule borel_measurable_diff)
      show "(\<lambda>w. (cls_val_process Mkt pf (Suc n) w)) \<in> borel_measurable (F (Suc n))"
        using assms cls_val_process_adapted unfolding adapt_stoch_proc_def by auto
      show "(\<lambda>w. (val_process Mkt pf (Suc n) w)) \<in> borel_measurable (F (Suc n))"
        using assms  ats_val_process_adapted by (simp add:adapt_stoch_proc_def)
    qed
    show "prices Mkt asset (Suc n) \<in> borel_measurable (F (Suc n))" using assms unfolding adapt_stoch_proc_def by simp
  qed
  moreover have "remaining_qty Mkt v pf asset (Suc n) \<in> borel_measurable (F (Suc n))" using Suc
    Suc_n_not_le_n increasing_measurable_info nat_le_linear by blast
  ultimately show ?case using Suc remaining_qty.simps(3)[of Mkt v pf asset n] by simp
qed

lemma (in disc_equity_market) remaining_qty_predict:
  assumes "borel_adapt_stoch_proc F (prices Mkt asset)"
  and "trading_strategy pf"
and "support_adapt Mkt pf"
shows "borel_predict_stoch_proc F (remaining_qty Mkt v pf asset)"  unfolding predict_stoch_proc_def
proof (intro conjI allI)
  show "remaining_qty Mkt v pf asset 0 \<in> borel_measurable (F 0)" using init by simp
  fix n
  show "remaining_qty Mkt v pf asset (Suc n) \<in> borel_measurable (F n)" using assms by (simp add: remaining_qty_predict')
qed


lemma (in disc_equity_market) remaining_qty_adapt:
  assumes "borel_adapt_stoch_proc F (prices Mkt asset)"
  and "trading_strategy pf"
and "support_adapt Mkt pf"
shows "remaining_qty Mkt v pf asset n \<in> borel_measurable (F n)"
  using adapt_stoch_proc_def assms(1) assms(2) predict_imp_adapt remaining_qty_predict
  by (metis assms(3))


lemma (in disc_equity_market) remaining_qty_adapted:
  assumes "borel_adapt_stoch_proc F (prices Mkt asset)"
  and "trading_strategy pf"
and "support_adapt Mkt pf"
shows "borel_adapt_stoch_proc F (remaining_qty Mkt v pf asset)" using assms unfolding adapt_stoch_proc_def
  using assms remaining_qty_adapt by blast


definition self_finance where
  "self_finance Mkt v pf (asset::'a) = qty_sum pf (qty_single asset (remaining_qty Mkt v pf asset))"


lemma self_finance_portfolio:
  assumes "portfolio pf"
shows "portfolio (self_finance Mkt v pf asset)" unfolding self_finance_def
  by (simp add: assms single_comp_portfolio sum_portfolio)


lemma self_finance_init:
  assumes "\<forall>w. prices Mkt asset 0 w \<noteq> 0"
  and "portfolio pf"
shows "val_process Mkt (self_finance Mkt v pf asset) 0 w = v"
proof -
  define scp where "scp = qty_single asset (remaining_qty Mkt v pf asset)"
  have "val_process Mkt (self_finance Mkt v pf asset) 0 w =
    val_process Mkt pf 0 w +
    val_process Mkt scp 0 w" unfolding scp_def using assms single_comp_portfolio[of asset]
    sum_val_process[of pf "qty_single asset (remaining_qty Mkt v pf asset)" Mkt]
    by (simp add: \<open>\<And>qty. portfolio (qty_single asset qty)\<close> self_finance_def)
  also have "... = val_process Mkt pf 0 w +
    (sum (\<lambda>x. ((prices Mkt) x 0 w) * (scp x (Suc 0) w)) {asset})"
    using subset_val_process'[of "{asset}" scp] unfolding scp_def by (auto simp add:  single_comp_support)
  also have "... = val_process Mkt pf 0 w + prices Mkt asset 0 w * scp asset (Suc 0) w" by auto
  also have "... = val_process Mkt pf 0 w + prices Mkt asset 0 w * (remaining_qty Mkt v pf asset) (Suc 0) w"
    unfolding scp_def qty_single_def by simp
  also have "... = val_process Mkt pf 0 w + prices Mkt asset 0 w * (v - val_process Mkt pf 0 w)/(prices Mkt asset 0 w)"
    by simp
  also have "... = val_process Mkt pf 0 w + (v - val_process Mkt pf 0 w)" using assms by simp
  also have "... = v" by simp
  finally show ?thesis .
qed


lemma self_finance_succ:
  assumes "prices Mkt asset (Suc n) w \<noteq> 0"
  and "portfolio pf"
shows "val_process Mkt (self_finance Mkt v pf asset) (Suc n) w = prices Mkt asset (Suc n) w * remaining_qty Mkt v pf asset (Suc n) w +
  cls_val_process Mkt pf (Suc n) w"
proof -
  define scp where "scp = qty_single asset (remaining_qty Mkt v pf asset)"
  have "val_process Mkt (self_finance Mkt v pf asset) (Suc n) w =
    val_process Mkt pf (Suc n) w +
    val_process Mkt scp (Suc n) w" unfolding scp_def using assms single_comp_portfolio[of asset]
    sum_val_process[of pf "qty_single asset (remaining_qty Mkt v pf asset)" Mkt]
    by (simp add: \<open>\<And>qty. portfolio (qty_single asset qty)\<close> self_finance_def)
  also have "... = val_process Mkt pf (Suc n) w +
    (sum (\<lambda>x. ((prices Mkt) x (Suc n) w) * (scp x (Suc (Suc n)) w)) {asset})"
    using subset_val_process'[of "{asset}" scp] unfolding scp_def by (auto simp add:  single_comp_support)
  also have "... = val_process Mkt pf (Suc n) w + prices Mkt asset (Suc n) w * scp asset (Suc (Suc n)) w" by auto
  also have "... = val_process Mkt pf (Suc n) w + prices Mkt asset (Suc n) w * (remaining_qty Mkt v pf asset) (Suc (Suc n)) w"
    unfolding scp_def qty_single_def by simp
  also have "... = val_process Mkt pf (Suc n) w +
    prices Mkt asset (Suc n) w *
    (remaining_qty Mkt v pf asset (Suc n) w + (cls_val_process Mkt pf (Suc n) w - val_process Mkt pf (Suc n) w)/(prices Mkt asset (Suc n) w))"
    by simp
  also have "... = val_process Mkt pf (Suc n) w +
     prices Mkt asset (Suc n) w * remaining_qty Mkt v pf asset (Suc n) w +
    prices Mkt asset (Suc n) w * (cls_val_process Mkt pf (Suc n) w - val_process Mkt pf (Suc n) w)/(prices Mkt asset (Suc n) w)"
     by (simp add: distrib_left)
  also have "... = val_process Mkt pf (Suc n) w +
     prices Mkt asset (Suc n) w * remaining_qty Mkt v pf asset (Suc n) w + (cls_val_process Mkt pf (Suc n) w - val_process Mkt pf (Suc n) w)"
     using assms by simp
  also have "... = prices Mkt asset (Suc n) w * remaining_qty Mkt v pf asset (Suc n) w + cls_val_process Mkt pf (Suc n) w" by simp
  finally show ?thesis .
qed


lemma self_finance_updated:
  assumes "prices Mkt asset (Suc n) w \<noteq> 0"
  and "portfolio pf"
shows "cls_val_process Mkt (self_finance Mkt v pf asset) (Suc n) w =
  cls_val_process Mkt pf (Suc n) w + prices Mkt asset (Suc n) w * (remaining_qty Mkt v pf asset) (Suc n) w"
proof -
  define scp where "scp = qty_single asset (remaining_qty Mkt v pf asset)"
  have "cls_val_process Mkt (self_finance Mkt v pf asset) (Suc n) w =
    cls_val_process Mkt pf (Suc n) w +
    cls_val_process Mkt scp (Suc n) w" unfolding scp_def using assms single_comp_portfolio[of asset]
    sum_cls_val_process[of pf "qty_single asset (remaining_qty Mkt v pf asset)" Mkt]
    by (simp add: \<open>\<And>qty. portfolio (qty_single asset qty)\<close> self_finance_def)
  also have "... = cls_val_process Mkt pf (Suc n) w +
    (sum (\<lambda>x. ((prices Mkt) x (Suc n) w) * (scp x (Suc n) w)) {asset})"
    using subset_cls_val_process[of "{asset}" scp] unfolding scp_def by (auto simp add:  single_comp_support)
  also have "... = cls_val_process Mkt pf (Suc n) w + prices Mkt asset (Suc n) w * scp asset (Suc n) w" by auto
  also have "... = cls_val_process Mkt pf (Suc n) w + prices Mkt asset (Suc n) w * (remaining_qty Mkt v pf asset) (Suc n) w"
    unfolding scp_def qty_single_def by simp
  finally show ?thesis .
qed

lemma self_finance_charact:
  assumes "\<forall> n w. prices Mkt asset (Suc n) w \<noteq> 0"
  and "portfolio pf"
shows "self_financing Mkt (self_finance Mkt v pf asset)"
proof-
  have "\<forall>n w. val_process Mkt (self_finance Mkt v pf asset) (Suc n) w =
     cls_val_process Mkt (self_finance Mkt v pf asset) (Suc n) w"
  proof (intro allI)
    fix n w
    show "val_process Mkt (self_finance Mkt v pf asset) (Suc n) w =
      cls_val_process Mkt (self_finance Mkt v pf asset) (Suc n) w" using assms self_finance_succ[of Mkt asset]
      by (simp add: self_finance_updated)
  qed
  thus ?thesis unfolding self_financing_def by auto
qed


subsubsection \<open>Replicating portfolios\<close>


definition (in disc_filtr_prob_space) price_structure::"('a \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> real \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool" where
  "price_structure pyf T \<pi> pr \<longleftrightarrow> ((\<forall> w\<in> space M. pr 0 w = \<pi>) \<and> (AE w in M. pr T w = pyf w) \<and> (pr T \<in> borel_measurable (F T)))"

lemma (in disc_filtr_prob_space) price_structure_init:
  assumes "price_structure pyf T \<pi> pr"
  shows "\<forall> w\<in> space M. pr 0 w = \<pi>" using assms unfolding price_structure_def by simp

lemma (in disc_filtr_prob_space) price_structure_borel_measurable:
  assumes "price_structure pyf T \<pi> pr"
  shows "pr T \<in> borel_measurable (F T)" using assms unfolding price_structure_def by simp

lemma (in disc_filtr_prob_space) price_structure_maturity:
  assumes "price_structure pyf T \<pi> pr"
  shows "AE w in M. pr T w = pyf w" using assms unfolding price_structure_def by simp

definition (in disc_equity_market) replicating_portfolio where
  "replicating_portfolio pf der matur  \<longleftrightarrow> (stock_portfolio Mkt pf) \<and> (trading_strategy pf) \<and> (self_financing Mkt pf) \<and>
  (AE w in M. cls_val_process Mkt pf matur w = der w)"


definition (in disc_equity_market) is_attainable where
  "is_attainable der matur \<longleftrightarrow> (\<exists> pf. replicating_portfolio pf der matur)"

lemma (in disc_equity_market) replicating_price_process:
  assumes "replicating_portfolio pf der matur"
and "support_adapt Mkt pf"
  shows "price_structure der matur (initial_value pf) (cls_val_process Mkt pf)"
  unfolding price_structure_def
proof (intro conjI)
  show "AE w in M. cls_val_process Mkt pf matur w = der w" using assms unfolding replicating_portfolio_def by simp
  show "\<forall>w\<in>space M. cls_val_process Mkt pf 0 w = initial_value pf"
  proof
    fix w
    assume "w\<in> space M"
    thus "cls_val_process Mkt pf 0 w = initial_value pf" unfolding initial_value_def using constant_imageI[of "cls_val_process Mkt pf 0"]
      trading_strategy_init[of pf] assms replicating_portfolio_def [of pf der matur]
      by (simp add: stock_portfolio_def cls_val_process_def)
  qed
  show "cls_val_process Mkt pf matur \<in> borel_measurable (F matur)" using assms unfolding replicating_portfolio_def
    using ats_val_process_adapted[of pf]
    cls_val_process_adapted by (simp add:adapt_stoch_proc_def)
qed


subsubsection \<open>Arbitrages\<close>


definition (in disc_filtr_prob_space) arbitrage_process
where
  "arbitrage_process Mkt p \<longleftrightarrow> (\<exists> m. (self_financing Mkt p) \<and> (trading_strategy p) \<and>
    (\<forall>w \<in> space M. val_process Mkt p 0 w = 0) \<and>
    (AE w in M. 0 \<le> cls_val_process Mkt p m w) \<and>
    0 < \<P>(w in M. cls_val_process Mkt p m w > 0))"

lemma (in disc_filtr_prob_space) arbitrage_processE:
  assumes "arbitrage_process Mkt p"
  shows "(\<exists> m. (self_financing Mkt p) \<and> (trading_strategy p) \<and>
    (\<forall>w \<in> space M. cls_val_process Mkt p 0 w = 0) \<and>
    (AE w in M. 0 \<le> cls_val_process Mkt p m w) \<and>
    0 < \<P>(w in M. cls_val_process Mkt p m w > 0))"
  using assms disc_filtr_prob_space.arbitrage_process_def disc_filtr_prob_space_axioms self_financingE by fastforce



lemma (in disc_filtr_prob_space) arbitrage_processI:
  assumes "(\<exists> m. (self_financing Mkt p) \<and> (trading_strategy p) \<and>
    (\<forall>w \<in> space M. cls_val_process Mkt p 0 w = 0) \<and>
    (AE w in M. 0 \<le> cls_val_process Mkt p m w) \<and>
    0 < \<P>(w in M. cls_val_process Mkt p m w > 0))"
  shows "arbitrage_process Mkt p" unfolding arbitrage_process_def  using assms
  by (simp add: self_financingE cls_val_process_def)

definition (in disc_filtr_prob_space) viable_market
where
  "viable_market Mkt  \<longleftrightarrow> (\<forall>p. stock_portfolio Mkt p \<longrightarrow> \<not> arbitrage_process Mkt p)"

lemma (in disc_filtr_prob_space) arbitrage_val_process:
  assumes "arbitrage_process Mkt pf1"
  and "self_financing Mkt pf2"
  and "trading_strategy pf2"
  and "\<forall> n w. cls_val_process Mkt pf1 n w = cls_val_process Mkt pf2 n w"
shows "arbitrage_process Mkt pf2"
proof -
  have "(\<exists> m. (self_financing Mkt pf1) \<and> (trading_strategy pf1) \<and>
    (\<forall>w \<in> space M. cls_val_process Mkt pf1 0 w = 0) \<and>
    (AE w in M. 0 \<le> cls_val_process Mkt pf1 m w) \<and>
    0 < \<P>(w in M. cls_val_process Mkt pf1 m w > 0))" using assms arbitrage_processE[of Mkt pf1] by simp
  from this obtain m where "(self_financing Mkt pf1)" and "(trading_strategy pf1)" and
    "(\<forall>w \<in> space M. cls_val_process Mkt pf1 0 w = 0)" and
    "(AE w in M. 0 \<le> cls_val_process Mkt pf1 m w)"
    "0 < \<P>(w in M. cls_val_process Mkt pf1 m w > 0)" by auto
  have ae_eq:"\<forall>w\<in> space M. (cls_val_process Mkt pf1 0 w = 0) = (cls_val_process Mkt pf2 0 w = 0)"
  proof
    fix w
    assume "w\<in> space M"
    show "(cls_val_process Mkt pf1 0 w = 0) = (cls_val_process Mkt pf2 0 w = 0) "
      using  assms  by simp
  qed
  have ae_geq:"almost_everywhere M (\<lambda>w. cls_val_process Mkt pf1 m w \<ge> 0) = almost_everywhere M (\<lambda>w. cls_val_process Mkt pf2 m w \<ge> 0)"
  proof (rule AE_cong)
    fix w
    assume "w\<in> space M"
    show "(cls_val_process Mkt pf1 m w \<ge> 0) = (cls_val_process Mkt pf2 m w \<ge> 0) "
      using  assms by simp
  qed
  have "self_financing Mkt pf2" using assms by simp
  moreover have "trading_strategy pf2" using assms by simp
  moreover have "(\<forall>w \<in> space M. cls_val_process Mkt pf2 0 w = 0)"  using \<open>(\<forall>w \<in> space M. cls_val_process Mkt pf1 0 w = 0)\<close> ae_eq by simp
  moreover have "AE w in M. 0 \<le> cls_val_process Mkt pf2 m w" using \<open>AE w in M. 0 \<le> cls_val_process Mkt pf1 m w\<close> ae_geq by simp
  moreover have "0 < prob {w \<in> space M. 0 < cls_val_process Mkt pf2 m w}"
  proof -
    have "{w \<in> space M. 0 < cls_val_process Mkt pf2 m w} = {w \<in> space M. 0 < cls_val_process Mkt pf1 m w}"
      by (simp add: assms(4))
    thus ?thesis by (simp add: \<open>0 < prob {w \<in> space M. 0 < cls_val_process Mkt pf1 m w}\<close>)
  qed
  ultimately show ?thesis using arbitrage_processI by blast
qed


definition coincides_on where
  "coincides_on Mkt Mkt2 A \<longleftrightarrow> (stocks Mkt = stocks Mkt2 \<and> (\<forall>x. x\<in> A \<longrightarrow> prices Mkt x = prices Mkt2 x))"

lemma coincides_val_process:
  assumes "coincides_on Mkt Mkt2 A"
  and "support_set pf \<subseteq> A"
  shows "\<forall>n w. val_process Mkt pf n w = val_process Mkt2 pf n w"
proof (intro allI)
  fix n w
  show "val_process Mkt pf n w = val_process Mkt2 pf n w"
  proof (cases "portfolio pf")
    case False
    thus ?thesis unfolding val_process_def by simp
  next
    case True
    hence "val_process Mkt pf n w = (\<Sum>x\<in> support_set pf. prices Mkt x n w * pf x (Suc n) w)" using assms
      unfolding val_process_def  by simp
    also have "... = (\<Sum>x\<in> support_set pf. prices Mkt2 x n w * pf x (Suc n) w)"
    proof (rule sum.cong, simp)
      fix y
      assume "y\<in> support_set pf"
      hence "y\<in> A" using assms unfolding  stock_portfolio_def by auto
      hence "prices Mkt y n w = prices Mkt2 y n w" using assms
        unfolding coincides_on_def by auto
      thus "prices Mkt y n w * pf y (Suc n) w = prices Mkt2 y n w * pf y (Suc n) w" by simp
    qed
    also have "... = val_process Mkt2 pf n w"
      by (metis (mono_tags, lifting) calculation val_process_def)
    finally show "val_process Mkt pf n w = val_process Mkt2 pf n w" .
  qed
qed

lemma coincides_cls_val_process':
  assumes "coincides_on Mkt Mkt2 A"
  and "support_set pf \<subseteq> A"
  shows "\<forall>n w. cls_val_process Mkt pf (Suc n) w = cls_val_process Mkt2 pf (Suc n) w"
proof (intro allI)
  fix n w
  show "cls_val_process Mkt pf (Suc n) w = cls_val_process Mkt2 pf (Suc n) w"
  proof (cases "portfolio pf")
    case False
    thus ?thesis unfolding cls_val_process_def by simp
  next
    case True
    hence "cls_val_process Mkt pf (Suc n) w = (\<Sum>x\<in> support_set pf. prices Mkt x (Suc n) w * pf x (Suc n) w)" using assms
      unfolding cls_val_process_def  by simp
    also have "... = (\<Sum>x\<in> support_set pf. prices Mkt2 x (Suc n) w * pf x (Suc n) w)"
    proof (rule sum.cong, simp)
      fix y
      assume "y\<in> support_set pf"
      hence "y\<in> A" using assms unfolding  stock_portfolio_def by auto
      hence "prices Mkt y (Suc n) w = prices Mkt2 y (Suc n) w" using assms
        unfolding coincides_on_def by auto
      thus "prices Mkt y (Suc n) w * pf y (Suc n) w = prices Mkt2 y (Suc n) w * pf y (Suc n) w" by simp
    qed
    also have "... = cls_val_process Mkt2 pf (Suc n) w"
      by (metis (mono_tags, lifting) True  up_cl_proc.simps(2) cls_val_process_def)
    finally show "cls_val_process Mkt pf (Suc n) w = cls_val_process Mkt2 pf (Suc n) w" .
  qed
qed

lemma coincides_cls_val_process:
  assumes "coincides_on Mkt Mkt2 A"
  and "support_set pf \<subseteq> A"
  shows "\<forall>n w. cls_val_process Mkt pf n w = cls_val_process Mkt2 pf n w"
proof (intro allI)
  fix n w
  show "cls_val_process Mkt pf n w = cls_val_process Mkt2 pf n w"
  proof (cases "portfolio pf")
    case False
    thus ?thesis unfolding cls_val_process_def by simp
  next
    case True
    show "cls_val_process Mkt pf n w = cls_val_process Mkt2 pf n w"
    proof (induct n)
      case 0
      with assms show ?case
        by (simp add: cls_val_process_def coincides_val_process)
    next
      case Suc
      thus ?case using coincides_cls_val_process' assms by blast
    qed
  qed
qed


lemma (in disc_filtr_prob_space) coincides_on_self_financing:
  assumes "coincides_on Mkt Mkt2 A"
  and "support_set p \<subseteq> A"
  and "self_financing Mkt p"
shows "self_financing Mkt2 p"
proof -
  have "\<forall> n w. val_process Mkt2 p (Suc n) w = cls_val_process Mkt2 p (Suc n) w"
  proof (intro allI)
    fix n w
    have "val_process Mkt2 p (Suc n) w = val_process Mkt p (Suc n) w"
      using assms(1) assms(2) coincides_val_process stock_portfolio_def by fastforce
    also have "... = cls_val_process Mkt p (Suc n) w" by (metis \<open>self_financing Mkt p\<close> self_financing_def)
    also have "... = cls_val_process Mkt2 p (Suc n) w"
      using assms(1) assms(2) coincides_cls_val_process stock_portfolio_def by blast
    finally show "val_process Mkt2 p (Suc n) w = cls_val_process Mkt2 p (Suc n) w" .
  qed
  thus "self_financing Mkt2 p" unfolding self_financing_def by auto
qed


lemma (in disc_filtr_prob_space) coincides_on_arbitrage:
  assumes "coincides_on Mkt Mkt2 A"
  and "support_set p \<subseteq> A"
  and "arbitrage_process Mkt p"
shows "arbitrage_process Mkt2 p"
proof -
  have "(\<exists> m. (self_financing Mkt p) \<and> (trading_strategy p) \<and>
    (\<forall>w\<in> space M. cls_val_process Mkt p 0 w = 0) \<and>
    (AE w in M. 0 \<le> cls_val_process Mkt p m w) \<and>
    0 < \<P>(w in M. cls_val_process Mkt p m w > 0))" using assms using arbitrage_processE by simp
  from this obtain m where "(self_financing Mkt p)" and "(trading_strategy p)" and
    "(\<forall>w\<in> space M. cls_val_process Mkt p 0 w = 0)" and
    "(AE w in M. 0 \<le> cls_val_process Mkt p m w)"
    "0 < \<P>(w in M. cls_val_process Mkt p m w > 0)" by auto
  have ae_eq:"\<forall>w\<in> space M. (cls_val_process Mkt2 p 0 w = 0) = (cls_val_process Mkt p 0 w = 0)"
  proof
    fix w
    assume "w\<in> space M"
    show "(cls_val_process Mkt2 p 0 w = 0) = (cls_val_process Mkt p 0 w = 0) "
      using  assms coincides_cls_val_process by (metis)
  qed
  have ae_geq:"almost_everywhere M (\<lambda>w. cls_val_process Mkt2 p m w \<ge> 0) = almost_everywhere M (\<lambda>w. cls_val_process Mkt p m w \<ge> 0)"
  proof (rule AE_cong)
    fix w
    assume "w\<in> space M"
    show "(cls_val_process Mkt2 p m w \<ge> 0) = (cls_val_process Mkt p m w \<ge> 0) "
      using  assms coincides_cls_val_process by (metis)
  qed
  have "self_financing Mkt2 p" using assms coincides_on_self_financing
    using \<open>self_financing Mkt p\<close> by blast
  moreover have "trading_strategy p" using \<open>trading_strategy p\<close> .
  moreover have "(\<forall>w\<in> space M. cls_val_process Mkt2 p 0 w = 0)"  using \<open>(\<forall>w\<in> space M. cls_val_process Mkt p 0 w = 0)\<close> ae_eq by simp
  moreover have "AE w in M. 0 \<le> cls_val_process Mkt2 p m w" using \<open>AE w in M. 0 \<le> cls_val_process Mkt p m w\<close> ae_geq by simp
  moreover have "0 < prob {w \<in> space M. 0 < cls_val_process Mkt2 p m w}"
  proof -
    have "{w \<in> space M. 0 < cls_val_process Mkt2 p m w} = {w \<in> space M. 0 < cls_val_process Mkt p m w}"
      by (metis (no_types, lifting) assms(1) assms(2) coincides_cls_val_process)
    thus ?thesis by (simp add: \<open>0 < prob {w \<in> space M. 0 < cls_val_process Mkt p m w}\<close>)
  qed
  ultimately show ?thesis using arbitrage_processI by blast
qed


lemma (in disc_filtr_prob_space) coincides_on_stocks_viable:
  assumes "coincides_on Mkt Mkt2 (stocks Mkt)"
  and "viable_market Mkt"
shows "viable_market Mkt2" using coincides_on_arbitrage
  by (metis (mono_tags, hide_lams) assms(1) assms(2) coincides_on_def stock_portfolio_def viable_market_def)


lemma coincides_stocks_val_process:
  assumes "stock_portfolio Mkt pf"
  and "coincides_on Mkt Mkt2 (stocks Mkt)"
shows "\<forall>n w. val_process Mkt pf n w = val_process Mkt2 pf n w" using assms  unfolding stock_portfolio_def
  by (simp add: coincides_val_process)

lemma coincides_stocks_cls_val_process:
  assumes "stock_portfolio Mkt pf"
  and "coincides_on Mkt Mkt2 (stocks Mkt)"
shows "\<forall>n w. cls_val_process Mkt pf n w = cls_val_process Mkt2 pf n w" using assms  unfolding stock_portfolio_def
    by (simp add: coincides_cls_val_process)

lemma (in disc_filtr_prob_space) coincides_on_adapted_val_process:
  assumes "coincides_on Mkt Mkt2 A"
  and "support_set p \<subseteq> A"
  and "borel_adapt_stoch_proc F (val_process Mkt p)"
shows "borel_adapt_stoch_proc F (val_process Mkt2 p)" unfolding adapt_stoch_proc_def
proof
  fix n
  have "val_process Mkt p n \<in> borel_measurable (F n)" using assms unfolding adapt_stoch_proc_def by simp
  moreover have "\<forall>w. val_process Mkt p n w = val_process Mkt2 p n w" using assms coincides_val_process[of Mkt Mkt2 A]
    by auto
  thus "val_process Mkt2 p n \<in> borel_measurable (F n)"
    using calculation by presburger
qed

lemma (in disc_filtr_prob_space) coincides_on_adapted_cls_val_process:
  assumes "coincides_on Mkt Mkt2 A"
  and "support_set p \<subseteq> A"
  and "borel_adapt_stoch_proc F (cls_val_process Mkt p)"
shows "borel_adapt_stoch_proc F (cls_val_process Mkt2 p)" unfolding adapt_stoch_proc_def
proof
  fix n
  have "cls_val_process Mkt p n \<in> borel_measurable (F n)" using assms unfolding adapt_stoch_proc_def by simp
  moreover have "\<forall>w. cls_val_process Mkt p n w = cls_val_process Mkt2 p n w" using assms coincides_cls_val_process[of Mkt Mkt2 A]
    by auto
  thus "cls_val_process Mkt2 p n \<in> borel_measurable (F n)"
    using calculation by presburger
qed

subsubsection \<open>Fair prices\<close>
definition (in disc_filtr_prob_space) fair_price where
  "fair_price Mkt \<pi> pyf matur \<longleftrightarrow>
    (\<exists> pr. price_structure pyf matur \<pi> pr \<and>
    (\<forall> x Mkt2 p. (x\<notin> stocks Mkt \<longrightarrow>
      ((coincides_on Mkt Mkt2 (stocks Mkt)) \<and> (prices Mkt2 x = pr) \<and> portfolio p \<and> support_set p \<subseteq> stocks Mkt \<union> {x} \<longrightarrow>
        \<not> arbitrage_process Mkt2 p))))"



lemma (in disc_filtr_prob_space) fair_priceI:
  assumes "fair_price Mkt \<pi> pyf matur"
  shows "(\<exists> pr. price_structure pyf matur \<pi> pr \<and>
    (\<forall> x. (x\<notin> stocks Mkt \<longrightarrow>
      (\<forall> Mkt2 p. (coincides_on Mkt Mkt2 (stocks Mkt)) \<and> (prices Mkt2 x = pr) \<and> portfolio p \<and> support_set p \<subseteq> stocks Mkt \<union> {x} \<longrightarrow>
        \<not> arbitrage_process Mkt2 p))))" using assms unfolding fair_price_def by simp

paragraph \<open>Existence when replicating portfolio\<close>


lemma (in disc_equity_market) replicating_fair_price:
  assumes "viable_market Mkt"
  and "replicating_portfolio pf der matur"
and "support_adapt Mkt pf"
shows "fair_price Mkt (initial_value pf) der matur"
proof (rule ccontr)
  define \<pi> where  "\<pi> = (initial_value pf)"
  assume "\<not> fair_price Mkt \<pi> der matur"
  hence imps: "\<forall>pr. (price_structure der matur \<pi> pr) \<longrightarrow>  (\<exists> x Mkt2 p. (x\<notin> stocks Mkt \<and>
    (coincides_on Mkt Mkt2 (stocks Mkt)) \<and> (prices Mkt2 x = pr) \<and> portfolio p \<and> support_set p \<subseteq> stocks Mkt \<union> {x} \<and>
     arbitrage_process Mkt2 p))" unfolding fair_price_def by simp
  have "(price_structure der matur \<pi> (cls_val_process Mkt pf))" unfolding \<pi>_def  using replicating_price_process assms by simp
  hence "\<exists> x Mkt2 p. (x\<notin> stocks Mkt \<and>
    (coincides_on Mkt Mkt2 (stocks Mkt)) \<and> (prices Mkt2 x = (cls_val_process Mkt pf)) \<and> portfolio p \<and> support_set p \<subseteq> stocks Mkt \<union> {x} \<and>
     arbitrage_process Mkt2 p)" using imps by simp
  from this obtain x Mkt2 p where "x\<notin> stocks Mkt" and "coincides_on Mkt Mkt2 (stocks Mkt)" and "prices Mkt2 x = cls_val_process Mkt pf"
    and "portfolio p" and "support_set p\<subseteq> stocks Mkt \<union> {x}" and "arbitrage_process Mkt2 p" by auto
  have "\<forall>n w. cls_val_process Mkt pf n w = cls_val_process Mkt2 pf n w"
    using coincides_stocks_cls_val_process[of Mkt pf Mkt2] assms \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close>  unfolding replicating_portfolio_def
    by simp
  have "\<exists>m. self_financing Mkt2 p \<and>
      trading_strategy p \<and>
      (AE w in M. cls_val_process Mkt2 p 0 w = 0) \<and>
      (AE w in M. 0 \<le> cls_val_process Mkt2 p m w) \<and> 0 < prob {w \<in> space M. 0 < cls_val_process Mkt2 p m w}"
    using \<open>arbitrage_process Mkt2 p\<close> using arbitrage_processE[of Mkt2] by simp
  from this obtain m where "self_financing Mkt2 p"
      "trading_strategy p \<and>
      (AE w in M. cls_val_process Mkt2 p 0 w = 0) \<and>
      (AE w in M. 0 \<le> cls_val_process Mkt2 p m w) \<and> 0 < prob {w \<in> space M. 0 < cls_val_process Mkt2 p m w}" by auto note mprop = this
  define eq_stock where "eq_stock = qty_replace_comp p x pf"
  have "\<forall>n w. cls_val_process Mkt pf n w = cls_val_process Mkt2 pf n w" using assms unfolding replicating_portfolio_def
      using coincides_cls_val_process
      using \<open>\<forall>n w. cls_val_process Mkt pf n w = cls_val_process Mkt2 pf n w\<close> by blast
    hence prx: "\<forall>n w. prices Mkt2 x n w = cls_val_process Mkt2 pf n w" using \<open>prices Mkt2 x = cls_val_process Mkt pf\<close> by simp
  have "stock_portfolio Mkt2 eq_stock"
    by (metis (no_types, lifting) \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> \<open>portfolio p\<close> \<open>support_set p \<subseteq> stocks Mkt \<union> {x}\<close>
        assms(2) coincides_on_def disc_equity_market.replicating_portfolio_def disc_equity_market_axioms eq_stock_def
        replace_comp_portfolio replace_comp_stocks stock_portfolio_def)
  moreover have "arbitrage_process Mkt2 eq_stock"
  proof (rule arbitrage_val_process)
    show "arbitrage_process Mkt2 p" using \<open>arbitrage_process Mkt2 p\<close> .
    show vp: "\<forall>n w. cls_val_process Mkt2 p n w = cls_val_process Mkt2 eq_stock n w" using replace_comp_cls_val_process
        \<open>prices Mkt2 x = cls_val_process Mkt pf\<close> unfolding eq_stock_def
      by (metis (no_types, lifting) \<open>\<forall>n w. cls_val_process Mkt pf n w = cls_val_process Mkt2 pf n w\<close> \<open>portfolio p\<close> assms(2) replicating_portfolio_def
          stock_portfolio_def)
    show "trading_strategy eq_stock"
      by (metis \<open>arbitrage_process Mkt2 p\<close> arbitrage_process_def assms(2) eq_stock_def
          replace_comp_trading_strat replicating_portfolio_def)
    show "self_financing Mkt2 eq_stock" unfolding eq_stock_def
    proof (rule replace_comp_self_financing)
      show "portfolio pf" using assms unfolding replicating_portfolio_def stock_portfolio_def by simp
      show "portfolio p" using \<open>portfolio p\<close> .
      show "\<forall>n w. prices Mkt2 x n w = cls_val_process Mkt2 pf n w" using prx .
      show "self_financing Mkt2 p" using \<open>self_financing Mkt2 p\<close> .
      show "self_financing Mkt2 pf" using coincides_on_self_financing[of Mkt Mkt2 "stocks Mkt" pf]
        \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> assms(2) (*disc_equity_market.replicating_portfolio_def
          disc_equity_market_axioms*) unfolding stock_portfolio_def replicating_portfolio_def by auto
    qed
  qed
  moreover have "viable_market Mkt2" using assms coincides_on_stocks_viable[of Mkt Mkt2]
    by (simp add: \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close>)
  ultimately show False unfolding viable_market_def by simp
qed


paragraph \<open>Uniqueness when replicating portfolio\<close>


text \<open>The proof of uniqueness requires the existence of a stock that always takes strictly positive values.\<close>


locale disc_market_pos_stock = disc_equity_market +
  fixes pos_stock
  assumes in_stock: "pos_stock \<in> stocks Mkt"
  and positive: "\<forall> n w. prices Mkt pos_stock n w > 0"
and readable: "\<forall> asset\<in> stocks Mkt. borel_adapt_stoch_proc F (prices Mkt asset)"




lemma (in disc_market_pos_stock) pos_stock_borel_adapted:
  shows "borel_adapt_stoch_proc F (prices Mkt pos_stock)"
  using assets_def readable in_stock  by auto


definition static_quantities where
  "static_quantities p \<longleftrightarrow> (\<forall>asset \<in> support_set p. \<exists>c::real. p asset = (\<lambda> n w. c))"

lemma (in disc_filtr_prob_space) static_quantities_trading_strat:
  assumes "static_quantities p"
  and "finite (support_set p)"
  shows "trading_strategy p" unfolding trading_strategy_def
proof (intro conjI ballI)
  show "portfolio p" using assms unfolding portfolio_def by simp
  fix asset
  assume "asset \<in> support_set p"
  hence "\<exists>c. p asset = (\<lambda> n w. c)" using assms unfolding static_quantities_def by simp
  then obtain c where "p asset = (\<lambda> n w. c)" by auto
  show "borel_predict_stoch_proc F (p asset)" unfolding predict_stoch_proc_def
  proof (intro conjI)
    show "p asset 0 \<in> borel_measurable (F 0)" using \<open>p asset = (\<lambda> n w. c)\<close> by simp
    show "\<forall>n. p asset (Suc n) \<in> borel_measurable (F n)"
    proof
    fix n
      have "p asset (Suc n) = (\<lambda> w. c)" using \<open>p asset = (\<lambda> n w. c)\<close> by simp
      thus "p asset (Suc n) \<in> borel_measurable (F n)" by simp
    qed
  qed
qed



lemma two_component_support_set:
  assumes "\<exists> n w. a n w \<noteq> 0"
  and "\<exists> n w. b n w\<noteq> 0"
  and "x \<noteq> y"
shows "support_set ((\<lambda> (x::'b) (n::nat) (w::'a). 0::real)(x:= a, y:= b)) = {x,y}"
proof
  let ?arb_pf = "(\<lambda> (x::'b) (n::nat) (w::'a). 0::real)(x:= a, y:= b)"
  have "\<exists> n w. ?arb_pf x n w \<noteq> 0" using assms by simp
  moreover have "\<exists>n w. ?arb_pf y n w \<noteq> 0" using assms by simp
  ultimately show "{x, y} \<subseteq> support_set ?arb_pf" unfolding support_set_def by simp
  show "support_set ?arb_pf \<subseteq> {x, y}"
  proof (rule ccontr)
    assume "\<not> support_set ?arb_pf \<subseteq> {x, y}"
    hence "\<exists>z. z\<in> support_set ?arb_pf \<and> z\<notin> {x, y}" by auto
    from this obtain z where "z\<in> support_set ?arb_pf" and "z\<notin> {x, y}" by auto
    have "\<exists>n w. ?arb_pf z n w \<noteq> 0" using \<open>z\<in> support_set ?arb_pf\<close> unfolding support_set_def by simp
    from this obtain n w where "?arb_pf z n w \<noteq> 0" by auto
    have "?arb_pf z n w = 0" using \<open>z\<notin> {x, y}\<close>  by simp
    thus False using \<open>?arb_pf z n w \<noteq> 0\<close> by simp
  qed
qed

lemma two_component_val_process:
  assumes "arb_pf = ((\<lambda> (x::'b) (n::nat) (w::'a). 0::real)(x:= a, y:= b))"
  and "portfolio arb_pf"
  and "x \<noteq> y"
  and "\<exists> n w. a n w \<noteq> 0"
  and "\<exists> n w. b n w\<noteq> 0"
  shows "val_process Mkt arb_pf n w =
    prices Mkt y n w * b (Suc n) w + prices Mkt x n w * a (Suc n) w"
proof -
  have "support_set arb_pf = {x,y}" using assms by (simp add:two_component_support_set)
  have "val_process Mkt arb_pf n w = (\<Sum>x\<in>support_set arb_pf. prices Mkt x n w * arb_pf x (Suc n) w)"
        unfolding val_process_def using \<open>portfolio arb_pf\<close> by simp
  also have "... = (\<Sum>x\<in>{x, y}. prices Mkt x n w * arb_pf x (Suc n) w)" using \<open>support_set arb_pf = {x, y}\<close>
        by simp
  also have "... = (\<Sum>x\<in>{y}. prices Mkt x n w * arb_pf x (Suc n) w) + prices Mkt x n w * arb_pf x (Suc n) w"
        using sum.insert[of "{y}" x  "\<lambda>x. prices Mkt x n w * arb_pf x n w"] assms(3) by auto
  also have "... = prices Mkt y n w * arb_pf y (Suc n) w + prices Mkt x n w * arb_pf x (Suc n) w" by simp
  also have "... = prices Mkt y n w * b (Suc n) w + prices Mkt x n w * a (Suc n) w" using assms by auto
  finally show "val_process Mkt arb_pf n w = prices Mkt y n w * b (Suc n) w + prices Mkt x n w * a (Suc n) w" .
qed

lemma quantity_update_support_set:
  assumes "\<exists>n w. pr n w \<noteq> 0"
  and "x\<notin> support_set p"
shows "support_set (p(x:=pr)) = support_set p \<union> {x}"
proof
  show "support_set (p(x := pr)) \<subseteq> support_set p \<union> {x}"
  proof
    fix y
    assume "y\<in> support_set (p(x := pr))"
    show "y \<in> support_set p \<union> {x}"
    proof (rule ccontr)
      assume "\<not>y \<in> support_set p \<union> {x}"
      hence "y \<noteq> x" by simp
      have "\<exists>n w. (p(x := pr)) y n w \<noteq> 0" using \<open>y\<in> support_set (p(x := pr))\<close> unfolding support_set_def by simp
      then obtain n w where nwprop: "(p(x := pr)) y n w \<noteq> 0" by auto
      have "y\<notin> support_set p" using \<open>\<not>y \<in> support_set p \<union> {x}\<close> by simp
      hence "y = x" using nwprop using support_set_def by force
      thus False using \<open>y\<noteq> x\<close> by simp
    qed
  qed
  show "support_set p \<union> {x} \<subseteq> support_set (p(x := pr))"
  proof
    fix y
    assume "y \<in> support_set p \<union> {x}"
    show "y\<in> support_set (p(x := pr))"
    proof (cases "y\<in> support_set p")
      case True
      thus ?thesis
      proof -
        have f1: "y \<in> {b. \<exists>n a. p b n a \<noteq> 0}"
          by (metis True support_set_def)
        then have "y \<noteq> x"
          using assms(2) support_set_def by force
        then show ?thesis
          using f1 by (simp add: support_set_def)
      qed
    next
      case False
      hence "y = x" using \<open>y \<in> support_set p \<union> {x}\<close> by auto
      thus ?thesis using assms by (simp add: support_set_def)
    qed
  qed
qed


lemma fix_asset_price:
  shows "\<exists>x Mkt2. x \<notin> stocks Mkt \<and>
  coincides_on Mkt Mkt2 (stocks Mkt) \<and>
  prices Mkt2 x = pr"
proof -
  have "\<exists>x. x\<notin> stocks Mkt" by (metis UNIV_eq_I stk_strict_subs_def mkt_stocks_assets)
  from this obtain x where "x\<notin> stocks Mkt" by auto
  let ?res = "discrete_market_of (stocks Mkt) ((prices Mkt)(x:=pr))"
  have "coincides_on Mkt ?res (stocks Mkt)"
  proof -
    have "stocks Mkt = stocks (discrete_market_of (stocks Mkt) ((prices Mkt)(x := pr)))"
      by (metis (no_types) stk_strict_subs_def mkt_stocks_assets stocks_of)
    then show ?thesis
      by (simp add: \<open>x \<notin> stocks Mkt\<close> coincides_on_def prices_of)
  qed
  have "prices ?res x = pr" by (simp add: prices_of)
 show ?thesis
   using \<open>coincides_on Mkt (discrete_market_of (stocks Mkt) ((prices Mkt)(x := pr))) (stocks Mkt)\<close> \<open>prices (discrete_market_of (stocks Mkt) ((prices Mkt)(x := pr))) x = pr\<close> \<open>x \<notin> stocks Mkt\<close> by blast
qed



lemma (in disc_market_pos_stock) arbitrage_portfolio_properties:
  assumes "price_structure der matur \<pi> pr"
  and "replicating_portfolio pf der matur"
  and  "(coincides_on Mkt Mkt2 (stocks Mkt))"
  and "(prices Mkt2 x = pr)"
  and "x\<notin> stocks Mkt"
  and "diff_inv = (\<pi> - initial_value pf) / constant_image (prices Mkt pos_stock 0)"
  and "diff_inv \<noteq> 0"
  and "arb_pf = (\<lambda> (x::'b) (n::nat) (w::'a). 0::real)(x:= (\<lambda> n w. -1), pos_stock := (\<lambda> n w. diff_inv))"
  and "contr_pf = qty_sum arb_pf pf"
shows "self_financing Mkt2 contr_pf"
  and "trading_strategy contr_pf"
  and "\<forall>w\<in> space M. cls_val_process Mkt2 contr_pf 0 w = 0"
  and "0 < diff_inv \<longrightarrow> (AE w in M. 0 < cls_val_process Mkt2 contr_pf matur w)"
  and "diff_inv < 0 \<longrightarrow> (AE w in M. 0 > cls_val_process Mkt2 contr_pf matur w)"
  and "support_set arb_pf = {x, pos_stock}"
  and "portfolio contr_pf"
proof -
  have "0 < constant_image (prices Mkt pos_stock 0)" using trading_strategy_init
  proof -
    have "borel_adapt_stoch_proc F (prices Mkt pos_stock)" using pos_stock_borel_adapted by simp
    hence "\<exists>c. \<forall>w\<in>space M. prices Mkt pos_stock 0 w = c" using  adapted_init[of "prices Mkt pos_stock"] by simp
    moreover have "\<forall>w\<in> space M. 0 < prices Mkt pos_stock 0 w" using positive by simp
    ultimately show ?thesis using constant_image_pos by simp
  qed
  show "support_set arb_pf = {x, pos_stock}"
  proof -
    have "arb_pf = (\<lambda> (x::'b) (n::nat) (w::'a). 0::real)(x:= (\<lambda> n w. -1), pos_stock := (\<lambda> n w. diff_inv))"
      using \<open>arb_pf = (\<lambda> (x::'b) (n::nat) (w::'a). 0::real)(x:= (\<lambda> n w. -1), pos_stock := (\<lambda> n w. diff_inv))\<close> .
    moreover have "\<exists>n w. diff_inv \<noteq> 0" using assms by simp
    moreover have "x\<noteq> pos_stock" using \<open>x \<notin> stocks Mkt\<close> in_stock by auto
    ultimately show ?thesis by (simp add:two_component_support_set)
  qed
  hence "portfolio arb_pf" unfolding portfolio_def by simp
  have arb_vp:"\<forall>n w. val_process Mkt2 arb_pf n w = prices Mkt2 pos_stock n w * diff_inv - pr n w"
  proof (intro allI)
    fix n w
    have "val_process Mkt2 arb_pf n w = prices Mkt2 pos_stock n w * (\<lambda> n w. diff_inv) n w + prices Mkt2 x n w * (\<lambda> n w. -1) n w"
    proof (rule two_component_val_process)
      show "x\<noteq> pos_stock" using \<open>x \<notin> stocks Mkt\<close> in_stock by auto
      show "arb_pf = (\<lambda>x n w. 0)(x := \<lambda>a b. - 1, pos_stock := \<lambda>a b. diff_inv)" using assms by simp
      show "portfolio arb_pf" using \<open>portfolio arb_pf\<close> by simp
      show "\<exists>n w. - (1::real) \<noteq> 0" by simp
      show "\<exists>n w. diff_inv \<noteq> 0" using assms by auto
    qed
    also have "... = prices Mkt2 pos_stock n w * diff_inv - pr n w" using \<open>prices Mkt2 x = pr\<close> by simp
    finally show "val_process Mkt2 arb_pf n w = prices Mkt2 pos_stock n w * diff_inv - pr n w" .
  qed
  have "static_quantities arb_pf" unfolding static_quantities_def
  proof
    fix asset
    assume "asset \<in> support_set arb_pf"
    thus "\<exists>c. arb_pf asset = (\<lambda>n w. c)"
    proof (cases "asset = x")
      case True
      thus ?thesis using assms by auto
    next
      case False
      hence "asset = pos_stock" using \<open>support_set arb_pf = {x, pos_stock}\<close>
        using \<open>asset \<in> support_set arb_pf\<close> by blast
      thus ?thesis using assms by auto
    qed
  qed
  hence "trading_strategy arb_pf"
    using \<open>portfolio arb_pf\<close> portfolio_def static_quantities_trading_strat by blast
  have "self_financing Mkt2 arb_pf"
        by (simp add: static_portfolio_self_financing \<open>arb_pf = (\<lambda>x n w. 0) (x := \<lambda>n w. -1, pos_stock := \<lambda>n w. diff_inv)\<close>)
  hence arb_uvp: "\<forall>n w. cls_val_process Mkt2 arb_pf n w = prices Mkt2 pos_stock n w * diff_inv - pr n w" using assms arb_vp
    by (simp add:self_financingE)
  show "portfolio contr_pf" using assms
      by (metis \<open>support_set arb_pf = {x, pos_stock}\<close> replicating_portfolio_def
          finite.emptyI finite.insertI portfolio_def stock_portfolio_def sum_portfolio)
  have "support_set contr_pf \<subseteq> stocks Mkt \<union> {x}"
  proof -
    have "support_set contr_pf \<subseteq> support_set arb_pf \<union> support_set pf" using assms
      by (simp add:sum_support_set)
    moreover have "support_set arb_pf \<subseteq> stocks Mkt \<union> {x}" using \<open>support_set arb_pf = {x, pos_stock}\<close> in_stock by simp
    moreover have "support_set pf \<subseteq> stocks Mkt \<union> {x}" using assms unfolding replicating_portfolio_def
      stock_portfolio_def by auto
    ultimately show ?thesis by auto
  qed
  show "self_financing Mkt2 contr_pf"
    proof -
    have "self_financing Mkt2 (qty_sum arb_pf pf)"
    proof (rule sum_self_financing)
      show "portfolio arb_pf"  using  \<open>support_set arb_pf = {x, pos_stock}\<close> unfolding portfolio_def by auto
      show "portfolio pf" using assms unfolding replicating_portfolio_def stock_portfolio_def by auto
      show "self_financing Mkt2 pf" using coincides_on_self_financing
        \<open>(coincides_on Mkt Mkt2 (stocks Mkt))\<close> \<open>(prices Mkt2 x = pr)\<close> assms(2)
        unfolding replicating_portfolio_def stock_portfolio_def  by blast
      show "self_financing Mkt2 arb_pf"
        by (simp add: static_portfolio_self_financing \<open>arb_pf = (\<lambda>x n w. 0) (x := \<lambda>n w. -1, pos_stock := \<lambda>n w. diff_inv)\<close>)
    qed
    thus ?thesis using assms by simp
  qed
  show "trading_strategy contr_pf"
  proof -
    have "trading_strategy (qty_sum arb_pf pf)"
    proof (rule sum_trading_strat)
      show "trading_strategy pf" using assms unfolding replicating_portfolio_def by simp
      show "trading_strategy arb_pf" using \<open>trading_strategy arb_pf\<close> .
    qed
    thus ?thesis using assms by simp
  qed
  show "\<forall>w\<in> space M. cls_val_process Mkt2 contr_pf 0 w = 0"
  proof
    fix w
    assume "w\<in> space M"
    have "cls_val_process Mkt2 contr_pf 0 w = cls_val_process Mkt2 arb_pf 0 w + cls_val_process Mkt2 pf 0 w"
      using sum_cls_val_process0[of arb_pf pf Mkt2]
      using \<open>portfolio arb_pf\<close> assms replicating_portfolio_def stock_portfolio_def by blast
    also have "... = prices Mkt2 pos_stock 0 w * diff_inv - pr 0 w + cls_val_process Mkt2 pf 0 w" using arb_uvp by simp
    also have "... = constant_image (prices Mkt pos_stock 0) * diff_inv - pr 0 w + cls_val_process Mkt2 pf 0 w"
    proof -
      have f1: "prices Mkt pos_stock = prices Mkt2 pos_stock"
        using \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close>  in_stock unfolding coincides_on_def by blast
      have "prices Mkt pos_stock 0 w = constant_image (prices Mkt pos_stock 0)"
        using \<open>w \<in> space M\<close> adapted_init constant_imageI pos_stock_borel_adapted by blast
      then show ?thesis
        using f1 by simp
    qed
    also have "... = (\<pi> - initial_value pf) - pr 0 w + cls_val_process Mkt2 pf 0 w"
      using \<open>0 < constant_image (prices Mkt pos_stock 0)\<close> assms by simp
    also have "... = (\<pi> - initial_value pf) - \<pi> + cls_val_process Mkt2 pf 0 w" using \<open>price_structure der matur \<pi> pr\<close>
      price_structure_init[of der matur \<pi> pr] by (simp add: \<open>w \<in> space M\<close>)
    also have "... = (\<pi> - initial_value pf) - \<pi> + (initial_value pf)" using initial_valueI assms unfolding replicating_portfolio_def
      using \<open>w \<in> space M\<close> coincides_stocks_cls_val_process self_financingE readable
      by (metis (no_types, hide_lams) support_adapt_def stock_portfolio_def subsetCE)
    also have "... = 0" by simp
    finally show "cls_val_process Mkt2 contr_pf 0 w = 0" .
  qed
  show "0 < diff_inv \<longrightarrow> (AE w in M. 0 < cls_val_process Mkt2 contr_pf matur w)"
  proof
    assume "0 < diff_inv"
    show "AE w in M. 0 < cls_val_process Mkt2 contr_pf matur w"
    proof (rule AE_mp)
      have "AE w in M. prices Mkt2 x matur w = der w" using \<open>price_structure der matur \<pi> pr\<close> \<open>prices Mkt2 x = pr\<close>
        unfolding price_structure_def by auto
      moreover have "AE w in M. cls_val_process Mkt2 pf matur  w = der w" using assms coincides_stocks_cls_val_process[of Mkt pf Mkt2]
        \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> unfolding replicating_portfolio_def by auto
      ultimately show "AE w in M. prices Mkt2 x matur w = cls_val_process Mkt2 pf matur w" by auto
      show "AE w in M. prices Mkt2 x matur w = cls_val_process Mkt2 pf matur w \<longrightarrow> 0 < cls_val_process Mkt2 contr_pf matur w"
      proof (rule AE_I2, rule impI)
        fix w
        assume "w\<in> space M"
        and "prices Mkt2 x matur w = cls_val_process Mkt2 pf matur w"
        have "cls_val_process Mkt2 contr_pf matur w = cls_val_process Mkt2 arb_pf matur w + cls_val_process Mkt2 pf matur w"
          using sum_cls_val_process[of arb_pf pf Mkt2]
          \<open>portfolio arb_pf\<close> assms replicating_portfolio_def stock_portfolio_def by blast
        also have "... = prices Mkt2 pos_stock matur w * diff_inv - pr matur w + cls_val_process Mkt2 pf matur w"
          using arb_uvp by simp
        also have "... = prices Mkt2 pos_stock matur w * diff_inv - prices Mkt2 x matur w + cls_val_process Mkt2 pf matur w"
          using \<open>prices Mkt2 x = pr\<close> by simp
        also have "... = prices Mkt2 pos_stock matur w * diff_inv" using \<open>prices Mkt2 x matur w = cls_val_process Mkt2 pf matur w\<close>
          by simp
        also have "... > 0" using positive \<open>0 < diff_inv\<close>
          by (metis \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> coincides_on_def in_stock mult_pos_pos)
        finally have "cls_val_process Mkt2 contr_pf matur w > 0".
        thus "0 < cls_val_process Mkt2 contr_pf matur w" by simp
      qed
    qed
  qed
  show "diff_inv < 0 \<longrightarrow> (AE w in M. 0 > cls_val_process Mkt2 contr_pf matur w)"
  proof
    assume "diff_inv < 0"
    show "AE w in M. 0 > cls_val_process Mkt2 contr_pf matur w"
    proof (rule AE_mp)
      have "AE w in M. prices Mkt2 x matur w = der w" using \<open>price_structure der matur \<pi> pr\<close> \<open>prices Mkt2 x = pr\<close>
        unfolding price_structure_def by auto
      moreover have "AE w in M. cls_val_process Mkt2 pf matur  w = der w" using assms coincides_stocks_cls_val_process[of Mkt pf Mkt2]
        \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> unfolding replicating_portfolio_def by auto
      ultimately show "AE w in M. prices Mkt2 x matur w = cls_val_process Mkt2 pf matur w" by auto
      show "AE w in M. prices Mkt2 x matur w = cls_val_process Mkt2 pf matur w \<longrightarrow> 0 > cls_val_process Mkt2 contr_pf matur w"
      proof (rule AE_I2, rule impI)
        fix w
        assume "w\<in> space M"
        and "prices Mkt2 x matur w = cls_val_process Mkt2 pf matur w"
        have "cls_val_process Mkt2 contr_pf matur w = cls_val_process Mkt2 arb_pf matur w + cls_val_process Mkt2 pf matur w"
          using sum_cls_val_process[of arb_pf pf Mkt2]
          \<open>portfolio arb_pf\<close> assms replicating_portfolio_def stock_portfolio_def by blast
        also have "... = prices Mkt2 pos_stock matur w * diff_inv - pr matur w + cls_val_process Mkt2 pf matur w"
          using arb_uvp by simp
        also have "... = prices Mkt2 pos_stock matur w * diff_inv - prices Mkt2 x matur w + cls_val_process Mkt2 pf matur w"
          using \<open>prices Mkt2 x = pr\<close> by simp
        also have "... = prices Mkt2 pos_stock matur w * diff_inv" using \<open>prices Mkt2 x matur w = cls_val_process Mkt2 pf matur w\<close>
          by simp
        also have "... < 0" using positive \<open>diff_inv < 0\<close>
          by (metis \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> coincides_on_def in_stock mult_pos_neg)
        finally have "cls_val_process Mkt2 contr_pf matur w < 0".
        thus "0 > cls_val_process Mkt2 contr_pf matur w" by simp
      qed
    qed
  qed
qed

lemma (in disc_equity_market) mult_comp_cls_val_process_measurable':
  assumes "cls_val_process Mkt2 pf n \<in>borel_measurable (F n)"
  and "portfolio pf"
  and "qty n \<in> borel_measurable (F n)"
  and "0 \<noteq> n"
shows "cls_val_process Mkt2 (qty_mult_comp pf qty) n \<in> borel_measurable (F n)"
proof -
  have "\<exists>m. n = Suc m" using assms by presburger
  from this obtain m where "n = Suc m" by auto
  hence "cls_val_process Mkt2 (qty_mult_comp pf qty) (Suc m) \<in> borel_measurable (F (Suc m))"
    using  mult_comp_cls_val_process_Suc[of pf Mkt2 qty] borel_measurable_times[of "cls_val_process Mkt2 pf (Suc m)" "F (Suc m)" "qty (Suc m)"]
      assms \<open>n= Suc m\<close> by presburger
  thus ?thesis using \<open>n = Suc m\<close> by simp
qed


lemma (in disc_equity_market) mult_comp_cls_val_process_measurable:
  assumes "\<forall>n. cls_val_process Mkt2 pf n \<in>borel_measurable (F n)"
  and "portfolio pf"
  and "\<forall>n. qty (Suc n) \<in> borel_measurable (F n)"
shows "\<forall>n. cls_val_process Mkt2 (qty_mult_comp pf qty) n \<in> borel_measurable (F n)"
proof
  fix n
  show "cls_val_process Mkt2 (qty_mult_comp pf qty) n \<in> borel_measurable (F n)"
  proof (cases "n=0")
    case False
    hence "\<exists>m. n = Suc m" by presburger
    from this obtain m where "n = Suc m" by auto
    have "qty n \<in> borel_measurable (F n)"
    using Suc_n_not_le_n \<open>n = Suc m\<close> assms(3) increasing_measurable_info nat_le_linear by blast
    hence "qty (Suc m) \<in> borel_measurable (F (Suc m))" using \<open>n = Suc m\<close> by simp
    hence "cls_val_process Mkt2 (qty_mult_comp pf qty) (Suc m) \<in> borel_measurable (F (Suc m))"
      using  mult_comp_cls_val_process_Suc[of pf Mkt2 qty] borel_measurable_times[of "cls_val_process Mkt2 pf (Suc m)" "F (Suc m)" "qty (Suc m)"]
        assms \<open>n= Suc m\<close> by presburger
    thus ?thesis using \<open>n = Suc m\<close> by simp
  next
    case True
    have "qty (Suc 0) \<in> borel_measurable (F 0)" using assms by simp
    moreover have "cls_val_process Mkt2 pf 0 \<in> borel_measurable (F 0)" using assms  by simp
    ultimately have "(\<lambda>w. cls_val_process Mkt2 pf 0 w * qty (Suc 0) w) \<in> borel_measurable (F 0)" by simp
    thus ?thesis using assms(2) True mult_comp_cls_val_process0
      by (simp add: \<open>(\<lambda>w. cls_val_process Mkt2 pf 0 w * qty (Suc 0) w) \<in> borel_measurable (F 0)\<close> mult_comp_cls_val_process0 measurable_cong)
  qed
qed





lemma (in disc_equity_market) mult_comp_val_process_measurable:
  assumes "val_process Mkt2 pf n \<in>borel_measurable (F n)"
  and "portfolio pf"
  and "qty (Suc n) \<in> borel_measurable (F n)"
shows "val_process Mkt2 (qty_mult_comp pf qty) n \<in> borel_measurable (F n)"
  using  mult_comp_val_process[of pf Mkt2 qty] borel_measurable_times[of "val_process Mkt2 pf n" "F n" "qty (Suc n)"]
  assms by presburger

lemma (in disc_market_pos_stock) repl_fair_price_unique:
  assumes "replicating_portfolio pf der matur"
  and "fair_price Mkt \<pi> der matur"
shows "\<pi> = initial_value pf"
proof -
  have expr: "(\<exists> pr. price_structure der matur \<pi> pr \<and>
    (\<forall> x. (x\<notin> stocks Mkt \<longrightarrow>
      (\<forall> Mkt2 p. (coincides_on Mkt Mkt2 (stocks Mkt)) \<and> (prices Mkt2 x = pr) \<and> portfolio p \<and> support_set p \<subseteq> stocks Mkt \<union> {x} \<longrightarrow>
        \<not> arbitrage_process Mkt2 p))))" using assms fair_priceI by simp
  then obtain pr where "price_structure der matur \<pi> pr" and
    xasset: "(\<forall> x. (x\<notin> stocks Mkt \<longrightarrow>
      (\<forall> Mkt2 p. (coincides_on Mkt Mkt2 (stocks Mkt)) \<and> (prices Mkt2 x = pr) \<and> portfolio p \<and> support_set p \<subseteq> stocks Mkt \<union> {x} \<longrightarrow>
        \<not> arbitrage_process Mkt2 p)))" by auto
  define diff_inv where "diff_inv = (\<pi> - initial_value pf) / constant_image (prices Mkt pos_stock 0)"
  {
    fix x
    assume "x\<notin> stocks Mkt"
    hence mkprop: "(\<forall> Mkt2 p. (coincides_on Mkt Mkt2 (stocks Mkt)) \<and> (prices Mkt2 x = pr) \<and> portfolio p \<and> support_set p \<subseteq> stocks Mkt \<union> {x} \<longrightarrow>
          \<not> arbitrage_process Mkt2 p)" using xasset by simp
    fix Mkt2
    assume "(coincides_on Mkt Mkt2 (stocks Mkt))" and "(prices Mkt2 x = pr)"
    have "0 < constant_image (prices Mkt pos_stock 0)" using trading_strategy_init
      proof -
        have "borel_adapt_stoch_proc F (prices Mkt pos_stock)" using pos_stock_borel_adapted by simp
        hence "\<exists>c. \<forall>w\<in>space M. prices Mkt pos_stock 0 w = c" using  adapted_init[of "prices Mkt pos_stock"] by simp
        moreover have "\<forall>w\<in> space M. 0 < prices Mkt pos_stock 0 w" using positive by simp
        ultimately show ?thesis using constant_image_pos by simp
      qed

    define arb_pf where "arb_pf = (\<lambda> (x::'b) (n::nat) (w::'a). 0::real)(x:= (\<lambda> n w. -1), pos_stock := (\<lambda> n w. diff_inv))"
    define contr_pf where "contr_pf = qty_sum arb_pf pf"
    have 1:"0 \<noteq> diff_inv \<longrightarrow> self_financing Mkt2 contr_pf"
      using arbitrage_portfolio_properties[of der matur \<pi> pr pf Mkt2 x diff_inv arb_pf contr_pf]
      using  \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> \<open>price_structure der matur \<pi> pr\<close> \<open>prices Mkt2 x = pr\<close>
        \<open>x \<notin> stocks Mkt\<close> arb_pf_def assms(1) contr_pf_def diff_inv_def by blast
    have 2:"0 \<noteq> diff_inv \<longrightarrow> trading_strategy contr_pf"
      using arbitrage_portfolio_properties[of der matur \<pi> pr pf Mkt2 x diff_inv arb_pf contr_pf]
      using  \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> \<open>price_structure der matur \<pi> pr\<close> \<open>prices Mkt2 x = pr\<close>
        \<open>x \<notin> stocks Mkt\<close> arb_pf_def assms(1) contr_pf_def diff_inv_def by blast
    have 3:"0 \<noteq> diff_inv \<longrightarrow> (\<forall>w\<in> space M. cls_val_process Mkt2 contr_pf 0 w = 0)"
      using arbitrage_portfolio_properties[of der matur \<pi> pr pf Mkt2 x diff_inv arb_pf contr_pf]
      using  \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> \<open>price_structure der matur \<pi> pr\<close> \<open>prices Mkt2 x = pr\<close>
        \<open>x \<notin> stocks Mkt\<close> arb_pf_def assms(1) contr_pf_def diff_inv_def by blast
    have 4: "0 < diff_inv \<longrightarrow> (AE w in M. 0 < cls_val_process Mkt2 contr_pf matur w)"
      using arbitrage_portfolio_properties[of der matur \<pi> pr pf Mkt2 x diff_inv arb_pf contr_pf]
      using  \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> \<open>price_structure der matur \<pi> pr\<close> \<open>prices Mkt2 x = pr\<close>
        \<open>x \<notin> stocks Mkt\<close> arb_pf_def assms(1) contr_pf_def diff_inv_def by blast
    have 5: "diff_inv < 0 \<longrightarrow> (AE w in M. 0 > cls_val_process Mkt2 contr_pf matur w)"
      using arbitrage_portfolio_properties[of der matur \<pi> pr pf Mkt2 x diff_inv arb_pf contr_pf]
      using  \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> \<open>price_structure der matur \<pi> pr\<close> \<open>prices Mkt2 x = pr\<close>
        \<open>x \<notin> stocks Mkt\<close> arb_pf_def assms(1) contr_pf_def diff_inv_def by blast
    have 6: "0 \<noteq> diff_inv \<longrightarrow> support_set arb_pf = {x, pos_stock}"
      using arbitrage_portfolio_properties[of der matur \<pi> pr pf Mkt2 x diff_inv arb_pf contr_pf]
      using  \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> \<open>price_structure der matur \<pi> pr\<close> \<open>prices Mkt2 x = pr\<close>
        \<open>x \<notin> stocks Mkt\<close> arb_pf_def assms(1) contr_pf_def diff_inv_def by blast
    have 7: "0 \<noteq> diff_inv \<longrightarrow>support_set contr_pf \<subseteq> stocks Mkt \<union> {x}"
    proof -
      have "0 \<noteq> diff_inv \<longrightarrow> support_set contr_pf \<subseteq> support_set arb_pf \<union> support_set pf" unfolding contr_pf_def
        by (simp add:sum_support_set)
      moreover have "0 \<noteq> diff_inv \<longrightarrow>support_set arb_pf \<subseteq> stocks Mkt \<union> {x}" using \<open>0 \<noteq> diff_inv \<longrightarrow> support_set arb_pf = {x, pos_stock}\<close> in_stock by simp
      moreover have "0 \<noteq> diff_inv \<longrightarrow>support_set pf \<subseteq> stocks Mkt \<union> {x}" using assms unfolding replicating_portfolio_def
        stock_portfolio_def by auto
      ultimately show ?thesis by auto
    qed
    have 8:"0 \<noteq> diff_inv \<longrightarrow>portfolio contr_pf"
      using arbitrage_portfolio_properties[of der matur \<pi> pr pf Mkt2 x diff_inv arb_pf contr_pf]
      using  \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> \<open>price_structure der matur \<pi> pr\<close> \<open>prices Mkt2 x = pr\<close>
        \<open>x \<notin> stocks Mkt\<close> arb_pf_def assms(1) contr_pf_def diff_inv_def by blast
    have 9: "0 \<noteq> diff_inv \<longrightarrow> cls_val_process Mkt2 contr_pf matur \<in> borel_measurable (F matur)"
    proof
      assume "0 \<noteq> diff_inv"
      have 10:"\<forall> asset \<in> support_set arb_pf \<union> support_set pf. prices Mkt2 asset matur \<in> borel_measurable (F matur)"
      proof
        fix asset
        assume "asset \<in> support_set arb_pf \<union> support_set pf"
        show "prices Mkt2 asset matur \<in> borel_measurable (F matur)"
        proof (cases "asset \<in> support_set pf")
          case True
          thus ?thesis using assms readable
            by (metis (no_types, lifting)  \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> adapt_stoch_proc_def
                coincides_on_def disc_equity_market.replicating_portfolio_def
                disc_equity_market_axioms  stock_portfolio_def subsetCE)
        next
          case False
          hence "asset\<in> support_set arb_pf" using \<open>asset \<in> support_set arb_pf \<union> support_set pf\<close> by auto
          show ?thesis
          proof (cases "asset = x")
            case True
            thus ?thesis
              using \<open>price_structure der matur \<pi> pr\<close> \<open>prices Mkt2 x = pr\<close> price_structure_borel_measurable by blast
          next
            case False
            hence "asset = pos_stock" using \<open>asset\<in> support_set arb_pf\<close> \<open>0 \<noteq> diff_inv \<longrightarrow> support_set arb_pf = {x, pos_stock}\<close>
              \<open>0 \<noteq> diff_inv\<close> by auto
            thus ?thesis
              by (metis \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> adapt_stoch_proc_def coincides_on_def in_stock pos_stock_borel_adapted)
          qed
        qed
      qed
      moreover have "\<forall>asset\<in>support_set contr_pf. contr_pf asset matur \<in> borel_measurable (F matur)"
        using \<open>0 \<noteq> diff_inv \<longrightarrow>trading_strategy contr_pf\<close> \<open>0 \<noteq> diff_inv\<close>
        by (metis adapt_stoch_proc_def disc_filtr_prob_space.predict_imp_adapt disc_filtr_prob_space_axioms trading_strategy_def)
      ultimately show "cls_val_process Mkt2 contr_pf matur \<in> borel_measurable (F matur)"
      proof-
        have "\<forall>asset\<in>support_set contr_pf. contr_pf asset (Suc matur) \<in> borel_measurable (F matur)"
           using \<open>0 \<noteq> diff_inv \<longrightarrow>trading_strategy contr_pf\<close> \<open>0 \<noteq> diff_inv\<close>
           by (simp add: predict_stoch_proc_def trading_strategy_def)
         moreover have "\<forall>asset\<in>support_set contr_pf. prices Mkt2 asset matur \<in> borel_measurable (F matur)" using 10 unfolding contr_pf_def
           using sum_support_set[of arb_pf pf] by auto
         ultimately show ?thesis  by (metis (no_types, lifting) "1" \<open>0 \<noteq> diff_inv\<close> quantity_adapted self_financingE)
      qed
    qed
    {
      assume "0 > diff_inv"
      define opp_pf where "opp_pf = qty_mult_comp contr_pf (\<lambda> n w. -1)"
      have "arbitrage_process Mkt2 opp_pf"
      proof (rule arbitrage_processI, rule exI, intro conjI)
        show "self_financing Mkt2 opp_pf" using 1 \<open>0 > diff_inv\<close> mult_time_constant_self_financing[of contr_pf] 8
          unfolding opp_pf_def by auto
        show "trading_strategy opp_pf" unfolding opp_pf_def
        proof (rule mult_comp_trading_strat)
          show "trading_strategy contr_pf" using 2 \<open>0 > diff_inv\<close> by auto
          show "borel_predict_stoch_proc F (\<lambda>n w. - 1)" by (simp add: constant_process_borel_predictable)
        qed
        show "\<forall>w\<in>space M. cls_val_process Mkt2 opp_pf 0 w = 0"
        proof
          fix w
          assume "w\<in> space M"
          show "cls_val_process Mkt2 opp_pf 0 w = 0" using 3 8 \<open>0 > diff_inv\<close>
            using \<open>w \<in> space M\<close> mult_comp_cls_val_process0 opp_pf_def by fastforce
        qed
        have "AE w in M. 0 < cls_val_process Mkt2 opp_pf matur w"
        proof (rule AE_mp)
          show "AE w in M. 0 > cls_val_process Mkt2 contr_pf matur w" using 5 \<open>0 > diff_inv\<close> by auto
          show "AE w in M. cls_val_process Mkt2 contr_pf matur w < 0 \<longrightarrow> 0 < cls_val_process Mkt2 opp_pf matur w"
          proof
            fix w
            assume "w\<in> space M"
            show "cls_val_process Mkt2 contr_pf matur w < 0 \<longrightarrow> 0 < cls_val_process Mkt2 opp_pf matur w"
            proof
              assume "cls_val_process Mkt2 contr_pf matur w < 0"
              show "0 < cls_val_process Mkt2 opp_pf matur w"
              proof (cases "matur = 0")
                case False
                hence "\<exists>m. Suc m = matur" by presburger
                from this obtain m where "Suc m = matur" by auto
                hence "0 < cls_val_process Mkt2 opp_pf (Suc m) w" using 3 8 \<open>0 > diff_inv\<close> \<open>w \<in> space M\<close> mult_comp_cls_val_process_Suc  opp_pf_def
                  using \<open>cls_val_process Mkt2 contr_pf matur w < 0\<close> by fastforce
                thus ?thesis using \<open>Suc m = matur\<close> by simp
              next
                case True
                thus ?thesis using 3 8 \<open>0 > diff_inv\<close> \<open>w \<in> space M\<close> mult_comp_cls_val_process0 opp_pf_def
                  using \<open>cls_val_process Mkt2 contr_pf matur w < 0\<close> by auto
              qed
            qed
          qed
        qed
        thus "AE w in M. 0 \<le> cls_val_process Mkt2 opp_pf matur w" by auto
        show "0 < prob {w \<in> space M. 0 < cls_val_process Mkt2 opp_pf matur w}"
        proof -
          let ?P = "{w\<in> space M. 0 < cls_val_process Mkt2 opp_pf matur w}"
          have "cls_val_process Mkt2 opp_pf matur \<in> borel_measurable (F matur)" (*unfolding opp_pf_def *)
          proof -
            have "cls_val_process Mkt2 contr_pf matur \<in> borel_measurable (F matur)" using 9 \<open>0 > diff_inv\<close> by simp
            moreover have "portfolio contr_pf" using 8 \<open>0 > diff_inv\<close> by simp
            moreover have "(\<lambda>w. - 1) \<in> borel_measurable (F matur)" by (simp add:constant_process_borel_adapted)
            ultimately show ?thesis
              using mult_comp_cls_val_process_measurable
            proof -
              have "diff_inv \<noteq> 0"
                using \<open>diff_inv < 0\<close> by blast
              then have "self_financing Mkt2 contr_pf"
                by (metis "1")
              then show ?thesis
                by (metis (no_types) \<open>(\<lambda>w. - 1) \<in> borel_measurable (F matur)\<close> \<open>portfolio contr_pf\<close>
                    \<open>self_financing Mkt2 opp_pf\<close> \<open>cls_val_process Mkt2 contr_pf matur \<in> borel_measurable (F matur)\<close>
                    mult_comp_val_process_measurable opp_pf_def self_financingE)
            qed
          qed
          moreover have "space M = space (F matur)"
            using filtration by (simp add: filtration_def subalgebra_def)
          ultimately have "?P \<in> sets (F matur)" using borel_measurable_iff_greater[of "val_process Mkt2 contr_pf matur" "F matur"]
            by auto
          hence "?P \<in> sets M" by (meson filtration filtration_def subalgebra_def subsetCE)
          hence "measure M ?P = 1" using  prob_Collect_eq_1[of "\<lambda>x. 0 < cls_val_process Mkt2 opp_pf matur x"]
             \<open>AE w in M. 0 < cls_val_process Mkt2 opp_pf matur w\<close> \<open>0 > diff_inv\<close> by blast
          thus ?thesis by simp
        qed
      qed
        have "\<exists> p. portfolio p \<and> support_set p \<subseteq> stocks Mkt \<union> {x} \<and> arbitrage_process Mkt2 p"
        proof(intro exI conjI)
          show "arbitrage_process Mkt2 opp_pf" using \<open>arbitrage_process Mkt2 opp_pf\<close> .
          show "portfolio opp_pf" unfolding opp_pf_def using 8 \<open>0 > diff_inv\<close> by (auto simp add: mult_comp_portfolio)
          show "support_set opp_pf \<subseteq> stocks Mkt \<union> {x}" unfolding opp_pf_def using 7 \<open>0 > diff_inv\<close>
            using mult_comp_support_set by fastforce
        qed
      } note negp = this
      {
        assume "0 < diff_inv"
        have "arbitrage_process Mkt2 contr_pf"
        proof (rule arbitrage_processI, rule exI, intro conjI)
          show "self_financing Mkt2 contr_pf" using 1 \<open>0 < diff_inv\<close> by auto
          show "trading_strategy contr_pf" using 2 \<open>0 < diff_inv\<close> by auto
          show "\<forall>w\<in>space M. cls_val_process Mkt2 contr_pf 0 w = 0" using 3 \<open>0 < diff_inv\<close> by auto
          show "AE w in M. 0 \<le> cls_val_process Mkt2 contr_pf matur w" using 4 \<open>0 < diff_inv\<close> by auto
          show "0 < prob {w \<in> space M. 0 < cls_val_process Mkt2 contr_pf matur w}"
            proof -
              let ?P = "{w\<in> space M. 0 < cls_val_process Mkt2 contr_pf matur w}"
              have "cls_val_process Mkt2 contr_pf matur \<in> borel_measurable (F matur)" using 9 \<open>0 < diff_inv\<close> by auto
              moreover have "space M = space (F matur)"
                using filtration  by (simp add: filtration_def subalgebra_def)
              ultimately have "?P \<in> sets (F matur)" using borel_measurable_iff_greater[of "val_process Mkt2 contr_pf matur" "F matur"]
                by auto
              hence "?P \<in> sets M" by (meson filtration filtration_def subalgebra_def subsetCE)
              hence "measure M ?P = 1" using  prob_Collect_eq_1[of "\<lambda>x. 0 < cls_val_process Mkt2 contr_pf matur x"]
                 4 \<open>0 < diff_inv\<close> by blast
              thus ?thesis by simp
            qed
          qed
          have "\<exists> p. portfolio p \<and> support_set p \<subseteq> stocks Mkt \<union> {x} \<and> arbitrage_process Mkt2 p"
          proof(intro exI conjI)
            show "arbitrage_process Mkt2 contr_pf" using \<open>arbitrage_process Mkt2 contr_pf\<close> .
            show "portfolio contr_pf" using 8 \<open>0 < diff_inv\<close> by auto
            show "support_set contr_pf \<subseteq> stocks Mkt \<union> {x}" using 7 \<open>0 < diff_inv\<close> by auto
          qed
      } note posp = this
      have "diff_inv \<noteq> 0 \<longrightarrow> \<not>(\<exists> pr. price_structure der matur \<pi> pr \<and>
        (\<forall> x. (x\<notin> stocks Mkt \<longrightarrow>
          (\<forall> Mkt2 p. (coincides_on Mkt Mkt2 (stocks Mkt)) \<and> (prices Mkt2 x = pr) \<and> portfolio p \<and> support_set p \<subseteq> stocks Mkt \<union> {x} \<longrightarrow>
            \<not> arbitrage_process Mkt2 p))))"
        using \<open>coincides_on Mkt Mkt2 (stocks Mkt)\<close> \<open>prices Mkt2 x = pr\<close> \<open>x \<notin> stocks Mkt\<close> xasset posp negp by force
  }
  hence "diff_inv = 0" using fix_asset_price expr by metis
  moreover have "constant_image (prices Mkt pos_stock 0) > 0"
    by (simp add: adapted_init constant_image_pos pos_stock_borel_adapted positive)
  ultimately show ?thesis unfolding diff_inv_def by auto
qed


subsection \<open>Risk-neutral probability space\<close>

subsubsection \<open>risk-free rate and discount factor processes\<close>

fun disc_rfr_proc:: "real \<Rightarrow> nat \<Rightarrow> 'a \<Rightarrow> real"
where
  rfr_base: "(disc_rfr_proc r) 0 w = 1"|
  rfr_step: "(disc_rfr_proc r) (Suc n) w = (1+r) * (disc_rfr_proc r) n w"


lemma disc_rfr_proc_borel_measurable:
  shows "(disc_rfr_proc r) n \<in> borel_measurable M"
proof (induct n)
case (Suc n) thus ?case by (simp add:borel_measurable_times)
qed auto

lemma disc_rfr_proc_nonrandom:
  fixes r::real
  shows "\<And>n. disc_rfr_proc r n \<in> borel_measurable (F 0)" using disc_rfr_proc_borel_measurable by auto


lemma (in disc_equity_market) disc_rfr_constant_time:
shows "\<exists>c. \<forall>w \<in> space (F 0).  (disc_rfr_proc r n) w = c"
proof (rule triv_measurable_cst)
  show "space (F 0) = space M" using filtration by (simp add:filtration_def subalgebra_def)
  show "sets (F 0) = {{}, space M}" using info_disc_filtr  by (simp add: bot_nat_def init_triv_filt_def)
  show "(disc_rfr_proc r n) \<in> borel_measurable (F 0)" using disc_rfr_proc_nonrandom by blast
  show "space M \<noteq> {}" by (simp add:not_empty)
qed



lemma (in disc_filtr_prob_space) disc_rfr_proc_borel_adapted:
  shows "borel_adapt_stoch_proc F (disc_rfr_proc r)"
unfolding adapt_stoch_proc_def using disc_rfr_proc_nonrandom
         filtration unfolding filtration_def
  by (meson increasing_measurable_info le0)



lemma disc_rfr_proc_positive:
  assumes "-1 < r"
  shows "\<And>n w . 0 < disc_rfr_proc r n w"
proof -
  fix n
  fix w::'a
  show "0 < disc_rfr_proc r n w"
  proof (induct n)
  case 0 thus ?case using assms  "disc_rfr_proc.simps" by simp
  next
  case (Suc n) thus ?case using  assms "disc_rfr_proc.simps" by simp
  qed
qed





lemma (in prob_space) disc_rfr_constant_time_pos:
  assumes "-1 < r"
shows "\<exists>c > 0. \<forall>w \<in> space M.  (disc_rfr_proc r n) w = c"
proof -
  let ?F = "sigma (space M) {{}, space M}"
  have  ex: "\<exists>c. \<forall>w \<in> space ?F.  (disc_rfr_proc r n) w = c"
  proof (rule triv_measurable_cst)
    show "space ?F = space M" by simp
    show "sets ?F = {{}, space M}" by (meson sigma_algebra.sets_measure_of_eq sigma_algebra_trivial)
    show "(disc_rfr_proc r n) \<in> borel_measurable ?F" using disc_rfr_proc_borel_measurable by blast
    show "space M \<noteq> {}" by (simp add:not_empty)
  qed
  from this obtain c where "\<forall>w \<in> space ?F.  (disc_rfr_proc r n) w = c" by auto note cprops = this
  have "c>0"
  proof -
    have "\<exists> w. w\<in> space M" using subprob_not_empty by blast
    from this obtain w where "w\<in> space M" by auto
    hence "c = disc_rfr_proc r n w" using cprops  by simp
    also have "... > 0" using disc_rfr_proc_positive[of r n] assms by simp
    finally show ?thesis .
  qed
  moreover have "space M = space ?F" by simp
  ultimately show ?thesis using ex using cprops by blast
qed


lemma  disc_rfr_proc_Suc_div:
  assumes "-1 < r"
  shows "\<And>w. disc_rfr_proc r (Suc n) w/disc_rfr_proc r n w = 1+r"
proof -
  fix w::'a
  show "disc_rfr_proc r (Suc n) w/disc_rfr_proc r n w = 1+r"
    using disc_rfr_proc_positive assms by (metis rfr_step  less_irrefl nonzero_eq_divide_eq)
qed

definition discount_factor where
  "discount_factor r n = (\<lambda>w. inverse (disc_rfr_proc r n w))"

lemma discount_factor_times_rfr:
  assumes "-1 < r"
  shows "(1+r) * discount_factor r (Suc n) w = discount_factor r n w" unfolding discount_factor_def using assms by simp

lemma discount_factor_borel_measurable:
  shows "discount_factor r n \<in> borel_measurable M" unfolding discount_factor_def
proof (rule borel_measurable_inverse)
  show "disc_rfr_proc r n \<in> borel_measurable M" by (simp add:disc_rfr_proc_borel_measurable)
qed

lemma discount_factor_init:
  shows "discount_factor r 0 = (\<lambda>w. 1)" unfolding discount_factor_def by simp

lemma discount_factor_nonrandom:
  shows "discount_factor r n \<in> borel_measurable M" unfolding discount_factor_def
proof (rule borel_measurable_inverse)
  show "disc_rfr_proc r n \<in> borel_measurable M" by (simp add:disc_rfr_proc_borel_measurable)
qed


lemma discount_factor_positive:
  assumes "-1 < r"
  shows "\<And>n w . 0 < discount_factor r n w" using assms disc_rfr_proc_positive unfolding discount_factor_def by auto


lemma (in prob_space) discount_factor_constant_time_pos:
  assumes "-1 < r"
shows "\<exists>c > 0. \<forall>w \<in> space M.  (discount_factor r n) w = c"  using  disc_rfr_constant_time_pos unfolding discount_factor_def
  by (metis assms inverse_positive_iff_positive)


locale rsk_free_asset =
  fixes Mkt r risk_free_asset
  assumes acceptable_rate: "-1 < r"
  and rf_price: "prices Mkt risk_free_asset = disc_rfr_proc r"
  and rf_stock: "risk_free_asset \<in> stocks Mkt"

locale rfr_disc_equity_market = disc_equity_market   + rsk_free_asset +
  assumes rd: "\<forall> asset\<in> stocks Mkt. borel_adapt_stoch_proc F (prices Mkt asset)"



sublocale rfr_disc_equity_market \<subseteq> disc_market_pos_stock _ _ _ "risk_free_asset"
by (unfold_locales, (auto simp add: rf_stock rd disc_rfr_proc_positive rf_price acceptable_rate))

subsubsection \<open>Discounted value of a stochastic process\<close>

definition discounted_value where
  "discounted_value r X = (\<lambda> n w. discount_factor r n w * X n w)"



lemma (in rfr_disc_equity_market) discounted_rfr:
  shows "discounted_value r (prices Mkt risk_free_asset) n w = 1" unfolding discounted_value_def discount_factor_def
  using rf_price by (metis less_irrefl mult.commute positive right_inverse)

lemma  discounted_init:
  shows "\<forall>w. discounted_value r X 0 w = X 0 w" unfolding discounted_value_def by (simp add: discount_factor_init)

lemma  discounted_mult:
  shows "\<forall>n w. discounted_value r (\<lambda>m x. X m x * Y m x) n w = X n w * (discounted_value r Y) n w"
  by (simp add: discounted_value_def)

lemma  discounted_mult':
  shows "discounted_value r (\<lambda>m x. X m x * Y m x) n w = X n w * (discounted_value r Y) n w"
  by (simp add: discounted_value_def)

lemma discounted_mult_times_rfr:
  assumes "-1 < r"
  shows "discounted_value r (\<lambda>m w. (1+r) * X w) (Suc n) w = discounted_value r (\<lambda>m w. X w) n w"
    unfolding discounted_value_def using assms discount_factor_times_rfr discounted_mult
    by (simp add: discount_factor_times_rfr mult.commute)

lemma discounted_cong:
  assumes "\<forall>n w. X n w = Y n w"
  shows "\<forall> n w. discounted_value r X n w = discounted_value r Y n w"
  by (simp add: assms discounted_value_def)

lemma  discounted_cong':
  assumes "X n w = Y n w"
  shows "discounted_value r X n w = discounted_value r Y n w"
  by (simp add: assms discounted_value_def)

lemma discounted_AE_cong:
  assumes "AE w in N. X n w = Y n w"
  shows "AE w in N. discounted_value r X n w = discounted_value r Y n w"
proof (rule AE_mp)
  show "AE w in N. X n w = Y n w" using assms by simp
  show "AE w in N. X n w = Y n w \<longrightarrow> discounted_value r X n w = discounted_value r Y n w"
  proof
    fix w
    assume "w\<in> space N"
    thus "X n w = Y n w \<longrightarrow> discounted_value r X n w = discounted_value r Y n w " by (simp add:discounted_value_def)
  qed
qed



lemma discounted_sum:
  assumes "finite I"
shows "\<forall>n w. (\<Sum> i\<in> I. (discounted_value r (\<lambda>m x. f i m x)) n w) = (discounted_value r (\<lambda>m x. (\<Sum>i\<in> I. f i m x)) n w)"
  using assms(1) subset_refl[of I]
proof (induct rule: finite_subset_induct)
  case empty
  then show ?case
    by (simp add: discounted_value_def)
next
  case (insert a F)
  show ?case
  proof (intro allI)
    fix n w
    have "(\<Sum>i\<in>insert a F. discounted_value r (f i) n w) = discounted_value r (f a) n w + (\<Sum>i\<in>F. discounted_value r (f i) n w)"
      by (simp add: insert.hyps(1) insert.hyps(3))
    also have "... = discounted_value r (f a) n w + discounted_value r (\<lambda>m x. \<Sum>i\<in>F. f i m x) n w" using insert.hyps(4) by simp
    also have "... = discounted_value r (\<lambda>m x. \<Sum>i\<in>insert a F. f i m x) n w"
      by (simp add: discounted_value_def insert.hyps(1) insert.hyps(3) ring_class.ring_distribs(1))
    finally show "(\<Sum>i\<in>insert a F. discounted_value r (f i) n w) = discounted_value r (\<lambda>m x. \<Sum>i\<in>insert a F. f i m x) n w" .
  qed
qed

lemma  discounted_adapted:
  assumes "borel_adapt_stoch_proc F X"
  shows "borel_adapt_stoch_proc F (discounted_value r X)" unfolding adapt_stoch_proc_def
proof
  fix t
  show "discounted_value r X t \<in> borel_measurable (F t)" unfolding discounted_value_def
  proof (rule borel_measurable_times)
    show "X t \<in> borel_measurable (F t)" using assms unfolding adapt_stoch_proc_def by simp
    show "discount_factor r t \<in> borel_measurable (F t)" using discount_factor_borel_measurable by auto
  qed
qed

lemma discounted_measurable:
  assumes "X\<in> borel_measurable N"
  shows "discounted_value r (\<lambda>m. X) m \<in> borel_measurable N" unfolding discounted_value_def
proof (rule borel_measurable_times)
  show "X\<in> borel_measurable N" using assms by simp
  show "discount_factor r m \<in> borel_measurable N" using discount_factor_borel_measurable by auto
qed


lemma (in prob_space) discounted_integrable:
  assumes "integrable N (X n)"
  and "-1 < r"
  and "space N = space M"
  shows "integrable N (discounted_value r X n)" unfolding discounted_value_def
proof -
  have "\<exists>c> 0. \<forall>w \<in> space M.  (discount_factor r n) w = c" using discount_factor_constant_time_pos assms by simp
  from this obtain c where "c > 0" and "\<forall>w \<in> space M.  (discount_factor r n) w = c" by auto note cprops = this
  hence "\<forall>w \<in> space M. discount_factor r n w = c" using cprops  by simp
  hence "\<forall>w \<in> space N. discount_factor r n w = c" using assms by simp
  thus "integrable N (\<lambda>w. discount_factor r n w * X n w)"
    using \<open>\<forall>w \<in> space N. discount_factor r n w = c\<close> assms
    integrable_cong[of N N "(\<lambda>w. discount_factor r n w * X n w)" "(\<lambda>w. c * X n w)"] by simp
qed


subsubsection \<open>Results on risk-neutral probability spaces\<close>

definition (in rfr_disc_equity_market) risk_neutral_prob where
  "risk_neutral_prob N \<longleftrightarrow> (prob_space N) \<and> (\<forall> asset \<in> stocks Mkt. martingale N F (discounted_value r (prices Mkt asset)))"


lemma integrable_val_process:
  assumes "\<forall> asset \<in> support_set pf. integrable M (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w)"
  shows "integrable M (val_process Mkt pf n)"
proof (cases "portfolio pf")
  case False
  thus ?thesis unfolding val_process_def by simp
next
  case True
  hence "val_process Mkt pf n = (\<lambda>w. \<Sum>x\<in>support_set pf. prices Mkt x n w * pf x (Suc n) w)"
    unfolding val_process_def by simp
  moreover have "integrable M (\<lambda>w. \<Sum>x\<in>support_set pf. prices Mkt x n w * pf x (Suc n) w)" using assms by simp
  ultimately show ?thesis by simp
qed

lemma integrable_self_fin_uvp:
  assumes "\<forall> asset \<in> support_set pf. integrable M (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w)"
  and "self_financing Mkt pf"
shows "integrable M (cls_val_process Mkt pf n)"
proof -
  have "val_process Mkt pf n = cls_val_process Mkt pf n" using assms by (simp add:self_financingE)
  moreover have "integrable M (val_process Mkt pf n)" using assms by (simp add:integrable_val_process)
  ultimately show ?thesis by simp
qed



lemma (in rfr_disc_equity_market) stocks_portfolio_risk_neutral:
  assumes "risk_neutral_prob N"
  and "trading_strategy pf"
  and "subalgebra N M"
  and "support_set pf \<subseteq> stocks Mkt"
  and "\<forall>n. \<forall> asset \<in> support_set pf. integrable N (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w)"
  shows  "\<forall>x \<in> support_set pf. AE w in N.
        (real_cond_exp N (F n) (discounted_value r (\<lambda>m y. prices Mkt x m y * pf x m y) (Suc n))) w =
        discounted_value r (\<lambda>m y. prices Mkt x m y * pf x (Suc m) y) n w"
proof
  have nsigfin: "\<forall>n. sigma_finite_subalgebra N (F n)" using assms unfolding risk_neutral_prob_def martingale_def subalgebra_def
      using filtration filtration_def risk_neutral_prob_def prob_space.subalgebra_sigma_finite in_stock by metis
  have "disc_filtr_prob_space N F"
  proof -
    have "prob_space N" using assms unfolding risk_neutral_prob_def by simp
    moreover have "disc_filtr N F" using assms subalgebra_filtration
      by (metis (no_types, lifting) filtration disc_filtr_def filtration_def)
    ultimately show ?thesis
      by (simp add: disc_filtr_prob_space_axioms_def disc_filtr_prob_space_def)
  qed
  fix asset
  assume "asset \<in> support_set pf"
  hence "asset \<in> stocks Mkt" using assms by auto
  have "discounted_value r (prices Mkt asset) (Suc n) \<in> borel_measurable M" using assms readable
    by (meson \<open>asset \<in> stocks Mkt\<close> borel_adapt_stoch_proc_borel_measurable discounted_adapted
        rfr_disc_equity_market.risk_neutral_prob_def rfr_disc_equity_market_axioms)
  hence b: "discounted_value r (prices Mkt asset) (Suc n) \<in> borel_measurable N"
      using assms Conditional_Expectation.measurable_from_subalg[of N M _ borel] by auto
  show "AEeq N (real_cond_exp N (F n) (discounted_value r (\<lambda>m y. prices Mkt asset m y * pf asset m y) (Suc n)))
  (discounted_value r (\<lambda>m y. prices Mkt asset m y * pf asset (Suc m) y) n)"
  proof -
    have "AE w in N. (real_cond_exp N (F n) (discounted_value r (\<lambda>m y. prices Mkt asset m y * pf asset m y) (Suc n))) w =
      (real_cond_exp N (F n) (\<lambda>z. pf asset (Suc n) z * discounted_value r (\<lambda>m y. prices Mkt asset m y) (Suc n) z)) w"
    proof (rule sigma_finite_subalgebra.real_cond_exp_cong)
      show "sigma_finite_subalgebra N (F n)" using nsigfin ..
      show "AE w in N. discounted_value r (\<lambda>m y. prices Mkt asset m y * pf asset m y) (Suc n) w =
         pf asset (Suc n) w * discounted_value r (\<lambda>m y. prices Mkt asset m y) (Suc n) w"
        by (simp add: discounted_value_def)
      show "discounted_value r (\<lambda>m y. prices Mkt asset m y * pf asset m y) (Suc n) \<in> borel_measurable N"
      proof -
        have "(\<lambda>y. prices Mkt asset (Suc n) y * pf asset (Suc n) y) \<in> borel_measurable N"
          using assms \<open>asset\<in> support_set pf\<close> by (simp add:borel_measurable_integrable)
        thus ?thesis unfolding discounted_value_def using discount_factor_borel_measurable[of r "Suc n" N] by simp
      qed
      show "(\<lambda>z. pf asset (Suc n) z * discounted_value r (prices Mkt asset) (Suc n) z) \<in> borel_measurable N"
      proof -
        have "pf asset (Suc n) \<in> borel_measurable M" using assms \<open>asset\<in> support_set pf\<close> unfolding trading_strategy_def
          using borel_predict_stoch_proc_borel_measurable[of "pf asset"] by auto
        hence a: "pf asset (Suc n) \<in> borel_measurable N" using assms Conditional_Expectation.measurable_from_subalg[of N M _ borel] by blast
        show ?thesis using a b by simp
      qed
    qed
    also have "AE w in N. (real_cond_exp N (F n) (\<lambda>z. pf asset (Suc n) z * discounted_value r (\<lambda>m y. prices Mkt asset m y) (Suc n) z)) w =
      pf asset (Suc n) w * (real_cond_exp N (F n) (\<lambda>z. discounted_value r (\<lambda>m y. prices Mkt asset m y) (Suc n) z)) w"
    proof (rule sigma_finite_subalgebra.real_cond_exp_mult)
      show "discounted_value r (prices Mkt asset) (Suc n) \<in> borel_measurable N" using b by simp
      show "sigma_finite_subalgebra N (F n)" using nsigfin ..
      show "pf asset (Suc n) \<in> borel_measurable (F n)" using assms \<open>asset\<in> support_set pf\<close> unfolding trading_strategy_def
          predict_stoch_proc_def by auto
      show "integrable N (\<lambda>z. pf asset (Suc n) z * discounted_value r (prices Mkt asset) (Suc n) z)"
      proof -
        have "integrable N (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w)" using assms \<open>asset \<in> support_set pf\<close> by auto
        hence "integrable N (discounted_value r (\<lambda>m w. prices Mkt asset m w * pf asset m w) (Suc n))" using assms
          unfolding risk_neutral_prob_def using acceptable_rate  by (auto simp add:discounted_integrable subalgebra_def)
        thus ?thesis using discounted_mult
            integrable_cong[of N N "discounted_value r (\<lambda>m w. prices Mkt asset m w * pf asset m w) (Suc n)" "(\<lambda>z. pf asset (Suc n) z * discounted_value r (prices Mkt asset) (Suc n) z)"]
          by (simp add: discounted_value_def)
      qed
    qed
    also have "AE w in N.  pf asset (Suc n) w * (real_cond_exp N (F n) (\<lambda>z. discounted_value r (\<lambda>m y. prices Mkt asset m y) (Suc n) z)) w =
            pf asset (Suc n) w * discounted_value r (\<lambda>m y. prices Mkt asset m y) n w"
    proof -
      have "AEeq N (real_cond_exp N (F n) (\<lambda>z. discounted_value r (\<lambda>m y. prices Mkt asset m y) (Suc n) z))
        (\<lambda>z. discounted_value r (\<lambda>m y. prices Mkt asset m y) n z)"
      proof -
        have "martingale N F (discounted_value r (prices Mkt asset))"
          using assms \<open>asset \<in> stocks Mkt\<close> unfolding risk_neutral_prob_def by simp
        moreover have "filtrated_prob_space N F" using \<open>disc_filtr_prob_space N F\<close>
          using assms(2) disc_filtr_prob_space.axioms(1) filtrated_prob_space.intro filtrated_prob_space_axioms.intro filtration prob_space_axioms
          by (metis assms(3) subalgebra_filtration)
        ultimately show ?thesis using martingaleAE[of N F "discounted_value r (prices Mkt asset)" n "Suc n"] assms
          by simp
      qed
      thus ?thesis by auto
    qed
    also have "AE w in N.  pf asset (Suc n) w * discounted_value r (\<lambda>m y. prices Mkt asset m y) n w =
      discounted_value r (\<lambda>m y. pf asset (Suc m) y * prices Mkt asset m y) n w" by (simp add: discounted_value_def)
    also have "AE w in N. discounted_value r (\<lambda>m y. pf asset (Suc m) y * prices Mkt asset m y) n w =
      discounted_value r (\<lambda>m y. prices Mkt asset m y * pf asset (Suc m) y) n w"
      by (simp add: discounted_value_def)
    finally show "AE w in N.
      (real_cond_exp N (F n) (discounted_value r (\<lambda>m y. prices Mkt asset m y * pf asset m y) (Suc n))) w =
      (\<lambda>x. discounted_value r (\<lambda>m y. prices Mkt asset m y * pf asset (Suc m) y) n x) w" .
  qed
qed



lemma (in rfr_disc_equity_market) self_fin_trad_strat_mart:
  assumes "risk_neutral_prob N"
  and "filt_equiv F M N"
  and "trading_strategy pf"
  and "self_financing Mkt pf"
and "stock_portfolio Mkt pf"
  and "\<forall>n. \<forall> asset \<in> support_set pf. integrable N (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w)"
  and "\<forall>n. \<forall> asset \<in> support_set pf. integrable N (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w)"
shows "martingale N F (discounted_value r (cls_val_process Mkt pf))" (*unfolding martingale_def*)
proof (rule disc_martingale_charact)
  show nsigfin: "\<forall>n. sigma_finite_subalgebra N (F n)" using filt_equiv_prob_space_subalgebra assms
          using filtration filtration_def risk_neutral_prob_def subalgebra_sigma_finite by fastforce
  show "filtration N F" using assms by (simp  add:filt_equiv_filtration)
  have "borel_adapt_stoch_proc F (discounted_value r (cls_val_process Mkt pf))" using assms discounted_adapted
    cls_val_process_adapted[of pf] stock_portfolio_def
    by (metis (mono_tags, hide_lams) support_adapt_def readable subsetCE)
  thus "\<forall>m. discounted_value r (cls_val_process Mkt pf) m \<in> borel_measurable (F m)" unfolding adapt_stoch_proc_def by simp
  show "\<forall>t. integrable N (discounted_value r (cls_val_process Mkt pf) t)"
  proof
    fix t
    have "integrable N (cls_val_process Mkt pf t)" using assms by (simp add: integrable_self_fin_uvp)
    thus "integrable N (discounted_value r (cls_val_process Mkt pf) t)" using assms discounted_integrable acceptable_rate
      by (metis filt_equiv_space)
  qed
  show "\<forall>n. AE w in N. real_cond_exp N (F n) (discounted_value r (cls_val_process Mkt pf) (Suc n)) w =
                   discounted_value r (cls_val_process Mkt pf) n w"
  proof
    fix n
    show "AE w in N. real_cond_exp N (F n) (discounted_value r (cls_val_process Mkt pf) (Suc n)) w =
                    discounted_value r (cls_val_process Mkt pf) n w"
    proof -
      {
        fix w
        assume "w\<in> space M"
        have "discounted_value r (cls_val_process Mkt pf) (Suc n) w =
                  discount_factor r (Suc n) w * (\<Sum>x\<in>support_set pf. prices Mkt x (Suc n) w * pf x (Suc n) w)"
          unfolding discounted_value_def cls_val_process_def using assms unfolding trading_strategy_def by simp
        also have "... = (\<Sum>x\<in>support_set pf. discount_factor r (Suc n) w * prices Mkt x (Suc n) w * pf x (Suc n) w)"
          by (metis (no_types, lifting) mult.assoc sum.cong sum_distrib_left)
        finally have "discounted_value r (cls_val_process Mkt pf) (Suc n) w =
                  (\<Sum>x\<in>support_set pf. discount_factor r (Suc n) w * prices Mkt x (Suc n) w * pf x (Suc n) w)" .
      }
      hence space: "\<forall>w\<in> space M. discounted_value r (cls_val_process Mkt pf) (Suc n) w =
                (\<Sum>x\<in>support_set pf. discount_factor r (Suc n) w * prices Mkt x (Suc n) w * pf x (Suc n) w)" by simp
      hence nspace: "\<forall>w\<in> space N. discounted_value r (cls_val_process Mkt pf) (Suc n) w =
                (\<Sum>x\<in>support_set pf. discount_factor r (Suc n) w * prices Mkt x (Suc n) w * pf x (Suc n) w)" using assms by (simp add:filt_equiv_space)
      have sup_disc: "\<forall>x \<in> support_set pf. AE w in N.
        (real_cond_exp N (F n) (discounted_value r (\<lambda>m y. prices Mkt x m y * pf x m y) (Suc n))) w =
        discounted_value r (\<lambda>m y. prices Mkt x m y * pf x (Suc m) y) n w" using assms
        by (simp add:stocks_portfolio_risk_neutral filt_equiv_imp_subalgebra stock_portfolio_def)
      have "AE w in N. real_cond_exp N (F n) (discounted_value r (cls_val_process Mkt pf) (Suc n)) w =
                real_cond_exp N (F n) (\<lambda>y. \<Sum>x\<in>support_set pf. discounted_value r (\<lambda>m y. prices Mkt x m y * pf x m y) (Suc n) y) w"
      proof (rule sigma_finite_subalgebra.real_cond_exp_cong')
        show "sigma_finite_subalgebra N (F n)" using nsigfin ..
        show "\<forall>w\<in>space N. discounted_value r (cls_val_process Mkt pf) (Suc n) w =
          (\<lambda>y. \<Sum>x\<in>support_set pf. discounted_value r (\<lambda>m y. prices Mkt x m y * pf x m y) (Suc n) y) w"  using nspace
          by (metis (no_types, lifting) discounted_value_def mult.assoc sum.cong)
        show "(discounted_value r (cls_val_process Mkt pf) (Suc n)) \<in> borel_measurable N" using assms
          using \<open>\<forall>t. integrable N (discounted_value r (cls_val_process Mkt pf) t)\<close> by blast
      qed
      also have "AE w in N. real_cond_exp N (F n)
        (\<lambda>y. \<Sum>x\<in>support_set pf. discounted_value r (\<lambda>m y. prices Mkt x m y * pf x m y) (Suc n) y) w =
        (\<Sum>x\<in> support_set pf. (real_cond_exp N (F n) (discounted_value r (\<lambda>m y. prices Mkt x m y * pf x m y) (Suc n))) w)"
      proof (rule sigma_finite_subalgebra.real_cond_exp_bsum)
        show "sigma_finite_subalgebra N (F n)" using filt_equiv_prob_space_subalgebra assms
          using filtration filtration_def risk_neutral_prob_def subalgebra_sigma_finite by fastforce
        fix asset
        assume "asset \<in> support_set pf"
        show "integrable N (discounted_value r (\<lambda>m y. prices Mkt asset m y * pf asset m y) (Suc n))"
        proof (rule discounted_integrable)
          show "integrable N (\<lambda>y. prices Mkt asset (Suc n) y * pf asset (Suc n) y)" using assms \<open>asset\<in> support_set pf\<close> by simp
          show "space N = space M" using assms by (metis filt_equiv_space)
          show "-1 < r" using acceptable_rate by simp
        qed
      qed
      also have "AE w in N.
        (\<Sum>x\<in> support_set pf. (real_cond_exp N (F n) (discounted_value r (\<lambda>m y. prices Mkt x m y * pf x m y) (Suc n))) w) =
        (\<Sum>x\<in> support_set pf. discounted_value r (\<lambda>m y. prices Mkt x m y * pf x (Suc m) y) n w)"
      proof (rule AE_sum)
        show "finite (support_set pf)" using assms(3) portfolio_def trading_strategy_def by auto
        show  "\<forall>x \<in> support_set pf. AE w in N.
        (real_cond_exp N (F n) (discounted_value r (\<lambda>m y. prices Mkt x m y * pf x m y) (Suc n))) w =
        discounted_value r (\<lambda>m y. prices Mkt x m y * pf x (Suc m) y) n w" using sup_disc by simp
      qed
      also have "AE w in N.
        (\<Sum>x\<in> support_set pf. discounted_value r (\<lambda>m y. prices Mkt x m y * pf x (Suc m) y) n w) =
        discounted_value r (cls_val_process Mkt pf) n w"
      proof
        fix w
        assume "w\<in> space N"
        have "(\<Sum>x\<in> support_set pf. discounted_value r (\<lambda>m y. prices Mkt x m y * pf x (Suc m) y) n w) =
          discounted_value r (\<lambda>m y. (\<Sum>x\<in> support_set pf. prices Mkt x m y * pf x (Suc m) y)) n w" using discounted_sum
          assms(3) portfolio_def trading_strategy_def by (simp add: discounted_value_def sum_distrib_left)
        also have "... = discounted_value r (val_process Mkt pf) n w"  unfolding val_process_def
          by (simp add: portfolio_def)
        also have "... = discounted_value r (cls_val_process Mkt pf) n w" using assms
          by (simp add:self_financingE discounted_cong)
        finally show "(\<Sum>x\<in> support_set pf. discounted_value r (\<lambda>m y. prices Mkt x m y * pf x (Suc m) y) n w) =
          discounted_value r (cls_val_process Mkt pf) n w" .
      qed
      finally show "AE w in N. real_cond_exp N (F n) (discounted_value r (cls_val_process Mkt pf) (Suc n)) w =
        discounted_value r (cls_val_process Mkt pf) n w" .
    qed
  qed
qed

lemma (in disc_filtr_prob_space) finite_integrable_vp:
  assumes "\<forall>n. \<forall> asset \<in> support_set pf. finite (prices Mkt asset n `(space M))"
  and "\<forall>n. \<forall> asset \<in> support_set pf. finite (pf asset n `(space M))"
and "prob_space N"
  and "filt_equiv F M N"
and "trading_strategy pf"
and "\<forall>n. \<forall> asset \<in> support_set pf. prices Mkt asset n \<in> borel_measurable M"
shows  "\<forall>n. \<forall>asset\<in>support_set pf. integrable N (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w)"
proof (intro allI ballI)
  fix n
  fix asset
  assume "asset\<in>support_set pf"
  show "integrable N (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w)"
  proof (rule prob_space.finite_borel_measurable_integrable)
    show "prob_space N" using assms by simp
    have "finite ((\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) ` space M)"
    proof -
      have "\<forall>y\<in> prices Mkt asset n `(space M). finite ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y)"
        by (metis \<open>asset \<in> support_set pf\<close> assms(2) finite_imageI image_image)
      hence "finite (\<Union> y\<in> prices Mkt asset n `(space M). ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y))"
        using \<open>asset \<in> support_set pf\<close> assms by blast
      moreover have "(\<Union> y\<in> prices Mkt asset n `(space M). ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y)) =
        (\<Union> y\<in> prices Mkt asset n `(space M). (\<lambda>w. y * pf asset (Suc n) w) ` space M)"  by simp
      moreover have "((\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) ` space M) \<subseteq>
        (\<Union> y\<in> prices Mkt asset n `(space M). (\<lambda>w. y * pf asset (Suc n) w) ` space M)"
      proof
        fix x
        assume "x \<in> (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) ` space M"
        show "x \<in> (\<Union>y\<in>prices Mkt asset n ` space M. (\<lambda>w. y * pf asset (Suc n) w) ` space M)"
          using \<open>x \<in> (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) ` space M\<close> by auto
      qed
      ultimately show ?thesis by (simp add:finite_subset)
    qed
    thus "finite ((\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) ` space N)" using assms by (simp add:filt_equiv_space)
    have "(\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) \<in> borel_measurable M"
    proof -
      have "prices Mkt asset n \<in> borel_measurable M" using assms \<open>asset \<in> support_set pf\<close> by simp
      moreover have "pf asset (Suc n) \<in> borel_measurable M" using assms unfolding trading_strategy_def
        using \<open>asset \<in> support_set pf\<close> borel_predict_stoch_proc_borel_measurable by blast
      ultimately show ?thesis by simp
    qed
    thus "(\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) \<in> borel_measurable N" using assms by (simp add:filt_equiv_measurable)
  qed
qed


lemma (in disc_filtr_prob_space) finite_integrable_uvp:
  assumes "\<forall>n. \<forall> asset \<in> support_set pf. finite (prices Mkt asset n `(space M))"
  and "\<forall>n. \<forall> asset \<in> support_set pf. finite (pf asset n `(space M))"
and "prob_space N"
  and "filt_equiv F M N"
and "trading_strategy pf"
and "\<forall>n. \<forall> asset \<in> support_set pf. prices Mkt asset n \<in> borel_measurable M"
shows  "\<forall>n. \<forall>asset\<in>support_set pf. integrable N (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w)"
proof (intro allI ballI)
  fix n
  fix asset
  assume "asset\<in>support_set pf"
  show "integrable N (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w)"
  proof (rule prob_space.finite_borel_measurable_integrable)
    show "prob_space N" using assms by simp
    have "finite ((\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) ` space M)"
    proof -
      have "\<forall>y\<in> prices Mkt asset (Suc n) `(space M). finite ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y)"
        by (metis \<open>asset \<in> support_set pf\<close> assms(2) finite_imageI image_image)
      hence "finite (\<Union> y\<in> prices Mkt asset (Suc n) `(space M). ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y))"
        using \<open>asset \<in> support_set pf\<close> assms by blast
      moreover have "(\<Union> y\<in> prices Mkt asset (Suc n) `(space M). ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y)) =
        (\<Union> y\<in> prices Mkt asset (Suc n) `(space M). (\<lambda>w. y * pf asset (Suc n) w) ` space M)"  by simp
      moreover have "((\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) ` space M) \<subseteq>
        (\<Union> y\<in> prices Mkt asset (Suc n) `(space M). (\<lambda>w. y * pf asset (Suc n) w) ` space M)"
      proof
        fix x
        assume "x \<in> (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) ` space M"
        show "x \<in> (\<Union>y\<in>prices Mkt asset (Suc n) ` space M. (\<lambda>w. y * pf asset (Suc n) w) ` space M)"
          using \<open>x \<in> (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) ` space M\<close> by auto
      qed
      ultimately show ?thesis by (simp add:finite_subset)
    qed
    thus "finite ((\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) ` space N)" using assms by (simp add:filt_equiv_space)
    have "(\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) \<in> borel_measurable M"
    proof -
      have "prices Mkt asset (Suc n) \<in> borel_measurable M" using assms
        using \<open>asset \<in> support_set pf\<close> borel_adapt_stoch_proc_borel_measurable by blast
      moreover have "pf asset (Suc n) \<in> borel_measurable M" using assms unfolding trading_strategy_def
        using \<open>asset \<in> support_set pf\<close> borel_predict_stoch_proc_borel_measurable by blast
      ultimately show ?thesis by simp
    qed
    thus "(\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) \<in> borel_measurable N" using assms by (simp add:filt_equiv_measurable)
  qed
qed

lemma (in rfr_disc_equity_market) self_fin_trad_strat_mart_finite:
  assumes "risk_neutral_prob N"
  and "filt_equiv F M N"
  and "trading_strategy pf"
  and "self_financing Mkt pf"
  and "support_set pf \<subseteq> stocks Mkt"
  and "\<forall>n. \<forall> asset \<in> support_set pf. finite (prices Mkt asset n `(space M))"
  and "\<forall>n. \<forall> asset \<in> support_set pf. finite (pf asset n `(space M))"
and "\<forall> asset\<in> stocks Mkt. borel_adapt_stoch_proc F (prices Mkt asset)"
shows "martingale N F (discounted_value r (cls_val_process Mkt pf))"
proof (rule self_fin_trad_strat_mart, (simp add:assms)+)
  show "\<forall>n. \<forall>asset\<in>support_set pf. integrable N (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w)"
  proof (intro allI ballI)
    fix n
    fix asset
    assume "asset\<in>support_set pf"
    show "integrable N (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w)"
    proof (rule prob_space.finite_borel_measurable_integrable)
      show "prob_space N" using assms unfolding risk_neutral_prob_def by auto
      have "finite ((\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) ` space M)"
      proof -
        have "\<forall>y\<in> prices Mkt asset n `(space M). finite ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y)"
          by (metis \<open>asset \<in> support_set pf\<close> assms(7) finite_imageI image_image)
        hence "finite (\<Union> y\<in> prices Mkt asset n `(space M). ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y))"
          using \<open>asset \<in> support_set pf\<close> assms(6) by blast
        moreover have "(\<Union> y\<in> prices Mkt asset n `(space M). ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y)) =
          (\<Union> y\<in> prices Mkt asset n `(space M). (\<lambda>w. y * pf asset (Suc n) w) ` space M)"  by simp
        moreover have "((\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) ` space M) \<subseteq>
          (\<Union> y\<in> prices Mkt asset n `(space M). (\<lambda>w. y * pf asset (Suc n) w) ` space M)"
        proof
          fix x
          assume "x \<in> (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) ` space M"
          show "x \<in> (\<Union>y\<in>prices Mkt asset n ` space M. (\<lambda>w. y * pf asset (Suc n) w) ` space M)"
            using \<open>x \<in> (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) ` space M\<close> by auto
        qed
        ultimately show ?thesis by (simp add:finite_subset)
      qed
      thus "finite ((\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) ` space N)" using assms by (simp add:filt_equiv_space)
      have "(\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) \<in> borel_measurable M"
      proof -
        have "prices Mkt asset n \<in> borel_measurable M" using assms readable
          using \<open>asset \<in> support_set pf\<close> borel_adapt_stoch_proc_borel_measurable by blast
        moreover have "pf asset (Suc n) \<in> borel_measurable M" using assms unfolding trading_strategy_def
          using \<open>asset \<in> support_set pf\<close> borel_predict_stoch_proc_borel_measurable by blast
        ultimately show ?thesis by simp
      qed
      thus "(\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w) \<in> borel_measurable N" using assms by (simp add:filt_equiv_measurable)
    qed
  qed
  show "\<forall>n. \<forall>asset\<in>support_set pf. integrable N (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w)"
  proof (intro allI ballI)
    fix n
    fix asset
    assume "asset\<in>support_set pf"
    show "integrable N (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w)"
    proof (rule prob_space.finite_borel_measurable_integrable)
      show "prob_space N" using assms unfolding risk_neutral_prob_def by auto
      have "finite ((\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) ` space M)"
      proof -
        have "\<forall>y\<in> prices Mkt asset (Suc n) `(space M). finite ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y)"
          by (metis \<open>asset \<in> support_set pf\<close> assms(7) finite_imageI image_image)
        hence "finite (\<Union> y\<in> prices Mkt asset (Suc n) `(space M). ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y))"
          using \<open>asset \<in> support_set pf\<close> assms(6) by blast
        moreover have "(\<Union> y\<in> prices Mkt asset (Suc n) `(space M). ((\<lambda> z. (\<lambda>w. z * pf asset (Suc n) w) ` space M) y)) =
          (\<Union> y\<in> prices Mkt asset (Suc n) `(space M). (\<lambda>w. y * pf asset (Suc n) w) ` space M)"  by simp
        moreover have "((\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) ` space M) \<subseteq>
          (\<Union> y\<in> prices Mkt asset (Suc n) `(space M). (\<lambda>w. y * pf asset (Suc n) w) ` space M)"
        proof
          fix x
          assume "x \<in> (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) ` space M"
          show "x \<in> (\<Union>y\<in>prices Mkt asset (Suc n) ` space M. (\<lambda>w. y * pf asset (Suc n) w) ` space M)"
            using \<open>x \<in> (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) ` space M\<close> by auto
        qed
        ultimately show ?thesis by (simp add:finite_subset)
      qed
      thus "finite ((\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) ` space N)" using assms by (simp add:filt_equiv_space)
      have "(\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) \<in> borel_measurable M"
      proof -
        have "prices Mkt asset (Suc n) \<in> borel_measurable M" using assms readable
          using \<open>asset \<in> support_set pf\<close> borel_adapt_stoch_proc_borel_measurable by blast
        moreover have "pf asset (Suc n) \<in> borel_measurable M" using assms unfolding trading_strategy_def
          using \<open>asset \<in> support_set pf\<close> borel_predict_stoch_proc_borel_measurable by blast
        ultimately show ?thesis by simp
      qed
      thus "(\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w) \<in> borel_measurable N" using assms by (simp add:filt_equiv_measurable)
    qed
  qed
  show "stock_portfolio Mkt pf" using assms stock_portfolio_def
    by (simp add: stock_portfolio_def trading_strategy_def)
qed


lemma (in rfr_disc_equity_market) replicating_expectation:
  assumes "risk_neutral_prob N"
  and "filt_equiv F M N"
  and "replicating_portfolio pf pyf matur"
  and "\<forall>n. \<forall> asset \<in> support_set pf. integrable N (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w)"
  and "\<forall>n. \<forall> asset \<in> support_set pf. integrable N (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w)"
  and "viable_market Mkt"
  and "sets (F 0) = {{}, space M}"
  and "pyf  \<in> borel_measurable (F matur)"
shows "fair_price Mkt (prob_space.expectation N (discounted_value r (\<lambda>m. pyf) matur)) pyf matur"
proof -
  have fn: "filtrated_prob_space N F" using assms
    by (simp add: \<open>pyf \<in> borel_measurable (F matur)\<close> filtrated_prob_space_axioms.intro
        filtrated_prob_space_def risk_neutral_prob_def filt_equiv_filtration)
  have "discounted_value r (cls_val_process Mkt pf) matur \<in> borel_measurable N"
    using assms(3) disc_equity_market.replicating_portfolio_def disc_equity_market_axioms discounted_adapted
    filtrated_prob_space.borel_adapt_stoch_proc_borel_measurable fn cls_val_process_adapted
    by (metis (no_types, hide_lams) support_adapt_def readable  stock_portfolio_def subsetCE)
  have "discounted_value r (\<lambda>m. pyf) matur \<in> borel_measurable N"
  proof -
    have "(\<lambda>m. pyf) matur \<in> borel_measurable (F matur)" using assms by simp
    hence "(\<lambda>m. pyf) matur \<in> borel_measurable M"  using filtration filtrationE1 measurable_from_subalg by blast
    hence "(\<lambda>m. pyf) matur \<in> borel_measurable N" using assms by (simp add:filt_equiv_measurable)
    thus ?thesis by (simp add:discounted_measurable)
  qed
  have mpyf: "AE w in M. cls_val_process Mkt pf matur w = pyf w" using assms unfolding replicating_portfolio_def by simp
  have "AE w in N. cls_val_process Mkt pf matur w = pyf w"
  proof (rule filt_equiv_borel_AE_eq)
    show "filt_equiv F M N" using assms by simp
    show "pyf \<in> borel_measurable (F matur)" using assms by simp
    show "AE w in M. cls_val_process Mkt pf matur w = pyf w" using mpyf by simp
    show "cls_val_process Mkt pf matur \<in> borel_measurable (F matur)"
      using assms(3) price_structure_def replicating_price_process
      by (meson support_adapt_def disc_equity_market.replicating_portfolio_def disc_equity_market_axioms readable  stock_portfolio_def subsetCE)
  qed
  hence disc:"AE w in N. discounted_value r (cls_val_process Mkt pf) matur w = discounted_value r (\<lambda>m. pyf) matur w"
    by (simp add:discounted_AE_cong)
  have "AEeq N (real_cond_exp N (F 0) (discounted_value r (cls_val_process Mkt pf) matur))
    (real_cond_exp N (F 0) (discounted_value r (\<lambda>m. pyf) matur))"
  proof (rule sigma_finite_subalgebra.real_cond_exp_cong)
    show "sigma_finite_subalgebra N (F 0)"
      using filtrated_prob_space.axioms(1) filtrated_prob_space.filtration fn filtrationE1
        prob_space.subalgebra_sigma_finite by blast
    show "AEeq N (discounted_value r (cls_val_process Mkt pf) matur) (discounted_value r (\<lambda>m. pyf) matur)" using disc by simp
    show "discounted_value r (cls_val_process Mkt pf) matur \<in> borel_measurable N"
      using \<open>discounted_value r (cls_val_process Mkt pf) matur \<in> borel_measurable N\<close> .
    show "discounted_value r (\<lambda>m. pyf) matur \<in> borel_measurable N"
      using \<open>discounted_value r (\<lambda>m. pyf) matur \<in> borel_measurable N\<close> .
  qed
  have "martingale N F (discounted_value r (cls_val_process Mkt pf))" using assms unfolding replicating_portfolio_def
    using self_fin_trad_strat_mart[of N pf] by (simp add: stock_portfolio_def)
  hence "AEeq N (real_cond_exp N (F 0) (discounted_value r (cls_val_process Mkt pf) matur))
    (discounted_value r (cls_val_process Mkt pf) 0)" using martingaleAE[of N F "discounted_value r (cls_val_process Mkt pf)" 0 matur]
    fn by simp
  also have "AE w in N. (discounted_value r (cls_val_process Mkt pf) 0 w) = initial_value pf"
  proof
    fix w
    assume "w\<in> space N"
    have "discounted_value r (cls_val_process Mkt pf) 0 w = cls_val_process Mkt pf 0 w" by (simp add:discounted_init)
    also have "... = val_process Mkt pf 0 w" unfolding cls_val_process_def using assms
      unfolding replicating_portfolio_def stock_portfolio_def by simp
    also have "... = initial_value pf" using assms unfolding replicating_portfolio_def using \<open>w\<in> space N\<close>
      by (metis (no_types, lifting) support_adapt_def filt_equiv_space initial_valueI readable stock_portfolio_def subsetCE)
    finally show "discounted_value r (cls_val_process Mkt pf) 0 w = initial_value pf" .
  qed
  finally have "AE w in N. (real_cond_exp N (F 0) (discounted_value r (cls_val_process Mkt pf) matur)) w =
    initial_value pf" .
  moreover have "\<forall>w\<in> space N. (real_cond_exp N (F 0) (discounted_value r (cls_val_process Mkt pf) matur)) w =
    prob_space.expectation N (discounted_value r (cls_val_process Mkt pf) matur)"
  proof (rule prob_space.trivial_subalg_cond_expect_eq)
    show "prob_space N" using assms unfolding risk_neutral_prob_def by simp
    show "subalgebra N (F 0)"
      using \<open>prob_space N\<close> filtrated_prob_space.filtration fn filtrationE1 by blast
    show "sets (F 0) = {{}, space N}" using assms by (simp add:filt_equiv_space)
    show "integrable N (discounted_value r (cls_val_process Mkt pf) matur)"
    proof (rule discounted_integrable)
      show "space N = space M" using assms by (simp add:filt_equiv_space)
      show "integrable N (cls_val_process Mkt pf matur)" using assms unfolding replicating_portfolio_def
        by (simp add: integrable_self_fin_uvp)
      show "-1 < r" using acceptable_rate by simp
    qed
  qed
  ultimately have "AE w in N. prob_space.expectation N (discounted_value r (cls_val_process Mkt pf) matur) =
     initial_value pf" by simp
  hence "prob_space.expectation N (discounted_value r (cls_val_process Mkt pf) matur) =
    initial_value pf" using assms unfolding risk_neutral_prob_def using  prob_space.emeasure_space_1[of N]
    AE_eq_cst[of _ _ N] by simp
  moreover have "prob_space.expectation N (discounted_value r (cls_val_process Mkt pf) matur) =
    prob_space.expectation N (discounted_value r (\<lambda>m. pyf) matur)"
  proof (rule integral_cong_AE)
    show "AEeq N (discounted_value r (cls_val_process Mkt pf) matur) (discounted_value r (\<lambda>m. pyf) matur)"
      using disc by simp
    show "discounted_value r (\<lambda>m. pyf) matur \<in> borel_measurable N"
      using \<open>discounted_value r (\<lambda>m. pyf) matur \<in> borel_measurable N\<close> .
    show "discounted_value r (cls_val_process Mkt pf) matur \<in> borel_measurable N"
      using \<open>discounted_value r (cls_val_process Mkt pf) matur \<in> borel_measurable N\<close> .
  qed
  ultimately have "prob_space.expectation N (discounted_value r (\<lambda>m. pyf) matur) = initial_value pf" by simp
  thus ?thesis using assms
    by (metis (full_types) support_adapt_def disc_equity_market.replicating_portfolio_def disc_equity_market_axioms
        readable replicating_fair_price stock_portfolio_def subsetCE)
qed


lemma (in rfr_disc_equity_market) replicating_expectation_finite:
  assumes "risk_neutral_prob N"
  and "filt_equiv F M N"
  and "replicating_portfolio pf pyf matur"
  and "\<forall>n. \<forall> asset \<in> support_set pf. finite (prices Mkt asset n `(space M))"
  and "\<forall>n. \<forall> asset \<in> support_set pf. finite (pf asset n `(space M))"
  and "viable_market Mkt"
  and "sets (F 0) = {{}, space M}"
  and "pyf  \<in> borel_measurable (F matur)"
shows "fair_price Mkt (prob_space.expectation N (discounted_value r (\<lambda>m. pyf) matur)) pyf matur"
proof -
  have  "\<forall>n. \<forall> asset \<in> support_set pf. integrable N (\<lambda>w. prices Mkt asset n w * pf asset (Suc n) w)"
  proof (rule finite_integrable_vp, (auto simp add:assms))
    show "prob_space N" using assms unfolding risk_neutral_prob_def by simp
    show "trading_strategy pf" using assms unfolding replicating_portfolio_def by simp
    show "\<And>n asset. asset \<in> support_set pf \<Longrightarrow> random_variable borel (prices Mkt asset n)"
    proof-
      fix n
      fix asset
      assume "asset \<in> support_set pf"
      show "random_variable borel (prices Mkt asset n)"
        using assms unfolding replicating_portfolio_def stock_portfolio_def  adapt_stoch_proc_def using readable
        by (meson \<open>asset \<in> support_set pf\<close> adapt_stoch_proc_borel_measurable subsetCE)
    qed
  qed
  moreover have "\<forall>n. \<forall> asset \<in> support_set pf. integrable N (\<lambda>w. prices Mkt asset (Suc n) w * pf asset (Suc n) w)"
  proof (rule finite_integrable_uvp, (auto simp add:assms))
    show "prob_space N" using assms unfolding risk_neutral_prob_def by simp
    show "trading_strategy pf" using assms unfolding replicating_portfolio_def by simp
    show "\<And>n asset. asset \<in> support_set pf \<Longrightarrow> random_variable borel (prices Mkt asset n)"
    proof-
      fix n
      fix asset
      assume "asset \<in> support_set pf"
      show "random_variable borel (prices Mkt asset n)"
        using assms unfolding replicating_portfolio_def stock_portfolio_def  adapt_stoch_proc_def using readable
        by (meson \<open>asset \<in> support_set pf\<close> adapt_stoch_proc_borel_measurable subsetCE)
    qed
  qed
  ultimately show ?thesis using assms replicating_expectation by simp
qed



end