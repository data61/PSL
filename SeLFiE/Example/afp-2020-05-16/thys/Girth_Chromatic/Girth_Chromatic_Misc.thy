theory Girth_Chromatic_Misc
imports
  Main
  "HOL-Library.Extended_Real"
begin

section \<open>Auxilliary lemmas and setup\<close>

text \<open>
  This section contains facts about general concepts which are not directly
  connected to the proof of the Chromatic-Girth theorem. At some point in time,
  most of them could be moved to the Isabelle base library.

  Also, a little bit of setup happens.
\<close>

subsection \<open>Numbers\<close>

lemma enat_in_Inf:
  fixes S :: "enat set"
  assumes "Inf S \<noteq> top"
  shows "Inf S \<in> S"
proof (rule ccontr)
  assume A: "~?thesis"

  obtain n where Inf_conv: "Inf S = enat n" using assms by (auto simp: top_enat_def)
  { fix s assume "s \<in> S"
    then have "Inf S \<le> s" by (rule complete_lattice_class.Inf_lower)
    moreover have "Inf S \<noteq> s" using A \<open>s \<in> S\<close> by auto
    ultimately have "Inf S < s" by simp
    with Inf_conv have "enat (Suc n) \<le> s" by (cases s) auto
  }
  then have "enat (Suc n) \<le> Inf S" by (simp add: le_Inf_iff)
  with Inf_conv show False by auto
qed

lemma enat_in_INF:
  fixes f :: "'a \<Rightarrow> enat"
  assumes "(INF x\<in> S. f x) \<noteq> top"
  obtains x where "x \<in> S" and "(INF x\<in> S. f x) = f x"
proof -
  from assms have "(INF x\<in> S. f x) \<in> f ` S"
    using enat_in_Inf [of "f ` S"] by auto
  then obtain x where "x \<in> S" "(INF x\<in> S. f x) = f x" by auto
  then show ?thesis ..
qed

lemma enat_less_INF_I:
  fixes f :: "'a \<Rightarrow> enat"
  assumes not_inf: "x \<noteq> \<infinity>" and less: "\<And>y. y \<in> S \<Longrightarrow> x < f y"
  shows "x < (INF y\<in>S. f y)"
  using assms by (auto simp: Suc_ile_eq[symmetric] INF_greatest)

lemma enat_le_Sup_iff:
  "enat k \<le> Sup M \<longleftrightarrow> k = 0 \<or> (\<exists>m \<in> M. enat k \<le> m)" (is "?L \<longleftrightarrow> ?R")
proof cases
  assume "k = 0" then show ?thesis by (auto simp: enat_0)
next
  assume "k \<noteq> 0"
  show ?thesis
  proof
    assume ?L
    then have "\<lbrakk>enat k \<le> (if finite M then Max M else \<infinity>); M \<noteq> {}\<rbrakk> \<Longrightarrow> \<exists>m\<in>M. enat k \<le> m"
      by (metis Max_in Sup_enat_def finite_enat_bounded linorder_linear)
    with \<open>k \<noteq> 0\<close> and \<open>?L\<close> show ?R
      unfolding Sup_enat_def
      by (cases "M={}") (auto simp add: enat_0[symmetric])
  next
    assume ?R then show ?L
      by (auto simp: enat_0 intro: complete_lattice_class.Sup_upper2)
  qed
qed

lemma enat_neq_zero_cancel_iff[simp]:
  "0 \<noteq> enat n \<longleftrightarrow> 0 \<noteq> n"
  "enat n \<noteq> 0 \<longleftrightarrow> n \<noteq> 0"
by (auto simp: enat_0[symmetric])


lemma natceiling_lessD: "nat(ceiling x) < n \<Longrightarrow> x < real n"
by linarith

lemma le_natceiling_iff:
  fixes n :: nat and r :: real
  shows "n \<le> r \<Longrightarrow> n \<le> nat(ceiling r)"
by linarith

lemma natceiling_le_iff:
  fixes n :: nat and r :: real
  shows "r \<le> n \<Longrightarrow> nat(ceiling r) \<le> n"
by linarith

lemma dist_real_noabs_less:
  fixes a b c :: real assumes "dist a b < c" shows "a - b < c"
using assms by (simp add: dist_real_def)

lemma n_choose_2_nat:
  fixes n :: nat shows "(n choose 2) = (n * (n - 1)) div 2"
proof -
  show ?thesis
  proof (cases "2 \<le> n")
    case True
    then obtain m where "n = Suc (Suc m)"
      by (metis add_Suc le_Suc_ex numeral_2_eq_2)
    moreover have "(n choose 2) = (fact n div fact (n - 2)) div 2"
      using \<open>2 \<le> n\<close> by (simp add: binomial_altdef_nat
        div_mult2_eq[symmetric] mult.commute numeral_2_eq_2)
    ultimately show ?thesis by (simp add: algebra_simps)
  qed (auto simp: binomial_eq_0)
qed

lemma powr_less_one:
  fixes x::real
  assumes "1 < x" "y < 0"
  shows "x powr y < 1"
using assms less_log_iff by force

lemma powr_le_one_le: "\<And>x y::real. 0 < x \<Longrightarrow> x \<le> 1 \<Longrightarrow> 1 \<le> y \<Longrightarrow> x powr y \<le> x"
proof -
  fix x y :: real
  assume "0 < x" "x \<le> 1" "1 \<le> y"
  have "x powr y = (1 / (1 / x)) powr y" using \<open>0 < x\<close> by (simp add: field_simps)
  also have "\<dots> = 1 / (1 / x) powr y" using \<open>0 < x\<close> by (simp add: powr_divide)
  also have "\<dots> \<le> 1 / (1 / x) powr 1" proof -
    have "1 \<le> 1 / x" using \<open>0 < x\<close> \<open>x \<le> 1\<close> by (auto simp: field_simps)
    then have "(1 / x) powr 1  \<le> (1 / x) powr y" using \<open>0 < x\<close>
      using \<open>1 \<le> y\<close> by ( simp only: powr_mono)
    then show ?thesis
      by (metis \<open>1 \<le> 1 / x\<close> \<open>1 \<le> y\<close> neg_le_iff_le powr_minus_divide powr_mono)
  qed
  also have "\<dots> \<le> x" using \<open>0 < x\<close> by (auto simp: field_simps)
  finally show "?thesis x y" .
qed


subsection \<open>Lists and Sets\<close>

lemma list_set_tl: "x \<in> set (tl xs) \<Longrightarrow> x \<in> set xs"
by (cases xs) auto

lemma list_exhaust3:
  obtains "xs = []" | x where "xs = [x]" | x y ys where "xs = x # y # ys"
by (metis list.exhaust)

lemma card_Ex_subset:
  "k \<le> card M \<Longrightarrow> \<exists>N. N \<subseteq> M \<and> card N = k"
by (induct rule: inc_induct) (auto simp: card_Suc_eq)



subsection \<open>Limits and eventually\<close>

text \<open>
  We employ filters and the @{term eventually} predicate to deal with the
  @{term "\<exists>N. \<forall>n\<ge>N. P n"} cases. To make this more convenient, introduce
  a shorter syntax.
\<close>

abbreviation evseq :: "(nat \<Rightarrow> bool) \<Rightarrow> bool" (binder "\<forall>\<^sup>\<infinity>" 10) where
  "evseq P \<equiv> eventually P sequentially"

lemma eventually_le_le:
  fixes P :: "'a => ('b :: preorder)"
  assumes "eventually (\<lambda>x. P x \<le> Q x) net"
  assumes "eventually (\<lambda>x. Q x \<le> R  x) net"
  shows "eventually (\<lambda>x. P x \<le> R x) net"
using assms by eventually_elim (rule order_trans)

lemma LIMSEQ_neg_powr:
  assumes s: "s < 0"
  shows "(%x. (real x) powr s) \<longlonglongrightarrow> 0"
by (rule tendsto_neg_powr[OF assms filterlim_real_sequentially])

lemma LIMSEQ_inv_powr:
  assumes "0 < c" "0 < d"
  shows "(\<lambda>n :: nat. (c / n) powr d) \<longlonglongrightarrow> 0"
proof (rule tendsto_zero_powrI)
  from \<open>0 < c\<close> have "\<And>x. 0 < x \<Longrightarrow> 0 < c / x" by simp
  then show "\<forall>\<^sup>\<infinity>n. 0 \<le> c / real n"
    using assms(1) by auto
  show "(\<lambda>x. c / real x) \<longlonglongrightarrow> 0"
    by (intro tendsto_divide_0[OF tendsto_const] filterlim_at_top_imp_at_infinity
              filterlim_real_sequentially tendsto_divide_0)
  show "0 < d" by (rule assms)
  show "(\<lambda>x. d) \<longlonglongrightarrow> d" by auto
qed


end
