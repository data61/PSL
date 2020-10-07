(*
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Mojmir Automata\<close>

theory Mojmir
  imports Main Semi_Mojmir
begin

subsection \<open>Definitions\<close>

locale mojmir_def = semi_mojmir_def +
  fixes
    \<comment> \<open>Final States\<close>
    F :: "'b set"
begin

definition token_succeeds :: "nat \<Rightarrow> bool"
where
  "token_succeeds x = (\<exists>n. token_run x n \<in> F)"

definition token_fails :: "nat \<Rightarrow> bool"
where
  "token_fails x = (\<exists>n. sink (token_run x n) \<and> token_run x n \<notin> F)"

definition accept :: "bool" ("accept\<^sub>M")
where
  "accept \<longleftrightarrow> (\<forall>\<^sub>\<infinity>x. token_succeeds x)"

definition fail :: "nat set"
where
  "fail = {x. token_fails x}"

definition merge :: "nat \<Rightarrow> (nat \<times> nat) set"
where
  "merge i = {(x, y) | x y n j. j < i
    \<and> (token_run x n \<noteq> token_run y n \<and> rank y n \<noteq> None \<or> y = Suc n)
    \<and> token_run x (Suc n) = token_run y (Suc n)
    \<and> token_run x (Suc n) \<notin> F
    \<and> rank x n = Some j}"

definition succeed :: "nat \<Rightarrow> nat set"
where
  "succeed i = {x. \<exists>n. rank x n = Some i
    \<and> token_run x n \<notin> F - {q\<^sub>0}
    \<and> token_run x (Suc n) \<in> F}"

definition smallest_accepting_rank :: "nat option"
where
  "smallest_accepting_rank \<equiv> (if accept then
    Some (LEAST i. finite fail \<and> finite (merge i) \<and> infinite (succeed i)) else None)"

definition fail_t :: "nat set"
where
  "fail_t = {n. \<exists>q q'. state_rank q n \<noteq> None \<and> q' = \<delta> q (w n) \<and> q' \<notin> F \<and> sink q'}"

definition merge_t :: "nat \<Rightarrow> nat set"
where
  "merge_t i = {n. \<exists>q q' j. state_rank q n = Some j \<and> j < i \<and> q' = \<delta> q (w n) \<and> q' \<notin> F \<and>
    ((\<exists>q''. q'' \<noteq> q \<and> q' = \<delta> q'' (w n) \<and> state_rank q'' n \<noteq> None) \<or> q' = q\<^sub>0)}"

definition succeed_t :: "nat \<Rightarrow> nat set"
where
  "succeed_t i = {n. \<exists>q. state_rank q n = Some i \<and> q \<notin> F - {q\<^sub>0} \<and> \<delta> q (w n) \<in> F}"

fun "\<S>"
where
  "\<S> n = F \<union> {q. (\<exists>j \<ge> the smallest_accepting_rank. state_rank q n = Some j)}"

end

locale mojmir = semi_mojmir + mojmir_def +
  assumes
    \<comment> \<open>All states reachable from final states are also final\<close>
    wellformed_F: "\<And>q \<nu>. q \<in> F \<Longrightarrow> \<delta> q \<nu> \<in> F"
begin

lemma token_stays_in_final_states:
  "token_run x n \<in> F \<Longrightarrow> token_run x (n + m) \<in> F"
proof (induction m)
  case (Suc m)
    thus ?case
    proof (cases "n + m < x")
      case False
        hence "n + m \<ge> x"
          by arith
        then obtain j where "n + m = x + j"
          using le_Suc_ex by blast
        hence "\<delta> (token_run x (n + m)) (suffix x w j) = token_run x (n + (Suc m))"
          unfolding suffix_def by fastforce
        thus ?thesis
          using wellformed_F Suc suffix_nth by (metis (no_types, hide_lams))
    qed fastforce
qed simp

lemma token_run_enter_final_states:
  assumes "token_run x n \<in> F"
  shows "\<exists>m \<ge> x. token_run x m \<notin> F - {q\<^sub>0} \<and> token_run x (Suc m) \<in> F"
proof (cases "x \<le> n")
  case True
    then obtain n' where "token_run x (x + n') \<in> F"
      using assms by force
    hence "\<exists>m. token_run x (x + m) \<notin> F - {q\<^sub>0} \<and> token_run x (x + Suc m) \<in> F"
      by (induction n') ((metis (erased, hide_lams) token_stays_in_final_states token_run_intial_state  Diff_iff Nat.add_0_right Suc_eq_plus1 insertCI ), blast)
    thus ?thesis
      by (metis add_Suc_right le_add1)
next
  case False
    hence "token_run x x \<notin> F - {q\<^sub>0}" and "token_run x (Suc x) \<in> F"
      using assms wellformed_F by simp_all
    thus ?thesis
      by blast
qed

subsection \<open>Token Properties\<close>

subsubsection \<open>Alternative Definitions\<close>

lemma token_succeeds_alt_def:
  "token_succeeds x = (\<forall>\<^sub>\<infinity>n. token_run x n \<in> F)"
  unfolding token_succeeds_def MOST_nat_le le_iff_add
  using token_stays_in_final_states by blast

lemma token_fails_alt_def:
  "token_fails x = (\<forall>\<^sub>\<infinity>n. sink (token_run x n) \<and> token_run x n \<notin> F)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then obtain n where "sink (token_run x n)" and "token_run x n \<notin> F"
    using token_fails_def by blast
  hence "\<forall>m \<ge> n. sink (token_run x m)" and "\<forall>m \<ge> n. token_run x m \<notin> F"
    using token_stays_in_sink unfolding le_iff_add by auto
  thus ?rhs
    unfolding MOST_nat_le by blast
qed (unfold MOST_nat_le token_fails_def, blast)

lemma token_fails_alt_def_2:
  "token_fails x \<longleftrightarrow> \<not>token_succeeds x \<and> \<not>token_squats x"
  by (metis add.commute token_fails_def token_squats_def token_stays_in_final_states token_stays_in_sink token_succeeds_def)

subsubsection \<open>Properties\<close>

lemma token_succeeds_run_merge:
  "x \<le> n \<Longrightarrow> y \<le> n \<Longrightarrow> token_run x n = token_run y n \<Longrightarrow> token_succeeds x \<Longrightarrow> token_succeeds y"
  using token_run_merge token_stays_in_final_states add.commute unfolding token_succeeds_def by metis

lemma token_squats_run_merge:
  "x \<le> n \<Longrightarrow> y \<le> n \<Longrightarrow> token_run x n = token_run y n \<Longrightarrow> token_squats x \<Longrightarrow> token_squats y"
  using token_run_merge token_stays_in_sink add.commute unfolding token_squats_def by metis

subsubsection \<open>Pulled-Up Lemmas\<close>

lemma configuration_token_succeeds:
  "\<lbrakk>x \<in> configuration q n; y \<in> configuration q n\<rbrakk> \<Longrightarrow> token_succeeds x = token_succeeds y"
  using token_succeeds_run_merge push_down_configuration_token_run by meson

lemma configuration_token_squats:
  "\<lbrakk>x \<in> configuration q n; y \<in> configuration q n\<rbrakk> \<Longrightarrow> token_squats x = token_squats y"
  using token_squats_run_merge push_down_configuration_token_run by meson

subsection \<open>Mojmir Acceptance\<close>

lemma Mojmir_reject:
  "\<not> accept \<longleftrightarrow> (\<exists>\<^sub>\<infinity>x. \<not>token_succeeds x)"
  unfolding accept_def Alm_all_def by blast

lemma mojmir_accept_alt_def:
  "accept \<longleftrightarrow> finite {x. \<not>token_succeeds x}"
  using Inf_many_def Mojmir_reject by blast

lemma mojmir_accept_initial:
  "q\<^sub>0 \<in> F \<Longrightarrow> accept"
  unfolding accept_def MOST_nat_le token_succeeds_def
  using token_run_intial_state by metis

subsection \<open>Equivalent Acceptance Conditions\<close>

subsubsection \<open>Token-Based Definitions\<close>

lemma merge_token_succeeds:
  assumes "(x, y) \<in> merge i"
  shows "token_succeeds x \<longleftrightarrow> token_succeeds y"
proof -
  obtain n j j' where "token_run x (Suc n) = token_run y (Suc n)"
    and "rank x n = Some j" and "rank y n = Some j' \<or> y = Suc n"
    using assms unfolding merge_def by blast
  hence "x \<le> Suc n" and "y \<le> Suc n"
    using rank_Some_time le_Suc_eq by blast+
  then obtain q where "x \<in> configuration q (Suc n)" and "y \<in> configuration q (Suc n)"
    using \<open>token_run x (Suc n) = token_run y (Suc n)\<close> pull_up_token_run_tokens by blast
  thus ?thesis
    using configuration_token_succeeds by blast
qed

lemma merge_subset:
   "i \<le> j \<Longrightarrow> merge i \<subseteq> merge j"
proof
  assume "i \<le> j"
  fix p
  assume "p \<in> merge i"
  then obtain x y n k where "p = (x, y)" and "k < i" and "token_run x n \<noteq> token_run y n \<and> rank y n \<noteq> None \<or> y = Suc n"
    and "token_run x (Suc n) = token_run y (Suc n)" and "token_run x (Suc n) \<notin> F" and "rank x n = Some k"
    unfolding merge_def by blast
  moreover
  hence "k < j"
    using \<open>i \<le> j\<close> by simp
  ultimately
  have "(x, y) \<in> merge j"
    unfolding merge_def by blast
  thus "p \<in> merge j"
    using \<open>p = (x, y)\<close> by simp
qed

lemma merge_finite:
  "i \<le> j \<Longrightarrow> finite (merge j) \<Longrightarrow> finite (merge i)"
  using merge_subset by (blast intro: rev_finite_subset)

lemma merge_finite':
  "i < j \<Longrightarrow> finite (merge j) \<Longrightarrow> finite (merge i)"
  using merge_finite[of i j] by force

lemma succeed_membership:
  "token_succeeds x \<longleftrightarrow> (\<exists>i. x \<in> succeed i)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain m where "token_run x m \<in> F"
    unfolding token_succeeds_alt_def MOST_nat_le by blast
  then obtain n where 1: "token_run x n \<notin> F - {q\<^sub>0}"
    and 2: "token_run x (Suc n) \<in> F" and "x \<le> n"
    using token_run_enter_final_states by blast
  moreover
  hence "\<not>sink (token_run x n)"
  proof (cases "token_run x n \<noteq> q\<^sub>0")
    case True
      hence "token_run x n \<notin> F"
        using \<open>token_run x n \<notin> F - {q\<^sub>0}\<close> by blast
      thus ?thesis
        using \<open>token_run x (Suc n) \<in> F\<close> token_stays_in_sink unfolding Suc_eq_plus1 by metis
  qed (simp add: sink_def)
  then obtain i where "rank x n = Some i"
    using \<open>x \<le> n\<close> by fastforce
  ultimately
  show ?rhs
    unfolding succeed_def by blast
qed (unfold token_succeeds_def succeed_def, blast)

lemma stable_rank_succeed:
  assumes "infinite (succeed i)"
      and "x \<in> succeed i"
      and "q\<^sub>0 \<notin> F"
  shows "\<not>stable_rank x i"
proof
  assume "stable_rank x i"
  then obtain n where "\<forall>n' \<ge> n. rank x n' = Some i"
    unfolding stable_rank_def MOST_nat_le by rule

  from assms(2) obtain m where "token_run x m \<notin> F"
    and "token_run x (Suc m) \<in> F"
    and "rank x m = Some i"
    using assms(3) unfolding succeed_def by force

  obtain y where "y > max n m" and "y \<in> succeed i"
    using assms(1) unfolding infinite_nat_iff_unbounded by blast

  then obtain m' where "token_run y m' \<notin> F"
    and "token_run y (Suc m') \<in> F"
    and "rank y m' = Some i"
    using assms(3) unfolding succeed_def by force

  moreover

  \<comment> \<open>token has still rank i at m'\<close>
  have "m' \<ge> n"
    using rank_Some_time[OF \<open>rank y m' = Some i\<close>] \<open>y > max n m\<close> by force
  hence "rank x m' = Some i"
    using  \<open>\<forall>n' \<ge> n. rank x n' = Some i\<close> by blast

  moreover

  \<comment> \<open>but x and y are not in the same state\<close>
  have "m' \<ge> Suc m"
    using rank_Some_time[OF \<open>rank y m' = Some i\<close>] \<open>y > max n m\<close> by force
  hence "token_run x m' \<in> F"
    using token_stays_in_final_states[OF \<open>token_run x (Suc m) \<in> F\<close>]
    unfolding le_iff_add by fast
  with \<open>token_run y m' \<notin> F \<close> have "token_run y m' \<noteq> token_run x m'"
    by metis

  ultimately

  show "False"
    using push_down_rank_tokens by force
qed

lemma stable_rank_bounded:
  assumes stable: "stable_rank x j"
  assumes inf: "infinite (succeed i)"
  assumes "q\<^sub>0 \<notin> F"
  shows "j < i"
proof -
  from stable obtain m where "\<forall>m' \<ge> m. rank x m' = Some j"
    unfolding stable_rank_def MOST_nat_le by rule
  from inf obtain y where "y \<ge> m" and "y \<in> succeed i"
    unfolding infinite_nat_iff_unbounded_le by meson
  then obtain n where "rank y n = Some i"
    unfolding succeed_def MOST_nat_le by blast

  moreover

  hence "n \<ge> y"
    by (rule rank_Some_time)
  hence "rank x n = Some j"
    using \<open>\<forall>m' \<ge> m. rank x m' = Some j\<close> \<open>y \<ge> m\<close> by fastforce

  ultimately

  \<comment> \<open>In the case @{term "i \<le> j"}, the token y has also to stabilise with @{term i} at @{term n}.\<close>
  have "i \<le> j \<Longrightarrow> stable_rank y i"
    using stable by (blast intro: stable_rank_tower)
  thus "j < i"
    using stable_rank_succeed[OF inf \<open>y \<in> succeed i\<close> \<open>q\<^sub>0 \<notin> F\<close>] by linarith
qed

\<comment> \<open>Relation to Mojmir Acceptance\<close>

lemma mojmir_accept_token_set_def1:
  assumes "accept"
  shows "\<exists>i < max_rank. finite fail \<and> finite (merge i) \<and> infinite (succeed i) \<and> (\<forall>j < i. finite (succeed j))"
proof (rule+)
  define i where "i = (LEAST k. infinite (succeed k))"

  from assms have "infinite {t. token_succeeds t}"
    unfolding mojmir_accept_alt_def by force

  moreover

  have "{x. token_succeeds x} = \<Union>{succeed i | i. i < max_rank}"
    (is "?lhs = ?rhs")
  proof -
    have "?lhs = \<Union>{succeed i | i. True}"
      using succeed_membership by blast
    also
    have "\<dots> = ?rhs"
    proof
      show "\<dots> \<subseteq> ?rhs"
      proof
        fix x
        assume "x \<in> \<Union>{succeed i |i. True}"
        then obtain i where "x \<in> succeed i"
          by blast
        moreover
        \<comment> \<open>Obtain upper bound for succeed ranks\<close>
        have "\<And>u. u \<ge> max_rank \<Longrightarrow> succeed u = {}"
          unfolding succeed_def using rank_upper_bound by fastforce
        ultimately
        show "x \<in> \<Union>{succeed i |i. i < max_rank}"
          by (cases "i < max_rank") (blast, simp)
      qed
    qed blast
    finally
    show ?thesis .
  qed

  ultimately

  have "\<exists>j. infinite (succeed j)"
    by force
  hence "infinite (succeed i)" and "\<And>j. j < i \<Longrightarrow> finite (succeed j)"
    unfolding i_def by (metis LeastI_ex, metis not_less_Least)
  hence fin_succeed_ranks: "finite (\<Union>{succeed j | j. j < i})"
    by auto

  \<comment> \<open>@{term i} is bounded by @{term max_rank}\<close>
  {
    obtain x where "x \<in> succeed i"
      using \<open>infinite (succeed i)\<close> by fastforce
    then obtain n where "rank x n = Some i"
      unfolding succeed_def by blast
    thus "i < max_rank"
      by (rule rank_upper_bound)
  }

  define S where "S = {(x, y). token_succeeds x \<and> token_succeeds y}"

  have "finite (merge i \<inter> S)"
  proof (rule finite_product)
    {
      fix x y
      assume "(x, y) \<in> (merge i \<inter> S)"

      then obtain n k k'' where "k < i"
        and "rank x n = Some k"
        and "rank y n = Some k'' \<or> y = Suc n"
        and "token_run x (Suc n) \<notin> F"
        and "token_run x (Suc n) = token_run y (Suc n)"
        and "token_succeeds x"
        unfolding merge_def S_def by fast

      then obtain m where "token_run x (Suc n + m) \<notin> F"
        and "token_run x (Suc (Suc n + m)) \<in> F"
        by (metis Suc_eq_plus1 add.commute token_run_P[of "\<lambda>q. q \<in> F"] token_stays_in_final_states token_succeeds_def)

      moreover

      have "x \<le> Suc n" and "y \<le> Suc n" and "x \<le> Suc n + m" and "y \<le> Suc n + m"
        using rank_Some_time \<open>rank x n = Some k\<close> \<open>rank y n = Some k'' \<or> y = Suc n\<close> by fastforce+

      hence "token_run y (Suc n + m) \<notin> F" and "token_run y (Suc (Suc n + m)) \<in> F"
        using \<open>token_run x (Suc n + m) \<notin> F\<close> \<open>token_run x (Suc (Suc n + m)) \<in> F\<close> \<open>token_run x (Suc n) = token_run y (Suc n)\<close>
        using token_run_merge token_run_merge_Suc by metis+

      moreover

      have "\<not>sink (token_run x (Suc n + m))"
        using \<open>token_run x (Suc n + m) \<notin> F\<close> \<open>token_run x (Suc(Suc n + m)) \<in> F\<close>
        using token_is_not_in_sink by blast

      \<comment> \<open>Obtain rank used to enter final\<close>
      obtain k' where "rank x (Suc n + m) = Some k'"
        using \<open>\<not>sink (token_run x (Suc n + m))\<close> \<open>x \<le> Suc n + m\<close> by fastforce

      moreover

      hence "rank y (Suc n + m) = Some k'"
        by (metis \<open>x \<le> Suc n + m\<close> \<open>y \<le> Suc n + m\<close> token_run_merge \<open>x \<le> Suc n\<close> \<open>y \<le> Suc n\<close>
                  \<open>token_run x (Suc n) = token_run y (Suc n)\<close> pull_up_token_run_tokens
                  pull_up_configuration_rank[of x _ "Suc n + m" y])

      moreover

      \<comment> \<open>Rank used to enter final states is strictly bounded by i\<close>
      have "k' < i"
        using \<open>rank x (Suc n + m) = Some k'\<close> rank_monotonic[OF \<open>rank x n = Some k\<close>] \<open>k < i\<close>
        unfolding add_Suc_shift by fastforce

      ultimately

      have "x \<in> \<Union>{succeed j | j. j < i}" and "y \<in> \<Union>{succeed j | j. j < i}"
        unfolding succeed_def by blast+
    }
    hence "fst ` (merge i \<inter> S) \<subseteq> \<Union>{succeed j | j. j < i}" and "snd ` (merge i \<inter> S) \<subseteq> \<Union>{succeed j | j. j < i}"
      by force+
    thus "finite (fst ` (merge i \<inter> S))" and "finite (snd ` (merge i \<inter> S))"
      using finite_subset[OF _ fin_succeed_ranks] by meson+
  qed

  moreover

  have "finite (merge i \<inter> (UNIV - S))"
  proof -
    obtain l where l_def: "\<forall>x \<ge> l. token_succeeds x"
      using assms unfolding accept_def MOST_nat_le by blast
    {
      fix x y
      assume "(x, y) \<in> merge i \<inter> (UNIV - S)"
      hence "\<not>token_succeeds x \<or> \<not>token_succeeds y"
        unfolding S_def by simp
      hence "\<not>token_succeeds x \<and> \<not>token_succeeds y"
        using merge_token_succeeds \<open>(x, y) \<in> merge i \<inter> (UNIV - S)\<close> by blast
      hence "x < l" and "y < l"
        by (metis l_def le_eq_less_or_eq linear)+
    }
    hence "merge i \<inter> (UNIV - S) \<subseteq> {0..l} \<times> {0..l}"
      by fastforce
    thus ?thesis
      using finite_subset by blast
  qed

  ultimately

  have "finite (merge i)"
    by (metis Int_Diff Un_Diff_Int finite_UnI inf_top_right)
  moreover
  have "finite fail"
    by (metis assms mojmir_accept_alt_def fail_def token_fails_alt_def_2 infinite_nat_iff_unbounded_le mem_Collect_eq)
  ultimately
  show "finite fail \<and> finite (merge i) \<and> infinite (succeed i) \<and> (\<forall>j < i. finite (succeed j))"
    using \<open>infinite (succeed i)\<close> \<open>\<And>j. j < i \<Longrightarrow> finite (succeed j)\<close> by blast
qed

lemma mojmir_accept_token_set_def2:
  assumes "finite fail"
      and "finite (merge i)"
      and "infinite (succeed i)"
  shows "accept"
proof (rule ccontr, cases "q\<^sub>0 \<notin> F")
  case True
    assume "\<not> accept"
    moreover
    have "finite {x. \<not>token_succeeds x \<and> \<not>token_squats x}"
      using \<open>finite fail\<close> unfolding fail_def token_fails_alt_def_2[symmetric] .
    moreover
    have X: "{x. \<not> token_succeeds x} = {x. \<not> token_succeeds x \<and> token_squats x} \<union> {x. \<not> token_succeeds x \<and> \<not> token_squats x}"
      by blast
    ultimately
    have inf: "infinite {x. \<not>token_succeeds x \<and> token_squats x}"
      unfolding mojmir_accept_alt_def X by blast

    \<comment> \<open>Obtain j, where j is the rank used by infinitely many configuration stabilising and not succeeding\<close>
    have "{x. \<not>token_succeeds x \<and> token_squats x} = {x. \<exists>j < i. \<not>token_succeeds x \<and> token_squats x \<and> stable_rank x j}"
      using stable_rank_bounded \<open>infinite (succeed i)\<close> \<open>q\<^sub>0 \<notin> F\<close>
      unfolding stable_rank_equiv_token_squats by metis
    also
    have "\<dots> = \<Union>{{x.  \<not>token_succeeds x \<and> token_squats x \<and> stable_rank x j} | j. j < i}"
      by blast
    finally
    obtain j where "j < i" and "infinite {t. \<not>token_succeeds t \<and> token_squats t \<and> stable_rank t j}"
      (is "infinite ?S")
      using inf by force

    \<comment> \<open>Obtain such a token x\<close>
    then obtain x where "\<not>token_succeeds x" and "token_squats x" and "stable_rank x j"
      unfolding infinite_nat_iff_unbounded_le by blast
    then obtain n where "\<forall>m \<ge> n. rank x m = Some j"
      unfolding stable_rank_def MOST_nat_le by blast

    \<comment> \<open>All configuration with same stable rank are bought at some n with rank smaller i\<close>
    have "{(x, y) | y. y > n \<and> stable_rank y j} \<subseteq> merge i"
      (is "?lhs \<subseteq> ?rhs")
    proof
      fix p
      assume "p \<in> ?lhs"
      then obtain y where "p = (x, y)" and "y > n" and "stable_rank y j"
        by blast
      hence "x < y" and "x \<noteq> y"
        using rank_Some_time \<open>\<forall>n'\<ge>n. rank x n' = Some j\<close> by fastforce+

      moreover

      \<comment> \<open>Obtain a time n'' where x and y have the same rank\<close>
      obtain n'' where "rank x n'' = Some j" and "rank y n'' = Some j"
        using \<open>\<forall>n'\<ge>n. rank x n' = Some j\<close> \<open>stable_rank y j\<close>
        unfolding stable_rank_def MOST_nat_le by (metis add.commute le_add2)
      hence "token_run x n'' = token_run y n''" and "y \<le> n''"
        using push_down_rank_tokens rank_Some_time[OF \<open>rank y n'' = Some j\<close>] by simp_all

      \<comment> \<open>Obtain the time n' where x merges y and proof all necessary properties\<close>
      then obtain n' where "token_run x n' \<noteq> token_run y n' \<or> y = Suc n'"
        and "token_run x (Suc n') = token_run y (Suc n')" and "y \<le> Suc n'"
        using token_run_mergepoint[OF \<open>x < y\<close>] le_add_diff_inverse by metis

      moreover

      hence "(\<exists>j'. rank y n' = Some j') \<or> y = Suc n'"
        using \<open>stable_rank y j\<close> stable_rank_equiv_token_squats rank_token_squats
        unfolding le_Suc_eq by blast

      moreover

      have "rank x n' = Some j"
        using \<open>\<forall>n'\<ge>n. rank x n' = Some j\<close> \<open>y \<le> Suc n'\<close> \<open>y > n\<close> by fastforce

      moreover

      have "token_run x (Suc n') \<notin> F"
        using \<open>\<not> token_succeeds x\<close> token_succeeds_def by blast

      ultimately
      show "p \<in> ?rhs"
        unfolding merge_def \<open>p = (x, y)\<close>
        using \<open>j < i\<close> by blast
    qed

    moreover

    \<comment> \<open>However, x merges infinitely many configuration\<close>
    hence "infinite {(x, y) | y. y > n \<and> stable_rank y j}"
      (is "infinite ?S'")
    proof -
      {
        {
          fix y
          assume "stable_rank y j" and "y > n"
          then obtain n' where "rank y n' = Some j"
            unfolding stable_rank_def MOST_nat_le by blast
          moreover
          hence "y \<le> n'"
            by (rule rank_Some_time)
          hence "n' > n"
            using \<open>y > n\<close> by arith
          hence "rank x n' = Some j"
            using \<open>\<forall>n' \<ge> n. rank x n' = Some j\<close> by simp
          ultimately
          have "\<not>token_succeeds y"
            by (metis \<open>\<not>token_succeeds x\<close> configuration_token_succeeds push_down_rank_tokens)
        }
        hence "{y | y. y > n \<and> stable_rank y j} = {y | y. token_squats y \<and> \<not>token_succeeds y \<and> stable_rank y j \<and>  y > n}"
          (is "_ = ?S''")
          using stable_rank_equiv_token_squats by blast
        moreover
        have "finite {y | y. token_squats y \<and> \<not>token_succeeds y \<and> stable_rank y j \<and>  y \<le> n}"
          (is "finite ?S'''")
          by simp
        moreover
        have "?S = ?S'' \<union> ?S'''"
          by auto
        ultimately
        have "infinite {y | y. y > n \<and> stable_rank y j}"
          using \<open>infinite ?S\<close> by simp
      }
      moreover
      have "{x} \<times> {y. y > n \<and> stable_rank y j} = ?S'"
        by auto
      ultimately
      show ?thesis
        by (metis empty_iff finite_cartesian_productD2 singletonI)
    qed

    ultimately

    have "infinite (merge i)"
      by (rule infinite_super)
    with \<open>finite (merge i)\<close> show "False"
      by blast
qed (blast intro: mojmir_accept_initial)

theorem mojmir_accept_iff_token_set_accept:
  "accept \<longleftrightarrow> (\<exists>i < max_rank. finite fail \<and> finite (merge i) \<and> infinite (succeed i))"
  using mojmir_accept_token_set_def1 mojmir_accept_token_set_def2 by blast

theorem mojmir_accept_iff_token_set_accept2:
  "accept \<longleftrightarrow> (\<exists>i < max_rank. finite fail \<and> finite (merge i) \<and> infinite (succeed i) \<and> (\<forall>j < i. finite (merge j) \<and> finite (succeed j)))"
  using mojmir_accept_token_set_def1 mojmir_accept_token_set_def2 merge_finite' by blast

subsubsection \<open>Time-Based Definitions\<close>

\<comment> \<open>Proof Rules\<close>

lemma finite_monotonic_image:
  fixes A B :: "nat set"
  assumes "\<And>i. i \<in> A \<Longrightarrow> i \<le> f i"
  assumes "f ` A = B"
  shows "finite A \<longleftrightarrow> finite B"
proof
  assume "finite B"
  thus "finite A"
  proof (cases "B \<noteq> {}")
    case True
      hence "\<And>i. i \<in> A \<Longrightarrow> i \<le> Max B"
        by (metis assms Max_ge_iff \<open>finite B\<close> imageI)
      thus "finite A"
        unfolding finite_nat_set_iff_bounded_le by blast
  qed (metis assms(2) image_is_empty)
qed (metis assms(2) finite_imageI)

lemma finite_monotonic_image_pairs:
  fixes A :: "(nat \<times> nat) set"
  fixes B :: "nat set"
  assumes "\<And>i. i \<in> A \<Longrightarrow> (fst i) \<le> f i + c"
  assumes "\<And>i. i \<in> A \<Longrightarrow> (snd i) \<le> f i + d"
  assumes "f ` A = B"
  shows "finite A \<longleftrightarrow> finite B"
proof
  assume "finite B"
  thus "finite A"
  proof (cases "B \<noteq> {}")
    case True
      hence "\<And>i. i \<in> A \<Longrightarrow> fst i \<le> Max B + c \<and> snd i \<le> Max B + d"
        by (metis assms Max_ge_iff \<open>finite B\<close> imageI le_diff_conv)
      thus "finite A"
        using finite_product[of A] unfolding finite_nat_set_iff_bounded_le by blast
  qed (metis assms(3) finite.emptyI image_is_empty)
qed (metis assms(3) finite_imageI)

lemma token_time_finite_rule:
  fixes A B :: "nat set"
  assumes unique:  "\<And>x y z. P x y \<Longrightarrow> P x z \<Longrightarrow> y = z"
      and existsA: "\<And>x. x \<in> A \<Longrightarrow> (\<exists>y. P x y)"
      and existsB: "\<And>y. y \<in> B \<Longrightarrow> (\<exists>x. P x y)"
      and inA:     "\<And>x y. P x y \<Longrightarrow> x \<in> A"
      and inB:     "\<And>x y. P x y \<Longrightarrow> y \<in> B"
      and mono:    "\<And>x y. P x y \<Longrightarrow> x \<le> y"
  shows "finite A \<longleftrightarrow> finite B"
proof (rule finite_monotonic_image)
  let ?f = "(\<lambda>x. if x \<in> A then The (P x) else undefined)"

  {
    fix x
    assume "x \<in> A"
    then obtain y where "P x y" and "y = ?f x"
      using existsA the_equality unique by metis
    thus "x \<le> ?f x"
      using mono by blast
  }

  {
    fix y
    have "y \<in> ?f ` A \<longleftrightarrow> (\<exists>x. x \<in> A \<and> y = The (P x))"
      unfolding image_def by force
    also
    have "\<dots> \<longleftrightarrow> (\<exists>x. P x y)"
      by (metis inA existsA unique the_equality)
    also
    have "\<dots> \<longleftrightarrow> y \<in> B"
      using inB existsB by blast
    finally
    have "y \<in> ?f ` A \<longleftrightarrow> y \<in> B"
      .
  }
  thus "?f ` A = B"
    by blast
qed

lemma token_time_finite_pair_rule:
  fixes A :: "(nat \<times> nat) set"
  fixes B :: "nat set"
  assumes unique:  "\<And>x y z. P x y \<Longrightarrow> P x z \<Longrightarrow> y = z"
      and existsA: "\<And>x. x \<in> A \<Longrightarrow> (\<exists>y. P x y)"
      and existsB: "\<And>y. y \<in> B \<Longrightarrow> (\<exists>x. P x y)"
      and inA:     "\<And>x y. P x y \<Longrightarrow> x \<in> A"
      and inB:     "\<And>x y. P x y \<Longrightarrow> y \<in> B"
      and mono:    "\<And>x y. P x y \<Longrightarrow> fst x \<le> y + c \<and> snd x \<le> y + d"
  shows "finite A \<longleftrightarrow> finite B"
proof (rule finite_monotonic_image_pairs)
  let ?f = "(\<lambda>x. if x \<in> A then The (P x) else undefined)"

  {
    fix x
    assume "x \<in> A"
    then obtain y where "P x y" and "y = ?f x"
      using existsA the_equality unique by metis
    thus "fst x \<le> ?f x + c" and "snd x \<le> ?f x + d"
      using mono by blast+
  }

  {
    fix y
    have "y \<in> ?f ` A \<longleftrightarrow> (\<exists>x. x \<in> A \<and> y = The (P x))"
      unfolding image_def by force
    also
    have "\<dots> \<longleftrightarrow> (\<exists>x. P x y)"
      by (metis inA existsA unique the_equality)
    also
    have "\<dots> \<longleftrightarrow> y \<in> B"
      using inB existsB by blast
    finally
    have "y \<in> ?f ` A \<longleftrightarrow> y \<in> B"
      .
  }
  thus "?f ` A = B"
    by blast
qed

\<comment> \<open>Correspondence Between Token- and Time-Based Definitions\<close>

lemma fail_t_inclusion:
  assumes "x \<le> n"
  assumes "\<not>sink (token_run x n)"
  assumes "sink (token_run x (Suc n))"
  assumes "token_run x (Suc n) \<notin> F"
  shows "n \<in> fail_t"
proof -
  define q q' where "q = token_run x n" and "q' = token_run x (Suc n)"
  hence *: "\<not>sink q" "sink q'" and "q' \<notin> F"
    using assms by blast+
  moreover
  from * have **: "state_rank q n \<noteq> None"
    unfolding q_def by (metis oldest_token_always_def option.distinct(1) state_rank_None)
  moreover
  from ** have "q' = \<delta> q (w n)"
    unfolding q_def q'_def using assms(1) token_run_step' by blast
  ultimately
  show "n \<in> fail_t"
    unfolding fail_t_def by blast
qed

lemma merge_t_inclusion:
  assumes "x \<le> n"
  assumes "(\<exists>j'. token_run x n \<noteq> token_run y n \<and> y \<le> n \<and> state_rank (token_run y n) n = Some j') \<or> y = Suc n"
  assumes "token_run x (Suc n) = token_run y (Suc n)"
  assumes "token_run x (Suc n) \<notin> F"
  assumes "state_rank (token_run x n) n = Some j"
  assumes "j < i"
  shows "n \<in> merge_t i"
proof -
  define q q' q''
    where "q = token_run x n"
      and "q' = token_run x (Suc n)"
      and "q'' = token_run y n"
  have "y \<le> Suc n"
    using assms(2) by linarith
  hence "(q' = \<delta> q'' (w n) \<and> state_rank q'' n \<noteq> None \<and> q'' \<noteq> q) \<or> q' = q\<^sub>0"
    unfolding q_def q'_def q''_def using assms(2-3)
    by (cases "y = Suc n") ((metis token_run_intial_state), (metis option.distinct(1) token_run_step))
  moreover
  have "state_rank q n = Some j \<and> j < i \<and> q' = \<delta> q (w n) \<and> q' \<notin> F"
    unfolding q_def q'_def using token_run_step[OF assms(1)] assms(4-6) by blast
  ultimately
  show "n \<in> merge_t i"
    unfolding merge_t_def by blast
qed

lemma succeed_t_inclusion:
  assumes "rank x n = Some i"
  assumes "token_run x n \<notin> F - {q\<^sub>0}"
  assumes "token_run x (Suc n) \<in> F"
  shows "n \<in> succeed_t i"
proof -
  define q where "q = token_run x n"
  hence "state_rank q n = Some i" and "q \<notin> F - {q\<^sub>0}" and "\<delta> q (w n) \<in> F"
    using token_run_step' rank_Some_time[OF assms(1)] assms rank_eq_state_rank by auto
  thus "n \<in> succeed_t i"
    unfolding succeed_t_def by blast
qed

lemma finite_fail_t:
  "finite fail = finite fail_t"
proof (rule token_time_finite_rule)
  let ?P = "(\<lambda>x n. x \<le> n
    \<and> \<not>sink (token_run x n)
    \<and> sink (token_run x (Suc n))
    \<and> token_run x (Suc n) \<notin> F)"

  {
    fix x
    have "\<not>sink (token_run x x)"
      unfolding sink_def by simp

    assume "x \<in> fail"
    hence "token_fails x"
      unfolding fail_def ..
    moreover
    then obtain y'' where "sink (token_run x (Suc (x + y'')))"
      unfolding token_fails_alt_def MOST_nat
      using \<open>\<not> sink (token_run x x)\<close> less_add_Suc2 by blast
    then obtain y' where "\<not>sink (token_run x (x + y'))" and "sink (token_run x (Suc (x + y')))"
      using token_run_P[of "\<lambda>q. sink q", OF \<open>\<not>sink (token_run x x)\<close>] by blast
    ultimately
    show "\<exists>y. ?P x y"
      using token_fails_alt_def_2 token_succeeds_def by (metis le_add1)
  }

  {
    fix y
    assume "y \<in> fail_t"
    then obtain q q' i where "state_rank q y = Some i" and "q' = \<delta> q (w y)" and "q' \<notin> F" and "sink q'"
      unfolding fail_t_def by blast
    moreover
    then obtain x where "token_run x y = q" and "x \<le> y"
      by (blast dest: push_down_state_rank_token_run)
    moreover
    hence "token_run x (Suc y) = q'"
      using token_run_step[OF _ _ \<open>q' = \<delta> q (w y)\<close>] by blast
    ultimately
    show "\<exists>x. ?P x y"
      by (metis option.distinct(1) state_rank_sink)
  }

  {
    fix x y
    assume "?P x y"
    thus "x \<in> fail" and "x \<le> y" and "y \<in> fail_t"
      unfolding fail_def using token_fails_def fail_t_inclusion by blast+
  }

  \<comment> \<open>Uniqueness\<close>
  {
    fix x y z
    assume "?P x y" and "?P x z"
    from \<open>?P x y\<close> have "\<not>sink (token_run x y)" and "sink (token_run x (Suc y))"
      by blast+
    moreover
    from \<open>?P x z\<close> have "\<not>sink (token_run x z)" and "sink (token_run x (Suc z))"
      by blast+
    ultimately
    show "y = z"
      using token_stays_in_sink
      by (cases y z rule: linorder_cases, simp_all)
         (metis (no_types, lifting) Suc_leI le_add_diff_inverse)+
  }
qed

lemma finite_succeed_t':
  assumes "q\<^sub>0 \<notin> F"
  shows "finite (succeed i) = finite (succeed_t i)"
proof (rule token_time_finite_rule)
  let ?P = "(\<lambda>x n. x \<le> n
    \<and> state_rank (token_run x n) n = Some i
    \<and> (token_run x n) \<notin> F - {q\<^sub>0}
    \<and> (token_run x (Suc n)) \<in> F)"

  {
    fix x
    assume "x \<in> succeed i"
    then obtain y where "token_run x y \<notin> F - {q\<^sub>0}" and "token_run x (Suc y) \<in> F" and "rank x y = Some i"
       unfolding succeed_def by force
    moreover
    hence "rank (senior x y) y = Some i"
      using rank_Some_time[THEN rank_senior_senior] by presburger
    hence "state_rank (token_run x y) y = Some i"
      unfolding state_rank_eq_rank senior.simps by (metis oldest_token_always_def option.sel option.simps(5))
    ultimately
    show "\<exists>y. ?P x y"
      using rank_Some_time by blast
  }

  {
    fix y
    assume "y \<in> succeed_t i"
    then obtain q where "state_rank q y = Some i" and "q \<notin> F - {q\<^sub>0}" and "(\<delta> q (w y)) \<in> F"
      unfolding succeed_t_def by blast
    moreover
    then obtain x where "q = token_run x y" and "x \<le> y"
      by (metis oldest_token_bounded push_down_oldest_token_token_run push_down_state_rank_oldest_token)
    moreover
    hence "token_run x (Suc y) \<in> F"
      using token_run_step \<open>(\<delta> q (w y)) \<in> F\<close> by simp
    ultimately
    show "\<exists>x. ?P x y"
      by meson
  }

  {
    fix x y
    assume "?P x y"
    thus "x \<le> y" and "x \<in> succeed i" and "y \<in> succeed_t i"
      unfolding succeed_def using rank_eq_state_rank[of x y] succeed_t_inclusion
      by (metis (mono_tags, lifting) mem_Collect_eq)+
  }

  \<comment> \<open>Uniqueness\<close>
  {
    fix x y z
    assume "?P x y" and "?P x z"
    from \<open>?P x y\<close> have "token_run x y \<notin> F" and "token_run x (Suc y) \<in> F"
      using \<open>q\<^sub>0 \<notin> F\<close> by auto
    moreover
    from \<open>?P x z\<close> have "token_run x z \<notin> F" and "token_run x (Suc z) \<in> F"
      using \<open>q\<^sub>0 \<notin> F\<close> by auto
    ultimately
    show "y = z"
      using token_stays_in_final_states
      by (cases y z rule: linorder_cases, simp_all)
         (metis le_Suc_ex less_Suc_eq_le not_le)+
  }
qed

lemma initial_in_F_token_run:
  assumes "q\<^sub>0 \<in> F"
  shows "token_run x y \<in> F"
  using assms token_stays_in_final_states[of _ 0] by fastforce

lemma finite_succeed_t'':
  assumes "q\<^sub>0 \<in> F"
  shows "finite (succeed i) = finite (succeed_t i)"
  (is "?lhs = ?rhs")
proof
  have "succeed_t i = {n. state_rank q\<^sub>0 n = Some i}"
    unfolding succeed_t_def using initial_in_F_token_run assms wellformed_F by auto
  also
  have "... = {n. rank n n = Some i}"
    unfolding rank_eq_state_rank[OF order_refl] token_run_intial_state ..
  finally
  have succeed_t_alt_def: "succeed_t i = {n. rank n n = Some i \<and> token_run n n = q\<^sub>0}"
    by simp

  have succeed_alt_def: "succeed i = {x. \<exists>n. rank x n = Some i \<and> token_run x n = q\<^sub>0}"
    unfolding succeed_def using initial_in_F_token_run[OF assms] by auto

  {
    assume ?lhs
    moreover
    have "succeed_t i \<subseteq> succeed i"
      unfolding succeed_t_alt_def succeed_alt_def by blast
    ultimately
    show ?rhs
      by (rule rev_finite_subset)
  }

  {
    assume ?rhs
    then obtain U where U_def: "\<And>x. x \<in> succeed_t i \<Longrightarrow> U \<ge> x"
      unfolding finite_nat_set_iff_bounded_le by blast
    {
      fix x
      assume "x \<in> succeed i"
      then obtain n where "rank x n = Some i" and "token_run x n = q\<^sub>0"
        unfolding succeed_alt_def by blast
      moreover
      hence "x \<le> n"
        by (blast dest: rank_Some_time)
      moreover
      hence "rank n n = Some i"
        using \<open>rank x n = Some i\<close> \<open>token_run x n = q\<^sub>0\<close>
        by (metis order_refl token_run_intial_state[of n] pull_up_token_run_tokens pull_up_configuration_rank)
      hence "n \<in> succeed_t i"
        unfolding succeed_t_alt_def by simp
      ultimately
      have "U \<ge> x"
        using U_def by fastforce
    }
    thus ?lhs
      unfolding finite_nat_set_iff_bounded_le by blast
  }
qed

lemma finite_succeed_t:
  "finite (succeed i) = finite (succeed_t i)"
  using finite_succeed_t' finite_succeed_t'' by blast

lemma finite_merge_t:
  "finite (merge i) = finite (merge_t i)"
proof (rule token_time_finite_pair_rule)
  let ?P = "(\<lambda>(x, y) n. \<exists>j. x \<le> n
    \<and> ((\<exists>j'. token_run x n \<noteq> token_run y n \<and> y \<le> n \<and> state_rank (token_run y n) n = Some j') \<or> y = Suc n)
    \<and> token_run x (Suc n) = token_run y (Suc n)
    \<and> token_run x (Suc n) \<notin> F
    \<and> state_rank (token_run x n) n = Some j
    \<and> j < i)"

  {
    fix x
    assume "x \<in> merge i"
    then obtain t t' n j where 1: "x = (t, t')"
      and 3: "(\<exists>j'. token_run t n \<noteq> token_run t' n \<and> rank t' n = Some j') \<or>  t' = Suc n"
      and 4: "token_run t (Suc n) = token_run t' (Suc n)"
      and 5: "token_run t (Suc n) \<notin> F"
      and 6: "rank t n = Some j"
      and 7:  "j < i"
      unfolding merge_def by blast
    moreover
    hence 8: "t \<le> n" and 9: "t' \<le> Suc n"
      using rank_Some_time le_Suc_eq by blast+
    moreover
    hence 10: "state_rank (token_run t n) n = Some j"
      using \<open>rank t n = Some j\<close> rank_eq_state_rank by metis
    ultimately
    show "\<exists>y. ?P x y"
    proof (cases "t' = Suc n")
      case False
        hence "t' \<le> n"
          using \<open>t' \<le> Suc n\<close> by simp
        with 1 3 4 5 7 8 10 show ?thesis
          unfolding rank_eq_state_rank[OF \<open>t' \<le> n\<close>] by blast
    qed blast
  }

  {
    fix y
    assume "y \<in> merge_t i"
    then obtain q q' j where 1: "state_rank q y = Some j"
      and 2: "j < i"
      and 3: "q' = \<delta> q (w y)"
      and 4: "q' \<notin> F"
      and 5: "(\<exists>q''. q' = \<delta> q'' (w y) \<and> state_rank q'' y \<noteq> None \<and> q'' \<noteq> q) \<or> q' = q\<^sub>0"
      unfolding merge_t_def by blast

    then obtain t where 6: "q = token_run t y" and 7: "t \<le> y"
      using push_down_state_rank_token_run by metis
    hence 8: "q' = token_run t (Suc y)"
      unfolding \<open>q' = \<delta> q (w y)\<close> using token_run_step by simp

    {
      assume "q' = q\<^sub>0"
      hence "token_run t (Suc y) = token_run (Suc y) (Suc y)"
        unfolding 8 by simp
      moreover
      then obtain x where "x = (t, Suc y)"
        by simp
      ultimately
      have "?P x y"
        using 1 2 3 4 5 7 unfolding 6 8 by force
      hence "\<exists>x. ?P x y"
        by blast
    }
    moreover
    {
      assume "q' \<noteq> q\<^sub>0"
      then obtain q'' j' where 9: "q' = \<delta> q'' (w y)"
        and "state_rank q'' y = Some j'"
        and "q'' \<noteq> q"
        using 5 by blast
      moreover
      then obtain t' where 12: "q'' = token_run t' y" and "t' \<le> y"
        by (blast dest: push_down_state_rank_token_run)
      moreover
      hence "token_run t (Suc y) = token_run t' (Suc y)"
        using 8 9 token_run_step by presburger
      moreover
      have "token_run t y \<noteq> token_run t' y"
        using \<open>q'' \<noteq> q\<close> unfolding 6 12 ..
      moreover
      then obtain x where "x = (t, t')"
        by simp
      ultimately
      have "?P x y"
        using 1 2 4 7 unfolding 6 8 by fast
      hence "\<exists>x. ?P x y"
        by blast
    }
    ultimately
    show "\<exists>x. ?P x y"
      by blast
  }

  {
    fix x y
    assume "?P x y"
    then obtain t t' j where 1: "x = (t, t')"
      and 3: "t \<le> y"
      and 4: "(\<exists>j'. token_run t y \<noteq> token_run t' y \<and> t' \<le> y \<and> state_rank (token_run t' y) y = Some j') \<or> t' = Suc y"
      and 5: "token_run t (Suc y) = token_run t' (Suc y)"
      and 6: "token_run t (Suc y) \<notin> F"
      and 7: "state_rank (token_run t y) y = Some j"
      and 8: "j < i"
      by blast

    thus "x \<in> merge i"
    proof (cases "t' = Suc y")
      case False
        hence "t' \<le> y"
          using 4 by blast
        thus ?thesis
          using 1 3 4 5 6 7 8 unfolding merge_def
          unfolding rank_eq_state_rank[OF \<open>t' \<le> y\<close>, symmetric] rank_eq_state_rank[OF \<open>t \<le> y\<close>, symmetric]
          by blast
    qed (unfold rank_eq_state_rank[OF \<open>t \<le> y\<close>, symmetric] merge_def, blast)

    show "y \<in> merge_t i" and "fst x \<le> y + 0 \<and> snd x \<le> y + 1"
      using merge_t_inclusion \<open>?P x y\<close> by force+
  }

  \<comment> \<open>Uniqueness\<close>
  {
    fix x y z
    assume "?P x y" and "?P x z"
    then obtain t t' where "x = (t, t')"
      by blast
    from \<open>?P x y\<close>[unfolded \<open>x = (t, t')\<close>] have y1: "t \<le> y"
      and y2: "(token_run t y \<noteq> token_run t' y \<and> t' \<le> y) \<or> t' = Suc y"
      and y3: "token_run t (Suc y) = token_run t' (Suc y)" by blast+
    moreover
    from \<open>?P x z\<close>[unfolded \<open>x = (t, t')\<close>] have z1: "t \<le> z"
      and z2: "(token_run t z \<noteq> token_run t' z \<and> t' \<le> z) \<or> t' = Suc z"
      and z3: "token_run t (Suc z) = token_run t' (Suc z)" by blast+
    moreover
    have y4: "t' \<le> Suc y" and z4: "t' \<le> Suc z"
      using y2 z2 by linarith+
    ultimately
    show "y = z"
    proof (cases y z rule: linorder_cases)
      case less
        then obtain d where "Suc y + d = z"
          by (metis add_Suc_right add_Suc_shift less_imp_Suc_add)
        thus ?thesis
          using y1 y2 z2 token_run_merge[OF _ y4 y3] by auto
    next
      case greater
        then obtain d where "Suc z + d = y"
          by (metis add_Suc_right add_Suc_shift less_imp_Suc_add)
        thus ?thesis
          using z1 y2 z2 token_run_merge[OF _ z4 z3] by auto
    qed
  }
qed

subsubsection \<open>Relation to Mojmir Acceptance\<close>

lemma token_iff_time_accept:
  shows "(finite fail \<and> finite (merge i) \<and> infinite (succeed i) \<and> (\<forall>j < i. finite (succeed j)))
       = (finite fail_t \<and> finite (merge_t i) \<and> infinite (succeed_t i) \<and> (\<forall>j < i. finite (succeed_t j)))"
  unfolding finite_fail_t finite_merge_t finite_succeed_t by simp

subsection \<open>Succeeding Tokens (Alternative Definition)\<close>

definition stable_rank_at :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "stable_rank_at x n \<equiv> \<exists>i. \<forall>m \<ge> n. rank x m = Some i"

lemma stable_rank_at_ge:
  "n \<le> m \<Longrightarrow> stable_rank_at x n \<Longrightarrow> stable_rank_at x m"
  unfolding stable_rank_at_def by fastforce

lemma stable_rank_equiv:
  "(\<exists>i. stable_rank x i) = (\<exists>n. stable_rank_at x n)"
  unfolding stable_rank_def MOST_nat_le stable_rank_at_def by blast

lemma smallest_accepting_rank_properties:
  assumes "smallest_accepting_rank = Some i"
  shows "accept" "finite fail" "finite (merge i)" "infinite (succeed i)" "\<forall>j < i. finite (succeed j)" "i < max_rank"
proof -
  from assms show "accept"
    unfolding smallest_accepting_rank_def using option.distinct(1) by metis
  then obtain i' where "finite fail" and "finite (merge i')" and "infinite (succeed i')"
    and "\<forall>j < i'. finite (succeed j)" and "i' < max_rank"
    unfolding mojmir_accept_iff_token_set_accept2 by blast
  moreover
  hence "\<And>y. finite fail \<and> finite (merge y) \<and> infinite (succeed y) \<longrightarrow> i' \<le> y"
    using not_le by blast
  ultimately
  have "(LEAST i. finite fail \<and> finite (merge i) \<and> infinite (succeed i)) = i'"
    using le_antisym unfolding Least_def by (blast dest: the_equality[of _ i'])
  hence "i' = i"
    using \<open>smallest_accepting_rank = Some i\<close> \<open>accept\<close> unfolding smallest_accepting_rank_def by simp
  thus "finite fail" and "finite (merge i)" and "infinite (succeed i)"
    and "\<forall>j < i. finite (succeed j)" and "i < max_rank"
    using \<open>finite fail\<close> \<open>finite (merge i')\<close> \<open>infinite (succeed i')\<close>
    using \<open>\<forall>j < i'. finite (succeed j)\<close> \<open>i' < max_rank\<close> by simp+
qed

lemma token_smallest_accepting_rank:
  assumes "smallest_accepting_rank = Some i"
  shows "\<forall>\<^sub>\<infinity>n. \<forall>x. token_succeeds x \<longleftrightarrow> (x > n \<or> (\<exists>j \<ge> i. rank x n = Some j) \<or> token_run x n \<in> F)"
proof -
  from assms have "accept" "finite fail" "infinite (succeed i)" "\<forall>j < i. finite (succeed j)"
    using smallest_accepting_rank_properties by blast+

  then obtain n\<^sub>1 where n\<^sub>1_def: "\<forall>x \<ge> n\<^sub>1. token_succeeds x"
    unfolding accept_def MOST_nat_le by blast
  define n\<^sub>2 where "n\<^sub>2 = Suc (Max (fail_t \<union> \<Union>{succeed_t j | j. j < i}))" (is "_ = Suc (Max ?S)")
  define n\<^sub>3 where "n\<^sub>3 = Max ({LEAST m. stable_rank_at x m | x. x < n\<^sub>1 \<and> token_squats x})" (is "_ = Max ?S'")
  define n where "n = Max {n\<^sub>1, n\<^sub>2, n\<^sub>3}"

  have "finite ?S" and "finite ?S'"
    using \<open>finite fail\<close> \<open>\<forall>j < i. finite (succeed j)\<close>
    unfolding finite_fail_t finite_succeed_t by fastforce+

  {
    fix x
    assume "x < n\<^sub>1" "token_squats x"
    hence "(LEAST m. stable_rank_at x m) \<in> ?S'" (is "?m \<in> _")
      by blast
    hence "?m \<le> n\<^sub>3"
      using Max.coboundedI[OF \<open>finite ?S'\<close>] n\<^sub>3_def by simp
    moreover
    obtain k where "stable_rank x k"
      using \<open>x < n\<^sub>1\<close> \<open>token_squats x\<close> stable_rank_equiv_token_squats by blast
    hence "stable_rank_at x ?m"
      by (metis stable_rank_equiv LeastI)
    ultimately
    have "stable_rank_at x n\<^sub>3"
      by (rule stable_rank_at_ge)
    hence "\<exists>i. \<forall>m' \<ge> n. rank x m' = Some i"
      unfolding n_def stable_rank_at_def by fastforce
  }
  note Stable = this

  have "\<And>m j. j < i \<Longrightarrow> m \<in> succeed_t j \<Longrightarrow> m < n"
    using Max.coboundedI[OF \<open>finite ?S\<close>] unfolding n_def n\<^sub>2_def by fastforce
  hence Succeed: "\<And>m j x. n \<le> m \<Longrightarrow> token_run x m \<notin> F - {q\<^sub>0} \<Longrightarrow> token_run x (Suc m) \<in> F \<Longrightarrow> rank x m = Some j \<Longrightarrow> i \<le> j"
    by (metis not_le succeed_t_inclusion)

  have "\<And>m. m \<in> fail_t \<Longrightarrow> m < n"
    using Max.coboundedI[OF \<open>finite ?S\<close>] unfolding n_def n\<^sub>2_def by fastforce
  hence Fail: "\<And>m x. n \<le> m \<Longrightarrow> x \<le> m \<Longrightarrow> sink (token_run x m) \<or> \<not>sink (token_run x (Suc m)) \<or> \<not>token_run x (Suc m) \<notin> F"
    using fail_t_inclusion by fastforce

  {
    fix m x
    assume "m \<ge> n" "m \<ge> x"
    moreover
    {
      assume "token_succeeds x" "token_run x m \<notin> F"
      then obtain m' where "x \<le> m'" and "token_run x m' \<notin> F - {q\<^sub>0}" and "token_run x (Suc m') \<in> F"
        using token_run_enter_final_states unfolding token_succeeds_def by meson
      moreover
      hence "\<not>sink (token_run x m')"
        by (metis Diff_empty Diff_insert0 \<open>token_run x m \<notin> F\<close> initial_in_F_token_run token_is_not_in_sink)
      ultimately
      obtain j' where "rank x m' = Some j'"
        by simp
      moreover
      have "m \<le> m'"
        by (metis \<open>token_run x m \<notin> F\<close> token_stays_in_final_states[OF \<open>token_run x (Suc m') \<in> F\<close>] add_Suc_right add_Suc_shift less_imp_Suc_add not_le)
      moreover
      hence "m' \<ge> n"
        using \<open>x \<le> m\<close> \<open>m \<ge> n\<close> by simp
      hence "j' \<ge> i"
        using Succeed[OF _ \<open>token_run x m' \<notin> F - {q\<^sub>0}\<close> \<open>token_run x (Suc m') \<in> F\<close> \<open>rank x m' = Some j'\<close>] by blast
      moreover
      obtain k where "rank x x = Some k"
        using rank_initial[of x] by blast
      ultimately
      obtain j where "rank x m = Some j"
        by (metis rank_continuous[OF \<open>rank x x = Some k\<close>, of "m' - x"] \<open>x \<le> m'\<close> \<open>x \<le> m\<close> diff_le_mono le_add_diff_inverse)
      hence "\<exists>j \<ge> i. rank x m = Some j"
        using rank_monotonic \<open>rank x m' = Some j'\<close> \<open>j' \<ge> i\<close> \<open>m \<le> m'\<close>[THEN le_Suc_ex]
        by (blast dest: le_Suc_ex trans_le_add1)
    }
    moreover
    {
      assume "\<not>token_succeeds x"
      hence "\<And>m. token_run x m \<notin> F"
        unfolding token_succeeds_def by blast
      moreover
      have "\<not>(\<exists>j \<ge> i. rank x m = Some j)"
      proof (cases "token_squats x")
        case True
          \<comment> \<open>The token already stabilised\<close>
          have "x < n\<^sub>1"
            using \<open>\<not>token_succeeds x\<close> n\<^sub>1_def by (metis not_le)
          then obtain k where "\<forall>m' \<ge> n. rank x m' = Some k"
            using Stable[OF _ True] by blast
          moreover
          hence "stable_rank x k"
            unfolding stable_rank_def MOST_nat_le by blast
          moreover
          have "q\<^sub>0 \<notin> F"
            by (metis \<open>\<And>m. token_run x m \<notin> F\<close> initial_in_F_token_run)
          ultimately
          \<comment> \<open>Hence the rank is smaller than i\<close>
          have "k < i" and "rank x m = Some k"
            using stable_rank_bounded \<open>infinite (succeed i)\<close> \<open>n \<le> m\<close> by blast+
          thus ?thesis
            by simp
      next
        case False
          \<comment> \<open>Then token is already in a sink\<close>
          have "sink (token_run x m)"
          proof (rule ccontr)
            assume "\<not>sink (token_run x m)"
            moreover
            obtain m' where "m < m'" and "sink (token_run x m')"
              by (metis False token_squats_def le_add2 not_le not_less_eq_eq token_stays_in_sink)
            ultimately
            obtain m'' where "m \<le> m''" and  "\<not>sink (token_run x m'')" and "sink (token_run x (Suc m''))"
              by (metis le_add1 less_imp_Suc_add token_run_P)
            thus False
              by (metis Fail \<open>\<And>m. token_run x m \<notin> F\<close> \<open>n \<le> m\<close> \<open>x \<le> m\<close> le_trans)
          qed
          \<comment> \<open>Hence there is no rank\<close>
          thus ?thesis
            by simp
      qed
      ultimately
      have "\<not>(\<exists>j \<ge> i. rank x m = Some j) \<and> token_run x m \<notin> F"
        by blast
    }
    ultimately
    have "(\<exists>j \<ge> i. rank x m = Some j) \<or> token_run x m \<in> F \<longleftrightarrow> token_succeeds x"
      by (cases "token_succeeds x") (blast, simp)
  }
  moreover
  \<comment> \<open>By definition of n all tokens @{term "\<And>x. x \<ge> n"} succeed\<close>
  have "\<And>m x. m \<ge> n \<Longrightarrow> \<not>x \<le> m \<Longrightarrow> token_succeeds x"
    using n_def n\<^sub>1_def by force
  ultimately
  show ?thesis
    unfolding MOST_nat_le not_le[symmetric] by blast
qed

lemma succeeding_states:
  assumes "smallest_accepting_rank = Some i"
  shows "\<forall>\<^sub>\<infinity>n. \<forall>q. ((\<exists>x \<in> configuration q n. token_succeeds x) \<longrightarrow> q \<in> \<S> n) \<and> (q \<in> \<S> n \<longrightarrow> (\<forall>x \<in> configuration q n. token_succeeds x))"
proof -
  obtain n where n_def: "\<And>m x. m \<ge> n \<Longrightarrow> token_succeeds x = (x > m \<or> (\<exists>j \<ge> i. rank x m = Some j) \<or> token_run x m \<in> F)"
    using token_smallest_accepting_rank[OF assms] unfolding MOST_nat_le by auto
  {
    fix m q
    assume "m \<ge> n" "q \<notin> F" "\<exists>x \<in> configuration q m. token_succeeds x"
    moreover
    then obtain x where "token_run x m = q" and "x \<le> m" and "token_succeeds x"
      by auto
    ultimately
    have "\<exists>j \<ge> i. rank x m = Some j"
      using n_def by simp
    hence "\<exists>j \<ge> i. state_rank q m = Some j"
      using rank_eq_state_rank \<open>x \<le> m\<close> \<open>token_run x m = q\<close> by metis
  }
  moreover
  {
    fix m q x
    assume "m \<ge> n" "x \<in> configuration q m"
    hence "x \<le> m" and "token_run x m = q"
      by simp+
    moreover
    assume "q \<in> \<S> m"
    hence "(\<exists>j \<ge> i. state_rank q m = Some j) \<or> q \<in> F"
      using assms by fastforce
    ultimately
    have "(\<exists>j \<ge> i. rank x m = Some j) \<or> q \<in> F"
      using rank_eq_state_rank by presburger
    hence "token_succeeds x"
      unfolding n_def[OF \<open>m \<ge> n\<close>] \<open>token_run x m = q\<close> by presburger
  }
  ultimately
  show ?thesis
    unfolding MOST_nat_le \<S>.simps assms option.sel by blast
qed

end

end
