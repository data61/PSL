(*
    Author:      Salomon Sickert
    License:     BSD
*)

section \<open>Mojmir Automata (Without Final States)\<close>

theory Semi_Mojmir
  imports Main "Auxiliary/Preliminaries2" DTS
begin

subsection \<open>Definitions\<close>

locale semi_mojmir_def =
  fixes
    \<comment> \<open>Alphapet\<close>
    \<Sigma> :: "'a set"
  fixes
    \<comment> \<open>Transition Function\<close>
    \<delta> :: "('b, 'a) DTS"
  fixes
    \<comment> \<open>Initial State\<close>
    q\<^sub>0 :: "'b"
  fixes
    \<comment> \<open>$\omega$-Word\<close>
    w :: "'a word"
begin

definition sink :: "'b \<Rightarrow> bool"
where
  "sink q \<equiv> (q\<^sub>0 \<noteq> q) \<and> (\<forall>\<nu> \<in> \<Sigma>. \<delta> q \<nu> = q)"

declare sink_def [code]

fun token_run :: "nat \<Rightarrow> nat \<Rightarrow> 'b"
where
  "token_run x n = run \<delta> q\<^sub>0 (suffix x w) (n - x)"

fun configuration :: "'b \<Rightarrow> nat \<Rightarrow> nat set"
where
  "configuration q n = {x. x \<le> n \<and> token_run x n = q}"

fun oldest_token :: "'b \<Rightarrow> nat \<Rightarrow> nat option"
where
  "oldest_token q n = (if configuration q n \<noteq> {} then Some (Min (configuration q n)) else None)"

fun senior :: "nat \<Rightarrow> nat \<Rightarrow> nat"
where
  "senior x n = the (oldest_token (token_run x n) n)"

fun older_seniors :: "nat \<Rightarrow> nat \<Rightarrow> nat set"
where
  "older_seniors x n = {s. \<exists>y. s = senior y n \<and> s < senior x n \<and> \<not> sink (token_run s n)}"

fun rank :: "nat \<Rightarrow> nat \<Rightarrow> nat option"
where
  "rank x n =
    (if x \<le> n \<and> \<not>sink (token_run x n) then Some (card (older_seniors x n)) else None)"

fun senior_states :: "'b \<Rightarrow> nat \<Rightarrow> 'b set"
where
  "senior_states q n =
    {p. \<exists>x y. oldest_token p n = Some y \<and> oldest_token q n = Some x \<and> y < x \<and> \<not> sink p}"

fun state_rank :: "'b \<Rightarrow> nat \<Rightarrow> nat option"
where
  "state_rank q n = (if configuration q n \<noteq> {} \<and> \<not>sink q then Some (card (senior_states q n)) else None)"

definition max_rank :: "nat"
where
  "max_rank = card (reach \<Sigma> \<delta> q\<^sub>0 - {q. sink q})"

subsubsection \<open>Iterative Computation of State-Ranks\<close>

fun initial :: "'b \<Rightarrow> nat option"
where
  "initial q = (if q = q\<^sub>0 then Some 0 else None)"

fun pre_ranks :: "('b \<Rightarrow> nat option) \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> nat set"
where
  "pre_ranks r \<nu> q = {i . \<exists>q'. r q' = Some i \<and> q = \<delta> q' \<nu>} \<union> (if q = q\<^sub>0 then {max_rank} else {})"

fun step :: "('b \<Rightarrow> nat option) \<Rightarrow> 'a \<Rightarrow> ('b \<Rightarrow> nat option)"
where
  "step r \<nu> q = (
    if
      \<not>sink q \<and> pre_ranks r \<nu> q \<noteq> {}
    then
      Some (card {q'. \<not>sink q' \<and> pre_ranks r \<nu> q' \<noteq> {} \<and> Min (pre_ranks r \<nu> q') < Min (pre_ranks r \<nu> q)})
    else
      None)"

subsubsection \<open>Properties of Tokens\<close>

definition token_squats :: "nat \<Rightarrow> bool"
where
  "token_squats x = (\<forall>n. \<not>sink (token_run x n))"

end

locale semi_mojmir = semi_mojmir_def +
  assumes
    \<comment> \<open>The alphabet is finite. Non-emptiness is derived from well-formed w\<close>
    finite_\<Sigma>: "finite \<Sigma>"
  assumes
    \<comment> \<open>The set of reachable states is finite\<close>
    finite_reach: "finite (reach \<Sigma> \<delta> q\<^sub>0)"
  assumes
    \<comment> \<open>w only contains letters from the alphabet\<close>
    bounded_w: "range w \<subseteq> \<Sigma>"
begin

lemma nonempty_\<Sigma>: "\<Sigma> \<noteq> {}"
  using bounded_w by blast

lemma bounded_w': "w i \<in> \<Sigma>"
  using bounded_w by blast

\<comment> \<open>Naming Scheme:

This theory uses the following naming scheme to consistently name variables.

* Tokens: x, y, z
* Time: n, m
* Rank: i, j, k
* States: p, q\<close>

lemma sink_rev_step:
  "\<not>sink q \<Longrightarrow> q = \<delta> q' \<nu> \<Longrightarrow> \<nu> \<in> \<Sigma> \<Longrightarrow> \<not>sink q'"
  "\<not>sink q \<Longrightarrow> q = \<delta> q' (w i) \<Longrightarrow> \<not>sink q'"
  using bounded_w' by (force simp only: sink_def)+

subsection \<open>Token Run\<close>

lemma token_stays_in_sink:
  assumes "sink q"
  assumes "token_run x n = q"
  shows "token_run x (n + m) = q"
proof (cases "x \<le> n")
  case True
    show ?thesis
    proof (induction m)
      case 0
        show ?case
          using assms(2) by simp
    next
      case (Suc m)
        have "x \<le> n + m"
          using True by simp
        moreover
        have "\<And>x. w x \<in> \<Sigma>"
          using bounded_w by auto
        ultimately
        have "\<And>t. token_run x (n + m)  = q \<Longrightarrow> token_run x (n + m + 1) = q"
          using \<open>sink q\<close>[unfolded sink_def] upt_add_eq_append[OF le0, of "n + m" 1]
          using Suc_diff_le by simp
        with Suc show ?case
          by simp
    qed
qed (insert assms, simp add: sink_def)

lemma token_is_not_in_sink:
  "token_run x n \<notin> A \<Longrightarrow> token_run x (Suc n) \<in> A \<Longrightarrow> \<not>sink (token_run x n)"
  by (metis Suc_eq_plus1 token_stays_in_sink)

lemma token_run_intial_state:
  "token_run x x = q\<^sub>0"
  by simp

lemma token_run_P:
  assumes "\<not> P (token_run x n)"
  assumes "P (token_run x (Suc (n + m)))"
  shows "\<exists>m' \<le> m. \<not> P (token_run x (n + m')) \<and> P (token_run x (Suc (n + m')))"
  using assms by (induction m) (simp_all, metis add_Suc_right le_Suc_eq)

lemma token_run_merge_Suc:
  assumes "x \<le> n"
  assumes "y \<le> n"
  assumes "token_run x n = token_run y n"
  shows "token_run x (Suc n) = token_run y (Suc n)"
proof -
  have "run \<delta> q\<^sub>0 (suffix x w) (Suc (n - x)) = run \<delta> q\<^sub>0 (suffix y w) (Suc (n - y))"
    using assms by fastforce
  thus ?thesis
    using Suc_diff_le assms(1,2) by force
qed

lemma token_run_merge:
  "\<lbrakk>x \<le> n; y \<le> n; token_run x n = token_run y n\<rbrakk> \<Longrightarrow> token_run x (n + m) = token_run y (n + m)"
  using token_run_merge_Suc[of x _ y] by (induction m) auto

lemma token_run_mergepoint:
  assumes "x < y"
  assumes "token_run x (y + n) = token_run y (y + n)"
  obtains m where "x \<le> (Suc m)" and "y \<le> (Suc m)"
    and "y = Suc m \<or> token_run x m \<noteq> token_run y m"
    and "token_run x (Suc m) = token_run y (Suc m)"
  using assms by (induction n)
    ((metis add_0_iff le_Suc_eq le_add1 less_imp_Suc_add),
     (metis add_Suc_right le_add1 less_or_eq_imp_le order_trans))

subsubsection \<open>Step Lemmas\<close>

lemma token_run_step:
  assumes "x \<le> n"
  assumes "token_run x n = q'"
  assumes "q = \<delta> q' (w n)"
  shows "token_run x (Suc n) = q"
  using assms unfolding token_run.simps Suc_diff_le[OF \<open>x \<le> n\<close>] by force

lemma token_run_step':
  "x \<le> n \<Longrightarrow> token_run x (Suc n) = \<delta> (token_run x n) (w n)"
  using token_run_step by simp

subsection \<open>Configuration\<close>

subsubsection \<open>Properties\<close>

lemma configuration_distinct:
  "q \<noteq> q' \<Longrightarrow> configuration q n \<inter> configuration q' n = {}"
  by auto

lemma configuration_finite:
  "finite (configuration q n)"
  by simp

lemma configuration_non_empty:
  "x \<le> n \<Longrightarrow> configuration (token_run x n) n \<noteq> {}"
  by fastforce

lemma configuration_token:
  "x \<le> n \<Longrightarrow> x \<in> configuration (token_run x n) n"
  by fastforce

lemmas configuration_Max_in = Max_in[OF configuration_finite]
lemmas configuration_Min_in = Min_in[OF configuration_finite]

subsubsection \<open>Monotonicity\<close>

lemma configuration_monotonic_Suc:
  "x \<le> n \<Longrightarrow> configuration (token_run x n) n \<subseteq> configuration (token_run x (Suc n)) (Suc n)"
proof
  fix y
  assume "y \<in> configuration (token_run x n) n"
  hence "y \<le> n" and "token_run x n = token_run y n"
    by simp_all
  moreover
  assume "x \<le> n"
  ultimately
  have "token_run x (Suc n) = token_run y (Suc n)"
    using token_run_merge_Suc by blast
  thus "y \<in> configuration (token_run x (Suc n)) (Suc n)"
    using configuration_token \<open>y \<le> n\<close> by simp
qed

subsubsection \<open>Pull-Up and Push-Down\<close>

lemma pull_up_token_run_tokens:
  "\<lbrakk>x \<le> n; y \<le> n; token_run x n = token_run y n\<rbrakk> \<Longrightarrow> \<exists>q. x \<in> configuration q n \<and> y \<in> configuration q n"
  by force

lemma push_down_configuration_token_run:
  "\<lbrakk>x \<in> configuration q n; y \<in> configuration q n\<rbrakk> \<Longrightarrow> x \<le> n \<and> y \<le> n \<and> token_run x n = token_run y n"
  by simp

subsubsection \<open>Step Lemmas\<close>

lemma configuration_step:
  "x \<in> configuration q' n \<Longrightarrow> q = \<delta> q' (w n) \<Longrightarrow> x \<in> configuration q (Suc n)"
  using Suc_diff_le by simp

lemma configuration_step_non_empty:
  "configuration q' n \<noteq> {} \<Longrightarrow> q = \<delta> q' (w n) \<Longrightarrow> configuration q (Suc n) \<noteq> {}"
  by (blast dest: configuration_step)

lemma configuration_rev_step':
  assumes "x \<noteq> Suc n"
  assumes "x \<in> configuration q (Suc n)"
  obtains q' where "q = \<delta> q' (w n)" and "x \<in> configuration q' n"
  using assms Suc_diff_le by force

lemma configuration_rev_step'':
  assumes "x \<in> configuration q\<^sub>0 (Suc n)"
  shows "x = Suc n \<or> (\<exists>q'. q\<^sub>0 = \<delta> q' (w n) \<and> x \<in> configuration q' n)"
  using assms configuration_rev_step' by metis

lemma configuration_step_eq_q\<^sub>0:
  "configuration q\<^sub>0 (Suc n) = {Suc n} \<union> \<Union>{configuration q' n | q'. q\<^sub>0 = \<delta> q' (w n)}"
  apply rule using configuration_rev_step'' apply fast using configuration_step[of _ _ n q\<^sub>0] by fastforce

lemma configuration_rev_step:
  assumes "q \<noteq> q\<^sub>0"
  assumes "x \<in> configuration q (Suc n)"
  obtains q' where "q = \<delta> q' (w n)" and "x \<in> configuration q' n"
  using configuration_rev_step'[OF _ assms(2)] assms by fastforce

lemma configuration_step_eq:
  assumes "q \<noteq> q\<^sub>0"
  shows "configuration q (Suc n) = \<Union>{configuration q' n | q'. q = \<delta> q' (w n)}"
  using configuration_rev_step[OF assms, of _ n] configuration_step by auto

lemma configuration_step_eq_unified:
  shows "configuration q (Suc n) = \<Union>{configuration q' n | q'. q = \<delta> q' (w n)} \<union> (if q = q\<^sub>0 then {Suc n} else {}) "
  using configuration_step_eq configuration_step_eq_q\<^sub>0 by force

subsection \<open>Oldest Token\<close>

subsubsection \<open>Properties\<close>

lemma oldest_token_always_def:
  "\<exists>i. i \<le> x \<and> oldest_token (token_run x n) n = Some i"
proof (cases "x \<le> n")
  case False
    let ?q = "token_run x n"
    from False have "n \<in> configuration ?q n" and "configuration ?q n \<noteq> {}"
      by auto
    then obtain i where "i \<le> n" and "oldest_token ?q n = Some i"
      by (metis Min.coboundedI oldest_token.simps configuration_finite)
    moreover
    hence "i \<le> x"
      using False by linarith
    ultimately
    show ?thesis
      by blast
qed fastforce

lemma oldest_token_bounded:
  "oldest_token q n = Some x \<Longrightarrow> x \<le> n"
  by (metis oldest_token.simps configuration_Min_in option.distinct(1) option.inject push_down_configuration_token_run)

lemma oldest_token_distinct:
  "q \<noteq> q' \<Longrightarrow> oldest_token q n = Some i \<Longrightarrow> oldest_token q' n = Some j \<Longrightarrow> i \<noteq> j"
  by (metis configuration_Min_in configuration_distinct disjoint_iff_not_equal option.distinct(1) oldest_token.simps option.sel)

lemma oldest_token_equal:
  "oldest_token q n = Some i \<Longrightarrow> oldest_token q' n = Some i \<Longrightarrow> q = q'"
  using oldest_token_distinct by blast

subsubsection \<open>Monotonicity\<close>

lemma oldest_token_monotonic_Suc:
  assumes "x \<le> n"
  assumes "oldest_token (token_run x n) n = Some i"
  assumes "oldest_token (token_run x (Suc n)) (Suc n) = Some j"
  shows "i \<ge> j"
proof -
  from assms have "i = Min (configuration (token_run x n) n)"
    and "j = Min (configuration (token_run x (Suc n)) (Suc n))"
    by (metis oldest_token.elims option.discI option.sel)+
  thus ?thesis
    using Min_antimono[OF configuration_monotonic_Suc[OF assms(1)] configuration_non_empty[OF assms(1)] configuration_finite] by blast
qed

subsubsection \<open>Pull-Up and Push-Down\<close>

lemma push_down_oldest_token_configuration:
  "oldest_token q n = Some x \<Longrightarrow> x \<in> configuration q n"
  by (metis configuration_Min_in oldest_token.simps option.distinct(2) option.inject)

lemma push_down_oldest_token_token_run:
  "oldest_token q n = Some x \<Longrightarrow> token_run x n = q"
  using push_down_oldest_token_configuration configuration.simps by blast

subsection \<open>Senior Token\<close>

subsubsection \<open>Properties\<close>

lemma senior_le_token:
  "senior x n \<le> x"
  using oldest_token_always_def[of x n] by fastforce

lemma senior_token_run:
  "senior x n = senior y n \<longleftrightarrow> token_run x n = token_run y n"
  by (metis oldest_token_always_def oldest_token_distinct option.sel senior.simps)

text \<open>The senior of a token is always in the same state\<close>

lemma senior_same_state:
  "token_run (senior x n) n = token_run x n"
proof -
  have X: "{t. t \<le> n \<and> token_run t n = token_run x n} \<noteq> {}"
    by (cases "x \<le> n") auto
  show ?thesis
    using Min_in[OF _ X] by force
qed

lemma senior_senior:
  "senior (senior x n) n = senior x n"
  using senior_same_state senior_token_run by blast

subsubsection \<open>Monotonicity\<close>

lemma senior_monotonic_Suc:
  "x \<le> n \<Longrightarrow> senior x n \<ge> senior x (Suc n)"
  by (metis oldest_token_always_def oldest_token_monotonic_Suc option.sel senior.simps)

subsubsection \<open>Pull-Up and Push-Down\<close>

lemma pull_up_configuration_senior:
  "\<lbrakk>x \<in> configuration q n; y \<in> configuration q n\<rbrakk> \<Longrightarrow> senior x n = senior y n"
  by force

lemma push_down_senior_tokens:
  "\<lbrakk>x \<le> n; y \<le> n; senior x n = senior y n\<rbrakk> \<Longrightarrow> \<exists>q. x \<in> configuration q n \<and> y \<in> configuration q n"
  using senior_token_run pull_up_token_run_tokens by blast

subsection \<open>Set of Older Seniors\<close>

subsubsection \<open>Properties\<close>

lemma older_seniors_cases_subseteq [case_names le ge]:
  assumes "older_seniors x n \<subseteq> older_seniors y n \<Longrightarrow> P"
  assumes "older_seniors x n \<supseteq> older_seniors y n \<Longrightarrow> P"
  shows "P" using assms by fastforce

lemma older_seniors_cases_subset [case_names less equal greater]:
  assumes "older_seniors x n \<subset> older_seniors y n \<Longrightarrow> P"
  assumes "older_seniors x n = older_seniors y n \<Longrightarrow> P"
  assumes "older_seniors x n \<supset> older_seniors y n \<Longrightarrow> P"
  shows "P" using assms older_seniors_cases_subseteq by blast

lemma older_seniors_finite:
  "finite (older_seniors x n)"
  by fastforce

lemma older_seniors_older:
  "y \<in> older_seniors x n \<Longrightarrow> y < x"
  using less_le_trans[OF _ senior_le_token, of y x n] by force

lemma older_seniors_senior_simp:
  "older_seniors (senior x n) n = older_seniors x n"
  unfolding older_seniors.simps senior_senior ..

lemma older_seniors_not_self_referential:
  "senior x n \<notin> older_seniors x n"
  by simp

lemma older_seniors_not_self_referential_2:
  "x \<notin> older_seniors x n"
  using older_seniors_older older_seniors_not_self_referential less_not_refl by blast

lemma older_seniors_subset:
  "y \<in> older_seniors x n \<Longrightarrow> older_seniors y n \<subset> older_seniors x n"
  using older_seniors_not_self_referential_2 by (cases rule: older_seniors_cases_subset) blast+

lemma older_seniors_subset_2:
  assumes "\<not> sink (token_run x n)"
  assumes "older_seniors x n \<subset> older_seniors y n"
  shows "senior x n \<in> older_seniors y n"
proof -
  have "senior x n < senior y n"
    using assms(2) by fastforce
  thus ?thesis
    using assms(1)[unfolded senior_same_state[symmetric, of x n]]
    unfolding older_seniors.simps by blast
qed

lemmas older_seniors_Max_in = Max_in[OF older_seniors_finite]
lemmas older_seniors_Min_in = Min_in[OF older_seniors_finite]
lemmas older_seniors_Max_coboundedI = Max.coboundedI[OF older_seniors_finite]
lemmas older_seniors_Min_coboundedI = Min.coboundedI[OF older_seniors_finite]
lemmas older_seniors_card_mono = card_mono[OF older_seniors_finite]
lemmas older_seniors_psubset_card_mono = psubset_card_mono[OF older_seniors_finite]

lemma older_seniors_recursive:
  fixes x n
  defines "os \<equiv> older_seniors x n"
  assumes "os \<noteq> {}"
  shows "os = {Max os} \<union> older_seniors (Max os) n"
  (is "?lhs = ?rhs")
proof
  show "?lhs \<subseteq> ?rhs"
  proof
    fix x
    assume "x \<in> ?lhs"
    show "x \<in> ?rhs"
    proof (cases "x = Max os")
      case False
        hence "x < Max os"
          by (metis older_seniors_Max_coboundedI os_def \<open>x \<in> os\<close> dual_order.order_iff_strict)
        moreover
        obtain y' where "Max os = senior y' n"
          using older_seniors_Max_in assms(2)
          unfolding os_def older_seniors.simps by blast
        ultimately
        have "x < senior (Max os) n"
          using senior_senior by presburger
        moreover
        from \<open>x \<in> ?lhs\<close> obtain y where "x = senior y n" and "\<not> sink (token_run x n)"
          unfolding os_def older_seniors.simps by blast
        ultimately
        show ?thesis
          unfolding older_seniors.simps by blast
    qed blast
  qed
next
  show "?lhs \<supseteq> ?rhs"
    using older_seniors_subset older_seniors_Max_in assms(2)
    unfolding os_def by blast
qed

lemma older_seniors_recursive_card:
  fixes x n
  defines "os \<equiv> older_seniors x n"
  assumes "os \<noteq> {}"
  shows "card os = Suc (card (older_seniors (Max os) n))"
  by (metis older_seniors_recursive assms Un_empty_left Un_insert_left card_insert_disjoint older_seniors_finite older_seniors_not_self_referential_2)

lemma older_seniors_card:
  "card (older_seniors x n) = card (older_seniors y n) \<longleftrightarrow> older_seniors x n = older_seniors y n"
  by (metis less_not_refl older_seniors_cases_subset older_seniors_psubset_card_mono)

lemma older_seniors_card_le:
  "card (older_seniors x n) < card (older_seniors y n) \<longleftrightarrow> older_seniors x n \<subset> older_seniors y n"
  by (metis card_mono card_psubset not_le older_seniors_cases_subseteq older_seniors_finite psubset_card_mono)

lemma older_seniors_card_less:
  "card (older_seniors x n) \<le> card (older_seniors y n) \<longleftrightarrow> older_seniors x n \<subseteq> older_seniors y n"
   by (metis not_le older_seniors_card_mono older_seniors_cases_subseteq older_seniors_psubset_card_mono subset_not_subset_eq)

subsubsection \<open>Monotonicity\<close>

lemma older_seniors_monotonic_Suc:
  assumes "x \<le> n"
  shows "older_seniors x n \<supseteq> older_seniors x (Suc n)"
proof
  fix y
  assume "y \<in> older_seniors x (Suc n)"
  then obtain ox where "y = senior ox (Suc n)"
    and "y < senior x (Suc n)"
    and "\<not> sink (token_run y (Suc n))"
    unfolding older_seniors.simps by blast

  hence "y = senior y n"
    using senior_senior senior_le_token senior_monotonic_Suc assms
    by (metis add.commute add.left_commute dual_order.order_iff_strict linear not_add_less1 not_less le_iff_add)
  moreover
  have "y < senior x n"
    using assms less_le_trans[OF \<open>y < senior x (Suc n)\<close> senior_monotonic_Suc]
    by blast
  moreover
  have "\<not> sink (token_run y n)"
    using \<open>\<not> sink (token_run y (Suc n))\<close> token_stays_in_sink
    unfolding Suc_eq_plus1 by metis

  ultimately
  show "y \<in> older_seniors x n"
    unfolding older_seniors.simps by blast
qed

lemma older_seniors_monotonic:
  "x \<le> n \<Longrightarrow> older_seniors x n \<supseteq> older_seniors x (n + m)"
  by (induction m) (simp, metis older_seniors_monotonic_Suc add_Suc_right dual_order.trans trans_le_add1)

lemma older_seniors_stable:
  "x \<le> n \<Longrightarrow> older_seniors x n = older_seniors x (n + m + m') \<Longrightarrow> older_seniors x n = older_seniors x (n + m)"
  by (induction m') (simp, unfold set_eq_subset, metis dual_order.trans le_add1 older_seniors_monotonic)

lemma card_older_seniors_monotonic:
  "x \<le> n \<Longrightarrow> card (older_seniors x n) \<ge> card (older_seniors x (n + m))"
  using older_seniors_monotonic older_seniors_card_mono by meson

subsubsection \<open>Pull-Up and Push-Down\<close>

lemma pull_up_senior_older_seniors:
  "senior x n = senior y n \<Longrightarrow> older_seniors x n = older_seniors y n"
  unfolding older_seniors.simps senior.simps senior_token_run by presburger

lemma pull_up_senior_older_seniors_less:
  "senior x n < senior y n \<Longrightarrow> older_seniors x n \<subseteq> older_seniors y n"
  by force

lemma pull_up_senior_older_seniors_less_2:
  assumes "\<not> sink (token_run x n)"
  assumes "senior x n < senior y n"
  shows "older_seniors x n \<subset> older_seniors y n"
proof -
  from assms have "senior x n \<in> older_seniors y n"
    unfolding senior_same_state[of x n, symmetric] older_seniors.simps by blast
  thus ?thesis
    using older_seniors_not_self_referential pull_up_senior_older_seniors_less[OF assms(2)] by blast
qed

lemma pull_up_senior_older_seniors_le:
  "senior x n \<le> senior y n \<Longrightarrow> older_seniors x n \<subseteq> older_seniors y n"
  using pull_up_senior_older_seniors pull_up_senior_older_seniors_less
  unfolding dual_order.order_iff_strict by blast

lemma push_down_older_seniors_senior:
  assumes "\<not> sink (token_run x n)"
  assumes "\<not> sink (token_run y n)"
  assumes "older_seniors x n = older_seniors y n"
  shows "senior x n = senior y n"
  using assms by (cases "senior x n" " senior y n" rule: linorder_cases) (fast dest: pull_up_senior_older_seniors_less_2)+

subsubsection \<open>Tower Lemma\<close>

lemma older_seniors_tower'':
  assumes "x \<le> n"
  assumes "y \<le> n"
  assumes "\<not>sink (token_run x n)"
  assumes "\<not>sink (token_run y n)"
  assumes "older_seniors x n = older_seniors x (Suc n)"
  assumes "older_seniors y n \<subseteq> older_seniors x n"
  shows "older_seniors y n = older_seniors y (Suc n)"
proof
  {
    fix s
    assume "s \<in> older_seniors y n" and "older_seniors y n \<subset> older_seniors x n"
    hence "s \<in> older_seniors x n"
      using assms by blast
    hence "\<not>sink (token_run s (Suc n))" and "\<exists>z. s = senior z (Suc n)"
      unfolding assms by simp+
    moreover
    have "senior y n \<le> senior y (Suc n)"
    proof (rule ccontr)
      assume "\<not>senior y n \<le> senior y (Suc n)"
      moreover
      have "senior y n \<le> n"
        by (metis assms(2) senior_le_token le_trans)
      ultimately
      have "\<forall>z. senior y n \<noteq> senior z (Suc n)"
        using token_run_merge_Suc[unfolded senior_token_run[symmetric], OF \<open>y \<le> n\<close>]
        by (metis senior_senior le_refl)
      hence "senior y n \<notin> older_seniors x (Suc n)"
        using assms by simp
      moreover
      have "senior y n \<in> older_seniors x n"
        using assms \<open>older_seniors y n \<subset> older_seniors x n\<close> older_seniors_subset_2 by meson
      ultimately
      show False
        unfolding assms ..
    qed
    hence "s < senior y (Suc n)"
      using \<open>s \<in> older_seniors y n\<close> by fastforce
    ultimately
    have "s \<in> older_seniors y (Suc n)"
      unfolding older_seniors.simps by blast
  }
  moreover
  {
    fix s
    assume "s \<in> older_seniors y n" and "older_seniors y n = older_seniors x n"
    moreover
    hence "senior y n = senior x n"
      using assms(3-4) push_down_older_seniors_senior by blast
    hence "senior y (Suc n) = senior x (Suc n)"
      using token_run_merge_Suc[OF assms(2,1)] unfolding senior_token_run by blast
    ultimately
    have "s \<in> older_seniors y (Suc n)"
      by (metis assms(5) older_seniors_senior_simp)
  }
  ultimately
  show "older_seniors y n \<subseteq> older_seniors y (Suc n)"
    using assms by blast
qed (metis older_seniors_monotonic_Suc assms(2))

lemma older_seniors_tower''2:
  assumes "x \<le> n"
  assumes "y \<le> n"
  assumes "\<not>sink (token_run x (n + m))"
  assumes "\<not>sink (token_run y (n + m))"
  assumes "older_seniors x n = older_seniors x (n + m)"
  assumes "older_seniors y n \<subseteq> older_seniors x n"
  shows "older_seniors y n = older_seniors y (n + m)"
  using assms
proof (induction m arbitrary: n)
  case (Suc m)
    have "\<not>sink (token_run x (n + m))" and "\<not>sink (token_run y (n + m))"
      using \<open>\<not>sink (token_run x (n + Suc m))\<close> \<open>\<not>sink (token_run y (n + Suc m))\<close>
      using token_stays_in_sink[of _ _ "n + m" 1]
      unfolding Suc_eq_plus1 add.assoc[symmetric] by metis+
    moreover
    have "older_seniors x n = older_seniors x (n + m)"
      using Suc.prems(5) older_seniors_stable[OF \<open>x \<le> n\<close>]
      unfolding Suc_eq_plus1 add.assoc by blast
    moreover
    hence "older_seniors x (n + m) = older_seniors x (Suc (n + m))"
      unfolding Suc.prems add_Suc_right ..
    ultimately
    have "older_seniors y n = older_seniors y (n + m)"
      using Suc by meson
    also
    have "\<dots> = older_seniors y (Suc (n + m))"
      using older_seniors_tower''[OF _ _ \<open>\<not>sink (token_run x (n + m))\<close> \<open>\<not>sink (token_run y (n + m))\<close> \<open>older_seniors x (n + m) = older_seniors x (Suc (n + m))\<close>] Suc
      by (metis \<open>older_seniors x n = older_seniors x (n + m)\<close> add.commute add.left_commute calculation le_iff_add)
    finally
    show ?case
      unfolding add_Suc_right .
qed simp

lemma older_seniors_tower':
  assumes "y \<in> older_seniors x n"
  assumes "older_seniors x n = older_seniors x (Suc n)"
  shows "older_seniors y n = older_seniors y (Suc n)"
  (is "?lhs = ?rhs")
  using assms
proof (induction "card (older_seniors x n)" arbitrary: x y)
  case 0
    hence "older_seniors x n = {}"
      using older_seniors_finite card_eq_0_iff by metis
    thus ?case
      using "0.prems" by blast
next
  case (Suc c)
    let ?os = "older_seniors x n"
    have "?os \<noteq> {}"
      using Suc.prems(1) by blast

    hence "y = Max ?os \<or> y \<in> older_seniors (Max ?os) n"
      using Suc.prems(1) older_seniors_recursive by blast
    moreover
    have "older_seniors (Max ?os) n = older_seniors (Max ?os) (Suc n)"
      using Suc.prems(2) older_seniors_recursive \<open>?os \<noteq> {}\<close> older_seniors_not_self_referential_2
      by (metis Un_empty_left Un_insert_left insert_ident)
    moreover
    {
      fix s
      assume "s \<in> older_seniors (Max ?os) n"
      moreover
      from Suc.hyps(2) have "card (older_seniors (Max ?os) n) = c"
        unfolding older_seniors_recursive_card[OF \<open>?os \<noteq> {}\<close>] by blast
      ultimately
      have "older_seniors s n = older_seniors s (Suc n)"
        by (metis Suc.hyps(1) \<open>older_seniors (Max ?os) n = older_seniors (Max ?os) (Suc n)\<close>)
    }
    ultimately
    show ?case
      by blast
qed

lemma older_seniors_tower:
  "\<lbrakk>x \<le> n; y \<in> older_seniors x n; older_seniors x n = older_seniors x (n + m)\<rbrakk> \<Longrightarrow> older_seniors y n = older_seniors y (n + m)"
proof (induction m)
  case (Suc m)
    hence "older_seniors x n = older_seniors x (n + m)"
      using older_seniors_monotonic older_seniors_monotonic_Suc subset_antisym
      by (metis Nat.add_0_right add.assoc add_Suc_shift trans_le_add1)
    hence "older_seniors y n = older_seniors y (n + m)"
      using Suc.IH[OF Suc.prems(1,2)] by blast
    also
    have "\<dots> = older_seniors y (n + Suc m)"
      using older_seniors_tower'[of y x "n + m"] Suc.prems unfolding add_Suc_right
      by (metis \<open>older_seniors x n = older_seniors x (n + m)\<close>)
    finally
    show ?case .
qed simp

subsection \<open>Rank\<close>

subsubsection \<open>Properties\<close>

lemma rank_None_before:
  "x > n \<Longrightarrow> rank x n = None"
  by simp

lemma rank_None_Suc:
  assumes "x \<le> n"
  assumes "rank x n = None"
  shows "rank x (Suc n) = None"
proof -
  have "sink (token_run x n)"
    using assms by (metis option.distinct(1) rank.simps)
  hence "sink (token_run x (Suc n))"
    using token_stays_in_sink by (metis (erased, hide_lams) Suc_leD le_Suc_ex not_less_eq_eq)
  thus ?thesis
    by simp
qed

lemma rank_Some_time:
  "rank x n = Some j \<Longrightarrow> x \<le> n"
  by (metis option.distinct(1) rank.simps)

lemma rank_Some_sink:
  "rank x n = Some j \<Longrightarrow> \<not>sink (token_run x n)"
  by fastforce

lemma rank_Some_card:
  "rank x n = Some j \<Longrightarrow> card (older_seniors x n) = j"
  by (metis option.distinct(1) option.inject rank.simps)

lemma rank_initial:
  "\<exists>i. rank x x = Some i"
  unfolding rank.simps sink_def by force

lemma rank_continuous:
  assumes "rank x n = Some i"
  assumes "rank x (n + m) = Some j"
  assumes "m' \<le> m"
  shows "\<exists>k. rank x (n + m') = Some k"
  using assms
proof (induction m arbitrary: j m')
  case (Suc m)
    thus ?case
    proof (cases "m' = Suc m")
      case False
        with Suc.prems have "m' \<le> m"
          by linarith
        moreover
        obtain j' where "rank x (n + m) = Some j'"
          using Suc.prems(1,2) rank_Some_time rank_None_Suc
          by (metis add_Suc_right add_lessD1 not_less rank.simps)
        ultimately
        show ?thesis
          using Suc.IH[OF Suc.prems(1)] by blast
    qed simp
qed simp

lemma rank_token_squats:
  "token_squats x \<Longrightarrow> x \<le> n \<Longrightarrow> \<exists>i. rank x n = Some i"
  unfolding token_squats_def by simp

lemma rank_older_seniors_bounded:
  assumes "y \<in> older_seniors x n"
  assumes "rank x n = Some j"
  shows "\<exists>j' < j. rank y n = Some j'"
proof -
  from assms(1) have "\<not>sink (token_run y n)"
    by simp
  moreover
  from assms have "y \<le> n"
    by (metis dual_order.trans linear not_less older_seniors_older option.distinct(1) rank.simps)
  moreover
  have "older_seniors y n \<subset> older_seniors x n"
    using older_seniors_subset assms(1) by presburger
  hence "card (older_seniors y n) < card (older_seniors x n)"
    by (rule older_seniors_psubset_card_mono)
  ultimately
  show ?thesis
    using rank_Some_card[OF assms(2)] rank.simps by meson
qed

subsubsection \<open>Bounds\<close>

lemma max_rank_lowerbound:
  "0 < max_rank"
proof -
  obtain a where "a \<in> \<Sigma>"
    using nonempty_\<Sigma> by blast
  hence "range (\<lambda>_. a) \<subseteq> \<Sigma>" and "q\<^sub>0 = run \<delta> q\<^sub>0 (\<lambda>_. a) 0"
    by auto
  hence "q\<^sub>0 \<in> reach \<Sigma> \<delta> q\<^sub>0"
    unfolding reach_def by blast
  thus ?thesis
    using reach_card_0[OF nonempty_\<Sigma>] finite_reach max_rank_def sink_def by force
qed

lemma older_seniors_card_bounded:
  assumes "\<not>sink (token_run x n)" and "x \<le> n"
  shows "card (older_seniors x n) < card (reach \<Sigma> \<delta> q\<^sub>0 - {q. sink q})"
  (is "card ?S4 < card ?S0")
proof -
  let ?S1 = "{token_run x n | x n. True} - {q. sink q}"
  let ?S2 = "(\<lambda>q. the (oldest_token q n)) ` ?S1"
  let ?S3 = "{s. \<exists>x. s = senior x n \<and> \<not>(sink (token_run s n))}"

  have "?S1 \<subseteq> ?S0"
    unfolding reach_def token_run.simps using bounded_w by fastforce
  hence "finite ?S1" and C1: "card ?S1 \<le> card ?S0"
    using finite_reach card_mono finite_subset
   apply (simp add: finite_subset) by (metis \<open>{token_run x n |x n. True} - Collect sink \<subseteq> reach \<Sigma> \<delta> q\<^sub>0 - Collect sink\<close> card_mono finite_Diff local.finite_reach)
  hence "finite ?S2" and C2: "card ?S2 \<le> card ?S1"
    using finite_imageI card_image_le by blast+
  moreover
  have "?S3 \<subseteq> ?S2"
  proof
    fix s
    assume "s \<in> ?S3"
    hence "s = senior s n" and "\<not>sink (token_run s n)"
      using senior_senior by fastforce+
    thus "s \<in> ?S2"
      by auto
  qed
  ultimately
  have "finite ?S3" and C3: "card ?S3 \<le> card ?S2"
    using card_mono finite_subset by blast+
  moreover
  have "senior x n \<in> ?S3" and "senior x n \<notin> ?S4" and "?S4 \<subseteq> ?S3"
    using assms older_seniors_not_self_referential senior_same_state by auto
  hence "?S4 \<subset> ?S3"
    by blast
  ultimately
  have "finite ?S4" and C4: "card ?S4 < card ?S3"
    using psubset_card_mono finite_subset by blast+
  show ?thesis
    using C1 C2 C3 C4 by linarith
qed

lemma rank_upper_bound:
  "rank x n = Some i \<Longrightarrow> i < max_rank"
  using older_seniors_card_bounded unfolding max_rank_def
  by (fast dest: rank_Some_card rank_Some_time rank_Some_sink )

lemma rank_range:
  "\<exists>i. range (rank x) \<subseteq> {None} \<union> Some ` {0..<i}"
proof
  {
    fix i_option
    assume "i_option \<in> range (rank x)"
    hence "i_option \<in> {None} \<union> Some ` {0..<max_rank}"
    proof (cases i_option)
      case (Some i)
        hence "i \<in> {0..<max_rank}"
          using \<open>i_option \<in> range (rank x)\<close> rank_upper_bound by force
        thus ?thesis
          using Some by blast
    qed blast
  }
  thus "range (rank x) \<subseteq> ({None} \<union> Some ` {0..<max_rank})" ..
qed

subsubsection \<open>Monotonicity\<close>

lemma rank_monotonic:
  "\<lbrakk>rank x n = Some i; rank x (n + m) = Some j\<rbrakk> \<Longrightarrow> i \<ge> j"
  using card_older_seniors_monotonic rank_Some_card rank_Some_time by metis

subsubsection \<open>Pull-Up and Push-Down\<close>

lemma pull_up_senior_rank:
  "\<lbrakk>x \<le> n; y \<le> n; senior x n = senior y n\<rbrakk> \<Longrightarrow> rank x n = rank y n"
  by (metis senior_token_run rank.simps pull_up_senior_older_seniors)

lemma pull_up_configuration_rank:
  "\<lbrakk>x \<in> configuration q n; y \<in> configuration q n\<rbrakk> \<Longrightarrow> rank x n = rank y n"
  by force

lemma push_down_rank_older_seniors:
  "\<lbrakk>rank x n = rank y n; rank x n = Some i\<rbrakk> \<Longrightarrow> older_seniors x n = older_seniors y n"
  by (metis older_seniors_card option.distinct(2) option.sel rank.simps)

lemma push_down_rank_senior:
  "\<lbrakk>rank x n = rank y n; rank x n = Some i\<rbrakk> \<Longrightarrow> senior x n = senior y n"
  by (metis push_down_rank_older_seniors push_down_older_seniors_senior option.distinct(1) rank.elims)

lemma push_down_rank_tokens:
  "\<lbrakk>rank x n = rank y n; rank x n = Some i\<rbrakk> \<Longrightarrow> (\<exists>q. x \<in> configuration q n \<and> y \<in> configuration q n)"
  by (metis push_down_senior_tokens rank_Some_time push_down_rank_senior)

subsubsection \<open>Pulled-Up Lemmas\<close>

lemma rank_senior_senior:
  "x \<le> n \<Longrightarrow> rank (senior x n) n = rank x n"
  by (metis le_iff_add add.commute add.left_commute pull_up_senior_rank senior_le_token senior_senior)

subsubsection \<open>Stable Rank\<close>

definition stable_rank :: "nat \<Rightarrow> nat \<Rightarrow> bool"
where
  "stable_rank x i = (\<forall>\<^sub>\<infinity>n. rank x n = Some i)"

lemma stable_rank_unique:
  assumes "stable_rank x i"
  assumes "stable_rank x j"
  shows "i = j"
proof -
  from assms obtain n m where "\<And>n'. n' \<ge> n \<Longrightarrow> rank x n' = Some i"
    and "\<And>m'. m' \<ge> m \<Longrightarrow> rank x m' = Some j"
    unfolding stable_rank_def MOST_nat_le by blast
  hence "rank x (n + m) = Some i" and "rank x (n + m) = Some j"
    by (metis add.commute le_add1)+
  thus ?thesis
    by simp
qed

lemma stable_rank_equiv_token_squats:
  "token_squats x = (\<exists>i. stable_rank x i)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  define ranks where "ranks = {j | j n. rank x n = Some j}"
  hence "ranks \<subseteq> {0..<max_rank}" and "the (rank x x) \<in> ranks"
    using rank_upper_bound rank_initial[of x] unfolding ranks_def by fastforce+ (* Takes roughly 10s *)
  hence "finite ranks" and "ranks \<noteq> {}"
    using finite_reach finite_atLeastAtMost infinite_super by fast+

  define i where "i = Min ranks"
  obtain n where "rank x n = Some i"
    using Min_in[OF \<open>finite ranks\<close> \<open>ranks \<noteq> {}\<close>]
    unfolding i_def ranks_def by blast

  have "\<And>j. j \<in> ranks \<Longrightarrow> j \<ge> i"
    using Min_in[OF \<open>finite ranks\<close> \<open>ranks \<noteq> {}\<close>] unfolding i_def
    by (metis Min.coboundedI \<open>finite ranks\<close>)
  hence "\<And>m j. rank x (n + m) = Some j \<Longrightarrow> j \<ge> i"
    unfolding ranks_def by blast
  moreover
  have "\<And>m j. rank x (n + m) = Some j \<Longrightarrow> j \<le> i"
    using rank_monotonic[OF \<open>rank x n = Some i\<close>] by blast
  moreover
  have "\<And>m. \<exists>j. rank x (n + m) = Some j"
    using rank_token_squats[OF \<open>?lhs\<close>] rank_Some_time[OF \<open>rank x n = Some i\<close>] by simp
  ultimately
  have "\<And>m. rank x (n + m) = Some i"
    by (metis le_antisym)
  thus ?rhs
    unfolding stable_rank_def MOST_nat_le by (metis le_iff_add)
next
  assume ?rhs
  thus ?lhs
    unfolding token_squats_def stable_rank_def MOST_nat_le
    by (metis le_add2 rank_Some_sink token_stays_in_sink)
qed

lemma stable_rank_same_tokens:
  assumes "stable_rank x i"
  assumes "stable_rank y j"
  assumes "x \<in> configuration q n"
  assumes "y \<in> configuration q n"
  shows "i = j"
proof -
  from assms(1) obtain n_i where "n_i \<ge> n" and "\<forall>t \<ge> n_i. rank x t = Some i"
    unfolding stable_rank_def MOST_nat_le by (metis linear order_trans)
  moreover
  from assms(2) obtain n_j where "n_j \<ge> n" and "\<forall>t \<ge> n_j. rank y t = Some j"
    unfolding stable_rank_def MOST_nat_le by (metis linear order_trans)
  moreover
  define m where "m = max n_i n_j"
  ultimately
  have "rank x m = Some i" and "rank y m = Some j"
    by (metis max.bounded_iff order_refl)+
  moreover
  have "m \<ge> n"
    by (metis \<open>n \<le> n_j\<close> le_trans max.cobounded2 m_def)
  have "\<exists>q'. x \<in> configuration q' m \<and> y \<in> configuration q' m"
    using push_down_configuration_token_run[OF assms(3,4)]
    using token_run_merge[of x n y]
    using pull_up_token_run_tokens[of x m y]
    using \<open>m \<ge> n\<close>[unfolded le_iff_add] by force
  ultimately
  show ?thesis
    using pull_up_configuration_rank by (metis option.inject)
qed

subsubsection \<open>Tower Lemma\<close>

lemma rank_tower:
  assumes "i \<le> j"
  assumes "rank x n = Some j"
  assumes "rank x (n + m) = Some j"
  assumes "rank y n = Some i"
  shows "rank y (n + m) = Some i"
proof (cases i j rule: linorder_cases)
  case less
    {
      hence "card (older_seniors (senior y n) n) < card (older_seniors x n)"
        using assms rank_Some_card senior_same_state by force
      hence "senior y n \<in> older_seniors x n"
        by (metis older_seniors_card_le rank_Some_sink assms(4) older_seniors_senior_simp older_seniors_subset_2)
      moreover
      have "older_seniors x n = older_seniors x (n + m)"
        by (metis assms(2,3) rank_Some_card rank_Some_time card_subset_eq[OF older_seniors_finite] older_seniors_monotonic)
      ultimately
      have "older_seniors (senior y n) n = older_seniors (senior y n) (n + m)" and "senior y n \<in> older_seniors x (n + m)"
        using older_seniors_tower rank_Some_time assms(2) by blast+
    }
    moreover
    have "rank (senior y n) n = Some i"
      by (metis assms(4) rank_Some_time rank_senior_senior)
    ultimately
    have "rank (senior y n) (n + m) = Some i"
      by (metis rank_older_seniors_bounded[OF _ assms(3)] rank_Some_card)
    moreover
    have "senior y n \<le> n"
      by (metis \<open>rank (senior y n) n = Some i\<close> rank_Some_time)
    hence "senior y n \<in> configuration (token_run y (n + m)) (n + m)"
      by (metis (full_types) token_run_merge[OF _ rank_Some_time[OF assms(4)] senior_same_state] configuration_token trans_le_add1)
    ultimately
    show ?thesis
      by (metis pull_up_configuration_rank le_iff_add add.assoc assms(4) configuration_token rank_Some_time)
next
  case equal
    hence "x \<le> n" and "y \<le> n" and "token_run x n = token_run y n"
      using assms(2-4) push_down_rank_tokens by force+
    moreover
    hence "token_run x (n + m) = token_run y (n + m)"
      using token_run_merge by blast
    ultimately
    show ?thesis
      by (metis assms(3) equal rank_senior_senior senior_token_run le_iff_add add.assoc)
qed (insert \<open>i \<le> j\<close>, linarith)

lemma stable_rank_alt_def:
  "rank x n = Some j \<and> stable_rank x j \<longleftrightarrow> (\<forall>m \<ge> n. rank x m = Some j)"
  (is "?rhs \<longleftrightarrow> ?lhs")
proof
  assume ?rhs
  then obtain m' where "\<forall>m \<ge> m'. rank x m = Some j"
    unfolding stable_rank_def MOST_nat_le by blast
  moreover
  hence "rank x n = Some j" and "rank x m' = Some j"
    using \<open>?rhs\<close> by blast+
  {
    fix m
    assume "n \<le> n + m" and "n + m < m'"
    then obtain j' where "rank x (n + m) = Some j'"
      by (metis \<open>?rhs\<close> stable_rank_equiv_token_squats rank_Some_time rank_token_squats trans_le_add1)
    moreover
    hence "j' \<le> j"
      using \<open>rank x n = Some j\<close> rank_monotonic by blast
    moreover
    have "j \<le> j'"
      using \<open>rank x (n + m) = Some j'\<close> \<open>rank x m' = Some j\<close>  \<open>n + m < m'\<close> rank_monotonic
      by (metis add_Suc_right less_imp_Suc_add)
    ultimately
    have "rank x (n + m) = Some j"
      by simp
  }
  ultimately
  show ?lhs
    by (metis le_add_diff_inverse not_le)
qed (unfold stable_rank_def MOST_nat_le, blast)

lemma stable_rank_tower:
  assumes "j \<le> i"
  assumes "rank x n = Some j"
  assumes "rank y n = Some i"
  assumes "stable_rank y i"
  shows "stable_rank x j"
  using assms rank_tower[OF \<open>j \<le> i\<close>] stable_rank_alt_def[of y n i]
  unfolding stable_rank_def[of x j, unfolded MOST_nat_le] by (metis le_Suc_ex)

subsection \<open>Senior States\<close>

lemma senior_states_initial:
  "senior_states q 0 = {}"
  by simp

lemma senior_states_cases_subseteq [case_names le ge]:
  assumes "senior_states p n \<subseteq> senior_states q n \<Longrightarrow> P"
  assumes "senior_states p n \<supseteq> senior_states q n \<Longrightarrow> P"
  shows "P" using assms by force

lemma senior_states_cases_subset [case_names less equal greater]:
  assumes "senior_states p n \<subset> senior_states q n \<Longrightarrow> P"
  assumes "senior_states p n = senior_states q n \<Longrightarrow> P"
  assumes "senior_states p n \<supset> senior_states q n \<Longrightarrow> P"
  shows "P" using assms senior_states_cases_subseteq by blast

lemma senior_states_finite:
  "finite (senior_states q n)"
  by fastforce

lemmas senior_states_card_mono = card_mono[OF senior_states_finite]
lemmas senior_states_psubset_card_mono = psubset_card_mono[OF senior_states_finite]

lemma senior_states_card:
  "card (senior_states p n) = card (senior_states q n) \<longleftrightarrow> senior_states p n = senior_states q n"
  by (metis less_not_refl senior_states_cases_subset senior_states_psubset_card_mono)

lemma senior_states_card_le:
  "card (senior_states p n) < card (senior_states q n) \<longleftrightarrow> senior_states p n \<subset> senior_states q n"
  by (metis card_mono not_less senior_states_cases_subseteq senior_states_finite senior_states_psubset_card_mono subset_not_subset_eq)

lemma senior_states_card_less:
  "card (senior_states p n) \<le> card (senior_states q n) \<longleftrightarrow> senior_states p n \<subseteq> senior_states q n"
  by (metis card_mono card_seteq senior_states_cases_subseteq senior_states_finite)

lemma senior_states_older_seniors:
  "(\<lambda>y. token_run y n) ` older_seniors x n = senior_states (token_run x n) n"
  (is "?lhs = ?rhs")
proof -
  have "?lhs = {q'. \<exists>ost ot. q' = token_run ost n \<and> ost = senior ot n \<and> ost < senior x n \<and> \<not> sink q'}"
    by auto
  also
  have "\<dots> = {q'. \<exists>t ot. oldest_token q' n = Some t \<and> t = senior ot n \<and> t < senior x n \<and> \<not> sink q'}"
    unfolding senior.simps by (metis (erased, hide_lams) oldest_token_always_def push_down_oldest_token_token_run option.sel)
  also
  have "\<dots> = {q'. \<exists>t. oldest_token q' n = Some t \<and> t < senior x n \<and> \<not> sink q'}"
    by auto
  also
  have "\<dots> = ?rhs"
    unfolding senior_states.simps senior.simps by (metis (erased, hide_lams) oldest_token_always_def option.sel)
  finally
  show "?lhs = ?rhs"
    .
qed

lemma card_older_senior_senior_states:
  assumes "x \<in> configuration q n"
  shows "card (older_seniors x n) = card (senior_states q n)"
  (is "?lhs = ?rhs")
proof -
  have "inj_on (\<lambda>t. token_run t n) (older_seniors x n)"
    unfolding inj_on_def using senior_same_state
    by (fastforce simp del: token_run.simps)
  moreover
  have "token_run x n = q"
    using assms by simp
  ultimately
  show "?lhs = ?rhs"
    using card_image[of "(\<lambda>t. token_run t n)" "older_seniors x n"]
    unfolding senior_states_older_seniors by presburger
qed

subsection \<open>Rank of States\<close>

subsubsection \<open>Alternative Definitions\<close>

lemma state_rank_eq_rank:
  "state_rank q n = (case oldest_token q n of None \<Rightarrow> None | Some t \<Rightarrow> rank t n) "
  (is "?lhs = ?rhs")
proof (cases "oldest_token q n")
  case (None)
    thus ?thesis
      by (metis not_Some_eq oldest_token.elims option.simps(4) state_rank.elims)
next
  case (Some x)
    hence "?lhs = (if \<not>sink q then Some (card (older_seniors x n)) else None)"
      by (metis emptyE push_down_oldest_token_configuration[OF Some] card_older_senior_senior_states state_rank.simps)
    also
    have "\<dots> = rank x n"
      using oldest_token_bounded[OF Some] push_down_oldest_token_token_run[OF Some] by auto
    also
    have "\<dots> = ?rhs"
      using Some by force
    finally
    show ?thesis .
qed

lemma state_rank_eq_rank_SOME:
  "state_rank q n = (if configuration q n \<noteq> {} then rank (SOME x. x \<in> configuration q n) n else None)"
proof (cases "oldest_token q n")
  case (Some x)
    thus ?thesis
      unfolding state_rank_eq_rank Some option.simps(5)
      by (metis Some ex_in_conv pull_up_configuration_rank push_down_oldest_token_configuration someI_ex)
qed (unfold state_rank_eq_rank; metis not_Some_eq oldest_token.elims option.simps(4))

lemma rank_eq_state_rank:
  "x \<le> n \<Longrightarrow> rank x n = state_rank (token_run x n) n"
  unfolding state_rank_eq_rank_SOME[of "token_run x n"]
  by (metis all_not_in_conv configuration_token pull_up_configuration_rank someI_ex)

subsubsection \<open>Pull-Up and Push-Down\<close>

lemma pull_up_configuration_state_rank:
  "configuration q n = {} \<Longrightarrow> state_rank q n = None"
  by force

lemma push_down_state_rank_tokens:
  "state_rank q n = Some i \<Longrightarrow> configuration q n \<noteq> {}"
  by (metis not_Some_eq state_rank.elims)

lemma push_down_state_rank_configuration_None:
  "state_rank q n = None \<Longrightarrow> \<not>sink q \<Longrightarrow> configuration q n = {}"
  unfolding state_rank.simps by (metis option.distinct(1))

lemma push_down_state_rank_oldest_token:
  "state_rank q n = Some i \<Longrightarrow> \<exists>x. oldest_token q n = Some x"
  by (metis oldest_token.elims state_rank.elims)

lemma push_down_state_rank_token_run:
  "state_rank q n = Some i \<Longrightarrow> \<exists>x. token_run x n = q \<and> x \<le> n"
  by (blast dest: push_down_state_rank_oldest_token push_down_oldest_token_token_run oldest_token_bounded)

subsubsection \<open>Properties\<close>

lemma state_rank_distinct:
  assumes distinct: "p \<noteq> q"
  assumes ranked_1: "state_rank p n = Some i"
  assumes ranked_2: "state_rank q n = Some j"
  shows "i \<noteq> j"
proof
  assume "i = j"
  obtain x y where "x \<in> configuration p n" and "y \<in> configuration q n"
    using assms push_down_state_rank_tokens by blast
  hence "rank x n = Some i" and "rank y n = Some j"
    using assms pull_up_configuration_rank unfolding state_rank_eq_rank_SOME
    by (metis all_not_in_conv someI_ex)+
  hence "x \<in> configuration q n"
    using \<open>y \<in> configuration q n\<close> push_down_rank_tokens
    unfolding \<open>i = j\<close> by auto
  hence "p = q"
    using \<open>x \<in> configuration p n\<close> by fastforce
  thus "False"
    using distinct by blast
qed

lemma state_rank_initial_state:
  obtains i where "state_rank q\<^sub>0 n = Some i"
  unfolding state_rank.simps sink_def by fastforce

lemma state_rank_sink:
  "sink q \<Longrightarrow> state_rank q n = None"
  by simp

lemma state_rank_upper_bound:
  "state_rank q n = Some i \<Longrightarrow> i < max_rank"
  by (metis option.simps(5) rank_upper_bound push_down_state_rank_oldest_token state_rank_eq_rank)

lemma state_rank_range:
  "state_rank q n \<in> {None} \<union> Some ` {0..<max_rank}"
  by (cases "state_rank q n") (simp add: state_rank_upper_bound[of q n])+

lemma state_rank_None:
  "\<not>sink q \<Longrightarrow> state_rank q n = None \<longleftrightarrow> oldest_token q n = None"
  by simp

lemma state_rank_Some:
  "\<not>sink q \<Longrightarrow> (\<exists>i. state_rank q n = Some i) \<longleftrightarrow> (\<exists>j. oldest_token q n = Some j)"
  by simp

lemma state_rank_oldest_token:
  assumes "state_rank p n = Some i"
  assumes "state_rank q n = Some j"
  assumes "oldest_token p n = Some x"
  assumes "oldest_token q n = Some y"
  shows "i < j \<longleftrightarrow> x < y"
proof -
  have "configuration p n \<noteq> {}" and "configuration q n \<noteq> {}"
    using assms(3,4) by (metis oldest_token.simps option.distinct(1))+
  moreover
  have "\<not>sink p" and "\<not>sink q"
    using assms(1,2) state_rank_sink by auto
  ultimately
  have i_def: "i = card (senior_states p n)" and j_def: "j = card (senior_states q n)"
    using assms(1,2) option.sel by simp_all
  hence "i < j \<longleftrightarrow> senior_states p n \<subset> senior_states q n"
    using senior_states_card_le by presburger
  also
  with assms(3,4) have "\<dots> \<longleftrightarrow> x < y"
  proof (cases rule: senior_states_cases_subset[of p n q])
    case equal
      thus ?thesis
        using assms state_rank_distinct i_def j_def
        by (metis less_irrefl option.sel)
  qed auto
  ultimately
  show ?thesis
    by meson
qed

lemma state_rank_oldest_token_le:
  assumes "state_rank p n = Some i"
  assumes "state_rank q n = Some j"
  assumes "oldest_token p n = Some x"
  assumes "oldest_token q n = Some y"
  shows "i \<le> j \<longleftrightarrow> x \<le> y"
  using state_rank_oldest_token[OF assms] assms state_rank_distinct oldest_token_equal
  by (cases "x = y") ((metis option.sel order_refl), (metis le_eq_less_or_eq option.inject))

lemma state_rank_in_function_set:
  shows "(\<lambda>q. state_rank q t) \<in> {f. (\<forall>x. x \<notin> reach \<Sigma> \<delta> q\<^sub>0 \<longrightarrow> f x = None) \<and>
      (\<forall>x. x \<in> reach \<Sigma> \<delta> q\<^sub>0 \<longrightarrow> f x \<in> {None} \<union> Some ` {0..<max_rank})}"
proof -
  {
    fix x
    assume "x \<notin> reach \<Sigma> \<delta> q\<^sub>0"
    hence "\<And>token. x \<noteq> token_run token t"
      unfolding reach_def token_run.simps using bounded_w by fastforce
    hence "state_rank x t = None"
      using pull_up_configuration_state_rank by auto
  }
  with state_rank_range show ?thesis
    by blast
qed

subsection \<open>Step Function\<close>

fun pre_oldest_tokens :: "'b \<Rightarrow> nat \<Rightarrow> nat set"
where
  "pre_oldest_tokens q n = {x. \<exists>q'. oldest_token q' n = Some x \<and> q = \<delta> q' (w n)} \<union> (if q = q\<^sub>0 then {Suc n} else {})"

lemma pre_oldest_configuration_range:
  "pre_oldest_tokens q n \<subseteq> {0..Suc n}"
proof -
  have "{x. \<exists>q'. oldest_token q' n = Some x \<and> q = \<delta> q' (w n)} \<subseteq> {0..n}"
    (is "?lhs \<subseteq> ?rhs")
  proof
    fix x
    assume "x \<in> ?lhs"
    then obtain q' where "oldest_token q' n = Some x"
      by blast
    thus "x \<in> ?rhs"
      unfolding atLeastAtMost_iff using oldest_token_bounded[of q' n x] by blast
  qed
  thus ?thesis
    by (cases "q = q\<^sub>0") fastforce+
qed

lemma pre_oldest_configuration_finite:
  "finite (pre_oldest_tokens q n)"
  using pre_oldest_configuration_range finite_atLeastAtMost by (rule finite_subset)

lemmas pre_oldest_configuration_Min_in = Min_in[OF pre_oldest_configuration_finite]

lemma pre_oldest_configuration_obtain:
  assumes "x \<in> pre_oldest_tokens q n - {Suc n}"
  obtains q' where "oldest_token q' n = Some x" and "q = \<delta> q' (w n)"
  using assms by (cases "q = q\<^sub>0", auto)

lemma pre_oldest_configuration_element:
  assumes "oldest_token q' n = Some ot"
  assumes "q = \<delta> q' (w n)"
  shows "ot \<in> pre_oldest_tokens q n"
proof
  show "ot \<in> {ot. \<exists>q'. oldest_token q' n = Some ot \<and> q = \<delta> q' (w n)}"
    (is "_ \<in> ?A")
    using assms by blast
  show "?A \<subseteq> pre_oldest_tokens q n"
    by simp
qed

lemma pre_oldest_configuration_initial_state:
  "Suc n \<in> pre_oldest_tokens q n \<Longrightarrow> q = q\<^sub>0"
  using oldest_token_bounded[of _ n "Suc n"]
  by (cases "q = q\<^sub>0") auto

lemma pre_oldest_configuration_initial_state_2:
  "q = q\<^sub>0 \<Longrightarrow> Suc n \<in> pre_oldest_tokens q n"
  by fastforce

lemma pre_oldest_configuration_tokens:
  "pre_oldest_tokens q n \<noteq> {} \<longleftrightarrow> configuration q (Suc n) \<noteq> {}"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain ot where ot_def: "ot \<in> pre_oldest_tokens q n"
    by blast
  thus ?rhs
  proof (cases "ot = Suc n")
    case True
      thus ?thesis
    using pre_oldest_configuration_initial_state configuration_non_empty[of "Suc n" "Suc n"] \<open>ot \<in> pre_oldest_tokens q n\<close> unfolding token_run_intial_state  by blast
  next
    case False
      then obtain q' where "oldest_token q' n = Some ot" and "q = \<delta> q' (w n)"
        using ot_def pre_oldest_configuration_obtain by blast
      moreover
      hence "configuration q' n \<noteq> {}"
        by (metis oldest_token.simps option.distinct(2))
      ultimately
      show ?rhs
        by (elim configuration_step_non_empty)
  qed
next
  assume ?rhs
  then obtain token where "token \<in> configuration q (Suc n)" and "token \<le> Suc n" and "token_run token (Suc n) = q"
    by auto
  moreover
  {
    assume "token \<le> n"
    then obtain q' where "token_run token n = q'" and "q = \<delta> q' (w n)"
      using \<open>token_run token (Suc n) = q\<close> unfolding token_run.simps Suc_diff_le[OF \<open>token \<le> n\<close>] by fastforce
    then obtain ot where "oldest_token q' n = Some ot"
      using oldest_token_always_def by blast
    with \<open>q = \<delta> q' (w n)\<close> have ?lhs
      using pre_oldest_configuration_element by blast
  }
  ultimately
  show ?lhs
    using pre_oldest_configuration_initial_state_2 by fastforce
qed

lemma oldest_token_rec:
  "oldest_token q (Suc n) = (if pre_oldest_tokens q n \<noteq> {} then Some (Min (pre_oldest_tokens q n)) else None)"
proof (cases "oldest_token q (Suc n)")
  case (Some ot)
    moreover
    hence "ot \<in> configuration q (Suc n)"
      by (rule push_down_oldest_token_configuration)
    hence "configuration q (Suc n) \<noteq> {}"
      by blast
    hence "pre_oldest_tokens q n \<noteq> {}"
      unfolding pre_oldest_configuration_tokens .
    let ?ot = "Min (pre_oldest_tokens q n)"
    {
      {
        {
          assume "ot < Suc n"
          hence "ot \<noteq> Suc n"
            by blast
          then obtain q' where "ot \<in> configuration q' n" and "q = \<delta> q' (w n)"
            using configuration_rev_step' \<open>ot \<in> configuration q (Suc n)\<close> by metis
          {
            fix token
            assume "token \<in> configuration q' n"
            hence "token \<in> configuration q (Suc n)"
              using \<open>q = \<delta> q' (w n)\<close> by (rule configuration_step)
            hence "ot \<le> token"
              using Some by (metis Min.coboundedI \<open>configuration q (Suc n) \<noteq> {}\<close> configuration_finite oldest_token.simps option.inject)
          }
          hence "Min (configuration q' n) = ot"
            by (metis Min_eqI \<open>ot \<in> configuration q' n\<close> configuration_finite)
          hence "oldest_token q' n = Some ot"
            using \<open>ot \<in> configuration q' n\<close> unfolding oldest_token.simps by auto
          hence "ot \<in> pre_oldest_tokens q n"
            using \<open>q = \<delta> q' (w n)\<close> by (rule pre_oldest_configuration_element)
        }
        moreover
        {
          assume "ot = Suc n"
          moreover
          hence "q = q\<^sub>0"
            using Some by (metis push_down_oldest_token_token_run token_run_intial_state)
          ultimately
          have "ot \<in> pre_oldest_tokens q n"
            by simp
        }
        ultimately
        have "ot \<in> pre_oldest_tokens q n"
          using Some[THEN oldest_token_bounded] by linarith
      }
      moreover
      {
        fix ot' q'
        assume "oldest_token q' n = Some ot'" and "q = \<delta> q' (w n)"
        moreover
        hence "ot' \<in> configuration q (Suc n)"
          using push_down_oldest_token_configuration configuration_step by blast
        hence "ot \<le> ot'"
          using Some by (metis Min.coboundedI \<open>configuration q (Suc n) \<noteq> {}\<close> configuration_finite oldest_token.simps option.inject)
      }
      hence "\<And>y. y \<in> pre_oldest_tokens q n - {Suc n} \<Longrightarrow> ot \<le> y"
        using pre_oldest_configuration_obtain by metis
      hence "\<And>y. y \<in> pre_oldest_tokens q n \<Longrightarrow> ot \<le> y"
        using Some[THEN oldest_token_bounded] by force
      ultimately
      have "?ot = ot"
        using Min_eqI[OF pre_oldest_configuration_finite, of q n ot] by fast
    }
    ultimately
    show ?thesis
      unfolding pre_oldest_configuration_tokens oldest_token.simps
      by (metis \<open>configuration q (Suc n) \<noteq> {}\<close>)
qed (unfold pre_oldest_configuration_tokens oldest_token.simps, metis option.distinct(2))

lemma pre_ranks_range:
  "pre_ranks (\<lambda>q. state_rank q n) \<nu> q  \<subseteq> {0..max_rank}"
proof -
  have "{i | q' i. state_rank q' n = Some i \<and> q = \<delta> q' \<nu>} \<subseteq> {0..max_rank}"
    using state_rank_upper_bound by fastforce
  thus ?thesis
    by auto
qed

lemma pre_ranks_finite:
  "finite (pre_ranks (\<lambda>q. state_rank q n) \<nu> q)"
  using pre_ranks_range finite_atLeastAtMost by (rule finite_subset)

lemmas pre_ranks_Min_in = Min_in[OF pre_ranks_finite]

lemma pre_ranks_state_obtain:
  assumes "r\<^sub>q \<in> pre_ranks r \<nu> q - {max_rank}"
  obtains q' where "r q' = Some r\<^sub>q" and "q = \<delta> q' \<nu>"
  using assms by (cases "q = q\<^sub>0", auto)

lemma pre_ranks_element:
  assumes "state_rank q' n = Some r"
  assumes "q = \<delta> q' (w n)"
  shows "r \<in> pre_ranks (\<lambda>q. state_rank q n) (w n) q"
proof
  show "r \<in> {i. \<exists>q'. (\<lambda>q. state_rank q n) q' = Some i \<and> q = \<delta> q' (w n)}"
    (is "_ \<in> ?A")
    using assms by blast
  show "?A \<subseteq> pre_ranks (\<lambda>q. state_rank q n) (w n) q"
    by simp
qed

lemma pre_ranks_initial_state:
  "max_rank \<in> pre_ranks (\<lambda>q. state_rank q n) \<nu> q \<Longrightarrow> q = q\<^sub>0"
  using state_rank_upper_bound by (cases "q = q\<^sub>0") auto

lemma pre_ranks_initial_state_2:
  "q = q\<^sub>0 \<Longrightarrow> max_rank \<in> pre_ranks r \<nu> q"
  by fastforce

lemma pre_ranks_tokens:
  assumes "\<not>sink q"
  shows "pre_ranks (\<lambda>q. state_rank q n) (w n) q \<noteq> {} \<longleftrightarrow> configuration q (Suc n) \<noteq> {}"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  thus ?rhs
  proof (cases "q \<noteq> q\<^sub>0")
    case True
      hence "{i. \<exists>q'. state_rank q' n = Some i \<and> q = \<delta> q' (w n)} \<noteq> {}"
        using \<open>?lhs\<close> by simp
      then obtain q' where "state_rank q' n \<noteq> None" and "q = \<delta> q' (w n)"
        by blast
      moreover
      hence "configuration q' n \<noteq> {}"
        unfolding state_rank.simps by meson
      ultimately
      show ?rhs
        by (elim configuration_step_non_empty)
  qed auto
next
  assume ?rhs
  then obtain token where "token \<in> configuration q (Suc n)" and "token \<le> Suc n" and "token_run token (Suc n) = q"
    by auto
  moreover
  {
    assume "token \<le> n"
    then obtain q' where "token_run token n = q'" and "q = \<delta> q' (w n)"
      using \<open>token_run token (Suc n) = q\<close> unfolding token_run.simps Suc_diff_le[OF \<open>token \<le> n\<close>] by fastforce
    hence "\<not>sink q'"
      using \<open>\<not>sink q\<close> sink_rev_step bounded_w by blast
    then obtain r where "state_rank q' n = Some r"
      using \<open>\<not>sink q\<close> configuration_non_empty[OF \<open>token \<le> n\<close>] unfolding \<open>token_run token n = q'\<close> by simp
    with \<open>q = \<delta> q' (w n)\<close> have ?lhs
      using pre_ranks_element by blast
  }
  ultimately
  show ?lhs
    by fastforce
qed

lemma pre_ranks_pre_oldest_token_Min_state_special:
  assumes "\<not>sink q"
  assumes "configuration q (Suc n) \<noteq> {}"
  shows "Min (pre_ranks (\<lambda>q. state_rank q n) (w n) q) = max_rank \<longleftrightarrow> Min (pre_oldest_tokens q n) = Suc n"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  from assms have "pre_oldest_tokens q n \<noteq> {}"
    and "pre_ranks  (\<lambda>q. state_rank q n) (w n) q \<noteq> {}"
    using pre_ranks_tokens pre_oldest_configuration_tokens by simp_all

  {
    assume ?lhs
    have "q = q\<^sub>0"
      apply (rule ccontr)
      using state_rank_upper_bound pre_ranks_Min_in[OF \<open>pre_ranks (\<lambda>q. state_rank q n) (w n) q \<noteq> {}\<close>] \<open>?lhs\<close>
      by auto
    moreover
    {
      fix q'
      assume "q = \<delta> q' (w n)"
      hence "\<not>sink q'"
        using \<open>\<not>sink q\<close> bounded_w unfolding sink_def
        using calculation by blast
      {
        fix i
        assume "state_rank q' n = Some i"
        hence "False"
          using \<open>q = \<delta> q' (w n)\<close>
        using Min.coboundedI[OF pre_ranks_finite, of _ n "(w n)" q]
        unfolding \<open>?lhs\<close> using state_rank_upper_bound[of q' n] by fastforce
      }
      hence "state_rank q' n = None"
        by fastforce
      hence "oldest_token q' n = None"
        using \<open>\<not>sink q'\<close> by (metis state_rank_None)
    }
    hence "{ot. \<exists>q'. oldest_token q' n = Some ot \<and> q = \<delta> q' (w n)} = {}"
      by fastforce
    ultimately
    show "?rhs"
      by auto
  }

  {
    assume ?rhs
    {
      fix q'
      assume "q = \<delta> q' (w n)"
      have "state_rank q' n = None"
      proof (cases "oldest_token q' n")
        case (Some t)
          hence "t \<le> n"
            using oldest_token_bounded[of q' n] by blast
          moreover
          have "Suc n \<le> t"
            using \<open>q = \<delta> q' (w n)\<close>
            using Min.coboundedI[OF pre_oldest_configuration_finite, of _ q n]
            unfolding \<open>?rhs\<close> using \<open>oldest_token q' n = Some t\<close> by auto
          ultimately
          have "False"
            by linarith
          thus ?thesis
            ..
      qed (unfold state_rank_eq_rank, auto)
    }
    hence X: "{i. \<exists>q'.  (\<lambda>q. state_rank q n) q' = Some i \<and> q = \<delta> q' (w n)} = {}"
      by fastforce

    have "q = q\<^sub>0"
      apply (rule ccontr)
      using \<open>pre_ranks (\<lambda>q. state_rank q n) (w n) q \<noteq> {}\<close>
      unfolding pre_ranks.simps X by simp
    hence "pre_ranks (\<lambda>q. state_rank q n) (w n) q = {max_rank}"
      unfolding pre_ranks.simps X by force
    thus ?lhs
      by fastforce
  }
qed

lemma pre_ranks_pre_oldest_token_Min_state:
  assumes "\<not>sink q"
  assumes "q = \<delta> q' (w n)"
  assumes "configuration q (Suc n) \<noteq> {}"
  defines "min_r \<equiv> Min (pre_ranks (\<lambda>q. state_rank q n) (w n) q)"
  defines "min_ot \<equiv> Min (pre_oldest_tokens q n)"
  shows "state_rank q' n = Some min_r \<longleftrightarrow> oldest_token q' n = Some min_ot"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  from assms have "pre_oldest_tokens q n \<noteq> {}" and "\<not>sink q'"
    and "pre_ranks (\<lambda>q. state_rank q n) (w n) q \<noteq> {}"
    using pre_ranks_tokens pre_oldest_configuration_tokens bounded_w unfolding sink_def
    by (simp_all, metis rangeI subset_iff)

  {
    assume ?lhs
    thus ?rhs
    proof (cases min_r max_rank rule: linorder_cases)
      case less
        then obtain ot where "oldest_token q' n = Some ot"
           by (metis push_down_state_rank_oldest_token \<open>?lhs\<close>)
        moreover
        {
          {
            fix q'' ot''
            assume "q = \<delta> q'' (w n)"
            assume "oldest_token q'' n = Some ot''"
            moreover
            have "\<not>sink q''"
              using \<open>q = \<delta> q'' (w n)\<close> assms unfolding sink_def
              by (metis rangeI subset_eq bounded_w)
            then obtain r'' where "state_rank q'' n = Some r''"
              using \<open>oldest_token q'' n = Some ot''\<close> by (metis state_rank_Some)
            moreover
            hence "r'' \<in> pre_ranks (\<lambda>q. state_rank q n) (w n) q" (* Move to special lemma *)
              using \<open>q = \<delta> q'' (w n)\<close> unfolding pre_ranks.simps by blast
            then have "min_r \<le> r''"
              unfolding min_r_def by (metis Min.coboundedI pre_ranks_finite)
            ultimately
            have "ot \<le> ot''"
              using state_rank_oldest_token_le[OF \<open>?lhs\<close> _ \<open>oldest_token q' n = Some ot\<close>] by blast
          }
          hence "\<And>x. x \<in> {ot. \<exists>q'. oldest_token q' n = Some ot \<and> q = \<delta> q' (w n)} \<Longrightarrow> ot \<le> x"
            by blast
          moreover
          have "ot \<le> Suc n"
            using oldest_token_bounded[OF \<open>oldest_token q' n = Some ot\<close>] by simp
          ultimately
          have "\<And>x. x \<in> pre_oldest_tokens q n \<Longrightarrow> ot \<le> x"
            unfolding pre_oldest_tokens.simps apply (cases "q\<^sub>0 = q") apply auto done
          hence "ot \<le> min_ot"
            unfolding min_ot_def
            unfolding Min_ge_iff[OF pre_oldest_configuration_finite \<open>pre_oldest_tokens q n \<noteq> {}\<close>, of ot]
             by simp
        }
        moreover
        have "ot \<ge> min_ot"
          using Min.coboundedI[OF pre_oldest_configuration_finite] pre_oldest_configuration_element
          unfolding min_ot_def by (metis assms(2) calculation(1))
        ultimately
        show ?thesis
          by simp
    qed (insert not_less, blast intro: state_rank_upper_bound less_imp_le_nat)+
  }

  {
    assume ?rhs
    thus ?lhs
    proof (cases min_ot "Suc n" rule: linorder_cases)
      case less
        then obtain r where "state_rank q' n = Some r"
          using \<open>?rhs\<close> \<open>\<not>sink q'\<close> by (metis state_rank_Some)
        moreover
        {
          {
            fix r''
            assume "r'' \<in> pre_ranks (\<lambda>q. state_rank q n) (w n) q - {max_rank}"
            then obtain q'' where "state_rank q'' n = Some r''"
              and "q = \<delta> q'' (w n)"
              using pre_ranks_state_obtain by blast
            moreover
            then obtain ot'' where "oldest_token q'' n = Some ot''"
               using push_down_state_rank_oldest_token by fastforce
            moreover
            hence "min_ot \<le> ot''"
              using \<open>q = \<delta> q'' (w n)\<close> pre_oldest_configuration_element Min.coboundedI pre_oldest_configuration_finite
              unfolding min_ot_def by metis
            ultimately
            have "r \<le> r''"
              using state_rank_oldest_token_le[OF \<open>state_rank q' n = Some r\<close> _ \<open>?rhs\<close>] by blast
          }
          moreover
          have "r \<le> max_rank"
            using state_rank_upper_bound[OF \<open>state_rank q' n = Some r\<close>] by linarith
          ultimately
          have "\<And>x. x \<in>  pre_ranks (\<lambda>q. state_rank q n) (w n) q \<Longrightarrow> r \<le> x"
            unfolding pre_ranks.simps apply (cases "q\<^sub>0 = q") apply auto done
          hence "r \<le> min_r"
            unfolding min_r_def Min_ge_iff[OF pre_ranks_finite \<open>pre_ranks (\<lambda>q. state_rank q n) (w n) q \<noteq> {}\<close>]
            by simp
        }
        moreover
        have "r \<ge> min_r"
          using Min.coboundedI[OF pre_ranks_finite] pre_ranks_element
          unfolding min_r_def by (metis assms(2) calculation(1))
        ultimately
        show ?thesis
          by simp
    qed (insert not_less, blast intro: oldest_token_bounded Suc_lessD)+
  }
qed

lemma Min_pre_ranks_pre_oldest_tokens:
  fixes n
  defines "r \<equiv> (\<lambda>q. state_rank q n)"
  assumes "configuration p (Suc n) \<noteq> {}"
      and "configuration q (Suc n) \<noteq> {}"
  assumes "\<not>sink q"
      and "\<not>sink p"
  shows "Min (pre_ranks r (w n) p) < Min (pre_ranks r (w n) q) \<longleftrightarrow> Min (pre_oldest_tokens p n) < Min (pre_oldest_tokens q n)"
  (is "?lhs \<longleftrightarrow> ?rhs")
proof
  have pre_ranks_Min: "\<And>x \<nu>. (x < Min (pre_ranks r (w n) q)) = (\<forall>a \<in> pre_ranks r (w n) q. x < a)"
    using assms pre_ranks_finite Min.bounded_iff pre_ranks_tokens by simp
  have pre_oldest_configuration_Min: "\<And>x. (x < Min (pre_oldest_tokens q n)) = (\<forall>a\<in>pre_oldest_tokens q n. x < a)"
    using assms pre_oldest_configuration_finite Min.bounded_iff pre_oldest_configuration_tokens by simp
  have "\<And>x. w x \<in> \<Sigma>"
    using bounded_w by auto

  {
    let ?min_i = "Min (pre_ranks r (w n) p)"
    let ?min_j = "Min (pre_ranks r (w n) q)"

    assume ?lhs

    have "?min_i \<in> pre_ranks r (w n) p" and "?min_j \<in> pre_ranks r (w n) q"
      using Min_in[OF pre_ranks_finite] assms pre_ranks_tokens by presburger+
    hence "?min_i \<le> max_rank" and "?min_j \<le> max_rank"
      using pre_ranks_range atLeastAtMost_iff unfolding r_def by blast+
    with \<open>?lhs\<close> have "?min_i \<noteq> max_rank"
      by linarith
    then obtain p' i' where "i' = ?min_i" and "r p' = Some i'" and "p = \<delta> p' (w n)"
      using \<open>?min_i \<in> pre_ranks r (w n) p\<close> apply (cases "p = q\<^sub>0") apply auto[1] by fastforce
    then obtain ot' where "oldest_token p' n = Some ot'"
      unfolding assms by (metis push_down_state_rank_oldest_token)
    have "state_rank p' n = Some ?min_i"
      using \<open>i' = ?min_i\<close> \<open>r p' = Some i'\<close> unfolding assms by simp
    hence "ot' = Min (pre_oldest_tokens p n)"
      using pre_ranks_pre_oldest_token_Min_state[OF \<open>\<not>sink p\<close> \<open>p = \<delta> p' (w n)\<close> \<open>configuration p (Suc n) \<noteq> {}\<close>] \<open>oldest_token p' n = Some ot'\<close>
      unfolding r_def by (metis option.inject)
    moreover
    have "ot' < Suc n"
    proof (cases ot' "Suc n" rule: linorder_cases)
      case equal
        hence "?min_i = max_rank"
          using pre_ranks_pre_oldest_token_Min_state_special[of p n, OF \<open>\<not>sink p\<close> \<open>configuration p (Suc n) \<noteq> {}\<close>] assms
          unfolding \<open>ot' = Min (pre_oldest_tokens p n)\<close> by simp
        thus ?thesis
          using \<open>?min_i \<noteq> max_rank\<close> by simp
    next
      case greater
        moreover
        have "ot' \<in> {0..Suc n}"
          using \<open>oldest_token p' n = Some ot'\<close>[THEN oldest_token_bounded] by fastforce
        ultimately
        show ?thesis
          by simp
    qed simp
    moreover
    {
      fix ot\<^sub>q
      assume "ot\<^sub>q \<in> pre_oldest_tokens q n - {Suc n}"
      then obtain q' where "oldest_token q' n = Some ot\<^sub>q" and "q = \<delta> q' (w n)"
        using pre_oldest_configuration_obtain by blast
      moreover
      hence "\<not>sink q'"
        using \<open>\<not>sink q\<close> \<open>\<And>x. w x \<in> \<Sigma>\<close> unfolding sink_def by auto
      then obtain r\<^sub>q where "state_rank q' n = Some r\<^sub>q"
        unfolding assms state_rank.simps using \<open>oldest_token q' n = Some ot\<^sub>q\<close>
        by (metis oldest_token.simps option.distinct(2))
      moreover
      hence "r\<^sub>q \<in> pre_ranks r (w n) q"
        using \<open>q = \<delta> q' (w n)\<close>
        unfolding pre_ranks.simps assms by blast
      hence "?min_j \<le> r\<^sub>q"
        using Min.coboundedI[OF pre_ranks_finite] unfolding assms by blast
      hence "?min_i < r\<^sub>q"
        using \<open>?lhs\<close> by linarith
      hence "ot' < ot\<^sub>q"
        using state_rank_oldest_token[OF \<open>state_rank p' n = Some ?min_i\<close> \<open>state_rank q' n = Some r\<^sub>q\<close> \<open>oldest_token p' n = Some ot'\<close> \<open>oldest_token q' n = Some ot\<^sub>q\<close>]
        unfolding assms by simp
    }
    ultimately
    show ?rhs
      using pre_oldest_configuration_Min by blast
  }

  {
    define ot_p where "ot_p = Min (pre_oldest_tokens p n)"
    define ot_q where "ot_q = Min (pre_oldest_tokens q n)"
    assume ?rhs
    hence "ot_p < ot_q"
      unfolding ot_p_def ot_q_def .

    have "oldest_token p (Suc n) = Some ot_p" and "oldest_token q (Suc n) = Some ot_q"
      unfolding ot_p_def ot_q_def oldest_token_rec pre_oldest_configuration_tokens by (metis assms)+

   (* Min oldest \<longleftrightarrow> Min rank *)
    define min_r\<^sub>p where "min_r\<^sub>p = Min (pre_ranks r (w n) p)"
    hence "min_r\<^sub>p \<in> pre_ranks r (w n) p"
      using pre_ranks_Min_in assms pre_ranks_tokens by simp
    hence *: "min_r\<^sub>p < max_rank"
    proof (cases min_r\<^sub>p max_rank rule: linorder_cases)
      case equal
        hence "ot_p = Suc n"
          using pre_ranks_pre_oldest_token_Min_state_special[of p n, OF _ \<open>configuration p (Suc n) \<noteq> {}\<close>] assms
          unfolding ot_p_def min_r\<^sub>p_def by simp
        moreover
        have "Min (pre_oldest_tokens q n) \<in> pre_oldest_tokens q n"
          using Min_in[OF pre_oldest_configuration_finite ] assms pre_oldest_configuration_tokens by presburger
        hence "ot_q \<in> {0..Suc n}"
          using pre_oldest_configuration_range[of q n]
          unfolding ot_q_def by blast
        hence "ot_q \<le> Suc n"
          by simp
        ultimately
        show ?thesis
          using \<open>ot_p < ot_q\<close> by simp
    next
      case greater
        moreover
        have "min_r\<^sub>p \<in> {0..max_rank}"
          using pre_ranks_range \<open>min_r\<^sub>p \<in> pre_ranks r (w n) p\<close>
          unfolding r_def ..
        ultimately
        show ?thesis
          by simp
    qed simp
    moreover
    from * have "min_r\<^sub>p \<in> pre_ranks r (w n) p - {max_rank}"
      using \<open>min_r\<^sub>p \<in> pre_ranks r (w n) p\<close> by simp
    then obtain p' where "r p' = Some min_r\<^sub>p" and "p = \<delta> p' (w n)"
      using pre_ranks_state_obtain by blast
    hence "oldest_token p' n = Some ot_p"
      using pre_ranks_pre_oldest_token_Min_state[OF \<open>\<not>sink p\<close> \<open>p = \<delta> p' (w n)\<close> \<open>configuration p (Suc n) \<noteq> {}\<close>]
      unfolding r_def[symmetric] min_r\<^sub>p_def[symmetric] ot_p_def[symmetric] by (metis r_def)
    {
      fix r\<^sub>q
      assume "r\<^sub>q \<in> pre_ranks r (w n) q - {max_rank}"
      then obtain q' where q': "r q' = Some r\<^sub>q" "q = \<delta> q' (w n)"
        using pre_ranks_state_obtain by blast
      moreover
      from q' obtain ot_q' where ot_q': "oldest_token q' n = Some ot_q'"
        unfolding assms by (metis push_down_state_rank_oldest_token)
      moreover
      from ot_q' have "ot_q' \<in> pre_oldest_tokens q n"
        using \<open>q = \<delta> q' (w n)\<close>
        unfolding pre_oldest_tokens.simps by blast
      hence "ot_q \<le> ot_q'"
        unfolding ot_q_def
        by (rule Min.coboundedI[OF pre_oldest_configuration_finite])
      hence "ot_p < ot_q'"
        using \<open>ot_p < ot_q\<close> by linarith
      ultimately
      have "min_r\<^sub>p < r\<^sub>q"
        using state_rank_oldest_token \<open>r p' = Some min_r\<^sub>p\<close> \<open>oldest_token p' n = Some ot_p\<close>
        unfolding assms by blast
    }
    ultimately
    show ?lhs
      using pre_ranks_Min unfolding min_r\<^sub>p_def by blast
  }
qed

subsubsection \<open>Definition of initial and step\<close>

lemma state_rank_initial:
  "state_rank q 0 = initial q"
  using state_rank_initial_state by force

lemma state_rank_step:
  "state_rank q (Suc n) = step (\<lambda>q. state_rank q n) (w n) q"
  (is "?lhs = ?rhs")
proof (cases "sink q")
  case False
    {
      assume "configuration q (Suc n) = {}"
      hence ?thesis
        using False pull_up_configuration_state_rank pre_ranks_tokens
        unfolding step.simps by presburger
    }
    moreover
    {
      assume "configuration q (Suc n) \<noteq> {}"
      hence "?lhs = Some (card (senior_states q (Suc n)))"
        using False unfolding state_rank.simps by presburger
      also
      have "\<dots> = ?rhs"
      proof -
        let ?r = "\<lambda>q. state_rank q n"
        have "{q'. \<not>sink q' \<and> pre_ranks ?r (w n) q' \<noteq> {} \<and> Min (pre_ranks ?r (w n) q') < Min (pre_ranks ?r (w n) q)} = senior_states q (Suc n)"
          (is "?S = ?S'")
        proof (rule set_eqI)
          fix q'
          have "q' \<in> ?S \<longleftrightarrow> \<not>sink q' \<and> configuration q' (Suc n) \<noteq> {} \<and> Min (pre_ranks  ?r (w n) q') < Min (pre_ranks ?r (w n) q)"
            using pre_ranks_tokens by blast
          also
          have "\<dots> \<longleftrightarrow> \<not>sink q' \<and> configuration q' (Suc n) \<noteq> {} \<and> Min (pre_oldest_tokens q' n) < Min (pre_oldest_tokens q n)"
            by (metis \<open>configuration q (Suc n) \<noteq> {}\<close> \<open>\<not>sink q\<close> Min_pre_ranks_pre_oldest_tokens)
          also
          have "\<dots> \<longleftrightarrow> \<not>sink q' \<and> (\<exists>x y. oldest_token q' (Suc n) = Some y \<and> oldest_token q (Suc n) = Some x \<and> y < x)"
            unfolding oldest_token_rec by (metis pre_oldest_configuration_tokens \<open>configuration q (Suc n) \<noteq> {}\<close> option.distinct(2) option.sel)
          finally
          show "q' \<in> ?S \<longleftrightarrow> q' \<in> ?S'"
            unfolding senior_states.simps by blast
        qed
        thus ?thesis
          using \<open>\<not>sink q\<close> \<open>configuration q (Suc n) \<noteq> {}\<close>
          unfolding step.simps pre_ranks_tokens[OF \<open>\<not>sink q\<close>] by presburger
      qed
      finally
      have ?thesis .
    }
    ultimately
    show ?thesis
      by blast
qed auto

lemma state_rank_step_foldl:
  "(\<lambda>q. state_rank q n) = foldl step initial (map w [0..<n])"
  by (induction n) (unfold state_rank_initial state_rank_step, simp_all)

end

end
