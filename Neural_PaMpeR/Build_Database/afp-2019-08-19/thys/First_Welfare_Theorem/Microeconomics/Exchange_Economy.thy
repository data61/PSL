(* License: LGPL *)
(*
Author: Julian Parsert <julian.parsert@gmail.com>
Author: Cezary Kaliszyk
*)


theory Exchange_Economy
  imports
    "HOL-Analysis.Analysis"
    "../Preferences"
    "../Utility_Functions"
    "../Argmax"
    Consumers
    Common
begin

section \<open> Exchange Economy \<close>

text \<open> Define the exchange economy model \<close>

locale exchange_economy =
  fixes consumption_set :: "('a::ordered_euclidean_space) set"
  fixes agents :: "'i set"
  fixes \<E> :: "'i \<Rightarrow> 'a"
  fixes Pref :: "'i \<Rightarrow> 'a relation"
  fixes U :: "'i \<Rightarrow> 'a \<Rightarrow> real"
  assumes cons_set_props: "pre_arrow_debreu_consumption_set consumption_set"
  assumes agent_props: "i \<in> agents \<Longrightarrow> eucl_ordinal_utility consumption_set (Pref i) (U i)"
  assumes finite_agents: "finite agents" and "agents \<noteq> {}"

sublocale exchange_economy \<subseteq> pareto_ordering agents U
  .                                 

context exchange_economy
begin

context 
begin

notation U ("U[_]")
notation Pref ("Pr[_]")
notation \<E> ("\<E>[_]")

lemma base_pref_is_ord_eucl_rpr: "i \<in> agents \<Longrightarrow> rational_preference consumption_set Pr[i]"
  by (meson exchange_economy.agent_props exchange_economy_axioms
      ord_eucl_utility_imp_rpr real_vector_rpr.have_rpr)

private abbreviation calculate_value 
  where
    "calculate_value P x \<equiv> P \<bullet> x"

subsection \<open> Feasibility \<close>

definition feasible_allocation
  where
    "feasible_allocation A E \<longleftrightarrow>
      (\<Sum>i\<in>agents. A i) \<le> (\<Sum>i\<in>agents. E i)"


subsection \<open> Pareto optimality \<close>

definition pareto_optimal_endow
  where
    "pareto_optimal_endow X E \<longleftrightarrow>
              (feasible_allocation X E \<and>
              (\<nexists>X'. feasible_allocation X' E \<and> X' \<succ>Pareto X))"


subsection \<open>Competitive Equilibrium in Exchange Economy \<close>

text \<open> Competitive Equilibirum or Walrasian Equilibrium definition. \<close>

definition comp_equilib_endow
  where
    "comp_equilib_endow P X E \<equiv>
      feasible_allocation X E \<and>
      (\<forall>i \<in> agents. X i \<in> arg_max_set U[i]
        (budget_constraint (calculate_value P) consumption_set (P \<bullet> E i)))"


subsection \<open> Lemmas for final result \<close>

lemma utility_function_def[iff]:
  assumes "i \<in> agents"
  shows "U[i] x \<ge> U[i] y \<longleftrightarrow> x \<succeq>[Pr[i]] y"
proof
  have "ordinal_utility consumption_set (Pref i) (U[i])"
    using agent_props assms eucl_ordinal_utility_def by auto
  then show " U[i] y \<le>  U[i] x \<Longrightarrow> x \<succeq>[Pref i] y"
    by (meson UNIV_I cons_set_props ordinal_utility.util_def_conf
        pre_arrow_debreu_consumption_set_def)
next
  show "x \<succeq>[Pref i] y \<Longrightarrow> U[i] y \<le> U[i] x"
    by (meson agent_props assms ordinal_utility_def eucl_ordinal_utility_def)
qed

lemma budget_constraint_is_feasible:
  assumes "i \<in> agents"
  assumes "X \<in> (budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i]))"
  shows "P \<bullet> X \<le> P \<bullet> \<E>[i]"
  using budget_constraint_def assms
  by (simp add: budget_constraint_def)

lemma arg_max_set_therefore_no_better :
  assumes "i \<in> agents"
  assumes "x \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i]))"
  shows "U[i] y > U[i] x \<longrightarrow> y \<notin> budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i])"
  by (meson no_better_in_s assms)

text \<open> Since we need no restriction on the consumption set for the First Welfare Theorem \<close>

lemma consumption_set_member: "\<forall>x. x \<in> consumption_set"
proof -
  have "\<And>(x::'a). x \<in> consumption_set"
    using cons_set_props pre_arrow_debreu_consumption_set_def
    by (simp add: pre_arrow_debreu_consumption_set_def)
  thus ?thesis
    by blast
qed

text \<open> Under the assumption of Local non-satiation, agents will utilise their entire budget. \<close>

lemma argmax_entire_budget :
  assumes "i \<in> agents"
  assumes "local_nonsatiation consumption_set Pr[i]"
  assumes "X \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i]))"
  shows "P \<bullet> X = P \<bullet> \<E>[i]"
proof -
  have leq : "(P \<bullet> X) \<le> (P \<bullet> \<E>[i])"
  proof-
    have "X \<in> budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i])"
      using argmax_sol_in_s[of X "U[i]" "budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i])"]
        assms by auto
    thus ?thesis
      using assms(1) budget_constraint_is_feasible by blast
  qed
  have not_less: "\<not>(P \<bullet> X < P \<bullet> \<E>[i])"
  proof
    assume cpos: "(P \<bullet> X) < (P \<bullet> \<E>[i])"
    define lesS where "lesS = {x. P \<bullet> x < P \<bullet> \<E>[i]}"
    obtain e where
      e: "0 < e" "ball X e \<subseteq> lesS"
      by (metis cpos lesS_def mem_Collect_eq
          open_contains_ball_eq open_halfspace_lt)
    obtain Y where
      Y: "Y \<succ>[Pref i] X " "Y \<in> ball X e"
      using e consumption_set_member assms by blast
    have "Y \<in> consumption_set"
      using consumption_set_member by blast
    hence "Y \<in> budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i])"
      using budget_constraint_def e lesS_def
        less_eq_real_def Y  by fastforce
    thus False
      by (meson assms Y all_leq utility_function_def)
  qed
  show ?thesis
    using leq not_less by auto
qed

text \<open> All bundles that would be strictly preferred to any argmax result, are more expensive. \<close>

lemma pref_more_expensive:
  assumes "i \<in> agents"
  assumes "x \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i]))"
  assumes "U[i] y > U[i] x"
  shows "y \<bullet> P > P \<bullet> \<E>[i]"
proof (rule ccontr)
  assume cpos :  "\<not>(y \<bullet> P > P \<bullet> \<E>[i])"
  then have xp_leq : "y \<bullet> P \<le> P \<bullet>  \<E>[i]"
    by auto
  hence "x \<in> budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i])"
    using argmax_sol_in_s[of x " U[i]" "budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i])"]
      assms by auto
  hence xp_in: "y \<in> budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i])"
  proof -
    have "P \<bullet> y \<le> P \<bullet> \<E>[i]"
      by (metis xp_leq inner_commute)
    then show ?thesis
      using consumption_set_member by (simp add: budget_constraint_def)
  qed
  hence "y \<succ>[Pref i] x"
    using arg_max_set_therefore_no_better assms by blast
  hence "y \<succ>[Pref i] x \<and> y \<in> budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i])"
    using xp_in by blast
  hence "x \<notin> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i]))"
    by (meson assms exchange_economy.arg_max_set_therefore_no_better
        exchange_economy_axioms)
  then show False
    using assms(2) by auto
qed

text \<open> Greater or equal utility implies greater or equal price. \<close>

lemma same_util_is_equal_or_more_expensive:
  assumes "i \<in> agents"
  assumes "local_nonsatiation consumption_set Pr[i]"
  assumes "x \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i]))"
  assumes "U[i] y \<ge> U[i] x"
  shows "y \<bullet> P \<ge> P \<bullet> \<E>[i]"
proof-
  have not_in: "y \<notin> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i]))
    \<Longrightarrow> y \<bullet> P > P \<bullet> \<E>[i]"
  proof-
    assume "y \<notin> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i]))"
    then have "y \<notin> budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i])"
      by (meson assms leq_all_in_sol assms)
    then show ?thesis
      by (simp add: budget_constraint_def inner_commute
          consumption_set_member)
  qed
  show ?thesis
    by (metis argmax_entire_budget not_in assms(1,2,3)
        dual_order.order_iff_strict inner_commute)
qed

lemma all_in_argmax_same_price:
  assumes "i \<in> agents"
  assumes "local_nonsatiation consumption_set Pr[i]"
  assumes "x \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i]))"
    and  "y \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (P \<bullet> \<E>[i]))"
  shows "P \<bullet> x = P \<bullet> y"
  using argmax_entire_budget assms(1) assms(2) assms(3) assms(4) by presburger

text \<open> All rationally acting agents (which is every agent by assumption)
        will not decrease his utility \<close>
lemma individual_rationalism :
  assumes "comp_equilib_endow P X \<E>"
  shows "\<forall>i \<in> agents. X i \<succeq>[Pref i] \<E>[i]"
  by (metis pref_more_expensive comp_equilib_endow_def assms
      inner_commute less_irrefl not_le utility_function_def)

lemma walras_law_per_agent :
  assumes "\<And>i. i \<in> agents \<Longrightarrow> local_nonsatiation consumption_set Pr[i]"
  assumes "comp_equilib_endow P X \<E>"
  shows "\<forall>i \<in> agents. P \<bullet> X i = P \<bullet> \<E>[i]"
  by (meson argmax_entire_budget comp_equilib_endow_def assms)

text \<open> Walras Law holds in our Exchange Economy model. It states that in an equilibrium,
       demand equals supply \<close>

lemma walras_law:
  assumes "\<And>i. i \<in> agents \<Longrightarrow> local_nonsatiation consumption_set Pr[i]"
  assumes "comp_equilib_endow P X \<E>"
  shows "(\<Sum>i\<in>agents. P \<bullet> (X i)) - (\<Sum>i\<in>agents. P \<bullet> \<E>[i]) = 0"
  using assms walras_law_per_agent by auto

lemma inner_with_ge_0: "(P::(real, 'n::finite) vec) > 0 \<Longrightarrow> A \<ge> B \<Longrightarrow>  P \<bullet> A \<ge> P \<bullet> B"
  by (metis dual_order.order_iff_strict inner_commute
      interval_inner_leI(2) ord_class.atLeastAtMost_iff)

subsection \<open> First Welfare Theorem in Exchange Economy \<close>

text \<open> We prove the first welfare theorem in our Exchange Economy model. \<close>

theorem first_welfare_theorem_exchange:
  assumes lns : "\<And>i. i \<in> agents \<Longrightarrow> local_nonsatiation consumption_set Pr[i]"
    and price_cond: "Price > 0"
  assumes equilibrium : "comp_equilib_endow Price \<X> \<E>"
  shows "pareto_optimal_endow \<X> \<E>"
proof (rule ccontr)
  assume neg_ass : "\<not> pareto_optimal_endow \<X> \<E>"
  have equili_feasible : "feasible_allocation \<X> \<E>"
    using comp_equilib_endow_def equilibrium
    by (simp add: comp_equilib_endow_def)
  have price_g_zero : "Price > 0"
    by (simp add: price_cond)
  obtain Y where
    xprime_pareto: "feasible_allocation Y \<E> \<and>
            (\<forall>i \<in> agents. U[i] (Y i) \<ge> U[i] (\<X> i)) \<and>
            (\<exists>i \<in> agents. U[i] (Y i) > U[i] (\<X> i))"
    using equili_feasible neg_ass pareto_dominating_def
      pareto_optimal_endow_def by auto
  have is_feasible : "feasible_allocation Y \<E>"
    using xprime_pareto by blast
  have all_great_eq_value : "\<forall>i \<in> agents. Price \<bullet> (Y i) \<ge> Price \<bullet> (\<X> i)"
  proof
    fix i
    assume "i \<in> agents"
    show "Price \<bullet> (Y i) \<ge> Price \<bullet> (\<X> i)"
    proof -
      have x_in_agmx : "(\<X> i) \<in> arg_max_set U[i] (budget_constraint (calculate_value Price) consumption_set (Price \<bullet> \<E>[i]))"
        by (meson \<open>i \<in> agents\<close> comp_equilib_endow_def equilibrium)
      have "( U[i]) (\<X> i) - U[i] (Y i) \<le> 0"
        using \<open>i \<in> agents\<close> xprime_pareto by auto
      hence "Price \<bullet> (\<X> i) - Price \<bullet> (Y i) \<le> 0"
        by (metis \<open>i \<in> agents\<close> argmax_entire_budget diff_le_0_iff_le x_in_agmx
            inner_commute lns same_util_is_equal_or_more_expensive)
      then show ?thesis
        by auto
    qed
  qed
  have ex_greater_value : "\<exists>i \<in> agents. Price \<bullet> (Y i) > Price \<bullet> (\<X> i)"
  proof (rule ccontr)
    assume a1 : "\<not>(\<exists>i \<in> agents. Price \<bullet> (Y i) > Price \<bullet> (\<X> i))"
    obtain i where
      obt_witness : "i \<in> agents" "U[i] (Y i) > ( U[i]) (\<X> i)"
      using xprime_pareto by blast
    have "Price \<bullet> Y i \<noteq> Price \<bullet> \<X> i"
    proof -
      have "Price \<bullet> Y i > Price \<bullet> \<E> i"
        by (metis pref_more_expensive comp_equilib_endow_def
            equilibrium inner_commute obt_witness(1) obt_witness(2))
      have "Price \<bullet> \<E> i = Price \<bullet> \<X> i"
        using equilibrium lns obt_witness(1) walras_law_per_agent by auto
      then show ?thesis
        using \<open>Price \<bullet> \<E> i < Price \<bullet> Y i\<close> by linarith
    qed
    then show False
      using a1 all_great_eq_value obt_witness(1) by fastforce
  qed
  have dominating_more_exp : "Price \<bullet> (\<Sum>i\<in>agents. Y i) > Price \<bullet> (\<Sum>i\<in>agents. \<X> i)"
  proof -
    have mp_rule : "(\<Sum>i\<in>agents. Price \<bullet> Y i) > (\<Sum>i\<in>agents. Price \<bullet> \<X> i) \<Longrightarrow> ?thesis"
      by (simp add: inner_sum_right)
    have "(\<Sum>i\<in>agents. Price \<bullet> Y i) > (\<Sum>i\<in>agents. Price \<bullet> \<X> i)"
      by (simp add: all_great_eq_value finite_agents ex_greater_value sum_strict_mono_ex1)
    thus "Price \<bullet> (\<Sum>i\<in>agents. Y i) > Price \<bullet> (\<Sum>i\<in>agents. \<X> i)"
      using mp_rule by blast
  qed
  have equili_walras_law : "Price \<bullet> (\<Sum>i\<in>agents. \<X> i) = Price \<bullet> (\<Sum>i\<in>agents. \<E>[i])"
    by (metis (mono_tags) eq_iff_diff_eq_0 equilibrium
        inner_sum_right lns walras_law)
  have dominating_feasible : "Price \<bullet> (\<Sum>i\<in>agents. \<X> i) \<ge> Price \<bullet> (\<Sum>i\<in>agents. Y i)"
    by (metis atLeastAtMost_iff dual_order.order_iff_strict equili_walras_law
        feasible_allocation_def inner_commute interval_inner_leI(1) is_feasible price_g_zero)
  show False
    using dominating_more_exp equili_walras_law dominating_feasible
    by linarith
qed


text \<open> Monotone preferences can be used instead of local non-satiation.
       Many textbooks etc. do not introduce the concept of
       local non-satiation and use monotonicity instead. \<close>

corollary first_welfare_exch_thm_monot:
  assumes "\<forall>M \<in> carrier. (\<forall>x > M. x \<in> carrier)"
  assumes "\<And>i. i \<in> agents \<Longrightarrow> monotone_preference consumption_set Pr[i]"
  and price_cond: "Price > 0"
  assumes "comp_equilib_endow Price \<X> \<E>"
  shows "pareto_optimal_endow \<X> \<E>"
  by (meson assms exchange_economy.consumption_set_member
      first_welfare_theorem_exchange exchange_economy_axioms unbounded_above_mono_imp_lns)

end

end

end