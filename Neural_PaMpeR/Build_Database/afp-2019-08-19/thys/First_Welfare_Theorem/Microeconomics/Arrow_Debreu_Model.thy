(* License: LGPL *)
(*
Author: Julian Parsert <julian.parsert@gmail.com>
Author: Cezary Kaliszyk
*)


section \<open> Arrow-Debreu model \<close>

theory Arrow_Debreu_Model
  imports
    "HOL-Analysis.Analysis"
    "../Preferences"
    "../Preferences"
    "../Utility_Functions"
    "../Argmax"
    Consumers
    Common
begin

locale pre_arrow_debreu_model =
  fixes production_sets :: "'f \<Rightarrow> ('a::ordered_euclidean_space) set"
  fixes consumption_set :: "'a set"
  fixes agents :: "'i set"
  fixes firms :: "'f set"
  fixes \<E> :: "'i \<Rightarrow> 'a"  ("\<E>[_]")
  fixes Pref :: "'i \<Rightarrow> 'a relation" ("Pr[_]")
  fixes U :: "'i \<Rightarrow> 'a \<Rightarrow> real" ("U[_]")
  fixes \<Theta> :: "'i \<Rightarrow> 'f \<Rightarrow> real"  ("\<Theta>[_,_]")
  assumes cons_set_props: "arrow_debreu_consum_set consumption_set"
  assumes agent_props: "i \<in> agents \<Longrightarrow> eucl_ordinal_utility consumption_set (Pr[i]) (U[i])"
  assumes firms_comp_owned: "j \<in> firms \<Longrightarrow> (\<Sum>i\<in>agents. \<Theta>[i,j]) = 1"
  assumes finite_nonepty_agents: "finite agents" and "agents \<noteq> {}"

sublocale pre_arrow_debreu_model \<subseteq> pareto_ordering agents U
  .

(*sublocale pre_arrow_debreu_model \<subseteq> exchange_economy consumption_set agents \<E> Pref U Price
  by (metis exchange_economy.intro pre_arrow_debreu_model_axioms pre_arrow_debreu_model_def)
*)

context pre_arrow_debreu_model
begin

text \<open> Calculate wealth of individual i in context of Private Ownership economy. \<close>

context 
begin

private abbreviation poe_wealth
  where
    "poe_wealth P i Y \<equiv> P \<bullet> \<E>[i] + (\<Sum>j\<in>firms. \<Theta>[i,j] *\<^sub>R (P \<bullet> Y j))"


subsection \<open> Feasiblity \<close>
private abbreviation feasible
  where
    "feasible X Y \<equiv> feasible_private_ownership agents firms \<E> consumption_set production_sets X Y"

private abbreviation calculate_value 
  where
    "calculate_value P x \<equiv> P \<bullet> x"


subsection \<open> Profit maximisation \<close>

text \<open> In a production economy (which this is) we need to specify profit maximisation. \<close>

definition profit_maximisation
  where
    "profit_maximisation P S = arg_max_set (\<lambda>x. P \<bullet> x) S"


subsection \<open> Competitive Equilibirium \<close>

text \<open> Competitive equilibrium in context of production economy with private ownership.
             This includes the profit maximisation condition. \<close>

definition competitive_equilibrium
  where
    "competitive_equilibrium P X Y \<longleftrightarrow> feasible X Y \<and>
    (\<forall>j \<in> firms. (Y j) \<in> profit_maximisation P (production_sets j)) \<and>
    (\<forall>i \<in> agents. (X i) \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y)))"

lemma competitive_equilibriumD [dest]:
  assumes "competitive_equilibrium P X Y"
  shows "feasible X Y \<and>
         (\<forall>j \<in> firms. (Y j) \<in> profit_maximisation P (production_sets j)) \<and>
         (\<forall>i \<in> agents. (X i) \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y)))"
  using assms by (simp add: competitive_equilibrium_def)

lemma compet_max_profit:
  assumes "j \<in> firms"
  assumes "competitive_equilibrium P X Y"
  shows "Y j \<in> profit_maximisation P (production_sets j)"
  using assms(1) assms(2) by blast

subsection \<open> Pareto Optimality \<close>

definition pareto_optimal
  where
    "pareto_optimal X Y \<longleftrightarrow>
              (feasible X Y \<and>
              (\<nexists>X' Y'. feasible X' Y' \<and> X' \<succ>Pareto X))"

lemma pareto_optimalI[intro]:
  assumes "feasible X Y"
    and "\<nexists>X' Y'. feasible X' Y' \<and> X' \<succ>Pareto X"
  shows "pareto_optimal X Y"
  using pareto_optimal_def assms(1) assms(2) by blast

lemma pareto_optimalD[dest]:
  assumes "pareto_optimal X Y"
  shows "feasible X Y" and "\<nexists>X' Y'. feasible X' Y' \<and> X' \<succ>Pareto X"
  using pareto_optimal_def assms by auto

lemma util_fun_def_holds: 
  assumes "i \<in> agents" 
    and "x \<in> consumption_set" 
    and "y \<in> consumption_set"
  shows "x \<succeq>[Pr[i]] y \<longleftrightarrow> U[i] x \<ge> U[i] y"
proof
  assume "x \<succeq>[Pr[i]] y"
  show "U[i] x \<ge> U[i] y"
    by (meson \<open>x \<succeq>[Pr[i]] y\<close> agent_props assms eucl_ordinal_utility_def ordinal_utility_def)
next
  assume "U[i] x \<ge> U[i] y"
  have "eucl_ordinal_utility consumption_set (Pr[i]) (U[i])"
    by (simp add: agent_props assms)
  then show "x \<succeq>[Pr[i]] y"
    by (meson \<open>U[i] y \<le> U[i] x\<close> assms(2) assms(3) eucl_ordinal_utility_def ordinal_utility.util_def_conf)
qed

lemma base_pref_is_ord_eucl_rpr: "i \<in> agents \<Longrightarrow> rational_preference consumption_set Pr[i]"
  using agent_props ord_eucl_utility_imp_rpr real_vector_rpr.have_rpr by blast

lemma prof_max_ge_all_in_pset:
  assumes "j \<in> firms"
  assumes "Y j \<in> profit_maximisation P (production_sets j)"
  shows "\<forall>y \<in> production_sets j. P \<bullet> Y j \<ge> P \<bullet> y"
  using all_leq assms(2) profit_maximisation_def by fastforce


subsection \<open> Lemmas for final result \<close>

text \<open> Strictly preferred bundles are strictly more expensive. \<close>

lemma all_prefered_are_more_expensive:
  assumes i_agt: "i \<in> agents"
  assumes equil: "competitive_equilibrium P \<X> \<Y>"
  assumes "z \<in> consumption_set"
  assumes "(U i) z > (U i) (\<X> i)"
  shows "z \<bullet> P > P \<bullet> (\<X> i)"
proof (rule ccontr)
  assume neg_as :  "\<not>(z \<bullet> P > P \<bullet> (\<X> i))"
  have xp_leq : "z \<bullet> P \<le> P \<bullet>  (\<X> i)"
    using \<open>\<not>z \<bullet> P > P \<bullet> (\<X> i)\<close> by auto
  have x_in_argmax: "(\<X> i) \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (poe_wealth P i \<Y>))"
    using equil i_agt by blast
  hence x_in: "\<X> i \<in> (budget_constraint (calculate_value P) consumption_set (poe_wealth P i \<Y>))"
    using argmax_sol_in_s [of "(\<X> i)" "U[i]" "budget_constraint (calculate_value P) consumption_set (poe_wealth P i \<Y>)"]
    by blast
  hence z_in_budget: "z \<in> (budget_constraint (calculate_value P) consumption_set (poe_wealth P i \<Y>))"
  proof -
    have z_leq_endow: "P \<bullet> z \<le> P \<bullet> (\<X> i)"
      by (metis xp_leq inner_commute)
    have z_in_cons: "z \<in> consumption_set"
      using assms by auto
    then show ?thesis
      using x_in budget_constraint_def z_leq_endow
    proof -
      have "\<forall>r.  P \<bullet> \<X> i \<le> r \<longrightarrow> P \<bullet> z \<le> r"
        using z_leq_endow by linarith
      then show ?thesis
        using budget_constraint_def x_in z_in_cons
        by (simp add: budget_constraint_def)
    qed
  qed
  have nex_prop: "\<nexists>e. e \<in>  (budget_constraint (calculate_value P) consumption_set (poe_wealth P i \<Y>)) \<and>
        U[i] e > U[i] (\<X> i)"
    using no_better_in_s[of "\<X> i" "U[i]"
        "budget_constraint (calculate_value P) consumption_set (poe_wealth P i \<Y>)"] x_in_argmax by blast
  have "z \<in> budget_constraint (calculate_value P) consumption_set (poe_wealth P i \<Y>) \<and> U[i] z > U[i] (\<X> i)"
    using assms z_in_budget by blast
  thus False using nex_prop
    by blast
qed

text \<open> Given local non-satiation, argmax will use the entire budget. \<close>

lemma am_utilises_entire_bgt:
  assumes i_agts: "i \<in> agents"
  assumes lns : "local_nonsatiation consumption_set Pr[i]"
  assumes argmax_sol : "X \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y))"
  shows "P \<bullet> X = P \<bullet> \<E>[i] + (\<Sum>j\<in>firms. \<Theta>[i,j] *\<^sub>R (P \<bullet> Y j))"
proof -
  let ?wlt = "P \<bullet> \<E>[i] + (\<Sum>j\<in>firms. \<Theta>[i,j] *\<^sub>R (P \<bullet> Y j))"
  let ?bc = "budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y)"
  have xin: "X \<in> budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y)"
    using argmax_sol_in_s [of "X" "U[i]" ?bc] argmax_sol by blast
  hence is_leq: "X \<bullet> P \<le> (poe_wealth P i Y)"
    by (metis (mono_tags, lifting) budget_constraint_def
        inner_commute mem_Collect_eq)
  have not_less: "\<not>X \<bullet> P < (poe_wealth P i Y)"
  proof
    assume neg: "X \<bullet> P < (poe_wealth P i Y)"
    have bgt_leq: "\<forall>x\<in> ?bc. U[i] X \<ge> U[i] x"
      using leq_all_in_sol [of "X" "U[i]" "?bc"]
        all_leq [of "X" "U[i]" "?bc"]
        argmax_sol by blast
    define s_low where
      "s_low = {x . P \<bullet> x < ?wlt}"
    have "\<exists>e > 0. ball X e \<subseteq> s_low"
    proof -
      have x_in_budget: "P \<bullet> X < ?wlt"
        by (metis inner_commute neg)
      have s_low_open: "open s_low"
        using open_halfspace_lt s_low_def by blast
      then show ?thesis
        using s_low_open open_contains_ball_eq
          s_low_def x_in_budget by blast
    qed
    obtain e where
      "e > 0" and e: "ball X e \<subseteq> s_low"
      using \<open>\<exists>e>0. ball X e \<subseteq> s_low\<close> by blast
    obtain y where
      y_props: "y \<in> ball X e" "y \<succ>[Pref i] X"
      using \<open>0 < e\<close> xin assms(2) budget_constraint_def 
      by (metis (no_types, lifting) lns_alt_def2 mem_Collect_eq)
    have "y \<in> budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y)"
    proof -
      have "y \<in> s_low"
        using \<open>y \<in> ball X e\<close> e by blast
      moreover have "y \<in> consumption_set"
        by (meson agent_props eucl_ordinal_utility_def i_agts ordinal_utility_def y_props(2))
      moreover have "P \<bullet> y \<le> poe_wealth P i Y"
        using calculation(1) s_low_def by auto
      ultimately show ?thesis
        by (simp add: budget_constraint_def)
    qed
    then show False
      using bgt_leq i_agts y_props(2) util_fun_def_holds xin budget_constraint_def
      by (metis (no_types, lifting) mem_Collect_eq)
  qed
  then show ?thesis
    by (metis inner_commute is_leq
        less_eq_real_def)
qed

corollary x_equil_x_ext_budget:
  assumes i_agt: "i \<in> agents"
  assumes lns : "local_nonsatiation consumption_set Pr[i]"
  assumes equilibrium : "competitive_equilibrium P X Y"
  shows "P \<bullet> X i = P \<bullet> \<E>[i] + (\<Sum>j\<in>firms. \<Theta>[i,j] *\<^sub>R (P \<bullet> Y j))"
proof -
  have "X i \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y))"
    using equilibrium i_agt by blast
  then show ?thesis
    using am_utilises_entire_bgt i_agt lns by blast
qed

lemma same_price_in_argmax :
  assumes i_agt: "i \<in> agents"
  assumes lns : "local_nonsatiation consumption_set Pr[i]"
  assumes "x \<in> arg_max_set (U[i]) (budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y))"
  assumes "y \<in> arg_max_set (U[i]) (budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y))"
  shows "(P \<bullet> x) = (P \<bullet> y)"
  using am_utilises_entire_bgt assms lns
  by (metis (no_types) am_utilises_entire_bgt assms(3) assms(4) i_agt lns)

text \<open> Greater or equal utility implies greater or equal value. \<close>

lemma utility_ge_price_ge :
  assumes agts: "i \<in> agents"
  assumes lns : "local_nonsatiation consumption_set Pr[i]"
  assumes equil: "competitive_equilibrium P X Y"
  assumes geq: "U[i] z \<ge> U[i] (X i)"
    and "z \<in> consumption_set"
  shows "P \<bullet> z \<ge> P \<bullet> (X i)"
proof -
  let ?bc = "(budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y))"
  have not_in : "z \<notin> arg_max_set (U[i]) ?bc \<Longrightarrow>
    P \<bullet> z > (P \<bullet> \<E>[i]) + (\<Sum>j\<in>(firms). (\<Theta>[i,j] *\<^sub>R (P \<bullet> Y j)))"
  proof-
    assume "z \<notin> arg_max_set (U[i]) ?bc"
    moreover have "X i \<in> arg_max_set (U[i]) ?bc"
      using competitive_equilibriumD assms pareto_optimal_def
      by auto
    ultimately have "z \<notin> budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y)"
      by (meson  geq leq_all_in_sol)
    then show ?thesis
      using budget_constraint_def assms
      by (simp add: budget_constraint_def)
  qed
  have x_in_argmax: "(X i) \<in> arg_max_set U[i] ?bc"
    using agts equil by blast
  hence x_in_budget: "(X i) \<in> ?bc"
    using argmax_sol_in_s [of "(X i)" "U[i]" "?bc"] by blast
  have "U[i] z = U[i] (X i) \<Longrightarrow> P \<bullet> z \<ge> P \<bullet> (X i)"
  proof(rule contrapos_pp)
    assume con_neg: "\<not> P \<bullet> z \<ge> P \<bullet> (X i)"
    then have "P \<bullet> z < P \<bullet> (X i)"
      by linarith
    then have z_in_argmax: "z \<in> arg_max_set U[i] ?bc"
    proof -
      have "P \<bullet>(X i) = P \<bullet> \<E>[i] + (\<Sum>j\<in>firms. \<Theta>[i,j] *\<^sub>R (P \<bullet> Y j))"
        using agts am_utilises_entire_bgt lns x_in_argmax by blast
      then show ?thesis
        by (metis (no_types) con_neg less_eq_real_def not_in)
    qed
    have z_budget_utilisation: "P \<bullet> z = P \<bullet> (X i)"
      by (metis (no_types) agts am_utilises_entire_bgt lns x_in_argmax z_in_argmax)
    have "P \<bullet> (X i) = P \<bullet> \<E>[i] + (\<Sum>j\<in>firms. \<Theta>[i,j] *\<^sub>R (P \<bullet> Y j))"
      using agts am_utilises_entire_bgt lns x_in_argmax by blast
    show "\<not> U[i] z = U[i] (X i)"
      using z_budget_utilisation con_neg by linarith
  qed
  thus ?thesis
    by (metis (no_types) agts am_utilises_entire_bgt eq_iff eucl_less_le_not_le lns not_in x_in_argmax)
qed

lemma commutativity_sums_over_funs:
  fixes X :: "'x set"
  fixes Y :: "'y set"
  shows "(\<Sum>i\<in>X. \<Sum>j\<in>Y. (f i j *\<^sub>R C \<bullet> g j)) = (\<Sum>j\<in>Y.\<Sum>i\<in>X. (f i j *\<^sub>R C \<bullet> g j))"
  using Groups_Big.comm_monoid_add_class.sum.swap by auto

lemma assoc_fun_over_sum:
  fixes X :: "'x set"
  fixes Y :: "'y set"
  shows "(\<Sum>j\<in>Y. \<Sum>i\<in>X. f i j *\<^sub>R C \<bullet> g j) = (\<Sum>j\<in>Y. (\<Sum>i\<in>X. f i j) *\<^sub>R C \<bullet> g j)"
  by (simp add: inner_sum_left scaleR_left.sum)

text \<open> Walras' law in context of production economy with private ownership.
       That is, in an equilibrium demand equals supply. \<close>

lemma walras_law:
  assumes "\<And>i. i\<in>agents \<Longrightarrow> local_nonsatiation consumption_set Pr[i]"
  assumes "(\<forall>i \<in> agents. (X i) \<in> arg_max_set U[i] (budget_constraint (calculate_value P) consumption_set (poe_wealth P i Y)))"
  shows "P \<bullet> (\<Sum>i\<in>agents. (X i)) = P \<bullet> ((\<Sum>i\<in>agents. \<E>[i]) + (\<Sum>j\<in>firms. Y j))"
proof -
  have value_equal: "P \<bullet> (\<Sum>i\<in>agents. (X i)) = P \<bullet> (\<Sum>i\<in>agents. \<E>[i]) + (\<Sum>i\<in>agents. \<Sum>f\<in>firms. \<Theta>[i,f] *\<^sub>R (P \<bullet> Y f))"
  proof -
    have all_exhaust_bgt: "\<forall>i\<in>agents. P \<bullet> (X i) = P \<bullet> \<E>[i] + (\<Sum>j\<in>firms. \<Theta>[i,j] *\<^sub>R (P \<bullet> (Y j)))"
      using assms am_utilises_entire_bgt by blast
    then show ?thesis
      by (simp add:all_exhaust_bgt inner_sum_right sum.distrib)
  qed
  have eq_1: "(\<Sum>i\<in>agents. \<Sum>j\<in>firms. (\<Theta>[i,j] *\<^sub>R P \<bullet> Y j)) = (\<Sum>j\<in>firms. \<Sum>i\<in>agents. (\<Theta>[i,j] *\<^sub>R P \<bullet> Y j))"
    using commutativity_sums_over_funs [of \<Theta> P Y firms agents] by blast
  hence eq_2: "P \<bullet> (\<Sum>i\<in>agents. X i) = P \<bullet> (\<Sum>i\<in>agents. \<E>[i]) + (\<Sum>j\<in>firms. \<Sum>i\<in>agents. \<Theta>[i,j] *\<^sub>R P \<bullet> Y j)"
    using value_equal by auto
  also  have eq_3: "...= P \<bullet> (\<Sum>i\<in>agents. \<E>[i]) + (\<Sum>j\<in>firms. (\<Sum>i\<in>agents. \<Theta>[i,j]) *\<^sub>R P \<bullet>  Y j)"
    using assoc_fun_over_sum[of "\<Theta>" P Y agents firms] by auto
  also have eq_4: "... = P \<bullet> (\<Sum>i\<in>agents. \<E>[i]) + (\<Sum>f\<in>firms. P \<bullet>  Y f)"
    using firms_comp_owned by auto
  have comp_wise_inner: "P \<bullet>  (\<Sum>i\<in>agents. X i) - (P \<bullet> (\<Sum>i\<in>agents. \<E>[i])) - (\<Sum>f\<in>firms. P \<bullet> Y f) = 0"
    using eq_1 eq_2 eq_3 eq_4 by linarith
  then show ?thesis 
    by (simp add: inner_right_distrib inner_sum_right)
qed

lemma walras_law_in_compeq:
  assumes "\<And>i. i\<in>agents \<Longrightarrow> local_nonsatiation consumption_set Pr[i]"
  assumes "competitive_equilibrium P X Y"
  shows "P \<bullet> ((\<Sum>i\<in>agents. (X i)) - (\<Sum>i\<in>agents. \<E>[i]) - (\<Sum>j\<in>firms. Y j)) = 0"
proof-
  have "P \<bullet> (\<Sum>i\<in>agents. (X i)) = P \<bullet> ((\<Sum>i\<in>agents. \<E>[i]) + (\<Sum>j\<in>firms. Y j))"
    using assms(1) assms(2) walras_law by auto
  then show ?thesis
    by (simp add: inner_diff_right inner_right_distrib)
qed

subsection \<open> First Welfare Theorem \<close>

text \<open> Proof of First Welfare Theorem in context of production economy with private ownership. \<close>

theorem first_welfare_theorem_priv_own:
  assumes "\<And>i. i \<in> agents \<Longrightarrow> local_nonsatiation consumption_set Pr[i]"
    and "Price > 0"
  assumes "competitive_equilibrium Price \<X> \<Y>"
  shows "pareto_optimal \<X> \<Y>"
proof (rule ccontr)
  assume neg_as: "\<not> pareto_optimal \<X> \<Y>"
  have equili_feasible : "feasible \<X> \<Y>"
    using  assms by (simp add: competitive_equilibrium_def)
  obtain X' Y' where
    xprime_pareto: "feasible X' Y' \<and>
      (\<forall>i \<in> agents. U[i] (X' i) \<ge> U[i] (\<X> i)) \<and>
      (\<exists>i \<in> agents. U[i] (X' i) > U[i] (\<X> i))"
    using equili_feasible pareto_optimal_def
      pareto_dominating_def neg_as by auto
  have is_feasible: "feasible X' Y'"
    using xprime_pareto by blast
  have xprime_leq_y: "\<forall>i \<in> agents. (Price \<bullet> (X' i) \<ge>
    (Price \<bullet> \<E>[i]) + (\<Sum>j\<in>(firms). \<Theta>[i,j] *\<^sub>R (Price \<bullet> \<Y> j)))"
  proof
    fix i
    assume as: "i \<in> agents"
    have xprime_cons: "X' i \<in> consumption_set"
      using feasible_private_ownershipD as is_feasible by blast
    have x_leq_xprime: "U[i] (X' i) \<ge> U[i] (\<X> i)"
      using \<open>i \<in> agents\<close> xprime_pareto by blast
    have lns_pref: "local_nonsatiation consumption_set Pr[i]"
      using as assms by blast
    hence xprime_ge_x: "Price \<bullet> (X' i) \<ge> Price \<bullet> (\<X> i)"
      using x_leq_xprime xprime_cons as assms utility_ge_price_ge by blast
    then show  "Price \<bullet> (X' i) \<ge> (Price \<bullet> \<E>[i]) + (\<Sum>j\<in>(firms). \<Theta>[i,j] *\<^sub>R (Price \<bullet> \<Y> j))"
      using xprime_ge_x \<open>i \<in> agents\<close> lns_pref assms x_equil_x_ext_budget by fastforce
  qed
  have ex_greater_value : "\<exists>i \<in> agents. Price \<bullet> (X' i) > Price \<bullet> (\<X> i)"
  proof(rule ccontr)
    assume cpos : "\<not>(\<exists>i \<in> agents. Price \<bullet> (X' i) > Price \<bullet> (\<X> i))"
    obtain i where
      obt_witness : "i \<in> agents" "(U[i]) (X' i) > U[i] (\<X> i)"
      using xprime_pareto by blast
    show False
      by (metis all_prefered_are_more_expensive assms(3) cpos 
          feasible_private_ownershipD(2) inner_commute xprime_pareto)
  qed
  have dom_g : "Price \<bullet> (\<Sum>i\<in>agents. X' i) > Price \<bullet> (\<Sum>i\<in>agents. (\<X> i))" (is "_ > _ \<bullet> ?x_sum")
  proof-
    have "(\<Sum>i\<in>agents. Price \<bullet> X' i) > (\<Sum>i\<in>agents. Price \<bullet> (\<X> i))"
      by (metis (mono_tags, lifting) xprime_leq_y assms(1,3) ex_greater_value
          finite_nonepty_agents sum_strict_mono_ex1 x_equil_x_ext_budget)
    thus "Price \<bullet> (\<Sum>i\<in>agents. X' i) > Price \<bullet> ?x_sum"
      by (simp add: inner_sum_right)
  qed
  let ?y_sum = "(\<Sum>j\<in>firms. \<Y> j)"
  have equili_walras_law: "Price \<bullet> ?x_sum =
    (\<Sum>i\<in>agents. Price \<bullet> \<E>[i] + (\<Sum>j\<in>firms. \<Theta>[i,j] *\<^sub>R (Price \<bullet> \<Y> j)))" (is "_ = ?ws")
  proof-
    have "\<forall>i\<in>agents. Price \<bullet> \<X> i = Price \<bullet> \<E>[i] + (\<Sum>j\<in>firms. \<Theta>[i,j] *\<^sub>R (Price \<bullet> \<Y> j))"
      by (metis (no_types, lifting) assms(1,3) x_equil_x_ext_budget)
    then show ?thesis
      by (simp add: inner_sum_right)
  qed
  also have remove_firm_pct: "... = Price \<bullet> (\<Sum>i\<in>agents. \<E>[i]) + (Price \<bullet> ?y_sum)"
  proof-
    have equals_inner_price:"0 = Price \<bullet> (?x_sum - ((\<Sum>i\<in>agents. \<E> i) + ?y_sum))"
      by (metis (no_types) diff_diff_add assms(1,3) walras_law_in_compeq)
    have "Price \<bullet> ?x_sum = Price \<bullet> ((\<Sum>i\<in>agents. \<E> i) + ?y_sum)"
      by (metis (no_types) equals_inner_price inner_diff_right right_minus_eq)
    then show ?thesis
      by (simp add: equili_walras_law inner_right_distrib)
  qed
  have xp_l_yp: "(\<Sum>i\<in>agents. X' i) \<le> (\<Sum>i\<in>agents. \<E>[i]) + (\<Sum>f\<in>firms. Y' f)"
    using feasible_private_ownership_def is_feasible by blast
  hence yprime_sgr_y: "Price \<bullet> (\<Sum>i\<in>agents. \<E>[i]) + Price \<bullet> (\<Sum>f\<in>firms. Y' f) > ?ws"
  proof -
    have "Price \<bullet> (\<Sum>i\<in>agents. X' i) \<le> Price \<bullet> ((\<Sum>i\<in>agents. \<E>[i]) + (\<Sum>j\<in>firms. Y' j))"
      by (metis xp_l_yp atLeastAtMost_iff inner_commute
          interval_inner_leI(2) less_imp_le order_refl assms(2))
    hence "?ws < Price \<bullet> ((\<Sum>i\<in>agents. \<E> i) + (\<Sum>j\<in>firms. Y' j))"
      using dom_g equili_walras_law by linarith
    then show ?thesis
      by (simp add: inner_right_distrib)
  qed
  have Y_is_optimum: "\<forall>j\<in>firms. \<forall>y \<in> production_sets j. Price \<bullet> \<Y> j \<ge> Price \<bullet> y"
    using assms prof_max_ge_all_in_pset by blast
  have yprime_in_prod_set: "\<forall>j \<in> firms. Y' j \<in> production_sets j"
    using feasible_private_ownershipD xprime_pareto by fastforce
  hence "\<forall>j \<in> firms. \<forall>y \<in> production_sets j. Price \<bullet> \<Y> j \<ge> Price \<bullet> y"
    using Y_is_optimum by blast
  hence Y_ge_yprime: "\<forall>j \<in> firms. Price \<bullet> \<Y> j \<ge> Price \<bullet> Y' j"
    using yprime_in_prod_set by blast
  hence yprime_p_leq_Y: "Price \<bullet> (\<Sum>f\<in>firms. Y' f) \<le> Price \<bullet> ?y_sum"
    by (simp add: Y_ge_yprime inner_sum_right sum_mono)
  then show False
    using remove_firm_pct yprime_sgr_y by linarith
qed

text \<open> Equilibrium cannot be Pareto dominated. \<close>

lemma equilibria_dom_eachother:
  assumes "\<And>i. i \<in> agents \<Longrightarrow> local_nonsatiation consumption_set Pr[i]"
    and "Price > 0"
  assumes equil: "competitive_equilibrium Price \<X> \<Y>"
  shows "\<nexists>X' Y'. competitive_equilibrium P X' Y' \<and> X' \<succ>Pareto \<X>"
proof -
  have "pareto_optimal \<X> \<Y>"
    by (meson equil first_welfare_theorem_priv_own assms)
  hence "\<nexists>X' Y'. feasible X' Y' \<and> X' \<succ>Pareto \<X>"
    using pareto_optimal_def by blast
  thus ?thesis
    by auto
qed

text \<open> Using monotonicity instead of local non-satiation proves the First Welfare Theorem. \<close>

corollary first_welfare_thm_monotone:
  assumes "\<forall>M \<in> carrier. (\<forall>x > M. x \<in> carrier)"
  assumes "\<And>i. i \<in> agents \<Longrightarrow> monotone_preference consumption_set Pr[i]"
    and "Price > 0"
  assumes "competitive_equilibrium Price \<X> \<Y>"
  shows "pareto_optimal \<X> \<Y>"
  by (meson arrow_debreu_consum_set_def assms cons_set_props first_welfare_theorem_priv_own unbounded_above_mono_imp_lns)

end

end

end
