(*  
  Title:    Social Decision Schemes.thy
  Author:   Manuel Eberl, TU München

  Definitions of Social Decision Schemes, their properties, and related concepts
*)

section \<open>Social Decision Schemes\<close>

theory Social_Decision_Schemes
imports 
  Complex_Main 
  "HOL-Probability.Probability"
  Preference_Profiles
  Elections
  Order_Predicates
  Stochastic_Dominance
  SD_Efficiency
begin

subsection \<open>Basic Social Choice definitions\<close>

context election
begin

text \<open>
  The set of lotteries, i.e. the probability mass functions on the type @{typ "'alt"}
  whose support is a subset of the alternative set. 
\<close>
abbreviation lotteries where
  "lotteries \<equiv> lotteries_on alts"

text \<open>
  The probability that a lottery returns an alternative that is in the given set
\<close>
abbreviation lottery_prob :: "'alt lottery \<Rightarrow> 'alt set \<Rightarrow> real" where
  "lottery_prob \<equiv> measure_pmf.prob"

lemma lottery_prob_alts_superset: 
  assumes "p \<in> lotteries" "alts \<subseteq> A"
  shows   "lottery_prob p A = 1"
  using assms by (subst measure_pmf.prob_eq_1) (auto simp: AE_measure_pmf_iff lotteries_on_def)

lemma lottery_prob_alts: "p \<in> lotteries \<Longrightarrow> lottery_prob p alts = 1"
  by (rule lottery_prob_alts_superset) simp_all

end


text \<open>
  In the context of an election, a preference profile is a function that 
  assigns to each agent her preference relation (which is a total preorder)
\<close>


subsection \<open>Social Decision Schemes\<close>

text \<open>
  In the context of an election, a Social Decision Scheme (SDS) is a function that 
  maps preference profiles to lotteries on the alternatives.
\<close> 
locale social_decision_scheme = election agents alts 
  for agents :: "'agent set" and alts :: "'alt set" +
  fixes sds :: "('agent, 'alt) pref_profile \<Rightarrow> 'alt lottery"
  assumes sds_wf: "is_pref_profile R \<Longrightarrow> sds R \<in> lotteries"


subsection \<open>Anonymity\<close>

text \<open>
  An SDS is anonymous if permuting the agents in the input does not change the result.
\<close>
locale anonymous_sds = social_decision_scheme agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  assumes anonymous: "\<pi> permutes agents \<Longrightarrow> is_pref_profile R \<Longrightarrow> sds (R \<circ> \<pi>) = sds R" 
begin

lemma anonymity_prefs_from_table:
  assumes "prefs_from_table_wf agents alts xs" "prefs_from_table_wf agents alts ys"
  assumes "mset (map snd xs) = mset (map snd ys)"
  shows   "sds (prefs_from_table xs) = sds (prefs_from_table ys)"
proof -
  from prefs_from_table_agent_permutation[OF assms] guess \<pi> .
  with anonymous[of \<pi>, of "prefs_from_table xs"] assms(1) show ?thesis 
    by (simp add: pref_profile_from_tableI)
qed

context
begin
qualified lemma anonymity_prefs_from_table_aux:
  assumes "R1 = prefs_from_table xs" "prefs_from_table_wf agents alts xs"
  assumes "R2 = prefs_from_table ys" "prefs_from_table_wf agents alts ys"
  assumes "mset (map snd xs) = mset (map snd ys)"
  shows   "sds R1 = sds R2" unfolding assms(1,3)
  by (rule anonymity_prefs_from_table) (simp_all add: assms del: mset_map)
end

end


subsection \<open>Neutrality\<close>

text \<open>
  An SDS is neutral if permuting the alternatives in the input does not change the
  result, modulo the equivalent permutation in the output lottery.
\<close>
locale neutral_sds = social_decision_scheme agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  assumes neutral: "\<sigma> permutes alts \<Longrightarrow> is_pref_profile R \<Longrightarrow> 
                        sds (permute_profile \<sigma> R) = map_pmf \<sigma> (sds R)"
begin

text \<open>
  Alternative formulation of neutrality that shows that our definition is 
  equivalent to that in the paper.
\<close>
lemma neutral':
  assumes "\<sigma> permutes alts"
  assumes "is_pref_profile R"
  assumes "a \<in> alts"
  shows   "pmf (sds (permute_profile \<sigma> R)) (\<sigma> a) = pmf (sds R) a"
proof -
  from assms have A: "set_pmf (sds R) \<subseteq> alts" using sds_wf
    by (simp add: lotteries_on_def)
  from assms(1,2) have "pmf (sds (permute_profile \<sigma> R)) (\<sigma> a) = pmf (map_pmf \<sigma> (sds R)) (\<sigma> a)"
    by (subst neutral) simp_all
  also from assms have "\<dots> = pmf (sds R) a"
    by (intro pmf_map_inj') (simp_all add: permutes_inj)
  finally show ?thesis .
qed

end


locale an_sds = 
  anonymous_sds agents alts sds + neutral_sds agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds
begin

lemma sds_anonymous_neutral:
  assumes perm: "\<sigma> permutes alts" and wf: "is_pref_profile R1" "is_pref_profile R2"
  assumes eq: "anonymous_profile R1 = 
                 image_mset (map ((`) \<sigma>)) (anonymous_profile R2)"
  shows   "sds R1 = map_pmf \<sigma> (sds R2)"
proof -
  interpret R1: pref_profile_wf agents alts R1 by fact
  interpret R2: pref_profile_wf agents alts R2 by fact
  from perm have wf': "is_pref_profile (permute_profile \<sigma> R2)"
    by (rule R2.wf_permute_alts)
  from eq perm have "anonymous_profile R1 = anonymous_profile (permute_profile \<sigma> R2)"
    by (simp add: R2.anonymous_profile_permute)
  from anonymous_profile_agent_permutation[OF this wf(1) wf']
    obtain \<pi> where "\<pi> permutes agents" "permute_profile \<sigma> R2 \<circ> \<pi> = R1" by auto
  have "sds (permute_profile \<sigma> R2 \<circ> \<pi>) = sds (permute_profile \<sigma> R2)"
    by (rule anonymous) fact+
  also have "\<dots> = map_pmf \<sigma> (sds R2)"
    by (rule neutral) fact+
  also have "permute_profile \<sigma> R2 \<circ> \<pi> = R1" by fact
  finally show ?thesis .
qed


lemma sds_anonymous_neutral':
  assumes perm: "\<sigma> permutes alts" and wf: "is_pref_profile R1" "is_pref_profile R2"
  assumes eq: "anonymous_profile R1 = 
                 image_mset (map ((`) \<sigma>)) (anonymous_profile R2)"
  shows   "pmf (sds R1) (\<sigma> x) = pmf (sds R2) x"
proof -
  have "sds R1 = map_pmf \<sigma> (sds R2)" by (intro sds_anonymous_neutral) fact+
  also have "pmf \<dots> (\<sigma> x) = pmf (sds R2) x" by (intro pmf_map_inj' permutes_inj[OF perm])
  finally show ?thesis .
qed

lemma sds_automorphism:
  assumes perm: "\<sigma> permutes alts" and wf: "is_pref_profile R"
  assumes eq: "image_mset (map ((`) \<sigma>)) (anonymous_profile R) = anonymous_profile R"
  shows   "map_pmf \<sigma> (sds R) = sds R"
  using sds_anonymous_neutral[OF perm wf wf eq [symmetric]] ..

end

lemma an_sds_automorphism_aux:
  assumes wf: "prefs_from_table_wf agents alts yss" "R \<equiv> prefs_from_table yss"
  assumes an: "an_sds agents alts sds"
  assumes eq: "mset (map ((map ((`) (permutation_of_list xs))) \<circ> snd) yss) = mset (map snd yss)"
  assumes perm: "set (map fst xs) \<subseteq> alts" "set (map snd xs) = set (map fst xs)" 
                "distinct (map fst xs)" 
      and x: "x \<in> alts" "y = permutation_of_list xs x"
  shows   "pmf (sds R) x = pmf (sds R) y"
proof -
  note perm = list_permutesI[OF perm]
  let ?\<sigma> = "permutation_of_list xs"
  note perm' = permutation_of_list_permutes [OF perm]
  from wf have wf': "pref_profile_wf agents alts R" by (simp add: pref_profile_from_tableI)
  then interpret R: pref_profile_wf agents alts R .
  from perm' interpret R': pref_profile_wf agents alts "permute_profile ?\<sigma> R"
    by (simp add: R.wf_permute_alts)
  from an interpret an_sds agents alts sds .

  from eq wf have eq': "image_mset (map ((`) ?\<sigma>)) (anonymous_profile R) = anonymous_profile R"
    by (simp add: anonymise_prefs_from_table mset_map multiset.map_comp)
  from perm' x have "pmf (sds R) x = pmf (map_pmf ?\<sigma> (sds R)) (?\<sigma> x)"
    by (simp add: pmf_map_inj' permutes_inj)
  also from eq' x wf' perm' have "map_pmf ?\<sigma> (sds R) = sds R"
    by (intro sds_automorphism) 
       (simp_all add: R.anonymous_profile_permute pref_profile_from_tableI)
  finally show ?thesis using x by simp
qed


subsection \<open>Ex-post efficiency\<close>

locale ex_post_efficient_sds = social_decision_scheme agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  assumes ex_post_efficient: 
    "is_pref_profile R \<Longrightarrow> set_pmf (sds R) \<inter> pareto_losers R = {}"
begin

lemma ex_post_efficient':
  assumes "is_pref_profile R" "y \<succ>[Pareto(R)] x"
  shows   "pmf (sds R) x = 0"
  using ex_post_efficient[of R] assms 
  by (auto simp: set_pmf_eq pareto_losers_def)

lemma ex_post_efficient'':
  assumes "is_pref_profile R" "i \<in> agents"  "\<forall>i\<in>agents. y \<succeq>[R i] x" "\<not>y \<preceq>[R i] x"
  shows   "pmf (sds R) x = 0"
proof -
  from assms(1) interpret pref_profile_wf agents alts R .
  from assms(2-) show ?thesis
    by (intro ex_post_efficient'[OF assms(1), of _ y])
       (auto simp: Pareto_iff strongly_preferred_def)
qed

end



subsection \<open>SD efficiency\<close>

text \<open>
  An SDS is SD-efficient if it returns an SD-efficient lottery for every 
  preference profile, i.e. if the SDS outputs a lottery, it is never the case 
  that there is another lottery that is weakly preferred by all agents an 
  strictly preferred by at least one agent.
\<close>
locale sd_efficient_sds = social_decision_scheme agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  assumes SD_efficient: "is_pref_profile R \<Longrightarrow> SD_efficient R (sds R)"
begin

text \<open>
  An alternative formulation of SD-efficiency that is somewhat more convenient to use.
\<close>
lemma SD_efficient':
  assumes "is_pref_profile R" "q \<in> lotteries"
  assumes "\<And>i. i \<in> agents \<Longrightarrow> q \<succeq>[SD(R i)] sds R" "i \<in> agents" "q \<succ>[SD(R i)] sds R"
  shows   P
proof -
  interpret pref_profile_wf agents alts R by fact
  show ?thesis
    using SD_efficient[of R] sds_wf[OF assms(1)] assms unfolding SD_efficient_def' by blast
qed


text \<open>
  Any SD-efficient SDS is also ex-post efficient.
\<close>
sublocale ex_post_efficient_sds
proof unfold_locales
  fix R :: "('agent, 'alt) pref_profile" assume R_wf: "is_pref_profile R"
  interpret pref_profile_wf agents alts R by fact
  from R_wf show "set_pmf (sds R) \<inter> pareto_losers R = {}"
    by (intro SD_efficient_no_pareto_loser SD_efficient sds_wf)
qed


text \<open>
  The following rule can be used to derive facts from inefficient supports:
  If a set of alternatives is an inefficient support, at least one of the 
  alternatives in it must receive probability 0.
\<close>
lemma SD_inefficient_support:
  assumes A: "A \<noteq> {}" "A \<subseteq> alts" and inefficient: "\<not>SD_efficient R (pmf_of_set A)" 
  assumes wf: "is_pref_profile R" 
  shows   "\<exists>x\<in>A. pmf (sds R) x = 0"
proof (rule ccontr)
  interpret pref_profile_wf agents alts R by fact
  assume "\<not>(\<exists>x\<in>A. pmf (sds R) x = 0)"
  with A have "set_pmf (pmf_of_set A) \<subseteq> set_pmf (sds R)"
     by (subst set_pmf_of_set) (auto simp: set_pmf_eq intro: finite_subset[OF _ finite_alts])
  from inefficient and this have "\<not>SD_efficient R (sds R)"
    by (rule SD_inefficient_support_subset) (simp add: wf sds_wf)
  moreover from SD_efficient wf have "SD_efficient R (sds R)" .
  ultimately show False by contradiction
qed

lemma SD_inefficient_support':
  assumes wf: "is_pref_profile R" 
  assumes A: "A \<noteq> {}" "A \<subseteq> alts" and 
     wit: "p \<in> lotteries" "\<forall>i\<in>agents. p \<succeq>[SD(R i)] pmf_of_set A" "i \<in> agents" 
          "\<not>p \<preceq>[SD(R i)] pmf_of_set A"
  shows   "\<exists>x\<in>A. pmf (sds R) x = 0"
proof (rule SD_inefficient_support)
  from wf interpret pref_profile_wf agents alts R .
  from wit show "\<not>SD_efficient R (pmf_of_set A)"
    by (intro SD_inefficientI') (auto intro!: bexI[of _ i] simp: strongly_preferred_def)
qed fact+

end



subsection \<open>Weak strategyproofness\<close>

context social_decision_scheme
begin

text \<open>
  The SDS is said to be manipulable for a particular preference profile,
  a particular agent, and a particular alternative preference ordering for that agent
  if the lottery obtained if the agent submits the alternative preferences strictly 
  SD-dominates that obtained if the original preferences are submitted.
  (SD-dominated w.r.t. the original preferences)
\<close>
definition manipulable_profile 
    :: "('agent, 'alt) pref_profile \<Rightarrow> 'agent \<Rightarrow> 'alt relation \<Rightarrow> bool" where 
  "manipulable_profile R i Ri' \<longleftrightarrow> sds (R(i := Ri')) \<succ>[SD (R i)] sds R"

end


text \<open>
  An SDS is weakly strategyproof (or just strategyproof) if it is not manipulable 
  for any combination of preference profiles, agents, and alternative preference relations.
\<close>
locale strategyproof_sds = social_decision_scheme agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  assumes strategyproof: 
    "is_pref_profile R \<Longrightarrow> i \<in> agents \<Longrightarrow> total_preorder_on alts Ri' \<Longrightarrow>
         \<not>manipulable_profile R i Ri'"  


subsection \<open>Strong strategyproofness\<close>

context social_decision_scheme
begin

text \<open>
  The SDS is said to be strongly strategyproof for a particular preference profile, 
  a particular agent, and a particular alternative preference ordering for that agent
  if the lottery obtained if the agent submits the alternative preferences is
  SD-dominated by the one obtained if the original preferences are submitted.
  (SD-dominated w.r.t. the original preferences)
  
  In other words: the SDS is strategyproof w.r.t the preference profile $R$ and 
  the agent $i$ and the alternative preference relation $R_i'$ if the lottery for 
  obtained for $R$ is at least as good for $i$ as the lottery obtained when $i$ 
  misrepresents her preferences as $R_i'$.
\<close>
definition strongly_strategyproof_profile 
    :: "('agent, 'alt) pref_profile \<Rightarrow> 'agent \<Rightarrow> 'alt relation \<Rightarrow> bool" where
  "strongly_strategyproof_profile R i Ri' \<longleftrightarrow> sds R \<succeq>[SD (R i)] sds (R(i := Ri'))"

lemma strongly_strategyproof_profileI [intro]:
  assumes "is_pref_profile R" "total_preorder_on alts Ri'" "i \<in> agents"
  assumes "\<And>x. x \<in> alts \<Longrightarrow> lottery_prob (sds (R(i := Ri'))) (preferred_alts (R i) x)
                               \<le> lottery_prob (sds R) (preferred_alts (R i) x)"
  shows "strongly_strategyproof_profile R i Ri'"
proof -
  interpret pref_profile_wf agents alts R by fact
  show ?thesis
    unfolding strongly_strategyproof_profile_def
    by rule (auto intro!: sds_wf assms pref_profile_wf.wf_update)
qed

lemma strongly_strategyproof_imp_not_manipulable:
  assumes "strongly_strategyproof_profile R i Ri'"
  shows   "\<not>manipulable_profile R i Ri'"
  using assms unfolding strongly_strategyproof_profile_def manipulable_profile_def
  by (auto simp: strongly_preferred_def)

end


text \<open>
  An SDS is strongly strategyproof if it is strongly strategyproof for all combinations
  of preference profiles, agents, and alternative preference relations.
\<close>
locale strongly_strategyproof_sds = social_decision_scheme agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  assumes strongly_strategyproof: 
    "is_pref_profile R \<Longrightarrow> i \<in> agents \<Longrightarrow> total_preorder_on alts Ri' \<Longrightarrow>
         strongly_strategyproof_profile R i Ri'"
begin

text \<open>
  Any SDS that is strongly strategyproof is also weakly strategyproof.
\<close>
sublocale strategyproof_sds
  by unfold_locales
     (simp add: strongly_strategyproof_imp_not_manipulable strongly_strategyproof)

end


locale strategyproof_an_sds =
  strategyproof_sds agents alts sds + an_sds agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds

end
