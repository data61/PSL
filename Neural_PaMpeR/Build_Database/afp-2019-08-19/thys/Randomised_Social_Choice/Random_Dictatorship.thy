(*  
  Title:    Random_Dictatorship.thy
  Author:   Manuel Eberl, TU München

  Definition and basic properties of Random Dictatorship
  (on weak preferences)
*)

section \<open>Random Dictatorship\<close>

theory Random_Dictatorship
imports
  Complex_Main
  Social_Decision_Schemes
begin

text \<open>
  We define Random Dictatorship as a social decision scheme on total preorders 
  (i.e. agents are allowed to have ties in their rankings) by first selecting an agent
  uniformly at random and then selecting one of that agents' most preferred alternatives
  uniformly at random. Note that this definition also works for weak preferences.
\<close>
definition random_dictatorship :: "'agent set \<Rightarrow> 'alt set \<Rightarrow> ('agent, 'alt) pref_profile \<Rightarrow> 'alt lottery" where
  random_dictatorship_auxdef:
  "random_dictatorship agents alts R =
      do {
        i \<leftarrow> pmf_of_set agents; 
        pmf_of_set (Max_wrt_among (R i) alts)
      }"

context election
begin

abbreviation RD :: "('agent, 'alt) pref_profile \<Rightarrow> 'alt lottery" where
  "RD \<equiv> random_dictatorship agents alts"

lemma random_dictatorship_def:
  assumes "is_pref_profile R"
  shows  "RD R =
            do {
              i \<leftarrow> pmf_of_set agents; 
              pmf_of_set (favorites R i)
            }"
proof -
  from assms interpret pref_profile_wf agents alts R .
  show ?thesis by (simp add: random_dictatorship_auxdef favorites_altdef)
qed

lemma random_dictatorship_unique_favorites:
  assumes "is_pref_profile R" "has_unique_favorites R"
  shows   "RD R = map_pmf (favorite R) (pmf_of_set agents)"
proof -
  from assms(1) interpret pref_profile_wf agents alts R .
  from assms(2) interpret pref_profile_unique_favorites agents alts R by unfold_locales
  show ?thesis unfolding random_dictatorship_def[OF assms(1)] map_pmf_def 
    by (intro bind_pmf_cong) (auto simp: unique_favorites pmf_of_set_singleton)
qed

lemma random_dictatorship_unique_favorites':
  assumes "is_pref_profile R" "has_unique_favorites R"
  shows   "RD R = pmf_of_multiset (image_mset (favorite R) (mset_set agents))"
  using assms by (simp add: random_dictatorship_unique_favorites map_pmf_of_set)

lemma pmf_random_dictatorship:
  assumes "is_pref_profile R"
  shows "pmf (RD R) x =
           (\<Sum>i\<in>agents. indicator (favorites R i) x /
              real (card (favorites R i))) / real (card agents)"
proof -
  from assms(1) interpret pref_profile_wf agents alts R .
  from nonempty_dom have "card agents > 0" by (auto simp del: nonempty_agents)
  hence "ennreal (pmf (RD R) x) = 
           ennreal ((\<Sum>i\<in>agents. pmf (pmf_of_set (favorites R i)) x) / real (card agents))"
    (is "_ = ennreal (?p / _)") unfolding random_dictatorship_def[OF assms]
    by (simp_all add: ennreal_pmf_bind nn_integral_pmf_of_set max_def 
          divide_ennreal [symmetric] ennreal_of_nat_eq_real_of_nat sum_nonneg)
  also have "?p = (\<Sum>i\<in>agents. indicator (favorites R i) x / real (card (favorites R i)))"
    by (intro sum.cong) (simp_all add: favorites_nonempty)
  finally show ?thesis 
    by (subst (asm) ennreal_inj) (auto intro!: sum_nonneg divide_nonneg_nonneg)
qed


sublocale RD: social_decision_scheme agents alts RD
proof
  fix R assume R_wf: "is_pref_profile R"
  then interpret pref_profile_wf agents alts R .
  from R_wf show "RD R \<in> lotteries"
    using favorites_subset_alts favorites_nonempty
    by (auto simp: lotteries_on_def random_dictatorship_def)
qed

text \<open>
  We now show that Random Dictatorship fulfils anonymity, neutrality, 
  and strong strategyproofness.
  At the very least, this shows that the definitions of these notions are 
  consistent.
\<close>

subsection \<open>Anonymity\<close>

text \<open>
  The following proof is essentially the following:
  In Random Dictatorship, permuting the agents in the preference profile is the same
  as applying the permutation to the agent that was picked uniformly at random in the 
  first step. However, uniform distributions are invariant under permutation, therefore
  the outcome is totally unchanged.
\<close>

sublocale RD: anonymous_sds agents alts RD
proof
  fix R \<pi> assume wf: "is_pref_profile R" and perm: "\<pi> permutes agents"
  interpret pref_profile_wf agents alts R by fact
  from wf_permute_agents[OF perm]
    have "RD (R \<circ> \<pi>) = map_pmf \<pi> (pmf_of_set agents) \<bind> (\<lambda>i. pmf_of_set (favorites R i))"
    by (simp add: bind_map_pmf random_dictatorship_def o_def favorites_def)
  also from perm wf have "\<dots> = RD R"
    by (simp add: map_pmf_of_set_inj permutes_inj_on permutes_image random_dictatorship_def)
  finally show "RD (R \<circ> \<pi>) = RD R" .
qed


subsection \<open>Neutrality\<close>

text \<open>
  The proof of neutrality is similar to that of anonymity. We have proven elsewhere
  that the most preferred alternatives of an agent in a profile with permuted alternatives
  are simply the image of the originally preferred alternatives.
  Since we pick one alternative from the most preferred alternatives of the selected agent
  uniformly at random, this means that we effectively pick an agent, then pick on of her 
  most preferred alternatives, and then apply the permutation to that alternative, 
  which is simply Random Dictatorship transformed with the permutation.
\<close>

sublocale RD: neutral_sds agents alts RD
proof
  fix \<sigma> R
  assume perm: "\<sigma> permutes alts" and R_wf: "is_pref_profile R"
  from R_wf interpret pref_profile_wf agents alts R .
  from wf_permute_alts[OF perm] R_wf perm show "RD (permute_profile \<sigma> R) = map_pmf \<sigma> (RD R)"
    by (subst random_dictatorship_def)
       (auto intro!: bind_pmf_cong simp: random_dictatorship_def map_bind_pmf 
          favorites_permute map_pmf_of_set_inj permutes_inj_on favorites_nonempty)
qed


subsection \<open>Strong strategyproofness\<close>

text \<open>
  The argument for strategyproofness is quite simple:
  Since the preferences submitted by an agent @{term i} only influence 
  the outcome when that agent is picked in the first process, it suffices 
  to focus on this case.
  When the agent @{term i} submits her true preferences, the probability of 
  obtaining a result at least as good as @{term x} (for any alternative @{term x})
  is 1, since the outcome will always be one of her most-preferred alternatives.
  Obviously, the probability of obtaining such a result cannot exceed 1 no matter
  what preferences she submits instead, and thus, RD is strategyproof.
\<close>

sublocale RD: strongly_strategyproof_sds agents alts RD
proof (unfold_locales, unfold RD.strongly_strategyproof_profile_def)
  fix R i Ri' assume R_wf: "is_pref_profile R" and i: "i \<in> agents"
                 and Ri'_wf: "total_preorder_on alts Ri'"
  interpret R: pref_profile_wf agents alts R by fact
  from R_wf Ri'_wf i have R'_wf: "is_pref_profile (R(i := Ri'))"
    by (simp add: R.wf_update)
  interpret R': pref_profile_wf agents alts "R(i := Ri')" by fact

  show "SD (R i) (RD (R(i := Ri'))) (RD R)"
  proof (rule R.SD_pref_profileI)
    fix x assume "x \<in> alts"
    hence "emeasure (measure_pmf (RD (R(i := Ri')))) (preferred_alts (R i) x)
             \<le> emeasure (measure_pmf (RD R)) (preferred_alts (R i) x)"
      using Ri'_wf maximal_imp_preferred[of "R i" x]
      by (auto intro!: card_mono nn_integral_mono_AE 
               simp: random_dictatorship_def R_wf R'_wf AE_measure_pmf_iff Max_wrt_prefs_finite
                     emeasure_pmf_of_set Int_absorb2 favorites_def
                     Max_wrt_prefs_nonempty card_gt_0_iff)
    thus "lottery_prob (RD (R(i := Ri'))) (preferred_alts (R i) x)
            \<le> lottery_prob (RD R) (preferred_alts (R i) x)"
      by (simp add: measure_pmf.emeasure_eq_measure) 
  qed (insert R_wf R'_wf, simp_all add: RD.sds_wf i)
qed

end


end
