(*  
  Title:    SDS_Lowering.thy
  Author:   Manuel Eberl, TU München

  Allows to lower an SDS, i.e. take an existing ex-post efficient SDS
  and construct from it an SDS for fewer agents and alternatives. (which is
  also ex-post efficient)
    The standard properties (anonymity, neutrality, SD efficiency, strategyproofness)
  are preserved by this construction.
*)

section \<open>Lowering Social Decision Schemes\<close>

theory SDS_Lowering
imports Social_Decision_Schemes
begin

definition lift_pref_profile :: 
    "'agent set \<Rightarrow> 'alt set \<Rightarrow> 'agent set \<Rightarrow> 'alt set \<Rightarrow>
       ('agent, 'alt) pref_profile \<Rightarrow> ('agent, 'alt) pref_profile" where
  "lift_pref_profile agents alts agents' alts' R = (\<lambda>i x y. 
     x \<in> alts' \<and> y \<in> alts' \<and> i \<in> agents' \<and>
     (x = y \<or> x \<notin> alts \<or> i \<notin> agents \<or> (y \<in> alts \<and> R i x y)))"

lemma lift_pref_profile_wf:
  assumes "pref_profile_wf agents alts R"
  assumes "agents \<subseteq> agents'" "alts \<subseteq> alts'" "finite alts'"
  defines "R' \<equiv> lift_pref_profile agents alts agents' alts' R"
  shows   "pref_profile_wf agents' alts' R'"
proof -
  from assms interpret R: pref_profile_wf agents alts by simp
  have "finite_total_preorder_on alts' (R' i)" 
    if i: "i \<in> agents'" for i
  proof (cases "i \<in> agents")
    case True
    then interpret finite_total_preorder_on alts "R i" by simp
    from True assms show ?thesis
      by unfold_locales (auto simp: lift_pref_profile_def dest: total intro: trans)
  next 
    case False
    with assms i show ?thesis
      by unfold_locales (simp_all add: lift_pref_profile_def)
  qed
  moreover have "R' i = (\<lambda>_ _. False)" if "i \<notin> agents'" for i
    unfolding lift_pref_profile_def R'_def using that by simp
  ultimately show ?thesis unfolding pref_profile_wf_def using assms by auto
qed

lemma lift_pref_profile_permute_agents:
  assumes "\<pi> permutes agents" "agents \<subseteq> agents'"
  shows   "lift_pref_profile agents alts agents' alts' (R \<circ> \<pi>) = 
             lift_pref_profile agents alts agents' alts' R \<circ> \<pi>"
  using assms permutes_subset[OF assms]
  by (auto simp add: lift_pref_profile_def o_def permutes_in_image)

lemma lift_pref_profile_permute_alts:
  assumes "\<sigma> permutes alts" "alts \<subseteq> alts'"
  shows   "lift_pref_profile agents alts agents' alts' (permute_profile \<sigma> R) = 
             permute_profile \<sigma> (lift_pref_profile agents alts agents' alts' R)"
proof -
  from assms have inv: "inv \<sigma> permutes alts" by (intro permutes_inv)
  from this assms(2) have "inv \<sigma> permutes alts'" by (rule permutes_subset)
  with inv show ?thesis using assms permutes_inj[OF \<open>inv \<sigma> permutes alts\<close>]
    by (fastforce simp add: lift_pref_profile_def permutes_in_image
          permute_profile_def fun_eq_iff dest: injD)
qed


lemma lotteries_on_subset: "A \<subseteq> B \<Longrightarrow> p \<in> lotteries_on A \<Longrightarrow> p \<in> lotteries_on B"
  unfolding lotteries_on_def by blast

lemma lottery_prob_carrier: "p \<in> lotteries_on A \<Longrightarrow> measure_pmf.prob p A = 1"
  by (auto simp: measure_pmf.prob_eq_1 lotteries_on_def AE_measure_pmf_iff)

context
  fixes agents alts R agents' alts' R'
  assumes R_wf: "pref_profile_wf agents alts R"
  assumes election: "agents \<subseteq> agents'" "alts \<subseteq> alts'" "alts \<noteq> {}" "agents \<noteq> {}" "finite alts'"
  defines "R' \<equiv> lift_pref_profile agents alts agents' alts' R"
begin

interpretation R: pref_profile_wf agents alts R by fact
interpretation R': pref_profile_wf agents' alts' R' 
  using election R_wf by (simp add: R'_def lift_pref_profile_wf)

lemma lift_pref_profile_strict_iff:
  "x \<prec>[lift_pref_profile agents alts agents' alts' R i] y \<longleftrightarrow>
     i \<in> agents \<and> ((y \<in> alts \<and> x \<in> alts' - alts) \<or> x \<prec>[R i] y)"
proof (cases "i \<in> agents")
  case True
  then interpret total_preorder_on alts "R i" by simp
  show ?thesis using not_outside election
    by (auto simp: lift_pref_profile_def strongly_preferred_def)
qed (simp_all add: lift_pref_profile_def strongly_preferred_def)

lemma preferred_alts_lift_pref_profile: 
  assumes i: "i \<in> agents'" and x: "x \<in> alts'"
  shows   "preferred_alts (R' i) x = 
             (if i \<in> agents \<and> x \<in> alts then preferred_alts (R i) x else alts')"
proof (cases "i \<in> agents")
  assume i: "i \<in> agents"
  then interpret Ri: total_preorder_on alts "R i" by simp
  show ?thesis
  using i x election Ri.not_outside
    by (auto simp: preferred_alts_def R'_def lift_pref_profile_def Ri.refl)
qed (auto simp: preferred_alts_def R'_def lift_pref_profile_def i x)

lemma lift_pref_profile_Pareto_iff:
  "x \<preceq>[Pareto(R')] y \<longleftrightarrow> x \<in> alts' \<and> y \<in> alts' \<and> (x \<notin> alts \<or> x \<preceq>[Pareto(R)] y)"
proof -
  from R.nonempty_agents obtain i where i: "i \<in> agents" by blast
  then interpret Ri: finite_total_preorder_on alts "R i" by simp
  show ?thesis unfolding R'.Pareto_iff R.Pareto_iff unfolding R'_def lift_pref_profile_def
    using election i by (auto simp: preorder_on.refl[OF R.in_dom] 
      simp del: R.nonempty_alts R.nonempty_agents  intro: Ri.not_outside)
qed

lemma lift_pref_profile_Pareto_strict_iff:
  "x \<prec>[Pareto(R')] y \<longleftrightarrow> x \<in> alts' \<and> y \<in> alts' \<and> (x \<notin> alts \<and> y \<in> alts \<or> x \<prec>[Pareto(R)] y)"
  by (auto simp: strongly_preferred_def lift_pref_profile_Pareto_iff R.Pareto.not_outside)

lemma pareto_losers_lift_pref_profile:
  shows   "pareto_losers R' = pareto_losers R \<union> (alts' - alts)"
proof -
  have A: "x \<in> alts" "y \<in> alts" if "x \<prec>[Pareto(R)] y" for x y
    using that R.Pareto.not_outside unfolding strongly_preferred_def by auto
  have B: "x \<in> alts'" if "x \<in> alts" for x using election that by blast
  from R.nonempty_alts obtain x where x: "x \<in> alts" by blast
  thus ?thesis unfolding pareto_losers_def lift_pref_profile_Pareto_strict_iff [abs_def]
    by (auto dest: A B)
qed

context
begin
private lemma lift_SD_iff_agent:
  assumes "p \<in> lotteries_on alts" "q \<in> lotteries_on alts" and i: "i \<in> agents"
  shows   "p \<preceq>[SD(R' i)] q \<longleftrightarrow> p \<preceq>[SD(R i)] q"
proof -
  from i interpret Ri: preorder_on alts "R i" by simp
  from i election have i': "i \<in> agents'" by blast
  then interpret R'i: preorder_on alts' "R' i" by simp
  from assms election have "p \<in> lotteries_on alts'" "q \<in> lotteries_on alts'"
    by (auto intro: lotteries_on_subset)
  with assms election i' show ?thesis
    by (auto simp: Ri.SD_preorder R'i.SD_preorder 
          preferred_alts_lift_pref_profile lottery_prob_carrier)
qed

private lemma lift_SD_iff_nonagent:
  assumes "p \<in> lotteries_on alts" "q \<in> lotteries_on alts" and i: "i \<in> agents' - agents"
  shows   "p \<preceq>[SD(R' i)] q"
proof -
  from i election have i': "i \<in> agents'" by blast
  then interpret R'i: preorder_on alts' "R' i" by simp
  from assms election have "p \<in> lotteries_on alts'" "q \<in> lotteries_on alts'"
    by (auto intro: lotteries_on_subset)
  with assms election i' show ?thesis
    by (auto simp: R'i.SD_preorder preferred_alts_lift_pref_profile lottery_prob_carrier)
qed

lemmas lift_SD_iff = lift_SD_iff_agent lift_SD_iff_nonagent

lemma lift_SD_iff':
  "p \<in> lotteries_on alts \<Longrightarrow> q \<in> lotteries_on alts \<Longrightarrow> i \<in> agents' \<Longrightarrow>
     p \<preceq>[SD(R' i)] q \<longleftrightarrow> i \<notin> agents \<or> p \<preceq>[SD(R i)] q"
  by (cases "i \<in> agents") (simp_all add: lift_SD_iff)

end

lemma lift_SD_strict_iff:
  assumes "p \<in> lotteries_on alts" "q \<in> lotteries_on alts" and i: "i \<in> agents"
  shows   "p \<prec>[SD(R' i)] q \<longleftrightarrow> p \<prec>[SD(R i)] q"
  using assms by (simp add: strongly_preferred_def lift_SD_iff)

lemma lift_Pareto_SD_iff:
  assumes "p \<in> lotteries_on alts" "q \<in> lotteries_on alts"
  shows   "p \<preceq>[Pareto(SD \<circ> R')] q \<longleftrightarrow> p \<preceq>[Pareto(SD \<circ> R)] q"
  using assms election by (auto simp: R.SD.Pareto_iff R'.SD.Pareto_iff lift_SD_iff')

lemma lift_Pareto_SD_strict_iff:
  assumes "p \<in> lotteries_on alts" "q \<in> lotteries_on alts"
  shows   "p \<prec>[Pareto(SD \<circ> R')] q \<longleftrightarrow> p \<prec>[Pareto(SD \<circ> R)] q"
  using assms by (simp add: strongly_preferred_def lift_Pareto_SD_iff)

lemma lift_SD_efficient_iff:
  assumes p: "p \<in> lotteries_on alts"
  shows   "SD_efficient R' p \<longleftrightarrow> SD_efficient R p"
proof
  assume eff: "SD_efficient R' p"
  have "\<not>(q \<succ>[Pareto(SD \<circ> R)] p)" if q: "q \<in> lotteries_on alts" for q
  proof -
    from q election have q': "q \<in> lotteries_on alts'" by (blast intro: lotteries_on_subset)
    with eff have "\<not>(q \<succ>[Pareto(SD \<circ> R')] p)" by (simp add: R'.SD_efficient_def)
    with p q show ?thesis by (simp add: lift_Pareto_SD_strict_iff)
  qed
  thus "SD_efficient R p" by (simp add: R.SD_efficient_def)
next
  assume eff: "SD_efficient R p"
  have "\<not>(q \<succ>[Pareto(SD \<circ> R')] p)" if q: "q \<in> lotteries_on alts'" for q
  proof
    assume less: "q \<succ>[Pareto(SD \<circ> R')] p"
    from R'.SD_efficient_lottery_exists[OF q] guess q' . note q' = this
    have "x \<notin> set_pmf q'" if x: "x \<in> alts' - alts" for x
    proof -
      from x have "x \<in> pareto_losers R'" by (simp add: pareto_losers_lift_pref_profile)
      with R'.SD_efficient_no_pareto_loser[OF q'(3,1)] show "x \<notin> set_pmf q'" by blast
    qed
    with q' have "q' \<in> lotteries_on alts" by (auto simp: lotteries_on_def)
    moreover from q' less have "q' \<succ>[Pareto(SD \<circ> R')] p" 
      by (auto intro: R'.SD.Pareto.strict_weak_trans)
    with \<open>q' \<in> lotteries_on alts\<close> p have "q' \<succ>[Pareto(SD \<circ> R)] p"
      by (subst (asm) lift_Pareto_SD_strict_iff)
    ultimately have "\<not>SD_efficient R p" by (auto simp: R.SD_efficient_def)
    with eff show False by contradiction
  qed
  thus "SD_efficient R' p" by (simp add: R'.SD_efficient_def)
qed

end


locale sds_lowering = 
  ex_post_efficient_sds agents alts sds
  for agents :: "'agent set" and alts :: "'alt set" and sds +
  fixes agents' alts' 
  assumes agents'_subset: "agents' \<subseteq> agents" and alts'_subset: "alts' \<subseteq> alts"
      and agents'_nonempty [simp]: "agents' \<noteq> {}" and alts'_nonempty [simp]: "alts' \<noteq> {}"
begin

lemma finite_agents' [simp]: "finite agents'"
  using agents'_subset finite_agents by (rule finite_subset)

lemma finite_alts' [simp]: "finite alts'"
  using alts'_subset finite_alts by (rule finite_subset)

abbreviation lift :: "('agent, 'alt) pref_profile \<Rightarrow> ('agent, 'alt) pref_profile" where
  "lift \<equiv> lift_pref_profile agents' alts' agents alts"

definition lowered :: "('agent, 'alt) pref_profile \<Rightarrow> 'alt lottery" where
  "lowered = sds \<circ> lift"

lemma lift_wf [simp, intro]: 
  "pref_profile_wf agents' alts' R \<Longrightarrow> is_pref_profile (lift R)"
  using alts'_subset agents'_subset by (intro lift_pref_profile_wf) simp_all

sublocale lowered: election agents' alts'
  by unfold_locales simp_all

lemma preferred_alts_lift:
  "lowered.is_pref_profile R \<Longrightarrow> i \<in> agents \<Longrightarrow> x \<in> alts \<Longrightarrow>
     preferred_alts (lift R i) x = 
       (if i \<in> agents' \<and> x \<in> alts' then preferred_alts (R i) x else alts)"
  using alts'_subset agents'_subset
  by (intro preferred_alts_lift_pref_profile) simp_all

lemma pareto_losers_lift:
  "lowered.is_pref_profile R \<Longrightarrow> pareto_losers (lift R) = pareto_losers R \<union> (alts - alts')"
  using agents'_subset alts'_subset by (intro pareto_losers_lift_pref_profile) simp_all

lemma lowered_lotteries: "lowered.lotteries \<subseteq> lotteries"
  unfolding lotteries_on_def using alts'_subset by blast

sublocale lowered: social_decision_scheme agents' alts' lowered
proof
  fix R assume R_wf: "pref_profile_wf agents' alts' R"
  from R_wf have R'_wf: "pref_profile_wf agents alts (lift R)" by (rule lift_wf)
  show "lowered R \<in> lowered.lotteries" unfolding lotteries_on_def
  proof safe
    fix x assume "x \<in> set_pmf (lowered R)"
    hence x: "x \<in> set_pmf (sds (lift R))" by (simp add: lowered_def)
    with ex_post_efficient[OF R'_wf]
      have "x \<notin> pareto_losers (lift R)" by blast
    with pareto_losers_lift[OF R_wf]
      have "x \<notin> alts - alts'" by blast
    moreover from x have "x \<in> alts" using sds_wf[OF R'_wf] 
      by (auto simp: lotteries_on_def)
    ultimately show "x \<in> alts'" by simp
  qed
qed

sublocale ex_post_efficient_sds agents' alts' lowered
proof
  fix R assume R_wf: "lowered.is_pref_profile R"
  hence "is_pref_profile (lift R)" by simp
  have "set_pmf (lowered R) \<inter> pareto_losers (lift R) = {}"
    unfolding lowered_def o_def by (intro ex_post_efficient lift_wf R_wf)
  also have "pareto_losers (lift R) = pareto_losers R \<union> (alts - alts')"
    by (intro pareto_losers_lift R_wf)
  finally show "set_pmf (lowered R) \<inter> pareto_losers R = {}" by blast
qed

lemma lowered_in_lotteries [simp]: "lowered.is_pref_profile R \<Longrightarrow> lowered R \<in> lotteries"
  using lowered.sds_wf[of R] lowered_lotteries by blast

end



locale sds_lowering_anonymous =
  anonymous_sds agents alts sds +
  sds_lowering agents alts sds agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and sds agents' alts'
begin

sublocale lowered: anonymous_sds agents' alts' lowered
proof
  fix \<pi> R assume perm: "\<pi> permutes agents'" and R_wf: "lowered.is_pref_profile R"
  from perm have "lift (R \<circ> \<pi>) = lift R \<circ> \<pi>"
    using agents'_subset by (rule lift_pref_profile_permute_agents)
  hence "sds (lift (R \<circ> \<pi>)) = sds (lift R \<circ> \<pi>)" by simp
  also from perm R_wf have "\<pi> permutes agents" "is_pref_profile (lift R)"
    using agents'_subset by (auto dest: permutes_subset)
  from anonymous[OF this] have "sds (lift R \<circ> \<pi>) = sds (lift R)"
    by (simp add: lowered_def)
  finally show "lowered (R \<circ> \<pi>) = lowered R" unfolding lowered_def o_def .
qed

end

locale sds_lowering_neutral =
  neutral_sds agents alts sds +
  sds_lowering agents alts sds agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and sds agents' alts'
begin

sublocale lowered: neutral_sds agents' alts' lowered
proof
  fix \<sigma> R assume perm: "\<sigma> permutes alts'" and R_wf: "lowered.is_pref_profile R"
  from perm alts'_subset 
    have "lift (permute_profile \<sigma> R) = permute_profile \<sigma> (lift R)"
    by (rule lift_pref_profile_permute_alts)
  hence "sds (lift (permute_profile \<sigma> R)) = sds (permute_profile \<sigma> (lift R))" by simp
  also from R_wf perm have "is_pref_profile (lift R)" by simp
  with perm alts'_subset 
    have "sds (permute_profile \<sigma> (lift R)) = map_pmf \<sigma> (sds (lift R))"
    by (intro neutral) (auto intro: permutes_subset)
  finally show "lowered (permute_profile \<sigma> R) = map_pmf \<sigma> (lowered R)"
    by (simp add: lowered_def o_def)
qed

end

locale sds_lowering_sd_efficient =
  sd_efficient_sds agents alts sds +
  sds_lowering agents alts sds agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and sds agents' alts'
begin

sublocale sd_efficient_sds agents' alts' lowered
proof
  fix R assume R_wf: "lowered.is_pref_profile R"
  interpret R: pref_profile_wf agents' alts' R by fact
  from R_wf agents'_subset alts'_subset show "SD_efficient R (lowered R)"
    unfolding lowered_def o_def
    by (subst lift_SD_efficient_iff [symmetric])
       (insert SD_efficient R_wf lowered.sds_wf[OF R_wf], auto simp: lowered_def)
qed

end


locale sds_lowering_strategyproof =
  strategyproof_sds agents alts sds +
  sds_lowering agents alts sds agents' alts'
  for agents :: "'agent set" and alts :: "'alt set" and sds agents' alts'
begin

sublocale strategyproof_sds agents' alts' lowered
proof (unfold_locales, safe)
  fix R i Ri'
  assume R_wf: "lowered.is_pref_profile R" and i: "i \<in> agents'"
  assume Ri': "total_preorder_on alts' Ri'"
  assume manipulable: "lowered.manipulable_profile R i Ri'"
  from i agents'_subset have i': "i \<in> agents" by blast
  interpret R: pref_profile_wf agents' alts' R by fact
  from R_wf interpret liftR: pref_profile_wf agents alts "lift R" by simp

  define lift_Ri'
    where "lift_Ri' x y \<longleftrightarrow> x \<in> alts \<and> y \<in> alts \<and> (x = y \<or> x \<notin> alts' \<or> (y \<in> alts' \<and> Ri' x y))"
    for x y
  define S where "S = (lift R)(i := lift_Ri')"
  from Ri' interpret Ri': total_preorder_on alts' Ri' .
  have wf_lift_Ri': "total_preorder_on alts lift_Ri'" using Ri'.total
    by unfold_locales (auto simp: lift_Ri'_def intro: Ri'.trans)
  from agents'_subset i have S_altdef: "S = lift (R(i := Ri'))"
    by (auto simp: fun_eq_iff lift_pref_profile_def lift_Ri'_def S_def)
  have "lowered (R(i := Ri')) \<in> lowered.lotteries"
    by (intro lowered.sds_wf R.wf_update i Ri')
  hence sds_S_wf: "sds S \<in> lowered.lotteries" by (simp add: S_altdef lowered_def)

  from manipulable have "lowered R \<prec>[SD (R i)] sds (lift (R(i := Ri')))"
    unfolding lowered.manipulable_profile_def by (simp add: lowered_def)
  also note S_altdef [symmetric]
  finally have "lowered R \<prec>[SD (lift R i)] sds S"
    using R_wf i lowered.sds_wf[OF R_wf] sds_S_wf
      by (subst lift_SD_strict_iff) (simp_all add: agents'_subset alts'_subset)
  hence "manipulable_profile (lift R) i lift_Ri'"
    by (simp add: manipulable_profile_def lowered_def S_def)
  with strategyproof[OF lift_wf[OF R_wf] i' wf_lift_Ri'] show False by contradiction
qed

end


locale sds_lowering_anonymous_neutral_sdeff_stratproof =
  sds_lowering_anonymous + sds_lowering_neutral + 
  sds_lowering_sd_efficient + sds_lowering_strategyproof

end
