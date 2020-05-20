section \<open>The Observing Quorums Model\<close>

theory Observing_Quorums
imports Same_Vote
begin

subsection \<open>Model definition\<close>
(******************************************************************************)

text \<open>The state adds one field to the Voting model state:\<close>
record obsv_state = v_state +
  obs :: "round \<Rightarrow> (process, val) map"

text \<open>For the observation mechanism to work, we need monotonicity of quorums.\<close>
context mono_quorum begin

definition obs_safe 
  where
  "obs_safe r s v \<equiv> (\<forall>r' < r. \<exists>p. obs s r' p \<in> {None, Some v})"

definition obsv_round 
  :: "round \<Rightarrow> process set \<Rightarrow> val \<Rightarrow> (process, val)map \<Rightarrow> process set \<Rightarrow> (obsv_state \<times> obsv_state) set" 
  where
  "obsv_round r S v r_decisions Os = {(s, s').
     \<comment> \<open>guards\<close>
     r = next_round s
     \<and> (S \<noteq> {} \<longrightarrow> obs_safe r s v)
     \<and> d_guard r_decisions (const_map v S)
     \<and> (S \<in> Quorum \<longrightarrow> Os = UNIV)
     \<and> (Os \<noteq> {} \<longrightarrow> S \<noteq> {})
     \<and> \<comment> \<open>actions\<close>
     s' = s\<lparr> 
       next_round := Suc r
       , votes := (votes s)(r := const_map v S)
       , decisions := decisions s ++ r_decisions
       , obs := (obs s)(r := const_map v Os)
     \<rparr>
  }"

definition obsv_trans :: "(obsv_state \<times> obsv_state) set" where
  "obsv_trans = (\<Union>r S v d_f Os. obsv_round r S v d_f Os) \<union> Id"

definition obsv_init :: "obsv_state set" where
  "obsv_init = { \<lparr> next_round = 0, votes = \<lambda>r a. None, decisions = Map.empty, obs = \<lambda>r a. None \<rparr> }"  

definition obsv_TS :: "obsv_state TS" where
  "obsv_TS = \<lparr> init = obsv_init, trans = obsv_trans \<rparr>"

lemmas obsv_TS_defs = obsv_TS_def obsv_init_def obsv_trans_def


subsection \<open>Invariants\<close>
(******************************************************************************)

definition OV_inv1 where
  "OV_inv1 = {s. \<forall>r Q v. quorum_for Q v (votes s r) \<longrightarrow>
    (\<forall>Q' \<in> Quorum. quorum_for Q' v (obs s r))}"

lemmas OV_inv1I = OV_inv1_def [THEN setc_def_to_intro, rule_format]
lemmas OV_inv1E [elim] = OV_inv1_def [THEN setc_def_to_elim, rule_format]
lemmas OV_inv1D = OV_inv1_def [THEN setc_def_to_dest, rule_format]
 
subsubsection \<open>Proofs of invariants\<close>
(******************************************************************************)
  
lemma OV_inv1_obsv_round: 
  "{OV_inv1} obsv_round r S v d_f Ob {> OV_inv1}"
proof(clarsimp simp add: PO_hoare_defs intro!: OV_inv1I)
  fix v' s s' Q Q' r'
  assume 
    Q: "quorum_for Q v' (votes s' r')"  
    and inv: "s \<in> OV_inv1"
    and step: "(s, s') \<in> obsv_round r S v d_f Ob"
    and quorum: "Q' \<in> Quorum"
  from Q inv[THEN OV_inv1D] step quorum
  show "quorum_for Q' v' (obs s' r')"
  proof(cases "r'=r")
    case True
    with step and Q have "S \<in> Quorum"
      by(fastforce simp add: obsv_round_def obs_safe_def quorum_for_def const_map_is_Some
        ball_conj_distrib subset_eq[symmetric] intro: mono_quorum[where Q'=S])      
    thus ?thesis using step inv[THEN OV_inv1D] Q quorum
      by(clarsimp simp add: obsv_round_def obs_safe_def quorum_for_def const_map_is_Some
        ball_conj_distrib subset_eq[symmetric] dest!: quorum_non_empty)
  qed(clarsimp simp add: obsv_round_def obs_safe_def quorum_for_def)
qed

lemma OV_inv1_inductive:
  "init obsv_TS \<subseteq> OV_inv1" 
  "{OV_inv1} trans obsv_TS {> OV_inv1}" 
  apply (simp add: obsv_TS_defs OV_inv1_def) 
   apply (auto simp add: obsv_TS_defs OV_inv1_obsv_round quorum_for_def dest: empty_not_quorum)
  done

lemma quorum_for_const_map:
  "(quorum_for Q w (const_map v S)) = (Q \<in> Quorum \<and> Q \<subseteq> S \<and> w = v)"
  by(auto simp add: quorum_for_def const_map_is_Some dest: quorum_non_empty)

subsection \<open>Refinement\<close>
(******************************************************************************)

definition obsv_ref_rel where 
  "obsv_ref_rel \<equiv> {(sa, sc).
    sa = v_state.truncate sc
  }"

lemma obsv_round_refines:
  "{obsv_ref_rel \<inter> UNIV \<times> OV_inv1} sv_round r S v dec_f, obsv_round r S v dec_f Ob {> obsv_ref_rel}"
  apply(clarsimp simp add: PO_rhoare_defs sv_round_def obsv_round_def safe_def obsv_ref_rel_def 
    v_state.truncate_def obs_safe_def quorum_for_def OV_inv1_def)
  by (metis UNIV_I UNIV_quorum  option.distinct(1) option.inject)

lemma Observable_Refines:
  "PO_refines (obsv_ref_rel \<inter> UNIV \<times> OV_inv1) sv_TS obsv_TS"
proof(rule refine_using_invariants)
  show "init obsv_TS \<subseteq> obsv_ref_rel `` init sv_TS"
  by(auto simp add: PO_refines_def sv_TS_defs  obsv_TS_defs  obsv_ref_rel_def 
    v_state.truncate_def)
next
  show "{obsv_ref_rel \<inter> UNIV \<times> OV_inv1} trans sv_TS, trans obsv_TS {> obsv_ref_rel}"
    by(auto simp add: PO_refines_def sv_TS_defs  obsv_TS_defs intro!: 
      obsv_round_refines relhoare_refl)
qed(auto intro: OV_inv1_inductive del: subsetI)

subsection \<open>Additional invariants\<close>
(******************************************************************************)

definition OV_inv2 where
  "OV_inv2 = {s. \<forall>r \<ge> next_round s. obs s r = Map.empty }"

lemmas OV_inv2I = OV_inv2_def [THEN setc_def_to_intro, rule_format]
lemmas OV_inv2E [elim] = OV_inv2_def [THEN setc_def_to_elim, rule_format]
lemmas OV_inv2D = OV_inv2_def [THEN setc_def_to_dest, rule_format]

definition OV_inv3 where
  "OV_inv3 = {s. \<forall>r p v. obs s r p = Some v \<longrightarrow>
    obs_safe r s v}"

lemmas OV_inv3I = OV_inv3_def [THEN setc_def_to_intro, rule_format]
lemmas OV_inv3E [elim] = OV_inv3_def [THEN setc_def_to_elim, rule_format]
lemmas OV_inv3D = OV_inv3_def [THEN setc_def_to_dest, rule_format]

definition OV_inv4 where
  "OV_inv4 = {s. \<forall>r p q v w. obs s r p = Some v \<and> obs s r q = Some w \<longrightarrow>
    w = v}"

lemmas OV_inv4I = OV_inv4_def [THEN setc_def_to_intro, rule_format]
lemmas OV_inv4E [elim] = OV_inv4_def [THEN setc_def_to_elim, rule_format]
lemmas OV_inv4D = OV_inv4_def [THEN setc_def_to_dest, rule_format]


subsubsection \<open>Proofs of additional invariants\<close>
(******************************************************************************)

lemma OV_inv2_inductive:
  "init obsv_TS \<subseteq> OV_inv2"
  "{OV_inv2} trans obsv_TS {> OV_inv2}" 
  by(auto simp add: PO_hoare_defs OV_inv2_def obsv_TS_defs obsv_round_def const_map_is_Some)

lemma SVinv3_inductive:
  "init obsv_TS \<subseteq> SV_inv3"
  "{SV_inv3} trans obsv_TS {> SV_inv3}" 
  by(auto simp add: PO_hoare_defs SV_inv3_def obsv_TS_defs obsv_round_def const_map_is_Some)

lemma OV_inv3_obsv_round: 
  "{OV_inv3 \<inter> OV_inv2} obsv_round r S v D Ob {> OV_inv3}"
proof(clarsimp simp add: PO_hoare_defs intro!: OV_inv3I)
  fix s s' r_w p w
  assume Assms:
    "obs s' r_w p = Some w" 
    "s \<in> OV_inv3"
    "(s, s') \<in> obsv_round r S v D Ob"
    "s \<in> OV_inv2"
  hence "s' \<in> OV_inv2"
    by(force simp add: obsv_TS_defs intro: OV_inv2_inductive(2)[THEN hoareD, OF \<open>s \<in> OV_inv2\<close>])
  hence "r_w \<le> next_round s'" using Assms
    by(auto simp add: OV_inv2_def intro!: leI)
  hence r_w_le: "r_w \<le> next_round s" using Assms
    by(auto simp add: obsv_round_def le_Suc_eq)
  show "obs_safe r_w s' w"
  proof(cases "r_w = next_round s")
    case True
    thus ?thesis using Assms
      by(auto simp add: obsv_round_def const_map_is_Some obs_safe_def)
  next
    case False
    hence "r_w < next_round s" using r_w_le
      by(metis less_le)
    moreover have "\<forall>r'. r' \<noteq> next_round s \<longrightarrow> obs s' r' = obs s r'" using Assms(3)
      by(auto simp add: obsv_round_def)
    ultimately have 
      "\<forall>r' \<le> r_w. obs s' r' = obs s r'"
      by(auto)
    thus ?thesis using Assms
      by(auto simp add: OV_inv3_def obs_safe_def)
  qed
qed

lemma OV_inv3_inductive:
  "init obsv_TS \<subseteq> OV_inv3"
  "{OV_inv3 \<inter> OV_inv2} trans obsv_TS {> OV_inv3}" 
  apply(auto simp add: obsv_TS_def obsv_trans_def intro: OV_inv3_obsv_round)
  apply(auto simp add: obsv_init_def OV_inv3_def)
  done

lemma OV_inv4_inductive:
  "init obsv_TS \<subseteq> OV_inv4"
  "{OV_inv4} trans obsv_TS {> OV_inv4}" 
  by(auto simp add: PO_hoare_defs OV_inv4_def obsv_TS_defs obsv_round_def const_map_is_Some)

end

end
