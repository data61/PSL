section \<open>Two-Step Observing Quorums Model\<close>

theory Two_Step_Observing
imports "../Observing_Quorums_Opt" "../Two_Steps"
begin

text \<open>To make the coming proofs of concrete algorithms easier, in this model we split 
  the @{term olv_round} into two steps.\<close>

subsection \<open>Model definition\<close>
(******************************************************************************)
record tso_state = opt_obsv_state +
  r_votes :: "process \<Rightarrow> val option"

context mono_quorum
begin

definition tso_round0 
  :: "round \<Rightarrow> process set \<Rightarrow> val \<Rightarrow> (tso_state \<times> tso_state)set"
  where
  "tso_round0 r S v \<equiv> {(s, s').
    \<comment> \<open>guards\<close>
    r = next_round s
    \<and> two_step r = 0
    \<and> (S \<noteq> {} \<longrightarrow> opt_obs_safe (last_obs s) v)
    \<comment> \<open>actions\<close>
    \<and> s' = s\<lparr>
      next_round := Suc r
      , r_votes := const_map v S
    \<rparr>
  }"

definition obs_guard :: "(process, val)map \<Rightarrow> (process, val)map \<Rightarrow> bool" where
  "obs_guard r_obs r_v \<equiv> \<forall>p.
    (\<forall>v. r_obs p = Some v \<longrightarrow> (\<exists>q. r_v q = Some v))
    \<and> (dom r_v \<in> Quorum \<longrightarrow> (\<exists>q \<in> dom r_v. r_obs p = r_v q))"

definition tso_round1 
  :: "round \<Rightarrow> (process, val)map \<Rightarrow> (process, val)map \<Rightarrow> (tso_state \<times> tso_state)set" 
  where
  "tso_round1 r r_decisions r_obs \<equiv> {(s, s').
    \<comment> \<open>guards\<close>
    r = next_round s
    \<and> two_step r = 1
    \<and> d_guard r_decisions (r_votes s)
    \<and> obs_guard r_obs (r_votes s)
    \<comment> \<open>actions\<close>
    \<and> s' = s\<lparr>
      next_round := Suc r
      , decisions := decisions s ++ r_decisions
      , last_obs := last_obs s ++ r_obs
    \<rparr>
  }"

definition tso_init where
  "tso_init = { \<lparr> next_round = 0, decisions = Map.empty, last_obs = Map.empty, r_votes = Map.empty \<rparr> }"

definition tso_trans :: "(tso_state \<times> tso_state) set" where
  "tso_trans = (\<Union>r S v. tso_round0 r S v) \<union> (\<Union>r d_f o_f. tso_round1 r d_f o_f) \<union> Id"

definition tso_TS :: "tso_state TS" where
  "tso_TS = \<lparr> init = tso_init, trans = tso_trans \<rparr>"

lemmas tso_TS_defs = tso_TS_def tso_init_def tso_trans_def

subsection \<open>Refinement\<close>
(******************************************************************************)

definition basic_rel :: "(opt_obsv_state \<times> tso_state)set" where
  "basic_rel = {(sa, sc).
    next_round sa = two_phase (next_round sc)
    \<and> last_obs sc = last_obs sa
    \<and> decisions sc = decisions sa
  }"

definition step0_rel :: "(opt_obsv_state \<times> tso_state)set" where
  "step0_rel = basic_rel"

definition step1_add_rel :: "(opt_obsv_state \<times> tso_state)set" where
  "step1_add_rel = {(sa, sc). \<exists>S v.
    r_votes sc = const_map v S
    \<and> (S \<noteq> {} \<longrightarrow> opt_obs_safe (last_obs sc) v)
  }"

definition step1_rel :: "(opt_obsv_state \<times> tso_state)set" where
  "step1_rel = basic_rel \<inter> step1_add_rel"

definition tso_ref_rel :: "(opt_obsv_state \<times> tso_state)set" where
  "tso_ref_rel \<equiv> {(sa, sc).
    (two_step (next_round sc) = 0 \<longrightarrow> (sa, sc) \<in> step0_rel)
    \<and> (two_step (next_round sc) = 1 \<longrightarrow> 
        (sa, sc) \<in> step1_rel
        \<and> (\<exists>sc' r S v. (sc', sc) \<in> tso_round0 r S v \<and> (sa, sc') \<in> step0_rel))
  }"

lemma const_map_equality:
  "(const_map v S = const_map v' S') = (S = S' \<and> (S = {} \<or> v = v'))"
  apply(simp add: const_map_def restrict_map_def)
  by (metis equals0D option.distinct(2) option.inject subsetI subset_antisym)

lemma rhoare_skipI:
  "\<lbrakk> \<And>sa sc sc'. \<lbrakk> (sa, sc) \<in> Pre; (sc, sc') \<in> Tc \<rbrakk> \<Longrightarrow> (sa, sc') \<in> Post \<rbrakk> \<Longrightarrow> {Pre} Id, Tc {>Post}"
  by(auto simp add: PO_rhoare_defs)

lemma tso_round0_refines:
  "{tso_ref_rel} Id, tso_round0 r S v {>tso_ref_rel}"
  apply(rule rhoare_skipI)
  apply(auto simp add: tso_ref_rel_def basic_rel_def step1_rel_def 
     step1_add_rel_def  step0_rel_def tso_round0_def const_map_equality conj_disj_distribR
     ex_disj_distrib two_step_phase_Suc)
  done

lemma tso_round1_refines:
  "{tso_ref_rel} \<Union>r S v dec_f Ob. olv_round r S v dec_f Ob, tso_round1 r dec_f o_f {>tso_ref_rel}"
proof(clarsimp simp add: PO_rhoare_defs)
  fix sa sc and sc'
  assume
    R: "(sa, sc) \<in> tso_ref_rel" 
    and step1: "(sc, sc') \<in> tso_round1 r dec_f o_f"

  hence step_r: "two_step r = 1" and r_next: "next_round sc = r" by (auto simp add: tso_round1_def)
  then obtain r0 sc0 S0 v0 where 
    R0: "(sa, sc0) \<in> step0_rel" and step0: "(sc0, sc) \<in> tso_round0 r0 S0 v0"
    using R
    by(auto simp add: tso_ref_rel_def) 

  from step_r r_next R obtain S v where
    v: "r_votes sc = const_map v S"
    and safe: "S \<noteq> {} \<longrightarrow> opt_obs_safe (last_obs sc) v"
    by(auto simp add: tso_ref_rel_def step1_rel_def step1_add_rel_def)

  define sa' where "sa' = sa\<lparr> 
      next_round := Suc (next_round sa)
      , decisions := decisions sa ++ dec_f
      , last_obs := last_obs sa ++ const_map v (dom o_f)
    \<rparr>"

  have "S \<in> Quorum \<longrightarrow> dom o_f = UNIV" using step1 v
    by(auto simp add: tso_round1_def obs_guard_def const_map_def)
  moreover have "o_f \<noteq> Map.empty \<longrightarrow> S \<noteq> {}" using step1 v
    by(auto simp add: tso_round1_def obs_guard_def dom_const_map)
  ultimately have 
    abs_step: 
    "(sa, sa') \<in> olv_round (next_round sa) S v dec_f (dom o_f)" using R safe v step_r r_next step1
    by(clarsimp simp add: tso_ref_rel_def step1_rel_def basic_rel_def sa'_def 
      olv_round_def tso_round1_def)

  from v have post_rel: "(sa', sc') \<in> tso_ref_rel" using R step1
    apply(clarsimp simp add: tso_round0_def tso_round1_def 
      step0_rel_def basic_rel_def  sa'_def tso_ref_rel_def two_step_phase_Suc o_def
      const_map_is_Some const_map_is_None const_map_equality obs_guard_def 
      intro!: arg_cong2[where f=map_add, OF refl])
    apply(auto simp add: const_map_def restrict_map_def intro!: ext)
    done

  from abs_step post_rel show 
    "\<exists>sa'. (\<exists>r' S' w dec_f' Ob'. (sa, sa') \<in> olv_round r' S' w dec_f' Ob') \<and> (sa', sc') \<in> tso_ref_rel"
    by blast
qed
  
lemma TS_Observing_Refines:
  "PO_refines tso_ref_rel olv_TS tso_TS"
  apply(auto simp add: PO_refines_def olv_TS_defs tso_TS_defs 
    intro!: tso_round0_refines tso_round1_refines)
  apply(auto simp add: tso_ref_rel_def step0_rel_def basic_rel_def tso_init_def quorum_for_def 
    dest: empty_not_quorum)
  done

subsection \<open>Invariants\<close>
(******************************************************************************)

definition TSO_inv1 where
  "TSO_inv1 = {s. two_step (next_round s) = Suc 0 \<longrightarrow>
    (\<exists>v. \<forall>p w. r_votes s p = Some w \<longrightarrow> w = v)}"

lemmas TSO_inv1I = TSO_inv1_def [THEN setc_def_to_intro, rule_format]
lemmas TSO_inv1E [elim] = TSO_inv1_def [THEN setc_def_to_elim, rule_format]
lemmas TSO_inv1D = TSO_inv1_def [THEN setc_def_to_dest, rule_format]

definition TSO_inv2 where
  "TSO_inv2 = {s. two_step (next_round s) = Suc 0 \<longrightarrow>
    (\<forall>p v. (r_votes s p = Some v \<longrightarrow> (\<exists>q. last_obs s q \<in> {None, Some v})))}"

lemmas TSO_inv2I = TSO_inv2_def [THEN setc_def_to_intro, rule_format]
lemmas TSO_inv2E [elim] = TSO_inv2_def [THEN setc_def_to_elim, rule_format]
lemmas TSO_inv2D = TSO_inv2_def [THEN setc_def_to_dest, rule_format]

subsubsection \<open>Proofs of invariants\<close>
(******************************************************************************)

lemma TSO_inv1_inductive:
  "init tso_TS \<subseteq> TSO_inv1"
  "{TSO_inv1} TS.trans tso_TS {> TSO_inv1}"
  by(auto simp add: TSO_inv1_def tso_TS_defs PO_hoare_def 
    tso_round0_def tso_round1_def const_map_is_Some two_step_phase_Suc)
  
lemma TSO_inv1_invariant:
  "reach tso_TS \<subseteq> TSO_inv1"
  by(intro inv_rule_basic TSO_inv1_inductive)

lemma TSO_inv2_inductive:
  "init tso_TS \<subseteq> TSO_inv2"
  "{TSO_inv2} TS.trans tso_TS {> TSO_inv2}"
  by(auto simp add: TSO_inv2_def tso_TS_defs PO_hoare_def 
    opt_obs_safe_def tso_round0_def tso_round1_def const_map_is_Some two_step_phase_Suc)
  
lemma TSO_inv2_invariant:
  "reach tso_TS \<subseteq> TSO_inv2"
  by(intro inv_rule_basic TSO_inv2_inductive)

end

end
