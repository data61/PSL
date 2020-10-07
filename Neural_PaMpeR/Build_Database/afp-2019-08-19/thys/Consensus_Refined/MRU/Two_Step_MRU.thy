section \<open>Two-step Optimized MRU Model\<close>
theory Two_Step_MRU
imports "../MRU_Vote_Opt" "../Two_Steps"
begin

text \<open>To make the coming proofs of concrete algorithms easier, in this model we split 
  the @{term opt_mru_round} into two steps\<close>

context mono_quorum
begin                    

subsection \<open>Model definition\<close>
(******************************************************************************)

definition opt_mru_step0 :: "round \<Rightarrow> process set \<Rightarrow> process set \<Rightarrow> val \<Rightarrow>  (opt_mru_state \<times> opt_mru_state) set" where
  "opt_mru_step0 r Q S v = {(s, s').
     (* guards *)
     r = next_round s \<and> two_step r = 0
     \<and> (S = {} \<or> opt_mru_guard (mru_vote s) Q v)
     \<and> (* actions *)
     s' = s\<lparr> 
       mru_vote := mru_vote s ++ const_map (two_phase r, v) S
       , next_round := Suc r
     \<rparr>
  }"

definition r_votes :: "opt_mru_state \<Rightarrow> round \<Rightarrow> (process, val)map" where
  "r_votes s r \<equiv> \<lambda>p. if (\<exists>v. mru_vote s p = Some (two_phase r, v))
        then map_option snd (mru_vote s p)
        else None"

definition opt_mru_step1 :: "round \<Rightarrow> (process, val)map \<Rightarrow> (opt_mru_state \<times> opt_mru_state) set" where
  "opt_mru_step1 r dec_f = {(s, s').
     (* guards *)
     r = next_round s \<and> two_step r = 1
     \<and> d_guard dec_f (r_votes s r)
     \<and> (* actions *)
     s' = s\<lparr> 
       next_round := Suc r
       , decisions := decisions s ++ dec_f
     \<rparr>
  }"

lemmas ts_lv_evt_defs = opt_mru_step0_def opt_mru_step1_def opt_mru_guard_def

definition ts_lv_trans :: "(opt_mru_state \<times> opt_mru_state) set" where
  "ts_lv_trans = (\<Union>r Q S v. opt_mru_step0 r Q S v) \<union> (\<Union>r dec_f. opt_mru_step1 r dec_f) \<union> Id"

definition ts_lv_TS :: "opt_mru_state TS" where
  "ts_lv_TS = \<lparr> init = opt_mru_init, trans = ts_lv_trans \<rparr>"

lemmas ts_lv_TS_defs = ts_lv_TS_def opt_mru_init_def ts_lv_trans_def

subsection \<open>Refinement\<close>
(******************************************************************************)

definition basic_rel where
  "basic_rel \<equiv> {(sa, sc).    
    decisions sc = decisions sa
    \<and> next_round sa = two_phase (next_round sc)
  }"

definition two_step0_rel :: "(opt_mru_state \<times> opt_mru_state)set" where
  "two_step0_rel \<equiv> basic_rel \<inter> {(sa, sc).    
    two_step (next_round sc) = 0
    \<and> mru_vote sc = mru_vote sa
  }"

definition two_step1_rel :: "(opt_mru_state \<times> opt_mru_state)set"  where
  "two_step1_rel \<equiv> basic_rel \<inter> {(sa, sc).
    (\<exists>sc' r Q S v. (sa, sc') \<in> two_step0_rel \<and> (sc', sc) \<in> opt_mru_step0 r Q S v)
  }"

definition ts_ref_rel where
  "ts_ref_rel = {(sa, sc).
    (two_step (next_round sc) = 0 \<longrightarrow> (sa, sc) \<in> two_step0_rel)
    \<and> (two_step (next_round sc) = 1 \<longrightarrow> (sa, sc) \<in> two_step1_rel)
  }"

lemmas ts_ref_rel_defs = 
  basic_rel_def
  ts_ref_rel_def
  two_step0_rel_def
  two_step1_rel_def


lemma step0_ref:
  "{ts_ref_rel} Id, opt_mru_step0 r Q S v {> ts_ref_rel}"
  apply(auto simp only: PO_rhoare_defs)
  apply(auto simp add: ts_ref_rel_def opt_mru_step0_def two_step_phase_Suc two_step1_rel_def)
  apply(auto simp add: two_step0_rel_def basic_rel_def two_step_phase_Suc)
  done

lemma step1_ref:
  "{ts_ref_rel \<inter> OMRU_inv1 \<times> UNIV} 
    \<Union>r' Q S' v dec_f'. opt_mru_round r' Q S' v dec_f', 
    opt_mru_step1 r dec_f {> ts_ref_rel}"
proof(auto simp only: PO_rhoare_defs)
  fix sa sc1 sc2
  assume 
    ainv: "sa \<in> OMRU_inv1"
    and R: "(sa, sc1) \<in> ts_ref_rel"
    and step1: "(sc1, sc2) \<in> opt_mru_step1 r dec_f"

  then obtain sc0 r0 S0 Q v where
    R0: "(sa, sc0) \<in> two_step0_rel" and step0: "(sc0, sc1) \<in> opt_mru_step0 r0 Q S0 v"
    by(auto simp add: ts_ref_rel_def two_step1_rel_def opt_mru_step1_def)

  have R1: "(sa, sc1) \<in> two_step1_rel" 
    and r1_step: "two_step (next_round sc1) = Suc 0" 
    and r2_step: "two_step (next_round sc2) = 0"
    using R step1
    by(auto simp add: ts_ref_rel_def opt_mru_step1_def two_step_phase_Suc)

  have r: "r = Suc r0" and r0: "r0 = next_round sc0" and r0_step: "two_step r0 = 0" and 
    r1: "r = next_round sc1" 
    using step0 step1
    by(auto simp add: opt_mru_step0_def opt_mru_step1_def)

  have abs_round1: "next_round sa = two_phase r" using R1 r1
    by(auto simp add: two_step1_rel_def basic_rel_def)
  have abs_round0: "next_round sa = two_phase r0" using R0 r0 r
    by(auto simp add: two_step0_rel_def basic_rel_def two_step_phase_Suc)

  have r_votes: "r_votes sc1 r = const_map v S0"
  proof(rule ext)
    fix p
    show "r_votes sc1 r p = const_map v S0 p"
    proof(cases "r_votes sc1 r p")
      case None
      thus ?thesis using step0 abs_round0 abs_round1
        by(auto simp add: r_votes_def opt_mru_step0_def
          const_map_def restrict_map_def map_add_def)
    next
      case (Some w)
      hence in_S0: "mru_vote sc0 p \<noteq> mru_vote sc1 p" using R0 step0 ainv r1_step r abs_round0
        by(auto simp add: r_votes_def ts_ref_rel_defs
          two_step_phase_Suc opt_mru_step0_def dest: OMRU_inv1D[where p=p])
      hence "p \<in> S0"  using step0
        by(auto simp add: opt_mru_step0_def map_add_def const_map_is_Some 
          split: option.split_asm)
      moreover have "w=v" using R0 step0 ainv r1_step r abs_round0 Some
        by(auto simp add: r_votes_def ts_ref_rel_defs const_map_is_Some
          two_step_phase_Suc opt_mru_step0_def dest: OMRU_inv1D[where p=p])
      ultimately show ?thesis using Some
        by(auto simp add: const_map_def)
    qed
  qed
    
  define sa' where "sa' = sa\<lparr>
      mru_vote := mru_vote sa ++ const_map (two_phase r, v) S0
      , next_round := Suc (two_phase r)
      , decisions := decisions sa ++ dec_f
    \<rparr>"
  
  have "(sa, sa') \<in> opt_mru_round (two_phase r) Q S0 v dec_f \<and> (sa', sc2) \<in> ts_ref_rel"
  proof
    show "(sa', sc2) \<in> ts_ref_rel" using r2_step R0 step0 step1
      by(auto simp add: ts_ref_rel_def two_step0_rel_def basic_rel_def opt_mru_step0_def opt_mru_step1_def 
        sa'_def two_step_phase_Suc)
  next
    show "(sa, sa') \<in> opt_mru_round (two_phase r) Q S0 v dec_f" 
      using R0 r0_step r1_step step0 step1 r0 r1 r r_votes
      by(auto simp add: ts_ref_rel_defs opt_mru_round_def two_step_phase_Suc
        opt_mru_step0_def opt_mru_step1_def sa'_def)
  qed
  thus "\<exists>y. (sa, y) \<in> (\<Union>r' Q S' v D'. opt_mru_round r' Q S' v D') \<and> (y, sc2) \<in> ts_ref_rel"
    by blast
qed  

lemma TwoStep_Coordinated_Refines:
  "PO_refines (ts_ref_rel \<inter> OMRU_inv1 \<times> UNIV) 
    lv_TS ts_lv_TS"
proof(rule refine_using_invariants)
  show "init ts_lv_TS \<subseteq> ts_ref_rel `` init lv_TS"
    by(auto simp add: ts_lv_TS_defs lv_TS_def ts_ref_rel_def two_step0_rel_def two_step1_rel_def
      basic_rel_def)
next
  show 
    "{ts_ref_rel \<inter> OMRU_inv1 \<times> UNIV} TS.trans lv_TS, 
      TS.trans (ts_lv_TS) {> ts_ref_rel}"
    apply(simp add: lv_TS_defs ts_lv_TS_defs)
    apply(auto simp add: ts_lv_trans_def intro!: step0_ref step1_ref)
    done
qed(auto intro!: OMRU_inv1_inductive)

subsection \<open>Invariants\<close>
(******************************************************************************)

definition TS_OMRU_inv1 where
  "TS_OMRU_inv1 \<equiv> {s. 
    (two_step (next_round s) = 0 \<longrightarrow> 
      (\<forall>p \<Phi> v. mru_vote s p = Some (\<Phi>, v) \<longrightarrow> \<Phi> < two_phase (next_round s)))
    \<and> (two_step (next_round s) = 1 \<longrightarrow> 
      (\<forall>p \<Phi> v. mru_vote s p = Some (\<Phi>, v) \<longrightarrow> \<Phi> \<le> two_phase (next_round s)))
  }"

lemma two_step_neqD: 
  "two_step x \<noteq> Suc 0 \<Longrightarrow> two_step x = 0"
  "0 < two_step x \<Longrightarrow> two_step x = Suc 0"
  by(auto simp add: two_step_def)

lemma TS_OMRU_inv1_inductive:
  "init ts_lv_TS \<subseteq> TS_OMRU_inv1"
  "{TS_OMRU_inv1} trans ts_lv_TS {> TS_OMRU_inv1}"
  apply(fastforce simp add: PO_hoare_defs ts_lv_TS_def opt_mru_init_def TS_OMRU_inv1_def)[1]
  apply(auto simp add: PO_hoare_defs ts_lv_TS_def ts_lv_trans_def opt_mru_step0_def opt_mru_step1_def)
  apply(auto simp add: TS_OMRU_inv1_def two_step_phase_Suc const_map_is_Some const_map_is_None
    less_Suc_eq_le dest: less_imp_le)
  done

end

end
