section \<open>Three-step Optimized MRU Model\<close>
theory Three_Step_MRU
imports "../MRU_Vote_Opt" Three_Steps
begin            

text \<open>To make the coming proofs of concrete algorithms easier, in this model we split 
  the @{term opt_mru_round} into three steps\<close>

subsection \<open>Model definition\<close>
(******************************************************************************)
record three_step_mru_state = opt_mru_state + 
  candidates :: "val set"

context mono_quorum
begin                    

definition opt_mru_step0 :: "round \<Rightarrow> val set \<Rightarrow>  (three_step_mru_state \<times> three_step_mru_state) set" where
  "opt_mru_step0 r C = {(s, s').
     \<comment> \<open>guards\<close>
     r = next_round s \<and> three_step r = 0
     \<and> (\<forall>cand \<in> C. \<exists>Q. opt_mru_guard (mru_vote s) Q cand)
     \<and> \<comment> \<open>actions\<close>
     s' = s\<lparr> 
       candidates := C
       , next_round := Suc r
     \<rparr>
  }"

definition opt_mru_step1 :: "round \<Rightarrow> process set \<Rightarrow> val \<Rightarrow> 
  (three_step_mru_state \<times> three_step_mru_state) set" where
  "opt_mru_step1 r S v = {(s, s').
     \<comment> \<open>guards\<close>
     r = next_round s \<and> three_step r = 1
     \<and> (S \<noteq> {} \<longrightarrow> v \<in> candidates s)
     \<and> \<comment> \<open>actions\<close>
     s' = s\<lparr> 
       mru_vote := mru_vote s ++ const_map (three_phase r, v) S
       , next_round := Suc r
     \<rparr>
  }"

definition step2_d_guard :: "(process, val)map \<Rightarrow> (process, val)map \<Rightarrow> bool" where
  "step2_d_guard r_decisions r_votes \<equiv> \<forall>p v. r_decisions p = Some v \<longrightarrow> 
      v \<in> ran r_votes \<and> dom r_votes \<in> Quorum"

definition r_votes :: "three_step_mru_state \<Rightarrow> round \<Rightarrow> (process, val)map" where
  "r_votes s r \<equiv> \<lambda>p. if (\<exists>v. mru_vote s p = Some (three_phase r, v))
        then map_option snd (mru_vote s p)
        else None"

definition opt_mru_step2 :: "round \<Rightarrow> (process, val)map \<Rightarrow> (three_step_mru_state \<times> three_step_mru_state) set" where
  "opt_mru_step2 r r_decisions = {(s, s').
     \<comment> \<open>guards\<close>
     r = next_round s \<and> three_step r = 2
     \<and> step2_d_guard r_decisions  (r_votes s r)
     \<and> \<comment> \<open>actions\<close>
     s' = s\<lparr> 
       next_round := Suc r
       , decisions := decisions s ++ r_decisions
     \<rparr>
  }"

lemmas ts_mru_evt_defs = opt_mru_step0_def opt_mru_step1_def opt_mru_guard_def

definition ts_mru_trans :: "(three_step_mru_state \<times> three_step_mru_state) set" where
  "ts_mru_trans = (\<Union>r C. opt_mru_step0 r C) 
      \<union> (\<Union>r S v. opt_mru_step1 r S v)
      \<union> (\<Union>r dec_f. opt_mru_step2 r dec_f) \<union> Id"

definition ts_mru_init where
  "ts_mru_init = { \<lparr> next_round = 0, mru_vote = Map.empty, decisions = Map.empty, candidates = {} \<rparr> }"

definition ts_mru_TS :: "three_step_mru_state TS" where
  "ts_mru_TS = \<lparr> init = ts_mru_init, trans = ts_mru_trans \<rparr>"

lemmas ts_mru_TS_defs = ts_mru_TS_def ts_mru_init_def ts_mru_trans_def

subsection \<open>Refinement\<close>
(******************************************************************************)

definition basic_rel where
  "basic_rel \<equiv> {(sa, sc).    
    decisions sc = decisions sa
    \<and> next_round sa = three_phase (next_round sc)
  }"

definition three_step0_rel :: "(opt_mru_state \<times> three_step_mru_state)set" where
  "three_step0_rel \<equiv> basic_rel \<inter> {(sa, sc).    
    three_step (next_round sc) = 0
    \<and> mru_vote sc = mru_vote sa
  }"

definition three_step1_rel :: "(opt_mru_state \<times> three_step_mru_state)set"  where
  "three_step1_rel \<equiv> basic_rel \<inter> {(sa, sc).
    (\<exists>sc' r C. (sa, sc') \<in> three_step0_rel \<and> (sc', sc) \<in> opt_mru_step0 r C)
    \<and> mru_vote sc = mru_vote sa
  }"

definition three_step2_rel :: "(opt_mru_state \<times> three_step_mru_state)set"  where
  "three_step2_rel \<equiv> basic_rel \<inter> {(sa, sc).
    (\<exists>sc' r S v. (sa, sc') \<in> three_step1_rel \<and> (sc', sc) \<in> opt_mru_step1 r S v)
  }"

definition ts_ref_rel where
  "ts_ref_rel = {(sa, sc).
    (three_step (next_round sc) = 0 \<longrightarrow> (sa, sc) \<in> three_step0_rel)
    \<and> (three_step (next_round sc) = 1 \<longrightarrow> (sa, sc) \<in> three_step1_rel)
    \<and> (three_step (next_round sc) = 2 \<longrightarrow> (sa, sc) \<in> three_step2_rel)
  }"

lemmas ts_ref_rel_defs = 
  basic_rel_def
  ts_ref_rel_def
  three_step0_rel_def
  three_step1_rel_def
  three_step2_rel_def


lemma step0_ref:
  "{ts_ref_rel} Id, opt_mru_step0 r C {> ts_ref_rel}"
proof(simp only: PO_rhoare_defs, safe)
  fix sa sc sc'
  assume R: "(sa, sc) \<in> ts_ref_rel" and step: "(sc, sc') \<in> opt_mru_step0 r C"
  hence r_step: "three_step (next_round sc) = 0" "three_step (next_round sc') = 1"
    by(auto simp add: ts_ref_rel_def opt_mru_step0_def three_step_Suc)
  hence "(sa, sc') \<in> ts_ref_rel" using R step
    apply(auto simp add: ts_ref_rel_def  three_step_phase_Suc three_step1_rel_def
      three_step2_rel_def intro!: exI[where x=sc] step R)
     apply(auto simp add: three_step0_rel_def basic_rel_def three_step_phase_Suc
        opt_mru_step0_def)
    done
  thus "\<exists>sa'. (sa, sa') \<in> Id \<and> (sa', sc') \<in> ts_ref_rel" 
    by blast
qed

lemma step1_ref:
  "{ts_ref_rel} Id, opt_mru_step1 r S v {> ts_ref_rel}"
proof(simp only: PO_rhoare_defs, safe)
  fix sa sc sc'
  assume R: "(sa, sc) \<in> ts_ref_rel" and step: "(sc, sc') \<in> opt_mru_step1 r S v"
  hence r_step: "three_step (next_round sc) = 1" "three_step (next_round sc') = 2"
    by(auto simp add: ts_ref_rel_def opt_mru_step1_def three_step_Suc)
  hence "(sa, sc') \<in> ts_ref_rel" using R step
    apply(auto simp add: ts_ref_rel_def  three_step_phase_Suc three_step0_rel_def
      three_step2_rel_def intro!: exI[where x=sc] step R)
    apply(auto simp add: three_step1_rel_def basic_rel_def three_step_phase_Suc
      opt_mru_step1_def)
    done
  thus "\<exists>sa'. (sa, sa') \<in> Id \<and> (sa', sc') \<in> ts_ref_rel" 
    by blast
qed

lemma step2_ref:
  "{ts_ref_rel \<inter> OMRU_inv1 \<times> UNIV} 
    \<Union>r' Q S' v dec_f'. opt_mru_round r' Q S' v dec_f', 
    opt_mru_step2 r dec_f {> ts_ref_rel}"
proof(auto simp only: PO_rhoare_defs)
  fix sa sc2 sc3
  assume 
    ainv: "sa \<in> OMRU_inv1"
    and R: "(sa, sc2) \<in> ts_ref_rel"
    and step2: "(sc2, sc3) \<in> opt_mru_step2 r dec_f"

  from R step2 obtain sc0 r0 C sc1 r1 S v where
    R0: "(sa, sc0) \<in> three_step0_rel" and step0: "(sc0, sc1) \<in> opt_mru_step0 r0 C"
    and R1: "(sa, sc1) \<in> three_step1_rel" and step1: "(sc1, sc2) \<in> opt_mru_step1 r1 S v"
    by(fastforce simp add: ts_ref_rel_def three_step2_rel_def opt_mru_step2_def
      three_step1_rel_def)

  have R2: "(sa, sc2) \<in> three_step2_rel" 
    and r2_step: "three_step (next_round sc2) = Suc (Suc 0)" 
    and r3_step: "three_step (next_round sc3) = 0"
    using R step2
    by(auto simp add: ts_ref_rel_def opt_mru_step2_def three_step_phase_Suc three_step_Suc)

  have r: "r = Suc r1" and r1: "r1 = Suc r0" "r1 = next_round sc1" and 
    r0: "r0 = next_round sc0" and r0_step: "three_step r0 = 0" and 
    r2: "r = next_round sc2" 
    using step0 step1 step2
    by(auto simp add: opt_mru_step0_def opt_mru_step1_def opt_mru_step2_def)

  have abs_round2: "next_round sa = three_phase r" using R2 r2
    by(auto simp add: three_step2_rel_def basic_rel_def)
  have abs_round1: "next_round sa = three_phase r1" using R1 r1
    by(auto simp add: three_step1_rel_def basic_rel_def)
  have abs_round0: "next_round sa = three_phase r0" using R0 r0 r
    by(auto simp add: three_step0_rel_def basic_rel_def three_step_phase_Suc)

  have r_votes: "r_votes sc2 r = const_map v S"
  proof(rule ext)
    fix p
    show "r_votes sc2 r p = const_map v S p"
    proof(cases "r_votes sc2 r p")
      case None
      thus ?thesis using step0 step1 abs_round0 abs_round1 abs_round2
        by(auto simp add: r_votes_def opt_mru_step1_def
          const_map_def restrict_map_def map_add_def)        
    next
      case (Some w)
      hence in_S: "mru_vote sc1 p \<noteq> mru_vote sc2 p" using R0 step0 ainv r1 r abs_round0
        by(auto simp add: r_votes_def ts_ref_rel_defs
          three_step_phase_Suc opt_mru_step0_def dest: OMRU_inv1D[where p=p])
      hence "p \<in> S"  using step1
        by(auto simp add: opt_mru_step1_def map_add_def const_map_is_Some 
          split: option.split_asm)
      moreover have "w=v" using R0 R1 step1 ainv r abs_round1 Some
        by(auto simp add: r_votes_def ts_ref_rel_defs const_map_is_Some
          three_step_phase_Suc opt_mru_step1_def dest: OMRU_inv1D[where p=p])
      ultimately show ?thesis using Some
        by(auto simp add: const_map_def)
    qed
  qed

  from step0 step1 obtain Q where Q: "S \<noteq> {} \<longrightarrow> opt_mru_guard (mru_vote sc0) Q v"
    by(auto simp add: opt_mru_step0_def opt_mru_step1_def)
    
  define sa' where "sa' = sa\<lparr>
      mru_vote := mru_vote sa ++ const_map (three_phase r, v) S
      , next_round := Suc (three_phase r)
      , decisions := decisions sa ++ dec_f
    \<rparr>"
  
  have guard_strengthening:
    "step2_d_guard dec_f (r_votes sc2 r) \<longrightarrow> d_guard dec_f (const_map v S)"
    by(auto simp add: r_votes d_guard_def step2_d_guard_def locked_in_vf_def 
      quorum_for_def const_map_is_Some dom_const_map)
  have "(sa, sa') \<in> opt_mru_round (three_phase r) Q S v dec_f \<and> (sa', sc3) \<in> ts_ref_rel"
  proof
    show "(sa', sc3) \<in> ts_ref_rel" using r3_step R0 R1 R2 step0 step1 step2 
      by(auto simp add: ts_ref_rel_def three_step0_rel_def basic_rel_def opt_mru_step0_def 
        opt_mru_step1_def opt_mru_step2_def  sa'_def three_step_phase_Suc)
  next
    show "(sa, sa') \<in> opt_mru_round (three_phase r) Q S v dec_f" 
      using R0 r0_step step0 step1 step2 r0 r1 r2 r r_votes Q guard_strengthening
      by(auto simp add: ts_ref_rel_defs opt_mru_round_def three_step_phase_Suc
        opt_mru_step0_def opt_mru_step1_def opt_mru_step2_def sa'_def)
  qed
  thus "\<exists>y. (sa, y) \<in> (\<Union>r' Q S' v D'. opt_mru_round r' Q S' v D') \<and> (y, sc3) \<in> ts_ref_rel"
    by simp blast
qed  

lemma ThreeStep_Coordinated_Refines:
  "PO_refines (ts_ref_rel \<inter> OMRU_inv1 \<times> UNIV) 
    mru_opt_TS ts_mru_TS"
proof(rule refine_using_invariants)
  show "init ts_mru_TS \<subseteq> ts_ref_rel `` init mru_opt_TS"
    by(auto simp add: ts_mru_TS_defs mru_opt_TS_defs ts_ref_rel_def three_step0_rel_def 
      three_step1_rel_def three_step2_rel_def basic_rel_def)
next
  show 
    "{ts_ref_rel \<inter> OMRU_inv1 \<times> UNIV} TS.trans mru_opt_TS, 
      TS.trans (ts_mru_TS) {> ts_ref_rel}"
    apply(simp add: mru_opt_TS_defs ts_mru_TS_defs)
    apply(auto simp add: ts_mru_trans_def intro!: step0_ref step1_ref step2_ref)
    done
qed(auto intro!: OMRU_inv1_inductive)

end

end
