section \<open>Optimized MRU Vote Model\<close>

theory MRU_Vote_Opt
imports MRU_Vote
begin

subsection \<open>Model definition\<close>
(******************************************************************************)

record opt_mru_state = 
  next_round :: round 
  mru_vote :: "(process, round \<times> val) map"
  decisions :: "(process, val)map"

definition opt_mru_init where
  "opt_mru_init = { \<lparr> next_round = 0, mru_vote = Map.empty, decisions = Map.empty \<rparr> }"

context quorum_process begin
  
definition opt_mru_vote :: "(process, round \<times> val)map \<Rightarrow> (process set, round \<times> val)map" where
  "opt_mru_vote lvs Q = option_Max_by fst (ran (lvs |` Q))"

definition opt_mru_guard :: "(process, round \<times> val)map \<Rightarrow> process set \<Rightarrow> val \<Rightarrow> bool" where
  "opt_mru_guard mru_votes Q v \<equiv> Q \<in> Quorum \<and> 
    (let mru = opt_mru_vote mru_votes Q in mru = None \<or> (\<exists>r. mru = Some (r, v)))"
                    
definition opt_mru_round 
  :: "round \<Rightarrow> process set \<Rightarrow> process set \<Rightarrow> val \<Rightarrow> (process, val)map \<Rightarrow> (opt_mru_state \<times> opt_mru_state) set" 
  where
  "opt_mru_round r Q S v r_decisions = {(s, s').
     \<comment> \<open>guards\<close>
     r = next_round s
     \<and> (S \<noteq> {} \<longrightarrow> opt_mru_guard (mru_vote s) Q v)
     \<and> d_guard r_decisions (const_map v S)
     \<and> \<comment> \<open>actions\<close>
     s' = s\<lparr> 
       mru_vote := mru_vote s ++ const_map (r, v) S
       , next_round := Suc r
       , decisions := decisions s ++ r_decisions
     \<rparr>
  }"

lemmas lv_evt_defs = opt_mru_round_def opt_mru_guard_def

definition mru_opt_trans :: "(opt_mru_state \<times> opt_mru_state) set" where
  "mru_opt_trans = (\<Union>r Q S v D. opt_mru_round r Q S v D) \<union> Id"

definition mru_opt_TS :: "opt_mru_state TS" where
  "mru_opt_TS = \<lparr> init = opt_mru_init, trans = mru_opt_trans \<rparr>"

lemmas mru_opt_TS_defs = mru_opt_TS_def opt_mru_init_def mru_opt_trans_def

subsection \<open>Refinement\<close>
(******************************************************************************)

definition lv_ref_rel :: "(v_state \<times> opt_mru_state)set" where
  "lv_ref_rel = {(sa, sc).
    sc = \<lparr>
      next_round = v_state.next_round sa
      , mru_vote = process_mru (votes sa)
      , decisions = v_state.decisions sa
    \<rparr>
  }"

subsubsection \<open>The concrete guard implies the abstract guard\<close>
(******************************************************************************)


definition voters :: "(round \<Rightarrow> (process, val)map) \<Rightarrow> process set" where
  "voters vs = {a|a r v. ((r, a), v) \<in> map_graph (case_prod vs)}"

lemma vote_set_as_Union:
  "vote_set vs Q = (\<Union>a\<in>(Q \<inter> voters vs). vote_set vs {a})"
  by(auto simp add: vote_set_def voters_def)

lemma empty_ran:
  "(ran f = {}) = (\<forall>x. f x = None)"
  apply(auto simp add: ran_def)
  by (metis option.collapse)

lemma empty_ran_restrict:
  "(ran (f |` A) = {}) = (\<forall>x \<in> A. f x = None)"
  by(auto simp add: empty_ran restrict_map_def)

lemma option_Max_by_eqI:
  "\<lbrakk> (S = {}) \<longleftrightarrow> (S' = {}); S \<noteq> {} \<and> S' \<noteq> {} \<Longrightarrow> Max_by f S = Max_by g S' \<rbrakk> 
  \<Longrightarrow>  option_Max_by f S = option_Max_by g S'"
  by(auto simp add: option_Max_by_def)

lemma ran_process_mru_only_voters:
  "ran (process_mru vs |` Q) = ran (process_mru vs |` (Q \<inter> voters vs))"
  by(auto simp add: ran_def restrict_map_def voters_def process_mru_def 
    mru_of_set_def option_Max_by_def vote_set_def)

lemma SV_inv3_inj_on_fst_vote_set:
  "s \<in> SV_inv3 \<Longrightarrow> inj_on fst (vote_set (votes s) Q)"
  by(clarsimp simp add: SV_inv3_def inj_on_def vote_set_def)

lemma opt_mru_vote_mru_of_set:
  assumes
    inv1: "s \<in> Vinv1"
    and inv3: "s \<in> SV_inv3"
  defines "vs \<equiv> votes s"
  shows
    "opt_mru_vote (process_mru vs) Q = mru_of_set vs Q"
proof(simp add: opt_mru_vote_def mru_of_set_def, intro option_Max_by_eqI, clarsimp_all)
  show "(ran (process_mru vs |` Q) = {}) = (vote_set vs Q = {})"
    apply(clarsimp simp add: empty_ran_restrict process_mru_def mru_of_set_def option_Max_by_def 
      vote_set_def)
    by (metis option.collapse option.distinct(1))
next
  assume nempty: "ran (process_mru vs |` Q) \<noteq> {}" "vote_set vs Q \<noteq> {}"

  hence nempty': "Q \<inter> voters vs \<noteq> {}"
    by(auto simp add: vote_set_def voters_def)

  have nempty'': "{} \<notin> (\<lambda>a. vote_set vs {a}) ` (Q \<inter> voters vs)"
    by(auto simp add: vote_set_def voters_def)

  note fin=Vinv1_finite_vote_set[OF inv1]

  have ran_eq: 
    "ran (process_mru vs |` Q) = Max_by fst ` (\<lambda>a. \<Union>a\<in>{a} \<inter> voters vs. vote_set vs {a}) ` (Q \<inter> voters vs)"
    apply(subst ran_process_mru_only_voters)
    apply(auto simp add: image_def process_mru_def ran_def restrict_map_def mru_of_set_def option_Max_by_def)
    by (metis (erased, lifting) Set.set_insert image_eqI insertI1 insert_inter_insert nempty'')

  note inj=inv3[THEN SV_inv3_inj_on_fst_vote_set]

  show "Max_by fst (ran (process_mru vs |` Q)) = Max_by fst (vote_set vs Q)"
    apply(subst vs_def 
      Max_by_UNION_distrib[OF fin vote_set_as_Union nempty'[simplified vs_def] 
        nempty''[simplified vs_def] inj])+
    apply(subst vote_set_as_Union)
    by(metis ran_eq vs_def)
qed

lemma opt_mru_guard_imp_mru_guard:
  assumes invs:
    "s \<in> Vinv1" "s \<in> SV_inv3"
    and c_guard: "opt_mru_guard (process_mru (votes s)) Q v"
  shows "mru_guard s Q v" using c_guard
  by(simp add: opt_mru_vote_mru_of_set[OF invs] opt_mru_guard_def mru_guard_def Let_def)

subsubsection \<open>The concrete action refines the abstract action\<close>
(******************************************************************************)


lemma act_ref:
  assumes
    "s \<in> Vinv1"
  shows 
    "process_mru (votes s) ++ const_map (v_state.next_round s, v) S 
    = process_mru ((votes s)(v_state.next_round s := const_map v S))"
    by(auto simp add: process_mru_map_add[OF assms(1)] map_add_def const_map_def 
      restrict_map_def
      split:option.split)

subsubsection \<open>The complete refinement\<close> 
(******************************************************************************)

lemma opt_mru_guard_imp_Quorum:
  "opt_mru_guard vs Q v \<Longrightarrow> Q \<in> Quorum"
  by (simp add: opt_mru_guard_def Let_def)

lemma opt_mru_round_refines:
  "{lv_ref_rel \<inter> (Vinv1 \<inter> SV_inv3 \<inter> SV_inv4) \<times> UNIV} 
    sv_round r S v d_f, opt_mru_round r Q S v d_f 
  {> lv_ref_rel}"
  apply(clarsimp simp add: PO_rhoare_defs lv_ref_rel_def opt_mru_round_def sv_round_def 
    act_ref del: disjCI)
  apply(auto intro!: opt_mru_guard_imp_mru_guard[where Q=Q]  mru_vote_implies_safe[where Q=Q]
    dest: opt_mru_guard_imp_Quorum)
  done
  
lemma Opt_MRU_Vote_Refines:
  "PO_refines (lv_ref_rel \<inter> (Vinv1 \<inter> Vinv2 \<inter> SV_inv3 \<inter> SV_inv4) \<times> UNIV) sv_TS mru_opt_TS"
proof(rule refine_using_invariants)
  show "init mru_opt_TS \<subseteq> lv_ref_rel `` init sv_TS"
    by(auto simp add: mru_opt_TS_defs sv_TS_defs lv_ref_rel_def
      process_mru_def mru_of_set_def vote_set_def option_Max_by_def)
next
  show 
    "{lv_ref_rel \<inter> (Vinv1 \<inter> Vinv2 \<inter> SV_inv3 \<inter> SV_inv4) \<times> UNIV} trans sv_TS, trans mru_opt_TS {> lv_ref_rel}"
    by(auto simp add: sv_TS_defs mru_opt_TS_defs intro!: opt_mru_round_refines)
next
  show
    "{Vinv1 \<inter> Vinv2 \<inter> SV_inv3 \<inter> SV_inv4 \<inter> Domain (lv_ref_rel \<inter> UNIV \<times> UNIV)} 
      trans sv_TS 
    {> Vinv1 \<inter> Vinv2 \<inter> SV_inv3 \<inter> SV_inv4}" 
    using SV_inv1_inductive(2) SV_inv2_inductive(2) SV_inv3_inductive(2) SV_inv4_inductive(2)
    by blast
qed(auto intro!: SV_inv1_inductive(1) SV_inv2_inductive(1) SV_inv3_inductive(1) SV_inv4_inductive(1))

subsection \<open>Invariants\<close>
(******************************************************************************)

definition OMRU_inv1 :: "opt_mru_state set" where
  "OMRU_inv1 = {s. \<forall>p. (case mru_vote s p of
      Some (r, _) \<Rightarrow> r < next_round s
      | None \<Rightarrow> True)
  }"

lemma OMRU_inv1_inductive:
  "init mru_opt_TS \<subseteq> OMRU_inv1"
  "{OMRU_inv1} trans mru_opt_TS {> OMRU_inv1}"
  by(fastforce simp add: mru_opt_TS_def opt_mru_init_def PO_hoare_def OMRU_inv1_def mru_opt_trans_def 
    opt_mru_round_def const_map_is_Some less_Suc_eq
    split: option.split_asm option.split)+

lemmas OMRU_inv1I = OMRU_inv1_def [THEN setc_def_to_intro, rule_format]
lemmas OMRU_inv1E [elim] = OMRU_inv1_def [THEN setc_def_to_elim, rule_format]
lemmas OMRU_inv1D = OMRU_inv1_def [THEN setc_def_to_dest, rule_format]

end

end
