section \<open>The Same Vote Model\<close>
                                                                                            
theory Same_Vote
imports Voting
begin

context quorum_process begin

subsection \<open>Model definition\<close>
(******************************************************************************)

text \<open>The system state remains the same as in the Voting model, but the
  voting event is changed.\<close>

definition safe :: "v_state \<Rightarrow> round \<Rightarrow> val \<Rightarrow> bool" where
  safe_def': "safe s r v \<equiv> 
    \<forall>r' < r. \<forall>Q \<in> Quorum. \<forall>w. (votes s r') ` Q = {Some w} \<longrightarrow> v = w"

text \<open>This definition of @{term safe} is easier to reason about in Isabelle.\<close>
lemma safe_def:
  "safe s r v =
    (\<forall>r' < r. \<forall>Q w. quorum_for Q w (votes s r')  \<longrightarrow> v = w)"
  by(auto simp add: safe_def' quorum_for_def' Ball_def)

definition sv_round :: "round \<Rightarrow> process set \<Rightarrow> val \<Rightarrow> (process, val)map \<Rightarrow> (v_state \<times> v_state) set" where
  "sv_round r S v r_decisions = {(s, s').
     \<comment> \<open>guards\<close>
     r = next_round s
     \<and> (S \<noteq> {} \<longrightarrow> safe s r v)
     \<and> d_guard r_decisions (const_map v S)
     \<and> \<comment> \<open>actions\<close>
     s' = s\<lparr> 
       next_round := Suc r
       , votes := (votes s)(r := const_map v S)
       , decisions := (decisions s ++ r_decisions)
     \<rparr>
  }"

definition sv_trans :: "(v_state \<times> v_state) set" where
  "sv_trans = (\<Union>r S v D. sv_round r S v D) \<union> Id"

definition sv_TS :: "v_state TS" where
  "sv_TS = \<lparr> init = v_init, trans = sv_trans \<rparr>"

lemmas sv_TS_defs = sv_TS_def v_init_def sv_trans_def

subsection \<open>Refinement\<close>
(******************************************************************************)

lemma safe_imp_no_defection:
  "safe s (next_round s) v \<Longrightarrow> no_defection s (const_map v S) (next_round s)" 
  by(auto simp add: safe_def no_defection_def restrict_map_def const_map_def)
 
lemma const_map_quorum_locked:
  "S \<in> Quorum \<Longrightarrow> locked_in_vf (const_map v S) v"
  by(auto simp add: locked_in_vf_def const_map_def quorum_for_def)

lemma sv_round_refines:
  "{Id} v_round r (const_map v S) r_decisions, sv_round r S v r_decisions {> Id}"
  by(auto simp add: PO_rhoare_defs sv_round_def v_round_def  no_defection_empty
    dest!: safe_imp_no_defection const_map_quorum_locked)

lemma Same_Vote_Refines:
  "PO_refines Id v_TS sv_TS"
  by(auto simp add: PO_refines_def sv_TS_def sv_trans_def v_TS_defs intro!: 
    sv_round_refines relhoare_refl)


subsection \<open>Invariants\<close>
(******************************************************************************)

definition SV_inv3 where
  "SV_inv3 = {s. \<forall>r a b v w. 
    votes s r a = Some v \<and> votes s r b = Some w \<longrightarrow> v = w
  }"

lemmas SV_inv3I = SV_inv3_def [THEN setc_def_to_intro, rule_format]
lemmas SV_inv3E [elim] = SV_inv3_def [THEN setc_def_to_elim, rule_format]
lemmas SV_inv3D = SV_inv3_def [THEN setc_def_to_dest, rule_format]
 
subsubsection \<open>Proof of invariants\<close>
(******************************************************************************)

lemma SV_inv3_v_round: 
  "{SV_inv3} sv_round r S v D {> SV_inv3}" 
  apply(clarsimp simp add: PO_hoare_defs intro!: SV_inv3I)
  apply(force simp add: sv_round_def const_map_def restrict_map_def SV_inv3_def)
  done

lemmas SV_inv3_event_pres = SV_inv3_v_round 

lemma SV_inv3_inductive:
  "init sv_TS \<subseteq> SV_inv3" 
  "{SV_inv3} trans sv_TS {> SV_inv3}" 
  apply (simp add: sv_TS_defs SV_inv3_def)
  by (auto simp add: sv_TS_defs SV_inv3_event_pres)

lemma SV_inv3_invariant: "reach sv_TS \<subseteq> SV_inv3"
  by (auto intro!: inv_rule_basic SV_inv3_inductive del: subsetI)

text \<open>

This is a different characterization of @{term safe}, due to Lampson~\cite{lampson_abcds_2001}:
  @{term "safe' s r v = (\<forall>r'< r. (\<exists>Q \<in> Quorum. \<forall>a \<in> Q. \<forall>w. votes s r' a = Some w \<longrightarrow> w = v))"}

It is, however, strictly stronger than our characterization, since we do not at this point assume
the "completeness" of our quorum system (for any set S, either S or the complement of S is a
quorum), and the following is thus not provable: @{term "s \<in> SV_inv3 \<Longrightarrow> safe' s = safe s"}.

\<close>

subsubsection \<open>Transfer of abstract invariants\<close>
(******************************************************************************)

lemma SV_inv1_inductive:
  "init sv_TS \<subseteq> Vinv1"
  "{Vinv1} trans sv_TS {> Vinv1}" 
  apply(rule abs_INV_init_transfer[OF Same_Vote_Refines Vinv1_inductive(1), simplified])
  apply(rule abs_INV_trans_transfer[OF Same_Vote_Refines Vinv1_inductive(2), simplified])
  done

lemma SV_inv1_invariant:
  "reach sv_TS \<subseteq> Vinv1"
  by(rule abs_INV_transfer[OF Same_Vote_Refines Vinv1_invariant, simplified])

lemma SV_inv2_inductive:
  "init sv_TS \<subseteq> Vinv2"
  "{Vinv2 \<inter> Vinv1} trans sv_TS {> Vinv2}" 
  apply(rule abs_INV_init_transfer[OF Same_Vote_Refines Vinv2_inductive(1), simplified])
  apply(rule abs_INV_trans_transfer[OF Same_Vote_Refines Vinv2_inductive(2), simplified])
  done

lemma SV_inv2_invariant:
  "reach sv_TS \<subseteq> Vinv2"
  by(rule abs_INV_transfer[OF Same_Vote_Refines Vinv2_invariant, simplified])

subsubsection \<open>Additional invariants\<close>
(******************************************************************************)

text \<open>With Same Voting, the voted values are safe in the next round.\<close>

definition SV_inv4 :: "v_state set" where
  "SV_inv4 = {s. \<forall>v a r. votes s r a = Some v \<longrightarrow> safe s (Suc r) v }"

lemmas SV_inv4I = SV_inv4_def [THEN setc_def_to_intro, rule_format]
lemmas SV_inv4E [elim] = SV_inv4_def [THEN setc_def_to_elim, rule_format]
lemmas SV_inv4D = SV_inv4_def [THEN setc_def_to_dest, rule_format]

lemma SV_inv4_sv_round: 
  "{SV_inv4 \<inter> (Vinv1 \<inter> Vinv2)} sv_round r S v D {> SV_inv4}" 
proof(clarsimp simp add: PO_hoare_defs intro!: SV_inv4I)
  fix s v' a r' s'
  assume 
    step: "(s, s') \<in> sv_round r S v D"
    and invs: "s \<in> SV_inv4" "s \<in> Vinv1" "s \<in> Vinv2"
    and vote: "votes s' r' a = Some v'"
  thus "safe s' (Suc r') v'"
  proof(cases "r=r'")
    case True
    moreover hence safe: "safe s' r' v'" using step vote
      by(force simp add: sv_round_def const_map_is_Some safe_def quorum_for_def)
    ultimately show ?thesis using step vote
      by(force simp add: safe_def less_Suc_eq sv_round_def quorum_for_def const_map_is_Some 
        dest: quorum_non_empty)
  qed(clarsimp simp add: sv_round_def safe_def Vinv2_def Vinv1_def  SV_inv4_def
      intro: Quorum_not_empty)
qed

lemmas SV_inv4_event_pres = SV_inv4_sv_round 

lemma SV_inv4_inductive:
  "init sv_TS \<subseteq> SV_inv4" 
  "{SV_inv4 \<inter> (Vinv1 \<inter> Vinv2)} trans sv_TS {> SV_inv4}"
  apply(simp add: sv_TS_defs SV_inv4_def)
  by (auto simp add: sv_TS_defs SV_inv4_event_pres)

lemma SV_inv4_invariant: "reach sv_TS \<subseteq> SV_inv4"
  by (rule inv_rule_incr)
  (auto intro: SV_inv4_inductive SV_inv2_invariant SV_inv1_invariant del: subsetI)

end (* context quorum_process *)

end
