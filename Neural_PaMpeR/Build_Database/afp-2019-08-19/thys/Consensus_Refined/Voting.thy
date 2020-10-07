section \<open>The Voting Model\<close>

theory Voting imports Refinement Consensus_Misc Quorums
begin

subsection \<open>Model definition\<close>
(******************************************************************************)

record v_state = 
  (* We want 0 to be the first round, and we also have to use something in the initial state
     - hence next_round *)
  next_round :: round 
  votes :: "round \<Rightarrow> (process, val) map"
  decisions :: "(process, val)map"

text \<open>Initially, no rounds have been executed (the next round is 0), no votes have been
  cast, and no decisions have been made.\<close>

definition v_init :: "v_state set" where
  "v_init = { \<lparr> next_round = 0, votes = \<lambda>r a. None, decisions = Map.empty \<rparr> }"  

context quorum_process begin

definition quorum_for :: "process set \<Rightarrow> val \<Rightarrow> (process, val)map \<Rightarrow> bool" where
  quorum_for_def':
  "quorum_for Q v v_f \<equiv> Q \<in> Quorum \<and> v_f ` Q = {Some v}"

text \<open>The following definition of @{term quorum_for} is easier to reason about in Isabelle.\<close>

lemma quorum_for_def:
  "quorum_for Q v v_f = (Q \<in> Quorum \<and> (\<forall>p \<in> Q. v_f p = Some v))"
  by(auto simp add: quorum_for_def' image_def dest: quorum_non_empty)

definition locked_in_vf :: "(process, val)map \<Rightarrow> val \<Rightarrow> bool" where
  "locked_in_vf v_f v \<equiv> \<exists>Q. quorum_for Q v v_f"

definition locked_in :: "v_state \<Rightarrow> round \<Rightarrow> val \<Rightarrow> bool" where
  "locked_in s r v = locked_in_vf (votes s r) v"

definition d_guard :: "(process \<Rightarrow> val option) \<Rightarrow> (process \<Rightarrow> val option) \<Rightarrow> bool" where
  "d_guard r_decisions r_votes \<equiv> \<forall>p v.
    r_decisions p = Some v \<longrightarrow> locked_in_vf r_votes v"

definition no_defection :: "v_state \<Rightarrow> (process, val)map \<Rightarrow> round \<Rightarrow> bool" where
  no_defection_def':
  "no_defection s r_votes r \<equiv> 
    \<forall>r' < r. \<forall>Q \<in> Quorum. \<forall>v. (votes s r') ` Q = {Some v} \<longrightarrow> r_votes ` Q \<subseteq> {None, Some v}"

text \<open>The following definition of @{term no_defection} is easier to reason about in Isabelle.\<close>

lemma no_defection_def:
  "no_defection s round_votes r =
    (\<forall>r' < r. \<forall>a Q v. quorum_for Q v (votes s r') \<and> a \<in> Q \<longrightarrow> round_votes a \<in> {None, Some v})"
  apply(auto simp add: no_defection_def' Ball_def quorum_for_def')
   apply(blast)
  by (metis option.discI option.inject)
  
definition locked :: "v_state \<Rightarrow> val set" where
  "locked s = {v. \<exists>r. locked_in s r v}"

text \<open>The sole system event.\<close>

definition v_round :: "round \<Rightarrow> (process, val)map \<Rightarrow> (process, val)map \<Rightarrow> (v_state \<times> v_state) set" where
  "v_round r r_votes r_decisions = {(s, s').
     \<comment> \<open>guards\<close>
     r = next_round s
     \<and> no_defection s r_votes r
     \<and> d_guard r_decisions r_votes
     \<and> \<comment> \<open>actions\<close>
     s' = s\<lparr> 
       next_round := Suc r,
       votes := (votes s)(r := r_votes),
       decisions := (decisions s) ++ r_decisions
     \<rparr>
  }"

lemmas v_evt_defs = v_round_def

definition v_trans :: "(v_state \<times> v_state) set" where
  "v_trans = (\<Union>r v_f d_f. v_round r v_f d_f) \<union> Id"

definition v_TS :: "v_state TS" where
  "v_TS = \<lparr> init = v_init, trans = v_trans \<rparr>"

lemmas v_TS_defs = v_TS_def v_init_def v_trans_def


subsection \<open>Invariants\<close>
(******************************************************************************)

text \<open>The only rounds where votes could have been cast are the ones 
  preceding the next round.\<close>
definition Vinv1 where
  "Vinv1 = {s. \<forall>r. next_round s \<le> r \<longrightarrow> votes s r = Map.empty }"

lemmas Vinv1I = Vinv1_def [THEN setc_def_to_intro, rule_format]
lemmas Vinv1E [elim] = Vinv1_def [THEN setc_def_to_elim, rule_format]
lemmas Vinv1D = Vinv1_def [THEN setc_def_to_dest, rule_format]

text \<open>The votes cast must respect the @{term no_defection} property.\<close> 
definition Vinv2 where
  "Vinv2 = {s. \<forall>r. no_defection s (votes s r) r }"

lemmas Vinv2I = Vinv2_def [THEN setc_def_to_intro, rule_format]
lemmas Vinv2E [elim] = Vinv2_def [THEN setc_def_to_elim, rule_format]
lemmas Vinv2D = Vinv2_def [THEN setc_def_to_dest, rule_format]

definition Vinv3 where
  "Vinv3 = {s. ran (decisions s) \<subseteq> locked s}"

lemmas Vinv3I = Vinv3_def [THEN setc_def_to_intro, rule_format]
lemmas Vinv3E [elim] = Vinv3_def [THEN setc_def_to_elim, rule_format]
lemmas Vinv3D = Vinv3_def [THEN setc_def_to_dest, rule_format]

subsubsection \<open>Proofs of invariants\<close>
(******************************************************************************)

(*************************) 
lemma Vinv1_v_round: 
  "{Vinv1} v_round r v_f d_f {> Vinv1}" 
  by(auto simp add: PO_hoare_defs v_round_def intro!: Vinv1I)

lemmas Vinv1_event_pres = Vinv1_v_round

lemma Vinv1_inductive:
  "init v_TS \<subseteq> Vinv1"
  "{Vinv1} trans v_TS {> Vinv1}"
  apply (simp add: v_TS_defs Vinv1_def)
  by (auto simp add: v_TS_defs Vinv1_event_pres)

lemma Vinv1_invariant: "reach v_TS \<subseteq> Vinv1"
  by (rule inv_rule_basic, auto intro!: Vinv1_inductive)

text \<open>The following two lemmas will be useful later, when we
  start taking votes with the maximum timestamp.\<close>

lemma Vinv1_finite_map_graph:
   "s \<in> Vinv1 \<Longrightarrow> finite (map_graph (case_prod (votes s)))"
  apply(rule finite_dom_finite_map_graph)
  apply(rule finite_subset[where B="{0..< v_state.next_round s} \<times> UNIV"])
   apply(auto simp add: Vinv1_def dom_def not_le[symmetric])
  done

lemma Vinv1_finite_vote_set:
   "s \<in> Vinv1 \<Longrightarrow> finite (vote_set (votes s) Q)"
   apply(drule Vinv1_finite_map_graph)
   apply(clarsimp simp add: map_graph_def fun_graph_def vote_set_def)
   apply(erule finite_surj[where f="\<lambda>((r, a), v). (r, v)"])
   by(force simp add: image_def)   

lemma process_mru_map_add:
  assumes
    "s \<in> Vinv1"
  shows 
    "process_mru ((votes s)(next_round s := v_f)) = 
    (process_mru (votes s) ++ (\<lambda>p. map_option (Pair (next_round s)) (v_f p)))"
proof-
  from assms[THEN Vinv1D] have empty: "\<forall>r' \<ge> next_round s. votes s r' = Map.empty"
    by simp
  show ?thesis
    by(auto  simp add: process_mru_new_votes[OF empty] map_add_def split: option.split)
qed

(*************************)

lemma no_defection_empty:
  "no_defection s Map.empty r'"
  by(auto simp add: no_defection_def)

lemma no_defection_preserved:
assumes
  "s \<in> Vinv1"
  "r = next_round s"
  "no_defection s v_f r"
  "no_defection s (votes s r') r'"
  "votes s' = (votes s)(r := v_f)"
shows 
  "no_defection s' (votes s' r') r'" using assms
  by(force simp add: no_defection_def)
  
(********)

lemma Vinv2_v_round: 
  "{Vinv2 \<inter> Vinv1} v_round r v_f d_f {> Vinv2}" 
  apply(auto simp add: PO_hoare_defs intro!: Vinv2I)
  apply(rename_tac s' r' s)
  apply(erule no_defection_preserved)
      apply(auto simp add: v_round_def intro!: v_state.equality)
  done

lemmas Vinv2_event_pres = Vinv2_v_round

lemma Vinv2_inductive:
  "init v_TS \<subseteq> Vinv2"
  "{Vinv2 \<inter> Vinv1} trans v_TS {> Vinv2}" 
  apply(simp add: v_TS_defs Vinv2_def no_defection_def)
  by (auto simp add: v_TS_defs Vinv2_event_pres)

lemma Vinv2_invariant: "reach v_TS \<subseteq> Vinv2"
  by (rule inv_rule_incr, auto intro: Vinv2_inductive Vinv1_invariant del: subsetI)

(*************************)
lemma locked_preserved:
assumes
  "s \<in> Vinv1"
  "r = next_round s"
  "votes s' = (votes s)(r := v_f)"
shows 
  "locked s \<subseteq> locked s'" using assms
  apply(auto simp add: locked_def locked_in_def locked_in_vf_def quorum_for_def dest!: Vinv1D)
  by (metis option.distinct(1))
  

(*************************)

lemma Vinv3_v_round: 
  "{Vinv3 \<inter> Vinv1} v_round r v_f d_f {> Vinv3}"
proof(clarsimp simp add: PO_hoare_defs, intro Vinv3I, safe)
  fix s s' v
  assume step: "(s, s') \<in> v_round r v_f d_f" and inv3: "s \<in> Vinv3" and inv1: "s \<in> Vinv1"
  and dec: "v \<in> ran (decisions s')"
  have "locked s \<subseteq> locked s'" using step
    by(intro locked_preserved[OF inv1, where s'=s']) (auto simp add: v_round_def)
  with Vinv3D[OF inv3] step dec
  show "v \<in> locked s'"
    apply(auto simp add: v_round_def dest!: ran_map_addD)
    apply(auto simp add: locked_def locked_in_def d_guard_def ran_def)
    done
qed

lemmas Vinv3_event_pres = Vinv3_v_round

lemma Vinv3_inductive:
  "init v_TS \<subseteq> Vinv3"
  "{Vinv3 \<inter> Vinv1} trans v_TS {> Vinv3}" 
  apply(simp add: v_TS_defs Vinv3_def no_defection_def)
  by (auto simp add: v_TS_defs Vinv3_event_pres)

lemma Vinv3_invariant: "reach v_TS \<subseteq> Vinv3"
  by (rule inv_rule_incr, auto intro: Vinv3_inductive Vinv1_invariant del: subsetI)


subsection \<open>Agreement and stability\<close>
(******************************************************************************)

text \<open>Only a singe value can be locked within the votes for one round.\<close>
lemma locked_in_vf_same:
  "\<lbrakk> locked_in_vf v_f v; locked_in_vf v_f w \<rbrakk> \<Longrightarrow> v = w" using qintersect
  apply(auto simp add: locked_in_vf_def quorum_for_def image_iff)
  by (metis Int_iff all_not_in_conv option.inject)

text \<open>In any reachable state, no two different values can be locked in
  different rounds.\<close>
theorem locked_in_different:
assumes
  "s \<in> Vinv2"
  "locked_in s r1 v"
  "locked_in s r2 w"
  "r1 < r2"
shows
  "v = w"
proof- 
  \<comment> \<open>To be locked, @{term v} and @{term w} must each have received votes from a quorum.\<close>
  from assms(2-3) obtain Q1 Q2 
  where Q12: "Q1 \<in> Quorum" "Q2 \<in> Quorum" "quorum_for Q1 v (votes s r1)" "quorum_for Q2 w (votes s r2)"
    by(auto simp add: locked_in_def locked_in_vf_def quorum_for_def)
  \<comment> \<open>By the quorum intersection property, some process from @{term Q1} voted for @{term w}:\<close>
  then obtain a where "a \<in> Q1" "votes s r2 a = Some w" 
    using qintersect[OF \<open>Q1 \<in> Quorum\<close> \<open>Q2 \<in> Quorum\<close>]
    by(auto simp add: quorum_for_def)
  \<comment> \<open>But from @{term Vinv2} we conclude that @{term a} could not have defected by voting
        @{term w}, so @{term ?thesis}:\<close>
  thus ?thesis using \<open>s \<in> Vinv2\<close> \<open>quorum_for Q1 v (votes s r1)\<close> \<open>r1 < r2\<close>
    by(fastforce simp add: Vinv2_def no_defection_def quorum_for_def')
qed

text \<open>It is simple to extend the previous theorem to any two (not necessarily different) rounds.\<close>
theorem locked_unique: 
assumes 
  "s \<in> Vinv2"
  "v \<in> locked s" "w \<in> locked s"
shows 
  "v = w"
proof -
  from assms(2-3) obtain r1 r2 where quoIn: "locked_in s r1 v" "locked_in s r2 w"
    by (auto simp add: locked_def)
  have "r1 < r2 \<or> r1 = r2 \<or> r2 < r1" by (rule linorder_less_linear) 
  thus ?thesis
  proof (elim disjE)
    assume "r1 = r2"
    with quoIn show ?thesis
      by(simp add: locked_in_def locked_in_vf_same)
  qed(auto intro: locked_in_different[OF \<open>s \<in> Vinv2\<close>] quoIn sym)
qed

text \<open>We now prove that decisions are stable; once a process makes a decision, it never
  changes it, and it does not go back to an undecided state. Note that behaviors grow at 
  the front; hence @{term "tr ! (i-j)"} is later in the trace than @{term "tr ! i"}.\<close>
lemma stable_decision:
  assumes beh: "tr \<in> beh v_TS"
  and len: "i < length tr"
  and s: "s = nth tr i"
  and t: "t = nth tr (i - j)"
  and dec: 
    "decisions s p = Some v"
  shows
    "decisions t p = Some v"
proof-
  \<comment> \<open>First, we show that the both @{term s} and @{term t} respect the invariants.\<close>
  have reach: "s \<in> reach v_TS" "t \<in> reach v_TS" using beh s t len
     apply(simp_all add: reach_equiv_beh_states)
     apply (metis len nth_mem) 
    apply (metis less_imp_diff_less nth_mem)
    done
  hence invs2: "s \<in> Vinv2" and invs3: "s \<in> Vinv3"
    by(blast dest: Vinv2_invariant[THEN subsetD] Vinv3_invariant[THEN subsetD])+
    
  show ?thesis using t
  proof(induction j arbitrary: t)
    case (Suc j)
    hence dec_j: "decisions (tr ! (i - j)) p = Some v" 
      by simp
    thus "decisions t p = Some v" using Suc
    \<comment> \<open>As @{term "(-)"} is a total function on naturals, we perform a case distinction;
          if @{term "i < j"}, the induction step is trivial.\<close>
    proof(cases "i \<le> j") 
      \<comment> \<open>The non-trivial case.\<close>
      case False
      define t' where "t' = tr ! (i - j)"
      \<comment> \<open>Both @{term t} and @{term t'} are reachable, thus respect the invariants, and
        they are related by the transition relation.\<close>
      hence "t' \<in> reach v_TS" "t \<in> reach v_TS" using beh len Suc
        by (metis beh_in_reach less_imp_diff_less nth_mem)+
      hence invs: "t' \<in> Vinv1" "t' \<in> Vinv3" "t \<in> Vinv2" "t \<in> Vinv3"
        by(blast dest: Vinv1_invariant[THEN subsetD] Vinv2_invariant[THEN subsetD] 
          Vinv3_invariant[THEN subsetD])+
      hence locked_v: "v \<in> locked t'" using Suc
        by(auto simp add: t'_def intro: ranI)
      have "i - j = Suc (i - (Suc j))" using False
        by simp
      hence trans: "(t', t) \<in> trans v_TS" using beh len Suc 
        by(auto simp add: t'_def intro!: beh_consecutive_in_trans)
      \<comment> \<open>Thus @{term v} also remains locked in @{term t}, and @{term p} does not 
        revoke, nor change its decision.\<close>
      hence locked_v_t: "v \<in> locked t" using locked_v
        by(auto simp add: v_TS_defs v_round_def
          intro: locked_preserved[OF invs(1), THEN subsetD, OF _ _ locked_v])
      from trans obtain w where "decisions t p = Some w" using dec_j
        by(fastforce simp add: t'_def v_TS_defs v_round_def 
          split: option.split option.split_asm)
      thus ?thesis using invs(4)[THEN Vinv3D] locked_v_t locked_unique[OF invs(3)]
        by (metis contra_subsetD ranI)
    qed(auto)
  next
    case 0
    thus "decisions t p = Some v" using assms
      by auto
  qed
qed

text \<open>Finally, we prove that the Voting model ensures agreement. Without a loss 
  of generality, we assume that \<open>t\<close> preceeds \<open>s\<close> in the trace.\<close>
lemma Voting_agreement:
  assumes beh: "tr \<in> beh v_TS"
  and len: "i < length tr"
  and s: "s = nth tr i"
  and t: "t = nth tr (i - j)"
  and dec: 
    "decisions s p = Some v"
    "decisions t q = Some w"
  shows "w = v"
proof-
  \<comment> \<open>Again, we first prove that the invariants hold for @{term s}.\<close>
  have reach: "s \<in> reach v_TS" using beh s t len
    apply(simp_all add: reach_equiv_beh_states)
    by (metis nth_mem)
  hence invs2: "s \<in> Vinv2" and invs3: "s \<in> Vinv3"
    by(blast dest: Vinv2_invariant[THEN subsetD] Vinv3_invariant[THEN subsetD])+

  \<comment> \<open>We now proceed to prove the thesis by induction.\<close>
  thus ?thesis using assms
  proof(induction j arbitrary: t)
    case 0
    hence
      "v \<in> locked (tr ! i)"
      "w \<in> locked (tr ! i)"
      by(auto intro: ranI)
    thus ?thesis using invs2 using assms 0
      by(auto dest: locked_unique)
  next
    case (Suc j)
    thus ?thesis
    \<comment> \<open>Again, the totality of @{term "(-)"} makes the claim trivial if @{term "i < j"}.\<close>
    proof(cases "i \<le> j")
      case False
      \<comment> \<open>In the non-trivial case, the proof follows from the decision stability theorem 
        and the uniqueness of locked values.\<close>
      have dec_t: "decisions t p = Some v" using Suc
        by(auto intro: stable_decision[OF beh len s ])
      have "t \<in> reach v_TS" using beh len Suc
        by (metis beh_in_reach less_imp_diff_less nth_mem)
      hence invs: "t \<in> Vinv2" "t \<in> Vinv3"
        by(blast dest: Vinv2_invariant[THEN subsetD] Vinv3_invariant[THEN subsetD])+
      from dec_t have "v \<in> locked t" using invs(2)
        by(auto intro: ranI) 
      moreover have locked_w_t: "w \<in> locked t" using Suc \<open>t \<in> Vinv3\<close>[THEN Vinv3D]
        by(auto intro: ranI)
      ultimately show ?thesis using locked_unique[OF \<open>t \<in> Vinv2\<close>]
        by blast
    qed(auto)
  qed
qed

end (* context quorum *)

end
