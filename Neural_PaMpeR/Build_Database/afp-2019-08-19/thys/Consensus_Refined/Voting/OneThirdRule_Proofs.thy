(*<*)
theory OneThirdRule_Proofs
imports Heard_Of.Majorities 
  "../HO_Transition_System" "../Voting_Opt" OneThirdRule_Defs
begin
(*>*)

subsection \<open>Proofs\<close>

definition majs :: "(process set) set" where
  "majs \<equiv> {S. card S > (2 * N) div 3}"

lemma card_Compl:
  fixes S :: "('a :: finite) set"
  shows "card (-S) = card (UNIV :: 'a set) - card S"
proof-
  have "card S + card (-S) = card (UNIV :: 'a set)"
    by(rule card_Un_disjoint[of S "-S", simplified Compl_partition, symmetric])
      (auto)
  thus ?thesis
    by simp
qed

lemma m_mult_div_Suc_m:
  "n > 0 \<Longrightarrow> m * n div Suc m < n"
  by (simp add: less_mult_imp_div_less)
  
interpretation majorities: quorum_process majs
proof
  fix Q Q' assume "Q \<in> majs" "Q' \<in> majs"
  hence "(4 * N) div 3 < card Q + card Q'"
    by(auto simp add: majs_def)
  thus "Q \<inter> Q' \<noteq> {}"
    apply (intro majorities_intersect)
    apply(auto)
    done
next
  have "N > 0"
    by auto
  have "2 * N div 3 < N"
    by(simp only: eval_nat_numeral m_mult_div_Suc_m[OF \<open>N > 0\<close>])
  thus "\<exists>Q. Q \<in> majs" 
    apply(rule_tac x=UNIV in exI)
    apply(auto simp add: majs_def intro!: div_less_dividend)
    done
qed

lemma card_Un_le:
  "\<lbrakk> finite A; finite B \<rbrakk> \<Longrightarrow> card (A \<union> B) \<le> card A + card B"
  by(simp only: card_Un_Int)


lemma qintersect_card:
  assumes "Q \<in> majs" "Q' \<in> majs"
  shows "card (Q \<inter> Q') > card (Q \<inter> -Q')"
proof-
  have "card (Q \<inter> -Q') \<le> card (-Q')"
    by(auto intro!: card_mono)
  also have "... < N - (card (-Q) + card (-Q'))"
  proof-
    have sum: "N < card Q + card Q'" using assms
      by(auto simp add: majs_def)
    have le_N: "card Q \<le> N" "card Q' \<le> N" by (auto intro!: card_mono)
    show ?thesis using assms sum
      apply(simp add: card_Compl)
      apply(intro diff_less_mono2)
      apply(auto simp add: majs_def card_Compl)
       apply(simp add: diff_add_assoc2[symmetric, OF le_N(1)] add_diff_assoc[OF le_N(2)])
      by (metis add_mono le_N(1) le_N(2) less_diff_conv2 nat_add_left_cancel_less) 
  qed              
  also have "... \<le> card (Q \<inter> Q')"
  proof-
    have "N - (card (-Q) + card (-Q')) \<le> card (-(-Q \<union> -Q'))"
      apply(simp only: card_Compl[where S="-Q \<union> -Q'"])
      apply(auto intro!: diff_le_mono2 card_Un_le)
      done
    thus ?thesis
      by(auto)
  qed
  finally show ?thesis . 
qed

axiomatization where val_linorder: 
  (* "class.finite TYPE(process)" *)
  "OFCLASS(val, linorder_class)"

instance val :: linorder by (rule val_linorder)

type_synonym p_TS_state = "(nat \<times> (process \<Rightarrow> (val pstate)))"

definition K where
  "K y \<equiv> \<lambda>x. y"

definition OTR_Alg where
  "OTR_Alg =
    \<lparr> CinitState =  (\<lambda> p st crd. OTR_initState p st),
     sendMsg =  OTR_sendMsg,
     CnextState = (\<lambda> r p st msgs crd st'. OTR_nextState r p st msgs st')
   \<rparr>"

definition OTR_TS ::
  "(round \<Rightarrow> process HO)
  \<Rightarrow> (round \<Rightarrow> process HO)
  \<Rightarrow> (round \<Rightarrow> process)
  \<Rightarrow> p_TS_state TS"
where
  "OTR_TS HOs SHOs crds = CHO_to_TS OTR_Alg HOs SHOs (K o crds)"

lemmas OTR_TS_defs = OTR_TS_def CHO_to_TS_def OTR_Alg_def CHOinitConfig_def
  OTR_initState_def

definition
  "OTR_trans_step HOs \<equiv> \<Union>r \<mu>.
   {((r, cfg), Suc r, cfg')|cfg cfg'.
    (\<forall>p. \<mu> p \<in> get_msgs (OTR_sendMsg r) cfg (HOs r) (HOs r) p) \<and>
    (\<forall>p. OTR_nextState r p (cfg p) (\<mu> p) (cfg' p))}"

definition CSHOnextConfig where
  "CSHOnextConfig A r cfg HO SHO coord cfg' \<equiv>
   \<forall>p. \<exists>\<mu> \<in> SHOmsgVectors A r p cfg (HO p) (SHO p).
          CnextState A r p (cfg p) \<mu> (coord p) (cfg' p)"

type_synonym rHO = "nat \<Rightarrow> process HO"

subsubsection \<open>Refinement\<close>
(******************************************************************************)

definition otr_ref_rel :: "(opt_v_state \<times> p_TS_state)set" where
  "otr_ref_rel =  {(sa, (r, sc)).
    r = next_round sa
    \<and> (\<forall>p. decisions sa p = decision (sc p))
    \<and> majorities.opt_no_defection sa (Some o last_vote o sc)
  }"

lemma decide_origin:
  assumes 
    send: "\<mu> p \<in> get_msgs (OTR_sendMsg r) sc (HOs r) (HOs r) p"
    and nxt: "OTR_nextState r p (sc p) (\<mu> p) (sc' p)"
    and new_dec: "decision (sc' p) \<noteq> decision (sc p)"
  shows
    "\<exists>v. decision (sc' p) = Some v \<and> {q. last_vote (sc q) = v} \<in> majs"
proof-
  from new_dec and nxt obtain v where 
    p_dec_v: "decision (sc' p) = Some v" 
    and two_thirds_v: "TwoThirds (\<mu> p) v"
    apply(auto simp add: OTR_nextState_def split: if_split_asm)
    by (metis exE_some)
  then have "2 * N div 3 < card {q. last_vote (sc q) = v}" using send
    by(auto simp add: get_msgs_benign OTR_sendMsg_def TwoThirds_def HOV_def 
      restrict_map_def elim!: less_le_trans intro!: card_mono)
  with p_dec_v show ?thesis by (auto simp add: majs_def)
qed

lemma MFR_in_msgs:
  assumes HO:"dom msgs \<noteq> {}"
      and v: "MFR msgs v"
  shows "\<exists>q \<in> dom msgs. v = the (msgs q)"
proof -
  from HO obtain q where q: "q \<in> dom msgs"
    by auto
  with v have "HOV msgs (the (msgs q)) \<noteq> {}"
    by (auto simp: HOV_def )
  hence HOp: "0 < card (HOV msgs (the (msgs q)))"
    by auto
  also from v have "\<dots> \<le> card (HOV msgs v)"
    by (simp add: MFR_def)
  finally have "HOV msgs v \<noteq> {}"
    by auto
  thus ?thesis
    by (force simp: HOV_def)
qed

lemma step_ref:
  "{otr_ref_rel} 
      (\<Union>r v_f d_f. majorities.flv_round r v_f d_f), 
      OTR_trans_step HOs 
    {> otr_ref_rel}"
proof(simp add: PO_rhoare_defs OTR_trans_step_def, safe)
  fix sa r sc sc' \<mu>
  assume
    R: "(sa, r, sc) \<in> otr_ref_rel"
    and send: "\<forall>p. \<mu> p \<in> get_msgs (OTR_sendMsg r) sc (HOs r) (HOs r) p"
    and nxt: "\<forall>p. OTR_nextState r p (sc p) (\<mu> p) (sc' p)"
  note step=send nxt
  define d_f
    where "d_f p = (if decision (sc' p) \<noteq> decision (sc p) then decision (sc' p) else None)" for p

  define sa' where "sa' = \<lparr> 
    opt_v_state.next_round = Suc r
    , opt_v_state.last_vote = opt_v_state.last_vote sa ++ (Some o last_vote o sc) 
    , opt_v_state.decisions = opt_v_state.decisions sa ++ d_f
    \<rparr>"
  
  have "majorities.d_guard d_f (Some o last_vote o sc)"
  proof(clarsimp simp add: majorities.d_guard_def d_f_def)
    fix p v
    assume
      "Some v \<noteq> decision (sc p)" 
      "decision (sc' p) = Some v"
    from this and 
      decide_origin[where \<mu>=\<mu> and HOs=HOs and sc'=sc', OF send[THEN spec, of p] nxt[THEN spec, of p]]
    show "quorum_process.locked_in_vf majs (Some \<circ> last_vote \<circ> sc) v"
      by(auto simp add: majorities.locked_in_vf_def majorities.quorum_for_def)
  qed
  hence
    "(sa, sa') \<in> majorities.flv_round r (Some o last_vote o sc) d_f" using R
    by(auto simp add: majorities.flv_round_def otr_ref_rel_def sa'_def)
  moreover have "(sa', Suc r, sc') \<in> otr_ref_rel"
  proof(unfold otr_ref_rel_def, safe)
    fix p
    show "opt_v_state.decisions sa' p = decision (sc' p)" using R nxt[THEN spec, of p]
      by(auto simp add: otr_ref_rel_def sa'_def map_add_def d_f_def OTR_nextState_def
        split: option.split)
  next
    show "quorum_process.opt_no_defection majs sa' (Some \<circ> last_vote \<circ> sc')"
    proof(clarsimp simp add: sa'_def majorities.opt_no_defection_def map_add_def majorities.quorum_for_def)
      fix Q p v
      assume Q: "Q \<in> majs" and Q_v: "\<forall>q \<in> Q. last_vote (sc q) = v" and p_Q: "p \<in> Q"
      hence old: "last_vote (sc p) = v" by simp
      have v_maj: "{q. last_vote (sc q) = v} \<in> majs" using Q Q_v
        apply(simp add: majs_def)
        apply(erule less_le_trans, rule card_mono, auto)
        done
      show "last_vote (sc' p) = v"
      proof(rule ccontr)
        assume new: "last_vote (sc' p) \<noteq> v"
        let ?w = "last_vote (sc' p)"
        have 
          w_MFR: "?w = Min {z. MFR (\<mu> p) z}" (is "?w = Min ?MFRs") and dom_maj: "dom (\<mu> p) \<in> majs" 
          using old new nxt[THEN spec, where x=p]
          by(auto simp add: OTR_nextState_def majs_def dom_def split: if_split_asm)
        from dom_maj have not_empty: "dom (\<mu> p) \<noteq> {}" by(elim majorities.quorum_non_empty)
        from MFR_exists obtain mfr_v where mfr_v: "mfr_v \<in> ?MFRs"
          by fastforce
        from not_empty obtain q z where "\<mu> p q = Some z" by(fastforce)
        hence "0 < card (HOV (\<mu> p) (the (\<mu> p q)))"
          by(auto simp add: HOV_def)
        have "?w \<in> {z. MFR (\<mu> p) z}"
        proof(unfold w_MFR, rule Min_in)
          have "?MFRs \<subseteq> (the o (\<mu> p)) ` (dom (\<mu> p))" using not_empty
            by(auto simp: image_def intro: MFR_in_msgs)
          thus "finite ?MFRs" by (auto elim: finite_subset)
        qed(auto simp add: MFR_exists)
        hence card_HOV: "card (HOV (\<mu> p) v) \<le> card (HOV (\<mu> p) ?w)"
          by(auto simp add: MFR_def)
        have "dom (\<mu> p) = HOs r p" using send[THEN spec, where x=p]
          by(auto simp add: get_msgs_def)
        from this[symmetric] have "\<forall>v'. HOV (\<mu> p) v' = {q. last_vote (sc q) = v'} \<inter> dom (\<mu> p)" 
          using send[THEN spec, where x=p]
          by(fastforce simp add: HOV_def get_msgs_benign OTR_sendMsg_def restrict_map_def)
        hence card_le1: "card ({q. last_vote (sc q) = v} \<inter> dom (\<mu> p)) \<le> card ({q. last_vote (sc q) = ?w} \<inter> dom (\<mu> p))"
          using card_HOV
          by(simp)
        have 
          "card ({q. last_vote (sc q) = v} \<inter> dom (\<mu> p)) \<le> card ({q. last_vote (sc q) \<noteq> v} \<inter> dom (\<mu> p))"
          apply(rule le_trans[OF card_le1], rule card_mono)
           apply(auto simp add: new[symmetric])
          done
        thus False using qintersect_card[OF dom_maj v_maj]
          by(simp add: Int_commute Collect_neg_eq)
      qed
    qed
  qed(auto simp add: sa'_def)

  ultimately show 
    "\<exists>sa'. (\<exists>ra v_f d_f. (sa, sa') \<in> quorum_process.flv_round majs ra v_f d_f) 
    \<and> (sa', Suc r, sc') \<in> otr_ref_rel"
    by blast
qed

lemma OTR_Refines_LV_VOting:
  "PO_refines (otr_ref_rel) 
    majorities.flv_TS (OTR_TS HOs HOs crds)"
proof(rule refine_basic)
  show "init (OTR_TS HOs HOs crds) \<subseteq> otr_ref_rel `` init (quorum_process.flv_TS majs)"
    by(auto simp add: OTR_TS_def CHO_to_TS_def OTR_Alg_def CHOinitConfig_def OTR_initState_def
      majorities.flv_TS_def flv_init_def majorities.opt_no_defection_def majorities.quorum_for_def'
      otr_ref_rel_def)
next
  show 
    "{otr_ref_rel} TS.trans (quorum_process.flv_TS majs), TS.trans (OTR_TS HOs HOs crds) {> otr_ref_rel}"
    using step_ref
    by(simp add: majorities.flv_TS_defs OTR_TS_def CHO_to_TS_def OTR_Alg_def 
      CSHO_trans_alt_def CHO_trans_alt OTR_trans_step_def)
qed

subsubsection \<open>Termination\<close>
(******************************************************************************)

text \<open>The termination proof for the algorithm is already given in the Heard-Of Model AFP
  entry, and we do not repeat it here.\<close>


end
