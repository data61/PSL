(*<*)
theory Ate_Proofs
imports "../Voting_Opt" Ate_Defs Heard_Of.Majorities 
  "../HO_Transition_System"
begin
(*>*)

subsection \<open>Proofs\<close>
axiomatization where val_linorder: 
  "OFCLASS(val, linorder_class)"

instance val :: linorder by (rule val_linorder)

context ate_parameters
begin

definition majs :: "(process set) set" where
  "majs \<equiv> {S. card S > E}"

interpretation majorities: quorum_process majs
proof
  fix Q Q' assume "Q \<in> majs" "Q' \<in> majs"
  hence "N < card Q + card Q'" using majE
    by(auto simp add: majs_def)
  thus "Q \<inter> Q' \<noteq> {}"
    apply (intro majorities_intersect)
    apply(auto)
    done
next
  from EltN
  show "\<exists>Q. Q \<in> majs" 
    apply(rule_tac x=UNIV in exI)
    apply(auto simp add: majs_def intro!: div_less_dividend)
    done
qed

type_synonym p_TS_state = "(nat \<times> (process \<Rightarrow> (val pstate)))"

definition K where
  "K y \<equiv> \<lambda>x. y"

definition Ate_Alg where
  "Ate_Alg =
    \<lparr> CinitState =  (\<lambda> p st crd. Ate_initState p st),
     sendMsg =  Ate_sendMsg,
     CnextState = (\<lambda> r p st msgs crd st'. Ate_nextState r p st msgs st')
   \<rparr>"

definition Ate_TS ::
  "(round \<Rightarrow> process HO)
  \<Rightarrow> (round \<Rightarrow> process HO)
  \<Rightarrow> (round \<Rightarrow> process)
  \<Rightarrow> p_TS_state TS"
where
  "Ate_TS HOs SHOs crds = CHO_to_TS Ate_Alg HOs SHOs (K o crds)"

lemmas Ate_TS_defs = Ate_TS_def CHO_to_TS_def Ate_Alg_def CHOinitConfig_def
  Ate_initState_def

definition
  "Ate_trans_step HOs \<equiv> \<Union>r \<mu>.
   {((r, cfg), Suc r, cfg')|cfg cfg'.
    (\<forall>p. \<mu> p \<in> get_msgs (Ate_sendMsg r) cfg (HOs r) (HOs r) p) \<and>
    (\<forall>p. Ate_nextState r p (cfg p) (\<mu> p) (cfg' p))}"

definition CSHOnextConfig where
  "CSHOnextConfig A r cfg HO SHO coord cfg' \<equiv>
   \<forall>p. \<exists>\<mu> \<in> SHOmsgVectors A r p cfg (HO p) (SHO p).
          CnextState A r p (cfg p) \<mu> (coord p) (cfg' p)"

type_synonym rHO = "nat \<Rightarrow> process HO"

subsubsection \<open>Refinement\<close>
(******************************************************************************)

definition ate_ref_rel :: "(opt_v_state \<times> p_TS_state)set" where
  "ate_ref_rel =  {(sa, (r, sc)).
    r = next_round sa
    \<and> (\<forall>p. decisions sa p = Ate_Defs.decide (sc p))
    \<and> majorities.opt_no_defection sa (Some o x o sc)
  }"

lemma decide_origin:
  assumes 
    send: "\<mu> p \<in> get_msgs (Ate_sendMsg r) sc (HOs r) (HOs r) p"
    and nxt: "Ate_nextState r p (sc p) (\<mu> p) (sc' p)"
    and new_dec: "decide (sc' p) \<noteq> decide (sc p)"
  shows
    "\<exists>v. decide (sc' p) = Some v \<and> {q. x (sc q) = v} \<in> majs" using assms
  by(auto simp add: get_msgs_benign Ate_sendMsg_def Ate_nextState_def
    majs_def restrict_map_def elim!: order.strict_trans2 intro!: card_mono)

lemma other_values_received:
  assumes nxt: "Ate_nextState  r q (sc q) \<mu>q ((sc') q)"
  and muq: "\<mu>q \<in> get_msgs (Ate_sendMsg r) sc (HOs r) (HOs r) q"
  and vsent: "card {qq. sendMsg Ate_M r qq q (sc qq) = v} > E - \<alpha>"
             (is "card ?vsent > _")
  shows "card ({qq. \<mu>q qq \<noteq> Some v} \<inter> HOs r q) \<le> N + 2*\<alpha> - E"
proof -
  from nxt muq
  have "({qq. \<mu>q qq \<noteq> Some v} \<inter> HOs r q) - (HOs r q - HOs r q)
        \<subseteq>  {qq. sendMsg Ate_M r qq q (sc qq) \<noteq> v}"
    (is "?notvrcvd - ?aho \<subseteq> ?notvsent") 
    unfolding get_msgs_def SHOmsgVectors_def Ate_SHOMachine_def by auto
  hence "card ?notvsent \<ge> card (?notvrcvd - ?aho)"
    and "card (?notvrcvd - ?aho) \<ge> card ?notvrcvd - card ?aho"
    by (auto simp: card_mono diff_card_le_card_Diff)
  moreover
  have 1: "card ?notvsent + card ?vsent = card (?notvsent \<union> ?vsent)"
    by (subst card_Un_Int) auto
  have "?notvsent \<union> ?vsent = (UNIV::process set)" by auto
  hence "card (?notvsent \<union> ?vsent) = N" by simp
  with 1 vsent have "card ?notvsent \<le>  N - (E + 1 - \<alpha>)" by auto
  ultimately
  show ?thesis using EltN Egta by auto
qed

text \<open>
  If more than \<open>E - \<alpha>\<close> processes send a value \<open>v\<close> to some
  process \<open>q\<close> at some round \<open>r\<close>, and if \<open>q\<close> receives more than
  \<open>T\<close> messages in \<open>r\<close>, then \<open>v\<close> is the most frequently
  received value by \<open>q\<close> in \<open>r\<close>.
\<close>

lemma mostOftenRcvd_v:
  assumes nxt: "Ate_nextState  r q (sc q) \<mu>q ((sc') q)"
  and muq: "\<mu>q \<in> get_msgs (Ate_sendMsg r) sc (HOs r) (HOs r) q"
  and threshold_T: "card {qq. \<mu>q qq \<noteq> None} > T"
  and threshold_E: "card {qq. sendMsg Ate_M r qq q (sc qq) = v} > E - \<alpha>"
  shows "mostOftenRcvd \<mu>q = {v}"
proof -
  from muq have hodef:"HOs r q = {qq. \<mu>q qq \<noteq> None}"
    unfolding get_msgs_def SHOmsgVectors_def by auto

  from nxt muq threshold_E
  have "card ({qq. \<mu>q qq \<noteq> Some v} \<inter> HOs r q) \<le> N + 2*\<alpha> - E"
    (is "card ?heardnotv \<le> _")
    by (rule other_values_received)
  moreover
  have "card ?heardnotv \<ge> T + 1 - card {qq. \<mu>q qq = Some v}"
  proof -
    from muq
    have "?heardnotv = (HOs r q) - {qq. \<mu>q qq = Some v}"
      and "{qq. \<mu>q qq = Some v} \<subseteq> HOs r q"
      unfolding SHOmsgVectors_def get_msgs_def by auto
    hence "card ?heardnotv = card (HOs r q) - card {qq. \<mu>q qq = Some v}"
      by (auto simp: card_Diff_subset)
    with hodef threshold_T show ?thesis by auto
  qed
  ultimately
  have "card {qq. \<mu>q qq = Some v} > card ?heardnotv"
    using TNaE by auto
  moreover
  {
    fix w
    assume w: "w \<noteq> v"
    with hodef have "{qq. \<mu>q qq = Some w} \<subseteq> ?heardnotv" by auto
    hence "card {qq. \<mu>q qq = Some w} \<le> card ?heardnotv" by (auto simp: card_mono)
  }
  ultimately
  have "{w. card {qq. \<mu>q qq = Some w} \<ge> card {qq. \<mu>q qq = Some v}} = {v}"
    by force
  thus ?thesis unfolding mostOftenRcvd_def by auto
qed

lemma step_ref:
  "{ate_ref_rel} 
      (\<Union>r v_f d_f. majorities.flv_round r v_f d_f), 
      Ate_trans_step HOs 
    {> ate_ref_rel}"
proof(simp add: PO_rhoare_defs Ate_trans_step_def, safe)
  fix sa r sc sc' \<mu>
  assume
    R: "(sa, r, sc) \<in> ate_ref_rel"
    and send: "\<forall>p. \<mu> p \<in> get_msgs (Ate_sendMsg r) sc (HOs r) (HOs r) p"
    and nxt: "\<forall>p. Ate_nextState r p (sc p) (\<mu> p) (sc' p)"
  note step=send nxt
  define d_f
    where "d_f p = (if decide (sc' p) \<noteq> decide (sc p) then decide (sc' p) else None)" for p

  define sa' where "sa' = \<lparr> 
    opt_v_state.next_round = Suc r
    , opt_v_state.last_vote = opt_v_state.last_vote sa ++ (Some o x o sc) 
    , opt_v_state.decisions = opt_v_state.decisions sa ++ d_f
    \<rparr>"
  
  have "majorities.d_guard d_f (Some o x o sc)"
  proof(clarsimp simp add: majorities.d_guard_def d_f_def)
    fix p v
    assume
      "Some v \<noteq> decide (sc p)" 
      "decide (sc' p) = Some v"
    from this and 
      decide_origin[where \<mu>=\<mu> and HOs=HOs and sc'=sc', OF send[THEN spec, of p] nxt[THEN spec, of p]]
    show "quorum_process.locked_in_vf majs (Some \<circ> x \<circ> sc) v"
      by(auto simp add: majorities.locked_in_vf_def majorities.quorum_for_def)
  qed
  hence
    "(sa, sa') \<in> majorities.flv_round r (Some o x o sc) d_f" using R
    by(auto simp add: majorities.flv_round_def ate_ref_rel_def sa'_def)
  moreover have "(sa', Suc r, sc') \<in> ate_ref_rel"
  proof(unfold ate_ref_rel_def, safe)
    fix p
    show "opt_v_state.decisions sa' p = decide (sc' p)" using R nxt[THEN spec, of p]
      by(auto simp add: ate_ref_rel_def sa'_def map_add_def d_f_def Ate_nextState_def
        split: option.split)
  next
    show "quorum_process.opt_no_defection majs sa' (Some \<circ> x \<circ> sc')"
    proof(clarsimp simp add: sa'_def majorities.opt_no_defection_def map_add_def majorities.quorum_for_def)
      fix Q p v
      assume Q: "Q \<in> majs" and Q_v: "\<forall>q \<in> Q. x (sc q) = v" and p_Q: "p \<in> Q"
      hence old: "x (sc p) = v" by simp

      have v_maj: "{q. x (sc q) = v} \<in> majs" using Q Q_v
        apply(simp add: majs_def)
        apply(erule less_le_trans, rule card_mono, auto)
        done
      show "x (sc' p) = v"
      proof(cases "T < card {qq. \<mu> p qq \<noteq> None}")
        case True
        have
          "E - \<alpha> < card {qq. sendMsg Ate_M r qq p (sc qq) = v}" using v_maj
          by(auto simp add: Ate_SHOMachine_def Ate_sendMsg_def majs_def)
        from mostOftenRcvd_v[where HOs=HOs and sc=sc and sc'=sc', 
          OF nxt[THEN spec, of p] send[THEN spec, of p] True this]
        show ?thesis using nxt[THEN spec, of p] old
          by(clarsimp simp add: Ate_nextState_def)
      next
        case False
        thus ?thesis using nxt[THEN spec, of p] old
          by(clarsimp simp add: Ate_nextState_def)
      qed
    qed
  qed(auto simp add: sa'_def)

  ultimately show 
    "\<exists>sa'. (\<exists>ra v_f d_f. (sa, sa') \<in> quorum_process.flv_round majs ra v_f d_f) 
    \<and> (sa', Suc r, sc') \<in> ate_ref_rel"
    by blast
qed

lemma Ate_Refines_LV_VOting:
  "PO_refines (ate_ref_rel) 
    majorities.flv_TS (Ate_TS HOs HOs crds)"
proof(rule refine_basic)
  show "init (Ate_TS HOs HOs crds) \<subseteq> ate_ref_rel `` init (quorum_process.flv_TS majs)"
    by(auto simp add: Ate_TS_def CHO_to_TS_def Ate_Alg_def CHOinitConfig_def Ate_initState_def
      majorities.flv_TS_def flv_init_def majorities.opt_no_defection_def majorities.quorum_for_def'
      ate_ref_rel_def)
next
  show 
    "{ate_ref_rel} TS.trans (quorum_process.flv_TS majs), TS.trans (Ate_TS HOs HOs crds) {> ate_ref_rel}"
    using step_ref
    by(simp add: majorities.flv_TS_defs Ate_TS_def CHO_to_TS_def Ate_Alg_def 
      CSHO_trans_alt_def CHO_trans_alt Ate_trans_step_def)
qed

end   \<comment> \<open>context @{text "ate_parameters"}\<close>

subsubsection \<open>Termination\<close>
(******************************************************************************)

text \<open>The termination proof for the algorithm is already given in the Heard-Of Model AFP
  entry, and we do not repeat it here.\<close>

end   (* theory AteProof *)

