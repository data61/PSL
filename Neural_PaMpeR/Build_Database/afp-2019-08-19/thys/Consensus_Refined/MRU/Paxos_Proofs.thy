(*<*)
theory Paxos_Proofs
imports Three_Step_MRU "../HO_Transition_System" Heard_Of.Majorities "../Quorums" Paxos_Defs
begin
(*>*)

subsection \<open>Proofs\<close>

type_synonym p_TS_state = "(nat \<times> (process \<Rightarrow> (val pstate)))"

definition Paxos_TS ::
  "(round \<Rightarrow> process HO)
  \<Rightarrow> (round \<Rightarrow> process HO)
  \<Rightarrow> (round \<Rightarrow> process)
  \<Rightarrow> p_TS_state TS"
where
  "Paxos_TS HOs SHOs crds = CHO_to_TS Paxos_Alg HOs SHOs (K o crds)"

lemmas Paxos_TS_defs = Paxos_TS_def CHO_to_TS_def Paxos_Alg_def CHOinitConfig_def
  Paxos_initState_def

definition Paxos_trans_step where
  "Paxos_trans_step HOs SHOs crds nxt_f snd_f stp \<equiv> \<Union>r \<mu>.
    {((r, cfg), (Suc r, cfg'))|cfg cfg'. three_step r = stp  \<and> (\<forall>p.
      \<mu> p \<in> get_msgs (snd_f r) cfg (HOs r) (SHOs r) p
      \<and> nxt_f r p (cfg p) (\<mu> p) (crds r) (cfg' p)
    )}"

lemma three_step_less_D:
  "0 < three_step r \<Longrightarrow> three_step r = 1 \<or> three_step r = 2"
  by(unfold three_step_def, arith)

lemma Paxos_trans:
  "CSHO_trans_alt Paxos_sendMsg Paxos_nextState HOs SHOs (K \<circ> crds) = 
  Paxos_trans_step HOs SHOs crds next0 send0 0
  \<union> Paxos_trans_step HOs SHOs crds next1 send1 1
  \<union> Paxos_trans_step HOs SHOs crds next2 send2 2
  "
proof(rule equalityI)
  show "CSHO_trans_alt Paxos_sendMsg Paxos_nextState HOs SHOs (K \<circ> crds)
    \<subseteq> Paxos_trans_step HOs SHOs crds next0 send0 0 \<union>
       Paxos_trans_step HOs SHOs crds next1 send1 1 \<union>
       Paxos_trans_step HOs SHOs crds next2 send2 2"
  by(force simp add: CSHO_trans_alt_def Paxos_sendMsg_def Paxos_nextState_def 
    Paxos_trans_step_def K_def dest!: three_step_less_D)
next
  show "Paxos_trans_step HOs SHOs crds next0 send0 0 \<union>
    Paxos_trans_step HOs SHOs crds next1 send1 1 \<union>
    Paxos_trans_step HOs SHOs crds next2 send2 2
    \<subseteq> CSHO_trans_alt Paxos_sendMsg Paxos_nextState HOs SHOs (K \<circ> crds)"
  by(force simp add: CSHO_trans_alt_def Paxos_sendMsg_def Paxos_nextState_def 
    Paxos_trans_step_def K_def)
qed

type_synonym rHO = "nat \<Rightarrow> process HO"

subsubsection \<open>Refinement\<close>
(******************************************************************************)

definition coord_vote_to_set :: "nat \<Rightarrow> (process \<Rightarrow> (val pstate)) \<Rightarrow> val set" where
  "coord_vote_to_set r sc \<equiv> (let v = pstate.commt (sc (coord r)) in 
      if v = None 
          then {}
          else {the v})"

definition paxos_ref_rel :: "(three_step_mru_state \<times> p_TS_state)set" where
  "paxos_ref_rel = {(sa, (r, sc)).
    opt_mru_state.next_round sa = r
    \<and> opt_mru_state.decisions sa = pstate.decide o sc
    \<and> opt_mru_state.mru_vote sa = pstate.mru_vote o sc
    \<and> (three_step r = Suc 0 \<longrightarrow> three_step_mru_state.candidates sa = coord_vote_to_set r sc)
  }"

lemma mru_vote_evolution0:
  "\<forall>p. next0 r p (s p) (msgs p) (crd p) (s' p) \<Longrightarrow> mru_vote o s' = mru_vote o s"
  apply(rule_tac[!] ext, rename_tac x, erule_tac[!] x=x in allE)
  by(auto simp add: next0_def next2_def Let_def)

lemma mru_vote_evolution2:
  "\<forall>p. next2 r p (s p) (msgs p) (crd p) (s' p) \<Longrightarrow> mru_vote o s' = mru_vote o s"
  apply(rule_tac[!] ext, rename_tac x, erule_tac[!] x=x in allE)
  by(auto simp add: next0_def next2_def Let_def)

lemma decide_evolution:
  "\<forall>p. next0 r p (s p) (msgs p) (crd p) (s' p) \<Longrightarrow> decide o s = decide o s'"
  "\<forall>p. next1 r p (s p) (msgs p) (crd p) (s' p) \<Longrightarrow> decide o s = decide o s'"
  apply(rule_tac[!] ext, rename_tac x, erule_tac[!] x=x in allE)
  by(auto simp add: next0_def next1_def Let_def)

lemma msgs_mru_vote: 
  assumes
  "\<mu> (coord r) \<in> get_msgs (send0 r) cfg (HOs r) (HOs r) (coord r)" (is "\<mu> ?p \<in> _")
  shows "((msgs_to_lvs (\<mu> ?p)) |` HOs r ?p) = (mru_vote o cfg) |` HOs r ?p" using assms
  by(auto simp add: get_msgs_benign send0_def restrict_map_def msgs_to_lvs_def
      mru_vote_to_msg_def map_comp_def intro!: ext split: option.split)

lemma step0_ref:
  "{paxos_ref_rel} 
    (\<Union>r C. majorities.opt_mru_step0 r C), 
    Paxos_trans_step HOs HOs crds next0 send0 0 {> paxos_ref_rel}"
proof(clarsimp simp add: PO_rhoare_defs Paxos_trans_step_def all_conj_distrib)
  fix r sa sc sc' \<mu>
  assume R: "(sa, (r, sc)) \<in> paxos_ref_rel"
    and r: "three_step r = 0"
    and \<mu>: "\<forall>p. \<mu> p \<in> get_msgs (send0 r) sc (HOs r) (HOs r) p"
        and nxt: "\<forall>p. next0 r p (sc p) (\<mu> p) (crds r) (sc' p)"
  note \<mu>nxt = \<mu> nxt
  from r have same_coord: "coord (Suc r) = coord r"
    by(auto simp add: three_step_phase_Suc intro: coord_phase)
  define C where "C = coord_vote_to_set (Suc r) sc'"
  have guard: "\<forall>cand\<in>C. \<exists>Q. majorities.opt_mru_guard (mru_vote \<circ> sc) Q cand"
  proof
    fix cand
    assume cand: "cand \<in> C"
    hence Some: "commt (sc' (coord r)) = Some cand" using nxt[THEN spec, where x="coord r"]
      by(auto simp add: C_def coord_vote_to_set_def Let_def same_coord)

    let ?Q = "HOs r (coord r)"
    let ?lvs0 = "mru_vote o sc"

    have "?Q \<in> majs" using Some \<mu>nxt[THEN spec, where x="coord r"]
      by(auto simp add: Let_def majs_def next0_def same_coord get_msgs_dom)
    moreover have
      "map_option snd (option_Max_by fst (ran (?lvs |` ?Q))) \<in> {None, Some cand}"
      using Some nxt[THEN spec, where x="coord r"]
      msgs_mru_vote[where HOs=HOs and \<mu>=\<mu>, OF \<mu>[THEN spec, where x="coord r"]] 
      get_msgs_dom[OF \<mu>[THEN spec, of "coord r"]]
      by(auto simp add: next0_def Let_def split: option.split_asm)
    ultimately have "majorities.opt_mru_guard ?lvs0 ?Q cand"
      by(auto simp add: majorities.opt_mru_guard_def Let_def majorities.opt_mru_vote_def)
    thus "\<exists>Q. majorities.opt_mru_guard ?lvs0 Q cand"
      by blast
  qed

  define sa' where "sa' = sa\<lparr>
      next_round := Suc r,
      candidates := C
    \<rparr>"
  have "(sa, sa') \<in> majorities.opt_mru_step0 r C" using R r nxt guard
    by(auto simp add: majorities.opt_mru_step0_def sa'_def paxos_ref_rel_def)
  moreover have "(sa', (Suc r, sc')) \<in> paxos_ref_rel" using R nxt
    apply(auto simp add: sa'_def paxos_ref_rel_def intro!:
      mru_vote_evolution0[OF nxt, symmetric] decide_evolution(1)[OF nxt])
       apply(auto simp add: Let_def C_def o_def intro!: ext)
    done
  ultimately show 
    "\<exists>sa'. (\<exists>r C. (sa, sa') \<in> majorities.opt_mru_step0 r C) 
        \<and> (sa', Suc r, sc') \<in> paxos_ref_rel"
    by blast
qed

lemma step1_ref:
  "{paxos_ref_rel} 
    (\<Union>r S v. majorities.opt_mru_step1 r S v), 
    Paxos_trans_step HOs HOs crds next1 send1 (Suc 0) {> paxos_ref_rel}"
proof(clarsimp  simp add: PO_rhoare_defs Paxos_trans_step_def all_conj_distrib)
  fix r sa sc sc' \<mu>
  assume R: "(sa, (r, sc)) \<in> paxos_ref_rel"
    and r: "three_step r = Suc 0"
    and \<mu>: "\<forall>p. \<mu> p \<in> get_msgs (send1 r) sc (HOs r) (HOs r) p"
        and nxt: "\<forall>p. next1 r p (sc p) (\<mu> p) (crds r) (sc' p)"
  note \<mu>nxt = \<mu> nxt

  define v where "v = the (commt (sc (coord r)))"
  define S where "S = {p. coord r \<in> HOs r p \<and> commt (sc (coord r)) \<noteq> None}"
  define sa' where "sa' = sa\<lparr> next_round := Suc r, 
    opt_mru_state.mru_vote := opt_mru_state.mru_vote sa ++ const_map (three_phase r, v) S
  \<rparr>"
  have "(sa, sa') \<in> majorities.opt_mru_step1 r S v" using r R 
    by(clarsimp simp add: majorities.opt_mru_step1_def sa'_def  S_def v_def 
      coord_vote_to_set_def paxos_ref_rel_def)
  moreover have "(sa', (Suc r, sc')) \<in> paxos_ref_rel" using r R
  proof-
    have "mru_vote o sc' = ((mru_vote \<circ> sc) ++ const_map (three_phase r, v) S)"
    proof(rule ext, simp)
      fix p
      show "mru_vote (sc' p) = ((mru_vote \<circ> sc) ++ const_map (three_phase r, v) S) p"
        using \<mu>nxt[THEN spec, of p]
        by(auto simp add: get_msgs_benign next1_def send1_def S_def v_def map_add_def 
          const_map_is_None const_map_is_Some restrict_map_def isVote_def split: option.split)
    qed
    thus ?thesis using R r nxt
      by(force simp add: paxos_ref_rel_def sa'_def three_step_Suc intro: decide_evolution)
  qed      
  ultimately show 
    "\<exists>sa'. (\<exists>r S v. (sa, sa') \<in> majorities.opt_mru_step1 r S v) 
        \<and> (sa', Suc r, sc') \<in> paxos_ref_rel"
    by blast
qed

lemma step2_ref:
  "{paxos_ref_rel} 
    (\<Union>r dec_f. majorities.opt_mru_step2 r dec_f), 
    Paxos_trans_step HOs HOs crds next2 send2 2 {> paxos_ref_rel}"
proof(clarsimp  simp add: PO_rhoare_defs Paxos_trans_step_def all_conj_distrib)
  fix r sa sc sc' \<mu>
  assume R: "(sa, (r, sc)) \<in> paxos_ref_rel"
    and r: "three_step r = 2"
    and \<mu>: "\<forall>p. \<mu> p \<in> get_msgs (send2 r) sc (HOs r) (HOs r) p"
        and nxt: "\<forall>p. next2 r p (sc p) (\<mu> p) (crds r) (sc' p)"
  note \<mu>nxt = \<mu> nxt

  define dec_f
    where "dec_f p = (if decide (sc' p) \<noteq> decide (sc p) then decide (sc' p) else None)" for p

  have dec_f: "(decide \<circ> sc) ++ dec_f = decide \<circ> sc'"
  proof
    fix p
    show "((decide \<circ> sc) ++ dec_f) p = (decide \<circ> sc') p" using nxt[THEN spec, of p]
      by(auto simp add: map_add_def dec_f_def next2_def split: option.split intro!: ext)
  qed

  define sa' where "sa' = sa\<lparr>
    next_round := Suc r,
    decisions := decisions sa ++ dec_f
  \<rparr>"

  have "(sa', (Suc r, sc')) \<in> paxos_ref_rel" using R r nxt
    by(auto simp add: paxos_ref_rel_def sa'_def dec_f three_step_Suc 
      mru_vote_evolution2[OF nxt])
  moreover have "(sa, sa') \<in> majorities.opt_mru_step2 r dec_f" using r R
  proof-
    define sc_r_votes where "sc_r_votes p = (if (\<exists>v. mru_vote (sc p) = Some (three_phase r, v))
        then map_option snd (mru_vote (sc p))
        else None)" for p
    have sc_r_votes: "sc_r_votes = majorities.r_votes sa r" using R r
      by(auto simp add: paxos_ref_rel_def sc_r_votes_def majorities.r_votes_def intro!: ext)
    have "majorities.step2_d_guard dec_f sc_r_votes"
    proof(clarsimp simp add: majorities.step2_d_guard_def)
      fix p v
      assume d_f_p: "dec_f p = Some v"
      let ?Qv = "votes_rcvd (\<mu> p)"
      have Qv: "card ?Qv > N div 2" 
        "v = the_rcvd_vote (\<mu> p)" using nxt[THEN spec, of p] d_f_p
        by(auto simp add: next2_def dec_f_def)

      hence "v \<in> snd ` votes_rcvd (\<mu> p)"
        by(fastforce simp add: the_rcvd_vote_def ex_in_conv[symmetric]
          dest!: card_gt_0_iff[THEN iffD1, OF le_less_trans[OF le0]] elim!: imageI intro: someI)
      moreover have "?Qv = map_graph (sc_r_votes) \<inter> (HOs r p \<times> UNIV)" using \<mu>[THEN spec, of p]
        by(auto simp add: get_msgs_benign send2_def restrict_map_def votes_rcvd_def
          sc_r_votes_def image_def split: option.split_asm)
      ultimately show "v \<in> ran sc_r_votes \<and> dom sc_r_votes \<in> majs" using Qv(1)
        by(auto simp add: majs_def inj_on_def map_graph_def fun_graph_def sc_r_votes_def
          the_rcvd_vote_def majs_def intro: ranI
          elim!: less_le_trans intro!: card_inj_on_le[where f=fst])
    qed

    thus ?thesis using r R
      by(auto simp add: majorities.opt_mru_step2_def sa'_def paxos_ref_rel_def sc_r_votes)
  qed

  ultimately show 
    "\<exists>sa'. (\<exists>r dec_f. (sa, sa') \<in> majorities.opt_mru_step2 r dec_f) 
        \<and> (sa', Suc r, sc') \<in> paxos_ref_rel"
    by blast

qed

lemma Paxos_Refines_ThreeStep_MRU:
  "PO_refines paxos_ref_rel 
    majorities.ts_mru_TS (Paxos_TS HOs HOs crds)"
proof(rule refine_basic)
  show "init (Paxos_TS HOs HOs crds) \<subseteq> paxos_ref_rel `` init majorities.ts_mru_TS"
    by(auto simp add: Paxos_TS_defs majorities.ts_mru_TS_def paxos_ref_rel_def 
      majorities.ts_mru_init_def)
next
  show 
    "{paxos_ref_rel} TS.trans majorities.ts_mru_TS, 
      TS.trans (Paxos_TS HOs HOs crds) {> paxos_ref_rel}"
    apply(simp add: majorities.ts_mru_TS_defs Paxos_TS_defs)
    apply(auto simp add: CHO_trans_alt Paxos_trans intro!: step0_ref step1_ref step2_ref)
    done
qed

subsubsection \<open>Termination\<close>
(******************************************************************************)

theorem Paxos_termination:
  assumes run: "CHORun Paxos_Alg rho HOs crds"
      and commR: "\<forall>r. CHOcommPerRd Paxos_M r (HOs r) (crds r)"
      and commG: "CHOcommGlobal Paxos_M HOs crds"
  shows "\<exists>r v. decide (rho r p) = Some v"
proof -
  from commG obtain ph c where 
    HOs:
       "coord (nr_steps*ph) = c
         \<and> card (HOs (nr_steps*ph) c) > N div 2
         \<and> (\<forall>p. c \<in> HOs (nr_steps*ph+1) p)
         \<and> (\<forall>p. card (HOs (nr_steps*ph+2) p) > N div 2)"
    by(auto simp add: Paxos_CHOMachine_def Paxos_commGlobal_def)

  \<comment> \<open>The tedious bit: obtain three consecutive rounds linked by send/next functions\<close>
  define r0 where "r0 = nr_steps * ph"
  define cfg0 where "cfg0 = rho r0"
  define r1 where "r1 = Suc r0"
  define cfg1 where "cfg1 = rho r1"
  define r2 where "r2 = Suc r1"
  define cfg2 where "cfg2 = rho r2"
  define cfg3 where "cfg3 = rho (Suc r2)"

  from   
    run[simplified CHORun_def, THEN CSHORun_step, THEN spec, where x="r0"] 
    run[simplified CHORun_def, THEN CSHORun_step, THEN spec, where x="r1"]
    run[simplified CHORun_def, THEN CSHORun_step, THEN spec, where x="r2"] 
    obtain \<mu>0 \<mu>1 \<mu>2 where
    send0: "\<forall>p. \<mu>0 p \<in> get_msgs (send0 r0) cfg0 (HOs r0) (HOs r0) p"
    and three_step0: "\<forall>p. next0 r0 p (cfg0 p) (\<mu>0 p) (crds (Suc r0) p) (cfg1 p)"
    and send1: "\<forall>p. \<mu>1 p \<in> get_msgs (send1 r1) cfg1 (HOs r1) (HOs r1) p"
    and three_step1: "\<forall>p. next1 r1 p (cfg1 p) (\<mu>1 p) (crds (Suc r1) p) (cfg2 p)"
    and send2: "\<forall>p. \<mu>2 p \<in> get_msgs (send2 r2) cfg2 (HOs r2) (HOs r2) p"
    and three_step2: "\<forall>p. next2 r2 p (cfg2 p) (\<mu>2 p) (crds (Suc r2) p) (cfg3 p)"
    apply(auto simp add: Paxos_Alg_def three_step_def Paxos_nextState_def Paxos_sendMsg_def all_conj_distrib
      r0_def r1_def r2_def
      cfg0_def cfg1_def cfg2_def cfg3_def mod_Suc
      )
    done
    
  \<comment> \<open>The proof: the coordinator hears enough messages in r0 and thus selects a value.\<close>

  from HOs three_step0[THEN spec, of c] send0[THEN spec, of c]
    have 
    "commt (cfg1 c) \<noteq> None"
    by(auto simp add: next0_def Let_def r0_def get_msgs_dom)

  then obtain dec_v where dec_v: "commt (cfg1 c) = Some dec_v"
    by (metis option.collapse)

  have step_r0: "three_step r0 = 0"
    by(auto simp add: r0_def three_step_def)
  hence same_coord: 
    "coord r1 = coord r0"
    "coord r2 = coord r0"
    by(auto simp add: three_step_phase_Suc r2_def r1_def r0_def intro!: coord_phase)

  \<comment> \<open>All processes hear from the coordinator, and thus set their vote to @{term dec_v}.\<close>  
  hence all_vote: "\<forall>p. mru_vote (cfg2 p) = Some (three_phase r2, dec_v)"
    using HOs three_step1 send1 step_r0 dec_v
    by(auto simp add: next1_def Let_def get_msgs_benign send1_def restrict_map_def isVote_def
      r2_def r1_def r0_def[symmetric] same_coord[simplified r2_def r1_def] three_step_phase_Suc)

  \<comment> \<open>And finally, everybody will also decide @{term dec_v}.\<close>
  have all_decide: "\<forall>p. decide (cfg3 p) = Some dec_v"
  proof
    fix p
    have "votes_rcvd (\<mu>2 p) = HOs r2 p \<times> {dec_v}" using send2[THEN spec, where x=p] all_vote
      by(auto simp add: send2_def get_msgs_benign votes_rcvd_def restrict_map_def image_def o_def)

    moreover from HOs have "N div 2 < card (HOs r2 p)"
      by(auto simp add: r2_def r1_def r0_def)

    moreover then have "HOs r2 p \<noteq> {}"
      by (metis card_empty less_nat_zero_code)
    ultimately show "decide (cfg3 p) = Some dec_v" 
    using three_step2[THEN spec, where x=p] send2[THEN spec, where x=p] all_vote
      by(auto simp add: next2_def send2_def Let_def get_msgs_benign 
        the_rcvd_vote_def restrict_map_def image_def o_def)
  qed
    
  thus ?thesis 
    by(auto simp add: cfg3_def)

qed

end
