(*<*)
theory New_Algorithm_Proofs
imports Three_Step_MRU New_Algorithm_Defs "../HO_Transition_System"
  Heard_Of.Majorities "../Quorums"
begin
(*>*)

subsection \<open>Proofs\<close>
type_synonym p_TS_state = "(nat \<times> (process \<Rightarrow> pstate))"

definition New_Algo_TS ::
  "(round \<Rightarrow> process HO) \<Rightarrow> (round \<Rightarrow> process HO) \<Rightarrow> (round \<Rightarrow> process) \<Rightarrow> p_TS_state TS"
where
  "New_Algo_TS HOs SHOs crds = CHO_to_TS New_Algo_Alg HOs SHOs (K o crds)"

lemmas New_Algo_TS_defs = New_Algo_TS_def CHO_to_TS_def New_Algo_Alg_def CHOinitConfig_def
  NA_initState_def

definition New_Algo_trans_step where
  "New_Algo_trans_step HOs SHOs crds nxt_f snd_f stp \<equiv> \<Union>r \<mu>.
    {((r, cfg), (Suc r, cfg'))|cfg cfg'. three_step r = stp  \<and> (\<forall>p.
      \<mu> p \<in> get_msgs (snd_f r) cfg (HOs r) (SHOs r) p
      \<and> nxt_f r p (cfg p) (\<mu> p) (crds r) (cfg' p)
    )}"

lemma three_step_less_D:
  "0 < three_step r \<Longrightarrow> three_step r = 1 \<or> three_step r = 2"
  by(unfold three_step_def, arith)

lemma New_Algo_trans:
  "CSHO_trans_alt NA_sendMsg NA_nextState HOs SHOs (K \<circ> crds) = 
  New_Algo_trans_step HOs SHOs crds next0 send0 0
  \<union> New_Algo_trans_step HOs SHOs crds next1 send1 1
  \<union> New_Algo_trans_step HOs SHOs crds next2 send2 2
  "
proof(rule equalityI)
  show "CSHO_trans_alt NA_sendMsg NA_nextState HOs SHOs (K \<circ> crds)
    \<subseteq> New_Algo_trans_step HOs SHOs crds next0 send0 0 \<union>
       New_Algo_trans_step HOs SHOs crds next1 send1 1 \<union>
       New_Algo_trans_step HOs SHOs crds next2 send2 2"
  by(force simp add: CSHO_trans_alt_def NA_sendMsg_def NA_nextState_def 
    New_Algo_trans_step_def K_def dest!: three_step_less_D)
next
  show "New_Algo_trans_step HOs SHOs crds next0 send0 0 \<union>
    New_Algo_trans_step HOs SHOs crds next1 send1 1 \<union>
    New_Algo_trans_step HOs SHOs crds next2 send2 2
    \<subseteq> CSHO_trans_alt NA_sendMsg NA_nextState HOs SHOs (K \<circ> crds)"
  by(force simp add: CSHO_trans_alt_def NA_sendMsg_def NA_nextState_def 
    New_Algo_trans_step_def K_def)
qed

type_synonym rHO = "nat \<Rightarrow> process HO"

subsubsection \<open>Refinement\<close>
(******************************************************************************)

definition new_algo_ref_rel :: "(three_step_mru_state \<times> p_TS_state)set" where
  "new_algo_ref_rel = {(sa, (r, sc)).
    opt_mru_state.next_round sa = r
    \<and> opt_mru_state.decisions sa = pstate.decide o sc
    \<and> opt_mru_state.mru_vote sa = pstate.mru_vote o sc
    \<and> (three_step r = Suc 0 \<longrightarrow> three_step_mru_state.candidates sa = ran (prop_vote o sc))
  }"

text \<open>
  Different types seem to be derived for the two \<open>mru_vote_evolution\<close> lemmas,
  so we state them separately.\<close>
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
  "\<mu> p \<in> get_msgs (send0 r) cfg (HOs r) (HOs r) p"
  shows "((msgs_to_lvs (\<mu> p)) |` HOs r p) = (mru_vote o cfg) |` HOs r p" using assms
  by(auto simp add: get_msgs_benign send0_def restrict_map_def msgs_to_lvs_def
      map_comp_def intro!: ext split: option.split)

lemma step0_ref:
  "{new_algo_ref_rel} 
    (\<Union>r C. majorities.opt_mru_step0 r C), 
    New_Algo_trans_step HOs HOs crds next0 send0 0 {> new_algo_ref_rel}"
proof(clarsimp simp add: PO_rhoare_defs New_Algo_trans_step_def all_conj_distrib)
  fix r sa sc sc' \<mu>
  assume R: "(sa, (r, sc)) \<in> new_algo_ref_rel"
    and r: "three_step r = 0"
    and \<mu>: "\<forall>p. \<mu> p \<in> get_msgs (send0 r) sc (HOs r) (HOs r) p"
        and nxt: "\<forall>p. next0 r p (sc p) (\<mu> p) (crds r) (sc' p)"
  note \<mu>nxt = \<mu> nxt
  have r_phase_step: "nr_steps * three_phase r = r" using r three_phase_step[of r]
    by(auto)
  define C where "C = ran (prop_vote o sc')"
  have guard: "\<forall>cand\<in>C. \<exists>Q. majorities.opt_mru_guard (mru_vote \<circ> sc) Q cand"
  proof(simp add: C_def ran_def, safe)
    fix p cand
    assume Some: "prop_vote (sc' p) = Some cand"

    let ?Q = "HOs r p"
    let ?lvs0 = "mru_vote o sc"

    have "?Q \<in> majs" using Some \<mu>nxt[THEN spec, where x=p]
      by(auto simp add: Let_def majs_def next0_def get_msgs_dom)

    moreover have
      "map_option snd (option_Max_by fst (ran (?lvs |` ?Q))) \<in> {None, Some cand}"
      using Some nxt[THEN spec, where x=p]
      msgs_mru_vote[where HOs=HOs and \<mu>=\<mu>, OF \<mu>[THEN spec, of p]]
      get_msgs_dom[OF \<mu>[THEN spec, of p]]
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
    by(auto simp add: majorities.opt_mru_step0_def sa'_def new_algo_ref_rel_def)
  moreover have "(sa', (Suc r, sc')) \<in> new_algo_ref_rel" using R nxt
    apply(auto simp add: sa'_def new_algo_ref_rel_def intro!:
      mru_vote_evolution0[OF nxt, symmetric] decide_evolution(1)[OF nxt]
    )
       apply(auto simp add: Let_def C_def o_def intro!: ext)
    done
  ultimately show 
    "\<exists>sa'. (\<exists>r C. (sa, sa') \<in> majorities.opt_mru_step0 r C) 
        \<and> (sa', Suc r, sc') \<in> new_algo_ref_rel"
    by blast
qed

lemma step1_ref:
  "{new_algo_ref_rel} 
    (\<Union>r S v. majorities.opt_mru_step1 r S v), 
    New_Algo_trans_step HOs HOs crds next1 send1 (Suc 0) {> new_algo_ref_rel}"
proof(clarsimp  simp add: PO_rhoare_defs New_Algo_trans_step_def all_conj_distrib)
  fix r sa sc sc' \<mu>
  assume R: "(sa, (r, sc)) \<in> new_algo_ref_rel"
    and r: "three_step r = Suc 0"
    and \<mu>: "\<forall>p. \<mu> p \<in> get_msgs (send1 r) sc (HOs r) (HOs r) p"
        and nxt: "\<forall>p. next1 r p (sc p) (\<mu> p) (crds r) (sc' p)"
  note \<mu>nxt = \<mu> nxt

  define S where "S = {p. mru_vote (sc' p) \<noteq> mru_vote (sc p)}"

  have S: "S \<subseteq> {p. \<exists>Q v. Q \<subseteq> HOs r p
      \<and> (\<forall>q \<in> Q. prop_vote (sc q) = Some v)
      \<and> Q \<in> majs
      \<and> (mru_vote (sc' p) = Some (three_phase r, v))
    }"
  proof(safe)
    fix p
    assume "p \<in> S"
    then obtain Q v 
      where 
      "\<forall>q \<in> Q. \<mu> p q = Some (PreVote v)"
      and maj_Q: "Q \<in> majs"
      and Q_HOs: "Q \<subseteq> dom (\<mu> p)"
      and lv: "mru_vote (sc' p) = Some (three_phase r, v)" (is "?LV v")
      using nxt[THEN spec, where x=p]
      by(clarsimp simp add: next1_def Let_def S_def majs_def Q_prevotes_v_def)
  
    then have 
      "\<forall>q \<in> Q. prop_vote (sc q) = Some v" (is "?P Q v")
      "Q \<subseteq> HOs r p"
      using \<mu>[THEN spec, where x=p]
      by(auto simp add: get_msgs_benign send1_def restrict_map_def split: option.split_asm)
    
    with maj_Q and lv show "\<exists>Q v. Q \<subseteq> HOs r p \<and> ?P Q v \<and> Q \<in> majs \<and> ?LV v" by blast
  qed    

  obtain v where 
    v: "\<forall>p \<in> S. mru_vote (sc' p) = Some (three_phase r, v) \<and> v \<in> ran (prop_vote o sc)"
  proof(cases "S = {}")
    case False
    assume asm: 
      "\<And>v. \<forall>p\<in>S. pstate.mru_vote (sc' p) = Some (three_phase r, v) \<and> v \<in> ran (prop_vote o sc)  
        \<Longrightarrow> thesis"
    from False obtain p where "p \<in> S" by auto
    with S nxt
      obtain Q v 
      where prop_vote: "(\<forall>q \<in> Q. prop_vote (sc q) = Some v)" and maj_Q: "Q \<in> majs" 
      by auto
      
    hence "\<forall>p\<in>S. pstate.mru_vote (sc' p) = Some (three_phase r, v)" (is "?LV(v)")
      using S
      by(fastforce dest!: subsetD dest: majorities.qintersect)
    
    with asm prop_vote maj_Q show thesis
      by (metis all_not_in_conv comp_eq_dest_lhs majorities.empty_not_quorum ranI)
  qed(auto)

  define sa' where "sa' = sa\<lparr> next_round := Suc r, 
    opt_mru_state.mru_vote := opt_mru_state.mru_vote sa ++ const_map (three_phase r, v) S
  \<rparr>"

  have "(sa, sa') \<in> majorities.opt_mru_step1 r S v" using r R v
    by(clarsimp simp add: majorities.opt_mru_step1_def sa'_def 
      new_algo_ref_rel_def ball_conj_distrib)

  moreover have "(sa', (Suc r, sc')) \<in> new_algo_ref_rel" using r R
  proof-
    have "mru_vote o sc' = ((mru_vote \<circ> sc) ++ const_map (three_phase r, v) S)"
    proof(rule ext, simp)
      fix p
      show "mru_vote (sc' p) = ((mru_vote \<circ> sc) ++ const_map (three_phase r, v) S) p"
        using v
        by(auto simp add: S_def map_add_def const_map_is_None const_map_is_Some split: option.split)
    qed
    thus ?thesis using R r nxt
      by(force simp add: new_algo_ref_rel_def sa'_def three_step_Suc intro: decide_evolution)
  qed      
  ultimately show 
    "\<exists>sa'. (\<exists>r S v. (sa, sa') \<in> majorities.opt_mru_step1 r S v) 
        \<and> (sa', Suc r, sc') \<in> new_algo_ref_rel"
    by blast
qed

lemma step2_ref:
  "{new_algo_ref_rel} 
    (\<Union>r dec_f. majorities.opt_mru_step2 r dec_f), 
    New_Algo_trans_step HOs HOs crds next2 send2 2 {> new_algo_ref_rel}"
proof(clarsimp  simp add: PO_rhoare_defs New_Algo_trans_step_def all_conj_distrib)
  fix r sa sc sc' \<mu>
  assume R: "(sa, (r, sc)) \<in> new_algo_ref_rel"
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
      by(auto simp add: map_add_def dec_f_def next2_def Let_def split: option.split intro!: ext)
  qed

  define sa' where "sa' = sa\<lparr>
    next_round := Suc r,
    decisions := decisions sa ++ dec_f
  \<rparr>"

  have "(sa', (Suc r, sc')) \<in> new_algo_ref_rel" using R r nxt
    by(auto simp add: new_algo_ref_rel_def sa'_def dec_f three_step_Suc 
      mru_vote_evolution2[OF nxt])
  moreover have "(sa, sa') \<in> majorities.opt_mru_step2 r dec_f" using r R
  proof-
    define sc_r_votes where "sc_r_votes p = (if (\<exists>v. mru_vote (sc p) = Some (three_phase r, v))
        then map_option snd (mru_vote (sc p))
        else None)" for p
    have sc_r_votes: "sc_r_votes = majorities.r_votes sa r" using R r
      by(auto simp add: new_algo_ref_rel_def sc_r_votes_def majorities.r_votes_def intro!: ext)
    have "majorities.step2_d_guard dec_f sc_r_votes"
    proof(clarsimp simp add: majorities.step2_d_guard_def)
      fix p v
      assume d_f_p: "dec_f p = Some v"
      then obtain Q where Q: 
        "Q \<in> majs"
        and vote: "Q \<subseteq> HOs r p" "\<forall>q\<in>Q. \<mu> p q = Some (Vote v)"
        using nxt[THEN spec, of p] d_f_p
        by(auto simp add: next2_def dec_f_def Q'_votes_v_def Let_def majs_def)
      have mru_vote: "\<forall>q\<in>Q. mru_vote (sc q) = Some (three_phase r, v)"  using vote \<mu>[THEN spec, of p]
        by(fastforce simp add: get_msgs_benign send2_def sc_r_votes_def restrict_map_def 
          split: option.split_asm if_split_asm)
      hence "dom sc_r_votes \<in> majs"
        by(auto intro!:  majorities.mono_quorum[OF Q] simp add: sc_r_votes_def)
      moreover have "v \<in> ran sc_r_votes" using Q[THEN majorities.quorum_non_empty] mru_vote
        by(force simp add: sc_r_votes_def ex_in_conv[symmetric] intro: ranI)
      ultimately show "v \<in> ran sc_r_votes \<and> dom sc_r_votes \<in> majs" 
        by blast
    qed

    thus ?thesis using r R
      by(auto simp add: majorities.opt_mru_step2_def sa'_def new_algo_ref_rel_def sc_r_votes)
  qed

  ultimately show 
    "\<exists>sa'. (\<exists>r dec_f. (sa, sa') \<in> majorities.opt_mru_step2 r dec_f) 
        \<and> (sa', Suc r, sc') \<in> new_algo_ref_rel"
    by blast

qed

lemma New_Algo_Refines_votes:
  "PO_refines new_algo_ref_rel
    majorities.ts_mru_TS (New_Algo_TS HOs HOs crds)"
proof(rule refine_basic)
  show "init (New_Algo_TS HOs HOs crds) \<subseteq> new_algo_ref_rel `` init majorities.ts_mru_TS"
    by(auto simp add: New_Algo_TS_defs majorities.ts_mru_TS_defs new_algo_ref_rel_def)
next
  show 
    "{new_algo_ref_rel} TS.trans majorities.ts_mru_TS, 
      TS.trans (New_Algo_TS HOs HOs crds) {> new_algo_ref_rel}"
    apply(simp add: majorities.ts_mru_TS_defs New_Algo_TS_defs)
    apply(auto simp add: CHO_trans_alt New_Algo_trans intro!: step0_ref step1_ref step2_ref)
    done
qed

subsubsection \<open>Termination\<close>
(******************************************************************************)

theorem New_Algo_termination:
  assumes run: "HORun New_Algo_Alg rho HOs"
      and commR: "\<forall>r. HOcommPerRd New_Algo_M (HOs r)"
      and commG: "HOcommGlobal New_Algo_M HOs"
  shows "\<exists>r v. decide (rho r p) = Some v"
proof -
  from commG obtain ph where 
    HOs: "\<forall>i \<in> {0..2}. 
      (\<forall>p. card (HOs (nr_steps*ph+i) p) > N div 2)
      \<and> (\<forall>p q. HOs (nr_steps*ph+i) p = HOs (nr_steps*ph) q)"
    by(auto simp add: New_Algo_HOMachine_def NA_commGlobal_def)

  \<comment> \<open>The tedious bit: obtain four consecutive rounds linked by send/next functions\<close>
  define r0 where "r0 = nr_steps * ph"
  define cfg0 where "cfg0 = rho r0"
  define r1 where "r1 = Suc r0"
  define cfg1 where "cfg1 = rho r1"
  define r2 where "r2 = Suc r1"
  define cfg2 where "cfg2 = rho r2"
  define cfg3 where "cfg3 = rho (Suc r2)"

  from 
    run[simplified HORun_def SHORun_def, THEN CSHORun_step, THEN spec, where x="r0"] 
    run[simplified HORun_def SHORun_def, THEN CSHORun_step, THEN spec, where x="r1"]
    run[simplified HORun_def SHORun_def, THEN CSHORun_step, THEN spec, where x="r2"] 
    obtain \<mu>0 \<mu>1 \<mu>2 where
    send0: "\<forall>p. \<mu>0 p \<in> get_msgs (send0 r0) cfg0 (HOs r0) (HOs r0) p"
    and three_step0: "\<forall>p. next0 r0 p (cfg0 p) (\<mu>0 p) undefined (cfg1 p)"
    and send1: "\<forall>p. \<mu>1 p \<in> get_msgs (send1 r1) cfg1 (HOs r1) (HOs r1) p"
    and three_step1: "\<forall>p. next1 r1 p (cfg1 p) (\<mu>1 p) undefined (cfg2 p)"
    and send2: "\<forall>p. \<mu>2 p \<in> get_msgs (send2 r2) cfg2 (HOs r2) (HOs r2) p"
    and three_step2: "\<forall>p. next2 r2 p (cfg2 p) (\<mu>2 p) undefined (cfg3 p)"
    apply(auto simp add: New_Algo_Alg_def three_step_def NA_nextState_def NA_sendMsg_def all_conj_distrib
      r0_def r1_def r2_def
      cfg0_def cfg1_def cfg2_def cfg3_def mod_Suc
      )
    done

  \<comment> \<open>The proof: everybody hears the same messages (non-empty!) in r0...\<close>

  from HOs[THEN bspec, where x=0, simplified] send0
    have 
    "\<forall>p q. \<mu>0 p = \<mu>0 q" "\<forall>p. N div 2 < card (dom (\<mu>0 p))"
    apply(auto simp add: get_msgs_benign send0_def r1_def r0_def dom_def restrict_map_def intro!: ext)
      apply(blast)+
    done

  \<comment> \<open>...hence everybody sets @{term prop_vote} to the same value...\<close>    
  hence same_prevote: 
    "\<forall>p. prop_vote (cfg1 p) \<noteq> None"
    "\<forall>p q. prop_vote (cfg1 p) = prop_vote (cfg1 q)" using three_step0
    apply(auto simp add: next1_def Let_def all_conj_distrib intro!: ext)
     apply(clarsimp simp add: next0_def all_conj_distrib Let_def)
    apply(clarsimp simp add: next0_def all_conj_distrib Let_def)
    by (metis (full_types) dom_eq_empty_conv empty_iff majoritiesE')

  \<comment> \<open>...which will become our decision value.\<close>
  then obtain dec_v where dec_v: "\<forall>p. prop_vote (cfg1 p) = Some dec_v"
    by (metis option.collapse)

  \<comment> \<open>...and since everybody hears from majority in r1...\<close>
  from HOs[THEN bspec, where x="Suc 0", simplified] send1
  have "\<forall>p q. \<mu>1 p = \<mu>1 q" "\<forall>p. N div 2 < card (dom (\<mu>1 p))"
    apply(auto simp add: get_msgs_benign send1_def r1_def r0_def dom_def restrict_map_def intro!: ext)
     apply(blast)+
    done

  \<comment> \<open>and since everybody casts a pre-vote for @{term dec_v}, everybody will vote @{term dec_v}\<close> 
  have all_vote: "\<forall>p. mru_vote (cfg2 p) = Some (three_phase r2, dec_v)"
  proof
    fix p
    have r0_step: "three_step r0 = 0"
      by(auto simp add: r0_def three_step_def)
    from HOs[THEN bspec, where x="Suc 0", simplified] 
    obtain Q where Q: "N div 2 < card Q" "Q \<subseteq> HOs r1 p"
      by(auto simp add: r1_def r0_def)
    hence "Q_prevotes_v (\<mu>1 p) Q dec_v" using dec_v send1[THEN spec, where x=p]
      by(auto simp add: Q_prevotes_v_def get_msgs_benign restrict_map_def send1_def)
    thus "mru_vote (cfg2 p) = Some (three_phase r2, dec_v)" using 
      three_step1[THEN spec, where x=p] r0_step
      by(auto simp add: next1_def r2_def r1_def three_step_phase_Suc)
  qed

  \<comment> \<open>And finally, everybody will also decide @{term dec_v}\<close>
  have all_decide: "\<forall>p. decide (cfg3 p) = Some dec_v"
  proof
    fix p
    from HOs[THEN bspec, where x="Suc (Suc 0)", simplified] 
    obtain Q where Q: "N div 2 < card Q" "Q \<subseteq> HOs r2 p"
      by(auto simp add: r2_def r1_def r0_def)
    thus "decide (cfg3 p) = Some dec_v" 
    using three_step2[THEN spec, where x=p] send2[THEN spec, where x=p]
      by(auto simp add: next2_def send2_def Let_def)
  qed

  thus ?thesis 
    by(auto simp add: cfg3_def)
qed

end

