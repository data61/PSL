(*<*)
theory Uv_Proofs
imports Heard_Of.Reduction
  Two_Step_Observing "../HO_Transition_System" Uv_Defs
begin
(*>*)

subsection \<open>Proofs\<close>
type_synonym uv_TS_state = "(nat \<times> (process \<Rightarrow> (val pstate)))"

axiomatization where val_linorder: 
  "OFCLASS(val, linorder_class)"

instance val :: linorder by (rule val_linorder)

lemma two_step_step:
   "step = two_step"
   "phase = two_phase"
   by(auto simp add: step_def two_step_def phase_def two_phase_def)

context mono_quorum
begin

definition UV_Alg :: "(process, val pstate, val msg)CHOAlgorithm" where
  "UV_Alg = CHOAlgorithm.truncate UV_M"

definition UV_TS ::
  "(round \<Rightarrow> process HO) \<Rightarrow> (round \<Rightarrow> process HO) \<Rightarrow> (round \<Rightarrow> process) \<Rightarrow> uv_TS_state TS"
where
  "UV_TS HOs SHOs crds = CHO_to_TS UV_Alg HOs SHOs (K o crds)"

lemmas UV_TS_defs = UV_TS_def CHO_to_TS_def UV_Alg_def CHOinitConfig_def
  UV_initState_def

type_synonym rHO = "nat \<Rightarrow> process HO"

definition UV_trans_step 
  where
  "UV_trans_step HOs SHOs nxt_f snd_f stp \<equiv> \<Union>r \<mu>.
    {((r, cfg), (Suc r, cfg'))|cfg cfg'. step r = stp  \<and> (\<forall>p.
      \<mu> p \<in> get_msgs (snd_f r) cfg (HOs r) (SHOs r) p
      \<and> nxt_f r p (cfg p) (\<mu> p) (cfg' p)
    )}"

lemma step_less_D:
  "0 < step r \<Longrightarrow> step r = Suc 0"
  by(auto simp add: step_def)

lemma UV_trans:
  "CSHO_trans_alt UV_sendMsg (\<lambda>r p st msgs crd st'. UV_nextState r p st msgs st') HOs SHOs crds = 
  UV_trans_step HOs SHOs next0 send0 0
  \<union> UV_trans_step HOs SHOs  next1 send1 1
  "
proof
  show "CSHO_trans_alt UV_sendMsg (\<lambda>r p st msgs crd. UV_nextState r p st msgs) HOs SHOs crds
    \<subseteq> UV_trans_step HOs SHOs next0 send0 0 \<union> UV_trans_step HOs SHOs next1 send1 1"
  by(force simp add: CSHO_trans_alt_def UV_sendMsg_def UV_nextState_def UV_trans_step_def 
    K_def dest!: step_less_D)
next
  show " UV_trans_step HOs SHOs next0 send0 0 \<union>
    UV_trans_step HOs SHOs next1 send1 1
    \<subseteq> CSHO_trans_alt UV_sendMsg
        (\<lambda>r p st msgs crd. UV_nextState r p st msgs) HOs SHOs crds"
  by(force simp add: CSHO_trans_alt_def UV_sendMsg_def UV_nextState_def UV_trans_step_def)
qed

subsubsection \<open>Invariants\<close>
(******************************************************************************)

definition UV_inv1
  :: "uv_TS_state set" 
where  
  "UV_inv1  = {(r, s). 
    two_step r = 0 \<longrightarrow> (\<forall>p. agreed_vote (s p) = None)
  }"

lemmas UV_inv1I = UV_inv1_def [THEN setc_def_to_intro, rule_format]
lemmas UV_inv1E [elim] = UV_inv1_def [THEN setc_def_to_elim, rule_format]
lemmas UV_inv1D = UV_inv1_def [THEN setc_def_to_dest, rule_format]

lemma UV_inv1_inductive:
  "init (UV_TS HOs SHOs crds) \<subseteq> UV_inv1"
  "{UV_inv1} TS.trans (UV_TS HOs SHOs crds) {> UV_inv1}"
  by(auto simp add: UV_inv1_def UV_TS_defs CHO_trans_alt UV_trans PO_hoare_def 
    UV_HOMachine_def CHOAlgorithm.truncate_def UV_trans_step_def 
    all_conj_distrib two_step_phase_Suc two_step_step next1_def)
  
lemma UV_inv1_invariant:
  "reach (UV_TS HOs SHOs crds) \<subseteq> UV_inv1"
  by(intro inv_rule_basic UV_inv1_inductive)

subsubsection \<open>Refinement\<close>
(******************************************************************************)

definition ref_rel :: "(tso_state \<times> uv_TS_state)set" where
  "ref_rel \<equiv> {(sa, (r, sc)).
    r = next_round sa
    \<and> (step r = 1 \<longrightarrow> r_votes sa = agreed_vote o sc)
    \<and> (\<forall>p v. last_obs (sc p) = v \<longrightarrow> (\<exists>q. opt_obsv_state.last_obs sa q \<in> {None, Some v}))
    \<and> decisions sa = decide o sc
  }"

(******************************************************************************)
text \<open>Agreement for UV only holds if the communication predicates hold\<close>
context
  fixes
    HOs :: "nat \<Rightarrow> process \<Rightarrow> process set"
    and rho :: "nat \<Rightarrow> process \<Rightarrow> 'val pstate"
  assumes global: "UV_commGlobal HOs"
  and per_rd: "\<forall>r. UV_commPerRd (HOs r)"
  and run: "HORun fA rho HOs"
begin
(******************************************************************************)

lemma HOs_intersect:
  "HOs r p \<inter> HOs r' q \<noteq> {}" using per_rd
  apply(simp add: UV_commPerRd_def)
  apply(blast dest: qintersect)
  done

lemma HOs_nonempty:
  "HOs r p \<noteq> {}" 
  using HOs_intersect
  by blast

lemma vote_origin:
  assumes
  send: "\<forall>p. \<mu> p \<in> get_msgs (send0 r) cfg (HOs r) (HOs r) p"
  and step: "\<forall>p. next0 r p (cfg p) (\<mu> p) (cfg' p)"
  and inv: "(r, cfg) \<in> UV_inv1"
  and step_r: "two_step r = 0"
  shows 
    "agreed_vote (cfg' p) = Some v \<longleftrightarrow> (\<forall>q \<in> HOs r p. last_obs (cfg q) = v)" 
  using send[THEN spec, where x=p] step[THEN spec, where x=p] inv step_r HOs_nonempty
  by(auto simp add: next0_def get_msgs_benign send0_def msgRcvd_def o_def restrict_map_def)
  
lemma same_new_vote:
  assumes 
  send: "\<forall>p. \<mu> p \<in> get_msgs (send0 r) cfg (HOs r) (HOs r) p"
  and step: "\<forall>p. next0 r p (cfg p) (\<mu> p) (cfg' p)"
  and inv: "(r, cfg) \<in> UV_inv1"
  and step_r: "two_step r = 0"
  obtains v where "\<forall>p w. agreed_vote (cfg' p) = Some w \<longrightarrow> w = v" 
proof(cases "\<exists>p v. agreed_vote (cfg' p) = Some v")
  case True
  assume asm: "\<And>v. \<forall>p w. agreed_vote (cfg' p) = Some w \<longrightarrow> w = v \<Longrightarrow> thesis"
  from True obtain p v where "agreed_vote (cfg' p) = Some v" by auto

  hence "\<forall>p w. agreed_vote (cfg' p) = Some w \<longrightarrow> w = v" (is "?LV(v)")
    using vote_origin[OF send step inv step_r] HOs_intersect
    by(force)

  from asm[OF this] show ?thesis .
qed(auto)

lemma x_origin1:
  assumes
  send: "\<forall>p. \<mu> p \<in> get_msgs (send0 r) cfg (HOs r) (HOs r) p"
  and step: "\<forall>p. next0 r p (cfg p) (\<mu> p) (cfg' p)"
  and step_r: "two_step r = 0"
  and last_obs: "last_obs (cfg' p) = v"
  shows 
    "\<exists>q. last_obs (cfg q) = v" 
proof-
  have "smallestValRcvd (\<mu> p) \<in> {v. \<exists>q. \<mu> p q = Some (Val v)}" (is "smallestValRcvd ?msgs \<in> ?vals")
  unfolding smallestValRcvd_def
  proof(rule Min_in)
    have "?vals \<subseteq> getval ` ((the \<circ> ?msgs) ` (HOs r p))"
      using send[THEN spec, where x=p]
      by (auto simp: image_def get_msgs_benign restrict_map_def send0_def)
    thus "finite ?vals" by (auto simp: finite_subset)
  next
    from send[THEN spec, where x=p]
    show "?vals \<noteq> {}" using HOs_nonempty[of r p]
      by (auto simp: image_def get_msgs_benign restrict_map_def send0_def)
  qed
  hence "v \<in> ?vals" using last_obs step[THEN spec, of p] 
    by(auto simp add: next0_def all_conj_distrib)
  thus ?thesis using send[THEN spec, of p]
    by(auto simp add: get_msgs_benign send0_def restrict_map_def)
qed
    
lemma step0_ref:
  "{ref_rel \<inter> UNIV \<times> UV_inv1} \<Union>r S v. tso_round0 r S v, 
    UV_trans_step HOs HOs next0 send0 0 {> ref_rel}"
proof(clarsimp simp add: PO_rhoare_defs UV_trans_step_def two_step_step all_conj_distrib)
  fix sa r cfg \<mu> cfg'
  assume
    R: "(sa, (r, cfg)) \<in> ref_rel"
    and step_r: "two_step r = 0" 
    and send: "\<forall>p. \<mu> p \<in> get_msgs (send0 r) cfg (HOs r) (HOs r) p"
    and step: "\<forall>p. next0 r p (cfg p) (\<mu> p) (cfg' p)"
    and inv: "(r, cfg) \<in> UV_inv1"

  from R have next_r: "next_round sa = r"
    by(simp add: ref_rel_def)

  from HOs_nonempty send have "\<forall>p. \<exists>q. q \<in> msgRcvd (\<mu> p)"
    by(fastforce simp add: get_msgs_benign send0_def msgRcvd_def restrict_map_def)
  with step have same_dec: "decide o cfg' = decide o cfg"
    apply(simp add: next0_def o_def)
    by (metis pstate.select_convs(3) pstate.surjective pstate.update_convs(1) pstate.update_convs(2))

  define S where "S = {p. \<exists>v. agreed_vote (cfg' p) = Some v}"
  from same_new_vote[OF send step inv step_r] 
  obtain v where v: "\<forall>p \<in> S. agreed_vote (cfg' p) = Some v"
    by(simp add: S_def) (metis)
  hence vote_const_map: "agreed_vote o cfg' = const_map v S"
    by(auto simp add: S_def const_map_def restrict_map_def intro!: ext)

  note x_origin = x_origin1[OF send step step_r]

  define sa' where "sa' = sa\<lparr> next_round := Suc r, r_votes := const_map v S \<rparr>"

  have "\<forall>p. p \<in> S \<longrightarrow> opt_obs_safe (opt_obsv_state.last_obs sa) v"
    using vote_origin[OF send step inv step_r] R per_rd[THEN spec, of r] v
    apply(clarsimp simp add: UV_commPerRd_def opt_obs_safe_def ref_rel_def)
    by metis
    
  hence "(sa, sa') \<in> tso_round0 r S v" using next_r step_r v R 
    vote_origin[OF send step inv step_r]
    by(auto simp add: tso_round0_def sa'_def all_conj_distrib)

  moreover have "(sa', Suc r, cfg') \<in> ref_rel" using step send v R same_dec step_r next_r
    apply(clarsimp simp add: ref_rel_def sa'_def two_step_step two_step_phase_Suc vote_const_map)
    by (metis x_origin)
  ultimately show
    "\<exists>sa'. (\<exists>r S v. (sa, sa') \<in> tso_round0 r S v) \<and> (sa', Suc r, cfg') \<in> ref_rel"
    by blast
qed


lemma x_origin2:
  assumes
  send: "\<forall>p. \<mu> p \<in> get_msgs (send1 r) cfg (HOs r) (HOs r) p"
  and step: "\<forall>p. next1 r p (cfg p) (\<mu> p) (cfg' p)"
  and step_r: "two_step r = Suc 0"
  and last_obs: "last_obs (cfg' p) = v"
  shows 
    "(\<exists>q. last_obs (cfg q) = v) \<or> (\<exists>q. agreed_vote (cfg q) = Some v)" 
proof(cases "\<forall>q \<in> HOs r p. \<exists>w. \<mu> p q = Some (ValVote w None)")
  case True
  hence empty: "someVoteRcvd (\<mu> p) = {}" using send[THEN spec, of p] HOs_nonempty[of r p]
    by(auto simp add: someVoteRcvd_def msgRcvd_def isValVote_def 
      get_msgs_benign send1_def restrict_map_def)
  have "smallestValNoVoteRcvd (\<mu> p) \<in> {v. \<exists>q. \<mu> p q = Some (ValVote v None)}" 
    (is "smallestValNoVoteRcvd ?msgs \<in> ?vals")
  unfolding smallestValNoVoteRcvd_def
  proof(rule Min_in)
    have "?vals \<subseteq> getval ` ((the \<circ> ?msgs) ` (HOs r p))"
      using send[THEN spec, where x=p]
      by (auto simp: image_def get_msgs_benign restrict_map_def send0_def)
    thus "finite ?vals" by (auto simp: finite_subset)
  next
    from send[THEN spec, where x=p] True HOs_nonempty[of r p]
    show "?vals \<noteq> {}" 
      by (auto simp: image_def get_msgs_benign restrict_map_def send1_def)
  qed
  hence "v \<in> ?vals" using empty step[THEN spec, of p] last_obs
    by(auto simp add: next1_def x_update_def)
  thus ?thesis using send[THEN spec, of p]
    by(auto simp add: get_msgs_benign restrict_map_def send1_def)
next
  case False
  hence "someVoteRcvd (\<mu> p) \<noteq> {}" using send[THEN spec, of p] HOs_nonempty[of r p]
    by(auto simp add: someVoteRcvd_def msgRcvd_def isValVote_def 
      get_msgs_benign send1_def restrict_map_def)
  hence "\<exists>q \<in> someVoteRcvd (\<mu> p). v = the (getvote (the (\<mu> p q)))" using step[THEN spec, of p] last_obs
    by(auto simp add: next1_def x_update_def)
  thus ?thesis using send[THEN spec, of p]
    by(auto simp add: next1_def x_update_def someVoteRcvd_def isValVote_def 
      send1_def get_msgs_benign msgRcvd_def restrict_map_def)
qed

definition D where
  "D cfg cfg' \<equiv> {p. decide (cfg' p) \<noteq> decide (cfg p) }"

lemma decide_origin:
  assumes
  send: "\<forall>p. \<mu> p \<in> get_msgs (send1 r) cfg (HOs r) (HOs r) p"
  and step: "\<forall>p. next1 r p (cfg p) (\<mu> p) (cfg' p)"
  and step_r: "two_step r = Suc 0"
  shows 
    "D cfg cfg' \<subseteq> {p. \<exists>v. decide (cfg' p) = Some v \<and> (\<forall>q \<in> HOs r p. agreed_vote (cfg q) = Some v)}" 
  using assms
  by(fastforce simp add: D_def next1_def get_msgs_benign send1_def msgRcvd_def o_def restrict_map_def
    x_update_def dec_update_def identicalVoteRcvd_def all_conj_distrib someVoteRcvd_def isValVote_def
    smallestValNoVoteRcvd_def)
  
lemma step1_ref:
  "{ref_rel \<inter> (TSO_inv1 \<inter> TSO_inv2) \<times> UNIV} \<Union>r d_f o_f. tso_round1 r d_f o_f, 
    UV_trans_step HOs HOs next1 send1 (Suc 0) {> ref_rel}"
proof(clarsimp simp add: PO_rhoare_defs UV_trans_step_def two_step_step all_conj_distrib)
  fix sa r cfg \<mu> and cfg' :: "process \<Rightarrow> val pstate"
  assume
    R: "(sa, (r, cfg)) \<in> ref_rel"
    and step_r: "two_step r = Suc 0" 
    and send: "\<forall>p. \<mu> p \<in> get_msgs (send1 r) cfg (HOs r) (HOs r) p"
    and step: "\<forall>p. next1 r p (cfg p) (\<mu> p) (cfg' p)"
    and ainv: "sa \<in> TSO_inv1"
    and ainv2: "sa \<in> TSO_inv2"

  from R have next_r: "next_round sa = r"
    by(simp add: ref_rel_def)

  define S where "S = {p. \<exists>v. agreed_vote (cfg p) = Some v}"
  from R obtain v where v: "\<forall>p \<in> S. agreed_vote (cfg p) = Some v" using ainv step_r
    by(auto simp add: ref_rel_def TSO_inv1_def S_def two_step_step)

  define Ob where "Ob = {p. last_obs (cfg' p) = v}"
  define o_f where "o_f p = (if S \<in> Quorum then Some v else None)" for p :: process

  define dec_f where "dec_f p = (if p \<in> D cfg cfg' then decide (cfg' p) else None)" for p

  {
    fix p w
    assume "agreed_vote (cfg p) = Some w"
    hence "w = v" using v
      by(unfold S_def, auto)
  } note v'=this
    
  have d_guard: "d_guard dec_f (agreed_vote \<circ> cfg)" using per_rd[THEN spec, of r]
    by(fastforce simp add: d_guard_def locked_in_vf_def quorum_for_def dec_f_def
      UV_commPerRd_def dest!: decide_origin[OF send step step_r, THEN subsetD])

  have "dom (agreed_vote \<circ> cfg) \<in> Quorum \<longrightarrow> Ob = UNIV"
  proof(auto simp add: Ob_def)
    fix p
    assume Q: "dom (agreed_vote \<circ> cfg) \<in> Quorum" (is "?Q \<in> Quorum")
    hence "?Q \<inter> HOs r p \<noteq> {}"  using per_rd[THEN spec, of r]
      by(auto simp add: UV_commPerRd_def dest: qintersect)
    hence "someVoteRcvd (\<mu> p) \<noteq> {}" using send[THEN spec, of p]
      by(force simp add: someVoteRcvd_def get_msgs_benign msgRcvd_def restrict_map_def 
        isValVote_def send1_def)
    moreover have "\<forall>q \<in> someVoteRcvd (\<mu> p). \<exists>x'. \<mu> p q = Some (ValVote x' (Some v))"
      using send[THEN spec, of p]
      by(auto simp add: someVoteRcvd_def get_msgs_benign msgRcvd_def restrict_map_def
        isValVote_def send1_def dest: v')
    ultimately show "last_obs (cfg' p) = v" using step[THEN spec, of p]
      by(auto simp add: next1_def x_update_def)
  qed
  note Ob_UNIV=this[rule_format]

  have obs_guard: "obs_guard o_f (agreed_vote \<circ> cfg)"
    apply(auto simp add: obs_guard_def o_f_def S_def dom_def
      dest: v' Ob_UNIV quorum_non_empty) 
    apply (metis S_def all_not_in_conv  empty_not_quorum v)
    done

  define sa' where "sa' = sa\<lparr> 
    next_round := Suc (next_round sa)
    , decisions := decisions sa ++ dec_f
    , opt_obsv_state.last_obs := opt_obsv_state.last_obs sa ++ o_f
    \<rparr>"


  \<comment> \<open>Abstract step\<close>
  have abs_step: "(sa, sa') \<in> tso_round1 r dec_f o_f"  using next_r step_r R d_guard obs_guard
    by(auto simp add: tso_round1_def sa'_def ref_rel_def two_step_step)

  \<comment> \<open>Relation preserved\<close>
  have "\<forall>p. ((decide \<circ> cfg) ++ dec_f) p = decide (cfg' p)"
  proof
    fix p
    show "((decide \<circ> cfg) ++ dec_f) p = decide (cfg' p)" using step[THEN spec, of p]
      by(auto simp add: dec_f_def D_def next1_def dec_update_def map_add_def)
  qed
  note dec_rel=this[rule_format]

  have "\<forall>p. (\<exists>q. o_f q = None \<and> opt_obsv_state.last_obs sa q = None 
        \<or> (opt_obsv_state.last_obs sa ++ o_f) q = Some (last_obs (cfg' p)))"
  proof(intro allI impI, cases "S \<in> Quorum")
    fix p 
    case True 
    hence "last_obs (cfg' p) = v" using Ob_UNIV
      by(auto simp add: S_def Ob_def dom_def)
    thus "(\<exists>q. o_f q = None \<and> opt_obsv_state.last_obs sa q = None 
        \<or> (opt_obsv_state.last_obs sa ++ o_f) q = Some (last_obs (cfg' p)))"
      using True
      by(auto simp add: o_f_def)
  next
    fix p
    case False
    hence empty: "o_f = Map.empty"
      by(auto simp add: o_f_def)
    note last_obs = x_origin2[OF send step step_r refl, of p]
    thus "(\<exists>q. o_f q = None \<and> opt_obsv_state.last_obs sa q = None 
        \<or> (opt_obsv_state.last_obs sa ++ o_f) q = Some (last_obs (cfg' p)))"
    proof(elim disjE exE)
      fix q
      assume "last_obs (cfg q) = last_obs (cfg' p)"
      from this[symmetric] show ?thesis using R step_r empty
        by(simp add: ref_rel_def two_step_step)
    next
      fix q
      assume "agreed_vote (cfg q) = Some (last_obs (cfg' p))" 
      from this[symmetric] show ?thesis using R ainv2 step_r empty
        apply(auto simp add: ref_rel_def two_step_step TSO_inv2_def)
        by metis
    qed
  qed
  note obs_rel=this[rule_format]

  have post_rel: 
    "(sa', Suc r, cfg') \<in> ref_rel" using step send next_r R step_r
    by(auto simp add: sa'_def ref_rel_def two_step_step
      two_step_phase_Suc dec_rel obs_rel)
    
  from abs_step post_rel show
    "\<exists>sa'. (\<exists>r d_f o_f. (sa, sa') \<in> tso_round1 r d_f o_f) \<and> (sa', Suc r, cfg') \<in> ref_rel"
    by blast
qed

lemma UV_Refines_votes:
  "PO_refines (ref_rel \<inter> (TSO_inv1 \<inter> TSO_inv2) \<times> UV_inv1)
    tso_TS (UV_TS HOs HOs crds)"
proof(rule refine_using_invariants)
  show "init (UV_TS HOs HOs crds) \<subseteq> ref_rel `` init tso_TS"
    by(auto simp add: UV_TS_defs UV_HOMachine_def CHOAlgorithm.truncate_def 
      tso_TS_defs ref_rel_def tso_init_def Let_def o_def)
next
  show 
    "{ref_rel \<inter> (TSO_inv1 \<inter> TSO_inv2) \<times> UV_inv1} TS.trans tso_TS, 
      TS.trans (UV_TS HOs HOs crds) {> ref_rel}"
    apply(simp add: tso_TS_defs UV_TS_defs UV_HOMachine_def CHOAlgorithm.truncate_def)
    apply(auto simp add: CHO_trans_alt UV_trans intro!: step0_ref step1_ref)
    done
qed(auto intro!: TSO_inv1_inductive TSO_inv2_inductive UV_inv1_inductive)

end (* HO predicate context *)

end (* mono_quorum context *)

subsubsection \<open>Termination\<close>
(******************************************************************************)

text \<open>As the model of the algorithm is taken verbatim from the HO Model AFP, we
  do not repeat the termination proof here and refer to that AFP entry.\<close>

end (* theory *)
