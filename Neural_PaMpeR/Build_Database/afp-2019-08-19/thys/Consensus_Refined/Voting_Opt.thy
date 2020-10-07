section \<open>The Optimized Voting Model\<close>

theory Voting_Opt
imports Voting
begin

subsection \<open>Model definition\<close>
(*****************************************************************************)

record opt_v_state = 
  next_round :: round 
  last_vote :: "(process, val) map"
  decisions :: "(process, val)map"

definition flv_init where
  "flv_init = { \<lparr> next_round = 0, last_vote = Map.empty, decisions = Map.empty \<rparr> }"

context quorum_process begin

definition fmru_lv :: "(process, round \<times> val)map \<Rightarrow> (process set, round \<times> val)map" where
  "fmru_lv lvs Q = option_Max_by fst (ran (lvs |` Q))"

definition flv_guard :: "(process, round \<times> val)map \<Rightarrow> process set \<Rightarrow> val \<Rightarrow> bool" where
  "flv_guard lvs Q v \<equiv> Q \<in> Quorum \<and> 
    (let alv = fmru_lv lvs Q in alv = None \<or> (\<exists>r. alv = Some (r, v)))"

definition opt_no_defection :: "opt_v_state \<Rightarrow> (process, val)map \<Rightarrow> bool" where
  opt_no_defection_def':
    "opt_no_defection s round_votes \<equiv> 
    \<forall>v. \<forall>Q. quorum_for Q v (last_vote s) \<longrightarrow> round_votes ` Q \<subseteq> {None, Some v}"

lemma opt_no_defection_def:
  "opt_no_defection s round_votes =
    (\<forall>a Q v. quorum_for Q v (last_vote s) \<and> a \<in> Q \<longrightarrow> round_votes a \<in> {None, Some v})"
  apply(auto simp add: opt_no_defection_def')
  by (metis option.distinct(1) option.sel)
                    
definition flv_round :: "round \<Rightarrow> (process, val)map \<Rightarrow>  (process, val)map \<Rightarrow> (opt_v_state \<times> opt_v_state) set" where
  "flv_round r r_votes r_decisions = {(s, s').
     \<comment> \<open>guards\<close>
     r = next_round s
     \<and> opt_no_defection s r_votes
     \<and> d_guard r_decisions r_votes
     \<and> \<comment> \<open>actions\<close>
     s' = s\<lparr> 
       next_round := Suc r
       , last_vote := last_vote s ++ r_votes
       , decisions := (decisions s) ++ r_decisions
     \<rparr>
  }"

lemmas flv_evt_defs = flv_round_def flv_guard_def

definition flv_trans :: "(opt_v_state \<times> opt_v_state) set" where
  "flv_trans = (\<Union>r v_f d_f. flv_round r v_f d_f)"

definition flv_TS :: "opt_v_state TS" where
  "flv_TS = \<lparr> init = flv_init, trans = flv_trans \<rparr>"

lemmas flv_TS_defs = flv_TS_def flv_init_def flv_trans_def

subsection \<open>Refinement\<close>
(******************************************************************************)

definition flv_ref_rel :: "(v_state \<times> opt_v_state)set" where
  "flv_ref_rel = {(sa, sc).
    sc = \<lparr>
      next_round = v_state.next_round sa
      , last_vote = map_option snd o (process_mru (votes sa))
      , decisions = v_state.decisions sa
    \<rparr>
  }"

subsubsection \<open>Guard strengthening\<close>
(******************************************************************************)

lemma process_mru_Max:
  assumes 
    inv: "sa \<in> Vinv1"
    and process_mru: "process_mru (votes sa) p = Some (r, v)"
  shows 
    "votes sa r p = Some v \<and> (\<forall>r' > r. votes sa r' p = None)"
proof-
  from process_mru have not_empty: "vote_set (votes sa) {p} \<noteq> {}"
    by(auto simp add: process_mru_def mru_of_set_def option_Max_by_def)
  note Max_by_conds = Vinv1_finite_vote_set[OF inv] this
  from Max_by_dest[OF Max_by_conds, where f=fst]
  have
    r: 
      "(r, v) = Max_by fst (vote_set (votes sa) {p})" 
      "votes sa r p = Some v" 
      using process_mru
      by(auto simp add: process_mru_def mru_of_set_def option_Max_by_def vote_set_def)
  have "\<forall>r' >r . votes sa r' p = None"
  proof(safe)
    fix r'
    assume less: "r < r'"
    hence "\<forall>v. (r', v) \<notin> vote_set (votes sa) {p}" using process_mru
      by(auto dest!: Max_by_ge[where f=fst, OF Vinv1_finite_vote_set[OF inv]] 
        simp add: process_mru_def mru_of_set_def option_Max_by_def)
    thus "votes sa r' p = None"
      by(auto simp add: vote_set_def)
  qed
  thus ?thesis using r(2)
    by(auto)
qed

lemma opt_no_defection_imp_no_defection:
  assumes
    conc_guard: "opt_no_defection sc round_votes"
    and R: "(sa, sc) \<in> flv_ref_rel"
    and ainv: "sa \<in> Vinv1" "sa \<in> Vinv2"
  shows
    "no_defection sa round_votes r"
proof(unfold no_defection_def, safe)
  fix r' v a Q w
  assume
    r'_less: "r' < r"
    and a_votes_w: "round_votes a = Some w"
    and Q: "quorum_for Q v (votes sa r')"
    and a_in_Q: "a \<in> Q"
  have "Q \<in> Quorum" using Q
    by(auto simp add: quorum_for_def)
  hence "quorum_for Q v (last_vote sc)"
  proof(clarsimp simp add: quorum_for_def)
    fix q
    assume "q \<in> Q"
    with Q have q_r': "votes sa r' q = Some v"
      by(auto simp add: quorum_for_def)
    hence votes: "vote_set (votes sa) {q} \<noteq> {}"
      by(auto simp add: vote_set_def)
    then obtain w where w: "last_vote sc q = Some w" using R
      by(clarsimp simp add: flv_ref_rel_def process_mru_def mru_of_set_def
        option_Max_by_def)
    with R obtain r_max where "process_mru (votes sa) q = Some (r_max, w)"
      by(clarsimp simp add: flv_ref_rel_def)
    from process_mru_Max[OF ainv(1) this] q_r' have
      "votes sa r_max q = Some w" 
      "r' \<le> r_max"
      using q_r'
      by(auto simp add: not_less[symmetric])
    thus "last_vote sc q = Some v" using ainv(2) Q \<open>q \<in> Q\<close>
      apply(case_tac "r_max = r'")
       apply(clarsimp simp add: w Vinv2_def no_defection_def q_r' dest: le_neq_implies_less)
      apply(fastforce simp add: w Vinv2_def no_defection_def q_r' dest!: le_neq_implies_less)
      done
  qed
  thus "round_votes a = Some v" using conc_guard a_in_Q a_votes_w r'_less
    by(fastforce simp add: opt_no_defection_def)
qed

subsubsection \<open>Action refinement\<close>
(******************************************************************************)

lemma act_ref:
  assumes
    inv: "s \<in> Vinv1"
  shows 
    "map_option snd o (process_mru ((votes s)(v_state.next_round s := v_f)))
    = ((map_option snd o (process_mru (votes s))) ++ v_f)"
    by(auto simp add: process_mru_map_add[OF inv] map_add_def split: option.split)

subsubsection \<open>The complete refinement proof\<close>
(******************************************************************************)

lemma flv_round_refines:
  "{flv_ref_rel \<inter> (Vinv1 \<inter> Vinv2) \<times> UNIV}
    v_round r v_f  d_f, flv_round r v_f d_f
  {> flv_ref_rel}"
  by(auto simp add: PO_rhoare_defs flv_round_def v_round_def 
    flv_ref_rel_def act_ref
    intro: opt_no_defection_imp_no_defection)
  
lemma Last_Voting_Refines:
  "PO_refines (flv_ref_rel \<inter> (Vinv1 \<inter> Vinv2) \<times> UNIV) v_TS flv_TS"
proof(rule refine_using_invariants)
  show "init flv_TS \<subseteq> flv_ref_rel `` init v_TS"
    by(auto simp add: flv_TS_defs v_TS_defs flv_ref_rel_def
      process_mru_def mru_of_set_def vote_set_def option_Max_by_def)
next
  show 
    "{flv_ref_rel \<inter> (Vinv1 \<inter> Vinv2) \<times> UNIV} trans v_TS, trans flv_TS {> flv_ref_rel}"
    by(auto simp add: v_TS_defs flv_TS_defs intro!: flv_round_refines)
next
  show
    "{Vinv1 \<inter> Vinv2 \<inter> Domain (flv_ref_rel \<inter> UNIV \<times> UNIV)} 
      trans v_TS 
    {> Vinv1 \<inter> Vinv2}" 
    using Vinv1_inductive(2) Vinv2_inductive(2)
    by blast
qed(auto intro!: Vinv1_inductive(1) Vinv2_inductive(1))

end

end
