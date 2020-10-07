section \<open>The Optimized Observing Quorums Model\<close>

theory Observing_Quorums_Opt
imports Observing_Quorums
begin

subsection \<open>Model definition\<close>
(******************************************************************************)

record opt_obsv_state = 
  next_round :: round 
  decisions :: "(process, val)map"
  last_obs :: "(process, val)map"

context mono_quorum
begin

definition opt_obs_safe where
  "opt_obs_safe obs_f v \<equiv> \<exists>p. obs_f p \<in> {None, Some v}"

definition olv_round where
  "olv_round r S v r_decisions Ob \<equiv> {(s, s').
    \<comment> \<open>guards\<close>
    r = next_round s
    \<and> (S \<noteq> {} \<longrightarrow> opt_obs_safe (last_obs s) v)
    \<and> (S \<in> Quorum \<longrightarrow> Ob = UNIV)
    \<and> d_guard r_decisions (const_map v S)
    \<and> (Ob \<noteq> {} \<longrightarrow> S \<noteq> {})
    \<and> \<comment> \<open>actions\<close>
    s' = s\<lparr> 
     next_round := Suc r
     , decisions := decisions s ++ r_decisions
     , last_obs := last_obs s ++ const_map v Ob
   \<rparr>
  }"

definition olv_init where
  "olv_init = { \<lparr> next_round = 0, decisions = Map.empty, last_obs = Map.empty \<rparr> }"

definition olv_trans :: "(opt_obsv_state \<times> opt_obsv_state) set" where
  "olv_trans = (\<Union>r S v D Ob. olv_round r S v D Ob) \<union> Id"

definition olv_TS :: "opt_obsv_state TS" where
  "olv_TS = \<lparr> init = olv_init, trans = olv_trans \<rparr>"

lemmas olv_TS_defs = olv_TS_def olv_init_def olv_trans_def

subsection \<open>Refinement\<close>
(******************************************************************************)

definition olv_ref_rel where
  "olv_ref_rel \<equiv> {(sa, sc).
    next_round sc = v_state.next_round sa
    \<and> decisions sc = v_state.decisions sa
    \<and> last_obs sc = map_option snd o process_mru (obsv_state.obs sa)
  }"


lemma OV_inv2_finite_map_graph:
   "s \<in> OV_inv2 \<Longrightarrow> finite (map_graph (case_prod (obsv_state.obs s)))"
  apply(rule finite_dom_finite_map_graph)
  apply(rule finite_subset[where B="{0..< v_state.next_round s} \<times> UNIV"])
   apply(auto simp add: OV_inv2_def dom_def not_le[symmetric])
  done

lemma OV_inv2_finite_obs_set:
   "s \<in> OV_inv2 \<Longrightarrow> finite (vote_set (obsv_state.obs s) Q)"
   apply(drule OV_inv2_finite_map_graph)
   apply(clarsimp simp add: map_graph_def fun_graph_def vote_set_def)
   apply(erule finite_surj[where f="\<lambda>((r, a), v). (r, v)"])
   by(force simp add: image_def)   

lemma olv_round_refines:
  "{olv_ref_rel \<inter> (OV_inv2 \<inter> OV_inv3 \<inter> OV_inv4) \<times> UNIV} obsv_round r S v D Ob, olv_round r S v D Ob {>olv_ref_rel}"
proof(clarsimp simp add: PO_rhoare_defs)
  fix sa :: obsv_state and sc sc'
  assume
    ainv: "sa \<in> OV_inv2" "sa \<in> OV_inv3" "sa \<in> OV_inv4"
    and step: "(sc, sc') \<in> olv_round r S v D Ob"
    and R: "(sa, sc) \<in> olv_ref_rel"

  \<comment> \<open>Abstract guard.\<close>
  have "S \<noteq> {} \<longrightarrow> obs_safe (v_state.next_round sa) sa v"
  proof(rule impI, rule ccontr)
    assume S_nonempty: "S \<noteq> {}" and no_Q: "\<not> obs_safe (v_state.next_round sa) sa v"
    from no_Q obtain r_w w where 
      r_w: "r_w < v_state.next_round sa"
      and all_obs: "\<forall>p. obsv_state.obs sa r_w p = Some w"
      and diff: "w \<noteq> v" using ainv(3)[THEN OV_inv4D]
      by(simp add: obs_safe_def)  (metis)
    from diff step R obtain p where 
      p_w: "S \<noteq> {} \<longrightarrow> (map_option snd \<circ> process_mru (obsv_state.obs sa)) p \<noteq> Some w"
      by (simp add: opt_obs_safe_def quorum_for_def olv_round_def  olv_ref_rel_def)  
       (metis option.distinct(1) option.sel snd_conv)
    from all_obs have nempty: "vote_set (obsv_state.obs sa) {p} \<noteq> {}" 
      by(auto simp add:  vote_set_def)
    then obtain r_w' w' where w': "process_mru (obsv_state.obs sa) p = Some (r_w', w')"
      by (simp add: process_mru_def mru_of_set_def) 
        (metis option_Max_by_def surj_pair)
    hence max: "(r_w', w') = Max_by fst (vote_set (obsv_state.obs sa) {p})"
      by(auto simp add: process_mru_def mru_of_set_def option_Max_by_def)
    hence w'_obs: "(r_w', w') \<in> vote_set (obsv_state.obs sa) {p}" 
      using Max_by_in[OF OV_inv2_finite_obs_set[OF ainv(1), of "{p}"] nempty]
      by fastforce
    have "r_w \<le> r_w'" using all_obs
      apply -
      apply(rule Max_by_ge[OF OV_inv2_finite_obs_set[OF ainv(1), of "{p}"], of "(r_w, w)" fst, 
                            simplified max[symmetric], simplified])
      apply(auto simp add: quorum_for_def vote_set_def)
      done
    moreover have "w' \<noteq> w" using p_w w' S_nonempty
      by(auto)
    ultimately have "r_w < r_w'" using all_obs w'_obs
      apply(elim le_neq_implies_less)
      apply(auto simp add: quorum_for_def vote_set_def)
      done
    thus False using ainv(2)[THEN OV_inv3D] w'_obs all_obs \<open>w' \<noteq> w\<close>
      by(fastforce simp add: vote_set_def obs_safe_def)
  qed

  \<comment> \<open>Action refinement.\<close>
  moreover have 
    "(map_option snd \<circ> process_mru (obsv_state.obs sa)) ++ const_map v Ob =
      map_option snd \<circ> process_mru ((obsv_state.obs sa)(v_state.next_round sa := const_map v Ob))"
  proof-
    from \<open>sa \<in> OV_inv2\<close>[THEN OV_inv2D] 
    have empty: "\<forall>r'\<ge>v_state.next_round sa. obsv_state.obs sa r' = Map.empty"
      by simp
    show ?thesis
      by(auto simp add: map_add_def const_map_def restrict_map_def process_mru_new_votes[OF empty])
  qed

  ultimately show "\<exists>sa'. (sa, sa') \<in> obsv_round r S v D Ob \<and> (sa', sc') \<in> olv_ref_rel" 
    using R step
    by(clarsimp simp add: obsv_round_def olv_round_def olv_ref_rel_def)

qed

lemma OLV_Refines:
  "PO_refines (olv_ref_rel \<inter> (OV_inv2 \<inter> OV_inv3 \<inter> OV_inv4) \<times> UNIV) obsv_TS olv_TS"
proof(rule refine_using_invariants)
  show "init olv_TS \<subseteq> olv_ref_rel `` init obsv_TS"
    by(auto simp add: obsv_TS_defs olv_TS_defs olv_ref_rel_def process_mru_def mru_of_set_def
      vote_set_def option_Max_by_def intro!: ext)
next
  show
    "{olv_ref_rel \<inter> (OV_inv2 \<inter> OV_inv3 \<inter> OV_inv4) \<times> UNIV} TS.trans obsv_TS, TS.trans olv_TS {> olv_ref_rel}"
    by(auto simp add: PO_refines_def obsv_TS_defs olv_TS_defs 
      intro!: olv_round_refines)
qed (auto intro: OV_inv2_inductive OV_inv3_inductive OV_inv4_inductive
  OV_inv2_inductive(1)[THEN subsetD] OV_inv3_inductive(1)[THEN subsetD] 
  OV_inv4_inductive(1)[THEN subsetD])

end

end
