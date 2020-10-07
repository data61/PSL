(*<*)
(*
 * Copyright 2015, NICTA
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(NICTA_BSD)
 *)

theory Handshakes
imports
  TSO
begin

(*>*)
subsection\<open>Handshake phases\<close>

text\<open>

The mutators can be at most one step behind the garbage collector (and
system). If any mutator is behind then the GC is stalled on a pending
handshake. Unfortunately this is a complicated by needing to consider
the handshake type due to \<open>get_work\<close>. This relation is very
precise.

\<close>

definition hp_step_rel :: "(bool \<times> handshake_type \<times> handshake_phase \<times> handshake_phase) set" where
  "hp_step_rel \<equiv>
  { True }  \<times> ({ (ht_NOOP, hp, hp) |hp. hp \<in> {hp_Idle, hp_IdleInit, hp_InitMark, hp_Mark} }
            \<union> { (ht_GetRoots, hp_IdleMarkSweep, hp_IdleMarkSweep)
              , (ht_GetWork,  hp_IdleMarkSweep, hp_IdleMarkSweep) })
\<union> { False } \<times> { (ht_NOOP,     hp_Idle,          hp_IdleMarkSweep)
              , (ht_NOOP,     hp_IdleInit,      hp_Idle)
              , (ht_NOOP,     hp_InitMark,      hp_IdleInit)
              , (ht_NOOP,     hp_Mark,          hp_InitMark)
              , (ht_GetRoots, hp_IdleMarkSweep, hp_Mark)
              , (ht_GetWork,  hp_IdleMarkSweep, hp_IdleMarkSweep) }"

definition handshake_phase_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "handshake_phase_inv = (\<^bold>\<forall>m.
      (sys_ghost_handshake_in_sync m \<^bold>\<otimes> sys_handshake_type
        \<^bold>\<otimes> sys_ghost_handshake_phase \<^bold>\<otimes> mut_m.mut_ghost_handshake_phase m) \<^bold>\<in> \<langle>hp_step_rel\<rangle>
  \<^bold>\<and> (sys_handshake_pending m \<^bold>\<longrightarrow> \<^bold>\<not>(sys_ghost_handshake_in_sync m)))"
(*<*)

(* Sanity *)
lemma handshake_step_inv:
  "hp' = handshake_step hp \<Longrightarrow> \<exists>in' ht. (in', ht, hp', hp) \<in> hp_step_rel"
by (cases hp) (auto simp: hp_step_rel_def)

(* Sanity *)
lemma handshake_step_invD:
  "(False, ht, hp', hp) \<in> hp_step_rel \<Longrightarrow> hp' = hp_step ht hp"
by (cases ht) (auto simp: hp_step_rel_def)

lemma (in mut_m) handshake_phase_invD:
  "handshake_phase_inv s \<Longrightarrow> (sys_ghost_handshake_in_sync m s, sys_handshake_type s, sys_ghost_handshake_phase s, mut_ghost_handshake_phase s) \<in> hp_step_rel
                          \<and> (sys_handshake_pending m s \<longrightarrow> \<not>sys_ghost_handshake_in_sync m s)"
by (simp add: handshake_phase_inv_def)

lemma handshake_in_syncD:
  "\<lbrakk> All (ghost_handshake_in_sync (s sys)); handshake_phase_inv s \<rbrakk>
     \<Longrightarrow> \<forall>m'. mut_m.mut_ghost_handshake_phase m' s = sys_ghost_handshake_phase s"
by clarsimp (auto simp: hp_step_rel_def dest!: mut_m.handshake_phase_invD)

lemma (in sys) handshake_phase_inv[intro]:
  "\<lbrace> LSTP handshake_phase_inv \<rbrace> sys"
by (vcg_jackhammer simp: handshake_phase_inv_def)

(*>*)
text\<open>

Connect @{const "sys_ghost_handshake_phase"} with locations in the GC.

\<close>

locset_definition "hp_Idle_locs =
  (prefixed ''idle_noop'' - { ''idle_noop_mfence'', ''idle_noop_init_type'' })
\<union> { ''idle_read_fM'', ''idle_invert_fM'', ''idle_write_fM'', ''idle_flip_noop_mfence'', ''idle_flip_noop_init_type'' }"

locset_definition "hp_IdleInit_locs =
    (prefixed ''idle_flip_noop'' - { ''idle_flip_noop_mfence'', ''idle_flip_noop_init_type'' })
  \<union> { ''idle_phase_init'', ''init_noop_mfence'', ''init_noop_init_type'' }"

locset_definition "hp_InitMark_locs =
  (prefixed ''init_noop'' - { ''init_noop_mfence'', ''init_noop_init_type'' })
\<union> { ''init_phase_mark'', ''mark_read_fM'', ''mark_write_fA'', ''mark_noop_mfence'', ''mark_noop_init_type'' }"

locset_definition "hp_IdleMarkSweep_locs =
     { ''idle_noop_mfence'', ''idle_noop_init_type'', ''mark_end'' }
  \<union>  sweep_locs
  \<union> (mark_loop_locs - { ''mark_loop_get_roots_init_type'' })"

locset_definition "hp_Mark_locs =
    (prefixed ''mark_noop'' - { ''mark_noop_mfence'', ''mark_noop_init_type'' })
  \<union> { ''mark_loop_get_roots_init_type'' }"

abbreviation
  "hs_noop_prefixes \<equiv> {''idle_noop'', ''idle_flip_noop'', ''init_noop'', ''mark_noop'' }"

locset_definition "hs_noop_locs =
  (\<Union>l \<in> hs_noop_prefixes. prefixed l - (suffixed ''_noop_mfence'' \<union> suffixed ''_noop_init_type''))"

locset_definition "hs_get_roots_locs =
  prefixed ''mark_loop_get_roots'' - {''mark_loop_get_roots_init_type''}"

locset_definition "hs_get_work_locs =
  prefixed ''mark_loop_get_work'' - {''mark_loop_get_work_init_type''}"

abbreviation "hs_prefixes \<equiv>
  hs_noop_prefixes \<union> { ''mark_loop_get_roots'', ''mark_loop_get_work'' }"

locset_definition "hs_init_loop_locs = (\<Union>l \<in> hs_prefixes. prefixed (l @ ''_init_loop''))"

locset_definition "hs_done_loop_locs = (\<Union>l \<in> hs_prefixes. prefixed (l @ ''_done_loop''))"

locset_definition "hs_done_locs = (\<Union>l \<in> hs_prefixes. prefixed (l @ ''_done''))"

locset_definition "hs_none_pending_locs = - (hs_init_loop_locs \<union> hs_done_locs)"

locset_definition "hs_in_sync_locs =
  (- ( (\<Union>l \<in> hs_prefixes. prefixed (l @ ''_init'')) \<union> hs_done_locs ))
  \<union> (\<Union>l \<in> hs_prefixes. {l @ ''_init_type''})"

locset_definition "hs_out_of_sync_locs =
  (\<Union>l \<in> hs_prefixes. {l @ ''_init_muts''})"

locset_definition "hs_mut_in_muts_locs =
  (\<Union>l \<in> hs_prefixes. {l @ ''_init_loop_set_pending'', l @ ''_init_loop_done''})"

locset_definition "hs_init_loop_done_locs =
  (\<Union>l \<in> hs_prefixes. {l @ ''_init_loop_done''})"

locset_definition "hs_init_loop_not_done_locs =
  (hs_init_loop_locs - (\<Union>l \<in> hs_prefixes. {l @ ''_init_loop_done''}))"

inv_definition (in gc) handshake_invL :: "('field, 'mut, 'ref) gc_pred" where
  "handshake_invL =
     (atS_gc hs_noop_locs         (sys_handshake_type \<^bold>= \<langle>ht_NOOP\<rangle>)
    \<^bold>\<and> atS_gc hs_get_roots_locs    (sys_handshake_type \<^bold>= \<langle>ht_GetRoots\<rangle>)
    \<^bold>\<and> atS_gc hs_get_work_locs     (sys_handshake_type \<^bold>= \<langle>ht_GetWork\<rangle>)

    \<^bold>\<and> atS_gc hs_mut_in_muts_locs      (gc_mut \<^bold>\<in> gc_muts)
    \<^bold>\<and> atS_gc hs_init_loop_locs        (\<^bold>\<forall>m. \<^bold>\<not>(\<langle>m\<rangle> \<^bold>\<in> gc_muts) \<^bold>\<longrightarrow> sys_handshake_pending m
                                                                  \<^bold>\<or> sys_ghost_handshake_in_sync m)
    \<^bold>\<and> atS_gc hs_init_loop_not_done_locs (\<^bold>\<forall>m.   \<langle>m\<rangle> \<^bold>\<in> gc_muts \<^bold>\<longrightarrow> \<^bold>\<not>(sys_handshake_pending m)
                                                                 \<^bold>\<and> \<^bold>\<not>(sys_ghost_handshake_in_sync m))
    \<^bold>\<and> atS_gc hs_init_loop_done_locs     ( (sys_handshake_pending \<^bold>$ gc_mut
                                        \<^bold>\<or> sys_ghost_handshake_in_sync \<^bold>$ gc_mut)
                                      \<^bold>\<and> (\<^bold>\<forall>m. \<langle>m\<rangle> \<^bold>\<in> gc_muts \<^bold>\<and> \<langle>m\<rangle> \<^bold>\<noteq> gc_mut
                                                                 \<^bold>\<longrightarrow> \<^bold>\<not>(sys_handshake_pending m)
                                                                   \<^bold>\<and> \<^bold>\<not>(sys_ghost_handshake_in_sync m)) )
    \<^bold>\<and> atS_gc hs_done_locs       (\<^bold>\<forall>m. sys_handshake_pending m \<^bold>\<or> sys_ghost_handshake_in_sync m)
    \<^bold>\<and> atS_gc hs_done_loop_locs  (\<^bold>\<forall>m. \<^bold>\<not>(\<langle>m\<rangle> \<^bold>\<in> gc_muts) \<^bold>\<longrightarrow> \<^bold>\<not>(sys_handshake_pending m))
    \<^bold>\<and> atS_gc hs_none_pending_locs (\<^bold>\<forall>m. \<^bold>\<not>(sys_handshake_pending m))
    \<^bold>\<and> atS_gc hs_in_sync_locs      (\<^bold>\<forall>m. sys_ghost_handshake_in_sync m)
    \<^bold>\<and> atS_gc hs_out_of_sync_locs  (\<^bold>\<forall>m. \<^bold>\<not>(sys_handshake_pending m)
                                         \<^bold>\<and> \<^bold>\<not>(sys_ghost_handshake_in_sync m))

    \<^bold>\<and> atS_gc hp_Idle_locs          (sys_ghost_handshake_phase \<^bold>= \<langle>hp_Idle\<rangle>)
    \<^bold>\<and> atS_gc hp_IdleInit_locs      (sys_ghost_handshake_phase \<^bold>= \<langle>hp_IdleInit\<rangle>)
    \<^bold>\<and> atS_gc hp_InitMark_locs      (sys_ghost_handshake_phase \<^bold>= \<langle>hp_InitMark\<rangle>)
    \<^bold>\<and> atS_gc hp_IdleMarkSweep_locs (sys_ghost_handshake_phase \<^bold>= \<langle>hp_IdleMarkSweep\<rangle>)
    \<^bold>\<and> atS_gc hp_Mark_locs          (sys_ghost_handshake_phase \<^bold>= \<langle>hp_Mark\<rangle>))"
(*<*)

lemma hs_get_roots_locs_subseteq_hp_IdleMarkSweep_locs:
  "hs_get_roots_locs \<subseteq> hp_IdleMarkSweep_locs"
by (auto simp: hs_get_roots_locs_def hp_IdleMarkSweep_locs_def mark_loop_locs_def
        intro: append_prefixD)

lemma hs_get_work_locs_subseteq_hp_IdleMarkSweep_locs:
  "hs_get_work_locs \<subseteq> hp_IdleMarkSweep_locs"
apply (simp add: hs_get_work_locs_def hp_IdleMarkSweep_locs_def mark_loop_locs_def)
apply clarsimp
apply (drule mp)
 apply (auto intro: append_prefixD)[1]
apply auto
done

lemma gc_handshake_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s gc, s\<down> gc, sys_ghost_handshake_phase s\<down>, handshake_pending (s\<down> sys), ghost_handshake_in_sync (s\<down> sys), sys_handshake_type s\<down>))
          gc.handshake_invL"
by (simp add: gc.handshake_invL_def eq_imp_def)

lemmas gc_handshake_invL_niE[nie] =
  iffD1[OF gc_handshake_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in gc) handshake_invL[intro]:
  "\<lbrace> handshake_invL \<rbrace> gc"
by vcg_jackhammer_ff

lemma (in sys) gc_handshake_invL[intro]:
  notes gc.handshake_invL_def[inv]
  shows "\<lbrace> gc.handshake_invL \<rbrace> sys"
by vcg_ni

lemma (in gc) handshake_phase_inv[intro]:
  "\<lbrace> handshake_invL \<^bold>\<and> LSTP handshake_phase_inv \<rbrace> gc \<lbrace> LSTP handshake_phase_inv \<rbrace>"
by (vcg_jackhammer_ff simp: handshake_phase_inv_def hp_step_rel_def)

(*>*)
text\<open>

Local handshake phase invariant for the mutators.

\<close>

locset_definition "mut_no_pending_mutates_locs =
    (prefixed ''hs_noop'' - { ''hs_noop'', ''hs_noop_mfence'' })
  \<union> (prefixed ''hs_get_roots'' - { ''hs_get_roots'', ''hs_get_roots_mfence'' })
  \<union> (prefixed ''hs_get_work'' - { ''hs_get_work'', ''hs_get_work_mfence'' })"

inv_definition (in mut_m) handshake_invL :: "('field, 'mut, 'ref) gc_pred" where
  "handshake_invL =
   (atS_mut (prefixed ''hs_noop_'')     (sys_handshake_type \<^bold>= \<langle>ht_NOOP\<rangle> \<^bold>\<and> sys_handshake_pending m)
 \<^bold>\<and> atS_mut (prefixed ''hs_get_roots_'') (sys_handshake_type \<^bold>= \<langle>ht_GetRoots\<rangle> \<^bold>\<and> sys_handshake_pending m)
 \<^bold>\<and> atS_mut (prefixed ''hs_get_work_'')  (sys_handshake_type \<^bold>= \<langle>ht_GetWork\<rangle> \<^bold>\<and> sys_handshake_pending m)
 \<^bold>\<and> atS_mut mut_no_pending_mutates_locs  (LIST_NULL (tso_pending_mutate (mutator m))))"
(*<*)

lemma (in mut_m) handshake_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s (mutator m), s\<down> (mutator m), sys_handshake_type s\<down>, handshake_pending (s\<down> sys), mem_write_buffers (s\<down> sys) (mutator m)))
          handshake_invL"
by (simp add: eq_imp_def handshake_invL_def)

lemmas mut_m_handshake_invL_niE[nie] =
  iffD1[OF mut_m.handshake_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in mut_m) handshake_invL[intro]:
  "\<lbrace> handshake_invL \<rbrace> mutator m"
by vcg_jackhammer

lemma (in mut_m') handshake_invL[intro]:
  "\<lbrace> handshake_invL \<rbrace> mutator m'"
by vcg_nihe vcg_ni+

lemma (in gc) mut_handshake_invL[intro]:
  notes mut_m.handshake_invL_def[inv]
  shows "\<lbrace> handshake_invL \<^bold>\<and> mut_m.handshake_invL m \<rbrace> gc \<lbrace> mut_m.handshake_invL m \<rbrace>"
by vcg_nihe vcg_ni+

lemma (in sys) mut_handshake_invL[intro]:
  notes mut_m.handshake_invL_def[inv]
  shows "\<lbrace> mut_m.handshake_invL m \<rbrace> sys"
by (vcg_ni split: if_splits)

lemma (in mut_m) gc_handshake_invL[intro]:
  notes gc.handshake_invL_def[inv]
  shows "\<lbrace> handshake_invL \<^bold>\<and> gc.handshake_invL \<rbrace> mutator m \<lbrace> gc.handshake_invL \<rbrace>"
by vcg_nihe vcg_ni+

lemma (in mut_m) handshake_phase_inv[intro]:
  "\<lbrace> handshake_invL \<^bold>\<and> LSTP handshake_phase_inv \<rbrace> mutator m \<lbrace> LSTP handshake_phase_inv \<rbrace>"
by (vcg_jackhammer simp: handshake_phase_inv_def) (auto simp: hp_step_rel_def)

(*>*)
text\<open>

Relate @{const "sys_ghost_handshake_phase"}, @{const "gc_phase"},
@{const "sys_phase"} and writes to the phase in the GC's TSO buffer.

The first relation treats the case when the GC's TSO buffer does not
contain any writes to the phase.

The second relation exhibits the data race on the phase variable: we
need to precisely track the possible states of the GC's TSO buffer.

\<close>

definition handshake_phase_rel :: "handshake_phase \<Rightarrow> bool \<Rightarrow> gc_phase \<Rightarrow> bool" where
  "handshake_phase_rel hp in_sync ph \<equiv>
     case hp of
       hp_Idle          \<Rightarrow> ph = ph_Idle
     | hp_IdleInit      \<Rightarrow> ph = ph_Idle \<or> (in_sync \<and> ph = ph_Init)
     | hp_InitMark      \<Rightarrow> ph = ph_Init \<or> (in_sync \<and> ph = ph_Mark)
     | hp_Mark          \<Rightarrow> ph = ph_Mark
     | hp_IdleMarkSweep \<Rightarrow> ph = ph_Mark \<or> (in_sync \<and> ph \<in> { ph_Idle, ph_Sweep })"

definition phase_rel :: "(bool \<times> handshake_phase \<times> gc_phase \<times> gc_phase \<times> ('field, 'ref) mem_write_action list) set" where
  "phase_rel \<equiv>
      { (in_sync, hp, ph, ph, []) |in_sync hp ph. handshake_phase_rel hp in_sync ph }
    \<union> ({True} \<times> { (hp_IdleInit, ph_Init, ph_Idle, [mw_Phase ph_Init]),
                  (hp_InitMark, ph_Mark, ph_Init, [mw_Phase ph_Mark]),
                  (hp_IdleMarkSweep, ph_Sweep, ph_Mark, [mw_Phase ph_Sweep]),
                  (hp_IdleMarkSweep, ph_Idle, ph_Mark, [mw_Phase ph_Sweep, mw_Phase ph_Idle]),
                  (hp_IdleMarkSweep, ph_Idle, ph_Sweep, [mw_Phase ph_Idle]) })"

definition phase_rel_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "phase_rel_inv = ((\<^bold>\<forall>m. sys_ghost_handshake_in_sync m) \<^bold>\<otimes> sys_ghost_handshake_phase \<^bold>\<otimes> gc_phase \<^bold>\<otimes> sys_phase \<^bold>\<otimes> tso_pending_phase gc \<^bold>\<in> \<langle>phase_rel\<rangle>)"
(*<*)

simps_of_case handshake_phase_rel_simps[simp]: handshake_phase_rel_def (splits: handshake_phase.split)

lemma phase_rel_invD:
  "phase_rel_inv s \<Longrightarrow> (\<forall>m. sys_ghost_handshake_in_sync m s, sys_ghost_handshake_phase s, gc_phase s, sys_phase s, tso_pending_phase gc s) \<in> phase_rel"
by (simp add: phase_rel_inv_def)

lemma phases_rel_Id[iff]:
  "(\<forall>m. sys_ghost_handshake_in_sync m s, sys_ghost_handshake_phase s, gc_phase s, sys_phase s, tso_pending_phase gc s) \<in> phase_rel
     \<Longrightarrow> (\<forall>ph. mw_Phase ph \<notin> set (sys_mem_write_buffers gc s)) \<longleftrightarrow> sys_phase s = gc_phase s"
by (auto simp: phase_rel_def filter_empty_conv filter_eq_Cons_iff)

(*>*)
text\<open>

Tie the garbage collector's control location to the value of @{const
"gc_phase"}.

\<close>

locset_definition no_pending_phase_locs :: "location set" where
  "no_pending_phase_locs \<equiv>
       (idle_locs - { ''idle_noop_mfence'' })
     \<union> (init_locs - { ''init_noop_mfence'' })
     \<union> (mark_locs - { ''mark_read_fM'', ''mark_write_fA'', ''mark_noop_mfence'' })"

inv_definition (in gc) phase_invL :: "('field, 'mut, 'ref) gc_pred" where
  "phase_invL =
     (atS_gc idle_locs             (gc_phase \<^bold>= \<langle>ph_Idle\<rangle>)
  \<^bold>\<and> atS_gc init_locs             (gc_phase \<^bold>= \<langle>ph_Init\<rangle>)
  \<^bold>\<and> atS_gc mark_locs             (gc_phase \<^bold>= \<langle>ph_Mark\<rangle>)
  \<^bold>\<and> atS_gc sweep_locs            (gc_phase \<^bold>= \<langle>ph_Sweep\<rangle>)
  \<^bold>\<and> atS_gc no_pending_phase_locs (LIST_NULL (tso_pending_phase gc)))"
(*<*)

lemma (in gc) phase_invL_eq_imp:
  "eq_imp (\<lambda>r (s :: ('field, 'mut, 'ref) gc_pred_state). (AT s gc, s\<down> gc, tso_pending_phase gc s\<down>))
          phase_invL"
by (clarsimp simp: eq_imp_def inv)

lemmas gc_phase_invL_niE[nie] =
  iffD1[OF gc.phase_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in gc) phase_invL[intro]:
  "\<lbrace> phase_invL \<^bold>\<and> LSTP phase_rel_inv \<rbrace> gc \<lbrace> phase_invL \<rbrace>"
by (vcg_jackhammer dest!: phase_rel_invD simp: phase_rel_def)

lemma (in sys) gc_phase_invL[intro]:
  notes gc.phase_invL_def[inv]
  shows "\<lbrace> gc.phase_invL \<^bold>\<and> LSTP tso_writes_inv \<rbrace> sys \<lbrace> gc.phase_invL \<rbrace>"
by (vcg_ni split: if_splits)

lemma (in mut_m) gc_phase_invL[intro]:
  notes gc.phase_invL_def[inv]
  shows "\<lbrace> gc.phase_invL \<rbrace> mutator m"
by vcg_nihe

lemma (in gc) phase_rel_inv[intro]:
  notes phase_rel_inv_def[inv]
  shows "\<lbrace> handshake_invL \<^bold>\<and> phase_invL \<^bold>\<and> LSTP phase_rel_inv \<rbrace> gc \<lbrace> LSTP phase_rel_inv \<rbrace>"
by (vcg_jackhammer_ff dest!: phase_rel_invD simp: phase_rel_def)

lemma (in sys) phase_rel_inv[intro]:
  notes gc.phase_invL_def[inv] phase_rel_inv_def[inv]
  shows "\<lbrace> LSTP (phase_rel_inv \<^bold>\<and> tso_writes_inv) \<rbrace> sys \<lbrace> LSTP phase_rel_inv \<rbrace>"
apply vcg_jackhammer
apply (simp add: phase_rel_def p_not_sys split: if_splits)
apply (elim disjE; auto split: if_splits)
done

lemma (in mut_m) phase_rel_inv[intro]:
  "\<lbrace> handshake_invL \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> phase_rel_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP phase_rel_inv \<rbrace>"
apply (vcg_jackhammer simp: phase_rel_inv_def)
subgoal by (auto dest!: handshake_phase_invD
             simp: handshake_phase_rel_def phase_rel_def hp_step_rel_def
            split: handshake_phase.splits)
subgoal by (auto dest!: handshake_phase_invD
             simp: handshake_phase_rel_def phase_rel_def hp_step_rel_def
            split: handshake_phase.splits)
subgoal by (auto dest!: handshake_phase_invD
             simp: handshake_phase_rel_def phase_rel_def hp_step_rel_def
            split: handshake_phase.splits)
done

(*>*)
text\<open>

Validity of @{const "sys_fM"} wrt @{const "gc_fM"} and the handshake
phase. Effectively we use @{const "gc_fM"} as ghost state. We also
include the TSO lock to rule out the GC having any pending marks
during the @{const "hp_Idle"} handshake phase.

\<close>

definition fM_rel :: "(bool \<times> handshake_phase \<times> gc_mark \<times> gc_mark \<times> ('field, 'ref) mem_write_action list \<times> bool) set" where
  "fM_rel =
      { (in_sync, hp, fM, fM, [], l) |fM hp in_sync l. hp = hp_Idle \<longrightarrow> \<not>in_sync }
    \<union> { (in_sync, hp_Idle, fM, fM', [], l) |fM fM' in_sync l. in_sync }
    \<union> { (in_sync, hp_Idle, \<not>fM, fM, [mw_fM (\<not>fM)], False) |fM in_sync. in_sync }"

definition fM_rel_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "fM_rel_inv = ((\<^bold>\<forall>m. sys_ghost_handshake_in_sync m) \<^bold>\<otimes> sys_ghost_handshake_phase \<^bold>\<otimes> gc_fM \<^bold>\<otimes> sys_fM \<^bold>\<otimes> tso_pending_fM gc \<^bold>\<otimes> (sys_mem_lock \<^bold>= \<langle>Some gc\<rangle>) \<^bold>\<in> \<langle>fM_rel\<rangle>)"

definition fA_rel :: "(bool \<times> handshake_phase \<times> gc_mark \<times> gc_mark \<times> ('field, 'ref) mem_write_action list) set" where
  "fA_rel =
      { (in_sync, hp_Idle,          fA,  fM, []) |fA fM in_sync. \<not>in_sync \<longrightarrow> fA = fM }
    \<union> { (in_sync, hp_IdleInit,      fA, \<not>fA, []) |fA in_sync. True }
    \<union> { (in_sync, hp_InitMark,      fA, \<not>fA, [mw_fA (\<not>fA)]) |fA in_sync. in_sync }
    \<union> { (in_sync, hp_InitMark,      fA,  fM, []) |fA fM in_sync. \<not>in_sync \<longrightarrow> fA \<noteq> fM }
    \<union> { (in_sync, hp_Mark,          fA,  fA, []) |fA in_sync. True }
    \<union> { (in_sync, hp_IdleMarkSweep, fA,  fA, []) |fA in_sync. True }"

definition fA_rel_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "fA_rel_inv = ((\<^bold>\<forall>m. sys_ghost_handshake_in_sync m) \<^bold>\<otimes> sys_ghost_handshake_phase \<^bold>\<otimes> sys_fA \<^bold>\<otimes> gc_fM \<^bold>\<otimes> tso_pending_fA gc \<^bold>\<in> \<langle>fA_rel\<rangle>)"

locset_definition "fM_eq_locs = (- { ''idle_write_fM'', ''idle_flip_noop_mfence'' })"
locset_definition "fM_tso_empty_locs = (- { ''idle_flip_noop_mfence'' })"
locset_definition "fA_tso_empty_locs = (- { ''mark_noop_mfence'' })"

locset_definition
  "fA_eq_locs \<equiv> { ''idle_read_fM'', ''idle_invert_fM'' }
              \<union> prefixed ''idle_noop''
              \<union> (mark_locs - { ''mark_read_fM'', ''mark_write_fA'', ''mark_noop_mfence'' })
              \<union> sweep_locs"

locset_definition
  "fA_neq_locs \<equiv> { ''idle_phase_init'', ''idle_write_fM'', ''mark_read_fM'', ''mark_write_fA'' }
               \<union> prefixed ''idle_flip_noop''
               \<union> init_locs"

inv_definition (in gc) fM_fA_invL :: "('field, 'mut, 'ref) gc_pred" where
  "fM_fA_invL =
   (atS_gc fM_eq_locs                    (sys_fM  \<^bold>= gc_fM)
  \<^bold>\<and> at_gc ''idle_write_fM''              (sys_fM \<^bold>\<noteq> gc_fM)
  \<^bold>\<and> at_gc ''idle_flip_noop_mfence''      (sys_fM \<^bold>\<noteq> gc_fM \<^bold>\<longrightarrow> (\<^bold>\<not>(LIST_NULL (tso_pending_fM gc))))
  \<^bold>\<and> atS_gc fM_tso_empty_locs             (LIST_NULL (tso_pending_fM gc))

  \<^bold>\<and> atS_gc fA_eq_locs                    (sys_fA  \<^bold>= gc_fM)
  \<^bold>\<and> atS_gc fA_neq_locs                   (sys_fA \<^bold>\<noteq> gc_fM)
  \<^bold>\<and> at_gc ''mark_noop_mfence''           (sys_fA \<^bold>\<noteq> gc_fM \<^bold>\<longrightarrow> (\<^bold>\<not>(LIST_NULL (tso_pending_fA gc))))
  \<^bold>\<and> atS_gc fA_tso_empty_locs             (LIST_NULL (tso_pending_fA gc)))"
(*<*)

lemmas fM_rel_invD = iffD1[OF fun_cong[OF fM_rel_inv_def[simplified atomize_eq]]]

lemma do_write_action_fM[simp]:
  "\<lbrakk> sys_mem_write_buffers p s = w # ws; tso_writes_inv s; handshake_phase_inv s; fM_rel_inv s;
     ghost_handshake_phase (s (mutator m)) \<noteq> hp_Idle \<or> (sys_ghost_handshake_phase s = hp_IdleMarkSweep \<and> All (ghost_handshake_in_sync (s sys)));
     p \<noteq> sys \<rbrakk>
     \<Longrightarrow> fM (do_write_action w (s sys)) = fM (s sys)"
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (clarsimp simp: do_write_action_def p_not_sys
               split: mem_write_action.splits)
apply (simp add: hp_step_rel_def)
apply (elim disjE, auto simp: fM_rel_inv_def fM_rel_def)
done

lemmas fA_rel_invD = iffD1[OF fun_cong[OF fA_rel_inv_def[simplified atomize_eq]]]

lemma gc_fM_fA_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. (AT s gc, s\<down> gc, sys_fA s\<down>, sys_fM s\<down>, sys_mem_write_buffers gc s\<down>))
          gc.fM_fA_invL"
by (simp add: gc.fM_fA_invL_def eq_imp_def)

lemmas gc_fM_fA_invL_niE[nie] =
  iffD1[OF gc_fM_fA_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode], rotated -1]

lemma (in gc) fM_fA_invL[intro]:
  "\<lbrace> fM_fA_invL \<rbrace> gc"
by vcg_jackhammer

lemma (in gc) fM_rel_inv[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> handshake_invL \<^bold>\<and> tso_lock_invL \<^bold>\<and> LSTP fM_rel_inv \<rbrace>
     gc
   \<lbrace> LSTP fM_rel_inv \<rbrace>"
by (vcg_jackhammer simp: fM_rel_inv_def fM_rel_def)

lemma (in gc) fA_rel_inv[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> handshake_invL \<^bold>\<and> LSTP fA_rel_inv \<rbrace>
     gc
   \<lbrace> LSTP fA_rel_inv \<rbrace>"
by (vcg_jackhammer simp: fA_rel_inv_def; auto simp: fA_rel_def)

lemma (in mut_m) gc_fM_fA_invL[intro]:
  notes gc.fM_fA_invL_def[inv]
  shows "\<lbrace> gc.fM_fA_invL \<rbrace> mutator m"
by vcg_nihe

lemma (in mut_m) fM_rel_inv[intro]:
  "\<lbrace> LSTP fM_rel_inv \<rbrace> mutator m"
by (vcg_jackhammer simp: fM_rel_inv_def fM_rel_def; elim disjE; auto split: if_splits)
(* FIXME trivial but eta reduction plays merry hell *)

lemma (in mut_m) fA_rel_inv[intro]:
  "\<lbrace> LSTP fA_rel_inv \<rbrace> mutator m"
by (vcg_jackhammer simp: fA_rel_inv_def; simp add: fA_rel_def; elim disjE; auto split: if_splits)

lemma fA_neq_locs_diff_fA_tso_empty_locs[simp]:
  "fA_neq_locs - fA_tso_empty_locs = {}"
by (simp add: fA_neq_locs_def fA_tso_empty_locs_def loc)

lemma (in sys) gc_fM_fA_invL[intro]:
  notes gc.fM_fA_invL_def[inv]
  shows
  "\<lbrace> gc.fM_fA_invL \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> tso_writes_inv) \<rbrace>
     sys
   \<lbrace> gc.fM_fA_invL \<rbrace>"
apply (vcg_ni simp: p_not_sys)

apply (erule disjE)
 apply (clarsimp simp: fM_rel_inv_def fM_rel_def split: if_splits)
apply (clarsimp simp: fM_rel_inv_def fM_rel_def filter_empty_conv)

apply (erule disjE; clarsimp)

apply (rule conjI; clarsimp simp: fM_rel_inv_def fM_rel_def split: if_splits)

apply (clarsimp split: if_splits)

apply (erule disjE)
 apply (clarsimp simp: fA_rel_inv_def fA_rel_def)
apply clarsimp

apply (erule disjE)
 apply (clarsimp simp: fA_rel_inv_def fA_rel_def fM_rel_inv_def fM_rel_def)
 apply (drule (1) atS_dests(3), fastforce simp: atS_simps)
apply clarsimp

apply (rule conjI)
 apply (clarsimp simp: fA_rel_inv_def fA_rel_def split: if_splits)
apply clarsimp

apply (clarsimp split: if_splits)
done

lemma (in sys) fM_rel_inv[intro]:
  "\<lbrace> LSTP (fM_rel_inv \<^bold>\<and> tso_writes_inv) \<rbrace> sys \<lbrace> LSTP fM_rel_inv \<rbrace>"
apply (vcg_ni simp: p_not_sys)
apply (fastforce simp: do_write_action_def fM_rel_inv_def fM_rel_def
                split: mem_write_action.splits)
done

lemma (in sys) fA_rel_inv[intro]:
  "\<lbrace> LSTP (fA_rel_inv \<^bold>\<and> tso_writes_inv) \<rbrace> sys \<lbrace> LSTP fA_rel_inv \<rbrace>"
apply (vcg_ni simp: p_not_sys)
apply (fastforce simp: do_write_action_def fA_rel_inv_def fA_rel_def
                split: mem_write_action.splits)
done

lemma mut_m_get_roots_no_fM_write:
  "\<lbrakk> atS (mutator m) (prefixed ''hs_get_roots_'') s; mut_m.handshake_invL m s; handshake_phase_inv s\<down>; fM_rel_inv s\<down>; tso_writes_inv s\<down>; p \<noteq> sys \<rbrakk>
     \<Longrightarrow> \<not>sys_mem_write_buffers p s\<down> = mw_fM fl # ws"
unfolding mut_m.handshake_invL_def
apply (elim conjE)
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule fM_rel_invD)
apply (fastforce simp: hp_step_rel_def fM_rel_def loc filter_empty_conv p_not_sys)
done

lemma mut_m_get_roots_no_phase_write:
  "\<lbrakk> atS (mutator m) (prefixed ''hs_get_roots_'') s; mut_m.handshake_invL m s; handshake_phase_inv s\<down>; phase_rel_inv s\<down>; tso_writes_inv s\<down>; p \<noteq> sys \<rbrakk>
     \<Longrightarrow> \<not>sys_mem_write_buffers p s\<down> = mw_Phase ph # ws"
unfolding mut_m.handshake_invL_def
apply (elim conjE)
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule phase_rel_invD)
apply (fastforce simp: hp_step_rel_def phase_rel_def loc filter_empty_conv p_not_sys)
done

lemma mut_m_not_idle_no_fM_write:
  "\<lbrakk> ghost_handshake_phase (s (mutator m)) \<noteq> hp_Idle; fM_rel_inv s; handshake_phase_inv s; tso_writes_inv s; p \<noteq> sys \<rbrakk>
     \<Longrightarrow> \<not>sys_mem_write_buffers p s = mw_fM fl # ws"
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (drule fM_rel_invD)
apply (fastforce simp: hp_step_rel_def fM_rel_def filter_empty_conv p_not_sys)
done

lemma (in mut_m) mut_ghost_handshake_phase_idle:
  "\<lbrakk> mut_ghost_handshake_phase s = hp_Idle; handshake_phase_inv s; phase_rel_inv s \<rbrakk>
     \<Longrightarrow> sys_phase s = ph_Idle"
by (auto dest!: phase_rel_invD handshake_phase_invD
          simp: phase_rel_def hp_step_rel_def)
(*>*)
(*<*)

end
(*>*)
