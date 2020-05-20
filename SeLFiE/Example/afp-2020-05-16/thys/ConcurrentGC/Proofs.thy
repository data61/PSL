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

theory Proofs
imports
  StrongTricolour
begin

(*>*)
section\<open>Top-level safety \label{sec:top-level-correctness}\<close>

subsection\<open>Invariants\<close>

definition (in gc) invsL :: "('field, 'mut, 'ref) gc_pred" where
  "invsL \<equiv>
    fM_fA_invL
  \<^bold>\<and> gc_mark.mark_object_invL
  \<^bold>\<and> gc_W_empty_invL
  \<^bold>\<and> handshake_invL
  \<^bold>\<and> obj_fields_marked_invL
  \<^bold>\<and> phase_invL
  \<^bold>\<and> sweep_loop_invL
  \<^bold>\<and> tso_lock_invL
  \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv)"

definition (in mut_m) invsL :: "('field, 'mut, 'ref) gc_pred" where
  "invsL \<equiv>
    mark_object_invL
  \<^bold>\<and> mut_get_roots.mark_object_invL m
  \<^bold>\<and> mut_store_ins.mark_object_invL m
  \<^bold>\<and> mut_store_del.mark_object_invL m
  \<^bold>\<and> handshake_invL
  \<^bold>\<and> tso_lock_invL
  \<^bold>\<and> LSTP mutator_phase_inv"

definition invs :: "('field, 'mut, 'ref) lsts_pred" where
  "invs \<equiv>
    handshake_phase_inv
  \<^bold>\<and> phase_rel_inv
  \<^bold>\<and> strong_tricolour_inv
  \<^bold>\<and> sys_phase_inv
  \<^bold>\<and> tso_writes_inv
  \<^bold>\<and> valid_refs_inv
  \<^bold>\<and> valid_W_inv"

definition I :: "('field, 'mut, 'ref) gc_pred" where
  "I \<equiv>
     gc.invsL
  \<^bold>\<and> (\<^bold>\<forall>m. mut_m.invsL m)
  \<^bold>\<and> LSTP invs"
(*<*)

lemmas I_defs = gc.invsL_def mut_m.invsL_def invs_def I_def

lemma (in gc) I:
  "\<lbrace> I \<rbrace> gc"
apply (simp add: I_defs)
apply (rule valid_pre)
apply ( rule valid_conj_lift valid_all_lift | fastforce )+
done

lemma (in sys) I:
  "\<lbrace> I \<rbrace> sys"
apply (simp add: I_defs)
apply (rule valid_pre)
apply ( rule valid_conj_lift valid_all_lift | fastforce )+
done

text\<open>

We need to separately treat the two cases of a single mutator and
multiple mutators. In the latter case we have the additional
obligation of showing mutual non-interference amongst mutators.

\<close>

lemma mut_invsL[intro]:
  "\<lbrace>I\<rbrace> mutator m \<lbrace>mut_m.invsL m'\<rbrace>"
proof(cases "m = m'")
  case True
  interpret mut_m m' by unfold_locales
  from True show ?thesis
    apply (simp add: I_defs)
    apply (rule valid_pre)
    apply ( rule valid_conj_lift valid_all_lift | fastforce )+
    done
next
  case False
  then interpret mut_m' m' m by unfold_locales blast
  from False show ?thesis
    apply (simp add: I_defs)
    apply (rule valid_pre)
    apply ( rule valid_conj_lift valid_all_lift | fastforce )+
    done
qed

lemma (in mut_m) I:
  "\<lbrace> I \<rbrace> mutator m"
apply (simp add: I_def gc.invsL_def invs_def)
apply (rule valid_pre)
apply ( rule valid_conj_lift valid_all_lift | fastforce )+
apply (simp add: I_defs)
done

(*>*)

subsection\<open>Initial conditions\<close>

text\<open>

We ask that the GC and system initially agree on some things:
\begin{itemize}

\item All objects on the heap are marked (have their flags equal to
  @{const "sys_fM"}, and there are no grey references, i.e. the heap
  is uniformly black.

\item The GC and system have the same values for @{term "fA"}, @{term
  "fM"}, etc. and the phase is @{term "Idle"}.

\item No process holds the TSO lock and all write buffers are empty.

\item All root-reachable references are backed by objects.

\end{itemize}
Note that these are merely sufficient initial conditions and can be
weakened.

\<close>

locale gc_system =
  fixes initial_mark :: gc_mark
begin

definition gc_initial_state :: "('field, 'mut, 'ref) lst_pred" where
  "gc_initial_state s \<equiv>
     fM s = initial_mark
   \<and> phase s = ph_Idle
   \<and> ghost_honorary_grey s = {}
   \<and> W s = {}"

definition mut_initial_state :: "('field, 'mut, 'ref) lst_pred" where
  "mut_initial_state s \<equiv>
     ghost_handshake_phase s = hp_IdleMarkSweep
   \<and> ghost_honorary_grey s = {}
   \<and> ghost_honorary_root s = {}
   \<and> W s = {}"

definition sys_initial_state :: "('field, 'mut, 'ref) lst_pred" where
  "sys_initial_state s \<equiv>
     (\<forall>m. \<not>handshake_pending s m \<and> ghost_handshake_in_sync s m)
   \<and> ghost_handshake_phase s = hp_IdleMarkSweep \<and> handshake_type s = ht_GetRoots
   \<and> obj_mark ` ran (heap s) \<subseteq> {initial_mark}
   \<and> fA s = initial_mark
   \<and> fM s = initial_mark
   \<and> phase s = ph_Idle
   \<and> ghost_honorary_grey s = {}
   \<and> W s = {}
   \<and> (\<forall>p. mem_write_buffers s p = [])
   \<and> mem_lock s = None"

abbreviation
  "root_reachable y \<equiv> \<^bold>\<exists>m x. \<langle>x\<rangle> \<^bold>\<in> mut_m.mut_roots m \<^bold>\<and> x reaches y"

definition valid_refs :: "('field, 'mut, 'ref) lsts_pred" where
  "valid_refs \<equiv> \<^bold>\<forall>y. root_reachable y \<^bold>\<longrightarrow> valid_ref y"

definition gc_system_init :: "('field, 'mut, 'ref) lsts_pred" where
  "gc_system_init \<equiv>
       (\<lambda>s. gc_initial_state (s gc))
     \<^bold>\<and> (\<lambda>s. \<forall>m. mut_initial_state (s (mutator m)))
     \<^bold>\<and> (\<lambda>s. sys_initial_state (s sys))
     \<^bold>\<and> valid_refs"

text\<open>

The system consists of the programs and these constraints on the initial state.

\<close>

abbreviation gc_system :: "('field, 'mut, 'ref) gc_system" where
  "gc_system \<equiv> (gc_pgms, gc_system_init)"
(*<*)

lemma init_strong_tricolour_inv:
  "\<lbrakk> obj_mark ` ran (sys_heap (mkP (s, []))\<down>) \<subseteq> {gc_fM (mkP (s, []))\<down>};
     sys_fM (mkP (s, []))\<down> = gc_fM (mkP (s, []))\<down> \<rbrakk>
     \<Longrightarrow> strong_tricolour_inv (mkP (s, []))\<down>"
by (auto simp: strong_tricolour_inv_def ran_def
        split: obj_at_splits)

lemma init_no_grey_refs:
  "\<lbrakk> gc_W (mkP (s, []))\<down> = {}; \<forall>m. W ((mkP (s, []))\<down> (mutator m)) = {}; sys_W (mkP (s, []))\<down> = {};
     gc_ghost_honorary_grey (mkP (s, []))\<down> = {}; \<forall>m. ghost_honorary_grey ((mkP (s, []))\<down> (mutator m)) = {}; sys_ghost_honorary_grey (mkP (s, []))\<down> = {} \<rbrakk>
     \<Longrightarrow> no_grey_refs (mkP (s, []))\<down>"
apply (clarsimp simp: no_grey_refs_def grey_def)
apply (rename_tac x xa)
apply (case_tac xa)
apply (auto simp: WL_def)
done

lemma valid_refs_imp_valid_refs_inv:
  "\<lbrakk> valid_refs s; no_grey_refs s; \<forall>p. sys_mem_write_buffers p s = []; \<forall>m. ghost_honorary_root (s (mutator m)) = {} \<rbrakk>
     \<Longrightarrow> valid_refs_inv s"
by (auto simp: valid_refs_def valid_refs_inv_def mut_m.reachable_def mut_m.tso_write_refs_def
         dest: no_grey_refs_not_grey_reachableD)

lemma no_grey_refs_imp_valid_W_inv:
  "\<lbrakk> no_grey_refs s; \<forall>p. sys_mem_write_buffers p s = [] \<rbrakk>
     \<Longrightarrow> valid_W_inv s"
unfolding valid_W_inv_def
by (auto simp: no_grey_refs_def grey_def WL_def)

lemma init_inv_sys: "\<forall>s\<in>initial_states gc_system. invs (mkP (s, []))\<down>"
apply (clarsimp dest!: initial_statesD
              simp: gc_system_init_def invs_def gc_initial_state_def mut_initial_state_def sys_initial_state_def
                    inv
                    handshake_phase_rel_def handshake_phase_inv_def hp_step_rel_def phase_rel_inv_def phase_rel_def
                    tso_writes_inv_def
                    init_no_grey_refs init_strong_tricolour_inv no_grey_refs_imp_valid_W_inv
                    valid_refs_imp_valid_refs_inv
                    all_conj_distrib)
done

lemma init_inv_gc: "\<forall>s\<in>initial_states gc_system. gc.invsL (mkP (s, []))"
apply (clarsimp dest!: initial_statesD)
apply (drule fun_cong[where x=gc]) (* hacky *)
apply (simp add: com)
apply (clarsimp simp: gc_system_init_def gc_initial_state_def mut_initial_state_def sys_initial_state_def
                      gc.invsL_def inv
                      gc.fM_fA_invL_def fA_rel_inv_def fA_rel_def fM_rel_inv_def fM_rel_def gc.handshake_invL_def
                      gc.obj_fields_marked_invL_def gc.phase_invL_def gc.sweep_loop_invL_def
                      gc.tso_lock_invL_def gc.gc_W_empty_invL_def
                      init_no_grey_refs
                      loc atS_simps
                      all_conj_distrib)
apply (auto simp: ran_def image_subset_iff split: obj_at_splits)
done

lemma valid_refs_imp_reachable_snapshot_inv:
  "\<lbrakk> valid_refs s; obj_mark ` ran (sys_heap s) \<subseteq> {sys_fM s}; \<forall>p. sys_mem_write_buffers p s = []; \<forall>m. ghost_honorary_root (s (mutator m)) = {} \<rbrakk>
     \<Longrightarrow> mut_m.reachable_snapshot_inv m s"
apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def valid_refs_def)
apply (auto simp: image_subset_iff ran_def black_def mut_m.reachable_def mut_m.tso_write_refs_def
           split: obj_at_splits)
done

lemma init_inv_mut: "\<forall>s\<in>initial_states gc_system. mut_m.invsL m (mkP (s, []))"
apply (clarsimp dest!: initial_statesD)
apply (drule fun_cong[where x="mutator m"]) (* hacky *)
apply (simp add: com)
apply (clarsimp simp: gc_system_init_def mut_initial_state_def sys_initial_state_def
                      valid_refs_imp_reachable_snapshot_inv
                      mut_m.invsL_def inv
                      mut_m.mark_object_invL_def
                      mut_m.handshake_invL_def mut_m.tso_lock_invL_def
                      mut_m.marked_deletions_def mut_m.marked_insertions_def
                      loc atS_simps)
done

lemma init_inv: "\<forall>s\<in>initial_states gc_system. I (mkP (s, []))"
by (simp add: I_def init_inv_sys init_inv_gc init_inv_mut)

(*>*)
text\<open>\<close>

theorem inv: "s \<in> reachable_states gc_system \<Longrightarrow> I (mkP s)"
(*<*)
apply (erule VCG)
 apply (rule init_inv)
apply (rename_tac p)
apply (case_tac p, simp_all)
  apply (rule mut_m.I[unfolded valid_proc_def, simplified])
 apply (rule gc.I[unfolded valid_proc_def, simplified])
apply (rule sys.I[unfolded valid_proc_def, simplified])
done

(*>*)
text\<open>

Our headline safety result follows directly.

\<close>

corollary safety:
  "s \<in> reachable_states gc_system \<Longrightarrow> valid_refs (mkP s)\<down>"
(*<*)
apply (drule inv)
apply (clarsimp simp: I_def invs_def valid_refs_inv_def valid_refs_def)
apply (rename_tac x xa xb)
apply (drule_tac x=x in spec)
apply clarsimp
apply (drule_tac x=xa in spec, fastforce simp: mut_m.reachable_def)
done

(*>*)
text\<open>\<close>

end

text\<open>

The GC is correct for the remaining fixed-but-arbitrary initial
conditions.

\<close>

interpretation gc_system_interpretation: gc_system undefined .


subsection\<open>A concrete system state\<close>

text\<open>

We demonstrate that our definitions are not vacuous by exhibiting a
concrete initial state that satisfies the initial conditions. We use
Isabelle's notation for types of a given size.

\<close>
(*<*)

end
(*>*)
