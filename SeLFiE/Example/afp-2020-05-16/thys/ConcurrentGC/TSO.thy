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

theory TSO
imports
  Proofs_basis
begin

(*>*)
subsection\<open>Coarse TSO invariants\<close>

text\<open>

Very coarse invariants about what processes write, and when they hold
the TSO lock.

\<close>

abbreviation gc_writes :: "('field, 'ref) mem_write_action \<Rightarrow> bool" where
  "gc_writes w \<equiv> case w of mw_Mark _ _ \<Rightarrow> True | mw_Phase _ \<Rightarrow> True | mw_fM _ \<Rightarrow> True | mw_fA _ \<Rightarrow> True | _ \<Rightarrow> False"

abbreviation mut_writes :: "('field, 'ref) mem_write_action \<Rightarrow> bool" where
  "mut_writes w \<equiv> case w of mw_Mutate _ _ _ \<Rightarrow> True | mw_Mark _ _ \<Rightarrow> True | _ \<Rightarrow> False"

definition tso_writes_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "tso_writes_inv \<equiv>
      (\<^bold>\<forall>w.   tso_pending_write gc          w \<^bold>\<longrightarrow> \<langle>gc_writes w\<rangle>)
   \<^bold>\<and> (\<^bold>\<forall>m w. tso_pending_write (mutator m) w \<^bold>\<longrightarrow> \<langle>mut_writes w\<rangle>)"
(*<*)

lemma tso_writes_inv_eq_imp:
  "eq_imp (\<lambda>p s. mem_write_buffers (s sys) p)
          tso_writes_inv"
by (simp add: eq_imp_def tso_writes_inv_def)

lemmas tso_writes_inv_fun_upd[simp] = eq_imp_fun_upd[OF tso_writes_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma tso_writes_invD[simp]:
  "tso_writes_inv s \<Longrightarrow> \<not>sys_mem_write_buffers gc s = mw_Mutate r f r' # ws"
  "tso_writes_inv s \<Longrightarrow> \<not>sys_mem_write_buffers (mutator m) s = mw_fA fl # ws"
  "tso_writes_inv s \<Longrightarrow> \<not>sys_mem_write_buffers (mutator m) s = mw_fM fl # ws"
  "tso_writes_inv s \<Longrightarrow> \<not>sys_mem_write_buffers (mutator m) s = mw_Phase ph # ws"
by (auto simp: tso_writes_inv_def dest!: spec[where x=m])

lemma mut_do_write_action[simp]:
  "\<lbrakk> sys_mem_write_buffers (mutator m) s = w # ws; tso_writes_inv s \<rbrakk> \<Longrightarrow> fA (do_write_action w (s sys)) = sys_fA s"
  "\<lbrakk> sys_mem_write_buffers (mutator m) s = w # ws; tso_writes_inv s \<rbrakk> \<Longrightarrow> fM (do_write_action w (s sys)) = sys_fM s"
  "\<lbrakk> sys_mem_write_buffers (mutator m) s = w # ws; tso_writes_inv s \<rbrakk> \<Longrightarrow> phase (do_write_action w (s sys)) = sys_phase s"
by (auto simp: do_write_action_def split: mem_write_action.splits)

lemma tso_writes_inv_sys_read_Mut[simp]:
  assumes "tso_writes_inv s"
  assumes "(ract, v) \<in> { (mr_fM, mv_Mark (Some (sys_fM s))), (mr_fA, mv_Mark (Some (sys_fA s))), (mr_Phase, mv_Phase (sys_phase s)) }"
  shows "sys_read (mutator m) ract (s sys) = v"
using assms
apply (clarsimp simp: sys_read_def fold_writes_def)
apply (rule fold_invariant[where P="\<lambda>fr. do_read_action ract (fr (s sys)) = v" and Q="mut_writes"])
  apply (fastforce simp: tso_writes_inv_def)
 apply (auto simp: do_read_action_def split: mem_write_action.splits)
done

lemma tso_writes_inv_sys_read_GC[simp]:
  assumes "tso_writes_inv s"
  shows "sys_read gc (mr_Ref r f) (s sys) = mv_Ref (sys_heap s r \<bind> (\<lambda>obj. obj_fields obj f))" (is "?lhs = mv_Ref ?rhs")
using assms
apply (simp add: sys_read_def fold_writes_def)
apply (rule fold_invariant[where P="\<lambda>fr. heap (fr (s sys)) r \<bind> (\<lambda>obj. obj_fields obj f) = ?rhs"
                             and Q="\<lambda>w. \<forall>r f r'. w \<noteq> mw_Mutate r f r'"])
  apply (force simp: tso_writes_inv_def)
 apply (auto simp: do_write_action_def Option.map_option_case
            split: mem_write_action.splits option.splits)
done

lemma tso_no_pending_marksD[simp]:
  assumes "tso_pending_mark p s = []"
  shows "sys_read p (mr_Mark r) (s sys) = mv_Mark (Option.map_option obj_mark (sys_heap s r))"
using assms
apply (clarsimp simp: sys_read_def fold_writes_def)
apply (rule fold_invariant[where P="\<lambda>fr. Option.map_option obj_mark (heap (fr (s sys)) r) = Option.map_option obj_mark (sys_heap s r)"
                             and Q="\<lambda>w. \<forall>fl. w \<noteq> mw_Mark r fl"])
  apply (auto simp: Option.map_option_case do_write_action_def filter_empty_conv
             split: mem_write_action.splits option.splits)
done

lemma no_pending_phase_sys_read[simp]:
  assumes "tso_pending_phase p s = []"
  shows "sys_read p mr_Phase (s sys) = mv_Phase (sys_phase s)"
using assms
apply (clarsimp simp: sys_read_def fold_writes_def)
apply (rule fold_invariant[where P="\<lambda>fr. phase (fr (s sys)) = sys_phase s" and Q="\<lambda>w. \<forall>ph. w \<noteq> mw_Phase ph"])
  apply (auto simp: do_write_action_def filter_empty_conv
             split: mem_write_action.splits)
done

lemma gc_no_pending_fM_write[simp]:
  assumes "tso_pending_fM gc s = []"
  shows "sys_read gc mr_fM (s sys) = mv_Mark (Some (sys_fM s))"
using assms
apply (clarsimp simp: sys_read_def fold_writes_def)
apply (rule fold_invariant[where P="\<lambda>fr. fM (fr (s sys)) = sys_fM s" and Q="\<lambda>w. \<forall>fl. w \<noteq> mw_fM fl"])
  apply (auto simp: do_write_action_def filter_empty_conv
             split: mem_write_action.splits)
done

lemma (in sys) tso_gc_writes_inv[intro]:
  "\<lbrace> LSTP tso_writes_inv \<rbrace> sys"
apply (vcg_jackhammer simp: tso_writes_inv_def)
apply (metis (no_types) list.set_intros(2))
done

lemma (in gc) tso_writes_inv[intro]:
  "\<lbrace> LSTP tso_writes_inv \<rbrace> gc"
by (vcg_jackhammer simp: tso_writes_inv_def)

lemma (in mut_m) tso_writes_inv[intro]:
  "\<lbrace> LSTP tso_writes_inv \<rbrace> mutator m"
by (vcg_jackhammer simp: tso_writes_inv_def)

(*>*)

subsubsection\<open>Locations where the TSO lock is held\<close>

text (in gc) \<open>

The GC holds the TSO lock only during the \texttt{CAS} in @{const
"mark_object"}.

\<close>

locset_definition gc_tso_lock_locs :: "location set" where
  "gc_tso_lock_locs \<equiv> \<Union>l\<in>{ ''mo_co_cmark'', ''mo_co_ctest'', ''mo_co_mark'', ''mo_co_unlock'' }. suffixed l"

inv_definition (in gc) tso_lock_invL :: "('field, 'mut, 'ref) gc_pred" where
  "tso_lock_invL \<equiv>
     atS_gc gc_tso_lock_locs (tso_locked_by gc)
   \<^bold>\<and> atS_gc (- gc_tso_lock_locs) (\<^bold>\<not> (tso_locked_by gc))"

(*<*)

lemma (in gc) tso_lock_invL[intro]:
  "\<lbrace> tso_lock_invL \<rbrace> gc"
by vcg_jackhammer

lemma (in sys) gc_tso_lock_invL[intro]:
  notes gc.tso_lock_invL_def[inv]
  shows "\<lbrace> gc.tso_lock_invL \<rbrace> sys"
by vcg_ni

lemma (in mut_m) gc_tso_lock_invL[intro]:
  notes gc.tso_lock_invL_def[inv]
  shows "\<lbrace> gc.tso_lock_invL \<rbrace> mutator m"
by vcg_ni

(*>*)
text (in mut_m) \<open>

A mutator holds the TSO lock only during the \texttt{CAS}s in @{const
"mark_object"}.

\<close>

locset_definition "mut_tso_lock_locs =
  (\<Union>l\<in>{ ''mo_co_cmark'', ''mo_co_ctest'', ''mo_co_mark'', ''mo_co_unlock'' }. suffixed l)"

inv_definition (in mut_m) tso_lock_invL :: "('field, 'mut, 'ref) gc_pred" where
  "tso_lock_invL =
    (atS_mut mut_tso_lock_locs     (tso_locked_by (mutator m))
   \<^bold>\<and> atS_mut (- mut_tso_lock_locs) (\<^bold>\<not>(tso_locked_by (mutator m))))"
(*<*)

lemma (in mut_m) tso_lock_invL[intro]:
  "\<lbrace> tso_lock_invL \<rbrace> mutator m"
by vcg_jackhammer

lemma (in gc) mut_tso_lock_invL[intro]:
  notes mut_m.tso_lock_invL_def[inv]
  shows "\<lbrace> mut_m.tso_lock_invL m \<rbrace> gc"
by vcg_ni

lemma (in sys) mut_tso_lock_invL[intro]:
  notes mut_m.tso_lock_invL_def[inv]
  shows "\<lbrace> mut_m.tso_lock_invL m \<rbrace> sys"
by vcg_ni

lemma (in mut_m') tso_lock_invL[intro]:
  "\<lbrace> tso_lock_invL \<rbrace> mutator m'"
by vcg_ni

(*>*)
(*<*)

end
(*>*)
