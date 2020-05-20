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

theory Proofs_basis
imports
  Tactics
  "HOL-Library.Simps_Case_Conv"
begin

(*>*)
subsection\<open>Functions and predicates\<close>

text\<open>

We define a pile of predicates and accessor functions for the
process's local states. One might hope that a more sophisticated
approach would automate all of this (cf @{cite [cite_macro=citet]
"DBLP:journals/entcs/SchirmerW09"}).

\<close>

abbreviation "is_mw_Mark w \<equiv> \<exists>r fl. w = mw_Mark r fl"
abbreviation "is_mw_Mutate w \<equiv> \<exists>r f r'. w = mw_Mutate r f r'"
abbreviation "is_mw_fA w \<equiv> \<exists>fl. w = mw_fA fl"
abbreviation "is_mw_fM w \<equiv> \<exists>fl. w = mw_fM fl"
abbreviation "is_mw_Phase w \<equiv> \<exists>ph. w = mw_Phase ph"

abbreviation (input) pred_in_W :: "'ref \<Rightarrow> 'mut process_name \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" (infix "in'_W" 50) where
  "r in_W p \<equiv> \<lambda>s. r \<in> W (s p)"

abbreviation (input) pred_in_ghost_honorary_grey :: "'ref \<Rightarrow> 'mut process_name \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" (infix "in'_ghost'_honorary'_grey" 50) where
  "r in_ghost_honorary_grey p \<equiv> \<lambda>s. r \<in> ghost_honorary_grey (s p)"

context gc
begin

abbreviation
  valid_gc_syn :: "('field, 'mut, 'ref) gc_loc_comp \<Rightarrow> ('field, 'mut, 'ref) gc_pred \<Rightarrow> ('field, 'mut, 'ref) gc_com \<Rightarrow> ('field, 'mut, 'ref) gc_pred \<Rightarrow> bool"
                       ("_ \<Turnstile> \<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>")
where
  "afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<equiv> gc_pgms, gc, afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"

abbreviation valid_gc_inv_syn :: "('field, 'mut, 'ref) gc_loc_comp \<Rightarrow> ('field, 'mut, 'ref) gc_pred \<Rightarrow> ('field, 'mut, 'ref) gc_com \<Rightarrow> bool" ("_ \<Turnstile> \<lbrace>_\<rbrace>/ _") where
  "afts \<Turnstile> \<lbrace>P\<rbrace> c \<equiv> afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>P\<rbrace>"

end

abbreviation "gc_cas_mark s \<equiv> cas_mark (s gc)"
abbreviation "gc_fM s \<equiv> fM (s gc)"
abbreviation "gc_field s \<equiv> field (s gc)"
abbreviation "gc_field_set s \<equiv> field_set (s gc)"
abbreviation "gc_mark s \<equiv> mark (s gc)"
abbreviation "gc_mut s \<equiv> mut (s gc)"
abbreviation "gc_muts s \<equiv> muts (s gc)"
abbreviation "gc_phase s \<equiv> phase (s gc)"
abbreviation "gc_tmp_ref s \<equiv> tmp_ref (s gc)"
abbreviation "gc_ghost_honorary_grey s \<equiv> ghost_honorary_grey (s gc)"
abbreviation "gc_ref s \<equiv> ref (s gc)"
abbreviation "gc_refs s \<equiv> refs (s gc)"
abbreviation "gc_the_ref \<equiv> the \<circ> gc_ref"
abbreviation "gc_W s \<equiv> W (s gc)"

abbreviation at_gc :: "location \<Rightarrow> ('field, 'mut, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'ref) gc_pred" where
  "at_gc l P \<equiv> at gc l \<^bold>\<longrightarrow> LSTP P"

abbreviation atS_gc :: "location set \<Rightarrow> ('field, 'mut, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'ref) gc_pred" where
  "atS_gc ls P \<equiv> atS gc ls \<^bold>\<longrightarrow> LSTP P"

context mut_m
begin

abbreviation
  valid_mut_syn :: "('field, 'mut, 'ref) gc_loc_comp \<Rightarrow> ('field, 'mut, 'ref) gc_pred \<Rightarrow> ('field, 'mut, 'ref) gc_com \<Rightarrow> ('field, 'mut, 'ref) gc_pred \<Rightarrow> bool"
                    ("_ \<Turnstile> \<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>")
where
  "afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<equiv> gc_pgms, mutator m, afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"

abbreviation valid_mut_inv_syn :: "('field, 'mut, 'ref) gc_loc_comp \<Rightarrow> ('field, 'mut, 'ref) gc_pred \<Rightarrow> ('field, 'mut, 'ref) gc_com \<Rightarrow> bool" ("_ \<Turnstile> \<lbrace>_\<rbrace>/ _") where
  "afts \<Turnstile> \<lbrace>P\<rbrace> c \<equiv> afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>P\<rbrace>"

abbreviation at_mut :: "location \<Rightarrow> ('field, 'mut, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'ref) gc_pred" where
  "at_mut l P \<equiv> at (mutator m) l \<^bold>\<longrightarrow> LSTP P"

abbreviation atS_mut :: "location set \<Rightarrow> ('field, 'mut, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'ref) gc_pred" where
  "atS_mut ls P \<equiv> atS (mutator m) ls \<^bold>\<longrightarrow> LSTP P"

abbreviation "mut_cas_mark s \<equiv> cas_mark (s (mutator m))"
abbreviation "mut_field s \<equiv> field (s (mutator m))"
abbreviation "mut_fM s \<equiv> fM (s (mutator m))"
abbreviation "mut_ghost_honorary_grey s \<equiv> ghost_honorary_grey (s (mutator m))"
abbreviation "mut_ghost_handshake_phase s \<equiv> ghost_handshake_phase (s (mutator m))"
abbreviation "mut_ghost_honorary_root s \<equiv> ghost_honorary_root (s (mutator m))"
abbreviation "mut_mark s \<equiv> mark (s (mutator m))"
abbreviation "mut_new_ref s \<equiv> new_ref (s (mutator m))"
abbreviation "mut_phase s \<equiv> phase (s (mutator m))"
abbreviation "mut_ref s \<equiv> ref (s (mutator m))"
abbreviation "mut_tmp_ref s \<equiv> tmp_ref (s (mutator m))"
abbreviation "mut_the_new_ref \<equiv> the \<circ> mut_new_ref"
abbreviation "mut_the_ref \<equiv> the \<circ> mut_ref"
abbreviation "mut_refs s \<equiv> refs (s (mutator m))"
abbreviation "mut_roots s \<equiv> roots (s (mutator m))"
abbreviation "mut_W s \<equiv> W (s (mutator m))"

end

context sys
begin

abbreviation
  valid_sys_syn :: "('field, 'mut, 'ref) gc_loc_comp \<Rightarrow> ('field, 'mut, 'ref) gc_pred \<Rightarrow> ('field, 'mut, 'ref) gc_com \<Rightarrow> ('field, 'mut, 'ref) gc_pred \<Rightarrow> bool"
                    ("_ \<Turnstile> \<lbrace>_\<rbrace>/ _/ \<lbrace>_\<rbrace>")
where
  "afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace> \<equiv> gc_pgms, sys, afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>Q\<rbrace>"

abbreviation valid_sys_inv_syn :: "('field, 'mut, 'ref) gc_loc_comp \<Rightarrow> ('field, 'mut, 'ref) gc_pred \<Rightarrow> ('field, 'mut, 'ref) gc_com \<Rightarrow> bool" ("_ \<Turnstile> \<lbrace>_\<rbrace>/ _") where
  "afts \<Turnstile> \<lbrace>P\<rbrace> c \<equiv> afts \<Turnstile> \<lbrace>P\<rbrace> c \<lbrace>P\<rbrace>"

end

abbreviation sys_heap :: "('field, 'mut, 'ref) lsts \<Rightarrow> 'ref \<Rightarrow> ('field, 'ref) object option" where "sys_heap s \<equiv> heap (s sys)"

abbreviation "sys_fA s \<equiv> fA (s sys)"
abbreviation "sys_fM s \<equiv> fM (s sys)"
abbreviation "sys_ghost_honorary_grey s \<equiv> ghost_honorary_grey (s sys)"
abbreviation "sys_ghost_handshake_in_sync m s \<equiv> ghost_handshake_in_sync (s sys) m"
abbreviation "sys_ghost_handshake_phase s \<equiv> ghost_handshake_phase (s sys)"
abbreviation "sys_handshake_pending m s \<equiv> handshake_pending (s sys) m"
abbreviation "sys_handshake_type s \<equiv> handshake_type (s sys)"
abbreviation "sys_mem_write_buffers p s \<equiv> mem_write_buffers (s sys) p"
abbreviation "sys_mem_lock s \<equiv> mem_lock (s sys)"
abbreviation "sys_phase s \<equiv> phase (s sys)"
abbreviation "sys_W s \<equiv> W (s sys)"

abbreviation atS_sys :: "location set \<Rightarrow> ('field, 'mut, 'ref) lsts_pred \<Rightarrow> ('field, 'mut, 'ref) gc_pred" where
  "atS_sys ls P \<equiv> atS sys ls \<^bold>\<longrightarrow> LSTP P"

text\<open>Projections on TSO buffers.\<close>

abbreviation (input) "tso_unlocked s \<equiv> mem_lock (s sys) = None"
abbreviation (input) "tso_locked_by p s \<equiv> mem_lock (s sys) = Some p"

abbreviation (input) "tso_pending p P s \<equiv> filter P (mem_write_buffers (s sys) p)"
abbreviation (input) "tso_pending_write p w s \<equiv> w \<in> set (mem_write_buffers (s sys) p)"

abbreviation (input) "tso_pending_fA p \<equiv> tso_pending p is_mw_fA"
abbreviation (input) "tso_pending_fM p \<equiv> tso_pending p is_mw_fM"
abbreviation (input) "tso_pending_mark p \<equiv> tso_pending p is_mw_Mark"
abbreviation (input) "tso_pending_mutate p \<equiv> tso_pending p is_mw_Mutate"
abbreviation (input) "tso_pending_phase p \<equiv> tso_pending p is_mw_Phase"

abbreviation (input) "tso_no_pending_marks \<equiv> \<^bold>\<forall>p. LIST_NULL (tso_pending_mark p)"

text\<open>

A somewhat-useful abstraction of the heap, following l4.verified,
which asserts that there is an object at the given reference with the
given property.

\<close>

definition obj_at :: "(('field, 'ref) object \<Rightarrow> bool) \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "obj_at P r \<equiv> \<lambda>s. case sys_heap s r of None \<Rightarrow> False | Some obj \<Rightarrow> P obj"

abbreviation (input) valid_ref :: "'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "valid_ref r \<equiv> obj_at \<langle>True\<rangle> r"

definition valid_null_ref :: "'ref option \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "valid_null_ref r \<equiv> case r of None \<Rightarrow> \<langle>True\<rangle> | Some r' \<Rightarrow> valid_ref r'"

abbreviation pred_points_to :: "'ref \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" (infix "points'_to" 51) where
  "x points_to y \<equiv> \<lambda>s. obj_at (\<lambda>obj. y \<in> ran (obj_fields obj)) x s"

text\<open>

We use Isabelle's standard transitive-reflexive closure to define
reachability through the heap.

\<close>

abbreviation pred_reaches :: "'ref \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" (infix "reaches" 51) where
  "x reaches y \<equiv> \<lambda>s. (\<lambda>x y. (x points_to y) s)\<^sup>*\<^sup>* x y"

text\<open>

The predicate \<open>obj_at_field_on_heap\<close> asserts that @{term \<open>valid_ref r\<close>}
and if \<open>f\<close> is a field of the object referred to by \<open>r\<close> then it it satisfies \<open>P\<close>.

\<close>

(* FIXME rename *)
definition obj_at_field_on_heap :: "('ref \<Rightarrow> bool) \<Rightarrow> 'ref \<Rightarrow> 'field \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "obj_at_field_on_heap P r f \<equiv> \<lambda>s.
     case Option.map_option obj_fields (sys_heap s r) of
         None \<Rightarrow> False
       | Some fs \<Rightarrow> (case fs f of None \<Rightarrow> True
                               | Some r' \<Rightarrow> P r')"


subsection\<open> Garbage collector locations \<close>

locset_definition "idle_locs = prefixed ''idle''"
locset_definition "init_locs = prefixed ''init''"
locset_definition "mark_locs = prefixed ''mark''"
locset_definition "mark_loop_locs = prefixed ''mark_loop''"
locset_definition "sweep_locs = prefixed ''sweep''"

(*<*)

subsection\<open> Lemma bucket \<close>

lemma obj_at_split:
  "Q (obj_at P r s) = ((sys_heap s r = None \<longrightarrow> Q False) \<and> (\<forall>obj. sys_heap s r = Some obj \<longrightarrow> Q (P obj)))"
by (simp add: obj_at_def split: option.splits)

lemma obj_at_split_asm:
  "Q (obj_at P r s) = (\<not> ((sys_heap s r = None \<and> \<not>Q False) \<or> (\<exists>obj. sys_heap s r = Some obj \<and> \<not> Q (P obj))))"
by (simp add: obj_at_def split: option.splits)

lemmas obj_at_splits = obj_at_split obj_at_split_asm

lemma p_not_sys:
  "p \<noteq> sys \<longleftrightarrow> p = gc \<or> (\<exists>m. p = mutator m)"
by (cases p) simp_all

lemma (in mut_m') m'm[iff]: "m' \<noteq> m"
using mm' by blast

lemma obj_at_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. map_option P (sys_heap s r))
          (obj_at P r)"
by (simp add: eq_imp_def obj_at_def split: option.splits)

lemmas obj_at_fun_upd[simp] = eq_imp_fun_upd[OF obj_at_eq_imp, simplified eq_imp_simps]

simps_of_case handshake_step_simps[simp]: handshake_step_def (splits: handshake_phase.split)

(* Looks like a good idea but seems very weak. The split rules do a better job. *)
lemma obj_at_weakenE[elim]:
  "\<lbrakk> obj_at P r s; \<And>s. P s \<Longrightarrow> P' s \<rbrakk> \<Longrightarrow> obj_at P' r s"
by (simp add: obj_at_def split: option.splits)

lemma obj_at_ref_sweep_loop_free[simp]:
  "obj_at P r (s(sys := (s sys)\<lparr>heap := (sys_heap s)(r' := None)\<rparr>)) \<longleftrightarrow> obj_at P r s \<and> r \<noteq> r'"
by (clarsimp split: obj_at_splits)

lemma obj_at_alloc[simp]:
  "sys_heap s r' = None
  \<Longrightarrow> obj_at P r (s(Mut m := mut_m_s', sys := (s sys)\<lparr> heap := sys_heap s(r' \<mapsto> obj) \<rparr>))
  \<longleftrightarrow> (obj_at P r s \<or> (r = r' \<and> P obj))"
by (simp add: ran_def split: obj_at_splits)

simps_of_case do_read_action_simps[simp]: fun_cong[OF do_read_action_def[simplified atomize_eq]] (splits: mem_read_action.split)
simps_of_case do_write_action_simps[simp]: fun_cong[OF do_write_action_def[simplified atomize_eq]] (splits: mem_write_action.split)

(* This gives some indication of how much we're cheating on the TSO front. *)
lemma do_write_action_prj_simps[simp]:
  "fM (do_write_action w s) = fl \<longleftrightarrow> (fM s = fl \<and> w \<noteq> mw_fM (\<not>fM s)) \<or> w = mw_fM fl"
  "fl = fM (do_write_action w s) \<longleftrightarrow> (fl = fM s \<and> w \<noteq> mw_fM (\<not>fM s)) \<or> w = mw_fM fl"
  "fA (do_write_action w s) = fl \<longleftrightarrow> (fA s = fl \<and> w \<noteq> mw_fA (\<not>fA s)) \<or> w = mw_fA fl"
  "fl = fA (do_write_action w s) \<longleftrightarrow> (fl = fA s \<and> w \<noteq> mw_fA (\<not>fA s)) \<or> w = mw_fA fl"
  "ghost_handshake_in_sync (do_write_action w s) = ghost_handshake_in_sync s"
  "ghost_handshake_phase (do_write_action w s) = ghost_handshake_phase s"
  "ghost_honorary_grey (do_write_action w s) = ghost_honorary_grey s"
  "handshake_pending (do_write_action w s) = handshake_pending s"
  "handshake_type (do_write_action w s) = handshake_type s"
  "heap (do_write_action w s) r = None \<longleftrightarrow> heap s r = None"
  "mem_lock (do_write_action w s) = mem_lock s"
  "phase (do_write_action w s) = ph \<longleftrightarrow> (phase s = ph \<and> (\<forall>ph'. w \<noteq> mw_Phase ph') \<or> w = mw_Phase ph)"
  "ph = phase (do_write_action w s) \<longleftrightarrow> (ph = phase s \<and> (\<forall>ph'. w \<noteq> mw_Phase ph') \<or> w = mw_Phase ph)"
  "W (do_write_action w s) = W s"
by (auto simp: do_write_action_def split: mem_write_action.splits obj_at_splits)

lemma valid_null_ref_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. r \<bind> (Option.map_option \<langle>True\<rangle> \<circ> sys_heap s))
          (valid_null_ref r)"
by (simp add: eq_imp_def obj_at_def valid_null_ref_def split: option.splits)

lemmas valid_null_ref_fun_upd[simp] = eq_imp_fun_upd[OF valid_null_ref_eq_imp, simplified]

lemma valid_null_ref_simps[simp]:
  "valid_null_ref None s"
  "valid_null_ref (Some r) s \<longleftrightarrow> valid_ref r s"
by (simp_all add: valid_null_ref_def)

lemma obj_at_field_on_heap_eq_imp:
  "eq_imp (\<lambda>(_::unit) s. sys_heap s r)
          (obj_at_field_on_heap P r f)"
by (simp add: eq_imp_def obj_at_field_on_heap_def)

lemmas obj_at_field_on_heap_fun_upd[simp] = eq_imp_fun_upd[OF obj_at_field_on_heap_eq_imp, simplified eq_imp_simps]

lemma obj_at_field_on_heapE[elim]:
  "\<lbrakk> obj_at_field_on_heap P r f s; sys_heap s' r = sys_heap s r; \<And>r'. P r' \<Longrightarrow> P' r' \<rbrakk>
       \<Longrightarrow> obj_at_field_on_heap P' r f s'"
by (simp add: obj_at_field_on_heap_def split: option.splits)

lemma obj_at_field_on_heap_mw_simps[simp]:
  "obj_at_field_on_heap P r0 f0
         (s(sys := (s sys)\<lparr> heap := (sys_heap s)(r := Option.map_option (\<lambda>obj :: ('field, 'ref) object. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                            mem_write_buffers := (mem_write_buffers (s Sys))(p := ws) \<rparr>))
\<longleftrightarrow> ( (r \<noteq> r0 \<or> f \<noteq> f0) \<and> obj_at_field_on_heap P r0 f0 s )
   \<or> (r = r0 \<and> f = f0 \<and> valid_ref r s \<and> (case opt_r' of Some r'' \<Rightarrow> P r'' | _ \<Rightarrow> True))"
  "obj_at_field_on_heap P r f (s(sys := s sys\<lparr>heap := (sys_heap s)(r' := Option.map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r')), mem_write_buffers := sb'\<rparr>))
\<longleftrightarrow> obj_at_field_on_heap P r f s"
by (auto simp: obj_at_field_on_heap_def split: option.splits obj_at_splits)

lemma obj_at_field_on_heap_no_pending_writes:
  "\<lbrakk> sys_read (mutator m) (mr_Ref r f) (s sys) = mv_Ref opt_r'; \<forall>opt_r'. mw_Mutate r f opt_r' \<notin> set (sys_mem_write_buffers (mutator m) s); valid_ref r s \<rbrakk>
     \<Longrightarrow> obj_at_field_on_heap (\<lambda>r. opt_r' = Some r) r f s"
apply (clarsimp simp: sys_read_def fold_writes_def)
apply (rule fold_invariant[where P="\<lambda>fr. obj_at_field_on_heap (\<lambda>r'. heap (fr (s sys)) r \<bind> (\<lambda>obj. obj_fields obj f) = Some r') r f s"
                             and Q="\<lambda>w. w \<in> set (sys_mem_write_buffers (mutator m) s)"])
  apply auto[1]
 apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits obj_at_splits)
apply (auto simp: obj_at_field_on_heap_def do_write_action_def Option.map_option_case
           split: option.splits obj_at_splits mem_write_action.splits)
done

lemma obj_at_field_on_heap_imp_valid_ref[elim]:
  "obj_at_field_on_heap P r f s \<Longrightarrow> valid_ref r s"
  "obj_at_field_on_heap P r f s \<Longrightarrow> valid_null_ref (Some r) s"
by (auto simp: obj_at_field_on_heap_def valid_null_ref_def split: obj_at_splits option.splits)

lemma obj_at_field_on_heap_weakenE[elim]:
  "\<lbrakk> obj_at_field_on_heap P r f s; \<And>s. P s \<Longrightarrow> P' s\<rbrakk> \<Longrightarrow> obj_at_field_on_heap P' r f s"
by (clarsimp simp: obj_at_field_on_heap_def split: option.splits)

lemma Set_bind_insert[simp]:
  "insert a A \<bind> B = B a \<union> (A \<bind> B)"
by (auto simp: Set.bind_def)

lemma option_bind_invE[elim]:
  "\<lbrakk> f \<bind> g = None; \<And>a. \<lbrakk> f = Some a; g a = None \<rbrakk> \<Longrightarrow> Q; f = None \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
  "\<lbrakk> f \<bind> g = Some x; \<And>a. \<lbrakk> f = Some a; g a = Some x \<rbrakk> \<Longrightarrow> Q \<rbrakk> \<Longrightarrow> Q"
by (case_tac [!] f) simp_all

(*>*)
(*<*)

end
(*>*)
