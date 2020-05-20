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

theory Concrete
imports
  Concrete_heap
begin

(*>*)
text\<open>\<close>

context gc_system
begin

abbreviation sys_init_state :: concrete_local_state where
  "sys_init_state \<equiv>
     undefined\<lparr> fA := initial_mark
              , fM := initial_mark
              , heap := sys_init_heap
              , handshake_pending := \<langle>False\<rangle>
              , handshake_type := ht_GetRoots
              , mem_lock := None
              , mem_write_buffers := \<langle>[]\<rangle>
              , phase := ph_Idle
              , W := {}
              , ghost_honorary_grey := {}
              , ghost_handshake_in_sync := \<langle>True\<rangle>
              , ghost_handshake_phase := hp_IdleMarkSweep \<rparr>"

abbreviation gc_init_state :: concrete_local_state where
  "gc_init_state \<equiv>
     undefined\<lparr> fM := initial_mark
              , fA := initial_mark
              , phase := ph_Idle
              , W := {}
              , ghost_honorary_grey := {} \<rparr>"

primrec lookup :: "('k \<times> 'v) list \<Rightarrow> 'v \<Rightarrow> 'k \<Rightarrow> 'v" where
  "lookup [] v0 k = v0"
| "lookup (kv # kvs) v0 k = (if fst kv = k then snd kv else lookup kvs v0 k)"

abbreviation muts_init_states :: "(mut \<times> concrete_local_state) list" where
  "muts_init_states \<equiv> [ (0, mut_init_state0), (1, mut_init_state1), (2, mut_init_state2) ]"

abbreviation init_state :: clsts where
  "init_state \<equiv> \<lambda>p. case p of
              gc \<Rightarrow> gc_init_state
            | sys \<Rightarrow> sys_init_state
            | mutator m \<Rightarrow> lookup muts_init_states mut_common_init_state m"

lemma
  "gc_system_init init_state"
(*<*)
apply (clarsimp simp: gc_system_init_def
                      gc_initial_state_def
                      mut_initial_state_def
                      sys_initial_state_def)
apply (auto simp: ran_def)
apply (auto simp: valid_refs_def)
apply (erule rtranclp.cases; auto simp: ran_def split: if_splits obj_at_splits)+
done
(*>*)
text\<open>\<close>

end
(*<*)

end
(*>*)
