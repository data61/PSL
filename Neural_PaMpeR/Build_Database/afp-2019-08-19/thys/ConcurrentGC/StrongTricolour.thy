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

theory StrongTricolour
imports
  MarkObject
begin

(*>*)
subsection\<open>The strong-tricolour invariant \label{sec:strong-tricolour-invariant} \<close>

text\<open>

As the GC algorithm uses both insertion and deletion barriers, it
preserves the \emph{strong tricolour-invariant}:

\<close>

abbreviation points_to_white :: "'ref \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" (infix "points'_to'_white" 51) where
  "x points_to_white y \<equiv> x points_to y \<^bold>\<and> white y"

definition strong_tricolour_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "strong_tricolour_inv = (\<^bold>\<forall>b w. black b \<^bold>\<longrightarrow> \<^bold>\<not>(b points_to_white w))"

text\<open>

Intuitively this invariant says that there are no pointers from
completely processed objects to the unexplored space; i.e., the grey
references properly separate the two. In contrast the weak tricolour
invariant allows such pointers, provided there is a grey reference
that protects the unexplored object.

\<close>

definition has_white_path_to :: "'ref \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" (infix "has'_white'_path'_to" 51) where
  "x has_white_path_to y \<equiv> \<lambda>s. (\<lambda>x y. (x points_to_white y) s)\<^sup>*\<^sup>* x y"

definition grey_protects_white :: "'ref \<Rightarrow> 'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" (infix "grey'_protects'_white" 51) where
  "g grey_protects_white w = (grey g \<^bold>\<and> g has_white_path_to w)"

definition weak_tricolour_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "weak_tricolour_inv =
     (\<^bold>\<forall>b w. black b \<^bold>\<and> b points_to_white w \<^bold>\<longrightarrow> (\<^bold>\<exists>g. g grey_protects_white w))"

lemma "strong_tricolour_inv s \<Longrightarrow> weak_tricolour_inv s"
(*<*)
by (clarsimp simp: strong_tricolour_inv_def weak_tricolour_inv_def grey_protects_white_def)

(*>*)
text\<open>

The key invariant that the mutators establish as they perform \<open>get_roots\<close>: they protect their white-reachable references with grey
objects.

\<close>

definition in_snapshot :: "'ref \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "in_snapshot r = (black r \<^bold>\<or> (\<^bold>\<exists>g. g grey_protects_white r))"

definition (in mut_m) reachable_snapshot_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "reachable_snapshot_inv = (\<^bold>\<forall>r. reachable r \<^bold>\<longrightarrow> in_snapshot r)"

text\<open>

Note that it is not easy to specify precisely when the snapshot (of
objects the GC will retain) is taken due to the raggedness of the
initialisation.

In some phases we need to know that the insertion and deletion
barriers are installed, in order to preserve the snapshot. These can
ignore TSO effects as marks hit system memory in a timely way.

\<close>

abbreviation marked_insertion :: "('field, 'ref) mem_write_action \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "marked_insertion w \<equiv> \<lambda>s. case w of mw_Mutate r f (Some r') \<Rightarrow> marked r' s | _ \<Rightarrow> True"

definition (in mut_m) marked_insertions :: "('field, 'mut, 'ref) lsts_pred" where
  "marked_insertions = (\<^bold>\<forall>w. tso_pending_write (mutator m) w \<^bold>\<longrightarrow> marked_insertion w)"

abbreviation marked_deletion :: "('field, 'ref) mem_write_action \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "marked_deletion w \<equiv> \<lambda>s. case w of mw_Mutate r f opt_r' \<Rightarrow> obj_at_field_on_heap (\<lambda>r'. marked r' s) r f s | _ \<Rightarrow> True"

definition (in mut_m) marked_deletions :: "('field, 'mut, 'ref) lsts_pred" where
  "marked_deletions = (\<^bold>\<forall>w. tso_pending_write (mutator m) w \<^bold>\<longrightarrow> marked_deletion w)"

text\<open>

Finally, in some phases the heap is somewhat monochrome.

\<close>

definition black_heap :: "('field, 'mut, 'ref) lsts_pred" where
  "black_heap = (\<^bold>\<forall>r. valid_ref r \<^bold>\<longrightarrow> black r)"

definition white_heap :: "('field, 'mut, 'ref) lsts_pred" where
  "white_heap = (\<^bold>\<forall>r. valid_ref r \<^bold>\<longrightarrow> white r)"

definition no_black_refs :: "('field, 'mut, 'ref) lsts_pred" where
  "no_black_refs = (\<^bold>\<forall>r. \<^bold>\<not>(black r))"

definition no_grey_refs :: "('field, 'mut, 'ref) lsts_pred" where
  "no_grey_refs = (\<^bold>\<forall>r. \<^bold>\<not>(grey r))"
(*<*)

lemma no_black_refsD:
  "no_black_refs s \<Longrightarrow> \<not>black r s"
unfolding no_black_refs_def by simp

lemma has_white_path_to_eq_imp:
  "eq_imp (\<lambda>(_::unit). sys_fM \<^bold>\<otimes> sys_heap)
          (x has_white_path_to y)"
by (clarsimp simp: eq_imp_def has_white_path_to_def obj_at_def cong: option.case_cong)

lemmas has_white_path_to_fun_upd[simp] = eq_imp_fun_upd[OF has_white_path_to_eq_imp, simplified eq_imp_simps, rule_format]

lemma has_white_path_toD[dest]:
  "(x has_white_path_to y) s \<Longrightarrow> white y s \<or> x = y"
unfolding has_white_path_to_def by (fastforce elim: rtranclp.cases)

lemma has_white_path_toI[iff]:
  "(x has_white_path_to x) s"
by (simp add: has_white_path_to_def)

lemma has_white_path_toE[elim!]:
  "\<lbrakk> (x points_to y) s; white y s \<rbrakk> \<Longrightarrow> (x has_white_path_to y) s"
  "\<lbrakk> (x has_white_path_to y) s; (y points_to z) s; white z s \<rbrakk> \<Longrightarrow> (x has_white_path_to z) s"
by (auto simp: has_white_path_to_def
         elim: rtranclp.intros(2))

lemma has_white_path_to_reaches[elim]:
  "(x has_white_path_to y) s \<Longrightarrow> (x reaches y) s"
unfolding has_white_path_to_def
by (induct rule: rtranclp.induct)
   (auto intro: rtranclp.intros(2))

lemma has_white_path_to_blacken[simp]:
  "(x has_white_path_to w) (s(gc := s gc\<lparr> W := gc_W s - rs \<rparr>)) \<longleftrightarrow> (x has_white_path_to w) s"
by (simp add: has_white_path_to_def)

text\<open>WL\<close>

lemma WL_mo_co_mark[simp]:
  "ghost_honorary_grey (s p) = {}
     \<Longrightarrow> WL p' (s(p := s p\<lparr> ghost_honorary_grey := rs \<rparr>)) = WL p' s \<union> { r |r. p' = p \<and> r \<in> rs}"
by (auto simp: WL_def)

lemma WL_blacken[simp]:
  "gc_ghost_honorary_grey s = {}
    \<Longrightarrow> WL p (s(gc := s gc\<lparr> W := gc_W s - rs \<rparr>)) = WL p s - { r |r. p = gc \<and> r \<in> rs }"
by (auto simp: WL_def)

lemma WL_hs_done[simp]:
  "ghost_honorary_grey (s (mutator m)) = {}
     \<Longrightarrow> WL p (s(mutator m := s (mutator m)\<lparr> W := {}, ghost_handshake_phase := hp' \<rparr>,
                 sys   := s sys\<lparr> handshake_pending := hsp', W := sys_W s \<union> W (s (mutator m)),
                                 ghost_handshake_in_sync := in' \<rparr>))
      = (case p of gc \<Rightarrow> WL gc s | mutator m' \<Rightarrow> (if m' = m then {} else WL (mutator m') s) | sys \<Rightarrow> WL sys s \<union> WL (mutator m) s)"
  "ghost_honorary_grey (s (mutator m)) = {}
     \<Longrightarrow> WL p (s(mutator m := s (mutator m)\<lparr> W := {} \<rparr>,
                 sys   := s sys\<lparr> handshake_pending := hsp', W := sys_W s \<union> W (s (mutator m)),
                                 ghost_handshake_in_sync := in' \<rparr>))
      = (case p of gc \<Rightarrow> WL gc s | mutator m' \<Rightarrow> (if m' = m then {} else WL (mutator m') s) | sys \<Rightarrow> WL sys s \<union> WL (mutator m) s)"
by (auto simp: WL_def split: process_name.splits)

lemma colours_load_W[iff]:
  "gc_W s = {} \<Longrightarrow> black r (s(gc := (s gc)\<lparr>W := W (s sys)\<rparr>, sys := (s sys)\<lparr>W := {}\<rparr>)) \<longleftrightarrow> black r s"
  "gc_W s = {} \<Longrightarrow> grey r (s(gc := (s gc)\<lparr>W := W (s sys)\<rparr>, sys := (s sys)\<lparr>W := {}\<rparr>)) \<longleftrightarrow> grey r s"
apply (simp_all add: black_def grey_def WL_def)
apply safe
apply (case_tac [!] x)
apply blast+
done

lemma colours_sweep_loop_free[iff]:
  "black r (s(sys := s sys\<lparr>heap := (heap (s sys))(r' := None)\<rparr>)) \<longleftrightarrow> (black r s \<and> r \<noteq> r')"
  "grey r (s(sys := s sys\<lparr>heap := (heap (s sys))(r' := None)\<rparr>)) \<longleftrightarrow> (grey r s)"
  "white r (s(sys := s sys\<lparr>heap := (heap (s sys))(r' := None)\<rparr>)) \<longleftrightarrow> (white r s \<and> r \<noteq> r')"
by (auto simp: black_def grey_def split: obj_at_splits)

lemma colours_get_work_done[simp]:
  "black r (s(mutator m := (s (mutator m))\<lparr>W := {}\<rparr>,
              sys := (s sys)\<lparr> handshake_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_handshake_in_sync := his' \<rparr>)) \<longleftrightarrow> black r s"
  "grey r (s(mutator m := (s (mutator m))\<lparr>W := {}\<rparr>,
              sys := (s sys)\<lparr> handshake_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_handshake_in_sync := his' \<rparr>)) \<longleftrightarrow> grey r s"
  "white r (s(mutator m := (s (mutator m))\<lparr>W := {}\<rparr>,
              sys := (s sys)\<lparr> handshake_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_handshake_in_sync := his' \<rparr>)) \<longleftrightarrow> white r s"
apply (simp_all add: black_def grey_def WL_def split: obj_at_splits)
apply auto
apply (metis (full_types) process_name.distinct(3))
by metis

lemma colours_get_roots_done[simp]:
  "black r (s(mutator m := (s (mutator m))\<lparr> W := {}, ghost_handshake_phase := hs' \<rparr>,
              sys := (s sys)\<lparr> handshake_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_handshake_in_sync := his' \<rparr>)) \<longleftrightarrow> black r s"
  "grey r (s(mutator m := (s (mutator m))\<lparr> W := {}, ghost_handshake_phase := hs' \<rparr>,
              sys := (s sys)\<lparr> handshake_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_handshake_in_sync := his' \<rparr>)) \<longleftrightarrow> grey r s"
  "white r (s(mutator m := (s (mutator m))\<lparr> W := {}, ghost_handshake_phase := hs' \<rparr>,
              sys := (s sys)\<lparr> handshake_pending := hp', W := W (s sys) \<union> W (s (mutator m)),
                              ghost_handshake_in_sync := his' \<rparr>)) \<longleftrightarrow> white r s"
apply (simp_all add: black_def grey_def WL_def split: obj_at_splits)
apply auto
apply (metis process_name.distinct(3))
by metis

lemma colours_mark[simp]:
  "\<lbrakk> ghost_honorary_grey (s p) = {} \<rbrakk> \<Longrightarrow> black b (s(p := s p\<lparr>ghost_honorary_grey := {r}\<rparr>)) \<longleftrightarrow> black b s \<and> b \<noteq> r"
  "\<lbrakk> ghost_honorary_grey (s p) = {} \<rbrakk> \<Longrightarrow> grey g (s(p := (s p)\<lparr>ghost_honorary_grey := {r}\<rparr>)) \<longleftrightarrow> grey g s \<or> g = r"
  "\<lbrakk> ghost_honorary_grey (s p) = {} \<rbrakk> \<Longrightarrow> white w (s(p := s p\<lparr>ghost_honorary_grey := {r}\<rparr>))  \<longleftrightarrow> white w s"
by (auto simp: black_def grey_def)

lemma colours_flip_fM[simp]:
  "fl \<noteq> sys_fM s \<Longrightarrow> black b (s(sys := (s sys)\<lparr>fM := fl, mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>)) \<longleftrightarrow> white b s \<and> \<not>grey b s"
by (simp_all add: black_def)

lemma colours_alloc[simp]:
  "heap (s sys) r' = None
     \<Longrightarrow> black r (s(mutator m := (s (mutator m))\<lparr> roots := roots' \<rparr>, sys := (s sys)\<lparr>heap := heap (s sys)(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> black r s \<or> (r' = r \<and> fl = sys_fM s \<and> \<not>grey r' s)"
  "grey r (s(mutator m := (s (mutator m))\<lparr> roots := roots' \<rparr>, sys := (s sys)\<lparr>heap := heap (s sys)(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> grey r s"
  "heap (s sys) r' = None
     \<Longrightarrow> white r (s(mutator m := (s (mutator m))\<lparr> roots := roots' \<rparr>, sys := (s sys)\<lparr>heap := heap (s sys)(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> white r s \<or> (r' = r \<and> fl \<noteq> sys_fM s)"
by (auto simp: black_def split: obj_at_splits dest!: valid_refs_invD)

lemma colours_blacken[simp]:
  "valid_W_inv s \<Longrightarrow> black b (s(gc := s gc\<lparr>W := gc_W s - {r}\<rparr>)) \<longleftrightarrow> black b s \<or> (r \<in> gc_W s \<and> b = r)"
  "\<lbrakk> r \<in> gc_W s; valid_W_inv s \<rbrakk> \<Longrightarrow> grey g (s(gc := s gc\<lparr>W := gc_W s - {r}\<rparr>)) \<longleftrightarrow> (grey g s \<and> g \<noteq> r)"
  "white w (s(gc := s gc\<lparr>W := gc_W s - {r}\<rparr>)) \<longleftrightarrow> white w s"
apply (auto simp: black_def grey_def WL_def split: obj_at_splits)
apply metis+
done

lemma colours_dequeue[simp]:
  "black b (s(sys := (s sys)\<lparr> heap := (sys_heap s)(r := Option.map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_write_buffers := (mem_write_buffers (s sys))(p := ws) \<rparr>))
\<longleftrightarrow> (black b s \<and> b \<noteq> r) \<or> (b = r \<and> fl = sys_fM s \<and> valid_ref r s \<and> \<not>grey r s)"
by (auto simp: black_def split: obj_at_splits)

lemma W_load_W[simp]:
  "gc_W s = {} \<Longrightarrow> (\<Union>p. W (if p = sys then (s sys)\<lparr>W := {}\<rparr> else if p = gc then (s gc)\<lparr>W := sys_W s\<rparr> else s p)) = (\<Union>p. W (s p))"
apply (rule equalityI)
 apply (fastforce split: if_splits)
apply clarsimp
apply (rename_tac x p)
apply (case_tac p)
apply force+
done

lemma WL_load_W[simp]:
  "gc_W s = {}
    \<Longrightarrow> (WL p (s(gc := (s gc)\<lparr>W := sys_W s\<rparr>, sys := (s sys)\<lparr>W := {}\<rparr>)))
     = (case p of gc \<Rightarrow> WL gc s \<union> sys_W s | mutator m \<Rightarrow> WL (mutator m) s | sys \<Rightarrow> sys_ghost_honorary_grey s)"
by (auto simp: WL_def split: process_name.splits)

lemma colours_mo_co_W[simp]:
  "ghost_honorary_grey (s p') = {r}
     \<Longrightarrow> (WL p (s(p' := (s p')\<lparr>W := insert r (W (s p')), ghost_honorary_grey := {}\<rparr>))) = (WL p s)"
  "ghost_honorary_grey (s p') = {r}
     \<Longrightarrow> grey g (s(p' := (s p')\<lparr>W := insert r (W (s p')), ghost_honorary_grey := {}\<rparr>)) \<longleftrightarrow> grey g s"
by (force simp: grey_def WL_def split: process_name.splits if_splits)+

lemma no_grey_refs_eq_imp:
  "eq_imp (\<lambda>(_::unit). (\<lambda>s. \<Union>p. WL p s))
          no_grey_refs"
by (auto simp add: eq_imp_def grey_def no_grey_refs_def set_eq_iff)

lemmas no_grey_refs_fun_upd[simp] = eq_imp_fun_upd[OF no_grey_refs_eq_imp, simplified eq_imp_simps, rule_format]

lemma no_grey_refs_no_pending_marks:
  "\<lbrakk> no_grey_refs s; valid_W_inv s \<rbrakk> \<Longrightarrow> tso_no_pending_marks s"
by (auto intro!: filter_False simp: no_grey_refs_def)

lemma (in mut_m) reachable_blackD:
  "\<lbrakk> no_grey_refs s; reachable_snapshot_inv s; reachable r s \<rbrakk> \<Longrightarrow> black r s"
by (simp add: no_grey_refs_def reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)

lemma (in mut_m) no_grey_refs_not_reachable:
  "\<lbrakk> no_grey_refs s; reachable_snapshot_inv s; white r s \<rbrakk> \<Longrightarrow> \<not>reachable r s"
by (fastforce simp: no_grey_refs_def reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def
             split: obj_at_splits)

lemma (in mut_m) no_grey_refs_not_rootD:
  "\<lbrakk> no_grey_refs s; reachable_snapshot_inv s; white r s \<rbrakk>
     \<Longrightarrow> r \<notin> mut_roots s \<and> r \<notin> mut_ghost_honorary_root s \<and> r \<notin> tso_write_refs s"
apply (drule (2) no_grey_refs_not_reachable)
apply (force simp: reachable_def)
done

lemma no_grey_refs_not_grey_reachableD:
  "no_grey_refs s \<Longrightarrow> \<not>grey_reachable x s"
by (clarsimp simp: no_grey_refs_def grey_reachable_def)

lemma (in mut_m) reachable_snapshot_inv_white_root:
  "\<lbrakk> white w s; w \<in> mut_roots s \<or> w \<in> mut_ghost_honorary_root s; reachable_snapshot_inv s \<rbrakk> \<Longrightarrow> \<exists>g. (g grey_protects_white w) s"
by (auto simp: reachable_snapshot_inv_def in_snapshot_def
               reachable_def grey_protects_white_def)

lemma no_grey_refsD:
  "no_grey_refs s \<Longrightarrow> r \<notin> W (s p)"
  "no_grey_refs s \<Longrightarrow> r \<notin> WL p s"
  "no_grey_refs s \<Longrightarrow> r \<notin> ghost_honorary_grey (s p)"
by (auto simp: no_grey_refs_def)

lemma no_grey_refs_marked[dest]:
  "\<lbrakk> marked r s; no_grey_refs s \<rbrakk> \<Longrightarrow> black r s"
by (auto simp: no_grey_refs_def black_def)

lemma no_grey_refs_bwD[dest]:
  "\<lbrakk> heap (s sys) r = Some obj; no_grey_refs s \<rbrakk> \<Longrightarrow> black r s \<or> white r s"
by (clarsimp simp: black_def grey_def no_grey_refs_def split: obj_at_splits)

text\<open>tso write refs\<close>

lemma tso_write_refs_simps[simp]:
  "mut_m.tso_write_refs m (s(mutator m' := s (mutator m')\<lparr>roots := roots'\<rparr>))
 = mut_m.tso_write_refs m s"
  "mut_m.tso_write_refs m (s(mutator m' := s (mutator m')\<lparr>ghost_honorary_root := {}\<rparr>,
                             sys := s sys\<lparr>mem_write_buffers := (mem_write_buffers (s sys))(mutator m' := sys_mem_write_buffers (mutator m') s @ [mw_Mutate r f opt_r'])\<rparr>))
 = mut_m.tso_write_refs m s \<union> (if m' = m then write_refs (mw_Mutate r f opt_r') else {})"
  "mut_m.tso_write_refs m (s(sys := s sys\<lparr>heap := (sys_heap s)(r' := None)\<rparr>))
 = mut_m.tso_write_refs m s"
  "mut_m.tso_write_refs m (s(mutator m' := s (mutator m')\<lparr>roots := insert r (roots (s (mutator m')))\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r \<mapsto> obj)\<rparr>))
 = mut_m.tso_write_refs m s"
  "mut_m.tso_write_refs m (s(mutator m' := s (mutator m')\<lparr>ghost_honorary_root := Option.set_option opt_r', ref := opt_r'\<rparr>))
 = mut_m.tso_write_refs m s"
  "mut_m.tso_write_refs m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                          mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))
 = (if p = mutator m then \<Union>w \<in> set ws. write_refs w else mut_m.tso_write_refs m s)"
  "sys_mem_write_buffers p s = mw_Mark r fl # ws
\<Longrightarrow> mut_m.tso_write_refs m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))
 = mut_m.tso_write_refs m s"
by (auto simp: mut_m.tso_write_refs_def)

lemma mutator_reachable_tso:
  "sys_mem_write_buffers (mutator m) s = mw_Mutate r f opt_r' # ws
    \<Longrightarrow> mut_m.reachable m r s \<and> (\<forall>r'. opt_r' = Some r' \<longrightarrow> mut_m.reachable m r' s)"
by (auto simp: mut_m.tso_write_refs_def)

text\<open>coloured heaps\<close>

lemma black_heap_eq_imp:
  "eq_imp (\<lambda>(_::unit). (\<lambda>s. \<Union>p. WL p s) \<^bold>\<otimes> sys_fM \<^bold>\<otimes> (\<lambda>s. Option.map_option obj_mark \<circ> sys_heap s))
          black_heap"
apply (clarsimp simp add: eq_imp_def black_heap_def black_def grey_def all_conj_distrib fun_eq_iff split: option.splits)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>x. marked x s \<longleftrightarrow> marked x s'")
 apply (subgoal_tac "\<forall>x. valid_ref x s \<longleftrightarrow> valid_ref x s'")
  apply (subgoal_tac "\<forall>x. (\<forall>p. x \<notin> WL p s) \<longleftrightarrow> (\<forall>p. x \<notin> WL p s')")
   apply clarsimp
  apply (auto simp: set_eq_iff)[1]
 apply clarsimp
 apply (rename_tac x)
 apply (rule eq_impD[OF obj_at_eq_imp])
 apply (drule_tac x=x in spec)
 apply (drule_tac f="Option.map_option \<langle>True\<rangle>" in arg_cong)
 apply (clarsimp simp: map_option.compositionality o_def)
apply (clarsimp simp: map_option.compositionality o_def)
apply (rule eq_impD[OF obj_at_eq_imp])
apply clarsimp
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (drule_tac f="Option.map_option (\<lambda>fl. fl = sys_fM s)" in arg_cong)
apply (simp add: map_option.compositionality o_def)
done

lemma white_heap_eq_imp:
  "eq_imp (\<lambda>(_::unit). sys_fM \<^bold>\<otimes> (\<lambda>s. Option.map_option obj_mark \<circ> sys_heap s))
          white_heap"
apply (clarsimp simp: all_conj_distrib eq_imp_def white_heap_def obj_at_def fun_eq_iff
               split: option.splits)
apply (rule iffI)
apply (metis (hide_lams, no_types) map_option_eq_Some)+
done

lemma no_black_refs_eq_imp:
  "eq_imp (\<lambda>(_::unit). (\<lambda>s. (\<Union>p. WL p s)) \<^bold>\<otimes> sys_fM \<^bold>\<otimes> (\<lambda>s. Option.map_option obj_mark \<circ> sys_heap s))
          no_black_refs"
apply (clarsimp simp add: eq_imp_def no_black_refs_def black_def grey_def all_conj_distrib fun_eq_iff set_eq_iff split: option.splits)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>x. marked x s \<longleftrightarrow> marked x s'")
 apply clarsimp
apply clarsimp
apply (rename_tac x)
apply ( (drule_tac x=x in spec)+ )[1]
apply (auto split: obj_at_splits)
done

lemmas black_heap_fun_upd[simp] = eq_imp_fun_upd[OF black_heap_eq_imp, simplified eq_imp_simps, rule_format]
lemmas white_heap_fun_upd[simp] = eq_imp_fun_upd[OF white_heap_eq_imp, simplified eq_imp_simps, rule_format]
lemmas no_black_refs_fun_upd[simp] = eq_imp_fun_upd[OF no_black_refs_eq_imp, simplified eq_imp_simps, rule_format]

lemma white_heap_imp_no_black_refs[elim!]:
  "white_heap s \<Longrightarrow> no_black_refs s"
apply (clarsimp simp: white_heap_def no_black_refs_def black_def)
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (clarsimp split: obj_at_splits)
done

lemma (in sys) no_black_refs_dequeue[simp]:
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mark r fl # ws; no_black_refs s; valid_W_inv s \<rbrakk>
   \<Longrightarrow> no_black_refs (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))"
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mutate r f r' # ws; no_black_refs s \<rbrakk>
     \<Longrightarrow> no_black_refs (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := r')\<rparr>) (sys_heap s r)),
                                      mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))"
by (auto simp: no_black_refs_def map_option.compositionality o_def)

lemma black_heap_no_greys[elim]:
  "\<lbrakk> black_heap s; valid_refs_inv s \<rbrakk> \<Longrightarrow> no_grey_refs s"
  "\<lbrakk> no_grey_refs s; \<forall>r. marked r s \<or> \<not>valid_ref r s \<rbrakk> \<Longrightarrow> black_heap s"
by (auto simp: black_def black_heap_def no_grey_refs_def dest: valid_refs_invD)

lemma heap_colours_alloc[simp]:
  "\<lbrakk> heap (s sys) r' = None; valid_refs_inv s \<rbrakk>
  \<Longrightarrow> black_heap (s(mutator m := s (mutator m)\<lparr>roots := insert r' (roots (s (mutator m)))\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty\<rparr>)\<rparr>))
  \<longleftrightarrow> black_heap s \<and> fl = sys_fM s"
  "heap (s sys) r' = None
  \<Longrightarrow> white_heap (s(mutator m := s (mutator m)\<lparr>roots := insert r' (roots (s (mutator m)))\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty\<rparr>)\<rparr>))
  \<longleftrightarrow> white_heap s \<and> fl \<noteq> sys_fM s"
 apply (simp_all add: black_heap_def white_heap_def split: obj_at_splits)
 apply (rule iffI)
  apply (intro allI conjI impI)
   apply (rename_tac x)
   apply (drule_tac x=x in spec)
   apply clarsimp
  apply (drule spec[where x=r'], auto dest!: valid_refs_invD split: obj_at_splits)[2]
apply (rule iffI)
 apply (intro allI conjI impI)
  apply (rename_tac x obj)
  apply (drule_tac x=x in spec)
  apply clarsimp
 apply (drule spec[where x=r'], auto dest!: valid_refs_invD split: obj_at_splits)[2]
done

lemma heap_colours_colours:
  "black_heap s \<Longrightarrow> \<not>white r s"
  "white_heap s \<Longrightarrow> \<not>black r s"
by (auto simp: black_heap_def white_heap_def
        dest!: spec[where x=r]
        split: obj_at_splits)

lemma heap_colours_marked:
  "\<lbrakk> black_heap s; obj_at P r s \<rbrakk> \<Longrightarrow> marked r s"
  "\<lbrakk> white_heap s; obj_at P r s \<rbrakk> \<Longrightarrow> white r s"
by (auto simp: black_heap_def white_heap_def
        dest!: spec[where x=r]
        split: obj_at_splits)

lemma (in gc) obj_fields_marked_inv_blacken:
  "\<lbrakk> gc_field_set s = {}; obj_fields_marked_inv s; (gc_tmp_ref s points_to w) s; white w s; tso_writes_inv s \<rbrakk> \<Longrightarrow> False"
by (simp add: obj_fields_marked_inv_def obj_at_field_on_heap_def ran_def split: option.splits obj_at_splits)

lemma (in gc) obj_fields_marked_inv_has_white_path_to_blacken:
  "\<lbrakk> gc_field_set s = {}; gc_tmp_ref s \<in> gc_W s; (gc_tmp_ref s has_white_path_to w) s; obj_fields_marked_inv s; valid_W_inv s; tso_writes_inv s \<rbrakk> \<Longrightarrow> w = gc_tmp_ref s"
apply (drule (1) valid_W_invD)
apply (clarsimp simp: has_white_path_to_def)
apply (erule converse_rtranclpE)
 apply (clarsimp split: obj_at_splits)
apply clarsimp
apply (simp add: obj_fields_marked_inv_def obj_at_field_on_heap_def ran_def split: option.splits obj_at_splits)
done

lemma fold_writes_points_to[rule_format, simplified conj_explode]:
  "heap (fold_writes ws (s sys)) r = Some obj \<and> obj_fields obj f = Some r'
     \<longrightarrow> (r points_to r') s \<or> (\<exists>w \<in> set ws. r' \<in> write_refs w)" (is "?P (fold_writes ws) obj")
unfolding fold_writes_def
apply (rule spec[OF fold_invariant[where P="\<lambda>fr. \<forall>obj. ?P fr obj" and Q="\<lambda>w. w \<in> set ws"]])
  apply simp
 apply (fastforce simp: ran_def split: obj_at_splits)
apply clarsimp
apply (drule (1) bspec)
apply (clarsimp split: mem_write_action.split_asm if_splits)
done

lemma (in mut_m) reachable_load[simp]:
  assumes "sys_read (mutator m) (mr_Ref r f) (s sys) = mv_Ref r'"
  assumes "r \<in> mut_roots s"
  shows "mut_m.reachable m' y (s(mutator m := s (mutator m)\<lparr> roots := mut_roots s \<union> Option.set_option r' \<rparr>)) \<longleftrightarrow> mut_m.reachable m' y s" (is "?lhs = ?rhs")
proof(cases "m' = m")
  case True show ?thesis
  proof(rule iffI)
    assume ?lhs with assms True show ?rhs
apply (clarsimp simp: sys_read_def)
apply (clarsimp simp: reachable_def tso_write_refs_def)
apply (clarsimp simp: sys_read_def fold_writes_def)
 apply (elim disjE)
    apply blast
   defer
  apply blast
 apply blast

apply (fold fold_writes_def)
apply clarsimp
apply (drule (1) fold_writes_points_to)
apply (erule disjE)
 apply (fastforce elim!: converse_rtranclp_into_rtranclp[rotated] split: obj_at_splits intro!: ranI)
apply clarsimp
apply (case_tac w, simp_all)
apply (erule disjE)
 apply (rule_tac x=x in exI)
 apply (fastforce elim!: converse_rtranclp_into_rtranclp[rotated] split: obj_at_splits intro!: ranI)
apply (rule_tac x=x in exI)
apply (fastforce elim!: converse_rtranclp_into_rtranclp[rotated] split: obj_at_splits intro!: ranI)
done (* filthy *)
  next
    assume ?rhs with True show ?lhs by (fastforce simp: reachable_def)
  qed
qed simp

lemma (in mut_m) reachable_deref_del[simp]:
  "\<lbrakk> sys_read (mutator m) (mr_Ref r f) (s sys) = mv_Ref opt_r'; r \<in> mut_roots s; mut_ghost_honorary_root s = {} \<rbrakk>
   \<Longrightarrow> mut_m.reachable m' y (s(mutator m := s (mutator m)\<lparr> ghost_honorary_root := Option.set_option opt_r', ref := opt_r' \<rparr>))
   \<longleftrightarrow> mut_m.reachable m' y s"
apply (clarsimp simp: mut_m.reachable_def sys_read_def)
apply (rule iffI)
 apply clarsimp
 apply (elim disjE)
   apply metis
  apply (erule option_bind_invE; auto dest!: fold_writes_points_to)
 apply (auto elim!: converse_rtranclp_into_rtranclp[rotated]
              simp: tso_write_refs_def)
done

text\<open>strong tricolour\<close>

lemma strong_tricolour_invD:
  "\<lbrakk> black x s; (x points_to y) s; valid_ref y s; strong_tricolour_inv s \<rbrakk>
     \<Longrightarrow> marked y s"
apply (clarsimp simp: strong_tricolour_inv_def)
apply (drule spec[where x=x])
apply (auto split: obj_at_splits)
done

text\<open>grey protects white\<close>

lemma grey_protects_whiteD[dest]:
  "(g grey_protects_white w) s \<Longrightarrow> grey g s \<and> (g = w \<or> white w s)"
by (auto simp: grey_protects_white_def)

lemma grey_protects_whiteI[iff]:
  "grey g s \<Longrightarrow> (g grey_protects_white g) s"
by (simp add: grey_protects_white_def)

lemma grey_protects_whiteE[elim!]:
  "\<lbrakk> (g points_to w) s; grey g s; white w s \<rbrakk> \<Longrightarrow> (g grey_protects_white w) s"
  "\<lbrakk> (g grey_protects_white y) s; (y points_to w) s; white w s \<rbrakk> \<Longrightarrow> (g grey_protects_white w) s"
by (auto simp: grey_protects_white_def)

lemma grey_protects_white_reaches[elim]:
  "(g grey_protects_white w) s \<Longrightarrow> (g reaches w) s"
by (auto simp: grey_protects_white_def)

lemma grey_protects_white_hs_done[simp]:
  "(g grey_protects_white w) (s(mutator m := s (mutator m)\<lparr> W := {}, ghost_handshake_phase := hs' \<rparr>,
                              sys := s sys\<lparr> handshake_pending := hp', W := sys_W s \<union> W (s (mutator m)),
                                            ghost_handshake_in_sync := his' \<rparr>))
  \<longleftrightarrow> (g grey_protects_white w) s"
by (simp add: grey_protects_white_def)

lemma grey_protects_white_alloc[simp]:
  "\<lbrakk> fl = sys_fM s; sys_heap s r = None \<rbrakk>
     \<Longrightarrow> (g grey_protects_white w) (s(mutator m := s (mutator m)\<lparr>roots := insert r (roots (s (mutator m)))\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> (g grey_protects_white w) s"
by (clarsimp simp: grey_protects_white_def has_white_path_to_def)

text\<open>reachable snapshot inv\<close>

lemma (in mut_m) reachable_snapshot_invI[intro]:
  "(\<And>y. reachable y s \<Longrightarrow> in_snapshot y s) \<Longrightarrow> reachable_snapshot_inv s"
by (simp add: reachable_snapshot_inv_def)

lemma (in mut_m) reachable_snapshot_inv_eq_imp:
  "eq_imp (\<lambda>r. mut_roots \<^bold>\<otimes> mut_ghost_honorary_root \<^bold>\<otimes> (\<lambda>s. r \<in> (\<Union>p. WL p s)) \<^bold>\<otimes> sys_fM \<^bold>\<otimes> sys_heap \<^bold>\<otimes> tso_pending_mutate (mutator m))
          reachable_snapshot_inv"
apply (clarsimp simp: eq_imp_def mut_m.reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)
apply (rename_tac s s')
apply (clarsimp simp: black_def grey_def obj_at_def cong: option.case_cong)
apply (subst eq_impD[OF has_white_path_to_eq_imp])
 defer
 apply (subst eq_impD[OF reachable_eq_imp])
  defer
  apply (subgoal_tac "\<forall>x. (\<forall>p. x \<notin> WL p s) \<longleftrightarrow> (\<forall>p. x \<notin> WL p s')")
   apply force
  apply blast
 apply simp
apply simp
done

lemmas reachable_snapshot_fun_upd[simp] = eq_imp_fun_upd[OF mut_m.reachable_snapshot_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma in_snapshotI[intro]:
  "black r s \<Longrightarrow> in_snapshot r s"
  "grey r s \<Longrightarrow> in_snapshot r s"
  "\<lbrakk> white w s; (g grey_protects_white w) s \<rbrakk> \<Longrightarrow> in_snapshot w s"
by (auto simp: in_snapshot_def)

lemma in_snapshot_colours:
  "in_snapshot r s \<Longrightarrow> black r s \<or> grey r s \<or> white r s"
by (auto simp: in_snapshot_def)

lemma in_snapshot_valid_ref:
  "\<lbrakk> in_snapshot r s; valid_refs_inv s \<rbrakk> \<Longrightarrow> valid_ref r s"
by (fastforce dest: in_snapshot_colours)

lemma (in mut_m) reachable_snapshot_inv_sweep_loop_free:
  fixes s :: "('field, 'mut, 'ref) lsts"
  assumes nmr: "white r s"
  assumes ngs: "no_grey_refs s"
  assumes rsi: "reachable_snapshot_inv s"
  shows "reachable_snapshot_inv (s(sys := (s sys)\<lparr>heap := (heap (s sys))(r := None)\<rparr>))" (is "reachable_snapshot_inv ?s'")
proof
  fix y :: "'ref"
  assume rx: "reachable y ?s'"
  then have "black y s \<and> y \<noteq> r"
  proof(induct rule: reachable_induct)
    case (root x) with ngs nmr rsi show ?case
      by (auto dest: reachable_blackD)
  next
    case (ghost_honorary_root x) with ngs nmr rsi show ?case
      apply -
      apply (frule (1) reachable_blackD[where r=x])
       apply (auto simp: reachable_def)
      done
  next
    case (tso_root x) with ngs nmr rsi show ?case
      apply -
      apply (frule (1) reachable_blackD[where r=x])
       apply (auto simp: reachable_def tso_write_refs_def)
      done
  next
    case (reaches x y) with ngs nmr rsi show ?case
      apply (clarsimp simp: reachable_def)
      apply (drule predicate2D[OF rtranclp_mono[where s="\<lambda>x y. (x points_to y) s", OF predicate2I], rotated])
       apply (clarsimp split: obj_at_splits if_splits)
      apply (rule conjI)
       apply (rule reachable_blackD, assumption, assumption)
       apply (simp add: reachable_def)
       apply (blast intro: rtranclp.intros(2))
      apply clarsimp
      apply (frule (1) reachable_blackD[where r=r])
       apply (simp add: reachable_def)
       apply (blast intro: rtranclp.intros(2))
      apply auto
      done
  qed
  then show "in_snapshot y ?s'"
    unfolding in_snapshot_def by simp
qed

lemma reachableI2[intro]:
  "x \<in> mut_m.mut_ghost_honorary_root m s \<Longrightarrow> mut_m.reachable m x s"
by (auto simp: mut_m.reachable_def)

lemma reachable_alloc[simp]:
  assumes rn: "sys_heap s r = None"
  shows "mut_m.reachable m r' (s(mutator m' := (s (mutator m'))\<lparr>roots := insert r (roots (s (mutator m')))\<rparr>, sys := (s sys)\<lparr>heap := (sys_heap s)(r \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> mut_m.reachable m r' s \<or> (m' = m \<and> r' = r)" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs from this assms show ?rhs
  proof(induct rule: reachable_induct)
    case (reaches x y) then show ?case by clarsimp (fastforce simp: mut_m.reachable_def elim: rtranclp.intros(2) split: obj_at_splits)
  qed (auto split: if_splits)
next
  assume ?rhs then show ?lhs
  proof(rule disjE)
    assume "mut_m.reachable m r' s" then show ?thesis
    proof(induct rule: reachable_induct)
      case (tso_root x) then show ?case
        by (fastforce simp: mut_m.reachable_def simp del: fun_upd_apply)
    next
      case (reaches x y) with rn show ?case
        by (fastforce simp: mut_m.reachable_def simp del: fun_upd_apply elim: rtranclp.intros(2))
    qed auto
  next
    assume "m' = m \<and> r' = r" with rn show ?thesis
      by (fastforce simp: mut_m.reachable_def)
  qed
qed

lemma (in mut_m) reachable_snapshot_inv_alloc[simp]:
  fixes s :: "('field, 'mut, 'ref) lsts"
  assumes rn: "sys_heap s r = None"
  assumes fl: "fl = sys_fM s"
  assumes vri: "valid_refs_inv s"
  assumes rsi: "reachable_snapshot_inv s"
  shows "reachable_snapshot_inv (s(mutator m' := (s (mutator m'))\<lparr>roots := insert r (roots (s (mutator m')))\<rparr>, sys := (s sys)\<lparr>heap := (sys_heap s)(r \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty\<rparr>)\<rparr>))" (is "reachable_snapshot_inv ?s'")
using assms unfolding reachable_snapshot_inv_def in_snapshot_def
by (auto simp del: reachable_fun_upd)

lemma (in mut_m) reachable_snapshot_inv_discard_roots[simp]:
  "\<lbrakk> reachable_snapshot_inv s; roots' \<subseteq> roots (s (mutator m)) \<rbrakk>
     \<Longrightarrow> reachable_snapshot_inv (s(mutator m := (s (mutator m))\<lparr>roots := roots'\<rparr>))"
unfolding reachable_snapshot_inv_def reachable_def in_snapshot_def grey_protects_white_def by auto

lemma grey_protects_white_mark[simp]:
  assumes ghg: "ghost_honorary_grey (s p) = {}"
  shows "(\<exists>g. (g grey_protects_white w) (s(p := s p\<lparr> ghost_honorary_grey := {r} \<rparr>)))
      \<longleftrightarrow> (\<exists>g'. (g' grey_protects_white w) s) \<or> (r has_white_path_to w) s" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs
  then obtain g where "(g grey_protects_white w) (s(p := s p\<lparr>ghost_honorary_grey := {r}\<rparr>))" by blast
  from this ghg show ?rhs
    apply (clarsimp simp: grey_protects_white_def has_white_path_to_def if_distrib cong: if_cong)
    apply (rotate_tac 2)
    apply (induct rule: rtranclp.induct)
    apply (auto intro: rtranclp.intros(2))
    done
next
  assume ?rhs then show ?lhs
  proof(safe)
    fix g assume "(g grey_protects_white w) s"
    with ghg show ?thesis
      apply (clarsimp simp: grey_protects_white_def has_white_path_to_def)
      apply (rotate_tac 2)
      apply (induct rule: rtranclp.induct)
      apply (auto intro: rtranclp.intros(2))
      done
  next
    assume "(r has_white_path_to w) s" with ghg show ?thesis
      by (auto simp: grey_protects_white_def has_white_path_to_def)
  qed
qed

(*>*)
subsection\<open>Invariants\<close>

text (in mut_m) \<open>

We need phase invariants in terms of both @{const
"mut_ghost_handshake_phase"} and @{const "sys_ghost_handshake_phase"}
which respectively track what the mutators and GC know by virtue of
the synchronisation structure of the system.

Read the following as ``when mutator \<open>m\<close> is past the specified
handshake, and has yet to reach the next one, ... holds.''

\<close>

primrec (in mut_m) mutator_phase_inv_aux :: "handshake_phase \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "mutator_phase_inv_aux hp_Idle          = \<langle>True\<rangle>"
| "mutator_phase_inv_aux hp_IdleInit      = no_black_refs"
| "mutator_phase_inv_aux hp_InitMark      = marked_insertions"
| "mutator_phase_inv_aux hp_Mark          = (marked_insertions \<^bold>\<and> marked_deletions)"
| "mutator_phase_inv_aux hp_IdleMarkSweep = (marked_insertions \<^bold>\<and> marked_deletions \<^bold>\<and> reachable_snapshot_inv)"

abbreviation (in mut_m) mutator_phase_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "mutator_phase_inv s \<equiv> mutator_phase_inv_aux (mut_ghost_handshake_phase s) s"

abbreviation mutators_phase_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "mutators_phase_inv \<equiv> (\<^bold>\<forall>m. mut_m.mutator_phase_inv m)"

text\<open>

This is what the GC guarantees. Read this as ``when the GC is at or
past the specified handshake, ... holds.''

\<close>

primrec sys_phase_inv_aux :: "handshake_phase \<Rightarrow> ('field, 'mut, 'ref) lsts_pred" where
  "sys_phase_inv_aux hp_Idle          = ( (If sys_fA \<^bold>= sys_fM Then black_heap Else white_heap) \<^bold>\<and> no_grey_refs )"
| "sys_phase_inv_aux hp_IdleInit      = no_black_refs"
| "sys_phase_inv_aux hp_InitMark      = (sys_fA \<^bold>\<noteq> sys_fM \<^bold>\<longrightarrow> no_black_refs)"
| "sys_phase_inv_aux hp_Mark          = \<langle>True\<rangle>"
| "sys_phase_inv_aux hp_IdleMarkSweep = ( (sys_phase \<^bold>= \<langle>ph_Idle\<rangle> \<^bold>\<or> tso_pending_write gc (mw_Phase ph_Idle)) \<^bold>\<longrightarrow> no_grey_refs )"

abbreviation sys_phase_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "sys_phase_inv s \<equiv> sys_phase_inv_aux (sys_ghost_handshake_phase s) s"
(*<*)

declare mut_m.mutator_phase_inv_aux.simps[simp]
case_of_simps mutator_phase_inv_aux_case: mut_m.mutator_phase_inv_aux.simps
case_of_simps sys_phase_inv_aux_case: sys_phase_inv_aux.simps

lemma tso_pending_mutate_cong:
  "\<lbrakk> filter is_mw_Mutate (sys_mem_write_buffers p s) = filter is_mw_Mutate (sys_mem_write_buffers p s'); \<And>r f r'. P r f r' \<longleftrightarrow> Q r f r' \<rbrakk>
     \<Longrightarrow> (\<forall>r f r'. mw_Mutate r f r' \<in> set (sys_mem_write_buffers p s)  \<longrightarrow> P r f r') =
        (\<forall>r f r'. mw_Mutate r f r' \<in> set (sys_mem_write_buffers p s') \<longrightarrow> Q r f r')"
apply (intro iff_allI)
apply (auto dest!: arg_cong[where f=set])
done

lemma (in mut_m) marked_insertions_eq_imp:
  "eq_imp (\<lambda>(_::unit). sys_fM \<^bold>\<otimes> (\<lambda>s. Option.map_option obj_mark \<circ> sys_heap s) \<^bold>\<otimes> tso_pending_mutate (mutator m))
          marked_insertions"
apply (clarsimp simp: eq_imp_def marked_insertions_def obj_at_def fun_eq_iff
               split: mem_write_action.splits)
apply (erule tso_pending_mutate_cong)
apply (clarsimp split: option.splits obj_at_splits)
apply (rename_tac s s' opt x)
apply (drule_tac x=x in spec)
apply auto
done

lemmas marked_insertions_fun_upd[simp] = eq_imp_fun_upd[OF mut_m.marked_insertions_eq_imp, simplified eq_imp_simps, rule_format]

lemma marked_insertionD[elim!]:
  "\<lbrakk> sys_mem_write_buffers (mutator m) s = mw_Mutate r f (Some r') # ws; mut_m.marked_insertions m s \<rbrakk>
     \<Longrightarrow> marked r' s"
by (auto simp: mut_m.marked_insertions_def)

lemma (in mut_m) marked_insertions_store_buffer_empty[intro]:
  "tso_pending_mutate (mutator m) s = [] \<Longrightarrow> marked_insertions s"
by (auto simp: marked_insertions_def filter_empty_conv
        split: mem_write_action.splits option.splits)

lemma (in mut_m) marked_insertions_blacken[simp]:
  "marked_insertions (s(gc := (s gc)\<lparr> W := gc_W s - {r} \<rparr>)) \<longleftrightarrow> marked_insertions s"
by (clarsimp simp: marked_insertions_def
            split: mem_write_action.splits option.splits)

lemma (in mut_m) marked_insertions_alloc[simp]:
  "\<lbrakk> heap (s sys) r' = None; valid_refs_inv s \<rbrakk>
  \<Longrightarrow> marked_insertions (s(mutator m' := s (mutator m')\<lparr>roots := roots'\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> obj')\<rparr>))
  \<longleftrightarrow> marked_insertions s"
apply (clarsimp simp: mut_m.marked_insertions_def split: mem_write_action.splits option.splits)
apply (rule iffI)
 apply clarsimp
 apply (rename_tac ref field x)
 apply (drule_tac x=ref in spec, drule_tac x=field in spec, drule_tac x=x in spec, clarsimp)
 apply (drule valid_refs_invD(6)[where x=r' and y=r'], simp_all)
done

lemma marked_insertions_free[simp]:
  "\<lbrakk> mut_m.marked_insertions m s; white r s \<rbrakk>
     \<Longrightarrow> mut_m.marked_insertions m (s(sys := (s sys)\<lparr>heap := (heap (s sys))(r := None)\<rparr>))"
by (fastforce simp: mut_m.marked_insertions_def split: mem_write_action.splits obj_at_splits option.splits)

lemma (in mut_m) marked_deletions_eq_imp:
  "eq_imp (\<lambda>(_::unit). sys_fM \<^bold>\<otimes> sys_heap \<^bold>\<otimes> tso_pending_mutate (mutator m))
          marked_deletions"
apply (clarsimp simp: eq_imp_def fun_eq_iff marked_deletions_def obj_at_field_on_heap_def)
apply (rule iffI)
 apply (clarsimp split: mem_write_action.splits)
 apply (rename_tac s s' ref field option)
 apply (drule_tac x="mw_Mutate ref field option" in spec)
 apply (drule mp)
  apply (metis (lifting, full_types) filter_set member_filter)
 apply clarsimp
 apply (subst eq_impD[OF obj_at_eq_imp])
  prefer 2
  apply (fastforce cong: option.case_cong)
 apply clarsimp
(* opposite dir *)
apply (clarsimp split: mem_write_action.splits)
apply (rename_tac s s' ref field option)
apply (drule_tac x="mw_Mutate ref field option" in spec)
apply (drule mp)
 apply (metis (lifting, full_types) filter_set member_filter)
apply clarsimp
apply (subst eq_impD[OF obj_at_eq_imp])
 prefer 2
 apply (fastforce cong: option.case_cong)
apply clarsimp
done

lemmas marked_deletions_fun_upd[simp] = eq_imp_fun_upd[OF mut_m.marked_deletions_eq_imp, simplified eq_imp_simps, rule_format]

lemma (in mut_m) marked_deletions_store_buffer_empty[intro]:
  "tso_pending_mutate (mutator m) s = [] \<Longrightarrow> marked_deletions s"
by (auto simp: marked_deletions_def filter_empty_conv
        split: mem_write_action.splits)

lemma (in mut_m) marked_deletions_alloc[simp]:
  "\<lbrakk> marked_deletions s; heap (s sys) r' = None; valid_refs_inv s \<rbrakk>
  \<Longrightarrow> marked_deletions (s(mutator m' := s (mutator m')\<lparr>roots := roots'\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> obj')\<rparr>))"
apply (clarsimp simp: marked_deletions_def split: mem_write_action.splits)
apply (rename_tac ref field option)
apply (drule_tac x="mw_Mutate ref field option" in spec)
apply clarsimp
apply (case_tac "ref = r'")
 apply (auto simp: obj_at_field_on_heap_def split: option.splits)
done

(*>*)

subsection\<open> Mutator proofs \<close>

lemma (in mut_m) reachable_snapshot_inv_hs_get_roots_done[simp]:
  assumes sti: "strong_tricolour_inv s"
  assumes m: "\<forall>r \<in> mut_roots s. marked r s"
  assumes ghr: "mut_ghost_honorary_root s = {}"
  assumes t: "tso_pending_mutate (mutator m) s = []"
  assumes vri: "valid_refs_inv s"
  shows "reachable_snapshot_inv
               (s(mutator m := s (mutator m)\<lparr>W := {}, ghost_handshake_phase := ghp'\<rparr>,
                  sys := s sys\<lparr>handshake_pending := hp', W := sys_W s \<union> mut_W s, ghost_handshake_in_sync := in'\<rparr>))"
  (is "reachable_snapshot_inv ?s'")
proof(rule, clarsimp)
  fix r assume "reachable r s"
  then show "in_snapshot r ?s'"
  proof (induct rule: reachable_induct)
    case (root x) with m show ?case
      apply (clarsimp simp: in_snapshot_def simp del: fun_upd_apply) (* FIXME intro rules *)
      apply (auto dest: marked_imp_black_or_grey)
      done
  next
    case (ghost_honorary_root x) with ghr show ?case by simp
  next
    case (tso_root x) with t show ?case
      apply (clarsimp simp: filter_empty_conv tso_write_refs_def)
      apply (force split: mem_write_action.splits)
      done
  next
    case (reaches x y)
    from reaches vri have "valid_ref x s" "valid_ref y s" by auto
    with reaches sti vri show ?case
      apply (clarsimp simp: in_snapshot_def simp del: fun_upd_apply)
      apply (elim disjE)
       apply (clarsimp simp: strong_tricolour_inv_def)
       apply (drule spec[where x=x])
       apply clarsimp
       apply (auto dest!: marked_imp_black_or_grey)[1]
      apply (cases "white y s")
      apply (auto dest: grey_protects_whiteE
                 dest!: marked_imp_black_or_grey)
        done
    qed
qed

lemma (in mut_m) reachable_snapshot_inv_hs_get_work_done[simp]:
  "reachable_snapshot_inv s
    \<Longrightarrow> reachable_snapshot_inv
               (s(mutator m := s (mutator m)\<lparr>W := {}\<rparr>,
                   sys := s sys\<lparr>handshake_pending := (handshake_pending (s sys))(m := False), W := sys_W s \<union> mut_W s,
                                ghost_handshake_in_sync := (ghost_handshake_in_sync (s sys))(m := True)\<rparr>))"
by (simp add: reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)

lemma (in mut_m) reachable_write_enqueue[simp]:
  "reachable r (s(sys := s sys\<lparr>mem_write_buffers := (mem_write_buffers (s sys))(mutator m := sys_mem_write_buffers (mutator m) s @ [w])\<rparr>))
  \<longleftrightarrow> reachable r s \<or> (\<exists>x. x \<in> write_refs w \<and> (x reaches r) s)"
by (auto simp: reachable_def tso_write_refs_def)

lemma no_black_refs_mo_co_mark[simp]:
  "\<lbrakk> ghost_honorary_grey (s p) = {}; white r s \<rbrakk>
     \<Longrightarrow> no_black_refs (s(p := s p\<lparr>ghost_honorary_grey := {r}\<rparr>)) \<longleftrightarrow> no_black_refs s"
by (auto simp: no_black_refs_def)

lemma (in mut_m) reachable_snapshot_inv_mo_co_mark[simp]:
  "\<lbrakk> ghost_honorary_grey (s p) = {}; reachable_snapshot_inv s \<rbrakk>
     \<Longrightarrow> reachable_snapshot_inv (s(p := s p\<lparr> ghost_honorary_grey := {r} \<rparr>))"
by (auto simp: in_snapshot_def reachable_snapshot_inv_def)

lemma (in mut_m) no_black_refs_alloc[simp]:
  "\<lbrakk> heap (s sys) r' = None; no_black_refs s \<rbrakk>
     \<Longrightarrow> no_black_refs (s(mutator m' := s (mutator m')\<lparr>roots := roots'\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty\<rparr>)\<rparr>))
     \<longleftrightarrow> fl \<noteq> sys_fM s \<or> grey r' s"
by (auto simp: no_black_refs_def)

lemma (in mut_m) reachable_snapshot_inv_load[simp]:
  "\<lbrakk> reachable_snapshot_inv s; sys_read (mutator m) (mr_Ref r f) (s sys) = mv_Ref r'; r \<in> mut_roots s \<rbrakk>
     \<Longrightarrow> reachable_snapshot_inv (s(mutator m := s (mutator m)\<lparr> roots := mut_roots s \<union> Option.set_option r' \<rparr>))"
by (simp add: reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)

lemma (in mut_m) reachable_snapshot_inv_store_ins[simp]:
  "\<lbrakk> reachable_snapshot_inv s; r \<in> mut_roots s; (\<exists>r'. opt_r' = Some r') \<longrightarrow> the opt_r' \<in> mut_roots s \<rbrakk>
     \<Longrightarrow> reachable_snapshot_inv (s(mutator m := s (mutator m)\<lparr>ghost_honorary_root := {}\<rparr>,
                                  sys := s sys\<lparr>  mem_write_buffers := (mem_write_buffers (s sys))(mutator m := sys_mem_write_buffers (mutator m) s @ [mw_Mutate r f opt_r']) \<rparr>))"
apply (clarsimp simp: reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)
apply (drule_tac x=x in spec)
apply (auto simp: reachable_def)
done

lemma (in mut_m) marked_insertions_store_ins[simp]:
  "\<lbrakk> marked_insertions s; (\<exists>r'. opt_r' = Some r') \<longrightarrow> marked (the opt_r') s \<rbrakk>
     \<Longrightarrow> marked_insertions
               (s(mutator m := s (mutator m)\<lparr>ghost_honorary_root := {}\<rparr>,
                   sys := s sys
                     \<lparr>mem_write_buffers := (mem_write_buffers (s sys))(mutator m := sys_mem_write_buffers (mutator m) s @ [mw_Mutate r f opt_r'])\<rparr>))"
by (auto simp: marked_insertions_def
        split: mem_write_action.splits option.splits)

lemma (in mut_m) marked_deletions_store_ins[simp]:
  "\<lbrakk> marked_deletions s; obj_at_field_on_heap (\<lambda>r'. marked r' s) r f s \<rbrakk>
     \<Longrightarrow> marked_deletions
               (s(mutator m := s (mutator m)\<lparr>ghost_honorary_root := {}\<rparr>,
                   sys := s sys
                     \<lparr>mem_write_buffers := (mem_write_buffers (s sys))(mutator m := sys_mem_write_buffers (mutator m) s @ [mw_Mutate r f opt_r'])\<rparr>))"
by (auto simp: marked_deletions_def
        split: mem_write_action.splits option.splits)

lemma (in mut_m) reachable_snapshot_inv_deref_del[simp]:
  "\<lbrakk> reachable_snapshot_inv s; sys_read (mutator m) (mr_Ref r f) (s sys) = mv_Ref opt_r'; r \<in> mut_roots s; mut_ghost_honorary_root s = {} \<rbrakk>
     \<Longrightarrow> reachable_snapshot_inv (s(mutator m := s (mutator m)\<lparr>ghost_honorary_root := Option.set_option opt_r', ref := opt_r'\<rparr>))"
by (clarsimp simp: reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)

lemma (in mut_m) mutator_phase_inv[intro]:
  "\<lbrace> handshake_invL
       \<^bold>\<and> mark_object_invL
       \<^bold>\<and> mut_get_roots.mark_object_invL m
       \<^bold>\<and> mut_store_del.mark_object_invL m
       \<^bold>\<and> mut_store_ins.mark_object_invL m
       \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> phase_rel_inv \<^bold>\<and> strong_tricolour_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP mutator_phase_inv \<rbrace>"
apply (vcg_jackhammer dest!: handshake_phase_invD simp: fA_rel_inv_def fM_rel_inv_def;
       simp add: mutator_phase_inv_aux_case split: handshake_phase.splits if_splits)

subgoal
 apply (drule_tac x=m in spec)
 apply (clarsimp simp: fM_rel_def hp_step_rel_def)
 apply (intro conjI impI; simp)
  apply (elim disjE; force simp: fA_rel_def) (* FIXME annoying: unfolding fA_rel early leads to non-termination *)
 apply (rule reachable_snapshot_inv_alloc, simp_all)
 apply (elim disjE; force simp: fA_rel_def) (* FIXME annoying: unfolding fA_rel early leads to non-termination *)
 done

subgoal for s s'
 apply (drule_tac x=m in spec)
 apply (intro conjI impI)
   apply clarsimp
   apply (rule marked_deletions_store_ins, assumption) (* FIXME shuffle the following into this lemma *)
    apply (cases "(\<forall>opt_r'. mw_Mutate (mut_tmp_ref s\<down>) (mut_field s\<down>) opt_r' \<notin> set (sys_mem_write_buffers (mutator m) s\<down>))")
    apply force
   apply (force simp: marked_deletions_def)
  apply clarsimp
  apply (erule marked_insertions_store_ins)
  apply (drule phase_rel_invD)
  apply (clarsimp simp: phase_rel_def hp_step_rel_def; elim disjE; fastforce dest: reachable_blackD elim: blackD)
 apply clarsimp
 apply (rule marked_deletions_store_ins, assumption) (* FIXME as above *)
 apply clarsimp
 apply (erule disjE)
  apply (drule phase_rel_invD)
  apply (clarsimp simp: phase_rel_def)
  apply (elim disjE, simp_all)[1]
   apply (clarsimp simp: hp_step_rel_def)
  apply (clarsimp simp: hp_step_rel_def)
  apply (case_tac "sys_ghost_handshake_phase s\<down>", simp_all)[1] (* FIXME invert handshake_phase_rel *)
   apply (clarsimp simp: fA_rel_def fM_rel_def)
   apply (elim disjE, simp_all)[1]
   apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits)
   apply (rule conjI)
    apply fast
   apply clarsimp
   apply (frule_tac r=x2a in blackD(1)[OF reachable_blackD], simp_all)[1]
   apply (rule_tac x="mut_tmp_ref s\<down>" in reachableE; auto simp: ran_def split: obj_at_splits; fail)
  apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits)
  apply (rule conjI)
   apply fast
  apply clarsimp
  apply (frule_tac r=x2a in blackD(1)[OF reachable_blackD], simp_all)[1]
  apply (rule_tac x="mut_tmp_ref s\<down>" in reachableE; auto simp: ran_def split: obj_at_splits; fail)
 apply (force simp: marked_deletions_def)
 done

(* hs_noop_done *)
subgoal for s s'
 apply (drule_tac x=m in spec)
 apply (simp add: fA_rel_def fM_rel_def hp_step_rel_def)
 apply (cases "mut_ghost_handshake_phase s\<down>", simp_all)[1] (* FIXME invert handshake_step *)
 apply (erule marked_insertions_store_buffer_empty) (* FIXME simp? *)
 apply (erule marked_deletions_store_buffer_empty) (* FIXME simp? *)
 done

(* hs_get_roots_done *)
subgoal
 apply (drule_tac x=m in spec)
 apply (simp add: fA_rel_def fM_rel_def hp_step_rel_def)
 done

(* hs_get_work_done *)
subgoal
 apply (drule_tac x=m in spec)
 apply (simp add: fA_rel_def fM_rel_def hp_step_rel_def)
 done

done

lemma (in mut_m') mutator_phase_inv[intro]:
  notes mut_m.mark_object_invL_def[inv]
  notes mut_m.handshake_invL_def[inv]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> mut_m.handshake_invL m'
       \<^bold>\<and> mut_m.mark_object_invL m'
       \<^bold>\<and> mut_get_roots.mark_object_invL m'
       \<^bold>\<and> mut_store_del.mark_object_invL m'
       \<^bold>\<and> mut_store_ins.mark_object_invL m'
       \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m'
   \<lbrace> LSTP mutator_phase_inv \<rbrace>"
apply (vcg_jackhammer simp: fA_rel_inv_def fM_rel_inv_def dest!: handshake_phase_invD)
apply (simp_all add: mutator_phase_inv_aux_case split: handshake_phase.splits)

apply (drule spec[where x=m])
apply (intro conjI impI)
 apply (clarsimp simp: fA_rel_def fM_rel_def hp_step_rel_def)
 apply (elim disjE, auto)[1]

 apply (rule reachable_snapshot_inv_alloc, simp_all)[1]
 apply (clarsimp simp: fA_rel_def fM_rel_def hp_step_rel_def)
 apply (elim disjE, auto)[1]

apply (drule spec[where x=m])
apply (clarsimp simp: no_black_refs_def)
apply (clarsimp simp: reachable_snapshot_inv_def in_snapshot_def)

apply (drule spec[where x=m])
apply (clarsimp simp: no_black_refs_def reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)

done

lemma (in sys) grey_protects_white_dequeue_mark[simp]:
  assumes fl: "fl = sys_fM s"
  assumes "r \<in> ghost_honorary_grey (s p)"
  shows "(\<exists>g. (g grey_protects_white w) (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>)))
      \<longleftrightarrow> (\<exists>g. (g grey_protects_white w) s)" (is "(\<exists>g. (g grey_protects_white w) ?s') \<longleftrightarrow> ?rhs")
proof
  assume "\<exists>g. (g grey_protects_white w) ?s'"
  then obtain g where "(g grey_protects_white w) ?s'" by blast
  with assms show ?rhs
    apply (clarsimp simp: grey_protects_white_def has_white_path_to_def)
    apply (rotate_tac -1)
    apply (induct rule: rtranclp.induct)
     apply fastforce
    apply clarsimp
    apply (rename_tac a b c g)
    apply (case_tac "white c s")
     apply (rule_tac x=g in exI)
     apply clarsimp
     apply (erule rtranclp.intros)
     apply clarsimp
    apply (auto split: obj_at_splits if_splits)
    done
next
  assume ?rhs
  then obtain g' where "(g' grey_protects_white w) s" by blast
  with assms show "\<exists>g. (g grey_protects_white w) ?s'"
    apply (clarsimp simp: grey_protects_white_def has_white_path_to_def)
    apply (rotate_tac -1)
    apply (induct rule: rtranclp.induct)
     apply (fastforce simp: grey_def)
    apply clarsimp
    apply (rename_tac a b c g)
    apply (case_tac "c = r")
     apply (clarsimp simp: grey_def)
     apply blast
    apply (rule_tac x=g in exI)
    apply clarsimp
    apply (erule rtranclp.intros)
    apply clarsimp
    done
qed

lemma (in sys) reachable_snapshot_inv_dequeue_mark[simp]:
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mark r fl # ws; mut_m.reachable_snapshot_inv m s; valid_W_inv s \<rbrakk>
     \<Longrightarrow> mut_m.reachable_snapshot_inv m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))"
apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def)
apply (rename_tac x)
apply (subst (asm) reachable_fun_upd, simp_all)[1]
 apply auto[1]
apply (drule_tac x=x in spec)
apply clarsimp
apply (subst (asm) arg_cong[where f=Not, OF grey_protects_white_dequeue_mark, simplified], simp_all)
  apply blast
 apply blast
apply blast
done

lemma (in sys) marked_insertions_dequeue_mark[simp]:
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mark r fl # ws; mut_m.marked_insertions m s; tso_writes_inv s; valid_W_inv s \<rbrakk>
     \<Longrightarrow> mut_m.marked_insertions m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))"
apply (clarsimp simp: mut_m.marked_insertions_def)
apply (cases "mutator m = p")
 apply clarsimp
 apply (rename_tac x)
 apply (drule_tac x=x in spec)
 apply (auto split: mem_write_action.splits option.splits obj_at_splits)[1]
apply clarsimp
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (auto split: mem_write_action.splits option.splits obj_at_splits)[1]
done

lemma (in sys) marked_insertions_dequeue_ref[simp]:
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mutate r f r' # ws; mut_m.marked_insertions m s \<rbrakk>
     \<Longrightarrow> mut_m.marked_insertions m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := r')\<rparr>) (sys_heap s r)),
                                                    mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))"
apply (clarsimp simp: mut_m.marked_insertions_def)
apply (cases "mutator m = p")
 apply clarsimp
 apply (rename_tac x)
 apply (drule_tac x=x in spec)
 apply (auto split: mem_write_action.splits option.splits obj_at_splits)[1]
apply clarsimp
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (auto split: mem_write_action.splits option.splits obj_at_splits)[1]
done

(* redundant to fit with other rules. Perhaps want points_to with explicit witness for f? *)
lemma points_to_mw_Mutate:
  "(x points_to y)
         (s(sys := (s sys)\<lparr> heap := (sys_heap s)(r := Option.map_option (\<lambda>obj :: ('field, 'ref) object. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                            mem_write_buffers := (mem_write_buffers (s sys))(p := ws) \<rparr>))
  \<longleftrightarrow> (r \<noteq> x \<and> (x points_to y) s) \<or> (r = x \<and> valid_ref r s \<and> (opt_r' = Some y \<or> ( (x points_to y) s \<and> obj_at (\<lambda>obj. \<exists>f'. obj_fields obj f' = Some y \<and> f \<noteq> f') r s)))"
by (auto simp: ran_def split: obj_at_splits)

(* shows the snapshot is preserved by the two marks. *)
lemma (in sys) grey_protects_white_dequeue_ref[simp]:
  assumes sb: "sys_mem_write_buffers (mutator m) s = mw_Mutate r f opt_r' # ws"
  assumes mi: "mut_m.marked_insertions m s"
  assumes md: "mut_m.marked_deletions m s"
  notes map_option.compositionality[simp] o_def[simp]
  shows "(\<exists>g. (g grey_protects_white w) (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                                        mem_write_buffers := (mem_write_buffers (s sys))(mutator m := ws)\<rparr>)))
      \<longleftrightarrow> (\<exists>g. (g grey_protects_white w) s)" (is "(\<exists>g. (g grey_protects_white w) ?s') \<longleftrightarrow> ?rhs")
proof
  assume "(\<exists>g. (g grey_protects_white w) ?s')"
  then obtain g where "(g grey_protects_white w) ?s'" by blast
  with mi sb show ?rhs
    apply (clarsimp simp: grey_protects_white_def has_white_path_to_def)
    apply (rotate_tac -1)
    apply (induct rule: rtranclp.induct)
     apply fastforce
    apply (auto simp: points_to_mw_Mutate elim: rtranclp.intros(2))
    apply (rename_tac a c g)
    apply (clarsimp simp: mut_m.marked_insertions_def) (* FIXME rule *)
    apply (drule_tac x="mw_Mutate r f (Some c)" in spec)
    apply (simp split: obj_at_splits)
    done
next
  assume ?rhs then show "(\<exists>g. (g grey_protects_white w) ?s')"
  proof(clarsimp)
    fix g assume "(g grey_protects_white w) s"
    with md sb show ?thesis
      apply (clarsimp simp: grey_protects_white_def has_white_path_to_def)
      apply (rotate_tac -1)
      apply (induct rule: rtranclp.induct)
       apply fastforce
      apply clarsimp
      apply (rename_tac a b c g)

      apply (case_tac "b = r")
       defer
       apply (auto simp: points_to_mw_Mutate elim: rtranclp.intros(2))[1]
      apply clarsimp
      apply (subst (asm) (3) obj_at_def) (* FIXME rule: witness field for r points_to c *)
      apply (clarsimp simp: ran_def split: option.splits)
      apply (rename_tac a c g x2 aa)
      apply (case_tac "aa = f")
       defer
       apply (rule_tac x=g in exI)
       apply clarsimp
       apply (erule rtranclp.intros)
       apply (auto split: obj_at_splits)[1]
      apply clarsimp

      apply (clarsimp simp: mut_m.marked_deletions_def) (* FIXME rule *)
      apply (drule spec[where x="mw_Mutate r f opt_r'"])
      apply (clarsimp simp: obj_at_field_on_heap_def)
      apply (simp split: obj_at_splits)
      done
  qed
qed

(* write barrier installed but not all mutators are necessarily past get_roots *)
lemma (in sys) reachable_snapshot_inv_dequeue_ref[simp]:
  fixes s :: "('field, 'mut, 'ref) lsts"
  assumes sb: "sys_mem_write_buffers (mutator m') s = mw_Mutate r f opt_r' # ws"
  assumes mi: "mut_m.marked_insertions m' s"
  assumes md: "mut_m.marked_deletions m' s"
  assumes rsi: "mut_m.reachable_snapshot_inv m s"
  assumes sti: "strong_tricolour_inv s"
  assumes vri: "valid_refs_inv s"
  notes map_option.compositionality[simp] o_def[simp]
  shows "mut_m.reachable_snapshot_inv m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                                        mem_write_buffers := (mem_write_buffers (s sys))(mutator m' := ws)\<rparr>))" (is "mut_m.reachable_snapshot_inv m ?s'")
proof(rule mut_m.reachable_snapshot_invI)
  fix y assume y: "mut_m.reachable m y ?s'"
  then have "(mut_m.reachable m y s \<or> mut_m.reachable m' y s) \<and> in_snapshot y ?s'"
  proof(induct rule: reachable_induct)
    case (root x) with mi md rsi sb show ?case
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def
                  simp del: fun_upd_apply)
      apply auto
      done
  next
    case (ghost_honorary_root x) with mi md rsi sb show ?case
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def
                  simp del: fun_upd_apply)
      apply auto
      done
  next
    case (tso_root x) with mi md rsi sb show ?case
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def
                  simp del: fun_upd_apply)
      apply (clarsimp split: if_splits)
       apply (rename_tac xa)
       apply (case_tac xa, simp_all)[1]
       apply (rename_tac ref field option)
       apply (clarsimp simp: mut_m.marked_deletions_def mut_m.marked_insertions_def)
       apply (drule_tac x="mw_Mutate ref field option" in spec)
       apply (drule_tac x="mw_Mutate ref field option" in spec)
       apply clarsimp
       apply (frule spec[where x=x])
       apply (subgoal_tac "mut_m.reachable m x s")
        apply force
       apply (rule reachableI(2))
       apply (force simp: mut_m.tso_write_refs_def)
      apply auto
      done
  next
    case (reaches x y)
    from reaches sb have y: "mut_m.reachable m y s \<or> mut_m.reachable m' y s"
      apply (clarsimp simp: points_to_mw_Mutate mut_m.reachable_snapshot_inv_def in_snapshot_def)
      apply (elim disjE, (force dest!: reachableE mutator_reachable_tso)+)[1]
      done
    moreover
    from y vri have "valid_ref y s" by auto
    with reaches mi md rsi sb sti y have "(black y s \<or> (\<exists>x. (x grey_protects_white y) s))"
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def
                  simp del: fun_upd_apply)
      apply clarsimp
      apply (drule spec[where x=y])
      apply (clarsimp simp: points_to_mw_Mutate mut_m.marked_insertions_def mut_m.marked_deletions_def) (* FIXME lemmas *)
      apply (drule spec[where x="mw_Mutate r f opt_r'"])+
      apply clarsimp
      apply (elim disjE, simp_all) (* FIXME probably want points_to_mw_Mutate as an elim rule to make this robust, reduce duplication *)
       apply (force dest!: reachableE)
       apply (force dest!: reachableE)

       apply clarsimp
       apply (drule (3) strong_tricolour_invD)
       apply (metis (no_types) grey_protects_whiteI marked_imp_black_or_grey(1))

       apply clarsimp
       apply (cases "white y s") (* FIXME lemma *)
        apply (drule (2) grey_protects_whiteE)
        apply blast
       apply (force simp: black_def split: obj_at_splits)

       apply clarsimp
       apply (elim disjE, simp_all)
        apply (force simp: black_def)
       apply clarsimp
       apply (drule (3) strong_tricolour_invD)
       apply (force simp: black_def)

       apply clarsimp
       apply (elim disjE, simp_all)
        apply (force simp: black_def)
       apply clarsimp
       apply (cases "white y s") (* FIXME lemma *)
        apply (drule (2) grey_protects_whiteE)
        apply blast
       apply (force simp: black_def split: obj_at_splits)

       apply clarsimp
       apply (elim disjE, simp_all)
        apply (force simp: black_def)
       apply clarsimp
       apply (drule (3) strong_tricolour_invD)
       apply (force simp: black_def)

       apply clarsimp
       apply (elim disjE, simp_all)
        apply (force simp: black_def)
       apply clarsimp
       apply (cases "white y s") (* FIXME lemma *)
        apply (drule (2) grey_protects_whiteE)
        apply blast
       apply (force simp: black_def split: obj_at_splits)
       done
    moreover note mi md rsi sb
    ultimately show ?case
      apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def
                  simp del: fun_upd_apply)
      apply clarsimp
      done
  qed
  then show "in_snapshot y ?s'" by blast
qed

lemma valid_refs_invI:
  "\<lbrakk> \<And>m x y. \<lbrakk> (x reaches y) s; x \<in> mut_m.mut_roots m s \<or> x \<in> mut_m.mut_ghost_honorary_root m s \<or> x \<in> mut_m.tso_write_refs m s \<or> grey x s \<rbrakk> \<Longrightarrow> valid_ref y s
   \<rbrakk> \<Longrightarrow> valid_refs_inv s"
by (auto simp: valid_refs_inv_def mut_m.reachable_def grey_reachable_def)

lemma black_heap_reachable:
  assumes "mut_m.reachable m y s"
  assumes bh: "black_heap s"
  assumes vri: "valid_refs_inv s"
  shows "black y s"
using assms
apply (induct rule: reachable_induct)
apply (simp_all add: black_heap_def valid_refs_invD)
apply (metis obj_at_weakenE reachableE valid_refs_inv_def)
done

lemma valid_refs_inv_dequeue_ref[simp]:
  notes map_option.compositionality[simp] o_def[simp]
  fixes s :: "('field, 'mut, 'ref) lsts"
  assumes vri: "valid_refs_inv s"
  assumes sb: "sys_mem_write_buffers (mutator m') s = mw_Mutate r f opt_r' # ws"
  shows "valid_refs_inv (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                        mem_write_buffers := (mem_write_buffers (s sys))(mutator m' := ws)\<rparr>))" (is "valid_refs_inv ?s'")
proof(rule valid_refs_invI)
  fix m
  let ?root = "\<lambda>m x (s::('field, 'mut, 'ref) lsts). x \<in> mut_m.mut_roots m s \<or> x \<in> mut_m.mut_ghost_honorary_root m s \<or> x \<in> mut_m.tso_write_refs m s \<or> grey x s"
  fix x y assume xy: "(x reaches y) ?s'" and x: "?root m x ?s'"
  from xy have "(\<exists>m x. ?root m x s \<and> (x reaches y) s) \<and> valid_ref y ?s'"
  proof induct
    case base with x sb vri show ?case
      apply -
      apply (subst obj_at_fun_upd)
       apply (auto simp: mut_m.tso_write_refs_def split: if_splits intro: valid_refs_invD(5)[where m=m])
      apply (metis list.set_intros(2) rtranclp.rtrancl_refl)
      done (* FIXME rules *)
  next
    case (step y z)
    with sb vri show ?case
      apply -
      apply (subst obj_at_fun_upd, clarsimp)
      apply (subst (asm) obj_at_fun_upd, fastforce)
      apply (clarsimp simp: points_to_mw_Mutate simp del: fun_upd_apply)
      apply (fastforce elim: rtranclp.intros(2) simp: mut_m.tso_write_refs_def intro: exI[where x=m'] valid_refs_invD(5)[where m=m'])
      done
   qed
  then show "valid_ref y ?s'" by blast
qed

declare map_option.compositionality[simp] o_def[simp]

lemma (in sys) reachable_snapshot_inv_black_heap_no_grey_refs_dequeue_ref[simp]:
  assumes sb: "sys_mem_write_buffers (mutator m') s = mw_Mutate r f opt_r' # ws"
  assumes bh: "black_heap s"
  assumes ngr: "no_grey_refs s"
  assumes vri: "valid_refs_inv s"
  shows "mut_m.reachable_snapshot_inv m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                                        mem_write_buffers := (mem_write_buffers (s sys))(mutator m' := ws)\<rparr>))" (is "mut_m.reachable_snapshot_inv m ?s'")
apply (rule mut_m.reachable_snapshot_invI)
apply (rule in_snapshotI)
apply (erule black_heap_reachable)
 using bh vri
 apply (simp add: black_heap_def)
using bh ngr sb vri
apply (subst valid_refs_inv_def)
apply clarsimp
apply (simp add: no_grey_refs_def grey_reachable_def)
apply clarsimp
apply (drule black_heap_reachable)
  apply (simp add: black_heap_def)
 apply clarsimp
apply auto
done

lemma (in sys) marked_deletions_dequeue_mark[simp]:
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mark r fl # ws; mut_m.marked_deletions m s; tso_writes_inv s; valid_W_inv s \<rbrakk>
     \<Longrightarrow> mut_m.marked_deletions m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))"
apply (clarsimp simp: mut_m.marked_deletions_def)
apply (cases "mutator m = p")
 apply clarsimp
 apply (rename_tac x)
 apply (drule_tac x=x in spec)
 apply (clarsimp split: mem_write_action.splits)
 apply (simp add: obj_at_field_on_heap_def cong: option.case_cong)
 apply (auto split: option.splits)[1]
apply clarsimp
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (clarsimp split: mem_write_action.splits)
apply (simp add: obj_at_field_on_heap_def cong: option.case_cong)
apply (auto split: option.splits)[1]
done

lemma (in sys) marked_deletions_dequeue_ref[simp]:
  "\<lbrakk> sys_mem_write_buffers (mutator m') s = mw_Mutate r f opt_r' # ws; mut_m.marked_deletions m s; mut_m.marked_insertions m' s \<rbrakk>
     \<Longrightarrow> mut_m.marked_deletions m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                                 mem_write_buffers := (mem_write_buffers (s sys))((mutator m') := ws)\<rparr>))"
apply (clarsimp simp: mut_m.marked_deletions_def)
apply (cases "m = m'")
 apply clarsimp
 apply (rename_tac x)
 apply (drule_tac x=x in spec)
 apply (fastforce simp: obj_at_field_on_heap_def mut_m.marked_insertions_def split: mem_write_action.splits obj_at_splits option.splits)
apply clarsimp
apply (rename_tac x)
apply (drule_tac x=x in spec)
apply (fastforce simp: obj_at_field_on_heap_def mut_m.marked_insertions_def split: mem_write_action.splits obj_at_splits option.splits)
done

lemma (in sys) black_heap_marked_insertions_dequeue[simp]:
  "\<lbrakk> black_heap s; valid_refs_inv s \<rbrakk> \<Longrightarrow> mut_m.marked_insertions m s"
by (auto simp: mut_m.marked_insertions_def black_heap_def black_def
        split: mem_write_action.splits option.splits
         dest: valid_refs_invD)

lemma (in sys) mutator_phase_inv[intro]:
  "\<lbrace> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> strong_tricolour_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> tso_writes_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> LSTP (mut_m.mutator_phase_inv m) \<rbrace>"
apply vcg_nihe
apply vcg_ni

apply (clarsimp simp: fA_rel_inv_def fM_rel_inv_def mutator_phase_inv_aux_case p_not_sys hp_step_rel_def do_write_action_def
               split: handshake_phase.splits mem_write_action.splits)

(* fM *)
prefer 2
apply (drule mut_m.handshake_phase_invD[where m=m])
apply (erule disjE)
 apply (clarsimp simp: fM_rel_def hp_step_rel_def)
apply clarsimp

(* FIXME mess *)
apply (frule mut_m.handshake_phase_invD[where m=m])
apply (intro allI conjI impI)
  apply (erule disjE)
   apply auto[1]
  apply clarsimp
  apply (rename_tac s s' ws ref field option ma)
  apply (rule marked_deletions_dequeue_ref, simp_all)
  apply (drule_tac x=ma in spec)
  apply (frule_tac m=ma in mut_m.handshake_phase_invD, clarsimp simp: hp_step_rel_def)
  apply (elim disjE, simp_all)[1]
 apply (erule disjE)
  apply auto[1]
 apply clarsimp
 apply (rule marked_deletions_dequeue_ref, simp_all)
 apply (drule_tac x=ma in spec)
 apply (frule_tac m=ma in mut_m.handshake_phase_invD, clarsimp simp: hp_step_rel_def)
 apply (elim disjE, simp_all)[1]
 apply (clarsimp simp: fA_rel_def fM_rel_def if_splits)
 apply (elim disjE, simp_all)[1]

apply (erule disjE, simp)
apply (clarsimp simp: hp_step_rel_def)
apply (frule_tac m=ma in mut_m.handshake_phase_invD, clarsimp simp: hp_step_rel_def)
apply (elim disjE, simp_all split: if_splits)[1]
apply (clarsimp simp: fA_rel_def fM_rel_def, blast)
done

(*>*)

subsection\<open>The infamous termination argument.\<close>

text\<open>

We need to know that if the GC does not receive any further work to do
at \<open>get_roots\<close> and \<open>get_work\<close>, then there are no grey
objects left. Essentially this encodes the stability property that
grey objects must exist for mutators to create grey objects.

Note that this is not invariant across the scan: it is possible for
the GC to hold all the grey references. The two handshakes transform
the GC's local knowledge that it has no more work to do into a global
property, or gives it more work.

\<close>

definition (in mut_m) gc_W_empty_mut_inv :: "('field, 'mut, 'ref) lsts_pred" where
  "gc_W_empty_mut_inv =
      ((EMPTY sys_W \<^bold>\<and> sys_ghost_handshake_in_sync m \<^bold>\<and> \<^bold>\<not>(EMPTY (WL (mutator m))))
   \<^bold>\<longrightarrow> (\<^bold>\<exists>m'. \<^bold>\<not>(sys_ghost_handshake_in_sync m') \<^bold>\<and> \<^bold>\<not>(EMPTY (WL (mutator m')))))"

locset_definition (in -) gc_W_empty_locs :: "location set" where
  "gc_W_empty_locs \<equiv>
       idle_locs \<union> init_locs \<union> sweep_locs \<union> { ''mark_read_fM'', ''mark_write_fA'', ''mark_end'' }
     \<union> prefixed ''mark_noop''
     \<union> prefixed ''mark_loop_get_roots''
     \<union> prefixed ''mark_loop_get_work''"

locset_definition "black_heap_locs = { ''sweep_idle'', ''idle_noop_mfence'', ''idle_noop_init_type'' }"
locset_definition "no_grey_refs_locs = black_heap_locs \<union> sweep_locs \<union> {''mark_end''}"

inv_definition (in gc) gc_W_empty_invL :: "('field, 'mut, 'ref) gc_pred" where
  "gc_W_empty_invL =
   (atS_gc (hs_get_roots_locs \<union> hs_get_work_locs)  (\<^bold>\<forall>m. mut_m.gc_W_empty_mut_inv m)
  \<^bold>\<and> at_gc ''mark_loop_get_roots_load_W''          (EMPTY sys_W \<^bold>\<longrightarrow> no_grey_refs)
  \<^bold>\<and> at_gc ''mark_loop_get_work_load_W''           (EMPTY sys_W \<^bold>\<longrightarrow> no_grey_refs)
  \<^bold>\<and> at_gc ''mark_loop''                           (EMPTY gc_W \<^bold>\<longrightarrow> no_grey_refs)
  \<^bold>\<and> atS_gc no_grey_refs_locs                      no_grey_refs
  \<^bold>\<and> atS_gc gc_W_empty_locs                        (EMPTY gc_W))"
(*<*)

lemma (in mut_m) gc_W_empty_mut_inv_eq_imp:
  "eq_imp (\<lambda>m'. sys_W \<^bold>\<otimes> WL (mutator m') \<^bold>\<otimes> sys_ghost_handshake_in_sync m')
          gc_W_empty_mut_inv"
by (simp add: eq_imp_def gc_W_empty_mut_inv_def)

lemmas gc_W_empty_mut_inv_fun_upd[simp] = eq_imp_fun_upd[OF mut_m.gc_W_empty_mut_inv_eq_imp, simplified eq_imp_simps, rule_format]

lemma (in gc) gc_W_empty_invL_eq_imp:
  "eq_imp (\<lambda>(m', p) s. (AT s gc, s\<down> gc, sys_W s\<down>, WL p s\<down>, sys_ghost_handshake_in_sync m' s\<down>))
          gc_W_empty_invL"
by (simp add: eq_imp_def gc_W_empty_invL_def mut_m.gc_W_empty_mut_inv_def no_grey_refs_def grey_def)

lemmas gc_W_empty_invL_niE[nie] =
  iffD1[OF gc.gc_W_empty_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode, rule_format], rotated -1]

lemma get_roots_get_work_subseteq_gc_W_empty_locs:
  "hs_get_roots_locs \<union> hs_get_work_locs \<subseteq> gc_W_empty_locs"
by (auto simp: hs_get_roots_locs_def hs_get_work_locs_def gc_W_empty_locs_def)

lemma (in gc) gc_W_empty_mut_inv_handshake_init[iff]:
  "mut_m.gc_W_empty_mut_inv m (s(sys := s sys\<lparr>handshake_type := ht, ghost_handshake_in_sync := \<langle>False\<rangle>\<rparr>))"
  "mut_m.gc_W_empty_mut_inv m (s(sys := s sys\<lparr>handshake_type := ht, ghost_handshake_in_sync := \<langle>False\<rangle>, ghost_handshake_phase := hp' \<rparr>))"
by (simp_all add: mut_m.gc_W_empty_mut_inv_def)

lemma gc_W_empty_mut_inv_load_W:
  "\<lbrakk> \<forall>m. mut_m.gc_W_empty_mut_inv m s; \<forall>m. sys_ghost_handshake_in_sync m s; WL gc s = {}; WL sys s = {} \<rbrakk>
     \<Longrightarrow> no_grey_refs s"
apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def no_grey_refs_def grey_def)
apply (rename_tac x xa)
apply (case_tac xa)
apply (simp_all add: WL_def)
done

lemma (in gc) gc_W_empty_invL[intro]:
  "\<lbrace> handshake_invL \<^bold>\<and> obj_fields_marked_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> LSTP valid_W_inv \<rbrace>
     gc
   \<lbrace> gc_W_empty_invL \<rbrace>"
apply vcg_jackhammer
apply (auto elim: gc_W_empty_mut_inv_load_W simp: WL_def)
done

lemma (in sys) gc_gc_W_empty_invL[intro]:
  "\<lbrace> gc.gc_W_empty_invL \<rbrace> sys"
by vcg_nihe

lemma (in gc) handshake_get_rootsD:
  "\<lbrakk> atS gc hs_get_roots_locs s; handshake_invL s \<rbrakk> \<Longrightarrow> sys_ghost_handshake_phase s\<down> = hp_IdleMarkSweep \<and> sys_handshake_type s\<down> = ht_GetRoots"
apply (simp add: handshake_invL_def)
apply (elim conjE)
apply (drule mp, erule atS_mono[OF _ hs_get_roots_locs_subseteq_hp_IdleMarkSweep_locs])
apply simp
done

lemma (in gc) handshake_get_workD:
  "\<lbrakk> atS gc hs_get_work_locs s; handshake_invL s \<rbrakk> \<Longrightarrow> sys_ghost_handshake_phase s\<down> = hp_IdleMarkSweep \<and> sys_handshake_type s\<down> = ht_GetWork"
apply (simp add: handshake_invL_def)
apply (elim conjE)
apply (drule mp, erule atS_mono[OF _ hs_get_work_locs_subseteq_hp_IdleMarkSweep_locs])
apply simp
done

lemma (in gc) handshake_get_roots_get_workD:
  "\<lbrakk> atS gc (hs_get_roots_locs \<union> hs_get_work_locs) s; handshake_invL s \<rbrakk> \<Longrightarrow> sys_ghost_handshake_phase s\<down> = hp_IdleMarkSweep \<and> sys_handshake_type s\<down> \<in> {ht_GetWork, ht_GetRoots}"
apply (simp add: handshake_invL_def)
apply (elim conjE)
apply (drule mp, rule atS_mono[OF _ iffD2[OF Un_subset_iff, unfolded conj_explode, OF hs_get_roots_locs_subseteq_hp_IdleMarkSweep_locs hs_get_work_locs_subseteq_hp_IdleMarkSweep_locs]], assumption)
apply (auto simp: atS_un)
done

lemma no_grey_refs_locs_subseteq_hs_in_sync_locs:
  "no_grey_refs_locs \<subseteq> hs_in_sync_locs"
by (auto simp: no_grey_refs_locs_def black_heap_locs_def hs_in_sync_locs_def hs_done_locs_def sweep_locs_def
         dest: prefix_same_cases)

lemma (in mut_m) handshake_sweep_mark_endD:
  "\<lbrakk> atS gc no_grey_refs_locs s; gc.handshake_invL s; handshake_phase_inv s\<down> \<rbrakk>
     \<Longrightarrow> mut_ghost_handshake_phase s\<down> = hp_IdleMarkSweep \<and> All (ghost_handshake_in_sync (s\<down> sys))"
apply (simp add: gc.handshake_invL_def)
apply (elim conjE)
apply (drule mp, erule atS_mono[OF _ no_grey_refs_locs_subseteq_hs_in_sync_locs])
apply (drule handshake_phase_invD)
apply (simp only: no_grey_refs_locs_def cong del: atS_state_cong)
apply (clarsimp simp: atS_un)
apply (elim disjE)
  apply (drule mp, erule atS_mono[where ls'="hp_IdleMarkSweep_locs"])
   apply (clarsimp simp: black_heap_locs_def loc)
  apply (clarsimp simp: hp_step_rel_def)
  apply blast
 apply (drule mp, erule atS_mono[where ls'="hp_IdleMarkSweep_locs"])
  apply (clarsimp simp: hp_IdleMarkSweep_locs_def hp_step_rel_def)
 apply (clarsimp simp: hp_step_rel_def)
 apply blast
apply (clarsimp simp: atS_simps loc hp_step_rel_def)
apply blast
done

lemma empty_WL_GC:
  "\<lbrakk> atS gc (hs_get_roots_locs \<union> hs_get_work_locs) s; gc.obj_fields_marked_invL s \<rbrakk> \<Longrightarrow> gc_ghost_honorary_grey s\<down> = {}"
by (clarsimp simp: gc.obj_fields_marked_invL_def
            dest!: atS_mono[OF _ get_roots_get_work_subseteq_ghost_honorary_grey_empty_locs])

(* think about showing gc_W_empty_invL instead *)
lemma (in mut_m) gc_W_empty_mut_mo_co_mark[simp]:
  "\<lbrakk> \<forall>x. mut_m.gc_W_empty_mut_inv x s\<down>; mutators_phase_inv s\<down>;
     mut_ghost_honorary_grey s\<down> = {};
     r \<in> mut_roots s\<down> \<union> mut_ghost_honorary_root s\<down>; white r s\<down>;
     atS gc (hs_get_roots_locs \<union> hs_get_work_locs) s; gc.handshake_invL s; gc.obj_fields_marked_invL s;
     atS gc gc_W_empty_locs s \<longrightarrow> gc_W s\<down> = {};
     handshake_phase_inv s\<down>; valid_W_inv s\<down> \<rbrakk>
    \<Longrightarrow> mut_m.gc_W_empty_mut_inv m' (s\<down>(mutator m := s\<down> (mutator m)\<lparr>ghost_honorary_grey := {r}\<rparr>))"
apply (frule (1) gc.handshake_get_roots_get_workD)
apply (frule handshake_phase_invD)
apply (clarsimp simp: hp_step_rel_def simp del: Un_iff)
apply (elim disjE, simp_all)
   (* before get work *)
   apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def)
   apply blast
  (* past get work *)
  apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def)
  apply (frule spec[where x=m], clarsimp)
  apply (frule (2) reachable_snapshot_inv_white_root)
  apply clarsimp
  apply (drule grey_protects_whiteD)
  apply (clarsimp simp: grey_def)
  apply (rename_tac g x)
  apply (case_tac x, simp_all)
    (* Can't be the GC *)
    prefer 2
    apply (frule (1) empty_WL_GC)
    apply (drule mp, erule atS_mono[OF _ get_roots_get_work_subseteq_gc_W_empty_locs])
    apply (clarsimp simp: WL_def)
   (* Can't be sys *)
   prefer 2
   apply (clarsimp simp: WL_def)
  apply clarsimp
  apply (rename_tac g mut)
  apply (case_tac "sys_ghost_handshake_in_sync mut s\<down>")
   apply (drule mp, rule_tac x=mut in exI, clarsimp)
   apply blast
  apply (rule_tac x=mut in exI)
  apply clarsimp
 (* before get roots *)
 apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def)
 apply blast
(* after get roots *)
apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def)
apply (frule spec[where x=m], clarsimp)
apply (frule (2) reachable_snapshot_inv_white_root)
apply clarsimp
apply (drule grey_protects_whiteD)
apply (clarsimp simp: grey_def)
apply (rename_tac g x)
apply (case_tac x, simp_all)
  (* Can't be the GC *)
  prefer 2
  apply (frule (1) empty_WL_GC)
  apply (drule mp, erule atS_mono[OF _ get_roots_get_work_subseteq_gc_W_empty_locs])
  apply (clarsimp simp: WL_def)
 (* Can't be sys *)
 prefer 2
 apply (clarsimp simp: WL_def)
apply clarsimp
apply (rename_tac g mut)
apply (case_tac "sys_ghost_handshake_in_sync mut s\<down>")
 apply (drule mp, rule_tac x=mut in exI, clarsimp)
 apply blast
apply (rule_tac x=mut in exI)
apply clarsimp
done (* FIXME common up *)

lemma (in mut_m) no_grey_refs_mo_co_mark[simp]:
  "\<lbrakk> mutators_phase_inv s\<down>;
     no_grey_refs s\<down>;
     gc.handshake_invL s;
     at gc ''mark_loop'' s \<or> at gc ''mark_loop_get_roots_load_W'' s \<or> at gc ''mark_loop_get_work_load_W'' s \<or> atS gc no_grey_refs_locs s;
     r \<in> mut_roots s\<down> \<union> mut_ghost_honorary_root s\<down>; white r s\<down>;
     handshake_phase_inv s\<down> \<rbrakk>
    \<Longrightarrow> no_grey_refs (s\<down>(mutator m := s\<down> (mutator m)\<lparr>ghost_honorary_grey := {r}\<rparr>))"
apply (elim disjE)
   apply (clarsimp simp: atS_simps gc.handshake_invL_def loc)
   apply (frule handshake_phase_invD)
   apply (clarsimp simp: hp_step_rel_def)
   apply (drule spec[where x=m])
   apply (clarsimp simp: conj_disj_distribR[symmetric])
   apply (drule (2) no_grey_refs_not_rootD)
   apply blast
  apply (clarsimp simp: atS_simps gc.handshake_invL_def loc)
  apply (frule handshake_phase_invD)
  apply (clarsimp simp: hp_step_rel_def)
  apply (drule spec[where x=m])
  apply (clarsimp simp: conj_disj_distribR[symmetric])
  apply (drule (2) no_grey_refs_not_rootD)
  apply blast
 apply (clarsimp simp: atS_simps gc.handshake_invL_def loc)
 apply (frule handshake_phase_invD)
 apply (clarsimp simp: hp_step_rel_def)
 apply (drule spec[where x=m])
 apply clarsimp
 apply (drule (2) no_grey_refs_not_rootD)
 apply blast
apply (frule (2) handshake_sweep_mark_endD)
apply (drule spec[where x=m])
apply clarsimp
apply (drule (2) no_grey_refs_not_rootD)
apply blast
done

lemma (in mut_m) gc_W_empty_invL[intro]:
  notes gc.gc_W_empty_invL_def[inv]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> mark_object_invL \<^bold>\<and> tso_lock_invL
             \<^bold>\<and> mut_get_roots.mark_object_invL m
             \<^bold>\<and> mut_store_del.mark_object_invL m
             \<^bold>\<and> mut_store_ins.mark_object_invL m
           \<^bold>\<and> gc.handshake_invL \<^bold>\<and> gc.obj_fields_marked_invL
           \<^bold>\<and> gc.gc_W_empty_invL
             \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     mutator m
   \<lbrace> gc.gc_W_empty_invL \<rbrace>"
apply vcg_nihe
(* apply vcg_ni -- very slow *)
apply(tactic \<open>
let val ctxt = @{context} in

  TRY (HEADGOAL (vcg_clarsimp_tac ctxt))
THEN
  PARALLEL_ALLGOALS (
               vcg_sem_tac ctxt
         THEN' (TRY o SELECT_GOAL (Local_Defs.unfold_tac ctxt (Named_Theorems.get ctxt @{named_theorems inv})))
         THEN' (TRY o REPEAT_ALL_NEW (Tactic.match_tac ctxt @{thms conjI})) (* expose the location predicates, do not split the consequents *)
  THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (Tactic.match_tac ctxt @{thms impI}))
                   (* Preserve the label sets in atS but normalise the label in at; turn s' into s *)
  THEN_ALL_NEW full_simp_tac ctxt (* FIXME vcg_ni uses asm_full_simp_tac here *)
  THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (Tactic.ematch_tac ctxt @{thms conjE}))
                   (* The effect of vcg_pre: should be cheap *)
  THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (Tactic.ematch_tac ctxt @{thms thin_locs} THEN' REPEAT1 o assume_tac ctxt))
  THEN_ALL_NEW asm_full_simp_tac (ss_only (@{thms loc_simps} @ Named_Theorems.get ctxt @{named_theorems loc}) ctxt)
  THEN_ALL_NEW (TRY o REPEAT_ALL_NEW (Rule_Insts.thin_tac ctxt "True" []))
  THEN_ALL_NEW clarsimp_tac ctxt)

end
\<close>)

(* hs_noop_done *)
apply (clarsimp simp: atS_un gc.handshake_invL_def)

(* hs_get_roots_done: gc_W_empty *)
apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def)
apply (rule conjI)
 apply (clarsimp simp: WL_def)
apply clarsimp
apply (drule mp)
 apply blast
apply (clarsimp simp: WL_def)
apply (rename_tac xa)
apply (rule_tac x=xa in exI)
apply clarsimp

(* hs_get_roots_done: no_grey_refs *)
apply (simp add: no_grey_refs_def)
apply (simp add: no_grey_refs_def)

(* hs_get_work_done: gc_W_empty *)
apply (clarsimp simp: mut_m.gc_W_empty_mut_inv_def)
apply (rule conjI)
 apply (clarsimp simp: WL_def)
apply clarsimp
apply (drule mp)
 apply blast
apply (clarsimp simp: WL_def)
apply (rename_tac xa)
apply (rule_tac x=xa in exI)
apply clarsimp

(* hs_get_work_done: no_grey_refs *)
apply (simp add: no_grey_refs_def)
apply (simp add: no_grey_refs_def)

done

(*>*)

subsection\<open>Sweep loop invariants\<close>

locset_definition "sweep_loop_locs = prefixed ''sweep_loop''"

inv_definition (in gc) sweep_loop_invL :: "('field, 'mut, 'ref) gc_pred" where
  "sweep_loop_invL =
   (at_gc ''sweep_loop_check''        ( (\<^bold>\<not>(NULL gc_mark) \<^bold>\<longrightarrow> (\<lambda>s. obj_at (\<lambda>obj. Some (obj_mark obj) = gc_mark s) (gc_tmp_ref s) s))
                                      \<^bold>\<and> (  NULL gc_mark \<^bold>\<longrightarrow> valid_ref \<^bold>$ gc_tmp_ref \<^bold>\<longrightarrow> marked \<^bold>$ gc_tmp_ref ) )
  \<^bold>\<and> at_gc ''sweep_loop_free''         ( \<^bold>\<not>(NULL gc_mark) \<^bold>\<and> the \<circ> gc_mark \<^bold>\<noteq> gc_fM \<^bold>\<and> (\<lambda>s. obj_at (\<lambda>obj. Some (obj_mark obj) = gc_mark s) (gc_tmp_ref s) s) )
  \<^bold>\<and> at_gc ''sweep_loop_ref_done''     (valid_ref \<^bold>$ gc_tmp_ref \<^bold>\<longrightarrow> marked \<^bold>$ gc_tmp_ref)
  \<^bold>\<and> atS_gc sweep_loop_locs            (\<^bold>\<forall>r. \<^bold>\<not>(\<langle>r\<rangle> \<^bold>\<in> gc_refs) \<^bold>\<longrightarrow> valid_ref r \<^bold>\<longrightarrow> marked r)
  \<^bold>\<and> atS_gc black_heap_locs            (\<^bold>\<forall>r. valid_ref r \<^bold>\<longrightarrow> marked r)
  \<^bold>\<and> atS_gc (prefixed ''sweep_loop_'' - { ''sweep_loop_choose_ref'' }) (gc_tmp_ref \<^bold>\<in> gc_refs))"
(*<*)

lemma (in gc) sweep_loop_invL_eq_imp:
  "eq_imp (\<lambda>(_::unit) (s :: ('field, 'mut, 'ref) gc_pred_state). (AT s gc, s\<down> gc, sys_fM s\<down>, Option.map_option obj_mark \<circ> sys_heap s\<down>))
          sweep_loop_invL"
apply (clarsimp simp: eq_imp_def inv)
apply (rename_tac s s')
apply (subgoal_tac "\<forall>r. valid_ref r s\<down> \<longleftrightarrow> valid_ref r s'\<down>")
 apply (subgoal_tac "\<forall>P r. obj_at (\<lambda>obj. P (obj_mark obj)) r s\<down> \<longleftrightarrow> obj_at (\<lambda>obj. P (obj_mark obj)) r s'\<down>")
  apply (frule_tac x="\<lambda>mark. Some mark = gc_mark s'\<down>" in spec)
  apply (frule_tac x="\<lambda>mark. mark = sys_fM s'\<down>" in spec)
  apply clarsimp
 apply (clarsimp simp: fun_eq_iff split: obj_at_splits)
 apply (rename_tac r)
 apply ( (drule_tac x=r in spec)+, auto)[1]
apply (clarsimp simp: fun_eq_iff split: obj_at_splits)
apply (rename_tac r)
apply (drule_tac x=r in spec, auto)[1]
apply (metis map_option_eq_Some)+
done

lemmas gc_sweep_loop_invL_niE[nie] =
  iffD1[OF gc.sweep_loop_invL_eq_imp[simplified eq_imp_simps, rule_format, unfolded conj_explode, rule_format], rotated -1]

lemma (in gc) sweep_loop_invL[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> phase_invL \<^bold>\<and> sweep_loop_invL \<^bold>\<and> tso_lock_invL
         \<^bold>\<and> LSTP (phase_rel_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     gc
   \<lbrace> sweep_loop_invL \<rbrace>"
apply (vcg_jackhammer simp: no_grey_refs_def phase_rel_inv_def phase_rel_def)

apply (rename_tac s s' x)
apply (case_tac "x \<in> gc_refs s\<down>")
 apply force
apply blast

apply (clarsimp split: obj_at_splits)
done

lemma sweep_loop_sweep_locs[iff]:
  "sweep_loop_locs \<subseteq> sweep_locs"
by (auto simp: sweep_loop_locs_def sweep_locs_def intro: append_prefixD)

lemma sweep_locs_subseteq_fM_tso_empty_locs[iff]:
  "sweep_locs \<subseteq> fM_tso_empty_locs"
by (auto simp: sweep_locs_def fM_tso_empty_locs_def)

lemma sweep_loop_locs_fM_eq_locs:
  "sweep_loop_locs \<subseteq> fM_eq_locs"
by (auto simp: sweep_loop_locs_def fM_eq_locs_def sweep_locs_def)

lemma sweep_loop_locs_fA_eq_locs:
  "sweep_loop_locs \<subseteq> fA_eq_locs"
apply (simp add: sweep_loop_locs_def fA_eq_locs_def sweep_locs_def)
apply (intro subset_insertI2)
apply (auto intro: append_prefixD)
done

lemma black_heap_locs_subseteq_fM_tso_empty_locs[iff]:
  "black_heap_locs \<subseteq> fM_tso_empty_locs"
by (auto simp: black_heap_locs_def fM_tso_empty_locs_def)

lemma black_heap_locs_fM_eq_locs:
  "black_heap_locs \<subseteq> fM_eq_locs"
by (simp add: black_heap_locs_def fM_eq_locs_def)

lemma black_heap_locs_fA_eq_locs:
  "black_heap_locs \<subseteq> fA_eq_locs"
by (simp add: black_heap_locs_def fA_eq_locs_def sweep_locs_def)

lemma (in gc) fM_invL_tso_emptyD:
  "\<lbrakk> atS gc ls s; fM_fA_invL s; ls \<subseteq> fM_tso_empty_locs \<rbrakk> \<Longrightarrow> tso_pending_fM gc s\<down> = []"
by (auto simp: fM_fA_invL_def dest: atS_mono)

lemma gc_sweep_loop_invL_locsE[rule_format]:
  "(atS gc (sweep_locs \<union> black_heap_locs) s \<longrightarrow> False) \<Longrightarrow> gc.sweep_loop_invL s"
apply (simp add: gc.sweep_loop_invL_def atS_un)
apply (auto simp: loc atS_simps dest: atS_mono)
apply (clarsimp simp: atS_def)
apply (rename_tac x)
apply (drule_tac x=x in bspec)
apply (auto simp: sweep_locs_def intro: append_prefixD)
done

lemma (in sys) gc_sweep_loop_invL[intro]:
  "\<lbrace> gc.fM_fA_invL \<^bold>\<and> gc.gc_W_empty_invL \<^bold>\<and> gc.handshake_invL \<^bold>\<and> gc.phase_invL \<^bold>\<and> gc.sweep_loop_invL
       \<^bold>\<and> LSTP (mutators_phase_inv \<^bold>\<and> tso_writes_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> gc.sweep_loop_invL \<rbrace>"
apply vcg_nihe
apply vcg_ni
apply (clarsimp simp: do_write_action_def
               split: mem_write_action.splits
                elim: gc_sweep_loop_invL_niE) (* FIXME elimination rule using tso_writes_inv *)

(* mw_Mark *)
apply (rename_tac s s' p ws ref bool)
apply (rule gc_sweep_loop_invL_locsE)
apply (simp only: gc.gc_W_empty_invL_def no_grey_refs_locs_def cong del: atS_state_cong)
apply (clarsimp simp: atS_un)
apply (erule disjE)
 apply clarsimp
 apply (drule (1) no_grey_refs_no_pending_marks)
 apply (clarsimp simp: filter_empty_conv)
 apply (drule_tac x=p in spec)
 apply fastforce
apply clarsimp
apply (drule (1) no_grey_refs_no_pending_marks)
apply (clarsimp simp: filter_empty_conv)
apply (drule_tac x=p in spec)
apply fastforce

(* mw_Mutate *)
apply (erule gc_sweep_loop_invL_niE, simp_all add: fun_eq_iff)[1] (* FIXME should be automatic *)

(* mw_fA *)
apply (erule gc_sweep_loop_invL_niE, simp_all add: fun_eq_iff)[1] (* FIXME should be automatic *)

(* mw_fM *)
apply (rename_tac s s' p ws bool)
apply (rule gc_sweep_loop_invL_locsE)
apply (case_tac p, clarsimp+)
apply (drule (1) gc.fM_invL_tso_emptyD)
apply simp_all

(* mv_Phase *)
apply (erule gc_sweep_loop_invL_niE, simp_all add: fun_eq_iff)[1] (* FIXME should be automatic *)

done (* FIXME weird: expect more aggressive use of gc_sweep_loop_invL_niE by clarsimp *)

lemma (in mut_m) gc_sweep_loop_invL[intro]:
  "\<lbrace> gc.fM_fA_invL \<^bold>\<and> gc.handshake_invL \<^bold>\<and> gc.sweep_loop_invL
       \<^bold>\<and> LSTP (mutators_phase_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> gc.sweep_loop_invL \<rbrace>"
apply vcg_nihe
apply vcg_ni
apply (clarsimp simp: inv gc.sweep_loop_invL_def gc.fM_fA_invL_def)
apply (intro allI conjI impI)
 (* four subgoals *)
 apply ((erule (1) thin_locs)+)[1]
 apply (force simp: loc)

 apply ((erule (1) thin_locs)+)[1]
 apply (force simp: loc)

 apply (rename_tac s s' ra)
 apply (drule mp, erule atS_mono[OF _ sweep_loop_locs_fA_eq_locs])
 apply (drule mp, erule atS_mono[OF _ sweep_loop_locs_fM_eq_locs])
 apply force

 apply (rename_tac s s' ra)
 apply (drule mp, erule atS_mono[OF _ black_heap_locs_fA_eq_locs])
 apply (drule mp, erule atS_mono[OF _ black_heap_locs_fM_eq_locs])
 apply force
done (* FIXME crappy split *)

lemma (in gc) sys_phase_inv[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> handshake_invL \<^bold>\<and> obj_fields_marked_invL
       \<^bold>\<and> phase_invL \<^bold>\<and> sweep_loop_invL
       \<^bold>\<and> LSTP (phase_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_writes_inv) \<rbrace>
     gc
   \<lbrace> LSTP sys_phase_inv \<rbrace>"
apply vcg_jackhammer
apply ( (erule black_heap_no_greys, simp)
      | fastforce dest!: phase_rel_invD simp: phase_rel_def filter_empty_conv )+
done

lemma (in gc) no_black_refs_sweep_loop_free[simp]:
  "no_black_refs s \<Longrightarrow> no_black_refs (s(sys := s sys\<lparr>heap := (sys_heap s)(gc_tmp_ref s := None)\<rparr>))"
by (simp add: no_black_refs_def)

lemma (in gc) no_black_refs_load_W[simp]:
  "\<lbrakk> no_black_refs s; gc_W s = {} \<rbrakk>
     \<Longrightarrow> no_black_refs (s(gc := s gc\<lparr>W := sys_W s\<rparr>, sys := s sys\<lparr>W := {}\<rparr>))"
by (simp add: no_black_refs_def)

lemma marked_deletions_sweep_loop_free[simp]:
  "\<lbrakk> mut_m.marked_deletions m s; mut_m.reachable_snapshot_inv m s; no_grey_refs s; white r s \<rbrakk>
     \<Longrightarrow> mut_m.marked_deletions m (s(sys := s sys\<lparr>heap := (sys_heap s)(r := None)\<rparr>))"
apply (clarsimp simp: mut_m.marked_deletions_def split: mem_write_action.splits)
apply (rename_tac ref field option)
apply (drule_tac x="mw_Mutate ref field option" in spec)
apply clarsimp
apply (clarsimp simp: obj_at_field_on_heap_def split: option.splits)
 apply (rule conjI)
  apply (clarsimp simp: mut_m.reachable_snapshot_inv_def)
  apply (drule spec[where x=r], clarsimp simp: in_snapshot_def)
  apply (drule mp, auto simp: mut_m.reachable_def mut_m.tso_write_refs_def split: mem_write_action.splits)[1] (* FIXME rule *)
  apply (drule grey_protects_whiteD)
  apply (clarsimp simp: no_grey_refs_def)
 apply clarsimp
apply (rule conjI)
 apply clarsimp
apply clarsimp
apply (rule conjI)
 apply (clarsimp simp: mut_m.reachable_snapshot_inv_def)
 apply (drule spec[where x=r], clarsimp simp: in_snapshot_def)
 apply (drule mp, auto simp: mut_m.reachable_def mut_m.tso_write_refs_def split: mem_write_action.splits)[1] (* FIXME rule *)
 apply (drule grey_protects_whiteD)
 apply (clarsimp simp: no_grey_refs_def)
apply (clarsimp split: obj_at_splits)
done

lemma (in gc) mutator_phase_inv[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> handshake_invL \<^bold>\<and> obj_fields_marked_invL \<^bold>\<and> sweep_loop_invL
       \<^bold>\<and> gc_mark.mark_object_invL
       \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> tso_writes_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     gc
   \<lbrace> LSTP (mut_m.mutator_phase_inv m) \<rbrace>"
apply vcg_jackhammer
apply (simp_all add: mutator_phase_inv_aux_case split: handshake_phase.splits)

(* sweep_loop_free *)
apply (intro allI conjI impI)
 apply (drule mut_m.handshake_phase_invD[where m=m], clarsimp simp: hp_step_rel_def)
apply (rule mut_m.reachable_snapshot_inv_sweep_loop_free, simp_all)

(* ''mark_loop_get_work_load_W'' *)
apply clarsimp
apply (drule spec[where x=m])
apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def) (* FIXME rule *)

(* mark_loop_blacken *)
apply (drule spec[where x=m])
apply clarsimp
apply (intro allI conjI impI)
 apply clarsimp
 apply (drule mut_m.handshake_phase_invD[where m=m], clarsimp simp: hp_step_rel_def)
apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def)
apply (rename_tac s s' x)
apply (drule_tac x=x in spec)
apply clarsimp
apply (rename_tac s s' x xa)
apply (drule_tac x=xa in spec)
apply clarsimp
apply (rule obj_fields_marked_inv_has_white_path_to_blacken, simp_all)[1]

(* mark_loop_mo_co_mark *)
apply clarsimp
apply (erule mut_m.reachable_snapshot_inv_mo_co_mark) (* FIXME hoist to the top level *)
apply blast

(* mark_loop_get_roots_load_W *)
apply clarsimp
apply (drule spec[where x=m])
apply (clarsimp simp: mut_m.reachable_snapshot_inv_def in_snapshot_def grey_protects_white_def) (* FIXME rule *)

done

lemma (in mut_m) sys_phase_inv[intro]:
  "\<lbrace> handshake_invL
             \<^bold>\<and> mark_object_invL
             \<^bold>\<and> mut_get_roots.mark_object_invL m
             \<^bold>\<and> mut_store_del.mark_object_invL m
             \<^bold>\<and> mut_store_ins.mark_object_invL m
        \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> phase_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP sys_phase_inv \<rbrace>"
apply (vcg_jackhammer simp: fA_rel_inv_def fM_rel_inv_def)
apply (simp_all add: sys_phase_inv_aux_case heap_colours_colours
              split: handshake_phase.splits if_splits)

(* alloc *)
subgoal by (clarsimp simp: fA_rel_def fM_rel_def no_black_refs_def
               dest!: handshake_phase_invD phase_rel_invD
               split: handshake_phase.splits)

(* store_ins_mo_co_mark *)
subgoal by (fastforce simp: fA_rel_def fM_rel_def hp_step_rel_def
                dest!: handshake_phase_invD phase_rel_invD)
subgoal
  apply (drule spec[where x=m])
  apply (rule conjI)
   apply (clarsimp simp: hp_step_rel_def phase_rel_def conj_disj_distribR[symmetric]
                  dest!: handshake_phase_invD phase_rel_invD)
   apply (elim disjE, simp_all add: no_grey_refs_not_rootD)[1]
  apply (clarsimp simp: hp_step_rel_def phase_rel_def
                 dest!: handshake_phase_invD phase_rel_invD)
  apply (elim disjE, simp_all add: no_grey_refs_not_rootD)[1]
  apply clarsimp
  apply (elim disjE, simp_all add: no_grey_refs_not_rootD filter_empty_conv)[1]
  apply fastforce
  done

(* store_del_mo_co_unlock *)
subgoal by (fastforce simp: fA_rel_def fM_rel_def hp_step_rel_def
                dest!: handshake_phase_invD phase_rel_invD)

subgoal
  apply (drule spec[where x=m])
  apply (rule conjI)
   apply (clarsimp simp: hp_step_rel_def phase_rel_def conj_disj_distribR[symmetric] no_grey_refs_not_rootD
                  dest!: handshake_phase_invD phase_rel_invD)
  apply (clarsimp simp: hp_step_rel_def phase_rel_def
                 dest!: handshake_phase_invD phase_rel_invD)
  apply (elim disjE, simp_all add: no_grey_refs_not_rootD)[1]
  apply clarsimp
  apply (elim disjE, simp_all add: no_grey_refs_not_rootD filter_empty_conv)[1]
  apply fastforce
  done

(* hs_get_roots_done *)
subgoal by (clarsimp simp: hp_step_rel_def
               dest!: handshake_phase_invD phase_rel_invD)
subgoal by (clarsimp simp: hp_step_rel_def
               dest!: handshake_phase_invD phase_rel_invD)
subgoal by (clarsimp simp: hp_step_rel_def
               dest!: handshake_phase_invD phase_rel_invD)
subgoal by (clarsimp simp: hp_step_rel_def
               dest!: handshake_phase_invD phase_rel_invD)
subgoal
  apply (clarsimp simp: hp_step_rel_def phase_rel_def filter_empty_conv
               dest!: handshake_phase_invD phase_rel_invD)
  apply auto
  done

(* hs_get_roots_loop_mo_co_mark *)
subgoal by (clarsimp simp: hp_step_rel_def
                 dest!: handshake_phase_invD phase_rel_invD)
subgoal
  apply (clarsimp simp: hp_step_rel_def phase_rel_def filter_empty_conv
                 dest!: handshake_phase_invD phase_rel_invD)
  apply auto
  done

(* hs_get_work_done *)
subgoal by (clarsimp simp: hp_step_rel_def
               dest!: handshake_phase_invD phase_rel_invD)
subgoal by (clarsimp simp: hp_step_rel_def
               dest!: handshake_phase_invD phase_rel_invD)
subgoal by (clarsimp simp: hp_step_rel_def
               dest!: handshake_phase_invD phase_rel_invD)
subgoal by (clarsimp simp: hp_step_rel_def
               dest!: handshake_phase_invD phase_rel_invD)
subgoal
  apply (clarsimp simp: hp_step_rel_def phase_rel_def filter_empty_conv
               dest!: handshake_phase_invD phase_rel_invD)
  apply auto
  done
done

lemma no_grey_refs_no_marks[simp]:
  "\<lbrakk> no_grey_refs s; valid_W_inv s \<rbrakk> \<Longrightarrow> \<not>sys_mem_write_buffers p s = mw_Mark r fl # ws"
by (auto simp: no_grey_refs_def)

context sys
begin

lemma black_heap_dequeue_mark[iff]:
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mark r fl # ws; black_heap s; valid_W_inv s \<rbrakk>
   \<Longrightarrow> black_heap (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (obj_mark_update (\<lambda>_. fl)) (sys_heap s r)), mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))"
by (auto simp: black_heap_def)

lemma black_heap_dequeue_ref[iff]:
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mutate r f r' # ws; black_heap s \<rbrakk>
     \<Longrightarrow> black_heap (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := r')\<rparr>) (sys_heap s r)),
                                   mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))"
by (simp add: black_heap_def black_def)

lemma white_heap_dequeue_fM[iff]:
  "black_heap s\<down>
     \<Longrightarrow> white_heap (s\<down>(sys := s\<down> sys\<lparr>fM := \<not> sys_fM s\<down>, mem_write_buffers := (mem_write_buffers (s\<down> sys))(gc := ws)\<rparr>))"
by (auto simp: black_heap_def white_heap_def)

lemma black_heap_dequeue_fM[iff]:
  "\<lbrakk> white_heap s\<down>; no_grey_refs s\<down> \<rbrakk>
     \<Longrightarrow> black_heap (s\<down>(sys := s\<down> sys\<lparr>fM := \<not> sys_fM s\<down>, mem_write_buffers := (mem_write_buffers (s\<down> sys))(gc := ws)\<rparr>))"
by (auto simp: black_heap_def white_heap_def no_grey_refs_def)

lemma white_heap_dequeue_ref[iff]:
  "\<lbrakk> sys_mem_write_buffers p s = mw_Mutate r f r' # ws; white_heap s \<rbrakk>
     \<Longrightarrow> white_heap (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := r')\<rparr>) (sys_heap s r)),
                                   mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))"
by (simp add: white_heap_def)

lemma (in sys) sys_phase_inv[intro]:
  "\<lbrace> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> phase_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> tso_writes_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> LSTP sys_phase_inv \<rbrace>"
by (vcg_jackhammer simp: fA_rel_inv_def fM_rel_inv_def p_not_sys)
   (clarsimp simp: do_write_action_def sys_phase_inv_aux_case
               split: mem_write_action.splits handshake_phase.splits if_splits;
    erule disjE; clarsimp simp: fA_rel_def fM_rel_def; fail)

end

lemma valid_W_inv_unlockE[iff]:
  "\<lbrakk> sys_mem_lock s = Some p; sys_mem_write_buffers p s = [];
     \<And>r. r \<in> ghost_honorary_grey (s p) \<Longrightarrow> marked r s;
     valid_W_inv s
   \<rbrakk> \<Longrightarrow> valid_W_inv (s(sys := mem_lock_update Map.empty (s sys)))"
unfolding valid_W_inv_def by clarsimp (metis emptyE empty_set)

lemma valid_W_inv_mark:
  "\<lbrakk> sys_mem_lock s = Some p; white w s; valid_W_inv s \<rbrakk>
     \<Longrightarrow> w \<in> ghost_honorary_grey (s p) \<or> (\<forall>q. w \<notin> WL q s)"
by (metis Un_iff WL_def marked_not_white option.inject valid_W_invD(1) valid_W_invD3(2))

lemma (in gc) valid_W_inv[intro]:
  notes valid_W_invD2[dest!, simp]
  notes valid_W_invD3[dest, simp]
  shows
  "\<lbrace> fM_invL \<^bold>\<and> gc_mark.mark_object_invL \<^bold>\<and> gc_W_empty_invL
       \<^bold>\<and> obj_fields_marked_invL
       \<^bold>\<and> sweep_loop_invL \<^bold>\<and> tso_lock_invL
       \<^bold>\<and> LSTP (tso_writes_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     gc
   \<lbrace> LSTP valid_W_inv \<rbrace>"
apply (vcg_jackhammer simp: fM_rel_def)

(* sweep loop free: what's with the case splitting? *)
subgoal for s s'
  apply (subst valid_W_inv_def)
  apply (intro allI conjI impI; clarsimp simp: p_not_sys split: if_splits)
       apply blast
      apply blast
     apply blast
    apply blast
   apply (rename_tac p x)
   apply (case_tac p; auto)
  apply (rename_tac p)
  apply (case_tac p; force simp: no_grey_refs_def)
  done

(* mark_loop_get_work_load_W *)
subgoal by (subst valid_W_inv_def) (auto simp: all_conj_distrib split: process_name.splits)

(* mark_loop_blacken *)
subgoal by (subst valid_W_inv_def) (auto simp: all_conj_distrib)

(* mark_loop_mo_co_W *)
subgoal
  apply (subst valid_W_inv_def)
  apply clarsimp
  apply blast
  done

(* mark_loop_mo_co_unlock *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
        apply blast
       apply blast
      apply (auto iff: p_not_sys split: if_splits)[1]
     apply blast
    apply blast
   apply blast
  apply force
  done

(* mark_loop_mo_co_mark *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
               apply blast
              apply blast
             apply blast
            apply (frule (2) valid_W_inv_mark; auto)[1]
           apply (clarsimp dest!: valid_W_invD(1) split: obj_at_splits) (* FIXME want a cheaper contradiction between white and marked *)
          apply (clarsimp dest!: valid_W_invD(1) split: obj_at_splits)
         apply (clarsimp dest!: valid_W_invD(1) split: obj_at_splits)
        apply blast
       apply blast
      apply blast
     apply blast
    apply blast
   apply blast
  apply force
  done

(* mark_loop_mo_co_lock *)
subgoal
  apply (subst valid_W_inv_def)
  apply (auto simp: all_conj_distrib)
  done

(* ''mark_loop_get_roots_load_W'' *)
subgoal
  apply (subst valid_W_inv_def)
  apply (auto simp: all_conj_distrib split: process_name.splits)
  done

done

lemma (in mut_m) valid_W_inv[intro]:
  notes valid_W_invD2[dest!, simp]
  notes valid_W_invD3[dest, simp]
  shows
  "\<lbrace> handshake_invL \<^bold>\<and> mark_object_invL \<^bold>\<and> tso_lock_invL
      \<^bold>\<and> mut_get_roots.mark_object_invL m
      \<^bold>\<and> mut_store_del.mark_object_invL m
      \<^bold>\<and> mut_store_ins.mark_object_invL m
       \<^bold>\<and> LSTP (fM_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> tso_writes_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP valid_W_inv \<rbrace>"
apply (vcg_jackhammer simp: fM_rel_inv_def fM_rel_def)

(* alloc *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI; auto)
  done

(* store ins mo co W *)
subgoal
  apply (subst valid_W_inv_def)
  apply clarsimp
  apply blast
  done

(* store ins mo co unlock *)
subgoal for s s' y
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
        subgoal by blast
       subgoal by blast
      subgoal for p x by (case_tac "p = mutator m"; force split: if_splits)
     subgoal by blast
    subgoal by blast
   subgoal by blast
  subgoal by force
  done

(* store ins mo co mark *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
               subgoal by blast
              subgoal by blast
             subgoal by blast
            subgoal by (blast dest: valid_W_inv_mark)
           subgoal by (clarsimp dest!: valid_W_invD(1) split: obj_at_splits) (* FIXME want a cheaper contradiction between white and marked *)
          subgoal by (clarsimp dest!: valid_W_invD(1) split: obj_at_splits)
         subgoal by (clarsimp dest!: valid_W_invD(1) split: obj_at_splits)
        subgoal by blast
       subgoal by blast
      subgoal by blast
     subgoal by blast
    subgoal by blast
   subgoal by blast
  subgoal by force
  done

(* store ins mo co lock *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
          subgoal by blast
         subgoal by blast
        subgoal by force
       subgoal by blast
      subgoal by blast
     subgoal by blast
    subgoal by force
   subgoal by blast
  subgoal by force
  done

(* store del mo co W *)
subgoal
  apply (subst valid_W_inv_def)
  apply clarsimp
  apply blast
  done

(* store del mo co unlock *)
subgoal for s s' y
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
        subgoal by blast
       subgoal by blast
      subgoal for p x by (cases "p = mutator m") (auto split: if_splits)
     subgoal by blast
    subgoal by blast
   subgoal by blast
  subgoal by force
  done

(* store del mo co mark *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
               subgoal by blast
              subgoal by blast
             subgoal by blast
            subgoal by (frule (2) valid_W_inv_mark; auto)
           subgoal by (clarsimp dest!: valid_W_invD(1) split: obj_at_splits) (* FIXME want a cheaper contradiction between white and marked *)
          subgoal by (clarsimp dest!: valid_W_invD(1) split: obj_at_splits)
         subgoal by (clarsimp dest!: valid_W_invD(1) split: obj_at_splits)
        subgoal by blast
       subgoal by blast
      subgoal by blast
     subgoal by blast
    subgoal by blast
   subgoal by blast
  subgoal by force
  done

(* store del mo co lock *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
          subgoal by blast
         subgoal by blast
        subgoal by force
       subgoal by blast
      subgoal by blast
     subgoal by blast
    subgoal by force
   subgoal by blast
  subgoal by force
  done

(* get roots done *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
            subgoal by blast
           subgoal by blast
          subgoal by blast
         subgoal by blast
        subgoal by (auto split: if_splits obj_at_splits process_name.splits)
       subgoal by blast
      subgoal by blast
     subgoal by blast
    subgoal by (auto split: if_splits obj_at_splits process_name.splits)
   subgoal by blast
  subgoal by blast
  done

(* hs get roots loop mo co W *)
subgoal
  apply (subst valid_W_inv_def)
  apply clarsimp
  apply blast
  done

(* hs get roots loop mo co unlock *)
subgoal for s s' y
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
        subgoal by blast
       subgoal by blast
      subgoal for p x by (cases "p = mutator m") (auto split: if_splits)
     subgoal by blast
    subgoal by blast
   subgoal by blast
  subgoal by force
  done

(* hs get roots loop mo co mark *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
               subgoal by blast
              subgoal by blast
             subgoal by blast
            subgoal by (frule (2) valid_W_inv_mark; auto)
           subgoal by (clarsimp dest!: valid_W_invD(1) split: obj_at_splits) (* FIXME want a cheaper contradiction between white and marked *)
          subgoal by (clarsimp dest!: valid_W_invD(1) split: obj_at_splits)
         subgoal by (clarsimp dest!: valid_W_invD(1) split: obj_at_splits)
        subgoal by blast
       subgoal by blast
      subgoal by blast
     subgoal by blast
    subgoal by blast
   subgoal by blast
  subgoal by force
  done

(* hs get roots loop mo co lock *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
          subgoal by blast
         subgoal by blast
        subgoal by force
       subgoal by blast
      subgoal by blast
     subgoal by blast
    subgoal by force
   subgoal by blast
  subgoal by force
  done

(* hs get work done *)
subgoal
  apply (subst valid_W_inv_def)
  apply (clarsimp simp: all_conj_distrib)
  apply (intro allI conjI impI)
            subgoal by blast
           subgoal by blast
          subgoal by blast
         subgoal by blast
        subgoal by (auto split: if_splits obj_at_splits process_name.splits)
       subgoal by blast
      subgoal by blast
     subgoal by blast
    subgoal by force
   subgoal by blast
  subgoal by blast
  done

done

lemma (in sys) valid_W_inv[intro]:
  notes valid_W_invD2[dest!, simp]
  notes valid_W_invD3[dest, simp]
  notes valid_W_invD4[dest!, simp]
  notes o_def[simp]
  shows
  "\<lbrace> LSTP (fM_rel_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> tso_writes_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> LSTP valid_W_inv \<rbrace>"
apply vcg_jackhammer
apply (subst valid_W_inv_def)
apply (clarsimp simp: do_write_action_def all_conj_distrib fM_rel_inv_def
               split: mem_write_action.splits)

(* mw_Mark *)
subgoal
  apply (intro allI conjI impI)
             apply blast
            apply blast
           apply blast
          apply blast
         apply blast
        apply force
       apply blast
      apply blast
     apply blast
    apply (force simp: filter_empty_conv)
   apply force
  apply blast
  done

(* mw_Mutate, mw_fA *)
subgoal by (intro allI conjI impI; auto)
subgoal by (intro allI conjI impI; auto)

(* mw_fM *)
subgoal for s s' p ws bool
  apply (clarsimp simp: fM_rel_def)
  apply (rule disjE[OF iffD1[OF p_not_sys]], assumption)
   prefer 2
   apply clarsimp
  apply (case_tac "sys_ghost_handshake_phase s\<down> = hp_Idle"; clarsimp)
  apply (intro allI conjI impI)
            subgoal by blast
           subgoal by blast
          subgoal by blast
         subgoal by blast
        subgoal by blast
       subgoal by force
      subgoal by (force dest: no_grey_refs_no_pending_marks)
     subgoal by blast
    subgoal by force
   subgoal by (fastforce dest: no_grey_refs_no_pending_marks)
  subgoal by (fastforce dest: no_grey_refs_no_pending_marks)
  done

(* mw_Phase *)
apply (intro allI conjI impI; auto)
done

lemma (in gc) strong_tricolour_inv[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> gc_mark.mark_object_invL \<^bold>\<and> obj_fields_marked_invL \<^bold>\<and> sweep_loop_invL
       \<^bold>\<and> LSTP (strong_tricolour_inv \<^bold>\<and> tso_writes_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     gc
   \<lbrace> LSTP strong_tricolour_inv \<rbrace>"
apply (vcg_jackhammer simp: strong_tricolour_inv_def)
apply (fastforce elim!: obj_fields_marked_inv_blacken)
done

lemma (in mut_m) strong_tricolour[intro]:
  "\<lbrace> mark_object_invL
      \<^bold>\<and> mut_get_roots.mark_object_invL m
      \<^bold>\<and> mut_store_del.mark_object_invL m
      \<^bold>\<and> mut_store_ins.mark_object_invL m
      \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> strong_tricolour_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> valid_refs_inv) \<rbrace>
     mutator m
   \<lbrace> LSTP strong_tricolour_inv \<rbrace>"
apply (vcg_jackhammer simp: strong_tricolour_inv_def fA_rel_inv_def fM_rel_inv_def)

apply (drule handshake_phase_invD)
apply (clarsimp simp: sys_phase_inv_aux_case
               split: handshake_phase.splits if_splits)

 apply (blast dest: heap_colours_colours)
 apply (blast dest: heap_colours_colours)

 apply (clarsimp simp: fA_rel_def fM_rel_def no_black_refs_def) (* FIXME rule *)

 apply (drule_tac x=m in spec)
 apply (clarsimp simp: hp_step_rel_def)
 apply (elim disjE, simp_all)
  apply (auto dest: no_black_refsD)[1]
  apply (auto dest: no_black_refsD)[1]

  apply (clarsimp simp: fA_rel_def fM_rel_def)
  apply (clarsimp split: obj_at_splits)

 apply (drule spec[where x=m])
 apply (clarsimp simp: hp_step_rel_def)
 apply (elim disjE; force simp: fA_rel_def fM_rel_def split: obj_at_splits)

 apply (drule spec[where x=m])
 apply (clarsimp simp: hp_step_rel_def)
 apply (elim disjE; force simp: fA_rel_def fM_rel_def split: obj_at_splits)
done

lemma (in sys) strong_tricolour_inv[intro]:
  "\<lbrace> LSTP (fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> strong_tricolour_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> tso_writes_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> LSTP strong_tricolour_inv \<rbrace>"
apply (vcg_jackhammer simp: strong_tricolour_inv_def p_not_sys)
apply (clarsimp simp: do_write_action_def fM_rel_inv_def
               split: mem_write_action.splits)
apply (rename_tac ref field)

(* mw_Mark *)
subgoal for s s' p ws x xa ref field
  apply (frule (1) valid_W_invD2)
  apply clarsimp
  apply (case_tac "x = ref", simp_all)
  apply (clarsimp simp: grey_def WL_def)
  done

(* mw_Mutate *)
apply (elim disjE, simp_all)
apply (clarsimp simp: points_to_mw_Mutate)
apply (elim disjE, simp_all)
apply (rename_tac s s' ws x xa ref field option m)
apply (drule_tac m=m in mut_m.handshake_phase_invD)
apply (frule_tac x=m in spec)
apply (clarsimp simp: mutator_phase_inv_aux_case hp_step_rel_def
               split: handshake_phase.splits)

 apply (elim disjE, simp_all split: if_splits)
  apply (blast dest!: heap_colours_colours)
  apply (blast dest!: heap_colours_colours)

  apply (drule_tac x=m in spec)
  apply (clarsimp simp: no_black_refs_def)

  apply (drule_tac x=m in spec)
  apply (clarsimp simp: no_black_refsD)

  (* FIXME split less *)
  apply (drule_tac x=m in spec)
  apply (clarsimp simp: mut_m.marked_insertions_def)
  apply (drule_tac x="mw_Mutate x field (Some xa)" in spec)
  apply (clarsimp dest!: marked_not_white)

  apply (drule_tac x=m in spec)
  apply (clarsimp simp: mut_m.marked_insertions_def)
  apply (drule_tac x="mw_Mutate x field (Some xa)" in spec)
  apply (clarsimp dest!: marked_not_white)

  apply (drule_tac x=m in spec)
  apply (clarsimp simp: mut_m.marked_insertions_def)
  apply (drule_tac x="mw_Mutate x field (Some xa)" in spec)
  apply (clarsimp dest!: marked_not_white)

  apply (drule_tac x=m in spec)
  apply (clarsimp simp: mut_m.marked_insertions_def)
  apply (drule_tac x="mw_Mutate x field (Some xa)" in spec)
  apply (clarsimp dest!: marked_not_white)

  apply (drule_tac x=m in spec)
  apply (clarsimp simp: mut_m.marked_insertions_def)
  apply (drule_tac x="mw_Mutate x field (Some xa)" in spec)
  apply (clarsimp dest!: marked_not_white)

  apply clarsimp
  apply (elim disjE, simp_all split: if_splits)
   apply (blast dest!: heap_colours_colours)
   apply (blast dest!: heap_colours_colours)

   apply (drule_tac x=m in spec)
   apply (clarsimp simp: no_black_refs_def)

   apply (drule_tac x=m in spec)
   apply (clarsimp simp: mut_m.marked_insertions_def)
   apply (drule_tac x="mw_Mutate x field (Some xa)" in spec)
   apply (clarsimp dest!: marked_not_white)

   apply (drule_tac x=m in spec)
   apply (clarsimp simp: mut_m.marked_insertions_def)
   apply (drule_tac x="mw_Mutate x field (Some xa)" in spec)
   apply (clarsimp dest!: marked_not_white)

(* mw_fM *)
apply (rename_tac s s' p ws x xa bool)
apply (erule disjE)
 apply (clarsimp simp: fM_rel_def black_heap_def split: if_splits)
  apply ( (drule_tac x=x in spec)+ )[1]
  apply (frule colours_distinct)
  apply (clarsimp split: obj_at_splits)
 apply (clarsimp simp: white_heap_def)
 apply ( (drule_tac x=xa in spec)+ )[1]
 apply (clarsimp split: obj_at_splits)
apply fastforce

done

text\<open>Remaining non-interference proofs.\<close>

lemma marked_insertionsD:
  "\<lbrakk> sys_mem_write_buffers (mutator m) s = mw_Mutate r f (Some r') # ws; mut_m.marked_insertions m s \<rbrakk>
     \<Longrightarrow> marked r' s"
by (clarsimp simp: mut_m.marked_insertions_def)

lemma mut_hs_get_roots_loop_locs_subseteq_hs_get_roots:
  "mut_hs_get_roots_loop_locs \<subseteq> prefixed ''hs_get_roots_''"
by (auto simp: mut_hs_get_roots_loop_locs_def intro: append_prefixD)

lemma mut_m_handshake_invL_get_roots:
  "\<lbrakk> mut_m.handshake_invL m s; atS (mutator m) mut_hs_get_roots_loop_locs s \<rbrakk>
     \<Longrightarrow> sys_handshake_type s\<down> = ht_GetRoots \<and> sys_handshake_pending m s\<down>"
unfolding mut_m.handshake_invL_def
 apply (elim conjE)
 apply (drule mp, erule (1) atS_mono[OF _ mut_hs_get_roots_loop_locs_subseteq_hs_get_roots])
done

lemma subseteq_mut_mo_valid_ref_locs:
  "prefixed ''store_del_mo'' \<union> {''lop_store_ins''} \<subseteq> mut_mo_valid_ref_locs"
by (auto simp: mut_mo_valid_ref_locs_def intro: append_prefixD)

lemma subseteq_mut_mo_valid_ref_locs2:
  "prefixed ''store_ins'' \<subseteq> mut_mo_valid_ref_locs"
by (clarsimp simp: mut_mo_valid_ref_locs_def)

lemma mut_phase_inv:
  "\<lbrakk> ghost_handshake_phase (s (mutator m)) = hp_Mark \<or> ghost_handshake_phase (s (mutator m)) = hp_IdleMarkSweep \<and> sys_phase s \<noteq> ph_Idle;
     mut_m.mutator_phase_inv_aux m (ghost_handshake_phase (s (mutator m))) s \<rbrakk>
     \<Longrightarrow> mut_m.marked_insertions m s \<and> mut_m.marked_deletions m s"
by (cases "ghost_handshake_phase (s (mutator m))", simp_all)

lemma (in sys) mut_mark_object_invL[intro]:
  notes mut_m.mark_object_invL_def[inv]
  notes do_write_action_fM[where m=m, simp]
  notes do_write_action_prj_simps(1)[simp del] do_write_action_prj_simps(2)[simp del]
  notes mut_m_get_roots_no_fM_write[where m=m, simp]
  notes mut_m_get_roots_no_phase_write[where m=m, simp]
  notes mut_m_ghost_handshake_phase_not_hp_Idle[where m=m, simp]
  notes atS_simps[simp] filter_empty_conv[simp]
  shows "\<lbrace> mut_m.handshake_invL m \<^bold>\<and> mut_m.mark_object_invL m
             \<^bold>\<and> LSTP (fA_rel_inv \<^bold>\<and> fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> phase_rel_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv \<^bold>\<and> tso_writes_inv) \<rbrace>
           sys
         \<lbrace> mut_m.mark_object_invL m \<rbrace>"
apply vcg_nihe
apply vcg_ni

subgoal by (clarsimp simp: do_write_action_def filter_empty_conv p_not_sys
               dest!: valid_W_invD2
               elim!: obj_at_weakenE
               split: mem_write_action.splits)

subgoal by (clarsimp simp: do_write_action_def filter_empty_conv p_not_sys
               dest!: valid_W_invD2
               elim!: obj_at_weakenE
               split: mem_write_action.splits)

subgoal by (clarsimp simp: do_write_action_def filter_empty_conv p_not_sys loc
               dest!: valid_W_invD2
               elim!: obj_at_weakenE
               split: mem_write_action.splits)

subgoal
  apply (drule phase_rel_invD)
  apply (drule mut_m.handshake_phase_invD[where m=m])
  apply (clarsimp simp: p_not_sys)
  apply (erule disjE)
   apply (clarsimp simp: hp_step_rel_def)
   apply (elim disjE, simp_all add: phase_rel_def)[1]
  apply force
  done

subgoal
  apply (clarsimp simp: do_write_action_def filter_empty_conv p_not_sys loc fM_rel_inv_def
                 dest!: valid_W_invD2
                 elim!: obj_at_weakenE
                 split: mem_write_action.splits)
    apply (rule conjI)
     apply (clarsimp elim!: obj_at_weakenE)
    apply clarsimp
   apply (drule mut_m.handshake_phase_invD[where m=m])
   apply (erule disjE)
    apply (auto simp: fM_rel_def hp_step_rel_def)[1]
   apply force
  apply (erule disjE)
   apply (drule mut_m.handshake_phase_invD[where m=m])
   apply (drule phase_rel_invD)
   apply (clarsimp simp: hp_step_rel_def)
   apply (auto simp: phase_rel_def)[1]
  apply force
  done

subgoal for s s' p w ws
  apply (drule mp, erule atS_mono[OF _ subseteq_mut_mo_valid_ref_locs])
  apply ((thin_tac "atS p ls s \<longrightarrow> Q" for p ls s Q)+)[1]
  apply ((thin_tac "at p ls s \<longrightarrow> Q" for p ls s Q)+)[1]
  apply (clarsimp simp: do_write_action_def p_not_sys loc
                 split: mem_write_action.splits if_splits)
       apply (drule (1) valid_W_invD2)
       apply (erule obj_at_field_on_heap_weakenE)
       apply (fastforce split: obj_at_splits)
      apply (drule (1) valid_W_invD2)
      apply (erule obj_at_field_on_heap_weakenE)
      apply (fastforce split: obj_at_splits)
     apply (drule spec[where x=m])
     apply (frule (1) mut_phase_inv)
     apply (rename_tac refa fielda option)
     apply (frule_tac y="refa" in valid_refs_invD3, simp_all)[1]
     apply (frule_tac y="tmp_ref (s\<down> (mutator m))" in valid_refs_invD(2), simp_all)[1]
     apply (clarsimp split: obj_at_splits option.splits)
      apply force
     apply (frule (1) marked_insertionsD)
     apply (auto split: obj_at_splits; fail)[1]
    apply (erule disjE) (* super messy case *)
     apply force
    apply (rule conjI)
     apply (erule obj_at_field_on_heap_imp_valid_ref)
    apply (clarsimp split: option.splits)
    apply (drule phase_rel_invD)
    apply (frule mut_m.handshake_phase_invD[where m=m])
    apply (rename_tac ma x2)
    apply (drule_tac m=ma in mut_m.handshake_phase_invD)
    apply (frule spec[where x=m])
    apply (drule_tac x=ma in spec)
    apply (clarsimp simp: hp_step_rel_def)
    apply (elim disjE, auto simp: phase_rel_def dest: marked_insertionsD; fail)[1]
   apply (erule disjE; clarsimp)
   apply (drule mut_m.handshake_phase_invD[where m=m])
   apply (clarsimp simp: fM_rel_inv_def fM_rel_def hp_step_rel_def)
   apply (metis (no_types, lifting) handshake_phase.distinct(5) handshake_phase.distinct(7))
  apply (erule disjE; clarsimp)
  apply (drule mut_m.handshake_phase_invD[where m=m])
  apply (drule phase_rel_invD)
  apply (clarsimp simp: hp_step_rel_def phase_rel_def)
  done

subgoal for s s' p w ws y
  apply (clarsimp simp: do_write_action_def p_not_sys
                 split: mem_write_action.splits if_splits)
    apply (auto split: obj_at_splits; fail)[1]
   apply (erule disjE; clarsimp)
   apply (drule mut_m.handshake_phase_invD[where m=m])
   apply (clarsimp simp: fM_rel_inv_def fM_rel_def hp_step_rel_def)
   apply (metis (no_types, lifting) handshake_phase.distinct(5) handshake_phase.distinct(7))
  apply (erule disjE; clarsimp)
  apply (drule mut_m.handshake_phase_invD[where m=m])
  apply (drule phase_rel_invD)
  apply (clarsimp simp: hp_step_rel_def phase_rel_def)
  done

subgoal for s s' p w ws
  apply (drule mp, erule atS_mono[OF _ subseteq_mut_mo_valid_ref_locs2])
  apply ((thin_tac "atS p ls s \<longrightarrow> Q" for p ls s Q)+)[1]
  apply ((thin_tac "at p ls s \<longrightarrow> Q" for p ls s Q)+)[1]
  apply (subst do_write_action_fM[where m=m], simp_all)[1]
   apply (elim disjE, simp_all)[1]
  apply (clarsimp simp: do_write_action_def p_not_sys
                 split: mem_write_action.splits if_splits)
      apply (erule obj_at_field_on_heap_weakenE, auto)[1]
     apply (erule obj_at_field_on_heap_weakenE, auto split: obj_at_splits)[1]
    apply (drule spec[where x=m])
    apply (frule (1) mut_phase_inv)
    apply (rename_tac refa fielda option)
    apply (frule_tac y="refa" in valid_refs_invD3, simp_all)[1]
    apply (frule_tac y="tmp_ref (s\<down> (mutator m))" in valid_refs_invD(2), simp_all)[1]
    apply (clarsimp split: obj_at_splits option.splits)
     apply auto[1]
    apply (frule (1) marked_insertionsD)
    apply (auto split: obj_at_splits)[1]
   apply (erule disjE) (* super messy case *)
    apply force
   apply (rule conjI)
    apply (erule obj_at_field_on_heap_imp_valid_ref)
   apply (clarsimp split: option.splits)
   apply (drule phase_rel_invD)
   apply (frule mut_m.handshake_phase_invD[where m=m])
   apply (rename_tac ma x2)
   apply (drule_tac m=ma in mut_m.handshake_phase_invD)
   apply (frule spec[where x=m])
   apply (drule_tac x=ma in spec)
   apply (clarsimp simp: hp_step_rel_def)
   apply (elim disjE, auto simp: phase_rel_def dest: marked_insertionsD)[1]
  apply (erule disjE)
   apply (drule mut_m.handshake_phase_invD[where m=m])
   apply (drule phase_rel_invD)
   apply (clarsimp simp: hp_step_rel_def phase_rel_def)
  apply force
  done

done

lemma (in gc) mut_mark_object_invL[intro]:
  notes mut_m.mark_object_invL_def[inv]
  notes atS_simps[simp]
  shows "\<lbrace> fM_fA_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> handshake_invL \<^bold>\<and> sweep_loop_invL
            \<^bold>\<and> mut_m.handshake_invL m
            \<^bold>\<and> mut_m.mark_object_invL m
            \<^bold>\<and> LSTP (fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> sys_phase_inv) \<rbrace>
           gc
         \<lbrace> mut_m.mark_object_invL m \<rbrace>"
apply vcg_nihe
apply vcg_ni

subgoal
 apply (drule (1) mut_m_handshake_invL_get_roots)
 apply clarsimp
 done

subgoal by (simp add: mut_m.handshake_invL_def)

subgoal by (fastforce simp: fM_rel_inv_def fM_rel_def hp_step_rel_def split: obj_at_splits)

subgoal
 apply (drule mut_m.handshake_phase_invD[where m=m])
 apply (drule spec[where x=m])
 apply (clarsimp simp: valid_null_ref_def hp_step_rel_def conj_disj_distribR[symmetric] split: option.splits)
 apply (drule (1) mut_m.reachable_blackD)
  apply blast
 apply (clarsimp split: obj_at_splits)
 done

subgoal
 apply (drule mp, erule atS_mono[OF _ subseteq_mut_mo_valid_ref_locs])
 apply ((thin_tac "atS p ls s \<longrightarrow> Q" for p ls s Q)+)[1]
 apply ((thin_tac "at p ls s \<longrightarrow> Q" for p ls s Q)+)[1]
 apply (drule mut_m.handshake_phase_invD[where m=m])
 apply (drule spec[where x=m])
 apply (clarsimp simp: valid_null_ref_def hp_step_rel_def conj_disj_distribR[symmetric] split: option.splits)
 apply (drule (1) mut_m.reachable_blackD)
  apply blast
 apply (auto simp: obj_at_field_on_heap_def black_def split: obj_at_splits option.splits)[1]
 done

subgoal by (clarsimp split: obj_at_splits)

subgoal
 apply (drule mp, erule atS_mono[OF _ subseteq_mut_mo_valid_ref_locs2])
 apply ((thin_tac "atS p ls s \<longrightarrow> Q" for p ls s Q)+)[1]
 apply ((thin_tac "at p ls s \<longrightarrow> Q" for p ls s Q)+)[1]
 apply (drule mut_m.handshake_phase_invD[where m=m])
 apply (drule spec[where x=m])
 apply (clarsimp simp: valid_null_ref_def hp_step_rel_def conj_disj_distribR[symmetric] split: option.splits)
 apply (drule (1) mut_m.reachable_blackD)
  apply blast
 apply (auto simp: obj_at_field_on_heap_def black_def split: obj_at_splits option.splits)[1]
done

done

lemma (in gc) mut_store_old_mark_object_invL[intro]:
  notes mut_m.mark_object_invL_def[inv]
  shows
  "\<lbrace> fM_fA_invL \<^bold>\<and> handshake_invL \<^bold>\<and> sweep_loop_invL \<^bold>\<and> gc_W_empty_invL
      \<^bold>\<and> mut_m.mark_object_invL m
      \<^bold>\<and> mut_store_del.mark_object_invL m
      \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mut_m.mutator_phase_inv m) \<rbrace>
     gc
   \<lbrace> mut_store_del.mark_object_invL m \<rbrace>"
apply vcg_nihe
apply vcg_ni
 apply ( (clarsimp dest!: mut_m.handshake_phase_invD[where m=m]
                   simp: hp_step_rel_def conj_disj_distribR[symmetric]
        , drule_tac r="gc_tmp_ref s\<down>" in mut_m.no_grey_refs_not_rootD[where m=m]
        , auto split: obj_at_splits if_splits)[1] )+
done

lemma (in gc) mut_store_ins_mark_object_invL[intro]:
  notes mut_m.mark_object_invL_def[inv]
  shows
  "\<lbrace> fM_fA_invL \<^bold>\<and> handshake_invL \<^bold>\<and> sweep_loop_invL \<^bold>\<and> gc_W_empty_invL
      \<^bold>\<and> mut_m.mark_object_invL m
      \<^bold>\<and> mut_store_ins.mark_object_invL m
      \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mut_m.mutator_phase_inv m) \<rbrace>
     gc
   \<lbrace> mut_store_ins.mark_object_invL m \<rbrace>"
apply vcg_nihe
apply vcg_ni
 apply ( (clarsimp dest!: mut_m.handshake_phase_invD[where m=m]
                   simp: hp_step_rel_def conj_disj_distribR[symmetric]
        , drule_tac r="gc_tmp_ref s\<down>" in mut_m.no_grey_refs_not_rootD[where m=m]
        , auto split: obj_at_splits if_splits)[1] )+
done

lemma obj_fields_marked_locs_subseteq_hp_IdleMarkSweep_locs:
  "obj_fields_marked_locs \<subseteq> hp_IdleMarkSweep_locs"
apply (clarsimp simp: obj_fields_marked_locs_def hp_IdleMarkSweep_locs_def mark_loop_locs_def)
apply (drule mp)
apply (auto intro: append_prefixD)
done

lemma obj_fields_marked_locs_subseteq_hs_in_sync_locs:
  "obj_fields_marked_locs \<subseteq> hs_in_sync_locs"
by (auto simp: obj_fields_marked_locs_def hs_in_sync_locs_def hs_done_locs_def
         dest: prefix_same_cases)

lemma handshake_obj_fields_markedD:
  "\<lbrakk> atS gc obj_fields_marked_locs s; gc.handshake_invL s \<rbrakk> \<Longrightarrow> sys_ghost_handshake_phase s\<down> = hp_IdleMarkSweep \<and> All (ghost_handshake_in_sync (s\<down> sys))"
apply (simp add: gc.handshake_invL_def)
apply (elim conjE)
apply (drule mp, erule atS_mono[OF _ obj_fields_marked_locs_subseteq_hp_IdleMarkSweep_locs])
apply (drule mp, erule atS_mono[OF _ obj_fields_marked_locs_subseteq_hs_in_sync_locs])
apply clarsimp
done

lemma mark_loop_mo_mark_loop_field_done_subseteq_hp_IdleMarkSweep_locs:
  "prefixed ''mark_loop_mo'' \<union> {''mark_loop_mark_field_done''} \<subseteq> hp_IdleMarkSweep_locs"
apply (clarsimp simp: hp_IdleMarkSweep_locs_def mark_loop_locs_def)
apply (drule mp)
apply (auto intro: append_prefixD)
done

lemma mark_loop_mo_mark_loop_field_done_subseteq_hs_in_sync_locs:
  "prefixed ''mark_loop_mo'' \<union> {''mark_loop_mark_field_done''} \<subseteq> hs_in_sync_locs"
by (auto simp: hs_in_sync_locs_def hs_done_locs_def
         dest: prefix_same_cases)

lemma mark_loop_mo_mark_loop_field_done_hp_phaseD:
  "\<lbrakk> atS gc (prefixed ''mark_loop_mo'' \<union> {''mark_loop_mark_field_done''}) s; gc.handshake_invL s \<rbrakk> \<Longrightarrow> sys_ghost_handshake_phase s\<down> = hp_IdleMarkSweep \<and> All (ghost_handshake_in_sync (s\<down> sys))"
apply (simp add: gc.handshake_invL_def)
apply (elim conjE)
apply (drule mp, erule atS_mono[OF _ mark_loop_mo_mark_loop_field_done_subseteq_hp_IdleMarkSweep_locs])
apply (drule mp, erule atS_mono[OF _ mark_loop_mo_mark_loop_field_done_subseteq_hs_in_sync_locs])
apply clarsimp
done

(* an alternative is some kind of ghost_honorary_XXX for the GC while marking *)
lemma gc_marking_reaches_mw_Mutate:
  assumes xys: "\<forall>y. (x reaches y) s \<longrightarrow> valid_ref y s"
  assumes xy: "(x reaches y) (s(sys := s sys\<lparr>heap := (sys_heap s)(r := Option.map_option (\<lambda>obj. obj\<lparr>obj_fields := (obj_fields obj)(f := opt_r')\<rparr>) (sys_heap s r)),
                                             mem_write_buffers := (mem_write_buffers (s sys))(p := ws)\<rparr>))"
  assumes sb: "sys_mem_write_buffers (mutator m) s = mw_Mutate r f opt_r' # ws"
  assumes vri: "valid_refs_inv s"
  shows "valid_ref y s"
proof -
  from xy xys
  have "\<exists>z. z \<in> {x} \<union> mut_m.tso_write_refs m s \<and> (z reaches y) s \<and> valid_ref y s"
  proof(induct rule: rtranclp.induct)
    case (rtrancl_refl x) then show ?case by auto
  next
    case (rtrancl_into_rtrancl x y z) with sb vri show ?case
      apply (clarsimp simp: points_to_mw_Mutate)
      apply (elim disjE)
         apply (force dest: rtranclp.intros(2))
        apply (force dest: rtranclp.intros(2))
       apply clarsimp
       apply (elim disjE)
        apply (rule exI[where x=z])
        apply (clarsimp simp: mut_m.tso_write_refs_def)
        apply (rule valid_refs_invD(3)[where m=m and x=z], auto simp: mut_m.tso_write_refs_def)[1]
       apply (force dest: rtranclp.intros(2))
      apply clarsimp
      apply (elim disjE)
       apply (rule exI[where x=z])
       apply (clarsimp simp: mut_m.tso_write_refs_def)
       apply (rule valid_refs_invD(3)[where m=m and x=z], auto simp: mut_m.tso_write_refs_def)[1]
      apply (force dest: rtranclp.intros(2))
      done
  qed
  then show ?thesis by blast
qed

lemma (in sys) gc_obj_fields_marked_invL[intro]:
  notes gc.obj_fields_marked_invL_def[inv]
  shows
  "\<lbrace> gc.fM_fA_invL \<^bold>\<and> gc.handshake_invL \<^bold>\<and> gc.obj_fields_marked_invL
       \<^bold>\<and> LSTP (fM_rel_inv \<^bold>\<and> handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> tso_writes_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     sys
   \<lbrace> gc.obj_fields_marked_invL \<rbrace>"
apply vcg_nihe
apply (vcg_ni simp: p_not_sys fM_rel_inv_def)
 apply (clarsimp simp: gc.obj_fields_marked_inv_def)
 apply (frule (1) handshake_obj_fields_markedD)
 apply (clarsimp simp: do_write_action_def
                split: mem_write_action.splits)

(* mark *)
subgoal for s s' p ws x ref bool
 apply (frule (1) valid_W_invD2)
 apply (drule_tac x=x in spec)
 apply clarsimp
 apply (erule obj_at_field_on_heap_weakenE)
 apply (clarsimp split: obj_at_splits)
 done

(* ref *)
subgoal for s s' p ws x x23
  apply (erule disjE; clarsimp)
  apply (rename_tac m)
  apply (drule_tac m=m in mut_m.handshake_phase_invD; clarsimp simp: hp_step_rel_def conj_disj_distribR[symmetric])
  apply (drule_tac x=m in spec; clarsimp)
  apply (drule_tac x=x in spec; clarsimp)
  apply (auto split: option.splits)
  done

(* fM *)
subgoal for s s' p ws x x4
   apply (erule disjE)
    apply (auto simp: fM_rel_def filter_empty_conv)[1]
   apply clarsimp
   done

subgoal for s s' p w ws
   apply (clarsimp simp: gc.obj_fields_marked_inv_def)
   apply (frule (1) mark_loop_mo_mark_loop_field_done_hp_phaseD)
   apply (clarsimp simp: do_write_action_def
                  split: mem_write_action.splits)
   (* mark *)
   apply (frule (1) valid_W_invD2)
   apply (erule obj_at_field_on_heap_weakenE)
   apply (clarsimp split: obj_at_splits)
  (* ref *)
  apply (erule disjE, clarsimp+)[1]
  apply (rename_tac option m)
  apply (drule_tac m=m in mut_m.handshake_phase_invD, clarsimp simp: hp_step_rel_def conj_disj_distribR[symmetric])
  apply (drule_tac x=m in spec, clarsimp)
  apply (rule conjI)
   apply (rule_tac x="gc_tmp_ref s\<down>" and m=m in valid_refs_invD(3), auto simp: mut_m.tso_write_refs_def)[1]
  apply (clarsimp split: option.splits dest!: marked_insertionD)
 (* fM *)
 apply (erule disjE)
  apply (auto simp: fM_rel_def filter_empty_conv)[1]
 apply clarsimp
 done

subgoal for s s' p w ws x y
 apply (clarsimp simp: do_write_action_def
                split: mem_write_action.splits)
  (* mark *)
  subgoal
    apply (drule_tac x=x in spec)
    apply (drule mp, erule predicate2D[OF rtranclp_mono[OF predicate2I], rotated])
     apply clarsimp
    apply assumption
    done
 (* ref *)
 subgoal
   apply (clarsimp simp: atS_un)
   apply (erule disjE; clarsimp)
   apply (erule gc_marking_reaches_mw_Mutate; blast)
   done
 done

(* mark loop mark field done *)
subgoal
 apply (clarsimp simp: do_write_action_def
               split: mem_write_action.splits)
  (* mark *)
  apply fast
 (* fM *)
 apply (clarsimp simp: gc.handshake_invL_def loc atS_simps)
 apply (erule disjE)
  apply (auto simp: fM_rel_def filter_empty_conv)[1]
 apply clarsimp
 done

done

lemma reachable_sweep_loop_free:
  "mut_m.reachable m r (s(sys := s sys\<lparr>heap := (sys_heap s)(r' := None)\<rparr>))
   \<Longrightarrow> mut_m.reachable m r s"
apply (clarsimp simp: mut_m.reachable_def)
apply (rename_tac x)
apply (rule_tac x=x in exI, simp)
apply (erule predicate2D[OF rtranclp_mono[OF predicate2I], rotated], clarsimp split: if_splits obj_at_splits)
done

lemma valid_refs_inv_sweep_loop_free[simp]:
  assumes "valid_refs_inv s"
  assumes ngr: "no_grey_refs s"
  assumes rsi: "\<forall>m'. mut_m.reachable_snapshot_inv m' s"
  assumes "white r' s"
  shows "valid_refs_inv (s(sys := s sys\<lparr>heap := (sys_heap s)(r' := None)\<rparr>))"
using assms
apply (clarsimp simp: valid_refs_inv_def grey_reachable_def no_grey_refs_def dest!: reachable_sweep_loop_free)
apply (drule mut_m.reachable_blackD[OF ngr spec[OF rsi]])
apply (auto split: obj_at_splits)
done

lemma (in gc) valid_refs_inv[intro]:
  "\<lbrace> fM_fA_invL \<^bold>\<and> handshake_invL \<^bold>\<and> gc_W_empty_invL \<^bold>\<and> gc_mark.mark_object_invL \<^bold>\<and> obj_fields_marked_invL \<^bold>\<and> phase_invL \<^bold>\<and> sweep_loop_invL
       \<^bold>\<and> LSTP (handshake_phase_inv \<^bold>\<and> mutators_phase_inv \<^bold>\<and> sys_phase_inv \<^bold>\<and> valid_refs_inv \<^bold>\<and> valid_W_inv) \<rbrace>
     gc
   \<lbrace> LSTP valid_refs_inv \<rbrace>"
apply vcg_jackhammer

(* sweep loop free *)
apply (drule (1) handshake_in_syncD)
apply clarsimp

apply (auto simp: valid_refs_inv_def grey_reachable_def)
done

lemma (in sys) valid_refs_inv[intro]:
  "\<lbrace> LSTP (valid_refs_inv \<^bold>\<and> tso_writes_inv) \<rbrace> sys \<lbrace> LSTP valid_refs_inv \<rbrace>"
apply vcg_jackhammer
apply (auto simp: do_write_action_def p_not_sys
           split: mem_write_action.splits)
done

lemma (in mut_m) valid_refs_inv_discard_roots[simp]:
  "\<lbrakk> valid_refs_inv s; roots' \<subseteq> mut_roots s \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr>roots := roots'\<rparr>))"
by (auto simp: valid_refs_inv_def mut_m.reachable_def split: if_splits)

lemma (in mut_m) valid_refs_inv_load[simp]:
  "\<lbrakk> valid_refs_inv s; sys_read (mutator m) (mr_Ref r f) (s sys) = mv_Ref r'; r \<in> mut_roots s \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr>roots := mut_roots s \<union> Option.set_option r'\<rparr>))"
by (auto simp: valid_refs_inv_def)

lemma (in mut_m) valid_refs_inv_alloc[simp]:
  "\<lbrakk> valid_refs_inv s; sys_heap s r' = None \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr>roots := insert r' (mut_roots s)\<rparr>, sys := s sys\<lparr>heap := sys_heap s(r' \<mapsto> \<lparr>obj_mark = fl, obj_fields = Map.empty\<rparr>)\<rparr>))"
apply (clarsimp simp: valid_refs_inv_def)
apply (clarsimp simp: mut_m.reachable_def split: if_splits)
apply (auto elim: converse_rtranclpE split: obj_at_splits)
done

lemma (in mut_m) valid_refs_inv_store_ins[simp]:
  "\<lbrakk> valid_refs_inv s; r \<in> mut_roots s; (\<exists>r'. opt_r' = Some r') \<longrightarrow> the opt_r' \<in> mut_roots s \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr> ghost_honorary_root := {} \<rparr>,
                          sys := s sys\<lparr> mem_write_buffers := (mem_write_buffers (s sys))(mutator m := sys_mem_write_buffers (mutator m) s @ [mw_Mutate r f opt_r']) \<rparr>))"
apply (subst valid_refs_inv_def)
apply (clarsimp simp: grey_reachable_def mut_m.reachable_def)
apply (rule conjI)
 apply clarsimp
 apply (rename_tac x xa)
 apply (case_tac "xa = m")
  apply clarsimp
  apply fastforce
 apply clarsimp
 apply (fastforce dest: valid_refs_invD)
apply fastforce
done

lemma (in mut_m) valid_refs_inv_deref_del[simp]:
  "\<lbrakk> valid_refs_inv s; sys_read (mutator m) (mr_Ref r f) (s sys) = mv_Ref opt_r'; r \<in> mut_roots s; mut_ghost_honorary_root s = {} \<rbrakk>
     \<Longrightarrow> valid_refs_inv (s(mutator m := s (mutator m)\<lparr>ghost_honorary_root := Option.set_option opt_r', ref := opt_r'\<rparr>))"
by (clarsimp simp: valid_refs_inv_def)

lemma (in mut_m) valid_refs_inv[intro]:
  "\<lbrace> mark_object_invL
       \<^bold>\<and> mut_get_roots.mark_object_invL m
       \<^bold>\<and> mut_store_del.mark_object_invL m
       \<^bold>\<and> mut_store_ins.mark_object_invL m
       \<^bold>\<and> LSTP valid_refs_inv \<rbrace>
     mutator m
   \<lbrace> LSTP valid_refs_inv \<rbrace>"
apply vcg_jackhammer

(* store ins mo co mark - FIXME some elim/dest rule really gets in the way here *)
subgoal
  apply (subst valid_refs_inv_def)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule (1) valid_refs_invD)
  apply (clarsimp simp: grey_reachable_def)
  apply (erule disjE)
   apply (erule (1) valid_refs_invD, simp)
  apply clarsimp
  apply (erule (1) valid_refs_invD, simp)
  done

(* store del mo co mark *)
subgoal
  apply (subst valid_refs_inv_def)
  apply clarsimp
  apply (rule conjI)
   apply clarsimp
   apply (erule (1) valid_refs_invD)
  apply (clarsimp simp: grey_reachable_def)
  apply (erule disjE)
   apply (erule (1) valid_refs_invD, simp)
  apply clarsimp
  apply (erule (1) valid_refs_invD, simp)
  done

(* get roots done *)
subgoal by (clarsimp simp: valid_refs_inv_def grey_reachable_def)

(* get roots loop mo co mark *)
subgoal by (auto simp: valid_refs_inv_def grey_reachable_def)

(* get work done *)
subgoal by (clarsimp simp: valid_refs_inv_def grey_reachable_def)

done

(*>*)
(*<*)

end
(*>*)
