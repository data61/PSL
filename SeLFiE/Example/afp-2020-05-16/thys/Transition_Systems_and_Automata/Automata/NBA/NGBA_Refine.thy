section \<open>Relations on Nondeterministic Generalized Büchi Automata\<close>

theory NGBA_Refine
imports
  "NGBA"
  "../../Transition_Systems/Transition_System_Refine"
begin

  definition ngba_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1) ngba \<times> ('label\<^sub>2, 'state\<^sub>2) ngba) set" where
    [to_relAPP]: "ngba_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabet A\<^sub>1, alphabet A\<^sub>2) \<in> \<langle>L\<rangle> set_rel \<and>
      (initial A\<^sub>1, initial A\<^sub>2) \<in> \<langle>S\<rangle> set_rel \<and>
      (transition A\<^sub>1, transition A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel \<and>
      (accepting A\<^sub>1, accepting A\<^sub>2) \<in> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel}"

  lemma ngba_param[param]:
    "(ngba, ngba) \<in> \<langle>L\<rangle> set_rel \<rightarrow> \<langle>S\<rangle> set_rel \<rightarrow> (L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel) \<rightarrow> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel \<rightarrow>
      \<langle>L, S\<rangle> ngba_rel"
    "(alphabet, alphabet) \<in> \<langle>L, S\<rangle> ngba_rel \<rightarrow> \<langle>L\<rangle> set_rel"
    "(initial, initial) \<in> \<langle>L, S\<rangle> ngba_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    "(transition, transition) \<in> \<langle>L, S\<rangle> ngba_rel \<rightarrow> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel"
    "(accepting, accepting) \<in> \<langle>L, S\<rangle> ngba_rel \<rightarrow> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel"
    unfolding ngba_rel_def fun_rel_def by auto

  lemma ngba_rel_id[simp]: "\<langle>Id, Id\<rangle> ngba_rel = Id" unfolding ngba_rel_def using ngba.expand by auto

  lemma enableds_param[param]: "(ngba.enableds, ngba.enableds) \<in> \<langle>L, S\<rangle> ngba_rel \<rightarrow> S \<rightarrow> \<langle>L \<times>\<^sub>r S\<rangle> set_rel"
    using ngba_param(2, 4) unfolding ngba.enableds_def fun_rel_def set_rel_def by fastforce
  lemma paths_param[param]: "(ngba.paths, ngba.paths) \<in> \<langle>L, S\<rangle> ngba_rel \<rightarrow> S \<rightarrow> \<langle>\<langle>L \<times>\<^sub>r S\<rangle> list_rel\<rangle> set_rel"
    using enableds_param[param_fo] by parametricity
  lemma runs_param[param]: "(ngba.runs, ngba.runs) \<in> \<langle>L, S\<rangle> ngba_rel \<rightarrow> S \<rightarrow> \<langle>\<langle>L \<times>\<^sub>r S\<rangle> stream_rel\<rangle> set_rel"
    using enableds_param[param_fo] by parametricity

  lemma reachable_param[param]: "(reachable, reachable) \<in> \<langle>L, S\<rangle> ngba_rel \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel"
  proof -
    have 1: "reachable A p = (\<lambda> wr. target wr p) ` ngba.paths A p" for A :: "('label, 'state) ngba" and p
      unfolding ngba.reachable_alt_def ngba.paths_def by auto
    show ?thesis unfolding 1 using enableds_param[param_fo] by parametricity
  qed
  lemma nodes_param[param]: "(nodes, nodes) \<in> \<langle>L, S\<rangle> ngba_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    unfolding ngba.nodes_alt_def Collect_mem_eq by parametricity

  (* TODO: move *)
  lemma gen_param[param]: "(gen, gen) \<in> (A \<rightarrow> B \<rightarrow> bool_rel) \<rightarrow> \<langle>A\<rangle> list_rel \<rightarrow> B \<rightarrow> bool_rel"
    unfolding gen_def by parametricity

  lemma language_param[param]: "(language, language) \<in> \<langle>L, S\<rangle> ngba_rel \<rightarrow> \<langle>\<langle>L\<rangle> stream_rel\<rangle> set_rel"
  proof -
    have 1: "language A = (\<Union> p \<in> initial A. \<Union> wr \<in> ngba.runs A p.
      if gen infs (accepting A) (p ## smap snd wr) then {smap fst wr} else {})"
      for A :: "('label, 'state) ngba"
      unfolding ngba.language_def ngba.runs_def image_def
      by (auto iff: split_szip_ex simp del: alw_smap)
    show ?thesis unfolding 1 using enableds_param[param_fo] by parametricity
  qed

end