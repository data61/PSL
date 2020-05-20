section \<open>Relations on Nondeterministic Büchi Automata\<close>

theory NBA_Refine
imports
  "NBA"
  "../../Transition_Systems/Transition_System_Refine"
begin

  definition nba_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1) nba \<times> ('label\<^sub>2, 'state\<^sub>2) nba) set" where
    [to_relAPP]: "nba_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabet A\<^sub>1, alphabet A\<^sub>2) \<in> \<langle>L\<rangle> set_rel \<and>
      (initial A\<^sub>1, initial A\<^sub>2) \<in> \<langle>S\<rangle> set_rel \<and>
      (transition A\<^sub>1, transition A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel \<and>
      (accepting A\<^sub>1, accepting A\<^sub>2) \<in> S \<rightarrow> bool_rel}"

  lemma nba_param[param]:
    "(nba, nba) \<in> \<langle>L\<rangle> set_rel \<rightarrow> \<langle>S\<rangle> set_rel \<rightarrow> (L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel) \<rightarrow> (S \<rightarrow> bool_rel) \<rightarrow>
      \<langle>L, S\<rangle> nba_rel"
    "(alphabet, alphabet) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> \<langle>L\<rangle> set_rel"
    "(initial, initial) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    "(transition, transition) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel"
    "(accepting, accepting) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> S \<rightarrow> bool_rel"
    unfolding nba_rel_def fun_rel_def by auto

  lemma nba_rel_id[simp]: "\<langle>Id, Id\<rangle> nba_rel = Id" unfolding nba_rel_def using nba.expand by auto
  lemma nba_rel_comp[trans]:
    assumes [param]: "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1\<rangle> nba_rel" "(B, C) \<in> \<langle>L\<^sub>2, S\<^sub>2\<rangle> nba_rel"
    shows "(A, C) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2\<rangle> nba_rel"
  proof -
    have "(accepting A, accepting B) \<in> S\<^sub>1 \<rightarrow> bool_rel" by parametricity
    also have "(accepting B, accepting C) \<in> S\<^sub>2 \<rightarrow> bool_rel" by parametricity
    finally have 1: "(accepting A, accepting C) \<in> S\<^sub>1 O S\<^sub>2 \<rightarrow> bool_rel" by simp
    have "(transition A, transition B) \<in> L\<^sub>1 \<rightarrow> S\<^sub>1 \<rightarrow> \<langle>S\<^sub>1\<rangle> set_rel" by parametricity
    also have "(transition B, transition C) \<in> L\<^sub>2 \<rightarrow> S\<^sub>2 \<rightarrow> \<langle>S\<^sub>2\<rangle> set_rel" by parametricity
    finally have 2: "(transition A, transition C) \<in> L\<^sub>1 O L\<^sub>2 \<rightarrow> S\<^sub>1 O S\<^sub>2 \<rightarrow> \<langle>S\<^sub>1\<rangle> set_rel O \<langle>S\<^sub>2\<rangle> set_rel" by simp
    show ?thesis
      unfolding nba_rel_def mem_Collect_eq prod.case set_rel_compp
      using 1 2
      using nba_param(2 - 5)[THEN fun_relD, OF assms(1)]
      using nba_param(2 - 5)[THEN fun_relD, OF assms(2)]
      by auto
  qed
  lemma nba_rel_converse[simp]: "(\<langle>L, S\<rangle> nba_rel)\<inverse> = \<langle>L\<inverse>, S\<inverse>\<rangle> nba_rel"
  proof -
    have 1: "\<langle>L\<rangle> set_rel = (\<langle>L\<inverse>\<rangle> set_rel)\<inverse>" by simp
    have 2: "\<langle>S\<rangle> set_rel = (\<langle>S\<inverse>\<rangle> set_rel)\<inverse>" by simp
    have 3: "L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel = (L\<inverse> \<rightarrow> S\<inverse> \<rightarrow> \<langle>S\<inverse>\<rangle> set_rel)\<inverse>" by simp
    have 4: "S \<rightarrow> bool_rel = (S\<inverse> \<rightarrow> bool_rel)\<inverse>" by simp
    show ?thesis unfolding nba_rel_def unfolding 3 unfolding 1 2 4 by fastforce
  qed

  lemma nba_rel_eq: "(A, A) \<in> \<langle>Id_on (alphabet A), Id_on (nodes A)\<rangle> nba_rel"
    unfolding nba_rel_def by auto

  lemma enableds_param[param]: "(nba.enableds, nba.enableds) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> S \<rightarrow> \<langle>L \<times>\<^sub>r S\<rangle> set_rel"
    using nba_param(2, 4) unfolding nba.enableds_def fun_rel_def set_rel_def by fastforce
  lemma paths_param[param]: "(nba.paths, nba.paths) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> S \<rightarrow> \<langle>\<langle>L \<times>\<^sub>r S\<rangle> list_rel\<rangle> set_rel"
    using enableds_param[param_fo] by parametricity
  lemma runs_param[param]: "(nba.runs, nba.runs) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> S \<rightarrow> \<langle>\<langle>L \<times>\<^sub>r S\<rangle> stream_rel\<rangle> set_rel"
    using enableds_param[param_fo] by parametricity

  lemma reachable_param[param]: "(reachable, reachable) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel"
  proof -
    have 1: "reachable A p = (\<lambda> wr. target wr p) ` nba.paths A p" for A :: "('label, 'state) nba" and p
      unfolding nba.reachable_alt_def nba.paths_def by auto
    show ?thesis unfolding 1 using enableds_param[param_fo] by parametricity
  qed
  lemma nodes_param[param]: "(nodes, nodes) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    unfolding nba.nodes_alt_def Collect_mem_eq by parametricity

  lemma language_param[param]: "(language, language) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> \<langle>\<langle>L\<rangle> stream_rel\<rangle> set_rel"
  proof -
    have 1: "language A = (\<Union> p \<in> initial A. \<Union> wr \<in> nba.runs A p.
      if infs (accepting A) (p ## smap snd wr) then {smap fst wr} else {})"
      for A :: "('label, 'state) nba"
      unfolding nba.language_def nba.runs_def image_def
      by (auto iff: split_szip_ex simp del: alw_smap)
    show ?thesis unfolding 1 using enableds_param[param_fo] by parametricity
  qed

end