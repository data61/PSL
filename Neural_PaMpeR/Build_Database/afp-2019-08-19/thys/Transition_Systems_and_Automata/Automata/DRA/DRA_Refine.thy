section \<open>Relations on Deterministic Rabin Automata\<close>

theory DRA_Refine
imports
  "DRA"
  "../../Basic/Acceptance_Refine"
  "../../Transition_Systems/Transition_System_Refine"
begin

  definition dra_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1) dra \<times> ('label\<^sub>2, 'state\<^sub>2) dra) set" where
    [to_relAPP]: "dra_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabet A\<^sub>1, alphabet A\<^sub>2) \<in> \<langle>L\<rangle> set_rel \<and>
      (initial A\<^sub>1, initial A\<^sub>2) \<in> S \<and>
      (succ A\<^sub>1, succ A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> S \<and>
      (accepting A\<^sub>1, accepting A\<^sub>2) \<in> \<langle>rabin_rel S\<rangle> list_rel}"

  lemma dra_param[param]:
    "(dra, dra) \<in> \<langle>L\<rangle> set_rel \<rightarrow> S \<rightarrow> (L \<rightarrow> S \<rightarrow> S) \<rightarrow> \<langle>rabin_rel S\<rangle> list_rel \<rightarrow>
      \<langle>L, S\<rangle> dra_rel"
    "(alphabet, alphabet) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> \<langle>L\<rangle> set_rel"
    "(initial, initial) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> S"
    "(succ, succ) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> L \<rightarrow> S \<rightarrow> S"
    "(accepting, accepting) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> \<langle>rabin_rel S\<rangle> list_rel"
    unfolding dra_rel_def fun_rel_def by auto

  lemma dra_rel_id[simp]: "\<langle>Id, Id\<rangle> dra_rel = Id" unfolding dra_rel_def using dra.expand by auto
  lemma dra_rel_comp[trans]:
    assumes [param]: "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1\<rangle> dra_rel" "(B, C) \<in> \<langle>L\<^sub>2, S\<^sub>2\<rangle> dra_rel"
    shows "(A, C) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2\<rangle> dra_rel"
  proof -
    have "(accepting A, accepting B) \<in> \<langle>rabin_rel S\<^sub>1\<rangle> list_rel" by parametricity
    also have "(accepting B, accepting C) \<in> \<langle>rabin_rel S\<^sub>2\<rangle> list_rel" by parametricity
    finally have 1: "(accepting A, accepting C) \<in> \<langle>rabin_rel S\<^sub>1 O rabin_rel S\<^sub>2\<rangle> list_rel" by simp
    have 2: "rabin_rel S\<^sub>1 O rabin_rel S\<^sub>2 \<subseteq> rabin_rel (S\<^sub>1 O S\<^sub>2)" by (force simp: fun_rel_def)
    have 3: "(accepting A, accepting C) \<in> \<langle>rabin_rel (S\<^sub>1 O S\<^sub>2)\<rangle> list_rel" using 1 2 list_rel_mono by blast
    have "(succ A, succ B) \<in> L\<^sub>1 \<rightarrow> S\<^sub>1 \<rightarrow> S\<^sub>1" by parametricity
    also have "(succ B, succ C) \<in> L\<^sub>2 \<rightarrow> S\<^sub>2 \<rightarrow> S\<^sub>2" by parametricity
    finally have 4: "(succ A, succ C) \<in> L\<^sub>1 O L\<^sub>2 \<rightarrow> S\<^sub>1 O S\<^sub>2 \<rightarrow> S\<^sub>1 O S\<^sub>2" by this
    show ?thesis
      unfolding dra_rel_def mem_Collect_eq prod.case set_rel_compp
      using 3 4
      using dra_param(2 - 5)[THEN fun_relD, OF assms(1)]
      using dra_param(2 - 5)[THEN fun_relD, OF assms(2)]
      by auto
  qed
  lemma dra_rel_converse[simp]: "(\<langle>L, S\<rangle> dra_rel)\<inverse> = \<langle>L\<inverse>, S\<inverse>\<rangle> dra_rel"
  proof -
    have 1: "\<langle>L\<rangle> set_rel = (\<langle>L\<inverse>\<rangle> set_rel)\<inverse>" by simp
    have 2: "\<langle>S\<rangle> set_rel = (\<langle>S\<inverse>\<rangle> set_rel)\<inverse>" by simp
    have 3: "L \<rightarrow> S \<rightarrow> S = (L\<inverse> \<rightarrow> S\<inverse> \<rightarrow> S\<inverse>)\<inverse>" by simp
    have 4: "\<langle>rabin_rel S\<rangle> list_rel = (\<langle>rabin_rel (S\<inverse>)\<rangle> list_rel)\<inverse>" by simp
    show ?thesis unfolding dra_rel_def unfolding 3 unfolding 1 2 4 by fastforce
  qed

  lemma dra_rel_eq: "(A, A) \<in> \<langle>Id_on (alphabet A), Id_on (nodes A)\<rangle> dra_rel"
    unfolding dra_rel_def prod_rel_def using list_all2_same[to_set] by auto

  lemma enableds_param[param]: "(enableds, enableds) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> S \<rightarrow> \<langle>L\<rangle> set_rel"
    using dra_param(2, 4) unfolding dra.enableds_def fun_rel_def set_rel_def by fastforce
  lemma paths_param[param]: "(paths, paths) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> S \<rightarrow> \<langle>\<langle>L\<rangle> list_rel\<rangle> set_rel"
    unfolding paths_def by (intro fun_relI paths_param, fold enableds_def) (parametricity+)
  lemma runs_param[param]: "(runs, runs) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> S \<rightarrow> \<langle>\<langle>L\<rangle> stream_rel\<rangle> set_rel"
    unfolding runs_def by (intro fun_relI runs_param, fold enableds_def) (parametricity+)

  lemma reachable_param[param]: "(reachable, reachable) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel"
  proof -
    have 1: "reachable A p = (\<lambda> w. target A w p) ` paths A p" for A :: "('label, 'state) dra" and p
      unfolding dra.reachable_alt_def dra.paths_def by auto
    show ?thesis unfolding 1 by parametricity
  qed
  lemma nodes_param[param]: "(nodes, nodes) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> \<langle>S\<rangle> set_rel"
  proof -
    have 1: "nodes A = reachable A (initial A)" for A :: "('label, 'state) dra"
      unfolding dra.nodes_alt_def by simp
    show ?thesis unfolding 1 by parametricity
  qed

  lemma language_param[param]: "(language, language) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> \<langle>\<langle>L\<rangle> stream_rel\<rangle> set_rel"
  proof -
    have 1: "language A = (\<Union> w \<in> runs A (initial A).
      if cogen rabin (accepting A) (trace A w (initial A)) then {w} else {})"
      for A :: "('label, 'state) dra"
      unfolding language_def dra.runs_def image_def by auto
    show ?thesis unfolding 1 by parametricity
  qed

end