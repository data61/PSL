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
      (transition A\<^sub>1, transition A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> S \<and>
      (condition A\<^sub>1, condition A\<^sub>2) \<in> \<langle>rabin_rel S\<rangle> list_rel}"

  lemma dra_param[param]:
    "(dra, dra) \<in> \<langle>L\<rangle> set_rel \<rightarrow> S \<rightarrow> (L \<rightarrow> S \<rightarrow> S) \<rightarrow> \<langle>rabin_rel S\<rangle> list_rel \<rightarrow>
      \<langle>L, S\<rangle> dra_rel"
    "(alphabet, alphabet) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> \<langle>L\<rangle> set_rel"
    "(initial, initial) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> S"
    "(transition, transition) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> L \<rightarrow> S \<rightarrow> S"
    "(condition, condition) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> \<langle>rabin_rel S\<rangle> list_rel"
    unfolding dra_rel_def fun_rel_def by auto

  lemma dra_rel_id[simp]: "\<langle>Id, Id\<rangle> dra_rel = Id" unfolding dra_rel_def using dra.expand by auto
  lemma dra_rel_comp[trans]:
    assumes [param]: "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1\<rangle> dra_rel" "(B, C) \<in> \<langle>L\<^sub>2, S\<^sub>2\<rangle> dra_rel"
    shows "(A, C) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2\<rangle> dra_rel"
  proof -
    have "(condition A, condition B) \<in> \<langle>rabin_rel S\<^sub>1\<rangle> list_rel" by parametricity
    also have "(condition B, condition C) \<in> \<langle>rabin_rel S\<^sub>2\<rangle> list_rel" by parametricity
    finally have 1: "(condition A, condition C) \<in> \<langle>rabin_rel S\<^sub>1 O rabin_rel S\<^sub>2\<rangle> list_rel" by simp
    have 2: "rabin_rel S\<^sub>1 O rabin_rel S\<^sub>2 \<subseteq> rabin_rel (S\<^sub>1 O S\<^sub>2)" by (force simp: fun_rel_def)
    have 3: "(condition A, condition C) \<in> \<langle>rabin_rel (S\<^sub>1 O S\<^sub>2)\<rangle> list_rel" using 1 2 list_rel_mono by blast
    have "(transition A, transition B) \<in> L\<^sub>1 \<rightarrow> S\<^sub>1 \<rightarrow> S\<^sub>1" by parametricity
    also have "(transition B, transition C) \<in> L\<^sub>2 \<rightarrow> S\<^sub>2 \<rightarrow> S\<^sub>2" by parametricity
    finally have 4: "(transition A, transition C) \<in> L\<^sub>1 O L\<^sub>2 \<rightarrow> S\<^sub>1 O S\<^sub>2 \<rightarrow> S\<^sub>1 O S\<^sub>2" by this
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

  lemma enableds_param[param]: "(dra.enableds, dra.enableds) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> S \<rightarrow> \<langle>L\<rangle> set_rel"
    unfolding dra.enableds_def Collect_mem_eq by parametricity
  lemma paths_param[param]: "(dra.paths, dra.paths) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> S \<rightarrow> \<langle>\<langle>L\<rangle> list_rel\<rangle> set_rel"
    using enableds_param[param_fo] by parametricity
  lemma runs_param[param]: "(dra.runs, dra.runs) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> S \<rightarrow> \<langle>\<langle>L\<rangle> stream_rel\<rangle> set_rel"
    using enableds_param[param_fo] by parametricity

  lemma reachable_param[param]: "(reachable, reachable) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> S \<rightarrow> \<langle>S\<rangle> set_rel"
  proof -
    have 1: "reachable A p = (\<lambda> w. target A w p) ` dra.paths A p" for A :: "('label, 'state) dra" and p
      unfolding dra.reachable_alt_def dra.paths_def by auto
    show ?thesis unfolding 1 using enableds_param[param_fo] by parametricity
  qed
  lemma nodes_param[param]: "(nodes, nodes) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> \<langle>S\<rangle> set_rel"
  proof -
    have 1: "nodes A = reachable A (initial A)" for A :: "('label, 'state) dra"
      unfolding dra.nodes_alt_def by simp
    show ?thesis unfolding 1 by parametricity
  qed

  lemma language_param[param]: "(language, language) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> \<langle>\<langle>L\<rangle> stream_rel\<rangle> set_rel"
  proof -
    have 1: "language A = (\<Union> w \<in> dra.runs A (initial A).
      if cogen rabin (condition A) (initial A ## trace A w (initial A)) then {w} else {})"
      for A :: "('label, 'state) dra"
      unfolding dra.language_def dra.runs_def by auto
    show ?thesis unfolding 1 using enableds_param[param_fo] by parametricity
  qed

end