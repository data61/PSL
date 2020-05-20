section \<open>Implementation of Deterministic Rabin Automata\<close>

theory DRA_Implement
imports
  "DRA_Refine"
  "../../Basic/Implement"
begin

  datatype ('label, 'state) drai = drai
    (alphabeti: "'label list")
    (initiali: "'state")
    (transitioni: "'label \<Rightarrow> 'state \<Rightarrow> 'state")
    (conditioni: "'state rabin gen")

  definition drai_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1) drai \<times> ('label\<^sub>2, 'state\<^sub>2) drai) set" where
    [to_relAPP]: "drai_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabeti A\<^sub>1, alphabeti A\<^sub>2) \<in> \<langle>L\<rangle> list_rel \<and>
      (initiali A\<^sub>1, initiali A\<^sub>2) \<in> S \<and>
      (transitioni A\<^sub>1, transitioni A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> S \<and>
      (conditioni A\<^sub>1, conditioni A\<^sub>2) \<in> \<langle>rabin_rel S\<rangle> list_rel}"

  lemma drai_param[param]:
    "(drai, drai) \<in> \<langle>L\<rangle> list_rel \<rightarrow> S \<rightarrow> (L \<rightarrow> S \<rightarrow> S) \<rightarrow>
      \<langle>rabin_rel S\<rangle> list_rel \<rightarrow> \<langle>L, S\<rangle> drai_rel"
    "(alphabeti, alphabeti) \<in> \<langle>L, S\<rangle> drai_rel \<rightarrow> \<langle>L\<rangle> list_rel"
    "(initiali, initiali) \<in> \<langle>L, S\<rangle> drai_rel \<rightarrow> S"
    "(transitioni, transitioni) \<in> \<langle>L, S\<rangle> drai_rel \<rightarrow> L \<rightarrow> S \<rightarrow> S"
    "(conditioni, conditioni) \<in> \<langle>L, S\<rangle> drai_rel \<rightarrow> \<langle>rabin_rel S\<rangle> list_rel"
    unfolding drai_rel_def fun_rel_def by auto

  definition drai_dra_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1) drai \<times> ('label\<^sub>2, 'state\<^sub>2) dra) set" where
    [to_relAPP]: "drai_dra_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabeti A\<^sub>1, alphabet A\<^sub>2) \<in> \<langle>L\<rangle> list_set_rel \<and>
      (initiali A\<^sub>1, initial A\<^sub>2) \<in> S \<and>
      (transitioni A\<^sub>1, transition A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> S \<and>
      (conditioni A\<^sub>1, condition A\<^sub>2) \<in> \<langle>rabin_rel S\<rangle> list_rel}"

  lemma drai_dra_param[param, autoref_rules]:
    "(drai, dra) \<in> \<langle>L\<rangle> list_set_rel \<rightarrow> S \<rightarrow> (L \<rightarrow> S \<rightarrow> S) \<rightarrow>
      \<langle>rabin_rel S\<rangle> list_rel \<rightarrow> \<langle>L, S\<rangle> drai_dra_rel"
    "(alphabeti, alphabet) \<in> \<langle>L, S\<rangle> drai_dra_rel \<rightarrow> \<langle>L\<rangle> list_set_rel"
    "(initiali, initial) \<in> \<langle>L, S\<rangle> drai_dra_rel \<rightarrow> S"
    "(transitioni, transition) \<in> \<langle>L, S\<rangle> drai_dra_rel \<rightarrow> L \<rightarrow> S \<rightarrow> S"
    "(conditioni, condition) \<in> \<langle>L, S\<rangle> drai_dra_rel \<rightarrow> \<langle>rabin_rel S\<rangle> list_rel"
    unfolding drai_dra_rel_def fun_rel_def by auto

  definition drai_dra :: "('label, 'state) drai \<Rightarrow> ('label, 'state) dra" where
    "drai_dra A \<equiv> dra (set (alphabeti A)) (initiali A) (transitioni A) (conditioni A)"
  definition drai_invar :: "('label, 'state) drai \<Rightarrow> bool" where
    "drai_invar A \<equiv> distinct (alphabeti A)"

  lemma drai_dra_id_param[param]: "(drai_dra, id) \<in> \<langle>L, S\<rangle> drai_dra_rel \<rightarrow> \<langle>L, S\<rangle> dra_rel"
  proof
    fix Ai A
    assume 1: "(Ai, A) \<in> \<langle>L, S\<rangle> drai_dra_rel"
    have 2: "drai_dra Ai = dra (set (alphabeti Ai)) (initiali Ai) (transitioni Ai) (conditioni Ai)"
      unfolding drai_dra_def by rule
    have 3: "id A = dra (id (alphabet A)) (initial A) (transition A) (condition A)" by simp
    show "(drai_dra Ai, id A) \<in> \<langle>L, S\<rangle> dra_rel" unfolding 2 3 using 1 by parametricity
  qed

  lemma drai_dra_br: "\<langle>Id, Id\<rangle> drai_dra_rel = br drai_dra drai_invar"
  proof safe
    show "(A, B) \<in> \<langle>Id, Id\<rangle> drai_dra_rel" if "(A, B) \<in> br drai_dra drai_invar"
      for A and B :: "('a, 'b) dra"
      using that unfolding drai_dra_rel_def drai_dra_def drai_invar_def
      by (auto simp: in_br_conv list_set_rel_def)
    show "(A, B) \<in> br drai_dra drai_invar" if "(A, B) \<in> \<langle>Id, Id\<rangle> drai_dra_rel"
      for A and B :: "('a, 'b) dra"
    proof -
      have 1: "(drai_dra A, id B) \<in> \<langle>Id, Id\<rangle> dra_rel" using that by parametricity
      have 2: "drai_invar A"
        using drai_dra_param(2 - 5)[param_fo, OF that]
        by (auto simp: in_br_conv list_set_rel_def drai_invar_def)
      show ?thesis using 1 2 unfolding in_br_conv by auto
    qed
  qed

end