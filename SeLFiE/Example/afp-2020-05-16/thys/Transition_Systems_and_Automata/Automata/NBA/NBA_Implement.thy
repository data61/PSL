section \<open>Implementation of Nondeterministic Büchi Automata\<close>

theory NBA_Implement
imports
  "NBA_Refine"
  "../../Basic/Implement"
begin

  consts i_nba_scheme :: "interface \<Rightarrow> interface \<Rightarrow> interface"

  context
  begin

    interpretation autoref_syn by this

    lemma nba_scheme_itype[autoref_itype]:
      "nba ::\<^sub>i \<langle>L\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i (L \<rightarrow>\<^sub>i S \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set) \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i
        \<langle>L, S\<rangle>\<^sub>i i_nba_scheme"
      "alphabet ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_nba_scheme \<rightarrow>\<^sub>i \<langle>L\<rangle>\<^sub>i i_set"
      "initial ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_nba_scheme \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      "transition ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_nba_scheme \<rightarrow>\<^sub>i L \<rightarrow>\<^sub>i S \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      "accepting ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_nba_scheme \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      by auto

  end

  datatype ('label, 'state) nbai = nbai
    (alphabeti: "'label list")
    (initiali: "'state list")
    (transitioni: "'label \<Rightarrow> 'state \<Rightarrow> 'state list")
    (acceptingi: "'state \<Rightarrow> bool")

  definition nbai_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1) nbai \<times> ('label\<^sub>2, 'state\<^sub>2) nbai) set" where
    [to_relAPP]: "nbai_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabeti A\<^sub>1, alphabeti A\<^sub>2) \<in> \<langle>L\<rangle> list_rel \<and>
      (initiali A\<^sub>1, initiali A\<^sub>2) \<in> \<langle>S\<rangle> list_rel \<and>
      (transitioni A\<^sub>1, transitioni A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_rel \<and>
      (acceptingi A\<^sub>1, acceptingi A\<^sub>2) \<in> S \<rightarrow> bool_rel}"

  lemma nbai_param[param, autoref_rules]:
    "(nbai, nbai) \<in> \<langle>L\<rangle> list_rel \<rightarrow> \<langle>S\<rangle> list_rel \<rightarrow> (L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_rel) \<rightarrow>
      (S \<rightarrow> bool_rel) \<rightarrow> \<langle>L, S\<rangle> nbai_rel"
    "(alphabeti, alphabeti) \<in> \<langle>L, S\<rangle> nbai_rel \<rightarrow> \<langle>L\<rangle> list_rel"
    "(initiali, initiali) \<in> \<langle>L, S\<rangle> nbai_rel \<rightarrow> \<langle>S\<rangle> list_rel"
    "(transitioni, transitioni) \<in> \<langle>L, S\<rangle> nbai_rel \<rightarrow> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_rel"
    "(acceptingi, acceptingi) \<in> \<langle>L, S\<rangle> nbai_rel \<rightarrow> (S \<rightarrow> bool_rel)"
    unfolding nbai_rel_def fun_rel_def by auto

  definition nbai_nba_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1) nbai \<times> ('label\<^sub>2, 'state\<^sub>2) nba) set" where
    [to_relAPP]: "nbai_nba_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabeti A\<^sub>1, alphabet A\<^sub>2) \<in> \<langle>L\<rangle> list_set_rel \<and>
      (initiali A\<^sub>1, initial A\<^sub>2) \<in> \<langle>S\<rangle> list_set_rel \<and>
      (transitioni A\<^sub>1, transition A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_set_rel \<and>
      (acceptingi A\<^sub>1, accepting A\<^sub>2) \<in> S \<rightarrow> bool_rel}"

  lemmas [autoref_rel_intf] = REL_INTFI[of nbai_nba_rel i_nba_scheme]

  (* TODO: why is there a warning? *)
  lemma nbai_nba_param[param, autoref_rules]:
    "(nbai, nba) \<in> \<langle>L\<rangle> list_set_rel \<rightarrow> \<langle>S\<rangle> list_set_rel \<rightarrow> (L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_set_rel) \<rightarrow>
      (S \<rightarrow> bool_rel) \<rightarrow> \<langle>L, S\<rangle> nbai_nba_rel"
    "(alphabeti, alphabet) \<in> \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>L\<rangle> list_set_rel"
    "(initiali, initial) \<in> \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(transitioni, transition) \<in> \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(acceptingi, accepting) \<in> \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> S \<rightarrow> bool_rel"
    unfolding nbai_nba_rel_def fun_rel_def by auto

  definition nbai_nba :: "('label, 'state) nbai \<Rightarrow> ('label, 'state) nba" where
    "nbai_nba A \<equiv> nba (set (alphabeti A)) (set (initiali A)) (\<lambda> a p. set (transitioni A a p)) (acceptingi A)"
  definition nbai_invar :: "('label, 'state) nbai \<Rightarrow> bool" where
    "nbai_invar A \<equiv> distinct (alphabeti A) \<and> distinct (initiali A) \<and> (\<forall> a p. distinct (transitioni A a p))"

  lemma nbai_nba_id_param[param]: "(nbai_nba, id) \<in> \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>L, S\<rangle> nba_rel"
  proof
    fix Ai A
    assume 1: "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
    have 2: "nbai_nba Ai = nba (set (alphabeti Ai)) (set (initiali Ai))
      (\<lambda> a p. set (transitioni Ai a p)) (acceptingi Ai)" unfolding nbai_nba_def by rule
    have 3: "id A = nba (id (alphabet A)) (id (initial A))
      (\<lambda> a p. id (transition A a p)) (accepting A)" by simp
    show "(nbai_nba Ai, id A) \<in> \<langle>L, S\<rangle> nba_rel" unfolding 2 3 using 1 by parametricity
  qed

  lemma nbai_nba_br: "\<langle>Id, Id\<rangle> nbai_nba_rel = br nbai_nba nbai_invar"
  proof safe
    show "(A, B) \<in> \<langle>Id, Id\<rangle> nbai_nba_rel" if "(A, B) \<in> br nbai_nba nbai_invar"
      for A and B :: "('a, 'b) nba"
      using that unfolding nbai_nba_rel_def nbai_nba_def nbai_invar_def
      by (auto simp: in_br_conv list_set_rel_def)
    show "(A, B) \<in> br nbai_nba nbai_invar" if "(A, B) \<in> \<langle>Id, Id\<rangle> nbai_nba_rel"
      for A and B :: "('a, 'b) nba"
    proof -
      have 1: "(nbai_nba A, id B) \<in> \<langle>Id, Id\<rangle> nba_rel" using that by parametricity
      have 2: "nbai_invar A"
        using nbai_nba_param(2 - 5)[param_fo, OF that]
        by (auto simp: in_br_conv list_set_rel_def nbai_invar_def)
      show ?thesis using 1 2 unfolding in_br_conv by auto
    qed
  qed

end