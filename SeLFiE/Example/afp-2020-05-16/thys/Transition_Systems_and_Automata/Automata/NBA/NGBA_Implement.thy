section \<open>Implementation of Nondeterministic Generalized Büchi Automata\<close>

theory NGBA_Implement
imports
  "NGBA_Refine"
  "../../Basic/Implement"
begin

  consts i_ngba_scheme :: "interface \<Rightarrow> interface \<Rightarrow> interface"

  context
  begin

    interpretation autoref_syn by this

    lemma ngba_scheme_itype[autoref_itype]:
      "ngba ::\<^sub>i \<langle>L\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i (L \<rightarrow>\<^sub>i S \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set) \<rightarrow>\<^sub>i \<langle>\<langle>S\<rangle>\<^sub>i i_set\<rangle>\<^sub>i i_list \<rightarrow>\<^sub>i
        \<langle>L, S\<rangle>\<^sub>i i_ngba_scheme"
      "alphabet ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_ngba_scheme \<rightarrow>\<^sub>i \<langle>L\<rangle>\<^sub>i i_set"
      "initial ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_ngba_scheme \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      "transition ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_ngba_scheme \<rightarrow>\<^sub>i L \<rightarrow>\<^sub>i S \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      "accepting ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_ngba_scheme \<rightarrow>\<^sub>i \<langle>\<langle>S\<rangle>\<^sub>i i_set\<rangle>\<^sub>i i_list"
      by auto

  end

  datatype ('label, 'state) ngbai = ngbai
    (alphabeti: "'label list")
    (initiali: "'state list")
    (transitioni: "'label \<Rightarrow> 'state \<Rightarrow> 'state list")
    (acceptingi: "('state \<Rightarrow> bool) list")

  definition ngbai_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1) ngbai \<times> ('label\<^sub>2, 'state\<^sub>2) ngbai) set" where
    [to_relAPP]: "ngbai_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabeti A\<^sub>1, alphabeti A\<^sub>2) \<in> \<langle>L\<rangle> list_rel \<and>
      (initiali A\<^sub>1, initiali A\<^sub>2) \<in> \<langle>S\<rangle> list_rel \<and>
      (transitioni A\<^sub>1, transitioni A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_rel \<and>
      (acceptingi A\<^sub>1, acceptingi A\<^sub>2) \<in> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel}"

  lemma ngbai_param[param]:
    "(ngbai, ngbai) \<in> \<langle>L\<rangle> list_rel \<rightarrow> \<langle>S\<rangle> list_rel \<rightarrow> (L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_rel) \<rightarrow>
      \<langle>S \<rightarrow> bool_rel\<rangle> list_rel \<rightarrow> \<langle>L, S\<rangle> ngbai_rel"
    "(alphabeti, alphabeti) \<in> \<langle>L, S\<rangle> ngbai_rel \<rightarrow> \<langle>L\<rangle> list_rel"
    "(initiali, initiali) \<in> \<langle>L, S\<rangle> ngbai_rel \<rightarrow> \<langle>S\<rangle> list_rel"
    "(transitioni, transitioni) \<in> \<langle>L, S\<rangle> ngbai_rel \<rightarrow> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_rel"
    "(acceptingi, acceptingi) \<in> \<langle>L, S\<rangle> ngbai_rel \<rightarrow> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel"
    unfolding ngbai_rel_def fun_rel_def by auto

  definition ngbai_ngba_rel :: "('label\<^sub>1 \<times> 'label\<^sub>2) set \<Rightarrow> ('state\<^sub>1 \<times> 'state\<^sub>2) set \<Rightarrow>
    (('label\<^sub>1, 'state\<^sub>1) ngbai \<times> ('label\<^sub>2, 'state\<^sub>2) ngba) set" where
    [to_relAPP]: "ngbai_ngba_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabeti A\<^sub>1, alphabet A\<^sub>2) \<in> \<langle>L\<rangle> list_set_rel \<and>
      (initiali A\<^sub>1, initial A\<^sub>2) \<in> \<langle>S\<rangle> list_set_rel \<and>
      (transitioni A\<^sub>1, transition A\<^sub>2) \<in> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_set_rel \<and>
      (acceptingi A\<^sub>1, accepting A\<^sub>2) \<in> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel}"

  lemmas [autoref_rel_intf] = REL_INTFI[of ngbai_ngba_rel i_ngba_scheme]

  lemma ngbai_ngba_param[param, autoref_rules]:
    "(ngbai, ngba) \<in> \<langle>L\<rangle> list_set_rel \<rightarrow> \<langle>S\<rangle> list_set_rel \<rightarrow> (L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_set_rel) \<rightarrow>
      \<langle>S \<rightarrow> bool_rel\<rangle> list_rel \<rightarrow> \<langle>L, S\<rangle> ngbai_ngba_rel"
    "(alphabeti, alphabet) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel \<rightarrow> \<langle>L\<rangle> list_set_rel"
    "(initiali, initial) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(transitioni, transition) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel \<rightarrow> L \<rightarrow> S \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(acceptingi, accepting) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel \<rightarrow> \<langle>S \<rightarrow> bool_rel\<rangle> list_rel"
    unfolding ngbai_ngba_rel_def fun_rel_def by auto

  definition ngbai_ngba :: "('label, 'state) ngbai \<Rightarrow> ('label, 'state) ngba" where
    "ngbai_ngba A \<equiv> ngba (set (alphabeti A)) (set (initiali A)) (\<lambda> a p. set (transitioni A a p)) (acceptingi A)"
  definition ngbai_invar :: "('label, 'state) ngbai \<Rightarrow> bool" where
    "ngbai_invar A \<equiv> distinct (alphabeti A) \<and> distinct (initiali A) \<and> (\<forall> a p. distinct (transitioni A a p))"

  lemma ngbai_ngba_id_param[param]: "(ngbai_ngba, id) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel \<rightarrow> \<langle>L, S\<rangle> ngba_rel"
  proof
    fix Ai A
    assume 1: "(Ai, A) \<in> \<langle>L, S\<rangle> ngbai_ngba_rel"
    have 2: "ngbai_ngba Ai = ngba (set (alphabeti Ai)) (set (initiali Ai))
      (\<lambda> a p. set (transitioni Ai a p)) (acceptingi Ai)" unfolding ngbai_ngba_def by rule
    have 3: "id A = ngba (id (alphabet A)) (id (initial A))
      (\<lambda> a p. id (transition A a p)) (accepting A)" by simp
    show "(ngbai_ngba Ai, id A) \<in> \<langle>L, S\<rangle> ngba_rel" unfolding 2 3 using 1 by parametricity
  qed

  lemma ngbai_ngba_br: "\<langle>Id, Id\<rangle> ngbai_ngba_rel = br ngbai_ngba ngbai_invar"
  proof safe
    show "(A, B) \<in> \<langle>Id, Id\<rangle> ngbai_ngba_rel" if "(A, B) \<in> br ngbai_ngba ngbai_invar"
      for A and B :: "('a, 'b) ngba"
      using that unfolding ngbai_ngba_rel_def ngbai_ngba_def ngbai_invar_def
      by (auto simp: in_br_conv list_set_rel_def)
    show "(A, B) \<in> br ngbai_ngba ngbai_invar" if "(A, B) \<in> \<langle>Id, Id\<rangle> ngbai_ngba_rel"
      for A and B :: "('a, 'b) ngba"
    proof -
      have 1: "(ngbai_ngba A, id B) \<in> \<langle>Id, Id\<rangle> ngba_rel" using that by parametricity
      have 2: "ngbai_invar A"
        using ngbai_ngba_param(2 - 5)[param_fo, OF that]
        by (auto simp: in_br_conv list_set_rel_def ngbai_invar_def)
      show ?thesis using 1 2 unfolding in_br_conv by auto
    qed
  qed

end