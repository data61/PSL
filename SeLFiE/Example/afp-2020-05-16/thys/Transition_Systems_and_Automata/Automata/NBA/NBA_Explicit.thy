section \<open>Explicit Nondeterministic Büchi Automata\<close>

theory NBA_Explicit
imports NBA_Algorithms
begin

  datatype ('label, 'state) nbae = nbae
    (alphabete: "'label set")
    (initiale: "'state set")
    (transitione: "('state \<times> 'label \<times> 'state) set")
    (acceptinge: "'state set")

  definition nbae_rel where
    [to_relAPP]: "nbae_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabete A\<^sub>1, alphabete A\<^sub>2) \<in> \<langle>L\<rangle> set_rel \<and>
      (initiale A\<^sub>1, initiale A\<^sub>2) \<in> \<langle>S\<rangle> set_rel \<and>
      (transitione A\<^sub>1, transitione A\<^sub>2) \<in> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel \<and>
      (acceptinge A\<^sub>1, acceptinge A\<^sub>2) \<in> \<langle>S\<rangle> set_rel}"

  lemma nbae_param[param, autoref_rules]:
    "(nbae, nbae) \<in> \<langle>L\<rangle> set_rel \<rightarrow> \<langle>S\<rangle> set_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel \<rightarrow>
      \<langle>S\<rangle> set_rel \<rightarrow> \<langle>L, S\<rangle> nbae_rel"
    "(alphabete, alphabete) \<in> \<langle>L, S\<rangle> nbae_rel \<rightarrow> \<langle>L\<rangle> set_rel"
    "(initiale, initiale) \<in> \<langle>L, S\<rangle> nbae_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    "(transitione, transitione) \<in> \<langle>L, S\<rangle> nbae_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel"
    "(acceptinge, acceptinge) \<in> \<langle>L, S\<rangle> nbae_rel \<rightarrow> \<langle>S\<rangle> set_rel"
    unfolding nbae_rel_def by auto

  lemma nbae_rel_id[simp]: "\<langle>Id, Id\<rangle> nbae_rel = Id" unfolding nbae_rel_def using nbae.expand by auto
  lemma nbae_rel_comp[simp]: "\<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2\<rangle> nbae_rel = \<langle>L\<^sub>1, S\<^sub>1\<rangle> nbae_rel O \<langle>L\<^sub>2, S\<^sub>2\<rangle> nbae_rel"
  proof safe
    fix A B
    assume 1: "(A, B) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2\<rangle> nbae_rel"
    obtain a b c d where 2:
      "(alphabete A, a) \<in> \<langle>L\<^sub>1\<rangle> set_rel" "(a, alphabete B) \<in> \<langle>L\<^sub>2\<rangle> set_rel"
      "(initiale A, b) \<in> \<langle>S\<^sub>1\<rangle> set_rel" "(b, initiale B) \<in> \<langle>S\<^sub>2\<rangle> set_rel"
      "(transitione A, c) \<in> \<langle>S\<^sub>1 \<times>\<^sub>r L\<^sub>1 \<times>\<^sub>r S\<^sub>1\<rangle> set_rel" "(c, transitione B) \<in> \<langle>S\<^sub>2 \<times>\<^sub>r L\<^sub>2 \<times>\<^sub>r S\<^sub>2\<rangle> set_rel"
      "(acceptinge A, d) \<in> \<langle>S\<^sub>1\<rangle> set_rel" "(d, acceptinge B) \<in> \<langle>S\<^sub>2\<rangle> set_rel"
      using 1 unfolding nbae_rel_def prod_rel_compp set_rel_compp by auto
    show "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1\<rangle> nbae_rel O \<langle>L\<^sub>2, S\<^sub>2\<rangle> nbae_rel"
    proof
      show "(A, nbae a b c d) \<in> \<langle>L\<^sub>1, S\<^sub>1\<rangle> nbae_rel" using 2 unfolding nbae_rel_def by auto
      show "(nbae a b c d, B) \<in> \<langle>L\<^sub>2, S\<^sub>2\<rangle> nbae_rel" using 2 unfolding nbae_rel_def by auto
    qed
  next
    show "(A, C) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2\<rangle> nbae_rel"
      if "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1\<rangle> nbae_rel" "(B, C) \<in> \<langle>L\<^sub>2, S\<^sub>2\<rangle> nbae_rel" for A B C
      using that unfolding nbae_rel_def prod_rel_compp set_rel_compp by auto
  qed

  (* TODO: why do we need all this setup? can't i_of_rel do the trick? *)
  consts i_nbae_scheme :: "interface \<Rightarrow> interface \<Rightarrow> interface"

  context
  begin

    interpretation autoref_syn by this

    lemma nbae_scheme_itype[autoref_itype]:
      "nbae ::\<^sub>i \<langle>L\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>\<langle>S, \<langle>L, S\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i
        \<langle>L, S\<rangle>\<^sub>i i_nbae_scheme"
      "alphabete ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_nbae_scheme \<rightarrow>\<^sub>i \<langle>L\<rangle>\<^sub>i i_set"
      "initiale ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_nbae_scheme \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      "transitione ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_nbae_scheme \<rightarrow>\<^sub>i \<langle>\<langle>S, \<langle>L, S\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_set"
      "acceptinge ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_nbae_scheme \<rightarrow>\<^sub>i \<langle>S\<rangle>\<^sub>i i_set"
      by auto

  end

  datatype ('label, 'state) nbaei = nbaei
    (alphabetei: "'label list")
    (initialei: "'state list")
    (transitionei: "('state \<times> 'label \<times> 'state) list")
    (acceptingei: "'state list")

  definition nbaei_rel where
    [to_relAPP]: "nbaei_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabetei A\<^sub>1, alphabetei A\<^sub>2) \<in> \<langle>L\<rangle> list_rel \<and>
      (initialei A\<^sub>1, initialei A\<^sub>2) \<in> \<langle>S\<rangle> list_rel \<and>
      (transitionei A\<^sub>1, transitionei A\<^sub>2) \<in> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_rel \<and>
      (acceptingei A\<^sub>1, acceptingei A\<^sub>2) \<in> \<langle>S\<rangle> list_rel}"

  lemma nbaei_param[param, autoref_rules]:
    "(nbaei, nbaei) \<in> \<langle>L\<rangle> list_rel \<rightarrow> \<langle>S\<rangle> list_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_rel \<rightarrow>
      \<langle>S\<rangle> list_rel \<rightarrow> \<langle>L, S\<rangle> nbaei_rel"
    "(alphabetei, alphabetei) \<in> \<langle>L, S\<rangle> nbaei_rel \<rightarrow> \<langle>L\<rangle> list_rel"
    "(initialei, initialei) \<in> \<langle>L, S\<rangle> nbaei_rel \<rightarrow> \<langle>S\<rangle> list_rel"
    "(transitionei, transitionei) \<in> \<langle>L, S\<rangle> nbaei_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_rel"
    "(acceptingei, acceptingei) \<in> \<langle>L, S\<rangle> nbaei_rel \<rightarrow> \<langle>S\<rangle> list_rel"
    unfolding nbaei_rel_def by auto

  definition nbaei_nbae_rel where
    [to_relAPP]: "nbaei_nbae_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabetei A\<^sub>1, alphabete A\<^sub>2) \<in> \<langle>L\<rangle> list_set_rel \<and>
      (initialei A\<^sub>1, initiale A\<^sub>2) \<in> \<langle>S\<rangle> list_set_rel \<and>
      (transitionei A\<^sub>1, transitione A\<^sub>2) \<in> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel \<and>
      (acceptingei A\<^sub>1, acceptinge A\<^sub>2) \<in> \<langle>S\<rangle> list_set_rel}"

  lemmas [autoref_rel_intf] = REL_INTFI[of nbaei_nbae_rel i_nbae_scheme]

  lemma nbaei_nbae_param[param, autoref_rules]:
    "(nbaei, nbae) \<in> \<langle>L\<rangle> list_set_rel \<rightarrow> \<langle>S\<rangle> list_set_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel \<rightarrow>
      \<langle>S\<rangle> list_set_rel \<rightarrow> \<langle>L, S\<rangle> nbaei_nbae_rel"
    "(alphabetei, alphabete) \<in> \<langle>L, S\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>L\<rangle> list_set_rel"
    "(initialei, initiale) \<in> \<langle>L, S\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>S\<rangle> list_set_rel"
    "(transitionei, transitione) \<in> \<langle>L, S\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel"
    "(acceptingei, acceptinge) \<in> \<langle>L, S\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>S\<rangle> list_set_rel"
    unfolding nbaei_nbae_rel_def by auto

  definition nbaei_nbae where
    "nbaei_nbae A \<equiv> nbae (set (alphabetei A)) (set (initialei A))
      (set (transitionei A)) (set (acceptingei A))"

  lemma nbaei_nbae_id_param[param]: "(nbaei_nbae, id) \<in> \<langle>L, S\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>L, S\<rangle> nbae_rel"
  proof
    fix Ai A
    assume 1: "(Ai, A) \<in> \<langle>L, S\<rangle> nbaei_nbae_rel"
    have 2: "nbaei_nbae Ai = nbae (set (alphabetei Ai)) (set (initialei Ai))
      (set (transitionei Ai)) (set (acceptingei Ai))" unfolding nbaei_nbae_def by rule
    have 3: "id A = nbae (id (alphabete A)) (id (initiale A))
      (id (transitione A)) (id (acceptinge A))" by simp
    show "(nbaei_nbae Ai, id A) \<in> \<langle>L, S\<rangle> nbae_rel" unfolding 2 3 using 1 by parametricity
  qed

  abbreviation "transitions L S s \<equiv> \<Union> a \<in> L. \<Union> p \<in> S. {p} \<times> {a} \<times> s a p"
  abbreviation "succs T a p \<equiv> (T `` {p}) `` {a}"

  definition nba_nbae where "nba_nbae A \<equiv> nbae (alphabet A) (initial A)
    (transitions (alphabet A) (nodes A) (transition A)) (Set.filter (accepting A) (nodes A))"
  definition nbae_nba where "nbae_nba A \<equiv> nba (alphabete A) (initiale A)
    (succs (transitione A)) (\<lambda> p. p \<in> acceptinge A)"

  lemma nba_nbae_param[param]: "(nba_nbae, nba_nbae) \<in> \<langle>L, S\<rangle> nba_rel \<rightarrow> \<langle>L, S\<rangle> nbae_rel"
    unfolding nba_nbae_def by parametricity
  lemma nbae_nba_param[param]:
    assumes "bijective L" "bijective S"
    shows "(nbae_nba, nbae_nba) \<in> \<langle>L, S\<rangle> nbae_rel \<rightarrow> \<langle>L, S\<rangle> nba_rel"
    using assms assms(2)[unfolded bijective_alt] unfolding nbae_nba_def by parametricity auto

  lemma nbae_nba_nba_nbae_param[param]:
    "((nbae_nba \<circ> nba_nbae) A, id A) \<in> \<langle>Id_on (alphabet A), Id_on (nodes A)\<rangle> nba_rel"
  proof -
    have "(nbae_nba \<circ> nba_nbae) A = nba (alphabet A) (initial A)
      (succs (transitions (alphabet A) (nodes A) (transition A))) (\<lambda> p. p \<in> Set.filter (accepting A) (nodes A))"
      unfolding nbae_nba_def nba_nbae_def by simp
    also have "(\<dots>, nba (alphabet A) (initial A) (transition A) (accepting A)) \<in>
      \<langle>Id_on (alphabet A), Id_on (nodes A)\<rangle> nba_rel"
      using nba_rel_eq by parametricity auto
    also have  "nba (alphabet A) (initial A) (transition A) (accepting A) = id A" by simp
    finally show ?thesis by this
  qed

  definition nbaei_nba_rel where
    [to_relAPP]: "nbaei_nba_rel L S \<equiv> {(Ae, A). (nbae_nba (nbaei_nbae Ae), A) \<in> \<langle>L, S\<rangle> nba_rel}"
  lemma nbaei_nba_id[param]: "(nbae_nba \<circ> nbaei_nbae, id) \<in> \<langle>L, S\<rangle> nbaei_nba_rel \<rightarrow> \<langle>L, S\<rangle> nba_rel"
    unfolding nbaei_nba_rel_def by auto

  schematic_goal nbae_nba_impl:
    assumes [autoref_rules]: "(leq, HOL.eq) \<in> L \<rightarrow> L \<rightarrow> bool_rel"
    assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
    shows "(?f, nbae_nba) \<in> \<langle>L, S\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>L, S\<rangle> nbai_nba_rel"
    unfolding nbae_nba_def by autoref
  concrete_definition nbae_nba_impl uses nbae_nba_impl
  lemma nbae_nba_impl_refine[autoref_rules]:
    assumes "GEN_OP leq HOL.eq (L \<rightarrow> L \<rightarrow> bool_rel)"
    assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
    shows "(nbae_nba_impl leq seq, nbae_nba) \<in> \<langle>L, S\<rangle> nbaei_nbae_rel \<rightarrow> \<langle>L, S\<rangle> nbai_nba_rel"
    using nbae_nba_impl.refine assms unfolding autoref_tag_defs by this

end