section \<open>Explicit Deterministic Rabin Automata\<close>

theory DRA_Explicit
imports DRA_Nodes
begin

  datatype ('label, 'state) drae = drae
    (alphabete: "'label set")
    (initiale: "'state")
    (transe: "('state \<times> 'label \<times> 'state) set")
    (acceptinge: "('state set \<times> 'state set) list")

  definition drae_rel where
    [to_relAPP]: "drae_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabete A\<^sub>1, alphabete A\<^sub>2) \<in> \<langle>L\<rangle> set_rel \<and>
      (initiale A\<^sub>1, initiale A\<^sub>2) \<in> S \<and>
      (transe A\<^sub>1, transe A\<^sub>2) \<in> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel \<and>
      (acceptinge A\<^sub>1, acceptinge A\<^sub>2) \<in> \<langle>\<langle>S\<rangle> set_rel \<times>\<^sub>r \<langle>S\<rangle> set_rel\<rangle> list_rel}"

  lemma drae_param[param, autoref_rules]:
    "(drae, drae) \<in> \<langle>L\<rangle> set_rel \<rightarrow> S \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel \<rightarrow>
      \<langle>\<langle>S\<rangle> set_rel \<times>\<^sub>r \<langle>S\<rangle> set_rel\<rangle> list_rel \<rightarrow> \<langle>L, S\<rangle> drae_rel"
    "(alphabete, alphabete) \<in> \<langle>L, S\<rangle> drae_rel \<rightarrow> \<langle>L\<rangle> set_rel"
    "(initiale, initiale) \<in> \<langle>L, S\<rangle> drae_rel \<rightarrow> S"
    "(transe, transe) \<in> \<langle>L, S\<rangle> drae_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel"
    "(acceptinge, acceptinge) \<in> \<langle>L, S\<rangle> drae_rel \<rightarrow> \<langle>\<langle>S\<rangle> set_rel \<times>\<^sub>r \<langle>S\<rangle> set_rel\<rangle> list_rel"
    unfolding drae_rel_def by auto

  lemma drae_rel_id[simp]: "\<langle>Id, Id\<rangle> drae_rel = Id" unfolding drae_rel_def using drae.expand by auto
  lemma drae_rel_comp[simp]: "\<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2\<rangle> drae_rel = \<langle>L\<^sub>1, S\<^sub>1\<rangle> drae_rel O \<langle>L\<^sub>2, S\<^sub>2\<rangle> drae_rel"
  proof safe
    fix A B
    assume 1: "(A, B) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2\<rangle> drae_rel"
    obtain a b c d where 2:
      "(alphabete A, a) \<in> \<langle>L\<^sub>1\<rangle> set_rel" "(a, alphabete B) \<in> \<langle>L\<^sub>2\<rangle> set_rel"
      "(initiale A, b) \<in> S\<^sub>1" "(b, initiale B) \<in> S\<^sub>2"
      "(transe A, c) \<in> \<langle>S\<^sub>1 \<times>\<^sub>r L\<^sub>1 \<times>\<^sub>r S\<^sub>1\<rangle> set_rel" "(c, transe B) \<in> \<langle>S\<^sub>2 \<times>\<^sub>r L\<^sub>2 \<times>\<^sub>r S\<^sub>2\<rangle> set_rel"
      "(acceptinge A, d) \<in> \<langle>\<langle>S\<^sub>1\<rangle> set_rel \<times>\<^sub>r \<langle>S\<^sub>1\<rangle> set_rel\<rangle> list_rel"
      "(d, acceptinge B) \<in> \<langle>\<langle>S\<^sub>2\<rangle> set_rel \<times>\<^sub>r \<langle>S\<^sub>2\<rangle> set_rel\<rangle> list_rel"
      using 1 unfolding drae_rel_def prod_rel_compp set_rel_compp by auto
    show "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1\<rangle> drae_rel O \<langle>L\<^sub>2, S\<^sub>2\<rangle> drae_rel"
    proof
      show "(A, drae a b c d) \<in> \<langle>L\<^sub>1, S\<^sub>1\<rangle> drae_rel" using 2 unfolding drae_rel_def by auto
      show "(drae a b c d, B) \<in> \<langle>L\<^sub>2, S\<^sub>2\<rangle> drae_rel" using 2 unfolding drae_rel_def by auto
    qed
  next
    show "(A, C) \<in> \<langle>L\<^sub>1 O L\<^sub>2, S\<^sub>1 O S\<^sub>2\<rangle> drae_rel"
      if "(A, B) \<in> \<langle>L\<^sub>1, S\<^sub>1\<rangle> drae_rel" "(B, C) \<in> \<langle>L\<^sub>2, S\<^sub>2\<rangle> drae_rel" for A B C
      using that unfolding drae_rel_def prod_rel_compp set_rel_compp by auto
  qed

  (* TODO: why do we need all this setup? can't i_of_rel do the trick? *)
  consts i_drae_scheme :: "interface \<Rightarrow> interface \<Rightarrow> interface"

  context
  begin

    interpretation autoref_syn by this

    lemma drae_scheme_itype[autoref_itype]:
      "drae ::\<^sub>i \<langle>L\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i S \<rightarrow>\<^sub>i \<langle>\<langle>S, \<langle>L, S\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_set \<rightarrow>\<^sub>i
        \<langle>\<langle>\<langle>S\<rangle>\<^sub>i i_set, \<langle>S\<rangle>\<^sub>i i_set\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_list \<rightarrow>\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_drae_scheme"
      "alphabete ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_drae_scheme \<rightarrow>\<^sub>i \<langle>L\<rangle>\<^sub>i i_set"
      "initiale ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_drae_scheme \<rightarrow>\<^sub>i S"
      "transe ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_drae_scheme \<rightarrow>\<^sub>i \<langle>\<langle>S, \<langle>L, S\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_set"
      "acceptinge ::\<^sub>i \<langle>L, S\<rangle>\<^sub>i i_drae_scheme \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>S\<rangle>\<^sub>i i_set, \<langle>S\<rangle>\<^sub>i i_set\<rangle>\<^sub>i i_prod\<rangle>\<^sub>i i_list"
      by auto

  end

  datatype ('label, 'state) draei = draei
    (alphabetei: "'label list")
    (initialei: "'state")
    (transei: "('state \<times> 'label \<times> 'state) list")
    (acceptingei: "('state list \<times> 'state list) list")

  definition draei_rel where
    [to_relAPP]: "draei_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabetei A\<^sub>1, alphabetei A\<^sub>2) \<in> \<langle>L\<rangle> list_rel \<and>
      (initialei A\<^sub>1, initialei A\<^sub>2) \<in> S \<and>
      (transei A\<^sub>1, transei A\<^sub>2) \<in> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_rel \<and>
      (acceptingei A\<^sub>1, acceptingei A\<^sub>2) \<in> \<langle>\<langle>S\<rangle> list_rel \<times>\<^sub>r \<langle>S\<rangle> list_rel\<rangle> list_rel}"

  lemma draei_param[param, autoref_rules]:
    "(draei, draei) \<in> \<langle>L\<rangle> list_rel \<rightarrow> S \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_rel \<rightarrow>
      \<langle>\<langle>S\<rangle> list_rel \<times>\<^sub>r \<langle>S\<rangle> list_rel\<rangle> list_rel \<rightarrow> \<langle>L, S\<rangle> draei_rel"
    "(alphabetei, alphabetei) \<in> \<langle>L, S\<rangle> draei_rel \<rightarrow> \<langle>L\<rangle> list_rel"
    "(initialei, initialei) \<in> \<langle>L, S\<rangle> draei_rel \<rightarrow> S"
    "(transei, transei) \<in> \<langle>L, S\<rangle> draei_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_rel"
    "(acceptingei, acceptingei) \<in> \<langle>L, S\<rangle> draei_rel \<rightarrow> \<langle>\<langle>S\<rangle> list_rel \<times>\<^sub>r \<langle>S\<rangle> list_rel\<rangle> list_rel"
    unfolding draei_rel_def by auto

  definition draei_drae_rel where
    [to_relAPP]: "draei_drae_rel L S \<equiv> {(A\<^sub>1, A\<^sub>2).
      (alphabetei A\<^sub>1, alphabete A\<^sub>2) \<in> \<langle>L\<rangle> list_set_rel \<and>
      (initialei A\<^sub>1, initiale A\<^sub>2) \<in> S \<and>
      (transei A\<^sub>1, transe A\<^sub>2) \<in> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel \<and>
      (acceptingei A\<^sub>1, acceptinge A\<^sub>2) \<in> \<langle>\<langle>S\<rangle> list_set_rel \<times>\<^sub>r \<langle>S\<rangle> list_set_rel\<rangle> list_rel}"

  lemmas [autoref_rel_intf] = REL_INTFI[of draei_drae_rel i_drae_scheme]

  lemma draei_drae_param[param, autoref_rules]:
    "(draei, drae) \<in> \<langle>L\<rangle> list_set_rel \<rightarrow> S \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel \<rightarrow>
      \<langle>\<langle>S\<rangle> list_set_rel \<times>\<^sub>r \<langle>S\<rangle> list_set_rel\<rangle> list_rel \<rightarrow> \<langle>L, S\<rangle> draei_drae_rel"
    "(alphabetei, alphabete) \<in> \<langle>L, S\<rangle> draei_drae_rel \<rightarrow> \<langle>L\<rangle> list_set_rel"
    "(initialei, initiale) \<in> \<langle>L, S\<rangle> draei_drae_rel \<rightarrow> S"
    "(transei, transe) \<in> \<langle>L, S\<rangle> draei_drae_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> list_set_rel"
    "(acceptingei, acceptinge) \<in> \<langle>L, S\<rangle> draei_drae_rel \<rightarrow> \<langle>\<langle>S\<rangle> list_set_rel \<times>\<^sub>r \<langle>S\<rangle> list_set_rel\<rangle> list_rel"
    unfolding draei_drae_rel_def by auto

  definition draei_drae where
    "draei_drae A \<equiv> drae (set (alphabetei A)) (initialei A)
      (set (transei A)) (map (map_prod set set) (acceptingei A))"

  lemma draei_drae_id_param[param]: "(draei_drae, id) \<in> \<langle>L, S\<rangle> draei_drae_rel \<rightarrow> \<langle>L, S\<rangle> drae_rel"
  proof
    fix Ai A
    assume 1: "(Ai, A) \<in> \<langle>L, S\<rangle> draei_drae_rel"
    have 2: "draei_drae Ai = drae (set (alphabetei Ai)) (initialei Ai)
      (set (transei Ai)) (map (map_prod set set) (acceptingei Ai))" unfolding draei_drae_def by rule
    have 3: "id A = drae (id (alphabete A)) (initiale A)
      (id (transe A)) (map (map_prod id id) (acceptinge A))" by simp
    show "(draei_drae Ai, id A) \<in> \<langle>L, S\<rangle> drae_rel" unfolding 2 3 using 1 by parametricity
  qed

  abbreviation "transitions L S s \<equiv> \<Union> a \<in> L. \<Union> p \<in> S. {p} \<times> {a} \<times> {s a p}"
  abbreviation "succs T a p \<equiv> the_elem ((T `` {p}) `` {a})"

  definition wft :: "'label set \<Rightarrow> 'state set \<Rightarrow> ('state \<times> 'label \<times> 'state) set \<Rightarrow> bool" where
    "wft L S T \<equiv> \<forall> a \<in> L. \<forall> p \<in> S. is_singleton ((T `` {p}) `` {a})"

  lemma wft_param[param]:
    assumes "bijective S" "bijective L"
    shows "(wft, wft) \<in> \<langle>L\<rangle> set_rel \<rightarrow> \<langle>S\<rangle> set_rel \<rightarrow> \<langle>S \<times>\<^sub>r L \<times>\<^sub>r S\<rangle> set_rel \<rightarrow> bool_rel"
    using assms unfolding wft_def by parametricity

  lemma wft_transitions: "wft L S (transitions L S s)" unfolding wft_def is_singleton_def by auto

  definition dra_drae where "dra_drae A \<equiv> drae (alphabet A) (initial A) 
    (transitions (alphabet A) (nodes A) (succ A))
    (map (\<lambda> (P, Q). (Set.filter P (nodes A), Set.filter Q (nodes A))) (accepting A))"
  definition drae_dra where "drae_dra A \<equiv> dra (alphabete A) (initiale A)
    (succs (transe A)) (map (\<lambda> (I, F). (\<lambda> p. p \<in> I, \<lambda> p. p \<in> F)) (acceptinge A))"

  lemma set_rel_Domain_Range[intro!, simp]: "(Domain A, Range A) \<in> \<langle>A\<rangle> set_rel" unfolding set_rel_def by auto

  lemma dra_drae_param[param]: "(dra_drae, dra_drae) \<in> \<langle>L, S\<rangle> dra_rel \<rightarrow> \<langle>L, S\<rangle> drae_rel"
    unfolding dra_drae_def by parametricity
  lemma drae_dra_param[param]:
    assumes "bijective L" "bijective S"
    assumes "wft (Range L) (Range S) (transe B)"
    assumes [param]: "(A, B) \<in> \<langle>L, S\<rangle> drae_rel"
    shows "(drae_dra A, drae_dra B) \<in> \<langle>L, S\<rangle> dra_rel"
  proof -
    have 1: "(wft (Domain L) (Domain S) (transe A), wft (Range L) (Range S) (transe B)) \<in> bool_rel"
      using assms(1, 2) by parametricity auto
    have 2: "wft (Domain L) (Domain S) (transe A)" using assms(3) 1 by simp
    show ?thesis
      using assms(1 - 3) 2 assms(2)[unfolded bijective_alt]
      unfolding drae_dra_def wft_def
      by parametricity force+
  qed

  lemma succs_transitions_param[param]:
    "(succs \<circ> transitions L S, id) \<in> (Id_on L \<rightarrow> Id_on S \<rightarrow> Id_on S) \<rightarrow> (Id_on L \<rightarrow> Id_on S \<rightarrow> Id_on S)"
  proof
    fix f g
    assume 1[param]: "(f, g) \<in> Id_on L \<rightarrow> Id_on S \<rightarrow> Id_on S"
    show "((succs \<circ> transitions L S) f, id g) \<in> Id_on L \<rightarrow> Id_on S \<rightarrow> Id_on S"
    proof safe
      fix a p
      assume 2: "a \<in> L" "p \<in> S"
      have "(succs \<circ> transitions L S) f a p = succs (transitions L S f) a p" by simp
      also have "(transitions L S f `` {p}) `` {a} = {f a p}" using 2 by auto
      also have "the_elem \<dots> = f a p" by simp
      also have "(\<dots>, g a p) \<in> Id_on S" using 2 by parametricity auto
      finally show "(succs \<circ> transitions L S) f a p = id g a p" by simp
      show "id g a p \<in> S" using 1[param_fo] 2 by simp
    qed
  qed
  lemma drae_dra_dra_drae_param[param]:
    "((drae_dra \<circ> dra_drae) A, id A) \<in> \<langle>Id_on (alphabet A), Id_on (nodes A)\<rangle> dra_rel"
  proof -
    have [param]: "(\<lambda> (P, Q). (\<lambda> p. p \<in> Set.filter P (nodes A), \<lambda> p. p \<in> Set.filter Q (nodes A)), id) \<in>
      pred_rel (Id_on (nodes A)) \<times>\<^sub>r pred_rel (Id_on (nodes A)) \<rightarrow> rabin_rel (Id_on (nodes A))"
      unfolding fun_rel_def Id_on_def by auto
    have "(drae_dra \<circ> dra_drae) A = dra (alphabet A) (initial A)
      ((succs \<circ> transitions (alphabet A) (nodes A)) (succ A))
      (map (\<lambda> (P, Q). (\<lambda> p. p \<in> Set.filter P (nodes A), \<lambda> p. p \<in> Set.filter Q (nodes A))) (accepting A))"
      unfolding drae_dra_def dra_drae_def by auto
    also have "(\<dots>, dra (alphabet A) (initial A) (id (succ A)) (map id (accepting A))) \<in>
      \<langle>Id_on (alphabet A), Id_on (nodes A)\<rangle> dra_rel" using dra_rel_eq by parametricity auto
    also have "dra (alphabet A) (initial A) (id (succ A)) (map id (accepting A)) = id A" by simp
    finally show ?thesis by this
  qed

  definition draei_dra_rel where
    [to_relAPP]: "draei_dra_rel L S \<equiv> {(Ae, A). (drae_dra (draei_drae Ae), A) \<in> \<langle>L, S\<rangle> dra_rel}"
  lemma draei_dra_id[param]: "(drae_dra \<circ> draei_drae, id) \<in> \<langle>L, S\<rangle> draei_dra_rel \<rightarrow> \<langle>L, S\<rangle> dra_rel"
    unfolding draei_dra_rel_def by auto

(*
  schematic_goal drae_dra_impl: "(?f, drae_dra) \<in> \<langle>Id, Id\<rangle> draei_drae_rel \<rightarrow> \<langle>Id, Id\<rangle> drai_dra_rel"
    unfolding drae_dra_def by (autoref (trace))
  concrete_definition drae_dra_impl uses drae_dra_impl
*)

end