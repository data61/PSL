section \<open>Explore and Enumerate Nodes of Nondeterministic Büchi Automata\<close>

theory NBA_Translate
imports NBA_Explicit
begin

  subsection \<open>Syntax\<close>

  (* TODO: this syntax has unnecessarily high inner binding strength, requiring extra parentheses
    the regular let syntax correctly uses inner binding strength 0: ("(2_ =/ _)" 10) *)
  no_syntax "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" [1000, 13] 13)
  syntax "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" 13)

  section \<open>Image on Explicit Automata\<close>

  (* TODO: this should not be needed, only use nba_image *)
  definition nbae_image where "nbae_image f A \<equiv> nbae (alphabete A) (f ` initiale A)
    ((\<lambda> (p, a, q). (f p, a, f q)) ` transitione A) (f ` acceptinge A)"

  lemma nbae_image_param[param]: "(nbae_image, nbae_image) \<in> (S \<rightarrow> T) \<rightarrow> \<langle>L, S\<rangle> nbae_rel \<rightarrow> \<langle>L, T\<rangle> nbae_rel"
    unfolding nbae_image_def by parametricity

  lemma nbae_image_id[simp]: "nbae_image id = id" unfolding nbae_image_def by auto
  lemma nbae_image_nba_nbae: "nbae_image f (nba_nbae A) = nbae
    (alphabet A) (f ` initial A)
    (\<Union> p \<in> nodes A. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p)
    (f ` {p \<in> nodes A. accepting A p})"
    unfolding nba_nbae_def nbae_image_def nbae.simps Set.filter_def by force

  section \<open>Exploration and Translation\<close>

  definition trans_spec where
    "trans_spec A f \<equiv> \<Union> p \<in> nodes A. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p"

  definition trans_algo where
    "trans_algo N L S f \<equiv>
      FOREACH N (\<lambda> p T. do {
        ASSERT (p \<in> N);
        FOREACH L (\<lambda> a T. do {
          ASSERT (a \<in> L);
          FOREACH (S a p) (\<lambda> q T. do {
            ASSERT (q \<in> S a p);
            ASSERT ((f p, a, f q) \<notin> T);
            RETURN (insert (f p, a, f q) T) }
          ) T }
        ) T }
      ) {}"

  lemma trans_algo_refine:
    assumes "finite (nodes A)" "finite (alphabet A)" "inj_on f (nodes A)"
    assumes "N = nodes A" "L = alphabet A" "S = transition A"
    shows "(trans_algo N L S f, SPEC (HOL.eq (trans_spec A f))) \<in> \<langle>Id\<rangle> nres_rel"
  unfolding trans_algo_def trans_spec_def assms(4-6)
  proof (refine_vcg FOREACH_rule_insert_eq)
    show "finite (nodes A)" using assms(1) by this
    show "(\<Union> p \<in> nodes A. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p) =
      (\<Union> p \<in> nodes A. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p)" by rule
    show "(\<Union> p \<in> {}. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p) = {}" by simp
    fix T x
    assume 1: "T \<subseteq> nodes A" "x \<in> nodes A" "x \<notin> T"
    show "finite (alphabet A)" using assms(2) by this
    show "(\<Union> a \<in> {}. f ` {x} \<times> {a} \<times> f ` transition A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p) =
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p)"
      "(\<Union> a \<in> alphabet A. f ` {x} \<times> {a} \<times> f ` transition A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p) =
      (\<Union> p \<in> insert x T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p)" by auto
    fix Ta xa
    assume 2: "Ta \<subseteq> alphabet A" "xa \<in> alphabet A" "xa \<notin> Ta"
    show "finite (transition A xa x)" using 1 2 assms(1) by (meson infinite_subset nba.nodes_transition subsetI)
    show "(f ` {x} \<times> {xa} \<times> f ` transition A xa x) \<union>
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` transition A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p) =
      (\<Union> a \<in> insert xa Ta. f ` {x} \<times> {a} \<times> f ` transition A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p)"
      by auto
    show "(f ` {x} \<times> {xa} \<times> f ` {}) \<union>
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` transition A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p) =
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` transition A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p)"
      by auto
    fix Tb xb
    assume 3: "Tb \<subseteq> transition A xa x" "xb \<in> transition A xa x" "xb \<notin> Tb"
    show "(f x, xa, f xb) \<notin> f ` {x} \<times> {xa} \<times> f ` Tb \<union>
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` transition A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p)"
      using 1 2 3 assms(3) by (blast dest: inj_onD)
    show "f ` {x} \<times> {xa} \<times> f ` insert xb Tb \<union>
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` transition A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p) =
      insert (f x, xa, f xb) (f ` {x} \<times> {xa} \<times> f ` Tb \<union>
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` transition A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` transition A a p))"
      by auto
  qed

  (* TODO: move this to nondeterministic automaton
    there, it will have to be treated more elementarily
    at least until we abstract from NBA_Refine to do that there aswell *)
  definition nba_image :: "('state\<^sub>1 \<Rightarrow> 'state\<^sub>2) \<Rightarrow> ('label, 'state\<^sub>1) nba \<Rightarrow> ('label, 'state\<^sub>2) nba" where
    "nba_image f A \<equiv> nba
      (alphabet A)
      (f ` initial A)
      (\<lambda> a p. f ` transition A a (inv_into (nodes A) f p))
      (\<lambda> p. accepting A (inv_into (nodes A) f p))"

  lemma nba_image_rel[param]:
    assumes "inj_on f (nodes A)"
    shows "(A, nba_image f A) \<in> \<langle>Id_on (alphabet A), br f (\<lambda> p. p \<in> nodes A)\<rangle> nba_rel"
  proof -
    have "A = nba (alphabet A) (initial A) (transition A) (accepting A)" by simp
    also have "(\<dots>, nba_image f A) \<in> \<langle>Id_on (alphabet A), br f (\<lambda> p. p \<in> nodes A)\<rangle> nba_rel"
      using assms unfolding nba_image_def
      by (parametricity) (auto intro: nba_rel_eq simp: in_br_conv br_set_rel_alt)
    finally show ?thesis by this
  qed

  lemma nba_image_nodes[simp]:
    assumes "inj_on f (nodes A)"
    shows "nodes (nba_image f A) = f ` nodes A"
  proof -
    have "(nodes A, nodes (nba_image f A)) \<in> \<langle>br f (\<lambda> p. p \<in> nodes A)\<rangle> set_rel"
      using assms by parametricity
    then show ?thesis unfolding br_set_rel_alt by simp
  qed
  lemma nba_image_language[simp]:
    assumes "inj_on f (nodes A)"
    shows "language (nba_image f A) = language A"
  proof -
    have "(language A, language (nba_image f A)) \<in> \<langle>\<langle>Id_on (alphabet A)\<rangle> stream_rel\<rangle> set_rel"
      using assms by parametricity
    then show ?thesis by simp
  qed

  lemma nba_image_nbae:
    assumes "inj_on f (nodes A)"
    shows "nbae_image f (nba_nbae A) = nba_nbae (nba_image f A)"
    unfolding nbae_image_nba_nbae
    unfolding nba_nbae_def
    unfolding nba_image_nodes[OF assms]
    unfolding nbae.simps
    unfolding nba_image_def
    unfolding nba.sel
    using assms by auto

  (* TODO: with this, maybe much of the nbae infrastructure is obsolete?
    since now there is very little happening in terms of relations, maybe we can even make do
    with just the abstraction function *)
  (* TODO: maybe the specification for translation is just that the translated automaton
    is related in \<langle>Id_on (alphabet A), ???\<rangle> nba_rel? *)
  definition op_translate :: "('label, 'state) nba \<Rightarrow> ('label, nat) nbae nres" where
    "op_translate A \<equiv> SPEC (\<lambda> B. \<exists> f. inj_on f (nodes A) \<and> B = nba_nbae (nba_image f A))"

  lemma op_translate_language:
    assumes "(RETURN Ai, op_translate A) \<in> \<langle>\<langle>Id, nat_rel\<rangle> nbaei_nbae_rel\<rangle> nres_rel"
    shows "language (nbae_nba (nbaei_nbae Ai)) = language A"
  proof -
    (* TODO: can we leave all this inside the nres without explicit obtain? *)
    obtain f where 1:
      "(Ai, nba_nbae (nba_image f A)) \<in> \<langle>Id, nat_rel\<rangle> nbaei_nbae_rel" "inj_on f (nodes A)"
      using assms[unfolded in_nres_rel_iff op_translate_def, THEN RETURN_ref_SPECD]
      by metis
    let ?C = "nba_image f A"
    have "(nbae_nba (nbaei_nbae Ai), nbae_nba (id (nba_nbae ?C))) \<in> \<langle>Id, nat_rel\<rangle> nba_rel"
      using 1(1) by parametricity auto
    also have "nbae_nba (id (nba_nbae ?C)) = (nbae_nba \<circ> nba_nbae) ?C" by simp
    also have "(\<dots>, id ?C) \<in> \<langle>Id_on (alphabet ?C), Id_on (nodes ?C)\<rangle> nba_rel" by parametricity
    finally have 2: "(nbae_nba (nbaei_nbae Ai), ?C) \<in>
      \<langle>Id_on (alphabet ?C), Id_on (nodes ?C)\<rangle> nba_rel" by simp
    have "(language (nbae_nba (nbaei_nbae Ai)), language ?C) \<in>
      \<langle>\<langle>Id_on (alphabet ?C)\<rangle> stream_rel\<rangle> set_rel"
      using 2 by parametricity
    also have "language ?C = language A" using 1(2) by simp
    finally show ?thesis by simp
  qed

  (* TODO: make separate implementations for "nba_nbae" and "op_set_enumerate \<bind> nbae_image"
    make sure to do regression tests along the way *)
  (* TODO: since we have translate_impl, maybe just having a good nba_nbae implementation is enough? *)
  schematic_goal to_nbaei_impl:
    fixes S :: "('statei \<times> 'state) set"
    assumes [simp]: "finite (nodes A)"
    assumes [autoref_ga_rules]: "is_bounded_hashcode S seq bhc"
    assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('statei) hms"
    assumes [autoref_rules]: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
    assumes [autoref_rules]: "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
    shows "(?f :: ?'a, do {
        let N = nodes A;
        f \<leftarrow> op_set_enumerate N;
        ASSERT (dom f = N);
        ASSERT (\<forall> p \<in> initial A. f p \<noteq> None);
        ASSERT (\<forall> a \<in> alphabet A. \<forall> p \<in> dom f. \<forall> q \<in> transition A a p. f q \<noteq> None);
        T \<leftarrow> trans_algo N (alphabet A) (transition A) (\<lambda> x. the (f x));
        RETURN (nbae (alphabet A) ((\<lambda> x. the (f x)) ` initial A) T
          ((\<lambda> x. the (f x)) ` {p \<in> N. accepting A p}))
      }) \<in> ?R"
    unfolding trans_algo_def by (autoref_monadic (plain))
  concrete_definition to_nbaei_impl uses to_nbaei_impl

  context
  begin

    interpretation autoref_syn by this

    lemma to_nbaei_impl_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_PRECOND (finite (nodes A))"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      assumes "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
      shows "(RETURN (to_nbaei_impl seq bhc hms Ai),
        (OP op_translate ::: \<langle>L, S\<rangle> nbai_nba_rel \<rightarrow> \<langle>\<langle>L, nat_rel\<rangle> nbaei_nbae_rel\<rangle> nres_rel) $ A) \<in>
        \<langle>\<langle>L, nat_rel\<rangle> nbaei_nbae_rel\<rangle> nres_rel"
    proof -
      have 1: "finite (alphabet A)"
        using nbai_nba_param(2)[param_fo, OF assms(5)] list_set_rel_finite
        unfolding finite_set_rel_def by auto
      note to_nbaei_impl.refine[OF assms[unfolded autoref_tag_defs]]
      also have "(do {
          let N = nodes A;
          f \<leftarrow> op_set_enumerate N;
          ASSERT (dom f = N);
          ASSERT (\<forall> p \<in> initial A. f p \<noteq> None);
          ASSERT (\<forall> a \<in> alphabet A. \<forall> p \<in> dom f. \<forall> q \<in> transition A a p. f q \<noteq> None);
          T \<leftarrow> trans_algo N (alphabet A) (transition A) (\<lambda> x. the (f x));
          RETURN (nbae (alphabet A) ((\<lambda> x. the (f x)) ` initial A) T ((\<lambda> x. the (f x)) ` {p \<in> N. accepting A p}))
        }, do {
          f \<leftarrow> op_set_enumerate (nodes A);
          T \<leftarrow> SPEC (HOL.eq (trans_spec A (\<lambda> x. the (f x))));
          RETURN (nbae (alphabet A) ((\<lambda> x. the (f x)) ` initial A) T ((\<lambda> x. the (f x)) ` {p \<in> nodes A. accepting A p}))
        }) \<in> \<langle>Id\<rangle> nres_rel"
        unfolding Let_def comp_apply op_set_enumerate_def using assms(1) 1
        by (refine_vcg vcg0[OF trans_algo_refine]) (auto intro!: inj_on_map_the[unfolded comp_apply])
      also have "(do {
          f \<leftarrow> op_set_enumerate (nodes A);
          T \<leftarrow> SPEC (HOL.eq (trans_spec A (\<lambda> x. the (f x))));
          RETURN (nbae (alphabet A) ((\<lambda> x. the (f x)) ` initial A) T ((\<lambda> x. the (f x)) ` {p \<in> nodes A. accepting A p}))
        }, do {
          f \<leftarrow> op_set_enumerate (nodes A);
          RETURN (nbae_image (the \<circ> f) (nba_nbae A))
        }) \<in> \<langle>Id\<rangle> nres_rel"
        unfolding trans_spec_def nbae_image_nba_nbae by refine_vcg force
      also have "(do {
          f \<leftarrow> op_set_enumerate (nodes A);
          RETURN (nbae_image (the \<circ> f) (nba_nbae A))
        }, do {
          f \<leftarrow> op_set_enumerate (nodes A);
          RETURN (nba_nbae (nba_image (the \<circ> f) A))
        }) \<in> \<langle>Id\<rangle> nres_rel"
        unfolding op_set_enumerate_def by (refine_vcg) (simp add: inj_on_map_the nba_image_nbae)
      also have "(do {
          f \<leftarrow> op_set_enumerate (nodes A);
          RETURN (nba_nbae (nba_image (the \<circ> f) A))
        }, op_translate A) \<in> \<langle>Id\<rangle> nres_rel"
        unfolding op_set_enumerate_def op_translate_def
        by (refine_vcg) (metis Collect_mem_eq inj_on_map_the subset_Collect_conv)
      finally show ?thesis unfolding nres_rel_comp by simp
    qed

  end

end