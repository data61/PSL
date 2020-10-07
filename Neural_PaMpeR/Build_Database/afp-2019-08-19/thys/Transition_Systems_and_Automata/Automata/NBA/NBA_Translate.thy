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

  definition nbae_image where "nbae_image f A \<equiv> nbae (alphabete A) (f ` initiale A)
    ((\<lambda> (p, a, q). (f p, a, f q)) ` transe A) (f ` acceptinge A)"

  lemma nbae_image_param[param]: "(nbae_image, nbae_image) \<in> (S \<rightarrow> T) \<rightarrow> \<langle>L, S\<rangle> nbae_rel \<rightarrow> \<langle>L, T\<rangle> nbae_rel"
    unfolding nbae_image_def by parametricity

  lemma nbae_image_id[simp]: "nbae_image id = id" unfolding nbae_image_def by auto
  lemma nbae_image_nba_nbae: "nbae_image f (nba_nbae A) = nbae
    (alphabet A) (f ` initial A)
    (\<Union> p \<in> nodes A. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p)
    (f ` {p \<in> nodes A. accepting A p})"
    unfolding nba_nbae_def nbae_image_def nbae.simps Set.filter_def by force

  section \<open>Exploration and Translation\<close>

  definition trans_spec where
    "trans_spec A f \<equiv> \<Union> p \<in> nodes A. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p"

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
    assumes "N = nodes A" "L = alphabet A" "S = succ A"
    shows "(trans_algo N L S f, SPEC (HOL.eq (trans_spec A f))) \<in> \<langle>Id\<rangle> nres_rel"
  unfolding trans_algo_def trans_spec_def assms(4-6)
  proof (refine_vcg FOREACH_rule_insert_eq)
    show "finite (nodes A)" using assms(1) by this
    show "(\<Union> p \<in> nodes A. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p) =
      (\<Union> p \<in> nodes A. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p)" by rule
    show "(\<Union> p \<in> {}. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p) = {}" by simp
    fix T x
    assume 1: "T \<subseteq> nodes A" "x \<in> nodes A" "x \<notin> T"
    show "finite (alphabet A)" using assms(2) by this
    show "(\<Union> a \<in> {}. f ` {x} \<times> {a} \<times> f ` succ A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p) =
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p)"
      "(\<Union> a \<in> alphabet A. f ` {x} \<times> {a} \<times> f ` succ A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p) =
      (\<Union> p \<in> insert x T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p)" by auto
    fix Ta xa
    assume 2: "Ta \<subseteq> alphabet A" "xa \<in> alphabet A" "xa \<notin> Ta"
    show "finite (succ A xa x)" using 1 2 assms(1) by (meson infinite_subset nodes_succ subsetI)
    show "(f ` {x} \<times> {xa} \<times> f ` succ A xa x) \<union>
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` succ A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p) =
      (\<Union> a \<in> insert xa Ta. f ` {x} \<times> {a} \<times> f ` succ A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p)"
      by auto
    show "(f ` {x} \<times> {xa} \<times> f ` {}) \<union>
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` succ A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p) =
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` succ A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p)"
      by auto
    fix Tb xb
    assume 3: "Tb \<subseteq> succ A xa x" "xb \<in> succ A xa x" "xb \<notin> Tb"
    show "(f x, xa, f xb) \<notin> f ` {x} \<times> {xa} \<times> f ` Tb \<union>
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` succ A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p)"
      using 1 2 3 assms(3) by (blast dest: inj_onD)
    show "f ` {x} \<times> {xa} \<times> f ` insert xb Tb \<union>
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` succ A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p) =
      insert (f x, xa, f xb) (f ` {x} \<times> {xa} \<times> f ` Tb \<union>
      (\<Union> a \<in> Ta. f ` {x} \<times> {a} \<times> f ` succ A a x) \<union>
      (\<Union> p \<in> T. \<Union> a \<in> alphabet A. f ` {p} \<times> {a} \<times> f ` succ A a p))"
      by auto
  qed

  definition to_nbaei :: "('state, 'label) nba \<Rightarrow> ('state, 'label) nba"
    where "to_nbaei \<equiv> id"

  (* TODO: make separate implementations for "nba_nbae" and "op_set_enumerate \<bind> nbae_image" *)
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
        ASSERT (\<forall> a \<in> alphabet A. \<forall> p \<in> dom f. \<forall> q \<in> succ A a p. f q \<noteq> None);
        T \<leftarrow> trans_algo N (alphabet A) (succ A) (\<lambda> x. the (f x));
        RETURN (nbae (alphabet A) ((\<lambda> x. the (f x)) ` initial A) T
          ((\<lambda> x. the (f x)) ` {p \<in> N. accepting A p}))
      }) \<in> ?R"
    unfolding trans_algo_def by (autoref_monadic (plain))
  concrete_definition to_nbaei_impl uses to_nbaei_impl
  lemma to_nbaei_impl_refine'':
    fixes S :: "('statei \<times> 'state) set"
    assumes "finite (nodes A)"
    assumes "is_bounded_hashcode S seq bhc"
    assumes "is_valid_def_hm_size TYPE('statei) hms"
    assumes "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
    assumes "(Ai, A) \<in> \<langle>L, S\<rangle> nbai_nba_rel"
    shows "(RETURN (to_nbaei_impl seq bhc hms Ai), do {
        f \<leftarrow> op_set_enumerate (nodes A);
        RETURN (nbae_image (the \<circ> f) (nba_nbae A))
      }) \<in> \<langle>\<langle>L, nat_rel\<rangle> nbaei_nbae_rel\<rangle> nres_rel"
  proof -
    have 1: "finite (alphabet A)"
      using nbai_nba_param(2)[param_fo, OF assms(5)] list_set_rel_finite
      unfolding finite_set_rel_def by auto
    note to_nbaei_impl.refine[OF assms]
    also have "(do {
        let N = nodes A;
        f \<leftarrow> op_set_enumerate N;
        ASSERT (dom f = N);
        ASSERT (\<forall> p \<in> initial A. f p \<noteq> None);
        ASSERT (\<forall> a \<in> alphabet A. \<forall> p \<in> dom f. \<forall> q \<in> succ A a p. f q \<noteq> None);
        T \<leftarrow> trans_algo N (alphabet A) (succ A) (\<lambda> x. the (f x));
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
      },  do {
        f \<leftarrow> op_set_enumerate (nodes A);
        RETURN (nbae_image (the \<circ> f) (nba_nbae A))
      }) \<in> \<langle>Id\<rangle> nres_rel"
      unfolding trans_spec_def nbae_image_nba_nbae by refine_vcg force
    finally show ?thesis unfolding nres_rel_comp by simp
  qed

  (* TODO: generalize L *)
  context
    fixes Ai A
    fixes seq bhc hms
    fixes S :: "('statei \<times> 'state) set"
    assumes a: "finite (nodes A)"
    assumes b: "is_bounded_hashcode S seq bhc"
    assumes c: "is_valid_def_hm_size TYPE('statei) hms"
    assumes d: "(seq, HOL.eq) \<in> S \<rightarrow> S \<rightarrow> bool_rel"
    assumes e: "(Ai, A) \<in> \<langle>Id, S\<rangle> nbai_nba_rel"
  begin

    definition f' where "f' \<equiv> SOME f'.
      (to_nbaei_impl seq bhc hms Ai, nbae_image (the \<circ> f') (nba_nbae A)) \<in> \<langle>Id, nat_rel\<rangle> nbaei_nbae_rel \<and>
      dom f' = nodes A \<and> inj_on f' (nodes A)"

    lemma 1: "\<exists> f'. (to_nbaei_impl seq bhc hms Ai, nbae_image (the \<circ> f') (nba_nbae A)) \<in>
      \<langle>Id, nat_rel\<rangle> nbaei_nbae_rel \<and> dom f' = nodes A \<and> inj_on f' (nodes A)"
      using to_nbaei_impl_refine''[
        OF a b c d e,
        unfolded op_set_enumerate_def bind_RES_RETURN_eq,
        THEN nres_relD,
        THEN RETURN_ref_SPECD]
      by force

    lemma f'_refine: "(to_nbaei_impl seq bhc hms Ai, nbae_image (the \<circ> f') (nba_nbae A)) \<in>
      \<langle>Id, nat_rel\<rangle> nbaei_nbae_rel" using someI_ex[OF 1, folded f'_def] by auto
    lemma f'_dom: "dom f' = nodes A" using someI_ex[OF 1, folded f'_def] by auto
    lemma f'_inj: "inj_on f' (nodes A)" using someI_ex[OF 1, folded f'_def] by auto

    definition f where "f \<equiv> the \<circ> f'"
    definition g where "g = inv_into (nodes A) f"
    lemma inj_f[intro!, simp]: "inj_on f (nodes A)"
      using f'_inj f'_dom unfolding f_def by (simp add: inj_on_map_the)
    lemma inj_g[intro!, simp]: "inj_on g (f ` nodes A)"
      unfolding g_def by (simp add: inj_on_inv_into)

    definition rel where "rel \<equiv> {(f p, p) |p. p \<in> nodes A}"
    lemma rel_alt_def: "rel = (br f (\<lambda> p. p \<in> nodes A))\<inverse>"
      unfolding rel_def by (auto simp: in_br_conv)
    lemma rel_inv_def: "rel = br g (\<lambda> k. k \<in> f ` nodes A)"
      unfolding rel_alt_def g_def by (auto simp: in_br_conv)
    lemma rel_domain[simp]: "Domain rel = f ` nodes A" unfolding rel_def by force
    lemma rel_range[simp]: "Range rel = nodes A" unfolding rel_def by auto
    lemma [intro!, simp]: "bijective rel" unfolding rel_inv_def by (simp add: bijective_alt)
    lemma [simp]: "Id_on (f ` nodes A) O rel = rel" unfolding rel_def by auto
    lemma [simp]: "rel O Id_on (nodes A) = rel" unfolding rel_def by auto

    lemma [param]: "(f, f) \<in> Id_on (Range rel) \<rightarrow> Id_on (Domain rel)" unfolding rel_alt_def by auto
    lemma [param]: "(g, g) \<in> Id_on (Domain rel) \<rightarrow> Id_on (Range rel)" unfolding rel_inv_def by auto
    lemma [param]: "(id, f) \<in> rel \<rightarrow> Id_on (Domain rel)" unfolding rel_alt_def by (auto simp: in_br_conv)
    lemma [param]: "(f, id) \<in> Id_on (Range rel) \<rightarrow> rel" unfolding rel_alt_def by (auto simp: in_br_conv)
    lemma [param]: "(id, g) \<in> Id_on (Domain rel) \<rightarrow> rel" unfolding rel_inv_def by (auto simp: in_br_conv)
    lemma [param]: "(g, id) \<in> rel \<rightarrow> Id_on (Range rel)" unfolding rel_inv_def by (auto simp: in_br_conv)

    lemma to_nbaei_impl_refine':
      "(to_nbaei_impl seq bhc hms Ai, to_nbaei A) \<in> \<langle>Id_on (alphabet A), rel\<rangle> nbaei_nba_rel"
    proof -
      have "(nbae_nba (nbaei_nbae (to_nbaei_impl seq bhc hms Ai)), nbae_nba (id (nbae_image f (nba_nbae A)))) \<in>
        \<langle>Id, nat_rel\<rangle> nba_rel" using f'_refine[folded f_def] by parametricity auto
      also have "(nbae_nba (id (nbae_image f (nba_nbae A))), nbae_nba (id (nbae_image id (nba_nbae A)))) \<in>
        \<langle>Id_on (alphabet A), rel\<rangle> nba_rel" using nba_rel_eq by parametricity auto
      also have "nbae_nba (id (nbae_image id (nba_nbae A))) = (nbae_nba \<circ> nba_nbae) A" by simp
      also have "(\<dots>, id A) \<in> \<langle>Id_on (alphabet A), Id_on (nodes A)\<rangle> nba_rel" by parametricity
      also have "id A = to_nbaei A" unfolding to_nbaei_def by simp
      finally show ?thesis unfolding nbaei_nba_rel_def by simp
    qed

  end

  context
  begin

    interpretation autoref_syn by this

    lemma to_nbaei_impl_refine[autoref_rules]:
      fixes S :: "('statei \<times> 'state) set"
      assumes "SIDE_PRECOND (finite (nodes A))"
      assumes "SIDE_GEN_ALGO (is_bounded_hashcode S seq bhc)"
      assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('statei) hms)"
      assumes "GEN_OP seq HOL.eq (S \<rightarrow> S \<rightarrow> bool_rel)"
      assumes "(Ai, A) \<in> \<langle>Id, S\<rangle> nbai_nba_rel"
      shows "(to_nbaei_impl seq bhc hms Ai,
        (OP to_nbaei ::: \<langle>Id, S\<rangle> nbai_nba_rel \<rightarrow>
        \<langle>Id_on (alphabet A), rel Ai A seq bhc hms\<rangle> nbaei_nba_rel) $ A) \<in>
        \<langle>Id_on (alphabet A), rel Ai A seq bhc hms\<rangle> nbaei_nba_rel"
      using to_nbaei_impl_refine' assms unfolding autoref_tag_defs by this

  end

end