section \<open>Final Instantiation of Algorithms Related to Complementation\<close>

theory Complementation_Final
imports
  "Complementation_Implement"
  "Formula"
  "Transition_Systems_and_Automata.NBA_Translate"
  "Transition_Systems_and_Automata.NGBA_Algorithms"
  "HOL-Library.Permutation"
begin

  subsection \<open>Syntax\<close>

  (* TODO: this syntax has unnecessarily high inner binding strength, requiring extra parentheses
    the regular let syntax correctly uses inner binding strength 0: ("(2_ =/ _)" 10) *)
  no_syntax "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" [1000, 13] 13)
  syntax "_do_let" :: "[pttrn, 'a] \<Rightarrow> do_bind" ("(2let _ =/ _)" 13)

  subsection \<open>Hashcodes on Complement States\<close>

  definition "hci k \<equiv> uint32_of_nat k * 1103515245 + 12345"
  definition "hc \<equiv> \<lambda> (p, q, b). hci p + hci q * 31 + (if b then 1 else 0)"
  definition "list_hash xs \<equiv> fold (bitXOR \<circ> hc) xs 0"

  lemma list_hash_eq:
    assumes "distinct xs" "distinct ys" "set xs = set ys"
    shows "list_hash xs = list_hash ys"
  proof -
    have "remdups xs <~~> remdups ys" using eq_set_perm_remdups assms(3) by this
    then have "xs <~~> ys" using assms(1, 2) by (simp add: distinct_remdups_id)
    then have "fold (bitXOR \<circ> hc) xs a = fold (bitXOR \<circ> hc) ys a" for a
    proof (induct arbitrary: a)
      case (swap y x l)
      have "x XOR y XOR a = y XOR x XOR a" for x y by (transfer) (simp add: word_bw_lcs(3))
      then show ?case by simp
    qed simp+
    then show ?thesis unfolding list_hash_def by this
  qed

  definition state_hash :: "nat \<Rightarrow> Complementation_Implement.state \<Rightarrow> nat" where
    "state_hash n p \<equiv> nat_of_hashcode (list_hash p) mod n"

  lemma state_hash_bounded_hashcode[autoref_ga_rules]: "is_bounded_hashcode state_rel
    (gen_equals (Gen_Map.gen_ball (foldli \<circ> list_map_to_list)) (list_map_lookup (=))
    (prod_eq (=) (\<longleftrightarrow>))) state_hash"
  proof
    show [param]: "(gen_equals (Gen_Map.gen_ball (foldli \<circ> list_map_to_list)) (list_map_lookup (=))
      (prod_eq (=) (\<longleftrightarrow>)), (=)) \<in> state_rel \<rightarrow> state_rel \<rightarrow> bool_rel" by autoref
    show "state_hash n xs = state_hash n ys" if "xs \<in> Domain state_rel" "ys \<in> Domain state_rel"
      "gen_equals (Gen_Map.gen_ball (foldli \<circ> list_map_to_list))
      (list_map_lookup (=)) (prod_eq (=) (=)) xs ys" for xs ys n
    proof -
      have 1: "distinct (map fst xs)" "distinct (map fst ys)"
        using that(1, 2) unfolding list_map_rel_def list_map_invar_def by (auto simp: in_br_conv)
      have 2: "distinct xs" "distinct ys" using 1 by (auto intro: distinct_mapI)
      have 3: "(xs, map_of xs) \<in> state_rel" "(ys, map_of ys) \<in> state_rel"
        using 1 unfolding list_map_rel_def list_map_invar_def by (auto simp: in_br_conv)
      have 4: "(gen_equals (Gen_Map.gen_ball (foldli \<circ> list_map_to_list)) (list_map_lookup (=))
        (prod_eq (=) (\<longleftrightarrow>)) xs ys, map_of xs = map_of ys) \<in> bool_rel" using 3 by parametricity
      have 5: "map_to_set (map_of xs) = map_to_set (map_of ys)" using that(3) 4 by simp
      have 6: "set xs = set ys" using map_to_set_map_of 1 5 by blast
      show "state_hash n xs = state_hash n ys" unfolding state_hash_def using list_hash_eq 2 6 by metis
    qed
    show "state_hash n x < n" if "1 < n" for n x using that unfolding state_hash_def by simp
  qed

  subsection \<open>Complementation\<close>

  schematic_goal complement_impl:
    assumes [simp]: "finite (NBA.nodes A)"
    assumes [autoref_rules]: "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "(?f :: ?'c, op_translate (complement_4 A)) \<in> ?R"
    by (autoref_monadic (plain))
  concrete_definition complement_impl uses complement_impl

  theorem complement_impl_correct:
    assumes "finite (NBA.nodes A)"
    assumes "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "NBA.language (nbae_nba (nbaei_nbae (complement_impl Ai))) =
      streams (nba.alphabet A) - NBA.language A"
    using op_translate_language[OF complement_impl.refine[OF assms]]
    using complement_4_correct[OF assms(1)]
    by simp

  subsection \<open>Language Subset\<close>

  definition [simp]: "op_language_subset A B \<equiv> NBA.language A \<subseteq> NBA.language B"

  lemmas [autoref_op_pat] = op_language_subset_def[symmetric]

  (* TODO: maybe we can implement emptiness check on NGBAs and skip degeneralization step *)
  schematic_goal language_subset_impl:
    assumes [simp]: "finite (NBA.nodes B)"
    assumes [autoref_rules]: "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    assumes [autoref_rules]: "(Bi, B) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "(?f :: ?'c, do {
      let AB' = intersect A (complement_4 B);
      ASSERT (finite (NBA.nodes AB'));
      RETURN (NBA.language AB' = {})
    }) \<in> ?R"
		by (autoref_monadic (plain))
  concrete_definition language_subset_impl uses language_subset_impl
  lemma language_subset_impl_refine[autoref_rules]:
    assumes "SIDE_PRECOND (finite (NBA.nodes A))"
    assumes "SIDE_PRECOND (finite (NBA.nodes B))"
    assumes "SIDE_PRECOND (nba.alphabet A \<subseteq> nba.alphabet B)"
    assumes "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    assumes "(Bi, B) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "(language_subset_impl Ai Bi, (OP op_language_subset :::
      \<langle>Id, nat_rel\<rangle> nbai_nba_rel \<rightarrow> \<langle>Id, nat_rel\<rangle> nbai_nba_rel \<rightarrow> bool_rel) $ A $ B) \<in> bool_rel"
  proof -
    have "(RETURN (language_subset_impl Ai Bi), do {
      let AB' = intersect A (complement_4 B);
      ASSERT (finite (NBA.nodes AB'));
      RETURN (NBA.language AB' = {})
    }) \<in> \<langle>bool_rel\<rangle> nres_rel"
      using language_subset_impl.refine assms(2, 4, 5) unfolding autoref_tag_defs by this
    also have "(do {
      let AB' = intersect A (complement_4 B);
      ASSERT (finite (NBA.nodes AB'));
      RETURN (NBA.language AB' = {})
    }, RETURN (NBA.language A \<subseteq> NBA.language B)) \<in> \<langle>bool_rel\<rangle> nres_rel"
    proof refine_vcg
      show "finite (NBA.nodes (intersect A (complement_4 B)))" using assms(1, 2) by auto
      have 1: "NBA.language A \<subseteq> streams (nba.alphabet B)"
        using nba.language_alphabet streams_mono2 assms(3) unfolding autoref_tag_defs by blast
      have 2: "NBA.language (complement_4 B) = streams (nba.alphabet B) - NBA.language B"
        using complement_4_correct assms(2) by auto
      show "(NBA.language (intersect A (complement_4 B)) = {},
        NBA.language A \<subseteq> NBA.language B) \<in> bool_rel" using 1 2 by auto
    qed
    finally show ?thesis using RETURN_nres_relD unfolding nres_rel_comp by force
  qed

  subsection \<open>Language Equality\<close>

  definition [simp]: "op_language_equal A B \<equiv> NBA.language A = NBA.language B"

  lemmas [autoref_op_pat] = op_language_equal_def[symmetric]

  schematic_goal language_equal_impl:
    assumes [simp]: "finite (NBA.nodes A)"
    assumes [simp]: "finite (NBA.nodes B)"
    assumes [simp]: "nba.alphabet A = nba.alphabet B"
    assumes [autoref_rules]: "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    assumes [autoref_rules]: "(Bi, B) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "(?f :: ?'c, NBA.language A \<subseteq> NBA.language B \<and> NBA.language B \<subseteq> NBA.language A) \<in> ?R"
    by autoref
  concrete_definition language_equal_impl uses language_equal_impl
  lemma language_equal_impl_refine[autoref_rules]:
    assumes "SIDE_PRECOND (finite (NBA.nodes A))"
    assumes "SIDE_PRECOND (finite (NBA.nodes B))"
    assumes "SIDE_PRECOND (nba.alphabet A = nba.alphabet B)"
    assumes "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    assumes "(Bi, B) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "(language_equal_impl Ai Bi, (OP op_language_equal :::
      \<langle>Id, nat_rel\<rangle> nbai_nba_rel \<rightarrow> \<langle>Id, nat_rel\<rangle> nbai_nba_rel \<rightarrow> bool_rel) $ A $ B) \<in> bool_rel"
    using language_equal_impl.refine[OF assms[unfolded autoref_tag_defs]] by auto

  schematic_goal product_impl:
    assumes [simp]: "finite (NBA.nodes B)"
    assumes [autoref_rules]: "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    assumes [autoref_rules]: "(Bi, B) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "(?f :: ?'c, do {
      let AB' = intersect A (complement_4 B);
      ASSERT (finite (NBA.nodes AB'));
      op_translate AB'
    }) \<in> ?R"
		by (autoref_monadic (plain))
  concrete_definition product_impl uses product_impl

  (* TODO: possible optimizations:
    - introduce op_map_map operation for maps instead of manually iterating via FOREACH
    - consolidate various binds and maps in expand_map_get_7 *)
  export_code
    Set.empty Set.insert Set.member
    "Inf :: 'a set set \<Rightarrow> 'a set" "Sup :: 'a set set \<Rightarrow> 'a set" image Pow set
    nat_of_integer integer_of_nat
    Variable Negation Conjunction Disjunction satisfies
    nbaei alphabetei initialei transitionei acceptingei
    nbae_nba_impl complement_impl language_equal_impl product_impl
    in SML module_name Complementation file_prefix Complementation

end