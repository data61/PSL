section \<open>Complementation to Explicit Büchi Automaton\<close>

theory Complementation_Final
imports
  "Complementation_Implement"
  "Transition_Systems_and_Automata.NBA_Translate"
  "HOL-Library.Permutation"
begin

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

  schematic_goal complement_impl:
    assumes [simp]: "finite (nodes A)"
    assumes [autoref_rules]: "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "(?f :: ?'c, RETURN (to_nbaei (complement_4 A))) \<in> ?R"
    by (autoref_monadic (plain))
  concrete_definition complement_impl uses complement_impl[unfolded autoref_tag_defs]

  theorem complement_impl_correct:
    assumes "finite (nodes A)"
    assumes "(Ai, A) \<in> \<langle>Id, nat_rel\<rangle> nbai_nba_rel"
    shows "language (nbae_nba (nbaei_nbae (complement_impl Ai))) = streams (alphabet A) - language A"
  proof -
    have "(language ((nbae_nba \<circ> nbaei_nbae) (complement_impl Ai)), language (id (complement_4 A))) \<in>
      \<langle>\<langle>Id_on (alphabet (complement_4 A))\<rangle> stream_rel\<rangle> set_rel"
      using complement_impl.refine[OF assms, unfolded to_nbaei_def id_apply, THEN RETURN_nres_relD]
      by parametricity
    also have "language (id (complement_4 A)) = streams (alphabet A) - language A"
      using assms(1) complement_4_correct by simp
    finally show ?thesis by simp
  qed

  definition nbaei_nbai :: "(String.literal, nat) nbaei \<Rightarrow> (String.literal, nat) nbai" where
    "nbaei_nbai \<equiv> nbae_nba_impl"

  (* TODO: possible optimizations:
    - introduce op_map_map operation for maps instead of manually iterating via FOREACH
    - consolidate various binds and maps in expand_map_get_7 *)
  export_code
    nat_of_integer integer_of_nat
    nbaei alphabetei initialei transei acceptingei
    nbaei_nbai complement_impl
    in SML module_name Complementation file_prefix Complementation_Export

end