section \<open>Deterministic Co-Büchi Automata Combinations\<close>

theory DCA_Combine
imports DCA DGCA
begin

  global_interpretation degeneralization: automaton_degeneralization_run
    dgca dgca.alphabet dgca.initial dgca.transition dgca.rejecting "\<lambda> P w r p. cogen fins P (p ## r)"
    dca dca.alphabet dca.initial dca.transition dca.rejecting "\<lambda> P w r p. fins P (p ## r)"
    fst id
    defines degeneralize = degeneralization.degeneralize
    by (unfold_locales) (auto simp flip: sscan_smap)

  lemmas degeneralize_language[simp] = degeneralization.degeneralize_language[folded DCA.language_def]
  lemmas degeneralize_nodes_finite[iff] = degeneralization.degeneralize_nodes_finite[folded DCA.nodes_def]
  lemmas degeneralize_nodes_card = degeneralization.degeneralize_nodes_card[folded DCA.nodes_def]

  global_interpretation intersection: automaton_intersection_run
    dca.dca dca.alphabet dca.initial dca.transition dca.rejecting "\<lambda> P w r p. fins P (p ## r)"
    dca.dca dca.alphabet dca.initial dca.transition dca.rejecting "\<lambda> P w r p. fins P (p ## r)"
    dca.dca dca.alphabet dca.initial dca.transition dca.rejecting "\<lambda> P w r p. fins P (p ## r)"
    "\<lambda> c\<^sub>1 c\<^sub>2 pq. (c\<^sub>1 \<circ> fst) pq \<or> (c\<^sub>2 \<circ> snd) pq"
    defines intersect = intersection.product
    by (unfold_locales) (simp del: comp_apply)

  lemmas intersect_language = intersection.product_language
  lemmas intersect_nodes_finite = intersection.product_nodes_finite
  lemmas intersect_nodes_card = intersection.product_nodes_card

  global_interpretation union: automaton_union_run
    dca.dca dca.alphabet dca.initial dca.transition dca.rejecting "\<lambda> P w r p. fins P (p ## r)"
    dca.dca dca.alphabet dca.initial dca.transition dca.rejecting "\<lambda> P w r p. fins P (p ## r)"
    dgca.dgca dgca.alphabet dgca.initial dgca.transition dgca.rejecting "\<lambda> P w r p. cogen fins P (p ## r)"
    "\<lambda> c\<^sub>1 c\<^sub>2. [c\<^sub>1 \<circ> fst, c\<^sub>2 \<circ> snd]"
    defines union' = union.product
    by unfold_locales auto

  lemmas union'_language[simp] = union.product_language[folded DGCA.language_def]
  lemmas union'_nodes_finite = union.product_nodes_finite[folded DGCA.nodes_def]
  lemmas union'_nodes_card = union.product_nodes_card[folded DGCA.nodes_def]

  global_interpretation intersection_list: automaton_intersection_list_run
    dca.dca dca.alphabet dca.initial dca.transition dca.rejecting "\<lambda> P w r p. fins P (p ## r)"
    dca.dca dca.alphabet dca.initial dca.transition dca.rejecting "\<lambda> P w r p. fins P (p ## r)"
    "\<lambda> cs pp. \<exists> k < length cs. (cs ! k) (pp ! k)"
    defines intersect_list = intersection_list.product
    by (unfold_locales) (simp add: comp_def)

  lemmas intersect_list_language = intersection_list.product_language
  lemmas intersect_list_nodes_finite = intersection_list.product_nodes_finite
  lemmas intersect_list_nodes_card = intersection_list.product_nodes_card

  global_interpretation union_list: automaton_union_list_run
    dca.dca dca.alphabet dca.initial dca.transition dca.rejecting "\<lambda> P w r p. fins P (p ## r)"
    dgca.dgca dgca.alphabet dgca.initial dgca.transition dgca.rejecting "\<lambda> P w r p. cogen fins P (p ## r)"
    "\<lambda> cs. map (\<lambda> k pp. (cs ! k) (pp ! k)) [0 ..< length cs]"
    defines union_list' = union_list.product
    by (unfold_locales) (auto simp: cogen_def comp_def)

  lemmas union_list'_language[simp] = union_list.product_language[folded DGCA.language_def]
  lemmas union_list'_nodes_finite = union_list.product_nodes_finite[folded DGCA.nodes_def]
  lemmas union_list'_nodes_card = union_list.product_nodes_card[folded DGCA.nodes_def]

  abbreviation union where "union A B \<equiv> degeneralize (union' A B)"

  lemma union_language[simp]:
    assumes "dca.alphabet A = dca.alphabet B"
    shows "DCA.language (union A B) = DCA.language A \<union> DCA.language B"
    using assms by simp
  lemma union_nodes_finite:
    assumes "finite (DCA.nodes A)" "finite (DCA.nodes B)"
    shows "finite (DCA.nodes (union A B))"
    using union'_nodes_finite assms by simp
  lemma union_nodes_card:
    assumes "finite (DCA.nodes A)" "finite (DCA.nodes B)"
    shows "card (DCA.nodes (union A B)) \<le> 2 * card (DCA.nodes A) * card (DCA.nodes B)"
  proof -
    have "card (DCA.nodes (union A B)) \<le>
      max 1 (length (dgca.rejecting (union' A B))) * card (DGCA.nodes (union' A B))"
      using degeneralize_nodes_card by this
    also have "length (dgca.rejecting (union' A B)) = 2" by simp
    also have "card (DGCA.nodes (union' A B)) \<le> card (DCA.nodes A) * card (DCA.nodes B)"
      using union'_nodes_card assms by this
    finally show ?thesis by simp
  qed

  abbreviation union_list where "union_list AA \<equiv> degeneralize (union_list' AA)"

  lemma union_list_language[simp]:
    assumes "\<Inter> (dca.alphabet ` set AA) = \<Union> (dca.alphabet ` set AA)"
    shows "DCA.language (union_list AA) = \<Union> (DCA.language ` set AA)"
    using assms by simp
  lemma union_list_nodes_finite:
    assumes "list_all (finite \<circ> DCA.nodes) AA"
    shows "finite (DCA.nodes (union_list AA))"
    using union_list'_nodes_finite assms by simp
  lemma union_list_nodes_card:
    assumes "list_all (finite \<circ> DCA.nodes) AA"
    shows "card (DCA.nodes (union_list AA)) \<le> max 1 (length AA) * prod_list (map (card \<circ> DCA.nodes) AA)"
  proof -
    have "card (DCA.nodes (union_list AA)) \<le>
      max 1 (length (dgca.rejecting (union_list' AA))) * card (DGCA.nodes (union_list' AA))"
      using degeneralize_nodes_card by this
    also have "length (dgca.rejecting (union_list' AA)) = length AA" by simp
    also have "card (DGCA.nodes (union_list' AA)) \<le> prod_list (map (card \<circ> DCA.nodes) AA)"
      using union_list'_nodes_card assms by this
    finally show ?thesis by simp
  qed

end