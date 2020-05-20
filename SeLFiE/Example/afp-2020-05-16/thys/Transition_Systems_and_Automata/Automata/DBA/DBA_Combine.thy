section \<open>Deterministic Büchi Automata Combinations\<close>

theory DBA_Combine
imports DBA DGBA
begin

  global_interpretation degeneralization: automaton_degeneralization_run
    dgba dgba.alphabet dgba.initial dgba.transition dgba.accepting "\<lambda> P w r p. gen infs P (p ## r)"
    dba dba.alphabet dba.initial dba.transition dba.accepting "\<lambda> P w r p. infs P (p ## r)"
    fst id
    defines degeneralize = degeneralization.degeneralize
    by (unfold_locales) (auto simp flip: sscan_smap)

  lemmas degeneralize_language[simp] = degeneralization.degeneralize_language[folded DBA.language_def]
  lemmas degeneralize_nodes_finite[iff] = degeneralization.degeneralize_nodes_finite[folded DBA.nodes_def]
  lemmas degeneralize_nodes_card = degeneralization.degeneralize_nodes_card[folded DBA.nodes_def]

  global_interpretation intersection: automaton_intersection_run
    dba.dba dba.alphabet dba.initial dba.transition dba.accepting "\<lambda> P w r p. infs P (p ## r)"
    dba.dba dba.alphabet dba.initial dba.transition dba.accepting "\<lambda> P w r p. infs P (p ## r)"
    dgba.dgba dgba.alphabet dgba.initial dgba.transition dgba.accepting "\<lambda> P w r p. gen infs P (p ## r)"
    "\<lambda> c\<^sub>1 c\<^sub>2. [c\<^sub>1 \<circ> fst, c\<^sub>2 \<circ> snd]"
    defines intersect' = intersection.product
    by unfold_locales auto

  lemmas intersect'_language[simp] = intersection.product_language[folded DGBA.language_def]
  lemmas intersect'_nodes_finite = intersection.product_nodes_finite[folded DGBA.nodes_def]
  lemmas intersect'_nodes_card = intersection.product_nodes_card[folded DGBA.nodes_def]

  global_interpretation union: automaton_union_run
    dba.dba dba.alphabet dba.initial dba.transition dba.accepting "\<lambda> P w r p. infs P (p ## r)"
    dba.dba dba.alphabet dba.initial dba.transition dba.accepting "\<lambda> P w r p. infs P (p ## r)"
    dba.dba dba.alphabet dba.initial dba.transition dba.accepting "\<lambda> P w r p. infs P (p ## r)"
    "\<lambda> c\<^sub>1 c\<^sub>2 pq. (c\<^sub>1 \<circ> fst) pq \<or> (c\<^sub>2 \<circ> snd) pq"
    defines union = union.product
    by (unfold_locales) (simp del: comp_apply)

  lemmas union_language = union.product_language
  lemmas union_nodes_finite = union.product_nodes_finite
  lemmas union_nodes_card = union.product_nodes_card

  global_interpretation intersection_list: automaton_intersection_list_run
    dba.dba dba.alphabet dba.initial dba.transition dba.accepting "\<lambda> P w r p. infs P (p ## r)"
    dgba.dgba dgba.alphabet dgba.initial dgba.transition dgba.accepting "\<lambda> P w r p. gen infs P (p ## r)"
    "\<lambda> cs. map (\<lambda> k pp. (cs ! k) (pp ! k)) [0 ..< length cs]"
    defines intersect_list' = intersection_list.product
    by (unfold_locales) (auto simp: gen_def comp_def)

  lemmas intersect_list'_language[simp] = intersection_list.product_language[folded DGBA.language_def]
  lemmas intersect_list'_nodes_finite = intersection_list.product_nodes_finite[folded DGBA.nodes_def]
  lemmas intersect_list'_nodes_card = intersection_list.product_nodes_card[folded DGBA.nodes_def]

  global_interpretation union_list: automaton_union_list_run
    dba.dba dba.alphabet dba.initial dba.transition dba.accepting "\<lambda> P w r p. infs P (p ## r)"
    dba.dba dba.alphabet dba.initial dba.transition dba.accepting "\<lambda> P w r p. infs P (p ## r)"
    "\<lambda> cs pp. \<exists> k < length cs. (cs ! k) (pp ! k)"
    defines union_list = union_list.product
    by (unfold_locales) (simp add: comp_def)

  lemmas union_list_language = union_list.product_language
  lemmas union_list_nodes_finite = union_list.product_nodes_finite
  lemmas union_list_nodes_card = union_list.product_nodes_card

  (* TODO: these compound definitions are annoying, can we move those into Deterministic theory *)

  abbreviation intersect where "intersect A B \<equiv> degeneralize (intersect' A B)"

  lemma intersect_language[simp]: "DBA.language (intersect A B) = DBA.language A \<inter> DBA.language B"
    by simp
  lemma intersect_nodes_finite:
    assumes "finite (DBA.nodes A)" "finite (DBA.nodes B)"
    shows "finite (DBA.nodes (intersect A B))"
    using intersect'_nodes_finite assms by simp
  lemma intersect_nodes_card:
    assumes "finite (DBA.nodes A)" "finite (DBA.nodes B)"
    shows "card (DBA.nodes (intersect A B)) \<le> 2 * card (DBA.nodes A) * card (DBA.nodes B)"
  proof -
    have "card (DBA.nodes (intersect A B)) \<le>
      max 1 (length (dgba.accepting (intersect' A B))) * card (DGBA.nodes (intersect' A B))"
      using degeneralize_nodes_card by this
    also have "length (dgba.accepting (intersect' A B)) = 2" by simp
    also have "card (DGBA.nodes (intersect' A B)) \<le> card (DBA.nodes A) * card (DBA.nodes B)"
      using intersect'_nodes_card assms by this
    finally show ?thesis by simp
  qed

  abbreviation intersect_list where "intersect_list AA \<equiv> degeneralize (intersect_list' AA)"

  lemma intersect_list_language[simp]: "DBA.language (intersect_list AA) = \<Inter> (DBA.language ` set AA)"
    by simp
  lemma intersect_list_nodes_finite:
    assumes "list_all (finite \<circ> DBA.nodes) AA"
    shows "finite (DBA.nodes (intersect_list AA))"
    using intersect_list'_nodes_finite assms by simp
  lemma intersect_list_nodes_card:
    assumes "list_all (finite \<circ> DBA.nodes) AA"
    shows "card (DBA.nodes (intersect_list AA)) \<le> max 1 (length AA) * prod_list (map (card \<circ> DBA.nodes) AA)"
  proof -
    have "card (DBA.nodes (intersect_list AA)) \<le>
      max 1 (length (dgba.accepting (intersect_list' AA))) * card (DGBA.nodes (intersect_list' AA))"
      using degeneralize_nodes_card by this
    also have "length (dgba.accepting (intersect_list' AA)) = length AA" by simp
    also have "card (DGBA.nodes (intersect_list' AA)) \<le> prod_list (map (card \<circ> DBA.nodes) AA)"
      using intersect_list'_nodes_card assms by this
    finally show ?thesis by simp
  qed

end