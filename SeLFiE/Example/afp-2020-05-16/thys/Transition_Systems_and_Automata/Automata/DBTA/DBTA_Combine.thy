section \<open>Deterministic Büchi Transition Automata Combinations\<close>

theory DBTA_Combine
imports DBTA DGBTA
begin

  (* TODO: exact copy-paste from NBTA, abstract *)
  global_interpretation degeneralization: automaton_degeneralization_run
    dgbta dgbta.alphabet dgbta.initial dgbta.transition dgbta.accepting "\<lambda> P w r p. gen infs P (p ## r ||| w ||| r)"
    dbta dbta.alphabet dbta.initial dbta.transition dbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    id "\<lambda> ((p, k), a, (q, l)). ((p, a, q), k)"
    defines degeneralize = degeneralization.degeneralize
  proof
    fix w :: "'a stream"
    fix r :: "'b stream"
    fix cs p k
    let ?f = "\<lambda> ((p, k), a, (q, l)). ((p, a, q), k)"
    let ?s = "sscan (count cs \<circ> id) (p ## r ||| w ||| r) k"
    have "infs (degen cs \<circ> ?f) ((p, k) ## (r ||| ?s) ||| w ||| (r ||| ?s)) \<longleftrightarrow>
      infs (degen cs) (smap ?f ((p, k) ## (r ||| ?s) ||| w ||| (r ||| ?s)))"
      by (simp add: comp_def)
    also have "smap ?f ((p, k) ## (r ||| ?s) ||| w ||| (r ||| ?s)) = (p ## r ||| w ||| r) ||| k ## ?s"
      by (coinduction arbitrary: p k r w) (auto simp: eq_scons simp flip: szip_unfold sscan_scons)
    also have "\<dots> = (p ## r ||| w ||| r) ||| k ## sscan (count cs) (p ## r ||| w ||| r) k" by simp
    also have "infs (degen cs) \<dots> = gen infs cs (p ## r ||| w ||| r)" using degen_infs by this
    finally show "infs (degen cs \<circ> ?f) ((p, k) ## (r ||| ?s) ||| w ||| (r ||| ?s)) \<longleftrightarrow>
      gen infs cs (p ## r ||| w ||| r)" by this
  qed

  lemmas degeneralize_language[simp] = degeneralization.degeneralize_language[folded DBTA.language_def]
  lemmas degeneralize_nodes_finite[iff] = degeneralization.degeneralize_nodes_finite[folded DBTA.nodes_def]
  lemmas degeneralize_nodes_card = degeneralization.degeneralize_nodes_card[folded DBTA.nodes_def]

  global_interpretation intersection: automaton_intersection_run
    dbta.dbta dbta.alphabet dbta.initial dbta.transition dbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    dbta.dbta dbta.alphabet dbta.initial dbta.transition dbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    dgbta.dgbta dgbta.alphabet dgbta.initial dgbta.transition dgbta.accepting "\<lambda> P w r p. gen infs P (p ## r ||| w ||| r)"
    "\<lambda> c\<^sub>1 c\<^sub>2. [c\<^sub>1 \<circ> (\<lambda> ((p\<^sub>1, p\<^sub>2), a, (q\<^sub>1, q\<^sub>2)). (p\<^sub>1, a, q\<^sub>1)), c\<^sub>2 \<circ> (\<lambda> ((p\<^sub>1, p\<^sub>2), a, (q\<^sub>1, q\<^sub>2)). (p\<^sub>2, a, q\<^sub>2))]"
    defines intersect' = intersection.product
  proof
    fix w :: "'a stream"
    fix u :: "'b stream"
    fix v :: "'c stream"
    fix c\<^sub>1 c\<^sub>2 p q
    let ?tfst = "\<lambda> ((p\<^sub>1, p\<^sub>2), a, (q\<^sub>1, q\<^sub>2)). (p\<^sub>1, a, q\<^sub>1)"
    let ?tsnd = "\<lambda> ((p\<^sub>1, p\<^sub>2), a, (q\<^sub>1, q\<^sub>2)). (p\<^sub>2, a, q\<^sub>2)"
    have "gen infs [c\<^sub>1 \<circ> ?tfst, c\<^sub>2 \<circ> ?tsnd] ((p, q) ## (u ||| v) ||| w ||| u ||| v) \<longleftrightarrow>
      infs c\<^sub>1 (smap ?tfst ((p, q) ## (u ||| v) ||| w ||| u ||| v)) \<and>
      infs c\<^sub>2 (smap ?tsnd ((p, q) ## (u ||| v) ||| w ||| u ||| v))"
      unfolding gen_def by (simp add: comp_def)
    also have "smap ?tfst ((p, q) ## (u ||| v) ||| w ||| u ||| v) = p ## u ||| w ||| u"
      by (coinduction arbitrary: p q u v w) (auto simp flip: szip_unfold, metis stream.collapse)
    also have "smap ?tsnd ((p, q) ## (u ||| v) ||| w ||| u ||| v) = q ## v ||| w ||| v"
      by (coinduction arbitrary: p q u v w) (auto simp flip: szip_unfold, metis stream.collapse)
    finally show "gen infs [c\<^sub>1 \<circ> ?tfst, c\<^sub>2 \<circ> ?tsnd] ((p, q) ## (u ||| v) ||| w ||| u ||| v) \<longleftrightarrow>
      infs c\<^sub>1 (p ## u ||| w ||| u) \<and> infs c\<^sub>2 (q ## v ||| w ||| v)" by this
  qed

  lemmas intersect'_language[simp] = intersection.product_language[folded DGBTA.language_def]
  lemmas intersect'_nodes_finite = intersection.product_nodes_finite[folded DGBTA.nodes_def]
  lemmas intersect'_nodes_card = intersection.product_nodes_card[folded DGBTA.nodes_def]

  global_interpretation union: automaton_union_run
    dbta.dbta dbta.alphabet dbta.initial dbta.transition dbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    dbta.dbta dbta.alphabet dbta.initial dbta.transition dbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    dbta.dbta dbta.alphabet dbta.initial dbta.transition dbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    "\<lambda> c\<^sub>1 c\<^sub>2 pq. (c\<^sub>1 \<circ> (\<lambda> ((p\<^sub>1, p\<^sub>2), a, (q\<^sub>1, q\<^sub>2)). (p\<^sub>1, a, q\<^sub>1))) pq \<or> (c\<^sub>2 \<circ> (\<lambda> ((p\<^sub>1, p\<^sub>2), a, (q\<^sub>1, q\<^sub>2)). (p\<^sub>2, a, q\<^sub>2))) pq"
    defines union = union.product
  proof
    fix w :: "'a stream"
    fix u :: "'b stream"
    fix v :: "'c stream"
    fix c\<^sub>1 c\<^sub>2 p q
    let ?tfst = "\<lambda> ((p\<^sub>1, p\<^sub>2), a, (q\<^sub>1, q\<^sub>2)). (p\<^sub>1, a, q\<^sub>1)"
    let ?tsnd = "\<lambda> ((p\<^sub>1, p\<^sub>2), a, (q\<^sub>1, q\<^sub>2)). (p\<^sub>2, a, q\<^sub>2)"
    have "infs (\<lambda> pq. (c\<^sub>1 \<circ> (\<lambda> ((p\<^sub>1, p\<^sub>2), a, q\<^sub>1, q\<^sub>2). (p\<^sub>1, a, q\<^sub>1))) pq \<or>
       (c\<^sub>2 \<circ> (\<lambda> ((p\<^sub>1, p\<^sub>2), a, q\<^sub>1, q\<^sub>2). (p\<^sub>2, a, q\<^sub>2))) pq) ((p, q) ## (u ||| v) ||| w ||| (u ||| v))  \<longleftrightarrow>
      infs c\<^sub>1 (smap ?tfst ((p, q) ## (u ||| v) ||| w ||| u ||| v)) \<or>
      infs c\<^sub>2 (smap ?tsnd ((p, q) ## (u ||| v) ||| w ||| u ||| v))"
      by (simp add: comp_def)
    also have "smap ?tfst ((p, q) ## (u ||| v) ||| w ||| u ||| v) = p ## u ||| w ||| u"
      by (coinduction arbitrary: p q u v w) (auto simp flip: szip_unfold, metis stream.collapse)
    also have "smap ?tsnd ((p, q) ## (u ||| v) ||| w ||| u ||| v) = q ## v ||| w ||| v"
      by (coinduction arbitrary: p q u v w) (auto simp flip: szip_unfold, metis stream.collapse)
    finally show "infs (\<lambda> pq. (c\<^sub>1 \<circ> (\<lambda> ((p\<^sub>1, p\<^sub>2), a, q\<^sub>1, q\<^sub>2). (p\<^sub>1, a, q\<^sub>1))) pq \<or>
       (c\<^sub>2 \<circ> (\<lambda> ((p\<^sub>1, p\<^sub>2), a, q\<^sub>1, q\<^sub>2). (p\<^sub>2, a, q\<^sub>2))) pq) ((p, q) ## (u ||| v) ||| w ||| (u ||| v)) \<longleftrightarrow>
      infs c\<^sub>1 (p ## u ||| w ||| u) \<or> infs c\<^sub>2 (q ## v ||| w ||| v)" by this
  qed

  lemmas union_language = union.product_language
  lemmas union_nodes_finite = union.product_nodes_finite
  lemmas union_nodes_card = union.product_nodes_card

  abbreviation intersect where "intersect A B \<equiv> degeneralize (intersect' A B)"

  lemma intersect_language[simp]: "DBTA.language (intersect A B) = DBTA.language A \<inter> DBTA.language B"
    by simp
  lemma intersect_nodes_finite:
    assumes "finite (DBTA.nodes A)" "finite (DBTA.nodes B)"
    shows "finite (DBTA.nodes (intersect A B))"
    using intersect'_nodes_finite assms by simp
  lemma intersect_nodes_card:
    assumes "finite (DBTA.nodes A)" "finite (DBTA.nodes B)"
    shows "card (DBTA.nodes (intersect A B)) \<le> 2 * card (DBTA.nodes A) * card (DBTA.nodes B)"
  proof -
    have "card (DBTA.nodes (intersect A B)) \<le>
      max 1 (length (dgbta.accepting (intersect' A B))) * card (DGBTA.nodes (intersect' A B))"
      using degeneralize_nodes_card by this
    also have "length (dgbta.accepting (intersect' A B)) = 2" by simp
    also have "card (DGBTA.nodes (intersect' A B)) \<le> card (DBTA.nodes A) * card (DBTA.nodes B)"
      using intersect'_nodes_card assms by this
    finally show ?thesis by simp
  qed

end