section \<open>Nondeterministic Büchi Transition Automata Combinations\<close>

theory NBTA_Combine
imports NBTA NGBTA
begin

  global_interpretation degeneralization: automaton_degeneralization_run
    ngbta ngbta.alphabet ngbta.initial ngbta.transition ngbta.accepting "\<lambda> P w r p. gen infs P (p ## r ||| w ||| r)"
    nbta nbta.alphabet nbta.initial nbta.transition nbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
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

  lemmas degeneralize_language[simp] = degeneralization.degeneralize_language[folded NBTA.language_def]
  lemmas degeneralize_nodes_finite[iff] = degeneralization.degeneralize_nodes_finite[folded NBTA.nodes_def]

  global_interpretation intersection: automaton_intersection_run
    nbta nbta.alphabet nbta.initial nbta.transition nbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    nbta nbta.alphabet nbta.initial nbta.transition nbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    ngbta ngbta.alphabet ngbta.initial ngbta.transition ngbta.accepting "\<lambda> P w r p. gen infs P (p ## r ||| w ||| r)"
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

  lemmas intersect'_language[simp] = intersection.product_language[folded NGBTA.language_def]
  lemmas intersect'_nodes_finite[intro] = intersection.product_nodes_finite[folded NGBTA.nodes_def]

  global_interpretation union: automaton_union_run
    nbta nbta.alphabet nbta.initial nbta.transition nbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    nbta nbta.alphabet nbta.initial nbta.transition nbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    nbta nbta.alphabet nbta.initial nbta.transition nbta.accepting "\<lambda> P w r p. infs P (p ## r ||| w ||| r)"
    "\<lambda> c\<^sub>1 c\<^sub>2 m. case m of (Inl p, a, Inl q) \<Rightarrow> c\<^sub>1 (p, a, q) | (Inr p, a, Inr q) \<Rightarrow> c\<^sub>2 (p, a, q)"
    defines union = union.sum
    by (unfold_locales) (auto simp add: szip_smap_fold comp_def case_prod_unfold simp flip: stream.map)

  lemmas union_language = union.sum_language
  lemmas union_nodes_finite = union.sum_nodes_finite

  abbreviation intersect where "intersect A B \<equiv> degeneralize (intersect' A B)"

  lemma intersect_language[simp]: "NBTA.language (intersect A B) = NBTA.language A \<inter> NBTA.language B"
    by simp
  lemma intersect_nodes_finite[intro]:
    assumes "finite (NBTA.nodes A)" "finite (NBTA.nodes B)"
    shows "finite (NBTA.nodes (intersect A B))"
    using intersect'_nodes_finite assms by simp

end