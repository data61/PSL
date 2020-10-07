section \<open>Deterministic Co-Büchi Automata Combinations\<close>

theory DCA_Combine
imports "DCA" "DGCA"
begin

  definition dcai :: "('label, 'state\<^sub>1) dca \<Rightarrow> ('label, 'state\<^sub>2) dca \<Rightarrow>
    ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) dca" where
    "dcai A B \<equiv> dca
      (dca.alphabet A \<inter> dca.alphabet B)
      (dca.initial A, dca.initial B)
      (\<lambda> a (p, q). (dca.succ A a p, dca.succ B a q))
      (\<lambda> (p, q). dca.rejecting A p \<or> dca.rejecting B q)"

  lemma dcai_fst[iff]: "infs (P \<circ> fst) (dca.trace (dcai A B) w (p, q)) \<longleftrightarrow> infs P (dca.trace A w p)"
  proof -
    let ?t = "dca.trace (dcai A B) w (p, q)"
    have "infs (P \<circ> fst) ?t \<longleftrightarrow> infs P (smap fst ?t)" by simp
    also have "smap fst ?t = dca.trace A w p" unfolding dcai_def by (coinduction arbitrary: w p q) (auto)
    finally show ?thesis by this
  qed
  lemma dcai_snd[iff]: "infs (P \<circ> snd) (dca.trace (dcai A B) w (p, q)) \<longleftrightarrow> infs P (dca.trace B w q)"
  proof -
    let ?t = "dca.trace (dcai A B) w (p, q)"
    have "infs (P \<circ> snd) ?t \<longleftrightarrow> infs P (smap snd ?t)" by simp
    also have "smap snd ?t = dca.trace B w q" unfolding dcai_def by (coinduction arbitrary: w p q) (auto)
    finally show ?thesis by this
  qed
  lemma dcai_nodes_fst[intro]: "fst ` DCA.nodes (dcai A B) \<subseteq> DCA.nodes A"
  proof (rule subsetI, erule imageE)
    fix pq p
    assume "pq \<in> DCA.nodes (dcai A B)" "p = fst pq"
    then show "p \<in> DCA.nodes A" unfolding dcai_def by (induct arbitrary: p) (auto)
  qed
  lemma dcai_nodes_snd[intro]: "snd ` DCA.nodes (dcai A B) \<subseteq> DCA.nodes B"
  proof (rule subsetI, erule imageE)
    fix pq q
    assume "pq \<in> DCA.nodes (dcai A B)" "q = snd pq"
    then show "q \<in> DCA.nodes B" unfolding dcai_def by (induct arbitrary: q) (auto)
  qed

  lemma dcai_nodes_finite[intro]:
    assumes "finite (DCA.nodes A)" "finite (DCA.nodes B)"
    shows "finite (DCA.nodes (dcai A B))"
  proof (rule finite_subset)
    show "DCA.nodes (dcai A B) \<subseteq> DCA.nodes A \<times> DCA.nodes B"
      using dcai_nodes_fst dcai_nodes_snd unfolding image_subset_iff by force
    show "finite (DCA.nodes A \<times> DCA.nodes B)" using assms by simp
  qed
  lemma dcai_nodes_card[intro]:
    assumes "finite (DCA.nodes A)" "finite (DCA.nodes B)"
    shows "card (DCA.nodes (dcai A B)) \<le> card (DCA.nodes A) * card (DCA.nodes B)"
  proof -
    have "card (DCA.nodes (dcai A B)) \<le> card (DCA.nodes A \<times> DCA.nodes B)"
    proof (rule card_mono)
      show "finite (DCA.nodes A \<times> DCA.nodes B)" using assms by simp
      show "DCA.nodes (dcai A B) \<subseteq> DCA.nodes A \<times> DCA.nodes B"
        using dcai_nodes_fst dcai_nodes_snd unfolding image_subset_iff by force
    qed
    also have "\<dots> = card (DCA.nodes A) * card (DCA.nodes B)" using card_cartesian_product by this
    finally show ?thesis by this
  qed

  lemma dcai_language[simp]: "DCA.language (dcai A B) = DCA.language A \<inter> DCA.language B"
  proof -
    have 1: "dca.alphabet (dcai A B) = dca.alphabet A \<inter> dca.alphabet B" unfolding dcai_def by simp
    have 2: "dca.initial (dcai A B) = (dca.initial A, dca.initial B)" unfolding dcai_def by simp
    have 3: "dca.rejecting (dcai A B) = (\<lambda> pq. (dca.rejecting A \<circ> fst) pq \<or> (dca.rejecting B \<circ> snd) pq)"
      unfolding dcai_def by auto
    have 4: "infs (dca.rejecting (dcai A B)) (DCA.trace (dcai A B) w (p, q)) \<longleftrightarrow>
      infs (dca.rejecting A) (DCA.trace A w p) \<or> infs (dca.rejecting B) (DCA.trace B w q)" for w p q
      unfolding 3 by blast
    show ?thesis unfolding DCA.language_def DCA.run_alt_def 1 2 4 by auto
  qed

  definition dcail :: "('label, 'state) dca list \<Rightarrow> ('label, 'state list) dca" where
    "dcail AA \<equiv> dca
      (INTER (set AA) dca.alphabet)
      (map dca.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dca.succ A a p) AA pp)
      (\<lambda> pp. \<exists> k < length AA. dca.rejecting (AA ! k) (pp ! k))"

  lemma dcail_trace_smap:
    assumes "length pp = length AA" "k < length AA"
    shows "smap (\<lambda> pp. pp ! k) (dca.trace (dcail AA) w pp) = dca.trace (AA ! k) w (pp ! k)"
    using assms unfolding dcail_def by (coinduction arbitrary: w pp) (force)
  lemma dcail_nodes_length:
    assumes "pp \<in> DCA.nodes (dcail AA)"
    shows "length pp = length AA"
    using assms unfolding dcail_def by induct auto
  lemma dcail_nodes[intro]:
    assumes "pp \<in> DCA.nodes (dcail AA)" "k < length pp"
    shows "pp ! k \<in> DCA.nodes (AA ! k)"
    using assms unfolding dcail_def by induct auto

  lemma dcail_finite[intro]:
    assumes "list_all (finite \<circ> DCA.nodes) AA"
    shows "finite (DCA.nodes (dcail AA))"
  proof (rule finite_subset)
    show "DCA.nodes (dcail AA) \<subseteq> listset (map DCA.nodes AA)"
      by (force simp: listset_member list_all2_conv_all_nth dcail_nodes_length)
    have "finite (listset (map DCA.nodes AA)) \<longleftrightarrow> list_all finite (map DCA.nodes AA)"
      by (rule listset_finite) (auto simp: list_all_iff)
    then show "finite (listset (map DCA.nodes AA))" using assms by (simp add: list.pred_map)
  qed
  lemma dcail_nodes_card:
    assumes "list_all (finite \<circ> DCA.nodes) AA"
    shows "card (DCA.nodes (dcail AA)) \<le> prod_list (map (card \<circ> DCA.nodes) AA)"
  proof -
    have "card (DCA.nodes (dcail AA)) \<le> card (listset (map DCA.nodes AA))"
    proof (rule card_mono)
      have "finite (listset (map DCA.nodes AA)) \<longleftrightarrow> list_all finite (map DCA.nodes AA)"
        by (rule listset_finite) (auto simp: list_all_iff)
      then show "finite (listset (map DCA.nodes AA))" using assms by (simp add: list.pred_map)
      show "DCA.nodes (dcail AA) \<subseteq> listset (map DCA.nodes AA)"
        by (force simp: listset_member list_all2_conv_all_nth dcail_nodes_length)
    qed
    also have "\<dots> = prod_list (map (card \<circ> DCA.nodes) AA)" by simp
    finally show ?thesis by this
  qed

  lemma dcail_language[simp]: "DCA.language (dcail AA) = INTER (set AA) DCA.language"
  proof safe
    fix A w
    assume 1: "w \<in> DCA.language (dcail AA)" "A \<in> set AA"
    obtain 2:
      "dca.run (dcail AA) w (dca.initial (dcail AA))"
      "\<not> infs (dca.rejecting (dcail AA)) (dca.trace (dcail AA) w (dca.initial (dcail AA)))"
      using 1(1) by rule
    obtain k where 3: "A = AA ! k" "k < length AA" using 1(2) unfolding in_set_conv_nth by auto
    have 4: "\<not> infs (\<lambda> pp. dca.rejecting A (pp ! k)) (dca.trace (dcail AA) w (map dca.initial AA))"
      using 2(2) 3 unfolding dcail_def by auto
    show "w \<in> DCA.language A"
    proof
      show "dca.run A w (dca.initial A)"
        using 1(2) 2(1) unfolding DCA.run_alt_def dcail_def by auto
      have "True \<longleftrightarrow> \<not> infs (\<lambda> pp. dca.rejecting A (pp ! k)) (dca.trace (dcail AA) w (map dca.initial AA))"
        using 4 by simp
      also have "\<dots> \<longleftrightarrow> \<not> infs (dca.rejecting A) (smap (\<lambda> pp. pp ! k)
        (dca.trace (dcail AA) w (map dca.initial AA)))" by (simp add: comp_def)
      also have "smap (\<lambda> pp. pp ! k) (dca.trace (dcail AA) w (map dca.initial AA)) =
        dca.trace (AA ! k) w (map dca.initial AA ! k)" using 3(2) by (fastforce intro: dcail_trace_smap)
      also have "\<dots> = dca.trace A w (dca.initial A)" using 3 by auto
      finally show "\<not> infs (dca.rejecting A) (DCA.trace A w (dca.initial A))" by simp
    qed
  next
    fix w
    assume 1: "w \<in> INTER (set AA) DCA.language"
    have 2: "dca.run A w (dca.initial A)" "\<not> infs (dca.rejecting A) (dca.trace A w (dca.initial A))"
      if "A \<in> set AA" for A using 1 that by auto
    have 3: "\<not> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k)) (dca.trace (dcail AA) w (map dca.initial AA))"
      if "k < length AA" for k
    proof -
      have "True \<longleftrightarrow> \<not> infs (dca.rejecting (AA ! k)) (dca.trace (AA ! k) w (map dca.initial AA ! k))"
        using 2(2) that by auto
      also have "dca.trace (AA ! k) w (map dca.initial AA ! k) =
        smap (\<lambda> pp. pp ! k) (dca.trace (dcail AA) w (map dca.initial AA))"
        using that by (fastforce intro: dcail_trace_smap[symmetric])
      also have "infs (dca.rejecting (AA ! k)) \<dots> \<longleftrightarrow> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k))
        (dca.trace (dcail AA) w (map dca.initial AA))" by (simp add: comp_def)
      finally show ?thesis by simp
    qed
    show "w \<in> DCA.language (dcail AA)"
    proof
      show "dca.run (dcail AA) w (dca.initial (dcail AA))"
        using 2(1) unfolding DCA.run_alt_def dcail_def by auto
      show "\<not> infs (dca.rejecting (dcail AA)) (dca.trace (dcail AA) w (dca.initial (dcail AA)))"
        using 3 unfolding dcail_def by auto
    qed
  qed

  definition dcgaul :: "('label, 'state) dca list \<Rightarrow> ('label, 'state list) dgca" where
    "dcgaul AA \<equiv> dgca
      (UNION (set AA) dca.alphabet)
      (map dca.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dca.succ A a p) AA pp)
      (map (\<lambda> k pp. dca.rejecting (AA ! k) (pp ! k)) [0 ..< length AA])"

  lemma dcgaul_trace_smap:
    assumes "length pp = length AA" "k < length AA"
    shows "smap (\<lambda> pp. pp ! k) (dgca.trace (dcgaul AA) w pp) = dca.trace (AA ! k) w (pp ! k)"
    using assms unfolding dcgaul_def by (coinduction arbitrary: w pp) (force)
  lemma dcgaul_nodes_length:
    assumes "pp \<in> DGCA.nodes (dcgaul AA)"
    shows "length pp = length AA"
    using assms unfolding dcgaul_def by induct auto
  lemma dcgaul_nodes[intro]:
    assumes "INTER (set AA) dca.alphabet = UNION (set AA) dca.alphabet"
    assumes "pp \<in> DGCA.nodes (dcgaul AA)" "k < length pp"
    shows "pp ! k \<in> DCA.nodes (AA ! k)"
    using assms(2, 3, 1) unfolding dcgaul_def by induct force+

  lemma dcgaul_nodes_finite[intro]:
    assumes "INTER (set AA) dca.alphabet = UNION (set AA) dca.alphabet"
    assumes "list_all (finite \<circ> DCA.nodes) AA"
    shows "finite (DGCA.nodes (dcgaul AA))"
  proof (rule finite_subset)
    show "DGCA.nodes (dcgaul AA) \<subseteq> listset (map DCA.nodes AA)"
      using assms(1) by (force simp: listset_member list_all2_conv_all_nth dcgaul_nodes_length)
    have "finite (listset (map DCA.nodes AA)) \<longleftrightarrow> list_all finite (map DCA.nodes AA)"
      by (rule listset_finite) (auto simp: list_all_iff)
    then show "finite (listset (map DCA.nodes AA))" using assms(2) by (simp add: list.pred_map)
  qed
  lemma dcgaul_nodes_card:
    assumes "INTER (set AA) dca.alphabet = UNION (set AA) dca.alphabet"
    assumes "list_all (finite \<circ> DCA.nodes) AA"
    shows "card (DGCA.nodes (dcgaul AA)) \<le> prod_list (map (card \<circ> DCA.nodes) AA)"
  proof -
    have "card (DGCA.nodes (dcgaul AA)) \<le> card (listset (map DCA.nodes AA))"
    proof (rule card_mono)
      have "finite (listset (map DCA.nodes AA)) \<longleftrightarrow> list_all finite (map DCA.nodes AA)"
        by (rule listset_finite) (auto simp: list_all_iff)
      then show "finite (listset (map DCA.nodes AA))" using assms(2) by (simp add: list.pred_map)
      show "DGCA.nodes (dcgaul AA) \<subseteq> listset (map DCA.nodes AA)"
        using assms(1) by (force simp: listset_member list_all2_conv_all_nth dcgaul_nodes_length)
    qed
    also have "\<dots> = prod_list (map (card \<circ> DCA.nodes) AA)" by simp
    finally show ?thesis by this
  qed

  lemma dcgaul_language[simp]:
    assumes "INTER (set AA) dca.alphabet = UNION (set AA) dca.alphabet"
    shows "DGCA.language (dcgaul AA) = UNION (set AA) DCA.language"
  proof safe
    fix w
    assume 1: "w \<in> DGCA.language (dcgaul AA)"
    obtain k where 2:
      "dgca.run (dcgaul AA) w (dgca.initial (dcgaul AA))"
      "k < length AA"
      "\<not> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k)) (dgca.trace (dcgaul AA) w (dgca.initial (dcgaul AA)))"
      using 1 unfolding dcgaul_def by force
    show "w \<in> UNION (set AA) DCA.language"
    proof (intro UN_I DCA.language)
      show "AA ! k \<in> set AA" using 2(2) by simp
      show "dca.run (AA ! k) w (dca.initial (AA ! k))"
        using assms 2(1, 2) unfolding DCA.run_alt_def DGCA.run_alt_def dcgaul_def by force
      have "True \<longleftrightarrow> \<not> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k))
        (dgca.trace (dcgaul AA) w (map dca.initial AA))" using 2(3) unfolding dcgaul_def by auto
      also have "\<dots> \<longleftrightarrow> \<not> infs (dca.rejecting (AA ! k))
        (smap (\<lambda> pp. pp ! k) (dgca.trace (dcgaul AA) w (map dca.initial AA)))" by (simp add: comp_def)
      also have "smap (\<lambda> pp. pp ! k) (dgca.trace (dcgaul AA) w (map dca.initial AA)) =
        dca.trace (AA ! k) w (map dca.initial AA ! k)" using 2(2) by (fastforce intro: dcgaul_trace_smap)
      also have "\<dots> = dca.trace (AA ! k) w (dca.initial (AA ! k))" using 2(2) by auto
      finally show "\<not> infs (dca.rejecting (AA ! k)) (dca.trace (AA ! k) w (dca.initial (AA ! k)))" by simp
    qed
  next
    fix A w
    assume 1: "A \<in> set AA" "w \<in> DCA.language A"
    obtain 2: "dca.run A w (dca.initial A)" "\<not> infs (dca.rejecting A) (dca.trace A w (dca.initial A))"
      using 1(2) by rule
    obtain k where 3: "A = AA ! k" "k < length AA" using 1(1) unfolding in_set_conv_nth by auto
    show "w \<in> DGCA.language (dcgaul AA)"
    proof (intro DGCA.language bexI cogen)
      show "dgca.run (dcgaul AA) w (dgca.initial (dcgaul AA))"
        using 1(1) 2(1) unfolding DCA.run_alt_def DGCA.run_alt_def dcgaul_def by auto
      have "True \<longleftrightarrow> \<not> infs (dca.rejecting (AA ! k)) (dca.trace (AA ! k) w (map dca.initial AA ! k))"
        using 2(2) 3 by auto
      also have "dca.trace (AA ! k) w (map dca.initial AA ! k) =
        smap (\<lambda> pp. pp ! k) (dgca.trace (dcgaul AA) w (map dca.initial AA))"
        using 3(2) by (fastforce intro: dcgaul_trace_smap[symmetric])
      also have "\<not> infs (dca.rejecting (AA ! k)) \<dots> \<longleftrightarrow> \<not> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k))
        (dgca.trace (dcgaul AA) w (map dca.initial AA))" by (simp add: comp_def)
      also have "map dca.initial AA = dgca.initial (dcgaul AA)" unfolding dcgaul_def by simp
      finally show "\<not> infs (\<lambda> pp. dca.rejecting (AA ! k) (pp ! k)) (dgca.trace (dcgaul AA) w (dgca.initial (dcgaul AA)))"
        by simp
      show "(\<lambda> pp. dca.rejecting (AA ! k) (pp ! k)) \<in> set (dgca.rejecting (dcgaul AA))"
        unfolding dcgaul_def using 3(2) by simp
    qed
  qed

  definition dcaul :: "('label, 'state) dca list \<Rightarrow> ('label, 'state list degen) dca" where
    "dcaul = degen \<circ> dcgaul"

  lemma dcaul_nodes_finite[intro]:
    assumes "INTER (set AA) dca.alphabet = UNION (set AA) dca.alphabet"
    assumes "list_all (finite \<circ> DCA.nodes) AA"
    shows "finite (DCA.nodes (dcaul AA))"
    using dcgaul_nodes_finite assms unfolding dcaul_def by auto
  lemma dcaul_nodes_card:
    assumes "INTER (set AA) dca.alphabet = UNION (set AA) dca.alphabet"
    assumes "list_all (finite \<circ> DCA.nodes) AA"
    shows "card (DCA.nodes (dcaul AA)) \<le> max 1 (length AA) * prod_list (map (card \<circ> DCA.nodes) AA)"
  proof -
    have "card (DCA.nodes (dcaul AA)) \<le>
      max 1 (length (dgca.rejecting (dcgaul AA))) * card (DGCA.nodes (dcgaul AA))"
      unfolding dcaul_def using degen_nodes_card by simp
    also have "length (dgca.rejecting (dcgaul AA)) = length AA" unfolding dcgaul_def by simp
    also have "card (DGCA.nodes (dcgaul AA)) \<le> prod_list (map (card \<circ> DCA.nodes) AA)"
      using dcgaul_nodes_card assms by this
    finally show ?thesis by simp
  qed

  lemma dcaul_language[simp]:
    assumes "INTER (set AA) dca.alphabet = UNION (set AA) dca.alphabet"
    shows "DCA.language (dcaul AA) = UNION (set AA) DCA.language"
    unfolding dcaul_def using degen_language dcgaul_language[OF assms] by auto

end