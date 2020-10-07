section \<open>Deterministic Büchi Automata Combinations\<close>

theory DBA_Combine
imports "DBA" "DGBA"
begin

  definition dbgail :: "('label, 'state) dba list \<Rightarrow> ('label, 'state list) dgba" where
    "dbgail AA \<equiv> dgba
      (INTER (set AA) dba.alphabet)
      (map dba.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dba.succ A a p) AA pp)
      (map (\<lambda> k pp. dba.accepting (AA ! k) (pp ! k)) [0 ..< length AA])"

  lemma dbgail_trace_smap:
    assumes "length pp = length AA" "k < length AA"
    shows "smap (\<lambda> pp. pp ! k) (dgba.trace (dbgail AA) w pp) = dba.trace (AA ! k) w (pp ! k)"
    using assms unfolding dbgail_def by (coinduction arbitrary: w pp) (force)
  lemma dbgail_nodes_length:
    assumes "pp \<in> DGBA.nodes (dbgail AA)"
    shows "length pp = length AA"
    using assms unfolding dbgail_def by induct auto
  lemma dbgail_nodes[intro]:
    assumes "pp \<in> DGBA.nodes (dbgail AA)" "k < length pp"
    shows "pp ! k \<in> DBA.nodes (AA ! k)"
    using assms unfolding dbgail_def by induct auto

  lemma dbgail_nodes_finite[intro]:
    assumes "list_all (finite \<circ> DBA.nodes) AA"
    shows "finite (DGBA.nodes (dbgail AA))"
  proof (rule finite_subset)
    show "DGBA.nodes (dbgail AA) \<subseteq> listset (map DBA.nodes AA)"
      by (force simp: listset_member list_all2_conv_all_nth dbgail_nodes_length)
    have "finite (listset (map DBA.nodes AA)) \<longleftrightarrow> list_all finite (map DBA.nodes AA)"
      by (rule listset_finite) (auto simp: list_all_iff)
    then show "finite (listset (map DBA.nodes AA))" using assms by (simp add: list.pred_map)
  qed
  lemma dbgail_nodes_card:
    assumes "list_all (finite \<circ> DBA.nodes) AA"
    shows "card (DGBA.nodes (dbgail AA)) \<le> prod_list (map (card \<circ> DBA.nodes) AA)"
  proof -
    have "card (DGBA.nodes (dbgail AA)) \<le> card (listset (map DBA.nodes AA))"
    proof (rule card_mono)
      have "finite (listset (map DBA.nodes AA)) \<longleftrightarrow> list_all finite (map DBA.nodes AA)"
        by (rule listset_finite) (auto simp: list_all_iff)
      then show "finite (listset (map DBA.nodes AA))" using assms by (simp add: list.pred_map)
      show "DGBA.nodes (dbgail AA) \<subseteq> listset (map DBA.nodes AA)"
        by (force simp: listset_member list_all2_conv_all_nth dbgail_nodes_length)
    qed
    also have "\<dots> = prod_list (map (card \<circ> DBA.nodes) AA)" by simp
    finally show ?thesis by this
  qed

  lemma dbgail_language[simp]: "DGBA.language (dbgail AA) = INTER (set AA) DBA.language"
  proof safe
    fix w A
    assume 1: "w \<in> DGBA.language (dbgail AA)" "A \<in> set AA"
    obtain 2:
      "dgba.run (dbgail AA) w (dgba.initial (dbgail AA))"
      "gen infs (dgba.accepting (dbgail AA)) (dgba.trace (dbgail AA) w (dgba.initial (dbgail AA)))"
      using 1(1) by rule
    obtain k where 3: "A = AA ! k" "k < length AA" using 1(2) unfolding in_set_conv_nth by auto
    have 4: "(\<lambda> pp. dba.accepting A (pp ! k)) \<in> set (dgba.accepting (dbgail AA))"
      using 3 unfolding dbgail_def by auto
    show "w \<in> DBA.language A"
    proof
      show "dba.run A w (dba.initial A)"
        using 1(2) 2(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbgail_def by auto
      have "True \<longleftrightarrow> infs (\<lambda> pp. dba.accepting A (pp ! k)) (dgba.trace (dbgail AA) w (map dba.initial AA))"
        using 2(2) 4 unfolding dbgail_def by auto
      also have "\<dots> \<longleftrightarrow> infs (dba.accepting A) (smap (\<lambda> pp. pp ! k)
        (dgba.trace (dbgail AA) w (map dba.initial AA)))" by (simp add: comp_def)
      also have "smap (\<lambda> pp. pp ! k) (dgba.trace (dbgail AA) w (map dba.initial AA)) =
        dba.trace (AA ! k) w (map dba.initial AA ! k)" using 3(2) by (fastforce intro: dbgail_trace_smap)
      also have "\<dots> = dba.trace A w (dba.initial A)" using 3 by auto
      finally show "infs (dba.accepting A) (dba.trace A w (dba.initial A))" by simp
    qed
  next
    fix w
    assume 1: "w \<in> INTER (set AA) DBA.language"
    have 2: "dba.run A w (dba.initial A)" "infs (dba.accepting A) (dba.trace A w (dba.initial A))"
      if "A \<in> set AA" for A using 1 that by auto
    show "w \<in> DGBA.language (dbgail AA)"
    proof (intro DGBA.language ballI gen)
      show "dgba.run (dbgail AA) w (dgba.initial (dbgail AA))"
        using 2(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbgail_def by auto
    next
      fix P
      assume 3: "P \<in> set (dgba.accepting (dbgail AA))"
      obtain k where 4: "P = (\<lambda> pp. dba.accepting (AA ! k) (pp ! k))" "k < length AA"
        using 3 unfolding dbgail_def by auto
      have "True \<longleftrightarrow> infs (dba.accepting (AA ! k)) (dba.trace (AA ! k) w (map dba.initial AA ! k))"
        using 2(2) 4(2) by auto
      also have "dba.trace (AA ! k) w (map dba.initial AA ! k) =
        smap (\<lambda> pp. pp ! k) (dgba.trace (dbgail AA) w (map dba.initial AA))"
        using 4(2) by (fastforce intro: dbgail_trace_smap[symmetric])
      also have "infs (dba.accepting (AA ! k)) \<dots> \<longleftrightarrow> infs P (dgba.trace (dbgail AA) w (map dba.initial AA))"
        unfolding 4(1) by (simp add: comp_def)
      also have "map dba.initial AA = dgba.initial (dbgail AA)" unfolding dbgail_def by simp
      finally show "infs P (dgba.trace (dbgail AA) w (dgba.initial (dbgail AA)))" by simp
    qed
  qed

  definition dbail :: "('label, 'state) dba list \<Rightarrow> ('label, 'state list degen) dba" where
    "dbail = degen \<circ> dbgail"

  lemma dbail_nodes_finite[intro]:
    assumes "list_all (finite \<circ> DBA.nodes) AA"
    shows "finite (DBA.nodes (dbail AA))"
    using dbgail_nodes_finite assms unfolding dbail_def by auto
  lemma dbail_nodes_card:
    assumes"list_all (finite \<circ> DBA.nodes) AA"
    shows "card (DBA.nodes (dbail AA)) \<le> max 1 (length AA) * prod_list (map (card \<circ> DBA.nodes) AA)"
  proof -
    have "card (DBA.nodes (dbail AA)) \<le>
      max 1 (length (dgba.accepting (dbgail AA))) * card (DGBA.nodes (dbgail AA))"
      unfolding dbail_def using degen_nodes_card by simp
    also have "length (dgba.accepting (dbgail AA)) = length AA" unfolding dbgail_def by simp
    also have "card (DGBA.nodes (dbgail AA)) \<le> prod_list (map (card \<circ> DBA.nodes) AA)"
      using dbgail_nodes_card assms by this
    finally show ?thesis by simp
  qed

  lemma dbail_language[simp]: "DBA.language (dbail AA) = INTER (set AA) DBA.language"
    unfolding dbail_def using degen_language dbgail_language by auto

  definition dbau :: "('label, 'state\<^sub>1) dba \<Rightarrow> ('label, 'state\<^sub>2) dba \<Rightarrow>
    ('label, 'state\<^sub>1 \<times> 'state\<^sub>2) dba" where
    "dbau A B \<equiv> dba
      (dba.alphabet A \<union> dba.alphabet B)
      (dba.initial A, dba.initial B)
      (\<lambda> a (p, q). (dba.succ A a p, dba.succ B a q))
      (\<lambda> (p, q). dba.accepting A p \<or> dba.accepting B q)"

  lemma dbau_fst[iff]: "infs (P \<circ> fst) (dba.trace (dbau A B) w (p, q)) \<longleftrightarrow> infs P (dba.trace A w p)"
  proof -
    let ?t = "dba.trace (dbau A B) w (p, q)"
    have "infs (P \<circ> fst) ?t \<longleftrightarrow> infs P (smap fst ?t)" by simp
    also have "smap fst ?t = dba.trace A w p" unfolding dbau_def by (coinduction arbitrary: w p q) (auto)
    finally show ?thesis by this
  qed
  lemma dbau_snd[iff]: "infs (P \<circ> snd) (dba.trace (dbau A B) w (p, q)) \<longleftrightarrow> infs P (dba.trace B w q)"
  proof -
    let ?t = "dba.trace (dbau A B) w (p, q)"
    have "infs (P \<circ> snd) ?t \<longleftrightarrow> infs P (smap snd ?t)" by simp
    also have "smap snd ?t = dba.trace B w q" unfolding dbau_def by (coinduction arbitrary: w p q) (auto)
    finally show ?thesis by this
  qed
  lemma dbau_nodes_fst[intro]:
    assumes "dba.alphabet A = dba.alphabet B"
    shows "fst ` DBA.nodes (dbau A B) \<subseteq> DBA.nodes A"
  proof (rule subsetI, erule imageE)
    fix pq p
    assume "pq \<in> DBA.nodes (dbau A B)" "p = fst pq"
    then show "p \<in> DBA.nodes A" using assms unfolding dbau_def by (induct arbitrary: p) (auto)
  qed
  lemma dbau_nodes_snd[intro]:
    assumes "dba.alphabet A = dba.alphabet B"
    shows "snd ` DBA.nodes (dbau A B) \<subseteq> DBA.nodes B"
  proof (rule subsetI, erule imageE)
    fix pq q
    assume "pq \<in> DBA.nodes (dbau A B)" "q = snd pq"
    then show "q \<in> DBA.nodes B" using assms unfolding dbau_def by (induct arbitrary: q) (auto)
  qed

  lemma dbau_nodes_finite[intro]:
    assumes "dba.alphabet A = dba.alphabet B"
    assumes "finite (DBA.nodes A)" "finite (DBA.nodes B)"
    shows "finite (DBA.nodes (dbau A B))"
  proof (rule finite_subset)
    show "DBA.nodes (dbau A B) \<subseteq> DBA.nodes A \<times> DBA.nodes B"
      using dbau_nodes_fst[OF assms(1)] dbau_nodes_snd[OF assms(1)] unfolding image_subset_iff by force
    show "finite (DBA.nodes A \<times> DBA.nodes B)" using assms(2, 3) by simp
  qed
  lemma dbau_nodes_card[intro]:
    assumes "dba.alphabet A = dba.alphabet B"
    assumes "finite (DBA.nodes A)" "finite (DBA.nodes B)"
    shows "card (DBA.nodes (dbau A B)) \<le> card (DBA.nodes A) * card (DBA.nodes B)"
  proof -
    have "card (DBA.nodes (dbau A B)) \<le> card (DBA.nodes A \<times> DBA.nodes B)"
    proof (rule card_mono)
      show "finite (DBA.nodes A \<times> DBA.nodes B)" using assms(2, 3) by simp
      show "DBA.nodes (dbau A B) \<subseteq> DBA.nodes A \<times> DBA.nodes B"
        using dbau_nodes_fst[OF assms(1)] dbau_nodes_snd[OF assms(1)] unfolding image_subset_iff by force
    qed
    also have "\<dots> = card (DBA.nodes A) * card (DBA.nodes B)" using card_cartesian_product by this
    finally show ?thesis by this
  qed

  lemma dbau_language[simp]:
    assumes "dba.alphabet A = dba.alphabet B"
    shows "DBA.language (dbau A B) = DBA.language A \<union> DBA.language B"
  proof -
    have 1: "dba.alphabet (dbau A B) = dba.alphabet A \<union> dba.alphabet B" unfolding dbau_def by simp
    have 2: "dba.initial (dbau A B) = (dba.initial A, dba.initial B)" unfolding dbau_def by simp
    have 3: "dba.accepting (dbau A B) = (\<lambda> pq. (dba.accepting A \<circ> fst) pq \<or> (dba.accepting B \<circ> snd) pq)"
      unfolding dbau_def by auto
    have 4: "infs (dba.accepting (dbau A B)) (DBA.trace (dbau A B) w (p, q)) \<longleftrightarrow>
      infs (dba.accepting A) (DBA.trace A w p) \<or> infs (dba.accepting B) (DBA.trace B w q)" for w p q
      unfolding 3 by blast
    show ?thesis using assms unfolding DBA.language_def DBA.run_alt_def 1 2 4 by auto
  qed

  definition dbaul :: "('label, 'state) dba list \<Rightarrow> ('label, 'state list) dba" where
    "dbaul AA \<equiv> dba
      (UNION (set AA) dba.alphabet)
      (map dba.initial AA)
      (\<lambda> a pp. map2 (\<lambda> A p. dba.succ A a p) AA pp)
      (\<lambda> pp. \<exists> k < length AA. dba.accepting (AA ! k) (pp ! k))"

  lemma dbaul_trace_smap:
    assumes "length pp = length AA" "k < length AA"
    shows "smap (\<lambda> pp. pp ! k) (dba.trace (dbaul AA) w pp) = dba.trace (AA ! k) w (pp ! k)"
    using assms unfolding dbaul_def by (coinduction arbitrary: w pp) (force)
  lemma dbaul_nodes_length:
    assumes "pp \<in> DBA.nodes (dbaul AA)"
    shows "length pp = length AA"
    using assms unfolding dbaul_def by induct auto
  lemma dbaul_nodes[intro]:
    assumes "INTER (set AA) dba.alphabet = UNION (set AA) dba.alphabet"
    assumes "pp \<in> DBA.nodes (dbaul AA)" "k < length pp"
    shows "pp ! k \<in> DBA.nodes (AA ! k)"
    using assms(2, 3, 1) unfolding dbaul_def by induct force+

  lemma dbaul_nodes_finite[intro]:
    assumes "INTER (set AA) dba.alphabet = UNION (set AA) dba.alphabet"
    assumes "list_all (finite \<circ> DBA.nodes) AA"
    shows "finite (DBA.nodes (dbaul AA))"
  proof (rule finite_subset)
    show "DBA.nodes (dbaul AA) \<subseteq> listset (map DBA.nodes AA)"
      using assms(1) by (force simp: listset_member list_all2_conv_all_nth dbaul_nodes_length)
    have "finite (listset (map DBA.nodes AA)) \<longleftrightarrow> list_all finite (map DBA.nodes AA)"
      by (rule listset_finite) (auto simp: list_all_iff)
    then show "finite (listset (map DBA.nodes AA))" using assms(2) by (simp add: list.pred_map)
  qed
  lemma dbaul_nodes_card:
    assumes "INTER (set AA) dba.alphabet = UNION (set AA) dba.alphabet"
    assumes "list_all (finite \<circ> DBA.nodes) AA"
    shows "card (DBA.nodes (dbaul AA)) \<le> prod_list (map (card \<circ> DBA.nodes) AA)"
  proof -
    have "card (DBA.nodes (dbaul AA)) \<le> card (listset (map DBA.nodes AA))"
    proof (rule card_mono)
      have "finite (listset (map DBA.nodes AA)) \<longleftrightarrow> list_all finite (map DBA.nodes AA)"
        by (rule listset_finite) (auto simp: list_all_iff)
      then show "finite (listset (map DBA.nodes AA))" using assms(2) by (simp add: list.pred_map)
      show "DBA.nodes (dbaul AA) \<subseteq> listset (map DBA.nodes AA)"
        using assms(1) by (force simp: listset_member list_all2_conv_all_nth dbaul_nodes_length)
    qed
    also have "\<dots> = prod_list (map (card \<circ> DBA.nodes) AA)" by simp
    finally show ?thesis by this
  qed

  lemma dbaul_language[simp]:
    assumes "INTER (set AA) dba.alphabet = UNION (set AA) dba.alphabet"
    shows "DBA.language (dbaul AA) = UNION (set AA) DBA.language"
  proof safe
    fix w
    assume 1: "w \<in> DBA.language (dbaul AA)"
    obtain 2:
      "dba.run (dbaul AA) w (dba.initial (dbaul AA))"
      "infs (dba.accepting (dbaul AA)) (dba.trace (dbaul AA) w (dba.initial (dbaul AA)))"
      using 1 by rule
    obtain k where 3:
      "k < length AA"
      "infs (\<lambda> pp. dba.accepting (AA ! k) (pp ! k)) (dba.trace (dbaul AA) w (map dba.initial AA))"
      using 2(2) unfolding dbaul_def by auto
    show "w \<in> UNION (set AA) DBA.language"
    proof (intro UN_I DBA.language)
      show "AA ! k \<in> set AA" using 3(1) by simp
      show "dba.run (AA ! k) w (dba.initial (AA ! k))"
        using assms 2(1) 3(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbaul_def by force
      have "True \<longleftrightarrow> infs (\<lambda> pp. dba.accepting (AA ! k) (pp ! k))
        (dba.trace (dbaul AA) w (map dba.initial AA))" using 3(2) by auto
      also have "\<dots> \<longleftrightarrow> infs (dba.accepting (AA ! k))
        (smap (\<lambda> pp. pp ! k) (dba.trace (dbaul AA) w (map dba.initial AA)))" by (simp add: comp_def)
      also have "smap (\<lambda> pp. pp ! k) (dba.trace (dbaul AA) w (map dba.initial AA)) =
        dba.trace (AA ! k) w (map dba.initial AA ! k)" using 3(1) by (fastforce intro: dbaul_trace_smap)
      also have "\<dots> = dba.trace (AA ! k) w (dba.initial (AA ! k))" using 3 by auto
      finally show "infs (dba.accepting (AA ! k)) (dba.trace (AA ! k) w (dba.initial (AA ! k)))" by simp
    qed
  next
    fix A w
    assume 1: "A \<in> set AA" "w \<in> DBA.language A"
    obtain 2: "dba.run A w (dba.initial A)" "infs (dba.accepting A) (dba.trace A w (dba.initial A))"
      using 1(2) by rule
    obtain k where 3: "A = AA ! k" "k < length AA" using 1(1) unfolding in_set_conv_nth by auto
    show "w \<in> DBA.language (dbaul AA)"
    proof
      show "dba.run (dbaul AA) w (dba.initial (dbaul AA))"
        using 1(1) 2(1) unfolding DBA.run_alt_def DGBA.run_alt_def dbaul_def by auto
      have "True \<longleftrightarrow> infs (dba.accepting (AA ! k)) (dba.trace (AA ! k) w (map dba.initial AA ! k))"
        using 2(2) 3 by auto
      also have "dba.trace (AA ! k) w (map dba.initial AA ! k) =
        smap (\<lambda> pp. pp ! k) (dba.trace (dbaul AA) w (map dba.initial AA))"
        using 3(2) by (fastforce intro: dbaul_trace_smap[symmetric])
      also have "infs (dba.accepting (AA ! k)) \<dots> \<longleftrightarrow> infs (\<lambda> pp. dba.accepting (AA ! k) (pp ! k))
        (dba.trace (dbaul AA) w (map dba.initial AA))" by (simp add: comp_def)
      finally show "infs (dba.accepting (dbaul AA)) (dba.trace (dbaul AA) w (dba.initial (dbaul AA)))"
        using 3(2) unfolding dbaul_def by auto
    qed
  qed

end