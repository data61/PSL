(*  Title:      Construct_SSA_code.thy
    Author:     Denis Lohner, Sebastian Ullrich
*)

subsection \<open>Code Equations for SSA Construction\<close>

theory Construct_SSA_code imports
  SSA_CFG_code
  Construct_SSA
  Mapping_Exts
  "HOL-Library.Product_Lexorder"
begin

definition[code]: "lookup_multimap m k \<equiv> (case_option {} id (Mapping.lookup m k))"

locale CFG_Construct_linorder = CFG_Construct_wf \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses"
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> ('var::linorder) set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set"
begin
  type_synonym ('n, 'v) sparse_phis = "('n \<times> 'v, ('n, 'v) ssaVal list) mapping"

  function readVariableRecursive :: "'g \<Rightarrow> 'var \<Rightarrow> 'node \<Rightarrow> ('node, 'var) sparse_phis \<Rightarrow> (('node, 'var) ssaVal \<times> ('node, 'var) sparse_phis)"
       and readArgs :: "'g \<Rightarrow> 'var \<Rightarrow> 'node \<Rightarrow> ('node, 'var) sparse_phis \<Rightarrow> 'node list \<Rightarrow> ('node, 'var) sparse_phis \<times> ('node, 'var) ssaVal list"
  where[code]: "readVariableRecursive g v n phis = (if v \<in> defs g n then ((v,n,SimpleDef), phis)
    else case predecessors g n of
      []  \<Rightarrow> ((v,n,PhiDef), Mapping.update (n,v) [] phis)
    | [m] \<Rightarrow> readVariableRecursive g v m phis
    | ms  \<Rightarrow> (case Mapping.lookup phis (n,v) of
        Some _ \<Rightarrow> ((v,n,PhiDef),phis)
      | None \<Rightarrow>
        let phis = Mapping.update (n,v) [] phis in
        let (phis,args) = readArgs g v n phis ms in
        ((v,n,PhiDef), Mapping.update (n,v) args phis)
  ))"
  | "readArgs g v n phis [] = (phis,[])"
  | "readArgs g v n phis (m#ms) = (
      let (phis,args) = readArgs g v n phis ms in
      let (v,phis) = readVariableRecursive g v m phis in
      (phis,v#args))"
  by pat_completeness auto

  lemma length_filter_less2:
    assumes "x \<in> set xs" "\<not>P x" "Q x" "\<And>x. P x \<Longrightarrow> Q x"
    shows "length (filter P xs) < length (filter Q xs)"
  proof-
    have "\<And>x. (Q x \<and> P x) = P x"
      using assms(4) by auto
    hence "filter P xs = filter P (filter Q xs)"
      by auto
    also have "length (...) < length (filter Q xs)"
      using assms(1-3) by - (rule length_filter_less, auto)
    finally show ?thesis .
  qed

  lemma length_filter_le2:
    assumes "\<And>x. P x \<Longrightarrow> Q x"
    shows "length (filter P xs) \<le> length (filter Q xs)"
  proof-
    have "\<And>x. (Q x \<and> P x) = P x"
      using assms by auto
    hence "filter P xs = filter P (filter Q xs)"
      by auto
    also have "length (...) \<le> length (filter Q xs)"
      by - (rule length_filter_le)
    finally show ?thesis .
  qed

  abbreviation "phis_measure g v phis \<equiv> length [n \<leftarrow> \<alpha>n g. Mapping.lookup phis (n,v) = None]"

  lemma phis_measure_update_le: "phis_measure g v (Mapping.update k a p) \<le> phis_measure g v p"
  apply (rule length_filter_le2)
  apply (case_tac "k = (x, v)")
   apply (auto simp: lookup_update lookup_update_neq)
  done

  lemma phis_measure_update_le': "phis_measure g v p \<le> phis_measure g v (Mapping.update k [] phis) \<Longrightarrow>
       phis_measure g v (Mapping.update k a p) \<le> phis_measure g v phis"
  apply (rule le_trans, rule phis_measure_update_le)
  apply (rule le_trans, assumption, rule phis_measure_update_le)
  done

  lemma readArgs_phis_le:
    "readVariableRecursive_readArgs_dom (Inl (g, v, n, phis)) \<Longrightarrow> (val,p) = readVariableRecursive g v n phis \<Longrightarrow> phis_measure g v p \<le> phis_measure g v phis"
    "readVariableRecursive_readArgs_dom (Inr (g, v, n, phis, ms)) \<Longrightarrow> (p,u) = readArgs g v n phis ms \<Longrightarrow> phis_measure g v p \<le> phis_measure g v phis"
  proof (induction arbitrary: val p and p u rule: readVariableRecursive_readArgs.pinduct)
    case (1 g v n phis)
    show ?case
    using "1.IH"(1,2) "1.prems"
    apply (auto simp: readVariableRecursive.psimps Let_def phis_measure_update_le split: if_split_asm list.splits option.splits prod.splits)
    apply (subgoal_tac "phis_measure g v x1 \<le> phis_measure g v (Mapping.update (n,v) [] phis)")
     defer
     apply (rule "1.IH"(3))
     apply (auto simp: phis_measure_update_le')
    done
  next
    case (3 g v n m ms phis)
    from "3.IH"(1) "3.prems" show ?case
    apply (auto simp: readArgs.psimps split: prod.splits)
    apply (rule le_trans)
     apply (rule "3.IH"(3))
     apply auto
    apply (rule "3.IH"(2))
    apply auto
    done
  qed (auto simp: readArgs.psimps split: prod.splits)

  termination
  apply (relation "measures [
    \<lambda>args. let (g,v,phis) = case args of Inl((g,v,n,phis)) \<Rightarrow> (g,v,phis) | Inr((g,v,n,phis,ms)) \<Rightarrow> (g,v,phis) in
      phis_measure g v phis,
    \<lambda>args. case args of Inl(_) \<Rightarrow> 0 | Inr((g,v,n,phis,ms)) \<Rightarrow> length ms,
    \<lambda>args. let (g,n) = case args of Inl((g,v,n,phis)) \<Rightarrow> (g,n) | Inr((g,v,n,ms,phis)) \<Rightarrow> (g,n) in
      shortestPath g n
    ]")
  apply (auto intro: shortestPath_single_predecessor)[2]
  apply clarsimp
  apply (rule_tac x=n in length_filter_less2)
     apply (rule successor_in_\<alpha>n; auto)
    apply (auto simp: lookup_update)[2]
  apply (case_tac "x=n"; auto simp: lookup_update_neq)
  apply (auto dest: readArgs_phis_le)
  done

  declare readVariableRecursive.simps[simp del] readArgs.simps[simp del]

  lemma fst_readVariableRecursive:
    assumes "n \<in> set (\<alpha>n g)"
    shows "fst (readVariableRecursive g v n phis) = lookupDef g n v"
  using assms
  apply (induction rule: lookupDef_induct[where v=v])
    apply (simp add: readVariableRecursive.simps)
   apply (simp add: readVariableRecursive.simps; auto simp: split_def Let_def split: list.split option.split)
  apply (auto simp add: readVariableRecursive.simps)
  done

  definition "phis'_aux g v ns (phis:: ('node,'var) sparse_phis) \<equiv> Mapping.Mapping (\<lambda>(m,v\<^sub>2).
    (if v\<^sub>2=v \<and> m \<in> \<Union>(phiDefNodes_aux g v [n \<leftarrow> \<alpha>n g. (n,v) \<notin> Mapping.keys phis] ` ns) \<and> v \<in> vars g then Some (map (\<lambda>m. lookupDef g m v) (predecessors g m)) else (Mapping.lookup phis (m,v\<^sub>2))))"

  lemma phis'_aux_keys_super: "Mapping.keys (phis'_aux g v ns phis) \<supseteq> Mapping.keys phis"
    by (auto simp: keys_dom_lookup phis'_aux_def)

  lemma phiDefNodes_aux_in_unvisited:
    shows "phiDefNodes_aux g v un n \<subseteq> set un"
  proof (induction un arbitrary: n rule:removeAll_induct)
    case (1 un)
    show ?case
    apply (simp only: phiDefNodes_aux.simps)
    apply (auto elim!: fold_union_elem)
     apply (rename_tac m n')
     apply (drule_tac x2=n and n2=n' in 1)
     apply auto[1]
    apply (rename_tac m n')
    apply (drule_tac x2=n and n2=n' in 1)
    apply auto
    done
  qed

  lemma phiDefNodes_aux_unvisited_monotonic:
    assumes "set un \<subseteq> set un'"
    shows "phiDefNodes_aux g v un n \<subseteq> phiDefNodes_aux g v un' n"
  using assms proof (induction un arbitrary: un' n rule:removeAll_induct)
    case (1 un)
    {
      fix m A
      assume "n \<in> set un"
      hence a: "\<And>m. phiDefNodes_aux g v (removeAll n un) m \<subseteq> phiDefNodes_aux g v (removeAll n un') m"
      apply (rule 1)
      using 1(2)
      by auto

      assume "m \<in> fold (\<union>) (map (phiDefNodes_aux g v (removeAll n un)) (predecessors g n)) A"
      hence "m \<in> fold (\<union>) (map (phiDefNodes_aux g v (removeAll n un')) (predecessors g n)) A"
      apply (rule fold_union_elem)
      apply (rule fold_union_elemI')
      apply (auto simp: image_def dest: a[THEN subsetD])
      done
    }
    with 1(2) show ?case
    apply (subst(1 2) phiDefNodes_aux.simps)
    by auto
  qed

  lemma phiDefNodes_aux_single_pred:
    assumes "predecessors g n = [m]"
    shows "phiDefNodes_aux g v (removeAll n un) m = phiDefNodes_aux g v un m"
  proof-
    {
      fix n' ns
      assume asm: "g \<turnstile> n'-ns\<rightarrow>m" "distinct ns" "length (predecessors g n') \<noteq> 1" "n \<in> set ns"
      then obtain ns\<^sub>1 ns\<^sub>2 where split: "g \<turnstile> n'-ns\<^sub>1\<rightarrow>n" "g \<turnstile> n-ns\<^sub>2\<rightarrow>m" "ns = butlast ns\<^sub>1 @ ns\<^sub>2"
        by - (rule path2_split_ex)
      with \<open>distinct ns\<close> have "m \<notin> set (butlast ns\<^sub>1)"
        by (auto dest: path2_last_in_ns)
      from split(1,2) have False
      apply-
      apply (frule path2_unsnoc)
        apply (erule path2_nontrivial)
        using assms asm(3) \<open>m \<notin> set (butlast ns\<^sub>1)\<close>
        apply (auto dest: path2_not_Nil)
      done
    }
    with assms show ?thesis
    apply-
    apply rule
     apply (rule phiDefNodes_aux_unvisited_monotonic; auto)
    apply (rule subsetI)
    apply (rename_tac n')
    apply (erule phiDefNodes_auxE)
     apply (rule predecessor_is_node[where n'=n]; auto)
    apply (rule phiDefNodes_auxI; auto)
    done
  qed

  lemma phis'_aux_finite:
    assumes "finite (Mapping.keys phis)"
    shows "finite (Mapping.keys (phis'_aux g v ns phis))"
  proof-
    have a: "\<And>n. phiDefNodes_aux g v [n\<leftarrow>\<alpha>n g . (n, v) \<notin> dom (Mapping.lookup phis)] n \<subseteq> (set (\<alpha>n g))"
      by (rule subset_trans, rule phiDefNodes_aux_in_unvisited, auto)
    have "Mapping.keys (phis'_aux g v ns phis) \<subseteq> set (\<alpha>n g) \<times> vars g \<union> Mapping.keys phis"
      by (auto simp: phis'_aux_def keys_dom_lookup split: if_split_asm dest: subsetD[OF a])
    thus ?thesis by (rule finite_subset, auto intro: assms)
  qed

  lemma phiDefNodes_aux_redirect:
    assumes asm: "g \<turnstile> n-ns\<rightarrow>m"  "\<forall>n \<in> set ns. v \<notin> defs g n" "length (predecessors g n) \<noteq> 1" "unvisitedPath un ns"
    assumes n': "n' \<in> set ns" "n' \<in> phiDefNodes_aux g v un m'" "m' \<in> set (\<alpha>n g)"
    shows "n \<in> phiDefNodes_aux g v un m'"
  proof-
    from asm(1) n'(1) obtain ns\<^sub>1 where ns\<^sub>1: "g \<turnstile> n-ns\<^sub>1\<rightarrow>n'" "set ns\<^sub>1 \<subseteq> set ns"
      by (rule path2_split_ex, simp)

    from n'(2-3) obtain ns' where ns': "g \<turnstile> n'-ns'\<rightarrow>m'" "\<forall>n \<in> set ns'. v \<notin> defs g n" "length (predecessors g n') \<noteq> 1"
      "unvisitedPath un ns'"
      by (rule phiDefNodes_auxE)

    from ns\<^sub>1(1) ns'(1) obtain ms where ms: "g \<turnstile> n-ms\<rightarrow>m'" "distinct ms" "set ms \<subseteq> set ns\<^sub>1 \<union> set (tl ns')"
      by - (drule path2_app, auto elim: simple_path2)

    show ?thesis
    using ms(1)
    apply (rule phiDefNodes_auxI)
      using ms asm(4) ns\<^sub>1(2) ns'(4)
      apply clarsimp
      apply (rename_tac x)
      apply (case_tac "x \<in> set ns\<^sub>1")
       apply (drule_tac A="set ns" and c=x in subsetD; auto)
      apply (drule_tac A="set ns'" and c=x in subsetD; auto)
     using asm(2-3) ns\<^sub>1(2) ns'(2) ms(3)
     apply (auto dest!: bspec)
    done
  qed

  lemma snd_readVariableRecursive:
    assumes "v \<in> vars g" "n \<in> set (\<alpha>n g)" "finite (Mapping.keys phis)"
    "\<And>n. (n,v) \<in> Mapping.keys phis \<Longrightarrow> length (predecessors g n) \<noteq> 1" "Mapping.lookup phis (Entry g,v) \<in> {None, Some []}"
    shows
      "phis'_aux g v {n} phis = snd (readVariableRecursive g v n phis)"
      "set ms \<subseteq> set (\<alpha>n g) \<Longrightarrow> (phis'_aux g v (set ms) phis, map (\<lambda>m. lookupDef g m v) ms) = readArgs g v n phis ms"
  using assms proof (induction g v n phis and g v n phis ms rule: readVariableRecursive_readArgs.induct)
    case (1 g v n phis)
    note "1.prems"(1-3)[simp]
    note phis_wf = "1.prems"(4)[rule_format]

    from "1.prems"(5) have a: "(Entry g,v) \<in> Mapping.keys phis \<Longrightarrow> Mapping.lookup phis (Entry g, v) = Some []"
    by (auto simp: keys_dom_lookup)

    have IH1: "\<And>m. v \<notin> defs g n \<Longrightarrow> predecessors g n = [m] \<Longrightarrow> phis'_aux g v {m} phis = snd (readVariableRecursive g v m phis)"
    apply (rule "1.IH"[rule_format])
          apply auto[4]
      apply (rule_tac n'=n in predecessor_is_node; auto)
     using "1.prems"(5)
     apply (auto dest: phis_wf)
    done

    {
      fix m\<^sub>1 m\<^sub>2 :: 'node
      fix ms' :: "'node list"
      let ?ms = "m\<^sub>1#m\<^sub>2#ms'"
      let ?phis' = "Mapping.update (n,v) [] phis"
      assume asm: "v \<notin> defs g n" "predecessors g n = ?ms" "Mapping.lookup phis (n, v) = None"
      moreover have "set ?ms \<subseteq> set (\<alpha>n g)"
        by (rule subsetI, rule predecessor_is_node[of _ g n]; auto simp: asm(2))
      ultimately have "readArgs g v n ?phis' ?ms = (phis'_aux g v (set ?ms) ?phis', map (\<lambda>m. lookupDef g m v) ?ms)"
      using "1.prems"(5)
      by - (rule "1.IH"(2)[symmetric, rule_format]; auto dest: phis_wf simp: lookup_update_cases)
    }
    note IH2 = this

    note foldr_Cons[simp del] fold_Cons[simp del] list.map(2)[simp del] set_simps(2)[simp del]

    have c: "\<And>f x. \<Union>(f ` {x}) = f x" by auto

    show ?case
    unfolding phis'_aux_def c
    apply (subst readVariableRecursive.simps)
    apply (subst phiDefNodes_aux.simps[abs_def])
    apply (cases "predecessors g n")
     apply (auto simp: a Mapping_eq_lookup lookup_update_cases Entry_iff_unreachable[OF invar] split: list.split intro!: ext)[1]
    apply (rename_tac m\<^sub>1 ms)
    apply (case_tac ms)
     apply (subst Mapping_eq_lookup)
     apply (intro ext)
     apply (auto simp: fold_Cons list.map(2))[1]
        apply (auto dest: phis_wf)[1]
       apply (subst IH1[symmetric], assumption, assumption)
       apply (auto simp: phis'_aux_def)[1]
       apply (drule rev_subsetD, rule phiDefNodes_aux_unvisited_monotonic[where un'="[n\<leftarrow>\<alpha>n g . (n, v) \<notin> Mapping.keys phis]"]; auto)
      apply (subst IH1[symmetric], assumption, assumption)
      apply (auto simp: phis'_aux_def)[1]
     apply (subst IH1[symmetric], assumption, assumption)
     apply (auto simp: phis'_aux_def phiDefNodes_aux_single_pred)[1]
    apply (auto simp: Mapping_eq_lookup lookup_update_cases intro!: ext)
       apply (auto simp: keys_dom_lookup)[1]
      apply (auto split: option.split prod.split)[1]
       apply (subst(asm) IH2, assumption, assumption, assumption)
       apply (erule fold_union_elem)
       apply (auto simp: lookup_update_cases phis'_aux_def[abs_def])[1]
         apply (drule rev_subsetD, rule phiDefNodes_aux_unvisited_monotonic[where un'="[n'\<leftarrow>\<alpha>n g . n' \<noteq> n \<and> (n', v) \<notin> Mapping.keys phis]"]; auto)
        apply (drule rev_subsetD, rule phiDefNodes_aux_unvisited_monotonic[where un'="[n'\<leftarrow>\<alpha>n g . n' \<noteq> n \<and> (n', v) \<notin> Mapping.keys phis]"]; auto)
       apply (rename_tac m)
       apply (erule_tac x=m in ballE)
        apply (drule rev_subsetD, rule phiDefNodes_aux_unvisited_monotonic[where un'="[n'\<leftarrow>\<alpha>n g . n' \<noteq> n \<and> (n', v) \<notin> Mapping.keys phis]"]; auto)
       apply auto[1]
      apply (subst(asm) IH2, assumption, assumption)
       apply (auto simp: keys_dom_lookup)[2]
     apply (auto split: option.split prod.split)[1]
     apply (subst(asm) IH2, assumption, assumption, assumption)
     apply (auto simp: lookup_update_neq phis'_aux_def)[1]
    apply (auto split: option.splits prod.splits)[1]
    apply (subst(asm) IH2, assumption, assumption, assumption)
    apply (auto simp: lookup_update_cases phis'_aux_def removeAll_filter_not_eq image_def split: if_split_asm)[1]
       apply (cut_tac fold_union_elemI)
         apply auto[3]
      apply (cut_tac fold_union_elemI)
        apply auto[1]
       apply assumption
      apply (subgoal_tac "[x\<leftarrow>\<alpha>n g . x \<noteq> n \<and> (x, v) \<notin> Mapping.keys phis] = [x\<leftarrow>\<alpha>n g . (x, v) \<notin> Mapping.keys phis \<and> n \<noteq> x]")
       apply auto[1]
      apply (rule arg_cong2[where f=filter])
       apply auto[2]
     apply (cut_tac fold_union_elemI)
       apply auto[1]
      apply assumption
     apply (subgoal_tac "[x\<leftarrow>\<alpha>n g . x \<noteq> n \<and> (x, v) \<notin> Mapping.keys phis] = [x\<leftarrow>\<alpha>n g . (x, v) \<notin> Mapping.keys phis \<and> n \<noteq> x]")
      apply auto[1]
     apply (rule arg_cong2[where f=filter])
      apply auto[2]
    apply (cut_tac fold_union_elemI)
      apply auto[1]
     apply assumption
    apply (subgoal_tac "[x\<leftarrow>\<alpha>n g . x \<noteq> n \<and> (x, v) \<notin> Mapping.keys phis] = [x\<leftarrow>\<alpha>n g . (x, v) \<notin> Mapping.keys phis \<and> n \<noteq> x]")
     apply auto[1]
    apply (rule arg_cong2[where f=filter])
     apply auto[2]
    done
  next
    case (3 g v n phis m ms)
    note "3.prems"(2-4)[simp]
    from "3.prems"(1) have[simp]: "m \<in> set (\<alpha>n g)" by auto

    from 3 have IH1: "readArgs g v n phis ms = (phis'_aux g v (set ms) phis, map (\<lambda>m. lookupDef g m v) ms)"
    by auto

    have IH2: "phis'_aux g v {m} (phis'_aux g v (set ms) phis) = snd (readVariableRecursive g v m (phis'_aux g v (set ms) phis))"
    apply (rule "3.IH"(2))
          apply (auto simp: IH1 intro: phis'_aux_finite)[5]
     apply (simp add: phis'_aux_def keys_dom_lookup dom_def split: if_split_asm)
     apply safe
      apply (erule phiDefNodes_auxE)
       using "3.prems"(1,5)
       apply (auto simp: keys_dom_lookup)[3]
    using "3.prems"(6)
    apply (auto simp: phis'_aux_def split: if_split_asm)
    done

    have a: "phiDefNodes_aux g v [n\<leftarrow>\<alpha>n g . (n, v) \<notin> Mapping.keys (phis'_aux g v (set ms) phis)] m \<subseteq> phiDefNodes_aux g v [n\<leftarrow>\<alpha>n g . (n, v) \<notin> Mapping.keys phis] m"
    apply (rule phiDefNodes_aux_unvisited_monotonic)
    by (auto dest: phis'_aux_keys_super[THEN subsetD])

    {
      fix n
      assume m:  "n \<in> phiDefNodes_aux g v [n\<leftarrow>\<alpha>n g . (n, v) \<notin> Mapping.keys phis] m" and
             ms: "\<forall>x\<in>set ms. n \<notin> phiDefNodes_aux g v [n\<leftarrow>\<alpha>n g . (n, v) \<notin> Mapping.keys phis] x"

      have "n \<in> phiDefNodes_aux g v [n\<leftarrow>\<alpha>n g . (n, v) \<notin> Mapping.keys (phis'_aux g v (set ms) phis)] m"
      using m
      apply-
      apply (erule phiDefNodes_auxE, simp)
      apply (rule phiDefNodes_auxI)
         apply (auto simp: phis'_aux_def keys_dom_lookup split: if_split_asm)[3]
        apply (drule phiDefNodes_aux_redirect)
              using "3.prems"(1)
              apply auto[6]
        apply (rule ms[THEN ballE]; auto simp: keys_dom_lookup)
       apply auto
      done
    }
    note b = this

    show ?case
    unfolding readArgs.simps phis'_aux_def
    unfolding IH1
    apply (simp add: split_def Let_def IH2[symmetric])
    apply (subst phis'_aux_def)
    apply (subst(2) phis'_aux_def)
    apply (auto simp: Mapping_eq_lookup fst_readVariableRecursive split: prod.splits intro!: ext dest!: a[THEN subsetD] b)
    done
  qed (auto simp: readArgs.simps phis'_aux_def)

  definition "aux_1 g n = (\<lambda>v (uses,phis).
    let (use,phis') = readVariableRecursive g v n phis in
    (Mapping.update n (insert use (lookup_multimap uses n)) uses, phis')
  )"

  definition "aux_2 g n = foldr (aux_1 g n) (sorted_list_of_set (uses g n))"

  abbreviation "init_state \<equiv> (Mapping.empty, Mapping.empty)"
  abbreviation "from_sparse \<equiv> \<lambda>(n,v). (n,(v,n,PhiDef))"
  definition "uses'_phis' g = (
    let (u,p) = foldr (aux_2 g) (\<alpha>n g) init_state in
    (u, map_keys from_sparse p)
  )"

  lemma from_sparse_inj: "inj from_sparse"
    by (rule injI, auto)

  declare uses'_phis'_def[unfolded aux_2_def[abs_def] aux_1_def, code]

  lift_definition phis'_code :: "'g \<Rightarrow> ('node, ('node, 'var) ssaVal) phis_code" is phis' .

  lemma foldr_prod: "foldr (\<lambda>x y. (f1 x (fst y), f2 x (snd y))) xs y = (foldr f1 xs (fst y), foldr f2 xs (snd y))"
  by (induction xs, auto)

  lemma foldr_aux_1:
    assumes "set us \<subseteq> uses g n" "Mapping.lookup u n = None" "foldr (aux_1 g n) us (u,p) = (u',p')" (is "foldr ?f _ _ = _")
    assumes "finite (Mapping.keys p)" "\<And>n v. (n,v) \<in> Mapping.keys p \<Longrightarrow> length (predecessors g n) \<noteq> 1" "\<And>v. Mapping.lookup p (Entry g,v) \<in> {None, Some []}"
    shows "lookupDef g n ` set us = lookup_multimap u' n" "\<And>m. m \<noteq> n \<Longrightarrow> Mapping.lookup u' m = Mapping.lookup u m"
      "\<And>m v. (if m \<in> phiDefNodes_aux g v [n \<leftarrow> \<alpha>n g. (n,v) \<notin> Mapping.keys p] n \<and> v \<in> set us then
        Some (map (\<lambda>m. lookupDef g m v) (predecessors g m)) else
        (Mapping.lookup p (m,v))) = Mapping.lookup p' (m,v)"
  using assms proof (induction us arbitrary: u' p')
    case (Cons v us)
    let ?u = "fst (foldr ?f us (u,p))"
    let ?p = "snd (foldr ?f us (u,p))"
    {
      case 1
      have "n \<in> set (\<alpha>n g)" using 1(1) uses_in_\<alpha>n by auto
      hence "lookupDef g n v = fst (readVariableRecursive g v n ?p)"
        by (rule fst_readVariableRecursive[symmetric])
      moreover have "lookupDef g n ` set us = lookup_multimap ?u n"
        using 1 by - (rule Cons(1)[of ?u ?p], auto)
      ultimately show ?case
        using 1(3) by (auto simp: aux_1_def split_def Let_def lookup_multimap_def lookup_update split: option.splits)
    next
      case 2
      have "Mapping.lookup ?u m = Mapping.lookup u m"
        using 2 by - (rule Cons(2)[of _ ?u ?p], auto)
      thus ?case
        using 2 by (auto simp: aux_1_def split_def Let_def lookup_multimap_def lookup_update_neq split: option.splits)
    next
      case (3 m v' u' p')
      from 3(1) have[simp]: "\<And>v. v \<in> set us \<Longrightarrow> v \<in> vars g"
        by auto

      from 3 have IH: "\<And>m v'. (if m \<in> phiDefNodes_aux g v' [n \<leftarrow> \<alpha>n g. (n,v') \<notin> Mapping.keys p] n \<and> v' \<in> set us then
        Some (map (\<lambda>m. lookupDef g m v') (predecessors g m)) else
        (Mapping.lookup p (m,v'))) = Mapping.lookup ?p (m,v')"
        by - (rule Cons(3)[of ?u ?p], auto)

      have rVV: "phis'_aux g v {n} ?p = snd (readVariableRecursive g v n ?p)"
      apply (rule snd_readVariableRecursive(1))
         using 3
         apply (auto simp: uses_in_\<alpha>n)[2]
        apply (rule finite_subset[where B="set (\<alpha>n g) \<times> vars g \<union> Mapping.keys p"])
         apply (auto simp: keys_dom_lookup IH[symmetric] split: if_split_asm dest!: phiDefNodes_aux_in_unvisited[THEN subsetD])[1]
        apply (simp add: 3(4))[1]
       using 3(5-6)
       apply (auto simp: keys_dom_lookup dom_def IH[symmetric] split: if_split_asm dest!: phiDefNode_aux_is_join_node)
      done

      have a: "m \<in> phiDefNodes_aux g v [n\<leftarrow>\<alpha>n g . (n, v) \<notin> Mapping.keys ?p] n \<Longrightarrow> m \<in> phiDefNodes_aux g v [n\<leftarrow>\<alpha>n g . (n, v) \<notin> Mapping.keys p] n"
      apply (erule rev_subsetD)
      apply (rule phiDefNodes_aux_unvisited_monotonic)
      by (auto simp: IH[symmetric] keys_dom_lookup split: if_split_asm)

      have b: "v \<notin> set us \<Longrightarrow> [n\<leftarrow>\<alpha>n g . (n, v) \<notin> Mapping.keys ?p] = [n\<leftarrow>\<alpha>n g . (n, v) \<notin> Mapping.keys p]"
      by (rule arg_cong2[where f=filter], auto simp: keys_dom_lookup IH[symmetric])

      from 3 show ?case
      unfolding aux_1_def
      unfolding foldr.foldr_Cons
      unfolding aux_1_def[symmetric]
      by (auto simp: Let_def split_def IH[symmetric] rVV[symmetric] phis'_aux_def b dest: a uses_in_vars split: if_split_asm)
    }
  qed (auto simp: lookup_multimap_def)

  lemma foldr_aux_2:
    assumes "set ns \<subseteq> set (\<alpha>n g)" "distinct ns" "foldr (aux_2 g) ns init_state = (u',p')"
    shows "\<And>n. n \<in> set ns \<Longrightarrow> uses' g n = lookup_multimap u' n" "\<And>n. n \<notin> set ns \<Longrightarrow> Mapping.lookup u' n = None"
      "\<And>m v. (if \<exists>n \<in> set ns. m \<in> phiDefNodes_aux g v (\<alpha>n g) n \<and> v \<in> uses g n then
        Some (map (\<lambda>m. lookupDef g m v) (predecessors g m)) else
        None) = Mapping.lookup p' (m,v)"
  using assms proof (induction ns arbitrary: u' p')
    case (Cons n ns)
    let ?u = "fst (foldr (aux_2 g) ns init_state)"
    let ?p = "snd (foldr (aux_2 g) ns init_state)"

    fix m u' p'
    assume asm: "set (n#ns) \<subseteq> set (\<alpha>n g)" "distinct (n#ns)" "foldr (aux_2 g) (n#ns) init_state = (u', p')"
    hence IH:
      "\<And>n. n \<in> set ns \<Longrightarrow> uses' g n = lookup_multimap ?u n"
      "\<And>n. n \<notin> set ns \<Longrightarrow> Mapping.lookup ?u n = None"
      "\<And>m v. (if \<exists>n \<in> set ns. m \<in> phiDefNodes_aux g v (\<alpha>n g) n \<and> v \<in> uses g n then
        Some (map (\<lambda>m. lookupDef g m v) (predecessors g m)) else
        None) = Mapping.lookup ?p (m,v)"
    apply -
      apply (rule Cons.IH(1)[where p'2="?p"]; auto; fail)
     apply (rule Cons.IH(2)[where p'2="?p"]; auto; fail)
    by (rule Cons.IH(3)[where u'2="?u"], auto)

    with this[of n] asm(2) have a': "Mapping.lookup ?u n = None" by simp
    moreover have "finite (Mapping.keys ?p)"
      by (rule finite_subset[where B="set (\<alpha>n g) \<times> vars g"]) (auto simp: keys_dom_lookup IH[symmetric] split: if_split_asm dest!: phiDefNodes_aux_in_unvisited[THEN subsetD])
    moreover have "\<And>n v. (n,v) \<in> Mapping.keys ?p \<Longrightarrow> length (predecessors g n) \<noteq> 1"
      by (auto simp: keys_dom_lookup dom_def IH[symmetric] split: if_split_asm dest!: phiDefNode_aux_is_join_node)
    moreover have "\<And>v. Mapping.lookup ?p (Entry g,v) \<in> {None, Some []}"
      by (auto simp: IH[symmetric])
    ultimately have aux_2: "lookupDef g n ` uses g n = lookup_multimap u' n" "\<And>m. m \<noteq> n \<Longrightarrow> Mapping.lookup u' m = Mapping.lookup ?u m"
      "\<And>m v. (if m \<in> phiDefNodes_aux g v [n \<leftarrow> \<alpha>n g. (n,v) \<notin> Mapping.keys ?p] n \<and> v \<in> uses g n then
        Some (map (\<lambda>m. lookupDef g m v) (predecessors g m)) else
        (Mapping.lookup ?p (m,v))) = Mapping.lookup p' (m,v)"
    apply-
      apply (rule foldr_aux_1(1)[of "sorted_list_of_set (uses g n)" g n ?u ?p u' p', simplified]; simp add: aux_2_def[symmetric] asm(3)[simplified]; fail)
     apply (rule foldr_aux_1(2)[of "sorted_list_of_set (uses g n)" g n ?u ?p u' p', simplified]; simp add: aux_2_def[symmetric] asm(3)[simplified]; fail)
    apply (rule foldr_aux_1(3)[of "sorted_list_of_set (uses g n)" g n ?u ?p u' p', simplified]; simp add: aux_2_def[symmetric] asm(3)[simplified]; fail)
    done

    {
      assume 1: "m \<in> set (n#ns)"
      show "uses' g m = lookup_multimap u' m"
      apply (cases "m = n")
       apply (simp add: uses'_def aux_2)
      using 1 asm(2)
      apply (auto simp: IH(1) lookup_multimap_def aux_2(2))
      done
    next
      assume 2: "m \<notin> set (n#ns)"
      thus "Mapping.lookup u' m = None"
        by (simp add: aux_2(2) IH(2))
    next
      fix v
      show "(if \<exists>n \<in> set (n#ns). m \<in> phiDefNodes_aux g v (\<alpha>n g) n \<and> v \<in> uses g n then
        Some (map (\<lambda>m. lookupDef g m v) (predecessors g m)) else
        None) = Mapping.lookup p' (m,v)"
      apply (auto simp: aux_2(3)[symmetric] IH(3)[symmetric] keys_dom_lookup dom_def)
       apply (erule phiDefNodes_auxE)
        apply (erule uses_in_\<alpha>n)
       apply (rule phiDefNodes_auxI)
          apply auto[4]
       apply (drule phiDefNodes_aux_redirect; auto simp: uses_in_\<alpha>n; fail)
      apply (drule rev_subsetD)
       apply (rule phiDefNodes_aux_unvisited_monotonic)
       apply auto
      done
    }
  qed (auto simp: lookup_empty)

  lemma fst_uses'_phis': "uses' g = lookup_multimap (fst (uses'_phis' g))"
  apply (rule ext)
  apply (simp add: uses'_phis'_def Let_def split_def)
  apply (case_tac "x \<in> set (\<alpha>n g)")
   apply (rule foldr_aux_2(1)[OF _ _ surjective_pairing]; auto simp: lookup_empty intro: \<alpha>n_distinct; fail)
  unfolding lookup_multimap_def
  apply (subst foldr_aux_2(2)[OF _ _ surjective_pairing]; auto simp: lookup_empty uses_in_\<alpha>n uses'_def intro: \<alpha>n_distinct)
  done

  lemma fst_uses'_phis'_in_\<alpha>n: "Mapping.keys (fst (uses'_phis' g)) \<subseteq> set (\<alpha>n g)"
  apply (rule subsetI)
  apply (rule ccontr)
  apply (simp add: uses'_phis'_def Let_def split_def keys_dom_lookup dom_def)
  apply (subst(asm) foldr_aux_2(2)[OF _ _ surjective_pairing]; auto intro: \<alpha>n_distinct)
  done

  lemma snd_uses'_phis': "phis'_code g = snd (uses'_phis' g)"
  proof-
    have a: "\<And>n v. (THE k. (\<lambda>p. (fst p, snd p, fst p, PhiDef)) -` {(n, v, n, PhiDef)} = {k}) = (n,v)"
      by (rule the1_equality) (auto simp: vimage_def)
    show ?thesis
    apply (subst Mapping_eq_lookup)
    apply transfer
    apply (simp add: phis'_def uses'_phis'_def Let_def split_def)
    apply (auto simp: lookup_map_keys a intro!: ext)
    subgoal by (auto simp: vimage_def)[1]
    subgoal
      apply (subst foldr_aux_2(3)[OF _ _ surjective_pairing, symmetric])
      by (auto simp: phiDefNodes_def vimage_def elim!: fold_union_elem intro!: \<alpha>n_distinct split: if_split_asm)

    subgoal
      apply (subst(asm) foldr_aux_2(3)[OF _ _ surjective_pairing, symmetric])
      by (auto simp: phiDefNodes_def vimage_def elim!: fold_union_elem intro!: \<alpha>n_distinct split: if_split_asm)
        
    subgoal
      apply (subst(asm) foldr_aux_2(3)[OF _ _ surjective_pairing, symmetric])
      by (auto simp: phiDefNodes_def vimage_def elim!: fold_union_elem intro!: \<alpha>n_distinct fold_union_elemI split: if_split_asm)
    done
  qed
end

end
