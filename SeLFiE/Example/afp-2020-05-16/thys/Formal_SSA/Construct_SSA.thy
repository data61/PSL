(*  Title:      Construct_SSA.thy
    Author:     Sebastian Ullrich
*)

section \<open>SSA Construction\<close>
subsection \<open>CFG to SSA CFG\<close>

theory Construct_SSA imports SSA_CFG
  "HOL-Library.While_Combinator"
  "HOL-Library.Product_Lexorder"
begin

datatype Def = SimpleDef | PhiDef
type_synonym ('node, 'var) ssaVal = "'var \<times> 'node \<times> Def"

instantiation Def :: linorder
begin
  definition "x < y \<longleftrightarrow> x = SimpleDef \<and> y = PhiDef"
  definition "less_eq_Def (x :: Def) y \<longleftrightarrow> x = y \<or> x < y"
  instance by intro_classes (metis Def.distinct(1) less_Def_def less_eq_Def_def Def.exhaust)+
end

locale CFG_Construct = CFG \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses"
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set"
begin
  fun phiDefNodes_aux :: "'g \<Rightarrow> 'var \<Rightarrow> 'node list \<Rightarrow> 'node \<Rightarrow> 'node set" where
    "phiDefNodes_aux g v unvisited n =(
        if n \<notin> set unvisited \<or> v \<in> defs g n then {}
        else fold (\<union>)
          [phiDefNodes_aux g v (removeAll n unvisited) m . m \<leftarrow> predecessors g n]
          (if length (predecessors g n) \<noteq> 1 then {n} else {})
    )"

  definition phiDefNodes :: "'g \<Rightarrow> 'var \<Rightarrow> 'node set" where
    "phiDefNodes g v \<equiv> fold (\<union>)
      [phiDefNodes_aux g v (\<alpha>n g) n . n \<leftarrow> \<alpha>n g, v \<in> uses g n]
      {}"

  definition var :: "'g \<Rightarrow> ('node, 'var) ssaVal \<Rightarrow> 'var" where "var g \<equiv> fst"
  abbreviation defNode :: "('node, 'var) ssaVal \<Rightarrow> 'node" where "defNode v \<equiv> fst (snd v)"
  abbreviation defKind :: "('node, 'var) ssaVal \<Rightarrow> Def" where "defKind v \<equiv> snd (snd v)"

  declare var_def[simp]

  function lookupDef :: "'g \<Rightarrow> 'node \<Rightarrow> 'var \<Rightarrow> ('node, 'var) ssaVal" where
    "lookupDef g n v =(
        if n \<notin> set (\<alpha>n g) then undefined
        else if v \<in> defs g n then (v,n,SimpleDef)
        else case predecessors g n of
          [m] \<Rightarrow> lookupDef g m v
          | _ \<Rightarrow> (v,n,PhiDef)
    )"

  by auto
  termination by (relation "measure (\<lambda>(g,n,_). shortestPath g n)") (auto intro:shortestPath_predecessor)
  declare lookupDef.simps [code]

  definition defs' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node, 'var) ssaVal set" where
    "defs' g n \<equiv> (\<lambda>v. (v,n,SimpleDef)) ` defs g n"
  definition uses' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node, 'var) ssaVal set" where
    "uses' g n \<equiv> lookupDef g n ` uses g n"
  definition phis' :: "'g \<Rightarrow> ('node, ('node, 'var) ssaVal) phis" where
    "phis' \<equiv> \<lambda>g (n,(v,m,def)).
      if m = n \<and> n \<in> phiDefNodes g v \<and> v \<in> vars g \<and> def = PhiDef then
        Some [lookupDef g m v . m \<leftarrow> predecessors g n]
      else None"
  declare uses'_def [code] defs'_def [code] phis'_def [code]

  abbreviation "lookupDefNode g n v \<equiv> defNode (lookupDef g n v)"
  declare lookupDef.simps [simp del]
  declare phiDefNodes_aux.simps [simp del]

  lemma phiDefNodes_aux_cases:
    obtains (nonrec) "phiDefNodes_aux g v unvisited n = {}" "(n \<notin> set unvisited \<or> v \<in> defs g n)"
    | (rec) "phiDefNodes_aux g v unvisited n = fold union (map (phiDefNodes_aux g v (removeAll n unvisited)) (predecessors g n))
          (if length (predecessors g n) = 1 then {} else {n})"
       "n \<in> set unvisited" "v \<notin> defs g n"
  proof (cases "n \<in> set unvisited \<and> v \<notin> defs g n")
    case True
    thus ?thesis using rec by (simp add:phiDefNodes_aux.simps)
  next
    case False
    thus ?thesis using nonrec by (simp add:phiDefNodes_aux.simps)
  qed

  lemma phiDefNode_aux_is_join_node:
    assumes "n \<in> phiDefNodes_aux g v un m"
    shows "length (predecessors g n) \<noteq> 1"
  using assms proof (induction un arbitrary: m rule:removeAll_induct)
    case (1 un m)
    thus ?case
    proof (cases un v g m rule:phiDefNodes_aux_cases)
      case rec
      with 1 show ?thesis by (fastforce elim!:fold_union_elem split:if_split_asm)
    qed auto
  qed

  lemma phiDefNode_is_join_node:
    assumes "n \<in> phiDefNodes g v"
    shows "length (predecessors g n) \<noteq> 1"
  using assms unfolding phiDefNodes_def
  by (auto elim!:fold_union_elem dest!:phiDefNode_aux_is_join_node)

  abbreviation unvisitedPath :: "'node list \<Rightarrow> 'node list \<Rightarrow> bool" where
    "unvisitedPath un ns \<equiv> distinct ns \<and> set ns \<subseteq> set un"

  lemma unvisitedPath_removeLast:
    assumes "unvisitedPath un ns" "length ns \<ge> 2"
    shows "unvisitedPath (removeAll (last ns) un) (butlast ns)"
  proof-
    let ?n = "last ns"
    let ?ns' = "butlast ns"
    let ?un' = "removeAll ?n un"
    let ?n' = "last ?ns'"
    from assms(2) have [simp]: "?n = ns ! (length ns - 1)" by -(rule last_conv_nth, auto)
    from assms(1) have "distinct ?ns'" by -(rule distinct_butlast, simp)
    moreover
    have "set ?ns' \<subseteq> set ?un'"
    proof
      fix n
      assume assm: "n \<in> set ?ns'"
      then obtain i where "n = ?ns' ! i" "i < length ?ns'" by (auto simp add:in_set_conv_nth)
      hence i: "n = ns ! i" "i < length ns - 1" by (auto simp add:nth_butlast)
      with assms have 1: "n \<noteq> ?n" by (auto iff:nth_eq_iff_index_eq)
      from i assms(1) have "n \<in> set un" by auto
      with \<open>n \<in> set ?ns'\<close> assms(1) 1 show "n \<in> set ?un'" by auto
    qed
    ultimately show ?thesis by simp
  qed

  lemma phiDefNodes_auxI:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "unvisitedPath un ns" "\<forall>n \<in> set ns. v \<notin> defs g n" "length (predecessors g n) \<noteq> 1"
    shows "n \<in> phiDefNodes_aux g v un m"
  using assms(1,2,3) proof (induction un arbitrary: m ns rule:removeAll_induct)
    case (1 un)
    show ?case
    proof (cases un v g m rule:phiDefNodes_aux_cases)
      case nonrec
      from "1.prems"(1) have "m \<in> set ns" unfolding path2_def by auto
      with nonrec show ?thesis using "1.prems"(2,3) by auto
    next
      case rec
      show ?thesis
      proof (cases "n = m")
        case True
        thus ?thesis using rec assms(4) by -(subst rec(1), rule fold_union_elemI[of _ "{m}"], auto)
      next
        case False
        let ?ns' = "butlast ns"
        let ?m' = "last ?ns'"
        from "1.prems"(1) have [simp]: "m = last ns" unfolding path2_def by simp
        with 1(2) False have ns': "g \<turnstile> n-?ns'\<rightarrow>?m'" "?m' \<in> set (predecessors g m)" by (auto intro: path2_unsnoc)

        have "n \<in> phiDefNodes_aux g v (removeAll m un) ?m'"
        using rec(2) ns'
        apply-
        proof (rule "1.IH")
          from "1.prems"(1) False have "length ns \<ge> 2" by (auto simp del:\<open>m = last ns\<close>)
          with "1.prems"(2) show "unvisitedPath (removeAll m un) ?ns'" by (subst \<open>m = last ns\<close>, rule unvisitedPath_removeLast)
          from "1.prems"(3) show "\<forall>n \<in> set ?ns'. v \<notin> defs g n" by (auto intro:in_set_butlastD)
        qed
        with ns'(2) show ?thesis by -(subst rec, rule fold_union_elemI, auto)
      qed
    qed
  qed

  lemma phiDefNodes_auxE:
    assumes "n \<in> phiDefNodes_aux g v un m" "m \<in> set (\<alpha>n g)"
    obtains ns where "g \<turnstile> n-ns\<rightarrow>m" "\<forall>n \<in> set ns. v \<notin> defs g n" "length (predecessors g n) \<noteq> 1" "unvisitedPath un ns"
  using assms proof (atomize_elim, induction un arbitrary:m rule:removeAll_induct)
    case (1 un)
    show ?case
    proof (cases un v g m rule:phiDefNodes_aux_cases)
      case nonrec
      thus ?thesis using "1.prems" by simp
    next
      case rec
      show ?thesis
      proof (cases "n \<in> (if length (predecessors g m) = 1 then {} else {m})")
        case True
        hence "n = m" by (simp split:if_split_asm)
        thus ?thesis using "1.prems"(2) rec True by auto
      next
        case False
        with rec "1.prems"(1) obtain m' where m': "n \<in> phiDefNodes_aux g v (removeAll m un) m'" "m' \<in> set (predecessors g m)"
          by (auto elim!:fold_union_elem)
        with "1.prems"(2) have "m' \<in> set (\<alpha>n g)" by auto
        with "1.IH"[of m m'] m' rec obtain ns where "g \<turnstile> n-ns\<rightarrow>m'" "\<forall>n \<in> set ns. v \<notin> defs g n" "length (predecessors g n) \<noteq> 1" "unvisitedPath (removeAll m un) ns" by auto
        thus ?thesis using m' rec by -(rule exI, auto)
      qed
    qed
  qed

  lemma phiDefNodesE:
    assumes "n \<in> phiDefNodes g v"
    obtains ns m where "g \<turnstile> n-ns\<rightarrow>m" "\<forall>n \<in> set ns. v \<notin> defs g n" "v \<in> uses g m"
  using assms
  by (auto elim!:phiDefNodes_auxE elim!:fold_union_elem simp:phiDefNodes_def)

  lemma phiDefNodes_\<alpha>n[simp]: "n \<in> phiDefNodes g v \<Longrightarrow> n \<in> set (\<alpha>n g)"
  by (erule phiDefNodesE, auto)

  lemma phiDefNodesI:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "v \<in> uses g m" "\<forall>n \<in> set ns. v \<notin> defs g n" "length (predecessors g n) \<noteq> 1"
    shows "n \<in> phiDefNodes g v"
  proof-
    from assms(1) have "m \<in> set (\<alpha>n g)" by (rule path2_in_\<alpha>n, auto)
    from assms obtain ns' where "g \<turnstile> n-ns'\<rightarrow>m" "distinct ns'" "\<forall>n \<in> set ns'. v \<notin> defs g n" by -(rule simple_path2, auto)
    with assms(4) have 1: "n \<in> phiDefNodes_aux g v (\<alpha>n g) m" by -(rule phiDefNodes_auxI, auto intro:path2_in_\<alpha>n)
    thus ?thesis using assms(2) \<open>m \<in> set (\<alpha>n g)\<close>
    unfolding phiDefNodes_def
    by -(rule fold_union_elemI, auto)
  qed

  lemma lookupDef_cases[consumes 1]:
    assumes "n \<in> set (\<alpha>n g)"
    obtains (SimpleDef) "v \<in> defs g n" "lookupDef g n v = (v,n,SimpleDef)"
          | (PhiDef)    "v \<notin> defs g n" "length (predecessors g n) \<noteq> 1" "lookupDef g n v = (v,n,PhiDef)"
          | (rec) m where "v \<notin> defs g n" "predecessors g n = [m]" "m \<in> set (\<alpha>n g)" "lookupDef g n v = lookupDef g m v"
  proof (cases "v \<in> defs g n")
    case True
    thus thesis using assms SimpleDef by (simp add:lookupDef.simps)
  next
    case False
    thus thesis
    proof (cases "length (predecessors g n) = 1")
      case True
      then obtain m where m: "predecessors g n = [m]" by (cases "predecessors g n", auto)
      hence "m \<in> set (predecessors g n)" by simp
      thus thesis using False rec assms m by -(subst(asm) lookupDef.simps, drule predecessor_is_node, auto)
    next
      case False
      thus thesis using \<open>v \<notin> defs g n\<close> assms by -(rule PhiDef, assumption, assumption, subst lookupDef.simps, auto split:list.split)
    qed
  qed

  lemma lookupDef_cases'[consumes 1]:
    assumes "n \<in> set (\<alpha>n g)"
    obtains (SimpleDef) "v \<in> defs g n" "defNode (lookupDef g n v) = n" "defKind (lookupDef g n v) = SimpleDef"
          | (PhiDef)    "v \<notin> defs g n" "length (predecessors g n) \<noteq> 1" "lookupDefNode g n v = n" "defKind (lookupDef g n v) = PhiDef"
          | (rec) m where "v \<notin> defs g n" "predecessors g n = [m]" "m \<in> set (\<alpha>n g)" "lookupDef g n v = lookupDef g m v"
  using assms
  by (rule lookupDef_cases[of n g v]) simp_all

  lemma lookupDefE:
    assumes "lookupDef g n v = v'" "n \<in> set (\<alpha>n g)"
    obtains (SimpleDef) "v \<in> defs g n" "v' = (v,n,SimpleDef)"
          | (PhiDef)    "v \<notin> defs g n" "length (predecessors g n) \<noteq> 1" "v' = (v,n,PhiDef)"
          | (rec) m where "v \<notin> defs g n" "predecessors g n = [m]" "m \<in> set (\<alpha>n g)" "v' = lookupDef g m v"
  using assms by -(atomize_elim, cases rule:lookupDef_cases[of n g v], auto)

  lemma lookupDef_induct[consumes 1, case_names SimpleDef PhiDef rec]:
    assumes "n \<in> set (\<alpha>n g)"
            "\<And>n. \<lbrakk>n \<in> set (\<alpha>n g); v \<in> defs g n; lookupDef g n v = (v,n,SimpleDef)\<rbrakk> \<Longrightarrow> P n"
            "\<And>n. \<lbrakk>n \<in> set (\<alpha>n g); v \<notin> defs g n; length (predecessors g n) \<noteq> 1; lookupDef g n v = (v,n,PhiDef)\<rbrakk> \<Longrightarrow> P n"
            "\<And>n m. \<lbrakk>v \<notin> defs g n; predecessors g n = [m]; m \<in> set (\<alpha>n g); lookupDef g n v = lookupDef g m v; P m\<rbrakk> \<Longrightarrow> P n"
    shows "P n"
  apply (induct rule:lookupDef.induct[where P = "\<lambda>g' n v'. g'=g \<and> v'=v \<and> n \<in> set (\<alpha>n g) \<longrightarrow> P n", of g v n, simplified (no_asm), THEN mp])
   apply clarsimp
   apply (rule_tac v=v and n=n in lookupDef_cases; auto intro: assms lookupDef_cases)
  by (rule assms(1))

  lemma lookupDef_induct'[consumes 2, case_names SimpleDef PhiDef rec]:
    assumes "n \<in> set (\<alpha>n g)" "lookupDef g n v = (v,n',def)"
            "\<lbrakk>v \<in> defs g n'; def = SimpleDef\<rbrakk> \<Longrightarrow> P n'"
            "\<lbrakk>v \<notin> defs g n'; length (predecessors g n') \<noteq> 1; def = PhiDef\<rbrakk> \<Longrightarrow> P n'"
            "\<And>n m. \<lbrakk>v \<notin> defs g n; predecessors g n = [m]; m \<in> set (\<alpha>n g); lookupDef g n v = lookupDef g m v; P m\<rbrakk> \<Longrightarrow> P n"
    shows "P n"
    using assms(1,2)
    proof (induction rule:lookupDef_induct[where v=v])
      case (SimpleDef n)
      with assms(2) have "n = n'" "def = SimpleDef" by auto
      with SimpleDef assms(3) show ?case by simp
    next
      case (PhiDef n)
      with assms(2) have "n = n'" "def = PhiDef" by auto
      with PhiDef assms(4) show ?case by simp
    qed (rule assms(5), simp_all)

  lemma lookupDef_looksup[simp]:
    assumes "lookupDef g n v = (v',n',def)" "n \<in> set (\<alpha>n g)"
    shows "v' = v"
  using assms(1) assms(2) by (induction rule:lookupDef.induct) (auto elim:lookupDefE)

  lemma lookupDef_looksup':
    assumes "(v',n',def) = lookupDef g n v" "n \<in> set (\<alpha>n g)"
    shows "v' = v"
  using assms(1)[symmetric] assms(2) by (rule lookupDef_looksup)

  lemma lookupDef_looksup'':
    assumes "n \<in> set (\<alpha>n g)"
    obtains n' "def" where "lookupDef g n v = (v,n',def)"
  apply atomize_elim
  using assms by (induction rule:lookupDef.induct) (cases rule:lookupDef_cases, auto)

  lemma lookupDef_fst[simp]: "n \<in> set (\<alpha>n g) \<Longrightarrow> fst (lookupDef g n v) = v"
  by (metis fst_conv lookupDef_looksup'')

  lemma lookupDef_to_\<alpha>n:
    assumes "lookupDef g n v = (v',n',def)" "n \<in> set (\<alpha>n g)"
    shows "n' \<in> set (\<alpha>n g)"
  using assms(2,1)
  by (induction rule:lookupDef_induct[of n g v]) simp_all

  lemma lookupDef_to_\<alpha>n'[simp]:
    assumes "lookupDef g n v = val" "n \<in> set (\<alpha>n g)"
    shows "defNode val \<in> set (\<alpha>n g)"
  using assms by (cases val) (auto simp:lookupDef_to_\<alpha>n)

  lemma lookupDef_induct''[consumes 2, case_names SimpleDef PhiDef rec]:
    assumes "lookupDef g n v = val" "n \<in> set (\<alpha>n g)"
            "\<lbrakk>v \<in> defs g (defNode val); defKind val = SimpleDef\<rbrakk> \<Longrightarrow> P (defNode val)"
            "\<lbrakk>v \<notin> defs g (defNode val); length (predecessors g (defNode val)) \<noteq> 1; defKind val = PhiDef\<rbrakk> \<Longrightarrow> P (defNode val)"
            "\<And>n m. \<lbrakk>v \<notin> defs g n; predecessors g n = [m]; m \<in> set (\<alpha>n g); lookupDef g n v = lookupDef g m v; P m\<rbrakk> \<Longrightarrow> P n"
    shows "P n"
  using assms
  apply (cases val)
  apply (simp)
  apply (erule lookupDef_induct')
  using assms(2) by auto

  lemma defs'_finite: "finite (defs' g n)"
  unfolding defs'_def using defs_finite
  by simp

  lemma uses'_finite: "finite (uses' g n)"
  unfolding uses'_def using uses_finite
  by simp

  lemma defs'_uses'_disjoint: "n \<in> set (\<alpha>n g) \<Longrightarrow> defs' g n \<inter> uses' g n = {}"
  unfolding defs'_def uses'_def using defs_uses_disjoint
  by (auto dest:lookupDef_looksup')

  lemma allDefs'_disjoint: " n \<in> set (\<alpha>n g) \<Longrightarrow> m \<in> set (\<alpha>n g) \<Longrightarrow> n \<noteq> m
    \<Longrightarrow> (defs' g n \<union> {v. (n, v) \<in> dom (phis' g)}) \<inter> (defs' g m \<union> {v. (m, v) \<in> dom (phis' g)}) = {}"
  by (auto split:if_split_asm simp: defs'_def phis'_def)

  lemma phiDefNodes_aux_finite: "finite (phiDefNodes_aux g v un m)"
  proof (induction un arbitrary:m rule:removeAll_induct)
    case (1 un)
    thus ?case by (cases un v g m rule:phiDefNodes_aux_cases) auto
  qed

  lemma phis'_finite: "finite (dom (phis' g))"
  proof-
    let ?super = "set (\<alpha>n g) \<times> vars g \<times> set (\<alpha>n g) \<times> {PhiDef}"
    have "finite ?super" by auto
    thus ?thesis
    by - (rule finite_subset[of _ ?super], auto simp:phis'_def split:if_split_asm)
  qed

  lemma phis'_wf: "phis' g (n, v) = Some args \<Longrightarrow> length (predecessors g n) = length args"
  unfolding phis'_def predecessors_def by (auto split:prod.splits if_split_asm)

  lemma simpleDefs_phiDefs_disjoint: "n \<in> set (\<alpha>n g) \<Longrightarrow> defs' g n \<inter> {v. (n, v) \<in> dom (phis' g)} = {}"
  unfolding phis'_def defs'_def by auto

  lemma oldDefs_correct: "defs g n = var g ` defs' g n"
  by (simp add:defs'_def image_image)

  lemma oldUses_correct: "n \<in> set (\<alpha>n g) \<Longrightarrow> uses g n = var g ` uses' g n"
  by (simp add:uses'_def image_image)

  lemmas base_SSA_defs = CFG_SSA_base.CFG_SSA_defs

  sublocale braun_ssa: CFG_SSA \<alpha>e \<alpha>n invar inEdges' Entry defs' uses' phis'
  apply unfold_locales
           apply (rule defs'_uses'_disjoint, simp_all)
          apply (rule defs'_finite)
         apply (auto simp add: uses'_def uses_in_\<alpha>n)[1]
        apply (rule uses'_finite)
       apply (rule invar)
      apply (rule phis'_finite)
     apply (auto simp: phis'_def split: if_split_asm)[1]
    apply (rule phis'_wf, simp_all add: base_SSA_defs)
   apply (erule simpleDefs_phiDefs_disjoint)
  apply (erule allDefs'_disjoint, simp, simp)
  done
end

declare (in CFG) invar[rule del]
declare (in CFG) Entry_no_predecessor[simp del]
context CFG_Construct
begin
  declare invar[intro!]
  declare Entry_no_predecessor[simp]

  lemma no_disjoint_cycle[simp]:
    assumes "g \<turnstile> n-ns\<rightarrow>n" "distinct ns"
    shows "ns = [n]"
  using assms unfolding path2_def
  by (metis distinct.simps(2) hd_Cons_tl last_in_set last_tl path_not_Nil)

  lemma lookupDef_path:
    assumes "m \<in> set (\<alpha>n g)"
    obtains ns where  "g \<turnstile> lookupDefNode g m v-ns\<rightarrow>m" "(\<forall>x \<in> set (tl ns). v \<notin> defs g x)"
  apply atomize_elim
  using assms proof (induction rule:lookupDef_induct[of m g v])
    case (SimpleDef n)
    thus ?case by -(rule exI[of _ "[n]"], auto)
  next
    case (PhiDef n)
    thus ?case by -(rule exI[of _ "[n]"], auto)
  next
    case (rec m m')
    then obtain ns where "g \<turnstile> lookupDefNode g m v-ns\<rightarrow>m'" "\<forall>x \<in> set (tl ns). v \<notin> defs g x" by auto
    with rec.hyps(1,2) show ?case by - (rule exI[of _ "ns@[m]"], auto simp: path2_not_Nil)
  qed

  lemma lookupDef_path_conventional:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "n = lookupDefNode g m v" "n \<notin> set (tl ns)" "x \<in> set (tl ns)" "v' \<in> braun_ssa.allDefs g x"
    shows "var g v' \<noteq> v"
  using assms(1-4) proof (induction rule:path2_rev_induct)
    case empty
    from empty.prems(3) have False by simp
    thus ?case ..
  next
    case (snoc ns m m')
    note snoc.prems(1)[simp]
    from snoc.hyps have p: "g \<turnstile> n-ns@[m']\<rightarrow>m'" by auto
    hence "m' \<in> set (\<alpha>n g)" by auto
    thus ?thesis
    proof (cases rule:lookupDef_cases'[of m' g v])
      case SimpleDef
      with snoc.prems(2,3) have False by (simp add:tl_append split:list.split_asm)
      thus ?thesis ..
    next
      case PhiDef
      with snoc.prems(2,3) have False by (simp add:tl_append split:list.split_asm)
      thus ?thesis ..
    next
      case (rec m\<^sub>2)
      from this(2) snoc.hyps(2) have[simp]: "m\<^sub>2 = m" by simp
      show ?thesis
      proof (cases "x \<in> set (tl ns)")
        case True
        with rec(4) snoc.prems(2) show ?thesis by - (rule snoc.IH, simp_all add:tl_append split:list.split_asm)
      next
        case False
        with snoc.prems(3) have[simp]: "x = m'" by (simp add:tl_append split:list.split_asm)

        show ?thesis
        proof (cases "v' \<in> defs' g x")
          case True
          with rec(1) show ?thesis by (auto simp add:defs'_def)
        next
          case False
          with assms(5) have "v' \<in> braun_ssa.phiDefs g m'" by (simp add:braun_ssa.allDefs_def)
          hence "m' \<in> phiDefNodes g (fst v')"
            unfolding braun_ssa.phiDefs_def by (auto simp add: phis'_def split:prod.split_asm if_split_asm)
          with rec(2) show ?thesis by (auto dest:phiDefNode_is_join_node)
        qed
      qed
    qed
  qed

  lemma allUse_lookupDef:
    assumes "v \<in> braun_ssa.allUses g m" "m \<in> set (\<alpha>n g)"
    shows "lookupDef g m (var g v) = v"
  proof (cases "v \<in> uses' g m")
    case True
    then obtain v' where v': "v = lookupDef g m v'" "v' \<in> uses g m" by (auto simp add:uses'_def)
    with assms(2) have "var g v = v'" unfolding var_def by (metis lookupDef_fst)
    with v' show ?thesis by simp
  next
    case False
    with assms(1) obtain  m' v' vs where "(m,v) \<in> set (zip (predecessors g m') vs)" "phis' g (m', v') = Some vs"
      by (auto simp add:braun_ssa.allUses_def elim:braun_ssa.phiUsesE)
    hence l: "v = lookupDef g m (var g v')" by (auto simp add:phis'_def split:prod.split_asm if_split_asm elim:in_set_zip_map)
    with assms(2) have "var g v = var g v'" unfolding var_def by (metis lookupDef_fst)
    with l show ?thesis by simp
  qed

  lemma phis'_fst:
    assumes "phis' g (n,v) = Some vs" "v' \<in> set vs"
    shows "var g v' = var g v"
  using assms by (auto intro!:lookupDef_fst dest!:phiDefNodes_\<alpha>n simp add:phis'_def split:prod.split_asm if_split_asm)

  lemma allUse_simpleUse:
    assumes "v \<in> braun_ssa.allUses g m" "m \<in> set (\<alpha>n g)"
    obtains ms m' where "g \<turnstile> m-ms\<rightarrow>m'" "var g v \<in> uses g m'" "\<forall>x \<in> set (tl ms). var g v \<notin> defs g x"
  proof (cases "v \<in> uses' g m")
    case True
    then obtain v' where v': "v = lookupDef g m v'" "v' \<in> uses g m" by (auto simp add:uses'_def)
    with assms(2) have "var g v = v'" unfolding var_def by (metis lookupDef_fst)
    with v' assms(2) show ?thesis by - (rule that, auto)
  next
    case False
    with assms(1) obtain  m' v' vs where phi: "(m,v) \<in> set (zip (predecessors g m') vs)" "phis' g (m', v') = Some vs"
      by (auto simp add:braun_ssa.allUses_def elim:braun_ssa.phiUsesE)
    hence m': "m' \<in> phiDefNodes g (var g v')" by (auto simp add:phis'_def split:prod.split_asm if_split_asm)
    from phi have[simp]: "var g v = var g v'" by - (rule phis'_fst, auto)
    from m' obtain m'' ms where "g \<turnstile> m'-ms\<rightarrow>m''" "\<forall>x \<in> set ms. var g v' \<notin> defs g x" "var g v' \<in> uses g m''" by (erule phiDefNodesE)
    with phi(1) show ?thesis by - (rule that[of "m#ms" m''], auto simp del:var_def)
  qed

  lemma defs': "v \<in> defs' g n \<longleftrightarrow> var g v \<in> defs g n \<and> defKind v = SimpleDef \<and> defNode v = n"
  by (cases v, auto simp add:defs'_def)

  lemma use_implies_allDef:
    assumes "lookupDef g m (var g v) = v"  "m \<in> set (\<alpha>n g)" "var g v \<in> uses g m'" "g \<turnstile> m-ms\<rightarrow>m'" "\<forall>x \<in> set (tl ms). var g v \<notin> defs g x"
    shows "v \<in> braun_ssa.allDefs g (defNode v)"
  using assms proof (induction arbitrary:ms rule:lookupDef_induct'')
      case SimpleDef
      hence "v \<in> defs' g (defNode v)" by (simp add:defs')
      thus ?case by (simp add:braun_ssa.allDefs_def)
    next
      case PhiDef
      from PhiDef.prems(1,2) have vars: "var g v \<in> vars g" by auto
      from PhiDef.hyps(1) PhiDef.prems(2,3) have "\<forall>n\<in>set ms. var g v \<notin> defs g n" by (metis hd_Cons_tl path2_def path2_not_Nil set_ConsD)
      with PhiDef have "defNode v \<in> phiDefNodes g (var g v)" by - (rule phiDefNodesI)
      with PhiDef.hyps(3) vars have "v \<in> braun_ssa.phiDefs g (defNode v)" unfolding braun_ssa.phiDefs_def by (auto simp add: phis'_def split:prod.split)
      thus ?case by (simp add:braun_ssa.allDefs_def)
    next
      case (rec n m)
      from rec.hyps(1) rec.prems(2,3) have "\<forall>n\<in>set ms. var g v \<notin> defs g n" by (metis hd_Cons_tl path2_def path2_not_Nil set_ConsD)
      with rec show ?case by - (rule rec.IH[of "m#ms"], auto)
    qed

  lemma allUse_defNode_in_\<alpha>n[simp]:
    assumes "v \<in> braun_ssa.allUses g m" "m \<in> set (\<alpha>n g)"
    shows "defNode v \<in> set (\<alpha>n g)"
  proof-
    let ?n = "defNode (lookupDef g m (var g v))"
    from assms(1,2) have l: "lookupDef g m (var g v) = v" by (rule allUse_lookupDef)
    from assms obtain ns where ns: "g \<turnstile> ?n-ns\<rightarrow>m" by - (rule lookupDef_path, auto)
    with l show ?thesis by auto
  qed

  lemma allUse_implies_allDef:
    assumes "v \<in> braun_ssa.allUses g m" "m \<in> set (\<alpha>n g)"
    shows "v \<in> braun_ssa.allDefs g (defNode v)"
  proof-
    let ?n = "defNode (lookupDef g m (var g v))"
    from assms(1,2) have l: "lookupDef g m (var g v) = v" by (rule allUse_lookupDef)
    from assms obtain ns where ns: "g \<turnstile> ?n-ns\<rightarrow>m" "\<forall>x \<in> set (tl ns). var g v \<notin> defs g x" by - (rule lookupDef_path, auto)
    from assms obtain ms m' where "g \<turnstile> m-ms\<rightarrow>m'" "var g v \<in> uses g m'" "\<forall>x \<in> set (tl ms). var g v \<notin> defs g x" by - (rule allUse_simpleUse)
    hence "v \<in> braun_ssa.allDefs g (defNode v)" using ns assms(2) l by - (rule use_implies_allDef, auto)
    with assms(2) l show ?thesis by simp
  qed

  lemma conventional:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "n \<notin> set (tl ns)" "v \<in> braun_ssa.allDefs g n" "v \<in> braun_ssa.allUses g m"
      "x \<in> set (tl ns)" "v' \<in> braun_ssa.allDefs g x"
    shows "var g v' \<noteq> var g v"
  proof-
    from assms(1) have[simp]: "m \<in> set (\<alpha>n g)" by auto
    from assms(4) have[simp]: "lookupDef g m (var g v) = v" by - (rule allUse_lookupDef, auto)

    from assms(1,4) have "v \<in> braun_ssa.allDefs g (defNode v)" by - (rule allUse_implies_allDef, auto)
    with assms(1,3,4) braun_ssa.allDefs_disjoint[of n g "defNode v"] have[simp]: "defNode v = n" by - (rule braun_ssa.allDefs_disjoint', auto)

    from assms show ?thesis by - (rule lookupDef_path_conventional[where m=m], simp_all add:uses'_def del:var_def)
  qed

  lemma allDefs_var_disjoint_aux: "n \<in> set (\<alpha>n g) \<Longrightarrow> v \<in> defs g n \<Longrightarrow> n \<notin> phiDefNodes g v"
    by (auto elim!:phiDefNodesE dest:path2_hd_in_ns)

  lemma allDefs_var_disjoint: "\<lbrakk>n \<in> set (\<alpha>n g); v \<in> braun_ssa.allDefs g n; v' \<in> braun_ssa.allDefs g n; v \<noteq> v'\<rbrakk> \<Longrightarrow> var g v' \<noteq> var g v"
    unfolding braun_ssa.allDefs_def braun_ssa.phiDefs_def
    by (auto simp: defs'_def phis'_def allDefs_var_disjoint_aux split:prod.splits if_split_asm)

  lemma[simp]: "n \<in> set (\<alpha>n g) \<Longrightarrow> v \<in> defs g n \<Longrightarrow> lookupDefNode g n v = n"
  by (cases rule:lookupDef_cases[of n g v]) simp_all

  lemma[simp]: "n \<in> set (\<alpha>n g) \<Longrightarrow> length (predecessors g n) \<noteq> 1 \<Longrightarrow> lookupDefNode g n v = n"
  by (cases rule:lookupDef_cases[of n g v]) simp_all

  lemma lookupDef_idem[simp]:
    assumes "n \<in> set (\<alpha>n g)"
    shows "lookupDef g (lookupDefNode g n v) v = lookupDef g n v"
  using assms by (induction rule:lookupDef_induct''[of g n v, OF refl]) (simp_all add:assms)
end

locale CFG_Construct_wf = CFG_Construct \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" + CFG_wf \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses"
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set"
begin
  lemma def_ass_allUses_aux:
    assumes "g \<turnstile> Entry g-ns\<rightarrow>n"
    shows "lookupDefNode g n (var g v) \<in> set ns"
  proof-
    from assms have[simp]: "n \<in> set (\<alpha>n g)" by auto
    thus ?thesis using assms
    proof (induction arbitrary:ns rule:lookupDef_induct''[of g n "var g v", OF refl, consumes 1])
      case (3 m m' ns)
      show ?case
      proof (cases "length ns \<ge> 2")
        case False
        with "3.prems" have "m = Entry g" by (metis path2_nontrivial)
        with "3.hyps"(2) have False by simp
        thus ?thesis ..
      next
        case True
        with "3.prems" have "g \<turnstile> Entry g-butlast ns\<rightarrow>m'"
        by (rule path2_unsnoc) (simp add:"3.hyps"(2))
        with "3.hyps" "3.IH"[of "butlast ns"] show ?thesis by (simp add:in_set_butlastD)
      qed
    qed auto
  qed

  lemma def_ass_allUses:
    assumes "v \<in> braun_ssa.allUses g n" "n \<in> set (\<alpha>n g)"
    shows "braun_ssa.defAss g n v"
  proof (rule braun_ssa.defAssI)
    fix ns
    assume asm: "g \<turnstile> Entry g-ns\<rightarrow>n"
    let ?m = "lookupDefNode g n (var g v)"
    from asm have "?m \<in> set ns" by (rule def_ass_allUses_aux)
    moreover from assms allUse_lookupDef have "?m = defNode v" by simp
    moreover from assms allUse_implies_allDef have "v \<in> braun_ssa.allDefs g (defNode v)" by simp
    ultimately show "\<exists>n\<in>set ns. v \<in> braun_ssa.allDefs g n" by auto
  qed

  lemma Empty_no_phis:
    shows "phis' g (Entry g, v) = None"
  proof-
    have "\<And>v. Entry g \<notin> phiDefNodes g v"
    proof (rule, rule phiDefNodesE, assumption)
      fix v ns m
      assume asm: "g \<turnstile> Entry g-ns\<rightarrow>m" "\<forall>n\<in>set ns. v \<notin> defs g n" "v \<in> uses g m"
      hence "m \<in> set (\<alpha>n g)" by auto
      from def_ass_uses[of g, THEN bspec[OF _ this], THEN bspec[OF _ asm(3)]] asm
      show False by (auto elim!:defAss'E)
    qed
    thus ?thesis by (auto simp:phis'_def split:prod.split)
  qed

  lemma braun_ssa_CFG_SSA_wf:
    "CFG_SSA_wf \<alpha>e \<alpha>n invar inEdges' Entry defs' uses' phis'"
  apply unfold_locales
   apply (erule def_ass_allUses, assumption)
  apply (rule Empty_no_phis)
  done

  sublocale braun_ssa: CFG_SSA_wf \<alpha>e \<alpha>n invar inEdges' Entry defs' uses' phis'
  by (rule braun_ssa_CFG_SSA_wf)

  lemma braun_ssa_CFG_SSA_Transformed:
    "CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges' Entry defs uses defs' uses' phis' var"
  apply unfold_locales
      apply (rule oldDefs_correct)
     apply (erule oldUses_correct)
    apply (erule conventional, simp, simp, simp, simp, simp)
   apply (erule phis'_fst, simp)
  apply (erule allDefs_var_disjoint, simp, simp, simp)
  done

  sublocale braun_ssa: CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" defs' uses' phis' var
  by (rule braun_ssa_CFG_SSA_Transformed)

  lemma PhiDef_defNode_eq:
    assumes "n \<in> set (\<alpha>n g)" "n \<in> phiDefNodes g v" "v \<in> vars g"
    shows "braun_ssa.defNode g (v,n,PhiDef) = n"
  using assms by - (rule braun_ssa.defNode_eq, rule assms(1), subst braun_ssa.allDefs_def, subst braun_ssa.phiDefs_def, auto simp: phis'_def)

  lemma phiDefNodes_aux_pruned_aux:
    assumes "n \<in> phiDefNodes_aux g v (\<alpha>n g) nUse" "v \<in> uses g nUse" "g \<turnstile> n-ns\<rightarrow>m" "g \<turnstile>m-ms\<rightarrow>nUse" "braun_ssa.liveVal g (lookupDef g m v)" "\<forall>n \<in> set (ns@ms). v \<notin> defs g n"
    shows "braun_ssa.liveVal g (v,n,PhiDef)"
  using assms(3-) proof (induction n ns m arbitrary:ms rule:path2_rev_induct)
    case empty
    with assms(1) have "lookupDef g n v = (v,n,PhiDef)"
      by -(drule phiDefNode_aux_is_join_node, cases rule:lookupDef_cases, auto)
    with empty.prems(2) show ?case by simp
  next
    case (snoc ns m m')
    from snoc.prems have "m' \<in> set (\<alpha>n g)" by auto
    thus ?case
    proof (cases rule:lookupDef_cases[where v=v])
      case SimpleDef
      with snoc.prems(3) have False by simp
      thus ?thesis..
    next
      have step: "braun_ssa.liveVal g (lookupDef g m v) \<Longrightarrow> ?thesis"
      proof (rule snoc.IH)
        from snoc.prems(1) snoc.hyps(2) show "g \<turnstile> m-m#ms\<rightarrow>nUse" by auto
        from snoc.prems(3) snoc.hyps(1) show "\<forall>n\<in> set(ns @ m # ms). v \<notin> defs g n" by auto
      qed
      {
        case rec
        from snoc.hyps(2) rec(2) have[simp]: "predecessors g m' = [m]" by auto
        with rec snoc.prems(2) have "braun_ssa.liveVal g (lookupDef g m v)" by auto
        with step show ?thesis.
      next
        case PhiDef
        with snoc assms(2) have phiDefNode: "m' \<in> phiDefNodes g v" by -(rule phiDefNodesI, auto)
        from assms(2,4) have vars: "v \<in> vars g" by auto
        have "braun_ssa.liveVal g (lookupDef g m v)"
        proof (rule braun_ssa.livePhi)
          from PhiDef(3) snoc.prems(2) show "braun_ssa.liveVal g (v,m',PhiDef)" by simp
          from phiDefNode snoc.hyps(2) vars show "braun_ssa.phiArg g (v,m',PhiDef) (lookupDef g m v)"
            by (subst braun_ssa.phiArg_def, subst braun_ssa.phi_def, subst PhiDef_defNode_eq, auto simp: phis'_def)
        qed
        thus ?thesis by (rule step)
      }
    qed
  qed

  lemma phiDefNodes_aux_pruned:
    assumes "m \<in> phiDefNodes_aux g v (\<alpha>n g) n" "n \<in> set (\<alpha>n g)" "v \<in> uses g n"
    shows "braun_ssa.liveVal g (v, m, PhiDef)"
  proof-
    from assms(1,2) obtain ns where ns: "g \<turnstile> m-ns\<rightarrow>n" "\<forall>n \<in> set ns. v \<notin> defs g n" by (rule phiDefNodes_auxE)
    hence "v \<notin> defs g n" by (auto dest:path2_last simp: path2_not_Nil)
    with ns assms(1,3) show ?thesis
    apply-
    proof (rule phiDefNodes_aux_pruned_aux)
      from assms(2,3) show "braun_ssa.liveVal g (lookupDef g n v)" by -(rule braun_ssa.liveSimple, auto simp add:uses'_def)
    qed auto
  qed

  theorem phis'_pruned: "braun_ssa.pruned g"
  unfolding braun_ssa.pruned_def braun_ssa.phiDefs_def
  apply (subst phis'_def)
  by (auto split:prod.splits if_split_asm simp add:phiDefNodes_def elim!:fold_union_elem phiDefNodes_aux_pruned)

  declare var_def[simp del]

  declare no_disjoint_cycle [simp del]
  declare lookupDef_looksup [simp del]

  declare lookupDef.simps [code]
  declare phiDefNodes_aux.simps [code]
  declare phiDefNodes_def [code]
  declare defs'_def [code]
  declare uses'_def [code]
  declare phis'_def [code]
  declare predecessors_def [code]
end

end
