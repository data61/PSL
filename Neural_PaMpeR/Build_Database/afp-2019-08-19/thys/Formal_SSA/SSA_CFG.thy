(*  Title:      SSA_CFG.thy
    Author:     Sebastian Ullrich, Denis Lohner
*)

theory SSA_CFG
imports Graph_path "HOL-Library.Sublist"
begin

subsection \<open>CFG\<close>

locale CFG_base = graph_Entry_base \<alpha>e \<alpha>n invar inEdges' Entry
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry :: "'g \<Rightarrow> 'node" +
fixes "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set"
fixes "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set"
begin
  definition "vars g \<equiv> fold (\<union>) (map (uses g) (\<alpha>n g)) {}"
  definition defAss' :: "'g \<Rightarrow> 'node \<Rightarrow> 'var \<Rightarrow> bool" where
    "defAss' g m v \<longleftrightarrow> (\<forall>ns. g \<turnstile> Entry g-ns\<rightarrow>m \<longrightarrow> (\<exists>n \<in> set ns. v \<in> defs g n))"

  definition defAss'Uses :: "'g \<Rightarrow> bool" where
    "defAss'Uses g \<equiv> \<forall>m \<in> set (\<alpha>n g). \<forall>v \<in> uses g m. defAss' g m v"
end

locale CFG = CFG_base \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses"
+ graph_Entry \<alpha>e \<alpha>n invar inEdges' Entry
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry :: "'g \<Rightarrow> 'node" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set" +
assumes defs_uses_disjoint: "n \<in> set (\<alpha>n g) \<Longrightarrow> defs g n \<inter> uses g n = {}"
assumes defs_finite[simp]: "finite (defs g n)"
assumes uses_in_\<alpha>n: "v \<in> uses g n \<Longrightarrow> n \<in> set (\<alpha>n g)"
assumes uses_finite[simp, intro!]: "finite (uses g n)"
assumes invar[intro!]: "invar g"
begin
  lemma vars_finite[simp]: "finite (vars g)"
  by (auto simp:vars_def)

  lemma Entry_no_predecessor[simp]: "predecessors g (Entry g) = []"
  using Entry_unreachable
  by (auto simp:predecessors_def)

  lemma uses_in_vars[elim, simp]: "v \<in> uses g n \<Longrightarrow>  v \<in> vars g"
  by (auto simp add:vars_def uses_in_\<alpha>n intro!: fold_union_elemI)

  lemma varsE:
    assumes "v \<in> vars g"
    obtains n where "n \<in> set (\<alpha>n g)" "v \<in> uses g n"
  using assms by (auto simp:vars_def elim!:fold_union_elem)

  lemma defs_uses_disjoint'[simp]: "n \<in> set (\<alpha>n g) \<Longrightarrow> v \<in> defs g n \<Longrightarrow> v \<in> uses g n \<Longrightarrow> False"
  using defs_uses_disjoint by auto
end

context CFG
begin
  lemma defAss'E:
    assumes "defAss' g m v" "g \<turnstile> Entry g-ns\<rightarrow>m"
    obtains n where "n \<in> set ns" "v \<in> defs g n"
  using assms unfolding defAss'_def by auto

  lemmas defAss'I = defAss'_def[THEN iffD2, rule_format]

  lemma defAss'_extend:
    assumes "defAss' g m v"
    assumes "g \<turnstile> n-ns\<rightarrow>m" "\<forall>n \<in> set (tl ns). v \<notin> defs g n"
    shows "defAss' g n v"
  unfolding defAss'_def proof (rule allI, rule impI)
    fix ns'
    assume "g \<turnstile> Entry g-ns'\<rightarrow>n"
    with assms(2) have "g \<turnstile> Entry g-ns'@tl ns\<rightarrow>m" by auto
    with assms(1) obtain n' where n': "n' \<in> set (ns'@tl ns)" "v \<in> defs g n'" by -(erule defAss'E)
    with assms(3) have "n' \<notin> set (tl ns)" by auto
    with n' show "\<exists>n \<in> set ns'. v \<in> defs g n" by auto
  qed
end

text \<open>A CFG is well-formed if it satisfies definite assignment.\<close>

locale CFG_wf = CFG \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses"
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set" +
assumes def_ass_uses: "\<forall>m \<in> set (\<alpha>n g). \<forall>v \<in> uses g m. defAss' g m v"

subsection \<open>SSA CFG\<close>

type_synonym ('node, 'val) phis = "'node \<times> 'val \<rightharpoonup> 'val list"

declare in_set_zipE[elim]
declare zip_same[simp]

locale CFG_SSA_base = CFG_base \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses"
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val set" +
fixes phis :: "'g \<Rightarrow> ('node, 'val) phis"
begin
  definition "phiDefs g n \<equiv> {v. (n,v) \<in> dom (phis g)}"
  definition[code]: "allDefs g n \<equiv> defs g n \<union> phiDefs g n"

  definition[code]: "phiUses g n \<equiv>
    \<Union>n' \<in> set (successors g n). \<Union>v' \<in> phiDefs g n'. snd ` Set.filter (\<lambda>(n'',v). n'' = n) (set (zip (predecessors g n') (the (phis g (n',v')))))"
  definition[code]: "allUses g n \<equiv> uses g n \<union> phiUses g n"
  definition[code]: "allVars g \<equiv> \<Union>n \<in> set (\<alpha>n g). allDefs g n \<union> allUses g n"

  definition defAss :: "'g \<Rightarrow> 'node \<Rightarrow> 'val \<Rightarrow> bool" where
    "defAss g m v \<longleftrightarrow> (\<forall>ns. g \<turnstile> Entry g-ns\<rightarrow>m \<longrightarrow> (\<exists>n \<in> set ns. v \<in> allDefs g n))"

  lemmas CFG_SSA_defs = phiDefs_def allDefs_def phiUses_def allUses_def allVars_def defAss_def
end

locale CFG_SSA = CFG \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" + CFG_SSA_base \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val set" and
   phis :: "'g \<Rightarrow> ('node, 'val) phis" +
assumes phis_finite: "finite (dom (phis g))"
assumes phis_in_\<alpha>n: "phis g (n,v) = Some vs \<Longrightarrow> n \<in> set (\<alpha>n g)"
assumes phis_wf:
  "phis g (n,v) = Some args \<Longrightarrow> length (predecessors g n) = length args"
assumes simpleDefs_phiDefs_disjoint:             
  "n \<in> set (\<alpha>n g) \<Longrightarrow> defs g n \<inter> phiDefs g n = {}"
assumes allDefs_disjoint:
  "\<lbrakk>n \<in> set (\<alpha>n g); m \<in> set (\<alpha>n g); n \<noteq> m\<rbrakk> \<Longrightarrow> allDefs g n \<inter> allDefs g m = {}"
begin
  lemma phis_disj:
    assumes "phis g (n,v) = Some vs"
    and "phis g (n',v) = Some vs'"
    shows "n = n'" and "vs = vs'"
  proof -
    from assms have "n \<in> set (\<alpha>n g)" and "n' \<in> set (\<alpha>n g)"
      by (auto dest: phis_in_\<alpha>n)
    from allDefs_disjoint [OF this] assms show "n = n'"
      by (auto simp: allDefs_def phiDefs_def)
    with assms show "vs = vs'" by simp
  qed

  lemma allDefs_disjoint': "\<lbrakk>n \<in> set (\<alpha>n g); m \<in> set (\<alpha>n g); v \<in> allDefs g n; v \<in> allDefs g m\<rbrakk> \<Longrightarrow> n = m"
  using allDefs_disjoint by auto

  lemma phiUsesI:
    assumes "n' \<in> set (\<alpha>n g)" "phis g (n',v') = Some vs" "(n,v) \<in> set (zip (predecessors g n') vs)"
    shows "v \<in> phiUses g n"
  proof-
    from assms(3) have "n \<in> set (predecessors g n')" by auto
    hence 1: "n' \<in> set (successors g n)" using assms(1) by simp
    from assms(2) have 2: "v' \<in> phiDefs g n'" by (auto simp add:phiDefs_def)
    from assms(2) have 3: "the (phis g (n',v')) = vs" by simp
    show ?thesis unfolding phiUses_def by (rule UN_I[OF 1], rule UN_I[OF 2], auto simp:image_def Set.filter_def assms(3) 3)
  qed

  lemma phiUsesE:
    assumes "v \<in> phiUses g n"
    obtains  n' v' vs where "n' \<in> set (successors g n)" "(n,v) \<in> set (zip (predecessors g n') vs)" "phis g (n', v') = Some vs"
  proof-
    from assms(1) obtain n' v' where "n'\<in>set (successors g n)" "v'\<in>phiDefs g n'"
      "v \<in> snd ` Set.filter (\<lambda>(n'', v). n'' = n) (set (zip (predecessors g n') (the (phis g (n', v')))))" by (auto simp:phiUses_def)
    thus ?thesis by - (rule that[of n' "the (phis g (n',v'))" v'], auto simp:phiDefs_def)
  qed

  lemma defs_in_allDefs[simp]: "v \<in> defs g n \<Longrightarrow> v \<in> allDefs g n" by (simp add:allDefs_def)
  lemma phiDefs_in_allDefs[simp, elim]: "v \<in> phiDefs g n \<Longrightarrow> v \<in> allDefs g n" by (simp add:allDefs_def)
  lemma uses_in_allUses[simp]: "v \<in> uses g n \<Longrightarrow> v \<in> allUses g n" by (simp add:allUses_def)
  lemma phiUses_in_allUses[simp]: "v \<in> phiUses g n \<Longrightarrow> v \<in> allUses g n" by (simp add:allUses_def)
  lemma allDefs_in_allVars[simp, intro]: "\<lbrakk>v \<in> allDefs g n; n \<in> set (\<alpha>n g)\<rbrakk> \<Longrightarrow> v \<in> allVars g" by (auto simp:allVars_def)
  lemma allUses_in_allVars[simp, intro]: "\<lbrakk>v \<in> allUses g n; n \<in> set (\<alpha>n g)\<rbrakk> \<Longrightarrow> v \<in> allVars g" by (auto simp:allVars_def)

  lemma phiDefs_finite[simp]: "finite (phiDefs g n)"
  unfolding phiDefs_def
  proof (rule finite_surj[where f=snd], rule phis_finite[where g=g])
    have "\<And>x y. phis g (n,x) = Some y \<Longrightarrow> x \<in> snd ` dom (phis g)" by (metis domI imageI snd_conv)
    thus "{v. (n, v) \<in> dom (phis g)} \<subseteq> snd ` dom (phis g)" by auto
  qed

  lemma phiUses_finite[simp]:
    assumes "n \<in> set (\<alpha>n g)"
    shows "finite (phiUses g n)"
  by (auto simp:phiUses_def Set.filter_def)

  lemma allDefs_finite[simp]: "n \<in> set (\<alpha>n g) \<Longrightarrow> finite (allDefs g n)" by (auto simp add:allDefs_def)
  lemma allUses_finite[simp]: "n \<in> set (\<alpha>n g) \<Longrightarrow> finite (allUses g n)" by (auto simp add:allUses_def)
  lemma allVars_finite[simp]: "finite (allVars g)" by (auto simp add:allVars_def)

  lemmas defAssI = defAss_def[THEN iffD2, rule_format]
  lemmas defAssD = defAss_def[THEN iffD1, rule_format]

  lemma defAss_extend:
    assumes "defAss g m v"
    assumes "g \<turnstile> n-ns\<rightarrow>m" "\<forall>n \<in> set (tl ns). v \<notin> allDefs g n"
    shows "defAss g n v"
  unfolding defAss_def proof (rule allI, rule impI)
    fix ns'
    assume "g \<turnstile> Entry g-ns'\<rightarrow>n"
    with assms(2) have "g \<turnstile> Entry g-ns'@tl ns\<rightarrow>m" by auto
    with assms(1) obtain n' where n': "n' \<in> set (ns'@tl ns)" "v \<in> allDefs g n'" by (auto dest:defAssD)
    with assms(3) have "n' \<notin> set (tl ns)" by auto
    with n' show "\<exists>n \<in> set ns'. v \<in> allDefs g n" by auto
  qed

  lemma defAss_dominating:
    assumes[simp]: "n \<in> set (\<alpha>n g)"
    shows "defAss g n v \<longleftrightarrow> (\<exists>m \<in> set (\<alpha>n g). dominates g m n \<and> v \<in> allDefs g m)"
  proof
    assume asm: "defAss g n v"
    obtain ns where ns: "g \<turnstile> Entry g-ns\<rightarrow>n" by (atomize, auto)
    from defAssD[OF asm this] obtain m where m: "m \<in> set ns" "v \<in> allDefs g m" by auto
    have "dominates g m n"
    proof
      fix ns'
      assume ns': "g \<turnstile> Entry g-ns'\<rightarrow>n"
      from defAssD[OF asm this] obtain m' where m': "m' \<in> set ns'" "v \<in> allDefs g m'" by auto
      with m ns ns' have "m' = m" by - (rule allDefs_disjoint', auto)
      with m' show "m \<in> set ns'" by simp
    qed simp
    with m ns show "\<exists>m\<in>set (\<alpha>n g). dominates g m n \<and> v \<in> allDefs g m" by auto
  next
    assume "\<exists>m \<in> set (\<alpha>n g). dominates g m n \<and> v \<in> allDefs g m"
    then obtain m where[simp]: "m \<in> set (\<alpha>n g)" and m: "dominates g m n" "v \<in> allDefs g m" by auto
    show "defAss g n v"
    proof (rule defAssI)
      fix ns
      assume "g \<turnstile> Entry g-ns\<rightarrow>n"
      with m(1) have "m \<in> set ns" by - (rule dominates_mid, auto)
      with m(2) show "\<exists>n\<in>set ns. v \<in> allDefs g n" by auto
    qed
  qed
end

locale CFG_SSA_wf_base = CFG_SSA_base \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val set" and
  phis :: "'g \<Rightarrow> ('node, 'val) phis"
begin
  text \<open>Using the SSA properties, we can map every value to its unique defining node and
    remove the @{typ 'node} parameter of the @{term phis} map.\<close>

  definition defNode :: "'g \<Rightarrow> 'val \<Rightarrow> 'node" where
    defNode_code [code]: "defNode g v \<equiv> hd [n \<leftarrow> \<alpha>n g. v \<in> allDefs g n]"

  abbreviation "def_dominates g v' v \<equiv> dominates g (defNode g v') (defNode g v)"
  abbreviation "strict_def_dom g v' v \<equiv> defNode g v' \<noteq> defNode g v \<and> def_dominates g v' v"

  definition "phi g v = phis g (defNode g v,v)"
  definition[simp]: "phiArg g v v' \<equiv> \<exists>vs. phi g v = Some vs \<and> v' \<in> set vs"

  definition[code]: "isTrivialPhi g v v' \<longleftrightarrow> v' \<noteq> v \<and>
    (case phi g v of
      Some vs \<Rightarrow> set vs = {v,v'} \<or> set vs = {v'}
    | None \<Rightarrow> False)"
  definition[code]: "trivial g v \<equiv> \<exists>v' \<in> allVars g. isTrivialPhi g v v'"
  definition[code]: "redundant g \<equiv> \<exists>v \<in> allVars g. trivial g v"

  definition "defAssUses g \<equiv> \<forall>n \<in> set (\<alpha>n g). \<forall>v \<in> allUses g n. defAss g n v"

  text \<open>'liveness' of an SSA value is defined inductively starting from simple uses so that
    a circle of \pf s is not considered live.\<close>

  declare [[inductive_internals]]
  inductive liveVal :: "'g \<Rightarrow> 'val \<Rightarrow> bool"
    for g :: 'g
  where
    liveSimple: "\<lbrakk>n \<in> set (\<alpha>n g); val \<in> uses g n\<rbrakk> \<Longrightarrow> liveVal g val"
  | livePhi: "\<lbrakk>liveVal g v; phiArg g v v'\<rbrakk> \<Longrightarrow> liveVal g v'"

  definition "pruned g = (\<forall>n \<in> set (\<alpha>n g). \<forall>val. val \<in> phiDefs g n \<longrightarrow> liveVal g val)"

  lemmas "CFG_SSA_wf_defs" = CFG_SSA_defs defNode_code phi_def isTrivialPhi_def trivial_def redundant_def liveVal_def pruned_def
end

locale CFG_SSA_wf = CFG_SSA \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis + CFG_SSA_wf_base \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val set" and
  phis :: "'g \<Rightarrow> ('node, 'val) phis" +
  assumes allUses_def_ass: "\<lbrakk>v \<in> allUses g n; n \<in> set (\<alpha>n g)\<rbrakk> \<Longrightarrow> defAss g n v"
  assumes Entry_no_phis[simp]: "phis g (Entry g,v) = None"
begin
  lemma allVars_in_allDefs: "v \<in> allVars g \<Longrightarrow> \<exists>n \<in> set (\<alpha>n g). v \<in> allDefs g n"
    unfolding allVars_def
  apply auto
  apply (drule(1) allUses_def_ass)
  apply (clarsimp simp: defAss_def)
  apply (drule Entry_reaches)
   apply auto[1]
  by fastforce

  lemma phiDefs_Entry_empty[simp]: "phiDefs g (Entry g) = {}"
  by (auto simp: phiDefs_def)

  lemma phi_Entry_empty[simp]: "defNode g v = Entry g \<Longrightarrow> phi g v = None"
    by (simp add:phi_def)

  lemma defNode_ex1:
    assumes "v \<in> allVars g"
    shows "\<exists>!n. n \<in> set (\<alpha>n g) \<and> v \<in> allDefs g n"
  proof (rule ex_ex1I)
    show "\<exists>n. n \<in> set (\<alpha>n g) \<and> v \<in> allDefs g n"
    proof-
      from assms(1) obtain n where n: "n \<in> set (\<alpha>n g)" "v \<in> allDefs g n \<or> v \<in> allUses g n" by (auto simp:allVars_def)
      thus ?thesis
      proof (cases "v \<in> allUses g n")
        case True
        from n(1) obtain ns where ns: "g \<turnstile> Entry g-ns\<rightarrow>n" by (atomize_elim, rule Entry_reaches, auto)
        with allUses_def_ass[OF True n(1)] obtain m where m: "m \<in> set ns" "v \<in> allDefs g m" by - (drule defAssD, auto)
        from ns this(1) have "m \<in> set (\<alpha>n g)" by (rule path2_in_\<alpha>n)
        with n(1) m show ?thesis by auto
      qed auto
    qed
    show "\<And>n m. n \<in> set (\<alpha>n g) \<and> v \<in> allDefs g n \<Longrightarrow> m \<in> set (\<alpha>n g) \<and> v \<in> allDefs g m \<Longrightarrow> n = m" using allDefs_disjoint by auto
  qed

  lemma defNode_def: "v \<in> allVars g \<Longrightarrow> defNode g v = (THE n. n \<in> set (\<alpha>n g) \<and> v \<in> allDefs g n)"
  unfolding defNode_code by (rule the1_list[symmetric], rule defNode_ex1)

  lemma defNode[simp]:
    assumes "v \<in> allVars g"
    shows  "(defNode g v) \<in> set (\<alpha>n g)" "v \<in> allDefs g (defNode g v)"
  apply (atomize(full))
  unfolding defNode_def[OF assms] using assms
  by - (rule theI', rule defNode_ex1)

  lemma defNode_eq[intro]:
    assumes "n \<in> set (\<alpha>n g)" "v \<in> allDefs g n"
    shows "defNode g v = n"
  apply (subst defNode_def, rule allDefs_in_allVars[OF assms(2) assms(1)])
  by (rule the1_equality, rule defNode_ex1, rule allDefs_in_allVars[where n=n], simp_all add:assms)

  lemma defNode_cases[consumes 1]:
    assumes "v \<in> allVars g"
    obtains (simpleDef) "v \<in> defs g (defNode g v)"
          | (phi)       "phi g v \<noteq> None"
  proof (cases "v \<in> defs g (defNode g v)")
    case True
    thus thesis by (rule simpleDef)
  next
    case False
    with assms[THEN defNode(2)] show thesis
      by - (rule phi, auto simp: allDefs_def phiDefs_def phi_def)
  qed

  lemma phi_phiDefs[simp]: "phi g v = Some vs \<Longrightarrow> v \<in> phiDefs g (defNode g v)" by (auto simp:phiDefs_def phi_def)

  lemma simpleDef_not_phi:
    assumes "n \<in> set (\<alpha>n g)" "v \<in> defs g n"
    shows "phi g v = None"
  proof-
    from assms have "defNode g v = n" by auto
    with assms show ?thesis using simpleDefs_phiDefs_disjoint by (auto simp: phi_def phiDefs_def)
  qed

  lemma phi_wf: "phi g v = Some vs \<Longrightarrow> length (predecessors g (defNode g v)) = length vs"
  by (rule phis_wf) (simp add:phi_def)

  lemma phi_finite: "finite (dom (phi g))"
  proof-
    let ?f = "\<lambda>v. (defNode g v,v)"
    have "phi g = phis g \<circ> ?f" by (auto simp add:phi_def)
    moreover have "inj ?f" by (auto intro:injI)
    hence "finite (dom (phis g \<circ> ?f))" by - (rule finite_dom_comp, auto simp add:phis_finite inj_on_def)
    ultimately show ?thesis by simp
  qed

  lemma phiUses_exI:
    assumes "m \<in> set (predecessors g n)" "phis g (n,v) = Some vs" "n \<in> set (\<alpha>n g)"
    obtains v' where "v' \<in> phiUses g m" "v' \<in> set vs"
  proof-
    from assms(1) obtain i where i: "m = predecessors g n ! i" "i < length (predecessors g n)" by (metis in_set_conv_nth)
    with assms(2) phis_wf have[simp]: "i < length vs" by (auto simp add:phi_def)
    from i assms(2,3) have "vs ! i \<in> phiUses g m" by - (rule phiUsesI, auto simp add:phiUses_def phi_def set_zip)
    thus thesis by (rule that) (auto simp add:i(2) phis_wf)
  qed

  lemma phiArg_exI:
    assumes "m \<in> set (predecessors g (defNode g v))" "phi g v \<noteq> None" and[simp]: "v \<in> allVars g"
    obtains v' where "v' \<in> phiUses g m" "phiArg g v v'"
  proof-
    from assms(2) obtain vs where "phi g v = Some vs" by auto
    with assms(1) show thesis
      by - (rule phiUses_exI, auto intro!:that simp: phi_def)
  qed

  lemma phiUses_exI':
    assumes "phiArg g p q" and[simp]: "p \<in> allVars g"
    obtains m where "q \<in> phiUses g m" "m \<in> set (predecessors g (defNode g p))"
  proof-
    let ?n = "defNode g p"
    from assms(1) obtain i vs where vs: "phi g p = Some vs" and i: "q = vs ! i" "i < length vs" by (metis in_set_conv_nth phiArg_def)
    with phis_wf have[simp]: "i < length (predecessors g ?n)" by (auto simp add:phi_def)
    from vs i have "q \<in> phiUses g (predecessors g ?n ! i)" by - (rule phiUsesI, auto simp add:phiUses_def phi_def set_zip)
    thus thesis by (rule that) (auto simp add:i(2) phis_wf)
  qed

  lemma phiArg_in_allVars[simp]:
    assumes "phiArg g v v'"
    shows "v' \<in> allVars g"
  proof-
    let ?n = "defNode g v"
    from assms(1) obtain vs where vs: "phi g v = Some vs" "v' \<in> set vs" by auto
    then obtain m where m: "(m,v') \<in> set (zip (predecessors g ?n) vs)" by - (rule set_zip_leftI, rule phi_wf)
    from vs(1) have n: "?n \<in> set (\<alpha>n g)" by (simp add: phi_def phis_in_\<alpha>n)
    with m have[simp]: "m \<in> set (\<alpha>n g)" by auto
    from n m vs have "v' \<in> phiUses g m" by - (rule phiUsesI, simp_all add:phi_def)
    thus ?thesis by - (rule allUses_in_allVars, auto simp:allUses_def)
  qed

  lemma defAss_defNode:
    assumes "defAss g m v" "v \<in> allVars g" "g \<turnstile> Entry g-ns\<rightarrow>m"
    shows "defNode g v \<in> set ns"
  proof-
    from assms obtain n where n: "n \<in> set ns" "v \<in> allDefs g n" by (auto simp:defAss_def)
    with assms(3) have "n = defNode g v" by - (rule defNode_eq[symmetric], auto)
    with n show "defNode g v \<in> set ns" by (simp add:defAss_def)
  qed

  lemma defUse_path_ex:
    assumes "v \<in> allUses g m" "m \<in> set (\<alpha>n g)"
    obtains ns where "g \<turnstile> defNode g v-ns\<rightarrow>m" "EntryPath g ns"
  proof-
    from assms have "defAss g m v" by - (rule allUses_def_ass, auto)
    moreover from assms obtain ns where ns: "g \<turnstile> Entry g-ns\<rightarrow>m" "EntryPath g ns"
      by - (atomize_elim, rule Entry_reachesE, auto)
    ultimately have "defNode g v \<in> set ns" using assms(1)
      by - (rule defAss_defNode, auto)
    with ns(1) obtain ns' where "g \<turnstile> defNode g v-ns'\<rightarrow>m" "suffix ns' ns"
      by (rule path2_split_ex', auto simp: Sublist.suffix_def)
    thus thesis using ns(2)
      by - (rule that, assumption, rule EntryPath_suffix, auto)
  qed

  lemma defUse_path_dominated:
    assumes "g \<turnstile> defNode g v-ns\<rightarrow>n" "defNode g v \<notin> set (tl ns)" "v \<in> allUses g n" "n' \<in> set ns"
    shows "dominates g (defNode g v) n'"
  proof (rule dominatesI)
    fix es
    assume asm: "g \<turnstile> Entry g-es\<rightarrow>n'"
    from assms(1,4) obtain ns' where ns': "g \<turnstile> n'-ns'\<rightarrow>n" "suffix ns' ns"
      by - (rule path2_split_ex, auto simp: Sublist.suffix_def)
    from assms have "defAss g n v" by - (rule allUses_def_ass, auto)
    with asm ns'(1) assms(3) have "defNode g v \<in> set (es@tl ns')" by - (rule defAss_defNode, auto)
    with suffix_tl_subset[OF ns'(2)] assms(2) show "defNode g v \<in> set es" by auto
  next
    show "n' \<in> set (\<alpha>n g)" using assms(1,4) by auto
  qed

  lemma allUses_dominated:
    assumes "v \<in> allUses g n" "n \<in> set (\<alpha>n g)"
    shows "dominates g (defNode g v) n"
  proof-
    from assms obtain ns where "g \<turnstile> defNode g v-ns\<rightarrow>n" "defNode g v \<notin> set (tl ns)"
      by - (rule defUse_path_ex, auto elim: simple_path2)
    with assms(1) show ?thesis by - (rule defUse_path_dominated, auto)
  qed

  lemma phiArg_path_ex':
    assumes "phiArg g p q" and[simp]: "p \<in> allVars g"
    obtains ns m where "g \<turnstile> defNode g q-ns\<rightarrow>m" "EntryPath g ns" "q \<in> phiUses g m" "m \<in> set (predecessors g (defNode g p))"
  proof-
    from assms obtain m where m: "q \<in> phiUses g m" "m \<in> set (predecessors g (defNode g p))"
      by (rule phiUses_exI')
    then obtain ns where "g \<turnstile> defNode g q-ns\<rightarrow>m" "EntryPath g ns" by - (rule defUse_path_ex, auto)
    with m show thesis by - (rule that)
  qed

  lemma phiArg_path_ex:
    assumes "phiArg g p q" and[simp]: "p \<in> allVars g"
    obtains ns where "g \<turnstile> defNode g q-ns\<rightarrow>defNode g p" "length ns > 1"
    by (rule phiArg_path_ex'[OF assms], rule, auto)

  lemma phiArg_tranclp_path_ex:
    assumes "r\<^sup>+\<^sup>+ p q" "p \<in> allVars g" and[simp]: "\<And>p q. r p q \<Longrightarrow> phiArg g p q"
    obtains ns where "g \<turnstile> defNode g q-ns\<rightarrow>defNode g p" "length ns > 1"
      "\<forall>n \<in> set (butlast ns). \<exists>p q m ns'. r p q \<and> g \<turnstile> defNode g q-ns'\<rightarrow>m \<and> (defNode g q) \<notin> set (tl ns') \<and> q \<in> phiUses g m \<and> m \<in> set (predecessors g (defNode g p)) \<and> n \<in> set ns' \<and> set ns' \<subseteq> set ns \<and> defNode g p \<in> set ns"
  using assms(1,2) proof (induction rule: converse_tranclp_induct)
    case (base p)
    from base.hyps base.prems(2) obtain ns' m where ns': "g \<turnstile> defNode g q-ns'\<rightarrow>m" "defNode g q \<notin> set (tl ns')" "m \<in> set (predecessors g (defNode g p))" "q \<in> phiUses g m"
      by - (rule phiArg_path_ex', rule assms(3), auto intro: simple_path2)
    hence ns: "g \<turnstile> defNode g q-ns'@[defNode g p]\<rightarrow>defNode g p" "length (ns'@[defNode g p]) > 1" by auto

    show ?case
    proof (rule base.prems(1)[OF ns, rule_format], rule exI, rule exI, rule exI, rule exI)
      fix n
      assume "n \<in> set (butlast (ns' @ [defNode g p]))"
      with base.hyps ns'
      show "r p q \<and>
          g \<turnstile> defNode g q-ns'\<rightarrow>m \<and>
          defNode g q \<notin> set (tl ns') \<and>
          q \<in> phiUses g m \<and>
          m \<in> set (predecessors g (defNode g p)) \<and> n \<in> set ns' \<and> set ns' \<subseteq> set (ns' @ [defNode g p]) \<and> defNode g p \<in> set (ns' @ [defNode g p])"
        by auto
    qed
  next
    case (step p p')
    from step.prems(2) step.hyps(1) obtain ns'\<^sub>2 m where ns'\<^sub>2: "g \<turnstile> defNode g p'-ns'\<^sub>2\<rightarrow>m" "m \<in> set (predecessors g (defNode g p))" "defNode g p' \<notin> set (tl ns'\<^sub>2)" "p' \<in> phiUses g m"
      by - (rule phiArg_path_ex', rule assms(3), auto intro: simple_path2)
    then obtain ns\<^sub>2 where ns\<^sub>2: "g \<turnstile> defNode g p'-ns\<^sub>2\<rightarrow>defNode g p" "length ns\<^sub>2 > 1" "ns\<^sub>2 = ns'\<^sub>2@[defNode g p]" by (atomize_elim, auto)

    show thesis
    proof (rule step.IH)
      fix ns
      assume ns: "g \<turnstile> defNode g q-ns\<rightarrow>defNode g p'" "1 < length ns"
      assume IH: "\<forall>n\<in>set (butlast ns).
             \<exists>p q m ns'.
                r p q \<and>
                g \<turnstile> defNode g q-ns'\<rightarrow>m \<and>
                defNode g q \<notin> set (tl ns') \<and>
                q \<in> phiUses g m \<and> m \<in> set (predecessors g (defNode g p)) \<and> n \<in> set ns' \<and> set ns' \<subseteq> set ns \<and> defNode g p \<in> set ns"

      let ?path = "ns@tl ns\<^sub>2"
      have ns_ns\<^sub>2: "g \<turnstile> defNode g q-?path\<rightarrow>defNode g p" "1 < length ?path" using ns ns\<^sub>2(1,2) by auto
      show thesis
      proof (rule step.prems(1)[OF ns_ns\<^sub>2, rule_format])
        fix n
        assume n: "n \<in> set (butlast ?path)"
        show "\<exists>p q m ns'a.
          r p q \<and>
          g \<turnstile> defNode g q-ns'a\<rightarrow>m \<and>
          defNode g q \<notin> set (tl ns'a) \<and>
          q \<in> phiUses g m \<and> m \<in> set (predecessors g (defNode g p)) \<and> n \<in> set ns'a \<and> set ns'a \<subseteq> set ?path \<and> defNode g p \<in> set ?path"
        proof (cases "n \<in> set (butlast ns)")
          case True
          with IH obtain p q m ns' where "
                r p q \<and>
                g \<turnstile> defNode g q-ns'\<rightarrow>m \<and>
                defNode g q \<notin> set (tl ns') \<and>
                q \<in> phiUses g m \<and> m \<in> set (predecessors g (defNode g p)) \<and> n \<in> set ns' \<and> set ns' \<subseteq> set ns \<and> defNode g p \<in> set ns" by auto
          thus ?thesis by - (rule exI, rule exI, rule exI, rule exI, auto)
        next
          case False
          from ns ns\<^sub>2 have 1: "?path = butlast ns@ns\<^sub>2"
            by - (rule concat_join[symmetric], auto simp: path2_def)
          from ns\<^sub>2(1) n False 1 have "n \<in> set (butlast ns\<^sub>2)" by (auto simp: butlast_append path2_not_Nil)
          with step.hyps ns'\<^sub>2 ns\<^sub>2(3) show ?thesis
            by - (subst 1, rule exI[where x=p], rule exI[where x=p'], rule exI, rule exI, auto simp: path2_not_Nil)
        qed
      qed
    next
      show "p' \<in> allVars g" using step.prems(2) step.hyps(1)[THEN assms(3)] by auto
    qed
  qed

  lemma non_dominated_predecessor:
    assumes "n \<in> set (\<alpha>n g)" "n \<noteq> Entry g"
    obtains m where "m \<in> set (predecessors g n)" "\<not>dominates g n m"
  proof-
    obtain ns where "g \<turnstile> Entry g-ns\<rightarrow>n"
      by (atomize_elim, rule Entry_reaches, auto simp add:assms(1))
    then obtain ns' where ns': "g \<turnstile> Entry g-ns'\<rightarrow>n" "n \<notin> set (butlast ns')"
      by (rule simple_path2)
    let ?m = "last (butlast ns')"
    from ns'(1) assms(2) obtain m: "g \<turnstile> Entry g-butlast ns'\<rightarrow>?m" "?m \<in> set (predecessors g n)"
      by - (rule path2_unsnoc, auto)
    with m(1) ns'(2) show thesis
      by - (rule that, auto elim:dominatesE)
  qed

  lemmas dominates_trans'[trans, elim] = dominates_trans[OF invar]
  lemmas strict_dom_trans'[trans, elim] = strict_dom_trans[OF invar]
  lemmas dominates_refl'[simp] = dominates_refl[OF invar]
  lemmas dominates_antisymm'[dest] = dominates_antisymm[OF invar]

  lemma liveVal_in_allVars[simp]: "liveVal g v \<Longrightarrow> v \<in> allVars g"
  by (induction rule: liveVal.induct, auto intro!: allUses_in_allVars)

  lemma phi_no_closed_loop:
    assumes[simp]: "p \<in> allVars g" and "phi g p = Some vs"
    shows "set vs \<noteq> {p}"
  proof (cases "defNode g p = Entry g")
    case True
    with assms(2) show ?thesis by auto
  next
    case False
    show ?thesis
    proof
      assume[simp]: "set vs = {p}"
      let ?n = "defNode g p"
      obtain ns where ns: "g \<turnstile> Entry g-ns\<rightarrow>?n" "?n \<notin> set (butlast ns)" by (rule simple_Entry_path, auto)
      let ?m = "last (butlast ns)"
      from ns False obtain m: "g \<turnstile> Entry g-butlast ns\<rightarrow>?m" "?m \<in> set (predecessors g ?n)"
        by - (rule path2_unsnoc, auto)
      hence "p \<in> phiUses g ?m" using assms(2) by - (rule phiUses_exI, auto simp:phi_def)
      hence "defAss g ?m p" using m by - (rule allUses_def_ass, auto)
      then obtain l where l: "l \<in> set (butlast ns)" "p \<in> allDefs g l" using m by - (drule defAssD, auto)
      with assms(2) m have "l = ?n" by - (rule allDefs_disjoint', auto)
      with ns l m show False by auto
    qed
  qed

  lemma phis_phi: "phis g (n, v) = Some vs \<Longrightarrow> phi g v = Some vs"
  unfolding phi_def
  apply (subst defNode_eq)
  by (auto simp: allDefs_def phi_def phiDefs_def intro: phis_in_\<alpha>n)

  lemma trivial_phi: "trivial g v \<Longrightarrow> phi g v \<noteq> None"
  by (auto simp: trivial_def isTrivialPhi_def split: option.splits)

  lemma trivial_finite: "finite {v. trivial g v}"
  by (rule finite_subset[OF _ phi_finite]) (auto dest: trivial_phi)

  lemma trivial_in_allVars: "trivial g v \<Longrightarrow> v \<in> allVars g"
  by (drule trivial_phi, auto simp: allDefs_def phiDefs_def image_def phi_def intro: phis_in_\<alpha>n intro!: allDefs_in_allVars)

  declare phiArg_def [simp del]
end

subsection \<open>Bundling of CFG and Equivalent SSA CFG\<close>

locale CFG_SSA_Transformed_base = old: CFG_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses + CFG_SSA_wf_base \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  oldDefs :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val set" and
  phis :: "'g \<Rightarrow> ('node, 'val) phis" +
  fixes var :: "'g \<Rightarrow> 'val \<Rightarrow> 'var"

locale CFG_SSA_Transformed = CFG_SSA_Transformed_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var
  + old: CFG_wf \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses + CFG_SSA_wf \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  oldDefs :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val set" and
  phis :: "'g \<Rightarrow> ('node, 'val) phis" and
  var :: "'g \<Rightarrow> 'val \<Rightarrow> 'var" +
  assumes oldDefs_def: "oldDefs g n = var g ` defs g n"
  assumes oldUses_def: "n \<in> set (\<alpha>n g) \<Longrightarrow> oldUses g n = var g ` uses g n"
  assumes conventional: "
\<lbrakk>g \<turnstile> n-ns\<rightarrow>m; n \<notin> set (tl ns); v \<in> allDefs g n; v \<in> allUses g m; x \<in> set (tl ns); v' \<in> allDefs g x\<rbrakk> \<Longrightarrow> var g v' \<noteq> var g v"
  assumes phis_same_var[elim]: "phis g (n,v) = Some vs \<Longrightarrow> v' \<in> set vs \<Longrightarrow> var g v' = var g v"
  assumes allDefs_var_disjoint: "\<lbrakk>n \<in> set (\<alpha>n g); v \<in> allDefs g n; v' \<in> allDefs g n; v \<noteq> v'\<rbrakk> \<Longrightarrow> var g v' \<noteq> var g v"
begin
  lemma conventional': "\<lbrakk>g \<turnstile> n-ns\<rightarrow>m; n \<notin> set (tl ns); v \<in> allDefs g n; v \<in> allUses g m; v' \<in> allDefs g x; var g v' = var g v\<rbrakk> \<Longrightarrow> x \<notin> set (tl ns)"
    using conventional by auto

  lemma conventional'': "\<lbrakk>g \<turnstile> defNode g v-ns\<rightarrow>m; defNode g v \<notin> set (tl ns); v \<in> allUses g m; var g v' = var g v; v \<in> allVars g; v' \<in> allVars g\<rbrakk> \<Longrightarrow> defNode g v' \<notin> set (tl ns)"
    by (rule conventional'[where v=v and v'=v'], auto)

  lemma phiArg_same_var: "phiArg g p q \<Longrightarrow> var g q = var g p"
    by (metis phiArg_def phi_def phis_same_var)

  lemma oldDef_defAss:
    assumes "v \<in> allUses g n" "g \<turnstile> Entry g-ns\<rightarrow>n"
    obtains m where "m \<in> set ns" "var g v \<in> oldDefs g m"
  using assms proof (induction ns arbitrary: v n rule: length_induct)
    case (1 ns)
    from "1.prems"(2-) have 2: "defNode g v \<in> set ns"
      by - (rule defAss_defNode, rule allUses_def_ass, auto)
    let ?V = "defNode g v"
    from "1.prems"(2,3) have[simp]: "v \<in> allVars g" by auto
    thus ?case
    proof (cases v rule: defNode_cases)
      case simpleDef
      with 2 show thesis by - (rule "1.prems"(1), auto simp: oldDefs_def)
    next
      case phi
      then obtain vs where vs: "phi g v = Some vs" by auto
      from "1.prems"(3) 2 obtain ns' where ns': "g \<turnstile> Entry g-ns'\<rightarrow>?V" "prefix ns' ns"
        by (rule old.path2_split_ex, auto)
      let ?V' = "last (butlast ns')"
      from ns' phi have nontriv: "length ns' \<ge> 2"
        by - (rule old.path2_nontrivial, auto)
      hence 3: "g \<turnstile> Entry g-butlast ns'\<rightarrow>?V'" "?V' \<in> set (old.predecessors g ?V)"
        using ns'(1) by (auto intro: old.path2_unsnoc)
      with phi vs obtain v' where v': "v' \<in> phiUses g ?V'" "var g v' = var g v"
        by - (rule phiArg_exI, auto simp: phi_def phis_same_var phiArg_def)
      show thesis
      proof (rule "1.IH"[rule_format])
        show "length (butlast ns') < length ns" using ns' by (cases ns', auto simp: old.path2_not_Nil2 dest: prefix_length_le)
        show "v' \<in> allUses g ?V'" using v'(1) by simp
      next
        fix n
        assume "n \<in> set (butlast ns')" "var g v' \<in> oldDefs g n"
        thus thesis
          using ns'(2)[THEN set_mono_prefix] v'(2) by - (rule "1.prems"(1)[of n], auto dest: in_set_butlastD)
      qed (rule 3(1))
    qed
  qed

  lemma allDef_path_from_simpleDef:
    assumes[simp]: "v \<in> allVars g"
    obtains n ns where "g \<turnstile> n-ns\<rightarrow>defNode g v" "old.EntryPath g ns" "var g v \<in> oldDefs g n"
  proof-
    let ?V = "defNode g v"
    from assms obtain ns where ns: "g \<turnstile> Entry g-ns\<rightarrow>?V" "old.EntryPath g ns"
      by - (rule old.Entry_reachesE, auto)
    from assms show thesis
    proof (cases v rule: defNode_cases)
      case simpleDef
      thus thesis by - (rule that, auto simp: oldDefs_def)
    next
      case phi
      then obtain vs where vs: "phi g v = Some vs" by auto
      let ?V' = "last (butlast ns)"
      from ns phi have nontriv: "length ns \<ge> 2"
        by - (rule old.path2_nontrivial, auto)
      hence 3: "g \<turnstile> Entry g-butlast ns\<rightarrow>?V'" "?V' \<in> set (old.predecessors g ?V)"
        using ns(1) by (auto intro: old.path2_unsnoc)
      with phi vs obtain v' where v': "v' \<in> phiUses g ?V'" "var g v' = var g v"
        by - (rule phiArg_exI, auto simp: phi_def phis_same_var phiArg_def)
      with 3(1) obtain n where n: "n \<in> set (butlast ns)" "var g v' \<in> oldDefs g n"
        by - (rule oldDef_defAss[of v' g], auto)
      with ns obtain ns' where "g \<turnstile> n-ns'\<rightarrow>?V" "suffix ns' ns"
        by - (rule old.path2_split_ex'[OF ns(1)], auto intro: in_set_butlastD simp: Sublist.suffix_def)
      with n(2) v'(2) ns(2) show thesis
        by - (rule that, assumption, erule old.EntryPath_suffix, auto)
    qed
  qed

  lemma defNode_var_disjoint:
    assumes "p \<in> allVars g" "q \<in> allVars g" "p \<noteq> q" "defNode g p = defNode g q"
    shows "var g p \<noteq> var g q"
  proof-
    have "q \<in> allDefs g (defNode g p)" using assms(2) assms(4) by (auto)
    thus ?thesis using assms(1-3)
      by - (rule allDefs_var_disjoint[of "defNode g p" g], auto)
  qed

  lemma phiArg_distinct_nodes:
    assumes "phiArg g p q" "p \<noteq> q" and[simp]: "p \<in> allVars g"
    shows "defNode g p \<noteq> defNode g q"
  proof
    have "p \<in> allDefs g (defNode g p)" by simp
    moreover assume "defNode g p = defNode g q"
    ultimately have "var g p \<noteq> var g q" using assms
      by - (rule defNode_var_disjoint, auto)
    moreover
    from assms(1) have "var g q = var g p" by (rule phiArg_same_var)
    ultimately show False by simp
  qed

  lemma phiArgs_def_distinct:
    assumes "phiArg g p q" "phiArg g p r" "q \<noteq> r" "p \<in> allVars g"
    shows "defNode g q \<noteq> defNode g r"
  proof (rule)
    assume "defNode g q = defNode g r"
    hence "var g q \<noteq> var g r" using assms by - (rule defNode_var_disjoint, auto)
    thus False using phiArg_same_var[OF assms(1)] phiArg_same_var[OF assms(2)] by simp
  qed

  lemma defNode_not_on_defUse_path:
    assumes p: "g \<turnstile> defNode g p-ns\<rightarrow>n" "defNode g p \<notin> set (tl ns)" "p \<in> allUses g n"
    assumes[simp]: "q \<in> allVars g" "p \<noteq> q" "var g p = var g q"
    shows "defNode g q \<notin> set ns"
  proof-
    let ?P = "defNode g p"
    let ?Q = "defNode g q"

    have[simp]: "p \<in> allVars g" using p(1,3) by auto
    have "?P \<noteq> ?Q" using defNode_var_disjoint[of p g q] by auto
    moreover have "?Q \<notin> set (tl ns)" using p(2,3)
      by - (rule conventional'[OF p(1), of p q], auto)
    ultimately show ?thesis using p(1) by (cases ns, auto simp: old.path2_def)
  qed

  lemma defUse_paths_disjoint:
    assumes p: "g \<turnstile> defNode g p-ns\<rightarrow>n" "defNode g p \<notin> set (tl ns)" "p \<in> allUses g n"
    assumes q: "g \<turnstile> defNode g q-ms\<rightarrow>m" "defNode g q \<notin> set (tl ms)" "q \<in> allUses g m"
    assumes[simp]: "p \<noteq> q" "var g p = var g q"
    shows "set ns \<inter> set ms = {}"
  proof (rule equals0I)
    fix y
    assume y: "y \<in> set ns \<inter> set ms"

    {
      fix p ns n
      assume p: "g \<turnstile> defNode g p-ns\<rightarrow>n" "defNode g p \<notin> set (tl ns)" "p \<in> allUses g n"
      assume y: "y \<in> set ns"
      from p(1,3) have dom: "old.dominates g (defNode g p) n" by - (rule allUses_dominated, auto)
      moreover
      obtain ns' where "g \<turnstile> y-ns'\<rightarrow>n" "suffix ns' ns"
        by (rule old.path2_split_first_last[OF p(1) y], auto)
      ultimately have "old.dominates g (defNode g p) y" using suffix_tl_subset[of ns' ns] p(2)
        by - (rule old.dominates_extend[where ms=ns'], auto)
    }
    with assms y have dom: "old.dominates g (defNode g p) y" "old.dominates g (defNode g q) y" by auto

    {
      fix p ns n q ms m
      let ?P = "defNode g p"
      let ?Q = "defNode g q"

      assume p: "g \<turnstile> defNode g p-ns\<rightarrow>n" "defNode g p \<notin> set (tl ns)" "p \<in> allUses g n" "old.dominates g ?P y" "y \<in> set ns"
      assume q: "g \<turnstile> defNode g q-ms\<rightarrow>m" "defNode g q \<notin> set (tl ms)" "q \<in> allUses g m" "old.dominates g ?Q y" "y \<in> set ms"
      assume[simp]: "p \<noteq> q" "var g p = var g q"
      assume dom: "old.dominates g ?P ?Q"
      then obtain pqs where pqs: "g \<turnstile> ?P-pqs\<rightarrow>?Q" "?P \<notin> set (tl pqs)" by (rule old.dominates_path, auto intro: old.simple_path2)
      from p obtain ns\<^sub>2 where ns\<^sub>2: "g \<turnstile> y-ns\<^sub>2\<rightarrow>n" "suffix ns\<^sub>2 ns" by - (rule old.path2_split_first_last, auto)
      from q obtain ms\<^sub>1 where ms\<^sub>1: "g \<turnstile> ?Q-ms\<^sub>1\<rightarrow>y" "prefix ms\<^sub>1 ms" by - (rule old.path2_split_first_last, auto)
      have "var g q \<noteq> var g p"
      proof (rule conventional[OF _ _ _ p(3)])
        let ?path = "(pqs@tl ms\<^sub>1)@tl ns\<^sub>2"
        show "g \<turnstile> ?P-?path\<rightarrow>n" using pqs ms\<^sub>1 ns\<^sub>2
          by (auto simp del:append_assoc intro:old.path2_app)
        have "?P \<notin> set (tl ns\<^sub>2)" using p(2) ns\<^sub>2(2)[THEN suffix_tl_subset, THEN subsetD] by auto
        moreover
        have[simp]: "q \<in> allVars g" "p \<in> allVars g" using p q by auto
        have "?P \<notin> set (tl ms)" using q
          by - (rule conventional'[where v'=p and v=q], auto)
        hence "?P \<notin> set (tl ms\<^sub>1)" using ms\<^sub>1(2)[simplified, THEN prefix_tl_subset] by auto
        ultimately
        show "?P \<notin> set (tl ?path)" using pqs(2)
          by - (rule notI, auto dest: subsetD[OF set_tl_append'])
        show "p \<in> allDefs g (defNode g p)" by auto
        have "?P \<noteq> ?Q" using defNode_var_disjoint[of p g q] by auto
        hence 1: "length pqs > 1" using pqs by - (rule old.path2_nontriv)
        hence "?Q \<in> set (tl pqs)" using pqs unfolding old.path2_def by (auto intro:last_in_tl)
        moreover from 1 have "pqs \<noteq> []" by auto
        ultimately show "?Q \<in> set (tl ?path)" by simp
        show "q \<in> allDefs g ?Q" by simp
      qed
      hence False by simp
    }
    from this[OF p _ _ q] this[OF q _ _ p] y dom show False
      by - (rule old.dominates_antitrans[OF _ dom], auto)
  qed

  lemma oldDefsI: "v \<in> defs g n \<Longrightarrow> var g v \<in> oldDefs g n" by (simp add: oldDefs_def)
 
  lemma simpleDefs_phiDefs_var_disjoint:
    assumes "v \<in> phiDefs g n" "n \<in> set (\<alpha>n g)"
    shows "var g v \<notin> oldDefs g n"
  proof
    from assms have[simp]: "v \<in> allVars g" by auto
    assume "var g v \<in> oldDefs g n"
    then obtain v'' where v'': "v'' \<in> defs g n" "var g v'' = var g v"
      by (auto simp: oldDefs_def)
    from this(1) assms have "v'' \<noteq> v"
      using simpleDefs_phiDefs_disjoint[of n g] by (auto simp: phiArg_def)
    with v'' assms show False
      using allDefs_var_disjoint[of n g v'' v] by auto
  qed

  lemma liveVal_use_path: 
    assumes "liveVal g v"
    obtains ns m where "g \<turnstile> defNode g v-ns\<rightarrow>m" "var g v \<in> oldUses g m"
      "\<And>x. x \<in> set (tl ns) \<Longrightarrow> var g v \<notin> oldDefs g x"
  using assms proof (induction)
    case (liveSimple m v)
    from liveSimple.hyps have[simp]: "v \<in> allVars g"
      by - (rule allUses_in_allVars, auto)
    from liveSimple.hyps obtain ns where ns: "g \<turnstile> defNode g v-ns\<rightarrow>m" "defNode g v \<notin> set (tl ns)"
      by - (rule defUse_path_ex, auto intro!: uses_in_allUses elim: old.simple_path2)
    from this(1) show thesis
    proof (rule liveSimple.prems)
      show "var g v \<in> oldUses g m" using liveSimple.hyps by (auto simp: oldUses_def)
      {
        fix x
        assume asm: "x \<in> set (tl ns)" "var g v \<in> oldDefs g x"
        then obtain v' where "v' \<in> defs g x" "var g v' = var g v"
          by (auto simp: oldDefs_def)
        with asm liveSimple.hyps have False
          by - (rule conventional[OF ns, of v x v', THEN notE], auto)
      }
      thus "\<And>x. x \<in> set (tl ns) \<Longrightarrow> var g v \<notin> oldDefs g x" by auto
    qed
  next
    case (livePhi v v')
    from livePhi.hyps have[simp]: "v \<in> allVars g" "v' \<in> allVars g" "var g v' = var g v"
      by (auto intro: phiArg_same_var)
    show thesis
    proof (rule livePhi.IH)
      fix ns m
      assume asm: "g \<turnstile> defNode g v-ns\<rightarrow>m" "var g v \<in> oldUses g m"
        "\<And>x. x \<in> set (tl ns) \<Longrightarrow> var g v \<notin> oldDefs g x"
      from livePhi.hyps(2) obtain ns' m' where ns': "g \<turnstile> defNode g v'-ns'\<rightarrow>m'" "v' \<in> phiUses g m'"
        "m' \<in> set (old.predecessors g (defNode g v))" "defNode g v' \<notin> set (tl ns')"
        by (rule phiArg_path_ex', auto elim: old.simple_path2)
      show thesis 
      proof (rule livePhi.prems)
        show "g \<turnstile> defNode g v'-(ns'@[defNode g v])@tl ns\<rightarrow>m"
        apply (rule old.path2_app)
         apply (rule old.path2_snoc[OF ns'(1,3)])
        by (rule asm(1))
        show "var g v' \<in> oldUses g m" using asm(2) by simp
        {
          fix x
          assume asm: "x \<in> set (tl ns')" "var g v \<in> oldDefs g x"
          then obtain v'' where "v'' \<in> defs g x" "var g v'' = var g v"
            by (auto simp: oldDefs_def)
          with asm ns'(2) have False
            by - (rule conventional[OF ns'(1,4), of v' x v'', THEN notE], auto)
        }
        then show "\<And>x. x \<in> set (tl ((ns'@[defNode g v])@tl ns)) \<Longrightarrow> var g v' \<notin> oldDefs g x"
          using simpleDefs_phiDefs_var_disjoint[of v g "defNode g v"] livePhi.hyps(2)
          by (auto dest!: set_tl_append'[THEN subsetD] asm(3) simp: phiArg_def)
      qed
    qed
  qed
end

end
