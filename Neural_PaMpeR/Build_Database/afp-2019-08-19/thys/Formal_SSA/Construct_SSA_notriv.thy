(*  Title:      Construct_SSA_notriv_code.thy
    Author:     Sebastian Ullrich, Denis Lohner
*)

subsection \<open>Inductive Removal of Trivial Phi Functions\<close>

theory Construct_SSA_notriv
imports SSA_CFG Minimality "HOL-Library.While_Combinator"
begin

locale CFG_SSA_Transformed_notriv_base = CFG_SSA_Transformed_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var
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
fixes chooseNext_all :: "('node \<Rightarrow> 'val set) \<Rightarrow> ('node, 'val) phis \<Rightarrow> 'g \<Rightarrow> ('node \<times> 'val)"
begin
  abbreviation "chooseNext g \<equiv> snd (chooseNext_all (uses g) (phis g) g)"
  abbreviation "chooseNext' g \<equiv> chooseNext_all (uses g) (phis g) g"

  definition "substitution g \<equiv> THE v'. isTrivialPhi g (chooseNext g) v'"
  definition "substNext g \<equiv> \<lambda>v. if v = chooseNext g then substitution g else v"
  definition[simp]: "uses' g n \<equiv> substNext g ` uses g n"
  definition[simp]: "phis' g x \<equiv> case x of (n,v) \<Rightarrow> if v = chooseNext g
    then None
    else map_option (map (substNext g)) (phis g (n,v))"
end

locale CFG_SSA_Transformed_notriv = CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var
  + CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  "oldDefs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  "oldUses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val set" and
  phis :: "'g \<Rightarrow> ('node, 'val) phis" and
  var :: "'g \<Rightarrow> 'val \<Rightarrow> 'var" and
  chooseNext_all :: "('node \<Rightarrow> 'val set) \<Rightarrow> ('node, 'val) phis \<Rightarrow> 'g \<Rightarrow> ('node \<times> 'val)" +
assumes chooseNext_all: "CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs u p var \<Longrightarrow>
  CFG_SSA_wf_base.redundant \<alpha>n inEdges' defs u p g \<Longrightarrow>
  chooseNext_all (u g) (p g) g \<in> dom (p g) \<and>
  CFG_SSA_wf_base.trivial \<alpha>n inEdges' defs u p g (snd (chooseNext_all (u g) (p g) g))"
begin
  lemma chooseNext':"redundant g \<Longrightarrow> chooseNext' g \<in> dom (phis g) \<and> trivial g (chooseNext g)"
  by (rule chooseNext_all, unfold_locales)

  lemma chooseNext: "redundant g \<Longrightarrow> chooseNext g \<in> allVars g \<and> trivial g (chooseNext g)"
  by (drule chooseNext', auto simp: trivial_in_allVars)

  lemmas chooseNext_in_allVars[simp] = chooseNext[THEN conjunct1]

  lemma isTrivialPhi_det: "trivial g v \<Longrightarrow> \<exists>!v'. isTrivialPhi g v v'"
  proof(rule ex_ex1I)
    fix v' v''
    assume "isTrivialPhi g v v'" "isTrivialPhi g v v''"
    from this[unfolded isTrivialPhi_def, THEN conjunct2] show "v' = v''" by (auto simp:isTrivialPhi_def doubleton_eq_iff split:option.splits)
  qed (auto simp: trivial_def)

  lemma trivialPhi_strict_dom:
    assumes[simp]: "v \<in> allVars g" and triv: "isTrivialPhi g v v'"
    shows "strict_def_dom g v' v"
  proof
    let ?n = "defNode g v"
    let ?n' = "defNode g v'"
    from triv obtain vs where vs: "phi g v = Some vs" "(set vs = {v'} \<or> set vs = {v,v'})" by (auto simp:isTrivialPhi_def split:option.splits)
    hence "?n \<noteq> Entry g" by auto

    have other_preds_dominated: "\<And>m. m \<in> set (old.predecessors g ?n) \<Longrightarrow> v' \<notin> phiUses g m \<Longrightarrow> old.dominates g ?n m"
    proof-
      fix m
      assume m: "m \<in> set (old.predecessors g ?n)" "v' \<notin> phiUses g m"
      hence[simp]: "m \<in> set (\<alpha>n g)" by auto
      show "old.dominates g ?n m"
      proof (cases "v \<in> phiUses g m")
        case True
        hence "v \<in> allUses g m" by simp
        thus ?thesis by (rule allUses_dominated) simp_all
      next
        case False
        with vs have  "v' \<in> phiUses g m" by - (rule phiUses_exI[OF m(1)], auto simp:phi_def)
        with m(2) show ?thesis by simp
      qed
    qed

    show "?n' \<noteq> ?n"
    proof (rule notI)
      assume asm: "?n' = ?n"
      have "\<And>m. m \<in> set (old.predecessors g ?n) \<Longrightarrow> v' \<in> phiUses g m \<Longrightarrow> old.dominates g ?n m"
      proof-
        fix m
        assume "m \<in> set (old.predecessors g ?n)" "v' \<in> phiUses g m"
        hence "old.dominates g ?n' m" by - (rule allUses_dominated, auto)
        thus "?thesis m" by (simp add:asm)
      qed
      with non_dominated_predecessor[of ?n g] other_preds_dominated \<open>?n \<noteq> Entry g\<close> show False by auto
    qed

    show "old.dominates g ?n' ?n"
    proof
      fix ns
      assume asm: "g \<turnstile> Entry g-ns\<rightarrow>?n"
      from \<open>?n \<noteq> Entry g\<close> obtain m ns'
        where ns': "g \<turnstile> Entry g-ns'\<rightarrow>m" "m \<in> set (old.predecessors g ?n)" "?n \<notin> set ns'" "set ns' \<subseteq> set ns"
        by - (rule old.simple_path2_unsnoc[OF asm], auto)
      hence[simp]: "m \<in> set (\<alpha>n g)" by auto
      from ns' have "\<not>old.dominates g ?n m" by (auto elim:old.dominatesE)
      with other_preds_dominated[of m] ns'(2) have "v' \<in> phiUses g m" by auto
      hence "old.dominates g ?n' m" by - (rule allUses_dominated, auto)
      with ns'(1) have "?n' \<in> set ns'" by - (erule old.dominatesE)
      with ns'(4) show "?n' \<in> set ns" by auto
    qed auto
  qed

  lemma isTrivialPhi_asymmetric:
  assumes "isTrivialPhi g a b"
    and "isTrivialPhi g b a"
  shows "False"
  using assms
  proof -
    from \<open>isTrivialPhi g a b\<close>
    have "b \<in> allVars g"
      unfolding isTrivialPhi_def
      by (fastforce intro!: phiArg_in_allVars simp: phiArg_def split: option.splits)
    from \<open>isTrivialPhi g b a\<close>
    have "a \<in> allVars g"
      unfolding isTrivialPhi_def
      by (fastforce intro!: phiArg_in_allVars simp: phiArg_def split: option.splits)
    from trivialPhi_strict_dom [OF \<open>a \<in> allVars g\<close> assms(1)]
       trivialPhi_strict_dom [OF \<open>b \<in> allVars g\<close> assms(2)]
    show ?thesis by blast
  qed

  lemma substitution[intro]: "redundant g \<Longrightarrow> isTrivialPhi g (chooseNext g) (substitution g)"
    unfolding substitution_def by (rule theI', rule isTrivialPhi_det, simp add: chooseNext)

  lemma trivialPhi_in_allVars[simp]:
    assumes "isTrivialPhi g v v'" and[simp]: "v \<in> allVars g"
    shows "v' \<in> allVars g"
  proof-
    from assms(1) have "phiArg g v v'"
      unfolding phiArg_def
      by (auto simp:isTrivialPhi_def split:option.splits)
    thus "v' \<in> allVars g" by - (rule phiArg_in_allVars, auto)
  qed

  lemma substitution_in_allVars[simp]:
    assumes "redundant g"
    shows "substitution g \<in> allVars g"
  using assms by - (rule trivialPhi_in_allVars, auto)

  lemma defs_uses_disjoint_inv:
    assumes[simp]: "n \<in> set (\<alpha>n g)" "redundant g"
    shows "defs g n \<inter> uses' g n = {}"
  proof (rule equals0I)
    fix v'
    assume asm: "v' \<in> defs g n \<inter> uses' g n"
    then obtain v where v: "v \<in> uses g n" "v' = substNext g v" and v': "v' \<in> defs g n" by auto
    show False
    proof (cases "v = chooseNext g")
      case False
      thus ?thesis using v v' defs_uses_disjoint[of n g] by (auto simp:substNext_def split:if_split_asm)
    next
      case [simp]: True
      from v' have n_defNode: "n = defNode g v'" by - (rule defNode_eq[symmetric], auto)
      from v(1) have[simp]: "v \<in> allVars g" by - (rule allUses_in_allVars[where n=n], auto)
      let ?n' = "defNode g v"
      have "old.strict_dom g n ?n'"
        by (simp only:n_defNode v(2), rule trivialPhi_strict_dom, auto simp:substNext_def)
      moreover from v(1) have "old.dominates g ?n' n" by - (rule allUses_dominated, auto)
      ultimately show False by auto
    qed
  qed
end

context CFG_SSA_wf
begin
  inductive liveVal' :: "'g \<Rightarrow> 'val list \<Rightarrow> bool"
    for g :: 'g
  where
    liveSimple': "\<lbrakk>n \<in> set (\<alpha>n g); val \<in> uses g n\<rbrakk> \<Longrightarrow> liveVal' g [val]"
  | livePhi': "\<lbrakk>liveVal' g (v#vs); phiArg g v v'\<rbrakk> \<Longrightarrow> liveVal' g (v'#v#vs)"

  lemma liveVal'_suffix:
    assumes "liveVal' g vs" "suffix vs' vs" "vs' \<noteq> []"
    shows "liveVal' g vs'"
  using assms proof induction
    case (liveSimple' n v)
    from liveSimple'.prems have "vs' = [v]"
      by (metis append_Nil butlast.simps(2) suffixI suffix_order.antisym suffix_unsnoc)
    with liveSimple'.hyps show ?case by (auto intro: liveVal'.liveSimple')
  next
    case (livePhi' v vs v')
    show ?case
    proof (cases "vs' = v' # v # vs")
      case True
      with livePhi' show ?thesis by - (auto intro: liveVal'.livePhi')
    next
      case False
      with livePhi'.prems have "suffix vs' (v#vs)"
        by (metis list.sel(3) self_append_conv2 suffixI suffix_take tl_append2)
      with livePhi'.prems(2) show ?thesis by - (rule livePhi'.IH)
    qed
  qed

  lemma liveVal'I:
    assumes "liveVal g v"
    obtains vs where "liveVal' g (v#vs)"
  using assms proof induction
    case (liveSimple n v)
    thus thesis by - (rule liveSimple(3), rule liveSimple')
  next
    case (livePhi v v')
    show thesis
    proof (rule livePhi.IH)
      fix vs
      assume asm: "liveVal' g (v#vs)"
      show thesis
      proof (cases "v' \<in> set (v#vs)")
        case False
        with livePhi.hyps asm show thesis by - (rule livePhi.prems, rule livePhi')
      next
        case True
        then obtain vs' where "suffix (v'#vs') (v#vs)"
          by - (drule split_list_last, auto simp: Sublist.suffix_def)
        with asm show thesis by - (rule livePhi.prems, rule liveVal'_suffix, simp_all)
      qed
    qed
  qed

  lemma liveVal'D:
    assumes "liveVal' g vs" "vs = v#vs'"
    shows "liveVal g v"
  using assms proof (induction arbitrary: v vs')
    case (liveSimple' n vs)
    thus ?case by - (rule liveSimple, auto)
  next
    case (livePhi' v\<^sub>2 vs v')
    thus ?case by - (rule livePhi, auto)
  qed
end

locale CFG_SSA_step = CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  "oldDefs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  "oldUses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val set" and
  phis :: "'g \<Rightarrow> ('node, 'val) phis" and
  var :: "'g \<Rightarrow> 'val \<Rightarrow> 'var" and
  chooseNext_all :: "('node \<Rightarrow> 'val set) \<Rightarrow> ('node, 'val) phis \<Rightarrow> 'g \<Rightarrow> ('node \<times> 'val)" and
  g :: "'g" +
assumes redundant[simp]: "redundant g"
begin
  abbreviation "u_g \<equiv> uses(g:=uses' g)"
  abbreviation "p_g \<equiv> phis(g:=phis' g)"

  sublocale step: CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" u_g p_g var chooseNext_all .

  lemma simpleDefs_phiDefs_disjoint_inv:
    assumes "n \<in> set (\<alpha>n g)"
    shows "defs g n \<inter> step.phiDefs g n = {}"
  using simpleDefs_phiDefs_disjoint[OF assms]
  by (auto simp: phiDefs_def step.phiDefs_def dom_def split:option.splits)

  lemma allDefs_disjoint_inv:
    assumes "n \<in> set (\<alpha>n g)" "m \<in> set (\<alpha>n g)" "n \<noteq> m"
    shows "step.allDefs g n \<inter> step.allDefs g m = {}"
  using allDefs_disjoint[OF assms]
  by (auto simp: CFG_SSA_defs step.CFG_SSA_defs dom_def split:option.splits)

  lemma phis_finite_inv:
    shows "finite (dom (phis' g))"
  using phis_finite[of g] by - (rule finite_subset, auto split:if_split_asm)

  lemma phis_wf_inv:
    assumes "phis' g (n, v) = Some args"
    shows "length (old.predecessors g n) = length args"
  using phis_wf[of g] assms by (auto split:if_split_asm)


  sublocale step: CFG_SSA \<alpha>e \<alpha>n invar inEdges' Entry "defs" u_g p_g
  apply unfold_locales
  apply (rename_tac g')
  apply (case_tac "g'=g")
   apply (simp add:defs_uses_disjoint_inv[simplified])
   apply (simp add:defs_uses_disjoint)
  apply (rule defs_finite)
  apply (auto simp: uses_in_\<alpha>n split: if_split_asm)[1]
  apply (rename_tac g' n)
  apply (case_tac "g'=g")
   apply simp
   apply simp
  apply (rule invar)
  apply (rename_tac g')
  apply (case_tac "g'=g")
   apply (simp add:phis_finite_inv)
   apply (simp add:phis_finite)
  apply (auto simp: phis_in_\<alpha>n split: if_split_asm)[1]
  apply (rename_tac g' n v args)
  apply (case_tac "g'=g")
   apply (simp add:phis_wf_inv)
   apply (simp add:phis_wf)
  apply (rename_tac g')
  apply (case_tac "g'=g")
   apply (simp add: simpleDefs_phiDefs_disjoint_inv)
   apply (simp add: simpleDefs_phiDefs_disjoint[unfolded CFG_SSA_defs] step.CFG_SSA_defs )
  apply (rename_tac g' m)
  apply (case_tac "g'=g")
   apply (simp add: allDefs_disjoint_inv)
  apply (simp add: allDefs_disjoint[unfolded CFG_SSA_defs] step.CFG_SSA_defs)
  done

  lemma allUses_narrows:
    assumes "n \<in> set (\<alpha>n g)"
    shows "step.allUses g n \<subseteq> substNext g ` allUses g n"
  proof-
    have "\<And>n' v' z b. phis g (n', v') = Some z \<Longrightarrow> (n, b) \<in> set (zip (old.predecessors g n') z) \<Longrightarrow> b \<notin> phiUses g n \<Longrightarrow> b \<in> uses g n"
    proof-
      fix n' v' z b
      assume "(n, b) \<in> set (zip (old.predecessors g n') (z :: 'val list))"
      with assms(1) have "n' \<in> set (\<alpha>n g)" by auto
      thus "phis g (n', v') = Some z \<Longrightarrow> (n, b) \<in> set (zip (old.predecessors g n') z) \<Longrightarrow> b \<notin> phiUses g n \<Longrightarrow> b \<in> uses g n" by (auto intro:phiUsesI)
    qed
    thus ?thesis by (auto simp:step.allUses_def allUses_def zip_map2 intro!:imageI elim!:step.phiUsesE phiUsesE split:if_split_asm)
  qed

  lemma allDefs_narrows[simp]: "v \<in> step.allDefs g n \<Longrightarrow> v \<in> allDefs g n"
    by (auto simp:step.allDefs_def step.phiDefs_def phiDefs_def allDefs_def split:if_split_asm)

  lemma allUses_def_ass_inv:
    assumes "v' \<in> step.allUses g n" "n \<in> set (\<alpha>n g)"
    shows "step.defAss g n v'"
  proof (rule step.defAssI)
    fix ns
    assume asm: "g \<turnstile> Entry g-ns\<rightarrow>n"

    from assms obtain v where v': "v' = substNext g v" and[simp]: "v \<in> allUses g n"
      using allUses_narrows by auto
    with assms(2) have[simp]: "v \<in> allVars g" by - (rule allUses_in_allVars)
    have[simp]: "v' \<in> allVars g" by (simp add:substNext_def v')
    let ?n\<^sub>v = "defNode g v"
    let ?n\<^sub>v\<^sub>' = "defNode g v'"
    from assms(2) asm have 1: "?n\<^sub>v \<in> set ns" using allUses_def_ass[of v g n] by (simp add:defAss_defNode)
    then obtain ns\<^sub>v where ns\<^sub>v: "prefix (ns\<^sub>v@[?n\<^sub>v]) ns" by (rule prefix_split_first)
    with asm have 2: "g \<turnstile> Entry g-ns\<^sub>v@[?n\<^sub>v]\<rightarrow>?n\<^sub>v" by auto
    show "\<exists>n \<in> set ns. v' \<in> step.allDefs g n"
    proof (cases "v = chooseNext g")
      case True
      hence dom: "strict_def_dom g v' v" using substitution[of g] by - (rule trivialPhi_strict_dom, simp_all add:substNext_def v')
      hence[simp]: "v' \<noteq> v" by auto
      have "v' \<in> allDefs g ?n\<^sub>v\<^sub>'" by simp
      hence "v' \<in> step.allDefs g ?n\<^sub>v\<^sub>'" unfolding step.allDefs_def step.phiDefs_def allDefs_def phiDefs_def by (auto simp:True[symmetric])
      moreover have "?n\<^sub>v\<^sub>' \<in> set ns"
      proof-
        from dom have "def_dominates g v' v" by auto
        hence "?n\<^sub>v\<^sub>' \<in> set (ns\<^sub>v@[?n\<^sub>v])" using 2 by -(erule old.dominatesE)
        with ns\<^sub>v show ?thesis by auto
      qed
      ultimately show ?thesis by auto
    next
      case [simp]: False
      have[simp]: "v' = v" by (simp add:v' substNext_def)
      have "v \<in> allDefs g ?n\<^sub>v" by simp
      thus ?thesis by - (rule bexI[of _ ?n\<^sub>v\<^sub>'], auto simp:allDefs_def step.allDefs_def step.phiDefs_def 1 phiDefs_def)
    qed
  qed

  lemma Entry_no_phis_inv: "phis' g (Entry g, v) = None"
  by (simp add:Entry_no_phis)

  sublocale step: CFG_SSA_wf \<alpha>e \<alpha>n invar inEdges' Entry "defs" u_g p_g
  apply unfold_locales
  apply (rename_tac g' n)
  apply (case_tac "g'=g")
   apply (simp add:allUses_def_ass_inv)
   apply (simp add:allUses_def_ass[unfolded CFG_SSA_defs, simplified] step.CFG_SSA_defs)
  apply (rename_tac g' v)
  apply (case_tac "g'=g")
   apply (simp add:Entry_no_phis_inv)
   apply (simp)
  done

  lemma chooseNext_eliminated: "chooseNext g \<notin> step.allDefs g (defNode g (chooseNext g))"
  proof-
    let ?v = "chooseNext g"
    let ?n = "defNode g ?v"
    from chooseNext[OF redundant] have "?v \<in> phiDefs g ?n" "?n \<in> set (\<alpha>n g)"
      by (auto simp: trivial_def isTrivialPhi_def phiDefs_def phi_def split: option.splits)
    hence "?v \<notin> defs g ?n" using simpleDefs_phiDefs_disjoint[of ?n g] by auto
    thus ?thesis by (auto simp:step.allDefs_def step.phiDefs_def)
  qed

  lemma oldUses_inv:
    assumes "n \<in> set (\<alpha>n g)"
    shows "oldUses g n = var g ` u_g g n"
  proof-
    have "var g (substitution g) = var g (chooseNext g)" using substitution[of g]
      by - (rule phiArg_same_var, auto simp: isTrivialPhi_def phiArg_def split: option.splits)
    thus ?thesis using assms by (auto simp: substNext_def oldUses_def image_Un)
  qed

  lemma conventional_inv:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "n \<notin> set (tl ns)" "v \<in> step.allDefs g n" "v \<in> step.allUses g m" "x \<in> set (tl ns)" "v' \<in> step.allDefs g x"
    shows "var g v' \<noteq> var g v"
  proof-
    from assms(1,3) have[simp]: "n = defNode g v" "v \<in> allDefs g n" by - (rule defNode_eq[symmetric], auto)
    from assms(1) have[simp]: "m \<in> set (\<alpha>n g)" by auto
    from assms(4) obtain v\<^sub>0 where v\<^sub>0: "v = substNext g v\<^sub>0" "v\<^sub>0 \<in> allUses g m" using allUses_narrows[of m] by auto
    hence[simp]: "v\<^sub>0 \<in> allVars g" using assms(1) by auto
    let ?n\<^sub>0 = "defNode g v\<^sub>0"
    show ?thesis
    proof (cases "v\<^sub>0 = chooseNext g")
      case False
      with v\<^sub>0 have "v = v\<^sub>0" by (simp add:substNext_def split:if_split_asm)
      with assms v\<^sub>0 show ?thesis by - (rule conventional, auto)
    next
      case True
      hence dom: "strict_def_dom g v v\<^sub>0" using substitution[of g] by - (rule trivialPhi_strict_dom, simp_all add:substNext_def v\<^sub>0)
      from v\<^sub>0(2) have "old.dominates g ?n\<^sub>0 m" using assms(1) by - (rule allUses_dominated, auto)
      with assms(1) dom have "?n\<^sub>0 \<in> set ns" by - (rule old.dominates_mid, auto)
      with assms(1) obtain ns\<^sub>1 ns\<^sub>3 ns\<^sub>2 where
        ns: "ns = ns\<^sub>1@ns\<^sub>3@ns\<^sub>2" and
        ns\<^sub>1: "g \<turnstile> n-ns\<^sub>1@[?n\<^sub>0]\<rightarrow>?n\<^sub>0"  "?n\<^sub>0 \<notin> set ns\<^sub>1" and
        ns\<^sub>3: "g \<turnstile> ?n\<^sub>0-ns\<^sub>3\<rightarrow>?n\<^sub>0" and
        ns\<^sub>2: "g \<turnstile> ?n\<^sub>0-?n\<^sub>0#ns\<^sub>2\<rightarrow>m" "?n\<^sub>0 \<notin> set ns\<^sub>2" by (rule old.path2_split_first_last)
      have[simp]: "ns\<^sub>1 \<noteq> []"
      proof
        assume "ns\<^sub>1 = []"
        hence "?n\<^sub>0 = n" "hd ns = n" using assms(1) ns\<^sub>3 by (auto simp:ns old.path2_def)
        thus False by (metis \<open>n = defNode g v\<close> dom)
      qed
      hence "length (ns\<^sub>1@[?n\<^sub>0]) \<ge> 2" by (cases ns\<^sub>1, auto)
      with ns\<^sub>1 have 1: "g \<turnstile> n-ns\<^sub>1\<rightarrow>last ns\<^sub>1" "last ns\<^sub>1 \<in> set (old.predecessors g ?n\<^sub>0)" by - (erule old.path2_unsnoc, simp, simp, erule old.path2_unsnoc, auto)
      from \<open>v\<^sub>0 = chooseNext g\<close> v\<^sub>0 have triv: "isTrivialPhi g v\<^sub>0 v" using substitution[of g] by (auto simp:substNext_def)
      then obtain vs where vs: "phi g v\<^sub>0 = Some vs" "set vs = {v\<^sub>0,v} \<or> set vs = {v}" by (auto simp:isTrivialPhi_def split:option.splits)
      hence[simp]: "var g v\<^sub>0 = var g v" by - (rule phiArg_same_var[symmetric], auto simp: phiArg_def)
      have[simp]: "v \<in> phiUses g (last ns\<^sub>1)"
      proof-
        from vs ns\<^sub>1 1 have "v \<in> phiUses g (last ns\<^sub>1) \<or> v\<^sub>0 \<in> phiUses g (last ns\<^sub>1)" by - (rule phiUses_exI[of "last ns\<^sub>1" g ?n\<^sub>0 v\<^sub>0 vs], auto simp:phi_def)
        moreover have "v\<^sub>0 \<notin> phiUses g (last ns\<^sub>1)"
        proof
          assume asm: "v\<^sub>0 \<in> phiUses g (last ns\<^sub>1)"
          from True have "last ns\<^sub>1 \<in> set ns\<^sub>1" by - (rule last_in_set, auto)
          hence "last ns\<^sub>1 \<in> set (\<alpha>n g)" by - (rule old.path2_in_\<alpha>n[OF ns\<^sub>1(1)], auto)
          with asm ns\<^sub>1 have "old.dominates g ?n\<^sub>0 (last ns\<^sub>1)" by - (rule allUses_dominated, auto)
          moreover have "strict_def_dom g v v\<^sub>0" using triv by - (rule trivialPhi_strict_dom, auto)
          ultimately have "?n\<^sub>0 \<in> set ns\<^sub>1" using 1(1) by - (rule old.dominates_mid, auto)
          with ns\<^sub>1(2) show False ..
        qed
        ultimately show ?thesis by simp
      qed

      show ?thesis
      proof (cases "x \<in> set (tl ns\<^sub>1)")
        case True
        thus ?thesis using assms(2,3,6) by - (rule conventional[where x=x, OF 1(1)], auto simp:ns)
      next
        case False
        show ?thesis
        proof (cases "var g v' = var g v\<^sub>0")
          case [simp]: True
          {
            assume asm: "x \<in> set ns\<^sub>3"
            with assms(6)[THEN allDefs_narrows] have[simp]: "x = defNode g v'"
              using ns\<^sub>3 by - (rule defNode_eq[symmetric], auto)
            {
              assume "v' = v\<^sub>0"
              hence False using assms(6) \<open>v\<^sub>0 = chooseNext g\<close> simpleDefs_phiDefs_disjoint[of x g] vs(1)
                by (auto simp: step.allDefs_def step.phiDefs_def)
            }
            moreover {
              assume "v' \<noteq> v\<^sub>0"
              hence "x \<noteq> ?n\<^sub>0" using allDefs_var_disjoint[OF _ assms(6)[THEN allDefs_narrows], of v\<^sub>0]
                by auto
              from ns\<^sub>3 asm ns obtain ns\<^sub>3 where ns\<^sub>3: "g \<turnstile> ?n\<^sub>0-ns\<^sub>3\<rightarrow>?n\<^sub>0" "?n\<^sub>0 \<notin> set (tl (butlast ns\<^sub>3))" "x \<in> set ns\<^sub>3" "set ns\<^sub>3 \<subseteq> set (tl ns)"
                by - (rule old.path2_simple_loop, auto)
              with \<open>x \<noteq> ?n\<^sub>0\<close> have "length ns\<^sub>3 > 1"
                by (metis empty_iff graph_path_base.path2_def hd_Cons_tl insert_iff length_greater_0_conv length_tl list.set(1) list.set(2) zero_less_diff)
              with ns\<^sub>3 obtain ns' m where ns': "g \<turnstile> ?n\<^sub>0-ns'\<rightarrow>m" "m \<in> set (old.predecessors g ?n\<^sub>0)" "ns' = butlast ns\<^sub>3"
                by - (rule old.path2_unsnoc, auto)
              with vs ns\<^sub>3 have "v \<in> phiUses g m \<or> v\<^sub>0 \<in> phiUses g m"
                by - (rule phiUses_exI[of m g ?n\<^sub>0 v\<^sub>0 vs], auto simp:phi_def)
              moreover {
                assume "v \<in> phiUses g m"
                have "var g v\<^sub>0 \<noteq> var g v"
                proof (rule conventional)
                  show "g \<turnstile> n-ns\<^sub>1 @ ns'\<rightarrow>m" using old.path2_app'[OF ns\<^sub>1(1) ns'(1)] by simp
                  have "n \<notin> set (tl ns\<^sub>1)" using ns assms(2) by auto
                  moreover have "n \<notin> set ns'" using ns'(3) ns\<^sub>3(4) assms(2) by (auto dest: in_set_butlastD)
                  ultimately show "n \<notin> set (tl (ns\<^sub>1 @ ns'))" by simp
                  show "v \<in> allDefs g n" using \<open>v \<in> allDefs g n\<close> .
                  show "?n\<^sub>0 \<in> set (tl (ns\<^sub>1 @ ns'))" using ns'(1) by (auto simp: old.path2_def)
                qed (auto simp: \<open>v \<in> phiUses g m\<close>)
                hence False by simp
              }
              moreover {
                assume "v\<^sub>0 \<in> phiUses g m"
                moreover from ns\<^sub>3(1,3) \<open>x \<noteq> ?n\<^sub>0\<close> \<open>length ns\<^sub>3 > 1\<close> have "x \<in> set (tl (butlast ns\<^sub>3))"
                  by (cases ns\<^sub>3, auto simp: old.path2_def intro: in_set_butlastI)
                ultimately have "var g v' \<noteq> var g v\<^sub>0"
                  using assms(6)[THEN allDefs_narrows] ns\<^sub>3(2,3) ns'(3) by - (rule conventional[OF ns'(1)], auto)
                hence False by simp
              }
              ultimately have False by auto
            }
            ultimately have False by auto
          }
          moreover {
            assume asm: "x \<notin> set ns\<^sub>3"
            have "var g v' \<noteq> var g v\<^sub>0"
            proof (cases "x = ?n\<^sub>0")
              case True
              moreover have "v\<^sub>0 \<notin> step.allDefs g ?n\<^sub>0" by (auto simp:\<open>v\<^sub>0 = chooseNext g\<close> chooseNext_eliminated)
              ultimately show ?thesis using assms(6) vs(1) by - (rule allDefs_var_disjoint[of x g], auto)
            next
              case False
              with \<open>x \<notin> set (tl ns\<^sub>1)\<close> assms(5) asm have "x \<in> set ns\<^sub>2" by (auto simp:ns)
              thus ?thesis using assms(2,6) v\<^sub>0(2) ns\<^sub>2(2) by - (rule conventional[OF ns\<^sub>2(1), where x=x], auto simp:ns)
            qed
          }
          ultimately show ?thesis by auto
        qed auto
      qed
    qed
  qed

  lemma[simp]: "var g (substNext g v) = var g v"
    using substitution[OF redundant]
    by (auto simp:substNext_def isTrivialPhi_def phi_def split:option.splits)

  lemma phis_same_var_inv:
    assumes "phis' g (n,v) = Some vs" "v' \<in> set vs"
    shows "var g v' = var g v"
  proof-
    from assms obtain vs\<^sub>0 v\<^sub>0 where 1: "phis g (n,v) = Some vs\<^sub>0" "v\<^sub>0 \<in> set vs\<^sub>0" "v' = substNext g v\<^sub>0" by (auto split:if_split_asm)
    hence "var g v\<^sub>0 = var g v" by auto
    with 1 show ?thesis by auto
  qed

  lemma allDefs_var_disjoint_inv: "\<lbrakk>n \<in> set (\<alpha>n g); v \<in> step.allDefs g n; v' \<in> step.allDefs g n; v \<noteq> v'\<rbrakk> \<Longrightarrow> var g v' \<noteq> var g v"
    using allDefs_var_disjoint
    by (auto simp:step.allDefs_def)

  lemma step_CFG_SSA_Transformed_notriv: "CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs u_g p_g var chooseNext_all"
  apply unfold_locales
  apply (rule oldDefs_def)
  apply (rename_tac g')
  apply (case_tac "g'=g")
   apply (simp add:oldUses_inv)
   apply (simp add:oldUses_def)
  apply (rename_tac g' n ns m v x v')
  apply (case_tac "g'=g")
   apply (simp add:conventional_inv)
   apply (simp add:conventional[unfolded CFG_SSA_defs, simplified] step.CFG_SSA_defs)
  apply (rename_tac g' n v vs v')
  apply (case_tac "g'=g")
   apply (simp add:phis_same_var_inv)
   apply (simp add:phis_same_var)
  apply (rename_tac g' v v')
  apply (case_tac "g'=g")
   apply (simp add:allDefs_var_disjoint_inv)
   apply (simp add:allDefs_var_disjoint[unfolded allDefs_def phiDefs_def, simplified] step.allDefs_def step.phiDefs_def)
  by (rule chooseNext_all)

  sublocale step: CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" u_g p_g var chooseNext_all
  by (rule step_CFG_SSA_Transformed_notriv)

  lemma step_defNode: "v \<in> allVars g \<Longrightarrow> v \<noteq> chooseNext g \<Longrightarrow> step.defNode g v = defNode g v"
  by (auto simp: step.CFG_SSA_wf_defs dom_def CFG_SSA_wf_defs)

  lemma step_phi: "v \<in> allVars g \<Longrightarrow> v \<noteq> chooseNext g \<Longrightarrow> step.phi g v = map_option (map (substNext g)) (phi g v)"
  by (auto simp: step.phi_def step_defNode phi_def)

  lemma liveVal'_inv:
    assumes "liveVal' g (v#vs)" "v \<noteq> chooseNext g"
    obtains vs' where "step.liveVal' g (v#vs')"
  using assms proof (induction "length vs" arbitrary: v vs rule: nat_less_induct)
    case (1 vs v)
    from "1.prems"(2) show thesis
    proof cases
      case (liveSimple' n)
      with "1.prems"(3) show thesis by - (rule "1.prems"(1), rule step.liveSimple', auto simp: substNext_def)
    next
      case (livePhi' v' vs')
      from this(2) have[simp]: "v' \<in> allVars g" by - (drule liveVal'D, rule, rule liveVal_in_allVars)
      show thesis
      proof (cases "chooseNext g = v'")
        case False
        show thesis
        proof (rule "1.hyps"[rule_format, of "length vs'" vs' v'])
          fix vs'\<^sub>2
          assume asm: "step.liveVal' g (v'#vs'\<^sub>2)"
          have "step.phiArg g v' v" using livePhi'(3) False "1.prems"(3) by (auto simp: step.phiArg_def phiArg_def step_phi substNext_def)
          thus thesis by - (rule "1.prems"(1), rule step.livePhi', rule asm)
        qed (auto simp: livePhi' False[symmetric])
      next
        case [simp]: True
        with "1.prems"(3) have[simp]: "v \<noteq> v'" by simp
        from True have "trivial g v'" using chooseNext[OF redundant] by auto
        with \<open>phiArg g v' v\<close> have "isTrivialPhi g v' v" by (auto simp: phiArg_def trivial_def isTrivialPhi_def)
        hence[simp]: "substitution g = v" unfolding substitution_def
        by - (rule the1_equality, auto intro!: isTrivialPhi_det[unfolded trivial_def])
  
        obtain vs'\<^sub>2 where vs'\<^sub>2: "suffix (v'#vs'\<^sub>2) (v'#vs')" "v' \<notin> set vs'\<^sub>2"
          using split_list_last[of v' "v'#vs'"] by (auto simp: Sublist.suffix_def)
        with \<open>liveVal' g (v'#vs')\<close> have "liveVal' g (v'#vs'\<^sub>2)" by - (rule liveVal'_suffix, simp_all)
        thus thesis
        proof (cases rule: liveVal'.cases)
          case (liveSimple' n)
          hence "v \<in> uses' g n" by (auto simp: substNext_def)
          with liveSimple' show thesis by - (rule "1.prems"(1), rule step.liveSimple', auto)
        next
          case (livePhi' v'' vs'')
          from this(2) have[simp]: "v'' \<in> allVars g" by - (drule liveVal'D, rule, rule liveVal_in_allVars)
          from vs'\<^sub>2(2) livePhi'(1) have[simp]: "v'' \<noteq> v'" by auto
          show thesis
          proof (rule "1.hyps"[rule_format, of "length vs''" vs'' v''])
            show "length vs'' < length vs" using \<open>vs = v'#vs'\<close> livePhi'(1) vs'\<^sub>2(1)[THEN suffix_ConsD2]
              by (auto simp: Sublist.suffix_def)
          next
            fix vs''\<^sub>2
            assume asm: "step.liveVal' g (v''#vs''\<^sub>2)"
            from livePhi' \<open>phiArg g v' v\<close> have "step.phiArg g v'' v" by (auto simp: phiArg_def step.phiArg_def step_phi substNext_def)
            thus thesis by - (rule "1.prems"(1), rule step.livePhi', rule asm)
          qed (auto simp: livePhi'(2))
        qed
      qed
    qed
  qed

  lemma liveVal_inv:
    assumes "liveVal g v" "v \<noteq> chooseNext g"
    shows "step.liveVal g v"
  apply (rule liveVal'I[OF assms(1)])
  apply (erule liveVal'_inv[OF _ assms(2)])
  apply (rule step.liveVal'D)
  by simp_all

  lemma pruned_inv:
    assumes "pruned g"
    shows "step.pruned g"
  proof (rule step.pruned_def[THEN iffD2, rule_format])
    fix n v
    assume "v \<in> step.phiDefs g n" and[simp]: "n \<in> set (\<alpha>n g)"
    hence "v \<in> phiDefs g n" "v \<noteq> chooseNext g" by (auto simp: step.CFG_SSA_defs CFG_SSA_defs split: if_split_asm)
    hence "liveVal g v" using assms by (auto simp: pruned_def)
    thus "step.liveVal g v" using \<open>v \<noteq> chooseNext g\<close> by (rule liveVal_inv)
  qed
end

context CFG_SSA_Transformed_notriv_base
begin
  abbreviation "inst g u p \<equiv> CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs (uses(g:=u)) (phis(g:=p)) var chooseNext_all"
  abbreviation "inst' g \<equiv> \<lambda>(u,p). inst g u p"

  interpretation uninst: CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" u p var chooseNext_all
  for u and p
  by unfold_locales


  definition "cond g \<equiv> \<lambda>(u,p). uninst.redundant (uses(g:=u)) (phis(g:=p)) g"
  definition "step g \<equiv> \<lambda>(u,p). (uninst.uses' (uses(g:=u)) (phis(g:=p)) g,
                                uninst.phis' (uses(g:=u)) (phis(g:=p)) g)"
  definition[code]: "substAll g \<equiv> while (cond g) (step g) (uses g,phis g)"

  definition[code]: "uses'_all g \<equiv> fst (substAll g)"
  definition[code]: "phis'_all g \<equiv> snd (substAll g)"

  lemma uninst_allVars_simps [simp]:
    "uninst.allVars u (\<lambda>_. p g) g = uninst.allVars u p g"
    "uninst.allVars (\<lambda>_. u g) p g = uninst.allVars u p g"
    "uninst.allVars (uses(g:=u g)) p g = uninst.allVars u p g"
    "uninst.allVars u (phis(g:=p g)) g = uninst.allVars u p g"
    unfolding uninst.allVars_def uninst.allDefs_def uninst.allUses_def uninst.phiDefs_def uninst.phiUses_def
  by simp_all

  lemma uninst_trivial_simps [simp]:
    "uninst.trivial u (\<lambda>_. p g) g = uninst.trivial u p g"
    "uninst.trivial (\<lambda>_. u g) p g = uninst.trivial u p g"
    "uninst.trivial (uses(g:=u g)) p g = uninst.trivial u p g"
    "uninst.trivial u (phis(g:=p g)) g = uninst.trivial u p g"
    unfolding uninst.trivial_def [abs_def] uninst.isTrivialPhi_def uninst.phi_def uninst.defNode_code
      uninst.allDefs_def uninst.phiDefs_def
  by simp_all

end

context CFG_SSA_Transformed_notriv
begin
  declare fun_upd_apply[simp del] fun_upd_same[simp]

  lemma substAll_wf:
    assumes[simp]: "redundant g"
    shows "card (dom (phis' g)) < card (dom (phis g))"
  proof (rule psubset_card_mono)
    let ?v = "chooseNext g"
    from chooseNext[of g] obtain n where "(n,?v) \<in> dom (phis g)" by (auto simp: trivial_def isTrivialPhi_def phi_def split:option.splits)
    moreover have "(n,?v) \<notin> dom (phis' g)" by auto
    ultimately have "dom (phis' g) \<noteq> dom (phis g)" by auto
    thus "dom (phis' g) \<subset> dom (phis g)" by (auto split:if_split_asm)
  qed (rule phis_finite)

  lemma step_preserves_inst:
    assumes "inst' g (u,p)"
      and "CFG_SSA_wf_base.redundant \<alpha>n inEdges' defs (uses(g:=u)) (phis(g:=p)) g"
    shows "inst' g (step g (u,p))"
  proof-
    from assms(1) interpret i: CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses(g:=u)" "phis(g:=p)" var
    by simp

    from assms(2) interpret step: CFG_SSA_step \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses(g:=u)" "phis(g:=p)" var chooseNext_all
    by unfold_locales

    show ?thesis using step.step_CFG_SSA_Transformed_notriv[simplified] by (simp add: step_def)
  qed

  lemma substAll:
    assumes "P (uses g, phis g)"
    assumes "\<And>x. P x \<Longrightarrow> inst' g x \<Longrightarrow> cond g x \<Longrightarrow> P (step g x)"
    assumes "\<And>x. P x \<Longrightarrow> inst' g x \<Longrightarrow> \<not>cond g x \<Longrightarrow> Q (fst x) (snd x)"
    shows "inst g (uses'_all g) (phis'_all g)" "Q (uses'_all g) (phis'_all g)"
  proof-
    note uses'_def[simp del]
    note phis'_def[simp del]
    have 2: "\<And>f x. f x = f (fst x, snd x)" by simp

    have "inst' g (substAll g) \<and> Q (uses'_all g) (phis'_all g)" unfolding substAll_def uses'_all_def phis'_all_def
    apply (rule while_rule[where P="\<lambda>x. inst' g x \<and> P x"])
        apply (rule conjI)
         apply (simp, unfold_locales)
        apply (rule assms(1))
       apply (rule conjI)
        apply (clarsimp simp: cond_def step_def)
        apply (rule step_preserves_inst [unfolded step_def, simplified], assumption+)
       proof-
         show "wf {(y,x). (inst' g x \<and> cond g x) \<and> y = step g x}"
         apply (rule wf_if_measure[where f="\<lambda>(u,p). card (dom p)"])
         apply (clarsimp simp: cond_def step_def split:prod.split)
         proof-
           fix u p
           assume "inst g u p"
           then interpret i: CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses(g:=u)" "phis(g:=p)" by simp
           assume "i.redundant g"
           thus "card (dom (i.phis' g)) < card (dom p)" by (rule i.substAll_wf[of g, simplified])
         qed
       qed (auto intro: assms(2,3))
    thus "inst g (uses'_all g) (phis'_all g)" "Q (uses'_all g) (phis'_all g)"
    by (auto simp: uses'_all_def phis'_all_def)
  qed


  sublocale notriv: CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" uses'_all phis'_all
  proof-
    interpret ssa: CFG_SSA \<alpha>e \<alpha>n invar inEdges' Entry "defs" uses'_all phis'_all
    proof
      fix g
      interpret i: CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses(g:=uses'_all g)" "phis(g:=phis'_all g)" var
      by (rule substAll, auto)
      interpret uninst: CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" u p var chooseNext_all
      for u and p
      by unfold_locales

      fix n v args m
      show "finite (defs g n)" by (rule defs_finite)
      show "v \<in> uses'_all g n \<Longrightarrow> n \<in> set (\<alpha>n g)" by (rule i.uses_in_\<alpha>n[of _ g, simplified])
      show "finite (uses'_all g n)" by (rule i.uses_finite[of g, simplified])
      show "invar g" by (rule invar) 
      show "finite (dom (phis'_all g))" by (rule i.phis_finite[of g, simplified])
      show "phis'_all g (n, v) = Some args \<Longrightarrow> n \<in> set (\<alpha>n g)" using i.phis_in_\<alpha>n[of g] by simp
      show "phis'_all g (n, v) = Some args \<Longrightarrow> length (old.predecessors g n) = length args" using i.phis_wf[of g] by simp
      show "n \<in> set (\<alpha>n g) \<Longrightarrow> defs g n \<inter> uninst.phiDefs phis'_all g n = {}" using i.simpleDefs_phiDefs_disjoint[of n g] by (simp add: uninst.CFG_SSA_defs)
      show "n \<in> set (\<alpha>n g) \<Longrightarrow> m \<in> set (\<alpha>n g) \<Longrightarrow> n \<noteq> m \<Longrightarrow> uninst.allDefs phis'_all g n \<inter> uninst.allDefs phis'_all g m = {}"
      using i.allDefs_disjoint[of n g] by (simp add: uninst.CFG_SSA_defs)
      show "n \<in> set (\<alpha>n g) \<Longrightarrow> defs g n \<inter> uses'_all g n = {}" using i.defs_uses_disjoint[of n g] by simp
    qed
    interpret uninst: CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" u p var chooseNext_all
    for u and p
    by unfold_locales

    show "CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs uses'_all phis'_all var"
    proof
      fix g n v ns m x v' vs
      interpret i: CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses(g:=uses'_all g)" "phis(g:=phis'_all g)" var
      by (rule substAll, auto)
      show "oldDefs g n = var g ` defs g n" by (rule oldDefs_def)
      show "n \<in> set (\<alpha>n g) \<Longrightarrow> oldUses g n = var g ` uses'_all g n" using i.oldUses_def[of n g] by simp
      show "v \<in> ssa.allUses g n \<Longrightarrow> n \<in> set (\<alpha>n g) \<Longrightarrow> ssa.defAss g n v" using i.allUses_def_ass[of v g n] by (simp add: uninst.CFG_SSA_defs)
      show "old.path2 g n ns m \<Longrightarrow> n \<notin> set (tl ns) \<Longrightarrow> v \<in> ssa.allDefs g n \<Longrightarrow> v \<in> ssa.allUses g m \<Longrightarrow> x \<in> set (tl ns) \<Longrightarrow> v' \<in> ssa.allDefs g x \<Longrightarrow> var g v' \<noteq> var g v" using i.conventional[of g n ns m v x v'] by (simp add: uninst.CFG_SSA_defs)
      show "phis'_all g (n, v) = Some vs \<Longrightarrow> v' \<in> set vs \<Longrightarrow> var g v' = var g v" using i.phis_same_var[of g n v] by simp
      show "n \<in> set (\<alpha>n g) \<Longrightarrow> v \<in> ssa.allDefs g n \<Longrightarrow> v' \<in> ssa.allDefs g n \<Longrightarrow> v \<noteq> v' \<Longrightarrow> var g v' \<noteq> var g v" using i.allDefs_var_disjoint by (simp add: uninst.CFG_SSA_defs)
      show "phis'_all g (Entry g, v) = None" using i.Entry_no_phis[of g v] by simp
    qed
  qed

  theorem not_redundant: "\<not>notriv.redundant g"
  proof-
    interpret uninst: CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" u p var chooseNext_all
    for u and p
    by unfold_locales

    have 1: "\<And>u p. uninst.redundant (uses(g:=u g)) (phis(g:=p g)) g \<longleftrightarrow> uninst.redundant u p g"
      by (simp add: uninst.CFG_SSA_wf_defs)
    show ?thesis
      by (rule substAll(2)[where Q="\<lambda>u p. \<not>uninst.redundant (uses(g:=u)) (phis(g:=p)) g" and P="\<lambda>_. True" and g=g, simplified cond_def substAll_def 1], auto)
  qed

  corollary minimal: "old.reducible g \<Longrightarrow> notriv.cytronMinimal g"
  by (erule notriv.reducible_nonredundant_imp_minimal, rule not_redundant)

  theorem pruned_invariant:
    assumes "pruned g"
    shows "notriv.pruned g"
  proof-
    {
      fix u p
      assume "inst g u p"
      then interpret i: CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses(g:=u)" "phis(g:=p)" var chooseNext_all
      by simp

      assume "i.redundant g"
      then interpret i: CFG_SSA_step \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses(g:=u)" "phis(g:=p)" var chooseNext_all g
      by unfold_locales

      interpret uninst: CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" u p var chooseNext_all
      for u and p
      by unfold_locales

      assume "i.pruned g" 
      hence "uninst.pruned (uses(g:=i.uses' g)) (phis(g:=i.phis' g)) g"
        by (rule i.pruned_inv[simplified])
    }
    note 1 = this

    interpret uninst: CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" u p var chooseNext_all
    for u and p
    by unfold_locales

    have 2: "\<And>u u' p p' g. uninst.pruned (u'(g:=u g)) (p'(g:=p g)) g \<longleftrightarrow> uninst.pruned u p g"
    by (clarsimp simp: uninst.CFG_SSA_wf_defs)

    from 1 assms show ?thesis
    by - (rule substAll(2)[where P="\<lambda>(u,p). uninst.pruned (uses(g:=u)) (phis(g:=p)) g" and Q="\<lambda>u p. uninst.pruned (uses(g:=u)) (phis(g:=p)) g" and g=g, simplified 2],
          auto simp: cond_def step_def)
  qed
end

end
