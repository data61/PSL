(*  Title:      Construct_SSA_notriv_code.thy
    Author:     Denis Lohner, Sebastian Ullrich
*)

subsection \<open>Code Equations for SSA Minimization\<close>

theory Construct_SSA_notriv_code imports
  SSA_CFG_code
  Construct_SSA_notriv
  While_Combinator_Exts
begin

abbreviation (input) "const x \<equiv> (\<lambda>_. x)"

context CFG_SSA_Transformed_notriv_base begin
  definition [code]: "substitution_code g next = the (the_trivial (snd next) (the (phis g next)))"
  definition [code]: "substNext_code g next \<equiv> \<lambda>v. if v = snd next then substitution_code g next else v"
  definition [code]: "uses'_code g next n \<equiv> substNext_code g next ` uses g n"

  lemma substNext_code_alt_def:
    "substNext_code g next = id(snd next := substitution_code g next)"
    unfolding substNext_code_def by auto
end

type_synonym ('g, 'node, 'val) chooseNext_code = "('node \<Rightarrow> 'val set) \<Rightarrow> ('node, 'val) phis_code \<Rightarrow> 'g \<Rightarrow> ('node \<times> 'val)"

locale CFG_SSA_Transformed_notriv_base_code =
  ssa:CFG_SSA_wf_base_code \<alpha>e \<alpha>n invar inEdges' Entry "defs" "uses" phis +
  CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "usesOf \<circ> uses" "\<lambda>g. Mapping.lookup (phis g)" var "\<lambda>uses phis. chooseNext_all uses (Mapping.Mapping phis)"
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  oldDefs :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> ('node, 'val set) mapping" and
  phis :: "'g \<Rightarrow> ('node, 'val) phis_code" and
  var :: "'g \<Rightarrow> 'val \<Rightarrow> 'var" and
  chooseNext_all :: "('g, 'node, 'val) chooseNext_code"
begin
  definition [code]: "cond_code g = ssa.redundant_code g"

  definition uses'_codem :: "'g \<Rightarrow> 'node \<times> 'val \<Rightarrow> 'val \<Rightarrow> ('val, 'node set) mapping \<Rightarrow> ('node, 'val set) mapping"
  where [code]: "uses'_codem g next next' nodes_of_uses =
    fold (\<lambda>n. Mapping.update n (Set.insert next' (Set.remove (snd next) (the (Mapping.lookup (uses g) n)))))
      (sorted_list_of_set (case_option {} id (Mapping.lookup nodes_of_uses (snd next))))
      (uses g)"

  definition nodes_of_uses' :: "'g \<Rightarrow> 'node \<times> 'val \<Rightarrow> 'val \<Rightarrow> 'val set \<Rightarrow> ('val, 'node set) mapping \<Rightarrow> ('val, 'node set) mapping"
  where [code]: "nodes_of_uses' g next next' phiVals nodes_of_uses =
    (let users = case_option {} id (Mapping.lookup nodes_of_uses (snd next))
    in
    if (next' \<in> phiVals) then Mapping.map_default next' {} (\<lambda>ns. ns \<union> users) (Mapping.delete (snd next) nodes_of_uses)
    else Mapping.delete (snd next) nodes_of_uses)"

  (* FIXME: phis'_code ist in O(n) \<rightarrow> verwende nodes_of_uses ? *)
  definition [code]: "phis'_code g next \<equiv> map_values (\<lambda>(n,v) vs. if v = snd next then None else Some (map (substNext_code g next) vs)) (phis g)"

  (* Schon besser: O(log(n)) *)
  definition [code]: "phis'_codem g next next' nodes_of_phis =
    fold (\<lambda>n. Mapping.update n (List.map (id(snd next := next')) (the (Mapping.lookup (phis g) n))))
      (sorted_list_of_set (case_option {} (Set.remove next) (Mapping.lookup nodes_of_phis (snd next))))
      (Mapping.delete next (phis g))"

  definition nodes_of_phis' :: "'g \<Rightarrow> 'node \<times> 'val \<Rightarrow> 'val \<Rightarrow> ('val, ('node \<times> 'val) set) mapping \<Rightarrow> ('val, ('node \<times> 'val) set) mapping"
  where [code]: "nodes_of_phis' g next next' nodes_of_phis =
      (let old_phis = Set.remove next (case_option {} id (Mapping.lookup nodes_of_phis (snd next)));
        nop = Mapping.delete (snd next) nodes_of_phis
      in
      Mapping.map_default next' {} (\<lambda>ns. (Set.remove next ns) \<union> old_phis) nop)"

  definition [code]: "triv_phis' g next triv_phis nodes_of_phis
    = (Set.remove next triv_phis) \<union> (Set.filter (\<lambda>n. ssa.trivial_code (snd n) (the (Mapping.lookup (phis g) n))) (case_option {} (Set.remove next) (Mapping.lookup nodes_of_phis (snd next))))"

  definition [code]: "step_code g = (let next = chooseNext' g in (uses'_code g next, phis'_code g next))"
  definition [code]: "step_codem g next next' nodes_of_uses nodes_of_phis = (uses'_codem g next next' nodes_of_uses, phis'_codem g next next' nodes_of_phis)"

  definition phi_equiv_mapping :: "'g \<Rightarrow> ('val, 'a set) mapping \<Rightarrow> ('val, 'a set) mapping \<Rightarrow> bool" ("_ \<turnstile> _ \<approx>\<^sub>\<phi> _" 50)
    where "g \<turnstile> nou\<^sub>1 \<approx>\<^sub>\<phi> nou\<^sub>2 \<equiv> \<forall>v \<in> Mapping.keys (ssa.phidefNodes g). case_option {} id (Mapping.lookup nou\<^sub>1 v) = case_option {} id (Mapping.lookup nou\<^sub>2 v)"
end

locale CFG_SSA_Transformed_notriv_linorder = CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
   + CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
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
  var :: "'g \<Rightarrow> 'val \<Rightarrow> 'var" and
  chooseNext_all :: "('node \<Rightarrow> 'val set) \<Rightarrow> ('node, 'val) phis \<Rightarrow> 'g \<Rightarrow> ('node \<times> 'val)"
begin
  lemma isTrivial_the_trivial: "\<lbrakk> phi g v = Some vs; isTrivialPhi g v v' \<rbrakk> \<Longrightarrow> the_trivial v vs = Some v'"
    by (subst the_trivialI [of vs v v']) (auto simp: isTrivialPhi_def)

  lemma the_trivial_THE_isTrivial: "\<lbrakk> phi g v = Some vs; trivial g v \<rbrakk> \<Longrightarrow> the_trivial v vs = Some (The (isTrivialPhi g v))"
    apply (frule isTrivialPhi_det)
    apply clarsimp
    apply (frule(1) isTrivial_the_trivial)
    by (auto dest: isTrivial_the_trivial intro!: the_equality intro: sym)

  lemma substitution_code_correct:
    assumes "redundant g"
    shows "substitution g = substitution_code g (chooseNext' g)"
  proof -
    from substitution [OF assms] have "phi g (chooseNext g) \<noteq> None"
      unfolding isTrivialPhi_def by (clarsimp split: option.splits)
    then obtain vs where "phi g (chooseNext g) = Some vs" by blast
    with isTrivial_the_trivial [OF this substitution [OF assms]] chooseNext'[OF assms]
    show ?thesis unfolding substitution_code_def by (auto simp: phis_phi[of g "fst (chooseNext' g)"])
  qed

  lemma substNext_code_correct:
    assumes "redundant g"
    shows "substNext g = substNext_code g (chooseNext' g)"
    unfolding substNext_def [abs_def] substNext_code_def
    by (auto simp: substitution_code_correct [OF assms])

  lemma uses'_code_correct:
    assumes "redundant g"
    shows "uses' g = uses'_code g (chooseNext' g)"
    unfolding uses'_def [abs_def] uses'_code_def [abs_def]
    by (auto simp: substNext_code_correct [OF assms])

end

context CFG_SSA_Transformed_notriv_linorder
begin
  lemma substAll_terminates: "while_option (cond g) (step g) (uses g, phis g) \<noteq> None"
  apply (rule notI)
  apply (rule while_option_None_invD [where I="inst' g" and r="{(y,x). (inst' g x \<and> cond g x) \<and> y = step g x}"], assumption)
     apply (rule wf_if_measure[where f="\<lambda>(u,p). card (dom p)"])
     defer
     apply simp
     apply unfold_locales
    apply (case_tac s)
    apply (simp add: step_def cond_def)
    apply (rule step_preserves_inst [unfolded step_def, simplified], assumption+)
   apply (simp add: step_def cond_def)
  apply (clarsimp simp: cond_def step_def split:prod.split)
  proof-
    fix u p
    assume "CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs (uses(g:=u)) (phis(g:=p)) var chooseNext_all"
    then interpret i: CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses(g:=u)" "phis(g:=p)" var chooseNext_all .
    assume "i.redundant g"
    thus "card (dom (i.phis' g)) < card (dom p)" by (rule i.substAll_wf[of g, simplified])
  qed
end

locale CFG_SSA_Transformed_notriv_linorder_code =
  CFG_SSA_Transformed_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var
+ CFG_SSA_Transformed_notriv_base_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
+ CFG_SSA_Transformed_notriv_linorder \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "usesOf \<circ> uses" "\<lambda>g. Mapping.lookup (phis g)" var
  "\<lambda>uses phis. chooseNext_all uses (Mapping.Mapping phis)"
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  oldDefs :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> ('node, 'val set) mapping" and
  phis :: "'g \<Rightarrow> ('node, 'val) phis_code" and
  var :: "'g \<Rightarrow> 'val \<Rightarrow> 'var" and
  chooseNext_all :: "('g, 'node, 'val) chooseNext_code"
+
assumes chooseNext_all_code:
  "CFG_SSA_Transformed_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs u p var \<Longrightarrow>
  CFG_SSA_wf_base_code.redundant_code p g \<Longrightarrow>
  chooseNext_all (usesOf (u g)) (p g) g = Max (CFG_SSA_wf_base_code.trivial_phis p g)"

locale CFG_SSA_step_code =
  step_code: CFG_SSA_Transformed_notriv_linorder_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
+
  CFG_SSA_step \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "usesOf \<circ> uses" "\<lambda>g. Mapping.lookup (phis g)" var "\<lambda>uses phis. chooseNext_all uses (Mapping.Mapping phis)" g
for
  \<alpha>e :: "'g \<Rightarrow> ('node::linorder \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry::"'g \<Rightarrow> 'node" and
  oldDefs :: "'g \<Rightarrow> 'node \<Rightarrow> 'var::linorder set" and
  oldUses :: "'g \<Rightarrow> 'node \<Rightarrow> 'var set" and
  "defs" :: "'g \<Rightarrow> 'node \<Rightarrow> 'val::linorder set" and
  "uses" :: "'g \<Rightarrow> ('node, 'val set) mapping" and
  phis :: "'g \<Rightarrow> ('node, 'val) phis_code" and
  var :: "'g \<Rightarrow> 'val \<Rightarrow> 'var" and
  chooseNext_all :: "('g, 'node, 'val) chooseNext_code" and
  g :: 'g

context CFG_SSA_Transformed_notriv_linorder_code
begin
  abbreviation "u_g g u \<equiv> uses(g:=u)"
  abbreviation "p_g g p \<equiv> phis(g:=p)"
  abbreviation "cN \<equiv> (\<lambda>uses phis. chooseNext_all uses (Mapping.Mapping phis))"

  interpretation uninst_code: CFG_SSA_Transformed_notriv_base_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" u p var chooseNext_all
    for u p
  by unfold_locales

  interpretation uninst: CFG_SSA_Transformed_notriv_base \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" u p var cN
    for u p
  by unfold_locales

  lemma phis'_code_correct:
    assumes "ssa.redundant g"
    shows "phis' g = Mapping.lookup (phis'_code g (chooseNext' g))"
  unfolding phis'_def [abs_def] phis'_code_def [abs_def]
  by (auto simp: Mapping_lookup_map_values substNext_code_correct [OF assms] split: if_split Option.bind_split)

  lemma redundant_ign[simp]: "uninst_code.ssa.redundant_code (const p) g = uninst_code.ssa.redundant_code (phis(g:=p)) g"
  unfolding uninst_code.ssa.redundant_code_def uninst_code.ssa.trivial_code_def[abs_def] CFG_SSA_wf_base.CFG_SSA_wf_defs uninst_code.ssa.trivial_phis_def
  unfolding fun_upd_same
  ..

  lemma uses'_ign[simp]: "uninst_code.uses'_codem (const u) g = uninst_code.uses'_codem (u_g g u) g"
  unfolding uninst_code.uses'_codem_def[abs_def] uninst.substNext_code_def uninst.substitution_code_def uninst_code.ssa.trivial_code_def[abs_def] CFG_SSA_wf_base.CFG_SSA_wf_defs
    uninst.uses'_code_def[abs_def]
  by simp

  lemma phis'_ign[simp]: "uninst_code.phis'_code (const p) g = uninst_code.phis'_code (phis(g:=p)) g"
  unfolding uninst_code.phis'_code_def[abs_def] uninst.substNext_code_def uninst.substitution_code_def uninst_code.ssa.trivial_code_def[abs_def] CFG_SSA_wf_base.CFG_SSA_wf_defs
  unfolding fun_upd_same
  ..

  lemma phis'm_ign[simp]: "uninst_code.phis'_codem (const p) g = uninst_code.phis'_codem (phis(g:=p)) g"
  unfolding uninst_code.phis'_codem_def[abs_def] uninst.substNext_code_def uninst.substitution_code_def uninst_code.ssa.trivial_code_def[abs_def] CFG_SSA_wf_base.CFG_SSA_wf_defs
  unfolding fun_upd_same
  ..

  lemma set_sorted_list_of_set_phis_dom [simp]:
  "set (sorted_list_of_set {x \<in> dom (Mapping.lookup (phis g)). P x}) = {x \<in> dom (Mapping.lookup (phis g)). P x}"
  apply (subst set_sorted_list_of_set)
  by (rule finite_subset [OF _ ssa.phis_finite [of g]]) auto

  lemma phis'_codem_correct:
    assumes "g \<turnstile> nodes_of_phis \<approx>\<^sub>\<phi> (ssa.phiNodes_of g)" and "next \<in> Mapping.keys (phis g)"
    shows "phis'_codem g next (substitution_code g next) nodes_of_phis = phis'_code g next"
  proof -
    from assms
    have "phis'_code g next = mmap (map (substNext_code g next)) (Mapping.delete next (phis g))"
      unfolding phis'_code_def mmap_def phi_equiv_mapping_def
    apply (subst mapping_eq_iff)
    by (auto simp: Mapping_lookup_map_values Mapping_lookup_map Option.bind_def map_option_case lookup_delete keys_dom_lookup
      dest: ssa.phis_disj [where n="fst next" and v="snd next", simplified] split: option.splits)

    also from assms have "... = phis'_codem g next (substitution_code g next) nodes_of_phis"
      unfolding phis'_codem_def mmap_def ssa.lookup_phiNodes_of [OF ssa.phis_finite] phi_equiv_mapping_def
    apply (subst mapping_eq_iff)
    apply (simp add: Mapping_lookup_map lookup_delete map_option_case)
    by (erule_tac x="next" in ballE)
    (force intro!: map_idI
      simp: substNext_code_def keys_dom_lookup fun_upd_apply
      split: option.splits if_splits)+
    finally show ?thesis ..
  qed

  lemma uses_transfer [transfer_rule]: "(rel_fun (=) (pcr_mapping (=) (=))) (\<lambda>g n. Mapping.lookup (uses g) n) uses"
    by (auto simp: mapping.pcr_cr_eq cr_mapping_def Mapping.lookup.rep_eq)

  lemma uses'_codem_correct:
  assumes "g \<turnstile> nodes_of_uses \<approx>\<^sub>\<phi> ssa.useNodes_of g" and "next \<in> Mapping.keys (phis g)"
  shows "usesOf (uses'_codem g next (substitution_code g next) nodes_of_uses) = uses'_code g next"
  using dom_uses_in_graph [of g] assms
  unfolding uses'_codem_def uses'_code_def [abs_def]
  apply (clarsimp simp: mmap_def Mapping.replace_def [abs_def] phi_equiv_mapping_def intro!: ext)
  apply (transfer' fixing: g)
  apply (subgoal_tac "\<And>b. finite
             {n. (\<exists>y. Mapping.lookup (uses g) n = Some y) \<and>
                 (\<forall>x2. Mapping.lookup (uses g) n = Some x2 \<longrightarrow> n \<in> set (\<alpha>n g) \<and> b \<in> x2)}")
   prefer 2
   apply (rule finite_subset [where B="set (\<alpha>n g)"])
    apply (clarsimp simp: Mapping.keys_dom_lookup)
   apply simp
  by (auto simp: map_of_map_restrict restrict_map_def substNext_code_def fold_update_conv Mapping.keys_dom_lookup
    split: option.splits)

  lemma step_ign[simp]: "uninst_code.step_codem (const u) (const p) g = uninst_code.step_codem (u_g g u) (phis(g:=p)) g"
  by (rule ext)+ (simp add: uninst_code.step_codem_def Let_def)

  lemma cN_transfer [transfer_rule]: "(rel_fun (=) (rel_fun (pcr_mapping (=) (=)) (=))) cN chooseNext_all"
    by (auto simp: rel_fun_def mapping.pcr_cr_eq cr_mapping_def mapping.rep_inverse)

  lemma usesOf_transfer [transfer_rule]: "(rel_fun (pcr_mapping (=) (=)) (=)) (\<lambda>m x. case_option {} id (m x))  usesOf"
    by (auto simp: rel_fun_def mapping.pcr_cr_eq cr_mapping_def Mapping.lookup.rep_eq)

  lemma dom_phis'_codem:
  assumes "\<And>ns. Mapping.lookup nodes_of_phis (snd next) = Some ns \<Longrightarrow> finite ns"
  shows "dom (Mapping.lookup (phis'_codem g next next' nodes_of_phis)) = dom (Mapping.lookup (phis g)) \<union> (case_option {} id (Mapping.lookup nodes_of_phis (snd next))) - {next}"
    using assms unfolding phis'_codem_def
    by (auto split: if_splits option.splits  simp: lookup_delete)

  lemma dom_phis'_code [simp]:
  shows "dom (Mapping.lookup (phis'_code g next)) = dom (Mapping.lookup (phis g)) - {v. snd v = snd next}"
    by (auto simp: phis'_code_def Mapping_lookup_map_values bind_eq_Some_conv)

  lemma nodes_of_phis_finite [simplified]:
  assumes "g \<turnstile> nodes_of_phis \<approx>\<^sub>\<phi> ssa.phiNodes_of g" and "Mapping.lookup nodes_of_phis v = Some ns" and "v \<in> Mapping.keys (ssa.phidefNodes g)"
  shows "finite ns"
  using assms unfolding phi_equiv_mapping_def
    by (erule_tac x=v in ballE) (auto intro: finite_subset [OF _ ssa.phis_finite [of g]])

  lemma lookup_phis'_codem_next:
  assumes "\<And>ns. Mapping.lookup nodes_of_phis (snd next) = Some ns \<Longrightarrow> finite ns"
  shows "Mapping.lookup (phis'_codem g next next' nodes_of_phis) next = None"
    using assms unfolding phis'_codem_def
    by (auto simp: Set.remove_def lookup_delete split: option.splits)

  lemma lookup_phis'_codem_other:
  assumes "g \<turnstile> nodes_of_phis \<approx>\<^sub>\<phi> (ssa.phiNodes_of g)"
  and "next \<in> Mapping.keys (phis g)" and "next \<noteq> \<phi>"
  shows "Mapping.lookup (phis'_codem g next (substitution_code g next) nodes_of_phis) \<phi> =
    map_option (map (substNext_code g next)) (Mapping.lookup (phis g) \<phi>)"
  proof (cases "snd next \<noteq> snd \<phi>")
    case True
    with assms(1,2) show ?thesis
      unfolding phis'_codem_correct [OF assms(1,2)] phis'_code_def
      using assms(3)
      by (auto intro!: map_idI [symmetric] simp: Mapping_lookup_map_values substNext_code_def lookup_delete map_option_case split: option.splits prod.splits)
  next
    case False
    hence "snd next = snd \<phi>" by simp
    with assms(3) have "fst next \<noteq> fst \<phi>" by (cases "next", cases \<phi>) auto
    with assms(2) False have [simp]: "Mapping.lookup (phis g) \<phi> = None"
      by (cases \<phi>, cases "next") (fastforce simp: keys_dom_lookup dest: ssa.phis_disj)
    from \<open>fst next \<noteq> fst \<phi>\<close> \<open>snd next = snd \<phi>\<close> show ?thesis
    unfolding phis'_codem_correct [OF assms(1,2)] phis'_code_def
      by (auto simp: Mapping_lookup_map_values lookup_delete map_option_case substNext_code_def split: option.splits)
  qed

  lemma lookup_nodes_of_phis'_subst [simp]:
  "Mapping.lookup (nodes_of_phis' g next (substitution_code g next) nodes_of_phis) (substitution_code g next) =
    Some ((case_option {} (Set.remove next) (Mapping.lookup nodes_of_phis (substitution_code g next))) \<union> (case_option {} (Set.remove next) (Mapping.lookup nodes_of_phis (snd next))))"
  unfolding nodes_of_phis'_def
    by (clarsimp simp: Mapping_lookup_map_default Set.remove_def lookup_delete split: option.splits)

  lemma lookup_nodes_of_phis'_not_subst:
  "v \<noteq> substitution_code g next \<Longrightarrow>
  Mapping.lookup (nodes_of_phis' g next (substitution_code g next) nodes_of_phis) v = (if v = snd next then None else Mapping.lookup nodes_of_phis v)"
  unfolding nodes_of_phis'_def
    by (clarsimp simp: Mapping_lookup_map_default lookup_delete)

  lemma lookup_phis'_code:
  "Mapping.lookup (phis'_code g next) v = (if snd v = snd next then None else map_option (map (substNext_code g next)) (Mapping.lookup (phis g) v))"
    unfolding phis'_code_def
    by (auto simp: Mapping_lookup_map_values bind_eq_None_conv map_conv_bind_option comp_def split: prod.splits)

  lemma phi_equiv_mappingE':
    assumes "g \<turnstile> m\<^sub>1 \<approx>\<^sub>\<phi> ssa.phiNodes_of g"
    and "Mapping.lookup (phis g) x = Some vs" and "b \<in> set vs" and "b \<in> snd ` Mapping.keys (phis g)"
    obtains "Mapping.lookup m\<^sub>1 b = Some {n \<in> Mapping.keys (phis g). b \<in> set (the (Mapping.lookup (phis g) n))}"
    using assms unfolding phi_equiv_mapping_def
    apply (auto split: option.splits if_splits)
    apply (clarsimp simp: keys_dom_lookup)
    apply (rename_tac n \<phi>_args)
    apply (erule_tac x="(n,b)" in ballE)
     prefer 2 apply auto[1]
    by (cases x) force

  lemma phi_equiv_mappingE:
    assumes "g \<turnstile> m\<^sub>1 \<approx>\<^sub>\<phi> ssa.phiNodes_of g" and "b \<in> Mapping.keys (phis g)"
    and "Mapping.lookup (phis g) x = Some vs" and "snd b \<in> set vs"
    obtains ns where "Mapping.lookup m\<^sub>1 (snd b) = Some {n \<in> Mapping.keys (phis g). snd b \<in> set (the (Mapping.lookup (phis g) n))}"
  proof -
    from assms(2) have "snd b \<in> snd ` Mapping.keys (phis g)" by simp
    with assms(1,3,4) show ?thesis
    by (rule phi_equiv_mappingE') (rule that)
  qed

  lemma phi_equiv_mappingE2':
    assumes "g \<turnstile> m\<^sub>1 \<approx>\<^sub>\<phi> ssa.phiNodes_of g"
    and "b \<in> snd ` Mapping.keys (phis g)"
    and "\<forall>\<phi> \<in> Mapping.keys (phis g). b \<notin> set (the (Mapping.lookup (phis g) \<phi>))"
    shows "Mapping.lookup m\<^sub>1 b = None \<or> Mapping.lookup m\<^sub>1 b = Some {}"
    using assms unfolding phi_equiv_mapping_def
    apply (auto split: option.splits if_splits)
    apply (clarsimp simp: keys_dom_lookup)
    apply (rename_tac n \<phi>_args)
    apply (erule_tac x="(n,b)" in ballE)
     prefer 2 apply auto[1]
    by (cases "Mapping.lookup m\<^sub>1 b"; auto)

  lemma keys_phis'_codem [simp]: "Mapping.keys (phis'_codem g next next' (ssa.phiNodes_of g)) = Mapping.keys (phis g) - {next}"
    unfolding phis'_codem_def
  by (auto simp: keys_dom_lookup fun_upd_apply lookup_delete split: option.splits if_splits)

  lemma keys_phis'_codem':
    assumes "g \<turnstile> nodes_of_phis \<approx>\<^sub>\<phi> ssa.phiNodes_of g" and "next \<in> Mapping.keys (phis g)"
    shows "Mapping.keys (phis'_codem g next next' nodes_of_phis) = Mapping.keys (phis g) - {next}"
    using assms unfolding phis'_codem_def phi_equiv_mapping_def ssa.keys_phidefNodes [OF ssa.phis_finite]
  by (force split: option.splits if_splits simp: fold_update_conv fun_upd_apply keys_dom_lookup lookup_delete)

  lemma triv_phis'_correct:
    assumes "g \<turnstile> nodes_of_phis \<approx>\<^sub>\<phi> ssa.phiNodes_of g" and "next \<in> Mapping.keys (phis g)" and "ssa.trivial g (snd next)"
    shows "uninst_code.triv_phis' (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g next (ssa.trivial_phis g) nodes_of_phis = uninst_code.ssa.trivial_phis (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g"
  proof (rule set_eqI)
    note keys_phis'_codem' [OF assms(1,2), simp]
    fix \<phi>

    from assms(2,3) ssa.phis_in_\<alpha>n [of g "fst next" "snd next"]
    have "ssa.redundant g"
      unfolding ssa.redundant_def ssa.allVars_def ssa.allDefs_def ssa.phiDefs_def
      by (cases "next") (auto simp: keys_dom_lookup)

    then interpret step: CFG_SSA_step_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
      by unfold_locales

    let ?u_g = "\<lambda>g. Mapping.Mapping (\<lambda>n. if step.u_g g n = {} then None else Some (step.u_g g n))"
    let ?p_g = "\<lambda>g. Mapping.Mapping (step.p_g g)"

    have u_g_is_u_g: "usesOf \<circ> ?u_g = step.u_g"
      by (subst usesOf_def [abs_def]) (intro ext; auto)
    have p_g_is_p_g: "(\<lambda>g. Mapping.lookup (?p_g g)) = step.p_g" by simp

    interpret step: CFG_SSA_wf_code \<alpha>e \<alpha>n invar inEdges' Entry "defs" "\<lambda>g. Mapping.Mapping (\<lambda>n. if step.u_g g n = {} then None else Some (step.u_g g n))" "\<lambda>g. Mapping.Mapping (step.p_g g)"
      apply (intro CFG_SSA_wf_code.intro CFG_SSA_code.intro)
      unfolding u_g_is_u_g p_g_is_p_g by intro_locales

    show "\<phi> \<in> uninst_code.triv_phis' (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g next (ssa.trivial_phis g) nodes_of_phis \<longleftrightarrow> \<phi> \<in> uninst_code.ssa.trivial_phis (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g"
    proof (cases "\<phi> = next")
      case True
      hence "\<phi> \<notin> uninst_code.triv_phis' (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g next (ssa.trivial_phis g) nodes_of_phis"
        unfolding uninst_code.triv_phis'_def by (auto split: option.splits)
      moreover
      from True have "\<phi> \<notin> Mapping.keys (phis'_codem g next (substitution_code g next) nodes_of_phis)"
        unfolding phis'_codem_def
        by (transfer fixing: nodes_of_phis "next") (auto simp: fold_update_conv split: if_splits option.splits)
      hence "\<phi> \<notin> uninst_code.ssa.trivial_phis (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g"
        unfolding uninst_code.ssa.trivial_phis_def by simp
      ultimately show ?thesis by simp
    next
      case False
      show ?thesis
      proof (cases "Mapping.lookup nodes_of_phis (snd next)")
        case None
        hence "uninst_code.triv_phis' (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g next (ssa.trivial_phis g) nodes_of_phis = ssa.trivial_phis g - {next}"
          unfolding uninst_code.triv_phis'_def by auto
        moreover from None
        have "uninst_code.ssa.trivial_phis (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g = ssa.trivial_phis g - {next}"
          unfolding phis'_codem_def uninst_code.ssa.trivial_phis_def by (auto simp: lookup_delete)
        ultimately show ?thesis by simp
      next
        case [simp]: (Some nodes)
        from assms(2) have "snd next \<in> snd ` dom (Mapping.lookup (phis g))" by (auto simp: keys_dom_lookup)
        with assms(1) Some have "finite nodes" by (rule nodes_of_phis_finite)
        hence [simp]: "set (sorted_list_of_set nodes) = nodes" by simp
        obtain \<phi>_node \<phi>_val where [simp]: "\<phi> = (\<phi>_node, \<phi>_val)" by (cases \<phi>) auto
        show ?thesis
        proof (cases "\<phi> \<in> nodes")
          case False
          with \<open>\<phi> \<noteq> next\<close> have "\<phi> \<in> uninst_code.triv_phis' (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g next (ssa.trivial_phis g) nodes_of_phis \<longleftrightarrow> \<phi> \<in> ssa.trivial_phis g"
            unfolding uninst_code.triv_phis'_def by simp
          moreover

          from False \<open>\<phi> \<noteq> next\<close> have "... \<longleftrightarrow> \<phi> \<in> uninst_code.ssa.trivial_phis (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g"
            unfolding phis'_codem_def uninst_code.ssa.trivial_phis_def
            by (auto simp add: keys_dom_lookup dom_def lookup_delete)
          ultimately show ?thesis by simp
        next
          case True
          with assms(1,2) have "\<phi> \<in> Mapping.keys (phis g)"
            unfolding phi_equiv_mapping_def apply clarsimp
            apply (clarsimp simp: keys_dom_lookup)
            by (erule_tac x="next" in ballE) (auto split: option.splits if_splits)

          then obtain \<phi>_args where [simp]: "Mapping.lookup (phis g) (\<phi>_node, \<phi>_val) = Some \<phi>_args"
            unfolding keys_dom_lookup by auto
          hence [simp]: "ssa.phi g \<phi>_val = Some \<phi>_args"
            by (rule ssa.phis_phi)

          from True \<open>\<phi> \<noteq> next\<close> have "\<phi> \<in> uninst_code.triv_phis' (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g next (ssa.trivial_phis g) nodes_of_phis \<longleftrightarrow>
            \<phi> \<in> ssa.trivial_phis g \<or> ssa.trivial_code (snd \<phi>) (the (Mapping.lookup (phis'_codem g next (substitution_code g next) nodes_of_phis) \<phi>))"
            unfolding uninst_code.triv_phis'_def by simp
          moreover

          from \<open>\<phi> \<noteq> next\<close> \<open>\<phi> \<in> Mapping.keys (phis g)\<close> \<open>next \<in> Mapping.keys (phis g)\<close>
          have [simp]: "\<phi>_val \<noteq> snd next"
            unfolding keys_dom_lookup
            by (cases "next", cases \<phi>) (auto dest: ssa.phis_disj)

          show ?thesis
          proof (cases "\<phi> \<in> ssa.trivial_phis g")
            case True
            hence "ssa.trivial_code \<phi>_val \<phi>_args"
              unfolding ssa.trivial_phis_def by clarsimp
            hence "ssa.trivial_code \<phi>_val (map (substNext_code g next) \<phi>_args)"
              apply (rule ssa.trivial_code_mapI)
               prefer 2
               apply (clarsimp simp: substNext_code_def)
              apply (clarsimp simp: substNext_code_def substitution_code_def)
              apply (erule_tac c="\<phi>_val" in equalityCE)
               prefer 2 apply simp
              apply clarsimp
              apply (subgoal_tac "ssa.isTrivialPhi g \<phi>_val (snd next)")
               apply (subgoal_tac "ssa.isTrivialPhi g (snd next) \<phi>_val")
                apply (blast dest: isTrivialPhi_asymmetric)
               using assms(3) \<open>next \<in> Mapping.keys (phis g)\<close>
               apply (clarsimp simp: ssa.trivial_def keys_dom_lookup)
               apply (frule isTrivial_the_trivial [rotated 1, where v="snd next"])
                apply -
                apply (rule ssa.phis_phi [where n="fst next"])
                apply simp
               apply simp
              apply (thin_tac "\<phi>_val = v" for v)
              using \<open>ssa.trivial_code \<phi>_val \<phi>_args\<close>
              apply (clarsimp simp: ssa.trivial_code_def)
              by (erule the_trivial_SomeE) (auto simp: ssa.isTrivialPhi_def)
            with calculation True \<open>\<phi> \<noteq> next\<close> \<open>\<phi> \<in> nodes\<close> show ?thesis
              unfolding uninst_code.ssa.trivial_phis_def phis'_codem_def
              by (clarsimp simp: keys_dom_lookup substNext_code_alt_def)
          next
            case False
            with calculation \<open>\<phi> \<noteq> next\<close> \<open>\<phi> \<in> Mapping.keys (phis g)\<close> True show ?thesis
              unfolding phis'_codem_def uninst_code.ssa.trivial_phis_def
              by (auto simp: keys_dom_lookup triv_phis'_def ssa.trivial_code_def)
          qed
        qed
      qed
    qed
  qed

  lemma nodes_of_phis'_correct:
  assumes "g \<turnstile> nodes_of_phis \<approx>\<^sub>\<phi> ssa.phiNodes_of g"
    and "next \<in> Mapping.keys (phis g)" and "ssa.trivial g (snd next)"
  shows "g \<turnstile> (nodes_of_phis' g next (substitution_code g next) nodes_of_phis) \<approx>\<^sub>\<phi> (uninst_code.ssa.phiNodes_of (const (phis'_codem g next (substitution_code g next) nodes_of_phis)) g)"
  proof -
    from assms(2) obtain next_args where lookup_next [simp]: "Mapping.lookup (phis g) next = Some next_args"
      unfolding keys_dom_lookup by auto
    hence phi_next [simp]: "ssa.phi g (snd next) = Some next_args"
      by -(rule ssa.phis_phi [where n="fst next"], simp)
    from assms(3) have in_next_args: "\<And>v. v \<in> set next_args \<Longrightarrow> v = snd next \<or> v = substitution_code g next"
      unfolding ssa.trivial_def substitution_code_def
      apply clarsimp
      apply (subst(asm) isTrivial_the_trivial)
        apply (rule ssa.phis_phi [where g=g and n="fst next"])
        apply simp
       apply assumption
      by (auto simp: ssa.isTrivialPhi_def split: option.splits)
    from assms(2) have [dest!]: "\<And>x vs. Mapping.lookup (phis g) (x, snd next) = Some vs \<Longrightarrow> x = fst next \<and> vs = next_args"
      by (auto simp add: keys_dom_lookup dest: ssa.phis_disj [where n'="fst next"])
    show ?thesis
    apply (simp only: phi_equiv_mapping_def)
    apply (subgoal_tac "finite (dom (Mapping.lookup (phis'_codem g next (substitution_code g next) nodes_of_phis)))")
     prefer 2
     apply (subst dom_phis'_codem)
      apply (rule nodes_of_phis_finite [OF assms(1)], assumption)
      using assms(2) [simplified keys_dom_lookup]
      apply clarsimp
     apply (clarsimp simp: ssa.phis_finite split: option.splits)
     apply (rule nodes_of_phis_finite [OF assms(1)], assumption)
     using assms(2) [simplified keys_dom_lookup]
     apply clarsimp
    apply (simp_all only: phis'_codem_correct [OF assms(1,2)])
    apply (intro ballI)
    apply (rename_tac v)
    apply (subst(asm) ssa.keys_phidefNodes [OF ssa.phis_finite])
    apply (subst uninst_code.ssa.lookup_phiNodes_of, assumption)
    apply (subst lookup_phis'_code)+
    apply (subst substNext_code_def)+
    apply (subst dom_phis'_code)+
    apply (cases "\<exists>\<phi> \<in> Mapping.keys (phis g). snd next \<in> set (the (Mapping.lookup (phis g) \<phi>))")
     apply (erule bexE)
     apply (subst(asm) keys_dom_lookup)
     apply (drule domD)
     apply (erule exE)
     apply (rule phi_equiv_mappingE [OF assms(1,2)], assumption)
      apply clarsimp
     apply (cases "substitution_code g next \<in> snd ` Mapping.keys (phis g)")
      apply (cases "\<exists>\<phi>' \<in> Mapping.keys (phis g). substitution_code g next \<in> set (the (Mapping.lookup (phis g) \<phi>'))")
       apply (erule bexE)
       apply (subst(asm) keys_dom_lookup)+
       apply (drule domD)
       apply (erule exE)
       apply (rule_tac x="\<phi>'" in phi_equiv_mappingE' [OF assms(1)], assumption)
         apply simp
        apply (simp add: keys_dom_lookup)
       apply (case_tac "v = substitution_code g next")
        apply (simp only:)
        apply (subst lookup_nodes_of_phis'_subst)
        apply (simp add: lookup_phis'_code)
        apply (auto 4 4 intro: rev_image_eqI
          simp: keys_dom_lookup map_option_case substNext_code_def split: option.splits)[1]
       apply (subst lookup_nodes_of_phis'_not_subst, assumption)
       apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys (phis g). v \<in> set (the (Mapping.lookup (phis g) \<phi>\<^sub>v))")
        apply (erule bexE)
        apply (simp add: keys_dom_lookup)
        apply (drule domD)
        apply (erule exE)
        apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
          apply simp
         apply (clarsimp simp: keys_dom_lookup)
        apply (clarsimp simp: keys_dom_lookup)
        apply (rename_tac n v \<phi>_args n' v' n'' \<phi>_args' \<phi>_args'')
        apply (auto dest: in_next_args)[1]
        apply (erule_tac x="(n,v)" in ballE)
         prefer 2 apply (auto dest: in_next_args)[1]
        apply auto[1]
       using phi_equiv_mappingE2' [OF assms(1), rotated 1]
       apply (erule_tac x=v in meta_allE)
       apply (erule meta_impE)
        apply clarsimp
       apply (auto simp: keys_dom_lookup)[1]
        apply force
       apply force
      using phi_equiv_mappingE2' [OF assms(1), rotated 1]
      apply (erule_tac x="substitution_code g next" in meta_allE)
      apply (erule meta_impE)
       apply clarsimp
      apply (erule meta_impE)
       apply assumption
      apply (case_tac "v = substitution_code g next")
       apply (auto simp: keys_dom_lookup)[1]
            apply force
           apply force
          apply force
         apply force
        apply force
       apply force
      apply (subst lookup_nodes_of_phis'_not_subst, assumption)
      apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys (phis g). v \<in> set (the (Mapping.lookup (phis g) \<phi>\<^sub>v))")
       apply (erule bexE)
       apply (simp add: keys_dom_lookup)
       apply (drule domD)
       apply (erule exE)
       apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
         apply simp
        apply (clarsimp simp: keys_dom_lookup)
       apply (auto simp: keys_dom_lookup dest: in_next_args)[1]
        apply (force dest: in_next_args)[1]
       apply (force dest: in_next_args)[1]
      using phi_equiv_mappingE2' [OF assms(1), rotated 1]
      apply (erule_tac x=v in meta_allE)
      apply (erule meta_impE)
       apply clarsimp
      apply (auto simp: keys_dom_lookup)[1]
         apply force
        apply force
       apply force
      apply force
     apply (case_tac "v = substitution_code g next")
      apply (auto simp: keys_dom_lookup)[1]
     apply (subst lookup_nodes_of_phis'_not_subst, assumption)
     apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys (phis g). v \<in> set (the (Mapping.lookup (phis g) \<phi>\<^sub>v))")
      apply (erule bexE)
      apply (simp add: keys_dom_lookup)
      apply (drule domD)
      apply (erule exE)
      apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
        apply simp
       apply (clarsimp simp: keys_dom_lookup)
      apply (auto simp: keys_dom_lookup dest: in_next_args)[1]
      apply (force dest: in_next_args)[1]
     using phi_equiv_mappingE2' [OF assms(1), rotated 1]
     apply (erule_tac x="v" in meta_allE)
     apply (erule meta_impE)
      apply clarsimp
     apply (auto simp: keys_dom_lookup)[1]
      apply force
     apply force
    using phi_equiv_mappingE2' [OF assms(1), rotated 1]
    apply (erule_tac x="snd next" in meta_allE)
    apply (erule meta_impE)
     apply clarsimp
    apply (erule meta_impE)
     using assms(2)
     apply clarsimp
    apply (subgoal_tac "{n \<in> Mapping.keys (phis g). snd next \<in> set (the (Mapping.lookup (phis g) n))} = {}")
     prefer 2
     apply auto[1]
    apply (cases "substitution_code g next \<in> snd ` Mapping.keys (phis g)")
     apply (cases "\<exists>\<phi>' \<in> Mapping.keys (phis g). substitution_code g next \<in> set (the (Mapping.lookup (phis g) \<phi>'))")
      apply (erule bexE)
      apply (subst(asm) keys_dom_lookup)+
      apply (drule domD)
      apply (erule exE)
      apply (rule_tac x="\<phi>'" in phi_equiv_mappingE' [OF assms(1)], assumption)
        apply simp
       apply (simp add: keys_dom_lookup)
      apply (case_tac "v = substitution_code g next")
       apply (auto simp: keys_dom_lookup; force)[1]
      apply (subst lookup_nodes_of_phis'_not_subst, assumption)
      apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys (phis g). v \<in> set (the (Mapping.lookup (phis g) \<phi>\<^sub>v))")
       apply (erule bexE)
       apply (simp add: keys_dom_lookup)
       apply (drule domD)
       apply (erule exE)
       apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
         apply simp
        apply (clarsimp simp: keys_dom_lookup)
       apply (auto simp: keys_dom_lookup dest: in_next_args)[1]
        apply (force dest: in_next_args)[1]
       apply (force dest: in_next_args)[1]
      using phi_equiv_mappingE2' [OF assms(1), rotated 1]
      apply (erule_tac x=v in meta_allE)
      apply (erule meta_impE)
       apply clarsimp
      apply (auto simp: keys_dom_lookup; force)[1]
     using phi_equiv_mappingE2' [OF assms(1), rotated 1]
     apply (erule_tac x="substitution_code g next" in meta_allE)
     apply (erule meta_impE)
      apply clarsimp
     apply (erule meta_impE)
      apply assumption
     apply (case_tac "v = substitution_code g next")
      apply (auto simp: keys_dom_lookup; force)[1]
     apply (subst lookup_nodes_of_phis'_not_subst, assumption)
     apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys (phis g). v \<in> set (the (Mapping.lookup (phis g) \<phi>\<^sub>v))")
      apply (erule bexE)
      apply (simp add: keys_dom_lookup)
      apply (drule domD)
      apply (erule exE)
      apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
        apply simp
       apply (clarsimp simp: keys_dom_lookup)
      apply (auto simp: keys_dom_lookup dest: in_next_args; force dest: in_next_args)[1]
     using phi_equiv_mappingE2' [OF assms(1), rotated 1]
     apply (erule_tac x="v" in meta_allE)
     apply (erule meta_impE)
      apply clarsimp
     apply (erule meta_impE)
      apply (clarsimp simp: keys_dom_lookup)
     apply (auto simp: keys_dom_lookup; force)[1]
    apply (case_tac "v = substitution_code g next")
     apply (auto simp: keys_dom_lookup)[1]
    apply (subst lookup_nodes_of_phis'_not_subst, assumption)
    apply (case_tac "\<exists>\<phi>\<^sub>v \<in> Mapping.keys (phis g). v \<in> set (the (Mapping.lookup (phis g) \<phi>\<^sub>v))")
     apply (erule bexE)
     apply (simp add: keys_dom_lookup)
     apply (drule domD)
     apply (erule exE)
     apply (rule_tac x="\<phi>\<^sub>v" in phi_equiv_mappingE' [OF assms(1)], assumption)
       apply simp
      apply (clarsimp simp: keys_dom_lookup)
     apply (auto simp: keys_dom_lookup dest: in_next_args; force dest: in_next_args)[1]
    using phi_equiv_mappingE2' [OF assms(1), rotated 1]
    apply (erule_tac x=v in meta_allE)
    apply (erule meta_impE)
     apply clarsimp
    apply (erule meta_impE)
     apply (clarsimp simp: keys_dom_lookup)
    apply (auto simp: keys_dom_lookup; force)[1]
    done
  qed

  lemma nodes_of_uses'_correct:
  assumes "g \<turnstile> nodes_of_uses \<approx>\<^sub>\<phi> ssa.useNodes_of g"
    and "next \<in> Mapping.keys (phis g)" and "ssa.trivial g (snd next)"
  shows "g \<turnstile> (nodes_of_uses' g next (substitution_code g next) (Mapping.keys (ssa.phidefNodes g)) nodes_of_uses) \<approx>\<^sub>\<phi> (uninst_code.ssa.useNodes_of (const (uses'_codem g next (substitution_code g next) nodes_of_uses)) g)"
  proof -
    from assms(2,3) ssa.phis_in_\<alpha>n [of g "fst next" "snd next"]
    have "ssa.redundant g"
      unfolding ssa.redundant_def ssa.allVars_def ssa.allDefs_def ssa.phiDefs_def
      by (cases "next") (auto simp: keys_dom_lookup)

    then interpret step: CFG_SSA_step_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "uses" phis var chooseNext_all
      by unfold_locales


    from assms(2,3) obtain next_args v where lookup_next [simp]: "Mapping.lookup (phis g) next = Some next_args"
      and "ssa.isTrivialPhi g (snd next) v"
      unfolding keys_dom_lookup ssa.trivial_def by auto
    hence phi_next [simp]: "ssa.phi g (snd next) = Some next_args"
      by -(rule ssa.phis_phi [where n="fst next"], simp)
    hence the_trivial_next_args [simp]: "the_trivial (snd next) next_args = Some v" using \<open>ssa.isTrivialPhi g (snd next) v\<close>
      by (rule isTrivial_the_trivial)

    from assms(3) have in_next_args: "\<And>v. v \<in> set next_args \<Longrightarrow> v = snd next \<or> v = substitution_code g next"
      unfolding ssa.trivial_def substitution_code_def
      apply (clarsimp simp del: the_trivial_next_args)
      apply (subst(asm) isTrivial_the_trivial)
        apply (rule ssa.phis_phi [where g=g and n="fst next"])
        apply simp
       apply assumption
      by (auto simp: ssa.isTrivialPhi_def split: option.splits)

    from \<open>ssa.isTrivialPhi g (snd next) v\<close>
    have triv_phi_is_v [dest!]: "\<And>v'. ssa.isTrivialPhi g (snd next) v' \<Longrightarrow> v' = v"
      using isTrivialPhi_det [OF assms(3)] by auto

    from \<open>ssa.isTrivialPhi g (snd next) v\<close> have [simp]: "v \<noteq> snd next" unfolding ssa.isTrivialPhi_def by simp

    from assms(2) have [dest!]: "\<And>x vs. Mapping.lookup (phis g) (x, snd next) = Some vs \<Longrightarrow> x = fst next \<and> vs = next_args"
      by (auto simp add: keys_dom_lookup dest: ssa.phis_disj [where n'="fst next"])

    have [simp]: "(CFG_base.useNodes_of \<alpha>n
              (const
                (CFG_SSA_Transformed_notriv_base.uses' \<alpha>n defs (usesOf \<circ> uses)
                  (\<lambda>g. Mapping.lookup (phis g)) cN g))
              g)
     = (CFG_base.useNodes_of \<alpha>n
     ((usesOf \<circ> uses)
      (g := CFG_SSA_Transformed_notriv_base.uses' \<alpha>n defs (usesOf \<circ> uses)
             (\<lambda>g. Mapping.lookup (phis g)) cN g)) g)"
     unfolding uninst.useNodes_of_def uninst.addN_def [abs_def]
      by auto

    have substNext_idem [simp]: "\<And>v. substNext g (substNext g v) = substNext g v"
      unfolding substNext_def by (auto split: if_splits)

    from assms(1)
    have nodes_of_uses_eq_NoneD [elim_format, elim]: "\<And>v n args. \<lbrakk>Mapping.lookup nodes_of_uses v = None; Mapping.lookup (phis g) (n,v) = Some args \<rbrakk>
      \<Longrightarrow> (\<forall>n \<in> set (\<alpha>n g). \<forall>vs. Mapping.lookup (uses g) n = Some vs \<longrightarrow> v \<notin> vs)"
       unfolding phi_equiv_mapping_def
     apply (clarsimp simp: ssa.lookup_useNodes_of split: option.splits if_splits)
     by (erule_tac x="(n,v)" in ballE) auto

    from assms(1)
    have nodes_of_uses_eq_SomeD [elim_format, elim]: "\<And>v nodes n args. \<lbrakk> Mapping.lookup nodes_of_uses v = Some nodes; Mapping.lookup (phis g) (n,v) = Some args\<rbrakk>
      \<Longrightarrow> nodes = {n \<in> set (\<alpha>n g). \<exists>vs. Mapping.lookup (uses g) n = Some vs \<and> v \<in> vs}"
      unfolding phi_equiv_mapping_def
    apply (clarsimp simp: ssa.lookup_useNodes_of split: option.splits if_splits)
    by (erule_tac x="(n,v)" in ballE) auto

    show ?thesis
    unfolding phi_equiv_mapping_def nodes_of_uses'_def substitution_code_def Let_def ssa.keys_phidefNodes [OF ssa.phis_finite]
    apply (subst o_def [where g="const g" for g])
    apply (subst uses'_codem_correct [OF assms(1,2), unfolded substitution_code_def])
    apply (subst uninst.lookup_useNodes_of')
     apply (clarsimp simp: uses'_code_def split: option.splits)
     apply (rule finite_imageI)
     using ssa.uses_finite [of g]
     apply (fastforce split: option.splits)[1]
    apply (cases "v \<in> snd ` dom (Mapping.lookup (phis g))")
     prefer 2
     apply (force intro: rev_image_eqI simp: lookup_delete uninst_code.uses'_code_def substNext_code_def substitution_code_def split: option.splits)[1]
    apply (clarsimp simp: Mapping_lookup_map_default lookup_delete uses'_code_def substNext_code_def substitution_code_def)
    apply (rename_tac n n' v' phi_args phi_args')
    apply safe
                         apply (auto elim: nodes_of_uses_eq_SomeD [where n="fst next"]
                           nodes_of_uses_eq_NoneD [where n="fst next"] simp: phi_equiv_mapping_def split: option.splits)[13]

            using assms(1)
            apply (simp add: phi_equiv_mapping_def)
            apply (erule_tac x="(n,v)" in ballE)
             prefer 2 apply auto[1]
            apply (auto simp: ssa.lookup_useNodes_of split: option.splits)[1]

           apply (auto elim: nodes_of_uses_eq_SomeD [where n="fst next"]
             nodes_of_uses_eq_NoneD [where n="fst next"] split: option.splits)[1]

          using assms(1)
          apply (simp add: phi_equiv_mapping_def)
          apply (erule_tac x="(n,v)" in ballE)
           prefer 2 apply auto[1]
          apply (auto simp: ssa.lookup_useNodes_of split: option.splits)[1]

         apply (auto 4 3 elim: nodes_of_uses_eq_SomeD [where n="fst next"] split: option.splits)[4]

     using assms(1)
     apply (simp add: phi_equiv_mapping_def)
     apply (erule_tac x="(n',v')" in ballE)
      prefer 2 apply auto[1]
     apply (auto simp: ssa.lookup_useNodes_of split: option.splits)[1]

    by (auto split: option.splits)[1]
  qed

  definition[code]: "substAll_efficient g \<equiv>
    let phiVals = Mapping.keys (ssa.phidefNodes g);
        u = uses g;
        p = phis g;
        tp = ssa.trivial_phis g;
        nou = ssa.useNodes_of g;
        nop = ssa.phiNodes_of g
    in
    while
    (\<lambda>((u,p),triv_phis,nodes_of_uses,nodes_of_phis). \<not> Set.is_empty triv_phis)
    (\<lambda>((u,p),triv_phis,nodes_of_uses,nodes_of_phis). let
        next = Max triv_phis;
        next' = uninst_code.substitution_code (const p) g next;
        (u',p') = uninst_code.step_codem (const u) (const p) g next next' nodes_of_uses nodes_of_phis;
        tp' = uninst_code.triv_phis' (const p') g next triv_phis nodes_of_phis;
        nou' = uninst_code.nodes_of_uses' g next next' phiVals nodes_of_uses;
        nop' = uninst_code.nodes_of_phis' g next next' nodes_of_phis
      in ((u', p'), tp', nou', nop'))
    ((u, p), tp, nou, nop)"

  abbreviation "u_c x \<equiv> const (usesOf (fst x))"
  abbreviation "p_c x \<equiv> const (Mapping.lookup (snd x))"
  abbreviation "u g x \<equiv> u_g g (fst x)"
  abbreviation "p g x \<equiv> p_g g (snd x)"

  lemma usesOf_upd [simp]: "(usesOf \<circ> u g s1)(g := usesOf us) = usesOf \<circ> u_g g us"
    by (auto simp: fun_upd_apply usesOf_def [abs_def] split: option.splits if_splits)

  lemma keys_uses'_codem [simp]: "Mapping.keys (uses'_codem g next (substitution_code g next) (ssa.useNodes_of g)) = Mapping.keys (uses g)"
    unfolding uses'_codem_def
  apply (transfer fixing: g)
  apply (auto split: option.splits if_splits simp: fold_update_conv)
  by (subst(asm) sorted_list_of_set) (auto intro: finite_subset [OF _ finite_set])

  lemma keys_uses'_codem': "\<lbrakk> g \<turnstile> nodes_of_uses \<approx>\<^sub>\<phi> ssa.useNodes_of g; next \<in> Mapping.keys (phis g) \<rbrakk>
    \<Longrightarrow> Mapping.keys (uses'_codem g next (substitution_code g next) nodes_of_uses) = Mapping.keys (uses g)"
    unfolding uses'_codem_def
  apply (clarsimp simp: keys_dom_lookup split: if_splits option.splits)
  apply (auto simp: phi_equiv_mapping_def)
  by (erule_tac x="next" in ballE) (auto simp: ssa.lookup_useNodes_of split: if_splits option.splits)

  lemma triv_phis_base [simp]: "uninst_code.ssa.trivial_phis (const (phis g)) g = ssa.trivial_phis g"
    unfolding uninst_code.ssa.trivial_phis_def ..
  lemma useNodes_of_base [simp]: "uninst_code.ssa.useNodes_of (const (uses g)) g = ssa.useNodes_of g"
    unfolding uninst_code.ssa.useNodes_of_def uninst_code.ssa.addN_def [abs_def] mmap_def Mapping.map_default_def [abs_def] Mapping.default_def
    unfolding usesOf_def [abs_def]
    by transfer auto

  lemma phiNodes_of_base [simp]: "uninst_code.ssa.phiNodes_of (const (phis g)) g = ssa.phiNodes_of g"
    unfolding uninst_code.ssa.phiNodes_of_def uninst_code.ssa.phis_addN_def [abs_def] mmap_def Mapping.map_default_def [abs_def] Mapping.default_def
    by transfer auto

  lemma phi_equiv_mapping_refl [simp]: "uninst_code.phi_equiv_mapping ph g m m"
    unfolding uninst_code.phi_equiv_mapping_def by simp

  lemma substAll_efficient_code [code]:
    "substAll g = map_prod usesOf Mapping.lookup (fst (substAll_efficient g))"
    unfolding substAll_efficient_def while_def substAll_def Let_def
  apply -
  apply (rule map_option_the [OF _ substAll_terminates])
  proof (rule while_option_sim [where
      R="\<lambda>x y. y = map_option (\<lambda>a. map_prod usesOf Mapping.lookup (fst (f a))) x" and
      I="\<lambda>((u,p),triv_phis,nodes_of_uses, phis_of_nodes). Mapping.keys u \<subseteq> set (\<alpha>n g) \<and> Mapping.keys p \<subseteq> Mapping.keys (phis g)
        \<and> CFG_SSA_Transformed_notriv_linorder_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs (uses(g:=u)) (phis(g:=p)) var chooseNext_all
        \<and> triv_phis = uninst_code.ssa.trivial_phis (const p) g
        \<and> uninst_code.phi_equiv_mapping (const p) g nodes_of_uses (uninst_code.ssa.useNodes_of (const u) g)
        \<and> uninst_code.phi_equiv_mapping (const p) g phis_of_nodes (uninst_code.ssa.phiNodes_of (const p) g)"
      for f
      , simplified], simp_all add: split_def dom_uses_in_graph Set.is_empty_def)
    show "CFG_SSA_Transformed_notriv_linorder_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs uses phis var
     chooseNext_all"
      by unfold_locales
  next
    fix s1
    assume "Mapping.keys (fst (fst s1)) \<subseteq> set (\<alpha>n g) \<and> Mapping.keys (snd (fst s1)) \<subseteq> Mapping.keys (phis g)
      \<and> CFG_SSA_Transformed_notriv_linorder_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs (u g (fst s1)) (p g (fst s1)) var chooseNext_all
      \<and> fst (snd s1) = uninst_code.ssa.trivial_phis (const (snd (fst s1))) g
      \<and> uninst_code.phi_equiv_mapping (const (snd (fst s1))) g (fst (snd (snd s1))) (uninst_code.ssa.useNodes_of (const (fst (fst s1))) g)
      \<and> uninst_code.phi_equiv_mapping (const (snd (fst s1))) g (snd (snd (snd s1))) (uninst_code.ssa.phiNodes_of (const (snd (fst s1))) g)"
    then obtain s1_uses s1_phis s1_triv_phis s1_nodes_of_uses s1_phi_nodes_of where
      [simp]: "s1 = ((s1_uses, s1_phis), s1_triv_phis, s1_nodes_of_uses, s1_phi_nodes_of)"
      and "Mapping.keys s1_uses \<subseteq> set (\<alpha>n g)"
      and "Mapping.keys s1_phis \<subseteq> Mapping.keys (phis g)"
      and "CFG_SSA_Transformed_notriv_linorder_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs (u_g g s1_uses) (p_g g s1_phis) var chooseNext_all"
      and [simp]: "s1_triv_phis = uninst_code.ssa.trivial_phis (const s1_phis) g"
      and nou_equiv: "uninst_code.phi_equiv_mapping (const s1_phis) g s1_nodes_of_uses (uninst_code.ssa.useNodes_of (const s1_uses) g)"
      and pno_equiv: "uninst_code.phi_equiv_mapping (const s1_phis) g s1_phi_nodes_of (uninst_code.ssa.phiNodes_of (const s1_phis) g)"
      by (cases s1; auto)
    from this(4) interpret i: CFG_SSA_Transformed_notriv_linorder_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs" "u_g g s1_uses" "p_g g s1_phis" var chooseNext_all .
    let ?s2 = "map_prod usesOf Mapping.lookup (fst s1)"
    have [simp]: "uninst_code.ssa.trivial_phis (const s1_phis) g \<noteq> {} \<longleftrightarrow> cond g ?s2"
      unfolding uninst_code.ssa.redundant_code_def [symmetric]
      by (clarsimp simp add: cond_def i.ssa.redundant_code [simplified, symmetric] CFG_SSA_wf_base.CFG_SSA_wf_defs)
    thus "uninst_code.ssa.trivial_phis (const (snd (fst s1))) g \<noteq> {} \<longleftrightarrow> cond g ?s2"
      by simp
    {
      assume "uninst_code.ssa.trivial_phis (const (snd (fst s1))) g \<noteq> {}"
      hence red: "uninst.redundant (usesOf \<circ> u_g g s1_uses) (\<lambda>g'. Mapping.lookup (p_g g s1_phis g')) g"
        by (simp add: cond_def uninst.CFG_SSA_wf_defs)
      then interpret step: CFG_SSA_step_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs"
        "u_g g s1_uses" "p_g g s1_phis" var chooseNext_all g
        by unfold_locales simp
      from step.step_CFG_SSA_Transformed_notriv[simplified]
      interpret step_step: CFG_SSA_Transformed_notriv \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses "defs"
      "(usesOf \<circ> u_g g s1_uses)(g := uninst.uses' (usesOf \<circ> u_g g s1_uses) (\<lambda>g'. Mapping.lookup (p_g g s1_phis g')) g)"
      "(\<lambda>g'. Mapping.lookup (p_g g s1_phis g'))(g := uninst.phis' (usesOf \<circ> u_g g s1_uses) (\<lambda>g'. Mapping.lookup (p_g g s1_phis g')) g)"
      var i.cN .

      interpret step_step: CFG_SSA_ext \<alpha>e \<alpha>n invar inEdges' Entry "defs"
      "(usesOf \<circ> u_g g s1_uses)(g := uninst.uses' (usesOf \<circ> (u_g g s1_uses)) (\<lambda>g'. Mapping.lookup (p_g g s1_phis g')) g)"
      "(\<lambda>g'. Mapping.lookup (p_g g s1_phis g'))(g := uninst.phis' (usesOf \<circ> u_g g s1_uses) (\<lambda>g'. Mapping.lookup (p_g g s1_phis g')) g)"
      ..

      from \<open>Mapping.keys s1_uses \<subseteq> set (\<alpha>n g)\<close>
      have keys_u_g: "Mapping.keys (u_g g s1_uses g) \<subseteq> set (\<alpha>n g)"
        by clarsimp

      have "Max (CFG_SSA_wf_base_code.trivial_phis (p_g g s1_phis) g) = chooseNext_all (usesOf (u_g g s1_uses g)) (p_g g s1_phis g) g"
      apply (rule chooseNext_all_code [where u="u_g g s1_uses", symmetric])
      by unfold_locales (simp add: i.ssa.redundant_code [symmetric])

      hence [simp]: "Max (CFG_SSA_wf_base_code.trivial_phis (const s1_phis) g) = chooseNext_all (usesOf s1_uses) s1_phis g"
        by (simp add: uninst_code.ssa.trivial_phis_def)

      have [simp]: "chooseNext_all (usesOf s1_uses) s1_phis g \<in> Mapping.keys s1_phis"
        using i.chooseNext' [of g]
        by (clarsimp simp: Mapping.keys_dom_lookup)

      have [simp]: "uninst_code.ssa.useNodes_of (const s1_uses) g = uninst_code.ssa.useNodes_of (u_g g s1_uses) g"
        unfolding uninst_code.ssa.useNodes_of_def
        unfolding uninst_code.ssa.addN_def [abs_def]
        by simp

      have [simp]: "uninst_code.ssa.phiNodes_of (const s1_phis) g = uninst_code.ssa.phiNodes_of (p_g g s1_phis) g"
        unfolding uninst_code.ssa.phiNodes_of_def
        unfolding uninst_code.ssa.phis_addN_def [abs_def]
        by simp

      from \<open>Mapping.keys s1_phis \<subseteq> Mapping.keys (phis g)\<close>
      have "finite (Mapping.keys s1_phis)"
      by (rule finite_subset) (auto simp: keys_dom_lookup intro: ssa.phis_finite)

      hence [simp]: "uninst_code.phi_equiv_mapping (const s1_phis) g = uninst_code.phi_equiv_mapping (p_g g s1_phis) g"
        apply (intro ext)
        apply (clarsimp simp: uninst_code.phi_equiv_mapping_def)
        apply (subst uninst.keys_phidefNodes)
         apply (simp add: keys_dom_lookup)
        by clarsimp

      have uses_conv: "(usesOf \<circ>
          u_g g
           (CFG_SSA_Transformed_notriv_base_code.uses'_codem (u_g g s1_uses)
             g (chooseNext_all (usesOf s1_uses) s1_phis g)
             (uninst_code.substitution_code (p_g g s1_phis) g (chooseNext_all (usesOf s1_uses) s1_phis g))
             s1_nodes_of_uses))
                  = ((usesOf \<circ> u_g g s1_uses)
       (g := CFG_SSA_Transformed_notriv_base.uses' \<alpha>n defs (usesOf \<circ> u_g g s1_uses) (\<lambda>ga. Mapping.lookup (p_g g s1_phis ga))
              i.cN g))"
       unfolding i.uses'_code_correct [OF red]
       apply (subst i.uses'_codem_correct [symmetric, where nodes_of_uses=s1_nodes_of_uses])
         apply (rule nou_equiv [simplified])
        apply auto[1]
       by (auto simp: fun_upd_apply)

      have phis_conv: "(\<lambda>ga. Mapping.lookup
                (p_g g (CFG_SSA_Transformed_notriv_base_code.phis'_codem (p_g g s1_phis) g
                         (chooseNext_all (usesOf s1_uses) s1_phis g)
                         (uninst_code.substitution_code (p_g g s1_phis) g (chooseNext_all (usesOf s1_uses) s1_phis g))
                         (CFG_SSA_base.phiNodes_of (\<lambda>ga. Mapping.lookup (p_g g s1_phis ga)) g))
                  ga)) =
       (\<lambda>ga. Mapping.lookup (p_g g s1_phis ga))
       (g := CFG_SSA_Transformed_notriv_base.phis' \<alpha>n defs (usesOf \<circ> u_g g s1_uses) (\<lambda>ga. Mapping.lookup (p_g g s1_phis ga))
              i.cN g)"
       apply (subst i.phis'_code_correct [OF red])
       apply (subst i.phis'_codem_correct [symmetric])
       by (auto simp: fun_upd_apply)

      have [simp]: "uninst_code.substitution_code (const s1_phis) g = uninst_code.substitution_code (p_g g s1_phis) g"
        by (intro ext) (clarsimp simp: uninst_code.substitution_code_def)

      let ?next = "Max (uninst_code.ssa.trivial_phis (const (snd (fst s1))) g)"
      let ?u' = "fst (uninst_code.step_codem (u g (fst s1)) (p g (fst s1)) g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) (fst (snd (snd s1))) (snd (snd (snd s1))))"
      let ?p' = "snd (uninst_code.step_codem (u g (fst s1)) (p g (fst s1)) g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) (fst (snd (snd s1))) (snd (snd (snd s1))))"

      show step_s2: "step g ?s2 = map_prod usesOf Mapping.lookup (uninst_code.step_codem (u g (fst s1)) (p g (fst s1)) g
        ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next)
        (fst (snd (snd s1))) (snd (snd (snd s1))))"
        unfolding uninst_code.step_codem_def uninst.step_def split_def map_prod_def Let_def
      apply (auto simp: map_prod_def Let_def step_step.usesOf_cache[of g, simplified]
        i.phis'_codem_correct [OF pno_equiv [simplified]]
        i.phis'_code_correct[simplified, OF red, simplified, symmetric]
        i.uses'_codem_correct [OF nou_equiv [simplified]]
        i.uses'_code_correct [OF red, symmetric, simplified])
       apply (subst uninst.uses'_def [abs_def])+
       apply (clarsimp simp: uninst.substNext_def uninst.substitution_def CFG_SSA_wf_base.CFG_SSA_wf_defs)
      apply (subst uninst.phis'_def [abs_def])+
      by (clarsimp simp: uninst.substNext_def [abs_def] uninst.substitution_def CFG_SSA_wf_base.CFG_SSA_wf_defs cong: if_cong option.case_cong)

      have [simplified, simp]:
        "uninst_code.phis'_codem (p g (fst s1)) g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) s1_phi_nodes_of
          = uninst_code.phis'_codem (p g (fst s1)) g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) (uninst_code.ssa.phiNodes_of (const (snd (fst s1))) g)"
        by (auto simp: i.phis'_codem_correct [OF phi_equiv_mapping_refl] i.phis'_codem_correct [OF pno_equiv [simplified]])

      have [simplified, simp]:
        "usesOf (uninst_code.uses'_codem (u g (fst s1)) g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) s1_nodes_of_uses)
          = usesOf (uninst_code.uses'_codem (u g (fst s1)) g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) (uninst_code.ssa.useNodes_of (const (fst (fst s1))) g))"
        by (auto simp: i.uses'_codem_correct [OF phi_equiv_mapping_refl] i.uses'_codem_correct [OF nou_equiv [simplified]])

      from step_s2[symmetric] step.step_CFG_SSA_Transformed_notriv \<open>Mapping.keys s1_uses \<subseteq> set (\<alpha>n g)\<close>
        \<open>Mapping.keys s1_phis \<subseteq> Mapping.keys (phis g)\<close>
      have "Mapping.keys ?u' \<subseteq> set (\<alpha>n g) \<and>
          Mapping.keys ?p' \<subseteq> Mapping.keys (phis g) \<and>
          CFG_SSA_Transformed_notriv_linorder_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs
           (u g (uninst_code.step_codem (u g (fst s1)) (p g (fst s1)) g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) s1_nodes_of_uses s1_phi_nodes_of))
           (p g (uninst_code.step_codem (u g (fst s1)) (p g (fst s1)) g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) s1_nodes_of_uses s1_phi_nodes_of))
           var chooseNext_all"
      unfolding CFG_SSA_Transformed_notriv_linorder_code_def
        CFG_SSA_Transformed_notriv_linorder_def
        CFG_SSA_Transformed_code_def
        CFG_SSA_wf_code_def CFG_SSA_code_def
      apply (clarsimp simp: map_prod_def split_def uninst_code.step_codem_def Let_def uses_conv phis_conv)
      apply (rule conjI)
       prefer 2
       apply (rule conjI)
        prefer 2
        apply auto[1]
        apply unfold_locales
        apply (rename_tac g')
        apply (case_tac "g \<noteq> g'")
        by (auto intro!: dom_uses_in_graph chooseNext_all_code
          simp: fun_upd_apply
            i.keys_phis'_codem' [OF pno_equiv [simplified], of ?next, simplified fun_upd_apply, simplified]
            i.keys_uses'_codem' [OF nou_equiv [simplified], of ?next, simplified fun_upd_apply, simplified])
      moreover

      have [simp]: "uninst_code.ssa.trivial_phis (p_g g s1_phis) g = uninst_code.ssa.trivial_phis (const s1_phis) g"
        unfolding uninst_code.ssa.trivial_phis_def uninst_code.ssa.trivial_code_def
        by clarsimp

      from i.triv_phis'_correct [of g "snd (snd (snd s1))" ?next] i.chooseNext' [of g]
      have "uninst_code.triv_phis' (const ?p') g ?next s1_triv_phis (snd (snd (snd s1)))
        = uninst_code.ssa.trivial_phis (const ?p') g"
        by (auto intro: pno_equiv [simplified] simp: uninst_code.step_codem_def)
      moreover

      from \<open>Mapping.keys s1_phis \<subseteq> Mapping.keys (phis g)\<close> ssa.phis_finite
      have "finite (dom (Mapping.lookup s1_phis))"
        by (auto intro: finite_subset simp: keys_dom_lookup)
      hence phi_equiv_mapping_p'I [simplified]:
      "\<And>m1 m2. uninst_code.phi_equiv_mapping (const s1_phis) g m1 m2 \<Longrightarrow> uninst_code.phi_equiv_mapping (const ?p') g m1 m2"
        unfolding uninst_code.phi_equiv_mapping_def
        apply clarsimp
        apply (subst(asm) uninst.keys_phidefNodes)
         apply simp
        apply (subst(asm) uninst.keys_phidefNodes)
         apply (simp add: uninst_code.step_codem_def keys_dom_lookup [symmetric])
        by (clarsimp simp: uninst_code.step_codem_def keys_dom_lookup [symmetric]) fastforce

      have "?next \<in> Mapping.keys s1_phis" by auto
      with \<open>Mapping.keys s1_phis \<subseteq> Mapping.keys (phis g)\<close> nou_equiv i.chooseNext' [of g]
      have "uninst_code.nodes_of_uses' g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) (snd ` dom (Mapping.lookup (phis g))) (fst (snd (snd s1)))
        = uninst_code.nodes_of_uses' g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) (snd ` dom (Mapping.lookup s1_phis)) (fst (snd (snd s1)))"
        unfolding uninst_code.nodes_of_uses'_def
        apply -
        apply (erule meta_impE)
         apply auto[1]
        apply (auto simp: Let_def uninst_code.substitution_code_def keys_dom_lookup uninst_code.ssa.trivial_def)
        apply (drule i.isTrivial_the_trivial [rotated 1])
         apply (rule i.ssa.phis_phi [where n="fst ?next"])
         apply simp
        apply clarsimp
        apply (drule i.ssa.allVars_in_allDefs)
        apply clarsimp
        apply (drule ssa.phis_phi)
        apply clarsimp
        apply (clarsimp simp: uninst_code.ssa.allVars_def uninst_code.ssa.allDefs_def uninst_code.ssa.allUses_def uninst_code.ssa.phiDefs_def)
        apply (erule disjE)
         apply (drule(1) ssa.simpleDef_not_phi)
         apply simp
        by (auto intro: rev_image_eqI)

      ultimately
      show "Mapping.keys ?u' \<subseteq> set (\<alpha>n g) \<and>
          Mapping.keys ?p' \<subseteq> Mapping.keys (phis g) \<and>
          CFG_SSA_Transformed_notriv_linorder_code \<alpha>e \<alpha>n invar inEdges' Entry oldDefs oldUses defs
           (u g (uninst_code.step_codem (u g (fst s1)) (p g (fst s1)) g (Max (uninst_code.ssa.trivial_phis (const (snd (fst s1))) g)) (uninst_code.substitution_code (const (snd (fst s1))) g ?next) (fst (snd (snd s1))) (snd (snd (snd s1)))))
           (p g (uninst_code.step_codem (u g (fst s1)) (p g (fst s1)) g (Max (uninst_code.ssa.trivial_phis (const (snd (fst s1))) g)) (uninst_code.substitution_code (const (snd (fst s1))) g ?next) (fst (snd (snd s1))) (snd (snd (snd s1)))))
           var chooseNext_all \<and>
          uninst_code.triv_phis' (const ?p') g ?next (uninst_code.ssa.trivial_phis (const (snd (fst s1))) g) (snd (snd (snd s1)))
            = uninst_code.ssa.trivial_phis (const ?p') g \<and>
          uninst_code.phi_equiv_mapping (const ?p') g (uninst_code.nodes_of_uses' g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) (snd ` dom (Mapping.lookup (phis g))) (fst (snd (snd s1)))) (uninst_code.ssa.useNodes_of (const ?u') g) \<and>
          uninst_code.phi_equiv_mapping (const ?p') g (uninst_code.nodes_of_phis' g ?next (uninst_code.substitution_code (const (snd (fst s1))) g ?next) (snd (snd (snd s1)))) (uninst_code.ssa.phiNodes_of (const ?p') g)"
      using i.nodes_of_uses'_correct [of g s1_nodes_of_uses ?next, OF nou_equiv [simplified]]
        i.chooseNext' [of g]
        i.nodes_of_phis'_correct [of g s1_phi_nodes_of ?next, OF pno_equiv [simplified]]
        apply simp
        apply (rule conjI)
         apply (rule phi_equiv_mapping_p'I)
         apply (clarsimp simp: uninst_code.step_codem_def)
        apply (rule phi_equiv_mapping_p'I)
        by (clarsimp simp: uninst_code.step_codem_def)
    }
  qed

end

end
