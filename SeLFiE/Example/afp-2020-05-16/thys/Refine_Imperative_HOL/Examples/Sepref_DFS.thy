section \<open>Simple DFS Algorithm\<close>
theory Sepref_DFS
imports 
  "../Sepref"
  Sepref_Graph
begin

text \<open>
  We define a simple DFS-algorithm, prove a simple correctness
  property, and do data refinement to an efficient implementation.
\<close>

subsection \<open>Definition\<close>

text \<open>Recursive DFS-Algorithm. 
  \<open>E\<close> is the edge relation of the graph, \<open>vd\<close> the node to 
  search for, and \<open>v0\<close> the start node.
  Already explored nodes are stored in \<open>V\<close>.\<close>

context 
  fixes E :: "'v rel" and v0 :: 'v and tgt :: "'v \<Rightarrow> bool"
begin
  definition dfs :: "('v set \<times> bool) nres" where
    "dfs \<equiv> do {
      (V,r) \<leftarrow> RECT (\<lambda>dfs (V,v). 
        if v\<in>V then RETURN (V,False)
        else do {
          let V=insert v V;
          if tgt v then
            RETURN (V,True)
          else
            FOREACH\<^sub>C (E``{v}) (\<lambda>(_,b). \<not>b) (\<lambda>v' (V,_). dfs (V,v')) (V,False)
        }
      ) ({},v0);
      RETURN (V,r)
    }"

  definition "reachable \<equiv> {v. (v0,v)\<in>E\<^sup>*}"

  definition "dfs_spec \<equiv> SPEC (\<lambda>(V,r). (r \<longleftrightarrow> reachable\<inter>Collect tgt\<noteq>{}) \<and> (\<not>r \<longrightarrow> V=reachable))"
  
  lemma dfs_correct:
    assumes fr: "finite reachable"
    shows "dfs \<le> dfs_spec"
  proof -
    have F: "\<And>v. v\<in>reachable \<Longrightarrow> finite (E``{v})"
      using fr
      apply (auto simp: reachable_def)
      by (metis (mono_tags) Image_singleton Image_singleton_iff
        finite_subset rtrancl.rtrancl_into_rtrancl subsetI)

  
    define rpre where "rpre = (\<lambda>S (V,v). 
        v\<in>reachable 
      \<and> V\<subseteq>reachable
      \<and> S\<subseteq>V
      \<and> (V \<inter> Collect tgt = {})
      \<and> E``(V-S) \<subseteq> V)"

    define rpost where "rpost = (\<lambda>S (V,v) (V',r). 
          (r\<longleftrightarrow>V'\<inter>Collect tgt \<noteq> {}) 
        \<and> V\<subseteq>V' 
        \<and> v\<in>V'
        \<and> V'\<subseteq>reachable
        \<and> (\<not>r \<longrightarrow> (E``(V'-S) \<subseteq> V')))
      "

    define fe_inv where "fe_inv = (\<lambda>S V v it (V',r).
        (r\<longleftrightarrow>V'\<inter>Collect tgt \<noteq> {})
      \<and> insert v V\<subseteq>V'
      \<and> E``{v} - it \<subseteq> V'
      \<and> V'\<subseteq>reachable
      \<and> S\<subseteq>insert v V
      \<and> (\<not>r \<longrightarrow> E``(V'-S) \<subseteq> V' \<union> it \<and> E``(V'-insert v S) \<subseteq> V'))"

    have vc_pre_initial: "rpre {} ({}, v0)"
      by (auto simp: rpre_def reachable_def)

    {
      (* Case: Node already visited *)
      fix S V v
      assume "rpre S (V,v)"
        and "v\<in>V"
      hence "rpost S (V,v) (V,False)"
        unfolding rpre_def rpost_def
        by auto
    } note vc_node_visited = this

    {
      (* Case: Found node *)
      fix S V v
      assume "tgt v"
      and "rpre S (V,v)"
      hence "rpost S (V,v) (insert v V, True)"
        unfolding rpre_def rpost_def
        by auto
    } note vc_node_found = this

    { 
      fix S V v
      assume "rpre S (V, v)"
      hence "finite (E``{v})"
        unfolding rpre_def using F by (auto)
    } note vc_foreach_finite = this
  
    {
      (* fe_inv initial *)
      fix S V v
      assume A: "v \<notin> V" "\<not>tgt v"
        and PRE: "rpre S (V, v)"
      hence "fe_inv S V v (E``{v}) (insert v V, False)"
        unfolding fe_inv_def rpre_def by (auto)
    } note vc_enter_foreach = this

    {
      (* fe_inv ensures rpre *)
      fix S V v v' it V'
      assume A: "v \<notin> V" "\<not>tgt v" "v' \<in> it" "it \<subseteq> E``{v}"
        and FEI: "fe_inv S V v it (V', False)"
        and PRE: "rpre S (V, v)"

      from A have "v' \<in> E``{v}" by auto
      moreover from PRE have "v \<in> reachable" by (auto simp: rpre_def)
      hence "E``{v} \<subseteq> reachable" by (auto simp: reachable_def)
      ultimately have [simp]: "v'\<in>reachable" by blast

      have "rpre (insert v S) (V', v')"
        unfolding rpre_def
        using FEI PRE by (auto simp: fe_inv_def rpre_def) []
    } note vc_rec_pre = this

    {
      (* rpost implies fe_inv *)
      fix S V V' v v' it Vr''
      assume "fe_inv S V v it (V', False)"
        and "rpost (insert v S) (V', v') Vr''"
      hence "fe_inv S V v (it - {v'}) Vr''"
        unfolding rpre_def rpost_def fe_inv_def
        by clarsimp blast
    } note vc_iterate_foreach = this

    {
      (* fe_inv (completed) implies rpost *)
      fix S V v V'
      assume PRE: "rpre S (V, v)" 
      assume A: "v \<notin> V" "\<not>tgt v"
      assume FEI: "fe_inv S V v {} (V', False)"
      have "rpost S (V, v) (V', False)"
        unfolding rpost_def
        using FEI by (auto simp: fe_inv_def) []
    } note vc_foreach_completed_imp_post = this

    {
      (* fe_inv (interrupted) implies rpost *)
      fix S V v V' it
      assume PRE: "rpre S (V, v)" 
        and A: "v \<notin> V" "\<not>tgt v" "it \<subseteq> E``{v}"
        and FEI: "fe_inv S V v it (V', True)"
      hence "rpost S (V, v) (V', True)"
        by (auto simp add: rpre_def rpost_def fe_inv_def) []
    } note vc_foreach_interrupted_imp_post = this

    {
      fix V r
      assume "rpost {} ({}, v0) (V, r)"
      hence "(r \<longleftrightarrow> reachable \<inter> Collect tgt \<noteq> {}) \<and> (\<not>r\<longrightarrow>V=reachable)"
        by (auto 
          simp: rpost_def reachable_def 
          dest: Image_closed_trancl 
          intro: rev_ImageI)
    } note vc_rpost_imp_spec = this

    show ?thesis
      unfolding dfs_def dfs_spec_def
      apply (refine_rcg refine_vcg)
      apply (rule order_trans)
      
      apply(rule RECT_rule_arb[where 
          pre=rpre 
          and M="\<lambda>a x. SPEC (rpost a x)"
          and V="finite_psupset reachable <*lex*> {}"
          ])
      apply refine_mono
      apply (blast intro: fr)
      apply (rule vc_pre_initial)
      
      apply (refine_rcg refine_vcg 
        FOREACHc_rule'[where I="fe_inv S v s" for S v s]
        )
      apply (simp_all add: vc_node_visited vc_node_found)

      apply (simp add: vc_foreach_finite)

      apply (auto intro: vc_enter_foreach) []

      apply (rule order_trans)
      apply (rprems)
      apply (erule (5) vc_rec_pre)
        apply (auto simp add: fe_inv_def finite_psupset_def) []
        apply (refine_rcg refine_vcg)
        apply (simp add: vc_iterate_foreach)

      apply (auto simp add: vc_foreach_completed_imp_post) []

      apply (auto simp add: vc_foreach_interrupted_imp_post) []

      apply (auto dest: vc_rpost_imp_spec) []
      done
  qed

end

lemma dfs_correct': "(uncurry2 dfs, uncurry2 dfs_spec) 
  \<in> [\<lambda>((E,s),t). finite (reachable E s)]\<^sub>f ((Id\<times>\<^sub>rId)\<times>\<^sub>rId) \<rightarrow> \<langle>Id\<rangle>nres_rel"  
  apply (intro frefI nres_relI; clarsimp)
  by (rule dfs_correct)


subsection \<open>Refinement to Imperative/HOL\<close>

text \<open>We set up a schematic proof goal,
  and use the sepref-tool to synthesize the implementation.
\<close>

sepref_definition dfs_impl is 
  "uncurry2 dfs" :: "(adjg_assn nat_assn)\<^sup>k*\<^sub>anat_assn\<^sup>k*\<^sub>a(pure (nat_rel \<rightarrow> bool_rel))\<^sup>k \<rightarrow>\<^sub>a prod_assn (ias.assn nat_assn) bool_assn"
  unfolding dfs_def[abs_def] \<comment> \<open>Unfold definition of DFS\<close>
  using [[goals_limit = 1]]
  apply (rewrite in "RECT _ (\<hole>,_)" ias.fold_custom_empty) \<comment> \<open>Select impls\<close>
  apply (rewrite in "if \<hole> then RETURN (_,True) else _" fold_pho_apply)
  apply sepref \<comment> \<open>Invoke sepref-tool\<close>
  done
export_code dfs_impl checking SML_imp
  \<comment> \<open>Generate SML code with Imperative/HOL\<close>

export_code dfs_impl in Haskell module_name DFS


text \<open>Finally, correctness is shown by combining the 
  generated refinement theorem with the abstract correctness theorem.\<close>

lemmas dfs_impl_correct' = dfs_impl.refine[FCOMP dfs_correct']

corollary dfs_impl_correct:
  "finite (reachable E s) \<Longrightarrow> 
  <adjg_assn nat_assn E Ei> 
    dfs_impl Ei s tgt
  < \<lambda>(Vi,r). \<exists>\<^sub>AV. adjg_assn nat_assn E Ei * ias.assn nat_assn V Vi * \<up>((r \<longleftrightarrow> reachable E s \<inter> Collect tgt \<noteq> {}) \<and> (\<not>r \<longrightarrow> V=reachable E s) ) >\<^sub>t"
  using dfs_impl_correct'[THEN hfrefD, THEN hn_refineD, of "((E,s),tgt)" "((Ei,s),tgt)", simplified]
  apply (rule cons_rule[rotated -1])
  apply (sep_auto intro!: ent_ex_preI simp: dfs_spec_def pure_def)+
  done


end

