section \<open>Find a Feedback Arc Set\<close>
theory Feedback_Arcs
imports   
  "../DFS_Framework"
  CAVA_Automata.Digraph_Impl
  Reachable_Nodes
begin
text \<open>A feedback arc set is a set of edges that breaks all reachable cycles.
  In this theory, we define an algorithm to find a feedback arc set.\<close>
definition is_fas :: "('v, 'more) graph_rec_scheme \<Rightarrow> 'v rel \<Rightarrow> bool" where
  "is_fas G EC \<equiv> \<not>(\<exists> u \<in> (g_E G)\<^sup>* `` g_V0 G. (u, u) \<in> (g_E G - EC)\<^sup>+)"

lemma is_fas_alt:
  "is_fas G EC = acyclic ((g_E G \<inter> ((g_E G)\<^sup>* `` g_V0 G \<times> UNIV) - EC))"
  unfolding is_fas_def acyclic_def
proof (clarsimp, safe)
  fix u
  assume A: "(u,u) \<in> (g_E G \<inter> (g_E G)\<^sup>* `` g_V0 G \<times> UNIV - EC)\<^sup>+"
  hence "(u,u)\<in>(g_E G - EC)\<^sup>+" by (rule trancl_mono) blast
  moreover from A have "u \<in> (g_E G)\<^sup>* `` g_V0 G" by (cases rule: converse_tranclE) auto
  moreover assume "\<forall>u\<in>(g_E G)\<^sup>* `` g_V0 G. (u, u) \<notin> (g_E G - EC)\<^sup>+"
  ultimately show False by blast
next
  fix u v0
  assume 1: "v0\<in>g_V0 G" and 2: "(v0,u)\<in>(g_E G)\<^sup>*" and 3: "(u,u)\<in>(g_E G - EC)\<^sup>+"
  have "(u, u) \<in> (Restr (g_E G - EC) ((g_E G)\<^sup>* `` g_V0 G))\<^sup>+"
    apply (rule trancl_restrict_reachable[OF 3, where S="(g_E G)\<^sup>* `` g_V0 G"])
    apply (rule order_trans[OF _ rtrancl_image_unfold_right])
    using 1 2 by auto
  hence "(u, u) \<in> (g_E G \<inter> (g_E G)\<^sup>* `` g_V0 G \<times> UNIV - EC)\<^sup>+"
    by (rule trancl_mono) auto
  moreover assume "\<forall>x. (x, x) \<notin> (g_E G \<inter> (g_E G)\<^sup>* `` g_V0 G \<times> UNIV - EC)\<^sup>+"
  ultimately show False by blast
qed

subsection \<open>Instantiation of the DFS-Framework\<close>
record 'v fas_state = "'v state" +
  fas :: "('v\<times>'v) set"

(* Some utility lemmas for the simplifier, to handle idiosyncrasies of
  the record package. *)
lemma fas_more_cong: "state.more s = state.more s' \<Longrightarrow> fas s = fas s'"
  by (cases s, cases s', simp)

lemma [simp]: "s\<lparr> state.more := \<lparr> fas = foo \<rparr> \<rparr> = s \<lparr> fas := foo \<rparr>"
  by (cases s) simp

definition fas_params :: "('v,('v,unit) fas_state_ext) parameterization"
where "fas_params \<equiv> dflt_parametrization state.more 
  (RETURN \<lparr> fas = {} \<rparr>) \<lparr>
    on_back_edge := \<lambda>u v s. RETURN \<lparr> fas = insert (u,v) (fas s) \<rparr>
  \<rparr>"
lemmas fas_params_simp[simp] = 
  gen_parameterization.simps[mk_record_simp, OF fas_params_def[simplified]]

interpretation fas: param_DFS_defs where param=fas_params for G .

text \<open> Find feedback arc set \<close>
definition "find_fas G \<equiv> do {
  ASSERT (graph G);
  ASSERT (finite ((g_E G)\<^sup>* `` g_V0 G));
  s \<leftarrow> fas.it_dfsT TYPE('a) G;
  RETURN (fas_state.fas s)
}"

locale fas =
  param_DFS G fas_params
  for G :: "('v, 'more) graph_rec_scheme" 
  +
  assumes finite_reachable[simp, intro!]: "finite ((g_E G)\<^sup>* `` g_V0 G)"
begin

  sublocale DFS G fas_params
    apply unfold_locales
    apply (simp_all add: fas_params_def)
    done

end

lemma fasI:
  assumes "graph G"
  assumes "finite ((g_E G)\<^sup>* `` g_V0 G)"
  shows "fas G"
proof -
  interpret graph G by fact
  interpret fb_graph G by (rule fb_graphI_fr[OF assms(2)])
  show ?thesis by unfold_locales fact
qed

subsection \<open>Correctness Proof\<close>

locale fas_invar = DFS_invar where param = fas_params + fas
begin

  lemma (in fas) i_fas_eq_back: "is_invar (\<lambda>s. fas_state.fas s = back_edges s)"
    apply (induct rule: establish_invarI)
    apply (simp_all add: cond_def cong: fas_more_cong)
    apply (simp add: empty_state_def)
    done
  lemmas fas_eq_back = i_fas_eq_back[THEN make_invar_thm]

  lemma find_fas_correct_aux:
    assumes NC: "\<not>cond s"
    shows "is_fas G (fas_state.fas s)"
  proof -
    note [simp] = fas_eq_back  

    from nc_edges_covered[OF NC] edges_disjoint have 
      "E \<inter> reachable \<times> UNIV - back_edges s = tree_edges s \<union> cross_edges s"
      by auto
    with tree_cross_acyclic show "is_fas G (fas_state.fas s)"
      unfolding is_fas_alt by simp
  qed    

end

lemma find_fas_correct:
  assumes "graph G"
  assumes "finite ((g_E G)\<^sup>* `` g_V0 G)"
  shows "find_fas G \<le> SPEC (is_fas G)"
  unfolding find_fas_def
proof (refine_vcg le_ASSERTI order_trans[OF DFS.it_dfsT_correct], clarsimp_all)
  interpret graph G by fact
  assume "finite ((g_E G)\<^sup>* `` g_V0 G)"
  then interpret fb_graph G by (rule fb_graphI_fr)
  interpret fas by unfold_locales fact
  show "DFS G fas_params" by unfold_locales
next
  fix s
  assume "DFS_invar G fas_params s"
  then interpret DFS_invar G fas_params s .
  interpret fas_invar G s by unfold_locales fact
  assume "\<not>fas.cond TYPE('b) G s"
  thus "is_fas G (fas_state.fas s)"
    by (rule find_fas_correct_aux)
qed (rule assms)+

subsection \<open>Implementation\<close>

(* Implementation with stack and sso_visited set *)
record 'v fas_state_impl = "'v simple_state" +
  fas :: "('v\<times>'v) set"

(* Definition of refinement relation: The break-flag is refined by identity.*)
definition "fas_erel \<equiv> { 
  (\<lparr> fas_state_impl.fas = f \<rparr>, \<lparr> fas_state.fas = f\<rparr>) | f. True }"
abbreviation "fas_rel \<equiv> \<langle>fas_erel\<rangle>simple_state_rel"

(* Implementation of the parameters *)
definition fas_params_impl 
  :: "('v,'v fas_state_impl,('v,unit) fas_state_impl_ext) gen_parameterization"
where "fas_params_impl 
  \<equiv> dflt_parametrization simple_state.more (RETURN \<lparr> fas = {} \<rparr>) \<lparr>
  on_back_edge := \<lambda>u v s. RETURN \<lparr> fas = insert (u,v) (fas s) \<rparr>\<rparr>"
lemmas fas_params_impl_simp[simp,DFS_code_unfold] = 
  gen_parameterization.simps[mk_record_simp, OF fas_params_impl_def[simplified]]

lemma fas_impl: "(si,s)\<in>fas_rel 
  \<Longrightarrow> fas_state_impl.fas si = fas_state.fas s"
  by (cases si, cases s, simp add: simple_state_rel_def fas_erel_def)

interpretation fas_impl: simple_impl_defs G fas_params_impl fas_params 
  for G .

(* The above locale creates an iterative and a recursive implementation *)
term fas_impl.tailrec_impl term fas_impl.tailrec_implT term fas_impl.rec_impl

definition [DFS_code_unfold]: "find_fas_impl G \<equiv> do {
  ASSERT (graph G);
  ASSERT (finite ((g_E G)\<^sup>* `` g_V0 G));
  s \<leftarrow> fas_impl.tailrec_implT TYPE('a) G;
  RETURN (fas s)
}"


context fas begin
  (* Derive the implementation *)
  sublocale simple_impl G fas_params fas_params_impl fas_erel 
    apply unfold_locales
    apply (intro fun_relI, clarsimp simp: simple_state_rel_def, parametricity) []
    apply (auto simp: fas_erel_def fas_impl simple_state_rel_def)
    done

  lemmas impl_refine = simple_tailrec_refine simple_tailrecT_refine simple_rec_refine
  thm simple_refine
end

lemma find_fas_impl_refine: "find_fas_impl G \<le> \<Down>Id (find_fas G)"
  unfolding find_fas_impl_def find_fas_def
  apply (refine_vcg fas.impl_refine)
  apply (simp_all add: fas_impl fasI)
  done
  
    
subsection \<open>Synthesis of Executable Code\<close>
(* Autoref *)
record ('si,'nsi,'fsi)fas_state_impl' = "('si,'nsi)simple_state_impl" +
  fas_impl :: 'fsi

definition [to_relAPP]: "fas_state_erel frel erel \<equiv> {
  (\<lparr>fas_impl = fi, \<dots> =  mi\<rparr>,\<lparr>fas = f, \<dots> = m\<rparr>) | fi mi f m.
    (fi,f)\<in>frel \<and> (mi,m)\<in>erel}"

consts 
  i_fas_state_ext :: "interface \<Rightarrow> interface \<Rightarrow> interface"

lemmas [autoref_rel_intf] = REL_INTFI[of fas_state_erel i_fas_state_ext]


term fas_update
term fas_state_impl'.fas_impl_update
lemma [autoref_rules]:
  fixes ns_rel vis_rel frel erel
  defines "R \<equiv> \<langle>ns_rel,vis_rel,\<langle>frel,erel\<rangle>fas_state_erel\<rangle>ss_impl_rel"
  shows 
    "(fas_state_impl'_ext, fas_state_impl_ext) \<in> frel \<rightarrow> erel \<rightarrow> \<langle>frel,erel\<rangle>fas_state_erel"
    "(fas_impl, fas_state_impl.fas) \<in> R \<rightarrow> frel"
    "(fas_state_impl'.fas_impl_update, fas_update) \<in> (frel \<rightarrow> frel) \<rightarrow> R \<rightarrow> R"
  unfolding fas_state_erel_def ss_impl_rel_def R_def
  by (auto, parametricity)

schematic_goal find_fas_impl:
  fixes V :: "('vi\<times>'v) set"
  assumes [autoref_ga_rules]: "is_bounded_hashcode V eq bhc"
  assumes [autoref_rules]: "(eq,(=)) \<in> V \<rightarrow> V \<rightarrow> bool_rel"
  assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE ('vi) sz"
  assumes [autoref_rules]: 
    "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
  notes [autoref_tyrel] = 
    TYRELI[where R="\<langle>V\<rangle>ahs_rel bhc"]
    TYRELI[where R="\<langle>V \<times>\<^sub>r V\<rangle>ahs_rel (prod_bhc bhc bhc)"]
    TYRELI[where R="\<langle>V \<times>\<^sub>r \<langle>V\<rangle>list_set_rel\<rangle>ras_rel"]
  shows "RETURN (?c::?'c) \<le>\<Down>?R (find_fas_impl G)"
  unfolding DFS_code_unfold
  using [[autoref_trace_failed_id, goals_limit=1]]
  apply (autoref_monadic (trace))
  done
concrete_definition find_fas_code for eq bhc sz Gi uses find_fas_impl
export_code find_fas_code checking SML

thm find_fas_code.refine

lemma find_fas_code_refine[refine]:
  fixes V :: "('vi\<times>'v) set"
  assumes "is_bounded_hashcode V eq bhc"
  assumes "(eq,(=)) \<in> V \<rightarrow> V \<rightarrow> bool_rel"
  assumes "is_valid_def_hm_size TYPE ('vi) sz"
  assumes 2: "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
  shows "RETURN (find_fas_code eq bhc sz Gi) \<le> \<Down>(\<langle>V\<times>\<^sub>rV\<rangle>ahs_rel (prod_bhc bhc bhc)) (find_fas G)"
proof -
  note find_fas_code.refine[OF assms]
  also note find_fas_impl_refine
  finally show ?thesis .
qed

context begin interpretation autoref_syn .

text \<open>Declare this algorithm to Autoref:\<close>
theorem find_fas_code_autoref[autoref_rules]:
  fixes V :: "('vi\<times>'v) set" and bhc
  defines "RR \<equiv> \<langle>\<langle>V\<times>\<^sub>rV\<rangle>ahs_rel (prod_bhc bhc bhc)\<rangle>nres_rel"
  assumes BHC: "SIDE_GEN_ALGO (is_bounded_hashcode V eq bhc)"
  assumes EQ: "GEN_OP eq (=) (V \<rightarrow> V \<rightarrow> bool_rel)"
  assumes VDS: "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE ('vi) sz)"
  assumes 2: "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
  shows "(RETURN (find_fas_code eq bhc sz Gi),
    (OP find_fas 
      ::: \<langle>Rm, V\<rangle>g_impl_rel_ext \<rightarrow> RR)$G)\<in>RR"
  unfolding RR_def
  apply (rule nres_relI)
  using assms 
  by (simp add: find_fas_code_refine)  

end

subsection \<open>Feedback Arc Set with Initialization\<close>
text \<open>This algorithm extends a given set to a feedback arc set. It works in two steps:
  \<^enum> Determine set of reachable nodes
  \<^enum> Construct feedback arc set for graph without initial set
\<close>

definition find_fas_init where
  "find_fas_init G FI \<equiv> do {
    ASSERT (graph G);
    ASSERT (finite ((g_E G)\<^sup>* `` g_V0 G));
    let nodes = (g_E G)\<^sup>* `` g_V0 G;
    fas \<leftarrow> find_fas \<lparr> g_V = g_V G, g_E = g_E G - FI, g_V0 = nodes \<rparr>;
    RETURN (FI \<union> fas)
  }"

text \<open>The abstract idea:
  To find a feedback arc set that contains some set F2,
  we can find a feedback arc set for the graph with F2 removed,
  and then join with F2.
\<close>
lemma is_fas_join: "is_fas G (F1 \<union> F2) \<longleftrightarrow>
  is_fas \<lparr> g_V = g_V G, g_E = g_E G - F2, g_V0 = (g_E G)\<^sup>* `` g_V0 G \<rparr> F1"
  unfolding is_fas_def
  apply (auto simp: set_diff_diff_left Un_commute)
  by (metis ImageI rtrancl_trans subsetCE rtrancl_mono[of "g_E G - F2" "g_E G", OF Diff_subset]) 

lemma graphI_init:
  assumes "graph G"
  shows "graph \<lparr> g_V = g_V G, g_E = g_E G - FI, g_V0 = (g_E G)\<^sup>* `` g_V0 G \<rparr>"
proof -
  interpret graph G by fact
  show ?thesis
    apply unfold_locales
    using reachable_V apply simp
    using E_ss apply force
    done
qed

lemma find_fas_init_correct:
  assumes [simp, intro!]: "graph G"
  assumes [simp, intro!]: "finite ((g_E G)\<^sup>* `` g_V0 G)"
  shows "find_fas_init G FI \<le> SPEC (\<lambda>fas. is_fas G fas \<and> FI \<subseteq> fas)"
  unfolding find_fas_init_def
  apply (refine_vcg order_trans[OF find_fas_correct])
  apply clarsimp_all
  apply (rule graphI_init)
  apply simp
  apply (rule finite_subset[rotated], rule assms)
  apply (metis Diff_subset Image_closed_trancl reachable_mono 
    rtrancl_image_unfold_right rtrancl_reflcl rtrancl_trancl_reflcl 
    trancl_rtrancl_absorb)
  apply (simp add: is_fas_join[where ?F2.0=FI] Un_commute)
  done


lemma gen_cast_set[autoref_rules_raw]:
  assumes PRIO_TAG_GEN_ALGO
  assumes INS: "GEN_OP ins Set.insert (Rk\<rightarrow>\<langle>Rk\<rangle>Rs2\<rightarrow>\<langle>Rk\<rangle>Rs2)"
  assumes EM: "GEN_OP emp {} (\<langle>Rk\<rangle>Rs2)"
  assumes IT: "SIDE_GEN_ALGO (is_set_to_list Rk Rs1 tsl)"
  shows "(\<lambda>s. gen_union (\<lambda>x. foldli (tsl x)) ins s emp,CAST) 
    \<in> (\<langle>Rk\<rangle>Rs1) \<rightarrow> (\<langle>Rk\<rangle>Rs2)"
proof -
  note [autoref_rules] = GEN_OP_D[OF INS]
  note [autoref_rules] = GEN_OP_D[OF EM]
  note [autoref_ga_rules] = SIDE_GEN_ALGO_D[OF IT]
  have 1: "CAST = (\<lambda>s. s \<union> {})" by auto
  show ?thesis
    unfolding 1
    by autoref
qed

lemma gen_cast_fun_set_rel[autoref_rules_raw]:
  assumes INS: "GEN_OP mem (\<in>) (Rk\<rightarrow>\<langle>Rk\<rangle>Rs\<rightarrow>bool_rel)"
  shows "(\<lambda>s x. mem x s,CAST) \<in> (\<langle>Rk\<rangle>Rs) \<rightarrow> (\<langle>Rk\<rangle>fun_set_rel)"
proof -
  have A: "\<And>s. (\<lambda>x. x\<in>s,CAST s) \<in> br Collect (\<lambda>_. True)"
    by (auto simp: br_def)
    
  show ?thesis
    unfolding fun_set_rel_def
    apply rule
    apply rule
    defer
    apply (rule A)
    using INS[simplified]
    apply parametricity
    done
qed  


lemma find_fas_init_impl_aux_unfolds: 
  "Let (E\<^sup>*``V0) = Let (CAST (E\<^sup>*``V0))" 
  "(\<lambda>S. RETURN (FI \<union> S)) = (\<lambda>S. RETURN (FI \<union> CAST S))"
  by simp_all


schematic_goal find_fas_init_impl:
  fixes V :: "('vi\<times>'v) set" and bhc
  assumes [autoref_ga_rules]: "is_bounded_hashcode V eq bhc"
  assumes [autoref_rules]: "(eq,(=)) \<in> V \<rightarrow> V \<rightarrow> bool_rel"
  assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE ('vi) sz"
  assumes [autoref_rules]: 
    "(Gi, G) \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext"
    "(FIi,FI)\<in>\<langle>V\<times>\<^sub>rV\<rangle>fun_set_rel"
  shows "RETURN (?c::?'c) \<le>\<Down>?R (find_fas_init G FI)"
  unfolding find_fas_init_def
  unfolding find_fas_init_impl_aux_unfolds
  by (autoref_monadic (plain,trace))

concrete_definition find_fas_init_code for eq bhc sz Gi FIi
  uses find_fas_init_impl
export_code find_fas_init_code checking SML

context begin interpretation autoref_syn .

text \<open>The following theorem declares our implementation to Autoref:\<close>
theorem find_fas_init_code_autoref[autoref_rules]:
  fixes V :: "('vi\<times>'v) set" and bhc
  defines "RR \<equiv> \<langle>V\<times>\<^sub>rV\<rangle>fun_set_rel"
  assumes "SIDE_GEN_ALGO (is_bounded_hashcode V eq bhc)"
  assumes "GEN_OP eq (=) (V \<rightarrow> V \<rightarrow> bool_rel)"
  assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE ('vi) sz)"
  shows "(\<lambda>Gi FIi. RETURN (find_fas_init_code eq bhc sz Gi FIi),find_fas_init) 
    \<in> \<langle>Rm, V\<rangle>g_impl_rel_ext \<rightarrow> RR \<rightarrow> \<langle>RR\<rangle>nres_rel"
  unfolding RR_def
  apply (intro fun_relI nres_relI)
  using assms
  by (simp add: find_fas_init_code.refine)

end

subsection \<open>Conclusion\<close>
text \<open>
  We have defined an algorithm to find a feedback arc set, and one to 
  extend a given set to a feedback arc set. We have registered them to Autoref
  as implementations for @{const find_fas} and @{const find_fas_init}.

  For preliminary refinement steps, you need the theorems  
  @{thm [source] find_fas_correct} and @{thm [source] find_fas_init_correct}.
\<close>

thm find_fas_code_autoref find_fas_init_code_autoref
thm find_fas_correct thm find_fas_init_correct


end

