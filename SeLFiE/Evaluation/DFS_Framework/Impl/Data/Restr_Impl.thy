section \<open>Restricting Nodes by Pre-Initializing Visited Set\<close>
theory Restr_Impl
imports Simple_Impl
begin
text \<open>
  Implementation of node and edge restriction via pre-initialized visited set.

  We now further refine the simple implementation in case that the graph has
  the form \<open>G'=(rel_restrict E R, V0-R)\<close> for some \<open>fb_graph G=(E,V0)\<close>.
  If, additionally, the parameterization is not "too sensitive" to the 
  visited set, we can pre-initialize the visited set with \<open>R\<close>, and use the
  \<open>V0\<close> and \<open>E\<close> of \<open>G\<close>. This may be a more efficient implementation 
  than explicitely
  restricting \<open>V0\<close> and \<open>E\<close>, as it saves additional membership queries in \<open>R\<close> 
  on each successor function call. 
  
  Moreover, in applications where the restriction is updated between multiple 
  calls, we can use one linearly accessed restriction set.
\<close>

definition "restr_rel R \<equiv> { (s,s'). 
  (ss_stack s, ss_stack s')\<in>\<langle>Id \<times>\<^sub>r {(U,U'). U-R = U'}\<rangle>list_rel 
\<and> on_stack s = on_stack s'
\<and> visited s = visited s' \<union> R \<and> visited s' \<inter> R = {}
\<and> simple_state.more s = simple_state.more s' }"

lemma restr_rel_simps:
  assumes "(s,s')\<in>restr_rel R"
  shows "visited s = visited s' \<union> R"
  and "simple_state.more s = simple_state.more s'"
  using assms unfolding restr_rel_def by auto

lemma 
  assumes "(s,s')\<in>restr_rel R"
  shows restr_rel_stackD: "(ss_stack s, ss_stack s') \<in> \<langle>Id \<times>\<^sub>r {(U,U'). U-R = U'}\<rangle>list_rel"
  and restr_rel_vis_djD: "visited s' \<inter> R = {}"
  using assms unfolding restr_rel_def by auto

context fixes R :: "'v set" begin
  definition [to_relAPP]: "restr_simple_state_rel ES \<equiv> { (s,s') .
    (ss_stack s, map (\<lambda>u. (u,pending s' `` {u})) (stack s')) 
      \<in> \<langle>Id \<times>\<^sub>r {(U,U'). U-R = U'}\<rangle>list_rel \<and>
    on_stack s = set (stack s') \<and>
    visited s = dom (discovered s') \<union> R \<and> dom (discovered s') \<inter> R = {} \<and>
    dom (finished s') = dom (discovered s') - set (stack s') \<and>
    set (stack s') \<subseteq> dom (discovered s') \<and>
    (simple_state.more s, state.more s') \<in> ES
  }"
end

lemma restr_simple_state_rel_combine: 
  "\<langle>ES\<rangle>restr_simple_state_rel R = restr_rel R O \<langle>ES\<rangle>simple_state_rel"
  unfolding restr_simple_state_rel_def
  apply (intro equalityI subsetI)
    apply clarify
    apply (rule relcompI[OF _ simple_state_relI], auto simp: restr_rel_def) []

    apply (auto simp: restr_rel_def simple_state_rel_def) []
  done


text \<open>
  Locale that assumes a simple implementation, makes some 
  additional assumptions on the parameterization (intuitively, that it
  is not too sensitive to adding nodes from R to the visited set), and then
  provides a new implementation with pre-initialized visited set.
\<close>
(* 
  TODO/FIXME: The refinement step from simple_impl is not yet clean,
    as the parameterizatioin refinement is not handled properly.
    Ideally, one would assume the required parameterization refinement
    w.r.t. restr_simple_state_rel, and derive the refinement for 
    simple_state_rel.
 
*)

locale restricted_impl_defs =
  graph_defs G +
  a: simple_impl_defs "graph_restrict G R"
  for G :: "('v, 'more) graph_rec_scheme"
  and R
begin
  sublocale pre_simple_impl G .

  abbreviation "rel \<equiv> restr_rel R"

  definition "gbs' \<equiv> gbs \<lparr> 
    gbs_init := \<lambda>e. RETURN 
      \<lparr> ss_stack=[], on_stack={}, visited = R, \<dots>=e \<rparr> \<rparr>"

  lemmas gbs'_simps[simp, DFS_code_unfold]
    = gen_basic_dfs_struct.simps[mk_record_simp, OF gbs'_def[unfolded gbs_simps]]

  sublocale gen_param_dfs_defs gbs' parami simple_state.more_update V0 .
  
  (* Seems to be fixed in Isabelle-2016
  (* Some ad-hoc fix for locale abbreviations not being properly printed *)
  abbreviation (output) "abbrev_gen_dfs \<equiv> gen_dfs"
  abbreviation (output) "abbrev__gen_cond \<equiv> gen_cond"
  abbreviation (output) "abbrev__gen_step \<equiv> gen_step"

  abbreviation (output) "abbrev__ac_gen_dfs \<equiv> a.c.gen_dfs"
  abbreviation (output) "abbrev__ac_gen_cond \<equiv> a.c.gen_cond"
  abbreviation (output) "abbrev__ac_gen_step \<equiv> a.c.gen_step"

  abbreviation "abbrev_do_new_root \<equiv> do_new_root"
  abbreviation "abbrev_do_cross_edge \<equiv> do_cross_edge"
  abbreviation "abbrev_do_back_edge \<equiv> do_back_edge"
  abbreviation "abbrev_do_discover \<equiv> do_discover"
  abbreviation "abbrev_do_finish \<equiv> do_finish"

  abbreviation "abbrev_ac_do_new_root \<equiv> a.c.do_new_root"
  abbreviation "abbrev_ac_do_cross_edge \<equiv> a.c.do_cross_edge"
  abbreviation "abbrev_ac_do_back_edge \<equiv> a.c.do_back_edge"
  abbreviation "abbrev_ac_do_discover \<equiv> a.c.do_discover"
  abbreviation "abbrev_ac_do_finish \<equiv> a.c.do_finish"
  *)


  sublocale tailrec_impl_defs G gds .
end

locale restricted_impl = 
  fb_graph +
  a: simple_impl "graph_restrict G R" +
  restricted_impl_defs +
  
  (* Cross and back edges must not cause any effect. 
    Intuitively, we will see spurious cross edges to nodes from R.
    TODO/FIXME: The condition here is a quite crude over-approximation!
    *)
  assumes [simp]: "on_cross_edge parami = (\<lambda>u v s. RETURN (simple_state.more s))"
  assumes [simp]: "on_back_edge parami = (\<lambda>u v s. RETURN (simple_state.more s))"

  (* TODO/FIXME: The next 4 are crude approximations. One should include
    some precondition! *)
  assumes is_break_refine: 
    "\<lbrakk> (s,s')\<in>restr_rel R \<rbrakk> 
      \<Longrightarrow> is_break parami s \<longleftrightarrow> is_break parami s'"

  assumes on_new_root_refine: 
    "\<lbrakk> (s,s')\<in>restr_rel R \<rbrakk> 
      \<Longrightarrow> on_new_root parami v0 s \<le> on_new_root parami v0 s'"

  assumes on_finish_refine: 
    "\<lbrakk> (s,s')\<in>restr_rel R \<rbrakk> 
      \<Longrightarrow> on_finish parami u s \<le> on_finish parami u s'"

  assumes on_discover_refine: 
    "\<lbrakk> (s,s')\<in>restr_rel R \<rbrakk> 
      \<Longrightarrow> on_discover parami u v s \<le> on_discover parami u v s'"

begin

  lemmas rel_def = restr_rel_def[where R=R]
  sublocale gen_param_dfs gbs' parami simple_state.more_update V0 .

  lemma is_break_param'[param]: "(is_break parami, is_break parami)\<in>rel \<rightarrow> bool_rel"
    using is_break_refine unfolding rel_def by auto

  lemma do_init_refine[refine]: "do_init \<le> \<Down> rel (a.c.do_init)"
    unfolding do_action_defs a.c.do_action_defs
    apply (simp add: rel_def a.c.init_impl_def)
    apply refine_rcg
    apply simp
    done

  lemma gen_cond_param: "(gen_cond,a.c.gen_cond)\<in>rel \<rightarrow> bool_rel"
    apply (clarsimp simp del: graph_restrict_simps)
    apply (frule is_break_param'[param_fo])
    unfolding gen_cond_def a.c.gen_cond_def rel_def
    apply simp
    unfolding a.c.is_discovered_impl_def a.c.is_empty_stack_impl_def
    by auto


  lemma cross_back_id[simp]: 
    "do_cross_edge u v s = RETURN s"
    "do_back_edge u v s = RETURN s"
    "a.c.do_cross_edge u v s = RETURN s"
    "a.c.do_back_edge u v s = RETURN s"
    unfolding do_action_defs a.c.do_action_defs
    by simp_all

  lemma pred_rel_simps:
    assumes "(s,s')\<in>rel"
    shows "a.c.is_discovered_impl u s \<longleftrightarrow> a.c.is_discovered_impl u s' \<or> u\<in>R"
    and "a.c.is_empty_stack_impl s \<longleftrightarrow> a.c.is_empty_stack_impl s'"
    using assms
    unfolding a.c.is_discovered_impl_def a.c.is_empty_stack_impl_def 
    unfolding rel_def
    by auto

  lemma no_pending_refine:
    assumes "(s,s')\<in>rel" "\<not>a.c.is_empty_stack_impl s'"
    shows "(hd (ss_stack s) = (u,{})) \<Longrightarrow> hd (ss_stack s') = (u,{})"
    using assms
    unfolding a.c.is_empty_stack_impl_def rel_def
    apply (cases "ss_stack s'", simp)
    apply (auto elim: list_relE)
    done

  lemma do_new_root_refine[refine]:
    "\<lbrakk> (v0i,v0)\<in>Id; (si,s)\<in>rel; v0\<notin>R \<rbrakk> 
      \<Longrightarrow> do_new_root v0i si \<le> \<Down> rel (a.c.do_new_root v0 s)"  
    unfolding do_action_defs a.c.do_action_defs
    apply refine_rcg
    apply (rule intro_prgR[where R=rel])
    apply (simp add: a.c.new_root_impl_def new_root_impl_def)
    apply (refine_rcg,auto simp: rel_def rel_restrict_def) []

    apply (rule intro_prgR[where R=Id])
    apply (simp add: on_new_root_refine)
    apply (simp add: rel_def)
    done

  lemma do_finish_refine[refine]:
    "\<lbrakk>(s, s') \<in> rel; (u,u')\<in>Id\<rbrakk>
       \<Longrightarrow> do_finish u s \<le> \<Down> rel (a.c.do_finish u' s')"
    unfolding do_action_defs a.c.do_action_defs
    apply refine_rcg
    apply (rule intro_prgR[where R=rel])
    apply (simp add: finish_impl_def is_empty_stack_impl_def)
    apply (refine_rcg,auto simp: rel_def rel_restrict_def) []
    apply parametricity

    apply (rule intro_prgR[where R=Id])
    apply (simp add: on_finish_refine)
    apply (simp add: rel_def)
    done

  lemma aux_cnv_pending: 
    "\<lbrakk> (s, s') \<in> rel; 
      \<not> is_empty_stack_impl s; vs\<in>Vs; vs\<notin>R;
      hd (ss_stack s) = (u,Vs) \<rbrakk> \<Longrightarrow>
      hd (ss_stack s') = (u,insert vs (Vs-R))"
    (* Conc-Pending node that is also in abs-visited is also abs-pending *)
    unfolding rel_def is_empty_stack_impl_def
    apply (cases "ss_stack s'", simp)
    apply (auto elim: list_relE)
    done
    

  lemma get_pending_refine: 
    assumes "(s, s') \<in> rel" "gen_cond s" "\<not> is_empty_stack_impl s"
    shows "
      get_pending_impl s \<le> (sup 
        (\<Down>(Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel \<times>\<^sub>r rel) (inf 
          (get_pending_impl s') 
          (SPEC (\<lambda>(_,Vs,_). case Vs of None \<Rightarrow> True | Some v \<Rightarrow> v\<notin>R))))
        (\<Down>(Id \<times>\<^sub>r \<langle>Id\<rangle>option_rel \<times>\<^sub>r rel) (
          SPEC (\<lambda>(u,Vs,s''). \<exists>v. Vs=Some v \<and> v\<in>R \<and> s''=s') 
        )))"
  proof -
    from assms have 
      [simp]: "ss_stack s' \<noteq> []"
      and [simp]: "ss_stack s \<noteq> []"
      unfolding rel_def impl_defs 
      apply (auto)
      done

    from assms show ?thesis
      unfolding get_pending_impl_def
      apply (subst Let_def, subst Let_def)
      apply (rule ASSERT_leI)
      apply (auto simp: impl_defs gen_cond_def rel_def) [] 

      apply (split prod.split, intro allI impI)      
      apply (rule lhs_step_If)
        (* No pending *)
        apply (rule le_supI1)
        apply (simp add: pred_rel_simps no_pending_refine restr_rel_simps
          RETURN_RES_refine_iff)
  
        (* Pending *)
        apply (rule lhs_step_bind, simp)
        apply (simp split del: if_split)
        apply (rename_tac v)
        apply (case_tac "v\<in>R")
          (* Spurious node from R *)
          apply (rule le_supI2)
          apply (rule RETURN_SPEC_refine)
          apply (auto simp: rel_def is_empty_stack_impl_def neq_Nil_conv) []
          apply (cases "ss_stack s'", simp) apply (auto elim!: list_relE) []
  
          (* Non-spurious node *)
          apply (rule le_supI1)
          apply (frule (4) aux_cnv_pending)
          apply (simp add: no_pending_refine pred_rel_simps memb_imp_not_empty)
          apply (subst nofail_inf_serialize, 
            (simp_all add: refine_pw_simps split: prod.splits) [2])
          apply simp
          apply (rule rhs_step_bind_RES, blast)
          apply (simp add: rel_def is_empty_stack_impl_def) []
          apply (cases "ss_stack s'", simp)
          apply (auto elim: list_relE) []
      done
  qed

  lemma do_discover_refine[refine]:
    "\<lbrakk> (s, s') \<in> rel; (u,u')\<in>Id; (v,v')\<in>Id; v' \<notin> R \<rbrakk>
       \<Longrightarrow> do_discover u v s \<le> \<Down> rel (a.c.do_discover u' v' s')"
    unfolding do_action_defs a.c.do_action_defs
    apply refine_rcg
      apply (rule intro_prgR[where R=rel])
      apply (simp add: discover_impl_def a.c.discover_impl_def)
      apply (refine_rcg,auto simp: rel_def rel_restrict_def) []

      apply (rule intro_prgR[where R=Id])
      apply (simp add: on_discover_refine)

      apply (auto simp: rel_def) []
    done

  lemma aux_R_node_discovered: "\<lbrakk>(s,s')\<in>rel; v\<in>R\<rbrakk> \<Longrightarrow> is_discovered_impl v s"
    by (auto simp: pred_rel_simps)

  lemma re_refine_aux: "gen_dfs \<le> \<Down>rel a.c.gen_dfs"
    unfolding a.c.gen_dfs_def gen_dfs_def
    apply (simp del: graph_restrict_simps)
    (* Some manual refinements for finer control *)
    apply (rule bind_refine)
    apply (refine_rcg)
    apply (erule WHILE_invisible_refine)

    (* Condition *)
    apply (frule gen_cond_param[param_fo], fastforce)

    (* Step *)
    apply (frule (1) gen_cond_param[param_fo, THEN IdD, THEN iffD1])
    apply (simp del: graph_restrict_simps)
    unfolding gen_step_def
    apply (simp del: graph_restrict_simps cong: if_cong option.case_cong split del: if_split)
    apply (rule lhs_step_If)
      (* new_root *)
      apply (frule (1) pred_rel_simps[THEN iffD1])
      apply (rule le_supI1)
      apply (simp add: a.c.gen_step_def del: graph_restrict_simps)
      apply refine_rcg
      apply (auto simp: pred_rel_simps) [2]

      (* pending edges *)
      apply (frule (1) pred_rel_simps[THEN Not_eq_iff[symmetric, THEN iffD1], THEN iffD1])
      thm order_trans[OF bind_mono(1)[OF get_pending_refine order_refl]]
      apply (rule order_trans[OF bind_mono(1)[OF get_pending_refine order_refl]])
      apply assumption+

      apply (unfold bind_distrib_sup1)
      apply (rule sup_least)
        (* Non-spurious node *)
        apply (rule le_supI1)
        apply (simp add: a.c.gen_step_def del: graph_restrict_simps cong: option.case_cong if_cong)
        apply (rule bind_refine'[OF conc_fun_mono[THEN monoD]], simp)
        apply (clarsimp simp: refine_pw_simps)
        apply (refine_rcg, refine_dref_type, simp_all add: pred_rel_simps) []

        (* Spurious node *)
        apply (rule le_supI2)
        apply (rule RETURN_as_SPEC_refine)
        apply (simp add: conc_fun_SPEC)
        apply (refine_rcg refine_vcg bind_refine', simp_all) []
        apply (clarsimp)
        apply (frule (1) aux_R_node_discovered, blast)
    done        

  theorem re_refine_aux2: "gen_dfs \<le>\<Down>(rel O \<langle>ES\<rangle>simple_state_rel) a.a.it_dfs"
  proof -
    note re_refine_aux 
    also note a.gen_dfs_refine
    finally show ?thesis by (simp add: conc_fun_chain del: graph_restrict_simps)
  qed

  theorem re_refine: "gen_dfs \<le>\<Down>(\<langle>ES\<rangle>restr_simple_state_rel R) a.a.it_dfs"
    unfolding restr_simple_state_rel_combine
    by (rule re_refine_aux2)


  (* Link to tailrec_impl *)
  sublocale tailrec_impl G gds
    apply unfold_locales
    apply (simp_all add: do_action_defs impl_defs[abs_def])
    apply (auto simp: pw_leof_iff refine_pw_simps split: prod.split)
    done

  lemma tailrec_refine: "tailrec_impl \<le> \<Down>(\<langle>ES\<rangle>restr_simple_state_rel R) a.a.it_dfs"
  proof -
    note tailrec_impl also note re_refine finally show ?thesis .
  qed

  (* TODO: Link to rec_impl *)
end

end

