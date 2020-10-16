section \<open>Simple Data Structures\<close>
theory Simple_Impl
imports 
  "../Structural/Rec_Impl"
  "../Structural/Tailrec_Impl"
begin

text \<open>
  We provide some very basic data structures to implement the DFS state
\<close>

subsection \<open> Stack, Pending Stack, and Visited Set \<close>
record 'v simple_state =
  ss_stack :: "('v \<times> 'v set) list"
  on_stack :: "'v set"
  visited :: "'v set"

definition [to_relAPP]: "simple_state_rel erel \<equiv> { (s,s') .
  ss_stack s = map (\<lambda>u. (u,pending s' `` {u})) (stack s') \<and>
  on_stack s = set (stack s') \<and>
  visited s = dom (discovered s') \<and>
  dom (finished s') = dom (discovered s') - set (stack s') \<and> \<comment> \<open>TODO: Hmm, this is an invariant of the abstract\<close>
  set (stack s') \<subseteq> dom (discovered s') \<and>
  (simple_state.more s, state.more s') \<in> erel
}"

lemma simple_state_relI:
  assumes 
  "dom (finished s') = dom (discovered s') - set (stack s')"
  "set (stack s') \<subseteq> dom (discovered s')"
  "(m', state.more s') \<in> erel"
  shows "(\<lparr>
    ss_stack = map (\<lambda>u. (u,pending s' `` {u})) (stack s'),
    on_stack = set (stack s'),
    visited = dom (discovered s'),
    \<dots> = m'
  \<rparr>, s')\<in>\<langle>erel\<rangle>simple_state_rel"
  using assms
  unfolding simple_state_rel_def
  by auto

lemma simple_state_more_refine[param]: 
  "(simple_state.more_update, state.more_update)
    \<in> (R \<rightarrow> R) \<rightarrow> \<langle>R\<rangle>simple_state_rel \<rightarrow> \<langle>R\<rangle>simple_state_rel"
  apply (clarsimp simp: simple_state_rel_def) 
  apply parametricity
  done


text \<open> We outsource the definitions in a separate locale, as we want to re-use them
  for similar implementations \<close>
locale pre_simple_impl = graph_defs
begin

  definition "init_impl e 
    \<equiv> RETURN \<lparr> ss_stack = [], on_stack = {}, visited = {}, \<dots> = e \<rparr>"

  definition "is_empty_stack_impl s \<equiv> (ss_stack s = [])"
  definition "is_discovered_impl u s \<equiv> (u\<in>visited s)"
  definition "is_finished_impl u s \<equiv> (u\<in>visited s - (on_stack s))"

  definition "finish_impl u s \<equiv> do {
    ASSERT (ss_stack s \<noteq> [] \<and> u\<in>on_stack s);
    let s = s\<lparr>ss_stack := tl (ss_stack s)\<rparr>;
    let s = s\<lparr>on_stack := on_stack s - {u}\<rparr>;
    RETURN s
    }"
  
  definition "get_pending_impl s \<equiv> do {
      ASSERT (ss_stack s \<noteq> []);
      let (u,Vs) = hd (ss_stack s);
      if Vs = {} then
        RETURN (u,None,s)
      else do {
        v \<leftarrow> SPEC (\<lambda>v. v\<in>Vs);
        let Vs = Vs - {v};
        let s = s\<lparr> ss_stack := (u,Vs) # tl (ss_stack s) \<rparr>;
        RETURN (u, Some v, s)
      }
    }"
  
  definition "discover_impl u v s \<equiv> do {
    ASSERT (v\<notin>on_stack s \<and> v\<notin>visited s);
    let s = s\<lparr>ss_stack := (v,E``{v}) # ss_stack s\<rparr>;
    let s = s\<lparr>on_stack := insert v (on_stack s)\<rparr>;
    let s = s\<lparr>visited := insert v (visited s)\<rparr>;
    RETURN s
    }"
  
  definition "new_root_impl v0 s \<equiv> do {
    ASSERT (v0\<notin>visited s);
    let s = s\<lparr>ss_stack := [(v0,E``{v0})]\<rparr>;
    let s = s\<lparr>on_stack := {v0}\<rparr>;
    let s = s\<lparr>visited := insert v0 (visited s)\<rparr>;
    RETURN s
    }"

  definition "gbs \<equiv> \<lparr>
    gbs_init = init_impl,
    gbs_is_empty_stack = is_empty_stack_impl ,
    gbs_new_root =  new_root_impl ,
    gbs_get_pending = get_pending_impl ,
    gbs_finish =  finish_impl ,
    gbs_is_discovered = is_discovered_impl ,
    gbs_is_finished = is_finished_impl ,
    gbs_back_edge = (\<lambda>u v s. RETURN s) ,
    gbs_cross_edge = (\<lambda>u v s. RETURN s) ,
    gbs_discover = discover_impl
  \<rparr>"

  lemmas gbs_simps[simp, DFS_code_unfold] = gen_basic_dfs_struct.simps[mk_record_simp, OF gbs_def]

  lemmas impl_defs[DFS_code_unfold] 
  = init_impl_def is_empty_stack_impl_def new_root_impl_def
    get_pending_impl_def finish_impl_def is_discovered_impl_def 
    is_finished_impl_def discover_impl_def

end

text \<open>
  Simple implementation of a DFS. This locale assumes a refinement of the
  parameters, and provides an implementation via a stack and a visited set.
\<close>
locale simple_impl_defs =
  a: param_DFS_defs G param
  + c: pre_simple_impl
  + gen_param_dfs_refine_defs 
    where gbsi = c.gbs 
    and gbs = a.gbs
    and upd_exti = simple_state.more_update
    and upd_ext = state.more_update
    and V0i = a.V0
    and V0 = a.V0
begin

  sublocale tailrec_impl_defs G c.gds .


  definition "get_pending s \<equiv> \<Union>(set (map (\<lambda>(u,Vs). {u}\<times>Vs) (ss_stack s)))"
  definition "get_stack s \<equiv> map fst (ss_stack s)"
  definition choose_pending 
    :: "'v \<Rightarrow> 'v option \<Rightarrow> ('v,'d) simple_state_scheme \<Rightarrow> ('v,'d) simple_state_scheme nres"
    where [DFS_code_unfold]: 
  "choose_pending u vo s \<equiv> 
    case vo of
      None \<Rightarrow> RETURN s
    | Some v \<Rightarrow> do {
        ASSERT (ss_stack s \<noteq> []);
        let (u,Vs) = hd (ss_stack s);
        RETURN (s\<lparr> ss_stack := (u,Vs-{v})#tl (ss_stack s)\<rparr>)
      }"

  sublocale rec_impl_defs G c.gds get_pending get_stack choose_pending .
end
  

locale simple_impl =
  a: param_DFS
  + simple_impl_defs
  + param_refinement
    where gbsi = c.gbs
    and gbs = a.gbs
    and upd_exti = simple_state.more_update
    and upd_ext = state.more_update
    and V0i = a.V0
    and V0 = a.V0
    and V=Id
    and S = "\<langle>ES\<rangle>simple_state_rel"
begin

  lemma init_impl: "(ei, e) \<in> ES \<Longrightarrow>
    c.init_impl ei \<le>\<Down>(\<langle>ES\<rangle>simple_state_rel) (RETURN (a.empty_state e))"
    unfolding c.init_impl_def a.empty_state_def simple_state_rel_def
    by (auto)

  lemma new_root_impl: 
    "\<lbrakk>a.gen_dfs.pre_new_root v0 s; 
      (v0i, v0)\<in>Id; (si, s) \<in> \<langle>ES\<rangle>simple_state_rel\<rbrakk>
      \<Longrightarrow> c.new_root_impl v0 si \<le>\<Down>(\<langle>ES\<rangle>simple_state_rel) (RETURN (a.new_root v0 s))"
      unfolding simple_state_rel_def a.gen_dfs.pre_new_root_def c.new_root_impl_def
      by (auto simp add: a.pred_defs)
  
  lemma get_pending_impl: "
    \<lbrakk>a.gen_dfs.pre_get_pending s; (si, s) \<in> \<langle>ES\<rangle>simple_state_rel\<rbrakk>
      \<Longrightarrow> c.get_pending_impl si 
          \<le> \<Down> (Id \<times>\<^sub>r Id \<times>\<^sub>r \<langle>ES\<rangle>simple_state_rel) (a.get_pending s)"
    apply (unfold a.get_pending_def c.get_pending_impl_def) []
    apply (refine_rcg bind_refine' Let_refine' IdI)
    apply (refine_dref_type)
    apply (auto 
        simp: simple_state_rel_def a.gen_dfs.pre_defs a.pred_defs neq_Nil_conv
        dest: DFS_invar.stack_distinct
      )
    done

  lemma inres_get_pending_None_conv: "inres (a.get_pending s0) (v, None, s) 
      \<longleftrightarrow> s=s0 \<and> v=hd (stack s0) \<and> pending s0``{hd (stack s0)} = {}" 
    unfolding a.get_pending_def
    by (auto simp add: refine_pw_simps)
  
  lemma inres_get_pending_Some_conv: "inres (a.get_pending s0) (v,Some Vs,s) 
      \<longleftrightarrow> v = hd (stack s) \<and> s = s0\<lparr>pending := pending s0 - {(hd (stack s0), Vs)}\<rparr>
       \<and> (hd (stack s0), Vs) \<in> pending s0"
    unfolding a.get_pending_def
    by (auto simp add: refine_pw_simps)
  
  lemma finish_impl:
    "\<lbrakk>a.gen_dfs.pre_finish v s0 s; (vi, v)\<in>Id; (si, s) \<in> \<langle>ES\<rangle>simple_state_rel\<rbrakk>
     \<Longrightarrow> c.finish_impl v si \<le>\<Down>(\<langle>ES\<rangle>simple_state_rel) (RETURN (a.finish v s))"
      unfolding simple_state_rel_def a.gen_dfs.pre_defs c.finish_impl_def
       
      (* Proof is fine-tuned to optimize speed *)
      apply (clarsimp simp: inres_get_pending_None_conv)
      apply (frule DFS_invar.stack_distinct)
      apply (simp add: a.pred_defs map_tl) 
      apply (clarsimp simp: neq_Nil_conv) 
      apply blast
      done
  
  lemma cross_edge_impl: "
    \<lbrakk>a.gen_dfs.pre_cross_edge u v s0 s; 
      (ui, u)\<in>Id; (vi, v)\<in>Id; (si, s) \<in> \<langle>ES\<rangle>simple_state_rel\<rbrakk>
      \<Longrightarrow> (si, a.cross_edge u v s) \<in> \<langle>ES\<rangle>simple_state_rel"
    unfolding simple_state_rel_def a.gen_dfs.pre_defs
    by simp
  
  lemma back_edge_impl: "
    \<lbrakk>a.gen_dfs.pre_back_edge u v s0 s; 
      (ui, u)\<in>Id; (vi, v)\<in>Id; (si, s) \<in> \<langle>ES\<rangle>simple_state_rel\<rbrakk>
      \<Longrightarrow> (si, a.back_edge u v s) \<in> \<langle>ES\<rangle>simple_state_rel"
    unfolding simple_state_rel_def a.gen_dfs.pre_defs
    by simp
  
  lemma discover_impl:
    "\<lbrakk>a.gen_dfs.pre_discover u v s0 s; (ui, u)\<in>Id; (vi, v)\<in>Id; (si, s) \<in> \<langle>ES\<rangle>simple_state_rel\<rbrakk>
     \<Longrightarrow> c.discover_impl ui vi si \<le>\<Down>(\<langle>ES\<rangle>simple_state_rel) (RETURN (a.discover u v s))"
      unfolding simple_state_rel_def a.gen_dfs.pre_defs c.discover_impl_def
      apply (rule ASSERT_leI)
      apply (clarsimp simp: inres_get_pending_Some_conv)
      apply (frule DFS_invar.stack_discovered)
      apply (auto simp: a.pred_defs) []

      apply (clarsimp simp: inres_get_pending_Some_conv)
      apply (frule DFS_invar.stack_discovered)
      apply (frule DFS_invar.pending_ssE)
      apply (clarsimp simp: a.pred_defs)
      apply blast
      done

  sublocale gen_param_dfs_refine 
    where gbsi = c.gbs 
    and gbs = a.gbs
    and upd_exti = simple_state.more_update
    and upd_ext = state.more_update
    and V0i = a.V0
    and V0 = a.V0
    and V = Id
    and S = "\<langle>ES\<rangle>simple_state_rel"
    apply unfold_locales
    apply (simp_all add: is_break_param) (* TODO: Strange effect,   
      the is_break_param subgoal should not be visible at all!*)
    
    apply (auto simp: a.is_discovered_def c.is_discovered_impl_def simple_state_rel_def) []

    apply (auto simp: a.is_finished_def c.is_finished_impl_def simple_state_rel_def) []

    apply (auto simp: a.is_empty_stack_def c.is_empty_stack_impl_def simple_state_rel_def) []

    apply (refine_rcg init_impl)
    
    apply (refine_rcg new_root_impl, simp_all) []

    apply (refine_rcg get_pending_impl) []

    apply (refine_rcg finish_impl, simp_all) []

    apply (refine_rcg cross_edge_impl, simp_all) []

    apply (refine_rcg back_edge_impl, simp_all) []

    apply (refine_rcg discover_impl, simp_all) []
    done

  text \<open> Main outcome of this locale: The simple DFS-Algorithm, which is
    a general DFS scheme itself (and thus open to further refinements),
    and a refinement theorem that states correct refinement of the original DFS \<close>

  lemma simple_refine[refine]: "c.gen_dfs \<le> \<Down>(\<langle>ES\<rangle>simple_state_rel) a.it_dfs"
    using gen_dfs_refine
    by simp

  lemma simple_refineT[refine]: "c.gen_dfsT \<le> \<Down>(\<langle>ES\<rangle>simple_state_rel) a.it_dfsT"
    using gen_dfsT_refine
    by simp


  text \<open>Link with tail-recursive implementation\<close>

  sublocale tailrec_impl G c.gds
    apply unfold_locales
    apply (simp_all add: c.do_action_defs c.impl_defs[abs_def])
    apply (auto simp: pw_leof_iff refine_pw_simps split: prod.splits)
    done

  lemma simple_tailrec_refine[refine]: "tailrec_impl \<le> \<Down>(\<langle>ES\<rangle>simple_state_rel) a.it_dfs"
  proof -
    note tailrec_impl also note simple_refine finally show ?thesis .
  qed

  lemma simple_tailrecT_refine[refine]: "tailrec_implT \<le> \<Down>(\<langle>ES\<rangle>simple_state_rel) a.it_dfsT"
  proof -
    note tailrecT_impl also note simple_refineT finally show ?thesis .
  qed

  text \<open>Link to recursive implementation\<close>
  (* TODO: Currently, we have to prove this invar at several places.
    Maybe it's worth to share in a common locale!?
  *)
  lemma reachable_invar: 
    assumes "c.gen_rwof s" 
    shows "set (map fst (ss_stack s)) \<subseteq> visited s 
      \<and> distinct (map fst (ss_stack s))"
    using assms
    apply (induct rule: establish_rwof_invar[rotated -1, consumes 1])
    apply (simp add: c.do_action_defs c.impl_defs[abs_def])
    apply (refine_rcg refine_vcg)
    apply simp

    unfolding c.gen_step_def c.do_action_defs c.impl_defs[abs_def] c.gds_simps c.gbs_simps
    apply (refine_rcg refine_vcg)
    apply simp_all
    apply (fastforce simp: neq_Nil_conv) [] 
    apply (fastforce simp: neq_Nil_conv) [] 
    apply (fastforce simp: neq_Nil_conv) [] 
    apply (fastforce simp: neq_Nil_conv) [] 
    done


  sublocale rec_impl G c.gds get_pending get_stack choose_pending
    apply unfold_locales
    unfolding get_pending_def get_stack_def choose_pending_def
    apply (simp_all add: c.do_action_defs c.impl_defs[abs_def])
    apply (auto simp: pw_leof_iff refine_pw_simps pw_le_iff select_def
      split: prod.split) []
    apply (auto simp: pw_leof_iff refine_pw_simps pw_le_iff select_def
      split: prod.split) []

    apply (rule le_ASSERTI)
    apply (unfold c.pre_defs, clarify) []
    apply (frule reachable_invar)
      
    apply (fastforce simp add: pw_leof_iff refine_pw_simps pw_le_iff neq_Nil_conv
      split: prod.split option.split) []  

    apply (unfold c.pre_defs, clarify) []
    apply (frule reachable_invar)
    apply (auto simp: pw_leof_iff refine_pw_simps pw_le_iff select_def c.impl_defs neq_Nil_conv
      split: prod.split option.split) []

    apply (auto simp: pw_leof_iff refine_pw_simps pw_le_iff select_def neq_Nil_conv c.pre_defs c.impl_defs
      split: prod.split if_split_asm) []

    apply (auto simp: pw_leof_iff refine_pw_simps pw_le_iff split: prod.split) []

    apply (auto simp: pw_leof_iff refine_pw_simps pw_le_iff split: prod.split) []

    apply (auto simp: pw_leof_iff refine_pw_simps pw_le_iff split: prod.split) []
    done

  lemma simple_rec_refine[refine]: "rec_impl \<le> \<Down>(\<langle>ES\<rangle>simple_state_rel) a.it_dfs"
  proof -
    note rec_impl also note simple_refine finally show ?thesis .
  qed

end

text \<open> Autoref Setup \<close>

record ('si,'nsi)simple_state_impl =
  ss_stack_impl :: 'si
  ss_on_stack_impl :: 'nsi
  ss_visited_impl :: 'nsi

definition [to_relAPP]: "ss_impl_rel s_rel vis_rel erel \<equiv> 
  {(\<lparr>ss_stack_impl = si, ss_on_stack_impl = osi, ss_visited_impl = visi, \<dots> = mi\<rparr>,
    \<lparr>ss_stack = s, on_stack = os, visited = vis, \<dots> = m\<rparr>) |
    si osi visi mi s os vis m.
    (si, s) \<in> s_rel \<and>
    (osi, os) \<in> vis_rel \<and>
    (visi, vis) \<in> vis_rel \<and>
    (mi, m) \<in> erel
  }"

consts 
  i_simple_state :: "interface \<Rightarrow> interface \<Rightarrow> interface \<Rightarrow> interface"

lemmas [autoref_rel_intf] = REL_INTFI[of ss_impl_rel i_simple_state]

term simple_state_ext

lemma [autoref_rules, param]:
  fixes s_rel ps_rel vis_rel erel
  defines "R \<equiv> \<langle>s_rel,vis_rel,erel\<rangle>ss_impl_rel"
  shows
  "(ss_stack_impl, ss_stack) \<in>  R \<rightarrow> s_rel"
  "(ss_on_stack_impl, on_stack) \<in>  R \<rightarrow> vis_rel"
  "(ss_visited_impl, visited) \<in> R \<rightarrow> vis_rel"
  "(simple_state_impl.more, simple_state.more) \<in> R \<rightarrow> erel"
  "(ss_stack_impl_update, ss_stack_update) \<in> (s_rel \<rightarrow> s_rel) \<rightarrow> R \<rightarrow> R"
  "(ss_on_stack_impl_update, on_stack_update) \<in> (vis_rel \<rightarrow> vis_rel) \<rightarrow> R \<rightarrow> R"
  "(ss_visited_impl_update, visited_update) \<in> (vis_rel \<rightarrow> vis_rel) \<rightarrow> R \<rightarrow> R"
  "(simple_state_impl.more_update, simple_state.more_update) \<in> (erel \<rightarrow> erel) \<rightarrow> R \<rightarrow> R"
  "(simple_state_impl_ext, simple_state_ext) \<in> s_rel \<rightarrow> vis_rel \<rightarrow> vis_rel \<rightarrow> erel \<rightarrow> R"
  unfolding ss_impl_rel_def R_def
  apply auto
  apply parametricity+
  done

subsection \<open> Simple state without on-stack \<close>
text \<open> We can further refine the simple implementation and drop the on-stack set \<close>
record ('si,'nsi)simple_state_nos_impl =
  ssnos_stack_impl :: 'si
  ssnos_visited_impl :: 'nsi

definition [to_relAPP]: "ssnos_impl_rel s_rel vis_rel erel \<equiv> 
  {(\<lparr>ssnos_stack_impl = si, ssnos_visited_impl = visi, \<dots> = mi\<rparr>,
    \<lparr>ss_stack = s, on_stack = os, visited = vis, \<dots> = m\<rparr>) |
    si visi mi s os vis m.
    (si, s) \<in> s_rel \<and>
    (visi, vis) \<in> vis_rel \<and>
    (mi, m) \<in> erel
  }"

lemmas [autoref_rel_intf] = REL_INTFI[of ssnos_impl_rel i_simple_state]

definition op_nos_on_stack_update 
  :: "(_ set \<Rightarrow> _ set) \<Rightarrow> (_,_)simple_state_scheme \<Rightarrow> _"
  where "op_nos_on_stack_update \<equiv> on_stack_update"

context begin interpretation autoref_syn .
lemma [autoref_op_pat_def]: "op_nos_on_stack_update f s 
  \<equiv> OP (op_nos_on_stack_update f)$s" by simp

end

lemmas ssnos_unfolds \<comment> \<open>To be unfolded before autoref when using @{term ssnos_impl_rel}\<close>
  = op_nos_on_stack_update_def[symmetric]

lemma [autoref_rules, param]:
  fixes s_rel vis_rel erel
  defines "R \<equiv> \<langle>s_rel,vis_rel,erel\<rangle>ssnos_impl_rel"
  shows
  "(ssnos_stack_impl, ss_stack) \<in>  R \<rightarrow> s_rel"
  "(ssnos_visited_impl, visited) \<in> R \<rightarrow> vis_rel"
  "(simple_state_nos_impl.more, simple_state.more) \<in> R \<rightarrow> erel"
  "(ssnos_stack_impl_update, ss_stack_update) \<in> (s_rel \<rightarrow> s_rel) \<rightarrow> R \<rightarrow> R"
  "(\<lambda>x. x, op_nos_on_stack_update f) \<in> R \<rightarrow> R"
  "(ssnos_visited_impl_update, visited_update) \<in> (vis_rel \<rightarrow> vis_rel) \<rightarrow> R \<rightarrow> R"
  "(simple_state_nos_impl.more_update, simple_state.more_update) \<in> (erel \<rightarrow> erel) \<rightarrow> R \<rightarrow> R"
  "(\<lambda>ns _ ps vs. simple_state_nos_impl_ext ns ps vs, simple_state_ext) 
    \<in> s_rel \<rightarrow> ANY_rel \<rightarrow> vis_rel \<rightarrow> erel \<rightarrow> R"
  unfolding ssnos_impl_rel_def R_def op_nos_on_stack_update_def
  apply auto
  apply parametricity+
  done

subsection \<open>Simple state without stack and on-stack\<close>
text \<open>Even further refinement yields an implementation without a stack.
  Note that this only works for structural implementations that provide their own
  stack (e.g., recursive)!\<close>
record ('si,'nsi)simple_state_ns_impl =
  ssns_visited_impl :: 'nsi

definition [to_relAPP]: "ssns_impl_rel (R::('a\<times>'b) set) vis_rel erel \<equiv> 
  {(\<lparr>ssns_visited_impl = visi, \<dots> = mi\<rparr>,
    \<lparr>ss_stack = s, on_stack = os, visited = vis, \<dots> = m\<rparr>) |
    visi mi s os vis m.
    (visi, vis) \<in> vis_rel \<and>
    (mi, m) \<in> erel
  }"

lemmas [autoref_rel_intf] = REL_INTFI[of ssns_impl_rel i_simple_state]

definition op_ns_on_stack_update 
  :: "(_ set \<Rightarrow> _ set) \<Rightarrow> (_,_)simple_state_scheme \<Rightarrow> _"
  where "op_ns_on_stack_update \<equiv> on_stack_update"

definition op_ns_stack_update 
  :: "(_ list \<Rightarrow> _ list) \<Rightarrow> (_,_)simple_state_scheme \<Rightarrow> _"
  where "op_ns_stack_update \<equiv> ss_stack_update"

context begin interpretation autoref_syn .
lemma [autoref_op_pat_def]: "op_ns_on_stack_update f s 
  \<equiv> OP (op_ns_on_stack_update f)$s" by simp

lemma [autoref_op_pat_def]: "op_ns_stack_update f s 
  \<equiv> OP (op_ns_stack_update f)$s" by simp

end


context simple_impl_defs begin
  thm choose_pending_def[unfolded op_ns_stack_update_def[symmetric], no_vars]

  lemma choose_pending_ns_unfold: "choose_pending u vo s = (
    case vo of None \<Rightarrow> RETURN s
    | Some v \<Rightarrow> do {
          _ \<leftarrow> ASSERT (ss_stack s \<noteq> []);
          RETURN
           (op_ns_stack_update 
             ( let 
                 (u, Vs) = hd (ss_stack s) 
               in (\<lambda>_. (u, Vs - {v}) # tl (ss_stack s))
             )
             s
           )
        })"
    unfolding choose_pending_def op_ns_stack_update_def
    by (auto split: option.split prod.split)

  lemmas ssns_unfolds \<comment> \<open>To be unfolded before autoref when using @{term ssns_impl_rel}.
    Attention: This lemma conflicts with the standard unfolding lemma in 
    @{text DFS_code_unfold}, so has to be placed first in an unfold-statement!\<close>
  = op_ns_on_stack_update_def[symmetric] op_ns_stack_update_def[symmetric]
    choose_pending_ns_unfold

end

lemma [autoref_rules, param]:
  fixes s_rel vis_rel erel ANY_rel
  defines "R \<equiv> \<langle>ANY_rel,vis_rel,erel\<rangle>ssns_impl_rel"
  shows
  "(ssns_visited_impl, visited) \<in> R \<rightarrow> vis_rel"
  "(simple_state_ns_impl.more, simple_state.more) \<in> R \<rightarrow> erel"
  "\<And>f. (\<lambda>x. x, op_ns_stack_update f) \<in> R \<rightarrow> R"
  "\<And>f. (\<lambda>x. x, op_ns_on_stack_update f) \<in> R \<rightarrow> R"
  "(ssns_visited_impl_update, visited_update) \<in> (vis_rel \<rightarrow> vis_rel) \<rightarrow> R \<rightarrow> R"
  "(simple_state_ns_impl.more_update, simple_state.more_update) \<in> (erel \<rightarrow> erel) \<rightarrow> R \<rightarrow> R"
  "(\<lambda>_ _ ps vs. simple_state_ns_impl_ext ps vs, simple_state_ext) 
    \<in> ANY1_rel \<rightarrow> ANY2_rel \<rightarrow> vis_rel \<rightarrow> erel \<rightarrow> R"
  unfolding ssns_impl_rel_def R_def op_ns_on_stack_update_def op_ns_stack_update_def
  apply auto
  apply parametricity+
  done


lemma [refine_transfer_post_simp]:
  "\<And>a m. a\<lparr>simple_state_nos_impl.more := m::unit\<rparr> = a"
  "\<And>a m. a\<lparr>simple_state_impl.more := m::unit\<rparr> = a"
  "\<And>a m. a\<lparr>simple_state_ns_impl.more := m::unit\<rparr> = a"
  by auto


end

