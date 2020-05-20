section \<open>Relabel-to-Front Algorithm\<close>
theory Relabel_To_Front
imports 
  Prpu_Common_Inst 
  Graph_Topological_Ordering
begin
  text \<open>As an example for an implementation, Cormen et al.\ discuss the 
    relabel-to-front algorithm.
    It iterates over a queue of nodes, discharging each node, and putting
    a node to the front of the queue if it has been relabeled.
\<close>
  
subsection \<open>Admissible Network\<close>  
text \<open>The admissible network consists of those edges over which we 
  can push flow. \<close>
  
context Network 
begin  
  definition adm_edges :: "'capacity flow \<Rightarrow> (nat\<Rightarrow>nat) \<Rightarrow> _" 
    where "adm_edges f l \<equiv> {(u,v)\<in>cfE_of f. l u = l v + 1}"
    
  lemma adm_edges_inv_disj: "adm_edges f l \<inter> (adm_edges f l)\<inverse> = {}"
    unfolding adm_edges_def by auto
  
  lemma finite_adm_edges[simp, intro!]: "finite (adm_edges f l)"
    apply (rule finite_subset[of _ "cfE_of f"])
    by (auto simp: adm_edges_def)
  
  
  
end \<comment> \<open>Network\<close> 
  
text \<open>The edge of a push operation is admissible.\<close>  
lemma (in push_effect_locale) uv_adm: "(u,v)\<in>adm_edges f l" 
  unfolding adm_edges_def by auto


text \<open>
  A push operation will not create new admissible edges, but the 
  edge that we pushed over may become inadmissible \cormen{26.27}.
\<close>
lemma (in Labeling) push_adm_edges:
  assumes "push_precond f l e"  
  shows "adm_edges f l - {e} \<subseteq> adm_edges (push_effect f e) l" (is ?G1)
    and "adm_edges (push_effect f e) l \<subseteq> adm_edges f l" (is ?G2)
proof -    
  from assms consider (sat) "sat_push_precond f l e" 
                 | (nonsat) "nonsat_push_precond f l e"
    by (auto simp: push_precond_eq_sat_or_nonsat)                  
  hence "?G1 \<and> ?G2" 
  proof cases
    case sat have "adm_edges (push_effect f e) l = adm_edges f l - {e}"
      unfolding sat_push_alt[OF sat]
    proof -
      (* TODO: Clean up. Use push_effect_locale! *)
      let ?f'="(augment_edge f e (cf e))"
      interpret l': Labeling c s t ?f' l 
        using push_pres_Labeling[OF assms]
        unfolding sat_push_alt[OF sat] .
    
      from sat have G1: "e\<in>adm_edges f l"    
        unfolding sat_push_precond_def adm_edges_def by auto
          
      have "l'.cf.E \<subseteq> insert (prod.swap e) cf.E - {e}" "l'.cf.E \<supseteq> cf.E - {e}"
        unfolding l'.cf_def cf_def
        unfolding augment_edge_def residualGraph_def Graph.E_def
        by (auto split!: if_splits prod.splits)
      hence "l'.cf.E = insert (prod.swap e) cf.E - {e} \<or> l'.cf.E = cf.E - {e}"
        by auto
      thus "adm_edges ?f' l = adm_edges f l - {e}" 
      proof (cases rule: disjE[consumes 1])
        case 1
        from sat have "e \<in> adm_edges f l" unfolding sat_push_precond_def adm_edges_def by auto
        with adm_edges_inv_disj have "prod.swap e \<notin> adm_edges f l" by (auto simp: swap_in_iff_inv)
        thus "adm_edges ?f' l = adm_edges f l - {e}" using G1
          unfolding adm_edges_def 1   
          by auto
      next
        case 2
        thus "adm_edges ?f' l = adm_edges f l - {e}" 
          unfolding adm_edges_def 2   
          by auto  
      qed
    qed    
    thus ?thesis by auto
  next
    case nonsat
    hence "adm_edges (push_effect f e) l = adm_edges f l"
    proof (cases e; simp add: nonsat_push_alt)
      fix u v assume [simp]: "e=(u,v)"
      
      let ?f'="(augment_edge f (u,v) (excess f u))"
      interpret l': Labeling c s t ?f' l 
        using push_pres_Labeling[OF assms] nonsat_push_alt nonsat
        by auto
      
      from nonsat have "e \<in> adm_edges f l" 
        unfolding nonsat_push_precond_def adm_edges_def by auto
      with adm_edges_inv_disj have AUX: "prod.swap e \<notin> adm_edges f l" 
        by (auto simp: swap_in_iff_inv)
          
      from nonsat have 
        "excess f u < cf (u,v)" "0 < excess f u"
        and [simp]: "l u = l v + 1" 
        unfolding nonsat_push_precond_def by auto
      hence "l'.cf.E \<subseteq> insert (prod.swap e) cf.E" "l'.cf.E \<supseteq> cf.E"
        unfolding l'.cf_def cf_def
        unfolding augment_edge_def residualGraph_def Graph.E_def
        apply (safe)
        apply (simp split: if_splits)  
        apply (simp split: if_splits)  
        subgoal
          by (metis (full_types) capacity_const diff_0_right 
                diff_strict_left_mono not_less)  
        subgoal
          by (metis add_le_same_cancel1 f_non_negative linorder_not_le)  
        done    
      hence "l'.cf.E = insert (prod.swap e) cf.E \<or> l'.cf.E = cf.E"
        by auto
      thus "adm_edges ?f' l = adm_edges f l" using AUX
        unfolding adm_edges_def  
        by auto  
    qed  
    thus ?thesis by auto
  qed      
  thus ?G1 ?G2 by auto  
qed    
    
text \<open>After a relabel operation, there is at least 
  one admissible edge leaving the relabeled node, 
  but no admissible edges do enter the relabeled node~\cormen{26.28}.
  Moreover, the part of the admissible network not adjacent to the relabeled 
  node does not change.
\<close>  
  
lemma (in Labeling) relabel_adm_edges:
  assumes PRE: "relabel_precond f l u"
  defines "l' \<equiv> relabel_effect f l u"
  shows "adm_edges f l' \<inter> cf.outgoing u \<noteq> {}" (is ?G1)
    and "adm_edges f l' \<inter> cf.incoming u = {}" (is ?G2)
    and "adm_edges f l' - cf.adjacent u = adm_edges f l - cf.adjacent u" (is ?G3)
proof -
  from PRE have  
        NOT_SINK: "u\<noteq>t"
    and ACTIVE: "excess f u > 0"
    and NO_ADM: "\<And>v. (u,v)\<in>cf.E \<Longrightarrow> l u \<noteq> l v + 1"
  unfolding relabel_precond_def by auto
  
  have NE: "{l v |v. (u, v) \<in> cf.E} \<noteq> {}"  
    using active_has_cf_outgoing[OF ACTIVE] cf.outgoing_def by blast
  obtain v 
    where VUE: "(u,v)\<in>cf.E" and [simp]: "l v = Min {l v |v. (u, v) \<in> cf.E}"
    using Min_in[OF finite_min_cf_outgoing[of u] NE] by auto
  hence "(u,v) \<in> adm_edges f l' \<inter> cf.outgoing u"  
    unfolding l'_def relabel_effect_def adm_edges_def cf.outgoing_def
    by (auto simp: cf_no_self_loop)
  thus ?G1 by blast

  {
    fix uh
    assume "(uh,u) \<in> adm_edges f l'"  
    hence 1: "l' uh = l' u + 1" and UHUE: "(uh,u) \<in> cf.E" 
      unfolding adm_edges_def by auto
    hence "uh \<noteq> u" using cf_no_self_loop by auto
    hence [simp]: "l' uh = l uh" unfolding l'_def relabel_effect_def by simp
    from 1 relabel_increase_u[OF PRE, folded l'_def] have "l uh > l u + 1" 
      by simp
    with valid[OF UHUE] have False by auto    
  }    
  thus ?G2 by (auto simp: cf.incoming_def)
      
  show ?G3    
    unfolding adm_edges_def
    by (auto 
        simp: l'_def relabel_effect_def cf.adjacent_def 
        simp: cf.incoming_def cf.outgoing_def
        split: if_splits)
      
qed    

subsection \<open>Neighbor Lists\<close>  
text \<open>
  For each node, the algorithm will cycle through the adjacent edges 
  when discharging. This cycling takes place across the boundaries of
  discharge operations, i.e.\ when a node is discharged, discharging will 
  start at the edge where the last discharge operation stopped.

  The crucial invariant for the neighbor lists is that already visited 
  edges are not admissible.

  Formally, we maintain a function \<open>n :: node \<Rightarrow> node set\<close> from 
  each node to the set of target nodes of not yet visited edges.
\<close>
  
locale neighbor_invar = Height_Bounded_Labeling +
  fixes n :: "node \<Rightarrow> node set"  
  assumes neighbors_adm: "\<lbrakk>v \<in> adjacent_nodes u - n u\<rbrakk> \<Longrightarrow> (u,v) \<notin> adm_edges f l"
  assumes neighbors_adj: "n u \<subseteq> adjacent_nodes u"  
  assumes neighbors_finite[simp, intro!]: "finite (n u)"  
begin
  
lemma nbr_is_hbl: "Height_Bounded_Labeling c s t f l" by unfold_locales

lemma push_pres_nbr_invar:
  assumes PRE: "push_precond f l e"
  shows "neighbor_invar c s t (push_effect f e) l n"  
proof (cases e)
  case [simp]: (Pair u v)
  show ?thesis proof simp
    from PRE interpret push_effect_locale c s t f l u v
      by unfold_locales simp
    from push_pres_height_bound[OF PRE] 
    interpret l': Height_Bounded_Labeling c s t f' l .
  
    show "neighbor_invar c s t f' l n"
      apply unfold_locales
      using push_adm_edges[OF PRE] neighbors_adm neighbors_adj
      by auto  
  qed
qed
    
lemma relabel_pres_nbr_invar:  
  assumes PRE: "relabel_precond f l u"
  shows "neighbor_invar c s t f (relabel_effect f l u) (n(u:=adjacent_nodes u))"
proof -
  let ?l' = "relabel_effect f l u"
  from relabel_pres_height_bound[OF PRE] 
  interpret l': Height_Bounded_Labeling c s t f ?l' .
  
  show ?thesis 
    using neighbors_adj
  proof (unfold_locales; clarsimp split: if_splits)
    fix a b
    assume A: "a\<noteq>u" "b\<in>adjacent_nodes a" "b \<notin> n a" "(a,b)\<in>adm_edges f ?l'"
    hence "(a,b)\<in>cf.E" unfolding adm_edges_def by auto
    with A relabel_adm_edges(2,3)[OF PRE] neighbors_adm
    show False 
      apply (auto) (* TODO: Clean up this mess *)
      by (smt DiffD2 Diff_triv adm_edges_def cf.incoming_def 
          mem_Collect_eq prod.simps(2) relabel_preserve_other)
  qed
qed  

lemma excess_nz_iff_gz: "\<lbrakk> u\<in>V; u\<noteq>s \<rbrakk> \<Longrightarrow> excess f u \<noteq> 0 \<longleftrightarrow> excess f u > 0"  
  using excess_non_negative' by force
  
lemma no_neighbors_relabel_precond: 
  assumes "n u = {}" "u\<noteq>t" "u\<noteq>s" "u\<in>V" "excess f u \<noteq> 0"
  shows "relabel_precond f l u"  
  using assms neighbors_adm cfE_ss_invE 
  unfolding relabel_precond_def adm_edges_def
  by (auto simp: adjacent_nodes_def excess_nz_iff_gz)
  
lemma remove_neighbor_pres_nbr_invar: "(u,v)\<notin>adm_edges f l 
  \<Longrightarrow> neighbor_invar c s t f l (n (u := n u - {v}))"
  apply unfold_locales
  using neighbors_adm neighbors_adj
  by (auto split: if_splits)
    
end
  
subsection \<open>Discharge Operation\<close>  
context Network 
begin  
text \<open>The discharge operation performs push and relabel operations on a 
  node until it becomes inactive.
  The lemmas in this section are based on the ideas described in
 the proof of \cormen{26.29}.
\<close>  
  
definition "discharge f l n u \<equiv> do {  
  assert (u \<in> V - {s,t});
  while\<^sub>T (\<lambda>(f,l,n). excess f u \<noteq> 0) (\<lambda>(f,l,n). do {
    v \<leftarrow> select v. v\<in>n u;
    case v of
      None \<Rightarrow> do {
        l \<leftarrow> relabel f l u;
        return (f,l,n(u := adjacent_nodes u))
      }
    | Some v \<Rightarrow> do {
        assert (v\<in>V \<and> (u,v)\<in>E\<union>E\<inverse>);
        if ((u,v) \<in> cfE_of f \<and> l u = l v + 1) then do {
          f \<leftarrow> push f l (u,v);
          return (f,l,n)
        } else do {
          assert ( (u,v) \<notin> adm_edges f l );
          return (f,l,n( u := n u - {v} ))
        }
      }
  }) (f,l,n)
}"
  
end \<comment> \<open>Network\<close>  
  
text \<open>Invariant for the discharge loop\<close>  
locale discharge_invar = 
        neighbor_invar c s t f l n 
  + lo: neighbor_invar c s t fo lo no
  for c s t and u :: node and fo lo no f l n +
  assumes lu_incr: "lo u \<le> l u"
  assumes u_node: "u\<in>V-{s,t}"  
  assumes no_relabel_adm_edges: "lo u = l u \<Longrightarrow> adm_edges f l \<subseteq> adm_edges fo lo"
  assumes no_relabel_excess: 
    "\<lbrakk>lo u = l u; u\<noteq>v; excess fo v \<noteq> excess f v\<rbrakk> \<Longrightarrow> (u,v)\<in>adm_edges fo lo"
  assumes adm_edges_leaving_u: "(u',v)\<in>adm_edges f l - adm_edges fo lo \<Longrightarrow> u'=u"
  assumes relabel_u_no_incoming_adm: "lo u \<noteq> l u \<Longrightarrow> (v,u)\<notin>adm_edges f l"
  assumes algo_rel: "((f,l),(fo,lo)) \<in> pr_algo_rel\<^sup>*"  
begin

lemma u_node_simp1[simp]: "u\<noteq>s" "u\<noteq>t" "s\<noteq>u" "t\<noteq>u" using u_node by auto
lemma u_node_simp2[simp, intro!]: "u\<in>V" using u_node by auto   
  
lemma dis_is_lbl: "Labeling c s t f l" by unfold_locales
lemma dis_is_hbl: "Height_Bounded_Labeling c s t f l" by unfold_locales
lemma dis_is_nbr: "neighbor_invar c s t f l n" by unfold_locales
  
lemma new_adm_imp_relabel: 
  "(u',v)\<in>adm_edges f l - adm_edges fo lo \<Longrightarrow> lo u \<noteq> l u"
  using no_relabel_adm_edges adm_edges_leaving_u by auto
  
lemma push_pres_dis_invar:
  assumes PRE: "push_precond f l (u,v)"
  shows "discharge_invar c s t u fo lo no (push_effect f (u,v)) l n"
proof -  
  from PRE interpret push_effect_locale by unfold_locales
  
  from push_pres_nbr_invar[OF PRE] interpret neighbor_invar c s t f' l n .
    
  show "discharge_invar c s t u fo lo no f' l n"
    apply unfold_locales
    subgoal using lu_incr by auto
    subgoal by auto    
    subgoal using no_relabel_adm_edges push_adm_edges(2)[OF PRE] by auto  
    subgoal for v' proof -
      assume LOU: "lo u = l u"
      assume EXNE: "excess fo v' \<noteq> excess f' v'"
      assume UNV': "u\<noteq>v'"  
      {
        assume "excess fo v' \<noteq> excess f v'"
        from no_relabel_excess[OF LOU UNV' this] have ?thesis .
      } moreover {
        assume "excess fo v' = excess f v'"
        with EXNE have "excess f v' \<noteq> excess f' v'" by simp
        hence "v'=v" using UNV' by (auto simp: excess'_if split: if_splits)
        hence ?thesis using no_relabel_adm_edges[OF LOU] uv_adm by auto
      } ultimately show ?thesis by blast
    qed
    subgoal 
      by (meson Diff_iff push_adm_edges(2)[OF PRE] adm_edges_leaving_u subsetCE)  
    subgoal 
      using push_adm_edges(2)[OF PRE] relabel_u_no_incoming_adm by blast
    subgoal 
      using converse_rtrancl_into_rtrancl[
              OF pr_algo_rel.push[OF dis_is_hbl PRE] algo_rel] 
      .
    done
qed
      
lemma relabel_pres_dis_invar:
  assumes PRE: "relabel_precond f l u"
  shows "discharge_invar c s t u fo lo no f 
            (relabel_effect f l u) (n(u := adjacent_nodes u))"
proof -  
  let ?l' = "relabel_effect f l u"
  let ?n' = "n(u := adjacent_nodes u)"  
  from relabel_pres_nbr_invar[OF PRE] 
  interpret l': neighbor_invar c s t f ?l' ?n' .
    
  note lu_incr 
  also note relabel_increase_u[OF PRE] 
  finally have INCR: "lo u < ?l' u" .
      
  show ?thesis    
    apply unfold_locales
    using INCR  
    apply simp_all
    subgoal for u' v 
    proof clarsimp
      assume IN': "(u', v) \<in> adm_edges f ?l'" 
         and NOT_INO: "(u', v) \<notin> adm_edges fo lo"
      {
        assume IN: "(u', v) \<in> adm_edges f l"
        with adm_edges_leaving_u NOT_INO have "u'=u" by auto
      } moreover {
        assume NOT_IN: "(u', v) \<notin> adm_edges f l"
        with IN' relabel_adm_edges[OF PRE] have "u'=u" 
          unfolding cf.incoming_def cf.outgoing_def cf.adjacent_def
          by auto  
      } ultimately show ?thesis by blast
    qed      
    subgoal 
      using relabel_adm_edges(2)[OF PRE] 
      unfolding adm_edges_def cf.incoming_def 
      by fastforce  
    subgoal 
      using converse_rtrancl_into_rtrancl[
              OF pr_algo_rel.relabel[OF dis_is_hbl PRE] algo_rel] 
      .
    done  
qed                                                    

lemma push_precondI_nz: 
  "\<lbrakk>excess f u \<noteq> 0; (u,v)\<in>cfE_of f; l u = l v + 1\<rbrakk> \<Longrightarrow> push_precond f l (u,v)"
  unfolding push_precond_def by (auto simp: excess_nz_iff_gz)
  
  
lemma remove_neighbor_pres_dis_invar: 
  assumes PRE: "(u,v)\<notin>adm_edges f l"  
  defines "n' \<equiv> n (u := n u - {v})"  
  shows "discharge_invar c s t u fo lo no f l n'"
proof -
  from remove_neighbor_pres_nbr_invar[OF PRE] 
  interpret neighbor_invar c s t f l n' unfolding n'_def .
  show ?thesis 
    apply unfold_locales
    using lu_incr no_relabel_adm_edges no_relabel_excess adm_edges_leaving_u 
      relabel_u_no_incoming_adm algo_rel
    by auto  
qed  
    
lemma neighbors_in_V: "v\<in>n u \<Longrightarrow> v\<in>V"  
  using neighbors_adj[of u] E_ss_VxV unfolding adjacent_nodes_def by auto

lemma neighbors_in_E: "v\<in>n u \<Longrightarrow> (u,v)\<in>E\<union>E\<inverse>"  
  using neighbors_adj[of u] E_ss_VxV unfolding adjacent_nodes_def by auto
    
    
lemma relabeled_node_has_outgoing: 
  assumes "relabel_precond f l u"
  shows "\<exists>v. (u,v)\<in>cfE_of f"  
  using assms unfolding relabel_precond_def  
  using active_has_cf_outgoing unfolding cf.outgoing_def by auto
    
  
end  
  
lemma (in neighbor_invar) discharge_invar_init: 
  assumes "u\<in>V-{s,t}"
  shows "discharge_invar c s t u f l n f l n"
  using assms  
  by unfold_locales auto  
  
  
context Network begin  
text \<open>
  The discharge operation preserves the invariant, and discharges the node.
\<close>  
lemma discharge_correct[THEN order_trans, refine_vcg]:
  assumes DINV: "neighbor_invar c s t f l n"
  assumes NOT_ST: "u\<noteq>t" "u\<noteq>s" and UIV: "u\<in>V"
  shows "discharge f l n u 
    \<le> SPEC (\<lambda>(f',l',n'). discharge_invar c s t u f l n f' l' n' 
                       \<and> excess f' u = 0)"  
  unfolding discharge_def push_def relabel_def
  apply (refine_vcg WHILET_rule[where 
            I="\<lambda>(f',l',n'). discharge_invar c s t u f l n f' l' n'"
        and R="inv_image (pr_algo_rel <*lex*> finite_psubset) 
                (\<lambda>(f',l',n'). ((f',l'),n' u))"]
      )
  apply (vc_solve 
      solve: wf_lex_prod DINV 
      solve: neighbor_invar.discharge_invar_init[OF DINV]
      solve: neighbor_invar.no_neighbors_relabel_precond 
      solve: discharge_invar.relabel_pres_dis_invar 
      solve: discharge_invar.push_pres_dis_invar
      solve: discharge_invar.push_precondI_nz pr_algo_rel.relabel 
      solve: pr_algo_rel.push[OF discharge_invar.dis_is_hbl]
      solve: discharge_invar.remove_neighbor_pres_dis_invar
      solve: discharge_invar.neighbors_in_V
      solve: discharge_invar.relabeled_node_has_outgoing
      solve: discharge_invar.dis_is_hbl 
      intro: discharge_invar.dis_is_nbr 
      solve: discharge_invar.dis_is_lbl
      simp: NOT_ST 
      simp: neighbor_invar.neighbors_finite[OF discharge_invar.dis_is_nbr] UIV)
  subgoal by (auto dest: discharge_invar.neighbors_in_E)  
  subgoal unfolding adm_edges_def by auto  
  subgoal by (auto)
  done
  
end \<comment> \<open>Network\<close> 
  
subsection \<open>Main Algorithm\<close>  
text \<open>We state the main algorithm and prove its 
  termination and correctness\<close>
  
context Network
begin
text \<open>Initially, all edges are unprocessed. \<close>  
definition "rtf_init_n u \<equiv> if u\<in>V-{s,t} then adjacent_nodes u else {}"

lemma rtf_init_n_finite[simp, intro!]: "finite (rtf_init_n u)"
  unfolding rtf_init_n_def
  by auto  
  
lemma init_no_adm_edges[simp]: "adm_edges pp_init_f pp_init_l = {}"  
  unfolding adm_edges_def pp_init_l_def
  using card_V_ge2  
  by auto  

lemma rtf_init_neighbor_invar: 
  "neighbor_invar c s t pp_init_f pp_init_l rtf_init_n"
proof -
  from pp_init_height_bound 
  interpret Height_Bounded_Labeling c s t pp_init_f pp_init_l .

  have [simp]: "rtf_init_n u \<subseteq> adjacent_nodes u" for u
    by (auto simp: rtf_init_n_def)
      
  show ?thesis by unfold_locales auto
qed


definition "relabel_to_front \<equiv> do {
  let f = pp_init_f;
  let l = pp_init_l;
  let n = rtf_init_n;

  let L_left=[];
  L_right \<leftarrow> spec l. distinct l \<and> set l = V - {s,t};

  (f,l,n,L_left,L_right) \<leftarrow> while\<^sub>T 
    (\<lambda>(f,l,n,L_left,L_right). L_right \<noteq> []) 
    (\<lambda>(f,l,n,L_left,L_right). do {
      let u = hd L_right;
      assert (u \<in> V);
      let old_lu = l u;
  
      (f,l,n) \<leftarrow> discharge f l n u;
  
      if (l u \<noteq> old_lu) then do {
        \<comment> \<open>Move \<open>u\<close> to front of \<open>l\<close>, and restart scanning \<open>L\<close>\<close>
        let (L_left,L_right) = ([u],L_left @ tl L_right);
        return (f,l,n,L_left,L_right)
      } else do {
        \<comment> \<open>Goto next node in \<open>l\<close>\<close>
        let (L_left,L_right) = (L_left@[u], tl L_right);
        return (f,l,n,L_left,L_right)
      }
  
    }) (f,l,n,L_left,L_right);

  assert (neighbor_invar c s t f l n);

  return f
}"
  
  
end \<comment> \<open>Network\<close> 
  
  
text \<open>Invariant for the main algorithm:
  \<^enum> Nodes in the queue left of the current node are not active
  \<^enum> The queue is a topological sort of the admissible network
  \<^enum> All nodes except source and sink are on the queue
\<close>    
    
locale rtf_invar = neighbor_invar +
  fixes L_left L_right :: "node list"
  assumes left_no_excess: "\<forall>u\<in>set (L_left). excess f u = 0"  
  assumes L_sorted: "is_top_sorted (adm_edges f l) (L_left @ L_right)"
  assumes L_set: "set L_left \<union> set L_right = V-{s,t}"  
begin    
  lemma rtf_is_nbr: "neighbor_invar c s t f l n" by unfold_locales
      
  lemma L_distinct: "distinct (L_left @ L_right)" 
    using is_top_sorted_distinct[OF L_sorted] .
  
  lemma terminated_imp_maxflow: 
    assumes [simp]: "L_right = []"   
    shows "isMaxFlow f" 
  proof -
    from L_set left_no_excess have "\<forall>u\<in>V-{s,t}. excess f u = 0" by auto
    with no_excess_imp_maxflow show ?thesis .    
  qed        
      
      
end  

context Network begin  
lemma rtf_init_invar: 
  assumes DIS: "distinct L_left" and L_set: "set L_left = V-{s,t}"
  shows "rtf_invar c s t pp_init_f pp_init_l rtf_init_n [] L_left"  
proof -
  from rtf_init_neighbor_invar 
  interpret neighbor_invar c s t pp_init_f pp_init_l rtf_init_n .
  show ?thesis using DIS L_set by unfold_locales auto  
qed  
  
theorem relabel_to_front_correct: 
  "relabel_to_front \<le> SPEC isMaxFlow"
  unfolding relabel_to_front_def
  apply (rewrite in "while\<^sub>T _ \<hole>" vcg_intro_frame)
  apply (refine_vcg  
      WHILET_rule[where 
            I="\<lambda>(f,l,n,L_left,L_right). rtf_invar c s t f l n L_left L_right"
        and R="inv_image 
                (pr_algo_rel\<^sup>+ <*lex*> less_than) 
                (\<lambda>(f,l,n,L_left,L_right). ((f,l),length L_right))"
        ]
      )
  apply (vc_solve simp: rtf_init_invar rtf_invar.rtf_is_nbr)
  subgoal by (blast intro: wf_lex_prod wf_trancl)  
  subgoal for _ f l n L_left L_right proof -
    assume "rtf_invar c s t f l n L_left L_right"
    then interpret rtf_invar c s t f l n L_left L_right .
        
    assume "L_right \<noteq> []" then obtain u L_right' 
      where [simp]: "L_right = u#L_right'" by (cases L_right) auto
        
    from L_set have [simp]: "u\<in>V" "u\<noteq>s" "u\<noteq>t" "s\<noteq>u" "t\<noteq>u" by auto
        
    from L_distinct have [simp]: "u\<notin>set L_left" "u\<notin>set L_right'" by auto
        
    show ?thesis
      apply (rule vcg_rem_frame)
      apply (rewrite in "do {(_,_,_) \<leftarrow> discharge _ _ _ _; \<hole>}" vcg_intro_frame)  
      apply refine_vcg
      apply (vc_solve simp: rtf_is_nbr split del: if_split)
      subgoal for f' l' n' proof -
        assume "discharge_invar c s t u f l n f' l' n'"
        then interpret l': discharge_invar c s t u f l n f' l' n' .
      
        assume [simp]: "excess f' u = 0"
  
        show ?thesis 
          apply (rule vcg_rem_frame)
          apply refine_vcg
          apply (vc_solve)
          subgoal proof -
            assume RELABEL: "l' u \<noteq> l u"
              
            have AUX1: "x=u" if "(x, u) \<in> (adm_edges f' l')\<^sup>*" for x
              using that l'.relabel_u_no_incoming_adm[OF RELABEL[symmetric]]
              by (auto elim: rtranclE)
              
            have TS1: "is_top_sorted (adm_edges f l) (L_left @ L_right')"
              using L_sorted by (auto intro: is_top_sorted_remove_elem)

            \<comment> \<open>Intuition:\<close>
              \<comment> \<open>new edges come from \<open>u\<close>, but \<open>u\<close> has no incoming edges, nor is it in \<open>L_left@L_right'\<close>.\<close>
              \<comment> \<open>thus, these new edges cannot add effective constraints.\<close>
            from l'.adm_edges_leaving_u 
              and l'.relabel_u_no_incoming_adm[OF RELABEL[symmetric]]
            have "adm_edges f' l' \<subseteq> adm_edges f l \<union> {u}\<times>UNIV" 
              and "adm_edges f' l' \<inter> UNIV\<times>{u}={}" by auto
            from is_top_sorted_isolated_constraint[OF this _ TS1]    
            have AUX2: "is_top_sorted (adm_edges f' l') (L_left @ L_right')" 
              by simp   
                
            show "rtf_invar c s t f' l' n' [u] (L_left @ L_right')"
              apply unfold_locales
              subgoal by simp  
              subgoal using AUX2 by (auto simp: is_top_sorted_cons dest!: AUX1)
              subgoal using L_set by auto
              done    
          qed  
          subgoal using l'.algo_rel by (auto dest: rtranclD)
          subgoal proof -
            assume NO_RELABEL[simp]: "l' u = l u"
            \<comment> \<open>Intuition: non-zero excess would imply an admissible edge contrary to \<open>top_sorted\<close>.\<close>
            have AUX: "excess f' v = 0" if "v\<in>set L_left" for v
            proof (rule ccontr)
              from that \<open>u\<notin>set L_left\<close> have "u \<noteq> v" by blast 
              moreover assume "excess f' v \<noteq> 0"
              moreover from that left_no_excess have "excess f v = 0" by auto
              ultimately have "(u,v)\<in>adm_edges f l"    
                using l'.no_relabel_excess[OF NO_RELABEL[symmetric]] 
                by auto
              
              with L_sorted that show False
                by (auto simp: is_top_sorted_append is_top_sorted_cons)
            qed      
            show "rtf_invar c s t f' l' n' (L_left @ [u]) L_right'"  
              apply unfold_locales
              subgoal by (auto simp: AUX)  
              subgoal 
                apply (rule is_top_sorted_antimono[
                  OF l'.no_relabel_adm_edges[OF NO_RELABEL[symmetric]]])
                using L_sorted by simp  
              subgoal using L_set by auto
              done
          qed
          subgoal using l'.algo_rel by (auto dest: rtranclD)
          done    
      qed
      done  
  qed
  subgoal by (auto intro: rtf_invar.terminated_imp_maxflow)  
  done
    
end \<comment> \<open>Network\<close> 
  
end
