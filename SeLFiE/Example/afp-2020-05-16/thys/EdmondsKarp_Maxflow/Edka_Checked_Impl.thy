section \<open>Combination with Network Checker\<close>
theory Edka_Checked_Impl
imports Flow_Networks.NetCheck EdmondsKarp_Impl
begin
text \<open>
  In this theory, we combine the Edmonds-Karp implementation with the 
  network checker.
\<close>

subsection \<open>Adding Statistic Counters\<close>
text \<open>We first add some statistic counters, that we use for profiling\<close>
definition stat_outer_c :: "unit Heap" where "stat_outer_c = return ()"
lemma insert_stat_outer_c: "m = stat_outer_c \<then> m" 
  unfolding stat_outer_c_def by simp
definition stat_inner_c :: "unit Heap" where "stat_inner_c = return ()"
lemma insert_stat_inner_c: "m = stat_inner_c \<then> m" 
  unfolding stat_inner_c_def by simp

code_printing
  code_module stat \<rightharpoonup> (SML) \<open>
    structure stat = struct
      val outer_c = ref 0;
      fun outer_c_incr () = (outer_c := !outer_c + 1; ())
      val inner_c = ref 0;
      fun inner_c_incr () = (inner_c := !inner_c + 1; ())
    end
    \<close>
| constant stat_outer_c \<rightharpoonup> (SML) "stat.outer'_c'_incr"  
| constant stat_inner_c \<rightharpoonup> (SML) "stat.inner'_c'_incr"  


schematic_goal [code]: "edka_imp_run_0 s t N f brk = ?foo"
  apply (subst edka_imp_run.code)
  apply (rewrite in "\<hole>" insert_stat_outer_c)
  by (rule refl)
  
thm bfs_impl.code
schematic_goal [code]: "bfs_impl_0 succ_impl ci ti x = ?foo"
  apply (subst bfs_impl.code)
  apply (rewrite in "imp_nfoldli _ _ \<hole> _" insert_stat_inner_c)
  by (rule refl)

subsection \<open>Combined Algorithm\<close>

definition "edmonds_karp el s t \<equiv> do {
  case prepareNet el s t of
    None \<Rightarrow> return None
  | Some (c,am,N) \<Rightarrow> do {
      f \<leftarrow> edka_imp c s t N am ;
      return (Some (c,am,N,f))
  }
}"
export_code edmonds_karp checking SML

lemma network_is_impl: "Network c s t \<Longrightarrow> Network_Impl c s t" by intro_locales

theorem edmonds_karp_correct:
  "<emp> edmonds_karp el s t <\<lambda>
      None \<Rightarrow> \<up>(\<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)
    | Some (c,am,N,fi) \<Rightarrow> 
      \<exists>\<^sub>Af. Network_Impl.is_rflow c s t N f fi 
      * \<up>(ln_\<alpha> el = c \<and> Graph.is_adj_map c am
        \<and> Network.isMaxFlow c s t f
        \<and> ln_invar el \<and> Network c s t \<and> Graph.V c \<subseteq> {0..<N})
  >\<^sub>t"
  unfolding edmonds_karp_def
  using prepareNet_correct[of el s t]
  by (sep_auto 
    split: option.splits 
    heap: Network_Impl.edka_imp_correct 
    simp: ln_rel_def br_def network_is_impl)

context
begin
private definition "is_rflow \<equiv> Network_Impl.is_rflow"

text_raw \<open>\DefineSnippet{edmonds_karp_correct}{\<close>       
theorem
  fixes el defines "c \<equiv> ln_\<alpha> el"
  shows 
    "<emp> 
      edmonds_karp el s t 
    <\<lambda> None \<Rightarrow> \<up>(\<not>ln_invar el \<or> \<not>Network c s t)
     | Some (_,_,N,cf) \<Rightarrow> 
         \<up>(ln_invar el \<and> Network c s t \<and> Graph.V c \<subseteq> {0..<N})
       * (\<exists>\<^sub>Af. is_rflow c s t N f cf * \<up>(Network.isMaxFlow c s t f))
    >\<^sub>t"
text_raw \<open>}%EndSnippet\<close>
  unfolding c_def is_rflow_def
  by (sep_auto heap: edmonds_karp_correct[of el s t] split: option.split)

end

subsection \<open>Usage Example: Computing Maxflow Value \<close>
text \<open>We implement a function to compute the value of the maximum flow.\<close>


lemma (in Network) am_s_is_incoming:
  assumes "is_adj_map am"
  shows "E``{s} = set (am s)"
  using assms no_incoming_s
  unfolding is_adj_map_def
  by auto
  
context RGraph begin

  lemma val_by_adj_map:
    assumes "is_adj_map am"
    shows "f.val = (\<Sum>v\<in>set (am s). c (s,v) - cf (s,v))"
  proof -
    have "f.val = (\<Sum>v\<in>E``{s}. c (s,v) - cf (s,v))"
      unfolding f.val_alt
      by (simp add: sum_outgoing_pointwise f_def flow_of_cf_def)
    also have "\<dots> = (\<Sum>v\<in>set (am s). c (s,v) - cf (s,v))"  
      by (simp add: am_s_is_incoming[OF assms])
    finally show ?thesis . 
  qed  
      
end


context Network 
begin

  definition "get_cap e \<equiv> c e"
  definition (in -) get_am :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> node list" 
    where "get_am am v \<equiv> am v"

  definition "compute_flow_val am cf \<equiv> do {
      let succs = get_am am s;
      sum_impl 
      (\<lambda>v. do {
        let csv = get_cap (s,v);
        cfsv \<leftarrow> cf_get cf (s,v);
        return (csv - cfsv)
      }) (set succs)
    }"

  lemma (in RGraph) compute_flow_val_correct:
    assumes "is_adj_map am"
    shows "compute_flow_val am cf \<le> (spec v. v = f.val)"
    unfolding val_by_adj_map[OF assms]
    unfolding compute_flow_val_def cf_get_def get_cap_def get_am_def
    apply (refine_vcg sum_impl_correct)
    apply (vc_solve simp: s_node)
    unfolding am_s_is_incoming[symmetric, OF assms] 
    by (auto simp: V_def)

  text \<open>For technical reasons (poor foreach-support of Sepref tool), 
    we have to add another refinement step: \<close>  
  definition "compute_flow_val2 am cf \<equiv> (do {
    let succs = get_am am s;
    nfoldli succs (\<lambda>_. True)
     (\<lambda>x a. do {
           b \<leftarrow> do {
               let csv = get_cap (s, x);
               cfsv \<leftarrow> cf_get cf (s, x);
               return (csv - cfsv)
             };
           return (a + b)
         })
     0
  })"  

  lemma (in RGraph) compute_flow_val2_correct:
    assumes "is_adj_map am"
    shows "compute_flow_val2 am cf \<le> (spec v. v = f.val)"
  proof -
    have [refine_dref_RELATES]: "RELATES (\<langle>Id\<rangle>list_set_rel)" 
      by (simp add: RELATES_def)
    show ?thesis
      apply (rule order_trans[OF _ compute_flow_val_correct[OF assms]])
      unfolding compute_flow_val2_def compute_flow_val_def sum_impl_def
      apply (rule refine_IdD)
      apply (refine_rcg LFO_refine bind_refine')
      apply refine_dref_type
      apply vc_solve
      using assms
      by (auto 
          simp: list_set_rel_def br_def get_am_def is_adj_map_def 
          simp: refine_pw_simps)
  qed    
    


end

context Edka_Impl begin
  term is_am

  lemma [sepref_import_param]: "(c,PR_CONST get_cap) \<in> Id\<times>\<^sub>rId \<rightarrow> Id" 
    by (auto simp: get_cap_def)
  lemma [def_pat_rules]: 
    "Network.get_cap$c \<equiv> UNPROTECT get_cap" by simp
  sepref_register 
    "PR_CONST get_cap" :: "node\<times>node \<Rightarrow> capacity_impl"

  lemma [sepref_import_param]: "(get_am,get_am) \<in> Id \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>list_rel" 
    by (auto simp: get_am_def intro!: ext)

  schematic_goal compute_flow_val_imp:
    fixes am :: "node \<Rightarrow> node list" and cf :: "capacity_impl graph"
    notes [id_rules] = 
      itypeI[Pure.of am "TYPE(node \<Rightarrow> node list)"]
      itypeI[Pure.of cf "TYPE(capacity_impl i_mtx)"]
    notes [sepref_import_param] = IdI[of N] IdI[of am]
    shows "hn_refine 
      (hn_ctxt (asmtx_assn N id_assn) cf cfi)
      (?c::?'d Heap) ?\<Gamma> ?R (compute_flow_val2 am cf)"
    unfolding compute_flow_val2_def
    using [[id_debug, goals_limit = 1]]
    by sepref
  concrete_definition (in -) compute_flow_val_imp for c s N am cfi
    uses Edka_Impl.compute_flow_val_imp
  prepare_code_thms (in -) compute_flow_val_imp_def
end

context Network_Impl begin

lemma compute_flow_val_imp_correct_aux: 
  assumes VN: "Graph.V c \<subseteq> {0..<N}"
  assumes ABS_PS: "is_adj_map am"
  assumes RG: "RGraph c s t cf"
  shows "
    <asmtx_assn N id_assn cf cfi> 
      compute_flow_val_imp c s N am cfi
    <\<lambda>v. asmtx_assn N id_assn cf cfi * \<up>(v = Flow.val c s (flow_of_cf cf))>\<^sub>t"
proof -
  interpret rg: RGraph c s t cf by fact

  have EI: "Edka_Impl c s t N" by unfold_locales fact
  from hn_refine_ref[OF 
      rg.compute_flow_val2_correct[OF ABS_PS] 
      compute_flow_val_imp.refine[OF EI], of cfi]
  show ?thesis
    apply (simp add: hn_ctxt_def pure_def hn_refine_def rg.f_def)
    apply (erule cons_post_rule)
    apply sep_auto
    done
qed

lemma compute_flow_val_imp_correct: 
  assumes VN: "Graph.V c \<subseteq> {0..<N}"
  assumes ABS_PS: "Graph.is_adj_map c am"
  shows "
    <is_rflow N f cfi> 
      compute_flow_val_imp c s N am cfi
    <\<lambda>v. is_rflow N f cfi * \<up>(v = Flow.val c s f)>\<^sub>t"
  apply (rule hoare_triple_preI)  
  apply (clarsimp simp: is_rflow_def)
  apply vcg
  apply (rule cons_rule[OF _ _ compute_flow_val_imp_correct_aux[where cfi=cfi]])
  apply (sep_auto simp: VN ABS_PS)+
  done

end


definition "edmonds_karp_val el s t \<equiv> do {
  r \<leftarrow> edmonds_karp el s t;
  case r of
    None \<Rightarrow> return None
  | Some (c,am,N,cfi) \<Rightarrow> do {
      v \<leftarrow> compute_flow_val_imp c s N am cfi;
      return (Some v)
    } 
}"

theorem edmonds_karp_val_correct:
  "<emp> edmonds_karp_val el s t <\<lambda>
    None \<Rightarrow> \<up>(\<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)
  | Some v \<Rightarrow> \<up>(\<exists>f N. 
          ln_invar el \<and> Network (ln_\<alpha> el) s t 
        \<and> Graph.V (ln_\<alpha> el) \<subseteq> {0..<N}
        \<and> Network.isMaxFlow (ln_\<alpha> el) s t f
        \<and> v = Flow.val (ln_\<alpha> el) s f)  
        >\<^sub>t"
  unfolding edmonds_karp_val_def
  by (sep_auto 
    intro: network_is_impl
    heap: edmonds_karp_correct Network_Impl.compute_flow_val_imp_correct)      


end
