section \<open>Implementation of Relabel-to-Front\<close>
theory Relabel_To_Front_Impl
imports
  Relabel_To_Front
  Prpu_Common_Impl
begin
  
  
subsection \<open>Basic Operations\<close>  
  
context Network_Impl
begin
  
subsubsection \<open>Neighbor Lists\<close>
definition n_init :: "(node \<Rightarrow> node list) \<Rightarrow> (node \<Rightarrow> node list) nres" 
  where "n_init am \<equiv> return (am( s := [], t := []) )"
  
definition n_at_end :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> bool nres" 
  where "n_at_end n u \<equiv> do {
    assert (u\<in>V-{s,t});
    return (n u = [])
  }"
    
definition n_get_hd :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> node nres"    
  where "n_get_hd n u \<equiv> do {
    assert (u\<in>V-{s,t} \<and> n u \<noteq> []);
    return (hd (n u))
  }"

definition n_move_next 
  :: "(node \<Rightarrow> node list) \<Rightarrow> node \<Rightarrow> (node \<Rightarrow> node list) nres"
  where "n_move_next n u \<equiv> do {
    assert (u\<in>V-{s,t} \<and> n u \<noteq> []);
    return (n (u := tl (n u)))
  }"
    
definition n_reset 
  :: "(node \<Rightarrow> node list) \<Rightarrow> (node \<Rightarrow> node list) \<Rightarrow> node 
    \<Rightarrow> (node \<Rightarrow> node list) nres"
  where "n_reset am n u \<equiv> do {
    assert (u\<in>V-{s,t});
    return (n (u := am u))
  }"
  
lemma n_init_refine[refine2]: 
  assumes AM: "is_adj_map am"  
  shows "n_init am 
    \<le> (spec c. (c, rtf_init_n) \<in> (nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel))"
proof -
  have[simp]: "am v = []" if "v\<notin>V" for v
  proof -
    from that have "adjacent_nodes v = {}" 
      unfolding adjacent_nodes_def using E_ss_VxV by auto
    thus ?thesis using am_to_adj_nodes_refine[OF AM] 
      by (auto simp: list_set_rel_def in_br_conv)
  qed
  show ?thesis      
    unfolding n_init_def rtf_init_n_def 
    by (auto 
        simp: pw_le_iff refine_pw_simps list_set_autoref_empty 
        simp: am_to_adj_nodes_refine[OF AM])
qed  
  
subsection \<open>Refinement to Basic Operations\<close>  
  
subsubsection \<open>Discharge\<close>  
definition "discharge2 am x cf l n u \<equiv> do {  
  assert (u \<in> V);
  monadic_WHILEIT (\<lambda>_. True) 
    (\<lambda>((x,cf),l,n). do { xu \<leftarrow> x_get x u; return (xu \<noteq> 0) } ) 
    (\<lambda>((x,cf),l,n). do {
      at_end \<leftarrow> n_at_end n u;
      if at_end then do {
        l \<leftarrow> relabel2 am cf l u;
        n \<leftarrow> n_reset am n u;
        return ((x,cf),l,n)
      } else do {
        v \<leftarrow> n_get_hd n u;
        cfuv \<leftarrow> cf_get cf (u,v);
        lu \<leftarrow> l_get l u;
        lv \<leftarrow> l_get l v;
        if (cfuv \<noteq> 0 \<and> lu = lv + 1) then do {
          (x,cf) \<leftarrow> push2 x cf (u,v);
          return ((x,cf),l,n)
        } else do {
          n \<leftarrow> n_move_next n u;
          return ((x,cf),l,n)
        }
      }
    }) ((x,cf),l,n)
}"

lemma discharge_structure_refine_aux:
  assumes SR: "(ni,n)\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"
  assumes SU: "(ui,u)\<in>Id"  
  assumes fNR: "fNi \<le> \<Down>R fN"
  assumes UIV: "u\<in>V-{s,t}"  
  assumes fSR: "\<And>v vi vs. \<lbrakk> 
      (vi,v)\<in>Id; v\<in>n u; ni u = v#vs; (v#vs,n u)\<in>\<langle>nat_rel\<rangle>list_set_rel 
    \<rbrakk> \<Longrightarrow> fSi vi \<le> \<Down>R (fS v)"
  shows
  "( do {
    at_end \<leftarrow> n_at_end ni ui;
    if at_end then fNi
    else do {
      v \<leftarrow> n_get_hd ni ui;
      fSi v
    }
  } ) \<le> \<Down>R (

  do {
    v \<leftarrow> select v. v\<in>n u;
    case v of
      None \<Rightarrow> fN
    | Some v \<Rightarrow> fS v
  })" (is "?lhs \<le>\<Down>R ?rhs")
  unfolding n_at_end_def n_get_hd_def
  apply (simp only: nres_monad_laws)  
  apply (cases "ni u")
  subgoal
    using fun_relD[OF SR SU] SU UIV fNR
    by (auto simp: list_set_rel_def in_br_conv pw_le_iff refine_pw_simps)
    
  subgoal for v vs
    using fun_relD[OF SR SU] SU UIV
    using fSR[OF IdI[of v], of vs]  
    apply (clarsimp 
        simp: list_set_rel_def in_br_conv pw_le_iff refine_pw_simps 
        split: option.splits)
    by fastforce  
  done    
  
lemma xf_rel_RELATES[refine_dref_RELATES]: "RELATES xf_rel" 
  by (auto simp: RELATES_def)
  
lemma discharge2_refine[refine]:     
  assumes A: "((x,cf),f) \<in> xf_rel"
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(li,l)\<in>Id" "(ui,u)\<in>Id"
  assumes NR: "(ni,n)\<in>nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"  
  shows "discharge2 am x cf li ni ui 
    \<le> \<Down>(xf_rel \<times>\<^sub>r Id \<times>\<^sub>r (nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel)) (discharge f l n u)"  
  unfolding discharge2_def discharge_def
  apply (rewrite in "monadic_WHILEIT _ _ \<hole> _" vcg_intro_frame)  
  apply refine_rcg  
  apply (vc_solve simp: A NR)
  subgoal by (simp add: xf_rel_def x_get_def)  
  subgoal for f l n x cf ni   
    apply (subst vcg_rem_frame)
    unfolding n_reset_def cf_get_def l_get_def n_move_next_def  
    apply (simp only: nres_monad_laws)  
    apply (rule discharge_structure_refine_aux; (refine_vcg AM)?; (assumption)?)  
    apply (vc_solve simp: fun_relD fun_relD[OF AM])  
    subgoal for v vs unfolding xf_rel_def Graph.E_def by auto
    subgoal for v vs by (auto simp: list_set_rel_def in_br_conv)  
    done
  done
  
subsubsection \<open> Initialization of Queue \<close>
    
lemma V_is_adj_nodes: "V = { v . adjacent_nodes v \<noteq> {} }"
  unfolding V_def adjacent_nodes_def by auto
    
definition "init_CQ am \<equiv> do {
  let cardV=0;
  let Q=[];
  nfoldli [0..<N] (\<lambda>_. True) (\<lambda>v (cardV,Q). do {
    assert (v<N);
    inV \<leftarrow> am_is_in_V am v;
    if inV then do {
      let cardV = cardV + 1;
      if v\<noteq>s \<and> v\<noteq>t then
        return (cardV,v#Q)
      else 
        return (cardV,Q)
    } else
      return (cardV,Q)
  }) (cardV,Q)
}"    

lemma init_CQ_correct[THEN order_trans, refine_vcg]:
  assumes AM: "is_adj_map am"  
  shows "init_CQ am \<le> SPEC (\<lambda>(C,Q). C = card V \<and> distinct Q \<and> set Q = V-{s,t})"
  unfolding init_CQ_def  
  apply (refine_vcg 
      nfoldli_rule[where 
        I="\<lambda>l1 _ (C,Q). 
             C = card (V\<inter>set l1) \<and> distinct Q \<and> set Q = (V\<inter>set l1)-{s,t} "]
      )  
  apply (clarsimp_all simp: am_to_adj_nodes_refine[OF AM])
  using V_ss by (auto simp: upt_eq_lel_conv Int_absorb2)
    
subsubsection \<open>Main Algorithm\<close>    
    
definition "relabel_to_front2 am \<equiv> do {
  (cardV, L_right) \<leftarrow> init_CQ am;

  xcf \<leftarrow> pp_init_xcf2 am;
  l \<leftarrow> l_init cardV;
  n \<leftarrow> n_init am;

  let L_left=[];

  ((x,cf),l,n,L_left,L_right) \<leftarrow> while\<^sub>T 
    (\<lambda>((x,cf),l,n,L_left,L_right). L_right \<noteq> []) 
    (\<lambda>((x,cf),l,n,L_left,L_right). do {
      assert (L_right \<noteq> []);
      let u = hd L_right;
      old_lu \<leftarrow> l_get l u;
  
      ((x,cf),l,n) \<leftarrow> discharge2 am x cf l n u;
  
      lu \<leftarrow> l_get l u;
      if (lu \<noteq> old_lu) then do {
        \<comment> \<open>Move \<open>u\<close> to front of \<open>l\<close>, and restart scanning \<open>L\<close>. The cost for\<close>
        \<comment> \<open>\<open>rev_append\<close> is amortized by going to next node in \<open>L\<close>\<close>
        let (L_left,L_right) = ([u],rev_append L_left (tl L_right));
        return ((x,cf),l,n,L_left,L_right)
      } else do {
        \<comment> \<open>Goto next node in \<open>L\<close>\<close>
        let (L_left,L_right) = (u#L_left, tl L_right);
        return ((x,cf),l,n,L_left,L_right)
      }
  
    }) (xcf,l,n,L_left,L_right);

  return cf
}"
  
    
lemma relabel_to_front2_refine[refine]: 
  assumes AM: "is_adj_map am"  
  shows "relabel_to_front2 am 
    \<le> \<Down>(br (flow_of_cf) (RPreGraph c s t)) relabel_to_front"
proof -
  define s_rel 
    :: "( _ \<times> (
       capacity_impl flow 
    \<times> (nat\<Rightarrow>nat) 
    \<times> (node\<Rightarrow>node set) 
    \<times> node list 
    \<times> node list)) set"
    where "s_rel \<equiv> 
       xf_rel 
    \<times>\<^sub>r Id 
    \<times>\<^sub>r (nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel) 
    \<times>\<^sub>r br rev (\<lambda>_. True) 
    \<times>\<^sub>r Id"
  
  have [refine_dref_RELATES]: "RELATES s_rel" unfolding RELATES_def ..
      
  {
    fix f l n
    assume "neighbor_invar c s t f l n"
    then interpret neighbor_invar c s t f l n .  
    have G1: "flow_of_cf cf = f" by (rule fo_rg_inv)
    have G2: "RPreGraph c s t cf" by (rule is_RPreGraph)
    note G1 G2    
  } note AUX1=this   
      
  have AUXR: "do {
      (cardV, L_right) \<leftarrow> init_CQ am;
      xcf \<leftarrow> pp_init_xcf2 am;
      l \<leftarrow> l_init cardV;
      n \<leftarrow> n_init am;
      Fi L_right xcf l n
    }
    \<le> \<Down>R (do {
      L_right \<leftarrow> spec l. distinct l \<and> set l = V - {s, t};
      F L_right
    })
  " 
  if "\<And>L_right xcf n. 
    \<lbrakk> (xcf,pp_init_f)\<in>xf_rel; (n,rtf_init_n) \<in> nat_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel \<rbrakk>
    \<Longrightarrow> Fi L_right xcf pp_init_l n \<le> \<Down>R (F L_right)"
  for Fi F R
    unfolding l_init_def
    apply (rule refine2specI)
    supply pp_init_xcf2_refine
            [OF AM, unfolded conc_fun_RETURN, THEN order_trans, refine_vcg]  
    supply n_init_refine[OF AM,THEN order_trans, refine_vcg]  
    apply (refine_vcg AM V_ss)
    apply clarsimp  
    subgoal for L_right x cf n
      using that[of "(x,cf)" n L_right]
      unfolding pp_init_l_def  
      by (clarsimp simp: pw_le_iff refine_pw_simps; meson)  
    done  
  show ?thesis
    unfolding relabel_to_front2_def relabel_to_front_def Let_def l_get_def
    apply (simp only: nres_monad_laws)  
    apply (rule AUXR)  
    apply (refine_rcg)
    apply refine_dref_type
    unfolding s_rel_def
    apply (vc_solve 
        simp: in_br_conv rev_append_eq xf_rel_def AUX1 fun_relD 
        simp: am_to_adj_nodes_refine[OF AM])
    done  
qed  
  
  
subsection \<open>Refinement to Efficient Data Structures\<close>  
  
context includes Network_Impl_Sepref_Register 
begin  
  sepref_register n_init  
  sepref_register n_at_end
  sepref_register n_get_hd
  sepref_register n_move_next
  sepref_register n_reset
  sepref_register discharge2
  sepref_register "init_CQ"
  sepref_register relabel_to_front2
end  
  
subsubsection \<open>Neighbor Lists by Array of Lists\<close>  
definition "n_assn \<equiv> is_nf N ([]::nat list)"    
    
definition (in -) "n_init_impl s t am \<equiv> do {
  n \<leftarrow> array_copy am;
  n \<leftarrow> Array.upd s [] n;
  n \<leftarrow> Array.upd t [] n;
  return n
}"      
    
lemma [sepref_fr_rules]: 
  "(n_init_impl s t,PR_CONST n_init) \<in> am_assn\<^sup>k \<rightarrow>\<^sub>a n_assn" 
  apply sepref_to_hoare
  unfolding am_assn_def n_assn_def n_init_impl_def n_init_def
  by (sep_auto)  
    
definition (in -) "n_at_end_impl n u \<equiv> do {
  nu \<leftarrow> Array.nth n u;
  return (is_Nil nu)
}"
    
lemma [sepref_fr_rules]: 
  "(uncurry n_at_end_impl, uncurry (PR_CONST n_at_end)) 
  \<in> n_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"  
  apply sepref_to_hoare unfolding n_at_end_impl_def n_at_end_def n_assn_def
  by (sep_auto simp: refine_pw_simps split: list.split)
  
definition (in -) "n_get_hd_impl n u \<equiv> do {
  nu \<leftarrow> Array.nth n u;
  return (hd nu)
}"      
lemma [sepref_fr_rules]: 
  "(uncurry n_get_hd_impl, uncurry (PR_CONST n_get_hd)) 
  \<in> n_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a node_assn"  
  apply sepref_to_hoare unfolding n_get_hd_impl_def n_get_hd_def n_assn_def
  by (sep_auto simp: refine_pw_simps)
  
definition (in -) "n_move_next_impl n u \<equiv> do {
  nu \<leftarrow> Array.nth n u;
  n \<leftarrow> Array.upd u (tl nu) n;
  return n
}" 
lemma [sepref_fr_rules]: 
  "(uncurry n_move_next_impl, uncurry (PR_CONST n_move_next)) 
  \<in> n_assn\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a n_assn"  
  apply sepref_to_hoare 
  unfolding n_move_next_impl_def n_move_next_def n_assn_def
  by (sep_auto simp: refine_pw_simps)
  
definition (in -) "n_reset_impl am n u \<equiv> do {
  nu \<leftarrow> Array.nth am u;
  n \<leftarrow> Array.upd u nu n;
  return n
}"
lemma [sepref_fr_rules]: 
  "(uncurry2 n_reset_impl, uncurry2 (PR_CONST n_reset)) 
  \<in> am_assn\<^sup>k *\<^sub>a n_assn\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a n_assn"  
  apply sepref_to_hoare 
  unfolding n_reset_impl_def n_reset_def n_assn_def am_assn_def
  by (sep_auto simp: refine_pw_simps)
  
subsubsection \<open>Discharge\<close>  
sepref_thm discharge_impl is "uncurry5 (PR_CONST discharge2)" 
  :: "am_assn\<^sup>k *\<^sub>a x_assn\<^sup>d *\<^sub>a cf_assn\<^sup>d *\<^sub>a l_assn\<^sup>d *\<^sub>a n_assn\<^sup>d *\<^sub>a node_assn\<^sup>k 
    \<rightarrow>\<^sub>a (x_assn \<times>\<^sub>a cf_assn) \<times>\<^sub>a l_assn \<times>\<^sub>a n_assn"  
  unfolding discharge2_def PR_CONST_def
  by sepref  
concrete_definition (in -) discharge_impl 
  uses Network_Impl.discharge_impl.refine_raw is "(uncurry5 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = discharge_impl.refine[OF Network_Impl_axioms]    

subsubsection \<open>Initialization of Queue\<close>  
  
sepref_thm init_CQ_impl is "(PR_CONST init_CQ)" 
  :: "am_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn \<times>\<^sub>a list_assn nat_assn"
  unfolding init_CQ_def PR_CONST_def
  apply (rewrite HOL_list.fold_custom_empty)
  by sepref
concrete_definition (in -) init_CQ_impl 
  uses Network_Impl.init_CQ_impl.refine_raw is "(?f,_)\<in>_"
lemmas [sepref_fr_rules] = init_CQ_impl.refine[OF Network_Impl_axioms]    
  
subsubsection \<open>Main Algorithm\<close>  
sepref_thm relabel_to_front_impl is 
  "(PR_CONST relabel_to_front2)" :: "am_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn"  
  unfolding relabel_to_front2_def PR_CONST_def
  supply [[goals_limit = 1]]  
  apply (rewrite in "Let [] _" HOL_list.fold_custom_empty)
  apply (rewrite in "[_]" HOL_list.fold_custom_empty)
  by sepref  
concrete_definition (in -) relabel_to_front_impl 
  uses Network_Impl.relabel_to_front_impl.refine_raw is "(?f,_)\<in>_"
lemmas [sepref_fr_rules] = relabel_to_front_impl.refine[OF Network_Impl_axioms]
  
end \<comment> \<open>Network Implementation Locale\<close> 
  
export_code relabel_to_front_impl checking SML_imp
  
subsection \<open>Combination with Network Checker and Correctness\<close>  
context Network_Impl begin
  
  theorem relabel_to_front_impl_correct[sep_heap_rules]: 
    assumes AM: "is_adj_map am"
    shows "
      <am_assn am ami> 
        relabel_to_front_impl c s t N ami
      <\<lambda>cfi. \<exists>\<^sub>Acf. cf_assn cf cfi 
                * \<up>(isMaxFlow (flow_of_cf cf) \<and> RGraph_Impl c s t N cf)>\<^sub>t"
  proof -
    note relabel_to_front2_refine[OF AM]    
    also note relabel_to_front_correct
    finally have R1: 
      "relabel_to_front2 am 
      \<le> \<Down> (br flow_of_cf (RPreGraph c s t)) (SPEC isMaxFlow)" .  

    have [simp]: "nofail (\<Down>R (RES X))" for R X by (auto simp: refine_pw_simps)
        
    note R2 = relabel_to_front_impl.refine[
      OF Network_Impl_axioms, to_hnr, unfolded autoref_tag_defs]
    note R3 = hn_refine_ref[OF R1 R2, of ami]  
    note R4 = R3[unfolded hn_ctxt_def pure_def, THEN hn_refineD, simplified]

    note RGII = rgraph_and_network_impl_imp_rgraph_impl[OF 
      RPreGraph.maxflow_imp_rgraph
      Network_Impl_axioms
        ]  
      
    show ?thesis  
      by (sep_auto heap: R4 simp: pw_le_iff refine_pw_simps in_br_conv RGII)
  qed
end    

definition "relabel_to_front_impl_tab_am c s t N am \<equiv> do {
  ami \<leftarrow> Array.make N am;  \<comment> \<open>TODO/DUP: Called \<open>init_ps\<close> in Edmonds-Karp impl\<close>
  relabel_to_front_impl c s t N ami
}"  
  
theorem relabel_to_front_impl_tab_am_correct[sep_heap_rules]: 
  assumes NW: "Network c s t"
  assumes VN: "Graph.V c \<subseteq> {0..<N}"
  assumes ABS_PS: "Graph.is_adj_map c am"
  shows "
    <emp> 
      relabel_to_front_impl_tab_am c s t N am
    <\<lambda>cfi. \<exists>\<^sub>Acf. 
        asmtx_assn N id_assn cf cfi 
      * \<up>(Network.isMaxFlow c s t (Network.flow_of_cf c cf)
        \<and> RGraph_Impl c s t N cf
        )>\<^sub>t"
proof -
  interpret Network c s t by fact
  interpret Network_Impl c s t N using VN by unfold_locales    
  
  from ABS_PS have [simp]: "am u = []" if "u\<ge>N" for u
    unfolding is_adj_map_def
    using E_ss_VxV VN that 
    apply (subgoal_tac "u\<notin>V") 
    by (auto simp del: inV_less_N)
  
  show ?thesis
    unfolding relabel_to_front_impl_tab_am_def 
    apply vcg
    apply (rule 
        Hoare_Triple.cons_rule[OF _ _ relabel_to_front_impl_correct[OF ABS_PS]])
    subgoal unfolding am_assn_def is_nf_def by sep_auto
    subgoal unfolding cf_assn_def by sep_auto
    done  
qed        
  
definition "relabel_to_front el s t \<equiv> do {
  case prepareNet el s t of
    None \<Rightarrow> return None
  | Some (c,am,N) \<Rightarrow> do {
      cf \<leftarrow> relabel_to_front_impl_tab_am c s t N am;
      return (Some (c,am,N,cf))
  }
}"
export_code relabel_to_front checking SML_imp

text \<open>
  Main correctness statement:
  \<^item> If \<open>relabel_to_front\<close> returns \<open>None\<close>, the edge list was invalid or described 
    an invalid network. 
  \<^item> If it returns \<open>Some (c,am,N,cfi)\<close>, then the edge list is valid and describes
    a valid network. Moreover, \<open>cfi\<close> is an integer square matrix of 
    dimension \<open>N\<close>, which describes a valid residual graph in the network, whose
    corresponding flow is maximal. Finally, \<open>am\<close> is a valid adjacency map of the
    graph, and the nodes of the graph are integers less than \<open>N\<close>.
\<close>  
theorem relabel_to_front_correct:
  "<emp>
  relabel_to_front el s t
  <\<lambda>
    None \<Rightarrow> \<up>(\<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)
  | Some (c,am,N,cfi) \<Rightarrow> 
      \<up>(c = ln_\<alpha> el \<and> ln_invar el) 
    * (\<exists>\<^sub>Acf. asmtx_assn N int_assn cf cfi
          * \<up>(RGraph_Impl c s t N cf 
            \<and> Network.isMaxFlow c s t (Network.flow_of_cf c cf))) 
    * \<up>(Graph.is_adj_map c am)
  >\<^sub>t
  "
  unfolding relabel_to_front_def
  using prepareNet_correct[of el s t]
  by (sep_auto simp: ln_rel_def in_br_conv)
  

end
