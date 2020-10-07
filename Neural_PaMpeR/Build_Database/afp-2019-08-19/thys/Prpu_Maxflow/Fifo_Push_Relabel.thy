section \<open>FIFO Push Relabel Algorithm\<close>
theory Fifo_Push_Relabel
imports 
  Flow_Networks.Refine_Add_Fofu
  Generic_Push_Relabel 
begin
text \<open>The FIFO push-relabel algorithm maintains a first-in-first-out queue
  of active nodes. As long as the queue is not empty, it discharges the 
  first node of the queue. 

  Discharging repeatedly applied push operations from the node.
  If no more push operations are possible, and the node is still active, 
  it is relabeled and enqueued.

  Moreover, we implement the gap heuristics, which may accelerate relabeling
  if there is a gap in the label values, i.e., a label value that is assigned 
  to no node.
\<close>

subsection \<open>Implementing the Discharge Operation\<close>  
  
context Network
begin

text \<open>
  First, we implement push and relabel operations that maintain 
  a queue of all active nodes. 
\<close>  
(* TODO: Use push and relabel from Prpu_Common_Inst.thy ! *)  
definition "fifo_push f l Q \<equiv> \<lambda>(u,v). do {
  assert (push_precond f l (u,v));
  assert (Labeling c s t f l);
  let Q = (if v\<noteq>s \<and> v\<noteq>t \<and> excess f v = 0 then Q@[v] else Q);
  return (push_effect f (u,v),Q)
}"  
  
text \<open>For the relabel operation, we assume that
  only active nodes are relabeled, and enqueue the relabeled node.
\<close>  
definition "fifo_gap_relabel f l Q u \<equiv> do {
  assert (u\<in>V-{s,t});
  assert (Height_Bounded_Labeling c s t f l);
  let Q = Q@[u];
  assert (relabel_precond f l u);
  assert (l u < 2*card V \<and> relabel_effect f l u u < 2*card V);
  let l = gap_relabel_effect f l u;
  return (l,Q)
}"  

text \<open>The discharge operation iterates over the edges, and pushes 
  flow, as long as then node is active. If the node is still active after all 
  edges have been saturated, the node is relabeled.
\<close>
definition "fifo_discharge f\<^sub>0 l Q \<equiv> do {  
  assert (Q\<noteq>[]);
  let u=hd Q; let Q=tl Q;
  assert (u\<in>V \<and> u\<noteq>s \<and> u\<noteq>t);

  (f,l,Q) \<leftarrow> FOREACHc {v . (u,v)\<in>cfE_of f\<^sub>0} (\<lambda>(f,l,Q). excess f u \<noteq> 0) (\<lambda>v (f,l,Q). do {
    if (l u = l v + 1) then do {
      (f',Q) \<leftarrow> fifo_push f l Q (u,v);
      assert (\<forall>v'. v'\<noteq>v \<longrightarrow> cf_of f' (u,v') = cf_of f (u,v'));
      return (f',l,Q)
    } else return (f,l,Q)
  }) (f\<^sub>0,l,Q);

  if excess f u \<noteq> 0 then do {
    (l,Q) \<leftarrow> fifo_gap_relabel f l Q u;
    return (f,l,Q)
  } else do {
    return (f,l,Q)
  }
}"
  
  
text \<open>
  We will show that the discharge operation maintains the invariant that the queue
  is disjoint and contains exactly the active nodes:
\<close>  
definition "Q_invar f Q \<equiv> distinct Q \<and> set Q = { v\<in>V-{s,t}. excess f v \<noteq> 0 }"  
  
text \<open>Inside the loop of the discharge operation, we will use the following 
  version of the invariant:\<close>  
definition "QD_invar u f Q \<equiv> u\<in>V-{s,t} \<and> distinct Q \<and> set Q = { v\<in>V-{s,t,u}. excess f v \<noteq> 0 }"  

  
lemma Q_invar_when_discharged1: "\<lbrakk>QD_invar u f Q; excess f u = 0\<rbrakk> \<Longrightarrow> Q_invar f Q"  
  unfolding Q_invar_def QD_invar_def by auto

lemma Q_invar_when_discharged2: "\<lbrakk>QD_invar u f Q; excess f u \<noteq> 0\<rbrakk> \<Longrightarrow> Q_invar f (Q@[u])"  
  unfolding Q_invar_def QD_invar_def 
  by auto  
  
lemma (in Labeling) push_no_activate_pres_QD_invar:
  fixes v
  assumes INV: "QD_invar u f Q"
  assumes PRE: "push_precond f l (u,v)"
  assumes VC: "s=v \<or> t=v \<or> excess f v \<noteq> 0"  
  shows "QD_invar u (push_effect f (u,v)) Q"
proof -
  interpret push_effect_locale c s t f l u v 
    using PRE by unfold_locales
  
  from excess_non_negative \<Delta>_positive have "excess f v + \<Delta> \<noteq> 0" if "v\<notin>{s,t}"
    using that by force
  thus ?thesis    
    using VC INV
    unfolding QD_invar_def
    by (auto simp: excess'_if split!: if_splits)  
qed      

lemma (in Labeling) push_activate_pres_QD_invar:  
  fixes v
  assumes INV: "QD_invar u f Q"
  assumes PRE: "push_precond f l (u,v)"
  assumes VC: "s\<noteq>v" "t\<noteq>v" and [simp]: "excess f v = 0"  
  shows "QD_invar u (push_effect f (u,v)) (Q@[v])"
proof -
  interpret push_effect_locale c s t f l u v 
    using PRE by unfold_locales
  
  show ?thesis    
    using VC INV \<Delta>_positive
    unfolding QD_invar_def
    by (auto simp: excess'_if split!: if_splits)  
qed      
  
text \<open>Main theorem for the discharge operation:
  It maintains a height bounded labeling, the invariant for the FIFO queue,
  and only performs valid steps due to the generic push-relabel algorithm with
  gap-heuristics.
\<close>  
theorem fifo_discharge_correct[THEN order_trans, refine_vcg]:
  assumes DINV: "Height_Bounded_Labeling c s t f l"
  assumes QINV: "Q_invar f Q" and QNE: "Q\<noteq>[]"
  shows "fifo_discharge f l Q \<le> SPEC (\<lambda>(f',l',Q'). 
      Height_Bounded_Labeling c s t f' l' 
    \<and> Q_invar f' Q' 
    \<and> ((f',l'),(f,l))\<in>gap_algo_rel\<^sup>+
  )"  
proof -
  from QNE obtain u Qr where [simp]: "Q=u#Qr" by (cases Q) auto
  
  from QINV have U: "u\<in>V-{s,t}" "QD_invar u f Qr" and XU_orig: "excess f u \<noteq> 0"
    by (auto simp: Q_invar_def QD_invar_def)    

  have [simp, intro!]: "finite {v. (u, v) \<in> cfE_of f}" 
    apply (rule finite_subset[where B=V])
    using cfE_of_ss_VxV  
    by auto  
      
  show ?thesis
    using U
    unfolding fifo_discharge_def fifo_push_def fifo_gap_relabel_def
    apply (simp only: split nres_monad_laws)  
    apply (rewrite in "FOREACHc _ _ \<hole> _" vcg_intro_frame)  
    apply (rewrite in "if excess _ _ \<noteq> 0 then \<hole> else _" vcg_intro_frame)  
    apply (refine_vcg FOREACHc_rule[where 
            I="\<lambda>it (f',l',Q'). 
                Height_Bounded_Labeling c s t f' l' 
              \<and> QD_invar u f' Q'
              \<and> ((f',l'),(f,l))\<in>gap_algo_rel\<^sup>*
              \<and> it \<subseteq> {v. (u,v) \<in> cfE_of f' }
              \<and> (excess f' u\<noteq>0 \<longrightarrow> (\<forall>v\<in>{v. (u,v) \<in> cfE_of f' }-it. l' u \<noteq> l' v + 1)
            )
            "
          ])
    apply (vc_solve simp: DINV QINV it_step_insert_iff split del: if_split)
    subgoal for v it f' l' Q' proof -
      assume HBL: "Height_Bounded_Labeling c s t f' l'"
      then interpret l': Height_Bounded_Labeling c s t f' l' .  
      
      assume X: "excess f' u \<noteq> 0" and UI: "u \<in> V" "u \<noteq> s" "u \<noteq> t" 
        and QDI: "QD_invar u f' Q'"  
          
      assume "v \<in> it" and ITSS: "it \<subseteq> {v. (u, v) \<in> l'.cf.E}"
      hence UVE: "(u,v) \<in> l'.cf.E" by auto 
      
      assume REL: "((f', l'), f, l) \<in> gap_algo_rel\<^sup>*"    
          
      assume SAT_EDGES: "\<forall>v\<in>{v. (u, v) \<in> cfE_of f'} - it. l' u \<noteq> Suc (l' v)"  
        
      from X UI l'.excess_non_negative have X': "excess f' u > 0" by force   
          
      have PP: "push_precond f' l' (u, v)" if "l' u = l' v + 1"
        unfolding push_precond_def using that UVE X' by auto
        
      show ?thesis
        apply (rule vcg_rem_frame)
        apply (rewrite in "if _ then (assert _ \<then> \<hole>) else _" vcg_intro_frame)  
        apply refine_vcg  
        apply (vc_solve simp: REL solve: PP l'.push_pres_height_bound HBL QDI split del: if_split)
        subgoal proof - 
          assume [simp]: "l' u = Suc (l' v)" 
          assume PRE: "push_precond f' l' (u, v)"
          then interpret pe: push_effect_locale c s t f' l' u v by unfold_locales
          
          have UVNE': "l'.cf (u, v) \<noteq> 0"    
            using l'.resE_positive by fastforce
            
          show ?thesis
            apply (rule vcg_rem_frame)
            apply refine_vcg  
            apply (vc_solve simp: l'.push_pres_height_bound[OF PRE])
            subgoal by unfold_locales  
            subgoal by (auto simp: pe.cf'_alt augment_edge_cf_def)
            subgoal 
              using l'.push_activate_pres_QD_invar[OF QDI PRE] 
              using l'.push_no_activate_pres_QD_invar[OF QDI PRE]
              by auto
            subgoal
              by (meson gap_algo_rel.push REL PRE converse_rtrancl_into_rtrancl HBL)
            subgoal for x proof -
              assume "x\<in>it" "x\<noteq>v"
              with ITSS have "(u,x)\<in>l'.cf.E" by auto    
              thus ?thesis
                using \<open>x\<noteq>v\<close>
                unfolding pe.f'_alt 
                apply (simp add: augment_edge_cf')
                unfolding Graph.E_def  
                by (auto)
            qed
            subgoal for v' proof -
              assume "excess f' u \<noteq> pe.\<Delta>"
              hence PED: "pe.\<Delta> = l'.cf (u,v)"
                unfolding pe.\<Delta>_def by auto
              hence E'SS: "pe.l'.cf.E \<subseteq> (l'.cf.E \<union> {(v,u)}) - {(u,v)}"
                unfolding pe.f'_alt 
                apply (simp add: augment_edge_cf')
                unfolding Graph.E_def  
                by auto 
                  
              assume "v' \<in> it \<longrightarrow> v' = v" and UV'E: "(u, v') \<in> pe.l'.cf.E" and LUSLV': "l' v = l' v'"    
              with E'SS have "v'\<notin>it" by auto
              moreover from UV'E E'SS pe.uv_not_eq(2) have "(u,v')\<in>l'.cf.E" by auto  
              ultimately have "l' u \<noteq> Suc (l' v')" using SAT_EDGES by auto    
              with LUSLV' show False by simp  
            qed      
            done
        qed      
        subgoal using ITSS by auto
        subgoal using SAT_EDGES by auto
        done
    qed
    subgoal premises prems for f' l' Q' proof -
      from prems interpret l': Height_Bounded_Labeling c s t f' l' by simp
      from prems have UI: "u\<in>V" "u\<noteq>s" "u\<noteq>t" 
        and X: "excess f' u \<noteq> 0" 
        and QDI: "QD_invar u f' Q'"
        and REL: "((f', l'), f, l) \<in> gap_algo_rel\<^sup>*"
        and NO_ADM: "\<forall>v. (u, v) \<in> l'.cf.E \<longrightarrow> l' u \<noteq> Suc (l' v)"
        by simp_all
        
      from X have X': "excess f' u > 0" using l'.excess_non_negative UI by force    
          
      from X' UI NO_ADM have PRE: "relabel_precond f' l' u" 
        unfolding relabel_precond_def by auto
          
      from l'.height_bound \<open>u\<in>V\<close> card_V_ge2 have [simp]: "l' u < 2*card V" by auto
          
      from l'.relabel_pres_height_bound[OF PRE] 
      interpret l'': Height_Bounded_Labeling c s t f' "relabel_effect f' l' u" .
          
      from l''.height_bound \<open>u\<in>V\<close> card_V_ge2 have [simp]: "relabel_effect f' l' u u < 2*card V" by auto
          
      show ?thesis 
        apply (rule vcg_rem_frame)
        apply refine_vcg
        apply (vc_solve 
            simp: UI PRE 
            simp: l'.gap_relabel_pres_hb_labeling[OF PRE] 
            simp: Q_invar_when_discharged2[OF QDI X])
        subgoal by unfold_locales    
        subgoal
          by (meson PRE REL gap_algo_rel.relabel l'.Height_Bounded_Labeling_axioms rtrancl_into_trancl2)
        done  
    qed      
    subgoal by (auto simp: Q_invar_when_discharged1 Q_invar_when_discharged2)
    subgoal using XU_orig by (metis Pair_inject rtranclD)    
    subgoal by (auto simp: Q_invar_when_discharged1)
    subgoal using XU_orig by (metis Pair_inject rtranclD)    
    done    
qed
    
end \<comment> \<open>Network\<close> 
  
subsection \<open>Main Algorithm\<close>
  
context Network 
begin
  
text \<open>The main algorithm initializes the flow, labeling, and the queue, 
  and then applies the discharge operation until the queue is empty:
\<close>
  
definition "fifo_push_relabel \<equiv> do {
  let f = pp_init_f;
  let l = pp_init_l;

  Q \<leftarrow> spec l. distinct l \<and> set l = {v\<in>V - {s,t}. excess f v \<noteq> 0}; \<comment> \<open>TODO: This is exactly \<open>E``{s} - {t}\<close>!\<close>

  (f,l,_) \<leftarrow> while\<^sub>T (\<lambda>(f,l,Q). Q \<noteq> []) (\<lambda>(f,l,Q). do {
    fifo_discharge f l Q
  }) (f,l,Q);

  assert (Height_Bounded_Labeling c s t f l);
  return f
}"
  
text \<open>Having proved correctness of the discharge operation, the correctness 
  theorem of the main algorithm is straightforward: 
  As the discharge operation implements the generic algorithm, the loop
  will terminate after finitely many steps.
  Upon termination, the queue that contains exactly the active nodes is empty.
  Thus, all nodes are inactive, and the resulting preflow is actually a maximal 
  flow. 
\<close>  
theorem fifo_push_relabel_correct: 
  "fifo_push_relabel \<le> SPEC isMaxFlow"
  unfolding fifo_push_relabel_def
  apply (refine_vcg  
      WHILET_rule[where 
            I="\<lambda>(f,l,Q). Height_Bounded_Labeling c s t f l \<and> Q_invar f Q"
        and R="inv_image (gap_algo_rel\<^sup>+) (\<lambda>(f,l,Q). ((f,l)))"
        ]
      )
  apply (vc_solve solve: pp_init_height_bound)
  subgoal by (blast intro: wf_lex_prod wf_trancl)  
  subgoal unfolding Q_invar_def by auto 
  subgoal for initQ f l proof -
    assume "Height_Bounded_Labeling c s t f l"
    then interpret Height_Bounded_Labeling c s t f l .
    assume "Q_invar f []"    
    hence "\<forall>u\<in>V-{s,t}. excess f u = 0" unfolding Q_invar_def by auto
    thus "isMaxFlow f" by (rule no_excess_imp_maxflow)    
  qed
  done
  
end \<comment> \<open>Network\<close> 
    
end
