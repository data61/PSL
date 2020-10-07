section \<open>Implementation of the FIFO Push/Relabel Algorithm\<close>
theory Fifo_Push_Relabel_Impl
imports 
  Fifo_Push_Relabel
  Prpu_Common_Impl
begin

subsection \<open>Basic Operations\<close>
context Network_Impl 
begin  


subsubsection \<open>Queue\<close>    
text \<open>Obtain the empty queue.\<close>  
definition q_empty :: "node list nres" where
  "q_empty \<equiv> return []"

text \<open>Check whether a queue is empty.\<close>  
definition q_is_empty :: "node list \<Rightarrow> bool nres" where
  "q_is_empty Q \<equiv> return ( Q = [] )"
  
text \<open>Enqueue a node.\<close>  
definition q_enqueue :: "node \<Rightarrow> node list \<Rightarrow> node list nres" where
  "q_enqueue v Q \<equiv> do {
    assert (v\<in>V);
    return (Q@[v])
  }"

text \<open>Dequeue a node.\<close>  
definition q_dequeue :: "node list \<Rightarrow> (node \<times> node list) nres" where
  "q_dequeue Q \<equiv> do {
    assert (Q\<noteq>[]);
    return (hd Q, tl Q)
  }"

end \<comment> \<open>Network Implementation Locale\<close>  
  
subsection \<open>Refinements to Basic Operations\<close>  
  
context Network_Impl 
begin  
text \<open>In this section, we refine the algorithm to actually use the 
 basic operations.
\<close>
  
  

subsubsection \<open>Refinement of Push\<close>  
definition "fifo_push2_aux x cf Q \<equiv> \<lambda>(u,v). do {
  assert ( (u,v) \<in> E \<union> E\<inverse> );
  assert ( u \<noteq> v );
  let \<Delta> = min (x u) (cf (u,v));
  let Q = (if v\<noteq>s \<and> v\<noteq>t \<and> x v = 0 then Q@[v] else Q);
  return ((x( u := x u - \<Delta>, v := x v + \<Delta> ),augment_edge_cf cf (u,v) \<Delta>),Q)
}"
    
  
lemma fifo_push2_aux_refine: 
  "\<lbrakk>((x,cf),f)\<in>xf_rel; (ei,e)\<in>Id\<times>\<^sub>rId; (Qi,Q)\<in>Id\<rbrakk> 
    \<Longrightarrow> fifo_push2_aux x cf Qi ei \<le> \<Down>(xf_rel \<times>\<^sub>r Id) (fifo_push f l Q e)"
  unfolding fifo_push_def fifo_push2_aux_def
  apply refine_vcg  
  apply (vc_solve simp: xf_rel_def no_self_loop)
  subgoal for u v 
    unfolding push_precond_def using cfE_of_ss_invE by auto
  subgoal for u v 
  proof -
    assume [simp]: "Labeling c s t f l"
    then interpret Labeling c s t f l .
    assume "push_precond f l (u, v)"    
    then interpret l': push_effect_locale c s t f l u v by unfold_locales
    show ?thesis 
      apply (safe intro!: ext)
      using l'.excess'_if l'.\<Delta>_def l'.cf'_alt l'.uv_not_eq(1)
      by (auto)  
  qed
  done  

definition "fifo_push2 x cf Q \<equiv> \<lambda>(u,v). do {
  assert ( (u,v) \<in> E \<union> E\<inverse> );
  xu \<leftarrow> x_get x u;
  xv \<leftarrow> x_get x v;
  cfuv \<leftarrow> cf_get cf (u,v);
  cfvu \<leftarrow> cf_get cf (v,u);
  let \<Delta> = min xu cfuv;
  x \<leftarrow> x_add x u (-\<Delta>);
  x \<leftarrow> x_add x v \<Delta>;

  cf \<leftarrow> cf_set cf (u,v) (cfuv - \<Delta>);
  cf \<leftarrow> cf_set cf (v,u) (cfvu + \<Delta>);

  if v\<noteq>s \<and> v\<noteq>t \<and> xv = 0 then do {
    Q \<leftarrow> q_enqueue v Q;
    return ((x,cf),Q)
  } else
    return ((x,cf),Q)
}"
    
lemma fifo_push2_refine[refine]: 
  assumes "((x,cf),f)\<in>xf_rel" "(ei,e)\<in>Id\<times>\<^sub>rId" "(Qi,Q)\<in>Id"
  shows "fifo_push2 x cf Qi ei \<le> \<Down>(xf_rel \<times>\<^sub>r Id) (fifo_push f l Q e)"
proof -
  have "fifo_push2 x cf Qi ei \<le> (fifo_push2_aux x cf Qi ei)"  
    unfolding fifo_push2_def fifo_push2_aux_def
    unfolding x_get_def x_add_def cf_get_def cf_set_def q_enqueue_def
    unfolding augment_edge_cf_def  
    apply (simp only: nres_monad_laws)  
    apply refine_vcg  
    using E_ss_VxV  
    by auto  
  also note fifo_push2_aux_refine[OF assms]    
  finally show ?thesis . 
qed  
  
subsubsection \<open>Refinement of Gap-Relabel\<close>    
  
    
definition "fifo_gap_relabel_aux C f l Q u \<equiv> do {
  Q \<leftarrow> q_enqueue u Q;
  lu \<leftarrow> l_get l u;
  l \<leftarrow> relabel f l u;
  if gap_precond l lu then do {
    l \<leftarrow> gap_aux C l lu;
    return (l,Q)
  } else return (l,Q)
}"  

lemma fifo_gap_relabel_aux_refine: 
  assumes [simp]: "C = card V" "l_invar l"
  shows "fifo_gap_relabel_aux C f l Q u \<le> fifo_gap_relabel f l Q u"  
  unfolding fifo_gap_relabel_aux_def fifo_gap_relabel_def relabel_def 
    gap_relabel_effect_def l_get_def q_enqueue_def
  apply (simp only: Let_def nres_monad_laws)  
  apply refine_vcg  
  by auto  
  
  
  
    
definition "fifo_gap_relabel2 C am cf clc Q u \<equiv> do {
  Q \<leftarrow> q_enqueue u Q;
  lu \<leftarrow> clc_get clc u;
  clc \<leftarrow> clc_relabel2 am cf clc u;
  has_gap \<leftarrow> clc_has_gap clc lu;
  if has_gap then do {
    clc \<leftarrow> gap2 C clc lu;
    RETURN (clc,Q)
  } else 
    RETURN (clc,Q)
}"  
  
lemma fifo_gap_relabel2_refine_aux:
  assumes XCF: "((x, cf), f) \<in> xf_rel"  
  assumes CLC: "(clc,l)\<in>clc_rel"  
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(Ci,C)\<in>Id" "(Qi,Q)\<in>Id" "(ui,u)\<in>Id"
  shows "fifo_gap_relabel2 Ci am cf clc Qi ui 
          \<le> \<Down>(clc_rel \<times>\<^sub>r Id) (fifo_gap_relabel_aux C f l Q u)"  
  unfolding fifo_gap_relabel2_def fifo_gap_relabel_aux_def
  apply (refine_vcg XCF AM CLC if_bind_cond_refine bind_refine')
  apply refine_dref_type  
  apply (vc_solve solve: refl )
  subgoal for _ lu
    using CLC
    unfolding clc_get_def l_get_def clc_rel_def in_br_conv clc_invar_def
    by (auto simp: refine_pw_simps split: prod.splits)
  done    
    
lemma fifo_gap_relabel2_refine[refine]:
  assumes XCF: "((x, cf), f) \<in> xf_rel"  
  assumes CLC: "(clc,l)\<in>clc_rel"  
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(Qi,Q)\<in>Id" "(ui,u)\<in>Id"    
  assumes CC: "C = card V"  
  shows "fifo_gap_relabel2 C am cf clc Qi ui 
          \<le>\<Down>(clc_rel \<times>\<^sub>r Id) (fifo_gap_relabel f l Q u)"
proof -
  from CLC have LINV: "l_invar l" 
    unfolding clc_rel_def in_br_conv clc_invar_def by auto
  
  note fifo_gap_relabel2_refine_aux[OF XCF CLC AM IdI IdI IdI]
  also note fifo_gap_relabel_aux_refine[OF CC LINV]  
  finally show ?thesis by simp  
qed    
  
subsubsection \<open>Refinement of Discharge\<close>
context begin  
text \<open>
  Some lengthy, multi-step refinement of discharge, 
  changing the iteration to iteration over adjacent nodes with filter,
  and showing that we can do the filter wrt.\ the current state, rather than 
  the original state before the loop. 
\<close>  
  
lemma am_nodes_as_filter:
  assumes "is_adj_map am"
  shows "{v . (u,v)\<in>cfE_of f} = set (filter (\<lambda>v. cf_of f (u,v) \<noteq> 0) (am u))"
  using assms cfE_of_ss_invE 
  unfolding is_adj_map_def Graph.E_def
  by fastforce 
      
private lemma adjacent_nodes_iterate_refine1:   
  fixes ff u f
  assumes AMR: "(am,adjacent_nodes)\<in>Id \<rightarrow> \<langle>Id\<rangle>list_set_rel"
  assumes CR: "\<And>s si. (si,s)\<in>Id \<Longrightarrow> cci si \<longleftrightarrow> cc s"  
  assumes FR: "\<And>v vi s si. \<lbrakk>(vi,v)\<in>Id; v\<in>V; (u,v)\<in>E\<union>E\<inverse>; (si,s)\<in>Id\<rbrakk> \<Longrightarrow> 
    ffi vi si \<le> \<Down>Id (do {
                      if (cf_of f (u,v) \<noteq> 0) then ff v s else RETURN s
                    })" (is "\<And>v vi s si. \<lbrakk>_;_;_;_\<rbrakk> \<Longrightarrow> _  \<le> \<Down>_ (?ff' v s)")
  assumes S0R: "(s0i,s0)\<in>Id"
  assumes UR: "(ui,u)\<in>Id"  
  shows "nfoldli (am ui) cci ffi s0i 
        \<le>\<Down>Id (FOREACHc {v . (u,v)\<in>cfE_of f} cc ff s0)"
proof -
  from fun_relD[OF AMR] have AM: "is_adj_map am"
    unfolding is_adj_map_def
    by (auto simp: list_set_rel_def in_br_conv adjacent_nodes_def)  
  
  from AM have AM_SS_V: "set (am u) \<subseteq> V" "{u}\<times>set (am u) \<subseteq> E \<union> E\<inverse>"
    unfolding is_adj_map_def using E_ss_VxV by auto
      
  thm nfoldli_refine    
  have "nfoldli (am ui) cci ffi s0 \<le> \<Down>Id (nfoldli (am ui) cc ?ff' s0)"    
    apply (refine_vcg FR) 
    apply (rule list_rel_congD)  
    apply refine_dref_type 
    using CR  
    apply vc_solve
    using AM_SS_V UR by auto  
  also have "nfoldli (am ui) cc ?ff' s0 
            \<le>\<Down>Id (FOREACHc (adjacent_nodes u) cc ?ff' s0)"    
    by (rule LFOc_refine[OF fun_relD[OF AMR UR]]; simp)
  also have "FOREACHc (adjacent_nodes u) cc ?ff' s0 
            \<le> FOREACHc {v . (u,v)\<in>cfE_of f} cc ff s0"
    apply (subst am_nodes_as_filter[OF AM])  
    apply (subst FOREACHc_filter_deforestation2)  
    subgoal using AM unfolding is_adj_map_def by auto
    subgoal 
      apply (rule eq_refl) 
      apply ((fo_rule cong)+; (rule refl)?)
      subgoal 
        using fun_relD[OF AMR IdI[of u]] 
        by (auto simp: list_set_rel_def in_br_conv) 
      done    
    done
  finally show ?thesis using S0R by simp
qed    
    
private definition "dis_loop_aux am f\<^sub>0 l Q u \<equiv> do {
  assert (u\<in>V - {s,t});
  assert (distinct (am u));
  nfoldli (am u) (\<lambda>(f,l,Q). excess f u \<noteq> 0) (\<lambda>v (f,l,Q). do {
    assert ((u,v)\<in>E\<union>E\<inverse> \<and> v\<in>V);
    if (cf_of f\<^sub>0 (u,v) \<noteq> 0) then do {
      if (l u = l v + 1) then do {
        (f',Q) \<leftarrow> fifo_push f l Q (u,v);
        assert (\<forall>v'. v'\<noteq>v \<longrightarrow> cf_of f' (u,v') = cf_of f (u,v'));
        return (f',l,Q)
      } else return (f,l,Q)
    } else return (f,l,Q)
  }) (f\<^sub>0,l,Q)
}"
    
private definition "fifo_discharge_aux am f\<^sub>0 l Q \<equiv> do {  
  (u,Q) \<leftarrow> q_dequeue Q;
  assert (u\<in>V \<and> u\<noteq>s \<and> u\<noteq>t);

  (f,l,Q) \<leftarrow> dis_loop_aux am f\<^sub>0 l Q u;

  if excess f u \<noteq> 0 then do {
    (l,Q) \<leftarrow> fifo_gap_relabel f l Q u;
    return (f,l,Q)
  } else do {
    return (f,l,Q)
  }
}"
    
private lemma fifo_discharge_aux_refine:  
  assumes AM: "(am,adjacent_nodes)\<in>Id \<rightarrow> \<langle>Id\<rangle>list_set_rel"
  assumes [simplified,simp]: "(fi,f)\<in>Id" "(li,l)\<in>Id" "(Qi,Q)\<in>Id"
  shows "fifo_discharge_aux am fi li Qi \<le> \<Down>Id (fifo_discharge f l Q)"
  unfolding fifo_discharge_aux_def fifo_discharge_def dis_loop_aux_def 
  unfolding q_dequeue_def  
  apply (simp only: nres_monad_laws)  
  apply (refine_rcg adjacent_nodes_iterate_refine1[OF AM])  
  apply refine_dref_type
  apply vc_solve  
  subgoal 
    using fun_relD[OF AM IdI[of "hd Q"]]  
    unfolding list_set_rel_def by (auto simp: in_br_conv)
  done  
    
private definition "dis_loop_aux2 am f\<^sub>0 l Q u \<equiv> do {
  assert (u\<in>V - {s,t});
  assert (distinct (am u));
  nfoldli (am u) (\<lambda>(f,l,Q). excess f u \<noteq> 0) (\<lambda>v (f,l,Q). do {
    assert ((u,v)\<in>E\<union>E\<inverse> \<and> v\<in>V);
    if (cf_of f (u,v) \<noteq> 0) then do {
      if (l u = l v + 1) then do {
        (f',Q) \<leftarrow> fifo_push f l Q (u,v);
        assert (\<forall>v'. v'\<noteq>v \<longrightarrow> cf_of f' (u,v') = cf_of f (u,v'));
        return (f',l,Q)
      } else return (f,l,Q)
    } else return (f,l,Q)
  }) (f\<^sub>0,l,Q)
}"
    
private lemma dis_loop_aux2_refine:
  shows "dis_loop_aux2 am f\<^sub>0 l Q u \<le>\<Down>Id (dis_loop_aux am f\<^sub>0 l Q u)"  
  unfolding dis_loop_aux2_def dis_loop_aux_def
  apply (intro ASSERT_refine_right ASSERT_refine_left; assumption?)  
  apply (rule nfoldli_invar_refine[where 
            I="\<lambda>it1 it2 (f,_,_). \<forall>v\<in>set it2. cf_of f (u,v) = cf_of f\<^sub>0 (u,v)"])
  apply refine_dref_type  
  apply vc_solve
  apply (auto simp: pw_leof_iff refine_pw_simps fifo_push_def; metis) 
  done  
    
private definition "dis_loop_aux3 am x cf l Q u \<equiv> do {
  assert (u\<in>V \<and> distinct (am u));
  monadic_nfoldli (am u) 
    (\<lambda>((x,cf),l,Q). do { xu \<leftarrow> x_get x u; return (xu \<noteq> 0) }) 
    (\<lambda>v ((x,cf),l,Q). do {
      cfuv \<leftarrow> cf_get cf (u,v);
      if (cfuv \<noteq> 0) then do {
        lu \<leftarrow> l_get l u;
        lv \<leftarrow> l_get l v;
        if (lu = lv + 1) then do {
          ((x,cf),Q) \<leftarrow> fifo_push2 x cf Q (u,v);
          return ((x,cf),l,Q)
        } else return ((x,cf),l,Q)
      } else return ((x,cf),l,Q)
  }) ((x,cf),l,Q)
}"
    
private lemma dis_loop_aux3_refine:
  assumes [simplified,simp]: "(ami,am)\<in>Id" "(li,l)\<in>Id" "(Qi,Q)\<in>Id" "(ui,u)\<in>Id"
  assumes XF: "((x,cf),f)\<in>xf_rel"
  shows "dis_loop_aux3 ami x cf li Qi ui 
        \<le>\<Down>(xf_rel \<times>\<^sub>r Id \<times>\<^sub>r Id) (dis_loop_aux2 am f l Q u)"  
  unfolding dis_loop_aux3_def dis_loop_aux2_def
  unfolding x_get_def cf_get_def l_get_def  
  apply (simp only: nres_monad_laws nfoldli_to_monadic)  
  apply (refine_rcg)
  apply refine_dref_type  
  using XF  
  by (vc_solve simp: xf_rel_def in_br_conv)
    
definition "dis_loop2 am x cf clc Q u \<equiv> do {
  assert (distinct (am u));
  amu \<leftarrow> am_get am u;
  monadic_nfoldli amu
    (\<lambda>((x,cf),clc,Q). do { xu \<leftarrow> x_get x u; return (xu \<noteq> 0) }) 
    (\<lambda>v ((x,cf),clc,Q). do {
      cfuv \<leftarrow> cf_get cf (u,v);
      if (cfuv \<noteq> 0) then do {
        lu \<leftarrow> clc_get clc u;
        lv \<leftarrow> clc_get clc v;
        if (lu = lv + 1) then do {
          ((x,cf),Q) \<leftarrow> fifo_push2 x cf Q (u,v);
          return ((x,cf),clc,Q)
        } else return ((x,cf),clc,Q)
      } else return ((x,cf),clc,Q)
  }) ((x,cf),clc,Q)
}"
    
private lemma dis_loop2_refine_aux:
  assumes [simplified,simp]: "(xi,x)\<in>Id" "(cfi,cf)\<in>Id" "(ami,am)\<in>Id" 
  assumes [simplified,simp]: "(li,l)\<in>Id" "(Qi,Q)\<in>Id" "(ui,u)\<in>Id"
  assumes CLC: "(clc,l)\<in>clc_rel"
  shows "dis_loop2 ami xi cfi clc Qi ui 
        \<le>\<Down>(Id \<times>\<^sub>r clc_rel \<times>\<^sub>r Id) (dis_loop_aux3 am x cf l Q u)"  
  unfolding dis_loop2_def dis_loop_aux3_def am_get_def
  apply (simp only: nres_monad_laws)  
  apply refine_rcg  
  apply refine_dref_type  
  apply (vc_solve simp: CLC)
  done
    
lemma dis_loop2_refine[refine]:
  assumes XF: "((x,cf),f)\<in>xf_rel"
  assumes CLC: "(clc,l)\<in>clc_rel"
  assumes [simplified,simp]: "(ami,am)\<in>Id" "(Qi,Q)\<in>Id" "(ui,u)\<in>Id"
  shows "dis_loop2 ami x cf clc Qi ui 
        \<le>\<Down>(xf_rel \<times>\<^sub>r clc_rel \<times>\<^sub>r Id) (dis_loop_aux am f l Q u)"
proof -      
  have [simp]: 
    "((Id \<times>\<^sub>r clc_rel \<times>\<^sub>r Id) O (xf_rel \<times>\<^sub>r Id)) = xf_rel \<times>\<^sub>r clc_rel \<times>\<^sub>r Id"
    by (auto simp: prod_rel_comp)
  
  note dis_loop2_refine_aux[OF IdI IdI IdI IdI IdI IdI CLC]
  also note dis_loop_aux3_refine[OF IdI IdI IdI IdI XF]
  also note dis_loop_aux2_refine  
  finally show ?thesis 
    by (auto simp: conc_fun_chain monoD[OF conc_fun_mono])
qed    
    
    
definition "fifo_discharge2 C am x cf clc Q \<equiv> do {  
  (u,Q) \<leftarrow> q_dequeue Q;
  assert (u\<in>V \<and> u\<noteq>s \<and> u\<noteq>t);

  ((x,cf),clc,Q) \<leftarrow> dis_loop2 am x cf clc Q u;

  xu \<leftarrow> x_get x u;
  if xu \<noteq> 0 then do {
    (clc,Q) \<leftarrow> fifo_gap_relabel2 C am cf clc Q u;
    return ((x,cf),clc,Q)
  } else do {
    return ((x,cf),clc,Q)
  }
}"
    
lemma fifo_discharge2_refine[refine]:
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes XCF: "((x, cf), f) \<in> xf_rel"  
  assumes CLC: "(clc,l)\<in>clc_rel"  
  assumes [simplified,simp]: "(Qi,Q)\<in>Id"  
  assumes CC: "C = card V"  
  shows "fifo_discharge2 C am x cf clc Qi 
        \<le>\<Down>(xf_rel \<times>\<^sub>r clc_rel \<times>\<^sub>r Id) (fifo_discharge f l Q)"
proof -
  have "fifo_discharge2 C am x cf clc Q 
        \<le>\<Down>(xf_rel \<times>\<^sub>r clc_rel \<times>\<^sub>r Id) (fifo_discharge_aux am f l Q)"
    unfolding fifo_discharge2_def fifo_discharge_aux_def  
    unfolding x_get_def  
    apply (simp only: nres_monad_laws)  
    apply (refine_rcg XCF CLC AM IdI)
    apply (vc_solve simp: CC) 
    subgoal unfolding xf_rel_def in_br_conv by auto  
    applyS assumption  
    done  
  also note fifo_discharge_aux_refine[OF AM IdI IdI IdI]
  finally show ?thesis by simp  
qed    
  
end \<comment> \<open>Anonymous Context\<close>    

  
subsubsection \<open>Computing the Initial Queue\<close>  
definition "q_init am \<equiv> do {
  Q \<leftarrow> q_empty;
  ams \<leftarrow> am_get am s;
  nfoldli ams (\<lambda>_. True) (\<lambda>v Q. do {
    if v\<noteq>t then q_enqueue v Q else return Q
  }) Q
}"

lemma q_init_correct[THEN order_trans, refine_vcg]: 
  assumes AM: "is_adj_map am"  
  shows "q_init am 
    \<le> (spec l. distinct l \<and> set l = {v \<in> V - {s, t}. excess pp_init_f v \<noteq> 0})"  
proof -    
  from am_to_adj_nodes_refine[OF AM] have "set (am s) \<subseteq> V"
    using adjacent_nodes_ss_V
    by (auto simp: list_set_rel_def in_br_conv)
  hence "q_init am \<le> RETURN (filter ((\<noteq>) t) (am s))"
    unfolding q_init_def q_empty_def q_enqueue_def am_get_def
    apply (refine_vcg nfoldli_rule[where I="\<lambda>l1 _ l. l = filter ((\<noteq>) t) l1"])  
    by auto  
  also have "\<dots> 
    \<le> (spec l. distinct l \<and> set l = {v \<in> V - {s, t}. excess pp_init_f v \<noteq> 0})"    
  proof -    
    from am_to_adj_nodes_refine[OF AM] 
    have [simp]: "distinct (am s)" "set (am s) = adjacent_nodes s" 
      unfolding list_set_rel_def
      by (auto simp: in_br_conv)
    
    show ?thesis
      using E_ss_VxV
      apply (auto simp: pp_init_x_def adjacent_nodes_def)
      unfolding Graph.E_def by auto      
  qed
  finally show ?thesis .
qed    

subsubsection \<open>Refining the Main Algorithm\<close>  
definition "fifo_push_relabel_aux am \<equiv> do {
  cardV \<leftarrow> init_C am;
  assert (cardV = card V);
  let f = pp_init_f;
  l \<leftarrow> l_init cardV;

  Q \<leftarrow> q_init am;

  (f,l,_) \<leftarrow> monadic_WHILEIT (\<lambda>_. True) 
    (\<lambda>(f,l,Q). do {qe \<leftarrow> q_is_empty Q; return (\<not>qe)}) 
    (\<lambda>(f,l,Q). do {
      fifo_discharge f l Q
    }) 
    (f,l,Q);

  assert (Height_Bounded_Labeling c s t f l);
  return f
}"
  
lemma fifo_push_relabel_aux_refine:
  assumes AM: "is_adj_map am"  
  shows "fifo_push_relabel_aux am \<le> \<Down>Id (fifo_push_relabel)"
  unfolding fifo_push_relabel_aux_def fifo_push_relabel_def
  unfolding l_init_def pp_init_l_def q_is_empty_def bind_to_let_conv
  apply (rule specify_left[OF init_C_correct[OF AM]])
  apply (refine_rcg q_init_correct[OF AM])
  apply refine_dref_type  
  apply vc_solve
  done    
    
  
definition "fifo_push_relabel2 am \<equiv> do {
  cardV \<leftarrow> init_C am;
  (x,cf) \<leftarrow> pp_init_xcf2 am;
  clc \<leftarrow> clc_init cardV;
  Q \<leftarrow> q_init am;

  ((x,cf),clc,Q) \<leftarrow> monadic_WHILEIT (\<lambda>_. True) 
    (\<lambda>((x,cf),clc,Q). do {qe \<leftarrow> q_is_empty Q; return (\<not>qe)}) 
    (\<lambda>((x,cf),clc,Q). do {
      fifo_discharge2 cardV am x cf clc Q
    }) 
    ((x,cf),clc,Q);

  return cf
}"

lemma fifo_push_relabel2_refine:
  assumes AM: "is_adj_map am"
  shows "fifo_push_relabel2 am 
        \<le> \<Down>(br (flow_of_cf) (RPreGraph c s t)) fifo_push_relabel"
proof -
  {
    fix f l n
    assume "Height_Bounded_Labeling c s t f l"
    then interpret Height_Bounded_Labeling c s t f l .  
    have G1: "flow_of_cf cf = f" by (rule fo_rg_inv)
    have G2: "RPreGraph c s t cf" by (rule is_RPreGraph)
    note G1 G2    
  } note AUX1=this   
  
  
  have "fifo_push_relabel2 am 
        \<le> \<Down>(br (flow_of_cf) (RPreGraph c s t)) (fifo_push_relabel_aux am)"
    unfolding fifo_push_relabel2_def fifo_push_relabel_aux_def
    apply (refine_rcg)  
    apply (refine_dref_type)      
    apply (vc_solve simp: AM am_to_adj_nodes_refine[OF AM])   
    subgoal using AUX1 by (auto simp: in_br_conv xf_rel_def AM)
    done  
  also note fifo_push_relabel_aux_refine[OF AM]
  finally show ?thesis .  
qed      
  
end \<comment> \<open>Network Impl. Locale\<close>

subsection \<open>Separating out the Initialization of the Adjacency Matrix\<close>  
context Network_Impl
begin
  
text \<open>We split the algorithm into an initialization of the adjacency 
  matrix, and the actual algorithm. This way, the algorithm can handle 
  pre-initialized adjacency matrices.
\<close>  
 
definition "fifo_push_relabel_init2 \<equiv> cf_init"  
definition "pp_init_xcf2' am cf \<equiv> do {
  x \<leftarrow> x_init;

  assert (s\<in>V);
  adj \<leftarrow> am_get am s;
  nfoldli adj (\<lambda>_. True) (\<lambda>v (x,cf). do {
    assert ((s,v)\<in>E);
    assert (s \<noteq> v);
    a \<leftarrow> cf_get cf (s,v);
    x \<leftarrow> x_add x s (-a);
    x \<leftarrow> x_add x v a;
    cf \<leftarrow> cf_set cf (s,v) 0; 
    cf \<leftarrow> cf_set cf (v,s) a; 
    return (x,cf)
  }) (x,cf)
}"
  
definition "fifo_push_relabel_run2 am cf \<equiv> do {
  cardV \<leftarrow> init_C am;
  (x,cf) \<leftarrow> pp_init_xcf2' am cf;
  clc \<leftarrow> clc_init cardV;
  Q \<leftarrow> q_init am;

  ((x,cf),clc,Q) \<leftarrow> monadic_WHILEIT (\<lambda>_. True) 
    (\<lambda>((x,cf),clc,Q). do {qe \<leftarrow> q_is_empty Q; return (\<not>qe)}) 
    (\<lambda>((x,cf),clc,Q). do {
      fifo_discharge2 cardV am x cf clc Q
    }) 
    ((x,cf),clc,Q);

  return cf
}"
  
lemma fifo_push_relabel2_alt:
  "fifo_push_relabel2 am = do {
    cf \<leftarrow> fifo_push_relabel_init2;
    fifo_push_relabel_run2 am cf
  }"  
  unfolding fifo_push_relabel_init2_def fifo_push_relabel_run2_def
    fifo_push_relabel2_def pp_init_xcf2_def pp_init_xcf2'_def
    cf_init_def (* Unfolding this b/c it's a return and thus can be inlined.*)
  by simp
  
  
  
end \<comment> \<open>Network Impl. Locale\<close>
  
  
subsection \<open>Refinement To Efficient Data Structures\<close>  
  
context Network_Impl
begin

subsubsection \<open>Registration of Abstract Operations\<close>  
text \<open>We register all abstract operations at once, 
  auto-rewriting the capacity matrix type\<close>
  
context includes Network_Impl_Sepref_Register 
begin  
  
sepref_register q_empty q_is_empty q_enqueue q_dequeue  
  
sepref_register fifo_push2  
  
sepref_register fifo_gap_relabel2 
  
sepref_register dis_loop2 fifo_discharge2
  
sepref_register q_init pp_init_xcf2'
  
sepref_register fifo_push_relabel_run2 fifo_push_relabel_init2
sepref_register fifo_push_relabel2
  
end \<comment> \<open>Anonymous Context\<close> 
  
  
subsubsection \<open>Queue by Two Stacks\<close>  
definition (in -) "q_\<alpha> \<equiv> \<lambda>(L,R). L@rev R"    
definition (in -) "q_empty_impl \<equiv> ([],[])"
definition (in -) "q_is_empty_impl \<equiv> \<lambda>(L,R). is_Nil L \<and> is_Nil R"
definition (in -) "q_enqueue_impl \<equiv> \<lambda>x (L,R). (L,x#R)"  
definition (in -) "q_dequeue_impl 
  \<equiv> \<lambda>(x#L,R) \<Rightarrow> (x,(L,R)) | ([],R) \<Rightarrow> case rev R of (x#L) \<Rightarrow> (x,(L,[]))"  
    
lemma q_empty_impl_correct[simp]: "q_\<alpha> q_empty_impl = []" 
  by (auto simp: q_\<alpha>_def q_empty_impl_def)
    
lemma q_enqueue_impl_correct[simp]: "q_\<alpha> (q_enqueue_impl x Q) = q_\<alpha> Q @ [x]" 
  by (auto simp: q_\<alpha>_def q_enqueue_impl_def split: prod.split)
  
lemma q_is_empty_impl_correct[simp]: "q_is_empty_impl Q \<longleftrightarrow> q_\<alpha> Q = []" 
  unfolding q_\<alpha>_def q_is_empty_impl_def
  by (cases Q) (auto split: list.splits)

    
lemma q_dequeue_impl_correct_aux: 
  "\<lbrakk>q_\<alpha> Q = x#xs\<rbrakk> \<Longrightarrow> apsnd q_\<alpha> (q_dequeue_impl Q) = (x,xs)"
  unfolding q_\<alpha>_def q_dequeue_impl_def
  by (cases Q) (auto split!: list.split)  

lemma q_dequeue_impl_correct[simp]: 
  assumes "q_dequeue_impl Q = (x,Q')"
  assumes "q_\<alpha> Q \<noteq> []"
  shows "x = hd (q_\<alpha> Q)" and "q_\<alpha> Q' = tl (q_\<alpha> Q)"
  using assms q_dequeue_impl_correct_aux[of Q]
  by - (cases "q_\<alpha> Q"; auto)+
    
definition "q_assn \<equiv> pure (br q_\<alpha> (\<lambda>_. True))"

  
  
lemma q_empty_impl_hnr[sepref_fr_rules]: 
  "(uncurry0 (return q_empty_impl), uncurry0 q_empty) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a q_assn"  
  apply (sepref_to_hoare)
  unfolding q_assn_def q_empty_def pure_def
  by (sep_auto simp: in_br_conv) 
    
lemma q_is_empty_impl_hnr[sepref_fr_rules]: 
  "(return o q_is_empty_impl, q_is_empty) \<in> q_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  apply (sepref_to_hoare)
  unfolding q_assn_def q_is_empty_def pure_def
  by (sep_auto simp: in_br_conv) 
  
lemma q_enqueue_impl_hnr[sepref_fr_rules]: 
  "(uncurry (return oo q_enqueue_impl), uncurry (PR_CONST q_enqueue)) 
    \<in> nat_assn\<^sup>k *\<^sub>a q_assn\<^sup>d \<rightarrow>\<^sub>a q_assn"    
  apply (sepref_to_hoare)
  unfolding q_assn_def q_enqueue_def pure_def
  by (sep_auto simp: in_br_conv refine_pw_simps) 
  
lemma q_dequeue_impl_hnr[sepref_fr_rules]:    
  "(return o q_dequeue_impl, q_dequeue) \<in> q_assn\<^sup>d \<rightarrow>\<^sub>a nat_assn \<times>\<^sub>a q_assn"
  apply (sepref_to_hoare)
  unfolding q_assn_def q_dequeue_def pure_def prod_assn_def
  by (sep_auto simp: in_br_conv refine_pw_simps split: prod.split) 
    
  
subsubsection \<open>Push\<close>   

sepref_thm fifo_push_impl is "uncurry3 (PR_CONST fifo_push2)" 
  :: "x_assn\<^sup>d *\<^sub>a cf_assn\<^sup>d *\<^sub>a q_assn\<^sup>d *\<^sub>a edge_assn\<^sup>k 
      \<rightarrow>\<^sub>a ((x_assn\<times>\<^sub>acf_assn)\<times>\<^sub>aq_assn)" 
  unfolding fifo_push2_def PR_CONST_def
  by sepref  
concrete_definition (in -) fifo_push_impl 
  uses Network_Impl.fifo_push_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_push_impl.refine[OF Network_Impl_axioms]
  
subsubsection \<open>Gap-Relabel\<close>   
  
sepref_thm fifo_gap_relabel_impl is "uncurry5 (PR_CONST fifo_gap_relabel2)" 
    :: "nat_assn\<^sup>k *\<^sub>a am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a clc_assn\<^sup>d *\<^sub>a q_assn\<^sup>d *\<^sub>a node_assn\<^sup>k 
      \<rightarrow>\<^sub>a clc_assn \<times>\<^sub>a q_assn" 
  unfolding fifo_gap_relabel2_def PR_CONST_def
  by sepref  
concrete_definition (in -) fifo_gap_relabel_impl 
  uses Network_Impl.fifo_gap_relabel_impl.refine_raw is "(uncurry5 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_gap_relabel_impl.refine[OF Network_Impl_axioms]

subsubsection \<open>Discharge\<close>  
  
sepref_thm fifo_dis_loop_impl is "uncurry5 (PR_CONST dis_loop2)" 
    :: "am_assn\<^sup>k *\<^sub>a x_assn\<^sup>d *\<^sub>a cf_assn\<^sup>d *\<^sub>a clc_assn\<^sup>d *\<^sub>a q_assn\<^sup>d *\<^sub>a node_assn\<^sup>k 
      \<rightarrow>\<^sub>a (x_assn\<times>\<^sub>acf_assn)\<times>\<^sub>aclc_assn \<times>\<^sub>a q_assn" 
  unfolding dis_loop2_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_dis_loop_impl 
  uses Network_Impl.fifo_dis_loop_impl.refine_raw is "(uncurry5 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_dis_loop_impl.refine[OF Network_Impl_axioms]
  
sepref_thm fifo_fifo_discharge_impl is "uncurry5 (PR_CONST fifo_discharge2)" 
    :: "nat_assn\<^sup>k *\<^sub>a am_assn\<^sup>k *\<^sub>a x_assn\<^sup>d *\<^sub>a cf_assn\<^sup>d *\<^sub>a clc_assn\<^sup>d *\<^sub>a q_assn\<^sup>d 
    \<rightarrow>\<^sub>a (x_assn\<times>\<^sub>acf_assn)\<times>\<^sub>aclc_assn \<times>\<^sub>a q_assn" 
  unfolding fifo_discharge2_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_fifo_discharge_impl 
  uses Network_Impl.fifo_fifo_discharge_impl.refine_raw is "(uncurry5 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = 
  fifo_fifo_discharge_impl.refine[OF Network_Impl_axioms]
  
subsubsection \<open>Computing the Initial State\<close>  
sepref_thm fifo_init_C_impl is "(PR_CONST init_C)" 
    :: "am_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn" 
  unfolding init_C_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_init_C_impl 
  uses Network_Impl.fifo_init_C_impl.refine_raw is "(?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_init_C_impl.refine[OF Network_Impl_axioms]
  
sepref_thm fifo_q_init_impl is "(PR_CONST q_init)" 
    :: "am_assn\<^sup>k \<rightarrow>\<^sub>a q_assn" 
  unfolding q_init_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_q_init_impl 
  uses Network_Impl.fifo_q_init_impl.refine_raw is "(?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_q_init_impl.refine[OF Network_Impl_axioms]

sepref_thm pp_init_xcf2'_impl is "uncurry (PR_CONST pp_init_xcf2')" 
    :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>d \<rightarrow>\<^sub>a x_assn \<times>\<^sub>a cf_assn" 
  unfolding pp_init_xcf2'_def PR_CONST_def
  by sepref
concrete_definition (in -) pp_init_xcf2'_impl 
  uses Network_Impl.pp_init_xcf2'_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas [sepref_fr_rules] = pp_init_xcf2'_impl.refine[OF Network_Impl_axioms]

subsubsection \<open>Main Algorithm\<close>  
sepref_thm fifo_push_relabel_run_impl 
  is "uncurry (PR_CONST fifo_push_relabel_run2)" 
    :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>d \<rightarrow>\<^sub>a cf_assn" 
  unfolding fifo_push_relabel_run2_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_push_relabel_run_impl 
  uses Network_Impl.fifo_push_relabel_run_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas [sepref_fr_rules] = 
  fifo_push_relabel_run_impl.refine[OF Network_Impl_axioms]
  
sepref_thm fifo_push_relabel_init_impl 
  is "uncurry0 (PR_CONST fifo_push_relabel_init2)" 
    :: "unit_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn" 
  unfolding fifo_push_relabel_init2_def PR_CONST_def
  by sepref
concrete_definition (in -) fifo_push_relabel_init_impl 
  uses Network_Impl.fifo_push_relabel_init_impl.refine_raw 
    is "(uncurry0 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = 
  fifo_push_relabel_init_impl.refine[OF Network_Impl_axioms]

  
sepref_thm fifo_push_relabel_impl is "(PR_CONST fifo_push_relabel2)" 
    :: "am_assn\<^sup>k \<rightarrow>\<^sub>a cf_assn" 
  unfolding fifo_push_relabel2_alt PR_CONST_def
  by sepref
concrete_definition (in -) fifo_push_relabel_impl 
  uses Network_Impl.fifo_push_relabel_impl.refine_raw is "(?f,_)\<in>_"
lemmas [sepref_fr_rules] = fifo_push_relabel_impl.refine[OF Network_Impl_axioms]
  
  
end \<comment> \<open>Network Impl. Locale\<close>
  
export_code fifo_push_relabel_impl checking SML_imp 
  
subsection \<open>Combining the Refinement Steps\<close>  
  
  
theorem (in Network_Impl) fifo_push_relabel_impl_correct[sep_heap_rules]: 
  assumes AM: "is_adj_map am"
  shows "
    <am_assn am ami> 
      fifo_push_relabel_impl c s t N ami
    <\<lambda>cfi. \<exists>\<^sub>Acf. 
        am_assn am ami * cf_assn cf cfi 
      * \<up>(isMaxFlow (flow_of_cf cf) \<and> RGraph_Impl c s t N cf)>\<^sub>t"
proof -
  note fifo_push_relabel2_refine[OF AM]    
  also note fifo_push_relabel_correct
  finally have R1: 
    "fifo_push_relabel2 am 
    \<le> \<Down> (br flow_of_cf (RPreGraph c s t)) (SPEC isMaxFlow)" .  

  have [simp]: "nofail (\<Down>R (RES X))" for R X by (auto simp: refine_pw_simps)

  note R2 = fifo_push_relabel_impl.refine[
              OF Network_Impl_axioms, to_hnr, unfolded autoref_tag_defs]
  note R3 = hn_refine_ref[OF R1 R2, of ami]
  note R4 = R3[unfolded hn_ctxt_def pure_def, THEN hn_refineD, simplified]
    
  note RGII = rgraph_and_network_impl_imp_rgraph_impl[OF 
    RPreGraph.maxflow_imp_rgraph
    Network_Impl_axioms
      ]  
    
  show ?thesis  
    by (sep_auto 
        heap: R4 
        simp: RGII
        simp: pw_le_iff refine_pw_simps in_br_conv)
qed

subsection \<open>Combination with Network Checker and Main Correctness Theorem\<close>
  
definition "fifo_push_relabel_impl_tab_am c s t N am \<equiv> do {
  ami \<leftarrow> Array.make N am;  \<comment> \<open>TODO/DUP: Called \<open>init_ps\<close> in Edmonds-Karp impl\<close>
  cfi \<leftarrow> fifo_push_relabel_impl c s t N ami;
  return (ami,cfi)
}"  
  
  
theorem fifo_push_relabel_impl_tab_am_correct[sep_heap_rules]: 
  assumes NW: "Network c s t"
  assumes VN: "Graph.V c \<subseteq> {0..<N}"
  assumes ABS_PS: "Graph.is_adj_map c am"
  shows "
    <emp> 
      fifo_push_relabel_impl_tab_am c s t N am
    <\<lambda>(ami,cfi). \<exists>\<^sub>Acf. 
        am_assn N am ami * cf_assn N cf cfi
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
    unfolding fifo_push_relabel_impl_tab_am_def 
    apply vcg
    apply (rule Hoare_Triple.cons_rule[
            OF _ _ fifo_push_relabel_impl_correct[OF ABS_PS]])
    subgoal unfolding am_assn_def is_nf_def by sep_auto
    apply (rule ent_refl)    
    subgoal by sep_auto
    done  
qed        
  
  
definition "fifo_push_relabel el s t \<equiv> do {
  case prepareNet el s t of
    None \<Rightarrow> return None
  | Some (c,am,N) \<Rightarrow> do {
      (ami,cf) \<leftarrow> fifo_push_relabel_impl_tab_am c s t N am;
      return (Some (c,ami,N,cf))
  }
}"
export_code fifo_push_relabel checking SML_imp

  
(* TODO: Also generate correctness theorem for fifo_push_relabel_run!
  For this, push the split up to abstract level!
*)  
  
text \<open>
  Main correctness statement:
  \<^item> If \<open>fifo_push_relabel\<close> returns \<open>None\<close>, the edge list was invalid or 
    described an invalid network. 
  \<^item> If it returns \<open>Some (c,am,N,cfi)\<close>, then the edge list is valid and describes 
    a valid network. Moreover, \<open>cfi\<close> is an integer square matrix of dimension 
    \<open>N\<close>, which describes a valid residual graph in the network, whose 
    corresponding flow is maximal. Finally, \<open>am\<close> is a valid adjacency map of the
    graph, and the nodes of the graph are integers less than \<open>N\<close>.
\<close>  
  
theorem fifo_push_relabel_correct[sep_heap_rules]:
  "<emp>
  fifo_push_relabel el s t
  <\<lambda>
    None \<Rightarrow> \<up>(\<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)
  | Some (c,ami,N,cfi) \<Rightarrow> 
      \<up>(c = ln_\<alpha> el \<and> ln_invar el \<and> Network c s t) 
    * (\<exists>\<^sub>Aam cf. am_assn N am ami * cf_assn N cf cfi 
          * \<up>(RGraph_Impl c s t N cf \<and> Graph.is_adj_map c am
            \<and> Network.isMaxFlow c s t (Network.flow_of_cf c cf))
      )
  >\<^sub>t
  "
  unfolding fifo_push_relabel_def
  using prepareNet_correct[of el s t]
  by (sep_auto simp: ln_rel_def in_br_conv)
  

subsubsection \<open>Justification of Splitting into Prepare and Run Phase\<close>    
(* TODO: Show correctness theorems for both phases separately!  *)    
    
definition "fifo_push_relabel_prepare_impl el s t \<equiv> do {
  case prepareNet el s t of
    None \<Rightarrow> return None
  | Some (c,am,N) \<Rightarrow> do {
      ami \<leftarrow> Array.make N am;
      cfi \<leftarrow> fifo_push_relabel_init_impl c N;
      return (Some (N,ami,c,cfi))
    }
}"

theorem justify_fifo_push_relabel_prep_run_split:
  "fifo_push_relabel el s t = 
  do {
    pr \<leftarrow> fifo_push_relabel_prepare_impl el s t;
    case pr of
      None \<Rightarrow> return None
    | Some (N,ami,c,cf) \<Rightarrow> do {
        cf \<leftarrow> fifo_push_relabel_run_impl s t N ami cf;
        return (Some (c,ami,N,cf))
      }
  }"  
  unfolding fifo_push_relabel_def fifo_push_relabel_prepare_impl_def
    fifo_push_relabel_impl_tab_am_def fifo_push_relabel_impl_def
  by (auto split: option.split)  
  
  
subsection \<open>Usage Example: Computing Maxflow Value \<close>
text \<open>We implement a function to compute the value of the maximum flow.\<close>
  
definition "fifo_push_relabel_compute_flow_val el s t \<equiv> do {
  r \<leftarrow> fifo_push_relabel el s t;
  case r of 
    None \<Rightarrow> return None
  | Some (c,am,N,cf) \<Rightarrow> do {
      v \<leftarrow> compute_flow_val_impl s N am cf;
      return (Some v)
    }
}"
    
text \<open>The computed flow value is correct\<close>  
theorem fifo_push_relabel_compute_flow_val_correct:
  "<emp> 
    fifo_push_relabel_compute_flow_val el s t 
  <\<lambda>
    None \<Rightarrow> \<up>(\<not>ln_invar el \<or> \<not>Network (ln_\<alpha> el) s t)
  | Some v \<Rightarrow> \<up>( ln_invar el 
      \<and> (let c = ln_\<alpha> el in
          Network c s t \<and> Network.is_max_flow_val c s t v
        ))    
  >\<^sub>t"  
proof -
  {
    fix cf N
    assume "RGraph_Impl (ln_\<alpha> el) s t N cf"
    then interpret RGraph "(ln_\<alpha> el)" s t cf by (rule RGraph_Impl.axioms)
    have "f = flow_of_cf cf" unfolding f_def by simp
  } note aux=this
  
  show ?thesis
    unfolding fifo_push_relabel_compute_flow_val_def    
    by (sep_auto simp: Network.is_max_flow_val_def aux)
      
qed    
      
export_code fifo_push_relabel_compute_flow_val checking SML_imp  
  

end
