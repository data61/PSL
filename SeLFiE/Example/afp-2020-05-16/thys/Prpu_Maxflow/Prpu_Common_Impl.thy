section \<open>Tools for Implementing Push-Relabel Algorithms\<close>
theory Prpu_Common_Impl
imports
  Prpu_Common_Inst
  Flow_Networks.Network_Impl 
  Flow_Networks.NetCheck
begin
  
subsection \<open>Basic Operations\<close>
  
type_synonym excess_impl = "node \<Rightarrow> capacity_impl"  
  
context Network_Impl 
begin  

subsubsection \<open>Excess Map\<close>    
text \<open>Obtain an excess map with all nodes mapped to zero.\<close>  
definition x_init :: "excess_impl nres" where "x_init \<equiv> return (\<lambda>_. 0)"
text \<open>Get the excess of a node.\<close>  
definition x_get :: "excess_impl \<Rightarrow> node \<Rightarrow> capacity_impl nres" 
  where "x_get x u \<equiv> do {
    assert (u\<in>V);
    return (x u)
  }"
text \<open>Add a capacity to the excess of a node.\<close>    
definition x_add :: "excess_impl \<Rightarrow> node \<Rightarrow> capacity_impl \<Rightarrow> excess_impl nres"  
  where "x_add x u \<Delta> \<equiv> do {
    assert (u\<in>V);
    return (x(u := x u + \<Delta>))
  }"
  
subsubsection \<open>Labeling\<close>
text \<open>Obtain the initial labeling: All nodes are zero, except the 
  source which is labeled by \<open>|V|\<close>. The exact cardinality of \<open>V\<close> is passed
  as a parameter.
\<close>  
definition l_init :: "nat \<Rightarrow> (node \<Rightarrow> nat) nres"
  where "l_init C \<equiv> return ((\<lambda>_. 0)(s := C))"

text \<open>Get the label of a node.\<close>    
definition l_get :: "(node \<Rightarrow> nat) \<Rightarrow> node \<Rightarrow> nat nres"    
  where "l_get l u \<equiv> do {
    assert (u \<in> V);
    return (l u)
  }"

text \<open>Set the label of a node.\<close>    
definition l_set :: "(node \<Rightarrow> nat) \<Rightarrow> node \<Rightarrow> nat \<Rightarrow> (node \<Rightarrow> nat) nres"    
  where "l_set l u a \<equiv> do {
    assert (u\<in>V);
    assert (a < 2*card V);
    return (l(u := a))
  }"

subsubsection \<open>Label Frequency Counts for Gap Heuristics\<close>
text \<open>Obtain the frequency counts for the initial labeling.
  Again, the cardinality of \<open>|V|\<close>, which is required to determine the label
  of the source node, is passed as an explicit parameter.
\<close>  
definition cnt_init :: "nat \<Rightarrow> (nat \<Rightarrow> nat) nres"
  where "cnt_init C \<equiv> do {
    assert (C<2*N);
    return ((\<lambda>_. 0)(0 := C - 1, C := 1))
  }"

text \<open>Get the count for a label value.\<close>    
definition cnt_get :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat nres"    
  where "cnt_get cnt lv \<equiv> do {
    assert (lv < 2*N);
    return (cnt lv)
  }"

text \<open>Increment the count for a label value by one.\<close>    
definition cnt_incr :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) nres"    
  where "cnt_incr cnt lv \<equiv> do {
    assert (lv < 2*N);
    return (cnt ( lv := cnt lv + 1 ))
  }"

text \<open>Decrement the count for a label value by one.\<close>    
definition cnt_decr :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> nat) nres"    
  where "cnt_decr cnt lv \<equiv> do {
    assert (lv < 2*N \<and> cnt lv > 0);
    return (cnt ( lv := cnt lv - 1 ))
  }"
    
end \<comment> \<open>Network Implementation Locale\<close>  

  
subsection \<open>Refinements to Basic Operations\<close>  
  
context Network_Impl 
begin  
text \<open>In this section, we refine the algorithm to actually use the 
 basic operations.
\<close>
  
subsubsection \<open>Explicit Computation of the Excess\<close>  
definition "xf_rel \<equiv> { ((excess f,cf_of f),f) | f. True }"
lemma xf_rel_RELATES[refine_dref_RELATES]: "RELATES xf_rel" 
  by (auto simp: RELATES_def)
  
definition "pp_init_x 
  \<equiv> \<lambda>u. (if u=s then (\<Sum>(u,v)\<in>outgoing s. - c(u,v)) else c (s,u))"
  
lemma excess_pp_init_f[simp]: "excess pp_init_f = pp_init_x"  
  apply (intro ext)  
  subgoal for u  
    unfolding excess_def pp_init_f_def pp_init_x_def
    apply (cases "u=s")  
    subgoal
      unfolding outgoing_def incoming_def    
      by (auto intro: sum.cong simp: sum_negf)
    subgoal proof -
      assume [simp]: "u\<noteq>s"
      have [simp]: 
        "(case e of (u, v) \<Rightarrow> if u = s then c (u, v) else 0) = 0" 
        if "e\<in>outgoing u" for e
        using that by (auto simp: outgoing_def)
      have [simp]: "(case e of (u, v) \<Rightarrow> if u = s then c (u, v) else 0) 
        = (if e = (s,u) then c (s,u) else 0)" 
        if "e\<in>incoming u" for e
        using that by (auto simp: incoming_def split: if_splits)
      show ?thesis by (simp add: sum.delta) (simp add: incoming_def)
    qed 
    done  
  done  
    
definition "pp_init_cf 
  \<equiv> \<lambda>(u,v). if (v=s) then c (v,u) else if u=s then 0 else c (u,v)"
lemma cf_of_pp_init_f[simp]: "cf_of pp_init_f = pp_init_cf"
  apply (intro ext)  
  unfolding pp_init_cf_def pp_init_f_def residualGraph_def
  using no_parallel_edge  
  by auto  
    
  
lemma pp_init_x_rel: "((pp_init_x, pp_init_cf), pp_init_f) \<in> xf_rel"
  unfolding xf_rel_def by auto

subsubsection \<open>Algorithm to Compute Initial Excess and Flow\<close>    
definition "pp_init_xcf2_aux \<equiv> do {
  let x=(\<lambda>_. 0);
  let cf=c;

  foreach (adjacent_nodes s) (\<lambda>v (x,cf). do {
    assert ((s,v)\<in>E);
    assert (s \<noteq> v);
    let a = cf (s,v);
    assert (x v = 0);
    let x = x( s := x s - a, v := a );
    let cf = cf( (s,v) := 0, (v,s) := a);
    return (x,cf)
  }) (x,cf)
}"
  
lemma pp_init_xcf2_aux_spec: 
  shows "pp_init_xcf2_aux \<le> SPEC (\<lambda>(x,cf). x=pp_init_x \<and> cf = pp_init_cf)"
proof -
  have ADJ_S_AUX: "adjacent_nodes s = {v . (s,v)\<in>E}"
    unfolding adjacent_nodes_def using no_incoming_s by auto
    
  have CSU_AUX: "c (s,u) = 0" if "u\<notin>adjacent_nodes s" for u
    using that unfolding adjacent_nodes_def by auto
      
  show ?thesis
    unfolding pp_init_xcf2_aux_def
    apply (refine_vcg FOREACH_rule[where I="\<lambda>it (x,cf). 
        x s = (\<Sum>v\<in>adjacent_nodes s - it. - c(s,v)) 
      \<and> (\<forall>v\<in>adjacent_nodes s. x v = (if v\<in>it then 0 else c (s,v)))
      \<and> (\<forall>v\<in>-insert s (adjacent_nodes s). x v = 0)
      \<and> (\<forall>v\<in>adjacent_nodes s. 
            if v\<notin>it then cf (s,v) = 0 \<and> cf (v,s) = c (s,v) 
            else cf (s,v) = c (s,v) \<and> cf (v,s) = c (v,s))
      \<and> (\<forall>u v. u\<noteq>s \<and> v\<noteq>s \<longrightarrow> cf (u,v) = c (u,v) )
      \<and> (\<forall>u. u\<notin>adjacent_nodes s \<longrightarrow> cf (u,s) = 0 \<and> cf (s,u) = 0)
    "])
    apply (vc_solve simp: it_step_insert_iff simp: CSU_AUX)
    subgoal for v it by (auto simp: ADJ_S_AUX) 
    subgoal for u it _ v by (auto split: if_splits)
    subgoal by (auto simp: ADJ_S_AUX)    
    subgoal by (auto simp: ADJ_S_AUX)    
    subgoal by (auto split: if_splits)    
    (* TODO: This proof is still a bit fragile *)    
    subgoal for x
      unfolding pp_init_x_def
      apply (intro ext)  
      subgoal for u  
        apply (clarsimp simp: ADJ_S_AUX outgoing_def; intro conjI)  
        applyS (auto intro!: sum.reindex_cong[where l=snd] intro: inj_onI)
        applyS (metis (mono_tags, lifting) Compl_iff Graph.zero_cap_simp insertE mem_Collect_eq)  
        done
      done  
    subgoal for x cf    
      unfolding pp_init_cf_def
      apply (intro ext)  
      apply (clarsimp; auto simp: CSU_AUX)
      done  
    done  
qed      
    
definition "pp_init_xcf2 am \<equiv> do {
  x \<leftarrow> x_init;
  cf \<leftarrow> cf_init;

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
  
  
lemma pp_init_xcf2_refine_aux:
  assumes AM: "is_adj_map am"  
  shows "pp_init_xcf2 am \<le> \<Down>Id (pp_init_xcf2_aux)"
  unfolding pp_init_xcf2_def pp_init_xcf2_aux_def
  unfolding x_init_def cf_init_def am_get_def cf_get_def cf_set_def x_add_def  
  apply (simp only: nres_monad_laws)
  supply LFO_refine[OF am_to_adj_nodes_refine[OF AM], refine]
  apply refine_rcg  
  using E_ss_VxV  
  by auto
  
  
lemma pp_init_xcf2_refine[refine2]: 
  assumes AM: "is_adj_map am"  
  shows "pp_init_xcf2 am \<le>\<Down>xf_rel (RETURN pp_init_f)"
  using pp_init_xcf2_refine_aux[OF AM] pp_init_xcf2_aux_spec pp_init_x_rel
  by (auto simp: pw_le_iff refine_pw_simps)  
  
subsubsection \<open>Computing the Minimal Adjacent Label\<close>  
definition (in Network) "min_adj_label_aux cf l u \<equiv> do {
  assert (u\<in>V);
  x \<leftarrow> foreach (adjacent_nodes u) (\<lambda>v x. do {
    assert ((u,v)\<in>E\<union>E\<inverse>);
    assert (v\<in>V);
    if (cf (u,v) \<noteq> 0) then 
      case x of 
        None \<Rightarrow> return (Some (l v)) 
      | Some xx \<Rightarrow> return (Some (min (l v) (xx)))
    else
      return x
  }) None;

  assert (x\<noteq>None);
  return (the x)
}"
    

lemma (in -) set_filter_xform_aux: 
  "{ f x | x. ( x = a \<or> x\<in>S \<and> x\<notin>it ) \<and> P x } 
  = (if P a then {f a} else {}) \<union> {f x | x. x\<in>S-it \<and> P x}"    
  by auto
    
lemma (in Labeling) min_adj_label_aux_spec: 
  assumes PRE: "relabel_precond f l u"
  shows "min_adj_label_aux cf l u \<le> SPEC (\<lambda>x. x = Min { l v | v. (u,v)\<in>cf.E })"
proof -
  have AUX: "cf (u,v) \<noteq> 0 \<longleftrightarrow> (u,v)\<in>cf.E" for v unfolding cf.E_def by auto
  
  have EQ: "{ l v | v. (u,v)\<in>cf.E } 
    = { l v | v. v\<in>adjacent_nodes u \<and> cf (u,v)\<noteq>0 }"
    unfolding AUX
    using cfE_ss_invE
    by (auto simp: adjacent_nodes_def)
  
  define Min_option :: "nat set \<rightharpoonup> nat" 
    where "Min_option X \<equiv> if X={} then None else Some (Min X)" for X
      
  from PRE active_has_cf_outgoing have "cf.outgoing u \<noteq> {}" 
    unfolding relabel_precond_def by auto
  hence [simp]: "u\<in>V" unfolding cf.outgoing_def using cfE_of_ss_VxV by auto
  from \<open>cf.outgoing u \<noteq> {}\<close> 
  have AUX2: "\<exists>v. v \<in> adjacent_nodes u \<and> cf (u, v) \<noteq> 0"
    by (smt AUX Collect_empty_eq Image_singleton_iff UnCI adjacent_nodes_def 
            cf.outgoing_def cf_def converse_iff prod.simps(2))
      
  show ?thesis unfolding min_adj_label_aux_def EQ   
    apply (refine_vcg 
        FOREACH_rule[where 
          I="\<lambda>it x. x = Min_option 
                          { l v | v. v\<in>adjacent_nodes u - it \<and> cf (u,v)\<noteq>0 }"]
        )  
    apply (vc_solve 
        simp: Min_option_def it_step_insert_iff set_filter_xform_aux 
        split: if_splits)
    subgoal unfolding adjacent_nodes_def by auto  
    subgoal unfolding adjacent_nodes_def by auto  
    subgoal using adjacent_nodes_ss_V by auto  
    subgoal using adjacent_nodes_ss_V by auto
    subgoal by (auto simp: Min.insert_remove)
    subgoal using AUX2 by auto
    done    
qed        

definition "min_adj_label am cf l u \<equiv> do {
  assert (u\<in>V);
  adj \<leftarrow> am_get am u;
  x \<leftarrow> nfoldli adj (\<lambda>_. True) (\<lambda>v x. do {
    assert ((u,v)\<in> E \<union> E\<inverse>);
    assert (v\<in>V);
    cfuv \<leftarrow> cf_get cf (u,v);
    if (cfuv \<noteq> 0) then do {
      lv \<leftarrow> l_get l v;
      case x of 
        None \<Rightarrow> return (Some lv) 
      | Some xx \<Rightarrow> return (Some (min lv xx))
    } else
      return x
  }) None;

  assert (x\<noteq>None);
  return (the x)
}"

lemma min_adj_label_refine[THEN order_trans, refine_vcg]:
  assumes "Height_Bounded_Labeling c s t f l"
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes PRE: "relabel_precond f l u"
  assumes [simp]: "cf = cf_of f"  
  shows "min_adj_label am cf l u \<le> SPEC (\<lambda>x. x 
        = Min { l v | v. (u,v)\<in>cfE_of f })"  
proof - 
  interpret Height_Bounded_Labeling c s t f l by fact

  have "min_adj_label am (cf_of f) l u \<le> \<Down>Id (min_adj_label_aux (cf_of f) l u)"  
    unfolding min_adj_label_def min_adj_label_aux_def Let_def
    unfolding am_get_def cf_get_def l_get_def  
    apply (simp only: nres_monad_laws)  
    supply LFO_refine[OF fun_relD[OF AM IdI] _ IdI, refine]
    apply (refine_rcg)
    apply refine_dref_type  
    by auto  
  also note min_adj_label_aux_spec[OF PRE]    
  finally show ?thesis by simp  
qed      

subsubsection \<open>Refinement of Relabel\<close>
text \<open>Utilities to Implement Relabel Operations\<close>    
    
definition "relabel2 am cf l u \<equiv> do {
  assert (u\<in>V - {s,t});
  nl \<leftarrow> min_adj_label am cf l u;
  l \<leftarrow> l_set l u (nl+1);
  return l
}"
  
lemma relabel2_refine[refine]: 
  assumes "((x,cf),f)\<in>xf_rel"
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(li,l)\<in>Id" "(ui,u)\<in>Id"
  shows "relabel2 am cf li ui \<le> \<Down>Id (relabel f l u)"    
proof -
  have [simp]: "{l v |v. v \<in> V \<and> cf_of f (u, v) \<noteq> 0} = {l v |v. cf_of f (u, v) \<noteq> 0}"
    using cfE_of_ss_VxV[of f] 
    by (auto simp: Graph.E_def)
  
  show ?thesis
    using assms
    unfolding relabel2_def relabel_def
    unfolding l_set_def
    apply (refine_vcg AM)
    apply (vc_solve (nopre) simp: xf_rel_def relabel_effect_def solve: asm_rl)
    subgoal premises prems for a proof -   
      from prems interpret Height_Bounded_Labeling c s t f l by simp
      interpret l': Height_Bounded_Labeling c s t f "relabel_effect f l u"
        by (rule relabel_pres_height_bound) (rule prems)
      from prems have "u\<in>V" by simp
      from prems have "a + 1 = relabel_effect f l u u"
        by (auto simp: relabel_effect_def)
      also note l'.height_bound[THEN bspec, OF \<open>u\<in>V\<close>]
      finally show "a + 1 < 2 * card V" using card_V_ge2 by auto
    qed      
    done
qed
  
subsubsection \<open>Refinement of Push\<close>  
definition "push2_aux x cf \<equiv> \<lambda>(u,v). do {
  assert ( (u,v) \<in> E \<union> E\<inverse> );
  assert ( u \<noteq> v );
  let \<Delta> = min (x u) (cf (u,v));
  return ((x( u := x u - \<Delta>, v := x v + \<Delta> ),augment_edge_cf cf (u,v) \<Delta>))
}"
    
  
lemma push2_aux_refine: 
  "\<lbrakk>((x,cf),f)\<in>xf_rel; (ei,e)\<in>Id\<times>\<^sub>rId\<rbrakk> 
    \<Longrightarrow> push2_aux x cf ei \<le> \<Down>xf_rel (push f l e)"
  unfolding push_def push2_aux_def
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

definition "push2 x cf \<equiv> \<lambda>(u,v). do {
  assert ( (u,v) \<in> E \<union> E\<inverse> );
  xu \<leftarrow> x_get x u;
  cfuv \<leftarrow> cf_get cf (u,v);
  cfvu \<leftarrow> cf_get cf (v,u);
  let \<Delta> = min xu cfuv;
  x \<leftarrow> x_add x u (-\<Delta>);
  x \<leftarrow> x_add x v \<Delta>;

  cf \<leftarrow> cf_set cf (u,v) (cfuv - \<Delta>);
  cf \<leftarrow> cf_set cf (v,u) (cfvu + \<Delta>);

  return (x,cf)
}"
    
lemma push2_refine[refine]: 
  assumes "((x,cf),f)\<in>xf_rel" "(ei,e)\<in>Id\<times>\<^sub>rId"
  shows "push2 x cf ei \<le> \<Down>xf_rel (push f l e)"
proof -
  have "push2 x cf ei \<le> (push2_aux x cf ei)"  
    unfolding push2_def push2_aux_def
    unfolding x_get_def x_add_def cf_get_def cf_set_def
    unfolding augment_edge_cf_def  
    apply (simp only: nres_monad_laws)  
    apply refine_vcg  
    using E_ss_VxV  
    by auto  
  also note push2_aux_refine[OF assms]    
  finally show ?thesis . 
qed  
  
  
  
subsubsection \<open>Adding frequency counters to labeling\<close>
      
definition "l_invar l \<equiv> \<forall>v. l v \<noteq> 0 \<longrightarrow> v\<in>V"  

definition "clc_invar \<equiv> \<lambda>(cnt,l). 
  (\<forall>lv. cnt lv = card { u\<in>V . l u = lv }) 
\<and> (\<forall>u. l u < 2*N) \<and> l_invar l"
definition "clc_rel \<equiv> br snd clc_invar"    
    
definition "clc_init C \<equiv> do {
  l \<leftarrow> l_init C;
  cnt \<leftarrow> cnt_init C;
  return (cnt,l)
}"
  
definition "clc_get \<equiv> \<lambda>(cnt,l) u. l_get l u"
definition "clc_set \<equiv> \<lambda>(cnt,l) u a. do {
  assert (a<2*N);
  lu \<leftarrow> l_get l u;
  cnt \<leftarrow> cnt_decr cnt lu;
  l \<leftarrow> l_set l u a;
  lu \<leftarrow> l_get l u;
  cnt \<leftarrow> cnt_incr cnt lu;
  return (cnt,l)
}"  

definition "clc_has_gap \<equiv> \<lambda>(cnt,l) lu. do {
  nlu \<leftarrow> cnt_get cnt lu;
  return (nlu = 0)
}"
    
lemma cardV_le_N: "card V \<le> N" using card_mono[OF _ V_ss] by auto
lemma N_not_Z: "N \<noteq> 0" using card_V_ge2 cardV_le_N by auto
lemma N_ge_2: "2\<le>N" using card_V_ge2 cardV_le_N by auto
  
lemma clc_init_refine[refine]:
  assumes [simplified,simp]: "(Ci,C)\<in>nat_rel" 
  assumes [simp]: "C = card V" 
  shows "clc_init Ci \<le>\<Down>clc_rel (l_init C)"  
proof -
  have AUX: "{u. u \<noteq> s \<and> u \<in> V} = V-{s}" by auto
  
  show ?thesis
    unfolding clc_init_def l_init_def cnt_init_def
    apply refine_vcg
    unfolding clc_rel_def clc_invar_def
    using cardV_le_N N_not_Z
    by (auto simp: in_br_conv V_not_empty AUX l_invar_def)  
qed  

lemma clc_get_refine[refine]: 
  "\<lbrakk> (clc,l)\<in>clc_rel; (ui,u)\<in>nat_rel \<rbrakk> \<Longrightarrow> clc_get clc ui \<le>\<Down>Id (l_get l u)"
  unfolding clc_get_def clc_rel_def
  by (auto simp: in_br_conv split: prod.split)  

definition l_get_rlx :: "(node \<Rightarrow> nat) \<Rightarrow> node \<Rightarrow> nat nres"    
  where "l_get_rlx l u \<equiv> do {
    assert (u < N);
    return (l u)
  }"
definition "clc_get_rlx \<equiv> \<lambda>(cnt,l) u. l_get_rlx l u"
  
lemma clc_get_rlx_refine[refine]: 
  "\<lbrakk> (clc,l)\<in>clc_rel; (ui,u)\<in>nat_rel \<rbrakk> 
  \<Longrightarrow> clc_get_rlx clc ui \<le>\<Down>Id (l_get_rlx l u)"
  unfolding clc_get_rlx_def clc_rel_def
  by (auto simp: in_br_conv split: prod.split)  
    
lemma card_insert_disjointI: 
  "\<lbrakk> finite Y; X = insert x Y; x\<notin>Y \<rbrakk> \<Longrightarrow> card X = Suc (card Y)"    
  by auto
  
lemma clc_set_refine[refine]:
  "\<lbrakk> (clc,l) \<in> clc_rel; (ui,u)\<in>nat_rel; (ai,a)\<in>nat_rel \<rbrakk> \<Longrightarrow>
    clc_set clc ui ai \<le>\<Down>clc_rel (l_set l u a)"
  unfolding clc_set_def l_set_def l_get_def cnt_decr_def cnt_incr_def
  apply refine_vcg  
  apply vc_solve
  unfolding clc_rel_def in_br_conv clc_invar_def l_invar_def
  subgoal using cardV_le_N by auto
  applyS auto  
  applyS (auto simp: simp: card_gt_0_iff)
    
  subgoal for cnt ll 
    apply clarsimp  
    apply (intro impI conjI; clarsimp?)
    subgoal  
      apply (subst le_imp_diff_is_add; simp)
      apply (rule card_insert_disjointI[where x=u])
      by auto
    subgoal     
      apply (rule card_insert_disjointI[where x=u, symmetric])
      by auto
    subgoal
      by (auto intro!: arg_cong[where f=card])
    done
  done    

lemma clc_has_gap_correct[THEN order_trans, refine_vcg]:
  "\<lbrakk>(clc,l)\<in>clc_rel; k<2*N\<rbrakk> 
  \<Longrightarrow> clc_has_gap clc k \<le> (spec r. r \<longleftrightarrow> gap_precond l k)"
  unfolding clc_has_gap_def cnt_get_def gap_precond_def
  apply refine_vcg  
  unfolding clc_rel_def clc_invar_def in_br_conv
  by auto  
  
  
    
subsubsection \<open>Refinement of Gap-Heuristics\<close>
text \<open>Utilities to Implement Gap-Heuristics\<close>    
    
definition "gap_aux C l k \<equiv> do {
  nfoldli [0..<N] (\<lambda>_. True) (\<lambda>v l. do {
    lv \<leftarrow> l_get_rlx l v;
    if (k < lv \<and> lv < C) then do {
      assert (C+1 < 2*N);
      l \<leftarrow> l_set l v (C+1);
      return l
    } else return l
  }) l
}"
  
lemma gap_effect_invar[simp]: "l_invar l \<Longrightarrow> l_invar (gap_effect l k)"   
  unfolding gap_effect_def l_invar_def
  by auto  
  
lemma relabel_effect_invar[simp]: "\<lbrakk>l_invar l; u\<in>V\<rbrakk> \<Longrightarrow> l_invar (relabel_effect f l u)"    
  unfolding relabel_effect_def l_invar_def by auto
    
lemma gap_aux_correct[THEN order_trans, refine_vcg]: 
  "\<lbrakk>l_invar l; C=card V\<rbrakk> \<Longrightarrow> gap_aux C l k \<le> SPEC (\<lambda>r. r=gap_effect l k)"
  unfolding gap_aux_def l_get_rlx_def l_set_def
  apply (simp only: nres_monad_laws)  
  apply (refine_vcg nfoldli_rule[where I = "\<lambda>it1 it2 l'. \<forall>u. if u\<in>set it2 then l' u = l u else l' u = gap_effect l k u"])
  apply (vc_solve simp: upt_eq_lel_conv)
  subgoal
    apply (frule gap_effect_invar[where k=k])
    unfolding l_invar_def using V_ss by force 
  subgoal using N_not_Z cardV_le_N by auto
  subgoal unfolding l_invar_def by auto  
  subgoal unfolding gap_effect_def by auto
  subgoal for v l' u
    apply (drule spec[where x=u])
    by (auto split: if_splits simp: gap_effect_def)
  subgoal by auto
  done  
    
definition "gap2 C clc k \<equiv> do {
  nfoldli [0..<N] (\<lambda>_. True) (\<lambda>v clc. do {
    lv \<leftarrow> clc_get_rlx clc v;
    if (k < lv \<and> lv < C) then do {
      clc \<leftarrow> clc_set clc v (C+1);
      return clc
    } else return clc
  }) clc
}"
    
lemma gap2_refine[refine]:  
  assumes [simplified,simp]: "(Ci,C)\<in>nat_rel" "(ki,k)\<in>nat_rel"
  assumes CLC: "(clc,l)\<in>clc_rel"  
  shows "gap2 Ci clc ki \<le>\<Down>clc_rel (gap_aux C l k)"
  unfolding gap2_def gap_aux_def  
  apply (refine_rcg CLC)
  apply refine_dref_type  
  by auto    
    
  
definition "gap_relabel_aux C f l u \<equiv> do {
  lu \<leftarrow> l_get l u;
  l \<leftarrow> relabel f l u;
  if gap_precond l lu then 
    gap_aux C l lu
  else return l
}"  

lemma gap_relabel_aux_refine: 
  assumes [simp]: "C = card V" "l_invar l"
  shows "gap_relabel_aux C f l u \<le> gap_relabel f l u"  
  unfolding gap_relabel_aux_def gap_relabel_def relabel_def 
    gap_relabel_effect_def l_get_def
  apply (simp only: Let_def nres_monad_laws)  
  apply refine_vcg  
  by auto  
    
    
    
definition "min_adj_label_clc am cf clc u \<equiv> case clc of (_,l) \<Rightarrow> min_adj_label am cf l u"
    
definition "clc_relabel2 am cf clc u \<equiv> do {
  assert (u\<in>V - {s,t});
  nl \<leftarrow> min_adj_label_clc am cf clc u;
  clc \<leftarrow> clc_set clc u (nl+1);
  return clc
}"
    
lemma clc_relabel2_refine[refine]: 
  assumes XF: "((x,cf),f)\<in>xf_rel"
  assumes CLC: "(clc,l)\<in>clc_rel"  
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(ui,u)\<in>Id"
  shows "clc_relabel2 am cf clc ui \<le> \<Down>clc_rel (relabel f l u)"    
proof -
  have "clc_relabel2 am cf clc ui \<le>\<Down>clc_rel (relabel2 am cf l ui)"
    unfolding clc_relabel2_def relabel2_def
    apply (refine_rcg)
    apply (refine_dref_type)  
    apply (vc_solve simp: CLC)
    subgoal 
      using CLC 
      unfolding clc_rel_def in_br_conv min_adj_label_clc_def 
      by (auto split: prod.split)
    done    
  also note relabel2_refine[OF XF AM, of l l ui u]
  finally show ?thesis by simp  
qed  
  
  
definition "gap_relabel2 C am cf clc u \<equiv> do {
  lu \<leftarrow> clc_get clc u;
  clc \<leftarrow> clc_relabel2 am cf clc u;
  has_gap \<leftarrow> clc_has_gap clc lu;
  if has_gap then gap2 C clc lu
  else 
    RETURN clc
}"  
  
lemma gap_relabel2_refine_aux:
  assumes XCF: "((x, cf), f) \<in> xf_rel"  
  assumes CLC: "(clc,l)\<in>clc_rel"  
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(Ci,C)\<in>Id" "(ui,u)\<in>Id"
  shows "gap_relabel2 Ci am cf clc ui \<le> \<Down>clc_rel (gap_relabel_aux C f l u)"  
  unfolding gap_relabel2_def gap_relabel_aux_def
  apply (refine_vcg XCF AM CLC if_bind_cond_refine bind_refine')
  apply (vc_solve solve: refl )
  subgoal for _ lu
    using CLC
    unfolding clc_get_def l_get_def clc_rel_def in_br_conv clc_invar_def
    by (auto simp: refine_pw_simps split: prod.splits)
  done    
    
lemma gap_relabel2_refine[refine]:
  assumes XCF: "((x, cf), f) \<in> xf_rel"  
  assumes CLC: "(clc,l)\<in>clc_rel"  
  assumes AM: "(am,adjacent_nodes)\<in>nat_rel\<rightarrow>\<langle>nat_rel\<rangle>list_set_rel"
  assumes [simplified,simp]: "(ui,u)\<in>Id"    
  assumes CC: "C = card V"  
  shows "gap_relabel2 C am cf clc ui \<le>\<Down>clc_rel (gap_relabel f l u)"
proof -
  from CLC have LINV: "l_invar l" unfolding clc_rel_def in_br_conv clc_invar_def by auto
  
  note gap_relabel2_refine_aux[OF XCF CLC AM IdI IdI]
  also note gap_relabel_aux_refine[OF CC LINV]  
  finally show ?thesis by simp  
qed    
    
    
subsection \<open>Refinement to Efficient Data Structures\<close>  
  
subsubsection \<open>Registration of Abstract Operations\<close>  
text \<open>We register all abstract operations at once, 
  auto-rewriting the capacity matrix type\<close>
  
context includes Network_Impl_Sepref_Register 
begin  
sepref_register x_get x_add
  
sepref_register l_init l_get l_get_rlx l_set

sepref_register clc_init clc_get clc_set clc_has_gap clc_get_rlx  
  
sepref_register cnt_init cnt_get cnt_incr cnt_decr  
sepref_register gap2 min_adj_label min_adj_label_clc 
  
sepref_register push2 relabel2 clc_relabel2 gap_relabel2
  
sepref_register pp_init_xcf2  
  
end \<comment> \<open>Anonymous Context\<close> 
  
  
subsubsection \<open>Excess by Array\<close>  
definition "x_assn \<equiv> is_nf N (0::capacity_impl)"    
  
lemma x_init_hnr[sepref_fr_rules]: 
  "(uncurry0 (Array.new N 0), uncurry0 x_init) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a x_assn"  
  apply sepref_to_hoare unfolding x_assn_def x_init_def 
  by (sep_auto heap: nf_init_rule)
    
lemma x_get_hnr[sepref_fr_rules]: 
  "(uncurry Array.nth, uncurry (PR_CONST x_get)) 
  \<in> x_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a cap_assn"
  apply sepref_to_hoare 
  unfolding x_assn_def x_get_def by (sep_auto simp: refine_pw_simps)
    
definition (in -) "x_add_impl x u \<Delta> \<equiv> do {
  xu \<leftarrow> Array.nth x u;
  x \<leftarrow> Array.upd u (xu+\<Delta>) x;
  return x
}"  
lemma x_add_hnr[sepref_fr_rules]: 
  "(uncurry2 x_add_impl, uncurry2 (PR_CONST x_add)) 
  \<in> x_assn\<^sup>d *\<^sub>a node_assn\<^sup>k *\<^sub>a cap_assn\<^sup>k \<rightarrow>\<^sub>a x_assn"  
  apply sepref_to_hoare 
  unfolding x_assn_def x_add_impl_def x_add_def 
  by (sep_auto simp: refine_pw_simps)

subsubsection \<open>Labeling by Array\<close>      
definition "l_assn \<equiv> is_nf N (0::nat)"    
definition (in -) "l_init_impl N s cardV \<equiv> do {
  l \<leftarrow> Array.new N (0::nat);
  l \<leftarrow> Array.upd s cardV l;
  return l
}"  
lemma l_init_hnr[sepref_fr_rules]: 
  "(l_init_impl N s, (PR_CONST l_init)) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a l_assn"  
  apply sepref_to_hoare 
  unfolding l_assn_def l_init_def l_init_impl_def 
  by (sep_auto heap: nf_init_rule)
    
lemma l_get_hnr[sepref_fr_rules]: 
  "(uncurry Array.nth, uncurry (PR_CONST l_get)) 
  \<in> l_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  apply sepref_to_hoare 
  unfolding l_assn_def l_get_def by (sep_auto simp: refine_pw_simps)
    
lemma l_get_rlx_hnr[sepref_fr_rules]: 
  "(uncurry Array.nth, uncurry (PR_CONST l_get_rlx)) 
  \<in> l_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"
  apply sepref_to_hoare 
  unfolding l_assn_def l_get_rlx_def by (sep_auto simp: refine_pw_simps)
    
    
lemma l_set_hnr[sepref_fr_rules]: 
  "(uncurry2 (\<lambda>a i x. Array.upd i x a), uncurry2 (PR_CONST l_set)) 
  \<in> l_assn\<^sup>d *\<^sub>a node_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a l_assn"
  apply sepref_to_hoare 
  unfolding l_assn_def l_set_def 
  by (sep_auto simp: refine_pw_simps split: prod.split)
      
    
subsubsection \<open>Label Frequency by Array\<close>  
  
definition "cnt_assn (f::node\<Rightarrow>nat) a 
  \<equiv> \<exists>\<^sub>Al. a\<mapsto>\<^sub>al * \<up>(length l = 2*N \<and> (\<forall>i<2*N. l!i = f i) \<and> (\<forall>i\<ge>2*N. f i = 0))"
  
definition (in -) "cnt_init_impl N C \<equiv> do {
  a \<leftarrow> Array.new (2*N) (0::nat);
  a \<leftarrow> Array.upd 0 (C-1) a;
  a \<leftarrow> Array.upd C 1 a;
  return a
}"  

definition (in -) "cnt_incr_impl a k \<equiv> do {
  freq \<leftarrow> Array.nth a k;
  a \<leftarrow> Array.upd k (freq+1) a;
  return a
}"  

definition (in -) "cnt_decr_impl a k \<equiv> do {
  freq \<leftarrow> Array.nth a k;
  a \<leftarrow> Array.upd k (freq-1) a;
  return a
}"  
  
 
lemma cnt_init_hnr[sepref_fr_rules]: "(cnt_init_impl N, PR_CONST cnt_init) \<in> nat_assn\<^sup>k \<rightarrow>\<^sub>a cnt_assn"
  apply sepref_to_hoare
  unfolding cnt_init_def cnt_init_impl_def cnt_assn_def
  by (sep_auto simp: refine_pw_simps) 

lemma cnt_get_hnr[sepref_fr_rules]: "(uncurry Array.nth, uncurry (PR_CONST cnt_get)) \<in> cnt_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"    
  apply sepref_to_hoare
  unfolding cnt_get_def cnt_assn_def
  by (sep_auto simp: refine_pw_simps) 

lemma cnt_incr_hnr[sepref_fr_rules]: "(uncurry cnt_incr_impl, uncurry (PR_CONST cnt_incr)) \<in> cnt_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a cnt_assn"    
  apply sepref_to_hoare
  unfolding cnt_incr_def cnt_incr_impl_def cnt_assn_def
  by (sep_auto simp: refine_pw_simps) 
    
lemma cnt_decr_hnr[sepref_fr_rules]: "(uncurry cnt_decr_impl, uncurry (PR_CONST cnt_decr)) \<in> cnt_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a cnt_assn"    
  apply sepref_to_hoare
  unfolding cnt_decr_def cnt_decr_impl_def cnt_assn_def
  by (sep_auto simp: refine_pw_simps) 
  
    
subsubsection \<open>Combined Frequency Count and Labeling\<close>    
definition "clc_assn \<equiv> cnt_assn \<times>\<^sub>a l_assn"
    

sepref_thm clc_init_impl is "PR_CONST clc_init" :: "nat_assn\<^sup>k \<rightarrow>\<^sub>a clc_assn" 
  unfolding clc_init_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) clc_init_impl 
  uses Network_Impl.clc_init_impl.refine_raw
lemmas [sepref_fr_rules] = clc_init_impl.refine[OF Network_Impl_axioms]
    
sepref_thm clc_get_impl is "uncurry (PR_CONST clc_get)" 
  :: "clc_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn" 
  unfolding clc_get_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) clc_get_impl 
  uses Network_Impl.clc_get_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas [sepref_fr_rules] = clc_get_impl.refine[OF Network_Impl_axioms]
  
sepref_thm clc_get_rlx_impl is "uncurry (PR_CONST clc_get_rlx)" 
  :: "clc_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn" 
  unfolding clc_get_rlx_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) clc_get_rlx_impl 
  uses Network_Impl.clc_get_rlx_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas [sepref_fr_rules] = clc_get_rlx_impl.refine[OF Network_Impl_axioms]
  
  
sepref_thm clc_set_impl is "uncurry2 (PR_CONST clc_set)" 
  :: "clc_assn\<^sup>d *\<^sub>a node_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a clc_assn" 
  unfolding clc_set_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) clc_set_impl 
  uses Network_Impl.clc_set_impl.refine_raw is "(uncurry2 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = clc_set_impl.refine[OF Network_Impl_axioms]
  
sepref_thm clc_has_gap_impl is "uncurry (PR_CONST clc_has_gap)" 
  :: "clc_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a bool_assn" 
  unfolding clc_has_gap_def PR_CONST_def clc_assn_def
  by sepref  
concrete_definition (in -) clc_has_gap_impl 
  uses Network_Impl.clc_has_gap_impl.refine_raw is "(uncurry ?f,_)\<in>_"
lemmas [sepref_fr_rules] = clc_has_gap_impl.refine[OF Network_Impl_axioms]
    
    
subsubsection \<open>Push\<close>   

sepref_thm push_impl is "uncurry2 (PR_CONST push2)" 
  :: "x_assn\<^sup>d *\<^sub>a cf_assn\<^sup>d *\<^sub>a edge_assn\<^sup>k \<rightarrow>\<^sub>a (x_assn\<times>\<^sub>acf_assn)" 
  unfolding push2_def PR_CONST_def
  by sepref  
concrete_definition (in -) push_impl 
  uses Network_Impl.push_impl.refine_raw is "(uncurry2 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = push_impl.refine[OF Network_Impl_axioms]

subsubsection \<open>Relabel\<close>   
sepref_thm min_adj_label_impl is "uncurry3 (PR_CONST min_adj_label)" 
  :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a l_assn\<^sup>k *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn"  
  unfolding min_adj_label_def PR_CONST_def
  by sepref  
concrete_definition (in -) min_adj_label_impl 
  uses Network_Impl.min_adj_label_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = min_adj_label_impl.refine[OF Network_Impl_axioms]    
  

sepref_thm relabel_impl is "uncurry3 (PR_CONST relabel2)" 
  :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a l_assn\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a l_assn" 
  unfolding relabel2_def PR_CONST_def
  by sepref  
concrete_definition (in -) relabel_impl 
  uses Network_Impl.relabel_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = relabel_impl.refine[OF Network_Impl_axioms]
  
subsubsection \<open>Gap-Relabel\<close>   
  
sepref_thm gap_impl is "uncurry2 (PR_CONST gap2)" 
  :: "nat_assn\<^sup>k *\<^sub>a clc_assn\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a clc_assn" 
  unfolding gap2_def PR_CONST_def
  by sepref  
concrete_definition (in -) gap_impl 
  uses Network_Impl.gap_impl.refine_raw is "(uncurry2 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = gap_impl.refine[OF Network_Impl_axioms]

sepref_thm min_adj_label_clc_impl is "uncurry3 (PR_CONST min_adj_label_clc)" 
  :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a clc_assn\<^sup>k *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a nat_assn" 
  unfolding min_adj_label_clc_def PR_CONST_def clc_assn_def
  by sepref    
    
concrete_definition (in -) min_adj_label_clc_impl 
  uses Network_Impl.min_adj_label_clc_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = min_adj_label_clc_impl.refine[OF Network_Impl_axioms]
  
sepref_thm clc_relabel_impl is "uncurry3 (PR_CONST clc_relabel2)" 
    :: "am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a clc_assn\<^sup>d *\<^sub>a node_assn\<^sup>k \<rightarrow>\<^sub>a clc_assn" 
  unfolding clc_relabel2_def PR_CONST_def
  by sepref  
concrete_definition (in -) clc_relabel_impl 
  uses Network_Impl.clc_relabel_impl.refine_raw is "(uncurry3 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = clc_relabel_impl.refine[OF Network_Impl_axioms]
  
sepref_thm gap_relabel_impl is "uncurry4 (PR_CONST gap_relabel2)" 
    :: "nat_assn\<^sup>k *\<^sub>a am_assn\<^sup>k *\<^sub>a cf_assn\<^sup>k *\<^sub>a clc_assn\<^sup>d *\<^sub>a node_assn\<^sup>k 
      \<rightarrow>\<^sub>a clc_assn" 
  unfolding gap_relabel2_def PR_CONST_def
  by sepref  
concrete_definition (in -) gap_relabel_impl 
  uses Network_Impl.gap_relabel_impl.refine_raw is "(uncurry4 ?f,_)\<in>_"
lemmas [sepref_fr_rules] = gap_relabel_impl.refine[OF Network_Impl_axioms]
  
subsubsection \<open>Initialization\<close>  
sepref_thm pp_init_xcf2_impl is "(PR_CONST pp_init_xcf2)" 
    :: "am_assn\<^sup>k \<rightarrow>\<^sub>a x_assn \<times>\<^sub>a cf_assn" 
  unfolding pp_init_xcf2_def PR_CONST_def
  by sepref
concrete_definition (in -) pp_init_xcf2_impl 
  uses Network_Impl.pp_init_xcf2_impl.refine_raw is "(?f,_)\<in>_"
lemmas [sepref_fr_rules] = pp_init_xcf2_impl.refine[OF Network_Impl_axioms]
  
  
end \<comment> \<open>Network Implementation Locale\<close>  
  
  
  
  
end
