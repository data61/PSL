section \<open>Breadth First Search\<close>
theory Augmenting_Path_BFS
imports 
  Flow_Networks.Refine_Add_Fofu
  Flow_Networks.Graph_Impl
begin
  text \<open>
    In this theory, we present a verified breadth-first search
    with an efficient imperative implementation.
    It is parametric in the successor function.
    \<close>

  subsection \<open>Algorithm\<close>
  locale pre_bfs_invar = Graph +    
    fixes src dst :: node
  begin  

    abbreviation "ndist v \<equiv> min_dist src v"

    definition Vd :: "nat \<Rightarrow> node set"
    where
      "\<And>d. Vd d \<equiv> {v. connected src v \<and> ndist v = d}"

    lemma Vd_disj: "\<And>d d'. d\<noteq>d' \<Longrightarrow> Vd d \<inter> Vd d' = {}"  
      by (auto simp: Vd_def)

    lemma src_Vd0[simp]: "Vd 0 = {src}"  
      by (auto simp: Vd_def)

    lemma in_Vd_conv: "v\<in>Vd d \<longleftrightarrow> connected src v \<and> ndist v = d"
      by (auto simp: Vd_def)

    lemma Vd_succ: 
      assumes "u\<in>Vd d"  
      assumes "(u,v)\<in>E"
      assumes "\<forall>i\<le>d. v\<notin>Vd i"
      shows "v\<in>Vd (Suc d)"
      using assms
      by (metis connected_append_edge in_Vd_conv le_SucE min_dist_succ)

  end

  locale valid_PRED = pre_bfs_invar +
    fixes PRED :: "node \<rightharpoonup> node"
    assumes SRC_IN_V[simp]: "src\<in>V"
    assumes FIN_V[simp, intro!]: "finite V"
    assumes PRED_src[simp]: "PRED src = Some src"
    assumes PRED_dist: "\<lbrakk>v\<noteq>src; PRED v = Some u\<rbrakk> \<Longrightarrow> ndist v = Suc (ndist u)"
    assumes PRED_E: "\<lbrakk>v\<noteq>src; PRED v = Some u\<rbrakk> \<Longrightarrow> (u,v)\<in>E"
    assumes PRED_closed: "\<lbrakk> PRED v = Some u \<rbrakk> \<Longrightarrow> u\<in>dom PRED"
  begin
    lemma FIN_E[simp, intro!]: "finite E" using E_ss_VxV by simp
    lemma FIN_succ[simp, intro!]: "finite (E``{u})" 
      by (auto intro: finite_Image)
  end  
    
  locale nf_invar' = valid_PRED c src dst PRED for c src dst 
    and PRED :: "node \<rightharpoonup> node"
    and C N :: "node set"
    and d :: nat 
    +
    assumes VIS_eq: "dom PRED = N \<union> {u. \<exists>i\<le>d. u\<in>Vd i}"
    assumes C_ss: "C \<subseteq> Vd d"
    assumes N_eq: "N = Vd (d+1) \<inter> E``(Vd d - C)"
      
    assumes dst_ne_VIS: "dst \<notin> dom PRED"

  locale nf_invar = nf_invar' +   
    assumes empty_assm: "C={} \<Longrightarrow> N={}"

  locale f_invar = valid_PRED c src dst PRED for c src dst 
    and PRED :: "node \<rightharpoonup> node"
    and d :: nat   
    + 
    assumes dst_found: "dst \<in> dom PRED \<inter> Vd d"

  context Graph begin

    abbreviation "outer_loop_invar src dst \<equiv> \<lambda>(f,PRED,C,N,d). 
      (f \<longrightarrow> f_invar c src dst PRED d) \<and>
      (\<not>f \<longrightarrow> nf_invar c src dst PRED C N d)

      "
    abbreviation "assn1 src dst \<equiv> \<lambda>(f,PRED,C,N,d). 
      \<not>f \<and> nf_invar' c src dst PRED C N d"

  definition "add_succ_spec dst succ v PRED N \<equiv> ASSERT (N \<subseteq> dom PRED) \<then> 
    SPEC (\<lambda>(f,PRED',N').
      case f of
        False \<Rightarrow> dst \<notin> succ - dom PRED 
          \<and> PRED' = map_mmupd PRED (succ - dom PRED) v 
          \<and> N' = N \<union> (succ - dom PRED)
      | True \<Rightarrow> dst \<in> succ - dom PRED 
        \<and> PRED \<subseteq>\<^sub>m PRED' 
        \<and> PRED' \<subseteq>\<^sub>m map_mmupd PRED (succ - dom PRED) v 
        \<and> dst\<in>dom PRED'
  )"

  definition pre_bfs :: "node \<Rightarrow> node \<Rightarrow> (nat \<times> (node\<rightharpoonup>node)) option nres"
    where "pre_bfs src dst \<equiv> do {
    (f,PRED,_,_,d) \<leftarrow> WHILEIT (outer_loop_invar src dst) 
      (\<lambda>(f,PRED,C,N,d). f=False \<and> C\<noteq>{})
      (\<lambda>(f,PRED,C,N,d). do {
        v \<leftarrow> SPEC (\<lambda>v. v\<in>C); let C = C-{v};
        ASSERT (v\<in>V);
        let succ = (E``{v});
        ASSERT (finite succ);
        (f,PRED,N) \<leftarrow> add_succ_spec dst succ v PRED N;
        if f then
          RETURN (f,PRED,C,N,d+1)
        else do {
          ASSERT (assn1 src dst (f,PRED,C,N,d));
          if (C={}) then do {
            let C=N; 
            let N={}; 
            let d=d+1;
            RETURN (f,PRED,C,N,d)
          } else RETURN (f,PRED,C,N,d)
        }  
      })
      (False,[src\<mapsto>src],{src},{},0::nat);
    if f then RETURN (Some (d, PRED)) else RETURN None
    }"

  subsection "Correctness Proof"

  lemma (in nf_invar') ndist_C[simp]: "\<lbrakk>v\<in>C\<rbrakk> \<Longrightarrow> ndist v = d"  
    using C_ss by (auto simp: Vd_def)
  lemma (in nf_invar) CVdI: "\<lbrakk>u\<in>C\<rbrakk> \<Longrightarrow> u\<in>Vd d"
    using C_ss by (auto)

  lemma (in nf_invar) inPREDD: 
    "\<lbrakk>PRED v = Some u\<rbrakk> \<Longrightarrow> v\<in>N \<or> (\<exists>i\<le>d. v\<in>Vd i)"   
    using VIS_eq by (auto)

  lemma (in nf_invar') C_ss_VIS: "\<lbrakk>v\<in>C\<rbrakk> \<Longrightarrow> v\<in>dom PRED"
    using C_ss VIS_eq by blast  

  lemma (in nf_invar) invar_succ_step:
    assumes "v\<in>C"
    assumes "dst \<notin> E``{v} - dom PRED"
    shows "nf_invar' c src dst 
      (map_mmupd PRED (E``{v} - dom PRED) v) 
      (C-{v}) 
      (N \<union> (E``{v} - dom PRED)) 
      d"
  proof -
    from C_ss_VIS[OF \<open>v\<in>C\<close>] dst_ne_VIS have "v\<noteq>dst" by auto

    show ?thesis  
      using \<open>v\<in>C\<close> \<open>v\<noteq>dst\<close>
      apply unfold_locales
      apply simp
      apply simp
      apply (auto simp: map_mmupd_def) []
  
      apply (erule map_mmupdE)
      using PRED_dist apply blast
      apply (unfold VIS_eq) []
      apply clarify
      apply (metis CVdI Vd_succ in_Vd_conv)
  
      using PRED_E apply (auto elim!: map_mmupdE) []   
      using PRED_closed apply (auto elim!: map_mmupdE dest: C_ss_VIS) [] 
  
      using VIS_eq apply auto []
      using C_ss apply auto []
  
      apply (unfold N_eq) []
      apply (frule CVdI)
      apply (auto) []
      apply (erule (1) Vd_succ)
      using VIS_eq apply (auto) []
      apply (auto dest!: inPREDD simp: N_eq in_Vd_conv) []
  
      using dst_ne_VIS assms(2) apply auto []
      done
  qed  

  lemma invar_init: "\<lbrakk>src\<noteq>dst; src\<in>V; finite V\<rbrakk> 
    \<Longrightarrow> nf_invar c src dst [src \<mapsto> src] {src} {} 0"            
    apply unfold_locales
    apply (auto)
    apply (auto simp: pre_bfs_invar.Vd_def split: if_split_asm)
    done

  lemma (in nf_invar) invar_exit:
    assumes "dst\<in>C"
    shows "f_invar c src dst PRED d"  
    apply unfold_locales
    using assms VIS_eq C_ss by auto

  lemma (in nf_invar) invar_C_ss_V: "u\<in>C \<Longrightarrow> u\<in>V"  
    apply (drule CVdI)
    apply (auto simp: in_Vd_conv connected_inV_iff)
    done

  lemma (in nf_invar) invar_N_ss_Vis: "u\<in>N \<Longrightarrow> \<exists>v. PRED u = Some v"
    using VIS_eq by auto  
    
  lemma (in pre_bfs_invar) Vdsucinter_conv[simp]: 
    "Vd (Suc d) \<inter> E `` Vd d = Vd (Suc d)"
    apply (auto)
    by (metis Image_iff in_Vd_conv min_dist_suc)  

  lemma (in nf_invar') invar_shift:
    assumes [simp]: "C={}"
    shows "nf_invar c src dst PRED N {} (Suc d)"  
    apply unfold_locales
    apply vc_solve
    using VIS_eq N_eq[simplified] apply (auto simp add: le_Suc_eq) []
    using N_eq apply auto []
    using N_eq[simplified] apply auto []
    using dst_ne_VIS apply auto []
    done    

  lemma (in nf_invar') invar_restore:
    assumes [simp]: "C\<noteq>{}"
    shows "nf_invar c src dst PRED C N d"
    apply unfold_locales by auto

  definition "bfs_spec src dst r \<equiv> (
    case r of None \<Rightarrow> \<not> connected src dst
            | Some (d,PRED) \<Rightarrow> connected src dst 
                \<and> min_dist src dst = d 
                \<and> valid_PRED c src PRED 
                \<and> dst\<in>dom PRED)"

  lemma (in f_invar) invar_found:
    shows "bfs_spec src dst (Some (d,PRED))"
    unfolding bfs_spec_def
    apply simp
    using dst_found 
    apply (auto simp: in_Vd_conv)
    by unfold_locales

  lemma (in nf_invar) invar_not_found:
    assumes [simp]: "C={}"
    shows "bfs_spec src dst None"
    unfolding bfs_spec_def
    apply simp
  proof (rule notI)
    have [simp]: "N={}" using empty_assm by simp

    assume C: "connected src dst"
    then obtain d' where dstd': "dst \<in> Vd d'"
      by (auto simp: in_Vd_conv)

    txt \<open>We make a case-distinction whether \<open>d'\<le>d\<close>:\<close>
    have "d'\<le>d \<or> Suc d \<le> d'" by auto  
    moreover {
      assume "d'\<le>d"
      with VIS_eq dstd' have "dst \<in> dom PRED" by auto
      with dst_ne_VIS have False by auto
    } moreover {
      assume "Suc d \<le> d'"
      txt \<open>In the case \<open>d+1 \<le> d'\<close>, we also obtain a node
        that has a shortest path of length \<open>d+1\<close>:\<close>
      with min_dist_le[OF C] dstd' obtain v' where "v' \<in> Vd (Suc d)"
        by (auto simp: in_Vd_conv)
      txt \<open>However, the invariant states that such nodes are either in
        \<open>N\<close> or are successors of \<open>C\<close>. As \<open>N\<close> 
        and \<open>C\<close> are both empty, we again get a contradiction.\<close>
      with N_eq have False by auto  
    } ultimately show False by blast
  qed

  lemma map_le_mp: "\<lbrakk>m\<subseteq>\<^sub>mm'; m k = Some v\<rbrakk> \<Longrightarrow> m' k = Some v"
    by (force simp: map_le_def)

  lemma (in nf_invar) dst_notin_Vdd[intro, simp]: "i\<le>d \<Longrightarrow> dst\<notin>Vd i"
    using VIS_eq dst_ne_VIS by auto 

  lemma (in nf_invar) invar_exit':
    assumes "u\<in>C" "(u,dst) \<in> E" "dst \<in> dom PRED'"
    assumes SS1: "PRED \<subseteq>\<^sub>m PRED'" 
      and SS2: "PRED' \<subseteq>\<^sub>m map_mmupd PRED (E``{u} - dom PRED) u"
    shows "f_invar c src dst PRED' (Suc d)"
    apply unfold_locales
    apply simp_all

    using map_le_mp[OF SS1 PRED_src] apply simp

    apply (drule map_le_mp[OF SS2])
    apply (erule map_mmupdE)
    using PRED_dist apply auto []
    apply (unfold VIS_eq) []
    apply clarify
    using \<open>u\<in>C\<close>
    apply (metis CVdI Vd_succ in_Vd_conv)

    apply (drule map_le_mp[OF SS2])
    using PRED_E apply (auto elim!: map_mmupdE) []   
    
    apply (drule map_le_mp[OF SS2])
    apply (erule map_mmupdE)
    using map_le_implies_dom_le[OF SS1]
    using PRED_closed apply (blast) []
    using C_ss_VIS[OF \<open>u\<in>C\<close>] map_le_implies_dom_le[OF SS1] apply blast
    using \<open>dst \<in> dom PRED'\<close> apply simp

    using \<open>u\<in>C\<close> CVdI[OF \<open>u\<in>C\<close>] \<open>(u,dst)\<in>E\<close>
    apply (auto) []
    apply (erule (1) Vd_succ)
    using VIS_eq apply (auto) []
    done



  definition "max_dist src \<equiv> Max (min_dist src`V)"

  definition "outer_loop_rel src \<equiv> 
    inv_image (
        less_than_bool 
        <*lex*> greater_bounded (max_dist src + 1) 
        <*lex*> finite_psubset) 
      (\<lambda>(f,PRED,C,N,d). (\<not>f,d,C))"
  lemma outer_loop_rel_wf: 
    assumes "finite V"
    shows "wf (outer_loop_rel src)"
    using assms
    unfolding outer_loop_rel_def
    by auto

  lemma (in nf_invar) C_ne_max_dist:
    assumes "C\<noteq>{}"
    shows "d \<le> max_dist src"
  proof -
    from assms obtain u where "u\<in>C" by auto
    with C_ss have "u\<in>Vd d" by auto
    hence "min_dist src u = d" "u\<in>V" 
      by (auto simp: in_Vd_conv connected_inV_iff)
    thus "d\<le>max_dist src" 
      unfolding max_dist_def by auto
  qed    

  lemma (in nf_invar) Vd_ss_V: "Vd d \<subseteq> V"
    by (auto simp: Vd_def connected_inV_iff)

  lemma (in nf_invar) finite_C[simp, intro!]: "finite C"
    using C_ss FIN_V Vd_ss_V by (blast intro: finite_subset)
  
  lemma (in nf_invar) finite_succ: "finite (E``{u})"  
    by auto

  theorem pre_bfs_correct: 
    assumes [simp]: "src\<in>V" "src\<noteq>dst"       
    assumes [simp]: "finite V"
    shows "pre_bfs src dst \<le> SPEC (bfs_spec src dst)"
    unfolding pre_bfs_def add_succ_spec_def
    apply (intro refine_vcg)
    apply (rule outer_loop_rel_wf[where src=src])
    apply (vc_solve simp:
      invar_init 
      nf_invar.invar_exit' 
      nf_invar.invar_C_ss_V 
      nf_invar.invar_succ_step
      nf_invar'.invar_shift
      nf_invar'.invar_restore        
      f_invar.invar_found
      nf_invar.invar_not_found
      nf_invar.invar_N_ss_Vis
      nf_invar.finite_succ
      )
    apply (vc_solve 
      simp: remove_subset outer_loop_rel_def 
      simp: nf_invar.C_ne_max_dist nf_invar.finite_C)
    done



  (* Presentation for Paper *)  
  definition bfs_core :: "node \<Rightarrow> node \<Rightarrow> (nat \<times> (node\<rightharpoonup>node)) option nres"
    where "bfs_core src dst \<equiv> do {
    (f,P,_,_,d) \<leftarrow> while\<^sub>T (\<lambda>(f,P,C,N,d). f=False \<and> C\<noteq>{})
      (\<lambda>(f,P,C,N,d). do {
        v \<leftarrow> spec v. v\<in>C; let C = C-{v};
        let succ = (E``{v});
        (f,P,N) \<leftarrow> add_succ_spec dst succ v P N;
        if f then
          return (f,P,C,N,d+1)
        else do {
          if (C={}) then do {
            let C=N; let N={}; let d=d+1;
            return (f,P,C,N,d)
          } else return (f,P,C,N,d)
        }  
      })
      (False,[src\<mapsto>src],{src},{},0::nat);
    if f then return (Some (d, P)) else return None
    }"

  theorem 
    assumes "src\<in>V" "src\<noteq>dst" "finite V"
    shows "bfs_core src dst \<le> (spec p. bfs_spec src dst p)"
    apply (rule order_trans[OF _ pre_bfs_correct])
    apply (rule refine_IdD)
    unfolding bfs_core_def pre_bfs_def
    apply refine_rcg
    apply refine_dref_type
    apply (vc_solve simp: assms)
    done


      
  subsection \<open>Extraction of Result Path\<close>

    definition "extract_rpath src dst PRED \<equiv> do {
      (_,p) \<leftarrow> WHILEIT
        (\<lambda>(v,p). 
          v\<in>dom PRED 
        \<and> isPath v p dst
        \<and> distinct (pathVertices v p)
        \<and> (\<forall>v'\<in>set (pathVertices v p). 
            pre_bfs_invar.ndist c src v \<le> pre_bfs_invar.ndist c src v')
        \<and> pre_bfs_invar.ndist c src v + length p 
          = pre_bfs_invar.ndist c src dst)
        (\<lambda>(v,p). v\<noteq>src) (\<lambda>(v,p). do {
        ASSERT (v\<in>dom PRED);
        let u=the (PRED v);
        let p = (u,v)#p;
        let v=u;
        RETURN (v,p)
      }) (dst,[]);
      RETURN p
    }"

  end  

  context valid_PRED begin
    lemma extract_rpath_correct:
      assumes "dst\<in>dom PRED"
      shows "extract_rpath src dst PRED 
        \<le> SPEC (\<lambda>p. isSimplePath src p dst \<and> length p = ndist dst)"
      using assms unfolding extract_rpath_def isSimplePath_def
      apply (refine_vcg wf_measure[where f="\<lambda>(d,_). ndist d"])
      apply (vc_solve simp: PRED_closed[THEN domD] PRED_E PRED_dist)
      apply auto
      done

  end

  context Graph begin

    definition "bfs src dst \<equiv> do {
      if src=dst then RETURN (Some [])
      else do {
        br \<leftarrow> pre_bfs src dst;
        case br of
          None \<Rightarrow> RETURN None
        | Some (d,PRED) \<Rightarrow> do {
            p \<leftarrow> extract_rpath src dst PRED;
            RETURN (Some p)
          }  
      }    
    }"

    lemma bfs_correct:
      assumes "src\<in>V" "finite V" 
      shows "bfs src dst 
        \<le> SPEC (\<lambda>
          None \<Rightarrow> \<not>connected src dst 
        | Some p \<Rightarrow> isShortestPath src p dst)"
      unfolding bfs_def
      apply (refine_vcg
        pre_bfs_correct[THEN order_trans]
        valid_PRED.extract_rpath_correct[THEN order_trans]
        )
      using assms
      apply (vc_solve 
        simp: bfs_spec_def isShortestPath_min_dist_def isSimplePath_def)
      done      
  end

  (* Snippet for paper *)  
  context Finite_Graph begin
    interpretation Refine_Monadic_Syntax .
    theorem
      assumes "src\<in>V" 
      shows "bfs src dst \<le> (spec p. case p of 
          None \<Rightarrow> \<not>connected src dst 
        | Some p \<Rightarrow> isShortestPath src p dst)"
      unfolding bfs_def
      apply (refine_vcg
        pre_bfs_correct[THEN order_trans]
        valid_PRED.extract_rpath_correct[THEN order_trans]
        )
      using assms
      apply (vc_solve 
        simp: bfs_spec_def isShortestPath_min_dist_def isSimplePath_def)
      done      

  end  

  subsection \<open>Inserting inner Loop and Successor Function\<close>
  context Graph begin

  definition "inner_loop dst succ u PRED N \<equiv> FOREACHci
    (\<lambda>it (f,PRED',N'). 
        PRED' = map_mmupd PRED ((succ - it) - dom PRED) u 
      \<and> N' = N \<union> ((succ - it) - dom PRED)
      \<and> f = (dst\<in>(succ - it) - dom PRED)
    )
    (succ)
    (\<lambda>(f,PRED,N). \<not>f)
    (\<lambda>v (f,PRED,N). do {
      if v\<in>dom PRED then RETURN (f,PRED,N)
      else do {
        let PRED = PRED(v \<mapsto> u);
        ASSERT (v\<notin>N);
        let N = insert v N;
        RETURN (v=dst,PRED,N)
      }
    }) 
    (False,PRED,N)"


  lemma inner_loop_refine[refine]: 
    (*assumes NSS: "N \<subseteq> dom PRED"*)
    assumes [simp]: "finite succ"
    assumes [simplified, simp]: 
      "(succi,succ)\<in>Id" "(ui,u)\<in>Id" "(PREDi,PRED)\<in>Id" "(Ni,N)\<in>Id"
    shows "inner_loop dst succi ui PREDi Ni 
      \<le> \<Down>Id (add_succ_spec dst succ u PRED N)"
    unfolding inner_loop_def add_succ_spec_def
    apply refine_vcg
    apply (auto simp: it_step_insert_iff; fail) +
    apply (auto simp: it_step_insert_iff fun_neq_ext_iff map_mmupd_def 
      split: if_split_asm) []
    apply (auto simp: it_step_insert_iff split: bool.split; fail)
    apply (auto simp: it_step_insert_iff split: bool.split; fail)
    apply (auto simp: it_step_insert_iff split: bool.split; fail)
    apply (auto simp: it_step_insert_iff intro: map_mmupd_update_less 
      split: bool.split; fail)
    done


  definition "inner_loop2 dst succl u PRED N \<equiv> nfoldli
    (succl) (\<lambda>(f,_,_). \<not>f) (\<lambda>v (f,PRED,N). do {
    if PRED v \<noteq> None then RETURN (f,PRED,N)
    else do {
      let PRED = PRED(v \<mapsto> u);
      ASSERT (v\<notin>N);
      let N = insert v N;
      RETURN ((v=dst),PRED,N)
    }
  }) (False,PRED,N)"

  lemma inner_loop2_refine:
    assumes SR: "(succl,succ)\<in>\<langle>Id\<rangle>list_set_rel"
    shows "inner_loop2 dst succl u PRED N \<le> \<Down>Id (inner_loop dst succ u PRED N)"
    using assms
    unfolding inner_loop2_def inner_loop_def
    apply (refine_rcg LFOci_refine SR)
    apply (vc_solve)
    apply auto
    done

  thm conc_trans[OF inner_loop2_refine inner_loop_refine, no_vars]

  lemma inner_loop2_correct:
    assumes "(succl, succ) \<in> \<langle>Id\<rangle>list_set_rel"
    (*assumes "N \<subseteq> dom PRED"*)
    assumes [simplified, simp]: 
      "(dsti,dst)\<in>Id" "(ui, u) \<in> Id" "(PREDi, PRED) \<in> Id" "(Ni, N) \<in> Id"
    shows "inner_loop2 dsti succl ui PREDi Ni 
      \<le> \<Down> Id (add_succ_spec dst succ u PRED N)"
    apply simp
    apply (rule conc_trans[OF inner_loop2_refine inner_loop_refine, simplified])
    using assms(1-2)
    apply (simp_all)
    done


  type_synonym bfs_state = "bool \<times> (node \<rightharpoonup> node) \<times> node set \<times> node set \<times> nat"  

    context
      fixes succ :: "node \<Rightarrow> node list nres"
    begin
      definition init_state :: "node \<Rightarrow> bfs_state nres"
      where 
        "init_state src \<equiv> RETURN (False,[src\<mapsto>src],{src},{},0::nat)"
  
      definition pre_bfs2 :: "node \<Rightarrow> node \<Rightarrow> (nat \<times> (node\<rightharpoonup>node)) option nres"
        where "pre_bfs2 src dst \<equiv> do {
        s \<leftarrow> init_state src;
        (f,PRED,_,_,d) \<leftarrow> WHILET (\<lambda>(f,PRED,C,N,d). f=False \<and> C\<noteq>{})
          (\<lambda>(f,PRED,C,N,d). do {
            ASSERT (C\<noteq>{});
            v \<leftarrow> op_set_pick C; let C = C-{v};
            ASSERT (v\<in>V);
            sl \<leftarrow> succ v;
            (f,PRED,N) \<leftarrow> inner_loop2 dst sl v PRED N;
            if f then
              RETURN (f,PRED,C,N,d+1)
            else do {
              ASSERT (assn1 src dst (f,PRED,C,N,d));
              if (C={}) then do {
                let C=N; 
                let N={}; 
                let d=d+1;
                RETURN (f,PRED,C,N,d)
              } else RETURN (f,PRED,C,N,d)
            }  
          })
          s;
        if f then RETURN (Some (d, PRED)) else RETURN None
        }"
    
      lemma pre_bfs2_refine: 
        assumes succ_impl: "\<And>ui u. \<lbrakk>(ui,u)\<in>Id; u\<in>V\<rbrakk> 
          \<Longrightarrow> succ ui \<le> SPEC (\<lambda>l. (l,E``{u}) \<in> \<langle>Id\<rangle>list_set_rel)"
        shows "pre_bfs2 src dst \<le>\<Down>Id (pre_bfs src dst)"
        unfolding pre_bfs_def pre_bfs2_def init_state_def
        apply (subst nres_monad1)
        apply (refine_rcg inner_loop2_correct succ_impl)
        apply refine_dref_type
        apply vc_solve (* Takes some time *)
        done
  
    end    
  
    definition "bfs2 succ src dst \<equiv> do {
      if src=dst then 
        RETURN (Some [])
      else do {  
        br \<leftarrow> pre_bfs2 succ src dst;
        case br of
          None \<Rightarrow> RETURN None
        | Some (d,PRED) \<Rightarrow> do {
            p \<leftarrow> extract_rpath src dst PRED;
            RETURN (Some p)
          }  
      }    
    }"

    lemma bfs2_refine:
      assumes succ_impl: "\<And>ui u. \<lbrakk>(ui,u)\<in>Id; u\<in>V\<rbrakk> 
        \<Longrightarrow> succ ui \<le> SPEC (\<lambda>l. (l,E``{u}) \<in> \<langle>Id\<rangle>list_set_rel)"
      shows "bfs2 succ src dst \<le> \<Down>Id (bfs src dst)"
      unfolding bfs_def bfs2_def
      apply (refine_vcg pre_bfs2_refine)
      apply refine_dref_type
      using assms
      apply (vc_solve)
      done      

  end  

  
  lemma bfs2_refine_succ: 
    assumes [refine]: "\<And>ui u. \<lbrakk>(ui,u)\<in>Id; u\<in>Graph.V c\<rbrakk> 
      \<Longrightarrow> succi ui \<le> \<Down>Id (succ u)"
    assumes [simplified, simp]: "(si,s)\<in>Id" "(ti,t)\<in>Id" "(ci,c)\<in>Id"
    shows "Graph.bfs2 ci succi si ti \<le> \<Down>Id (Graph.bfs2 c succ s t)"
    unfolding Graph.bfs2_def Graph.pre_bfs2_def
    apply (refine_rcg 
      param_nfoldli[param_fo, THEN nres_relD] nres_relI fun_relI)
    apply refine_dref_type
    apply vc_solve
    done

subsection \<open>Imperative Implementation\<close>

  context Impl_Succ begin
    definition op_bfs :: "'ga \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nres" 
      where [simp]: "op_bfs c s t \<equiv> Graph.bfs2 (absG c) (succ c) s t"
  
    lemma pat_op_dfs[pat_rules]: 
      "Graph.bfs2$(absG$c)$(succ$c)$s$t \<equiv> UNPROTECT op_bfs$c$s$t" by simp 
  
    sepref_register "PR_CONST op_bfs" 
      :: "'ig \<Rightarrow> node \<Rightarrow> node \<Rightarrow> path option nres"  
  
    type_synonym ibfs_state 
      = "bool \<times> (node,node) i_map \<times> node set \<times> node set \<times> nat"

    sepref_register Graph.init_state :: "node \<Rightarrow> ibfs_state nres"
    schematic_goal init_state_impl:
      fixes src :: nat
      notes [id_rules] = 
        itypeI[Pure.of src "TYPE(nat)"]
      shows "hn_refine (hn_val nat_rel src srci) 
        (?c::?'c Heap) ?\<Gamma>' ?R (Graph.init_state src)"
      using [[id_debug, goals_limit = 1]]
      unfolding Graph.init_state_def
      apply (rewrite in "[src\<mapsto>src]" iam.fold_custom_empty)
      apply (subst ls.fold_custom_empty)
      apply (subst ls.fold_custom_empty)
      apply (rewrite in "insert src _" fold_set_insert_dj)
      apply (rewrite in "_(\<hole>\<mapsto>src)" fold_COPY)
      apply sepref
      done
    concrete_definition (in -) init_state_impl uses Impl_Succ.init_state_impl
    lemmas [sepref_fr_rules] = init_state_impl.refine[OF this_loc,to_hfref]

    schematic_goal bfs_impl:
      (*notes [sepref_opt_simps del] = imp_nfoldli_def 
          -- \<open>Prevent the foreach-loop to be unfolded to a fixed-point, 
              to produce more readable code for presentation purposes.\<close>*)
      notes [sepref_opt_simps] = heap_WHILET_def
      fixes s t :: nat
      notes [id_rules] = 
        itypeI[Pure.of s "TYPE(nat)"]
        itypeI[Pure.of t "TYPE(nat)"]
        itypeI[Pure.of c "TYPE('ig)"]
        \<comment> \<open>Declare parameters to operation identification\<close>
      shows "hn_refine (
        hn_ctxt (isG) c ci 
      * hn_val nat_rel s si 
      * hn_val nat_rel t ti) (?c::?'c Heap) ?\<Gamma>' ?R (PR_CONST op_bfs c s t)"
      unfolding op_bfs_def PR_CONST_def
      unfolding Graph.bfs2_def Graph.pre_bfs2_def 
        Graph.inner_loop2_def Graph.extract_rpath_def
      unfolding nres_monad_laws  
      apply (rewrite in "nfoldli _ _ \<hole> _" fold_set_insert_dj)
      apply (subst HOL_list.fold_custom_empty)+
      apply (rewrite in "let N={} in _" ls.fold_custom_empty)
      using [[id_debug, goals_limit = 1]]
      apply sepref
      done
    
    concrete_definition (in -) bfs_impl uses Impl_Succ.bfs_impl
      \<comment> \<open>Extract generated implementation into constant\<close>
    prepare_code_thms (in -) bfs_impl_def
   
    lemmas bfs_impl_fr_rule = bfs_impl.refine[OF this_loc,to_hfref]  
  
  end

  export_code bfs_impl checking SML_imp

end
