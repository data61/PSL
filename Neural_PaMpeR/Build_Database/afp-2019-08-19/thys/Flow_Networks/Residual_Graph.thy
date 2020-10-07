section \<open>Residual Graph\<close>
theory Residual_Graph
imports Network
begin
text \<open>
  In this theory, we define the residual graph.
  \<close>

subsection \<open>Definition\<close>
text \<open>The \<^emph>\<open>residual graph\<close> of a network and a flow indicates how much 
  flow can be effectively pushed along or reverse to a network edge,
  by increasing or decreasing the flow on that edge:\<close>
definition residualGraph :: "_ graph \<Rightarrow> _ flow \<Rightarrow> _ graph"
where "residualGraph c f \<equiv> \<lambda>(u, v).
  if (u, v) \<in> Graph.E c then
    c (u, v) - f (u, v)
  else if (v, u) \<in> Graph.E c then
    f (v, u)
  else
    0"

context Network begin
  
abbreviation "cf_of \<equiv> residualGraph c"
abbreviation "cfE_of f \<equiv> Graph.E (cf_of f)"

text \<open>The edges of the residual graph are either parallel or reverse 
  to the edges of the network.\<close>
lemma cfE_of_ss_invE: "cfE_of cf \<subseteq> E \<union> E\<inverse>"
  unfolding residualGraph_def Graph.E_def
  by auto
  
lemma cfE_of_ss_VxV: "cfE_of f \<subseteq> V\<times>V"
  unfolding V_def
  unfolding residualGraph_def Graph.E_def
  by auto  

lemma cfE_of_finite[simp, intro!]: "finite (cfE_of f)"
  using finite_subset[OF cfE_of_ss_VxV] by auto

lemma cf_no_self_loop: "(u,u)\<notin>cfE_of f"
proof
  assume a1: "(u, u) \<in> cfE_of f"
  have "(u, u) \<notin> E"
    using no_parallel_edge by blast
  then show False
    using a1 unfolding Graph.E_def residualGraph_def by fastforce
qed 
  
end
  
  
  
text \<open>Let's fix a network with a preflow @{term f} on it\<close>
context NPreflow
begin
  text \<open>We abbreviate the residual graph by @{term cf}.\<close>
  abbreviation "cf \<equiv> residualGraph c f"
  sublocale cf: Graph cf .
  lemmas cf_def = residualGraph_def[of c f]

subsection \<open>Properties\<close>

lemmas cfE_ss_invE = cfE_of_ss_invE[of f]  
(*lemma cfE_ss_invE: "Graph.E cf \<subseteq> E \<union> E\<inverse>"
  unfolding residualGraph_def Graph.E_def
  by auto*)

text \<open>The nodes of the residual graph are exactly the nodes of the network.\<close>
lemma resV_netV[simp]: "cf.V = V"
proof
  show "V \<subseteq> Graph.V cf"
  proof 
    fix u
    assume "u \<in> V"
    then obtain v where "(u, v) \<in> E \<or> (v, u) \<in> E" unfolding V_def by auto
    (* TODO: Use nifty new Isabelle2016 case-distinction features here! *)
    moreover {
      assume "(u, v) \<in> E"
      then have "(u, v) \<in> Graph.E cf \<or> (v, u) \<in> Graph.E cf"
      proof (cases)
        assume "f (u, v) = 0"
        then have "cf (u, v) = c (u, v)"
          unfolding residualGraph_def using \<open>(u, v) \<in> E\<close> by (auto simp:)
        then have "cf (u, v) \<noteq> 0" using \<open>(u, v) \<in> E\<close> unfolding E_def by auto
        thus ?thesis unfolding Graph.E_def by auto
      next
        assume "f (u, v) \<noteq> 0"
        then have "cf (v, u) = f (u, v)" unfolding residualGraph_def
          using \<open>(u, v) \<in> E\<close> no_parallel_edge by auto
        then have "cf (v, u) \<noteq> 0" using \<open>f (u, v) \<noteq> 0\<close> by auto
        thus ?thesis unfolding Graph.E_def by auto
      qed
    } moreover {
      assume "(v, u) \<in> E"
      then have "(v, u) \<in> Graph.E cf \<or> (u, v) \<in> Graph.E cf"
      proof (cases)
        assume "f (v, u) = 0"
        then have "cf (v, u) = c (v, u)"
          unfolding residualGraph_def using \<open>(v, u) \<in> E\<close> by (auto)
        then have "cf (v, u) \<noteq> 0" using \<open>(v, u) \<in> E\<close> unfolding E_def by auto
        thus ?thesis unfolding Graph.E_def by auto
      next
        assume "f (v, u) \<noteq> 0"
        then have "cf (u, v) = f (v, u)" unfolding residualGraph_def
          using \<open>(v, u) \<in> E\<close> no_parallel_edge by auto
        then have "cf (u, v) \<noteq> 0" using \<open>f (v, u) \<noteq> 0\<close> by auto
        thus ?thesis unfolding Graph.E_def by auto
      qed
    } ultimately show "u\<in>cf.V" unfolding cf.V_def by auto
  qed  
next
  show "Graph.V cf \<subseteq> V" using cfE_ss_invE unfolding Graph.V_def by auto
qed

text \<open>Note, that Isabelle is powerful enough to prove the above case 
  distinctions completely automatically, although it takes some time:\<close>
lemma "cf.V = V"
  unfolding residualGraph_def Graph.E_def Graph.V_def
  using no_parallel_edge[unfolded E_def]
  by auto
  
text \<open>As the residual graph has the same nodes as the network, it is also finite:\<close>
sublocale cf: Finite_Graph cf
  by unfold_locales auto

text \<open>The capacities on the edges of the residual graph are non-negative\<close>
lemma resE_nonNegative: "cf e \<ge> 0"
proof (cases e; simp)
  fix u v
  {
    assume "(u, v) \<in> E"
    then have "cf (u, v) = c (u, v) - f (u, v)" unfolding cf_def by auto
    hence "cf (u,v) \<ge> 0" 
      using capacity_const cap_non_negative by auto
  } moreover {
    assume "(v, u) \<in> E"
    then have "cf (u,v) = f (v, u)" 
      using no_parallel_edge unfolding cf_def by auto
    hence "cf (u,v) \<ge> 0" 
      using capacity_const by auto
  } moreover {
    assume "(u, v) \<notin> E" "(v, u) \<notin> E"
    hence "cf (u,v) \<ge> 0" unfolding residualGraph_def by simp
  } ultimately show "cf (u,v) \<ge> 0" by blast
qed

text \<open>Again, there is an automatic proof\<close>
lemma "cf e \<ge> 0"
  apply (cases e)
  unfolding residualGraph_def
  using no_parallel_edge capacity_const cap_positive
  by auto

text \<open>All edges of the residual graph are labeled with positive capacities:\<close>
corollary resE_positive: "e \<in> cf.E \<Longrightarrow> cf e > 0"
proof -
  assume "e \<in> cf.E"
  hence "cf e \<noteq> 0" unfolding cf.E_def by auto
  thus ?thesis using resE_nonNegative by (meson eq_iff not_le)
qed 
      
(* TODO: Only one usage: Move or remove! *)  
lemma reverse_flow: "Preflow cf s t f' \<Longrightarrow> \<forall>(u, v) \<in> E. f' (v, u) \<le> f (u, v)"
proof -
  assume asm: "Preflow cf s t f'"
  then interpret f': Preflow cf s t f' .
      
  {
    fix u v
    assume "(u, v) \<in> E"
    
    then have "cf (v, u) = f (u, v)"
      unfolding residualGraph_def using no_parallel_edge by auto
    moreover have "f' (v, u) \<le> cf (v, u)" using f'.capacity_const by auto
    ultimately have "f' (v, u) \<le> f (u, v)" by metis
  }
  thus ?thesis by auto
qed  

  
definition (in Network) "flow_of_cf cf e \<equiv> (if (e\<in>E) then c e - cf e else 0)"

(* TODO: We have proved/used this fact already for Edka-Analysis! (uE) *)  
lemma (in NPreflow) E_ss_cfinvE: "E \<subseteq> Graph.E cf \<union> (Graph.E cf)\<inverse>"
  unfolding residualGraph_def Graph.E_def
  apply (clarsimp)
  using no_parallel_edge (* Speed optimization: Adding this directly takes very long *)
  unfolding E_def
  apply (simp add: )
  done
  
  
text \<open>Nodes with positive excess must have an outgoing edge in the 
  residual graph. 

  Intuitively: The excess flow must come from somewhere.\<close>
lemma active_has_cf_outgoing: "excess f u > 0 \<Longrightarrow> cf.outgoing u \<noteq> {}"  
  unfolding excess_def
proof -
  assume "0 < sum f (incoming u) - sum f (outgoing u)"
  hence "0 < sum f (incoming u)"
    by (metis diff_gt_0_iff_gt linorder_neqE_linordered_idom linorder_not_le 
        sum_f_non_negative)
  with f_non_negative obtain e where "e\<in>incoming u" "f e > 0"
    by (meson not_le sum_nonpos)
  then obtain v where "(v,u)\<in>E" "f (v,u) > 0" unfolding incoming_def by auto
  hence "cf (u,v) > 0" unfolding residualGraph_def by auto
  thus ?thesis unfolding cf.outgoing_def cf.E_def by fastforce   
qed      
    
    
    
end \<comment> \<open>Network with preflow\<close>
  
  
locale RPreGraph \<comment> \<open>Locale that characterizes a residual graph of a network\<close>
= Network +
  fixes cf
  assumes EX_RPG: "\<exists>f. NPreflow c s t f \<and> cf = residualGraph c f"
begin  

  lemma this_loc_rpg: "RPreGraph c s t cf"
    by unfold_locales

  definition "f \<equiv> flow_of_cf cf"

  lemma f_unique:
    assumes "NPreflow c s t f'"
    assumes A: "cf = residualGraph c f'"
    shows "f' = f"
  proof -
    interpret f': NPreflow c s t f' by fact
    
    show ?thesis
      unfolding f_def[abs_def] flow_of_cf_def[abs_def]
      unfolding A residualGraph_def
      apply (rule ext)
      using f'.capacity_const unfolding E_def
      apply (auto split: prod.split)
      by (metis antisym)
  qed

  lemma is_NPreflow: "NPreflow c s t (flow_of_cf cf)"
    apply (fold f_def)
    using EX_RPG f_unique by metis
    
  sublocale f: NPreflow c s t f unfolding f_def by (rule is_NPreflow)

  lemma rg_is_cf[simp]: "residualGraph c f = cf"
    using EX_RPG f_unique by auto

  lemma rg_fo_inv[simp]: "residualGraph c (flow_of_cf cf) = cf"  
    using rg_is_cf
    unfolding f_def
    .
    

  sublocale cf: Graph cf .

  lemma resV_netV[simp]: "cf.V = V"
    using f.resV_netV by simp

  sublocale cf: Finite_Graph cf 
    apply unfold_locales
    apply simp
    done

  lemma E_ss_cfinvE: "E \<subseteq> cf.E \<union> cf.E\<inverse>"  
    using f.E_ss_cfinvE by simp

  lemma cfE_ss_invE: "cf.E \<subseteq> E \<union> E\<inverse>"
    using f.cfE_ss_invE by simp
    
  lemma resE_nonNegative: "cf e \<ge> 0"  
    using f.resE_nonNegative by auto
      
end

context NPreflow begin
  lemma is_RPreGraph: "RPreGraph c s t cf"
    apply unfold_locales
    apply (rule exI[where x=f])
    apply (safe; unfold_locales)
    done

  lemma fo_rg_inv: "flow_of_cf cf = f"  
    unfolding flow_of_cf_def[abs_def]
    unfolding residualGraph_def
    apply (rule ext)
    using capacity_const unfolding E_def
    apply (clarsimp split: prod.split)
    by (metis antisym)

end    

(* For snippet*)
lemma (in NPreflow)
  "flow_of_cf (residualGraph c f) = f"
  by (rule fo_rg_inv)


locale RGraph \<comment> \<open>Locale that characterizes a residual graph of a network\<close>
= Network +
  fixes cf
  assumes EX_RG: "\<exists>f. NFlow c s t f \<and> cf = residualGraph c f"
begin  
  sublocale RPreGraph 
  proof    
    from EX_RG obtain f where 
      "NFlow c s t f" and [simp]: "cf = residualGraph c f" by auto
    then interpret NFlow c s t f by simp    

    show "\<exists>f. NPreflow c s t f \<and> cf = residualGraph c f"
      apply (rule exI[where x="f"])
      apply simp
      by unfold_locales  
  qed  

  lemma this_loc: "RGraph c s t cf"
    by unfold_locales
  lemma this_loc_rpg: "RPreGraph c s t cf"
    by unfold_locales
    
  lemma is_NFlow: "NFlow c s t (flow_of_cf cf)"
    using EX_RG f_unique is_NPreflow NFlow.axioms(1)
    apply (fold f_def) by force  
    
  sublocale f: NFlow c s t f unfolding f_def by (rule is_NFlow)
end        
      
context NFlow begin

lemma is_RGraph: "RGraph c s t cf"
  apply unfold_locales
  apply (rule exI[where x=f])
  apply (safe; unfold_locales)
  done
      
text \<open>The value of the flow can be computed from the residual graph.\<close>
lemma val_by_cf: "val = (\<Sum>(u,v)\<in>outgoing s. cf (v,u))"
proof -
  have "f (s,v) = cf (v,s)" for v
    unfolding cf_def by auto
  thus ?thesis 
    unfolding val_alt outgoing_def 
    by (auto intro!: sum.cong) 
qed  
      
end \<comment> \<open>Network with Flow\<close>

lemma (in RPreGraph) maxflow_imp_rgraph:
  assumes "isMaxFlow (flow_of_cf cf)"
  shows "RGraph c s t cf"
proof -  
  from assms interpret Flow c s t f 
    unfolding isMaxFlow_def by (simp add: f_def)
 
  interpret NFlow c s t f by unfold_locales     
  
  show ?thesis    
    apply unfold_locales
    apply (rule exI[of _ f])
    apply (simp add: NFlow_axioms)  
    done  
qed      
  
end \<comment> \<open>Theory\<close>
