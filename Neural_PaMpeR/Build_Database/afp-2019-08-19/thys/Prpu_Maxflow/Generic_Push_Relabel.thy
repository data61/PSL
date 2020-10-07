section \<open>Generic Push Relabel Algorithm\<close>
theory Generic_Push_Relabel
imports 
  Flow_Networks.Fofu_Abs_Base
  Flow_Networks.Ford_Fulkerson
begin

  
  
subsection \<open>Labeling\<close>
 
text \<open>The central idea of the push-relabel algorithm is to add natural number
  labels \<open>l : node \<Rightarrow> nat\<close> to each node, and maintain the invariant that for 
  all edges \<open>(u,v)\<close> in the residual graph, we have \<open>l u \<le> l v + 1\<close>.\<close>

type_synonym labeling = "node \<Rightarrow> nat"
  
locale Labeling = NPreflow +
  fixes l :: labeling
  assumes valid: "(u,v) \<in> cf.E \<Longrightarrow> l(u) \<le> l(v) + 1"
  assumes lab_src[simp]: "l s = card V"
  assumes lab_sink[simp]: "l t = 0"
begin
text \<open>Generalizing validity to paths\<close>
lemma gen_valid: "l(u) \<le> l(x) + length p" if "cf.isPath u p x"
  using that by (induction p arbitrary: u; fastforce dest: valid)

text \<open>
  In a valid labeling, there cannot be an augmenting path~\cormen{26.17}.

  The proof works by contradiction, using the validity constraint 
  to show that any augmenting path would be too long for a simple path.
\<close>
theorem no_augmenting_path: "\<not>isAugmentingPath p"
proof
  assume "isAugmentingPath p"  
  hence SP: "cf.isSimplePath s p t" unfolding isAugmentingPath_def .
  hence "cf.isPath s p t" unfolding cf.isSimplePath_def by auto
  from gen_valid[OF this] have "length p \<ge> card V" by auto
  with cf.simplePath_length_less_V[OF _ SP] show False by auto 
qed

text \<open>
  The idea of push relabel algorithms is to maintain a valid labeling,
  and, ultimately, arrive at a valid flow, i.e., no nodes have excess flow. 
  We then immediately get that the flow is maximal:
\<close>  
corollary no_excess_imp_maxflow:    
  assumes "\<forall>u\<in>V-{s,t}. excess f u = 0"
  shows "isMaxFlow f"  
proof -    
  from assms interpret NFlow 
    apply unfold_locales 
    using no_deficient_nodes unfolding excess_def by auto
  from noAugPath_iff_maxFlow no_augmenting_path show "isMaxFlow f" by auto
qed
  
end \<comment> \<open>Labeling\<close>
    
subsection \<open>Basic Operations\<close>    
text \<open>
  The operations of the push relabel algorithm are local operations on 
  single nodes and edges.  
\<close>

subsubsection \<open>Augmentation of Edges\<close>
context Network
begin
  
text \<open>We define a function to augment a single edge in the residual graph.\<close>
  
definition augment_edge :: "'capacity flow \<Rightarrow> _" 
  where "augment_edge f \<equiv> \<lambda>(u,v) \<Delta>. 
    if (u,v)\<in>E then f( (u,v) := f (u,v) + \<Delta> )
    else if (v,u)\<in>E then f( (v,u) := f (v,u) - \<Delta> )
    else f"
  
lemma augment_edge_zero[simp]: "augment_edge f e 0 = f" 
  unfolding augment_edge_def by (auto split: prod.split) 
    
lemma augment_edge_same[simp]: "e\<in>E \<Longrightarrow> augment_edge f e \<Delta> e = f e + \<Delta>"
  unfolding augment_edge_def by (auto split!: prod.splits)
    
lemma augment_edge_other[simp]:"\<lbrakk>e\<in>E; e'\<noteq>e \<rbrakk> \<Longrightarrow> augment_edge f e \<Delta> e' = f e'"    
  unfolding augment_edge_def by (auto split!: prod.splits)

lemma augment_edge_rev_same[simp]: 
  "(v,u)\<in>E \<Longrightarrow> augment_edge f (u,v) \<Delta> (v,u) = f (v,u) - \<Delta>"    
  using no_parallel_edge
  unfolding augment_edge_def by (auto split!: prod.splits)

lemma augment_edge_rev_other[simp]: 
  "\<lbrakk>(u,v)\<notin>E; e'\<noteq>(v,u)\<rbrakk> \<Longrightarrow> augment_edge f (u,v) \<Delta> e' = f e'"    
  unfolding augment_edge_def by (auto split!: prod.splits)

lemma augment_edge_cf[simp]: "(u,v)\<in>E\<union>E\<inverse> \<Longrightarrow> 
    cf_of (augment_edge f (u,v) \<Delta>) 
  = (cf_of f)( (u,v) := cf_of f (u,v) - \<Delta>, (v,u) := cf_of f (v,u) + \<Delta>)"    
  apply (intro ext; cases "(u,v)\<in>E")
  subgoal for e' 
    apply (cases "e'=(u,v)")  
    subgoal by (simp split!: if_splits add: no_self_loop residualGraph_def)
    apply (cases "e'=(v,u)")  
    subgoal by (simp split!: if_splits add: no_parallel_edge residualGraph_def)
    subgoal by (simp 
                  split!: if_splits prod.splits 
                  add: residualGraph_def augment_edge_def)
    done
  subgoal for e'
    apply (cases "e'=(u,v)")  
    subgoal by (simp split!: if_splits add: no_self_loop residualGraph_def)
    apply (cases "e'=(v,u)")  
    subgoal by (simp split!: if_splits add: no_self_loop residualGraph_def)
    subgoal by (simp 
                  split!: if_splits prod.splits 
                  add: residualGraph_def augment_edge_def)
    done
  done
    
lemma augment_edge_cf': "(u,v)\<in>cfE_of f \<Longrightarrow> 
    cf_of (augment_edge f (u,v) \<Delta>) 
  = (cf_of f)( (u,v) := cf_of f (u,v) - \<Delta>, (v,u) := cf_of f (v,u) + \<Delta>)"    
proof -
  assume "(u,v)\<in>cfE_of f"
  hence "(u,v)\<in>E\<union>E\<inverse>" using cfE_of_ss_invE ..
  thus ?thesis by simp
qed      
  
text \<open>The effect of augmenting an edge on the residual graph\<close>  
definition (in -) augment_edge_cf :: "_ flow \<Rightarrow> _" where 
  "augment_edge_cf cf 
    \<equiv> \<lambda>(u,v) \<Delta>. (cf)( (u,v) := cf (u,v) - \<Delta>, (v,u) := cf (v,u) + \<Delta>)"
  
lemma cf_of_augment_edge:
  assumes A: "(u,v)\<in>cfE_of f" 
  shows "cf_of (augment_edge f (u,v) \<Delta>) = augment_edge_cf (cf_of f) (u,v) \<Delta>"  
proof -  
  show "cf_of (augment_edge f (u, v) \<Delta>) = augment_edge_cf (cf_of f) (u, v) \<Delta>"
    by (simp add: augment_edge_cf_def A augment_edge_cf')
qed      
  
  
  
lemma cfE_augment_ss:
  assumes EDGE: "(u,v)\<in>cfE_of f"  
  shows "cfE_of (augment_edge f (u,v) \<Delta>) \<subseteq> insert (v,u) (cfE_of f)"
  using EDGE  
  apply (clarsimp simp: augment_edge_cf')
  unfolding Graph.E_def  
  apply (auto split: if_splits)  
  done
  
  
end \<comment> \<open>Network\<close>  
  
context NPreflow begin  

text \<open>Augmenting an edge \<open>(u,v)\<close> with a flow \<open>\<Delta>\<close> that does not exceed the 
  available edge capacity, nor the available excess flow on the source node,
  preserves the preflow property.
\<close>  
lemma augment_edge_preflow_preserve: "\<lbrakk>0\<le>\<Delta>; \<Delta> \<le> cf (u,v); \<Delta> \<le> excess f u\<rbrakk> 
  \<Longrightarrow> Preflow c s t (augment_edge f (u,v) \<Delta>)"  
  apply unfold_locales
  subgoal
    unfolding residualGraph_def augment_edge_def  
    using capacity_const
    by (fastforce split!: if_splits)
  subgoal
  proof (intro ballI; clarsimp)
    assume "0\<le>\<Delta>" "\<Delta> \<le> cf (u,v)" "\<Delta> \<le> excess f u"
    fix v'
    assume V': "v'\<in>V" "v'\<noteq>s" "v'\<noteq>t"  
      
    show "sum (augment_edge f (u, v) \<Delta>) (outgoing v')
            \<le> sum (augment_edge f (u, v) \<Delta>) (incoming v')"  
    proof (cases)
      assume "\<Delta> = 0"
      with no_deficient_nodes show ?thesis using V' by auto 
    next
      assume "\<Delta> \<noteq> 0" with \<open>0\<le>\<Delta>\<close> have "0<\<Delta>" by auto
      with \<open>\<Delta> \<le> cf (u,v)\<close> have "(u,v)\<in>cf.E" unfolding Graph.E_def by auto
          
      show ?thesis
      proof (cases)    
        assume [simp]: "(u,v)\<in>E"
        hence AE: "augment_edge f (u,v) \<Delta> = f ( (u,v) := f (u,v) + \<Delta> )"  
          unfolding augment_edge_def by auto
        have 1: "\<forall>e\<in>outgoing v'. augment_edge f (u,v) \<Delta> e = f e" if "v'\<noteq>u"
          using that unfolding outgoing_def AE by auto
        have 2: "\<forall>e\<in>incoming v'. augment_edge f (u,v) \<Delta> e = f e" if "v'\<noteq>v"
          using that unfolding incoming_def AE by auto

        from \<open>(u,v)\<in>E\<close> no_self_loop have "u\<noteq>v" by blast
            
        {
          assume "v' \<noteq> u" "v' \<noteq> v"
          with 1 2 V' no_deficient_nodes have ?thesis by auto
        } moreover {
          assume [simp]: "v'=v" 
          have "sum (augment_edge f (u, v) \<Delta>) (outgoing v') 
              = sum f (outgoing v)"  
            using 1 \<open>u\<noteq>v\<close> V' by auto
          also have "\<dots> \<le> sum f (incoming v)" 
            using V' no_deficient_nodes by auto
          also have "\<dots> \<le> sum (augment_edge f (u, v) \<Delta>) (incoming v)"
            apply (rule sum_mono)
            using \<open>0\<le>\<Delta>\<close>
            by (auto simp: incoming_def augment_edge_def split!: if_split)
          finally have ?thesis by simp
        } moreover {
          assume [simp]: "v'=u"
          have A1: "sum (augment_edge f (u,v) \<Delta>) (incoming v') 
                  = sum f (incoming u)"  
            using 2 \<open>u\<noteq>v\<close> by auto
          have "(u,v) \<in> outgoing u" using \<open>(u,v)\<in>E\<close> 
            by (auto simp: outgoing_def)
          note AUX = sum.remove[OF _ this, simplified]
          have A2: "sum (augment_edge f (u,v) \<Delta>) (outgoing u) 
                  = sum f (outgoing u) + \<Delta>"
            using AUX[of "augment_edge f (u,v) \<Delta>"] AUX[of "f"] by auto
          from A1 A2 \<open>\<Delta> \<le> excess f u\<close> no_deficient_nodes V' have ?thesis 
            unfolding excess_def by auto
        } ultimately show ?thesis by blast
      next
        assume [simp]: \<open>(u,v)\<notin>E\<close> 
        hence [simp]: "(v,u)\<in>E" using cfE_ss_invE \<open>(u,v)\<in>cf.E\<close> by auto
        from \<open>(u,v)\<notin>E\<close> \<open>(v,u)\<in>E\<close> have "u\<noteq>v" by blast
        
        have AE: "augment_edge f (u,v) \<Delta> = f ( (v,u) := f (v,u) - \<Delta> )"  
          unfolding augment_edge_def by simp
        have 1: "\<forall>e\<in>outgoing v'. augment_edge f (u,v) \<Delta> e = f e" if "v'\<noteq>v"
          using that unfolding outgoing_def AE by auto
        have 2: "\<forall>e\<in>incoming v'. augment_edge f (u,v) \<Delta> e = f e" if "v'\<noteq>u"
          using that unfolding incoming_def AE by auto

        {
          assume "v' \<noteq> u" "v' \<noteq> v"
          with 1 2 V' no_deficient_nodes have ?thesis by auto
        } moreover {
          assume [simp]: "v'=u" 
          have A1: "sum (augment_edge f (u, v) \<Delta>) (outgoing v') 
                  = sum f (outgoing u)"  
            using 1 \<open>u\<noteq>v\<close> V' by auto
              
          have "(v,u) \<in> incoming u" 
            using \<open>(v,u)\<in>E\<close> by (auto simp: incoming_def)
          note AUX = sum.remove[OF _ this, simplified]    
          have A2: "sum (augment_edge f (u,v) \<Delta>) (incoming u) 
                  = sum f (incoming u) - \<Delta>"
            using AUX[of "augment_edge f (u,v) \<Delta>"] AUX[of "f"] by auto
              
          from A1 A2 \<open>\<Delta> \<le> excess f u\<close> no_deficient_nodes V' have ?thesis 
            unfolding excess_def by auto
        } moreover {
          assume [simp]: "v'=v"
          have "sum (augment_edge f (u,v) \<Delta>) (outgoing v') 
              \<le> sum f (outgoing v')"  
            apply (rule sum_mono)
            using \<open>0<\<Delta>\<close>  
            by (auto simp: augment_edge_def)  
          also have "\<dots> \<le> sum f (incoming v)" 
            using no_deficient_nodes V' by auto
          also have "\<dots> \<le> sum (augment_edge f (u,v) \<Delta>) (incoming v')"    
            using 2 \<open>u\<noteq>v\<close> by auto
          finally have ?thesis by simp
        } ultimately show ?thesis by blast
      qed      
    qed              
  qed          
  done            
end \<comment> \<open>Network with Preflow\<close> 

subsubsection \<open>Push Operation\<close>  
context Network 
begin  
text \<open>The push operation pushes as much flow as possible flow from an active 
  node over an admissible edge.

  A node is called \emph{active} if it has positive excess, and an edge \<open>(u,v)\<close>
  of the residual graph is called admissible, if @{term \<open>l u = l v + 1\<close>}.
\<close> 
definition push_precond :: "'capacity flow \<Rightarrow> labeling \<Rightarrow> edge \<Rightarrow> bool" 
  where "push_precond f l 
    \<equiv> \<lambda>(u,v). excess f u > 0 \<and> (u,v)\<in>cfE_of f \<and> l u = l v + 1"
  
text \<open>The maximum possible flow is determined by the available excess flow at 
  the source node and the available capacity of the edge.\<close>  
definition push_effect :: "'capacity flow \<Rightarrow> edge \<Rightarrow> 'capacity flow" 
  where "push_effect f 
    \<equiv> \<lambda>(u,v). augment_edge f (u,v) (min (excess f u) (cf_of f (u,v)))"

lemma push_precondI[intro?]: 
  "\<lbrakk>excess f u > 0; (u,v)\<in>cfE_of f; l u = l v + 1\<rbrakk> \<Longrightarrow> push_precond f l (u,v)"
  unfolding push_precond_def by auto

subsubsection \<open>Relabel Operation\<close>    
text \<open>
  An active node (not the sink) without any outgoing admissible edges 
  can be relabeled. 
\<close>    
definition relabel_precond :: "'capacity flow \<Rightarrow> labeling \<Rightarrow> node \<Rightarrow> bool" 
  where "relabel_precond f l u 
    \<equiv> u\<noteq>t \<and> excess f u > 0 \<and> (\<forall>v. (u,v)\<in>cfE_of f \<longrightarrow> l u \<noteq> l v + 1)"

text \<open>The new label is computed from the neighbour's labels, to be the minimum
  value that will create an outgoing admissible edge.\<close>    
definition relabel_effect :: "'capacity flow \<Rightarrow> labeling \<Rightarrow> node \<Rightarrow> labeling"
  where "relabel_effect f l u 
    \<equiv> l( u := Min { l v | v. (u,v)\<in>cfE_of f } + 1 )"
  
subsubsection \<open>Initialization\<close>
(* TODO: The algorithm can be initialized with other labelings ... 
  reflect this in abstract complexity/correctness theorem.*)  
text \<open>
  The initial preflow exhausts all outgoing edges of the source node.
\<close>  
definition "pp_init_f \<equiv> \<lambda>(u,v). if (u=s) then c (u,v) else 0"

text \<open>
  The initial labeling labels the source with \<open>|V|\<close>, and all other nodes
  with \<open>0\<close>.
\<close>  
definition "pp_init_l \<equiv> (\<lambda>x. 0)(s := card V)"

end \<comment> \<open>Network\<close>

subsection \<open>Abstract Correctness\<close>
text \<open>We formalize the abstract correctness argument of the algorithm. 
  It consists of two parts:
    \<^enum> Execution of push and relabel operations maintain a valid labeling
    \<^enum> If no push or relabel operations can be executed, the preflow is actually 
      a flow.

  This section corresponds to the proof of \cormen{26.18}.
\<close>  
  
subsubsection \<open>Maintenance of Invariants\<close>  
  
context Network 
begin  
  
lemma pp_init_invar: "Labeling c s t pp_init_f pp_init_l"
  apply (unfold_locales;
      ((auto simp: pp_init_f_def pp_init_l_def cap_non_negative; fail) 
        | (intro ballI)?))  
proof -  
  fix v
  assume "v\<in>V - {s,t}"
  hence "\<forall>e\<in>outgoing v. pp_init_f e = 0"
    by (auto simp: outgoing_def pp_init_f_def)
  hence [simp]: "sum pp_init_f (outgoing v) = 0" by auto
  have "0 \<le> pp_init_f e" for e
    by (auto simp: pp_init_f_def cap_non_negative split: prod.split)
  from sum_bounded_below[of "incoming v" 0 pp_init_f, OF this]
  have "0 \<le> sum pp_init_f (incoming v)" by auto
  thus "sum pp_init_f (outgoing v) \<le> sum pp_init_f (incoming v)"
    by auto
      
next
  fix u v
  assume "(u, v) \<in> Graph.E (residualGraph c pp_init_f)"  
  thus "pp_init_l u \<le> pp_init_l v + 1"
    unfolding pp_init_l_def Graph.E_def pp_init_f_def residualGraph_def
    by (auto split: if_splits)
      
qed    

lemma pp_init_f_preflow: "NPreflow c s t pp_init_f" 
proof -  
  from pp_init_invar interpret Labeling c s t pp_init_f pp_init_l .
  show ?thesis by unfold_locales    
qed  
  
end \<comment> \<open>Network\<close>  

context Labeling
begin
  
text \<open>Push operations preserve a valid labeling~\cormen{26.16}.\<close>
theorem push_pres_Labeling:
  assumes "push_precond f l e"
  shows "Labeling c s t (push_effect f e) l"
  unfolding push_effect_def  
proof (cases e; clarsimp)    
  fix u v
  assume [simp]: "e=(u,v)"
  let ?f' = "(augment_edge f (u, v) (min (excess f u) (cf (u, v))))"
    
  from assms have   
    ACTIVE: "excess f u > 0"
    and EDGE: "(u,v)\<in>cf.E"  
    and ADM: "l u = l v + 1"
    unfolding push_precond_def by auto
      
  interpret cf': Preflow c s t ?f'
   apply (rule augment_edge_preflow_preserve)
   using ACTIVE resE_nonNegative  
   by auto
  show "Labeling c s t ?f' l"
    apply unfold_locales using valid
    using cfE_augment_ss[OF EDGE] ADM
    apply (fastforce)
    by auto  
qed      
  
lemma finite_min_cf_outgoing[simp, intro!]: "finite {l v |v. (u, v) \<in> cf.E}"    
proof -
  have "{l v |v. (u, v) \<in> cf.E} = l`snd`cf.outgoing u"
    by (auto simp: cf.outgoing_def)
  moreover have "finite (l`snd`cf.outgoing u)" by auto
  ultimately show ?thesis by auto
qed  
  
text \<open>Relabel operations preserve a valid labeling~\cormen{26.16}. 
  Moreover, they increase the label of the relabeled node~\cormen{26.15}.
\<close>  
theorem 
  assumes PRE: "relabel_precond f l u"
  shows relabel_increase_u: "relabel_effect f l u u > l u" (is ?G1)
    and relabel_pres_Labeling: "Labeling c s t f (relabel_effect f l u)" (is ?G2)
proof -
  from PRE have  
        NOT_SINK: "u\<noteq>t"
    and ACTIVE: "excess f u > 0"
    and NO_ADM: "\<And>v. (u,v)\<in>cf.E \<Longrightarrow> l u \<noteq> l v + 1"
  unfolding relabel_precond_def by auto
  
  from ACTIVE have [simp]: "s\<noteq>u" using excess_s_non_pos by auto
      
  from active_has_cf_outgoing[OF ACTIVE] have [simp]: "\<exists>v. (u, v) \<in> cf.E" 
    by (auto simp: cf.outgoing_def)
  
  from NO_ADM valid have "l u < l v + 1" if "(u,v)\<in>cf.E" for v
    by (simp add: nat_less_le that)
  hence LU_INCR: "l u \<le> Min { l v | v. (u,v)\<in>cf.E }" 
    by (auto simp: less_Suc_eq_le)
  with valid have "\<forall>u'. (u',u)\<in>cf.E \<longrightarrow> l u' \<le> Min { l v | v. (u,v)\<in>cf.E } + 1"    
    by (smt ab_semigroup_add_class.add.commute add_le_cancel_left le_trans)
  moreover have "\<forall>v. (u,v)\<in>cf.E \<longrightarrow> Min { l v | v. (u,v)\<in>cf.E } + 1 \<le> l v + 1"
    using Min_le by auto
  ultimately show ?G1 ?G2
    unfolding relabel_effect_def
    apply (clarsimp_all simp: PRE)
    subgoal using LU_INCR by (simp add: less_Suc_eq_le)
    apply (unfold_locales)
    subgoal for u' v' using valid by auto
    subgoal by auto    
    subgoal using NOT_SINK by auto
    done
qed      
 
lemma relabel_preserve_other: "u\<noteq>v \<Longrightarrow> relabel_effect f l u v = l v" 
  unfolding relabel_effect_def by auto
  
subsubsection \<open>Maxflow on Termination\<close>    
text \<open>
  If no push or relabel operations can be performed any more,
  we have arrived at a maximal flow.
\<close>  
theorem push_relabel_term_imp_maxflow:
  assumes no_push: "\<forall>(u,v)\<in>cf.E. \<not>push_precond f l (u,v)"
  assumes no_relabel: "\<forall>u. \<not>relabel_precond f l u"
  shows "isMaxFlow f"  
proof -
  from assms have "\<forall>u\<in>V-{t}. excess f u \<le> 0"
    unfolding push_precond_def relabel_precond_def
    by force 
  with excess_non_negative have "\<forall>u\<in>V-{s,t}. excess f u = 0" by force
  with no_excess_imp_maxflow show ?thesis . 
qed      
  
end \<comment> \<open>Labeling\<close>  
  
subsection \<open>Convenience Lemmas\<close>
text \<open>We define a locale to reflect the effect of a push operation\<close>  
locale push_effect_locale = Labeling +
  fixes u v
  assumes PRE: "push_precond f l (u,v)"
begin    
  abbreviation "f' \<equiv> push_effect f (u,v)"
  sublocale l': Labeling c s t f' l  
    using push_pres_Labeling[OF PRE] .
  
  lemma uv_cf_edge[simp, intro!]: "(u,v)\<in>cf.E" 
    using PRE unfolding push_precond_def by auto
  lemma excess_u_pos: "excess f u > 0" 
    using PRE unfolding push_precond_def by auto   
  lemma l_u_eq[simp]: "l u = l v + 1" 
    using PRE unfolding push_precond_def by auto   

  lemma uv_edge_cases:
    obtains (par) "(u,v)\<in>E" "(v,u)\<notin>E" 
          | (rev) "(v,u)\<in>E" "(u,v)\<notin>E"
    using uv_cf_edge cfE_ss_invE no_parallel_edge by blast  

  lemma uv_nodes[simp, intro!]: "u\<in>V" "v\<in>V" 
    using E_ss_VxV cfE_ss_invE no_parallel_edge by auto
      
  lemma uv_not_eq[simp]: "u\<noteq>v" "v\<noteq>u"
    using E_ss_VxV cfE_ss_invE[THEN subsetD, OF uv_cf_edge] no_parallel_edge 
    by auto

  definition "\<Delta> = min (excess f u) (cf_of f (u,v))"    
    
  lemma \<Delta>_positive: "\<Delta> > 0"  
    unfolding \<Delta>_def 
    using excess_u_pos uv_cf_edge[unfolded cf.E_def] resE_positive 
    by auto
      
  lemma f'_alt: "f' = augment_edge f (u,v) \<Delta>" 
    unfolding push_effect_def \<Delta>_def by auto
      
  lemma cf'_alt: "l'.cf = augment_edge_cf cf (u,v) \<Delta>"    
    unfolding push_effect_def \<Delta>_def augment_edge_cf_def
    by (auto simp: augment_edge_cf')
      
  lemma excess'_u[simp]: "excess f' u = excess f u - \<Delta>"
    unfolding excess_def[where f=f']
  proof -
    show "sum f' (incoming u) - sum f' (outgoing u) = excess f u - \<Delta>"
    proof (cases rule: uv_edge_cases)  
      case [simp]: par 
      hence UV_ONI:"(u,v)\<in>outgoing u - incoming u"
        by (auto simp: incoming_def outgoing_def no_self_loop)
      have 1: "sum f' (incoming u) = sum f (incoming u)"    
        apply (rule sum.cong[OF refl])
        using UV_ONI unfolding f'_alt
        apply (subst augment_edge_other)
        by auto  
          
      have "sum f' (outgoing u) 
        = sum f (outgoing u) + (\<Sum>x\<in>outgoing u. if x = (u, v) then \<Delta> else 0)"
        unfolding f'_alt augment_edge_def sum.distrib[symmetric] 
          by (rule sum.cong) auto
      also have "\<dots> = sum f (outgoing u) + \<Delta>" 
        using UV_ONI by (auto simp: sum.delta)
      finally show ?thesis using 1 unfolding excess_def by simp 
    next  
      case [simp]: rev 
      have UV_INO:"(v,u)\<in>incoming u - outgoing u"
        by (auto simp: incoming_def outgoing_def no_self_loop)
      have 1: "sum f' (outgoing u) = sum f (outgoing u)"    
        apply (rule sum.cong[OF refl])
        using UV_INO unfolding f'_alt
        apply (subst augment_edge_rev_other)  
        by (auto)
      have "sum f' (incoming u) 
        = sum f (incoming u) + (\<Sum>x\<in>incoming u. if x = (v, u) then - \<Delta> else 0)"
        unfolding f'_alt augment_edge_def sum.distrib[symmetric] 
          by (rule sum.cong) auto
      also have "\<dots> = sum f (incoming u) - \<Delta>"  
        using UV_INO by (auto simp: sum.delta)
      finally show ?thesis using 1 unfolding excess_def by auto
    qed      
  qed
    
  lemma excess'_v[simp]: "excess f' v = excess f v + \<Delta>"
    unfolding excess_def[where f=f']
  proof -    
    show "sum f' (incoming v) - sum f' (outgoing v) = excess f v + \<Delta>"
    proof (cases rule: uv_edge_cases)
      case [simp]: par 
      have UV_INO: "(u,v)\<in>incoming v - outgoing v"
        unfolding incoming_def outgoing_def by (auto simp: no_self_loop)
      have 1: "sum f' (outgoing v) = sum f (outgoing v)"    
        using UV_INO unfolding f'_alt
        by (auto simp: augment_edge_def intro: sum.cong)
          
      have "sum f' (incoming v) 
        = sum f (incoming v) + (\<Sum>x\<in>incoming v. if x=(u,v) then \<Delta> else 0)"    
        unfolding f'_alt augment_edge_def sum.distrib[symmetric] 
        apply (rule sum.cong)
        using UV_INO unfolding f'_alt by auto
      also have "\<dots> = sum f (incoming v) + \<Delta>" 
        using UV_INO by (auto simp: sum.delta)
      finally show ?thesis using 1 by (auto simp: excess_def)
    next
      case [simp]: rev
      have UV_INO:"(v,u)\<in>outgoing v - incoming v"
        by (auto simp: incoming_def outgoing_def no_self_loop)

      have 1: "sum f' (incoming v) = sum f (incoming v)"
        using UV_INO unfolding f'_alt
        by (auto simp: augment_edge_def intro: sum.cong)
          
      have "sum f' (outgoing v) 
        = sum f (outgoing v) + (\<Sum>x\<in>outgoing v. if x=(v,u) then - \<Delta> else 0)"    
        unfolding f'_alt augment_edge_def sum.distrib[symmetric] 
        apply (rule sum.cong)
        using UV_INO unfolding f'_alt by auto
      also have "\<dots> = sum f (outgoing v) - \<Delta>" 
        using UV_INO by (auto simp: sum.delta)
      finally show ?thesis using 1 by (auto simp: excess_def)
    qed
  qed  
    
  lemma excess'_other[simp]:
    assumes "x \<noteq> u" "x \<noteq> v"  
    shows "excess f' x = excess f x"
  proof -
    have NE: "(u,v)\<notin>incoming x" "(u,v)\<notin>outgoing x"
          "(v,u)\<notin>incoming x" "(v,u)\<notin>outgoing x"
      using assms unfolding incoming_def outgoing_def by auto
    have 
      "sum f' (outgoing x) = sum f (outgoing x)"
      "sum f' (incoming x) = sum f (incoming x)"
      by (auto 
            simp: augment_edge_def f'_alt NE 
            split!: if_split 
            intro: sum.cong)  
    thus ?thesis    
      unfolding excess_def by auto
  qed      

  lemma excess'_if: 
    "excess f' x = (
           if x=u then excess f u - \<Delta> 
      else if x=v then excess f v + \<Delta> 
         else excess f x)"  
    by simp
    
end \<comment> \<open>Push Effect Locale\<close> 
  
  
  
subsection \<open>Complexity\<close>  
text \<open>
  Next, we analyze the complexity of the generic push relabel algorithm.
  We will show that it has a complexity of \<open>O(V\<^sup>2E)\<close> basic operations.
  Here, we often trade precise estimation of constant factors for simplicity
  of the proof.
\<close>  
 
subsubsection \<open>Auxiliary Lemmas\<close>  
context Network 
begin  
  
lemma cardE_nz_aux[simp, intro!]:
  "card E \<noteq> 0" "card E \<ge> Suc 0" "card E > 0"
proof -
  show "card E \<noteq> 0" by (simp add: E_not_empty)
  thus "card E \<ge> Suc 0" by linarith
  thus "card E > 0" by auto
qed
  
text \<open>The number of nodes can be estimated by the number of edges.
  This estimation is done in various places to get smoother bounds.
\<close>  
lemma card_V_est_E: "card V \<le> 2 * card E" 
proof -
  have "card V \<le> card (fst`E) + card (snd`E)"
    by (auto simp: card_Un_le V_alt)
  also note card_image_le[OF finite_E]
  also note card_image_le[OF finite_E]
  finally show "card V \<le> 2 * card E" by auto
qed  
  

end  
  
subsubsection \<open>Height Bound\<close>  
text \<open>A crucial idea of estimating the complexity is the insight that 
  no label will exceed \<open>2|V|-1\<close> during the algorithm.

  We define a locale that states this invariant, and show that the algorithm
  maintains it. The corresponds to the proof of \cormen{26.20}.
\<close>  
locale Height_Bounded_Labeling = Labeling +
  assumes height_bound: "\<forall>u\<in>V. l u \<le> 2*card V - 1"
begin    
  lemma height_bound': "u\<in>V \<Longrightarrow> l u \<le> 2*card V - 1"
    using height_bound by auto
end  
  
lemma (in Network) pp_init_height_bound: 
  "Height_Bounded_Labeling c s t pp_init_f pp_init_l"
proof -
  interpret Labeling c s t pp_init_f pp_init_l by (rule pp_init_invar)
  show ?thesis by unfold_locales (auto simp: pp_init_l_def)  
qed    

context Height_Bounded_Labeling
begin

text \<open>As push does not change the labeling, it trivially preserves the 
  height bound.\<close>  
lemma push_pres_height_bound:
  assumes "push_precond f l e"
  shows "Height_Bounded_Labeling c s t (push_effect f e) l"  
proof -    
  from push_pres_Labeling[OF assms] 
  interpret l': Labeling c s t "push_effect f e" l .
  show ?thesis using height_bound by unfold_locales    
qed      

text \<open>
  In a valid labeling,
  any active node has a (simple) path to the source node in 
  the residual graph~\cormen{26.19}.
\<close>  
lemma (in Labeling) excess_imp_source_path: 
  assumes "excess f u > 0"
  obtains p where "cf.isSimplePath u p s"
proof -
  obtain U where U_def: "U = {v|p v. cf.isSimplePath u p v}" by blast
  have fct1: "U \<subseteq> V"
  proof 
    fix v
    assume "v \<in> U"
    then have "(u, v) \<in> cf.E\<^sup>*" 
      using U_def cf.isSimplePath_def cf.isPath_rtc by auto
    then obtain u' where "u = v \<or> ((u, u') \<in> cf.E\<^sup>* \<and> (u', v) \<in> cf.E)" 
      by (meson rtranclE)
    thus "v \<in> V"
    proof
      assume "u = v"
      thus ?thesis using excess_nodes_only[OF assms] by blast
    next
      assume "(u, u') \<in> cf.E\<^sup>* \<and> (u', v) \<in> cf.E"
      then have "v \<in> cf.V" unfolding cf.V_def by blast
      thus ?thesis by simp
    qed
  qed 
    
  have "s \<in> U"
  proof(rule ccontr)
    assume "s \<notin> U"
    obtain U' where U'_def: "U' = V - U" by blast
    
    have "(\<Sum>u\<in>U. excess f u) 
        = (\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (v, u))) - (\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (u, v)))"
    proof -
      have "(\<Sum>u\<in>U. excess f u) 
          = (\<Sum>u\<in>U. (\<Sum>v\<in>incoming u. f v)) - (\<Sum>u\<in>U.(\<Sum>v\<in>outgoing u. f v))"
        (is "_ = ?R1 - ?R2") unfolding excess_def by (simp add: sum_subtractf)
      also have "?R1 = (\<Sum>u\<in>U. (\<Sum>v\<in>V. f (v, u)))" 
        using sum_incoming_alt_flow fct1 by (meson subsetCE sum.cong)
      also have "\<dots> = (\<Sum>u\<in>U. (\<Sum>v\<in>U. f (v, u))) + (\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (v, u)))"
      proof -
        have "(\<Sum>v\<in>V. f (v, u)) = (\<Sum>v\<in>U. f (v, u)) + (\<Sum>v\<in>U'. f (v, u))" for u
          using U'_def fct1 finite_V 
          by (metis ab_semigroup_add_class.add.commute sum.subset_diff)
        thus ?thesis by (simp add: sum.distrib)
      qed
      also have "?R2 = (\<Sum>u\<in>U. (\<Sum>v\<in>V. f (u, v)))" 
        using sum_outgoing_alt_flow fct1 by (meson subsetCE sum.cong)
      also have "\<dots> = (\<Sum>u\<in>U. (\<Sum>v\<in>U. f (u, v))) + (\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (u, v)))"
      proof -
        have "(\<Sum>v\<in>V. f (u, v)) = (\<Sum>v\<in>U. f (u, v)) + (\<Sum>v\<in>U'. f (u, v))" for u
          using U'_def fct1 finite_V 
          by (metis ab_semigroup_add_class.add.commute sum.subset_diff)
        thus ?thesis by (simp add: sum.distrib)
      qed
      also have "(\<Sum>u\<in>U. (\<Sum>v\<in>U. f (u, v))) = (\<Sum>u\<in>U. (\<Sum>v\<in>U. f (v, u)))"
      proof -
        {
          fix A :: "nat set"
          assume "finite A"
          then have "(\<Sum>u\<in>A. (\<Sum>v\<in>A. f (u, v))) = (\<Sum>u\<in>A. (\<Sum>v\<in>A. f (v, u)))"
          proof (induction "card A" arbitrary: A)
            case 0
            then show ?case by auto
          next
            case (Suc x)
            then obtain A' a 
              where o1:"A = insert a A'" and o2:"x = card A'" and o3:"finite A'"
              by (metis card_insert_disjoint card_le_Suc_iff le_refl nat.inject)
            then have lm:"(\<Sum>e\<in>A. g e) = (\<Sum>e\<in>A'. g e) + g a" 
              for g :: "nat \<Rightarrow> 'a"  
              using Suc.hyps(2)
              by (metis card_insert_if n_not_Suc_n 
                        semiring_normalization_rules(24) sum.insert)

            have "(\<Sum>u\<in>A. (\<Sum>v\<in>A. f (u, v))) 
              = (\<Sum>u\<in>A'. (\<Sum>v\<in>A. f (u, v))) + (\<Sum>v\<in>A. f (a, v))"
              (is "_ = ?R1 + ?R2") using lm by auto     
            also have "?R1 = (\<Sum>u\<in>A'. (\<Sum>v\<in>A'. f (u, v))) + (\<Sum>u\<in>A'. f(u, a))" 
              (is "_ = ?R1_1 + ?R1_2") using lm sum.distrib by force
            also note add.assoc
            also have "?R1_2 + ?R2 = (\<Sum>u\<in>A'. f(a, u)) + (\<Sum>v\<in>A. f(v, a))"
              (is "_ = ?R1_2' + ?R2'") using lm by auto    
            also have "?R1_1 = (\<Sum>u\<in>A'. (\<Sum>v\<in>A'. f (v, u)))" 
              (is "_ = ?R1_1'") using Suc.hyps(1)[of A'] o2 o3 by auto
            also note add.assoc[symmetric]
            also have "?R1_1' + ?R1_2' = (\<Sum>u\<in>A'. (\<Sum>v\<in>A. f (v, u)))"
              by (metis (no_types, lifting) lm sum.cong sum.distrib)
            finally show ?case using lm[symmetric] by auto
          qed
        } note this[of U]
        thus ?thesis using fct1 finite_V finite_subset by auto
      qed
      finally show ?thesis by arith
    qed
    moreover have "(\<Sum>u\<in>U. excess f u) > 0"
    proof -
      have "u \<in> U" using U_def by simp
      moreover have "u \<in> U \<Longrightarrow> excess f u \<ge> 0" for u 
        using fct1 excess_non_negative' \<open>s \<notin> U\<close> by auto
      ultimately show ?thesis using assms fct1 finite_V
        by (metis Diff_cancel Diff_eq_empty_iff 
                  Diff_infinite_finite finite_Diff sum_pos2)
    qed
    ultimately have 
      fct2: "(\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (v, u))) - (\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (u, v))) > 0" 
      by simp
    
    have fct3: "(\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (v, u))) > 0"
    proof -
      have "(\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (v, u))) \<ge> 0" 
        using capacity_const by (simp add: sum_nonneg)
      moreover have "(\<Sum>u\<in>U. (\<Sum>v\<in>U'. f (u, v))) \<ge> 0" 
        using capacity_const by (simp add: sum_nonneg)
      ultimately show ?thesis using fct2 by simp
    qed
      
    have "\<exists>u' v'. (u' \<in> U \<and> v' \<in> U' \<and> f (v', u') > 0)"
    proof(rule ccontr)
      assume "\<not> (\<exists>u' v'. u' \<in> U \<and> v' \<in> U' \<and> f (v', u') > 0)"
      then have "(\<forall>u' v'. (u' \<in> U \<and> v' \<in> U' \<longrightarrow> f (v', u') = 0))"
        using capacity_const by (metis le_neq_trans)
      thus False using fct3 by simp
    qed
    then obtain u' v' where "u' \<in> U" and "v' \<in> U'" and "f (v', u') > 0" 
      by blast
    
    obtain p1 where "cf.isSimplePath u p1 u'" using U_def \<open>u' \<in> U\<close> by auto
    moreover have "(u', v') \<in> cf.E"
    proof -
      have "(v', u') \<in> E" 
        using capacity_const \<open>f (v', u') > 0\<close> 
        by (metis not_less zero_flow_simp)
      then have "cf (u', v') > 0" unfolding cf_def 
        using no_parallel_edge \<open>f (v', u') > 0\<close> by (auto split: if_split)
      thus ?thesis unfolding cf.E_def by simp
    qed
    ultimately have "cf.isPath u (p1 @ [(u', v')]) v'" 
      using Graph.isPath_append_edge Graph.isSimplePath_def by blast
    then obtain p2 where "cf.isSimplePath u p2 v'" 
      using cf.isSPath_pathLE by blast
    then have "v' \<in> U" using U_def by auto
    thus False using \<open>v' \<in> U'\<close> and U'_def by simp
  qed
  then obtain p' where "cf.isSimplePath u p' s" using U_def by auto
  thus ?thesis ..
qed
  
text \<open>Relabel operations preserve the height bound~\cormen{26.20}.\<close>
lemma relabel_pres_height_bound:
  assumes "relabel_precond f l u"
  shows "Height_Bounded_Labeling c s t f (relabel_effect f l u)"
proof -
  let ?l' = "relabel_effect f l u"
  
  from relabel_pres_Labeling[OF assms]  
  interpret l': Labeling c s t f ?l' .
  
  from assms have "excess f u > 0" unfolding relabel_precond_def by auto
  with l'.excess_imp_source_path obtain p where p_obt: "cf.isSimplePath u p s" .
  
  have "u \<in> V" using excess_nodes_only \<open>excess f u > 0\<close> .
  then have "length p < card V" 
    using cf.simplePath_length_less_V[of u p] p_obt by auto
  moreover have "?l' u \<le> ?l' s + length p" 
    using p_obt l'.gen_valid[of u p s] p_obt 
    unfolding cf.isSimplePath_def by auto
  moreover have "?l' s = card V" 
    using l'.Labeling_axioms Labeling_def Labeling_axioms_def by auto
  ultimately have "?l' u \<le> 2*card V - 1" by auto
  thus "Height_Bounded_Labeling c s t f ?l'" 
    apply unfold_locales
    using height_bound relabel_preserve_other
    by metis  
qed      
  
text \<open>Thus, the total number of relabel operations is 
  bounded by \<open>O(V\<^sup>2)\<close>~\cormen{26.21}. 

  We express this bound by defining a measure function, and show that 
  it is decreased by relabel operations.
\<close>  
definition (in Network) "sum_heights_measure l \<equiv> \<Sum>v\<in>V. 2*card V - l v"
  
corollary relabel_measure:
  assumes "relabel_precond f l u"
  shows "sum_heights_measure (relabel_effect f l u) < sum_heights_measure l"
proof -
  let ?l' = "relabel_effect f l u"
  from relabel_pres_height_bound[OF assms] 
  interpret l': Height_Bounded_Labeling c s t f ?l' .
    
  from assms have "u\<in>V" 
    by (simp add: excess_nodes_only relabel_precond_def)
      
  hence V_split: "V = insert u V" by auto
      
  show ?thesis  
    using relabel_increase_u[OF assms] relabel_preserve_other[of u]
    using l'.height_bound 
    unfolding sum_heights_measure_def
    apply (rewrite at "\<Sum>_\<in>\<hole>. _" V_split)+
    apply (subst sum.insert_remove[OF finite_V])+
    using \<open>u\<in>V\<close>  
    by auto   
qed        
end \<comment> \<open>Height Bounded Labeling\<close>  
  
lemma (in Network) sum_height_measure_is_OV2: 
  "sum_heights_measure l \<le> 2*(card V)\<^sup>2"
  unfolding  sum_heights_measure_def
proof -
  have "2 * card V - l v \<le> 2 * card V" for v by auto
  then have "(\<Sum>v\<in>V. 2 * card V - l v) \<le> (\<Sum>v\<in>V. 2 * card V)" 
    by (meson sum_mono)
  also have "(\<Sum>v\<in>V. 2 * card V) = card V * (2 * card V)" 
    using finite_V by auto
  finally show "(\<Sum>v\<in>V. 2 * card V - l v) \<le> 2 * (card V)^2" 
    by (simp add: power2_eq_square)
qed
  
  
subsubsection \<open>Formulation of the Abstract Algorithm\<close>
text \<open>We give a simple relational characterization 
  of the abstract algorithm as a labeled transition system,
  where the labels indicate the type of operation (push or relabel) that
  have been executed.
\<close>  
context Network
begin
  
datatype pr_operation = is_PUSH: PUSH | is_RELABEL: RELABEL
inductive_set pr_algo_lts 
  :: "(('capacity flow\<times>labeling) \<times> pr_operation \<times> ('capacity flow\<times>labeling)) set" 
where
  push: "\<lbrakk>push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((f,l),PUSH,(push_effect f e,l))\<in>pr_algo_lts"
| relabel: "\<lbrakk>relabel_precond f l u\<rbrakk>
    \<Longrightarrow> ((f,l),RELABEL,(f,relabel_effect f l u))\<in>pr_algo_lts"

  
end \<comment> \<open>Network\<close> 
  
text \<open>We show invariant maintenance and correctness on termination\<close>  
  
lemma (in Height_Bounded_Labeling) pr_algo_maintains_hb_labeling:
  assumes "((f,l),a,(f',l')) \<in> pr_algo_lts"
  shows "Height_Bounded_Labeling c s t f' l'"  
  using assms
  by cases (simp_all add: push_pres_height_bound relabel_pres_height_bound)  
  
lemma (in Height_Bounded_Labeling) pr_algo_term_maxflow:
  assumes "(f,l)\<notin>Domain pr_algo_lts"
  shows "isMaxFlow f"
proof -
  from assms have "\<nexists>e. push_precond f l e" and "\<nexists>u. relabel_precond f l u"
    by (auto simp: Domain_iff dest: pr_algo_lts.intros)
  with push_relabel_term_imp_maxflow show ?thesis by blast
qed      
  
  
subsubsection \<open>Saturating and Non-Saturating Push Operations\<close>  
context Network
begin
  
text \<open>
  For complexity estimation, it is distinguished whether a push operation
  saturates the edge or not.
\<close>  
definition sat_push_precond :: "'capacity flow \<Rightarrow> labeling \<Rightarrow> edge \<Rightarrow> bool"
  where "sat_push_precond f l 
  \<equiv> \<lambda>(u,v). excess f u > 0 
          \<and> excess f u \<ge> cf_of f (u,v) 
          \<and> (u,v)\<in>cfE_of f 
          \<and> l u = l v + 1"

definition nonsat_push_precond :: "'capacity flow \<Rightarrow> labeling \<Rightarrow> edge \<Rightarrow> bool"
  where "nonsat_push_precond f l 
  \<equiv> \<lambda>(u,v). excess f u > 0 
          \<and> excess f u < cf_of f (u,v) 
          \<and> (u,v)\<in>cfE_of f 
          \<and> l u = l v + 1"

lemma push_precond_eq_sat_or_nonsat: 
  "push_precond f l e \<longleftrightarrow> sat_push_precond f l e \<or> nonsat_push_precond f l e"  
  unfolding push_precond_def sat_push_precond_def nonsat_push_precond_def
  by auto  
  
lemma sat_nonsat_push_disj: 
  "sat_push_precond f l e \<Longrightarrow> \<not>nonsat_push_precond f l e"
  "nonsat_push_precond f l e \<Longrightarrow> \<not>sat_push_precond f l e"
  unfolding sat_push_precond_def nonsat_push_precond_def
  by auto  
  
lemma sat_push_alt: "sat_push_precond f l e 
  \<Longrightarrow> push_effect f e = augment_edge f e (cf_of f e)"
  unfolding push_effect_def push_precond_eq_sat_or_nonsat sat_push_precond_def 
  by (auto simp: min_absorb2)
    
lemma nonsat_push_alt: "nonsat_push_precond f l (u,v) 
  \<Longrightarrow> push_effect f (u,v) = augment_edge f (u,v) (excess f u)"    
  unfolding push_effect_def push_precond_eq_sat_or_nonsat nonsat_push_precond_def 
  by (auto simp: min_absorb1)

end \<comment> \<open>Network\<close> 
  
context push_effect_locale
begin
  lemma nonsat_push_\<Delta>: "nonsat_push_precond f l (u,v) \<Longrightarrow> \<Delta> = excess f u"      
    unfolding \<Delta>_def nonsat_push_precond_def by auto
  lemma sat_push_\<Delta>: "sat_push_precond f l (u,v) \<Longrightarrow> \<Delta> = cf (u,v)"      
    unfolding \<Delta>_def sat_push_precond_def by auto
    
end    
  
  
subsubsection \<open>Refined Labeled Transition System\<close>
context Network
begin
  
text \<open>For simpler reasoning, we make explicit the different push operations,
  and integrate the invariant into the LTS\<close>
  
datatype pr_operation' = 
  is_RELABEL': RELABEL' 
| is_NONSAT_PUSH': NONSAT_PUSH'
| is_SAT_PUSH': SAT_PUSH' edge   
  
inductive_set pr_algo_lts' where
  nonsat_push': "\<lbrakk>Height_Bounded_Labeling c s t f l; nonsat_push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((f,l),NONSAT_PUSH',(push_effect f e,l))\<in>pr_algo_lts'"
| sat_push': "\<lbrakk>Height_Bounded_Labeling c s t f l; sat_push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((f,l),SAT_PUSH' e,(push_effect f e,l))\<in>pr_algo_lts'"
| relabel': "\<lbrakk>Height_Bounded_Labeling c s t f l; relabel_precond f l u \<rbrakk>
    \<Longrightarrow> ((f,l),RELABEL',(f,relabel_effect f l u))\<in>pr_algo_lts'"

fun project_operation where
  "project_operation RELABEL' = RELABEL"
| "project_operation NONSAT_PUSH' = PUSH"  
| "project_operation (SAT_PUSH' _) = PUSH"  

lemma is_RELABEL_project_conv[simp]: 
  "is_RELABEL \<circ> project_operation = is_RELABEL'"
  apply (clarsimp intro!: ext) subgoal for x by (cases x) auto done

lemma is_PUSH_project_conv[simp]: 
  "is_PUSH \<circ> project_operation = (\<lambda>x. is_SAT_PUSH' x \<or> is_NONSAT_PUSH' x)"
  apply (clarsimp intro!: ext) subgoal for x by (cases x) auto done
    
end \<comment> \<open>Network\<close> 
  
context Height_Bounded_Labeling
begin  
lemma (in Height_Bounded_Labeling) xfer_run:
  assumes "((f,l),p,(f',l')) \<in> trcl pr_algo_lts"
  obtains p' where "((f,l),p',(f',l')) \<in> trcl pr_algo_lts'" 
               and "p = map project_operation p'"
proof -    
  have "\<exists>p'. 
      Height_Bounded_Labeling c s t f' l'
    \<and> ((f,l),p',(f',l')) \<in> trcl pr_algo_lts' 
    \<and> p = map project_operation p'"
    using assms
  proof (induction p arbitrary: f' l' rule: rev_induct)
    case Nil thus ?case using Height_Bounded_Labeling_axioms by simp  
  next
    case (snoc a p)
    from snoc.prems obtain fh lh 
      where PP: "((f, l), p, fh, lh) \<in> trcl pr_algo_lts" 
        and LAST: "((fh,lh),a,(f',l'))\<in>pr_algo_lts" 
      by (auto dest!: trcl_rev_uncons)  

    from snoc.IH[OF PP] obtain p' 
      where HBL: "Height_Bounded_Labeling c s t fh lh" 
        and PP': "((f, l), p', fh, lh) \<in> trcl pr_algo_lts'" 
        and [simp]: "p = map project_operation p'"
      by blast
        
    from LAST obtain a' 
      where LAST': "((fh,lh),a',(f',l'))\<in>pr_algo_lts'"
        and [simp]: "a = project_operation a'" 
      apply cases
      by (auto 
          simp: push_precond_eq_sat_or_nonsat
          dest: relabel'[OF HBL] nonsat_push'[OF HBL] sat_push'[OF HBL])  
    
    note HBL' = 
      Height_Bounded_Labeling.pr_algo_maintains_hb_labeling[OF HBL LAST]
      
    from HBL' trcl_rev_cons[OF PP' LAST'] show ?case by auto
  qed
  with assms that show ?thesis by blast
qed      
  
lemma xfer_relabel_bound:
  assumes BOUND: "\<forall>p'. ((f,l),p',(f',l')) \<in> trcl pr_algo_lts' 
          \<longrightarrow> length (filter is_RELABEL' p') \<le> B"
  assumes RUN: "((f,l),p,(f',l')) \<in> trcl pr_algo_lts"
  shows "length (filter is_RELABEL p) \<le> B"  
proof -
  from xfer_run[OF RUN] obtain p' 
    where RUN': "((f,l),p',(f',l')) \<in> trcl pr_algo_lts'" 
      and [simp]: "p = map project_operation p'" .
  
  have "length (filter is_RELABEL p) = length (filter is_RELABEL' p')" 
    by simp
  also from BOUND[rule_format,OF RUN'] 
  have "length (filter is_RELABEL' p') \<le> B" .
  finally show ?thesis .
qed
  
lemma xfer_push_bounds:
  assumes BOUND_SAT: "\<forall>p'. ((f,l),p',(f',l')) \<in> trcl pr_algo_lts' 
          \<longrightarrow> length (filter is_SAT_PUSH' p') \<le> B1"
  assumes BOUND_NONSAT: "\<forall>p'. ((f,l),p',(f',l')) \<in> trcl pr_algo_lts' 
          \<longrightarrow> length (filter is_NONSAT_PUSH' p') \<le> B2"
  assumes RUN: "((f,l),p,(f',l')) \<in> trcl pr_algo_lts"
  shows "length (filter is_PUSH p) \<le> B1 + B2"  
proof -
  
  from xfer_run[OF RUN] obtain p' 
    where RUN': "((f,l),p',(f',l')) \<in> trcl pr_algo_lts'" 
      and [simp]: "p = map project_operation p'" .
  
  have [simp]: "length [x\<leftarrow>p' . is_SAT_PUSH' x \<or> is_NONSAT_PUSH' x]
    = length (filter is_SAT_PUSH' p') + length (filter is_NONSAT_PUSH' p')"    
    by (induction p') auto
      
  have "length (filter is_PUSH p) 
    = length (filter is_SAT_PUSH' p') + length (filter is_NONSAT_PUSH' p')" 
    by simp
  also note BOUND_SAT[rule_format,OF RUN']    
  also note BOUND_NONSAT[rule_format,OF RUN']    
  finally show ?thesis by simp
qed
  
  
  
end \<comment> \<open>Height Bounded Labeling\<close> 

  
subsubsection \<open>Bounding the Relabel Operations\<close>  
  
lemma (in Network) relabel_action_bound':
  assumes A: "(fxl,p,fxl') \<in> trcl pr_algo_lts'"
  shows "length (filter (is_RELABEL') p) \<le> 2 * (card V)\<^sup>2"
proof -   
  from A have "length (filter (is_RELABEL') p) \<le> sum_heights_measure (snd fxl)"
    apply (induction rule: trcl.induct)
    apply (auto elim!: pr_algo_lts'.cases)  
    apply (drule (1) Height_Bounded_Labeling.relabel_measure)
    apply auto
    done
  also note sum_height_measure_is_OV2
  finally show "length (filter (is_RELABEL') p) \<le> 2 * (card V)\<^sup>2" .
qed  
  
lemma (in Height_Bounded_Labeling) relabel_action_bound:
  assumes A: "((f,l),p,(f',l')) \<in> trcl pr_algo_lts"
  shows "length (filter (is_RELABEL) p) \<le> 2 * (card V)\<^sup>2"
  using xfer_relabel_bound relabel_action_bound' A by meson
  
subsubsection \<open>Bounding the Saturating Push Operations\<close>
  
context Network
begin
text \<open>
  The basic idea is to estimate the saturating push operations per edge:
  After a saturating push, the edge disappears from the residual graph.
  It can only re-appear due to a push over the reverse edge, which requires
  relabeling of the nodes. 

  The estimation in \cormen{26.22} uses the same idea. However, it invests 
  some extra work in getting a more precise constant factor 
  by counting the pushes for an edge and its reverse edge together.
\<close>  

lemma labels_path_increasing:
  assumes "((f,l),p,(f',l')) \<in> trcl pr_algo_lts'"
  shows "l u \<le> l' u"
  using assms 
proof (induction p arbitrary: f l)
  case Nil thus ?case by simp
next
  case (Cons a p)
  then obtain fh lh 
    where FIRST: "((f,l),a,(fh,lh)) \<in> pr_algo_lts'"
      and PP: "((fh,lh),p,(f',l')): trcl pr_algo_lts'"
    by (auto simp: trcl_conv)  
      
  from FIRST interpret Height_Bounded_Labeling c s t f l
    by cases auto
    
  from FIRST Cons.IH[OF PP] show ?case
    apply (auto elim!: pr_algo_lts'.cases)
    using relabel_increase_u relabel_preserve_other
    by (metis le_trans nat_le_linear not_less)  
qed
  
lemma edge_reappears_at_increased_labeling:
  assumes "((f,l),p,(f',l')) \<in> trcl pr_algo_lts'"
  assumes "l u \<ge> l v + 1"
  assumes "(u,v) \<notin> cfE_of f"  
  assumes E': "(u,v) \<in> cfE_of f'"
  shows "l v < l' v"  
  using assms(1-3)
proof (induction p arbitrary: f l)
  case Nil thus ?case using E' by auto
next
  case (Cons a p)
  then obtain fh lh 
    where FIRST: "((f,l),a,(fh,lh)) \<in> pr_algo_lts'"
      and PP: "((fh,lh),p,(f',l')): trcl pr_algo_lts'"
    by (auto simp: trcl_conv)  
      
  from FIRST interpret Height_Bounded_Labeling c s t f l
    by cases auto
  
  consider 
    (push) u' v' 
      where "push_precond f l (u',v')" "fh = push_effect f (u',v')" "lh=l"
  | (relabel) u' 
      where "relabel_precond f l u'" "fh=f" "lh=relabel_effect f l u'"
    using FIRST       
    by (auto elim!: pr_algo_lts'.cases simp: push_precond_eq_sat_or_nonsat)  
  then show ?case proof cases
    case push
    note [simp] = push(2,3)  
    text \<open>The push operation cannot go on edge \<open>(u,v)\<close> or \<open>(v,u)\<close>\<close>  
    from push(1) have "(u',v')\<noteq>(u,v)" "(u',v')\<noteq>(v,u)" "(u',v')\<in>cf.E"
      using \<open>l u \<ge> l v + 1\<close> \<open>(u,v)\<notin>cf.E\<close>
      by (auto simp: push_precond_def)
    hence NE': "(u,v)\<notin>cfE_of fh" using \<open>(u,v)\<notin>cf.E\<close>
      using cfE_augment_ss[of u' v' f]  
      by (auto simp: push_effect_def)  
    from Cons.IH[OF PP _ NE'] \<open>l u \<ge> l v + 1\<close> show ?thesis by simp
  next
    case relabel
    note [simp] = relabel(2)  
      
    show ?thesis 
    proof (cases "u'=v")
      case False 
      from False relabel(3) relabel_preserve_other have [simp]: "lh v = l v" 
        by auto
      from False relabel(3) 
           relabel_preserve_other relabel_increase_u[OF relabel(1)]
      have "lh u \<ge> l u" by (cases "u'=u") auto
      with \<open>l u \<ge> l v + 1\<close> have LHG: "lh u \<ge> lh v + 1" by auto
          
      from Cons.IH[OF PP LHG] \<open>(u,v)\<notin>cf.E\<close> show ?thesis by simp
    next
      case True
      note [simp] = relabel(3)  
      from True relabel_increase_u[OF relabel(1)] 
      have "l v < lh v" by simp
      also note labels_path_increasing[OF PP, of v]
      finally show ?thesis by simp       
    qed
  qed
qed
  
lemma sat_push_edge_action_bound':
  assumes "((f,l),p,(f',l')) \<in> trcl pr_algo_lts'" 
  shows "length (filter ((=) (SAT_PUSH' e)) p) \<le> 2*card V"
proof -
  obtain u v where [simp]: "e=(u,v)" by (cases e)
  
  have "length (filter ((=) (SAT_PUSH' (u,v))) p) \<le> 2*card V - l v"
    if "((f,l),p,(f',l')) \<in> trcl pr_algo_lts'" for p
    using that
  proof (induction p arbitrary: f l rule: length_induct)
    case (1 p) thus ?case 
    proof (cases p)
      case Nil thus ?thesis by auto
    next        
      case [simp]: (Cons a p') 
      from "1.prems" obtain fh lh 
        where FIRST: "((f,l),a,(fh,lh)) \<in> pr_algo_lts'"
          and PP: "((fh,lh),p',(f',l')) \<in> trcl pr_algo_lts'"
        by (auto dest!: trcl_uncons)  
        
      from FIRST interpret Height_Bounded_Labeling c s t f l
        by cases auto
          
      show ?thesis
      proof (cases "a = SAT_PUSH' (u,v)")  
        case [simp]: False
        from "1.IH" PP have 
          "length (filter ((=) (SAT_PUSH' (u, v))) p') 
          \<le> 2 * card V - lh v"
          by auto
        with FIRST show ?thesis
          apply (cases; clarsimp)
        proof -
          fix ua :: nat
          assume a1: "length (filter ((=) (SAT_PUSH' (u, v))) p') 
                    \<le> 2 * card V - relabel_effect f l ua v"
          assume a2: "relabel_precond f l ua"
          have "2 * card V - relabel_effect f l ua v \<le> 2 * card V - l v 
          \<longrightarrow> length (filter ((=) (SAT_PUSH' (u, v))) p') \<le> 2 * card V - l v"
            using a1 order_trans by blast
          then show "length (filter ((=) (SAT_PUSH' (u, v))) p') 
                    \<le> 2 * card V - l v"
            using a2 a1 by (metis (no_types) Labeling.relabel_increase_u 
                Labeling_axioms diff_le_mono2 nat_less_le 
                relabel_preserve_other)
        qed  
      next          
        case [simp]: True
  
        from FIRST have 
          [simp]: "fh = push_effect f (u,v)" "lh = l" 
          and PRE: "sat_push_precond f l (u,v)"
          by (auto elim !: pr_algo_lts'.cases)  
          
        from PRE have "(u,v)\<in>cf.E" "l u = l v + 1" 
          unfolding sat_push_precond_def by auto
        hence "u\<in>V" "v\<in>V" "u\<noteq>v" using cfE_ss_invE E_ss_VxV by auto
            
        have UVNEH: "(u,v)\<notin>cfE_of fh" 
          using \<open>u\<noteq>v\<close>
          apply (simp 
                  add: sat_push_alt[OF PRE] augment_edge_cf'[OF \<open>(u,v)\<in>cf.E\<close>])
          unfolding Graph.E_def by simp
            
            
        show ?thesis 
        proof (cases "SAT_PUSH' (u,v) \<in> set p'")  
          case False 
          hence [simp]: "filter ((=) (SAT_PUSH' (u,v))) p' = []" 
            by (induction p') auto
          show ?thesis 
            using bspec[OF height_bound \<open>u\<in>V\<close>]  
            using bspec[OF height_bound \<open>v\<in>V\<close>]
            using card_V_ge2 
            by simp
        next
          case True
          then obtain p1 p2 
            where [simp]: "p'=p1@SAT_PUSH' (u,v)#p2" 
              and NP1: "SAT_PUSH' (u,v) \<notin> set p1"
            using in_set_conv_decomp_first[of _ p'] by auto 
              
          from NP1 have [simp]: "filter ((=) (SAT_PUSH' (u,v))) p1 = []" 
            by (induction p1) auto
              
          from PP obtain f2 l2 f3 l3 
            where P1: "((fh,lh),p1,(f2,l2)) \<in> trcl pr_algo_lts'"
              and S: "((f2,l2),SAT_PUSH' (u,v),(f3,l3)) \<in> pr_algo_lts'"
              and P2: "((f3,l3),p2,(f',l'))\<in>trcl pr_algo_lts'"
            by (auto simp: trcl_conv)  
          from S have "(u,v)\<in>cfE_of f2" and [simp]: "l3=l2" 
            by (auto elim!: pr_algo_lts'.cases simp: sat_push_precond_def)
          with edge_reappears_at_increased_labeling[OF P1 _ UVNEH] 
            \<open>l u = l v + 1\<close>
          have AUX1: "l v < l2 v" by auto
  
          from S interpret l2: Height_Bounded_Labeling c s t f2 l2
            by (auto elim!: pr_algo_lts'.cases)
              
          from spec[OF "1.IH", of "SAT_PUSH' (u,v)#p2"] S P2 have 
            "Suc (length (filter ((=) (SAT_PUSH' (u, v))) p2)) 
            \<le> 2 * card V - l2 v" 
            by (auto simp: trcl_conv)
          also have "\<dots> + 1 \<le> 2*card V - l v"
            using AUX1
            using bspec[OF l2.height_bound \<open>u\<in>V\<close>]  
            using bspec[OF l2.height_bound \<open>v\<in>V\<close>]
            by auto  
          finally show ?thesis
            by simp
        qed
      qed  
    qed
  qed
  thus ?thesis using assms by fastforce  
qed          

lemma sat_push_action_bound':
  assumes A: "((f,l),p,(f',l')) \<in> trcl pr_algo_lts'"
  shows "length (filter is_SAT_PUSH' p) \<le> 4 * card V * card E"
proof -
  from A have IN_E: "e\<in>E\<union>E\<inverse>" if "SAT_PUSH' e \<in> set p" for e
    using that cfE_of_ss_invE
    apply (induction p arbitrary: f l)
    apply (auto 
        simp: trcl_conv sat_push_precond_def 
        elim!: pr_algo_lts'.cases
      ; blast)+
    done  
    
  have AUX: "length (filter (\<lambda>a. \<exists>e\<in>S. a = SAT_PUSH' e) p) 
    = (\<Sum>e\<in>S. length (filter ((=) (SAT_PUSH' e)) p))" if "finite S" for S
    using that
    apply induction
    apply simp 
    apply clarsimp
    apply (subst length_filter_disj_or_conv; clarsimp)
    apply (fo_rule arg_cong)
    subgoal premises by (induction p) auto
    done    

  have "is_SAT_PUSH' a = (\<exists>e\<in>E\<union>E\<inverse>. a = SAT_PUSH' e)" if "a\<in>set p" for a
    using IN_E that by (cases a) auto
  hence "length (filter is_SAT_PUSH' p) 
    = length (filter (\<lambda>a. \<exists>e\<in>E\<union>E\<inverse>. a = SAT_PUSH' e) p)" 
    by (auto cong: filter_cong)
  also have "\<dots> = (\<Sum>e\<in>E\<union>E\<inverse>. length (filter ((=) (SAT_PUSH' e)) p))" 
    by (auto simp: AUX)
  also have "\<dots> \<le> (\<Sum>i\<in>E \<union> E\<inverse>. 2 * card V)" 
    using sum_mono[OF sat_push_edge_action_bound'[OF A], where K="E\<union>E\<inverse>"] .
  also have "\<dots> \<le> 4 * card V * card E" using card_Un_le[of E "E\<inverse>"] by simp
  finally show "length (filter is_SAT_PUSH' p) \<le> 4 * card V * card E" .
qed    
  
end \<comment> \<open>Network\<close>  
  
subsubsection \<open>Bounding the Non-Saturating Push Operations\<close>    

text \<open>
  For estimating the number of non-saturating push operations, we
  define a potential function that is the sum of the labels of
  all active nodes, and examine the effect of the operations
  on this potential:
    \<^item> A non-saturating push deactivates the source node and may activate 
      the target node. As the source node's label is higher, the potential
      decreases.
    \<^item> A saturating push may activate a node, thus increasing the potential 
      by \<open>O(V)\<close>.
    \<^item> A relabel operation may increase the potential by \<open>O(V)\<close>.

  As there are at most \<open>O(V\<^sup>2)\<close> relabel and \<open>O(VE)\<close> saturating push operations,
  the above bounds suffice to yield an \<open>O(V\<^sup>2E)\<close> bound for the non-saturating 
  push operations.

  This argumentation corresponds to \cormen{26.23}.
\<close>  

text \<open>Sum of heights of all active nodes\<close>
definition (in Network) "nonsat_potential f l \<equiv> sum l {v\<in>V. excess f v > 0}"
  
context Height_Bounded_Labeling
begin
  
text \<open>The potential does not exceed \<open>O(V\<^sup>2)\<close>. \<close>  
lemma nonsat_potential_bound:
  shows "nonsat_potential f l \<le> 2 * (card V)^2"
proof -
  have "nonsat_potential f l = (\<Sum>v\<in>{v \<in> V. 0 < excess f v}. l v)" 
    unfolding nonsat_potential_def by auto
  also have "\<dots> \<le> (\<Sum>v\<in>V. l v)"
  proof -
    have f1:"{v \<in> V. 0 < excess f v} \<subseteq> V" by auto
    thus ?thesis using sum.subset_diff[OF f1 finite_V, of l] by auto
  qed
  also have "\<dots>  \<le> (\<Sum>v\<in>V. 2 * card V - 1)" 
    using height_bound by (meson sum_mono)
  also have "\<dots> = card V * (2 * card V - 1)" by auto
  also have "card V * (2 * card V - 1) \<le> 2 * card V * card V" by auto
  finally show ?thesis by (simp add: power2_eq_square)
qed
  
  
  
text \<open>A non-saturating push decreases the potential.\<close>  
lemma nonsat_push_decr_nonsat_potential:
  assumes "nonsat_push_precond f l e"
  shows "nonsat_potential (push_effect f e) l < nonsat_potential f l"  
proof (cases e)
  case [simp]: (Pair u v)
    
  show ?thesis 
  proof simp  
    interpret push_effect_locale c s t f l u v 
      apply unfold_locales using assms 
      by (simp add: push_precond_eq_sat_or_nonsat)
      
    note [simp] = nonsat_push_\<Delta>[OF assms[simplified]]
  
    define S where "S={x\<in>V. x\<noteq>u \<and> x\<noteq>v \<and> 0<excess f x}"
    have S_alt: "S = {x\<in>V. x\<noteq>u \<and> x\<noteq>v \<and> 0<excess f' x}"  
      unfolding S_def by auto
  
    have NES: "s\<notin>S" "u\<notin>S" "v\<notin>S" 
      and [simp, intro!]: "finite S" 
      unfolding S_def using excess_s_non_pos
      by auto 
      
    have 1: "{v\<in>V. 0 < excess f' v} = (if s=v then S else insert v S)"
      unfolding S_alt
      using excess_u_pos excess_non_negative' l'.excess_s_non_pos
      by (auto intro!: add_nonneg_pos)
        
    have 2: "{v\<in>V. 0 < excess f v} 
      = insert u S \<union> (if excess f v>0 then {v} else {})"    
      unfolding S_def using excess_u_pos by auto  
  
    show "nonsat_potential f' l < nonsat_potential f l"
      unfolding nonsat_potential_def 1 2
      by (cases "s=v"; cases "0<excess f v"; auto simp: NES)
  qed      
qed
  
  
text \<open>A saturating push increases the potential by \<open>O(V)\<close>.\<close>
lemma sat_push_nonsat_potential:
  assumes PRE: "sat_push_precond f l e"
  shows "nonsat_potential (push_effect f e) l 
      \<le> nonsat_potential f l + 2 * card V"
proof - 
  obtain u v where [simp]: "e = (u, v)" by (cases e) auto   
  
  interpret push_effect_locale c s t f l u v
    using PRE
    by unfold_locales (simp add: push_precond_eq_sat_or_nonsat)

  have [simp, intro!]: "finite {v\<in>V. excess f v > 0}"
    by auto
      
  text \<open>Only target node may get activated\<close>
  have "{v\<in>V. excess f' v > 0} \<subseteq> insert v {v\<in>V. excess f v > 0}"    
    using \<Delta>_positive
    by (auto simp: excess'_if)
  text \<open>Thus, potential increases by at most \<open>l v\<close>\<close>    
  with sum_mono2[OF _ this, of l]
  have "nonsat_potential f' l \<le> nonsat_potential f l + l v"
    unfolding nonsat_potential_def 
    by (auto simp: sum.insert_if split: if_splits)
  text \<open>Which is bounded by \<open>O(V)\<close>\<close>    
  also note height_bound'[of v]
  finally show ?thesis by simp
qed

  
text \<open>A relabeling increases the potential by at most \<open>O(V)\<close>\<close>
lemma relabel_nonsat_potential:
  assumes PRE: "relabel_precond f l u"
  shows "nonsat_potential f (relabel_effect f l u) 
       \<le> nonsat_potential f l + 2 * card V"
proof -  
  have [simp, intro!]: "finite {v\<in>V. excess f v > 0}"
    by auto
  
  let ?l' = "relabel_effect f l u"
      
  interpret l': Height_Bounded_Labeling c s t f ?l'
    using relabel_pres_height_bound[OF assms] .
      
  from PRE have U_ACTIVE: "u \<in> {v\<in>V. excess f v > 0}" and [simp]: "u\<in>V"
    unfolding relabel_precond_def using excess_nodes_only
    by auto
      
  have "nonsat_potential f ?l' 
      = sum ?l' ({v \<in> V. 0 < excess f v} - {u}) + ?l' u"    
    unfolding nonsat_potential_def
    using U_ACTIVE by (auto intro: sum_arb)
  also have "sum ?l' ({v \<in> V. 0 < excess f v} - {u}) 
      = sum l ({v \<in> V. 0 < excess f v} - {u})"
    using relabel_preserve_other by auto
  also have "?l' u \<le> l u + 2*card V"    
    using l'.height_bound'[OF \<open>u\<in>V\<close>] by auto
  finally have "nonsat_potential f ?l' 
              \<le> sum l ({v \<in> V. 0 < excess f v} - {u}) + l u + 2 * card V"
    by auto
  also have "sum l ({v \<in> V. 0 < excess f v} - {u}) + l u 
           = nonsat_potential f l"    
    unfolding nonsat_potential_def
    using U_ACTIVE by (auto intro: sum_arb[symmetric])
  finally show ?thesis .   
qed  

end \<comment> \<open>Height Bounded Labeling\<close>  
  
context Network 
begin
  
lemma nonsat_push_action_bound':
  assumes A: "((f,l),p,(f',l')) \<in> trcl pr_algo_lts'"
  shows "length (filter is_NONSAT_PUSH' p) \<le> 18 * (card V)\<^sup>2 * card E"
proof -
  have B1: "length (filter is_NONSAT_PUSH' p) 
    \<le>   nonsat_potential f l 
      + 2 * card V * (length (filter is_SAT_PUSH' p))
      + 2 * card V * (length (filter is_RELABEL' p))"
    using A
  proof (induction p arbitrary: f l)    
    case Nil thus ?case by auto
  next
    case [simp]: (Cons a p)
    then obtain fh lh 
      where FIRST: "((f,l),a,(fh,lh))\<in>pr_algo_lts'" 
          and PP: "((fh,lh),p,(f',l')) \<in> trcl pr_algo_lts'"
      by (auto simp: trcl_conv)  
    note IH = Cons.IH[OF PP]
  
    from FIRST interpret Height_Bounded_Labeling c s t f l 
      by cases auto
      
    show ?case using FIRST IH
      apply (cases a)
      apply (auto 
          elim!: pr_algo_lts'.cases 
          dest!: relabel_nonsat_potential nonsat_push_decr_nonsat_potential 
          dest!: sat_push_nonsat_potential
      )
      done
  qed
  
  
  
  (* TODO: Technical case distinction, as we do not assume invariant on f,l! *)
  show ?thesis proof (cases p)
    case Nil thus ?thesis by simp
  next
    case (Cons a' p')
    then interpret Height_Bounded_Labeling c s t f l using A
      by (auto simp: trcl_conv elim!: pr_algo_lts'.cases)
    note B1  
    also note nonsat_potential_bound  
    also note sat_push_action_bound'[OF A]
    also note relabel_action_bound'[OF A]
    finally have "length (filter is_NONSAT_PUSH' p)
      \<le> 2 * (card V)\<^sup>2 + 8 * (card V)\<^sup>2 * card E + 4 * (card V)^3"  
      by (simp add: power2_eq_square power3_eq_cube)
    also have "(card V)^3 \<le> 2 * (card V)\<^sup>2 * card E"  
      by (simp add: card_V_est_E power2_eq_square power3_eq_cube)
    finally have "length (filter is_NONSAT_PUSH' p) 
      \<le> 2 * (card V)\<^sup>2 + 16 * (card V)\<^sup>2 * card E"
      by linarith
    also have "2 * (card V)\<^sup>2 \<le> 2*(card V)\<^sup>2 * card E" by auto
    finally show "length (filter is_NONSAT_PUSH' p) \<le> 18 * (card V)\<^sup>2 * card E"
      by linarith
  qed
qed    
        
end \<comment> \<open>Network\<close>  
        
subsubsection \<open>Assembling the Final Theorem\<close>
  
text \<open>We combine the bounds for saturating and non-saturating push 
  operations.\<close>
lemma (in Height_Bounded_Labeling) push_action_bound:
  assumes A: "((f,l),p,(f',l')) \<in> trcl pr_algo_lts"
  shows "length (filter (is_PUSH) p) \<le> 22 * (card V)\<^sup>2 * card E"
  apply (rule order_trans[OF xfer_push_bounds[OF _ _ A]]; (intro allI impI)?)  
    apply (erule sat_push_action_bound'; fail)
    apply (erule nonsat_push_action_bound'; fail)
    apply (auto simp: power2_eq_square)
  done

text \<open>We estimate the cost of a push by \<open>O(1)\<close>, and of 
  a relabel operation by \<open>O(V)\<close>\<close>
    
fun (in Network) cost_estimate :: "pr_operation \<Rightarrow> nat" where
  "cost_estimate RELABEL = card V"
| "cost_estimate PUSH = 1"  
  
text \<open>We show the complexity bound of \<open>O(V\<^sup>2E)\<close> when starting from any valid
  labeling \cormen{26.24}.\<close>  
theorem (in Height_Bounded_Labeling) pr_algo_cost_bound:  
  assumes A: "((f,l),p,(f',l')) \<in> trcl pr_algo_lts"
  shows "(\<Sum>a\<leftarrow>p. cost_estimate a) \<le> 26 * (card V)^2 * card E"
proof -
  have "(\<Sum>a\<leftarrow>p. cost_estimate a) 
    = card V * length (filter is_RELABEL p) + length (filter is_PUSH p)"
  proof (induction p)
    case Nil
    then show ?case by simp
  next
    case (Cons a p)
    then show ?case by (cases a) auto
  qed  
  also have "card V * length (filter is_RELABEL p) \<le> 2 * (card V)^3"  
    using relabel_action_bound[OF A] 
    by (auto simp: power2_eq_square power3_eq_cube) 
  also note push_action_bound[OF A]
  finally have "sum_list (map cost_estimate p) 
              \<le> 2 * card V ^ 3 + 22 * (card V)\<^sup>2 * card E"
    by simp
  also have "(card V)^3 \<le> 2 * (card V)\<^sup>2 * card E"  
    by (simp add: card_V_est_E power2_eq_square power3_eq_cube)
  finally show ?thesis by linarith     
qed      
      
subsection \<open>Main Theorem: Correctness and Complexity\<close>  
text \<open>Finally, we state the main theorem of this section:
  If the algorithm executes some steps from the beginning, then
    \<^enum> If no further steps are possible from the reached state, we have 
      computed a maximum flow~\cormen{26.18}.
    \<^enum> The cost of these steps is bounded by \<open>O(V\<^sup>2E)\<close>~\cormen{26.24}. 
      Note that this also implies termination.
\<close>  
theorem (in Network) generic_preflow_push_OV2E_and_correct:
  assumes A: "((pp_init_f, pp_init_l), p, (f, l)) \<in> trcl pr_algo_lts" 
  shows "(\<Sum>x\<leftarrow>p. cost_estimate x) \<le> 26 * (card V)^2 * card E" (is ?G1)
    and "(f,l)\<notin>Domain pr_algo_lts \<longrightarrow> isMaxFlow f" (is ?G2)
proof -
  show ?G1 
    using pp_init_height_bound Height_Bounded_Labeling.pr_algo_cost_bound A 
    by blast
  
  show ?G2 
    proof -
    from A interpret Height_Bounded_Labeling c s t f l
      apply (induction p arbitrary: f l rule: rev_induct)
      apply (auto 
        simp: pp_init_height_bound trcl_conv 
        intro: Height_Bounded_Labeling.pr_algo_maintains_hb_labeling)  
      done      
    from pr_algo_term_maxflow show ?G2 by simp
  qed      
qed    
  
subsection \<open>Convenience Tools for Implementation\<close>  
  
context Network
begin
text \<open>In order to show termination of the algorithm, 
  we only need a well-founded relation over push and relabel steps\<close>
  
inductive_set pr_algo_rel where
  push: "\<lbrakk>Height_Bounded_Labeling c s t f l; push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((push_effect f e,l),(f,l))\<in>pr_algo_rel"
| relabel: "\<lbrakk>Height_Bounded_Labeling c s t f l; relabel_precond f l u\<rbrakk>
    \<Longrightarrow> ((f,relabel_effect f l u),(f,l))\<in>pr_algo_rel"

lemma pr_algo_rel_alt: "pr_algo_rel = 
    { ((push_effect f e,l),(f,l)) | f e l. 
        Height_Bounded_Labeling c s t f l \<and> push_precond f l e }
  \<union> { ((f, relabel_effect f l u), (f,l)) | f u l. 
        Height_Bounded_Labeling c s t f l \<and> relabel_precond f l u }"  
  by (auto elim!: pr_algo_rel.cases intro: pr_algo_rel.intros)
  
  
definition "pr_algo_len_bound \<equiv> 2 * (card V)\<^sup>2 + 22 * (card V)\<^sup>2 * card E"
  
lemma (in Height_Bounded_Labeling) pr_algo_lts_length_bound:  
  assumes A: "((f, l), p, (f', l')) \<in> trcl pr_algo_lts"
  shows "length p \<le> pr_algo_len_bound"
proof -
  have "length p = length (filter is_PUSH p) + length (filter is_RELABEL p)"
  proof (induction p)
    case Nil then show ?case by simp
  next
    case (Cons a p) then show ?case by (cases a) auto
  qed  
  also note push_action_bound[OF A]
  also note relabel_action_bound[OF A]
  finally show ?thesis unfolding pr_algo_len_bound_def by simp 
qed    
    
lemma (in Height_Bounded_Labeling) path_set_finite:  
  "finite {p. \<exists>f' l'. ((f,l),p,(f',l')) \<in> trcl pr_algo_lts}"
proof -  
  have FIN_OPS: "finite (UNIV::pr_operation set)"
    apply (rule finite_subset[where B="{PUSH,RELABEL}"])
    using pr_operation.exhaust by auto 
    
  have "{p. \<exists>f' l'. ((f,l),p,(f',l')) \<in> trcl pr_algo_lts} 
    \<subseteq> {p. length p \<le> pr_algo_len_bound}"  
    by (auto simp: pr_algo_lts_length_bound)
  also note finite_lists_length_le[OF FIN_OPS, simplified]
  finally (finite_subset) show ?thesis .
qed  
  
definition "pr_algo_measure 
  \<equiv> \<lambda>(f,l). Max {length p |p. \<exists>aa ba. ((f, l), p, aa, ba) \<in> trcl pr_algo_lts}"  
  
lemma pr_algo_measure: 
  assumes "(fl',fl) \<in> pr_algo_rel"  
  shows "pr_algo_measure fl' < pr_algo_measure fl"
  using assms  
proof (cases fl'; cases fl; simp)
  fix f l f' l'
  assume A: "((f',l'),(f,l)) \<in> pr_algo_rel"  
  then obtain a where LTS_STEP: "((f,l),a,(f',l'))\<in>pr_algo_lts"
    by cases (auto intro: pr_algo_lts.intros)  
      
  from A interpret Height_Bounded_Labeling c s t f l by cases auto    
  from pr_algo_maintains_hb_labeling[OF LTS_STEP] 
  interpret f': Height_Bounded_Labeling c s t f' l' .

  let ?S1 = "{length p |p. \<exists>fx lx. ((f, l), p, fx, lx) \<in> trcl pr_algo_lts}"    
  let ?S2 = "{length p |p. \<exists>fx lx. ((f', l'), p, fx, lx) \<in> trcl pr_algo_lts}"    

  have "finite ?S1" using finite_image_set path_set_finite by blast 
  moreover have "?S1 \<noteq> {}" by (auto intro: exI[where x="[]"])   
  ultimately obtain p fx lx where 
    "length p = Max ?S1" 
    "((f, l), p, fx, lx) \<in> trcl pr_algo_lts"
    apply -
    apply (drule (1) Max_in)
    by auto 

  have "finite ?S2" using finite_image_set f'.path_set_finite by blast 
  have "?S2 \<noteq> {}" by (auto intro: exI[where x="[]"])
  {
    assume MG: "Max ?S2 \<ge> Max ?S1"
  
    from Max_in[OF \<open>finite ?S2\<close> \<open>?S2\<noteq>{}\<close>] obtain p fx lx where  
      "length p = Max ?S2" 
      "((f', l'), p, fx, lx) \<in> trcl pr_algo_lts"
      by auto
    with MG LTS_STEP have
      LEN: "length (a#p) > Max ?S1"
      and P: "((f,l),a#p,(fx,lx)) \<in> trcl pr_algo_lts"
      by (auto simp: trcl_conv)  
    from P have "length (a#p) \<in> ?S1" by blast
    from Max_ge[OF \<open>finite ?S1\<close> this] LEN have False by simp   
  } thus "pr_algo_measure (f', l') < pr_algo_measure (f, l)"
    unfolding pr_algo_measure_def by (rule ccontr) auto
qed  

lemma wf_pr_algo_rel[simp, intro!]: "wf pr_algo_rel"  
  apply (rule wf_subset)
  apply (rule wf_measure[where f=pr_algo_measure])
  by (auto simp: pr_algo_measure)  
  
      
end \<comment> \<open>Network\<close>
  
subsection \<open>Gap Heuristics\<close>  
context Network
begin
text \<open>If we find a label value \<open>k\<close> that is assigned to no node,
  we may relabel all nodes \<open>v\<close> with \<open>k < l v < card V\<close> to \<open>card V + 1\<close>.
\<close>
definition "gap_precond l k \<equiv> \<forall>v\<in>V. l v \<noteq> k"
definition "gap_effect l k 
  \<equiv> \<lambda>v. if k<l v \<and> l v < card V then card V + 1 else l v"
  
text \<open>The gap heuristics preserves a valid labeling.\<close>  
lemma (in Labeling) gap_pres_Labeling:
  assumes PRE: "gap_precond l k"
  defines "l' \<equiv> gap_effect l k"
  shows "Labeling c s t f l'"
proof    
  from lab_src show "l' s = card V" unfolding l'_def gap_effect_def by auto
  from lab_sink show "l' t = 0" unfolding l'_def gap_effect_def by auto
  
  have l'_incr: "l' v \<ge> l v" for v unfolding l'_def gap_effect_def by auto
      
  fix u v
  assume A: "(u,v) \<in> cf.E"  
  hence "u\<in>V" "v\<in>V" using cfE_ss_invE E_ss_VxV by auto  
  thus "l' u \<le> l' v + 1"  
    unfolding l'_def gap_effect_def
    using valid[OF A] PRE 
    unfolding gap_precond_def 
    by auto
qed  

text \<open>The gap heuristics also preserves the height bounds.\<close>  
lemma (in Height_Bounded_Labeling) gap_pres_hb_labeling:
  assumes PRE: "gap_precond l k"
  defines "l' \<equiv> gap_effect l k"
  shows "Height_Bounded_Labeling c s t f l'"  
proof -  
  from gap_pres_Labeling[OF PRE] interpret Labeling c s t f l'
    unfolding l'_def .
  
  show ?thesis    
    apply unfold_locales
    unfolding l'_def gap_effect_def using height_bound by auto
qed  
  
text \<open>We combine the regular relabel operation with the gap heuristics:
  If relabeling results in a gap, the gap heuristics is applied immediately.
\<close>  
definition "gap_relabel_effect f l u \<equiv> let l' = relabel_effect f l u in
  if (gap_precond l' (l u)) then gap_effect l' (l u) else l'
"  

text \<open>The combined gap-relabel operation preserves a valid labeling.\<close>  
lemma (in Labeling) gap_relabel_pres_Labeling:
  assumes PRE: "relabel_precond f l u"
  defines "l' \<equiv> gap_relabel_effect f l u"
  shows "Labeling c s t f l'"
  unfolding l'_def gap_relabel_effect_def
  using relabel_pres_Labeling[OF PRE] Labeling.gap_pres_Labeling
  by (fastforce simp: Let_def)
  
text \<open>The combined gap-relabel operation preserves the height-bound.\<close>  
lemma (in Height_Bounded_Labeling) gap_relabel_pres_hb_labeling:
  assumes PRE: "relabel_precond f l u"
  defines "l' \<equiv> gap_relabel_effect f l u"
  shows "Height_Bounded_Labeling c s t f l'"  
  unfolding l'_def gap_relabel_effect_def
  using relabel_pres_height_bound[OF PRE] Height_Bounded_Labeling.gap_pres_hb_labeling
  by (fastforce simp: Let_def)

subsubsection \<open>Termination with Gap Heuristics\<close>    
text \<open>
  Intuitively, the algorithm with the gap heuristics terminates because 
  relabeling according to the gap heuristics preserves the invariant and 
  increases some labels towards their upper bound. 

  Formally, the simplest way is to combine a heights measure function with
  the already established measure for the standard algorithm:
\<close>    
lemma (in Height_Bounded_Labeling) gap_measure:
  assumes "gap_precond l k"
  shows "sum_heights_measure (gap_effect l k) \<le> sum_heights_measure l"
  unfolding gap_effect_def sum_heights_measure_def
  by (auto intro!: sum_mono)  
  
lemma (in Height_Bounded_Labeling) gap_relabel_measure:
  assumes PRE: "relabel_precond f l u"
  shows "sum_heights_measure (gap_relabel_effect f l u) < sum_heights_measure l"
  unfolding gap_relabel_effect_def
  using relabel_measure[OF PRE] relabel_pres_height_bound[OF PRE] Height_Bounded_Labeling.gap_measure
  by (fastforce simp: Let_def)
    
text \<open>Analogously to @{const pr_algo_rel}, we provide a well-founded relation 
  that over-approximates the steps of a push-relabel algorithm with gap 
  heuristics.
\<close>    
inductive_set gap_algo_rel where
  push: "\<lbrakk>Height_Bounded_Labeling c s t f l; push_precond f l e\<rbrakk> 
    \<Longrightarrow> ((push_effect f e,l),(f,l))\<in>gap_algo_rel"
| relabel: "\<lbrakk>Height_Bounded_Labeling c s t f l; relabel_precond f l u\<rbrakk>
    \<Longrightarrow> ((f,gap_relabel_effect f l u),(f,l))\<in>gap_algo_rel"
  
lemma wf_gap_algo_rel[simp, intro!]: "wf gap_algo_rel"  
proof -
  have "gap_algo_rel \<subseteq> inv_image (less_than <*lex*> less_than) (\<lambda>(f,l). (sum_heights_measure l, pr_algo_measure (f,l)))"
    using pr_algo_measure  
    using Height_Bounded_Labeling.gap_relabel_measure  
    by (fastforce elim!: gap_algo_rel.cases intro: pr_algo_rel.intros )
  thus ?thesis
    by (rule_tac wf_subset; auto)
qed  
  
end \<comment> \<open>Network\<close>
  
  
end
