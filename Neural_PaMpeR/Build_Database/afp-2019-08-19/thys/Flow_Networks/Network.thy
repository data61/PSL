section \<open>Flows, Cuts, and Networks\<close>
theory Network
imports Graph
begin
text \<open>
  In this theory, we define the basic concepts of flows, cuts, 
  and (flow) networks.
  \<close>  

subsection \<open>Definitions\<close>

subsubsection \<open>Flows\<close>

text \<open>An \<open>s\<close>-\<open>t\<close> preflow on a graph is a labeling of the edges with 
  values from a linearly ordered integral domain, such that: 
  \begin{description}
    \item[capacity constraint] the flow on each edge is non-negative and 
      does not exceed the edge's capacity;
    \item[non-deficiency constraint] for all nodes except \<open>s\<close> and \<open>t\<close>, 
      the incoming flow greater or equal to the outgoing flow.
  \end{description}    
\<close>
  
type_synonym 'capacity flow = "edge \<Rightarrow> 'capacity"

locale Preflow = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s t :: node
  fixes f :: "'capacity flow"  
  (* TODO: Move \<forall>-quantifiers to meta-level!? *)
  assumes capacity_const: "\<forall>e. 0 \<le> f e \<and> f e \<le> c e"
  assumes no_deficient_nodes: "\<forall>v \<in> V-{s,t}.
    (\<Sum>e\<in>outgoing v. f e) \<le> (\<Sum>e\<in>incoming v. f e)" 
begin
end  
  
  
text \<open>An \<open>s\<close>-\<open>t\<close> \<^emph>\<open>flow\<close> on a graph is a preflow that has no active nodes except 
  source and sink, where a node is \<^emph>\<open>active\<close> iff it has more incoming flow 
  than outgoing flow.
\<close>

locale Flow = Preflow c s t f
  for c :: "'capacity::linordered_idom graph"
  and s t :: node
  and f +
  assumes no_active_nodes: 
    "\<forall>v \<in> V - {s,t}. (\<Sum>e\<in>outgoing v. f e) \<ge> (\<Sum>e\<in>incoming v. f e)"
begin
  text \<open>For a flow, inflow equals outflow for all nodes except sink and source.
    This is called \<^emph>\<open>conservation\<close>. \<close>
  lemma conservation_const: 
    "\<forall>v \<in> V - {s, t}. (\<Sum>e \<in> incoming v. f e) = (\<Sum>e \<in> outgoing v. f e)"
    using no_deficient_nodes no_active_nodes 
    by force
  
  text \<open>The value of a flow is the flow that leaves $s$ and does not return.\<close>
  definition val :: "'capacity"
    where "val \<equiv> (\<Sum>e \<in> outgoing s. f e) - (\<Sum>e \<in> incoming s. f e)"
end

locale Finite_Preflow = Preflow c s t f + Finite_Graph c 
  for c :: "'capacity::linordered_idom graph" and s t f
  
locale Finite_Flow = Flow c s t f + Finite_Preflow c s t f
  for c :: "'capacity::linordered_idom graph" and s t f


subsubsection \<open>Cuts\<close>
text \<open>A \<^emph>\<open>cut\<close> is a partitioning of the nodes into two sets. 
  We define it by just specifying one of the partitions. 
  The other partition is implicitly given by the remaining nodes.\<close>
type_synonym cut = "node set" 

locale Cut = Graph +  (* TODO: We probably do not need the cut-locale, 
  only NCut.*)
  fixes k :: cut
  assumes cut_ss_V: "k \<subseteq> V"

subsubsection \<open>Networks\<close>
text \<open>A \<^emph>\<open>network\<close> is a finite graph with two distinct nodes, source and sink, 
  such that all edges are labeled with positive capacities. 
  Moreover, we assume that 
  \<^item> The source has no incoming edges, and the sink has no outgoing edges.
  \<^item> There are no parallel edges, i.e., for any edge, the reverse edge must not be in the network.
  \<^item> Every node must lay on a path from the source to the sink.

  Notes on the formalization
  \<^item> We encode the graph by a mapping \<open>c\<close>, such that \<open>c (u,v)\<close> is 
    the capacity of edge \<open>(u,v)\<close>, or \<open>0\<close>, if there is no edge from \<open>u\<close> to \<open>v\<close>.
    Thus, in the formalization below, we only demand 
    that \<open>c (u,v) \<ge> 0\<close> for all \<open>u\<close> and \<open>v\<close>.
  \<^item> We only demand the set of nodes reachable from the source to be finite.
    Together with the constraint that all nodes lay on a path from the source,
    this implies that the graph is finite.
\<close>

locale Network = Graph c for c :: "'capacity::linordered_idom graph" +
  fixes s t :: node
  assumes s_node[simp, intro!]: "s \<in> V"
  assumes t_node[simp, intro!]: "t \<in> V"
  assumes s_not_t[simp, intro!]: "s \<noteq> t"
    
  assumes cap_non_negative: "\<forall>u v. c (u, v) \<ge> 0"
  assumes no_incoming_s: "\<forall>u. (u, s) \<notin> E"
  assumes no_outgoing_t: "\<forall>u. (t, u) \<notin> E"
  assumes no_parallel_edge: "\<forall>u v. (u, v) \<in> E \<longrightarrow> (v, u) \<notin> E"
  assumes nodes_on_st_path: "\<forall>v \<in> V. connected s v \<and> connected v t"
  assumes finite_reachable: "finite (reachableNodes s)"
begin
  text \<open>Edges have positive capacity\<close>
  lemma edge_cap_positive: "(u,v)\<in>E \<Longrightarrow> c (u,v) > 0"
    unfolding E_def using cap_non_negative[THEN spec2, of u v] by simp
  
  text \<open>The network constraints implies that all nodes are 
    reachable from the source node\<close>  
  lemma reachable_is_V[simp]: "reachableNodes s = V"
  proof
    show "V \<subseteq> reachableNodes s"
    unfolding reachableNodes_def using s_node nodes_on_st_path
      by auto
  qed (simp add: reachable_ss_V)
  
  text \<open>Thus, the network is actually a finite graph.\<close>
  sublocale Finite_Graph 
    apply unfold_locales
    using reachable_is_V finite_reachable by auto
      
  
  text \<open>Our assumptions imply that there are no self loops\<close>
  lemma no_self_loop: "\<forall>u. (u, u) \<notin> E"
    using no_parallel_edge by auto

  lemma adjacent_not_self[simp, intro!]: "v \<notin> adjacent_nodes v"
    unfolding adjacent_nodes_def using no_self_loop 
    by auto
    

  text \<open>A flow is maximal, if it has a maximal value\<close>  
  definition isMaxFlow :: "_ flow \<Rightarrow> bool" 
  where "isMaxFlow f \<equiv> Flow c s t f \<and> 
    (\<forall>f'. Flow c s t f' \<longrightarrow> Flow.val c s f' \<le> Flow.val c s f)"
    
  definition "is_max_flow_val fv \<equiv> \<exists>f. isMaxFlow f \<and> fv=Flow.val c s f"

(* TODO: Can we prove existence of a maximum flow *easily*, i.e.,
  without going over the min-cut-max-flow theorem or the Ford-Fulkerson method?
  definition "max_flow_val \<equiv> THE fv. is_max_flow_val fv"
*)  
    
  lemma t_not_s[simp]: "t \<noteq> s" using s_not_t by blast

      
  text \<open>The excess of a node is the difference between incoming and 
    outgoing flow.\<close> (* TODO: Define in context of preflow!? *)
  definition excess :: "'capacity flow \<Rightarrow> node \<Rightarrow> 'capacity" where
    "excess f v \<equiv> (\<Sum>e\<in>incoming v. f e) - (\<Sum>e\<in>outgoing v. f e)"
  
end  
  
subsubsection \<open>Networks with Flows and Cuts\<close>  
text \<open>For convenience, we define locales for a network with a fixed flow,
  and a network with a fixed cut\<close>

locale NPreflow = Network c s t + Preflow c s t f 
  for c :: "'capacity::linordered_idom graph" and s t f
begin
  
end
    
locale NFlow = NPreflow c s t f + Flow c s t f 
  for c :: "'capacity::linordered_idom graph" and s t f

lemma (in Network) isMaxFlow_alt: 
  "isMaxFlow f \<longleftrightarrow> NFlow c s t f \<and> 
    (\<forall>f'. NFlow c s t f' \<longrightarrow> Flow.val c s f' \<le> Flow.val c s f)"
  unfolding isMaxFlow_def     
  by (auto simp: NFlow_def Flow_def NPreflow_def) intro_locales  

text \<open>A cut in a network separates the source from the sink\<close>
locale NCut = Network c s t + Cut c k 
  for c :: "'capacity::linordered_idom graph" and s t k +
  assumes s_in_cut: "s \<in> k"
  assumes t_ni_cut: "t \<notin> k"
begin
  text \<open>The capacity of the cut is the capacity of all edges going from the 
    source's side to the sink's side.\<close>
  definition cap :: "'capacity"
    where "cap \<equiv> (\<Sum>e \<in> outgoing' k. c e)"
end

text \<open>A minimum cut is a cut with minimum capacity.\<close> 
(* TODO: The definitions of min-cut and max-flow are done in different contexts. 
  Align, probably both in network context! *)
definition isMinCut :: "_ graph \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> cut \<Rightarrow> bool" 
where "isMinCut c s t k \<equiv> NCut c s t k \<and>
  (\<forall>k'. NCut c s t k' \<longrightarrow> NCut.cap c k \<le> NCut.cap c k')"

subsection \<open>Properties\<close>
subsubsection \<open>Flows\<close>

context Preflow 
begin

text \<open>Only edges are labeled with non-zero flows\<close>
lemma zero_flow_simp[simp]:
  "(u,v)\<notin>E \<Longrightarrow> f(u,v) = 0"
  by (metis capacity_const eq_iff zero_cap_simp)

lemma f_non_negative: "0 \<le> f e"
  using capacity_const by (cases e) auto
    
lemma sum_f_non_negative: "sum f X \<ge> 0" using capacity_const
  by (auto simp: sum_nonneg f_non_negative) 
    
end \<comment> \<open>Preflow\<close>   
    
context Flow
begin
text \<open>We provide a useful equivalent formulation of the 
  conservation constraint.\<close>
lemma conservation_const_pointwise: 
  assumes "u\<in>V - {s,t}"
  shows "(\<Sum>v\<in>E``{u}. f (u,v)) = (\<Sum>v\<in>E\<inverse>``{u}. f (v,u))"
  using conservation_const assms
  by (auto simp: sum_incoming_pointwise sum_outgoing_pointwise)

text \<open>The value of the flow is bounded by the capacity of the 
  outgoing edges of the source node\<close>
lemma val_bounded: 
  "-(\<Sum>e\<in>incoming s. c e) \<le> val"
  "val \<le> (\<Sum>e\<in>outgoing s. c e)"
proof -
  have 
    "sum f (outgoing s) \<le> sum c (outgoing s)"
    "sum f (incoming s) \<le> sum c (incoming s)"
    using capacity_const by (auto intro!: sum_mono)
  thus "-(\<Sum>e\<in>incoming s. c e) \<le> val" "val \<le> (\<Sum>e\<in>outgoing s. c e)" 
    using sum_f_non_negative[of "incoming s"] 
    using sum_f_non_negative[of "outgoing s"]  
    unfolding val_def by auto 
qed    
    
    
end \<comment> \<open>Flow\<close>   

text \<open>Introduce a flow via the conservation constraint\<close>  
lemma (in Graph) intro_Flow:
  assumes cap: "\<forall>e. 0 \<le> f e \<and> f e \<le> c e"
  assumes cons: "\<forall>v \<in> V - {s, t}. 
    (\<Sum>e \<in> incoming v. f e) = (\<Sum>e \<in> outgoing v. f e)"
  shows "Flow c s t f"  
  using assms by unfold_locales auto  
  
context Finite_Preflow 
begin

text \<open>The summation of flows over incoming/outgoing edges can be 
  extended to a summation over all possible predecessor/successor nodes,
  as the additional flows are all zero.\<close>  
lemma sum_outgoing_alt_flow:
  fixes g :: "edge \<Rightarrow> 'capacity"
  assumes "u\<in>V"
  shows "(\<Sum>e\<in>outgoing u. f e) = (\<Sum>v\<in>V. f (u,v))"
  apply (subst sum_outgoing_alt)
  using assms capacity_const
  by auto
  
lemma sum_incoming_alt_flow:
  fixes g :: "edge \<Rightarrow> 'capacity"
  assumes "u\<in>V"
  shows "(\<Sum>e\<in>incoming u. f e) = (\<Sum>v\<in>V. f (v,u))"
  apply (subst sum_incoming_alt)
  using assms capacity_const
  by auto
end \<comment> \<open>Finite Preflow\<close>   

subsubsection \<open>Networks\<close>  
context Network
begin
  
lemmas [simp] = no_incoming_s no_outgoing_t
  
lemma incoming_s_empty[simp]: "incoming s = {}"
  unfolding incoming_def using no_incoming_s by auto
  
lemma outgoing_t_empty[simp]: "outgoing t = {}"
  unfolding outgoing_def using no_outgoing_t by auto
  
  
lemma cap_positive: "e \<in> E \<Longrightarrow> c e > 0"
  unfolding E_def using cap_non_negative le_neq_trans by fastforce 

lemma V_not_empty: "V\<noteq>{}" using s_node by auto
lemma E_not_empty: "E\<noteq>{}" using V_not_empty by (auto simp: V_def)
    
lemma card_V_ge2: "card V \<ge> 2"
proof -
  have "2 = card {s,t}" by auto
  also have "{s,t} \<subseteq> V" by auto
  hence "card {s,t} \<le> card V" by (rule_tac card_mono) auto
  finally show ?thesis .   
qed  
    
lemma zero_is_flow: "Flow c s t (\<lambda>_. 0)"
  using cap_non_negative by unfold_locales auto  

lemma max_flow_val_unique: 
  "\<lbrakk>is_max_flow_val fv1; is_max_flow_val fv2\<rbrakk> \<Longrightarrow> fv1=fv2"    
  unfolding is_max_flow_val_def isMaxFlow_def 
  by (auto simp: antisym)
  
end \<comment> \<open>Network\<close>

subsubsection \<open>Networks with Flow\<close>

context NPreflow 
begin

sublocale Finite_Preflow by unfold_locales

text \<open>As there are no edges entering the source/leaving the sink, 
  also the corresponding flow values are zero:\<close>
lemma no_inflow_s: "\<forall>e \<in> incoming s. f e = 0" (is ?thesis)
proof (rule ccontr)
  assume "\<not>(\<forall>e \<in> incoming s. f e = 0)"
  then obtain e where obt1: "e \<in> incoming s \<and> f e \<noteq> 0" by blast
  then have "e \<in> E" using incoming_def by auto
  thus "False" using obt1 no_incoming_s incoming_def by auto
qed
  
lemma no_outflow_t: "\<forall>e \<in> outgoing t. f e = 0"
proof (rule ccontr)
  assume "\<not>(\<forall>e \<in> outgoing t. f e = 0)"
  then obtain e where obt1: "e \<in> outgoing t \<and> f e \<noteq> 0" by blast
  then have "e \<in> E" using outgoing_def by auto
  thus "False" using obt1 no_outgoing_t outgoing_def by auto
qed

text \<open>For an edge, there is no reverse edge, and thus, 
  no flow in the reverse direction:\<close>
lemma zero_rev_flow_simp[simp]: "(u,v)\<in>E \<Longrightarrow> f(v,u) = 0"
  using no_parallel_edge by auto

    
lemma excess_non_negative: "\<forall>v\<in>V-{s,t}. excess f v \<ge> 0"
  unfolding excess_def using no_deficient_nodes by auto
  
lemma excess_nodes_only: "excess f v > 0 \<Longrightarrow> v \<in> V"  
  unfolding excess_def incoming_def outgoing_def V_def 
  using sum.not_neutral_contains_not_neutral by fastforce
  
lemma excess_non_negative': "\<forall>v \<in> V - {s}. excess f v \<ge> 0"
proof -
  have "excess f t \<ge> 0" unfolding excess_def outgoing_def 
    by (auto simp: capacity_const sum_nonneg)
  thus ?thesis using excess_non_negative by blast
qed 

lemma excess_s_non_pos: "excess f s \<le> 0"
  unfolding excess_def
  by (simp add: capacity_const sum_nonneg)  
    
end \<comment> \<open>Network with preflow\<close>

context NFlow begin  
  sublocale Finite_Preflow by unfold_locales
      
  text \<open>There is no outflow from the sink in a network. 
    Thus, we can simplify the definition of the value:\<close>  
  corollary val_alt: "val = (\<Sum>e \<in> outgoing s. f e)"
    unfolding val_def by (auto simp: no_inflow_s)
      
end  
  
end \<comment> \<open>Theory\<close>
