section  \<open>Undirected Graphs\<close>
theory Undirected_Graph
imports
  Common
begin
subsection \<open>Nodes and Edges\<close>  

typedef 'v ugraph 
  = "{ (V::'v set , E). E \<subseteq> V\<times>V \<and> finite V \<and> sym E \<and> irrefl E }"
  unfolding sym_def irrefl_def by blast

setup_lifting type_definition_ugraph

lift_definition nodes_internal :: "'v ugraph \<Rightarrow> 'v set" is fst .
lift_definition edges_internal :: "'v ugraph \<Rightarrow> ('v\<times>'v) set" is snd .
lift_definition graph_internal :: "'v set \<Rightarrow> ('v\<times>'v) set \<Rightarrow> 'v ugraph" 
  is "\<lambda>V E. if finite V \<and> finite E then (V\<union>fst`E\<union>snd`E, (E\<union>E\<inverse>)-Id) else ({},{})"
  by (auto simp: sym_def irrefl_def; force)     

definition nodes :: "'v ugraph \<Rightarrow> 'v set" 
  where "nodes = nodes_internal" 
definition edges :: "'v ugraph \<Rightarrow> ('v\<times>'v) set" 
  where "edges = edges_internal" 
definition graph :: "'v set \<Rightarrow> ('v\<times>'v) set \<Rightarrow> 'v ugraph" 
  where "graph = graph_internal" 

lemma edges_subset: "edges g \<subseteq> nodes g \<times> nodes g"
  unfolding edges_def nodes_def by transfer auto

lemma nodes_finite[simp, intro!]: "finite (nodes g)"
  unfolding edges_def nodes_def by transfer auto
  
lemma edges_sym: "sym (edges g)"    
  unfolding edges_def nodes_def by transfer auto

lemma edges_irrefl: "irrefl (edges g)"      
  unfolding edges_def nodes_def by transfer auto

lemma nodes_graph: "\<lbrakk>finite V; finite E\<rbrakk> \<Longrightarrow> nodes (graph V E) = V\<union>fst`E\<union>snd`E"    
  unfolding edges_def nodes_def graph_def by transfer auto
  
lemma edges_graph: "\<lbrakk>finite V; finite E\<rbrakk> \<Longrightarrow> edges (graph V E) = (E\<union>E\<inverse>)-Id"    
  unfolding edges_def nodes_def graph_def by transfer auto

lemmas graph_accs = nodes_graph edges_graph  
  
lemma nodes_edges_graph_presentation: "\<lbrakk>finite V; finite E\<rbrakk> 
    \<Longrightarrow> nodes (graph V E) = V \<union> fst`E \<union> snd`E \<and> edges (graph V E) = E\<union>E\<inverse> - Id"
  by (simp add: graph_accs)
      
lemma graph_eq[simp]: "graph (nodes g) (edges g) = g"  
  unfolding edges_def nodes_def graph_def
  apply transfer
  unfolding sym_def irrefl_def
  apply (clarsimp split: prod.splits)
  by (fastforce simp: finite_subset)

lemma edges_finite[simp, intro!]: "finite (edges g)"
  using edges_subset finite_subset by fastforce
  
lemma graph_cases[cases type]: obtains V E 
  where "g = graph V E" "finite V" "finite E" "E\<subseteq>V\<times>V" "sym E" "irrefl E"  
proof -
  show ?thesis
    apply (rule that[of "nodes g" "edges g"]) 
    using edges_subset edges_sym edges_irrefl[of g]
    by auto
qed     

lemma graph_eq_iff: "g=g' \<longleftrightarrow> nodes g = nodes g' \<and> edges g = edges g'"  
  unfolding edges_def nodes_def graph_def by transfer auto

  
  
lemma edges_sym': "(u,v)\<in>edges g \<Longrightarrow> (v,u)\<in>edges g" using edges_sym 
  by (blast intro: symD)
  
lemma edges_irrefl'[simp,intro!]: "(u,u)\<notin>edges g"
  by (meson edges_irrefl irrefl_def)
  
lemma edges_irreflI[simp, intro]: "(u,v)\<in>edges g \<Longrightarrow> u\<noteq>v" by auto 
  
lemma edgesT_diff_sng_inv_eq[simp]: 
  "(edges T - {(x, y), (y, x)})\<inverse> = edges T - {(x, y), (y, x)}"
  using edges_sym' by fast
  
lemma nodesI[simp,intro]: assumes "(u,v)\<in>edges g" shows "u\<in>nodes g" "v\<in>nodes g"
  using assms edges_subset by auto
  
lemma split_edges_sym: "\<exists>E. E\<inter>E\<inverse> = {} \<and> edges g = E \<union> E\<inverse>"  
  using split_sym_rel[OF edges_sym edges_irrefl, of g] by metis

  
subsection \<open>Connectedness Relation\<close>  
  
lemma rtrancl_edges_sym': "(u,v)\<in>(edges g)\<^sup>* \<Longrightarrow> (v,u)\<in>(edges g)\<^sup>*"  
  by (simp add: edges_sym symD sym_rtrancl)
  
lemma trancl_edges_subset: "(edges g)\<^sup>+ \<subseteq> nodes g \<times> nodes g"  
  by (simp add: edges_subset trancl_subset_Sigma)
      
lemma find_crossing_edge:
  assumes "(u,v)\<in>E\<^sup>*" "u\<in>V" "v\<notin>V"
  obtains u' v' where "(u',v')\<in>E\<inter>V\<times>-V"
  using assms apply (induction rule: converse_rtrancl_induct)
  by auto


  

subsection \<open>Constructing Graphs\<close>
  
definition "graph_empty \<equiv> graph {} {}"
definition "ins_node v g \<equiv> graph (insert v (nodes g)) (edges g)"
definition "ins_edge e g \<equiv> graph (nodes g) (insert e (edges g))"
definition "graph_join g\<^sub>1 g\<^sub>2 \<equiv> graph (nodes g\<^sub>1 \<union> nodes g\<^sub>2) (edges g\<^sub>1 \<union> edges g\<^sub>2)"
definition "restrict_nodes g V \<equiv> graph (nodes g \<inter> V) (edges g \<inter> V\<times>V)"
definition "restrict_edges g E \<equiv> graph (nodes g) (edges g \<inter> (E\<union>E\<inverse>))"


definition "nodes_edges_consistent V E \<equiv> finite V \<and> irrefl E \<and> sym E \<and> E \<subseteq> V\<times>V"

lemma [simp]:
  assumes "nodes_edges_consistent V E"
  shows nodes_graph': "nodes (graph V E) = V" (is ?G1)
    and edges_graph': "edges (graph V E) = E" (is ?G2)
proof -
  from assms have [simp]: "finite E" unfolding nodes_edges_consistent_def
    by (meson finite_SigmaI rev_finite_subset) 

  show ?G1 ?G2 using assms
    by (auto simp: nodes_edges_consistent_def nodes_graph edges_graph irrefl_def)
    
qed    

lemma nec_empty[simp]: "nodes_edges_consistent {} {}" 
  by (auto simp: nodes_edges_consistent_def irrefl_def sym_def)

lemma graph_empty_accs[simp]:
  "nodes graph_empty = {}"
  "edges graph_empty = {}"
  unfolding graph_empty_def by (auto)  
  
lemma graph_empty[simp]: "graph {} {} = graph_empty"  
  by (simp add: graph_empty_def)
    
lemma nodes_empty_iff_empty[simp]: 
  "nodes G = {} \<longleftrightarrow> G=graph {} {}"
  "{} = nodes G \<longleftrightarrow> G=graph_empty"
  using edges_subset
  by (auto simp: graph_eq_iff)
  
lemma nodes_ins_nodes[simp]: "nodes (ins_node v g) = insert v (nodes g)"         
  and edges_ins_nodes[simp]: "edges (ins_node v g) = edges g"
  unfolding ins_node_def by (auto simp: graph_accs edges_sym')
  
  
lemma nodes_ins_edge[simp]: "nodes (ins_edge e g) = {fst e, snd e} \<union> nodes g"
  and edges_ins_edge: 
    "edges (ins_edge e g) 
      = (if fst e = snd e then edges g else {e,prod.swap e}\<union>(edges g))"
  unfolding ins_edge_def
  apply (all \<open>cases e\<close>)
  by (auto simp: graph_accs dest: edges_sym')
  
lemma edges_ins_edge'[simp]: 
  "u\<noteq>v \<Longrightarrow> edges (ins_edge (u,v) g) = {(u,v),(v,u)} \<union> edges g"
  by (auto simp: edges_ins_edge)

lemma edges_ins_edge_ss: "edges g \<subseteq> edges (ins_edge e g)"  
  by (auto simp: edges_ins_edge)
  
  
lemma nodes_join[simp]: "nodes (graph_join g\<^sub>1 g\<^sub>2) = nodes g\<^sub>1 \<union> nodes g\<^sub>2"  
  and edges_join[simp]: "edges (graph_join g\<^sub>1 g\<^sub>2) = edges g\<^sub>1 \<union> edges g\<^sub>2"
  unfolding graph_join_def
  by (auto simp: graph_accs dest: edges_sym')

lemma nodes_restrict_nodes[simp]: "nodes (restrict_nodes g V) = nodes g \<inter> V"  
  and edges_restrict_nodes[simp]: "edges (restrict_nodes g V) = edges g \<inter> V\<times>V"
  unfolding restrict_nodes_def
  by (auto simp: graph_accs dest: edges_sym')
  
lemma nodes_restrict_edges[simp]: "nodes (restrict_edges g E) = nodes g"
  and edges_restrict_edges[simp]: "edges (restrict_edges g E) = edges g \<inter> (E\<union>E\<inverse>)"
  unfolding restrict_edges_def
  by (auto simp: graph_accs dest: edges_sym')

lemma unrestricte_edges: "edges (restrict_edges g E) \<subseteq> edges g" by auto
lemma unrestrictn_edges: "edges (restrict_nodes g V) \<subseteq> edges g" by auto

lemma unrestrict_nodes: "nodes (restrict_edges g E) \<subseteq> nodes g" by auto



subsection \<open>Paths\<close>  
    
fun path where
  "path g u [] v \<longleftrightarrow> u=v"  
| "path g u (e#ps) w \<longleftrightarrow> (\<exists>v. e=(u,v) \<and> e\<in>edges g \<and> path g v ps w)"  

lemma path_emptyI[intro!]: "path g u [] u" by auto
    
lemma path_append[simp]: 
  "path g u (p1@p2) w \<longleftrightarrow> (\<exists>v. path g u p1 v \<and> path g v p2 w)" 
  by (induction p1 arbitrary: u) auto

lemma path_transs1[trans]:
  "path g u p v \<Longrightarrow> (v,w)\<in>edges g \<Longrightarrow> path g u (p@[(v,w)]) w"  
  "(u,v)\<in>edges g \<Longrightarrow> path g v p w \<Longrightarrow> path g u ((u,v)#p) w"
  "path g u p1 v \<Longrightarrow> path g v p2 w \<Longrightarrow> path g u (p1@p2) w"
  by auto
  
lemma path_graph_empty[simp]: "path graph_empty u p v \<longleftrightarrow> v=u \<and> p=[]" 
  by (cases p) auto

abbreviation "revp p \<equiv> rev (map prod.swap p)"
lemma revp_alt: "revp p = rev (map (\<lambda>(u,v). (v,u)) p)" by auto
  
lemma path_rev[simp]: "path g u (revp p) v \<longleftrightarrow> path g v p u"  
  by (induction p arbitrary: v) (auto dest: edges_sym')

lemma path_rev_sym[sym]: "path g v p u \<Longrightarrow> path g u (revp p) v" by simp 

lemma path_transs2[trans]: 
  "path g u p v \<Longrightarrow> (w,v)\<in>edges g \<Longrightarrow> path g u (p@[(v,w)]) w"  
  "(v,u)\<in>edges g \<Longrightarrow> path g v p w \<Longrightarrow> path g u ((u,v)#p) w"
  "path g u p1 v \<Longrightarrow> path g w p2 v \<Longrightarrow> path g u (p1@revp p2) w"
  by (auto dest: edges_sym')

  
lemma path_edges: "path g u p v \<Longrightarrow> set p \<subseteq> edges g"
  by (induction p arbitrary: u) auto

lemma path_graph_cong: 
  "\<lbrakk>path g\<^sub>1 u p v; set p \<subseteq> edges g\<^sub>1 \<Longrightarrow> set p \<subseteq> edges g\<^sub>2\<rbrakk> \<Longrightarrow> path g\<^sub>2 u p v"
  apply (frule path_edges; simp)
  apply (induction p arbitrary: u) 
  by auto    
  
                
lemma path_endpoints: 
  assumes "path g u p v" "p\<noteq>[]" shows "u\<in>nodes g" "v\<in>nodes g"
  subgoal using assms by (cases p) (auto intro: nodesI)
  subgoal using assms by (cases p rule: rev_cases) (auto intro: nodesI)
  done

lemma path_mono: "edges g \<subseteq> edges g' \<Longrightarrow> path g u p v \<Longrightarrow> path g' u p v"  
  by (meson path_edges path_graph_cong subset_trans)

  
  
lemmas unrestricte_path = path_mono[OF unrestricte_edges]
lemmas unrestrictn_path = path_mono[OF unrestrictn_edges]

lemma unrestrict_path_edges: "path (restrict_edges g E) u p v \<Longrightarrow> path g u p v"  
  by (induction p arbitrary: u) auto
  
lemma unrestrict_path_nodes: "path (restrict_nodes g E) u p v \<Longrightarrow> path g u p v"  
  by (induction p arbitrary: u) auto
  
      
  
subsubsection \<open>Paths and Connectedness\<close>  
  
lemma rtrancl_edges_iff_path: "(u,v)\<in>(edges g)\<^sup>* \<longleftrightarrow> (\<exists>p. path g u p v)"
  apply rule
  subgoal
    apply (induction rule: converse_rtrancl_induct)
    by (auto dest: path_transs1)
  apply clarify  
  subgoal for p by (induction p arbitrary: u; force)
  done  
  
lemma rtrancl_edges_pathE: 
  assumes "(u,v)\<in>(edges g)\<^sup>*" obtains p where "path g u p v"
  using assms by (auto simp: rtrancl_edges_iff_path)

lemma path_rtrancl_edgesD: "path g u p v \<Longrightarrow> (u,v)\<in>(edges g)\<^sup>*"
  by (auto simp: rtrancl_edges_iff_path)  
      
  
subsubsection \<open>Simple Paths\<close>  
  
definition "uedge \<equiv> \<lambda>(a,b). {a,b}"   
  
definition "simple p \<equiv> distinct (map uedge p)"  


lemma in_uedge_conv[simp]: "x\<in>uedge (u,v) \<longleftrightarrow> x=u \<or> x=v"
  by (auto simp: uedge_def)

lemma uedge_eq_iff: "uedge (a,b) = uedge (c,d) \<longleftrightarrow> a=c \<and> b=d \<or> a=d \<and> b=c"
  by (auto simp: uedge_def doubleton_eq_iff)
  
lemma uedge_degen[simp]: "uedge (a,a) = {a}"  
  by (auto simp: uedge_def)

lemma uedge_in_set_eq: "uedge (u, v) \<in> uedge ` S \<longleftrightarrow> (u,v)\<in>S \<or> (v,u)\<in>S"  
  by (auto simp: uedge_def doubleton_eq_iff)
  
lemma uedge_commute: "uedge (a,b) = uedge (b,a)" by auto 
      
lemma simple_empty[simp]: "simple []"
  by (auto simp: simple_def)

lemma simple_cons[simp]: "simple (e#p) \<longleftrightarrow> uedge e \<notin> uedge ` set p \<and> simple p"
  by (auto simp: simple_def)

lemma simple_append[simp]: "simple (p\<^sub>1@p\<^sub>2) 
  \<longleftrightarrow> simple p\<^sub>1 \<and> simple p\<^sub>2 \<and> uedge ` set p\<^sub>1 \<inter> uedge ` set p\<^sub>2 = {}"
  by (auto simp: simple_def)

  
lemma simplify_pathD:
  "path g u p v \<Longrightarrow> \<exists>p'. path g u p' v \<and> simple p' \<and> set p' \<subseteq> set p"
proof (induction p arbitrary: u v rule: length_induct)
  case A: (1 p)
  then show ?case proof (cases "simple p")
    assume "simple p" with A.prems show ?case by blast
  next
    assume "\<not>simple p"  
    then consider p\<^sub>1 a b p\<^sub>2 p\<^sub>3 where "p=p\<^sub>1@[(a,b)]@p\<^sub>2@[(a,b)]@p\<^sub>3"
                | p\<^sub>1 a b p\<^sub>2 p\<^sub>3 where "p=p\<^sub>1@[(a,b)]@p\<^sub>2@[(b,a)]@p\<^sub>3"
      by (auto 
        simp: simple_def map_eq_append_conv uedge_eq_iff 
        dest!: not_distinct_decomp)
    then obtain p' where "path g u p' v" "length p' < length p" "set p' \<subseteq> set p"
    proof cases
      case [simp]: 1
      from A.prems have "path g u (p\<^sub>1@[(a,b)]@p\<^sub>3) v" by auto
      from that[OF this] show ?thesis by auto
    next
      case [simp]: 2
      from A.prems have "path g u (p\<^sub>1@p\<^sub>3) v" by auto
      from that[OF this] show ?thesis by auto
    qed
    with A.IH show ?thesis by blast
  qed
qed  
    
lemma simplify_pathE: 
  assumes "path g u p v" 
  obtains p' where "path g u p' v" "simple p'" "set p' \<subseteq> set p"
  using assms by (auto dest: simplify_pathD)
   

subsubsection \<open>Splitting Paths\<close>  

lemma find_crossing_edge_on_path:
  assumes "path g u p v" "\<not>P u" "P v"
  obtains u' v' where "(u',v')\<in>set p" "\<not>P u'" "P v'"
  using assms by (induction p arbitrary: u) auto
  
lemma find_crossing_edges_on_path:  
  assumes P: "path g u p v" and "P u" "P v"
  obtains "\<forall>(u,v)\<in>set p. P u \<and> P v"
        | u\<^sub>1 v\<^sub>1 v\<^sub>2 u\<^sub>2 p\<^sub>1 p\<^sub>2 p\<^sub>3 
          where "p=p\<^sub>1@[(u\<^sub>1,v\<^sub>1)]@p\<^sub>2@[(u\<^sub>2,v\<^sub>2)]@p\<^sub>3" "P u\<^sub>1" "\<not>P v\<^sub>1" "\<not>P u\<^sub>2" "P v\<^sub>2"
proof (cases "\<forall>(u,v)\<in>set p. P u \<and> P v")
  case True with that show ?thesis by blast
next
  case False
  with P \<open>P u\<close> have "\<exists>(u\<^sub>1,v\<^sub>1)\<in>set p. P u\<^sub>1 \<and> \<not>P v\<^sub>1"
    apply clarsimp apply (induction p arbitrary: u) by auto
  then obtain u\<^sub>1 v\<^sub>1 where "(u\<^sub>1,v\<^sub>1)\<in>set p" and PRED1: "P u\<^sub>1" "\<not>P v\<^sub>1" by blast
  then obtain p\<^sub>1 p\<^sub>2\<^sub>3 where [simp]: "p=p\<^sub>1@[(u\<^sub>1,v\<^sub>1)]@p\<^sub>2\<^sub>3" 
    by (auto simp: in_set_conv_decomp)
  with P have "path g v\<^sub>1 p\<^sub>2\<^sub>3 v" by auto
  from find_crossing_edge_on_path[where P=P, OF this \<open>\<not>P v\<^sub>1\<close> \<open>P v\<close>] obtain u\<^sub>2 v\<^sub>2 
    where "(u\<^sub>2,v\<^sub>2)\<in>set p\<^sub>2\<^sub>3" "\<not>P u\<^sub>2" "P v\<^sub>2" .
  then show thesis using PRED1
    by (auto simp: in_set_conv_decomp intro: that)
qed      
  
lemma find_crossing_edge_rtrancl:
  assumes "(u,v)\<in>(edges g)\<^sup>*" "\<not>P u" "P v"
  obtains u' v' where "(u',v')\<in>edges g" "\<not>P u'" "P v'"
  using assms
  by (metis converse_rtrancl_induct)
  

lemma path_change: 
  assumes "u\<in>S" "v\<notin>S" "path g u p v" "simple p"
  obtains x y p1 p2 where 
    "(x,y) \<in> set p" "x \<in> S" "y \<notin> S"
    "path (restrict_edges g (-{(x,y),(y,x)})) u p1 x" 
    "path (restrict_edges g (-{(x,y),(y,x)})) y p2 v"
proof -
  from find_crossing_edge_on_path[where P="\<lambda>x. x\<notin>S"] assms obtain x y where 
    1: "(x,y)\<in>set p" "x\<in>S" "y\<notin>S" by blast
  then obtain p1 p2 where [simp]: "p=p1@[(x,y)]@p2" 
    by (auto simp: in_set_conv_decomp)
  
  let ?g' = "restrict_edges g (-{(x,y),(y,x)})"
  
  from \<open>path g u p v\<close> have P1: "path g u p1 x" and P2: "path g y p2 v" by auto
  from \<open>simple p\<close> 
    have "uedge (x,y)\<notin>set (map uedge p1)" "uedge (x,y)\<notin>set (map uedge p2)" 
  by auto
  then have "path ?g' u p1 x" "path ?g' y p2 v"  
    using path_graph_cong[OF P1, of ?g'] path_graph_cong[OF P2, of ?g']
    by (auto simp: uedge_in_set_eq)
  with 1 show ?thesis by (blast intro: that)
qed
      




subsection \<open>Cycles\<close>      
  
definition "cycle_free g \<equiv> \<nexists>p u. p\<noteq>[] \<and> simple p \<and> path g u p u"

lemma cycle_free_alt_in_nodes: 
  "cycle_free g \<equiv> \<nexists>p u. p\<noteq>[] \<and> u\<in>nodes g \<and> simple p \<and> path g u p u"
  by (smt cycle_free_def path_endpoints(2))

lemma cycle_freeI:
  assumes "\<And>p u. \<lbrakk> path g u p u; p\<noteq>[]; simple p \<rbrakk> \<Longrightarrow> False"
  shows "cycle_free g"
  using assms unfolding cycle_free_def by auto

lemma cycle_freeD:
  assumes "cycle_free g" "path g u p u" "p\<noteq>[]" "simple p" 
  shows False
  using assms unfolding cycle_free_def by auto

  
lemma cycle_free_antimono: "edges g \<subseteq> edges g' \<Longrightarrow> cycle_free g' \<Longrightarrow> cycle_free g"
  unfolding cycle_free_def
  by (auto dest: path_mono)

lemma cycle_free_empty[simp]: "cycle_free graph_empty" 
  unfolding cycle_free_def by auto
  
lemma cycle_free_no_edges: "edges g = {} \<Longrightarrow> cycle_free g"
  by (rule cycle_freeI) (auto simp: neq_Nil_conv)
  
lemma simple_path_cycle_free_unique:
  assumes CF: "cycle_free g" 
  assumes P: "path g u p v" "path g u p' v" "simple p" "simple p'"
  shows "p=p'"
  using P 
proof (induction p arbitrary: u p')
  case Nil
  then show ?case using cycle_freeD[OF CF] by auto
next
  case (Cons e p)
  
  note CF = cycle_freeD[OF CF]
  
  from Cons.prems obtain u' where 
    [simp]: "e=(u,u')" 
    and P': "(u,u')\<notin>set p" "(u',u)\<notin>set p" "(u,u')\<in>edges g"
    by (auto simp: uedge_in_set_eq)
  with Cons.prems obtain sp\<^sub>1 where 
    SP1: "path g u ((u,u')#sp\<^sub>1) v" "simple ((u,u')#sp\<^sub>1)" 
    by blast
  
  from Cons.prems obtain u'' p'' where 
    [simp]: "p' = (u,u'')#p''" 
    and P'': "(u,u'')\<notin>set p''" "(u'',u)\<notin>set p''" "(u,u'')\<in>edges g"
    apply (cases p')
    subgoal by auto (metis Cons.prems(1) Cons.prems(3) CF list.distinct(1))
    by (auto simp: uedge_in_set_eq)
  with Cons.prems obtain sp\<^sub>2 where 
    SP2: "path g u ((u,u'')#sp\<^sub>2) v" "simple ((u,u'')#sp\<^sub>2)" 
    by blast  
    
  have "u''=u'" proof (rule ccontr)
    assume [simp, symmetric, simp]: "u''\<noteq>u'"
    
    have AUX1: "(u,x)\<notin>set sp\<^sub>1" for x 
    proof 
      assume "(u, x) \<in> set sp\<^sub>1" 
      with SP1 obtain sp' where "path g u ((u,u')#sp') u" and "simple ((u,u')#sp')"
        by (clarsimp simp: in_set_conv_decomp; blast)
      with CF show False by blast
    qed  
    
    have AUX2:"(x,u)\<notin>set sp\<^sub>1" for x 
    proof 
      assume "(x, u) \<in> set sp\<^sub>1" 
      
      with SP1 obtain sp' where "path g u ((u,u')#sp') u" and "simple ((u,u')#sp')"
        apply (clarsimp simp: in_set_conv_decomp)
        (* TODO: Do more explicit, like other AUXes*)
        by (metis Cons.prems(1) Cons.prems(3) Un_iff 
        AUX1 \<open>e = (u, u')\<close> insert_iff list.simps(15) 
        path.elims(2) path.simps(2) prod.sel(2) set_append simple_cons)
      with CF show False by blast
    qed  
    
    have AUX3:"(u,x)\<notin>set sp\<^sub>2" for x 
    proof 
      assume "(u, x) \<in> set sp\<^sub>2" 
      then obtain sp' sp'' where [simp]: "sp\<^sub>2 = sp'@[(u,x)]@sp''"
        by (auto simp: in_set_conv_decomp)
      from SP2 have "path g u ((u,u'')#sp') u" "simple ((u,u'')#sp')" by auto
      with CF show False by blast
    qed    
    
    have AUX4:"(x,u)\<notin>set sp\<^sub>2" for x 
    proof 
      assume "(x, u) \<in> set sp\<^sub>2" 
      then obtain sp' sp'' where [simp]: "sp\<^sub>2 = sp'@[(x,u)]@sp''"
        by (auto simp: in_set_conv_decomp)
      from SP2 
        have "path g u ((u,u'')#sp'@[(x,u)]) u" "simple ((u,u'')#sp'@[(x,u)])" 
        by auto
      with CF show False by blast
    qed    
    
    have [simp]: "set (revp p) = (set p)\<inverse>" by auto
    
    from SP1 SP2 have "path g u' (sp\<^sub>1@revp sp\<^sub>2) u''" by auto
    then obtain sp where 
      SP: "path g u' sp u''" "simple sp" "set sp \<subseteq> set sp\<^sub>1 \<union> set (revp sp\<^sub>2)"
      by (erule_tac simplify_pathE) auto
    with \<open>(u,u')\<in>edges g\<close> \<open>(u,u'')\<in>edges g\<close> 
      have "path g u ((u,u')#sp@[(u'',u)]) u"
      by (auto dest: edges_sym' simp: uedge_eq_iff)
    moreover
    from SP SP1 SP2 AUX1 AUX2 AUX3 AUX4 have "simple (((u,u')#sp@[(u'',u)]))"
      by (auto 0 3 simp: uedge_eq_iff)
    ultimately show False using CF by blast  
  qed    

  with Cons.IH[of u' p''] Cons.prems show ?case by simp 
qed    
  
              
  
subsubsection \<open>Characterization by Removing Edge\<close>      



lemma cycle_free_alt: "cycle_free g 
  \<longleftrightarrow> (\<forall>e\<in>edges g. e\<notin>(edges (restrict_edges g (-{e,prod.swap e})))\<^sup>*)"
  apply (rule)
  apply (clarsimp simp del: edges_restrict_edges)
  subgoal premises prems for u v proof -
    note edges_restrict_edges[simp del]
    let ?rg = "(restrict_edges g (- {(u,v), (v,u)}))"
    from \<open>(u, v) \<in> (edges ?rg)\<^sup>*\<close>
    obtain p where P: "path ?rg u p v" and "simple p" 
      by (auto simp: rtrancl_edges_iff_path elim: simplify_pathE)
    from P have "path g u p v" by (rule unrestricte_path) 
    also note \<open>(u, v) \<in> edges g\<close> finally have "path g u (p @ [(v, u)]) u" .
    moreover from path_edges[OF P] have "uedge (u,v) \<notin> set (map uedge p)" 
      by (auto simp: uedge_eq_iff edges_restrict_edges)
    with \<open>simple p\<close> have "simple (p @ [(v, u)])"
      by (auto simp: uedge_eq_iff uedge_in_set_eq)
    ultimately show ?thesis using \<open>cycle_free g\<close>  
      unfolding cycle_free_def by blast
  qed
  apply (clarsimp simp: cycle_free_def)
  subgoal premises prems for p u proof -
    from \<open>p\<noteq>[]\<close> \<open>path g u p u\<close> obtain v p' where 
      [simp]: "p=(u,v)#p'" and "(u,v)\<in>edges g" "path g v p' u" 
      by (cases p) auto
    from \<open>simple p\<close> have "simple p'" "uedge (u,v) \<notin> set (map uedge p')" by auto  
    hence "(u,v)\<notin>set p'" "(v,u)\<notin>set p'" by (auto simp: uedge_in_set_eq)
    with \<open>path g v p' u\<close> 
      have "path (restrict_edges g (-{(u,v),(v,u)})) v p' u" (is "path ?rg _ _ _")
      by (erule_tac path_graph_cong) auto
      
    hence "(u,v)\<in>(edges ?rg)\<^sup>*"
      by (meson path_rev rtrancl_edges_iff_path)  
    with prems(1) \<open>(u,v)\<in>edges g\<close> show False by auto
  qed    
  done
  
lemma cycle_free_altI:
  assumes "\<And>u v. \<lbrakk> (u,v)\<in>edges g; (u,v)\<in>(edges g - {(u,v),(v,u)})\<^sup>* \<rbrakk> \<Longrightarrow> False"
  shows "cycle_free g"
  unfolding cycle_free_alt using assms by (force)
  
lemma cycle_free_altD:  
  assumes "cycle_free g"
  assumes "(u,v)\<in>edges g" 
  shows "(u,v)\<notin>(edges g - {(u,v),(v,u)})\<^sup>*"
  using assms unfolding cycle_free_alt by (auto)
  


lemma remove_redundant_edge:
  assumes "(u, v) \<in> (edges g - {(u, v), (v, u)})\<^sup>*"  
  shows "(edges g - {(u, v), (v, u)})\<^sup>* = (edges g)\<^sup>*" (is "?E'\<^sup>* = _")
proof  
  show "?E'\<^sup>* \<subseteq> (edges g)\<^sup>*"
    by (simp add: Diff_subset rtrancl_mono)
next
  show "(edges g)\<^sup>* \<subseteq> ?E'\<^sup>*"
  proof clarify
    fix a b assume "(a,b)\<in>(edges g)\<^sup>*" then 
    show "(a,b)\<in>?E'\<^sup>*"
    proof induction
      case base
      then show ?case by simp
    next
      case (step b c)
      then show ?case 
      proof (cases "(b,c)\<in>{(u,v),(v,u)}")
        case True

        have SYME: "sym (?E'\<^sup>*)"
          apply (rule sym_rtrancl)
          using edges_sym[of g] 
          by (auto simp: sym_def)
        with step.IH assms have 
          IH': "(b,a) \<in> ?E'\<^sup>*"
          by (auto intro: symD)
        
        from True show ?thesis apply safe
          subgoal using assms step.IH by simp
          subgoal using assms IH' apply (rule_tac symD[OF SYME]) by simp
          done
        
      next
        case False
        then show ?thesis
          by (meson DiffI rtrancl.rtrancl_into_rtrancl step.IH step.hyps(2))
      qed 
        
    qed
  qed
qed
  
  
  
  
  
subsection \<open>Connected Graphs\<close>  
  
  
definition connected 
  where "connected g \<equiv> nodes g \<times> nodes g \<subseteq> (edges g)\<^sup>*"  

lemma connectedI[intro?]: 
  assumes "\<And>u v. \<lbrakk>u\<in>nodes g; v\<in>nodes g\<rbrakk> \<Longrightarrow> (u,v)\<in>(edges g)\<^sup>*"  
  shows "connected g"
  using assms unfolding connected_def by auto
  
lemma connectedD[intro?]: 
  assumes "connected g" "u\<in>nodes g" "v\<in>nodes g"
  shows "(u,v)\<in>(edges g)\<^sup>*"  
  using assms unfolding connected_def by auto
  
lemma connected_empty[simp]: "connected graph_empty" 
  unfolding connected_def by auto

subsection \<open>Component Containing Node\<close>
definition "reachable_nodes g r \<equiv> (edges g)\<^sup>*``{r}"
definition "component_of g r 
  \<equiv> ins_node r (restrict_nodes g (reachable_nodes g r))"

lemma reachable_nodes_refl[simp, intro!]: "r \<in> reachable_nodes g r" 
  by (auto simp: reachable_nodes_def)
  
lemma reachable_nodes_step: 
  "edges g `` reachable_nodes g r \<subseteq> reachable_nodes g r"
  by (auto simp: reachable_nodes_def)

lemma reachable_nodes_steps: 
  "(edges g)\<^sup>* `` reachable_nodes g r \<subseteq> reachable_nodes g r"
  by (auto simp: reachable_nodes_def)

lemma reachable_nodes_step':
  assumes "u \<in> reachable_nodes g r" "(u, v) \<in> edges g" 
  shows "v\<in>reachable_nodes g r" "(u, v) \<in> edges (component_of g r)" 
proof -
  show "v \<in> reachable_nodes g r"
    by (meson ImageI assms(1) assms(2) reachable_nodes_step rev_subsetD)
  then show "(u, v) \<in> edges (component_of g r)"
    by (simp add: assms(1) assms(2) component_of_def)
qed
  
lemma reachable_nodes_steps':
  assumes "u \<in> reachable_nodes g r" "(u, v) \<in> (edges g)\<^sup>*" 
  shows "v\<in>reachable_nodes g r" "(u, v) \<in> (edges (component_of g r))\<^sup>*" 
proof -
  show "v\<in>reachable_nodes g r" using reachable_nodes_steps assms by fast
  show "(u, v) \<in> (edges (component_of g r))\<^sup>*"
    using assms(2,1)
    apply (induction rule: converse_rtrancl_induct)
    subgoal by auto
    subgoal by (smt converse_rtrancl_into_rtrancl reachable_nodes_step')
    done
qed
   
lemma reachable_not_node: "r\<notin>nodes g \<Longrightarrow> reachable_nodes g r = {r}"
  by (force elim: converse_rtranclE simp: reachable_nodes_def intro: nodesI)
   
  
lemma nodes_of_component[simp]: "nodes (component_of g r) = reachable_nodes g r"
  apply (rule equalityI)
  unfolding component_of_def reachable_nodes_def
  subgoal by auto
  subgoal by clarsimp (metis nodesI(2) rtranclE)
  done

lemma component_connected[simp, intro!]: "connected (component_of g r)"
proof (rule connectedI; simp)
  fix u v
  assume A: "u \<in> reachable_nodes g r" "v \<in> reachable_nodes g r"
  hence "(u,r)\<in>(edges g)\<^sup>*" "(r,v)\<in>(edges g)\<^sup>*" 
    by (auto simp: reachable_nodes_def dest: rtrancl_edges_sym')
  hence "(u,v)\<in>(edges g)\<^sup>*" by (rule rtrancl_trans)
  with A show "(u, v) \<in> (edges (component_of g r))\<^sup>*" 
    by (rule_tac reachable_nodes_steps'(2))
qed  

lemma component_edges_subset: "edges (component_of g r) \<subseteq> edges g"  
  by (auto simp: component_of_def)

lemma component_path: "u\<in>nodes (component_of g r) \<Longrightarrow> 
  path (component_of g r) u p v \<longleftrightarrow> path g u p v"  
  apply rule
  subgoal by (erule path_mono[OF component_edges_subset])     
  subgoal by (induction p arbitrary: u) (auto simp: reachable_nodes_step')
  done  
  
lemma component_cycle_free: "cycle_free g \<Longrightarrow> cycle_free (component_of g r)"  
  by (meson component_edges_subset cycle_free_antimono)
  
lemma component_of_connected_graph: 
  "\<lbrakk>connected g; r\<in>nodes g\<rbrakk> \<Longrightarrow> component_of g r = g"  
  unfolding graph_eq_iff 
  apply safe
  subgoal by simp (metis Image_singleton_iff nodesI(2) reachable_nodes_def rtranclE)
  subgoal by (simp add: connectedD reachable_nodes_def)
  subgoal by (simp add: component_of_def)
  subgoal by (simp add: connectedD reachable_nodes_def reachable_nodes_step'(2))
  done

lemma component_of_not_node: "r\<notin>nodes g \<Longrightarrow> component_of g r = graph {r} {}"
  by (clarsimp simp: graph_eq_iff component_of_def reachable_not_node graph_accs)

      
subsection \<open>Trees\<close>

definition "tree g \<equiv> connected g \<and> cycle_free g "    

lemma tree_empty[simp]: "tree graph_empty" by (simp add: tree_def)

lemma component_of_tree: "tree T \<Longrightarrow> tree (component_of T r)"
  unfolding tree_def using component_connected component_cycle_free by auto


subsubsection \<open>Joining and Splitting Trees on Single Edge\<close>
      
lemma join_connected:
  assumes CONN: "connected g\<^sub>1" "connected g\<^sub>2"
  assumes IN_NODES: "u\<in>nodes g\<^sub>1" "v\<in>nodes g\<^sub>2"
  shows "connected (ins_edge (u,v) (graph_join g\<^sub>1 g\<^sub>2))" (is "connected ?g'") 
  unfolding connected_def
proof clarify
  fix a b
  assume A: "a\<in>nodes ?g'" "b\<in>nodes ?g'"
  
  have ESS: "(edges g\<^sub>1)\<^sup>* \<subseteq> (edges ?g')\<^sup>*" "(edges g\<^sub>2)\<^sup>* \<subseteq> (edges ?g')\<^sup>*"
    using edges_ins_edge_ss
    by (force intro!: rtrancl_mono)+
  
  have UV: "(u,v)\<in>(edges ?g')\<^sup>*"
    by (simp add: edges_ins_edge r_into_rtrancl)
    
  show "(a,b)\<in>(edges ?g')\<^sup>*"
  proof -
    {
      assume "a\<in>nodes g\<^sub>1" "b\<in>nodes g\<^sub>1"
      hence ?thesis using \<open>connected g\<^sub>1\<close> ESS(1) unfolding connected_def by blast
    } moreover {
      assume "a\<in>nodes g\<^sub>2" "b\<in>nodes g\<^sub>2"
      hence ?thesis using \<open>connected g\<^sub>2\<close> ESS(2) unfolding connected_def by blast
    } moreover {
      assume "a\<in>nodes g\<^sub>1" "b\<in>nodes g\<^sub>2"
      with connectedD[OF CONN(1)] connectedD[OF CONN(2)] ESS
      have ?thesis by (meson UV IN_NODES contra_subsetD rtrancl_trans)
    } moreover {
      assume "a\<in>nodes g\<^sub>2" "b\<in>nodes g\<^sub>1"
      with connectedD[OF CONN(1)] connectedD[OF CONN(2)] ESS
      have ?thesis
        by (meson UV IN_NODES contra_subsetD rtrancl_edges_sym' rtrancl_trans)
    }
    ultimately show ?thesis using A IN_NODES by auto
  qed    
qed
  
  
lemma join_cycle_free:  
  assumes CYCF: "cycle_free g\<^sub>1" "cycle_free g\<^sub>2"
  assumes DJ: "nodes g\<^sub>1 \<inter> nodes g\<^sub>2 = {}"
  assumes IN_NODES: "u\<in>nodes g\<^sub>1" "v\<in>nodes g\<^sub>2"
  shows "cycle_free (ins_edge (u,v) (graph_join g\<^sub>1 g\<^sub>2))" (is "cycle_free ?g'") 
proof (rule cycle_freeI)
  fix p a
  assume P: "path ?g' a p a" "p\<noteq>[]" "simple p"
  from path_endpoints[OF this(1,2)] IN_NODES 
    have A_NODE: "a\<in>nodes g\<^sub>1 \<union> nodes g\<^sub>2" 
    by auto
  thus False proof 
    assume N1: "a\<in>nodes g\<^sub>1"
    have "set p \<subseteq> nodes g\<^sub>1 \<times> nodes g\<^sub>1"
    proof (cases 
      rule: find_crossing_edges_on_path[where P="\<lambda>x. x\<in>nodes g\<^sub>1", OF P(1) N1 N1])
      case 1
      then show ?thesis by auto
    next
      case (2 u\<^sub>1 v\<^sub>1 v\<^sub>2 u\<^sub>2 p\<^sub>1 p\<^sub>2 p\<^sub>3)
      then show ?thesis using \<open>simple p\<close> P
        apply clarsimp
        apply (drule path_edges)+
        apply (cases "u=v"; clarsimp simp: edges_ins_edge uedge_in_set_eq)
        apply (metis DJ IntI IN_NODES empty_iff)
        by (metis DJ IntI empty_iff nodesI uedge_eq_iff)
        
    qed
    hence "set p \<subseteq> edges g\<^sub>1" using DJ edges_subset path_edges[OF P(1)] IN_NODES
      by (auto simp: edges_ins_edge split: if_splits; blast)
    hence "path g\<^sub>1 a p a" by (meson P(1) path_graph_cong)
    thus False using cycle_freeD[OF CYCF(1)] P(2,3) by blast
  next
    assume N2: "a\<in>nodes g\<^sub>2"
    have "set p \<subseteq> nodes g\<^sub>2 \<times> nodes g\<^sub>2"
    proof (cases 
      rule: find_crossing_edges_on_path[where P="\<lambda>x. x\<in>nodes g\<^sub>2", OF P(1) N2 N2])
      case 1
      then show ?thesis by auto
    next
      case (2 u\<^sub>1 v\<^sub>1 v\<^sub>2 u\<^sub>2 p\<^sub>1 p\<^sub>2 p\<^sub>3)
      then show ?thesis using \<open>simple p\<close> P
        apply clarsimp
        apply (drule path_edges)+
        apply (cases "u=v"; clarsimp simp: edges_ins_edge uedge_in_set_eq)
        apply (metis DJ IntI IN_NODES empty_iff)
        by (metis DJ IntI empty_iff nodesI uedge_eq_iff)
        
    qed
    hence "set p \<subseteq> edges g\<^sub>2" using DJ edges_subset path_edges[OF P(1)] IN_NODES
      by (auto simp: edges_ins_edge split: if_splits; blast)
    hence "path g\<^sub>2 a p a" by (meson P(1) path_graph_cong)
    thus False using cycle_freeD[OF CYCF(2)] P(2,3) by blast
  qed
qed
      
lemma join_trees:     
  assumes TREE: "tree g\<^sub>1" "tree g\<^sub>2"
  assumes DJ: "nodes g\<^sub>1 \<inter> nodes g\<^sub>2 = {}"
  assumes IN_NODES: "u\<in>nodes g\<^sub>1" "v\<in>nodes g\<^sub>2"
  shows "tree (ins_edge (u,v) (graph_join g\<^sub>1 g\<^sub>2))"
  using assms join_cycle_free join_connected unfolding tree_def by metis 
  
  
lemma split_tree:
  assumes "tree T" "(x,y)\<in>edges T"
  defines "E' \<equiv> (edges T - {(x,y),(y,x)})"
  obtains T1 T2 where 
    "tree T1" "tree T2" 
    "nodes T1 \<inter> nodes T2 = {}" "nodes T = nodes T1 \<union> nodes T2"
    "edges T1 \<union> edges T2 = E'"
    "nodes T1 = { u. (x,u)\<in>E'\<^sup>*}" "nodes T2 = { u. (y,u)\<in>E'\<^sup>*}"
    "x\<in>nodes T1" "y\<in>nodes T2"
proof -
  (* TODO: Use component_of here! *)
  define N1 where "N1 = { u. (x,u)\<in>E'\<^sup>* }"
  define N2 where "N2 = { u. (y,u)\<in>E'\<^sup>* }"

  define T1 where "T1 = restrict_nodes T N1"
  define T2 where "T2 = restrict_nodes T N2"
  
  have SYME: "sym (E'\<^sup>*)"
    apply (rule sym_rtrancl) 
    using edges_sym[of T] by (auto simp: sym_def E'_def)
  

  from assms have "connected T" "cycle_free T" unfolding tree_def by auto
  from \<open>cycle_free T\<close> have "cycle_free T1" "cycle_free T2"
    unfolding T1_def T2_def
    using cycle_free_antimono unrestrictn_edges by blast+

  from \<open>(x,y) \<in> edges T\<close> have XYN: "x\<in>nodes T" "y\<in>nodes T" 
    using edges_subset by auto
  from XYN have [simp]: "nodes T1 = N1" "nodes T2 = N2" 
    unfolding T1_def T2_def N1_def N2_def unfolding E'_def
    apply (safe)
    apply (all \<open>clarsimp\<close>)
    by (metis DiffD1 nodesI(2) rtrancl.simps)+
  
  have "x\<in>N1" "y\<in>N2" by (auto simp: N1_def N2_def)   
  
  have "N1 \<inter> N2 = {}" 
  proof (safe;simp)
    fix u
    assume "u\<in>N1" "u\<in>N2"
    hence "(x,u)\<in>E'\<^sup>*" "(u,y)\<in>E'\<^sup>*" by (auto simp: N1_def N2_def symD[OF SYME])
    with cycle_free_altD[OF \<open>cycle_free T\<close> \<open>(x,y)\<in>edges T\<close>] show False 
      unfolding E'_def by (meson rtrancl_trans)
  qed

  
  have N1C: "E'``N1 \<subseteq> N1"
    unfolding N1_def
    apply clarsimp 
    by (simp add: rtrancl.rtrancl_into_rtrancl)
  
  have N2C: "E'``N2 \<subseteq> N2"
    unfolding N2_def
    apply clarsimp 
    by (simp add: rtrancl.rtrancl_into_rtrancl)

  have XE1: "(x,u) \<in> (edges T1)\<^sup>*" if "u\<in>N1" for u
  proof -
    from that have "(x,u)\<in>E'\<^sup>*" by (auto simp: N1_def)
    then show ?thesis using \<open>x\<in>N1\<close> 
      unfolding T1_def
    proof (induction rule: converse_rtrancl_induct)
      case (step y z)
      with N1C have "z\<in>N1" by auto
      with step.hyps(1) step.prems have "(y,z)\<in>Restr (edges T) N1" 
        unfolding E'_def by auto
      with step.IH[OF \<open>z\<in>N1\<close>] show ?case 
        by (metis converse_rtrancl_into_rtrancl edges_restrict_nodes)
    qed auto
  qed    
  
  have XE2: "(y,u) \<in> (edges T2)\<^sup>*" if "u\<in>N2" for u
  proof -
    from that have "(y,u)\<in>E'\<^sup>*" by (auto simp: N2_def)
    then show ?thesis using \<open>y\<in>N2\<close> 
      unfolding T2_def
    proof (induction rule: converse_rtrancl_induct)
      case (step y z)
      with N2C have "z\<in>N2" by auto
      with step.hyps(1) step.prems have "(y,z)\<in>Restr (edges T) N2" 
        unfolding E'_def by auto
      with step.IH[OF \<open>z\<in>N2\<close>] show ?case 
        by (metis converse_rtrancl_into_rtrancl edges_restrict_nodes)
    qed auto
  qed    
  
  
  have "connected T1" 
    apply rule
    apply simp
    apply (drule XE1)+
    by (meson rtrancl_edges_sym' rtrancl_trans)      
  
  have "connected T2" 
    apply rule
    apply simp
    apply (drule XE2)+
    by (meson rtrancl_edges_sym' rtrancl_trans)      
   
  have "u\<in>N1 \<union> N2" if "u\<in>nodes T" for u 
  proof -
    from connectedD[OF \<open>connected T\<close> \<open>x\<in>nodes T\<close> that ]
    obtain p where P: "path T x p u" "simple p" 
      by (auto simp: rtrancl_edges_iff_path elim: simplify_pathE)
    show ?thesis proof cases
      assume "(x,y)\<notin>set p \<and> (y,x)\<notin>set p"
      with P(1) have "path (restrict_edges T E') x p u" 
        unfolding E'_def by (erule_tac path_graph_cong) auto
      from path_rtrancl_edgesD[OF this]
      show ?thesis unfolding N1_def E'_def by auto
    next
      assume "\<not>((x,y)\<notin>set p \<and> (y,x)\<notin>set p)"
      with P obtain p' where 
        "uedge (x,y)\<notin>set (map uedge p')" "path T y p' u \<or> path T x p' u"
        by (auto simp: in_set_conv_decomp uedge_commute)
      hence "path (restrict_edges T E') y p' u \<or> path (restrict_edges T E') x p' u"  
        apply (clarsimp simp: uedge_in_set_eq E'_def)
        by (smt ComplD DiffI Int_iff UnCI edges_restrict_edges insertE 
                path_graph_cong subset_Compl_singleton subset_iff)
      then show ?thesis unfolding N1_def N2_def E'_def 
        by (auto dest: path_rtrancl_edgesD)
    qed
  qed
  then have "nodes T = N1 \<union> N2" 
    unfolding N1_def N2_def using XYN
    unfolding E'_def
    apply (safe)
    subgoal by auto []
    subgoal by (metis DiffD1 nodesI(2) rtrancl.cases)
    subgoal by (metis DiffD1 nodesI(2) rtrancl.cases)
    done

  have "edges T1 \<union> edges T2 \<subseteq> E'"
    unfolding T1_def T2_def E'_def using \<open>N1 \<inter> N2 = {}\<close> \<open>x \<in> N1\<close> \<open>y \<in> N2\<close> 
    by auto  
  also have "edges T1 \<union> edges T2 \<supseteq> E'"
  proof -
    note ED1 = nodesI[where g=T, unfolded \<open>nodes T = N1\<union>N2\<close>]  
    have "E' \<subseteq> edges T" by (auto simp: E'_def)
    thus "edges T1 \<union> edges T2 \<supseteq> E'"
      unfolding T1_def T2_def
      using ED1 N1C N2C by (auto; blast)
  qed 
  finally have "edges T1 \<union> edges T2 = E'" .  
          
  show ?thesis
    apply (rule that[of T1 T2, unfolded tree_def]; (intro conjI)?; fact?)
    apply simp_all
    apply fact+
    done
qed
  
  
  
  
subsection \<open>Spanning Trees\<close>    
                                    
definition "is_spanning_tree G T 
  \<equiv> tree T \<and> nodes T = nodes G \<and> edges T \<subseteq> edges G"    
  
(* TODO: Move *)
lemma connected_singleton[simp]: "connected (ins_node u graph_empty)"
  unfolding connected_def by auto
  
lemma path_singleton[simp]: "path (ins_node u graph_empty) v p w \<longleftrightarrow> v=w \<and> p=[]"  
  by (cases p) auto

lemma tree_singleton[simp]: "tree (ins_node u graph_empty)"
  by (simp add: cycle_free_no_edges tree_def)

(* TODO: Move *)
lemma tree_add_edge_in_out:
  assumes "tree T"
  assumes "u\<in>nodes T" "v\<notin>nodes T"
  shows "tree (ins_edge (u,v) T)"
proof -
  from assms have [simp]: "u\<noteq>v" by auto
  have "ins_edge (u,v) T = ins_edge (u,v) (graph_join T (ins_node v graph_empty))"
    by (auto simp: graph_eq_iff)
  also have "tree \<dots>"
    apply (rule join_trees)
    using assms
    by auto
  finally show ?thesis .
qed
  
text \<open>Remove edges on cycles until the graph is cycle free\<close>
lemma ex_spanning_tree: 
  "connected g \<Longrightarrow> \<exists>t. is_spanning_tree g t"
  using edges_finite[of g]
proof (induction "edges g" arbitrary: g rule: finite_psubset_induct)
  case psubset
  show ?case proof (cases "cycle_free g")
    case True 
    with \<open>connected g\<close> show ?thesis by (auto simp: is_spanning_tree_def tree_def)
  next
    case False 
    then obtain u v where 
          EDGE: "(u,v)\<in>edges g" 
      and RED: "(u,v)\<in>(edges g - {(u,v),(v,u)})\<^sup>*" 
      using cycle_free_altI by metis
    from \<open>connected g\<close> 
      have "connected (restrict_edges g (- {(u,v),(v,u)}))" (is "connected ?g'")
      unfolding connected_def
      by (auto simp: remove_redundant_edge[OF RED])
    moreover have "edges ?g' \<subset> edges g" using EDGE by auto
    ultimately obtain t where "is_spanning_tree ?g' t" 
      using psubset.hyps(2)[of ?g'] by blast
    hence "is_spanning_tree g t" by (auto simp: is_spanning_tree_def)
    thus ?thesis ..
  qed
qed
  

section \<open>Weighted Undirected Graphs\<close>

definition weight :: "('v set \<Rightarrow> nat) \<Rightarrow> 'v ugraph \<Rightarrow> nat" 
  where "weight w g \<equiv> (\<Sum>e\<in>edges g. w (uedge e)) div 2"

  
lemma weight_alt: "weight w g = (\<Sum>e\<in>uedge`edges g. w e)"  
proof -
  from split_edges_sym[of g] obtain E where 
    "edges g = E \<union> E\<inverse>" and "E\<inter>E\<inverse>={}" by auto
  hence [simp, intro!]: "finite E" by (metis edges_finite finite_Un) 
  hence [simp, intro!]: "finite (E\<inverse>)" by blast

  have [simp]: "(\<Sum>e\<in>E\<inverse>. w (uedge e)) = (\<Sum>e\<in>E. w (uedge e))"
    apply (rule sum.reindex_cong[where l=prod.swap and A="E\<inverse>" and B="E"])
    by (auto simp: uedge_def insert_commute)

  have [simp]: "inj_on uedge E" using \<open>E\<inter>E\<inverse>=_\<close>
    by (auto simp: uedge_def inj_on_def doubleton_eq_iff)
        
  have "weight w g = (\<Sum>e\<in>E. w (uedge e))"
    unfolding weight_def \<open>edges g = _\<close> using \<open>E\<inter>E\<inverse>={}\<close>
    by (auto simp: sum.union_disjoint)
  also have "\<dots> = (\<Sum>e\<in>uedge`E. w e)" 
    using sum.reindex[of uedge E w]
    by auto 
  also have "uedge`E = uedge`(edges g)"  
    unfolding \<open>edges g = _\<close> uedge_def using \<open>E\<inter>E\<inverse>={}\<close>
    by auto
  finally show ?thesis .
qed 

lemma weight_empty[simp]: "weight w graph_empty = 0" unfolding weight_def by auto
  
lemma weight_ins_edge[simp]: "\<lbrakk>u\<noteq>v; (u,v)\<notin>edges g\<rbrakk> 
  \<Longrightarrow> weight w (ins_edge (u,v) g) = w {u,v} + weight w g"
  unfolding weight_def
  apply clarsimp
  apply (subst sum.insert)
  by (auto dest: edges_sym' simp: uedge_def insert_commute)

lemma uedge_img_disj_iff[simp]: 
  "uedge`edges g\<^sub>1 \<inter> uedge`edges g\<^sub>2 = {} \<longleftrightarrow> edges g\<^sub>1 \<inter> edges g\<^sub>2 = {}"
  by (auto simp: uedge_eq_iff dest: edges_sym')+  
  
lemma weight_join[simp]: "edges g\<^sub>1 \<inter> edges g\<^sub>2 = {} 
  \<Longrightarrow> weight w (graph_join g\<^sub>1 g\<^sub>2) = weight w g\<^sub>1 + weight w g\<^sub>2"  
  unfolding weight_alt by (auto simp: sum.union_disjoint image_Un)

lemma weight_cong: "edges g\<^sub>1 = edges g\<^sub>2 \<Longrightarrow> weight w g\<^sub>1 = weight w g\<^sub>2"  
  by (auto simp: weight_def)

lemma weight_mono: "edges g \<subseteq> edges g' \<Longrightarrow> weight w g \<le> weight w g'"
  unfolding weight_alt by (rule sum_mono2) auto
  
lemma weight_ge_edge:
  assumes "(x,y)\<in>edges T"
  shows "weight w T \<ge> w {x,y}"
  using assms unfolding weight_alt
  by (auto simp: uedge_def intro: member_le_sum)
  
  
          
lemma weight_del_edge[simp]: 
  assumes "(x,y)\<in>edges T"  
  shows "weight w (restrict_edges T (- {(x, y), (y, x)})) = weight w T - w {x,y}"
proof -
  define E where "E = uedge ` edges T - {{x,y}}"
  have [simp]: "(uedge ` (edges T - {(x, y), (y, x)})) = E"  
    by (safe; simp add: E_def uedge_def doubleton_eq_iff; blast)
    
  from assms have [simp]: "uedge ` edges T = insert {x,y} E"
    unfolding E_def by force

  have [simp]: "{x,y}\<notin>E" unfolding E_def by blast        

  then show ?thesis
    unfolding weight_alt
    apply simp
    by (metis E_def \<open>uedge ` edges T = insert {x, y} E\<close> insertI1 sum_diff1_nat)
qed    
  
        
subsection \<open>Minimum Spanning Trees\<close>

definition "is_MST w g t \<equiv> is_spanning_tree g t 
  \<and> (\<forall>t'. is_spanning_tree g t' \<longrightarrow> weight w t \<le> weight w t')"  

lemma exists_MST: "connected g \<Longrightarrow> \<exists>t. is_MST w g t"
  using ex_has_least_nat[of "is_spanning_tree g"] ex_spanning_tree 
  unfolding is_MST_def 
  by blast
  
end
