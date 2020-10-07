theory Incredible_Deduction
imports
  Main 
  "HOL-Library.FSet"
  "HOL-Library.Stream"
  Incredible_Signatures
  "HOL-Eisbach.Eisbach"
begin

text \<open>This theory contains the definition for actual proof graphs, and their various possible
properties.\<close>

text \<open>The following locale first defines graphs, without edges.\<close>

locale Vertex_Graph = 
  Port_Graph_Signature nodes inPorts outPorts
    for nodes :: "'node stream"
    and inPorts :: "'node \<Rightarrow> 'inPort fset"
    and outPorts :: "'node \<Rightarrow> 'outPort fset" +
  fixes vertices :: "'v fset"
  fixes nodeOf :: "'v \<Rightarrow> 'node"
begin
  fun valid_out_port where "valid_out_port (v,p) \<longleftrightarrow> v |\<in>| vertices \<and> p |\<in>| outPorts (nodeOf v)"
  fun valid_in_port  where "valid_in_port (v,p) \<longleftrightarrow> v |\<in>| vertices \<and> p |\<in>| inPorts (nodeOf v)" 

  fun terminal_node where
    "terminal_node n \<longleftrightarrow> outPorts n = {||}"
  fun terminal_vertex where
    "terminal_vertex v \<longleftrightarrow> v |\<in>| vertices \<and> terminal_node (nodeOf v)"
end

text \<open>And now we add the edges. This allows us to define paths and scopes.\<close>

type_synonym ('v, 'outPort, 'inPort) edge = "(('v \<times> 'outPort) \<times> ('v \<times> 'inPort))"

locale Pre_Port_Graph =
  Vertex_Graph nodes inPorts outPorts vertices nodeOf
    for nodes :: "'node stream"
    and inPorts :: "'node \<Rightarrow> 'inPort fset"
    and outPorts :: "'node \<Rightarrow> 'outPort fset"
    and vertices :: "'v fset"
    and nodeOf :: "'v \<Rightarrow> 'node" +
  fixes edges :: "('v, 'outPort, 'inPort) edge set"
begin
  fun edge_begin :: "(('v \<times> 'outPort) \<times> ('v \<times> 'inPort)) \<Rightarrow> 'v" where
    "edge_begin ((v1,p1),(v2,p2)) = v1"
  fun edge_end :: "(('v \<times> 'outPort) \<times> ('v \<times> 'inPort)) \<Rightarrow> 'v" where
    "edge_end ((v1,p1),(v2,p2)) = v2"

  lemma edge_begin_tup: "edge_begin x = fst (fst x)" by (metis edge_begin.simps prod.collapse)
  lemma edge_end_tup: "edge_end x = fst (snd x)" by (metis edge_end.simps prod.collapse)

  inductive path :: "'v \<Rightarrow> 'v \<Rightarrow> ('v, 'outPort, 'inPort) edge list \<Rightarrow> bool"   where
    path_empty: "path v v []" |
    path_cons: "e \<in> edges \<Longrightarrow> path (edge_end e) v' pth \<Longrightarrow> path (edge_begin e) v' (e#pth)"

  inductive_simps path_cons_simp': "path v v' (e#pth)"
  inductive_simps path_empty_simp[simp]: "path v v' []"
  lemma path_cons_simp: "path v v' (e # pth) \<longleftrightarrow> fst (fst e) = v \<and> e \<in> edges \<and> path (fst (snd e)) v' pth"
    by(auto simp add: path_cons_simp', metis prod.collapse)

  lemma path_appendI: "path v v' pth1 \<Longrightarrow> path v' v'' pth2 \<Longrightarrow> path v v'' (pth1@pth2)"
    by (induction pth1 arbitrary: v) (auto simp add: path_cons_simp )

  lemma path_split: "path v v' (pth1@[e]@pth2) \<longleftrightarrow> path v (edge_end e) (pth1@[e]) \<and> path (edge_end e) v' pth2"
    by (induction pth1 arbitrary: v) (auto simp add: path_cons_simp edge_end_tup intro: path_empty)

  lemma path_split2: "path v v' (pth1@(e#pth2)) \<longleftrightarrow> path v (edge_begin e) pth1 \<and> path (edge_begin e) v' (e#pth2)"
    by (induction pth1 arbitrary: v) (auto simp add: path_cons_simp edge_begin_tup intro: path_empty)

  lemma path_snoc: "path v v' (pth1@[e]) \<longleftrightarrow> e \<in> edges \<and> path v (edge_begin e) pth1 \<and> edge_end e = v'"
    by (auto simp add: path_split2 path_cons_simp edge_end_tup edge_begin_tup)

  inductive_set scope :: "'v \<times> 'inPort \<Rightarrow> 'v set" for ps where
    "v |\<in>| vertices \<Longrightarrow> (\<And> pth v'.  path v v' pth \<Longrightarrow> terminal_vertex v' \<Longrightarrow> ps \<in> snd ` set pth)
    \<Longrightarrow> v \<in> scope ps"

  lemma scope_find:
    assumes "v \<in> scope ps"
    assumes "terminal_vertex v'"
    assumes "path v v' pth"
    shows "ps \<in> snd ` set pth"
  using assms by (auto simp add: scope.simps)

  lemma snd_set_split:
    assumes "ps \<in> snd ` set pth"
    obtains pth1 pth2 e  where "pth = pth1@[e]@pth2" and "snd e = ps" and "ps \<notin> snd ` set pth1"
    using assms
    proof (atomize_elim, induction pth)
      case Nil thus ?case by simp
    next
      case (Cons e pth)
      show ?case
      proof(cases "snd e = ps")
        case True
        hence "e # pth = [] @ [e] @ pth \<and> snd e = ps \<and> ps \<notin> snd ` set []" by auto
        thus ?thesis by (intro exI)
      next
        case False
        with Cons(2)
        have "ps \<in> snd ` set pth" by auto
        from Cons.IH[OF this this] 
        obtain pth1 e' pth2 where "pth = pth1 @ [e'] @ pth2 \<and> snd e' = ps \<and> ps \<notin> snd ` set pth1" by auto
        with False
        have "e#pth = (e# pth1) @ [e'] @ pth2 \<and> snd e' = ps \<and> ps \<notin> snd ` set (e#pth1)" by auto
        thus ?thesis by blast
      qed
    qed

  lemma scope_split:
    assumes "v \<in> scope ps"
    assumes "path v v' pth"
    assumes "terminal_vertex v'"
    obtains pth1 e pth2
    where "pth = (pth1@[e])@pth2" and "path v (fst ps) (pth1@[e])" and "path (fst ps) v' pth2" and "snd e = ps" and "ps \<notin> snd ` set pth1"
  proof-
    from assms
    have "ps \<in> snd ` set pth" by (auto simp add: scope.simps)
    then obtain pth1 pth2 e  where "pth = pth1@[e]@pth2" and "snd e = ps" and "ps \<notin> snd ` set pth1" by (rule snd_set_split)
    
    from \<open>path _ _ _\<close> and \<open>pth = pth1@[e]@pth2\<close>
    have "path v (edge_end e) (pth1@[e])" and "path (edge_end e) v' pth2" by (metis path_split)+
    show thesis
    proof(rule that)
      show "pth = (pth1@[e])@pth2" using \<open>pth= _\<close> by simp
      show "path v (fst ps) (pth1@[e])" using \<open>path v (edge_end e) (pth1@[e])\<close>  \<open>snd e = ps\<close> by (simp add: edge_end_tup)
      show "path (fst ps) v' pth2" using \<open>path (edge_end e) v' pth2\<close>  \<open>snd e = ps\<close> by (simp add: edge_end_tup)
      show "ps \<notin> snd ` set pth1" by fact
      show "snd e = ps" by fact
    qed
  qed  
end

text \<open>This adds well-formedness conditions to the edges and vertices.\<close>

locale Port_Graph = Pre_Port_Graph +
  assumes valid_nodes: "nodeOf ` fset vertices  \<subseteq> sset nodes"
  assumes valid_edges: "\<forall> (ps1,ps2) \<in> edges. valid_out_port ps1 \<and> valid_in_port ps2"
begin
  lemma snd_set_path_verties: "path v v' pth \<Longrightarrow> fst ` snd ` set pth \<subseteq> fset vertices"
    apply (induction rule: path.induct)
    apply auto
    apply (metis valid_in_port.elims(2) edge_end.simps notin_fset case_prodD valid_edges)
    done

  lemma fst_set_path_verties: "path v v' pth \<Longrightarrow> fst ` fst ` set pth \<subseteq> fset vertices"
    apply (induction rule: path.induct)
    apply auto
    apply (metis valid_out_port.elims(2) edge_begin.simps notin_fset case_prodD valid_edges)
    done
end

text \<open>A pruned graph is one where every node has a path to a terminal node (which will be the conclusions).\<close>

locale Pruned_Port_Graph = Port_Graph +
  assumes pruned: "\<And>v.  v |\<in>| vertices \<Longrightarrow> (\<exists>pth v'. path v v' pth \<and> terminal_vertex v')"
begin
  lemma scopes_not_refl:
    assumes "v |\<in>| vertices"
    shows "v \<notin> scope (v,p)"
  proof(rule notI)
    assume "v \<in> scope (v,p)"

    from pruned[OF assms]
    obtain pth t where "terminal_vertex t" and "path v t pth" and least: "\<forall> pth'. path v t pth' \<longrightarrow> length pth \<le> length pth'"
      by atomize_elim (auto simp del: terminal_vertex.simps elim: ex_has_least_nat)
        
    from scope_split[OF \<open>v \<in> scope (v,p)\<close> \<open>path v t pth\<close> \<open>terminal_vertex t\<close>]
    obtain pth1 e pth2 where "pth = (pth1 @ [e]) @ pth2" "path v t pth2" by (metis fst_conv)

    from this(2) least
    have "length pth \<le> length pth2" by auto
    with \<open>pth = _\<close>
    show False by auto
  qed

  text \<open>This lemma can be found in \cite{incredible}, but it is otherwise inconsequential.\<close>
  lemma scopes_nest:
    fixes ps1 ps2
    shows "scope ps1 \<subseteq> scope ps2 \<or> scope ps2 \<subseteq> scope ps1 \<or> scope ps1 \<inter> scope ps2 = {}"
  proof(cases "ps1 = ps2")
    assume "ps1 \<noteq> ps2"
    {
    fix v
    assume "v \<in> scope ps1 \<inter> scope ps2"
    hence "v |\<in>| vertices" using scope.simps by auto
    then obtain pth t where "path v t pth" and "terminal_vertex t" using pruned by blast
  
    from \<open>path v t pth\<close> and \<open>terminal_vertex t\<close> and \<open>v \<in> scope ps1 \<inter> scope ps2\<close>
    obtain pth1a e1 pth1b  where "pth = (pth1a@[e1])@pth1b" and "path v (fst ps1) (pth1a@[e1])" and "snd e1 = ps1" and "ps1 \<notin> snd ` set pth1a"
      by (auto elim: scope_split)
  
    from \<open>path v t pth\<close> and \<open>terminal_vertex t\<close> and \<open>v \<in> scope ps1 \<inter> scope ps2\<close>
    obtain pth2a e2 pth2b  where "pth = (pth2a@[e2])@pth2b" and "path v (fst ps2) (pth2a@[e2])" and "snd e2 = ps2" and "ps2 \<notin> snd ` set pth2a"
      by (auto elim: scope_split)
   
    from \<open>pth = (pth1a@[e1])@pth1b\<close> \<open>pth = (pth2a@[e2])@pth2b\<close>
    have "set pth1a \<subseteq> set pth2a \<or> set pth2a \<subseteq> set pth1a" by (auto simp add: append_eq_append_conv2)
    hence "scope ps1 \<subseteq> scope ps2 \<or> scope ps2 \<subseteq> scope ps1"
    proof
      assume "set pth1a \<subseteq> set pth2a" with \<open>ps2 \<notin> _\<close>
      have "ps2 \<notin> snd ` set (pth1a@[e1])" using \<open>ps1 \<noteq> ps2\<close> \<open>snd e1 = ps1\<close> by auto
  
      have "scope ps1 \<subseteq> scope ps2"
      proof
        fix v'
        assume "v' \<in> scope ps1"
        hence "v' |\<in>| vertices" using scope.simps by auto
        thus "v' \<in> scope ps2"
        proof(rule scope.intros)
          fix pth' t'
          assume "path v' t' pth'" and "terminal_vertex t'"
          with \<open>v' \<in> scope ps1\<close>
          obtain pth3a e3 pth3b where "pth' = (pth3a@[e3])@pth3b" and "path (fst ps1) t' pth3b"
            by (auto elim: scope_split)
  
          have "path v t' ((pth1a@[e1]) @ pth3b)" using \<open>path v (fst ps1) (pth1a@[e1])\<close> and \<open>path (fst ps1) t' pth3b\<close>
            by (rule path_appendI)
          with \<open>terminal_vertex t'\<close> \<open>v \<in> _\<close>
          have "ps2 \<in> snd ` set ((pth1a@[e1]) @ pth3b)" by (meson IntD2 scope.cases)
          hence "ps2 \<in> snd ` set pth3b" using \<open>ps2 \<notin> snd ` set (pth1a@[e1])\<close> by auto
          thus "ps2 \<in> snd ` set pth'" using \<open>pth'=_\<close> by auto
        qed
      qed
      thus ?thesis by simp
    next
      assume "set pth2a \<subseteq> set pth1a" with \<open>ps1 \<notin> _\<close>
      have "ps1 \<notin> snd ` set (pth2a@[e2])" using \<open>ps1 \<noteq> ps2\<close> \<open>snd e2 = ps2\<close> by auto
  
      have "scope ps2 \<subseteq> scope ps1"
      proof
        fix v'
        assume "v' \<in> scope ps2"
        hence "v' |\<in>| vertices" using scope.simps by auto
        thus "v' \<in> scope ps1"
        proof(rule scope.intros)
          fix pth' t'
          assume "path v' t' pth'" and "terminal_vertex t'"
          with \<open>v' \<in> scope ps2\<close>
          obtain pth3a e3 pth3b where "pth' = (pth3a@[e3])@pth3b" and "path (fst ps2) t' pth3b" 
            by (auto elim: scope_split)
  
          have "path v t' ((pth2a@[e2]) @ pth3b)" using \<open>path v (fst ps2) (pth2a@[e2])\<close> and \<open>path (fst ps2) t' pth3b\<close>
            by (rule path_appendI)
          with \<open>terminal_vertex t'\<close> \<open>v \<in> _\<close>
          have "ps1 \<in> snd ` set ((pth2a@[e2]) @ pth3b)" by (meson IntD1 scope.cases)
          hence "ps1 \<in> snd ` set pth3b" using \<open>ps1 \<notin> snd ` set (pth2a@[e2])\<close> by auto
          thus "ps1 \<in> snd ` set pth'" using \<open>pth'=_\<close> by auto
        qed
      qed
      thus ?thesis by simp
    qed
    }
    thus ?thesis by blast
  qed simp
end

text \<open>A well-scoped graph is one where a port marked to be a local hypothesis is only connected to
the corresponding input port, either directly or via a path. It must not be, however, that there is
a a path from such a hypothesis to a terminal node that does not pass by the dedicated input port;
this is expressed via scopes.
\<close>

locale Scoped_Graph = Port_Graph + Port_Graph_Signature_Scoped
locale Well_Scoped_Graph = Scoped_Graph +
  assumes well_scoped: "((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2)) \<in> edges \<Longrightarrow> hyps (nodeOf v\<^sub>1) p\<^sub>1 = Some p' \<Longrightarrow> (v\<^sub>2,p\<^sub>2) = (v\<^sub>1,p') \<or> v\<^sub>2 \<in> scope (v\<^sub>1,p')"

context Scoped_Graph
begin

definition hyps_free where
  "hyps_free pth = (\<forall> v\<^sub>1 p\<^sub>1 v\<^sub>2 p\<^sub>2. ((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2)) \<in> set pth \<longrightarrow> hyps (nodeOf v\<^sub>1) p\<^sub>1 = None)"

lemma hyps_free_Nil[simp]: "hyps_free []" by (simp add: hyps_free_def)

lemma hyps_free_Cons[simp]: "hyps_free (e#pth) \<longleftrightarrow> hyps_free pth \<and> hyps (nodeOf (fst (fst e))) (snd (fst e)) = None"
  by (auto simp add: hyps_free_def) (metis prod.collapse)

lemma path_vertices_shift:
  assumes "path v v' pth"
  shows "map fst (map fst pth)@[v'] = v#map fst (map snd pth)"
using assms by induction auto

inductive terminal_path where
    terminal_path_empty: "terminal_vertex v \<Longrightarrow> terminal_path v v []" |
    terminal_path_cons: "((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2)) \<in> edges \<Longrightarrow> terminal_path v\<^sub>2 v' pth \<Longrightarrow> hyps (nodeOf v\<^sub>1) p\<^sub>1 = None \<Longrightarrow> terminal_path v\<^sub>1 v' (((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2))#pth)"

lemma terminal_path_is_path:
  assumes "terminal_path v v' pth"
  shows "path v v' pth"
using assms by induction (auto simp add: path_cons_simp)

lemma terminal_path_is_hyps_free:
  assumes "terminal_path v v' pth"
  shows "hyps_free pth"
using assms by induction (auto simp add: hyps_free_def)

lemma terminal_path_end_is_terminal:
  assumes "terminal_path v v' pth"
  shows "terminal_vertex v'"
using assms by induction

lemma terminal_pathI:
  assumes "path v v' pth"
  assumes "hyps_free pth"
  assumes "terminal_vertex v'"
  shows "terminal_path v v' pth"
using assms
by induction (auto intro: terminal_path.intros)
end

text \<open>An acyclic graph is one where there are no non-trivial cyclic paths (disregarding
edges that are local hypotheses -- these are naturally and benignly cyclic).\<close>

locale Acyclic_Graph = Scoped_Graph +
  assumes hyps_free_acyclic: "path v v pth \<Longrightarrow> hyps_free pth \<Longrightarrow> pth = []"
begin
lemma hyps_free_vertices_distinct:
  assumes "terminal_path v v' pth"
  shows "distinct (map fst (map fst pth)@[v'])"
using assms
proof(induction v v' pth)
  case terminal_path_empty
  show ?case by simp
next
  case (terminal_path_cons v\<^sub>1 p\<^sub>1 v\<^sub>2 p\<^sub>2 v' pth)
  note terminal_path_cons.IH
  moreover
  have "v\<^sub>1 \<notin> fst ` fst ` set pth"
  proof
    assume "v\<^sub>1 \<in> fst ` fst ` set pth"
    then obtain pth1 e' pth2 where "pth = pth1@[e']@pth2" and "v\<^sub>1 = fst (fst e')"
      apply (atomize_elim)
      apply (induction pth)
      apply (solves simp)
      apply (auto)
      apply (solves \<open>rule exI[where x = "[]"]; simp\<close>)
      apply (metis Cons_eq_appendI image_eqI prod.sel(1))
      done
    with terminal_path_is_path[OF \<open>terminal_path v\<^sub>2 v' pth\<close>]
    have "path v\<^sub>2 v\<^sub>1 pth1" by (simp add:  path_split2 edge_begin_tup)
    with \<open>((v\<^sub>1, p\<^sub>1), (v\<^sub>2, p\<^sub>2)) \<in> _\<close>
    have "path v\<^sub>1 v\<^sub>1 (((v\<^sub>1, p\<^sub>1), (v\<^sub>2, p\<^sub>2)) # pth1)" by (simp add: path_cons_simp)
    moreover
    from terminal_path_is_hyps_free[OF \<open>terminal_path v\<^sub>2 v' pth\<close>]
         \<open>hyps (nodeOf v\<^sub>1) p\<^sub>1 = None\<close>
         \<open>pth = pth1@[e']@pth2\<close>
    have "hyps_free(((v\<^sub>1, p\<^sub>1), (v\<^sub>2, p\<^sub>2)) # pth1)"
      by (auto simp add: hyps_free_def)
    ultimately
    show False  using hyps_free_acyclic by blast
  qed
  moreover
  have "v\<^sub>1 \<noteq> v'"
    using hyps_free_acyclic path_cons terminal_path_cons.hyps(1) terminal_path_cons.hyps(2) terminal_path_cons.hyps(3) terminal_path_is_hyps_free terminal_path_is_path by fastforce
  ultimately
  show ?case by (auto simp add: comp_def)
qed

lemma hyps_free_vertices_distinct':
  assumes "terminal_path v v' pth"
  shows "distinct (v # map fst (map snd pth))"
  using hyps_free_vertices_distinct[OF assms]
  unfolding path_vertices_shift[OF terminal_path_is_path[OF assms]]
  .

lemma hyps_free_limited:
  assumes "terminal_path v v' pth"
  shows "length pth \<le> fcard vertices"
proof-
  have "length pth = length (map fst (map fst pth))" by simp
  also
  from hyps_free_vertices_distinct[OF assms]
  have "distinct (map fst (map fst pth))" by simp
  hence "length (map fst (map fst pth)) = card (set (map fst (map fst pth)))"
    by (rule distinct_card[symmetric])
  also have "\<dots> \<le> card (fset vertices)"
  proof (rule card_mono[OF finite_fset])    
    from assms(1) 
    show "set (map fst (map fst pth)) \<subseteq> fset vertices"
      by (induction v v' pth) (auto, metis valid_edges notin_fset case_prodD valid_out_port.simps)
  qed
  also have "\<dots> = fcard vertices" by (simp add: fcard.rep_eq)
  finally show ?thesis.
qed

lemma hyps_free_path_not_in_scope:
  assumes "terminal_path v t pth"
  assumes "(v',p') \<in> snd ` set pth"
  shows   "v' \<notin> scope (v, p)"
proof
  assume "v' \<in> scope (v,p)"

  from \<open>(v',p') \<in> snd ` set pth\<close>
  obtain pth1 pth2 e  where "pth = pth1@[e]@pth2" and "snd e = (v',p')" by (rule snd_set_split)
  from terminal_path_is_path[OF assms(1), unfolded \<open>pth = _ \<close>] \<open>snd e = _\<close>
  have "path v v' (pth1@[e])" and "path v' t pth2" unfolding path_split by (auto simp add: edge_end_tup)
  
  from \<open>v' \<in> scope (v,p)\<close> terminal_path_end_is_terminal[OF assms(1)] \<open>path v' t pth2\<close>
  have "(v,p) \<in> snd ` set pth2" by (rule scope_find)
  then obtain pth2a e' pth2b  where "pth2 = pth2a@[e']@pth2b" and "snd e' = (v,p)"  by (rule snd_set_split)
  from \<open>path v' t pth2\<close>[unfolded \<open>pth2 = _ \<close>] \<open>snd e' = _\<close>
  have "path v' v (pth2a@[e'])" and "path v t pth2b" unfolding path_split by (auto simp add: edge_end_tup)
  
  from \<open>path v v' (pth1@[e])\<close> \<open>path v' v (pth2a@[e'])\<close>
  have "path v v ((pth1@[e])@(pth2a@[e']))" by (rule path_appendI)
  moreover
  from terminal_path_is_hyps_free[OF assms(1)] \<open>pth = _\<close> \<open>pth2 = _\<close>
  have "hyps_free ((pth1@[e])@(pth2a@[e']))" by (auto simp add: hyps_free_def)
  ultimately
  have "((pth1@[e])@(pth2a@[e'])) = []" by (rule hyps_free_acyclic)
  thus False by simp
qed

end

text \<open>A saturated graph is one where every input port is incident to an edge.\<close>

locale Saturated_Graph = Port_Graph +
  assumes saturated: "valid_in_port (v,p) \<Longrightarrow> \<exists> e \<in> edges . snd e = (v,p)"

text \<open>These four conditions make up a well-shaped graph.\<close>

locale Well_Shaped_Graph =  Well_Scoped_Graph + Acyclic_Graph + Saturated_Graph + Pruned_Port_Graph

text \<open>Next we demand an instantiation. This consists of a unique natural number per vertex,
in order to rename the local constants apart, and furthermore a substitution per block
which instantiates the schematic formulas given in @{term Labeled_Signature}.\<close>

locale Instantiation =
  Vertex_Graph nodes _ _ vertices _ +
  Labeled_Signature nodes  _ _ _ labelsIn labelsOut +
  Abstract_Formulas freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP
  for nodes :: "'node stream" and edges :: "('vertex, 'outPort, 'inPort) edge set" and vertices :: "'vertex fset" and labelsIn :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'form" and labelsOut :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'form" 
  and  freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var" 
    and renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> 'form \<Rightarrow> 'form" 
    and lconsts :: "'form \<Rightarrow> 'var set" 
    and closed :: "'form \<Rightarrow> bool"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
    and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
    and anyP :: "'form" +
  fixes vidx :: "'vertex \<Rightarrow> nat"
    and inst :: "'vertex \<Rightarrow> 'subst"
  assumes vidx_inj: "inj_on vidx (fset vertices)"
begin
  definition labelAtIn :: "'vertex \<Rightarrow> 'inPort \<Rightarrow> 'form"  where
    "labelAtIn v p = subst (inst v) (freshen (vidx v) (labelsIn (nodeOf v) p))"
  definition labelAtOut :: "'vertex \<Rightarrow> 'outPort \<Rightarrow> 'form"  where
    "labelAtOut v p = subst (inst v) (freshen (vidx v) (labelsOut (nodeOf v) p))"
end

text \<open>A solution is an instantiation where on every edge, both incident ports are labeld with
the same formula.\<close>

locale Solution =
  Instantiation _ _ _ _ _ edges for edges :: "(('vertex \<times> 'outPort) \<times> 'vertex \<times> 'inPort) set" +
  assumes solved: "((v\<^sub>1,p\<^sub>1),(v\<^sub>2,p\<^sub>2)) \<in> edges \<Longrightarrow> labelAtOut v\<^sub>1 p\<^sub>1 = labelAtIn v\<^sub>2 p\<^sub>2"

locale Proof_Graph =  Well_Shaped_Graph + Solution

text \<open>If we have locally scoped constants, we demand that only blocks in the scope of the 
corresponding input port may mention such a locally scoped variable in its substitution.\<close>

locale Well_Scoped_Instantiation =
   Pre_Port_Graph  nodes inPorts outPorts vertices nodeOf edges +
   Instantiation  inPorts outPorts nodeOf hyps nodes edges  vertices labelsIn labelsOut freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP vidx inst +
   Port_Graph_Signature_Scoped_Vars nodes inPorts outPorts freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP local_vars
   for freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var" 
    and renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> 'form \<Rightarrow> 'form" 
    and lconsts :: "'form \<Rightarrow> 'var set" 
    and closed :: "'form \<Rightarrow> bool"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
    and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
    and anyP :: "'form"
    and inPorts :: "'node \<Rightarrow> 'inPort fset" 
    and outPorts :: "'node \<Rightarrow> 'outPort fset" 
    and nodeOf :: "'vertex \<Rightarrow> 'node" 
    and hyps :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'inPort option" 
    and nodes :: "'node stream" 
    and vertices :: "'vertex fset" 
    and labelsIn :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'form" 
    and labelsOut :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'form" 
    and vidx :: "'vertex \<Rightarrow> nat" 
    and inst :: "'vertex \<Rightarrow> 'subst" 
    and edges :: "('vertex, 'outPort, 'inPort) edge set" 
    and local_vars :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'var set" +
  assumes well_scoped_inst:
    "valid_in_port (v,p) \<Longrightarrow>
     var \<in> local_vars (nodeOf v) p \<Longrightarrow>
     v' |\<in>| vertices \<Longrightarrow>
     freshenLC (vidx v) var \<in> subst_lconsts (inst v') \<Longrightarrow>
     v' \<in> scope (v,p)"
begin
  lemma out_of_scope: "valid_in_port (v,p) \<Longrightarrow> v' |\<in>| vertices \<Longrightarrow> v' \<notin> scope (v,p) \<Longrightarrow> freshenLC (vidx v) ` local_vars (nodeOf v) p \<inter> subst_lconsts (inst v') = {}"
    using well_scoped_inst by auto
end

text \<open>The following locale assembles all these conditions.\<close>
  
locale Scoped_Proof_Graph =
  Instantiation  inPorts outPorts nodeOf hyps nodes edges  vertices labelsIn labelsOut freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP vidx inst +
  Well_Shaped_Graph  nodes inPorts outPorts vertices nodeOf edges hyps  +
  Solution inPorts outPorts nodeOf hyps nodes vertices  labelsIn labelsOut freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP vidx inst edges +
  Well_Scoped_Instantiation  freshenLC renameLCs lconsts closed subst subst_lconsts subst_renameLCs anyP inPorts outPorts nodeOf hyps  nodes vertices labelsIn labelsOut vidx inst edges local_vars
   for freshenLC :: "nat \<Rightarrow> 'var \<Rightarrow> 'var" 
    and renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> 'form \<Rightarrow> 'form" 
    and lconsts :: "'form \<Rightarrow> 'var set" 
    and closed :: "'form \<Rightarrow> bool"
    and subst :: "'subst \<Rightarrow> 'form \<Rightarrow> 'form" 
    and subst_lconsts :: "'subst \<Rightarrow> 'var set" 
    and subst_renameLCs :: "('var \<Rightarrow> 'var) \<Rightarrow> ('subst \<Rightarrow> 'subst)"
    and anyP :: "'form"
    and inPorts :: "'node \<Rightarrow> 'inPort fset" 
    and outPorts :: "'node \<Rightarrow> 'outPort fset" 
    and nodeOf :: "'vertex \<Rightarrow> 'node" 
    and hyps :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'inPort option" 
    and nodes :: "'node stream" 
    and vertices :: "'vertex fset" 
    and labelsIn :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'form" 
    and labelsOut :: "'node \<Rightarrow> 'outPort \<Rightarrow> 'form" 
    and vidx :: "'vertex \<Rightarrow> nat" 
    and inst :: "'vertex \<Rightarrow> 'subst" 
    and edges :: "('vertex, 'outPort, 'inPort) edge  set" 
    and local_vars :: "'node \<Rightarrow> 'inPort \<Rightarrow> 'var set"

end
