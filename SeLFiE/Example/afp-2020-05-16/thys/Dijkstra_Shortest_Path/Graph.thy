section \<open>Graphs\<close>
theory Graph
imports Main
begin
text \<open>
  This theory defines a notion of graphs. A graph is a record that
  contains a set of nodes \<open>V\<close> and a set of labeled edges 
  \<open>E \<subseteq> V\<times>W\<times>V\<close>, where \<open>W\<close> are the edge labels.
\<close>

subsection \<open>Definitions\<close>
  text \<open>A graph is represented by a record.\<close>
  record ('v,'w) graph =
    nodes :: "'v set"
    edges :: "('v \<times> 'w \<times> 'v) set"

  text \<open>In a valid graph, edges only go from nodes to nodes.\<close>
  locale valid_graph = 
    fixes G :: "('v,'w) graph"
    assumes E_valid: "fst`edges G \<subseteq> nodes G"
                     "snd`snd`edges G \<subseteq> nodes G"
  begin
    abbreviation "V \<equiv> nodes G"
    abbreviation "E \<equiv> edges G"

    lemma E_validD: assumes "(v,e,v')\<in>E"
      shows "v\<in>V" "v'\<in>V"
      apply -
      apply (rule subsetD[OF E_valid(1)])
      using assms apply force
      apply (rule subsetD[OF E_valid(2)])
      using assms apply force
      done

  end

  subsection \<open>Basic operations on Graphs\<close>

  text \<open>The empty graph.\<close>
  definition empty where 
    "empty \<equiv> \<lparr> nodes = {}, edges = {} \<rparr>"
  text \<open>Adds a node to a graph.\<close>
  definition add_node where 
    "add_node v g \<equiv> \<lparr> nodes = insert v (nodes g), edges=edges g\<rparr>"
  text \<open>Deletes a node from a graph. Also deletes all adjacent edges.\<close>
  definition delete_node where "delete_node v g \<equiv> \<lparr> 
    nodes = nodes g - {v},   
    edges = edges g \<inter> (-{v})\<times>UNIV\<times>(-{v})
    \<rparr>"
  text \<open>Adds an edge to a graph.\<close>
  definition add_edge where "add_edge v e v' g \<equiv> \<lparr>
    nodes = {v,v'} \<union> nodes g,
    edges = insert (v,e,v') (edges g)
    \<rparr>"
  text \<open>Deletes an edge from a graph.\<close>
  definition delete_edge where "delete_edge v e v' g \<equiv> \<lparr>
    nodes = nodes g, edges = edges g - {(v,e,v')} \<rparr>"
  text \<open>Successors of a node.\<close>
  definition succ :: "('v,'w) graph \<Rightarrow> 'v \<Rightarrow> ('w\<times>'v) set"
    where "succ G v \<equiv> {(w,v'). (v,w,v')\<in>edges G}"

  text \<open>Now follow some simplification lemmas.\<close>
  lemma empty_valid[simp]: "valid_graph empty"
    unfolding empty_def by unfold_locales auto
  lemma add_node_valid[simp]: assumes "valid_graph g" 
    shows "valid_graph (add_node v g)"
  proof -
    interpret valid_graph g by fact
    show ?thesis
      unfolding add_node_def 
      by unfold_locales (auto dest: E_validD)
  qed
  lemma delete_node_valid[simp]: assumes "valid_graph g" 
    shows "valid_graph (delete_node v g)"
  proof -
    interpret valid_graph g by fact
    show ?thesis
      unfolding delete_node_def 
      by unfold_locales (auto dest: E_validD)
  qed
  lemma add_edge_valid[simp]: assumes "valid_graph g" 
    shows "valid_graph (add_edge v e v' g)"
  proof -
    interpret valid_graph g by fact
    show ?thesis
      unfolding add_edge_def
      by unfold_locales (auto dest: E_validD)
  qed
  lemma delete_edge_valid[simp]: assumes "valid_graph g" 
    shows "valid_graph (delete_edge v e v' g)"
  proof -
    interpret valid_graph g by fact
    show ?thesis
      unfolding delete_edge_def
      by unfold_locales (auto dest: E_validD)
  qed

  lemma succ_finite[simp, intro]: "finite (edges G) \<Longrightarrow> finite (succ G v)"
    unfolding succ_def
    by (rule finite_subset[where B="snd`edges G"]) force+

  lemma nodes_empty[simp]: "nodes empty = {}" unfolding empty_def by simp
  lemma edges_empty[simp]: "edges empty = {}" unfolding empty_def by simp
  lemma succ_empty[simp]: "succ empty v = {}" unfolding empty_def succ_def by auto

  lemma nodes_add_node[simp]: "nodes (add_node v g) = insert v (nodes g)"
    by (simp add: add_node_def)
  lemma nodes_add_edge[simp]: 
    "nodes (add_edge v e v' g) = insert v (insert v' (nodes g))"
    by (simp add: add_edge_def)
  lemma edges_add_edge[simp]: 
    "edges (add_edge v e v' g) = insert (v,e,v') (edges g)"
    by (simp add: add_edge_def)
  lemma edges_add_node[simp]: 
    "edges (add_node v g) = edges g"
    by (simp add: add_node_def)

  lemma (in valid_graph) succ_subset: "succ G v \<subseteq> UNIV\<times>V"
    unfolding succ_def using E_valid
    by (force)

subsection \<open>Paths\<close>
  text \<open>A path is represented by a list of adjacent edges.\<close>
  type_synonym ('v,'w) path = "('v\<times>'w\<times>'v) list"

  context valid_graph
  begin
    text \<open>The following predicate describes a valid path:\<close>
    fun is_path :: "'v \<Rightarrow> ('v,'w) path \<Rightarrow> 'v \<Rightarrow> bool" where
      "is_path v [] v' \<longleftrightarrow> v=v' \<and> v'\<in>V" |
      "is_path v ((v1,w,v2)#p) v' \<longleftrightarrow> v=v1 \<and> (v1,w,v2)\<in>E \<and> is_path v2 p v'"
  
    lemma is_path_simps[simp, intro!]:
      "is_path v [] v \<longleftrightarrow> v\<in>V"
      "is_path v [(v,w,v')] v' \<longleftrightarrow> (v,w,v')\<in>E"
      by (auto dest: E_validD)
    
    lemma is_path_memb[simp]:
      "is_path v p v' \<Longrightarrow> v\<in>V \<and> v'\<in>V"
      apply (induct p arbitrary: v) 
      apply (auto dest: E_validD)
      done

    lemma is_path_split:
      "is_path v (p1@p2) v' \<longleftrightarrow> (\<exists>u. is_path v p1 u \<and> is_path u p2 v')"
      by (induct p1 arbitrary: v) auto

    lemma is_path_split'[simp]: 
      "is_path v (p1@(u,w,u')#p2) v' 
        \<longleftrightarrow> is_path v p1 u \<and> (u,w,u')\<in>E \<and> is_path u' p2 v'"
      by (auto simp add: is_path_split)
  end

  text \<open>Set of intermediate vertices of a path. These are all vertices but
    the last one. Note that, if the last vertex also occurs earlier on the path,
    it is contained in \<open>int_vertices\<close>.\<close>
  definition int_vertices :: "('v,'w) path \<Rightarrow> 'v set" where
    "int_vertices p \<equiv> set (map fst p)"

  lemma int_vertices_simps[simp]:
    "int_vertices [] = {}"
    "int_vertices (vv#p) = insert (fst vv) (int_vertices p)"
    "int_vertices (p1@p2) = int_vertices p1 \<union> int_vertices p2"
    by (auto simp add: int_vertices_def)
  
  lemma (in valid_graph) int_vertices_subset: 
    "is_path v p v' \<Longrightarrow> int_vertices p \<subseteq> V"
    apply (induct p arbitrary: v)
    apply (simp) 
    apply (force dest: E_validD)
    done

  lemma int_vertices_empty[simp]: "int_vertices p = {} \<longleftrightarrow> p=[]"
    by (cases p) auto

subsubsection \<open>Splitting Paths\<close>
  text \<open>Split a path at the point where it first leaves the set \<open>W\<close>:\<close>
  lemma (in valid_graph) path_split_set:
    assumes "is_path v p v'" and "v\<in>W" and "v'\<notin>W"
    obtains p1 p2 u w u' where
    "p=p1@(u,w,u')#p2" and
    "int_vertices p1 \<subseteq> W" and "u\<in>W" and "u'\<notin>W"
    using assms
  proof (induct p arbitrary: v thesis)
    case Nil thus ?case by auto
  next
    case (Cons vv p)
    note [simp, intro!] = \<open>v\<in>W\<close> \<open>v'\<notin>W\<close>
    from Cons.prems obtain w u' where 
      [simp]: "vv=(v,w,u')" and
        REST: "is_path u' p v'"
      by (cases vv) auto
    
    txt \<open>Distinguish wether the second node \<open>u'\<close> of the path is 
      in \<open>W\<close>. If yes, the proposition follows by the 
      induction hypothesis, otherwise it is straightforward, as
      the split takes place at the first edge of the path.\<close>
    {
      assume A [simp, intro!]: "u'\<in>W"
      from Cons.hyps[OF _ REST] obtain p1 uu ww uu' p2 where
        "p=p1@(uu,ww,uu')#p2" "int_vertices p1 \<subseteq> W" "uu \<in> W" "uu' \<notin> W"
        by blast
      with Cons.prems(1)[of "vv#p1" uu ww uu' p2] have thesis by auto
    } moreover {
      assume "u'\<notin>W"
      with Cons.prems(1)[of "[]" v w u' p] have thesis by auto
    } ultimately show thesis by blast
  qed
  
  text \<open>Split a path at the point where it first enters the set \<open>W\<close>:\<close>
  lemma (in valid_graph) path_split_set':
    assumes "is_path v p v'" and "v'\<in>W"
    obtains p1 p2 u where
    "p=p1@p2" and
    "is_path v p1 u" and
    "is_path u p2 v'" and
    "int_vertices p1 \<subseteq> -W" and "u\<in>W"
    using assms
  proof (cases "v\<in>W")
    case True with that[of "[]" p] assms show ?thesis
      by auto
  next
    case False with assms that show ?thesis
    proof (induct p arbitrary: v thesis)
      case Nil thus ?case by auto
    next
      case (Cons vv p)
      note [simp, intro!] = \<open>v'\<in>W\<close> \<open>v\<notin>W\<close>
      from Cons.prems obtain w u' where 
        [simp]: "vv=(v,w,u')" and [simp]: "(v,w,u')\<in>E" and
          REST: "is_path u' p v'"
        by (cases vv) auto
    
      txt \<open>Distinguish wether the second node \<open>u'\<close> of the path is 
        in \<open>W\<close>. If yes, the proposition is straightforward, otherwise,
        it follows by the induction hypothesis.
\<close>
      {
        assume A [simp, intro!]: "u'\<in>W"
        from Cons.prems(3)[of "[vv]" p u'] REST have ?case by auto
      } moreover {
        assume [simp, intro!]: "u'\<notin>W"
        from Cons.hyps[OF REST] obtain p1 p2 u'' where
          [simp]: "p=p1@p2" and 
            "is_path u' p1 u''" and 
            "is_path u'' p2 v'" and
            "int_vertices p1 \<subseteq> -W" and
            "u''\<in>W" by blast
        with Cons.prems(3)[of "vv#p1"] have ?case by auto
      } ultimately show ?case by blast
    qed
  qed

  text \<open>Split a path at the point where a given vertex is first visited:\<close>
  lemma (in valid_graph) path_split_vertex:
    assumes "is_path v p v'" and "u\<in>int_vertices p"
    obtains p1 p2 where
    "p=p1@p2" and
    "is_path v p1 u" and
    "u \<notin> int_vertices p1"
    using assms
  proof (induct p arbitrary: v thesis)
    case Nil thus ?case by auto
  next
    case (Cons vv p)
    from Cons.prems obtain w u' where 
      [simp]: "vv=(v,w,u')" "v\<in>V" "(v,w,u')\<in>E" and
        REST: "is_path u' p v'"
      by (cases vv) auto
    
    {
      assume "u=v"
      with Cons.prems(1)[of "[]" "vv#p"] have thesis by auto
    } moreover {
      assume [simp]: "u\<noteq>v"
      with Cons.hyps(1)[OF _ REST] Cons.prems(3) obtain p1 p2 where
        "p=p1@p2" "is_path u' p1 u" "u\<notin>int_vertices p1"
        by auto
      with Cons.prems(1)[of "vv#p1" p2] have thesis
        by auto
    } ultimately show ?case by blast
  qed

subsection \<open>Weighted Graphs\<close>
  locale valid_mgraph = valid_graph G for G::"('v,'w::monoid_add) graph"

  definition path_weight :: "('v,'w::monoid_add) path \<Rightarrow> 'w"
    where "path_weight p \<equiv> sum_list (map (fst \<circ> snd) p)"

  (* 
    lemma path_weight_alt: "path_weight p \<equiv> sum_list (map (fst \<circ> snd) p)"
    unfolding path_weight_def foldl_conv_fold
    by (simp add: sum_list_foldl)
  *)

  lemma path_weight_split[simp]:
    "(path_weight (p1@p2)::'w::monoid_add) = path_weight p1 + path_weight p2"
    unfolding path_weight_def
    by (auto)

  lemma path_weight_empty[simp]: "path_weight [] = 0"
    unfolding path_weight_def
    by auto

  lemma path_weight_cons[simp]:
    "(path_weight (e#p)::'w::monoid_add) = fst (snd e) + path_weight p"
    unfolding path_weight_def
    by (auto)

end
