section "Undirected Graphs as symmetric directed graphs"

theory Graph_Definition
  imports
    Dijkstra_Shortest_Path.Graph
    Dijkstra_Shortest_Path.Weight
begin

subsection \<open>Definition\<close>

fun is_path_undir :: "('v, 'w) graph \<Rightarrow> 'v \<Rightarrow> ('v,'w) path \<Rightarrow> 'v \<Rightarrow> bool" where
    "is_path_undir G v [] v' \<longleftrightarrow> v=v' \<and> v'\<in>nodes G" |
    "is_path_undir G v ((v1,w,v2)#p) v'
       \<longleftrightarrow> v=v1 \<and> ((v1,w,v2)\<in>edges G \<or> (v2,w,v1)\<in>edges G) \<and> is_path_undir G v2 p v'"

abbreviation "nodes_connected G a b \<equiv> \<exists>p. is_path_undir G a p b"

definition degree :: "('v, 'w) graph \<Rightarrow> 'v \<Rightarrow> nat" where
  "degree G v = card {e\<in>edges G. fst e = v \<or> snd (snd e) = v}"

locale forest = valid_graph G
  for G :: "('v,'w) graph" +
  assumes cycle_free:
    "\<forall>(a,w,b)\<in>E. \<not> nodes_connected (delete_edge a w b G) a b"

locale connected_graph = valid_graph G
  for G :: "('v,'w) graph" +
  assumes connected:
    "\<forall>v\<in>V. \<forall>v'\<in>V. nodes_connected G v v'"

locale tree = forest + connected_graph

locale finite_graph = valid_graph G
  for G :: "('v,'w) graph" +
  assumes finite_E: "finite E" and
    finite_V: "finite V"

locale finite_weighted_graph = finite_graph G
  for G :: "('v,'w::weight) graph"

definition subgraph :: "('v, 'w) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "subgraph G H \<equiv> nodes G = nodes H \<and> edges G \<subseteq> edges H"

definition edge_weight :: "('v, 'w) graph \<Rightarrow> 'w::weight" where
  "edge_weight G \<equiv> sum (fst o snd) (edges G)"

definition edges_less_eq :: "('a \<times> 'w::weight \<times> 'a) \<Rightarrow> ('a \<times> 'w \<times> 'a) \<Rightarrow> bool"
  where "edges_less_eq a b \<equiv> fst(snd a) \<le> fst(snd b)"

definition maximally_connected :: "('v, 'w) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "maximally_connected H G \<equiv> \<forall>v\<in>nodes G. \<forall>v'\<in>nodes G.
    (nodes_connected G v v') \<longrightarrow> (nodes_connected H v v')"

definition spanning_forest :: "('v, 'w) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "spanning_forest F G \<equiv> forest F \<and> maximally_connected F G \<and> subgraph F G"

definition optimal_forest :: "('v, 'w::weight) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "optimal_forest F G \<equiv> (\<forall>F'::('v, 'w) graph.
      spanning_forest F' G \<longrightarrow> edge_weight F \<le> edge_weight F')"

definition minimum_spanning_forest :: "('v, 'w::weight) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "minimum_spanning_forest F G \<equiv> spanning_forest F G \<and> optimal_forest F G"

definition spanning_tree :: "('v, 'w) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "spanning_tree F G \<equiv> tree F \<and> subgraph F G"

definition optimal_tree :: "('v, 'w::weight) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "optimal_tree F G \<equiv> (\<forall>F'::('v, 'w) graph.
      spanning_tree F' G \<longrightarrow> edge_weight F \<le> edge_weight F')"

definition minimum_spanning_tree :: "('v, 'w::weight) graph \<Rightarrow> ('v, 'w) graph \<Rightarrow> bool" where
  "minimum_spanning_tree F G \<equiv> spanning_tree F G \<and> optimal_tree F G"

subsection \<open>Helping lemmas\<close>

lemma nodes_delete_edge[simp]:
  "nodes (delete_edge v e v' G) = nodes G"
  by (simp add: delete_edge_def)

lemma edges_delete_edge[simp]:
  "edges (delete_edge v e v' G) = edges G - {(v,e,v')}"
  by (simp add: delete_edge_def)

lemma subgraph_node:
  assumes "subgraph H G"
  shows "v \<in> nodes G \<longleftrightarrow> v \<in> nodes H"
  using assms
  unfolding subgraph_def
  by simp

lemma delete_add_edge:
  assumes "a \<in> nodes H"
  assumes "c \<in> nodes H"
  assumes "(a, w, c) \<notin> edges H"
  shows "delete_edge a w c (add_edge a w c H) = H"
  using assms unfolding delete_edge_def add_edge_def
  by (simp add: insert_absorb)

lemma swap_delete_add_edge:
  assumes "(a, b, c) \<noteq> (x, y, z)"
  shows "delete_edge a b c (add_edge x y z H) = add_edge x y z (delete_edge a b c H)"
  using assms unfolding delete_edge_def add_edge_def
  by auto

lemma swap_delete_edges: "delete_edge a b c (delete_edge x y z H)
           = delete_edge x y z (delete_edge a b c H)"
  unfolding delete_edge_def
  by auto

context valid_graph
begin
  lemma valid_subgraph:
    assumes "subgraph H G"
    shows "valid_graph H"
    using assms E_valid unfolding subgraph_def valid_graph_def
    by blast

  lemma is_path_undir_simps[simp, intro!]:
    "is_path_undir G v [] v \<longleftrightarrow> v\<in>V"
    "is_path_undir G v [(v,w,v')] v' \<longleftrightarrow> (v,w,v')\<in>E \<or> (v',w,v)\<in>E"
    by (auto dest: E_validD)

  lemma is_path_undir_memb[simp]:
    "is_path_undir G v p v' \<Longrightarrow> v\<in>V \<and> v'\<in>V"
    apply (induct p arbitrary: v)
     apply (auto dest: E_validD)
    done

  lemma is_path_undir_memb_edges:
    assumes "is_path_undir G v p v'"
    shows "\<forall>(a,w,b) \<in> set p. (a,w,b) \<in> E \<or> (b,w,a) \<in> E"
    using assms
    by (induct p arbitrary: v) fastforce+

  lemma is_path_undir_split:
    "is_path_undir G v (p1@p2) v' \<longleftrightarrow> (\<exists>u. is_path_undir G v p1 u \<and> is_path_undir G u p2 v')"
    by (induct p1 arbitrary: v) auto

  lemma is_path_undir_split'[simp]:
    "is_path_undir G v (p1@(u,w,u')#p2) v'
      \<longleftrightarrow> is_path_undir G v p1 u \<and> ((u,w,u')\<in>E \<or> (u',w,u)\<in>E) \<and> is_path_undir G u' p2 v'"
    by (auto simp add: is_path_undir_split)

  lemma is_path_undir_sym:
    assumes "is_path_undir G v p v'"
    shows "is_path_undir G v' (rev (map (\<lambda>(u, w, u'). (u', w, u)) p)) v"
    using assms
    by (induct p arbitrary: v) (auto simp: E_validD)

  lemma is_path_undir_subgraph:
    assumes "is_path_undir H x p y"
    assumes "subgraph H G"
    shows "is_path_undir G x p y"
    using assms is_path_undir.simps
    unfolding subgraph_def
    by (induction p arbitrary: x y) auto

  lemma no_path_in_empty_graph:
    assumes "E = {}"
    assumes "p \<noteq> []"
    shows "\<not>is_path_undir G v p v"
    using assms by (cases p) auto

  lemma is_path_undir_split_distinct:
    assumes "is_path_undir G v p v'"
    assumes "(a, w, b) \<in> set p \<or> (b, w, a) \<in> set p"
    shows "(\<exists>p' p'' u u'.
            is_path_undir G v p' u \<and> is_path_undir G u' p'' v' \<and>
            length p' < length p \<and> length p'' < length p \<and>
            (u \<in> {a, b} \<and> u' \<in> {a, b}) \<and>
            (a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
            (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p'')"
    using assms
  proof (induction n == "length p" arbitrary: p v v' rule: nat_less_induct)
    case 1
    then obtain u u' where "(u, w, u') \<in> set p" and u: "u \<in> {a, b} \<and> u' \<in> {a, b}"
      by blast
    with split_list obtain p' p''
      where p: "p = p' @ (u, w, u') # p''"
      by fast
    then have len_p': "length p' < length p" and len_p'': "length p'' < length p"
      by auto
    from 1 p have p': "is_path_undir G v p' u" and p'': "is_path_undir G u' p'' v'"
      by auto
    from 1 len_p' p' have "(a, w, b) \<in> set p' \<or> (b, w, a) \<in> set p' \<longrightarrow> (\<exists>p'2 u2.
            is_path_undir G v p'2 u2 \<and>
            length p'2 < length p' \<and>
            u2 \<in> {a, b} \<and>
            (a, w, b) \<notin> set p'2 \<and> (b, w, a) \<notin> set p'2)"
      by metis
    with len_p' p' u have p': "\<exists>p' u. is_path_undir G v p' u \<and> length p' < length p \<and>
      u \<in> {a,b} \<and> (a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p'"
      by fastforce
    from 1 len_p'' p'' have "(a, w, b) \<in> set p'' \<or> (b, w, a) \<in> set p'' \<longrightarrow> (\<exists>p''2 u'2.
            is_path_undir G u'2 p''2 v' \<and>
            length p''2 < length p'' \<and>
            u'2 \<in> {a, b} \<and>
            (a, w, b) \<notin> set p''2 \<and> (b, w, a) \<notin> set p''2)"
      by metis
    with len_p'' p'' u have "\<exists>p'' u'. is_path_undir G u' p'' v'\<and> length p'' < length p \<and>
      u' \<in> {a,b} \<and> (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p''"
      by fastforce
    with p' show ?case by auto
  qed

  lemma add_edge_is_path:
    assumes "is_path_undir G x p y"
    shows "is_path_undir (add_edge a b c G) x p y"
  proof -
    from E_valid have "valid_graph (add_edge a b c G)"
      unfolding valid_graph_def add_edge_def
      by auto
    with assms is_path_undir.simps[of "add_edge a b c G"]
    show "is_path_undir (add_edge a b c G) x p y"
      by (induction p arbitrary: x y) auto
  qed

  lemma add_edge_was_path:
    assumes "is_path_undir (add_edge a b c G) x p y"
    assumes "(a, b, c) \<notin> set p"
    assumes "(c, b, a) \<notin> set p"
    assumes "a \<in> V"
    assumes "c \<in> V"
    shows "is_path_undir G x p y"
  proof -
    from E_valid have "valid_graph (add_edge a b c G)"
      unfolding valid_graph_def add_edge_def
      by auto
    with assms is_path_undir.simps[of "add_edge a b c G"]
    show "is_path_undir G x p y"
      by (induction p arbitrary: x y) auto
  qed

  lemma delete_edge_is_path:
    assumes "is_path_undir G x p y"
    assumes "(a, b, c) \<notin> set p"
    assumes "(c, b, a) \<notin> set p"
    shows "is_path_undir (delete_edge a b c G) x p y"
  proof -
    from E_valid have "valid_graph (delete_edge a b c G)"
      unfolding valid_graph_def delete_edge_def
      by auto
    with assms is_path_undir.simps[of "delete_edge a b c G"]
    show ?thesis
      by (induction p arbitrary: x y) auto
  qed

  lemma delete_node_is_path:
    assumes "is_path_undir G x p y"
    assumes "x \<noteq> v"
    assumes "v \<notin> fst`set p \<union> snd`snd`set p"
    shows "is_path_undir (delete_node v G) x p y"
    using assms
    unfolding delete_node_def
    by (induction p arbitrary: x y) auto

  lemma delete_edge_was_path:
    assumes "is_path_undir (delete_edge a b c G) x p y"
    shows "is_path_undir G x p y"
    using assms
    by (induction p arbitrary: x y) auto

  lemma subset_was_path:
    assumes "is_path_undir H x p y"
    assumes "edges H \<subseteq> E"
    assumes "nodes H \<subseteq> V"
    shows "is_path_undir G x p y"
    using assms
    by (induction p arbitrary: x y) auto

  lemma delete_node_was_path:
    assumes "is_path_undir (delete_node v G) x p y"
    shows "is_path_undir G x p y"
    using assms
    unfolding delete_node_def
    by (induction p arbitrary: x y) auto

  lemma add_edge_preserve_subgraph:
    assumes "subgraph H G"
    assumes "(a, w, b) \<in> E"
    shows "subgraph (add_edge a w b H) G"
  proof -
    from assms E_validD have "a \<in> nodes H \<and> b \<in> nodes H"
      unfolding subgraph_def by simp
    with assms show ?thesis
      unfolding subgraph_def
      by auto
  qed

  lemma delete_edge_preserve_subgraph:
    assumes "subgraph H G"
    shows "subgraph (delete_edge a w b H) G"
    using assms
    unfolding subgraph_def
    by auto

  lemma add_delete_edge:
    assumes "(a, w, c) \<in> E"
    shows "add_edge a w c (delete_edge a w c G) = G"
    using assms E_validD unfolding delete_edge_def add_edge_def
    by (simp add: insert_absorb)

  lemma swap_add_edge_in_path:
    assumes "is_path_undir (add_edge a w b G) v p v'"
    assumes "(a,w',a') \<in> E \<or> (a',w',a) \<in> E"
    shows "\<exists>p. is_path_undir (add_edge a' w'' b G) v p v'"
  using assms(1)
  proof (induction p arbitrary: v)
    case Nil
    with assms(2) E_validD
    have "is_path_undir (add_edge a' w'' b G) v [] v'"
      by auto
    then show ?case
      by blast
  next
    case (Cons e p')
    then obtain v2 x e_w where "e = (v2, e_w, x)"
      using prod_cases3 by blast
    with Cons(2)
    have e: "e = (v, e_w, x)" and
         edge_e: "(v, e_w, x) \<in> edges (add_edge a w b G)
                   \<or> (x, e_w, v) \<in> edges (add_edge a w b G)" and
         p': "is_path_undir (add_edge a w b G) x p' v'"
      by auto
    have "\<exists>p. is_path_undir (add_edge a' w'' b G) v p x"
    proof (cases "e = (a, w, b) \<or> e = (b, w, a)")
      case True
      from True e assms(2) E_validD
      have "is_path_undir (add_edge a' w'' b G) v [(a,w',a'), (a',w'',b)] x
          \<or> is_path_undir (add_edge a' w'' b G) v [(b,w'',a'), (a',w',a)] x"
        by auto
      then show ?thesis
        by blast
    next
      case False
      with edge_e e
      have "is_path_undir (add_edge a' w'' b G) v [e] x"
        by (auto simp: E_validD)
      then show ?thesis
        by auto
    qed
    with p' Cons.IH 
     and valid_graph.is_path_undir_split[OF add_edge_valid[OF valid_graph.intro[OF E_valid]]]
    show ?case
      by blast
  qed

  lemma induce_maximally_connected:
    assumes "subgraph H G"
    assumes "\<forall>(a,w,b)\<in>E. nodes_connected H a b"
    shows "maximally_connected H G"
  proof -
    from valid_subgraph[OF \<open>subgraph H G\<close>]
    have valid_H: "valid_graph H" .
    have "(nodes_connected G v v') \<longrightarrow> (nodes_connected H v v')" (is "?lhs \<longrightarrow> ?rhs")
      if "v\<in>V" and "v'\<in>V" for v v'
    proof
      assume ?lhs
      then obtain p where "is_path_undir G v p v'"
        by blast
      then show ?rhs
      proof (induction p arbitrary: v v')
        case Nil
        with subgraph_node[OF assms(1)] show ?case
          by (metis is_path_undir.simps(1))
      next
        case (Cons e p)
        from prod_cases3 obtain a w b where awb: "e = (a, w, b)" .
        with assms Cons.prems valid_graph.is_path_undir_sym[OF valid_H, of b _ a]
        obtain p' where p': "is_path_undir H a p' b"
          by fastforce
        from assms awb Cons.prems Cons.IH[of b v']
        obtain p'' where "is_path_undir H b p'' v'"
          unfolding subgraph_def by auto
        with Cons.prems awb assms p' valid_graph.is_path_undir_split[OF valid_H]
          have "is_path_undir H v (p'@p'') v'"
            by auto
        then show ?case ..
      qed
    qed
    with assms show ?thesis
      unfolding maximally_connected_def
      by auto
  qed

  lemma add_edge_maximally_connected:
    assumes "maximally_connected H G"
    assumes "subgraph H G"
    assumes "(a, w, b) \<in> E"
    shows "maximally_connected (add_edge a w b H) G"
  proof -
    have "(nodes_connected G v v') \<longrightarrow> (nodes_connected (add_edge a w b H) v v')"
      (is "?lhs \<longrightarrow> ?rhs") if vv': "v \<in> V" "v' \<in> V" for v v'
    proof
      assume ?lhs
      with \<open>maximally_connected H G\<close> vv' obtain p where "is_path_undir H v p v'"
        unfolding maximally_connected_def
        by auto
      with valid_graph.add_edge_is_path[OF valid_subgraph[OF \<open>subgraph H G\<close>] this]
      show ?rhs
        by auto
    qed
    then show ?thesis
      unfolding maximally_connected_def
      by auto
  qed

  lemma delete_edge_maximally_connected:
    assumes "maximally_connected H G"
    assumes "subgraph H G"
    assumes pab: "is_path_undir (delete_edge a w b H) a pab b"
    shows "maximally_connected (delete_edge a w b H) G"
  proof -
    from valid_subgraph[OF \<open>subgraph H G\<close>]
    have valid_H: "valid_graph H" .
    have "(nodes_connected G v v') \<longrightarrow> (nodes_connected (delete_edge a w b H) v v')" 
      (is "?lhs \<longrightarrow> ?rhs") if vv': "v \<in> V" "v' \<in> V" for v v'
    proof
      assume ?lhs
      with \<open>maximally_connected H G\<close> vv' obtain p where p: "is_path_undir H v p v'"
        unfolding maximally_connected_def
        by auto
      show ?rhs
      proof (cases "(a, w, b) \<in> set p \<or> (b, w, a) \<in> set p")
        case True
        with p valid_graph.is_path_undir_split_distinct[OF valid_H p, of a w b] obtain p' p'' u u'
          where "is_path_undir H v p' u \<and> is_path_undir H u' p'' v'" and
            u: "(u \<in> {a, b} \<and> u' \<in> {a, b})" and
            "(a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
            (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p''"
          by auto
        with valid_graph.delete_edge_is_path[OF valid_H] obtain p' p''
          where p': "is_path_undir (delete_edge a w b H) v p' u \<and>
                 is_path_undir (delete_edge a w b H) u' p'' v'"
          by blast
        note dev_H = delete_edge_valid[OF valid_H]
        note * = valid_graph.is_path_undir_split[OF dev_H, of a w b v]
        from valid_graph.is_path_undir_sym[OF delete_edge_valid[OF valid_H] pab] obtain pab'
          where "is_path_undir (delete_edge a w b H) b pab' a"
          by auto
        with assms u p' valid_graph.is_path_undir_split[OF dev_H, of a w b v p' p'' v']
          *[of p' pab b] *[of "p'@pab" p'' v'] *[of p' pab' a] *[of "p'@pab'" p'' v']
        show ?thesis by auto
      next
        case False
        with valid_graph.delete_edge_is_path[OF valid_H p] show ?thesis
          by auto
      qed
    qed
    then show ?thesis
      unfolding maximally_connected_def
      by auto
  qed

  lemma connected_impl_maximally_connected:
    assumes "connected_graph H"
    assumes subgraph: "subgraph H G"
    shows "maximally_connected H G"
    using assms
    unfolding connected_graph_def connected_graph_axioms_def maximally_connected_def
      subgraph_def
    by blast

  lemma add_edge_is_connected:
    "nodes_connected (add_edge a b c G) a c"
    "nodes_connected (add_edge a b c G) c a"
  using valid_graph.is_path_undir_simps(2)[OF
        add_edge_valid[OF valid_graph_axioms], of a b c a b c]
      valid_graph.is_path_undir_simps(2)[OF
        add_edge_valid[OF valid_graph_axioms], of a b c c b a]
  by fastforce+

  lemma swap_edges:
    assumes "nodes_connected (add_edge a w b G) v v'"
    assumes "a \<in> V"
    assumes "b \<in> V"
    assumes "\<not> nodes_connected G v v'"
    shows "nodes_connected (add_edge v w' v' G) a b"
  proof -
    from assms(1) obtain p where p: "is_path_undir (add_edge a w b G) v p v'"
      by auto
    have awb: "(a, w, b) \<in> set p \<or> (b, w, a) \<in> set p"
    proof (rule ccontr)
      assume "\<not> ((a, w, b) \<in> set p \<or> (b, w, a) \<in> set p)"
      with add_edge_was_path[OF p _ _ assms(2,3)] assms(4)
      show False
        by auto
    qed
    from valid_graph.is_path_undir_split_distinct[OF
        add_edge_valid[OF valid_graph_axioms] p awb]
    obtain p' p'' u u' where
         "is_path_undir (add_edge a w b G) v p' u \<and>
          is_path_undir (add_edge a w b G) u' p'' v'" and
          u: "u \<in> {a, b} \<and> u' \<in> {a, b}" and
          "(a, w, b) \<notin> set p' \<and> (b, w, a) \<notin> set p' \<and>
          (a, w, b) \<notin> set p'' \<and> (b, w, a) \<notin> set p'' "
      by auto
    with assms(2,3) add_edge_was_path
    have paths: "is_path_undir G v p' u \<and>
                 is_path_undir G u' p'' v'"
      by blast
    with is_path_undir_split[of v p' p'' v'] assms(4)
    have "u \<noteq> u'"
      by blast
    from paths assms add_edge_is_path
    have paths': "is_path_undir (add_edge v w' v' G) v p' u \<and>
                  is_path_undir (add_edge v w' v' G) u' p'' v'"
      by blast
    note * = add_edge_valid[OF valid_graph_axioms]
    from add_edge_is_connected obtain p''' where
      "is_path_undir (add_edge v w' v' G) v' p''' v"
      by blast
    with paths' valid_graph.is_path_undir_split[OF *, of v w' v' u' p'' p''' v]
    have "is_path_undir (add_edge v w' v' G) u' (p''@p''') v"
        by auto
    with paths' valid_graph.is_path_undir_split[OF *, of v w' v' u' "p''@p'''" p' u]
    have "is_path_undir (add_edge v w' v' G) u' (p''@p'''@p') u"
        by auto
    with u \<open>u \<noteq> u'\<close> valid_graph.is_path_undir_sym[OF * this]
    show ?thesis
      by auto
  qed

  lemma subgraph_impl_connected:
    assumes "connected_graph H"
    assumes subgraph: "subgraph H G"
    shows "connected_graph G"
    using assms is_path_undir_subgraph[OF _ subgraph] valid_graph_axioms
    unfolding connected_graph_def connected_graph_axioms_def maximally_connected_def
      subgraph_def
    by blast

  lemma add_node_connected:
    assumes "\<forall>a\<in>V - {v}. \<forall>b\<in>V - {v}. nodes_connected G a b"
    assumes "(v, w, v') \<in> E \<or> (v', w, v) \<in> E"
    assumes "v \<noteq> v'"
    shows "\<forall>a\<in>V. \<forall>b\<in>V. nodes_connected G a b"
  proof -
    have "nodes_connected G a b" if a: "a\<in>V" and b: "b\<in>V" for a b
    proof (cases "a = v")
      case True
      show ?thesis
      proof (cases "b = v")
        case True
        with \<open>a = v\<close> a is_path_undir_simps(1) show ?thesis
          by blast
      next
        case False
        from assms(2) have "v' \<in> V"
          by (auto simp: E_validD)
        with b assms(1) \<open>b \<noteq> v\<close> \<open>v \<noteq> v'\<close> have "nodes_connected G v' b"
          by blast
        with assms(2) \<open>a = v\<close> is_path_undir.simps(2)[of G v v w v' _ b]
        show ?thesis
          by blast
      qed
    next
      case False
      show ?thesis
      proof (cases "b = v")
        case True
        from assms(2) have "v' \<in> V"
          by (auto simp: E_validD)
        with a assms(1) \<open>a \<noteq> v\<close> \<open>v \<noteq> v'\<close> have "nodes_connected G a v'"
          by blast
        with assms(2) \<open>b = v\<close> is_path_undir.simps(2)[of G v v w v' _ a]
          is_path_undir_sym
        show ?thesis
          by blast
      next
        case False
        with \<open>a \<noteq> v\<close> assms(1) a b show ?thesis
          by simp
      qed
    qed
    then show ?thesis by simp
  qed
end

context connected_graph
begin
  lemma maximally_connected_impl_connected:
    assumes "maximally_connected H G"
    assumes subgraph: "subgraph H G"
    shows "connected_graph H"
    using assms connected_graph_axioms valid_subgraph[OF subgraph]
    unfolding connected_graph_def connected_graph_axioms_def maximally_connected_def
      subgraph_def
    by auto
end

context forest
begin

  lemmas delete_edge_valid' = delete_edge_valid[OF valid_graph_axioms]

  lemma delete_edge_from_path:
    assumes "nodes_connected G a b"
    assumes "subgraph H G"
    assumes "\<not> nodes_connected H a b"
    shows "\<exists>(x, w, y) \<in> E - edges H.  (\<not> nodes_connected (delete_edge x w y G) a b) \<and>
      (nodes_connected (add_edge a w' b (delete_edge x w y G)) x y)"
  proof -
    from assms(1) obtain p where "is_path_undir G a p b"
      by auto
    from this assms(3) show ?thesis
    proof (induction n == "length p" arbitrary: p a b rule: nat_less_induct)
      case 1
      from valid_subgraph[OF assms(2)] have valid_H: "valid_graph H" .
      show ?case
      proof (cases p)
        case Nil
        with 1(2) have "a = b"
          by simp
        with 1(2) assms(2) have "is_path_undir H a [] b"
          unfolding subgraph_def
          by auto
        with 1(3) show ?thesis
          by blast
      next
        case (Cons e p')
        obtain a2 a' w where "e = (a2, w, a')"
          using prod_cases3 by blast
        with 1(2) Cons have e: "e = (a, w, a')"
          by simp
        with 1(2) Cons obtain e1 e2 where e12: "e = (e1, w, e2) \<or> e = (e2, w, e1)" and
          edge_e12: "(e1, w, e2) \<in> E"
          by auto
        from 1(2) Cons e have "is_path_undir G a' p' b"
          by simp
        with is_path_undir_split_distinct[OF this, of a w a'] Cons
        obtain p'_dst u' where  p'_dst: "is_path_undir G u' p'_dst b \<and> u' \<in> {a, a'}" and
            e_not_in_p': "(a, w, a') \<notin> set p'_dst \<and> (a', w, a) \<notin> set p'_dst" and
            len_p': "length p'_dst < length p"
          by fastforce 
        show ?thesis
        proof (cases "u' = a'")
          case False
          with 1 len_p' p'_dst show ?thesis
            by auto
        next
          case True
          with p'_dst have path_p': "is_path_undir G a' p'_dst b"
            by auto
          show ?thesis
          proof (cases "(e1, w, e2) \<in> edges H")
            case True
            have "\<not> nodes_connected H a' b"
            proof
              assume "nodes_connected H a' b"
              then obtain p_H where "is_path_undir H a' p_H b"
                by auto
              with True e12 e have "is_path_undir H a (e#p_H) b"
                by auto
              with 1(3) show False
                by simp
            qed
            with path_p' 1(1) len_p' obtain x z y where xy: "(x, z, y) \<in> E - edges H" and
              IH1: "(\<not>nodes_connected (delete_edge x z y G) a' b)" and
              IH2: "(nodes_connected (add_edge a' w' b (delete_edge x z y G)) x y)"
              by blast
            with True have xy_neq_e: "(x,z,y) \<noteq> (e1, w, e2)"
              by auto
            have thm1: "\<not> nodes_connected (delete_edge x z y G) a b"
            proof
              assume "nodes_connected (delete_edge x z y G) a b"
              then obtain p_e where "is_path_undir (delete_edge x z y G) a p_e b"
                by auto
              with edge_e12 e12 e xy_neq_e
              have "is_path_undir (delete_edge x z y G) a' ((a', w, a)#p_e) b"
                by auto
              with IH1 show False
                by blast
            qed
            from IH2 obtain p_xy
              where "is_path_undir (add_edge a' w' b (delete_edge x z y G)) x p_xy y"
              by auto
            from valid_graph.swap_add_edge_in_path[OF delete_edge_valid' this, of w a w'] edge_e12
              e12 e edges_delete_edge[of x z y G] xy_neq_e
            have thm2: "nodes_connected (add_edge a w' b (delete_edge x z y G)) x y"
              by blast
            with thm1 show ?thesis
              using xy by auto
          next
            case False
            have thm1: "\<not> nodes_connected (delete_edge e1 w e2 G) a b"
            proof
              assume "nodes_connected (delete_edge e1 w e2 G) a b"
              then obtain p_e where p_e: "is_path_undir (delete_edge e1 w e2 G) a p_e b"
                by auto
              from delete_edge_is_path[OF path_p', of e1 w e2] e_not_in_p' e12 e
              have "is_path_undir (delete_edge e1 w e2 G) a' p'_dst b"
                by auto
              with valid_graph.is_path_undir_sym[OF delete_edge_valid' this]
              obtain p_rev where "is_path_undir (delete_edge e1 w e2 G) b p_rev a'"
                by auto
              with p_e valid_graph.is_path_undir_split[OF delete_edge_valid']
              have "is_path_undir (delete_edge e1 w e2 G) a (p_e@p_rev) a'"
                by auto
              with cycle_free edge_e12 e12 e
                and valid_graph.is_path_undir_sym[OF delete_edge_valid' this]
              show False
                unfolding valid_graph_def
                by auto
            qed
            note ** = delete_edge_is_path[OF path_p', of e1 w e2]
            from valid_graph.is_path_undir_split[OF add_edge_valid[OF delete_edge_valid']]
              valid_graph.add_edge_is_path[OF delete_edge_valid' **, of a w' b]
              valid_graph.is_path_undir_simps(2)[OF add_edge_valid[OF delete_edge_valid'],
                                                 of a w' b e1 w e2 b w' a]
              e_not_in_p' e12 e
            have "is_path_undir (add_edge a w' b (delete_edge e1 w e2 G)) a' (p'_dst@[(b,w',a)]) a"
              by auto
            with valid_graph.is_path_undir_sym[OF add_edge_valid[OF delete_edge_valid'] this]
              e12 e
            have "nodes_connected (add_edge a w' b (delete_edge e1 w e2 G)) e1 e2"
              by blast
            with thm1 show ?thesis
              using False edge_e12 by auto
          qed
        qed
      qed
    qed
  qed

  lemma forest_add_edge:
    assumes "a \<in> V"
    assumes "b \<in> V"
    assumes "\<not> nodes_connected G a b"
    shows "forest (add_edge a w b G)"
  proof -
    from assms(3) have "\<not> is_path_undir G a [(a, w, b)] b"
      by blast
    with assms(2) have awb: "(a, w, b) \<notin> E \<and> (b, w, a) \<notin> E"
      by auto
    have "\<not> nodes_connected (delete_edge v w' v' (add_edge a w b G)) v v'"
       if e: "(v,w',v')\<in> edges (add_edge a w b G)" for v w' v'
    proof (cases "(v,w',v') = (a, w, b)")
      case True
      with assms awb delete_add_edge[of a G b w]
      show ?thesis by simp
    next
      case False
      with e have e': "(v,w',v')\<in> edges G"
        by auto 
      show ?thesis
      proof
        assume asm: "nodes_connected (delete_edge v w' v' (add_edge a w b G)) v v'"
        with swap_delete_add_edge[OF False, of G]
          valid_graph.swap_edges[OF delete_edge_valid', of a w b v w' v' v v' w']
          add_delete_edge[OF e'] cycle_free assms(1,2) e'
        have "nodes_connected G a b"
          by force
        with assms show False
          by simp
      qed
    qed
    with cycle_free add_edge_valid[OF valid_graph_axioms] show ?thesis
      unfolding forest_def forest_axioms_def by auto
  qed

  lemma forest_subsets:
    assumes "valid_graph H"
    assumes "edges H \<subseteq> E"
    assumes "nodes H \<subseteq> V"
    shows "forest H"
  proof -
    have "\<not> nodes_connected (delete_edge a w b H) a b"
      if e: "(a, w, b)\<in>edges H" for a w b
    proof
      assume asm: "nodes_connected (delete_edge a w b H) a b"
      from \<open>edges H \<subseteq> E\<close> 
      have edges: "edges (delete_edge a w b H) \<subseteq> edges (delete_edge a w b G)"
        by auto
      from \<open>nodes H \<subseteq> V\<close> 
      have nodes: "nodes (delete_edge a w b H) \<subseteq> nodes (delete_edge a w b G)"
        by auto
      from asm valid_graph.subset_was_path[OF delete_edge_valid' _ edges nodes]
      have "nodes_connected (delete_edge a w b G) a b"
        by auto
      with cycle_free e \<open>edges H \<subseteq> E\<close> show False
        by blast
    qed
    with assms(1) show ?thesis
    unfolding forest_def forest_axioms_def
    by auto
  qed

  lemma subgraph_forest:
    assumes "subgraph H G"
    shows "forest H"
    using assms forest_subsets valid_subgraph
    unfolding subgraph_def
    by simp

  lemma forest_delete_edge: "forest (delete_edge a w c G)"
    using forest_subsets[OF delete_edge_valid']
    unfolding delete_edge_def
    by auto

  lemma forest_delete_node: "forest (delete_node n G)"
    using forest_subsets[OF delete_node_valid[OF valid_graph_axioms]]
    unfolding delete_node_def
    by auto
end

context finite_graph
begin
 

  lemma finite_subgraphs: "finite {T. subgraph T G}"
  proof -
    from finite_E have "finite {E'. E' \<subseteq> E}"
      by simp
    then have "finite {\<lparr>nodes = V, edges = E'\<rparr>| E'. E' \<subseteq> E}"
      by simp
    also have "{\<lparr>nodes = V, edges = E'\<rparr>| E'. E' \<subseteq> E} = {T. subgraph T G}"
      unfolding subgraph_def
      by (metis (mono_tags, lifting) old.unit.exhaust select_convs(1) select_convs(2) surjective)
    finally show ?thesis .
  qed
 
end 

lemma minimum_spanning_forest_impl_tree:
  assumes "minimum_spanning_forest F G"
  assumes valid_G: "valid_graph G"
  assumes "connected_graph F"
  shows "minimum_spanning_tree F G"
  using assms valid_graph.connected_impl_maximally_connected[OF valid_G]
  unfolding minimum_spanning_forest_def minimum_spanning_tree_def
    spanning_forest_def spanning_tree_def tree_def
    optimal_forest_def optimal_tree_def
  by auto

lemma minimum_spanning_forest_impl_tree2:
  assumes "minimum_spanning_forest F G"
  assumes connected_G: "connected_graph G"
  shows "minimum_spanning_tree F G"
  using assms connected_graph.maximally_connected_impl_connected[OF connected_G]
    minimum_spanning_forest_impl_tree connected_graph.axioms(1)[OF connected_G]
  unfolding minimum_spanning_forest_def spanning_forest_def
  by auto

end
