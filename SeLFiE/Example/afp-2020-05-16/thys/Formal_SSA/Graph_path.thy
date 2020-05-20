(*  Title:      Graph_path.thy
    Author:     Sebastian Ullrich
*)

section \<open>SSA Representation\<close>

subsection \<open>Inductive Graph Paths\<close>

text \<open>We extend the Graph framework with inductively defined paths.
  We adopt the convention of separating locale definitions into assumption-less base locales.\<close>

theory Graph_path imports
  FormalSSA_Misc
  Dijkstra_Shortest_Path.GraphSpec
  CAVA_Automata.Digraph_Basic
begin

hide_const "Omega_Words_Fun.prefix" "Omega_Words_Fun.suffix"

type_synonym ('n, 'ed) edge = "('n \<times> 'ed \<times> 'n)"

definition getFrom :: "('n, 'ed) edge \<Rightarrow> 'n" where
  "getFrom \<equiv> fst"
definition getData :: "('n, 'ed) edge \<Rightarrow> 'ed" where
  "getData \<equiv> fst \<circ> snd"
definition getTo :: "('n, 'ed) edge \<Rightarrow> 'n" where
  "getTo \<equiv> snd \<circ> snd"

lemma get_edge_simps [simp]:
  "getFrom (f,d,t) = f"
  "getData (f,d,t) = d"
  "getTo (f,d,t) = t"
  by (simp_all add: getFrom_def getData_def getTo_def)

  text \<open>Predecessors of a node.\<close>
  definition pred :: "('v,'w) graph \<Rightarrow> 'v \<Rightarrow> ('v\<times>'w) set"
    where "pred G v \<equiv> {(v',w). (v',w,v)\<in>edges G}"

  lemma pred_finite[simp, intro]: "finite (edges G) \<Longrightarrow> finite (pred G v)"
    unfolding pred_def
    by (rule finite_subset[where B="(\<lambda>(v,w,v'). (v,w))`edges G"]) force+

  lemma pred_empty[simp]: "pred empty v = {}" unfolding empty_def pred_def by auto

  lemma (in valid_graph) pred_subset: "pred G v \<subseteq> V\<times>UNIV"
    unfolding pred_def using E_valid
    by (force)

  type_synonym ('V,'W,'\<sigma>,'G) graph_pred_it =
    "'G \<Rightarrow> 'V \<Rightarrow> ('V\<times>'W,'\<sigma>) set_iterator"

  locale graph_pred_it_defs =
    fixes pred_list_it :: "'G \<Rightarrow> 'V \<Rightarrow> ('V\<times>'W,('V\<times>'W) list) set_iterator"
  begin
    definition "pred_it g v \<equiv> it_to_it (pred_list_it g v)"
  end

  locale graph_pred_it = graph \<alpha> invar + graph_pred_it_defs pred_list_it
    for \<alpha> :: "'G \<Rightarrow> ('V,'W) graph" and invar and
    pred_list_it :: "'G \<Rightarrow> 'V \<Rightarrow> ('V\<times>'W,('V\<times>'W) list) set_iterator" +
    assumes pred_list_it_correct:
      "invar g \<Longrightarrow> set_iterator (pred_list_it g v) (pred (\<alpha> g) v)"
  begin
    lemma pred_it_correct:
      "invar g \<Longrightarrow> set_iterator (pred_it g v) (pred (\<alpha> g) v)"
      unfolding pred_it_def
      apply (rule it_to_it_correct)
      by (rule pred_list_it_correct)

    lemma pi_pred_it[icf_proper_iteratorI]:
      "proper_it (pred_it S v) (pred_it S v)"
      unfolding pred_it_def
      by (intro icf_proper_iteratorI)

    lemma pred_it_proper[proper_it]:
      "proper_it' (\<lambda>S. pred_it S v) (\<lambda>S. pred_it S v)"
      apply (rule proper_it'I)
      by (rule pi_pred_it)
  end

  record ('V,'W,'G) graph_ops = "('V,'W,'G) GraphSpec.graph_ops" +
    gop_pred_list_it :: "'G \<Rightarrow> 'V \<Rightarrow> ('V\<times>'W,('V\<times>'W) list) set_iterator"

  lemma (in graph_pred_it) pred_it_is_iterator[refine_transfer]:
    "invar g \<Longrightarrow> set_iterator (pred_it g v) (pred (\<alpha> g) v)"
    by (rule pred_it_correct)

locale StdGraphDefs = GraphSpec.StdGraphDefs ops
  + graph_pred_it_defs "gop_pred_list_it ops"
  for ops :: "('V,'W,'G,'m) graph_ops_scheme"
begin
  abbreviation pred_list_it  where "pred_list_it \<equiv> gop_pred_list_it ops"
end

locale StdGraph = StdGraphDefs + org:StdGraph +
  graph_pred_it \<alpha> invar pred_list_it

locale graph_path_base =
  graph_nodes_it_defs "\<lambda>g. foldri (\<alpha>n g)" +
  graph_pred_it_defs "\<lambda>g n. foldri (inEdges' g n)"
for
  \<alpha>e :: "'g \<Rightarrow> ('node \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list"
begin

(*
  abbreviation \<alpha>e :: "'g \<Rightarrow> ('node \<times> 'edgeD \<times> 'node) set"
  where "\<alpha>e g \<equiv> graph.edges (\<alpha> g)"
  definition \<alpha>n :: "'g \<Rightarrow> 'node list"
  where "\<alpha>n g \<equiv> nodes_it g (\<lambda>_. True) (#) []"
*)

  definition inEdges :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD \<times> 'node) list"
  where "inEdges g n \<equiv> map (\<lambda>(f,d). (f,d,n)) (inEdges' g n)"

  definition predecessors :: "'g \<Rightarrow> 'node \<Rightarrow> 'node list" where
    "predecessors g n \<equiv> map getFrom (inEdges g n)"

  definition successors :: "'g \<Rightarrow> 'node \<Rightarrow> 'node list" where
    "successors g m \<equiv> [n . n \<leftarrow> \<alpha>n g, m \<in> set (predecessors g n)]"


  declare predecessors_def [code]

  declare [[inductive_internals]]
  inductive path :: "'g \<Rightarrow> 'node list \<Rightarrow> bool"
    for g :: 'g
  where
    empty_path[intro]: "\<lbrakk>n \<in> set (\<alpha>n g); invar g\<rbrakk> \<Longrightarrow> path g [n]"
    | Cons_path[intro]: "\<lbrakk>path g ns; n' \<in> set (predecessors g (hd ns))\<rbrakk> \<Longrightarrow> path g (n'#ns)"

  definition path2 :: "'g \<Rightarrow> 'node \<Rightarrow> 'node list \<Rightarrow> 'node \<Rightarrow> bool" ("_ \<turnstile> _-_\<rightarrow>_" [51,0,0,51] 80) where
    "path2 g n ns m \<equiv> path g ns \<and> n = hd ns \<and> m = last ns"

  abbreviation "\<alpha> g \<equiv> \<lparr>nodes = set (\<alpha>n g), edges = \<alpha>e g\<rparr>"
end

locale graph_path =
  graph_path_base \<alpha>e \<alpha>n invar inEdges' +
  graph \<alpha> invar +
  ni: graph_nodes_it \<alpha> invar "\<lambda>g. foldri (\<alpha>n g)" +
  pi: graph_pred_it \<alpha> invar "\<lambda>g n. foldri (inEdges' g n)"
for
  \<alpha>e :: "'g \<Rightarrow> ('node \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list"
begin
  lemma \<alpha>n_correct: "invar g \<Longrightarrow> set (\<alpha>n g) \<supseteq> getFrom ` \<alpha>e g \<union> getTo ` \<alpha>e g"
    by (frule valid) (auto dest: valid_graph.E_validD)

  lemma \<alpha>n_distinct: "invar g \<Longrightarrow> distinct (\<alpha>n g)"
    by (frule ni.nodes_list_it_correct)
      (metis foldri_cons_id iterate_to_list_correct iterate_to_list_def)

  lemma inEdges_correct':
    assumes "invar g"
    shows "set (inEdges g n) = (\<lambda>(f,d). (f,d,n)) ` (pred (\<alpha> g) n)"
  proof -
    from iterate_to_list_correct [OF pi.pred_list_it_correct [OF assms], of n]
    show ?thesis
      by (auto intro: rev_image_eqI simp: iterate_to_list_def pred_def inEdges_def)
  qed

  lemma inEdges_correct [intro!, simp]:
    "invar g \<Longrightarrow> set (inEdges g n) = {(_, _, t). t = n} \<inter> \<alpha>e g"
    by (auto simp: inEdges_correct' pred_def)

  lemma in_set_\<alpha>nI1 [intro]: "\<lbrakk>invar g; x \<in> getFrom ` \<alpha>e g\<rbrakk> \<Longrightarrow> x \<in> set (\<alpha>n g)"
    using \<alpha>n_correct by blast
  lemma in_set_\<alpha>nI2 [intro]: "\<lbrakk>invar g; x \<in> getTo ` \<alpha>e g\<rbrakk> \<Longrightarrow> x \<in> set (\<alpha>n g)"
    using \<alpha>n_correct by blast

(*

locale graph_path_base = graph_inEdges_base \<alpha>e invar inEdges + graph_nodes_base \<alpha>e invar \<alpha>n
for
  \<alpha>e :: "'g \<Rightarrow> ('node \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD \<times> 'node) list"
begin
*)

(*
end

locale graph_path = graph_path_base \<alpha>e \<alpha>n invar inEdges + graph_inEdges \<alpha>e invar inEdges + graph_nodes \<alpha>e invar \<alpha>n
for
  \<alpha>e :: "'g \<Rightarrow> ('node \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD \<times> 'node) list"
begin
*)

  lemma edge_to_node:
    assumes "invar g" and "e \<in> \<alpha>e g"
    obtains "getFrom e \<in> set (\<alpha>n g)" and "getTo e \<in> set (\<alpha>n g)"
  using assms(2) \<alpha>n_correct [OF \<open>invar g\<close>]
    by (cases e) (auto 4 3 intro: rev_image_eqI)

  lemma inEdge_to_edge:
    assumes "e \<in> set (inEdges g n)" and "invar g"
    obtains eD n' where "(n',eD,n) \<in> \<alpha>e g"
    using assms by auto

  lemma edge_to_inEdge:
    assumes "(n,eD,m) \<in> \<alpha>e g" "invar g"
    obtains "(n,eD,m) \<in> set (inEdges g m)"
    using assms by auto

  lemma edge_to_predecessors:
    assumes "(n,eD,m) \<in> \<alpha>e g" "invar g"
    obtains "n \<in> set (predecessors g m)"
  proof atomize_elim
    from assms have "(n,eD,m) \<in> set (inEdges g m)" by (rule edge_to_inEdge)
    thus "n \<in> set (predecessors g m)" unfolding predecessors_def by (metis get_edge_simps(1) image_eqI set_map)
  qed

  lemma predecessor_is_node[elim]: "\<lbrakk>n \<in> set (predecessors g n'); invar g\<rbrakk> \<Longrightarrow> n \<in> set (\<alpha>n g)"
  unfolding predecessors_def by (fastforce intro: rev_image_eqI simp: getTo_def getFrom_def)

  lemma successor_is_node[elim]: "\<lbrakk>n \<in> set (predecessors g n'); n \<in> set (\<alpha>n g); invar g\<rbrakk> \<Longrightarrow> n' \<in> set (\<alpha>n g)"
  unfolding predecessors_def by (fastforce intro: rev_image_eqI)

  lemma successors_predecessors[simp]: "n \<in> set (\<alpha>n g) \<Longrightarrow> n \<in> set (successors g m) \<longleftrightarrow> m \<in> set (predecessors g n)"
  by (auto simp:successors_def predecessors_def)


  lemma path_not_Nil[simp, dest]: "path g ns \<Longrightarrow> ns \<noteq> []"
  by (erule path.cases) auto

  lemma path2_not_Nil[simp]: "g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> ns \<noteq> []"
  unfolding path2_def by auto

  lemma path2_not_Nil2[simp]: "\<not> g \<turnstile> n-[]\<rightarrow>m"
  unfolding path2_def by auto

  lemma path2_not_Nil3[simp]: "g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> length ns \<ge> 1"
    by (cases ns, auto)

  lemma empty_path2[intro]: "\<lbrakk>n \<in> set (\<alpha>n g); invar g\<rbrakk> \<Longrightarrow> g \<turnstile> n-[n]\<rightarrow>n"
  unfolding path2_def by auto

  lemma Cons_path2[intro]: "\<lbrakk>g \<turnstile> n-ns\<rightarrow>m; n' \<in> set (predecessors g n)\<rbrakk> \<Longrightarrow> g \<turnstile> n'-n'#ns\<rightarrow>m"
  unfolding path2_def by auto

  lemma path2_cases:
    assumes "g \<turnstile> n-ns\<rightarrow>m"
    obtains (empty_path) "ns = [n]" "m = n"
          | (Cons_path) "g \<turnstile> hd (tl ns)-tl ns\<rightarrow>m" "n \<in> set (predecessors g (hd (tl ns)))"
  proof-
    from assms have 1: "path g ns" "hd ns = n" "last ns = m" by (auto simp: path2_def)
    from this(1) show thesis
    proof cases
      case (empty_path n)
      with 1 show thesis by - (rule that(1), auto)
    next
      case (Cons_path ns n')
      with 1 show thesis by - (rule that(2), auto simp: path2_def)
    qed
  qed

  lemma path2_induct[consumes 1, case_names empty_path Cons_path]:
    assumes "g \<turnstile> n-ns\<rightarrow>m"
    assumes empty: "invar g \<Longrightarrow> P m [m] m"
    assumes Cons: "\<And>ns n' n. g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> P n ns m \<Longrightarrow> n' \<in> set (predecessors g n) \<Longrightarrow> P n' (n' # ns) m"
    shows "P n ns m"
  using assms(1)
  unfolding path2_def
  apply-
  proof (erule conjE, induction arbitrary: n rule:path.induct)
    case empty_path
    with empty show ?case by simp
  next
    case (Cons_path ns n' n'')
    hence[simp]: "n'' = n'" by simp
    from Cons_path Cons show ?case unfolding path2_def by auto
  qed

  lemma path_invar[intro]: "path g ns \<Longrightarrow> invar g"
  by (induction rule:path.induct)

  lemma path_in_\<alpha>n[intro]: "\<lbrakk>path g ns; n \<in> set ns\<rbrakk> \<Longrightarrow> n \<in> set (\<alpha>n g)"
  by (induct ns arbitrary: n rule:path.induct) auto

  lemma path2_in_\<alpha>n[elim]: "\<lbrakk>g \<turnstile> n-ns\<rightarrow>m; l \<in> set ns\<rbrakk> \<Longrightarrow> l \<in> set (\<alpha>n g)"
  unfolding path2_def by auto

  lemma path2_hd_in_\<alpha>n[elim]: "g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> n \<in> set (\<alpha>n g)"
  unfolding path2_def by auto

  lemma path2_tl_in_\<alpha>n[elim]: "g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> m \<in> set (\<alpha>n g)"
  unfolding path2_def by auto

  lemma path2_forget_hd[simp]: "g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> g \<turnstile> hd ns-ns\<rightarrow>m"
  unfolding path2_def by simp

  lemma path2_forget_last[simp]: "g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> g \<turnstile> n-ns\<rightarrow>last ns"
  unfolding path2_def by simp

  lemma path_hd[dest]: "path g (n#ns) \<Longrightarrow> path g [n]"
  by (rule empty_path, auto elim:path.cases)

  lemma path_by_tail[intro]: "\<lbrakk>path g (n#n'#ns); path g (n'#ns) \<Longrightarrow> path g (n'#ms)\<rbrakk> \<Longrightarrow> path g (n#n'#ms)"
  by (rule path.cases) auto

  lemma \<alpha>n_in_\<alpha>nE [elim]:
    assumes "(n,e,m) \<in> \<alpha>e g" and "invar g"
    obtains "n \<in> set (\<alpha>n g)" and "m \<in> set (\<alpha>n g)"
    using assms
    by (auto elim: edge_to_node)

  lemma path_split:
    assumes "path g (ns@m#ns')"
    shows "path g (ns@[m])" "path g(m#ns')"
  proof-
    from assms show "path g (ns@[m])"
    proof (induct ns)
      case (Cons n ns)
      thus ?case by (cases ns) auto
    qed auto
    from assms show "path g (m#ns')"
    proof (induct ns)
      case (Cons n ns)
      thus ?case by (auto elim:path.cases)
    qed auto
  qed

  lemma path2_split:
    assumes "g \<turnstile> n-ns@n'#ns'\<rightarrow>m"
    shows "g \<turnstile> n-ns@[n']\<rightarrow>n'" "g \<turnstile> n'-n'#ns'\<rightarrow>m"
  using assms unfolding path2_def by (auto intro:path_split iff:hd_append)

  lemma elem_set_implies_elem_tl_app_cons[simp]: "x \<in> set xs \<Longrightarrow> x \<in> set (tl (ys@y#xs))"
    by (induction ys arbitrary: y; auto)

  lemma path2_split_ex:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "x \<in> set ns"
    obtains ns\<^sub>1 ns\<^sub>2 where "g \<turnstile> n-ns\<^sub>1\<rightarrow>x" "g \<turnstile> x-ns\<^sub>2\<rightarrow>m" "ns = ns\<^sub>1@tl ns\<^sub>2" "ns = butlast ns\<^sub>1@ns\<^sub>2"
  proof-
    from assms(2) obtain ns\<^sub>1 ns\<^sub>2 where "ns = ns\<^sub>1@x#ns\<^sub>2" by atomize_elim (rule split_list)
    with assms[simplified this] show thesis
      by - (rule that, auto dest:path2_split(1) path2_split(2) intro: suffixI)
  qed

  lemma path2_split_ex':
    assumes "g \<turnstile> n-ns\<rightarrow>m" "x \<in> set ns"
    obtains ns\<^sub>1 ns\<^sub>2 where "g \<turnstile> n-ns\<^sub>1\<rightarrow>x" "g \<turnstile> x-ns\<^sub>2\<rightarrow>m" "ns = butlast ns\<^sub>1@ns\<^sub>2"
  using assms by (rule path2_split_ex)

  lemma path_snoc:
    assumes "path g (ns@[n])" "n \<in> set (predecessors g m)"
    shows "path g (ns@[n,m])"
  using assms(1) proof (induction ns)
    case Nil
    hence 1: "n \<in> set (\<alpha>n g)" "invar g" by auto
    with assms(2) have "m \<in> set (\<alpha>n g)" by auto
    with 1 have "path g [m]" by auto
    with assms(2) show ?case by auto
  next
    case (Cons l ns)
    hence 1: "path g (ns @ [n]) \<and> l \<in> set (predecessors g (hd (ns@[n])))" by -(cases g "(l # ns) @ [n]" rule:path.cases, auto)
    hence "path g (ns @ [n,m])" by (auto intro:Cons.IH)
    with 1 have "path g (l # ns @ [n,m])" by -(rule Cons_path, assumption, cases ns, auto)
    thus ?case by simp
  qed

  lemma path2_snoc[elim]:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "m \<in> set (predecessors g m')"
    shows "g \<turnstile> n-ns@[m']\<rightarrow>m'"
  proof-
    from assms(1) have 1: "ns \<noteq> []" by auto

    have "path g ((butlast ns) @ [last ns, m'])"
    using assms unfolding path2_def by -(rule path_snoc, auto)
    hence "path g ((butlast ns @ [last ns]) @ [m'])" by simp
    with 1 have "path g (ns @ [m'])" by simp
    thus ?thesis
    using assms unfolding path2_def by auto
  qed

  lemma path_unsnoc:
    assumes "path g ns" "length ns \<ge> 2"
    obtains "path g (butlast ns) \<and> last (butlast ns) \<in> set (predecessors g (last ns))"
  using assms
  proof (atomize_elim, induction ns)
    case (Cons_path ns n)
    show ?case
    proof (cases "2 \<le> length ns")
      case True
        hence [simp]: "hd (butlast ns) = hd ns" by (cases ns, auto)
        have 0: "n#butlast ns = butlast (n#ns)" using True by auto
        have 1: "n \<in> set (predecessors g (hd (butlast ns)))" using Cons_path by simp
        from True have "path g (butlast ns)" using Cons_path by auto
        hence "path g (n#butlast ns)" using 1 by auto
        hence "path g (butlast (n#ns))" using 0 by simp
      moreover
        from Cons_path True have "last (butlast ns) \<in> set (predecessors g (last ns))" by simp
        hence "last (butlast (n # ns)) \<in> set (predecessors g (last (n # ns)))"
          using True by (cases ns, auto)
      ultimately show ?thesis by auto
    next
      case False
      thus ?thesis
      proof (cases ns)
        case Nil
        thus ?thesis using Cons_path by -(rule ccontr, auto elim:path.cases)
      next
        case (Cons n' ns')
        hence [simp]: "ns = [n']" using False by (cases ns', auto)
        have "path g [n,n']" using Cons_path by auto
        thus ?thesis using Cons_path by auto
      qed
    qed
  qed auto

  lemma path2_unsnoc:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "length ns \<ge> 2"
    obtains "g \<turnstile> n-butlast ns\<rightarrow>last (butlast ns)" "last (butlast ns) \<in> set (predecessors g m)"
  using assms unfolding path2_def by (metis append_butlast_last_id hd_append2 path_not_Nil path_unsnoc)

  lemma path2_rev_induct[consumes 1, case_names empty snoc]:
    assumes "g \<turnstile> n-ns\<rightarrow>m"
    assumes empty: "n \<in> set (\<alpha>n g) \<Longrightarrow> P n [n] n"
    assumes snoc: "\<And>ns m' m. g \<turnstile> n-ns\<rightarrow>m' \<Longrightarrow> P n ns m' \<Longrightarrow> m' \<in> set (predecessors g m) \<Longrightarrow> P n (ns@[m]) m"
    shows "P n ns m"
  using assms(1) proof (induction arbitrary:m rule:length_induct)
    case (1 ns)
    show ?case
    proof (cases "length ns \<ge> 2")
      case False
      thus ?thesis
      proof (cases ns)
        case Nil
        thus ?thesis using 1(2) by auto
      next
        case (Cons n' ns')
        with False have "ns' = []" by (cases ns', auto)
        with Cons 1(2) have "n' = n" "m = n" unfolding path2_def by auto
        with Cons \<open>ns' = []\<close> 1(2) show ?thesis by (auto intro:empty)
      qed
    next
      case True
      let ?ns' = "butlast ns"
      let ?m' = "last ?ns'"
      from 1(2) have m: "m = last ns" unfolding path2_def by auto
      from True 1(2) obtain ns': "g \<turnstile> n-?ns'\<rightarrow>?m'" "?m' \<in> set (predecessors g m)" by -(rule path2_unsnoc)
      with True "1.IH" have "P n ?ns' ?m'" by auto
      with ns' have "P n (?ns'@[m]) m" by (auto intro!: snoc)
      with m 1(2) show ?thesis by auto
    qed
  qed

  lemma path2_hd[elim, dest?]: "g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> n = hd ns"
  unfolding path2_def by simp

  lemma path2_hd_in_ns[elim]: "g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> n \<in> set ns"
  unfolding path2_def by auto

  lemma path2_last[elim, dest?]: "g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> m = last ns"
  unfolding path2_def by simp

  lemma path2_last_in_ns[elim]: "g \<turnstile> n-ns\<rightarrow>m \<Longrightarrow> m \<in> set ns"
  unfolding path2_def by auto

  lemma path_app[elim]:
    assumes "path g ns" "path g ms" "last ns = hd ms"
    shows "path g (ns@tl ms)"
  using assms by (induction ns rule:path.induct) auto

  lemma path2_app[elim]:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "g \<turnstile> m-ms\<rightarrow>l"
    shows "g \<turnstile> n-ns@tl ms\<rightarrow>l"
  proof-
    have "last (ns @ tl ms) = last ms" using assms
    unfolding path2_def
    proof (cases "tl ms")
      case Nil
      hence "ms = [m]" using assms(2) unfolding path2_def by (cases ms, auto)
      thus ?thesis using assms(1) unfolding path2_def by auto
    next
      case (Cons m' ms')
      from this[symmetric] have "ms = hd ms#m'#ms'" using assms(2) by auto
      thus ?thesis using assms unfolding path2_def by auto
    qed
    with assms show ?thesis
      unfolding path2_def by auto
  qed

  lemma butlast_tl:
    assumes "last xs = hd ys" "xs \<noteq> []" "ys \<noteq> []"
    shows "butlast xs@ys = xs@tl ys"
    by (metis append.simps(1) append.simps(2) append_assoc append_butlast_last_id assms(1) assms(2) assms(3) list.collapse)

  lemma path2_app'[elim]:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "g \<turnstile> m-ms\<rightarrow>l"
    shows "g \<turnstile> n-butlast ns@ms\<rightarrow>l"
  proof-
    have "butlast ns@ms = ns@tl ms" using assms by - (rule butlast_tl, auto dest:path2_hd path2_last)
    moreover from assms have "g \<turnstile> n-ns@tl ms\<rightarrow>l" by (rule path2_app)
    ultimately show ?thesis by simp
  qed

  lemma path2_nontrivial[elim]:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "n \<noteq> m"
    shows "length ns \<ge> 2"
  using assms
    by (metis Suc_1 le_antisym length_1_last_hd not_less_eq_eq path2_hd path2_last path2_not_Nil3)

  lemma simple_path2_aux:
    assumes "g \<turnstile> n-ns\<rightarrow>m"
    obtains ns' where "g \<turnstile> n-ns'\<rightarrow>m" "distinct ns'" "set ns' \<subseteq> set ns" "length ns' \<le> length ns"
  apply atomize_elim
  using assms proof (induction rule:path2_induct)
    case empty_path
    with assms show ?case by - (rule exI[of _ "[m]"], auto)
  next
    case (Cons_path ns n n')
    then obtain ns' where ns': "g \<turnstile> n'-ns'\<rightarrow>m" "distinct ns'" "set ns' \<subseteq> set ns" "length ns' \<le> length ns" by auto
    show ?case
    proof (cases "n \<in> set ns'")
      case False
      with ns' Cons_path(2) show ?thesis by -(rule exI[where x="n#ns'"], auto)
    next
      case True
      with ns' obtain ns'\<^sub>1 ns'\<^sub>2 where split: "ns' = ns'\<^sub>1@n#ns'\<^sub>2" "n \<notin> set ns'\<^sub>2" by -(atomize_elim, rule split_list_last)
      with ns' have "g \<turnstile> n-n#ns'\<^sub>2\<rightarrow>m" by -(rule path2_split, simp)
      with split ns' show ?thesis by -(rule exI[where x="n#ns'\<^sub>2"], auto)
    qed
  qed

  lemma simple_path2:
    assumes "g \<turnstile> n-ns\<rightarrow>m"
    obtains ns' where "g \<turnstile> n-ns'\<rightarrow>m" "distinct ns'" "set ns' \<subseteq> set ns" "length ns' \<le>  length ns" "n \<notin> set (tl ns')" "m \<notin> set (butlast ns')"
  using assms
  apply (rule simple_path2_aux)
  by (metis append_butlast_last_id distinct.simps(2) distinct1_rotate hd_Cons_tl path2_hd path2_last path2_not_Nil rotate1.simps(2))

  lemma simple_path2_unsnoc:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "n \<noteq> m"
    obtains ns' where "g \<turnstile> n-ns'\<rightarrow>last ns'" "last ns' \<in> set (predecessors g m)" "distinct ns'" "set ns' \<subseteq> set ns" "m \<notin> set ns'"
  proof-
    obtain ns' where 1: "g \<turnstile> n-ns'\<rightarrow>m" "distinct ns'" "set ns' \<subseteq> set ns" "m \<notin> set (butlast ns')" by (rule simple_path2[OF assms(1)])
    with assms(2) obtain 2: "g \<turnstile> n-butlast ns'\<rightarrow>last (butlast ns')" "last (butlast ns') \<in> set (predecessors g m)" by - (rule path2_unsnoc, auto)
    show thesis
    proof (rule that[of "butlast ns'"])
      from 1(3) show "set (butlast ns') \<subseteq> set ns" by (metis in_set_butlastD subsetI subset_trans)
    qed (auto simp:1 2 distinct_butlast)
  qed

  lemma path2_split_first_last:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "x \<in> set ns"
    obtains ns\<^sub>1 ns\<^sub>3 ns\<^sub>2 where "ns = ns\<^sub>1@ns\<^sub>3@ns\<^sub>2" "prefix (ns\<^sub>1@[x]) ns" "suffix (x#ns\<^sub>2) ns"
        and "g \<turnstile> n-ns\<^sub>1@[x]\<rightarrow>x"  "x \<notin> set ns\<^sub>1"
        and "g \<turnstile> x-ns\<^sub>3\<rightarrow>x"
        and "g \<turnstile> x-x#ns\<^sub>2\<rightarrow>m" "x \<notin> set ns\<^sub>2"
  proof-
    from assms(2) obtain ns\<^sub>1 ns' where 1: "ns = ns\<^sub>1@x#ns'" "x \<notin> set ns\<^sub>1" by (atomize_elim, rule split_list_first)
    from assms(1)[unfolded 1(1)] have 2: "g \<turnstile> n-ns\<^sub>1@[x]\<rightarrow>x" "g \<turnstile> x-x#ns'\<rightarrow>m" by - (erule path2_split, erule path2_split)
    obtain ns\<^sub>3 ns\<^sub>2 where 3: "x#ns' = ns\<^sub>3@x#ns\<^sub>2" "x \<notin> set ns\<^sub>2" by (atomize_elim, rule split_list_last, simp)
    from 2(2)[unfolded 3(1)] have 4: "g \<turnstile> x-ns\<^sub>3@[x]\<rightarrow>x" "g \<turnstile> x-x#ns\<^sub>2\<rightarrow>m" by - (erule path2_split, erule path2_split)
    show thesis
    proof (rule that[OF _ _ _ 2(1) 1(2) 4 3(2)])
      show "ns = ns\<^sub>1 @ (ns\<^sub>3 @ [x]) @ ns\<^sub>2" using 1(1) 3(1) by simp
      show "prefix (ns\<^sub>1@[x]) ns" using 1 by auto
      show "suffix (x#ns\<^sub>2) ns" using 1 3 by (metis Sublist.suffix_def suffix_order.order_trans)
    qed
  qed

  lemma path2_simple_loop:
    assumes "g \<turnstile> n-ns\<rightarrow>n" "n' \<in> set ns"
    obtains ns' where "g \<turnstile> n-ns'\<rightarrow>n" "n' \<in> set ns'" "n \<notin> set (tl (butlast ns'))" "set ns' \<subseteq> set ns"
  using assms proof (induction "length ns" arbitrary: ns rule: nat_less_induct)
    case 1
    let ?ns' = "tl (butlast ns)"
    show ?case
    proof (cases "n \<in> set ?ns'")
      case False
      with "1.prems"(2,3) show ?thesis by - (rule "1.prems"(1), auto)
    next
      case True
      hence 2: "length ns > 1" by (cases ns, auto)
      with "1.prems"(2) obtain m where m: "g \<turnstile> n-butlast ns\<rightarrow>m" "m \<in> set (predecessors g n)" by - (rule path2_unsnoc, auto)
      with True obtain m' where m': "g \<turnstile> m'-?ns'\<rightarrow>m" "n \<in> set (predecessors g m')" by - (erule path2_cases, auto)
      with True obtain ns\<^sub>1 ns\<^sub>2 where split: "g \<turnstile> m'-ns\<^sub>1\<rightarrow>n" "g \<turnstile> n-ns\<^sub>2\<rightarrow>m" "?ns' = ns\<^sub>1@tl ns\<^sub>2" "?ns' = butlast ns\<^sub>1@ns\<^sub>2"
        by - (rule path2_split_ex)
      have "ns = butlast ns@[n]" using 2 "1.prems"(2) by (auto simp: path2_def)
      moreover have "butlast ns = n#tl (butlast ns)" using 2 m(1) by (auto simp: path2_def)
      ultimately have split': "ns = n#ns\<^sub>1@tl ns\<^sub>2@[n]" "ns = n#butlast ns\<^sub>1@ns\<^sub>2@[n]" using split(3,4) by auto
      show ?thesis
      proof (cases "n' \<in> set (n#ns\<^sub>1)")
        case True
        show ?thesis
        proof (rule "1.hyps"[rule_format, of _ "n#ns\<^sub>1"])
          show "length (n#ns\<^sub>1) < length ns" using split'(1) by auto
          show "n' \<in> set (n#ns\<^sub>1)" by (rule True)
        qed (auto intro: split(1) m'(2) intro!: "1.prems"(1) simp: split'(1))
      next
        case False
        from False split'(1) "1.prems"(3) have 5: "n' \<in> set (ns\<^sub>2@[n])" by auto
        show ?thesis
        proof (rule "1.hyps"[rule_format, of _ "ns\<^sub>2@[n]"])
          show "length (ns\<^sub>2@[n]) < length ns" using split'(2) by auto
          show "n' \<in> set (ns\<^sub>2@[n])" by (rule 5)
          show "g \<turnstile> n-ns\<^sub>2@[n]\<rightarrow>n" using split(2) m(2) by (rule path2_snoc)
        qed (auto intro!: "1.prems"(1) simp: split'(2))
      qed
    qed
  qed

  lemma path2_split_first_prop:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "\<exists>x\<in>set ns. P x"
    obtains m' ns' where "g \<turnstile> n-ns'\<rightarrow>m'" "P m'" "\<forall>x \<in> set (butlast ns'). \<not>P x" "prefix ns' ns"
  proof-
    obtain ns'' n' ns' where 1: "ns = ns''@n'#ns'" "P n'" "\<forall>x \<in> set ns''. \<not>P x" by - (rule split_list_first_propE[OF assms(2)])
    with assms(1) have "g \<turnstile> n-ns''@[n']\<rightarrow>n'" by - (rule path2_split(1), auto)
    with 1 show thesis by - (rule that, auto)
  qed

  lemma path2_split_last_prop:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "\<exists>x\<in>set ns. P x"
    obtains n' ns' where "g \<turnstile> n'-ns'\<rightarrow>m" "P n'" "\<forall>x \<in> set (tl ns'). \<not>P x" "suffix ns' ns"
  proof-
    obtain ns'' n' ns' where 1: "ns = ns''@n'#ns'" "P n'" "\<forall>x \<in> set ns'. \<not>P x" by - (rule split_list_last_propE[OF assms(2)])
    with assms(1) have "g \<turnstile> n'-n'#ns'\<rightarrow>m" by - (rule path2_split(2), auto)
    with 1 show thesis by - (rule that, auto simp: Sublist.suffix_def)
  qed

  lemma path2_prefix[elim]:
    assumes 1: "g \<turnstile> n-ns\<rightarrow>m"
    assumes 2: "prefix (ns'@[m']) ns"
    shows "g \<turnstile> n-ns'@[m']\<rightarrow>m'"
  using assms by -(erule prefixE, rule path2_split, simp)

  lemma path2_prefix_ex:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "m' \<in> set ns"
    obtains ns' where "g \<turnstile> n-ns'\<rightarrow>m'" "prefix ns' ns" "m' \<notin> set (butlast ns')"
  proof-
    from assms(2) obtain ns' where "prefix (ns'@[m']) ns" "m' \<notin> set ns'" by (rule prefix_split_first)
    with assms(1) show thesis by - (rule that, auto)
  qed

  lemma path2_strict_prefix_ex:
    assumes "g \<turnstile> n-ns\<rightarrow>m" "m' \<in> set (butlast ns)"
    obtains ns' where "g \<turnstile> n-ns'\<rightarrow>m'" "strict_prefix ns' ns" "m' \<notin> set (butlast ns')"
  proof-
    from assms(2) obtain ns' where ns': "prefix (ns'@[m']) (butlast ns)" "m' \<notin> set ns'" by (rule prefix_split_first)
    hence "strict_prefix (ns'@[m']) ns" using assms by - (rule strict_prefix_butlast, auto)
    with assms(1) ns'(2) show thesis by - (rule that, auto)
  qed

  lemma path2_nontriv[elim]: "\<lbrakk>g \<turnstile> n-ns\<rightarrow>m; n \<noteq> m\<rbrakk> \<Longrightarrow> length ns > 1"
    by (metis hd_Cons_tl last_appendR last_snoc length_greater_0_conv length_tl path2_def path_not_Nil zero_less_diff)

  declare path_not_Nil [simp del]
  declare path2_not_Nil [simp del]
  declare path2_not_Nil3 [simp del]
end

subsection \<open>Domination\<close>

text \<open>We fix an entry node per graph and use it to define node domination.\<close>

locale graph_Entry_base = graph_path_base \<alpha>e \<alpha>n invar inEdges'
for
  \<alpha>e :: "'g \<Rightarrow> ('node \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list"
+
fixes Entry :: "'g \<Rightarrow> 'node"
begin
  definition dominates :: "'g \<Rightarrow> 'node \<Rightarrow> 'node \<Rightarrow> bool" where
    "dominates g n m \<equiv> m \<in> set (\<alpha>n g) \<and> (\<forall>ns. g \<turnstile> Entry g-ns\<rightarrow>m \<longrightarrow> n \<in> set ns)"

  abbreviation "strict_dom g n m \<equiv> n \<noteq> m \<and> dominates g n m"
end

locale graph_Entry = graph_Entry_base \<alpha>e \<alpha>n invar inEdges' Entry
  + graph_path \<alpha>e \<alpha>n invar inEdges'
for
  \<alpha>e :: "'g \<Rightarrow> ('node \<times> 'edgeD \<times> 'node) set" and
  \<alpha>n :: "'g \<Rightarrow> 'node list" and
  invar :: "'g \<Rightarrow> bool" and
  inEdges' :: "'g \<Rightarrow> 'node \<Rightarrow> ('node \<times> 'edgeD) list" and
  Entry :: "'g \<Rightarrow> 'node"
+
assumes Entry_in_graph[simp]: "Entry g \<in> set (\<alpha>n g)"
assumes Entry_unreachable: "invar g \<Longrightarrow> inEdges g (Entry g) = []"
assumes Entry_reaches[intro]:
  "\<lbrakk>n \<in> set (\<alpha>n g); invar g\<rbrakk> \<Longrightarrow> \<exists>ns. g \<turnstile> Entry g-ns\<rightarrow>n"
begin
  lemma Entry_dominates[simp,intro]: "\<lbrakk>invar g; n \<in> set (\<alpha>n g)\<rbrakk> \<Longrightarrow> dominates g (Entry g) n"
  unfolding dominates_def by auto

  lemma Entry_iff_unreachable[simp]:
    assumes "invar g" "n \<in> set (\<alpha>n g)"
    shows "predecessors g n = [] \<longleftrightarrow> n = Entry g"
  proof (rule, rule ccontr)
    assume "predecessors g n = []" "n \<noteq> Entry g"
    with Entry_reaches[OF assms(2,1)] show False by (auto elim:simple_path2_unsnoc)
  qed (auto simp:assms Entry_unreachable predecessors_def)

  lemma Entry_loop:
    assumes "invar g" "g \<turnstile> Entry g-ns\<rightarrow>Entry g"
    shows "ns=[Entry g]"
  proof (cases "length ns \<ge> 2")
    case True
    with assms have "last (butlast ns) \<in> set (predecessors g (Entry g))" by - (rule path2_unsnoc)
    with Entry_unreachable[OF assms(1)] have False by (simp add:predecessors_def)
    thus ?thesis ..
  next
    case False
    with assms show ?thesis
      by (metis Suc_leI hd_Cons_tl impossible_Cons le_less length_greater_0_conv numeral_2_eq_2 path2_hd path2_not_Nil)
  qed

  lemma simple_Entry_path:
    assumes "invar g" "n \<in> set (\<alpha>n g)"
    obtains ns where "g \<turnstile> Entry g-ns\<rightarrow>n" and "n \<notin> set (butlast ns)"
  proof-
    from assms obtain ns where p: "g \<turnstile> Entry g-ns\<rightarrow>n" by -(atomize_elim, rule Entry_reaches)
    with p obtain ns' where "g \<turnstile> Entry g-ns'\<rightarrow>n" "n \<notin> set (butlast ns')" by -(rule path2_split_first_last, auto)
    thus ?thesis by (rule that)
  qed

  lemma dominatesI [intro]:
    "\<lbrakk>m \<in> set (\<alpha>n g); \<And>ns. \<lbrakk>g \<turnstile> Entry g-ns\<rightarrow>m\<rbrakk> \<Longrightarrow> n \<in> set ns\<rbrakk> \<Longrightarrow> dominates g n m"
  unfolding dominates_def by simp

  lemma dominatesE:
    assumes "dominates g n m"
    obtains "m \<in> set (\<alpha>n g)" and "\<And>ns. g \<turnstile> Entry g-ns\<rightarrow>m \<Longrightarrow> n \<in> set ns"
    using assms unfolding dominates_def by auto

  lemma[simp]: "dominates g n m \<Longrightarrow> m \<in> set (\<alpha>n g)" by (rule dominatesE)

  lemma[simp]:
    assumes "dominates g n m" and[simp]: "invar g"
    shows "n \<in> set (\<alpha>n g)"
  proof-
    from assms obtain ns where "g \<turnstile> Entry g-ns\<rightarrow>m" by atomize_elim (rule Entry_reaches, auto)
    with assms show ?thesis by (auto elim!:dominatesE)
  qed

  lemma strict_domE[elim]:
    assumes "strict_dom g n m"
    obtains "m \<in> set (\<alpha>n g)" and "\<And>ns. g \<turnstile> Entry g-ns\<rightarrow>m \<Longrightarrow> n \<in> set (butlast ns)"
  using assms by (metis dominates_def path2_def path_not_Nil rotate1.simps(2) set_ConsD set_rotate1 snoc_eq_iff_butlast)

  lemma dominates_refl[intro!]: "\<lbrakk>invar g; n \<in> set (\<alpha>n g)\<rbrakk> \<Longrightarrow> dominates g n n"
  by auto

  lemma dominates_trans:
    assumes "invar g"
    assumes part1: "dominates g n n'"
    assumes part2: "dominates g n' n''"
    shows   "dominates g n n''"
  proof
    from part2 show "n'' \<in> set (\<alpha>n g)" by auto

    fix ns :: "'node list"
    assume p: "g \<turnstile> Entry g-ns\<rightarrow>n''"
    with part2 have "n' \<in> set ns" by - (erule dominatesE, auto)
    then obtain as where prefix: "prefix (as@[n']) ns" by (auto intro:prefix_split_first)
    with p have "g \<turnstile> Entry g-(as@[n'])\<rightarrow>n'" by auto
    with part1 have "n \<in> set (as@[n'])" unfolding dominates_def by auto
    with prefix show "n \<in> set ns" by auto
  qed

  lemma dominates_antisymm:
    assumes "invar g"
    assumes dom1: "dominates g n n'"
    assumes dom2: "dominates g n' n"
    shows "n = n'"
  proof (rule ccontr)
    assume "n \<noteq> n'"
    from dom2 have "n \<in> set (\<alpha>n g)" by auto
    with \<open>invar g\<close> obtain ns where p: "g \<turnstile> Entry g-ns\<rightarrow>n" and "n \<notin> set (butlast ns)"
      by (rule simple_Entry_path)
    with dom2 have "n' \<in> set ns" by - (erule dominatesE, auto)
    then obtain as where prefix: "prefix (as@[n']) ns" by (auto intro:prefix_split_first)
    with p have "g \<turnstile> Entry g-as@[n']\<rightarrow>n'" by (rule path2_prefix)
    with dom1 have "n \<in> set (as@[n'])" unfolding dominates_def by auto
    with \<open>n \<noteq> n'\<close> have "n \<in> set as" by auto
    with \<open>prefix (as@[n']) ns\<close> have "n \<in> set (butlast ns)" by -(erule prefixE, auto iff:butlast_append)
    with \<open>n \<notin> set (butlast ns)\<close> show False..
  qed

  lemma dominates_unsnoc:
    assumes [simp]: "invar g" and "dominates g n m" "m' \<in> set (predecessors g m)" "n \<noteq> m"
    shows "dominates g n m'"
  proof
    show "m' \<in> set (\<alpha>n g)" using assms by auto
  next
    fix ns
    assume "g \<turnstile> Entry g-ns\<rightarrow>m'"
    with assms(3) have "g \<turnstile> Entry g-ns@[m]\<rightarrow>m" by auto
    with assms(2,4) show "n \<in> set ns" by (auto elim!:dominatesE)
  qed

  lemma dominates_unsnoc':
    assumes [simp]: "invar g" and "dominates g n m" "g \<turnstile> m'-ms\<rightarrow>m" "\<forall>x \<in> set (tl ms). x \<noteq> n"
    shows "dominates g n m'"
  using assms(3,4) proof (induction rule:path2_induct)
    case empty_path
    show ?case by (rule assms(2))
  next
    case (Cons_path ms m'' m')
    from Cons_path(4) have "dominates g n m'"
      by (simp add: Cons_path.IH in_set_tlD)
    moreover from Cons_path(1) have "m' \<in> set ms" by auto
    hence "m' \<noteq> n" using Cons_path(4) by simp
    ultimately show ?case using Cons_path(2) by - (rule dominates_unsnoc, auto)
  qed

  lemma dominates_path:
    assumes "dominates g n m" and[simp]: "invar g"
    obtains ns where "g \<turnstile> n-ns\<rightarrow>m"
  proof atomize_elim
    from assms obtain ns where ns: "g \<turnstile> Entry g-ns\<rightarrow>m" by atomize_elim (rule Entry_reaches, auto)
    with assms have "n \<in> set ns" by - (erule dominatesE)
    with ns show "\<exists>ns. g \<turnstile> n-ns\<rightarrow>m" by - (rule path2_split_ex, auto)
  qed

  lemma dominates_antitrans:
    assumes[simp]: "invar g" and "dominates g n\<^sub>1 m" "dominates g n\<^sub>2 m"
    obtains (1) "dominates g n\<^sub>1 n\<^sub>2"
          | (2) "dominates g n\<^sub>2 n\<^sub>1"
  proof (cases "dominates g n\<^sub>1 n\<^sub>2")
    case False
    show thesis
    proof (rule 2, rule dominatesI)
      show "n\<^sub>1 \<in> set (\<alpha>n g)" using assms(2) by simp
    next
      fix ns
      assume asm: "g \<turnstile> Entry g-ns\<rightarrow>n\<^sub>1"
      from assms(2) obtain ns\<^sub>2 where "g \<turnstile> n\<^sub>1-ns\<^sub>2\<rightarrow>m" by (rule dominates_path, simp)
      then obtain ns\<^sub>2' where ns\<^sub>2': "g \<turnstile> n\<^sub>1-ns\<^sub>2'\<rightarrow>m" "n\<^sub>1 \<notin> set (tl ns\<^sub>2')" "set ns\<^sub>2' \<subseteq> set ns\<^sub>2" by (rule simple_path2)
      with asm have "g \<turnstile> Entry g-ns@tl ns\<^sub>2'\<rightarrow>m" by auto
      with assms(3) have "n\<^sub>2 \<in> set (ns@tl ns\<^sub>2')" by - (erule dominatesE)
      moreover have "n\<^sub>2 \<notin> set (tl ns\<^sub>2')"
      proof
        assume "n\<^sub>2 \<in> set (tl ns\<^sub>2')"
        with ns\<^sub>2'(1,2) obtain ns\<^sub>3 where ns\<^sub>3: "g \<turnstile> n\<^sub>2-ns\<^sub>3\<rightarrow>m" "n\<^sub>1 \<notin> set (tl ns\<^sub>3)"
          by - (erule path2_split_ex, auto simp: path2_not_Nil)
        have "dominates g n\<^sub>1 n\<^sub>2"
        proof
          show "n\<^sub>2 \<in> set (\<alpha>n g)" using assms(3) by simp
        next
          fix ns'
          assume ns': "g \<turnstile> Entry g-ns'\<rightarrow>n\<^sub>2"
          with ns\<^sub>3(1) have "g \<turnstile> Entry g-ns'@tl ns\<^sub>3\<rightarrow>m" by auto
          with assms(2) have "n\<^sub>1 \<in> set (ns'@tl ns\<^sub>3)" by - (erule dominatesE)
          with ns\<^sub>3(2) show "n\<^sub>1 \<in> set ns'" by simp
        qed
        with False show False ..
      qed
      ultimately show "n\<^sub>2 \<in> set ns" by simp
    qed
  qed

  lemma dominates_extend:
    assumes "dominates g n m"
    assumes "g \<turnstile> m'-ms\<rightarrow>m" "n \<notin> set (tl ms)"
    shows "dominates g n m'"
  proof (rule dominatesI)
    show "m' \<in> set (\<alpha>n g)" using assms(2) by auto
  next
    fix ms'
    assume "g \<turnstile> Entry g-ms'\<rightarrow>m'"
    with assms(2) have "g \<turnstile> Entry g-ms'@tl ms\<rightarrow>m" by auto
    with assms(1) have "n \<in> set (ms'@tl ms)" by - (erule dominatesE)
    with assms(3) show "n \<in> set ms'" by auto
  qed

  definition dominators :: "'g \<Rightarrow> 'node \<Rightarrow> 'node set" where
    "dominators g n \<equiv> {m \<in> set (\<alpha>n g). dominates g m n}"

  definition "isIdom g n m \<longleftrightarrow> strict_dom g m n \<and> (\<forall>m' \<in> set (\<alpha>n g). strict_dom g m' n \<longrightarrow> dominates g m' m)"
  definition idom :: "'g \<Rightarrow> 'node \<Rightarrow> 'node" where
    "idom g n \<equiv> THE m. isIdom g n m"

  lemma idom_ex:
    assumes[simp]: "invar g" "n \<in> set (\<alpha>n g)" "n \<noteq> Entry g"
    shows "\<exists>!m. isIdom g n m"
  proof (rule ex_ex1I)
    let ?A = "\<lambda>m. {m' \<in> set (\<alpha>n g). strict_dom g m' n \<and> strict_dom g m m'}"

    have 1: "\<And>A m. finite A \<Longrightarrow> A = ?A m \<Longrightarrow> strict_dom g m n \<Longrightarrow> \<exists>m'. isIdom g n m'"
    proof-
      fix A m
      show "finite A \<Longrightarrow> A = ?A m \<Longrightarrow> strict_dom g m n \<Longrightarrow> \<exists>m'. isIdom g n m'"
      proof (induction arbitrary:m rule:finite_psubset_induct)
        case (psubset A m)
        show ?case
        proof (cases "A = {}")
          case True
          { fix m'
            assume asm: "strict_dom g m' n" and [simp]: "m' \<in> set (\<alpha>n g)"
            with True psubset.prems(1) have "\<not>(strict_dom g m m')" by auto
            hence "dominates g m' m" using dominates_antitrans[of g m' n m] asm psubset.prems(2) by fastforce
          }
          thus ?thesis using psubset.prems(2) by - (rule exI[of _ m], auto simp:isIdom_def)
        next
          case False
          then obtain m' where "m' \<in> A" by auto
          with psubset.prems(1) have m': "m' \<in> set (\<alpha>n g)" "strict_dom g m' n" "strict_dom g m m'" by auto
          have "?A m' \<subset> ?A m"
          proof
            show "?A m' \<noteq> ?A m" using m' by auto
            show "?A m' \<subseteq> ?A m" using m' dominates_antisymm[of g m m'] dominates_trans[of g m] by auto
          qed
          thus ?thesis by (rule psubset.IH[of _ m', simplified psubset.prems(1)], simp_all add: m')
        qed
      qed
    qed
    show "\<exists>m. isIdom g n m" by (rule 1[of "?A (Entry g)"], auto)
  next
    fix m m'
    assume "isIdom g n m" "isIdom g n m'"
    thus "m = m'" by - (rule dominates_antisymm[of g], auto simp:isIdom_def)
  qed

  lemma idom: "\<lbrakk>invar g; n \<in> set (\<alpha>n g) - {Entry g}\<rbrakk> \<Longrightarrow> isIdom g n (idom g n)"
  unfolding idom_def by (rule theI', rule idom_ex, auto)

  lemma dominates_mid:
    assumes "dominates g n x" "dominates g x m" "g \<turnstile> n-ns\<rightarrow>m" and[simp]: "invar g"
    shows "x \<in> set ns"
  using assms
  proof (cases "n = x")
    case False
    from assms(1) obtain ns\<^sub>0 where ns\<^sub>0: "g \<turnstile> Entry g-ns\<^sub>0\<rightarrow>n" "n \<notin> set (butlast ns\<^sub>0)" by - (rule simple_Entry_path, auto)
    with assms(3) have "g \<turnstile> Entry g-butlast ns\<^sub>0@ns\<rightarrow>m" by auto
    with assms(2) have "x \<in> set (butlast ns\<^sub>0@ns)" by (auto elim!:dominatesE)
    moreover have "x \<notin> set (butlast ns\<^sub>0)"
    proof
      assume asm: "x \<in> set (butlast ns\<^sub>0)"
      with ns\<^sub>0 obtain ns\<^sub>0' where ns\<^sub>0': "g \<turnstile> Entry g-ns\<^sub>0'\<rightarrow>x" "n \<notin> set (butlast ns\<^sub>0')"
        by - (erule path2_split_ex, auto dest:in_set_butlastD simp: butlast_append split: if_split_asm)
      show False by (metis False assms(1) ns\<^sub>0' strict_domE)
    qed
    ultimately show ?thesis by simp
  qed auto

  definition shortestPath :: "'g \<Rightarrow> 'node \<Rightarrow> nat" where
    "shortestPath g n \<equiv> (LEAST l. \<exists>ns. length ns = l \<and> g \<turnstile> Entry g-ns\<rightarrow>n)"

  lemma shortestPath_ex:
    assumes "n \<in> set (\<alpha>n g)" "invar g"
    obtains ns where "g \<turnstile> Entry g-ns\<rightarrow>n" "distinct ns" "length ns = shortestPath g n"
  proof-
    from assms obtain ns where "g \<turnstile> Entry g-ns\<rightarrow>n" by - (atomize_elim, rule Entry_reaches)
    then obtain sns where sns: "length sns = shortestPath g n" "g \<turnstile> Entry g-sns\<rightarrow>n"
      unfolding shortestPath_def
      by -(atomize_elim, rule LeastI, auto)
    then obtain sns' where sns': "length sns' \<le> shortestPath g n" "g \<turnstile> Entry g-sns'\<rightarrow>n" "distinct sns'" by - (rule simple_path2, auto)
    moreover from sns'(2) have "shortestPath g n \<le> length sns'" unfolding shortestPath_def by - (rule Least_le, auto)
    ultimately show thesis by -(rule that, auto)
  qed

  lemma[simp]: "\<lbrakk>n \<in> set (\<alpha>n g); invar g\<rbrakk> \<Longrightarrow> shortestPath g n \<noteq> 0"
    by (metis length_0_conv path2_not_Nil2 shortestPath_ex)

  lemma shortestPath_upper_bound:
    assumes "n \<in> set (\<alpha>n g)" "invar g"
    shows "shortestPath g n \<le> length (\<alpha>n g)"
  proof-
    from assms obtain ns where ns: "g \<turnstile> Entry g-ns\<rightarrow>n" "length ns = shortestPath g n" "distinct ns" by (rule shortestPath_ex)
    hence "shortestPath g n = length ns" by simp
    also have "... = card (set ns)" using ns(3) by (rule distinct_card[symmetric])
    also have "... \<le> card (set (\<alpha>n g))" using ns(1) by - (rule card_mono, auto)
    also have "... \<le> length (\<alpha>n g)" by (rule card_length)
    finally show ?thesis .
  qed

  lemma shortestPath_predecessor:
    assumes "n \<in> set (\<alpha>n g) - {Entry g}" and[simp]: "invar g"
    obtains n' where "Suc (shortestPath g n') = shortestPath g n" "n' \<in> set (predecessors g n)"
  proof -
    from assms obtain sns where sns: "length sns = shortestPath g n" "g \<turnstile> Entry g-sns\<rightarrow>n"
      by - (rule shortestPath_ex, auto)
    let ?n' = "last (butlast sns)"
    from assms(1) sns(2) have 1: "length sns \<ge> 2" by auto
    hence prefix: "g \<turnstile> Entry g-butlast sns\<rightarrow>last (butlast sns) \<and> last (butlast sns) \<in> set (predecessors g n)"
      using sns by -(rule path2_unsnoc, auto)
    hence "shortestPath g ?n' \<le> length (butlast sns)"
      unfolding shortestPath_def by -(rule Least_le, rule exI[where x = "butlast sns"], simp)
    with 1 sns(1) have 2: "shortestPath g ?n' < shortestPath g n" by auto
    { assume asm: "Suc (shortestPath g ?n') \<noteq> shortestPath g n"
      obtain sns' where sns': "g \<turnstile> Entry g-sns'\<rightarrow>?n'" "length sns' = shortestPath g ?n'"
        using prefix by - (rule shortestPath_ex, auto)
      hence[simp]: "g \<turnstile> Entry g-sns'@[n]\<rightarrow>n" using prefix by auto
      from asm 2 have "Suc (shortestPath g ?n') < shortestPath g n" by auto
      from this[unfolded shortestPath_def, THEN not_less_Least, folded shortestPath_def, simplified, THEN spec[of _ "sns'@[n]"]]
      have False using sns'(2) by auto
    }
    with prefix show thesis by - (rule that, auto)
  qed

  lemma successor_in_\<alpha>n[simp]:
    assumes "predecessors g n \<noteq> []" and[simp]: "invar g"
    shows "n \<in> set (\<alpha>n g)"
  proof-
    from assms(1) obtain m where "m \<in> set (predecessors g n)" by (cases "predecessors g n", auto)
    with assms(1) obtain m' e where "(m',e,n) \<in> \<alpha>e g" using inEdges_correct[of g n, THEN arg_cong[where f="(`) getTo"]]
      by (auto simp: predecessors_def simp del: inEdges_correct)
    with assms(1) show ?thesis
      by (auto simp: predecessors_def)
  qed

  lemma shortestPath_single_predecessor:
    assumes "predecessors g n = [m]" and[simp]: "invar g"
    shows "shortestPath g m < shortestPath g n"
  proof-
    from assms(1) have "n \<in> set (\<alpha>n g) - {Entry g}"
      by (auto simp: predecessors_def Entry_unreachable)
    thus ?thesis by (rule shortestPath_predecessor, auto simp: assms(1))
  qed

  lemma strict_dom_shortestPath_order:
    assumes "strict_dom g n m" "m \<in> set (\<alpha>n g)" "invar g"
    shows "shortestPath g n < shortestPath g m"
  proof-
    from assms(2,3) obtain sns where sns: "g \<turnstile> Entry g-sns\<rightarrow>m" "length sns = shortestPath g m"
      by (rule shortestPath_ex)
    with assms(1) sns(1) obtain sns' where sns': "g \<turnstile> Entry g-sns'\<rightarrow>n" "prefix sns' sns" by -(erule path2_prefix_ex, auto elim:dominatesE)
    hence "shortestPath g n \<le> length sns'"
      unfolding shortestPath_def by -(rule Least_le, auto)
    also have "length sns' < length sns"
    proof-
      from assms(1) sns(1) sns'(1) have "sns' \<noteq> sns" by -(drule path2_last, drule path2_last, auto)
      with sns'(2) have "strict_prefix sns' sns" by auto
      thus ?thesis by (rule prefix_length_less)
    qed
    finally show ?thesis by (simp add:sns(2))
  qed

  lemma dominates_shortestPath_order:
    assumes "dominates g n m" "m \<in> set (\<alpha>n g)" "invar g"
    shows "shortestPath g n \<le> shortestPath g m"
  using assms by (cases "n = m", auto intro:strict_dom_shortestPath_order[THEN less_imp_le])

  lemma strict_dom_trans:
    assumes[simp]: "invar g"
    assumes "strict_dom g n m" "strict_dom g m m'"
    shows "strict_dom g n m'"
  proof (rule, rule notI)
    assume "n = m'"
    moreover from assms(3) have "m' \<in> set (\<alpha>n g)" by auto
    ultimately have "dominates g m' n" by auto
    with assms(2) have "dominates g m' m" by - (rule dominates_trans, auto)
    with assms(3) show False by - (erule conjE, drule dominates_antisymm[OF assms(1)], auto)
  next
    from assms show "dominates g n m'" by - (rule dominates_trans, auto)
  qed

  inductive EntryPath :: "'g \<Rightarrow> 'node list \<Rightarrow> bool" where
    EntryPath_triv[simp]: "EntryPath g [n]"
  | EntryPath_snoc[intro]: "EntryPath g ns \<Longrightarrow> shortestPath g m = Suc (shortestPath g (last ns)) \<Longrightarrow> EntryPath g (ns@[m])"

  lemma[simp]:
    assumes "EntryPath g ns" "prefix ns' ns" "ns' \<noteq> []"
    shows "EntryPath g ns'"
  using assms proof induction
    case (EntryPath_triv ns n)
    thus ?case by (cases ns', auto)
  qed auto

  lemma EntryPath_suffix:
    assumes "EntryPath g ns" "suffix ns' ns" "ns' \<noteq> []"
    shows "EntryPath g ns'"
  using assms proof (induction arbitrary: ns')
    case EntryPath_triv
    thus ?case
      by (metis EntryPath.EntryPath_triv append_Nil append_is_Nil_conv list.sel(3) Sublist.suffix_def tl_append2)
  next
    case (EntryPath_snoc g ns m)
    from EntryPath_snoc.prems obtain ns'' where [simp]: "ns' = ns''@[m]"
      by - (erule suffix_unsnoc, auto)
    show ?case
    proof (cases "ns'' = []")
      case True
      thus ?thesis by auto
    next
      case False
      from EntryPath_snoc.prems(1) have "suffix ns'' ns" by (auto simp: Sublist.suffix_def)
      with False have "last ns'' = last ns" by (auto simp: Sublist.suffix_def)
      moreover from False have "EntryPath g ns''" using EntryPath_snoc.prems(1)
        by - (rule EntryPath_snoc.IH, auto simp: Sublist.suffix_def)
      ultimately show ?thesis using EntryPath_snoc.hyps(2)
        by - (simp, rule EntryPath.EntryPath_snoc, simp_all)
    qed
  qed

  lemma EntryPath_butlast_less_last:
    assumes "EntryPath g ns" "z \<in> set (butlast ns)"
    shows "shortestPath g z < shortestPath g (last ns)"
  using assms proof (induction)
    case (EntryPath_snoc g ns m)
    thus ?case by (cases "z \<in> set (butlast ns)", auto dest: not_in_butlast)
  qed simp

  lemma EntryPath_distinct:
    assumes "EntryPath g ns"
    shows "distinct ns"
  using assms
  proof (induction)
    case (EntryPath_snoc g ns m)
    from this consider (non_distinct) "m \<in> set ns" | "distinct (ns @ [m])" by auto
    thus "distinct (ns @ [m])"
    proof (cases)
      case non_distinct
      have "EntryPath g (ns @ [m])" using EntryPath_snoc by (intro EntryPath.intros(2))
      with non_distinct
      have "False"
       using EntryPath_butlast_less_last butlast_snoc last_snoc less_not_refl by force
      thus ?thesis by simp
    qed
  qed simp

  lemma Entry_reachesE:
    assumes "n \<in> set (\<alpha>n g)" and[simp]: "invar g"
    obtains ns where "g \<turnstile> Entry g-ns\<rightarrow>n" "EntryPath g ns"
  using assms(1) proof (induction "shortestPath g n" arbitrary:n)
    case 0
    hence False by simp
    thus ?case..
  next
    case (Suc l)
    note Suc.prems(2)[simp]
    show ?case
    proof (cases "n = Entry g")
      case True
      thus ?thesis by - (rule Suc.prems(1), auto)
    next
      case False
      then obtain n' where n': "shortestPath g n' = l" "n' \<in> set (predecessors g n)"
        using Suc.hyps(2)[symmetric] by - (rule shortestPath_predecessor, auto)
      moreover {
        fix ns
        assume asm: "g \<turnstile> Entry g-ns\<rightarrow>n'" "EntryPath g ns"
        hence thesis using n' Suc.hyps(2) path2_last[OF asm(1)]
          by - (rule Suc.prems(1)[of "ns@[n]"], auto)
      }
      ultimately show thesis by - (rule Suc.hyps(1), auto)
    qed
  qed
end

end

