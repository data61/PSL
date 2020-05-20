theory Graph
imports Main
begin



section\<open>Rooted Graphs\<close>

text \<open>In this section, we model rooted graphs and their sub\hyp{}paths and paths. We give a number 
of lemmas that will help proofs in the following theories, but that are very specific to our 
approach.\<close>

text \<open>First, we will need the following simple lemma, which is not graph related, but that will 
prove useful when we will want to exhibit the last element of a non-empty sequence.\<close>

lemma neq_Nil_conv2 :
  "xs \<noteq> [] = (\<exists> x xs'. xs = xs' @ [x])"
by (induct xs rule : rev_induct, auto)

subsection \<open>Basic Definitions and Properties\<close>

subsubsection \<open>Edges\<close>

text \<open>We model edges by a record \<open>'v edge\<close> which is parameterized by the type \<open>'v\<close> 
of vertices. This allows us to represent the red part
of red-black graphs as well as the black part (i.e. LTS) using extensible records (more on this later). Edges have two 
components, @{term "src"} and @{term "tgt"}, which respectively give their source and target.\<close>


record 'v edge = 
  src   :: "'v"
  tgt   :: "'v"


subsubsection \<open>Rooted graphs\<close>

text \<open>We model rooted graphs by the record \<open>'v rgraph\<close>. It consists of two components: its 
root and its set of edges.\<close>


record 'v rgraph =
  root  :: "'v"
  edges :: "'v edge set"

subsubsection \<open>Vertices\<close>

text \<open>The set of vertices of a rooted graph is made of its root and the endpoints of its 
edges. Isabelle/HOL provides \emph{extensible records}, i.e.\ it is possible to define records using 
existing records by adding components. The following definition suppose that @{term "g"} is of type 
\<open>('v,'x) rgraph_scheme\<close>, i.e.\ an object that has at least all the components of a 
\<open>'v rgraph\<close>. The second type parameter \<open>'x\<close> stands for the hypothetical type 
parameters that such an object could have in addition of the type of vertices \<open>'v\<close>. 
Using \<open>('v,'x) rgraph_scheme\<close> instead of \<open>'v rgraph\<close> allows to reuse the following 
definition(s) for all type of objects that have at least the components of a rooted graph. For 
example, we will reuse the following definition to characterize the set of locations of a LTS (see 
\verb?LTS.thy?).\<close>


definition vertices :: 
  "('v,'x) rgraph_scheme \<Rightarrow> 'v set"
where
  "vertices g = {root g} \<union> src `edges g \<union> tgt ` edges g"

subsubsection \<open>Basic properties of rooted graphs\<close>

text \<open>In the following, we will be only interested in loop free rooted graphs
and in what we call 
\emph{well formed rooted graphs}. A well formed rooted graph is rooted graph that has an empty set 
of edges or, if this is not the case, has at least one edge whose source is its root.\<close>


abbreviation loop_free :: 
  "('v,'x) rgraph_scheme \<Rightarrow> bool" 
where
"loop_free g \<equiv> \<forall> e \<in> edges g. src e \<noteq> tgt e"


abbreviation wf_rgraph :: 
  "('v,'x) rgraph_scheme \<Rightarrow> bool" 
where
"wf_rgraph g \<equiv> root g \<in> src ` edges g = (edges g \<noteq> {})"


text \<open>Even if we are only interested in this kind of rooted graphs, we will not assume the graphs 
are loop free or well formed when this is not needed.\<close>



subsubsection \<open>Out-going edges\<close>

text \<open>This abbreviation will prove handy in the following.\<close>


abbreviation out_edges ::
  "('v,'x) rgraph_scheme \<Rightarrow> 'v \<Rightarrow> 'v edge set" 
where
  "out_edges g v \<equiv> {e \<in> edges g. src e = v}"




subsection \<open>Consistent Edge Sequences, Sub-paths and Paths\<close>

subsubsection \<open>Consistency of a sequence of edges\<close>

text \<open>A sequence of edges @{term "es"} is consistent from
vertex @{term "v1"} to another vertex @{term "v2"} if @{term "v1 = v2"} if it is empty, or, if it is 
not empty:
\begin{itemize}
  \item @{term "v1"} is the source of its first element, and
  \item @{term "v2"} is the target of its last element, and
  \item the target of each of its elements is the source of its follower.
\end{itemize}\<close>


fun ces :: 
  "'v \<Rightarrow> 'v edge list \<Rightarrow> 'v \<Rightarrow> bool" 
where
  "ces v1 [] v2 = (v1 = v2)"
| "ces v1 (e#es) v2 = (src e = v1 \<and> ces (tgt e) es v2)"


subsubsection \<open>Sub-paths and paths\<close>

text \<open>Let @{term "g"} be a rooted graph, @{term "es"} a sequence of edges and @{term "v1"} and 
\<open>v2\<close> two vertices. @{term "es"} is a sub-path in @{term "g"} from @{term "v1"} to 
@{term "v2"} if:
\begin{itemize}
  \item it is consistent from @{term "v1"} to @{term "v2"},
  \item @{term "v1"} is a vertex of @{term "g"},
  \item all of its elements are edges of @{term "g"}.
\end{itemize}

The second constraint is needed in the case of the empty sequence: without it,
the empty sequence would be a sub-path of @{term "g"} even when @{term "v1"} is not one of 
its vertices.\<close>


definition subpath :: 
  "('v,'x) rgraph_scheme \<Rightarrow> 'v \<Rightarrow> 'v edge list \<Rightarrow> 'v \<Rightarrow> bool" 
where
  "subpath g v1 es v2 \<equiv> ces v1 es v2 \<and> v1 \<in> vertices g \<and> set es \<subseteq> edges g"


text \<open>Let @{term "es"} be a sub-path of @{term "g"} leading from @{term "v1"} to @{term "v2"}. 
@{term "v1"} and @{term "v2"} are both vertices of @{term "g"}.\<close>


lemma fst_of_sp_is_vert :
  assumes "subpath g v1 es v2"
  shows   "v1 \<in> vertices g"
using assms by (simp add : subpath_def)


lemma lst_of_sp_is_vert :
  assumes "subpath g v1 es v2"
  shows   "v2 \<in> vertices g"
using assms by (induction es arbitrary : v1, auto simp add: subpath_def vertices_def)


text \<open>The empty sequence of edges is a sub-path from @{term "v1"} to @{term "v2"} if and only if 
they are equal and belong to the graph.\<close>

text \<open>The empty sequence is a sub-path from the root of any rooted graph.\<close>


lemma
  "subpath g (root g) [] (root g)"
by (auto simp add : vertices_def subpath_def)


text \<open>In the following, we will not always be interested in the final vertex of a sub-path. We 
will use the abbreviation @{term "subpath_from"} whenever this final vertex has no importance, and 
@{term subpath} otherwise.\<close>


abbreviation subpath_from  ::
  "('v,'x) rgraph_scheme \<Rightarrow> 'v \<Rightarrow> 'v edge list \<Rightarrow> bool"
where
  "subpath_from g v es \<equiv> \<exists> v'. subpath g v es v'"

abbreviation subpaths_from ::
  "('v,'x) rgraph_scheme \<Rightarrow> 'v \<Rightarrow> 'v edge list set"
where
  "subpaths_from g v \<equiv> {es. subpath_from g v es}"


text \<open>A path is a sub-path starting at the root of the graph.\<close>


abbreviation path :: 
  "('v,'x) rgraph_scheme \<Rightarrow> 'v edge list \<Rightarrow> 'v \<Rightarrow> bool" 
where
  "path g es v \<equiv> subpath g (root g) es v"


abbreviation paths :: 
  "('a,'b) rgraph_scheme \<Rightarrow> 'a edge list set" 
where
  "paths g \<equiv> {es. \<exists> v. path g es v}"


text \<open>The empty sequence is a path of any rooted graph.\<close>


lemma
  "[] \<in> paths g"
by (auto simp add : subpath_def vertices_def)


text \<open>Some useful simplification lemmas for @{term "subpath"}.\<close>


lemma sp_one :
  "subpath g v1 [e] v2 = (src e = v1 \<and> e \<in> edges g \<and> tgt e = v2)"
by (auto simp add : subpath_def vertices_def)


lemma sp_Cons :
  "subpath g v1 (e#es) v2 = (src e = v1 \<and> e \<in> edges g \<and> subpath g (tgt e) es v2)"
by (auto simp add : subpath_def vertices_def)


lemma sp_append_one :
  "subpath g v1 (es@[e]) v2 = (subpath g v1 es (src e) \<and> e \<in> edges g \<and> tgt e = v2)"
by (induct es arbitrary : v1, auto simp add : subpath_def vertices_def)


lemma sp_append :
  "subpath g v1 (es1@es2) v2 = (\<exists> v. subpath g v1 es1 v \<and> subpath g v es2 v2)"
by (induct es1 arbitrary : v1)
   ((simp add : subpath_def, fast),
    (auto simp add : fst_of_sp_is_vert sp_Cons))


text \<open>A sub-path leads to a unique vertex.\<close>


lemma sp_same_src_imp_same_tgt :
  assumes "subpath g v es v1"
  assumes "subpath g v es v2"
  shows   "v1 = v2"
using assms 
by (induct es arbitrary : v) 
   (auto simp add :  sp_Cons subpath_def vertices_def)


text \<open>In the following, we are interested in the evolution of the set of sub-paths of our symbolic 
execution graph after symbolic execution of a transition from the LTS representation of the program 
under analysis. Symbolic execution of a transition results in adding to the graph a new edge whose 
source is already a vertex of this graph, but not its target. The following lemma describes 
sub-paths ending in the target of such an edge.\<close>

text \<open>Let @{term "e"} be an edge whose target has not out-going edges. A sub-path @{term "es"} 
containing @{term "e"} ends by @{term "e"} and this occurrence of @{term "e"} is unique along 
@{term "es"}.\<close>


lemma sp_through_de_decomp :
  assumes "out_edges g (tgt e) = {}"
  assumes "subpath g v1 es v2"
  assumes "e \<in> set es"
  shows   "\<exists> es'. es = es' @ [e] \<and> e \<notin> set es'"
using assms(2,3)
proof (induction es arbitrary : v1)
  case Nil thus ?case by simp
next
  case (Cons e' es) 
  
  hence "e = e' \<or> (e \<noteq> e' \<and> e \<in> set es)" by auto

  thus ?case
  proof (elim disjE, goal_cases)
    case 1 thus ?case
    using assms(1) Cons
    by (rule_tac ?x="[]" in exI) (cases es, auto simp add: sp_Cons)
  next
    case 2 thus ?case 
    using assms(1) Cons(1)[of "tgt e'"] Cons(2)
    by (auto simp add : sp_Cons)
  qed
qed
 

subsection \<open>Adding Edges\<close>

text \<open>This definition and the following lemma are here mainly to ease the definitions and proofs 
in the next theories.\<close>


abbreviation add_edge :: 
  "('v,'x) rgraph_scheme \<Rightarrow> 'v edge \<Rightarrow> ('v,'x) rgraph_scheme" 
where
  "add_edge g e \<equiv> rgraph.edges_update (\<lambda> edges. edges \<union> {e}) g"


text \<open>Let @{term "es"} be a sub-path from a vertex other than the target of @{term "e"} in the 
graph obtained from @{term "g"} by the addition of edge @{term "e"}. Moreover, assume that the 
target of @{term "e"} is not a vertex of @{term "g"}. Then @{term "e"} is an element of 
@{term "es"}.\<close>


lemma sp_ends_in_tgt_imp_mem :
  assumes "tgt e \<notin> vertices g"
  assumes "v \<noteq> tgt e"
  assumes "subpath (add_edge g e) v es (tgt e)"
  shows   "e \<in> set es"
proof -
  have "es \<noteq> []" using assms(2,3) by (auto simp add : subpath_def)

  then obtain e' es' where "es = es' @ [e']" by (simp add : neq_Nil_conv2) blast

  thus ?thesis using assms(1,3) by (auto simp add : sp_append_one vertices_def image_def)
qed


subsection \<open>Trees\<close>

text \<open>We define trees as rooted-graphs in which there exists a unique path leading to each vertex.\<close>


definition is_tree :: 
  "('v,'x) rgraph_scheme \<Rightarrow> bool" 
where
  "is_tree g \<equiv> \<forall> l \<in> Graph.vertices g. \<exists>! p. Graph.path g p l"


text \<open>The empty graph is thus a tree.\<close>


lemma empty_graph_is_tree :
  assumes "edges g = {}"
  shows   "is_tree g"
using assms by (auto simp add : is_tree_def subpath_def vertices_def)

end
