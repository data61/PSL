section \<open>Labeled Graphs\<close>
text \<open>We define graphs as in the paper. Graph homomorphisms and subgraphs are defined slightly
      differently.
      Their correspondence to the definitions in the paper is given by separate lemmas.
      After defining graphs, we only talk about the semantics until after defining homomorphisms.
      The reason is that graph rewriting can be done without knowing about semantics.\<close>

theory LabeledGraphs
imports MissingRelation
begin

datatype ('l,'v) labeled_graph
  = LG (edges:"('l \<times> 'v \<times> 'v) set") (vertices:"'v set")

definition restrict where
  "restrict G = LG {(l,v1,v2) \<in> edges G. v1 \<in> vertices G \<and> v2 \<in> vertices G } (vertices G)"

text \<open>Definition 1. We define graphs and show that any graph with no edges (in particular
       the empty graph) is indeed a graph.\<close>
abbreviation graph where
  "graph X \<equiv> X = restrict X"

lemma graph_empty_e[intro]: "graph (LG {} v)" unfolding restrict_def by auto

lemma graph_single[intro]: "graph (LG {(a,b,c)} {b,c})" unfolding restrict_def by auto

abbreviation finite_graph where
  "finite_graph X \<equiv> graph X \<and> finite (vertices X) \<and> finite (edges X)"

lemma restrict_idemp[simp]:
  "restrict (restrict x) = restrict x"
by(cases x,auto simp:restrict_def)

lemma vertices_restrict[simp]:
  "vertices (restrict G) = vertices G"
  by(cases G,auto simp:restrict_def)

lemma restrictI[intro]:
  assumes "edges G \<subseteq> {(l,v1,v2). v1 \<in> vertices G \<and> v2 \<in> vertices G }"
  shows "G = restrict G"
  using assms by(cases G,auto simp:restrict_def)

lemma restrict_subsD[dest]:
  assumes "edges G \<subseteq> edges (restrict G)"
  shows "G = restrict G"
  using assms by(cases G,auto simp:restrict_def)

lemma restrictD[dest]:
  assumes "G = restrict G"
  shows "edges G \<subseteq> {(l,v1,v2). v1 \<in> vertices G \<and> v2 \<in> vertices G }"
proof -
  have "edges (restrict G) \<subseteq> {(l,v1,v2). v1 \<in> vertices G \<and> v2 \<in> vertices G }"
    by (cases G,auto simp:restrict_def)
  thus ?thesis using assms by auto
qed

(* Given a relation on vertices, make one on edges *)
definition on_triple where "on_triple R \<equiv> {((l,s,t),(l',s',t')) . l=l' \<and> (s,s') \<in> R \<and> (t,t') \<in> R}"

lemma on_triple[simp]:
  "((l1,v1,v2),(l2,v3,v4)) \<in> on_triple R \<longleftrightarrow> (v1,v3)\<in> R \<and> (v2,v4) \<in> R \<and> l1 = l2"
unfolding on_triple_def by auto

lemma on_triple_univ[intro!]:
  "univalent f \<Longrightarrow> univalent (on_triple f)"
  unfolding on_triple_def univalent_def by auto

lemma on_tripleD[dest]:
  assumes "((l1,v1,v2),(l2,v3,v4)) \<in> on_triple R"
  shows "l2 = l1" "(v1,v3)\<in> R" "(v2,v4) \<in> R"
 using assms unfolding on_triple_def by auto

lemma on_triple_ID_restrict[simp]:
  shows "on_triple (Id_on (vertices G)) `` edges G = edges (restrict G)"
  unfolding on_triple_def by(cases G,auto simp:restrict_def)

lemma relcomp_on_triple[simp]:
  shows "on_triple (R O S) = on_triple R O on_triple S"
  unfolding on_triple_def by fast

lemma on_triple_preserves_finite[intro]:
"finite E  \<Longrightarrow> finite (on_triple (BNF_Def.Gr A f) `` E)"
  by (auto simp:on_triple_def BNF_Def.Gr_def)

lemma on_triple_fst[simp]:
  assumes "vertices G = Domain g" "graph G"
  shows "x \<in> fst ` on_triple g `` (edges G) \<longleftrightarrow> x \<in> fst ` edges G"
proof
  assume "x \<in> fst ` on_triple g `` edges G"
  then obtain a b where "(x,a,b) \<in> on_triple g `` edges G" by force
  then obtain c d where "(x,c,d) \<in> edges G" unfolding on_triple_def by auto
  thus "x \<in> fst ` edges G" by force next
  assume "x \<in> fst ` edges G"
  then obtain a b where ab:"(x,a,b) \<in> edges G" by force
  then obtain c d where "(a,c) \<in> g" "(b,d) \<in> g" using assms by force
  hence "(x,c,d) \<in> on_triple g `` edges G" using ab unfolding on_triple_def by auto
  thus "x \<in> fst ` on_triple g `` edges G" by (metis fst_conv image_iff)
qed

definition edge_preserving where
  "edge_preserving h e1 e2 \<equiv> 
     (\<forall> (k,v1,v2) \<in> e1. \<forall> v1' v2'. ((v1, v1') \<in> h \<and> (v2,v2') \<in> h)
                                    \<longrightarrow> (k,v1',v2') \<in> e2)"

lemma edge_preserving_atomic:
  assumes "edge_preserving h1 e1 e2" "(v1, v1') \<in> h1" "(v2, v2') \<in> h1" "(k, v1, v2) \<in> e1"
  shows "(k, v1', v2') \<in> e2"
using assms unfolding edge_preserving_def by auto

lemma edge_preservingI[intro]:
  assumes "on_triple R `` E \<subseteq> G"
  shows "edge_preserving R E G"
  unfolding edge_preserving_def proof(clarify,goal_cases)
  case (1 a s t v1' v2')
  thus ?case by (intro assms[THEN subsetD]) (auto simp:on_triple_def)
  qed

lemma on_triple_dest[dest]:
  assumes "on_triple R `` E \<subseteq> G"
          "(l,x,y) \<in> E" "(x,xx) \<in> R" "(y,yy) \<in> R"
        shows "(l,xx,yy) \<in> G"
  using assms unfolding Image_def on_triple_def by blast

lemma edge_preserving:
  shows "edge_preserving R E G \<longleftrightarrow> on_triple R `` E \<subseteq> G"
proof
  assume "edge_preserving R E G"
  hence "\<And> k v1 v2 v1' v2'. (k, v1, v2)\<in>E \<Longrightarrow>
            (v1, v1') \<in> R \<Longrightarrow> (v2, v2') \<in> R \<Longrightarrow> (k, v1', v2') \<in> G"
    unfolding edge_preserving_def by auto
  then show "on_triple R `` E \<subseteq> G" unfolding Image_def by auto
qed auto

lemma edge_preserving_subset:
  assumes "R\<^sub>1 \<subseteq> R\<^sub>2" "E\<^sub>1 \<subseteq> E\<^sub>2" "edge_preserving R\<^sub>2 E\<^sub>2 G"
  shows "edge_preserving R\<^sub>1 E\<^sub>1 G"
  using assms unfolding edge_preserving_def by blast

lemma edge_preserving_unionI[intro]:
  assumes "edge_preserving f A G" "edge_preserving f B G"
  shows "edge_preserving f (A \<union> B) G"
  using assms unfolding edge_preserving_def by blast

lemma compose_preserves_edge_preserving:
  assumes "edge_preserving h1 e1 e2" "edge_preserving h2 e2 e3"
  shows "edge_preserving (h1 O h2) e1 e3" unfolding edge_preserving_def
proof(standard,standard,standard,standard,standard,standard,goal_cases)
  case (1 _ k _ v1 v2 v1'' v2'')
  hence 1:"(k, v1, v2) \<in> e1" "(v1, v1'') \<in> h1 O h2" "(v2, v2'') \<in> h1 O h2" by auto
  then obtain v1' v2' where
    v:"(v1,v1') \<in> h1" "(v1',v1'') \<in> h2" "(v2,v2') \<in> h1" "(v2',v2'') \<in> h2" by auto
  from edge_preserving_atomic[OF assms(1) v(1,3) 1(1)]
       edge_preserving_atomic[OF assms(2) v(2,4)]
  show ?case by metis
qed

lemma edge_preserving_Id[intro]: "edge_preserving (Id_on y) x x"
unfolding edge_preserving_def by auto

text \<open>This is an alternate version of definition 10. We require @term{vertices s = Domain h}
   to ensure that graph homomorphisms are sufficiently unique:
   The partiality follows the definition in the paper, per the remark before Def. 7.
   but it means that we cannot use Isabelle's total functions for the homomorphisms.
   We show that graph homomorphisms and embeddings coincide in a separate lemma.\<close>

definition graph_homomorphism where
  "graph_homomorphism G\<^sub>1 G\<^sub>2 f 
    = ( vertices G\<^sub>1 = Domain f
      \<and> graph G\<^sub>1 \<and> graph G\<^sub>2
      \<and> f `` vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2
      \<and> univalent f
      \<and> edge_preserving f (edges G\<^sub>1) (edges G\<^sub>2)
      )"

lemma graph_homomorphismI:
  assumes "vertices s = Domain h"
          "h `` vertices s \<subseteq> vertices t"
          "univalent h"
          "edge_preserving h (edges s) (edges t)"
          "s = restrict s" "t = restrict t"
  shows "graph_homomorphism s t h" using assms unfolding graph_homomorphism_def by auto

lemma graph_homomorphism_composes[intro]:
  assumes "graph_homomorphism a b x"
          "graph_homomorphism b c y"
  shows "graph_homomorphism a c (x O y)" proof(rule graph_homomorphismI,goal_cases)
  case 1
    have "vertices a \<subseteq> Domain x" "x `` vertices a \<subseteq> Domain y"
      using assms(1,2)[unfolded graph_homomorphism_def] by blast+
    from this Domain_O[OF this]
    show ?case using assms[unfolded graph_homomorphism_def] by auto
  next
  case 2 from assms show ?case unfolding graph_homomorphism_def by blast 
  qed (insert assms,auto simp:graph_homomorphism_def intro:compose_preserves_edge_preserving)

lemma graph_homomorphism_empty[simp]:
  "graph_homomorphism (LG {} {}) G f \<longleftrightarrow> f = {} \<and> graph G"
unfolding graph_homomorphism_def by auto

lemma graph_homomorphism_Id[intro]:
  shows "graph_homomorphism (restrict a) (restrict a) (Id_on (vertices a))"
  by (rule graph_homomorphismI;auto simp:edge_preserving_def)

lemma Id_on_vertices_identity:
  assumes "graph_homomorphism a b f"
          "(aa, ba) \<in> f"
  shows "(aa, ba) \<in> Id_on (vertices a) O f"
        "(aa, ba) \<in> f O Id_on (vertices b)"
  using assms unfolding graph_homomorphism_def by auto

text \<open>Alternate version of definition 7.\<close>
abbreviation subgraph
  where "subgraph G\<^sub>1 G\<^sub>2 
  \<equiv> graph_homomorphism G\<^sub>1 G\<^sub>2 (Id_on (vertices G\<^sub>1))" 

lemma subgraph_trans:
  assumes "subgraph G\<^sub>1 G\<^sub>2" "subgraph G\<^sub>2 G\<^sub>3"
  shows "subgraph G\<^sub>1 G\<^sub>3"
proof-
  from assms[unfolded graph_homomorphism_def]
  have "Id_on (vertices G\<^sub>1) O Id_on (vertices G\<^sub>2) = Id_on (vertices G\<^sub>1)"
    by auto
  with graph_homomorphism_composes[OF assms] show ?thesis by auto
qed

text \<open> Just before Definition 7 in the paper, a notation is introduced for applying a function to
       a graph. We use @{term map_graph} for this, and the version @{term map_graph_fn} in
       case that its first argument is a total function rather than a partial one. \<close>
(* Introducing the map notation just above Def 7 in the paper *)
definition map_graph :: "('c \<times> 'b) set \<Rightarrow> ('a, 'c) labeled_graph \<Rightarrow> ('a, 'b) labeled_graph" where
  "map_graph f G = LG (on_triple f `` (edges G)) (f `` (vertices G))"

lemma map_graph_selectors[simp]:
  "vertices (map_graph f G) = f `` (vertices G)"
  "edges (map_graph f G) = on_triple f `` (edges G)"
  unfolding map_graph_def by auto

lemma map_graph_comp[simp]:
  assumes "Range g \<subseteq> Domain f"
  shows "map_graph (g O f) = map_graph f o map_graph g"
proof(standard,goal_cases) (* need goal_cases to get the type of x right *)
  case (1 x)
  from assms have "map_graph (g O f) x = (map_graph f o map_graph g) x"
    unfolding map_graph_def by auto
  thus ?case by auto
qed

lemma map_graph_returns_restricted:
  assumes "vertices G = Domain f"
  shows "map_graph f G = restrict (map_graph f G)"
  using assms by(cases G,auto simp:map_graph_def restrict_def)

lemma map_graph_preserves_restricted[intro]:
  assumes "graph G"
  shows "graph (map_graph f G)"
proof(rule restrictI,standard) fix x
  assume "x \<in> edges (map_graph f G)"
  with assms show "x \<in> {(l, v1, v2). v1\<in>vertices (map_graph f G) \<and> v2\<in>vertices (map_graph f G)}"
    by(cases x,auto simp:map_graph_def)
qed

lemma map_graph_edge_preserving[intro]:
  shows "edge_preserving f (edges G) (edges (map_graph f G))"
  unfolding map_graph_def by auto

lemma map_graph_homo[intro]:
  assumes "univalent f" "vertices G = Domain f" "G = restrict G"
  shows "graph_homomorphism G (map_graph f G) f"
proof(rule graph_homomorphismI)
  show "f `` vertices G \<subseteq> vertices (map_graph f G)"
    unfolding map_graph_def by auto
  show "edge_preserving f (edges G) (edges (map_graph f G))" by auto
  show "map_graph f G = restrict (map_graph f G)" using assms by auto
qed fact+

lemma map_graph_homo_simp:
  "graph_homomorphism G (map_graph f G) f
   \<longleftrightarrow> univalent f \<and> vertices G = Domain f \<and> graph G"
proof
  show "graph_homomorphism G (map_graph f G) f \<Longrightarrow>
    univalent f \<and> vertices G = Domain f \<and> G = restrict G"
    unfolding graph_homomorphism_def by blast
qed auto

abbreviation on_graph where
"on_graph G f \<equiv> BNF_Def.Gr (vertices G) f"

abbreviation map_graph_fn where
"map_graph_fn G f \<equiv> map_graph (on_graph G f) G"

lemma map_graph_fn_graphI[intro]:
"graph (map_graph_fn G f)" unfolding map_graph_def restrict_def by auto

lemma on_graph_id[simp]:
  shows "on_graph B id = Id_on (vertices B)"
  unfolding BNF_Def.Gr_def by auto

lemma in_on_graph[intro]:
  assumes "x \<in> vertices G" "(a x,y) \<in> b"
  shows "(x, y) \<in> on_graph G a O b"
  using assms unfolding BNF_Def.Gr_def by auto

lemma on_graph_comp:
  "on_graph G (f o g) = on_graph G g O on_graph (map_graph_fn G g) f"
  unfolding BNF_Def.Gr_def by auto

lemma map_graph_fn_eqI:
  assumes "\<And> x. x \<in> vertices G \<Longrightarrow> f x = g x"
  shows "map_graph_fn G f = map_graph_fn G g" (is "?l = ?r")
proof -
  {  fix a ac ba
    assume "(a, ac, ba) \<in> edges G" "ac \<in> vertices G" "ba \<in> vertices G"
    hence "\<exists>x\<in>edges G. (x, a, g ac, g ba) \<in> on_triple (on_graph G f)"
          "\<exists>x\<in>edges G. (x, a, g ac, g ba) \<in> on_triple (on_graph G g)"
      using assms by (metis in_Gr on_triple)+
  }
  hence e:"edges ?l = edges ?r" using assms by (auto simp:Image_def) 
  have v:"vertices ?l = vertices ?r" using assms by (auto simp:image_def)
  from e v show ?thesis by(cases ?l,cases ?r,auto)
qed

lemma map_graph_fn_comp[simp]:
"map_graph_fn G (f o g) = map_graph_fn (map_graph_fn G g) f"
  unfolding on_graph_comp by auto

lemma map_graph_fn_id[simp]:
"map_graph_fn X id = restrict X"
"map_graph (Id_on (vertices X)) X = restrict X"
  unfolding BNF_Def.Gr_def map_graph_def on_triple_def restrict_def by (cases X,force)+

lemma graph_homo[intro!]:
  assumes "graph G"
  shows "graph_homomorphism G (map_graph_fn G f) (on_graph G f)"
  using assms unfolding map_graph_homo_simp BNF_Def.Gr_def univalent_def by auto

lemma graph_homo_inv[intro!]:
  assumes "graph G" "inj_on f (vertices G)"
  shows "graph_homomorphism (map_graph_fn G f) G (converse (on_graph G f))"
proof(rule graph_homomorphismI)
  show "univalent ((on_graph G f)\<inverse>)" using assms(2)
    unfolding univalent_def BNF_Def.Gr_def inj_on_def by auto
  show "edge_preserving ((on_graph G f)\<inverse>) (edges (map_graph_fn G f)) (edges G)"
    using assms unfolding edge_preserving inj_on_def by auto auto
qed (insert assms(1),auto)

lemma edge_preserving_on_graphI[intro]:
  assumes "\<And> l x y. (l,x,y)\<in>edges X \<Longrightarrow> x\<in>vertices X \<Longrightarrow> y \<in> vertices X \<Longrightarrow> (l,f x,f y) \<in> Y"
  shows "edge_preserving (on_graph X f) (edges X) Y"
  using assms unfolding edge_preserving_def BNF_Def.Gr_def by auto

lemma subgraph_subset:
  assumes "subgraph G\<^sub>1 G\<^sub>2"
  shows "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2" "edges (restrict G\<^sub>1) \<subseteq> edges G\<^sub>2"
proof -
  have vrt:"Id_on (vertices G\<^sub>1) `` vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2"
    and ep:"edge_preserving (Id_on (vertices G\<^sub>1)) (edges G\<^sub>1) (edges G\<^sub>2)"
    using assms unfolding graph_homomorphism_def by auto
  hence "edges (restrict G\<^sub>1) \<subseteq> edges G\<^sub>2"
    using assms unfolding edge_preserving by auto
  thus "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2" "edges (restrict G\<^sub>1) \<subseteq> edges G\<^sub>2"
    using vrt by auto
qed

text \<open>Our definition of subgraph is equivalent to definition 7.\<close>
lemma subgraph_def2:
  assumes "graph G\<^sub>1" "graph G\<^sub>2"
  shows "subgraph G\<^sub>1 G\<^sub>2 \<longleftrightarrow> vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2 \<and> edges G\<^sub>1 \<subseteq> edges G\<^sub>2"
proof
  assume "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2 \<and> edges G\<^sub>1 \<subseteq> edges G\<^sub>2"
  hence v:"vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2" and "edges G\<^sub>1 \<subseteq> edges G\<^sub>2" by auto
  hence ep:"edge_preserving (Id_on (vertices G\<^sub>1)) (edges G\<^sub>1) (edges G\<^sub>2)"
    unfolding edge_preserving_def by auto
  show "subgraph G\<^sub>1 G\<^sub>2"
    using assms(2) v ep graph_homomorphism_Id[of "G\<^sub>1",folded assms]
    unfolding graph_homomorphism_def by auto
next
  assume sg:"subgraph G\<^sub>1 G\<^sub>2"
  hence vrt:"Id_on (vertices G\<^sub>1) `` vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2"
    and ep:"edge_preserving (Id_on (vertices G\<^sub>1)) (edges G\<^sub>1) (edges G\<^sub>2)"
    unfolding graph_homomorphism_def by auto
  hence "edges G\<^sub>1 \<subseteq> edges G\<^sub>2"
    using assms unfolding edge_preserving by auto
  thus "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2 \<and> edges G\<^sub>1 \<subseteq> edges G\<^sub>2"
    using vrt by auto
qed

text \<open>We also define @{term graph_union}. In contrast to the paper, our definition ignores the labels.
      The corresponding definition in the paper is written just above Definition 7.
      Adding labels to graphs would require a lot of unnecessary additional bookkeeping.
      Nowhere in the paper is the union actually used on different sets of labels,
      in which case these definitions coincide.\<close>

(* Since the set of labels is an implicit type, the notion of graph_union does not completely correspond to the one in the paper *)
definition graph_union where
"graph_union G\<^sub>1 G\<^sub>2 = LG (edges G\<^sub>1 \<union> edges G\<^sub>2) (vertices G\<^sub>1 \<union> vertices G\<^sub>2)"

lemma graph_unionI[intro]:
  assumes "edges G\<^sub>1 \<subseteq> edges G\<^sub>2"
          "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2"
  shows "graph_union G\<^sub>1 G\<^sub>2 = G\<^sub>2"
  using assms unfolding graph_union_def by (cases "G\<^sub>2",auto)

lemma graph_union_iff:
  shows "graph_union G\<^sub>1 G\<^sub>2 = G\<^sub>2 \<longleftrightarrow> (edges G\<^sub>1 \<subseteq> edges G\<^sub>2 \<and> vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2)"
  unfolding graph_union_def by (cases "G\<^sub>2",auto)

lemma graph_union_idemp[simp]:
"graph_union A A = A"
"graph_union A (graph_union A B) = (graph_union A B)"
"graph_union A (graph_union B A) = (graph_union B A)"
unfolding graph_union_def by auto

lemma graph_union_vertices[simp]:
"vertices (graph_union G\<^sub>1 G\<^sub>2) = vertices G\<^sub>1 \<union> vertices G\<^sub>2"
  unfolding graph_union_def by auto
lemma graph_union_edges[simp]:
"edges (graph_union G\<^sub>1 G\<^sub>2) = edges G\<^sub>1 \<union> edges G\<^sub>2"
  unfolding graph_union_def by auto

lemma graph_union_preserves_restrict[intro]:
  assumes "G\<^sub>1 = restrict G\<^sub>1" "G\<^sub>2 = restrict G\<^sub>2"
  shows "graph_union G\<^sub>1 G\<^sub>2 = restrict (graph_union G\<^sub>1 G\<^sub>2)"
proof -
  let ?e = "edges G\<^sub>1 \<union> edges G\<^sub>2"
  let ?v = "vertices G\<^sub>1 \<union> vertices G\<^sub>2"
  let ?r = "{(l, v1, v2). (l, v1, v2) \<in> ?e \<and> v1 \<in> ?v \<and> v2 \<in> ?v}" (* restricted edges *)
  { fix l v1 v2
    assume a:"(l,v1,v2) \<in> ?e"
    have "(l,v1,v2) \<in> ?r" proof(cases "(l,v1,v2) \<in> edges (restrict G\<^sub>1)")
      case True
      hence "(l,v1,v2) \<in> edges G\<^sub>1" "v1 \<in> vertices G\<^sub>1" "v2 \<in> vertices G\<^sub>1"
         by (auto simp:restrict_def)+
      thus ?thesis by auto
    next
      case False hence "(l,v1,v2) \<in> edges (restrict G\<^sub>2)" using a assms by auto
      hence "(l,v1,v2) \<in> edges G\<^sub>2" "v1 \<in> vertices G\<^sub>2" "v2 \<in> vertices G\<^sub>2"
         by (auto simp:restrict_def)+
      then show ?thesis by auto
    qed
  }
  hence "?e = ?r" by auto
  thus ?thesis unfolding graph_union_def by auto
qed

lemma graph_map_union[intro]:
  assumes "\<And> i::nat. graph_union (map_graph (g i) X) Y = Y" "\<And> i j. i \<le> j \<Longrightarrow> g i \<subseteq> g j"
  shows "graph_union (map_graph (\<Union>i. g i) X) Y = Y"
proof
  from assms have e:"edges (map_graph (g i) X) \<subseteq> edges Y"
              and v:"vertices (map_graph (g i) X) \<subseteq> vertices Y" for i by (auto simp:graph_union_iff)
  { fix a ac ba aa b x xa
    assume a:"(a, ac, ba) \<in> edges X" "(ac, aa) \<in> g x" "(ba, b) \<in> g xa"
    have "(a, aa, b) \<in> edges Y"
    proof(cases "x < xa")
      case True
      hence "(a, ac, ba) \<in> edges X" "(ac, aa) \<in> g xa" "(ba, b) \<in> g xa"
        using a assms(2)[of x xa] by auto
      then show ?thesis using e[of xa] by auto
    next
      case False
      hence "(a, ac, ba) \<in> edges X" "(ac, aa) \<in> g x" "(ba, b) \<in> g x"
        using a assms(2)[of xa x] by auto
      then show ?thesis using e[of x] by auto
    qed
  }
  thus "edges (map_graph (\<Union>i. g i) X) \<subseteq> edges Y" by auto
  show "vertices (map_graph (\<Union>i. g i) X) \<subseteq> vertices Y" using v by auto
qed

text \<open>We show that @{term subgraph} indeed matches the definition in the paper (Definition 7).\<close>

lemma subgraph_def:
"subgraph G\<^sub>1 G\<^sub>2 = (G\<^sub>1 = restrict G\<^sub>1 \<and> G\<^sub>2 = restrict G\<^sub>2 \<and> graph_union G\<^sub>1 G\<^sub>2 = G\<^sub>2)"
proof
  assume assms:"subgraph G\<^sub>1 G\<^sub>2"
  hence r:"G\<^sub>2 = restrict G\<^sub>2" "G\<^sub>1 = restrict G\<^sub>1"
    unfolding graph_homomorphism_def by auto
  from subgraph_subset[OF assms]
  have ss:"vertices (restrict G\<^sub>1) \<subseteq> vertices G\<^sub>2" "edges (restrict G\<^sub>1) \<subseteq> edges G\<^sub>2" by auto
  show "G\<^sub>1 = restrict G\<^sub>1 \<and> G\<^sub>2 = restrict G\<^sub>2 \<and> graph_union G\<^sub>1 G\<^sub>2 = G\<^sub>2"
  proof(cases G\<^sub>2)
    case (LG x1 x2) show ?thesis using ss r
    unfolding graph_union_def LG by auto
  qed next
  assume gu: "G\<^sub>1 = restrict G\<^sub>1 \<and> G\<^sub>2 = restrict G\<^sub>2 \<and> graph_union G\<^sub>1 G\<^sub>2 = G\<^sub>2"
  hence sub:"(edges G\<^sub>1 \<union> edges G\<^sub>2) \<subseteq> edges G\<^sub>2"
    "vertices G\<^sub>1 \<subseteq> vertices G\<^sub>2"
    unfolding graph_union_def by (cases G\<^sub>2;auto)+
  have r:"G\<^sub>1 = restrict G\<^sub>1" "G\<^sub>2 = restrict G\<^sub>2" using gu by auto
  show "subgraph G\<^sub>1 G\<^sub>2" unfolding subgraph_def2[OF r] using sub by auto
qed

lemma subgraph_refl[simp]: 
"subgraph G G = (G = restrict G)"
  unfolding subgraph_def graph_union_def by(cases G,auto)

lemma subgraph_restrict[simp]:
  "subgraph G (restrict G) = graph G"
  using subgraph_refl subgraph_def by auto

text \<open>Definition 10. We write @{term graph_homomorphism} instead of embedding.\<close>
lemma graph_homomorphism_def2: (* Shows a graph homomorphism is an embedding as in the paper *)
  shows "graph_homomorphism G\<^sub>1 G\<^sub>2 f =
   (vertices G\<^sub>1 = Domain f \<and> univalent f \<and> G\<^sub>1 = restrict G\<^sub>1 \<and> G\<^sub>2 = restrict G\<^sub>2 \<and> graph_union (map_graph f G\<^sub>1) G\<^sub>2 = G\<^sub>2)"
   (is "?lhs = ?rhs")
proof 
  let ?m = "map_graph f G\<^sub>1"
  assume ?rhs
  hence assms : "vertices G\<^sub>1 = Domain f" "univalent f" "G\<^sub>1 = restrict G\<^sub>1"
    and sg: "subgraph ?m G\<^sub>2"
    and f_id:"f O Id_on (f `` vertices G\<^sub>1) = f" unfolding subgraph_def by auto
  hence "edge_preserving (Id_on (vertices ?m)) (edges ?m) (edges G\<^sub>2)"
    unfolding graph_homomorphism_def by auto
  hence "on_triple (f O Id_on (f `` vertices G\<^sub>1)) `` edges G\<^sub>1 \<subseteq> edges G\<^sub>2"  (* rewriting peak *)
    unfolding relcomp_Image edge_preserving map_graph_selectors relcomp_on_triple.
  hence "edge_preserving f (edges G\<^sub>1) (edges G\<^sub>2)"
    unfolding edge_preserving f_id.
  thus ?lhs
    using sg assms unfolding graph_homomorphism_def
    by auto next
  assume ih:?lhs
  hence "vertices G\<^sub>1 = Domain f \<and> univalent f \<and> G\<^sub>1 = restrict G\<^sub>1 \<and> subgraph (map_graph f G\<^sub>1) G\<^sub>2"
    unfolding graph_homomorphism_def edge_preserving
    by auto
  thus ?rhs unfolding subgraph_def by auto
qed


lemma map_graph_preserves_subgraph[intro]:
  assumes "subgraph A B"
  shows "subgraph (map_graph f A) (map_graph f B)"
  using assms unfolding subgraph_def by (auto simp:graph_union_iff)

lemma graph_homomorphism_concr_graph:
  assumes "graph G" "graph (LG e v)"
  shows "graph_homomorphism (LG e v) G x \<longleftrightarrow>
         x `` v \<subseteq> vertices G \<and> on_triple x `` e \<subseteq> edges G \<and> univalent x \<and> Domain x = v"
  using assms unfolding graph_homomorphism_def2 graph_union_iff by auto

lemma subgraph_preserves_hom:
  assumes "subgraph A B"
          "graph_homomorphism X A h"
  shows "graph_homomorphism X B h"
  using assms by (meson graph_homomorphism_def2 map_graph_preserves_restricted subgraph_def subgraph_trans)

lemma graph_homo_union_id:
assumes "graph_homomorphism (graph_union A B) G f"
shows "graph A \<Longrightarrow> graph_homomorphism A G (Id_on (vertices A) O f)"
      "graph B \<Longrightarrow> graph_homomorphism B G (Id_on (vertices B) O f)"
  using assms unfolding graph_homomorphism_def edge_preserving
  by (auto dest:edge_preserving_atomic)

lemma graph_homo_union[intro]:
  assumes
   "graph_homomorphism A G f_a"
   "graph_homomorphism B G f_b"
   "Domain f_a \<inter> Domain f_b = Domain (f_a \<inter> f_b)"
  shows "graph_homomorphism (graph_union A B) G (f_a \<union> f_b)"
proof(rule graph_homomorphismI)
  have v0:"f_a `` vertices A \<subseteq> vertices G" "f_b `` vertices B \<subseteq> vertices G"
          "vertices A = Domain f_a" "vertices B = Domain f_b"
          "graph A" "graph B"
          "univalent f_a" "univalent f_b"
          "edge_preserving f_a (edges A) (edges G)"
          "edge_preserving f_b (edges B) (edges G)"
    using assms(1,2) unfolding graph_homomorphism_def by blast+
  hence v: "f_a `` vertices (graph_union A B) \<subseteq> vertices G"
           "f_b `` vertices (graph_union A B) \<subseteq> vertices G" by auto
  show uni:"univalent (f_a \<union> f_b)" using assms(3) v0 by auto
  show "(f_a \<union> f_b) `` vertices (graph_union A B) \<subseteq> vertices G" using v by auto
  have f_a:"Id_on (vertices A) O (f_a \<union> f_b) = f_a"
        using uni v0(3)
        by (cases A,auto simp:univalent_def on_triple_def Image_def)
  have onA:"on_triple (f_a \<union> f_b) `` edges A = on_triple (Id_on (vertices A) O (f_a \<union> f_b)) `` edges A"
    unfolding relcomp_on_triple relcomp_Image on_triple_ID_restrict v0(5)[symmetric] ..
  have f_b:"Id_on (vertices B) O (f_a \<union> f_b) = f_b"
        using uni v0(4) unfolding Un_commute[of f_a _]
        by (cases B,auto simp:univalent_def on_triple_def Image_def)
  have onB:"on_triple (f_a \<union> f_b) `` edges B = on_triple (Id_on (vertices B) O (f_a \<union> f_b)) `` edges B"
    unfolding relcomp_on_triple relcomp_Image on_triple_ID_restrict v0(6)[symmetric] ..
  have "edge_preserving (f_a \<union> f_b) (edges A) (edges G)"
       "edge_preserving (f_a \<union> f_b) (edges B) (edges G)"
    using v0(9,10) unfolding edge_preserving onA[unfolded f_a] onB[unfolded f_b] by auto
  thus "edge_preserving (f_a \<union> f_b) (edges (graph_union A B)) (edges G)"
    by auto
qed (insert assms[unfolded graph_homomorphism_def],auto)

lemma graph_homomorphism_on_graph:
  assumes "graph_homomorphism A B R"
  shows "graph_homomorphism A (map_graph_fn B f) (R O on_graph B f)"
proof -
  from assms have "Range R \<subseteq> vertices B"
    and ep: "edge_preserving R (edges A) (edges B)" unfolding graph_homomorphism_def by auto
  hence d:"Domain R \<subseteq> Domain (R O on_graph B f)" unfolding Domain_id_on by auto
  have v:"vertices (map_graph (R O on_graph B f) A) \<subseteq> vertices (map_graph_fn B f)"
    unfolding BNF_Def.Gr_def map_graph_selectors by auto
  have e:"edges (map_graph (R O on_graph B f) A) \<subseteq> edges (map_graph_fn B f)" using ep
    unfolding BNF_Def.Gr_def map_graph_selectors edge_preserving by auto
  have u:"graph_union (map_graph (R O on_graph B f) A) (map_graph_fn B f) = map_graph_fn B f"
    using e v graph_unionI by metis
  from d assms u show "graph_homomorphism A (map_graph_fn B f) (R O on_graph B f)"
    unfolding graph_homomorphism_def2 by auto
qed

end