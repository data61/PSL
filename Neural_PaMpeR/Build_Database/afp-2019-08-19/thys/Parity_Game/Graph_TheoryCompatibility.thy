section \<open>Compatibility with the Graph Theory Package\<close>

theory Graph_TheoryCompatibility
imports
  ParityGame
  Graph_Theory.Digraph
  Graph_Theory.Digraph_Isomorphism
begin

text \<open>
  In this section, we show that our @{locale Digraph} locale is compatible to the
  @{locale nomulti_digraph} locale from the graph theory package from the Archive of Formal Proofs.

  For this, we will define two functions converting between the different types and show that with
  these conversion functions the locales interpret each other.  Together, this indicates that our
  definition of digraph is reasonable.
\<close>

subsection \<open>To Graph Theory\<close>

text \<open>We can easily convert our graphs into @{type pre_digraph} objects.\<close>
definition to_pre_digraph :: "('a, 'b) Graph_scheme \<Rightarrow> ('a, 'a \<times> 'a) pre_digraph"
  where "to_pre_digraph G \<equiv> \<lparr>
    pre_digraph.verts = Graph.verts G,
    pre_digraph.arcs = Graph.arcs G,
    tail = fst,
    head = snd
  \<rparr>"

text \<open>
  With this conversion function, our @{locale Digraph} locale contains the locale
  @{locale nomulti_digraph} from the graph theory package.
\<close>
context Digraph begin
interpretation is_nomulti_digraph: nomulti_digraph "to_pre_digraph G" proof
  fix e assume *: "e \<in> pre_digraph.arcs (to_pre_digraph G)"
  show "tail (to_pre_digraph G) e \<in> pre_digraph.verts (to_pre_digraph G)"
    by (metis * edges_are_in_V(1) pre_digraph.ext_inject pre_digraph.surjective prod.collapse to_pre_digraph_def)
  show "head (to_pre_digraph G) e \<in> pre_digraph.verts (to_pre_digraph G)"
    by (metis * edges_are_in_V(2) pre_digraph.ext_inject pre_digraph.surjective prod.collapse to_pre_digraph_def)
qed (simp add: arc_to_ends_def to_pre_digraph_def)
end


subsection \<open>From Graph Theory\<close>

text \<open>We can also convert in the other direction.\<close>
definition from_pre_digraph :: "('a, 'b) pre_digraph \<Rightarrow> 'a Graph"
  where "from_pre_digraph G \<equiv> \<lparr>
    Graph.verts = pre_digraph.verts G,
    Graph.arcs = arcs_ends G
  \<rparr>"

context nomulti_digraph begin
interpretation is_Digraph: Digraph "from_pre_digraph G" proof-
  {
    fix v w assume "(v,w) \<in> E\<^bsub>from_pre_digraph G\<^esub>"
    then obtain e where e: "e \<in> pre_digraph.arcs G" "tail G e = v" "head G e = w"
      unfolding from_pre_digraph_def by auto
    hence "(v,w) \<in> V\<^bsub>from_pre_digraph G\<^esub> \<times> V\<^bsub>from_pre_digraph G\<^esub>"
      unfolding from_pre_digraph_def by auto
  }
  thus "Digraph (from_pre_digraph G)" by (simp add: Digraph.intro subrelI)
qed
end

subsection \<open>Isomorphisms\<close>

text \<open>
  We also show that our conversion functions make sense.  That is, we show that they are nearly
  inverses of each other.  Unfortunately, @{const from_pre_digraph} irretrievably loses information
  about the arcs, and only keeps tail/head intact, so the best we can get for this case is that the
  back-and-forth converted graphs are isomorphic.
\<close>

lemma graph_conversion_bij: "G = from_pre_digraph (to_pre_digraph G)"
  unfolding to_pre_digraph_def from_pre_digraph_def arcs_ends_def arc_to_ends_def by auto

lemma (in nomulti_digraph) graph_conversion_bij2: "digraph_iso G (to_pre_digraph (from_pre_digraph G))"
proof-
  define iso 
    where "iso = \<lparr>
      iso_verts = id :: 'a \<Rightarrow> 'a,
      iso_arcs = arc_to_ends G,
      iso_head = snd,
      iso_tail = fst
    \<rparr>"

  have "inj_on (iso_verts iso) (pre_digraph.verts G)" unfolding iso_def by auto
  moreover have "inj_on (iso_arcs iso) (pre_digraph.arcs G)"
    unfolding iso_def arc_to_ends_def by (simp add: arc_to_ends_def inj_onI no_multi_arcs)
  moreover have "\<forall>a \<in> pre_digraph.arcs G.
    iso_verts iso (tail G a) = iso_tail iso (iso_arcs iso a)
    \<and> iso_verts iso (head G a) = iso_head iso (iso_arcs iso a)"
    unfolding iso_def by (simp add: arc_to_ends_def)

  ultimately have "digraph_isomorphism iso"
    unfolding digraph_isomorphism_def using arc_to_ends_def wf_digraph_axioms by blast

  moreover have "to_pre_digraph (from_pre_digraph G) = app_iso iso G"
      unfolding to_pre_digraph_def from_pre_digraph_def iso_def app_iso_def by (simp_all add: arcs_ends_def)

  ultimately show ?thesis unfolding digraph_iso_def by blast
qed

end
