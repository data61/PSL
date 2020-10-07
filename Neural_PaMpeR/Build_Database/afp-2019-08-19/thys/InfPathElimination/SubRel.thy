theory SubRel
imports Graph
begin 

section \<open>Graphs equipped with a subsumption relation\<close>

text \<open>In this section, we define subsumption relations and the notion of sub\hyp{}paths in 
rooted graphs equipped with such relations. Sub-paths are defined in the same way than in 
\verb?Graph.thy?: first we define the consistency of a sequence of edges in presence of a 
subsumption relation, then sub-paths. We are interested in subsumptions taking places between red 
vertices of red-black graphs (see \verb?RB.thy?), i.e.\ occurrences of locations of LTSs. Here 
subsumptions are defined as pairs of indexed vertices of a LTS, and subsumption relations as sets 
of subsumptions. The type of vertices of such LTSs is represented by the abstract type \<open>'v\<close> 
in the following.\<close>

subsection \<open>Basic definitions and properties\<close>

subsubsection \<open>Subsumptions and subsumption relations\<close>

text \<open>Subsumptions take place between occurrences of the vertices of a graph. We represent 
such occurrences by indexed versions of vertices. A subsumption is defined as pair of indexed 
vertices.\<close>


type_synonym 'v sub_t = "(('v \<times> nat) \<times> ('v \<times> nat))"


text \<open>A subsumption relation is a set of subsumptions.\<close>


type_synonym 'v sub_rel_t = "'v sub_t set"


text \<open>We consider the left member to be subsumed by the right one. The left member of a 
subsumption is called its \emph{subsumee}, the right member its \emph{subsumer}.\<close>


abbreviation subsumee :: 
  "'v sub_t \<Rightarrow> ('v \<times> nat)" 
where 
  "subsumee sub \<equiv> fst sub"


abbreviation subsumer :: 
  "'v sub_t \<Rightarrow> ('v \<times> nat)" 
where 
  "subsumer sub \<equiv> snd sub"


text \<open>We will need to talk about the sets of subsumees and subsumers of a subsumption relation.\<close>


abbreviation subsumees :: 
  "'v sub_rel_t \<Rightarrow> ('v \<times> nat) set" 
where 
  "subsumees subs \<equiv> subsumee ` subs"


abbreviation subsumers :: 
  "'v sub_rel_t \<Rightarrow> ('v \<times> nat) set" 
where 
  "subsumers subs \<equiv> subsumer ` subs"


text \<open>The two following lemmas will prove useful in the following.\<close>


lemma subsumees_conv :
  "subsumees subs = {v. \<exists> v'. (v,v') \<in> subs}"
by force


lemma subsumers_conv :
  "subsumers subs = {v'. \<exists> v. (v,v') \<in> subs}"
by force



text \<open>We call set of vertices of the relation the union of its sets of subsumees and subsumers.\<close>


abbreviation vertices ::
  "'v sub_rel_t \<Rightarrow> ('v \<times> nat) set" 
where
  "vertices subs \<equiv> subsumers subs \<union> subsumees subs"


subsection \<open>Well-formed subsumption relation of a graph\<close>

subsubsection \<open>Well-formed subsumption relations\<close>

text \<open>In the following, we make an intensive use of \emph{locales}. We use them as a convenient 
way to add assumptions to the following lemmas, in order to ease their reading. Locales can be 
built from locales, allowing some modularity in the formalization. The following locale simply 
states that we suppose there exists  a subsumption relation called \emph{subs}. It will 
be used later in order to constrain subsumption relations.\<close>


locale sub_rel =
  fixes subs :: "'v sub_rel_t" (structure)


text \<open>We are only interested in subsumptions involving two different
occurrences of the same LTS 
location. Moreover, once a vertex has been subsumed, there is no point in trying to subsume it again
by another subsumer: subsumees must have a unique subsumer. Finally, we do not allow chains of 
subsumptions, thus the intersection of the sets of subsumers and subsumees must be empty. Such 
subsumption relations are said to be \emph{well-formed}.\<close>


locale wf_sub_rel = sub_rel +
  assumes sub_imp_same_verts : 
    "sub \<in> subs \<Longrightarrow> fst (subsumee sub) = fst (subsumer sub)"
  
  assumes subsumed_by_one : 
    "\<forall> v \<in> subsumees subs. \<exists>! v'. (v,v') \<in> subs"
  
  assumes inter_empty : 
    "subsumers subs \<inter> subsumees subs = {}"

begin
  lemmas wf_sub_rel = sub_imp_same_verts subsumed_by_one inter_empty

  text \<open>A rephrasing of the assumption @{term "subsumed_by_one"}.\<close>

  lemma (in wf_sub_rel) subsumed_by_two_imp : 
    assumes "(v,v1) \<in> subs"
    assumes "(v,v2) \<in> subs" 
    shows   "v1 = v2"
  using assms wf_sub_rel unfolding subsumees_conv by blast
  
  text \<open>A well-formed subsumption relation is equal to its transitive closure. We will see in the 
  following one has to handle transitive closures of such relations.\<close>

  lemma in_trancl_imp :
    assumes "(v,v') \<in> subs\<^sup>+"
    shows   "(v,v') \<in> subs"
  using tranclD[OF assms] tranclD[of _ v' subs]
        rtranclD[of _ v' subs]  
        inter_empty 
  by force

  lemma trancl_eq :
    "subs\<^sup>+ = subs"
  using in_trancl_imp r_into_trancl[of _ _ subs] by fast
end


text \<open>The empty subsumption relation is well-formed.\<close>


lemma
  "wf_sub_rel {}"
by (auto simp add : wf_sub_rel_def)


subsubsection \<open>Subsumption relation of a graph\<close>

text \<open>We consider subsumption relations to equip rooted graphs. However, nothing in the previous 
definitions relates these relations to graphs: subsumptions relations involve objects that are of 
the type of indexed vertices, but that might to not be vertices of an actual graph. We equip 
graphs with subsumption relations using the notion of \emph{sub-relation of a graph}. Such a 
relation must only involve vertices of the graph it equips.\<close>


locale rgraph = 
  fixes g :: "('v,'x) rgraph_scheme" (structure)


locale sub_rel_of = rgraph + sub_rel +
  assumes related_are_verts : "vertices subs \<subseteq> Graph.vertices g"
begin
  lemmas sub_rel_of = related_are_verts

  text \<open>The transitive closure of a sub-relation of a graph @{term "g"} is also a sub-relation of 
  @{term "g"}.\<close>

  lemma trancl_sub_rel_of :
     "sub_rel_of g (subs\<^sup>+)"
  using tranclD[of _ _ subs] tranclD2[of _ _ subs] sub_rel_of
  unfolding sub_rel_of_def subsumers_conv subsumees_conv by blast
end


text \<open>The empty relation is a sub-relation of any graph.\<close>


lemma
  "sub_rel_of g {}"
by (auto simp add : sub_rel_of_def)


subsubsection \<open>Well-formed sub-relations\<close>

text \<open>We pack both previous locales into a third one. We speak about 
\emph{well-formed sub-relations}.\<close>


locale wf_sub_rel_of = rgraph + sub_rel +
  assumes sub_rel_of : "sub_rel_of g subs"
  assumes wf_sub_rel : "wf_sub_rel subs"
begin
  lemmas wf_sub_rel_of = sub_rel_of wf_sub_rel                                                       
end


text \<open>The empty relation is a well-formed sub-relation of any graph.\<close>


lemma
  "wf_sub_rel_of g {}"
by (auto simp add : sub_rel_of_def wf_sub_rel_def wf_sub_rel_of_def)


text \<open>As previously, even if, in the end, we are only interested by well-formed sub-relations, we 
assume the relation is such only when needed.\<close>

subsection \<open>Consistent Edge Sequences, Sub-paths\<close>

subsubsection \<open>Consistency in presence of a subsumption relation\<close>

text \<open>We model sub-paths in the same spirit than in \verb?Graph.thy?, by starting with 
defining the consistency of a sequence of edges wrt.\ a subsumption relation. The idea is 
that subsumption links can ``fill the gaps'' between subsequent edges that would have made 
the sequence inconsistent otherwise. For now, we define consistency of a sequence wrt.\ any 
subsumption relation. Thus, we cannot account yet for the fact that we only consider relations 
without chains of subsumptions. The empty sequence is consistent wrt.\ to a subsumption relation 
from @{term "v1"} to @{term "v2"} if these two vertices are equal or if they belong to the 
transitive closure of the relation. A non-empty sequence is consistent if it is made of consistent 
sequences whose extremities are linked in the transitive closure of the subsumption relation.\<close>


fun ces :: "('v \<times> nat) \<Rightarrow> ('v \<times> nat) edge list \<Rightarrow> ('v \<times> nat) \<Rightarrow> 'v sub_rel_t \<Rightarrow> bool" where
  "ces v1 [] v2 subs = (v1 = v2  \<or> (v1,v2) \<in> subs\<^sup>+)"
| "ces v1 (e#es) v2 subs = ((v1 = src e \<or> (v1,src e) \<in> subs\<^sup>+) \<and> ces (tgt e) es v2 subs)"


text \<open>A consistent sequence from @{term "v1"} to @{term "v2"} without a  subsumption relation is 
consistent between these two vertices in presence of any relation.\<close>


lemma
  assumes "Graph.ces v1 es v2"
  shows   "ces v1 es v2 subs"
using assms by (induct es arbitrary : v1, auto)


text \<open>Consistency in presence of the empty subsumption relation reduces to consistency as defined 
in \verb?Graph.thy?.\<close>


lemma
  assumes "ces v1 es v2 {}"
  shows   "Graph.ces v1 es v2"
using assms by (induct es arbitrary : v1, auto)


text \<open>Let @{term "(v1,v2)"} be an element of a subsumption relation, and @{term "es"} a sequence of 
edges consistent wrt.\ this relation from vertex @{term "v2"}. Then @{term "es"} is also consistent 
from @{term "v1"}. Even if this lemma will not be used much in the following, this is the base fact 
for saying that paths feasible from a subsumee are also feasible from its subsumer.\<close>


lemma acas_imp_dcas :
  assumes "(v1,v2) \<in> subs"
  assumes "ces v2 es v subs"
  shows   "ces v1 es v subs"
using assms by (cases es, simp_all) (intro disjI2, force)+


text \<open>Let @{term "es"} be a sequence of edges consistent wrt. a subsumption relation. Extending 
this relation preserves the consistency of @{term "es"}.\<close>


lemma ces_Un :
  assumes "ces v1 es v2  subs1"
  shows   "ces v1 es v2 (subs1 \<union> subs2)"
using assms by (induct es arbitrary : v1, auto simp add : trancl_mono)


text \<open>A rephrasing of the previous lemma.\<close>


lemma cas_subset :
  assumes "ces v1 es v2  subs1"
  assumes "subs1 \<subseteq> subs2"
  shows   "ces v1 es v2 subs2"
using assms by (induct es arbitrary : v1, auto simp add : trancl_mono)


text \<open>Simplification lemmas for @{term "ces"}.\<close>


lemma ces_append_one :
  "ces v1 (es @ [e]) v2 subs = (ces v1 es (src e) subs \<and> ces (src e) [e] v2 subs)"
by (induct es arbitrary : v1, auto)


lemma ces_append :
  "ces v1 (es1 @ es2) v2 subs = (\<exists> v. ces v1 es1 v subs \<and> ces v es2 v2 subs)"
proof (intro iffI, goal_cases)
  case 1 thus ?case 
  by (induct es1 arbitrary : v1)  
     (simp_all del : split_paired_Ex, blast)
next
  case 2 thus ?case
  proof (induct es1 arbitrary : v1)
    case (Nil v1)

    then obtain v where "ces v1 [] v subs" 
                  and   "ces v es2 v2 subs" 
    by blast

    thus ?case
    unfolding ces.simps
    proof (elim disjE, goal_cases)
      case 1 thus ?case by simp
    next
      case 2 thus ?case by (cases es2) (simp, intro disjI2, fastforce)+
    qed
  next
    case Cons thus ?case by auto
  qed
qed


text \<open>Let @{term "es"} be a sequence of edges consistent from @{term "v1"} to @{term "v2"} wrt.\ a 
sub-relation @{term "subs"} of a graph @{term "g"}. Suppose elements of this sequence are edges of 
@{term "g"}. If @{term "v1"} is a vertex of @{term "g"} then @{term "v2"} is also a vertex of 
@{term "g"}.\<close>


lemma (in sub_rel_of) ces_imp_ends_vertices :
  assumes "ces v1 es v2 subs"
  assumes "set es \<subseteq> edges g"
  assumes "v1 \<in> Graph.vertices g"
  shows   "v2 \<in> Graph.vertices g"
using assms trancl_sub_rel_of 
unfolding sub_rel_of_def subsumers_conv vertices_def
by (induct es arbitrary : v1) (force, (simp del : split_paired_Ex, fast))


subsubsection \<open>Sub-paths\<close>

text \<open>A sub-path leading from @{term "v1"} to @{term "v2"}, two vertices of a graph @{term "g"} 
equipped with a subsumption relation @{term "subs"}, is a sequence of edges consistent wrt.\ 
@{term "subs"} from @{term "v1"} to @{term "v2"} whose elements are edges of @{term "g"}. 
Moreover, we must assume that @{term "subs"} is a sub-relation of @{term "g"}, otherwise 
@{term "es"} could ``exit'' @{term "g"} through subsumption links.\<close>


definition subpath :: 
  "(('v \<times> nat),'x) rgraph_scheme \<Rightarrow> ('v \<times> nat) \<Rightarrow> ('v \<times> nat) edge list \<Rightarrow> ('v \<times> nat) \<Rightarrow> (('v \<times> nat) \<times> ('v \<times> nat)) set \<Rightarrow> bool" 
where
  "subpath g v1 es v2 subs \<equiv> sub_rel_of g subs 
                           \<and> v1 \<in> Graph.vertices g
                           \<and> ces v1 es v2 subs  
                           \<and> set es \<subseteq> edges g"


text \<open>Once again, in some cases, we will not be interested in the ending vertex of a sub-path.\<close>


abbreviation subpath_from ::
  "(('v \<times> nat),'x) rgraph_scheme \<Rightarrow> ('v \<times> nat) \<Rightarrow> ('v \<times> nat) edge list \<Rightarrow> 'v sub_rel_t \<Rightarrow> bool"
where
  "subpath_from g v es subs \<equiv> \<exists> v'. subpath g v es v' subs"


text \<open>Simplification lemmas for @{term subpath}.\<close>


lemma Nil_sp :
  "subpath g v1 [] v2 subs \<longleftrightarrow> sub_rel_of g subs 
                             \<and> v1 \<in> Graph.vertices g 
                             \<and> (v1 = v2 \<or> (v1,v2) \<in> subs\<^sup>+)"
by (auto simp add : subpath_def)


text \<open>When the subsumption relation is well-formed (denoted by \<open>(in wf_sub_rel)\<close>), 
there is no need to account for the transitive closure of the relation.\<close>


lemma (in wf_sub_rel) Nil_sp :
  "subpath g v1 [] v2 subs \<longleftrightarrow> sub_rel_of g subs 
                             \<and> v1 \<in> Graph.vertices g 
                             \<and> (v1 = v2 \<or> (v1,v2) \<in> subs)"
using trancl_eq by (simp add : Nil_sp)


text \<open>Simplification lemma for the one-element sequence.\<close>


lemma sp_one :
  shows   "subpath g v1 [e] v2 subs \<longleftrightarrow> sub_rel_of g subs 
                                      \<and> (v1 = src e \<or> (v1,src e) \<in> subs\<^sup>+) 
                                      \<and> e \<in> edges g 
                                      \<and> (tgt e = v2 \<or> (tgt e,v2) \<in> subs\<^sup>+)"
using sub_rel_of.trancl_sub_rel_of[of g subs]
by (intro iffI, auto simp add : vertices_def sub_rel_of_def subpath_def) 


text \<open>Once again, when the subsumption relation is well-formed, the previous lemma can be 
simplified since, in this case, the transitive closure of the relation is the relation itself.\<close>


lemma (in wf_sub_rel_of) sp_one :
  shows "subpath g v1 [e] v2 subs \<longleftrightarrow> sub_rel_of g subs 
                                    \<and> (v1 = src e \<or> (v1,src e) \<in> subs) 
                                    \<and> e \<in> edges g 
                                    \<and> (tgt e = v2 \<or> (tgt e,v2) \<in> subs)"
using sp_one wf_sub_rel.trancl_eq[OF wf_sub_rel] by fast


text \<open>Simplification lemma for the non-empty sequence (which might contain more than one element).\<close>


lemma sp_Cons :
  shows   "subpath g v1 (e # es) v2 subs \<longleftrightarrow> sub_rel_of g subs 
                                           \<and> (v1 = src e  \<or> (v1,src e) \<in> subs\<^sup>+) 
                                           \<and> e \<in> edges g 
                                           \<and> subpath g (tgt e) es v2 subs"
using sub_rel_of.trancl_sub_rel_of[of g subs] 
by (intro iffI, auto simp add : subpath_def vertices_def sub_rel_of_def)


text \<open>The same lemma when the subsumption relation is well-formed.\<close>


lemma (in wf_sub_rel_of) sp_Cons :
  "subpath g v1 (e # es) v2 subs \<longleftrightarrow> sub_rel_of g subs 
                                   \<and> (v1 = src e \<or> (v1,src e) \<in> subs) 
                                   \<and> e \<in> edges g 
                                   \<and> subpath g (tgt e) es v2 subs"
using sp_Cons wf_sub_rel.trancl_eq[OF wf_sub_rel] by fast


text \<open>Simplification lemma for @{term "subpath"} when the sequence is known to end by a given 
edge.\<close>


lemma sp_append_one :
  "subpath g v1 (es @ [e]) v2 subs \<longleftrightarrow> subpath g v1 es (src e) subs 
                                     \<and> e \<in> edges g  
                                     \<and> (tgt e = v2 \<or> (tgt e, v2) \<in> subs\<^sup>+)"
unfolding subpath_def by (auto simp add :  ces_append_one)


text \<open>Simpler version in the case of a well-formed subsumption relation.\<close>


lemma (in wf_sub_rel) sp_append_one :
  "subpath g v1 (es @ [e]) v2 subs \<longleftrightarrow> subpath g v1 es (src e) subs 
                                     \<and> e \<in> edges g  
                                     \<and> (tgt e = v2 \<or> (tgt e, v2) \<in> subs)"
using sp_append_one in_trancl_imp by fast


text \<open>Simplification lemma when the sequence is known to be the concatenation of two 
sub-sequences.\<close>


lemma sp_append :
  "subpath g v1 (es1 @ es2) v2 subs \<longleftrightarrow> 
   (\<exists> v. subpath g v1 es1 v subs \<and> subpath g v es2 v2 subs)"
proof (intro iffI, goal_cases)
  case 1 thus ?case 
  using sub_rel_of.ces_imp_ends_vertices 
  by (simp add : subpath_def ces_append) blast
next
  case 2 thus ?case 
  unfolding subpath_def 
  by (simp only : ces_append) fastforce
qed


text \<open>Let @{term "es"} be a sub-path of a graph @{term "g"} starting at vertex @{term "v1"}. 
By definition of @{term "subpath"}, @{term "v1"} is a vertex of @{term "g"}. Even if this is a 
direct consequence of the definition of @{term "subpath"}, this lemma will ease the proofs of some 
goals in the following.\<close>


lemma fst_of_sp_is_vert :
  assumes "subpath g v1 es v2 subs"
  shows   "v1 \<in> Graph.vertices g"
using assms by (simp add : subpath_def)


text \<open>The same property (which also follows the definition of @{term "subpath"}, but not as 
trivially as the previous lemma) can be established for the final vertex @{term "v2"}.\<close>


lemma lst_of_sp_is_vert :
  assumes "subpath g v1 es v2 subs"
  shows   "v2 \<in> Graph.vertices g"
using assms sub_rel_of.trancl_sub_rel_of[of g subs]
by (induction es arbitrary : v1) 
   (force simp add : subpath_def sub_rel_of_def, (simp add : sp_Cons, fast))


text \<open>A sub-path ending in a subsumed vertex can be extended to the subsumer of this vertex, 
provided that the subsumption relation is a sub-relation of the graph it equips.\<close>


lemma sp_append_sub :
  assumes "subpath g v1 es v2 subs"
  assumes "(v2,v3) \<in> subs"
  shows   "subpath g v1 es v3 subs"
proof (cases es)
  case Nil

  moreover
  hence "v1 \<in> Graph.vertices g" 
  and   "v1 = v2 \<or> (v1,v2) \<in> subs\<^sup>+" 
  using assms(1) by (simp_all add : Nil_sp)

  ultimately
  show ?thesis 
  using assms(1,2) 
        Nil_sp[of g v1 v2 subs] 
        trancl_into_trancl[of v1 v2 subs v3] 
  by (auto simp add : subpath_def)
next
  case Cons

  then obtain es' e where "es = es' @ [e]" using neq_Nil_conv2[of es] by blast

  thus ?thesis using assms trancl_into_trancl by (simp add : sp_append_one) fast
qed


text \<open>Let @{term "g"} be a graph equipped with a well-formed sub-relation. A sub-path starting at 
a subsumed vertex @{term "v1"} whose set of out-edges is empty is either:
\begin{enumerate}
  \item empty,
  \item a sub-path starting at the subsumer @{term "v2"} of @{term "v1"}.
\end{enumerate}
The third assumption represent the fact that, when building red-black graphs, we do not allow to 
build the successor of a subsumed vertex.\<close>


lemma (in wf_sub_rel_of) sp_from_subsumee :
  assumes "(v1,v2) \<in> subs"
  assumes "subpath g v1 es v subs"
  assumes "out_edges g v1 = {}"               
  shows   "es = [] \<or> subpath g v2 es v subs"
using assms
      wf_sub_rel.subsumed_by_two_imp[OF wf_sub_rel assms(1)] 
by (cases es) 
   (fast, (intro disjI2, fastforce simp add : sp_Cons))


text \<open>Note that it is not possible to split this lemma into two lemmas (one for each member of the 
disjunctive conclusion). Suppose @{term "v"} is @{term "v1"}, then 
@{term "es"} could be empty or it could also be a non-empty sub-path leading from @{term "v2"} to 
@{term "v1"}. If @{term "v"} is not @{term "v1"}, it could be @{term "v2"} and @{term "es"} could 
be empty or not.\<close>


text \<open>A sub-path starting at a non-subsumed vertex whose set of out-edges is empty is also empty.\<close>


lemma sp_from_de_empty :
  assumes "v1 \<notin> subsumees subs"
  assumes "out_edges g v1 = {}"
  assumes "subpath g v1 es v2 subs"
  shows   "es = []"
using assms tranclD by (cases es) (auto simp add : sp_Cons, force)


text \<open>Let @{term "e"} be an edge whose target is not subsumed and has not out-going edges. A 
sub-path @{term "es"} containing @{term "e"} ends by @{term "e"} and this occurrence of @{term "e"} 
is unique along @{term "es"}.\<close>


lemma sp_through_de_decomp :
  assumes "tgt e \<notin> subsumees subs"
  assumes "out_edges g (tgt e) = {}"
  assumes "subpath g v1 es v2 subs"
  assumes "e \<in> set es"
  shows   "\<exists> es'. es = es' @ [e] \<and> e \<notin> set es'"
using assms(3,4)
proof (induction es arbitrary : v1)
  case (Nil v1) thus ?case by simp
next
  case (Cons e' es v1)

  hence "subpath g (tgt e') es v2 subs" 
  and  "e = e' \<or> (e \<noteq> e' \<and> e \<in> set es)" by (auto simp add : sp_Cons)

  thus ?case 
  proof (elim disjE, goal_cases)
    case 1 thus ?case 
    using sp_from_de_empty[OF assms(1,2)] by fastforce
  next
    case 2 thus ?case using Cons(1)[of "tgt e'"] by force
  qed
qed


text \<open>Consider a sub-path ending at the target of a recently added edge @{term "e"}, whose target 
did not belong to the graph prior to its addition. If @{term "es"} starts in another vertex than 
the target of @{term "e"}, then it contains @{term "e"}.\<close>


lemma (in sub_rel_of) sp_ends_in_tgt_imp_mem :
  assumes "tgt e \<notin> Graph.vertices g"
  assumes "v \<noteq> tgt e"
  assumes "subpath (add_edge g e) v es (tgt e) subs"
  shows   "e \<in> set es"
proof -
  have "tgt e \<notin> subsumers subs" using assms(1) sub_rel_of by auto

  hence "(v,tgt e) \<notin> subs\<^sup>+" using tranclD2 by force

  hence "es \<noteq> []" using assms(2,3) by (auto simp add : Nil_sp)

  then obtain es' e' where "es = es' @ [e']" by (simp add : neq_Nil_conv2) blast

  moreover
  hence "e' \<in> edges (add_edge g e)" using assms(3) by (auto simp add: subpath_def)
  
  moreover
  have "tgt e' = tgt e"  
  using tranclD2 assms(3) \<open>tgt e \<notin> subsumers subs\<close> \<open>es = es' @ [e']\<close>
  by (force simp add : sp_append_one)
  
  ultimately
  show ?thesis using assms(1) unfolding vertices_def image_def by force
qed

end
