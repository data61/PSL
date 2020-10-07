theory SubExt
imports SubRel
begin

section \<open>Extending subsomption relations\<close>

text \<open>In this section, we are interested in the evolution of the set of sub-paths of a rooted 
graph equipped with a subsumption relation after adding a subsumption to this relation. We are 
only interested in adding subsumptions such that the resulting relation is a well-formed 
sub-relation of the graph (provided the original relation was such). As
for the extension 
by edges, a number of side conditions must be met for the new subsumption to be added.\<close>

subsection \<open>Definition\<close>

text \<open>Extending a subsumption relation @{term subs} consists in adding a subsumption @{term "sub"} 
such that:
\begin{itemize}
  \item the two vertices involved are distinct,
  \item they are occurrences of the same vertex,
  \item they are both vertices of the graph,
  \item the subsumee must not already be a subsumer or a subsumee,
  \item the subsumer must not be a subsumee (but it can already be a subsumer),
  \item the subsumee must have no out-edges.
\end{itemize}\<close>

text \<open>Once again, in order to ease proofs, we use a predicate stating when a 
subsumpion relation is the extension of another instead of using a function that would produce the 
extension.\<close>

abbreviation extends ::
  "(('v \<times> nat),'x) rgraph_scheme \<Rightarrow> 'v sub_rel_t \<Rightarrow> 'v sub_t \<Rightarrow> 'v sub_rel_t \<Rightarrow> bool"
where
  "extends g subs sub subs' \<equiv> (
     subsumee sub \<noteq> subsumer sub              
   \<and> fst (subsumee sub)  = fst (subsumer sub)  
   \<and> subsumee sub \<in> Graph.vertices g
   \<and> subsumee sub \<notin> subsumers subs
   \<and> subsumee sub \<notin> subsumees subs
   \<and> subsumer sub \<in> Graph.vertices g
   \<and> subsumer sub \<notin> subsumees subs
   \<and> out_edges g (subsumee sub) = {}
   \<and> subs' = subs \<union> {sub})"


subsection \<open>Properties of extensions\<close>

text \<open>First, we show that such extensions yield sub-relations (resp.\ well-formed relations), 
provided the original relation is a sub-relation (resp.\ well-formed relation).\<close>


text \<open>Extending the sub-relation of a graph yields a new sub-relation for this graph.\<close>

lemma (in sub_rel_of)
  assumes "extends g subs sub subs'" 
  shows   "sub_rel_of g subs'"
using assms sub_rel_of unfolding sub_rel_of_def by force


text \<open>Extending a well-formed relation yields a well-formed relation.\<close>

lemma (in wf_sub_rel) extends_imp_wf_sub_rel :
  assumes "extends g subs sub subs'"
  shows   "wf_sub_rel subs'"
unfolding wf_sub_rel_def
proof (intro conjI, goal_cases)
  case 1 show ?case using wf_sub_rel assms by auto
next
  case 2 show ?case
  unfolding Ball_def
  proof (intro allI impI)
    fix v

    assume "v \<in> subsumees subs'" 

    hence  "v = subsumee sub \<or> v \<in> subsumees subs" using assms by auto

    thus "\<exists>! v'. (v,v') \<in> subs'"
    proof (elim disjE, goal_cases)
      case 1 show ?thesis
      unfolding Ex1_def
      proof (rule_tac ?x="subsumer sub" in exI, intro conjI)
        show "(v, subsumer sub) \<in> subs'" using 1 assms by simp
      next
        have "v \<notin> subsumees subs" using assms 1 by auto
        
        thus "\<forall> v'. (v, v') \<in> subs' \<longrightarrow> v' = subsumer sub" 
        using assms by auto force
      qed
    next
      case 2

      then obtain v' where "(v,v') \<in> subs" by auto

      hence "v \<noteq> subsumee sub"
      using assms unfolding subsumees_conv by (force simp del : split_paired_All split_paired_Ex)
 
      show ?thesis 
      using assms 
            \<open>v \<noteq> subsumee sub\<close> 
            \<open>(v,v') \<in> subs\<close> subsumed_by_one 
      unfolding subsumees_conv Ex1_def
      by (rule_tac ?x="v'" in exI) 
         (auto simp del : split_paired_All split_paired_Ex)
    qed
  qed
next
  case 3 show ?case using wf_sub_rel assms by auto
qed



text \<open>Thus, extending a well-formed sub-relation yields a well-formed sub-relation.\<close> 

lemma (in wf_sub_rel_of) extends_imp_wf_sub_rel_of :
  assumes "extends g subs sub subs'"
  shows   "wf_sub_rel_of g subs'"
using sub_rel_of assms
      wf_sub_rel.extends_imp_wf_sub_rel[OF wf_sub_rel assms]
by (simp add : wf_sub_rel_of_def sub_rel_of_def)




subsection \<open>Properties of sub-paths in an extension\<close>

text \<open>Extending a sub-relation of a graph preserves the existing sub-paths.\<close>

lemma sp_in_extends :
  assumes "extends g subs sub subs'"
  assumes "subpath g v1 es v2 subs"
  shows   "subpath g v1 es v2 subs'"
using assms ces_Un[of v1 es v2 subs "{sub}"]
by (simp add : subpath_def sub_rel_of_def) 

text \<open>We want to describe how the addition of a subsumption modifies the set of sub-paths in the 
graph. As in the previous theories, we will focus on a small number of theorems expressing 
sub-paths in extensions as functions of sub-paths in the graphs before extending them (their 
subsumption relations). 
We first express sub-paths starting at the subsumee of the new subsumption, then the sub-paths 
starting at any other vertex.\<close>

text \<open>First, we are interested in sub-paths starting at the subsumee of the new subsumption. Since 
such vertices have no out-edges, these sub-paths must be either empty or must  be sub-paths from 
the subsumer of this subsumption.\<close>


lemma (in wf_sub_rel_of) sp_in_extends_imp1 :
  assumes "extends g subs (v1,v2) subs'"
  assumes "subpath g v1 es v subs'"
  shows   "es = [] \<or> subpath g v2 es v subs'"
using assms
      extends_imp_wf_sub_rel_of[OF assms(1)]
      wf_sub_rel_of.sp_from_subsumee[of g subs' v1 v2 es v]
by simp


text \<open>After an extension, sub-paths starting at any other vertex than the new subsumee are either:
\begin{itemize}
  \item sub-paths of the graph before the extension if they do not ``use'' the new subsumption,
  \item made of a finite number of sub-paths of the graph before the extension if they use the 
new subsumption.
\end{itemize}
In order to state the lemmas expressing these facts, we first need to introduce the concept of 
\emph{usage} of a subsumption by a sub-path.\<close>

text \<open>The idea is that, if a sequence of edges that uses a subsumption @{term sub} is consistent 
wrt.\ a subsumption relation @{term subs}, then @{term sub} must occur in the transitive closure 
of @{term subs} i.e.\ the consistency of the sequence directly (and partially) depends on 
@{term sub}. In the case of well-formed subsumption relations, whose transitive 
closures equal the relations themselves, the dependency of the consistency reduces to the fact that 
@{term sub} is a member of @{term subs}.\<close>

fun uses_sub :: 
  "('v \<times> nat) \<Rightarrow> ('v \<times> nat) edge list \<Rightarrow> ('v \<times> nat) \<Rightarrow> (('v \<times> nat) \<times> ('v \<times> nat)) \<Rightarrow> bool"
where
  "uses_sub v1 [] v2 sub     = (v1 \<noteq> v2 \<and> sub = (v1,v2))"
| "uses_sub v1 (e#es) v2 sub = (v1 \<noteq> src e \<and> sub = (v1,src e) \<or> uses_sub (tgt e) es v2 sub)"


text \<open>In order for a sequence @{term es} using the subsumption @{term sub} to be consistent wrt.\ 
to a subsumption relation @{term subs}, the subsumption @{term sub} must occur in the transitive 
closure of @{term subs}.\<close>

lemma
  assumes "uses_sub v1 es v2 sub"
  assumes "ces v1 es v2 subs"
  shows   "sub \<in> subs\<^sup>+"
using assms by (induction es arbitrary : v1) fastforce+


text \<open>This reduces to the membership of @{term sub} to @{term subs} when the latter is 
well-formed.\<close>


lemma (in wf_sub_rel)
  assumes "uses_sub v1 es v2 sub"
  assumes "ces v1 es v2 subs"
  shows   "sub \<in> subs"
using assms trancl_eq by (induction es arbitrary : v1) fastforce+



text \<open>Sub-paths prior to the extension do not use the new subsumption.\<close>

lemma extends_and_sp_imp_not_using_sub :
  assumes "extends g subs (v,v') subs'"
  assumes "subpath g v1 es v2 subs"
  shows   "\<not> uses_sub v1 es v2 (v,v')"  
proof (intro notI)
  assume "uses_sub v1 es v2 (v,v')"

  moreover
  have "ces v1 es v2 subs" using assms(2) by (simp add : subpath_def)

  ultimately
  have "(v,v') \<in> subs\<^sup>+" by (induction es arbitrary : v1) fastforce+

  thus False 
  using assms(1) unfolding subsumees_conv 
  by (elim conjE) (frule tranclD, force)
qed





text \<open>Suppose that the empty sequence is a sub-path leading from @{term v1} to @{term v2} after 
the extension. Then, the empty sequence is a sub-path leading from @{term v1} to @{term v2} 
in the graph before the extension if and only if @{term "(v1,v2)"} is not the new subsumption.\<close>

lemma (in wf_sub_rel_of) sp_Nil_in_extends_imp :
  assumes "extends g subs (v,v') subs'"
  assumes "subpath g v1 [] v2 subs'"
  shows   "subpath g v1 [] v2 subs \<longleftrightarrow> (v1 \<noteq> v \<or> v2 \<noteq> v')"
proof (intro iffI, goal_cases)
  case 1 thus ?case 
  using assms(1) 
        extends_and_sp_imp_not_using_sub[OF assms(1), of v1 "[]" v2] 
  by auto
next
  case 2

  have "v1 = v2 \<or> (v1,v2) \<in> subs'" 
  and  "v1 \<in> Graph.vertices g" 
  using assms(2) 
        wf_sub_rel.extends_imp_wf_sub_rel[OF wf_sub_rel assms(1)]
  by (simp_all add : wf_sub_rel.Nil_sp)
  
  moreover
  hence "v1 = v2 \<or> (v1,v2) \<in> subs"
  using assms(1) 2 by auto

  moreover
  have "v2 \<in> Graph.vertices g"
  using assms(2) by (intro lst_of_sp_is_vert)

  ultimately
  show "subpath g v1 [] v2 subs" 
  using sub_rel_of by (auto simp add : subpath_def)
qed


text \<open>Thus, sub-paths after the extension that do not use the new subsumption are also sub-paths 
before the extension.\<close>

lemma (in wf_sub_rel_of) sp_in_extends_not_using_sub :
  assumes "extends g subs (v,v') subs'"
  assumes "subpath g v1 es v2 subs'"
  assumes "\<not> uses_sub v1 es v2 (v,v')"
  shows   "subpath g v1 es v2 subs"
using sub_rel_of assms extends_imp_wf_sub_rel_of 
by (induction es arbitrary : v1) 
   (auto simp add : sp_Nil_in_extends_imp wf_sub_rel_of.sp_Cons sp_Cons)



text \<open>We are finally able to describe sub-paths starting at any other vertex than the new 
subsumee after the extension. Such sub-paths are made of a finite number of sub-paths before the 
extension: the usage of the new subsumption between such (sub-)sub-paths makes them sub-paths 
after the extension. We express this idea as follows. Sub-paths starting at any other vertex 
than the new subsumee are either: 
\begin{itemize}
  \item sub-paths of the graph before the extension,
  \item made of a non-empty prefix that is a sub-path leading to the new subsumee in the original 
graph and a (potentially empty) suffix that is a sub-path starting at the new subsumer after 
the extension.
\end{itemize}
For the second case, the lemma \verb?sp_in_extends_imp1? as well as the following lemma could be 
applied to the suffix in order to decompose it into sub-paths of the graph before extension 
(combined with the fact that we only consider finite sub-paths, we indirectly obtain that sub-paths 
after the extension are made of a finite number of sub-paths before the extension, that are made 
consistent with the new relation by using the new subsumption).\<close>

lemma (in wf_sub_rel_of) sp_in_extends_imp2 : 
  assumes "extends g subs (v,v') subs'"
  assumes "subpath g v1 es v2 subs'"
  assumes "v1 \<noteq> v"
 
  shows   "subpath g v1 es v2 subs \<or> (\<exists> es1 es2. es = es1 @ es2 
                                               \<and> es1 \<noteq> [] 
                                               \<and> subpath g v1 es1 v subs 
                                               \<and> subpath g v es2 v2 subs')"
          (is "?P es v1")
proof (case_tac "uses_sub v1 es v2 (v,v')", goal_cases)
  case 1

  thus ?thesis
  using assms(2,3)
  proof (induction es arbitrary : v1)
    case (Nil v1) thus ?case by auto
  next
    case (Cons edge es v1)

    hence "v1 = src edge \<or> (v1, src edge) \<in> subs'"
    and   "edge \<in> edges g" 
    and   "subpath g (tgt edge) es v2 subs'"
    using assms(1) extends_imp_wf_sub_rel_of 
    by (simp_all add : wf_sub_rel_of.sp_Cons)

    hence "subpath g v1 [edge] (tgt edge) subs'" 
    using  wf_sub_rel_of.sp_one[OF extends_imp_wf_sub_rel_of[OF assms(1)]]
    by (simp add : subpath_def) fast

    have "subpath g v1 [edge] (tgt edge) subs"
    proof -
      have "\<not> uses_sub v1 [edge] (tgt edge) (v,v')" 
      using assms(1) Cons(2,4) by auto

      thus ?thesis
      using assms(1) \<open>subpath g v1 [edge] (tgt edge) subs'\<close> 
      by (elim sp_in_extends_not_using_sub)
    qed

    thus ?case
    proof (case_tac "tgt edge = v", goal_cases)  
      case 1 thus ?thesis 
      using \<open>subpath g v1 [edge] (tgt edge) subs\<close>  
            \<open>subpath g (tgt edge) es v2 subs'\<close>
      by (intro disjI2, rule_tac ?x="[edge]" in exI) auto
    next
      case 2

      moreover
      have "uses_sub (tgt edge) es v2 (v,v')" using Cons(2,4) by simp

      ultimately
      have "?P es (tgt edge)" 
      using \<open>subpath g (tgt edge) es v2 subs'\<close> 
      by (intro Cons.IH)

      thus ?thesis
      proof (elim disjE exE conjE, goal_cases)
        case 1 thus ?thesis 
        using \<open>subpath g (tgt edge) es v2 subs'\<close> 
              \<open>uses_sub (tgt edge) es v2 (v,v')\<close> 
              extends_and_sp_imp_not_using_sub[OF assms(1)]
        by fast
      next
        case (2 es1 es2) thus ?thesis 
        using \<open>es = es1 @ es2\<close> 
              \<open>subpath g v1 [edge] (tgt edge) subs\<close> 
              \<open>subpath g v es2 v2 subs'\<close>
        by (intro disjI2, rule_tac ?x="edge # es1" in exI) (auto simp add : sp_Cons)
      qed
    qed 
  qed
next
  case 2 thus ?thesis 
  using assms(1,2) by (simp add : sp_in_extends_not_using_sub)
qed

end
