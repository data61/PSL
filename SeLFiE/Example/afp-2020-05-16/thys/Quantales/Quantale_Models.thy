(* Title: Models of Quantales
   Author: Georg Struth
   Maintainer: Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Models of Quantales\<close>

theory Quantale_Models
  imports Quantales
  "Dioid_Models_New"

begin

text \<open>Most of the models in this section expand those of dioids (and hence Kleene algebras). They really belong here, 
because quantales form a stronger setting than dioids or Kleene algebras. They are, however, subsumed by the general lifting
results of partial semigroups and monoids from another AFP entry~\cite{DongolGHS17}.\<close>


subsection \<open>Quantales of Booleans\<close>

instantiation bool :: bool_ab_unital_quantale
begin
  
definition "one_bool = True"
  
definition "times_bool = (\<and>)"

instance
  by intro_classes (auto simp: times_bool_def one_bool_def)

end
  
lemma bool_sep_eq_conj [simp]: "((x :: bool) * y) = (x \<and> y)"
  by (auto simp: times_bool_def)
  
lemma bool_impl_eq [simp]: "(x :: bool) \<rightarrow> y = -x \<squnion> y"
  by (clarsimp simp: bres_def)
  
subsection \<open>Powerset Quantales of Semigroups and Monoids\<close>

instance set :: (semigroup_mult) quantale
  by intro_classes (auto simp: times_set_def)

text \<open>With the definition of products on powersets (from the component of models of dioids) one
can prove the following mixed distributivity law.\<close>

lemma comp_dist_mix: "\<Squnion>(X::'a::quantale set) \<cdot> \<Squnion>Y = \<Squnion>(X \<cdot> Y)"
proof-
  have "\<Squnion>X \<cdot> \<Squnion>Y = (\<Squnion>x \<in> X. \<Squnion>y \<in> Y. x \<cdot> y)"
    by (metis (no_types, lifting) SUP_cong Sup_distl Sup_distr)
  also have "... = \<Squnion>{\<Squnion>{x \<cdot> y|y. y \<in> Y} |x. x \<in> X}"
    by (simp add: setcompr_eq_image)
  also have "... = \<Squnion>{x \<cdot> y |x y. x \<in> X \<and> y \<in> Y}"
    apply (rule antisym)
     apply (rule Sup_least, smt Collect_mono Sup_subset_mono mem_Collect_eq)
    by (rule Sup_least, smt Sup_upper calculation mem_Collect_eq psrpq.mult_isol_var)
  finally show ?thesis
    by (simp add: times_set_def)
qed

text \<open>Powerset quantales of monoids can nevertheless be formalised as instances.\<close>

instance set :: (monoid_mult) unital_quantale..


text \<open>There is much more to this example. In fact, every quantale can be represented, up to isomorphism, 
as a certain quotient of a powerset quantale over some semigroup~\cite{Rosenthal90}. This representation theorem is 
formalised in the section on nuclei.\<close>


subsection \<open>Language, Relation, Trace and Path Quantales\<close>

text \<open>The language quantale is implcit in the powerset quantale over a semigroup or monoid. The free list monoid has
already been linked with the class of monoid as an instance in Isabelle's dioid components~\cite{ArmstrongSW13}. I provide an alternative
interpretation. In all of the following locale statements, an interpretation for Sup-quantales fails, due to the occurance of some low level
less operations in the underlying model...\<close>

interpretation lan_quantale: unital_quantale "1::'a lan" "(\<cdot>)" Inf Sup inf "(\<subseteq>)" "(\<subset>)" sup "0" UNIV
  by unfold_locales (simp_all add: Inf_lower Inter_greatest Sup_upper Sup_least zero_set_def Sup_distr Sup_distl)

text \<open>The relation quantale follows.\<close>

interpretation rel_quantale: unital_quantale Id relcomp Inf Sup inf "(\<subseteq>)" "(\<subset>)" sup "{}" "UNIV"
  by (unfold_locales, auto) 

text \<open>Traces alternate between state and action symbols, the first and last symbol of a trace being state symbols.
They can be associated with behaviours of automata or executions of programs.\<close>

interpretation trace_quantale: unital_quantale t_one t_prod Inf Sup inf "(\<subseteq>)" "(\<subset>)" sup t_zero UNIV
  by unfold_locales (auto simp: Inf_lower Inf_greatest Sup_upper Sup_least t_zero_def t_prod_def t_fusion_def)

text \<open>The final model corresponds to paths as sequences of states of an automata, transition system or graph.\<close>

interpretation path_quantale: unital_quantale p_one p_prod Inter Union "(\<inter>)" "(\<subseteq>)" "(\<subset>)" "(\<union>)" "{}" UNIV
  by unfold_locales (auto simp: p_prod_def)

text \<open>Rosenthal's book contains a wealth of other examples. Many of them come from ring theory 
(e.g. the additive subgroups of a ring form a quantale and so do the left, right and two-sided ideals). Others are based
on the interval $[0,\infty]$. The first line of models was the original motivation for the study of quantales, the second 
one is important to Lawvere's categorical generalisation of metric spaces. These examples are left for future consideration.\<close>

end  

    


  

