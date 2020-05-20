(*File: PBIJ.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory PBIJ imports OBJ begin

subsection\<open>Partial bijections\<close>

text\<open>Partial bijections between locations will be used in the next
section to define indistinguishability of objects and heaps. We define
such bijections as sets of pairs which satisfy the obvious
condition.\<close>

type_synonym PBij = "(Location \<times> Location) set"
definition Pbij :: "PBij set"
where "Pbij = { \<beta> . \<forall> l1 l2 l3 l4. (l1,l2):\<beta> \<longrightarrow> (l3,l4):\<beta> \<longrightarrow> 
                              ((l1 = l3) = (l2 = l4))}"

text\<open>Domain and codomain are defined as expected.\<close>

definition Pbij_Dom::"PBij \<Rightarrow> (Location set)"
where "Pbij_Dom \<beta> = {l . \<exists> ll .(l,ll):\<beta>}"

definition Pbij_Rng::"PBij \<Rightarrow> (Location set)"
where "Pbij_Rng \<beta> = {ll . \<exists> l .(l,ll):\<beta>}"

text\<open>We also define the inverse operation, the composition, and a
test deciding when one bijection extends another.\<close>

definition Pbij_inverse::"PBij \<Rightarrow> PBij"
where "Pbij_inverse \<beta> = {(l,ll) . (ll,l):\<beta>}"
(*<*)
lemma Pbij_inverseI:"(l1,l2):\<beta> \<Longrightarrow> (l2,l1):Pbij_inverse \<beta>"
by (simp add: Pbij_inverse_def)
lemma Pbij_inverseD:"(l1,l2):Pbij_inverse \<beta> \<Longrightarrow> (l2,l1):\<beta>"
by (simp add: Pbij_inverse_def) 
(*>*)

definition Pbij_compose::"PBij \<Rightarrow> PBij \<Rightarrow> PBij"
where "Pbij_compose \<beta> \<gamma> = {(l,ll) . \<exists> l1 . (l,l1):\<beta> \<and> (l1,ll):\<gamma>}"
(*<*)
lemma Pbij_composeI: "\<lbrakk>(l1, l2) \<in> \<beta>; (l2, l3) \<in> \<gamma>\<rbrakk> \<Longrightarrow> (l1, l3) \<in> Pbij_compose \<beta> \<gamma>"
by (simp add: Pbij_compose_def, rule_tac x=l2 in exI, simp)
lemma Pbij_composeD: "(l1, l3) \<in> Pbij_compose \<beta> \<gamma> \<Longrightarrow> \<exists> l2 . (l1, l2) \<in> \<beta> \<and> (l2, l3) \<in> \<gamma>"
by (simp add: Pbij_compose_def)
(*>*)

definition Pbij_extends ::"PBij \<Rightarrow> PBij \<Rightarrow> bool"
where "Pbij_extends \<gamma> \<beta> = (\<beta> \<subseteq> \<gamma>)"

text\<open>These definitions satisfy the following properties.\<close>

lemma Pbij_insert:
  "\<lbrakk>\<beta> \<in> Pbij;l \<notin> Pbij_Rng \<beta>; ll \<notin> Pbij_Dom \<beta>\<rbrakk> 
  \<Longrightarrow> insert (ll, l) \<beta> \<in> Pbij"
(*<*)
apply (simp add: Pbij_def)
apply clarsimp
apply rule
  apply clarsimp apply (simp add: Pbij_Dom_def Pbij_Rng_def) apply fast
  apply clarsimp apply (simp add: Pbij_Dom_def Pbij_Rng_def) apply fast
done
(*>*)

lemma Pbij_injective:
  "\<beta>:Pbij \<Longrightarrow> (\<forall> l l1 l2 . (l1,l):\<beta> \<longrightarrow> (l2,l):\<beta> \<longrightarrow> l1=l2)"
(*<*)
by (simp add: Pbij_def)
(*>*)

lemma Pbij_inverse_DomRng[rule_format]:
  "\<gamma> = Pbij_inverse \<beta> \<Longrightarrow> 
   (Pbij_Dom \<beta> = Pbij_Rng \<gamma> \<and> Pbij_Dom \<gamma> = Pbij_Rng \<beta>)"
(*<*)
by (simp add: Pbij_inverse_def Pbij_Dom_def Pbij_Rng_def) 
(*>*)

lemma Pbij_inverse_Dom: "Pbij_Dom \<beta> = Pbij_Rng (Pbij_inverse \<beta>)"
(*<*)
by (simp add: Pbij_inverse_def Pbij_Dom_def Pbij_Rng_def) 
(*>*)

lemma Pbij_inverse_Rng: "Pbij_Dom (Pbij_inverse \<beta>) = Pbij_Rng \<beta>"
(*<*)
by (simp add: Pbij_inverse_def Pbij_Dom_def Pbij_Rng_def) 
(*>*)

lemma Pbij_inverse_Pbij: "\<beta>:Pbij \<Longrightarrow> (Pbij_inverse \<beta>) : Pbij"
(*<*)
by (simp add: Pbij_def Pbij_inverse_def)
(*>*)

lemma Pbij_inverse_Inverse[rule_format]:
  "\<gamma> = Pbij_inverse \<beta> \<Longrightarrow> (\<forall> l ll . ((l,ll):\<beta>) = ((ll,l):\<gamma>))"
(*<*)
by (simp add: Pbij_inverse_def)
(*>*)

lemma Pbij_compose_Dom:
  "Pbij_Dom (Pbij_compose \<beta> \<gamma>) \<subseteq> Pbij_Dom \<beta>"
(*<*)
by (simp add: Pbij_compose_def Pbij_Dom_def, fast)
(*>*)

lemma Pbij_compose_Rng:
  "Pbij_Rng (Pbij_compose \<beta> \<gamma>) \<subseteq> Pbij_Rng \<gamma>"
(*<*)
by (simp add: Pbij_compose_def Pbij_Rng_def, fast)
(*>*)

lemma Pbij_compose_Pbij: 
  "\<lbrakk>\<beta> : Pbij; \<gamma> : Pbij\<rbrakk> \<Longrightarrow> Pbij_compose \<beta> \<gamma> : Pbij"
(*<*)
by (simp add: Pbij_compose_def Pbij_def, clarsimp)
(*>*)

lemma Pbij_extends_inverse: 
 "Pbij_extends \<gamma> (Pbij_inverse \<beta>) = Pbij_extends (Pbij_inverse \<gamma>) \<beta>"
(*<*)
by (simp add: Pbij_extends_def Pbij_inverse_def, fast)
(*>*)

lemma Pbij_extends_reflexive:"Pbij_extends \<beta> \<beta>"
(*<*)
by (simp add: Pbij_extends_def)
(*>*)

lemma Pbij_extends_transitive:
"\<lbrakk>Pbij_extends \<beta> \<gamma>; Pbij_extends \<gamma> \<delta>\<rbrakk> \<Longrightarrow> Pbij_extends \<beta> \<delta>"
(*<*)
by (simp add: Pbij_extends_def)
(*>*)

(*<*)
lemma Pbij_inverse_extends_twice_Aux:
"\<lbrakk> \<delta> = Pbij_inverse \<epsilon>; Pbij_extends \<epsilon> \<gamma>; \<gamma> = Pbij_inverse  \<beta>\<rbrakk>
 \<Longrightarrow> Pbij_extends \<delta> \<beta>"
by (simp add: Pbij_extends_def Pbij_inverse_def, fastforce) 
(*>*)

lemma Pbij_inverse_extends_twice:
" Pbij_extends (Pbij_inverse (Pbij_inverse \<beta>)) \<beta>"
(*<*)
by (simp add: Pbij_extends_def Pbij_inverse_def)
(*>*)

text\<open>The identity bijection on a heap associates each element of the
heap's domain with itself.\<close>

definition mkId::"Heap \<Rightarrow> (Location \<times> Location) set"
where "mkId h = {(l1,l2) . l1 = l2 \<and> l1 : Dom h}"

lemma mkId1: "(mkId h):Pbij"
(*<*)
by (simp add: mkId_def Pbij_def)
(*>*)

lemma mkId2: "Pbij_Dom (mkId h) = Dom h"
(*<*)
by (simp add: Dom_def Pbij_Dom_def mkId_def) 
(*>*)

lemma mkId2b: "Pbij_Rng (mkId h) = Dom h"
(*<*)
by (simp add: Dom_def Pbij_Rng_def mkId_def) 
(*>*)

lemma mkId4: "l:Dom h \<Longrightarrow> (l,l):(mkId h)"
(*<*)
by (simp add: mkId_def)
(*>*)

lemma mkId4b: "(l,ll):(mkId h) \<Longrightarrow> l:Dom h \<and> l = ll"
(*<*)
by (simp add: mkId_def, clarsimp)
(*>*)

text\<open>End of theory PBIJ\<close>
end
