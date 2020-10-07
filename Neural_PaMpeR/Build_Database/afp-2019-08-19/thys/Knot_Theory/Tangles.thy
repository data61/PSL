section\<open>Tangles: Definition as a type and basic functions on tangles\<close>
theory Tangles 
imports Preliminaries
begin


(* Time to split the file: Links and Tangles in another file*)

text\<open>well-defined wall as a type called diagram. The morphisms Abs\_diagram maps a well defined wall to 
its diagram type and Rep\_diagram maps the diagram back to the wall\<close>

typedef Tangle_Diagram = "{(x::wall). is_tangle_diagram x}"
 by (rule_tac x = "prod (cup#[]) (basic (cap#[]))" in exI) (auto)
 
typedef Link_Diagram = "{(x::wall). is_link_diagram x}"
 by (rule_tac x = "prod (cup#[]) (basic (cap#[]))" in exI) (auto simp 
 add:is_link_diagram_def abs_def)
 

text\<open>The next few lemmas list the properties of well defined diagrams\<close>

text\<open>For a well defined diagram, the morphism Rep\_diagram acts as an inverse of Abs\_diagram 
the morphism which maps a well defined wall to its representative in the type diagram\<close>

lemma Abs_Rep_well_defined: 
 assumes " is_tangle_diagram x" 
 shows "Rep_Tangle_Diagram (Abs_Tangle_Diagram x) = x"
 using Rep_Tangle_Diagram Abs_Tangle_Diagram_inverse assms mem_Collect_eq  by auto

text\<open>The map Abs\_diagram is injective\<close>
lemma Rep_Abs_well_defined: 
 assumes "is_tangle_diagram x"  
     and "is_tangle_diagram y" 
     and  "(Abs_Tangle_Diagram x) = (Abs_Tangle_Diagram y)"
 shows "x = y"
 using Rep_Tangle_Diagram Abs_Tangle_Diagram_inverse assms mem_Collect_eq  
 by metis

text\<open>restating the property of well-defined wall in terms of diagram\<close>

text\<open>In order to locally defined moves, it helps to prove that if composition of two wall is a 
well defined wall then the number of outgoing strands of the wall below are equal to the number of 
incoming strands of the wall above. The following lemmas prove that for a well defined wall, t
he number of incoming and outgoing strands are zero\<close>


(*is-tangle-compose*)
lemma is_tangle_left_compose: 
 "is_tangle_diagram (x \<circ> y) \<Longrightarrow> is_tangle_diagram x" 
proof (induct x)
 case (basic z)
  have "is_tangle_diagram (basic z)" using is_tangle_diagram.simps(1)  by auto
  then show ?case using basic by auto
 next
 case (prod z zs)
  have "(z*zs)\<circ>y = (z*(zs \<circ> y))" by auto
  then have " is_tangle_diagram (z*(zs\<circ>y))" using prod by auto
  moreover then have 1: "is_tangle_diagram zs" 
        using is_tangle_diagram.simps(2) prod.hyps prod.prems  by metis
  ultimately have "domain_wall (zs \<circ> y) = codomain_block z"
        by (metis is_tangle_diagram.simps(2))  
  moreover have "domain_wall (zs \<circ> y) = domain_wall zs" 
        using domain_wall_def domain_wall_compose by auto
  ultimately have "domain_wall zs = codomain_block z" by auto
  then have "is_tangle_diagram (z*zs)" 
        by (metis "1" is_tangle_diagram.simps(2))
  then show ?case by auto
qed

lemma is_tangle_right_compose: 
 "is_tangle_diagram (x \<circ> y) \<Longrightarrow> is_tangle_diagram y"
proof (induct x)
 case (basic z)
  have "(basic z) \<circ> y = (z*y) " using basic  by auto
  then have "is_tangle_diagram y" 
         unfolding is_tangle_diagram.simps(2) using basic.prems by (metis is_tangle_diagram.simps(2))
  then show ?case using basic.prems by auto 
 next
 case (prod z zs)
  have "((z*zs) \<circ> y) = (z *(zs \<circ> y))" by auto
  then have "is_tangle_diagram (z*(zs \<circ> y))" using prod by auto
  then have "is_tangle_diagram (zs \<circ> y)" using is_tangle_diagram.simps(2) by metis
  then have "is_tangle_diagram y"  using prod.hyps by auto 
  then show ?case by auto
qed

(*tangle diagrams using composition*)

lemma comp_of_tangle_dgms: 
 assumes"is_tangle_diagram y" 
 shows "((is_tangle_diagram x)
         \<and>(codomain_wall x = domain_wall y)) 
              \<Longrightarrow> is_tangle_diagram (x \<circ> y)"
proof(induct x)
 case (basic z)
  have "codomain_block z = codomain_wall (basic z)" 
      using domain_wall_def by auto
  moreover have "(basic z)\<circ>y= z*y" 
      using compose_def by auto
  ultimately have "codomain_block z = domain_wall y" 
      using basic.prems by auto 
  moreover have "is_tangle_diagram y" 
      using assms by auto
  ultimately have "is_tangle_diagram (z*y)" 
      unfolding is_tangle_diagram_def by auto
   then show ?case by auto
 next
 case (prod z zs)
  have "is_tangle_diagram (z*zs)" 
       using prod.prems by metis 
  then have "codomain_block z = domain_wall zs" 
      using is_tangle_diagram.simps(2) prod.prems  by metis
  then have "codomain_block z = domain_wall (zs \<circ> y)" 
      using domain_wall.simps domain_wall_compose by auto 
  moreover have "is_tangle_diagram (zs \<circ> y)" 
      using prod.hyps by (metis codomain_wall.simps(2) is_tangle_diagram.simps(2) prod.prems)
  ultimately have "is_tangle_diagram (z*(zs \<circ> y))" 
     unfolding is_tangle_diagram_def by auto 
  then show ?case by auto
qed

lemma composition_of_tangle_diagrams:
 assumes "is_tangle_diagram x" 
     and "is_tangle_diagram y"
     and "(domain_wall y = codomain_wall x)"
 shows "is_tangle_diagram (x \<circ> y)"
 using comp_of_tangle_dgms using assms by auto
    

lemma converse_composition_of_tangle_diagrams:
  "is_tangle_diagram (x \<circ> y) \<Longrightarrow> (domain_wall y) = (codomain_wall x)"
proof(induct x)
 case (basic z)
  have "(basic z) \<circ> y = z * y" 
      using compose_def basic by auto 
  then have 
    "is_tangle_diagram ((basic z) \<circ> y) \<Longrightarrow> 
              (is_tangle_diagram y)\<and> (codomain_block z = domain_wall y)"
     using is_tangle_diagram.simps(2)  by (metis)
  then have "(codomain_block z) = (domain_wall y)" 
      using basic.prems by auto
  moreover have "codomain_wall (basic z) = codomain_block z"
      using domain_wall_compose by auto
  ultimately have "(codomain_wall (basic z)) = (domain_wall y)" 
      by auto
  then show ?case by simp
 next
 case (prod z zs)
  have "codomain_wall zs = domain_wall y" 
          using prod.hyps prod.prems 
          by (metis compose_Nil compose_leftassociativity is_tangle_right_compose)
  moreover have "codomain_wall zs = codomain_wall (z*zs)"
          using domain_wall_compose by auto
  ultimately show ?case by metis
qed

(*defining compose for diagrams*)

definition compose_Tangle::"Tangle_Diagram \<Rightarrow> Tangle_Diagram \<Rightarrow> Tangle_Diagram" 
                                                                     (infixl "\<circ>" 65)
 where
"compose_Tangle x y = Abs_Tangle_Diagram 
                                  ((Rep_Tangle_Diagram x) \<circ> (Rep_Tangle_Diagram y))"

theorem well_defined_compose: 
 assumes "is_tangle_diagram x" 
     and "is_tangle_diagram y"
     and "domain_wall x = codomain_wall y"
 shows "(Abs_Tangle_Diagram x) \<circ> (Abs_Tangle_Diagram y) 
                          = (Abs_Tangle_Diagram (x \<circ> y))"
 using  Abs_Tangle_Diagram_inverse assms(1) assms(2) compose_Tangle_def 
        mem_Collect_eq 
 by auto

(*defining domain and co-domain of tangles*)
definition domain_Tangle::"Tangle_Diagram \<Rightarrow> int"
where
"domain_Tangle x = domain_wall(Rep_Tangle_Diagram x)"

definition codomain_Tangle::"Tangle_Diagram \<Rightarrow> int"
where
"codomain_Tangle x = codomain_wall(Rep_Tangle_Diagram x)"

end
