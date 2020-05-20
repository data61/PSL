section\<open>Link\_Algebra: Defining equivalence of tangles and links\<close>

theory Link_Algebra
imports Tangles Tangle_Algebra Tangle_Moves
begin

inductive Tangle_Equivalence :: "wall \<Rightarrow> wall  \<Rightarrow> bool"   (infixl "~" 64)
where
  refl [intro!, Pure.intro!, simp]: " a ~  a"
 |equality [Pure.intro]: "linkrel a b \<Longrightarrow>  a ~ b"
 |domain_compose:"(domain_wall a = 0)\<and>(is_tangle_diagram a) \<Longrightarrow>  a ~  ((basic [])\<circ>a)"
 |codomain_compose:"(codomain_wall a = 0) \<and> (is_tangle_diagram a) \<Longrightarrow> a ~ (a \<circ> (basic []))"
 |compose_eq:"((B::wall) ~ D) \<and> ((A::wall) ~ C)
         \<and>(is_tangle_diagram A)\<and>(is_tangle_diagram B)
         \<and>(is_tangle_diagram C)\<and>(is_tangle_diagram D) 
         \<and>(domain_wall B)= (codomain_wall A)
         \<and>(domain_wall D)= (codomain_wall C)
                \<Longrightarrow>((A::wall) \<circ> B) ~ (C \<circ> D)"
 |trans: "A~B \<Longrightarrow> B~C \<Longrightarrow> A ~ C"
 |sym:"A~ B \<Longrightarrow> B ~A"
 |tensor_eq: "((B::wall) ~ D) \<and> ((A::wall) ~ C) \<and>(is_tangle_diagram A)\<and>(is_tangle_diagram B)
 \<and>(is_tangle_diagram C)\<and>(is_tangle_diagram D) \<Longrightarrow>((A::wall) \<otimes> B) ~ (C \<otimes> D)" 


inductive Framed_Tangle_Equivalence :: "wall \<Rightarrow> wall  \<Rightarrow> bool"   (infixl "~f" 64)
where
  refl [intro!, Pure.intro!, simp]: " a ~f  a"
 |equality [Pure.intro]: "framed_linkrel a b \<Longrightarrow>  a ~f b"
 |domain_compose:"(domain_wall a = 0) \<and> (is_tangle_diagram a) \<Longrightarrow>  a ~f  ((basic [])\<circ>a)"
 |codomain_compose:"(codomain_wall a = 0) \<and> (is_tangle_diagram a) \<Longrightarrow> a ~f (a \<circ> (basic []))"
 |compose_eq:"((B::wall) ~f D) \<and> ((A::wall) ~f C)
         \<and>(is_tangle_diagram A)\<and>(is_tangle_diagram B)
         \<and>(is_tangle_diagram C)\<and>(is_tangle_diagram D) 
         \<and>(domain_wall B)= (codomain_wall A)
         \<and>(domain_wall D)= (codomain_wall C)
                \<Longrightarrow>((A::wall) \<circ> B) ~f (C \<circ> D)"
 |trans: "A~fB \<Longrightarrow> B~fC \<Longrightarrow> A ~f C"
 |sym:"A~f B \<Longrightarrow> B ~fA"
 |tensor_eq: "((B::wall) ~f D) \<and> ((A::wall) ~f C) \<and>(is_tangle_diagram A)\<and>(is_tangle_diagram B)
 \<and>(is_tangle_diagram C)\<and>(is_tangle_diagram D) \<Longrightarrow>((A::wall) \<otimes> B) ~f (C \<otimes> D)" 


definition Tangle_Diagram_Equivalence::"Tangle_Diagram \<Rightarrow> Tangle_Diagram \<Rightarrow> bool" 
 (infixl "~T" 64)
where
"Tangle_Diagram_Equivalence T1 T2 \<equiv> 
(Rep_Tangle_Diagram T1) ~ (Rep_Tangle_Diagram T2)"

definition Link_Diagram_Equivalence::"Link_Diagram \<Rightarrow> Link_Diagram \<Rightarrow> bool" 
 (infixl "~L" 64)
where
"Link_Diagram_Equivalence T1 T2 \<equiv> (Rep_Link_Diagram T1) ~ (Rep_Link_Diagram T2)"

quotient_type Tangle = "Tangle_Diagram"/"Tangle_Diagram_Equivalence"
morphisms Rep_Tangles Abs_Tangles
proof (rule equivpI)
 show "reflp Tangle_Diagram_Equivalence" 
         unfolding reflp_def Tangle_Diagram_Equivalence_def 
         Tangle_Equivalence.refl 
         by auto
 show "symp Tangle_Diagram_Equivalence" 
         unfolding Tangle_Diagram_Equivalence_def symp_def
         using  Tangle_Diagram_Equivalence_def Tangle_Equivalence.sym 
         by auto
 show "transp Tangle_Diagram_Equivalence"
         unfolding Tangle_Diagram_Equivalence_def transp_def
         using  Tangle_Diagram_Equivalence_def Tangle_Equivalence.trans 
         by metis
qed

quotient_type Link = "Link_Diagram"/"Link_Diagram_Equivalence"
morphisms Rep_Links Abs_Links
proof (rule equivpI)
 show "reflp Link_Diagram_Equivalence" 
         unfolding reflp_def Link_Diagram_Equivalence_def 
         Tangle_Equivalence.refl 
         by auto
 show "symp Link_Diagram_Equivalence" 
         unfolding Link_Diagram_Equivalence_def symp_def
         using  Link_Diagram_Equivalence_def  Tangle_Equivalence.sym 
         by auto
 show "transp Link_Diagram_Equivalence"
         unfolding Link_Diagram_Equivalence_def transp_def
         using  Link_Diagram_Equivalence_def Tangle_Equivalence.trans 
         by metis
qed

definition Framed_Tangle_Diagram_Equivalence::"Tangle_Diagram \<Rightarrow> Tangle_Diagram \<Rightarrow> bool" 
 (infixl "~T" 64)
where
"Framed_Tangle_Diagram_Equivalence T1 T2 
          \<equiv> (Rep_Tangle_Diagram T1) ~ (Rep_Tangle_Diagram T2)"


definition Framed_Link_Diagram_Equivalence::"Link_Diagram \<Rightarrow> Link_Diagram \<Rightarrow> bool" 
 (infixl "~L" 64)
where
"Framed_Link_Diagram_Equivalence T1 T2 
       \<equiv> (Rep_Link_Diagram T1) ~ (Rep_Link_Diagram T2)"


quotient_type Framed_Tangle = "Tangle_Diagram"
               /"Framed_Tangle_Diagram_Equivalence"
morphisms Rep_Framed_Tangles Abs_Framed_Tangles
proof (rule equivpI)
 show "reflp Framed_Tangle_Diagram_Equivalence" 
         unfolding reflp_def Framed_Tangle_Diagram_Equivalence_def 
         Framed_Tangle_Equivalence.refl 
         by auto
 show "symp Framed_Tangle_Diagram_Equivalence" 
         unfolding Framed_Tangle_Diagram_Equivalence_def symp_def
         using  Framed_Tangle_Diagram_Equivalence_def 
          Framed_Tangle_Equivalence.sym 
         by (metis Tangle_Equivalence.sym)
 show "transp Framed_Tangle_Diagram_Equivalence"
         unfolding Framed_Tangle_Diagram_Equivalence_def transp_def
         using  Framed_Tangle_Diagram_Equivalence_def Framed_Tangle_Equivalence.trans 
         by (metis Tangle_Equivalence.trans)
qed

quotient_type Framed_Link = "Link_Diagram"/"Framed_Link_Diagram_Equivalence"
morphisms Rep_Framed_Links Abs_Framed_Links
proof (rule equivpI)
 show "reflp Framed_Link_Diagram_Equivalence" 
         unfolding reflp_def Framed_Link_Diagram_Equivalence_def 
         Framed_Tangle_Equivalence.refl 
         by auto
 show "symp Framed_Link_Diagram_Equivalence" 
         unfolding Framed_Link_Diagram_Equivalence_def symp_def
         using  Framed_Link_Diagram_Equivalence_def  Framed_Tangle_Equivalence.sym 
         by (metis Tangle_Equivalence.sym)
 show "transp Framed_Link_Diagram_Equivalence"
         unfolding Framed_Link_Diagram_Equivalence_def transp_def
         using  Framed_Link_Diagram_Equivalence_def Framed_Tangle_Equivalence.trans 
         by (metis Tangle_Equivalence.trans)
 qed

end
