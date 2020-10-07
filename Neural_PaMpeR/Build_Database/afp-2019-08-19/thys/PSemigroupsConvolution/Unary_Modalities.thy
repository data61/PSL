(* Title: Unary Modalities
   Author: Brijesh Dongol, Victor Gomes, Ian J Hayes, Georg Struth
   Maintainer: Victor Gomes <victor.gomes@cl.cam.ac.uk>
               Georg Struth <g.struth@sheffield.ac.uk> 
*)

section \<open>Unary Modalities\<close>

theory Unary_Modalities
  imports Binary_Modalities
begin
  
text \<open>Unary modalites arise as specialisations of the binary ones; and as generalisations of the 
standard (multi-)modal operators from predicates to functions into complete lattices. They are interesting, for instance, 
in combination with partial semigroups or monoids, for modelling the Halpern-Shoham modalities in interval logics. \<close>
  
subsection \<open>Forward and Backward Diamonds\<close>

definition fdia :: "('a \<times> 'b) set \<Rightarrow> ('b \<Rightarrow> 'c::complete_lattice) \<Rightarrow> 'a \<Rightarrow> 'c" ("( |_\<rangle> _ _)" [61,81] 82) where
  "( |R\<rangle> f x) = \<Squnion>{f y|y. (x,y) \<in> R}" 

definition bdia :: "('a \<times> 'b) set \<Rightarrow> ('a \<Rightarrow> 'c::complete_lattice) \<Rightarrow> 'b \<Rightarrow> 'c" ("( \<langle>_| _ _)" [61,81] 82)where
  "(\<langle>R| f y) = \<Squnion>{f x |x. (x,y) \<in> R}"  

definition c1 :: "'a \<Rightarrow> 'b::unital_quantale" where
  "c1 x = 1"
  
text \<open>The relationship with binary modalities is as follows.\<close>
  
lemma fdia_bmod_comp: "( |R\<rangle> f x) = \<otimes> (\<lambda>x y z. (x,y) \<in> R) f c1 x"
  by (simp add: fdia_def bmod_comp_def c1_def)

lemma bdia_bmod_comp: "(\<langle>R| f x) = \<otimes> (\<lambda>y x z. (x,y) \<in> R) f c1 x"
  by (simp add: bdia_def bmod_comp_def c1_def)

lemma bmod_fdia_comp: "\<otimes> R f g x = |{(x,(y,z)) |x y z. R x y z}\<rangle> (\<lambda>(x,y). (f x) \<cdot> (g y)) x"
  by (simp add: fdia_def bmod_comp_def)

lemma bmod_fdia_comp_var: 
  "\<otimes> R f g x = |{(x,(y,z)) |x y z. R x y z}\<rangle> (\<lambda>(x,y). (\<lambda>(v,w).(v \<cdot> w)) (f x,g y)) x"
  by (simp add: fdia_def bmod_comp_def)

lemma fdia_im: "( |R\<rangle> f x) = \<Squnion>(f ` R `` {x})"
  apply (simp add: fdia_def)
  apply (rule antisym)
  apply (intro Sup_least, clarsimp simp: SUP_upper)
  by (intro SUP_least Sup_upper, force)

lemma fdia_un_rel: "fdia (R \<union> S) = fdia R \<squnion> fdia S" 
  apply (simp add: fun_eq_iff)
  by (clarsimp simp: fun_eq_iff fdia_im SUP_union Un_Image)

lemma fdia_Un_rel: "( |\<Union>\<R>\<rangle> f x) = \<Squnion>{|R\<rangle> f x |R. R \<in> \<R>}" 
  apply (simp add: fdia_im)
  apply (rule antisym)
  apply (intro SUP_least, safe)
  apply (rule Sup_upper2, force)
  apply (rule SUP_upper, simp)
  apply (rule Sup_least)
  by (clarsimp simp: Image_mono SUP_subset_mono Sup_upper)

lemma fdia_sup_fun: "fdia R (f \<squnion> g) = fdia R f \<squnion> fdia R g" 
  by (simp add: fun_eq_iff fdia_im complete_lattice_class.SUP_sup_distrib)
    
lemma fdia_Sup_fun: "( |R\<rangle> (\<Squnion>\<F>) x) = \<Squnion>{|R\<rangle> f x |f. f \<in> \<F>} "
  apply (simp add: fdia_im)
  apply (rule antisym) 
  apply (rule SUP_least)+
  apply (rule Sup_upper2, force)
  apply (rule SUP_upper, simp) 
  apply (rule Sup_least, safe)
  apply (rule SUP_least)
  by (simp add: SUP_upper2)

lemma fdia_seq: "fdia (R ; S) f x  = fdia R (fdia S f) x"
  by (simp add: fdia_im relcomp_Image, metis Image_eq_UN SUP_UNION) 

lemma fdia_Id [simp]: "( |Id\<rangle> f x) = f x"
  by (simp add: fdia_def)
    
    
subsection \<open>Forward and Backward Boxes\<close>
  
definition fbox :: "('a \<times> 'b) set \<Rightarrow> ('b \<Rightarrow> 'c::complete_lattice) \<Rightarrow> 'a \<Rightarrow> 'c" ("|_] _ _" [61,81] 82) where
  "( |R] f x) = \<Sqinter>{f y|y. (x,y) \<in> R}" 

definition bbox :: "('a \<times> 'b) set \<Rightarrow> ('a \<Rightarrow> 'c::complete_lattice) \<Rightarrow> 'b \<Rightarrow> 'c" ("[_| _ _" [61,81] 82)where
  "([R| f y) = \<Sqinter>{f x |x. (x,y) \<in> R}"  
  
  
subsection \<open>Symmetries and Dualities\<close>
  
lemma fdia_fbox_demorgan: "( |R\<rangle> (f::'b \<Rightarrow> 'c::complete_boolean_algebra) x) = - |R] (\<lambda>y. -f y) x"
  apply (simp add: fbox_def fdia_def)
  apply (rule antisym)
   apply (rule Sup_least)
   apply (simp add: Inf_lower compl_le_swap1)
  apply (simp add: uminus_Inf)
  apply (rule SUP_least; intro Sup_upper)
  by auto

lemma fbox_fdia_demorgan: "( |R] (f::'b \<Rightarrow> 'c::complete_boolean_algebra) x) = - |R\<rangle> (\<lambda>y. -f y) x"  
  apply (simp add: fbox_def fdia_def)
  apply (rule antisym)
   apply (simp add: uminus_Sup)
   apply (rule INF_greatest; rule Inf_lower)
   apply auto[1]
  apply (rule Inf_greatest)
  by (simp add: Sup_upper compl_le_swap2)
    
lemma bdia_bbox_demorgan: "(\<langle>R| (f::'b \<Rightarrow> 'c::complete_boolean_algebra) x) = - [R| (\<lambda>y. -f y) x"
  apply (simp add: bbox_def bdia_def)
  apply (rule antisym)
   apply (rule Sup_least)
   apply (simp add: Inf_lower compl_le_swap1)
  apply (simp add: uminus_Inf)
  apply (rule SUP_least; intro Sup_upper)
  by auto
    
lemma bbox_bdia_demorgan: "( [R| (f::'b \<Rightarrow> 'c::complete_boolean_algebra) x) = - \<langle>R| (\<lambda>y. -f y) x"  
  apply (simp add: bbox_def bdia_def)
  apply (rule antisym)
   apply (simp add: uminus_Sup)
   apply (rule INF_greatest; rule Inf_lower)
   apply auto[1]
  apply (rule Inf_greatest)
  by (simp add: Sup_upper compl_le_swap2)
 
lemma fdia_bdia_conv: "( |R\<rangle> f x) = \<langle>converse R| f x"
  by (simp add: fdia_def bdia_def) 

lemma fbox_bbox_conv: "( |R] f x) = [converse R| f x"
  by (simp add: fbox_def bbox_def)
    
lemma fdia_bbox_galois: "(\<forall>x. ( |R\<rangle> f x) \<le> g x) \<longleftrightarrow> (\<forall>x. f x \<le> [R| g x)"
  apply (standard, simp_all add: fdia_def bbox_def)
   apply safe
   apply (rule Inf_greatest)
   apply (force simp: Sup_le_iff)  
  apply (rule Sup_least)
  by (force simp: le_Inf_iff)  
    
lemma bdia_fbox_galois: "(\<forall>x. (\<langle>R| f x) \<le> g x) \<longleftrightarrow> (\<forall>x. f x \<le> |R] g x)"
  apply (standard, simp_all add: bdia_def fbox_def)
   apply safe
   apply (rule Inf_greatest)
   apply (force simp: Sup_le_iff)  
  apply (rule Sup_least)
  by (force simp: le_Inf_iff)  
  
lemma dia_conjugate: 
  "(\<forall>x. ( |R\<rangle> (f::'b \<Rightarrow> 'c::complete_boolean_algebra) x) \<sqinter> g x = \<bottom>) \<longleftrightarrow> (\<forall>x. f x \<sqinter> (\<langle>R| g x) = \<bottom>)"
  by (simp add: meet_shunt fdia_bbox_galois bdia_bbox_demorgan)
    
lemma box_conjugate: 
  "(\<forall>x. ( |R] (f::'b \<Rightarrow> 'c::complete_boolean_algebra) x) \<squnion> g x = \<top>) \<longleftrightarrow> (\<forall>x. f x \<squnion> ([R| g x) = \<top>)"
proof-
  have "(\<forall>x. ( |R] f x) \<squnion> g x = \<top>) \<longleftrightarrow> (\<forall>x. -g x \<le> |R] f x)"
    by (simp add: join_shunt sup_commute)
  also have "... \<longleftrightarrow> (\<forall>x. -g x \<le> - |R\<rangle> (\<lambda>y. -f y) x)"
    by (simp add: fbox_fdia_demorgan) 
  also have "... \<longleftrightarrow> (\<forall>x. ( |R\<rangle> (\<lambda>y. -f y) x) \<le> g x)"      
    by simp
  also have "... \<longleftrightarrow> (\<forall>x. -f x \<le> [R| g x)"
    by (simp add: fdia_bbox_galois)  
  finally show ?thesis
    by (simp add: join_shunt)
qed
  
end
                            

  

