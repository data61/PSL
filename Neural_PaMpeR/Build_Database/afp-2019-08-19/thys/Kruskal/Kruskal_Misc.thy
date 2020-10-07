section "Auxilliary Lemmas"  
theory Kruskal_Misc
  imports
    "Collections.Partial_Equivalence_Relation"
    "Automatic_Refinement.Misc"
    Refine_Imperative_HOL.Sepref
begin         
  
lemma card2_get2: assumes "card x = 2"
  obtains a b where  "x = {a, b}" "a \<noteq> b"
proof -
  from assms have [simp,intro!]: "finite x" apply(rule_tac ccontr) by auto
  from assms obtain a where ax: "a \<in> x"
    by fastforce
  with assms  have "card (x - {a}) = 1" by fastforce
  then obtain b where "x - {a} = {b}" "a \<noteq> b"
    by (metis Diff_cancel Diff_idemp card_1_singletonE insert_not_empty)
  with that ax show ?thesis by blast
qed

subsection "Lemmas on equivalence relations"
  
lemma equiv_sym: "equiv V R \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (y,x)\<in>R"
  by (metis equiv_def symD)

lemma equiv_trans: "equiv V R \<Longrightarrow> (x,y)\<in>R \<Longrightarrow> (y,z)\<in>R \<Longrightarrow> (x,z)\<in>R"
  by (metis equiv_def transD)
    
lemma equiv_trans_sym: 
  "\<lbrakk> equiv V R; (a,b)\<in>R; (c,b)\<in>R \<rbrakk> \<Longrightarrow> (a,c)\<in>R"
  "\<lbrakk> equiv V R; (a,b)\<in>R; (a,c)\<in>R \<rbrakk> \<Longrightarrow> (b,c)\<in>R"
  apply (metis equiv_sym equiv_trans)+
  done
  
lemma union_equiv: 
  "equiv V R \<Longrightarrow> equiv V (per_union R a b)"
  apply (rule equivI)        
  unfolding per_union_def 
  subgoal unfolding equiv_def refl_on_def by auto
  subgoal apply (rule symI) by (auto dest: equiv_sym)
  subgoal apply (rule transI) by (auto dest: equiv_trans equiv_trans_sym)
  done
  
  
lemma equiv_mono: "E'\<subseteq>E \<Longrightarrow> equiv E R1 \<Longrightarrow> equiv E' (R1 \<inter> E'\<times>E')"
  apply(rule equivI)
  subgoal unfolding equiv_def 
    by (simp add: refl_on_def subset_iff)  
  subgoal unfolding equiv_def 
    by (metis mem_Sigma_iff symI sym_Int)  
  subgoal unfolding equiv_def using trans_Restr by fastforce
  done
    
    

lemma unify2EquivClasses_alt: 
  assumes "R``{x} \<noteq> R``{y}" and inV: "y\<in>V" "x\<in>V" and "R\<subseteq>V\<times>V"    
   and eq: "equiv V R" and [simp]: "finite V"
  shows "Suc (card (quotient V (per_union R x y))) = card (quotient V R)"
proof -
   
  from eq have Rtrancl: "R\<^sup>+ = R" by (auto elim: equivE)
  from \<open>equiv V R\<close> have sym: "sym R" unfolding equiv_def by auto
  
  let ?R' = "per_union R x y"  

  \<comment> \<open> the equivalence classes not contining x and y, stay unchanged when performing @{term per_union} \<close>
  have "\<And>z. z \<in> V \<Longrightarrow> z \<notin> R `` {x} \<Longrightarrow> z \<notin> R `` {y} \<Longrightarrow> per_union R x y `` {z} = R `` {z}"
    using sym by(auto simp: sym_def per_union_def)
  then have K: "(\<Union>x \<in> (V-(R``{x})-(R``{y})). {?R'``{x}}) = (\<Union>x \<in> (V-(R``{x})-(R``{y})). {R``{x}})"
    by auto 
  
  have R_respect: "(\<lambda>x. {R `` {x}}) respects R"
    unfolding congruent_def using eq equiv_class_eq_iff by fastforce+
      
  have R'_respect: "(\<lambda>xa. {?R' `` {xa}}) respects R"
    unfolding congruent_def per_union_def
      using eq equiv_class_eq_iff by force+ 

  \<comment> \<open>some facts about the equivalence class of x, before and after the @{term per_union} operation\<close>
  have xdrin: "(R``{x}) \<subseteq> V" using assms(4) by auto
  have x1: "(\<Union>x \<in> (R``{x}). {?R'``{x}}) = {?R'``{x}}"
    apply(rule UN_equiv_class) by fact+
  have x2: "(\<Union>x \<in> (R``{x}). {R``{x}}) = {R``{x}}" 
    apply(rule UN_equiv_class) by fact+
      
  \<comment> \<open>some facts about the equivalence class of y, before and after the @{term per_union} operation\<close>
  have ydrin: "(R``{y}) \<subseteq> V" using assms(4) by auto
  have y1: "(\<Union>x \<in> (R``{y}). {?R'``{x}}) = {?R'``{y}}"
    apply(rule UN_equiv_class) by fact+
  have y2: "(\<Union>x \<in> (R``{y}). {R``{x}}) = {R``{y}}" 
    apply(rule UN_equiv_class) by fact+
  
  have z: "(y,x)\<in>?R'" unfolding per_union_def using sym sym_def
    using assms(2) assms(3) eq eq_equiv_class by fastforce
  have bla: "?R'``{y} = ?R'``{x}" 
    apply(rule equiv_class_eq)
     apply(rule union_equiv) 
     apply fact
    by fact 
      
  let ?Vm = "(\<Union>x \<in> (V-(R``{x})-(R``{y})). {R``{x}})"  

  \<comment> \<open>now consider the set of quotients wrt. the relation after the @{term per_union}\<close>
  have "quotient V ?R' = (\<Union>x \<in> V. {?R'``{x}})" unfolding quotient_def by auto
  also  \<comment> \<open>decompose it into the quotients for elements equivalent to x, y in R, and the rest\<close>
  have "\<dots> = (\<Union>x \<in> (V-(R``{x})-(R``{y})). {?R'``{x}})
             \<union> (\<Union>x \<in> (R``{y}). {?R'``{x}}) \<union> (\<Union>x \<in> (R``{x}). {?R'``{x}})"     
    using xdrin ydrin by auto     
  also  \<comment> \<open>for the elements equivalent to x and y in R the quotient is 
            the quotient containing x and y respectively \<close>
  have "\<dots> = (\<Union>x \<in> (V-(R``{x})-(R``{y})). {?R'``{x}}) \<union> {?R'``{y}} \<union> {?R'``{x}}" using x1 y1 by auto 
  also  \<comment> \<open>which is after uniting them, the same quotient \<close>
  have "\<dots> = (\<Union>x \<in> (V-(R``{x})-(R``{y})). {R``{x}}) \<union> {?R'``{y}}" using K bla by auto 
  also
  have "\<dots> = insert (?R'``{y}) ?Vm" by auto
  finally have leftside: "quotient V ?R' = insert (?R'``{y}) ?Vm" .
      
  have notin: "?R'``{y} \<notin> ?Vm" 
    apply (auto simp: per_union_def)
    by (metis (no_types, lifting) Image_singleton_iff UnI1 assms(2) eq equiv_class_self local.sym symE)  
  
  have o: "card (quotient V ?R') = Suc (card ?Vm)"
    unfolding leftside apply(rule card_insert_disjoint)
     using notin by auto
      
  \<comment> \<open>now consider the set of quotients wrt. the relation before the @{term per_union}\<close>
  have "quotient V R = (\<Union>x \<in> V. {R``{x}})" unfolding quotient_def by auto
  also \<comment> \<open>decompose it into the quotients for elements equivalent to x, y in R, and the rest\<close>
  have "\<dots> = (\<Union>x \<in> (V-(R``{x})-(R``{y})). {R``{x}})
           \<union> (\<Union>x \<in> (R``{y}). {R``{x}}) \<union> (\<Union>x \<in> (R``{x}). {R``{x}})"     
    using xdrin ydrin by auto     
  also \<comment> \<open>for the elements equivalent to x and y in R the quotient is 
            the quotient containing x and y respectively \<close>
  have "\<dots> = (\<Union>x \<in> (V-(R``{x})-(R``{y})). {R``{x}}) \<union> {R``{y}} \<union> {R``{x}}" using x2 y2 by auto 
  also \<comment> \<open> these are two distinct quotients  \<close>
  have "\<dots> = insert (R``{y}) (insert (R``{x}) ?Vm)" by auto 
  finally have ii: "quotient V R = insert (R``{y}) (insert (R``{x}) ?Vm)" .
      
      
  have "R``{x} \<notin> ?Vm"
    using eq equiv_class_self by fastforce   
  have "R``{y} \<notin> ?Vm" 
    using eq equiv_class_self by fastforce  
  with assms(1)
  have "R``{y} \<notin> (insert (R``{x}) ?Vm)" by blast
  have "card (quotient V R) = Suc (card (insert (R``{x}) ?Vm))" 
    apply(simp only: ii) 
    apply(rule card_insert_disjoint)
     apply simp
    apply fact done
  also have "card (insert (R``{x}) ?Vm) = Suc (card ?Vm)" 
    apply(rule card_insert_disjoint)
     apply simp
    apply fact done
  finally have a: "card (quotient V R) = Suc (Suc (card ?Vm))" by auto
  
  from a o show ?thesis by auto
qed  


  
  
subsection "On the pigeon hole principle"
  
lemma fixes f::"'c\<Rightarrow>'d"
    and g ::"'c\<Rightarrow>'d"
    assumes "finite A" and k: "\<And>a b. a\<in>A \<Longrightarrow> b\<in>A \<Longrightarrow> f a = f b \<Longrightarrow> g a = g b"
    shows  coarser: "card (f ` A) \<ge> card (g ` A)"  
      using assms 
proof - 
  let ?h = "\<lambda>d. THE x. {x} = g ` {x\<in>A. f x = d}" 
  term image 
  have z: "\<And>x. x\<in>A \<Longrightarrow> g ` {y\<in>A. f y = f x} = {g x} " 
     unfolding image_def apply auto using k  
     by blast
   have uz: "\<And>x. x\<in>A \<Longrightarrow> ?h (f x) = g x"
      by (simp add: z) 
  have "card (?h ` (f ` A)) \<le> card (f ` A)"
    apply(rule card_image_le)
    apply(rule finite_imageI) by fact
  moreover
    from uz have "?h ` (f ` A)  = g ` A"  
    by force
  ultimately show ?thesis by auto
qed   
       

subsection "On sorting and \<open>max_node\<close>"


definition edges_less_eq :: "('a \<times> 'w::{linorder, ordered_comm_monoid_add} \<times> 'a) \<Rightarrow> ('a \<times> 'w \<times> 'a) \<Rightarrow> bool"
  where "edges_less_eq a b \<equiv> fst(snd a) \<le> fst(snd b)"

definition "sort_edges \<equiv> quicksort_by_rel edges_less_eq []"

definition "max_node l \<equiv> Max (insert 0 (fst`set l \<union> (snd o snd)`set l))"

lemma max_node_impl[code]: "max_node l = fold (\<lambda>(u,_,w) x. max u (max w x)) l 0"
proof -
  have "fold (\<lambda>(u,_,w) x. max u (max w x)) l a = Max (insert a (fst`set l \<union> (snd o snd)`set l))" for a
    apply (induction l arbitrary: a)
     apply (auto simp:  )
    subgoal for a b l aa
      apply (cases l)
      by (auto simp: ac_simps)
    done
  thus ?thesis unfolding max_node_def by auto
qed

definition "is_linorder_rel R \<equiv> (\<forall>x y. R x y \<or> R y x) \<and> (\<forall>x y z. R x y \<longrightarrow> R y z \<longrightarrow> R x z)"

lemma edges_less_eq_linorder: "is_linorder_rel edges_less_eq"
  unfolding edges_less_eq_def is_linorder_rel_def
  by (metis linear order_trans)


lemma sort_edges_correct: "sorted_wrt edges_less_eq (quicksort_by_rel edges_less_eq [] l)"
  by (metis (no_types, hide_lams) edges_less_eq_linorder is_linorder_rel_def sorted_wrt_quicksort_by_rel)

lemma distinct_mset_eq:"distinct a \<Longrightarrow> mset a = mset b \<Longrightarrow> distinct b"
  by (metis card_distinct distinct_card set_mset_mset size_mset)

lemma quicksort_by_rel_distinct: "distinct l \<Longrightarrow> distinct (quicksort_by_rel edges_less_eq [] l)"
  by (auto intro: distinct_mset_eq)

 
subsection "On @{term list_rel}"


lemma map_in_list_rel_conv: 
  shows "(l, l') \<in> \<langle>br \<alpha> I\<rangle>list_rel \<longleftrightarrow> ((\<forall>x\<in>set l. I x) \<and> l'=map \<alpha> l)"
proof (induction l arbitrary: l') 
  case (Cons a l l')
  then show ?case apply(cases l') by (auto simp add: in_br_conv)
qed simp

lemma list_relD: "(x, y) \<in> \<langle>br a I\<rangle>list_rel \<Longrightarrow> y = map a x" 
  by(auto simp: map_in_list_rel_conv)

lemma list_relD2: "(x, y) \<in> \<langle>br a I\<rangle>list_rel \<Longrightarrow> y = map a x \<and> (\<forall>x\<in>set x. I x)"
  by(auto simp: map_in_list_rel_conv) 


lemma list_set_rel_append: "(x,s)\<in>br a I \<Longrightarrow> (xs,S)\<in>\<langle>br a I\<rangle>list_set_rel \<Longrightarrow> s\<notin>S
     \<Longrightarrow> (xs@[x],insert s S)\<in>\<langle>br a I\<rangle>list_set_rel"
  unfolding list_set_rel_def
  apply(intro relcompI[where b="map a (xs @ [x])"])
   apply (auto simp: in_br_conv)
      apply parametricity by (auto dest: list_relD simp add: in_br_conv)
 
subsection "Auxiliary lemmas for Sepref"


lemma pure_fold: "(\<lambda>a c. \<up> (c = a)) = pure Id" unfolding pure_def by auto
lemma list_assn_emp: "list_assn id_assn L L = emp" 
  apply(induct L) apply simp by (simp add: pure_def)

end