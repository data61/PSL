section "Topological Ordering of Graphs"
theory Graph_Topological_Ordering
imports 
  Refine_Imperative_HOL.Sepref_Misc
  "List-Index.List_Index"
begin

subsection \<open>List-Before Relation\<close>  
text \<open>
  Two elements of a list are in relation if the first element comes (strictly) before
  the second element.
\<close>  
definition "list_before_rel l \<equiv> { (a,b). \<exists>l1 l2 l3. l=l1@a#l2@b#l3 }"

text \<open>list-before only relates elements of the list\<close>    
lemma list_before_rel_on_elems: "list_before_rel l \<subseteq> set l \<times> set l" 
  unfolding list_before_rel_def by auto
  
text \<open>Irreflexivity of list-before is equivalent to the elements of the list being disjoint.\<close>  
lemma list_before_irrefl_eq_distinct: "irrefl (list_before_rel l) \<longleftrightarrow> distinct l"  
  using not_distinct_decomp[of l]
  by (auto simp: irrefl_def list_before_rel_def)
    
text \<open>Alternative characterization via indexes\<close>    
lemma list_before_rel_alt: "list_before_rel l = { (l!i, l!j) | i j. i<j \<and> j<length l }"
  unfolding list_before_rel_def
  apply (rule; clarsimp)
  subgoal for a b l1 l2 l3  
    apply (rule exI[of _ "length l1"]; simp)
    apply (rule exI[of _ "length l1 + Suc (length l2)"]; auto simp: nth_append)
    done      
  subgoal for i j
    apply (rule exI[of _ "take i l"])
    apply (rule exI[of _ "drop (Suc i) (take j l)"])
    apply (rule exI[of _ "drop (Suc j) l"])
    by (simp add: Cons_nth_drop_Suc drop_take_drop_unsplit)
  done      

text \<open>list-before is a strict ordering, i.e., it is transitive and asymmetric.\<close>    
lemma list_before_trans[trans]: "distinct l \<Longrightarrow> trans (list_before_rel l)" 
  by (clarsimp simp: trans_def list_before_rel_alt) (metis index_nth_id less_trans)    
    
lemma list_before_asym: "distinct l \<Longrightarrow> asym (list_before_rel l)"
  by (meson asym.intros irrefl_def list_before_irrefl_eq_distinct list_before_trans transE)

text \<open>Structural properties on the list\<close>    
lemma list_before_rel_empty[simp]: "list_before_rel [] = {}"    
  unfolding list_before_rel_def by auto
    
lemma list_before_rel_cons: "list_before_rel (x#l) = ({x}\<times>set l) \<union> list_before_rel l"    
  apply (intro equalityI subsetI; simp add: split_paired_all)  
  subgoal for a b proof -
    assume "(a,b) \<in> list_before_rel (x # l)"  
    then obtain i j where IDX_BOUND: "i<j" "j<Suc (length l)" and [simp]: "a=(x#l)!i" "b=(x#l)!j" 
      unfolding list_before_rel_alt by auto

    {
      assume "i=0"
      hence "x=a" "b\<in>set l" using IDX_BOUND
        by (auto simp: nth_Cons split: nat.splits)
    } moreover {
      assume "i\<noteq>0"
      with IDX_BOUND have "a=l!(i-1)" "b=l!(j-1)" "i-1 < j-1" "j-1 < length l"
        by auto
      hence "(a, b) \<in> list_before_rel l" unfolding list_before_rel_alt by blast 
    } ultimately show ?thesis by blast
  qed
  subgoal premises prems for a b  
  proof -
    {
      assume [simp]: "a=x" and "b\<in>set l"
      then obtain j where "b = l!j" "j<length l" by (auto simp: in_set_conv_nth)
      hence "a=(x#l)!0" "b = (x#l)!Suc j" "0 < Suc j" "Suc j < length (x#l)" by auto
      hence ?thesis unfolding list_before_rel_alt by blast    
    } moreover {
      assume "(a, b) \<in> list_before_rel l"
      hence ?thesis unfolding list_before_rel_alt
        by clarsimp (metis Suc_mono nth_Cons_Suc)  
    } ultimately show ?thesis using prems by blast
  qed
  done  

subsection \<open>Topological Ordering\<close>
  
text \<open>
  A topological ordering of a graph (binary relation) is an enumeration of its
  nodes, such that for any two nodes \<open>x\<close>,\<open>y\<close> with \<open>x\<close> being enumerated earlier than \<open>y\<close>,
  there is no path from \<open>y\<close> to \<open>x\<close> in the graph.

  We define the predicate \<open>is_top_sorted\<close> to capture the sortedness criterion, but
  not the completeness criterion, i.e., the list needs not contain all 
  nodes of the graph.
\<close>  
  
definition "is_top_sorted R l \<equiv> list_before_rel l \<inter> (R\<^sup>*)\<inverse> = {}"  
lemma is_top_sorted_alt: "is_top_sorted R l \<longleftrightarrow> (\<forall>x y. (x,y)\<in>list_before_rel l \<longrightarrow> (y,x)\<notin>R\<^sup>*)"
  unfolding is_top_sorted_def by auto
  
lemma is_top_sorted_empty_rel[simp]: "is_top_sorted {} l \<longleftrightarrow> distinct l"
  by (auto simp: is_top_sorted_def list_before_irrefl_eq_distinct[symmetric] irrefl_def)

lemma is_top_sorted_empty_list[simp]: "is_top_sorted R []"
  by (auto simp: is_top_sorted_def)

text \<open>A topological sorted list must be distinct\<close>    
lemma is_top_sorted_distinct: 
  assumes "is_top_sorted R l" 
  shows "distinct l"
proof (rule ccontr)  
  assume "\<not>distinct l"
  with list_before_irrefl_eq_distinct[of l] obtain x where "(x,x)\<in>(list_before_rel l)"
    by (auto simp: irrefl_def)
  with assms show False unfolding is_top_sorted_def by auto      
qed  
  
    
lemma is_top_sorted_cons: "is_top_sorted R (x#l) \<longleftrightarrow> ({x}\<times>set l \<inter> (R\<^sup>*)\<inverse> = {}) \<and> is_top_sorted R l"
  unfolding is_top_sorted_def
  by (auto simp: list_before_rel_cons)
    
lemma is_top_sorted_append: "is_top_sorted R (l1@l2) 
  \<longleftrightarrow> (set l1\<times>set l2 \<inter> (R\<^sup>*)\<inverse> = {}) \<and> is_top_sorted R l1 \<and> is_top_sorted R l2"    
  by (induction l1) (auto simp: is_top_sorted_cons)

lemma is_top_sorted_remove_elem: "is_top_sorted R (l1@x#l2) \<Longrightarrow> is_top_sorted R (l1@l2)"
  by (auto simp: is_top_sorted_cons is_top_sorted_append)

text \<open>Removing edges from the graph preserves topological sorting\<close>
lemma is_top_sorted_antimono:
  assumes "R\<subseteq>R'"
  assumes "is_top_sorted R' l"
  shows "is_top_sorted R l"  
  using assms 
  unfolding is_top_sorted_alt  
  by (auto dest: rtrancl_mono_mp)

text \<open>
  Adding a node to the graph, which has no incoming edges preserves topological ordering.
\<close>    
lemma is_top_sorted_isolated_constraint:
  assumes "R' \<subseteq> R \<union> {x}\<times>X" "R'\<inter>UNIV\<times>{x} = {}"
  assumes "x\<notin>set l"  
  assumes "is_top_sorted R l"  
  shows "is_top_sorted R' l"  
proof -
  {
    fix a b
    assume "(a,b)\<in>R'\<^sup>*" "a\<noteq>x" "b\<noteq>x"  
    hence "(a,b)\<in>R\<^sup>*"  
    proof (induction rule: converse_rtrancl_induct)
      case base
      then show ?case by simp
    next
      case (step y z)
      with assms(1,2) have "z\<noteq>x" "(y,z)\<in>R" by auto  
      with step show ?case by auto
    qed
  } note AUX=this
    
  show ?thesis
    using assms(3,4) AUX list_before_rel_on_elems 
    unfolding is_top_sorted_def by fastforce
qed  



end
