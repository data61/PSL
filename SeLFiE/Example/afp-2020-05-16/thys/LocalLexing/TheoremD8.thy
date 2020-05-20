theory TheoremD8
imports TheoremD7
begin

context LocalLexing begin

lemma wellformed_tokens_empty_path[simp]: "wellformed_tokens []"
  by (simp add: wellformed_tokens_def)

lemma \<P>_0_0_Gen: "Gen (\<P> 0 0) = { x . wellformed_item x \<and> item_origin x = 0 \<and> item_end x = 0 \<and>
  derives (item_\<alpha> x) [] \<and> (\<exists> \<gamma>. is_derivation ([item_nonterminal x] @ \<gamma>)) }"
by (auto simp add: Gen_def pvalid_def)

lemma Init_subset_Gen: "Init \<subseteq> Gen (\<P> 0 0)"
  apply (subst \<P>_0_0_Gen)
  apply (auto simp add: Init_def)
  apply (rule_tac x="[]" in exI)
  apply (simp add: is_derivation_def)
  done

lemma \<J>_0_0_subset_Gen: "\<J> 0 0 \<subseteq> Gen (\<P> 0 0)"
  apply (simp only: \<J>.simps)
  apply (rule_tac thmD5)
  apply (rule Init_subset_Gen)
  by auto

lemma inc_dot_rule[simp]: "item_rule (inc_dot d x) = item_rule x"
  by (simp add: inc_dot_def)

lemma init_item_rule[simp]: "item_rule (init_item r k) = r"
  by (simp add: init_item_def)  

lemma item_dot_is_\<alpha>_length: "wellformed_item x \<Longrightarrow> item_dot x = length (item_\<alpha> x)"
  apply (simp add: item_\<alpha>_def)
  by (simp add: min_absorb2 wellformed_item_def) 
  
lemma Gen_subset_\<J>_0_0_helper:
  assumes "wellformed_item x"
  assumes "item_origin x = 0"
  assumes "item_end x = 0"
  assumes "derives (item_\<alpha> x) []"
  assumes "is_derivation (item_nonterminal x # \<gamma>)"
  shows "x \<in> \<pi> 0 {} Init"
proof - 
  let ?y = "init_item (item_nonterminal x, item_rhs x) 0"
  have y_dom: "?y \<in> \<pi> 0 {} Init" 
    apply (rule_tac thmD7)
    using assms apply auto
    using is_nonterminal_item_nonterminal apply blast
    by (simp add: item_nonterminal_def item_rhs_def wellformed_item_def)
  let ?x = "inc_dot (length (item_\<alpha> x)) ?y"
  have x1: "item_rule x = item_rule ?x"
    apply (simp)
    by (simp add: item_nonterminal_def item_rhs_def)
  have x2: "item_dot x = item_dot ?x"
    apply simp
    by (simp add: assms(1) item_dot_is_\<alpha>_length)
  have x3: "item_origin x = item_origin ?x"
    using assms by auto
  have x4: "item_end x = item_end ?x"
    using assms by auto
  from x1 x2 x3 x4 have x_is_inc: "x = ?x" using item.expand by blast
  have wellformed_item_y: "wellformed_item ?y"
    using assms(1) item_nonterminal_def item_rhs_def wellformed_item_def by auto
  have "x \<in> \<pi> 0 {} {?y}"
    apply (subst x_is_inc)
    apply (rule_tac thmD6) 
    apply (simp add: wellformed_item_y)
    apply (simp add: item_rhs_split)
    apply simp
    using assms apply simp
    done
  with y_dom show ?thesis
    using \<pi>_subset_elem_trans empty_subsetI insert_subset by blast
qed        

lemma Gen_subset_\<J>_0_0: "Gen (\<P> 0 0) \<subseteq> \<J> 0 0"
  apply (subst \<P>_0_0_Gen)
  apply auto
  using Gen_subset_\<J>_0_0_helper by blast
  
theorem thmD8: "\<J> 0 0 = Gen (\<P> 0 0)"
  using Gen_subset_\<J>_0_0 \<J>_0_0_subset_Gen by blast

end

end
