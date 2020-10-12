section \<open>Multiset Interface\<close>
theory IICF_Multiset
imports "../../Sepref"
begin

subsection \<open>Additions to Multiset Theory\<close>
lemma rel_mset_Plus_gen: 
  assumes "rel_mset A m m'"
  assumes "rel_mset A n n'"
  shows "rel_mset A (m+n) (m'+n')"
  using assms
  by induction (auto simp: algebra_simps dest: rel_mset_Plus)
  
lemma rel_mset_single:
  assumes "A x y"
  shows "rel_mset A {#x#} {#y#}"
  unfolding rel_mset_def
  apply (rule exI[where x="[x]"])
  apply (rule exI[where x="[y]"])
  using assms by auto

lemma rel_mset_Minus:
  assumes BIU: "bi_unique A"
  shows "\<lbrakk> rel_mset A m n; A x y \<rbrakk> \<Longrightarrow> rel_mset A (m-{#x#}) (n-{#y#})"
  unfolding rel_mset_def 
proof clarsimp
  fix ml nl
  assume A: "A x y"
  assume R: "list_all2 A ml nl"
  show "\<exists>ml'. mset ml' = mset ml - {#x#} \<and>
                 (\<exists>nl'. mset nl' = mset nl - {#y#} \<and> list_all2 A ml' nl')"
  proof (cases "x\<in>set ml")
    case False
    have "y \<notin> set nl" using A R 
      apply (auto simp: in_set_conv_decomp list_all2_append2 list_all2_Cons2)
      using False BIU[unfolded bi_unique_alt_def]
      apply (auto dest: left_uniqueD)
      done
    with False R show ?thesis by (auto simp: diff_single_trivial in_multiset_in_set)
  next
    case True  
    then obtain ml1 ml2 where [simp]: "ml=ml1@x#ml2" by (auto simp: in_set_conv_decomp)
    then obtain nl1 nl2 where [simp]: "nl=nl1@y#nl2"
      and LA: "list_all2 A ml1 nl1" "list_all2 A ml2 nl2"
      using A R
      apply (auto simp: in_set_conv_decomp list_all2_append1 list_all2_Cons1)
      using BIU[unfolded bi_unique_alt_def]
      apply (auto dest: right_uniqueD)
      done
    have 
      "mset (ml1@ml2) = mset ml - {#x#}"
      "mset (nl1@nl2) = mset nl - {#y#}"
      using R
      by (auto simp: algebra_simps add_implies_diff union_assoc)
    moreover have "list_all2 A (ml1@ml2) (nl1@nl2)"
      by (rule list_all2_appendI) fact+
    ultimately show ?thesis by blast
  qed  
qed

lemma rel_mset_Minus_gen: 
  assumes BIU: "bi_unique A"
  assumes "rel_mset A m m'"
  assumes "rel_mset A n n'"
  shows "rel_mset A (m-n) (m'-n')"
  using assms(3,2)
  apply (induction R\<equiv>A _ _ rule: rel_mset_induct)
  apply (auto dest: rel_mset_Minus[OF BIU] simp: algebra_simps)
  done

lemma pcr_count:
  assumes "bi_unique A"
  shows "rel_fun (rel_mset A) (rel_fun A (=)) count count"
  apply (intro rel_funI)
  unfolding rel_mset_def
  apply clarsimp
  subgoal for x y xs ys
    apply (rotate_tac,induction xs ys rule: list_all2_induct)
    using assms
    by (auto simp: bi_unique_alt_def left_uniqueD right_uniqueD)
  done    

subsection \<open>Parametricity Setup\<close>
definition [to_relAPP]: "mset_rel A \<equiv> p2rel (rel_mset (rel2p A))"

lemma rel2p_mset[rel2p]: "rel2p (\<langle>A\<rangle>mset_rel) = rel_mset (rel2p A)"
  by (simp add: mset_rel_def)

lemma p2re_mset[p2rel]: "p2rel (rel_mset A) = \<langle>p2rel A\<rangle>mset_rel"  
  by (simp add: mset_rel_def)

lemma mset_rel_empty[simp]: 
  "(a,{#})\<in>\<langle>A\<rangle>mset_rel \<longleftrightarrow> a={#}"
  "({#},b)\<in>\<langle>A\<rangle>mset_rel \<longleftrightarrow> b={#}"
  by (auto simp: mset_rel_def p2rel_def rel_mset_def)


lemma param_mset_empty[param]: "({#},{#}) \<in> \<langle>A\<rangle>mset_rel"
  unfolding mset_rel_def
  apply (simp add: p2rel_def)
  by (rule rel_mset_Zero)

lemma param_mset_Plus[param]: "((+),(+))\<in>\<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel"  
  apply (rule rel2pD)
  apply (simp add: rel2p)
  apply (intro rel_funI)
  by (rule rel_mset_Plus_gen)


(*lemma param_mset_single[param]: 
  "(Multiset.single,Multiset.single) \<in> A \<rightarrow> \<langle>A\<rangle>mset_rel"
  apply (rule rel2pD)
  apply (simp add: rel2p)
  apply (intro rel_funI)
  by (rule rel_mset_single)*)

lemma param_mset_add[param]: "(add_mset, add_mset) \<in> A \<rightarrow> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel"
  apply (rule rel2pD)
  apply (simp add: rel2p)
  apply (intro rel_funI)
  by (rule rel_mset_Plus)

lemma param_mset_minus[param]: "\<lbrakk>single_valued A; single_valued (A\<inverse>)\<rbrakk> 
  \<Longrightarrow> ((-), (-)) \<in> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel" 
  apply (rule rel2pD)
  apply (simp add: rel2p)
  apply (intro rel_funI)
  apply (rule rel_mset_Minus_gen)
  subgoal apply (unfold IS_LEFT_UNIQUE_def[symmetric])
    by (simp add: prop2p bi_unique_alt_def)
  apply (simp; fail)
  apply (simp; fail)
  done

lemma param_count[param]: "\<lbrakk>single_valued A; single_valued (A\<inverse>)\<rbrakk> \<Longrightarrow> (count,count)\<in>\<langle>A\<rangle>mset_rel \<rightarrow> A \<rightarrow> nat_rel"  
  apply (rule rel2pD)
  apply (simp add: prop2p rel2p)
  apply (rule pcr_count)
  apply (simp add: bi_unique_alt_def)
  done

lemma param_set_mset[param]: 
  shows "(set_mset, set_mset) \<in> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>set_rel"
  apply (rule rel2pD; simp add: rel2p)
  by (rule multiset.set_transfer)  

definition [simp]: "mset_is_empty m \<equiv> m = {#}"

lemma mset_is_empty_param[param]: "(mset_is_empty,mset_is_empty) \<in> \<langle>A\<rangle>mset_rel \<rightarrow> bool_rel"
  unfolding mset_rel_def mset_is_empty_def[abs_def]
  by (auto simp: p2rel_def rel_mset_def intro: nres_relI)
  

subsection \<open>Operations\<close>
  sepref_decl_op mset_empty: "{#}" :: "\<langle>A\<rangle>mset_rel" .

  sepref_decl_op mset_is_empty: "\<lambda>m. m={#}" :: "\<langle>A\<rangle>mset_rel \<rightarrow> bool_rel"
    unfolding mset_is_empty_def[symmetric]
    apply (rule frefI) 
    by parametricity

  (*sepref_decl_op mset_single: "\<lambda>m. {#m#}" :: "A \<rightarrow> \<langle>A\<rangle>mset_rel" .*)

  sepref_decl_op mset_insert: "add_mset" :: "A \<rightarrow> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel" . 

  sepref_decl_op mset_delete: "\<lambda>x m. m - {#x#}" :: "A \<rightarrow> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel"
    where "single_valued A" "single_valued (A\<inverse>)" .

  sepref_decl_op mset_plus: "(+)::_ multiset \<Rightarrow> _" :: "\<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel" .
  sepref_decl_op mset_minus: "(-)::_ multiset \<Rightarrow> _" :: "\<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>mset_rel" 
    where "single_valued A" "single_valued (A\<inverse>)" .
  

  sepref_decl_op mset_contains: "(\<in>#)" :: "A \<rightarrow> \<langle>A\<rangle>mset_rel \<rightarrow> bool_rel" 
    where "single_valued A" "single_valued (A\<inverse>)" .
    
  sepref_decl_op mset_count: "\<lambda>x y. count y x" :: "A \<rightarrow> \<langle>A\<rangle>mset_rel \<rightarrow> nat_rel" 
    where "single_valued A" "single_valued (A\<inverse>)" .

  sepref_decl_op mset_pick: "\<lambda>m. SPEC (\<lambda>(x,m'). m = {#x#} + m')" :: 
    "[\<lambda>m. m\<noteq>{#}]\<^sub>f \<langle>A\<rangle>mset_rel \<rightarrow> A \<times>\<^sub>r \<langle>A\<rangle>mset_rel"
    unfolding mset_is_empty_def[symmetric]
    apply (intro frefI nres_relI)
    apply (refine_vcg SPEC_refine)
    apply1 (rule ccontr; clarsimp)
    applyS (metis msed_rel_invL rel2p_def rel2p_mset union_ac(2))
    applyS parametricity
    done
    

subsection \<open>Patterns\<close>

lemma [def_pat_rules]:
  "{#} \<equiv> op_mset_empty"
  "add_mset \<equiv> op_mset_insert"
  "(=) $b${#} \<equiv> op_mset_is_empty$b"
  "(=) ${#}$b \<equiv> op_mset_is_empty$b"
  "(+) $a$b \<equiv> op_mset_plus$a$b"
  "(-) $a$b \<equiv> op_mset_minus$a$b"
  by (auto intro!: eq_reflection simp: algebra_simps)

lemma [def_pat_rules]:
  "(+) $b$(add_mset$x${#}) \<equiv> op_mset_insert$x$b"
  "(+) $(add_mset$x${#})$b \<equiv> op_mset_insert$x$b"
  "(-) $b$(add_mset$x${#}) \<equiv> op_mset_delete$x$b"
  "(<) $0$(count$a$x) \<equiv> op_mset_contains$x$a"
  "(\<in>) $x$(set_mset$a) \<equiv> op_mset_contains$x$a"
  by (auto intro!: eq_reflection simp: algebra_simps)


locale mset_custom_empty = 
  fixes rel empty and op_custom_empty :: "'a multiset"
  assumes customize_hnr_aux: "(uncurry0 empty,uncurry0 (RETURN (op_mset_empty::'a multiset))) \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a rel"
  assumes op_custom_empty_def: "op_custom_empty = op_mset_empty"
begin
  sepref_register op_custom_empty :: "'ax multiset"

  lemma fold_custom_empty:
    "{#} = op_custom_empty"
    "op_mset_empty = op_custom_empty"
    "mop_mset_empty = RETURN op_custom_empty"
    unfolding op_custom_empty_def by simp_all

  lemmas custom_hnr[sepref_fr_rules] = customize_hnr_aux[folded op_custom_empty_def]
end

end
