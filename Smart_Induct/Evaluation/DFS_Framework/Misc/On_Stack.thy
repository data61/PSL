(* Currently not used, but may be of general use. Keep in Aux! *)
theory On_Stack
imports Collections.Refine_Dflt
begin
subsection \<open>Implementation of a stack with efficient on-stack operation\<close>
text \<open>This generic implementation combines a stack implementation and
  a set implementation that is used to keep track of the elements on the stack.
  It requires a distinct stack, i.e., no duplicate elements on the stack.

  Note that this generic implementation has to be instantiated to a
  concrete stack-relation in order to avoid looping of the autoref-tool,
  which otherwise tries to instantiate the stack-implementation with itself
  indefinitely often.
\<close>

definition stack_rel_internal_def: "stack_rel lrel srel vrel \<equiv> {
  ((li,si),l). (li,l)\<in>\<langle>vrel\<rangle>lrel \<and> (si,set l)\<in>\<langle>vrel\<rangle>srel \<and> distinct l}"

lemma stack_rel_def: "\<langle>vrel\<rangle>stack_rel lrel srel \<equiv> {
  ((li,si),l). (li,l)\<in>\<langle>vrel\<rangle>lrel \<and> (si,set l)\<in>\<langle>vrel\<rangle>srel \<and> distinct l}"
  unfolding stack_rel_internal_def relAPP_def by auto


lemmas [autoref_rel_intf] 
  = REL_INTFI[of "stack_rel lrel srel" i_list for lrel srel]

context 
  fixes lrel :: "('xi \<times> 'x) set \<Rightarrow> ('xli \<times> 'x list) set"
  and srel :: "('xi \<times> 'x) set \<Rightarrow> ('xsi \<times> 'x set) set"
begin

context begin interpretation autoref_syn .

lemma autoref_stack_empty[OF GEN_OP_D GEN_OP_D]:
  assumes "(el,[])\<in>\<langle>vrel\<rangle>lrel"
  assumes "(es,{})\<in>\<langle>vrel\<rangle>srel"
  shows "((el,es),[]) \<in> \<langle>vrel\<rangle>stack_rel lrel srel"
  using assms unfolding stack_rel_def
  by auto


primrec stack_push::"_::type" 
  where "stack_push push ins (el,es) v = (push el v, ins v es)"

lemma autoref_stack_push:
  assumes "GEN_OP push op_list_append_elem (\<langle>vrel\<rangle>lrel \<rightarrow> vrel \<rightarrow> \<langle>vrel\<rangle>lrel)"
  assumes "GEN_OP ins insert (vrel \<rightarrow> \<langle>vrel\<rangle>srel \<rightarrow> \<langle>vrel\<rangle>srel)"
  assumes "SIDE_PRECOND (v\<notin>set l)"
  assumes "(vi,v)\<in>vrel"
  assumes "(si,l)\<in>\<langle>vrel\<rangle>stack_rel lrel srel"
  shows "(stack_push push ins si vi,
    (OP op_list_append_elem ::: \<langle>vrel\<rangle>stack_rel lrel srel \<rightarrow> vrel \<rightarrow> \<langle>vrel\<rangle>stack_rel lrel srel)
      $l$v) \<in> \<langle>vrel\<rangle>stack_rel lrel srel"
  using assms unfolding stack_rel_def
  apply auto
  apply (unfold op_list_append_elem_def[symmetric])
  apply parametricity+
  done


lemma autoref_stack_sng:
  assumes "GEN_OP lsng op_list_singleton (vrel \<rightarrow> \<langle>vrel\<rangle>lrel)"
  assumes "GEN_OP sins insert (vrel \<rightarrow> \<langle>vrel\<rangle>srel \<rightarrow> \<langle>vrel\<rangle>srel)"
  assumes "GEN_OP semp {} (\<langle>vrel\<rangle>srel)"
  shows "(\<lambda>v. (lsng v, sins v semp),op_list_singleton) 
    \<in> vrel \<rightarrow> \<langle>vrel\<rangle>stack_rel lrel srel"
  using assms
  unfolding stack_rel_def autoref_tag_defs
  by (fastforce simp: op_list_singleton_def[abs_def] dest: fun_relD)
  
primrec stack_pop::"_::type" 
  where "stack_pop lpop ltop del (el,es) 
    = (let v = ltop el; el = lpop el; es = del v es in (el,es))"

lemma autoref_stack_pop:
  assumes POPR: "\<And>el l. \<lbrakk> (el,l)\<in>\<langle>vrel\<rangle>lrel; l\<noteq>[] \<rbrakk> 
    \<Longrightarrow> (lpop el,(OP butlast ::: \<langle>vrel\<rangle>lrel \<rightarrow> \<langle>vrel\<rangle>lrel)$l)\<in> \<langle>vrel\<rangle>lrel"
  assumes TOPR: "\<And>el l. \<lbrakk> (el,l)\<in>\<langle>vrel\<rangle>lrel; l\<noteq>[] \<rbrakk> 
    \<Longrightarrow> (ltop el,(OP last ::: \<langle>vrel\<rangle>lrel \<rightarrow> vrel)$l)\<in> vrel"
  assumes DELR: "GEN_OP del op_set_delete (vrel \<rightarrow> \<langle>vrel\<rangle>srel \<rightarrow> \<langle>vrel\<rangle>srel)"
  assumes NE: "SIDE_PRECOND (l \<noteq> [])"
  assumes R: "(si,l)\<in>\<langle>vrel\<rangle>stack_rel lrel srel"
  shows "(stack_pop lpop ltop del si,
    (OP butlast ::: \<langle>vrel\<rangle>stack_rel lrel srel \<rightarrow> \<langle>vrel\<rangle>stack_rel lrel srel)
      $l) \<in> \<langle>vrel\<rangle>stack_rel lrel srel"
proof -
  note POPR TOPR DELR
  note [param] = this[unfolded autoref_tag_defs]

  have AUX: "set (butlast l) = op_set_delete (last l) (set l)"
    using NE R unfolding stack_rel_def 
    by (cases l rule: rev_cases) auto

  show ?thesis
    using NE R unfolding stack_rel_def autoref_tag_defs
    apply (clarsimp simp: distinct_butlast, intro conjI)
    apply parametricity
    apply (subst AUX)
    apply parametricity
    done
qed

lemma autoref_stack_set: 
  shows "(snd, set) \<in> \<langle>vrel\<rangle>stack_rel lrel srel \<rightarrow> \<langle>vrel\<rangle>srel"
  unfolding stack_rel_def
  by auto

lemma autoref_stack_is_Nil: 
  assumes "GEN_OP ini is_Nil (\<langle>vrel\<rangle>lrel \<rightarrow> bool_rel)"
  shows "(ini o fst, is_Nil) \<in> \<langle>vrel\<rangle>stack_rel lrel srel \<rightarrow> bool_rel"
  using assms unfolding stack_rel_def
  by (auto dest: fun_relD)

lemma autoref_stack_ltop: 
  assumes TOPR: "\<And>el l. \<lbrakk> (el,l)\<in>\<langle>vrel\<rangle>lrel; l\<noteq>[] \<rbrakk> 
    \<Longrightarrow> (ltop el,(OP last ::: \<langle>vrel\<rangle>lrel \<rightarrow> vrel)$l)\<in> vrel"
  assumes NE: "SIDE_PRECOND (l \<noteq> [])"
  assumes R: "(si,l)\<in>\<langle>vrel\<rangle>stack_rel lrel srel"
  shows "(ltop (fst si), (OP last ::: \<langle>vrel\<rangle>stack_rel lrel srel \<rightarrow> vrel)$l) \<in> vrel"
  using assms unfolding stack_rel_def
  by (auto dest: fun_relD)

lemmas stack_autoref_rules 
  = autoref_stack_empty autoref_stack_push autoref_stack_sng autoref_stack_pop
    autoref_stack_set autoref_stack_is_Nil autoref_stack_ltop

end

end

abbreviation "as_ahs_stack_rel \<equiv> stack_rel as_rel dflt_ahs_rel"
lemmas as_ahs_stack_rules 
  = stack_autoref_rules[where lrel = as_rel and srel = dflt_ahs_rel]


schematic_goal 
  notes [autoref_rules] = as_ahs_stack_rules
  shows "(?c::?'c, set (butlast ([1::nat]@[2]))) \<in> ?R"
  apply (autoref (trace,keep_goal))
  done

end

