section \<open>ICF-setup for Automatic Refinement\<close>
theory ICF_Autoref
imports 
  ICF_Refine_Monadic 
  "../GenCF/Intf/Intf_Set"
  "../GenCF/Intf/Intf_Map"
begin

subsection \<open>Unique Priority Queue\<close>
consts i_prio :: "interface \<Rightarrow> interface \<Rightarrow> interface"
definition [simp]: "op_uprio_empty \<equiv> Map.empty"
definition [simp]: "op_uprio_is_empty x \<equiv> x = Map.empty"
definition [simp]: "op_uprio_insert s e a \<equiv> s(e \<mapsto> a)"
definition op_uprio_prio :: "('e\<rightharpoonup>'a)\<Rightarrow>'e\<rightharpoonup>'a"
  where [simp]: "op_uprio_prio s e \<equiv> s e"

(* FIXME: Tune id-(phase) such that it can distinguish those patterns!
  For now: Only include this patterns on demand!
*)
context begin interpretation autoref_syn .

lemma uprio_pats:
  fixes s :: "'e\<rightharpoonup>'a"
  shows
  "Map.empty::'e\<rightharpoonup>'a \<equiv> op_uprio_empty"
  "s e \<equiv> op_uprio_prio$s$e"
  "s(e\<mapsto>a) \<equiv> op_uprio_insert$s$e$a"

  "dom s = {} \<equiv> op_uprio_is_empty$s"
  "{} = dom s \<equiv> op_uprio_is_empty$s"
  "s=Map.empty \<equiv> op_uprio_is_empty$s"
  "Map.empty=s \<equiv> op_uprio_is_empty$s"
  by (auto intro!: eq_reflection)

end

term prio_pop_min

lemma [autoref_itype]:
  "op_uprio_empty ::\<^sub>i \<langle>Ie,Ia\<rangle>\<^sub>ii_prio"
  "op_uprio_prio ::\<^sub>i \<langle>Ie,Ia\<rangle>\<^sub>ii_prio \<rightarrow>\<^sub>i Ie \<rightarrow>\<^sub>i \<langle>Ia\<rangle>\<^sub>ii_option"
  "op_uprio_is_empty ::\<^sub>i \<langle>Ie,Ia\<rangle>\<^sub>ii_prio \<rightarrow>\<^sub>i i_bool"
  "op_uprio_insert ::\<^sub>i \<langle>Ie,Ia\<rangle>\<^sub>ii_prio \<rightarrow>\<^sub>i Ie \<rightarrow>\<^sub>i Ia \<rightarrow>\<^sub>i \<langle>Ie,Ia\<rangle>\<^sub>ii_prio"
  "prio_pop_min ::\<^sub>i \<langle>Ie,Ia\<rangle>\<^sub>ii_prio \<rightarrow>\<^sub>i \<langle>\<langle>Ie,\<langle>Ia,\<langle>Ie,Ia\<rangle>\<^sub>ii_prio\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_nres"
  by simp_all

context uprio begin
  definition rel_def_internal: 
    "\<And>Re Ra. rel Re Ra \<equiv> br \<alpha> invar O (Re \<rightarrow> \<langle>Ra\<rangle> option_rel)"
  lemma rel_def:
    "\<And>Re Ra. \<langle>Re,Ra\<rangle>rel \<equiv> br \<alpha> invar O (Re \<rightarrow> \<langle>Ra\<rangle> option_rel)" 
    by (simp add: rel_def_internal relAPP_def)
    
  lemma rel_id[simp]: "\<langle>Id,Id\<rangle>rel = br \<alpha> invar" 
    by (simp add: rel_def)

  lemma rel_sv[relator_props]: 
    "\<And>Re Ra. \<lbrakk>Range Re = UNIV; single_valued Ra\<rbrakk> \<Longrightarrow> single_valued (\<langle>Re,Ra\<rangle>rel)"
    unfolding rel_def by tagged_solver

  lemmas [autoref_rel_intf] = REL_INTFI[of rel i_prio]
end


lemma (in uprio) rel_alt: "\<langle>Id,Rv\<rangle>rel = 
  { (c,a). \<forall>x. (\<alpha> c x,a x)\<in>\<langle>Rv\<rangle>option_rel \<and> invar c }"
  by (auto simp: rel_def br_def dest: fun_relD)

lemma (in uprio_empty) autoref_empty[autoref_rules]:
  "\<And>Re Ra. PREFER_id Re \<Longrightarrow> (empty (),op_uprio_empty)\<in>\<langle>Re,Ra\<rangle>rel"
  by (auto simp: empty_correct rel_alt)

lemma (in uprio_isEmpty) autoref_is_empty[autoref_rules]:
  "\<And>Re Ra. PREFER_id Re \<Longrightarrow> (isEmpty,op_uprio_is_empty)\<in>\<langle>Re,Ra\<rangle>rel\<rightarrow>bool_rel"
  by (auto simp: isEmpty_correct rel_alt intro!: ext)

lemma (in uprio_prio) autoref_prio[autoref_rules]:
  "\<And>Re Ra. PREFER_id Re \<Longrightarrow> (prio,op_uprio_prio)\<in>\<langle>Re,Ra\<rangle>rel\<rightarrow>Re\<rightarrow>\<langle>Ra\<rangle>option_rel"
  by (auto simp: prio_correct rel_alt intro!: ext)

lemma (in uprio_insert) autoref_insert[autoref_rules]:
  "\<And>Re Ra. PREFER_id Re \<Longrightarrow> (insert,op_uprio_insert)\<in>\<langle>Re,Ra\<rangle>rel\<rightarrow>Re\<rightarrow>Ra\<rightarrow>\<langle>Re,Ra\<rangle>rel"
  by (auto simp: insert_correct rel_alt intro!: ext)

lemma (in uprio_pop) autoref_prio_pop_min[autoref_rules]:
  "\<And>Re Ra. \<lbrakk>PREFER_id Re; PREFER_id Ra \<rbrakk> 
  \<Longrightarrow> (\<lambda>s. RETURN (pop s),prio_pop_min)\<in>\<langle>Re,Ra\<rangle>rel\<rightarrow>\<langle>\<langle>Re,\<langle>Ra,\<langle>Re,Ra\<rangle>rel\<rangle>prod_rel\<rangle>prod_rel\<rangle>nres_rel"
  apply simp
  apply (intro fun_relI nres_relI)
  by (rule prio_pop_min_refine)




context set begin
  definition rel_def_internal: "rel R \<equiv> br \<alpha> invar O \<langle>R\<rangle>set_rel"
  lemma rel_def: "\<langle>R\<rangle>rel \<equiv> br \<alpha> invar O \<langle>R\<rangle>set_rel" 
    by (simp add: rel_def_internal relAPP_def)
    
  lemma rel_id[simp]: "\<langle>Id\<rangle>rel = br \<alpha> invar" by (simp add: rel_def)

  lemma rel_sv[relator_props]: "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>rel)"
    unfolding rel_def by tagged_solver

  lemmas [autoref_rel_intf] = REL_INTFI[of rel i_set]

end

context map begin
  definition rel_def_internal: 
    "rel Rk Rv \<equiv> br \<alpha> invar O (Rk \<rightarrow> \<langle>Rv\<rangle> option_rel)"
  lemma rel_def: 
    "\<langle>Rk,Rv\<rangle>rel \<equiv> br \<alpha> invar O (Rk \<rightarrow> \<langle>Rv\<rangle> option_rel)" 
    by (simp add: rel_def_internal relAPP_def)
    
  lemma rel_id[simp]: "\<langle>Id,Id\<rangle>rel = br \<alpha> invar" 
    by (simp add: rel_def)

  lemma rel_sv[relator_props]: 
    "\<lbrakk>Range Rk = UNIV; single_valued Rv\<rbrakk> \<Longrightarrow> single_valued (\<langle>Rk,Rv\<rangle>rel)"
    unfolding rel_def 
    by (tagged_solver (trace))

  lemmas [autoref_rel_intf] = REL_INTFI[of rel i_map]

end


(*
context list begin
  definition rel_def_internal: 
    "rel R \<equiv> br \<alpha> invar O R"
  lemma rel_def: "\<langle>R\<rangle>rel \<equiv> br \<alpha> invar O R" 
    by (simp add: rel_def_internal relAPP_def)
    
  lemma rel_id[simp]: "\<langle>Id\<rangle>rel = br \<alpha> invar" 
    by (simp add: rel_def)

  lemma rel_sv[relator_props]: "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>rel)"
    unfolding rel_def by refine_post
end

context al begin
  definition rel_def_internal: 
    "rel Re Ra \<equiv> br \<alpha> invar O \<langle>\<langle>Re,Ra\<rangle> prod_rel\<rangle>list_rel"
  lemma rel_def: 
    "\<langle>Re,Ra\<rangle>rel \<equiv> br \<alpha> invar O \<langle>\<langle>Re,Ra\<rangle> prod_rel\<rangle>list_rel" 
    by (simp add: rel_def_internal relAPP_def)
    
  lemma rel_id[simp]: "\<langle>Id,Id\<rangle>rel = br \<alpha> invar" 
    by (simp add: rel_def)

  lemma rel_sv[relator_props]: 
    "\<lbrakk>single_valued Re; single_valued Ra\<rbrakk> \<Longrightarrow> single_valued (\<langle>Re,Ra\<rangle>rel)"
    unfolding rel_def by refine_post

end

context prio begin
  (* TODO: Fix that to use multiset_rel! *)
  definition rel_def[simp]: "rel \<equiv> br \<alpha> invar"
  lemma rel_sv: "single_valued rel" unfolding rel_def by refine_post
end

context uprio begin
  definition rel_def_internal: 
    "rel Re Ra \<equiv> br \<alpha> invar O (Re \<rightarrow> \<langle>Ra\<rangle> option_rel)"
  lemma rel_def:
    "\<langle>Re,Ra\<rangle>rel \<equiv> br \<alpha> invar O (Re \<rightarrow> \<langle>Ra\<rangle> option_rel)" 
    by (simp add: rel_def_internal relAPP_def)
    
  lemma rel_id[simp]: "\<langle>Id,Id\<rangle>rel = br \<alpha> invar" 
    by (simp add: rel_def)

  lemma rel_sv[relator_props]: 
    "\<lbrakk>Range Re = UNIV; single_valued Ra\<rbrakk> \<Longrightarrow> single_valued (\<langle>Re,Ra\<rangle>rel)"
    unfolding rel_def by refine_post

end
*)


setup \<open>Revert_Abbrev.revert_abbrev "Autoref_Binding_ICF.*.rel"\<close>




(* TODO: Move *)
lemma Collect_x_x_pairs_rel_image[simp]: "{p. \<exists>x. p = (x, x)}``x = x" 
    by auto


subsection "Set"

lemma (in set_empty) empty_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (empty (), {}) \<in> \<langle>Rk\<rangle>rel"
  by (simp add: br_def empty_correct)

lemma (in set_memb) memb_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (memb,(\<in>))\<in>Rk\<rightarrow>\<langle>Rk\<rangle>rel\<rightarrow>Id"
  apply simp
  by (auto simp add: memb_correct br_def)

lemma (in set_ins) ins_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (ins,Set.insert)\<in>Rk\<rightarrow>\<langle>Rk\<rangle>rel\<rightarrow>\<langle>Rk\<rangle>rel"
  by simp (auto simp add: ins_correct br_def)

context set_ins_dj begin
context begin interpretation autoref_syn .
lemma ins_dj_autoref[autoref_rules]: 
  assumes "SIDE_PRECOND_OPT (x'\<notin>s')"
  assumes "PREFER_id Rk"
  assumes "(x,x')\<in>Rk"
  assumes "(s,s')\<in>\<langle>Rk\<rangle>rel"
  shows "(ins_dj x s,(OP Set.insert ::: Rk \<rightarrow> \<langle>Rk\<rangle>rel \<rightarrow> \<langle>Rk\<rangle>rel)$x'$s')\<in>\<langle>Rk\<rangle>rel"
  using assms 
  apply simp
  apply (auto simp add: ins_dj_correct br_def)
  done
end
end

lemma (in set_delete) delete_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (delete,op_set_delete)\<in>Rk\<rightarrow>\<langle>Rk\<rangle>rel\<rightarrow>\<langle>Rk\<rangle>rel"
  by simp (auto simp add: delete_correct op_set_delete_def br_def)
 
lemma (in set_isEmpty) isEmpty_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (isEmpty,op_set_isEmpty) \<in> \<langle>Rk\<rangle>rel\<rightarrow>Id"
  apply (simp add: br_def)
  apply (fastforce simp: isEmpty_correct)
  done

lemma (in set_isSng) isSng_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (isSng,op_set_isSng) \<in> \<langle>Rk\<rangle>rel\<rightarrow>Id"
  by simp
    (auto simp add: isSng_correct op_set_isSng_def br_def card_Suc_eq)

lemma (in set_ball) ball_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (ball,Set.Ball) \<in> \<langle>Rk\<rangle>rel\<rightarrow>(Rk\<rightarrow>Id)\<rightarrow>Id"
  by simp (auto simp add: ball_correct fun_rel_def br_def)

lemma (in set_bex) bex_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (bex,Set.Bex) \<in> \<langle>Rk\<rangle>rel\<rightarrow>(Rk\<rightarrow>Id)\<rightarrow>Id"
  apply simp
  apply (auto simp: bex_correct fun_rel_def br_def intro!: ext)
  done

lemma (in set_size) size_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (size,card) \<in> \<langle>Rk\<rangle>rel \<rightarrow> Id"
  by simp (auto simp add: size_correct br_def)

lemma (in set_size_abort) size_abort_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (size_abort,op_set_size_abort) \<in> Id \<rightarrow> \<langle>Rk\<rangle>rel \<rightarrow> Id"
  by simp
    (auto simp add: size_abort_correct op_set_size_abort_def br_def)

lemma (in set_union) union_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (union,(\<union>))\<in>\<langle>Rk\<rangle>s1.rel\<rightarrow>\<langle>Rk\<rangle>s2.rel\<rightarrow>\<langle>Rk\<rangle>s3.rel"
  by simp (auto simp add: union_correct br_def)

context set_union_dj begin
context begin interpretation autoref_syn .

lemma union_dj_autoref[autoref_rules]:
  assumes "PREFER_id Rk"
  assumes "SIDE_PRECOND_OPT (a'\<inter>b'={})"
  assumes "(a,a')\<in>\<langle>Rk\<rangle>s1.rel"
  assumes "(b,b')\<in>\<langle>Rk\<rangle>s2.rel"
  shows "(union_dj a b,(OP (\<union>) ::: \<langle>Rk\<rangle>s1.rel \<rightarrow> \<langle>Rk\<rangle>s2.rel \<rightarrow> \<langle>Rk\<rangle>s3.rel)$a'$b')
    \<in>\<langle>Rk\<rangle>s3.rel"
  using assms 
  by simp (auto simp: union_dj_correct br_def)
end 
end

lemma (in set_diff) diff_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (diff,(-))\<in>\<langle>Rk\<rangle>s1.rel\<rightarrow>\<langle>Rk\<rangle>s2.rel\<rightarrow>\<langle>Rk\<rangle>s1.rel"
  by simp (auto simp add: diff_correct br_def)

lemma (in set_filter) filter_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (filter,op_set_filter)\<in>(Rk \<rightarrow> Id) \<rightarrow> \<langle>Rk\<rangle>s1.rel\<rightarrow>\<langle>Rk\<rangle>s2.rel"
  by simp (auto simp add: filter_correct op_set_filter_def fun_rel_def 
    br_def)

lemma (in set_inter) inter_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (inter,(\<inter>))\<in>\<langle>Rk\<rangle>s1.rel\<rightarrow>\<langle>Rk\<rangle>s2.rel\<rightarrow>\<langle>Rk\<rangle>s3.rel"
  by simp (auto simp add: inter_correct br_def)

lemma (in set_subset) subset_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (subset,(\<subseteq>))\<in>\<langle>Rk\<rangle>s1.rel\<rightarrow>\<langle>Rk\<rangle>s2.rel\<rightarrow>Id"
  by simp (auto simp add: subset_correct br_def)

lemma (in set_equal) equal_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (equal,(=))\<in>\<langle>Rk\<rangle>s1.rel\<rightarrow>\<langle>Rk\<rangle>s2.rel\<rightarrow>Id"
  by simp (auto simp add: equal_correct br_def)

lemma (in set_disjoint) disjoint_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (disjoint,op_set_disjoint)\<in>\<langle>Rk\<rangle>s1.rel\<rightarrow>\<langle>Rk\<rangle>s2.rel\<rightarrow>Id"
  by simp (auto simp add: disjoint_correct op_set_disjoint_def br_def)

lemma (in list_to_set) to_set_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (to_set,set)\<in>\<langle>Rk\<rangle>list_rel \<rightarrow> \<langle>Rk\<rangle>rel"
  apply simp
  apply (auto simp add: to_set_correct br_def)
  done

context set_sel' begin
context begin interpretation autoref_syn .

lemma autoref_op_set_pick[autoref_rules]: 
  assumes "SIDE_PRECOND (s'\<noteq>{})"
  assumes "PREFER_id Rk"
  assumes "(s,s')\<in>\<langle>Rk\<rangle>rel"
  shows "(RETURN (the (sel' s (\<lambda>_. True))), 
          (OP op_set_pick ::: \<langle>Rk\<rangle>rel \<rightarrow> \<langle>Rk\<rangle>nres_rel) $ s')
    \<in> \<langle>Rk\<rangle>nres_rel"
  using assms
  apply (clarsimp simp add: br_def nres_rel_def ex_in_conv[symmetric])
  apply (erule (1) sel'E[OF _ _ TrueI])
  apply (auto intro: RES_refine)
  done
end
end

lemma (in poly_set_iteratei) proper[proper_it]:
  "proper_it' iteratei iteratei"
  apply (rule proper_it'I)
  by (rule pi_iteratei)

lemma (in poly_set_iteratei) autoref_iteratei[autoref_ga_rules]: 
  "REL_IS_ID Rk \<Longrightarrow> is_set_to_list Rk rel (it_to_list iteratei)"
  unfolding is_set_to_list_def is_set_to_sorted_list_def it_to_list_def 
    it_to_sorted_list_def
  apply (simp add: br_def, intro allI impI)
  apply (drule iteratei_correct)
  unfolding set_iterator_def set_iterator_genord_foldli_conv
  apply (elim exE)
  apply clarsimp
  apply (drule fun_cong[where x="\<lambda>_::'x list. True"])
  apply simp
  done

lemma (in poly_set_iterateoi) proper_o[proper_it]:
  "proper_it' iterateoi iterateoi"
  apply (rule proper_it'I)
  by (rule pi_iterateoi)

lemma (in poly_set_iterateoi) autoref_iterateoi[autoref_ga_rules]: 
  "REL_IS_ID Rk \<Longrightarrow> 
    is_set_to_sorted_list (\<le>) Rk rel (it_to_list iterateoi)"
  unfolding is_set_to_sorted_list_def it_to_list_def it_to_sorted_list_def
  apply (simp add: br_def, intro allI impI)
  apply (drule iterateoi_correct)
  unfolding set_iterator_linord_def set_iterator_genord_foldli_conv
  apply (elim exE)
  apply clarsimp
  apply (drule fun_cong[where x="\<lambda>_::'x list. True"])
  apply simp
  done

lemma (in poly_set_rev_iterateoi) autoref_rev_iterateoi[autoref_ga_rules]: 
  "REL_IS_ID Rk \<Longrightarrow> 
    is_set_to_sorted_list (\<ge>) Rk rel (it_to_list rev_iterateoi)"
  unfolding is_set_to_sorted_list_def it_to_list_def it_to_sorted_list_def
  apply (simp add: br_def, intro allI impI)
  apply (drule rev_iterateoi_correct)
  unfolding set_iterator_rev_linord_def set_iterator_genord_foldli_conv
  apply (elim exE)
  apply clarsimp
  apply (drule fun_cong[where x="\<lambda>_::'x list. True"])
  apply simp
  done

lemma (in poly_set_rev_iterateoi) proper_ro[proper_it]:
  "proper_it' rev_iterateoi rev_iterateoi"
  apply (rule proper_it'I)
  by (rule pi_rev_iterateoi)

subsection "Map"

lemma (in map) rel_alt: "\<langle>Id,Rv\<rangle>rel = 
  { (c,a). \<forall>x. (\<alpha> c x,a x)\<in>\<langle>Rv\<rangle>option_rel \<and> invar c }"
  by (auto simp: rel_def br_def dest: fun_relD)

lemma (in map_empty) empty_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (empty (),op_map_empty)\<in>\<langle>Rk,Rv\<rangle>rel"
  by (auto simp: empty_correct rel_alt)
  
lemma (in map_lookup) lookup_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (lookup,op_map_lookup)\<in>Rk\<rightarrow>\<langle>Rk,Rv\<rangle>rel\<rightarrow>\<langle>Rv\<rangle>option_rel"
  apply (intro fun_relI option_relI)
  apply (auto simp: lookup_correct rel_alt
    dest: fun_relD2)
  done

lemma (in map_update) update_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (update,op_map_update)\<in>Rk\<rightarrow>Rv\<rightarrow>\<langle>Rk,Rv\<rangle>rel\<rightarrow>\<langle>Rk,Rv\<rangle>rel"
  apply (intro fun_relI)
  apply (simp add: update_correct rel_alt)
  done

context map_update_dj begin
context begin interpretation autoref_syn .

lemma update_dj_autoref[autoref_rules]: 
  assumes "SIDE_PRECOND_OPT (k'\<notin>dom m')"
  assumes "PREFER_id Rk"
  assumes "(k,k')\<in>Rk"
  assumes "(v,v')\<in>Rv"
  assumes "(m,m')\<in>\<langle>Rk,Rv\<rangle>rel"
  shows "(update_dj k v m,
    (OP op_map_update ::: Rk \<rightarrow> Rv \<rightarrow> \<langle>Rk,Rv\<rangle>rel \<rightarrow> \<langle>Rk,Rv\<rangle>rel)$k'$v'$m'
  )\<in>\<langle>Rk,Rv\<rangle>rel"
  using assms
  apply (subgoal_tac "k\<notin>dom (\<alpha> m)")
  apply (simp add: update_dj_correct rel_alt)
  apply (auto simp add: rel_alt option_rel_def)
  apply (metis option.simps(3))
  done
end
end

lemma (in map_delete) delete_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (delete,op_map_delete)\<in>Rk\<rightarrow>\<langle>Rk,Rv\<rangle>rel\<rightarrow>\<langle>Rk,Rv\<rangle>rel"
  apply (intro fun_relI)
  apply (simp add: delete_correct restrict_map_def rel_alt)
  done

lemma (in map_restrict) restrict_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> 
    (restrict,op_map_restrict) 
    \<in> (\<langle>Rk,Rv\<rangle>prod_rel \<rightarrow> Id) \<rightarrow> \<langle>Rk,Rv\<rangle>m1.rel \<rightarrow> \<langle>Rk,Rv\<rangle>m2.rel"
  apply (intro fun_relI)
  apply (simp add: restrict_correct br_comp_alt m1.rel_def m2.rel_def )
  apply (intro fun_relI)
  apply (auto simp: restrict_map_def split: if_split_asm)
  apply (drule (1) fun_relD1)
  apply (auto simp: option_rel_def) []
  apply (drule (1) fun_relD1)
  apply (auto simp: option_rel_def) []
  apply (drule (1) fun_relD1)
  apply (auto simp: option_rel_def prod_rel_def fun_rel_def) []
  apply (drule (1) fun_relD2)
  apply (auto simp: option_rel_def prod_rel_def fun_rel_def) []
  done

lemma (in map_add) add_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (add,(++))\<in>\<langle>Rk,Rv\<rangle>rel\<rightarrow>\<langle>Rk,Rv\<rangle>rel\<rightarrow>\<langle>Rk,Rv\<rangle>rel"
  apply (auto simp add: add_correct rel_alt Map.map_add_def
    split: option.split)
  apply (drule_tac x=x in spec)+
  apply simp
  apply (metis option.simps(3) option_rel_simp(2))
  by (metis (lifting) option_rel_simp(3))


context map_add_dj begin
context begin interpretation autoref_syn .

lemma add_dj_autoref[autoref_rules]: 
  assumes "PREFER_id Rk"
  assumes "SIDE_PRECOND_OPT (dom a' \<inter> dom b' = {})"
  assumes "(a,a')\<in>\<langle>Rk,Rv\<rangle>rel"
  assumes "(b,b')\<in>\<langle>Rk,Rv\<rangle>rel"
  shows "(add_dj a b, (OP (++) ::: \<langle>Rk,Rv\<rangle>rel \<rightarrow> \<langle>Rk,Rv\<rangle>rel \<rightarrow> \<langle>Rk,Rv\<rangle>rel) $ a' $ b')\<in>\<langle>Rk,Rv\<rangle>rel"
  using assms
  apply simp
  apply (subgoal_tac "dom (\<alpha> a) \<inter> dom (\<alpha> b) = {}")
  apply (clarsimp simp add: add_dj_correct rel_def br_comp_alt)
  apply (auto 
    simp add: rel_def br_comp_alt Map.map_add_def
    split: option.split
    elim: fun_relE1 dest: fun_relD1 intro: option_relI
  ) []

  apply (clarsimp simp add: rel_def br_comp_alt)

  apply (auto simp: dom_def)
  apply (drule (1) fun_relD1)
  apply (drule (1) fun_relD1)
  apply (auto simp: option_rel_def)
  done
end
end

lemma (in map_isEmpty) isEmpty_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (isEmpty,op_map_isEmpty)\<in>\<langle>Rk,Rv\<rangle>rel\<rightarrow>Id"
  by (auto simp: isEmpty_correct rel_alt
    intro!: ext)

lemma sngI: 
  assumes "m k = Some v"
  assumes "\<forall>k'. k'\<noteq>k \<longrightarrow> m k' = None"
  shows "m = [k\<mapsto>v]"
  using assms
  by (auto intro!: ext)

lemma (in map_isSng) isSng_autoref[autoref_rules]: 
  "PREFER_id Rk \<Longrightarrow> (isSng,op_map_isSng)\<in>\<langle>Rk,Rv\<rangle>rel\<rightarrow>Id"
  (* TODO: Clean up this mess *)
  apply (auto simp add: isSng_correct rel_alt)
  apply (rule_tac x=k in exI)
  apply (rule_tac x="the (a' k)" in exI)
  apply (rule sngI)
  apply (drule_tac x=k in spec)
  apply (auto elim: option_relE) []
  apply (force elim: option_relE) []

  apply (rule_tac x=k in exI)
  apply (rule_tac x="the (\<alpha> a k)" in exI)
  apply (rule sngI)
  apply (drule_tac x=k in spec)
  apply (auto elim: option_relE) []
  apply (force elim: option_relE) []
  done

lemma (in map_ball) ball_autoref[autoref_rules]:
  "PREFER_id Rk \<Longrightarrow> (ball,op_map_ball)\<in>\<langle>Rk,Rv\<rangle>rel\<rightarrow>(\<langle>Rk,Rv\<rangle>prod_rel\<rightarrow>Id)\<rightarrow>Id"
  apply (auto simp: ball_correct rel_alt map_to_set_def
    option_rel_def prod_rel_def fun_rel_def)
  apply (metis option.inject option.simps(3))+
  done

lemma (in map_bex) bex_autoref[autoref_rules]:
  "PREFER_id Rk \<Longrightarrow> (bex,op_map_bex)\<in>\<langle>Rk,Rv\<rangle>rel\<rightarrow>(\<langle>Rk,Rv\<rangle>prod_rel\<rightarrow>Id)\<rightarrow>Id"
  apply (auto simp: bex_correct map_to_set_def rel_alt 
    option_rel_def prod_rel_def fun_rel_def)
  apply (metis option.inject option.simps(3))+
  done

lemma (in map_size) size_autoref[autoref_rules]:
  "PREFER_id Rk \<Longrightarrow> (size,op_map_size)\<in>\<langle>Rk,Rv\<rangle>rel\<rightarrow>Id"
  apply (auto simp: size_correct rel_alt option_rel_def dom_def 
    intro!: arg_cong[where f=card])
  apply (metis option.simps(3))+
  done

lemma (in map_size_abort) size_abort_autoref[autoref_rules]:
  "PREFER_id Rk \<Longrightarrow> (size_abort,op_map_size_abort)\<in>Id\<rightarrow>\<langle>Rk,Rv\<rangle>rel\<rightarrow>Id"
  apply (auto simp: size_abort_correct  
    rel_alt option_rel_def
    dom_def intro!: arg_cong[where f=card] cong[OF arg_cong[where f=min]])
  apply (metis option.simps(3))+
  done

lemma (in list_to_map) to_map_autoref[autoref_rules]:
  "PREFER_id Rk \<Longrightarrow> (to_map,map_of)\<in> \<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel \<rightarrow> \<langle>Rk,Rv\<rangle>rel"
proof (intro fun_relI)
  fix l :: "('u\<times>'v) list" and l' :: "('u\<times>'a) list"
  assume "PREFER_id Rk" hence [simp]: "Rk=Id" by simp
  assume "(l,l')\<in>\<langle>\<langle>Rk,Rv\<rangle>prod_rel\<rangle>list_rel"
  thus "(to_map l, map_of l') \<in> \<langle>Rk,Rv\<rangle>rel"
    apply (simp add: list_rel_def)
  proof (induct rule: list_all2_induct)
    case Nil thus ?case 
      by (auto simp add: to_map_correct rel_alt)
  next
    case (Cons x x' l l') thus ?case
      by (auto simp add: to_map_correct 
        rel_alt prod_rel_def)
  qed
qed

(* TODO: Move *)
lemma key_rel_true[simp]: "key_rel (\<lambda>_ _. True) = (\<lambda>_ _. True)"
  by (auto intro!: ext simp: key_rel_def)


lemma (in poly_map_iteratei) proper[proper_it]:
  "proper_it' iteratei iteratei"
  apply (rule proper_it'I)
  by (rule pi_iteratei)

lemma (in poly_map_iteratei) autoref_iteratei[autoref_ga_rules]: 
  assumes ID: "REL_IS_ID Rk"
    "REL_IS_ID Rv" (* TODO: Unnecessary*)
  shows "is_map_to_list Rk Rv rel (it_to_list iteratei)"
proof -
  from ID have [simp]: "Rk=Id" "Rv = Id" by simp_all

  show ?thesis
    unfolding is_map_to_sorted_list_def is_map_to_list_def
      it_to_sorted_list_def
    apply simp
    apply (intro allI impI conjI)
  proof -
    fix m m'
    assume "(m, m') \<in> br \<alpha> invar"
    hence I: "invar m" and M': "m' = \<alpha> m" by (simp_all add: br_def)

    have [simp]: "\<And>c. (\<lambda>(_,_). c) = (\<lambda>_. c)" by auto

    from map_it_to_list_genord_correct[where it = iteratei, 
      where R="\<lambda>_ _. True", simplified, OF 
      iteratei_correct[OF I, unfolded set_iterator_def]
    ] have 
        M: "Map.map_of (it_to_list iteratei m) = \<alpha> m"
        and D: "distinct (List.map fst (it_to_list iteratei m))"
      by (simp_all)

    from D show "distinct (it_to_list iteratei m)"
      by (rule distinct_mapI)

    from M show "map_to_set m' = set (it_to_list iteratei m)"
      by (simp add: M' map_of_map_to_set[OF D])
  qed
qed

lemma (in poly_map_iterateoi) proper_o[proper_it]:
  "proper_it' iterateoi iterateoi"
  apply (rule proper_it'I)
  by (rule pi_iterateoi)

lemma (in poly_map_iterateoi) autoref_iterateoi[autoref_ga_rules]: 
  assumes ID: "REL_IS_ID Rk"
    "REL_IS_ID Rv" (* TODO: Unnecessary*)
  shows "is_map_to_sorted_list (\<le>) Rk Rv rel (it_to_list iterateoi)"
proof -
  from ID have [simp]: "Rk=Id" "Rv = Id" by simp_all

  show ?thesis
    unfolding is_map_to_sorted_list_def
      it_to_sorted_list_def
    apply simp
    apply (intro allI impI conjI)
  proof -
    fix m m'
    assume "(m, m') \<in> br \<alpha> invar"
    hence I: "invar m" and M': "m' = \<alpha> m" by (simp_all add: br_def)

    have [simp]: "\<And>c. (\<lambda>(_,_). c) = (\<lambda>_. c)" by auto

    from map_it_to_list_linord_correct[where it = iterateoi, 
      OF iterateoi_correct[OF I]
    ] have 
        M: "map_of (it_to_list iterateoi m) = \<alpha> m"
        and D: "distinct (map fst (it_to_list iterateoi m))"
        and S: "sorted (map fst (it_to_list iterateoi m))"
      by (simp_all)

    from D show "distinct (it_to_list iterateoi m)"
      by (rule distinct_mapI)

    from M show "map_to_set m' = set (it_to_list iterateoi m)"
      by (simp add: M' map_of_map_to_set[OF D])

    from S show "sorted_wrt (key_rel (\<le>)) (it_to_list iterateoi m)"
      by (simp add: key_rel_def[abs_def])

  qed
qed

lemma (in poly_map_rev_iterateoi) proper_ro[proper_it]:
  "proper_it' rev_iterateoi rev_iterateoi"
  apply (rule proper_it'I)
  by (rule pi_rev_iterateoi)

lemma (in poly_map_rev_iterateoi) autoref_rev_iterateoi[autoref_ga_rules]: 
  assumes ID: "REL_IS_ID Rk"
    "REL_IS_ID Rv" (* TODO: Unnecessary*)
  shows "is_map_to_sorted_list (\<ge>) Rk Rv rel (it_to_list rev_iterateoi)"
proof -
  from ID have [simp]: "Rk=Id" "Rv = Id" by simp_all

  show ?thesis
    unfolding is_map_to_sorted_list_def
      it_to_sorted_list_def
    apply simp
    apply (intro allI impI conjI)
  proof -
    fix m m'
    assume "(m, m') \<in> br \<alpha> invar"
    hence I: "invar m" and M': "m' = \<alpha> m" by (simp_all add: br_def)

    have [simp]: "\<And>c. (\<lambda>(_,_). c) = (\<lambda>_. c)" by auto

    from map_it_to_list_rev_linord_correct[where it = rev_iterateoi, 
      OF rev_iterateoi_correct[OF I]
    ] have 
        M: "map_of (it_to_list rev_iterateoi m) = \<alpha> m"
        and D: "distinct (map fst (it_to_list rev_iterateoi m))"
        and S: "sorted (rev (map fst (it_to_list rev_iterateoi m)))"
      by (simp_all)

    from D show "distinct (it_to_list rev_iterateoi m)"
      by (rule distinct_mapI)

    from M show "map_to_set m' = set (it_to_list rev_iterateoi m)"
      by (simp add: M' map_of_map_to_set[OF D])

    from S show "sorted_wrt (key_rel (\<ge>)) (it_to_list rev_iterateoi m)"
      by (simp add: key_rel_def[abs_def])

  qed
qed

end
