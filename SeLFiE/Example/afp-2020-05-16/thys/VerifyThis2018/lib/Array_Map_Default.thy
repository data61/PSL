section \<open>Options and Maps with Default Value for None\<close>
theory Array_Map_Default
imports Dynamic_Array DRAT_Misc
begin
  text \<open>Implements maps from natural numbers to any value type that has an 
    unused default value in its implementation type. 
    Internally, uses a dynamic array.
    \<close>
  definition "is_unused_elem dflt A \<equiv> \<forall>x. A x dflt = false"
  lemma is_unused_elem_pure[simp]: 
    "is_unused_elem dflt (pure R) \<longleftrightarrow> dflt \<notin> Domain R"
    unfolding is_unused_elem_def
    by (auto simp: pure_rel_eq_false_iff)
  
  
  definition "dflt_option_rel_aux dflt 
    \<equiv> { (dflt,None) } \<union> { (x, Some x) | x. x\<noteq>dflt }"
  definition [to_relAPP]: "dflt_option_assn dflt A 
    \<equiv> pure (dflt_option_rel_aux dflt O \<langle>the_pure A\<rangle>option_rel)"
  
  subsection \<open>Function-Level Map Operations\<close>  
  text \<open>We justify the map operations implemented by a function\<close>
  lemma amd1_empty_refine: 
    "(uncurry0 (\<lambda>_. dflt), uncurry0 op_map_empty) 
    \<in> Id \<rightarrow>\<^sub>f (Id \<rightarrow> dflt_option_rel_aux dflt)"
    by (auto simp: dflt_option_rel_aux_def fref_def)
  
  lemma amd1_lookup_refine: 
    "(\<lambda>x f. f x, op_map_lookup) 
    \<in> Id \<rightarrow> (Id \<rightarrow> dflt_option_rel_aux dflt) \<rightarrow> dflt_option_rel_aux dflt"
    apply simp by parametricity
  
  lemma amd1_update_refine: 
    "(uncurry2 (\<lambda>k v f. f(k:=v)), uncurry2 op_map_update) 
    \<in> [\<lambda>((k,v),m). v\<noteq>dflt]\<^sub>f 
      ((Id \<times>\<^sub>r Id) \<times>\<^sub>r (Id \<rightarrow> dflt_option_rel_aux dflt)) 
      \<rightarrow> (Id \<rightarrow> dflt_option_rel_aux dflt)"
    unfolding op_map_update_def
    apply (rule frefI)
    apply auto
    applyS (auto simp: dflt_option_rel_aux_def)
    applyS (parametricity; simp)
    done
  
  definition [simp]: "amd1_delete dflt k f \<equiv> fun_upd f k dflt"
  lemma amd1_delete_refine: 
    "(uncurry (amd1_delete dflt), uncurry op_map_delete) 
    \<in> Id \<times>\<^sub>r (Id \<rightarrow> dflt_option_rel_aux dflt) \<rightarrow>\<^sub>f (Id \<rightarrow> dflt_option_rel_aux dflt)"
    unfolding op_map_delete_def PR_CONST_def amd1_delete_def
    apply (rule frefI)
    apply parametricity
    apply (auto simp: dflt_option_rel_aux_def)
    done

  subsection \<open>Map Operations, array-level\<close>
  text \<open>We use dynamic arrays to implement the function, and combine both to 
      implement the map interface.\<close>
  definition [code_unfold]: "amd_empty dflt \<equiv> dyn_array_new_sz dflt 16"
  definition [code_unfold]: "amd_lookup dflt k a \<equiv> array_get_dyn dflt a k"
  definition [code_unfold]: "amd_update dflt k v a \<equiv> array_set_dyn dflt a k v"
  definition [code_unfold]: "amd_delete dflt k a \<equiv> array_set_dyn dflt a k dflt"
 
  definition "amd_assn dflt K V 
    \<equiv> hr_comp (hr_comp 
        (is_nff dflt) 
        (nat_rel \<rightarrow>\<^sub>f dflt_option_rel_aux dflt)) 
        (\<langle>the_pure K, the_pure V\<rangle>map_rel)"
    
  lemma amd_assn_fold2: "hr_comp (hr_comp 
      (is_nff dflt) 
      (nat_rel \<rightarrow> dflt_option_rel_aux dflt)) 
      (\<langle>the_pure K, the_pure V\<rangle>map_rel) 
    = amd_assn dflt K V"
    unfolding amd_assn_def
    apply (fo_rule fun_cong arg_cong)+
    unfolding fref_def fun_rel_def by auto
  
  (* TODO: Move *)
  lemmas [intf_of_assn] 
    = intf_of_assnI[where R="amd_assn dflt K V" 
                      and 'a="(nat,'vv) i_map" for dflt K V]
  
  lemmas [safe_constraint_rules] 
    = CN_FALSEI[of is_pure "amd_assn dflt K V" for dflt K V]
    
    
context 
  notes [fcomp_norm_unfold] = 
    amd_assn_def[symmetric] dflt_option_assn_def[symmetric] amd_assn_fold2
  notes [intro!] = hfrefI hn_refineI[THEN hn_refine_preI]
  notes [simp] = pure_def hn_ctxt_def invalid_assn_def 
  fixes dflt :: "'a::heap"
begin  
  lemma amd2_empty_refine: 
    "(uncurry0 (amd_empty dflt), uncurry0 (RETURN (\<lambda>_. dflt))) 
    \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a is_nff dflt"
    by (sep_auto simp: amd_empty_def)

  lemma amd2_lookup_refine: 
    "(uncurry (amd_lookup dflt), uncurry (RETURN oo (\<lambda>x f. f x))) 
    \<in> id_assn\<^sup>k*\<^sub>a(is_nff dflt)\<^sup>k \<rightarrow>\<^sub>a id_assn"  
    by (sep_auto simp: amd_lookup_def)

  lemma amd2_update_refine: 
    "(uncurry2 (amd_update dflt), uncurry2 (RETURN ooo (\<lambda>k v f. f(k:=v)))) 
    \<in> id_assn\<^sup>k*\<^sub>aid_assn\<^sup>k*\<^sub>a(is_nff dflt)\<^sup>d \<rightarrow>\<^sub>a is_nff dflt"
    by (sep_auto simp: amd_update_def)

  lemma amd2_delete_refine: 
    "(uncurry (amd_delete dflt), uncurry (RETURN oo (amd1_delete dflt))) 
    \<in> id_assn\<^sup>k*\<^sub>a(is_nff dflt)\<^sup>d \<rightarrow>\<^sub>a is_nff dflt"
    by (sep_auto simp: amd_delete_def)
  
  sepref_decl_impl (no_register) amd_empty: 
    amd2_empty_refine[FCOMP amd1_empty_refine[where dflt=dflt]] .
      
  definition [simp]: "op_amd_empty \<equiv> op_map_empty"    
    
  sepref_decl_impl 
    amd2_lookup_refine[FCOMP amd1_lookup_refine[where dflt=dflt]] .
  sepref_decl_impl 
    amd2_delete_refine[FCOMP amd1_delete_refine[where dflt=dflt]] .

  text \<open>The only complication arises for the update operation, where we have 
    to use the fact that the default element is invalid, which forces us to do
    a manual composition proof.\<close>
  lemma amd2_update_hnr_aux:
    assumes "CONSTRAINT (IS_PURE single_valued) K"
      and "CONSTRAINT (IS_PURE IS_LEFT_UNIQUE) K"
      and "CONSTRAINT is_pure V"
      and "CONSTRAINT (is_unused_elem dflt) V"
    shows "(uncurry2 (amd_update dflt), uncurry2 (RETURN \<circ>\<circ>\<circ> op_map_update))
           \<in>  K\<^sup>k *\<^sub>a V\<^sup>k *\<^sub>a (amd_assn dflt K V)\<^sup>d \<rightarrow>\<^sub>a amd_assn dflt K V"    
    apply (rule 
        hfref_cons[
          OF amd2_update_refine[
                FCOMP amd1_update_refine[where dflt=dflt], 
                FCOMP (no_prenorm) op_map_update.fref, of K V]])
    subgoal using assms by (simp add: IS_PURE_def)
    subgoal using assms by (simp add: IS_PURE_def)
    subgoal using assms by (simp add: IS_PURE_def)
    subgoal using assms by (simp add: IS_PURE_def IS_LEFT_UNIQUE_def)
    subgoal
      using assms
      by (auto 
          simp del: pure_def
          simp: comp_PRE_def IS_PURE_def is_unused_elem_def is_pure_conv 
          simp: pure_rel_eq_false_iff 
          elim!: prod_relE)
    applyS simp
    applyS simp
    applyS simp
    done

  (* TODO: Somewhat of a hack. Perhaps add a flag to switch of 
      automatic parameterization on sepref_decl_impl? *)
  private lemma op_map_update_id_param: 
    "(uncurry2 (RETURN \<circ>\<circ>\<circ> op_map_update), uncurry2 (RETURN \<circ>\<circ>\<circ> op_map_update)) 
    \<in> (Id\<times>\<^sub>rId)\<times>\<^sub>rId \<rightarrow>\<^sub>f \<langle>Id\<rangle>nres_rel" 
    by (simp add: fref_def nres_rel_def)
  
  sepref_decl_impl amd2_update_hnr_aux uses op_map_update_id_param .

end  

interpretation amd: map_custom_empty op_amd_empty apply unfold_locales by auto 
lemmas [sepref_fr_rules] = amd_empty_hnr[folded op_amd_empty_def]
  
  
subsection \<open>Operations on Options\<close>

text \<open>We give own names to constructors, otherwise, we will get confusions 
  with the default option refinement.\<close>
definition [simp]: "dflt_None \<equiv> None"
definition [simp]: "dflt_Some \<equiv> Some"
sepref_register dflt_None dflt_Some

lemma doa_None_hnr: 
  "(uncurry0 (return dflt), uncurry0 (RETURN dflt_None)) 
  \<in> unit_assn\<^sup>k \<rightarrow>\<^sub>a dflt_option_assn dflt A"
  apply (sepref_to_hoare)
  apply (sep_auto simp: pure_def dflt_option_rel_aux_def dflt_option_assn_def)
  done  

lemma doa_Some_hnr: "\<lbrakk>CONSTRAINT (is_unused_elem dflt) A; CONSTRAINT is_pure A\<rbrakk> 
  \<Longrightarrow> (return o (\<lambda>x. x), RETURN o dflt_Some) \<in> A\<^sup>k \<rightarrow>\<^sub>a dflt_option_assn dflt A"
  apply (sepref_to_hoare)
  apply (clarsimp simp: is_pure_conv dflt_option_assn_def)
  apply (sep_auto simp: pure_def)
  apply (fastforce simp: dflt_option_rel_aux_def)
  done  

lemma doa_is_None_hnr[sepref_fr_rules]: 
  "(return o ((=) dflt), RETURN o is_None) 
  \<in> (dflt_option_assn dflt A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  apply (sepref_to_hoare)
  by (sep_auto 
        simp: dflt_option_assn_def pure_def dflt_option_rel_aux_def 
        split: option.split)

lemma doa_the_hnr[sepref_fr_rules]: "\<lbrakk>CONSTRAINT is_pure A\<rbrakk> 
  \<Longrightarrow> (return o (\<lambda>x. x), RETURN o the) 
      \<in> [\<lambda>x. x\<noteq>None]\<^sub>a (dflt_option_assn dflt A)\<^sup>k \<rightarrow> A"
  apply (sepref_to_hoare)
  apply (clarsimp simp: is_pure_conv dflt_option_assn_def)
  apply (sep_auto simp: pure_def dflt_option_rel_aux_def)
  done

(* TODO: Add proper rule for case distinction *)

(* Workaround for case-distinction: Rewrite with abstract-level rule: *)
lemma cnv_option_case_2_if: "(case x of None \<Rightarrow> fn | Some v \<Rightarrow> fv v) 
  \<longleftrightarrow> (if is_None x then fn else fv (the x))" by (cases x) auto


(* TODO: Hack:
  Due to lack of recursive generic algorithms with specialization, 
  we have instantiated equality on options as combinator rule. 
  This allows no backtracking or alternatives.
  Thus, we do a type-based rewriting of option-equalities for dflt-option 
  types in operator-id phase.
*)
definition [simp]: "dflt_option_eq \<equiv> (=)"

locale dflt_option =
  fixes A :: "'a \<Rightarrow> 'c \<Rightarrow> assn"
  fixes dflt :: "'c"
  fixes eq :: "'c \<Rightarrow> 'c \<Rightarrow> bool Heap"
  assumes unused_dflt[safe_constraint_rules]: "(is_unused_elem dflt) A"

  assumes eq_op: "(uncurry eq, uncurry (RETURN oo (=))) \<in> A\<^sup>k*\<^sub>aA\<^sup>k\<rightarrow>\<^sub>abool_assn"
  assumes eq_dflt: "\<And>a b. \<lbrakk> a=dflt \<or> b=dflt \<rbrakk> \<Longrightarrow> <emp> eq a b <\<lambda>r. \<up>(r \<longleftrightarrow> a=b)>\<^sub>t"
begin
  (* Type-based rewrites. 
      TODO: We would prefer type-based specializations in translate-phase! *)
  lemma fold_dflt_option[def_pat_rules]: 
    "(None::'a option) \<equiv> dflt_None"
    "(Some::'a\<Rightarrow>_) \<equiv> dflt_Some"
    "((=)::'a option \<Rightarrow> _) \<equiv> dflt_option_eq"
     by auto

  (* Constructors *)
  lemmas [sepref_fr_rules] = 
    doa_None_hnr[where dflt = dflt and A=A]
    doa_Some_hnr[where dflt = dflt and A=A]

  lemma eq_option_refine[sepref_fr_rules]:
    assumes "CONSTRAINT is_pure A"
    shows "(uncurry eq,uncurry (RETURN oo dflt_option_eq)) 
      \<in> (dflt_option_assn dflt A)\<^sup>k *\<^sub>a (dflt_option_assn dflt A)\<^sup>k \<rightarrow>\<^sub>a bool_assn"
  proof -
    from assms obtain R where [simp]: "A = pure R" by (auto simp: is_pure_conv)
    
    from eq_op have [sep_heap_rules]: 
      "\<lbrakk> (x,x')\<in>R; (y,y')\<in>R \<rbrakk> 
      \<Longrightarrow> <emp> eq x y <\<lambda>r. \<up>(r \<longleftrightarrow> x'=y')>\<^sub>t" for x x' y y'
      apply (drule_tac hfrefD[where a="(x',y')" and c="(x,y)"])
      apply simp
      apply (drule hn_refineD)
      apply simp
      apply (sep_auto simp: pure_def)
      apply (rule Hoare_Triple.cons_post_rule)
      apply assumption
      apply sep_auto
      done
  
    note [simplified,sep_heap_rules] 
      = eq_dflt[of dflt dflt] eq_dflt[of dflt] eq_dflt[of _ dflt] 
    
    show ?thesis
      apply sepref_to_hoare
      apply (simp add: dflt_option_assn_def)
      apply (auto simp: pure_def dflt_option_rel_aux_def elim!: option_relE)
      apply (sep_auto)
      apply (sep_auto)
      apply (sep_auto)
      apply (sep_auto)
      done
  qed  
    
    
    
end

end
