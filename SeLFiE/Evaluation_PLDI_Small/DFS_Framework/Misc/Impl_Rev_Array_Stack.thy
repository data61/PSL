section \<open>Stack by Reversed Array\<close>
theory Impl_Rev_Array_Stack
imports   
  CAVA_Base.CAVA_Base
  DFS_Framework_Refine_Aux
begin
(* TODO: Move theory to GenCF/Impl *)

type_synonym 'a rev_array_stack = "'a array \<times> nat"

term Diff_Array.array_length

definition "ras_raw_\<alpha> s \<equiv> rev (take (snd s) (list_of_array (fst s)))"
definition "ras_raw_invar s \<equiv> snd s \<le> array_length (fst s)"

definition ras_rel_def_internal: "ras_rel R \<equiv> br ras_raw_\<alpha> ras_raw_invar O \<langle>R\<rangle>list_rel"
lemma ras_rel_def: "\<langle>R\<rangle>ras_rel \<equiv> br ras_raw_\<alpha> ras_raw_invar O \<langle>R\<rangle>list_rel"
  unfolding ras_rel_def_internal[abs_def] by (simp add: relAPP_def)


(* TODO: Fix relator-props solver to also include atac! *)
lemma [relator_props]: 
  assumes [relator_props]: "single_valued R" 
  shows "single_valued (\<langle>R\<rangle>ras_rel)"
  unfolding ras_rel_def
  (*apply (tactic {* REPEAT_ALL_NEW (atac ORELSE' (resolve_tac @{thms relator_props})) 1*})*)
  by (tagged_solver)

lemmas [autoref_rel_intf] = REL_INTFI[of ras_rel i_list]


definition "ras_empty (_::unit) \<equiv> (array_of_list [],0)"

lemma ras_empty_refine[autoref_rules]: "(ras_empty (),[]) \<in> \<langle>R\<rangle>ras_rel"
  unfolding ras_rel_def ras_empty_def br_def
  unfolding ras_raw_\<alpha>_def ras_raw_invar_def
  by auto


definition "ras_push x s \<equiv> let
    (a,n)=s;
    a = if n = array_length a then
        array_grow a (max 4 (2*n)) x
      else a;
    a = array_set a n x
  in
    (a,n+1)"

lemma ras_push_refine[autoref_rules]: 
  "(ras_push,(#)) \<in> R \<rightarrow> \<langle>R\<rangle>ras_rel \<rightarrow> \<langle>R\<rangle>ras_rel"
  apply (intro fun_relI)
  apply (simp add: ras_push_def ras_rel_def br_def
    ras_raw_\<alpha>_def ras_raw_invar_def)
  apply clarsimp
  apply safe
  apply (rule)
  apply auto []
  apply (clarsimp simp: array_length_list) []

  apply rule
  apply auto []
  apply (auto simp: take_Suc_conv_app_nth array_length_list list_update_append) []
  done

term array_shrink

definition "ras_shrink s \<equiv> let 
    (a,n) = s;
    a = if 128*n \<le> array_length a \<and> n>4 then
        array_shrink a n
      else a
  in
    (a,n)"

lemma ras_shrink_id_refine: "(ras_shrink,id) \<in> \<langle>R\<rangle>ras_rel \<rightarrow> \<langle>R\<rangle>ras_rel"
  apply (intro fun_relI)
  apply (simp add: ras_shrink_def ras_rel_def br_def
    ras_raw_\<alpha>_def ras_raw_invar_def Let_def)
  apply clarsimp
  apply safe

  apply (rule)
  apply (auto simp: array_length_list)
  done

lemma ras_shrinkI:
  assumes [param]: "(s,a)\<in>\<langle>R\<rangle>ras_rel"
  shows "(ras_shrink s,a)\<in>\<langle>R\<rangle>ras_rel"
  apply (subst id_apply[of a,symmetric])
  apply (parametricity add: ras_shrink_id_refine)
  done

definition "ras_pop s \<equiv> let (a,n)=s in ras_shrink (a,n - 1)"


lemma ras_pop_refine[autoref_rules]: "(ras_pop,tl) \<in> \<langle>R\<rangle>ras_rel \<rightarrow> \<langle>R\<rangle>ras_rel"
  apply (intro fun_relI)
  apply (clarsimp simp add: ras_pop_def split: prod.split)
  apply (rule ras_shrinkI)

  apply (simp add: ras_pop_def ras_rel_def br_def
    ras_raw_\<alpha>_def ras_raw_invar_def Let_def)
  apply clarsimp

  apply rule
  apply (auto simp: array_length_list) []
  apply (clarsimp simp: array_length_list 
    take_minus_one_conv_butlast rev_butlast_is_tl_rev) []
  apply parametricity
  done
  
definition "ras_get s i \<equiv> let (a,n::nat)=s in array_get a (n-(i+1))"

lemma ras_get_refine: 
  assumes 1: "i'<length l" 
  assumes 2: "(a,l)\<in>\<langle>R\<rangle>ras_rel" 
  assumes 3[param]: "(i,i')\<in>nat_rel"
  shows "(ras_get a i,l!i')\<in>R"
  using 2
  apply (clarsimp 
    simp add: ras_get_def ras_rel_def br_def ras_raw_\<alpha>_def ras_raw_invar_def
    split: prod.split)
  apply (rename_tac aa bb)
  apply (case_tac aa, simp)
proof -
  fix n cl
  assume TKR[param]: "(rev (take n cl), l) \<in> \<langle>R\<rangle>list_rel"
  assume NLE: "n \<le> length cl"

  have "(rev (take n cl)!i, l!i')\<in>R"
    by parametricity (rule 1)
  also have "rev (take n cl)!i = (take n cl)!(n - Suc i)"
    apply (subst rev_nth) 
    using 1 3 list_rel_imp_same_length[OF TKR]
    apply simp
    apply (simp add: min_absorb2[OF NLE])
    done
  also have "take n cl!(n-Suc i) = cl!(n - Suc i)"
    using 1 3 list_rel_imp_same_length[OF TKR]
    by simp
  finally show "(cl!(n-Suc i),l!i')\<in>R" .
qed
  
context begin interpretation autoref_syn .
lemma ras_get_autoref[autoref_rules]: 
  assumes "(l,l')\<in>\<langle>R\<rangle>ras_rel"
  assumes "(i,i')\<in>Id"
  assumes "SIDE_PRECOND (i' < length l')"
  shows "(ras_get l i,(OP nth ::: \<langle>R\<rangle>ras_rel \<rightarrow> nat_rel \<rightarrow> R)$l'$i')\<in>R"
  using assms by (simp add: ras_get_refine)

definition "ras_set s i x \<equiv> let (a,n::nat)=s in (array_set a (n - (i+1)) x,n)"

lemma ras_set_refine: 
  assumes 1: "i'<length l" 
  assumes 2: "(a,l)\<in>\<langle>R\<rangle>ras_rel" 
  assumes 3[param]: "(x,x')\<in>R"
  assumes 4[param]: "(i,i')\<in>nat_rel"
  shows "(ras_set a i x, l[i':=x'])\<in>\<langle>R\<rangle>ras_rel"
  apply (clarsimp 
    simp: ras_set_def ras_rel_def br_def ras_raw_\<alpha>_def ras_raw_invar_def
    split: prod.split)
  apply rule
  using 2 apply (auto simp: ras_rel_def br_def ras_raw_invar_def) []

  apply (subst rev_update)
  using 1 2 3 4 
  apply (clarsimp simp: ras_rel_def br_def ras_raw_invar_def ras_raw_\<alpha>_def) 
  apply (rename_tac ar n)
  apply (case_tac ar, auto dest: list_rel_imp_same_length) []

  apply parametricity
  using 2 
  apply (auto simp: ras_rel_def br_def ras_raw_invar_def ras_raw_\<alpha>_def) []

  using 1 2 4
  apply clarsimp
  apply (auto simp: ras_rel_def br_def ras_raw_invar_def ras_raw_\<alpha>_def) []
  apply (rename_tac ar n)
  apply (case_tac ar, auto dest: list_rel_imp_same_length) []
  done

lemma ras_set_autoref[autoref_rules]: 
  assumes "(l,l')\<in>\<langle>R\<rangle>ras_rel"
  assumes "(i,i')\<in>Id"
  assumes 3[param]: "(x,x')\<in>R"
  assumes "SIDE_PRECOND (i' < length l')"
  shows "(ras_set l i x,
    (OP list_update ::: \<langle>R\<rangle>ras_rel \<rightarrow> nat_rel \<rightarrow> R \<rightarrow> \<langle>R\<rangle>ras_rel)$l'$i'$x'
    )\<in>\<langle>R\<rangle>ras_rel"
  using assms by (simp add: ras_set_refine)

definition ras_length :: "'a rev_array_stack \<Rightarrow> nat" where 
  "ras_length = snd"

lemma ras_length_refine[autoref_rules]: 
  "(ras_length,length) \<in> \<langle>R\<rangle>ras_rel \<rightarrow> nat_rel"
  by (auto 
    simp: ras_length_def ras_rel_def br_def ras_raw_\<alpha>_def ras_raw_invar_def
      array_length_list
    dest!: list_rel_imp_same_length
  )

definition "ras_top s \<equiv> ras_get s 0"

lemma ras_top_code[code]: "ras_top s = (let (a,n)=s in array_get a (n - 1))"
  unfolding ras_top_def ras_get_def ras_length_def 
  by (auto split: prod.split)

lemma ras_top_refine: "\<lbrakk>l\<noteq>[]; (s,l)\<in>\<langle>R\<rangle>ras_rel\<rbrakk> \<Longrightarrow> (ras_top s,hd l)\<in>R"
  unfolding ras_top_def
  apply (simp add: hd_conv_nth)
  apply (rule ras_get_refine)
  apply (auto simp: ras_length_def ras_rel_def br_def ras_raw_\<alpha>_def 
    ras_raw_invar_def array_length_list
    dest!: list_rel_imp_same_length)
  done

lemma ras_top_autoref[autoref_rules]:
  assumes "(l,l')\<in>\<langle>R\<rangle>ras_rel"
  assumes "SIDE_PRECOND (l' \<noteq> [])"
  shows "(ras_top l,(OP hd ::: \<langle>R\<rangle>ras_rel \<rightarrow> R)$l')\<in>R"
  using assms by (simp add: ras_top_refine)


definition "ras_is_empty s \<equiv> ras_length s = 0"
lemma ras_is_empty_code[code]: "ras_is_empty s = (snd s = 0)"
  unfolding ras_is_empty_def ras_length_def by simp

lemma ras_is_empty_refine[autoref_rules]: 
  "(ras_is_empty,is_Nil) \<in> \<langle>R\<rangle>ras_rel \<rightarrow> bool_rel"
proof
  fix s l
  assume [param]: "(s,l)\<in>\<langle>R\<rangle>ras_rel"
  have "(ras_is_empty s,length l = 0) \<in> bool_rel"
    unfolding ras_is_empty_def
    by (parametricity add: ras_length_refine)
  also have "length l = 0 \<longleftrightarrow> is_Nil l"
    by (cases l) auto
  finally show "(ras_is_empty s, is_Nil l) \<in> bool_rel" .
qed

definition "ras_singleton x \<equiv> (array_of_list [x],1)"
lemma ras_singleton_refine[autoref_rules]: 
  "(ras_singleton,op_list_singleton)\<in>R \<rightarrow> \<langle>R\<rangle>ras_rel"
  apply (intro fun_relI)
  apply (simp add: ras_singleton_def ras_rel_def br_def ras_raw_\<alpha>_def 
    ras_raw_invar_def)
  apply rule
  apply (auto simp: array_length_list) []
  apply simp
  done

definition "ras_cast_to_list s \<equiv> let (a,n) = s in rev (take n (list_of_array a))"
lemma ras_cast_to_list_refine[autoref_rules]: 
  "(ras_cast_to_list, CAST) \<in> \<langle>R\<rangle>ras_rel \<rightarrow> \<langle>R\<rangle>list_rel"
  apply (intro fun_relI)
  apply (simp add: ras_cast_to_list_def ras_rel_def br_def ras_raw_\<alpha>_def 
    ras_raw_invar_def)
  apply rule
  apply (auto simp: array_length_list) [2]
  done
  
end

end

