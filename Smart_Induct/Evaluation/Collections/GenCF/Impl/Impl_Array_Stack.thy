section \<open>Stack by Array\<close>
theory Impl_Array_Stack
imports   
  Automatic_Refinement.Automatic_Refinement
  "../../Lib/Diff_Array"
begin

type_synonym 'a array_stack = "'a array \<times> nat"

term Diff_Array.array_length

definition "as_raw_\<alpha> s \<equiv> take (snd s) (list_of_array (fst s))"
definition "as_raw_invar s \<equiv> snd s \<le> array_length (fst s)"

definition as_rel_def_internal: "as_rel R \<equiv> br as_raw_\<alpha> as_raw_invar O \<langle>R\<rangle>list_rel"
lemma as_rel_def: "\<langle>R\<rangle>as_rel \<equiv> br as_raw_\<alpha> as_raw_invar O \<langle>R\<rangle>list_rel"
  unfolding as_rel_def_internal[abs_def] by (simp add: relAPP_def)

lemma [relator_props]: "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>as_rel)"
  unfolding as_rel_def
  by tagged_solver

lemmas [autoref_rel_intf] = REL_INTFI[of as_rel i_list]


definition "as_empty (_::unit) \<equiv> (array_of_list [],0)"

lemma as_empty_refine[autoref_rules]: "(as_empty (),[]) \<in> \<langle>R\<rangle>as_rel"
  unfolding as_rel_def as_empty_def br_def
  unfolding as_raw_\<alpha>_def as_raw_invar_def
  by auto


definition "as_push s x \<equiv> let
    (a,n)=s;
    a = if n = array_length a then
        array_grow a (max 4 (2*n)) x
      else a;
    a = array_set a n x
  in
    (a,n+1)"

lemma as_push_refine[autoref_rules]: 
  "(as_push,op_list_append_elem) \<in> \<langle>R\<rangle>as_rel \<rightarrow> R \<rightarrow> \<langle>R\<rangle>as_rel"
  apply (intro fun_relI)
  apply (simp add: as_push_def op_list_append_elem_def as_rel_def br_def
    as_raw_\<alpha>_def as_raw_invar_def)
  apply clarsimp
  apply safe
  apply (rule)
  apply auto []
  apply (clarsimp simp: array_length_list) []
  apply parametricity

  apply rule
  apply auto []
  apply (auto simp: take_Suc_conv_app_nth array_length_list list_update_append) []
  apply parametricity
  done

term array_shrink

definition "as_shrink s \<equiv> let 
    (a,n) = s;
    a = if 128*n \<le> array_length a \<and> n>4 then
        array_shrink a n
      else a
  in
    (a,n)"

lemma as_shrink_id_refine: "(as_shrink,id) \<in> \<langle>R\<rangle>as_rel \<rightarrow> \<langle>R\<rangle>as_rel"
  apply (intro fun_relI)
  apply (simp add: as_shrink_def as_rel_def br_def
    as_raw_\<alpha>_def as_raw_invar_def Let_def)
  apply clarsimp
  apply safe

  apply (rule)
  apply (auto simp: array_length_list)
  done

lemma as_shrinkI:
  assumes [param]: "(s,a)\<in>\<langle>R\<rangle>as_rel"
  shows "(as_shrink s,a)\<in>\<langle>R\<rangle>as_rel"
  apply (subst id_apply[of a,symmetric])
  apply (parametricity add: as_shrink_id_refine)
  done

definition "as_pop s \<equiv> let (a,n)=s in as_shrink (a,n - 1)"

lemma as_pop_refine[autoref_rules]: "(as_pop,butlast) \<in> \<langle>R\<rangle>as_rel \<rightarrow> \<langle>R\<rangle>as_rel"
  apply (intro fun_relI)
  apply (clarsimp simp add: as_pop_def split: prod.split)
  apply (rule as_shrinkI)

  apply (simp add: as_pop_def as_rel_def br_def
    as_raw_\<alpha>_def as_raw_invar_def Let_def)
  apply clarsimp

  apply rule
  apply (auto simp: array_length_list) []
  apply (clarsimp simp: array_length_list take_minus_one_conv_butlast) []
  apply parametricity
  done
  
definition "as_get s i \<equiv> let (a,_::nat)=s in array_get a i"

lemma as_get_refine: 
  assumes 1: "i'<length l" 
  assumes 2: "(a,l)\<in>\<langle>R\<rangle>as_rel" 
  assumes 3[param]: "(i,i')\<in>nat_rel"
  shows "(as_get a i,l!i')\<in>R"
  using 2
  apply (clarsimp 
    simp add: as_get_def as_rel_def br_def as_raw_\<alpha>_def as_raw_invar_def
    split: prod.split)
  apply (rename_tac aa bb)
  apply (case_tac aa, simp)
proof -
  fix n cl
  assume TKR[param]: "(take n cl, l) \<in> \<langle>R\<rangle>list_rel"

  have "(take n cl!i, l!i')\<in>R"
    by parametricity (rule 1)
  also have "take n cl!i = cl!i"
    using 1 3 list_rel_imp_same_length[OF TKR]
    by simp
  finally show "(cl!i,l!i')\<in>R" .
qed
  
context begin interpretation autoref_syn .
lemma as_get_autoref[autoref_rules]: 
  assumes "(l,l')\<in>\<langle>R\<rangle>as_rel"
  assumes "(i,i')\<in>Id"
  assumes "SIDE_PRECOND (i' < length l')"
  shows "(as_get l i,(OP nth ::: \<langle>R\<rangle>as_rel \<rightarrow> nat_rel \<rightarrow> R)$l'$i')\<in>R"
  using assms by (simp add: as_get_refine)

definition "as_set s i x \<equiv> let (a,n::nat)=s in (array_set a i x,n)"

lemma as_set_refine[autoref_rules]: 
  "(as_set,list_update)\<in>\<langle>R\<rangle>as_rel \<rightarrow> nat_rel \<rightarrow> R \<rightarrow> \<langle>R\<rangle>as_rel"
  apply (intro fun_relI)
  apply (clarsimp 
    simp: as_set_def as_rel_def br_def as_raw_\<alpha>_def as_raw_invar_def
    split: prod.split)
  apply rule
  apply auto []
  apply parametricity
  by simp

definition as_length :: "'a array_stack \<Rightarrow> nat" where 
  "as_length = snd"

lemma as_length_refine[autoref_rules]: 
  "(as_length,length) \<in> \<langle>R\<rangle>as_rel \<rightarrow> nat_rel"
  by (auto 
    simp: as_length_def as_rel_def br_def as_raw_\<alpha>_def as_raw_invar_def
      array_length_list
    dest!: list_rel_imp_same_length
  )

definition "as_top s \<equiv> as_get s (as_length s - 1)"

lemma as_top_code[code]: "as_top s = (let (a,n)=s in array_get a (n - 1))"
  unfolding as_top_def as_get_def as_length_def 
  by (auto split: prod.split)

lemma as_top_refine: "\<lbrakk>l\<noteq>[]; (s,l)\<in>\<langle>R\<rangle>as_rel\<rbrakk> \<Longrightarrow> (as_top s,last l)\<in>R"
  unfolding as_top_def
  apply (simp add: last_conv_nth)
  apply (rule as_get_refine)
  apply (auto simp: as_length_def as_rel_def br_def as_raw_\<alpha>_def 
    as_raw_invar_def array_length_list
    dest!: list_rel_imp_same_length)
  done

lemma as_top_autoref[autoref_rules]:
  assumes "(l,l')\<in>\<langle>R\<rangle>as_rel"
  assumes "SIDE_PRECOND (l' \<noteq> [])"
  shows "(as_top l,(OP last ::: \<langle>R\<rangle>as_rel \<rightarrow> R)$l')\<in>R"
  using assms by (simp add: as_top_refine)


definition "as_is_empty s \<equiv> as_length s = 0"
lemma as_is_empty_code[code]: "as_is_empty s = (snd s = 0)"
  unfolding as_is_empty_def as_length_def by simp

lemma as_is_empty_refine[autoref_rules]: 
  "(as_is_empty,is_Nil) \<in> \<langle>R\<rangle>as_rel \<rightarrow> bool_rel"
proof
  fix s l
  assume [param]: "(s,l)\<in>\<langle>R\<rangle>as_rel"
  have "(as_is_empty s,length l = 0) \<in> bool_rel"
    unfolding as_is_empty_def
    by (parametricity add: as_length_refine)
  also have "length l = 0 \<longleftrightarrow> is_Nil l"
    by (cases l) auto
  finally show "(as_is_empty s, is_Nil l) \<in> bool_rel" .
qed

definition "as_take m s \<equiv> let (a,n) = s in 
  if m<n then 
    as_shrink (a,m)
  else (a,n)"

lemma as_take_refine[autoref_rules]: 
  "(as_take,take)\<in>nat_rel \<rightarrow> \<langle>R\<rangle>as_rel \<rightarrow> \<langle>R\<rangle>as_rel"
  apply (intro fun_relI)
  apply (clarsimp simp add: as_take_def, safe)

  apply (rule as_shrinkI)
  apply (simp add: as_rel_def br_def as_raw_\<alpha>_def as_raw_invar_def)
  apply rule
  apply auto []
  apply clarsimp
  apply (subgoal_tac "take a' (list_of_array a) = take a' (take ba (list_of_array a))")
  apply (simp only: )
  apply (parametricity, rule IdI)
  apply simp

  apply (simp add: as_rel_def br_def as_raw_\<alpha>_def as_raw_invar_def)
  apply rule
  apply auto []
  apply clarsimp
  apply (frule list_rel_imp_same_length)
  apply simp
  done

definition "as_singleton x \<equiv> (array_of_list [x],1)"
lemma as_singleton_refine[autoref_rules]: 
  "(as_singleton,op_list_singleton)\<in>R \<rightarrow> \<langle>R\<rangle>as_rel"
  apply (intro fun_relI)
  apply (simp add: as_singleton_def as_rel_def br_def as_raw_\<alpha>_def 
    as_raw_invar_def)
  apply rule
  apply (auto simp: array_length_list) []
  apply simp
  done

end

end
