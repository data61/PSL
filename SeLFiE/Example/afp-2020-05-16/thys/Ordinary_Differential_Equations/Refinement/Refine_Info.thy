theory
  Refine_Info
  imports
    Refine_Unions
    Refine_Vector_List
begin

consts i_info::"interface\<Rightarrow>interface\<Rightarrow>interface"

definition info_rel_internal: "info_rel I S = (I \<times>\<^sub>r S) O br snd top"
lemma info_rel_def: "\<langle>I, S\<rangle>info_rel = (I \<times>\<^sub>r S) O br snd top"
  by (auto simp: relAPP_def info_rel_internal)
lemmas [autoref_rel_intf] = REL_INTFI[of "info_rel" i_info]

lemma info_rel_br: "\<langle>br a I, (br b J)\<rangle>info_rel = br (\<lambda>y. b (snd y)) (\<lambda>x. I (fst x) \<and> J (snd x))"
  by (auto simp: info_rel_def br_def prod_rel_def)

lemma sv_info_rel[relator_props]:
  "single_valued S \<Longrightarrow>single_valued I \<Longrightarrow> single_valued (\<langle>I, S\<rangle>info_rel)"
  by (auto simp: info_rel_def intro!: relator_props)

definition [simp]: "op_info_is_empty = is_empty"
context includes autoref_syntax begin
lemma [autoref_op_pat]:  "is_empty \<equiv> OP op_info_is_empty"
  by simp
end

lemma op_set_isEmpty_info_rel_set[autoref_rules]:
  "GEN_OP empty_i (is_empty) (A \<rightarrow> bool_rel) \<Longrightarrow> (\<lambda>x. empty_i (snd x), op_info_is_empty) \<in> \<langle>I, A\<rangle>info_rel \<rightarrow> bool_rel"
  by (auto simp: info_rel_def br_def op_set_isEmpty_def[abs_def] dest: fun_relD)

definition [refine_vcg_def]: "get_info X = SPEC (\<lambda>(h, Y). Y = X)"
lemma get_info_autoref[autoref_rules]:
  shows "(\<lambda>x. RETURN x, get_info) \<in> \<langle>I, A\<rangle>info_rel \<rightarrow> \<langle>I \<times>\<^sub>r A\<rangle>nres_rel"
  by (force simp: get_info_def info_rel_def nres_rel_def br_def intro!: RETURN_SPEC_refine)

definition with_info::"'b \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where [simp, refine_vcg_def]: "with_info h x = x"

lemma with_stepsize_autoref[autoref_rules]:
  "((\<lambda>h x. (h, x)), with_info) \<in> R \<rightarrow> A \<rightarrow> \<langle>R, A\<rangle>info_rel"
  by (auto simp: info_rel_def br_def intro!: prod_relI)

definition with_half_stepsizes::"'a set \<Rightarrow> 'a set"
  where [simp, refine_vcg_def]: "with_half_stepsizes x = x"
lemma with_half_stepsize_autoref[autoref_rules]:
  "((map (\<lambda>(h, x). (h/2, x))), with_half_stepsizes) \<in>
  clw_rel (\<langle>rnv_rel, A\<rangle>info_rel) \<rightarrow> clw_rel (\<langle>rnv_rel, A\<rangle>info_rel)"
  if  [unfolded autoref_tag_defs, relator_props]: "single_valued A"
  unfolding with_half_stepsizes_def
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)+
  by (auto simp: info_rel_def br_def prod_rel_def)

definition with_infos::"'b \<Rightarrow> 'a set \<Rightarrow> 'a set"
  where [simp, refine_vcg_def]: "with_infos h x = x"
lemma with_infos_autoref[autoref_rules]:
  "(\<lambda>h. map (Pair h), with_infos) \<in> R \<rightarrow> clw_rel A \<rightarrow> clw_rel (\<langle>R, A\<rangle>info_rel)"
  if [unfolded autoref_tag_defs, relator_props]: "PREFER single_valued A" "PREFER single_valued R"
  unfolding with_infos_def
  apply (rule fun_relI)
  apply (rule lift_clw_rel_map)
     apply (rule relator_props)+
  by (auto simp: info_rel_def br_def prod_rel_def)

abbreviation "with_stepsize \<equiv> (with_info::real\<Rightarrow>_)"

definition split_with_info::"'a set \<Rightarrow> ('c \<times> 'a set \<times> 'a set) nres"
  where [refine_vcg_def]: "split_with_info X = SPEC (\<lambda>(S, Y, YS). X = Y \<union> YS)"

context includes autoref_syntax begin
lemma split_with_info_appr_plane_autoref[autoref_rules]:
  assumes "PREFER single_valued A"
  assumes "PREFER single_valued S"
  assumes "(xs, X) \<in> clw_rel (\<langle>A,S\<rangle>info_rel)"
  shows
    "(if xs = [] then SUCCEED else let s = fst (hd xs); (a, b) = List.partition (\<lambda>(sctn, _). sctn = s) xs in RETURN (s, map snd a, b),
    split_with_info $ X) \<in>
    \<langle>A \<times>\<^sub>r clw_rel S \<times>\<^sub>r clw_rel (\<langle>A, S\<rangle>info_rel)\<rangle>nres_rel"
  using assms
  by (fastforce simp: Let_def split_with_info_def split_beta'
      lw_rel_def Union_rel_br info_rel_br ex_br_conj_iff Id_br[where 'a="'a sctn"]
      split: if_splits
      elim!: single_valued_as_brE
      intro!: nres_relI RETURN_SPEC_refine brI hd_in_set
      dest!: brD )

definition
  "explicit_info_set X0 =
    do {
      e \<leftarrow> isEmpty_spec X0;
      (_, _, Xis) \<leftarrow> WHILE\<^bsup>\<lambda>(e, X, Y).
          (e \<longrightarrow> X = {}) \<and>
          X0 = X \<union> (\<Union>(sctn, IS)\<in>Y. IS)\<^esup>
        (\<lambda>(e, X, Y). \<not>e)
        (\<lambda>(e, X, Y).
          do {
            (sctn, S, X') \<leftarrow> split_with_info X;
            e \<leftarrow> isEmpty_spec X';
            RETURN (e, X', insert (sctn, S) Y)
          }
        )
        (e, X0, {});
      RETURN Xis
    }"

schematic_goal explicit_info_setc:
  fixes po :: "'d \<Rightarrow> 'a::executable_euclidean_space set"
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued A"
  assumes [THEN PREFER_sv_D, relator_props]: "PREFER single_valued S"
  assumes [autoref_rules]: "(XSi, XS) \<in> clw_rel (\<langle>S, A\<rangle>info_rel)"
  shows "(nres_of ?f, explicit_info_set $ XS) \<in> \<langle>\<langle>S \<times>\<^sub>r clw_rel A\<rangle>list_wset_rel\<rangle>nres_rel"
  unfolding autoref_tag_defs
  unfolding explicit_info_set_def
  including art
  by autoref_monadic
concrete_definition explicit_info_setc for XSi uses explicit_info_setc
lemmas [autoref_rules] = explicit_info_setc.refine

lemma explicit_info_set[THEN order_trans, refine_vcg]:
  "explicit_info_set X \<le> SPEC (\<lambda>R. X = (\<Union>(sctn, IS) \<in> R. IS))"
  unfolding explicit_info_set_def
  by (refine_vcg) (auto simp: split_beta' subset_iff)

lemmas [relator_props del] = sv_info_rel
lemma sv_info_rel'[relator_props]:
  "single_valued S \<Longrightarrow> single_valued (\<langle>I, S\<rangle>info_rel)"
  by (auto simp: info_rel_def single_valued_def br_def)

lemma
  is_empty_info_rel_autoref[autoref_rules]:
  "GEN_OP ie is_empty (A \<rightarrow> bool_rel) \<Longrightarrow> (\<lambda>x. ie(snd x), is_empty) \<in> \<langle>R, A\<rangle>info_rel \<rightarrow> bool_rel"
  by (force simp: info_rel_def br_def dest: fun_relD)

definition with_coll_infos::"'c set \<Rightarrow> 'a set \<Rightarrow> 'a set nres"
  where [simp, refine_vcg_def]: "with_coll_infos h x = SPEC (\<lambda>r. r = x)"

lemma with_coll_infos_autoref[autoref_rules]:
  "((\<lambda>ri ai. nres_of (if ri = [] then dSUCCEED else dRETURN (List.product ri ai))), with_coll_infos) \<in>
    clw_rel R \<rightarrow> clw_rel A \<rightarrow> \<langle>clw_rel (\<langle>R, A\<rangle>info_rel)\<rangle>nres_rel"
  if "PREFER single_valued R" "PREFER single_valued A"
  using that
  by (force simp: relcomp_unfold nres_rel_def info_rel_br list_wset_rel_def Union_rel_br
      Id_arbitrary_interface_def RETURN_RES_refine_iff set_rel_br
      elim!: single_valued_as_brE
      intro!: brI dest!: brD
      split: if_splits)

end

end