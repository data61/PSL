(*  Title:       Lightweight Java, the proof
    Authors:     Rok Strnisa <rok@strnisa.com>, 2006
                 Matthew Parkinson <matt@matthewp.com>, 2006
    Maintainer:  
*)

theory Lightweight_Java_Proof
imports Lightweight_Java_Equivalence "HOL-Library.Infinite_Set"
begin

lemmas wf_intros = wf_object_wf_varstate_wf_heap_wf_config_wf_stmt_wf_meth_wf_class_common_wf_class_wf_program.intros [simplified]
lemmas wf_induct = wf_object_wf_varstate_wf_heap_wf_config_wf_stmt_wf_meth_wf_class_common_wf_class_wf_program.induct [simplified]
lemmas wf_config_normalI = wf_object_wf_varstate_wf_heap_wf_config_wf_stmt_wf_meth_wf_class_common_wf_class_wf_program.wf_allI [simplified]
lemmas wf_objectE   = wf_object.cases[simplified]
lemmas wf_varstateE = wf_varstate.cases[simplified]
lemmas wf_heapE     = wf_heap.cases[simplified]
lemmas wf_configE   = wf_config.cases[simplified]
lemmas wf_stmtE     = wf_stmt.cases[simplified]
lemmas wf_methE     = wf_meth.cases[simplified]
lemmas wf_class_cE  = wf_class_common.cases[simplified]
lemmas wf_classE    = wf_class.cases[simplified]
lemmas wf_programE  = wf_program.cases[simplified]

lemma wf_subvarstateI:
  "\<lbrakk>wf_varstate P \<Gamma> H L; \<Gamma> x' = Some ty;
    wf_object P H (Some v) (Some ty)\<rbrakk>
        \<Longrightarrow> wf_varstate P \<Gamma> H (L (x' \<mapsto> v))"
apply(erule wf_varstateE) apply(rule wf_varstateI) apply(simp) apply(clarsimp)
done

lemma finite_super_varstate:
  "finite (dom ((L ++ map_of (map (\<lambda>(y, cl, var, var', y). (x_var var', y)) y_cl_var_var'_v_list))(x' \<mapsto> v_oid oid))) = finite (dom L)"
apply(induct y_cl_var_var'_v_list)
 apply(clarsimp) apply(simp add: dom_def)
 apply(subgoal_tac "{a. a \<noteq> x' \<longrightarrow> (\<exists>y. L a = Some y)} = {a. a = x' \<or> (\<exists>y. L a = Some y)}")
 apply(simp add: Collect_disj_eq) apply(force)
apply(clarsimp simp add: map_add_def dom_def split: if_split_asm)
apply(subgoal_tac "{aa. aa \<noteq> x_var a \<longrightarrow> aa \<noteq> x' \<longrightarrow> (\<exists>y. case_option (L aa) Some (map_of (map (\<lambda>(y, cl, var, var', y). (x_var var', y)) y_cl_var_var'_v_list) aa) = Some y)} =
                   {aa. aa = x_var a \<or> (aa = x' \<or> (\<exists>y. case_option (L aa) Some (map_of (map (\<lambda>(y, cl, var, var', y). (x_var var', y)) y_cl_var_var'_v_list) aa) = Some y))}")
apply(simp add: Collect_disj_eq) apply(force)
done

lemma fst_map_elem:
  "(y_k, ty_k, var_k, var'_k, v_k) \<in> set y_ty_var_var'_v_list \<Longrightarrow>
      x_var var'_k \<in> fst ` (\<lambda>(y, ty, var, var', v). (x_var var', ty)) ` set y_ty_var_var'_v_list"
by (force)

lemma map_add_x_var[THEN mp]:
  "var' \<in> set (map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list) \<longrightarrow>
   x_var var' \<in> set (map (\<lambda>(y, cl, var, var', v). x_var var) y_cl_var_var'_v_list)"
by (induct y_cl_var_var'_v_list, auto)

lemma map_of_map_and_x[simp]:
  "\<lbrakk>\<Gamma> x = Some ty_x; L x' = None; \<forall>x\<in>set y_cl_var_var'_v_list. (\<lambda>(y, cl, var, var', v). L (x_var var') = None) x;
    \<forall>x\<in>Map.dom \<Gamma>. wf_object Pa H (L x) (\<Gamma> x)\<rbrakk> \<Longrightarrow>
      (if x = x' then Some ty
       else (\<Gamma> ++ map_of (map (\<lambda>((y, cl, var, var', v), y', ty). (x_var var', ty)) (zip y_cl_var_var'_v_list y_ty_list))) x) =
          Some ty_x"
apply(subgoal_tac "x \<noteq> x'") apply(subgoal_tac "\<forall>(y, cl, var, var', v) \<in> set y_cl_var_var'_v_list. x_var var' \<noteq> x")
  apply(case_tac "map_of (map (\<lambda>((y, cl, var, var', v), y', ty). (x_var var', ty)) (zip y_cl_var_var'_v_list y_ty_list)) x")
   apply(clarsimp simp add: map_add_def)
  apply(clarsimp) apply(drule map_of_SomeD) apply(clarsimp) apply(rename_tac y cl var var' v y' ty)
  apply(drule_tac x = "(y, cl, var, var', v)" in bspec) apply(force simp add: set_zip)
  apply(drule_tac x = "x_var var'" in bspec, simp add: domI) apply(erule wf_objectE, simp+)
 apply(force elim: wf_objectE)+
done

lemma wf_stmt_in_G':
   "(L x' = None \<and> (\<forall>x\<in>set y_cl_var_var'_v_list. (\<lambda>(y, cl, var, var', v). L (x_var var') = None) x)
    \<and> (\<forall>x\<in>dom \<Gamma>. wf_object P H (L x) (\<Gamma> x)) \<and> wf_stmt P \<Gamma> s \<longrightarrow>
       wf_stmt P ((\<Gamma> ++ map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)))(x' \<mapsto> ty)) s) \<and>
    (L x' = None \<and> (\<forall>x\<in>set y_cl_var_var'_v_list. (\<lambda>(y, cl, var, var', v). L (x_var var') = None) x)
    \<and> (\<forall>x\<in>dom \<Gamma>. wf_object P H (L x) (\<Gamma> x)) \<and> (\<forall>s\<in>set ss. wf_stmt P \<Gamma> s) \<longrightarrow>
       (\<forall>s\<in>set ss. wf_stmt P ((\<Gamma> ++ map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)))(x' \<mapsto> ty)) s))"
apply(rule tr_s_f_tr_ss_f.induct)

apply(clarsimp, erule wf_stmtE, simp_all, simp add: wf_blockI)

apply(clarify, erule wf_stmtE, simp_all)
apply(erule sty_option.cases, force intro: wf_var_assignI sty_optionI)

apply(clarify, erule wf_stmtE, simp_all)
apply(erule sty_option.cases, force intro: wf_field_readI sty_optionI)

apply(clarify, erule wf_stmtE, simp_all)
apply(erule sty_option.cases, force intro: wf_field_writeI sty_optionI)

apply(clarify, erule wf_stmtE, simp_all)
apply(clarsimp)
apply(rule wf_ifI)
  apply(erule disjE)
   apply(rule disjI1, erule sty_option.cases, force intro: sty_optionI)
  apply(rule disjI2, erule sty_option.cases, force intro: sty_optionI)
 apply(assumption+)

apply(clarify, erule wf_stmtE, simp_all)
apply(erule sty_option.cases, force intro: wf_newI sty_optionI)

apply(clarify, erule wf_stmtE, simp_all)
apply(rule wf_mcallI, simp, simp, simp)
 apply(clarsimp split del: if_split) apply(rename_tac y_k ty_k)
 apply(drule_tac x = "(y_k, ty_k)" in bspec, simp, clarify)
 apply(erule_tac ?a3.0 = "Some ty_k" in sty_option.cases)
 apply(force intro: sty_optionI)
apply(clarify)
apply(erule sty_option.cases)
apply(rule sty_optionI, simp+)

done

lemma map_three_in_four:
  "var_k \<in> set (map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list)
   \<longrightarrow> (\<exists>y cl u. (y, cl, var_k, u) \<in> set y_cl_var_var'_v_list)"
by (induct y_cl_var_var'_v_list, auto)

lemma map_var:
  "\<lbrakk>(cl_k, var_k, ty_k) \<in> set cl_var_ty_list;
    map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list\<rbrakk>
      \<Longrightarrow> \<exists>y_k cl'_k u_k. (y_k, cl'_k, var_k, u_k) \<in> set y_cl_var_var'_v_list"
apply(subgoal_tac "var_k \<in> set (map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list)")
by (force simp add: map_three_in_four)+

lemma length_one_in_two:
  "length y_ty_list = length (map fst y_ty_list)"
by (induct y_ty_list, auto)

lemma length_two_in_two:
  "length y_ty_list = length (map snd y_ty_list)"
by (induct y_ty_list, auto)

lemma length_two_in_three:
  "length cl_var_ty_list = length (map (\<lambda>(cl, var, ty). var) cl_var_ty_list)"
by (induct cl_var_ty_list, auto)

lemma length_three_in_three:
  "length cl_var_ty_list = length (map (\<lambda>(cl, var, ty). ty) cl_var_ty_list)"
by (induct cl_var_ty_list, auto)

lemma length_three_in_four:
  "length y_cl_var_var'_v_list = length (map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list)"
by (induct y_cl_var_var'_v_list, auto)

lemma length_one_in_five:
  "length y_cl_var_var'_v_list = length (map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list)"
by (induct y_cl_var_var'_v_list, auto)

lemma length_three_in_five:
  "length y_cl_var_var'_v_list = length (map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list)"
by (induct y_cl_var_var'_v_list, auto)

lemma map_length_list:
  "length (map (\<lambda>((y, y'), yy, ty). (y', ty)) list) = length list"
by (induct list, auto)

lemma map_length_y:
  "map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list = map fst y_ty_list \<Longrightarrow>
   length y_cl_var_var'_v_list = length y_ty_list"
by (simp only: length_one_in_five length_one_in_two)

lemma map_length_y':
  "map fst y_y'_list = map fst y_ty_list \<Longrightarrow> length y_y'_list = length y_ty_list"
by (simp only: length_one_in_two length_two_in_two)

lemma map_length_var:
  "map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list \<Longrightarrow>
   length y_cl_var_var'_v_list = length cl_var_ty_list"
by (simp only: length_three_in_five length_two_in_three)

lemma map_length_ty:
  "map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list \<Longrightarrow>
   length cl_var_ty_list = length y_ty_list"
by (simp only: length_three_in_three length_two_in_two)

lemma map_length_var_ty:
  "\<lbrakk>map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list;
    map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list\<rbrakk> \<Longrightarrow>
   length y_cl_var_var'_v_list = length y_ty_list"
apply(rule_tac s = "length cl_var_ty_list" in trans)
apply (simp only: length_three_in_four length_two_in_three)
apply(simp only: length_three_in_three length_two_in_two)
done

lemma fun_eq_fst:
  "(fst \<circ> (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y))) = (\<lambda>((y, cl, var, var', v), y', y). (x_var var'))"
by (simp add: fun_eq_iff)

lemma fst_zip_eq:
  "length y_cl_var_var'_v_list = length y_ty_list \<Longrightarrow>
   (map fst (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list))) =
   (map (\<lambda>(y, cl, var, var', v). x_var var') y_cl_var_var'_v_list)"
apply(simp)
apply(simp add: fun_eq_fst)
apply(rule nth_equalityI)
 apply(force)
apply(clarsimp)
apply(frule nth_mem)
apply(subgoal_tac "\<exists>x. (y_cl_var_var'_v_list ! i) = x")
apply(force)
apply(rule_tac x = "y_cl_var_var'_v_list ! i" in exI)
apply(simp)
done

lemma distinct_x_var:
  "distinct (map (\<lambda>(y, cl, var, var', v). x_var var) y_cl_var_var'_v_list) =
   distinct (map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list)"
apply (induct y_cl_var_var'_v_list)
by (force simp add: contrapos_np)+

lemma distinct_x_var':
  "distinct (map (\<lambda>(y, cl, var, var', v). x_var var') y_cl_var_var'_v_list) =
   distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list)"
apply(induct y_cl_var_var'_v_list)
by (force simp add: contrapos_np)+

lemma map_fst_two:
  "map fst (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) =
   map (\<lambda>(y, cl, var, var', v). x_var var) y_cl_var_var'_v_list"
by (induct y_cl_var_var'_v_list, auto)

lemma map_fst_two':
  "map fst (map (\<lambda>(y, cl, var, var', y). (x_var var', y)) y_cl_var_var'_v_list) =
   map (\<lambda>(y, cl, var, var', y). x_var var') y_cl_var_var'_v_list"
by (induct y_cl_var_var'_v_list, auto)

lemma map_fst_var':
  "distinct (map fst (map (\<lambda>(y, cl, var, var', y). (x_var var', y)) y_cl_var_var'_v_list)) =
   distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list)"
by (simp only: map_fst_two' distinct_x_var')

lemma distinct_var:
  "\<lbrakk>distinct (map (\<lambda>(cl, var, ty). var) cl_var_ty_list);
    map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list\<rbrakk> \<Longrightarrow>
      distinct (map fst (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list))"
by (simp only: map_fst_two distinct_x_var)

lemma distinct_var':
  "\<lbrakk>map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list;
    map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list\<rbrakk> \<Longrightarrow>
    distinct (map fst (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list))) =
    distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list)"
by (simp only: map_length_var_ty fst_zip_eq distinct_x_var')

lemma weaken_list_var:
  "map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list =
   map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list"
by (induct y_cl_var_var'_v_list, auto)

lemma weaken_list_fd:
  "map (\<lambda>(y, cl, var, var', v). vd_def cl var) list = map (\<lambda>(y, cl, var, u). vd_def cl var) list"
by (induct list, auto)

lemma weaken_list_y:
 "map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list =
  map fst y_cl_var_var'_v_list"
by (induct y_cl_var_var'_v_list, auto)

lemma wf_cld_from_lu:
  "\<lbrakk>wf_program P; find_cld P ctx fqn (Some (ctx', cld'))\<rbrakk> \<Longrightarrow> wf_class P cld'"
apply(clarsimp) apply(drule find_to_mem) apply(erule wf_programE) by (simp add: member_def)

lemma meth_def_in_set[rule_format]:
  "find_meth_def_in_list meth_defs meth (Some meth_def) \<longrightarrow> meth_def \<in> set meth_defs"
apply(clarsimp) apply(induct meth_defs) by (auto split: meth_def.splits meth_sig.splits if_split_asm)

lemma find_meth_def_in_list_mem[rule_format, simp]:
  "find_meth_def_in_list_f meth_defs meth = Some meth_def \<longrightarrow> meth_def \<in> set meth_defs"
apply(induct meth_defs) apply(auto split: meth_def.splits meth_sig.splits) done

lemma find_meth_def_in_path_ex_cld[rule_format]:
   "find_meth_def_in_path_f ctxclds meth = Some (ctx, meth_def)
      \<longrightarrow> (\<exists>cld meth_defs. (ctx, cld) \<in> set ctxclds \<and> class_methods_f cld = meth_defs \<and> meth_def \<in> set meth_defs)"
apply(induct ctxclds) apply(simp) apply(clarsimp)
apply(clarsimp split: option.splits) apply(rule_tac x = cld in exI) apply(force)
apply(force)
done

lemma map_ctx_cld_dcl_two[simp]:
  "ctxclds = map (\<lambda>(ctx, cld, dcl). (ctx, cld)) (map (\<lambda>(ctx, cld). (ctx, cld, classname_f cld)) ctxclds)"
by (induct ctxclds, auto)

lemma clds_in_path_exist:
  "find_path_f P ctx' fqn = Some path \<Longrightarrow> (\<forall>(ctx, cld) \<in> set path. cld \<in> set P)"
apply(clarify)
apply(drule all_in_path_found) apply(simp) apply(clarsimp)
apply(drule find_to_mem) apply(simp add: member_def)
done

lemma wf_meth_defs_in_wf_class[rule_format]:
  "meth_def \<in> set (class_methods_f cld) \<and> wf_class P cld 
     \<longrightarrow> wf_meth P (ty_def ctx_def (class_name_f cld)) meth_def"
apply(clarsimp)
apply(erule wf_classE) apply(clarsimp simp: class_methods_f_def)
apply(erule wf_class_cE) apply(clarsimp simp: class_name_f_def)
apply(drule(1)bspec, simp)
done

lemma map_ctxclds: "ctxclds = map ((\<lambda>(ctx_XXX, cld_XXX, dcl_XXX). (ctx_XXX, cld_XXX)) \<circ> (\<lambda>(ctx, cld). (ctx, cld, class_name_f cld))) ctxclds"
by (induct ctxclds, auto)

lemma wf_method_from_find'[rule_format]:
  "wf_program P \<and> find_path_ty_f P (ty_def ctxa dcl) = Some ctxclds \<and> find_meth_def_in_path_f ctxclds meth = Some (ctx, meth_def)
       \<longrightarrow> (\<exists>dcla. is_sty_one P (ty_def ctxa dcl) (ty_def ctx dcla) = Some True \<and> wf_meth P (ty_def ctx_def dcla) meth_def)"
apply(clarsimp) apply(drule find_meth_def_in_path_ex_cld) apply(clarsimp)
apply(rule_tac x = "class_name_f cld" in exI)
apply(rule)
 apply(rule_tac ctx_cld_dcl_list = "map (\<lambda>(ctx, cld). (ctx, cld, class_name_f cld)) ctxclds" in sty_dclI[simplified])
   apply(simp add: map_ctxclds)
  apply(clarsimp)
 apply(force)
apply(drule clds_in_path_exist)
 apply(simp)
apply(erule wf_programE) apply(clarsimp)
apply(drule_tac x = "(ctx, cld)" in bspec, simp)
apply(drule_tac x = cld in bspec, simp)
apply(simp add: wf_meth_defs_in_wf_class)
done



(* fix the ctx problem here\<dots> *)
lemma wf_method_from_find:
  "\<lbrakk>wf_program P; find_meth_def P ty_x_d meth (Some (ctx, meth_def))\<rbrakk> \<Longrightarrow>
      \<exists>dcl. sty_one P ty_x_d (ty_def ctx dcl) \<and> wf_meth P (ty_def ctx_def dcl) meth_def"
apply(erule find_meth_def.cases, clarsimp+)

apply(induct ty_x_d) apply(simp) apply(rename_tac ctx' dcl' ctxclds)
apply(cut_tac P = P and ctxa = ctx' and dcl = dcl' and ctxclds = ctxclds and
              meth = meth and ctx = ctx and meth_def = meth_def in wf_method_from_find') apply(simp)
apply(simp)
done

lemma find_type_lift_opts[rule_format]:
  "(\<forall>x\<in>set cl_var_ty_list. (\<lambda>(cl_k, var_k, ty_k). find_type_f P ctx cl_k = Some ty_k) x) \<longrightarrow>
      lift_opts (map (case_vd (\<lambda>clk vark. find_type_f P ctx clk)) (map (\<lambda>(cl_k, var_k, ty_k). vd_def cl_k var_k) cl_var_ty_list)) =
      Some (map (\<lambda>(cl, var, ty). ty) cl_var_ty_list)"
by (induct cl_var_ty_list, auto)

lemma find_md_in_pre_path[rule_format]:
  "find_meth_def_in_path_f path m = Some ctxmd \<longrightarrow> (\<forall>path'. find_meth_def_in_path_f (path @ path') m = Some ctxmd)"
by (induct path, auto split: option.splits)

lemma lift_opts_map:
  "\<forall>x\<in>set cl_var_ty_list. (\<lambda>(cl_k, var_k, ty_k). find_type_f P ctx cl_k = Some ty_k) x \<Longrightarrow>
      lift_opts (map (case_vd (\<lambda>clk vark. find_type_f P ctx clk)) (map (\<lambda>(cl_k, var_k, ty_k). vd_def cl_k var_k) cl_var_ty_list)) = Some (map (\<lambda>(cl, var, ty). ty) cl_var_ty_list)"
by (induct cl_var_ty_list, auto)

lemma m_in_list[rule_format]:
  "(\<forall>x\<in>set meth_def_meth_list. case_prod (\<lambda>meth_def. op = (method_name_f meth_def)) x) \<and>
   find_meth_def_in_list_f (map fst meth_def_meth_list) m = Some md \<longrightarrow>
       m \<in> snd ` set meth_def_meth_list"
by (induct meth_def_meth_list, auto simp add: method_name_f_def split: meth_def.splits meth_sig.splits)

lemma m_image_eq[rule_format]:
  "meth_def_def (meth_sig_def cl m list2) meth_body \<in> set meth_defs \<longrightarrow>
      m \<in> case_meth_def (\<lambda>meth_sig meth_body. case meth_sig of meth_sig_def cl meth vds \<Rightarrow> meth) ` set meth_defs"
by (induct meth_defs, auto)

lemma fmdip_to_mip[rule_format]:
  "find_meth_def_in_path_f path m = Some ctxmd \<longrightarrow> m \<in> set (methods_in_path_f (map snd path))"
apply(induct path) apply(simp) apply(clarsimp simp add: class_methods_f_def split: option.splits cld.splits)
apply(rename_tac aa bb)
apply(case_tac aa) apply(rename_tac meth_sig meth_body) apply(case_tac meth_sig) apply(clarsimp) apply(frule find_md_m_match') apply(clarsimp)
apply(frule find_meth_def_in_list_mem) apply(frule m_image_eq) apply(assumption)
done

lemma lift_opts_for_all[rule_format]:
  "lift_opts (map (case_vd (\<lambda>clk vark. find_type_f P ctx clk)) (map (\<lambda>(cl, var, ty). vd_def cl var) cl_var_ty_list)) = None \<and>
   (\<forall>x\<in>set cl_var_ty_list. (\<lambda>(cl, var, ty). find_type_f P ctx_def cl = Some ty) x) \<longrightarrow> False"
apply(induct cl_var_ty_list) apply(simp) apply(clarsimp) apply(case_tac ctx) apply(simp) done

lemma mty_preservation'''':
  "\<lbrakk>find_cld_f P ctx (fqn_def dcl') = Some (ctx, cld_def dcl' (cl_fqn (fqn_def dcl'')) fds' mds');
    find_cld_f P ctx (fqn_def dcl'') = Some (ctx, cld_def dcl'' cl'' fds'' mds'');
    find_path_rec_f P ctx cl'' [(ctx, cld_def dcl'' cl'' fds'' mds'')] = Some path;
    find_meth_def_in_path_f path m = Some (ctx'', meth_def_def (meth_sig_def cl_r m' vds) mb);
    find_type_f P ctx'' cl_r = Some ty_r; lift_opts (map (case_vd (\<lambda>clk vark. find_type_f P ctx'' clk)) vds) = Some tys;
    lift_opts (map (case_vd (\<lambda>clk vark. find_type_f P ctx' clk)) vds') = Some tys'; find_type_f P ctx' cl_r' = Some ty_r';
    find_meth_def_in_path_f ((ctx, cld_def dcl' (cl_fqn (fqn_def dcl'')) fds' mds') # path) m = Some (ctx', meth_def_def (meth_sig_def cl_r' m'' vds') mb');
    wf_program P\<rbrakk>
       \<Longrightarrow> tys' = tys \<and> ty_r' = ty_r"
using [[hypsubst_thin = true]]
apply(clarsimp simp add: class_methods_f_def split: option.splits)
apply(drule wf_cld_from_lu) apply(simp) apply(erule wf_classE) apply(erule wf_class_cE) apply(clarsimp)
apply(subgoal_tac "m \<in> snd ` set meth_def_meth_list")
 apply(clarsimp) apply(rename_tac md_m m) apply(drule_tac x = "(md_m, m)" in bspec, simp)+ apply(clarsimp split: option.splits)
 apply(case_tac ctx') apply(clarsimp)
 apply(case_tac md_m) apply(rename_tac meth_sig meth_body) apply(case_tac meth_sig) apply(rename_tac ms mb_m cl_r_m m vds_m) apply(clarsimp simp add: method_name_f_def)
 apply(erule_tac Q = "tys' = tys \<longrightarrow> ty_r' \<noteq> ty_r" in contrapos_pp) apply(clarsimp)
 apply(clarsimp simp add: methods_f_def find_path_f_def superclass_name_f_def split: option.splits if_split_asm)
 apply(frule fmdip_to_mip) apply(clarsimp) apply(rename_tac m mty mty') apply(drule_tac x = "(m, mty, mty')" in bspec, simp)+
 apply(clarsimp) apply(frule_tac f = snd in imageI) apply(simp) apply(thin_tac "m \<in> snd ` set meth_def_meth_list") apply(clarsimp)
 apply(clarsimp simp add: mtype_f_def split: option.splits meth_def.splits meth_sig.splits)
 apply(clarsimp simp add: find_meth_def_f_def find_path_f_def superclass_name_f_def split: option.splits if_split_asm)
 apply(frule path_append) apply(rename_tac ad) apply(frule_tac path = ad in path_append) apply(clarsimp)
 apply(frule_tac prefix = "[(ctx_def, cld_def dcl'' cl'' fds'' mds'')]" and suffix = path'' and
                 prefix' = "[(ctx_def, cld_def dcl' (cl_fqn (fqn_def dcl'')) (map (\<lambda>(cl, f, ty). fd_def cl f) cl_f_ty_list) (map fst meth_def_meth_list)),
                                 (ctx_def, cld_def dcl'' cl'' fds'' mds'')]" in fpr_same_suffix[rule_format]) apply(simp)
 apply(clarsimp simp add: class_methods_f_def)
apply(rule m_in_list) apply(simp)
done

lemma mty_preservation'''[rule_format]:
  "\<forall>suffix dcl. find_path_rec_f P ctx cl prefix = Some (prefix @ suffix) \<longrightarrow> wf_program P \<and> cl = cl_fqn (fqn_def dcl) \<longrightarrow>
     (\<forall>(ctx', cld') \<in> set suffix.
         (\<forall>prefix' suffix'. find_path_rec_f P ctx' (cl_fqn (fqn_def (class_name_f cld'))) prefix' = Some (prefix' @ suffix') \<and>
               mtype_f P (ty_def ctx' (class_name_f cld')) m = Some mty \<longrightarrow> mtype_f P (ty_def ctx dcl) m = Some mty))"
apply(induct_tac P ctx cl prefix rule: find_path_rec_f.induct)
 apply(simp)
apply(clarsimp split: option.splits)
apply(frule path_append) apply(clarify)
apply(clarsimp)
apply(erule disjE)
 apply(clarify)
 apply(clarsimp simp add: class_name_f_def split: cld.splits)
 apply(frule find_cld_name_eq) apply(frule_tac ctx = a in find_cld_name_eq)
 apply(clarsimp simp add: class_name_f_def split: cld.splits)
apply(case_tac b) apply(rename_tac dcl' cl' fds' mds')
apply(clarsimp simp add: superclass_name_f_def) apply(case_tac cl') apply(simp) apply(rename_tac fqn) apply(case_tac fqn) apply(rename_tac dcl'') apply(clarsimp)
apply(clarsimp split: option.splits)
apply(subgoal_tac "\<forall>aa b ab bb. (a = ab \<and> cld_def dcl' (cl_fqn (fqn_def dcl'')) fds' mds' = bb \<and> aa = ab \<and> b = bb)
                      \<longrightarrow> (\<forall>suffix. find_path_rec_f P ab (case bb of cld_def dcl cl fds mds \<Rightarrow> cl) (path @ [(ab, bb)]) = Some (path @ (ab, bb) # suffix) \<longrightarrow>
                                  (\<forall>dcl. (case bb of cld_def dcl cl fds mds \<Rightarrow> cl) = cl_fqn (fqn_def dcl) \<longrightarrow>
                                         (\<forall>x\<in>set suffix.
                                             (\<lambda>(ctx', cld').
                                                 (\<exists>prefix' suffix'.
                                                     case_option None (case_prod (\<lambda>ctx' cld. find_path_rec_f P ctx' (superclass_name_f cld) (prefix' @ [(ctx', cld)]))) (find_cld_f P ctx' (fqn_def (class_name_f cld'))) =
                                                     Some (prefix' @ suffix')) \<and>
                                                 mtype_f P (ty_def ctx' (class_name_f cld')) m = Some mty \<longrightarrow>
                                                 mtype_f P (ty_def ab dcl) m = Some mty)
                                              x)))")
defer
apply(force)
apply(thin_tac "\<And>aa b x y.
           \<lbrakk>a = aa \<and> cld_def dcl' (cl_fqn (fqn_def dcl'')) fds' mds' = b; x = aa \<and> y = b\<rbrakk>
           \<Longrightarrow> \<forall>suffix.
                 find_path_rec_f P aa (case b of cld_def dcl cl fds mds \<Rightarrow> cl) (path @ [(aa, b)]) =
                 Some (path @ (aa, b) # suffix) \<longrightarrow>
                 (\<forall>dcl. (case b of cld_def dcl cl fds mds \<Rightarrow> cl) = cl_fqn (fqn_def dcl) \<longrightarrow>
                        (\<forall>x\<in>set suffix.
                            case x of
                            (ctx', cld') \<Rightarrow>
                              (\<exists>prefix' suffix'.
                                  case_option None
                                   (\<lambda>(ctx', cld).
                                       find_path_rec_f P ctx' (superclass_name_f cld)
                                        (prefix' @ [(ctx', cld)]))
                                   (find_cld_f P ctx' (fqn_def (class_name_f cld'))) =
                                  Some (prefix' @ suffix')) \<and>
                              mtype_f P (ty_def ctx' (class_name_f cld')) m = Some mty \<longrightarrow>
                              mtype_f P (ty_def aa dcl) m = Some mty))")
apply(clarsimp)
apply(drule_tac x = "(aa, ba)" in bspec, simp)
apply(clarsimp)
apply(subgoal_tac "(\<exists>prefix' suffix'. find_path_rec_f P ab (case bb of cld_def dcl cl fds mds \<Rightarrow> cl) (prefix' @ [(ab, bb)]) = Some (prefix' @ suffix'))")
 apply(erule impE) apply(simp add: superclass_name_f_def) apply(thin_tac "\<exists>prefix suffix'. P prefix suffix'" for P)
 apply(thin_tac "mtype_f P (ty_def aa (class_name_f ba)) m = Some mty")
 apply(frule find_cld_name_eq) apply(clarsimp split: option.splits if_split_asm)
 apply(clarsimp simp add: mtype_f_def split: option.splits meth_def.splits meth_sig.splits)
 apply(rule)
  apply(clarsimp simp add: find_meth_def_f_def) apply(subgoal_tac "\<exists>path'. find_path_f P a (cl_fqn (fqn_def dcl')) = Some path'")
   apply(case_tac b) apply(clarsimp simp add: find_path_f_def superclass_name_f_def split: if_split_asm option.splits)
   apply(rename_tac meth_body cl list_char1 list_vd ty list_ty list_char2 cla list_fd list_md list_p1 path')
   apply(frule_tac path = path' in path_append) apply(rename_tac ag ah) apply(frule_tac path = ag in path_append) apply(clarify)
   apply(frule_tac suffix = path''a and suffix' = path''b and prefix' = "[(ac, cld_def list_char2 cla list_fd list_md)]" in fpr_same_suffix[rule_format], force)
   apply(simp) apply(clarify) apply(clarsimp simp add: class_methods_f_def split: option.splits)
  apply(clarsimp simp add: find_path_f_def superclass_name_f_def split: option.splits if_split_asm)
  apply(frule_tac path' = "(path @ [(a, cld_def dcl' (cl_fqn (fqn_def dcl'')) fds' mds'), (ac, b)])" in path_append) apply(clarsimp)
  apply(frule_tac suffix = path''a and prefix' = "[(a, cld_def dcl' (cl_fqn (fqn_def dcl'')) fds' mds'), (ac, b)]" in fpr_same_suffix') back apply(simp) apply(simp)
 apply(clarsimp) apply(rule)
  apply(clarsimp) apply(frule_tac ty_x_d = "(ty_def a dcl')" in wf_method_from_find[simplified]) apply(simp) apply(clarsimp)
  apply(erule wf_methE) apply(rename_tac ag ah ai aj ak al am an ao ap aq ar as at au av) apply(case_tac ag) apply(clarsimp)
 apply(clarsimp) apply(rule)
  apply(clarsimp) apply(frule_tac ty_x_d = "(ty_def a dcl')" in wf_method_from_find[simplified]) apply(simp) apply(clarsimp)
  apply(erule wf_methE) apply(clarsimp) apply(cut_tac lift_opts_for_all) apply(assumption) apply(rule) apply(simp) apply(assumption)
 apply(clarsimp)
 apply(thin_tac "find_path_rec_f P ab (case bb of cld_def dcl cl fds mds \<Rightarrow> cl) (prefix' @ [(ab, bb)]) = Some (prefix' @ suffix')")
 apply(thin_tac "find_cld_f P aa (fqn_def (class_name_f ba)) = Some (ab, bb)") apply(thin_tac "(aa, ba) \<in> set path''")
 apply(case_tac b) apply(frule_tac dcl = dcl'' in find_cld_name_eq) apply(clarsimp simp add: superclass_name_f_def)
 apply(rename_tac ctx ctx'' mb cl_r m' vds ty_r tys ctx' cl_r' m'' vds' ty_r' tys' mb' dcl'' cl'' fds'' mds'')
 apply(clarsimp simp add: find_meth_def_f_def find_path_f_def superclass_name_f_def split: option.splits if_split_asm)
 apply(thin_tac "find_path_rec_f P ctx cl'' (path @ [(ctx, cld_def dcl' (cl_fqn (fqn_def dcl'')) fds' mds'), (ctx, cld_def dcl'' cl'' fds'' mds'')]) =
        Some (path @ (ctx, cld_def dcl' (cl_fqn (fqn_def dcl'')) fds' mds') # path'')") apply(clarsimp) apply(rename_tac path'' path')
 apply(frule_tac path = path' in path_append) apply(frule_tac path = path'' in path_append) apply(clarify)
 apply(frule_tac suffix = path''a and suffix' = path''b and prefix' = "[(ctx, cld_def dcl'' cl'' fds'' mds'')]" in fpr_same_suffix[rule_format], force)
  apply(clarsimp simp del: find_meth_def_in_path_f.simps) apply(rename_tac path'')
 apply(frule_tac ctx' = ctx' and m'' = m'' and cl'' = cl'' and fds'' = fds'' and ctx'' = ctx'' and
                 path = "(ctx, cld_def dcl'' cl'' fds'' mds'') # path''" in mty_preservation'''', simp+)
apply(rule_tac x = prefix' in exI) apply(clarsimp simp add: superclass_name_f_def)
done

lemma mty_preservation'':
  "\<lbrakk>wf_program P; find_path_f P ctx (cl_fqn (fqn_def dcl)) = Some path; (ctx', cld') \<in> set path\<rbrakk> \<Longrightarrow>
     \<forall>prefix' suffix'.
        find_path_rec_f P ctx' (cl_fqn (fqn_def (class_name_f cld'))) prefix' = Some (prefix' @ suffix') \<and>
        mtype_f P (ty_def ctx' (class_name_f cld')) m = Some mty \<longrightarrow> mtype_f P (ty_def ctx dcl) m = Some mty"
apply(cut_tac x = "(ctx', cld')" in mty_preservation'''[of _ _ _ "[]", simplified])
apply(unfold find_path_f_def) apply(assumption) apply(simp+) done

lemma mty_preservation':
  "\<lbrakk>wf_program P; find_path_f P ctx (cl_fqn (fqn_def dcl)) = Some path; (ctx', cld') \<in> set path;
    find_path_f P ctx' (cl_fqn (fqn_def (class_name_f cld'))) = Some path'; mtype_f P (ty_def ctx' (class_name_f cld')) m = Some mty\<rbrakk>
        \<Longrightarrow> mtype_f P (ty_def ctx dcl) m = Some mty"
apply(cut_tac path = path and suffix' = path' in mty_preservation''[rule_format, of _ _ _ _ _ _ "[]"])
apply(assumption+) apply(rule) apply(simp add: find_path_f_def) apply(assumption+) done

lemma lift_opts_for_all_true[rule_format]:
  "\<forall>y_ty_list.
      (\<forall>x\<in>set cl_var_ty_list. (\<lambda>(cl_k, var_k, ty_k). find_type_f P ctx cl_k = Some ty_k) x) \<and>
      lift_opts (map (case_vd (\<lambda>clk vark. find_type_f P ctx clk)) (map (\<lambda>(cl_k, var_k, ty_k). vd_def cl_k var_k) cl_var_ty_list)) = Some (map snd y_ty_list) \<longrightarrow>
          map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list"
by (induct cl_var_ty_list, auto split: option.splits)

lemma mty_preservation:
  "\<lbrakk>wf_program P;
    find_meth_def_f P ty_x_d meth = Some (ctx, meth_def_def (meth_sig_def cl_r meth (map (\<lambda>(cl_k, var_k, ty_k). vd_def cl_k var_k) cl_var_ty_list)) meth_body);
    find_type_f P ctx cl_r = Some ty_r_d; \<forall>x\<in>set cl_var_ty_list. (\<lambda>(cl_k, var_k, ty_k). find_type_f P ctx cl_k = Some ty_k) x;
    mtype_f P ty_x_s meth = Some (mty_def (map snd y_ty_list) ty_r_s); is_sty_one P ty_x_d ty_x_s = Some True\<rbrakk>
       \<Longrightarrow> ty_r_d = ty_r_s \<and> map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list"
apply(case_tac "ty_x_d = ty_x_s")
 apply(clarsimp) apply(clarsimp simp add: mtype_f_def find_type_lift_opts[simplified] split: option.splits)
apply(simp add: is_sty_one_def split: option.splits)
 apply(case_tac ty_x_s) apply(clarsimp simp add: mtype_f_def find_meth_def_f_def)
apply(clarsimp) apply(rename_tac path_d ctx_s cld_s)
apply(case_tac ty_x_d) apply(clarsimp) apply(clarsimp) apply(rename_tac ctx_d dcl_d)
apply(clarsimp simp add: find_meth_def_f_def split: option.splits)
apply(subgoal_tac "\<exists>path_s. find_path_f P ctx_s (cl_fqn (fqn_def (class_name_f cld_s))) = Some path_s")
 apply(clarify) apply(frule_tac path = path_d and path' = path_s in mty_preservation') apply(simp+)
 apply(clarsimp simp add: mtype_f_def split: option.splits meth_def.splits meth_sig.splits)
 apply(clarsimp simp add: find_meth_def_f_def)
 apply(rule_tac P = P and ctx = ctx in lift_opts_for_all_true) apply(simp)
apply(clarsimp simp add: mtype_f_def find_meth_def_f_def split: option.splits)
done

lemma map_not_mem:
  "\<lbrakk>(y_k, ty_k, var_k, var'_k, v_k) \<in> set y_ty_var_var'_v_list; x' \<notin> (\<lambda>(y, ty, var, var', v). x_var var') ` set y_ty_var_var'_v_list\<rbrakk>
         \<Longrightarrow> x_var var'_k \<noteq> x'"
by (force)

lemma map_fst:
   "map fst (map (\<lambda>(y, ty, var, var', v). (x_var var', ty)) y_ty_var_var'_v_list) = map (\<lambda>(y, ty, var, var', v). x_var var') y_ty_var_var'_v_list"
by (force)

lemma supertype_top:
  "sty_one P ty ty' \<Longrightarrow> ty = ty_top \<longrightarrow> ty' = ty_top"
by (induct rule: sty_one.induct, auto)

lemma top_not_subtype[rule_format]:
  "sty_one P ty_top (ty_def ctx dcl) \<longrightarrow> False"
by (rule, drule supertype_top, simp)

lemma f_in_found_fds:
  "ftype_in_fds_f P ctx fds f = ty_opt_bot_opt (Some ty_f) \<longrightarrow> f \<in> case_fd (\<lambda>cl f. f) ` set fds"
by (induct fds, auto split: fd.splits)

lemma ftype_fields[rule_format]:
  "ftype_in_path_f P path_s f = Some ty_f \<longrightarrow> f \<in> set (fields_in_path_f path_s)"
apply(induct path_s) apply(simp) apply(clarsimp split: option.splits)
apply(case_tac b) apply(clarsimp) apply(rename_tac ctx path_s dcl cl fds mds)
apply(clarsimp simp add: class_fields_f_def split: ty_opt_bot.splits option.splits) apply(simp add: f_in_found_fds)
done

lemma no_field_hiding''':
  "\<forall>suffix. find_path_rec_f P ctx cl prefix = Some (prefix @ suffix) \<longrightarrow> wf_program P \<longrightarrow>
     (\<forall>(ctx, cld) \<in> set suffix.
         (\<forall>prefix' suffix'. find_path_rec_f P ctx (cl_fqn (fqn_def (class_name_f cld))) prefix' = Some (prefix' @ suffix') \<and>
               f \<in> set (fields_in_path_f suffix') \<longrightarrow> f \<in> set (fields_in_path_f suffix)))"
apply(induct_tac P ctx cl prefix rule: find_path_rec_f.induct)
 apply(simp)
apply(clarsimp split: option.splits)

apply(subgoal_tac "\<forall>aa ba aaa bb.
           (a = aaa \<and> b = bb \<and> aa = aaa \<and> ba = bb)
           \<longrightarrow> (\<forall>suffix. find_path_rec_f P aaa (superclass_name_f bb) (path @ [(aaa, bb)]) = Some (path @ (aaa, bb) # suffix) \<longrightarrow>
                       (\<forall>x\<in>set suffix.
                           (\<lambda>(ctx, cld). (\<exists>prefix' suffix'.
                                             case_option None (case_prod (\<lambda>ctx' cld. find_path_rec_f P ctx' (superclass_name_f cld) (prefix' @ [(ctx', cld)]))) (find_cld_f P ctx (fqn_def (class_name_f cld))) =
                                             Some (prefix' @ suffix') \<and>
                                             f \<in> set (fields_in_path_f suffix')) \<longrightarrow>
                                         f \<in> set (fields_in_path_f suffix))
                            x))")
 defer
apply(thin_tac _)+
apply(force)
apply(thin_tac "\<And>aa ba x y.
           \<lbrakk>a = aa \<and> b = ba; x = aa \<and> y = ba\<rbrakk>
           \<Longrightarrow> \<forall>suffix.
                 find_path_rec_f P aa (superclass_name_f ba) (path @ [(aa, ba)]) =
                 Some (path @ (aa, ba) # suffix) \<longrightarrow>
                 (\<forall>x\<in>set suffix.
                     case x of
                     (ctx, cld) \<Rightarrow>
                       (\<exists>prefix' suffix'.
                           case_option None
                            (\<lambda>(ctx', cld).
                                find_path_rec_f P ctx' (superclass_name_f cld) (prefix' @ [(ctx', cld)]))
                            (find_cld_f P ctx (fqn_def (class_name_f cld))) =
                           Some (prefix' @ suffix') \<and>
                           f \<in> set (fields_in_path_f suffix')) \<longrightarrow>
                       f \<in> set (fields_in_path_f suffix))")
apply(clarsimp)
apply(frule path_append) apply(clarify)
apply(erule_tac x = "tl suffix" in allE)
apply(clarsimp)
apply(erule disjE)
 apply(clarify)
 apply(case_tac fqn)
 apply(clarsimp simp del: fmdip_cons simp add: class_name_f_def split: cld.splits)
 apply(frule find_cld_name_eq) apply(frule_tac ctx = a in find_cld_name_eq)
 apply(clarsimp simp del: fmdip_cons simp add: class_name_f_def split: cld.splits)
 apply (rename_tac list1 cl list2 list3)
 apply(frule_tac path = "prefix' @ suffix'" in path_append) apply(clarsimp simp del: fmdip_cons)
 apply(frule_tac prefix = "path @ [(ab, cld_def list1 cl list2 list3)]" and suffix = path'' and
                 prefix' = "prefix' @ [(ab, cld_def list1 cl list2 list3)]" and suffix' = path''a in fpr_same_suffix[rule_format])
 apply(clarsimp) apply(simp)
apply(drule_tac x = "(aa, ba)" in bspec, simp)
apply(force)
done

lemma no_field_hiding'':
  "\<lbrakk>find_path_f P ctx' cl = Some suffix; wf_program P; (ctx, cld) \<in> set suffix\<rbrakk>
      \<Longrightarrow> \<forall>prefix' suffix'.
            find_path_rec_f P ctx (cl_fqn (fqn_def (class_name_f cld))) prefix' = Some (prefix' @ suffix') \<and> f \<in> set (fields_in_path_f suffix') \<longrightarrow>
                        f \<in> set (fields_in_path_f suffix)"
apply(cut_tac x = "(ctx, cld)" in no_field_hiding'''[of _ _ _ "[]", rule_format]) apply(simp add: find_path_f_def)+ done

lemma no_field_hiding':
  "\<lbrakk>find_path_f P ctx' cl = Some path; wf_program P; (ctx, cld) \<in> set path;
    find_path_f P ctx (cl_fqn (fqn_def (class_name_f cld))) = Some path'; f \<in> set (fields_in_path_f path')\<rbrakk>
         \<Longrightarrow> f \<in> set (fields_in_path_f path)"
apply(cut_tac no_field_hiding''[rule_format, of _ _ _ _ _ _ "[]"]) apply(assumption+) apply(unfold find_path_f_def) apply(rule) apply(simp+) done

lemma no_field_hiding:
  "\<lbrakk>wf_program P; is_sty_one P ty_x_d ty_x_s = Some True; ftype_f P ty_x_s f = Some ty_f; fields_f P ty_x_d = Some fields_oid\<rbrakk>
        \<Longrightarrow> f \<in> set fields_oid"
apply(case_tac ty_x_s) apply(simp add: ftype_f_def)
apply(simp add: is_sty_one_def split: option.splits)
apply(case_tac ty_x_d) apply(simp) apply(clarsimp) apply(rename_tac ctx_s dcl_s path_d ctx_d dcl_d)
apply(simp add: ftype_f_def split: option.splits)
apply(clarsimp simp add: fields_f_def) apply(drule ftype_fields)
apply(frule no_field_hiding') apply(simp add: ftype_fields class_name_f_def)+
done

lemma ftype_pre_path[rule_format]:
  "ftype_in_path_f P path_s f = Some ty_f \<longrightarrow> ftype_in_path_f P (path_s @ path'') f = Some ty_f"
by (induct path_s, auto split: option.splits ty_opt_bot.splits)

lemma fields_non_intersection[rule_format]:
  " (\<lambda>(cl, f, ty). f) ` set cl_f_ty_list \<inter> set (fields_in_path_f path'') = {}
    \<and> f \<in> set (fields_in_path_f path'')
       \<longrightarrow> ftype_in_fds_f P ctx_def (map (\<lambda>(cl, f, ty). fd_def cl f) cl_f_ty_list) f = ty_opt_bot_opt None"
by (induct cl_f_ty_list, auto)

lemma f_notin_list[rule_format]:
  "f \<notin> set (map (\<lambda>(cl, f, ty). f) cl_f_ty_list) \<longrightarrow> ftype_in_fds_f P ctx_def (map (\<lambda>(cl, f, ty). fd_def cl f) cl_f_ty_list) f = ty_opt_bot_opt None"
by (induct cl_f_ty_list, auto)

declare find_path_rec_f.simps[simp del]
lemma ftype_preservation''''':
  "\<lbrakk>find_path_rec_f P ctx cl (prefix @ [cld']) = Some (prefix @ cld' # path'');
    find_type_f P ctx_def cl = Some ty; fields_f P ty = Some fs;
    ftype_in_path_f P path'' f = Some ty_f;
    (set (map (\<lambda>(cl, f, ty). f) cl_f_ty_list)) \<inter> (set fs) = {}\<rbrakk>
        \<Longrightarrow> ftype_in_fds_f P ctx (map (\<lambda>(cl, f, ty). fd_def cl f) cl_f_ty_list) f = ty_opt_bot_opt None"
apply(clarsimp simp add: fields_f_def split: option.splits) apply(rename_tac path)
apply(case_tac cl) apply(simp add: find_path_rec_f.simps) apply(clarsimp split: fqn.splits option.splits)
apply(rename_tac dcl ctx'' cld'') apply(case_tac ctx'') apply(case_tac ctx) apply(clarsimp simp add: find_path_f_def)
apply(frule_tac prefix = "prefix @ [cld']" and suffix = path'' and prefix' = "[]" in fpr_same_suffix[rule_format]) apply(simp)
apply(clarsimp) apply(drule ftype_fields) apply(cut_tac fields_non_intersection) apply(force) apply(force)
done
declare find_path_rec_f.simps[simp]

lemma ftype_preservation'''':
  "\<forall>suffix. find_path_rec_f P ctx cl prefix = Some (prefix @ suffix) \<longrightarrow> wf_program P \<longrightarrow>
     (\<forall>(ctx, cld) \<in> set suffix.
         (\<forall>prefix' suffix'. find_path_rec_f P ctx (cl_fqn (fqn_def (class_name_f cld))) prefix' = Some (prefix' @ suffix') \<and>
               ftype_in_path_f P suffix' f = Some ty \<longrightarrow> ftype_in_path_f P suffix f = Some ty))"
apply(induct_tac P ctx cl prefix rule: find_path_rec_f.induct)
 apply(simp)
apply(clarsimp split: option.splits)
apply(subgoal_tac "\<forall>aa ba aaa bb.
           (a = aaa \<and> b = bb \<and> aa = aaa \<and> ba = bb)
           \<longrightarrow> (\<forall>suffix. find_path_rec_f P aaa (superclass_name_f bb) (path @ [(aaa, bb)]) = Some (path @ (aaa, bb) # suffix) \<longrightarrow>
                       (\<forall>x\<in>set suffix.
                           (\<lambda>(ctx, cld). (\<exists>prefix' suffix'.
                                             case_option None (case_prod (\<lambda>ctx' cld. find_path_rec_f P ctx' (superclass_name_f cld) (prefix' @ [(ctx', cld)]))) (find_cld_f P ctx (fqn_def (class_name_f cld))) =
                                             Some (prefix' @ suffix') \<and>
                                             ftype_in_path_f P suffix' f = Some ty) \<longrightarrow>
                                         ftype_in_path_f P suffix f = Some ty)
                            x))")
defer
apply(thin_tac _)+
apply(force)
apply(clarsimp)
apply(frule path_append) apply(clarify)
apply(erule_tac x = "tl suffix" in allE)
apply(clarsimp)
apply(erule disjE)
 apply(clarify)
 apply(case_tac fqn)
 apply(clarsimp simp add: class_name_f_def split: cld.splits)
 apply(frule find_cld_name_eq) apply(frule_tac ctx = a in find_cld_name_eq)
 apply(clarsimp simp add: class_name_f_def split: cld.splits)
 apply(rename_tac list1 cl list2 list3)
 apply(frule_tac path = "prefix' @ suffix'" in path_append) apply(clarsimp)
 apply(frule_tac prefix = "path @ [(ab, cld_def list1 cl list2 list3)]" and suffix = path'' and
                 prefix' = "prefix' @ [(ab, cld_def list1 cl list2 list3)]" and suffix' = path''a in fpr_same_suffix[rule_format])
 apply(clarsimp) apply(clarsimp)
apply(drule_tac x = "(aa, ba)" in bspec, simp)
apply(clarsimp)
apply(subgoal_tac
  "(\<exists>prefix' suffix'.
            find_path_rec_f P ab (superclass_name_f bb) (prefix' @ [(ab, bb)]) = Some (prefix' @ suffix') \<and> ftype_in_path_f P suffix' f = Some ty)")
 apply(clarsimp)
 apply(subgoal_tac "ftype_in_fds_f P a (class_fields_f b) f = ty_opt_bot_opt None") apply(simp)
 apply(frule_tac cld' = b in wf_cld_from_lu) apply(simp) apply(erule wf_classE) apply(erule wf_class_cE)
 apply(clarsimp simp add: superclass_name_f_def class_fields_f_def)
 apply(rule ftype_preservation''''') apply(simp+)
apply(force)
done

lemma ftype_preservation''':
  "\<lbrakk>find_path_f P ctx' cl = Some suffix; wf_program P; (ctx, cld) \<in> set suffix\<rbrakk>
      \<Longrightarrow> \<forall>prefix' suffix'.
            find_path_rec_f P ctx (cl_fqn (fqn_def (class_name_f cld))) prefix' = Some (prefix' @ suffix') \<and> ftype_in_path_f P suffix' f = Some ty \<longrightarrow>
                        ftype_in_path_f P suffix f = Some ty"
apply(cut_tac x = "(ctx, cld)" in ftype_preservation''''[of _ _ _ "[]", rule_format]) apply(simp add: find_path_f_def)+ done

lemma ftype_preservation'':
  "\<lbrakk>find_path_f P ctx' cl = Some path; wf_program P; (ctx, cld) \<in> set path;
    find_path_f P ctx (cl_fqn (fqn_def (class_name_f cld))) = Some path'; ftype_in_path_f P path' f = Some ty\<rbrakk>
         \<Longrightarrow> ftype_in_path_f P path f = Some ty"
apply(cut_tac ftype_preservation'''[rule_format, of _ _ _ _ _ _ "[]"]) apply(assumption+) apply(unfold find_path_f_def) apply(rule) apply(simp+) done

lemma ftype_preservation'[simplified]:
  "\<lbrakk>wf_program P; sty_one P ty_x_d ty_x_s; ftype P ty_x_s f ty_f\<rbrakk>
     \<Longrightarrow> ftype P ty_x_d f ty_f"
apply(case_tac ty_x_s) apply(simp add: ftype_f_def)
apply(simp add: is_sty_one_def split: option.splits)
apply(case_tac ty_x_d) apply(simp) apply(clarsimp) apply(rename_tac ctx_s dcl_s path_d ctx_d dcl_d)
apply(simp add: ftype_f_def split: option.splits)
apply(rename_tac path_s cl_s fds_s mds_s)
apply(rule ftype_preservation'') apply(simp add: class_name_f_def)+
done

lemma ftype_preservation[simplified]:
  "\<lbrakk>wf_program P;
    \<forall>x\<in>dom \<Gamma>. wf_object P H (L x) (\<Gamma> x); \<Gamma> x = Some ty_x_s; ftype P ty_x_s f ty_f_s;
    L x = Some (v_oid oid_x); H oid_x = Some (ty_x_d, fs_oid); ftype P ty_x_d f ty_f_d\<rbrakk>
     \<Longrightarrow> ty_f_s = ty_f_d"
apply(drule_tac x = x in bspec, simp add: domI)
apply(erule wf_objectE)
 apply(simp)
apply(clarsimp)
apply(erule sty_option.cases)
apply(clarsimp)
apply(simp add: ftype_preservation')
done

lemma map_f:
  "\<forall>cl_f_ty_list. map (\<lambda>(cl, f). fd_def cl f) cl_f_list = map (\<lambda>(cl, f, ty). fd_def cl f) cl_f_ty_list \<longrightarrow>
   map (\<lambda>(cl, f). f) cl_f_list = map (\<lambda>(cl, f, ty). f) cl_f_ty_list"
by (induct cl_f_list, auto)

lemma fields_to_owner[rule_format]:
  "f \<in> set (fields_in_path_f path) \<longrightarrow> (\<exists>cld \<in> set (map snd path). \<exists>cl_f. fd_def cl_f f \<in> set (class_fields_f cld))"
apply(induct path) apply(simp) apply(clarsimp) apply(rename_tac cld path fd)
apply(clarsimp simp add: class_fields_f_def split: option.splits cld.splits fd.splits)
apply(force)
done

lemma ftype_in_fds_none[rule_format]:
  "f \<notin> (\<lambda>(cl, f, ty). f) ` set cl_f_ty_list \<longrightarrow> ftype_in_fds_f P ctx (map (\<lambda>(cl, f, ty). fd_def cl f) cl_f_ty_list) f = ty_opt_bot_opt None"
by (induct cl_f_ty_list, auto)

lemma ftype_in_fds_some[rule_format]:
  "(cl_f, f, ty_f) \<in> set cl_f_ty_list \<and> distinct (map (\<lambda>(cl, f, ty). f) cl_f_ty_list) \<and> find_type_f P ctx cl_f = Some ty_f
        \<longrightarrow> ftype_in_fds_f P ctx (map (\<lambda>(cl, f, ty). fd_def cl f) cl_f_ty_list) f = ty_opt_bot_opt (Some ty_f)"
apply(induct cl_f_ty_list) apply(simp) apply(clarsimp) apply(safe) apply(force) apply(simp)
apply(frule ftype_in_fds_none) apply(force)
done

lemma no_ty_bot[THEN mp]:
  "(\<forall>x\<in>set cl_f_ty_list. (\<lambda>(cl, f, ty). find_type_f P ctx_def cl = Some ty) x)
       \<longrightarrow> ftype_in_fds_f P ctx' (map (\<lambda>(cl, f, ty). fd_def cl f) cl_f_ty_list) f \<noteq> ty_opt_bot_bot"
apply(induct cl_f_ty_list) apply(simp) apply(clarsimp split: if_split_asm option.splits)
apply(case_tac ctx', simp) (* should get rid of ctx dependency here *)
done

lemma field_has_type'[rule_format]:
  "(cl_f, f, ty_f) \<in> set cl_f_ty_list \<and>
   (\<forall>(ctx, cld) \<in> set path. wf_class P cld) \<and>
   (ctx, cld_def dcl cl (map (\<lambda>(cl, f, ty). fd_def cl f) cl_f_ty_list) mds) \<in> set path \<and>
   distinct (map (\<lambda>(cl, f, ty). f) cl_f_ty_list) \<and>
   find_type_f P ctx cl_f = Some ty_f
           \<longrightarrow> (\<exists>ty'. ftype_in_path_f P path f = Some ty')"
apply(induct path) apply(simp)
apply(simp) apply(rule)
 apply(elim conjE) apply(erule disjE) apply(clarsimp)
 apply(subgoal_tac
    "ftype_in_fds_f P ctx (class_fields_f (cld_def dcl cl (map (\<lambda>(cl, f, ty). fd_def cl f) cl_f_ty_list) mds)) f = ty_opt_bot_opt (Some ty_f)") apply(simp)
 apply(simp add: class_fields_f_def) apply(rule ftype_in_fds_some) apply(force)
apply(case_tac a) apply(rename_tac ctx' cld') apply(simp) apply(case_tac "ftype_in_fds_f P ctx' (class_fields_f cld') f")
 apply(rename_tac ty_opt) apply(case_tac ty_opt)
  apply(clarsimp)
 apply(clarsimp)
apply(clarsimp)
apply(erule wf_classE) apply(erule wf_class_cE) apply(clarsimp simp add: class_fields_f_def)
apply(frule no_ty_bot) apply(force)
done

lemma mem_class_wf:
  "\<lbrakk>wf_program P; cld \<in> set P\<rbrakk> \<Longrightarrow> wf_class P cld"
apply(erule wf_programE) apply(drule_tac x = cld in bspec, simp) apply(clarsimp) done

lemma field_has_type:
  "\<lbrakk>wf_program P; fields P ty_oid (Some f_list); f \<in> set f_list\<rbrakk> \<Longrightarrow> \<exists>ty. ftype P ty_oid f ty"
apply(simp) apply(clarsimp simp add: fields_f_def split: option.splits) apply(rename_tac path)
apply(case_tac ty_oid) apply(simp) apply(clarsimp) apply(rename_tac dcl)
apply(frule fields_to_owner) apply(clarsimp) apply(rename_tac ctx' cld cl_f)
apply(frule clds_in_path_exist) apply(drule_tac x = "(ctx', cld)" in bspec, simp) apply(clarsimp)
apply(frule mem_class_wf, simp)
apply(erule wf_classE) apply(erule wf_class_cE) apply(clarsimp simp add: class_fields_f_def)
apply(rename_tac cl_f ty_f) apply(drule_tac x = "(cl_f, f, ty_f)" in bspec, simp) apply(clarsimp)
apply(simp add: ftype_f_def)
apply(rule_tac cl_f = cl_f and ty_f = ty_f and cl_f_ty_list = cl_f_ty_list and ctx = ctx' and
               dcl = dclb and cl = cla and mds = "(map fst meth_def_meth_list)" in field_has_type')
apply(simp) apply(case_tac ctx') apply(simp)
apply(clarify) apply(drule_tac cl = "cl_fqn (fqn_def dcl)" and ctxcld = "(a, b)" in all_in_path_found) apply(simp)
apply(clarsimp) apply(rule wf_cld_from_lu) apply(simp) apply(force)
done

lemma exists_three_in_five:
  "var_k \<in> set (map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list) \<longrightarrow>
   (\<exists>y cl var' v. (y, cl, var_k, var', v) \<in> set y_cl_var_var'_v_list)"
by (induct y_cl_var_var'_v_list, auto)

lemma map_xx[rule_format]:
  "(y, cl, var_k, var', v) \<in> set y_cl_var_var'_v_list \<longrightarrow>
   (x_var var_k, x_var var') \<in> set (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list)"
by (induct y_cl_var_var'_v_list, auto)

lemma map_of_vd[rule_format]:
  "\<forall>cl_var_ty_list.
      map (\<lambda>(y, cl, var, var', v). vd_def cl var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). vd_def cl var) cl_var_ty_list
      \<longrightarrow> map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list"
by (induct y_cl_var_var'_v_list, auto)

lemma mem_vd:
  "vd_def cl_k var_k \<in> set (map (\<lambda>(y, cl, var, var', v). vd_def cl var) y_cl_var_var'_v_list) \<longrightarrow>
   var_k \<in> set (map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list)"
by (induct y_cl_var_var'_v_list, auto)

lemma exists_var':
  "\<lbrakk>distinct (map (\<lambda>(cl, var, ty). var) cl_var_ty_list);
    map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list;
    map_of (map (\<lambda>(cl, var, ty). (x_var var, ty)) cl_var_ty_list) var_k = Some ty_k\<rbrakk>
      \<Longrightarrow> \<exists>var'_k. map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) var_k = Some (x_var var'_k)"
apply(drule map_of_SomeD) apply(clarsimp, hypsubst_thin) apply(rename_tac cl_k var_k)
apply(subgoal_tac "var_k \<in> set (map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list)")
 apply(simp (no_asm_use)) apply(clarify) apply(rename_tac y_k cl_k' var_k var'_k v_k)
 apply(rule_tac x = var'_k in exI)
 apply(rule map_of_is_SomeI)
  apply(drule distinct_var, assumption+)
 apply(rule map_xx, assumption)
by force

lemma map_y:
  "\<lbrakk>((y_k, cl_k, var_k, var'_k, v_k), y'_k, ty_k) \<in> set (zip y_cl_var_var'_v_list y_ty_list);
    map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list = map fst y_ty_list\<rbrakk>
      \<Longrightarrow> (y_k, ty_k) \<in> set y_ty_list"
apply(clarsimp simp add: set_zip)
apply(drule_tac f = "\<lambda>(y, cl, var, var', v). y" in arg_cong)
apply(drule_tac f1 = "\<lambda>(y, cl, var, var', v). y" in nth_map[THEN sym])
apply(frule_tac f = "\<lambda>(y, ty). y" in arg_cong)
apply(case_tac "y_ty_list ! i")
apply(force simp add: in_set_conv_nth)
done

lemma set_zip_var'_v:
  "\<lbrakk>((y_k, cl_k, var_k, var'_k, v_k), y'_k, ty_k) \<in> set (zip y_cl_var_var'_v_list y_ty_list)\<rbrakk>
       \<Longrightarrow> (x_var var'_k, v_k) \<in> set (map (\<lambda>(y, cl, var, var', y). (x_var var', y)) y_cl_var_var'_v_list)"
apply(subgoal_tac "(y_k, cl_k, var_k, var'_k, v_k) \<in> set y_cl_var_var'_v_list")
by (force simp add: set_zip)+

lemma map_of_map_zip_none:
  "\<lbrakk>map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list = map fst y_ty_list;
    map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)) x_G = None\<rbrakk>
      \<Longrightarrow> map_of (map (\<lambda>(y, cl, var, var', y). (x_var var', y)) y_cl_var_var'_v_list) x_G = None"
apply(drule map_length_y)
apply(clarsimp simp add: map_of_eq_None_iff)
apply(erule contrapos_np)
apply(simp only: set_map[THEN sym] fst_zip_eq)
by force

lemma map_of_map_zip_some:
  "\<lbrakk>distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list);
    map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list = map fst y_ty_list;
    map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)) x_G = Some ty_k\<rbrakk>
      \<Longrightarrow> \<exists>v_k. map_of (map (\<lambda>(y, cl, var, var', y). (x_var var', y)) y_cl_var_var'_v_list) x_G = Some v_k"
apply(drule map_of_SomeD)
apply(clarsimp) apply(rename_tac y cl var var' v y')
apply(subgoal_tac "(y, cl, var, var', v) \<in> set y_cl_var_var'_v_list")
 apply(rule_tac x = v in exI)
 apply(rule map_of_is_SomeI)
  apply(simp only: map_fst_two' distinct_x_var')
 apply(force)
by (force simp add: set_zip)

lemma x'_not_in_list:
  "\<lbrakk>(y_k, cl_k, var_k, var'_k, v_k) \<in> set y_cl_var_var'_v_list;
    x' \<notin> (\<lambda>(y, cl, var, var', v). x_var var') ` set y_cl_var_var'_v_list\<rbrakk>
      \<Longrightarrow> x_var var'_k \<noteq> x'"
by (erule contrapos_nn, force)

lemma nth_in_set:
  "\<lbrakk>i < length y_ty_list; map fst y_ty_list ! i = y_k\<rbrakk> \<Longrightarrow> y_k \<in> set (map fst y_ty_list)"
apply(subgoal_tac "\<exists>i<length (map fst y_ty_list). map fst y_ty_list ! i = y_k")
 apply(simp only: in_set_conv_nth[THEN sym])
apply(rule_tac x = i in exI) apply(clarsimp)
done

lemma map_one_in_two:
  "y_k \<in> set (map fst y_ty_list) \<longrightarrow> (\<exists>ty. (y_k, ty) \<in> set y_ty_list)"
by (induct y_ty_list, auto)

lemma exists_i: (* can probably simplify a lot *)
  "\<lbrakk>distinct (map (\<lambda>(cl, var, ty). var) cl_var_ty_list);
    (y_k, cl_ka, var_k, var'_k, v_k) \<in> set y_cl_var_var'_v_list;
    (cl_k, var_k, ty_k) \<in> set cl_var_ty_list;
     map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list\<rbrakk> \<Longrightarrow>
        \<exists>i < length cl_var_ty_list. cl_var_ty_list ! i = (cl_k, var_k, ty_k) \<and> y_cl_var_var'_v_list ! i = (y_k, cl_ka, var_k, var'_k, v_k)"
apply(simp only: in_set_conv_nth)
apply(erule_tac P = "\<lambda>i. i < length cl_var_ty_list \<and> cl_var_ty_list ! i = (cl_k, var_k, ty_k)" in exE) apply(erule conjE)
apply(rule_tac x = x in exI)
apply(simp)
apply(drule_tac f = "\<lambda>(cl, var, ty). var" in arg_cong)
apply(frule_tac f1 = "\<lambda>(cl, var, ty). var" in nth_map[THEN sym])
apply(drule_tac t = "map (\<lambda>(cl, var, ty). var) cl_var_ty_list ! x" in sym)
apply(drule_tac s = "(\<lambda>(cl, var, ty). var) (cl_var_ty_list ! x)" in trans)
apply(simp)
apply(thin_tac "(\<lambda>(cl, var, ty). var) (cl_var_ty_list ! x) = (\<lambda>(cl, var, ty). var) (cl_k, var_k, ty_k)")
apply(drule sym)
apply(simp)
apply(erule exE) apply(rename_tac j) apply(erule conjE)
apply(simp only: distinct_conv_nth)
apply(erule_tac x = x in allE)
apply(drule_tac s = "map (\<lambda>(cl, var, ty). var) cl_var_ty_list" in sym)
apply(drule map_length_var)
apply(simp)
apply(erule_tac x = j in allE)
apply(simp)
done

lemma y_ty_match:
  "\<lbrakk>i < length cl_var_ty_list; cl_var_ty_list ! i = (cl_k, var_k, ty_k);
    y_cl_var_var'_v_list ! i = (y_k, cl_ka, var_k, var'_k, v_k);
    map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list = map fst y_ty_list;
    map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list\<rbrakk> \<Longrightarrow>
       y_ty_list ! i = (y_k, ty_k)"
apply(drule_tac f = "\<lambda>(cl, var, ty). ty" in arg_cong)
apply(frule_tac f1 = "\<lambda>(cl, var, ty). ty" in nth_map[THEN sym])
apply(drule_tac t = "map (\<lambda>(cl, var, ty). ty) cl_var_ty_list ! i" in sym)
apply(frule map_length_y) apply(frule map_length_ty)
apply(drule_tac t = "length y_ty_list" in sym) apply(simp)
apply(drule_tac f = "\<lambda>(y, cl, var, var', v). y" in arg_cong)
apply(frule_tac f1 = "\<lambda>(y, cl, var, var', v). y" in nth_map[THEN sym])
apply(drule_tac t = "map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list ! i" in sym)
apply(case_tac "y_ty_list ! i") apply(simp)
done

lemma map_of_ty_k:
  "\<lbrakk>distinct (map (\<lambda>(cl, var, ty). var) cl_var_ty_list);
    distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list);
    (y_k, cl_ka, var_k, var'_k, v_k) \<in> set y_cl_var_var'_v_list;
    (cl_k, var_k, ty_k) \<in> set cl_var_ty_list;
     map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list = map fst y_ty_list;
     map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list;
     map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list\<rbrakk>
       \<Longrightarrow> map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)) (x_var var'_k) = Some ty_k"
apply(frule map_length_y)
apply(rule map_of_is_SomeI)
 apply(simp only: fst_zip_eq)
 apply(simp only: distinct_x_var')
apply(clarsimp)
apply(frule map_length_var)
apply(frule exists_i, simp+) apply(erule exE)
apply(drule_tac t = "length y_ty_list" in sym) apply(clarsimp)
apply(frule y_ty_match, assumption+)
apply(subgoal_tac "zip y_cl_var_var'_v_list y_ty_list ! i = (y_cl_var_var'_v_list ! i,  y_ty_list ! i)")
 apply(drule_tac f = "\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)" in arg_cong)
 apply(subgoal_tac "i < length (zip y_cl_var_var'_v_list y_ty_list)")
  apply(frule_tac f1 = "\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)" in nth_map[THEN sym])
  apply(drule_tac t = "map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list) ! i" in sym)
  apply(drule_tac s = "(\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list ! i)" in trans)
  apply(simp)
  apply(subgoal_tac "\<exists>j<length (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)). map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list) ! j = (x_var var'_k, ty_k)")
   apply(simp only: in_set_conv_nth[THEN sym])
   apply(simp)
  apply(rule_tac x = i in exI) apply(simp)
 apply(force)
apply(rule nth_zip) apply(simp) apply(simp)
done

lemma map_of_ty_k':
  "\<lbrakk>distinct (map (\<lambda>(cl, var, ty). var) cl_var_ty_list); distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list);
     x' \<notin> (\<lambda>(y, cl, var, var', v). x_var var') ` set y_cl_var_var'_v_list; map fst y_cl_var_var'_v_list = map fst y_ty_list;
     map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list; map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list;
     map_of (map (\<lambda>(cl, var, y). (x_var var, y)) cl_var_ty_list) (x_var var) = Some ty_var\<rbrakk>
    \<Longrightarrow> (if x_var (case_option var (case_x (\<lambda>var'. var') var) (map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) (x_var var))) = x' then Some ty_x_m
        else (\<Gamma> ++ map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)))
              (x_var (case_option var (case_x (\<lambda>var'. var') var)
                       (map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) (x_var var))))) =
       Some ty_var"
apply(frule exists_var') apply(simp add: weaken_list_var) apply(simp) apply(clarsimp split del: if_split) apply(clarsimp)
apply(drule map_of_SomeD)+ apply(clarsimp split del: if_split) apply(frule x'_not_in_list, simp+)
apply(frule map_of_ty_k) apply(simp add: weaken_list_y weaken_list_var)+
done

lemma var_not_var'_x':
  "\<lbrakk>\<Gamma> (x_var var) = Some ty_var; L (x_var var) = Some v_var;
    \<forall>x\<in>set y_cl_var_var'_v_list. L (x_var ((\<lambda>(y, cl, var, var', v). var') x)) = None; L x' = None\<rbrakk>
    \<Longrightarrow> (\<Gamma> ++ map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)) ++ empty(x' \<mapsto> ty_x_d)) (x_var var) = Some ty_var"
apply(subgoal_tac "x_var var \<noteq> x'")
 apply(simp add: map_add_def)
 apply(subgoal_tac "map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)) (x_var var) = None")
  apply(simp)
 apply(clarsimp simp add: map_of_eq_None_iff set_zip)
 apply(rename_tac y_k cl_k var_k v_k y'_k ty_k i)
 apply(drule_tac x = "(y_k, cl_k, var_k, var, v_k)" in bspec, simp)
 apply(force)
by force

lemma same_el:
  "\<lbrakk>distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list);
    i < length y_cl_var_var'_v_list;
    (y_i, cl_i, var_i, var'_i, v_i) = y_cl_var_var'_v_list ! i;
    (y_j, cl_j, var_j, var'_i, v_j) \<in> set y_cl_var_var'_v_list\<rbrakk>
       \<Longrightarrow> (y_i, cl_i, var_i, var'_i, v_i) = (y_j, cl_j, var_j, var'_i, v_j)"
apply(simp only: in_set_conv_nth) apply(clarsimp) apply(rename_tac j)
apply(simp only: distinct_conv_nth)
apply(erule_tac x = i in allE) apply(simp)
apply(erule_tac x = j in allE) apply(simp)
apply(drule sym) apply(simp)
done

lemma same_y:
  "\<lbrakk>map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list = map fst y_ty_list;
    i < length y_cl_var_var'_v_list;
    (y'_k, ty_k) = y_ty_list ! i; y_cl_var_var'_v_list ! i = (y_k, cl_k, var_k, var'_k, v_k)\<rbrakk>
        \<Longrightarrow> y'_k = y_k"
apply(drule_tac f = "\<lambda>(y, cl, var, var', v). y" in arg_cong)
apply(frule_tac f1 = "\<lambda>(y, cl, var, var', v). y" in nth_map[THEN sym])
apply(drule_tac f = fst in arg_cong) apply(simp)
apply(frule map_length_y) apply(simp)
done

lemma map_map_zip_y':
  "map fst y_y'_list = map fst y_ty_list \<Longrightarrow>
   map snd y_y'_list = map fst (map (\<lambda>((y, y'), yy, ty). (y', ty)) (zip y_y'_list y_ty_list))"
apply(rule nth_equalityI)
 apply(induct y_y'_list) apply(simp) apply(clarsimp) apply(frule map_length_y') apply(simp)
apply(clarsimp)
apply(case_tac "y_y'_list ! i")
apply(case_tac "y_ty_list ! i")
apply(clarsimp)
apply(subgoal_tac "i < length (map (\<lambda>((y, y'), yy, ty). (y', ty)) (zip y_y'_list y_ty_list))")
 apply(frule_tac f = fst and xs = "map (\<lambda>((y, y'), yy, ty). (y', ty)) (zip y_y'_list y_ty_list)" in nth_map)
 apply(simp)
apply(subgoal_tac "length (map (\<lambda>((y, y'), yy, ty). (y', ty)) list) = length list" for list)
 apply(simp) apply(frule map_length_y') apply(simp)
apply(simp only: map_length_list)
done

lemma map_map_zip_ty:
  "map fst y_y'_list = map fst y_ty_list \<Longrightarrow>
   map snd (map (\<lambda>((y, y'), yy, ty). (y', ty)) (zip y_y'_list y_ty_list)) = map snd y_ty_list"
apply(frule map_length_y')
apply(rule nth_equalityI)
 apply(induct y_ty_list) apply(simp) apply(simp)
apply(clarsimp)
apply(case_tac "y_y'_list ! i")
apply(case_tac "y_ty_list ! i")
apply(simp)
done

lemma map_y_yy:
  "\<lbrakk>i < length y_y'_list; i < length y_ty_list;
    map fst y_y'_list = map fst y_ty_list;
    y_y'_list ! i = (y, y'); y_ty_list ! i = (yy, ty)\<rbrakk> \<Longrightarrow>
       y = yy"
apply(drule_tac f = fst in arg_cong)
apply(frule_tac f1 = fst in nth_map[THEN sym])
by simp


lemma var_k_of_ty_k:
  "\<lbrakk>distinct (map (\<lambda>(cl, var, ty). var) cl_var_ty_list); distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list);
    x' \<notin> (\<lambda>(y, cl, var, var', v). x_var var') ` set y_cl_var_var'_v_list;
    map fst y_cl_var_var'_v_list = map fst y_ty_list;
    map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list;
    map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list;
    (if x = x_this then Some ty_x_m else map_of (map (\<lambda>(cl, var, y). (x_var var, y)) cl_var_ty_list) x) = Some ty_x\<rbrakk>
       \<Longrightarrow> (if (case if x = x_this then Some x' else map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) x of None \<Rightarrow> x | Some x' \<Rightarrow> x') = x'
           then Some ty_x_m
           else (\<Gamma> ++ map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)))
                 (case if x = x_this then Some x' else map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) x of None \<Rightarrow> x | Some x' \<Rightarrow> x')) =
          Some ty_x"
apply(clarsimp) apply(rule) apply(rule) apply(simp) apply(clarsimp)
apply(frule exists_var') apply(simp add: weaken_list_var) apply(simp) apply(clarsimp split del: if_split)
apply(drule map_of_SomeD)+ apply(clarsimp split del: if_split) apply(frule x'_not_in_list, simp+)
apply(frule map_of_ty_k) apply(simp add: weaken_list_y weaken_list_var)+
done

lemma x_var_not_this: "(if x_var var = x_this then Some x' else Q) = Q" by simp

lemma subtype_through_tr:
  "\<lbrakk>distinct (map (\<lambda>(cl, var, ty). var) cl_var_ty_list); distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list);
    x' \<notin> (\<lambda>(y, cl, var, var', v). x_var var') ` set y_cl_var_var'_v_list;
    map fst y_cl_var_var'_v_list = map fst y_ty_list;
    map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list;
    map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list;
    is_sty_one P ty_x ty_var = Some True; (if x = x_this then Some ty_x_m else map_of (map (\<lambda>(cl, var, y). (x_var var, y)) cl_var_ty_list) x) = Some ty_x;
    map_of (map (\<lambda>(cl, var, y). (x_var var, y)) cl_var_ty_list) (x_var var) = Some ty_var\<rbrakk>
       \<Longrightarrow> sty_option P (if (case if x = x_this then Some x' else map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) x of None \<Rightarrow> x | Some x' \<Rightarrow> x') =
                 x'
              then Some ty_x_m
              else (\<Gamma> ++ map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)))
                    (case if x = x_this then Some x' else map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) x of None \<Rightarrow> x | Some x' \<Rightarrow> x'))
           (if x_var (case_option var (case_x (\<lambda>var'. var') var) (map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) (x_var var))) = x' then Some ty_x_m
           else (\<Gamma> ++ map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)))
                 (x_var (case_option var (case_x (\<lambda>var'. var') var)
                          (if x_var var = x_this then Some x' else map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) (x_var var)))))"
apply(rule_tac ty = ty_x and ty' = ty_var in sty_optionI)
  apply(simp add: var_k_of_ty_k)
 apply(simp only: x_var_not_this) apply(rule map_of_ty_k') apply(simp+)
done

lemma subtypes_through_tr:
  "\<lbrakk>distinct (map (\<lambda>(cl, var, ty). var) cl_var_ty_list); distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list);
    x' \<notin> (\<lambda>(y, cl, var, var', v). x_var var') ` set y_cl_var_var'_v_list; map fst y_cl_var_var'_v_list = map fst y_ty_list;
    map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list; map (\<lambda>(y, cl, var, u). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list;
    \<forall>x\<in>set y_y'_list. case_prod (\<lambda>y. op = (case if y = x_this then Some x' else map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list) y of
                                       None \<Rightarrow> y | Some x' \<Rightarrow> x')) x;
    \<forall>x\<in>set y_ty_lista. (\<lambda>(y, ty). sty_option P (if y = x_this then Some ty_x_m else map_of (map (\<lambda>(cl, var, y). (x_var var, y)) cl_var_ty_list) y) (Some ty)) x;
    map fst y_y'_list = map fst y_ty_lista; (y, y') = y_y'_list ! i; (yy, ty) = y_ty_lista ! i; i < length y_y'_list; i < length y_ty_lista\<rbrakk> \<Longrightarrow>
     sty_option P (if y' = x' then Some ty_x_m else (\<Gamma> ++ map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list))) y') (Some ty)"
apply(drule_tac x = "(y, y')" in bspec, simp) apply(drule_tac x = "(yy, ty)" in bspec, simp) apply(clarsimp split del: if_split)
apply(frule_tac y_ty_list = y_ty_lista in map_y_yy, assumption+) apply(erule sty_option.cases) apply(clarsimp split del: if_split)
apply(rule_tac ty = tya in sty_optionI, (simp add: var_k_of_ty_k)+)
done

lemma map_override_get:
  "(\<Gamma> ++ (\<lambda>u. if u = x' then Some ty_x_d else None)) x' = Some ty_x_d"
apply(simp add: map_add_def)
done

lemma s_induct':
  "\<lbrakk>\<And>ss. \<forall>s\<in>set ss. P s \<Longrightarrow> P (s_block ss); \<And>list x. P (s_ass list x); \<And>list1 x list2. P (s_read list1 x list2); \<And>x1 list x2. P (s_write x1 list x2);
    \<And>x1 x2 s1 s2. \<lbrakk>P s1; P s2\<rbrakk> \<Longrightarrow> P (s_if x1 x2 s1 s2); \<And>list1 x list2 list3. P (s_call list1 x list2 list3); \<And>list ctx cl. P (s_new list ctx cl)\<rbrakk>
         \<Longrightarrow> P s"
by (metis s.induct)

lemma wf_tr_stmt_in_G':
  "\<forall>s'. distinct (map (\<lambda>(cl, var, ty). var) cl_var_ty_list)
    \<and> distinct (map (\<lambda>(y, cl, var, var', v). var') y_cl_var_var'_v_list)
    \<and> x' \<notin> (\<lambda>(y, cl, var, var', v). x_var var') ` set y_cl_var_var'_v_list
    \<and> map (\<lambda>(y, cl, var, var', v). y) y_cl_var_var'_v_list = map fst y_ty_list
    \<and> map (\<lambda>(cl, var, ty). ty) cl_var_ty_list = map snd y_ty_list
    \<and> map (\<lambda>(y, cl, var, var', v). var) y_cl_var_var'_v_list = map (\<lambda>(cl, var, ty). var) cl_var_ty_list
    \<and> is_sty_one P ty_x_d ty_x_m = Some True
    \<and> wf_stmt P (map_of (map (\<lambda>(cl, var, ty). (x_var var, ty)) cl_var_ty_list)(x_this \<mapsto> ty_x_m)) s'
    \<and> tr_s (map_of (map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var')) y_cl_var_var'_v_list)(x_this \<mapsto> x')) s' s''
    \<longrightarrow> wf_stmt P ((\<Gamma> ++ map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)))(x' \<mapsto> ty_x_m)) s''"
apply(rule s_induct')

apply(clarsimp)
apply(erule tr_s.cases, simp_all) apply(clarsimp)
apply(erule wf_stmtE, simp_all) apply(clarsimp)
apply(rule wf_blockI) apply(clarsimp) apply(rename_tac s'_s''_list s' s'')
apply(drule_tac x = "(s', s'')" in bspec, simp)+ apply(clarsimp)

apply(clarsimp) apply(rename_tac var x s')
apply(erule tr_s.cases, simp+) apply(erule wf_stmtE, simp_all)
apply(erule sty_option.cases) apply(rule wf_var_assignI) apply(clarsimp split del: if_split)
apply(rule_tac ty_x = ty in subtype_through_tr, simp+)

apply(clarsimp) apply(rename_tac var x f s')
apply(erule tr_s.cases, simp+) apply(erule wf_stmtE, simp_all)
apply(erule sty_option.cases) apply(clarsimp split del: if_split) apply(rename_tac f ty_x var x ty_f ty_var)
apply(rule wf_field_readI) apply(simp add: var_k_of_ty_k) apply(simp)
apply(rule_tac ty' = ty_var in sty_optionI) apply(simp) apply(rule map_of_ty_k', simp+)

apply(clarsimp) apply(rename_tac x f y s')
apply(erule tr_s.cases, simp+) apply(erule wf_stmtE, simp_all)
apply(erule sty_option.cases) apply(clarsimp split del: if_split) apply(rename_tac f ty_x x y ty_y ty_f)
apply(rule wf_field_writeI) apply(simp add: var_k_of_ty_k) apply(simp)
apply(rule sty_optionI, (simp add: var_k_of_ty_k)+)

apply(clarsimp) apply(rename_tac x y s1 s2 s')
apply(erule tr_s.cases, simp+) apply(erule wf_stmtE, simp_all) apply(rule wf_ifI)
  apply(erule disjE)
   apply(rule disjI1) apply(erule sty_option.cases) apply(clarsimp split del: if_split)
   apply(rule sty_optionI, (simp add: var_k_of_ty_k split del: if_split)+)
  apply(rule disjI2) apply(erule sty_option.cases) apply(clarsimp split del: if_split)
  apply(rule sty_optionI, (simp add: var_k_of_ty_k)+)
 apply(clarsimp)
apply(clarsimp)

apply(clarsimp) apply(rename_tac var x meth ys s')
apply(erule tr_s.cases, simp+) apply(erule wf_stmtE, simp_all) apply(clarsimp split del: if_split)
apply(rule_tac y_ty_list = "map (\<lambda>((y, y'), (yy, ty)). (y', ty)) (zip y_y'_list y_ty_lista)" in wf_mcallI[simplified])
    apply(force simp add: map_map_zip_y'[simplified])
   apply(simp add: var_k_of_ty_k)
  apply(force simp add: map_map_zip_ty[simplified])
 apply(clarsimp simp add: set_zip split del: if_split) apply(simp add: subtypes_through_tr)
apply(erule sty_option.cases) apply(clarsimp split del: if_split) apply(rule sty_optionI, (simp add: map_of_ty_k')+)

apply(clarsimp) apply(rename_tac var ctx cl s')
apply(erule tr_s.cases, simp+) apply(erule wf_stmtE, simp_all) apply(clarsimp)
apply(rule wf_newI) apply(simp)
apply(erule sty_option.cases) apply(clarsimp split del: if_split) apply(rule sty_optionI, (simp add: map_of_ty_k')+)
done

lemma wf_object_heap:
  "\<lbrakk>wf_object P H v_opt (Some ty'); is_sty_one Pa ty_y_s ty_f = Some True; H oid_x = Some (ty_x_d, fs_oid)\<rbrakk>
     \<Longrightarrow> wf_object P (H(oid_x \<mapsto> (ty_x_d, fs_oid(f \<mapsto> v)))) v_opt (Some ty')"
apply(erule wf_objectE) apply(clarsimp)
 apply(rule wf_nullI, simp)
apply(erule sty_option.cases) apply(clarsimp split: option.splits)
apply(rule wf_objectI) apply(force intro: sty_optionI)
done

lemma not_dom_is_none:
  "((\<lambda>(y, cl, var, var', v). x_var var') ` set y_cl_var_var'_v_list \<inter> Map.dom L = {})
     \<Longrightarrow> (\<forall>x\<in>set y_cl_var_var'_v_list. (\<lambda>(y, cl, var, var', v). L (x_var var') = None) x)"
by force

lemma type_to_val:
  "\<lbrakk>wf_varstate P \<Gamma> H L; sty_option P (\<Gamma> x) (\<Gamma> y)\<rbrakk> \<Longrightarrow> \<exists>v w. L x = Some v \<and> L y = Some w"
apply(erule sty_option.cases) apply(clarsimp) apply(erule wf_varstateE)
apply(frule_tac x = x in bspec, simp add: domI) apply(drule_tac x = y in bspec, simp add: domI)
apply(elim wf_objectE) by (simp+)

lemma find_path_fields[THEN mp]:
  "find_path_ty_f P ty = Some path \<longrightarrow> (\<exists>fs. fields_in_path_f path = fs)"
by (force)

lemma replicate_eq_length:
  "replicate x c = replicate y c \<Longrightarrow> x = y"
apply(subgoal_tac "length (replicate x c) = length (replicate y c)") apply(thin_tac _)
apply(subgoal_tac "length (replicate x c) = x")
apply(subgoal_tac "length (replicate y c) = y")
by simp_all


lemma string_infinite:
  "infinite (UNIV :: string set)"
apply(simp add: infinite_iff_countable_subset)
apply(rule_tac x = "\<lambda>n. replicate n c" in exI) apply(rule linorder_injI)
apply(clarify) apply(frule replicate_eq_length) apply(simp)
done

lemma x_infinite:
  "infinite (UNIV :: x set)"
apply(simp add: infinite_iff_countable_subset)
apply(rule_tac x = "\<lambda>n. if n = 0 then x_this else x_var (replicate n c)" in exI)
apply(rule linorder_injI) apply(clarsimp)
done

lemma fresh_oid:
  "wf_heap P H \<Longrightarrow> (\<exists>oid. oid \<notin> dom H)"
apply(erule wf_heapE) apply(clarsimp)
apply(cut_tac infinite_UNIV_nat) apply(frule_tac A = "dom H" in ex_new_if_finite)
apply(assumption) apply(simp)
done

lemma fresh_x:
  "finite A \<Longrightarrow> \<exists>x::x. x \<notin> A"
apply(cut_tac x_infinite) apply(frule_tac A = A in ex_new_if_finite)
apply(assumption) apply(simp)
done

lemma fresh_var_not_in_list:
  "finite (A::x set) \<Longrightarrow> \<exists>var::var. x_var var \<notin> A \<and> var \<notin> set list"
apply(cut_tac x_infinite) apply(subgoal_tac "finite (insert x_this A)")
apply(frule_tac F = "insert x_this A" and G = "x_var ` set list" in finite_UnI) apply(simp)
apply(frule_tac A = "insert x_this A \<union> x_var ` set list" in ex_new_if_finite)
apply(assumption) apply(erule exE) apply(clarsimp) apply(case_tac a) apply(force+)
done

lemma fresh_vars[rule_format]:
  "finite (A::x set) \<longrightarrow> (\<exists>list::var list. length list = i \<and> x_var` set list \<inter> A = {} \<and> distinct list)"
apply(induct i) apply(simp)
apply(clarsimp) apply(frule fresh_var_not_in_list) apply(erule exE)
apply(rule_tac x = "var#list" in exI) apply(simp)
done

lemma fresh_x_not_in_vars':
  "finite A \<Longrightarrow> \<exists>x'. x' \<notin> A \<and> x' \<notin> (x_var ` set vars')"
apply(subgoal_tac "finite (x_var ` set vars')") apply(frule_tac G = "x_var ` set vars'" in finite_UnI) apply(assumption)
apply(cut_tac x_infinite) apply(frule_tac A = "A \<union> x_var ` set vars'" in ex_new_if_finite)
apply(simp) apply(simp) apply(simp)
done

lemma lift_opts_ft_length[rule_format]:
  "\<forall>tys. lift_opts (map (case_vd (\<lambda>clk vark. find_type_f P ctx_o clk)) vds) = Some tys \<longrightarrow> length tys = length vds"
by (induct vds, auto split: vd.splits option.splits)

lemma fpr_mem_has_path'[rule_format]:
  "\<forall>suffix. find_path_rec_f P ctx cl prefix = Some (prefix @ suffix) \<longrightarrow>
     (\<forall>(ctx', cld') \<in> set suffix. \<forall>prefix'.
           (\<exists>suffix'. find_path_rec_f P ctx' (cl_fqn (fqn_def (class_name_f cld'))) prefix' = Some suffix'))"
apply(induct_tac P ctx cl prefix rule: find_path_rec_f.induct)
 apply(simp)
apply(clarsimp split: option.splits)
apply(subgoal_tac "\<forall>aa ba aaa bb.
           (a = aaa \<and> b = bb \<and> aa = aaa \<and> ba = bb)
           \<longrightarrow> (\<forall>suffix. find_path_rec_f P aaa (superclass_name_f bb) (path @ [(aaa, bb)]) = Some (path @ (aaa, bb) # suffix) \<longrightarrow>
                       (\<forall>x\<in>set suffix.
                           (\<lambda>(ctx', cld').
                               \<forall>prefix'. \<exists>suffix'. case_option None (case_prod (\<lambda>ctx' cld. find_path_rec_f P ctx' (superclass_name_f cld) (prefix' @ [(ctx', cld)]))) (find_cld_f P ctx' (fqn_def (class_name_f cld'))) =
                                                   Some suffix')
                            x))")
defer
apply(thin_tac _)+
apply(force)
apply(thin_tac "\<And>aa ba x y.
           \<lbrakk>a = aa \<and> b = ba; x = aa \<and> y = ba\<rbrakk>
           \<Longrightarrow> \<forall>suffix.
                 find_path_rec_f P aa (superclass_name_f ba) (path @ [(aa, ba)]) =
                 Some (path @ (aa, ba) # suffix) \<longrightarrow>
                 (\<forall>x\<in>set suffix.
                     case x of
                     (ctx', cld') \<Rightarrow>
                       \<forall>prefix'.
                          \<exists>suffix'.
                             case_option None
                              (\<lambda>(ctx', cld).
                                  find_path_rec_f P ctx' (superclass_name_f cld) (prefix' @ [(ctx', cld)]))
                              (find_cld_f P ctx' (fqn_def (class_name_f cld'))) =
                             Some suffix')")
apply(clarsimp)
apply(frule path_append) apply(clarify)
apply(erule_tac x = "tl suffix" in allE)
apply(clarsimp)
apply(erule disjE)
 apply(clarify)
 apply(clarsimp simp add: class_name_f_def split: cld.splits)
 apply(rename_tac list1 cl list2 list3)
 apply(case_tac fqn) apply(clarsimp) apply(frule find_cld_name_eq)
 apply(clarsimp simp add: class_name_f_def split: cld.splits)
 apply(frule_tac suffix = path'' and prefix' = " prefix' @ [(a, cld_def list1 cl list2 list3)]" in fpr_same_suffix') apply(simp) apply(simp)
apply(drule_tac x = "(aa, ba)" in bspec, simp) apply(clarsimp split: option.splits)
done

lemma fpr_mem_has_path:
  "\<lbrakk>find_path_f P ctx cl = Some suffix; (ctx', cld') \<in> set suffix\<rbrakk> \<Longrightarrow>
       \<exists>suffix'. find_path_rec_f P ctx' (cl_fqn (fqn_def (class_name_f cld'))) [] = Some suffix'"
apply(cut_tac x = "(ctx', cld')" in fpr_mem_has_path'[of _ _ _ "[]"]) apply(simp add: find_path_f_def)+ done

lemma mtype_to_find_md:
  "\<lbrakk>wf_program P; mtype_f P ty_x_s m = Some (mty_def tys ty_r); is_sty_one P ty_x_d ty_x_s = Some True\<rbrakk> \<Longrightarrow>
      \<exists>ctx cl_r vds ss' y. find_meth_def_f P ty_x_d m = Some (ctx, meth_def_def (meth_sig_def cl_r m vds) (meth_body_def ss' y))
                       \<and> length tys = length vds"
apply(clarsimp simp add: is_sty_one_def split: option.splits ty.splits)
 apply(clarsimp simp add: mtype_f_def find_meth_def_f_def)
apply(case_tac ty_x_d) apply(simp) apply(clarsimp) apply(rename_tac path_d ctx_s dcl_s ctx_d dcl_d)
apply(rename_tac cl_s fds_s mds_s)
apply(frule fpr_mem_has_path) apply(simp) apply(clarsimp simp del: find_path_rec_f.simps)
apply(frule_tac path = path_d and m = m and mty = "mty_def tys ty_r" and path' = suffix' in mty_preservation')
apply(simp add: class_name_f_def find_path_f_def)+
apply(clarsimp simp add: mtype_f_def split: option.splits if_split_asm meth_def.splits meth_sig.splits)
apply(rename_tac meth_body a b c d e f g)
apply(case_tac meth_body) apply(simp) apply(clarsimp simp add: lift_opts_ft_length)
apply(clarsimp simp add: find_meth_def_f_def split: option.splits)
apply(frule find_md_m_match[rule_format]) apply(assumption)
done

lemma exist_lifted_values:
  "\<lbrakk>\<forall>x\<in>dom \<Gamma>. wf_object P H (L x) (\<Gamma> x); \<forall>x\<in>set y_ty_list. (\<lambda>(y, ty). sty_option P (\<Gamma> y) (Some ty)) x\<rbrakk>
       \<Longrightarrow> \<exists>vs. lift_opts (map (\<lambda>(y, ty). L y) y_ty_list) = Some vs"
apply(induct y_ty_list) apply(simp) apply(clarsimp)
apply(erule sty_option.cases) apply(clarsimp) apply(drule_tac x = a in bspec, simp add: domI)
apply(erule wf_objectE) apply(simp) apply(simp)
done

lemma [iff]:
  "length (tr_ss_f (map_of (zip (map (case_vd (\<lambda>cl. x_var)) vds) (map x_var vars'))(x_this \<mapsto> x')) ss') = length ss'"
by (induct ss', auto)

lemma collect_suc_eq_lt[simp]:
  "{f i |i::nat. i < Suc n} = {f i |i. i = 0} \<union> {f (Suc i) |i. i < n}"
apply(induct n) apply(simp)
apply(clarsimp)
apply(simp add: less_Suc_eq)
apply(simp add: image_Collect[THEN sym])
apply(simp add: Collect_disj_eq)
apply(blast)
done

lemma [iff]:
  "\<forall>y_ty_list vars vars' vs. length y_ty_list = length vds \<and> length vars = length vds \<and> length vars' = length vds \<and> length vs = length vds \<longrightarrow>
   map (\<lambda>(y, cl, var, var', v). vd_def cl var) (zip (map fst y_ty_list) (zip (map (case_vd (\<lambda>cl var. cl)) vds) (zip (map (case_vd (\<lambda>cl var. var)) vds) (zip vars' vs)))) = vds"
apply(induct vds) apply(simp) apply(clarsimp simp add: set_zip length_Suc_conv split: vd.splits)
done

lemma vars'_eq[rule_format]:
  "\<forall>y_ty_list vds vars vs. length y_ty_list = length vars' \<and> length vds = length vars' \<and> length vars = length vars' \<and> length vs = length vars' \<longrightarrow>
   (\<lambda>(y, cl, var, var', v). x_var var') ` set (zip (map fst y_ty_list) (zip (map (case_vd (\<lambda>cl var. cl)) vds) (zip vars (zip vars' vs)))) = x_var ` set vars'"
apply(induct vars') apply(simp) apply(clarsimp simp add: set_zip length_Suc_conv)
done

lemma [iff]:
  "\<forall>y_ty_list vds vars vs. length y_ty_list = length vars' \<and> length vds = length vars' \<and> length vars = length vars' \<and> length vs = length vars' \<longrightarrow>
   map (\<lambda>(y, cl, var, var', v). var') (zip (map fst y_ty_list) (zip (map (case_vd (\<lambda>cl var. cl)) vds) (zip vars (zip vars' vs)))) = vars'"
apply(induct vars') apply(simp) apply(clarsimp simp add: set_zip length_Suc_conv)
done

lemma [iff]:
  "\<forall>y_ty_list vds vars vs. length y_ty_list = length vars' \<and> length vds = length vars' \<and> length vars = length vars' \<and> length vs = length vars' \<longrightarrow>
   map (\<lambda>(y, cl, var, var', v). (x_var var, x_var var'))
       (zip (map fst y_ty_list) (zip (map (case_vd (\<lambda>cl var. cl)) vds) (zip (map (case_vd (\<lambda>cl var. var)) vds) (zip vars' vs)))) =
     zip (map (case_vd (\<lambda>cl. x_var)) vds) (map x_var vars')"
apply(induct vars') apply(simp) apply(clarsimp simp add: set_zip length_Suc_conv split: vd.splits)
done

lemma [iff]:
  "\<forall>vds vars vars' vs. length vds = length y_ty_list \<and> length vars = length y_ty_list \<and> length vars' = length y_ty_list \<and> length vs = length y_ty_list \<longrightarrow>
   map (\<lambda>(y, cl, var, var', v). y) (zip (map fst y_ty_list) (zip (map (case_vd (\<lambda>cl var. cl)) vds) (zip vars (zip vars' vs)))) = map fst y_ty_list"
apply(induct y_ty_list) apply(simp) apply(clarsimp simp add: set_zip length_Suc_conv)
done

lemma lift_opts_mapping:
  "\<forall>vds vars vars' vs. length vds = length y_ty_list \<and> length vars = length y_ty_list \<and> length vars' = length y_ty_list \<and> length vs = length y_ty_list \<longrightarrow>
   lift_opts (map (\<lambda>(y, ty). L y) y_ty_list) = Some vs \<longrightarrow>
   (\<forall>x\<in>set (zip (map fst y_ty_list) (zip (map (case_vd (\<lambda>cl var. cl)) vds) (zip (map (case_vd (\<lambda>cl var. var)) vds) (zip vars' vs)))). (\<lambda>(y, cl, var, var', v). L y = Some v) x)"
apply(induct y_ty_list) apply(simp) apply(clarsimp simp add: set_zip length_Suc_conv split: vd.splits option.splits)
apply(rename_tac y1 y_ty_list v2 vs cl1 var1 var'1 v1 vds vars var'2 vars' i cl2 var2)
apply(erule_tac x = vds in allE) apply(erule_tac x = vars in allE) apply(erule_tac x = vars' in allE)
apply(simp) apply(case_tac i) apply(simp) apply(rename_tac j) apply(clarsimp)
apply(erule_tac x = "map fst y_ty_list ! j" in allE) apply(clarsimp)
apply(case_tac "zip (map (case_vd (\<lambda>cl var. cl)) vds) (zip (map (case_vd (\<lambda>cl var. var)) vds) (zip vars' vs)) ! j") apply(rename_tac cl1 var1 var'1 v1)
apply(erule_tac x = cl1 in allE) apply(erule_tac x = var1 in allE) apply(erule_tac x = var'1 in allE) apply(erule_tac x = v1 in allE)
apply(clarsimp) apply(erule_tac x = j in allE) apply(simp)
done

lemma length_y_ty_list_vs[rule_format]:
  "\<forall>vs. lift_opts (map (\<lambda>(y, ty). L y) y_ty_list) = Some vs \<longrightarrow> length y_ty_list = length vs"
by (induct y_ty_list, auto split: option.splits)

lemma translation_eq:
  "\<forall>x\<in>set (zip (tr_ss_f (map_of (zip (map (case_vd (\<lambda>cl. x_var)) vds) (map x_var vars'))(x_this \<mapsto> x')) ss') ss').
             (\<lambda>(s'', s'). tr_s (map_of (zip (map (case_vd (\<lambda>cl. x_var)) vds) (map x_var vars'))(x_this \<mapsto> x')) s' s'') x"
apply(induct ss') apply(simp add: tr_rel_f_eq)+ done




theorem progress:
  "\<lbrakk>wf_config \<Gamma> (config_normal P L H S); S \<noteq> []\<rbrakk> \<Longrightarrow> \<exists>config'. r_stmt (config_normal P L H S) config'"
apply(case_tac S)
 apply(simp)
apply(clarsimp) apply(rename_tac s ss)
apply(case_tac s)
apply(erule_tac[1-7] wf_configE) apply(simp_all)
-- "block"
apply(force intro: r_blockI[simplified])
-- "variable assignment"
apply(clarsimp, erule wf_stmtE, simp_all, clarsimp)
apply(frule type_to_val, simp) apply(clarify) apply(frule r_var_assignI) apply(force)
-- "field read"
apply(clarsimp, erule wf_stmtE, simp_all, clarsimp)
apply(erule wf_varstateE)
apply(drule_tac x = x in bspec, simp add: domI)
apply(erule wf_objectE) apply(clarsimp) apply(frule r_field_read_npeI) apply(force)
apply(clarsimp) apply(erule_tac ?a3.0 = "Some ty" in sty_option.cases) apply(clarsimp split: option.splits)
apply(erule wf_heapE) apply(drule_tac x = oid in bspec, simp add: domI) apply(clarsimp)
apply(rename_tac x oid ty_x_s ty_x_d fields_oid fs)
apply(frule no_field_hiding, simp+) apply(drule_tac x = f in bspec, simp) apply(clarsimp)
apply(erule wf_objectE) apply(clarsimp, frule_tac H = H in r_field_readI, simp, force)+
-- "field write"
apply(clarsimp, erule wf_stmtE, simp_all, clarsimp)
apply(erule wf_varstateE) apply(frule_tac x = x in bspec, simp add: domI)
apply(erule wf_objectE) apply(clarsimp) apply(frule r_field_write_npeI) apply(force)
apply(clarsimp) apply(erule sty_option.cases) apply(clarsimp) apply(rename_tac ty_y ty_f)
apply(drule_tac x = y in bspec, simp add: domI) apply(clarsimp)
apply(erule sty_option.cases) apply(clarsimp split: option.splits)
apply(erule wf_objectE) apply(clarsimp)
apply(frule_tac H = H and y = y in r_field_writeI, simp, force)+
-- "conditional branch"
apply(clarsimp, erule wf_stmtE, simp_all, clarsimp) apply(erule disjE)
apply(frule type_to_val, simp, clarify) apply(case_tac "v = w")
apply(frule_tac y = y in r_if_trueI, force+)
apply(frule_tac y = y in r_if_falseI, force+)
apply(frule type_to_val, simp, clarify) apply(case_tac "v = w")
apply(frule_tac y = y and v = w in r_if_trueI, force+)
apply(frule_tac y = y and v = w in r_if_falseI, force+)
-- "object creation"
apply(clarsimp, erule wf_stmtE, simp_all, clarsimp) apply(rename_tac cl ctx ty var)
apply(erule sty_option.cases) apply(clarsimp) apply(rename_tac ty_cl ty_var)
apply(simp add: is_sty_one_def split: option.splits) apply(rename_tac path)
apply(frule find_path_fields) apply(erule exE)
apply(frule fresh_oid) apply(erule exE)
apply(frule_tac H = H and L = L and var = var and s_list = ss and f_list = fs in r_newI[simplified])
apply(clarsimp simp add: fields_f_def split: option.splits) apply(assumption) apply(simp) apply(force)
-- "method call"
apply(clarsimp, erule wf_stmtE, simp_all, clarsimp)
apply(rename_tac ss y_ty_list x ty_x_s m ty_r_s var)
apply(erule wf_varstateE) apply(frule_tac x = x in bspec, simp add: domI) apply(clarsimp)
apply(erule wf_objectE) apply(clarsimp) apply(frule r_mcall_npeI) apply(force)
apply(elim sty_option.cases) apply(clarsimp split: option.splits)
apply(rename_tac ty_r_s ty_var_s ty_x_s ty_x_d fs_x)
apply(frule mtype_to_find_md, simp+) apply(clarsimp)
apply(frule_tac A = "dom L" and i = "length vds" in fresh_vars) apply(clarsimp) apply(rename_tac vars')
apply(frule exist_lifted_values) apply(simp) apply(clarify)
apply(frule_tac vars' = vars' in fresh_x_not_in_vars') apply(erule exE) apply(erule conjE)
apply(subgoal_tac "\<exists>vars. vars = map (\<lambda>vd. case vd of vd_def cl var \<Rightarrow> var) vds")
 apply(erule exE) apply(subgoal_tac "length vars = length vds")
  apply(frule length_y_ty_list_vs)
  apply(subgoal_tac "\<exists>T. T = (map_of (zip (map (\<lambda>vd. case vd of vd_def cl var \<Rightarrow> x_var var) vds) (map x_var vars')))(x_this \<mapsto> x')")
   apply(erule exE)
   apply(frule_tac H = H and P = P and meth = m and ctx = ctx and cl = cl_r and y = y and ty = ty_x_d and y_cl_var_var'_v_list =
                "zip (map fst y_ty_list) (zip (map (\<lambda>vd. case vd of vd_def cl var \<Rightarrow> cl) vds) (zip vars (zip vars' vs)))"
                and s''_s'_list = "zip (tr_ss_f T ss') ss'" and var = var and s_list = ss and x' = x' and T = T
                in r_mcallI[simplified])
   apply(force) apply(simp) apply(simp) apply(simp add: vars'_eq) apply(simp) apply(assumption) apply(simp add: vars'_eq)
   apply(cut_tac L = L and y_ty_list = y_ty_list in lift_opts_mapping) apply(erule_tac x = vds in allE)
   apply(erule_tac x = vars in allE) apply(erule_tac x = vars' in allE) apply(erule_tac x = vs in allE)
   apply(simp) apply(simp) apply(simp) apply(simp add: translation_eq) apply(simp) apply(force)
by force+


theorem wf_preservation:
  "\<And>\<Gamma> config.
       \<lbrakk>wf_config \<Gamma> config; r_stmt config config'\<rbrakk>
       \<Longrightarrow> \<exists>\<Gamma>'. \<Gamma> \<subseteq>\<^sub>m \<Gamma>' \<and> wf_config \<Gamma>' config'"
apply(erule r_stmt.cases)

(* s_read_npe, s_write_npe *)

(* \<Gamma>' = \<Gamma> for all cases except for mcall (case 11) *)
apply(rule_tac[1-10] x = \<Gamma> in exI)
apply(erule_tac[1-11] wf_configE)
apply(simp_all)

(* s_if s_block *)

apply(clarsimp) apply(erule wf_stmtE) apply(simp_all)
apply(force intro: wf_config_normalI)

(* s_ass *)

apply(clarsimp) apply(erule wf_stmtE) apply(simp_all)
apply(rule wf_config_normalI, assumption+)
 apply(erule sty_option.cases)
 apply(rule wf_subvarstateI, assumption+, simp)
 apply(erule wf_varstateE)
 apply(drule_tac x = x in bspec, simp add: domI)
 apply(erule wf_objectE)
  apply(simp add: wf_nullI)
 apply(clarsimp)
 apply(rule wf_objectI)
 apply(erule sty_option.cases, simp)
 apply(rule sty_optionI, simp+)
apply(rule_tac ty' = ty'a in sty_transitiveI, assumption+)

(* s_read *)

apply(force intro: wf_intros)
apply(clarsimp split: option.splits) apply(erule wf_stmtE) apply(simp_all)
apply(rule wf_config_normalI, assumption+)
 apply(clarsimp)
 apply(rename_tac L oid H v s_list ty_oid fs_oid \<Gamma> x ty_x P f ty_f var)
 apply(erule sty_option.cases)
 apply(rule wf_subvarstateI, assumption, simp)
 apply(clarsimp)
 apply(case_tac v)
  apply(clarify)
  apply(rule wf_nullI, simp)
 apply(clarify)
 apply(rename_tac ty_f ty_var P oid_v)
 apply(erule wf_heapE)
 apply(drule_tac x = oid in bspec, simp add: domI)
 apply(clarsimp)
 apply(rename_tac H P fs_oid)
 apply(erule wf_varstateE)
 apply(frule_tac x = x in bspec, simp add: domI)
 apply(clarsimp)
 apply(erule wf_objectE)
  apply(simp)
 apply(erule sty_option.cases)
 apply(clarsimp split: option.splits)
 apply(rename_tac L \<Gamma> H oid_x ty_x_d ty_x_s P)
 apply(frule_tac ty_x_s = ty_x_s in no_field_hiding, simp+)
 apply(drule_tac x = f in bspec, simp)
 apply(clarsimp)
 apply(frule ftype_preservation[simplified], assumption+)
 apply(clarsimp)
 apply(rename_tac ty_f)
 apply(erule wf_objectE)
  apply(simp)
 apply(clarsimp)
 apply(erule sty_option.cases)
 apply(clarsimp split: option.splits)
 apply(rename_tac H oid_v ty_f P ty_v fs_v)
 apply(rule wf_objectI)
 apply(rule sty_optionI, simp+)
 apply(rule sty_transitiveI, assumption+)

(* s_write *)

apply(force intro: wf_intros)
apply(clarsimp, hypsubst_thin) apply(erule wf_stmtE) apply(simp_all)
apply(clarsimp split: option.splits) apply(rule)
 apply(erule wf_varstateE) apply(clarsimp) apply(rename_tac \<Gamma> P H)
 apply(drule_tac x = xa in bspec, simp add: domI)
 apply(erule wf_objectE) apply(simp) apply(clarsimp)
 apply(elim sty_option.cases) apply(simp)
apply(erule sty_option.cases)
apply(clarsimp)
apply(rule wf_config_normalI)
  apply(assumption)
 apply(rename_tac L oid_x v H ss \<Gamma> x ty_x_s f y ty_y_s ty_f P ty_x_d fs_oid)
 apply(erule wf_heapE)
 apply(rule wf_heapI) apply(simp)
 apply(rule ballI) apply(clarsimp simp add: map_add_def) apply(rule)
  apply(clarsimp) apply(drule_tac x = oid_x in bspec, simp add: domI) apply(clarsimp)
  apply(drule_tac x = fa in bspec, simp) apply(clarsimp)
  apply(rule)
   apply(clarsimp) apply(case_tac v) apply(clarsimp simp add: wf_nullI) apply(clarsimp)
   apply(rename_tac H P fields_x_d ty_f_d oid_v)
   apply(erule wf_varstateE) apply(clarsimp)
   apply(frule ftype_preservation, assumption+) apply(clarsimp)
   apply(drule_tac x = y in bspec, simp add: domI) apply(clarsimp)
   apply(erule_tac ?a4.0 = "Some ty_y_s" in wf_objectE) apply(simp) apply(clarsimp)
   apply(erule sty_option.cases) apply(clarsimp split: option.splits)
   apply(rule wf_objectI) apply(force intro: sty_optionI sty_transitiveI)
  apply(clarsimp) apply(case_tac "fs_oid fa") apply(clarsimp) apply(force elim: wf_objectE)
  apply(case_tac a) apply(force intro: wf_nullI)
  apply(clarsimp) apply(rename_tac H P fields_x_d f ty_f_d oid_v)
  apply(erule wf_varstateE) apply(clarsimp)
  apply(drule_tac x = y in bspec, simp add: domI) apply(clarsimp)
  apply(erule wf_objectE) apply(simp) apply(clarsimp)
  apply(rule wf_objectI) apply(erule sty_option.cases) apply(clarsimp split: option.splits)
  apply(safe) apply(clarsimp) apply(force intro: sty_optionI) apply(force intro: sty_optionI)
 apply(drule_tac x = oid in bspec) apply(clarsimp)
 apply(clarsimp) apply(drule_tac x = fa in bspec, simp)
 apply(clarsimp simp add: wf_object_heap)
apply(rename_tac L oid_x v H ss \<Gamma> x ty_x_s f y ty_y_s ty_f P ty_x_d fs_x)
apply(erule wf_varstateE)
apply(rule wf_varstateI) apply(simp)
apply(clarsimp)
apply(rename_tac L \<Gamma> P H x' y')
apply(drule_tac x = x' in bspec, simp add: domI)
apply(clarsimp)
apply(erule wf_objectE)
 apply(clarsimp)
 apply(rule wf_nullI, simp)
apply(clarsimp)
apply(erule sty_option.cases)
apply(clarsimp split: option.splits)
apply(rename_tac H oid_x' ty_x'_s P ty_x'_d fs_x')
apply(rule wf_objectI)
apply(rule sty_optionI)
  apply(clarsimp)
  apply(rule conjI)
   apply(clarsimp)
   apply(simp)
  apply(clarsimp)
 apply(simp)
apply(simp)

(* s_if *)

apply(erule wf_stmtE) apply(simp_all)
apply(force intro: wf_config_normalI)

apply(erule wf_stmtE) apply(simp_all)
apply(force intro: wf_config_normalI)

(* s_new *)

apply(erule contrapos_np)
apply(erule wf_stmtE, simp_all, clarsimp)
apply(erule sty_option.cases, clarsimp)

apply(rule wf_config_normalI)
   apply(assumption)
  apply(rename_tac H L ss ctx cl \<Gamma> var ty' ty_var P)
  apply(erule wf_heapE)
  apply(rule wf_heapI) apply(simp)
  apply(safe) apply(simp add: map_upd_Some_unfold) apply(split if_split_asm)
   apply(clarsimp) apply(frule field_has_type, simp+)
   apply(erule exE) apply(rule_tac x = ty in exI) apply(simp) apply(force intro: wf_nullI)
  apply(drule_tac x = oida in bspec, simp add: domI) apply(clarsimp split: option.splits)
  apply(drule_tac x = f in bspec, simp) apply(safe) apply(rule_tac x = ty'a in exI) apply(simp)
  apply(erule wf_objectE) apply(clarsimp) apply(force intro: wf_nullI)
  apply(erule sty_option.cases) apply(clarsimp split: option.splits)
  apply(rule wf_objectI) apply(clarsimp) apply(rule conjI) apply(force)
  apply(force intro: sty_optionI)
 apply(rename_tac oid_new H L ss ctx cl \<Gamma> var ty_new ty_var P)
 apply(erule wf_varstateE) apply(clarsimp)
 apply(rule wf_varstateI) apply(simp) apply(rule ballI) apply(drule_tac x = x in bspec, simp)
 apply(clarsimp) apply(rule conjI)
  apply(clarsimp) apply(rule wf_objectI) apply(clarsimp) apply(force intro: sty_optionI)
 apply(rule) apply(erule wf_objectE) apply(clarsimp) apply(force intro: wf_nullI)
 apply(erule sty_option.cases) apply(clarsimp split: option.splits)
 apply(rule wf_objectI) apply(clarsimp) apply(rule) apply(rule) apply(force)
apply(rule) apply(force intro: sty_optionI)

(* s_call *)

apply(force intro: wf_all_exI)

(* setting the new type environment *)
apply(case_tac "H oid", simp) apply(clarsimp)
apply(erule wf_stmtE, simp_all, clarsimp)
apply(frule wf_method_from_find[simplified]) apply(simp) apply(safe)
apply(erule_tac Q = "\<forall>\<Gamma>'. \<Gamma> \<subseteq>\<^sub>m \<Gamma>' \<longrightarrow>
             ~ (wf_config \<Gamma>' (config_normal Pa ((L ++ map_of (map (\<lambda>(y_XXX, cl_XXX, var_XXX, var_', y). (x_var var_', y)) y_cl_var_var'_v_list))(x' \<mapsto> v_oid oid)) H
                   (map fst s''_s'_list @
                    s_ass vara
                     (case if y = x_this then Some x'
                           else map_of (map (\<lambda>(y_XXX, cl_XXX, var_XXX, var_', v_XXX). (x_var var_XXX, x_var var_')) y_cl_var_var'_v_list) y of
                      None \<Rightarrow> y | Some x' \<Rightarrow> x') #
                    s_list)))" in contrapos_pp) apply(simp only: not_all)
apply(rule_tac x = "\<Gamma> ++
                    map_of (map (\<lambda>((y, cl, var, var', v), (y', ty)). (x_var var', ty)) (zip y_cl_var_var'_v_list y_ty_list)) ++
                    empty (x' \<mapsto> ty_def ctx dcl)" in exI)
apply(clarsimp split del: if_split) apply(rule)
 apply(clarsimp simp add: map_le_def split del: if_split) apply(rule sym)
 apply(rule_tac L = L and Pa = Pa and H = H in map_of_map_and_x) apply(assumption+) apply(simp add: not_dom_is_none) apply(erule wf_varstateE) apply(clarsimp)
apply(rename_tac ss ty_x_d fs_x y_ty_list \<Gamma> x ty_x_s P meth ty_r var dcl)
apply(erule sty_option.cases) apply(clarsimp split del: if_split) apply(rename_tac ty_r ty_var P)
apply(erule wf_varstateE, clarify) apply(rename_tac L \<Gamma> P H)

apply(frule_tac x = x in bspec, simp add: domI)
apply(frule_tac x = "x_var var" in bspec, simp add: domI)
apply(clarsimp split del: if_split)
apply(erule wf_objectE, simp, clarsimp split del: if_split) apply(rename_tac P H oid)
apply(erule sty_option.cases, clarsimp split del: if_split) apply(rename_tac ty_x_d ty_x_s P)
apply(subgoal_tac "x_var var \<in> dom \<Gamma>")
 apply(clarify) apply(rename_tac v_var)
 apply(drule not_dom_is_none)

 apply(rule wf_config_normalI)
    apply(assumption)
   apply(assumption) 

  (* varstate *)
  apply(rule wf_varstateI) apply(simp only: finite_super_varstate) apply(clarsimp) apply(rule)
   apply(rule wf_objectI) apply(simp) apply(rule sty_optionI, simp+)
  apply(clarsimp, hypsubst_thin) apply(rule) apply(rule) apply(rule wf_objectI) apply(clarsimp) apply(rule sty_optionI, simp+)
  apply(rule) apply(erule disjE)
   apply(clarsimp) apply(drule map_of_SomeD) apply(clarsimp) apply(rename_tac y_k cl_k var_k var'_k v_k y'_k ty_k)
   apply(frule_tac x = "(y_k, cl_k, var_k, var'_k, v_k)" in bspec) apply(force simp add: set_zip) apply(clarsimp)
   apply(subgoal_tac "map_of (map (\<lambda>(y, cl, var, var', v). (x_var var', v)) y_cl_var_var'_v_list) (x_var var'_k) = Some v_k")
   apply(clarsimp) apply(drule map_y) apply(simp) apply(drule_tac x = "(y_k, ty_k)" in bspec, assumption) apply(clarsimp)
   apply(erule sty_option.cases) apply(clarsimp) apply(rename_tac ty_y_k ty_k P) apply(drule_tac x = y_k in bspec, simp add: domI)
   apply(clarsimp) apply(case_tac v_k) apply(clarify, rule wf_nullI, simp) apply(clarsimp) apply(rename_tac oid_y_k)
   apply(erule_tac ?a4.0 = "Some ty_y_k" in wf_objectE) apply(simp) apply(erule sty_option.cases)
   apply(clarsimp split: option.splits) apply(rule wf_objectI) apply(clarsimp) apply(rule sty_optionI, simp+)
   apply(rule_tac ty' = ty' in sty_transitiveI, assumption+)
   apply(rule map_of_is_SomeI) apply(simp add: map_fst_var'[simplified]) apply(rule set_zip_var'_v, simp)
  apply(clarify) apply(rename_tac x_G ty_x_G) apply(frule_tac x = x_G in bspec, simp add: domI)
  apply(case_tac "map_of (map (\<lambda>((y, cl, var, var', v), y', y). (x_var var', y)) (zip y_cl_var_var'_v_list y_ty_list)) x_G")
   apply(frule map_of_map_zip_none, simp+) apply(simp add: map_add_def)
  apply(frule map_of_map_zip_some, simp+) apply(clarsimp)
  apply(drule map_of_SomeD) apply(drule map_of_SomeD) apply(clarsimp simp add: set_zip)
  apply(frule same_el, simp+) apply(drule_tac s = "(aa, ab, ac, ai, b)" in sym)
  apply(clarsimp) apply(rename_tac y_k cl_k var_k v_k y'_k ty_k var'_k i)
  apply(frule_tac y_k = y_k and cl_k = cl_k and var_k = var_k and var'_k = var'_k and v_k = v_k in same_y, simp+) apply(clarsimp)
  apply(drule_tac x = "(y_k, ty_k)" in bspec, simp) apply(clarsimp) apply(rename_tac y_k ty_k)
  apply(erule sty_option.cases) apply(clarsimp) apply(drule_tac x = y_k in bspec, simp add: domI) apply(clarsimp)
  apply(drule_tac x = "(y_k, cl_k, var_k, var'_k, v_k)" in bspec) apply(drule_tac t = "(y_k, cl_k, var_k, var'_k, v_k)" in sym) apply(simp)
  apply(clarsimp) apply(erule_tac ?a4.0 = "Some ty" in wf_objectE) apply(clarsimp) apply(rule wf_nullI, simp)
  apply(erule sty_option.cases) apply(clarsimp split: option.splits) apply(rule wf_objectI) apply(clarsimp)
  apply(rule sty_optionI, simp+) apply(rule_tac ty' = ty'a in sty_transitiveI, assumption+)
 
 (* assignment *)
 apply(clarsimp split del: if_split) apply(rule)
  apply(rule wf_var_assignI) apply(frule wf_method_from_find) apply(simp) apply(erule exE) apply(erule wf_methE)
  apply(case_tac "ya = x_this")
   apply(clarsimp split del: if_split)
   apply(rule_tac ty' = ty_var in sty_optionI) apply(simp) apply(simp) apply(case_tac ctx, clarify)
   apply(frule_tac ty_r_d = ty in mty_preservation, assumption+) apply(clarify)
   apply(erule sty_option.cases) apply(clarsimp) apply(rule_tac ty' = ty' in sty_transitiveI, assumption+)
  (* y != this *)
  apply(erule sty_option.cases) apply(clarsimp split del: if_split)
  apply(frule_tac var_k = ya and ty_k = tya in exists_var') apply(drule map_of_vd) apply(assumption+) apply(erule exE) apply(clarsimp)
  apply(drule_tac y = "x_var var'_k" in map_of_SomeD) apply(clarsimp split del: if_split) apply(rename_tac y_k cl_k var_k var'_k v_k)
  apply(frule x'_not_in_list, assumption+) apply(clarsimp) apply(drule map_of_SomeD)
  apply(clarsimp split del: if_split) apply(rename_tac cl_k' var_k ty_k) apply(case_tac ctx, clarify) apply(frule mty_preservation, assumption+)
  apply(clarsimp split del: if_split) apply(drule map_of_vd) apply(frule map_of_ty_k, assumption+)
  apply(rule_tac ty = ty_k and ty' = ty_var in sty_optionI) apply(simp add: map_add_def) apply(simp) apply(simp)
  apply(rule_tac ty' = ty_r in sty_transitiveI) apply(assumption+)
 (* wf of translated statements *)  
 apply(clarsimp) apply(erule disjE) apply(erule wf_methE) apply(clarsimp)
  apply(frule map_of_vd[rule_format]) apply(case_tac ctx, clarify) apply(frule mty_preservation, simp+) apply(clarsimp)
  apply(rename_tac P dcl cl y meth s'' s')
  apply(drule_tac x = "(s'', s')" in bspec, simp)+ apply(clarsimp)
  apply(cut_tac cl_var_ty_list = cl_var_ty_list and y_cl_var_var'_v_list = y_cl_var_var'_v_list and y_ty_list = y_ty_list and
                P = P and ty_x_d = ty_x_d and ty_x_m = "ty_def ctx_def dcl" and  x' = x' and s'' = s'' and \<Gamma> = \<Gamma> in wf_tr_stmt_in_G')
  apply(clarsimp)
 (* wf of non-translated statements *)
 apply(cut_tac L = L and x' = x' and y_cl_var_var'_v_list = y_cl_var_var'_v_list and \<Gamma> = \<Gamma> and P = P and H = H and
               y_ty_list = y_ty_list and ty = "ty_def ctx dcl" and ss = ss in wf_stmt_in_G')
 apply(clarsimp)

apply(erule wf_objectE) apply(force) apply(force)
done

end
