section \<open>Imperative Implementation of of Nested DFS (HPY-Improvement)\<close>
theory Sepref_NDFS
imports 
  "../Sepref"
  Collections_Examples.Nested_DFS
  Sepref_Graph
  "HOL-Library.Code_Target_Numeral"
begin

sepref_decl_intf 'v i_red_witness is "'v list * 'v"

lemma id_red_witness[id_rules]:
  "red_init_witness ::\<^sub>i TYPE('v \<Rightarrow> 'v \<Rightarrow> 'v i_red_witness option)"
  "prep_wit_red ::\<^sub>i TYPE('v \<Rightarrow> 'v i_red_witness option \<Rightarrow> 'v i_red_witness option)"
  by simp_all

definition 
  red_witness_rel_def_internal: "red_witness_rel R \<equiv> \<langle>\<langle>R\<rangle>list_rel,R\<rangle>prod_rel"

lemma red_witness_rel_def: "\<langle>R\<rangle>red_witness_rel \<equiv> \<langle>\<langle>R\<rangle>list_rel,R\<rangle>prod_rel"
  unfolding red_witness_rel_def_internal[abs_def] by (simp add: relAPP_def)

lemma red_witness_rel_sv[constraint_rules]:
  "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>red_witness_rel)"
  unfolding red_witness_rel_def
  by tagged_solver

lemma [sepref_fr_rules]: "hn_refine
  (hn_val R u u' * hn_val R v v')
  (return (red_init_witness u' v'))
  (hn_val R u u' * hn_val R v v')
  (option_assn (pure (\<langle>R\<rangle>red_witness_rel)))
  (RETURN$(red_init_witness$u$v))"
  apply simp
  unfolding red_init_witness_def
  apply rule
  apply (sep_auto simp: hn_ctxt_def pure_def red_witness_rel_def)
  done

lemma [sepref_fr_rules]: "hn_refine
  (hn_val R u u' * hn_ctxt (option_assn (pure (\<langle>R\<rangle>red_witness_rel))) w w')
  (return (prep_wit_red u' w'))
  (hn_val R u u' * hn_ctxt (option_assn (pure (\<langle>R\<rangle>red_witness_rel))) w w')
  (option_assn (pure (\<langle>R\<rangle>red_witness_rel)))
  (RETURN$(prep_wit_red$u$w))"
  apply rule
  apply (cases w)
  apply (sep_auto simp: hn_ctxt_def pure_def red_witness_rel_def)
  apply (cases w')
  apply (sep_auto simp: hn_ctxt_def pure_def red_witness_rel_def)
  apply (sep_auto simp: hn_ctxt_def pure_def red_witness_rel_def)
  done

term red_dfs

sepref_definition red_dfs_impl is 
  "(uncurry2 (uncurry red_dfs))" 
  :: "(adjg_assn nat_assn)\<^sup>k *\<^sub>a (ias.assn nat_assn)\<^sup>k *\<^sub>a (ias.assn nat_assn)\<^sup>d *\<^sub>a nat_assn\<^sup>k \<rightarrow>\<^sub>a UNSPEC"
  unfolding red_dfs_def[abs_def]
  using [[goals_limit = 1]]
  by sepref
export_code red_dfs_impl checking SML_imp 

declare red_dfs_impl.refine[sepref_fr_rules]

sepref_register red_dfs :: "'a i_graph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a 
    \<Rightarrow> ('a set * 'a i_red_witness option) nres"

(*lemma id_red_dfs[id_rules]: 
  "red_dfs ::\<^sub>i TYPE(
    'a i_graph \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a 
    \<Rightarrow> ('a set * 'a i_red_witness option) nres)"
  by simp

lemma skel_red_dfs[sepref_la_skel]: "SKEL (red_dfs$E$os$V$s) = la_op (E,os,V,s)"
  by simp
*)

lemma id_init_wit_blue[id_rules]: 
  "init_wit_blue ::\<^sub>i TYPE('a \<Rightarrow> 'a i_red_witness option \<Rightarrow> 'a blue_witness)" 
  by simp

lemma hn_blue_wit[sepref_import_param]: 
  "(NO_CYC,NO_CYC)\<in>blue_wit_rel" 
  "(prep_wit_blue,prep_wit_blue)\<in>nat_rel\<rightarrow>blue_wit_rel\<rightarrow>blue_wit_rel"
  "((=),(=))\<in>blue_wit_rel\<rightarrow>blue_wit_rel\<rightarrow>bool_rel"
  by simp_all

lemma hn_init_wit_blue[sepref_fr_rules]: "hn_refine
  (hn_val nat_rel v v' * hn_ctxt (option_assn (pure (\<langle>nat_rel\<rangle>red_witness_rel))) w w')
  (return (init_wit_blue v' w'))
  (hn_val nat_rel v v' * hn_ctxt (option_assn (pure (\<langle>nat_rel\<rangle>red_witness_rel))) w w')
  (pure blue_wit_rel)
  (RETURN$(init_wit_blue$v$w))"
  apply rule
  apply (sep_auto simp: hn_ctxt_def pure_def)
  apply (case_tac w, sep_auto)
  apply (case_tac w', sep_auto, sep_auto simp: red_witness_rel_def)
  done

lemma hn_extract_res[sepref_import_param]: 
  "(extract_res, extract_res) \<in> blue_wit_rel \<rightarrow> Id"
  by simp

thm red_dfs_impl.refine


sepref_definition blue_dfs_impl is "uncurry2 blue_dfs" :: "((adjg_assn nat_assn)\<^sup>k*\<^sub>a(ias.assn nat_assn)\<^sup>k*\<^sub>anat_assn\<^sup>k\<rightarrow>\<^sub>aid_assn)"
  unfolding blue_dfs_def[abs_def]
  apply (rewrite in "RECT _ \<hole>" ias.fold_custom_empty)+
  using [[goals_limit = 1]]
  by sepref (* Takes long *)
export_code blue_dfs_impl checking SML_imp 

definition "blue_dfs_spec E A v0 \<equiv> SPEC (\<lambda>r. case r of None \<Rightarrow> \<not> has_acc_cycle E A v0
             | Some (v, pc, pv) \<Rightarrow> is_acc_cycle E A v0 v pv pc)"

lemma blue_dfs_correct': "(uncurry2 blue_dfs, uncurry2 blue_dfs_spec) \<in> [\<lambda>((E,A),v0). finite (E\<^sup>*``{v0})]\<^sub>f ((Id\<times>\<^sub>rId)\<times>\<^sub>rId) \<rightarrow> \<langle>Id\<rangle>nres_rel"
  apply (intro frefI nres_relI) 
  unfolding blue_dfs_spec_def apply clarsimp 
  apply (refine_vcg blue_dfs_correct)
  done

lemmas blue_dfs_impl_correct' = blue_dfs_impl.refine[FCOMP blue_dfs_correct']


theorem blue_dfs_impl_correct:
  fixes E
  assumes "finite (E\<^sup>*``{v0})"
  shows "<ias.assn id_assn A A_impl * adjg_assn id_assn E succ_impl>
      blue_dfs_impl succ_impl A_impl v0 
    <\<lambda>r. ias.assn id_assn A A_impl * adjg_assn id_assn E succ_impl
      * \<up>(
        case r of None \<Rightarrow> \<not>has_acc_cycle E A v0
      | Some (v,pc,pv) \<Rightarrow> is_acc_cycle E A v0 v pv pc
    )>\<^sub>t"
  using blue_dfs_impl_correct'[THEN hfrefD, THEN hn_refineD, of "((E,A),v0)" "((succ_impl,A_impl),v0)", simplified]  
  apply (rule cons_rule[rotated -1])
  using assms
  by (sep_auto simp: blue_dfs_spec_def pure_def)+

text \<open> We tweak the initialization vector of the outer DFS,
  to allow pre-initialization of the size of the array-lists.
  When set to the number of nodes, array-lists will never be resized 
  during the run, which saves some time. \<close>

context 
  fixes N :: nat
begin

lemma testsuite_blue_dfs_modify:
  "({}::nat set, {}::nat set, {}::nat set, s) 
  = (op_ias_empty_sz N, op_ias_empty_sz N, op_ias_empty_sz N, s)"
  by simp

sepref_definition blue_dfs_impl_sz is "uncurry2 blue_dfs" :: "((adjg_assn nat_assn)\<^sup>k*\<^sub>a(ias.assn nat_assn)\<^sup>k*\<^sub>anat_assn\<^sup>k\<rightarrow>\<^sub>aid_assn)"
  unfolding blue_dfs_def[abs_def]
  apply (rewrite in "RECT _ \<hole>" testsuite_blue_dfs_modify)
  using [[goals_limit = 1]]
  by sepref (* Takes long *)
export_code blue_dfs_impl_sz checking SML_imp 

end

lemmas blue_dfs_impl_sz_correct' = blue_dfs_impl_sz.refine[FCOMP blue_dfs_correct']

term blue_dfs_impl_sz

theorem blue_dfs_impl_sz_correct:
  fixes E
  assumes "finite (E\<^sup>*``{v0})"
  shows "<ias.assn id_assn A A_impl * adjg_assn id_assn E succ_impl>
      blue_dfs_impl_sz N succ_impl A_impl v0 
    <\<lambda>r. ias.assn id_assn A A_impl * adjg_assn id_assn E succ_impl
      * \<up>(
        case r of None \<Rightarrow> \<not>has_acc_cycle E A v0
      | Some (v,pc,pv) \<Rightarrow> is_acc_cycle E A v0 v pv pc
    )>\<^sub>t"
  using blue_dfs_impl_sz_correct'[THEN hfrefD, THEN hn_refineD, of "((E,A),v0)" "((succ_impl,A_impl),v0)", simplified]  
  apply (rule cons_rule[rotated -1])
  using assms
  by (sep_auto simp: blue_dfs_spec_def pure_def)+

end
