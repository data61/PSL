section \<open>\isaheader{Generic Map To Set Converter}\<close>
theory Gen_Map2Set
imports 
  "../Intf/Intf_Map"
  "../Intf/Intf_Set"
  "../Intf/Intf_Comp"
  "../../Iterator/Iterator"
begin

lemma map_fst_unit_distinct_eq[simp]:
  fixes l :: "('k\<times>unit) list"
  shows "distinct (map fst l) \<longleftrightarrow> distinct l"
  by (induct l) auto

definition 
  map2set_rel :: "
    (('ki\<times>'k) set \<Rightarrow> (unit\<times>unit) set \<Rightarrow> ('mi\<times>('k\<rightharpoonup>unit))set) \<Rightarrow> 
    ('ki\<times>'k) set \<Rightarrow> 
    ('mi\<times>('k set)) set"
  where 
  map2set_rel_def_internal: 
  "map2set_rel R Rk \<equiv> \<langle>Rk,Id::(unit\<times>_) set\<rangle>R O {(m,dom m)| m. True}"

lemma map2set_rel_def: "\<langle>Rk\<rangle>(map2set_rel R) 
  = \<langle>Rk,Id::(unit\<times>_) set\<rangle>R O {(m,dom m)| m. True}"
  unfolding map2set_rel_def_internal[abs_def] by (simp add: relAPP_def)

lemma map2set_relI:
  assumes "(s,m')\<in>\<langle>Rk,Id\<rangle>R" and "s'=dom m'"
  shows "(s,s')\<in>\<langle>Rk\<rangle>map2set_rel R"
  using assms unfolding map2set_rel_def by blast

lemma map2set_relE:
  assumes "(s,s')\<in>\<langle>Rk\<rangle>map2set_rel R"
  obtains m' where "(s,m')\<in>\<langle>Rk,Id\<rangle>R" and "s'=dom m'"
  using assms unfolding map2set_rel_def by blast

lemma map2set_rel_sv[relator_props]:
  "single_valued (\<langle>Rk,Id\<rangle>Rm) \<Longrightarrow> single_valued (\<langle>Rk\<rangle>map2set_rel Rm)"
  unfolding map2set_rel_def
  by (auto intro: single_valuedI dest: single_valuedD)

lemma map2set_empty[autoref_rules_raw]:
  assumes "PRIO_TAG_GEN_ALGO"
  assumes "GEN_OP e op_map_empty (\<langle>Rk,Id\<rangle>R)"
  shows "(e,{})\<in>\<langle>Rk\<rangle>map2set_rel R"
  using assms
  unfolding map2set_rel_def
  by auto

lemmas [autoref_rel_intf] = 
  REL_INTFI[of "map2set_rel R" i_set] for R


definition "map2set_insert i k s \<equiv> i k () s"
lemma map2set_insert[autoref_rules_raw]:
  assumes "PRIO_TAG_GEN_ALGO"
  assumes "GEN_OP i op_map_update (Rk \<rightarrow> Id \<rightarrow> \<langle>Rk,Id\<rangle>R \<rightarrow> \<langle>Rk,Id\<rangle>R)"
  shows 
    "(map2set_insert i,Set.insert)\<in>Rk\<rightarrow>\<langle>Rk\<rangle>map2set_rel R \<rightarrow> \<langle>Rk\<rangle>map2set_rel R"
  using assms
  unfolding map2set_rel_def map2set_insert_def[abs_def]
  by (force dest: fun_relD)

definition "map2set_memb l k s \<equiv> case l k s of None \<Rightarrow> False | Some _ \<Rightarrow> True"
lemma map2set_memb[autoref_rules_raw]:
  assumes "PRIO_TAG_GEN_ALGO"
  assumes "GEN_OP l op_map_lookup (Rk \<rightarrow> \<langle>Rk,Id\<rangle>R \<rightarrow> \<langle>Id\<rangle>option_rel)"
  shows "(map2set_memb l ,(\<in>))
    \<in> Rk\<rightarrow>\<langle>Rk\<rangle>map2set_rel R\<rightarrow>Id"
  using assms
  unfolding map2set_rel_def map2set_memb_def[abs_def]
  by (force dest: fun_relD split: option.splits)
  
lemma map2set_delete[autoref_rules_raw]:
  assumes "PRIO_TAG_GEN_ALGO"
  assumes "GEN_OP d op_map_delete (Rk\<rightarrow>\<langle>Rk,Id\<rangle>R\<rightarrow>\<langle>Rk,Id\<rangle>R)"
  shows "(d,op_set_delete)\<in>Rk\<rightarrow>\<langle>Rk\<rangle>map2set_rel R\<rightarrow>\<langle>Rk\<rangle>map2set_rel R"
  using assms
  unfolding map2set_rel_def
  by (force dest: fun_relD)

lemma map2set_to_sorted_list[autoref_ga_rules]:
  fixes it :: "'m \<Rightarrow> ('k\<times>unit) list"
  assumes A: "GEN_ALGO_tag (is_map_to_sorted_list ordR Rk Id R it)"
  shows "is_set_to_sorted_list ordR Rk (map2set_rel R) 
    (it_to_list (map_iterator_dom o (foldli o it)))"
proof -
  { 
    fix l::"('k\<times>unit) list"
    have "\<And>l0. foldli l (\<lambda>_. True) (\<lambda>x \<sigma>. \<sigma> @ [fst x]) l0 = l0@map fst l"
      by (induct l) auto
  }
  hence S: "it_to_list (map_iterator_dom o (foldli o it)) = map fst o it"
    unfolding it_to_list_def[abs_def] map_iterator_dom_def[abs_def]
      set_iterator_image_def set_iterator_image_filter_def
    by (auto)
  show ?thesis
    unfolding S
    using assms
    unfolding is_map_to_sorted_list_def is_set_to_sorted_list_def
    apply clarsimp
    apply (erule map2set_relE)
    apply (drule spec, drule spec)
    apply (drule (1) mp)
    apply (elim exE conjE)
    apply (rule_tac x="map fst l'" in exI)
    apply (rule conjI)
    apply parametricity

    unfolding it_to_sorted_list_def
    apply (simp add: map_to_set_dom)
    apply (simp add: sorted_wrt_map key_rel_def[abs_def])
    done
qed

lemma map2set_to_list[autoref_ga_rules]:
  fixes it :: "'m \<Rightarrow> ('k\<times>unit) list"
  assumes A: "GEN_ALGO_tag (is_map_to_list Rk Id R it)"
  shows "is_set_to_list Rk (map2set_rel R) 
    (it_to_list (map_iterator_dom o (foldli o it)))"
  using assms unfolding is_set_to_list_def is_map_to_list_def
  by (rule map2set_to_sorted_list)


(*lemma map2set_it_simp[iterator_simps]:
  "foldli ((map fst o it) x) c f s = foldli (it x) c (\<lambda>(k,v) s. f k s) s" 
  by (simp add: foldli_map comp_def fn_fst_conv)
*)

text \<open>Transfering also non-basic operations results in specializations
  of map-algorithms to also be used for sets\<close>
lemma map2set_union[autoref_rules_raw]:
  assumes "MINOR_PRIO_TAG (- 9)"
  assumes "GEN_OP u (++) (\<langle>Rk,Id\<rangle>R\<rightarrow>\<langle>Rk,Id\<rangle>R\<rightarrow>\<langle>Rk,Id\<rangle>R)"
  shows "(u,(\<union>))\<in>\<langle>Rk\<rangle>map2set_rel R\<rightarrow>\<langle>Rk\<rangle>map2set_rel R\<rightarrow>\<langle>Rk\<rangle>map2set_rel R"
  using assms
  unfolding map2set_rel_def
  by (force dest: fun_relD)

lemmas [autoref_ga_rules] = cmp_unit_eq_linorder 
lemmas [autoref_rules_raw] = param_cmp_unit

lemma cmp_lex_zip_unit[simp]:
  "cmp_lex (cmp_prod cmp cmp_unit) (map (\<lambda>k. (k, ())) l)
           (map (\<lambda>k. (k, ())) m) =
          cmp_lex cmp l m"
  apply (induct cmp l m rule: cmp_lex.induct)
  apply (auto split: comp_res.split)
  done

lemma cmp_img_zip_unit[simp]:
  "cmp_img (\<lambda>m. map (\<lambda>k. (k,())) (f m)) (cmp_lex (cmp_prod cmp1 cmp_unit))
    = cmp_img f (cmp_lex cmp1)"
  unfolding cmp_img_def[abs_def]
  apply (intro ext)
  apply simp
  done

(* TODO: Move *)

lemma map2set_finite[relator_props]:
  assumes "finite_map_rel (\<langle>Rk,Id\<rangle>R)"
  shows "finite_set_rel (\<langle>Rk\<rangle>map2set_rel R)"
  using assms
  unfolding map2set_rel_def finite_set_rel_def finite_map_rel_def
  by auto

lemma map2set_cmp[autoref_rules_raw]:
  assumes ELO: "SIDE_GEN_ALGO (eq_linorder cmpk)"
  assumes MPAR:
    "GEN_OP cmp (cmp_map cmpk cmp_unit) (\<langle>Rk,Id\<rangle>R \<rightarrow> \<langle>Rk,Id\<rangle>R \<rightarrow> Id)"
  assumes FIN: "PREFER finite_map_rel (\<langle>Rk, Id\<rangle>R)"
  shows "(cmp,cmp_set cmpk)\<in>\<langle>Rk\<rangle>map2set_rel R \<rightarrow> \<langle>Rk\<rangle>map2set_rel R \<rightarrow> Id"
proof -
  interpret linorder "comp2le cmpk" "comp2lt cmpk"
    using ELO by (simp add: eq_linorder_class_conv)

  show ?thesis
    using MPAR
    unfolding cmp_map_def cmp_set_def
    apply simp
    apply parametricity
    apply (drule cmp_extend_paramD)
    apply (insert FIN, fastforce simp add: finite_map_rel_def) []
    apply (simp add: sorted_list_of_map_def[abs_def])
    apply (auto simp: map2set_rel_def cmp_img_def[abs_def] dest: fun_relD) []

    apply (insert map2set_finite[OF FIN[unfolded autoref_tag_defs]],
      fastforce simp add: finite_set_rel_def)
    done
qed

end
