section \<open>Imperative Implementation of Dijkstra's Shortest Paths Algorithm\<close>
theory Sepref_Dijkstra
imports 
  "../IICF/IICF"
  "../Sepref_ICF_Bindings"
  Dijkstra_Shortest_Path.Dijkstra
  Dijkstra_Shortest_Path.Test
  "HOL-Library.Code_Target_Numeral"
  (*"../../../DFS_Framework/Misc/DFS_Framework_Refine_Aux"*)
  Sepref_WGraph
begin


(* Setup for Infty *)

instantiation infty :: (heap) heap
begin
  instance 
    apply standard
    apply (rule_tac x="\<lambda>Infty \<Rightarrow> 0 | Num a \<Rightarrow> to_nat a + 1" in exI)
    apply (rule injI)
    apply (auto split: infty.splits)
    done
end

fun infty_assn where
  "infty_assn A (Num x) (Num y) = A x y"
| "infty_assn A Infty Infty = emp"
| "infty_assn _ _ _ = false"

text \<open>Connection with \<open>infty_rel\<close>\<close>
lemma infty_assn_pure_conv: "infty_assn (pure A) = pure (\<langle>A\<rangle>infty_rel)"
  apply (intro ext)
  subgoal for x y by (cases x; cases y; simp add: pure_def)
  done

lemmas [sepref_import_rewrite, fcomp_norm_unfold, sepref_frame_normrel_eqs] =
  infty_assn_pure_conv[symmetric]
lemmas [constraint_simps] = infty_assn_pure_conv

lemma infty_assn_pure[safe_constraint_rules]: "is_pure A \<Longrightarrow> is_pure (infty_assn A)"
  by (auto simp: is_pure_conv infty_assn_pure_conv)

lemma infty_assn_id[simp]: "infty_assn id_assn = id_assn"
  by (simp add: infty_assn_pure_conv)

lemma [safe_constraint_rules]: "IS_BELOW_ID R \<Longrightarrow> IS_BELOW_ID (\<langle>R\<rangle>infty_rel)"  
  by (auto simp: infty_rel_def IS_BELOW_ID_def)

sepref_register Num Infty

lemma Num_hnr[sepref_fr_rules]: "(return o Num,RETURN o Num)\<in>A\<^sup>d \<rightarrow>\<^sub>a infty_assn A"
  by sepref_to_hoare sep_auto

lemma Infty_hnr[sepref_fr_rules]: "(uncurry0 (return Infty),uncurry0 (RETURN Infty))\<in>unit_assn\<^sup>k \<rightarrow>\<^sub>a infty_assn A"
  by sepref_to_hoare sep_auto

sepref_register case_infty
lemma [sepref_monadify_arity]: "case_infty \<equiv> \<lambda>\<^sub>2f1 f2 x. SP case_infty$f1$(\<lambda>\<^sub>2x. f2$x)$x"
  by simp
lemma [sepref_monadify_comb]: "case_infty$f1$f2$x \<equiv> (\<bind>)$(EVAL$x)$(\<lambda>\<^sub>2x. SP case_infty$f1$f2$x)" by simp
lemma [sepref_monadify_comb]: "EVAL$(case_infty$f1$(\<lambda>\<^sub>2x. f2 x)$x) 
  \<equiv> (\<bind>)$(EVAL$x)$(\<lambda>\<^sub>2x. SP case_infty$(EVAL $ f1)$(\<lambda>\<^sub>2x. EVAL $ f2 x)$x)"
  apply (rule eq_reflection)
  by (simp split: infty.splits)

lemma infty_assn_ctxt: "infty_assn A x y = z \<Longrightarrow> hn_ctxt (infty_assn A) x y = z"
  by (simp add: hn_ctxt_def)

lemma infty_cases_hnr[sepref_prep_comb_rule, sepref_comb_rules]:
  fixes A e e'
  defines [simp]: "INVe \<equiv> hn_invalid (infty_assn A) e e'"
  assumes FR: "\<Gamma> \<Longrightarrow>\<^sub>t hn_ctxt (infty_assn A) e e' * F"
  assumes Infty: "\<lbrakk>e = Infty; e' = Infty\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt (infty_assn A) e e' * F) f1' (hn_ctxt XX1 e e' * \<Gamma>1') R f1"
  assumes Num: "\<And>x1 x1a. \<lbrakk>e = Num x1; e' = Num x1a\<rbrakk> \<Longrightarrow> hn_refine (hn_ctxt A x1 x1a * INVe * F) (f2' x1a) (hn_ctxt A' x1 x1a * hn_ctxt XX2 e e' * \<Gamma>2') R (f2 x1)"
  assumes MERGE2[unfolded hn_ctxt_def]: "\<Gamma>1' \<or>\<^sub>A \<Gamma>2' \<Longrightarrow>\<^sub>t \<Gamma>'"
  shows "hn_refine \<Gamma> (case_infty f1' f2' e') (hn_ctxt (infty_assn A') e e' * \<Gamma>') R (case_infty$f1$(\<lambda>\<^sub>2x. f2 x)$e)"
  apply (rule hn_refine_cons_pre[OF FR])
  apply1 extract_hnr_invalids
  apply (cases e; cases e'; simp add: infty_assn.simps[THEN infty_assn_ctxt])
  subgoal 
    apply (rule hn_refine_cons[OF _ Infty _ entt_refl]; assumption?)
    applyS (simp add: hn_ctxt_def)
    apply (subst mult.commute, rule entt_fr_drop)
    apply (rule entt_trans[OF _ MERGE2])
    apply (simp add:)
  done  
  subgoal 
    apply (rule hn_refine_cons[OF _ Num _ entt_refl]; assumption?)
    applyS (simp add: hn_ctxt_def)
    apply (rule entt_star_mono)
    apply1 (rule entt_fr_drop)
    applyS (simp add: hn_ctxt_def)
    apply1 (rule entt_trans[OF _ MERGE2])
    applyS (simp add:)
  done    
  done
  
lemma hnr_val[sepref_fr_rules]: "(return o Weight.val,RETURN o Weight.val) \<in> [\<lambda>x. x\<noteq>Infty]\<^sub>a (infty_assn A)\<^sup>d \<rightarrow> A"
  apply sepref_to_hoare
  subgoal for x y by (cases x; cases y; sep_auto)
  done

context
  fixes A :: "'a::weight \<Rightarrow> 'b \<Rightarrow> assn"
  fixes plusi
  assumes GA[unfolded GEN_ALGO_def, sepref_fr_rules]: "GEN_ALGO plusi (\<lambda>f. (uncurry f,uncurry (RETURN oo (+)))\<in>A\<^sup>k*\<^sub>aA\<^sup>k \<rightarrow>\<^sub>a A)"
begin
  sepref_thm infty_plus_impl is "uncurry (RETURN oo (+))" :: "((infty_assn A)\<^sup>k *\<^sub>a (infty_assn A)\<^sup>k \<rightarrow>\<^sub>a infty_assn A)"
    unfolding infty_plus_eq_plus[symmetric] infty_plus_def[abs_def]
    by sepref
end
concrete_definition infty_plus_impl uses infty_plus_impl.refine_raw is "(uncurry ?impl,_)\<in>_"
lemmas [sepref_fr_rules] = infty_plus_impl.refine

definition infty_less where
  "infty_less lt a b \<equiv> case (a,b) of (Num a, Num b) \<Rightarrow> lt a b | (Num _, Infty) \<Rightarrow> True | _ \<Rightarrow> False"

lemma infty_less_param[param]:
  "(infty_less,infty_less) \<in> (R\<rightarrow>R\<rightarrow>bool_rel) \<rightarrow> \<langle>R\<rangle>infty_rel \<rightarrow> \<langle>R\<rangle>infty_rel \<rightarrow> bool_rel"
  unfolding infty_less_def[abs_def]
  by parametricity

lemma infty_less_eq_less: "infty_less (<) = (<)"
  unfolding infty_less_def[abs_def] 
  apply (clarsimp intro!: ext)
  subgoal for a b by (cases a; cases b; auto)
  done

context
  fixes A :: "'a::weight \<Rightarrow> 'b \<Rightarrow> assn"
  fixes lessi
  assumes GA[unfolded GEN_ALGO_def, sepref_fr_rules]: "GEN_ALGO lessi (\<lambda>f. (uncurry f,uncurry (RETURN oo (<)))\<in>A\<^sup>k*\<^sub>aA\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
begin
  sepref_thm infty_less_impl is "uncurry (RETURN oo (<))" :: "((infty_assn A)\<^sup>k *\<^sub>a (infty_assn A)\<^sup>k \<rightarrow>\<^sub>a bool_assn)"
    unfolding infty_less_eq_less[symmetric] infty_less_def[abs_def]
    by sepref
end
concrete_definition infty_less_impl uses infty_less_impl.refine_raw is "(uncurry ?impl,_)\<in>_"
lemmas [sepref_fr_rules] = infty_less_impl.refine

lemma param_mpath': "(mpath',mpath')
  \<in> \<langle>\<langle>A\<times>\<^sub>r B \<times>\<^sub>r A\<rangle>list_rel \<times>\<^sub>r B\<rangle>option_rel \<rightarrow> \<langle>\<langle>A\<times>\<^sub>r B \<times>\<^sub>r A\<rangle>list_rel\<rangle>option_rel"
proof -
  have 1: "mpath' = map_option fst"
    apply (intro ext, rename_tac x)
    apply (case_tac x)
    apply simp
    apply (rename_tac a)
    apply (case_tac a)
    apply simp
    done
  show ?thesis  
    unfolding 1
    by parametricity
qed
lemmas (in -) [sepref_import_param] = param_mpath'

lemma param_mpath_weight': 
  "(mpath_weight', mpath_weight') \<in> \<langle>\<langle>A\<times>\<^sub>rB\<times>\<^sub>rA\<rangle>list_rel \<times>\<^sub>r B\<rangle>option_rel \<rightarrow> \<langle>B\<rangle>infty_rel"
  by (auto elim!: option_relE simp: infty_rel_def top_infty_def)

lemmas [sepref_import_param] = param_mpath_weight'

context Dijkstra begin  
  lemmas impl_aux = mdijkstra_def[unfolded mdinit_def mpop_min_def mupdate_def]

  lemma mdijkstra_correct:  
    "(mdijkstra, SPEC (is_shortest_path_map v0)) \<in> \<langle>br \<alpha>r res_invarm\<rangle>nres_rel"
  proof -
    note mdijkstra_refines
    also note dijkstra'_refines
    also note dijkstra_correct
    finally show ?thesis
      by (rule nres_relI)
  qed

end

locale Dijkstra_Impl = fixes w_dummy :: "'W::{weight,heap}"
begin
  text \<open>Weights\<close>
  sepref_register "0::'W"  
  lemmas [sepref_import_param] = 
    IdI[of "0::'W"]

  abbreviation "weight_assn \<equiv> id_assn :: 'W \<Rightarrow> _"

  lemma w_plus_param: "((+), (+)::'W\<Rightarrow>_) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp
  lemma w_less_param: "((<), (<)::'W\<Rightarrow>_) \<in> Id \<rightarrow> Id \<rightarrow> Id" by simp
  lemmas [sepref_import_param] = w_plus_param w_less_param
  lemma [sepref_gen_algo_rules]: 
    "GEN_ALGO (return oo (+)) (\<lambda>f. (uncurry f, uncurry (RETURN \<circ>\<circ> (+))) \<in> id_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn)"
    "GEN_ALGO (return oo (<)) (\<lambda>f. (uncurry f, uncurry (RETURN \<circ>\<circ> (<))) \<in> id_assn\<^sup>k *\<^sub>a id_assn\<^sup>k \<rightarrow>\<^sub>a id_assn)"
    by (sep_auto simp: GEN_ALGO_def pure_def intro!: hfrefI hn_refineI)+

  lemma conv_prio_pop_min: "prio_pop_min m = do {
      ASSERT (dom m \<noteq> {}); 
      ((k,v),m) \<leftarrow> mop_pm_pop_min id m;
      RETURN (k,v,m)
    }"
    unfolding prio_pop_min_def mop_pm_pop_min_def
    by (auto simp: pw_eq_iff refine_pw_simps ran_def)
end

context fixes N :: nat and w_dummy::"'W::{heap,weight}" begin  

  interpretation Dijkstra_Impl w_dummy .

  definition "drmap_assn2 \<equiv> IICF_Sepl_Binding.iam.assn 
    (pure (node_rel N))  
    (prod_assn
      (list_assn (prod_assn (pure (node_rel N)) (prod_assn weight_assn (pure (node_rel N)))))
      weight_assn)
    "
    

  concrete_definition mdijkstra' uses Dijkstra.impl_aux

  sepref_definition dijkstra_imp is "uncurry mdijkstra'" 
    :: "(is_graph N (Id::('W\<times>'W) set))\<^sup>k *\<^sub>a (pure (node_rel N))\<^sup>k \<rightarrow>\<^sub>a drmap_assn2"
    unfolding mdijkstra'_def
    apply (subst conv_prio_pop_min)
    apply (rewrite in "RETURN (_,\<hole>)" iam.fold_custom_empty)
    apply (rewrite hm_fold_custom_empty_sz[of N])
    apply (rewrite in "_(_ \<mapsto> (\<hole>,0))" HOL_list.fold_custom_empty)
    unfolding drmap_assn2_def
    using [[id_debug, goals_limit = 1]]
    by sepref
  export_code dijkstra_imp checking SML_imp
end


text \<open>The main correctness theorem\<close>

thm Dijkstra.mdijkstra_correct

lemma mdijkstra'_aref: "(uncurry mdijkstra',uncurry (SPEC oo weighted_graph.is_shortest_path_map))
  \<in> [\<lambda>(G,v0). Dijkstra G v0]\<^sub>f Id\<times>\<^sub>rId \<rightarrow> \<langle>br Dijkstra.\<alpha>r Dijkstra.res_invarm\<rangle>nres_rel"
  using Dijkstra.mdijkstra_correct
  by (fastforce intro!: frefI simp: mdijkstra'.refine[symmetric])

definition "drmap_assn N \<equiv> hr_comp (drmap_assn2 N) (br Dijkstra.\<alpha>r Dijkstra.res_invarm)"

context notes [fcomp_norm_unfold] = drmap_assn_def[symmetric] begin

theorem dijkstra_imp_correct: "(uncurry (dijkstra_imp N), uncurry (SPEC \<circ>\<circ> weighted_graph.is_shortest_path_map))
  \<in> [\<lambda>(G, v0). v0 \<in> nodes G \<and> (\<forall>(v, w, v') \<in> edges G. 0 \<le> w)]\<^sub>a (is_graph N Id)\<^sup>k *\<^sub>a (node_assn N)\<^sup>k \<rightarrow> drmap_assn N"
  apply (rule hfref_weaken_pre'[OF _ dijkstra_imp.refine[FCOMP mdijkstra'_aref]])
proof clarsimp
  fix G :: "(nat,'w::{weight,heap}) graph" and v0
  assume v0_is_node: "v0 \<in> nodes G"
    and nonneg_weights: "\<forall>(v, w, v') \<in> edges G. 0 \<le> w"
    and "v0<N" 
    and RDOM: "rdomp (is_graph N Id) G"

  from RDOM interpret valid_graph G unfolding is_graph_def rdomp_def by auto

  from RDOM have [simp]: "finite V" unfolding is_graph_def rdomp_def by auto

  from RDOM have "\<forall>v\<in>V. {(w, v'). (v, w, v') \<in> E} \<in> 
    Range (\<langle>Id \<times>\<^sub>r node_rel N\<rangle>list_set_rel)"
    by (auto simp: succ_def is_graph_def rdomp_def)
  hence "\<forall>v\<in>V. finite {(w, v'). (v, w, v') \<in> E}"
    unfolding list_set_rel_range by simp
  hence "finite (Sigma V (\<lambda>v. {(w, v'). (v, w, v') \<in> E}))"
    by auto
  also have "E \<subseteq> (Sigma V (\<lambda>v. {(w, v'). (v, w, v') \<in> E}))"  
    using E_valid
    by auto
  finally (finite_subset[rotated]) have [simp]: "finite E" .
    
  show "Dijkstra G v0"
    apply (unfold_locales)
    unfolding is_graph_def using v0_is_node nonneg_weights
    by auto
qed    

end
  
corollary dijkstra_imp_rule: "
  <is_graph n Id G Gi * \<up>(v0 \<in> nodes G \<and> (\<forall>(v, w, v') \<in> edges G. 0 \<le> w))> 
    dijkstra_imp n Gi v0 
  <\<lambda>mi. (is_graph n Id) G Gi 
      * (\<exists>\<^sub>Am. drmap_assn n m mi * \<up>(weighted_graph.is_shortest_path_map G v0 m)) >\<^sub>t"
  using dijkstra_imp_correct[to_hnr, of v0 G n v0 Gi]
  unfolding hn_refine_def
  apply (clarsimp)
  apply (erule cons_rule[rotated -1])
  apply (sep_auto simp: hn_ctxt_def pure_def is_graph_def)
  apply (sep_auto simp: hn_ctxt_def)
  done


end

