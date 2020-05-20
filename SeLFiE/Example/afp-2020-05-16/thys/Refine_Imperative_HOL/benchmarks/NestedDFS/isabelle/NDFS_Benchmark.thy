theory NDFS_Benchmark
imports 
  Collections_Examples.Nested_DFS
  "../../../Examples/Sepref_NDFS"
  Separation_Logic_Imperative_HOL.From_List_GA
begin
  (* We re-do some of the refinement here, to have a more direct control 
    of the exact data-structures that are used *)

  (* Purely functional version *)  

locale bm_fun begin

  schematic_goal succ_of_list_impl:
    notes [autoref_tyrel] = 
      ty_REL[where 'a="nat\<rightharpoonup>nat set" and R="\<langle>nat_rel,R\<rangle>dflt_rm_rel" for R]
      ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>list_set_rel"]
  
    shows "(?f::?'c,succ_of_list) \<in> ?R"
    unfolding succ_of_list_def[abs_def]
    apply (autoref (keep_goal))
    done
  
  concrete_definition succ_of_list_impl uses succ_of_list_impl
  
  schematic_goal acc_of_list_impl:
    notes [autoref_tyrel] = 
      ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>dflt_rs_rel" for R]
  
    shows "(?f::?'c,acc_of_list) \<in> ?R"
    unfolding acc_of_list_def[abs_def]
    apply (autoref (keep_goal))
    done
  
  concrete_definition acc_of_list_impl uses acc_of_list_impl

  schematic_goal red_dfs_impl_refine_aux:
    (*notes [[goals_limit = 1]]*)
    fixes u'::"nat" and V'::"nat set"
    notes [autoref_tyrel] = 
      ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>dflt_rs_rel"]
    assumes [autoref_rules]:
      "(u,u')\<in>nat_rel" 
      "(V,V')\<in>\<langle>nat_rel\<rangle>dflt_rs_rel" 
      "(onstack,onstack')\<in>\<langle>nat_rel\<rangle>dflt_rs_rel" 
      "(E,E')\<in>\<langle>nat_rel\<rangle>slg_rel"
    shows "(RETURN (?f::?'c), red_dfs E' onstack' V' u') \<in> ?R"
    apply -
    unfolding red_dfs_def
    apply (autoref_monadic)
    done
  
  concrete_definition red_dfs_impl uses red_dfs_impl_refine_aux
  prepare_code_thms red_dfs_impl_def
  declare red_dfs_impl.refine[autoref_higher_order_rule, autoref_rules]
  
  schematic_goal ndfs_impl_refine_aux:
    fixes s::"nat" and succi
    notes [autoref_tyrel] = 
      ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>dflt_rs_rel"]
    assumes [autoref_rules]: 
      "(succi,E)\<in>\<langle>nat_rel\<rangle>slg_rel"
      "(Ai,A)\<in>\<langle>nat_rel\<rangle>dflt_rs_rel"
    notes [autoref_rules] = IdI[of s]
    shows "(RETURN (?f::?'c), blue_dfs E A s) \<in> \<langle>?R\<rangle>nres_rel"
    unfolding blue_dfs_def
    apply (autoref_monadic (trace))
    done
  
  concrete_definition fun_ndfs_impl for succi Ai s uses ndfs_impl_refine_aux 
  prepare_code_thms fun_ndfs_impl_def

  definition "fun_succ_of_list \<equiv> 
    succ_of_list_impl o map (\<lambda>(u,v). (nat_of_integer u, nat_of_integer v))"
  
  definition "fun_acc_of_list \<equiv> 
    acc_of_list_impl o map nat_of_integer"

end

interpretation "fun": bm_fun .

  (* Purely functional version *)  

locale bm_funs begin

  schematic_goal succ_of_list_impl:
    notes [autoref_tyrel] = 
      ty_REL[where 'a="nat\<rightharpoonup>nat set" and R="\<langle>nat_rel,R\<rangle>iam_map_rel" for R]
      ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>list_set_rel"]
  
    shows "(?f::?'c,succ_of_list) \<in> ?R"
    unfolding succ_of_list_def[abs_def]
    apply (autoref (keep_goal))
    done
  
  concrete_definition succ_of_list_impl uses succ_of_list_impl
  
  schematic_goal acc_of_list_impl:
    notes [autoref_tyrel] = 
      ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>iam_set_rel" for R]
  
    shows "(?f::?'c,acc_of_list) \<in> ?R"
    unfolding acc_of_list_def[abs_def]
    apply (autoref (keep_goal))
    done
  
  concrete_definition acc_of_list_impl uses acc_of_list_impl

  schematic_goal red_dfs_impl_refine_aux:
    (*notes [[goals_limit = 1]]*)
    fixes u'::"nat" and V'::"nat set"
    notes [autoref_tyrel] = 
      ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>iam_set_rel"]
    assumes [autoref_rules]:
      "(u,u')\<in>nat_rel" 
      "(V,V')\<in>\<langle>nat_rel\<rangle>iam_set_rel" 
      "(onstack,onstack')\<in>\<langle>nat_rel\<rangle>iam_set_rel" 
      "(E,E')\<in>\<langle>nat_rel\<rangle>slg_rel"
    shows "(RETURN (?f::?'c), red_dfs E' onstack' V' u') \<in> ?R"
    apply -
    unfolding red_dfs_def
    apply (autoref_monadic)
    done
  
  concrete_definition red_dfs_impl uses red_dfs_impl_refine_aux
  prepare_code_thms red_dfs_impl_def
  declare red_dfs_impl.refine[autoref_higher_order_rule, autoref_rules]
  
  schematic_goal ndfs_impl_refine_aux:
    fixes s::"nat" and succi
    notes [autoref_tyrel] = 
      ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>iam_set_rel"]
    assumes [autoref_rules]: 
      "(succi,E)\<in>\<langle>nat_rel\<rangle>slg_rel"
      "(Ai,A)\<in>\<langle>nat_rel\<rangle>iam_set_rel"
    notes [autoref_rules] = IdI[of s]
    shows "(RETURN (?f::?'c), blue_dfs E A s) \<in> \<langle>?R\<rangle>nres_rel"
    unfolding blue_dfs_def
    apply (autoref_monadic (trace))
    done
  
  concrete_definition funs_ndfs_impl for succi Ai s uses ndfs_impl_refine_aux 
  prepare_code_thms funs_ndfs_impl_def

  definition "funs_succ_of_list \<equiv> 
    succ_of_list_impl o map (\<lambda>(u,v). (nat_of_integer u, nat_of_integer v))"
  
  definition "funs_acc_of_list \<equiv> 
    acc_of_list_impl o map nat_of_integer"

end

interpretation "funs": bm_funs .

definition "imp_ndfs_impl \<equiv> blue_dfs_impl"
definition "imp_ndfs_sz_impl \<equiv> blue_dfs_impl_sz"
definition "imp_acc_of_list l \<equiv> From_List_GA.ias_from_list (map nat_of_integer l)"
definition "imp_graph_of_list n l \<equiv> cr_graph (nat_of_integer n) (map (pairself nat_of_integer) l)"

export_code 
  nat_of_integer integer_of_nat
  fun.fun_ndfs_impl fun.fun_succ_of_list fun.fun_acc_of_list
  funs.funs_ndfs_impl funs.funs_succ_of_list funs.funs_acc_of_list
  imp_ndfs_impl imp_ndfs_sz_impl imp_acc_of_list imp_graph_of_list
in SML_imp module_name NDFS_Benchmark file \<open>NDFS_Benchmark_export.sml\<close>

ML_val \<open>open Time\<close>
end

