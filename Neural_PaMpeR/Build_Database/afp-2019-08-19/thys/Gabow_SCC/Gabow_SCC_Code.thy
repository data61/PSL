section \<open>Code Generation for SCC-Computation \label{sec:scc_code}\<close>
theory Gabow_SCC_Code
imports 
  Gabow_SCC 
  Gabow_Skeleton_Code
  CAVA_Base.CAVA_Code_Target
begin

section \<open>Automatic Refinement to Efficient Data Structures\<close>
context fr_graph_impl_loc
begin
  schematic_goal last_seg_code_aux: 
    "(?c,last_seg_impl)\<in>GSi_rel \<rightarrow> \<langle>\<langle>node_rel\<rangle>list_set_rel\<rangle>nres_rel"
    unfolding last_seg_impl_def_opt[abs_def] 
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal,trace))
    done
  concrete_definition (in -) last_seg_code 
    uses fr_graph_impl_loc.last_seg_code_aux
  lemmas [autoref_rules] = last_seg_code.refine[OF locale_this]

  context begin interpretation autoref_syn .

    lemma [autoref_op_pat]: 
      "last_seg_impl \<equiv> OP last_seg_impl"
      by simp_all
  end

  schematic_goal compute_SCC_code_aux:
    "(?c,compute_SCC_impl) \<in> \<langle>\<langle>\<langle>node_rel\<rangle>list_set_rel\<rangle>list_rel\<rangle>nres_rel"
    unfolding compute_SCC_impl_def[abs_def] initial_impl_def GS_initial_impl_def
    unfolding path_is_empty_impl_def is_on_stack_impl_def is_done_impl_def 
      is_done_oimpl_def
    unfolding GS.is_on_stack_impl_def GS.is_done_impl_def
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal,trace))
    done

  concrete_definition (in -) compute_SCC_code 
    uses fr_graph_impl_loc.compute_SCC_code_aux
  lemmas [autoref_rules] = compute_SCC_code.refine[OF locale_this] 

  schematic_goal last_seg_tr_aux: "RETURN ?c \<le> last_seg_code s"
    unfolding last_seg_code_def by refine_transfer
  concrete_definition (in -) last_seg_tr uses fr_graph_impl_loc.last_seg_tr_aux
  lemmas [refine_transfer] = last_seg_tr.refine[OF locale_this]

  schematic_goal compute_SCC_tr_aux: "RETURN ?c \<le> compute_SCC_code g"
    unfolding compute_SCC_code_def by refine_transfer
  concrete_definition (in -) compute_SCC_tr 
    uses fr_graph_impl_loc.compute_SCC_tr_aux
  lemmas [refine_transfer] = compute_SCC_tr.refine[OF locale_this]
end

export_code compute_SCC_tr checking SML

section \<open>Correctness Theorem\<close>

theorem compute_SCC_tr_correct:
  \<comment> \<open>Correctness theorem for the constant we extracted to SML\<close>
  fixes Re
  fixes G :: "('a::hashable,'more) graph_rec_scheme"
  assumes A: "(G_impl,G)\<in>\<langle>Re,Id\<rangle>g_impl_rel_ext"
  assumes C: "fr_graph G"
  shows "RETURN (compute_SCC_tr G_impl) 
  \<le> \<Down>(\<langle>\<langle>Id\<rangle>list_set_rel\<rangle>list_rel) (fr_graph.compute_SCC_spec G)"
proof -
  from C interpret fr_graph G .
  have I: "fr_graph_impl_loc Re G_impl G"
    apply unfold_locales using A .
  then interpret fr_graph_impl_loc Re G_impl G .

  note compute_SCC_tr.refine[OF I]
  also note compute_SCC_code.refine[OF I, THEN nres_relD]
  also note compute_SCC_impl_refine
  also note compute_SCC_correct
  finally show ?thesis using A by simp
qed

section \<open>Extraction of Benchmark Code\<close>

schematic_goal list_set_of_list_aux: 
  "(?c,set)\<in>\<langle>nat_rel\<rangle>list_rel \<rightarrow> \<langle>nat_rel\<rangle>list_set_rel"
  by autoref
concrete_definition list_set_of_list uses list_set_of_list_aux

term compute_SCC_tr

definition compute_SCC_tr_nat :: "_ \<Rightarrow> nat list list"
  where "compute_SCC_tr_nat \<equiv> compute_SCC_tr"

(*export_code 
  compute_SCC_tr_nat
  succ_of_list_impl
  nat_of_integer
  integer_of_nat
  list_set_of_list
  in SML module_name CSCC_Gabow
  file "Gabow_Benchmark/cscc_gabow.sml"
*)

end
