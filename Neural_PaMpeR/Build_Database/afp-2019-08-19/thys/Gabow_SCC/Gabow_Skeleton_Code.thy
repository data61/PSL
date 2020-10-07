section \<open>Code Generation for the Skeleton Algorithm \label{sec:skel_code}\<close>
theory Gabow_Skeleton_Code
imports 
  Gabow_Skeleton
  CAVA_Automata.Digraph_Impl
  CAVA_Base.CAVA_Code_Target
begin

section \<open>Statistics\<close>
text \<open>
  In this section, we do the ML setup that gathers statistics about the 
  algorithm's execution.
\<close>

code_printing
  code_module Gabow_Skeleton_Statistics \<rightharpoonup> (SML) \<open>
    structure Gabow_Skeleton_Statistics = struct
      val active = Unsynchronized.ref false
      val num_vis = Unsynchronized.ref 0

      val time = Unsynchronized.ref Time.zeroTime

      fun is_active () = !active
      fun newnode () =
      (
        num_vis := !num_vis + 1;
        if !num_vis mod 10000 = 0 then tracing (IntInf.toString (!num_vis) ^ "\n") else ()
      )

      fun start () = (active := true; time := Time.now ())
      fun stop () = (time := Time.- (Time.now (), !time))

      fun to_string () = let
        val t = Time.toMilliseconds (!time)
        val states_per_ms = real (!num_vis) / real t
        val realStr = Real.fmt (StringCvt.FIX (SOME 2))
      in
        "Required time: " ^ IntInf.toString (t) ^ "ms\n"
      ^ "States per ms: " ^ realStr states_per_ms ^ "\n"
      ^ "# states: " ^ IntInf.toString (!num_vis) ^ "\n"
      end
        
      val _ = Statistics.register_stat ("Gabow-Skeleton",is_active,to_string)

    end
\<close>
code_reserved SML Gabow_Skeleton_Statistics

code_printing
  constant stat_newnode \<rightharpoonup> (SML) "Gabow'_Skeleton'_Statistics.newnode"
| constant stat_start \<rightharpoonup> (SML) "Gabow'_Skeleton'_Statistics.start"
| constant stat_stop \<rightharpoonup> (SML) "Gabow'_Skeleton'_Statistics.stop"

section \<open>Automatic Refinement Setup\<close>
consts i_node_state :: interface

definition "node_state_rel \<equiv> {(-1::int,DONE)} \<union> {(int k,STACK k) | k. True }"
lemma node_state_rel_simps[simp]:
  "(i,DONE)\<in>node_state_rel \<longleftrightarrow> i=-1"
  "(i,STACK n)\<in>node_state_rel \<longleftrightarrow> i = int n"
  unfolding node_state_rel_def
  by auto

lemma node_state_rel_sv[simp,intro!,relator_props]:
  "single_valued node_state_rel"
  unfolding node_state_rel_def
  by (auto intro: single_valuedI)

lemmas [autoref_rel_intf] = REL_INTFI[of node_state_rel i_node_state]

primrec is_DONE where
  "is_DONE DONE = True"
| "is_DONE (STACK _) = False"

lemma node_state_rel_refine[autoref_rules]:
  "(-1,DONE)\<in>node_state_rel"
  "(int,STACK)\<in>nat_rel\<rightarrow>node_state_rel"
  "(\<lambda>i. i<0,is_DONE)\<in>node_state_rel\<rightarrow>bool_rel"
  "((\<lambda>f g i. if i\<ge>0 then f (nat i) else g),case_node_state)
    \<in>(nat_rel \<rightarrow> R) \<rightarrow> R \<rightarrow> node_state_rel \<rightarrow> R"
  unfolding node_state_rel_def 
    apply auto [3]
    apply (fastforce dest: fun_relD)
    done

lemma [autoref_op_pat]: 
  "(x=DONE) \<equiv> is_DONE x"
  "(DONE=x) \<equiv> is_DONE x"
  apply (auto intro!: eq_reflection)
  apply ((cases x, simp_all) [])+
  done

(* TODO: Make changing the Autoref-config simpler, by concentrating
    everything here *)
consts i_node :: interface

(* TODO: Move generic part of this locale to Digraph_impl *)
locale fr_graph_impl_loc = fr_graph G
  for mrel and G_impl and G :: "('v::hashable,'more) graph_rec_scheme"
  +
  assumes G_refine: "(G_impl,G)\<in>\<langle>mrel,Id\<rangle>g_impl_rel_ext"
begin
  abbreviation "node_rel \<equiv> Id :: ('v \<times> _) set"
  lemmas [autoref_rel_intf] = REL_INTFI[of node_rel i_node]

  lemmas [autoref_rules] = G_refine

  lemma locale_this: "fr_graph_impl_loc mrel G_impl G"
    by unfold_locales

  abbreviation "oGSi_rel \<equiv> \<langle>node_rel,node_state_rel\<rangle>dflt_ahm_rel"

  abbreviation "GSi_rel \<equiv> 
    \<langle>node_rel\<rangle>as_rel 
    \<times>\<^sub>r \<langle>nat_rel\<rangle>as_rel 
    \<times>\<^sub>r \<langle>node_rel,node_state_rel\<rangle>dflt_ahm_rel
    \<times>\<^sub>r \<langle>nat_rel \<times>\<^sub>r \<langle>node_rel\<rangle>list_set_rel\<rangle>as_rel"

  lemmas [autoref_op_pat] = GS.S_def GS.B_def GS.I_def GS.P_def

end

section \<open>Generating the Code\<close>

context fr_graph_impl_loc
begin
  schematic_goal push_code_aux: "(?c,push_impl)\<in>node_rel \<rightarrow> GSi_rel \<rightarrow> GSi_rel"
    unfolding push_impl_def_opt[abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  concrete_definition (in -) push_code uses fr_graph_impl_loc.push_code_aux
  lemmas [autoref_rules] = push_code.refine[OF locale_this]
  
  schematic_goal pop_code_aux: "(?c,pop_impl)\<in>GSi_rel \<rightarrow> \<langle>GSi_rel\<rangle>nres_rel"
    unfolding pop_impl_def_opt[abs_def]
    unfolding GS.mark_as_done_def
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  concrete_definition (in -) pop_code uses fr_graph_impl_loc.pop_code_aux
  lemmas [autoref_rules] = pop_code.refine[OF locale_this]

  schematic_goal S_idx_of_code_aux: 
    notes [autoref_rules] = IdI[of "undefined::nat"] (* TODO: hack!*)
    shows "(?c,GS.S_idx_of)\<in>GSi_rel \<rightarrow> node_rel \<rightarrow> nat_rel"
    unfolding GS.S_idx_of_def[abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  concrete_definition (in -) S_idx_of_code 
    uses fr_graph_impl_loc.S_idx_of_code_aux
  lemmas [autoref_rules] = S_idx_of_code.refine[OF locale_this] 

  schematic_goal idx_of_code_aux:
    notes [autoref_rules] = IdI[of "undefined::nat"] (* TODO: hack!*)
    shows "(?c,GS.idx_of_impl)\<in> GSi_rel \<rightarrow> node_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
    unfolding 
      GS.idx_of_impl_def[abs_def, unfolded GS.find_seg_impl_def GS.S_idx_of_def,
        THEN opt_GSdef, unfolded GS_sel_simps, abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  concrete_definition (in -) idx_of_code uses fr_graph_impl_loc.idx_of_code_aux
  lemmas [autoref_rules] = idx_of_code.refine[OF locale_this] 

  schematic_goal collapse_code_aux: 
    "(?c,collapse_impl)\<in>node_rel \<rightarrow> GSi_rel \<rightarrow> \<langle>GSi_rel\<rangle>nres_rel"
    unfolding collapse_impl_def_opt[abs_def] 
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  concrete_definition (in -) collapse_code 
    uses fr_graph_impl_loc.collapse_code_aux
  lemmas [autoref_rules] = collapse_code.refine[OF locale_this] 

  term select_edge_impl
  schematic_goal select_edge_code_aux:
    "(?c,select_edge_impl) 
      \<in> GSi_rel \<rightarrow> \<langle>\<langle>node_rel\<rangle>option_rel \<times>\<^sub>r GSi_rel\<rangle>nres_rel"
    unfolding select_edge_impl_def_opt[abs_def] 

    using [[autoref_trace_failed_id]]
    using [[goals_limit=1]]
    apply (autoref (keep_goal,trace))
    done
  concrete_definition (in -) select_edge_code 
    uses fr_graph_impl_loc.select_edge_code_aux
  lemmas [autoref_rules] = select_edge_code.refine[OF locale_this] 

  context begin interpretation autoref_syn .

    term fr_graph.pop_impl
    lemma [autoref_op_pat]: 
      "push_impl \<equiv> OP push_impl"
      "collapse_impl \<equiv> OP collapse_impl"
      "select_edge_impl \<equiv> OP select_edge_impl"
      "pop_impl \<equiv> OP pop_impl"
      by simp_all
  
  end

  schematic_goal skeleton_code_aux:
    "(?c,skeleton_impl) \<in> \<langle>oGSi_rel\<rangle>nres_rel"
    unfolding skeleton_impl_def[abs_def] initial_impl_def GS_initial_impl_def
    unfolding path_is_empty_impl_def is_on_stack_impl_def is_done_impl_def 
      is_done_oimpl_def
    unfolding GS.is_on_stack_impl_def GS.is_done_impl_def
    using [[autoref_trace_failed_id]]

    apply (autoref (keep_goal,trace))
    done
  concrete_definition (in -) skeleton_code 
    uses fr_graph_impl_loc.skeleton_code_aux
  lemmas [autoref_rules] = skeleton_code.refine[OF locale_this] 
  

  schematic_goal pop_tr_aux: "RETURN ?c \<le> pop_code s"
    unfolding pop_code_def by refine_transfer
  concrete_definition (in -) pop_tr uses fr_graph_impl_loc.pop_tr_aux
  lemmas [refine_transfer] = pop_tr.refine[OF locale_this]

  schematic_goal select_edge_tr_aux: "RETURN ?c \<le> select_edge_code s"
    unfolding select_edge_code_def by refine_transfer
  concrete_definition (in -) select_edge_tr 
    uses fr_graph_impl_loc.select_edge_tr_aux
  lemmas [refine_transfer] = select_edge_tr.refine[OF locale_this]

  schematic_goal idx_of_tr_aux: "RETURN ?c \<le> idx_of_code v s"
    unfolding idx_of_code_def by refine_transfer
  concrete_definition (in -) idx_of_tr uses fr_graph_impl_loc.idx_of_tr_aux
  lemmas [refine_transfer] = idx_of_tr.refine[OF locale_this]

  schematic_goal collapse_tr_aux: "RETURN ?c \<le> collapse_code v s"
    unfolding collapse_code_def by refine_transfer
  concrete_definition (in -) collapse_tr uses fr_graph_impl_loc.collapse_tr_aux
  lemmas [refine_transfer] = collapse_tr.refine[OF locale_this]

  schematic_goal skeleton_tr_aux: "RETURN ?c \<le> skeleton_code g"
    unfolding skeleton_code_def by refine_transfer
  concrete_definition (in -) skeleton_tr uses fr_graph_impl_loc.skeleton_tr_aux
  lemmas [refine_transfer] = skeleton_tr.refine[OF locale_this]

end

term skeleton_tr

export_code skeleton_tr checking SML

end
