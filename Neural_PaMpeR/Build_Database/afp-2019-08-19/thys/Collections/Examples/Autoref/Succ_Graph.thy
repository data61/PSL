section \<open>Graphs defined by Successor Functions\<close>
theory Succ_Graph
imports 
  Collections.Refine_Dflt
begin

text \<open>
  This code is used in various examples
\<close>

type_synonym 'a slg = "'a \<Rightarrow> 'a list"
definition slg_rel_def_internal: "slg_rel R \<equiv> 
  {(succs,G). \<forall>v. (succs v, G``{v}) \<in> \<langle>R\<rangle>list_set_rel}"

lemma slg_rel_def: "\<langle>R\<rangle>slg_rel \<equiv> 
  {(succs,G). \<forall>v. (succs v, G``{v}) \<in> \<langle>R\<rangle>list_set_rel}" 
  by (auto simp: slg_rel_def_internal relAPP_def)

lemma [relator_props]: "single_valued R \<Longrightarrow> single_valued (\<langle>R\<rangle>slg_rel)"
  unfolding slg_rel_def
  apply (rule single_valuedI)
  apply (auto dest: single_valuedD[OF list_set_rel_sv])
  done

consts i_slg :: "interface \<Rightarrow> interface"

lemmas [autoref_rel_intf] =
  REL_INTFI[of slg_rel i_slg]

definition [simp]: "slg_succs E v \<equiv> E``{v}"

lemma [autoref_itype]: "slg_succs ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set" by simp

context begin interpretation autoref_syn .
lemma [autoref_op_pat]: "E``{v} \<equiv> slg_succs$E$v" by simp
end

definition [code_unfold, simp]: "slg_succs_impl succs v \<equiv> succs v"

lemma refine_slg_succs[autoref_rules_raw]: 
  "(slg_succs_impl,slg_succs)\<in>\<langle>Id\<rangle>slg_rel\<rightarrow>Id\<rightarrow>\<langle>Id\<rangle>list_set_rel"
  apply (intro fun_relI)
  apply (simp add: slg_succs_def slg_rel_def)
  done


subsection "Graph Representations"
(* TODO: Correctness proofs *)

definition succ_of_list :: "(nat\<times>nat) list \<Rightarrow> nat \<Rightarrow> nat set"
  where
  "succ_of_list l \<equiv> let
    m = fold (\<lambda>(u,v) g. 
          case g u of 
            None \<Rightarrow> g(u\<mapsto>{v})
          | Some s \<Rightarrow> g(u\<mapsto>insert v s)
        ) l Map.empty
  in
    (\<lambda>u. case m u of None \<Rightarrow> {} | Some s \<Rightarrow> s)
    
"
    
schematic_goal succ_of_list_impl:
  notes [autoref_tyrel] = 
    ty_REL[where 'a="nat\<rightharpoonup>nat set" and R="\<langle>nat_rel,R\<rangle>iam_map_rel" for R]
    ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>list_set_rel"]

  shows "(?f::?'c,succ_of_list) \<in> ?R"
  unfolding succ_of_list_def[abs_def]
  apply (autoref (keep_goal))
  done

concrete_definition succ_of_list_impl uses succ_of_list_impl
export_code succ_of_list_impl checking SML

definition acc_of_list :: "nat list \<Rightarrow> nat set" 
  where "acc_of_list l \<equiv> fold insert l {}"

schematic_goal acc_of_list_impl:
  notes [autoref_tyrel] = 
    ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>iam_set_rel" for R]

  shows "(?f::?'c,acc_of_list) \<in> ?R"
  unfolding acc_of_list_def[abs_def]
  apply (autoref (keep_goal))
  done

concrete_definition acc_of_list_impl uses acc_of_list_impl
export_code acc_of_list_impl checking SML

end
