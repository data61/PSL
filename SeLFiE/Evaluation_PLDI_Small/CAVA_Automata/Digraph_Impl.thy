section \<open>Implementing Graphs\<close>
(* Author: Peter Lammich *)
theory Digraph_Impl
imports Digraph
begin

subsection \<open>Directed Graphs by Successor Function\<close>
type_synonym 'a slg = "'a \<Rightarrow> 'a list"


definition slg_rel :: "('a\<times>'b) set \<Rightarrow> ('a slg \<times> 'b digraph) set" where 
  slg_rel_def_internal: "slg_rel R \<equiv> 
  (R \<rightarrow> \<langle>R\<rangle>list_set_rel) O br (\<lambda>succs. {(u,v). v\<in>succs u}) (\<lambda>_. True)"

lemma slg_rel_def: "\<langle>R\<rangle>slg_rel = 
  (R \<rightarrow> \<langle>R\<rangle>list_set_rel) O br (\<lambda>succs. {(u,v). v\<in>succs u}) (\<lambda>_. True)"
  unfolding slg_rel_def_internal relAPP_def by simp

lemma slg_rel_sv[relator_props]: 
  "\<lbrakk>single_valued R; Range R = UNIV\<rbrakk> \<Longrightarrow> single_valued (\<langle>R\<rangle>slg_rel)"
  unfolding slg_rel_def
  by (tagged_solver)

consts i_slg :: "interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of slg_rel i_slg]

definition [simp]: "op_slg_succs E v \<equiv> E``{v}"

lemma [autoref_itype]: "op_slg_succs ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set" by simp

context begin interpretation autoref_syn .
lemma [autoref_op_pat]: "E``{v} \<equiv> op_slg_succs$E$v" by simp
end

lemma refine_slg_succs[autoref_rules_raw]: 
  "(\<lambda>succs v. succs v,op_slg_succs)\<in>\<langle>R\<rangle>slg_rel\<rightarrow>R\<rightarrow>\<langle>R\<rangle>list_set_rel"
  apply (intro fun_relI)
  apply (auto simp add: slg_rel_def br_def dest: fun_relD)
  done

definition "E_of_succ succ \<equiv> { (u,v). v\<in>succ u }"
definition "succ_of_E E \<equiv> (\<lambda>u. {v . (u,v)\<in>E})"

lemma E_of_succ_of_E[simp]: "E_of_succ (succ_of_E E) = E"
  unfolding E_of_succ_def succ_of_E_def
  by auto

lemma succ_of_E_of_succ[simp]: "succ_of_E (E_of_succ E) = E"
  unfolding E_of_succ_def succ_of_E_def
  by auto


context begin interpretation autoref_syn .
  lemma [autoref_itype]: "E_of_succ ::\<^sub>i (I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set) \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg" by simp
  lemma [autoref_itype]: "succ_of_E ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg \<rightarrow>\<^sub>i I \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set" by simp
end

lemma E_of_succ_refine[autoref_rules]:
  "(\<lambda>x. x, E_of_succ) \<in> (R \<rightarrow> \<langle>R\<rangle>list_set_rel) \<rightarrow> \<langle>R\<rangle>slg_rel"
  "(\<lambda>x. x, succ_of_E) \<in> \<langle>R\<rangle>slg_rel \<rightarrow> (R \<rightarrow> \<langle>R\<rangle>list_set_rel)"
  unfolding E_of_succ_def[abs_def] succ_of_E_def[abs_def] slg_rel_def br_def
  apply auto []
  apply clarsimp
  apply (blast dest: fun_relD)
  done


subsubsection \<open>Restricting Edges\<close>
definition op_graph_restrict :: "'v set \<Rightarrow> 'v set \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> ('v \<times> 'v) set"
  where [simp]: "op_graph_restrict Vl Vr E \<equiv> E \<inter> Vl \<times> Vr"

definition op_graph_restrict_left :: "'v set \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> ('v \<times> 'v) set"
  where [simp]: "op_graph_restrict_left Vl E \<equiv> E \<inter> Vl \<times> UNIV"

definition op_graph_restrict_right :: "'v set \<Rightarrow> ('v \<times> 'v) set \<Rightarrow> ('v \<times> 'v) set"
  where [simp]: "op_graph_restrict_right Vr E \<equiv> E \<inter> UNIV \<times> Vr"

lemma [autoref_op_pat]: 
  "E \<inter> (Vl \<times> Vr) \<equiv> op_graph_restrict Vl Vr E"
  "E \<inter> (Vl \<times> UNIV) \<equiv> op_graph_restrict_left Vl E"
  "E \<inter> (UNIV \<times> Vr) \<equiv> op_graph_restrict_right Vr E"
  by simp_all

lemma graph_restrict_aimpl: "op_graph_restrict Vl Vr E = 
  E_of_succ (\<lambda>v. if v\<in>Vl then {x \<in> E``{v}. x\<in>Vr} else {})"
  by (auto simp: E_of_succ_def succ_of_E_def split: if_split_asm)
lemma graph_restrict_left_aimpl: "op_graph_restrict_left Vl E = 
  E_of_succ (\<lambda>v. if v\<in>Vl then E``{v} else {})"
  by (auto simp: E_of_succ_def succ_of_E_def split: if_split_asm)
lemma graph_restrict_right_aimpl: "op_graph_restrict_right Vr E = 
  E_of_succ (\<lambda>v. {x \<in> E``{v}. x\<in>Vr})"
  by (auto simp: E_of_succ_def succ_of_E_def split: if_split_asm)

schematic_goal graph_restrict_impl_aux:
  fixes Rsl Rsr
  notes [autoref_rel_intf] = REL_INTFI[of Rsl i_set] REL_INTFI[of Rsr i_set]
  assumes [autoref_rules]: "(meml, (\<in>)) \<in> R \<rightarrow> \<langle>R\<rangle>Rsl \<rightarrow> bool_rel"
  assumes [autoref_rules]: "(memr, (\<in>)) \<in> R \<rightarrow> \<langle>R\<rangle>Rsr \<rightarrow> bool_rel"
  shows "(?c, op_graph_restrict) \<in> \<langle>R\<rangle>Rsl \<rightarrow> \<langle>R\<rangle>Rsr \<rightarrow> \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>R\<rangle>slg_rel"
  unfolding graph_restrict_aimpl[abs_def]
  apply (autoref (keep_goal))
  done

schematic_goal graph_restrict_left_impl_aux:
  fixes Rsl Rsr
  notes [autoref_rel_intf] = REL_INTFI[of Rsl i_set] REL_INTFI[of Rsr i_set]
  assumes [autoref_rules]: "(meml, (\<in>)) \<in> R \<rightarrow> \<langle>R\<rangle>Rsl \<rightarrow> bool_rel"
  shows "(?c, op_graph_restrict_left) \<in> \<langle>R\<rangle>Rsl \<rightarrow> \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>R\<rangle>slg_rel"
  unfolding graph_restrict_left_aimpl[abs_def]
  apply (autoref (keep_goal, trace))
  done

schematic_goal graph_restrict_right_impl_aux:
  fixes Rsl Rsr
  notes [autoref_rel_intf] = REL_INTFI[of Rsl i_set] REL_INTFI[of Rsr i_set]
  assumes [autoref_rules]: "(memr, (\<in>)) \<in> R \<rightarrow> \<langle>R\<rangle>Rsr \<rightarrow> bool_rel"
  shows "(?c, op_graph_restrict_right) \<in> \<langle>R\<rangle>Rsr \<rightarrow> \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>R\<rangle>slg_rel"
  unfolding graph_restrict_right_aimpl[abs_def]
  apply (autoref (keep_goal, trace))
  done

concrete_definition graph_restrict_impl uses graph_restrict_impl_aux
concrete_definition graph_restrict_left_impl uses graph_restrict_left_impl_aux
concrete_definition graph_restrict_right_impl uses graph_restrict_right_impl_aux

context begin interpretation autoref_syn .
  lemma [autoref_itype]:
    "op_graph_restrict ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg"
    "op_graph_restrict_right ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg"
    "op_graph_restrict_left ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg"
    by auto
end

lemmas [autoref_rules_raw] = 
  graph_restrict_impl.refine[OF GEN_OP_D GEN_OP_D]
  graph_restrict_left_impl.refine[OF GEN_OP_D]
  graph_restrict_right_impl.refine[OF GEN_OP_D]

schematic_goal "(?c::?'c, \<lambda>(E::nat digraph) x. E``{x}) \<in> ?R"
  apply (autoref (keep_goal))
  done

lemma graph_minus_aimpl: 
  fixes E1 E2 :: "'a rel"
  shows "E1-E2 = E_of_succ (\<lambda>x. E1``{x} - E2``{x})"
  by (auto simp: E_of_succ_def)

schematic_goal graph_minus_impl_aux:
  fixes R :: "('vi\<times>'v) set"
  assumes [autoref_rules]: "(eq,(=))\<in>R\<rightarrow>R\<rightarrow>bool_rel"
  shows "(?c, (-)) \<in> \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>R\<rangle>slg_rel"
  apply (subst graph_minus_aimpl[abs_def])
  apply (autoref (keep_goal,trace))
  done

lemmas [autoref_rules] = graph_minus_impl_aux[OF GEN_OP_D]


lemma graph_minus_set_aimpl: 
  fixes E1 E2 :: "'a rel"
  shows "E1-E2 = E_of_succ (\<lambda>u. {v\<in>E1``{u}. (u,v)\<notin>E2})"
  by (auto simp: E_of_succ_def)

schematic_goal graph_minus_set_impl_aux:
  fixes R :: "('vi\<times>'v) set"
  assumes [autoref_rules]: "(eq,(=))\<in>R\<rightarrow>R\<rightarrow>bool_rel"
  assumes [autoref_rules]: "(mem,(\<in>)) \<in> R \<times>\<^sub>r R \<rightarrow> \<langle>R \<times>\<^sub>r R\<rangle>Rs \<rightarrow> bool_rel"
  shows "(?c, (-)) \<in> \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>R\<times>\<^sub>rR\<rangle>Rs \<rightarrow> \<langle>R\<rangle>slg_rel"
  apply (subst graph_minus_set_aimpl[abs_def])
  apply (autoref (keep_goal,trace))
  done

lemmas [autoref_rules (overloaded)] = graph_minus_set_impl_aux[OF GEN_OP_D GEN_OP_D]



subsection \<open>Rooted Graphs\<close>

subsubsection \<open>Operation Identification Setup\<close>

consts
  i_g_ext :: "interface \<Rightarrow> interface \<Rightarrow> interface"

abbreviation "i_frg \<equiv> \<langle>i_unit\<rangle>\<^sub>ii_g_ext"

context begin interpretation autoref_syn .

lemma g_type[autoref_itype]:
  "g_V ::\<^sub>i \<langle>Ie,I\<rangle>\<^sub>ii_g_ext \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "g_E ::\<^sub>i \<langle>Ie,I\<rangle>\<^sub>ii_g_ext \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg"
  "g_V0 ::\<^sub>i \<langle>Ie,I\<rangle>\<^sub>ii_g_ext \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set"
  "graph_rec_ext
    ::\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_slg \<rightarrow>\<^sub>i \<langle>I\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i iE \<rightarrow>\<^sub>i \<langle>Ie,I\<rangle>\<^sub>ii_g_ext" 
  by simp_all

end


subsubsection \<open>Generic Implementation\<close>
record ('vi,'ei,'v0i) gen_g_impl =
  gi_V :: 'vi
  gi_E :: 'ei
  gi_V0 :: 'v0i

definition gen_g_impl_rel_ext_internal_def: "\<And> Rm Rv Re Rv0. gen_g_impl_rel_ext Rm Rv Re Rv0
  \<equiv> { (gen_g_impl_ext Vi Ei V0i mi, graph_rec_ext V E V0 m) 
      | Vi Ei V0i mi V E V0 m. 
        (Vi,V)\<in>Rv \<and> (Ei,E)\<in>Re \<and> (V0i,V0)\<in>Rv0 \<and> (mi,m)\<in>Rm
    }"

lemma gen_g_impl_rel_ext_def: "\<And>Rm Rv Re Rv0. \<langle>Rm,Rv,Re,Rv0\<rangle>gen_g_impl_rel_ext
  \<equiv> { (gen_g_impl_ext Vi Ei V0i mi, graph_rec_ext V E V0 m) 
      | Vi Ei V0i mi V E V0 m. 
        (Vi,V)\<in>Rv \<and> (Ei,E)\<in>Re \<and> (V0i,V0)\<in>Rv0 \<and> (mi,m)\<in>Rm
    }"
  unfolding gen_g_impl_rel_ext_internal_def relAPP_def by simp

lemma gen_g_impl_rel_sv[relator_props]: 
  "\<And>Rm Rv Re Rv0. \<lbrakk>single_valued Rv; single_valued Re; single_valued Rv0; single_valued Rm \<rbrakk> \<Longrightarrow> 
  single_valued (\<langle>Rm,Rv,Re,Rv0\<rangle>gen_g_impl_rel_ext)"
  unfolding gen_g_impl_rel_ext_def
  apply (auto 
    intro!: single_valuedI 
    dest: single_valuedD slg_rel_sv list_set_rel_sv)
  done

lemma gen_g_refine:
  "\<And>Rm Rv Re Rv0. (gi_V,g_V) \<in> \<langle>Rm,Rv,Re,Rv0\<rangle>gen_g_impl_rel_ext \<rightarrow> Rv"
  "\<And>Rm Rv Re Rv0. (gi_E,g_E) \<in> \<langle>Rm,Rv,Re,Rv0\<rangle>gen_g_impl_rel_ext \<rightarrow> Re"
  "\<And>Rm Rv Re Rv0. (gi_V0,g_V0) \<in> \<langle>Rm,Rv,Re,Rv0\<rangle>gen_g_impl_rel_ext \<rightarrow> Rv0"
  "\<And>Rm Rv Re Rv0. (gen_g_impl_ext, graph_rec_ext) 
    \<in> Rv \<rightarrow> Re \<rightarrow> Rv0 \<rightarrow> Rm \<rightarrow> \<langle>Rm,Rv,Re,Rv0\<rangle>gen_g_impl_rel_ext"
  unfolding gen_g_impl_rel_ext_def
  by auto

subsubsection \<open>Implementation with list-set for Nodes\<close>
type_synonym ('v,'m) frgv_impl_scheme = 
  "('v list, 'v \<Rightarrow> 'v list, 'v list, 'm) gen_g_impl_scheme"

definition frgv_impl_rel_ext_internal_def: 
  "frgv_impl_rel_ext Rm Rv 
  \<equiv> \<langle>Rm,\<langle>Rv\<rangle>list_set_rel,\<langle>Rv\<rangle>slg_rel,\<langle>Rv\<rangle>list_set_rel\<rangle>gen_g_impl_rel_ext"

lemma frgv_impl_rel_ext_def: "\<langle>Rm,Rv\<rangle>frgv_impl_rel_ext
  \<equiv> \<langle>Rm,\<langle>Rv\<rangle>list_set_rel,\<langle>Rv\<rangle>slg_rel,\<langle>Rv\<rangle>list_set_rel\<rangle>gen_g_impl_rel_ext"
  unfolding frgv_impl_rel_ext_internal_def relAPP_def by simp

lemma [autoref_rel_intf]: "REL_INTF frgv_impl_rel_ext i_g_ext"
  by (rule REL_INTFI)

lemma [relator_props, simp]: 
  "\<lbrakk>single_valued Rv; Range Rv = UNIV; single_valued Rm\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rv\<rangle>frgv_impl_rel_ext)"
  unfolding frgv_impl_rel_ext_def by tagged_solver

lemmas [param, autoref_rules] = gen_g_refine[where 
  Rv = "\<langle>Rv\<rangle>list_set_rel" and Re = "\<langle>Rv\<rangle>slg_rel" and ?Rv0.0 = "\<langle>Rv\<rangle>list_set_rel"
  for Rv, folded frgv_impl_rel_ext_def]

subsubsection \<open>Implementation with Cfun for Nodes\<close>
text \<open>This implementation allows for the universal node set.\<close>
type_synonym ('v,'m) g_impl_scheme = 
  "('v \<Rightarrow> bool, 'v \<Rightarrow> 'v list, 'v list, 'm) gen_g_impl_scheme"

definition g_impl_rel_ext_internal_def: 
  "g_impl_rel_ext Rm Rv 
  \<equiv> \<langle>Rm,\<langle>Rv\<rangle>fun_set_rel,\<langle>Rv\<rangle>slg_rel,\<langle>Rv\<rangle>list_set_rel\<rangle>gen_g_impl_rel_ext"

lemma g_impl_rel_ext_def: "\<langle>Rm,Rv\<rangle>g_impl_rel_ext
  \<equiv> \<langle>Rm,\<langle>Rv\<rangle>fun_set_rel,\<langle>Rv\<rangle>slg_rel,\<langle>Rv\<rangle>list_set_rel\<rangle>gen_g_impl_rel_ext"
  unfolding g_impl_rel_ext_internal_def relAPP_def by simp

lemma [autoref_rel_intf]: "REL_INTF g_impl_rel_ext i_g_ext"
  by (rule REL_INTFI)

lemma [relator_props, simp]: 
  "\<lbrakk>single_valued Rv; Range Rv = UNIV; single_valued Rm\<rbrakk> 
  \<Longrightarrow> single_valued (\<langle>Rm,Rv\<rangle>g_impl_rel_ext)"
  unfolding g_impl_rel_ext_def by tagged_solver

lemmas [param, autoref_rules] = gen_g_refine[where 
  Rv = "\<langle>Rv\<rangle>fun_set_rel" 
  and Re = "\<langle>Rv\<rangle>slg_rel" 
  and ?Rv0.0 = "\<langle>Rv\<rangle>list_set_rel" 
  for Rv, folded g_impl_rel_ext_def]

lemma [autoref_rules]: "(gi_V_update, g_V_update) \<in> (\<langle>Rv\<rangle>fun_set_rel \<rightarrow> \<langle>Rv\<rangle>fun_set_rel) \<rightarrow>
  \<langle>Rm, Rv\<rangle>g_impl_rel_ext \<rightarrow> \<langle>Rm, Rv\<rangle>g_impl_rel_ext"
  unfolding g_impl_rel_ext_def gen_g_impl_rel_ext_def
  by (auto, metis (full_types) tagged_fun_relD_both)
lemma [autoref_rules]: "(gi_E_update, g_E_update) \<in> (\<langle>Rv\<rangle>slg_rel \<rightarrow> \<langle>Rv\<rangle>slg_rel) \<rightarrow>
  \<langle>Rm, Rv\<rangle>g_impl_rel_ext \<rightarrow> \<langle>Rm, Rv\<rangle>g_impl_rel_ext"
  unfolding g_impl_rel_ext_def gen_g_impl_rel_ext_def
  by (auto, metis (full_types) tagged_fun_relD_both)
lemma [autoref_rules]: "(gi_V0_update, g_V0_update) \<in> (\<langle>Rv\<rangle>list_set_rel \<rightarrow> \<langle>Rv\<rangle>list_set_rel) \<rightarrow>
  \<langle>Rm, Rv\<rangle>g_impl_rel_ext \<rightarrow> \<langle>Rm, Rv\<rangle>g_impl_rel_ext"
  unfolding g_impl_rel_ext_def gen_g_impl_rel_ext_def
  by (auto, metis (full_types) tagged_fun_relD_both)

(* HACK: The homgeneity rule heuristics erronously creates a homogeneity rule that
    equalizes Rv and Rv0, out of the frv-implementation, which happens to be the
    first. This declaration counters the undesired effects caused by this. *)
lemma [autoref_hom]: 
  "CONSTRAINT graph_rec_ext (\<langle>Rv\<rangle>Rvs \<rightarrow> \<langle>Rv\<rangle>Res \<rightarrow> \<langle>Rv\<rangle>Rv0s \<rightarrow> Rm \<rightarrow> \<langle>Rm,Rv\<rangle>Rg)"
  by simp


schematic_goal "(?c::?'c, \<lambda>G x. g_E G `` {x})\<in>?R"
  apply (autoref (keep_goal))
  done

schematic_goal "(?c,\<lambda>V0 E.
   \<lparr> g_V = UNIV, g_E = E, g_V0 = V0 \<rparr>  )
  \<in>\<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>unit_rel,R\<rangle>g_impl_rel_ext"
  apply (autoref (keep_goal))
  done

schematic_goal "(?c,\<lambda>V V0 E.
   \<lparr> g_V = V, g_E = E, g_V0 = V0 \<rparr>  )
  \<in>\<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>list_set_rel \<rightarrow> \<langle>R\<rangle>slg_rel \<rightarrow> \<langle>unit_rel,R\<rangle>frgv_impl_rel_ext"
  apply (autoref (keep_goal))
  done

subsubsection \<open>Renaming\<close>

definition "the_inv_into_map V f x 
  = (if x \<in> f`V then Some (the_inv_into V f x) else None)"

lemma the_inv_into_map_None[simp]:
  "the_inv_into_map V f x = None \<longleftrightarrow> x \<notin> f`V"
  unfolding the_inv_into_map_def by auto

lemma the_inv_into_map_Some':
  "the_inv_into_map V f x = Some y \<longleftrightarrow> x \<in> f`V \<and> y=the_inv_into V f x"
  unfolding the_inv_into_map_def by auto

lemma the_inv_into_map_Some[simp]:
  "inj_on f V \<Longrightarrow> the_inv_into_map V f x = Some y \<longleftrightarrow> y\<in>V \<and> x=f y"
  by (auto simp: the_inv_into_map_Some' the_inv_into_f_f)

definition "the_inv_into_map_impl V f = 
  FOREACH V (\<lambda>x m. RETURN (m(f x \<mapsto> x))) Map.empty"

lemma the_inv_into_map_impl_correct:
  assumes [simp]: "finite V"
  assumes INJ: "inj_on f V"
  shows "the_inv_into_map_impl V f \<le> SPEC (\<lambda>r. r = the_inv_into_map V f)"
  unfolding the_inv_into_map_impl_def
  apply (refine_rcg 
    FOREACH_rule[where I="\<lambda>it m. m=the_inv_into_map (V - it) f"]
    refine_vcg
  )

  apply (vc_solve 
    simp: the_inv_into_map_def[abs_def] it_step_insert_iff 
    intro!: ext)

  apply (intro allI impI conjI)

  apply (subst the_inv_into_f_f[OF subset_inj_on[OF INJ]], auto) []

  apply (subst the_inv_into_f_f[OF subset_inj_on[OF INJ]], auto) []

  apply safe []
  apply (subst the_inv_into_f_f[OF subset_inj_on[OF INJ]], (auto) [2])+
  apply simp
  done

schematic_goal the_inv_into_map_code_aux:
  fixes Rv' :: "('vti \<times> 'vt) set"
  assumes [autoref_ga_rules]: "is_bounded_hashcode Rv' eq bhc"
  assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('vti) (def_size)"
  assumes [autoref_rules]: "(Vi,V)\<in>\<langle>Rv\<rangle>list_set_rel"
  assumes [autoref_rules]: "(fi,f)\<in>Rv\<rightarrow>Rv'"
  shows "(RETURN ?c, the_inv_into_map_impl V f) \<in> \<langle>\<langle>Rv',Rv\<rangle>ahm_rel bhc\<rangle>nres_rel"
  unfolding the_inv_into_map_impl_def[abs_def]
  apply (autoref_monadic (plain))
  done

concrete_definition the_inv_into_map_code uses the_inv_into_map_code_aux
export_code the_inv_into_map_code checking SML

thm the_inv_into_map_code.refine

context begin interpretation autoref_syn .
lemma autoref_the_inv_into_map[autoref_rules]:
  fixes Rv' :: "('vti \<times> 'vt) set"
  assumes "SIDE_GEN_ALGO (is_bounded_hashcode Rv' eq bhc)"
  assumes "SIDE_GEN_ALGO (is_valid_def_hm_size TYPE('vti) def_size)"
  assumes INJ: "SIDE_PRECOND (inj_on f V)"
  assumes V: "(Vi,V)\<in>\<langle>Rv\<rangle>list_set_rel"
  assumes F: "(fi,f)\<in>Rv\<rightarrow>Rv'"
  shows "(the_inv_into_map_code eq bhc def_size Vi fi, 
    (OP the_inv_into_map 
      ::: \<langle>Rv\<rangle>list_set_rel \<rightarrow> (Rv\<rightarrow>Rv') \<rightarrow> \<langle>Rv', Rv\<rangle>Impl_Array_Hash_Map.ahm_rel bhc)
    $V$f) \<in> \<langle>Rv', Rv\<rangle>Impl_Array_Hash_Map.ahm_rel bhc"
proof simp

  from V have FIN: "finite V" using list_set_rel_range by auto

  note the_inv_into_map_code.refine[
    OF assms(1-2,4-5)[unfolded autoref_tag_defs], THEN nres_relD 
  ]
  also note the_inv_into_map_impl_correct[OF FIN INJ[unfolded autoref_tag_defs]]
  finally show "(the_inv_into_map_code eq bhc def_size Vi fi, the_inv_into_map V f)
    \<in> \<langle>Rv', Rv\<rangle>Impl_Array_Hash_Map.ahm_rel bhc"
    by (simp add: refine_pw_simps pw_le_iff)
qed

end

schematic_goal "(?c::?'c, do { 
  let s = {1,2,3::nat}; 
  \<^cancel>\<open>ASSERT (inj_on Suc s);\<close>
  RETURN (the_inv_into_map s Suc) }) \<in> ?R"
  apply (autoref (keep_goal))
  done


definition "fr_rename_ext_aimpl ecnv f G \<equiv> do {
    ASSERT (inj_on f (g_V G));
    ASSERT (inj_on f (g_V0 G));
    let fi_map = the_inv_into_map (g_V G) f;
    e \<leftarrow> ecnv fi_map G;
    RETURN \<lparr>
      g_V = f`(g_V G),
      g_E = (E_of_succ (\<lambda>v. case fi_map v of
          Some u \<Rightarrow> f ` (succ_of_E (g_E G) u) | None \<Rightarrow> {})),
      g_V0 = (f`g_V0 G),
      \<dots> = e
    \<rparr>
  }"

context g_rename_precond begin

  definition "fi_map x = (if x \<in> f`V then Some (fi x) else None)"
  lemma fi_map_alt: "fi_map = the_inv_into_map V f"
    apply (rule ext)
    unfolding fi_map_def the_inv_into_map_def fi_def
    by simp
    
  lemma fi_map_Some: "(fi_map u = Some v) \<longleftrightarrow> u\<in>f`V \<and> fi u = v"
    unfolding fi_map_def by (auto split: if_split_asm)

  lemma fi_map_None: "(fi_map u = None) \<longleftrightarrow> u\<notin>f`V"
    unfolding fi_map_def by (auto split: if_split_asm)

  lemma rename_E_aimpl_alt: "rename_E f E = E_of_succ (\<lambda>v. case fi_map v of
    Some u \<Rightarrow> f ` (succ_of_E E u) | None \<Rightarrow> {})"
    unfolding E_of_succ_def succ_of_E_def
    using E_ss
    by (force 
      simp: fi_f f_fi fi_map_Some fi_map_None 
      split: if_split_asm option.splits)


  lemma frv_rename_ext_aimpl_alt: 
    assumes ECNV: "ecnv' fi_map G \<le> SPEC (\<lambda>r. r = ecnv G)"
    shows "fr_rename_ext_aimpl ecnv' f G 
      \<le> SPEC (\<lambda>r. r = fr_rename_ext ecnv f G)"
  proof -
    (*have [simp]: "\<lparr> g_E =
             E_of_succ
              (\<lambda>v. case the_inv_into_map V f v of None \<Rightarrow> {}
                 | Some u \<Rightarrow> f ` succ_of_E (g_E G) u),
            g_V0 = f ` g_V0 G, \<dots> = ecnv Gv\<rparr>
      = frv_G (frv_rename_ext ecnv f Gv)"
      unfolding frv_rename_ext_def 
      by (auto simp: rename_E_aimpl_alt fi_map_alt)

    have [simp]: "\<lparr>frv_V = f ` V, frv_G = frv_G Gv'\<rparr> = Gv'"
      unfolding frv_rename_ext_def
      by simp*)

    show ?thesis
      unfolding fr_rename_ext_def fr_rename_ext_aimpl_def
      apply (refine_rcg 
        order_trans[OF ECNV[unfolded fi_map_alt]] 
        refine_vcg)
      using subset_inj_on[OF _ V0_ss]
      apply (auto intro: INJ simp: rename_E_aimpl_alt fi_map_alt)
      done
  qed
end

term frv_rename_ext_aimpl
schematic_goal fr_rename_ext_impl_aux:
  fixes Re and Rv' :: "('vti \<times> 'vt) set"
  assumes [autoref_rules]: "(eq, (=)) \<in> Rv' \<rightarrow> Rv' \<rightarrow> bool_rel"
  assumes [autoref_ga_rules]: "is_bounded_hashcode Rv' eq bhc"
  assumes [autoref_ga_rules]: "is_valid_def_hm_size TYPE('vti) def_size"
  shows "(?c,fr_rename_ext_aimpl) \<in> 
    ((\<langle>Rv',Rv\<rangle>ahm_rel bhc) \<rightarrow> \<langle>Re,Rv\<rangle>frgv_impl_rel_ext \<rightarrow> \<langle>Re'\<rangle>nres_rel) \<rightarrow>   
    (Rv\<rightarrow>Rv') \<rightarrow>
    \<langle>Re,Rv\<rangle>frgv_impl_rel_ext \<rightarrow> 
    \<langle>\<langle>Re',Rv'\<rangle>frgv_impl_rel_ext\<rangle>nres_rel"
  unfolding fr_rename_ext_aimpl_def[abs_def]
  apply (autoref (keep_goal))
  done

concrete_definition fr_rename_ext_impl uses fr_rename_ext_impl_aux

thm fr_rename_ext_impl.refine[OF GEN_OP_D SIDE_GEN_ALGO_D SIDE_GEN_ALGO_D]

subsection \<open>Graphs from Lists\<close>

definition succ_of_list :: "(nat\<times>nat) list \<Rightarrow> nat \<Rightarrow> nat set"
  where
  "succ_of_list l \<equiv> let
    m = fold (\<lambda>(u,v) g. 
          case g u of 
            None \<Rightarrow> g(u\<mapsto>{v})
          | Some s \<Rightarrow> g(u\<mapsto>insert v s)
        ) l Map.empty
  in
    (\<lambda>u. case m u of None \<Rightarrow> {} | Some s \<Rightarrow> s)"
    
lemma succ_of_list_correct_aux: 
  "(succ_of_list l, set l) \<in> br (\<lambda>succs. {(u,v). v\<in>succs u}) (\<lambda>_. True)"
proof -

  term the_default

  { fix m
    have "fold (\<lambda>(u,v) g. 
            case g u of 
              None \<Rightarrow> g(u\<mapsto>{v})
            | Some s \<Rightarrow> g(u\<mapsto>insert v s)
          ) l m 
      = (\<lambda>u. let s=set l `` {u} in 
          if s={} then m u else Some (the_default {} (m u) \<union> s))"
      apply (induction l arbitrary: m)
      apply (auto 
        split: option.split if_split 
        simp: Let_def Image_def
        intro!: ext)
      done
  } note aux=this
  
  show ?thesis
    unfolding succ_of_list_def aux
    by (auto simp: br_def Let_def split: option.splits if_split_asm)
qed


schematic_goal succ_of_list_impl:
  notes [autoref_tyrel] = 
    ty_REL[where 'a="nat\<rightharpoonup>nat set" and R="\<langle>nat_rel,R\<rangle>iam_map_rel" for R]
    ty_REL[where 'a="nat set" and R="\<langle>nat_rel\<rangle>list_set_rel"]

  shows "(?f::?'c,succ_of_list) \<in> ?R"
  unfolding succ_of_list_def[abs_def]
  apply (autoref (keep_goal))
  done

concrete_definition succ_of_list_impl uses succ_of_list_impl
export_code succ_of_list_impl in SML

lemma succ_of_list_impl_correct: "(succ_of_list_impl,set) \<in> Id \<rightarrow> \<langle>Id\<rangle>slg_rel"
  apply rule
  unfolding slg_rel_def
  apply rule
  apply (rule succ_of_list_impl.refine[THEN fun_relD])
  apply simp
  apply (rule succ_of_list_correct_aux)
  done

end


