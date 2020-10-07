(*  Title:      Generic_Interpretation.thy
    Author:     Sebastian Ullrich, Denis Lohner
*)

subsection \<open>Generic Code Extraction Based on typedefs\<close>

theory Generic_Interpretation
imports
Construct_SSA_code
Construct_SSA_notriv_code
RBT_Mapping_Exts
SSA_Transfer_Rules
"HOL-Library.RBT_Set"
"HOL-Library.Code_Target_Numeral"
begin

record ('node, 'var, 'edge) gen_cfg =
  gen_\<alpha>e :: "('node, 'edge) edge set"
  gen_\<alpha>n :: "'node list"
  gen_inEdges :: "'node \<Rightarrow> ('node, 'edge) edge list"
  gen_Entry :: "'node"
  gen_defs :: "'node \<Rightarrow> 'var set"
  gen_uses :: "'node \<Rightarrow> 'var set"

abbreviation "trivial_gen_cfg ext \<equiv> gen_cfg_ext {} [undefined] (const []) undefined (const {}) (const {}) ext"
abbreviation (input) "ign f g (_::unit) \<equiv> f g"

lemma set_iterator_foldri_Nil [simp, intro!]: "set_iterator (foldri []) {}"
  by (rule set_iterator_I; simp add: foldri_def)

lemma set_iterator_foldri_one [simp, intro!]: "set_iterator (foldri [a]) {a}"
  by (rule set_iterator_I; simp add: foldri_def)

abbreviation "gen_inEdges' g n \<equiv> map (\<lambda>(f,d,t). (f,d)) (gen_inEdges g n)"

lemma gen_cfg_inhabited: "let g = trivial_gen_cfg ext in CFG_wf (ign gen_\<alpha>e g) (ign gen_\<alpha>n g) (const True) (ign gen_inEdges' g) (ign gen_Entry g) (ign gen_defs g) (ign gen_uses g)"
apply auto
apply unfold_locales
by (auto simp: gen_cfg.defs graph_path_base.path2_def pred_def graph_path_base.inEdges_def intro!: graph_path_base.path.intros(1) exI)

typedef ('node, 'var, 'edge) gen_cfg_wf = "{g :: ('node::linorder, 'var::linorder, 'edge) gen_cfg.
  CFG_wf (ign gen_\<alpha>e g) (ign gen_\<alpha>n g) (const True) (ign gen_inEdges' g) (ign gen_Entry g) (ign gen_defs g) (ign gen_uses g)}"
by (rule exI[where x="trivial_gen_cfg undefined"]) (simp add: gen_cfg_inhabited[simplified])

setup_lifting type_definition_gen_cfg_wf

lift_definition gen_wf_\<alpha>n :: "('node::linorder, 'var::linorder, 'edge) gen_cfg_wf \<Rightarrow> 'node list" is gen_\<alpha>n .
lift_definition gen_wf_\<alpha>e :: "('node::linorder, 'var::linorder, 'edge) gen_cfg_wf \<Rightarrow> ('node, 'edge) edge set" is gen_\<alpha>e .
lift_definition gen_wf_inEdges :: "('node::linorder, 'var::linorder, 'edge) gen_cfg_wf \<Rightarrow> 'node \<Rightarrow> ('node, 'edge) edge list" is gen_inEdges .
lift_definition gen_wf_Entry :: "('node::linorder, 'var::linorder, 'edge) gen_cfg_wf \<Rightarrow> 'node" is gen_Entry .
lift_definition gen_wf_defs :: "('node::linorder, 'var::linorder, 'edge) gen_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'var set" is gen_defs .
lift_definition gen_wf_uses :: "('node::linorder, 'var::linorder, 'edge) gen_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'var set" is gen_uses .

abbreviation "gen_wf_invar \<equiv> const True"
abbreviation "gen_wf_inEdges' g n \<equiv> map (\<lambda>(f,d,t). (f,d)) (gen_wf_inEdges g n)"

lemma gen_wf_inEdges'_transfer [transfer_rule]: "rel_fun cr_gen_cfg_wf (=) gen_inEdges' gen_wf_inEdges'"
  using gen_wf_inEdges.transfer
  apply (auto simp: rel_fun_def cr_gen_cfg_wf_def)
  by (erule_tac x=y in allE) simp

lemma gen_wf_invar_trans: "rel_fun cr_gen_cfg_wf (=) gen_wf_invar gen_wf_invar"
by auto


declare graph_path_base.transfer_rules[OF gen_cfg_wf.right_total gen_wf_\<alpha>e.transfer gen_wf_\<alpha>n.transfer gen_wf_invar_trans gen_wf_inEdges'_transfer, transfer_rule]
declare CFG_base.defAss'_transfer[OF gen_cfg_wf.right_total gen_wf_\<alpha>e.transfer gen_wf_\<alpha>n.transfer gen_wf_invar_trans gen_wf_inEdges'_transfer, transfer_rule]

global_interpretation gen_wf: CFG_Construct_linorder gen_wf_\<alpha>e gen_wf_\<alpha>n gen_wf_invar gen_wf_inEdges' gen_wf_Entry gen_wf_defs gen_wf_uses
defines
  gen_wf_predecessors = gen_wf.predecessors and
  gen_wf_successors = gen_wf.successors and
  gen_wf_defs' = gen_wf.defs' and
  gen_wf_vars = gen_wf.vars and
  gen_wf_var = gen_wf.var and
  gen_wf_readVariableRecursive = gen_wf.readVariableRecursive and
  gen_wf_readArgs = gen_wf.readArgs and
  gen_wf_uses'_phis' = gen_wf.uses'_phis'
apply unfold_locales
              apply (transfer, simp add: CFG_Construct_wf_def CFG_wf_def CFG_def graph_Entry_def graph_path_def graph_Entry_axioms_def)
             apply (transfer, simp add: CFG_Construct_wf_def CFG_wf_def CFG_def graph_Entry_def graph_path_def graph_def)
            apply (transfer, simp add: CFG_Construct_wf_def CFG_wf_def CFG_def graph_Entry_def graph_path_def graph_def valid_graph_def)
           apply (transfer, simp add: CFG_Construct_wf_def CFG_wf_def CFG_def graph_Entry_def graph_path_def graph_Entry_axioms_def graph_def valid_graph_def)
          apply simp
          apply (rule set_iterator_foldri_correct)
          apply (transfer, clarsimp simp add: CFG_Construct_wf_def CFG_wf_def CFG_def graph_Entry_def)
          apply (drule graph_path.\<alpha>n_distinct; simp)
         apply (transfer, clarsimp simp: CFG_Construct_wf_def CFG_wf_def CFG_def graph_Entry_def graph_path_def graph_pred_it_def graph_pred_it_axioms_def)
        apply (transfer, clarsimp simp: CFG_Construct_wf_def CFG_wf_def CFG_def graph_Entry_def graph_Entry_axioms_def)
       apply (transfer, clarsimp simp: CFG_Construct_wf_def CFG_wf_def CFG_def graph_Entry_def graph_Entry_axioms_def graph_path_base.inEdges_def)
      apply (transfer, clarsimp simp: CFG_Construct_wf_def CFG_wf_def CFG_def graph_Entry_def graph_Entry_axioms_def graph_path_base.path2_def graph_path_base.path_def graph_path_base.predecessors_def graph_path_base.inEdges_def)
     apply (transfer, simp only: CFG_Construct_wf_def CFG_wf_def CFG_def CFG_axioms_def)
    apply (transfer, simp only: CFG_Construct_wf_def CFG_wf_def CFG_def CFG_axioms_def)
   apply (transfer, simp only: CFG_Construct_wf_def CFG_wf_def CFG_def CFG_axioms_def)
  apply (transfer, simp only: CFG_Construct_wf_def CFG_wf_def CFG_def CFG_axioms_def)
 apply simp
by (transfer, clarsimp simp: CFG_Construct_wf_def CFG_wf_def CFG_wf_axioms_def CFG_base.defAss'_def [abs_def]
  graph_path_base.path2_def graph_path_base.path_def graph_path_base.predecessors_def graph_path_base.inEdges_def)

record ('node, 'var, 'edge, 'val) gen_ssa_cfg = "('node, 'var, 'edge) gen_cfg" +
  gen_ssa_defs :: "'node \<Rightarrow> 'val set"
  gen_ssa_uses :: "('node, 'val set) mapping"
  gen_phis :: "('node, 'val) phis_code"
  gen_var :: "'val \<Rightarrow> 'var"

typedef ('node, 'var, 'edge, 'val) gen_ssa_cfg_wf = "{g :: ('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg.
  CFG_SSA_Transformed_code (ign gen_\<alpha>e g) (ign gen_\<alpha>n g) (const True) (ign gen_inEdges' g) (ign gen_Entry g) (ign gen_defs g) (ign gen_uses g) (ign gen_ssa_defs g) (ign gen_ssa_uses g) (ign gen_phis g) (ign gen_var g)}"
apply (rule exI[where x ="trivial_gen_cfg \<lparr> gen_ssa_defs = const {}, gen_ssa_uses = Mapping.empty, gen_phis = Mapping.empty, gen_var = undefined, \<dots> = undefined \<rparr>"])
apply auto
apply unfold_locales
by (auto simp: gen_cfg.defs graph_path_base.path2_def dom_def Mapping.lookup_empty CFG_SSA_base.CFG_SSA_defs pred_def  graph_path_base.inEdges_def intro!: graph_path_base.path.intros(1) exI)

setup_lifting type_definition_gen_ssa_cfg_wf

lift_definition gen_ssa_wf_\<alpha>n :: "('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node list" is gen_\<alpha>n .
lift_definition gen_ssa_wf_\<alpha>e :: "('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> ('node, 'edge) edge set" is gen_\<alpha>e .
lift_definition gen_ssa_wf_inEdges :: "('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node \<Rightarrow> ('node, 'edge) edge list" is gen_inEdges .
lift_definition gen_ssa_wf_Entry :: "('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node" is gen_Entry .
lift_definition gen_ssa_wf_defs :: "('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'var set" is gen_defs .
lift_definition gen_ssa_wf_uses :: "('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'var set" is gen_uses .
lift_definition gen_ssa_wf_ssa_defs :: "('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'node \<Rightarrow> 'val set" is gen_ssa_defs .
lift_definition gen_ssa_wf_ssa_uses :: "('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> ('node, 'val set) mapping" is gen_ssa_uses .
lift_definition gen_ssa_wf_phis :: "('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> ('node, 'val) phis_code" is gen_phis .
lift_definition gen_ssa_wf_var :: "('node::linorder, 'var::linorder, 'edge, 'val::linorder) gen_ssa_cfg_wf \<Rightarrow> 'val \<Rightarrow> 'var" is gen_var .

abbreviation "gen_ssa_wf_inEdges' g n \<equiv> map (\<lambda>(f,d,t). (f,d)) (gen_ssa_wf_inEdges g n)"

lemma gen_ssa_wf_inEdges'_transfer [transfer_rule]: "rel_fun cr_gen_ssa_cfg_wf (=) gen_inEdges' gen_ssa_wf_inEdges'"
  using gen_ssa_wf_inEdges.transfer
  apply (auto simp: rel_fun_def cr_gen_cfg_wf_def)
  by (erule_tac x=x in allE) simp

global_interpretation uninst: CFG_SSA_wf_base_code gen_ssa_wf_\<alpha>e gen_ssa_wf_\<alpha>n gen_wf_invar gen_ssa_wf_inEdges' gen_ssa_wf_Entry gen_ssa_wf_ssa_defs u p
  for u and p
  defines
      uninst_predecessors = uninst.predecessors
  and uninst_successors = uninst.successors
  and uninst_phiDefs = uninst.phiDefs
  and uninst_phiUses = uninst.phiUses
  and uninst_allDefs = uninst.allDefs
  and uninst_allUses = uninst.allUses
  and uninst_allVars = uninst.allVars
  and uninst_isTrivialPhi = uninst.isTrivialPhi
  and uninst_trivial = uninst.trivial_code
  and uninst_redundant = uninst.redundant_code
  and uninst_phi = uninst.phi
  and uninst_defNode = uninst.defNode
  and uninst_trivial_phis = uninst.trivial_phis
  and uninst_phidefNodes = uninst.phidefNodes
  and uninst_useNodes_of = uninst.useNodes_of
  and uninst_phiNodes_of = uninst.phiNodes_of
.

definition "uninst_chooseNext u p g \<equiv> Max (uninst_trivial_phis (const p) g)"

lemma gen_ssa_wf_invar_trans: "rel_fun cr_gen_ssa_cfg_wf (=) gen_wf_invar gen_wf_invar"
by auto

declare graph_path_base.transfer_rules[OF gen_ssa_cfg_wf.right_total gen_ssa_wf_\<alpha>e.transfer gen_ssa_wf_\<alpha>n.transfer gen_ssa_wf_invar_trans gen_ssa_wf_inEdges'_transfer, transfer_rule]
declare CFG_base.defAss'_transfer[OF gen_ssa_cfg_wf.right_total gen_ssa_wf_\<alpha>e.transfer gen_ssa_wf_\<alpha>n.transfer gen_ssa_wf_invar_trans gen_ssa_wf_inEdges'_transfer, transfer_rule]
declare CFG_SSA_base_code.CFG_SSA_base_code_transfer_rules[OF gen_ssa_cfg_wf.right_total gen_ssa_wf_\<alpha>e.transfer gen_ssa_wf_\<alpha>n.transfer gen_ssa_wf_invar_trans gen_ssa_wf_inEdges'_transfer gen_ssa_wf_Entry.transfer gen_ssa_wf_ssa_defs.transfer gen_ssa_wf_ssa_uses.transfer gen_ssa_wf_phis.transfer, transfer_rule]


lemma path2_ign[simp]: "graph_path_base.path2 (ign gen_\<alpha>n g) gen_wf_invar (ign gen_inEdges' g) g' n ns m \<longleftrightarrow> graph_path_base.path2 gen_\<alpha>n gen_wf_invar gen_inEdges' g n ns m"
by (simp add: graph_path_base.path2_def graph_path_base.path_def graph_path_base.predecessors_def graph_path_base.inEdges_def)
lemma allDefs_ign[simp]: "CFG_SSA_base.allDefs (ign gen_ssa_defs g) (ign Mapping.lookup (gen_phis g)) ga n = CFG_SSA_base.allDefs gen_ssa_defs (\<lambda>g. Mapping.lookup (gen_phis g)) g n"
by (simp add: CFG_SSA_base.CFG_SSA_defs)
lemma successors_ign[simp]: "graph_path_base.successors (ign gen_\<alpha>n g) (ign gen_inEdges' g) ga n = graph_path_base.successors gen_\<alpha>n gen_inEdges' g n"
by (simp add: graph_path_base.successors_def graph_path_base.predecessors_def graph_path_base.inEdges_def)
lemma predecessors_ign[simp]: "graph_path_base.predecessors (ign gen_inEdges' g) ga n = graph_path_base.predecessors gen_inEdges' g n"
by (simp add: graph_path_base.predecessors_def graph_path_base.inEdges_def)
lemma phiDefs_ign[simp]: "CFG_SSA_base.phiDefs (ign Mapping.lookup (gen_phis g)) ga = CFG_SSA_base.phiDefs (\<lambda>g. Mapping.lookup (gen_phis g)) g"
by (simp add: CFG_SSA_base.phiDefs_def [abs_def])
lemma defAss_ign[simp]: "CFG_SSA_base.defAss (ign gen_\<alpha>n g) gen_wf_invar (ign gen_inEdges' g) (ign gen_Entry g) (ign gen_ssa_defs g) (ign Mapping.lookup (gen_phis g)) ga
  = CFG_SSA_base.defAss gen_\<alpha>n gen_wf_invar gen_inEdges' gen_Entry gen_ssa_defs (\<lambda>g. Mapping.lookup (gen_phis g)) g"
by (simp add: CFG_SSA_base.defAss_def [abs_def])
lemma allUses_ign[simp]: "CFG_SSA_base.allUses (ign gen_\<alpha>n g) (ign gen_inEdges' g) (usesOf \<circ> ign gen_ssa_uses g) (ign Mapping.lookup (gen_phis g)) ga m
  = CFG_SSA_base.allUses gen_\<alpha>n gen_inEdges' (usesOf \<circ> gen_ssa_uses) (\<lambda>g. Mapping.lookup (gen_phis g)) g m"
by (simp add: CFG_SSA_base.CFG_SSA_defs)
lemma defAss'_ign[simp]: "CFG_base.defAss' (ign gen_\<alpha>n g) gen_wf_invar (ign gen_inEdges' g) (ign gen_Entry g) (ign gen_defs g) ga
  = CFG_base.defAss' gen_\<alpha>n gen_wf_invar gen_inEdges' gen_Entry gen_defs g"
by (simp add: CFG_base.defAss'_def [abs_def])

global_interpretation gen_ssa_wf_notriv: CFG_SSA_Transformed_notriv_linorder_code gen_ssa_wf_\<alpha>e gen_ssa_wf_\<alpha>n gen_wf_invar gen_ssa_wf_inEdges' gen_ssa_wf_Entry gen_ssa_wf_defs gen_ssa_wf_uses gen_ssa_wf_ssa_defs gen_ssa_wf_ssa_uses gen_ssa_wf_phis gen_ssa_wf_var uninst_chooseNext
defines
  gen_ssa_wf_notriv_substAll = gen_ssa_wf_notriv.substAll and
  gen_ssa_wf_notriv_substAll_efficient = gen_ssa_wf_notriv.substAll_efficient
apply unfold_locales
                                 apply simp
                                apply (transfer, clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_wf_def CFG_def graph_Entry_def graph_path_def graph_def)
                               apply (transfer, clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_wf_def CFG_def graph_Entry_def graph_path_def graph_def valid_graph_def)
                              apply (transfer, clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_wf_def CFG_def graph_Entry_def graph_path_def graph_def valid_graph_def)
                             apply (transfer, clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_wf_def CFG_def graph_Entry_def graph_path_def graph_nodes_it_def graph_nodes_it_axioms_def)
                            apply (transfer, clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_wf_def CFG_def graph_Entry_def graph_path_def graph_pred_it_def graph_pred_it_axioms_def)
                           apply (transfer, simp only: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def CFG_wf_def CFG_def graph_Entry_def graph_Entry_axioms_def)
                          apply (transfer, simp only: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def CFG_wf_def CFG_def graph_Entry_def graph_Entry_axioms_def graph_path_base.inEdges_def)
                         apply (transfer, simp only: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def  CFG_wf_def CFG_def graph_Entry_def graph_Entry_axioms_def graph_path_base.path2_def
                                                    graph_path_base.path_def graph_path_base.predecessors_def graph_path_base.inEdges_def)
                        apply (transfer, clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def  CFG_wf_def CFG_def CFG_axioms_def)
                       apply (transfer, simp only: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def  CFG_wf_def CFG_def CFG_axioms_def)
                      apply (transfer, clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def  CFG_wf_def CFG_def CFG_axioms_def)
                     apply (transfer, clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def  CFG_wf_def CFG_def CFG_axioms_def)
                    apply simp
                   subgoal by transfer (simp add: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_wf_def CFG_def CFG_axioms_def CFG_SSA_def CFG_SSA_axioms_def)
                  apply (transfer; force simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def CFG_SSA_axioms_def)
                 apply (transfer; simp add: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def CFG_SSA_axioms_def graph_path_base.predecessors_def graph_path_base.inEdges_def)
                apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def CFG_SSA_axioms_def)
               apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_def CFG_SSA_axioms_def)
              apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_wf_axioms_def CFG_SSA_base.defAss_def)
             apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_SSA_wf_axioms_def)
            apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_wf_def CFG_def CFG_axioms_def)
           apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_wf_def CFG_def CFG_axioms_def)
          apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_wf_def CFG_def CFG_axioms_def)
         apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_wf_def CFG_def CFG_axioms_def)
        apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_wf_def CFG_wf_def CFG_wf_axioms_def)
       apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_Transformed_axioms_def)
      apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_Transformed_axioms_def)
     apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_Transformed_axioms_def)
    apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_Transformed_axioms_def)
   apply (transfer; clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_def CFG_SSA_Transformed_axioms_def)
proof-
  fix u p g
  assume "CFG_SSA_Transformed gen_ssa_wf_\<alpha>e gen_ssa_wf_\<alpha>n gen_wf_invar gen_ssa_wf_inEdges' gen_ssa_wf_Entry gen_ssa_wf_defs gen_ssa_wf_uses gen_ssa_wf_ssa_defs (u::('a, 'b, 'c, 'd) gen_ssa_cfg_wf \<Rightarrow> 'a \<Rightarrow> 'd set) p gen_ssa_wf_var"
  then interpret i: CFG_SSA_Transformed gen_ssa_wf_\<alpha>e gen_ssa_wf_\<alpha>n gen_wf_invar gen_ssa_wf_inEdges' gen_ssa_wf_Entry gen_ssa_wf_defs gen_ssa_wf_uses gen_ssa_wf_ssa_defs u p gen_ssa_wf_var .
  obtain u' where [simp]: "usesOf \<circ> u' = u"
    apply (erule_tac x="\<lambda>g. Mapping.Mapping (\<lambda>n. if u g n = {} then None else Some (u g n))" in meta_allE)
    by (erule meta_impE) (auto 4 4 simp: o_def usesOf_def [abs_def] split: option.splits if_splits)
  interpret code: CFG_SSA_wf_code gen_ssa_wf_\<alpha>e gen_ssa_wf_\<alpha>n gen_wf_invar gen_ssa_wf_inEdges' gen_ssa_wf_Entry gen_ssa_wf_ssa_defs u' "\<lambda>g. Mapping.Mapping (p g)"
  unfolding CFG_SSA_wf_code_def CFG_SSA_code_def
  apply simp_all
  apply (rule conjI)
  by unfold_locales

  have aux: "uninst_trivial_phis (const (Mapping.Mapping (p g))) g = uninst_trivial_phis (\<lambda>g. (Mapping.Mapping (p g))) g"
  by (simp add: uninst.trivial_phis_def[abs_def])

  assume red: "i.redundant g"
  let ?cN = "uninst_chooseNext (u g) (Mapping.Mapping (p g)) g"

  show "?cN \<in> dom (p g) \<and> i.trivial g (snd ?cN)"
  unfolding uninst_chooseNext_def aux
  unfolding uninst_trivial_phis_def code.trivial_phis
  apply (rule CollectD[where a="Max _"])
  apply (rule subsetD[OF _ Max_in])
    apply auto[1]
   apply (rule finite_subset[OF _ i.phis_finite])
   using red
   apply (auto simp: i.redundant_def[abs_def])
  apply (frule code.trivial_phi[simplified])
  apply (auto simp: i.phi_def)
  done
next
  fix g
  show "Mapping.keys (gen_ssa_wf_ssa_uses (g::('a, 'b, 'c, 'd) gen_ssa_cfg_wf)) \<subseteq> set (gen_ssa_wf_\<alpha>n g)"
  by transfer (clarsimp simp: CFG_SSA_Transformed_code_def CFG_SSA_Transformed_code_axioms_def)
qed (auto simp: uninst_chooseNext_def uninst_trivial_phis_def CFG_SSA_wf_base_code.trivial_phis_def)

global_interpretation uninst_code: CFG_SSA_Transformed_notriv_base_code gen_ssa_wf_\<alpha>e gen_ssa_wf_\<alpha>n gen_wf_invar gen_ssa_wf_inEdges' gen_ssa_wf_Entry gen_ssa_wf_defs gen_ssa_wf_uses gen_ssa_wf_ssa_defs u p gen_ssa_wf_var uninst_chooseNext
for u and p
defines
  uninst_code_step_code = uninst_code.step_codem and
  uninst_code_phis' = uninst_code.phis'_codem and
  uninst_code_uses' = uninst_code.uses'_codem and
  uninst_code_substNext = uninst_code.substNext_code and
  uninst_code_substitution = uninst_code.substitution_code and
  uninst_code_triv_phis' = uninst_code.triv_phis' and
  uninst_code_nodes_of_uses' = uninst_code.nodes_of_uses' and
  uninst_code_nodes_of_phis' = uninst_code.nodes_of_phis'
.

lift_definition gen_cfg_wf_extend :: "('a::linorder, 'b::linorder, 'c) gen_cfg_wf \<Rightarrow> 'd \<Rightarrow> ('a, 'b, 'c, 'd) gen_cfg_scheme"
  is gen_cfg.extend .

lemma gen_\<alpha>e_wf_extend [simp]:
  "gen_\<alpha>e (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_\<alpha>e gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_\<alpha>e_def)

lemma gen_\<alpha>n_wf_extend [simp]:
  "gen_\<alpha>n (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_\<alpha>n gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_\<alpha>n_def)

lemma gen_inEdges_wf_extend [simp]:
  "gen_inEdges (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_inEdges gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_inEdges_def)

lemma gen_Entry_wf_extend [simp]:
  "gen_Entry (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_Entry gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_Entry_def)

lemma gen_defs_wf_extend [simp]:
  "gen_defs (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_defs gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_defs_def)

lemma gen_uses_wf_extend [simp]:
  "gen_uses (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = gen_wf_uses gen_cfg_wf"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs gen_wf_uses_def)

lemma gen_ssa_defs_wf_extend [simp]:
  "gen_ssa_defs (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = d"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs)

lemma gen_ssa_uses_wf_extend [simp]:
  "gen_ssa_uses (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = u"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs)

lemma gen_phis_wf_extend [simp]:
  "gen_phis (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = p"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs)

lemma gen_var_wf_extend [simp]:
  "gen_var (gen_cfg_wf_extend gen_cfg_wf \<lparr>gen_ssa_defs = d, gen_ssa_uses = u, gen_phis = p, gen_var = v\<rparr>)
  = v"
  by (simp add: gen_cfg_wf_extend_def gen_cfg.defs)

lemma CFG_SSA_Transformed_codeI:
  assumes "CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges Entry oldDefs oldUses defs (\<lambda>g. lookup_multimap (uses g)) (\<lambda>g. Mapping.lookup (phis g)) var"
  and "\<And>g. Mapping.keys (uses g) \<subseteq> set (\<alpha>n g)"
  shows "CFG_SSA_Transformed_code \<alpha>e \<alpha>n invar inEdges Entry oldDefs oldUses defs uses phis var"
proof -
  interpret CFG_SSA_Transformed \<alpha>e \<alpha>n invar inEdges Entry oldDefs oldUses "defs" "\<lambda>g. lookup_multimap (uses g)" "\<lambda>g. Mapping.lookup (phis g)" var
    by fact
  have [simp]: "usesOf = lookup_multimap"
    by (intro ext) (clarsimp simp: lookup_multimap_def)
  from assms
  show ?thesis
  apply unfold_locales
                   apply (auto intro!: defs_uses_disjoint)[1]
                  apply (rule defs_finite)
                 apply (rule uses_in_\<alpha>n)
                 apply simp
                apply (clarsimp split: option.splits)
               apply (rule invar)
              apply (rule phis_finite)
             apply (rule phis_in_\<alpha>n; simp)
            apply (rule phis_wf; simp)
           apply (rule simpleDefs_phiDefs_disjoint; simp)
          apply (rule allDefs_disjoint; simp)
         apply (rule allUses_def_ass; simp add: comp_def)
        apply (rule Entry_no_phis)
       apply (rule oldDefs_def)
      apply (auto intro!: oldUses_def)[1]
     apply (rule conventional; simp add: comp_def)
    apply (rule phis_same_var; simp)
   apply (rule allDefs_var_disjoint; simp)
  by auto
qed

lemma CFG_SSA_Transformed_ign:
  "CFG_SSA_Transformed (ign gen_wf_\<alpha>e gen_cfg_wf) (ign gen_wf_\<alpha>n gen_cfg_wf) gen_wf_invar
        (const (gen_wf_inEdges' gen_cfg_wf)) (ign gen_wf_Entry gen_cfg_wf) (ign gen_wf_defs gen_cfg_wf)
        (ign gen_wf_uses gen_cfg_wf) (ign gen_wf_defs' gen_cfg_wf) (ign gen_wf.uses' gen_cfg_wf)
        (ign gen_wf.phis' gen_cfg_wf)
        (ign gen_wf_var gen_cfg_wf)"
unfolding CFG_SSA_Transformed_def CFG_wf_def CFG_def CFG_wf_axioms_def
  graph_Entry_def graph_path_def graph_Entry_axioms_def
  CFG_axioms_def CFG_SSA_wf_def CFG_SSA_def CFG_SSA_axioms_def
  CFG_SSA_wf_axioms_def CFG_SSA_Transformed_axioms_def
  graph_def graph_nodes_it_def graph_pred_it_def
  graph_nodes_it_axioms_def graph_pred_it_axioms_def
apply (clarsimp simp: gen_wf.Entry_unreachable gen_wf.defs_uses_disjoint [where g=gen_cfg_wf]
  gen_wf.uses_in_\<alpha>n
  gen_wf.braun_ssa.uses_in_\<alpha>n gen_wf.phis'_finite
  gen_wf.\<alpha>n_distinct
  gen_wf.valid gen_wf.finite [simplified]
  gen_wf.ni.nodes_list_it_correct [simplified]
  gen_wf.pi.pred_list_it_correct [simplified])
apply (intro conjI)
               using gen_wf.Entry_unreachable [of gen_cfg_wf]
               apply (auto simp: graph_path_base.inEdges_def)[1]
              using gen_wf.Entry_reaches
              apply (fastforce cong del: imp_cong simp: graph_path_base.path2_def graph_path_base.path_def graph_path_base.predecessors_def graph_path_base.inEdges_def)[1]
             using gen_wf.def_ass_uses [of gen_cfg_wf]
             apply (auto simp: CFG_base.defAss'_def graph_path_base.path2_def graph_path_base.path_def graph_path_base.predecessors_def graph_path_base.inEdges_def)[1]
            using gen_wf.Entry_unreachable [of gen_cfg_wf]
            apply (auto simp: graph_path_base.inEdges_def)[1]
           using gen_wf.Entry_reaches
           apply (fastforce cong del: imp_cong simp: graph_path_base.path2_def graph_path_base.path_def graph_path_base.predecessors_def gen_wf.defs_uses_disjoint graph_path_base.inEdges_def)[1]
          apply (auto dest: gen_wf.defs'_uses'_disjoint [where g=gen_cfg_wf])[1]
         apply (auto dest: gen_wf.braun_ssa.phis_in_\<alpha>n)[1]
        apply (auto dest: gen_wf.phis'_wf simp: graph_path_base.predecessors_def gen_wf_predecessors_def graph_path_base.inEdges_def)[1]
       apply (fastforce dest: gen_wf.braun_ssa.simpleDefs_phiDefs_disjoint simp: CFG_SSA_base.phiDefs_def dom_def)[1]
      using gen_wf.braun_ssa.allDefs_disjoint[where g=gen_cfg_wf]
      apply (clarsimp simp: CFG_SSA_base.CFG_SSA_defs)
     apply clarsimp
     apply (drule gen_wf.braun_ssa.allUses_def_ass [where g=gen_cfg_wf, rotated 1])
      apply (auto simp: CFG_SSA_wf_base.CFG_SSA_wf_defs CFG_SSA_wf_base.defAssUses_def
        graph_path_base.path2_def graph_path_base.path_def graph_path_base.predecessors_def
        graph_path_base.successors_def graph_path_base.inEdges_def)[2]
    apply (clarsimp simp: gen_wf.oldDefs_correct)
   apply (clarsimp simp: gen_wf.oldUses_correct)
  apply (intro allI impI gen_wf.conventional; auto simp: graph_path_base.path2_def graph_path_base.path_def graph_path_base.predecessors_def graph_path_base.successors_def CFG_SSA_base.CFG_SSA_defs graph_path_base.inEdges_def)
 apply (intro allI impI gen_wf.phis'_fst; assumption)
by (intro allI impI gen_wf.allDefs_var_disjoint; auto simp: CFG_SSA_base.CFG_SSA_defs)

lift_definition gen_ssa_cfg_wf :: "('node::linorder, 'var::linorder, 'edge) gen_cfg_wf \<Rightarrow> ('node, 'var, 'edge , ('node,'var) ssaVal) gen_ssa_cfg_wf"
  is "\<lambda>g. let (uses,phis) = gen_wf_uses'_phis' g in (gen_cfg_wf_extend g)\<lparr>
    gen_ssa_defs = gen_wf_defs' g,
    gen_ssa_uses = uses,
    gen_phis = phis,
    gen_var = gen_wf_var g
  \<rparr>"
apply (simp add: Let_def gen_wf_uses'_phis'_def split_beta)
apply (subst CFG_Construct_linorder.snd_uses'_phis'[symmetric, of gen_wf_\<alpha>e _ gen_wf_invar _ gen_wf_Entry])
 apply unfold_locales[1]
apply (rule CFG_SSA_Transformed_codeI)
 apply (subst CFG_Construct_linorder.fst_uses'_phis'[symmetric, of gen_wf_\<alpha>e _ gen_wf_invar _ gen_wf_Entry])
  apply unfold_locales[1]
 apply transfer
 apply (rule CFG_SSA_Transformed_ign)
apply (rule CFG_Construct_linorder.fst_uses'_phis'_in_\<alpha>n)
by unfold_locales

declare uninst.defNode_code[abs_def, code] uninst.allVars_code[abs_def, code] uninst.allUses_def[abs_def, code] uninst.allDefs_def[abs_def, code]
  uninst.phiUses_code[abs_def, code] uninst.phi_def[abs_def, code] uninst.redundant_code_def[abs_def, code]
declare uninst_code.uses'_code_def[abs_def, code] uninst_code.substNext_code_def[abs_def, code] uninst_code.substitution_code_def[abs_def, folded uninst_phi_def, code]
declare uninst_code.phis'_code_def[folded uninst_code_substNext_def, code] uninst_code.step_code_def[folded uninst_code.uses'_code_def uninst_code.phis'_code_def, code]
  uninst_code.cond_code_def[folded uninst_redundant_def, code]
declare gen_ssa_wf_notriv.substAll_efficient_def
  [folded uninst_code_nodes_of_phis'_def uninst_code_nodes_of_uses'_def uninst_code_triv_phis'_def
    uninst_code_substitution_def
    uninst_code_step_code_def uninst_code_phis'_def uninst_code_uses'_def uninst_trivial_phis_def
    uninst_phidefNodes_def uninst_useNodes_of_def uninst_phiNodes_of_def, code]
declare keys_dom_lookup [symmetric, code_unfold]

definition "map_keys_from_sparse \<equiv> map_keys gen_wf.from_sparse"

declare map_keys_code[OF gen_wf.from_sparse_inj, folded map_keys_from_sparse_def, code]
declare map_keys_from_sparse_def[symmetric, code_unfold]

lemma fold_Cons_commute: "(\<And>a b. \<lbrakk>a \<in> set (x # xs); b \<in> set (x # xs)\<rbrakk> \<Longrightarrow> f a \<circ> f b = f b \<circ> f a)
  \<Longrightarrow> fold f (x # xs) = f x \<circ> (fold f xs)"
  by (simp add: fold_commute)

lemma Union_of_code [code]: "Union_of f (RBT_Set.Set r) = RBT.fold (\<lambda>a _. (\<union>) (f a)) r {}"
proof -
  { fix xs
    have "(\<Union>x\<in>{x. (x, ()) \<in> set xs}. f x) = fold (\<lambda>(a,_). (\<union>) (f a)) xs {}"
      apply (induction xs)
       apply simp
      by (subst fold_Cons_commute) auto
  }
  note Union_fold = this
  show ?thesis
    unfolding Union_of_def
    by (clarsimp simp: RBT_Set.Set_def RBT.fold_fold RBT.lookup_in_tree) (rule Union_fold [simplified])
qed

definition[code]: "disjoint xs ys = (xs \<inter> ys = {})"

definition "gen_ssa_wf_notriv_substAll' = fst \<circ> gen_ssa_wf_notriv_substAll_efficient"

definition "fold_set f A \<equiv> fold f (sorted_list_of_set A)"
declare fold_set_def [symmetric, code_unfold]
declare fold_set_def
  [where A="RBT_Set.Set r" for r,
    unfolded sorted_list_set fold_keys_def_alt [symmetric,abs_def] fold_keys_def [abs_def],
    code]

declare graph_path_base.inEdges_def [code]

end
