(*  Title:      SSA_Transfer_Rules.thy
    Author:     Denis Lohner
*)

subsection \<open>Locales Transfer Rules\<close>

theory SSA_Transfer_Rules imports
  SSA_CFG
  Construct_SSA_code
begin

context includes lifting_syntax
begin

lemmas weak_All_transfer1 [transfer_rule] = iffD1 [OF right_total_alt_def2]
lemma weak_All_transfer2 [transfer_rule]: "right_total R \<Longrightarrow> ((R ===> (=)) ===> (\<longrightarrow>)) All All"
  by (auto 4 4 elim: right_totalE rel_funE)

lemma weak_imp_transfer [transfer_rule]:
  "((=) ===> (=) ===> (\<longrightarrow>)) (\<longrightarrow>) (\<longrightarrow>)"
  by auto

lemma weak_conj_transfer [transfer_rule]:
  "((\<longrightarrow>) ===> (\<longrightarrow>) ===> (\<longrightarrow>)) (\<and>) (\<and>)"
  by auto

lemma graph_path_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges inEdges2"
  shows "(\<longrightarrow>) (graph_path \<alpha>e \<alpha>n invar inEdges) (graph_path \<alpha>e2 \<alpha>n2 invar2 inEdges2)"
  unfolding graph_path_def [abs_def] graph_def valid_graph_def graph_nodes_it_def graph_pred_it_def
  graph_nodes_it_axioms_def graph_pred_it_axioms_def set_iterator_def set_iterator_genord_def 
  foldri_def
  using assms(2-5)
  apply clarsimp
  apply safe
            apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+; auto)
           apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+; force)
          apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+; force)
         apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+; force)
        apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+; force)
       apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+; force)
      apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+)
      apply (erule_tac x=x in allE)+
      apply clarsimp
     apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+; force)
    apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+; force)
   apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+; force)
  apply (rule_tac y=g in right_totalE [OF assms(1)]; (erule(1) rel_funE)+; force)
  done

end


context graph_path_base begin

context includes lifting_syntax
begin

lemma inEdges_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total A"
    and [transfer_rule]: "(A ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(A ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(A ===> (=)) invar invar2"
    and [transfer_rule]: "(A ===> (=)) inEdges' inEdges2"
  shows "(A ===> (=)) inEdges (graph_path_base.inEdges inEdges2)"
proof -
  interpret gp2: graph_path_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 .
  show ?thesis
    unfolding gp2.inEdges_def [abs_def] inEdges_def [abs_def]
    by transfer_prover
qed

lemma predecessors_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total A"
    and [transfer_rule]: "(A ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(A ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(A ===> (=)) invar invar2"
    and [transfer_rule]: "(A ===> (=)) inEdges' inEdges2"
  shows "(A ===> (=)) predecessors (graph_path_base.predecessors inEdges2)"
proof -
  interpret gp2: graph_path_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 .
  show ?thesis
    unfolding gp2.predecessors_def [abs_def] predecessors_def [abs_def]
    by transfer_prover
qed

lemma successors_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total A"
    and [transfer_rule]: "(A ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(A ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(A ===> (=)) invar invar2"
    and [transfer_rule]: "(A ===> (=)) inEdges' inEdges2"
  shows "(A ===> (=)) successors (graph_path_base.successors \<alpha>n2 inEdges2)"
proof -
  interpret gp2: graph_path_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 .
  show ?thesis
    unfolding gp2.successors_def [abs_def] successors_def [abs_def]
    by transfer_prover
qed

lemma path_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total A"
    and [transfer_rule]: "(A ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(A ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(A ===> (=)) invar invar2"
    and [transfer_rule]: "(A ===> (=)) inEdges' inEdges2"
  shows "(A ===> (=)) path (graph_path_base.path \<alpha>n2 invar2 inEdges2)"
proof -
  interpret gp2: graph_path_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 .
  show ?thesis
    unfolding gp2.path_def path_def
  by transfer_prover
qed

lemma path2_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total A"
    and [transfer_rule]: "(A ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(A ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(A ===> (=)) invar invar2"
    and [transfer_rule]: "(A ===> (=)) inEdges' inEdges2"
  shows "(A ===> (=)) path2 (graph_path_base.path2 \<alpha>n2 invar2 inEdges2)"
proof -
  interpret gp2: graph_path_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 .
  show ?thesis
    unfolding gp2.path2_def [abs_def] path2_def [abs_def]
  by transfer_prover
qed

lemma weak_Ex_transfer [transfer_rule]: "(((=) ===> (\<longrightarrow>)) ===> (\<longrightarrow>)) Ex Ex"
  by (auto elim: rel_funE)

lemmas transfer_rules = inEdges_transfer predecessors_transfer successors_transfer path_transfer path2_transfer

end

end

lemma graph_Entry_transfer [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e1 \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n1 \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar1 invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges1 inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry1 Entry2"
  shows "(\<longrightarrow>) (graph_Entry \<alpha>e1 \<alpha>n1 invar1 inEdges1 Entry1) (graph_Entry \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2)"
proof -
  {
    assume a: "graph_path \<alpha>e1 \<alpha>n1 invar1 inEdges1 \<and> graph_Entry_axioms \<alpha>n1 invar1 inEdges1 Entry1"
    then interpret graph_path \<alpha>e1 \<alpha>n1 invar1 inEdges1 by simp
    have ?thesis
      unfolding graph_Entry_def [abs_def] graph_Entry_axioms_def
      by transfer_prover
  }
  thus ?thesis
    unfolding graph_Entry_def [abs_def] by simp
qed

context graph_Entry_base begin

lemma dominates_transfer [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
  shows "(G ===> (=)) dominates (graph_Entry_base.dominates \<alpha>n2 invar2 inEdges2 Entry2)"
proof -
  interpret gE2: graph_Entry_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 .
  show ?thesis
    unfolding dominates_def [abs_def] gE2.dominates_def [abs_def]
    by transfer_prover
qed

end

context graph_Entry begin

context includes lifting_syntax
begin

lemma shortestPath_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
  shows "(G ===> (=)) shortestPath (graph_Entry.shortestPath \<alpha>n2 invar2 inEdges2 Entry2)"
proof -
  interpret gE2: graph_Entry \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2
    by transfer' unfold_locales
  show ?thesis
    unfolding shortestPath_def [abs_def] gE2.shortestPath_def [abs_def]
    by transfer_prover
qed

lemma dominators_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
  shows "(G ===> (=)) dominators (graph_Entry.dominators \<alpha>n2 invar2 inEdges2 Entry2)"
proof -
  interpret gE2: graph_Entry \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2
    by transfer' unfold_locales
  show ?thesis
    unfolding dominators_def [abs_def] gE2.dominators_def [abs_def]
    by transfer_prover
qed

lemma isIdom_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
  shows "(G ===> (=)) isIdom (graph_Entry.isIdom \<alpha>n2 invar2 inEdges2 Entry2)"
proof -
  interpret gE2: graph_Entry \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2
    by transfer' unfold_locales
  show ?thesis
    unfolding isIdom_def [abs_def] gE2.isIdom_def [abs_def]
    by transfer_prover
qed

lemma idom_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
  shows "(G ===> (=)) idom (graph_Entry.idom \<alpha>n2 invar2 inEdges2 Entry2)"
proof -
  interpret gE2: graph_Entry \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2
    by transfer' unfold_locales
  show ?thesis
    unfolding idom_def [abs_def] gE2.idom_def [abs_def]
    by transfer_prover
qed

lemmas graph_Entry_transfer =
  dominates_transfer
  shortestPath_transfer
  dominators_transfer
  isIdom_transfer
  idom_transfer
end

end

lemma CFG_transfer [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e1 \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n1 \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar1 invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges1 inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry1 Entry2"
    and [transfer_rule]: "(G ===> (=)) defs1 defs2"
    and [transfer_rule]: "(G ===> (=)) uses1 uses2"
  shows "SSA_CFG.CFG \<alpha>e1 \<alpha>n1 invar1 inEdges1 Entry1 defs1 uses1
    \<longrightarrow> SSA_CFG.CFG \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2"
  unfolding SSA_CFG.CFG_def [abs_def] CFG_axioms_def [abs_def]
  by transfer_prover

context CFG_base begin

context includes lifting_syntax
begin

lemma vars_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
  shows "(G ===> (=)) vars (CFG_base.vars \<alpha>n2 uses2)"
proof -
  interpret CFG_base2: CFG_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2 .
  show ?thesis
    unfolding vars_def [abs_def] CFG_base2.vars_def [abs_def]
    by transfer_prover
qed

lemma defAss'_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
  shows "(G ===> (=)) defAss' (CFG_base.defAss' \<alpha>n2 invar2 inEdges2 Entry2 defs2)"
proof -
  interpret CFG2: CFG_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2 .
  show ?thesis
    unfolding defAss'_def [abs_def] CFG2.defAss'_def [abs_def]
    by transfer_prover
qed

lemma defAss'Uses_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
  shows "(G ===> (=)) defAss'Uses (CFG_base.defAss'Uses \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2)"
proof -
  interpret CFG2: CFG_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2 .
  show ?thesis
    unfolding defAss'Uses_def [abs_def] CFG2.defAss'Uses_def [abs_def]
    by transfer_prover
qed


lemmas CFG_transfers =
  vars_transfer
  defAss'_transfer
  defAss'Uses_transfer

end

end


context includes lifting_syntax
begin

lemma CFG_Construct_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e1 \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n1 \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar1 invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges1 inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry1 Entry2"
    and [transfer_rule]: "(G ===> (=)) defs1 defs2"
    and [transfer_rule]: "(G ===> (=)) uses1 uses2"
  shows "CFG_Construct \<alpha>e1 \<alpha>n1 invar1 inEdges1 Entry1 defs1 uses1
    \<longrightarrow> CFG_Construct \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2"
  unfolding CFG_Construct_def [abs_def] by transfer_prover

lemma CFG_Construct_linorder_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e1 \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n1 \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar1 invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges1 inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry1 Entry2"
    and [transfer_rule]: "(G ===> (=)) defs1 defs2"
    and [transfer_rule]: "(G ===> (=)) uses1 uses2"
  shows "CFG_Construct_linorder \<alpha>e1 \<alpha>n1 invar1 inEdges1 Entry1 defs1 uses1
    \<longrightarrow> CFG_Construct_linorder \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2"
proof -
  {
    assume "CFG_Construct_linorder \<alpha>e1 \<alpha>n1 invar1 inEdges1 Entry1 defs1 uses1"
    then interpret CFG_Construct_linorder \<alpha>e1 \<alpha>n1 invar1 inEdges1 Entry1 defs1 uses1 .

    have ?thesis
    unfolding CFG_Construct_linorder_def CFG_Construct_wf_def CFG_wf_def CFG_wf_axioms_def
      by transfer_prover
  }
  thus ?thesis by simp
qed

end

context CFG_Construct begin

context includes lifting_syntax
begin

lemma phiDefNodes_aux_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
  shows "(G ===> (=)) phiDefNodes_aux (CFG_Construct.phiDefNodes_aux inEdges2 defs2)"
proof -
  interpret i: CFG_Construct \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2
    by transfer' unfold_locales
  { fix g1 g2 v unvisited n
    assume "G g1 g2"
    with assms have "inEdges2 g2 = inEdges' g1" and "defs2 g2 = defs g1"
      by (auto elim: rel_funE)
    hence "phiDefNodes_aux g1 v unvisited n = CFG_Construct.phiDefNodes_aux inEdges2 defs2 g2 v unvisited n"
    apply (induction g1 v unvisited n rule: phiDefNodes_aux.induct)
    apply (subst phiDefNodes_aux.simps)
    apply (subst i.phiDefNodes_aux.simps)
    apply (subgoal_tac "i.predecessors g2 n = predecessors g n")
     prefer 2 apply (clarsimp simp: i.predecessors_def predecessors_def i.inEdges_def inEdges_def)
    by (simp cong: if_cong arg_cong2 [where f="fold (\<union>)"] map_cong)
  }
  thus ?thesis by blast
qed

lemma phiDefNodes_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
  shows "(G ===> (=)) phiDefNodes (CFG_Construct.phiDefNodes \<alpha>n2 inEdges2 defs2 uses2)"
proof -
  interpret i: CFG_Construct \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2
    by transfer' unfold_locales
  show ?thesis
    unfolding phiDefNodes_def [abs_def] i.phiDefNodes_def [abs_def]
    by transfer_prover
qed

lemma lookupDef_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
  shows "(G ===> (=)) lookupDef (CFG_Construct.lookupDef \<alpha>n2 inEdges2 defs2)"
proof -
  interpret i: CFG_Construct \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2
    by transfer' unfold_locales
  { fix g g2 n v
    assume "G g g2"
    with assms have "\<alpha>n2 g2 = \<alpha>n g" and "inEdges2 g2 = inEdges' g" and "defs2 g2 = defs g"
      by (auto elim: rel_funE)
    hence "lookupDef g n v = i.lookupDef g2 n v"
    apply (induction g n v rule: lookupDef.induct)
    apply (subst lookupDef.simps)
    apply (subst i.lookupDef.simps)
    apply (subgoal_tac "i.predecessors g2 n = predecessors g n")
     prefer 2 apply (clarsimp simp: i.predecessors_def predecessors_def i.inEdges_def inEdges_def)
    by (simp cong: if_cong list.case_cong)
  }
  thus ?thesis by blast
qed

lemma defs'_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
  shows "(G ===> (=)) defs' (CFG_Construct.defs' defs2)"
proof -
  interpret i: CFG_Construct \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2
    by transfer' unfold_locales
  show ?thesis
    unfolding defs'_def [abs_def] i.defs'_def [abs_def]
    by transfer_prover
qed

lemma uses'_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
  shows "(G ===> (=)) uses' (CFG_Construct.uses' \<alpha>n2 inEdges2 defs2 uses2)"
proof -
  interpret i: CFG_Construct \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2
    by transfer' unfold_locales
  show ?thesis
    unfolding uses'_def [abs_def] i.uses'_def [abs_def]
    by transfer_prover
qed

lemma phis'_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
  shows "(G ===> (=)) phis' (CFG_Construct.phis' \<alpha>n2 inEdges2 defs2 uses2)"
proof -
  interpret i: CFG_Construct \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2
    by transfer' unfold_locales
  show ?thesis
    unfolding phis'_def [abs_def] i.phis'_def [abs_def]
    by transfer_prover
qed

lemmas CFG_Construct_transfer_rules =
  phiDefNodes_aux_transfer
  phiDefNodes_transfer
  lookupDef_transfer
  defs'_transfer
  uses'_transfer
  phis'_transfer
end

end

context CFG_SSA_base begin

context includes lifting_syntax
begin

lemma phiDefs_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
    and [transfer_rule]: "(G ===> (=)) phis phis2"
  shows "(G ===> (=)) phiDefs (CFG_SSA_base.phiDefs phis2)"
proof -
  interpret i: CFG_SSA_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2 phis2 .
  show ?thesis
    unfolding phiDefs_def [abs_def] i.phiDefs_def [abs_def]
    by transfer_prover
qed

lemma allDefs_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs (defs2::'a \<Rightarrow> 'node \<Rightarrow> 'val set)"
    and [transfer_rule]: "(G ===> (=)) uses (uses2::'a \<Rightarrow> 'node \<Rightarrow> 'val set)"
    and [transfer_rule]: "(G ===> (=)) phis phis2"
  shows "(G ===> (=)) allDefs (CFG_SSA_base.allDefs defs2 phis2)"
proof -
  interpret i: CFG_SSA_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2 phis2 .
  show ?thesis
    unfolding allDefs_def [abs_def] i.allDefs_def [abs_def]
    by transfer_prover
qed

lemma phiUses_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
    and [transfer_rule]: "(G ===> (=)) phis phis2"
  shows "(G ===> (=)) phiUses (CFG_SSA_base.phiUses \<alpha>n2 inEdges2 phis2)"
proof -
  interpret i: CFG_SSA_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2 phis2 .
  show ?thesis
    unfolding phiUses_def [abs_def] i.phiUses_def [abs_def]
    by transfer_prover
qed

lemma allUses_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
    and [transfer_rule]: "(G ===> (=)) phis phis2"
  shows "(G ===> (=)) allUses (CFG_SSA_base.allUses \<alpha>n2 inEdges2 uses2 phis2)"
proof -
  interpret i: CFG_SSA_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2 phis2 .
  show ?thesis
    unfolding allUses_def [abs_def] i.allUses_def [abs_def]
    by transfer_prover
qed

lemma allVars_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
    and [transfer_rule]: "(G ===> (=)) phis phis2"
  shows "(G ===> (=)) allVars (CFG_SSA_base.allVars \<alpha>n2 inEdges2 defs2 uses2 phis2)"
proof -
  interpret i: CFG_SSA_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2 phis2 .
  show ?thesis
    unfolding allVars_def [abs_def] i.allVars_def [abs_def]
    by transfer_prover
qed

lemma defAss_transfer [transfer_rule]:
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
    and [transfer_rule]: "(G ===> (=)) phis phis2"
  shows "(G ===> (=)) defAss (CFG_SSA_base.defAss \<alpha>n2 invar2 inEdges2 Entry2 defs2 phis2)"
proof -
  interpret i: CFG_SSA_base \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2 phis2 .
  show ?thesis
    unfolding defAss_def [abs_def] i.defAss_def [abs_def]
    by transfer_prover
qed

lemmas CFG_SSA_base_transfer_rules =
  phiDefs_transfer
  allDefs_transfer
  phiUses_transfer
  allUses_transfer
  allVars_transfer
  defAss_transfer
end

end

context CFG_SSA_base_code begin

lemma CFG_SSA_base_code_transfer_rules [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges' inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry Entry2"
    and [transfer_rule]: "(G ===> (=)) defs defs2"
    and [transfer_rule]: "(G ===> (=)) uses uses2"
    and [transfer_rule]: "(G ===> (=)) phis phis2"
  shows "(G ===> (=)) phiDefs (CFG_SSA_base.phiDefs (\<lambda>g. Mapping.lookup (phis2 g)))"
        "(G ===> (=)) allDefs (CFG_SSA_base.allDefs defs2 (\<lambda>g. Mapping.lookup (phis2 g)))"
        "(G ===> (=)) phiUses (CFG_SSA_base.phiUses \<alpha>n2 inEdges2 (\<lambda>g. Mapping.lookup (phis2 g)))"
        "(G ===> (=)) allUses (CFG_SSA_base.allUses \<alpha>n2 inEdges2 (usesOf \<circ> uses2) (\<lambda>g. Mapping.lookup (phis2 g)))"
        "(G ===> (=)) defAss (CFG_SSA_base.defAss \<alpha>n2 invar2 inEdges2 Entry2 defs2 (\<lambda>g. Mapping.lookup (phis2 g)))"
apply (simp add: CFG_SSA_base.CFG_SSA_defs[abs_def], transfer_prover)
   apply (simp add: CFG_SSA_base.CFG_SSA_defs[abs_def], transfer_prover)
  apply (simp add: CFG_SSA_base.CFG_SSA_defs[abs_def], transfer_prover)
 apply (simp add: CFG_SSA_base.CFG_SSA_defs[abs_def], transfer_prover)
apply (simp add: CFG_SSA_base.CFG_SSA_defs[abs_def], transfer_prover)
done

end

lemma CFG_SSA_transfer [transfer_rule]:
  includes lifting_syntax
  assumes [transfer_rule]: "right_total G"
    and [transfer_rule]: "(G ===> (=)) \<alpha>e1 \<alpha>e2"
    and [transfer_rule]: "(G ===> (=)) \<alpha>n1 \<alpha>n2"
    and [transfer_rule]: "(G ===> (=)) invar1 invar2"
    and [transfer_rule]: "(G ===> (=)) inEdges1 inEdges2"
    and [transfer_rule]: "(G ===> (=)) Entry1 Entry2"
    and [transfer_rule]: "(G ===> (=)) defs1 defs2"
    and [transfer_rule]: "(G ===> (=)) uses1 uses2"
    and [transfer_rule]: "(G ===> (=)) phis1 phis2"
  shows "CFG_SSA  \<alpha>e1 \<alpha>n1 invar1 inEdges1 Entry1 defs1 uses1 phis1
    \<longrightarrow> CFG_SSA  \<alpha>e2 \<alpha>n2 invar2 inEdges2 Entry2 defs2 uses2 phis2"
proof -
  {
    assume "CFG_SSA \<alpha>e1 \<alpha>n1 invar1 inEdges1 Entry1 defs1 uses1 phis1"
    then interpret CFG_SSA \<alpha>e1 \<alpha>n1 invar1 inEdges1 Entry1 defs1 uses1 phis1 .

    have ?thesis
    unfolding CFG_SSA_def [abs_def] CFG_SSA_axioms_def
      by transfer_prover
  }
  thus ?thesis by simp
qed

end
