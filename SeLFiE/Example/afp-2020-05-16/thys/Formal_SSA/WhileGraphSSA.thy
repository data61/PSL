(*  Title:      WhileGraphSSA.thy
    Author:     Denis Lohner, Sebastian Ullrich
*)

subsubsection \<open>Instantiation for a Simple While Language\<close>

theory WhileGraphSSA imports
Generic_Interpretation
Disjoin_Transform
"HOL-Library.List_Lexorder"
"HOL-Library.Char_ord"
begin

instantiation w_node :: ord
begin

fun less_eq_w_node where
  "(_Entry_) \<le> x = True"
| "(_ n _) \<le> x = (case x of
     (_Entry_) \<Rightarrow> False
   | (_ m _) \<Rightarrow> n \<le> m
   | (_Exit_) \<Rightarrow> True)"
| "(_Exit_) \<le> x = (x = (_Exit_))"

fun less_w_node where
  "(_Entry_) < x = (x \<noteq> (_Entry_))"
| "(_ n _) < x = (case x of
     (_Entry_) \<Rightarrow> False
   | (_ m _) \<Rightarrow> n < m
   | (_Exit_) \<Rightarrow> True)"
| "(_Exit_) < x = False"

instance ..
end

instance w_node :: linorder proof
  fix x y z :: w_node

  show "x \<le> x" by (cases x) auto
  show "x \<le> y \<or> y \<le> x" by (cases x) (cases y, auto)+
  show "x < y \<longleftrightarrow> x \<le> y \<and> \<not> y \<le> x" by (cases x) (cases y, auto)+

  assume "x \<le> y" and "y \<le> z"
  thus "x \<le> z" by (cases x, cases y, cases z) auto

  assume "x \<le> y" and "y \<le> x"
  thus "x = y" by (cases x) (cases y, auto)+
qed

declare Defs.simps [simp del]
declare Uses.simps [simp del]
declare Let_def [simp]

declare finite_valid_nodes [simp, intro!]

lemma finite_valid_edge [simp, intro!]: "finite (Collect (valid_edge c))"
  unfolding valid_edge_def [abs_def]
apply (rule inj_on_finite [where f="\<lambda>(f,d,t). (f,t)" and B="Collect (valid_node c) \<times> Collect (valid_node c)"])
  apply (rule inj_onI)
  apply (auto intro: WCFG_edge_det)[1]
 apply (force simp: valid_node_def valid_edge_def)[1]
by auto

lemma uses_expr_finite: "finite (rhs_aux e)"
  by (induction e) auto

lemma uses_cmd_finite: "finite (rhs c)"
  by (induction c) (auto intro: uses_expr_finite)

lemma defs_cmd_finite: "finite (lhs c)"
  by (induction c) auto

lemma finite_labels': "finite {(l,c). labels prog l c}"
proof -
  have "{l. \<exists>c. labels prog l c} = fst ` {(l,c). labels prog l c}"
    by auto
  with finite_labels [of prog] labels_det [of prog] show ?thesis
    by (auto 4 4 intro: inj_onI dest: finite_imageD)
qed

lemma finite_Defs [simp, intro!]: "finite (Defs c n)"
  unfolding Defs.simps
apply clarsimp
apply (rule_tac B="\<Union>(lhs ` snd ` {(l,c'). labels c l c'})" in finite_subset)
 apply fastforce
apply (rule finite_Union)
 apply (rule finite_imageI)+
 apply (rule finite_labels')
by (clarsimp simp: defs_cmd_finite)

lemma finite_Uses [simp, intro!]: "finite (Uses c n)"
  unfolding Uses.simps
apply clarsimp
apply (rule_tac B="\<Union>(rhs ` snd ` {(l,c'). labels c l c'})" in finite_subset)
 apply fastforce
apply (rule finite_Union)
 apply (rule finite_imageI)+
 apply (rule finite_labels')
by (clarsimp simp: uses_cmd_finite)

definition "while_cfg_\<alpha>e c = Collect (valid_edge (transform c))"
definition "while_cfg_\<alpha>n c = sorted_list_of_set (Collect (valid_node (transform c)))"
definition "while_cfg_invar c = True"
definition "while_cfg_inEdges' c t = (SOME ls. distinct ls \<and> set ls = {(sourcenode e, kind e)| e. valid_edge (transform c) e \<and> targetnode e = t})"
definition "while_cfg_Entry c = (_Entry_)"
definition "while_cfg_defs c = (Defs (transform c))((_Entry_) := {v. \<exists>n. v \<in> Uses (transform c) n})"
definition "while_cfg_uses c = Uses (transform c)"

abbreviation "while_cfg_inEdges c t \<equiv> map (\<lambda>(f,d). (f,d,t)) (while_cfg_inEdges' c t)"

lemmas while_cfg_defs = while_cfg_\<alpha>e_def while_cfg_\<alpha>n_def
  while_cfg_invar_def while_cfg_inEdges'_def
  while_cfg_Entry_def while_cfg_defs_def
  while_cfg_uses_def

interpretation while: graph_path while_cfg_\<alpha>e while_cfg_\<alpha>n while_cfg_invar while_cfg_inEdges'
apply unfold_locales
apply (simp_all add: while_cfg_defs)
   apply (force simp: valid_node_def)[1]
  apply (force simp: valid_node_def)[1]
 apply (rule set_iterator_I)
   prefer 3 apply (simp add: foldri_def)
  apply simp
 apply simp
apply (clarsimp simp: Graph_path.pred_def)
apply (subgoal_tac "finite {(v', w). valid_edge (transform g) (v', w, v)}")
 apply (drule finite_distinct_list)
 apply clarsimp
 apply (rule_tac a=xs in someI2)
  apply simp
 apply clarsimp
 apply (metis set_iterator_foldri_correct)
apply (rule_tac f="\<lambda>(f,d,t). (f,d)" in finite_surj [OF finite_valid_edge])
by (auto intro: rev_image_eqI)

lemma right_total_const: "right_total (\<lambda>x y. x = c)"
  by (rule right_totalI) simp

lemma const_transfer: "rel_fun (\<lambda>x y. x = c) (=) f (\<lambda>_. f c)"
  by (clarsimp simp: rel_fun_def)

interpretation while_ign: graph_path "\<lambda>_. while_cfg_\<alpha>e cmd" "\<lambda>_. while_cfg_\<alpha>n cmd" "\<lambda>_. while_cfg_invar cmd" "\<lambda>_. while_cfg_inEdges' cmd"
by (rule graph_path_transfer [OF right_total_const const_transfer const_transfer const_transfer const_transfer, rule_format])
  unfold_locales

definition "gen_while_cfg g \<equiv> \<lparr>
  gen_\<alpha>e = while_cfg_\<alpha>e g,
  gen_\<alpha>n = while_cfg_\<alpha>n g,
  gen_inEdges = while_cfg_inEdges g,
  gen_Entry = while_cfg_Entry g,
  gen_defs = while_cfg_defs g ,
  gen_uses = while_cfg_uses g
\<rparr>"

lemma  while_path_graph_pathD: "While_CFG.path (transform c) n es m \<Longrightarrow> while.path2 c n (n#map targetnode es) m"
  unfolding while.path2_def
apply (induction n es m rule: While_CFG.path.induct)
 apply clarsimp
 apply (rule while.path.intros)
  apply (auto simp: while_cfg_defs valid_node_def While_CFG.valid_node_def)[1]
 apply (simp add: while_cfg_defs)
apply clarsimp
apply (rule while.path.intros)
 apply assumption
apply (clarsimp simp: while.predecessors_def)
apply (rename_tac n ed m)
apply (rule_tac x="(n,ed,m)" in image_eqI)
 apply simp
apply (clarsimp simp: while.inEdges_def)
apply (rule_tac x="(n,ed)" in image_eqI)
 apply simp
apply (clarsimp simp: while_cfg_inEdges'_def)
apply (subgoal_tac "finite {(aa, a). valid_edge (transform c) (aa, a, m)}")
 prefer 2
 apply (rule_tac f="\<lambda>(f,d,t). (f,d)" in finite_surj [OF finite_valid_edge])
 apply (auto intro: rev_image_eqI)[1]
apply (drule finite_distinct_list)
apply clarsimp
by (rule_tac a=xs in someI2; simp)

lemma Uses_Entry [simp]: "Uses c (_Entry_) = {}"
  unfolding Uses.simps by auto

lemma in_Uses_valid_node: "V \<in> Uses c n \<Longrightarrow> valid_node c n"
  by (auto dest!: label_less_num_inner_nodes less_num_nodes_edge
    simp: Uses.simps valid_node_def valid_edge_def)

lemma while_cfg_CFG_wf_impl:
  "SSA_CFG.CFG_wf (\<lambda>_. gen_\<alpha>e (gen_while_cfg cmd)) (\<lambda>_. gen_\<alpha>n (gen_while_cfg cmd))
            (\<lambda>_. while_cfg_invar cmd) (\<lambda>_. gen_inEdges' (gen_while_cfg cmd))
            (\<lambda>_. gen_Entry (gen_while_cfg cmd)) (\<lambda>_. gen_defs (gen_while_cfg cmd))
            (\<lambda>_. gen_uses (gen_while_cfg cmd))"
apply (simp add: gen_while_cfg_def o_def split_beta)
unfolding SSA_CFG.CFG_wf_def
apply (rule conjI)
apply (rule CFG_transfer [OF right_total_const const_transfer const_transfer const_transfer const_transfer const_transfer const_transfer const_transfer, rule_format])
apply unfold_locales[1]
        apply (auto simp: while_cfg_defs valid_node_def valid_edge_def intro: While_CFG.intros)[1]
       apply (clarsimp simp: while.inEdges_def)
       apply (clarsimp simp: while_cfg_defs valid_edge_def)
       apply (subgoal_tac "{(aa, a). transform g \<turnstile> aa -a\<rightarrow> (_Entry_)} = {}")
        apply clarsimp
        apply (rule_tac a="[]" in someI2; simp)
       apply auto[1]
      apply (subst(asm) while_cfg_\<alpha>n_def)
      apply simp
      apply (drule valid_node_Entry_path)
      apply clarsimp
      apply (drule while_path_graph_pathD)
      apply (auto simp: while_cfg_Entry_def)[1]
     apply (clarsimp simp: while_cfg_defs)
    apply (clarsimp simp: while_cfg_defs)
    apply (subgoal_tac "{v. \<exists>n. v \<in> Uses (transform g) n} = (\<Union>n \<in> Collect (valid_node (transform g)). Uses (transform g) n)")
     apply simp
    apply (auto dest: in_Uses_valid_node)[1]
   apply (auto dest!: label_less_num_inner_nodes less_num_nodes_edge
     simp: Uses.simps valid_node_def valid_edge_def while_cfg_defs)[1]
  apply (clarsimp simp: while_cfg_defs)
 apply (clarsimp simp: while_cfg_defs)
apply (clarsimp simp: SSA_CFG.CFG_wf_axioms_def CFG_base.defAss'_def)
apply (rule_tac x="(_Entry_)" in bexI)
 apply (auto simp: while_cfg_defs)[1]
by (auto elim: graph_path_base.path.cases simp: graph_path_base.path2_def while_cfg_Entry_def)

lift_definition gen_while_cfg_wf :: "cmd \<Rightarrow> (w_node, vname, state edge_kind) gen_cfg_wf"
  is gen_while_cfg
using while_cfg_CFG_wf_impl
  by (auto simp: gen_while_cfg_def o_def split_beta while_cfg_invar_def)

definition "build_ssa cmd = gen_ssa_wf_notriv_substAll (gen_ssa_cfg_wf (gen_while_cfg_wf cmd))"

end
