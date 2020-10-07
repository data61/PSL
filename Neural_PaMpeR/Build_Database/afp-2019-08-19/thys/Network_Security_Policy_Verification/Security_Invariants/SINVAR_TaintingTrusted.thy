theory SINVAR_TaintingTrusted
imports "../TopoS_Helper"
begin

subsection \<open>SecurityInvariant Tainting with Untainting-Feature for IFS\<close>

context
begin
  qualified datatype taints_raw = TaintsUntaints_Raw (taints_raw: "string set") (untaints_raw: "string set")

  text\<open>The @{const untaints_raw} set must be a subset of @{const taints_raw}.
        Otherwise, there can be entries in the untaints set, which do not affect anything.
        This is certainly undesirable.
        In addition, a unique default parameter cannot exist if we allow such dead entries.\<close>
  qualified typedef taints = "{ts::taints_raw. untaints_raw ts \<subseteq> taints_raw ts}"
    morphisms raw_of_taints Abs_taints
  proof
    show "TaintsUntaints_Raw {} {} \<in> {ts. untaints_raw ts \<subseteq> taints_raw ts}" by simp
  qed
  
  setup_lifting type_definition_taints
  
  lemma taints_eq_iff:
    "tsx = tsy \<longleftrightarrow> raw_of_taints tsx = raw_of_taints tsy"
    by (simp add: raw_of_taints_inject)

  definition taints :: "taints \<Rightarrow> string set" where
    "taints ts \<equiv> taints_raw (raw_of_taints ts)"
  definition untaints :: "taints \<Rightarrow> string set" where
    "untaints ts \<equiv> untaints_raw (raw_of_taints ts)"

  lemma taints_wellformedness: "untaints ts \<subseteq> taints ts"
    using raw_of_taints taints_def untaints_def by auto


  text \<open>Constructor for @{typ "taints"}:\<close>
  
  definition TaintsUntaints :: "string set \<Rightarrow> string set \<Rightarrow> taints" where
    "TaintsUntaints ts uts = Abs_taints (TaintsUntaints_Raw (ts \<union> uts) uts)"

  lemma raw_of_taints_TaintsUntaints:
    "raw_of_taints (TaintsUntaints ts uts) = (TaintsUntaints_Raw (ts \<union> uts) uts)"
    by (simp add: TaintsUntaints_def Abs_taints_inverse)

  lemma taints_TaintsUntaints[code]: "taints (TaintsUntaints ts uts) = ts \<union> uts"
    by(simp add: taints_def raw_of_taints_TaintsUntaints)
  lemma untaints_TaintsUntaints[code]: "untaints (TaintsUntaints ts uts) = uts"
    by(simp add: untaints_def raw_of_taints_TaintsUntaints)

  text\<open>The things in the first set are tainted, those in the second set are untainted.
    For example, a machine produces @{term "''foo''"}:
      @{term "TaintsUntaints {''foo''} {}"}

    For example, a machine consumes @{term "''foo''"} and @{term "''bar''"}, combines them in a 
    way that they are no longer critical and outputs @{term "''baz''"}:
      @{term "TaintsUntaints {''foo'', ''bar'', ''baz''} {''foo'', ''bar''}"}
      abbreviated: @{term "TaintsUntaints {''baz''} {''foo'', ''bar''}"}
\<close>
  lemma "TaintsUntaints {''foo'', ''bar'', ''baz''} {''foo'', ''bar''} = 
         TaintsUntaints {''baz''} {''foo'', ''bar''}"
    apply(simp add: taints_eq_iff raw_of_taints_TaintsUntaints)
    by blast
  

  qualified definition default_node_properties :: "taints"
    where  "default_node_properties \<equiv> TaintsUntaints {} {}"
  
  qualified definition sinvar :: "'v graph \<Rightarrow> ('v \<Rightarrow> taints) \<Rightarrow> bool" where
    "sinvar G nP \<equiv> \<forall> (v1,v2) \<in> edges G.
        taints (nP v1) - untaints (nP v1) \<subseteq> taints (nP v2)"
  
  text\<open>Information Flow Security\<close>
  qualified definition receiver_violation :: "bool" where "receiver_violation \<equiv> True"
  
  
  private lemma sinvar_mono: "SecurityInvariant_withOffendingFlows.sinvar_mono sinvar"
    apply(simp add: SecurityInvariant_withOffendingFlows.sinvar_mono_def sinvar_def)
    apply(clarify)
    by blast
  interpretation SecurityInvariant_preliminaries
  where sinvar = sinvar
  proof(unfold_locales, goal_cases)
    case (1 G nP)
      from 1 show ?case
      apply(frule_tac finite_distinct_list[OF wf_graph.finiteE])
      apply(erule_tac exE)
      apply(rename_tac list_edges)
      apply(rule_tac ff="list_edges" in SecurityInvariant_withOffendingFlows.mono_imp_set_offending_flows_not_empty[OF sinvar_mono])
          apply(auto simp add: sinvar_def)
      apply(auto simp add: sinvar_def SecurityInvariant_withOffendingFlows.is_offending_flows_def graph_ops)
      done
    next
    case (2 N E E' nP) thus ?case by(simp add: sinvar_def) blast
    next
    case 3 thus ?case by(fact SecurityInvariant_withOffendingFlows.sinvar_mono_imp_is_offending_flows_mono[OF sinvar_mono])
  qed
  
  
  
  text\<open>Needs the well-formedness condition that @{term "untaints otherbot \<subseteq> taints otherbot"}\<close>
  private lemma Taints_def_unique: "otherbot \<noteq> default_node_properties \<Longrightarrow>
      \<exists>G p i f. wf_graph G \<and> \<not> sinvar G p \<and> f \<in> (SecurityInvariant_withOffendingFlows.set_offending_flows sinvar G p) \<and>
         sinvar (delete_edges G f) p \<and>
          i \<in> snd ` f \<and> sinvar G (p(i := otherbot)) "
    apply(subgoal_tac "untaints otherbot \<subseteq> taints otherbot")
    prefer 2
     subgoal using taints_wellformedness by simp
    apply(simp add: default_node_properties_def)
    apply (simp add: SecurityInvariant_withOffendingFlows.set_offending_flows_def
        SecurityInvariant_withOffendingFlows.is_offending_flows_min_set_def
        SecurityInvariant_withOffendingFlows.is_offending_flows_def)
    apply (simp add:graph_ops)
    apply (simp split: prod.split_asm prod.split)
    apply(rule_tac x="\<lparr> nodes=set [vertex_1,vertex_2], edges = set [(vertex_1,vertex_2)] \<rparr>" in exI, simp)
    apply(rule conjI)
     apply(simp add: wf_graph_def; fail)
    apply(subgoal_tac "\<exists>foo. foo \<in> taints otherbot")
     prefer 2
     subgoal
     apply(case_tac otherbot, rename_tac tsraw)
     apply(simp)
     apply(subgoal_tac "taints_raw tsraw \<noteq> {}")
      prefer 2 subgoal for tsraw
      apply(case_tac tsraw)
      apply(simp add: TaintsUntaints_def)
      by fastforce
     by (simp add: Abs_taints_inverse ex_in_conv taints_def)
    apply(elim exE, rename_tac foo)
    apply(rule_tac x="(\<lambda> x. default_node_properties)
            (vertex_1 := TaintsUntaints {foo} {}, vertex_2 := default_node_properties)" in exI)
    apply(simp add: default_node_properties_def)
    apply(rule conjI)
     apply(simp add: sinvar_def taints_TaintsUntaints untaints_TaintsUntaints; fail)
    apply(rule_tac x="vertex_2" in exI)
    apply(rule_tac x="set [(vertex_1,vertex_2)]" in exI, simp)
    apply(simp add: sinvar_def taints_TaintsUntaints untaints_TaintsUntaints; fail)
    done
  
  
  
  subsubsection \<open>ENF\<close>
    private lemma Taints_ENF: "SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form
        sinvar (\<lambda>c1 c2. taints c1 - untaints c1 \<subseteq> taints c2)"
      unfolding SecurityInvariant_withOffendingFlows.sinvar_all_edges_normal_form_def sinvar_def
      by blast
    private lemma Taints_ENF_refl: "SecurityInvariant_withOffendingFlows.ENF_refl
        sinvar (\<lambda>c1 c2. taints c1 - untaints c1 \<subseteq> taints c2)"
      unfolding SecurityInvariant_withOffendingFlows.ENF_refl_def
      apply(intro conjI)
       subgoal using Taints_ENF by simp
      by auto
       
  
    qualified definition Taints_offending_set:: "'v graph \<Rightarrow> ('v \<Rightarrow> taints) \<Rightarrow> ('v \<times> 'v) set set" where
    "Taints_offending_set G nP = (if sinvar G nP then
        {}
       else 
        { {e \<in> edges G. case e of (e1,e2) \<Rightarrow> \<not> taints (nP e1) - untaints (nP e1) \<subseteq> taints (nP e2)} })"
    lemma Taints_offending_set: "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Taints_offending_set"
      by(auto simp add: fun_eq_iff
                        SecurityInvariant_withOffendingFlows.ENF_offending_set[OF Taints_ENF]
                        Taints_offending_set_def)
     
 
    interpretation Taints: SecurityInvariant_IFS sinvar default_node_properties
    rewrites "SecurityInvariant_withOffendingFlows.set_offending_flows sinvar = Taints_offending_set"
      unfolding receiver_violation_def
      unfolding default_node_properties_def
      proof(unfold_locales, goal_cases)
      case (1 G f nP)
        from 1(2) show ?case
        apply(intro ballI)
        apply(rule SecurityInvariant_withOffendingFlows.ENF_snds_refl_instance[OF Taints_ENF_refl])
          apply(simp add: sinvar_def taints_TaintsUntaints untaints_TaintsUntaints, blast)
         by(simp)+
      next
      case 2 thus ?case
        apply(elim default_uniqueness_by_counterexample_IFS)
        apply(rule Taints_def_unique)
        apply(simp_all add: default_node_properties_def)
        done
      next
      case 3 show "set_offending_flows = Taints_offending_set" by(fact Taints_offending_set)
     qed
  
  
    lemma TopoS_TaintingTrusted: "SecurityInvariant sinvar default_node_properties receiver_violation"
    unfolding receiver_violation_def by unfold_locales

end


code_datatype TaintsUntaints

value[code] "TaintsUntaints {''foo''} {''bar''}"

value[code] "taints (TaintsUntaints {''foo''} {''bar''})"

end
