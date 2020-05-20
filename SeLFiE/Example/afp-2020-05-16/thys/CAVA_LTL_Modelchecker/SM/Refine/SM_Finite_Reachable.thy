theory SM_Finite_Reachable
imports Type_System
begin

(* TODO: Move to Misc, near lists_of_len_fin1 - lemma *)
lemma lists_le_len_fin: "finite P \<Longrightarrow> finite (lists P \<inter> { l. length l \<le> n })"
proof (induct n)
  case 0 thus ?case by auto
next
  case (Suc n)
  have "lists P \<inter> { l. length l \<le> Suc n } 
        = (lists P \<inter> {l. length l \<le> n}) 
        \<union> (\<lambda>(a,l). a#l) ` (P \<times> (lists P \<inter> {l. length l \<le> n}))"
    apply auto
    apply (case_tac x)
    apply auto
    done
  moreover from Suc have "finite \<dots>" by auto
  ultimately show ?case by simp
qed

lemma obtain_list_of_multiset: 
  obtains l where "mset l = m"
proof -
  have "\<exists>l. mset l = m"
    apply (induction m)
    apply auto
    apply (rule_tac x="x#l" in exI)
    apply auto
    done
  thus ?thesis using that by blast
qed

lemma finitely_many_lists_for_multiset[simp, intro!]: 
  "finite {l . mset l = m}"
proof -
  have "{l . mset l = m} \<subseteq> {l. set l \<subseteq> set_mset m \<and> length l = size m}"
    by auto
  also note finite_lists_length_eq
  finally (finite_subset) show ?thesis by auto
qed


lemma finite_size_bounded_msets:
  assumes "finite S"
  shows "finite { m . size m \<le> len \<and> set_mset m \<subseteq> S }"
proof -
  have "{ m . size m \<le> len \<and> set_mset m \<subseteq> S } 
    \<subseteq> mset`(lists S \<inter> {l. length l \<le> len})"
    apply clarsimp
    apply (rule_tac m=x in obtain_list_of_multiset)
    apply (auto intro!: imageI)
    done  
  also have "finite (mset`(lists S \<inter> {l. length l \<le> len}))"
    apply (rule finite_imageI)
    apply (rule lists_le_len_fin)
    by (rule assms)
  finally (finite_subset) show ?thesis .
qed

lemma finite_maps_to_finite_type:
  assumes "finite (D::'a set)" "finite (UNIV::'v set)" 
  shows "finite ((dom::(_ \<rightharpoonup> 'v) \<Rightarrow> _) -` Pow D)"
proof -
  {fix DD::"'a set"
    have "{x. dom x \<subseteq> DD} = \<Union>{ {x. dom x = D } | D.  D\<subseteq>DD }"  
    by auto
  } note aux2=this

  from assms show ?thesis
    apply (simp add: vimage_def)
    apply (subst aux2)
    apply (rule finite_Union)
    using [[simproc add: finite_Collect]]
    apply simp
    apply clarsimp
    apply (rule finite_set_of_finite_maps[where B="UNIV::'v set", simplified])
    apply (erule finite_subset)
    apply simp
    by simp
qed



text \<open>In the following, we prove that the set of reachable states is finite.\<close>

text \<open>Approximation of reachable CFG-states\<close>
definition "cfg_approx prog 
  \<equiv> \<Union>{approx_reachable ((proc_decl.body p)) | p. p\<in>set (program.processes prog)}"

definition "local_var_approx prog \<equiv> \<Union>{ 
  set (proc_decl.local_vars p) | p. p\<in>set (program.processes prog) }"
definition "global_var_approx prog \<equiv> set (program.global_vars prog)"

definition "lc_approx prog \<equiv> { 
  \<lparr> 
    local_config.command = c, 
    local_config.state = \<lparr> local_state.variables = v\<rparr> \<rparr> 
  | c v. c \<in> cfg_approx prog \<and> dom v \<subseteq> local_var_approx prog }"

definition "gc_approx prog \<equiv> {
  \<lparr> global_config.processes = lcs,
    global_config.state = \<lparr> global_state.variables = v \<rparr>
  \<rparr> | lcs v.
    size lcs \<le> length (program.processes prog)
  \<and> set_mset lcs \<subseteq> lc_approx prog
  \<and> dom v \<subseteq> global_var_approx prog
}"

definition "gco_approx prog \<equiv> insert None (Some`gc_approx prog)"



lemma ginit_approx: "init_gc prog\<in>gc_approx prog"
  unfolding init_gc_def gc_approx_def
  apply auto
  apply (auto simp: 
    init_pc_def lc_approx_def cfg_approx_def local_var_approx_def 
    global_var_approx_def )
  done

lemma init_approx: "gc \<in> li.init prog \<Longrightarrow> gc \<in> gco_approx prog"
  apply (cases gc)
  apply (auto simp: gco_approx_def ginit_approx li.init_conv)
  done
  
lemma cfg_approx:
  assumes "c\<in>cfg_approx prog"
  assumes "cfg c a c'"
  shows "c'\<in>cfg_approx prog"
  using assms
  unfolding cfg_approx_def
  by (auto dest: approx_reachable_closed)


lemma step_approx: 
  assumes "gc\<in>gco_approx prog" 
  assumes "(gc, gc') \<in> li.step"
  shows "gc'\<in>gco_approx prog"
  using assms
  unfolding li.step_def
  apply (cases gc, simp_all add: gco_approx_def)
  apply (auto simp: li.gstep_eq_conv elim!: stutter_extend_edgesE) []
  apply (cases gc', simp_all)
  apply (rule imageI)
  apply (auto simp: li.gstep_eq_conv elim!: stutter_extend_edgesE) []
  
  unfolding li.gstep_succ_def
  apply clarsimp
  apply (clarsimp split: sum.splits option.splits bool.splits Option.bind_splits)
  apply (clarsimp simp: gco_approx_def gc_approx_def)
  apply (case_tac bb, clarsimp_all)
  apply (frule la_ex_pres_gs_vars, clarsimp)
  apply (clarsimp simp: lc_approx_def)
  apply (case_tac ac, clarsimp_all)
  apply (frule la_ex_pres_ls_vars, clarsimp)

  apply (auto simp: cfg_approx) []
  done  
  
lemma finite_local_var_approx[simp, intro!]: "finite (local_var_approx prog)"
  using [[simproc add: finite_Collect]]
  unfolding local_var_approx_def
  apply (rule finite_Union)
  apply simp
  apply clarsimp
  done

lemma finite_global_var_approx[simp, intro!]: "finite (global_var_approx prog)"
  using [[simproc add: finite_Collect]]
  unfolding global_var_approx_def
  by simp


lemma gco_approx_finite[simp, intro!]: "finite (gco_approx prog)"  
proof -
  have aux1: "({lcs.
        size lcs
        \<le> length (program.processes prog)} \<inter>
       set_mset -` Pow (lc_approx prog)) 
    = {lcs. size lcs \<le> length (program.processes prog) \<and> set_mset lcs \<subseteq> lc_approx prog }"
    by auto

  {fix DD::"ident set"
    have "{x. dom x \<subseteq> DD} = \<Union>{ {x. dom x = D } | D.  D\<subseteq>DD }"  
    by auto
  } note aux2=this

  show ?thesis
    unfolding gco_approx_def
    apply simp
    apply (rule finite_imageI)
    unfolding gc_approx_def
    using [[simproc add: finite_Collect]]
    apply simp
    apply (rule finite_imageI)
    apply (subst aux1)
    apply (rule finite_cartesian_product)
    apply (rule finite_size_bounded_msets)
    unfolding lc_approx_def
    apply simp
    apply (rule finite_imageI)
    apply (rule finite_cartesian_product)
    unfolding cfg_approx_def
    apply (rule finite_Union)
    apply simp
    apply auto []
    apply (simp add: finite_maps_to_finite_type)
    apply (simp add: finite_maps_to_finite_type)
    done
qed

lemma sys_finite_reachable: "finite ((g_E (li.system_automaton prog))\<^sup>* ``
  g_V0 (li.system_automaton prog))"
proof -
  have "(g_E (li.system_automaton prog))\<^sup>* `` g_V0 (li.system_automaton prog) \<subseteq> gco_approx prog"
    apply safe
    apply (erule rtrancl_induct)
    apply (auto intro: step_approx init_approx)
    done
  also note gco_approx_finite
  finally (finite_subset) show ?thesis .
qed

lemma "finite ((g_E (li.system_automaton (dloc prog)))\<^sup>* ``
  g_V0 (li.system_automaton (dloc prog)))"
  by (rule sys_finite_reachable)

context well_typed_prog begin
  lemma li'_finite_reachable: "finite ((g_E li'.s2.system_automaton)\<^sup>* `` g_V0 li'.s2.system_automaton)"
  proof -
    show ?thesis
      apply (rule li'.bisim.s1.reachable_finite_sim)
      apply (rule sys_finite_reachable)
      apply (clarsimp simp: build_rel_def)
      apply (case_tac b)
      apply simp
      apply simp
      done
  qed
end

end

