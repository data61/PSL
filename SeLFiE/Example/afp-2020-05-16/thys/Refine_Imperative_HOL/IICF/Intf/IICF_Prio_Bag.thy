section \<open>Priority Bag Interface\<close>
theory IICF_Prio_Bag
imports IICF_Multiset
begin
subsection \<open>Operations\<close>
  
  text \<open>We prove quite general parametricity lemmas, but restrict 
    them to relations below identity when we register the operations.

    This restriction, although not strictly necessary, makes usage of the tool
    much simpler, as we do not need to handle different prio-functions for 
    abstract and concrete types.
  \<close>

  context
    fixes prio:: "'a \<Rightarrow> 'b::linorder"
  begin  
    definition "mop_prio_pop_min b = ASSERT (b\<noteq>{#}) \<then> SPEC (\<lambda>(v,b'). 
        v \<in># b
      \<and> b'=b - {#v#} 
      \<and> (\<forall>v'\<in>set_mset b. prio v \<le> prio v'))"

    definition "mop_prio_peek_min b \<equiv> ASSERT (b\<noteq>{#}) \<then> SPEC (\<lambda>v. 
          v \<in># b
        \<and> (\<forall>v'\<in>set_mset b. prio v \<le> prio v'))"

  end

  lemma param_mop_prio_pop_min[param]: 
    assumes [param]: "(prio',prio) \<in> A \<rightarrow> B"
    assumes [param]: "((\<le>),(\<le>)) \<in> B \<rightarrow> B \<rightarrow> bool_rel"
    shows "(mop_prio_pop_min prio',mop_prio_pop_min prio) \<in> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A \<times>\<^sub>r \<langle>A\<rangle>mset_rel\<rangle>nres_rel"
    unfolding mop_prio_pop_min_def[abs_def]
    apply (clarsimp simp: mop_prio_pop_min_def nres_rel_def pw_le_iff refine_pw_simps)
    apply (safe; simp)
  proof goal_cases
    case (1 m n x)
    (*fix m n x*)
    assume "(m,n)\<in>\<langle>A\<rangle>mset_rel"
      and "x\<in>#m"
      and P': "\<forall>x'\<in>set_mset m. prio' x \<le> prio' x'"
    hence R: "rel_mset (rel2p A) m n" by (simp add: mset_rel_def p2rel_def)
    from multi_member_split[OF \<open>x\<in>#m\<close>] obtain m' where [simp]: "m=m'+{#x#}" by auto
  
    from msed_rel_invL[OF R[simplified]] obtain n' y where 
      [simp]: "n=n'+{#y#}" and [param, simp]: "(x,y)\<in>A" and R': "(m',n')\<in>\<langle>A\<rangle>mset_rel"
      by (auto simp: rel2p_def mset_rel_def p2rel_def)
    have "\<forall>y'\<in>set_mset n. prio y \<le> prio y'"  
    proof
      fix y' assume "y'\<in>set_mset n"
      then obtain x' where [param]: "(x',y')\<in>A" and "x'\<in>set_mset m"
        using R
        by (metis insert_DiffM msed_rel_invR rel2pD union_single_eq_member)
      with P' have "prio' x \<le> prio' x'" by blast
      moreover have "(prio' x \<le> prio' x', prio y \<le> prio y') \<in> bool_rel"
        by parametricity
      ultimately show "prio y \<le> prio y'" by simp
    qed 
    thus 
      "\<exists>a. (x, a) \<in> A \<and> (m - {#x#}, n - {#a#}) \<in> \<langle>A\<rangle>mset_rel \<and> a \<in># n \<and> (\<forall>v'\<in>set_mset n. prio a \<le> prio v')"
      using R' by (auto intro!: exI[where x=n'] exI[where x=y])
  qed    

  lemma param_mop_prio_peek_min[param]: 
    assumes [param]: "(prio',prio) \<in> A \<rightarrow> B"
    assumes [param]: "((\<le>),(\<le>)) \<in> B \<rightarrow> B \<rightarrow> bool_rel"
    shows "(mop_prio_peek_min prio',mop_prio_peek_min prio) \<in> \<langle>A\<rangle>mset_rel \<rightarrow> \<langle>A\<rangle>nres_rel"
    unfolding mop_prio_peek_min_def[abs_def]
    apply (clarsimp 
      simp: mop_prio_pop_min_def nres_rel_def pw_le_iff refine_pw_simps
      )
    apply (safe; simp?)
  proof -
    fix m n x
    assume "(m,n)\<in>\<langle>A\<rangle>mset_rel"
      and "x\<in>#m"
      and P': "\<forall>x'\<in>set_mset m. prio' x \<le> prio' x'"
    hence R: "rel_mset (rel2p A) m n" by (simp add: mset_rel_def p2rel_def)
    from multi_member_split[OF \<open>x\<in>#m\<close>] obtain m' where [simp]: "m=m'+{#x#}" by auto
  
    from msed_rel_invL[OF R[simplified]] obtain n' y where 
      [simp]: "n=n'+{#y#}" and [param, simp]: "(x,y)\<in>A" and R': "(m',n')\<in>\<langle>A\<rangle>mset_rel"
      by (auto simp: rel2p_def mset_rel_def p2rel_def)
  
    have "\<forall>y'\<in>set_mset n. prio y \<le> prio y'"  
    proof
      fix y' assume "y'\<in>set_mset n"
      then obtain x' where [param]: "(x',y')\<in>A" and "x'\<in>set_mset m"
        using R
        by (metis msed_rel_invR mset_contains_eq rel2pD union_mset_add_mset_left union_single_eq_member)
      with P' have "prio' x \<le> prio' x'" by blast
      moreover have "(prio' x \<le> prio' x', prio y \<le> prio y') \<in> bool_rel"
        by parametricity
      ultimately show "prio y \<le> prio y'" by simp
    qed  
    thus "\<exists>y. (x, y) \<in> A \<and> y \<in># n \<and> (\<forall>v'\<in>set_mset n. prio y \<le> prio v')"
      using R' by (auto intro!: exI[where x=y])
  qed




  context fixes prio :: "'a \<Rightarrow> 'b::linorder" and A :: "('a\<times>'a) set" begin
    sepref_decl_op (no_def,no_mop) prio_pop_min: 
      "PR_CONST (mop_prio_pop_min prio)" :: "\<langle>A\<rangle>mset_rel \<rightarrow>\<^sub>f \<langle>A \<times>\<^sub>r \<langle>A\<rangle>mset_rel\<rangle>nres_rel"
      where "IS_BELOW_ID A"
    proof goal_cases
      case 1
      hence [param]: "(prio,prio)\<in>A \<rightarrow> Id" 
        by (auto simp: IS_BELOW_ID_def)
      show ?case
        apply (rule fref_ncI)
        apply parametricity
        by auto
    qed

    sepref_decl_op (no_def,no_mop) prio_peek_min: 
      "PR_CONST (mop_prio_peek_min prio)" :: "\<langle>A\<rangle>mset_rel \<rightarrow>\<^sub>f \<langle>A\<rangle>nres_rel"
      where "IS_BELOW_ID A"
    proof goal_cases
      case 1
      hence [param]: "(prio,prio)\<in>A \<rightarrow> Id" 
        by (auto simp: IS_BELOW_ID_def)
      show ?case
        apply (rule fref_ncI)
        apply parametricity
        by auto
    qed
  end  

subsection \<open>Patterns\<close>

lemma [def_pat_rules]:
  "mop_prio_pop_min$prio \<equiv> UNPROTECT (mop_prio_pop_min prio)"
  "mop_prio_peek_min$prio \<equiv> UNPROTECT (mop_prio_peek_min prio)"
  by auto

end
