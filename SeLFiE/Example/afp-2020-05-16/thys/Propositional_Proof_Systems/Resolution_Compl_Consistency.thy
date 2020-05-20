theory Resolution_Compl_Consistency
imports Resolution Consistency CNF_Formulas CNF_Formulas_Sema
begin
 
lemma OrI2': "(\<not>P \<Longrightarrow> Q) \<Longrightarrow> P \<or> Q" by auto
    
lemma atomD: "Atom k \<in> S \<Longrightarrow> {Pos k} \<in> \<Union>(cnf ` S)" "Not (Atom k) \<in> S \<Longrightarrow> {Neg k} \<in> \<Union>(cnf ` S)" by force+
      
lemma pcp_disj: (* this is the same as for LSC \<Rightarrow> Res. but I don't want to make the proof of that too, so I'm keeping my code duplication *)
 "\<lbrakk>F \<^bold>\<or> G \<in> \<Gamma>; (\<forall>xa. (xa = F \<or> xa \<in> \<Gamma>) \<longrightarrow> is_cnf xa) \<longrightarrow> (cnf F \<union> (\<Union>x\<in>\<Gamma>. cnf x) \<turnstile> \<box>); (\<forall>xa. (xa = G \<or> xa \<in> \<Gamma>) \<longrightarrow> is_cnf xa) \<longrightarrow> (cnf G \<union> (\<Union>x\<in>\<Gamma>. cnf x) \<turnstile> \<box>); \<forall>x\<in>\<Gamma>. is_cnf x\<rbrakk>
    \<Longrightarrow> (\<Union>x\<in>\<Gamma>. cnf x) \<turnstile> \<box>"
proof goal_cases
  case 1
  from 1(1,4) have "is_cnf (F \<^bold>\<or> G)" by blast
  hence db: "is_disj F" "is_lit_plus F" "is_disj G" by(cases F; simp)+
  hence "is_cnf F \<and> is_cnf G" by(cases F; cases G; simp)
  with 1 have IH: "(\<Union>(cnf ` (F \<triangleright> \<Gamma>))) \<turnstile> \<box>" "(\<Union>(cnf ` (G \<triangleright> \<Gamma>))) \<turnstile> \<box>" by simp_all
  let ?\<Gamma> = "(\<Union>(cnf ` \<Gamma>))"
  from IH have IH_readable: "cnf F \<union> ?\<Gamma> \<turnstile> \<box>" "cnf G \<union> ?\<Gamma> \<turnstile> \<box>" by auto
  show ?case proof(cases "cnf F = {} \<or> cnf G = {}")
    case True
    hence "cnf (F \<^bold>\<or> G) = {}" by auto
    thus ?thesis using True IH by auto
  next
    case False
    then obtain S T where ST: "cnf F = {S}" "cnf G = {T}"
      using cnf_disj_ex db(1,3) (* try applying meson here. It's weird. and sledgehammer even suggests it. *) by metis
    (* hint: card S \<le> 1 *)
    hence R: "cnf (F \<^bold>\<or> G) = { S \<union> T }" by simp
    have "\<lbrakk>S\<triangleright>?\<Gamma> \<turnstile> \<box>; T\<triangleright>?\<Gamma> \<turnstile> \<box>\<rbrakk> \<Longrightarrow> S \<union> T\<triangleright> ?\<Gamma> \<turnstile> \<box>" proof -
      assume s: "S\<triangleright>?\<Gamma> \<turnstile> \<box>" and t: "T\<triangleright>?\<Gamma> \<turnstile> \<box>"
      hence s_w: "S \<triangleright> S \<union> T \<triangleright> ?\<Gamma> \<turnstile> \<box>" using Resolution_weaken by (metis insert_commute insert_is_Un)
      note Resolution_taint_assumptions[of "{T}" ?\<Gamma> "\<box>" S] t
      then obtain R where R: "S \<union> T \<triangleright> ?\<Gamma> \<turnstile> R" "R\<subseteq>S" by (auto simp: Un_commute)
      have literal_subset_sandwich: "R = \<box> \<or> R = S" if "is_lit_plus F" "cnf F = {S}" "R \<subseteq> S"
      using that by(cases F rule: is_lit_plus.cases; simp) blast+
      show ?thesis using literal_subset_sandwich[OF db(2) ST(1) R(2)] proof
        assume "R = \<box>" thus ?thesis using R(1) by blast
      next
        from Resolution_unnecessary[where T="{_}", simplified] R(1)
        have "(R \<triangleright> S \<union> T \<triangleright> ?\<Gamma> \<turnstile> \<box>) = (S \<union> T \<triangleright> ?\<Gamma> \<turnstile> \<box>)"  .
        moreover assume "R = S" 
        ultimately show ?thesis using s_w by simp
      qed
    qed
    thus ?thesis using IH ST R 1(1) by (metis UN_insert insert_absorb insert_is_Un)
  qed
qed

lemma R_consistent: "pcp {\<Gamma>|\<Gamma>. \<not>((\<forall>\<gamma> \<in> \<Gamma>. is_cnf \<gamma>) \<longrightarrow> ((\<Union>(cnf ` \<Gamma>)) \<turnstile> \<box>))}"
  unfolding pcp_def
  unfolding Ball_def
  unfolding mem_Collect_eq
  apply(intro allI impI)
  apply(erule contrapos_pp)
  apply(unfold not_ex de_Morgan_conj de_Morgan_disj not_not not_all not_imp disj_not1)
  apply(intro impI allI)
  apply(elim disjE exE conjE; intro OrI2')
          apply(unfold not_ex de_Morgan_conj de_Morgan_disj not_not not_all not_imp disj_not1 Ball_def[symmetric])
          apply safe
          apply (metis Ass Pow_bottom Pow_empty UN_I cnf.simps(3))
         apply (metis Diff_insert_absorb Resolution.simps insert_absorb singletonI sup_bot.right_neutral atomD)
        apply (simp; metis (no_types, hide_lams) UN_insert cnf.simps(5) insert_absorb is_cnf.simps(1) sup_assoc)
       apply (auto intro: pcp_disj)
  done
    
theorem Resolution_complete:
  fixes F :: "'a :: countable formula"
  shows "\<Turnstile> F \<Longrightarrow> cnf (nnf (\<^bold>\<not>F)) \<turnstile> \<box>"
proof(erule contrapos_pp)
  assume c: "\<not> (cnf (nnf (\<^bold>\<not> F)) \<turnstile> \<box>)"
  have "{cnf_form_of (nnf (\<^bold>\<not>F))} \<in> {\<Gamma> |\<Gamma>. \<not> ((\<forall>\<gamma>\<in>\<Gamma>. is_cnf \<gamma>) \<longrightarrow> \<Union> (cnf ` \<Gamma>) \<turnstile> \<box>)}"
    by(simp add: cnf_cnf[OF is_nnf_nnf] c cnf_form_of_is[OF is_nnf_nnf])
  from pcp_sat[OF R_consistent this] have "sat {cnf_form_of (nnf (\<^bold>\<not> F))}" .
  thus "\<not> \<Turnstile> F" by(simp add: sat_def cnf_form_semantics[OF is_nnf_nnf] nnf_semantics)
qed

    
end
