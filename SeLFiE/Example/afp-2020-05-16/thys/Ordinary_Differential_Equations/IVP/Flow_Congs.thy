theory Flow_Congs
  imports Reachability_Analysis
begin

lemma lipschitz_on_congI:
  assumes "L'-lipschitz_on s' g'"
  assumes "s' = s"
  assumes "L' \<le> L"
  assumes "\<And>x y. x \<in> s \<Longrightarrow> g' x = g x"
  shows "L-lipschitz_on s g"
  using assms
  by (auto simp: lipschitz_on_def intro!: order_trans[OF _ mult_right_mono[OF \<open>L' \<le> L\<close>]])

lemma local_lipschitz_congI:
  assumes "local_lipschitz s' t' g'"
  assumes "s' = s"
  assumes "t' = t"
  assumes "\<And>x y. x \<in> s \<Longrightarrow> y \<in> t \<Longrightarrow> g' x y = g x y"
  shows "local_lipschitz s t g"
proof -
  from assms have "local_lipschitz s t g'"
    by (auto simp: local_lipschitz_def)
  then show ?thesis
    apply (auto simp: local_lipschitz_def)
    apply (drule_tac bspec, assumption)
    apply (drule_tac bspec, assumption)
    apply auto
    subgoal for x y u L
    apply (rule exI[where x=u])
      apply (auto intro!: exI[where x=L])
      apply (drule bspec)
      apply simp
      apply (rule lipschitz_on_congI, assumption, rule refl, rule order_refl)
      using assms
      apply (auto)
      done
    done
qed

context ll_on_open_it\<comment> \<open>TODO: do this more generically for @{const ll_on_open_it}\<close>
begin

context fixes S Y g assumes cong: "X = Y" "T = S" "\<And>x t. x \<in> Y \<Longrightarrow> t \<in> S \<Longrightarrow> f t x = g t x"
begin

lemma ll_on_open_congI: "ll_on_open S g Y"
proof -
  interpret Y: ll_on_open_it S f Y t0
    apply (subst cong(1)[symmetric])
    apply (subst cong(2)[symmetric])
    by unfold_locales
  show ?thesis
    apply standard
    subgoal
      using local_lipschitz
      apply (rule local_lipschitz_congI)
      using cong by simp_all
    subgoal apply (subst continuous_on_cong) prefer 3 apply (rule cont)
      using cong by (auto)
    subgoal using open_domain by (auto simp: cong)
    subgoal using open_domain by (auto simp: cong)
    done
qed

lemma existence_ivl_subsetI:
  assumes t: "t \<in> existence_ivl t0 x0"
  shows "t \<in> ll_on_open.existence_ivl S g Y t0 x0"
proof -
  from assms have \<open>t0 \<in> T\<close> "x0 \<in> X"
    by (rule mem_existence_ivl_iv_defined)+
  interpret Y: ll_on_open S g Y by (rule ll_on_open_congI)
  have "(flow t0 x0 solves_ode f) (existence_ivl t0 x0) X"
    by (rule flow_solves_ode) (auto simp: \<open>x0 \<in> X\<close> \<open>t0 \<in> T\<close>)
  then have "(flow t0 x0 solves_ode f) {t0--t} X"
    by (rule solves_ode_on_subset)
     (auto simp add: t local.closed_segment_subset_existence_ivl)
  then have "(flow t0 x0 solves_ode g) {t0--t} Y"
    apply (rule solves_ode_congI)
       apply (auto intro!: assms cong)
    using \<open>(flow t0 x0 solves_ode f) {t0--t} X\<close> local.cong(1) solves_ode_domainD apply blast
    using \<open>t0 \<in> T\<close> assms closed_segment_subset_domainI general.mem_existence_ivl_subset local.cong(2)
    by blast
  then show ?thesis
    apply (rule Y.existence_ivl_maximal_segment)
    subgoal by (simp add: \<open>t0 \<in> T\<close> \<open>x0 \<in> X\<close>)
    apply (subst cong[symmetric])
    using \<open>t0 \<in> T\<close> assms closed_segment_subset_domainI general.mem_existence_ivl_subset local.cong(2)
    by blast
qed

lemma existence_ivl_cong:
  shows "existence_ivl t0 x0 = ll_on_open.existence_ivl S g Y t0 x0"
proof -
  interpret Y: ll_on_open S g Y by (rule ll_on_open_congI)
  show ?thesis
    apply (auto )
    subgoal by (rule existence_ivl_subsetI)
    subgoal
      apply (rule Y.existence_ivl_subsetI)
      using cong
      by auto
    done
qed

lemma flow_cong:
  assumes "t \<in> existence_ivl t0 x0"
  shows "flow t0 x0 t = ll_on_open.flow S g Y t0 x0 t"
proof -
  interpret Y: ll_on_open S g Y by (rule ll_on_open_congI)
  from assms have "t0 \<in> T" "x0 \<in> X"
    by (rule mem_existence_ivl_iv_defined)+
  from cong \<open>x0 \<in> X\<close> have "x0 \<in> Y" by auto
  from cong \<open>t0 \<in> T\<close> have "t0 \<in> S" by auto
  show ?thesis
    apply (rule Y.equals_flowI[where T'="existence_ivl t0 x0"])
    subgoal using \<open>t0 \<in> T\<close> \<open>x0 \<in> X\<close>  by auto
    subgoal using \<open>x0 \<in> X\<close> by auto
    subgoal by (auto simp: existence_ivl_cong \<open>x0 \<in> X\<close>)
    subgoal
      apply (rule solves_ode_congI)
          apply (rule flow_solves_ode[OF \<open>t0 \<in> T\<close> \<open>x0 \<in> X\<close>])
      using existence_ivl_subset[of x0]
      by (auto simp: cong(2)[symmetric] cong(1)[symmetric] assms flow_in_domain intro!: cong)
    subgoal using \<open>t0 \<in> S\<close> \<open>t0 \<in> T\<close> \<open>x0 \<in> X\<close> \<open>x0 \<in> Y\<close>
      by (auto simp:)
    subgoal by fact
    done
qed

end

end

context auto_ll_on_open begin

context fixes Y g assumes cong: "X = Y" "\<And>x t. x \<in> Y \<Longrightarrow> f x = g x"
begin

lemma auto_ll_on_open_congI: "auto_ll_on_open g Y"
  apply unfold_locales
  subgoal
    using local_lipschitz
    apply (rule local_lipschitz_congI)
    using cong by auto
  subgoal
    using open_domain
    using cong by auto
  done

lemma existence_ivl0_cong:
  shows "existence_ivl0 x0 = auto_ll_on_open.existence_ivl0 g Y x0"
proof -
  interpret Y: auto_ll_on_open g Y by (rule auto_ll_on_open_congI)
  show ?thesis
    unfolding Y.existence_ivl0_def
    apply (rule existence_ivl_cong)
    using cong by auto
qed

lemma flow0_cong:
  assumes "t \<in> existence_ivl0 x0"
  shows "flow0 x0 t = auto_ll_on_open.flow0 g Y x0 t"
proof -
  interpret Y: auto_ll_on_open g Y by (rule auto_ll_on_open_congI)
  show ?thesis
    unfolding Y.flow0_def
    apply (rule flow_cong)
    using cong assms by auto
qed

end

end


context c1_on_open_euclidean begin

context fixes Y g assumes cong: "X = Y" "\<And>x t. x \<in> Y \<Longrightarrow> f x = g x"
begin

lemma f'_cong: "(g has_derivative blinfun_apply (f' x)) (at x)" if "x \<in> Y"
proof -
  from derivative_rhs[of x] that cong
  have "(f has_derivative blinfun_apply (f' x)) (at x within Y)"
    by (auto intro!: has_derivative_at_withinI)
  then have "(g has_derivative blinfun_apply (f' x)) (at x within Y)"
    by (rule has_derivative_transform_within[OF _ zero_less_one that])
       (auto simp: cong)
  then show ?thesis
    using at_within_open[OF that] cong open_dom
    by (auto simp: )
qed

lemma c1_on_open_euclidean_congI: "c1_on_open_euclidean g f' Y"
proof -
  interpret Y: c1_on_open_euclidean f f' Y unfolding cong[symmetric] by unfold_locales
  show ?thesis
    apply standard
    subgoal using cong by simp
    subgoal by (rule f'_cong)
    subgoal by (simp add: cong[symmetric] continuous_derivative)
    done
qed

lemma vareq_cong: "vareq x0 t = c1_on_open_euclidean.vareq g f' Y x0 t"
  if "t \<in> existence_ivl0 x0"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    unfolding vareq_def Y.vareq_def
    apply (rule arg_cong[where f=f'])
    apply (rule flow0_cong)
    using cong that by auto
qed

lemma Dflow_cong:
  assumes "t \<in> existence_ivl0 x0"
  shows "Dflow x0 t = c1_on_open_euclidean.Dflow g f' Y x0 t"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  from assms have "x0 \<in> X"
    by (rule mem_existence_ivl_iv_defined)
  from cong \<open>x0 \<in> X\<close> have "x0 \<in> Y" by auto
  show ?thesis
    unfolding Dflow_def Y.Dflow_def
    apply (rule mvar.equals_flowI[symmetric, OF _ _ order_refl])
    subgoal using \<open>x0 \<in> X\<close> by auto
    subgoal using \<open>x0 \<in> X\<close> by auto
    subgoal
      apply (rule solves_ode_congI)
          apply (rule Y.mvar.flow_solves_ode)
           prefer 3 apply (rule refl)
      subgoal using \<open>x0 \<in> X\<close> \<open>x0 \<in> Y\<close> by auto
      subgoal using \<open>x0 \<in> X\<close> \<open>x0 \<in> Y\<close> by auto
      subgoal for t
        apply (subst vareq_cong)
         apply (subst (asm) Y.mvar_existence_ivl_eq_existence_ivl)
        subgoal using \<open>x0 \<in> Y\<close> by simp
        subgoal
          using cong
          by (subst (asm) existence_ivl0_cong[symmetric]) auto
        subgoal using \<open>x0 \<in> Y\<close> by simp
        done
      subgoal using \<open>x0 \<in> X\<close> \<open>x0 \<in> Y\<close>
        apply (subst mvar_existence_ivl_eq_existence_ivl)
        subgoal by simp
        apply (subst Y.mvar_existence_ivl_eq_existence_ivl)
        subgoal by simp
        using cong
        by (subst existence_ivl0_cong[symmetric]) auto
      subgoal by simp
      done
    subgoal using \<open>x0 \<in> X\<close> \<open>x0 \<in> Y\<close> by auto
    subgoal
      apply (subst mvar_existence_ivl_eq_existence_ivl)
       apply auto
       apply fact+
      done
    done
qed

lemma flowsto_congI1:
  assumes "flowsto A B C D"
  shows "c1_on_open_euclidean.flowsto g f' Y A B C D"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    using assms
    unfolding flowsto_def Y.flowsto_def
    apply (auto simp: existence_ivl0_cong[OF cong]  flow0_cong[OF cong])
       apply (drule bspec, assumption)
    apply clarsimp
    apply (rule bexI)
    apply (rule conjI)
       apply assumption
    apply (subst flow0_cong[symmetric, OF cong])
     apply auto
      apply (subst existence_ivl0_cong[OF cong])
    apply auto
    apply (subst Dflow_cong[symmetric])
     apply auto
      apply (subst existence_ivl0_cong[OF cong])
    apply auto
    apply (drule bspec, assumption)
    apply (subst flow0_cong[symmetric, OF cong])
     apply auto
      apply (subst existence_ivl0_cong[OF cong])
    apply auto defer
    apply (subst Dflow_cong[symmetric])
     apply auto
      apply (subst existence_ivl0_cong[OF cong])
    apply auto
    apply (drule Y.closed_segment_subset_existence_ivl)
    by (auto simp: open_segment_eq_real_ivl closed_segment_eq_real_ivl split: if_splits)
qed

lemma flowsto_congI2:
  assumes "c1_on_open_euclidean.flowsto g f' Y A B C D"
  shows "flowsto A B C D"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    apply (rule Y.flowsto_congI1)
    using assms
    by (auto simp: cong)
qed

lemma flowsto_congI: "flowsto A B C D = c1_on_open_euclidean.flowsto g f' Y A B C D"
  using flowsto_congI1[of A B C D] flowsto_congI2[of A B C D] by auto

lemma
  returns_to_congI1:
  assumes "returns_to A x"
  shows "auto_ll_on_open.returns_to g Y A x"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  from assms obtain t where t:
    "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> A"
    "0 < t" "t \<in> existence_ivl0 x" "flow0 x t \<in> A"
    by (auto simp: returns_to_def)

  note t(1)
  moreover
  have "\<forall>\<^sub>F s in at_right 0. s < t"
    using tendsto_ident_at \<open>0 < t\<close>
    by (rule order_tendstoD)
  moreover have "\<forall>\<^sub>F s in at_right 0. 0 < s"
    by (auto simp: eventually_at_topological)
  ultimately have "\<forall>\<^sub>F t in at_right 0. Y.flow0 x t \<notin> A"
    apply eventually_elim
    using ivl_subset_existence_ivl[OF \<open>t \<in> _\<close>]
    apply (subst (asm) flow0_cong[OF cong])
    by (auto simp: )

  moreover have "\<exists>t>0. t \<in> Y.existence_ivl0 x \<and> Y.flow0 x t \<in> A"
    using t
    by (auto intro!: exI[where x=t] simp: flow0_cong[OF cong] existence_ivl0_cong[OF cong])
  ultimately show ?thesis
    by (auto simp: Y.returns_to_def)
qed

lemma
  returns_to_congI2:
  assumes "auto_ll_on_open.returns_to g Y x A"
  shows "returns_to x A"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    by (rule Y.returns_to_congI1) (auto simp: assms cong)
qed

lemma returns_to_cong: "auto_ll_on_open.returns_to g Y A x = returns_to A x"
  using returns_to_congI1 returns_to_congI2 by blast

lemma
  return_time_cong:
  shows "return_time A x = auto_ll_on_open.return_time g Y A x"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  have P_eq: "0 < t \<and> t \<in> existence_ivl0 x \<and> flow0 x t \<in> A \<and> (\<forall>s\<in>{0<..<t}. flow0 x s \<notin> A) \<longleftrightarrow>
    0 < t \<and> t \<in> Y.existence_ivl0 x \<and> Y.flow0 x t \<in> A \<and> (\<forall>s\<in>{0<..<t}. Y.flow0 x s \<notin> A)"
    for t
    using ivl_subset_existence_ivl[of t x]
    apply (auto simp: existence_ivl0_cong[OF cong] flow0_cong[OF cong])
     apply (drule bspec)
      apply force
     apply (subst (asm) flow0_cong[OF cong])
    apply auto
    apply (auto simp: existence_ivl0_cong[OF cong, symmetric] flow0_cong[OF cong])
     apply (subst (asm) flow0_cong[OF cong])
    apply auto
    done
  show ?thesis
    unfolding return_time_def Y.return_time_def
    by (auto simp: returns_to_cong P_eq)
qed

lemma poincare_mapsto_congI1:
  assumes "poincare_mapsto A B C D E" "closed A"
  shows "c1_on_open_euclidean.poincare_mapsto g Y A B C D E"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    using assms
    unfolding poincare_mapsto_def Y.poincare_mapsto_def
    apply auto
    subgoal for a b
      by (rule returns_to_congI1) auto
    subgoal for a b
      by (subst return_time_cong[abs_def, symmetric]) auto
    subgoal for a b
      unfolding poincare_map_def Y.poincare_map_def
      apply (drule bspec, assumption)
      apply safe
      subgoal for D
        apply (auto intro!: exI[where x=D])
        subgoal premises prems
        proof -
          have "\<forall>\<^sub>F y in at a within C. returns_to A y"
            apply (rule eventually_returns_to_continuousI)
              apply fact apply fact
            apply (rule differentiable_imp_continuous_within)
            apply fact
            done
          moreover have "\<forall>\<^sub>F y in at a within C. y \<in> C"
            by (auto simp: eventually_at_filter)
          ultimately have "\<forall>\<^sub>F x' in at a within C. flow0 x' (return_time A x') = Y.flow0 x' (Y.return_time A x')"
          proof eventually_elim
            case (elim x')
            then show ?case
              apply (subst flow0_cong[OF cong, symmetric], force)
               apply (subst return_time_cong[symmetric])
              using prems
               apply (auto intro!: return_time_exivl)
              apply (subst return_time_cong[symmetric])
              apply auto
              done
          qed
          with prems(7)
          show ?thesis
            apply (rule has_derivative_transform_eventually)
            using prems
             apply (subst flow0_cong[OF cong, symmetric], force)
              apply (subst return_time_cong[symmetric])
            using prems
              apply (auto intro!: return_time_exivl)
            apply (subst return_time_cong[symmetric])
            apply auto
            done
        qed
        subgoal
          apply (subst flow0_cong[OF cong, symmetric], force)
           apply (subst return_time_cong[symmetric])
           apply (auto intro!: return_time_exivl)
          apply (subst return_time_cong[symmetric])
          apply auto
          done
        done
      done
    subgoal for a b t
      apply (drule bspec, assumption)
      apply (subst flow0_cong[OF cong, symmetric])
        apply auto
       apply (subst (asm) return_time_cong[symmetric])
       apply (rule less_return_time_imp_exivl)
          apply (rule less_imp_le, assumption)
         apply (auto simp: return_time_cong)
      done
    done
qed

lemma poincare_mapsto_congI2:
  assumes "c1_on_open_euclidean.poincare_mapsto g Y A B C D E" "closed A"
  shows "poincare_mapsto A B C D E"
proof -
  interpret Y: c1_on_open_euclidean g f' Y by (rule c1_on_open_euclidean_congI)
  show ?thesis
    apply (rule Y.poincare_mapsto_congI1)
    using assms
    by (auto simp: cong)
qed

lemma poincare_mapsto_cong: "closed A \<Longrightarrow>
    poincare_mapsto A B C D E = c1_on_open_euclidean.poincare_mapsto g Y A B C D E"
  using poincare_mapsto_congI1[of A B C] poincare_mapsto_congI2[of A B C] by auto

end

end

end