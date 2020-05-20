(*
  Theory: PDF_Compiler.thy
  Authors: Manuel Eberl

  The concrete compiler that compiles a PDF expression into a target language expression
  that describes a density function on the corresponding measure space.
*)

section \<open>Concrete PDF Compiler\<close>

theory PDF_Compiler
imports PDF_Compiler_Pred PDF_Target_Density_Contexts
begin

inductive expr_has_density_cexpr :: "cdens_ctxt \<Rightarrow> expr \<Rightarrow> cexpr \<Rightarrow> bool"
      ("(1_/ \<turnstile>\<^sub>c/ (_ \<Rightarrow>/ _))" [50,0,50] 50) where
(*  edc_equiv:  "cexpr_equiv f1 f2 \<Longrightarrow> \<Gamma> \<turnstile> e : t \<Longrightarrow> is_density_expr (vs,vs',\<Gamma>,\<delta>) t f2 \<Longrightarrow>
                       (vs, vs', \<Gamma>, \<delta>)  \<turnstile>\<^sub>c e \<Rightarrow> f1 \<Longrightarrow> (vs, vs', \<Gamma>, \<delta>)  \<turnstile>\<^sub>c e \<Rightarrow> f2"*)
  edc_val:     "countable_type (val_type v) \<Longrightarrow>
                  (vs, vs', \<Gamma>, \<delta>)  \<turnstile>\<^sub>c Val v \<Rightarrow>
                      map_vars Suc (branch_prob_cexpr (vs, vs', \<Gamma>, \<delta>)) *\<^sub>c \<langle>CVar 0 =\<^sub>c CVal v\<rangle>\<^sub>c"
| edc_var:     "x \<in> set vs \<Longrightarrow> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Var x \<Rightarrow> marg_dens_cexpr \<Gamma> vs x \<delta>"
| edc_pair:    "x \<in> set vs \<Longrightarrow> y \<in> set vs \<Longrightarrow> x \<noteq> y \<Longrightarrow>
                (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c <Var x, Var y> \<Rightarrow> marg_dens2_cexpr \<Gamma> vs x y \<delta>"
| edc_fail:    "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Fail t \<Rightarrow> CReal 0"
| edc_let:     "([], vs @ vs', \<Gamma>, CReal 1) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow>
                  (shift_vars vs, map Suc vs', the (expr_type \<Gamma> e) \<cdot> \<Gamma>,
                         map_vars Suc \<delta> *\<^sub>c f) \<turnstile>\<^sub>c e' \<Rightarrow> g \<Longrightarrow>
                    (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c LET e IN e' \<Rightarrow> map_vars (\<lambda>x. x - 1) g"
| edc_rand:    "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow>
                  (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Random dst e \<Rightarrow>
                    \<integral>\<^sub>c map_vars (case_nat 0 (\<lambda>x. x + 2)) f *\<^sub>c
                           dist_dens_cexpr dst (CVar 0) (CVar 1) \<partial>dist_param_type dst"
| edc_rand_det: "randomfree e \<Longrightarrow> free_vars e \<subseteq> set vs' \<Longrightarrow>
                   (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Random dst e \<Rightarrow>
                     map_vars Suc (branch_prob_cexpr (vs, vs', \<Gamma>, \<delta>)) *\<^sub>c
                     dist_dens_cexpr dst (map_vars Suc (expr_rf_to_cexpr e)) (CVar 0)"
| edc_if_det:   "randomfree b \<Longrightarrow>
                 (vs, vs', \<Gamma>, \<delta> *\<^sub>c \<langle>expr_rf_to_cexpr b\<rangle>\<^sub>c) \<turnstile>\<^sub>c e1 \<Rightarrow> f1 \<Longrightarrow>
                 (vs, vs', \<Gamma>, \<delta> *\<^sub>c \<langle>\<not>\<^sub>c expr_rf_to_cexpr b\<rangle>\<^sub>c) \<turnstile>\<^sub>c e2 \<Rightarrow> f2 \<Longrightarrow>
                 (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c IF b THEN e1 ELSE e2 \<Rightarrow> f1 +\<^sub>c f2"
| edc_if:       "([], vs @ vs', \<Gamma>, CReal 1) \<turnstile>\<^sub>c b \<Rightarrow> f \<Longrightarrow>
                     (vs, vs', \<Gamma>, \<delta> *\<^sub>c cexpr_subst_val f TRUE) \<turnstile>\<^sub>c e1 \<Rightarrow> g1 \<Longrightarrow>
                     (vs, vs', \<Gamma>, \<delta> *\<^sub>c cexpr_subst_val f FALSE) \<turnstile>\<^sub>c e2 \<Rightarrow> g2 \<Longrightarrow>
                     (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c IF b THEN e1 ELSE e2 \<Rightarrow> g1 +\<^sub>c g2"
| edc_op_discr: "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow> \<Gamma> \<turnstile> e : t \<Longrightarrow>
                   op_type oper t = Some t' \<Longrightarrow> countable_type t' \<Longrightarrow>
                      (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c oper $$ e \<Rightarrow>
                          \<integral>\<^sub>c \<langle>(oper $$\<^sub>c (CVar 0)) =\<^sub>c CVar 1\<rangle>\<^sub>c *\<^sub>c  map_vars (case_nat 0 (\<lambda>x. x+2)) f \<partial>t"
| edc_fst:      "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow> \<Gamma> \<turnstile> e : PRODUCT t t' \<Longrightarrow>
                     (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Fst $$ e \<Rightarrow>
                        \<integral>\<^sub>c (map_vars (case_nat 0 (\<lambda>x. x + 2)) f \<circ>\<^sub>c <CVar 1, CVar 0>\<^sub>c) \<partial>t'"
| edc_snd:      "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow> \<Gamma> \<turnstile> e : PRODUCT t t' \<Longrightarrow>
                     (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Snd $$ e \<Rightarrow>
                        \<integral>\<^sub>c (map_vars (case_nat 0 (\<lambda>x. x + 2)) f \<circ>\<^sub>c <CVar 0, CVar 1>\<^sub>c) \<partial>t"
| edc_neg:      "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow>
                     (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Minus $$ e \<Rightarrow> f \<circ>\<^sub>c (\<lambda>\<^sub>cx. -\<^sub>c x)"
| edc_addc:     "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow> randomfree e' \<Longrightarrow> free_vars e' \<subseteq> set vs' \<Longrightarrow>
                     (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Add $$ <e, e'> \<Rightarrow>
                         f \<circ>\<^sub>c (\<lambda>\<^sub>cx. x -\<^sub>c map_vars Suc (expr_rf_to_cexpr e'))"
| edc_multc:    "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow> c \<noteq> 0 \<Longrightarrow>
                     (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Mult $$ <e, Val (RealVal c)> \<Rightarrow>
                         (f \<circ>\<^sub>c (\<lambda>\<^sub>cx. x *\<^sub>c CReal (inverse c))) *\<^sub>c CReal (inverse (abs c))"
| edc_add:      "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow> \<Gamma> \<turnstile> e : PRODUCT t t \<Longrightarrow>
                      (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Add $$ e \<Rightarrow>
                       \<integral>\<^sub>c (map_vars (case_nat 0 (\<lambda>x. x+2)) f \<circ>\<^sub>c (\<lambda>\<^sub>cx. <x, CVar 1 -\<^sub>c x>\<^sub>c)) \<partial>t"
| edc_inv:      "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow>
                     (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Inverse $$ e \<Rightarrow>
                         (f \<circ>\<^sub>c (\<lambda>\<^sub>cx. inverse\<^sub>c x)) *\<^sub>c (\<lambda>\<^sub>cx. (inverse\<^sub>c x) ^\<^sub>c CInt 2)"
| edc_exp:      "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow>
                     (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c Exp $$ e \<Rightarrow>
                         (\<lambda>\<^sub>cx. IF\<^sub>c CReal 0 <\<^sub>c x THEN (f \<circ>\<^sub>c ln\<^sub>c x) *\<^sub>c inverse\<^sub>c x ELSE CReal 0)"

code_pred expr_has_density_cexpr .



text \<open>Auxiliary lemmas\<close>

lemma cdens_ctxt_invar_insert:
  assumes inv: "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  assumes t : "\<Gamma> \<turnstile> e : t'"
  assumes free_vars: "free_vars e \<subseteq> set vs \<union> set vs'"
  assumes hd: "dens_ctxt_\<alpha> ([], vs @ vs', \<Gamma>, CReal 1) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr f x xa))"
  notes invar = cdens_ctxt_invarD[OF inv]
  assumes wf1: "is_density_expr ([], vs @ vs', \<Gamma>, CReal 1) t' f"
  shows "cdens_ctxt_invar (shift_vars vs) (map Suc vs') (t' \<cdot> \<Gamma>) (map_vars Suc \<delta> *\<^sub>c f)"
proof (intro cdens_ctxt_invarI)
  show t': "case_nat t' \<Gamma> \<turnstile>\<^sub>c map_vars Suc \<delta> *\<^sub>c f : REAL" using invar wf1
    by (intro cet_op[where t = "PRODUCT REAL REAL"])
       (auto intro!: cexpr_typing.intros cexpr_typing_map_vars simp: o_def dest: is_density_exprD)

  let ?vs = "shift_var_set (set vs)" and ?vs' = "Suc ` set vs'" and ?\<Gamma> = "case_nat t' \<Gamma>" and
      ?\<delta> = "insert_dens (set vs) (set vs') (\<lambda>\<sigma> x. ennreal (eval_cexpr f \<sigma> x))
                        (\<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>)))"
  interpret density_context "set vs" "set vs'" \<Gamma> "\<lambda>\<sigma>. extract_real (cexpr_sem \<sigma> \<delta>)"
    by (rule density_context_\<alpha>[OF inv])

  have dc: "density_context {} (set vs \<union> set vs') \<Gamma> (\<lambda>_. 1)"
    by (rule density_context_empty)
  hence dens: "has_parametrized_subprob_density (state_measure (set vs \<union> set vs') \<Gamma>)
                (\<lambda>\<rho>. dens_ctxt_measure ({}, set vs \<union> set vs', \<Gamma>, \<lambda>_. 1) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e))
                (stock_measure t') (\<lambda>\<sigma> x. ennreal (eval_cexpr f \<sigma> x))"
    using hd free_vars by (intro expr_has_density_sound_aux[OF _ t dc])
      (auto simp: shift_var_set_def dens_ctxt_\<alpha>_def simp: extract_real_def one_ennreal_def)
  from density_context.density_context_insert[OF density_context_\<alpha>[OF inv] this]
    have "density_context ?vs ?vs' ?\<Gamma> ?\<delta>" .
  have dc: "density_context (shift_var_set (set vs)) (Suc ` set vs') (case_nat t' \<Gamma>)
                 (\<lambda>\<sigma>. extract_real (cexpr_sem \<sigma> (map_vars Suc \<delta> *\<^sub>c f)))"
  proof (rule density_context_equiv)
    show "density_context (shift_var_set (set vs)) (Suc ` set vs') (case_nat t' \<Gamma>) ?\<delta>" by fact
    show "(\<lambda>x. ennreal (extract_real (cexpr_sem x (map_vars Suc \<delta> *\<^sub>c f))))
            \<in> borel_measurable (state_measure (?vs \<union> ?vs') ?\<Gamma>)"
      apply (rule measurable_compose[OF _ measurable_ennreal], rule measurable_compose[OF _ measurable_extract_real])
      apply (rule measurable_cexpr_sem[OF t'])
      apply (insert invar is_density_exprD[OF wf1], auto simp: shift_var_set_def)
      done
  next
    fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure (?vs \<union> ?vs') ?\<Gamma>)"
    have [simp]: "case_nat (\<sigma> 0) (\<lambda>x. \<sigma> (Suc x)) = \<sigma>" by (intro ext) (simp split: nat.split)
    from \<sigma> show "insert_dens (set vs) (set vs') (\<lambda>\<sigma> x. ennreal (eval_cexpr f \<sigma> x))
                      (\<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>))) \<sigma> =
                   ennreal (extract_real (cexpr_sem \<sigma> (map_vars Suc \<delta> *\<^sub>c f)))"
      unfolding insert_dens_def using invar is_density_exprD[OF wf1]
      apply (subst ennreal_mult'[symmetric])
      apply (erule nonneg_cexprD)
      apply (rule measurable_space[OF measurable_remove_var[where t=t']])
      apply simp
      apply (subst cexpr_sem_Mult[of ?\<Gamma> _ _ _ "?vs \<union> ?vs'"])
      apply (auto intro!: cexpr_typing_map_vars ennreal_mult'[symmetric]
                  simp: o_def shift_var_set_def eval_cexpr_def
                        cexpr_sem_map_vars remove_var_def)
      done
  qed

  from subprob_imp_subprob_cexpr[OF this]
    show "subprob_cexpr (set (shift_vars vs)) (set (map Suc vs')) (case_nat t' \<Gamma>)
                        (map_vars Suc \<delta> *\<^sub>c f)" by simp

  have "Suc -` shift_var_set (set vs \<union> set vs') = set vs \<union> set vs'"
    by (auto simp: shift_var_set_def)
  moreover have "nonneg_cexpr (shift_var_set (set vs \<union> set vs')) (case_nat t' \<Gamma>) f"
    using wf1[THEN is_density_exprD_nonneg] by simp
  ultimately show "nonneg_cexpr (set (shift_vars vs) \<union> set (map Suc vs')) (case_nat t' \<Gamma>) (map_vars Suc \<delta> *\<^sub>c f)"
    using invar is_density_exprD[OF wf1]
    by (intro nonneg_cexpr_Mult)
        (auto intro!: cexpr_typing_map_vars nonneg_cexpr_map_vars
              simp: o_def shift_var_set_def image_Un)
qed (insert invar is_density_exprD[OF wf1],
     auto simp: shift_vars_def shift_var_set_def distinct_map intro!: cexpr_typing_map_vars)

lemma cdens_ctxt_invar_insert_bool:
  assumes dens: "dens_ctxt_\<alpha> ([], vs @ vs', \<Gamma>, CReal 1) \<turnstile>\<^sub>d b \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr f \<rho> x))"
  assumes wf: "is_density_expr ([], vs @ vs', \<Gamma>, CReal 1) BOOL f"
  assumes t: "\<Gamma> \<turnstile> b : BOOL" and vars: "free_vars b \<subseteq> set vs \<union> set vs'"
  assumes invar: "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  shows "cdens_ctxt_invar vs vs' \<Gamma> (\<delta> *\<^sub>c cexpr_subst_val f (BoolVal v))"
proof (intro cdens_ctxt_invarI nonneg_cexpr_Mult nonneg_cexpr_subst_val)
  note invar' = cdens_ctxt_invarD[OF invar] and wf' = is_density_exprD[OF wf]
  show "\<Gamma> \<turnstile>\<^sub>c \<delta> *\<^sub>c cexpr_subst_val f (BoolVal v) : REAL" using invar' wf'
    by (intro cet_op[where t = "PRODUCT REAL REAL"] cet_pair cexpr_typing_subst_val) simp_all
  let ?M = "\<lambda>\<rho>. dens_ctxt_measure ({}, set vs \<union> set vs', \<Gamma>, \<lambda>_. 1) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> b)"
  have dens': "has_parametrized_subprob_density (state_measure (set vs \<union> set vs') \<Gamma>) ?M
                 (stock_measure BOOL) (\<lambda>\<sigma> v. ennreal (eval_cexpr f \<sigma> v))"
    using density_context_\<alpha>[OF invar] t vars dens unfolding dens_ctxt_\<alpha>_def
    by (intro expr_has_density_sound_aux density_context.density_context_empty)
       (auto simp: extract_real_def one_ennreal_def)
  thus nonneg: "nonneg_cexpr (shift_var_set (set vs \<union> set vs')) (case_nat BOOL \<Gamma>) f"
    using wf[THEN is_density_exprD_nonneg] by simp

  show "subprob_cexpr (set vs) (set vs') \<Gamma> (\<delta> *\<^sub>c cexpr_subst_val f (BoolVal v))"
  proof (intro subprob_cexprI)
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    let ?eval = "\<lambda>e \<sigma>. extract_real (cexpr_sem (merge (set vs) (set vs') (\<sigma>, \<rho>)) e)"
    {
      fix \<sigma> assume \<sigma> : "\<sigma> \<in> space (state_measure (set vs) \<Gamma>)"
      have A: "?eval (\<delta> *\<^sub>c cexpr_subst_val f (BoolVal v)) \<sigma> =
                  ?eval \<delta> \<sigma> * ?eval (cexpr_subst_val f (BoolVal v)) \<sigma>" using wf' invar' \<sigma> \<rho>
        by (subst cexpr_sem_Mult[where \<Gamma> = \<Gamma> and V = "set vs \<union> set vs'"])
           (auto intro: merge_in_state_measure simp: shift_var_set_def)
      have "?eval \<delta> \<sigma> \<ge> 0" using \<sigma> \<rho> invar'
        by (blast dest: nonneg_cexprD intro: merge_in_state_measure)
      moreover have "?eval (cexpr_subst_val f (BoolVal v)) \<sigma> \<ge> 0" using \<sigma> \<rho> nonneg
        by (intro nonneg_cexprD nonneg_cexpr_subst_val) (auto intro: merge_in_state_measure)
      moreover have B: "ennreal (?eval (cexpr_subst_val f (BoolVal v)) \<sigma>) =
                          ennreal (eval_cexpr f (merge (set vs) (set vs') (\<sigma>, \<rho>)) (BoolVal v))"
                          (is "_ = ?f (BoolVal v)") by (simp add: eval_cexpr_def)
      hence "ennreal (?eval (cexpr_subst_val f (BoolVal v)) \<sigma>) \<le> 1"
        using \<sigma> \<rho> dens' unfolding has_parametrized_subprob_density_def
        by (subst B, intro subprob_count_space_density_le_1[of _ _ ?f])
           (auto intro: merge_in_state_measure simp: stock_measure.simps)
      ultimately have "?eval (\<delta> *\<^sub>c cexpr_subst_val f (BoolVal v)) \<sigma> \<le> ?eval \<delta> \<sigma>"
        by (subst A, intro mult_right_le_one_le) simp_all
    }
    hence "(\<integral>\<^sup>+\<sigma>. ?eval (\<delta> *\<^sub>c cexpr_subst_val f (BoolVal v)) \<sigma> \<partial>state_measure (set vs) \<Gamma>) \<le>
              (\<integral>\<^sup>+\<sigma>. ?eval \<delta> \<sigma> \<partial>state_measure (set vs) \<Gamma>)" by (intro nn_integral_mono) (simp add: ennreal_leI)
    also have "... \<le> 1" using invar' \<rho> by (intro subprob_cexprD)
    finally show "(\<integral>\<^sup>+\<sigma>. ?eval (\<delta> *\<^sub>c cexpr_subst_val f (BoolVal v)) \<sigma> \<partial>state_measure (set vs) \<Gamma>) \<le> 1" .
  qed
qed (insert cdens_ctxt_invarD[OF invar] is_density_exprD[OF wf],
     auto simp: shift_var_set_def)

lemma space_state_measureD_shift:
  "\<sigma> \<in> space (state_measure (shift_var_set V) (case_nat t \<Gamma>)) \<Longrightarrow>
  \<exists>x \<sigma>'. x \<in> type_universe t \<and> \<sigma>' \<in> space (state_measure V \<Gamma>) \<and> \<sigma> = case_nat x \<sigma>' "
  by (intro exI[of _ "\<sigma> 0"] exI[of _ "\<sigma> \<circ> Suc"])
     (auto simp: fun_eq_iff PiE_iff space_state_measure extensional_def split: nat.split)

lemma space_state_measure_shift_iff:
  "\<sigma> \<in> space (state_measure (shift_var_set V) (case_nat t \<Gamma>)) \<longleftrightarrow>
  (\<exists>x \<sigma>'. x \<in> type_universe t \<and> \<sigma>' \<in> space (state_measure V \<Gamma>) \<and> \<sigma> = case_nat x \<sigma>')"
  by (auto dest!: space_state_measureD_shift)

lemma nonneg_cexprI_shift:
  assumes "\<And>x \<sigma>. x \<in> type_universe t \<Longrightarrow> \<sigma> \<in> space (state_measure V \<Gamma>) \<Longrightarrow>
    0 \<le> extract_real (cexpr_sem (case_nat x \<sigma>) e)"
  shows "nonneg_cexpr (shift_var_set V) (case_nat t \<Gamma>) e"
  by (auto intro!: nonneg_cexprI assms dest!: space_state_measureD_shift)

lemma nonneg_cexpr_shift_iff:
  "nonneg_cexpr (shift_var_set V) (case_nat t \<Gamma>) (map_vars Suc e) \<longleftrightarrow> nonneg_cexpr V \<Gamma> e"
  apply (auto simp: cexpr_sem_map_vars o_def nonneg_cexpr_def space_state_measure_shift_iff)
  subgoal for \<sigma>
    apply (drule bspec[of _ _ "case_nat (SOME x. x \<in> type_universe t) \<sigma>"])
    using type_universe_nonempty[of t]
    unfolding ex_in_conv[symmetric]
    apply (auto intro!: case_nat_in_state_measure intro: someI)
    done
  done

lemma case_nat_case_nat: "case_nat x n (case_nat y m i) = case_nat (case_nat x n y) (\<lambda>i'. case_nat x n (m i')) i"
  by (rule nat.case_distrib)

lemma nonneg_cexpr_shift_iff2:
  "nonneg_cexpr (shift_var_set (shift_var_set V))
    (case_nat t1 (case_nat t2 \<Gamma>)) (map_vars (case_nat 0 (\<lambda>x. Suc (Suc x))) e) \<longleftrightarrow>
    nonneg_cexpr (shift_var_set V) (case_nat t1 \<Gamma>) e"
  apply (auto simp: cexpr_sem_map_vars o_def nonneg_cexpr_def space_state_measure_shift_iff)
  subgoal for x \<sigma>
    apply (drule bspec[of _ _ "case_nat x (case_nat (SOME x. x \<in> type_universe t2) \<sigma>)"])
    using type_universe_nonempty[of t2]
    unfolding ex_in_conv[symmetric]
    apply (auto simp: case_nat_case_nat cong: nat.case_cong
                intro!: case_nat_in_state_measure  intro: someI_ex someI)
    done
  apply (erule bspec)
  subgoal for x1 x2 \<sigma>
    by (auto simp add: space_state_measure_shift_iff fun_eq_iff split: nat.split
             intro!: exI[of _ x1] exI[of _ \<sigma>])
  done

lemma nonneg_cexpr_Add:
  assumes "\<Gamma> \<turnstile>\<^sub>c e1 : REAL" "\<Gamma> \<turnstile>\<^sub>c e2 : REAL"
  assumes "free_vars e1 \<subseteq> V" "free_vars e2 \<subseteq> V"
  assumes N1: "nonneg_cexpr V \<Gamma> e1" and N2: "nonneg_cexpr V \<Gamma> e2"
  shows "nonneg_cexpr V \<Gamma> (e1 +\<^sub>c e2)"
proof (rule nonneg_cexprI)
  fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure V \<Gamma>)"
  hence "extract_real (cexpr_sem \<sigma> (e1 +\<^sub>c e2)) = extract_real (cexpr_sem \<sigma> e1) + extract_real (cexpr_sem \<sigma> e2)"
    using assms by (subst cexpr_sem_Add[of \<Gamma> _ _ _ V]) simp_all
  also have "... \<ge> 0" using \<sigma> N1 N2 by (intro add_nonneg_nonneg nonneg_cexprD)
  finally show "extract_real (cexpr_sem \<sigma> (e1 +\<^sub>c e2)) \<ge> 0" .
qed

lemma expr_has_density_cexpr_sound_aux:
  assumes "\<Gamma> \<turnstile> e : t" "(vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>c e \<Rightarrow> f" "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
          "free_vars e \<subseteq> set vs \<union> set vs'"
  shows "dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> eval_cexpr f \<and> is_density_expr (vs,vs',\<Gamma>,\<delta>) t f"
using assms(2,1,3,4)
proof (induction arbitrary: t rule: expr_has_density_cexpr.induct[split_format (complete)])
(*  case (edc_equiv f1 f2 \<Gamma> e t vs vs' \<delta> t')
  hence [simp]: "t' = t" by (auto intro!: expr_typing_unique)
  from edc_equiv have "(\<lambda>\<rho> x. ennreal (eval_cexpr f1 \<rho> x)) = (\<lambda>\<rho> x. ennreal (eval_cexpr f2 \<rho> x))"
    unfolding cexpr_equiv_def eval_cexpr_def by (intro ext) auto
  with edc_equiv show ?case unfolding dens_ctxt_\<alpha>_def by auto

next*)
  case (edc_val v vs vs' \<Gamma> \<delta>)
  from edc_val.prems have [simp]: "t = val_type v" by auto
  note invar = cdens_ctxt_invarD[OF edc_val.prems(2)]
  let ?e1 = "map_vars Suc (branch_prob_cexpr (vs, vs', \<Gamma>, \<delta>))" and ?e2 = "\<langle>CVar 0 =\<^sub>c CVal v\<rangle>\<^sub>c"
  have ctype1: "case_nat t \<Gamma> \<turnstile>\<^sub>c ?e1 : REAL" and ctype2: "case_nat t \<Gamma> \<turnstile>\<^sub>c ?e2: REAL" using invar
     by (auto intro!: cexpr_typing.intros cexpr_typing_map_vars simp: o_def)
  hence ctype: "case_nat t \<Gamma> \<turnstile>\<^sub>c ?e1 *\<^sub>c ?e2 : REAL" by (auto intro!: cexpr_typing.intros)

  {
    fix \<rho> x assume x: "x \<in> type_universe (val_type v)"
               and \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    hence "case_nat x \<rho> \<in> space (state_measure (shift_var_set (set vs')) (case_nat (val_type v) \<Gamma>))"
      by (rule case_nat_in_state_measure)
    hence "ennreal (eval_cexpr (?e1 *\<^sub>c ?e2) \<rho> x) =
             ennreal (extract_real (cexpr_sem (case_nat x \<rho>)
                 (map_vars Suc (branch_prob_cexpr (vs, vs', \<Gamma>, \<delta>))))) *
             ennreal (extract_real (RealVal (bool_to_real (x = v))))" (is "_ = ?a * ?b")
      using invar unfolding eval_cexpr_def
      apply (subst ennreal_mult''[symmetric])
      apply (simp add: bool_to_real_def)
      apply (subst cexpr_sem_Mult[of "case_nat t \<Gamma>" _ _ _ "shift_var_set (set vs')"])
      apply (insert invar ctype1 ctype2)
      apply (auto simp: shift_var_set_def)
      done
    also have "?a = branch_prob (dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>)) \<rho>"
      by (subst cexpr_sem_map_vars, subst cexpr_sem_branch_prob) (simp_all add: o_def \<rho> edc_val.prems)
    also have "?b = indicator {v} x"
      by (simp add: extract_real_def bool_to_real_def split: split_indicator)
    finally have "ennreal (eval_cexpr (?e1 *\<^sub>c ?e2) \<rho> x) =
                     branch_prob (dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>)) \<rho> * indicator {v} x" .
  } note e = this

  have meas: "(\<lambda>(\<sigma>, x). ennreal (eval_cexpr (?e1 *\<^sub>c ?e2) \<sigma> x))
                 \<in> borel_measurable (state_measure (set vs') \<Gamma> \<Otimes>\<^sub>M stock_measure (val_type v))"
    apply (subst measurable_split_conv, rule measurable_compose[OF _ measurable_ennreal])
    apply (subst measurable_split_conv[symmetric], rule measurable_eval_cexpr)
    apply (insert ctype invar, auto simp: shift_var_set_def)
    done

  have *: "Suc -` shift_var_set (set vs') = set vs'" "case_nat (val_type v) \<Gamma> \<circ> Suc = \<Gamma>"
    by (auto simp: shift_var_set_def)

  have nn: "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>)
      (map_vars Suc (branch_prob_cexpr (vs, vs', \<Gamma>, \<delta>)) *\<^sub>c \<langle>CVar 0 =\<^sub>c CVal v\<rangle>\<^sub>c)"
    using invar ctype1 ctype2
    by (fastforce intro!: nonneg_cexpr_Mult nonneg_indicator nonneg_cexpr_map_vars
                          cexpr_typing.intros nonneg_cexpr_sem_integrate_vars'
                  simp: branch_prob_cexpr_def *)

  show ?case unfolding dens_ctxt_\<alpha>_def
    apply (simp only: prod.case, intro conjI)
    apply (rule hd_AE[OF hd_val et_val AE_I2])
    apply (insert edc_val, simp_all add: e dens_ctxt_\<alpha>_def meas) [4]
    apply (intro is_density_exprI)
    using ctype
    apply simp
    apply (insert invar nn, auto simp: shift_var_set_def)
    done
next

  case (edc_var x vs vs' \<Gamma> \<delta> t)
  hence t: "t = \<Gamma> x" by auto
  note invar = cdens_ctxt_invarD[OF edc_var.prems(2)]
  from invar have ctype: "case_nat t \<Gamma> \<turnstile>\<^sub>c marg_dens_cexpr \<Gamma> vs x \<delta> : REAL" by (auto simp: t)

  show ?case unfolding dens_ctxt_\<alpha>_def
  proof (simp only: prod.case, intro conjI is_density_exprI, rule hd_AE[OF hd_var edc_var.prems(1)])
    show "case_nat t \<Gamma> \<turnstile>\<^sub>c marg_dens_cexpr \<Gamma> vs x \<delta> : REAL" by fact
  next
    show "free_vars (marg_dens_cexpr \<Gamma> vs x \<delta>) \<subseteq> shift_var_set (set vs')"
      using edc_var.prems(2) by (rule free_vars_marg_dens_cexpr)
  next
    have free_vars: "free_vars (marg_dens_cexpr \<Gamma> vs x \<delta>) \<subseteq> shift_var_set (set vs')"
      using edc_var.prems(2) by (rule free_vars_marg_dens_cexpr)
    show "(\<lambda>(\<rho>, y). ennreal (eval_cexpr (marg_dens_cexpr \<Gamma> vs x \<delta>) \<rho> y))
             \<in> borel_measurable (state_measure (set vs') \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
    apply (subst measurable_split_conv, rule measurable_compose[OF _ measurable_ennreal])
    apply (subst measurable_split_conv[symmetric], rule measurable_eval_cexpr)
    apply (insert ctype free_vars, auto simp: shift_var_set_def)
    done
  next
    fix \<rho> assume "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    hence "AE y in stock_measure t.
             marg_dens (dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>)) x \<rho> y =
                  ennreal (eval_cexpr (marg_dens_cexpr \<Gamma> vs x \<delta>) \<rho> y)"
      using edc_var unfolding eval_cexpr_def by (subst t, subst eq_commute, intro cexpr_sem_marg_dens)
    thus "AE y in stock_measure t.
            marg_dens (set vs, set vs', \<Gamma>, \<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>))) x \<rho> y =
                 ennreal (eval_cexpr (marg_dens_cexpr \<Gamma> vs x \<delta>) \<rho> y)"
      by (simp add: dens_ctxt_\<alpha>_def)
  next
    show "x \<in> set vs"
      by (insert edc_var.prems edc_var.hyps, auto simp: eval_cexpr_def intro!: nonneg_cexpr_sem_marg_dens)
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) (marg_dens_cexpr \<Gamma> vs x \<delta>)"
      by (intro nonneg_cexprI_shift nonneg_cexpr_sem_marg_dens[OF edc_var.prems(2) \<open>x \<in> set vs\<close>])
         (auto simp: t)
  qed
next
  case (edc_pair x vs y vs' \<Gamma> \<delta> t)
  hence t[simp]: "t = PRODUCT (\<Gamma> x) (\<Gamma> y)" by auto
  note invar = cdens_ctxt_invarD[OF edc_pair.prems(2)]
  from invar have ctype: "case_nat t \<Gamma> \<turnstile>\<^sub>c marg_dens2_cexpr \<Gamma> vs x y \<delta> : REAL" by auto
  from edc_pair.prems have vars: "free_vars (marg_dens2_cexpr \<Gamma> vs x y \<delta>) \<subseteq> shift_var_set (set vs')"
    using free_vars_marg_dens2_cexpr by simp

  show ?case unfolding dens_ctxt_\<alpha>_def
  proof (simp only: prod.case, intro conjI is_density_exprI, rule hd_AE[OF hd_pair edc_pair.prems(1)])
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    show "AE z in stock_measure t.
              marg_dens2 (set vs, set vs', \<Gamma>, \<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>))) x y \<rho> z =
                ennreal (eval_cexpr (marg_dens2_cexpr \<Gamma> vs x y \<delta>) \<rho> z)"
      using cexpr_sem_marg_dens2[OF edc_pair.prems(2) edc_pair.hyps \<rho>] unfolding eval_cexpr_def
      by (subst t, subst eq_commute) (simp add: dens_ctxt_\<alpha>_def)
  next
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) (marg_dens2_cexpr \<Gamma> vs x y \<delta>)"
      by (intro nonneg_cexprI_shift nonneg_cexpr_sem_marg_dens2[OF edc_pair.prems(2) \<open>x \<in> set vs\<close> \<open>y\<in>set vs\<close>])
         auto
  qed (insert edc_pair invar ctype vars, auto simp: dens_ctxt_\<alpha>_def)

next
  case (edc_fail vs vs' \<Gamma> \<delta> t t')
  hence [simp]: "t = t'" by auto
  have ctype: "case_nat t' \<Gamma> \<turnstile>\<^sub>c CReal 0 : REAL"
    by (subst val_type.simps[symmetric]) (rule cexpr_typing.intros)
  thus ?case by (auto simp: dens_ctxt_\<alpha>_def eval_cexpr_def extract_real_def
                            zero_ennreal_def[symmetric] hd_fail
                      intro!: is_density_exprI nonneg_cexprI)

next
  case (edc_let vs vs' \<Gamma> e f \<delta> e' g t)
  then obtain t' where t1: "\<Gamma> \<turnstile> e : t'" and t2: "case_nat t' \<Gamma> \<turnstile> e' : t" by auto
  note invar = cdens_ctxt_invarD[OF edc_let.prems(2)]
  from t1 have t1': "the (expr_type \<Gamma> e) = t'" by (auto simp: expr_type_Some_iff[symmetric])
  have dens1: "dens_ctxt_\<alpha> ([], vs @ vs', \<Gamma>, CReal 1) \<turnstile>\<^sub>d  e \<Rightarrow>
                   (\<lambda>x xa. ennreal (eval_cexpr f x xa))" and
       wf1: "is_density_expr ([], vs @ vs', \<Gamma>, CReal 1) t' f"
    using edc_let.IH(1)[OF t1] edc_let.prems by (auto dest: cdens_ctxt_invar_empty)

  have invf: "cdens_ctxt_invar (shift_vars vs) (map Suc vs') (case_nat t' \<Gamma>) (map_vars Suc \<delta> *\<^sub>c f)"
    using edc_let.prems edc_let.hyps dens1 wf1 invar
    by (intro cdens_ctxt_invar_insert[OF _ t1]) (auto simp: dens_ctxt_\<alpha>_def)

  let ?\<Y> = "(shift_vars vs, map Suc vs', case_nat t' \<Gamma>, map_vars Suc \<delta> *\<^sub>c f)"
  have "set (shift_vars vs) \<union> set (map Suc vs') = shift_var_set (set vs \<union> set vs')"
    by (simp add: shift_var_set_def image_Un)
  hence "dens_ctxt_\<alpha> (shift_vars vs, map Suc vs', case_nat t' \<Gamma>, map_vars Suc \<delta> *\<^sub>c f) \<turnstile>\<^sub>d
            e' \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr g x xa)) \<and>
        is_density_expr (shift_vars vs, map Suc vs', case_nat t' \<Gamma>, map_vars Suc \<delta> *\<^sub>c f) t g"
    using invf t2 edc_let.prems subset_shift_var_set
    by (simp only: t1'[symmetric], intro edc_let.IH(2)) simp_all
  hence dens2: "dens_ctxt_\<alpha> ?\<Y>  \<turnstile>\<^sub>d e' \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr g x xa))" and
        wf2: "is_density_expr (shift_vars vs, map Suc vs', case_nat t' \<Gamma>, map_vars Suc \<delta> *\<^sub>c f) t g"
    by simp_all

  have cexpr_eq: "cexpr_sem (case_nat x \<rho> \<circ> (\<lambda>x. x - Suc 0)) g =
                   cexpr_sem (case_nat x (case_nat undefined \<rho>)) g" for x \<rho>
    using is_density_exprD[OF wf2]
    by (intro cexpr_sem_eq_on_vars) (auto split: nat.split simp: shift_var_set_def)

  have [simp]: "\<And>\<sigma>. case_nat (\<sigma> 0) (\<lambda>x. \<sigma> (Suc x)) = \<sigma>" by (intro ext) (simp split: nat.split)
  hence "(shift_var_set (set vs), Suc ` set vs', case_nat t' \<Gamma>,
           insert_dens (set vs) (set vs') (\<lambda>x xa. ennreal (eval_cexpr f x xa))
                (\<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>))))
          \<turnstile>\<^sub>d e' \<Rightarrow> (\<lambda>a aa. ennreal (eval_cexpr g a aa))" using dens2
    apply (simp only: dens_ctxt_\<alpha>_def prod.case set_shift_vars set_map)
    apply (erule hd_dens_ctxt_cong)
    apply (insert invar is_density_exprD[OF wf1])
    unfolding insert_dens_def
    apply (subst ennreal_mult'[symmetric])
    apply (erule nonneg_cexprD)
    apply (rule measurable_space[OF measurable_remove_var[where t=t']])
    apply simp
    apply (simp add: shift_var_set_def image_Un)
    apply (subst cexpr_sem_Mult[of "case_nat t' \<Gamma>"])
    apply (auto intro!: cexpr_typing_map_vars simp: o_def shift_var_set_def image_Un
             cexpr_sem_map_vars insert_dens_def eval_cexpr_def remove_var_def)
    done

  hence "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d LET e IN e' \<Rightarrow>
            (\<lambda>\<rho> x. ennreal (eval_cexpr g (case_nat undefined \<rho>) x))"
    unfolding dens_ctxt_\<alpha>_def
    by (simp only: prod.case, intro hd_let[where f = "\<lambda>x xa. ennreal (eval_cexpr f x xa)"])
       (insert dens1 dens2, simp_all add: dens_ctxt_\<alpha>_def extract_real_def one_ennreal_def t1')
  hence "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d LET e IN e' \<Rightarrow>
            (\<lambda>\<rho> x. ennreal (eval_cexpr (map_vars (\<lambda>x. x - 1) g) \<rho> x))"
  proof (simp only: dens_ctxt_\<alpha>_def prod.case, erule_tac hd_cong[OF _ _ edc_let.prems(1,3)])
    fix \<rho> x assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
               and x: "x \<in> space (stock_measure t)"
    have "eval_cexpr (map_vars (\<lambda>x. x - 1) g) \<rho> x =
            extract_real (cexpr_sem (case_nat x \<rho> \<circ> (\<lambda>x. x - Suc 0)) g)"
      unfolding eval_cexpr_def by (simp add: cexpr_sem_map_vars)
    also note cexpr_eq[of x \<rho>]
    finally show "ennreal (eval_cexpr g (case_nat undefined \<rho>) x) =
                      ennreal (eval_cexpr (map_vars (\<lambda>x. x - 1) g) \<rho> x)"
      by (simp add: eval_cexpr_def)
  qed (simp_all add: density_context_\<alpha>[OF edc_let.prems(2)])
  moreover have "is_density_expr (vs, vs', \<Gamma>, \<delta>) t (map_vars (\<lambda>x. x - 1) g)"
  proof (intro is_density_exprI)
    note wf = is_density_exprD[OF wf2]
    show "case_nat t \<Gamma> \<turnstile>\<^sub>c map_vars (\<lambda>x. x - 1) g : REAL"
      by (rule cexpr_typing_map_vars, rule cexpr_typing_cong'[OF wf(1)])
         (insert wf(2), auto split: nat.split simp: shift_var_set_def)
    from wf(2) show "free_vars (map_vars (\<lambda>x. x - 1) g)
                         \<subseteq> shift_var_set (set vs')"
      by (auto simp: shift_var_set_def)
  next
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) (map_vars (\<lambda>x. x - 1) g)"
      apply (intro nonneg_cexprI_shift)
      apply (simp add: cexpr_sem_map_vars cexpr_eq)
      apply (rule nonneg_cexprD[OF wf2[THEN is_density_exprD_nonneg]])
      apply (auto simp: space_state_measure PiE_iff extensional_def split: nat.splits)
      done
  qed
  ultimately show ?case by (rule conjI)

next
  case (edc_rand vs vs' \<Gamma> \<delta> e f dst t')
  define t where "t = dist_param_type dst"
  note invar = cdens_ctxt_invarD[OF edc_rand.prems(2)]
  from edc_rand have t1: "\<Gamma> \<turnstile> e : t" and t2: "t' = dist_result_type dst" by (auto simp: t_def)

  have dens: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr f x xa))" and
       wf: "is_density_expr (vs, vs', \<Gamma>, \<delta>) t f" using edc_rand t1 t2 by auto
  from wf have tf: "case_nat t \<Gamma> \<turnstile>\<^sub>c f : REAL" and varsf: "free_vars f \<subseteq> shift_var_set (set vs')"
    unfolding is_density_expr_def by simp_all
  let ?M = "(\<lambda>\<rho>. dens_ctxt_measure (dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>)) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e))"
  have dens': "has_parametrized_subprob_density (state_measure (set vs') \<Gamma>) ?M (stock_measure t)
                   (\<lambda>\<rho> x. ennreal (eval_cexpr f \<rho> x))" using dens t1 edc_rand.prems
    by (simp_all add: dens_ctxt_\<alpha>_def expr_has_density_sound_aux density_context_\<alpha>)

  let ?shift = "case_nat 0 (\<lambda>x. Suc (Suc x))"
  let ?e1 = "map_vars ?shift f"
  let ?e2 = "dist_dens_cexpr dst (CVar 0) (CVar 1)"
  let ?e = "(\<integral>\<^sub>c ?e1 *\<^sub>c ?e2 \<partial>t)"
  have [simp]: "\<And>t t' \<Gamma>. case_nat t (case_nat t' \<Gamma>) \<circ> ?shift = case_nat t \<Gamma>"
    by (intro ext) (simp split: nat.split add: o_def)
  have te1: "case_nat t (case_nat t' \<Gamma>) \<turnstile>\<^sub>c ?e1 : REAL" using tf
    by (auto intro!: cexpr_typing.intros cexpr_typing_dist_dens_cexpr cet_var'
        cexpr_typing_map_vars simp: t_def t2)
  have te2: "case_nat t (case_nat t' \<Gamma>) \<turnstile>\<^sub>c ?e2 : REAL"
    by (intro cexpr_typing_dist_dens_cexpr cet_var') (simp_all add: t_def t2)
  have te: "case_nat t' \<Gamma> \<turnstile>\<^sub>c ?e : REAL" using te1 te2
    by (intro cet_int cet_op[where t = "PRODUCT REAL REAL"] cet_pair) (simp_all add: t2 t_def)
  have vars_e1: "free_vars ?e1 \<subseteq> shift_var_set (shift_var_set (set vs'))"
    using varsf by (auto simp: shift_var_set_def)
  have "(case_nat 0 (\<lambda>x. Suc (Suc x)) -` shift_var_set (shift_var_set (set vs'))) =
          shift_var_set (set vs')" by (auto simp: shift_var_set_def split: nat.split_asm)
  have nonneg_e1: "nonneg_cexpr (shift_var_set (shift_var_set (set vs'))) (case_nat t  (case_nat t' \<Gamma>)) ?e1"
    by (auto intro!: nonneg_cexprI wf[THEN is_density_exprD_nonneg, THEN nonneg_cexprD] case_nat_in_state_measure
             dest!: space_state_measureD_shift simp: cexpr_sem_map_vars)
  have vars_e2: "free_vars ?e2 \<subseteq> shift_var_set (shift_var_set (set vs'))"
    by (intro order.trans[OF free_vars_dist_dens_cexpr]) (auto simp: shift_var_set_def)
  have nonneg_e2:  "nonneg_cexpr (shift_var_set (shift_var_set (set vs')))
                        (case_nat t  (case_nat t' \<Gamma>)) ?e2"
    by (intro nonneg_dist_dens_cexpr cet_var') (auto simp: t2 t_def shift_var_set_def)

  let ?f = "\<lambda>\<rho> x. \<integral>\<^sup>+y. ennreal (eval_cexpr f \<rho> y) * dist_dens dst y x\<partial>stock_measure t"
  let ?M = "(\<lambda>\<rho>. dens_ctxt_measure (dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>)) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Random dst e)))"
  have dens': "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d Random dst e \<Rightarrow> ?f" using dens
    by (simp only: dens_ctxt_\<alpha>_def prod.case t_def hd_rand[unfolded apply_dist_to_dens_def])
  hence dens'': "has_parametrized_subprob_density (state_measure (set vs') \<Gamma>) ?M (stock_measure t') ?f"
    using edc_rand.prems invar
    by (simp only: dens_ctxt_\<alpha>_def prod.case, intro expr_has_density_sound_aux)
       (auto intro!: density_context_\<alpha>)

  {
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    fix x assume x: "x \<in> type_universe t'"
    fix y assume y: "y \<in> type_universe t"
    let ?\<rho>'' = "case_nat y (case_nat x \<rho>)" and ?\<Gamma>'' = "case_nat t (case_nat t' \<Gamma>)"
    let ?V'' = "shift_var_set (shift_var_set (set vs'))"
    have \<rho>'': "?\<rho>'' \<in> space (state_measure (shift_var_set (shift_var_set (set vs'))) ?\<Gamma>'')"
      using \<rho> x y by (intro case_nat_in_state_measure) simp_all
    have A: "extract_real (cexpr_sem ?\<rho>'' (?e1 *\<^sub>c ?e2)) =
                extract_real (cexpr_sem ?\<rho>'' ?e1) * extract_real (cexpr_sem ?\<rho>'' ?e2)"
       by (rule cexpr_sem_Mult[OF te1 te2 \<rho>'' vars_e1 vars_e2])
    also have "... \<ge> 0" using nonneg_e1 nonneg_e2 \<rho>''
      by (blast intro: mult_nonneg_nonneg dest: nonneg_cexprD)
    finally have B: "extract_real (cexpr_sem ?\<rho>'' (?e1 *\<^sub>c ?e2)) \<ge> 0" .
    note A
    hence "eval_cexpr f \<rho> y * dist_dens dst y x = extract_real (cexpr_sem ?\<rho>'' (?e1 *\<^sub>c ?e2))"
      using \<rho>''
      apply (subst A)
      apply (subst ennreal_mult'')
      using nonneg_e2
      apply (erule nonneg_cexprD)
      apply (subst cexpr_sem_dist_dens_cexpr[of ?\<Gamma>'' _ _ _ ?V''])
      apply (force simp: cexpr_sem_map_vars eval_cexpr_def t2 t_def intro!: cet_var')+
      done
    note this B
  } note e1e2 = this

  {
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    have "AE x in stock_measure t'.
            apply_dist_to_dens dst (\<lambda>\<rho> x. ennreal (eval_cexpr f \<rho> x)) \<rho> x = eval_cexpr ?e \<rho> x"
    proof (rule AE_mp[OF _ AE_I2[OF impI]])
      from has_parametrized_subprob_density_integral[OF dens'' \<rho>]
        have "(\<integral>\<^sup>+x. ?f \<rho> x \<partial>stock_measure t') \<noteq> \<infinity>" by auto
      thus "AE x in stock_measure t'. ?f \<rho> x \<noteq> \<infinity>"
        using has_parametrized_subprob_densityD(3)[OF dens''] \<rho>
        by (intro nn_integral_PInf_AE ) simp_all
    next
      fix x assume x: "x \<in> space (stock_measure t')" and finite: "?f \<rho> x \<noteq> \<infinity>"
      let ?\<rho>' = "case_nat x \<rho>"
      have \<rho>': "?\<rho>' \<in> space (state_measure (shift_var_set (set vs')) (case_nat t' \<Gamma>))"
        using \<rho> x by (intro case_nat_in_state_measure) simp_all
      hence *: "(\<integral>\<^sup>+y. ennreal (eval_cexpr f \<rho> y) * dist_dens dst y x \<partial>stock_measure t) =
               \<integral>\<^sup>+y. extract_real (cexpr_sem (case_nat y ?\<rho>') (?e1 *\<^sub>c ?e2)) \<partial>stock_measure t" (is "_ = ?I")
        using \<rho> x by (intro nn_integral_cong) (simp add: e1e2)
      also from * and finite have finite': "?I < \<infinity>" by (simp add: less_top)
      have "?I = ennreal (eval_cexpr ?e \<rho> x)" using \<rho>' te te1 te2 vars_e1 vars_e2 nonneg_e1 nonneg_e2
        unfolding eval_cexpr_def
        by (subst cexpr_sem_integral_nonneg[OF finite'])
           (auto simp: eval_cexpr_def t2 t_def intro!: nonneg_cexpr_Mult)
      finally show "apply_dist_to_dens dst (\<lambda>\<rho> x. ennreal (eval_cexpr f \<rho> x)) \<rho> x =
                        ennreal (eval_cexpr ?e \<rho> x)"
        unfolding apply_dist_to_dens_def by (simp add: t_def)
     qed
   } note AE_eq = this

  have meas: "(\<lambda>(\<rho>, x). ennreal (eval_cexpr ?e \<rho> x))
                 \<in> borel_measurable (state_measure (set vs') \<Gamma> \<Otimes>\<^sub>M stock_measure t')"
    apply (subst measurable_split_conv, rule measurable_compose[OF _ measurable_ennreal])
    apply (subst measurable_split_conv[symmetric], rule measurable_eval_cexpr[OF te])
    apply (insert vars_e1 vars_e2, auto simp: shift_var_set_def)
    done
  show ?case
  proof (intro conjI is_density_exprI, simp only: dens_ctxt_\<alpha>_def prod.case,
         rule hd_AE[OF hd_rand edc_rand.prems(1)])
    from dens show "(set vs, set vs', \<Gamma>, \<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>))) \<turnstile>\<^sub>d
                        e \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr f x xa))"
      unfolding dens_ctxt_\<alpha>_def by simp
  next
    have "nonneg_cexpr (shift_var_set (set vs')) (case_nat t' \<Gamma>) (\<integral>\<^sub>c ?e1 *\<^sub>c ?e2 \<partial>t)"
      by (intro nonneg_cexpr_int nonneg_cexpr_Mult nonneg_dist_dens_cexpr te1 te2 vars_e1 vars_e2 nonneg_e1)
         (auto simp: t_def t2 intro!: cet_var')
    then show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t' \<Gamma>)
     (\<integral>\<^sub>c map_vars (case_nat 0 (\<lambda>x. x + 2)) f *\<^sub>c ?e2 \<partial>dist_param_type dst)"
     by (simp add: t_def)
  qed (insert AE_eq meas te vars_e1 vars_e2, auto simp: t_def t2 shift_var_set_def)

next
  case (edc_rand_det e vs' vs \<Gamma> \<delta> dst t')
  define t where "t = dist_param_type dst"
  note invar = cdens_ctxt_invarD[OF edc_rand_det.prems(2)]
  from edc_rand_det have t1: "\<Gamma> \<turnstile> e : t" and t2: "t' = dist_result_type dst" by (auto simp: t_def)
  let ?e1 = "map_vars Suc (branch_prob_cexpr (vs, vs', \<Gamma>, \<delta>))" and
      ?e2 = "dist_dens_cexpr dst (map_vars Suc (expr_rf_to_cexpr e)) (CVar 0)"
  have ctype1: "case_nat t' \<Gamma> \<turnstile>\<^sub>c ?e1 : REAL"
    using invar by (auto intro!: cexpr_typing_map_vars simp: o_def)
  have vars2': "free_vars (map_vars Suc (expr_rf_to_cexpr e)) \<subseteq> shift_var_set (set vs')"
    unfolding shift_var_set_def using free_vars_expr_rf_to_cexpr edc_rand_det.hyps by auto
  have vars2: "free_vars ?e2 \<subseteq> shift_var_set (free_vars e)"
    unfolding shift_var_set_def using free_vars_expr_rf_to_cexpr edc_rand_det.hyps
    by (intro order.trans[OF free_vars_dist_dens_cexpr]) auto
  have ctype2: "case_nat t' \<Gamma> \<turnstile>\<^sub>c ?e2 : REAL" using t1 edc_rand_det.hyps
    by (intro cexpr_typing_dist_dens_cexpr cexpr_typing_map_vars)
       (auto simp: o_def t_def t2 intro!: cet_var')

  have nonneg_e2: "nonneg_cexpr (shift_var_set (set vs')) (case_nat t' \<Gamma>) ?e2"
    using t1 \<open>randomfree e\<close> free_vars_expr_rf_to_cexpr[of e] edc_rand_det.hyps
    apply (intro nonneg_dist_dens_cexpr cexpr_typing_map_vars)
    apply (auto simp add: o_def t_def t2 intro!: cet_var')
    done

  have nonneg_e1: "nonneg_cexpr (shift_var_set (set vs')) (case_nat t' \<Gamma>) ?e1"
    using invar
    by (auto simp add: branch_prob_cexpr_def nonneg_cexpr_shift_iff intro!: nonneg_cexpr_sem_integrate_vars')

  {
    fix \<rho> x
    assume x: "x \<in> type_universe t'" and \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    hence \<rho>': "case_nat x \<rho> \<in> space (state_measure (shift_var_set (set vs')) (case_nat t' \<Gamma>))"
      by (rule case_nat_in_state_measure)
    hence "eval_cexpr (?e1 *\<^sub>c ?e2) \<rho> x =
             ennreal (extract_real (cexpr_sem (case_nat x \<rho>)
                 (map_vars Suc (branch_prob_cexpr (vs, vs', \<Gamma>, \<delta>))))) *
             ennreal (extract_real (cexpr_sem (case_nat x \<rho>) ?e2))" (is "_ = ?a * ?b")
      using invar
      apply (subst ennreal_mult''[symmetric])
      apply (rule nonneg_cexprD[OF nonneg_e2])
      apply simp
      unfolding eval_cexpr_def
      apply (subst cexpr_sem_Mult[of "case_nat t' \<Gamma>" _ _ _ "shift_var_set (set vs')"])
      apply (insert invar ctype1 vars2 ctype2 edc_rand_det.hyps(2))
      apply (auto simp: shift_var_set_def)
      done
    also have "?a = branch_prob (dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>)) \<rho>" (is "_ = ?c")
      by (subst cexpr_sem_map_vars, subst cexpr_sem_branch_prob) (simp_all add: o_def \<rho> edc_rand_det.prems)
    also have "?b = dist_dens dst (expr_sem_rf \<rho> e) x" (is "_ = ?d") using t1 edc_rand_det.hyps
      by (subst cexpr_sem_dist_dens_cexpr[of "case_nat t' \<Gamma>"], insert \<rho>' vars2')
         (auto intro!: cexpr_typing_map_vars cet_var'
               simp: o_def t_def t2 cexpr_sem_map_vars cexpr_sem_expr_rf_to_cexpr)
    finally have A: "ennreal (eval_cexpr (?e1 *\<^sub>c ?e2) \<rho> x) = ?c * ?d" .
  } note A = this

  have meas: "(\<lambda>(\<rho>, x). ennreal (eval_cexpr (?e1 *\<^sub>c ?e2) \<rho> x))
                \<in> borel_measurable (state_measure (set vs') \<Gamma> \<Otimes>\<^sub>M stock_measure t')"
    using ctype1 ctype2 vars2 invar edc_rand_det.hyps
    by (subst measurable_split_conv, intro measurable_compose[OF _ measurable_ennreal],
        subst measurable_split_conv[symmetric], intro measurable_eval_cexpr)
       (auto intro!: cexpr_typing.intros simp: shift_var_set_def)
  from ctype1 ctype2 vars2 invar edc_rand_det.hyps
    have wf: "is_density_expr (vs, vs', \<Gamma>, \<delta>) t' (?e1 *\<^sub>c ?e2)"
  proof (intro is_density_exprI)
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t' \<Gamma>) (?e1 *\<^sub>c ?e2)"
      using invar(2)
        order_trans[OF free_vars_expr_rf_to_cexpr[OF \<open>randomfree e\<close>] \<open>free_vars e \<subseteq> set vs'\<close>]
      by (intro nonneg_cexpr_Mult ctype1 ctype2 nonneg_e2 nonneg_e1
          free_vars_dist_dens_cexpr[THEN order_trans])
         (auto simp: intro: order_trans)
  qed (auto intro!: cexpr_typing.intros simp: shift_var_set_def)
  show ?case using edc_rand_det.prems edc_rand_det.hyps meas wf A
    apply (intro conjI, simp add: dens_ctxt_\<alpha>_def)
    apply (intro hd_AE[OF hd_rand_det[OF edc_rand_det.hyps] edc_rand_det.prems(1) AE_I2])
    apply (simp_all add: dens_ctxt_\<alpha>_def)
    done

next
  case (edc_if_det b vs vs' \<Gamma> \<delta> e1 f1 e2 f2 t)
  hence tb: "\<Gamma> \<turnstile> b : BOOL" and t1: "\<Gamma> \<turnstile> e1 : t" and t2: "\<Gamma> \<turnstile> e2 : t" by auto
  from edc_if_det have b: "randomfree b" "free_vars b \<subseteq> set vs \<union> set vs'" by simp_all
  note invar = cdens_ctxt_invarD[OF edc_if_det.prems(2)]

  let ?ind1 = "\<langle>expr_rf_to_cexpr b\<rangle>\<^sub>c" and ?ind2 = "\<langle>\<not>\<^sub>c expr_rf_to_cexpr b\<rangle>\<^sub>c"
  have tind1: "\<Gamma> \<turnstile>\<^sub>c ?ind1 : REAL" and tind2: "\<Gamma> \<turnstile>\<^sub>c ?ind2 : REAL"
    using edc_if_det.hyps tb by (auto intro!: cexpr_typing.intros)
  have t\<delta>1: "\<Gamma> \<turnstile>\<^sub>c \<delta> *\<^sub>c ?ind1 : REAL" and t\<delta>2: "\<Gamma> \<turnstile>\<^sub>c \<delta> *\<^sub>c ?ind2 : REAL"
    using invar(3) edc_if_det.hyps tb by (auto intro!: cexpr_typing.intros)
  have nonneg_ind1: "nonneg_cexpr (set vs \<union> set vs') \<Gamma> ?ind1" and
       nonneg_ind2: "nonneg_cexpr (set vs \<union> set vs') \<Gamma> ?ind2"
    using tind1 tind2 edc_if_det.hyps tb
    by (auto intro!: nonneg_cexprI simp: cexpr_sem_expr_rf_to_cexpr bool_to_real_def extract_real_def
             dest: val_type_expr_sem_rf[OF tb b] elim!: BOOL_E split: if_split)
  have subprob1: "subprob_cexpr (set vs) (set vs') \<Gamma> (\<delta> *\<^sub>c ?ind1)" and
       subprob2: "subprob_cexpr (set vs) (set vs') \<Gamma> (\<delta> *\<^sub>c ?ind2)"
    using invar tb edc_if_det.hyps edc_if_det.prems free_vars_expr_rf_to_cexpr[OF edc_if_det.hyps(1)]
    by (auto intro!: subprob_indicator cet_op)
  have vars1: "free_vars (\<delta> *\<^sub>c ?ind1) \<subseteq> set vs \<union> set vs'" and
       vars2: "free_vars (\<delta> *\<^sub>c ?ind2) \<subseteq> set vs \<union> set vs'"
    using invar edc_if_det.hyps edc_if_det.prems free_vars_expr_rf_to_cexpr by auto
  have inv1: "cdens_ctxt_invar vs vs' \<Gamma> (\<delta> *\<^sub>c ?ind1)"
    using invar edc_if_det.hyps edc_if_det.prems tind1 t\<delta>1  subprob1 nonneg_ind1 vars1
    by (intro cdens_ctxt_invarI nonneg_cexpr_Mult) auto
  have inv2: "cdens_ctxt_invar vs vs' \<Gamma> (\<delta> *\<^sub>c ?ind2)"
    using invar edc_if_det.hyps edc_if_det.prems tind2 t\<delta>2  subprob2 nonneg_ind2 vars2
    by (intro cdens_ctxt_invarI nonneg_cexpr_Mult) auto
  have dens1: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta> *\<^sub>c ?ind1) \<turnstile>\<^sub>d e1 \<Rightarrow> (\<lambda>\<rho> x. eval_cexpr f1 \<rho> x)" and
       wf1:   "is_density_expr (vs, vs', \<Gamma>, \<delta> *\<^sub>c ?ind1) t f1"
    using edc_if_det.IH(1)[OF t1 inv1] edc_if_det.prems by auto
  have dens2: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta> *\<^sub>c ?ind2) \<turnstile>\<^sub>d e2 \<Rightarrow> (\<lambda>\<rho> x. eval_cexpr f2 \<rho> x)" and
       wf2:   "is_density_expr (vs, vs', \<Gamma>, \<delta> *\<^sub>c ?ind2) t f2"
    using edc_if_det.IH(2)[OF t2 inv2] edc_if_det.prems by auto

  show ?case
  proof (rule conjI, simp only: dens_ctxt_\<alpha>_def prod.case, rule hd_cong[OF hd_if_det])
    let ?\<Y> = "(set vs, set vs', \<Gamma>, if_dens_det (\<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>))) b True)"
    show "?\<Y> \<turnstile>\<^sub>d e1 \<Rightarrow> (\<lambda>\<rho> x. eval_cexpr f1 \<rho> x)"
    proof (rule hd_dens_ctxt_cong)
      let ?\<delta> = "\<lambda>\<sigma>. ennreal (extract_real (cexpr_sem \<sigma> (\<delta> *\<^sub>c ?ind1)))"
      show "(set vs, set vs', \<Gamma>, ?\<delta>) \<turnstile>\<^sub>d e1 \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr f1 \<rho> x))"
        using dens1 by (simp add: dens_ctxt_\<alpha>_def)
      fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure (set vs \<union> set vs') \<Gamma>)"
      have "extract_real (cexpr_sem \<sigma> (\<delta> *\<^sub>c ?ind1)) =
                extract_real (cexpr_sem \<sigma> \<delta>) * extract_real (cexpr_sem \<sigma> ?ind1)" using invar vars1
        by (subst cexpr_sem_Mult[OF invar(3) tind1 \<sigma>]) simp_all
      also have "extract_real (cexpr_sem \<sigma> ?ind1) = (if expr_sem_rf \<sigma> b = TRUE then 1 else 0)"
        using edc_if_det.hyps val_type_expr_sem_rf[OF tb b \<sigma>]
        by (auto simp: cexpr_sem_expr_rf_to_cexpr extract_real_def bool_to_real_def elim!: BOOL_E)
      finally show "?\<delta> \<sigma> = if_dens_det (\<lambda>\<sigma>. ennreal (extract_real (cexpr_sem \<sigma> \<delta>))) b True \<sigma>"
        by (simp add: if_dens_det_def)
    qed
  next
    let ?\<Y> = "(set vs, set vs', \<Gamma>, if_dens_det (\<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>))) b False)"
    show "?\<Y> \<turnstile>\<^sub>d e2 \<Rightarrow> (\<lambda>\<rho> x. eval_cexpr f2 \<rho> x)"
    proof (rule hd_dens_ctxt_cong)
      let ?\<delta> = "\<lambda>\<sigma>. ennreal (extract_real (cexpr_sem \<sigma> (\<delta> *\<^sub>c ?ind2)))"
      show "(set vs, set vs', \<Gamma>, ?\<delta>) \<turnstile>\<^sub>d e2 \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr f2 \<rho> x))"
        using dens2 by (simp add: dens_ctxt_\<alpha>_def)
      fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure (set vs \<union> set vs') \<Gamma>)"
      have "extract_real (cexpr_sem \<sigma> (\<delta> *\<^sub>c ?ind2)) =
                extract_real (cexpr_sem \<sigma> \<delta>) * extract_real (cexpr_sem \<sigma> ?ind2)" using invar vars1
        by (subst cexpr_sem_Mult[OF invar(3) tind2 \<sigma>]) simp_all
      also have "extract_real (cexpr_sem \<sigma> ?ind2) = (if expr_sem_rf \<sigma> b = FALSE then 1 else 0)"
        using edc_if_det.hyps val_type_expr_sem_rf[OF tb b \<sigma>]
        by (auto simp: cexpr_sem_expr_rf_to_cexpr extract_real_def bool_to_real_def elim!: BOOL_E)
      finally show "?\<delta> \<sigma> = if_dens_det (\<lambda>\<sigma>. ennreal (extract_real (cexpr_sem \<sigma> \<delta>))) b False \<sigma>"
        by (simp add: if_dens_det_def)
    qed
  next
    fix \<rho> x assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)" and x : "x \<in> space (stock_measure t)"
    hence "eval_cexpr (f1 +\<^sub>c f2) \<rho> x = eval_cexpr f1 \<rho> x + eval_cexpr f2 \<rho> x"
      using wf1 wf2 unfolding eval_cexpr_def is_density_expr_def
      by (subst cexpr_sem_Add[where \<Gamma> = "case_nat t \<Gamma>" and V = "shift_var_set (set vs')"]) auto
    moreover have "0 \<le> eval_cexpr f1 \<rho> x" "0 \<le> eval_cexpr f2 \<rho> x"
      unfolding eval_cexpr_def
      using \<rho> x wf1[THEN is_density_exprD_nonneg, THEN nonneg_cexprD] wf2[THEN is_density_exprD_nonneg, THEN nonneg_cexprD]
      unfolding space_state_measure_shift_iff by auto
    ultimately show "ennreal (eval_cexpr f1 \<rho> x) + ennreal (eval_cexpr f2 \<rho> x) = ennreal (eval_cexpr (f1 +\<^sub>c f2) \<rho> x)"
      by simp
  next
    show "is_density_expr (vs, vs', \<Gamma>, \<delta>) t (f1 +\<^sub>c f2)" using wf1 wf2
      using wf1[THEN is_density_exprD_nonneg] wf2[THEN is_density_exprD_nonneg]
      by (auto simp: is_density_expr_def intro!: cet_op[where t = "PRODUCT REAL REAL"] cet_pair nonneg_cexpr_Add)
  qed (insert edc_if_det.prems edc_if_det.hyps, auto intro!: density_context_\<alpha>)

next
  case (edc_if vs vs' \<Gamma> b f \<delta> e1 g1 e2 g2 t)
  hence tb: "\<Gamma> \<turnstile> b : BOOL" and t1: "\<Gamma> \<turnstile> e1 : t" and t2: "\<Gamma> \<turnstile> e2 : t" by auto
  note invar = cdens_ctxt_invarD[OF edc_if.prems(2)]

  have densb: "dens_ctxt_\<alpha> ([], vs @ vs', \<Gamma>, CReal 1) \<turnstile>\<^sub>d b \<Rightarrow> (\<lambda>\<rho> b. ennreal (eval_cexpr f \<rho> b))" and
         wfb: "is_density_expr ([], vs @ vs', \<Gamma>, CReal 1) BOOL f"
    using edc_if.IH(1)[OF tb] edc_if.prems by (simp_all add: cdens_ctxt_invar_empty)
  have inv1: "cdens_ctxt_invar vs vs' \<Gamma> (\<delta> *\<^sub>c cexpr_subst_val f TRUE)" and
       inv2: "cdens_ctxt_invar vs vs' \<Gamma> (\<delta> *\<^sub>c cexpr_subst_val f FALSE)"
    using tb densb wfb edc_if.prems by (auto intro!: cdens_ctxt_invar_insert_bool)
  let ?\<delta>1 = "cexpr_subst_val f TRUE" and ?\<delta>2 = "cexpr_subst_val f FALSE"
  have t\<delta>1: "\<Gamma> \<turnstile>\<^sub>c \<delta> *\<^sub>c ?\<delta>1 : REAL" and t\<delta>2: "\<Gamma> \<turnstile>\<^sub>c \<delta> *\<^sub>c ?\<delta>2 : REAL"
    using is_density_exprD[OF wfb] invar
    by (auto intro!: cet_op[where t = "PRODUCT REAL REAL"] cet_pair)
  have vars1: "free_vars (\<delta> *\<^sub>c ?\<delta>1) \<subseteq> set vs \<union> set vs'" and
       vars2: "free_vars (\<delta> *\<^sub>c ?\<delta>2) \<subseteq> set vs \<union> set vs'"
    using invar is_density_exprD[OF wfb] by (auto simp: shift_var_set_def)
  have dens1: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta> *\<^sub>c ?\<delta>1) \<turnstile>\<^sub>d e1 \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr g1 x xa))" and
         wf1: "is_density_expr (vs, vs', \<Gamma>, \<delta> *\<^sub>c ?\<delta>1) t g1" and
       dens2: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta> *\<^sub>c ?\<delta>2) \<turnstile>\<^sub>d e2 \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr g2 x xa))" and
         wf2: "is_density_expr (vs, vs', \<Gamma>, \<delta> *\<^sub>c ?\<delta>2) t g2"
    using edc_if.IH(2)[OF t1 inv1] edc_if.IH(3)[OF t2 inv2] edc_if.prems by simp_all

  have f_nonneg[simp]: "\<sigma> \<in> space (state_measure (set vs \<union> set vs') \<Gamma>) \<Longrightarrow>
    0 \<le> extract_real (cexpr_sem (case_nat (BoolVal b) \<sigma>) f)" for b \<sigma>
    using wfb[THEN is_density_exprD_nonneg] by (rule nonneg_cexprD) auto

  let ?\<delta>' = "\<lambda>\<sigma>. ennreal (extract_real (cexpr_sem \<sigma> \<delta>))" and ?f = "\<lambda>\<sigma> x. ennreal (eval_cexpr f \<sigma> x)"
  show ?case
  proof (rule conjI, simp only: dens_ctxt_\<alpha>_def prod.case, rule hd_cong[OF hd_if])
    let ?\<Y> = "(set vs, set vs', \<Gamma>, if_dens ?\<delta>' ?f True)"
    show "?\<Y> \<turnstile>\<^sub>d e1 \<Rightarrow> (\<lambda>\<rho> x. eval_cexpr g1 \<rho> x)"
    proof (rule hd_dens_ctxt_cong)
      let ?\<delta> = "\<lambda>\<sigma>. ennreal (extract_real (cexpr_sem \<sigma> (\<delta> *\<^sub>c ?\<delta>1)))"
      show "(set vs, set vs', \<Gamma>, ?\<delta>) \<turnstile>\<^sub>d e1 \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr g1 \<rho> x))"
        using dens1 by (simp add: dens_ctxt_\<alpha>_def)
      fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure (set vs \<union> set vs') \<Gamma>)"
      have "extract_real (cexpr_sem \<sigma> (\<delta> *\<^sub>c ?\<delta>1)) =
                extract_real (cexpr_sem \<sigma> \<delta>) * extract_real (cexpr_sem \<sigma> ?\<delta>1)"
        using invar vars1 is_density_exprD[OF wfb] by (subst cexpr_sem_Mult[OF invar(3) _ \<sigma>]) auto
      also have "... = if_dens ?\<delta>' ?f True \<sigma>" unfolding if_dens_def by (simp add: eval_cexpr_def ennreal_mult'' \<sigma>)
      finally show "?\<delta> \<sigma> = if_dens ?\<delta>' ?f True \<sigma>" by (simp add: if_dens_det_def)
    qed
  next
    let ?\<Y> = "(set vs, set vs', \<Gamma>, if_dens ?\<delta>' ?f False)"
    show "?\<Y> \<turnstile>\<^sub>d e2 \<Rightarrow> (\<lambda>\<rho> x. eval_cexpr g2 \<rho> x)"
    proof (rule hd_dens_ctxt_cong)
      let ?\<delta> = "\<lambda>\<sigma>. ennreal (extract_real (cexpr_sem \<sigma> (\<delta> *\<^sub>c ?\<delta>2)))"
      show "(set vs, set vs', \<Gamma>, ?\<delta>) \<turnstile>\<^sub>d e2 \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr g2 \<rho> x))"
        using dens2 by (simp add: dens_ctxt_\<alpha>_def)
      fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure (set vs \<union> set vs') \<Gamma>)"
      have "extract_real (cexpr_sem \<sigma> (\<delta> *\<^sub>c ?\<delta>2)) =
                extract_real (cexpr_sem \<sigma> \<delta>) * extract_real (cexpr_sem \<sigma> ?\<delta>2)"
        using invar vars1 is_density_exprD[OF wfb] by (subst cexpr_sem_Mult[OF invar(3) _ \<sigma>]) auto
      also have "... = if_dens ?\<delta>' ?f False \<sigma>" unfolding if_dens_def by (simp add: eval_cexpr_def ennreal_mult'' \<sigma>)
      finally show "?\<delta> \<sigma> = if_dens ?\<delta>' ?f False \<sigma>" by (simp add: if_dens_det_def)
    qed
  next
    fix \<rho> x assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)" and x : "x \<in> space (stock_measure t)"
    hence "eval_cexpr (g1 +\<^sub>c g2) \<rho> x = eval_cexpr g1 \<rho> x + eval_cexpr g2 \<rho> x"
      using wf1 wf2 unfolding eval_cexpr_def is_density_expr_def
      by (subst cexpr_sem_Add[where \<Gamma> = "case_nat t \<Gamma>" and V = "shift_var_set (set vs')"]) auto
    moreover have "0 \<le> eval_cexpr g1 \<rho> x" "0 \<le> eval_cexpr g2 \<rho> x"
      unfolding eval_cexpr_def
      using \<rho> x wf1[THEN is_density_exprD_nonneg, THEN nonneg_cexprD] wf2[THEN is_density_exprD_nonneg, THEN nonneg_cexprD]
      unfolding space_state_measure_shift_iff by auto
    ultimately show "ennreal (eval_cexpr g1 \<rho> x) + ennreal (eval_cexpr g2 \<rho> x) = ennreal (eval_cexpr (g1 +\<^sub>c g2) \<rho> x)"
      by simp
  next
    show "is_density_expr (vs, vs', \<Gamma>, \<delta>) t (g1 +\<^sub>c g2)" using wf1 wf2
      by (auto simp: is_density_expr_def intro!: cet_op[where t = "PRODUCT REAL REAL"] cet_pair nonneg_cexpr_Add)
  next
    show "({}, set vs \<union> set vs', \<Gamma>, \<lambda>_. 1) \<turnstile>\<^sub>d b \<Rightarrow> (\<lambda>\<sigma> x. ennreal (eval_cexpr f \<sigma> x))"
      using densb unfolding dens_ctxt_\<alpha>_def by (simp add: extract_real_def one_ennreal_def)
  qed (insert edc_if.prems edc_if.hyps, auto intro!: density_context_\<alpha>)

next
  case (edc_op_discr vs vs' \<Gamma> \<delta> e f t oper t' t'')
  let ?expr' = "\<langle>(oper $$\<^sub>c (CVar 0)) =\<^sub>c CVar 1\<rangle>\<^sub>c *\<^sub>c map_vars (case_nat 0 (\<lambda>x. x+2)) f"
  let ?expr = "\<integral>\<^sub>c ?expr' \<partial>t" and ?shift = "case_nat 0 (\<lambda>x. x + 2)"
  from edc_op_discr.prems(1) edc_op_discr.hyps
    have t: "\<Gamma> \<turnstile> e : t" by (elim expr_typing_opE, fastforce split: pdf_type.split_asm)
  with edc_op_discr.prems(1) and edc_op_discr.hyps have [simp]: "t'' = t'"
    by (intro expr_typing_unique) (auto intro: et_op)
  from t and edc_op_discr.prems(1)
    have the_t1: "the (expr_type \<Gamma> e) = t" and the_t2: "the (expr_type \<Gamma> (oper $$ e)) = t'"
    by (simp_all add: expr_type_Some_iff[symmetric])

  from edc_op_discr.prems edc_op_discr.IH[OF t]
    have dens: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr f x xa))" and
         wf: "is_density_expr (vs, vs', \<Gamma>, \<delta>) t f" by simp_all
  note wf' = is_density_exprD[OF wf]
  have ctype''': "case_nat t (case_nat t' \<Gamma>) \<turnstile>\<^sub>c (oper $$\<^sub>c (CVar 0)) =\<^sub>c CVar 1 : BOOL" and
       ctype'':  "case_nat t (case_nat t' \<Gamma>) \<turnstile>\<^sub>c \<langle>(oper $$\<^sub>c (CVar 0)) =\<^sub>c CVar 1\<rangle>\<^sub>c : REAL" and
       ctype':   "case_nat t (case_nat t' \<Gamma>) \<turnstile>\<^sub>c ?expr' : REAL" using wf' edc_op_discr.hyps
    by ((intro cet_op_intros cexpr_typing_map_vars cet_var' cet_pair cet_eq,
         auto intro!: cet_op cet_var') [])+
  from ctype' have ctype: "case_nat t' \<Gamma> \<turnstile>\<^sub>c ?expr : REAL" by (rule cet_int)
  have vars': "free_vars ?expr' \<subseteq> shift_var_set (shift_var_set (set vs'))" using wf'
    by (auto split: nat.split simp: shift_var_set_def)
  hence vars: "free_vars ?expr \<subseteq> shift_var_set (set vs')" by (auto split: nat.split_asm)

  let ?\<Y> = "(set vs, set vs', \<Gamma>, \<lambda>\<rho>. ennreal (extract_real (cexpr_sem \<rho> \<delta>)))"
  let ?M = "\<lambda>\<rho>. dens_ctxt_measure ?\<Y> \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)"
  have "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) f"
    using wf[THEN is_density_exprD_nonneg] .
  hence nonneg: "nonneg_cexpr (shift_var_set (shift_var_set (set vs')))
                              (case_nat t (case_nat t' \<Gamma>)) ?expr'"
    using wf' vars' ctype''' by (intro nonneg_cexpr_Mult[OF ctype''] cexpr_typing_map_vars
                                       nonneg_cexpr_map_vars nonneg_indicator)
                                (auto dest: nonneg_cexprD simp: extract_real_def bool_to_real_def)

  let ?M = "\<lambda>\<rho>. dens_ctxt_measure ?\<Y> \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (oper $$ e))"
  let ?f = "\<lambda>\<rho> x y. (if op_sem oper y = x then 1 else 0) * ennreal (eval_cexpr f \<rho> y)"
  have "?\<Y> \<turnstile>\<^sub>d oper $$ e \<Rightarrow> (\<lambda>\<rho> x. \<integral>\<^sup>+y. ?f \<rho> x y \<partial>stock_measure t)" using dens t edc_op_discr.hyps
    by (subst the_t1[symmetric], intro hd_op_discr)
       (simp_all add: dens_ctxt_\<alpha>_def the_t1 expr_type_Some_iff[symmetric])
  hence dens: "?\<Y> \<turnstile>\<^sub>d oper $$ e \<Rightarrow> (\<lambda>\<rho> x. \<integral>\<^sup>+y. eval_cexpr ?expr' (case_nat x \<rho>) y \<partial>stock_measure t)"
  proof (rule hd_cong[OF _ _ _ _  nn_integral_cong])
    fix \<rho> x y let ?P = "\<lambda>x M. x \<in> space M"
    assume A: "?P \<rho> (state_measure (set vs') \<Gamma>)" "?P x (stock_measure t')" "?P y (stock_measure t)"
    hence "val_type (cexpr_sem (case_nat y \<rho>) f) = REAL" using wf' by (intro val_type_cexpr_sem) auto
    thus "?f \<rho> x y = ennreal (eval_cexpr ?expr' (case_nat x \<rho>) y)"
      by (auto simp: eval_cexpr_def extract_real_def lift_RealIntVal2_def
            bool_to_real_def cexpr_sem_map_vars elim!: REAL_E)
  qed (insert edc_op_discr.prems, auto intro!: density_context_\<alpha>)
  hence dens': "has_parametrized_subprob_density (state_measure (set vs') \<Gamma>) ?M (stock_measure t')
                     (\<lambda>\<rho> x. \<integral>\<^sup>+y. eval_cexpr ?expr' (case_nat x \<rho>) y \<partial>stock_measure t)"
    using edc_op_discr.prems by (intro expr_has_density_sound_aux density_context_\<alpha>) simp_all

  show ?case
  proof (intro conjI is_density_exprI, simp only: dens_ctxt_\<alpha>_def prod.case, rule hd_AE[OF dens])
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    let ?dens = "\<lambda>x. \<integral>\<^sup>+y. eval_cexpr ?expr' (case_nat x \<rho>) y \<partial>stock_measure t"
    show "AE x in stock_measure t'. ?dens x = ennreal (eval_cexpr ?expr \<rho> x)"
    proof (rule AE_mp[OF _ AE_I2[OF impI]])
      from has_parametrized_subprob_density_integral[OF dens' \<rho>] and
           has_parametrized_subprob_densityD(3)[OF dens'] and \<rho>
        show "AE x in stock_measure t'. ?dens x \<noteq> \<infinity>" by (intro nn_integral_PInf_AE) auto
    next
      fix x assume x: "x \<in> space (stock_measure t')" and fin: "?dens x \<noteq> \<infinity>"
      thus "?dens x = ennreal (eval_cexpr ?expr \<rho> x)"
        using \<rho> vars' ctype' ctype' nonneg unfolding eval_cexpr_def
        by (subst cexpr_sem_integral_nonneg) (auto intro!: nonneg_cexpr_map_vars simp: less_top)
    qed
  next
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t'' \<Gamma>) (\<integral>\<^sub>c ?expr' \<partial>t)"
      using nonneg by (intro nonneg_cexpr_int) simp
  qed (insert vars ctype edc_op_discr.prems, auto)

next
  case (edc_fst vs vs' \<Gamma> \<delta> e f t'' t' t)
  hence [simp]: "t'' = t" by (auto intro!: expr_typing_unique et_op)
  from edc_fst.hyps have t': "the (expr_type \<Gamma> (Snd $$ e)) = t'"
     by (simp add: expr_type_Some_iff[symmetric])
    let ?shift = "case_nat 0 (\<lambda>x. x + 2)"
  have [simp]: "\<And>t t'. case_nat t (case_nat t' \<Gamma>) \<circ> case_nat 0 (\<lambda>x. Suc (Suc x)) = case_nat t \<Gamma>"
    by (intro ext) (simp split: nat.split add: o_def)
  note invar = cdens_ctxt_invarD[OF edc_fst.prems(2)]
  have dens: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr f \<rho> x))" and
         wf: "is_density_expr (vs, vs', \<Gamma>, \<delta>) (PRODUCT t t') f" using edc_fst by auto
  let ?M = "\<lambda>\<rho>. dens_ctxt_measure (set vs, set vs', \<Gamma>, \<lambda>\<rho>. ennreal (extract_real (cexpr_sem \<rho> \<delta>))) \<rho>
                    \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)"
  have nonneg: "nonneg_cexpr (shift_var_set (set vs')) (case_nat (PRODUCT t t') \<Gamma>) f"
    using wf by (rule is_density_exprD_nonneg)

  note wf' = is_density_exprD[OF wf]
  let ?expr = "map_vars ?shift f \<circ>\<^sub>c <CVar 1, CVar 0>\<^sub>c"
  have ctype: "case_nat t' (case_nat t \<Gamma>) \<turnstile>\<^sub>c ?expr : REAL"
     using wf' by (auto intro!: cexpr_typing.intros cexpr_typing_map_vars)
  have vars: "free_vars ?expr \<subseteq> shift_var_set (shift_var_set (set vs'))" using free_vars_cexpr_comp wf'
    by (intro subset_shift_var_set) (force simp: shift_var_set_def)
  let ?M = "\<lambda>\<rho>. dens_ctxt_measure (set vs, set vs', \<Gamma>, \<lambda>\<rho>. ennreal (extract_real (cexpr_sem \<rho> \<delta>))) \<rho>
                    \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Fst $$ e))"
  have A: "\<And>x y \<rho>. ((case_nat x (case_nat y \<rho>))(0 := <|y, x|>)) \<circ> ?shift = case_nat <|y, x|> \<rho>"
    by (intro ext) (simp split: nat.split add: o_def)
  have dens': "(set vs, set vs', \<Gamma>, \<lambda>\<rho>. ennreal (extract_real (cexpr_sem \<rho> \<delta>))) \<turnstile>\<^sub>d Fst $$ e \<Rightarrow>
                  (\<lambda>\<rho> x. (\<integral>\<^sup>+y. eval_cexpr f \<rho> (<|x, y|>) \<partial>stock_measure t'))" (is "?\<Y> \<turnstile>\<^sub>d _ \<Rightarrow> ?f")
    using dens by (subst t'[symmetric], intro hd_fst) (simp add: dens_ctxt_\<alpha>_def)
  hence dens': "?\<Y> \<turnstile>\<^sub>d Fst $$ e \<Rightarrow> (\<lambda>\<rho> x. (\<integral>\<^sup>+y. eval_cexpr ?expr (case_nat x \<rho>) y \<partial>stock_measure t'))"
    (is "_ \<turnstile>\<^sub>d _ \<Rightarrow> ?f") by (rule hd_cong, intro density_context_\<alpha>, insert edc_fst.prems A)
       (auto intro!: nn_integral_cong simp: eval_cexpr_def cexpr_sem_cexpr_comp cexpr_sem_map_vars)
  hence dens'': "has_parametrized_subprob_density (state_measure (set vs') \<Gamma>) ?M (stock_measure t) ?f"
    using edc_fst.prems by (intro expr_has_density_sound_aux density_context_\<alpha>) simp_all

  have "\<And>V. ?shift -` shift_var_set (shift_var_set V) = shift_var_set V"
    by (auto simp: shift_var_set_def split: nat.split_asm)
  hence nonneg': "nonneg_cexpr (shift_var_set (shift_var_set (set vs'))) (case_nat t' (case_nat t \<Gamma>)) ?expr"
    by (auto intro!: nonneg_cexpr_comp nonneg_cexpr_map_vars nonneg cexpr_typing.intros cet_var')
  show ?case
  proof (intro conjI is_density_exprI, simp only: dens_ctxt_\<alpha>_def prod.case, rule hd_AE[OF dens'])
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    thus "AE x in stock_measure t. ?f \<rho> x = ennreal (eval_cexpr (\<integral>\<^sub>c ?expr \<partial>t') \<rho> x)"
      using ctype vars edc_fst.hyps nonneg'
      by (intro has_parametrized_subprob_density_cexpr_sem_integral[OF dens'']) auto
  next
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>)
     (\<integral>\<^sub>c (map_vars (case_nat 0 (\<lambda>x. x + 2)) f \<circ>\<^sub>c <CVar 1, CVar 0>\<^sub>c) \<partial>t')"
     using nonneg' by (intro nonneg_cexpr_int)
  qed (insert edc_fst.prems ctype vars, auto simp: measurable_split_conv
       intro!: cet_int measurable_compose[OF _ measurable_ennreal]
               measurable_Pair_compose_split[OF measurable_eval_cexpr])

next
  case (edc_snd vs vs' \<Gamma> \<delta> e f t t' t'')
  hence [simp]: "t'' = t'" by (auto intro!: expr_typing_unique et_op)
  from edc_snd.hyps have t': "the (expr_type \<Gamma> (Fst $$ e)) = t"
     by (simp add: expr_type_Some_iff[symmetric])
    let ?shift = "case_nat 0 (\<lambda>x. x + 2)"
  have [simp]: "\<And>t t'. case_nat t (case_nat t' \<Gamma>) \<circ> case_nat 0 (\<lambda>x. Suc (Suc x)) = case_nat t \<Gamma>"
    by (intro ext) (simp split: nat.split add: o_def)
  note invar = cdens_ctxt_invarD[OF edc_snd.prems(2)]
  have dens: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr f \<rho> x))" and
         wf: "is_density_expr (vs, vs', \<Gamma>, \<delta>) (PRODUCT t t') f" using edc_snd by auto
  let ?M = "\<lambda>\<rho>. dens_ctxt_measure (set vs, set vs', \<Gamma>, \<lambda>\<rho>. ennreal (extract_real (cexpr_sem \<rho> \<delta>))) \<rho>
                    \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)"
  have nonneg: "nonneg_cexpr (shift_var_set (set vs')) (case_nat (PRODUCT t t') \<Gamma>) f"
    using wf by (rule is_density_exprD_nonneg)

  note wf' = is_density_exprD[OF wf]
  let ?expr = "map_vars ?shift f \<circ>\<^sub>c <CVar 0, CVar 1>\<^sub>c"
  have ctype: "case_nat t (case_nat t' \<Gamma>) \<turnstile>\<^sub>c ?expr : REAL"
     using wf' by (auto intro!: cexpr_typing.intros cexpr_typing_map_vars)
  have vars: "free_vars ?expr \<subseteq> shift_var_set (shift_var_set (set vs'))" using free_vars_cexpr_comp wf'
    by (intro subset_shift_var_set) (force simp: shift_var_set_def)
  let ?M = "\<lambda>\<rho>. dens_ctxt_measure (set vs, set vs', \<Gamma>, \<lambda>\<rho>. ennreal (extract_real (cexpr_sem \<rho> \<delta>))) \<rho>
                    \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Snd $$ e))"
  have A: "\<And>x y \<rho>. ((case_nat y (case_nat x \<rho>))(0 := <|y, x|>)) \<circ> ?shift = case_nat <|y, x|> \<rho>"
    by (intro ext) (simp split: nat.split add: o_def)
  have dens': "(set vs, set vs', \<Gamma>, \<lambda>\<rho>. ennreal (extract_real (cexpr_sem \<rho> \<delta>))) \<turnstile>\<^sub>d Snd $$ e \<Rightarrow>
                  (\<lambda>\<rho> y. (\<integral>\<^sup>+x. eval_cexpr f \<rho> (<|x, y|>) \<partial>stock_measure t))" (is "?\<Y> \<turnstile>\<^sub>d _ \<Rightarrow> ?f")
    using dens by (subst t'[symmetric], intro hd_snd) (simp add: dens_ctxt_\<alpha>_def)
  hence dens': "?\<Y> \<turnstile>\<^sub>d Snd $$ e \<Rightarrow> (\<lambda>\<rho> y. (\<integral>\<^sup>+x. eval_cexpr ?expr (case_nat y \<rho>) x \<partial>stock_measure t))"
    (is "_ \<turnstile>\<^sub>d _ \<Rightarrow> ?f") by (rule hd_cong, intro density_context_\<alpha>, insert edc_snd.prems A)
       (auto intro!: nn_integral_cong simp: eval_cexpr_def cexpr_sem_cexpr_comp cexpr_sem_map_vars)
  hence dens'': "has_parametrized_subprob_density (state_measure (set vs') \<Gamma>) ?M (stock_measure t') ?f"
    using edc_snd.prems by (intro expr_has_density_sound_aux density_context_\<alpha>) simp_all

  have "\<And>V. ?shift -` shift_var_set (shift_var_set V) = shift_var_set V"
    by (auto simp: shift_var_set_def split: nat.split_asm)
  hence nonneg': "nonneg_cexpr (shift_var_set (shift_var_set (set vs'))) (case_nat t (case_nat t' \<Gamma>)) ?expr"
    by (auto intro!: nonneg_cexpr_comp nonneg_cexpr_map_vars nonneg cexpr_typing.intros cet_var')
  show ?case
  proof (intro conjI is_density_exprI , simp only: dens_ctxt_\<alpha>_def prod.case, rule hd_AE[OF dens'])
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    thus "AE x in stock_measure t'. ?f \<rho> x = ennreal (eval_cexpr (\<integral>\<^sub>c ?expr \<partial>t) \<rho> x)"
      using ctype vars edc_snd.hyps nonneg'
      by (intro has_parametrized_subprob_density_cexpr_sem_integral[OF dens'']) auto
  next
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t'' \<Gamma>) (\<integral>\<^sub>c ?expr \<partial>t)"
      using nonneg' by (intro nonneg_cexpr_int) simp
  qed (insert edc_snd.prems ctype vars, auto simp: measurable_split_conv
       intro!: cet_int measurable_compose[OF _ measurable_ennreal]
               measurable_Pair_compose_split[OF measurable_eval_cexpr])

next
  case (edc_neg vs vs' \<Gamma> \<delta> e f t)
  from edc_neg.prems(1) have t: "\<Gamma> \<turnstile> e : t" by (cases t)  (auto split: pdf_type.split_asm)
  from edc_neg.prems(1) have t_disj: "t = REAL \<or> t = INTEG"
    by (cases t)  (auto split: pdf_type.split_asm)
  from edc_neg.prems edc_neg.IH[OF t]
    have dens: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr f x xa))" and
         wf: "is_density_expr (vs, vs', \<Gamma>, \<delta>) t f" by simp_all

  have "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d Minus $$ e \<Rightarrow> (\<lambda>\<sigma> x. ennreal (eval_cexpr f \<sigma> (op_sem Minus x)))"
    using dens by (simp only: dens_ctxt_\<alpha>_def prod.case, intro hd_neg) simp_all
  also have "(\<lambda>\<sigma> x. ennreal (eval_cexpr f \<sigma> (op_sem Minus x))) =
                 (\<lambda>\<sigma> x. ennreal (eval_cexpr (f \<circ>\<^sub>c -\<^sub>c CVar 0) \<sigma> x))"
     by (intro ext) (auto simp: eval_cexpr_comp)
  finally have "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d Minus $$ e \<Rightarrow>
                    (\<lambda>\<sigma> x. ennreal (eval_cexpr (f \<circ>\<^sub>c -\<^sub>c CVar 0) \<sigma> x))" .
  moreover have "is_density_expr (vs, vs', \<Gamma>, \<delta>) t (f \<circ>\<^sub>c -\<^sub>c CVar 0)"
  proof (intro is_density_exprI)
    from t_disj have t_minus: "case_nat t \<Gamma> \<turnstile>\<^sub>c -\<^sub>c CVar 0 : t"
      by (intro cet_op[where t = t]) (auto simp: cexpr_type_Some_iff[symmetric])
    thus "case_nat t \<Gamma> \<turnstile>\<^sub>c f \<circ>\<^sub>c -\<^sub>c CVar 0 : REAL" using is_density_exprD(1)[OF wf]
      by (intro cexpr_typing_cexpr_comp[of _ _ _ t])
    show "free_vars (f \<circ>\<^sub>c -\<^sub>c CVar 0) \<subseteq> shift_var_set (set vs')" using is_density_exprD(2)[OF wf]
      by (intro order.trans[OF free_vars_cexpr_comp]) (auto simp: shift_var_set_def)
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) (f \<circ>\<^sub>c -\<^sub>c CVar 0)"
      using wf[THEN is_density_exprD_nonneg] t_disj
      by (intro nonneg_cexpr_comp)
         (auto intro!: cet_var' cet_minus_real cet_minus_int)
  qed
  ultimately show ?case by (rule conjI)

next
  case (edc_addc vs vs' \<Gamma> \<delta> e f e' t)
  let ?expr = "f \<circ>\<^sub>c (\<lambda>\<^sub>cx. x -\<^sub>c map_vars Suc (expr_rf_to_cexpr e'))"
  from edc_addc.prems(1)
    have t1: "\<Gamma> \<turnstile> e : t" and t2: "\<Gamma> \<turnstile> e' : t" and t3: "op_type Add (PRODUCT t t) = Some t"
    by (elim expr_typing_opE expr_typing_pairE, fastforce split: pdf_type.split_asm)+
  from edc_addc.prems(1) have t_disj: "t = REAL \<or> t = INTEG"
    by (cases t) (auto split: pdf_type.split_asm)
  hence t3': "op_type Minus t = Some t" by auto
  from edc_addc.prems edc_addc.IH[OF t1]
    have dens: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr f x xa))" and
         wf: "is_density_expr (vs, vs', \<Gamma>, \<delta>) t f" by simp_all
  hence ctype: "case_nat t \<Gamma> \<turnstile>\<^sub>c ?expr : REAL" using t1 t2 t3 t3' edc_addc.hyps edc_addc.prems
    by (intro cexpr_typing_cexpr_comp cet_op[where t = "PRODUCT t t"] cet_var')
       (auto intro!: cet_pair cexpr_typing_map_vars cet_var' cet_op dest: is_density_exprD simp: o_def)
  have vars: "free_vars ?expr \<subseteq> shift_var_set (set vs')" using edc_addc.prems edc_addc.hyps
    using free_vars_expr_rf_to_cexpr is_density_exprD[OF wf]
    by (intro order.trans[OF free_vars_cexpr_comp subset_shift_var_set]) auto

  have cet_e': "\<Gamma> \<turnstile> e' : t"
    using edc_addc.prems(1)
    apply (cases)
    apply (erule expr_typing.cases)
    apply (auto split: pdf_type.splits)
    done

  have "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d Add $$ <e, e'> \<Rightarrow>
            (\<lambda>\<sigma> x. ennreal (eval_cexpr f \<sigma> (op_sem Add <|x, expr_sem_rf \<sigma> (Minus $$ e')|>)))"
     (is "?\<Y> \<turnstile>\<^sub>d _ \<Rightarrow> ?f") using dens edc_addc.hyps
     by (simp only: dens_ctxt_\<alpha>_def prod.case, intro hd_addc) simp_all
  also have "?f = (\<lambda>\<sigma> x. ennreal (eval_cexpr ?expr \<sigma> x))" using edc_addc.hyps
     by (intro ext) (auto simp: eval_cexpr_comp cexpr_sem_map_vars o_def cexpr_sem_expr_rf_to_cexpr)
  finally have "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d Add $$ <e, e'> \<Rightarrow>
                    (\<lambda>\<sigma> x. ennreal (eval_cexpr ?expr \<sigma> x))" .
  moreover have "is_density_expr (vs, vs', \<Gamma>, \<delta>) t ?expr" using ctype vars
  proof (intro is_density_exprI)
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) ?expr"
      using t_disj edc_addc.hyps edc_addc.prems cet_e' free_vars_expr_rf_to_cexpr[of e']
      by (intro nonneg_cexpr_comp[OF wf[THEN is_density_exprD_nonneg]])
         (auto intro!: cet_add_int cet_add_real cet_minus_int cet_minus_real cet_var' cexpr_typing_map_vars
               simp: o_def)
  qed auto
  ultimately show ?case by (rule conjI)

next
  case (edc_multc vs vs' \<Gamma> \<delta> e f c t)
  let ?expr = "(f \<circ>\<^sub>c (\<lambda>\<^sub>cx. x *\<^sub>c CReal (inverse c))) *\<^sub>c CReal (inverse (abs c))"
  from edc_multc.prems(1) edc_multc.hyps have t1: "\<Gamma> \<turnstile> e : REAL" and [simp]: "t = REAL"
    by (elim expr_typing_opE expr_typing_pairE, force split: pdf_type.split_asm)+
  from edc_multc.prems edc_multc.IH[OF t1]
    have dens: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr f x xa))" and
         wf: "is_density_expr (vs, vs', \<Gamma>, \<delta>) REAL f" by simp_all
  have ctype': "case_nat t \<Gamma> \<turnstile>\<^sub>c f \<circ>\<^sub>c (\<lambda>\<^sub>cx. x *\<^sub>c CReal (inverse c)) : REAL"
    using t1 edc_multc.hyps edc_multc.prems is_density_exprD[OF wf]
    by (intro cexpr_typing_cexpr_comp)
       (auto intro!: cet_pair cexpr_typing_map_vars cet_var' cet_val' cet_op_intros)
  hence ctype: "case_nat t \<Gamma> \<turnstile>\<^sub>c ?expr : REAL"
    by (auto intro!: cet_op_intros cet_pair cet_val')
  have vars': "free_vars (f \<circ>\<^sub>c (\<lambda>\<^sub>cx. x *\<^sub>c CReal (inverse c))) \<subseteq> shift_var_set (set vs')"
    using edc_multc.prems edc_multc.hyps free_vars_expr_rf_to_cexpr is_density_exprD[OF wf]
    by (intro order.trans[OF free_vars_cexpr_comp subset_shift_var_set]) auto
  hence vars: "free_vars ?expr \<subseteq> shift_var_set (set vs')" by simp

  have "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d Mult $$ <e, Val (RealVal c)> \<Rightarrow>
            (\<lambda>\<sigma> x. ennreal (eval_cexpr f \<sigma> (op_sem Mult <|x, op_sem Inverse (RealVal c)|>)) *
                       ennreal (inverse (abs (extract_real (RealVal c)))))"
     (is "?\<Y> \<turnstile>\<^sub>d _ \<Rightarrow> ?f") using dens edc_multc.hyps
     by (simp only: dens_ctxt_\<alpha>_def prod.case, intro hd_multc) simp_all
  hence "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d Mult $$ <e, Val (RealVal c)> \<Rightarrow>
             (\<lambda>\<sigma> x. ennreal (eval_cexpr ?expr \<sigma> x))"
  proof (simp only: dens_ctxt_\<alpha>_def prod.case, erule_tac hd_cong)
    fix \<rho> x assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)" and x: "x \<in> space (stock_measure REAL)"
    hence "eval_cexpr ?expr \<rho> x =
               extract_real (cexpr_sem (case_nat x \<rho>) (f \<circ>\<^sub>c CVar 0 *\<^sub>c CReal (inverse c))) * inverse \<bar>c\<bar>"
       (is "_ = ?a * ?b") unfolding eval_cexpr_def
       by (subst cexpr_sem_Mult[OF ctype' cet_val' _ vars'])
          (auto simp: extract_real_def simp del: stock_measure.simps)
    also hence "?a = eval_cexpr f \<rho> (op_sem Mult <|x, op_sem Inverse (RealVal c)|>)"
      by (auto simp: cexpr_sem_cexpr_comp eval_cexpr_def lift_RealVal_def lift_RealIntVal2_def)
    finally show "ennreal (eval_cexpr f \<rho> (op_sem Mult <|x, op_sem Inverse (RealVal c)|>)) *
                      ennreal (inverse \<bar>extract_real (RealVal c)\<bar>) = ennreal (eval_cexpr ?expr \<rho> x)"
      by (simp add: extract_real_def ennreal_mult'')
  qed (insert edc_multc.prems, auto intro!: density_context_\<alpha>)
  moreover have "is_density_expr (vs, vs', \<Gamma>, \<delta>) t ?expr" using ctype vars
  proof (intro is_density_exprI)
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) ?expr"
      using is_density_exprD[OF wf] vars vars'
      by (intro nonneg_cexpr_comp[OF wf[THEN is_density_exprD_nonneg]] nonneg_cexpr_Mult ctype')
         (auto intro!: nonneg_cexprI cet_var' cet_val' cet_op_intros)
  qed auto
  ultimately show ?case by (rule conjI)

next
  case (edc_add vs vs' \<Gamma> \<delta> e f t t')
  note t = \<open>\<Gamma> \<turnstile> e : PRODUCT t t\<close>
  note invar = cdens_ctxt_invarD[OF edc_add.prems(2)]
  from edc_add.prems and t have "op_type Add (PRODUCT t t) = Some t'"
    by (elim expr_typing_opE) (auto dest: expr_typing_unique)
  hence [simp]: "t' = t" and t_disj: "t = INTEG \<or> t = REAL" by (auto split: pdf_type.split_asm)

  have dens: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>x xa. ennreal (eval_cexpr f x xa))" and
        wf:  "is_density_expr (vs, vs', \<Gamma>, \<delta>) (PRODUCT t t) f"
    using edc_add by simp_all
  note wf' = is_density_exprD[OF wf]
  let ?\<Y> = "(set vs, set vs', \<Gamma>, \<lambda>\<rho>. ennreal (extract_real (cexpr_sem \<rho> \<delta>)))"
  let ?M = "\<lambda>\<rho>. dens_ctxt_measure ?\<Y> \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)"
  have nonneg: "nonneg_cexpr (shift_var_set (set vs')) (case_nat (PRODUCT t t) \<Gamma>) f"
    using wf by (rule is_density_exprD_nonneg)

  let ?shift = "case_nat 0 (\<lambda>x. x + 2)"
  let ?expr' = "map_vars ?shift f \<circ>\<^sub>c (\<lambda>\<^sub>cx. <x, CVar 1 -\<^sub>c x>\<^sub>c)"
  let ?expr = "\<integral>\<^sub>c ?expr' \<partial>t"
  have [simp]: "\<And>t t' \<Gamma>. case_nat t (case_nat t' \<Gamma>) \<circ> case_nat 0 (\<lambda>x. Suc (Suc x)) = case_nat t \<Gamma>"
    by (intro ext) (simp split: nat.split add: o_def)
  have ctype'': "case_nat t (case_nat t \<Gamma>) \<turnstile>\<^sub>c <CVar 0, CVar 1 -\<^sub>c CVar 0>\<^sub>c : PRODUCT t t"
    by (rule cet_pair, simp add: cet_var', rule cet_op[where t = "PRODUCT t t"], rule cet_pair)
       (insert t_disj, auto intro!: cet_var' cet_op[where t = t])
  hence ctype': "case_nat t (case_nat t \<Gamma>) \<turnstile>\<^sub>c ?expr' : REAL" using wf'
    by (intro cexpr_typing_cexpr_comp cexpr_typing_map_vars) simp_all
  hence ctype: "case_nat t \<Gamma> \<turnstile>\<^sub>c ?expr : REAL" by (rule cet_int)
  have vars': "free_vars ?expr' \<subseteq> shift_var_set (shift_var_set (set vs'))" using wf'
    by (intro order.trans[OF free_vars_cexpr_comp]) (auto split: nat.split simp: shift_var_set_def)
  hence vars: "free_vars ?expr \<subseteq> shift_var_set (set vs')" by auto

  let ?M = "\<lambda>\<rho>. dens_ctxt_measure ?\<Y> \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Add $$ e))"
  let ?f = "\<lambda>\<rho> x y. eval_cexpr f \<rho> <|y, op_sem Add <|x, op_sem Minus y|>|>"
  have "?\<Y> \<turnstile>\<^sub>d Add $$ e \<Rightarrow> (\<lambda>\<rho> x. \<integral>\<^sup>+y. ?f \<rho> x y \<partial>stock_measure (val_type x))" using dens
    by (intro hd_add) (simp add: dens_ctxt_\<alpha>_def)
  hence dens: "?\<Y> \<turnstile>\<^sub>d Add $$ e \<Rightarrow> (\<lambda>\<rho> x. \<integral>\<^sup>+y. eval_cexpr ?expr' (case_nat x \<rho>) y \<partial>stock_measure t)"
  by (rule hd_cong) (insert edc_add.prems, auto intro!: density_context_\<alpha> nn_integral_cong
                                             simp: eval_cexpr_def cexpr_sem_cexpr_comp cexpr_sem_map_vars)
  hence dens': "has_parametrized_subprob_density (state_measure (set vs') \<Gamma>) ?M (stock_measure t)
                     (\<lambda>\<rho> x. \<integral>\<^sup>+y. eval_cexpr ?expr' (case_nat x \<rho>) y \<partial>stock_measure t)"
    using edc_add.prems by (intro expr_has_density_sound_aux density_context_\<alpha>) simp_all

  show ?case
  proof (intro conjI is_density_exprI, simp only: dens_ctxt_\<alpha>_def prod.case, rule hd_AE[OF dens])
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
    let ?dens = "\<lambda>x. \<integral>\<^sup>+y. eval_cexpr ?expr' (case_nat x \<rho>) y \<partial>stock_measure t"
    show "AE x in stock_measure t. ?dens x = ennreal (eval_cexpr ?expr \<rho> x)"
    proof (rule AE_mp[OF _ AE_I2[OF impI]])
      from has_parametrized_subprob_density_integral[OF dens' \<rho>] and
           has_parametrized_subprob_densityD(3)[OF dens'] and \<rho>
        show "AE x in stock_measure t. ?dens x \<noteq> \<infinity>" by (intro nn_integral_PInf_AE) auto
    next
      fix x assume x: "x \<in> space (stock_measure t)" and fin: "?dens x \<noteq> \<infinity>"
      thus "?dens x = ennreal (eval_cexpr ?expr \<rho> x)"
        using \<rho> vars' ctype' ctype'' nonneg unfolding eval_cexpr_def
        by (subst cexpr_sem_integral_nonneg) (auto intro!: nonneg_cexpr_comp nonneg_cexpr_map_vars simp: less_top)
    qed
  next
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t' \<Gamma>) ?expr"
      using ctype'' nonneg
      by (intro nonneg_cexpr_int nonneg_cexpr_comp[of _ "PRODUCT t t"] nonneg_cexpr_map_vars)
         auto
  qed (insert vars ctype edc_add.prems, auto)

next
  case (edc_inv vs vs' \<Gamma> \<delta> e f t)
  hence t: "\<Gamma> \<turnstile> e : t" and [simp]: "t = REAL"
    by (elim expr_typing_opE, force split: pdf_type.split_asm)+
  note invar = cdens_ctxt_invarD[OF edc_inv.prems(2)]
  let ?expr = "(f \<circ>\<^sub>c (\<lambda>\<^sub>cx. inverse\<^sub>c x)) *\<^sub>c (\<lambda>\<^sub>cx. (inverse\<^sub>c x) ^\<^sub>c CInt 2)"

  have dens: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr f \<rho> x))" and
         wf: "is_density_expr (vs, vs', \<Gamma>, \<delta>) REAL f" using edc_inv t by simp_all
  note wf' = is_density_exprD[OF wf]
  from wf' have ctype: "case_nat REAL \<Gamma> \<turnstile>\<^sub>c ?expr : REAL"
    by (auto intro!: cet_op_intros cexpr_typing_cexpr_comp cet_var' cet_val')
  from wf' have vars': "free_vars (f \<circ>\<^sub>c (\<lambda>\<^sub>cx. inverse\<^sub>c x)) \<subseteq> shift_var_set (set vs')"
    by (intro order.trans[OF free_vars_cexpr_comp]) auto
  hence vars: "free_vars ?expr \<subseteq> shift_var_set (set vs')" using free_vars_cexpr_comp by simp

  show ?case
  proof (intro conjI is_density_exprI, simp only: dens_ctxt_\<alpha>_def prod.case, rule hd_cong[OF hd_inv])
    fix \<rho> x assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
               and x: "x \<in> space (stock_measure REAL)"
    from x obtain x' where [simp]: "x = RealVal x'" by (auto simp: val_type_eq_REAL)
    from \<rho> and wf' have "val_type (cexpr_sem (case_nat (RealVal (inverse x')) \<rho>) f) = REAL"
      by (intro val_type_cexpr_sem[OF _ _ case_nat_in_state_measure ])
         (auto simp: type_universe_def simp del: type_universe_type)
    thus "ennreal (eval_cexpr f \<rho> (op_sem Inverse x)) * ennreal ((inverse (extract_real x))\<^sup>2) =
            ennreal (eval_cexpr ?expr \<rho> x)"
      by (auto simp: eval_cexpr_def lift_RealVal_def lift_RealIntVal2_def ennreal_mult''
                     extract_real_def cexpr_sem_cexpr_comp elim!: REAL_E)
  next
    have "nonneg_cexpr (shift_var_set (set vs')) (case_nat REAL \<Gamma>) (inverse\<^sub>c (CVar 0) ^\<^sub>c CInt 2)"
      by (auto intro!: nonneg_cexprI simp: space_state_measure_shift_iff val_type_eq_REAL lift_RealVal_eq)
    then show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) ?expr"
      using wf'
      by (intro nonneg_cexpr_Mult nonneg_cexpr_comp vars')
         (auto intro!: cet_op_intros cexpr_typing_cexpr_comp cet_var' cet_val')
  qed (insert edc_inv.prems ctype vars dens,
       auto intro!: density_context_\<alpha> simp: dens_ctxt_\<alpha>_def)

next
  case (edc_exp vs vs' \<Gamma> \<delta> e f t)
  hence t: "\<Gamma> \<turnstile> e : t" and [simp]: "t = REAL"
    by (elim expr_typing_opE, force split: pdf_type.split_asm)+
  note invar = cdens_ctxt_invarD[OF edc_exp.prems(2)]
  let ?expr = "(\<lambda>\<^sub>cx. IF\<^sub>c CReal 0 <\<^sub>c x THEN (f \<circ>\<^sub>c ln\<^sub>c x) *\<^sub>c inverse\<^sub>c x ELSE CReal 0)"

  have dens: "dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr f \<rho> x))" and
         wf: "is_density_expr (vs, vs', \<Gamma>, \<delta>) REAL f" using edc_exp t by simp_all
  note wf' = is_density_exprD[OF wf]
  from wf' have ctype: "case_nat REAL \<Gamma> \<turnstile>\<^sub>c ?expr : REAL"
    by (auto intro!: cet_if cet_op_intros cet_var' cet_val' cexpr_typing_cexpr_comp)
  from wf' have "free_vars (f \<circ>\<^sub>c (\<lambda>\<^sub>cx. ln\<^sub>c x)) \<subseteq> shift_var_set (set vs')"
    by (intro order.trans[OF free_vars_cexpr_comp]) auto
  hence vars: "free_vars ?expr \<subseteq> shift_var_set (set vs')" using free_vars_cexpr_comp by simp

  show ?case
  proof (intro conjI is_density_exprI, simp only: dens_ctxt_\<alpha>_def prod.case, rule hd_cong[OF hd_exp])
    fix \<rho> x assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
               and x: "x \<in> space (stock_measure REAL)"
    from x obtain x' where [simp]: "x = RealVal x'" by (auto simp: val_type_eq_REAL)
    from \<rho> and wf' have "val_type (cexpr_sem (case_nat (RealVal (ln x')) \<rho>) f) = REAL"
      by (intro val_type_cexpr_sem[OF _ _ case_nat_in_state_measure ])
         (auto simp: type_universe_def simp del: type_universe_type)
    thus "(if 0 < extract_real x then ennreal (eval_cexpr f \<rho> (lift_RealVal safe_ln x)) *
              ennreal (inverse (extract_real x)) else 0) = ennreal (eval_cexpr ?expr \<rho> x)"
      by (auto simp: eval_cexpr_def lift_RealVal_def lift_RealIntVal2_def lift_Comp_def ennreal_mult''
                     extract_real_def cexpr_sem_cexpr_comp elim!: REAL_E)
  next
    show "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) ?expr"
    proof (rule nonneg_cexprI_shift)
      fix x \<sigma> assume "x \<in> type_universe t" and \<sigma>: "\<sigma> \<in> space (state_measure (set vs') \<Gamma>)"
      then obtain r where "x = RealVal r"
        by (auto simp: val_type_eq_REAL)
      moreover note \<sigma> nonneg_cexprD[OF is_density_exprD_nonneg[OF wf], of "case_nat (RealVal (ln r)) \<sigma>"]
      moreover have "val_type (cexpr_sem (case_nat (RealVal (ln r)) \<sigma>) f) = REAL"
        using \<sigma> by (intro val_type_cexpr_sem[OF wf'(1,2)] case_nat_in_state_measure) auto
      ultimately show "0 \<le> extract_real
                 (cexpr_sem (case_nat x \<sigma>)
                   (IF\<^sub>c CReal 0 <\<^sub>c CVar 0 THEN (f \<circ>\<^sub>c ln\<^sub>c (CVar 0)) /\<^sub>c CVar 0 ELSE CReal 0))"
        by (auto simp: lift_Comp_def lift_RealVal_eq cexpr_sem_cexpr_comp val_type_eq_REAL
                       case_nat_in_state_measure lift_RealIntVal2_def)
    qed
  qed (insert edc_exp.prems ctype vars dens,
       auto intro!: density_context_\<alpha> simp: dens_ctxt_\<alpha>_def)
qed


lemma expr_has_density_cexpr_sound:
  assumes "([], [], \<Gamma>, CReal 1) \<turnstile>\<^sub>c e \<Rightarrow> f" "\<Gamma> \<turnstile> e : t" "free_vars e = {}"
  shows "has_subprob_density (expr_sem \<sigma> e) (stock_measure t) (\<lambda>x. ennreal (eval_cexpr f \<sigma> x))"
        "\<forall>x\<in>type_universe t. 0 \<le> extract_real (cexpr_sem (case_nat x \<sigma>) f)"
        "\<Gamma>' 0 = t \<Longrightarrow> \<Gamma>' \<turnstile>\<^sub>c f : REAL"
        "free_vars f \<subseteq> {0}"
proof-
  have "dens_ctxt_\<alpha> ([], [], \<Gamma>, CReal 1) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr f \<rho> x)) \<and>
          is_density_expr ([], [], \<Gamma>, CReal 1) t f" using assms
    by (intro expr_has_density_cexpr_sound_aux assms cdens_ctxt_invarI nonneg_cexprI subprob_cexprI)
       (auto simp: state_measure_def PiM_empty cexpr_type_Some_iff[symmetric] extract_real_def)
  hence dens: "dens_ctxt_\<alpha> ([], [], \<Gamma>, CReal 1) \<turnstile>\<^sub>d e \<Rightarrow> (\<lambda>\<rho> x. ennreal (eval_cexpr f \<rho> x))"
    and wf: "is_density_expr ([], [], \<Gamma>, CReal 1) t f" using assms by blast+

  have "has_subprob_density (expr_sem \<sigma> e) (stock_measure t)
             (\<lambda>x. ennreal (eval_cexpr f (\<lambda>_. undefined) x))" (is ?P) using dens assms
    by (intro expr_has_density_sound) (auto simp: dens_ctxt_\<alpha>_def extract_real_def one_ennreal_def)
  also have "\<And>x. cexpr_sem (case_nat x (\<lambda>_. undefined)) f = cexpr_sem (case_nat x \<sigma>) f"
    using is_density_exprD[OF wf]
    by (intro cexpr_sem_eq_on_vars) (auto split: nat.split simp: shift_var_set_def)
  hence "?P \<longleftrightarrow> has_subprob_density (expr_sem \<sigma> e) (stock_measure t)
                      (\<lambda>x. ennreal (eval_cexpr f \<sigma> x))"
    by (intro has_subprob_density_cong) (simp add: eval_cexpr_def)
  finally show "..." .

  from is_density_exprD[OF wf] show vars: "free_vars f \<subseteq> {0}" by (auto simp: shift_var_set_def)

  show "\<forall>x\<in>type_universe t. 0 \<le> extract_real (cexpr_sem (case_nat x \<sigma>) f)"
  proof
    fix v assume v: "v \<in> type_universe t"
    then have "0 \<le> extract_real (cexpr_sem (case_nat v (\<lambda>_. undefined)) f)"
      by (intro nonneg_cexprD[OF wf[THEN is_density_exprD_nonneg]] case_nat_in_state_measure)
         (auto simp: space_state_measure)
    also have "cexpr_sem (case_nat v (\<lambda>_. undefined)) f = cexpr_sem (case_nat v \<sigma>) f"
      using \<open>free_vars f \<subseteq> {0}\<close> by (intro cexpr_sem_eq_on_vars) auto
    finally show "0 \<le> extract_real (cexpr_sem (case_nat v \<sigma>) f)" .
  qed

  assume "\<Gamma>' 0 = t"
  thus "\<Gamma>' \<turnstile>\<^sub>c f : REAL"
    by (intro cexpr_typing_cong'[OF is_density_exprD(1)[OF wf]])
       (insert vars, auto split: nat.split)
qed

inductive expr_compiles_to :: "expr \<Rightarrow> pdf_type \<Rightarrow> cexpr \<Rightarrow> bool" ("_ : _ \<Rightarrow>\<^sub>c _" [10,0,10] 10)
  for e t f where
  "(\<lambda>_. UNIT) \<turnstile> e : t \<Longrightarrow> free_vars e = {} \<Longrightarrow>
      ([], [], \<lambda>_. UNIT, CReal 1) \<turnstile>\<^sub>c e \<Rightarrow> f \<Longrightarrow>
      e : t \<Rightarrow>\<^sub>c f"

code_pred expr_compiles_to .

lemma expr_compiles_to_sound:
  assumes "e : t \<Rightarrow>\<^sub>c f"
  shows  "expr_sem \<sigma> e = density (stock_measure t) (\<lambda>x. ennreal (eval_cexpr f \<sigma>' x))"
         "\<forall>x\<in>type_universe t. eval_cexpr f \<sigma>' x \<ge> 0"
         "\<Gamma> \<turnstile> e : t"
         "t \<cdot> \<Gamma>' \<turnstile>\<^sub>c f : REAL"
         "free_vars f \<subseteq> {0}"
proof-
  let ?\<Gamma> = "\<lambda>_. UNIT"
  from assms have A: "([], [], ?\<Gamma>, CReal 1) \<turnstile>\<^sub>c e \<Rightarrow> f" "?\<Gamma> \<turnstile> e : t" "free_vars e = {}"
     by (simp_all add: expr_compiles_to.simps)
  hence "expr_sem \<sigma> e = expr_sem \<sigma>' e" by (intro expr_sem_eq_on_vars) simp
  with expr_has_density_cexpr_sound[OF A]
    show "expr_sem \<sigma> e = density (stock_measure t) (\<lambda>x. ennreal (eval_cexpr f \<sigma>' x))"
         "\<forall>x\<in>type_universe t. eval_cexpr f \<sigma>' x \<ge> 0"
         "t \<cdot> \<Gamma>' \<turnstile>\<^sub>c f : REAL"
         "free_vars f \<subseteq> {0}" unfolding has_subprob_density_def has_density_def eval_cexpr_def
         by (auto intro!: nonneg_cexprD case_nat_in_state_measure)
  from assms have "(\<lambda>_. UNIT) \<turnstile> e : t" by (simp add: expr_compiles_to.simps)
  from this and assms show "\<Gamma> \<turnstile> e : t"
    by (subst expr_typing_cong) (auto simp: expr_compiles_to.simps)
qed


section \<open>Tests\<close>

values "{(t, f) |t f. Val (IntVal 42) : t \<Rightarrow>\<^sub>c f}"
values "{(t, f) |t f. Minus $$ (Val (IntVal 42)) : t \<Rightarrow>\<^sub>c f}"
values "{(t, f) |t f. Fst $$ (Val <|IntVal 13, IntVal 37|>) : t \<Rightarrow>\<^sub>c f}"
values "{(t, f) |t f. Random Bernoulli (Val (RealVal 0.5))  : t \<Rightarrow>\<^sub>c f}"
values "{(t, f) |t f. Add $$ <Val (IntVal 37), Minus $$ (Val (IntVal 13))> : t \<Rightarrow>\<^sub>c f}"
values "{(t, f) |t f. LET Val (IntVal 13) IN LET Minus $$ (Val (IntVal 37)) IN
                          Add $$ <Var 0, Var 1> : t \<Rightarrow>\<^sub>c f}"
values "{(t, f) |t f. IF Random Bernoulli (Val (RealVal 0.5)) THEN
                        Random Bernoulli (Val (RealVal 0.25))
                      ELSE
                        Random Bernoulli (Val (RealVal 0.75)) : t \<Rightarrow>\<^sub>c f}"
values "{(t, f) |t f. LET Random Bernoulli (Val (RealVal 0.5)) IN
                        IF Var 0 THEN
                          Random Bernoulli (Val (RealVal 0.25))
                        ELSE
                          Random Bernoulli (Val (RealVal 0.75)) : t \<Rightarrow>\<^sub>c f}"
values "{(t, f) |t f. LET Random Gaussian <Val (RealVal 0), Val (RealVal 1)> IN
                        LET Random Gaussian <Val (RealVal 0), Val (RealVal 1)> IN
                          Add $$ <Var 0, Var 1> : t \<Rightarrow>\<^sub>c f}"
values "{(t, f) |t f. LET Random UniformInt <Val (IntVal 1), Val (IntVal 6)> IN
                        LET Random UniformInt <Val (IntVal 1), Val (IntVal 6)> IN
                          Add $$ <Var 0, Var 1> : t \<Rightarrow>\<^sub>c f}"


(* Example from the paper by Bhat et.al. *)

values "{(t, f) |t f. LET Random UniformReal <Val (RealVal 0), Val (RealVal 1)> IN
                        LET Random Bernoulli (Var 0) IN
                          IF Var 0 THEN Add $$ <Var 1, Val (RealVal 1)> ELSE Var 1 : t \<Rightarrow>\<^sub>c f}"

(* Simplification of constant expression yields:
  \<integral>b. (IF 0 \<le> x - 1 \<and> x - 1 \<le> 1 THEN 1 ELSE 0) *
      (IF 0 \<le> x - 1 \<and> x - 1 \<le> 1 THEN IF b THEN x - 1 ELSE 1 - (x - 1) ELSE 0) * \<langle>b\<rangle> +
  \<integral>b. (IF 0 \<le> x \<and> x \<le> 1 THEN 1 ELSE 0) *
      (IF 0 \<le> x \<and> x \<le> 1 THEN IF b THEN x ELSE 1 - x ELSE 0) * \<langle>\<not>b\<rangle>
*)

(* Further simplification yields:
   (\<integral>b. \<langle>0 \<le> x-1 \<le> 1\<rangle> * (IF b THEN x-1 ELSE 2-x) * \<langle>b\<rangle>) +
   (\<integral>b. \<langle>0 \<le> x \<le> 1\<rangle> * (IF b THEN x ELSE 1-x) * \<langle>\<not>b\<rangle>)
*)

(* Further simplification yields:
  \<langle>1 \<le> x \<le> 2\<rangle>*(x-1) + \<langle>0 \<le> x \<le> 1\<rangle>*(1-x)
*)

(* Mathematica input:
   Piecewise[{{x-1, 1 <= x && x <= 2}, {1-x, 0 <= x && x <= 1}}]
*)

definition "cthulhu skill \<equiv>
  LET Random UniformInt (Val <|IntVal 1, IntVal 100|>)
   IN IF Less $$ <Val (IntVal skill), Var 0> THEN
        Val (IntVal skill)
      ELSE IF Or $$ <Less $$ <Var 0, Val (IntVal 6)>,
                     Less $$ <Mult $$ <Var 0, Val (IntVal 5)>,
                                  Add $$ <Val (IntVal skill), Val (IntVal 1)> > > THEN
        Add $$ <IF Less $$ <Val (IntVal skill),
                            Random UniformInt <Val (IntVal 1), Val (IntVal 100)> > THEN
                  Random UniformInt <Val (IntVal 1), Val (IntVal 10)>
                ELSE
                  Val (IntVal 0),
          Val (IntVal skill)>
      ELSE Val (IntVal skill)"

definition "cthulhu' (skill :: int) =
LET Random UniformInt (Val <|IntVal 1, IntVal 100|>)
   IN IF Less $$ <Val (IntVal skill), Var 0> THEN
        Val (IntVal skill)
      ELSE IF Or $$ <Less $$ <Var 0, Val (IntVal 6)>,
                     Less $$ <Mult $$ <Var 0, Val (IntVal 5)>,
                                  Add $$ <Val (IntVal skill), Val (IntVal 1)> > > THEN
        LET Random UniformInt (Val <|IntVal 1, IntVal 100|>)
        IN  Add $$ <IF Less $$ <Val (IntVal skill), Var 1 > THEN
                      Random UniformInt (Val <|IntVal 1, IntVal 10|>)
                    ELSE
                      Val (IntVal 0),
              Val (IntVal skill)>
      ELSE Val (IntVal skill)"

values "{(t, f) |t f. cthulhu' 42 : t \<Rightarrow>\<^sub>c f}"

end
