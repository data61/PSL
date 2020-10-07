(*
  Theory: PDF_Target_Density_Contexts.thy
  Authors: Manuel Eberl

  Concrete density contexts and operations on them as expressions in the
  target language
*)

section \<open>Concrete Density Contexts\<close>

theory PDF_Target_Density_Contexts
imports PDF_Density_Contexts PDF_Target_Semantics
begin

subsection \<open>Definition\<close>

type_synonym cdens_ctxt = "vname list \<times> vname list \<times> tyenv \<times> cexpr"

definition dens_ctxt_\<alpha> :: "cdens_ctxt \<Rightarrow> dens_ctxt" where
  "dens_ctxt_\<alpha> \<equiv> \<lambda>(vs,vs',\<Gamma>,\<delta>). (set vs, set vs', \<Gamma>, \<lambda>\<sigma>. extract_real (cexpr_sem \<sigma> \<delta>))"

definition shift_vars :: "nat list \<Rightarrow> nat list" where
  "shift_vars vs = 0 # map Suc vs"

lemma set_shift_vars[simp]: "set (shift_vars vs) = shift_var_set (set vs)"
  unfolding shift_vars_def shift_var_set_def by simp

definition is_density_expr :: "cdens_ctxt \<Rightarrow> pdf_type \<Rightarrow> cexpr \<Rightarrow> bool" where
  "is_density_expr \<equiv> \<lambda>(vs,vs',\<Gamma>,\<delta>) t e.
    case_nat t \<Gamma> \<turnstile>\<^sub>c e : REAL \<and>
    free_vars e \<subseteq> shift_var_set (set vs') \<and>
    nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) e"

lemma is_density_exprI:
  "case_nat t \<Gamma> \<turnstile>\<^sub>c e : REAL \<Longrightarrow>
    free_vars e \<subseteq> shift_var_set (set vs') \<Longrightarrow>
    nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) e \<Longrightarrow>
    is_density_expr (vs, vs', \<Gamma>, \<delta>) t e"
  unfolding is_density_expr_def by simp

lemma is_density_exprD:
  assumes "is_density_expr (vs, vs', \<Gamma>, \<delta>) t e"
  shows "case_nat t \<Gamma> \<turnstile>\<^sub>c e : REAL" "free_vars e \<subseteq> shift_var_set (set vs')"
    and is_density_exprD_nonneg: "nonneg_cexpr (shift_var_set (set vs')) (case_nat t \<Gamma>) e"
  using assms unfolding is_density_expr_def by simp_all


lemma density_context_\<alpha>:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  shows "density_context (set vs) (set vs') \<Gamma> (\<lambda>\<sigma>. extract_real (cexpr_sem \<sigma> \<delta>))"
proof (unfold density_context_def, intro allI ballI conjI impI subprob_spaceI)
  show "(\<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>)))
            \<in> borel_measurable (state_measure (set vs \<union> set vs') \<Gamma>)"
    apply (intro measurable_compose[OF _ measurable_ennreal] measurable_compose[OF _ measurable_extract_real])
    apply (insert cdens_ctxt_invarD[OF assms], auto)
    done
  note [measurable] = this

  fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
  let ?M = "dens_ctxt_measure (set vs, set vs', \<Gamma>, \<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>))) \<rho>"
  from \<rho> have "(\<lambda>\<sigma>. merge (set vs) (set vs') (\<sigma>, \<rho>))
                    \<in> measurable (state_measure (set vs) \<Gamma>) (state_measure (set vs \<union> set vs') \<Gamma>)"
    unfolding state_measure_def by simp
  hence "emeasure ?M (space ?M) =
             \<integral>\<^sup>+x. ennreal (extract_real (cexpr_sem (merge (set vs) (set vs') (x, \<rho>)) \<delta>))
                \<partial>state_measure (set vs) \<Gamma>" (is "_ = ?I")
    using \<rho> unfolding dens_ctxt_measure_def state_measure'_def
    by (simp add: emeasure_density nn_integral_distr, intro nn_integral_cong)
       (simp_all split: split_indicator add: merge_in_state_measure)
  also from cdens_ctxt_invarD[OF assms] have "subprob_cexpr (set vs) (set vs') \<Gamma> \<delta>" by simp
  with \<rho> have "?I \<le> 1" unfolding subprob_cexpr_def by blast
  finally show "emeasure ?M (space ?M) \<le> 1" .
qed (insert cdens_ctxt_invarD[OF assms], simp_all add: nonneg_cexpr_def)


subsection \<open>Expressions for density context operations\<close>

definition marg_dens_cexpr :: "tyenv \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> cexpr \<Rightarrow> cexpr" where
  "marg_dens_cexpr \<Gamma> vs x e =
      map_vars (\<lambda>y. if y = x then 0 else Suc y) (integrate_vars \<Gamma> (filter (\<lambda>y. y \<noteq> x) vs) e)"

lemma free_vars_marg_dens_cexpr:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  shows "free_vars (marg_dens_cexpr \<Gamma> vs x \<delta>) \<subseteq> shift_var_set (set vs')"
proof-
  have "free_vars (marg_dens_cexpr \<Gamma> vs x \<delta>) \<subseteq> shift_var_set (free_vars \<delta> - set vs)"
    unfolding marg_dens_cexpr_def shift_var_set_def by auto
  also from cdens_ctxt_invarD[OF assms] have "... \<subseteq> shift_var_set (set vs')"
      unfolding shift_var_set_def by auto
  finally show ?thesis .
qed

lemma cexpr_typing_marg_dens_cexpr[intro]:
  "\<Gamma> \<turnstile>\<^sub>c \<delta> : REAL \<Longrightarrow> case_nat (\<Gamma> x) \<Gamma> \<turnstile>\<^sub>c marg_dens_cexpr \<Gamma> vs x \<delta> : REAL"
  unfolding marg_dens_cexpr_def
  by (rule cexpr_typing_map_vars, rule cexpr_typing_cong', erule cexpr_typing_integrate_vars) simp

lemma cexpr_sem_marg_dens:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  assumes x: "x \<in> set vs" and \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
  shows "AE v in stock_measure (\<Gamma> x).
           ennreal (extract_real (cexpr_sem (case_nat v \<rho>) (marg_dens_cexpr \<Gamma> vs x \<delta>))) =
               marg_dens (dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>)) x \<rho> v"
proof-
  note invar = cdens_ctxt_invarD[OF assms(1)]
  let ?vs = "filter (\<lambda>y. y \<noteq> x) vs"
  note cdens_ctxt_invar_imp_integrable[OF assms(1) \<rho>]
  moreover from x have insert_eq: "insert x {xa \<in> set vs. xa \<noteq> x} = set vs" by auto
  ultimately have integrable:
    "AE v in stock_measure (\<Gamma> x).
          integrable (state_measure (set ?vs) \<Gamma>)
              (\<lambda>\<sigma>. extract_real (cexpr_sem (merge (set ?vs) (insert x (set vs')) (\<sigma>, \<rho>(x := v))) \<delta>))"
    using invar x \<rho> by (intro integrable_cexpr_projection) auto

  show ?thesis
  proof (rule AE_mp[OF integrable], rule AE_I2, intro impI)
    fix v assume v: "v \<in> space (stock_measure (\<Gamma> x))"
    assume integrable:
      "integrable (state_measure (set ?vs) \<Gamma>)
           (\<lambda>\<sigma>. extract_real (cexpr_sem (merge (set ?vs) (insert x (set vs')) (\<sigma>, \<rho>(x := v))) \<delta>))"

    from v and \<rho> have \<rho>': "(\<rho>(x := v)) \<in> space (state_measure (set (x#vs')) \<Gamma>)"
      by (auto simp: state_measure_def space_PiM split: if_split_asm)
    have "cexpr_sem (case_nat v \<rho>) (marg_dens_cexpr \<Gamma> vs x \<delta>) =
            cexpr_sem (case_nat v \<rho> \<circ> (\<lambda>y. if y = x then 0 else Suc y))
                   (integrate_vars \<Gamma> [y\<leftarrow>vs . y \<noteq> x] \<delta>)" (is "_ = ?A")
      unfolding marg_dens_cexpr_def by (simp add: cexpr_sem_map_vars)
    also have "\<And>y. y \<in> free_vars (integrate_vars \<Gamma> [y\<leftarrow>vs . y \<noteq> x] \<delta>)
                  \<Longrightarrow> (case_nat v \<rho> \<circ> (\<lambda>y. if y = x then 0 else Suc y)) y = (\<rho>(x := v)) y"
      unfolding o_def by simp
    hence "?A = cexpr_sem (\<rho>(x := v)) (integrate_vars \<Gamma> [y\<leftarrow>vs . y \<noteq> x] \<delta>)" by (rule cexpr_sem_eq_on_vars)
    also from x have "insert x {xa \<in> set vs. xa \<noteq> x} \<union> set vs' = set vs \<union> set vs'" by auto
    hence "extract_real (cexpr_sem (\<rho>(x := v)) (integrate_vars \<Gamma> [y\<leftarrow>vs . y \<noteq> x] \<delta>)) =
                  \<integral>\<^sup>+\<sigma>. extract_real (cexpr_sem (merge (set ?vs) (insert x (set vs')) (\<sigma>, \<rho>(x := v))) \<delta>)
                     \<partial>state_measure (set ?vs) \<Gamma>"
      using \<rho>' invar integrable by (subst cexpr_sem_integrate_vars') (auto )
    also from x have "(\<lambda>\<sigma>. merge (set ?vs) (insert x (set vs')) (\<sigma>, \<rho>(x := v))) =
                         (\<lambda>\<sigma>. merge (set vs) (set vs') (\<sigma>(x := v), \<rho>))"
      by (intro ext) (auto simp: merge_def)
    also from x have "set ?vs = set vs - {x}" by auto
    also have "(\<integral>\<^sup>+\<sigma>. extract_real (cexpr_sem (merge (set vs) (set vs') (\<sigma>(x := v), \<rho>)) \<delta>)
                     \<partial>state_measure (set vs - {x}) \<Gamma>) =
                 marg_dens (dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>)) x \<rho> v"
      unfolding marg_dens_def dens_ctxt_\<alpha>_def by simp
    finally show "ennreal (extract_real (cexpr_sem (\<lambda>a. case a of 0 \<Rightarrow> v | Suc a \<Rightarrow> \<rho> a)
                                               (marg_dens_cexpr \<Gamma> vs x \<delta>))) =
                    marg_dens (dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>)) x \<rho> v" .
  qed
qed

lemma nonneg_cexpr_sem_marg_dens:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  assumes x: "x \<in> set vs" and \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
  assumes v: "v \<in> type_universe (\<Gamma> x)"
  shows "extract_real (cexpr_sem (case_nat v \<rho>) (marg_dens_cexpr \<Gamma> vs x \<delta>)) \<ge> 0"
proof-
  note invar = cdens_ctxt_invarD[OF assms(1)]
  from assms have \<rho>: "case_nat v \<rho> \<circ> (\<lambda>y. if y = x then 0 else Suc y)
                        \<in> space (state_measure (set (x#vs')) \<Gamma>)"
    by (force simp: state_measure_def space_PiM o_def split: if_split_asm)
  moreover from x have "insert x {xa \<in> set vs. xa \<noteq> x} \<union> set vs' = set vs \<union> set vs'" by auto
  ultimately show ?thesis using assms invar unfolding marg_dens_cexpr_def
    by (subst cexpr_sem_map_vars, intro nonneg_cexpr_sem_integrate_vars[of _ "set (x#vs')"]) auto
qed


definition marg_dens2_cexpr :: "tyenv \<Rightarrow> vname list \<Rightarrow> vname \<Rightarrow> vname \<Rightarrow> cexpr \<Rightarrow> cexpr" where
  "marg_dens2_cexpr \<Gamma> vs x y e =
     (cexpr_comp_aux (Suc x) (fst\<^sub>c (CVar 0))
        (cexpr_comp_aux (Suc y) (snd\<^sub>c (CVar 0))
            (map_vars Suc (integrate_vars \<Gamma> (filter (\<lambda>z. z \<noteq> x \<and> z \<noteq> y) vs) e))))"


lemma free_vars_marg_dens2_cexpr:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  shows "free_vars (marg_dens2_cexpr \<Gamma> vs x y \<delta>) \<subseteq> shift_var_set (set vs')"
proof-
  have "free_vars (marg_dens2_cexpr \<Gamma> vs x y \<delta>) \<subseteq>
            shift_var_set (free_vars \<delta> - set vs)"
    unfolding marg_dens2_cexpr_def using cdens_ctxt_invarD[OF assms(1)]
    apply (intro order.trans[OF free_vars_cexpr_comp_aux] Un_least)
    apply (subst Diff_subset_conv, intro order.trans[OF free_vars_cexpr_comp_aux])
    apply (auto simp: shift_var_set_def)
    done
  also from cdens_ctxt_invarD[OF assms(1)] have "... \<subseteq> shift_var_set (set vs')"
      unfolding shift_var_set_def by auto
  finally show ?thesis .
qed

lemma cexpr_typing_marg_dens2_cexpr[intro]:
  assumes "\<Gamma> \<turnstile>\<^sub>c \<delta> : REAL"
  shows "case_nat (PRODUCT (\<Gamma> x) (\<Gamma> y)) \<Gamma> \<turnstile>\<^sub>c marg_dens2_cexpr \<Gamma> vs x y \<delta> : REAL"
proof-
  have A: "(case_nat (PRODUCT (\<Gamma> x) (\<Gamma> y)) \<Gamma>) (Suc x := \<Gamma> x, Suc y := \<Gamma> y) \<circ> Suc = \<Gamma>"
    by (intro ext) (auto split: nat.split)
  show ?thesis unfolding marg_dens2_cexpr_def
  apply (rule cexpr_typing_cexpr_comp_aux[of _ _ "\<Gamma> x"])
  apply (rule cexpr_typing_cexpr_comp_aux[of _ _ "\<Gamma> y"])
  apply (rule cexpr_typing_map_vars, subst A, rule cexpr_typing_integrate_vars[OF assms])
  apply (rule cet_op, rule cet_var, simp, rule cet_op, rule cet_var, simp)
  done
qed

lemma cexpr_sem_marg_dens2:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  assumes x: "x \<in> set vs" and y: "y \<in> set vs" and "x \<noteq> y"
  assumes \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
  shows "AE z in stock_measure (PRODUCT (\<Gamma> x) (\<Gamma> y)).
           ennreal (extract_real (cexpr_sem (case_nat z \<rho>) (marg_dens2_cexpr \<Gamma> vs x y \<delta>))) =
               marg_dens2 (dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>)) x y \<rho> z"
proof-
  note invar = cdens_ctxt_invarD[OF assms(1)]
  let ?f = "\<lambda>x. ennreal (extract_real (cexpr_sem x \<delta>))"
  let ?vs = "filter (\<lambda>z. z \<noteq> x \<and> z \<noteq> y) vs"
  interpret product_sigma_finite "\<lambda>x. stock_measure (\<Gamma> x)"
    unfolding product_sigma_finite_def by simp
  interpret sf_PiM: sigma_finite_measure "PiM (set ?vs) (\<lambda>x. stock_measure (\<Gamma> x))"
    by (intro sigma_finite) simp

  have meas: "(\<lambda>\<sigma>. extract_real (cexpr_sem (merge (set vs) (set vs') (\<sigma>, \<rho>)) \<delta>))
                 \<in> borel_measurable (state_measure (set vs) \<Gamma>)" using assms invar
    by (intro measurable_cexpr_sem') simp_all
  from x y have insert_eq: "insert x (insert y (set ?vs)) = set vs" by auto
  from x y have insert_eq': "insert y (insert x (set ?vs)) = set vs" by auto
  have meas_upd1: "(\<lambda>(\<sigma>,v). \<sigma>(y := v)) \<in>
      measurable (PiM (insert x (set vs)) (\<lambda>x. stock_measure (\<Gamma> x)) \<Otimes>\<^sub>M stock_measure (\<Gamma> y))
                 (PiM (insert y (insert x (set vs))) (\<lambda>x. stock_measure (\<Gamma> x)))"
    using measurable_add_dim[of y "insert x (set ?vs)" "\<lambda>x. stock_measure (\<Gamma> x)"]
    by (simp only: insert_eq', simp)
  hence meas_upd2: "(\<lambda>xa. (snd xa) (x := fst (fst xa), y := snd (fst xa)))
           \<in> measurable ((stock_measure (\<Gamma> x) \<Otimes>\<^sub>M stock_measure (\<Gamma> y)) \<Otimes>\<^sub>M
                           Pi\<^sub>M (set ?vs) (\<lambda>y. stock_measure (\<Gamma> y)))
                        (Pi\<^sub>M (set vs) (\<lambda>y. stock_measure (\<Gamma> y)))"
    by (subst insert_eq'[symmetric], intro measurable_Pair_compose_split[OF measurable_add_dim])
       (simp_all del: fun_upd_apply)

  from x y have A: "set vs = {x, y} \<union> set ?vs" by auto
  have "(\<integral>\<^sup>+\<sigma>. ?f (merge (set vs) (set vs') (\<sigma>, \<rho>)) \<partial>state_measure (set vs) \<Gamma>) =
               (\<integral>\<^sup>+\<sigma>'. \<integral>\<^sup>+\<sigma>. ?f (merge (set vs) (set vs') (merge {x, y} (set ?vs) (\<sigma>', \<sigma>), \<rho>))
                  \<partial>state_measure (set ?vs) \<Gamma> \<partial>state_measure {x,y} \<Gamma>)" (is "_ = ?I")
    using meas insert_eq unfolding state_measure_def
    by (subst A, subst product_nn_integral_fold) (simp_all add: measurable_compose[OF _ measurable_ennreal])
  also have "\<And>\<sigma>' \<sigma>. merge (set vs) (set vs') (merge {x, y} (set ?vs) (\<sigma>', \<sigma>), \<rho>) =
                       merge (set vs) (set vs') (\<sigma>(x := \<sigma>' x, y := \<sigma>' y), \<rho>)"
    by (intro ext) (auto simp: merge_def)
  hence "?I = (\<integral>\<^sup>+\<sigma>'. \<integral>\<^sup>+\<sigma>. ?f (merge (set vs) (set vs') (\<sigma>(x := \<sigma>' x, y := \<sigma>' y), \<rho>))
                  \<partial>state_measure (set ?vs) \<Gamma> \<partial>state_measure {x,y} \<Gamma>)" by simp
  also have "... = \<integral>\<^sup>+z. \<integral>\<^sup>+\<sigma>. ?f (merge (set vs) (set vs') (\<sigma>(x := fst z, y := snd z), \<rho>))
                     \<partial>state_measure (set ?vs) \<Gamma> \<partial>(stock_measure (\<Gamma> x) \<Otimes>\<^sub>M stock_measure (\<Gamma> y))"
    (is "_ = ?I") using \<open>x \<noteq> y\<close> meas_upd2 \<rho> invar unfolding state_measure_def
    by (subst product_nn_integral_pair, subst measurable_split_conv,
        intro sf_PiM.borel_measurable_nn_integral)
       (auto simp: measurable_split_conv state_measure_def intro!: measurable_compose[OF _ measurable_ennreal]
            measurable_compose[OF _ measurable_cexpr_sem'] measurable_Pair )
  finally have "(\<integral>\<^sup>+\<sigma>. ?f (merge (set vs) (set vs') (\<sigma>, \<rho>)) \<partial>state_measure (set vs) \<Gamma>) = ?I" .
  moreover have "(\<integral>\<^sup>+\<sigma>. ?f (merge (set vs) (set vs') (\<sigma>, \<rho>)) \<partial>state_measure (set vs) \<Gamma>) \<noteq> \<infinity>"
    using cdens_ctxt_invar_imp_integrable[OF assms(1) \<rho>] unfolding real_integrable_def by simp
  ultimately have "?I \<noteq> \<infinity>" by simp
  hence "AE z in stock_measure (\<Gamma> x) \<Otimes>\<^sub>M stock_measure (\<Gamma> y).
           (\<integral>\<^sup>+\<sigma>. ?f (merge (set vs) (set vs') (\<sigma>(x := fst z, y := snd z), \<rho>))
               \<partial>state_measure (set ?vs) \<Gamma>) \<noteq> \<infinity>" (is "AE z in _. ?P z")
    using meas_upd2 \<rho> invar unfolding state_measure_def
    by (intro nn_integral_PInf_AE sf_PiM.borel_measurable_nn_integral)
       (auto intro!: measurable_compose[OF _ measurable_ennreal] measurable_compose[OF _ measurable_cexpr_sem']
             measurable_Pair simp: measurable_split_conv state_measure_def)
  hence "AE z in stock_measure (\<Gamma> x) \<Otimes>\<^sub>M stock_measure (\<Gamma> y).
          ennreal (extract_real (cexpr_sem (case_nat (case_prod PairVal z) \<rho>) (marg_dens2_cexpr \<Gamma> vs x y \<delta>))) =
               marg_dens2 (dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>)) x y \<rho> (case_prod PairVal z)"
  proof (rule AE_mp[OF _ AE_I2[OF impI]])
    fix z assume z: "z \<in> space (stock_measure (\<Gamma> x) \<Otimes>\<^sub>M stock_measure (\<Gamma> y))"
    assume fin: "?P z"
    have "\<And>\<sigma>. merge (set vs) (set vs') (\<sigma>(x := fst z, y := snd z), \<rho>) =
                 merge (set ?vs) ({x,y} \<union> set vs') (\<sigma>, \<rho>(x := fst z, y := snd z))" using x y
      by (intro ext) (simp add: merge_def)
    hence A: "(\<integral>\<^sup>+\<sigma>. ?f (merge (set vs) (set vs') (\<sigma>(x := fst z, y := snd z), \<rho>))
                 \<partial>state_measure (set ?vs) \<Gamma>) =
              (\<integral>\<^sup>+\<sigma>. ?f (merge (set ?vs) ({x,y} \<union> set vs') (\<sigma>, \<rho>(x := fst z, y := snd z)))
                   \<partial>state_measure (set ?vs) \<Gamma>)" (is "_ = \<integral>\<^sup>+\<sigma>. ennreal (?g \<sigma>) \<partial>?M")
      by (intro nn_integral_cong) simp
    have \<rho>': "\<rho>(x := fst z, y := snd z) \<in> space (state_measure ({x, y} \<union> set vs') \<Gamma>)"
      using z \<rho> unfolding state_measure_def
      by (auto simp: space_PiM space_pair_measure split: if_split_asm)
    have integrable: "integrable ?M ?g"
    proof (intro integrableI_nonneg[OF _ AE_I2])
      show "?g \<in> borel_measurable ?M" using invar \<rho>' by (intro measurable_cexpr_sem') auto
      show "(\<integral>\<^sup>+\<sigma>. ennreal (?g \<sigma>) \<partial>?M) < \<infinity>" using fin A by (simp add: top_unique less_top)
      fix \<sigma> assume \<sigma>: "\<sigma> \<in> space ?M"
      from x y have "set ?vs \<union> ({x,y} \<union> set vs') = set vs \<union> set vs'" by auto
      thus "?g \<sigma> \<ge> 0" using merge_in_state_measure[OF \<sigma> \<rho>']
        by (intro nonneg_cexprD[OF invar(4)]) simp_all
    qed
    from x y have B: "(set ?vs \<union> ({x, y} \<union> set vs')) = set vs \<union> set vs'" by auto
    have nonneg: "nonneg_cexpr (set [z\<leftarrow>vs . z \<noteq> x \<and> z \<noteq> y] \<union> ({x, y} \<union> set vs')) \<Gamma> \<delta>"
      using invar by (subst B) simp

    have "ennreal (extract_real (cexpr_sem (case_nat (case_prod PairVal z) \<rho>) (marg_dens2_cexpr \<Gamma> vs x y \<delta>))) =
            extract_real (cexpr_sem ((case_nat <|fst z, snd z|> \<rho>) (Suc x := fst z, Suc y := snd z) \<circ> Suc)
                               (integrate_vars \<Gamma> ?vs \<delta>))"
      unfolding marg_dens2_cexpr_def
      by (simp add: cexpr_sem_cexpr_comp_aux cexpr_sem_map_vars split: prod.split)
    also have "((case_nat <|fst z, snd z|> \<rho>) (Suc x := fst z, Suc y := snd z)) \<circ> Suc =
                   \<rho>(x := fst z, y := snd z)" (is "?\<rho>1 = ?\<rho>2") by (intro ext) (simp split: nat.split)
    also have "ennreal (extract_real (cexpr_sem (\<rho>(x := fst z, y := snd z))
               (integrate_vars \<Gamma> [z\<leftarrow>vs . z \<noteq> x \<and> z \<noteq> y] \<delta>))) =
             \<integral>\<^sup>+xa. ?f (merge (set ?vs) ({x, y} \<union> set vs') (xa, \<rho>(x := fst z, y := snd z))) \<partial>?M"
      using invar assms by (intro cexpr_sem_integrate_vars'[OF \<rho>' _ _ nonneg integrable]) auto
    also have C: "set ?vs = set vs - {x, y}" by auto
    have "(\<integral>\<^sup>+xa. ?f (merge (set ?vs) ({x, y} \<union> set vs') (xa, \<rho>(x := fst z, y := snd z))) \<partial>?M) =
                 marg_dens2 (dens_ctxt_\<alpha> (vs,vs',\<Gamma>,\<delta>)) x y \<rho> (case_prod PairVal z)"
      unfolding marg_dens2_def
      by (subst A[symmetric], subst C, simp only: dens_ctxt_\<alpha>_def prod.case)
         (auto intro!: nn_integral_cong split: prod.split)
    finally show "ennreal (extract_real (cexpr_sem (case_nat (case_prod PairVal z) \<rho>)
                                            (marg_dens2_cexpr \<Gamma> vs x y \<delta>))) =
                      marg_dens2 (dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>)) x y \<rho> (case_prod PairVal z)" .
  qed
  thus ?thesis by (subst stock_measure.simps, subst AE_embed_measure[OF inj_PairVal]) simp
qed

lemma nonneg_cexpr_sem_marg_dens2:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  assumes x: "x \<in> set vs" and y: "y \<in> set vs" and \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
  assumes v: "v \<in> type_universe (PRODUCT (\<Gamma> x) (\<Gamma> y))"
  shows "extract_real (cexpr_sem (case_nat v \<rho>) (marg_dens2_cexpr \<Gamma> vs x y \<delta>)) \<ge> 0"
proof-
  from v obtain a b where v': "v = <|a, b|>" "a \<in> type_universe (\<Gamma> x)" "b \<in> type_universe (\<Gamma> y)"
    by (auto simp: val_type_eq_PRODUCT)
  let ?vs = "filter (\<lambda>z. z \<noteq> x \<and> z \<noteq> y) vs"
  note invar = cdens_ctxt_invarD[OF assms(1)]
  have A: "((case_nat v \<rho>) (Suc x := fst (extract_pair v), Suc y := snd (extract_pair v))) \<circ> Suc =
               \<rho>(x := fst (extract_pair v), y := snd (extract_pair v))" by (intro ext) auto
  have B: "\<rho>(x := fst (extract_pair v), y := snd (extract_pair v))
                     \<in> space (state_measure (set vs' \<union> {x,y}) \<Gamma>)" using x y v' \<rho>
    by (auto simp: space_state_measure split: if_split_asm)
  from x y have "set ?vs \<union> (set vs' \<union> {x, y}) = set vs \<union> set vs'" by auto
  with invar have "nonneg_cexpr (set ?vs \<union> (set vs' \<union> {x, y})) \<Gamma> \<delta>" by simp
  thus ?thesis using assms invar(1-3) A unfolding marg_dens2_cexpr_def
    by (auto simp: cexpr_sem_cexpr_comp_aux cexpr_sem_map_vars intro!: nonneg_cexpr_sem_integrate_vars[OF B])
qed



definition branch_prob_cexpr :: "cdens_ctxt \<Rightarrow> cexpr" where
  "branch_prob_cexpr \<equiv> \<lambda>(vs, vs', \<Gamma>, \<delta>). integrate_vars \<Gamma> vs \<delta>"

lemma free_vars_branch_prob_cexpr[simp]:
    "free_vars (branch_prob_cexpr (vs, vs', \<Gamma>, \<delta>)) = free_vars \<delta> - set vs"
  unfolding branch_prob_cexpr_def by simp

lemma cexpr_typing_branch_prob_cexpr[intro]:
  "\<Gamma> \<turnstile>\<^sub>c \<delta> : REAL \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>c branch_prob_cexpr (vs,vs',\<Gamma>,\<delta>) : REAL"
  unfolding branch_prob_cexpr_def
  by (simp only: prod.case, rule cexpr_typing_integrate_vars)

lemma cexpr_sem_branch_prob:
  assumes "cdens_ctxt_invar vs vs' \<Gamma> \<delta>"
  assumes \<rho>: "\<rho> \<in> space (state_measure (set vs') \<Gamma>)"
  shows "ennreal (extract_real (cexpr_sem \<rho> (branch_prob_cexpr (vs, vs', \<Gamma>, \<delta>)))) =
             branch_prob (dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>)) \<rho>"
proof-
  note invar = cdens_ctxt_invarD[OF assms(1)]
  interpret density_context "set vs" "set vs'" \<Gamma> "\<lambda>\<sigma>. extract_real (cexpr_sem \<sigma> \<delta>)"
    by (rule density_context_\<alpha>) fact
  have "ennreal (extract_real (cexpr_sem \<rho> (branch_prob_cexpr (vs, vs', \<Gamma>, \<delta>)))) =
          \<integral>\<^sup>+\<sigma>. extract_real (cexpr_sem (merge (set vs) (set vs') (\<sigma>, \<rho>)) \<delta>)
                   \<partial>state_measure (set vs) \<Gamma>" (is "_ = ?I")
    using assms(2) invar unfolding branch_prob_cexpr_def
    by (simp only: prod.case, subst cexpr_sem_integrate_vars')
       (auto intro!: cdens_ctxt_invar_imp_integrable assms)
  also have "... = branch_prob (dens_ctxt_\<alpha> (vs, vs', \<Gamma>, \<delta>)) \<rho>"
    using \<rho> unfolding dens_ctxt_\<alpha>_def by (simp only: prod.case branch_prob_altdef[of \<rho>])
  finally show ?thesis .
qed

lemma subprob_imp_subprob_cexpr:
  assumes "density_context V V' \<Gamma> (\<lambda>\<sigma>. extract_real (cexpr_sem \<sigma> \<delta>))"
  shows "subprob_cexpr V V' \<Gamma> \<delta>"
proof (intro subprob_cexprI)
  interpret density_context V V' \<Gamma> "\<lambda>\<sigma>. extract_real (cexpr_sem \<sigma> \<delta>)" by fact
  fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<lambda>\<sigma>. extract_real (cexpr_sem \<sigma> \<delta>)) \<rho>"
  from \<rho> have "(\<integral>\<^sup>+ x. ennreal (extract_real (cexpr_sem (merge V V' (x, \<rho>)) \<delta>)) \<partial>state_measure V \<Gamma>) =
                   branch_prob (V, V', \<Gamma>, \<lambda>\<sigma>. extract_real (cexpr_sem \<sigma> \<delta>)) \<rho>" (is "?I = _")
    by (subst branch_prob_altdef[symmetric]) simp_all
  also have "... = emeasure ?M (space ?M)" unfolding branch_prob_def by simp
  also have "... \<le> 1" by (rule subprob_space.emeasure_space_le_1) (simp add: subprob_space_dens \<rho>)
  finally show "?I \<le> 1" .
qed

end
