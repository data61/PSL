(*
  Theory: PDF_Density_Contexts.thy
  Authors: Manuel Eberl
*)

section \<open>Density Contexts\<close>

theory PDF_Density_Contexts
imports PDF_Semantics
begin

lemma measurable_proj_state_measure[measurable (raw)]:
    "i \<in> V \<Longrightarrow> (\<lambda>x. x i) \<in> measurable (state_measure V \<Gamma>) (\<Gamma> i)"
  unfolding state_measure_def by measurable

lemma measurable_dens_ctxt_fun_upd[measurable (raw)]:
  "f \<in> N \<rightarrow>\<^sub>M state_measure V' \<Gamma> \<Longrightarrow> V = V' \<union> {x} \<Longrightarrow>
    g \<in> N \<rightarrow>\<^sub>M stock_measure (\<Gamma> x) \<Longrightarrow>
    (\<lambda>\<omega>. (f \<omega>)(x := g \<omega>)) \<in> N \<rightarrow>\<^sub>M state_measure V \<Gamma>"
  unfolding state_measure_def
  by (rule measurable_fun_upd[where J=V']) auto

lemma measurable_case_nat_Suc_PiM:
  "(\<lambda>\<sigma>. \<sigma> \<circ> Suc) \<in> measurable (PiM (Suc ` A) (case_nat M N)) (PiM A N)"
proof-
  have "(\<lambda>\<sigma>. \<lambda>x\<in>A. \<sigma> (Suc x)) \<in> measurable
      (PiM (Suc ` A) (case_nat M N)) (PiM A (\<lambda>x. case_nat M N (Suc x)))" (is "?A")
    by measurable
  also have "?A \<longleftrightarrow> ?thesis"
    by (force intro!: measurable_cong ext simp: state_measure_def space_PiM dest: PiE_mem)
  finally show ?thesis .
qed

lemma measurable_case_nat_Suc:
  "(\<lambda>\<sigma>. \<sigma> \<circ> Suc) \<in> measurable (state_measure (Suc ` A) (case_nat t \<Gamma>)) (state_measure A \<Gamma>)"
proof-
  have "(\<lambda>\<sigma>. \<lambda>x\<in>A. \<sigma> (Suc x)) \<in> measurable
      (state_measure (Suc ` A) (case_nat t \<Gamma>)) (state_measure A (\<lambda>i. case_nat t \<Gamma> (Suc i)))" (is "?A")
    unfolding state_measure_def by measurable
  also have "?A \<longleftrightarrow> ?thesis"
    by (force intro!: measurable_cong ext simp: state_measure_def space_PiM dest: PiE_mem)
  finally show ?thesis .
qed

text \<open>A density context holds a set of variables @{term V}, their types (using @{term \<Gamma>}), and a
common density function @{term \<delta>} of the finite product space of all the variables in @{term V}.
@{term \<delta>} takes a state @{term "\<sigma> \<in> (\<Pi>\<^sub>E x\<in>V. type_universe (\<Gamma> x))"} and returns the common density
of these variables.\<close>

type_synonym dens_ctxt = "vname set \<times> vname set \<times> (vname \<Rightarrow> pdf_type) \<times> (state \<Rightarrow> ennreal)"
type_synonym expr_density = "state \<Rightarrow> val \<Rightarrow> ennreal"

definition empty_dens_ctxt :: dens_ctxt where
  "empty_dens_ctxt = ({}, {}, \<lambda>_. undefined, \<lambda>_. 1)"

definition state_measure'
    :: "vname set \<Rightarrow> vname set \<Rightarrow> (vname \<Rightarrow> pdf_type) \<Rightarrow> state \<Rightarrow> state measure" where
  "state_measure' V V' \<Gamma> \<rho> =
       distr (state_measure V \<Gamma>) (state_measure (V\<union>V') \<Gamma>) (\<lambda>\<sigma>. merge V V' (\<sigma>, \<rho>))"


text \<open>The marginal density of a variable @{term x} is obtained by integrating the common density
@{term \<delta>} over all the remaining variables.\<close>

definition marg_dens :: "dens_ctxt \<Rightarrow> vname \<Rightarrow> expr_density" where
  "marg_dens = (\<lambda>(V,V',\<Gamma>,\<delta>) x \<rho> v. \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>(x := v), \<rho>)) \<partial>state_measure (V-{x}) \<Gamma>)"

definition marg_dens2 :: "dens_ctxt \<Rightarrow> vname \<Rightarrow> vname \<Rightarrow> expr_density" where
  "marg_dens2 \<equiv> (\<lambda>(V,V',\<Gamma>,\<delta>) x y \<rho> v.
       \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>(x := fst (extract_pair v), y := snd (extract_pair v)), \<rho>))
           \<partial>state_measure (V-{x,y}) \<Gamma>)"

definition dens_ctxt_measure :: "dens_ctxt \<Rightarrow> state \<Rightarrow> state measure" where
  "dens_ctxt_measure \<equiv> \<lambda>(V,V',\<Gamma>,\<delta>) \<rho>. density (state_measure' V V' \<Gamma> \<rho>) \<delta>"

definition branch_prob :: "dens_ctxt \<Rightarrow> state \<Rightarrow> ennreal" where
  "branch_prob \<Y> \<rho> = emeasure (dens_ctxt_measure \<Y> \<rho>) (space (dens_ctxt_measure \<Y> \<rho>))"

lemma dens_ctxt_measure_nonempty[simp]:
    "space (dens_ctxt_measure \<Y> \<rho>) \<noteq> {}"
  unfolding dens_ctxt_measure_def state_measure'_def by (cases \<Y>) simp

lemma sets_dens_ctxt_measure_eq[measurable_cong]:
    "sets (dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>) = sets (state_measure (V\<union>V') \<Gamma>)"
  by (simp_all add: dens_ctxt_measure_def state_measure'_def)

lemma measurable_dens_ctxt_measure_eq:
    "measurable (dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>) = measurable (state_measure (V\<union>V') \<Gamma>)"
  by (intro ext measurable_cong_sets)
     (simp_all add: dens_ctxt_measure_def state_measure'_def)

lemma space_dens_ctxt_measure:
    "space (dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>) = space (state_measure (V\<union>V') \<Gamma>)"
  unfolding dens_ctxt_measure_def state_measure'_def by simp

definition apply_dist_to_dens :: "pdf_dist \<Rightarrow> (state \<Rightarrow> val \<Rightarrow> ennreal) \<Rightarrow> (state \<Rightarrow> val \<Rightarrow> ennreal)" where
  "apply_dist_to_dens dst f = (\<lambda>\<rho> y. \<integral>\<^sup>+x. f \<rho> x * dist_dens dst x y \<partial>stock_measure (dist_param_type dst))"

definition remove_var :: "state \<Rightarrow> state" where
  "remove_var \<sigma> = (\<lambda>x. \<sigma> (Suc x))"

lemma measurable_remove_var[measurable]:
  "remove_var \<in> measurable (state_measure (shift_var_set V) (case_nat t \<Gamma>)) (state_measure V \<Gamma>)"
proof-
  have "(\<lambda>\<sigma>. \<lambda>x\<in>V. \<sigma> (Suc x)) \<in> measurable
      (state_measure (shift_var_set V) (case_nat t \<Gamma>)) (state_measure V (\<lambda>x. case_nat t \<Gamma> (Suc x)))"
    (is "?f \<in> ?M")
    unfolding state_measure_def shift_var_set_def by measurable
  also have "\<And>x f. x \<notin> V \<Longrightarrow> f \<in> space (state_measure (shift_var_set V) (case_nat t \<Gamma>)) \<Longrightarrow>
                       f (Suc x) = undefined" unfolding state_measure_def
    by (subst (asm) space_PiM, drule PiE_arb[of _ _ _ "Suc x" for x])
       (simp_all add: space_PiM shift_var_set_def inj_image_mem_iff)
  hence "?f \<in> ?M \<longleftrightarrow> remove_var \<in> ?M" unfolding remove_var_def[abs_def] state_measure_def
    by (intro measurable_cong ext) (auto simp: space_PiM intro!: sym[of _ undefined])
  finally show ?thesis by simp
qed

lemma measurable_case_nat_undefined[measurable]:
  "case_nat undefined \<in> measurable (state_measure A \<Gamma>) (state_measure (Suc`A) (case_nat t \<Gamma>))" (is "_ \<in> ?M")
proof-
  have "(\<lambda>\<sigma>. \<lambda>x\<in>Suc`A. case_nat undefined \<sigma> x) \<in> ?M" (is "?f \<in> _")
    unfolding state_measure_def by (rule measurable_restrict) auto
  also have "?f \<in> ?M \<longleftrightarrow> ?thesis"
    by (intro measurable_cong ext)
       (auto simp: state_measure_def space_PiM dest: PiE_mem split: nat.split)
  finally show ?thesis .
qed

definition insert_dens
     :: "vname set \<Rightarrow> vname set \<Rightarrow> expr_density \<Rightarrow> (state \<Rightarrow> ennreal) \<Rightarrow> state \<Rightarrow> ennreal" where
  "insert_dens V V' f \<delta> \<equiv> \<lambda>\<sigma>. \<delta> (remove_var \<sigma>) * f (remove_var \<sigma>) (\<sigma> 0)"

definition if_dens :: "(state \<Rightarrow> ennreal) \<Rightarrow> (state \<Rightarrow> val \<Rightarrow> ennreal) \<Rightarrow> bool \<Rightarrow> (state \<Rightarrow> ennreal)" where
  "if_dens \<delta> f b \<equiv> \<lambda>\<sigma>. \<delta> \<sigma> * f \<sigma> (BoolVal b)"

definition if_dens_det :: "(state \<Rightarrow> ennreal) \<Rightarrow> expr \<Rightarrow> bool \<Rightarrow> (state \<Rightarrow> ennreal)" where
  "if_dens_det \<delta> e b \<equiv> \<lambda>\<sigma>. \<delta> \<sigma> * (if expr_sem_rf \<sigma> e = BoolVal b then 1 else 0)"

lemma measurable_if_dens:
  assumes [measurable]: "\<delta> \<in> borel_measurable M"
  assumes [measurable]: "case_prod f \<in> borel_measurable (M \<Otimes>\<^sub>M count_space (range BoolVal))"
  shows "if_dens \<delta> f b \<in> borel_measurable M"
  unfolding if_dens_def by measurable

lemma measurable_if_dens_det:
  assumes e: "\<Gamma> \<turnstile> e : BOOL" "randomfree e" "free_vars e \<subseteq> V"
  assumes [measurable]: "\<delta> \<in> borel_measurable (state_measure V \<Gamma>)"
  shows "if_dens_det \<delta> e b \<in> borel_measurable (state_measure V \<Gamma>)"
unfolding if_dens_det_def
proof (intro borel_measurable_times_ennreal assms measurable_If)
  have "{x \<in> space (state_measure V \<Gamma>). expr_sem_rf x e = BoolVal b} =
            (\<lambda>\<sigma>. expr_sem_rf \<sigma> e) -` {BoolVal b} \<inter> space (state_measure V \<Gamma>)" by auto
  also have "... \<in> sets (state_measure V \<Gamma>)"
    by (rule measurable_sets, rule measurable_expr_sem_rf[OF e]) simp_all
  finally show "{x \<in> space (state_measure V \<Gamma>). expr_sem_rf x e = BoolVal b}
                    \<in> sets (state_measure V \<Gamma>)" .
qed simp_all

locale density_context =
  fixes V V' \<Gamma> \<delta>
  assumes subprob_space_dens:
            "\<And>\<rho>. \<rho> \<in> space (state_measure V' \<Gamma>) \<Longrightarrow> subprob_space (dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>)"
      and finite_vars[simp]:     "finite V" "finite V'"
      and measurable_dens[measurable]:
                                 "\<delta> \<in> borel_measurable (state_measure (V \<union> V') \<Gamma>)"
      and disjoint:              "V \<inter> V' = {}"
begin

abbreviation "\<Y> \<equiv> (V,V',\<Gamma>,\<delta>)"

lemma branch_prob_altdef:
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  shows "branch_prob \<Y> \<rho> = \<integral>\<^sup>+ x. \<delta> (merge V V' (x, \<rho>)) \<partial>state_measure V \<Gamma>"
proof-
  have "branch_prob \<Y> \<rho> =
          \<integral>\<^sup>+ x. \<delta> (merge V V' (x, \<rho>)) * indicator (space (state_measure (V \<union> V') \<Gamma>))
                  (merge V V' (x, \<rho>)) \<partial>state_measure V \<Gamma>"
      using \<rho> unfolding branch_prob_def[abs_def] dens_ctxt_measure_def state_measure'_def
      by (simp add: emeasure_density ennreal_mult'' ennreal_indicator nn_integral_distr)
  also from \<rho> have "... = \<integral>\<^sup>+ x. \<delta> (merge V V' (x, \<rho>)) \<partial>state_measure V \<Gamma>"
    by (intro nn_integral_cong) (simp split: split_indicator add: merge_in_state_measure)
  finally show ?thesis .
qed

lemma measurable_branch_prob[measurable]:
  "branch_prob \<Y> \<in> borel_measurable (state_measure V' \<Gamma>)"
proof-
  interpret sigma_finite_measure "state_measure V \<Gamma>" by auto
  show ?thesis
    by (simp add: branch_prob_altdef cong: measurable_cong)
qed

lemma measurable_marg_dens':
  assumes [simp]: "x \<in> V"
  shows "case_prod (marg_dens \<Y> x) \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure (\<Gamma> x))"
proof-
  interpret sigma_finite_measure "state_measure (V - {x}) \<Gamma>"
    unfolding state_measure_def
    by (rule product_sigma_finite.sigma_finite, simp_all add: product_sigma_finite_def)
  from assms have "V = insert x (V - {x})" by blast
  hence A: "PiM V = PiM ..." by simp
  show ?thesis unfolding marg_dens_def
    by (simp add: insert_absorb)
qed

lemma insert_Diff: "insert x (A - B) = insert x A - (B - {x})"
  by auto

lemma measurable_marg_dens2':
  assumes "x \<in> V" "y \<in> V"
  shows "case_prod (marg_dens2 \<Y> x y) \<in>
             borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure (PRODUCT (\<Gamma> x) (\<Gamma> y)))"
proof-
  interpret sigma_finite_measure "state_measure (V - {x, y}) \<Gamma>"
    unfolding state_measure_def
    by (rule product_sigma_finite.sigma_finite, simp_all add: product_sigma_finite_def)
  have [measurable]: "V = insert x (V - {x, y}) \<union> {y}"
    using assms by blast
  show ?thesis unfolding marg_dens2_def
    by simp
qed

lemma measurable_marg_dens:
  assumes "x \<in> V" "\<rho> \<in> space (state_measure V' \<Gamma>)"
  shows "marg_dens \<Y> x \<rho> \<in> borel_measurable (stock_measure (\<Gamma> x))"
  using assms by (intro measurable_Pair_compose_split[OF measurable_marg_dens']) simp_all

lemma measurable_marg_dens2:
  assumes "x \<in> V" "y \<in> V" "x \<noteq> y" "\<rho> \<in> space (state_measure V' \<Gamma>)"
  shows "marg_dens2 \<Y> x y \<rho> \<in> borel_measurable (stock_measure (PRODUCT (\<Gamma> x) (\<Gamma> y)))"
  using assms by (intro measurable_Pair_compose_split[OF measurable_marg_dens2']) simp_all

lemma measurable_state_measure_component:
    "x \<in> V \<Longrightarrow> (\<lambda>\<sigma>. \<sigma> x) \<in> measurable (state_measure V \<Gamma>) (stock_measure (\<Gamma> x))"
  unfolding state_measure_def
  by (auto intro!: measurable_component_singleton)

lemma measurable_dens_ctxt_measure_component:
    "x \<in> V \<Longrightarrow> (\<lambda>\<sigma>. \<sigma> x) \<in> measurable (dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>) (stock_measure (\<Gamma> x))"
  unfolding dens_ctxt_measure_def state_measure'_def state_measure_def
  by (auto intro!: measurable_component_singleton)

lemma space_dens_ctxt_measure_dens_ctxt_measure':
  assumes "x \<in> V"
  shows "space (state_measure V \<Gamma>) =
             {\<sigma>(x := y) |\<sigma> y. \<sigma> \<in> space (state_measure (V-{x}) \<Gamma>) \<and> y \<in> type_universe (\<Gamma> x)}"
proof-
  from assms have "insert x (V-{x}) = V" by auto
  hence "state_measure V \<Gamma> = Pi\<^sub>M (insert x (V-{x})) (\<lambda>y. stock_measure (\<Gamma> y))"
    unfolding state_measure_def by simp
  also have "space ... = {\<sigma>(x := y) |\<sigma> y. \<sigma> \<in> space (state_measure (V-{x}) \<Gamma>) \<and> y \<in> type_universe (\<Gamma> x)}"
    unfolding state_measure_def space_PiM PiE_insert_eq
    by (simp add: image_def Bex_def) blast
  finally show ?thesis .
qed

lemma state_measure_integral_split:
  assumes "x \<in> A" "finite A"
  assumes "f \<in> borel_measurable (state_measure A \<Gamma>)"
  shows "(\<integral>\<^sup>+\<sigma>. f \<sigma> \<partial>state_measure A \<Gamma>) =
             (\<integral>\<^sup>+y. \<integral>\<^sup>+\<sigma>. f (\<sigma>(x := y)) \<partial>state_measure (A-{x}) \<Gamma> \<partial>stock_measure (\<Gamma> x))"
proof-
  interpret product_sigma_finite "\<lambda>y. stock_measure (\<Gamma> y)"
    unfolding product_sigma_finite_def by auto
  from assms have [simp]: "insert x A = A" by auto
  have "(\<integral>\<^sup>+\<sigma>. f \<sigma> \<partial>state_measure A \<Gamma>) = (\<integral>\<^sup>+\<sigma>. f \<sigma> \<partial>\<Pi>\<^sub>M v\<in>insert x (A-{x}). stock_measure (\<Gamma> v))"
    unfolding state_measure_def by simp
  also have "... = \<integral>\<^sup>+y. \<integral>\<^sup>+\<sigma>. f (\<sigma>(x := y)) \<partial>state_measure (A-{x}) \<Gamma> \<partial>stock_measure (\<Gamma> x)"
    using assms unfolding state_measure_def
    by (subst product_nn_integral_insert_rev) simp_all
  finally show ?thesis .
qed

lemma fun_upd_in_state_measure:
  "\<lbrakk>\<sigma> \<in> space (state_measure A \<Gamma>); y \<in> space (stock_measure (\<Gamma> x))\<rbrakk>
     \<Longrightarrow> \<sigma>(x := y) \<in> space (state_measure (insert x A) \<Gamma>)"
  unfolding state_measure_def by (auto simp: space_PiM split: if_split_asm)

lemma marg_dens_integral:
  fixes X :: "val set" assumes "x \<in> V" and [measurable]: "X \<in> sets (stock_measure (\<Gamma> x))"
  assumes "\<rho> \<in> space (state_measure V' \<Gamma>)"
  defines "X' \<equiv> (\<lambda>\<sigma>. \<sigma> x) -` X \<inter> space (state_measure V \<Gamma>)"
  shows "(\<integral>\<^sup>+ y. marg_dens \<Y> x \<rho> y * indicator X y \<partial>stock_measure (\<Gamma> x)) =
              (\<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>,\<rho>)) * indicator X' \<sigma> \<partial>state_measure V \<Gamma>)"
proof-
  from assms have [simp]: "insert x V = V" by auto
  interpret product_sigma_finite "\<lambda>y. stock_measure (\<Gamma> y)"
    unfolding product_sigma_finite_def by auto

  have "(\<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>,\<rho>)) * indicator X' \<sigma> \<partial>state_measure V \<Gamma>) =
           \<integral>\<^sup>+ y. \<integral>\<^sup>+ \<sigma>. \<delta> (merge V V' (\<sigma>(x := y), \<rho>)) * indicator X' (\<sigma>(x := y))
               \<partial>state_measure (V-{x}) \<Gamma> \<partial>stock_measure (\<Gamma> x)" using assms(1-3)
    by (subst state_measure_integral_split[of x]) (auto simp: X'_def)
  also have "... = \<integral>\<^sup>+ y. \<integral>\<^sup>+ \<sigma>. \<delta> (merge V V' (\<sigma>(x := y), \<rho>)) * indicator X y
                      \<partial>state_measure (V-{x}) \<Gamma> \<partial>stock_measure (\<Gamma> x)"
    by (intro nn_integral_cong)
       (auto simp: X'_def split: split_indicator dest: fun_upd_in_state_measure)
  also have "... = (\<integral>\<^sup>+ y. marg_dens \<Y> x \<rho> y * indicator X y \<partial>stock_measure (\<Gamma> x))"
    using measurable_dens_ctxt_fun_upd unfolding marg_dens_def using assms(1-3)
    by (intro nn_integral_cong) (simp split: split_indicator)
  finally show ?thesis ..
qed

lemma marg_dens2_integral:
  fixes X :: "val set"
  assumes "x \<in> V" "y \<in> V" "x \<noteq> y" and [measurable]: "X \<in> sets (stock_measure (PRODUCT (\<Gamma> x) (\<Gamma> y)))"
  assumes "\<rho> \<in> space (state_measure V' \<Gamma>)"
  defines "X' \<equiv> (\<lambda>\<sigma>. <|\<sigma> x, \<sigma> y|>) -` X \<inter> space (state_measure V \<Gamma>)"
  shows "(\<integral>\<^sup>+z. marg_dens2 \<Y> x y \<rho> z * indicator X z \<partial>stock_measure (PRODUCT (\<Gamma> x) (\<Gamma> y))) =
              (\<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>,\<rho>)) * indicator X' \<sigma> \<partial>state_measure V \<Gamma>)"
proof-
  let ?M = "stock_measure (PRODUCT (\<Gamma> x) (\<Gamma> y))"
  let ?M' = "stock_measure (\<Gamma> x) \<Otimes>\<^sub>M stock_measure (\<Gamma> y)"
  interpret product_sigma_finite "\<lambda>x. stock_measure (\<Gamma> x)"
    unfolding product_sigma_finite_def by simp
  from assms have "(\<integral>\<^sup>+ z. marg_dens2 \<Y> x y \<rho> z * indicator X z \<partial>?M) =
      \<integral>\<^sup>+z. marg_dens2 \<Y> x y \<rho> (case_prod PairVal z) * indicator X (case_prod PairVal z) \<partial>?M'"
    by (subst nn_integral_PairVal)
       (auto simp add: split_beta' intro!: borel_measurable_times_ennreal measurable_marg_dens2)

  have V'': "V - {x, y} = V - {y} - {x}"
    by auto

  from assms have A: "V = insert y (V-{y})" by blast
  from assms have B: "insert x (V-{x,y}) = V - {y}" by blast
  from assms have X'[measurable]: "X' \<in> sets (state_measure V \<Gamma>)" unfolding X'_def
    by (intro measurable_sets[OF _ assms(4)], unfold state_measure_def, subst stock_measure.simps)
       (rule measurable_Pair_compose_split[OF measurable_embed_measure2], rule inj_PairVal,
        erule measurable_component_singleton, erule measurable_component_singleton)

  have V[simp]: "insert y (V - {y}) = V" "insert x (V - {x, y}) = V - {y}" "insert y V = V"
    and [measurable]: "x \<in> V - {y}"
    using assms by auto

  have "(\<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>,\<rho>)) * indicator X' \<sigma> \<partial>state_measure V \<Gamma>) =
      (\<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>,\<rho>)) * indicator X' \<sigma> \<partial>state_measure (insert y (insert x (V-{x, y}))) \<Gamma>)"
    using assms by (intro arg_cong2[where f=nn_integral] arg_cong2[where f=state_measure]) auto
  also have "... = \<integral>\<^sup>+w. \<integral>\<^sup>+v. \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>(x := v, y := w), \<rho>)) * indicator X' (\<sigma>(x := v, y := w))
      \<partial>state_measure (V - {x, y}) \<Gamma> \<partial>stock_measure (\<Gamma> x) \<partial>stock_measure (\<Gamma> y)" (is "_ = ?I")
    unfolding state_measure_def
    using assms
    apply (subst product_nn_integral_insert_rev)
    apply (auto simp: state_measure_def[symmetric])
    apply (rule nn_integral_cong)
    apply (subst state_measure_def)
    apply (subst V(2)[symmetric])
    apply (subst product_nn_integral_insert_rev)
    apply (auto simp: state_measure_def[symmetric])
    apply measurable
    apply simp_all
    done
  also from assms(1-5)
    have "\<And>v w \<sigma>. v \<in> space (stock_measure (\<Gamma> x)) \<Longrightarrow> w \<in> space (stock_measure (\<Gamma> y))
               \<Longrightarrow> \<sigma> \<in> space (state_measure (V-{x,y}) \<Gamma>)
               \<Longrightarrow> \<sigma>(x := v, y := w) \<in> X' \<longleftrightarrow> <|v,w|> \<in> X"
    by (simp add: X'_def space_state_measure PiE_iff extensional_def)
  hence "?I = \<integral>\<^sup>+w. \<integral>\<^sup>+v. \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>(x := v, y := w), \<rho>)) * indicator X <|v,w|>
               \<partial>state_measure (V - {x,y}) \<Gamma> \<partial>stock_measure (\<Gamma> x) \<partial>stock_measure (\<Gamma> y)"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also from assms(5)
    have "... = \<integral>\<^sup>+w. \<integral>\<^sup>+v. (\<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>(x := v,y := w), \<rho>)) \<partial>state_measure (V - {x,y}) \<Gamma>)
                    * indicator X <|v,w|> \<partial>stock_measure (\<Gamma> x) \<partial>stock_measure (\<Gamma> y)"
      using assms
      apply (simp add: ennreal_mult'' ennreal_indicator)
      by (intro nn_integral_cong nn_integral_multc) (simp_all add: )
  also have "... = \<integral>\<^sup>+w. \<integral>\<^sup>+v. marg_dens2 \<Y> x y \<rho> <|v,w|> * indicator X <|v,w|>
                       \<partial>stock_measure (\<Gamma> x) \<partial>stock_measure (\<Gamma> y)"
    by (intro nn_integral_cong) (simp add: marg_dens2_def)
  also from assms(4)
    have "... = \<integral>\<^sup>+z. marg_dens2 \<Y> x y \<rho> (case_prod PairVal z) * indicator X (case_prod PairVal z)
                    \<partial>(stock_measure (\<Gamma> x) \<Otimes>\<^sub>M stock_measure (\<Gamma> y))"
      using assms
      by (subst pair_sigma_finite.nn_integral_snd[symmetric])
         (auto simp add: pair_sigma_finite_def intro!: borel_measurable_times_ennreal measurable_compose[OF _ measurable_marg_dens2])
  also have "... = \<integral>\<^sup>+z. marg_dens2 \<Y> x y \<rho> z * indicator X z \<partial>stock_measure (PRODUCT (\<Gamma> x) (\<Gamma> y))"
      apply (subst stock_measure.simps, subst embed_measure_eq_distr, rule inj_PairVal)
      apply (rule nn_integral_distr[symmetric], intro measurable_embed_measure2 inj_PairVal)
      apply (subst stock_measure.simps[symmetric])
      apply (intro borel_measurable_times_ennreal)
      apply simp
      apply (intro measurable_marg_dens2)
      apply (insert assms)
      apply simp_all
      done
  finally show ?thesis ..
qed


text \<open>The space described by the marginal density is the same as the space obtained by projecting
@{term x} (resp. @{term x} and @{term y}) out of the common distribution of all variables.\<close>

lemma density_marg_dens_eq:
  assumes "x \<in> V" "\<rho> \<in> space (state_measure V' \<Gamma>)"
  shows "density (stock_measure (\<Gamma> x)) (marg_dens \<Y> x \<rho>) =
              distr (dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>) (stock_measure (\<Gamma> x)) (\<lambda>\<sigma>. \<sigma> x)" (is "?M1 = ?M2")
proof (rule measure_eqI)
  fix X assume X: "X \<in> sets ?M1"
  let ?X' = "(\<lambda>\<sigma>. \<sigma> x) -` X \<inter> space (state_measure V \<Gamma>)"
  let ?X'' = "(\<lambda>\<sigma>. \<sigma> x) -` X \<inter> space (state_measure (V \<union> V') \<Gamma>)"
  from X have "emeasure ?M1 X = \<integral>\<^sup>+ \<sigma>. \<delta> (merge V V' (\<sigma>, \<rho>)) * indicator ?X' \<sigma> \<partial>state_measure V \<Gamma>"
    using assms measurable_marg_dens measurable_dens
    by (subst emeasure_density)
       (auto simp: emeasure_distr nn_integral_distr
        dens_ctxt_measure_def state_measure'_def emeasure_density marg_dens_integral)
  also from assms have "... = \<integral>\<^sup>+ \<sigma>. \<delta> (merge V V' (\<sigma>, \<rho>)) *
                                        indicator ?X'' (merge V V' (\<sigma>,\<rho>)) \<partial>state_measure V \<Gamma>"
    by (intro nn_integral_cong)
       (auto split: split_indicator simp: space_state_measure merge_def PiE_iff extensional_def)
  also from X and assms have "... = emeasure ?M2 X" using measurable_dens
    by (auto simp: emeasure_distr emeasure_density nn_integral_distr ennreal_indicator ennreal_mult''
                   dens_ctxt_measure_def state_measure'_def state_measure_def)
  finally show "emeasure ?M1 X = emeasure ?M2 X" .
qed simp

lemma density_marg_dens2_eq:
  assumes "x \<in> V" "y \<in> V" "x \<noteq> y" "\<rho> \<in> space (state_measure V' \<Gamma>)"
  defines "M \<equiv> stock_measure (PRODUCT (\<Gamma> x) (\<Gamma> y))"
  shows "density M (marg_dens2 \<Y> x y \<rho>) =
              distr (dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>) M (\<lambda>\<sigma>. <|\<sigma> x,\<sigma> y|>)" (is "?M1 = ?M2")
proof (rule measure_eqI)
  fix X assume X: "X \<in> sets ?M1"
  let ?X' = "(\<lambda>\<sigma>. <|\<sigma> x , \<sigma> y|>) -` X \<inter> space (state_measure V \<Gamma>)"
  let ?X'' = "(\<lambda>\<sigma>. <|\<sigma> x , \<sigma> y|>) -` X \<inter> space (state_measure (V\<union>V') \<Gamma>)"

  from assms have meas[measurable]: "(\<lambda>\<sigma>. <|\<sigma> x,\<sigma> y|>) \<in> measurable (state_measure (V \<union> V') \<Gamma>)
                                                        (stock_measure (PRODUCT (\<Gamma> x) (\<Gamma> y)))"
    unfolding state_measure_def
    apply (subst stock_measure.simps)
    apply (rule measurable_Pair_compose_split[OF measurable_embed_measure2[OF inj_PairVal]])
    apply (rule measurable_component_singleton, simp)+
    done
  from assms(1-4) X meas have "emeasure ?M2 X = emeasure (dens_ctxt_measure \<Y> \<rho>) ?X''"
    apply (subst emeasure_distr)
    apply (subst measurable_dens_ctxt_measure_eq, unfold state_measure_def M_def)
    apply (simp_all add: space_dens_ctxt_measure state_measure_def)
    done
  also from assms(1-4) X meas
    have "... = \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>, \<rho>)) * indicator ?X'' (merge V V' (\<sigma>, \<rho>)) \<partial>state_measure V \<Gamma>"
      (is "_ = ?I") unfolding dens_ctxt_measure_def state_measure'_def M_def
    by (simp add: emeasure_density nn_integral_distr ennreal_indicator ennreal_mult'')
  also from assms(1-4) X
    have "\<And>\<sigma>. \<sigma>\<in>space (state_measure V \<Gamma>) \<Longrightarrow> merge V V' (\<sigma>, \<rho>) \<in> ?X'' \<longleftrightarrow> \<sigma> \<in> ?X'"
    by (auto simp: space_state_measure merge_def PiE_iff extensional_def)
  hence "?I = \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>, \<rho>)) * indicator ?X' \<sigma> \<partial>state_measure V \<Gamma>"
    by (intro nn_integral_cong) (simp split: split_indicator)
  also from assms X have "... = \<integral>\<^sup>+z. marg_dens2 \<Y> x y \<rho> z * indicator X z \<partial>M" unfolding M_def
    by (subst marg_dens2_integral) simp_all
  also from X have "... = emeasure ?M1 X"
    using assms measurable_dens unfolding M_def
    by (subst emeasure_density, intro measurable_marg_dens2) simp_all
  finally show "emeasure ?M1 X = emeasure ?M2 X" ..
qed simp

lemma measurable_insert_dens[measurable]:
  assumes Mf[measurable]: "case_prod f \<in> borel_measurable (state_measure (V \<union> V') \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
  shows "insert_dens V V' f \<delta>
             \<in> borel_measurable (state_measure (shift_var_set (V \<union> V')) (case_nat t \<Gamma>))"
proof-
  have "(\<lambda>\<sigma>. \<sigma> 0) \<in> measurable (state_measure (shift_var_set (V \<union> V')) (case_nat t \<Gamma>))
                               (stock_measure (case_nat t \<Gamma> 0))" unfolding state_measure_def
    unfolding shift_var_set_def by measurable
  thus ?thesis unfolding insert_dens_def[abs_def] by simp
qed

lemma nn_integral_dens_ctxt_measure:
  assumes "\<rho> \<in> space (state_measure V' \<Gamma>)"
          "f \<in> borel_measurable (state_measure (V \<union> V') \<Gamma>)"
  shows "(\<integral>\<^sup>+x. f x \<partial>dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>) =
           \<integral>\<^sup>+ x. \<delta> (merge V V' (x, \<rho>)) * f (merge V V' (x, \<rho>)) \<partial>state_measure V \<Gamma>"
  unfolding dens_ctxt_measure_def state_measure'_def using assms measurable_dens
  by (simp only: prod.case, subst nn_integral_density)
     (auto simp: nn_integral_distr state_measure_def )

lemma shift_var_set_Un[simp]: "shift_var_set V \<union> Suc ` V' = shift_var_set (V \<union> V')"
  unfolding shift_var_set_def by (simp add: image_Un)

lemma emeasure_dens_ctxt_measure_insert:
  fixes t f \<rho>
  defines "M \<equiv> dens_ctxt_measure (shift_var_set V, Suc`V', case_nat t \<Gamma>, insert_dens V V' f \<delta>) \<rho>"
  assumes dens: "has_parametrized_subprob_density (state_measure (V\<union>V') \<Gamma>) F (stock_measure t) f"
  assumes \<rho>: "\<rho> \<in> space (state_measure (Suc`V') (case_nat t \<Gamma>))"
  assumes X: "X \<in> sets M"
  shows "emeasure M X =
           \<integral>\<^sup>+ x. insert_dens V V' f \<delta> (merge (shift_var_set V) (Suc ` V') (x, \<rho>)) *
                 indicator X (merge (shift_var_set V) (Suc ` V') (x, \<rho>))
             \<partial>state_measure (shift_var_set V) (case_nat t \<Gamma>)" (is "_ = ?I")
proof-
  note [measurable] = has_parametrized_subprob_densityD(3)[OF dens]
  have [measurable]:
    "(\<lambda>\<sigma>. merge (shift_var_set V) (Suc ` V') (\<sigma>, \<rho>))
       \<in> measurable (state_measure (shift_var_set V) (case_nat t \<Gamma>))
                    (state_measure (shift_var_set (V \<union> V')) (case_nat t \<Gamma>))"
    using \<rho> unfolding state_measure_def
    by (simp del: shift_var_set_Un add: shift_var_set_Un[symmetric])
  from assms have "emeasure M X = (\<integral>\<^sup>+x. indicator X x \<partial>M)"
    by (subst nn_integral_indicator)
       (simp_all add: dens_ctxt_measure_def state_measure'_def)
  also have MI: "indicator X \<in> borel_measurable
                     (state_measure (shift_var_set (V \<union> V')) (case_nat t \<Gamma>))"
    using X unfolding M_def dens_ctxt_measure_def state_measure'_def by simp
  have "(\<integral>\<^sup>+x. indicator X x \<partial>M) = ?I"
    using X unfolding M_def dens_ctxt_measure_def state_measure'_def
    apply (simp only: prod.case)
    apply (subst nn_integral_density)
    apply (simp_all add: nn_integral_density nn_integral_distr MI)
    done
  finally show ?thesis .
qed

lemma merge_Suc_aux':
  "\<rho> \<in> space (state_measure (Suc ` V') (case_nat t \<Gamma>)) \<Longrightarrow>
    (\<lambda>\<sigma>. merge V V' (\<sigma>, \<rho> \<circ> Suc)) \<in> measurable (state_measure V \<Gamma>) (state_measure (V \<union> V') \<Gamma>)"
by (unfold state_measure_def,
    rule measurable_compose[OF measurable_Pair measurable_merge], simp,
    rule measurable_const, auto simp: space_PiM dest: PiE_mem)

lemma merge_Suc_aux:
  "\<rho> \<in> space (state_measure (Suc ` V') (case_nat t \<Gamma>)) \<Longrightarrow>
    (\<lambda>\<sigma>. \<delta> (merge V V' (\<sigma>, \<rho> \<circ> Suc))) \<in> borel_measurable (state_measure V \<Gamma>)"
by (rule measurable_compose[OF _ measurable_dens], unfold state_measure_def,
    rule measurable_compose[OF measurable_Pair measurable_merge], simp,
    rule measurable_const, auto simp: space_PiM dest: PiE_mem)

lemma nn_integral_PiM_Suc:
  assumes fin: "\<And>i. sigma_finite_measure (N i)"
  assumes Mf: "f \<in> borel_measurable (Pi\<^sub>M V N)"
  shows "(\<integral>\<^sup>+x. f x \<partial>distr (Pi\<^sub>M (Suc`V) (case_nat M N)) (Pi\<^sub>M V N) (\<lambda>\<sigma>. \<sigma> \<circ> Suc)) =
             (\<integral>\<^sup>+x. f x \<partial>Pi\<^sub>M V N)"
         (is "nn_integral (?M1 V) _ = _")
using Mf
proof (induction arbitrary: f
                 rule: finite_induct[OF finite_vars(1), case_names empty insert])
  case empty
  show ?case by (auto simp add: PiM_empty nn_integral_distr intro!: nn_integral_cong)
next
  case (insert v V)
  let ?V = "insert v V" and ?M3 = "Pi\<^sub>M (insert (Suc v) (Suc ` V)) (case_nat M N)"
  let ?M4 = "Pi\<^sub>M (insert (Suc v) (Suc ` V)) (case_nat (count_space {}) N)"
  let ?M4' = "Pi\<^sub>M (Suc ` V) (case_nat (count_space {}) N)"
  have A: "?M3 = ?M4" by (intro PiM_cong) auto
  interpret product_sigma_finite "case_nat (count_space {}) N"
    unfolding product_sigma_finite_def
    by (auto intro: fin sigma_finite_measure_count_space_countable split: nat.split)
  interpret sigma_finite_measure "N v" by (rule assms)
  note Mf[measurable] = insert(4)

  from insert have "(\<integral>\<^sup>+x. f x \<partial>?M1 ?V) = \<integral>\<^sup>+x. f (x \<circ> Suc) \<partial>?M4"
    by (subst A[symmetric], subst nn_integral_distr)
       (simp_all add: measurable_case_nat_Suc_PiM image_insert[symmetric] del: image_insert)
  also from insert have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x(Suc v := y) \<circ> Suc) \<partial>N v \<partial>?M4'"
    apply (subst product_nn_integral_insert, simp, blast, subst image_insert[symmetric])
    apply (erule measurable_compose[OF measurable_case_nat_Suc_PiM], simp)
    done
  also have "(\<lambda>x y. x(Suc v := y) \<circ> Suc) = (\<lambda>x y. (x \<circ> Suc)(v := y))"
    by (intro ext) (simp add: o_def)
  also have "?M4' = Pi\<^sub>M (Suc ` V) (case_nat M N)" by (intro PiM_cong) auto
  also from insert have "(\<integral>\<^sup>+x. \<integral>\<^sup>+y. f ((x \<circ> Suc)(v := y)) \<partial>N v \<partial>...) =
                             (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x(v := y)) \<partial>N v \<partial>?M1 V)"
    by (subst nn_integral_distr)
       (simp_all add: borel_measurable_nn_integral measurable_case_nat_Suc_PiM)
  also from insert have "... = (\<integral>\<^sup>+x. \<integral>\<^sup>+y. f (x(v := y)) \<partial>N v \<partial>Pi\<^sub>M V N)"
    by (intro insert(3)) measurable
  also from insert have "... = (\<integral>\<^sup>+x. f x \<partial>Pi\<^sub>M ?V N)"
    by (subst product_sigma_finite.product_nn_integral_insert)
       (simp_all add: assms product_sigma_finite_def)
  finally show ?case .
qed

lemma PiM_Suc:
  assumes "\<And>i. sigma_finite_measure (N i)"
  shows "distr (Pi\<^sub>M (Suc`V) (case_nat M N)) (Pi\<^sub>M V N) (\<lambda>\<sigma>. \<sigma> \<circ> Suc) = Pi\<^sub>M V N" (is "?M1 = ?M2")
  by (intro measure_eqI)
     (simp_all add: nn_integral_indicator[symmetric] nn_integral_PiM_Suc assms
               del: nn_integral_indicator)

lemma distr_state_measure_Suc:
  "distr (state_measure (Suc ` V) (case_nat t \<Gamma>)) (state_measure V \<Gamma>) (\<lambda>\<sigma>. \<sigma> \<circ> Suc) =
     state_measure V \<Gamma>" (is "?M1 = ?M2")
  unfolding state_measure_def
  apply (subst (2) PiM_Suc[of "\<lambda>x. stock_measure (\<Gamma> x)" "stock_measure t", symmetric], simp)
  apply (intro distr_cong PiM_cong)
  apply (simp_all split: nat.split)
  done

lemma emeasure_dens_ctxt_measure_insert':
  fixes t f \<rho>
  defines "M \<equiv> dens_ctxt_measure (shift_var_set V, Suc`V', case_nat t \<Gamma>, insert_dens V V' f \<delta>) \<rho>"
  assumes dens: "has_parametrized_subprob_density (state_measure (V\<union>V') \<Gamma>) F (stock_measure t) f"
  assumes \<rho>: "\<rho> \<in> space (state_measure (Suc`V') (case_nat t \<Gamma>))"
  assumes X: "X \<in> sets M"
  shows "emeasure M X = \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>, \<rho> \<circ> Suc)) * \<integral>\<^sup>+y. f (merge V V' (\<sigma>, \<rho> \<circ> Suc)) y *
                       indicator X (merge (shift_var_set V) (Suc`V') (case_nat y \<sigma>, \<rho>))
                  \<partial>stock_measure t \<partial>state_measure V \<Gamma>" (is "_ = ?I")
proof-
  let ?m = "\<lambda>x y. merge (insert 0 (Suc ` V)) (Suc ` V') (x(0 := y), \<rho>)"
  from dens have Mf:
      "case_prod f \<in> borel_measurable (state_measure (V\<union>V') \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
    by (rule has_parametrized_subprob_densityD)
  note [measurable] = Mf[unfolded state_measure_def]
  have meas_merge: "(\<lambda>x. merge (shift_var_set V) (Suc`V') (x, \<rho>))
       \<in> measurable (state_measure (shift_var_set V) (case_nat t \<Gamma>))
                    (state_measure (shift_var_set (V \<union> V')) (case_nat t \<Gamma>))"
    using \<rho> unfolding state_measure_def shift_var_set_def
    by (simp add: image_Un image_insert[symmetric] Un_insert_left[symmetric]
             del: image_insert Un_insert_left)
  note measurable_insert_dens' =
           measurable_insert_dens[unfolded shift_var_set_def state_measure_def]
  have meas_merge': "(\<lambda>x. merge (shift_var_set V) (Suc ` V') (case_nat (snd x) (fst x), \<rho>))
       \<in> measurable (state_measure V \<Gamma> \<Otimes>\<^sub>M stock_measure t)
                    (state_measure (shift_var_set (V\<union>V')) (case_nat t \<Gamma>))"
    by (rule measurable_compose[OF _ meas_merge]) simp
  have meas_integral: "(\<lambda>\<sigma>. \<integral>\<^sup>+ y. \<delta> (merge V V' (\<sigma>, \<rho> \<circ> Suc)) * f (merge V V' (\<sigma>, \<rho> \<circ> Suc)) y *
                            indicator X (merge (shift_var_set V) (Suc ` V') (case_nat y \<sigma>, \<rho>))
                           \<partial>stock_measure t) \<in> borel_measurable (state_measure V \<Gamma>)"
    apply (rule sigma_finite_measure.borel_measurable_nn_integral, simp)
    apply (subst measurable_split_conv, intro borel_measurable_times_ennreal)
    apply (rule measurable_compose[OF measurable_fst merge_Suc_aux[OF \<rho>]])
    apply (rule measurable_Pair_compose_split[OF Mf])
    apply (rule measurable_compose[OF measurable_fst merge_Suc_aux'[OF \<rho>]], simp)
    apply (rule measurable_compose[OF meas_merge' borel_measurable_indicator])
    apply (insert X, simp add: M_def dens_ctxt_measure_def state_measure'_def)
    done
  have meas': "\<And>x. x \<in> space (state_measure V \<Gamma>)
                  \<Longrightarrow> (\<lambda>y. f (merge V V' (x, \<rho> \<circ> Suc)) y *
                      indicator X (merge (shift_var_set V) (Suc ` V') (case_nat y x, \<rho>)))
                  \<in> borel_measurable (stock_measure t)" using X
    apply (intro borel_measurable_times_ennreal)
    apply (rule measurable_Pair_compose_split[OF Mf])
    apply (rule measurable_const, erule measurable_space[OF merge_Suc_aux'[OF \<rho>]])
    apply (simp, rule measurable_compose[OF _ borel_measurable_indicator])
    apply (rule measurable_compose[OF measurable_case_nat'])
    apply (rule measurable_ident_sets[OF refl], erule measurable_const)
    apply (rule meas_merge, simp add: M_def dens_ctxt_measure_def state_measure'_def)
    done

  have "emeasure M X =
           \<integral>\<^sup>+ x. insert_dens V V' f \<delta> (merge (shift_var_set V) (Suc ` V') (x, \<rho>)) *
                 indicator X (merge (shift_var_set V) (Suc ` V') (x, \<rho>))
             \<partial>state_measure (shift_var_set V) (case_nat t \<Gamma>)"
    using assms unfolding M_def by (intro emeasure_dens_ctxt_measure_insert)
  also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. insert_dens V V' f \<delta> (?m x y) *
                  indicator X (?m x y) \<partial>stock_measure t \<partial>state_measure (Suc`V) (case_nat t \<Gamma>)"
    (is "_ = ?I") using \<rho> X meas_merge
    unfolding shift_var_set_def M_def dens_ctxt_measure_def state_measure'_def state_measure_def
    apply (subst product_sigma_finite.product_nn_integral_insert)
    apply (auto simp: product_sigma_finite_def) [3]
    apply (intro borel_measurable_times_ennreal)
    apply (rule measurable_compose[OF _ measurable_insert_dens'], simp)
    apply (simp_all add: measurable_compose[OF _ borel_measurable_indicator] image_Un)
    done
  also have "\<And>\<sigma> y. \<sigma> \<in> space (state_measure (Suc`V) (case_nat t \<Gamma>)) \<Longrightarrow>
                   y \<in> space (stock_measure t) \<Longrightarrow>
                   (remove_var (merge (insert 0 (Suc ` V)) (Suc ` V') (\<sigma>(0:=y), \<rho>))) =
                       merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)"
    by (auto simp: merge_def remove_var_def)
  hence "?I = \<integral>\<^sup>+\<sigma>. \<integral>\<^sup>+y. \<delta> (merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)) * f (merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)) y *
                       indicator X (?m \<sigma> y)
                  \<partial>stock_measure t \<partial>state_measure (Suc`V) (case_nat t \<Gamma>)" (is "_ = ?I")
    by (intro nn_integral_cong)
       (auto simp: insert_dens_def inj_image_mem_iff merge_def split: split_indicator nat.split)
  also have m_eq: "\<And>x y. ?m x y = merge (shift_var_set V) (Suc`V') (case_nat y (x \<circ> Suc), \<rho>)"
    by (intro ext) (auto simp add: merge_def shift_var_set_def split: nat.split)
  have "?I = \<integral>\<^sup>+\<sigma>. \<integral>\<^sup>+y. \<delta> (merge V V' (\<sigma>, \<rho> \<circ> Suc)) * f (merge V V' (\<sigma>, \<rho> \<circ> Suc)) y *
                       indicator X (merge (shift_var_set V) (Suc`V') (case_nat y \<sigma>, \<rho>))
                  \<partial>stock_measure t \<partial>state_measure V \<Gamma>" using \<rho> X
    apply (subst distr_state_measure_Suc[symmetric, of t])
    apply (subst nn_integral_distr)
    apply (rule measurable_case_nat_Suc)
    apply simp
    apply (rule meas_integral)
    apply (intro nn_integral_cong)
    apply (simp add: m_eq)
    done
  also have "... = \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>, \<rho> \<circ> Suc)) * \<integral>\<^sup>+y. f (merge V V' (\<sigma>, \<rho> \<circ> Suc)) y *
                       indicator X (merge (shift_var_set V) (Suc`V') (case_nat y \<sigma>, \<rho>))
                  \<partial>stock_measure t \<partial>state_measure V \<Gamma>" using \<rho> X
    apply (intro nn_integral_cong)
    apply (subst nn_integral_cmult[symmetric])
    apply (erule meas')
    apply (simp add: mult.assoc)
    done
  finally show ?thesis .
qed


lemma density_context_insert:
  assumes dens: "has_parametrized_subprob_density (state_measure (V\<union>V') \<Gamma>) F (stock_measure t) f"
  shows "density_context (shift_var_set V) (Suc ` V') (case_nat t \<Gamma>) (insert_dens V V' f \<delta>)"
             (is "density_context ?V ?V' ?\<Gamma>' ?\<delta>'")
unfolding density_context_def
proof (intro allI conjI impI)
  note measurable_insert_dens[OF has_parametrized_subprob_densityD(3)[OF dens]]
  thus "insert_dens V V' f \<delta>
          \<in> borel_measurable (state_measure (shift_var_set V \<union> Suc ` V') (case_nat t \<Gamma>))"
    unfolding shift_var_set_def by (simp only: image_Un Un_insert_left)
next
  fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure ?V' ?\<Gamma>')"
  hence \<rho>': "\<rho> \<circ> Suc \<in> space (state_measure V' \<Gamma>)"
    by (auto simp: state_measure_def space_PiM dest: PiE_mem)
  note dens' = has_parametrized_subprob_densityD[OF dens]
  note Mf[measurable] = dens'(3)
  have M_merge: "(\<lambda>x. merge (shift_var_set V) (Suc ` V') (x, \<rho>))
                   \<in> measurable (Pi\<^sub>M (insert 0 (Suc ` V)) (\<lambda>y. stock_measure (case_nat t \<Gamma> y)))
                                (state_measure (shift_var_set (V \<union> V')) (case_nat t \<Gamma>))"
    using \<rho> by (subst shift_var_set_Un[symmetric], unfold state_measure_def)
               (simp add: shift_var_set_def del: shift_var_set_Un Un_insert_left)
  show "subprob_space (dens_ctxt_measure (?V,?V',?\<Gamma>',?\<delta>') \<rho>)" (is "subprob_space ?M")
  proof (rule subprob_spaceI)
    interpret product_sigma_finite "(\<lambda>y. stock_measure (case y of 0 \<Rightarrow> t | Suc x \<Rightarrow> \<Gamma> x))"
      by (simp add: product_sigma_finite_def)
    have Suc_state_measure:
      "\<And>x. x \<in> space (state_measure (Suc ` V) (case_nat t \<Gamma>)) \<Longrightarrow>
              merge V V' (x \<circ> Suc, \<rho> \<circ> Suc) \<in> space (state_measure (V \<union> V') \<Gamma>)" using \<rho>
      by (intro merge_in_state_measure) (auto simp: state_measure_def space_PiM dest: PiE_mem)

    have S[simp]: "\<And>x X. Suc x \<in> Suc ` X \<longleftrightarrow> x \<in> X" by (rule inj_image_mem_iff) simp
    let ?M = "dens_ctxt_measure (?V,?V',?\<Gamma>',?\<delta>') \<rho>"
    from \<rho> have "\<And>\<sigma>. \<sigma> \<in> space (state_measure ?V ?\<Gamma>') \<Longrightarrow> merge ?V ?V' (\<sigma>, \<rho>) \<in> space ?M"
      by (auto simp: dens_ctxt_measure_def state_measure'_def simp del: shift_var_set_Un
               intro!: merge_in_state_measure)
    hence "emeasure ?M (space ?M) =
            \<integral>\<^sup>+\<sigma>. insert_dens V V' f \<delta> (merge ?V ?V' (\<sigma>, \<rho>)) \<partial>state_measure ?V ?\<Gamma>'"
     by (subst emeasure_dens_ctxt_measure_insert[OF dens \<rho>], simp, intro nn_integral_cong)
        (simp split: split_indicator)
    also have "... = \<integral>\<^sup>+\<sigma>. insert_dens V V' f \<delta> (merge ?V ?V' (\<sigma>, \<rho>))
                              \<partial>state_measure (insert 0 (Suc ` V)) ?\<Gamma>'"
      by (simp add: shift_var_set_def)
    also have "... = \<integral>\<^sup>+\<sigma>. \<integral>\<^sup>+x. insert_dens V V' f \<delta> (merge ?V ?V' (\<sigma>(0 := x), \<rho>))
                       \<partial>stock_measure t \<partial>state_measure (Suc ` V) ?\<Gamma>'"
       unfolding state_measure_def using M_merge
       by (subst product_nn_integral_insert) auto
    also have "... = \<integral>\<^sup>+\<sigma>. \<integral>\<^sup>+x. \<delta> (remove_var (merge ?V ?V' (\<sigma>(0:=x), \<rho>))) *
                               f (remove_var (merge ?V ?V' (\<sigma>(0:=x), \<rho>))) x
                        \<partial>stock_measure t \<partial>state_measure (Suc ` V) ?\<Gamma>'" (is "_ = ?I")
       by (intro nn_integral_cong) (auto simp: insert_dens_def merge_def shift_var_set_def)
    also have "\<And>\<sigma> x. remove_var (merge ?V ?V' (\<sigma>(0:=x), \<rho>)) = merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)"
      by (intro ext) (auto simp: remove_var_def merge_def shift_var_set_def o_def)
    hence "?I = \<integral>\<^sup>+\<sigma>. \<integral>\<^sup>+x. \<delta> (merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)) * f (merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)) x
                  \<partial>stock_measure t \<partial>state_measure (Suc ` V) ?\<Gamma>'" by simp
    also have "... = \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)) *
                            (\<integral>\<^sup>+x. f (merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)) x \<partial>stock_measure t)
                       \<partial>state_measure (Suc ` V) ?\<Gamma>'" (is "_ = ?I")
      using \<rho> disjoint
      apply (intro nn_integral_cong nn_integral_cmult)
      apply (rule measurable_Pair_compose_split[OF Mf], rule measurable_const)
      apply (auto intro!: Suc_state_measure)
      done
    also {
      fix \<sigma> assume \<sigma>: "\<sigma> \<in> space (state_measure (Suc ` V) ?\<Gamma>')"
      let ?\<sigma>' = "merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)"
      let ?N = "density (stock_measure t) (f ?\<sigma>')"
      have "(\<integral>\<^sup>+x. f (merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)) x \<partial>stock_measure t) = emeasure ?N (space ?N)"
        using dens'(3) Suc_state_measure[OF \<sigma>]
        by (simp_all cong: nn_integral_cong' add: emeasure_density)
      also have "?N = F ?\<sigma>'" by (subst dens') (simp_all add: Suc_state_measure \<sigma>)
      also have "subprob_space (F ?\<sigma>')" by (rule dens') (simp_all add: Suc_state_measure \<sigma>)
      hence "emeasure (F ?\<sigma>') (space (F ?\<sigma>')) \<le> 1" by (rule subprob_space.emeasure_space_le_1)
      finally have "(\<integral>\<^sup>+x. f (merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)) x \<partial>stock_measure t) \<le> 1" .
    }
    hence "?I \<le> \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma> \<circ> Suc, \<rho> \<circ> Suc)) * 1 \<partial>state_measure (Suc ` V) ?\<Gamma>'"
      by (intro nn_integral_mono mult_left_mono) (simp_all add: Suc_state_measure)
    also have "... = \<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>, \<rho> \<circ> Suc))
                       \<partial>distr (state_measure (Suc ` V) ?\<Gamma>') (state_measure V \<Gamma>) (\<lambda>\<sigma>. \<sigma> \<circ> Suc)"
      (is "_ = nn_integral ?N _")
      using \<rho> by (subst nn_integral_distr) (simp_all add: measurable_case_nat_Suc merge_Suc_aux)
    also have "?N = state_measure V \<Gamma>" by (rule distr_state_measure_Suc)
    also have "(\<integral>\<^sup>+\<sigma>. \<delta> (merge V V' (\<sigma>, \<rho> \<circ> Suc)) \<partial>state_measure V \<Gamma>) =
                   (\<integral>\<^sup>+\<sigma>. 1 \<partial>dens_ctxt_measure \<Y> (\<rho> \<circ> Suc))" (is "_ = nn_integral ?N _")
      by (subst nn_integral_dens_ctxt_measure) (simp_all add: \<rho>')
    also have "... = (\<integral>\<^sup>+\<sigma>. indicator (space ?N) \<sigma> \<partial>?N)"
      by (intro nn_integral_cong) (simp split: split_indicator)
    also have "... = emeasure ?N (space ?N)" by simp
    also have "... \<le> 1" by (simp_all add: subprob_space.emeasure_space_le_1 subprob_space_dens \<rho>')
    finally show "emeasure ?M (space ?M) \<le> 1" .
  qed (simp_all add: space_dens_ctxt_measure state_measure_def space_PiM PiE_eq_empty_iff)
qed (insert disjoint, auto simp: shift_var_set_def)


lemma dens_ctxt_measure_insert:
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  assumes meas_M: "M \<in> measurable (state_measure (V\<union>V') \<Gamma>) (subprob_algebra (stock_measure t))"
  assumes meas_f[measurable]: "case_prod f \<in> borel_measurable (state_measure (V\<union>V') \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
  assumes has_dens: "\<And>\<rho>. \<rho> \<in> space (state_measure (V\<union>V') \<Gamma>) \<Longrightarrow>
                         has_subprob_density (M \<rho>) (stock_measure t) (f \<rho>)"
  shows "do {\<sigma> \<leftarrow> dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>;
             y \<leftarrow> M \<sigma>;
             return (state_measure (shift_var_set (V \<union> V')) (case_nat t \<Gamma>)) (case_nat y \<sigma>)} =
         dens_ctxt_measure (shift_var_set V, Suc`V', case_nat t \<Gamma>, insert_dens V V' f \<delta>)
                           (case_nat undefined \<rho>)"
         (is "bind ?N (\<lambda>_. bind _ (\<lambda>_. return ?R _)) = dens_ctxt_measure (?V,?V',?\<Gamma>',?\<delta>') _")
proof (intro measure_eqI)
  let ?lhs = "?N \<bind> (\<lambda>\<sigma> . M \<sigma> \<bind> (\<lambda>y. return ?R (case_nat y \<sigma>)))"
  let ?rhs = "dens_ctxt_measure (?V,?V',?\<Gamma>',?\<delta>') (case_nat undefined \<rho>)"

  have meas_f': "\<And>M g h. g \<in> measurable M (state_measure (V\<union>V') \<Gamma>) \<Longrightarrow>
                         h \<in> measurable M (stock_measure t) \<Longrightarrow>
                         (\<lambda>x. f (g x) (h x)) \<in> borel_measurable M" by measurable
  have t: "t = ?\<Gamma>' 0" by simp

  have nonempty: "space ?N \<noteq> {}"
      by (auto simp: dens_ctxt_measure_def state_measure'_def state_measure_def
                     space_PiM PiE_eq_empty_iff)
  have meas_N_eq: "measurable ?N = measurable (state_measure (V\<union>V') \<Gamma>)"
    by (intro ext measurable_cong_sets) (auto simp: dens_ctxt_measure_def state_measure'_def)
  have meas_M': "M \<in> measurable ?N (subprob_algebra (stock_measure t))"
    by (subst meas_N_eq) (rule meas_M)
  have meas_N': "\<And>R. measurable (?N \<Otimes>\<^sub>M R) = measurable (state_measure (V\<union>V') \<Gamma> \<Otimes>\<^sub>M R)"
    by (intro ext measurable_cong_sets[OF _ refl] sets_pair_measure_cong)
       (simp_all add: dens_ctxt_measure_def state_measure'_def)
  have meas_M_eq: "\<And>\<rho>. \<rho> \<in> space ?N \<Longrightarrow> measurable (M \<rho>) = measurable (stock_measure t)"
    by (intro ext measurable_cong_sets sets_kernel[OF meas_M']) simp_all
  have meas_rhs: "\<And>M. measurable M ?rhs = measurable M ?R"
    by (intro ext measurable_cong_sets) (simp_all add: dens_ctxt_measure_def state_measure'_def)
  have subprob_algebra_rhs: "subprob_algebra ?rhs = subprob_algebra (state_measure (shift_var_set (V\<union>V')) ?\<Gamma>')"
    unfolding dens_ctxt_measure_def state_measure'_def by (intro subprob_algebra_cong) auto
  have nonempty': "\<And>\<rho>. \<rho> \<in> space ?N \<Longrightarrow> space (M \<rho>) \<noteq> {}"
    by (rule subprob_space.subprob_not_empty)
       (auto dest: has_subprob_densityD has_dens simp: space_dens_ctxt_measure)
  have merge_in_space: "\<And>x. x \<in> space (state_measure V \<Gamma>) \<Longrightarrow>
                              merge V V' (x, \<rho>) \<in> space (dens_ctxt_measure \<Y> \<rho>)"
    by (simp add: space_dens_ctxt_measure merge_in_state_measure \<rho>)

  have "sets ?lhs = sets (state_measure (shift_var_set (V \<union> V')) ?\<Gamma>')"
    using nonempty' by (subst sets_bind, subst sets_bind) auto
  thus sets_eq: "sets ?lhs = sets ?rhs"
    unfolding dens_ctxt_measure_def state_measure'_def by simp

  have meas_merge[measurable]:
    "(\<lambda>\<sigma>. merge V V' (\<sigma>, \<rho>)) \<in> measurable (state_measure V \<Gamma>) (state_measure (V \<union> V') \<Gamma>)"
    using \<rho> unfolding state_measure_def by - measurable

  fix X assume "X \<in> sets ?lhs"
  hence X: "X \<in> sets ?rhs" by (simp add: sets_eq)
  hence "emeasure ?lhs X = \<integral>\<^sup>+\<sigma>. emeasure (M \<sigma> \<bind> (\<lambda>y. return ?R (case_nat y \<sigma>))) X \<partial>?N"
    by (intro emeasure_bind measurable_bind[OF meas_M'])
       (simp, rule measurable_compose[OF _ return_measurable],
        simp_all add: dens_ctxt_measure_def state_measure'_def)
  also from X have "... =
    \<integral>\<^sup>+ x. \<delta> (merge V V' (x, \<rho>)) * emeasure (M (merge V V' (x, \<rho>)) \<bind>
             (\<lambda>y. return ?R (case_nat y (merge V V' (x, \<rho>))))) X \<partial>state_measure V \<Gamma>"
    apply (subst nn_integral_dens_ctxt_measure[OF \<rho>])
    apply (rule measurable_emeasure_kernel[OF measurable_bind[OF meas_M]])
    apply (rule measurable_compose[OF _ return_measurable], simp)
    apply (simp_all add: dens_ctxt_measure_def state_measure'_def)
    done
  also from X have "... = \<integral>\<^sup>+x. \<delta> (merge V V' (x, \<rho>)) *
                              \<integral>\<^sup>+y. indicator X (case_nat y (merge V V' (x, \<rho>)))
                                   \<partial>M (merge V V' (x, \<rho>)) \<partial>state_measure V \<Gamma>" (is "_ = ?I")
    apply (intro nn_integral_cong)
    apply (subst emeasure_bind, rule nonempty', simp add: merge_in_space)
    apply (rule measurable_compose[OF _ return_measurable], simp add: merge_in_space meas_M_eq)
    apply (simp_all add: dens_ctxt_measure_def state_measure'_def)
    done
  also have "\<And>x. x \<in> space (state_measure V \<Gamma>) \<Longrightarrow>
                  M (merge V V' (x, \<rho>)) = density (stock_measure t) (f (merge V V' (x, \<rho>)))"
    by (intro has_subprob_densityD[OF has_dens]) (simp add: merge_in_state_measure \<rho>)
  hence "?I = \<integral>\<^sup>+x. \<delta> (merge V V' (x, \<rho>)) *
                \<integral>\<^sup>+y. indicator X (case_nat y (merge V V' (x, \<rho>)))
                \<partial>density (stock_measure t) (f (merge V V' (x, \<rho>))) \<partial>state_measure V \<Gamma>"
    by (intro nn_integral_cong) simp
  also have "... = \<integral>\<^sup>+x. \<delta> (merge V V' (x, \<rho>)) *
                     \<integral>\<^sup>+y. f (merge V V' (x, \<rho>)) y * indicator X (case_nat y (merge V V' (x, \<rho>)))
                   \<partial>stock_measure t \<partial>state_measure V \<Gamma>" (is "_ = ?I") using X
    by (intro nn_integral_cong, subst nn_integral_density, simp)
       (auto simp: mult.assoc dens_ctxt_measure_def state_measure'_def
             intro!: merge_in_state_measure \<rho> AE_I'[of "{}"]
                     has_subprob_densityD[OF has_dens])
  also have A: "case_nat undefined \<rho> \<circ> Suc = \<rho>" by (intro ext) simp
  have B: "\<And>x y. x \<in> space (state_measure V \<Gamma>) \<Longrightarrow> y \<in> space (stock_measure t) \<Longrightarrow>
           (case_nat y (merge V V' (x, \<rho>))) =
           (merge (shift_var_set V) (Suc ` V') (case_nat y x, case_nat undefined \<rho>))"
    by (intro ext) (auto simp add: merge_def shift_var_set_def split: nat.split)
  have C: "\<And>x. x \<in> space (state_measure V \<Gamma>) \<Longrightarrow>
     (\<integral>\<^sup>+y. f (merge V V' (x, \<rho>)) y * indicator X (case_nat y (merge V V' (x,\<rho>))) \<partial>stock_measure t) =
      \<integral>\<^sup>+y. f (merge V V' (x, \<rho>)) y * indicator X (merge (shift_var_set V) (Suc`V')
                 (case_nat y x,case_nat undefined \<rho>)) \<partial>stock_measure t"
    by (intro nn_integral_cong) (simp add: B)
  have "?I = emeasure ?rhs X" using X
    apply (subst emeasure_dens_ctxt_measure_insert'[where F = M])
    apply (insert has_dens, simp add: has_parametrized_subprob_density_def)
    apply (rule measurable_space[OF measurable_case_nat_undefined \<rho>], simp)
    apply (intro nn_integral_cong, simp add: A C)
    done
  finally show "emeasure ?lhs X = emeasure ?rhs X" .
qed

lemma density_context_if_dens:
  assumes "has_parametrized_subprob_density (state_measure (V \<union> V') \<Gamma>) M
               (count_space (range BoolVal)) f"
  shows "density_context V V' \<Gamma> (if_dens \<delta> f b)"
unfolding density_context_def
proof (intro allI conjI impI subprob_spaceI)
  note D = has_parametrized_subprob_densityD[OF assms]
  from D(3) show M: "if_dens \<delta> f b \<in> borel_measurable (state_measure (V \<union> V') \<Gamma>)"
    by (intro measurable_if_dens) simp_all

  fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  hence [measurable]: "(\<lambda>\<sigma>. merge V V' (\<sigma>, \<rho>)) \<in>
                            measurable (state_measure V \<Gamma>) (state_measure (V \<union> V') \<Gamma>)"
    unfolding state_measure_def by simp

  {
    fix \<sigma> assume "\<sigma> \<in> space (state_measure V \<Gamma>)"
    with \<rho> have \<sigma>\<rho>: "merge V V' (\<sigma>, \<rho>) \<in> space (state_measure (V \<union> V') \<Gamma>)"
      by (intro merge_in_state_measure)
    with assms have "has_subprob_density (M (merge V V' (\<sigma>, \<rho>))) (count_space (range BoolVal))
                         (f (merge V V' (\<sigma>, \<rho>)))"
      unfolding has_parametrized_subprob_density_def by auto
    with \<sigma>\<rho> have "f (merge V V' (\<sigma>, \<rho>)) (BoolVal b) \<le> 1" "\<delta> (merge V V' (\<sigma>, \<rho>)) \<ge> 0"
      by (auto intro: subprob_count_space_density_le_1)
  } note dens_props = this

  from \<rho> interpret subprob_space "dens_ctxt_measure \<Y> \<rho>" by (rule subprob_space_dens)
  let ?M = "dens_ctxt_measure (V, V', \<Gamma>, if_dens \<delta> f b) \<rho>"
  have "emeasure ?M (space ?M) =
          \<integral>\<^sup>+x. if_dens \<delta> f b (merge V V' (x, \<rho>)) \<partial>state_measure V \<Gamma>"
    using M \<rho> unfolding dens_ctxt_measure_def state_measure'_def
    by (simp only: prod.case space_density)
       (auto simp: nn_integral_distr emeasure_density cong: nn_integral_cong')
  also from \<rho> have "... \<le> \<integral>\<^sup>+x. \<delta> (merge V V' (x, \<rho>)) * 1 \<partial>state_measure V \<Gamma>"
    unfolding if_dens_def using dens_props
    by (intro nn_integral_mono mult_left_mono) simp_all
  also from \<rho> have "... = branch_prob \<Y> \<rho>" by (simp add: branch_prob_altdef)
  also have "... = emeasure (dens_ctxt_measure \<Y> \<rho>) (space (dens_ctxt_measure \<Y> \<rho>))"
    by (simp add: branch_prob_def)
  also have "... \<le> 1" by (rule emeasure_space_le_1)
  finally show "emeasure ?M (space ?M) \<le> 1" .
qed (insert disjoint, auto)

lemma density_context_if_dens_det:
  assumes e: "\<Gamma> \<turnstile> e : BOOL" "randomfree e" "free_vars e \<subseteq> V \<union> V'"
  shows "density_context V V' \<Gamma> (if_dens_det \<delta> e b)"
unfolding density_context_def
proof (intro allI conjI impI subprob_spaceI)
  from assms show M: "if_dens_det \<delta> e b \<in> borel_measurable (state_measure (V \<union> V') \<Gamma>)"
    by (intro measurable_if_dens_det) simp_all

  fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  hence [measurable]: "(\<lambda>\<sigma>. merge V V' (\<sigma>, \<rho>)) \<in>
                            measurable (state_measure V \<Gamma>) (state_measure (V \<union> V') \<Gamma>)"
    unfolding state_measure_def by simp

  from \<rho> interpret subprob_space "dens_ctxt_measure \<Y> \<rho>" by (rule subprob_space_dens)
  let ?M = "dens_ctxt_measure (V, V', \<Gamma>, if_dens_det \<delta> e b) \<rho>"
  have "emeasure ?M (space ?M) =
          \<integral>\<^sup>+x. if_dens_det \<delta> e b (merge V V' (x, \<rho>)) \<partial>state_measure V \<Gamma>"
    using M \<rho> unfolding dens_ctxt_measure_def state_measure'_def
    by (simp only: prod.case space_density)
       (auto simp: nn_integral_distr emeasure_density cong: nn_integral_cong')
  also from \<rho> have "... \<le> \<integral>\<^sup>+x. \<delta> (merge V V' (x, \<rho>)) * 1 \<partial>state_measure V \<Gamma>"
    unfolding if_dens_det_def
    by (intro nn_integral_mono mult_left_mono) (simp_all add: merge_in_state_measure)
  also from \<rho> have "... = branch_prob \<Y> \<rho>" by (simp add: branch_prob_altdef)
  also have "... = emeasure (dens_ctxt_measure \<Y> \<rho>) (space (dens_ctxt_measure \<Y> \<rho>))"
    by (simp add: branch_prob_def)
  also have "... \<le> 1" by (rule emeasure_space_le_1)
  finally show "emeasure ?M (space ?M) \<le> 1" .
qed (insert disjoint assms, auto intro: measurable_if_dens_det)


lemma density_context_empty[simp]: "density_context {} (V\<union>V') \<Gamma> (\<lambda>_. 1)"
unfolding density_context_def
proof (intro allI conjI impI subprob_spaceI)
  fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure (V \<union> V') \<Gamma>)"
  let ?M = "dens_ctxt_measure ({},V\<union>V',\<Gamma>,\<lambda>_. 1) \<rho>"
  from \<rho> have "\<And>\<sigma>. merge {} (V\<union>V') (\<sigma>,\<rho>) = \<rho>"
    by (intro ext) (auto simp: merge_def state_measure_def space_PiM)
  with \<rho> show "emeasure ?M (space ?M) \<le> 1"
    unfolding dens_ctxt_measure_def state_measure'_def
    by (auto simp: emeasure_density emeasure_distr state_measure_def PiM_empty)
qed auto

lemma dens_ctxt_measure_bind_const:
  assumes "\<rho> \<in> space (state_measure V' \<Gamma>)" "subprob_space N"
  shows "dens_ctxt_measure \<Y> \<rho> \<bind> (\<lambda>_. N) = density N (\<lambda>_. branch_prob \<Y> \<rho>)" (is "?M1 = ?M2")
proof (rule measure_eqI)
  have [simp]: "sets ?M1 = sets N" by (auto simp: space_subprob_algebra assms)
  thus "sets ?M1 = sets ?M2" by simp
  fix X assume X: "X \<in> sets ?M1"
  with assms have "emeasure ?M1 X = emeasure N X * branch_prob \<Y> \<rho>"
    unfolding branch_prob_def by (subst emeasure_bind_const') (auto simp: subprob_space_dens)
  also from X have "emeasure N X = \<integral>\<^sup>+x. indicator X x \<partial>N" by simp
  also from X have "... * branch_prob \<Y> \<rho> = \<integral>\<^sup>+x. branch_prob \<Y> \<rho> * indicator X x \<partial>N"
    by (subst nn_integral_cmult) (auto simp: branch_prob_def field_simps)
  also from X have "... = emeasure ?M2 X" by (simp add: emeasure_density)
  finally show "emeasure ?M1 X = emeasure ?M2 X" .
qed


lemma nn_integral_dens_ctxt_measure_restrict:
  assumes "\<rho> \<in> space (state_measure V' \<Gamma>)" "f \<rho> \<ge> 0"
  assumes "f \<in> borel_measurable (state_measure V' \<Gamma>)"
  shows "(\<integral>\<^sup>+x. f (restrict x V') \<partial>dens_ctxt_measure \<Y> \<rho>) = branch_prob \<Y> \<rho> * f \<rho>"
proof-
  have "(\<integral>\<^sup>+x. f (restrict x V') \<partial>dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>) =
          \<integral>\<^sup>+ x. \<delta> (merge V V' (x, \<rho>)) * f (restrict (merge V V' (x, \<rho>)) V') \<partial>state_measure V \<Gamma>"
          (is "_ = ?I")
    by (subst nn_integral_dens_ctxt_measure, simp add: assms,
        rule measurable_compose[OF measurable_restrict], unfold state_measure_def,
        rule measurable_component_singleton, insert assms, simp_all add: state_measure_def)
  also from assms(1) and disjoint
    have "\<And>x. x \<in> space (state_measure V \<Gamma>) \<Longrightarrow> restrict (merge V V' (x, \<rho>)) V' = \<rho>"
    by (intro ext) (auto simp: restrict_def merge_def state_measure_def space_PiM dest: PiE_mem)
  hence "?I = \<integral>\<^sup>+ x. \<delta> (merge V V' (x, \<rho>)) * f \<rho> \<partial>state_measure V \<Gamma>"
    by (intro nn_integral_cong) simp
  also have "... = (\<integral>\<^sup>+x. f \<rho> \<partial>dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>)"
    by (subst nn_integral_dens_ctxt_measure) (simp_all add: assms)
  also have "... = f \<rho> * branch_prob \<Y> \<rho>"
    by (subst nn_integral_const)
       (simp_all add: assms branch_prob_def)
  finally show ?thesis by (simp add: field_simps)
qed

lemma expr_sem_op_eq_distr:
  assumes "\<Gamma> \<turnstile> oper $$ e : t'" "free_vars e \<subseteq> V \<union> V'" "\<rho> \<in> space (state_measure V' \<Gamma>)"
  defines "M \<equiv> dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>"
  shows "M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (oper $$ e)) =
             distr (M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t') (op_sem oper)"
proof-
  from assms(1) obtain t where t1: "\<Gamma> \<turnstile> e : t" and t2: "op_type oper t = Some t'" by auto
  let ?N = "stock_measure t" and ?R = "subprob_algebra (stock_measure t')"

  {
    fix x assume "x \<in> space (stock_measure t)"
    with t1 assms(2,3) have "val_type x = t"
      by (auto simp: state_measure_def space_PiM dest: PiE_mem)
    hence "return_val (op_sem oper x) = return (stock_measure t') (op_sem oper x)"
      unfolding return_val_def by (subst op_sem_val_type) (simp_all add: t2)
  } note return_op_sem = this

  from assms and t1 have M_e: "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<in> measurable M (subprob_algebra (stock_measure t))"
    by (simp add: M_def measurable_dens_ctxt_measure_eq measurable_expr_sem)
  from return_op_sem
    have M_cong: "(\<lambda>x. return_val (op_sem oper x)) \<in> measurable ?N ?R \<longleftrightarrow>
                     (\<lambda>x. return (stock_measure t') (op_sem oper x)) \<in> measurable ?N ?R"
    by (intro measurable_cong) simp
  have M_ret: "(\<lambda>x. return_val (op_sem oper x)) \<in> measurable (stock_measure t) ?R"
    by (subst M_cong, intro measurable_compose[OF measurable_op_sem[OF t2]] return_measurable)

  from M_e have [simp]: "sets (M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) = sets (stock_measure t)"
    by (intro sets_bind) (auto simp: M_def space_subprob_algebra dest!: measurable_space)
  from measurable_cong_sets[OF this refl]
    have M_op: "op_sem oper \<in> measurable (M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t')"
    by (auto intro!: measurable_op_sem t2)
  have [simp]: "space (M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) = space (stock_measure t)"
    by (rule sets_eq_imp_space_eq) simp

  from M_e and M_ret have "M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (oper $$ e)) =
                              (M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) \<bind> (\<lambda>x. return_val (op_sem oper x))"
    unfolding M_def by (subst expr_sem.simps, intro bind_assoc[symmetric]) simp_all
  also have "... = (M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) \<bind> (\<lambda>x. return (stock_measure t') (op_sem oper x))"
    by (intro bind_cong refl) (simp add: return_op_sem)
  also have "... = distr (M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t') (op_sem oper)"
    by (subst bind_return_distr[symmetric]) (simp_all add: o_def M_op)
  finally show ?thesis .
qed

end

lemma density_context_equiv:
  assumes "\<And>\<sigma>. \<sigma> \<in> space (state_measure (V \<union> V') \<Gamma>) \<Longrightarrow> \<delta> \<sigma> = \<delta>' \<sigma>"
  assumes [simp, measurable]: "\<delta>' \<in> borel_measurable (state_measure (V \<union> V') \<Gamma>)"
  assumes "density_context V V' \<Gamma> \<delta>"
  shows "density_context V V' \<Gamma> \<delta>'"
proof (unfold density_context_def, intro conjI allI impI subprob_spaceI)
  interpret density_context V V' \<Gamma> \<delta> by fact
  fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>') \<rho>"
  let ?N = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>"
  from \<rho> have "emeasure ?M (space ?M) = \<integral>\<^sup>+x. \<delta>' (merge V V' (x, \<rho>)) \<partial>state_measure V \<Gamma>"
     unfolding dens_ctxt_measure_def state_measure'_def
    apply (simp only: prod.case, subst space_density)
    apply (simp add: emeasure_density cong: nn_integral_cong')
    apply (subst nn_integral_distr, simp add: state_measure_def, simp_all)
    done
  also from \<rho> have "... = \<integral>\<^sup>+x. \<delta> (merge V V' (x, \<rho>)) \<partial>state_measure V \<Gamma>"
    by (intro nn_integral_cong, subst assms(1)) (simp_all add: merge_in_state_measure)
  also from \<rho> have "... = branch_prob (V,V',\<Gamma>,\<delta>) \<rho>" by (simp add: branch_prob_altdef)
  also have "... = emeasure ?N (space ?N)" by (simp add: branch_prob_def)
  also from \<rho> have "... \<le> 1" by (intro subprob_space.emeasure_space_le_1 subprob_space_dens)
  finally show "emeasure ?M (space ?M) \<le> 1" .
qed (insert assms, auto simp: density_context_def)

end

