(*
  Theory: PDF_Compiler_Pred.thy
  Authors: Manuel Eberl

  The abstract compiler that compiles a PDF expression into a (HOL) density function
  on the corresponding measure spaces.
*)

section \<open>Abstract PDF Compiler\<close>

theory PDF_Compiler_Pred
imports PDF_Semantics PDF_Density_Contexts PDF_Transformations Density_Predicates
begin

subsection \<open>Density compiler predicate\<close>

text \<open>
  Predicate version of the probability density compiler that compiles a expression
  to a probability density function of its distribution. The density is a HOL function of
  type @{typ "val \<Rightarrow> ennreal"}.
\<close>

inductive expr_has_density :: "dens_ctxt \<Rightarrow> expr \<Rightarrow> (state \<Rightarrow> val \<Rightarrow> ennreal) \<Rightarrow> bool"
              ("(1_ \<turnstile>\<^sub>d/ (_ \<Rightarrow>/ _))" [50,0,50] 50) where
  hd_AE:   "\<lbrakk>(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f; \<Gamma> \<turnstile> e : t;
             \<And>\<rho>. \<rho> \<in> space (state_measure V' \<Gamma>) \<Longrightarrow>
                     AE x in stock_measure t. f \<rho> x = f' \<rho> x;
             case_prod f' \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)\<rbrakk>
                \<Longrightarrow> (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f'"
| hd_dens_ctxt_cong:
           "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow> (\<And>\<sigma>. \<sigma> \<in> space (state_measure (V \<union> V') \<Gamma>) \<Longrightarrow> \<delta> \<sigma> = \<delta>' \<sigma>)
                 \<Longrightarrow> (V,V',\<Gamma>,\<delta>') \<turnstile>\<^sub>d e \<Rightarrow> f"
| hd_val:  "countable_type (val_type v) \<Longrightarrow>
                (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Val v \<Rightarrow> (\<lambda>\<rho> x. branch_prob (V,V',\<Gamma>,\<delta>) \<rho> * indicator {v} x)"
| hd_var:  "x \<in> V \<Longrightarrow> (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Var x \<Rightarrow> marg_dens (V,V',\<Gamma>,\<delta>) x"
| hd_let:  "\<lbrakk>({},V\<union>V',\<Gamma>,\<lambda>_. 1) \<turnstile>\<^sub>d e1 \<Rightarrow> f;
             (shift_var_set V,Suc`V',the(expr_type \<Gamma> e1) \<cdot> \<Gamma>,insert_dens V V' f \<delta>) \<turnstile>\<^sub>d e2 \<Rightarrow> g\<rbrakk>
            \<Longrightarrow> (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d LetVar e1 e2 \<Rightarrow> (\<lambda>\<rho>. g (case_nat undefined \<rho>))"
| hd_rand:  "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow> (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Random dst e \<Rightarrow> apply_dist_to_dens dst f"
| hd_rand_det: "randomfree e \<Longrightarrow> free_vars e \<subseteq> V' \<Longrightarrow>
                  (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Random dst e \<Rightarrow>
                     (\<lambda>\<rho> x. branch_prob (V,V',\<Gamma>,\<delta>) \<rho> * dist_dens dst (expr_sem_rf \<rho> e) x)"
| hd_fail: "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Fail t \<Rightarrow> (\<lambda>_ _. 0)"
| hd_pair: "x \<in> V \<Longrightarrow> y \<in> V \<Longrightarrow> x \<noteq> y \<Longrightarrow> (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d <Var x, Var y> \<Rightarrow> marg_dens2 (V,V',\<Gamma>,\<delta>) x y"
| hd_if:  "\<lbrakk>({},V\<union>V',\<Gamma>,\<lambda>_. 1) \<turnstile>\<^sub>d b \<Rightarrow> f;
             (V,V',\<Gamma>,if_dens \<delta> f True) \<turnstile>\<^sub>d e1 \<Rightarrow> g1; (V,V',\<Gamma>,if_dens \<delta> f False) \<turnstile>\<^sub>d e2 \<Rightarrow> g2\<rbrakk>
              \<Longrightarrow> (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d IF b THEN e1 ELSE e2 \<Rightarrow> (\<lambda>\<rho> x. g1 \<rho> x + g2 \<rho> x)"
| hd_if_det: "\<lbrakk>randomfree b; (V,V',\<Gamma>,if_dens_det \<delta> b True) \<turnstile>\<^sub>d e1 \<Rightarrow> g1;
               (V,V',\<Gamma>,if_dens_det \<delta> b False) \<turnstile>\<^sub>d e2 \<Rightarrow> g2\<rbrakk>
              \<Longrightarrow> (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d IF b THEN e1 ELSE e2 \<Rightarrow> (\<lambda>\<rho> x. g1 \<rho> x + g2 \<rho> x)"
| hd_fst:  "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow>
                (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Fst $$ e \<Rightarrow>
                    (\<lambda>\<rho> x. \<integral>\<^sup>+y. f \<rho> <|x,y|> \<partial>stock_measure (the (expr_type \<Gamma> (Snd $$ e))))"
| hd_snd:  "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow>
                (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Snd $$ e \<Rightarrow>
                    (\<lambda>\<rho> y. \<integral>\<^sup>+x. f \<rho> <|x,y|> \<partial>stock_measure (the (expr_type \<Gamma> (Fst $$ e))))"
| hd_op_discr: "countable_type (the (expr_type \<Gamma> (oper $$ e))) \<Longrightarrow> (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow>
                    (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d oper $$ e \<Rightarrow> (\<lambda>\<rho> y. \<integral>\<^sup>+x. (if op_sem oper x = y then 1 else 0) * f \<rho> x
                                                      \<partial>stock_measure (the (expr_type \<Gamma> e)))"
| hd_neg:  "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow>
                (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Minus $$ e \<Rightarrow> (\<lambda>\<sigma> x. f \<sigma> (op_sem Minus x))"
| hd_addc: "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow> randomfree e' \<Longrightarrow> free_vars e' \<subseteq> V' \<Longrightarrow>
                (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Add $$ <e, e'> \<Rightarrow>
                  (\<lambda>\<rho> x. f \<rho> (op_sem Add <|x, expr_sem_rf \<rho> (Minus $$ e')|>))"
| hd_multc: "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow> val_type c = REAL \<Longrightarrow> c \<noteq> RealVal 0 \<Longrightarrow>
                (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Mult $$ <e, Val c> \<Rightarrow>
                  (\<lambda>\<rho> x. f \<rho> (op_sem Mult <|x, op_sem Inverse c|>) *
                    inverse (abs (extract_real c)))"
| hd_exp: "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow>
               (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Exp $$ e \<Rightarrow>
                 (\<lambda>\<sigma> x. if extract_real x > 0 then
                           f \<sigma> (lift_RealVal safe_ln x) * inverse (extract_real x) else 0)"
| hd_inv: "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow>
               (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Inverse $$ e \<Rightarrow> (\<lambda>\<sigma> x. f \<sigma> (op_sem Inverse x) *
                                                  inverse (extract_real x) ^ 2)"
| hd_add: "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f \<Longrightarrow>
               (V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d Add $$ e \<Rightarrow> (\<lambda>\<sigma> z. \<integral>\<^sup>+x. f \<sigma> <|x, op_sem Add <|z, op_sem Minus x|>|>
                                                  \<partial>stock_measure (val_type z))"

lemmas expr_has_density_intros =
  hd_val hd_var hd_let hd_rand hd_rand_det hd_fail hd_pair hd_if hd_if_det
  hd_fst hd_snd hd_op_discr hd_neg hd_addc hd_multc hd_exp hd_inv hd_add

subsection \<open>Auxiliary lemmas\<close>

lemma has_subprob_density_distr_Fst:
  fixes t1 t2 f
  defines "N \<equiv> stock_measure (PRODUCT t1 t2)"
  defines "N' \<equiv> stock_measure t1"
  defines "fst' \<equiv> op_sem Fst"
  defines "f' \<equiv> \<lambda>x. \<integral>\<^sup>+y. f <|x,y|> \<partial>stock_measure t2"
  assumes dens: "has_subprob_density M N f"
  shows "has_subprob_density (distr M N' fst') N' f'"
proof (intro has_subprob_densityI measure_eqI)
  from dens interpret subprob_space M by (rule has_subprob_densityD)
  from dens have M_M: "measurable M = measurable N"
    by (intro ext measurable_cong_sets) (auto dest: has_subprob_densityD)
  hence meas_fst: "fst' \<in> measurable M N'" unfolding fst'_def
    by (subst op_sem.simps) (simp add: N'_def N_def M_M)
  thus "subprob_space (distr M N' fst')"
    by (rule subprob_space_distr) (simp_all add: N'_def)

  interpret sigma_finite_measure "stock_measure t2" by simp
  have f[measurable]: "f \<in> borel_measurable (stock_measure (PRODUCT t1 t2))"
    using dens by (auto simp: has_subprob_density_def has_density_def N_def)
  then show meas_f': "f' \<in> borel_measurable N'" unfolding f'_def N'_def
    by measurable

  let ?M1 = "distr M N' fst'" and ?M2 = "density N' f'"
  show "sets ?M1 = sets ?M2" by simp
  fix X assume "X \<in> sets ?M1"
  hence X: "X \<in> sets N'" "X \<in> sets N'" by (simp_all add: N'_def)
  then have [measurable]: "X \<in> sets (stock_measure t1)"
    by (simp add: N'_def)

  from meas_fst and X(1) have "emeasure ?M1 X = emeasure M (fst' -` X \<inter> space M)"
    by (rule emeasure_distr)
  also from dens have M: "M = density N f" by (rule has_subprob_densityD)
  from this and meas_fst have meas_fst': "fst' \<in> measurable N N'" by simp
  with dens and X have "emeasure M (fst' -` X \<inter> space M) =
                            \<integral>\<^sup>+x. f x * indicator (fst' -` X \<inter> space N) x \<partial>N"
    by (subst (1 2) M, subst space_density, subst emeasure_density)
       (erule has_subprob_densityD, erule measurable_sets, simp, simp)
  also have "N = distr (N' \<Otimes>\<^sub>M stock_measure t2) N (case_prod PairVal)" (is "_ = ?N")
    unfolding N_def N'_def stock_measure.simps by (rule embed_measure_eq_distr) (simp add: inj_PairVal)
  hence "\<And>f. nn_integral N f = nn_integral ... f" by simp
  also from dens and X
    have "(\<integral>\<^sup>+x. f x * indicator (fst' -` X \<inter> space N) x \<partial>?N) =
              \<integral>\<^sup>+x. f (case_prod PairVal x) * indicator (fst' -` X \<inter> space N) (case_prod PairVal x)
                \<partial>(N' \<Otimes>\<^sub>M stock_measure t2)"
      by (intro nn_integral_distr)
         (simp_all add: measurable_embed_measure2 N_def N'_def fst'_def)
  also from has_subprob_densityD(1)[OF dens] and X
    have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+y. f <|x,y|> * indicator (fst' -` X \<inter> space N) <|x, y|> \<partial>stock_measure t2 \<partial>N'"
             (is "_ = ?I")
    by (subst sigma_finite_measure.nn_integral_fst[symmetric])
       (auto simp: N_def N'_def fst'_def comp_def simp del: space_stock_measure)
  also from X have A: "\<And>x y. x \<in> space N' \<Longrightarrow> y \<in> space (stock_measure t2) \<Longrightarrow>
                          indicator (fst' -` X \<inter> space N) <|x, y|> = indicator X x"
    by (auto split: split_indicator simp: fst'_def N_def
                 space_embed_measure space_pair_measure N'_def)
  have "?I = \<integral>\<^sup>+x. \<integral>\<^sup>+y. f <|x,y|> * indicator X x \<partial>stock_measure t2 \<partial>N'"  (is "_ = ?I")
    by (intro nn_integral_cong) (simp add: A)
  also have A: "\<And>x. x \<in> space N' \<Longrightarrow> (\<lambda>y. f <|x,y|>) = f \<circ> case_prod PairVal \<circ> (\<lambda>y. (x,y))"
    by (intro ext) simp
  from dens have "?I = \<integral>\<^sup>+x. (\<integral>\<^sup>+y. f <|x,y|> \<partial>stock_measure t2) * indicator X x \<partial>N'"
    by (intro nn_integral_cong nn_integral_multc, subst A)
       (auto intro!: measurable_comp f measurable_PairVal simp: N'_def)
  also from meas_f' and X(2) have "... = emeasure ?M2 X" unfolding f'_def
    by (rule emeasure_density[symmetric])
  finally show "emeasure ?M1 X = emeasure ?M2 X" .
qed

lemma has_subprob_density_distr_Snd:
  fixes t1 t2 f
  defines "N \<equiv> stock_measure (PRODUCT t1 t2)"
  defines "N' \<equiv> stock_measure t2"
  defines "snd' \<equiv> op_sem Snd"
  defines "f' \<equiv> \<lambda>y. \<integral>\<^sup>+x. f <|x,y|> \<partial>stock_measure t1"
  assumes dens: "has_subprob_density M N f"
  shows "has_subprob_density (distr M N' snd') N' f'"
proof (intro has_subprob_densityI measure_eqI)
  from dens interpret subprob_space M by (rule has_subprob_densityD)
  from dens have M_M: "measurable M = measurable N"
    by (intro ext measurable_cong_sets) (auto dest: has_subprob_densityD)
  hence meas_snd: "snd' \<in> measurable M N'" unfolding snd'_def
    by (subst op_sem.simps) (simp add: N'_def N_def M_M)
  thus "subprob_space (distr M N' snd')"
    by (rule subprob_space_distr) (simp_all add: N'_def)

  interpret t1: sigma_finite_measure "stock_measure t1" by simp
  have A: "(\<lambda>(x, y). f <| x ,  y |>) = f \<circ> case_prod PairVal"
    by (intro ext) (simp add: o_def split: prod.split)
  have f[measurable]: "f \<in> borel_measurable (stock_measure (PRODUCT t1 t2))"
    using dens by (auto simp: has_subprob_density_def has_density_def N_def)
  then show meas_f': "f' \<in> borel_measurable N'" unfolding f'_def N'_def
    by measurable

  interpret N': sigma_finite_measure N'
    unfolding N'_def by (rule sigma_finite_stock_measure)

  interpret N'_t1: pair_sigma_finite t1 N' proof qed

  let ?M1 = "distr M N' snd'" and ?M2 = "density N' f'"
  show "sets ?M1 = sets ?M2" by simp
  fix X assume "X \<in> sets ?M1"
  hence X: "X \<in> sets N'" "X \<in> sets N'" by (simp_all add: N'_def)
  then have [measurable]: "X \<in> sets (stock_measure t2)"
    by (simp add: N'_def)

  from meas_snd and X(1) have "emeasure ?M1 X = emeasure M (snd' -` X \<inter> space M)"
    by (rule emeasure_distr)
  also from dens have M: "M = density N f" by (rule has_subprob_densityD)
  from this and meas_snd have meas_snd': "snd' \<in> measurable N N'" by simp
  with dens and X have "emeasure M (snd' -` X \<inter> space M) =
                            \<integral>\<^sup>+x. f x * indicator (snd' -` X \<inter> space N) x \<partial>N"
    by (subst (1 2) M, subst space_density, subst emeasure_density)
       (erule has_subprob_densityD, erule measurable_sets, simp, simp)
  also have "N = distr (stock_measure t1 \<Otimes>\<^sub>M N') N (case_prod PairVal)" (is "_ = ?N")
    unfolding N_def N'_def stock_measure.simps by (rule embed_measure_eq_distr) (simp add: inj_PairVal)
  hence "\<And>f. nn_integral N f = nn_integral ... f" by simp
  also from dens and X
    have "(\<integral>\<^sup>+x. f x * indicator (snd' -` X \<inter> space N) x \<partial>?N) =
              \<integral>\<^sup>+x. f (case_prod PairVal x) * indicator (snd' -` X \<inter> space N) (case_prod PairVal x)
                \<partial>(stock_measure t1 \<Otimes>\<^sub>M N')"
      by (intro nn_integral_distr)
         (simp_all add: measurable_embed_measure2 N_def N'_def snd'_def)
  also from has_subprob_densityD(1)[OF dens] and X
    have "... = \<integral>\<^sup>+y. \<integral>\<^sup>+x. f <|x,y|> * indicator (snd' -` X \<inter> space N) <|x, y|> \<partial>stock_measure t1 \<partial>N'"
      (is "\<dots> = ?I")
    by (subst N'_t1.nn_integral_snd[symmetric])
       (auto simp: N_def N'_def snd'_def comp_def simp del: space_stock_measure)
  also from X have A: "\<And>x y. x \<in> space N' \<Longrightarrow> y \<in> space (stock_measure t1) \<Longrightarrow>
                          indicator (snd' -` X \<inter> space N) <|y, x|> = indicator X x"
    by (auto split: split_indicator simp: snd'_def N_def
                 space_embed_measure space_pair_measure N'_def)
  have "?I = \<integral>\<^sup>+y. \<integral>\<^sup>+x. f <|x,y|> * indicator X y \<partial>stock_measure t1 \<partial>N'"  (is "_ = ?I")
    by (intro nn_integral_cong) (simp add: A)
  also have A: "\<And>y. y \<in> space N' \<Longrightarrow> (\<lambda>x. f <|x,y|>) = f \<circ> case_prod PairVal \<circ> (\<lambda>x. (x,y))"
    by (intro ext) simp
  from dens have "?I = \<integral>\<^sup>+y. (\<integral>\<^sup>+x. f <|x,y|> \<partial>stock_measure t1) * indicator X y \<partial>N'"
    by (intro nn_integral_cong nn_integral_multc) (auto simp: N'_def)
  also from meas_f' and X(2) have "... = emeasure ?M2 X" unfolding f'_def
    by (rule emeasure_density[symmetric])
  finally show "emeasure ?M1 X = emeasure ?M2 X" .
qed

lemma dens_ctxt_measure_empty_bind:
  assumes "\<rho> \<in> space (state_measure V' \<Gamma>)"
  assumes f[measurable]: "f \<in> measurable (state_measure V' \<Gamma>) (subprob_algebra N)"
  shows "dens_ctxt_measure ({},V',\<Gamma>,\<lambda>_. 1) \<rho> \<bind> f = f \<rho>" (is "bind ?M _ = ?R")
proof (intro measure_eqI)
  from assms have nonempty: "space ?M \<noteq> {}"
    by (auto simp: dens_ctxt_measure_def state_measure'_def state_measure_def space_PiM)
  moreover have meas: "measurable ?M = measurable (state_measure V' \<Gamma>)"
    by (intro ext measurable_cong_sets) (auto simp: dens_ctxt_measure_def state_measure'_def)
  moreover from assms have [simp]: "sets (f \<rho>) = sets N"
    by (intro sets_kernel[OF assms(2)])
  ultimately show sets_eq: "sets (?M \<bind> f) = sets ?R" using assms
    by (subst sets_bind[OF sets_kernel[OF f]])
       (simp_all add: dens_ctxt_measure_def state_measure'_def state_measure_def)

  from assms have [simp]: "\<And>\<sigma>. merge {} V' (\<sigma>,\<rho>) = \<rho>"
    by (intro ext) (auto simp: merge_def state_measure_def space_PiM)

  fix X assume X: "X \<in> sets (?M \<bind> f)"
  hence "emeasure (?M \<bind> f) X =  \<integral>\<^sup>+x. emeasure (f x) X \<partial>?M" using assms
    by (subst emeasure_bind[OF nonempty]) (simp_all add: nonempty meas sets_eq cong: measurable_cong_sets)
  also have "... = \<integral>\<^sup>+(x::state). emeasure (f \<rho>) X \<partial>count_space {\<lambda>_. undefined}"
    unfolding dens_ctxt_measure_def state_measure'_def state_measure_def using X assms
      apply (simp only: prod.case)
      apply (subst nn_integral_density)
      apply (auto intro!: measurable_compose[OF _ measurable_emeasure_subprob_algebra]
                  simp:  state_measure_def sets_eq PiM_empty) [3]
      apply (subst nn_integral_distr)
      apply (auto intro!: measurable_compose[OF _ measurable_emeasure_subprob_algebra]
                  simp: state_measure_def sets_eq PiM_empty)
    done
  also have "... = emeasure (f \<rho>) X"
    by (subst nn_integral_count_space_finite) (simp_all add: max_def)
  finally show "emeasure (?M \<bind> f) X = emeasure (f \<rho>) X" .
qed

lemma (in density_context) bind_dens_ctxt_measure_cong:
  assumes fg: "\<And>\<sigma>. (\<And>x. x \<in> V' \<Longrightarrow> \<sigma> x = \<rho> x) \<Longrightarrow> f \<sigma> = g \<sigma>"
  assumes \<rho>[measurable]: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  assumes Mf[measurable]: "f \<in> measurable (state_measure (V \<union> V') \<Gamma>) (subprob_algebra N)"
  assumes Mg[measurable]: "g \<in> measurable (state_measure (V \<union> V') \<Gamma>) (subprob_algebra N)"
  defines "M \<equiv> dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>"
  shows "M \<bind> f = M \<bind> g"
proof -
  have [measurable]: "(\<lambda>\<sigma>. merge V V' (\<sigma>, \<rho>)) \<in> measurable (state_measure V \<Gamma>) (state_measure (V \<union> V') \<Gamma>)"
    using \<rho> unfolding state_measure_def by simp
  show ?thesis
    using disjoint
    apply (simp add: M_def dens_ctxt_measure_def state_measure'_def density_distr)
    apply (subst (1 2) bind_distr)
    apply measurable
    apply (intro bind_cong_AE[where B=N] AE_I2 refl fg)
    apply measurable
    done
qed

lemma (in density_context) bin_op_randomfree_restructure:
  assumes t1: "\<Gamma> \<turnstile> e : t" and t2: "\<Gamma> \<turnstile> e' : t'" and t3: "op_type oper (PRODUCT t t') = Some tr"
  assumes rf: "randomfree e'" and vars1: "free_vars e \<subseteq> V\<union>V'" and vars2: "free_vars e' \<subseteq> V'"
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  defines "M \<equiv> dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>"
  defines "v \<equiv> expr_sem_rf \<rho> e'"
  shows "M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (oper $$ <e, e'>)) =
              distr (M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure tr) (\<lambda>w. op_sem oper <|w,v|>)"
proof-
  from assms have vars1': "\<And>\<sigma>. \<sigma> \<in> space M \<Longrightarrow> \<forall>x\<in>free_vars e. val_type (\<sigma> x) = \<Gamma> x"
               and vars2': "\<And>\<sigma>. \<sigma> \<in> space M \<Longrightarrow> \<forall>x\<in>free_vars e'. val_type (\<sigma> x) = \<Gamma> x"
    by (auto simp: M_def space_dens_ctxt_measure state_measure_def space_PiM
             dest: PiE_mem)
  have Me: "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<in>
                 measurable (state_measure (V \<union> V') \<Gamma>) (subprob_algebra (stock_measure t))"
    by (rule measurable_expr_sem[OF t1 vars1])

  from assms have e': "\<And>\<sigma>. \<sigma> \<in> space M \<Longrightarrow> expr_sem \<sigma> e' = return_val (expr_sem_rf \<sigma> e')"
    by (intro expr_sem_rf_sound[symmetric]) (auto simp: M_def space_dens_ctxt_measure)
  from assms have vt_e': "\<And>\<sigma>. \<sigma> \<in> space M \<Longrightarrow> val_type (expr_sem_rf \<sigma> e') = t'"
    by (intro val_type_expr_sem_rf) (auto simp: M_def space_dens_ctxt_measure)

  let ?tt' = "PRODUCT t t'"
  {
    fix \<sigma> assume \<sigma>: "\<sigma> \<in> space M"
    with vars2 have [simp]: "measurable (expr_sem \<sigma> e') = measurable (stock_measure t')"
      by (intro measurable_expr_sem_eq[OF t2, of _ "V\<union>V'"]) (auto simp: M_def space_dens_ctxt_measure)
    from \<sigma> have [simp]: "space (expr_sem \<sigma> e) = space (stock_measure t)"
                          "space (expr_sem \<sigma> e') = space (stock_measure t')"
      using space_expr_sem[OF t1 vars1'[OF \<sigma>]] space_expr_sem[OF t2 vars2'[OF \<sigma>]] by simp_all
    have "expr_sem \<sigma> e \<bind> (\<lambda>x. expr_sem \<sigma> e' \<bind> (\<lambda>y. return_val <| x ,  y |>)) =
            expr_sem \<sigma> e \<bind> (\<lambda>x. return_val (expr_sem_rf \<sigma> e') \<bind> (\<lambda>y. return_val <| x ,  y |>))"
      by (intro bind_cong refl, subst e'[OF \<sigma>]) simp
    also have "... = expr_sem \<sigma> e \<bind> (\<lambda>x. return_val <|x , expr_sem_rf \<sigma> e'|>)" using \<sigma> vars2
      by (intro bind_cong refl, subst bind_return_val'[of _ t' _ ?tt'])
         (auto simp: vt_e' M_def space_dens_ctxt_measure
               intro!: measurable_PairVal)
    finally have "expr_sem \<sigma> e \<bind> (\<lambda>x. expr_sem \<sigma> e' \<bind> (\<lambda>y. return_val <|x,y|>)) =
                     expr_sem \<sigma> e \<bind> (\<lambda>x. return_val <|x, expr_sem_rf \<sigma> e'|>)" .
  }
  hence "M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (oper $$ <e, e'>)) =
             M \<bind> (\<lambda>\<sigma>. (expr_sem \<sigma> e \<bind> (\<lambda>x. return_val <|x, expr_sem_rf \<sigma> e'|>))
                   \<bind> (\<lambda>x. return_val (op_sem oper x)))" (is "_ = ?T")
    by (intro bind_cong refl) (simp only: expr_sem.simps)
  also have [measurable]: "\<And>\<sigma>. \<sigma> \<in> space M \<Longrightarrow> expr_sem_rf \<sigma> e' \<in> space t'"
    by (simp add: type_universe_def vt_e' del: type_universe_type)
  note [measurable] = measurable_op_sem[OF t3]
  hence  "?T = M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e \<bind> (\<lambda>x. return_val (op_sem oper <|x, expr_sem_rf \<sigma> e'|>)))"
    (is "_ = ?T")
    by (intro bind_cong[OF refl], subst bind_assoc_return_val[of _ t _ ?tt' _ tr])
       (auto simp: sets_expr_sem[OF t1 vars1'])
  also have eq: "\<And>\<sigma>. (\<And>x. x \<in> V' \<Longrightarrow> \<sigma> x = \<rho> x) \<Longrightarrow> expr_sem_rf \<sigma> e' = expr_sem_rf \<rho> e'"
    using vars2 by (intro expr_sem_rf_eq_on_vars) auto
  have [measurable]: "(\<lambda>\<sigma>. expr_sem_rf \<sigma> e') \<in> measurable (state_measure (V \<union> V') \<Gamma>) (stock_measure t')"
    using vars2 by (intro measurable_expr_sem_rf[OF t2 rf]) blast
  note [measurable] = Me measurable_bind measurable_return_val
  have expr_sem_rf_space: "expr_sem_rf \<rho> e' \<in> space (stock_measure t')"
    using val_type_expr_sem_rf[OF t2 rf vars2 \<rho>]
    by (simp add: type_universe_def del: type_universe_type)
  hence "?T = M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e \<bind> (\<lambda>x. return_val (op_sem oper <|x,  expr_sem_rf \<rho> e'|>)))"
    using \<rho> unfolding M_def
    by (intro bind_dens_ctxt_measure_cong, subst eq) (simp, simp, simp, measurable)
  also have "... = (M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) \<bind>
                         return_val \<circ> (\<lambda>x. op_sem oper <|x, expr_sem_rf \<rho> e'|>)"
    using expr_sem_rf_space
      by (subst bind_assoc[of _ _ "stock_measure t" _ "stock_measure tr", symmetric])
         (simp_all add: M_def measurable_dens_ctxt_measure_eq o_def)
  also have "... = distr (M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure tr)
                      (\<lambda>x. op_sem oper <|x, expr_sem_rf \<rho> e'|>)" using Me expr_sem_rf_space
    by (subst bind_return_val_distr[of _ t _ tr])
       (simp_all add: M_def sets_expr_sem[OF t1 vars1'])
  finally show ?thesis unfolding v_def .
qed

lemma addc_density_measurable:
  assumes Mf: "case_prod f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
  assumes t_disj: "t = REAL \<or> t = INTEG" and t: "\<Gamma> \<turnstile> e' : t"
  assumes rf: "randomfree e'" and vars: "free_vars e' \<subseteq> V'"
  defines "f' \<equiv> (\<lambda>\<rho> x. f \<rho> (op_sem Add <|x, expr_sem_rf \<rho> (Minus $$ e')|>))"
  shows "case_prod f' \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
proof (insert t_disj, elim disjE)
  assume A: "t = REAL"
  from A and t have t': "\<Gamma> \<turnstile> e' : REAL" by simp
  with rf vars have vt_e':
    "\<And>\<rho>. \<rho> \<in> space (state_measure V' \<Gamma>) \<Longrightarrow> val_type (expr_sem_rf \<rho> e') = REAL"
    by (intro val_type_expr_sem_rf) simp_all
  let ?f' = "\<lambda>\<sigma> x. let c = expr_sem_rf \<sigma> e'
                    in  f \<sigma> (RealVal (extract_real x - extract_real c))"
  note Mf[unfolded A, measurable] and rf[measurable] and vars[measurable] and t[unfolded A, measurable]
  have "case_prod ?f' \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
    unfolding Let_def A by measurable
  also have "case_prod ?f' \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t) \<longleftrightarrow>
                case_prod f' \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
    by (intro measurable_cong)
       (auto simp: Let_def space_pair_measure A space_embed_measure f'_def lift_RealIntVal2_def
                   lift_RealIntVal_def extract_real_def
             dest!: vt_e' split: val.split)
  finally show ?thesis .
next
  assume A: "t = INTEG"
  with t have t': "\<Gamma> \<turnstile> e' : INTEG" by simp
  with rf vars have vt_e':
    "\<And>\<rho>. \<rho> \<in> space (state_measure V' \<Gamma>) \<Longrightarrow> val_type (expr_sem_rf \<rho> e') = INTEG"
    by (intro val_type_expr_sem_rf) simp_all
  let ?f' = "\<lambda>\<sigma> x. let c = expr_sem_rf \<sigma> e'
                    in  f \<sigma> (IntVal (extract_int x - extract_int c))"
  note Mf[unfolded A, measurable] and rf[measurable] and vars[measurable] and t[unfolded A, measurable]
  have Mdiff: "case_prod ((-) :: int \<Rightarrow> _) \<in>
                 measurable (count_space UNIV \<Otimes>\<^sub>M count_space UNIV) (count_space UNIV)" by simp
  have "case_prod ?f' \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
    unfolding Let_def A by measurable
  also have "case_prod ?f' \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t) \<longleftrightarrow>
                case_prod f' \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
    by (intro measurable_cong)
       (auto simp: Let_def space_pair_measure A space_embed_measure f'_def lift_RealIntVal2_def
                   lift_RealIntVal_def extract_int_def
             dest!: vt_e' split: val.split)
  finally show ?thesis .
qed

lemma (in density_context) emeasure_bind_if_dens_ctxt_measure:
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  defines "M \<equiv> dens_ctxt_measure \<Y> \<rho>"
  assumes Mf[measurable]: "f \<in> measurable M (subprob_algebra (stock_measure BOOL))"
  assumes Mg[measurable]: "g \<in> measurable M (subprob_algebra R)"
  assumes Mh[measurable]: "h \<in> measurable M (subprob_algebra R)"
  assumes densf: "has_parametrized_subprob_density (state_measure (V \<union> V') \<Gamma>)
                      f (stock_measure BOOL) \<delta>f"
  assumes densg: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                      (\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<lambda>\<sigma>. \<delta> \<sigma> * \<delta>f \<sigma> (BoolVal True)) \<rho> \<bind> g) R \<delta>g"
  assumes densh: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                      (\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<lambda>\<sigma>. \<delta> \<sigma> * \<delta>f \<sigma> (BoolVal False)) \<rho> \<bind> h) R \<delta>h"
  defines "P \<equiv> \<lambda>b. b = BoolVal True"
  shows "M \<bind> (\<lambda>x. f x \<bind> (\<lambda>b. if P b then g x else h x)) = density R (\<lambda>x. \<delta>g \<rho> x + \<delta>h \<rho> x)"
          (is "?lhs = ?rhs")
proof (intro measure_eqI)
  have sets_lhs: "sets ?lhs = sets R"
    apply (subst sets_bind_measurable[of _ _ R])
    apply measurable
    apply (simp_all add: P_def M_def)
    done
  thus "sets ?lhs = sets ?rhs" by simp

  fix X assume "X \<in> sets ?lhs"
  hence X: "X \<in> sets R" by (simp only: sets_lhs)
  from Mf have [simp]: "\<And>x. x \<in> space M \<Longrightarrow> sets (f x) = sets (stock_measure BOOL)"
    by (rule sets_kernel)
  note [simp] = sets_eq_imp_space_eq[OF this]
  from has_parametrized_subprob_densityD(3)[OF densf]
    have M\<delta>f[measurable]: "(\<lambda>(x, y). \<delta>f x y)
        \<in> borel_measurable (state_measure (V \<union> V') \<Gamma> \<Otimes>\<^sub>M stock_measure BOOL)"
      by (simp add: M_def dens_ctxt_measure_def state_measure'_def)
  have [measurable]: "Measurable.pred (stock_measure BOOL) P"
    unfolding P_def by simp
  have BoolVal_in_space: "BoolVal True \<in> space (stock_measure BOOL)"
                         "BoolVal False \<in> space (stock_measure BOOL)" by auto
  from Mg have Mg'[measurable]: "g \<in> measurable (state_measure (V \<union> V') \<Gamma>) (subprob_algebra R)"
    by (simp add: M_def measurable_dens_ctxt_measure_eq)
  from Mh have Mh'[measurable]: "h \<in> measurable (state_measure (V \<union> V') \<Gamma>) (subprob_algebra R)"
    by (simp add: M_def measurable_dens_ctxt_measure_eq)
  from densf have densf': "has_parametrized_subprob_density M f (stock_measure BOOL) \<delta>f"
    unfolding has_parametrized_subprob_density_def
    apply (subst measurable_cong_sets, subst sets_pair_measure_cong)
    apply (unfold M_def dens_ctxt_measure_def state_measure'_def, (subst prod.case)+) []
    apply (subst sets_density, subst sets_distr, rule refl, rule refl, rule refl, rule refl)
    apply (auto simp: M_def space_dens_ctxt_measure)
    done

  interpret dc_True: density_context V V' \<Gamma> "\<lambda>\<sigma>. \<delta> \<sigma> * \<delta>f \<sigma> (BoolVal True)"
    using density_context_if_dens[of _ \<delta>f True] densf unfolding if_dens_def by (simp add: stock_measure.simps)
  interpret dc_False: density_context V V' \<Gamma> "\<lambda>\<sigma>. \<delta> \<sigma> * \<delta>f \<sigma> (BoolVal False)"
    using density_context_if_dens[of _ \<delta>f False] densf unfolding if_dens_def by (simp add: stock_measure.simps)

  have "emeasure (M \<bind> (\<lambda>x. f x \<bind> (\<lambda>b. if P b then g x else h x))) X =
          \<integral>\<^sup>+x. emeasure (f x \<bind> (\<lambda>b. if P b then g x else h x)) X \<partial>M" using X
    by (subst emeasure_bind[of _ _ R], simp add: M_def, intro measurable_bind[OF Mf], measurable)
  also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+b. emeasure (if P b then g x else h x) X \<partial>f x \<partial>M"
    by (intro nn_integral_cong) (simp_all add: X emeasure_bind[where N=R])
  also have "... = \<integral>\<^sup>+x. \<integral>\<^sup>+b. emeasure (if P b then g x else h x) X * \<delta>f x b \<partial>stock_measure BOOL \<partial>M"
    using has_parametrized_subprob_densityD[OF densf]
    by (intro nn_integral_cong)
       (simp_all add: AE_count_space field_simps nn_integral_density
                      M_def space_dens_ctxt_measure stock_measure.simps)
  also have "... = \<integral>\<^sup>+x. emeasure (g x) X * \<delta>f x (BoolVal True) +
                        emeasure (h x) X * \<delta>f x (BoolVal False) \<partial>M"
    using has_parametrized_subprob_densityD[OF densf']
    by (intro nn_integral_cong, subst nn_integral_BoolVal)
       (auto simp: P_def nn_integral_BoolVal)
  also have "... = (\<integral>\<^sup>+x. emeasure (g x) X * \<delta>f x (BoolVal True) \<partial>M) +
                   (\<integral>\<^sup>+x. emeasure (h x) X * \<delta>f x (BoolVal False) \<partial>M)" using X
    using has_parametrized_subprob_densityD[OF densf'] BoolVal_in_space
    by (intro nn_integral_add) (auto simp:)
  also have "(\<integral>\<^sup>+x. emeasure (g x) X * \<delta>f x (BoolVal True) \<partial>M) =
                  \<integral>\<^sup>+x. \<delta> (merge V V' (x, \<rho>)) * \<delta>f (merge V V' (x, \<rho>)) (BoolVal True) *
                         (emeasure (g (merge V V' (x, \<rho>)))) X \<partial>state_measure V \<Gamma>"
    using X has_parametrized_subprob_densityD[OF densf] BoolVal_in_space unfolding M_def
    by (subst nn_integral_dens_ctxt_measure) (simp_all add: \<rho> mult_ac)
  also have "... = emeasure (density R (\<delta>g \<rho>)) X" using \<rho> X
    apply (subst dc_True.nn_integral_dens_ctxt_measure[symmetric], simp_all) []
    apply (subst emeasure_bind[of _ _ R, symmetric], simp_all add: measurable_dens_ctxt_measure_eq) []
    apply (subst has_parametrized_subprob_densityD(1)[OF densg], simp_all)
    done
  also have "(\<integral>\<^sup>+x. emeasure (h x) X * \<delta>f x (BoolVal False) \<partial>M) =
                  \<integral>\<^sup>+x. \<delta> (merge V V' (x, \<rho>)) * \<delta>f (merge V V' (x, \<rho>)) (BoolVal False) *
                         (emeasure (h (merge V V' (x, \<rho>)))) X \<partial>state_measure V \<Gamma>"
    using X has_parametrized_subprob_densityD[OF densf] BoolVal_in_space unfolding M_def
    by (subst nn_integral_dens_ctxt_measure) (simp_all add: \<rho> mult_ac)
  also have "... = emeasure (density R (\<delta>h \<rho>)) X" using \<rho> X
    apply (subst dc_False.nn_integral_dens_ctxt_measure[symmetric], simp_all) []
    apply (subst emeasure_bind[of _ _ R, symmetric], simp_all add: measurable_dens_ctxt_measure_eq) []
    apply (subst has_parametrized_subprob_densityD(1)[OF densh], simp_all)
    done
  also have "emeasure (density R (\<delta>g \<rho>)) X + emeasure (density R (\<delta>h \<rho>)) X =
                 emeasure (density R (\<lambda>x. \<delta>g \<rho> x + \<delta>h \<rho> x)) X" using X \<rho>
    using has_parametrized_subprob_densityD(2,3)[OF densg]
          has_parametrized_subprob_densityD(2,3)[OF densh]
    by (intro emeasure_density_add) simp_all
  finally show "emeasure ?lhs X = emeasure ?rhs X" .
qed

lemma (in density_context) emeasure_bind_if_det_dens_ctxt_measure:
  fixes f
  assumes \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
  defines "M \<equiv> dens_ctxt_measure \<Y> \<rho>"
  defines "P \<equiv> \<lambda>b. f b = BoolVal True" and "P' \<equiv> \<lambda>b. f b = BoolVal False"
  assumes dc1: "density_context V V' \<Gamma> (\<lambda>\<sigma>. \<delta> \<sigma> * (if P \<sigma> then 1 else 0))"
  assumes dc2: "density_context V V' \<Gamma> (\<lambda>\<sigma>. \<delta> \<sigma> * (if P' \<sigma> then 1 else 0))"
  assumes Mf[measurable]: "f \<in> measurable M (stock_measure BOOL)"
  assumes Mg[measurable]: "g \<in> measurable M (subprob_algebra R)"
  assumes Mh[measurable]: "h \<in> measurable M (subprob_algebra R)"
  assumes densg: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                      (\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<lambda>\<sigma>. \<delta> \<sigma> * (if P \<sigma> then 1 else 0)) \<rho> \<bind> g) R \<delta>g"
  assumes densh: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                      (\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<lambda>\<sigma>. \<delta> \<sigma> * (if P' \<sigma> then 1 else 0)) \<rho> \<bind> h) R \<delta>h"
  shows "M \<bind> (\<lambda>x. if P x then g x else h x) = density R (\<lambda>x. \<delta>g \<rho> x + \<delta>h \<rho> x)"
          (is "?lhs = ?rhs")
proof (intro measure_eqI)
  have [measurable]: "Measurable.pred M P"
    unfolding P_def by (rule pred_eq_const1[OF Mf]) simp
  have [measurable]: "Measurable.pred M P'"
    unfolding P'_def by (rule pred_eq_const1[OF Mf]) simp
  have sets_lhs: "sets ?lhs = sets R"
    by (subst sets_bind_measurable[of _ _ R]) (simp_all, simp add: M_def)
  thus "sets ?lhs = sets ?rhs" by simp
  from Mg have Mg'[measurable]: "g \<in> measurable (state_measure (V \<union> V') \<Gamma>) (subprob_algebra R)"
    by (simp add: M_def measurable_dens_ctxt_measure_eq)
  from Mh have Mh'[measurable]: "h \<in> measurable (state_measure (V \<union> V') \<Gamma>) (subprob_algebra R)"
    by (simp add: M_def measurable_dens_ctxt_measure_eq)
  have [simp]: "\<And>x. x \<in> space M \<Longrightarrow> sets (g x) = sets R"
    by (rule sets_kernel[OF Mg])
  have [simp]: "\<And>x. x \<in> space M \<Longrightarrow> sets (h x) = sets R"
    by (rule sets_kernel[OF Mh])
  have [simp]: "sets M = sets (state_measure (V \<union> V') \<Gamma>)"
    by (simp add: M_def dens_ctxt_measure_def state_measure'_def)
  then have [measurable_cong]: "sets (state_measure (V \<union> V') \<Gamma>) = sets M" ..
  have [simp]: "range BoolVal = {BoolVal True, BoolVal False}" by auto

  fix X assume "X \<in> sets ?lhs"
  hence X[measurable]: "X \<in> sets R" by (simp only: sets_lhs)

  interpret dc_True: density_context V V' \<Gamma> "\<lambda>\<sigma>. \<delta> \<sigma> * (if P \<sigma> then 1 else 0)" by fact
  interpret dc_False: density_context V V' \<Gamma> "\<lambda>\<sigma>. \<delta> \<sigma> * (if P' \<sigma> then 1 else 0)" by fact

  have "emeasure (M \<bind> (\<lambda>x. if P x then g x else h x)) X =
          \<integral>\<^sup>+x. (if P x then emeasure (g x) X else emeasure (h x) X) \<partial>M" using X
    by (subst emeasure_bind[of _ _ R], simp add: M_def, measurable)
       (intro nn_integral_cong, simp)
  also have "... = \<integral>\<^sup>+x. (if P x then 1 else 0) * emeasure (g x) X +
                        (if P' x then 1 else 0) * emeasure (h x) X \<partial>M" using X
    using measurable_space[OF Mf]
    by (intro nn_integral_cong) (auto simp add: P_def P'_def stock_measure.simps)
  also have "... = (\<integral>\<^sup>+x. (if P x then 1 else 0) * emeasure (g x) X \<partial>M) +
                   (\<integral>\<^sup>+x. (if P' x then 1 else 0) * emeasure (h x) X \<partial>M)" using X
    by (intro nn_integral_add) (simp_all add:)
  also have "... = (\<integral>\<^sup>+ y. \<delta>g \<rho> y * indicator X y \<partial>R) + (\<integral>\<^sup>+ y. \<delta>h \<rho> y * indicator X y \<partial>R)"
    unfolding M_def using \<rho> X
    apply (simp add: nn_integral_dens_ctxt_measure)
    apply (subst (1 2) mult.assoc[symmetric])
    apply (subst dc_True.nn_integral_dens_ctxt_measure[symmetric], simp, simp)
    apply (subst dc_False.nn_integral_dens_ctxt_measure[symmetric], simp, simp)
    apply (subst (1 2) emeasure_bind[symmetric], simp_all add: measurable_dens_ctxt_measure_eq)
    apply measurable
    apply (subst emeasure_has_parametrized_subprob_density[OF densg], simp, simp)
    apply (subst emeasure_has_parametrized_subprob_density[OF densh], simp_all)
    done
  also have "... = emeasure (density R (\<lambda>x. \<delta>g \<rho> x + \<delta>h \<rho> x)) X" using X \<rho>
    using has_parametrized_subprob_densityD(2,3)[OF densg]
    using has_parametrized_subprob_densityD(2,3)[OF densh]
    apply (subst (1 2) emeasure_density[symmetric], simp_all) []
    apply (intro emeasure_density_add, simp_all)
    done
  finally show "emeasure ?lhs X = emeasure ?rhs X" .
qed


subsection \<open>Soundness proof\<close>

lemma restrict_state_measure[measurable]:
  "(\<lambda>x. restrict x V') \<in> measurable (state_measure (V \<union> V') \<Gamma>) (state_measure V' \<Gamma>)"
  by (simp add: state_measure_def)

lemma expr_has_density_sound_op:
  assumes dens_ctxt: "density_context V V' \<Gamma> \<delta>"
  assumes dens: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                   (\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) f"
  assumes Mg: "case_prod g \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t')"
  assumes dens': "\<And>M \<rho>. has_subprob_density M (stock_measure t) (f \<rho>) \<Longrightarrow>
                            has_density (distr M (stock_measure t') (op_sem oper))
                                        (stock_measure t') (g \<rho>)"
  assumes t1: "\<Gamma> \<turnstile> e : t" and t2 : "op_type oper t = Some t'"
  assumes free_vars: "free_vars (oper $$ e) \<subseteq> V \<union> V'"
  shows "has_parametrized_subprob_density (state_measure V' \<Gamma>)
           (\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (oper $$ e))) (stock_measure t') g"
proof-
  interpret density_context V V' \<Gamma> \<delta> by fact
  show ?thesis unfolding has_parametrized_subprob_density_def
  proof (intro conjI ballI impI)
    show "case_prod g \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t')" by fact

    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>"
    have Me: "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<in> measurable ?M (subprob_algebra (stock_measure t))"
      by (subst measurable_dens_ctxt_measure_eq)
         (insert assms t1, auto intro!: measurable_expr_sem)
    from dens and \<rho> have dens: "has_subprob_density (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) (f \<rho>)"
        unfolding has_parametrized_subprob_density_def by auto
    have "has_subprob_density (distr (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t') (op_sem oper))
                           (stock_measure t') (g \<rho>)" (is "has_subprob_density ?N _ _")
    proof (unfold has_subprob_density_def, intro conjI)
      show "subprob_space ?N"
        apply (intro subprob_space.subprob_space_distr has_subprob_densityD[OF dens])
        apply (subst measurable_cong_sets[OF sets_bind_measurable refl])
        apply (rule Me)
        apply (simp_all add: measurable_op_sem t2)
        done
      from dens show "has_density ?N (stock_measure t') (g \<rho>)"
        by (intro dens') (simp add: has_subprob_density_def)
    qed
    also from assms and \<rho>
      have "?N = ?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (oper $$ e))"
      by (intro expr_sem_op_eq_distr[symmetric] expr_typing.intros) simp_all
    finally show "has_subprob_density ... (stock_measure t') (g \<rho>)" .
  qed
qed

lemma expr_has_density_sound_aux:
  assumes "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f" "\<Gamma> \<turnstile> e : t"
          "density_context V V' \<Gamma> \<delta>" "free_vars e \<subseteq> V \<union> V'"
  shows "has_parametrized_subprob_density (state_measure V' \<Gamma>)
             (\<lambda>\<rho>. do {\<sigma> \<leftarrow> dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>; expr_sem \<sigma> e}) (stock_measure t)
             (\<lambda>\<rho> x. f \<rho> x)"
using assms
proof (induction arbitrary: t rule: expr_has_density.induct[split_format (complete)])
  case (hd_AE V V' \<Gamma> \<delta> e f t f' t')
  from \<open>\<Gamma> \<turnstile> e : t'\<close> and \<open>\<Gamma> \<turnstile> e : t\<close> have t[simp]: "t' = t"
    by (rule expr_typing_unique)
  have "has_parametrized_subprob_density (state_measure V' \<Gamma>)
          (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) f" (is ?P)
    by (intro hd_AE.IH) fact+
  from has_parametrized_subprob_density_dens_AE[OF hd_AE.hyps(3,4) this] show ?case by simp
next

  case (hd_dens_ctxt_cong V V' \<Gamma> \<delta> e f \<delta>' t)
  interpret dc': density_context V V' \<Gamma> \<delta>' by fact
  from hd_dens_ctxt_cong.hyps and dc'.measurable_dens
    have [simp]: "\<delta> \<in> borel_measurable (state_measure (V \<union> V') \<Gamma>)"
    by (erule_tac subst[OF measurable_cong, rotated]) simp
  hence "density_context V V' \<Gamma> \<delta>"
    by (intro density_context_equiv[OF hd_dens_ctxt_cong.hyps(2)[symmetric]])
       (insert hd_dens_ctxt_cong.prems hd_dens_ctxt_cong.hyps, simp_all)
  hence "has_parametrized_subprob_density (state_measure V' \<Gamma>)
          (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) f" (is ?P)
    using hd_dens_ctxt_cong.prems hd_dens_ctxt_cong.hyps
    by (intro hd_dens_ctxt_cong.IH) simp_all
  also have "\<And>\<sigma>. \<sigma> \<in> space (state_measure V' \<Gamma>) \<Longrightarrow>
                dens_ctxt_measure (V, V', \<Gamma>, \<delta>') \<sigma> = dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<sigma>"
    by (auto simp: dens_ctxt_measure_def state_measure'_def AE_distr_iff hd_dens_ctxt_cong.hyps
             intro!: density_cong)
  hence "?P \<longleftrightarrow> ?case" by (intro has_parametrized_subprob_density_cong) simp
  finally show ?case .

next
  case (hd_val v V V' \<Gamma> \<delta> t)
  hence [simp]: "t = val_type v" by auto
  interpret density_context V V' \<Gamma> \<delta> by fact
  show ?case
  proof (rule has_parametrized_subprob_densityI)
    show "(\<lambda>(\<rho>, y). branch_prob (V,V',\<Gamma>,\<delta>) \<rho> * indicator {v} y) \<in>
              borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      by (subst measurable_split_conv)
         (auto intro!: measurable_compose[OF measurable_snd borel_measurable_indicator]
                       borel_measurable_times_ennreal)
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    have return_probspace: "prob_space (return_val v)" unfolding return_val_def
      by (simp add: prob_space_return)
    thus "subprob_space (dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Val v)))" using \<rho>
      by (auto simp: return_val_def
              intro!: measurable_compose[OF measurable_const return_measurable] subprob_space_bind
                      subprob_space_dens hd_val.prems)
    from hd_val.hyps have "stock_measure (val_type v) = count_space (type_universe t)"
      by (simp add: countable_type_imp_count_space)
    thus "dens_ctxt_measure \<Y> \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Val v)) =
            density (stock_measure t) (\<lambda>x. branch_prob \<Y> \<rho> * indicator {v} x)"
      by (subst expr_sem.simps, subst dens_ctxt_measure_bind_const, insert return_probspace)
         (auto simp: return_val_def return_count_space_eq_density \<rho>
                     density_density_eq field_simps intro!: prob_space_imp_subprob_space)
  qed

next
  case (hd_var x V V' \<Gamma> \<delta> t)
  hence t: "t = \<Gamma> x" by auto
  interpret density_context V V' \<Gamma> \<delta> by fact
  from hd_var have "x \<in> V" by simp
  show ?case
  proof (rule has_parametrized_subprob_densityI)
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    have "subprob_space (dens_ctxt_measure \<Y> \<rho> \<bind> (\<lambda>\<sigma>. return (stock_measure t) (\<sigma> x)))"
      (is "subprob_space (?M \<bind> ?f)") using hd_var \<rho>
      by (intro subprob_space_bind)
         (auto simp: return_val_def t intro!: subprob_space_bind subprob_space_dens
                 measurable_compose[OF measurable_dens_ctxt_measure_component return_measurable])
    also from hd_var.hyps have "?M \<bind> ?f = ?M \<bind> (\<lambda>\<sigma>. return_val (\<sigma> x))"
      by (intro bind_cong) (auto simp: return_val_def t space_dens_ctxt_measure
                                 state_measure_def space_PiM dest!: PiE_mem)
    finally show "subprob_space (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Var x)))" by simp

    from hd_var interpret dcm: subprob_space "dens_ctxt_measure \<Y> \<rho>"
      by (intro subprob_space_dens \<rho>)
    let ?M1 = "dens_ctxt_measure \<Y> \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Var x))"
    let ?M2 = "density (stock_measure t) (\<lambda>v. marg_dens \<Y> x \<rho> v)"
    have "\<forall>\<sigma>\<in>space (dens_ctxt_measure \<Y> \<rho>). val_type (\<sigma> x) = t" using hd_var
      by (auto simp: space_dens_ctxt_measure space_PiM  PiE_iff
                     state_measure_def intro: type_universe_type)
    hence "?M1 = dens_ctxt_measure \<Y> \<rho> \<bind> (return (stock_measure t) \<circ> (\<lambda>\<sigma>. \<sigma> x))"
      by (intro bind_cong_All) (simp add: return_val_def)
    also have "... = distr (dens_ctxt_measure \<Y> \<rho>) (stock_measure t) (\<lambda>\<sigma>. \<sigma> x)"
      using dcm.subprob_not_empty hd_var
      by (subst bind_return_distr) (auto intro!: measurable_dens_ctxt_measure_component)
    also have "... = ?M2" using density_marg_dens_eq[OF \<open>x \<in> V\<close>]
      by (simp add: t hd_var.prems \<rho>)
    finally show "?M1 = ?M2" .
  qed (auto intro!: measurable_marg_dens' simp: hd_var t)

next
  case (hd_let V V' \<Gamma> e1 f \<delta> e2 g t)
  let ?t = "the (expr_type \<Gamma> e1)"
  let ?\<Gamma>' = "case_nat ?t \<Gamma>" and ?\<delta>' = "insert_dens V V' f \<delta>"
  let ?\<Y>' = "(shift_var_set V, Suc`V', ?\<Gamma>', ?\<delta>')"
  from hd_let.prems have t1: "\<Gamma> \<turnstile> e1 : ?t" and t2: "?\<Gamma>' \<turnstile> e2 : t"
      by (auto simp: expr_type_Some_iff[symmetric] split: option.split_asm)
  interpret dc: density_context V V' \<Gamma> \<delta> by fact

  show ?case unfolding has_parametrized_subprob_density_def
  proof (intro ballI conjI)
    have "density_context {} (V \<union> V') \<Gamma> (\<lambda>a. 1)" by (rule dc.density_context_empty)
    moreover note hd_let.prems
    ultimately have "has_parametrized_subprob_density (state_measure (V \<union> V') \<Gamma>)
                         (\<lambda>\<rho>. dens_ctxt_measure ({},V\<union>V',\<Gamma>,\<lambda>a. 1) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e1))
                         (stock_measure ?t) f" (is "?P")
      by (intro hd_let.IH(1)) (auto intro!: t1)
    also have "?P \<longleftrightarrow> has_parametrized_subprob_density (state_measure (V \<union> V') \<Gamma>)
                         (\<lambda>\<sigma>. expr_sem \<sigma> e1) (stock_measure ?t) f" using hd_let.prems
      by (intro has_parametrized_subprob_density_cong dens_ctxt_measure_empty_bind)
         (auto simp: dens_ctxt_measure_def state_measure'_def
               intro!: measurable_expr_sem[OF t1])
    finally have f: "has_parametrized_subprob_density (state_measure (V\<union>V') \<Gamma>)
                         (\<lambda>\<rho>. expr_sem \<rho> e1) (stock_measure ?t) f" .
    have g: "has_parametrized_subprob_density (state_measure (Suc`V') ?\<Gamma>')
                 (\<lambda>\<rho>. dens_ctxt_measure ?\<Y>' \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e2)) (stock_measure t) g"
      using hd_let.prems hd_let.hyps f subset_shift_var_set
      by (intro hd_let.IH(2) t2 dc.density_context_insert)
         (auto dest: has_parametrized_subprob_densityD)

    note g[measurable]
    thus "(\<lambda>(\<rho>, x). g (case_nat undefined \<rho>) x) \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      by simp

    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>" and
        ?N = "state_measure (shift_var_set (V\<union>V')) ?\<Gamma>'"
    have M_dcm: "measurable ?M = measurable (state_measure (V\<union>V') \<Gamma>)"
      by (intro ext measurable_cong_sets)
         (auto simp: dens_ctxt_measure_def state_measure_def state_measure'_def)
    have M_dcm': "\<And>N. measurable (?M \<Otimes>\<^sub>M N) = measurable (state_measure (V\<union>V') \<Gamma> \<Otimes>\<^sub>M N)"
      by (intro ext measurable_cong_sets)
         (auto simp: dens_ctxt_measure_def state_measure_def state_measure'_def)
    have "?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (LetVar e1 e2)) =
            do {\<sigma> \<leftarrow> ?M; y \<leftarrow> expr_sem \<sigma> e1; return ?N (case_nat y \<sigma>)} \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e2)"
            (is "_ = bind ?R _")
      using hd_let.prems subset_shift_var_set
      apply (simp only: expr_sem.simps, intro double_bind_assoc)
      apply (rule measurable_expr_sem[OF t2], simp)
      apply (subst M_dcm, rule measurable_expr_sem[OF t1], simp)
      apply (subst M_dcm', simp)
      done
    also from t1 and hd_let.prems
      have "(\<lambda>\<sigma>. expr_sem \<sigma> e1) \<in>
                measurable (state_measure (V \<union> V') \<Gamma>) (subprob_algebra (stock_measure ?t))"
      by (intro measurable_expr_sem) auto
    hence "?R = dens_ctxt_measure ?\<Y>' (case_nat undefined \<rho>)" using hd_let.prems hd_let.hyps f \<rho>
      by (intro dc.dens_ctxt_measure_insert) (auto simp: has_parametrized_subprob_density_def)
    also have "case_nat undefined \<rho> \<in> space (state_measure (Suc`V') ?\<Gamma>')"
      by (rule measurable_space[OF measurable_case_nat_undefined \<rho>])
    with g have "has_subprob_density (dens_ctxt_measure ?\<Y>' (case_nat undefined \<rho>) \<bind>
                           (\<lambda>\<sigma>. expr_sem \<sigma> e2)) (stock_measure t) (g (case_nat undefined \<rho>))"
      using \<rho> unfolding has_parametrized_subprob_density_def by auto
    finally show "has_subprob_density (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (LetVar e1 e2))) (stock_measure t)
                                      (g (case_nat undefined \<rho>))" .
  qed

next
  case (hd_rand_det e V' V \<Gamma> \<delta> dst t)
  then have [measurable]: "\<Gamma>  \<turnstile> e : dist_param_type dst" "randomfree e" "free_vars e \<subseteq> V'"
    by auto

  interpret density_context V V' \<Gamma> \<delta> by fact
  from hd_rand_det have t: "t = dist_result_type dst" by auto

  {
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>" and ?t = "dist_param_type dst"
    have "?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Random dst e)) =
              ?M \<bind> (\<lambda>\<sigma>. return_val (expr_sem_rf \<sigma> e) \<bind> dist_measure dst)" (is "_ = ?N")
      using hd_rand_det by (subst expr_sem.simps, intro bind_cong refl, subst expr_sem_rf_sound)
                           (auto simp: dens_ctxt_measure_def state_measure'_def)
    also from hd_rand_det have A: "\<And>\<sigma>. \<sigma> \<in> space ?M \<Longrightarrow> val_type (expr_sem_rf \<sigma> e) = ?t"
      by (intro val_type_expr_sem_rf) (auto simp: dens_ctxt_measure_def state_measure'_def)
    hence "?N = ?M \<bind> (\<lambda>\<sigma>. return (stock_measure ?t) (expr_sem_rf \<sigma> e) \<bind> dist_measure dst)"
      using hd_rand_det unfolding return_val_def
      by (intro bind_cong) (auto simp: dens_ctxt_measure_def state_measure'_def)
    also have "... = ?M \<bind> (\<lambda>\<sigma>. dist_measure dst (expr_sem_rf \<sigma> e))"
      unfolding return_val_def
      by (intro bind_cong refl bind_return, rule measurable_dist_measure)
         (auto simp: type_universe_def A simp del: type_universe_type)
    finally have "?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Random dst e)) =
                      ?M \<bind> (\<lambda>\<sigma>. dist_measure dst (expr_sem_rf \<sigma> e))" .
  } note A = this

  have "has_parametrized_subprob_density (state_measure V' \<Gamma>)
            (\<lambda>\<rho>. dens_ctxt_measure \<Y> \<rho> \<bind> (\<lambda>\<sigma>. dist_measure dst (expr_sem_rf \<sigma> e)))
            (stock_measure t) (\<lambda>\<rho> x. branch_prob \<Y> \<rho> * dist_dens dst (expr_sem_rf \<rho> e) x)"
  proof (unfold has_parametrized_subprob_density_def, intro conjI ballI)
    show M: "(\<lambda>(\<rho>, v). branch_prob \<Y> \<rho> * dist_dens dst (expr_sem_rf \<rho> e) v)
                \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      by (subst t) measurable

    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>" and ?t = "dist_param_type dst"
    have "?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Random dst e)) =
              ?M \<bind> (\<lambda>\<sigma>. return_val (expr_sem_rf \<sigma> e) \<bind> dist_measure dst)" (is "_ = ?N")
      using hd_rand_det by (subst expr_sem.simps, intro bind_cong refl, subst expr_sem_rf_sound)
                           (auto simp: dens_ctxt_measure_def state_measure'_def)
    also from hd_rand_det have A: "\<And>\<sigma>. \<sigma> \<in> space ?M \<Longrightarrow> val_type (expr_sem_rf \<sigma> e) = ?t"
      by (intro val_type_expr_sem_rf) (auto simp: dens_ctxt_measure_def state_measure'_def)
    hence "?N = ?M \<bind> (\<lambda>\<sigma>. return (stock_measure ?t) (expr_sem_rf \<sigma> e) \<bind> dist_measure dst)"
      using hd_rand_det unfolding return_val_def
      by (intro bind_cong) (auto simp: dens_ctxt_measure_def state_measure'_def)
    also have "... = ?M \<bind> (\<lambda>\<sigma>. dist_measure dst (expr_sem_rf \<sigma> e))"
      unfolding return_val_def
      by (intro bind_cong refl bind_return, rule measurable_dist_measure)
         (auto simp: type_universe_def A simp del: type_universe_type)
    also have "has_subprob_density (?M \<bind> (\<lambda>\<sigma>. dist_measure dst (expr_sem_rf \<sigma> e))) (stock_measure t)
              (\<lambda>v. \<integral>\<^sup>+\<sigma>. dist_dens dst (expr_sem_rf (restrict \<sigma> V') e) v \<partial>?M)"
              (is "has_subprob_density ?N ?R ?f")
    proof (rule bind_has_subprob_density)
      show "space ?M \<noteq> {}" unfolding dens_ctxt_measure_def state_measure'_def state_measure_def
        by (auto simp: space_PiM PiE_eq_empty_iff)
      show "(\<lambda>\<sigma>. dist_measure dst (expr_sem_rf \<sigma> e)) \<in> measurable ?M (subprob_algebra (stock_measure t))"
        unfolding dens_ctxt_measure_def state_measure'_def
        by (subst t, rule measurable_compose[OF _ measurable_dist_measure], simp)
           (insert hd_rand_det, auto intro!: measurable_expr_sem_rf)
      show "(\<lambda>(x, y). dist_dens dst (expr_sem_rf (restrict x V') e) y)
               \<in> borel_measurable (?M \<Otimes>\<^sub>M stock_measure t)"
        unfolding t by measurable
      fix \<sigma> assume \<sigma>: "\<sigma> \<in> space ?M"
      hence \<sigma>': "restrict \<sigma> V' \<in> space (state_measure V' \<Gamma>)"
        unfolding dens_ctxt_measure_def state_measure'_def state_measure_def restrict_def
        by (auto simp: space_PiM)
      from hd_rand_det have restr: "expr_sem_rf (restrict \<sigma> V') e = expr_sem_rf \<sigma> e"
        by (intro expr_sem_rf_eq_on_vars) auto
      from hd_rand_det have "val_type (expr_sem_rf (restrict \<sigma> V') e) = dist_param_type dst"
        by (auto intro!: val_type_expr_sem_rf[OF _ _ _ \<sigma>'])
      also note restr
      finally have "has_density (dist_measure dst (expr_sem_rf \<sigma> e)) (stock_measure t)
               (dist_dens dst (expr_sem_rf \<sigma> e))" using hd_rand_det
        by (subst t, intro dist_measure_has_density)
           (auto intro!: val_type_expr_sem_rf simp: type_universe_def dens_ctxt_measure_def
                 state_measure'_def simp del: type_universe_type)
       thus "has_density (dist_measure dst (expr_sem_rf \<sigma> e)) (stock_measure t)
                (dist_dens dst (expr_sem_rf (restrict \<sigma> V') e))" by (simp add: restr)
    qed (insert \<rho>, auto intro!: subprob_space_dens)
    moreover have "val_type (expr_sem_rf \<rho> e) = dist_param_type dst" using hd_rand_det \<rho>
      by (intro val_type_expr_sem_rf) auto
    hence "expr_sem_rf \<rho> e \<in> type_universe (dist_param_type dst)"
      by (simp add: type_universe_def del: type_universe_type)
    ultimately show "has_subprob_density (?M \<bind> (\<lambda>\<sigma>. dist_measure dst (expr_sem_rf \<sigma> e)))
                       (stock_measure t) (\<lambda>v. branch_prob \<Y> \<rho> * dist_dens dst (expr_sem_rf \<rho> e) v)"
      using hd_rand_det
      apply (rule_tac has_subprob_density_equal_on_space, simp)
      apply (intro nn_integral_dens_ctxt_measure_restrict)
      apply (simp_all add: t \<rho>)
      done
  qed
  with A show ?case by (subst has_parametrized_subprob_density_cong) (simp_all add: A)

next
  case (hd_rand V V' \<Gamma> \<delta> e f dst t)
  let ?t = "dist_param_type dst"
  from hd_rand.prems have t1: "\<Gamma> \<turnstile> e : ?t" and t2: "t = dist_result_type dst" by auto
  interpret density_context V V' \<Gamma> \<delta> by fact
  have dens[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
      (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure ?t) f"
    using hd_rand.prems by (intro hd_rand.IH) auto
  show ?case
  proof (unfold has_parametrized_subprob_density_def, intro ballI conjI impI)
    interpret sigma_finite_measure "stock_measure (dist_param_type dst)" by simp
    show "case_prod (apply_dist_to_dens dst f) \<in>
              borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      unfolding apply_dist_to_dens_def t2 by measurable

    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>"
    have meas_M: "measurable ?M = measurable (state_measure (V \<union> V') \<Gamma>)"
      by (intro ext measurable_cong_sets) (auto simp: dens_ctxt_measure_def state_measure'_def)
    from hd_rand have Me: "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<in> measurable ?M (subprob_algebra (stock_measure ?t))"
      by (subst meas_M, intro measurable_expr_sem[OF t1]) auto
    hence "?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Random dst e)) = (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) \<bind> dist_measure dst"
      (is "_ = ?N")
      by (subst expr_sem.simps, intro bind_assoc[OF Me, symmetric])
         (insert hd_rand, auto intro!: measurable_dist_measure)
    also have "space ?M \<noteq> {}"
      by (auto simp: dens_ctxt_measure_def state_measure'_def state_measure_def
                     space_PiM PiE_eq_empty_iff)
    with dens \<rho> Me have "has_subprob_density ?N (stock_measure t) (apply_dist_to_dens dst f \<rho>)"
      unfolding apply_dist_to_dens_def has_parametrized_subprob_density_def
      by (subst t2, intro bind_has_subprob_density')
         (auto simp: hd_rand.IH space_bind_measurable
               intro!: measurable_dist_dens dist_measure_has_subprob_density)
    finally show "has_subprob_density (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Random dst e))) (stock_measure t)
                      (apply_dist_to_dens dst f \<rho>)" .
  qed

next
  case (hd_fail V V' \<Gamma> \<delta> t t')
  interpret density_context V V' \<Gamma> \<delta> by fact
  have "has_parametrized_subprob_density (state_measure V' \<Gamma>)
            (\<lambda>_. null_measure (stock_measure t)) (stock_measure t') (\<lambda>_ _. 0)" (is "?P")
    using hd_fail by (auto simp: has_parametrized_subprob_density_def
                           intro!: null_measure_has_subprob_density)
  also have "?P \<longleftrightarrow> ?case"
    by (intro has_parametrized_subprob_density_cong)
       (auto simp: dens_ctxt_measure_bind_const subprob_space_null_measure_iff)
  finally show ?case .

next
  case (hd_pair x V y V' \<Gamma> \<delta> t)
  interpret density_context V V' \<Gamma> \<delta> by fact
  let ?R = "stock_measure t"
  from hd_pair.prems have t: "t = PRODUCT (\<Gamma> x) (\<Gamma> y)" by auto

  have meas: "(\<lambda>\<sigma>. <|\<sigma> x, \<sigma> y|>) \<in> measurable (state_measure (V\<union>V') \<Gamma>) ?R"
    using hd_pair unfolding t state_measure_def by simp

  have "has_parametrized_subprob_density (state_measure V' \<Gamma>)
            (\<lambda>\<rho>. distr (dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>) ?R (\<lambda>\<sigma>. <|\<sigma> x, \<sigma> y|>))
            (stock_measure t) (marg_dens2 \<Y> x y)"
  proof (rule has_parametrized_subprob_densityI)
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>"
    from hd_pair.hyps \<rho> show "distr ?M ?R (\<lambda>\<sigma>. <|\<sigma> x , \<sigma> y |>) = density ?R  (marg_dens2 \<Y> x y \<rho>)"
      by (subst (1 2) t, rule density_marg_dens2_eq[symmetric])
    from \<rho> interpret subprob_space ?M by (rule subprob_space_dens)
    show "subprob_space (distr (dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>) ?R (\<lambda>\<sigma>. <|\<sigma> x ,\<sigma> y|>))"
      by (rule subprob_space_distr)
         (simp_all add: meas measurable_dens_ctxt_measure_eq)
  qed (auto simp: t intro!: measurable_marg_dens2' hd_pair.hyps simp del: stock_measure.simps)
  also from hd_pair.hyps
    have "(\<lambda>\<rho>. distr (dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>) ?R (\<lambda>\<sigma>. <|\<sigma> x, \<sigma> y|>)) =
              (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. return_val <|\<sigma> x, \<sigma> y|>))"
    by (intro ext bind_return_val[symmetric]) (simp_all add: meas measurable_dens_ctxt_measure_eq)
  finally show ?case by (simp only: expr_sem_pair_vars)

next
  case (hd_if V V' \<Gamma> b f \<delta> e1 g1 e2 g2 t)
  interpret dc: density_context V V' \<Gamma> \<delta> by fact
  from hd_if.prems have tb: "\<Gamma> \<turnstile> b : BOOL" and t1: "\<Gamma> \<turnstile> e1 : t" and t2: "\<Gamma> \<turnstile> e2 : t" by auto

  have "has_parametrized_subprob_density (state_measure (V \<union> V') \<Gamma>)
          (\<lambda>\<rho>. dens_ctxt_measure ({},V\<union>V',\<Gamma>,\<lambda>a. 1) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> b)) (stock_measure BOOL) f"
    (is "?P") using hd_if.prems tb by (intro hd_if.IH(1)) auto
  also have "?P \<longleftrightarrow> has_parametrized_subprob_density (state_measure (V \<union> V') \<Gamma>)
                       (\<lambda>\<sigma>. expr_sem \<sigma> b) (stock_measure BOOL) f" (is "_ = ?P") using hd_if.prems
      by (intro has_parametrized_subprob_density_cong dens_ctxt_measure_empty_bind)
         (auto simp: dens_ctxt_measure_def state_measure'_def
               intro!: measurable_expr_sem[OF tb])
  finally have f: ?P .

  let ?M = "\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>"
  let ?M' = "\<lambda>b \<rho>. dens_ctxt_measure (V,V',\<Gamma>,if_dens \<delta> f b) \<rho>"

  from f have dc': "\<And>b. density_context V V' \<Gamma> (if_dens \<delta> f b)"
    by (intro dc.density_context_if_dens) (simp add: stock_measure.simps)
  have g1[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
              (\<lambda>\<rho>. ?M' True \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e1)) (stock_measure t) g1" using hd_if.prems
    by (intro hd_if.IH(2)[OF t1 dc']) simp
  have g2[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
              (\<lambda>\<rho>. ?M' False \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e2)) (stock_measure t) g2" using hd_if.prems
    by (intro hd_if.IH(3)[OF t2 dc']) simp

  show ?case
  proof (rule has_parametrized_subprob_densityI)
    show "(\<lambda>(\<rho>, x). g1 \<rho> x + g2 \<rho> x) \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      by measurable
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    show "subprob_space (?M \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (IF b THEN e1 ELSE e2)))"
      using \<rho> hd_if.prems
      by (intro subprob_space_bind[of _ _ "stock_measure t"], simp add: dc.subprob_space_dens)
         (auto intro!: measurable_expr_sem simp: measurable_dens_ctxt_measure_eq
               simp del: expr_sem.simps)
    show "?M \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (IF b THEN e1 ELSE e2)) =
              density (stock_measure t) (\<lambda>x. g1 \<rho> x + g2 \<rho> x)" using \<rho> hd_if.prems f g1 g2
    by (subst expr_sem.simps, intro dc.emeasure_bind_if_dens_ctxt_measure)
       (auto simp: measurable_dens_ctxt_measure_eq if_dens_def
             simp del: stock_measure.simps intro!: measurable_expr_sem)
  qed

next
  case (hd_if_det b V V' \<Gamma> \<delta> e1 g1 e2 g2 t)
  interpret dc: density_context V V' \<Gamma> \<delta> by fact
  from hd_if_det.prems \<open>randomfree b\<close>
  have tb[measurable (raw)]: "\<Gamma> \<turnstile> b : BOOL" and [measurable (raw)]: "randomfree b"
    and t1[measurable (raw)]: "\<Gamma> \<turnstile> e1 : t"
    and t2[measurable (raw)]: "\<Gamma> \<turnstile> e2 : t"
    and fv_b[measurable (raw)]: "free_vars b \<subseteq> V \<union> V'"
    and fv_e1[measurable (raw)]: "free_vars e1 \<subseteq> V \<union> V'"
    and fv_e2[measurable (raw)]: "free_vars e2 \<subseteq> V \<union> V'" by auto
  let ?M = "\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho>"
  let ?M' = "\<lambda>x \<rho>. dens_ctxt_measure (V,V',\<Gamma>,if_dens_det \<delta> b x) \<rho>"
  let ?N = "\<lambda>\<rho>. ?M \<rho>\<bind> (\<lambda>\<sigma>. if expr_sem_rf \<sigma> b = BoolVal True then expr_sem \<sigma> e1 else expr_sem \<sigma> e2)"

  from hd_if_det.hyps hd_if_det.prems tb
    have dc': "\<And>x. density_context V V' \<Gamma> (if_dens_det \<delta> b x)"
    by (intro dc.density_context_if_dens_det) simp_all
  have g1[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
              (\<lambda>\<rho>. ?M' True \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e1)) (stock_measure t) g1" using hd_if_det.prems
    by (intro hd_if_det.IH(1)[OF]) (simp_all add: dc' t1)
  have g2[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
              (\<lambda>\<rho>. ?M' False \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e2)) (stock_measure t) g2" using hd_if_det.prems
    by (intro hd_if_det.IH(2)[OF]) (simp_all add: dc' t2)

  note val_type_expr_sem_rf[OF tb, of "V \<union> V'", simp]

  have "has_parametrized_subprob_density (state_measure V' \<Gamma>) ?N
            (stock_measure t) (\<lambda>a b. g1 a b + g2 a b)" (is "?P")
  proof (rule has_parametrized_subprob_densityI)
    show "(\<lambda>(\<rho>, x). g1 \<rho> x + g2 \<rho> x) \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      by measurable
    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    show "subprob_space (?N \<rho>)"
      using \<rho> hd_if_det.prems hd_if_det.hyps t1 t2
      by (intro subprob_space_bind[of _ _ "stock_measure t"]) (auto simp add: dc.subprob_space_dens)
    show "?N \<rho> = density (stock_measure t) (\<lambda>x. g1 \<rho> x + g2 \<rho> x)"
      using \<rho> hd_if_det.prems g1 g2 dc' hd_if_det.prems unfolding if_dens_det_def
      by (intro dc.emeasure_bind_if_det_dens_ctxt_measure)
         (simp_all add: space_dens_ctxt_measure)
  qed
  also from hd_if_det.prems hd_if_det.hyps have "?P \<longleftrightarrow> ?case"
    apply (intro has_parametrized_subprob_density_cong bind_cong refl)
    apply (subst expr_sem.simps)
    apply (subst expr_sem_rf_sound[OF tb, of "V \<union> V'", symmetric]) []
    apply (simp_all add: space_dens_ctxt_measure bind_return_val''[where M="stock_measure t"])
    done
  finally show ?case .

next
  case (hd_fst V V' \<Gamma> \<delta> e f t)
  interpret density_context V V' \<Gamma> \<delta> by fact
  from hd_fst.prems obtain t' where t: "\<Gamma> \<turnstile> e : PRODUCT t t'"
    by (elim expr_typing_opE) (auto split: pdf_type.split_asm)
  hence "\<Gamma> \<turnstile> Snd $$ e : t'" by (intro expr_typing.intros) auto
  hence t2: "the (expr_type \<Gamma> (Snd $$ e)) = t'" by (simp add: expr_type_Some_iff[symmetric])
  let ?N = "stock_measure (PRODUCT t t')"
  have dens[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) ?N f"
    by (intro hd_fst.IH) (insert hd_fst.prems hd_fst.hyps t, auto)

  let ?f = "\<lambda>\<rho> x. \<integral>\<^sup>+ y. f \<rho> <|x,y|> \<partial>stock_measure t'"
  have "has_parametrized_subprob_density (state_measure V' \<Gamma>)
          (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Fst $$ e))) (stock_measure t) ?f"
   unfolding has_parametrized_subprob_density_def
  proof (intro conjI ballI impI)
    interpret sigma_finite_measure "stock_measure t'" by simp
    show "case_prod ?f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      by measurable

    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>"
    from dens and \<rho> have "has_subprob_density (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) ?N (f \<rho>)"
        unfolding has_parametrized_subprob_density_def by auto
    hence "has_subprob_density (distr (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) (op_sem Fst))
               (stock_measure t) (?f \<rho>)" (is "has_subprob_density ?R _ _")
      by (intro has_subprob_density_distr_Fst)  simp
    also from hd_fst.prems and \<rho> have "?R = ?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Fst $$ e))"
      by (intro expr_sem_op_eq_distr[symmetric]) simp_all
    finally show "has_subprob_density ... (stock_measure t) (?f \<rho>)" .
  qed
  thus ?case by (subst t2)

next
  case (hd_snd V V' \<Gamma> \<delta> e f t')
  interpret density_context V V' \<Gamma> \<delta> by fact
  from hd_snd.prems obtain t where t: "\<Gamma> \<turnstile> e : PRODUCT t t'"
    by (elim expr_typing_opE) (auto split: pdf_type.split_asm)
  hence "\<Gamma> \<turnstile> Fst $$ e : t" by (intro expr_typing.intros) auto
  hence t2: "the (expr_type \<Gamma> (Fst $$ e)) = t" by (simp add: expr_type_Some_iff[symmetric])
  let ?N = "stock_measure (PRODUCT t t')"
  have dens[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) ?N f"
    by (intro hd_snd.IH) (insert hd_snd.prems hd_snd.hyps t, auto)

  let ?f = "\<lambda>\<rho> y. \<integral>\<^sup>+ x. f \<rho> <|x,y|> \<partial>stock_measure t"
  have "has_parametrized_subprob_density (state_measure V' \<Gamma>)
          (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Snd $$ e))) (stock_measure t') ?f"
   unfolding has_parametrized_subprob_density_def
  proof (intro conjI ballI impI)
    interpret sigma_finite_measure "stock_measure t" by simp
    show "case_prod ?f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t')"
      by measurable

    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>"
    from dens and \<rho> have "has_subprob_density (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) ?N (f \<rho>)"
        unfolding has_parametrized_subprob_density_def by auto
    hence "has_subprob_density (distr (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t') (op_sem Snd))
               (stock_measure t') (?f \<rho>)" (is "has_subprob_density ?R _ _")
      by (intro has_subprob_density_distr_Snd)  simp
    also from hd_snd.prems and \<rho> have "?R = ?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (Snd $$ e))"
      by (intro expr_sem_op_eq_distr[symmetric]) simp_all
    finally show "has_subprob_density ... (stock_measure t') (?f \<rho>)" .
  qed
  thus ?case by (subst t2)

next
  case (hd_op_discr \<Gamma> oper e V V' \<delta> f t')
  interpret density_context V V' \<Gamma> \<delta> by fact
  from hd_op_discr.prems obtain t where t1: "\<Gamma> \<turnstile> e : t" and t2: "op_type oper t = Some t'" by auto
  have dens[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) f"
    by (intro hd_op_discr.IH) (insert hd_op_discr.prems hd_op_discr.hyps t1, auto)
  from hd_op_discr t1 have "expr_type \<Gamma> e = Some t" and "expr_type \<Gamma> (oper $$ e) = Some t'"
    by (simp_all add: expr_type_Some_iff[symmetric])
  hence t1': "the (expr_type \<Gamma> e) = t" and t2': "the (expr_type \<Gamma> (oper $$ e)) = t'" by auto
  with hd_op_discr have countable: "countable_type t'" by simp

  have A: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
              (\<lambda>\<rho>. distr (dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e))
                         (stock_measure t') (op_sem oper))
              (stock_measure t')
              (\<lambda>a b. \<integral>\<^sup>+x. (if op_sem oper x = b then 1 else 0) * f a x \<partial>stock_measure t)"
  proof (intro has_parametrized_subprob_densityI)
    let ?f = "\<lambda>\<rho> y. \<integral>\<^sup>+x. (if op_sem oper x = y then 1 else 0) * f \<rho> x \<partial>stock_measure t"
    note sigma_finite_measure.borel_measurable_nn_integral[OF sigma_finite_stock_measure, measurable]
    show "case_prod ?f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t')"
      using measurable_op_sem[OF t2] by measurable

    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>"
    let ?N = "?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)"

    from dens and \<rho> have dens': "has_subprob_density ?N (stock_measure t) (f \<rho>)"
        unfolding has_parametrized_subprob_density_def by auto
    from hd_op_discr.prems t1
      have M_e: "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<in>  measurable ?M (subprob_algebra (stock_measure t))"
      by (auto simp: measurable_dens_ctxt_measure_eq intro!: measurable_expr_sem)
    from M_e have meas_N: "measurable ?N = measurable (stock_measure t)"
      by (intro ext measurable_cong_sets) (simp_all add: sets_bind_measurable)
    from dens' and t2 show "subprob_space (distr ?N (stock_measure t') (op_sem oper))"
      by (intro subprob_space.subprob_space_distr)
         (auto dest: has_subprob_densityD intro!: measurable_op_sem simp: meas_N)

    from countable have count_space: "stock_measure t' = count_space (type_universe t')"
      by (rule countable_type_imp_count_space)
    from dens' have "?N = density (stock_measure t) (f \<rho>)" by (rule has_subprob_densityD)
    also {
      fix x assume "x \<in> type_universe t"
      with M_e have "val_type x = t" by (auto simp:)
      hence "val_type (op_sem oper x) = t'" by (intro op_sem_val_type) (simp add: t2)
    } note op_sem_type_universe = this
    from countable countable_type_countable measurable_op_sem[OF t2] dens'
    have "distr ... (stock_measure t') (op_sem oper) = density (stock_measure t') (?f \<rho>)"
      by (subst count_space, subst distr_density_discrete)
         (auto simp: meas_N count_space intro!: op_sem_type_universe dest: has_subprob_densityD)
    finally show "distr ?N (stock_measure t') (op_sem oper) =  density (stock_measure t') (?f \<rho>)" .
  qed
  from hd_op_discr.prems
    have B: "\<And>\<rho>. \<rho> \<in> space (state_measure V' \<Gamma>) \<Longrightarrow>
              distr (dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e))
                       (stock_measure t') (op_sem oper) =
                 dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> (oper $$ e))"
      by (intro expr_sem_op_eq_distr[symmetric]) simp_all
  show ?case by (simp only: has_parametrized_subprob_density_cong[OF B[symmetric]] t1' A)

next
  case (hd_neg V V' \<Gamma> \<delta> e f t')
  from hd_neg.prems obtain t where t1: "\<Gamma> \<turnstile> e : t" and t2: "op_type Minus t = Some t'" by auto
  have dens: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
              (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) f"
  by (intro hd_neg.IH) (insert hd_neg.prems hd_neg.hyps t1, auto)
  with hd_neg and t1 and t2 show ?case
  proof (intro expr_has_density_sound_op[where t = t])
    from t2 have [measurable]: "lift_RealIntVal uminus uminus \<in> measurable (stock_measure t') (stock_measure t)"
      by (simp split: pdf_type.split_asm)
    from dens have Mf[measurable]: "case_prod f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
        by (blast dest: has_parametrized_subprob_densityD)
    show "(\<lambda>(\<rho>, x). f \<rho> (op_sem Minus x))
              \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t')" by simp

    fix M \<rho> assume dens': "has_subprob_density M (stock_measure t) (f \<rho>)"
    hence space_M: "space M = space (stock_measure t)" by (auto dest: has_subprob_densityD)
    from t2 have t_disj: "(t = REAL \<and> t' = REAL) \<or> (t = INTEG \<and> t' = INTEG)"
      by (auto split: pdf_type.split_asm)
    thus "has_density (distr M (stock_measure t') (op_sem Minus))
                      (stock_measure t') (\<lambda>x. f \<rho> (op_sem Minus x))" (is "?thesis")
    proof (elim disjE conjE)
      assume A: "t = REAL" "t' = REAL"
      have "has_density (distr M (stock_measure t') (lift_RealVal uminus)) (stock_measure t')
                        ((\<lambda>x. f \<rho> (RealVal (-x))) \<circ> extract_real)" using dens'
        by (simp only: A, intro distr_lift_RealVal)
           (auto intro!: distr_uminus_real dest: has_subprob_density_imp_has_density)
      also have "distr M (stock_measure t') (lift_RealVal uminus) =
                     distr M (stock_measure t') (lift_RealIntVal uminus uminus)" using dens'
        by (intro distr_cong) (auto intro!: lift_RealIntVal_Real[symmetric] simp: space_M A)
      also have "has_density ... (stock_measure t') ((\<lambda>x. f \<rho> (RealVal (-x))) \<circ> extract_real) \<longleftrightarrow>
                   has_density ... (stock_measure t') (\<lambda>x. f \<rho> (lift_RealIntVal uminus uminus x))"
        by (intro has_density_cong)
           (auto simp: lift_RealIntVal_def extract_real_def A space_embed_measure split: val.split)
      finally show ?thesis by simp
    next
      assume A: "t = INTEG" "t' = INTEG"
      have "has_density (distr M (stock_measure t') (lift_IntVal uminus)) (stock_measure t')
                        ((\<lambda>x. f \<rho> (IntVal (-x))) \<circ> extract_int)" using dens'
        by (simp only: A, intro distr_lift_IntVal)
           (auto intro!: distr_uminus_ring_count_space simp: has_subprob_density_def)
      also have "distr M (stock_measure t') (lift_IntVal uminus) =
                     distr M (stock_measure t') (lift_RealIntVal uminus uminus)" using dens'
        by (intro distr_cong) (auto intro!: lift_RealIntVal_Int[symmetric] simp: space_M A)
      also have "has_density ... (stock_measure t') ((\<lambda>x. f \<rho> (IntVal (-x))) \<circ> extract_int) \<longleftrightarrow>
                   has_density ... (stock_measure t') (\<lambda>x. f \<rho> (lift_RealIntVal uminus uminus x))"
        by (intro has_density_cong)
           (auto simp: lift_RealIntVal_def extract_int_def A space_embed_measure split: val.split)
      finally show ?thesis by simp
    qed
  qed auto

next
  case (hd_exp V V' \<Gamma> \<delta> e f t')
  from hd_exp.prems have t1: "\<Gamma> \<turnstile> e : REAL" and t2: "t' = REAL"
    by (auto split: pdf_type.split_asm)
  have dens[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
              (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure REAL) f"
    by (intro hd_exp.IH) (insert hd_exp.prems hd_exp.hyps t1, auto)
  with hd_exp and t1 and t2 show ?case
  proof (intro expr_has_density_sound_op[where t = REAL])
    from t2 have [measurable]: "lift_RealVal safe_ln \<in> measurable (stock_measure REAL) (stock_measure REAL)"
      by (simp split: pdf_type.split_asm)
    from dens have Mf[measurable]: "case_prod f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure REAL)"
        by (blast dest: has_parametrized_subprob_densityD)
    let ?f = "\<lambda>\<rho> x. if extract_real x > 0 then
                         f \<rho> (lift_RealVal safe_ln x) * inverse (extract_real x) else 0"
    show "case_prod ?f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t')"
      unfolding t2 by measurable
    fix M \<rho> assume dens': "has_subprob_density M (stock_measure REAL) (f \<rho>)"
    hence space_M: "space M = space (stock_measure REAL)" by (auto dest: has_subprob_densityD)
    have "has_density (distr M (stock_measure t') (lift_RealVal exp)) (stock_measure t')
            ((\<lambda>x. if 0 < x then f \<rho> (RealVal (ln x)) * ennreal (inverse x) else 0)
               \<circ> extract_real)" (is "has_density _ _ ?f'") using dens'
      apply (simp only: t2)
      apply (rule distr_lift_RealVal[where g = "\<lambda>f x. if x > 0 then f (ln x) * ennreal (inverse x) else 0"])
      apply (auto intro!: subprob_density_distr_real_exp intro: has_subprob_density_imp_has_density)
      done
    also have "?f' = ?f \<rho>"
      by (intro ext) (simp add: o_def lift_RealVal_def extract_real_def split: val.split)
    finally show "has_density (distr M (stock_measure t') (op_sem Exp)) (stock_measure t') ..."
      by simp
  qed auto

next
  case (hd_inv V V' \<Gamma> \<delta> e f t')
  from hd_inv.prems have t1: "\<Gamma> \<turnstile> e : REAL" and t2: "t' = REAL"
    by (auto split: pdf_type.split_asm)
  have dens: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
              (\<lambda>\<rho>. dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure REAL) f"
    by (intro hd_inv.IH) (insert hd_inv.prems hd_inv.hyps t1, auto)
  with hd_inv and t1 and t2 show ?case
  proof (intro expr_has_density_sound_op[where t = REAL])
    from t2 have [measurable]: "lift_RealVal inverse \<in> measurable (stock_measure REAL) (stock_measure REAL)"
      by (simp split: pdf_type.split_asm)
    from dens have Mf[measurable]: "case_prod f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure REAL)"
        by (blast dest: has_parametrized_subprob_densityD)
    let ?f = "\<lambda>\<rho> x. f \<rho> (op_sem Inverse x) * inverse (extract_real x) ^ 2"
    have [measurable]: "extract_real \<in> borel_measurable (stock_measure REAL)" by simp
    show "case_prod ?f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t')" by (simp add: t2)
    fix M \<rho> assume dens': "has_subprob_density M (stock_measure REAL) (f \<rho>)"
    hence space_M: "space M = space (stock_measure REAL)" by (auto dest: has_subprob_densityD)
    have "has_density (distr M (stock_measure t') (lift_RealVal inverse)) (stock_measure t')
            ((\<lambda>x. f \<rho> (RealVal (inverse x)) * ennreal (inverse (x * x)))
               \<circ> extract_real)" (is "has_density _ _ ?f'") using dens'
      apply (simp only: t2)
      apply (rule distr_lift_RealVal)
      apply (auto intro!: subprob_density_distr_real_inverse intro: has_subprob_density_imp_has_density
             simp del: inverse_mult_distrib)
      done
    also have "?f' = ?f \<rho>"
      by (intro ext) (simp add: o_def lift_RealVal_def extract_real_def power2_eq_square split: val.split)
    finally show "has_density (distr M (stock_measure t') (op_sem Inverse)) (stock_measure t') ..."
      by simp
  qed auto

next

  case (hd_addc V V' \<Gamma> \<delta> e f e' t)
  interpret density_context V V' \<Gamma> \<delta> by fact
  from hd_addc.prems have t1: "\<Gamma> \<turnstile> e : t" and t2: "\<Gamma> \<turnstile> e' : t" and t_disj: "t = REAL \<or> t = INTEG"
    by (elim expr_typing_opE, (auto split: pdf_type.split_asm)[])+
  hence t4: "op_type Add (PRODUCT t t) = Some t" by auto
  have dens: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                  (\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) f"
    by (rule hd_addc.IH) (insert hd_addc.prems t1, auto)
  show ?case (is "has_parametrized_subprob_density _ ?N _ ?f")
  proof (unfold has_parametrized_subprob_density_def has_subprob_density_def, intro conjI ballI)
    from t2 t_disj hd_addc.prems hd_addc.hyps
      show "case_prod ?f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      by (intro addc_density_measurable has_parametrized_subprob_densityD[OF dens]) auto

    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>"
    let ?v1 = "extract_int (expr_sem_rf \<rho> e')" and ?v2 = "extract_real (expr_sem_rf \<rho> e')"
    from dens and \<rho> have dens': "has_subprob_density (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) (f \<rho>)"
      unfolding has_parametrized_subprob_density_def has_subprob_density_def by auto

    have Me: "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<in>
                   measurable (state_measure (V \<union> V') \<Gamma>) (subprob_algebra (stock_measure t))"
      using t1 hd_addc.prems by (intro measurable_expr_sem) simp_all
    from hd_addc.prems hd_addc.hyps \<rho> have vt_e': "val_type (expr_sem_rf \<rho> e') = t"
      by (intro val_type_expr_sem_rf[OF t2]) auto
    have space_e: "space (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) = type_universe t"
      by (subst space_bind_measurable, subst measurable_dens_ctxt_measure_eq)
         (rule Me, simp, simp add:)
    from hd_addc.prems show "subprob_space (?N \<rho>)"
      by (intro subprob_space_bind subprob_space_dens[OF \<rho>],
          subst measurable_dens_ctxt_measure_eq)
         (rule measurable_expr_sem, auto)

    let ?N' = "distr (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t)
                          (lift_RealIntVal ((+) ?v1) ((+) ?v2))"
    have "has_density ?N' (stock_measure t) (?f \<rho>)" using t_disj
    proof (elim disjE)
      assume t: "t = REAL"
      let ?N'' = "distr (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) (lift_RealVal ((+) ?v2))"
      let ?f' = "(\<lambda>x. f \<rho> (RealVal (x - ?v2))) \<circ> extract_real"
      from dens' have "has_density ?N'' (stock_measure t) ?f'"
        by (subst (1 2) t, intro distr_lift_RealVal)
           (auto simp: t intro!: distr_plus_real dest: has_subprob_density_imp_has_density)
      also have "?N'' = ?N'"
        by (intro distr_cong)
           (auto simp: lift_RealVal_def lift_RealIntVal_def extract_real_def vt_e' space_e t
                 dest: split: val.split)
      also have "has_density ?N' (stock_measure t) ?f' = has_density ?N' (stock_measure t) (?f \<rho>)"
        using vt_e' by (intro has_density_cong)
                        (auto simp: lift_RealIntVal_def t extract_real_def space_embed_measure
                          lift_RealIntVal2_def split: val.split)
      finally show "has_density ?N' (stock_measure t) (?f \<rho>)" .
    next
      assume t: "t = INTEG"
      let ?N'' = "distr (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) (lift_IntVal ((+) ?v1))"
      let ?f' = "(\<lambda>x. f \<rho> (IntVal (x - ?v1))) \<circ> extract_int"
      from dens' have "has_density ?N'' (stock_measure t) ?f'"
        by (subst (1 2) t, intro distr_lift_IntVal)
           (auto simp: t intro!: distr_plus_ring_count_space dest: has_subprob_density_imp_has_density)
      also have "?N'' = ?N'"
        by (intro distr_cong)
           (auto simp: lift_IntVal_def lift_RealIntVal_def extract_real_def vt_e' space_e t
                 split: val.split)
      also have "has_density ?N' (stock_measure t) ?f' = has_density ?N' (stock_measure t) (?f \<rho>)"
        using vt_e' by (intro has_density_cong)
                        (auto simp: lift_RealIntVal_def t extract_int_def space_embed_measure
                          lift_RealIntVal2_def split: val.split)
      finally show "has_density ?N' (stock_measure t) (?f \<rho>)" .
    qed
    also have "?N' = distr (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t)
                          (\<lambda>w. op_sem Add <|w, expr_sem_rf \<rho> e'|>)" using t_disj vt_e'
      by (intro distr_cong, simp, simp)
         (auto split: val.split simp: lift_RealIntVal_def
            lift_RealIntVal2_def space_e extract_real_def extract_int_def)
    also have "... = ?N \<rho>"
        using hd_addc.prems hd_addc.hyps t_disj \<rho>
        by (intro bin_op_randomfree_restructure[OF t1 t2, symmetric]) auto
    finally show "has_density (?N \<rho>) (stock_measure t) (?f \<rho>)" .
  qed

next

  case (hd_multc V V' \<Gamma> \<delta> e f c t)
  interpret density_context V V' \<Gamma> \<delta> by fact
  from hd_multc.prems hd_multc.hyps
    have t1: "\<Gamma> \<turnstile> e : REAL" and t2: "val_type c = REAL" and t: "t = REAL"
      by (elim expr_typing_opE expr_typing_valE expr_typing_pairE,
          (auto split: pdf_type.split_asm) [])+
  have t4: "op_type Mult (PRODUCT REAL REAL) = Some REAL" by simp
  have dens[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                  (\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) f"
    by (rule hd_multc.IH) (insert hd_multc.prems t1 t, auto)
  show ?case (is "has_parametrized_subprob_density _ ?N _ ?f")
  proof (unfold has_parametrized_subprob_density_def has_subprob_density_def, intro conjI ballI)
    let ?MR = "stock_measure t" and ?MP = "stock_measure (PRODUCT t t)"
    have M_mult[measurable]: "(op_sem Mult) \<in> measurable ?MP ?MR" by (simp add: measurable_op_sem t)
    show "case_prod ?f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      by measurable (insert t2, auto simp: t val_type_eq_REAL lift_RealVal_def)

    fix \<rho> assume \<rho>: "\<rho> \<in> space (state_measure V' \<Gamma>)"
    let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>"
    from dens and \<rho> have dens': "has_subprob_density (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) (f \<rho>)"
      unfolding has_parametrized_subprob_density_def has_subprob_density_def by auto

    have Me: "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<in>
                   measurable (state_measure (V \<union> V') \<Gamma>) (subprob_algebra (stock_measure REAL))"
      using t1 hd_multc.prems by (intro measurable_expr_sem) simp_all
    have space_e: "space (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) = range RealVal"
      by (subst space_bind_measurable, subst measurable_dens_ctxt_measure_eq)
         (rule Me, simp, simp add: t space_embed_measure type_universe_REAL)
    from hd_multc.prems show "subprob_space (?N \<rho>)"
      by (intro subprob_space_bind subprob_space_dens[OF \<rho>],
          subst measurable_dens_ctxt_measure_eq)
         (rule measurable_expr_sem, auto)

    let ?N' = "distr (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t)
                          (lift_RealVal ((*) (extract_real c)))"
    let ?g = "\<lambda>f x. f (x / extract_real c) * ennreal (inverse (abs (extract_real c)))"
    let ?f' = "(\<lambda>x. f \<rho> (RealVal (x / extract_real c)) *
                    inverse (abs (extract_real c))) \<circ> extract_real"
    from hd_multc.hyps have "extract_real c \<noteq> 0"
      by (auto simp: extract_real_def split: val.split)
    with dens' have "has_density ?N' (stock_measure REAL) ?f'"
      by (subst t, intro distr_lift_RealVal[where g = ?g])
         (auto simp: t intro!: distr_mult_real dest: has_subprob_density_imp_has_density)
    also have "has_density ?N' (stock_measure REAL) ?f' =
                    has_density ?N' (stock_measure REAL) (?f \<rho>)"
       using hd_multc.hyps
       by (intro has_density_cong)
          (auto simp: lift_RealVal_def t extract_real_def space_embed_measure
                      lift_RealIntVal2_def field_simps split: val.split)
      finally have "has_density ?N' (stock_measure REAL) (?f \<rho>)" .
    also have "?N' = distr (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t)
                          (\<lambda>w. op_sem Mult <|w, expr_sem_rf \<rho> (Val c)|>)" using hd_multc.hyps
      by (intro distr_cong, simp, simp)
         (auto simp: lift_RealVal_def lift_RealIntVal2_def space_e extract_real_def
               split: val.split)
    also have "... = ?N \<rho>"
        using hd_multc.prems hd_multc.hyps \<rho>
        by (intro bin_op_randomfree_restructure[OF t1, symmetric])
           (auto simp: t intro!: expr_typing.intros)
    finally show "has_density (?N \<rho>) (stock_measure t) (?f \<rho>)" by (simp only: t)
  qed

next

  case (hd_add V V' \<Gamma> \<delta> e f t)
  interpret density_context V V' \<Gamma> \<delta> by fact
  from hd_add.prems hd_add.hyps
    have t1: "\<Gamma> \<turnstile> e : PRODUCT t t" and t2: "op_type Add (PRODUCT t t) = Some t" and
          t_disj: "t = REAL \<or> t = INTEG"
      by (elim expr_typing_opE expr_typing_valE expr_typing_pairE,
          (auto split: pdf_type.split_asm) [])+
  let ?tp = "PRODUCT t t"
  have dens[measurable]: "has_parametrized_subprob_density (state_measure V' \<Gamma>)
                  (\<lambda>\<rho>. dens_ctxt_measure (V,V',\<Gamma>,\<delta>) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure ?tp) f"
    by (rule hd_add.IH) (insert hd_add.prems t1 t2 t_disj, auto)
  from hd_add.prems hd_add.hyps t1 t2 t_disj show ?case (is "has_parametrized_subprob_density _ ?N _ ?f")
  proof (intro expr_has_density_sound_op[OF _ dens])
    note sigma_finite_measure.borel_measurable_nn_integral[OF sigma_finite_stock_measure, measurable]
    have [measurable]: "op_type Minus t = Some t"
      using t_disj by auto
    note measurable_op_sem[measurable] t2[measurable]
    let ?f' = "\<lambda>\<rho> z. \<integral>\<^sup>+ x. f \<rho>  <|x , op_sem Add <|z, op_sem Minus x|>|> \<partial>stock_measure t"
    have "case_prod ?f' \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      by measurable
    also have "case_prod ?f' \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t) \<longleftrightarrow>
                    case_prod ?f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
      by (intro measurable_cong) (auto simp: space_pair_measure)
    finally show "case_prod ?f \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)" .

    fix M \<rho> assume dens': "has_subprob_density M (stock_measure (PRODUCT t t)) (f \<rho>)"
    hence Mf[measurable]: "f \<rho> \<in> borel_measurable (stock_measure (PRODUCT t t))" by (rule has_subprob_densityD)
    let ?M = "dens_ctxt_measure (V, V', \<Gamma>, \<delta>) \<rho>"
    show "has_density (distr M (stock_measure t) (op_sem Add)) (stock_measure t) (?f \<rho>)"
    proof (insert t_disj, elim disjE)
      assume t: "t = REAL"
      let ?f'' = "(\<lambda>z. \<integral>\<^sup>+x. f \<rho> (RealPairVal (x, z - x)) \<partial>lborel) \<circ> extract_real"
      have "has_density (distr M (stock_measure t) (op_sem Add)) (stock_measure t) ?f''"
        using dens'
        by (simp only: t op_sem.simps, intro distr_lift_RealPairVal)
            (simp_all add: borel_prod[symmetric] has_subprob_density_imp_has_density
                           distr_convolution_real)
      also have "?f'' = (\<lambda>z. \<integral>\<^sup>+ x. f \<rho> (RealPairVal (x, extract_real z - x)) \<partial>lborel)"
        (is "_ = ?f''")
        by (auto simp add: t space_embed_measure extract_real_def)
      also have "\<And>z. val_type z = REAL \<Longrightarrow>
          (\<lambda>x. f \<rho>  <|x, op_sem Add <|z, op_sem Minus x|>|>) \<in> borel_measurable (stock_measure REAL)"
        by (rule Mf[THEN measurable_compose_rev]) (simp add: t)
      hence "has_density (distr M (stock_measure t) (op_sem Add)) (stock_measure t) ?f'' \<longleftrightarrow>
              has_density (distr M (stock_measure t) (op_sem Add)) (stock_measure t) (?f \<rho>)"
        by (intro has_density_cong, simp add: t space_embed_measure del: op_sem.simps)
           (auto simp add: nn_integral_RealVal RealPairVal_def lift_RealIntVal2_def lift_RealIntVal_def val_type_eq_REAL)
      finally show "..." .
    next
      assume t: "t = INTEG"
      let ?f'' = "(\<lambda>z. \<integral>\<^sup>+x. f \<rho> (IntPairVal (x, z - x)) \<partial>count_space UNIV) \<circ> extract_int"
      have "has_density (distr M (stock_measure t) (op_sem Add)) (stock_measure t) ?f''"
        using dens'
        by (simp only: t op_sem.simps, intro distr_lift_IntPairVal)
            (simp_all add: has_subprob_density_imp_has_density
                           distr_convolution_ring_count_space)
      also have "?f'' = (\<lambda>z. \<integral>\<^sup>+ x. f \<rho> (IntPairVal (x, extract_int z - x)) \<partial>count_space UNIV)"
        (is "_ = ?f''")
        by (auto simp add: t space_embed_measure extract_int_def)
      also have "has_density (distr M (stock_measure t) (op_sem Add)) (stock_measure t) ?f'' \<longleftrightarrow>
              has_density (distr M (stock_measure t) (op_sem Add)) (stock_measure t) (?f \<rho>)"
        by (intro has_density_cong, simp add: t space_embed_measure del: op_sem.simps)
            (auto simp:  nn_integral_IntVal IntPairVal_def val_type_eq_INTEG
                          lift_RealIntVal2_def lift_RealIntVal_def)
      finally show "..." .
    qed
  qed
qed

lemma hd_cong:
  assumes "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f" "density_context V V' \<Gamma> \<delta>" "\<Gamma> \<turnstile> e : t" "free_vars e \<subseteq> V \<union> V'"
  assumes "\<And>\<rho> x. \<rho> \<in> space (state_measure V' \<Gamma>) \<Longrightarrow> x \<in> space (stock_measure t) \<Longrightarrow> f \<rho> x = f' \<rho> x"
  shows "(V,V',\<Gamma>,\<delta>) \<turnstile>\<^sub>d e \<Rightarrow> f'"
proof (rule hd_AE[OF assms(1,3) AE_I2[OF assms(5)]])
  note dens = expr_has_density_sound_aux[OF assms(1,3,2,4)]
  note dens' = has_parametrized_subprob_densityD[OF this]
  show "(\<lambda>(\<rho>, x). f' \<rho> x) \<in> borel_measurable (state_measure V' \<Gamma> \<Otimes>\<^sub>M stock_measure t)"
    using assms(5) dens'(3)
    by (subst measurable_cong[of _ _ "case_prod f"]) (auto simp: space_pair_measure)
qed auto

lemma prob_space_empty_dens_ctxt[simp]:
  "prob_space (dens_ctxt_measure ({},{},\<Gamma>,(\<lambda>_. 1)) (\<lambda>_. undefined))"
    unfolding density_context_def
    by (auto simp: dens_ctxt_measure_def state_measure'_def state_measure_def
                   emeasure_distr emeasure_density PiM_empty intro!: prob_spaceI)

lemma branch_prob_empty_ctxt[simp]: "branch_prob ({},{},\<Gamma>,(\<lambda>_. 1)) (\<lambda>_. undefined) = 1"
  unfolding branch_prob_def by (subst prob_space.emeasure_space_1) simp_all


lemma expr_has_density_sound:
  assumes "({},{},\<Gamma>,(\<lambda>_. 1)) \<turnstile>\<^sub>d e \<Rightarrow> f" "\<Gamma> \<turnstile> e : t" "free_vars e = {}"
  shows "has_subprob_density (expr_sem \<sigma> e) (stock_measure t) (f (\<lambda>_. undefined))"
proof-
  let ?M = "dens_ctxt_measure ({},{},\<Gamma>,\<lambda>_. 1) (\<lambda>_. undefined)"
  have "density_context {} {} \<Gamma> (\<lambda>_. 1)"
    unfolding density_context_def
    by (auto simp: dens_ctxt_measure_def state_measure'_def state_measure_def
                   emeasure_distr emeasure_density PiM_empty intro!: subprob_spaceI)
  from expr_has_density_sound_aux[OF assms(1,2) this] assms(3)
    have "has_parametrized_subprob_density (state_measure {} \<Gamma>)
              (\<lambda>\<rho>. dens_ctxt_measure ({},{},\<Gamma>,\<lambda>_. 1) \<rho> \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e)) (stock_measure t) f"
    by blast
  also have "state_measure {} \<Gamma> = count_space {\<lambda>_. undefined}"
    by (rule measure_eqI) (simp_all add: state_measure_def PiM_empty emeasure_density)
  finally have "has_subprob_density (?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e))
                                 (stock_measure t) (f (\<lambda>_. undefined))"
    unfolding has_parametrized_subprob_density_def by simp
  also from assms have "(\<lambda>\<sigma>. expr_sem \<sigma> e) \<in> measurable (state_measure {} \<Gamma>)
                                                        (subprob_algebra (stock_measure t))"
    by (intro measurable_expr_sem) auto
  hence "?M \<bind> (\<lambda>\<sigma>. expr_sem \<sigma> e) = expr_sem (\<lambda>_. undefined) e"
    by (intro dens_ctxt_measure_empty_bind) (auto simp: state_measure_def PiM_empty)
  also from assms have "... = expr_sem \<sigma> e" by (intro expr_sem_eq_on_vars) auto
  finally show ?thesis .
qed

end
