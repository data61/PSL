(* Author: Johannes Hölzl <hoelzl@in.tum.de> *)

section \<open>Markov Decision Processes\<close>

theory Markov_Decision_Process
  imports Discrete_Time_Markov_Chain
begin

definition "some_elem s = (SOME x. x \<in> s)"

lemma some_elem_ne: "s \<noteq> {} \<Longrightarrow> some_elem s \<in> s"
  unfolding some_elem_def by (auto intro: someI)

subsection \<open>Configurations\<close>

text \<open>

We want to construct a \emph{non-free} codatatype
  \<open>'s cfg = Cfg (state: 's) (action: 's pmf) (cont: 's \<Rightarrow> 's cfg)\<close>.
with the restriction
  @{term "state (cont cfg s) = s"}

\<close>

hide_const cont

codatatype 's scheduler = Scheduler (action_sch: "'s pmf") (cont_sch: "'s \<Rightarrow> 's scheduler")

lemma equivp_rel_prod: "equivp R \<Longrightarrow> equivp Q \<Longrightarrow> equivp (rel_prod R Q)"
  by (auto intro!: equivpI prod.rel_symp prod.rel_transp prod.rel_reflp elim: equivpE)

coinductive eq_scheduler :: "'s scheduler \<Rightarrow> 's scheduler \<Rightarrow> bool"
where
  "\<And>D. action_sch sc1 = D \<Longrightarrow> action_sch sc2 = D \<Longrightarrow>
    (\<forall>s\<in>D. eq_scheduler (cont_sch sc1 s) (cont_sch sc2 s)) \<Longrightarrow> eq_scheduler sc1 sc2"

lemma eq_scheduler_refl[intro]: "eq_scheduler sc sc"
  by (coinduction arbitrary: sc) auto

quotient_type 's cfg = "'s \<times> 's scheduler" / "rel_prod (=) eq_scheduler"
proof (intro equivp_rel_prod equivpI reflpI sympI transpI)
  show "eq_scheduler sc1 sc2 \<Longrightarrow> eq_scheduler sc2 sc1" for sc1 sc2 :: "'s scheduler"
    by (coinduction arbitrary: sc1 sc2) (auto elim: eq_scheduler.cases)
  show "eq_scheduler sc1 sc2 \<Longrightarrow> eq_scheduler sc2 sc3 \<Longrightarrow> eq_scheduler sc1 sc3"
    for sc1 sc2 sc3 :: "'s scheduler"
    by (coinduction arbitrary: sc1 sc2 sc3)
       (subst (asm) (1 2) eq_scheduler.simps, auto)
qed auto

lift_definition state :: "'s cfg \<Rightarrow> 's" is "fst"
  by auto

lift_definition action :: "'s cfg \<Rightarrow> 's pmf" is "\<lambda>(s, sc). action_sch sc"
  by (force elim: eq_scheduler.cases)

lift_definition cont :: "'s cfg \<Rightarrow> 's \<Rightarrow> 's cfg" is
  "\<lambda>(s, sc) t. if t \<in> action_sch sc then (t, cont_sch sc t) else
    (t, cont_sch sc (some_elem (action_sch sc)))"
  apply (simp add: rel_prod_conv split: prod.splits)
  apply (subst (asm) eq_scheduler.simps)
  apply (auto simp: Let_def set_pmf_not_empty[THEN some_elem_ne])
  done

lift_definition Cfg :: "'s \<Rightarrow> 's pmf \<Rightarrow> ('s \<Rightarrow> 's cfg) \<Rightarrow> 's cfg" is
  "\<lambda>s D c. (s, Scheduler D (\<lambda>t. snd (c t)))"
  by (auto simp: rel_prod_conv split_beta' eq_scheduler.simps[of "Scheduler _  _"])

lift_definition cfg_corec :: "'s \<Rightarrow> ('a \<Rightarrow> 's pmf) \<Rightarrow> ('a \<Rightarrow> 's \<Rightarrow> 'a)  \<Rightarrow> 'a \<Rightarrow> 's cfg" is
  "\<lambda>s D C x. (s, corec_scheduler D (\<lambda>x s. Inr (C x s)) x)"  .

lemma state_cont[simp]: "state (cont cfg s) = s"
  by transfer (simp split: prod.split)

lemma state_Cfg[simp]: "state (Cfg s d' c') = s"
  by transfer simp

lemma action_Cfg[simp]: "action (Cfg s d' c') = d'"
  by transfer simp

lemma cont_Cfg[simp]: "t \<in> set_pmf d' \<Longrightarrow> state (c' t) = t \<Longrightarrow> cont (Cfg s d' c') t = c' t"
  by transfer (auto simp add: rel_prod_conv split: prod.split)

lemma state_cfg_corec[simp]: "state (cfg_corec s d c x) = s"
  by transfer auto

lemma action_cfg_corec[simp]: "action (cfg_corec s d c x) = d x"
  by transfer auto

lemma cont_cfg_corec[simp]: "t \<in> set_pmf (d x) \<Longrightarrow> cont (cfg_corec s d c x) t = cfg_corec t d c (c x t)"
  by transfer auto

lemma cfg_coinduct[consumes 1, case_names state action cont, coinduct pred]:
  "X c d \<Longrightarrow> (\<And>c d. X c d \<Longrightarrow> state c = state d) \<Longrightarrow> (\<And>c d. X c d \<Longrightarrow> action c = action d) \<Longrightarrow>
    (\<And>c d t. X c d \<Longrightarrow> t \<in> set_pmf (action c) \<Longrightarrow> X (cont c t) (cont d t)) \<Longrightarrow> c = d"
proof (transfer, clarsimp)
  fix X :: "('a \<times> 'a scheduler) \<Rightarrow> ('a \<times> 'a scheduler) \<Rightarrow> bool" and B s1 s2 sc1 sc2
  assume X: "X (s1, sc1) (s2, sc2)" and "rel_fun cr_cfg (rel_fun cr_cfg (=)) X B"
    and 1: "\<And>s1 sc1 s2 sc2. X (s1, sc1) (s2, sc2) \<Longrightarrow> s1 = s2"
    and 2: "\<And>s1 sc1 s2 sc2. X (s1, sc1) (s2, sc2) \<Longrightarrow> action_sch sc1 = action_sch sc2"
    and 3: "\<And>s1 sc1 s2 sc2 t. X (s1, sc1) (s2, sc2) \<Longrightarrow> t \<in> set_pmf (action_sch sc2) \<Longrightarrow>
      X (t, cont_sch sc1 t) (t, cont_sch sc2 t)"
  from X show "eq_scheduler sc1 sc2"
    by (coinduction arbitrary: s1 s2 sc1 sc2)
       (blast dest: 2 3)
qed

coinductive rel_cfg :: "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> 'a cfg \<Rightarrow> 'b cfg \<Rightarrow> bool" for P :: "'a \<Rightarrow> 'b \<Rightarrow> bool"
where
  "P (state cfg1) (state cfg2) \<Longrightarrow>
    rel_pmf (\<lambda>s t. rel_cfg P (cont cfg1 s) (cont cfg2 t)) (action cfg1) (action cfg2) \<Longrightarrow>
    rel_cfg P cfg1 cfg2"

lemma rel_cfg_state: "rel_cfg P cfg1 cfg2 \<Longrightarrow> P (state cfg1) (state cfg2)"
  by (auto elim: rel_cfg.cases)

lemma rel_cfg_cont:
  "rel_cfg P cfg1 cfg2 \<Longrightarrow>
    rel_pmf (\<lambda>s t. rel_cfg P (cont cfg1 s) (cont cfg2 t)) (action cfg1) (action cfg2)"
  by (auto elim: rel_cfg.cases)

lemma rel_cfg_action:
  assumes P: "rel_cfg P cfg1 cfg2" shows "rel_pmf P (action cfg1) (action cfg2)"
proof (rule pmf.rel_mono_strong)
  show "rel_pmf (\<lambda>s t. rel_cfg P (cont cfg1 s) (cont cfg2 t)) (action cfg1) (action cfg2)"
    using P by (rule rel_cfg_cont)
qed (auto dest: rel_cfg_state)

lemma rel_cfg_eq: "rel_cfg (=) cfg1 cfg2 \<longleftrightarrow> cfg1 = cfg2"
proof safe
  show "rel_cfg (=) cfg1 cfg2 \<Longrightarrow> cfg1 = cfg2"
  proof (coinduction arbitrary: cfg1 cfg2)
    case cont
    have "action cfg1 = action cfg2"
      using \<open>rel_cfg (=) cfg1 cfg2\<close> by (auto dest: rel_cfg_action simp: pmf.rel_eq)
    then have "rel_pmf (\<lambda>s t. rel_cfg (=) (cont cfg1 s) (cont cfg2 t)) (action cfg1) (action cfg1)"
      using cont by (auto dest: rel_cfg_cont)
    then have "rel_pmf (\<lambda>s t. rel_cfg (=) (cont cfg1 s) (cont cfg2 t) \<and> s = t) (action cfg1) (action cfg1)"
      by (rule pmf.rel_mono_strong) (auto dest: rel_cfg_state)
    then have "pred_pmf (\<lambda>s. rel_cfg (=) (cont cfg1 s) (cont cfg2 s)) (action cfg1)"
      unfolding pmf.pred_rel by (rule pmf.rel_mono_strong) (auto simp: eq_onp_def)
    with \<open>t \<in> action cfg1\<close> show ?case
      by (auto simp: pmf.pred_set)
  qed (auto dest: rel_cfg_state rel_cfg_action simp: pmf.rel_eq)
  show "rel_cfg (=) cfg2 cfg2"
    by (coinduction arbitrary: cfg2) (auto intro!: rel_pmf_reflI)
qed

subsection \<open>Configuration with Memoryless Scheduler\<close>

definition "memoryless_on f s = cfg_corec s f (\<lambda>_ t. t) s"

lemma
  shows state_memoryless_on[simp]: "state (memoryless_on f s) = s"
    and action_memoryless_on[simp]: "action (memoryless_on f s) = f s"
    and cont_memoryless_on[simp]: "t \<in> (f s) \<Longrightarrow> cont (memoryless_on f s) t = memoryless_on f t"
  by (simp_all add: memoryless_on_def)

definition K_cfg :: "'s cfg \<Rightarrow> 's cfg pmf" where
  "K_cfg cfg = map_pmf (cont cfg) (action cfg)"

lemma set_K_cfg: "set_pmf (K_cfg cfg) = cont cfg ` set_pmf (action cfg)"
  by (simp add: K_cfg_def)

lemma nn_integral_K_cfg: "(\<integral>\<^sup>+cfg. f cfg \<partial>K_cfg cfg) = (\<integral>\<^sup>+s. f (cont cfg s) \<partial>action cfg)"
  by (simp add: K_cfg_def map_pmf_rep_eq nn_integral_distr)

subsection \<open>MDP Kernel and Induced Configurations\<close>

locale Markov_Decision_Process =
  fixes K :: "'s \<Rightarrow> 's pmf set"
  assumes K_wf: "\<And>s. K s \<noteq> {}"
begin

definition "E = (SIGMA s:UNIV. \<Union>D\<in>K s. set_pmf D)"

coinductive cfg_onp :: "'s \<Rightarrow> 's cfg \<Rightarrow> bool" where
  "\<And>s. state cfg = s \<Longrightarrow> action cfg \<in> K s \<Longrightarrow> (\<And>t. t \<in> action cfg \<Longrightarrow> cfg_onp t (cont cfg t)) \<Longrightarrow>
    cfg_onp s cfg"

definition "cfg_on s = {cfg. cfg_onp s cfg}"

lemma
  shows cfg_onD_action[intro, simp]: "cfg \<in> cfg_on s \<Longrightarrow> action cfg \<in> K s"
    and cfg_onD_cont[intro, simp]: "cfg \<in> cfg_on s \<Longrightarrow> t \<in> action cfg \<Longrightarrow> cont cfg t \<in> cfg_on t"
    and cfg_onD_state[simp]: "cfg \<in> cfg_on s \<Longrightarrow> state cfg = s"
    and cfg_onI: "state cfg = s \<Longrightarrow> action cfg \<in> K s \<Longrightarrow> (\<And>t. t \<in> action cfg \<Longrightarrow> cont cfg t \<in> cfg_on t) \<Longrightarrow> cfg \<in> cfg_on s"
  by (auto simp: cfg_on_def intro: cfg_onp.intros elim: cfg_onp.cases)

lemma cfg_on_coinduct[coinduct set: cfg_on]:
  assumes "P s cfg"
  assumes "\<And>cfg s. P s cfg \<Longrightarrow> state cfg = s"
  assumes "\<And>cfg s. P s cfg \<Longrightarrow> action cfg \<in> K s"
  assumes "\<And>cfg s t. P s cfg \<Longrightarrow> t \<in> action cfg \<Longrightarrow> P t (cont cfg t)"
  shows "cfg \<in> cfg_on s"
  using assms cfg_onp.coinduct[of P s cfg] by (simp add: cfg_on_def)

lemma memoryless_on_cfg_onI:
  assumes "\<And>s. f s \<in> K s"
  shows "memoryless_on f s \<in> cfg_on s"
  by (coinduction arbitrary: s) (auto intro: assms)

lemma cfg_of_cfg_onI:
  "D \<in> K s \<Longrightarrow> (\<And>t. t \<in> D \<Longrightarrow> c t \<in> cfg_on t) \<Longrightarrow> Cfg s D c \<in> cfg_on s"
  by (rule cfg_onI) auto

definition "arb_act s = (SOME D. D \<in> K s)"

lemma arb_actI[simp]: "arb_act s \<in> K s"
  by (simp add: arb_act_def some_in_eq K_wf)

lemma cfg_on_not_empty[intro, simp]: "cfg_on s \<noteq> {}"
  by (auto intro: memoryless_on_cfg_onI arb_actI)

sublocale MC: MC_syntax K_cfg .

abbreviation St :: "'s stream measure" where
  "St \<equiv> stream_space (count_space UNIV)"

subsection \<open>Trace Space\<close>

definition "T cfg = distr (MC.T cfg) St (smap state)"

sublocale T: prob_space "T cfg" for cfg
  by (simp add: T_def MC.T.prob_space_distr)

lemma space_T[simp]: "space (T cfg) = space St"
  by (simp add: T_def)

lemma sets_T[simp]: "sets (T cfg) = sets St"
  by (simp add: T_def)

lemma measurable_T1[simp]: "measurable (T cfg) N = measurable St N"
  by (simp add: T_def)

lemma measurable_T2[simp]: "measurable N (T cfg) = measurable N St"
  by (simp add: T_def)

lemma nn_integral_T:
  assumes [measurable]: "f \<in> borel_measurable St"
  shows "(\<integral>\<^sup>+X. f X \<partial>T cfg) = (\<integral>\<^sup>+cfg'. (\<integral>\<^sup>+x. f (state cfg' ## x) \<partial>T cfg') \<partial>K_cfg cfg)"
  by (simp add: T_def MC.nn_integral_T[of _ cfg] nn_integral_distr)

lemma T_eq:
  "T cfg = (measure_pmf (K_cfg cfg) \<bind> (\<lambda>cfg'. distr (T cfg') St (\<lambda>\<omega>. state cfg' ## \<omega>)))"
proof (rule measure_eqI)
  fix A assume "A \<in> sets (T cfg)"
  then show "emeasure (T cfg) A =
    emeasure (measure_pmf (K_cfg cfg) \<bind> (\<lambda>cfg'. distr (T cfg') St (\<lambda>\<omega>. state cfg' ## \<omega>))) A"
    by (subst emeasure_bind[where N=St])
       (auto simp: space_subprob_algebra nn_integral_distr nn_integral_indicator[symmetric] nn_integral_T[of _ cfg]
             simp del: nn_integral_indicator intro!: prob_space_imp_subprob_space T.prob_space_distr)
qed simp

lemma T_memoryless_on: "T (memoryless_on ct s) = MC_syntax.T ct s"
proof -
  interpret ct: MC_syntax ct .
  have "T \<circ> (memoryless_on ct) = MC_syntax.T ct"
  proof (rule ct.T_bisim[symmetric])
    fix s show "(T \<circ> memoryless_on ct) s =
        measure_pmf (ct s) \<bind> (\<lambda>s. distr ((T \<circ> memoryless_on ct) s) St ((##) s))"
      by (auto simp add: T_eq[of "memoryless_on ct s"] K_cfg_def map_pmf_rep_eq bind_distr[where K=St]
                         space_subprob_algebra T.prob_space_distr prob_space_imp_subprob_space
               intro!: bind_measure_pmf_cong)
  qed (simp_all, intro_locales)
  then show ?thesis by (simp add: fun_eq_iff)
qed

lemma nn_integral_T_lfp:
  assumes [measurable]: "case_prod g \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M borel)"
  assumes cont_g: "\<And>s. sup_continuous (g s)"
  assumes int_g: "\<And>f cfg. f \<in> borel_measurable (stream_space (count_space UNIV)) \<Longrightarrow>
    (\<integral>\<^sup>+\<omega>. g (state cfg) (f \<omega>) \<partial>T cfg) = g (state cfg) (\<integral>\<^sup>+\<omega>. f \<omega> \<partial>T cfg)"
  shows "(\<integral>\<^sup>+\<omega>. lfp (\<lambda>f \<omega>. g (shd \<omega>) (f (stl \<omega>))) \<omega> \<partial>T cfg) =
    lfp (\<lambda>f cfg. \<integral>\<^sup>+t. g (state t) (f t) \<partial>K_cfg cfg) cfg"
proof (rule nn_integral_lfp)
  show "\<And>s. sets (T s) = sets St"
      "\<And>F. F \<in> borel_measurable St \<Longrightarrow> (\<lambda>a. g (shd a) (F (stl a))) \<in> borel_measurable St"
    by auto
next
  fix s and F :: "'s stream \<Rightarrow> ennreal" assume "F \<in> borel_measurable St"
  then show "(\<integral>\<^sup>+ a. g (shd a) (F (stl a)) \<partial>T s) =
           (\<integral>\<^sup>+ cfg. g (state cfg) (integral\<^sup>N (T cfg) F) \<partial>K_cfg s)"
    by (rewrite nn_integral_T) (simp_all add: int_g)
qed (auto intro!: order_continuous_intros cont_g[THEN sup_continuous_compose])

lemma emeasure_Collect_T:
  assumes [measurable]: "Measurable.pred St P"
  shows "emeasure (T cfg) {x\<in>space St. P x} =
    (\<integral>\<^sup>+cfg'. emeasure (T cfg') {x\<in>space St. P (state cfg' ## x)} \<partial>K_cfg cfg)"
  using MC.emeasure_Collect_T[of "\<lambda>x. P (smap state x)" cfg]
  by (simp add: nn_integral_distr emeasure_Collect_distr T_def)

definition E_sup :: "'s \<Rightarrow> ('s stream \<Rightarrow> ennreal) \<Rightarrow> ennreal"
where
  "E_sup s f = (\<Squnion>cfg\<in>cfg_on s. \<integral>\<^sup>+x. f x \<partial>T cfg)"

lemma E_sup_const: "0 \<le> c \<Longrightarrow> E_sup s (\<lambda>_. c) = c"
  using T.emeasure_space_1 by (simp add: E_sup_def)

lemma E_sup_mult_right:
  assumes [measurable]: "f \<in> borel_measurable St" and [simp]: "0 \<le> c"
  shows "E_sup s (\<lambda>x. c * f x) = c * E_sup s f"
  by (simp add: nn_integral_cmult E_sup_def SUP_mult_left_ennreal)

lemma E_sup_mono:
  "(\<And>\<omega>. f \<omega> \<le> g \<omega>) \<Longrightarrow> E_sup s f \<le> E_sup s g"
  unfolding E_sup_def by (intro SUP_subset_mono order_refl nn_integral_mono)

lemma E_sup_add:
  assumes [measurable]: "f \<in> borel_measurable St" "g \<in> borel_measurable St"
  shows "E_sup s (\<lambda>x. f x + g x) \<le> E_sup s f + E_sup s g"
proof -
  have "E_sup s (\<lambda>x. f x + g x) = (\<Squnion>cfg\<in>cfg_on s. (\<integral>\<^sup>+x. f x \<partial>T cfg) + (\<integral>\<^sup>+x. g x \<partial>T cfg))"
    by (simp add: E_sup_def nn_integral_add)
  also have "\<dots> \<le> (\<Squnion>cfg\<in>cfg_on s. \<integral>\<^sup>+x. f x \<partial>T cfg) + (\<Squnion>cfg\<in>cfg_on s. (\<integral>\<^sup>+x. g x \<partial>T cfg))"
    by (auto simp: SUP_le_iff intro!: add_mono SUP_upper)
  finally show ?thesis
    by (simp add: E_sup_def)
qed

lemma E_sup_add_left:
  assumes [measurable]: "f \<in> borel_measurable St"
  shows "E_sup s (\<lambda>x. f x + c) = E_sup s f + c"
  by (simp add: nn_integral_add E_sup_def T.emeasure_space_1[simplified] ennreal_SUP_add_left)

lemma E_sup_add_right:
  "f \<in> borel_measurable St \<Longrightarrow> E_sup s (\<lambda>x. c + f x) = c + E_sup s f"
  using E_sup_add_left[of f s c] by (simp add: add.commute)

lemma E_sup_SUP:
  assumes [measurable]: "\<And>i. f i \<in> borel_measurable St" and [simp]: "incseq f"
  shows "E_sup s (\<lambda>x. \<Squnion>i. f i x) = (\<Squnion>i. E_sup s (f i))"
  by (auto simp add: E_sup_def nn_integral_monotone_convergence_SUP intro: SUP_commute)

lemma E_sup_iterate:
  assumes [measurable]: "f \<in> borel_measurable St"
  shows "E_sup s f = (\<Squnion>D\<in>K s. \<integral>\<^sup>+ t. E_sup t (\<lambda>\<omega>. f (t ## \<omega>)) \<partial>measure_pmf D)"
proof -
  let ?v = "\<lambda>t. \<integral>\<^sup>+x. f (state t ## x) \<partial>T t"
  let ?p = "\<lambda>t. E_sup t (\<lambda>\<omega>. f (t ## \<omega>))"
  have "E_sup s f = (\<Squnion>cfg\<in>cfg_on s. \<integral>\<^sup>+t. ?v t \<partial>K_cfg cfg)"
    unfolding E_sup_def by (intro SUP_cong refl) (subst nn_integral_T, simp_all add: cfg_on_def)
  also have "\<dots> = (\<Squnion>D\<in>K s. \<integral>\<^sup>+t. ?p t \<partial>measure_pmf D)"
  proof (intro antisym SUP_least)
    fix cfg :: "'s cfg" assume cfg: "cfg \<in> cfg_on s"
    then show "(\<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg) \<le> (SUP D\<in>K s. \<integral>\<^sup>+t. ?p t \<partial>measure_pmf D)"
      by (auto simp: E_sup_def nn_integral_K_cfg AE_measure_pmf_iff
               intro!: nn_integral_mono_AE SUP_upper2)
  next
    fix D assume D: "D \<in> K s" show "(\<integral>\<^sup>+t. ?p t \<partial>D) \<le> (SUP cfg \<in> cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg)"
    proof cases
      assume p_finite: "\<forall>t\<in>D. ?p t < \<infinity>"
      show ?thesis
      proof (rule ennreal_le_epsilon)
        fix e :: real assume "0 < e"
        have "\<forall>t\<in>D. \<exists>cfg\<in>cfg_on t. ?p t \<le> ?v cfg + e"
        proof
          fix t assume "t \<in> D"
          moreover have "(SUP cfg \<in> cfg_on t. ?v cfg) = ?p t"
            unfolding E_sup_def by (simp add: cfg_on_def)
          ultimately have "(SUP cfg \<in> cfg_on t. ?v cfg) \<noteq> \<infinity>"
            using p_finite by auto
          from SUP_approx_ennreal[OF \<open>0<e\<close> _ refl this]
          show "\<exists>cfg\<in>cfg_on t. ?p t \<le> ?v cfg + e"
            by (auto simp add: E_sup_def intro: less_imp_le)
        qed
        then obtain cfg' where v_cfg': "\<And>t. t \<in> D \<Longrightarrow> ?p t \<le> ?v (cfg' t) + e" and
          cfg_on_cfg': "\<And>t. t \<in> D \<Longrightarrow> cfg' t \<in> cfg_on t"
          unfolding Bex_def bchoice_iff by blast

        let ?cfg = "Cfg s D cfg'"
        have cfg: "K_cfg ?cfg = map_pmf cfg' D"
          by (auto simp add: K_cfg_def fun_eq_iff cfg_on_cfg' intro!: map_pmf_cong)

        have "(\<integral>\<^sup>+ t. ?p t \<partial>D) \<le> (\<integral>\<^sup>+t. ?v (cfg' t) + e \<partial>D)"
          by (intro nn_integral_mono_AE) (simp add: v_cfg' AE_measure_pmf_iff)
        also have "\<dots> = (\<integral>\<^sup>+t. ?v (cfg' t) \<partial>D) + e"
          using \<open>0 < e\<close> measure_pmf.emeasure_space_1[of D]
          by (subst nn_integral_add) (auto intro: cfg_on_cfg' )
        also have "(\<integral>\<^sup>+t. ?v (cfg' t) \<partial>D) = (\<integral>\<^sup>+t. ?v t \<partial>K_cfg ?cfg)"
          by (simp add: cfg map_pmf_rep_eq nn_integral_distr)
        also have "\<dots> \<le> (SUP cfg\<in>cfg_on s. (\<integral>\<^sup>+t. ?v t \<partial>K_cfg cfg))"
          by (auto intro!: SUP_upper intro!: cfg_of_cfg_onI D cfg_on_cfg')
        finally show "(\<integral>\<^sup>+ t. ?p t \<partial>D) \<le> (SUP cfg \<in> cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg) + e"
          by (blast intro: add_mono)
      qed
    next
      assume "\<not> (\<forall>t\<in>D. ?p t < \<infinity>)"
      then obtain t where "t \<in> D" "?p t = \<infinity>"
        by (auto simp: not_less top_unique)
      then have "\<infinity> = pmf (D) t * ?p t"
        by (auto simp: ennreal_mult_top set_pmf_iff)
      also have "\<dots> = (SUP cfg \<in> cfg_on t. pmf (D) t * ?v cfg)"
        unfolding E_sup_def
        by (auto simp: SUP_mult_left_ennreal[symmetric])
      also have "\<dots> \<le> (SUP cfg \<in> cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg)"
        unfolding E_sup_def
      proof (intro SUP_least SUP_upper2)
        fix cfg :: "'s cfg" assume cfg: "cfg \<in> cfg_on t"

        let ?cfg = "Cfg s D ((memoryless_on arb_act) (t := cfg))"
        have C: "K_cfg ?cfg = map_pmf ((memoryless_on arb_act) (t := cfg)) D"
          by (auto simp add: K_cfg_def fun_eq_iff intro!: map_pmf_cong simp: cfg)

        show "?cfg \<in> cfg_on s"
          by (auto intro!: cfg_of_cfg_onI D cfg memoryless_on_cfg_onI)
        have "ennreal (pmf (D) t) * (\<integral>\<^sup>+ x. f (state cfg ## x) \<partial>T cfg) =
          (\<integral>\<^sup>+t'. (\<integral>\<^sup>+ x. f (state cfg ## x) \<partial>T cfg) * indicator {t} t' \<partial>D)"
          by (auto simp add:  max_def emeasure_pmf_single intro: mult_ac)
        also have "\<dots> = (\<integral>\<^sup>+cfg. ?v cfg * indicator {t} (state cfg) \<partial>K_cfg ?cfg)"
          unfolding C using cfg
          by (auto simp add: nn_integral_distr map_pmf_rep_eq split: split_indicator
                   simp del: nn_integral_indicator_singleton
                   intro!: nn_integral_cong)
        also have "\<dots> \<le> (\<integral>\<^sup>+cfg. ?v cfg \<partial>K_cfg ?cfg)"
          by (auto intro!: nn_integral_mono  split: split_indicator)
        finally show "ennreal (pmf (D) t) * (\<integral>\<^sup>+ x. f (state cfg ## x) \<partial>T cfg)
           \<le> (\<integral>\<^sup>+ t. \<integral>\<^sup>+ x. f (state t ## x) \<partial>T t \<partial>K_cfg ?cfg)" .
      qed
      finally show ?thesis
        by (simp add: top_unique del: Sup_eq_top_iff SUP_eq_top_iff)
    qed
  qed
  finally show ?thesis .
qed

lemma E_sup_bot: "E_sup s \<bottom> = 0"
  by (auto simp add: E_sup_def bot_ennreal)

lemma E_sup_lfp:
  fixes g
  defines "l \<equiv> \<lambda>f \<omega>. g (shd \<omega>) (f (stl \<omega>))"
  assumes measurable_g[measurable]: "case_prod g \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M borel)"
  assumes cont_g: "\<And>s. sup_continuous (g s)"
  assumes int_g: "\<And>f cfg. f \<in> borel_measurable St \<Longrightarrow>
     (\<integral>\<^sup>+ \<omega>. g (state cfg) (f \<omega>) \<partial>T cfg) = g (state cfg) (integral\<^sup>N (T cfg) f)"
  shows "(\<lambda>s. E_sup s (lfp l)) = lfp (\<lambda>f s. \<Squnion>D\<in>K s. \<integral>\<^sup>+t. g t (f t) \<partial>measure_pmf D)"
proof (rule lfp_transfer_bounded[where \<alpha>="\<lambda>F s. E_sup s F" and f=l and P="\<lambda>f. f \<in> borel_measurable St"])
  show "sup_continuous (\<lambda>f s. \<Squnion>x\<in>K s. \<integral>\<^sup>+ t. g t (f t) \<partial>measure_pmf x)"
    using cont_g[THEN sup_continuous_compose] by (auto intro!: order_continuous_intros)
  show "sup_continuous l"
    using cont_g[THEN sup_continuous_compose] by (auto intro!: order_continuous_intros simp: l_def)
  show "\<And>F. (\<lambda>s. E_sup s \<bottom>) \<le> (\<lambda>s. \<Squnion>D\<in>K s. \<integral>\<^sup>+ t. g t (F t) \<partial>measure_pmf D)"
    using K_wf by (auto simp: E_sup_bot le_fun_def intro: SUP_upper2 )
next
  fix f :: "'s stream \<Rightarrow> ennreal" assume f: "f \<in> borel_measurable St"
  moreover
  have "E_sup s (\<lambda>\<omega>. g s (f \<omega>)) = g s (E_sup s f)" for s
    unfolding E_sup_def using int_g[OF f]
    by (subst SUP_sup_continuous_ennreal[OF cont_g, symmetric])
       (auto intro!: SUP_cong simp del: cfg_onD_state dest: cfg_onD_state[symmetric])
  ultimately show "(\<lambda>s. E_sup s (l f)) = (\<lambda>s. \<Squnion>D\<in>K s. \<integral>\<^sup>+ t. g t (E_sup t f) \<partial>measure_pmf D)"
    by (subst E_sup_iterate) (auto simp: l_def int_g fun_eq_iff intro!: SUP_cong nn_integral_cong)
qed (auto simp: bot_fun_def l_def SUP_apply[abs_def] E_sup_SUP)

definition "P_sup s P = (\<Squnion>cfg\<in>cfg_on s. emeasure (T cfg) {x\<in>space St. P x})"

lemma P_sup_eq_E_sup:
  assumes [measurable]: "Measurable.pred St P"
  shows "P_sup s P = E_sup s (indicator {x\<in>space St. P x})"
  by (auto simp add: P_sup_def E_sup_def intro!: SUP_cong nn_integral_cong)

lemma P_sup_True[simp]: "P_sup t (\<lambda>\<omega>. True) = 1"
  using T.emeasure_space_1
  by (auto simp add: P_sup_def SUP_constant)

lemma P_sup_False[simp]: "P_sup t (\<lambda>\<omega>. False) = 0"
  by (auto simp add: P_sup_def SUP_constant)

lemma P_sup_SUP:
  fixes P :: "nat \<Rightarrow> 's stream \<Rightarrow> bool"
  assumes "mono P" and P[measurable]: "\<And>i. Measurable.pred St (P i)"
  shows "P_sup s (\<lambda>x. \<exists>i. P i x) = (\<Squnion>i. P_sup s (P i))"
proof -
  have "P_sup s (\<lambda>x. \<Squnion>i. P i x) = (\<Squnion>cfg\<in>cfg_on s. emeasure (T cfg) (\<Union>i. {x\<in>space St. P i x}))"
    by (auto simp: P_sup_def intro!: SUP_cong arg_cong2[where f=emeasure])
  also have "\<dots> = (\<Squnion>cfg\<in>cfg_on s. \<Squnion>i. emeasure (T cfg) {x\<in>space St. P i x})"
    using \<open>mono P\<close> by (auto intro!: SUP_cong SUP_emeasure_incseq[symmetric] simp: mono_def le_fun_def)
  also have "\<dots> = (\<Squnion>i. P_sup s (P i))"
    by (subst SUP_commute) (simp add: P_sup_def)
  finally show ?thesis
    by simp
qed

lemma P_sup_lfp:
  assumes Q: "sup_continuous Q"
  assumes f: "f \<in> measurable St M"
  assumes Q_m: "\<And>P. Measurable.pred M P \<Longrightarrow> Measurable.pred M (Q P)"
  shows "P_sup s (\<lambda>x. lfp Q (f x)) = (\<Squnion>i. P_sup s (\<lambda>x. (Q ^^ i) \<bottom> (f x)))"
  unfolding sup_continuous_lfp[OF Q]
  apply simp
proof (rule P_sup_SUP)
  fix i show "Measurable.pred St (\<lambda>x. (Q ^^ i) \<bottom> (f x))"
    apply (intro measurable_compose[OF f])
    by (induct i) (auto intro!: Q_m)
qed (intro mono_funpow sup_continuous_mono[OF Q] mono_compose[where f=f])

lemma P_sup_iterate:
  assumes [measurable]: "Measurable.pred St P"
  shows "P_sup s P = (\<Squnion>D\<in>K s. \<integral>\<^sup>+ t. P_sup t (\<lambda>\<omega>. P (t ## \<omega>)) \<partial>measure_pmf D)"
proof -
  have [simp]: "\<And>x s. indicator {x \<in> space St. P x} (x ## s) = indicator {s \<in> space St. P (x ## s)} s"
    by (auto simp: space_stream_space split: split_indicator)
  show ?thesis
    using E_sup_iterate[of "indicator {x\<in>space St. P x}" s] by (auto simp: P_sup_eq_E_sup)
qed

definition "E_inf s f = (\<Sqinter>cfg\<in>cfg_on s. \<integral>\<^sup>+x. f x \<partial>T cfg)"

lemma E_inf_const: "0 \<le> c \<Longrightarrow> E_inf s (\<lambda>_. c) = c"
  using T.emeasure_space_1 by (simp add: E_inf_def)

lemma E_inf_mono:
  "(\<And>\<omega>. f \<omega> \<le> g \<omega>) \<Longrightarrow> E_inf s f \<le> E_inf s g"
  unfolding E_inf_def by (intro INF_superset_mono order_refl nn_integral_mono)

lemma E_inf_iterate:
  assumes [measurable]: "f \<in> borel_measurable St"
  shows "E_inf s f = (\<Sqinter>D\<in>K s. \<integral>\<^sup>+ t. E_inf t (\<lambda>\<omega>. f (t ## \<omega>)) \<partial>measure_pmf D)"
proof -
  let ?v = "\<lambda>t. \<integral>\<^sup>+x. f (state t ## x) \<partial>T t"
  let ?p = "\<lambda>t. E_inf t (\<lambda>\<omega>. f (t ## \<omega>))"
  have "E_inf s f = (\<Sqinter>cfg\<in>cfg_on s. \<integral>\<^sup>+t. ?v t \<partial>K_cfg cfg)"
    unfolding E_inf_def by (intro INF_cong refl) (subst nn_integral_T, simp_all add: cfg_on_def)
  also have "\<dots> = (\<Sqinter>D\<in>K s. \<integral>\<^sup>+t. ?p t \<partial>measure_pmf D)"
  proof (intro antisym INF_greatest)
    fix cfg :: "'s cfg" assume cfg: "cfg \<in> cfg_on s"
    then show "(INF D\<in>K s. \<integral>\<^sup>+t. ?p t \<partial>measure_pmf D) \<le> (\<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg)"
      by (auto simp add: E_inf_def nn_integral_K_cfg AE_measure_pmf_iff intro!: nn_integral_mono_AE INF_lower2)
  next
    fix D assume D: "D \<in> K s" show "(INF cfg \<in> cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg) \<le> (\<integral>\<^sup>+t. ?p t \<partial>D)"
    proof (rule ennreal_le_epsilon)
      fix e :: real assume "0 < e"
      have "\<forall>t\<in>D. \<exists>cfg\<in>cfg_on t. ?v cfg \<le> ?p t + e"
      proof
        fix t assume "t \<in> D"
        show "\<exists>cfg\<in>cfg_on t. ?v cfg \<le> ?p t + e"
        proof cases
          assume "?p t = \<infinity>" with cfg_on_not_empty[of t] show ?thesis
            by (auto simp: top_add simp del: cfg_on_not_empty)
        next
          assume p_finite: "?p t \<noteq> \<infinity>"
          note \<open>t \<in> D\<close>
          moreover have "(INF cfg \<in> cfg_on t. ?v cfg) = ?p t"
            unfolding E_inf_def by (simp add: cfg_on_def)
          ultimately have "(INF cfg \<in> cfg_on t. ?v cfg) \<noteq> \<infinity>"
            using p_finite by auto
          from INF_approx_ennreal[OF \<open>0 < e\<close> refl this]
          show "\<exists>cfg\<in>cfg_on t. ?v cfg \<le> ?p t + e"
            by (auto simp: E_inf_def intro: less_imp_le)
        qed
      qed
      then obtain cfg' where v_cfg': "\<And>t. t \<in> D \<Longrightarrow> ?v (cfg' t) \<le> ?p t + e" and
        cfg_on_cfg': "\<And>t. t \<in> D \<Longrightarrow> cfg' t \<in> cfg_on t"
        unfolding Bex_def bchoice_iff by blast

      let ?cfg = "Cfg s D cfg'"

      have cfg: "K_cfg ?cfg = map_pmf cfg' D"
        by (auto simp add: K_cfg_def cfg_on_cfg' intro!: map_pmf_cong)

      have "?cfg \<in> cfg_on s"
        by (auto intro: D cfg_on_cfg' cfg_of_cfg_onI)
      then have "(INF cfg \<in> cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg) \<le> (\<integral>\<^sup>+ t. ?p t + e \<partial>D)"
        by (rule INF_lower2) (auto simp: cfg map_pmf_rep_eq nn_integral_distr v_cfg' AE_measure_pmf_iff intro!: nn_integral_mono_AE)
      also have "\<dots> = (\<integral>\<^sup>+ t. ?p t \<partial>D) + e"
        using \<open>0 < e\<close> by (simp add: nn_integral_add measure_pmf.emeasure_space_1[simplified])
      finally show "(INF cfg \<in> cfg_on s. \<integral>\<^sup>+ t. ?v t \<partial>K_cfg cfg) \<le> (\<integral>\<^sup>+ t. ?p t \<partial>D) + e" .
    qed
  qed
  finally show ?thesis .
qed

lemma emeasure_T_const[simp]: "emeasure (T s) (space St) = 1"
  using T.emeasure_space_1[of s] by simp

lemma E_inf_greatest:
  "(\<And>cfg. cfg \<in> cfg_on s \<Longrightarrow> x \<le> (\<integral>\<^sup>+x. f x \<partial>T cfg)) \<Longrightarrow> x \<le> E_inf s f"
  unfolding E_inf_def by (rule INF_greatest)

lemma E_inf_lower2:
  "cfg \<in> cfg_on s \<Longrightarrow> (\<integral>\<^sup>+x. f x \<partial>T cfg) \<le> x \<Longrightarrow> E_inf s f \<le> x"
  unfolding E_inf_def by (rule INF_lower2)

text \<open>
  Maybe the following statement can be generalized to infinite @{term "K s"}.
\<close>

lemma E_inf_lfp:
  fixes g
  defines "l \<equiv> \<lambda>f \<omega>. g (shd \<omega>) (f (stl \<omega>))"
  assumes measurable_g[measurable]: "case_prod g \<in> borel_measurable (count_space UNIV \<Otimes>\<^sub>M borel)"
  assumes cont_g: "\<And>s. sup_continuous (g s)"
  assumes int_g: "\<And>f cfg. f \<in> borel_measurable St \<Longrightarrow>
     (\<integral>\<^sup>+ \<omega>. g (state cfg) (f \<omega>) \<partial>T cfg) = g (state cfg) (integral\<^sup>N (T cfg) f)"
  assumes K_finite: "\<And>s. finite (K s)"
  shows "(\<lambda>s. E_inf s (lfp l)) = lfp (\<lambda>f s. \<Sqinter>D\<in>K s. \<integral>\<^sup>+t. g t (f t) \<partial>measure_pmf D)"
proof (rule antisym)
  let ?F = "\<lambda>F s. \<Sqinter>D\<in>K s. \<integral>\<^sup>+ t. g t (F t) \<partial>measure_pmf D"
  let ?I = "\<lambda>D. (\<integral>\<^sup>+t. g t (lfp ?F t) \<partial>measure_pmf D)"
  have mono_F: "mono ?F"
    using sup_continuous_mono[OF cont_g]
    by (force intro!: INF_mono nn_integral_mono monoI simp: mono_def le_fun_def)
  define ct where "ct s = (SOME D. D \<in> K s \<and> (lfp ?F s = ?I D))" for s
  { fix s
    have "finite (?I ` K s)"
      by (auto intro: K_finite)
    then obtain D where "D \<in> K s" "?I D = Min (?I ` K s)"
      by (auto simp: K_wf dest!: Min_in)
    note this(2)
    also have "\<dots> = (INF D \<in> K s. ?I D)"
      using K_wf by (subst Min_Inf) (auto intro: K_finite)
    also have "\<dots> = lfp ?F s"
      by (rewrite in "_ = \<hole>" lfp_unfold[OF mono_F]) auto
    finally have "\<exists>D. D \<in> K s \<and> (lfp ?F s = ?I D)"
      using \<open>D \<in> K s\<close> by auto
    then have "ct s \<in> K s \<and> (lfp ?F s = ?I (ct s))"
      unfolding ct_def by (rule someI_ex)
    then have "ct s \<in> K s" "lfp ?F s = ?I (ct s)"
      by auto }
  note ct = this
  then have ct_cfg_on[simp]: "\<And>s. memoryless_on ct s \<in> cfg_on s"
    by (intro memoryless_on_cfg_onI) simp
  then show "(\<lambda>s. E_inf s (lfp l)) \<le> lfp ?F"
  proof (intro le_funI, rule E_inf_lower2)
    fix s
    define P where "P f cfg = \<integral>\<^sup>+ t. g (state t) (f t) \<partial>K_cfg cfg" for f cfg
    have "integral\<^sup>N (T (memoryless_on ct s)) (lfp l) = lfp P (memoryless_on ct s)"
      unfolding P_def l_def using measurable_g cont_g int_g by (rule nn_integral_T_lfp)
    also have "\<dots> = (SUP i. (P ^^ i) \<bottom>) (memoryless_on ct s)"
      by (rewrite sup_continuous_lfp)
         (auto intro!: order_continuous_intros cont_g[THEN sup_continuous_compose] simp: P_def)
    also have "\<dots> = (SUP i. (P ^^ i) \<bottom> (memoryless_on ct s))"
      by (simp add: image_comp)
    also have "\<dots> \<le> lfp ?F s"
    proof (rule SUP_least)
      fix i show "(P ^^ i) \<bottom> (memoryless_on ct s) \<le> lfp ?F s"
      proof (induction i arbitrary: s)
        case 0 then show ?case
          by simp
      next
        case (Suc n)
        have "(P ^^ Suc n) \<bottom> (memoryless_on ct s) =
          (\<integral>\<^sup>+ t. g t ((P ^^ n) \<bottom> (memoryless_on ct t)) \<partial>ct s)"
          by (auto simp add: P_def K_cfg_def AE_measure_pmf_iff intro!: nn_integral_cong_AE)
        also have "\<dots> \<le> (\<integral>\<^sup>+ t. g t (lfp ?F t) \<partial>ct s)"
          by (intro nn_integral_mono sup_continuous_mono[OF cont_g, THEN monoD] Suc)
        also have "\<dots> = lfp ?F s"
          by (rule  ct(2) [symmetric])
        finally show ?case .
      qed
    qed
    finally show "integral\<^sup>N (T (memoryless_on ct s)) (lfp l) \<le> lfp ?F s" .
  qed

  have cont_l: "sup_continuous l"
    by (auto simp: l_def intro!: order_continuous_intros cont_g[THEN sup_continuous_compose])

  show "lfp ?F \<le> (\<lambda>s. E_inf s (lfp l))"
  proof (intro lfp_lowerbound le_funI)
    fix s show "(\<Sqinter>x\<in>K s. \<integral>\<^sup>+ t. g t (E_inf t (lfp l)) \<partial>measure_pmf x) \<le> E_inf s (lfp l)"
    proof (rewrite in "_ \<le> \<hole>" E_inf_iterate)
      show l: "lfp l \<in> borel_measurable St"
        using cont_l by (rule borel_measurable_lfp) (simp add: l_def)
      show "(\<Sqinter>D\<in>K s. \<integral>\<^sup>+ t. g t (E_inf t (lfp l)) \<partial>measure_pmf D) \<le>
        (\<Sqinter>D\<in>K s. \<integral>\<^sup>+ t. E_inf t (\<lambda>\<omega>. lfp l (t ## \<omega>)) \<partial>measure_pmf D)"
      proof (rule INF_mono nn_integral_mono bexI)+
        fix t D assume "D \<in> K s"
        { fix cfg assume "cfg \<in> cfg_on t"
          have "(\<integral>\<^sup>+ \<omega>. g (state cfg) (lfp l \<omega>) \<partial>T cfg) = g (state cfg) (\<integral>\<^sup>+ \<omega>. (lfp l \<omega>) \<partial>T cfg)"
            using l by (rule int_g)
          with \<open>cfg \<in> cfg_on t\<close> have *: "(\<integral>\<^sup>+ \<omega>. g t (lfp l \<omega>) \<partial>T cfg) = g t (\<integral>\<^sup>+ \<omega>. (lfp l \<omega>) \<partial>T cfg)"
            by simp }
        then
        have *: "g t (\<Sqinter>cfg\<in>cfg_on t. integral\<^sup>N (T cfg) (lfp l)) \<le> (\<Sqinter>cfg\<in>cfg_on t. \<integral>\<^sup>+ \<omega>. g t (lfp l \<omega>) \<partial>T cfg)"
          apply simp
          apply (rule INF_greatest)
          apply (rule sup_continuous_mono[OF cont_g, THEN monoD])
          apply (rule INF_lower)
          apply assumption
          done
        show "g t (E_inf t (lfp l)) \<le> E_inf t (\<lambda>\<omega>. lfp l (t ## \<omega>))"
          apply (rewrite in "_ \<le> \<hole>" lfp_unfold[OF sup_continuous_mono[OF cont_l]])
          apply (rewrite in "_ \<le> \<hole>" l_def)
          apply (simp add: E_inf_def *)
          done
      qed
    qed
  qed
qed

definition "P_inf s P = (\<Sqinter>cfg\<in>cfg_on s. emeasure (T cfg) {x\<in>space St. P x})"

lemma P_inf_eq_E_inf:
  assumes [measurable]: "Measurable.pred St P"
  shows "P_inf s P = E_inf s (indicator {x\<in>space St. P x})"
  by (auto simp add: P_inf_def E_inf_def intro!: SUP_cong nn_integral_cong)

lemma P_inf_True[simp]: "P_inf t (\<lambda>\<omega>. True) = 1"
  using T.emeasure_space_1
  by (auto simp add: P_inf_def SUP_constant)

lemma P_inf_False[simp]: "P_inf t (\<lambda>\<omega>. False) = 0"
  by (auto simp add: P_inf_def SUP_constant)

lemma P_inf_INF:
  fixes P :: "nat \<Rightarrow> 's stream \<Rightarrow> bool"
  assumes "decseq P" and P[measurable]: "\<And>i. Measurable.pred St (P i)"
  shows "P_inf s (\<lambda>x. \<forall>i. P i x) = (\<Sqinter>i. P_inf s (P i))"
proof -
  have "P_inf s (\<lambda>x. \<Sqinter>i. P i x) = (\<Sqinter>cfg\<in>cfg_on s. emeasure (T cfg) (\<Inter>i. {x\<in>space St. P i x}))"
    by (auto simp: P_inf_def intro!: INF_cong arg_cong2[where f=emeasure])
  also have "\<dots> = (\<Sqinter>cfg\<in>cfg_on s. \<Sqinter>i. emeasure (T cfg) {x\<in>space St. P i x})"
    using \<open>decseq P\<close> by (auto intro!: INF_cong INF_emeasure_decseq[symmetric] simp: decseq_def le_fun_def)
  also have "\<dots> = (\<Sqinter>i. P_inf s (P i))"
    by (subst INF_commute) (simp add: P_inf_def)
  finally show ?thesis
    by simp
qed

lemma P_inf_gfp:
  assumes Q: "inf_continuous Q"
  assumes f: "f \<in> measurable St M"
  assumes Q_m: "\<And>P. Measurable.pred M P \<Longrightarrow> Measurable.pred M (Q P)"
  shows "P_inf s (\<lambda>x. gfp Q (f x)) = (\<Sqinter>i. P_inf s (\<lambda>x. (Q ^^ i) \<top> (f x)))"
  unfolding inf_continuous_gfp[OF Q]
  apply simp
proof (rule P_inf_INF)
  fix i show "Measurable.pred St (\<lambda>x. (Q ^^ i) \<top> (f x))"
    apply (intro measurable_compose[OF f])
    by (induct i) (auto intro!: Q_m)
next
  show "decseq (\<lambda>i x. (Q ^^ i) \<top> (f x))"
    using inf_continuous_mono[OF Q, THEN funpow_increasing[rotated]]
    unfolding decseq_def le_fun_def by auto
qed

lemma P_inf_iterate:
  assumes [measurable]: "Measurable.pred St P"
  shows "P_inf s P = (\<Sqinter>D\<in>K s. \<integral>\<^sup>+ t. P_inf t (\<lambda>\<omega>. P (t ## \<omega>)) \<partial>measure_pmf D)"
proof -
  have [simp]: "\<And>x s. indicator {x \<in> space St. P x} (x ## s) = indicator {s \<in> space St. P (x ## s)} s"
    by (auto simp: space_stream_space split: split_indicator)
  show ?thesis
    using E_inf_iterate[of "indicator {x\<in>space St. P x}" s] by (auto simp: P_inf_eq_E_inf)
qed

end

subsection \<open>Finite MDPs\<close>

locale Finite_Markov_Decision_Process = Markov_Decision_Process K for K :: "'s \<Rightarrow> 's pmf set" +
  fixes S :: "'s set"
  assumes S_not_empty: "S \<noteq> {}"
  assumes S_finite: "finite S"
  assumes K_closed: "\<And>s. s \<in> S \<Longrightarrow> (\<Union>D\<in>K s. set_pmf D) \<subseteq> S"
  assumes K_finite: "\<And>s. s \<in> S \<Longrightarrow> finite (K s)"
begin

lemma action_closed: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> t \<in> action cfg \<Longrightarrow> t \<in> S"
  using cfg_onD_action[of cfg s] K_closed[of s] by auto

lemma set_pmf_closed: "s \<in> S \<Longrightarrow> D \<in> K s \<Longrightarrow> t \<in> D \<Longrightarrow> t \<in> S"
  using K_closed by auto

lemma Pi_closed: "ct \<in> Pi S K \<Longrightarrow> s \<in> S \<Longrightarrow> t \<in> ct s \<Longrightarrow> t \<in> S"
  using set_pmf_closed by auto

lemma E_closed: "s \<in> S \<Longrightarrow> (s, t) \<in> E \<Longrightarrow> t \<in> S"
  using K_closed by (auto simp: E_def)

lemma set_pmf_finite: "s \<in> S \<Longrightarrow> D \<in> K s \<Longrightarrow> finite D"
  using K_closed by (intro finite_subset[OF _ S_finite]) auto

definition "valid_cfg = (\<Union>s\<in>S. cfg_on s)"

lemma valid_cfgI: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> cfg \<in> valid_cfg"
  by (auto simp: valid_cfg_def)

lemma valid_cfgD: "cfg \<in> valid_cfg \<Longrightarrow> cfg \<in> cfg_on (state cfg)"
  by (auto simp: valid_cfg_def)

lemma
  shows valid_cfg_state_in_S: "cfg \<in> valid_cfg \<Longrightarrow> state cfg \<in> S"
    and valid_cfg_action: "cfg \<in> valid_cfg \<Longrightarrow> s \<in> action cfg \<Longrightarrow> s \<in> S"
    and valid_cfg_cont: "cfg \<in> valid_cfg \<Longrightarrow> s \<in> action cfg \<Longrightarrow> cont cfg s \<in> valid_cfg"
  by (auto simp: valid_cfg_def intro!: bexI[of _ s] intro: action_closed)

lemma valid_K_cfg[intro]: "cfg \<in> valid_cfg \<Longrightarrow> cfg' \<in> K_cfg cfg \<Longrightarrow> cfg' \<in> valid_cfg"
  by (auto simp add: K_cfg_def valid_cfg_cont)

definition "simple ct = memoryless_on (\<lambda>s. if s \<in> S then ct s else arb_act s)"

lemma simple_cfg_on[simp]: "ct \<in> Pi S K \<Longrightarrow> simple ct s \<in> cfg_on s"
  by (auto simp: simple_def intro!: memoryless_on_cfg_onI)

lemma simple_valid_cfg[simp]: "ct \<in> Pi S K \<Longrightarrow> s \<in> S \<Longrightarrow> simple ct s \<in> valid_cfg"
  by (auto intro: valid_cfgI)

lemma cont_simple[simp]: "s \<in> S \<Longrightarrow> t \<in> set_pmf (ct s) \<Longrightarrow> cont (simple ct s) t = simple ct t"
  by (simp add: simple_def)

lemma state_simple[simp]: "state (simple ct s) = s"
  by (simp add: simple_def)

lemma action_simple[simp]: "s \<in> S \<Longrightarrow> action (simple ct s) = ct s"
  by (simp add: simple_def)

lemma simple_valid_cfg_iff: "ct \<in> Pi S K \<Longrightarrow> simple ct s \<in> valid_cfg \<longleftrightarrow> s \<in> S"
  using cfg_onD_state[of "simple ct s"] by (auto simp add: valid_cfg_def intro!: bexI[of _ s])

end

end
