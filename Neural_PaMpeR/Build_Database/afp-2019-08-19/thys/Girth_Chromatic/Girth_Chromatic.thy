theory Girth_Chromatic
imports
  Ugraphs
  Girth_Chromatic_Misc
  "HOL-Probability.Probability"
  "HOL-Decision_Procs.Approximation"
begin

section \<open>Probability Space on Sets of Edges\<close>

definition cylinder :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a set \<Rightarrow> 'a set set" where
  "cylinder S A B = {T \<in> Pow S. A \<subseteq> T \<and> B \<inter> T = {}}"

lemma full_sum:
  fixes p :: real
  assumes "finite S"
  shows "(\<Sum>A\<in>Pow S. p^card A * (1 - p)^card (S - A)) = 1"
using assms
proof induct
  case (insert s S)
  have "inj_on (insert s) (Pow S)"
      and "\<And>x. S - insert s x = S - x"
      and "Pow S \<inter> insert s ` Pow S = {}"
      and "\<And>x. x \<in> Pow S \<Longrightarrow> card (insert s S - x) = Suc (card (S - x))"
    using insert(1-2) by (auto simp: insert_Diff_if intro!: inj_onI)
  moreover have "\<And>x. x \<subseteq> S \<Longrightarrow> card (insert s x) = Suc (card x)"
    using insert(1-2) by (subst card.insert) (auto dest: finite_subset)
  ultimately show ?case
    by (simp add: sum.reindex sum_distrib_left[symmetric] ac_simps
                  insert.hyps sum.union_disjoint Pow_insert)
qed simp

text \<open>Definition of the probability space on edges:\<close>
locale edge_space =
  fixes n :: nat and p :: real
  assumes p_prob: "0 \<le> p" "p \<le> 1"
begin

definition S_verts :: "nat set" where
  "S_verts \<equiv> {1..n}"

definition S_edges :: "uedge set" where
  "S_edges = all_edges S_verts"

definition edge_ugraph :: "uedge set \<Rightarrow> ugraph" where
  "edge_ugraph es \<equiv> (S_verts, es \<inter> S_edges)"

definition "P = point_measure (Pow S_edges) (\<lambda>s. p^card s * (1 - p)^card (S_edges - s))"

lemma finite_verts[intro!]: "finite S_verts"
  by (auto simp: S_verts_def)

lemma finite_edges[intro!]: "finite S_edges"
  by (auto simp: S_edges_def all_edges_def finite_verts)

lemma finite_graph[intro!]: "finite (uverts (edge_ugraph es))"
  unfolding edge_ugraph_def by auto

lemma uverts_edge_ugraph[simp]: "uverts (edge_ugraph es) = S_verts"
  by (simp add: edge_ugraph_def)

lemma uedges_edge_ugraph[simp]: "uedges (edge_ugraph es) = es \<inter> S_edges"
  unfolding edge_ugraph_def by simp

lemma space_eq: "space P = Pow S_edges" by (simp add: P_def space_point_measure)

lemma sets_eq: "sets P = Pow (Pow S_edges)" by (simp add: P_def sets_point_measure)

lemma emeasure_eq:
  "emeasure P A = (if A \<subseteq> Pow S_edges then (\<Sum>edges\<in>A. p^card edges * (1 - p)^card (S_edges - edges)) else 0)"
  using finite_edges p_prob
  by (simp add: P_def space_point_measure emeasure_point_measure_finite
    sets_point_measure emeasure_notin_sets)

lemma integrable_P[intro, simp]: "integrable P (f::_ \<Rightarrow> real)"
  using finite_edges by (simp add: integrable_point_measure_finite P_def)

lemma borel_measurable_P[measurable]: "f \<in> borel_measurable P"
  unfolding P_def by simp

lemma prob_space_P: "prob_space P"
proof
  show "emeasure P (space P) = 1" \<comment> \<open>Sum of probabilities equals 1\<close>
    using finite_edges by (simp add: emeasure_eq full_sum one_ereal_def space_eq)
qed

end

sublocale edge_space \<subseteq> prob_space P
  by (rule prob_space_P)

context edge_space
begin

lemma prob_eq:
  "prob A = (if A \<subseteq> Pow S_edges then (\<Sum>edges\<in>A. p^card edges * (1 - p)^card (S_edges - edges)) else 0)"
  using emeasure_eq[of A] p_prob unfolding emeasure_eq_measure by (simp add: sum_nonneg)

lemma integral_finite_singleton: "integral\<^sup>L P f = (\<Sum>x\<in>Pow S_edges. f x * measure P {x})"
  using p_prob prob_eq unfolding P_def
  by (subst lebesgue_integral_point_measure_finite) (auto intro!: sum.cong)

text \<open>Probability of cylinder sets:\<close>
lemma cylinder_prob:
  assumes "A \<subseteq> S_edges" "B \<subseteq> S_edges" "A \<inter> B = {}"
  shows "prob (cylinder S_edges A B) = p ^ (card A) * (1 - p) ^ (card B)" (is "_ = ?pp A B")
proof -
  have "Pow S_edges \<inter> cylinder S_edges A B = cylinder S_edges A B"
       "\<And>x. x \<in> cylinder S_edges A B \<Longrightarrow> A \<union> x = x"
       "\<And>x. x \<in> cylinder S_edges A B \<Longrightarrow> finite x"
       "\<And>x. x \<in> cylinder S_edges A B \<Longrightarrow> B \<inter> (S_edges - B - x) = {}"
       "\<And>x. x \<in> cylinder S_edges A B \<Longrightarrow> B \<union> (S_edges - B - x) = S_edges - x"
       "finite A" "finite B"
    using assms by (auto simp add: cylinder_def intro: finite_subset)
  then have "(\<Sum>T\<in>cylinder S_edges A B. ?pp T (S_edges - T))
      = (\<Sum>T \<in> cylinder S_edges A B. p^(card A + card (T - A)) * (1 - p)^(card B + card ((S_edges - B) - T)))"
    using finite_edges by (simp add: card_Un_Int)
  also have "\<dots> = ?pp A B * (\<Sum>T\<in>cylinder S_edges A B. ?pp (T - A) (S_edges - B - T))"
    by (simp add: power_add sum_distrib_left ac_simps)
  also have "\<dots> = ?pp A B"
  proof -
    have "\<And>T. T \<in> cylinder S_edges A B \<Longrightarrow> S_edges - B - T = (S_edges - A) - B - (T - A)"
         "Pow (S_edges - A - B) = (\<lambda>x. x - A) ` cylinder S_edges A B"
         "inj_on (\<lambda>x. x - A) (cylinder S_edges A B)"
         "finite (S_edges - A - B)"
      using assms by (auto simp: cylinder_def intro!: inj_onI)
    with full_sum[of "S_edges - A - B"] show ?thesis by (simp add: sum.reindex)
  qed
  finally show ?thesis by (auto simp add: prob_eq cylinder_def)
qed

lemma Markov_inequality:
  fixes a :: real and X :: "uedge set \<Rightarrow> real"
  assumes "0 < c" "\<And>x. 0 \<le> f x"
  shows "prob {x \<in> space P. c \<le> f x} \<le> (\<integral>x. f x \<partial> P) / c"
proof -
  from assms have "(\<integral>\<^sup>+ x. ennreal (f x) \<partial>P) = (\<integral>x. f x \<partial>P)"
    by (intro nn_integral_eq_integral) auto
  with assms show ?thesis
    using nn_integral_Markov_inequality[of f P "space P" "1 / c"]
    by (simp cong: nn_integral_cong add: emeasure_eq_measure ennreal_mult[symmetric])
qed

end

subsection \<open>Graph Probabilities outside of @{term Edge_Space} locale\<close>

text \<open>
 These abbreviations allow a compact expression of probabilities about random
 graphs outside of the @{term Edge_Space} locale. We also transfer a few of the lemmas
 we need from the locale into the toplevel theory.
\<close>

abbreviation MGn :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (uedge set) measure" where
  "MGn p n \<equiv> (edge_space.P n (p n))"
abbreviation probGn :: "(nat \<Rightarrow> real) \<Rightarrow> nat \<Rightarrow> (uedge set \<Rightarrow> bool) \<Rightarrow> real" where
  "probGn p n P \<equiv> measure (MGn p n) {es \<in> space (MGn p n). P es}"

lemma probGn_le:
  assumes p_prob: "0 < p n" "p n < 1"
  assumes sub: "\<And>n es. es \<in> space (MGn p n) \<Longrightarrow> P n es \<Longrightarrow> Q n es"
  shows "probGn p n (P n) \<le> probGn p n (Q n)"
proof -
  from p_prob interpret E: edge_space n "p n" by unfold_locales auto
  show ?thesis
    by (auto intro!: E.finite_measure_mono sub simp: E.space_eq E.sets_eq)
qed

section \<open>Short cycles\<close>

definition short_cycles :: "ugraph \<Rightarrow> nat \<Rightarrow> uwalk set" where
  "short_cycles G k \<equiv> {p \<in> ucycles G. uwalk_length p \<le> k}"

text \<open>obtains a vertex in a short cycle:\<close>
definition choose_v :: "ugraph \<Rightarrow> nat \<Rightarrow> uvert" where
  "choose_v G k \<equiv> SOME u. \<exists>p. p \<in> short_cycles G k \<and> u \<in> set p"

partial_function (tailrec) kill_short :: "ugraph \<Rightarrow> nat \<Rightarrow> ugraph" where
  "kill_short G k = (if short_cycles G k = {} then G else (kill_short (G -- (choose_v G k)) k))"

lemma ksc_simps[simp]:
  "short_cycles G k = {} \<Longrightarrow> kill_short G k = G"
  "short_cycles G k \<noteq> {}  \<Longrightarrow> kill_short G k = kill_short (G -- (choose_v G k)) k"
  by (auto simp: kill_short.simps)

lemma
  assumes "short_cycles G k \<noteq> {}"
  shows choose_v__in_uverts: "choose_v G k \<in> uverts G" (is ?t1)
    and choose_v__in_short: "\<exists>p. p \<in> short_cycles G k \<and> choose_v G k \<in> set p" (is ?t2)
proof -
  from assms obtain p where "p \<in> ucycles G" "uwalk_length p \<le> k"
    unfolding short_cycles_def by auto
  moreover
  then obtain u where "u \<in> set p" unfolding ucycles_def
    by (cases p) (auto simp: uwalk_length_conv)
  ultimately have "\<exists>u p. p \<in> short_cycles G k \<and> u \<in> set p"
    by (auto simp: short_cycles_def)
  then show ?t2 by (auto simp: choose_v_def intro!: someI_ex)
  then show ?t1 by (auto simp: short_cycles_def ucycles_def uwalks_def)
qed

lemma kill_step_smaller:
  assumes "short_cycles G k \<noteq> {}"
  shows "short_cycles (G -- (choose_v G k)) k \<subset> short_cycles G k"
proof -
  let ?cv = "choose_v G k"
  from assms obtain p where "p \<in> short_cycles G k" "?cv \<in> set p"
    by atomize_elim (rule choose_v__in_short)

  have "short_cycles (G -- ?cv) k \<subseteq> short_cycles G k"
  proof
    fix p assume "p \<in> short_cycles (G -- ?cv) k"
    then show "p \<in> short_cycles G k"
      unfolding short_cycles_def ucycles_def uwalks_def
      using edges_Gu[of G ?cv] by (auto simp: verts_Gu)
  qed
  moreover have "p \<notin> short_cycles (G -- ?cv) k"
    using \<open>?cv \<in> set p\<close> by (auto simp: short_cycles_def ucycles_def uwalks_def verts_Gu)
  ultimately show ?thesis using \<open>p \<in> short_cycles G k\<close> by auto
qed

text \<open>Induction rule for @{term kill_short}:\<close>
lemma kill_short_induct[consumes 1, case_names empty kill_vert]:
  assumes fin: "finite (uverts G)"
  assumes a_empty: "\<And>G. short_cycles G k = {} \<Longrightarrow> P G k"
  assumes a_kill: "\<And>G. finite (short_cycles G k) \<Longrightarrow> short_cycles G k \<noteq> {}
    \<Longrightarrow> P (G -- (choose_v G k)) k \<Longrightarrow> P G k"
  shows "P G k"
proof -
  have "finite (short_cycles G k)"
    using finite_ucycles[OF fin] by (auto simp: short_cycles_def)
  then show ?thesis
    by (induct "short_cycles G k" arbitrary: G rule: finite_psubset_induct)
      (metis kill_step_smaller a_kill a_empty)
qed

text \<open>Large Girth (after @{term kill_short}):\<close>
lemma kill_short_large_girth:
  assumes "finite (uverts G)"
  shows "k < girth (kill_short G k)"
using assms
proof (induct G k rule: kill_short_induct)
  case (empty G)
  then have "\<And>p. p \<in> ucycles G \<Longrightarrow> k < enat (uwalk_length p)"
    by (auto simp: short_cycles_def)
  with empty show ?case by (auto simp: girth_def intro: enat_less_INF_I)
qed simp

text \<open>Order of graph (after @{term kill_short}):\<close>
lemma kill_short_order_of_graph:
  assumes "finite (uverts G)"
  shows "card (uverts G) - card (short_cycles G k) \<le> card (uverts (kill_short G k))"
using assms assms
proof (induct G k rule: kill_short_induct)
  case (kill_vert G)
  let ?oG = "G -- (choose_v G k)"

  have "finite (uverts ?oG)"
    using kill_vert by (auto simp: remove_vertex_def)
  moreover
  have "uverts (kill_short G k) = uverts (kill_short ?oG k)"
    using kill_vert by simp
  moreover
  have "card (uverts G) = Suc (card (uverts ?oG))"
    using choose_v__in_uverts kill_vert
    by (simp add: remove_vertex_def card_Suc_Diff1 del: card_Diff_insert)
  moreover
  have "card (short_cycles ?oG k) < card (short_cycles G k)"
    by (intro psubset_card_mono kill_vert.hyps kill_step_smaller)
  ultimately show ?case using kill_vert.hyps by presburger
qed simp

text \<open>Independence number (after @{term kill_short}):\<close>
lemma kill_short_\<alpha>:
  assumes "finite (uverts G)"
  shows "\<alpha> (kill_short G k) \<le> \<alpha> G"
using assms
proof (induct G k rule: kill_short_induct)
  case (kill_vert G)
  note kill_vert(3)
  also have "\<alpha> (G -- (choose_v G k)) \<le> \<alpha> G" by (rule \<alpha>_remove_le)
  finally show ?case using kill_vert by simp
qed simp

text \<open>Wellformedness (after @{term kill_short}):\<close>
lemma kill_short_uwellformed:
  assumes "finite (uverts G)" "uwellformed G"
  shows "uwellformed (kill_short G k)"
using assms
proof (induct G k rule: kill_short_induct)
  case (kill_vert G)
  from kill_vert.prems have "uwellformed (G -- (choose_v G k))"
    by (auto simp: uwellformed_def remove_vertex_def)
  with kill_vert.hyps show ?case by simp
qed simp


section \<open>The Chromatic-Girth Theorem\<close>

text \<open>Probability of Independent Edges:\<close>
lemma (in edge_space) random_prob_independent:
  assumes "n \<ge> k" "k \<ge> 2"
  shows "prob {es \<in> space P. k \<le> \<alpha> (edge_ugraph es)}
    \<le> (n choose k)*(1-p)^(k choose 2)"
proof -
  let "?k_sets" = "{vs. vs \<subseteq> S_verts \<and> card vs = k}"

  { fix vs assume A: "vs \<in> ?k_sets"
    then have B: "all_edges vs \<subseteq> S_edges"
      unfolding all_edges_def S_edges_def by blast

    have "{es \<in> space P. vs \<in> independent_sets (edge_ugraph es)}
        = cylinder S_edges {} (all_edges vs)" (is "?L = _")
      using A by (auto simp: independent_sets_def edge_ugraph_def space_eq cylinder_def)
    then have "prob ?L = (1-p)^(k choose 2)"
      using A B finite by (auto simp: cylinder_prob card_all_edges dest: finite_subset)
  }
  note prob_k_indep = this
    \<comment> \<open>probability that a fixed set of k vertices is independent in a random graph\<close>

  have "{es \<in> space P. k \<in> card ` independent_sets (edge_ugraph es)}
    = (\<Union>vs \<in> ?k_sets. {es \<in> space P. vs \<in> independent_sets (edge_ugraph es)})" (is "?L = ?R")
    unfolding image_def space_eq independent_sets_def by auto
  then have "prob ?L \<le> (\<Sum>vs \<in> ?k_sets. prob {es \<in> space P. vs \<in> independent_sets (edge_ugraph es)})"
    by (auto intro!: finite_measure_subadditive_finite simp: space_eq sets_eq)
  also have "\<dots> = (n choose k)*((1 - p) ^ (k choose 2))"
    by (simp add: prob_k_indep S_verts_def n_subsets)
  finally show ?thesis using \<open>k \<ge> 2\<close> by (simp add: le_\<alpha>_iff)
qed

text \<open>Almost never many independent edges:\<close>
lemma almost_never_le_\<alpha>:
  fixes k :: nat
    and p :: "nat \<Rightarrow> real"
  assumes p_prob: "\<forall>\<^sup>\<infinity> n. 0 < p n \<and> p n < 1"
  assumes [arith]: "k > 0"
  assumes N_prop: "\<forall>\<^sup>\<infinity> n. (6 * k * ln n)/n \<le> p n"
  shows "(\<lambda>n. probGn p n (\<lambda>es. 1/2*n/k \<le> \<alpha> (edge_space.edge_ugraph n es))) \<longlonglongrightarrow> 0"
    (is "(\<lambda>n. ?prob_fun n) \<longlonglongrightarrow> 0")
proof -
  let "?prob_fun_raw n" = "probGn p n (\<lambda>es. nat(ceiling (1/2*n/k)) \<le> \<alpha> (edge_space.edge_ugraph n es))"

  define r where "r n = 1 / 2 * n / k" for n :: nat
  let ?nr = "\<lambda>n. nat(ceiling (r n))"

  have r_pos: "\<And>n. 0 < n \<Longrightarrow> 0 < r n " by (auto simp: r_def field_simps)

  have nr_bounds: "\<forall>\<^sup>\<infinity> n. 2 \<le> ?nr n \<and> ?nr n \<le> n"
    by (intro eventually_sequentiallyI[of "4 * k"])
       (simp add: r_def nat_ceiling_le_eq le_natceiling_iff field_simps)

  from nr_bounds p_prob have ev_prob_fun_raw_le:
    "\<forall>\<^sup>\<infinity> n. probGn p n (\<lambda>es. ?nr n\<le> \<alpha> (edge_space.edge_ugraph n es))
      \<le> (n * exp (- p n * (real (?nr n) - 1) / 2)) powr ?nr n"
    (is "\<forall>\<^sup>\<infinity> n. ?prob_fun_raw_le n")
  proof (rule eventually_elim2)
    fix n :: nat assume A: "2 \<le> ?nr n \<and> ?nr n \<le> n" "0 < p n \<and>p n < 1"
    then interpret pG: edge_space n "p n" by unfold_locales auto

    have r: "real (?nr n - Suc 0) = real (?nr n) - Suc 0" using A by auto

    have [simp]: "n>0" using A by linarith
    have "probGn p n (\<lambda>es. ?nr n \<le> \<alpha> (edge_space.edge_ugraph n es))
        \<le> (n choose ?nr n) * (1 - p n)^(?nr n choose 2)"
      using A by (auto intro: pG.random_prob_independent)
    also have "\<dots> \<le> n powr ?nr n * (1 - p n) powr (?nr n choose 2)"
      using A  by (simp add: powr_realpow of_nat_power [symmetric] binomial_le_pow  del: of_nat_power)
    also have "\<dots> = n powr ?nr n * (1 - p n) powr (?nr n * (?nr n - 1) / 2)"
      by (cases "even (?nr n - 1)")
        (auto simp add: n_choose_2_nat real_of_nat_div)
    also have "\<dots> = n powr ?nr n * ((1 - p n) powr ((?nr n - 1) / 2)) powr ?nr n"
      by (auto simp add: powr_powr r ac_simps)
    also have "\<dots> \<le> (n * exp (- p n * (?nr n - 1) / 2)) powr ?nr n"
    proof -
      have "(1 - p n) powr ((?nr n - 1) / 2) \<le> exp (- p n) powr ((?nr n - 1) / 2)"
        using A by (auto simp: powr_mono2 diff_conv_add_uminus simp del: add_uminus_conv_diff)
      also have "\<dots> = exp (- p n * (?nr n - 1) / 2)" by (auto simp: powr_def)
      finally show ?thesis
        using A by (auto simp: powr_mono2 powr_mult)
    qed
    finally show "probGn p n (\<lambda>es. ?nr n \<le> \<alpha> (edge_space.edge_ugraph n es))
      \<le> (n * exp (- p n * (real (?nr n) - 1) / 2)) powr ?nr n"
      using A r by simp
  qed

  from p_prob N_prop
  have ev_expr_bound: "\<forall>\<^sup>\<infinity> n. n * exp (-p n * (real (?nr n) - 1) / 2) \<le> (exp 1 / n) powr (1 / 2)"
  proof (elim eventually_rev_mp, intro eventually_sequentiallyI conjI impI)
    fix n assume n_bound[arith]: "2 \<le> n"
      and p_bound: "0 < p n \<and> p n < 1" "(6 * k * ln n) / n \<le> p n"
    have r_bound: "r n \<le> ?nr n" by (rule real_nat_ceiling_ge)

    have "n * exp (-p n * (real (?nr n)- 1) / 2) \<le> n * exp (- 3 / 2 * ln n + p n / 2)"
    proof -
      have "0 < ln n" using "n_bound" by auto
      then have "(3 / 2) * ln n \<le> ((6 * k * ln n) / n) * (?nr n / 2)"
        using r_bound le_of_int_ceiling[of "n/2*k"]
        by (simp add: r_def field_simps del: le_of_int_ceiling)
      also have "\<dots> \<le> p n * (?nr n / 2)"
        using n_bound p_bound r_bound r_pos[of n] by (auto simp: field_simps)
      finally show ?thesis using r_bound by (auto simp: field_simps)
    qed
    also have "\<dots> \<le> n * n powr (- 3 / 2) * exp 1 powr (1 / 2)"
      using p_bound by (simp add: powr_def exp_add [symmetric])
    also have "\<dots> \<le> n powr (-1 / 2) * exp 1 powr (1 / 2)" by (simp add: powr_mult_base)
    also have "\<dots> = (exp 1 / n) powr (1/2)"
      by (simp add: powr_divide powr_minus_divide)
    finally show "n * exp (- p n * (real (?nr n) - 1) / 2) \<le> (exp 1 / n) powr (1 / 2)" .
  qed

  have ceil_bound: "\<And>G n. 1/2*n/k \<le> \<alpha> G \<longleftrightarrow> nat(ceiling (1/2*n/k)) \<le> \<alpha> G"
    by (case_tac "\<alpha> G") (auto simp: nat_ceiling_le_eq)

  show ?thesis
  proof (unfold ceil_bound, rule real_tendsto_sandwich)
    show "(\<lambda>n. 0) \<longlonglongrightarrow> 0"
        "(\<lambda>n. (exp 1 / n) powr (1 / 2)) \<longlonglongrightarrow> 0"
        "\<forall>\<^sup>\<infinity> n. 0 \<le> ?prob_fun_raw n"
      using p_prob by (auto intro: measure_nonneg LIMSEQ_inv_powr elim: eventually_mono)
  next
    from nr_bounds ev_expr_bound ev_prob_fun_raw_le
    show "\<forall>\<^sup>\<infinity> n. ?prob_fun_raw n \<le> (exp 1 / n) powr (1 / 2)"
    proof (elim eventually_rev_mp, intro eventually_sequentiallyI impI conjI)
      fix n assume A: "3 \<le> n"
        and nr_bounds: "2 \<le> ?nr n \<and> ?nr n \<le> n"
        and prob_fun_raw_le: "?prob_fun_raw_le n"
        and expr_bound: "n * exp (- p n * (real (nat(ceiling (r n))) - 1) / 2) \<le> (exp 1 / n) powr (1 / 2)"

      have "exp 1 < (3 :: real)" by (approximation 6)
      then have "(exp 1 / n) powr (1 / 2) \<le> 1 powr (1 / 2)"
        using A by (intro powr_mono2) (auto simp: field_simps)
      then have ep_bound: "(exp 1 / n) powr (1 / 2) \<le> 1" by simp

      have "?prob_fun_raw n \<le> (n * exp (- p n * (real (?nr n) - 1) / 2)) powr (?nr n)"
        using prob_fun_raw_le by (simp add: r_def)
      also have "\<dots> \<le> ((exp 1 / n) powr (1 / 2)) powr ?nr n"
        using expr_bound A by (auto simp: powr_mono2)
      also have "\<dots> \<le> ((exp 1 / n) powr (1 / 2))"
        using nr_bounds ep_bound A by (auto simp: powr_le_one_le)
      finally show "?prob_fun_raw n \<le> (exp 1 / n) powr (1 / 2)" .
    qed
  qed
qed

text \<open>Mean number of k-cycles in a graph. (Or rather of paths describing a circle of length @{term k}):\<close>
lemma (in edge_space) mean_k_cycles:
  assumes "3 \<le> k" "k < n"
  shows "(\<integral>es. card {c \<in> ucycles (edge_ugraph es). uwalk_length c = k} \<partial> P)
    = of_nat (fact n div fact (n - k)) * p ^ k"
proof -
  let ?k_cycle = "\<lambda>es c k. c \<in> ucycles (edge_ugraph es) \<and> uwalk_length c = k"
  define C where "C k = {c. ?k_cycle S_edges c k}" for k
    \<comment> \<open>@{term "C k"} is the set of all possible cycles of size @{term k} in @{term "edge_ugraph S_edges"}\<close>
  define XG  where "XG es = {c. ?k_cycle es c k}" for es
    \<comment> \<open>@{term "XG es"} is the set of cycles contained in a @{term "edge_ugraph es"}\<close>
  define XC where "XC c = {es \<in> space P. ?k_cycle es c k}" for c
    \<comment> \<open>"@{term "XC c"} is the set of graphs (edge sets) containing a cycle c"\<close>
  then have XC_in_sets: "\<And>c. XC c \<in> sets P"
      and XC_cyl: "\<And>c. c \<in> C k \<Longrightarrow> XC c = cylinder S_edges (set (uwalk_edges c)) {}"
    by (auto simp: ucycles_def space_eq uwalks_def C_def cylinder_def sets_eq)

  have "(\<integral>es. card {c \<in> ucycles (edge_ugraph es). uwalk_length c = k} \<partial> P)
      =  (\<Sum>x\<in>space P. card (XG x) * prob {x})"
    by (simp add: XG_def integral_finite_singleton space_eq)
  also have "\<dots> = (\<Sum>c\<in>C k. prob (cylinder S_edges (set (uwalk_edges c)) {}))"
  proof -
    have XG_Int_C: "\<And>s. s \<in> space P \<Longrightarrow> C k \<inter> XG s = XG s"
      unfolding XG_def C_def ucycles_def uwalks_def edge_ugraph_def by auto
    have fin_XC: "\<And>k. finite (XC k)" and fin_C: "finite (C k)"
      unfolding C_def XC_def by (auto simp: finite_edges space_eq intro!: finite_ucycles)

    have "(\<Sum>x\<in>space P. card (XG x) * prob {x}) = (\<Sum>x\<in>space P. (\<Sum>c \<in> XG x. prob {x}))"
      by simp
    also have "\<dots> = (\<Sum>x\<in>space P. (\<Sum>c \<in> C k. if c \<in> XG x then prob {x} else 0))"
      using fin_C by (simp add: sum.If_cases) (simp add: XG_Int_C)
    also have "\<dots> = (\<Sum>c \<in> C k. (\<Sum> x \<in> space P \<inter> XC c. prob {x}))"
      using finite_edges by (subst sum.swap) (simp add: sum.inter_restrict XG_def XC_def space_eq)
    also have "\<dots> = (\<Sum>c \<in> C k. prob (XC c))"
      using fin_XC XC_in_sets
      by (auto simp add: prob_eq sets_eq space_eq intro!: sum.cong)
    finally show ?thesis by (simp add: XC_cyl)
  qed
  also have "\<dots> = (\<Sum>c\<in>C k. p ^ k)"
  proof -
    have "\<And>x. x \<in> C k \<Longrightarrow> card (set (uwalk_edges x)) = uwalk_length x"
      by (auto simp: uwalk_length_def C_def ucycles_distinct_edges intro: distinct_card)
    then show ?thesis by (auto simp: C_def ucycles_def uwalks_def cylinder_prob)
  qed
  also have "\<dots> = of_nat (fact n div fact (n - k)) * p ^ k"
  proof -
    have inj_last_Cons: "\<And>A. inj_on (\<lambda>es. last es # es) A" by (rule inj_onI) simp
    { fix xs A assume "3 \<le> length xs - Suc 0" "hd xs = last xs"
      then have "xs \<in> (\<lambda>xs. last xs # xs) ` A \<longleftrightarrow> tl xs \<in> A"
        by (cases xs) (auto simp: inj_image_mem_iff[OF inj_last_Cons] split: if_split_asm) }
    note image_mem_iff_inst = this

    { fix xs have "xs \<in> uwalks (edge_ugraph S_edges) \<Longrightarrow> set (tl xs) \<subseteq> S_verts"
        unfolding uwalks_def by (induct xs) auto }
    moreover
    { fix xs assume "set xs \<subseteq> S_verts" "2 \<le> length xs" "distinct xs"
      then have "(last xs # xs) \<in> uwalks (edge_ugraph S_edges)"
      proof (induct xs rule: uwalk_edges.induct)
        case (3 x y ys)
        have S_edges_memI: "\<And>x y. x \<in> S_verts \<Longrightarrow> y \<in> S_verts \<Longrightarrow> x \<noteq> y \<Longrightarrow> {x, y} \<in> S_edges"
          unfolding S_edges_def all_edges_def image_def by auto

        have "ys \<noteq> [] \<Longrightarrow> set ys \<subseteq> S_verts \<Longrightarrow> last ys \<in> S_verts"  by auto
        with 3 show ?case
          by (auto simp add: uwalks_def Suc_le_eq intro: S_edges_memI)
      qed simp_all}
    moreover note \<open>3 \<le> k\<close>
    ultimately
    have "C k = (\<lambda>xs. last xs # xs) ` {xs. length xs = k \<and> distinct xs \<and> set xs \<subseteq> S_verts}"
      by (auto simp: C_def ucycles_def uwalk_length_conv image_mem_iff_inst)
    moreover have "card S_verts = n" by (simp add: S_verts_def)
    ultimately have "card (C k) = fact n div fact (n - k)"
      using \<open>k < n\<close>
      by (simp add: card_image[OF inj_last_Cons] card_lists_distinct_length_eq' fact_div_fact)
    then show ?thesis by simp
  qed
  finally show ?thesis by simp
qed

text \<open>Girth-Chromatic number theorem:\<close>
theorem girth_chromatic:
  fixes l :: nat
  shows "\<exists>G. uwellformed G \<and> l < girth G \<and> l < chromatic_number G"
proof -
  define k where "k = max 3 l"
  define \<epsilon> where "\<epsilon> = 1 / (2 * k)"
  define p where "p n = real n powr (\<epsilon> - 1)" for n :: nat

  let ?ug = edge_space.edge_ugraph

  define short_count where "short_count g = card (short_cycles g k)" for g
    \<comment> \<open>This random variable differs from the one used in the proof of theorem 11.2.2,
          as we count the number of paths describing a circle, not the circles themselves\<close>

  from k_def have "3 \<le> k" "l \<le> k" by auto
  from \<open>3 \<le> k\<close> have \<epsilon>_props: "0 < \<epsilon>" "\<epsilon> < 1 / k" "\<epsilon> < 1" by (auto simp: \<epsilon>_def field_simps)

  have ev_p: "\<forall>\<^sup>\<infinity> n. 0 < p n \<and> p n < 1"
  proof (rule eventually_sequentiallyI)
    fix n :: nat assume "2 \<le> n"
    with \<open>\<epsilon> < 1\<close> have "n powr (\<epsilon> - 1) < 1" by (auto intro!: powr_less_one)
    then show "0 < p n \<and> p n < 1" using \<open>2 \<le> n\<close>
      by (auto simp: p_def)
  qed
  then
  have prob_short_count_le: "\<forall>\<^sup>\<infinity> n. probGn p n (\<lambda>es. (real n/2) \<le> short_count (?ug n es))
      \<le> 2 * (k - 2) * n powr (\<epsilon> * k - 1)"  (is "\<forall>\<^sup>\<infinity> n. ?P n")
  proof (elim eventually_rev_mp, intro eventually_sequentiallyI impI)
    fix n :: nat assume A: "Suc k \<le> n" "0 < p n \<and> p n < 1"
    then interpret pG: edge_space n "p n" by unfold_locales auto
    have "1 \<le> n" using A by auto

    define mean_short_count where "mean_short_count = (\<integral>es. short_count (?ug n es) \<partial> pG.P)"

    have mean_short_count_le: "mean_short_count \<le> (k - 2) * n powr (\<epsilon> * k)"
    proof -
      have small_empty: "\<And>es k. k \<le> 2 \<Longrightarrow> short_cycles (edge_space.edge_ugraph n es) k = {}"
          by (auto simp add: short_cycles_def ucycles_def)
      have short_count_conv: "\<And>es. short_count (?ug n es) = (\<Sum>i=3..k. real (card {c \<in> ucycles (?ug n es). uwalk_length c = i}))"
      proof (unfold short_count_def, induct k)
        case 0 with small_empty show ?case by auto
      next
        case (Suc k)
        show ?case proof (cases "Suc k \<le> 2")
          case True with small_empty show ?thesis by auto
        next
          case False
          have "{c \<in> ucycles (?ug n es). uwalk_length c \<le> Suc k}
              = {c \<in> ucycles (?ug n es). uwalk_length c \<le> k} \<union> {c \<in> ucycles (?ug n es). uwalk_length c = Suc k}"
            by auto
          moreover
          have "finite (uverts (edge_space.edge_ugraph n es))" by auto
          ultimately
          have "card {c \<in> ucycles (?ug n es). uwalk_length c \<le> Suc k}
            = card {c \<in> ucycles (?ug n es). uwalk_length c \<le> k} + card {c \<in> ucycles (?ug n es). uwalk_length c = Suc k}"
            using finite_ucycles by (subst card_Un_disjoint[symmetric]) auto
          then show ?thesis
            using Suc False unfolding short_cycles_def by (auto simp: not_le)
        qed
      qed

      have "mean_short_count = (\<Sum>i=3..k. \<integral>es. card {c \<in> ucycles (?ug n es). uwalk_length c = i} \<partial> pG.P)"
        unfolding mean_short_count_def short_count_conv
        by (subst Bochner_Integration.integral_sum) (auto intro: pG.integral_finite_singleton)
      also have "\<dots> = (\<Sum>i\<in>{3..k}. of_nat (fact n div fact (n - i)) * p n ^ i)"
        using A by (simp add: pG.mean_k_cycles)
      also have "\<dots> \<le> (\<Sum> i\<in>{3..k}. n ^ i * p n ^ i)"
        apply (rule sum_mono)
        by (meson A fact_div_fact_le_pow  Suc_leD atLeastAtMost_iff of_nat_le_iff order_trans real_mult_le_cancel_iff1 zero_less_power)
      also have "... \<le> (\<Sum> i\<in>{3..k}. n powr (\<epsilon> * k))"
        using \<open>1 \<le> n\<close> \<open>0 < \<epsilon>\<close> A
        by (intro sum_mono) (auto simp: p_def field_simps powr_mult_base powr_powr
          powr_realpow[symmetric] powr_mult[symmetric] powr_add[symmetric])
      finally show ?thesis by simp
    qed

    have "pG.prob {es \<in> space pG.P. n/2 \<le> short_count (?ug n es)} \<le> mean_short_count / (n/2)"
      unfolding mean_short_count_def using \<open>1 \<le> n\<close>
      by (intro pG.Markov_inequality) (auto simp: short_count_def)
    also have "\<dots> \<le> 2 * (k - 2) * n powr (\<epsilon> * k - 1)"
    proof -
      have "mean_short_count / (n / 2) \<le> 2 * (k - 2) * (1 / n powr 1) * n powr (\<epsilon> * k)"
        using mean_short_count_le \<open>1 \<le> n\<close> by (simp add: field_simps)
      then show ?thesis by (simp add: powr_diff algebra_simps)
    qed
    finally show "?P n" .
  qed

  define pf_short_count pf_\<alpha>
    where "pf_short_count n = probGn p n (\<lambda>es. n/2 \<le> short_count (?ug n es))"
      and "pf_\<alpha> n = probGn p n (\<lambda>es. 1/2 * n/k \<le> \<alpha> (edge_space.edge_ugraph n es))"
    for n

  have ev_short_count_le: "\<forall>\<^sup>\<infinity> n. pf_short_count n < 1 / 2"
  proof -
    have "\<epsilon> * k - 1 < 0"
      using \<epsilon>_props \<open>3 \<le> k\<close> by (auto simp: field_simps)
    then have "(\<lambda>n. 2 * (k - 2) * n powr (\<epsilon> * k - 1)) \<longlonglongrightarrow> 0" (is "?bound \<longlonglongrightarrow> 0")
      by (intro tendsto_mult_right_zero LIMSEQ_neg_powr)
    then have "\<forall>\<^sup>\<infinity> n. dist (?bound n) 0  < 1 / 2"
      by (rule tendstoD) simp
    with prob_short_count_le show ?thesis
      by (rule eventually_elim2) (auto simp: dist_real_def pf_short_count_def)
  qed

  have lim_\<alpha>: "pf_\<alpha> \<longlonglongrightarrow> 0"
  proof -
    have "0 < k" using \<open>3 \<le> k\<close> by simp

    have "\<forall>\<^sup>\<infinity> n. (6*k) * ln n / n \<le> p n \<longleftrightarrow> (6*k) * ln n * n powr - \<epsilon> \<le> 1"
    proof (rule eventually_sequentiallyI)
     fix n :: nat assume "1 \<le> n"
      then have "(6 * k) * ln n / n \<le> p n \<longleftrightarrow> (6*k) * ln n * (n powr - 1) \<le> n powr (\<epsilon> - 1)"
        by  (subst powr_minus) (simp add: divide_inverse p_def)
      also have "\<dots> \<longleftrightarrow> (6*k) * ln n * ((n powr - 1) / (n powr (\<epsilon> - 1))) \<le> n powr (\<epsilon> - 1) / (n powr (\<epsilon> - 1))"
        using \<open>1 \<le> n\<close> by (auto simp: field_simps)
      also have "\<dots> \<longleftrightarrow> (6*k) * ln n * n powr - \<epsilon> \<le> 1"
        by (simp add: powr_diff [symmetric] )
      finally show "(6*k) * ln n / n \<le> p n \<longleftrightarrow> (6*k) * ln n * n powr - \<epsilon> \<le> 1" .
    qed
    then have "(\<forall>\<^sup>\<infinity> n. (6 * k) * ln n / real n \<le> p n)
        \<longleftrightarrow> (\<forall>\<^sup>\<infinity> n. (6*k) * ln n * n powr - \<epsilon> \<le> 1)"
      by (rule eventually_subst)
    also have "\<forall>\<^sup>\<infinity> n. (6*k) * ln n * n powr - \<epsilon> \<le> 1"
    proof -
      { fix n :: nat assume "0 < n"
        have "ln (real n) \<le> n powr (\<epsilon>/2) / (\<epsilon>/2)"
          using \<open>0 < n\<close> \<open>0 < \<epsilon>\<close> by (intro ln_powr_bound) auto
        also have "\<dots> \<le> 2/\<epsilon> * n powr (\<epsilon>/2)" by (auto simp: field_simps)
        finally have "(6*k) * ln n * (n powr - \<epsilon>)  \<le> (6*k) * (2/\<epsilon> * n powr (\<epsilon>/2)) * (n powr - \<epsilon>)"
          using \<open>0 < n\<close> \<open>0 < k\<close> by (intro mult_right_mono mult_left_mono) auto
        also have "\<dots> = 12*k/\<epsilon> * n powr (-\<epsilon>/2)"
          unfolding divide_inverse
          by (auto simp: field_simps powr_minus[symmetric] powr_add[symmetric])
        finally have "(6*k) * ln n * (n powr - \<epsilon>) \<le> 12*k/\<epsilon> * n powr (-\<epsilon>/2)" .
      }
      then have "\<forall>\<^sup>\<infinity> n. (6*k) * ln n * (n powr - \<epsilon>) \<le> 12*k/\<epsilon> * n powr (-\<epsilon>/2)"
        by (intro eventually_sequentiallyI[of 1]) auto
      also have "\<forall>\<^sup>\<infinity> n. 12*k/\<epsilon> * n powr (-\<epsilon>/2) \<le> 1"
      proof -
        have "(\<lambda>n. 12*k/\<epsilon> * n powr (-\<epsilon>/2)) \<longlonglongrightarrow> 0"
          using \<open>0 < \<epsilon>\<close> by (intro tendsto_mult_right_zero LIMSEQ_neg_powr) auto
        then show ?thesis
          using \<open>0 < \<epsilon>\<close> by (auto elim: eventually_mono simp: dist_real_def dest!: tendstoD[where e=1])
      qed
      finally (eventually_le_le) show ?thesis .
    qed
    finally have "\<forall>\<^sup>\<infinity> n. real (6 * k) * ln (real n) / real n \<le> p n" .
    with ev_p \<open>0 < k\<close> show ?thesis unfolding pf_\<alpha>_def by (rule almost_never_le_\<alpha>)
  qed

  from ev_short_count_le lim_\<alpha>[THEN tendstoD, of "1/2"] ev_p
  have "\<forall>\<^sup>\<infinity> n. 0 < p n \<and> p n < 1 \<and> pf_short_count n < 1/2 \<and> pf_\<alpha> n < 1/2"
    by simp (elim eventually_rev_mp, auto simp: eventually_sequentially dist_real_def)
  then obtain n where "0 < p n" "p n < 1" and [arith]: "0 < n"
      and probs: "pf_short_count n < 1/2" "pf_\<alpha> n < 1/2"
    by (auto simp: eventually_sequentially)
  then interpret ES: edge_space n "(p n)" by unfold_locales auto

  have rest_compl: "\<And>A P. A - {x\<in>A. P x} = {x\<in>A. \<not>P x}" by blast

  from probs have "ES.prob ({es \<in> space ES.P. n/2 \<le> short_count (?ug n es)}
      \<union> {es \<in> space ES.P. 1/2 * n/k \<le> \<alpha> (?ug n es)}) \<le> pf_short_count n + pf_\<alpha> n"
    unfolding pf_short_count_def pf_\<alpha>_def  by (subst ES.finite_measure_subadditive) auto
  also have "\<dots> < 1" using probs by auto
  finally have "0 < ES.prob (space ES.P - ({es \<in> space ES.P. n/2 \<le> short_count (?ug n es)}
      \<union> {es \<in> space ES.P. 1/2 * n/k \<le> \<alpha> (?ug n es)}))" (is "0 < ES.prob ?S")
    by (subst ES.prob_compl) auto
  also have "?S = {es \<in> space ES.P. short_count (?ug n es) < n/2 \<and> \<alpha> (?ug n es) < 1/2* n/k}" (is "\<dots> = ?C")
    by (auto simp: not_less rest_compl)
  finally have "?C \<noteq> {}" by (intro notI) (simp only:, auto)
  then obtain es where es_props: "es \<in> space ES.P"
      "short_count (?ug n es) < n/2" "\<alpha> (?ug n es) < 1/2 * n/k"
    by auto
    \<comment> \<open>now we obtained a high colored graph (few independent nodes) with almost no short cycles\<close>

  define G where "G = ?ug n es"
  define H where "H = kill_short G k"

  have G_props: "uverts G = {1..n}" "finite (uverts G)" "short_count G < n/2" "\<alpha> G < 1/2 * n/k"
    unfolding G_def using es_props by (auto simp: ES.S_verts_def)

  have "uwellformed G" by (auto simp: G_def uwellformed_def all_edges_def ES.S_edges_def)
  with G_props have T1: "uwellformed H" unfolding H_def by (intro kill_short_uwellformed)

  have "enat l \<le> enat k" using \<open>l \<le> k\<close> by simp
  also have "\<dots> < girth H" using G_props by (auto simp: kill_short_large_girth H_def)
  finally have T2: "l < girth H" .

  have card_H: "n/2 \<le> card (uverts H)"
    using G_props es_props kill_short_order_of_graph[of G k] by (simp add: short_count_def H_def)

  then have uverts_H: "uverts H \<noteq> {}" "0 < card (uverts H)" by auto
  then have "0 < \<alpha> H" using zero_less_\<alpha> uverts_H by auto

  have \<alpha>_HG: "\<alpha> H \<le> \<alpha> G"
    unfolding H_def G_def by (auto intro: kill_short_\<alpha>)

  have "enat l \<le> ereal k" using \<open>l \<le> k\<close> by auto
  also have "\<dots> < (n/2) / \<alpha> G" using G_props \<open>3 \<le> k\<close>
    by (cases "\<alpha> G") (auto simp: field_simps)
  also have "\<dots> \<le> (n/2) / \<alpha> H" using \<alpha>_HG \<open>0 < \<alpha> H\<close>
    by (auto simp: ereal_of_enat_pushout intro!: ereal_divide_left_mono)
  also have "\<dots> \<le> card (uverts H) / \<alpha> H" using card_H \<open>0 < \<alpha> H\<close>
    by (auto intro!: ereal_divide_right_mono)
  also have "\<dots> \<le> chromatic_number H" using uverts_H T1 by (intro chromatic_lb) auto
  finally have T3: "l < chromatic_number H"
    by (simp del: ereal_of_enat_simps)

  from T1 T2 T3 show ?thesis by fast
qed

end
