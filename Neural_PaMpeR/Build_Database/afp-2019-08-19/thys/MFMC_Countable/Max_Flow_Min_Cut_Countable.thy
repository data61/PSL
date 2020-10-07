(* Author: Andreas Lochbihler, ETH Zurich *)
theory Max_Flow_Min_Cut_Countable imports
  MFMC_Misc
begin

section \<open>Graphs\<close>

type_synonym 'v edge = "'v \<times> 'v"

record 'v graph =
  edge :: "'v \<Rightarrow> 'v \<Rightarrow> bool"

abbreviation edges :: "('v, 'more) graph_scheme \<Rightarrow> 'v edge set" ("\<^bold>E\<index>")
where "\<^bold>E\<^bsub>G\<^esub> \<equiv> {(x, y). edge G x y}"

definition outgoing :: "('v, 'more) graph_scheme \<Rightarrow> 'v \<Rightarrow> 'v set" ("\<^bold>O\<^bold>U\<^bold>T\<index>")
where "\<^bold>O\<^bold>U\<^bold>T\<^bsub>G\<^esub> x = {y. (x, y) \<in> \<^bold>E\<^bsub>G\<^esub>}"

definition incoming :: "('v, 'more) graph_scheme \<Rightarrow> 'v \<Rightarrow> 'v set" ("\<^bold>I\<^bold>N\<index>")
where "\<^bold>I\<^bold>N\<^bsub>G\<^esub> y = {x. (x, y) \<in> \<^bold>E\<^bsub>G\<^esub>}"

text \<open>
  Vertices are implicitly defined as the endpoints of edges, so we do not allow isolated vertices.
  For the purpose of flows, this does not matter as isolated vertices cannot contribute to a flow.
  The advantage is that we do not need any invariant on graphs that the endpoints of edges are a
  subset of the vertices. Conversely, this design choice makes a few proofs about reductions on webs
  harder, because we have to adjust other sets which are supposed to be part of the vertices.
\<close>

definition vertex :: "('v, 'more) graph_scheme \<Rightarrow> 'v \<Rightarrow> bool"
where "vertex G x \<longleftrightarrow> Domainp (edge G) x \<or> Rangep (edge G) x"

lemma vertexI:
  shows vertexI1: "edge \<Gamma> x y \<Longrightarrow> vertex \<Gamma> x"
  and vertexI2: "edge \<Gamma> x y \<Longrightarrow> vertex \<Gamma> y"
by(auto simp add: vertex_def)

abbreviation vertices :: "('v, 'more) graph_scheme \<Rightarrow> 'v set" ("\<^bold>V\<index>")
where "\<^bold>V\<^bsub>G\<^esub> \<equiv> Collect (vertex G)"

lemma "\<^bold>V_def": "\<^bold>V\<^bsub>G\<^esub> = fst ` \<^bold>E\<^bsub>G\<^esub> \<union> snd ` \<^bold>E\<^bsub>G\<^esub>"
by(auto 4 3 simp add: vertex_def intro: rev_image_eqI prod.expand)

type_synonym 'v path = "'v list"

abbreviation path :: "('v, 'more) graph_scheme \<Rightarrow> 'v \<Rightarrow> 'v path \<Rightarrow> 'v \<Rightarrow> bool"
where "path G \<equiv> rtrancl_path (edge G)"

inductive cycle :: "('v, 'more) graph_scheme \<Rightarrow> 'v path \<Rightarrow> bool"
  for G
where \<comment> \<open>Cycles must not pass through the same node multiple times. Otherwise, the cycle might
  enter a node via two different edges and leave it via just one edge. Thus, the clean-up lemma
  would not hold any more.\<close>
  cycle: "\<lbrakk> path G v p v; p \<noteq> []; distinct p \<rbrakk> \<Longrightarrow> cycle G p"

inductive_simps cycle_Nil [simp]: "cycle G Nil"

abbreviation cycles :: "('v, 'more) graph_scheme \<Rightarrow> 'v path set"
where "cycles G \<equiv> Collect (cycle G)"

lemma countable_cycles [simp]:
  assumes "countable (\<^bold>V\<^bsub>G\<^esub>)"
  shows "countable (cycles G)"
proof -
  have "cycles G \<subseteq> lists \<^bold>V\<^bsub>G\<^esub>"
    by(auto elim!: cycle.cases dest: rtrancl_path_Range_end rtrancl_path_Range simp add: vertex_def)
  thus ?thesis by(rule countable_subset)(simp add: assms)
qed

definition cycle_edges :: "'v path \<Rightarrow> 'v edge list"
where "cycle_edges p = zip p (rotate1 p)"

lemma cycle_edges_not_Nil: "cycle G p \<Longrightarrow> cycle_edges p \<noteq> []"
by(auto simp add: cycle_edges_def cycle.simps neq_Nil_conv zip_Cons1 split: list.split)

lemma distinct_cycle_edges:
  "cycle G p \<Longrightarrow> distinct (cycle_edges p)"
by(erule cycle.cases)(simp add: cycle_edges_def distinct_zipI2)

lemma cycle_enter_leave_same:
  assumes "cycle G p"
  shows "card (set [(x', y) \<leftarrow> cycle_edges p. x' = x]) = card (set [(x', y) \<leftarrow> cycle_edges p. y = x])"
  (is "?lhs = ?rhs")
using assms
proof cases
  case (cycle v)
  from distinct_cycle_edges[OF assms]
  have "?lhs = length [x' \<leftarrow> map fst (cycle_edges p). x' = x]"
    by(subst distinct_card; simp add: filter_map o_def split_def)
  also have "\<dots> = (if x \<in> set p then 1 else 0)" using cycle
    by(auto simp add: cycle_edges_def filter_empty_conv length_filter_conv_card card_eq_1_iff in_set_conv_nth dest: nth_eq_iff_index_eq)
  also have "\<dots> = length [y \<leftarrow> map snd (cycle_edges p). y = x]" using cycle
    apply(auto simp add: cycle_edges_def filter_empty_conv Suc_length_conv intro!: exI[where x=x])
    apply(drule split_list_first)
    apply(auto dest: split_list_first simp add: append_eq_Cons_conv rotate1_append filter_empty_conv split: if_split_asm dest: in_set_tlD)
    done
  also have "\<dots> = ?rhs" using distinct_cycle_edges[OF assms]
    by(subst distinct_card; simp add: filter_map o_def split_def)
  finally show ?thesis .
qed

lemma cycle_leave_ex_enter:
  assumes "cycle G p" and "(x, y) \<in> set (cycle_edges p)"
  shows "\<exists>z. (z, x) \<in> set (cycle_edges p)"
using assms
by(cases)(auto 4 3 simp add: cycle_edges_def cong: conj_cong split: if_split_asm intro: set_zip_rightI dest: set_zip_leftD)

lemma cycle_edges_edges:
  assumes "cycle G p"
  shows "set (cycle_edges p) \<subseteq> \<^bold>E\<^bsub>G\<^esub>"
proof
  fix x
  assume "x \<in> set (cycle_edges p)"
  then obtain i where x: "x = (p ! i, rotate1 p ! i)" and i: "i < length p"
    by(auto simp add: cycle_edges_def set_zip)
  from assms obtain v where p: "path G v p v" and "p \<noteq> []" and "distinct p" by cases
  let ?i = "Suc i mod length p"
  have "?i < length p" by (simp add: \<open>p \<noteq> []\<close>)
  note rtrancl_path_nth[OF p this]
  also have "(v # p) ! ?i = p ! i"
  proof(cases "Suc i < length p")
    case True thus ?thesis by simp
  next
    case False
    with i have "Suc i = length p" by simp
    moreover from p \<open>p \<noteq> []\<close> have "last p = v" by(rule rtrancl_path_last)
    ultimately show ?thesis using \<open>p \<noteq> []\<close> by(simp add: last_conv_nth)(metis diff_Suc_Suc diff_zero)
  qed
  also have "p ! ?i = rotate1 p ! i" using i by(simp add: nth_rotate1)
  finally show "x \<in> \<^bold>E\<^bsub>G\<^esub>" by(simp add: x)
qed


section \<open>Network and Flow\<close>

record 'v network = "'v graph" +
  capacity :: "'v edge \<Rightarrow> ennreal"
  source :: "'v"
  sink :: "'v"

type_synonym 'v flow = "'v edge \<Rightarrow> ennreal"

inductive_set support_flow :: "'v flow \<Rightarrow> 'v edge set"
  for f
where "f e > 0 \<Longrightarrow> e \<in> support_flow f"

lemma support_flow_conv: "support_flow f = {e. f e > 0}"
by(auto simp add: support_flow.simps)

lemma not_in_support_flowD: "x \<notin> support_flow f \<Longrightarrow> f x = 0"
by(simp add: support_flow_conv)

definition d_OUT :: "'v flow \<Rightarrow> 'v \<Rightarrow> ennreal"
where "d_OUT g x = (\<Sum>\<^sup>+ y. g (x, y))"

definition d_IN :: "'v flow \<Rightarrow> 'v \<Rightarrow> ennreal"
where "d_IN g y = (\<Sum>\<^sup>+ x. g (x, y))"

lemma d_OUT_mono: "(\<And>y. f (x, y) \<le> g (x, y)) \<Longrightarrow> d_OUT f x \<le> d_OUT g x"
by(auto simp add: d_OUT_def le_fun_def intro: nn_integral_mono)

lemma d_IN_mono: "(\<And>x. f (x, y) \<le> g (x, y)) \<Longrightarrow> d_IN f y \<le> d_IN g y"
by(auto simp add: d_IN_def le_fun_def intro: nn_integral_mono)

lemma d_OUT_0 [simp]: "d_OUT (\<lambda>_. 0) x = 0"
by(simp add: d_OUT_def)

lemma d_IN_0 [simp]: "d_IN (\<lambda>_. 0) x = 0"
by(simp add: d_IN_def)

lemma d_OUT_add: "d_OUT (\<lambda>e. f e + g e) x = d_OUT f x + d_OUT g x"
unfolding d_OUT_def by(simp add: nn_integral_add)

lemma d_IN_add: "d_IN (\<lambda>e. f e + g e) x = d_IN f x + d_IN g x"
unfolding d_IN_def by(simp add: nn_integral_add)

lemma d_OUT_cmult: "d_OUT (\<lambda>e. c * f e) x = c * d_OUT f x"
by(simp add: d_OUT_def nn_integral_cmult)

lemma d_IN_cmult: "d_IN (\<lambda>e. c * f e) x = c * d_IN f x"
by(simp add: d_IN_def nn_integral_cmult)

lemma d_OUT_ge_point: "f (x, y) \<le> d_OUT f x"
by(auto simp add: d_OUT_def intro!: nn_integral_ge_point)

lemma d_IN_ge_point: "f (y, x) \<le> d_IN f x"
by(auto simp add: d_IN_def intro!: nn_integral_ge_point)

lemma d_OUT_monotone_convergence_SUP:
  assumes "incseq (\<lambda>n y. f n (x, y))"
  shows "d_OUT (\<lambda>e. SUP n. f n e) x = (SUP n. d_OUT (f n) x)"
unfolding d_OUT_def by(rule nn_integral_monotone_convergence_SUP[OF assms]) simp

lemma d_IN_monotone_convergence_SUP:
  assumes "incseq (\<lambda>n x. f n (x, y))"
  shows "d_IN (\<lambda>e. SUP n. f n e) y = (SUP n. d_IN (f n) y)"
unfolding d_IN_def by(rule nn_integral_monotone_convergence_SUP[OF assms]) simp

lemma d_OUT_diff:
  assumes "\<And>y. g (x, y) \<le> f (x, y)" "d_OUT g x \<noteq> \<top>"
  shows "d_OUT (\<lambda>e. f e - g e) x = d_OUT f x - d_OUT g x"
using assms by(simp add: nn_integral_diff d_OUT_def)

lemma d_IN_diff:
  assumes "\<And>x. g (x, y) \<le> f (x, y)" "d_IN g y \<noteq> \<top>"
  shows "d_IN (\<lambda>e. f e - g e) y = d_IN f y - d_IN g y"
using assms by(simp add: nn_integral_diff d_IN_def)

lemma fixes G (structure)
  shows d_OUT_alt_def: "(\<And>y. (x, y) \<notin> \<^bold>E \<Longrightarrow> g (x, y) = 0) \<Longrightarrow> d_OUT g x = (\<Sum>\<^sup>+  y\<in>\<^bold>O\<^bold>U\<^bold>T x. g (x, y))"
  and d_IN_alt_def: "(\<And>x. (x, y) \<notin> \<^bold>E \<Longrightarrow> g (x, y) = 0) \<Longrightarrow> d_IN g y = (\<Sum>\<^sup>+ x\<in>\<^bold>I\<^bold>N y. g (x, y))"
unfolding d_OUT_def d_IN_def
by(fastforce simp add: max_def d_OUT_def d_IN_def nn_integral_count_space_indicator outgoing_def incoming_def intro!: nn_integral_cong split: split_indicator)+

lemma d_OUT_alt_def2: "d_OUT g x = (\<Sum>\<^sup>+ y\<in>{y. (x, y) \<in> support_flow g}. g (x, y))"
  and d_IN_alt_def2: "d_IN g y = (\<Sum>\<^sup>+ x\<in>{x. (x, y) \<in> support_flow g}. g (x, y))"
unfolding d_OUT_def d_IN_def
by(auto simp add: max_def d_OUT_def d_IN_def nn_integral_count_space_indicator outgoing_def incoming_def support_flow.simps intro!: nn_integral_cong split: split_indicator)+

definition d_diff :: "('v edge \<Rightarrow> ennreal) \<Rightarrow> 'v \<Rightarrow> ennreal"
where "d_diff g x = d_OUT g x - d_IN g x"

abbreviation KIR :: "('v edge \<Rightarrow> ennreal) \<Rightarrow> 'v \<Rightarrow> bool"
where "KIR f x \<equiv> d_OUT f x = d_IN f x"

inductive_set SINK :: "('v edge \<Rightarrow> ennreal) \<Rightarrow> 'v set"
  for f
where SINK: "d_OUT f x = 0 \<Longrightarrow> x \<in> SINK f"

lemma SINK_mono:
  assumes "\<And>e. f e \<le> g e"
  shows "SINK g \<subseteq> SINK f"
proof(rule subsetI; erule SINK.cases; hypsubst)
  fix x
  assume "d_OUT g x = 0"
  moreover have "d_OUT f x \<le> d_OUT g x" using assms by(rule d_OUT_mono)
  ultimately have "d_OUT f x = 0" by simp
  thus "x \<in> SINK f" ..
qed

lemma SINK_mono': "f \<le> g \<Longrightarrow> SINK g \<subseteq> SINK f"
by(rule SINK_mono)(rule le_funD)

lemma support_flow_Sup: "support_flow (Sup Y) = (\<Union>f\<in>Y. support_flow f)"
by(auto simp add: support_flow_conv less_SUP_iff)

lemma
  assumes chain: "Complete_Partial_Order.chain (\<le>) Y"
  and Y: "Y \<noteq> {}"
  and countable: "countable (support_flow (Sup Y))"
  shows d_OUT_Sup: "d_OUT (Sup Y) x = (SUP f\<in>Y. d_OUT f x)" (is "?OUT x" is "?lhs1 x = ?rhs1 x")
  and d_IN_Sup: "d_IN (Sup Y) y = (SUP f\<in>Y. d_IN f y)" (is "?IN" is "?lhs2 = ?rhs2")
  and SINK_Sup: "SINK (Sup Y) = (\<Inter>f\<in>Y. SINK f)" (is "?SINK")
proof -
  have chain': "Complete_Partial_Order.chain (\<le>) ((\<lambda>f y. f (x, y)) ` Y)" for x using chain
    by(rule chain_imageI)(simp add: le_fun_def)
  have countable': "countable {y. (x, y) \<in> support_flow (Sup Y)}" for x
    using _ countable[THEN countable_image[where f=snd]]
    by(rule countable_subset)(auto intro: prod.expand rev_image_eqI)
  { fix x
    have "?lhs1 x = (\<Sum>\<^sup>+ y\<in>{y. (x, y) \<in> support_flow (Sup Y)}. SUP f\<in>Y. f (x, y))"
      by(subst d_OUT_alt_def2; simp)
    also have "\<dots> = (SUP f\<in>Y. \<Sum>\<^sup>+ y\<in>{y. (x, y) \<in> support_flow (Sup Y)}. f (x, y))" using Y
      by(rule nn_integral_monotone_convergence_SUP_countable)(auto simp add: chain' intro: countable')
    also have "\<dots> = ?rhs1 x" unfolding d_OUT_alt_def2
      by(auto 4 3 simp add: support_flow_Sup max_def nn_integral_count_space_indicator intro!: nn_integral_cong SUP_cong split: split_indicator dest: not_in_support_flowD)
    finally show "?OUT x" . }
  note out = this

  have chain'': "Complete_Partial_Order.chain (\<le>) ((\<lambda>f x. f (x, y)) ` Y)" for y using chain
    by(rule chain_imageI)(simp add: le_fun_def)
  have countable'': "countable {x. (x, y) \<in> support_flow (Sup Y)}" for y
    using _ countable[THEN countable_image[where f=fst]]
    by(rule countable_subset)(auto intro: prod.expand rev_image_eqI)
  have "?lhs2 = (\<Sum>\<^sup>+ x\<in>{x. (x, y) \<in> support_flow (Sup Y)}. SUP f\<in>Y. f (x, y))"
    by(subst d_IN_alt_def2; simp)
  also have "\<dots> = (SUP f\<in>Y. \<Sum>\<^sup>+ x\<in>{x. (x, y) \<in> support_flow (Sup Y)}. f (x, y))" using Y
    by(rule nn_integral_monotone_convergence_SUP_countable)(simp_all add: chain'' countable'')
  also have "\<dots> = ?rhs2" unfolding d_IN_alt_def2
    by(auto 4 3 simp add: support_flow_Sup max_def nn_integral_count_space_indicator intro!: nn_integral_cong SUP_cong split: split_indicator dest: not_in_support_flowD)
  finally show ?IN .

  show ?SINK by(rule set_eqI)(simp add: SINK.simps out Y bot_ennreal[symmetric])
qed

lemma
  assumes chain: "Complete_Partial_Order.chain (\<le>) Y"
  and Y: "Y \<noteq> {}"
  and countable: "countable (support_flow f)"
  and bounded: "\<And>g e. g \<in> Y \<Longrightarrow> g e \<le> f e"
  shows d_OUT_Inf: "d_OUT f x \<noteq> top \<Longrightarrow> d_OUT (Inf Y) x = (INF g\<in>Y. d_OUT g x)" (is "_ \<Longrightarrow> ?OUT" is "_ \<Longrightarrow> ?lhs1 = ?rhs1")
  and d_IN_Inf: "d_IN f x \<noteq> top \<Longrightarrow> d_IN (Inf Y) x = (INF g\<in>Y. d_IN g x)" (is "_ \<Longrightarrow> ?IN" is "_ \<Longrightarrow> ?lhs2 = ?rhs2")
proof -
  text \<open>We take a detour here via suprema because we have more theorems about @{const nn_integral}
    with suprema than with infinma.\<close>

  from Y obtain g0 where g0: "g0 \<in> Y" by auto
  have g0_le_f: "g0 e \<le> f e" for e by(rule bounded[OF g0])

  have "support_flow (SUP g\<in>Y. (\<lambda>e. f e - g e)) \<subseteq> support_flow f"
    by(clarsimp simp add: support_flow.simps less_SUP_iff elim!: less_le_trans intro!: diff_le_self_ennreal)
  then have countable': "countable (support_flow (SUP g\<in>Y. (\<lambda>e. f e - g e)))" by(rule countable_subset)(rule countable)

  have "Complete_Partial_Order.chain (\<ge>) Y" using chain by(simp add: chain_dual)
  hence chain': "Complete_Partial_Order.chain (\<le>) ((\<lambda>g e. f e - g e) ` Y)"
    by(rule chain_imageI)(auto simp add: le_fun_def intro: ennreal_minus_mono)

  { assume finite: "d_OUT f x \<noteq> top"
    have finite' [simp]: "f (x, y) \<noteq> \<top>" for y using finite
      by(rule neq_top_trans) (rule d_OUT_ge_point)

    have finite'_g: "g (x, y) \<noteq> \<top>" if "g \<in> Y" for g y using finite'[of y]
      by(rule neq_top_trans)(rule bounded[OF that])

    have finite1: "(\<Sum>\<^sup>+ y. f (x, y) - (INF g\<in>Y. g (x, y))) \<noteq> top"
      using finite by(rule neq_top_trans)(auto simp add: d_OUT_def intro!: nn_integral_mono)
    have finite2: "d_OUT g x \<noteq> top" if "g \<in> Y" for g using finite
      by(rule neq_top_trans)(auto intro: d_OUT_mono bounded[OF that])

    have bounded1: "(\<Sqinter>g\<in>Y. d_OUT g x) \<le> d_OUT f x"
      using Y by (blast intro: INF_lower2 d_OUT_mono bounded)

    have "?lhs1 = (\<Sum>\<^sup>+ y. INF g\<in>Y. g (x, y))" by(simp add: d_OUT_def)
    also have "\<dots> = d_OUT f x - (\<Sum>\<^sup>+ y. f (x, y) - (INF g\<in>Y. g (x, y)))" unfolding d_OUT_def
      using finite1 g0_le_f
      apply(subst nn_integral_diff[symmetric])
      apply(auto simp add: AE_count_space intro!: diff_le_self_ennreal INF_lower2[OF g0] nn_integral_cong diff_diff_ennreal[symmetric])
      done
    also have "(\<Sum>\<^sup>+ y. f (x, y) - (INF g\<in>Y. g (x, y))) = d_OUT (\<lambda>e. SUP g\<in>Y. f e - g e) x"
      unfolding d_OUT_def by(subst SUP_const_minus_ennreal)(simp_all add: Y)
    also have "\<dots> = (SUP h\<in>(\<lambda>g e. f e - g e) ` Y. d_OUT h x)" using countable' chain' Y
      by(subst d_OUT_Sup[symmetric])(simp_all add: SUP_apply[abs_def])
    also have "\<dots> = (SUP g\<in>Y. d_OUT (\<lambda>e. f e - g e) x)" unfolding image_image ..
    also have "\<dots> = (SUP g\<in>Y. d_OUT f x - d_OUT g x)"
      by(rule SUP_cong[OF refl] d_OUT_diff)+(auto intro: bounded simp add: finite2)
    also have "\<dots> = d_OUT f x - ?rhs1" by(subst SUP_const_minus_ennreal)(simp_all add: Y)
    also have "d_OUT f x - \<dots> = ?rhs1"
      using Y by(subst diff_diff_ennreal)(simp_all add: bounded1 finite)
    finally show ?OUT .
  next
    assume finite: "d_IN f x \<noteq> top"
    have finite' [simp]: "f (y, x) \<noteq> \<top>" for y using finite
      by(rule neq_top_trans) (rule d_IN_ge_point)

    have finite'_g: "g (y, x) \<noteq> \<top>" if "g \<in> Y" for g y using finite'[of y]
      by(rule neq_top_trans)(rule bounded[OF that])

    have finite1: "(\<Sum>\<^sup>+ y. f (y, x) - (INF g\<in>Y. g (y, x))) \<noteq> top"
      using finite by(rule neq_top_trans)(auto simp add: d_IN_def diff_le_self_ennreal intro!: nn_integral_mono)
    have finite2: "d_IN g x \<noteq> top" if "g \<in> Y" for g using finite
      by(rule neq_top_trans)(auto intro: d_IN_mono bounded[OF that])

    have bounded1: "(\<Sqinter>g\<in>Y. d_IN g x) \<le> d_IN f x"
      using Y by (blast intro: INF_lower2 d_IN_mono bounded)

    have "?lhs2 = (\<Sum>\<^sup>+ y. INF g\<in>Y. g (y, x))" by(simp add: d_IN_def)
    also have "\<dots> = d_IN f x - (\<Sum>\<^sup>+ y. f (y, x) - (INF g\<in>Y. g (y, x)))" unfolding d_IN_def
      using finite1 g0_le_f
      apply(subst nn_integral_diff[symmetric])
      apply(auto simp add: AE_count_space intro!: diff_le_self_ennreal INF_lower2[OF g0] nn_integral_cong diff_diff_ennreal[symmetric])
      done
    also have "(\<Sum>\<^sup>+ y. f (y, x) - (INF g\<in>Y. g (y, x))) = d_IN (\<lambda>e. SUP g\<in>Y. f e - g e) x"
      unfolding d_IN_def by(subst SUP_const_minus_ennreal)(simp_all add: Y)
    also have "\<dots> = (SUP h\<in>(\<lambda>g e. f e - g e) ` Y. d_IN h x)" using countable' chain' Y
      by(subst d_IN_Sup[symmetric])(simp_all add: SUP_apply[abs_def])
    also have "\<dots> = (SUP g\<in>Y. d_IN (\<lambda>e. f e - g e) x)" unfolding image_image ..
    also have "\<dots> = (SUP g\<in>Y. d_IN f x - d_IN g x)"
      by(rule SUP_cong[OF refl] d_IN_diff)+(auto intro: bounded simp add: finite2)
    also have "\<dots> = d_IN f x - ?rhs2" by(subst SUP_const_minus_ennreal)(simp_all add: Y)
    also have "d_IN f x - \<dots> = ?rhs2"
      by(subst diff_diff_ennreal)(simp_all add: finite bounded1)
    finally show ?IN . }
qed

inductive flow :: "('v, 'more) network_scheme \<Rightarrow> 'v flow \<Rightarrow> bool"
  for \<Delta> (structure) and f
where
  flow: "\<lbrakk> \<And>e. f e \<le> capacity \<Delta> e;
     \<And>x. \<lbrakk> x \<noteq> source \<Delta>; x \<noteq> sink \<Delta> \<rbrakk> \<Longrightarrow> KIR f x \<rbrakk>
  \<Longrightarrow> flow \<Delta> f"

lemma flowD_capacity: "flow \<Delta> f \<Longrightarrow> f e \<le> capacity \<Delta> e"
by(cases e)(simp add: flow.simps)

lemma flowD_KIR: "\<lbrakk> flow \<Delta> f; x \<noteq> source \<Delta>; x \<noteq> sink \<Delta> \<rbrakk> \<Longrightarrow> KIR f x"
by(simp add: flow.simps)

lemma flowD_capacity_OUT: "flow \<Delta> f \<Longrightarrow> d_OUT f x \<le> d_OUT (capacity \<Delta>) x"
by(rule d_OUT_mono)(erule flowD_capacity)

lemma flowD_capacity_IN: "flow \<Delta> f \<Longrightarrow> d_IN f x \<le> d_IN (capacity \<Delta>) x"
by(rule d_IN_mono)(erule flowD_capacity)

abbreviation value_flow :: "('v, 'more) network_scheme \<Rightarrow> ('v edge \<Rightarrow> ennreal) \<Rightarrow> ennreal"
where "value_flow \<Delta> f \<equiv> d_OUT f (source \<Delta>)"

subsection \<open>Cut\<close>

type_synonym 'v cut = "'v set"

inductive cut :: "('v, 'more) network_scheme \<Rightarrow> 'v cut \<Rightarrow> bool"
  for \<Delta> and S
where cut: "\<lbrakk> source \<Delta> \<in> S; sink \<Delta> \<notin> S \<rbrakk> \<Longrightarrow> cut \<Delta> S"

inductive orthogonal :: "('v, 'more) network_scheme \<Rightarrow> 'v flow \<Rightarrow> 'v cut \<Rightarrow> bool"
  for \<Delta> f S
where
  "\<lbrakk> \<And>x y. \<lbrakk> edge \<Delta> x y; x \<in> S; y \<notin> S \<rbrakk> \<Longrightarrow> f (x, y) = capacity \<Delta> (x, y);
     \<And>x y. \<lbrakk> edge \<Delta> x y; x \<notin> S; y \<in> S \<rbrakk> \<Longrightarrow> f (x, y) = 0 \<rbrakk>
  \<Longrightarrow> orthogonal \<Delta> f S"

lemma orthogonalD_out:
  "\<lbrakk> orthogonal \<Delta> f S; edge \<Delta> x y; x \<in> S; y \<notin> S \<rbrakk> \<Longrightarrow> f (x, y) = capacity \<Delta> (x, y)"
by(simp add: orthogonal.simps)

lemma orthogonalD_in:
  "\<lbrakk> orthogonal \<Delta> f S; edge \<Delta> x y; x \<notin> S; y \<in> S \<rbrakk> \<Longrightarrow> f (x, y) = 0"
by(simp add: orthogonal.simps)



section \<open>Countable network\<close>

locale countable_network =
  fixes \<Delta> :: "('v, 'more) network_scheme" (structure)
  assumes countable_E [simp]: "countable \<^bold>E"
  and source_neq_sink [simp]: "source \<Delta> \<noteq> sink \<Delta>"
  and capacity_outside: "e \<notin> \<^bold>E \<Longrightarrow> capacity \<Delta> e = 0"
  and capacity_finite [simp]: "capacity \<Delta> e \<noteq> \<top>"
begin

lemma sink_neq_source [simp]: "sink \<Delta> \<noteq> source \<Delta>"
using source_neq_sink[symmetric] .

lemma countable_V [simp]: "countable \<^bold>V"
unfolding "\<^bold>V_def" using countable_E by auto

lemma flowD_outside:
  assumes g: "flow \<Delta> g"
  shows "e \<notin> \<^bold>E \<Longrightarrow> g e = 0"
using flowD_capacity[OF g, of e] capacity_outside[of e] by simp

lemma flowD_finite:
  assumes "flow \<Delta> g"
  shows "g e \<noteq> \<top>"
using flowD_capacity[OF assms, of e] by (auto simp: top_unique)

lemma zero_flow [simp]: "flow \<Delta> (\<lambda>_. 0)"
by(rule flow.intros) simp_all

end

section \<open>Attainability of flows in networks\<close>

subsection \<open>Cleaning up flows\<close>

text \<open>If there is a flow along antiparallel edges, it suffices to consider the difference.\<close>

definition cleanup :: "'a flow \<Rightarrow> 'a flow"
where "cleanup f = (\<lambda>(a, b). if f (a, b) > f (b, a) then f (a, b) - f (b, a) else 0)"

lemma cleanup_simps [simp]:
  "cleanup f (a, b) = (if f (a, b) > f (b, a) then f (a, b) - f (b, a) else 0)"
by(simp add: cleanup_def)

lemma value_flow_cleanup:
  assumes [simp]: "\<And>x. f (x, source \<Delta>) = 0"
  shows "value_flow \<Delta> (cleanup f) = value_flow \<Delta> f"
unfolding d_OUT_def
by (auto simp add: not_less intro!: nn_integral_cong intro: antisym)

lemma KIR_cleanup:
  assumes KIR: "KIR f x"
  and finite_IN: "d_IN f x \<noteq> \<top>"
  shows "KIR (cleanup f) x"
proof -
  from finite_IN KIR have finite_OUT: "d_OUT f x \<noteq> \<top>" by simp

  have finite_IN: "(\<Sum>\<^sup>+ y\<in>A. f (y, x)) \<noteq> \<top>" for A
    using finite_IN by(rule neq_top_trans)(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
  have finite_OUT: "(\<Sum>\<^sup>+ y\<in>A. f (x, y)) \<noteq> \<top>" for A
    using finite_OUT by(rule neq_top_trans)(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
  have finite_in: "f (x, y) \<noteq> \<top>" for y using \<open>d_OUT f x \<noteq> \<top>\<close>
    by(rule neq_top_trans) (rule d_OUT_ge_point)

  let ?M = "{y. f (x, y) > f (y, x)}"

  have "d_OUT (cleanup f) x = (\<Sum>\<^sup>+ y\<in>?M. f (x, y) - f (y, x))"
    by(auto simp add: d_OUT_def nn_integral_count_space_indicator intro!: nn_integral_cong)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>?M. f (x, y)) - (\<Sum>\<^sup>+ y\<in>?M. f (y, x))" using finite_IN
    by(subst nn_integral_diff)(auto simp add: AE_count_space)
  also have "\<dots> = (d_OUT f x - (\<Sum>\<^sup>+ y\<in>{y. f (x, y) \<le> f (y, x)}. f (x, y))) - (\<Sum>\<^sup>+ y\<in>?M. f (y, x))"
    unfolding d_OUT_def d_IN_def using finite_IN finite_OUT
    apply(simp add: nn_integral_count_space_indicator)
    apply(subst (2) nn_integral_diff[symmetric])
    apply(auto simp add: AE_count_space finite_in split: split_indicator intro!: arg_cong2[where f="(-)"] intro!: nn_integral_cong)
    done
  also have "\<dots> = (d_IN f x - (\<Sum>\<^sup>+ y\<in>?M. f (y, x))) - (\<Sum>\<^sup>+ y\<in>{y. f (x, y) \<le> f (y, x)}. f (x, y))"
    using KIR by(simp add: diff_diff_commute_ennreal)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>{y. f (x, y) \<le> f (y, x)}. f (y, x)) - (\<Sum>\<^sup>+ y\<in>{y. f (x, y) \<le> f (y, x)}. f (x, y))"
    using finite_IN finite_IN[of "{ _ }"]
    apply(simp add: d_IN_def nn_integral_count_space_indicator)
    apply(subst nn_integral_diff[symmetric])
    apply(auto simp add: d_IN_def AE_count_space split: split_indicator intro!: arg_cong2[where f="(-)"] intro!: nn_integral_cong)
    done
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>{y. f (x, y) \<le> f (y, x)}. f (y, x) - f (x, y))" using finite_OUT
    by(subst nn_integral_diff)(auto simp add: AE_count_space)
  also have "\<dots> = d_IN (cleanup f) x" using finite_in
    by(auto simp add: d_IN_def nn_integral_count_space_indicator intro!: ennreal_diff_self nn_integral_cong split: split_indicator)
  finally show "KIR (cleanup f) x" .
qed

locale flow_attainability = countable_network \<Delta>
  for \<Delta> :: "('v, 'more) network_scheme" (structure)
  +
  assumes finite_capacity: "\<And>x. x \<noteq> sink \<Delta> \<Longrightarrow> d_IN (capacity \<Delta>) x \<noteq> \<top> \<or> d_OUT (capacity \<Delta>) x \<noteq> \<top>"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  and source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
begin

lemma source_in_not_cycle:
  assumes "cycle \<Delta> p"
  shows "(x, source \<Delta>) \<notin> set (cycle_edges p)"
using cycle_edges_edges[OF assms] source_in[of x] by(auto)

lemma source_out_not_cycle:
  "cycle \<Delta> p \<Longrightarrow> (source \<Delta>, x) \<notin> set (cycle_edges p)"
by(auto dest: cycle_leave_ex_enter source_in_not_cycle)

lemma flowD_source_IN:
  assumes "flow \<Delta> f"
  shows "d_IN f (source \<Delta>) = 0"
proof -
  have "d_IN f (source \<Delta>) = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N (source \<Delta>). f (y, source \<Delta>))"
    by(rule d_IN_alt_def)(simp add: flowD_outside[OF assms])
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N (source \<Delta>). 0)"
    by(rule nn_integral_cong)(simp add: source_in incoming_def)
  finally show ?thesis by simp
qed

lemma flowD_finite_IN:
  assumes f: "flow \<Delta> f" and x: "x \<noteq> sink \<Delta>"
  shows "d_IN f x \<noteq> top"
proof(cases "x = source \<Delta>")
  case True thus ?thesis by(simp add: flowD_source_IN[OF f])
next
  case False
  from finite_capacity[OF x] show ?thesis
  proof
    assume *: "d_IN (capacity \<Delta>) x \<noteq> \<top>"
    from flowD_capacity[OF f] have "d_IN f x \<le> d_IN (capacity \<Delta>) x" by(rule d_IN_mono)
    also have "\<dots> < \<top>" using * by (simp add: less_top)
    finally show ?thesis by simp
  next
    assume *: "d_OUT (capacity \<Delta>) x \<noteq> \<top>"
    have "d_IN f x = d_OUT f x" using flowD_KIR[OF f False x] by simp
    also have "\<dots> \<le> d_OUT (capacity \<Delta>) x" using flowD_capacity[OF f] by(rule d_OUT_mono)
    also have "\<dots> < \<top>" using * by (simp add: less_top)
    finally show ?thesis by simp
  qed
qed

lemma flowD_finite_OUT:
  assumes "flow \<Delta> f" "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  shows "d_OUT f x \<noteq> \<top>"
using flowD_KIR[OF assms] assms by(simp add: flowD_finite_IN)

end

locale flow_network = flow_attainability
  +
  fixes g :: "'v flow"
  assumes g: "flow \<Delta> g"
  and g_finite: "value_flow \<Delta> g \<noteq> \<top>"
  and nontrivial: "\<^bold>V - {source \<Delta>, sink \<Delta>} \<noteq> {}"
begin

lemma g_outside: "e \<notin> \<^bold>E \<Longrightarrow> g e = 0"
by(rule flowD_outside)(rule g)

lemma g_loop [simp]: "g (x, x) = 0"
by(rule g_outside)(simp add: no_loop)

lemma finite_IN_g: "x \<noteq> sink \<Delta> \<Longrightarrow> d_IN g x \<noteq> top"
by(rule flowD_finite_IN[OF g])

lemma finite_OUT_g:
  assumes "x \<noteq> sink \<Delta>"
  shows "d_OUT g x \<noteq> top"
proof(cases "x = source \<Delta>")
  case True
  with g_finite show ?thesis by simp
next
  case False
  with g have "KIR g x" using assms by(auto dest: flowD_KIR)
  with finite_IN_g[of x] False assms show ?thesis by(simp)
qed

lemma g_source_in [simp]: "g (x, source \<Delta>) = 0"
by(rule g_outside)(simp add: source_in)

lemma finite_g [simp]: "g e \<noteq> top"
  by(rule flowD_finite[OF g])


definition enum_v :: "nat \<Rightarrow> 'v"
where "enum_v n = from_nat_into (\<^bold>V - {source \<Delta>, sink \<Delta>}) (fst (prod_decode n))"

lemma range_enum_v: "range enum_v \<subseteq> \<^bold>V - {source \<Delta>, sink \<Delta>}"
using from_nat_into[OF nontrivial] by(auto simp add: enum_v_def)

lemma enum_v_repeat:
  assumes x: "x \<in> \<^bold>V" "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  shows "\<exists>i'>i. enum_v i' = x"
proof -
  let ?V = "\<^bold>V - {source \<Delta>, sink \<Delta>}"
  let ?n = "to_nat_on ?V x"
  let ?A = "{?n} \<times> (UNIV :: nat set)"
  from x have x': "x \<in> \<^bold>V - {source \<Delta>, sink \<Delta>}" by simp
  have "infinite ?A" by(auto dest: finite_cartesian_productD2)
  hence "infinite (prod_encode ` ?A)" by(auto dest: finite_imageD simp add: inj_prod_encode)
  then obtain i' where "i' > i" "i' \<in> prod_encode ` ?A"
    unfolding infinite_nat_iff_unbounded by blast
  from this(2) have "enum_v i' = x" using x by(clarsimp simp add: enum_v_def)
  with \<open>i' > i\<close> show ?thesis by blast
qed

fun h_plus :: "nat \<Rightarrow> 'v edge \<Rightarrow> ennreal"
where
  "h_plus 0 (x, y) = (if x = source \<Delta> then g (x, y) else 0)"
| "h_plus (Suc i) (x, y) =
  (if enum_v (Suc i) = x \<and> d_OUT (h_plus i) x < d_IN (h_plus i) x then
   let total = d_IN (h_plus i) x - d_OUT (h_plus i) x;
       share = g (x, y) - h_plus i (x, y);
       shares = d_OUT g x - d_OUT (h_plus i) x
   in h_plus i (x, y) + share * total / shares
   else h_plus i (x, y))"


lemma h_plus_le_g: "h_plus i e \<le> g e"
proof(induction i arbitrary: e and e)
  case 0 thus ?case by(cases e) simp
next
  case (Suc i)
  { fix x y
    assume enum: "x = enum_v (Suc i)"
    assume less: "d_OUT (h_plus i) x < d_IN (h_plus i) x"
    from enum have x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" using range_enum_v
      by(auto dest: sym intro: rev_image_eqI)

    define share where "share = g (x, y) - h_plus i (x, y)"
    define shares where "shares = d_OUT g x - d_OUT (h_plus i) x"
    define total where "total = d_IN (h_plus i) x - d_OUT (h_plus i) x"
    let ?h = "h_plus i (x, y) + share * total / shares"

    have "d_OUT (h_plus i) x \<le> d_OUT g x" by(rule d_OUT_mono)(rule Suc.IH)
    also have "\<dots> < top" using finite_OUT_g[of x] x by (simp add: less_top)
    finally have "d_OUT (h_plus i) x \<noteq> \<top>" by simp
    then have shares_eq: "shares = (\<Sum>\<^sup>+ y. g (x, y) - h_plus i (x, y))" unfolding shares_def d_OUT_def
      by(subst nn_integral_diff)(simp_all add: AE_count_space Suc.IH)

    have *: "share / shares \<le> 1"
    proof (cases "share = 0")
      case True thus ?thesis by(simp)
    next
      case False
      hence "share > 0" using \<open>h_plus i (x, y) \<le> g _\<close>
        by(simp add: share_def dual_order.strict_iff_order)
      moreover have "share \<le> shares" unfolding share_def shares_eq by(rule nn_integral_ge_point)simp
      ultimately show ?thesis by(simp add: divide_le_posI_ennreal)
    qed

    note shares_def
    also have "d_OUT g x = d_IN g x" by(rule flowD_KIR[OF g x])
    also have "d_IN (h_plus i) x \<le> d_IN g x" by(rule d_IN_mono)(rule Suc.IH)
    ultimately have *: "total \<le> shares" unfolding total_def by(simp add: ennreal_minus_mono)
    moreover have "total > 0" unfolding total_def using less by (clarsimp simp add: diff_gr0_ennreal)
    ultimately have "total / shares \<le> 1" by(intro divide_le_posI_ennreal)(simp_all)
    hence "share * (total / shares) \<le> share * 1"
      by(rule mult_left_mono) simp
    hence "?h \<le> h_plus i (x, y) + share" by(simp add: ennreal_times_divide add_mono)
    also have "\<dots> = g (x, y)" unfolding share_def using \<open>h_plus i (x, y) \<le> g _\<close> finite_g[of "(x, y)"]
      by simp
    moreover
    note calculation }
  note * = this
  show ?case using Suc.IH * by(cases e) clarsimp
qed

lemma h_plus_outside: "e \<notin> \<^bold>E \<Longrightarrow> h_plus i e = 0"
by (metis g_outside h_plus_le_g le_zero_eq)

lemma h_plus_not_infty [simp]: "h_plus i e \<noteq> top"
using h_plus_le_g[of i e] by (auto simp: top_unique)

lemma h_plus_mono: "h_plus i e \<le> h_plus (Suc i) e"
proof(cases e)
  case [simp]: (Pair x y)
  { assume "d_OUT (h_plus i) x < d_IN (h_plus i) x"
    hence "h_plus i (x, y) + 0 \<le> h_plus i (x, y) + (g (x, y) - h_plus i (x, y)) * (d_IN (h_plus i) x - d_OUT (h_plus i) x) / (d_OUT g x - d_OUT (h_plus i) x)"
      by(intro add_left_mono d_OUT_mono le_funI) (simp_all add: h_plus_le_g) }
  then show ?thesis by clarsimp
qed

lemma h_plus_mono': "i \<le> j \<Longrightarrow> h_plus i e \<le> h_plus j e"
by(induction rule: dec_induct)(auto intro: h_plus_mono order_trans)

lemma d_OUT_h_plus_not_infty': "x \<noteq> sink \<Delta> \<Longrightarrow> d_OUT (h_plus i) x \<noteq> top"
using d_OUT_mono[of "h_plus i" x g, OF h_plus_le_g] finite_OUT_g[of x] by (auto simp: top_unique)

lemma h_plus_OUT_le_IN:
  assumes "x \<noteq> source \<Delta>"
  shows "d_OUT (h_plus i) x \<le> d_IN (h_plus i) x"
proof(induction i)
  case 0
  thus ?case using assms by(simp add: d_OUT_def)
next
  case (Suc i)
  have "d_OUT (h_plus (Suc i)) x \<le> d_IN (h_plus i) x"
  proof(cases "enum_v (Suc i) = x \<and> d_OUT (h_plus i) x < d_IN (h_plus i) x")
    case False
    thus ?thesis using Suc.IH by(simp add: d_OUT_def cong: conj_cong)
  next
    case True
    hence x: "x \<noteq> sink \<Delta>" and le: "d_OUT (h_plus i) x < d_IN (h_plus i) x" using range_enum_v by auto
    let ?r = "\<lambda>y. (g (x, y) - h_plus i (x, y)) * (d_IN (h_plus i) x - d_OUT (h_plus i) x) / (d_OUT g x - d_OUT (h_plus i) x)"
    have "d_OUT (h_plus (Suc i)) x = d_OUT (h_plus i) x + (\<Sum>\<^sup>+ y. ?r y)"
      using True unfolding d_OUT_def h_plus.simps by(simp add: AE_count_space nn_integral_add)
    also from True have "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" using range_enum_v by auto
    from flowD_KIR[OF g this] le d_IN_mono[of "h_plus i" x g, OF h_plus_le_g]
    have le': "d_OUT (h_plus i) x < d_OUT g x" by(simp)
    then have "(\<Sum>\<^sup>+ y. ?r y) =
      (d_IN (h_plus i) x - d_OUT (h_plus i) x) * ((\<Sum>\<^sup>+ y. g (x, y) - h_plus i (x, y)) / (d_OUT g x - d_OUT (h_plus i) x))"
      by(subst mult.commute, subst ennreal_times_divide[symmetric])
        (simp add: nn_integral_cmult nn_integral_divide Suc.IH diff_gr0_ennreal)
    also have "(\<Sum>\<^sup>+ y. g (x, y) - h_plus i (x, y)) = d_OUT g x - d_OUT (h_plus i) x" using x
      by(subst nn_integral_diff)(simp_all add: d_OUT_def[symmetric] h_plus_le_g d_OUT_h_plus_not_infty')
    also have "\<dots> / \<dots> = 1" using le' finite_OUT_g[of x] x
      by(auto intro!: ennreal_divide_self dest: diff_gr0_ennreal simp: less_top[symmetric])
    also have "d_OUT (h_plus i) x + (d_IN (h_plus i) x - d_OUT (h_plus i) x) * 1 = d_IN (h_plus i) x" using x
      by (simp add: Suc)
    finally show ?thesis by simp
  qed
  also have "\<dots> \<le> d_IN (h_plus (Suc i)) x" by(rule d_IN_mono)(rule h_plus_mono)
  finally show ?case .
qed

lemma h_plus_OUT_eq_IN:
  assumes enum: "enum_v (Suc i) = x"
  shows "d_OUT (h_plus (Suc i)) x = d_IN (h_plus i) x"
proof(cases "d_OUT (h_plus i) x < d_IN (h_plus i) x")
  case False
  from enum have "x \<noteq> source \<Delta>" using range_enum_v by auto
  from h_plus_OUT_le_IN[OF this, of i] False have "d_OUT (h_plus i) x = d_IN (h_plus i) x" by auto
  with False enum show ?thesis by(simp add: d_OUT_def)
next
  case True
  from enum have x: "x \<noteq> source \<Delta>" and sink: "x \<noteq> sink \<Delta>" using range_enum_v by auto
  let ?r = "\<lambda>y. (g (x, y) - h_plus i (x, y)) * (d_IN (h_plus i) x - d_OUT (h_plus i) x) / (d_OUT g x - d_OUT (h_plus i) x)"
  have "d_OUT (h_plus (Suc i)) x = d_OUT (h_plus i) x + (\<Sum>\<^sup>+ y. ?r y)"
    using True enum unfolding d_OUT_def h_plus.simps by(simp add: AE_count_space nn_integral_add)
  also from True enum have "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" using range_enum_v by auto
  from flowD_KIR[OF g this] True d_IN_mono[of "h_plus i" x g, OF h_plus_le_g]
  have le': "d_OUT (h_plus i) x < d_OUT g x" by(simp)
  then have "(\<Sum>\<^sup>+ y. ?r y ) =
    (d_IN (h_plus i) x - d_OUT (h_plus i) x) * ((\<Sum>\<^sup>+ y. g (x, y) - h_plus i (x, y)) / (d_OUT g x - d_OUT (h_plus i) x))"
    by(subst mult.commute, subst ennreal_times_divide[symmetric])
      (simp add: nn_integral_cmult nn_integral_divide h_plus_OUT_le_IN[OF x] diff_gr0_ennreal)
  also have "(\<Sum>\<^sup>+ y. g (x, y) - h_plus i (x, y)) = d_OUT g x - d_OUT (h_plus i) x" using sink
    by(subst nn_integral_diff)(simp_all add: d_OUT_def[symmetric] h_plus_le_g d_OUT_h_plus_not_infty')
  also have "\<dots> / \<dots> = 1" using le' finite_OUT_g[of x] sink
    by(auto intro!: ennreal_divide_self dest: diff_gr0_ennreal simp: less_top[symmetric])
  also have "d_OUT (h_plus i) x + (d_IN (h_plus i) x - d_OUT (h_plus i) x) * 1 = d_IN (h_plus i) x" using sink
    by (simp add: h_plus_OUT_le_IN x)
  finally show ?thesis .
qed

lemma h_plus_source_in [simp]: "h_plus i (x, source \<Delta>) = 0"
by(induction i)simp_all

lemma h_plus_sum_finite: "(\<Sum>\<^sup>+ e. h_plus i e) \<noteq> top"
proof(induction i)
  case 0
  have "(\<Sum>\<^sup>+ e\<in>UNIV. h_plus 0 e) = (\<Sum>\<^sup>+ (x, y). h_plus 0 (x, y))"
    by(simp del: h_plus.simps)
  also have "\<dots> = (\<Sum>\<^sup>+ (x, y)\<in>range (Pair (source \<Delta>)). h_plus 0 (x, y))"
    by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_cong)
  also have "\<dots> = value_flow \<Delta> g" by(simp add: d_OUT_def nn_integral_count_space_reindex)
  also have "\<dots> < \<top>" using g_finite by (simp add: less_top)
  finally show ?case by simp
next
  case (Suc i)
  define xi where "xi = enum_v (Suc i)"
  then have xi: "xi \<noteq> source \<Delta>" "xi \<noteq> sink \<Delta>" using range_enum_v by auto
  show ?case
  proof(cases "d_OUT (h_plus i) xi < d_IN (h_plus i) xi")
    case False
    hence "(\<Sum>\<^sup>+ e\<in>UNIV. h_plus (Suc i) e) = (\<Sum>\<^sup>+ e. h_plus i e)"
      by(auto intro!: nn_integral_cong simp add: xi_def)
    with Suc.IH show ?thesis by simp
  next
    case True
    have less: "d_OUT (h_plus i) xi < d_OUT g xi"
      using True flowD_KIR[OF g xi] d_IN_mono[of "h_plus i" xi, OF h_plus_le_g]
      by simp

    have "(\<Sum>\<^sup>+ e. h_plus (Suc i) e) =
      (\<Sum>\<^sup>+ e\<in>UNIV. h_plus i e) + (\<Sum>\<^sup>+ (x, y). ((g (x, y) - h_plus i (x, y)) * (d_IN (h_plus i) x - d_OUT (h_plus i) x) / (d_OUT g x - d_OUT (h_plus i) x)) * indicator (range (Pair xi)) (x, y))"
      (is "_ = ?IH + ?rest" is "_ = _ + \<integral>\<^sup>+ (x, y). ?f x y * _ \<partial>_") using xi True
      by(subst nn_integral_add[symmetric])(auto simp add: xi_def split_beta AE_count_space intro!: nn_integral_cong split: split_indicator intro!: h_plus_le_g h_plus_OUT_le_IN d_OUT_mono le_funI)
    also have "?rest = (\<Sum>\<^sup>+ (x, y)\<in>range (Pair xi). ?f x y)"
      by(simp add: nn_integral_count_space_indicator split_def)
    also have "\<dots> = (\<Sum>\<^sup>+ y. ?f xi y)" by(simp add: nn_integral_count_space_reindex)
    also have "\<dots> = (\<Sum>\<^sup>+ y. g (xi, y) - h_plus i (xi, y)) * ((d_IN (h_plus i) xi - d_OUT (h_plus i) xi) / (d_OUT g xi - d_OUT (h_plus i) xi))"
      (is "_ = ?integral * ?factor")  using True less
      by(simp add: nn_integral_multc nn_integral_divide diff_gr0_ennreal ennreal_times_divide)
    also have "?integral = d_OUT g xi - d_OUT (h_plus i) xi" unfolding d_OUT_def using xi
      by(subst nn_integral_diff)(simp_all add: h_plus_le_g d_OUT_def[symmetric] d_OUT_h_plus_not_infty')
    also have "\<dots> * ?factor = (d_IN (h_plus i) xi - d_OUT (h_plus i) xi)" using xi
      apply (subst ennreal_times_divide)
      apply (subst mult.commute)
      apply (subst ennreal_mult_divide_eq)
      apply (simp_all add: diff_gr0_ennreal finite_OUT_g less zero_less_iff_neq_zero[symmetric])
      done
    also have "\<dots> \<noteq> \<top>" using h_plus_OUT_eq_IN[OF refl, of i, folded xi_def, symmetric] xi
      by(simp add: d_OUT_h_plus_not_infty')
    ultimately show ?thesis using Suc.IH by simp
  qed
qed

lemma d_OUT_h_plus_not_infty [simp]: "d_OUT (h_plus i) x \<noteq> top"
proof -
  have "d_OUT (h_plus i) x \<le> (\<Sum>\<^sup>+ y\<in>UNIV. \<Sum>\<^sup>+ x. h_plus i (x, y))"
    unfolding d_OUT_def by(rule nn_integral_mono nn_integral_ge_point)+ simp
  also have "\<dots> < \<top>" using h_plus_sum_finite by(simp add: nn_integral_snd_count_space less_top)
  finally show ?thesis by simp
qed

definition enum_cycle :: "nat \<Rightarrow> 'v path"
where "enum_cycle = from_nat_into (cycles \<Delta>)"

lemma cycle_enum_cycle [simp]: "cycles \<Delta> \<noteq> {} \<Longrightarrow> cycle \<Delta> (enum_cycle n)"
unfolding enum_cycle_def using from_nat_into[of "cycles \<Delta>" n] by simp

context
  fixes h' :: "'v flow"
  assumes finite_h': "h' e \<noteq> top"
begin

fun h_minus_aux :: "nat \<Rightarrow> 'v edge \<Rightarrow> ennreal"
where
  "h_minus_aux 0 e = 0"
| "h_minus_aux (Suc j) e =
  (if e \<in> set (cycle_edges (enum_cycle j)) then
     h_minus_aux j e + Min {h' e' - h_minus_aux j e'|e'. e'\<in>set (cycle_edges (enum_cycle j))}
   else h_minus_aux j e)"

lemma h_minus_aux_le_h': "h_minus_aux j e \<le> h' e"
proof(induction j e rule: h_minus_aux.induct)
  case 0: (1 e) show ?case by simp
next
  case Suc: (2 j e)
  { assume e: "e \<in> set (cycle_edges (enum_cycle j))"
    then have "h_minus_aux j e + Min {h' e' - h_minus_aux j e' |e'. e' \<in> set (cycle_edges (enum_cycle j))} \<le>
      h_minus_aux j e + (h' e - h_minus_aux j e)"
      using [[simproc add: finite_Collect]] by(cases e rule: prod.exhaust)(auto intro!: add_mono Min_le)
    also have "\<dots> = h' e" using e finite_h'[of e] Suc.IH(2)[of e]
      by(cases e rule: prod.exhaust)
        (auto simp add: add_diff_eq_ennreal top_unique intro!: ennreal_add_diff_cancel_left)
    also note calculation }
  then show ?case using Suc by clarsimp
qed

lemma h_minus_aux_finite [simp]: "h_minus_aux j e \<noteq> top"
using h_minus_aux_le_h'[of j e] finite_h'[of e] by (auto simp: top_unique)

lemma h_minus_aux_mono: "h_minus_aux j e \<le> h_minus_aux (Suc j) e"
proof(cases "e \<in> set (cycle_edges (enum_cycle j)) = True")
  case True
  have "h_minus_aux j e + 0 \<le> h_minus_aux (Suc j) e" unfolding h_minus_aux.simps True if_True
    using True [[simproc add: finite_Collect]]
    by(cases e)(rule add_mono, auto intro!: Min.boundedI simp add: h_minus_aux_le_h')
  thus ?thesis by simp
qed simp

lemma d_OUT_h_minus_aux:
  assumes "cycles \<Delta> \<noteq> {}"
  shows "d_OUT (h_minus_aux j) x = d_IN (h_minus_aux j) x"
proof(induction j)
  case 0 show ?case by simp
next
  case (Suc j)
  define C where "C = enum_cycle j"
  define \<delta> where "\<delta> = Min {h' e' - h_minus_aux j e' |e'. e' \<in> set (cycle_edges C)}"

  have "d_OUT (h_minus_aux (Suc j)) x =
    (\<Sum>\<^sup>+ y. h_minus_aux j (x, y) + (if (x, y) \<in> set (cycle_edges C) then \<delta> else 0))"
    unfolding d_OUT_def by(simp add: if_distrib C_def \<delta>_def cong del: if_weak_cong)
  also have "\<dots> = d_OUT (h_minus_aux j) x + (\<Sum>\<^sup>+ y. \<delta> * indicator (set (cycle_edges C)) (x, y))"
    (is "_ = _ + ?add")
    by(subst nn_integral_add)(auto simp add: AE_count_space d_OUT_def intro!: arg_cong2[where f="(+)"] nn_integral_cong)
  also have "?add = (\<Sum>\<^sup>+ e\<in>range (Pair x). \<delta> * indicator {(x', y). (x', y) \<in> set (cycle_edges C) \<and> x' = x} e)"
    by(auto simp add: nn_integral_count_space_reindex intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = \<delta> * card (set (filter (\<lambda>(x', y). x' = x) (cycle_edges C)))"
    using [[simproc add: finite_Collect]]
    apply(subst nn_integral_cmult_indicator; auto)
    apply(subst emeasure_count_space; auto simp add: split_def)
    done
  also have "card (set (filter (\<lambda>(x', y). x' = x) (cycle_edges C))) = card (set (filter (\<lambda>(x', y). y = x) (cycle_edges C)))"
    unfolding C_def by(rule cycle_enter_leave_same)(rule cycle_enum_cycle[OF assms])
  also have "\<delta> * \<dots> =  (\<Sum>\<^sup>+ e\<in>range (\<lambda>x'. (x', x)). \<delta> * indicator {(x', y). (x', y) \<in> set (cycle_edges C) \<and> y = x} e)"
    using [[simproc add: finite_Collect]]
    apply(subst nn_integral_cmult_indicator; auto)
    apply(subst emeasure_count_space; auto simp add: split_def)
    done
  also have "\<dots> = (\<Sum>\<^sup>+ x'. \<delta> * indicator (set (cycle_edges C)) (x', x))"
    by(auto simp add: nn_integral_count_space_reindex intro!: nn_integral_cong split: split_indicator)
  also have "d_OUT (h_minus_aux j) x + \<dots> = (\<Sum>\<^sup>+ x'. h_minus_aux j (x', x) + \<delta> * indicator (set (cycle_edges C)) (x', x))"
    unfolding Suc.IH d_IN_def by(simp add: nn_integral_add[symmetric])
  also have "\<dots> = d_IN (h_minus_aux (Suc j)) x" unfolding d_IN_def
    by(auto intro!: nn_integral_cong simp add: \<delta>_def C_def split: split_indicator)
  finally show ?case .
qed

lemma h_minus_aux_source:
  assumes "cycles \<Delta> \<noteq> {}"
  shows "h_minus_aux j (source \<Delta>, y) = 0"
proof(induction j)
  case 0 thus ?case by simp
next
  case (Suc j)
  have "(source \<Delta>, y) \<notin> set (cycle_edges (enum_cycle j))"
  proof
    assume *: "(source \<Delta>, y) \<in> set (cycle_edges (enum_cycle j))"
    have cycle: "cycle \<Delta> (enum_cycle j)" using assms by(rule cycle_enum_cycle)
    from cycle_leave_ex_enter[OF this *]
    obtain z where "(z, source \<Delta>) \<in> set (cycle_edges (enum_cycle j))" ..
    with cycle_edges_edges[OF cycle] have "(z, source \<Delta>) \<in> \<^bold>E" ..
    thus False using source_in[of z] by simp
  qed
  then show ?case using Suc.IH by simp
qed

lemma h_minus_aux_cycle:
  fixes j defines "C \<equiv> enum_cycle j"
  assumes "cycles \<Delta> \<noteq> {}"
  shows "\<exists>e\<in>set (cycle_edges C). h_minus_aux (Suc j) e = h' e"
proof -
  let ?A = "{h' e' - h_minus_aux j e'|e'. e' \<in> set (cycle_edges C)}"
  from assms have "cycle \<Delta> C" by auto
  from cycle_edges_not_Nil[OF this] have "Min ?A \<in> ?A" using [[simproc add: finite_Collect]]
    by(intro Min_in)(fastforce simp add: neq_Nil_conv)+
  then obtain e' where e: "e' \<in> set (cycle_edges C)"
    and "Min ?A = h' e' - h_minus_aux j e'" by auto
  hence "h_minus_aux (Suc j) e' = h' e'"
    by(simp add: C_def h_minus_aux_le_h')
  with e show ?thesis by blast
qed

end

fun h_minus :: "nat \<Rightarrow> 'v edge \<Rightarrow> ennreal"
where
  "h_minus 0 e = 0"
| "h_minus (Suc i) e = h_minus i e + (SUP j. h_minus_aux (\<lambda>e'. h_plus (Suc i) e' - h_minus i e') j e)"

lemma h_minus_le_h_plus: "h_minus i e \<le> h_plus i e"
proof(induction i e rule: h_minus.induct)
  case 0: (1 e) show ?case by simp
next
  case Suc: (2 i e)
  note IH = Suc.IH(2)[OF UNIV_I]
  let ?h' = "\<lambda>e'. h_plus (Suc i) e' - h_minus i e'"
  have h': "?h' e' \<noteq> top" for e' using IH(1)[of e'] by(simp add: )

  have "(\<Squnion>j. h_minus_aux ?h' j e) \<le> ?h' e" by(rule SUP_least)(rule h_minus_aux_le_h'[OF h'])
  hence "h_minus (Suc i) e \<le> h_minus i e + \<dots>" by(simp add: add_mono)
  also have "\<dots> = h_plus (Suc i) e" using IH[of e] h_plus_mono[of i e]
    by auto
  finally show ?case .
qed

lemma finite_h': "h_plus (Suc i) e - h_minus i e \<noteq> top"
  by simp

lemma h_minus_mono: "h_minus i e \<le> h_minus (Suc i) e"
proof -
  have "h_minus i e + 0 \<le> h_minus (Suc i) e" unfolding h_minus.simps
    by(rule add_mono; simp add: SUP_upper2)
  thus ?thesis by simp
qed

lemma h_minus_finite [simp]: "h_minus i e \<noteq> \<top>"
proof -
  have "h_minus i e \<le> h_plus i e" by(rule h_minus_le_h_plus)
  also have "\<dots> < \<top>" by (simp add: less_top[symmetric])
  finally show ?thesis by simp
qed

lemma d_OUT_h_minus:
  assumes cycles: "cycles \<Delta> \<noteq> {}"
  shows "d_OUT (h_minus i) x = d_IN (h_minus i) x"
proof(induction i)
  case (Suc i)
  let ?h' = "\<lambda>e. h_plus (Suc i) e - h_minus i e"
  have "d_OUT (\<lambda>e. h_minus (Suc i) e) x = d_OUT (h_minus i) x + d_OUT (\<lambda>e. SUP j. h_minus_aux ?h' j e) x"
    by(simp add: d_OUT_add SUP_upper2)
  also have "d_OUT (\<lambda>e. SUP j. h_minus_aux ?h' j e) x = (SUP j. d_OUT (h_minus_aux ?h' j) x)"
    by(rule d_OUT_monotone_convergence_SUP incseq_SucI le_funI h_minus_aux_mono finite_h')+
  also have "\<dots> = (SUP j. d_IN (h_minus_aux ?h' j) x)"
    by(rule SUP_cong[OF refl])(rule d_OUT_h_minus_aux[OF finite_h' cycles])
  also have "\<dots> = d_IN (\<lambda>e. SUP j. h_minus_aux ?h' j e) x"
    by(rule d_IN_monotone_convergence_SUP[symmetric] incseq_SucI le_funI h_minus_aux_mono finite_h')+
  also have "d_OUT (h_minus i) x + \<dots> = d_IN (\<lambda>e. h_minus (Suc i) e) x" using Suc.IH
    by(simp add: d_IN_add SUP_upper2)
  finally show ?case .
qed simp

lemma h_minus_source:
  assumes "cycles \<Delta> \<noteq> {}"
  shows "h_minus n (source \<Delta>, y) = 0"
by(induction n)(simp_all add: h_minus_aux_source[OF finite_h' assms])

lemma h_minus_source_in [simp]: "h_minus i (x, source \<Delta>) = 0"
using h_minus_le_h_plus[of i "(x, source \<Delta>)"] by simp

lemma h_minus_OUT_finite [simp]: "d_OUT (h_minus i) x \<noteq> top"
proof -
  have "d_OUT (h_minus i) x \<le> d_OUT (h_plus i) x" by(rule d_OUT_mono)(rule h_minus_le_h_plus)
  also have "\<dots> < \<top>" by (simp add: less_top[symmetric])
  finally show ?thesis by simp
qed

lemma h_minus_cycle:
  assumes "cycle \<Delta> C"
  shows "\<exists>e\<in>set (cycle_edges C). h_minus i e = h_plus i e"
proof(cases i)
  case (Suc i)
  let ?h' = "\<lambda>e. h_plus (Suc i) e - h_minus i e"
  from assms have cycles: "cycles \<Delta> \<noteq> {}" by auto
  with assms from_nat_into_surj[of "cycles \<Delta>" C] obtain j where j: "C = enum_cycle j"
    by(auto simp add: enum_cycle_def)
  from h_minus_aux_cycle[of "?h'" j, OF finite_h' cycles] j
  obtain e where e: "e \<in> set (cycle_edges C)" and "h_minus_aux ?h' (Suc j) e = ?h' e" by(auto)
  then have "h_plus (Suc i) e = h_minus i e + h_minus_aux ?h' (Suc j) e"
    using order_trans[OF h_minus_le_h_plus h_plus_mono]
    by (subst eq_commute) simp
  also have "\<dots> \<le> h_minus (Suc i) e" unfolding h_minus.simps
    by(intro add_mono SUP_upper; simp)
  finally show ?thesis using e h_minus_le_h_plus[of "Suc i" e] Suc by auto
next
  case 0
  from cycle_edges_not_Nil[OF assms] obtain x y where e: "(x, y) \<in> set (cycle_edges C)"
    by(fastforce simp add: neq_Nil_conv)
  then have "x \<noteq> source \<Delta>" using assms by(auto dest: source_out_not_cycle)
  hence "h_plus 0 (x, y) = 0" by simp
  with e 0 show ?thesis by(auto simp del: h_plus.simps)
qed

abbreviation lim_h_plus :: "'v edge \<Rightarrow> ennreal"
where "lim_h_plus e \<equiv> SUP n. h_plus n e"

abbreviation lim_h_minus :: "'v edge \<Rightarrow> ennreal"
where "lim_h_minus e \<equiv> SUP n. h_minus n e"

lemma lim_h_plus_le_g: "lim_h_plus e \<le> g e"
by(rule SUP_least)(rule h_plus_le_g)

lemma lim_h_plus_finite [simp]: "lim_h_plus e \<noteq> top"
proof -
  have "lim_h_plus e \<le> g e" by(rule lim_h_plus_le_g)
  also have "\<dots> < top" by (simp add: less_top[symmetric])
  finally show ?thesis unfolding less_top .
qed

lemma lim_h_minus_le_lim_h_plus: "lim_h_minus e \<le> lim_h_plus e"
by(rule SUP_mono)(blast intro: h_minus_le_h_plus)

lemma lim_h_minus_finite [simp]: "lim_h_minus e \<noteq> top"
proof -
  have "lim_h_minus e \<le> lim_h_plus e" by(rule lim_h_minus_le_lim_h_plus)
  also have "\<dots> < top" unfolding less_top[symmetric] by (rule lim_h_plus_finite)
  finally show ?thesis unfolding less_top[symmetric] by simp
qed

lemma lim_h_minus_IN_finite [simp]:
  assumes "x \<noteq> sink \<Delta>"
  shows "d_IN lim_h_minus x \<noteq> top"
proof -
  have "d_IN lim_h_minus x \<le> d_IN lim_h_plus x"
    by(intro d_IN_mono le_funI lim_h_minus_le_lim_h_plus)
  also have "\<dots> \<le> d_IN g x" by(intro d_IN_mono le_funI lim_h_plus_le_g)
  also have "\<dots> < \<top>" using assms by(simp add: finite_IN_g less_top[symmetric])
  finally show ?thesis by simp
qed

lemma lim_h_plus_OUT_IN:
  assumes "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  shows "d_OUT lim_h_plus x = d_IN lim_h_plus x"
proof(cases "x \<in> \<^bold>V")
  case True
  have "d_OUT lim_h_plus x = (SUP n. d_OUT (h_plus n) x)"
    by(rule d_OUT_monotone_convergence_SUP incseq_SucI le_funI h_plus_mono)+
  also have "\<dots> = (SUP n. d_IN (h_plus n) x)" (is "?lhs = ?rhs")
  proof(rule antisym)
    show "?lhs \<le> ?rhs" by(rule SUP_mono)(auto intro: h_plus_OUT_le_IN[OF assms(1)])
    show "?rhs \<le> ?lhs"
    proof(rule SUP_mono)
      fix i
      from enum_v_repeat[OF True assms, of i]
      obtain i' where "i' > i" "enum_v i' = x" by auto
      moreover then obtain i'' where i': "i' = Suc i''" by(cases i') auto
      ultimately have "d_OUT (h_plus i') x = d_IN (h_plus i'') x" using  \<open>x \<noteq> source \<Delta>\<close>
        by(simp add: h_plus_OUT_eq_IN)
      moreover have "i \<le> i''" using \<open>i < i'\<close> i' by simp
      then have "d_IN (h_plus i) x \<le> d_IN (h_plus i'') x" by(intro d_IN_mono h_plus_mono')
      ultimately have "d_IN (h_plus i) x \<le> d_OUT (h_plus i') x" by simp
      thus "\<exists>i'\<in>UNIV. d_IN (h_plus i) x \<le> d_OUT (h_plus i') x" by blast
    qed
  qed
  also have "\<dots> = d_IN lim_h_plus x"
    by(rule d_IN_monotone_convergence_SUP[symmetric] incseq_SucI le_funI h_plus_mono)+
  finally show ?thesis .
next
  case False
  have "(x, y) \<notin> support_flow lim_h_plus" for y using False h_plus_outside[of "(x, y)"]
    by(fastforce elim!: support_flow.cases simp add: less_SUP_iff vertex_def)
  moreover have "(y, x) \<notin> support_flow lim_h_plus" for y using False h_plus_outside[of "(y, x)"]
    by(fastforce elim!: support_flow.cases simp add: less_SUP_iff vertex_def)
  ultimately show ?thesis
    by(auto simp add: d_OUT_alt_def2 d_IN_alt_def2 AE_count_space intro!: nn_integral_cong_AE)
qed

lemma lim_h_minus_OUT_IN:
  assumes cycles: "cycles \<Delta> \<noteq> {}"
  shows "d_OUT lim_h_minus x = d_IN lim_h_minus x"
proof -
  have "d_OUT lim_h_minus x = (SUP n. d_OUT (h_minus n) x)"
    by(rule d_OUT_monotone_convergence_SUP incseq_SucI le_funI h_minus_mono)+
  also have "\<dots> = (SUP n. d_IN (h_minus n) x)" using cycles by(simp add: d_OUT_h_minus)
  also have "\<dots> = d_IN lim_h_minus x"
    by(rule d_IN_monotone_convergence_SUP[symmetric] incseq_SucI le_funI h_minus_mono)+
  finally show ?thesis .
qed

definition h :: "'v edge \<Rightarrow> ennreal"
where "h e = lim_h_plus e - (if cycles \<Delta> \<noteq> {} then lim_h_minus e else 0)"

lemma h_le_lim_h_plus: "h e \<le> lim_h_plus e"
by (simp add: h_def)

lemma h_le_g: "h e \<le> g e"
using h_le_lim_h_plus[of e] lim_h_plus_le_g[of e] by simp

lemma flow_h: "flow \<Delta> h"
proof
  fix e
  have "h e \<le> lim_h_plus e" by(rule h_le_lim_h_plus)
  also have "\<dots> \<le> g e" by(rule lim_h_plus_le_g)
  also have "\<dots> \<le> capacity \<Delta> e" using g by(rule flowD_capacity)
  finally show "h e \<le> \<dots>" .
next
  fix x
  assume "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  then show "KIR h x"
    by (cases "cycles \<Delta> = {}")
       (auto simp add: h_def[abs_def] lim_h_plus_OUT_IN d_OUT_diff d_IN_diff lim_h_minus_le_lim_h_plus lim_h_minus_OUT_IN)
qed

lemma value_h_plus: "value_flow \<Delta> (h_plus i) = value_flow \<Delta> g" (is "?lhs = ?rhs")
proof(rule antisym)
  show "?lhs \<le> ?rhs" by(rule d_OUT_mono)(rule h_plus_le_g)

  have "?rhs \<le> value_flow \<Delta> (h_plus 0)"
    by(auto simp add: d_OUT_def cong: if_cong intro!: nn_integral_mono)
  also have "\<dots> \<le> value_flow \<Delta> (h_plus i)"
    by(rule d_OUT_mono)(rule h_plus_mono'; simp)
  finally show "?rhs \<le> ?lhs" .
qed

lemma value_h: "value_flow \<Delta> h = value_flow \<Delta> g" (is "?lhs = ?rhs")
proof(rule antisym)
  have "?lhs \<le> value_flow \<Delta> lim_h_plus" using ennreal_minus_mono
    by(fastforce simp add: h_def intro!: d_OUT_mono)
  also have "\<dots> \<le> ?rhs" by(rule d_OUT_mono)(rule lim_h_plus_le_g)
  finally show "?lhs \<le> ?rhs" .

  show "?rhs \<le> ?lhs"
    by(auto simp add: d_OUT_def h_def h_minus_source cong: if_cong intro!: nn_integral_mono SUP_upper2[where i=0])
qed


definition h_diff :: "nat \<Rightarrow> 'v edge \<Rightarrow> ennreal"
where "h_diff i e = h_plus i e - (if cycles \<Delta> \<noteq> {} then h_minus i e else 0)"

lemma d_IN_h_source [simp]: "d_IN (h_diff i) (source \<Delta>) = 0"
by(simp add: d_IN_def h_diff_def cong del: if_weak_cong)

lemma h_diff_le_h_plus: "h_diff i e \<le> h_plus i e"
by(simp add: h_diff_def)

lemma h_diff_le_g: "h_diff i e \<le> g e"
using h_diff_le_h_plus[of i e] h_plus_le_g[of i e] by simp

lemma h_diff_loop [simp]: "h_diff i (x, x) = 0"
using h_diff_le_g[of i "(x, x)"] by simp

lemma supp_h_diff_edges: "support_flow (h_diff i) \<subseteq> \<^bold>E"
proof
  fix e
  assume "e \<in> support_flow (h_diff i)"
  then have "0 < h_diff i e" by(auto elim: support_flow.cases)
  also have "h_diff i e \<le> h_plus i e" by(rule h_diff_le_h_plus)
  finally show "e \<in> \<^bold>E" using h_plus_outside[of e i] by(cases "e \<in> \<^bold>E") auto
qed

lemma h_diff_OUT_le_IN:
  assumes "x \<noteq> source \<Delta>"
  shows "d_OUT (h_diff i) x \<le> d_IN (h_diff i) x"
proof(cases "cycles \<Delta> \<noteq> {}")
  case False
  thus ?thesis using assms by(simp add: h_diff_def[abs_def] h_plus_OUT_le_IN)
next
  case cycles: True
  then have "d_OUT (h_diff i) x = d_OUT (h_plus i) x - d_OUT (h_minus i) x"
    unfolding h_diff_def[abs_def] using assms
    by (simp add: h_minus_le_h_plus d_OUT_diff)
  also have "\<dots> \<le> d_IN (h_plus i) x - d_IN (h_minus i) x" using cycles assms
    by(intro ennreal_minus_mono h_plus_OUT_le_IN)(simp_all add: d_OUT_h_minus)
  also have "\<dots> = d_IN (h_diff i) x" using cycles
    unfolding h_diff_def[abs_def] by(subst d_IN_diff)(simp_all add: h_minus_le_h_plus d_OUT_h_minus[symmetric])
  finally show ?thesis .
qed

lemma h_diff_cycle:
  assumes "cycle \<Delta> p"
  shows "\<exists>e\<in>set (cycle_edges p). h_diff i e = 0"
proof -
  from h_minus_cycle[OF assms, of i] obtain e
    where e: "e \<in> set (cycle_edges p)" and "h_minus i e = h_plus i e" by auto
  hence "h_diff i e = 0" using assms by(auto simp add: h_diff_def)
  with e show ?thesis by blast
qed

lemma d_IN_h_le_value': "d_IN (h_diff i) x \<le> value_flow \<Delta> (h_plus i)"
proof -
  let ?supp = "support_flow (h_diff i)"
  define X where "X = {y. (y, x) \<in> ?supp^*} - {x}"

  { fix x y
    assume x: "x \<notin> X" and y: "y \<in> X"
    { assume yx: "(y, x) \<in> ?supp\<^sup>*" and neq: "y \<noteq> x" and xy: "(x, y) \<in> ?supp"
      from yx obtain p' where "rtrancl_path (\<lambda>x y. (x, y) \<in> ?supp) y p' x"
        unfolding rtrancl_def rtranclp_eq_rtrancl_path by auto
      then obtain p where p: "rtrancl_path (\<lambda>x y. (x, y) \<in> ?supp) y p x"
        and distinct: "distinct (y # p)" by(rule rtrancl_path_distinct)
      with neq have "p \<noteq> []" by(auto elim: rtrancl_path.cases)

      from xy have "(x, y) \<in> \<^bold>E" using supp_h_diff_edges[of i] by(auto)
      moreover from p have "path \<Delta> y p x"
        by(rule rtrancl_path_mono)(auto dest: supp_h_diff_edges[THEN subsetD])
      ultimately have "path \<Delta> x (y # p) x" by(auto intro: rtrancl_path.intros)
      hence cycle: "cycle \<Delta> (y # p)" using _ distinct by(rule cycle) simp
      from h_diff_cycle[OF this, of i] obtain e
        where e: "e \<in> set (cycle_edges (y # p))" and 0: "h_diff i e = 0" by blast
      from e obtain n where e': "e = ((y # p) ! n, (p @ [y]) ! n)" and n: "n < Suc (length p)"
        by(auto simp add: cycle_edges_def set_zip)
      have "e \<in> ?supp"
      proof(cases "n = length p")
        case True
        with rtrancl_path_last[OF p] \<open>p \<noteq> []\<close> have "(y # p) ! n = x"
          by(cases p)(simp_all add: last_conv_nth del: last.simps)
        with e' True have "e = (x, y)" by simp
        with xy show ?thesis by simp
      next
        case False
        with n have "n < length p" by simp
        with rtrancl_path_nth[OF p this] e' show ?thesis by(simp add: nth_append)
      qed
      with 0 have False by(simp add: support_flow.simps) }
    hence "(x, y) \<notin> ?supp" using x y
      by(auto simp add: X_def intro: converse_rtrancl_into_rtrancl)
    then have "h_diff i (x, y) = 0"
      by(simp add: support_flow.simps) }
  note acyclic = this

  { fix y
    assume "y \<notin> X"
    hence "(y, x) \<notin> ?supp" by(auto simp add: X_def support_flow.simps intro: not_in_support_flowD)
    hence "h_diff i (y, x) = 0"  by(simp add: support_flow.simps) }
  note in_X = this

  let ?diff = "\<lambda>x. (\<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x * indicator X y)"
  have finite2: "(\<Sum>\<^sup>+ x. ?diff x) \<noteq> top" (is "?lhs \<noteq> _")
  proof -
    have "?lhs \<le> (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_plus i (x, y))"
      by(intro nn_integral_mono)(auto simp add: h_diff_def split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ e. h_plus i e)" by(rule nn_integral_fst_count_space)
    also have "\<dots> < \<top>" by(simp add: h_plus_sum_finite less_top[symmetric])
    finally show ?thesis by simp
  qed
  have finite1: "?diff x \<noteq> top" for x
    using finite2 by(rule neq_top_trans)(rule nn_integral_ge_point, simp)
  have finite3: "(\<Sum>\<^sup>+ x. d_OUT (h_diff i) x * indicator (X - {source \<Delta>}) x) \<noteq> \<top>" (is "?lhs \<noteq> _")
  proof -
    have "?lhs \<le> (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_plus i (x, y))" unfolding d_OUT_def
      apply(simp add: nn_integral_multc[symmetric])
      apply(intro nn_integral_mono)
      apply(auto simp add: h_diff_def split: split_indicator)
      done
    also have "\<dots> = (\<Sum>\<^sup>+ e. h_plus i e)" by(rule nn_integral_fst_count_space)
    also have "\<dots> < \<top>" by(simp add: h_plus_sum_finite less_top[symmetric])
    finally show ?thesis by simp
  qed

  have "d_IN (h_diff i) x = (\<Sum>\<^sup>+ y. h_diff i (y, x) * indicator X y)" unfolding d_IN_def
    by(rule nn_integral_cong)(simp add: in_X split: split_indicator)
  also have "\<dots> \<le> (\<Sum>\<^sup>+ x\<in>- X. \<Sum>\<^sup>+ y. h_diff i (y, x) * indicator X y)"
    by(rule nn_integral_ge_point)(simp add: X_def)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_diff i (y, x) * indicator X y * indicator (- X) x)"
    by(simp add: nn_integral_multc nn_integral_count_space_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x * indicator (- X) y)"
    by(subst nn_integral_snd_count_space[where f="case_prod _", simplified])(simp add: nn_integral_fst_count_space[where f="case_prod _", simplified])
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. (\<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x * indicator (- X) y) + (?diff x - ?diff x))"
    by(simp add: finite1)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. (\<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x * indicator (- X) y + h_diff i (x, y) * indicator X x * indicator X y) - ?diff x)"
    apply (subst add_diff_eq_ennreal)
    apply simp
    by(subst nn_integral_add[symmetric])(simp_all add:)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. (\<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x) - ?diff x)"
    by(auto intro!: nn_integral_cong arg_cong2[where f="(-)"] split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y\<in>UNIV. h_diff i (x, y) * indicator X x) - (\<Sum>\<^sup>+ x. ?diff x)"
    by(subst nn_integral_diff)(auto simp add: AE_count_space finite2 intro!: nn_integral_mono split: split_indicator)
  also have "(\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y\<in>UNIV. h_diff i (x, y) * indicator X x) = (\<Sum>\<^sup>+ x. d_OUT (h_diff i) x * indicator X x)"
    unfolding d_OUT_def by(simp add: nn_integral_multc)
  also have "\<dots> = (\<Sum>\<^sup>+ x. d_OUT (h_diff i) x * indicator (X - {source \<Delta>}) x + value_flow \<Delta> (h_diff i) * indicator X (source \<Delta>) * indicator {source \<Delta>} x)"
    by(rule nn_integral_cong)(simp split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ x. d_OUT (h_diff i) x * indicator (X - {source \<Delta>}) x) + value_flow \<Delta> (h_diff i) * indicator X (source \<Delta>)"
    (is "_ = ?out" is "_ = _ + ?value")
    by(subst nn_integral_add) simp_all
  also have "(\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X x * indicator X y) =
             (\<Sum>\<^sup>+ x\<in>UNIV. \<Sum>\<^sup>+ y. h_diff i (x, y) * indicator X y)"
    using acyclic by(intro nn_integral_cong)(simp split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>UNIV. \<Sum>\<^sup>+ x. h_diff i (x, y) * indicator X y)"
    by(subst nn_integral_snd_count_space[where f="case_prod _", simplified])(simp add: nn_integral_fst_count_space[where f="case_prod _", simplified])
  also have "\<dots> = (\<Sum>\<^sup>+ y. d_IN (h_diff i) y * indicator X y)" unfolding d_IN_def
    by(simp add: nn_integral_multc)
  also have "\<dots> = (\<Sum>\<^sup>+ y. d_IN (h_diff i) y * indicator (X - {source \<Delta>}) y)"
    by(rule nn_integral_cong)(simp split: split_indicator)
  also have "?out - \<dots> \<le> (\<Sum>\<^sup>+ x. d_OUT (h_diff i) x * indicator (X - {source \<Delta>}) x) - \<dots> + ?value"
    by (auto simp add: add_ac intro!: add_diff_le_ennreal)
  also have "\<dots> \<le> 0 + ?value" using h_diff_OUT_le_IN finite3
    by(intro nn_integral_mono add_right_mono)(auto split: split_indicator intro!: diff_eq_0_ennreal nn_integral_mono simp add: less_top)
  also have "\<dots> \<le> value_flow \<Delta> (h_diff i)" by(simp split: split_indicator)
  also have "\<dots> \<le> value_flow \<Delta> (h_plus i)" by(rule d_OUT_mono le_funI h_diff_le_h_plus)+
  finally show ?thesis .
qed

lemma d_IN_h_le_value: "d_IN h x \<le> value_flow \<Delta> h" (is "?lhs \<le> ?rhs")
proof -
  have [tendsto_intros]: "(\<lambda>i. h_plus i e) \<longlonglongrightarrow> lim_h_plus e" for e
    by(rule LIMSEQ_SUP incseq_SucI h_plus_mono)+
  have [tendsto_intros]: "(\<lambda>i. h_minus i e) \<longlonglongrightarrow> lim_h_minus e" for e
    by(rule LIMSEQ_SUP incseq_SucI h_minus_mono)+
  have "(\<lambda>i. h_diff i e) \<longlonglongrightarrow> lim_h_plus e - (if cycles \<Delta> \<noteq> {} then lim_h_minus e else 0)" for e
    by(auto intro!: tendsto_intros tendsto_diff_ennreal simp add: h_diff_def simp del: Sup_eq_top_iff SUP_eq_top_iff)
  then have "d_IN h x = (\<Sum>\<^sup>+ y. liminf (\<lambda>i. h_diff i (y, x)))"
    by(simp add: d_IN_def h_def tendsto_iff_Liminf_eq_Limsup)
  also have "\<dots> \<le> liminf (\<lambda>i. d_IN (h_diff i) x)" unfolding d_IN_def
    by(rule nn_integral_liminf) simp_all
  also have "\<dots> \<le> liminf (\<lambda>i. value_flow \<Delta> h)" using d_IN_h_le_value'[of _ x]
    by(intro Liminf_mono eventually_sequentiallyI)(auto simp add: value_h_plus value_h)
  also have "\<dots> = value_flow \<Delta> h" by(simp add: Liminf_const)
  finally show ?thesis .
qed

lemma flow_cleanup: \<comment> \<open>Lemma 5.4\<close>
  "\<exists>h \<le> g. flow \<Delta> h \<and> value_flow \<Delta> h = value_flow \<Delta> g \<and> (\<forall>x. d_IN h x \<le> value_flow \<Delta> h)"
by(intro exI[where x=h] conjI strip le_funI d_IN_h_le_value flow_h value_h h_le_g)

end

subsection \<open>Residual network\<close>

context countable_network begin

definition residual_network :: "'v flow \<Rightarrow> ('v, 'more) network_scheme"
where "residual_network f =
  \<lparr>edge = \<lambda>x y. edge \<Delta> x y \<or> edge \<Delta> y x \<and> y \<noteq> source \<Delta>,
   capacity = \<lambda>(x, y). if edge \<Delta> x y then capacity \<Delta> (x, y) - f (x, y) else if y = source \<Delta> then 0 else f (y, x),
   source = source \<Delta>, sink = sink \<Delta>, \<dots> = network.more \<Delta> \<rparr>"

lemma residual_network_sel [simp]:
  "edge (residual_network f) x y \<longleftrightarrow> edge \<Delta> x y \<or> edge \<Delta> y x \<and> y \<noteq> source \<Delta>"
  "capacity (residual_network f) (x, y) = (if edge \<Delta> x y then capacity \<Delta> (x, y) - f (x, y) else if y = source \<Delta> then 0 else f (y, x))"
  "source (residual_network f) = source \<Delta>"
  "sink (residual_network f) = sink \<Delta>"
  "network.more (residual_network f) = network.more \<Delta>"
by(simp_all add: residual_network_def)

lemma "\<^bold>E_residual_network": "\<^bold>E\<^bsub>residual_network f\<^esub> = \<^bold>E \<union> {(x, y). (y, x) \<in> \<^bold>E \<and> y \<noteq> source \<Delta>}"
by auto

lemma vertices_residual_network [simp]: "vertex (residual_network f) = vertex \<Delta>"
by(auto simp add: vertex_def fun_eq_iff)

inductive wf_residual_network :: "bool"
where "\<lbrakk> \<And>x y. (x, y) \<in> \<^bold>E \<Longrightarrow> (y, x) \<notin> \<^bold>E; (source \<Delta>, sink \<Delta>) \<notin> \<^bold>E \<rbrakk> \<Longrightarrow> wf_residual_network"

lemma wf_residual_networkD:
  "\<lbrakk> wf_residual_network; edge \<Delta> x y \<rbrakk> \<Longrightarrow> \<not> edge \<Delta> y x"
  "\<lbrakk> wf_residual_network; e \<in> \<^bold>E \<rbrakk> \<Longrightarrow> prod.swap e \<notin> \<^bold>E"
  "\<lbrakk> wf_residual_network; edge \<Delta> (source \<Delta>) (sink \<Delta>) \<rbrakk> \<Longrightarrow> False"
by(auto simp add: wf_residual_network.simps)

lemma residual_countable_network:
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  shows "countable_network (residual_network f)" (is "countable_network ?\<Delta>")
proof
  have "countable (converse \<^bold>E)" by simp
  then have "countable {(x, y). (y, x) \<in> \<^bold>E \<and> y \<noteq> source \<Delta>}"
    by(rule countable_subset[rotated]) auto
  then show "countable \<^bold>E\<^bsub>?\<Delta>\<^esub>" unfolding "\<^bold>E_residual_network" by simp

  show "source ?\<Delta> \<noteq> sink ?\<Delta>" by simp
  show "capacity ?\<Delta> e = 0" if "e \<notin> \<^bold>E\<^bsub>?\<Delta>\<^esub>" for e using that by(cases e)(auto intro: flowD_outside[OF f])
  show "capacity ?\<Delta> e \<noteq> top" for e
    using flowD_finite[OF f] by(cases e) auto
qed

end

locale antiparallel_edges = countable_network \<Delta>
  for \<Delta> :: "('v, 'more) network_scheme" (structure)
begin

text \<open>We eliminate the assumption of antiparallel edges by adding a vertex for every edge.
  Thus, antiparallel edges are split up into a cycle of 4 edges. This idea already appears in
  @{cite Aharoni1983EJC}.\<close>

datatype (plugins del: transfer size) 'v' vertex = Vertex 'v' | Edge 'v' 'v'

inductive edg :: "'v vertex \<Rightarrow> 'v vertex \<Rightarrow> bool"
where
  OUT: "edge \<Delta> x y \<Longrightarrow> edg (Vertex x) (Edge x y)"
| IN: "edge \<Delta> x y \<Longrightarrow> edg (Edge x y) (Vertex y)"

inductive_simps edg_simps [simp]:
  "edg (Vertex x) v"
  "edg (Edge x y) v"
  "edg v (Vertex x)"
  "edg v (Edge x y)"

fun split :: "'v flow \<Rightarrow> 'v vertex flow"
where
  "split f (Vertex x, Edge x' y) = (if x' = x then f (x, y) else 0)"
| "split f (Edge x y', Vertex y) = (if y' = y then f (x, y) else 0)"
| "split f _ = 0"

lemma split_Vertex1_eq_0I: "(\<And>z. y \<noteq> Edge x z) \<Longrightarrow> split f (Vertex x, y) = 0"
by(cases y) auto

lemma split_Vertex2_eq_0I: "(\<And>z. y \<noteq> Edge z x) \<Longrightarrow> split f (y, Vertex x) = 0"
by(cases y) simp_all

lemma split_Edge1_eq_0I: "(\<And>z. y \<noteq> Vertex x) \<Longrightarrow> split f (Edge z x, y) = 0"
by(cases y) simp_all

lemma split_Edge2_eq_0I: "(\<And>z. y \<noteq> Vertex x) \<Longrightarrow> split f (y, Edge x z) = 0"
by(cases y) simp_all

definition \<Delta>'' :: "'v vertex network"
where "\<Delta>'' = \<lparr>edge = edg, capacity = split (capacity \<Delta>), source = Vertex (source \<Delta>), sink = Vertex (sink \<Delta>)\<rparr>"

lemma \<Delta>''_sel [simp]:
  "edge \<Delta>'' = edg"
  "capacity \<Delta>'' = split (capacity \<Delta>)"
  "source \<Delta>'' = Vertex (source \<Delta>)"
  "sink \<Delta>'' = Vertex (sink \<Delta>)"
by(simp_all add: \<Delta>''_def)

lemma "\<^bold>E_\<Delta>''": "\<^bold>E\<^bsub>\<Delta>''\<^esub> = (\<lambda>(x, y). (Vertex x, Edge x y)) ` \<^bold>E \<union> (\<lambda>(x, y). (Edge x y, Vertex y)) ` \<^bold>E"
by(auto elim: edg.cases)

lemma "\<^bold>V_\<Delta>''": "\<^bold>V\<^bsub>\<Delta>''\<^esub> = Vertex ` \<^bold>V \<union> case_prod Edge ` \<^bold>E"
by(auto 4 4 simp add: vertex_def elim!: edg.cases)

lemma inj_on_Edge1 [simp]: "inj_on (\<lambda>x. Edge x y) A"
by(simp add: inj_on_def)

lemma inj_on_Edge2 [simp]: "inj_on (Edge x) A"
by(simp add: inj_on_def)

lemma d_IN_split_Vertex [simp]: "d_IN (split f) (Vertex x) = d_IN f x" (is "?lhs = ?rhs")
proof(rule trans)
  show "?lhs = (\<Sum>\<^sup>+ v'\<in>range (\<lambda>y. Edge y x). split f (v', Vertex x))"
    by(auto intro!: nn_integral_cong split_Vertex2_eq_0I simp add: d_IN_def nn_integral_count_space_indicator split: split_indicator)
  show "\<dots> = ?rhs" by(simp add: nn_integral_count_space_reindex d_IN_def)
qed

lemma d_OUT_split_Vertex [simp]: "d_OUT (split f) (Vertex x) = d_OUT f x" (is "?lhs = ?rhs")
proof(rule trans)
  show "?lhs = (\<Sum>\<^sup>+ v'\<in>range (Edge x). split f (Vertex x, v'))"
    by(auto intro!: nn_integral_cong split_Vertex1_eq_0I simp add: d_OUT_def nn_integral_count_space_indicator split: split_indicator)
  show "\<dots> = ?rhs" by(simp add: nn_integral_count_space_reindex d_OUT_def)
qed

lemma d_IN_split_Edge [simp]: "d_IN (split f) (Edge x y) = max 0 (f (x, y))" (is "?lhs = ?rhs")
proof(rule trans)
  show "?lhs = (\<Sum>\<^sup>+ v'. split f (v', Edge x y) * indicator {Vertex x} v')"
    unfolding d_IN_def by(rule nn_integral_cong)(simp add: split_Edge2_eq_0I split: split_indicator)
  show "\<dots> = ?rhs" by(simp add: max_def)
qed

lemma d_OUT_split_Edge [simp]: "d_OUT (split f) (Edge x y) = max 0 (f (x, y))" (is "?lhs = ?rhs")
proof(rule trans)
  show "?lhs = (\<Sum>\<^sup>+ v'. split f (Edge x y, v') * indicator {Vertex y} v')"
    unfolding d_OUT_def by(rule nn_integral_cong)(simp add: split_Edge1_eq_0I split: split_indicator)
  show "\<dots> = ?rhs" by(simp add: max_def)
qed

lemma \<Delta>''_countable_network: "countable_network \<Delta>''"
proof
  show "countable \<^bold>E\<^bsub>\<Delta>''\<^esub>" unfolding "\<^bold>E_\<Delta>''" by(simp)
  show "source \<Delta>'' \<noteq> sink \<Delta>''" by auto
  show "capacity \<Delta>'' e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Delta>''\<^esub>" for e using that
    by(cases "(capacity \<Delta>, e)" rule: split.cases)(auto simp add: capacity_outside)
  show "capacity \<Delta>'' e \<noteq> top" for e by(cases "(capacity \<Delta>, e)" rule: split.cases)(auto)
qed

interpretation \<Delta>'': countable_network \<Delta>'' by(rule \<Delta>''_countable_network)

lemma \<Delta>''_flow_attainability:
  assumes "flow_attainability_axioms \<Delta>"
  shows "flow_attainability \<Delta>''"
proof -
  interpret flow_attainability \<Delta> using _ assms by(rule flow_attainability.intro) unfold_locales
  show ?thesis
  proof
    show "d_IN (capacity \<Delta>'') v \<noteq> \<top> \<or> d_OUT (capacity \<Delta>'') v \<noteq> \<top>" if "v \<noteq> sink \<Delta>''" for v
      using that finite_capacity by(cases v)(simp_all add: max_def)
    show "\<not> edge \<Delta>'' v v" for v by(auto elim: edg.cases)
    show "\<not> edge \<Delta>'' v (source \<Delta>'')" for v by(simp add: source_in)
  qed
qed

lemma flow_split [simp]:
  assumes "flow \<Delta> f"
  shows "flow \<Delta>'' (split f)"
proof
  show "split f e \<le> capacity \<Delta>'' e" for e
    by(cases "(f, e)" rule: split.cases)(auto intro: flowD_capacity[OF assms] intro: SUP_upper2 assms)
  show "KIR (split f) x" if "x \<noteq> source \<Delta>''" "x \<noteq> sink \<Delta>''" for x
    using that by(cases "x")(auto dest: flowD_KIR[OF assms])
qed

abbreviation (input) collect :: "'v vertex flow \<Rightarrow> 'v flow"
where "collect f \<equiv> (\<lambda>(x, y). f (Edge x y, Vertex y))"

lemma d_OUT_collect:
  assumes f: "flow \<Delta>'' f"
  shows "d_OUT (collect f) x = d_OUT f (Vertex x)"
proof -
  have "d_OUT (collect f) x = (\<Sum>\<^sup>+ y. f (Edge x y, Vertex y))"
    by(simp add: nn_integral_count_space_reindex d_OUT_def)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range (Edge x). f (Vertex x, y))"
  proof(clarsimp simp add: nn_integral_count_space_reindex intro!: nn_integral_cong)
    fix y
    have "(\<Sum>\<^sup>+ z. f (Edge x y, z) * indicator {Vertex y} z) = d_OUT f (Edge x y)"
      unfolding d_OUT_def by(rule nn_integral_cong)(simp split: split_indicator add: \<Delta>''.flowD_outside[OF f])
    also have "\<dots> = d_IN f (Edge x y)" using f by(rule flowD_KIR) simp_all
    also have "\<dots> = (\<Sum>\<^sup>+ z. f (z, Edge x y) * indicator {Vertex x} z)"
      unfolding d_IN_def by(rule nn_integral_cong)(simp split: split_indicator add: \<Delta>''.flowD_outside[OF f])
    finally show "f (Edge x y, Vertex y) = f (Vertex x, Edge x y)"
      by(simp add: max_def)
  qed
  also have "\<dots> = d_OUT f (Vertex x)"
    by(auto intro!: nn_integral_cong \<Delta>''.flowD_outside[OF f] simp add: nn_integral_count_space_indicator d_OUT_def split: split_indicator)
  finally show ?thesis .
qed

lemma flow_collect [simp]:
  assumes f: "flow \<Delta>'' f"
  shows "flow \<Delta> (collect f)"
proof
  show "collect f e \<le> capacity \<Delta> e" for e using flowD_capacity[OF f, of "(case_prod Edge e, Vertex (snd e))"]
    by(cases e)(simp)

  fix x
  assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  have "d_OUT (collect f) x = d_OUT f (Vertex x)" using f by(rule d_OUT_collect)
  also have "\<dots> = d_IN f (Vertex x)" using x flowD_KIR[OF f, of "Vertex x"] by(simp)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range (\<lambda>z. Edge z x). f (y, Vertex x))"
    by(auto intro!: nn_integral_cong \<Delta>''.flowD_outside[OF f] simp add: nn_integral_count_space_indicator d_IN_def split: split_indicator)
  also have "\<dots> = d_IN (collect f) x" by(simp add: nn_integral_count_space_reindex d_IN_def)
  finally show "KIR (collect f) x" .
qed

lemma value_collect: "flow \<Delta>'' f \<Longrightarrow> value_flow \<Delta> (collect f) = value_flow \<Delta>'' f"
by(simp add: d_OUT_collect)

lemma \<Delta>''_wf_residual_network:
  assumes no_loop: "\<And>x. \<not> edge \<Delta> x x"
  shows "\<Delta>''.wf_residual_network"
by(auto simp add: \<Delta>''.wf_residual_network.simps assms elim!: edg.cases)

end

subsection \<open>The attainability theorem\<close>

context flow_attainability begin

lemma residual_flow_attainability:
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  shows "flow_attainability (residual_network f)" (is "flow_attainability ?\<Delta>")
proof -
  interpret res: countable_network "residual_network f" by(rule residual_countable_network[OF assms])
  show ?thesis
  proof
    fix x
    assume sink: "x \<noteq> sink ?\<Delta>"
    then consider (source) "x = source \<Delta>" | (IN) "d_IN (capacity \<Delta>) x \<noteq> \<top>" | (OUT) "x \<noteq> source \<Delta>" "d_OUT (capacity \<Delta>) x \<noteq> \<top>"
      using finite_capacity[of x] by auto
    then show "d_IN (capacity ?\<Delta>) x \<noteq> \<top> \<or> d_OUT (capacity ?\<Delta>) x \<noteq> \<top>"
    proof(cases)
      case source
      hence "d_IN (capacity ?\<Delta>) x = 0" by(simp add: d_IN_def source_in)
      thus ?thesis by simp
    next
      case IN
      have "d_IN (capacity ?\<Delta>) x =
        (\<Sum>\<^sup>+ y. (capacity \<Delta> (y, x) - f (y, x)) * indicator \<^bold>E (y, x) +
              (if x = source \<Delta> then 0 else f (x, y) * indicator \<^bold>E (x, y)))"
        using flowD_outside[OF f] unfolding d_IN_def
        by(auto intro!: nn_integral_cong split: split_indicator dest: wf_residual_networkD[OF wf])
      also have "\<dots> = (\<Sum>\<^sup>+ y. (capacity \<Delta> (y, x) - f (y, x)) * indicator \<^bold>E (y, x)) +
        (\<Sum>\<^sup>+ y. (if x = source \<Delta> then 0 else f (x, y) * indicator \<^bold>E (x, y)))"
        (is "_ = ?in + ?out")
        by(subst nn_integral_add)(auto simp add: AE_count_space split: split_indicator intro!: flowD_capacity[OF f])
      also have "\<dots> \<le> d_IN (capacity \<Delta>) x + (if x = source \<Delta> then 0 else d_OUT f x)" (is "_ \<le> ?in + ?rest")
        unfolding d_IN_def d_OUT_def
        by(rule add_mono)(auto intro!: nn_integral_mono split: split_indicator simp add: nn_integral_0_iff_AE AE_count_space intro!: diff_le_self_ennreal)
      also consider (source) "x = source \<Delta>" | (inner) "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" using sink by auto
      then have "?rest < \<top>"
      proof cases
        case inner
        show ?thesis using inner flowD_finite_OUT[OF f inner] by (simp add: less_top)
      qed simp
      ultimately show ?thesis using IN sink by (auto simp: less_top[symmetric] top_unique)
    next
      case OUT
      have "d_OUT (capacity ?\<Delta>) x =
        (\<Sum>\<^sup>+ y. (capacity \<Delta> (x, y) - f (x, y)) * indicator \<^bold>E (x, y) +
              (if y = source \<Delta> then 0 else f (y, x) * indicator \<^bold>E (y, x)))"
        using flowD_outside[OF f] unfolding d_OUT_def
        by(auto intro!: nn_integral_cong split: split_indicator dest: wf_residual_networkD[OF wf] simp add: source_in)
      also have "\<dots> = (\<Sum>\<^sup>+ y. (capacity \<Delta> (x, y) - f (x, y)) * indicator \<^bold>E (x, y)) +
        (\<Sum>\<^sup>+ y. (if y = source \<Delta> then 0 else f (y, x) * indicator \<^bold>E (y, x)))"
        (is "_ = ?in + ?out")
        by(subst nn_integral_add)(auto simp add: AE_count_space split: split_indicator intro!: flowD_capacity[OF f])
      also have "\<dots> \<le> d_OUT (capacity \<Delta>) x + d_IN f x" (is "_ \<le> ?out + ?rest")
        unfolding d_IN_def d_OUT_def
        by(rule add_mono)(auto intro!: nn_integral_mono split: split_indicator simp add: nn_integral_0_iff_AE AE_count_space intro!: diff_le_self_ennreal)
      also have "?rest = d_OUT f x" using flowD_KIR[OF f OUT(1)] sink by simp
      also have "?out + \<dots> \<le> ?out + ?out" by(intro add_left_mono d_OUT_mono flowD_capacity[OF f])
      finally show ?thesis using OUT by (auto simp: top_unique)
    qed
  next
    show "\<not> edge ?\<Delta> x x" for x by(simp add: no_loop)
    show "\<not> edge ?\<Delta> x (source ?\<Delta>)" for x by(simp add: source_in)
  qed
qed

end

definition plus_flow :: "('v, 'more) graph_scheme \<Rightarrow> 'v flow \<Rightarrow> 'v flow \<Rightarrow> 'v flow" (infixr "\<oplus>\<index>" 65)
where "plus_flow G f g = (\<lambda>(x, y). if edge G x y then f (x, y) + g (x, y) - g (y, x) else 0)"

lemma plus_flow_simps [simp]: fixes G (structure) shows
  "(f \<oplus> g) (x, y) = (if edge G x y then f (x, y) + g (x, y) - g (y, x) else 0)"
by(simp add: plus_flow_def)

lemma plus_flow_outside: fixes G (structure) shows "e \<notin> \<^bold>E \<Longrightarrow> (f \<oplus> g) e = 0"
by(cases e) simp

lemma
  fixes \<Delta> (structure)
  assumes f_outside: "\<And>e. e \<notin> \<^bold>E \<Longrightarrow> f e = 0"
  and g_le_f: "\<And>x y. edge \<Delta> x y \<Longrightarrow> g (y, x) \<le> f (x, y)"
  shows OUT_plus_flow: "d_IN g x \<noteq> top \<Longrightarrow> d_OUT (f \<oplus> g) x = d_OUT f x + (\<Sum>\<^sup>+ y\<in>UNIV. g (x, y) * indicator \<^bold>E (x, y)) - (\<Sum>\<^sup>+ y. g (y, x) * indicator \<^bold>E (x, y))"
    (is "_ \<Longrightarrow> ?OUT" is "_ \<Longrightarrow> _ = _ + ?g_out - ?g_out'")
  and IN_plus_flow: "d_OUT g x \<noteq> top \<Longrightarrow> d_IN (f \<oplus> g) x = d_IN f x + (\<Sum>\<^sup>+ y\<in>UNIV. g (y, x) * indicator \<^bold>E (y, x)) - (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (y, x))"
    (is "_ \<Longrightarrow> ?IN" is "_ \<Longrightarrow> _ = _ + ?g_in - ?g_in'")
proof -
  assume "d_IN g x \<noteq> top"
  then have finite1: "(\<Sum>\<^sup>+ y. g (y, x) * indicator A (f y)) \<noteq> top" for A f
    by(rule neq_top_trans)(auto split: split_indicator simp add: d_IN_def intro!: nn_integral_mono)

  have "d_OUT (f \<oplus> g) x = (\<Sum>\<^sup>+ y. (g (x, y) + (f (x, y) - g (y, x))) * indicator \<^bold>E (x, y))"
    unfolding d_OUT_def by(rule nn_integral_cong)(simp split: split_indicator add: add_diff_eq_ennreal add.commute ennreal_diff_add_assoc g_le_f)
  also have "\<dots> = ?g_out + (\<Sum>\<^sup>+ y. (f (x, y) - g (y, x)) * indicator \<^bold>E (x, y))"
    (is "_ = _ + ?rest")
    by(subst nn_integral_add[symmetric])(auto simp add: AE_count_space g_le_f split: split_indicator intro!: nn_integral_cong)
  also have "?rest = (\<Sum>\<^sup>+ y. f (x, y) * indicator \<^bold>E (x, y)) - ?g_out'" (is "_ = ?f - _")
    apply(subst nn_integral_diff[symmetric])
    apply(auto intro!: nn_integral_cong split: split_indicator simp add: AE_count_space g_le_f finite1)
    done
  also have "?f = d_OUT f x" unfolding d_OUT_def using f_outside
    by(auto intro!: nn_integral_cong split: split_indicator)
  also have "(\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (x, y)) + (d_OUT f x - (\<Sum>\<^sup>+ y. g (y, x) * indicator \<^bold>E (x, y))) =
     d_OUT f x + ?g_out - ?g_out'"
     by (subst ennreal_diff_add_assoc[symmetric])
        (auto simp: ac_simps d_OUT_def intro!: nn_integral_mono g_le_f split: split_indicator)
  finally show ?OUT .
next
  assume "d_OUT g x \<noteq> top"
  then have finite2: "(\<Sum>\<^sup>+ y. g (x, y) * indicator A (f y)) \<noteq> top" for A f
    by(rule neq_top_trans)(auto split: split_indicator simp add: d_OUT_def intro!: nn_integral_mono)

  have "d_IN (f \<oplus> g) x = (\<Sum>\<^sup>+ y. (g (y, x) + (f (y, x) - g (x, y))) * indicator \<^bold>E (y, x))"
    unfolding d_IN_def by(rule nn_integral_cong)(simp split: split_indicator add: add_diff_eq_ennreal add.commute ennreal_diff_add_assoc g_le_f)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>UNIV. g (y, x) * indicator \<^bold>E (y, x)) + (\<Sum>\<^sup>+ y. (f (y, x) - g (x, y)) * indicator \<^bold>E (y, x))"
    (is "_ = _ + ?rest")
    by(subst nn_integral_add[symmetric])(auto simp add: AE_count_space g_le_f split: split_indicator intro!: nn_integral_cong)
  also have "?rest = (\<Sum>\<^sup>+ y. f (y, x) * indicator \<^bold>E (y, x))- ?g_in'"
    by(subst nn_integral_diff[symmetric])(auto intro!: nn_integral_cong split: split_indicator simp add: add_ac add_diff_eq_ennreal AE_count_space g_le_f finite2)
  also have "(\<Sum>\<^sup>+ y. f (y, x) * indicator \<^bold>E (y, x)) = d_IN f x"
    unfolding d_IN_def using f_outside by(auto intro!: nn_integral_cong split: split_indicator)
  also have "(\<Sum>\<^sup>+ y. g (y, x) * indicator \<^bold>E (y, x)) + (d_IN f x - (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (y, x))) =
     d_IN f x + ?g_in - ?g_in'"
     by (subst ennreal_diff_add_assoc[symmetric])
        (auto simp: ac_simps d_IN_def intro!: nn_integral_mono g_le_f split: split_indicator)
  finally show ?IN .
qed

context countable_network begin

lemma d_IN_plus_flow:
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  and g: "flow (residual_network f) g"
  shows "d_IN (f \<oplus> g) x \<le> d_IN f x + d_IN g x"
proof -
  have "d_IN (f \<oplus> g) x \<le> (\<Sum>\<^sup>+ y. f (y, x) + g (y, x))" unfolding d_IN_def
    by(rule nn_integral_mono)(auto intro: diff_le_self_ennreal)
  also have "\<dots> = d_IN f x + d_IN g x"
    by(subst nn_integral_add)(simp_all add: d_IN_def)
  finally show ?thesis .
qed

lemma scale_flow:
  assumes f: "flow \<Delta> f"
  and c: "c \<le> 1"
  shows "flow \<Delta> (\<lambda>e. c * f e)"
proof(intro flow.intros)
  fix e
  from c have "c * f e \<le> 1 * f e" by(rule mult_right_mono) simp
  also have "\<dots> \<le> capacity \<Delta> e" using flowD_capacity[OF f, of e] by simp
  finally show "c * f e \<le> \<dots>" .
next
  fix x
  assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  have "d_OUT (\<lambda>e. c * f e) x = c * d_OUT f x" by(simp add: d_OUT_cmult)
  also have "d_OUT f x = d_IN f x" using f x by(rule flowD_KIR)
  also have "c * \<dots> = d_IN (\<lambda>e. c * f e) x" by(simp add: d_IN_cmult)
  finally show "KIR (\<lambda>e. c * f e) x" .
qed

lemma value_scale_flow:
  "value_flow \<Delta> (\<lambda>e. c * f e) = c * value_flow \<Delta> f"
by(rule d_OUT_cmult)

lemma value_flow:
  assumes f: "flow \<Delta> f"
  and source_out: "\<And>y. edge \<Delta> (source \<Delta>) y \<longleftrightarrow> y = x"
  shows "value_flow \<Delta> f = f (source \<Delta>, x)"
proof -
  have "value_flow \<Delta> f = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T (source \<Delta>). f (source \<Delta>, y))"
    by(rule d_OUT_alt_def)(simp add: flowD_outside[OF f])
  also have "\<dots> = (\<Sum>\<^sup>+ y. f (source \<Delta>, y) * indicator {x} y)"
    by(subst nn_integral_count_space_indicator)(auto intro!: nn_integral_cong split: split_indicator simp add: outgoing_def source_out)
  also have "\<dots> = f (source \<Delta>, x)" by(simp add: one_ennreal_def[symmetric] max_def)
  finally show ?thesis .
qed

end

context flow_attainability begin

lemma value_plus_flow:
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  and g: "flow (residual_network f) g"
  shows "value_flow \<Delta> (f \<oplus> g) = value_flow \<Delta> f + value_flow \<Delta> g"
proof -
  interpret RES: countable_network "residual_network f" using wf f by(rule residual_countable_network)
  have "value_flow \<Delta> (f \<oplus> g) = (\<Sum>\<^sup>+ y. f (source \<Delta>, y) + g (source \<Delta>, y))"
    unfolding d_OUT_def by(rule nn_integral_cong)(simp add: flowD_outside[OF f] RES.flowD_outside[OF g] source_in)
  also have "\<dots> = value_flow \<Delta> f + value_flow \<Delta> g" unfolding d_OUT_def
    by(rule nn_integral_add) simp_all
  finally show ?thesis .
qed

lemma flow_residual_add: \<comment> \<open>Lemma 5.3\<close>
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  and g: "flow (residual_network f) g"
  shows "flow \<Delta> (f \<oplus> g)"
proof
  fix e
  { assume e: "e \<in> \<^bold>E"
    hence "(f \<oplus> g) e = f e + g e - g (prod.swap e)" by(cases e) simp
    also have "\<dots> \<le> f e + g e - 0" by(rule ennreal_minus_mono) simp_all
    also have "\<dots> \<le> f e + (capacity \<Delta> e - f e)"
      using e flowD_capacity[OF g, of e] by(simp split: prod.split_asm add: add_mono)
    also have "\<dots> = capacity \<Delta> e" using flowD_capacity[OF f, of e]
      by simp
    also note calculation }
  thus "(f \<oplus> g) e \<le> capacity \<Delta> e" by(cases e) auto
next
  fix x
  assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  have g_le_f: "g (y, x) \<le> f (x, y)" if "edge \<Delta> x y" for x y
    using that flowD_capacity[OF g, of "(y, x)"]
    by(auto split: if_split_asm dest: wf_residual_networkD[OF wf] elim: order_trans)

  interpret RES: flow_attainability "residual_network f" using wf f by(rule residual_flow_attainability)

  have finite1: "(\<Sum>\<^sup>+ y. g (y, x) * indicator A (f y)) \<noteq> \<top>" for A f
    using RES.flowD_finite_IN[OF g, of x]
    by(rule neq_top_trans)(auto simp add: x d_IN_def split: split_indicator intro: nn_integral_mono)
  have finite2: "(\<Sum>\<^sup>+ y. g (x, y) * indicator A (f y)) \<noteq> \<top>" for A f
    using RES.flowD_finite_OUT[OF g, of x]
    by(rule neq_top_trans)(auto simp add: x d_OUT_def split: split_indicator intro: nn_integral_mono)

  have "d_OUT (f \<oplus> g) x = d_OUT f x + (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (x, y)) - (\<Sum>\<^sup>+ y. g (y, x) * indicator \<^bold>E (x, y))"
    (is "_ = ?f + ?g_out - ?g_in")
    using flowD_outside[OF f] g_le_f RES.flowD_finite_IN[OF g, of x]
    by(rule OUT_plus_flow)(simp_all add: x)
  also have "?f = d_IN f x" using f x by(auto dest: flowD_KIR)
  also have "?g_out = (\<Sum>\<^sup>+ y. g (x, y) * indicator (- \<^bold>E) (y, x))"
  proof -
    have "(\<Sum>\<^sup>+ y. g (x, y) * indicator (- \<^bold>E) (y, x)) =
          (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (x, y)) + (\<Sum>\<^sup>+ y. g (x, y) * indicator (- \<^bold>E) (x, y) * indicator (- \<^bold>E) (y, x))"
      by(subst nn_integral_add[symmetric])(auto simp add: AE_count_space dest: wf_residual_networkD[OF wf] split: split_indicator intro!: nn_integral_cong)
    also have "(\<Sum>\<^sup>+ y. g (x, y) * indicator (- \<^bold>E) (x, y) * indicator (- \<^bold>E) (y, x)) = 0"
      using RES.flowD_outside[OF g]
      by(auto simp add: nn_integral_0_iff_AE AE_count_space split: split_indicator)
    finally show ?thesis by simp
  qed
  also have "\<dots> = (\<Sum>\<^sup>+ y. g (x, y) - g (x, y) * indicator \<^bold>E (y, x))"
    by(rule nn_integral_cong)(simp split: split_indicator add: RES.flowD_finite[OF g])
  also have "\<dots> = d_OUT g x - (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (y, x))"
    (is "_ = _ - ?g_in_E") unfolding d_OUT_def
    by(subst nn_integral_diff)(simp_all add: AE_count_space finite2 split: split_indicator)
  also have "d_IN f x + (d_OUT g x - (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (y, x))) - ?g_in =
    ((d_IN f x + d_OUT g x) - (\<Sum>\<^sup>+ y. g (x, y) * indicator \<^bold>E (y, x))) - ?g_in"
    by (subst add_diff_eq_ennreal) (auto simp: d_OUT_def intro!: nn_integral_mono split: split_indicator)
  also have "d_OUT g x = d_IN g x" using x g by(auto dest: flowD_KIR)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>UNIV. g (y, x) * indicator (- \<^bold>E) (y, x)) + (\<Sum>\<^sup>+ y. g (y, x) * indicator \<^bold>E (y, x))"
    (is "_ = ?x + ?g_in_E'")
    by(subst nn_integral_add[symmetric])(auto intro!: nn_integral_cong simp add: d_IN_def AE_count_space split: split_indicator)
  also have "?x = ?g_in"
  proof -
    have "?x = (\<Sum>\<^sup>+ y. g (y, x) * indicator (- \<^bold>E) (x, y) * indicator (- \<^bold>E) (y, x)) + ?g_in"
      by(subst nn_integral_add[symmetric])(auto simp add: AE_count_space  dest: wf_residual_networkD[OF wf] split: split_indicator intro!: nn_integral_cong)
    also have "(\<Sum>\<^sup>+ y. g (y, x) * indicator (- \<^bold>E) (x, y) * indicator (- \<^bold>E) (y, x)) = 0"
      using RES.flowD_outside[OF g]
      by(auto simp add: nn_integral_0_iff_AE AE_count_space split: split_indicator)
    finally show ?thesis by simp
  qed
  also have "(d_IN f x + (?g_in + ?g_in_E') - ?g_in_E) - ?g_in =
    d_IN f x + ?g_in_E' + ?g_in - ?g_in - ?g_in_E"
    by (subst diff_diff_commute_ennreal) (simp add: ac_simps)
  also have "\<dots> = d_IN f x + ?g_in_E' - ?g_in_E"
    by (subst ennreal_add_diff_cancel_right) (simp_all add: finite1)
  also have "\<dots> = d_IN (f \<oplus> g) x"
    using flowD_outside[OF f]  g_le_f RES.flowD_finite_OUT[OF g, of x]
    by(rule IN_plus_flow[symmetric])(simp_all add: x)
  finally show "KIR (f \<oplus> g) x" by simp
qed

definition minus_flow :: "'v flow \<Rightarrow> 'v flow \<Rightarrow> 'v flow" (infixl "\<ominus>" 65)
where
  "f \<ominus> g = (\<lambda>(x, y). if edge \<Delta> x y then f (x, y) - g (x, y) else if edge \<Delta> y x then g (y, x) - f (y, x) else 0)"

lemma minus_flow_simps [simp]:
  "(f \<ominus> g) (x, y) = (if edge \<Delta> x y then f (x, y) - g (x, y) else if edge \<Delta> y x then g (y, x) - f (y, x) else 0)"
by(simp add: minus_flow_def)

lemma minus_flow:
  assumes wf: "wf_residual_network"
  and f: "flow \<Delta> f"
  and g: "flow \<Delta> g"
  and value_le: "value_flow \<Delta> g \<le> value_flow \<Delta> f"
  and f_finite: "f (source \<Delta>, x) \<noteq> \<top>"
  and source_out: "\<And>y. edge \<Delta> (source \<Delta>) y \<longleftrightarrow> y = x"
  shows "flow (residual_network g) (f \<ominus> g)" (is "flow ?\<Delta> ?f")
proof
  show "?f e \<le> capacity ?\<Delta> e" for e
    using value_le f_finite flowD_capacity[OF g] flowD_capacity[OF f]
    by(cases e)(auto simp add: source_in source_out value_flow[OF f source_out] value_flow[OF g source_out] less_top
                     intro!: diff_le_self_ennreal diff_eq_0_ennreal ennreal_minus_mono)

  fix x
  assume "x \<noteq> source ?\<Delta>" "x \<noteq> sink ?\<Delta>"
  hence x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" by simp_all

  have finite_f_in: "(\<Sum>\<^sup>+ y. f (y, x) * indicator A y) \<noteq> top" for A
    using flowD_finite_IN[OF f, of x]
    by(rule neq_top_trans)(auto simp add: x d_IN_def split: split_indicator intro!: nn_integral_mono)
  have finite_f_out: "(\<Sum>\<^sup>+ y. f (x, y) * indicator A y) \<noteq> top" for A
    using flowD_finite_OUT[OF f, of x]
    by(rule neq_top_trans)(auto simp add: x d_OUT_def split: split_indicator intro!: nn_integral_mono)
  have finite_f[simp]: "f (x, y) \<noteq> top" "f (y, x) \<noteq> top" for y
    using finite_f_in[of "{y}"] finite_f_out[of "{y}"] by auto

  have finite_g_in: "(\<Sum>\<^sup>+ y. g (y, x) * indicator A y) \<noteq> top" for A
    using flowD_finite_IN[OF g, of x]
    by(rule neq_top_trans)(auto simp add: x d_IN_def split: split_indicator intro!: nn_integral_mono)
  have finite_g_out: "(\<Sum>\<^sup>+ y. g (x, y) * indicator A y) \<noteq> top" for A
    using flowD_finite_OUT[OF g x]
    by(rule neq_top_trans)(auto simp add: x d_OUT_def split: split_indicator intro!: nn_integral_mono)
  have finite_g[simp]: "g (x, y) \<noteq> top" "g (y, x) \<noteq> top" for y
    using finite_g_in[of "{y}"] finite_g_out[of "{y}"] by auto

  have "d_OUT (f \<ominus> g) x = (\<Sum>\<^sup>+ y. (f (x, y) - g (x, y)) * indicator \<^bold>E (x, y) * indicator {y. g (x, y) \<le> f (x, y)} y) +
    (\<Sum>\<^sup>+ y. (g (y, x) - f (y, x)) * indicator \<^bold>E (y, x) * indicator {y. f (y, x) < g (y, x)} y)"
    (is "_ = ?out + ?in" is "_ = (\<Sum>\<^sup>+ y\<in>_. _ * ?f_ge_g y) + (\<Sum>\<^sup>+ y\<in>_. _ * ?g_gt_f y)")
    using flowD_finite[OF g]
    apply(subst nn_integral_add[symmetric])
    apply(auto 4 4 simp add: d_OUT_def not_le less_top[symmetric] intro!: nn_integral_cong
           dest!: wf_residual_networkD[OF wf] split: split_indicator intro!: diff_eq_0_ennreal)
    done
  also have "?in = (\<Sum>\<^sup>+ y. (g (y, x) - f (y, x)) * ?g_gt_f y)"
    using flowD_outside[OF f] flowD_outside[OF g] by(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>UNIV. g (y, x) * ?g_gt_f y) - (\<Sum>\<^sup>+ y. f (y, x) * ?g_gt_f y)" (is "_ = ?g_in - ?f_in")
    using finite_f_in
    by(subst nn_integral_diff[symmetric])(auto simp add: AE_count_space split: split_indicator intro!: nn_integral_cong)
  also have "?out = (\<Sum>\<^sup>+ y. (f (x, y) - g (x, y)) * ?f_ge_g y)"
    using flowD_outside[OF f] flowD_outside[OF g] by(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ y. f (x, y) * ?f_ge_g y) - (\<Sum>\<^sup>+ y. g (x, y) * ?f_ge_g y)" (is "_ = ?f_out - ?g_out")
    using finite_g_out
    by(subst nn_integral_diff[symmetric])(auto simp add: AE_count_space split: split_indicator intro!: nn_integral_cong)
  also have "?f_out = d_OUT f x - (\<Sum>\<^sup>+ y. f (x, y) * indicator {y. f (x, y) < g (x, y)} y)" (is "_ = _ - ?f_out_less")
    unfolding d_OUT_def using flowD_finite[OF f] using finite_f_out
    by(subst nn_integral_diff[symmetric])(auto split: split_indicator intro!: nn_integral_cong)
  also have "?g_out = d_OUT g x - (\<Sum>\<^sup>+ y. g (x, y) * indicator {y. f (x, y) < g (x, y)} y)" (is "_ = _ - ?g_less_f")
    unfolding d_OUT_def using flowD_finite[OF g] finite_g_out
    by(subst nn_integral_diff[symmetric])(auto split: split_indicator intro!: nn_integral_cong)
  also have "d_OUT f x - ?f_out_less - (d_OUT g x - ?g_less_f) + (?g_in - ?f_in) =
    (?g_less_f + (d_OUT f x - ?f_out_less)) - d_OUT g x + (?g_in - ?f_in)"
    by (subst diff_diff_ennreal')
       (auto simp: ac_simps d_OUT_def nn_integral_diff[symmetric] finite_g_out finite_f_out intro!: nn_integral_mono split: split_indicator )
  also have "\<dots> = ?g_less_f + d_OUT f x - ?f_out_less - d_OUT g x + (?g_in - ?f_in)"
    by (subst add_diff_eq_ennreal)
       (auto simp: d_OUT_def intro!: nn_integral_mono split: split_indicator)
  also have "\<dots> = d_OUT f x + ?g_less_f - ?f_out_less - d_OUT g x + (?g_in - ?f_in)"
    by (simp add: ac_simps)
  also have "\<dots> = d_OUT f x + (?g_less_f - ?f_out_less) - d_OUT g x + (?g_in - ?f_in)"
    by (subst add_diff_eq_ennreal[symmetric])
       (auto intro!: nn_integral_mono split: split_indicator)
  also have "\<dots> = (?g_in - ?f_in) + ((?g_less_f - ?f_out_less) + d_OUT f x - d_OUT g x)"
    by (simp add: ac_simps)
  also have "\<dots> = ((?g_in - ?f_in) + ((?g_less_f - ?f_out_less) + d_OUT f x)) - d_OUT g x"
    apply (subst add_diff_eq_ennreal)
    apply (simp_all add: d_OUT_def)
    apply (subst nn_integral_diff[symmetric])
    apply (auto simp: AE_count_space finite_f_out nn_integral_add[symmetric] not_less diff_add_cancel_ennreal intro!: nn_integral_mono split: split_indicator)
    done
  also have "\<dots> = ((?g_less_f - ?f_out_less) + (d_OUT f x + (?g_in - ?f_in))) - d_OUT g x"
    by (simp add: ac_simps)
  also have "\<dots> = ((?g_less_f - ?f_out_less) + (d_IN f x + (?g_in - ?f_in))) - d_IN g x"
    unfolding flowD_KIR[OF f x] flowD_KIR[OF g x] ..
  also have "\<dots> = (?g_less_f - ?f_out_less) + ((d_IN f x + (?g_in - ?f_in)) - d_IN g x)"
    apply (subst (2) add_diff_eq_ennreal)
    apply (simp_all add: d_IN_def)
    apply (subst nn_integral_diff[symmetric])
    apply (auto simp: AE_count_space finite_f_in finite_f_out nn_integral_add[symmetric] not_less  ennreal_ineq_diff_add[symmetric]
                intro!: nn_integral_mono split: split_indicator)
    done
  also have "\<dots> = (?g_less_f - ?f_out_less) + (d_IN f x + ?g_in - d_IN g x - ?f_in)"
    by (subst (2) add_diff_eq_ennreal) (auto intro!: nn_integral_mono split: split_indicator simp: diff_diff_commute_ennreal)
  also have "\<dots> = (?g_less_f - ?f_out_less) + (d_IN f x - (d_IN g x - ?g_in) - ?f_in)"
    apply (subst diff_diff_ennreal')
    apply (auto simp: d_IN_def intro!: nn_integral_mono split: split_indicator)
    apply (subst nn_integral_diff[symmetric])
    apply (auto simp: AE_count_space finite_g_in intro!: nn_integral_mono split: split_indicator)
    done
  also have "\<dots> =(d_IN f x - ?f_in) - (d_IN g x - ?g_in) + (?g_less_f - ?f_out_less)"
    by (simp add: ac_simps diff_diff_commute_ennreal)
  also have "?g_less_f - ?f_out_less = (\<Sum>\<^sup>+ y. (g (x, y) - f (x, y)) * indicator {y. f (x, y) < g (x, y)} y)" using finite_f_out
    by(subst nn_integral_diff[symmetric])(auto simp add: AE_count_space split: split_indicator intro!: nn_integral_cong)
  also have "\<dots> = (\<Sum>\<^sup>+ y. (g (x, y) - f (x, y)) * indicator \<^bold>E (x, y) * indicator {y. f (x, y) < g (x, y)} y)" (is "_ = ?diff_out")
    using flowD_outside[OF f] flowD_outside[OF g] by(auto intro!: nn_integral_cong split: split_indicator)
  also have "d_IN f x - ?f_in = (\<Sum>\<^sup>+ y. f (y, x) * indicator {y. g (y, x) \<le> f (y, x)} y)"
    unfolding d_IN_def using finite_f_in
    apply(subst nn_integral_diff[symmetric])
    apply(auto simp add: AE_count_space split: split_indicator intro!: nn_integral_cong)
    done
  also have "d_IN g x - ?g_in = (\<Sum>\<^sup>+ y. g (y, x) * indicator {y. g (y, x) \<le> f (y, x)} y)"
    unfolding d_IN_def using finite_g_in
    by(subst nn_integral_diff[symmetric])(auto simp add: flowD_finite[OF g] AE_count_space split: split_indicator intro!: nn_integral_cong)
  also have "(\<Sum>\<^sup>+ y\<in>UNIV. f (y, x) * indicator {y. g (y, x) \<le> f (y, x)} y) - \<dots> = (\<Sum>\<^sup>+ y. (f (y, x) - g (y, x)) * indicator {y. g (y, x) \<le> f (y, x)} y)"
    using finite_g_in
    by(subst nn_integral_diff[symmetric])(auto simp add: flowD_finite[OF g] AE_count_space split: split_indicator intro!: nn_integral_cong)
  also have "\<dots> = (\<Sum>\<^sup>+ y. (f (y, x) - g (y, x)) * indicator \<^bold>E (y, x) * indicator {y. g (y, x) \<le> f (y, x)} y)"
    using flowD_outside[OF f] flowD_outside[OF g] by(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> + ?diff_out = d_IN ?f x"
    using flowD_finite[OF g]
    apply(subst nn_integral_add[symmetric])
    apply(auto 4 4 simp add: d_IN_def not_le less_top[symmetric] intro!: nn_integral_cong
               dest!: wf_residual_networkD[OF wf] split: split_indicator intro: diff_eq_0_ennreal)
    done
  finally show "KIR ?f x" .
qed

lemma value_minus_flow:
  assumes f: "flow \<Delta> f"
  and g: "flow \<Delta> g"
  and value_le: "value_flow \<Delta> g \<le> value_flow \<Delta> f"
  and source_out: "\<And>y. edge \<Delta> (source \<Delta>) y \<longleftrightarrow> y = x"
  shows "value_flow \<Delta> (f \<ominus> g) = value_flow \<Delta> f - value_flow \<Delta> g" (is "?value")
proof -
  have "value_flow \<Delta> (f \<ominus> g) = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T (source \<Delta>). (f \<ominus> g) (source \<Delta>, y))"
    by(subst d_OUT_alt_def)(auto simp add: flowD_outside[OF f] flowD_outside[OF g] source_in)
  also have "\<dots> = (\<Sum>\<^sup>+ y. (f (source \<Delta>, y) - g (source \<Delta>, y)) * indicator {x} y)"
    by(subst nn_integral_count_space_indicator)(auto intro!: nn_integral_cong split: split_indicator simp add: outgoing_def source_out)
  also have "\<dots> = f (source \<Delta>, x) - g (source \<Delta>, x)"
    using value_le value_flow[OF f source_out] value_flow[OF g source_out]
    by(auto simp add: one_ennreal_def[symmetric] max_def not_le intro: antisym)
  also have "\<dots> = value_flow \<Delta> f - value_flow \<Delta> g" using f g source_out by(simp add: value_flow)
  finally show ?value .
qed

context
  fixes \<alpha>
  defines "\<alpha> \<equiv> (SUP g\<in>{g. flow \<Delta> g}. value_flow \<Delta> g)"
begin

lemma flow_by_value:
  assumes "v < \<alpha>"
  and real[rule_format]: "\<forall>f. \<alpha> = \<top> \<longrightarrow> flow \<Delta> f \<longrightarrow> value_flow \<Delta> f < \<alpha>"
  obtains f where "flow \<Delta> f" "value_flow \<Delta> f = v"
proof -
  have \<alpha>_pos: "\<alpha> > 0" using assms by (auto simp add: zero_less_iff_neq_zero)
  from \<open>v < \<alpha>\<close> obtain f where f: "flow \<Delta> f" and v: "v < value_flow \<Delta> f"
    unfolding \<alpha>_def less_SUP_iff by blast
  have [simp]: "value_flow \<Delta> f \<noteq> \<top>"
  proof
    assume val: "value_flow \<Delta> f = \<top>"
    from f have "value_flow \<Delta> f \<le> \<alpha>" unfolding \<alpha>_def by(blast intro: SUP_upper2)
    with val have "\<alpha> = \<top>" by (simp add: top_unique)
    from real[OF this f] val show False by simp
  qed
  let ?f = "\<lambda>e. (v / value_flow \<Delta> f) * f e"
  note f
  moreover
  have *: "0 < value_flow \<Delta> f"
    using \<open>v < value_flow \<Delta> f\<close> by (auto simp add: zero_less_iff_neq_zero)
  then have "v / value_flow \<Delta> f \<le> 1" using v
    by (auto intro!: divide_le_posI_ennreal)
  ultimately have "flow \<Delta> ?f" by (rule scale_flow)
  moreover {
    have "value_flow \<Delta> ?f = v * (value_flow \<Delta> f / value_flow \<Delta> f)"
      by(subst value_scale_flow)(simp add: divide_ennreal_def ac_simps)
    also have "\<dots> = v" using * by(subst ennreal_divide_self) (auto simp: less_top[symmetric])
    also note calculation }
  ultimately show ?thesis by(rule that)
qed

theorem ex_max_flow':
  assumes wf: "wf_residual_network"
  assumes source_out: "\<And>y. edge \<Delta> (source \<Delta>) y \<longleftrightarrow> y = x"
  and nontrivial: "\<^bold>V - {source \<Delta>, sink \<Delta>} \<noteq> {}"
  and real: "\<alpha> = ennreal \<alpha>'" and \<alpha>'_nonneg[simp]: "0 \<le> \<alpha>'"
  shows "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = \<alpha> \<and> (\<forall>x. d_IN f x \<le> value_flow \<Delta> f)"
proof -
  have \<alpha>'_not_neg[simp]: "\<not> \<alpha>' < 0"
    using \<alpha>'_nonneg by linarith

  let ?v = "\<lambda>i. (1 - (1 / 2) ^ i) * \<alpha>"
  let ?v_r = "\<lambda>i. ennreal ((1 - (1 / 2) ^ i) * \<alpha>')"
  have v_eq: "?v i = ?v_r i" for i
    by (auto simp: real ennreal_mult power_le_one ennreal_lessI ennreal_minus[symmetric]
                   ennreal_power[symmetric] divide_ennreal_def)
  have "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = ?v i" for i :: nat
  proof(cases "\<alpha> = 0")
    case True thus ?thesis by(auto intro!: exI[where x="\<lambda>_. 0"])
  next
    case False
    then have "?v i < \<alpha>"
      unfolding v_eq by (auto simp: real field_simps intro!: ennreal_lessI) (simp_all add: less_le)
    then obtain f where "flow \<Delta> f" and "value_flow \<Delta> f = ?v i"
      by(rule flow_by_value)(simp add: real)
    thus ?thesis by blast
  qed
  then obtain f_aux where f_aux: "\<And>i. flow \<Delta> (f_aux i)"
    and value_aux: "\<And>i. value_flow \<Delta> (f_aux i) = ?v_r i"
    unfolding v_eq by moura

  define f_i where "f_i = rec_nat (\<lambda>_. 0) (\<lambda>i f_i.
    let g = f_aux (Suc i) \<ominus> f_i;
      k_i = SOME k. k \<le> g \<and> flow (residual_network f_i) k \<and> value_flow (residual_network f_i) k = value_flow (residual_network f_i) g \<and> (\<forall>x. d_IN k x \<le> value_flow (residual_network f_i) k)
    in f_i \<oplus> k_i)"
  let ?P = "\<lambda>i k. k \<le> f_aux (Suc i) \<ominus> f_i i \<and> flow (residual_network (f_i i)) k \<and> value_flow (residual_network (f_i i)) k = value_flow (residual_network (f_i i)) (f_aux (Suc i) \<ominus> f_i i) \<and> (\<forall>x. d_IN k x \<le> value_flow (residual_network (f_i i)) k)"
  define k_i where "k_i i = Eps (?P i)" for i

  have f_i_simps [simp]: "f_i 0 = (\<lambda>_. 0)" "f_i (Suc i) = f_i i \<oplus> k_i i" for i
    by(simp_all add: f_i_def Let_def k_i_def)

  have k_i: "flow (residual_network (f_i i)) (k_i i)" (is ?k_i)
    and value_k_i: "value_flow (residual_network (f_i i)) (k_i i) = value_flow (residual_network (f_i i)) (f_aux (Suc i) \<ominus> f_i i)" (is "?value_k_i")
    and IN_k_i: "d_IN (k_i i) x \<le> value_flow (residual_network (f_i i)) (k_i i)" (is "?IN_k_i")
    and value_diff: "value_flow (residual_network (f_i i)) (f_aux (Suc i) \<ominus> f_i i) = value_flow \<Delta> (f_aux (Suc i)) - value_flow \<Delta> (f_i i)" (is "?value_diff")
    if "flow_network \<Delta> (f_i i)" and value_f_i: "value_flow \<Delta> (f_i i) = value_flow \<Delta> (f_aux i)" for i x
  proof -
    let ?RES = "residual_network (f_i i)"
    interpret fn: flow_network \<Delta> "f_i i" by(rule that)
    interpret RES: flow_attainability "?RES" using wf fn.g by(rule residual_flow_attainability)
    have le: "value_flow \<Delta> (f_i i) \<le> value_flow \<Delta> (f_aux (Suc i))"
      unfolding value_aux value_f_i
      unfolding v_eq by (rule ennreal_leI) (auto simp: field_simps)
    with wf f_aux fn.g have res_flow: "flow ?RES (f_aux (Suc i) \<ominus> f_i i)"
      using flowD_finite[OF f_aux] source_out
      by(rule minus_flow)
    show value': ?value_diff by(simp add: value_minus_flow[OF f_aux fn.g le source_out])
    also have "\<dots> < \<top>"
      unfolding value_aux v_eq by (auto simp: less_top[symmetric])
    finally have "value_flow ?RES (f_aux (Suc i) \<ominus> f_i i) \<noteq> \<top>" by simp
    then have fn': "flow_network ?RES (f_aux (Suc i) \<ominus> f_i i)"
      using nontrivial res_flow by(unfold_locales) simp_all
    then interpret fn': flow_network "?RES" "f_aux (Suc i) \<ominus> f_i i" .
    from fn'.flow_cleanup show ?k_i ?value_k_i ?IN_k_i unfolding k_i_def by(rule someI2_ex; blast)+
  qed

  have fn_i: "flow_network \<Delta> (f_i i)"
    and value_f_i: "value_flow \<Delta> (f_i i) = value_flow \<Delta> (f_aux i)"
    and d_IN_i: "d_IN (f_i i) x \<le> value_flow \<Delta> (f_i i)"  for i x
  proof(induction i)
    case 0
    { case 1 show ?case using nontrivial by(unfold_locales)(simp_all add: f_aux value_aux) }
    { case 2 show ?case by(simp add: value_aux) }
    { case 3 show ?case by(simp) }
  next
    case (Suc i)
    interpret fn: flow_network \<Delta> "f_i i" using Suc.IH(1) .
    let ?RES = "residual_network (f_i i)"

    have k_i: "flow ?RES (k_i i)"
      and value_k_i: "value_flow ?RES (k_i i) = value_flow ?RES (f_aux (Suc i) \<ominus> f_i i)"
      and d_IN_k_i: "d_IN (k_i i) x \<le> value_flow ?RES (k_i i)" for x
      using Suc.IH(1-2) by(rule k_i value_k_i IN_k_i)+

    interpret RES: flow_attainability "?RES" using wf fn.g by(rule residual_flow_attainability)
    have le: "value_flow \<Delta> (f_i i) \<le> value_flow \<Delta> (f_aux (Suc i))"
      unfolding value_aux Suc.IH(2) v_eq using \<alpha>'_nonneg by(intro ennreal_leI)(simp add: real field_simps)
    { case 1 show ?case unfolding f_i_simps
      proof
        show "flow \<Delta> (f_i i \<oplus> k_i i)" using wf fn.g k_i by(rule flow_residual_add)
        with RES.flowD_finite[OF k_i] show "value_flow \<Delta> (f_i i \<oplus> k_i i) \<noteq> \<top>"
          by(simp add: value_flow[OF _ source_out])
      qed(rule nontrivial) }
    from value_k_i have value_k: "value_flow ?RES (k_i i) = value_flow \<Delta> (f_aux (Suc i)) - value_flow \<Delta> (f_aux i)"
      by(simp add: value_minus_flow[OF f_aux fn.g le source_out] Suc.IH)
    { case 2 show ?case using value_k
        by(auto simp add: source_out value_plus_flow[OF wf fn.g k_i] Suc.IH value_aux field_simps intro!: ennreal_leI) }
    note value_f = this
    { case 3
      have "d_IN (f_i i \<oplus> k_i i) x \<le> d_IN (f_i i) x + d_IN (k_i i) x"
        using fn.g k_i by(rule d_IN_plus_flow[OF wf])
      also have "\<dots> \<le> value_flow \<Delta> (f_i i) + d_IN (k_i i) x" using Suc.IH(3) by(rule add_right_mono)
      also have "\<dots> \<le> value_flow \<Delta> (f_i i) + value_flow ?RES (k_i i)" using d_IN_k_i by(rule add_left_mono)
      also have "\<dots> = value_flow \<Delta> (f_i (Suc i))" unfolding value_f Suc.IH(2) value_k
        by(auto simp add: value_aux field_simps intro!: ennreal_leI)
      finally show ?case by simp }
  qed
  interpret fn: flow_network \<Delta> "f_i i" for i by(rule fn_i)
  note k_i = k_i[OF fn_i value_f_i] and value_k_i = value_k_i[OF fn_i value_f_i]
    and IN_k_i = IN_k_i[OF fn_i value_f_i] and value_diff = value_diff[OF fn_i value_f_i]

  have "\<exists>x\<ge>0. f_i i e = ennreal x" for i e
    using fn.finite_g[of i e] by (cases "f_i i e") auto
  then obtain f_i' where f_i': "\<And>i e. f_i i e = ennreal (f_i' i e)" and [simp]: "\<And>i e. 0 \<le> f_i' i e"
    by metis

  { fix i e
    obtain x y :: 'v where e: "e = (x, y)" by(cases e)
    have "k_i i (x, y) \<le> d_IN (k_i i) y" by (rule d_IN_ge_point)
    also have "\<dots> \<le> value_flow (residual_network (f_i i)) (k_i i)" by(rule IN_k_i)
    also have "\<dots> < \<top>" using value_k_i[of i] value_diff[of i]
      by(simp add: value_k_i value_f_i value_aux real less_top[symmetric])
    finally have "\<exists>x\<ge>0. k_i i e = ennreal x"
      by(cases "k_i i e")(auto simp add: e) }
  then obtain k_i' where k_i': "\<And>i e. k_i i e = ennreal (k_i' i e)" and k_i'_nonneg[simp]: "\<And>i e. 0 \<le> k_i' i e"
    by metis

  have wf_k: "(x, y) \<in> \<^bold>E \<Longrightarrow> k_i i (y, x) \<le> f_i i (x, y) + k_i i (x, y)" for i x y
    using flowD_capacity[OF k_i, of i "(y, x)"]
    by (auto split: if_split_asm dest: wf_residual_networkD[OF wf] elim: order_trans)

  have f_i'_0[simp]: "f_i' 0 = (\<lambda>_. 0)" using f_i_simps(1) by (simp del: f_i_simps add: fun_eq_iff f_i')

  have f_i'_Suc[simp]: "f_i' (Suc i) e =  (if e \<in> \<^bold>E then f_i' i e + (k_i' i e - k_i' i (prod.swap e)) else 0)" for i e
    using f_i_simps(2)[of i, unfolded fun_eq_iff, THEN spec, of e] wf_k[of "fst e" "snd e" i]
    by (auto simp del: f_i_simps ennreal_plus
             simp add: fun_eq_iff f_i' k_i' ennreal_plus[symmetric] ennreal_minus split: if_split_asm)

  have k_i'_le: "k_i' i e \<le> \<alpha>' / 2 ^ (Suc i)" for i e
  proof -
    obtain x y where e: "e = (x, y)" by(cases e)
    have "k_i' i (x, y) \<le> d_IN (k_i' i) y" by (rule d_IN_ge_point)
    also have "\<dots> \<le> value_flow (residual_network (f_i i)) (k_i' i)"
      using IN_k_i[of i y] by(simp add: k_i'[abs_def])
    also have "\<dots> = \<alpha>' / 2 ^ (Suc i)" using value_k_i[of i] value_diff[of i]
      by(simp add: value_f_i value_aux real k_i'[abs_def] field_simps ennreal_minus mult_le_cancel_left1)
    finally show ?thesis using e by simp
  qed

  have convergent: "convergent (\<lambda>i. f_i' i e)" for e
  proof(cases "\<alpha>' > 0")
    case False
    obtain x y where [simp]: "e = (x, y)" by(cases e)

    { fix i
      from False \<alpha>'_nonneg have "\<alpha>' = 0" by simp
      moreover have "f_i i (x, y) \<le> d_IN (f_i i) y" by (rule d_IN_ge_point)
      ultimately have "f_i i (x, y) = 0" using d_IN_i[of i y]
        by(simp add: value_f_i value_aux real) }
    thus ?thesis by(simp add: f_i' convergent_const)
  next
    case \<alpha>'_pos: True
    show ?thesis
    proof(rule real_Cauchy_convergent Cauchy_real_Suc_diff)+
      fix n
      have "\<bar>k_i' n e - k_i' n (prod.swap e)\<bar> \<le> \<bar>k_i' n e\<bar> + \<bar>k_i' n (prod.swap e)\<bar>"
        by (rule abs_triangle_ineq4)
      then have "\<bar>k_i' n e - k_i' n (prod.swap e)\<bar> \<le> \<alpha>' / 2 ^ n"
        using k_i'_le[of n e] k_i'_le[of n "prod.swap e"] by simp
      then have "\<bar>f_i' (Suc n) e - f_i' n e\<bar> \<le> \<alpha>' / 2 ^ n"
        using flowD_outside[OF fn.g] by (cases e) (auto simp: f_i')
      thus "\<bar>f_i' (Suc n) e - f_i' n e\<bar> \<le> \<alpha>' / 2 ^ n" by simp
    qed simp
  qed
  then obtain f' where f': "\<And>e. (\<lambda>i. f_i' i e) \<longlonglongrightarrow> f' e" unfolding convergent_def by metis
  hence f: "\<And>e. (\<lambda>i. f_i i e) \<longlonglongrightarrow> ennreal (f' e)" unfolding f_i' by simp

  have f'_nonneg: "0 \<le> f' e" for e
    by (rule LIMSEQ_le_const[OF f']) auto

  let ?k = "\<lambda>i x y. (k_i' i (x, y) - k_i' i (y, x)) * indicator \<^bold>E (x, y)"
  have sum_i': "f_i' i (x, y) = (\<Sum>j<i. ?k j x y)" for x y i
    by (induction i) auto

  have summable_nk: "summable (\<lambda>i. \<bar>?k i x y\<bar>)" for x y
  proof(rule summable_rabs_comparison_test)
    show "\<exists>N. \<forall>i\<ge>N. \<bar>?k i x y\<bar> \<le> \<alpha>' * (1 / 2) ^ i"
    proof (intro exI allI impI)
      fix i have "\<bar>?k i x y\<bar> \<le> k_i' i (x, y) + k_i' i (y, x)"
        by (auto intro!: abs_triangle_ineq4[THEN order_trans] split: split_indicator)
      also have "\<dots> \<le> \<alpha>' * (1 / 2) ^ i"
        using k_i'_le[of i "(x, y)"] k_i'_le[of i "(y, x)"] \<alpha>'_nonneg k_i'_nonneg[of i "(x, y)"] k_i'_nonneg[of i "(y, x)"]
        by(auto simp add: abs_real_def power_divide split: split_indicator)
      finally show "\<bar>?k i x y\<bar> \<le> \<alpha>' * (1 / 2) ^ i"
        by simp
    qed
    show "summable (\<lambda>i. \<alpha>' * (1 / 2) ^ i)"
      by(rule summable_mult complete_algebra_summable_geometric)+ simp
  qed
  hence summable_k: "summable (\<lambda>i. ?k i x y)" for x y by(auto intro: summable_norm_cancel)

  have suminf: "(\<Sum>i. (k_i' i (x, y) - k_i' i (y, x)) * indicator \<^bold>E (x, y)) = f' (x, y)" for x y
    by(rule LIMSEQ_unique[OF summable_LIMSEQ])(simp_all add: sum_i'[symmetric] f' summable_k)

  have flow: "flow \<Delta> f'"
  proof
    fix e
    have "f' e \<le> Sup {..capacity \<Delta> e}" using _ f
      by(rule Sup_lim)(simp add: flowD_capacity[OF fn.g])
    then show "f' e \<le> capacity \<Delta> e" by simp
  next
    fix x
    assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"

    have integrable_f_i: "integrable (count_space UNIV) (\<lambda>y. f_i' i (x, y))" for i
      using flowD_finite_OUT[OF fn.g x, of i] by(auto intro!: integrableI_bounded simp add: f_i' d_OUT_def less_top)
    have integrable_f_i': "integrable (count_space UNIV) (\<lambda>y. f_i' i (y, x))" for i
      using flowD_finite_IN[OF fn.g, of x i] x by(auto intro!: integrableI_bounded simp add: f_i' d_IN_def less_top)

    have integral_k_bounded: "(\<Sum>\<^sup>+ y. norm (?k i x y)) \<le> \<alpha>' / 2 ^ i" (is ?thesis1)
      and integral_k'_bounded: "(\<Sum>\<^sup>+ y. norm (?k i y x)) \<le> \<alpha>' / 2 ^ i" (is ?thesis2) for i
    proof -
      define b where "b = (\<Sum>\<^sup>+ y. k_i i (x, y) + k_i i (y, x))"
      have "b = d_OUT (k_i i) x + d_IN (k_i i) x" unfolding b_def
        by(subst nn_integral_add)(simp_all add: d_OUT_def d_IN_def)
      also have "d_OUT (k_i i) x = d_IN (k_i i) x" using k_i by(rule flowD_KIR)(simp_all add: x)
      also have "\<dots> + \<dots> \<le> value_flow \<Delta> (k_i i) + value_flow \<Delta> (k_i i)"
        using IN_k_i[of i x, simplified] by-(rule add_mono)
      also have "\<dots> \<le> \<alpha>' / 2 ^ i" using value_k_i[of i] value_diff[of i]
        by(simp add: value_aux value_f_i  field_simps ennreal_minus_if ennreal_plus_if mult_le_cancel_left1
                del: ennreal_plus)
      also have "(\<Sum>\<^sup>+ y\<in>UNIV. norm (?k i x y)) \<le> b" and "(\<Sum>\<^sup>+ y. norm (?k i y x)) \<le> b" unfolding b_def
        by(rule nn_integral_mono; simp add: abs_real_def k_i' ennreal_plus_if del:  ennreal_plus split: split_indicator)+
      ultimately show ?thesis1 ?thesis2 by(auto)
    qed

    have integrable_k: "integrable (count_space UNIV) (\<lambda>y. ?k i x y)"
      and integrable_k': "integrable (count_space UNIV) (\<lambda>y. ?k i y x)" for i
      using integral_k_bounded[of i] integral_k'_bounded[of i] real
      by(auto intro!: integrableI_bounded simp: less_top[symmetric] top_unique ennreal_divide_eq_top_iff)

    have summable'_k: "summable (\<lambda>i. \<integral> y. \<bar>?k i x y\<bar> \<partial>count_space UNIV)"
    proof(rule summable_comparison_test)
      have "\<bar>\<integral> y. \<bar>?k i x y\<bar> \<partial>count_space UNIV\<bar> \<le> \<alpha>' * (1 / 2) ^ i" for i
        using integral_norm_bound_ennreal[OF integrable_norm, OF integrable_k, of i] integral_k_bounded[of i]
        by(bestsimp simp add: real power_divide dest: order_trans)
      thus "\<exists>N. \<forall>i\<ge>N. norm (\<integral> y. \<bar>?k i x y\<bar> \<partial>count_space UNIV) \<le> \<alpha>' * (1 / 2) ^ i"
        by auto
      show "summable (\<lambda>i. \<alpha>' * (1 / 2) ^ i)"
        by(rule summable_mult complete_algebra_summable_geometric)+ simp
    qed
    have summable'_k': "summable (\<lambda>i. \<integral> y. \<bar>?k i y x\<bar> \<partial>count_space UNIV)"
    proof(rule summable_comparison_test)
      have "\<bar>\<integral> y. \<bar>?k i y x\<bar> \<partial>count_space UNIV\<bar> \<le> \<alpha>' * (1 / 2) ^ i" for i
        using integral_norm_bound_ennreal[OF integrable_norm, OF integrable_k', of i] integral_k'_bounded[of i]
        by(bestsimp simp add: real power_divide dest: order_trans)
      thus "\<exists>N. \<forall>i\<ge>N. norm (\<integral> y. \<bar>?k i y x\<bar> \<partial>count_space UNIV) \<le> \<alpha>' * (1 / 2) ^ i" by auto
      show "summable (\<lambda>i. \<alpha>' * (1 / 2) ^ i)"
        by(rule summable_mult complete_algebra_summable_geometric)+ simp
    qed

    have "(\<lambda>i. \<integral> y. ?k i x y \<partial>count_space UNIV) sums \<integral> y. (\<Sum>i. ?k i x y) \<partial>count_space UNIV"
      using integrable_k by(rule sums_integral)(simp_all add: summable_nk summable'_k)
    also have "\<dots> = \<integral> y. f' (x, y) \<partial>count_space UNIV" by(rule Bochner_Integration.integral_cong[OF refl])(rule suminf)
    finally have "(\<lambda>i. \<Sum>j<i. \<integral> y. ?k j x y \<partial>count_space UNIV) \<longlonglongrightarrow> \<dots>" unfolding sums_def .
    also have "(\<lambda>i. \<Sum>j<i. \<integral> y. ?k j x y \<partial>count_space UNIV) = (\<lambda>i. \<integral> y. f_i' i (x, y) \<partial>count_space UNIV)"
      unfolding sum_i' by(rule ext Bochner_Integration.integral_sum[symmetric] integrable_k)+
    finally have "(\<lambda>i. ennreal (\<integral> y. f_i' i (x, y) \<partial>count_space UNIV)) \<longlonglongrightarrow> ennreal (\<integral> y. f' (x, y) \<partial>count_space UNIV)" by simp
    also have "(\<lambda>i. ennreal (\<integral> y. f_i' i (x, y) \<partial>count_space UNIV)) = (\<lambda>i. d_OUT (f_i i) x)"
      unfolding d_OUT_def f_i' by(rule ext nn_integral_eq_integral[symmetric] integrable_f_i)+ simp
    also have "ennreal (\<integral> y. f' (x, y) \<partial>count_space UNIV) = d_OUT f' x"
      unfolding d_OUT_def by(rule nn_integral_eq_integral[symmetric])(simp_all add: f'_nonneg, simp add: suminf[symmetric] integrable_suminf integrable_k summable_nk summable'_k)
    also have "(\<lambda>i. d_OUT (f_i i) x) = (\<lambda>i. d_IN (f_i i) x)"
      using flowD_KIR[OF fn.g x] by(simp)
    finally have *: "(\<lambda>i. d_IN (f_i i) x) \<longlonglongrightarrow> d_OUT (\<lambda>x. ennreal (f' x)) x" .

    have "(\<lambda>i. \<integral> y. ?k i y x \<partial>count_space UNIV) sums \<integral> y. (\<Sum>i. ?k i y x) \<partial>count_space UNIV"
      using integrable_k' by(rule sums_integral)(simp_all add: summable_nk summable'_k')
    also have "\<dots> = \<integral> y. f' (y, x) \<partial>count_space UNIV" by(rule Bochner_Integration.integral_cong[OF refl])(rule suminf)
    finally have "(\<lambda>i. \<Sum>j<i. \<integral> y. ?k j y x \<partial>count_space UNIV) \<longlonglongrightarrow> \<dots>" unfolding sums_def .
    also have "(\<lambda>i. \<Sum>j<i. \<integral> y. ?k j y x \<partial>count_space UNIV) = (\<lambda>i. \<integral> y. f_i' i (y, x) \<partial>count_space UNIV)"
      unfolding sum_i' by(rule ext Bochner_Integration.integral_sum[symmetric] integrable_k')+
    finally have "(\<lambda>i. ennreal (\<integral> y. f_i' i (y, x) \<partial>count_space UNIV)) \<longlonglongrightarrow> ennreal (\<integral> y. f' (y, x) \<partial>count_space UNIV)" by simp
    also have "(\<lambda>i. ennreal (\<integral> y. f_i' i (y, x) \<partial>count_space UNIV)) = (\<lambda>i. d_IN (f_i i) x)"
      unfolding d_IN_def f_i' by(rule ext nn_integral_eq_integral[symmetric] integrable_f_i')+ simp
    also have "ennreal (\<integral> y. f' (y, x) \<partial>count_space UNIV) = d_IN f' x"
      unfolding d_IN_def by(rule nn_integral_eq_integral[symmetric])(simp_all add: f'_nonneg, simp add: suminf[symmetric] integrable_suminf integrable_k' summable_nk summable'_k')
    finally show "d_OUT f' x = d_IN f' x" using * by(blast intro: LIMSEQ_unique)
  qed
  moreover
  { have "incseq (\<lambda>i. value_flow \<Delta> (f_i i))"
      by(rule incseq_SucI)(simp add: value_aux value_f_i real field_simps \<alpha>'_nonneg ennreal_leI del: f_i_simps)
    then have "(\<lambda>i. value_flow \<Delta> (f_i i)) \<longlonglongrightarrow> (SUP i. value_flow \<Delta> (f_i i))" by(rule LIMSEQ_SUP)
    also have "(SUP i. value_flow \<Delta> (f_i i)) = \<alpha>"
    proof -
      have "\<alpha> - (SUP i. value_flow \<Delta> (f_i i)) = (INF i. \<alpha> - value_flow \<Delta> (f_i i))"
        by(simp add: ennreal_SUP_const_minus real)
      also have "\<alpha> - value_flow \<Delta> (f_i i) = \<alpha>' / 2 ^ i" for i
        by(simp add: value_f_i value_aux real ennreal_minus_if field_simps mult_le_cancel_left1)
      hence "(INF i. \<alpha> - value_flow \<Delta> (f_i i)) = (INF i. ennreal (\<alpha>' / 2  ^ i))"
        by(auto intro: INF_cong)
      also have "\<dots> = 0"
      proof(rule LIMSEQ_unique)
        show "(\<lambda>i. \<alpha>' / 2 ^ i) \<longlonglongrightarrow> (INF i. ennreal (\<alpha>' / 2  ^ i))"
          by(rule LIMSEQ_INF)(simp add: field_simps real decseq_SucI)
      qed(simp add: LIMSEQ_divide_realpow_zero real ennreal_0[symmetric] del: ennreal_0)
      finally show "(SUP i. value_flow \<Delta> (f_i i)) = \<alpha>"
        apply (intro antisym)
        apply (auto simp: \<alpha>_def intro!: SUP_mono fn.g) []
        apply (rule ennreal_minus_eq_0)
        apply assumption
        done
    qed
    also have "(\<lambda>i. value_flow \<Delta> (f_i i)) \<longlonglongrightarrow> value_flow \<Delta> f'"
      by(simp add: value_flow[OF flow source_out] value_flow[OF fn.g source_out] f)
    ultimately have "value_flow \<Delta> f' = \<alpha>" by(blast intro: LIMSEQ_unique) }
  note value_f = this
  moreover {
    fix x
    have "d_IN f' x = \<integral>\<^sup>+ y. liminf (\<lambda>i. f_i i (y, x)) \<partial>count_space UNIV" unfolding d_IN_def using f
      by(simp add: tendsto_iff_Liminf_eq_Limsup)
    also have "\<dots> \<le> liminf (\<lambda>i. d_IN (f_i i) x)" unfolding d_IN_def
      by(rule nn_integral_liminf)(simp_all add:)
    also have "\<dots> \<le> liminf (\<lambda>i. \<alpha>)" using d_IN_i[of _ x] fn.g
      by(auto intro!: Liminf_mono SUP_upper2 eventually_sequentiallyI simp add: \<alpha>_def)
    also have "\<dots> = value_flow \<Delta> f'" using value_f by(simp add: Liminf_const)
    also note calculation
  } ultimately show ?thesis by blast
qed

theorem ex_max_flow'': \<comment> \<open>eliminate assumption of no antiparallel edges using locale @{const wf_residual_network}\<close>
  assumes source_out: "\<And>y. edge \<Delta> (source \<Delta>) y \<longleftrightarrow> y = x"
  and nontrivial: "\<^bold>E \<noteq> {}"
  and real: "\<alpha> = ennreal \<alpha>'" and nn[simp]: "0 \<le> \<alpha>'"
  shows "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = \<alpha> \<and> (\<forall>x. d_IN f x \<le> value_flow \<Delta> f)"
proof -
  interpret antiparallel_edges \<Delta> ..
  interpret \<Delta>'': flow_attainability \<Delta>''
    by(rule \<Delta>''_flow_attainability flow_attainability.axioms(2))+unfold_locales
  have wf_\<Delta>'': "\<Delta>''.wf_residual_network"
    by(rule \<Delta>''_wf_residual_network; simp add: no_loop)

  have source_out': "edge \<Delta>'' (source \<Delta>'') y \<longleftrightarrow> y = Edge (source \<Delta>) x" for y
    by(auto simp add: source_out)
  have nontrivial': "\<^bold>V\<^bsub>\<Delta>''\<^esub> - {source \<Delta>'', sink \<Delta>''} \<noteq> {}" using nontrivial by(auto simp add: "\<^bold>V_\<Delta>''")

  have "(SUP g \<in> {g. flow \<Delta>'' g}. value_flow \<Delta>'' g) = (SUP g \<in> {g. flow \<Delta> g}. value_flow \<Delta> g)" (is "?lhs = ?rhs")
  proof(intro antisym SUP_least; unfold mem_Collect_eq)
    fix g
    assume g: "flow \<Delta>'' g"
    hence "value_flow \<Delta>'' g = value_flow \<Delta> (collect g)" by(simp add: value_collect)
    also { from g have "flow \<Delta> (collect g)" by simp }
    then have "\<dots> \<le> ?rhs" by(blast intro: SUP_upper2)
    finally show "value_flow \<Delta>'' g \<le> \<dots>" .
  next
    fix g
    assume g: "flow \<Delta> g"
    hence "value_flow \<Delta> g = value_flow \<Delta>'' (split g)" by simp
    also { from g have "flow \<Delta>'' (split g)" by simp }
    then have "\<dots> \<le> ?lhs" by(blast intro: SUP_upper2)
    finally show "value_flow \<Delta> g \<le> ?lhs" .
  qed
  with real have eq: "(SUP g \<in> {g. flow \<Delta>'' g}. value_flow \<Delta>'' g) = ennreal \<alpha>'" by(simp add: \<alpha>_def)
  from \<Delta>''.ex_max_flow'[OF wf_\<Delta>'' source_out' nontrivial' eq]
  obtain f where f: "flow \<Delta>'' f"
    and "value_flow \<Delta>'' f = \<alpha>"
    and IN: "\<And>x. d_IN f x \<le> value_flow \<Delta>'' f" unfolding eq real using nn by blast
  hence "flow \<Delta> (collect f)" and "value_flow \<Delta> (collect f) = \<alpha>" by(simp_all add: value_collect)
  moreover {
    fix x
    have "d_IN (collect f) x = (\<Sum>\<^sup>+ y\<in>range (\<lambda>y. Edge y x). f (y, Vertex x))"
      by(simp add: nn_integral_count_space_reindex d_IN_def)
    also have "\<dots> \<le> d_IN f (Vertex x)" unfolding d_IN_def
      by (auto intro!: nn_integral_mono simp add: nn_integral_count_space_indicator split: split_indicator)
    also have "\<dots> \<le> value_flow \<Delta> (collect f)" using IN[of "Vertex x"] f by(simp add: value_collect)
    also note calculation }
  ultimately show ?thesis by blast
qed

context begin \<comment> \<open>We eliminate the assumption of only one edge leaving the source by introducing a new source vertex.\<close>
private datatype (plugins del: transfer size) 'v' node = SOURCE | Inner (inner: 'v')

private lemma not_Inner_conv: "x \<notin> range Inner \<longleftrightarrow> x = SOURCE"
by(cases x) auto

private lemma inj_on_Inner [simp]: "inj_on Inner A"
by(simp add: inj_on_def)

private inductive edge' :: "'v node \<Rightarrow> 'v node \<Rightarrow> bool"
where
  SOURCE: "edge' SOURCE (Inner (source \<Delta>))"
| Inner: "edge \<Delta> x y \<Longrightarrow> edge' (Inner x) (Inner y)"

private inductive_simps edge'_simps [simp]:
  "edge' SOURCE x"
  "edge' (Inner y) x"
  "edge' y SOURCE"
  "edge' y (Inner x)"

private fun capacity' :: "'v node flow"
where
  "capacity' (SOURCE, Inner x) = (if x = source \<Delta> then \<alpha> else 0)"
| "capacity' (Inner x, Inner y) = capacity \<Delta> (x, y)"
| "capacity' _ = 0"

private lemma capacity'_source_in [simp]: "capacity' (y, Inner (source \<Delta>)) = (if y = SOURCE then \<alpha> else 0)"
by(cases y)(simp_all add: capacity_outside source_in)

private definition \<Delta>' :: "'v node network"
where "\<Delta>' = \<lparr>edge = edge', capacity = capacity', source = SOURCE, sink = Inner (sink \<Delta>)\<rparr>"

private lemma \<Delta>'_sel [simp]:
  "edge \<Delta>' = edge'"
  "capacity \<Delta>' = capacity'"
  "source \<Delta>' = SOURCE"
  "sink \<Delta>' = Inner (sink \<Delta>)"
by(simp_all add: \<Delta>'_def)

private lemma "\<^bold>E_\<Delta>'": "\<^bold>E\<^bsub>\<Delta>'\<^esub> = {(SOURCE, Inner (source \<Delta>))} \<union> (\<lambda>(x, y). (Inner x, Inner y)) ` \<^bold>E"
by(auto elim: edge'.cases)

private lemma \<Delta>'_countable_network:
  assumes "\<alpha> \<noteq> \<top>"
  shows "countable_network \<Delta>'"
proof
  show "countable \<^bold>E\<^bsub>\<Delta>'\<^esub>" unfolding "\<^bold>E_\<Delta>'" by simp
  show "source \<Delta>' \<noteq> sink \<Delta>'" by simp
  show "capacity \<Delta>' e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Delta>'\<^esub>" for e using that unfolding "\<^bold>E_\<Delta>'"
    by(cases e rule: capacity'.cases)(auto intro: capacity_outside)
  show "capacity \<Delta>' e \<noteq> \<top>" for e by(cases e rule: capacity'.cases)(simp_all add: assms)
qed

private lemma \<Delta>'_flow_attainability:
  assumes "\<alpha> \<noteq> \<top>"
  shows "flow_attainability \<Delta>'"
proof -
  interpret \<Delta>': countable_network \<Delta>' using assms by(rule \<Delta>'_countable_network)
  show ?thesis
  proof
    show "d_IN (capacity \<Delta>') x \<noteq> \<top> \<or> d_OUT (capacity \<Delta>') x \<noteq> \<top>" if sink: "x \<noteq> sink \<Delta>'" for x
    proof(cases x)
      case (Inner x')
      consider (source) "x' = source \<Delta>" | (IN) "x' \<noteq> source \<Delta>" "d_IN (capacity \<Delta>) x' \<noteq> \<top>" | (OUT) "d_OUT (capacity \<Delta>) x' \<noteq> \<top>"
        using finite_capacity[of x'] sink Inner by(auto)
      thus ?thesis
      proof(cases)
        case source
        with Inner have "d_IN (capacity \<Delta>') x = (\<Sum>\<^sup>+ y. \<alpha> * indicator {SOURCE :: 'v node} y)"
          unfolding d_IN_def by(intro nn_integral_cong)(simp split: split_indicator)
        also have "\<dots> = \<alpha>" by(simp add: max_def)
        finally show ?thesis using assms by simp
      next
        case IN
        with Inner have "d_IN (capacity \<Delta>') x = (\<Sum>\<^sup>+ y\<in>range Inner. capacity \<Delta> (node.inner y, x'))"
          by(auto simp add: d_IN_def nn_integral_count_space_indicator not_Inner_conv intro!: nn_integral_cong split: split_indicator)
        also have "\<dots> = d_IN (capacity \<Delta>) x'" unfolding d_IN_def
          by(simp add: nn_integral_count_space_reindex)
        finally show ?thesis using Inner sink IN by(simp)
      next
        case OUT
        from Inner have "d_OUT (capacity \<Delta>') x = (\<Sum>\<^sup>+ y\<in>range Inner. capacity \<Delta> (x', node.inner y))"
          by(auto simp add: d_OUT_def nn_integral_count_space_indicator not_Inner_conv intro!: nn_integral_cong split: split_indicator)
        also have "\<dots> = d_OUT (capacity \<Delta>) x'" by(simp add: d_OUT_def nn_integral_count_space_reindex)
        finally show ?thesis using OUT by auto
      qed
    qed(simp add: d_IN_def)
    show "\<not> edge \<Delta>' x x" for x by(cases x)(simp_all add: no_loop)
    show "\<not> edge \<Delta>' x (source \<Delta>')" for x by simp
  qed
qed

private fun lift :: "'v flow \<Rightarrow> 'v node flow"
where
  "lift f (SOURCE, Inner y) = (if y = source \<Delta> then value_flow \<Delta> f else 0)"
| "lift f (Inner x, Inner y) = f (x, y)"
| "lift f _ = 0"

private lemma d_OUT_lift_Inner [simp]: "d_OUT (lift f) (Inner x) = d_OUT f x" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>\<^sup>+ y\<in>range Inner. lift f (Inner x, y))"
    by(auto simp add: d_OUT_def nn_integral_count_space_indicator not_Inner_conv intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ?rhs" by(simp add: nn_integral_count_space_reindex d_OUT_def)
  finally show ?thesis .
qed

private lemma d_OUT_lift_SOURCE [simp]: "d_OUT (lift f) SOURCE = value_flow \<Delta> f" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>\<^sup>+ y. lift f (SOURCE, y) * indicator {Inner (source \<Delta>)} y)"
    unfolding d_OUT_def by(rule nn_integral_cong)(case_tac x; simp)
  also have "\<dots> = ?rhs" by(simp add: nn_integral_count_space_indicator max_def)
  finally show ?thesis .
qed

private lemma d_IN_lift_Inner [simp]:
  assumes "x \<noteq> source \<Delta>"
  shows "d_IN (lift f) (Inner x) = d_IN f x" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>\<^sup>+ y\<in>range Inner. lift f (y, Inner x))" using assms
    by(auto simp add: d_IN_def nn_integral_count_space_indicator not_Inner_conv intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ?rhs" by(simp add: nn_integral_count_space_reindex d_IN_def)
  finally show ?thesis .
qed

private lemma d_IN_lift_source [simp]: "d_IN (lift f) (Inner (source \<Delta>)) = value_flow \<Delta> f + d_IN f (source \<Delta>)" (is "?lhs = ?rhs")
proof -
  have "?lhs = (\<Sum>\<^sup>+ y. lift f (y, Inner (source \<Delta>)) * indicator {SOURCE} y) + (\<Sum>\<^sup>+ y\<in>range Inner. lift f (y, Inner (source \<Delta>)))"
    (is "_ = ?SOURCE + ?rest")
    unfolding d_IN_def
    apply(subst nn_integral_count_space_indicator, simp)
    apply(subst nn_integral_add[symmetric])
    apply(auto simp add: AE_count_space max_def not_Inner_conv split: split_indicator intro!: nn_integral_cong)
    done
  also have "?rest = d_IN f (source \<Delta>)" by(simp add: nn_integral_count_space_reindex d_IN_def)
  also have "?SOURCE = value_flow \<Delta> f"
    by(simp add: max_def one_ennreal_def[symmetric] )
  finally show ?thesis .
qed

private lemma flow_lift [simp]:
  assumes "flow \<Delta> f"
  shows "flow \<Delta>' (lift f)"
proof
  show "lift f e \<le> capacity \<Delta>' e" for e
    by(cases e rule: capacity'.cases)(auto intro: flowD_capacity[OF assms] simp add: \<alpha>_def intro: SUP_upper2 assms)

  fix x
  assume x: "x \<noteq> source \<Delta>'" "x \<noteq> sink \<Delta>'"
  then obtain x' where x': "x = Inner x'" by(cases x) auto
  then show "KIR (lift f) x" using x
    by(cases "x' = source \<Delta>")(auto simp add: flowD_source_IN[OF assms] dest: flowD_KIR[OF assms])
qed

private abbreviation (input) unlift :: "'v node flow \<Rightarrow> 'v flow"
where "unlift f \<equiv> (\<lambda>(x, y). f (Inner x, Inner y))"

private lemma flow_unlift [simp]:
  assumes f: "flow \<Delta>' f"
  shows "flow \<Delta> (unlift f)"
proof
  show "unlift f e \<le> capacity \<Delta> e" for e using flowD_capacity[OF f, of "map_prod Inner Inner e"]
    by(cases e)(simp)
next
  fix x
  assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  have "d_OUT (unlift f) x = (\<Sum>\<^sup>+ y\<in>range Inner. f (Inner x, y))"
    by(simp add: nn_integral_count_space_reindex d_OUT_def)
  also have "\<dots> = d_OUT f (Inner x)" using flowD_capacity[OF f, of "(Inner x, SOURCE)"]
    by(auto simp add: nn_integral_count_space_indicator d_OUT_def not_Inner_conv intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = d_IN f (Inner x)" using x flowD_KIR[OF f, of "Inner x"] by(simp)
  also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. f (y, Inner x))"
    using x flowD_capacity[OF f, of "(SOURCE, Inner x)"]
    by(auto simp add: nn_integral_count_space_indicator d_IN_def not_Inner_conv intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = d_IN (unlift f) x" by(simp add: nn_integral_count_space_reindex d_IN_def)
  finally show "KIR (unlift f) x" .
qed

private lemma value_unlift:
  assumes f: "flow \<Delta>' f"
  shows "value_flow \<Delta> (unlift f) = value_flow \<Delta>' f"
proof -
  have "value_flow \<Delta> (unlift f) = (\<Sum>\<^sup>+ y\<in>range Inner. f (Inner (source \<Delta>), y))"
    by(simp add: nn_integral_count_space_reindex d_OUT_def)
  also have "\<dots> = d_OUT f (Inner (source \<Delta>))" using flowD_capacity[OF f, of "(Inner (source \<Delta>), SOURCE)"]
    by(auto simp add: nn_integral_count_space_indicator d_OUT_def not_Inner_conv intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = d_IN f (Inner (source \<Delta>))" using flowD_KIR[OF f, of "Inner (source \<Delta>)"] by(simp)
  also have "\<dots> = (\<Sum>\<^sup>+ y. f (y, Inner (source \<Delta>)) * indicator {SOURCE} y)"
    unfolding d_IN_def using flowD_capacity[OF f, of "(x, Inner (source \<Delta>))" for x]
    by(intro nn_integral_cong)(auto intro!: antisym split: split_indicator if_split_asm elim: meta_allE)
  also have "\<dots> = f (SOURCE, Inner (source \<Delta>))" by simp
  also have "\<dots> = (\<Sum>\<^sup>+ y. f (SOURCE, y) * indicator {Inner (source \<Delta>)} y)"
    by(simp add: one_ennreal_def[symmetric])
  also have "\<dots> = value_flow \<Delta>' f" unfolding d_OUT_def
    unfolding d_OUT_def using flowD_capacity[OF f, of "(SOURCE, Inner x)" for x] flowD_capacity[OF f, of "(SOURCE, SOURCE)"]
    apply(intro nn_integral_cong)
    apply(case_tac x)
    apply(auto intro!: antisym split: split_indicator if_split_asm elim: meta_allE)
    done
  finally show ?thesis .
qed

theorem ex_max_flow:
  "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = \<alpha> \<and> (\<forall>x. d_IN f x \<le> value_flow \<Delta> f)"
proof(cases "\<alpha>")
  case (real \<alpha>')
  hence \<alpha>: "\<alpha> \<noteq> \<top>" by simp
  then interpret \<Delta>': flow_attainability \<Delta>' by(rule \<Delta>'_flow_attainability)

  have source_out: "edge \<Delta>' (source \<Delta>') y \<longleftrightarrow> y = Inner (source \<Delta>)" for y by(auto)
  have nontrivial: "\<^bold>E\<^bsub>\<Delta>'\<^esub> \<noteq> {}" by(auto intro: edge'.intros)

  have eq: "(SUP g \<in> {g. flow \<Delta>' g}. value_flow \<Delta>' g) = (SUP g \<in> {g. flow \<Delta> g}. value_flow \<Delta> g)" (is "?lhs = ?rhs")
  proof(intro antisym SUP_least; unfold mem_Collect_eq)
    fix g
    assume g: "flow \<Delta>' g"
    hence "value_flow \<Delta>' g = value_flow \<Delta> (unlift g)" by(simp add: value_unlift)
    also { from g have "flow \<Delta> (unlift g)" by simp }
    then have "\<dots> \<le> ?rhs" by(blast intro: SUP_upper2)
    finally show "value_flow \<Delta>' g \<le> \<dots>" .
  next
    fix g
    assume g: "flow \<Delta> g"
    hence "value_flow \<Delta> g = value_flow \<Delta>' (lift g)" by simp
    also { from g have "flow \<Delta>' (lift g)" by simp }
    then have "\<dots> \<le> ?lhs" by(blast intro: SUP_upper2)
    finally show "value_flow \<Delta> g \<le> ?lhs" .
  qed
  also have "\<dots> = ennreal \<alpha>'" using real by(simp add: \<alpha>_def)
  finally obtain f where f: "flow \<Delta>' f"
    and value_f: "value_flow \<Delta>' f = (\<Squnion>g\<in>{g. flow \<Delta>' g}. value_flow \<Delta>' g)"
    and IN_f: "\<And>x. d_IN f x \<le> value_flow \<Delta>' f"
    using \<open>0 \<le> \<alpha>'\<close> by(blast dest: \<Delta>'.ex_max_flow''[OF source_out nontrivial])
  have "flow \<Delta> (unlift f)" using f by simp
  moreover have "value_flow \<Delta> (unlift f) = \<alpha>" using f eq value_f by(simp add: value_unlift \<alpha>_def)
  moreover {
    fix x
    have "d_IN (unlift f) x = (\<Sum>\<^sup>+ y\<in>range Inner. f (y, Inner x))"
      by(simp add: nn_integral_count_space_reindex d_IN_def)
    also have "\<dots> \<le> d_IN f (Inner x)" unfolding d_IN_def
      by(auto intro!: nn_integral_mono simp add: nn_integral_count_space_indicator split: split_indicator)
    also have "\<dots> \<le> value_flow \<Delta> (unlift f)" using IN_f[of "Inner x"] f by(simp add: value_unlift)
    also note calculation }
  ultimately show ?thesis by blast
next
  case top
  show ?thesis
  proof(cases "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = \<top>")
    case True
    with top show ?thesis by auto
  next
    case False
    hence real: "\<forall>f. \<alpha> = \<top> \<longrightarrow> flow \<Delta> f \<longrightarrow> value_flow \<Delta> f < \<alpha>" using top by (auto simp: less_top)
    { fix i
      have "2 * 2 ^ i < \<alpha>" using top by (simp_all add: ennreal_mult_less_top power_less_top_ennreal)
      from flow_by_value[OF this real] have "\<exists>f. flow \<Delta> f \<and> value_flow \<Delta> f = 2 * 2 ^ i" by blast }
    then obtain f_i where f_i: "\<And>i. flow \<Delta> (f_i i)"
      and value_i: "\<And>i. value_flow \<Delta> (f_i i) = 2 * 2 ^ i" by metis
    define f where "f e = (\<Sum>\<^sup>+ i. f_i i e / (2 * 2 ^ i))" for e
    have "flow \<Delta> f"
    proof
      fix e
      have "f e \<le> (\<Sum>\<^sup>+ i. (SUP i. f_i i e) / (2 * 2 ^ i))" unfolding f_def
        by(rule nn_integral_mono)(auto intro!: divide_right_mono_ennreal SUP_upper)
      also have "\<dots> = (SUP i. f_i i e) / 2 * (\<Sum>\<^sup>+ i. 1 / 2 ^ i)"
        apply(subst nn_integral_cmult[symmetric])
        apply(auto intro!: nn_integral_cong intro: SUP_upper2
          simp: divide_ennreal_def ennreal_inverse_mult power_less_top_ennreal mult_ac)
        done
      also have "(\<Sum>\<^sup>+ i. 1 / 2 ^ i) = (\<Sum>i. ennreal ((1 / 2) ^ i))"
        by(simp add: nn_integral_count_space_nat power_divide divide_ennreal[symmetric] ennreal_power[symmetric])
      also have "\<dots> = ennreal (\<Sum>i. (1 / 2) ^ i)"
        by(intro suminf_ennreal2 complete_algebra_summable_geometric) simp_all
      also have "\<dots> = 2" by(subst suminf_geometric; simp)
      also have "(SUP i. f_i i e) / 2 * 2 = (SUP i. f_i i e)"
        by (simp add: ennreal_divide_times)
      also have "\<dots> \<le> capacity \<Delta> e" by(rule SUP_least)(rule flowD_capacity[OF f_i])
      finally show "f e \<le> capacity \<Delta> e" .

      fix x
      assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
      have "d_OUT f x = (\<Sum>\<^sup>+ i\<in>UNIV. \<Sum>\<^sup>+ y. f_i i (x, y) / (2 * 2 ^ i))"
        unfolding d_OUT_def f_def
        by(subst nn_integral_snd_count_space[where f="case_prod _", simplified])
          (simp add: nn_integral_fst_count_space[where f="case_prod _", simplified])
      also have "\<dots> = (\<Sum>\<^sup>+ i. d_OUT (f_i i) x / (2 * 2 ^ i))" unfolding d_OUT_def
        by(simp add: nn_integral_divide)
      also have "\<dots> = (\<Sum>\<^sup>+ i. d_IN (f_i i) x / (2 * 2 ^ i))" by(simp add: flowD_KIR[OF f_i, OF x])
      also have "\<dots> = (\<Sum>\<^sup>+ i\<in>UNIV. \<Sum>\<^sup>+ y. f_i i (y, x) / (2 * 2 ^ i))"
        by(simp add: nn_integral_divide d_IN_def)
      also have "\<dots> = d_IN f x" unfolding d_IN_def f_def
        by(subst nn_integral_snd_count_space[where f="case_prod _", simplified])
          (simp add: nn_integral_fst_count_space[where f="case_prod _", simplified])
      finally show "KIR f x" .
    qed
    moreover {
      have "value_flow \<Delta> f = (\<Sum>\<^sup>+ i. value_flow \<Delta> (f_i i) / (2 * 2 ^ i))"
        unfolding d_OUT_def f_def
        by(subst nn_integral_snd_count_space[where f="case_prod _", simplified])
          (simp add: nn_integral_fst_count_space[where f="case_prod _", simplified] nn_integral_divide[symmetric])
      also have "\<dots> = \<top>"
        by(simp add: value_i ennreal_mult_less_top power_less_top_ennreal)
      finally have "value_flow \<Delta> f = \<top>" .
    }
    ultimately show ?thesis using top by auto
  qed
qed

end

end

end

section \<open>Webs and currents\<close>

record 'v web = "'v graph" +
  weight :: "'v \<Rightarrow> ennreal"
  A :: "'v set"
  B :: "'v set"

lemma vertex_weight_update [simp]: "vertex (weight_update f \<Gamma>) = vertex \<Gamma>"
by(simp add: vertex_def fun_eq_iff)

type_synonym 'v current = "'v edge \<Rightarrow> ennreal"

inductive current :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> bool"
  for \<Gamma> f
where
  current:
  "\<lbrakk> \<And>x. d_OUT f x \<le> weight \<Gamma> x;
     \<And>x. d_IN f x \<le> weight \<Gamma> x;
     \<And>x. x \<notin> A \<Gamma> \<Longrightarrow> d_OUT f x \<le> d_IN f x;
     \<And>a. a \<in> A \<Gamma> \<Longrightarrow> d_IN f a = 0;
     \<And>b. b \<in> B \<Gamma> \<Longrightarrow> d_OUT f b = 0;
     \<And>e. e \<notin> \<^bold>E\<^bsub>\<Gamma>\<^esub> \<Longrightarrow> f e = 0 \<rbrakk>
  \<Longrightarrow> current \<Gamma> f"

lemma currentD_weight_OUT: "current \<Gamma> f \<Longrightarrow> d_OUT f x \<le> weight \<Gamma> x"
by(simp add: current.simps)

lemma currentD_weight_IN: "current \<Gamma> f \<Longrightarrow> d_IN f x \<le> weight \<Gamma> x"
by(simp add: current.simps)

lemma currentD_OUT_IN: "\<lbrakk> current \<Gamma> f; x \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f x \<le> d_IN f x"
by(simp add: current.simps)

lemma currentD_IN: "\<lbrakk> current \<Gamma> f; a \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> d_IN f a = 0"
by(simp add: current.simps)

lemma currentD_OUT: "\<lbrakk> current \<Gamma> f; b \<in> B \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f b = 0"
by(simp add: current.simps)

lemma currentD_outside: "\<lbrakk> current \<Gamma> f; \<not> edge \<Gamma> x y \<rbrakk> \<Longrightarrow> f (x, y) = 0"
by(blast elim: current.cases)

lemma currentD_outside': "\<lbrakk> current \<Gamma> f; e \<notin> \<^bold>E\<^bsub>\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> f e = 0"
by(blast elim: current.cases)

lemma currentD_OUT_eq_0:
  assumes "current \<Gamma> f"
  shows "d_OUT f x = 0 \<longleftrightarrow> (\<forall>y. f (x, y) = 0)"
by(simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0)

lemma currentD_IN_eq_0:
  assumes "current \<Gamma> f"
  shows "d_IN f x = 0 \<longleftrightarrow> (\<forall>y. f (y, x) = 0)"
by(simp add: d_IN_def nn_integral_0_iff emeasure_count_space_eq_0)

lemma current_support_flow:
  fixes \<Gamma> (structure)
  assumes "current \<Gamma> f"
  shows "support_flow f \<subseteq> \<^bold>E"
using currentD_outside[OF assms] by(auto simp add: support_flow.simps intro: ccontr)

lemma currentD_outside_IN: "\<lbrakk> current \<Gamma> f; x \<notin> \<^bold>V\<^bsub>\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> d_IN f x = 0"
by(auto simp add: d_IN_def vertex_def nn_integral_0_iff  AE_count_space emeasure_count_space_eq_0 dest: currentD_outside)

lemma currentD_outside_OUT: "\<lbrakk> current \<Gamma> f; x \<notin> \<^bold>V\<^bsub>\<Gamma>\<^esub> \<rbrakk> \<Longrightarrow> d_OUT f x = 0"
by(auto simp add: d_OUT_def vertex_def nn_integral_0_iff  AE_count_space emeasure_count_space_eq_0 dest: currentD_outside)

lemma currentD_weight_in: "current \<Gamma> h \<Longrightarrow> h (x, y) \<le> weight \<Gamma> y"
  by (metis order_trans d_IN_ge_point currentD_weight_IN)

lemma currentD_weight_out: "current \<Gamma> h \<Longrightarrow> h (x, y) \<le> weight \<Gamma> x"
  by (metis order_trans d_OUT_ge_point currentD_weight_OUT)

lemma current_leI:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and le: "\<And>e. g e \<le> f e"
  and OUT_IN: "\<And>x. x \<notin> A \<Gamma> \<Longrightarrow> d_OUT g x \<le> d_IN g x"
  shows "current \<Gamma> g"
proof
  show "d_OUT g x \<le> weight \<Gamma> x" for x
    using d_OUT_mono[of g x f, OF le] currentD_weight_OUT[OF f] by(rule order_trans)
  show "d_IN g x \<le> weight \<Gamma> x" for x
    using d_IN_mono[of g x f, OF le] currentD_weight_IN[OF f] by(rule order_trans)
  show "d_IN g a = 0" if "a \<in> A \<Gamma>" for a
    using d_IN_mono[of g a f, OF le] currentD_IN[OF f that] by auto
  show "d_OUT g b = 0" if "b \<in> B \<Gamma>" for b
    using d_OUT_mono[of g b f, OF le] currentD_OUT[OF f that] by auto
  show "g e = 0" if "e \<notin> \<^bold>E" for e
    using currentD_outside'[OF f that] le[of e] by simp
qed(blast intro: OUT_IN)+

lemma current_weight_mono:
  "\<lbrakk> current \<Gamma> f; edge \<Gamma> = edge \<Gamma>'; A \<Gamma> = A \<Gamma>'; B \<Gamma> = B \<Gamma>'; \<And>x. weight \<Gamma> x \<le> weight \<Gamma>' x \<rbrakk>
  \<Longrightarrow> current \<Gamma>' f"
by(auto 4 3 elim!: current.cases intro!: current.intros intro: order_trans)

abbreviation (input) zero_current :: "'v current"
where "zero_current \<equiv> \<lambda>_. 0"

lemma SINK_0 [simp]: "SINK zero_current = UNIV"
by(auto simp add: SINK.simps)

lemma current_0 [simp]: "current \<Gamma> zero_current"
by(auto simp add: current.simps)

inductive web_flow :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> bool"
  for \<Gamma> (structure) and f
where
  web_flow: "\<lbrakk> current \<Gamma> f; \<And>x. \<lbrakk> x \<in> \<^bold>V; x \<notin> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> KIR f x \<rbrakk> \<Longrightarrow> web_flow \<Gamma> f"

lemma web_flowD_current: "web_flow \<Gamma> f \<Longrightarrow> current \<Gamma> f"
by(erule web_flow.cases)

lemma web_flowD_KIR: "\<lbrakk> web_flow \<Gamma> f; x \<notin> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> KIR f x"
apply(cases "x \<in> \<^bold>V\<^bsub>\<Gamma>\<^esub>")
 apply(fastforce elim!: web_flow.cases)
apply(auto simp add: vertex_def d_OUT_def d_IN_def elim!: web_flow.cases)
apply(subst (1 2) currentD_outside[of _ f]; auto)
done

subsection \<open>Saturated and terminal vertices\<close>

inductive_set SAT :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v set"
  for \<Gamma> f
where
  A: "x \<in> A \<Gamma> \<Longrightarrow> x \<in> SAT \<Gamma> f"
| IN: "d_IN f x \<ge> weight \<Gamma> x \<Longrightarrow> x \<in> SAT \<Gamma> f"
  \<comment> \<open>We use @{text "\<ge> weight"} such that @{text SAT} is monotone w.r.t. increasing currents\<close>

lemma SAT_0 [simp]: "SAT \<Gamma> zero_current = A \<Gamma> \<union> {x. weight \<Gamma> x \<le> 0}"
by(auto simp add: SAT.simps)

lemma SAT_mono:
  assumes "\<And>e. f e \<le> g e"
  shows "SAT \<Gamma> f \<subseteq> SAT \<Gamma> g"
proof
  fix x
  assume "x \<in> SAT \<Gamma> f"
  thus "x \<in> SAT \<Gamma> g"
  proof cases
    case IN
    also have "d_IN f x \<le> d_IN g x" using assms by(rule d_IN_mono)
    finally show ?thesis ..
  qed(rule SAT.A)
qed

lemma SAT_Sup_upper: "f \<in> Y \<Longrightarrow> SAT \<Gamma> f \<subseteq> SAT \<Gamma> (Sup Y)"
by(rule SAT_mono)(rule Sup_upper[THEN le_funD])

lemma currentD_SAT:
  assumes "current \<Gamma> f"
  shows "x \<in> SAT \<Gamma> f \<longleftrightarrow> x \<in> A \<Gamma> \<or> d_IN f x = weight \<Gamma> x"
using currentD_weight_IN[OF assms, of x] by(auto simp add: SAT.simps)

abbreviation terminal :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v set" ("TER\<index>")
where "terminal \<Gamma> f \<equiv> SAT \<Gamma> f \<inter> SINK f"

subsection \<open>Separation\<close>

inductive separating_gen :: "('v, 'more) graph_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> bool"
  for G A B S
where separating:
  "(\<And>x y p. \<lbrakk> x \<in> A; y \<in> B; path G x p y \<rbrakk> \<Longrightarrow> (\<exists>z \<in> set p. z \<in> S) \<or> x \<in> S)
  \<Longrightarrow> separating_gen G A B S"

abbreviation separating :: "('v, 'more) web_scheme \<Rightarrow> 'v set \<Rightarrow> bool"
where "separating \<Gamma> \<equiv> separating_gen \<Gamma> (A \<Gamma>) (B \<Gamma>)"

abbreviation separating_network :: "('v, 'more) network_scheme \<Rightarrow> 'v set \<Rightarrow> bool"
where "separating_network \<Delta> \<equiv> separating_gen \<Delta> {source \<Delta>} {sink \<Delta>}"

lemma separating_networkI [intro?]:
  "(\<And>p. path \<Delta> (source \<Delta>) p (sink \<Delta>) \<Longrightarrow> (\<exists>z \<in> set p. z \<in> S) \<or> source \<Delta> \<in> S)
  \<Longrightarrow> separating_network \<Delta> S"
by(auto intro: separating)

lemma separatingD:
  "\<And>A B. \<lbrakk> separating_gen G A B S; path G x p y; x \<in> A; y \<in> B \<rbrakk> \<Longrightarrow> (\<exists>z \<in> set p. z \<in> S) \<or> x \<in> S"
by(blast elim: separating_gen.cases)

lemma separating_left [simp]: "\<And>A B. A \<subseteq> A' \<Longrightarrow> separating_gen \<Gamma> A B A'"
by(auto simp add: separating_gen.simps)

lemma separating_weakening:
  "\<And>A B. \<lbrakk> separating_gen G A B S; S \<subseteq> S' \<rbrakk> \<Longrightarrow> separating_gen G A B S'"
by(rule separating; drule (3) separatingD; blast)

definition essential :: "('v, 'more) graph_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v \<Rightarrow> bool"
where \<comment> \<open>Should we allow only simple paths here?\<close>
  "\<And>B. essential G B S x \<longleftrightarrow> (\<exists>p. \<exists>y\<in>B. path G x p y \<and> (x \<noteq> y \<longrightarrow> (\<forall>z\<in>set p. z = x \<or> z \<notin> S)))"

abbreviation essential_web :: "('v, 'more) web_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set" ("\<E>\<index>")
where "essential_web \<Gamma> S \<equiv> {x\<in>S. essential \<Gamma> (B \<Gamma>) S x}"

lemma essential_weight_update [simp]:
  "essential (weight_update f G) = essential G"
by(simp add: essential_def fun_eq_iff)

lemma not_essentialD:
  "\<And>B. \<lbrakk> \<not> essential G B S x; path G x p y; y \<in> B \<rbrakk> \<Longrightarrow> x \<noteq> y \<and> (\<exists>z\<in>set p. z \<noteq> x \<and> z \<in> S)"
by(simp add: essential_def)

lemma essentialE [elim?, consumes 1, case_names essential, cases pred: essential]:
  "\<And>B. \<lbrakk> essential G B S x; \<And>p y. \<lbrakk> path G x p y; y \<in> B; \<And>z. \<lbrakk> x \<noteq> y; z \<in> set p \<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> S \<rbrakk> \<Longrightarrow> thesis \<rbrakk> \<Longrightarrow> thesis"
by(auto simp add: essential_def)

lemma essentialI [intro?]:
  "\<And>B. \<lbrakk> path G x p y; y \<in> B; \<And>z. \<lbrakk> x \<noteq> y; z \<in> set p \<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> S \<rbrakk> \<Longrightarrow> essential G B S x"
by(auto simp add: essential_def)

lemma essential_vertex: "\<And>B. \<lbrakk> essential G B S x; x \<notin> B \<rbrakk> \<Longrightarrow>vertex G x"
by(auto elim!: essentialE simp add: vertex_def elim: rtrancl_path.cases)

lemma essential_BI: "\<And>B. x \<in> B \<Longrightarrow> essential G B S x"
by(auto simp add: essential_def intro: rtrancl_path.base)

lemma \<E>_E [elim?, consumes 1, case_names \<E>, cases set: essential_web]:
  fixes \<Gamma> (structure)
  assumes "x \<in> \<E> S"
  obtains p y where "path \<Gamma> x p y" "y \<in> B \<Gamma>" "\<And>z. \<lbrakk> x \<noteq> y; z \<in> set p \<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> S"
using assms by(auto elim: essentialE)

lemma essential_mono: "\<And>B. \<lbrakk> essential G B S x; S' \<subseteq> S \<rbrakk> \<Longrightarrow> essential G B S' x"
by(auto simp add: essential_def)

lemma separating_essential: \<comment> \<open>Lem. 3.4 (cf. Lem. 2.14 in [5])\<close>
  fixes G A B S
  assumes "separating_gen G A B S"
  shows "separating_gen G A B {x\<in>S. essential G B S x}" (is "separating_gen _ _ _ ?E")
proof
  fix x y p
  assume x: "x \<in> A" and y: "y \<in> B" and p: "path G x p y"
  from separatingD[OF assms p x y] have "\<exists>z \<in> set (x # p). z \<in> S" by auto
  from split_list_last_prop[OF this] obtain ys z zs where decomp: "x # p = ys @ z # zs"
    and z: "z \<in> S" and last: "\<And>z. z \<in> set zs \<Longrightarrow> z \<notin> S" by auto
  from decomp consider (empty) "ys = []" "x = z" "p = zs"
    | (Cons) ys' where "ys = x # ys'" "p = ys' @ z # zs"
    by(auto simp add: Cons_eq_append_conv)
  then show "(\<exists>z\<in>set p. z \<in> ?E) \<or> x \<in> ?E"
  proof(cases)
    case empty
    hence "x \<in> ?E" using z p last y by(auto simp add: essential_def)
    thus ?thesis ..
  next
    case (Cons ys')
    from p have "path G z zs y" unfolding Cons by(rule rtrancl_path_appendE)
    hence "z \<in> ?E" using z y last by(auto simp add: essential_def)
    thus ?thesis using Cons by auto
  qed
qed

definition roofed_gen :: "('v, 'more) graph_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set \<Rightarrow> 'v set"
where roofed_def: "\<And>B. roofed_gen G B S = {x. \<forall>p. \<forall>y\<in>B. path G x p y \<longrightarrow> (\<exists>z\<in>set p. z \<in> S) \<or> x \<in> S}"

abbreviation roofed :: "('v, 'more) web_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set" ("RF\<index>")
where "roofed \<Gamma> \<equiv> roofed_gen \<Gamma> (B \<Gamma>)"

abbreviation roofed_network :: "('v, 'more) network_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set" ("RF\<^sup>N\<index>")
where "roofed_network \<Delta> \<equiv> roofed_gen \<Delta> {sink \<Delta>}"

lemma roofedI [intro?]:
  "\<And>B. (\<And>p y. \<lbrakk> path G x p y; y \<in> B \<rbrakk> \<Longrightarrow> (\<exists>z\<in>set p. z \<in> S) \<or> x \<in> S) \<Longrightarrow> x \<in> roofed_gen G B S"
by(auto simp add: roofed_def)

lemma not_roofedE: fixes B
  assumes "x \<notin> roofed_gen G B S"
  obtains p y where "path G x p y" "y \<in> B" "\<And>z. z \<in> set (x # p) \<Longrightarrow> z \<notin> S"
using assms by(auto simp add: roofed_def)

lemma roofed_greater: "\<And>B. S \<subseteq> roofed_gen G B S"
by(auto simp add: roofed_def)

lemma roofed_greaterI: "\<And>B. x \<in> S \<Longrightarrow> x \<in> roofed_gen G B S"
using roofed_greater[of S G] by blast

lemma roofed_mono: "\<And>B. S \<subseteq> S' \<Longrightarrow> roofed_gen G B S \<subseteq> roofed_gen G B S'"
by(fastforce simp add: roofed_def)

lemma in_roofed_mono: "\<And>B. \<lbrakk> x \<in> roofed_gen G B S; S \<subseteq> S' \<rbrakk> \<Longrightarrow> x \<in> roofed_gen G B S'"
using roofed_mono[THEN subsetD] .

lemma roofedD: "\<And>B. \<lbrakk> x \<in> roofed_gen G B S; path G x p y; y \<in> B \<rbrakk> \<Longrightarrow> (\<exists>z\<in>set p. z \<in> S) \<or> x \<in> S"
unfolding roofed_def by blast

lemma separating_RF_A:
  fixes A B
  assumes "separating_gen G A B X"
  shows "A \<subseteq> roofed_gen G B X"
by(rule subsetI roofedI)+(erule separatingD[OF assms])

lemma roofed_idem: fixes B shows "roofed_gen G B (roofed_gen G B S) = roofed_gen G B S"
proof(rule equalityI subsetI roofedI)+
  fix x p y
  assume x: "x \<in> roofed_gen G B (roofed_gen G B S)" and p: "path G x p y" and y: "y \<in> B"
  from roofedD[OF x p y] obtain z where *: "z \<in> set (x # p)" and z: "z \<in> roofed_gen G B S" by auto
  from split_list[OF *] obtain ys zs where split: "x # p = ys @ z # zs" by blast
  with p have p': "path G z zs y" by(auto simp add: Cons_eq_append_conv elim: rtrancl_path_appendE)
  from roofedD[OF z p' y] split show "(\<exists>z\<in>set p. z \<in> S) \<or> x \<in> S"
    by(auto simp add: Cons_eq_append_conv)
qed(rule roofed_mono roofed_greater)+

lemma in_roofed_mono': "\<And>B. \<lbrakk> x \<in> roofed_gen G B S; S \<subseteq> roofed_gen G B S' \<rbrakk> \<Longrightarrow> x \<in> roofed_gen G B S'"
by(subst roofed_idem[symmetric])(erule in_roofed_mono)

lemma roofed_mono': "\<And>B. S \<subseteq> roofed_gen G B S' \<Longrightarrow> roofed_gen G B S \<subseteq> roofed_gen G B S'"
by(rule subsetI)(rule in_roofed_mono')

lemma roofed_idem_Un1: fixes B shows "roofed_gen G B (roofed_gen G B S \<union> T) = roofed_gen G B (S \<union> T)"
proof -
  have "S \<subseteq> T \<union> roofed_gen G B S"
    by (metis (no_types) UnCI roofed_greater subsetCE subsetI)
  then have "S \<union> T \<subseteq> T \<union> roofed_gen G B S \<and> T \<union> roofed_gen G B S \<subseteq> roofed_gen G B (S \<union> T)"
    by (metis (no_types) Un_subset_iff Un_upper2 roofed_greater roofed_mono sup.commute)
  then show ?thesis
    by (metis (no_types) roofed_idem roofed_mono subset_antisym sup.commute)
qed

lemma roofed_UN: fixes A B
  shows "roofed_gen G B (\<Union>i\<in>A. roofed_gen G B (X i)) = roofed_gen G B (\<Union>i\<in>A. X i)" (is "?lhs = ?rhs")
proof(rule equalityI)
  show "?rhs \<subseteq> ?lhs" by(rule roofed_mono)(blast intro: roofed_greaterI)
  show "?lhs \<subseteq> ?rhs" by(rule roofed_mono')(blast intro: in_roofed_mono)
qed

lemma RF_essential: fixes \<Gamma> (structure) shows "RF (\<E> S) = RF S"
proof(intro set_eqI iffI)
  fix x
  assume RF: "x \<in> RF S"
  show "x \<in> RF (\<E> S)"
  proof
    fix p y
    assume p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    from roofedD[OF RF this] have "\<exists>z\<in>set (x # p). z \<in> S" by auto
    from split_list_last_prop[OF this] obtain ys z zs where decomp: "x # p = ys @ z # zs"
      and z: "z \<in> S" and last: "\<And>z. z \<in> set zs \<Longrightarrow> z \<notin> S" by auto
    from decomp consider (empty) "ys = []" "x = z" "p = zs"
      | (Cons) ys' where "ys = x # ys'" "p = ys' @ z # zs"
      by(auto simp add: Cons_eq_append_conv)
    then show "(\<exists>z\<in>set p. z \<in> \<E> S) \<or> x \<in> \<E> S"
    proof(cases)
      case empty
      hence "x \<in> \<E> S" using z p last y by(auto simp add: essential_def)
      thus ?thesis ..
    next
      case (Cons ys')
      from p have "path \<Gamma> z zs y" unfolding Cons by(rule rtrancl_path_appendE)
      hence "z \<in> \<E> S" using z y last by(auto simp add: essential_def)
      thus ?thesis using Cons by auto
    qed
  qed
qed(blast intro: in_roofed_mono)

lemma essentialE_RF:
  fixes \<Gamma> (structure) and B
  assumes "essential \<Gamma> B S x"
  obtains p y where "path \<Gamma> x p y" "y \<in> B" "distinct (x # p)" "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> roofed_gen \<Gamma> B S"
proof -
  from assms obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B"
    and bypass: "\<And>z. \<lbrakk> x \<noteq> y; z \<in> set p \<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> S" by(rule essentialE) blast
  from p obtain p' where p': "path \<Gamma> x p' y" and distinct: "distinct (x # p')"
    and subset: "set p' \<subseteq> set p" by(rule rtrancl_path_distinct)
  { fix z
    assume z: "z \<in> set p'"
    hence "y \<in> set p'" using rtrancl_path_last[OF p', symmetric] p'
      by(auto elim: rtrancl_path.cases intro: last_in_set)
    with distinct z subset have neq: "x \<noteq> y" and "z \<in> set p" by(auto)
    from bypass[OF this] z distinct have "z \<notin> S" by auto

    have "z \<notin> roofed_gen \<Gamma> B S"
    proof
      assume z': "z \<in> roofed_gen \<Gamma> B S"
      from split_list[OF z] obtain ys zs where decomp: "p' = ys @ z # zs" by blast
      with p' have "path \<Gamma> z zs y" by(auto elim: rtrancl_path_appendE)
      from roofedD[OF z' this y] \<open>z \<notin> S\<close> obtain z' where "z' \<in> set zs" "z' \<in> S" by auto
      with bypass[of z'] neq decomp subset distinct show False by auto
    qed }
  with p' y distinct show thesis ..
qed

lemma \<E>_E_RF:
  fixes \<Gamma> (structure)
  assumes "x \<in> \<E> S"
  obtains p y where "path \<Gamma> x p y" "y \<in> B \<Gamma>" "distinct (x # p)" "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF S"
using assms by(auto elim: essentialE_RF)

lemma in_roofed_essentialD:
  fixes \<Gamma> (structure)
  assumes RF: "x \<in> RF S"
  and ess: "essential \<Gamma> (B \<Gamma>) S x"
  shows "x \<in> S"
proof -
  from ess obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and "distinct (x # p)"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> S" by(rule essentialE_RF)(auto intro: roofed_greaterI)
  from roofedD[OF RF p y] bypass show "x \<in> S" by auto
qed

lemma separating_RF: fixes \<Gamma> (structure) shows "separating \<Gamma> (RF S) \<longleftrightarrow> separating \<Gamma> S"
proof
  assume sep: "separating \<Gamma> (RF S)"
  show "separating \<Gamma> S"
  proof
    fix x y p
    assume p: "path \<Gamma> x p y" and x: "x \<in> A \<Gamma>" and y: "y \<in> B \<Gamma>"
    from separatingD[OF sep p x y] have "\<exists>z \<in> set (x # p). z \<in> RF S" by auto
    from split_list_last_prop[OF this] obtain ys z zs where split: "x # p = ys @ z # zs"
      and z: "z \<in> RF S" and bypass: "\<And>z'. z' \<in> set zs \<Longrightarrow> z' \<notin> RF S" by auto
    from p split have "path \<Gamma> z zs y" by(cases ys)(auto elim: rtrancl_path_appendE)
    hence "essential \<Gamma> (B \<Gamma>) S z" using y
      by(rule essentialI)(auto dest: bypass intro: roofed_greaterI)
    with z have "z \<in> S" by(rule in_roofed_essentialD)
    with split show "(\<exists>z\<in>set p. z \<in> S) \<or> x \<in> S" by(cases ys)auto
  qed
qed(blast intro: roofed_greaterI separating_weakening)

definition roofed_circ :: "('v, 'more) web_scheme \<Rightarrow> 'v set \<Rightarrow> 'v set" ("RF\<^sup>\<circ>\<index>")
where "roofed_circ \<Gamma> S = roofed \<Gamma> S - \<E>\<^bsub>\<Gamma>\<^esub> S"

lemma roofed_circI: fixes \<Gamma> (structure) shows
  "\<lbrakk> x \<in> RF T; x \<in> T \<Longrightarrow> \<not> essential \<Gamma> (B \<Gamma>) T x \<rbrakk> \<Longrightarrow> x \<in> RF\<^sup>\<circ> T"
by(simp add: roofed_circ_def)

lemma roofed_circE:
  fixes \<Gamma> (structure)
  assumes "x \<in> RF\<^sup>\<circ> T"
  obtains "x \<in> RF T" "\<not> essential \<Gamma> (B \<Gamma>) T x"
using assms by(auto simp add: roofed_circ_def intro: in_roofed_essentialD)

lemma \<E>_\<E>: fixes \<Gamma> (structure) shows "\<E> (\<E> S) = \<E> S"
by(auto intro: essential_mono)

lemma roofed_circ_essential: fixes \<Gamma> (structure) shows "RF\<^sup>\<circ> (\<E> S) = RF\<^sup>\<circ> S"
unfolding roofed_circ_def RF_essential \<E>_\<E> ..

lemma essential_RF: fixes B
  shows "essential G B (roofed_gen G B S) = essential G B S"  (is "essential _ _ ?RF = _")
proof(intro ext iffI)
  show "essential G B S x" if "essential G B ?RF x" for x using that
    by(rule essential_mono)(blast intro: roofed_greaterI)
  show "essential G B ?RF x" if "essential G B S x" for x
    using that by(rule essentialE_RF)(erule (1) essentialI, blast)
qed

lemma \<E>_RF: fixes \<Gamma> (structure) shows "\<E> (RF S) = \<E> S"
by(auto dest: in_roofed_essentialD simp add: essential_RF intro: roofed_greaterI)

lemma essential_\<E>: fixes \<Gamma> (structure) shows "essential \<Gamma> (B \<Gamma>) (\<E> S) = essential \<Gamma> (B \<Gamma>) S"
by(subst essential_RF[symmetric])(simp only: RF_essential essential_RF)

lemma RF_in_B: fixes \<Gamma> (structure) shows "x \<in> B \<Gamma> \<Longrightarrow> x \<in> RF S \<longleftrightarrow> x \<in> S"
by(auto intro: roofed_greaterI dest: roofedD[OF _ rtrancl_path.base])

lemma RF_circ_edge_forward:
  fixes \<Gamma> (structure)
  assumes x: "x \<in> RF\<^sup>\<circ> S"
  and edge: "edge \<Gamma> x y"
  shows "y \<in> RF S"
proof
  fix p z
  assume p: "path \<Gamma> y p z" and z: "z \<in> B \<Gamma>"
  from x have rf: "x \<in> RF S" and ness: "x \<notin> \<E> S" by(auto elim: roofed_circE)
  show "(\<exists>z\<in>set p. z \<in> S) \<or> y \<in> S"
  proof(cases "\<exists>z'\<in>set (y # p). z' \<in> S")
    case False
    from edge p have p': "path \<Gamma> x (y # p) z" ..
    from roofedD[OF rf this z] False have "x \<in> S" by auto
    moreover have "essential \<Gamma> (B \<Gamma>) S x" using p' False z by(auto intro!: essentialI)
    ultimately have "x \<in> \<E> S" by simp
    with ness show ?thesis by contradiction
  qed auto
qed

subsection \<open>Waves\<close>

inductive wave :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> bool"
  for \<Gamma> (structure) and f
where
  wave:
  "\<lbrakk> separating \<Gamma> (TER f);
     \<And>x. x \<notin> RF (TER f) \<Longrightarrow> d_OUT f x = 0 \<rbrakk>
  \<Longrightarrow> wave \<Gamma> f"

lemma wave_0 [simp]: "wave \<Gamma> zero_current"
by rule simp_all

lemma waveD_separating: "wave \<Gamma> f \<Longrightarrow> separating \<Gamma> (TER\<^bsub>\<Gamma>\<^esub> f)"
by(simp add: wave.simps)

lemma waveD_OUT: "\<lbrakk> wave \<Gamma> f; x \<notin> RF\<^bsub>\<Gamma>\<^esub> (TER\<^bsub>\<Gamma>\<^esub> f) \<rbrakk> \<Longrightarrow> d_OUT f x = 0"
by(simp add: wave.simps)

lemma wave_A_in_RF: fixes \<Gamma> (structure)
  shows "\<lbrakk> wave \<Gamma> f; x \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> x \<in> RF (TER f)"
by(auto intro!: roofedI dest!: waveD_separating separatingD)

lemma wave_not_RF_IN_zero:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and x: "x \<notin> RF (TER f)"
  shows "d_IN f x = 0"
proof -
  from x obtain p z where z: "z \<in> B \<Gamma>" and p: "path \<Gamma> x p z"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER f" "x \<notin> TER f"
    by(clarsimp simp add: roofed_def)
  have "f (y, x) = 0" for y
  proof(cases "edge \<Gamma> y x")
    case edge: True
    have "d_OUT f y = 0"
    proof(cases "y \<in> TER f")
      case False
      with z p bypass edge have "y \<notin> RF (TER f)"
        by(auto simp add: roofed_def intro: rtrancl_path.step intro!: exI rev_bexI)
      thus "d_OUT f y = 0" by(rule waveD_OUT[OF w])
    qed(auto simp add: SINK.simps)
    moreover have "f (y, x) \<le> d_OUT f y" by (rule d_OUT_ge_point)
    ultimately show ?thesis by simp
  qed(simp add: currentD_outside[OF f])
  then show "d_IN f x = 0" unfolding d_IN_def
    by(simp add: nn_integral_0_iff emeasure_count_space_eq_0)
qed

lemma current_Sup:
  fixes \<Gamma> (structure)
  assumes chain: "Complete_Partial_Order.chain (\<le>) Y"
  and Y: "Y \<noteq> {}"
  and current: "\<And>f. f \<in> Y \<Longrightarrow> current \<Gamma> f"
  and countable [simp]: "countable (support_flow (Sup Y))"
  shows "current \<Gamma> (Sup Y)"
proof(rule, goal_cases)
  case (1 x)
  have "d_OUT (Sup Y) x = (SUP f\<in>Y. d_OUT f x)" using chain Y by(simp add: d_OUT_Sup)
  also have "\<dots> \<le> weight \<Gamma> x" using 1
    by(intro SUP_least)(auto dest!: current currentD_weight_OUT)
  finally show ?case .
next
  case (2 x)
  have "d_IN (Sup Y) x = (SUP f\<in>Y. d_IN f x)" using chain Y by(simp add: d_IN_Sup)
  also have "\<dots> \<le> weight \<Gamma> x" using 2
    by(intro SUP_least)(auto dest!: current currentD_weight_IN)
  finally show ?case .
next
  case (3 x)
  have "d_OUT (Sup Y) x = (SUP f\<in>Y. d_OUT f x)" using chain Y by(simp add: d_OUT_Sup)
  also have "\<dots> \<le> (SUP f\<in>Y. d_IN f x)" using 3
    by(intro SUP_mono)(auto dest: current currentD_OUT_IN)
  also have "\<dots> = d_IN (Sup Y) x" using chain Y by(simp add: d_IN_Sup)
  finally show ?case .
next
  case (4 a)
  have "d_IN (Sup Y) a = (SUP f\<in>Y. d_IN f a)" using chain Y by(simp add: d_IN_Sup)
  also have "\<dots> = (SUP f\<in>Y. 0)" using 4 by(intro SUP_cong)(auto dest!: current currentD_IN)
  also have "\<dots> = 0" using Y by simp
  finally show ?case .
next
  case (5 b)
  have "d_OUT (Sup Y) b = (SUP f\<in>Y. d_OUT f b)" using chain Y by(simp add: d_OUT_Sup)
  also have "\<dots> = (SUP f\<in>Y. 0)" using 5 by(intro SUP_cong)(auto dest!: current currentD_OUT)
  also have "\<dots> = 0" using Y by simp
  finally show ?case .
next
  fix e
  assume "e \<notin> \<^bold>E"
  from currentD_outside'[OF current this] have "f e = 0" if "f \<in> Y" for f using that by simp
  hence "Sup Y e = (SUP _\<in>Y. 0)" by(auto intro: SUP_cong)
  then show "Sup Y e = 0" using Y by(simp)
qed

lemma wave_lub: \<comment> \<open>Lemma 4.3\<close>
  fixes \<Gamma> (structure)
  assumes chain: "Complete_Partial_Order.chain (\<le>) Y"
  and Y: "Y \<noteq> {}"
  and wave: "\<And>f. f \<in> Y \<Longrightarrow> wave \<Gamma> f"
  and countable [simp]: "countable (support_flow (Sup Y))"
  shows "wave \<Gamma> (Sup Y)"
proof
  { fix x y p
    assume p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    define P where "P = {x} \<union> set p"

    let ?f = "\<lambda>f. SINK f \<inter> P"
    have "Complete_Partial_Order.chain (\<supseteq>) (?f ` Y)" using chain
      by(rule chain_imageI)(auto dest: SINK_mono')
    moreover have "\<dots> \<subseteq> Pow P" by auto
    hence "finite (?f ` Y)" by(rule finite_subset)(simp add: P_def)
    ultimately have "(\<Inter>(?f ` Y)) \<in> ?f ` Y"
      by(rule ccpo.in_chain_finite[OF complete_lattice_ccpo_dual])(simp add: Y)
    then obtain f where f: "f \<in> Y" and eq: "\<Inter>(?f ` Y) = ?f f" by clarify
    hence *: "(\<Inter>f\<in>Y. SINK f) \<inter> P = SINK f \<inter> P" by(clarsimp simp add: prod_lub_def Y)+
    { fix g
      assume "g \<in> Y" "f \<le> g"
      with * have "(\<Inter>f\<in>Y. SINK f) \<inter> P = SINK g \<inter> P" by(blast dest: SINK_mono')
      then have "TER (Sup Y) \<inter> P \<supseteq> TER g \<inter> P"
        using SAT_Sup_upper[OF \<open>g \<in> Y\<close>, of \<Gamma>] SINK_Sup[OF chain Y countable] by blast }
    with f have "\<exists>f\<in>Y. \<forall>g\<in>Y. g \<ge> f \<longrightarrow> TER g \<inter> P \<subseteq> TER (Sup Y) \<inter> P" by blast }
  note subset = this

  show "separating \<Gamma> (TER (Sup Y))"
  proof
    fix x y p
    assume *: "path \<Gamma> x p y" "y \<in> B \<Gamma>" and "x \<in> A \<Gamma>"
    let ?P = "{x} \<union> set p"
    from subset[OF *] obtain f where f:"f \<in> Y"
      and subset: "TER f \<inter> ?P \<subseteq> TER (Sup Y) \<inter> ?P" by blast
    from wave[OF f] have "TER f \<inter> ?P \<noteq> {}" using * \<open>x \<in> A \<Gamma>\<close>
      by(auto simp add: wave.simps dest: separatingD)
    with subset show " (\<exists>z\<in>set p. z \<in> TER (Sup Y)) \<or> x \<in> TER (Sup Y)" by blast
  qed

  fix x
  assume "x \<notin> RF (TER (Sup Y))"
  then obtain p y where y: "y \<in> B \<Gamma>"
    and p: "path \<Gamma> x p y"
    and ter: "TER (Sup Y) \<inter> ({x} \<union> set p) = {}" by(auto simp add: roofed_def)
  let ?P = "{x} \<union> set p"
  from subset[OF p y] obtain f where f: "f \<in> Y"
    and subset: "\<And>g. \<lbrakk> g \<in> Y; f \<le> g \<rbrakk> \<Longrightarrow> TER g \<inter> ?P \<subseteq> TER (Sup Y) \<inter> ?P" by blast

  { fix g
    assume g: "g \<in> Y"
    with chain f have "f \<le> g \<or> g \<le> f" by(rule chainD)
    hence "d_OUT g x = 0"
    proof
      assume "f \<le> g"
      from subset[OF g this] ter have "TER g \<inter> ?P = {}" by blast
      with p y have "x \<notin> RF (TER g)" by(auto simp add: roofed_def)
      with wave[OF g] show ?thesis by(blast elim: wave.cases)
    next
      assume "g \<le> f"
      from subset ter f have "TER f \<inter> ?P = {}" by blast
      with y p have "x \<notin> RF (TER f)" by(auto simp add: roofed_def)
      with wave[OF f] have "d_OUT f x = 0" by(blast elim: wave.cases)
      moreover have "d_OUT g x \<le> d_OUT f x" using \<open>g \<le> f\<close>[THEN le_funD] by(rule d_OUT_mono)
      ultimately show ?thesis by simp
    qed }
  thus "d_OUT (Sup Y) x = 0" using chain Y by(simp add: d_OUT_Sup)
qed

lemma ex_maximal_wave: \<comment> \<open>Corollary 4.4\<close>
  fixes \<Gamma> (structure)
  assumes countable: "countable \<^bold>E"
  shows "\<exists>f. current \<Gamma> f \<and> wave \<Gamma> f \<and> (\<forall>w. current \<Gamma> w \<and> wave \<Gamma> w \<and> f \<le> w \<longrightarrow> f = w)"
proof -
  define Field_r where "Field_r = {f. current \<Gamma> f \<and> wave \<Gamma> f}"
  define r where "r = {(f, g). f \<in> Field_r \<and> g \<in> Field_r \<and> f \<le> g}"
  have Field_r: "Field r = Field_r" by(auto simp add: Field_def r_def)

  have "Partial_order r" unfolding order_on_defs
    by(auto intro!: refl_onI transI antisymI simp add: Field_r r_def Field_def)
  hence "\<exists>m\<in>Field r. \<forall>a\<in>Field r. (m, a) \<in> r \<longrightarrow> a = m"
  proof(rule Zorns_po_lemma)
    fix Y
    assume "Y \<in> Chains r"
    hence Y: "Complete_Partial_Order.chain (\<le>) Y"
      and w: "\<And>f. f \<in> Y \<Longrightarrow> wave \<Gamma> f"
      and f: "\<And>f. f \<in> Y \<Longrightarrow> current \<Gamma> f"
      by(auto simp add: Chains_def r_def chain_def Field_r_def)
    show "\<exists>w \<in> Field r. \<forall>f \<in> Y. (f, w) \<in> r"
    proof(cases "Y = {}")
      case True
      have "zero_current \<in> Field r" by(simp add: Field_r Field_r_def)
      with True show ?thesis by blast
    next
      case False
      have "support_flow (Sup Y) \<subseteq> \<^bold>E" by(auto simp add: support_flow_Sup elim!: support_flow.cases dest!: f dest: currentD_outside)
      hence c: "countable (support_flow (Sup Y))" using countable  by(rule countable_subset)
      with Y False f w have "Sup Y \<in> Field r" unfolding Field_r Field_r_def
        by(blast intro: wave_lub current_Sup)
      moreover then have "(f, Sup Y) \<in> r" if "f \<in> Y" for f using w[OF that] f[OF that] that unfolding Field_r
        by(auto simp add: r_def Field_r_def intro: Sup_upper)
      ultimately show ?thesis by blast
    qed
  qed
  thus ?thesis by(simp add: Field_r Field_r_def)(auto simp add: r_def Field_r_def)
qed

lemma essential_leI:
  fixes \<Gamma> (structure)
  assumes g: "current \<Gamma> g" and w: "wave \<Gamma> g"
  and le: "\<And>e. f e \<le> g e"
  and x: "x \<in> \<E> (TER g)"
  shows "essential \<Gamma> (B \<Gamma>) (TER f) x"
proof -
  from x obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and distinct: "distinct (x # p)"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER g)" by(rule \<E>_E_RF) blast
  show ?thesis using p y
  proof
    fix z
    assume "z \<in> set p"
    hence z: "z \<notin> RF (TER g)" by(auto dest: bypass)
    with w have OUT: "d_OUT g z = 0" and IN: "d_IN g z = 0" by(rule waveD_OUT wave_not_RF_IN_zero[OF g])+
    with z have "z \<notin> A \<Gamma>" "weight \<Gamma> z > 0" by(auto intro!: roofed_greaterI simp add: SAT.simps SINK.simps)
    moreover from IN d_IN_mono[of f z g, OF le] have "d_IN f z \<le> 0" by(simp)
    ultimately have "z \<notin> TER f" by(auto simp add: SAT.simps)
    then show "z = x \<or> z \<notin> TER f" by simp
  qed
qed

lemma essential_eq_leI:
  fixes \<Gamma> (structure)
  assumes g: "current \<Gamma> g" and w: "wave \<Gamma> g"
  and le: "\<And>e. f e \<le> g e"
  and subset: "\<E> (TER g) \<subseteq> TER f"
  shows "\<E> (TER f) = \<E> (TER g)"
proof
  show subset: "\<E> (TER g) \<subseteq> \<E> (TER f)"
  proof
    fix x
    assume x: "x \<in> \<E> (TER g)"
    hence "x \<in> TER f" using subset by blast
    moreover have "essential \<Gamma> (B \<Gamma>) (TER f) x" using g w le x by(rule essential_leI)
    ultimately show "x \<in> \<E> (TER f)" by simp
  qed

  show "\<dots> \<subseteq> \<E> (TER g)"
  proof
    fix x
    assume x: "x \<in> \<E> (TER f)"
    hence "x \<in> TER f" by auto
    hence "x \<in> RF (TER g)"
    proof(rule contrapos_pp)
      assume x: "x \<notin> RF (TER g)"
      with w have OUT: "d_OUT g x = 0" and IN: "d_IN g x = 0" by(rule waveD_OUT wave_not_RF_IN_zero[OF g])+
      with x have "x \<notin> A \<Gamma>" "weight \<Gamma> x > 0" by(auto intro!: roofed_greaterI simp add: SAT.simps SINK.simps)
      moreover from IN d_IN_mono[of f x g, OF le] have "d_IN f x \<le> 0" by(simp)
      ultimately show "x \<notin> TER f" by(auto simp add: SAT.simps)
    qed
    moreover have "x \<notin> RF\<^sup>\<circ> (TER g)"
    proof
      assume "x \<in> RF\<^sup>\<circ> (TER g)"
      hence RF: "x \<in> RF (\<E> (TER g))" and not_E: "x \<notin> \<E> (TER g)"
        unfolding RF_essential by(simp_all add: roofed_circ_def)
      from x obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and distinct: "distinct (x # p)"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)" by(rule \<E>_E_RF) blast
      from roofedD[OF RF p y] not_E obtain z where "z \<in> set p" "z \<in> \<E> (TER g)" by blast
      with subset bypass[of z] show False by(auto intro: roofed_greaterI)
    qed
    ultimately show "x \<in> \<E> (TER g)" by(simp add: roofed_circ_def)
  qed
qed

subsection \<open>Hindrances and looseness\<close>

inductive hindrance_by :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> ennreal \<Rightarrow> bool"
  for \<Gamma> (structure) and f and \<epsilon>
where
  hindrance_by:
  "\<lbrakk> a \<in> A \<Gamma>; a \<notin> \<E> (TER f); d_OUT f a < weight \<Gamma> a; \<epsilon> < weight \<Gamma> a - d_OUT f a \<rbrakk> \<Longrightarrow> hindrance_by \<Gamma> f \<epsilon>"

inductive hindrance :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> bool"
  for \<Gamma> (structure) and f
where
  hindrance:
  "\<lbrakk> a \<in> A \<Gamma>; a \<notin> \<E> (TER f); d_OUT f a < weight \<Gamma> a \<rbrakk> \<Longrightarrow> hindrance \<Gamma> f"

inductive hindered :: "('v, 'more) web_scheme \<Rightarrow> bool"
  for \<Gamma> (structure)
where hindered: "\<lbrakk> hindrance \<Gamma> f; current \<Gamma> f; wave \<Gamma> f \<rbrakk> \<Longrightarrow> hindered \<Gamma>"

inductive hindered_by :: "('v, 'more) web_scheme \<Rightarrow> ennreal \<Rightarrow> bool"
  for \<Gamma> (structure) and \<epsilon>
where hindered_by: "\<lbrakk> hindrance_by \<Gamma> f \<epsilon>; current \<Gamma> f; wave \<Gamma> f \<rbrakk> \<Longrightarrow> hindered_by \<Gamma> \<epsilon>"

lemma hindrance_into_hindrance_by:
  assumes "hindrance \<Gamma> f"
  shows "\<exists>\<epsilon>>0. hindrance_by \<Gamma> f \<epsilon>"
using assms
proof cases
  case (hindrance a)
  let ?\<epsilon> = "if weight \<Gamma> a = \<top> then 1 else (weight \<Gamma> a - d_OUT f a) / 2"
  from \<open>d_OUT f a < weight \<Gamma> a\<close> have "weight \<Gamma> a - d_OUT f a > 0" "weight \<Gamma> a \<noteq> \<top> \<Longrightarrow> weight \<Gamma> a - d_OUT f a < \<top>"
    by(simp_all add: diff_gr0_ennreal less_top diff_less_top_ennreal)
  from ennreal_mult_strict_left_mono[of 1 2, OF _ this]
  have "0 < ?\<epsilon>" and "?\<epsilon> < weight \<Gamma> a - d_OUT f a" using \<open>d_OUT f a < weight \<Gamma> a\<close>
    by(auto intro!: diff_gr0_ennreal simp: ennreal_zero_less_divide divide_less_ennreal)
  with hindrance show ?thesis by(auto intro!: hindrance_by.intros)
qed

lemma hindrance_by_into_hindrance: "hindrance_by \<Gamma> f \<epsilon> \<Longrightarrow> hindrance \<Gamma> f"
by(blast elim: hindrance_by.cases intro: hindrance.intros)

lemma hindrance_conv_hindrance_by: "hindrance \<Gamma> f \<longleftrightarrow> (\<exists>\<epsilon>>0. hindrance_by \<Gamma> f \<epsilon>)"
by(blast intro: hindrance_into_hindrance_by hindrance_by_into_hindrance)

lemma hindered_into_hindered_by: "hindered \<Gamma> \<Longrightarrow> \<exists>\<epsilon>>0. hindered_by \<Gamma> \<epsilon>"
by(blast intro: hindered_by.intros elim: hindered.cases dest: hindrance_into_hindrance_by)

lemma hindered_by_into_hindered: "hindered_by \<Gamma> \<epsilon> \<Longrightarrow> hindered \<Gamma>"
by(blast elim: hindered_by.cases intro: hindered.intros dest: hindrance_by_into_hindrance)

lemma hindered_conv_hindered_by: "hindered \<Gamma> \<longleftrightarrow> (\<exists>\<epsilon>>0. hindered_by \<Gamma> \<epsilon>)"
by(blast intro: hindered_into_hindered_by hindered_by_into_hindered)

inductive loose :: "('v, 'more) web_scheme \<Rightarrow> bool"
  for \<Gamma>
where
  loose: "\<lbrakk> \<And>f. \<lbrakk> current \<Gamma> f; wave \<Gamma> f \<rbrakk> \<Longrightarrow> f = zero_current; \<not> hindrance \<Gamma> zero_current \<rbrakk>
  \<Longrightarrow> loose \<Gamma>"

lemma looseD_hindrance: "loose \<Gamma> \<Longrightarrow> \<not> hindrance \<Gamma> zero_current"
by(simp add: loose.simps)

lemma looseD_wave:
  "\<lbrakk> loose \<Gamma>; current \<Gamma> f; wave \<Gamma> f \<rbrakk> \<Longrightarrow> f = zero_current"
by(simp add: loose.simps)

lemma loose_unhindered:
  fixes \<Gamma> (structure)
  assumes "loose \<Gamma>"
  shows "\<not> hindered \<Gamma>"
apply auto
  apply(erule hindered.cases)
apply(frule (1) looseD_wave[OF assms])
apply simp
using looseD_hindrance[OF assms]
by simp

context
  fixes \<Gamma> \<Gamma>' :: "('v, 'more) web_scheme"
  assumes [simp]: "edge \<Gamma> = edge \<Gamma>'" "A \<Gamma> = A \<Gamma>'" "B \<Gamma> = B \<Gamma>'"
  and weight_eq: "\<And>x. x \<notin> A \<Gamma>' \<Longrightarrow> weight \<Gamma> x = weight \<Gamma>' x"
  and weight_le: "\<And>a. a \<in> A \<Gamma>' \<Longrightarrow> weight \<Gamma> a \<ge> weight \<Gamma>' a"
begin

private lemma essential_eq: "essential \<Gamma> = essential \<Gamma>'"
by(simp add: fun_eq_iff essential_def)

qualified lemma TER_eq: "TER\<^bsub>\<Gamma>\<^esub> f = TER\<^bsub>\<Gamma>'\<^esub> f"
apply(auto simp add: SINK.simps SAT.simps)
apply(erule contrapos_np; drule weight_eq; simp)+
done

qualified lemma separating_eq: "separating_gen \<Gamma> = separating_gen \<Gamma>'"
by(intro ext iffI; rule separating_gen.intros; drule separatingD; simp)

qualified lemma roofed_eq: "\<And>B. roofed_gen \<Gamma> B S = roofed_gen \<Gamma>' B S"
by(simp add: roofed_def)

lemma wave_eq_web: \<comment> \<open>Observation 4.6\<close>
  "wave \<Gamma> f \<longleftrightarrow> wave \<Gamma>' f"
by(simp add: wave.simps separating_eq TER_eq roofed_eq)

lemma current_mono_web: "current \<Gamma>' f \<Longrightarrow> current \<Gamma> f"
apply(rule current, simp_all add: currentD_OUT_IN currentD_IN currentD_OUT  currentD_outside')
subgoal for x by(cases "x \<in> A \<Gamma>'")(auto dest!: weight_eq weight_le dest: currentD_weight_OUT intro: order_trans)
subgoal for x by(cases "x \<in> A \<Gamma>'")(auto dest!: weight_eq weight_le dest: currentD_weight_IN intro: order_trans)
done

lemma hindrance_mono_web: "hindrance \<Gamma>' f \<Longrightarrow> hindrance \<Gamma> f"
apply(erule hindrance.cases)
apply(rule hindrance)
  apply simp
 apply(unfold TER_eq, simp add: essential_eq)
apply(auto dest!: weight_le)
done

lemma hindered_mono_web: "hindered \<Gamma>' \<Longrightarrow> hindered \<Gamma>"
apply(erule hindered.cases)
apply(rule hindered.intros)
  apply(erule hindrance_mono_web)
 apply(erule current_mono_web)
apply(simp add: wave_eq_web)
done

end

subsection \<open>Linkage\<close>

text \<open>
  The following definition of orthogonality is stronger than the original definition 3.5 in
  @{cite AharoniBergerGeorgakopoulusPerlsteinSpruessel2011JCT} in that the outflow from any
  \<open>A\<close>-vertices in the set must saturate the vertex; @{term "S \<subseteq> SAT \<Gamma> f"} is not enough.

  With the original definition of orthogonal current, the reduction from networks to webs fails because
  the induced flow need not saturate edges going out of the source. Consider the network with three
  nodes \<open>s\<close>, \<open>x\<close>, and \<open>t\<close> and edges \<open>(s, x)\<close> and \<open>(x, t)\<close> with
  capacity \<open>1\<close>. Then, the corresponding web has the vertices \<open>(s, x)\<close> and
  \<open>(x, t)\<close> and one edge from \<open>(s, x)\<close> to \<open>(x, t)\<close>. Clearly, the zero current
  @{term [source] zero_current} is a web-flow and \<open>TER zero_current = {(s, x)}\<close>, which is essential.
  Moreover, @{term [source] zero_current} and \<open>{(s, x)}\<close> are orthogonal because
  @{term [source] zero_current} trivially saturates \<open>(s, x)\<close> as this is a vertex in \<open>A\<close>.
\<close>
inductive orthogonal_current :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v set \<Rightarrow> bool"
  for \<Gamma> (structure) and f S
where orthogonal_current:
  "\<lbrakk> \<And>x. \<lbrakk> x \<in> S; x \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> weight \<Gamma> x \<le> d_IN f x;
     \<And>x. \<lbrakk> x \<in> S; x \<in> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f x = weight \<Gamma> x;
    \<And>u v. \<lbrakk> v \<in> RF S; u \<notin> RF\<^sup>\<circ> S \<rbrakk> \<Longrightarrow> f (u, v) = 0 \<rbrakk>
  \<Longrightarrow> orthogonal_current \<Gamma> f S"

lemma orthogonal_currentD_SAT: "\<lbrakk> orthogonal_current \<Gamma> f S; x \<in> S \<rbrakk> \<Longrightarrow> x \<in> SAT \<Gamma> f"
by(auto elim!: orthogonal_current.cases intro: SAT.intros)

lemma orthogonal_currentD_A: "\<lbrakk> orthogonal_current \<Gamma> f S; x \<in> S; x \<in> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f x = weight \<Gamma> x"
by(auto elim: orthogonal_current.cases)

lemma orthogonal_currentD_in: "\<lbrakk> orthogonal_current \<Gamma> f S; v \<in> RF\<^bsub>\<Gamma>\<^esub> S; u \<notin> RF\<^sup>\<circ>\<^bsub>\<Gamma>\<^esub> S \<rbrakk> \<Longrightarrow> f (u, v) = 0"
by(auto elim: orthogonal_current.cases)

inductive linkage :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> bool"
  for \<Gamma> f
where \<comment> \<open>Omit the condition @{const web_flow}\<close>
  linkage: "(\<And>x. x \<in> A \<Gamma> \<Longrightarrow> d_OUT f x = weight \<Gamma> x) \<Longrightarrow> linkage \<Gamma> f"

lemma linkageD: "\<lbrakk> linkage \<Gamma> f; x \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f x = weight \<Gamma> x"
by(rule linkage.cases)

abbreviation linkable :: "('v, 'more) web_scheme \<Rightarrow> bool"
where "linkable \<Gamma> \<equiv> \<exists>f. web_flow \<Gamma> f \<and> linkage \<Gamma> f"

subsection \<open>Trimming\<close>

context
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure)
  and f :: "'v current"
begin

inductive trimming :: "'v current \<Rightarrow> bool"
  for g
where
  trimming:
  \<comment> \<open>omits the condition that @{term f} is a wave\<close>
  "\<lbrakk> current \<Gamma> g; wave \<Gamma> g; g \<le> f; \<And>x. \<lbrakk> x \<in> RF\<^sup>\<circ> (TER f); x \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> KIR g x; \<E> (TER g) - A \<Gamma> = \<E> (TER f) - A \<Gamma> \<rbrakk>
  \<Longrightarrow> trimming g"

lemma assumes "trimming g"
  shows trimmingD_current: "current \<Gamma> g"
  and trimmingD_wave: "wave \<Gamma> g"
  and trimmingD_le: "\<And>e. g e \<le> f e"
  and trimmingD_KIR: "\<lbrakk> x \<in> RF\<^sup>\<circ> (TER f); x \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> KIR g x"
  and trimmingD_\<E>: "\<E> (TER g) - A \<Gamma> = \<E> (TER f) - A \<Gamma>"
using assms by(blast elim: trimming.cases dest: le_funD)+

lemma ex_trimming: \<comment> \<open>Lemma 4.8\<close>
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and countable: "countable \<^bold>E"
  and weight_finite: "\<And>x. weight \<Gamma> x \<noteq> \<top>"
  shows "\<exists>g. trimming g"
proof -
  define F where "F = {g. current \<Gamma> g \<and> wave \<Gamma> g \<and> g \<le> f \<and> \<E> (TER g) = \<E> (TER f)}"
  define leq where "leq = restrict_rel F {(g, g'). g' \<le> g}"
  have in_F [simp]: "g \<in> F \<longleftrightarrow> current \<Gamma> g \<and> wave \<Gamma> g \<and> (\<forall>e. g e \<le> f e) \<and> \<E> (TER g) = \<E> (TER f)" for g
    by(simp add: F_def le_fun_def)

  have f_finite [simp]: "f e \<noteq> \<top>" for e
  proof(cases e)
    case (Pair x y)
    have "f (x, y) \<le> d_IN f y" by (rule d_IN_ge_point)
    also have "\<dots> \<le> weight \<Gamma> y" by(rule currentD_weight_IN[OF f])
    also have "\<dots> < \<top>" by(simp add: weight_finite less_top[symmetric])
    finally show ?thesis using Pair by simp
  qed

  have chainD: "Inf M \<in> F" if M: "M \<in> Chains leq" and nempty: "M \<noteq> {}" for M
  proof -
    from nempty obtain g0 where g0: "g0 \<in> M" by auto
    have g0_le_f: "g0 e \<le> f e" and g: "current \<Gamma> g0" and w0: "wave \<Gamma> g0" for e
      using Chains_FieldD[OF M g0] by(cases e, auto simp add: leq_def)

    have finite_OUT: "d_OUT f x \<noteq> \<top>" for x using weight_finite[of x]
      by(rule neq_top_trans)(rule currentD_weight_OUT[OF f])
    have finite_IN: "d_IN f x \<noteq> \<top>" for x using weight_finite[of x]
      by(rule neq_top_trans)(rule currentD_weight_IN[OF f])

    from M have "M \<in> Chains {(g, g'). g' \<le> g}"
      by(rule mono_Chains[THEN subsetD, rotated])(auto simp add: leq_def in_restrict_rel_iff)
    then have chain: "Complete_Partial_Order.chain (\<ge>) M" by(rule Chains_into_chain)
    hence chain': "Complete_Partial_Order.chain (\<le>) M" by(simp add: chain_dual)

    have countable': "countable (support_flow f)"
      using current_support_flow[OF f] by(rule countable_subset)(rule countable)

    have OUT_M: "d_OUT (Inf M) x = (INF g\<in>M. d_OUT g x)" for x using chain' nempty countable' _ finite_OUT
      by(rule d_OUT_Inf)(auto dest!: Chains_FieldD[OF M]  simp add: leq_def)
    have IN_M: "d_IN (Inf M) x = (INF g\<in>M. d_IN g x)" for x using chain' nempty countable' _ finite_IN
      by(rule d_IN_Inf)(auto dest!: Chains_FieldD[OF M]  simp add: leq_def)

    have c: "current \<Gamma> (Inf M)" using g
    proof(rule current_leI)
      show "(Inf M) e \<le> g0 e" for e using g0 by(auto intro: INF_lower)
      show "d_OUT (\<Sqinter>M) x \<le> d_IN (\<Sqinter>M) x" if "x \<notin> A \<Gamma>" for x
        by(auto 4 4 simp add: IN_M OUT_M leq_def intro!: INF_mono dest: Chains_FieldD[OF M] intro: currentD_OUT_IN[OF _ that])
    qed

    have INF_le_f: "Inf M e \<le> f e" for e using g0 by(auto intro!: INF_lower2 g0_le_f)
    have eq: "\<E> (TER (Inf M)) = \<E> (TER f)" using f w INF_le_f
    proof(rule essential_eq_leI; intro subsetI)
      fix x
      assume x: "x \<in> \<E> (TER f)"
      hence "x \<in> SINK (Inf M)" using d_OUT_mono[of "Inf M" x f, OF INF_le_f]
        by(auto simp add: SINK.simps)
      moreover from x have "x \<in> SAT \<Gamma> g" if "g \<in> M" for g using Chains_FieldD[OF M that] by(auto simp add: leq_def)
      hence "x \<in> SAT \<Gamma> (Inf M)" by(auto simp add: SAT.simps IN_M intro!: INF_greatest)
      ultimately show "x \<in> TER (Inf M)" by auto
    qed

    have w': "wave \<Gamma> (Inf M)"
    proof
      have "separating \<Gamma> (\<E> (TER f))" by(rule separating_essential)(rule waveD_separating[OF w])
      then show "separating \<Gamma> (TER (Inf M))" unfolding eq[symmetric] by(rule separating_weakening) auto

      fix x
      assume "x \<notin> RF (TER (Inf M))"
      hence "x \<notin> RF (\<E> (TER (Inf M)))" unfolding RF_essential .
      hence "x \<notin> RF (TER f)" unfolding eq RF_essential .
      hence "d_OUT f x = 0" by(rule waveD_OUT[OF w])
      with d_OUT_mono[of _ x f, OF INF_le_f]
      show "d_OUT (Inf M) x = 0" by (metis le_zero_eq)
    qed
    from c w' INF_le_f eq show ?thesis by simp
  qed

  define trim1
    where "trim1 g =
      (if trimming g then g
        else let z = SOME z. z \<in> RF\<^sup>\<circ> (TER g) \<and> z \<notin> A \<Gamma> \<and> \<not> KIR g z;
            factor = d_OUT g z / d_IN g z
          in (\<lambda>(y, x). (if x = z then factor else 1) * g (y, x)))" for g

  have increasing: "trim1 g \<le> g \<and> trim1 g \<in> F" if "g \<in> F" for g
  proof(cases "trimming g")
    case True
    thus ?thesis using that by(simp add: trim1_def)
  next
    case False
    let ?P = "\<lambda>z. z \<in> RF\<^sup>\<circ> (TER g) \<and> z \<notin> A \<Gamma> \<and> \<not> KIR g z"
    define z where "z = Eps ?P"
    from that have g: "current \<Gamma> g" and w': "wave \<Gamma> g" and le_f: "\<And>e. g e \<le> f e"
      and \<E>: "\<E> (TER g) = \<E> (TER f)" by(auto simp add: le_fun_def)
    { with False obtain z where z: "z \<in> RF\<^sup>\<circ> (TER f)" and A: "z \<notin> A \<Gamma>" and neq: "d_OUT g z \<noteq> d_IN g z"
        by(auto simp add: trimming.simps le_fun_def)
      from z have "z \<in> RF\<^sup>\<circ> (\<E> (TER f))" unfolding roofed_circ_essential .
      with \<E> roofed_circ_essential[of \<Gamma> "TER g"] have "z \<in> RF\<^sup>\<circ> (TER g)" by simp
      with A neq have "\<exists>x. ?P x" by auto }
    hence "?P z" unfolding z_def by(rule someI_ex)
    hence RF: "z \<in> RF\<^sup>\<circ> (TER g)" and A: "z \<notin> A \<Gamma>" and neq: "d_OUT g z \<noteq> d_IN g z" by simp_all
    let ?factor = "d_OUT g z / d_IN g z"
    have trim1 [simp]: "trim1 g (y, x) = (if x = z then ?factor else 1) * g (y, x)" for x y
      using False by(auto simp add: trim1_def z_def Let_def)

    from currentD_OUT_IN[OF g A] neq have less: "d_OUT g z < d_IN g z" by auto
    hence "?factor \<le> 1" (is "?factor \<le> _")
      by (auto intro!: divide_le_posI_ennreal simp: zero_less_iff_neq_zero)
    hence le': "?factor * g (y, x) \<le> 1 * g (y, x)" for y x
      by(rule mult_right_mono) simp
    hence le: "trim1 g e \<le> g e" for e by(cases e)simp
    moreover {
      have c: "current \<Gamma> (trim1 g)" using g le
      proof(rule current_leI)
        fix x
        assume x: "x \<notin> A \<Gamma>"
        have "d_OUT (trim1 g) x \<le> d_OUT g x" unfolding d_OUT_def using le' by(auto intro: nn_integral_mono)
        also have "\<dots> \<le> d_IN (trim1 g) x"
        proof(cases "x = z")
          case True
          have "d_OUT g x = d_IN (trim1 g) x" unfolding d_IN_def
            using True currentD_weight_IN[OF g, of x] currentD_OUT_IN[OF g x]
            apply (cases "d_IN g x = 0")
            apply(auto simp add: nn_integral_divide nn_integral_cmult d_IN_def[symmetric] ennreal_divide_times)
            apply (subst ennreal_divide_self)
            apply (auto simp: less_top[symmetric] top_unique weight_finite)
            done
          thus ?thesis by simp
        next
          case False
          have "d_OUT g x \<le> d_IN g x" using x by(rule currentD_OUT_IN[OF g])
          also have "\<dots> \<le> d_IN (trim1 g) x" unfolding d_IN_def using False by(auto intro!: nn_integral_mono)
          finally show ?thesis .
        qed
        finally show "d_OUT (trim1 g) x \<le> d_IN (trim1 g) x" .
      qed
      moreover have le_f: "trim1 g \<le> f" using le le_f by(blast intro: le_funI order_trans)
      moreover have eq: "\<E> (TER (trim1 g)) = \<E> (TER f)" unfolding \<E>[symmetric] using g w' le
      proof(rule essential_eq_leI; intro subsetI)
        fix x
        assume x: "x \<in> \<E> (TER g)"
        hence "x \<in> SINK (trim1 g)" using d_OUT_mono[of "trim1 g" x g, OF le]
          by(auto simp add: SINK.simps)
        moreover from x have "x \<noteq> z" using RF by(auto simp add: roofed_circ_def)
        hence "d_IN (trim1 g) x = d_IN g x" unfolding d_IN_def by simp
        with \<open>x \<in> \<E> (TER g)\<close> have "x \<in> SAT \<Gamma> (trim1 g)" by(auto simp add: SAT.simps)
        ultimately show "x \<in> TER (trim1 g)" by auto
      qed
      moreover have "wave \<Gamma> (trim1 g)"
      proof
        have "separating \<Gamma> (\<E> (TER f))" by(rule separating_essential)(rule waveD_separating[OF w])
        then show "separating \<Gamma> (TER (trim1 g))" unfolding eq[symmetric] by(rule separating_weakening) auto

        fix x
        assume "x \<notin> RF (TER (trim1 g))"
        hence "x \<notin> RF (\<E> (TER (trim1 g)))" unfolding RF_essential .
        hence "x \<notin> RF (TER f)" unfolding eq RF_essential .
        hence "d_OUT f x = 0" by(rule waveD_OUT[OF w])
        with d_OUT_mono[of _ x f, OF le_f[THEN le_funD]]
        show "d_OUT (trim1 g) x = 0" by (metis le_zero_eq)
      qed
      ultimately have "trim1 g \<in> F" by(simp add: F_def) }
    ultimately show ?thesis using that by(simp add: le_fun_def del: trim1)
  qed

  have "bourbaki_witt_fixpoint Inf leq trim1" using chainD increasing unfolding leq_def
    by(intro bourbaki_witt_fixpoint_restrict_rel)(auto intro: Inf_greatest Inf_lower)
  then interpret bourbaki_witt_fixpoint Inf leq trim1 .

  have f_Field: "f \<in> Field leq" using f w by(simp add: leq_def)

  define g where "g = fixp_above f"

  have "g \<in> Field leq" using f_Field unfolding g_def by(rule fixp_above_Field)
  hence le_f: "g \<le> f"
    and g: "current \<Gamma> g"
    and w': "wave \<Gamma> g"
    and TER: "\<E> (TER g) = \<E> (TER f)" by(auto simp add: leq_def intro: le_funI)

  have "trimming g"
  proof(rule ccontr)
    let ?P = "\<lambda>x. x \<in> RF\<^sup>\<circ> (TER g) \<and> x \<notin> A \<Gamma> \<and> \<not> KIR g x"
    define x where "x = Eps ?P"
    assume False: "\<not> ?thesis"
    hence "\<exists>x. ?P x" using le_f g w' TER
      by(auto simp add: trimming.simps roofed_circ_essential[of \<Gamma> "TER g", symmetric] roofed_circ_essential[of \<Gamma> "TER f", symmetric])
    hence "?P x" unfolding x_def by(rule someI_ex)
    hence x: "x \<in> RF\<^sup>\<circ> (TER g)" and A: "x \<notin> A \<Gamma>" and neq: "d_OUT g x \<noteq> d_IN g x" by simp_all
    from neq have "\<exists>y. edge \<Gamma> y x \<and> g (y, x) > 0"
    proof(rule contrapos_np)
      assume "\<not> ?thesis"
      hence "d_IN g x = 0" using currentD_outside[OF g, of _ x]
        by(force simp add: d_IN_def nn_integral_0_iff_AE AE_count_space not_less)
      with currentD_OUT_IN[OF g A] show "KIR g x" by simp
    qed
    then obtain y where y: "edge \<Gamma> y x" and gr0: "g (y, x) > 0" by blast

    have [simp]: "g (y, x) \<noteq> \<top>"
    proof -
      have "g (y, x) \<le> d_OUT g y" by (rule d_OUT_ge_point)
      also have "\<dots> \<le> weight \<Gamma> y" by(rule currentD_weight_OUT[OF g])
      also have "\<dots> < \<top>" by(simp add: weight_finite less_top[symmetric])
      finally show ?thesis by simp
    qed

    from neq have factor: "d_OUT g x / d_IN g x \<noteq> 1"
      by (simp add: divide_eq_1_ennreal)

    have "trim1 g (y, x) = g (y, x) * (d_OUT g x / d_IN g x)"
      by(clarsimp simp add: False trim1_def Let_def x_def[symmetric] mult.commute)
    moreover have "\<dots> \<noteq> g (y, x) * 1" unfolding ennreal_mult_cancel_left using gr0 factor by auto
    ultimately have "trim1 g (y, x) \<noteq> g (y, x)" by auto
    hence "trim1 g \<noteq> g" by(auto simp add: fun_eq_iff)
    moreover have "trim1 g = g" using f_Field unfolding g_def by(rule fixp_above_unfold[symmetric])
    ultimately show False by contradiction
  qed
  then show ?thesis by blast
qed

end

lemma trimming_\<E>:
  fixes \<Gamma> (structure)
  assumes w: "wave \<Gamma> f" and trimming: "trimming \<Gamma> f g"
  shows "\<E> (TER f) = \<E> (TER g)"
proof(rule set_eqI)
  show "x \<in> \<E> (TER f) \<longleftrightarrow> x \<in> \<E> (TER g)" for x
  proof(cases "x \<in> A \<Gamma>")
    case False
    thus ?thesis using trimmingD_\<E>[OF trimming] by blast
  next
    case True
    show ?thesis
    proof
      assume x: "x \<in> \<E> (TER f)"
      hence "x \<in> TER g" using d_OUT_mono[of g x f, OF trimmingD_le[OF trimming]] True
        by(simp add: SINK.simps SAT.A)
      moreover from x have "essential \<Gamma> (B \<Gamma>) (TER f) x" by simp
      then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)" by(rule essentialE_RF) blast
      from p y have "essential \<Gamma> (B \<Gamma>) (\<E> (TER g)) x"
      proof(rule essentialI)
        fix z
        assume "z \<in> set p"
        hence z: "z \<notin> RF (TER f)" by(rule bypass)
        with waveD_separating[OF w, THEN separating_RF_A] have "z \<notin> A \<Gamma>" by blast
        with z have "z \<notin> \<E> (TER g)" using trimmingD_\<E>[OF trimming] by(auto intro: roofed_greaterI)
        thus "z = x \<or> z \<notin> \<E> (TER g)" ..
      qed
      ultimately show "x \<in> \<E> (TER g)" unfolding essential_\<E> by simp
    next
      assume "x \<in> \<E> (TER g)"
      then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER g)" by(rule \<E>_E_RF) blast
      have z: "z \<notin> \<E> (TER f)" if "z \<in> set p" for z
      proof -
        from that have z: "z \<notin> RF (TER g)" by(rule bypass)
        with waveD_separating[OF trimmingD_wave[OF trimming], THEN separating_RF_A] have "z \<notin> A \<Gamma>" by blast
        with z show "z \<notin> \<E> (TER f)" using trimmingD_\<E>[OF trimming] by(auto intro: roofed_greaterI)
      qed
      then have "essential \<Gamma> (B \<Gamma>) (\<E> (TER f)) x" by(intro essentialI[OF p y]) auto
      moreover have "x \<in> TER f"
        using waveD_separating[THEN separating_essential, THEN separatingD, OF w p True y] z
        by auto
      ultimately show "x \<in> \<E> (TER f)" unfolding essential_\<E> by simp
    qed
  qed
qed

subsection \<open>Composition of waves via quotients\<close>

definition quotient_web :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> ('v, 'more) web_scheme"
where \<comment> \<open>Modifications to original Definition 4.9: No incoming edges to nodes in @{const A},
  @{term "B \<Gamma> - A \<Gamma>"} is not part of @{const A} such that @{const A} contains only vertices
  is disjoint from @{const B}. The weight of vertices in @{const B} saturated by @{term f} is
  therefore set to @{term "0 :: ennreal"}.\<close>
  "quotient_web \<Gamma> f =
   \<lparr>edge = \<lambda>x y. edge \<Gamma> x y \<and> x \<notin> roofed_circ \<Gamma> (TER\<^bsub>\<Gamma>\<^esub> f) \<and> y \<notin> roofed \<Gamma> (TER\<^bsub>\<Gamma>\<^esub> f),
    weight = \<lambda>x. if x \<in> RF\<^sup>\<circ>\<^bsub>\<Gamma>\<^esub> (TER\<^bsub>\<Gamma>\<^esub> f) \<or> x \<in> TER\<^bsub>\<Gamma>\<^esub> f \<inter> B \<Gamma> then 0 else weight \<Gamma> x,
    A = \<E>\<^bsub>\<Gamma>\<^esub> (TER\<^bsub>\<Gamma>\<^esub> f) - (B \<Gamma> - A \<Gamma>),
    B = B \<Gamma>,
    \<dots> = web.more \<Gamma>\<rparr>"

lemma quotient_web_sel [simp]:
  fixes \<Gamma> (structure) shows
  "edge (quotient_web \<Gamma> f) x y \<longleftrightarrow> edge \<Gamma> x y \<and> x \<notin> RF\<^sup>\<circ> (TER f) \<and> y \<notin> RF (TER f)"
  "weight (quotient_web \<Gamma> f) x = (if x \<in> RF\<^sup>\<circ> (TER f) \<or> x \<in> TER\<^bsub>\<Gamma>\<^esub> f \<inter> B \<Gamma> then 0 else weight \<Gamma> x)"
  "A (quotient_web \<Gamma> f) = \<E> (TER f)- (B \<Gamma> - A \<Gamma>)"
  "B (quotient_web \<Gamma> f) = B \<Gamma>"
  "web.more (quotient_web \<Gamma> f) = web.more \<Gamma>"
by(simp_all add: quotient_web_def)

lemma vertex_quotient_webD: fixes \<Gamma> (structure) shows
  "vertex (quotient_web \<Gamma> f) x \<Longrightarrow> vertex \<Gamma> x \<and> x \<notin> RF\<^sup>\<circ> (TER f)"
by(auto simp add: vertex_def roofed_circ_def)

lemma path_quotient_web:
  fixes \<Gamma> (structure)
  assumes "path \<Gamma> x p y"
  and "x \<notin> RF\<^sup>\<circ> (TER f)"
  and "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)"
  shows "path (quotient_web \<Gamma> f) x p y"
using assms by(induction)(auto intro: rtrancl_path.intros simp add: roofed_circ_def)

definition restrict_current :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v current \<Rightarrow> 'v current"
where "restrict_current \<Gamma> f g = (\<lambda>(x, y). g (x, y) * indicator (- RF\<^sup>\<circ>\<^bsub>\<Gamma>\<^esub> (TER\<^bsub>\<Gamma>\<^esub> f)) x * indicator (- RF\<^bsub>\<Gamma>\<^esub> (TER\<^bsub>\<Gamma>\<^esub> f)) y)"

abbreviation restrict_curr :: "'v current \<Rightarrow> ('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v current" ("_ \<upharpoonleft> _ '/ _" [100, 0, 100] 100)
where "restrict_curr g \<Gamma> f \<equiv> restrict_current \<Gamma> f g"

lemma restrict_current_simps [simp]: fixes \<Gamma> (structure) shows
  "(g \<upharpoonleft> \<Gamma> / f) (x, y) = (g (x, y) * indicator (- RF\<^sup>\<circ> (TER f)) x * indicator (- RF (TER f)) y)"
by(simp add: restrict_current_def)

lemma d_OUT_restrict_current_outside: fixes \<Gamma> (structure) shows
  "x \<in> RF\<^sup>\<circ> (TER f) \<Longrightarrow> d_OUT (g \<upharpoonleft> \<Gamma> / f) x = 0"
by(simp add: d_OUT_def)

lemma d_IN_restrict_current_outside: fixes \<Gamma> (structure) shows
  "x \<in> RF (TER f) \<Longrightarrow> d_IN (g \<upharpoonleft> \<Gamma> / f) x = 0"
by(simp add: d_IN_def)

lemma restrict_current_le: "(g \<upharpoonleft> \<Gamma> / f) e \<le> g e"
by(cases e)(clarsimp split: split_indicator)

lemma d_OUT_restrict_current_le: "d_OUT (g \<upharpoonleft> \<Gamma> / f) x \<le> d_OUT g x"
unfolding d_OUT_def by(rule nn_integral_mono, simp split: split_indicator)

lemma d_IN_restrict_current_le: "d_IN (g \<upharpoonleft> \<Gamma> / f) x \<le> d_IN g x"
unfolding d_IN_def by(rule nn_integral_mono, simp split: split_indicator)

lemma restrict_current_IN_not_RF:
  fixes \<Gamma> (structure)
  assumes g: "current \<Gamma> g"
  and x: "x \<notin> RF (TER f)"
  shows "d_IN (g \<upharpoonleft> \<Gamma> / f) x = d_IN g x"
proof -
  {
    fix y
    assume y: "y \<in> RF\<^sup>\<circ> (TER f)"
    have "g (y, x) = 0"
    proof(cases "edge \<Gamma> y x")
      case True
      from y have y': "y \<in> RF (TER f)" and essential: "y \<notin> \<E> (TER f)" by(simp_all add: roofed_circ_def)
      moreover from x obtain p z where z: "z \<in> B \<Gamma>" and p: "path \<Gamma> x p z"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER f" "x \<notin> TER f"
        by(clarsimp simp add: roofed_def)
      from roofedD[OF y' rtrancl_path.step, OF True p z] bypass have "x \<in> TER f \<or> y \<in> TER f" by auto
      with roofed_greater[THEN subsetD, of x "TER f" \<Gamma>] x have "x \<notin> TER f" "y \<in> TER f" by auto
      with essential bypass have False
        by(auto dest!: not_essentialD[OF _ rtrancl_path.step, OF _ True p z])
      thus ?thesis ..
    qed(simp add: currentD_outside[OF g]) }
  then show ?thesis unfolding d_IN_def
    using x by(auto intro!: nn_integral_cong split: split_indicator)
qed

lemma restrict_current_IN_A:
  "a \<in> A (quotient_web \<Gamma> f) \<Longrightarrow> d_IN (g \<upharpoonleft> \<Gamma> / f) a = 0"
by(simp add: d_IN_restrict_current_outside roofed_greaterI)

lemma restrict_current_nonneg: "0 \<le> g e \<Longrightarrow> 0 \<le> (g \<upharpoonleft> \<Gamma> / f) e"
by(cases e) simp

lemma in_SINK_restrict_current: "x \<in> SINK g \<Longrightarrow> x \<in> SINK (g \<upharpoonleft> \<Gamma> / f)"
using d_OUT_restrict_current_le[of \<Gamma> f g x]
by(simp add: SINK.simps)

lemma SAT_restrict_current:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and g: "current \<Gamma> g"
  shows "SAT (quotient_web \<Gamma> f) (g \<upharpoonleft> \<Gamma> / f) = RF (TER f) \<union> (SAT \<Gamma> g - A \<Gamma>)" (is "SAT ?\<Gamma> ?g = ?rhs")
proof(intro set_eqI iffI; (elim UnE DiffE)?)
  show "x \<in> ?rhs" if "x \<in> SAT ?\<Gamma> ?g" for x using that
  proof cases
    case IN
    thus ?thesis using currentD_weight_OUT[OF f, of x]
      by(cases "x \<in> RF (TER f)")(auto simp add: d_IN_restrict_current_outside roofed_circ_def restrict_current_IN_not_RF[OF g] SAT.IN currentD_IN[OF g] roofed_greaterI SAT.A SINK.simps RF_in_B split: if_split_asm intro: essentialI[OF rtrancl_path.base])
  qed(simp add: roofed_greaterI)
  show "x \<in> SAT ?\<Gamma> ?g" if "x \<in> RF (TER f)" for x using that
    by(auto simp add: SAT.simps roofed_circ_def d_IN_restrict_current_outside)
  show "x \<in> SAT ?\<Gamma> ?g" if "x \<in> SAT \<Gamma> g" "x \<notin> A \<Gamma>" for x using that
    by(auto simp add: SAT.simps roofed_circ_def d_IN_restrict_current_outside restrict_current_IN_not_RF[OF g])
qed

lemma current_restrict_current:
  fixes \<Gamma> (structure)
  assumes w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
  shows "current (quotient_web \<Gamma> f) (g \<upharpoonleft> \<Gamma> / f)" (is "current ?\<Gamma> ?g")
proof
  show "d_OUT ?g x \<le> weight ?\<Gamma> x" for x
    using d_OUT_restrict_current_le[of \<Gamma> f g x] currentD_weight_OUT[OF g, of x] currentD_OUT[OF g, of x]
    by(auto simp add: d_OUT_restrict_current_outside)
  show "d_IN ?g x \<le> weight ?\<Gamma> x" for x
    using d_IN_restrict_current_le[of \<Gamma> f g x] currentD_weight_IN[OF g, of x]
    by(auto simp add: d_IN_restrict_current_outside roofed_circ_def)
      (subst d_IN_restrict_current_outside[of x \<Gamma> f g]; simp add: roofed_greaterI)

  fix x
  assume "x \<notin> A ?\<Gamma>"
  hence x: "x \<notin> \<E> (TER f) - B \<Gamma>" by simp
  show "d_OUT ?g x \<le> d_IN ?g x"
  proof(cases "x \<in> RF (TER f)")
    case True
    with x have "x \<in> RF\<^sup>\<circ> (TER f) \<union> B \<Gamma>" by(simp add: roofed_circ_def)
    with True show ?thesis using currentD_OUT[OF g, of x] d_OUT_restrict_current_le[of \<Gamma> f g x]
      by(auto simp add: d_OUT_restrict_current_outside d_IN_restrict_current_outside)
  next
    case False
    then obtain p z where z: "z \<in> B \<Gamma>" and p: "path \<Gamma> x p z"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER f" "x \<notin> TER f"
      by(clarsimp simp add: roofed_def)
    from g False have "d_IN ?g x = d_IN g x" by(rule restrict_current_IN_not_RF)
    moreover have "d_OUT ?g x \<le> d_OUT g x"
      by(rule d_OUT_mono restrict_current_le)+
    moreover have "x \<notin> A \<Gamma>"
      using separatingD[OF waveD_separating[OF w] p _ z] bypass by blast
    note currentD_OUT_IN[OF g this]
    ultimately show ?thesis by simp
  qed
next
  show "d_IN ?g a = 0" if "a \<in> A ?\<Gamma>" for a using that by(rule restrict_current_IN_A)
  show "d_OUT ?g b = 0" if "b \<in> B ?\<Gamma>" for b
    using d_OUT_restrict_current_le[of \<Gamma> f g b] currentD_OUT[OF g, of b] that by simp
  show "?g e = 0" if "e \<notin> \<^bold>E\<^bsub>?\<Gamma>\<^esub>" for e using that currentD_outside'[OF g, of e]
    by(cases e)(auto split: split_indicator)
qed

lemma TER_restrict_current:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
  shows "TER g \<subseteq> TER\<^bsub>quotient_web \<Gamma> f\<^esub> (g \<upharpoonleft> \<Gamma> / f)" (is "_ \<subseteq> ?TER" is "_ \<subseteq> TER\<^bsub>?\<Gamma>\<^esub> ?g")
proof
  fix x
  assume x: "x \<in> TER g"
  hence "x \<in> SINK ?g" by(simp add: in_SINK_restrict_current)
  moreover have "x \<in> RF (TER f)" if "x \<in> A \<Gamma>"
    using waveD_separating[OF w, THEN separatingD, OF _ that] by(rule roofedI)
  then have "x \<in> SAT ?\<Gamma> ?g" using SAT_restrict_current[OF f g] x by auto
  ultimately show "x \<in> ?TER" by simp
qed

lemma wave_restrict_current:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
  and w': "wave \<Gamma> g"
  shows "wave (quotient_web \<Gamma> f) (g \<upharpoonleft> \<Gamma> / f)" (is "wave ?\<Gamma> ?g")
proof
  show "separating ?\<Gamma> (TER\<^bsub>?\<Gamma>\<^esub> ?g)" (is "separating _ ?TER")
  proof
    fix x y p
    assume "x \<in> A ?\<Gamma>" "y \<in> B ?\<Gamma>" and p: "path ?\<Gamma> x p y"
    hence x: "x \<in> \<E> (TER f)" and y: "y \<in> B \<Gamma>" and SAT: "x \<in> SAT ?\<Gamma> ?g" by(simp_all add: SAT.A)
    from p have p': "path \<Gamma> x p y" by(rule rtrancl_path_mono) simp

    { assume "x \<notin> ?TER"
      hence "x \<notin> SINK ?g" using SAT by(simp)
      hence "x \<notin> SINK g" using d_OUT_restrict_current_le[of \<Gamma> f g x]
        by(auto simp add: SINK.simps)
      hence "x \<in> RF (TER g)" using waveD_OUT[OF w'] by(auto simp add: SINK.simps)
      from roofedD[OF this p' y] \<open>x \<notin> SINK g\<close> have "(\<exists>z\<in>set p. z \<in> ?TER)"
        using TER_restrict_current[OF f w g] by blast }
    then show "(\<exists>z\<in>set p. z \<in> ?TER) \<or> x \<in> ?TER" by blast
  qed

  fix x
  assume "x \<notin> RF\<^bsub>?\<Gamma>\<^esub> ?TER"
  hence "x \<notin> RF (TER g)"
  proof(rule contrapos_nn)
    assume *: "x \<in> RF (TER g)"
    show "x \<in> RF\<^bsub>?\<Gamma>\<^esub> ?TER"
    proof
      fix p y
      assume "path ?\<Gamma> x p y" "y \<in> B ?\<Gamma>"
      hence "path \<Gamma> x p y" "y \<in> B \<Gamma>" by(auto elim: rtrancl_path_mono)
      from roofedD[OF * this] show "(\<exists>z\<in>set p. z \<in> ?TER) \<or> x \<in> ?TER"
        using TER_restrict_current[OF f w g] by blast
    qed
  qed
  with w' have "d_OUT g x = 0" by(rule waveD_OUT)
  with d_OUT_restrict_current_le[of \<Gamma> f g x]
  show "d_OUT ?g x = 0" by simp
qed

definition plus_current :: "'v current \<Rightarrow> 'v current \<Rightarrow> 'v current"
where "plus_current f g = (\<lambda>e. f e + g e)"

lemma plus_current_simps [simp]: "plus_current f g e = f e + g e"
by(simp add: plus_current_def)

lemma plus_zero_current [simp]: "plus_current f zero_current = f"
by(simp add: fun_eq_iff)

lemma support_flow_plus_current: "support_flow (plus_current f g) \<subseteq> support_flow f \<union> support_flow g"
by(clarsimp simp add: support_flow.simps)

lemma SINK_plus_current: "SINK (plus_current f g) = SINK f \<inter> SINK g"
by(auto simp add: SINK.simps set_eq_iff d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 add_eq_0_iff_both_eq_0)

abbreviation plus_web :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> 'v current \<Rightarrow> 'v current" ("_ \<frown>\<index> _" [66, 66] 65)
where "plus_web \<Gamma> f g \<equiv> plus_current f (g \<upharpoonleft> \<Gamma> / f)"

context
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure) and f g
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current (quotient_web \<Gamma> f) g"
begin

lemma OUT_plus_current: "d_OUT (plus_current f g) x = (if x \<in> RF\<^sup>\<circ> (TER f) then d_OUT f x else d_OUT g x)" (is "d_OUT ?g _ = _")
proof -
  have "d_OUT ?g x = d_OUT f x + d_OUT g x" unfolding plus_current_def
    by(subst d_OUT_add) simp_all
  also have "\<dots> = (if x \<in> RF\<^sup>\<circ> (TER f) then d_OUT f x else d_OUT g x)"
  proof(cases "x \<in> RF\<^sup>\<circ> (TER f)")
    case True
    hence "d_OUT g x = 0" by(intro currentD_outside_OUT[OF g])(auto dest: vertex_quotient_webD)
    thus ?thesis using True by simp
  next
    case False
    hence "d_OUT f x = 0" by(auto simp add: roofed_circ_def SINK.simps dest: waveD_OUT[OF w])
    with False show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma IN_plus_current: "d_IN (plus_current f g) x = (if x \<in> RF (TER f) then d_IN f x else d_IN g x)" (is "d_IN ?g _ = _")
proof -
  have "d_IN ?g x = d_IN f x + d_IN g x" unfolding plus_current_def
    by(subst d_IN_add) simp_all
  also consider (RF) "x \<in> RF (TER f) - (B \<Gamma> - A \<Gamma>)" | (B) "x \<in> RF (TER f)" "x \<in> B \<Gamma> - A \<Gamma>" | (beyond) "x \<notin> RF (TER f)" by blast
  then have "d_IN f x + d_IN g x = (if x \<in> RF (TER f) then d_IN f x else d_IN g x)"
  proof(cases)
    case RF
    hence "d_IN g x = 0"
      by(cases "x \<in> \<E> (TER f)")(auto intro: currentD_outside_IN[OF g] currentD_IN[OF g] dest!: vertex_quotient_webD simp add: roofed_circ_def)
    thus ?thesis using RF by simp
  next
    case B
    hence "d_IN g x = 0" using currentD_outside_IN[OF g, of x] currentD_weight_IN[OF g, of x]
      by(auto dest: vertex_quotient_webD simp add: roofed_circ_def)
    with B show ?thesis by simp
  next
    case beyond
    from f w beyond have "d_IN f x = 0" by(rule wave_not_RF_IN_zero)
    with beyond show ?thesis by simp
  qed
  finally show ?thesis .
qed

lemma current_plus_current: "current \<Gamma> (plus_current f g)" (is "current _ ?g")
proof
  show "d_OUT ?g x \<le> weight \<Gamma> x" for x
    using currentD_weight_OUT[OF g, of x] currentD_weight_OUT[OF f, of x]
    by(auto simp add: OUT_plus_current split: if_split_asm elim: order_trans)
  show "d_IN ?g x \<le> weight \<Gamma> x" for x
    using currentD_weight_IN[OF f, of x] currentD_weight_IN[OF g, of x]
    by(auto simp add: IN_plus_current roofed_circ_def split: if_split_asm elim: order_trans)
  show "d_OUT ?g x \<le> d_IN ?g x" if "x \<notin> A \<Gamma>" for x
  proof(cases "x \<in> \<E> (TER f)")
    case False
    thus ?thesis
      using currentD_OUT_IN[OF f that] currentD_OUT_IN[OF g, of x] that
      by(auto simp add: OUT_plus_current IN_plus_current roofed_circ_def SINK.simps)
  next
    case True
    with that have "d_OUT f x = 0" "weight \<Gamma> x \<le> d_IN f x"
      by(auto simp add: SINK.simps elim: SAT.cases)
    thus ?thesis using that True currentD_OUT_IN[OF g, of x] currentD_weight_OUT[OF g, of x]
      by(auto simp add: OUT_plus_current IN_plus_current roofed_circ_def intro: roofed_greaterI split: if_split_asm)
  qed
  show "d_IN ?g a = 0" if "a \<in> A \<Gamma>" for a
    using wave_A_in_RF[OF w that] currentD_IN[OF f that] by(simp add: IN_plus_current)
  show "d_OUT ?g b = 0" if "b \<in> B \<Gamma>" for b
    using that currentD_OUT[OF f that] currentD_OUT[OF g, of b] that
    by(auto simp add: OUT_plus_current SINK.simps roofed_circ_def intro: roofed_greaterI)
  show "?g e = 0" if "e \<notin> \<^bold>E" for e using currentD_outside'[OF f, of e] currentD_outside'[OF g, of e] that
    by(cases e) auto
qed

lemma in_TER_plus_current:
  assumes RF: "x \<notin> RF\<^sup>\<circ> (TER f)"
  and x: "x \<in> TER\<^bsub>quotient_web \<Gamma> f\<^esub> g" (is "_ \<in> ?TER _")
  shows "x \<in> TER (plus_current f g)"  (is "_ \<in> TER ?g")
proof(cases "x \<in> \<E> (TER f) - (B \<Gamma> - A \<Gamma>)")
  case True
  with x show ?thesis using currentD_IN[OF g, of x]
    by(fastforce intro: roofed_greaterI SAT.intros simp add: SINK.simps OUT_plus_current IN_plus_current elim!: SAT.cases)
next
  case *: False
  have "x \<in> SAT \<Gamma> ?g"
  proof(cases "x \<in> B \<Gamma> - A \<Gamma>")
    case False
    with x RF * have "weight \<Gamma> x \<le> d_IN g x"
      by(auto elim!: SAT.cases split: if_split_asm simp add: essential_BI)
    also have "\<dots> \<le> d_IN ?g x" unfolding plus_current_def by(intro d_IN_mono) simp
    finally show ?thesis ..
  next
    case True
    with * x have "weight \<Gamma> x \<le> d_IN ?g x" using currentD_OUT[OF f, of x]
      by(auto simp add: IN_plus_current RF_in_B SINK.simps roofed_circ_def elim!: SAT.cases split: if_split_asm)
    thus ?thesis ..
  qed
  moreover have "x \<in> SINK ?g" using x by(simp add: SINK.simps OUT_plus_current RF)
  ultimately show ?thesis by simp
qed

context
  assumes w': "wave (quotient_web \<Gamma> f) g"
begin

lemma separating_TER_plus_current:
  assumes x: "x \<in> RF (TER f)" and y: "y \<in> B \<Gamma>" and p: "path \<Gamma> x p y"
  shows "(\<exists>z\<in>set p. z \<in> TER (plus_current f g)) \<or> x \<in> TER (plus_current f g)" (is "_ \<or> _ \<in> TER ?g")
proof -
  from x have "x \<in> RF (\<E> (TER f))" unfolding RF_essential .
  from roofedD[OF this p y] have "\<exists>z\<in>set (x # p). z \<in> \<E> (TER f)" by auto
  from split_list_last_prop[OF this] obtain ys z zs
    where decomp: "x # p = ys @ z # zs" and z: "z \<in> \<E> (TER f)"
    and outside: "\<And>z. z \<in> set zs \<Longrightarrow> z \<notin> \<E> (TER f)" by auto
  have zs: "path \<Gamma> z zs y" using decomp p
    by(cases ys)(auto elim: rtrancl_path_appendE)
  moreover have "z \<notin> RF\<^sup>\<circ> (TER f)" using z by(simp add: roofed_circ_def)
  moreover have RF: "z' \<notin> RF (TER f)" if "z' \<in> set zs" for z'
  proof
    assume "z' \<in> RF (TER f)"
    hence z': "z' \<in> RF (\<E> (TER f))" by(simp only: RF_essential)
    from split_list[OF that] obtain ys' zs' where decomp': "zs = ys' @ z' # zs'" by blast
    with zs have "path \<Gamma> z' zs' y" by(auto elim: rtrancl_path_appendE)
    from roofedD[OF z' this y] outside decomp' show False by auto
  qed
  ultimately have p': "path (quotient_web \<Gamma> f) z zs y" by(rule path_quotient_web)
  show ?thesis
  proof(cases "z \<in> B \<Gamma> - A \<Gamma>")
    case False
    with separatingD[OF waveD_separating[OF w'] p'] z y
    obtain z' where z': "z' \<in> set (z # zs)" and TER: "z' \<in> TER\<^bsub>quotient_web \<Gamma> f\<^esub> g" by auto
    hence "z' \<in> TER ?g" using in_TER_plus_current[of z'] RF[of z'] \<open>z \<notin> RF\<^sup>\<circ> (TER f)\<close> by(auto simp add: roofed_circ_def)
    with decomp z' show ?thesis by(cases ys) auto
  next
    case True
    hence "z \<in> TER ?g" using currentD_OUT[OF current_plus_current, of z] z
      by(auto simp add: SINK.simps SAT.simps IN_plus_current intro: roofed_greaterI)
    then show ?thesis using decomp by(cases ys) auto
  qed
qed

lemma wave_plus_current: "wave \<Gamma> (plus_current f g)" (is "wave _ ?g")
proof
  let ?\<Gamma> = "quotient_web \<Gamma> f"
  let ?TER = "TER\<^bsub>?\<Gamma>\<^esub>"

  show "separating \<Gamma> (TER ?g)" using separating_TER_plus_current[OF wave_A_in_RF[OF w]] by(rule separating)

  fix x
  assume x: "x \<notin> RF (TER ?g)"
  hence "x \<notin> RF (TER f)" by(rule contrapos_nn)(rule roofedI, rule separating_TER_plus_current)
  hence *: "x \<notin> RF\<^sup>\<circ> (TER f)" by(simp add: roofed_circ_def)
  moreover have "x \<notin> RF\<^bsub>?\<Gamma>\<^esub> (?TER g)"
  proof
    assume RF': "x \<in> RF\<^bsub>?\<Gamma>\<^esub> (?TER g)"
    from x obtain p y where y: "y \<in> B \<Gamma>" and p: "path \<Gamma> x p y"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER ?g" and x': "x \<notin> TER ?g"
      by(auto simp add: roofed_def)
    have RF: "z \<notin> RF (TER f)" if "z \<in> set p" for z
    proof
      assume z: "z \<in> RF (TER f)"
      from split_list[OF that] obtain ys' zs' where decomp: "p = ys' @ z # zs'" by blast
      with p have "path \<Gamma> z zs' y" by(auto elim: rtrancl_path_appendE)
      from separating_TER_plus_current[OF z y this] decomp bypass show False by auto
    qed
    with p have "path ?\<Gamma> x p y" using *
      by(induction)(auto intro: rtrancl_path.intros simp add: roofed_circ_def)
    from roofedD[OF RF' this] y consider (x) "x \<in> ?TER g" | (z) z where "z \<in> set p" "z \<in> ?TER g" by auto
    then show False
    proof(cases)
      case x
      with * have "x \<in> TER ?g" by(rule in_TER_plus_current)
      with x' show False by contradiction
    next
      case (z z)
      from z(1) have "z \<notin> RF (TER f)" by(rule RF)
      hence "z \<notin> RF\<^sup>\<circ> (TER f)" by(simp add: roofed_circ_def)
      hence "z \<in> TER ?g" using z(2) by(rule in_TER_plus_current)
      moreover from z(1) have "z \<notin> TER ?g" by(rule bypass)
      ultimately show False by contradiction
    qed
  qed
  with w' have "d_OUT g x = 0" by(rule waveD_OUT)
  ultimately show "d_OUT ?g x = 0" by(simp add: OUT_plus_current)
qed

end

end

lemma d_OUT_plus_web:
  fixes \<Gamma> (structure)
  shows "d_OUT (f \<frown> g) x = d_OUT f x + d_OUT (g \<upharpoonleft> \<Gamma> / f) x" (is "?lhs = ?rhs")
proof -
  have "?lhs = d_OUT f x + (\<Sum>\<^sup>+ y. (if x \<in> RF\<^sup>\<circ> (TER f) then 0 else g (x, y) * indicator (- RF (TER f)) y))"
    unfolding d_OUT_def by(subst nn_integral_add[symmetric])(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ?rhs" by(auto simp add: d_OUT_def intro!: arg_cong2[where f="(+)"] nn_integral_cong)
  finally show "?thesis" .
qed

lemma d_IN_plus_web:
  fixes \<Gamma> (structure)
  shows "d_IN (f \<frown> g) y = d_IN f y + d_IN (g \<upharpoonleft> \<Gamma> / f) y" (is "?lhs = ?rhs")
proof -
  have "?lhs = d_IN f y + (\<Sum>\<^sup>+ x. (if y \<in> RF (TER f) then 0 else g (x, y) * indicator (- RF\<^sup>\<circ> (TER f)) x))"
    unfolding d_IN_def by(subst nn_integral_add[symmetric])(auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> = ?rhs" by(auto simp add: d_IN_def intro!: arg_cong2[where f="(+)"] nn_integral_cong)
  finally show ?thesis .
qed

lemma plus_web_greater: "f e \<le> (f \<frown>\<^bsub>\<Gamma>\<^esub> g) e"
by(cases e)(auto split: split_indicator)

lemma current_plus_web:
  fixes \<Gamma> (structure)
  shows "\<lbrakk> current \<Gamma> f; wave \<Gamma> f; current \<Gamma> g \<rbrakk> \<Longrightarrow> current \<Gamma> (f \<frown> g)"
by(blast intro: current_plus_current current_restrict_current)

context
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure)
  and f g :: "'v current"
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
begin

context
  fixes x :: "'v"
  assumes x: "x \<in> \<E> (TER f \<union> TER g)"
begin

qualified lemma RF_f: "x \<notin> RF\<^sup>\<circ> (TER f)"
proof
  assume *: "x \<in> RF\<^sup>\<circ> (TER f)"

  from x obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    and bypass: "\<And>z. \<lbrakk>x \<noteq> y; z \<in> set p\<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> TER f \<union> TER g" by(rule \<E>_E) blast
  from rtrancl_path_distinct[OF p] obtain p'
    where p: "path \<Gamma> x p' y" and p': "set p' \<subseteq> set p" and distinct: "distinct (x # p')" .

  from * have x': "x \<in> RF (TER f)" and \<E>: "x \<notin> \<E> (TER f)" by(auto simp add: roofed_circ_def)
  hence "x \<notin> TER f" using not_essentialD[OF _ p y] p' bypass by blast
  with roofedD[OF x' p y] obtain z where z: "z \<in> set p'" "z \<in> TER f" by auto
  with p have "y \<in> set p'" by(auto dest!: rtrancl_path_last intro: last_in_set)
  with distinct have "x \<noteq> y" by auto
  with bypass z p' distinct show False by auto
qed

private lemma RF_g: "x \<notin> RF\<^sup>\<circ> (TER g)"
proof
  assume *: "x \<in> RF\<^sup>\<circ> (TER g)"

  from x obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    and bypass: "\<And>z. \<lbrakk>x \<noteq> y; z \<in> set p\<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> TER f \<union> TER g" by(rule \<E>_E) blast
  from rtrancl_path_distinct[OF p] obtain p'
    where p: "path \<Gamma> x p' y" and p': "set p' \<subseteq> set p" and distinct: "distinct (x # p')" .

  from * have x': "x \<in> RF (TER g)" and \<E>: "x \<notin> \<E> (TER g)" by(auto simp add: roofed_circ_def)
  hence "x \<notin> TER g" using not_essentialD[OF _ p y] p' bypass by blast
  with roofedD[OF x' p y] obtain z where z: "z \<in> set p'" "z \<in> TER g" by auto
  with p have "y \<in> set p'" by(auto dest!: rtrancl_path_last intro: last_in_set)
  with distinct have "x \<noteq> y" by auto
  with bypass z p' distinct show False by auto
qed

lemma TER_plus_web_aux:
  assumes SINK: "x \<in> SINK (g \<upharpoonleft> \<Gamma> / f)" (is "_ \<in> SINK ?g")
  shows "x \<in> TER (f \<frown> g)"
proof
  from x obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    and bypass: "\<And>z. \<lbrakk>x \<noteq> y; z \<in> set p\<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> TER f \<union> TER g" by(rule \<E>_E) blast
  from rtrancl_path_distinct[OF p] obtain p'
    where p: "path \<Gamma> x p' y" and p': "set p' \<subseteq> set p" and distinct: "distinct (x # p')" .

  from RF_f have "x \<in> SINK f"
    by(auto simp add: roofed_circ_def SINK.simps dest: waveD_OUT[OF w])
  thus "x \<in> SINK (f \<frown> g)" using SINK
    by(simp add: SINK.simps d_OUT_plus_web)
  show "x \<in> SAT \<Gamma> (f \<frown> g)"
  proof(cases "x \<in> TER f")
    case True
    hence "x \<in> SAT \<Gamma> f" by simp
    moreover have "\<dots> \<subseteq> SAT \<Gamma> (f \<frown> g)" by(rule SAT_mono plus_web_greater)+
    ultimately show ?thesis by blast
  next
    case False
    with x have "x \<in> TER g" by auto
    from False RF_f have "x \<notin> RF (TER f)" by(auto simp add: roofed_circ_def)
    moreover { fix z
      assume z: "z \<in> RF\<^sup>\<circ> (TER f)"
      have "(z, x) \<notin> \<^bold>E"
      proof
        assume "(z, x) \<in> \<^bold>E"
        hence path': "path \<Gamma> z (x # p') y" using p by(simp add: rtrancl_path.step)
        from z have "z \<in> RF (TER f)" by(simp add: roofed_circ_def)
        from roofedD[OF this path' y] False
        consider (path) z' where  "z' \<in> set p'" "z' \<in> TER f" | (TER) "z \<in> TER f" by auto
        then show False
        proof cases
          { case (path z')
            with p distinct have "x \<noteq> y"
              by(auto 4 3 intro: last_in_set elim: rtrancl_path.cases dest: rtrancl_path_last[symmetric])
            from bypass[OF this, of z'] path False p' show False by auto }
          note that = this
          case TER
          with z have "\<not> essential \<Gamma> (B \<Gamma>) (TER f) z" by(simp add: roofed_circ_def)
          from not_essentialD[OF this path' y] False obtain z' where "z' \<in> set p'" "z' \<in> TER f" by auto
          thus False by(rule that)
        qed
      qed }
    ultimately have "d_IN ?g x = d_IN g x" unfolding d_IN_def
      by(intro nn_integral_cong)(clarsimp split: split_indicator simp add: currentD_outside[OF g])
    hence "d_IN (f \<frown> g) x \<ge> d_IN g x"
      by(simp add: d_IN_plus_web)
    with \<open>x \<in> TER g\<close> show ?thesis by(auto elim!: SAT.cases intro: SAT.intros)
  qed
qed

qualified lemma SINK_TER_in'':
  assumes "\<And>x. x \<notin> RF (TER g) \<Longrightarrow> d_OUT g x = 0"
  shows "x \<in> SINK g"
using RF_g by(auto simp add: roofed_circ_def SINK.simps assms)

end

lemma wave_plus: "wave (quotient_web \<Gamma> f) (g \<upharpoonleft> \<Gamma> / f) \<Longrightarrow> wave \<Gamma> (f \<frown> g)"
using f w by(rule wave_plus_current)(rule current_restrict_current[OF w g])

lemma TER_plus_web'':
  assumes "\<And>x. x \<notin> RF (TER g) \<Longrightarrow> d_OUT g x = 0"
  shows "\<E> (TER f \<union> TER g) \<subseteq> TER (f \<frown> g)"
proof
  fix x
  assume *: "x \<in> \<E> (TER f \<union> TER g)"
  moreover have "x \<in> SINK (g \<upharpoonleft> \<Gamma> / f)"
    by(rule in_SINK_restrict_current)(rule Max_Flow_Min_Cut_Countable.SINK_TER_in''[OF f w g * assms])
  ultimately show "x \<in> TER (f \<frown> g)" by(rule TER_plus_web_aux)
qed

lemma TER_plus_web': "wave \<Gamma> g \<Longrightarrow> \<E> (TER f \<union> TER g) \<subseteq> TER (f \<frown> g)"
by(rule TER_plus_web'')(rule waveD_OUT)

lemma wave_plus': "wave \<Gamma> g \<Longrightarrow> wave \<Gamma> (f \<frown> g)"
by(rule wave_plus)(rule wave_restrict_current[OF f w g])

end

lemma RF_TER_plus_web:
  fixes \<Gamma> (structure)
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
  and w': "wave \<Gamma> g"
  shows "RF (TER (f \<frown> g)) = RF (TER f \<union> TER g)"
proof
  have "RF (\<E> (TER f \<union> TER g)) \<subseteq> RF (TER (f \<frown> g))"
    by(rule roofed_mono)(rule TER_plus_web'[OF f w g w'])
  also have "RF (\<E> (TER f \<union> TER g)) = RF (TER f \<union> TER g)" by(rule RF_essential)
  finally show "\<dots> \<subseteq> RF (TER (f \<frown> g))" .
next
  have fg: "current \<Gamma> (f \<frown> g)" using f w g by(rule current_plus_web)
  show "RF (TER (f \<frown> g)) \<subseteq> RF (TER f \<union> TER g)"
  proof(intro subsetI roofedI)
    fix x p y
    assume RF: "x \<in> RF (TER (f \<frown> g))" and p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    from roofedD[OF RF p y] obtain z where z: "z \<in> set (x # p)" and TER: "z \<in> TER (f \<frown> g)" by auto
    from TER have SINK: "z \<in> SINK f"
      by(auto simp add: SINK.simps d_OUT_plus_web add_eq_0_iff_both_eq_0)
    from TER have "z \<in> SAT \<Gamma> (f \<frown> g)" by simp
    hence SAT: "z \<in> SAT \<Gamma> f \<union> SAT \<Gamma> g"
      by(cases "z \<in> RF (TER f)")(auto simp add: currentD_SAT[OF f] currentD_SAT[OF g] currentD_SAT[OF fg] d_IN_plus_web d_IN_restrict_current_outside restrict_current_IN_not_RF[OF g] wave_not_RF_IN_zero[OF f w])

    show "(\<exists>z\<in>set p. z \<in> TER f \<union> TER g) \<or> x \<in> TER f \<union> TER g"
    proof(cases "z \<in> RF (TER g)")
      case False
      hence "z \<in> SINK g" by(simp add: SINK.simps waveD_OUT[OF w'])
      with SINK SAT have "z \<in> TER f \<union> TER g" by auto
      thus ?thesis using z by auto
    next
      case True
      from split_list[OF z] obtain ys zs where split: "x # p = ys @ z # zs" by blast
      with p have "path \<Gamma> z zs y" by(auto elim: rtrancl_path_appendE simp add: Cons_eq_append_conv)
      from roofedD[OF True this y] split show ?thesis by(auto simp add: Cons_eq_append_conv)
    qed
  qed
qed

lemma RF_TER_Sup:
  fixes \<Gamma> (structure)
  assumes f: "\<And>f. f \<in> Y \<Longrightarrow> current \<Gamma> f"
  and w: "\<And>f. f \<in> Y \<Longrightarrow> wave \<Gamma> f"
  and Y: "Complete_Partial_Order.chain (\<le>) Y" "Y \<noteq> {}" "countable (support_flow (Sup Y))"
  shows "RF (TER (Sup Y)) = RF (\<Union>f\<in>Y. TER f)"
proof(rule set_eqI iffI)+
  fix x
  assume x: "x \<in> RF (TER (Sup Y))"
  have "x \<in> RF (RF (\<Union>f\<in>Y. TER f))"
  proof
    fix p y
    assume p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    from roofedD[OF x p y] obtain z where z: "z \<in> set (x # p)" and TER: "z \<in> TER (Sup Y)" by auto
    from TER have SINK: "z \<in> SINK f" if "f \<in> Y" for f using that by(auto simp add: SINK_Sup[OF Y])

    from Y(2) obtain f where y: "f \<in> Y" by blast

    show "(\<exists>z\<in>set p. z \<in> RF (\<Union>f\<in>Y. TER f)) \<or> x \<in> RF (\<Union>f\<in>Y. TER f)"
    proof(cases "\<exists>f\<in>Y. z \<in> RF (TER f)")
      case True
      then obtain f where fY: "f \<in> Y" and zf: "z \<in> RF (TER f)" by blast
      from zf have "z \<in> RF (\<Union>f\<in>Y. TER f)" by(rule in_roofed_mono)(auto intro: fY)
      with z show ?thesis by auto
    next
      case False
      hence *: "d_IN f z = 0" if "f \<in> Y" for f using that by(auto intro: wave_not_RF_IN_zero[OF f w])
      hence "d_IN (Sup Y) z = 0" using Y(2) by(simp add: d_IN_Sup[OF Y])
      with TER have "z \<in> SAT \<Gamma> f" using *[OF y]
        by(simp add: SAT.simps)
      with SINK[OF y] have "z \<in> TER f" by simp
      with z y show ?thesis by(auto intro: roofed_greaterI)
    qed
  qed
  then show "x \<in> RF (\<Union>f\<in>Y. TER f)" unfolding roofed_idem .
next
  fix x
  assume x: "x \<in> RF (\<Union>f\<in>Y. TER f)"
  have "x \<in> RF (RF (TER (\<Squnion>Y)))"
  proof(rule roofedI)
    fix p y
    assume p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    from roofedD[OF x p y] obtain z f where *: "z \<in> set (x # p)"
      and **: "f \<in> Y" and TER: "z \<in> TER f" by auto
    have "z \<in> RF (TER (Sup Y))"
    proof(rule ccontr)
      assume z: "z \<notin> RF (TER (Sup Y))"
      have "wave \<Gamma> (Sup Y)" using Y(1-2) w Y(3) by(rule wave_lub)
      hence "d_OUT (Sup Y) z = 0" using z by(rule waveD_OUT)
      hence "z \<in> SINK (Sup Y)" by(simp add: SINK.simps)
      moreover have "z \<in> SAT \<Gamma> (Sup Y)" using TER SAT_Sup_upper[OF **, of \<Gamma>] by blast
      ultimately have "z \<in> TER (Sup Y)" by simp
      hence "z \<in> RF (TER (Sup Y))" by(rule roofed_greaterI)
      with z show False by contradiction
    qed
    thus "(\<exists>z\<in>set p. z \<in> RF (TER (Sup Y))) \<or> x \<in> RF (TER (Sup Y))" using * by auto
  qed
  then show "x \<in> RF (TER (\<Squnion>Y))" unfolding roofed_idem .
qed

lemma loose_quotient_web:
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure)
  assumes weight_finite: "\<And>x. weight \<Gamma> x \<noteq> \<top>"
  and f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and maximal: "\<And>w. \<lbrakk> current \<Gamma> w; wave \<Gamma> w; f \<le> w \<rbrakk> \<Longrightarrow> f = w"
  shows "loose (quotient_web \<Gamma> f)" (is "loose ?\<Gamma>")
proof
  fix g
  assume g: "current ?\<Gamma> g" and w': "wave ?\<Gamma> g"
  let ?g = "plus_current f g"
  from f w g have "current \<Gamma> ?g" "wave \<Gamma> ?g" by(rule current_plus_current wave_plus_current)+ (rule w')
  moreover have "f \<le> ?g" by(clarsimp simp add: le_fun_def add_eq_0_iff_both_eq_0)
  ultimately have eq: "f = ?g" by(rule maximal)
  have "g e = 0" for e
  proof(cases e)
    case (Pair x y)
    have "f e \<le> d_OUT f x" unfolding Pair by (rule d_OUT_ge_point)
    also have "\<dots> \<le> weight \<Gamma> x" by(rule currentD_weight_OUT[OF f])
    also have "\<dots> < \<top>" by(simp add: weight_finite less_top[symmetric])
    finally show "g e = 0" using Pair eq[THEN fun_cong, of e]
      by(cases "f e" "g e" rule: ennreal2_cases)(simp_all add: fun_eq_iff)
  qed
  thus "g = (\<lambda>_. 0)" by(simp add: fun_eq_iff)
next
  have 0: "current ?\<Gamma> zero_current" by(simp add: )
  show "\<not> hindrance ?\<Gamma> zero_current"
  proof
    assume "hindrance ?\<Gamma> zero_current"
    then obtain x where a: "x \<in> A ?\<Gamma>" and \<E>: "x \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> zero_current)"
      and "d_OUT zero_current x < weight ?\<Gamma> x" by cases
    from a have "x \<in> \<E> (TER f)" by simp
    then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
      and bypass: "\<And>z. \<lbrakk>x \<noteq> y; z \<in> set p\<rbrakk> \<Longrightarrow> z = x \<or> z \<notin> TER f" by(rule \<E>_E) blast
    from p obtain p' where p': "path \<Gamma> x p' y" and distinct: "distinct (x # p')"
      and subset: "set p' \<subseteq> set p" by(auto elim: rtrancl_path_distinct)
    note p'
    moreover have RF: "z \<notin> RF (TER f)" if "z \<in> set p'" for z
    proof
      assume z: "z \<in> RF (TER f)"
      from split_list[OF that] obtain ys zs where decomp: "p' = ys @ z # zs" by blast
      with p' have "y \<in> set p'" by(auto dest!: rtrancl_path_last intro: last_in_set)
      with distinct have neq: "x \<noteq> y" by auto
      from decomp p' have "path \<Gamma> z zs y" by(auto elim: rtrancl_path_appendE)
      from roofedD[OF z this y] obtain z' where "z' \<in> set (z # zs)" "z' \<in> TER f" by auto
      with distinct decomp subset bypass[OF neq] show False by auto
    qed
    moreover have "x \<notin> RF\<^sup>\<circ> (TER f)" using \<open>x \<in> \<E> (TER f)\<close> by(simp add: roofed_circ_def)
    ultimately have p'': "path ?\<Gamma> x p' y"
      by(induction)(auto intro: rtrancl_path.intros simp add: roofed_circ_def)
    from a \<E> have "\<not> essential ?\<Gamma> (B ?\<Gamma>) (TER\<^bsub>?\<Gamma>\<^esub> zero_current) x" by simp
    from not_essentialD[OF this p''] y obtain z where neq: "x \<noteq> y"
      and "z \<in> set p'" "z \<noteq> x" "z \<in> TER\<^bsub>?\<Gamma>\<^esub> zero_current" by auto
    moreover with subset RF[of z] have "z \<in> TER f"
      using currentD_weight_OUT[OF f, of z] currentD_weight_IN[OF f, of z]
      by(auto simp add: roofed_circ_def SINK.simps intro: SAT.IN split: if_split_asm)
    ultimately show False using bypass[of z] subset by auto
  qed
qed

lemma quotient_web_trimming:
  fixes \<Gamma> (structure)
  assumes w: "wave \<Gamma> f"
  and trimming: "trimming \<Gamma> f g"
  shows "quotient_web \<Gamma> f = quotient_web \<Gamma> g" (is "?lhs = ?rhs")
proof(rule web.equality)
  from trimming have \<E>: "\<E> (TER g) - A \<Gamma> = \<E> (TER f) - A \<Gamma>" by cases

  have RF: "RF (TER g) = RF (TER f)"
    by(subst (1 2) RF_essential[symmetric])(simp only: trimming_\<E>[OF w trimming])
  have RFc: "RF\<^sup>\<circ> (TER g) = RF\<^sup>\<circ> (TER f)"
    by(subst (1 2) roofed_circ_essential[symmetric])(simp only: trimming_\<E>[OF w trimming])

  show "edge ?lhs = edge ?rhs" by(rule ext)+(simp add: RF RFc)
  have "weight ?lhs = (\<lambda>x. if x \<in> RF\<^sup>\<circ> (TER g) \<or> x \<in> RF (TER g) \<inter> B \<Gamma> then 0 else weight \<Gamma> x)"
    unfolding RF RFc by(auto simp add: fun_eq_iff RF_in_B)
  also have "\<dots> = weight ?rhs" by(auto simp add: fun_eq_iff RF_in_B)
  finally show "weight ?lhs = weight ?rhs" .

  show "A ?lhs = A ?rhs" unfolding quotient_web_sel trimming_\<E>[OF w trimming] ..
qed simp_all

subsection \<open>Well-formed webs\<close>

locale web =
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure)
  assumes A_in: "x \<in> A \<Gamma> \<Longrightarrow> \<not> edge \<Gamma> y x"
  and B_out: "x \<in> B \<Gamma> \<Longrightarrow> \<not> edge \<Gamma> x y"
  and A_vertex: "A \<Gamma> \<subseteq> \<^bold>V"
  and disjoint: "A \<Gamma> \<inter> B \<Gamma> = {}"
  and no_loop: "\<And>x. \<not> edge \<Gamma> x x"
  and weight_outside: "\<And>x. x \<notin> \<^bold>V \<Longrightarrow> weight \<Gamma> x = 0"
  and weight_finite [simp]: "\<And>x. weight \<Gamma> x \<noteq> \<top>"
begin

lemma web_weight_update:
  assumes "\<And>x. \<not> vertex \<Gamma> x \<Longrightarrow> w x = 0"
  and "\<And>x. w x \<noteq> \<top>"
  shows "web (\<Gamma>\<lparr>weight := w\<rparr>)"
by unfold_locales(simp_all add: A_in B_out A_vertex disjoint no_loop assms)

lemma currentI [intro?]:
  assumes "\<And>x. d_OUT f x \<le> weight \<Gamma> x"
  and "\<And>x. d_IN f x \<le> weight \<Gamma> x"
  and OUT_IN: "\<And>x. \<lbrakk> x \<notin> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> d_OUT f x \<le> d_IN f x"
  and outside: "\<And>e. e \<notin> \<^bold>E \<Longrightarrow> f e = 0"
  shows "current \<Gamma> f"
proof
  show "d_IN f a = 0" if "a \<in> A \<Gamma>" for a using that
    by(auto simp add: d_IN_def nn_integral_0_iff emeasure_count_space_eq_0 A_in intro: outside)
  show "d_OUT f b = 0" if "b \<in> B \<Gamma>" for b using that
    by(auto simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 B_out intro: outside)
  then show "d_OUT f x \<le> d_IN f x" if "x \<notin> A \<Gamma>" for x using OUT_IN[OF that]
    by(cases "x \<in> B \<Gamma>") auto
qed(blast intro: assms)+

lemma currentD_finite_IN:
  assumes f: "current \<Gamma> f"
  shows "d_IN f x \<noteq> \<top>"
proof(cases "x \<in> \<^bold>V")
  case True
  have "d_IN f x \<le> weight \<Gamma> x" using f by(rule currentD_weight_IN)
  also have "\<dots> < \<top>" using True weight_finite[of x] by (simp add: less_top[symmetric])
  finally show ?thesis by simp
next
  case False
  then have "d_IN f x = 0"
    by(auto simp add: d_IN_def nn_integral_0_iff emeasure_count_space_eq_0 vertex_def intro: currentD_outside[OF f])
  thus ?thesis by simp
qed

lemma currentD_finite_OUT:
  assumes f: "current \<Gamma> f"
  shows "d_OUT f x \<noteq> \<top>"
proof(cases "x \<in> \<^bold>V")
  case True
  have "d_OUT f x \<le> weight \<Gamma> x" using f by(rule currentD_weight_OUT)
  also have "\<dots> < \<top>" using True weight_finite[of x] by (simp add: less_top[symmetric])
  finally show ?thesis by simp
next
  case False
  then have "d_OUT f x = 0"
    by(auto simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 vertex_def intro: currentD_outside[OF f])
  thus ?thesis by simp
qed

lemma currentD_finite:
  assumes f: "current \<Gamma> f"
  shows "f e \<noteq> \<top>"
proof(cases e)
  case (Pair x y)
  have "f (x, y) \<le> d_OUT f x" by (rule d_OUT_ge_point)
  also have "\<dots> < \<top>" using currentD_finite_OUT[OF f] by (simp add: less_top[symmetric])
  finally show ?thesis by(simp add: Pair)
qed

lemma web_quotient_web: "web (quotient_web \<Gamma> f)" (is "web ?\<Gamma>")
proof
  show "\<not> edge ?\<Gamma> y x" if "x \<in> A ?\<Gamma>" for x y using that by(auto intro: roofed_greaterI)
  show "\<not> edge ?\<Gamma> x y" if "x \<in> B ?\<Gamma>" for x y using that by(auto simp add: B_out)
  show "A ?\<Gamma> \<inter> B ?\<Gamma> = {}" using disjoint by auto
  show "A ?\<Gamma> \<subseteq> \<^bold>V\<^bsub>?\<Gamma>\<^esub>"
  proof
    fix x
    assume "x \<in> A ?\<Gamma>"
    hence \<E>: "x \<in> \<E> (TER f)" and x: "x \<notin> B \<Gamma>" using disjoint by auto
    from this(1) obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)"
      by(rule \<E>_E_RF) blast
    from p y x have "p \<noteq> []" by(auto simp add: rtrancl_path_simps)
    with rtrancl_path_nth[OF p, of 0] have "edge \<Gamma> x (p ! 0)" by simp
    moreover have "x \<notin> RF\<^sup>\<circ> (TER f)" using \<E> by(simp add: roofed_circ_def)
    moreover have "p ! 0 \<notin> RF (TER f)" using bypass \<open>p \<noteq> []\<close> by auto
    ultimately have "edge ?\<Gamma> x (p ! 0)" by simp
    thus "x \<in> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" by(auto intro: vertexI1)
  qed
  show "\<not> edge ?\<Gamma> x x" for x by(simp add: no_loop)
  show "weight ?\<Gamma> x = 0" if "x \<notin> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" for x
  proof(cases "x \<in> RF\<^sup>\<circ> (TER f) \<or> x \<in> TER f \<inter> B \<Gamma>")
    case True thus ?thesis by simp
  next
    case False
    hence RF: "x \<notin> RF\<^sup>\<circ> (TER f)" and B: "x \<in> B \<Gamma> \<Longrightarrow> x \<notin> TER f" by auto
    from RF obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)"
      apply(cases "x \<notin> RF (RF (TER f))")
       apply(auto elim!: not_roofedE)[1]
      apply(auto simp add: roofed_circ_def roofed_idem elim: essentialE_RF)
      done
    from that have "p = []" using p y B RF bypass
      by(auto 4 3 simp add: vertex_def dest!: rtrancl_path_nth[where i=0])
    with p have xy: "x = y" by(simp add: rtrancl_path_simps)
    with B y have "x \<notin> TER f" by simp
    hence RF': "x \<notin> RF (TER f)" using xy y by(subst RF_in_B) auto
    have "\<not> vertex \<Gamma> x"
    proof
      assume "vertex \<Gamma> x"
      then obtain x' where "edge \<Gamma> x' x" using xy y by(auto simp add: vertex_def B_out)
      moreover hence "x' \<notin> RF\<^sup>\<circ> (TER f)" using RF' by(auto dest: RF_circ_edge_forward)
      ultimately have "edge ?\<Gamma> x' x" using RF' by simp
      hence "vertex ?\<Gamma> x" by(rule vertexI2)
      with that show False by simp
    qed
    thus ?thesis by(simp add: weight_outside)
  qed
  show "weight ?\<Gamma> x \<noteq> \<top>" for x by simp
qed

end

locale countable_web = web \<Gamma>
  for \<Gamma> :: "('v, 'more) web_scheme" (structure)
  +
  assumes edge_antiparallel: "edge \<Gamma> x y \<Longrightarrow> \<not> edge \<Gamma> y x"
  and countable [simp]: "countable \<^bold>E"
begin

lemma countable_V [simp]: "countable \<^bold>V"
by(simp add: "\<^bold>V_def")

lemma countable_web_quotient_web: "countable_web (quotient_web \<Gamma> f)" (is "countable_web ?\<Gamma>")
proof -
  interpret r: web ?\<Gamma> by(rule web_quotient_web)
  show ?thesis
  proof
    have "\<^bold>E\<^bsub>?\<Gamma>\<^esub> \<subseteq> \<^bold>E" by auto
    then show "countable \<^bold>E\<^bsub>?\<Gamma>\<^esub>" by(rule countable_subset) simp
  qed(simp add: edge_antiparallel)
qed

end

subsection \<open>Subtraction of a wave\<close>

definition minus_web :: "('v, 'more) web_scheme \<Rightarrow> 'v current \<Rightarrow> ('v, 'more) web_scheme" (infixl "\<ominus>" 65) \<comment> \<open>Definition 6.6\<close>
where "\<Gamma> \<ominus> f = \<Gamma>\<lparr>weight := \<lambda>x. if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT f x else weight \<Gamma> x + d_OUT f x - d_IN f x\<rparr>"

lemma minus_web_sel [simp]:
  "edge (\<Gamma> \<ominus> f) = edge \<Gamma>"
  "weight (\<Gamma> \<ominus> f) x = (if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT f x else weight \<Gamma> x + d_OUT f x - d_IN f x)"
  "A (\<Gamma> \<ominus> f) = A \<Gamma>"
  "B (\<Gamma> \<ominus> f) = B \<Gamma>"
  "\<^bold>V\<^bsub>\<Gamma> \<ominus> f\<^esub> = \<^bold>V\<^bsub>\<Gamma>\<^esub>"
  "\<^bold>E\<^bsub>\<Gamma> \<ominus> f\<^esub> = \<^bold>E\<^bsub>\<Gamma>\<^esub>"
  "web.more (\<Gamma> \<ominus> f) = web.more \<Gamma>"
by(auto simp add: minus_web_def vertex_def)

lemma vertex_minus_web [simp]: "vertex (\<Gamma> \<ominus> f) = vertex \<Gamma>"
by(simp add: vertex_def fun_eq_iff)

lemma roofed_gen_minus_web [simp]: "roofed_gen (\<Gamma> \<ominus> f) = roofed_gen \<Gamma>"
by(simp add: fun_eq_iff roofed_def)

lemma minus_zero_current [simp]: "\<Gamma> \<ominus> zero_current = \<Gamma>"
by(rule web.equality)(simp_all add: fun_eq_iff)

lemma (in web) web_minus_web:
  assumes f: "current \<Gamma> f"
  shows "web (\<Gamma> \<ominus> f)"
unfolding minus_web_def
apply(rule web_weight_update)
apply(auto simp: weight_outside currentD_weight_IN[OF f] currentD_outside_OUT[OF f]
                 currentD_outside_IN[OF f] currentD_weight_OUT[OF f] currentD_finite_OUT[OF f])
done

section \<open>Bipartite webs\<close>

locale countable_bipartite_web =
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure)
  assumes bipartite_V: "\<^bold>V \<subseteq> A \<Gamma> \<union> B \<Gamma>"
  and A_vertex: "A \<Gamma> \<subseteq> \<^bold>V"
  and bipartite_E: "edge \<Gamma> x y \<Longrightarrow> x \<in> A \<Gamma> \<and> y \<in> B \<Gamma>"
  and disjoint: "A \<Gamma> \<inter> B \<Gamma> = {}"
  and weight_outside: "\<And>x. x \<notin> \<^bold>V \<Longrightarrow> weight \<Gamma> x = 0"
  and weight_finite [simp]: "\<And>x. weight \<Gamma> x \<noteq> \<top>"
  and countable_E [simp]: "countable \<^bold>E"
begin

lemma not_vertex: "\<lbrakk> x \<notin> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> \<not> vertex \<Gamma> x"
using bipartite_V by blast

lemma no_loop: "\<not> edge \<Gamma> x x"
using disjoint by(auto dest: bipartite_E)

lemma edge_antiparallel: "edge \<Gamma> x y \<Longrightarrow> \<not> edge \<Gamma> y x"
using disjoint by(auto dest: bipartite_E)

lemma A_in: "x \<in> A \<Gamma> \<Longrightarrow> \<not> edge \<Gamma> y x"
using disjoint by(auto dest: bipartite_E)

lemma B_out: "x \<in> B \<Gamma> \<Longrightarrow> \<not> edge \<Gamma> x y"
using disjoint by(auto dest: bipartite_E)

sublocale countable_web using disjoint
by(unfold_locales)(auto simp add: A_in B_out A_vertex no_loop weight_outside  edge_antiparallel)

lemma currentD_OUT':
  assumes f: "current \<Gamma> f"
  and x: "x \<notin> A \<Gamma>"
  shows "d_OUT f x = 0"
using currentD_outside_OUT[OF f, of x] x currentD_OUT[OF f, of x] bipartite_V by auto

lemma currentD_IN':
  assumes f: "current \<Gamma> f"
  and x: "x \<notin> B \<Gamma>"
  shows "d_IN f x = 0"
using currentD_outside_IN[OF f, of x] x currentD_IN[OF f, of x] bipartite_V by auto

lemma current_bipartiteI [intro?]:
  assumes OUT: "\<And>x. d_OUT f x \<le> weight \<Gamma> x"
  and IN: "\<And>x. d_IN f x \<le> weight \<Gamma> x"
  and outside: "\<And>e. e \<notin> \<^bold>E \<Longrightarrow> f e = 0"
  shows "current \<Gamma> f"
proof
  fix x
  assume "x \<notin> A \<Gamma>" "x \<notin> B \<Gamma>"
  hence "d_OUT f x = 0" by(auto simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 intro!: outside dest: bipartite_E)
  then show "d_OUT f x \<le> d_IN f x" by simp
qed(rule OUT IN outside)+

lemma wave_bipartiteI [intro?]:
  assumes sep: "separating \<Gamma> (TER f)"
  and f: "current \<Gamma> f"
  shows "wave \<Gamma> f"
using sep
proof(rule wave.intros)
  fix x
  assume "x \<notin> RF (TER f)"
  then consider "x \<notin> \<^bold>V" | "x \<in> \<^bold>V" "x \<in> B \<Gamma>" using separating_RF_A[OF sep] bipartite_V by auto
  then show "d_OUT f x = 0" using currentD_OUT[OF f, of x] currentD_outside_OUT[OF f, of x]
    by cases auto
qed

subsection \<open>Hindered webs with reduced weights\<close>

context
  fixes u :: "'v \<Rightarrow> ennreal"
  and \<epsilon>
  defines "\<epsilon> \<equiv> (\<integral>\<^sup>+ y. u y \<partial>count_space (B \<Gamma>))"
  assumes u_outside: "\<And>x. x \<notin> B \<Gamma> \<Longrightarrow> u x = 0"
  and finite_\<epsilon>: "\<epsilon> \<noteq> \<top>"
begin

private lemma u_A: "x \<in> A \<Gamma> \<Longrightarrow> u x = 0"
using u_outside[of x] disjoint by auto

private lemma u_finite: "u y \<noteq> \<top>"
proof(cases "y \<in> B \<Gamma>")
  case True
  have "u y \<le> \<epsilon>" unfolding \<epsilon>_def by(rule nn_integral_ge_point)(simp add: True)
  also have "\<dots> < \<top>" using finite_\<epsilon> by (simp add: less_top[symmetric])
  finally show ?thesis by simp
qed(simp add: u_outside)

lemma hindered_reduce: \<comment> \<open>Lemma 6.7\<close>
  assumes u: "u \<le> weight \<Gamma>"
  assumes hindered_by: "hindered_by (\<Gamma>\<lparr>weight := weight \<Gamma> - u\<rparr>) \<epsilon>" (is "hindered_by ?\<Gamma> _")
  shows "hindered \<Gamma>"
proof -
  note [simp] = u_finite
  let ?TER = "TER\<^bsub>?\<Gamma>\<^esub>"
  from hindered_by obtain f
    where hindrance_by: "hindrance_by ?\<Gamma> f \<epsilon>"
    and f: "current ?\<Gamma> f"
    and w: "wave ?\<Gamma> f" by cases
  from hindrance_by obtain a where a: "a \<in> A \<Gamma>" "a \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (?TER f)"
    and a_le: "d_OUT f a < weight \<Gamma> a"
    and \<epsilon>_less: "weight \<Gamma> a - d_OUT f a > \<epsilon>"
    and \<epsilon>_nonneg: "\<epsilon> \<ge> 0" by(auto simp add: u_A hindrance_by.simps)

  from f have f': "current \<Gamma> f" by(rule current_weight_mono)(auto intro: diff_le_self_ennreal)

  write Some ("\<langle>_\<rangle>")

  define edge'
    where "edge' xo yo =
      (case (xo, yo) of
        (None, Some y) \<Rightarrow> y \<in> \<^bold>V \<and> y \<notin> A \<Gamma>
      | (Some x, Some y) \<Rightarrow> edge \<Gamma> x y \<or> edge \<Gamma> y x
      | _ \<Rightarrow> False)" for xo yo
  define cap
    where "cap e =
      (case e of
        (None, Some y) \<Rightarrow> if y \<in> \<^bold>V then u y else 0
      | (Some x, Some y) \<Rightarrow> if edge \<Gamma> x y \<and> x \<noteq> a then f (x, y) else if edge \<Gamma> y x then max (weight \<Gamma> x) (weight \<Gamma> y) + 1 else 0
      | _ \<Rightarrow> 0)" for e
  define \<Psi> where "\<Psi> = \<lparr>edge = edge', capacity = cap, source = None, sink = Some a\<rparr>"

  have edge'_simps [simp]:
    "edge' None \<langle>y\<rangle> \<longleftrightarrow> y \<in> \<^bold>V \<and> y \<notin> A \<Gamma>"
    "edge' xo None \<longleftrightarrow> False"
    "edge' \<langle>x\<rangle> \<langle>y\<rangle> \<longleftrightarrow> edge \<Gamma> x y \<or> edge \<Gamma> y x"
    for xo x y by(simp_all add: edge'_def split: option.split)

  have edge_None1E [elim!]: thesis if "edge' None y" "\<And>z. \<lbrakk> y = \<langle>z\<rangle>; z \<in> \<^bold>V; z \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis" for y thesis
    using that by(simp add: edge'_def split: option.split_asm sum.split_asm)
  have edge_Some1E [elim!]: thesis if "edge' \<langle>x\<rangle> y" "\<And>z. \<lbrakk> y = \<langle>z\<rangle>; edge \<Gamma> x z \<or> edge \<Gamma> z x \<rbrakk> \<Longrightarrow> thesis" for x y thesis
    using that by(simp add: edge'_def split: option.split_asm sum.split_asm)
  have edge_Some2E [elim!]: thesis if "edge' x \<langle>y\<rangle>" "\<lbrakk> x = None; y \<in> \<^bold>V; y \<notin> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis" "\<And>z. \<lbrakk> x = \<langle>z\<rangle>; edge \<Gamma> z y \<or> edge \<Gamma> y z \<rbrakk> \<Longrightarrow> thesis" for x y thesis
    using that by(simp add: edge'_def split: option.split_asm sum.split_asm)

  have cap_simps [simp]:
    "cap (None, \<langle>y\<rangle>) = (if y \<in> \<^bold>V then u y else 0)"
    "cap (xo, None) = 0"
    "cap (\<langle>x\<rangle>, \<langle>y\<rangle>) =
    (if edge \<Gamma> x y \<and> x \<noteq> a then f (x, y) else if edge \<Gamma> y x then max (weight \<Gamma> x) (weight \<Gamma> y) + 1 else 0)"
    for xo x y by(simp_all add: cap_def split: option.split)

  have \<Psi>_sel [simp]:
    "edge \<Psi> = edge'"
    "capacity \<Psi> = cap"
    "source \<Psi> = None"
    "sink \<Psi> = \<langle>a\<rangle>"
    by(simp_all add: \<Psi>_def)

  have cap_outside1: "\<not> vertex \<Gamma> x \<Longrightarrow> cap (\<langle>x\<rangle>, y) = 0" for x y
    by(cases y)(auto simp add: vertex_def)
  have capacity_A_weight: "d_OUT cap \<langle>x\<rangle> \<le> weight \<Gamma> x" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_OUT cap \<langle>x\<rangle> \<le> (\<Sum>\<^sup>+ y\<in>range Some. f (x, the y))"
      using that disjoint a(1) unfolding d_OUT_def
      by(auto 4 4 intro!: nn_integral_mono simp add: nn_integral_count_space_indicator notin_range_Some currentD_outside[OF f] split: split_indicator dest: edge_antiparallel bipartite_E)
    also have "\<dots> = d_OUT f x" by(simp add: d_OUT_def nn_integral_count_space_reindex)
    also have "\<dots> \<le> weight \<Gamma> x" using f' by(rule currentD_weight_OUT)
    finally show ?thesis .
  qed
  have flow_attainability: "flow_attainability \<Psi>"
  proof
    have "\<^bold>E\<^bsub>\<Psi>\<^esub> = (\<lambda>(x, y). (\<langle>x\<rangle>, \<langle>y\<rangle>)) ` \<^bold>E \<union> (\<lambda>(x, y). (\<langle>y\<rangle>, \<langle>x\<rangle>)) ` \<^bold>E \<union> (\<lambda>x. (None, \<langle>x\<rangle>)) ` (\<^bold>V \<inter> - A \<Gamma>)"
      by(auto simp add: edge'_def split: option.split_asm)
    thus "countable \<^bold>E\<^bsub>\<Psi>\<^esub>" by simp
  next
    fix v
    assume "v \<noteq> sink \<Psi>"
    consider (sink) "v = None" | (A) x where "v = \<langle>x\<rangle>" "x \<in> A \<Gamma>"
      | (B) y where "v = \<langle>y\<rangle>" "y \<notin> A \<Gamma>" "y \<in> \<^bold>V" | (outside) x where "v = \<langle>x\<rangle>" "x \<notin> \<^bold>V"
      by(cases v) auto
    then show "d_IN (capacity \<Psi>) v \<noteq> \<top> \<or> d_OUT (capacity \<Psi>) v \<noteq> \<top>"
    proof cases
      case sink thus ?thesis by(simp add: d_IN_def)
    next
      case (A x)
      thus ?thesis using capacity_A_weight[of x] by (auto simp: top_unique)
    next
      case (B y)
      have "d_IN (capacity \<Psi>) v \<le> (\<Sum>\<^sup>+ x. f (the x, y) * indicator (range Some) x + u y * indicator {None} x)"
        using B disjoint bipartite_V a(1) unfolding d_IN_def
        by(auto 4 4 intro!: nn_integral_mono simp add: nn_integral_count_space_indicator notin_range_Some currentD_outside[OF f] split: split_indicator dest: edge_antiparallel bipartite_E)
      also have "\<dots> = (\<Sum>\<^sup>+ x\<in>range Some. f (the x, y)) + u y"
        by(subst nn_integral_add)(simp_all add: nn_integral_count_space_indicator)
      also have "\<dots> = d_IN f y + u y" by(simp add: d_IN_def nn_integral_count_space_reindex)
      also have "d_IN f y \<le> weight \<Gamma> y" using f' by(rule currentD_weight_IN)
      finally show ?thesis by(auto simp add: add_right_mono top_unique split: if_split_asm)
    next
      case outside
      hence "d_OUT (capacity \<Psi>) v = 0"
        by(auto simp add: d_OUT_def nn_integral_0_iff_AE AE_count_space cap_def vertex_def split: option.split)
      thus ?thesis by simp
    qed
  next
    show "capacity \<Psi> e \<noteq> \<top>" for e using weight_finite
      by(auto simp add: cap_def max_def vertex_def currentD_finite[OF f'] split: option.split prod.split simp del: weight_finite)
    show "capacity \<Psi> e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Psi>\<^esub>" for e
      using that bipartite_V disjoint
      by(auto simp add: cap_def max_def intro: u_outside split: option.split prod.split)
    show "\<not> edge \<Psi> x (source \<Psi>)" for x  by simp
    show "\<not> edge \<Psi> x x" for x by(cases x)(simp_all add: no_loop)
    show "source \<Psi> \<noteq> sink \<Psi>" by simp
  qed
  then interpret \<Psi>: flow_attainability "\<Psi>" .

  define \<alpha> where "\<alpha> = (\<Squnion>g\<in>{g. flow \<Psi> g}. value_flow \<Psi> g)"
  have \<alpha>_le: "\<alpha> \<le> \<epsilon>"
  proof -
    have "\<alpha> \<le> d_OUT cap None" unfolding \<alpha>_def by(rule SUP_least)(auto intro!: d_OUT_mono dest: flowD_capacity)
    also have "\<dots> \<le> \<integral>\<^sup>+ y. cap (None, y) \<partial>count_space (range Some)" unfolding d_OUT_def
      by(auto simp add: nn_integral_count_space_indicator notin_range_Some intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> \<le> \<epsilon>" unfolding \<epsilon>_def
      by (subst (2) nn_integral_count_space_indicator, auto simp add: nn_integral_count_space_reindex u_outside intro!: nn_integral_mono split: split_indicator)
    finally show ?thesis by simp
  qed
  then have finite_flow: "\<alpha> \<noteq> \<top>" using finite_\<epsilon> by (auto simp: top_unique)

  from \<Psi>.ex_max_flow
  obtain j where j: "flow \<Psi> j"
    and value_j: "value_flow \<Psi> j = \<alpha>"
    and IN_j: "\<And>x. d_IN j x \<le> \<alpha>"
    unfolding \<alpha>_def by auto

  have j_le_f: "j (Some x, Some y) \<le> f (x, y)" if "edge \<Gamma> x y" for x y
    using that flowD_capacity[OF j, of "(Some x, Some y)"] a(1) disjoint
    by(auto split: if_split_asm dest: bipartite_E intro: order_trans)

  have IN_j_finite [simp]: "d_IN j x \<noteq> \<top>" for x using finite_flow by(rule neq_top_trans)(simp add: IN_j)

  have j_finite[simp]: "j (x, y) < \<top>" for x y
    by (rule le_less_trans[OF d_IN_ge_point]) (simp add: IN_j_finite[of y] less_top[symmetric])

  have OUT_j_finite: "d_OUT j x \<noteq> \<top>" for x
  proof(cases "x = source \<Psi> \<or> x = sink \<Psi>")
    case True thus ?thesis
    proof cases
      case left thus ?thesis using finite_flow value_j by simp
    next
      case right
      have "d_OUT (capacity \<Psi>) \<langle>a\<rangle> \<noteq> \<top>" using capacity_A_weight[of a] a(1) by(auto simp: top_unique)
      thus ?thesis unfolding right[simplified]
        by(rule neq_top_trans)(rule d_OUT_mono flowD_capacity[OF j])+
    qed
  next
    case False then show ?thesis by(simp add: flowD_KIR[OF j])
  qed

  have IN_j_le_weight: "d_IN j \<langle>x\<rangle> \<le> weight \<Gamma> x" for x
  proof(cases "x \<in> A \<Gamma>")
    case xA: True
    show ?thesis
    proof(cases "x = a")
      case True
      have "d_IN j \<langle>x\<rangle> \<le> \<alpha>" by(rule IN_j)
      also have "\<dots> \<le> \<epsilon>" by(rule \<alpha>_le)
      also have "\<epsilon> < weight \<Gamma> a" using \<epsilon>_less diff_le_self_ennreal less_le_trans by blast
      finally show ?thesis using True by(auto intro: order.strict_implies_order)
    next
      case False
      have "d_IN j \<langle>x\<rangle> = d_OUT j \<langle>x\<rangle>" using flowD_KIR[OF j, of "Some x"] False by simp
      also have "\<dots> \<le> d_OUT cap \<langle>x\<rangle>" using flowD_capacity[OF j] by(auto intro: d_OUT_mono)
      also have "\<dots> \<le> weight \<Gamma> x" using xA  by(rule capacity_A_weight)
      finally show ?thesis .
    qed
  next
    case xA: False
    show ?thesis
    proof(cases "x \<in> B \<Gamma>")
      case True
      have "d_IN j \<langle>x\<rangle> \<le> d_IN cap \<langle>x\<rangle>" using flowD_capacity[OF j] by(auto intro: d_IN_mono)
      also have "\<dots> \<le> (\<Sum>\<^sup>+ z. f (the z, x) * indicator (range Some) z) + (\<Sum>\<^sup>+ z :: 'v option. u x * indicator {None} z)"
        using True disjoint
        by(subst nn_integral_add[symmetric])(auto simp add: vertex_def currentD_outside[OF f] d_IN_def B_out intro!: nn_integral_mono split: split_indicator)
      also have "\<dots> = d_IN f x + u x"
        by(simp add: nn_integral_count_space_indicator[symmetric] nn_integral_count_space_reindex d_IN_def)
      also have "\<dots> \<le> weight \<Gamma> x" using currentD_weight_IN[OF f, of x] u_finite[of x]
        using \<epsilon>_less u by (auto simp add: ennreal_le_minus_iff le_fun_def)
      finally show ?thesis .
    next
      case False
      with xA have "x \<notin> \<^bold>V" using bipartite_V by blast
      then have "d_IN j \<langle>x\<rangle> = 0" using False
        by(auto simp add: d_IN_def nn_integral_0_iff emeasure_count_space_eq_0 vertex_def edge'_def split: option.split_asm intro!: \<Psi>.flowD_outside[OF j])
      then show ?thesis
        by simp
    qed
  qed

  let ?j = "j \<circ> map_prod Some Some \<circ> prod.swap"

  have finite_j_OUT: "(\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. j (\<langle>x\<rangle>, \<langle>y\<rangle>)) \<noteq> \<top>" (is "?j_OUT \<noteq> _") if "x \<in> A \<Gamma>" for x
    using currentD_finite_OUT[OF f', of x]
    by(rule neq_top_trans)(auto intro!: nn_integral_mono j_le_f simp add: d_OUT_def nn_integral_count_space_indicator outgoing_def split: split_indicator)
  have j_OUT_eq: "?j_OUT x = d_OUT j \<langle>x\<rangle>" if "x \<in> A \<Gamma>" for x
  proof -
    have "?j_OUT x = (\<Sum>\<^sup>+ y\<in>range Some. j (Some x, y))" using that disjoint
      by(simp add: nn_integral_count_space_reindex)(auto 4 4 simp add: nn_integral_count_space_indicator outgoing_def intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] dest: bipartite_E split: split_indicator)
    also have "\<dots> = d_OUT j \<langle>x\<rangle>"
      by(auto simp add: d_OUT_def nn_integral_count_space_indicator notin_range_Some intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] split: split_indicator)
    finally show ?thesis .
  qed

  define g where "g = f \<oplus> ?j"
  have g_simps: "g (x, y) = (f \<oplus> ?j) (x, y)" for x y by(simp add: g_def)

  have OUT_g_A: "d_OUT g x = d_OUT f x + d_IN j \<langle>x\<rangle> - d_OUT j \<langle>x\<rangle>" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_OUT g x = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. f (x, y) + j (\<langle>y\<rangle>, \<langle>x\<rangle>) - j (\<langle>x\<rangle>, \<langle>y\<rangle>))"
      by(auto simp add: d_OUT_def g_simps currentD_outside[OF f'] outgoing_def nn_integral_count_space_indicator intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. f (x, y) + j (\<langle>y\<rangle>, \<langle>x\<rangle>)) - (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. j (\<langle>x\<rangle>, \<langle>y\<rangle>))"
      (is "_ = _ - ?j_OUT") using finite_j_OUT[OF that]
      by(subst nn_integral_diff)(auto simp add: AE_count_space outgoing_def intro!: order_trans[OF j_le_f])
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. f (x, y)) + (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. j (Some y, Some x)) - ?j_OUT"
      (is "_ = ?f + ?j_IN - _") by(subst nn_integral_add) simp_all
    also have "?f = d_OUT f x" by(subst d_OUT_alt_def[where G=\<Gamma>])(simp_all add: currentD_outside[OF f])
    also have "?j_OUT = d_OUT j \<langle>x\<rangle>" using that by(rule j_OUT_eq)
    also have "?j_IN = (\<Sum>\<^sup>+ y\<in>range Some. j (y, \<langle>x\<rangle>))" using that disjoint
      by(simp add: nn_integral_count_space_reindex)(auto 4 4 simp add: nn_integral_count_space_indicator outgoing_def intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] split: split_indicator dest: bipartite_E)
    also have "\<dots> = d_IN j (Some x)" using that disjoint
      by(auto 4 3 simp add: d_IN_def nn_integral_count_space_indicator notin_range_Some intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] split: split_indicator)
    finally show ?thesis by simp
  qed

  have OUT_g_B: "d_OUT g x = 0" if "x \<notin> A \<Gamma>" for x
    using disjoint that
    by(auto simp add: d_OUT_def nn_integral_0_iff_AE AE_count_space g_simps dest: bipartite_E)

  have OUT_g_a: "d_OUT g a < weight \<Gamma> a" using a(1)
  proof -
    have "d_OUT g a = d_OUT f a + d_IN j \<langle>a\<rangle> - d_OUT j \<langle>a\<rangle>" using a(1) by(rule OUT_g_A)
    also have "\<dots> \<le> d_OUT f a + d_IN j \<langle>a\<rangle>"
      by(rule diff_le_self_ennreal)
    also have "\<dots> < weight \<Gamma> a + d_IN j \<langle>a\<rangle> - \<epsilon>"
      using finite_\<epsilon> \<epsilon>_less currentD_finite_OUT[OF f']
      by (simp add: less_diff_eq_ennreal less_top ac_simps)
    also have "\<dots> \<le> weight \<Gamma> a"
      using IN_j[THEN order_trans, OF \<alpha>_le] by (simp add: ennreal_minus_le_iff)
    finally show ?thesis .
  qed

  have OUT_jj: "d_OUT ?j x = d_IN j \<langle>x\<rangle> - j (None, \<langle>x\<rangle>)" for x
  proof -
    have "d_OUT ?j x = (\<Sum>\<^sup>+ y\<in>range Some. j (y, \<langle>x\<rangle>))" by(simp add: d_OUT_def nn_integral_count_space_reindex)
    also have "\<dots> = d_IN j \<langle>x\<rangle> - (\<Sum>\<^sup>+ y. j (y, \<langle>x\<rangle>) * indicator {None} y)" unfolding d_IN_def
      by(subst nn_integral_diff[symmetric])(auto simp add: max_def \<Psi>.flowD_finite[OF j] AE_count_space nn_integral_count_space_indicator split: split_indicator intro!: nn_integral_cong)
    also have "\<dots> = d_IN j \<langle>x\<rangle> - j (None, \<langle>x\<rangle>)" by(simp add: max_def)
    finally show ?thesis .
  qed

  have OUT_jj_finite [simp]: "d_OUT ?j x \<noteq> \<top>" for x
    by(simp add: OUT_jj)

  have IN_g: "d_IN g x = d_IN f x + j (None, \<langle>x\<rangle>)" for x
  proof(cases "x \<in> B \<Gamma>")
    case True
    have finite: "(\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. j (Some y, Some x)) \<noteq> \<top>" using currentD_finite_IN[OF f', of x]
      by(rule neq_top_trans)(auto intro!: nn_integral_mono j_le_f simp add: d_IN_def nn_integral_count_space_indicator incoming_def split: split_indicator)

    have "d_IN g x = d_IN (f \<oplus> ?j) x" by(simp add: g_def)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. f (y, x) + j (Some x, Some y) - j (Some y, Some x))"
      by(auto simp add: d_IN_def currentD_outside[OF f'] incoming_def nn_integral_count_space_indicator intro!: nn_integral_cong)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. f (y, x) + j (Some x, Some y)) - (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. j (Some y, Some x))"
      (is "_ = _ - ?j_IN") using finite
      by(subst nn_integral_diff)(auto simp add: AE_count_space incoming_def intro!: order_trans[OF j_le_f])
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. f (y, x)) + (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. j (Some x, Some y)) - ?j_IN"
      (is "_ = ?f + ?j_OUT - _") by(subst nn_integral_add) simp_all
    also have "?f = d_IN f x" by(subst d_IN_alt_def[where G=\<Gamma>])(simp_all add: currentD_outside[OF f])
    also have "?j_OUT = (\<Sum>\<^sup>+ y\<in>range Some. j (Some x, y))" using True disjoint
      by(simp add: nn_integral_count_space_reindex)(auto 4 4 simp add: nn_integral_count_space_indicator incoming_def intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] split: split_indicator dest: bipartite_E)
    also have "\<dots> = d_OUT j (Some x)" using disjoint
      by(auto 4 3 simp add: d_OUT_def nn_integral_count_space_indicator notin_range_Some intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] split: split_indicator)
    also have "\<dots> = d_IN j (Some x)" using flowD_KIR[OF j, of "Some x"] True a disjoint by auto
    also have "?j_IN = (\<Sum>\<^sup>+ y\<in>range Some. j (y, Some x))" using True disjoint
      by(simp add: nn_integral_count_space_reindex)(auto 4 4 simp add: nn_integral_count_space_indicator incoming_def intro!: nn_integral_cong \<Psi>.flowD_outside[OF j] dest: bipartite_E split: split_indicator)
    also have "\<dots> = d_IN j (Some x) - (\<Sum>\<^sup>+ y :: 'v option. j (None, Some x) * indicator {None} y)"
      unfolding d_IN_def using flowD_capacity[OF j, of "(None, Some x)"]
      by(subst nn_integral_diff[symmetric])
        (auto simp add: nn_integral_count_space_indicator AE_count_space top_unique image_iff
              intro!: nn_integral_cong ennreal_diff_self split: split_indicator if_split_asm)
    also have "d_IN f x + d_IN j (Some x) - \<dots> = d_IN f x + j (None, Some x)"
      using ennreal_add_diff_cancel_right[OF IN_j_finite[of "Some x"], of "d_IN f x + j (None, Some x)"]
      apply(subst diff_diff_ennreal')
      apply(auto simp add: d_IN_def intro!: nn_integral_ge_point ennreal_diff_le_mono_left)
      apply(simp add: ac_simps)
      done
    finally show ?thesis .
  next
    case False
    hence "d_IN g x = 0" "d_IN f x = 0" "j (None, \<langle>x\<rangle>) = 0"
      using disjoint currentD_IN[OF f', of x] bipartite_V currentD_outside_IN[OF f'] u_outside[OF False] flowD_capacity[OF j, of "(None, \<langle>x\<rangle>)"]
      by(cases "vertex \<Gamma> x"; auto simp add: d_IN_def nn_integral_0_iff_AE AE_count_space g_simps dest: bipartite_E split: if_split_asm)+
    thus ?thesis by simp
  qed

  have g: "current \<Gamma> g"
  proof
    show "d_OUT g x \<le> weight \<Gamma> x" for x
    proof(cases "x \<in> A \<Gamma>")
      case False
      thus ?thesis by(simp add: OUT_g_B)
    next
      case True
      with OUT_g_a show ?thesis
        by(cases "x = a")(simp_all add: OUT_g_A flowD_KIR[OF j] currentD_weight_OUT[OF f'])
    qed

    show "d_IN g x \<le> weight \<Gamma> x" for x
    proof(cases "x \<in> B \<Gamma>")
      case False
      hence "d_IN g x = 0" using disjoint
        by(auto simp add: d_IN_def nn_integral_0_iff_AE AE_count_space g_simps dest: bipartite_E)
      thus ?thesis by simp
    next
      case True
      have "d_IN g x \<le> (weight \<Gamma> x - u x) + u x" unfolding IN_g
        using currentD_weight_IN[OF f, of x] flowD_capacity[OF j, of "(None, Some x)"] True bipartite_V
        by(intro add_mono)(simp_all split: if_split_asm)
      also have "\<dots> = weight \<Gamma> x"
        using u by (intro diff_add_cancel_ennreal) (simp add: le_fun_def)
      finally show ?thesis .
    qed
    show "g e = 0" if "e \<notin> \<^bold>E" for e using that
      by(cases e)(auto simp add: g_simps)
  qed

  define cap' where "cap' = (\<lambda>(x, y). if edge \<Gamma> x y then g (x, y) else if edge \<Gamma> y x then 1 else 0)"

  have cap'_simps [simp]: "cap' (x, y) = (if edge \<Gamma> x y then g (x, y) else if edge \<Gamma> y x then 1 else 0)"
    for x y by(simp add: cap'_def)

  define G where "G = \<lparr>edge = \<lambda>x y. cap' (x, y) > 0\<rparr>"
  have G_sel [simp]: "edge G x y \<longleftrightarrow> cap' (x, y) > 0" for x y by(simp add: G_def)
  define reachable where "reachable x = (edge G)\<^sup>*\<^sup>* x a" for x
  have reachable_alt_def: "reachable \<equiv> \<lambda>x. \<exists>p. path G x p a"
    by(simp add: reachable_def [abs_def] rtranclp_eq_rtrancl_path)

  have [simp]: "reachable a" by(auto simp add: reachable_def)

  have AB_edge: "edge G x y" if "edge \<Gamma> y x" for x y
    using that
    by(auto dest: edge_antiparallel simp add: min_def le_neq_trans add_eq_0_iff_both_eq_0)
  have reachable_AB: "reachable y" if "reachable x" "(x, y) \<in> \<^bold>E" for x y
    using that by(auto simp add: reachable_def simp del: G_sel dest!: AB_edge intro: rtrancl_path.step)
  have reachable_BA: "g (x, y) = 0" if "reachable y" "(x, y) \<in> \<^bold>E" "\<not> reachable x" for x y
  proof(rule ccontr)
    assume "g (x, y) \<noteq> 0"
    then have "g (x, y) > 0" by (simp add: zero_less_iff_neq_zero)
    hence "edge G x y" using that by simp
    then have "reachable x" using \<open>reachable y\<close>
      unfolding reachable_def by(rule converse_rtranclp_into_rtranclp)
    with \<open>\<not> reachable x\<close> show False by contradiction
  qed
  have reachable_V: "vertex \<Gamma> x" if "reachable x" for x
  proof -
    from that obtain p where p: "path G x p a" unfolding reachable_alt_def ..
    then show ?thesis using rtrancl_path_nth[OF p, of 0] a(1) A_vertex
      by(cases "p = []")(auto 4 3 simp add: vertex_def elim: rtrancl_path.cases split: if_split_asm)
  qed

  have finite_j_IN: "(\<integral>\<^sup>+ y. j (Some y, Some x) \<partial>count_space (\<^bold>I\<^bold>N x)) \<noteq> \<top>" for x
  proof -
    have "(\<integral>\<^sup>+ y. j (Some y, Some x) \<partial>count_space (\<^bold>I\<^bold>N x)) \<le> d_IN f x"
      by(auto intro!: nn_integral_mono j_le_f simp add: d_IN_def nn_integral_count_space_indicator incoming_def split: split_indicator)
    thus ?thesis using currentD_finite_IN[OF f', of x] by (auto simp: top_unique)
  qed
  have j_outside: "j (x, y) = 0" if "\<not> edge \<Psi> x y" for x y
    using that flowD_capacity[OF j, of "(x, y)"] \<Psi>.capacity_outside[of "(x, y)"]
    by(auto)

  define h where "h = (\<lambda>(x, y). if reachable x \<and> reachable y then g (x, y) else 0)"
  have h_simps [simp]: "h (x, y) = (if reachable x \<and> reachable y then g (x, y) else 0)" for x y
    by(simp add: h_def)
  have h_le_g: "h e \<le> g e" for e by(cases e) simp

  have OUT_h: "d_OUT h x = (if reachable x then d_OUT g x else 0)" for x
  proof -
    have "d_OUT h x = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. h (x, y))" using h_le_g currentD_outside[OF g]
      by(intro d_OUT_alt_def) auto
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>O\<^bold>U\<^bold>T x. if reachable x then g (x, y) else 0)"
      by(auto intro!: nn_integral_cong simp add: outgoing_def dest: reachable_AB)
    also have "\<dots> = (if reachable x then d_OUT g x else 0)"
      by(auto intro!: d_OUT_alt_def[symmetric] currentD_outside[OF g])
    finally show ?thesis .
  qed
  have IN_h: "d_IN h x = (if reachable x then d_IN g x else 0)" for x
  proof -
    have "d_IN h x = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. h (y, x))"
      using h_le_g currentD_outside[OF g] by(intro d_IN_alt_def) auto
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>\<^bold>I\<^bold>N x. if reachable x then g (y, x) else 0)"
      by(auto intro!: nn_integral_cong simp add: incoming_def dest: reachable_BA)
    also have "\<dots> = (if reachable x then d_IN g x else 0)"
      by(auto intro!: d_IN_alt_def[symmetric] currentD_outside[OF g])
    finally show ?thesis .
  qed

  have h: "current \<Gamma> h" using g h_le_g
  proof(rule current_leI)
    show "d_OUT h x \<le> d_IN h x" if "x \<notin> A \<Gamma>" for x
      by(simp add: OUT_h IN_h currentD_OUT_IN[OF g that])
  qed

  have reachable_full: "j (None, \<langle>y\<rangle>) = u y" if reach: "reachable y" for y
  proof(rule ccontr)
    assume "j (None, \<langle>y\<rangle>) \<noteq> u y"
    with flowD_capacity[OF j, of "(None, \<langle>y\<rangle>)"]
    have le: "j (None, \<langle>y\<rangle>) < u y" by(auto split: if_split_asm simp add: u_outside \<Psi>.flowD_outside[OF j] zero_less_iff_neq_zero)
    then obtain y: "y \<in> B \<Gamma>" and uy: "u y > 0" using u_outside[of y]
      by(cases "y \<in> B \<Gamma>"; cases "u y = 0") (auto simp add: zero_less_iff_neq_zero)

    from reach obtain q where q: "path G y q a" and distinct: "distinct (y # q)"
      unfolding reachable_alt_def by(auto elim: rtrancl_path_distinct)
    have q_Nil: "q \<noteq> []" using q a(1) disjoint y by(auto elim!: rtrancl_path.cases)

    let ?E = "zip (y # q) q"
    define E where "E = (None, Some y) # map (map_prod Some Some) ?E"
    define \<zeta> where "\<zeta> = Min (insert (u y - j (None, Some y)) (cap' ` set ?E))"
    let ?j' = "\<lambda>e. (if e \<in> set E then \<zeta> else 0) + j e"
    define j' where "j' = cleanup ?j'"

    have j_free: "0 < cap' e" if "e \<in> set ?E" for e using that unfolding E_def list.sel
    proof -
      from that obtain i where e: "e = ((y # q) ! i, q ! i)"
        and i: "i < length q" by(auto simp add: set_zip)
      have e': "edge G ((y # q) ! i) (q ! i)" using q i by(rule rtrancl_path_nth)
      thus ?thesis using e by(simp)
    qed
    have \<zeta>_pos: "0 < \<zeta>" unfolding \<zeta>_def using le
      by(auto intro: j_free diff_gr0_ennreal)
    have \<zeta>_le: "\<zeta> \<le> cap' e" if "e \<in> set ?E" for e using that unfolding \<zeta>_def by auto
    have finite_\<zeta> [simplified]: "\<zeta> < \<top>" unfolding \<zeta>_def
      by(intro Min_less_iff[THEN iffD2])(auto simp add: less_top[symmetric])

    have E_antiparallel: "(x', y') \<in> set ?E \<Longrightarrow> (y', x') \<notin> set ?E" for x' y'
      using distinct
      apply(auto simp add: in_set_zip nth_Cons in_set_conv_nth)
      apply(auto simp add: distinct_conv_nth split: nat.split_asm)
      by (metis Suc_lessD less_Suc_eq less_irrefl_nat)

    have OUT_j': "d_OUT ?j' x' = \<zeta> * card (set [(x'', y) \<leftarrow> E. x'' = x']) + d_OUT j x'" for x'
    proof -
      have "d_OUT ?j' x' = d_OUT (\<lambda>e. if e \<in> set E then \<zeta> else 0) x' + d_OUT j x'"
        using \<zeta>_pos by(intro d_OUT_add)
      also have "d_OUT (\<lambda>e. if e \<in> set E then \<zeta> else 0) x' = \<integral>\<^sup>+ y. \<zeta> * indicator (set E) (x', y) \<partial>count_space UNIV"
        unfolding d_OUT_def by(rule nn_integral_cong)(simp)
      also have "\<dots> = (\<integral>\<^sup>+ e. \<zeta> * indicator (set E) e \<partial>embed_measure (count_space UNIV) (Pair x'))"
        by(simp add: measurable_embed_measure1 nn_integral_embed_measure)
      also have "\<dots> = (\<integral>\<^sup>+ e. \<zeta> * indicator (set [(x'', y) \<leftarrow> E. x'' = x']) e \<partial>count_space UNIV)"
        by(auto simp add: embed_measure_count_space' nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = \<zeta> * card (set [(x'', y) \<leftarrow> E. x'' = x'])" using \<zeta>_pos by(simp add: nn_integral_cmult)
      finally show ?thesis .
    qed
    have IN_j': "d_IN ?j' x' = \<zeta> * card (set [(y, x'') \<leftarrow> E. x'' = x']) + d_IN j x'" for x'
    proof -
      have "d_IN ?j' x' = d_IN (\<lambda>e. if e \<in> set E then \<zeta> else 0) x' + d_IN j x'"
        using \<zeta>_pos by(intro d_IN_add)
      also have "d_IN (\<lambda>e. if e \<in> set E then \<zeta> else 0) x' = \<integral>\<^sup>+ y. \<zeta> * indicator (set E) (y, x') \<partial>count_space UNIV"
        unfolding d_IN_def by(rule nn_integral_cong)(simp)
      also have "\<dots> = (\<integral>\<^sup>+ e. \<zeta> * indicator (set E) e \<partial>embed_measure (count_space UNIV) (\<lambda>y. (y, x')))"
        by(simp add: measurable_embed_measure1 nn_integral_embed_measure)
      also have "\<dots> = (\<integral>\<^sup>+ e. \<zeta> * indicator (set [(y, x'') \<leftarrow> E. x'' = x']) e \<partial>count_space UNIV)"
        by(auto simp add: embed_measure_count_space' nn_integral_count_space_indicator intro!: nn_integral_cong split: split_indicator)
      also have "\<dots> = \<zeta> * card (set [(y, x'') \<leftarrow> E. x'' = x'])"
        using \<zeta>_pos by(auto simp add: nn_integral_cmult)
      finally show ?thesis .
    qed

    have j': "flow \<Psi> j'"
    proof
      fix e :: "'v option edge"
      consider (None) "e = (None, Some y)"
        | (Some) x y where "e = (Some x, Some y)" "(x, y) \<in> set ?E"
        | (old) x y where "e = (Some x, Some y)" "(x, y) \<notin> set ?E"
        | y' where "e = (None, Some y')" "y \<noteq> y'"
        | "e = (None, None)" | x where "e = (Some x, None)"
        by(cases e; case_tac a; case_tac b)(auto)
      then show "j' e \<le> capacity \<Psi> e" using uy \<zeta>_pos flowD_capacity[OF j, of e]
      proof(cases)
        case None
        have "\<zeta> \<le> u y - j (None, Some y)" by(simp add: \<zeta>_def)
        then have "\<zeta> + j (None, Some y) \<le> u y"
          using \<zeta>_pos by (auto simp add: ennreal_le_minus_iff)
        thus ?thesis using reachable_V[OF reach] None \<Psi>.flowD_outside[OF j, of "(Some y, None)"] uy
          by(auto simp add: j'_def E_def)
      next
        case (Some x' y')
        have e: "\<zeta> \<le> cap' (x', y')" using Some(2) by(rule \<zeta>_le)
        then consider (backward) "edge \<Gamma> x' y'" "x' \<noteq> a" | (forward) "edge \<Gamma> y' x'" "\<not> edge \<Gamma> x' y'"
          | (a') "edge \<Gamma> x' y'" "x' = a"
          using Some \<zeta>_pos by(auto split: if_split_asm)
        then show ?thesis
        proof cases
          case backward
          have "\<zeta> \<le> f (x', y') + j (Some y', Some x') - j (Some x', Some y')"
            using e backward Some(1) by(simp add: g_simps)
          hence "\<zeta> + j (Some x', Some y') - j (Some y', Some x') \<le> (f (x', y') + j (Some y', Some x') - j (Some x', Some y')) + j (Some x', Some y') - j (Some y', Some x')"
            by(intro ennreal_minus_mono add_right_mono) simp_all
          also have "\<dots> = f (x', y')"
            using j_le_f[OF \<open>edge \<Gamma> x' y'\<close>]
            by(simp_all add: add_increasing2 less_top diff_add_assoc2_ennreal)
          finally show ?thesis using Some backward
            by(auto simp add: j'_def E_def dest: in_set_tlD E_antiparallel)
        next
          case forward
          have "\<zeta> + j (Some x', Some y') - j (Some y', Some x') \<le> \<zeta> + j (Some x', Some y')"
            by(rule diff_le_self_ennreal)
          also have "j (Some x', Some y') \<le> d_IN j (Some y')"
            by(rule d_IN_ge_point)
          also have "\<dots> \<le> weight \<Gamma> y'" by(rule IN_j_le_weight)
          also have "\<zeta> \<le> 1" using e forward by simp
          finally have "\<zeta> + j (Some x', Some y') - j (Some y', Some x') \<le> max (weight \<Gamma> x') (weight \<Gamma> y') + 1"
            by(simp add: add_left_mono add_right_mono max_def)(metis (no_types, lifting) add.commute add_right_mono less_imp_le less_le_trans not_le)
          then show ?thesis using Some forward e
            by(auto simp add: j'_def E_def max_def dest: in_set_tlD E_antiparallel)
        next
          case a'
          with Some have "a \<in> set (map fst (zip (y # q) q))" by(auto intro: rev_image_eqI)
          also have "map fst (zip (y # q) q) = butlast (y # q)" by(induction q arbitrary: y) auto
          finally have False using rtrancl_path_last[OF q q_Nil] distinct q_Nil
            by(cases q rule: rev_cases) auto
          then show ?thesis ..
        qed
      next
        case (old x' y')
        hence "j' e \<le> j e" using \<zeta>_pos
          by(auto simp add: j'_def E_def intro!: diff_le_self_ennreal)
        also have "j e \<le> capacity \<Psi> e" using j by(rule flowD_capacity)
        finally show ?thesis .
      qed(auto simp add: j'_def E_def \<Psi>.flowD_outside[OF j] uy)
    next
      fix x'
      assume x': "x' \<noteq> source \<Psi>" "x' \<noteq> sink \<Psi>"
      then obtain x'' where x'': "x' = Some x''" by auto
      have "d_OUT ?j' x' = \<zeta> * card (set [(x'', y) \<leftarrow> E. x'' = x']) + d_OUT j x'" by(rule OUT_j')
      also have "card (set [(x'', y) \<leftarrow> E. x'' = x']) = card (set [(y, x'') \<leftarrow> E. x'' = x'])" (is "?lhs = ?rhs")
      proof -
        have "?lhs = length [(x'', y) \<leftarrow> E. x'' = x']" using distinct
          by(subst distinct_card)(auto simp add: E_def filter_map distinct_map inj_map_prod' distinct_zipI1)
        also have "\<dots> = length [x''' \<leftarrow> map fst ?E. x''' = x'']"
          by(simp add: E_def x'' split_beta cong: filter_cong)
        also have "map fst ?E = butlast (y # q)" by(induction q arbitrary: y) simp_all
        also have "[x''' \<leftarrow> butlast (y # q). x''' = x''] = [x''' \<leftarrow> y # q. x''' = x'']"
          using q_Nil rtrancl_path_last[OF q q_Nil] x' x''
          by(cases q rule: rev_cases) simp_all
        also have "q = map snd ?E" by(induction q arbitrary: y) auto
        also have "length [x''' \<leftarrow> y # \<dots>. x''' = x''] = length [x'' \<leftarrow> map snd E. x'' = x']" using x''
          by(simp add: E_def cong: filter_cong)
        also have "\<dots> = length [(y, x'') \<leftarrow> E. x'' = x']" by(simp cong: filter_cong add: split_beta)
        also have "\<dots> = ?rhs" using distinct
          by(subst distinct_card)(auto simp add: E_def filter_map distinct_map inj_map_prod' distinct_zipI1)
        finally show ?thesis .
      qed
      also have "\<zeta> * \<dots> + d_OUT j x' =  d_IN ?j' x'"
        unfolding flowD_KIR[OF j x'] by(rule IN_j'[symmetric])
      also have "d_IN ?j' x' \<noteq> \<top>"
        using \<Psi>.flowD_finite_IN[OF j x'(2)] finite_\<zeta> IN_j'[of x'] by (auto simp: top_add ennreal_mult_eq_top_iff)
      ultimately show "KIR j' x'" unfolding j'_def by(rule KIR_cleanup)
    qed
    hence "value_flow \<Psi> j' \<le> \<alpha>" unfolding \<alpha>_def by(auto intro: SUP_upper)
    moreover have "value_flow \<Psi> j' > value_flow \<Psi> j"
    proof -
      have "value_flow \<Psi> j + 0 < value_flow \<Psi> j + \<zeta> * 1"
        using \<zeta>_pos value_j finite_flow by simp
      also have "[(x', y') \<leftarrow> E. x' = None] = [(None, Some y)]"
        using q_Nil by(cases q)(auto simp add: E_def filter_map cong: filter_cong split_beta)
      hence "\<zeta> * 1 \<le> \<zeta> * card (set [(x', y') \<leftarrow> E. x' = None])" using \<zeta>_pos
        by(intro mult_left_mono)(auto simp add: E_def real_of_nat_ge_one_iff neq_Nil_conv card_insert)
      also have "value_flow \<Psi> j + \<dots> = value_flow \<Psi> ?j'"
        using OUT_j' by(simp add: add.commute)
      also have "\<dots> = value_flow \<Psi> j'" unfolding j'_def
        by(subst value_flow_cleanup)(auto simp add: E_def \<Psi>.flowD_outside[OF j])
      finally show ?thesis by(simp add: add_left_mono)
    qed
    ultimately show False using finite_flow \<zeta>_pos value_j
      by(cases "value_flow \<Psi> j" \<zeta> rule: ennreal2_cases) simp_all
  qed

  have sep_h: "y \<in> TER h" if reach: "reachable y" and y: "y \<in> B \<Gamma>" and TER: "y \<in> ?TER f" for y
  proof(rule ccontr)
    assume y': "y \<notin> TER h"
    from y a(1) disjoint have yna: "y \<noteq> a" by auto

    from reach obtain p' where "path G y p' a" unfolding reachable_alt_def ..
    then obtain p' where p': "path G y p' a" and distinct: "distinct (y # p')" by(rule rtrancl_path_distinct)

    have SINK: "y \<in> SINK h" using y disjoint
      by(auto simp add: SINK.simps d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 intro: currentD_outside[OF g] dest: bipartite_E)
    have hg: "d_IN h y = d_IN g y" using reach by(simp add: IN_h)
    also have "\<dots> = d_IN f y + j (None, Some y)" by(simp add: IN_g)
    also have "d_IN f y = weight \<Gamma> y - u y" using currentD_weight_IN[OF f, of y] y disjoint TER
      by(auto elim!: SAT.cases)
    also have "d_IN h y < weight \<Gamma> y" using y' currentD_weight_IN[OF g, of y] y disjoint SINK
      by(auto intro: SAT.intros)
    ultimately have le: "j (None, Some y) < u y"
      by(cases "weight \<Gamma> y" "u y" "j (None, Some y)" rule: ennreal3_cases; cases "u y \<le> weight \<Gamma> y")
        (auto simp: ennreal_minus ennreal_plus[symmetric] add_top ennreal_less_iff ennreal_neg simp del: ennreal_plus)
    moreover from reach have "j (None, \<langle>y\<rangle>) = u y" by(rule reachable_full)
    ultimately show False by simp
  qed

  have w': "wave \<Gamma> h"
  proof
    show sep: "separating \<Gamma> (TER h)"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      then obtain x p y where x: "x \<in> A \<Gamma>" and y: "y \<in> B \<Gamma>" and p: "path \<Gamma> x p y"
        and x': "x \<notin> TER h" and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER h"
        by(auto simp add: separating_gen.simps)
      from p disjoint x y have p_eq: "p = [y]" and edge: "(x, y) \<in> \<^bold>E"
        by -(erule rtrancl_path.cases, auto dest: bipartite_E)+
      from p_eq bypass have y': "y \<notin> TER h" by simp
      have "reachable x" using x' by(rule contrapos_np)(simp add: SINK.simps d_OUT_def SAT.A x)
      hence reach: "reachable y" using edge by(rule reachable_AB)

      have *: "x \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (?TER f)" using x'
      proof(rule contrapos_nn)
        assume *: "x \<in> \<E>\<^bsub>?\<Gamma>\<^esub> (?TER f)"
        have "d_OUT h x \<le> d_OUT g x" using h_le_g by(rule d_OUT_mono)
        also from * have "x \<noteq> a" using a by auto
        then have "d_OUT j (Some x) = d_IN j (Some x)" by(auto intro: flowD_KIR[OF j])
        hence "d_OUT g x \<le> d_OUT f x" using OUT_g_A[OF x] IN_j[of "Some x"] finite_flow
          by(auto split: if_split_asm)
        also have "\<dots> = 0" using * by(auto elim: SINK.cases)
        finally have "x \<in> SINK h" by(simp add: SINK.simps)
        with x show "x \<in> TER h" by(simp add: SAT.A)
      qed
      from p p_eq x y have "path ?\<Gamma> x [y] y" "x \<in> A ?\<Gamma>" "y \<in> B ?\<Gamma>" by simp_all
      from * separatingD[OF separating_essential, OF waveD_separating, OF w this]
      have "y \<in> ?TER f" by auto
      with reach y have "y \<in> TER h" by(rule sep_h)
      with y' show False by contradiction
    qed
  qed(rule h)

  have OUT_g_a: "d_OUT g a = d_OUT h a" by(simp add: OUT_h)
  have "a \<notin> \<E> (TER h)"
  proof
    assume *: "a \<in> \<E> (TER h)"

    have "j (Some a, Some y) = 0" for y
      using flowD_capacity[OF j, of "(Some a, Some y)"] a(1) disjoint
      by(auto split: if_split_asm dest: bipartite_E)
    then have "d_OUT f a \<le> d_OUT g a" unfolding d_OUT_def
      \<comment> \<open>This step requires that @{term j} does not decrease the outflow of @{term a}. That's
          why we set the capacity of the outgoing edges from @{term "Some a"} in @{term \<Psi>} to @{term "0 :: ennreal"}\<close>
      by(intro nn_integral_mono)(auto simp add: g_simps currentD_outside[OF f] intro: )
    then have "a \<in> SINK f" using OUT_g_a * by(simp add: SINK.simps)
    with a(1) have "a \<in> ?TER f" by(auto intro: SAT.A)
    with a(2) have a': "\<not> essential \<Gamma> (B \<Gamma>) (?TER f) a" by simp

    from * obtain y where ay: "edge \<Gamma> a y" and y: "y \<in> B \<Gamma>" and y': "y \<notin> TER h" using disjoint a(1)
      by(auto 4 4 simp add: essential_def elim: rtrancl_path.cases dest: bipartite_E)
    from not_essentialD[OF a' rtrancl_path.step, OF ay rtrancl_path.base y]
    have TER: "y \<in> ?TER f" by simp

    have "reachable y" using \<open>reachable a\<close> by(rule reachable_AB)(simp add: ay)
    hence "y \<in> TER h" using y TER by(rule sep_h)
    with y' show False by contradiction
  qed
  with \<open>a \<in> A \<Gamma>\<close> have "hindrance \<Gamma> h"
  proof
    have "d_OUT h a = d_OUT g a" by(simp add: OUT_g_a)
    also have "\<dots> \<le> d_OUT f a + \<integral>\<^sup>+ y. j (Some y, Some a) \<partial>count_space UNIV"
      unfolding d_OUT_def d_IN_def
      by(subst nn_integral_add[symmetric])(auto simp add: g_simps intro!: nn_integral_mono diff_le_self_ennreal)
    also have "(\<integral>\<^sup>+ y. j (Some y, Some a) \<partial>count_space UNIV) = (\<integral>\<^sup>+ y. j (y, Some a) \<partial>embed_measure (count_space UNIV) Some)"
      by(simp add: nn_integral_embed_measure measurable_embed_measure1)
    also have "\<dots> \<le> d_IN j (Some a)" unfolding d_IN_def
      by(auto simp add: embed_measure_count_space nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> \<le> \<alpha>" by(rule IN_j)
    also have "\<dots> \<le> \<epsilon>" by(rule \<alpha>_le)
    also have "d_OUT f a + \<dots> < d_OUT f a + (weight \<Gamma> a - d_OUT f a)" using \<epsilon>_less
      using currentD_finite_OUT[OF f'] by (simp add: ennreal_add_left_cancel_less)
    also have "\<dots> = weight \<Gamma> a"
      using a_le by simp
    finally show "d_OUT h a < weight \<Gamma> a" by(simp add: add_left_mono)
  qed
  then show ?thesis using h w' by(blast intro: hindered.intros)
qed

end

corollary hindered_reduce_current: \<comment> \<open>Corollary 6.8\<close>
  fixes \<epsilon> g
  defines "\<epsilon> \<equiv> \<Sum>\<^sup>+ x\<in>B \<Gamma>. d_IN g x - d_OUT g x"
  assumes g: "current \<Gamma> g"
  and \<epsilon>_finite: "\<epsilon> \<noteq> \<top>"
  and hindered: "hindered_by (\<Gamma> \<ominus> g) \<epsilon>"
  shows "hindered \<Gamma>"
proof -
  define \<Gamma>' where "\<Gamma>' = \<Gamma>\<lparr>weight := \<lambda>x. if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT g x else weight \<Gamma> x\<rparr>"
  have \<Gamma>'_sel [simp]:
    "edge \<Gamma>' = edge \<Gamma>"
    "A \<Gamma>' = A \<Gamma>"
    "B \<Gamma>' = B \<Gamma>"
    "weight \<Gamma>' x = (if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT g x else weight \<Gamma> x)"
    "vertex \<Gamma>' = vertex \<Gamma>"
    "web.more \<Gamma>' = web.more \<Gamma>"
    for x by(simp_all add: \<Gamma>'_def)
  have "countable_bipartite_web \<Gamma>'"
    by unfold_locales(simp_all add: A_in B_out A_vertex disjoint bipartite_V no_loop weight_outside currentD_outside_OUT[OF g]  currentD_weight_OUT[OF g] edge_antiparallel, rule bipartite_E)
  then interpret \<Gamma>': countable_bipartite_web \<Gamma>' .
  let ?u = "\<lambda>x. (d_IN g x - d_OUT g x) * indicator (- A \<Gamma>) x"

  have "hindered \<Gamma>'"
  proof(rule \<Gamma>'.hindered_reduce)
    show "?u x = 0" if "x \<notin> B \<Gamma>'" for x using that bipartite_V
      by(cases "vertex \<Gamma>' x")(auto simp add: currentD_outside_OUT[OF g] currentD_outside_IN[OF g])

    have *: "(\<Sum>\<^sup>+ x\<in>B \<Gamma>'. ?u x) = \<epsilon>" using disjoint
      by(auto intro!: nn_integral_cong simp add: \<epsilon>_def nn_integral_count_space_indicator currentD_outside_OUT[OF g] currentD_outside_IN[OF g] not_vertex split: split_indicator)
    thus "(\<Sum>\<^sup>+ x\<in>B \<Gamma>'. ?u x) \<noteq> \<top>" using \<epsilon>_finite by simp

    have **: "\<Gamma>'\<lparr>weight := weight \<Gamma>' - ?u\<rparr> = \<Gamma> \<ominus> g"
      using currentD_weight_IN[OF g] currentD_OUT_IN[OF g] currentD_IN[OF g] currentD_finite_OUT[OF g]
      by(intro web.equality)(simp_all add: fun_eq_iff diff_diff_ennreal' ennreal_diff_le_mono_left)
    show "hindered_by (\<Gamma>'\<lparr>weight := weight \<Gamma>' - ?u\<rparr>) (\<Sum>\<^sup>+ x\<in>B \<Gamma>'. ?u x)"
      unfolding * ** by(fact hindered)
    show "(\<lambda>x. (d_IN g x - d_OUT g x) * indicator (- A \<Gamma>) x) \<le> weight \<Gamma>'"
      using currentD_weight_IN[OF g]
      by (simp add: le_fun_def ennreal_diff_le_mono_left)
  qed
  then show ?thesis
    by(rule hindered_mono_web[rotated -1]) simp_all
qed

end

subsection \<open>Reduced weight in a loose web\<close>

definition reduce_weight :: "('v, 'more) web_scheme \<Rightarrow> 'v \<Rightarrow> real \<Rightarrow> ('v, 'more) web_scheme"
where "reduce_weight \<Gamma> x r = \<Gamma>\<lparr>weight := \<lambda>y. weight \<Gamma> y - (if x = y then r else 0)\<rparr>"

lemma reduce_weight_sel [simp]:
  "edge (reduce_weight \<Gamma> x r) = edge \<Gamma>"
  "A (reduce_weight \<Gamma> x r) = A \<Gamma>"
  "B (reduce_weight \<Gamma> x r) = B \<Gamma>"
  "vertex (reduce_weight \<Gamma> x r) = vertex \<Gamma>"
  "weight (reduce_weight \<Gamma> x r) y = (if x = y then weight \<Gamma> x - r else weight \<Gamma> y)"
  "web.more (reduce_weight \<Gamma> x r) = web.more \<Gamma>"
by(simp_all add: reduce_weight_def zero_ennreal_def[symmetric] vertex_def fun_eq_iff)

lemma essential_reduce_weight [simp]: "essential (reduce_weight \<Gamma> x r) = essential \<Gamma>"
by(simp add: fun_eq_iff essential_def)

lemma roofed_reduce_weight [simp]: "roofed_gen (reduce_weight \<Gamma> x r) = roofed_gen \<Gamma>"
by(simp add: fun_eq_iff roofed_def)

context countable_bipartite_web begin

context begin
private datatype (plugins del: transfer size) 'a vertex = SOURCE | SINK | Inner (inner: 'a)

private lemma notin_range_Inner:  "x \<notin> range Inner \<longleftrightarrow> x = SOURCE \<or> x = SINK"
by(cases x) auto

private lemma inj_Inner [simp]: "\<And>A. inj_on Inner A"
by(simp add: inj_on_def)

lemma unhinder_bipartite:
  assumes h: "\<And>n :: nat. current \<Gamma> (h n)"
  and SAT: "\<And>n. (B \<Gamma> \<inter> \<^bold>V) - {b} \<subseteq> SAT \<Gamma> (h n)"
  and b: "b \<in> B \<Gamma>"
  and IN: "(SUP n. d_IN (h n) b) = weight \<Gamma> b"
  and h0_b: "\<And>n. d_IN (h 0) b \<le> d_IN (h n) b"
  and b_V: "b \<in> \<^bold>V"
  shows "\<exists>h'. current \<Gamma> h' \<and> wave \<Gamma> h' \<and> B \<Gamma> \<inter> \<^bold>V \<subseteq> SAT \<Gamma> h'"
proof -
  write Inner ("\<langle>_\<rangle>")
  define edge'
    where "edge' xo yo =
      (case (xo, yo) of
        (\<langle>x\<rangle>, \<langle>y\<rangle>) \<Rightarrow> edge \<Gamma> x y \<or> edge \<Gamma> y x
      | (\<langle>x\<rangle>, SINK) \<Rightarrow> x \<in> A \<Gamma>
      | (SOURCE, \<langle>y\<rangle>) \<Rightarrow> y = b
      | (SINK, \<langle>x\<rangle>) \<Rightarrow> x \<in> A \<Gamma>
      | _ \<Rightarrow> False)" for xo yo
  have edge'_simps [simp]:
    "edge' \<langle>x\<rangle> \<langle>y\<rangle> \<longleftrightarrow> edge \<Gamma> x y \<or> edge \<Gamma> y x"
    "edge' \<langle>x\<rangle> SINK \<longleftrightarrow> x \<in> A \<Gamma>"
    "edge' SOURCE yo \<longleftrightarrow> yo = \<langle>b\<rangle>"
    "edge' SINK \<langle>x\<rangle> \<longleftrightarrow> x \<in> A \<Gamma>"
    "edge' SINK SINK \<longleftrightarrow> False"
    "edge' xo SOURCE \<longleftrightarrow> False"
    for x y yo xo by(simp_all add: edge'_def split: vertex.split)
  have edge'E: "thesis" if "edge' xo yo"
    "\<And>x y. \<lbrakk> xo = \<langle>x\<rangle>; yo = \<langle>y\<rangle>; edge \<Gamma> x y \<or> edge \<Gamma> y x \<rbrakk> \<Longrightarrow> thesis"
    "\<And>x. \<lbrakk> xo = \<langle>x\<rangle>; yo = SINK; x \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    "\<And>x. \<lbrakk> xo = SOURCE; yo = \<langle>b\<rangle> \<rbrakk> \<Longrightarrow> thesis"
    "\<And>y. \<lbrakk> xo = SINK; yo = \<langle>y\<rangle>; y \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    for xo yo thesis using that by(auto simp add: edge'_def split: option.split_asm vertex.split_asm)
  have edge'_Inner1 [elim!]: "thesis" if "edge' \<langle>x\<rangle> yo"
    "\<And>y. \<lbrakk> yo = \<langle>y\<rangle>; edge \<Gamma> x y \<or> edge \<Gamma> y x \<rbrakk> \<Longrightarrow> thesis"
    "\<lbrakk> yo = SINK; x \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    for x yo thesis using that by(auto elim: edge'E)
  have edge'_Inner2 [elim!]: "thesis" if "edge' xo \<langle>y\<rangle>"
    "\<And>x. \<lbrakk> xo = \<langle>x\<rangle>; edge \<Gamma> x y \<or> edge \<Gamma> y x \<rbrakk> \<Longrightarrow> thesis"
    "\<lbrakk> xo = SOURCE; y = b \<rbrakk> \<Longrightarrow> thesis"
    "\<lbrakk> xo = SINK; y \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    for xo y thesis using that by(auto elim: edge'E)
  have edge'_SINK1 [elim!]: "thesis" if "edge' SINK yo"
    "\<And>y. \<lbrakk> yo = \<langle>y\<rangle>; y \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    for yo thesis using that by(auto elim: edge'E)
  have edge'_SINK2 [elim!]: "thesis" if "edge' xo SINK"
    "\<And>x. \<lbrakk> xo = \<langle>x\<rangle>; x \<in> A \<Gamma> \<rbrakk> \<Longrightarrow> thesis"
    for xo thesis using that by(auto elim: edge'E)

  define cap
    where "cap xoyo =
      (case xoyo of
        (\<langle>x\<rangle>, \<langle>y\<rangle>) \<Rightarrow> if edge \<Gamma> x y then h 0 (x, y) else if edge \<Gamma> y x then max (weight \<Gamma> x) (weight \<Gamma> y) else 0
      | (\<langle>x\<rangle>, SINK) \<Rightarrow> if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT (h 0) x else 0
      | (SOURCE, yo) \<Rightarrow> if yo = \<langle>b\<rangle> then weight \<Gamma> b - d_IN (h 0) b else 0
      | (SINK, \<langle>y\<rangle>) \<Rightarrow> if y \<in> A \<Gamma> then weight \<Gamma> y else 0
      | _ \<Rightarrow> 0)" for xoyo
  have cap_simps [simp]:
    "cap (\<langle>x\<rangle>, \<langle>y\<rangle>) = (if edge \<Gamma> x y then h 0 (x, y) else if edge \<Gamma> y x then max (weight \<Gamma> x) (weight \<Gamma> y) else 0)"
    "cap (\<langle>x\<rangle>, SINK) = (if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT (h 0) x else 0)"
    "cap (SOURCE, yo) = (if yo = \<langle>b\<rangle> then weight \<Gamma> b - d_IN (h 0) b else 0)"
    "cap (SINK, \<langle>y\<rangle>) = (if y \<in> A \<Gamma> then weight \<Gamma> y else 0)"
    "cap (SINK, SINK) = 0"
    "cap (xo, SOURCE) = 0"
    for x y yo xo by(simp_all add: cap_def split: vertex.split)
  define \<Psi> where "\<Psi> = \<lparr>edge = edge', capacity = cap, source = SOURCE, sink = SINK\<rparr>"
  have \<Psi>_sel [simp]:
    "edge \<Psi> = edge'"
    "capacity \<Psi> = cap"
    "source \<Psi> = SOURCE"
    "sink \<Psi> = SINK"
    by(simp_all add: \<Psi>_def)

  have cap_outside1: "\<not> vertex \<Gamma> x \<Longrightarrow> cap (\<langle>x\<rangle>, y) = 0" for x y using A_vertex
    by(cases y)(auto simp add: vertex_def)
  have capacity_A_weight: "d_OUT cap \<langle>x\<rangle> \<le> 2 * weight \<Gamma> x" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_OUT cap \<langle>x\<rangle> \<le> (\<Sum>\<^sup>+ y. h 0 (x, inner y) * indicator (range Inner) y + weight \<Gamma> x * indicator {SINK} y)"
      using that disjoint unfolding d_OUT_def
      by(auto intro!: nn_integral_mono diff_le_self_ennreal simp add: A_in notin_range_Inner  split: split_indicator)
    also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. h 0 (x, inner y)) + weight \<Gamma> x"
      by(auto simp add: nn_integral_count_space_indicator nn_integral_add)
    also have "(\<Sum>\<^sup>+ y\<in>range Inner. h 0 (x, inner y)) = d_OUT (h 0) x"
      by(simp add: d_OUT_def nn_integral_count_space_reindex)
    also have "\<dots> \<le> weight \<Gamma> x" using h by(rule currentD_weight_OUT)
    finally show ?thesis unfolding one_add_one[symmetric] distrib_right by(simp add: add_right_mono)
  qed
  have flow_attainability: "flow_attainability \<Psi>"
  proof
    have "\<^bold>E\<^bsub>\<Psi>\<^esub> \<subseteq> (\<lambda>(x, y). (\<langle>x\<rangle>, \<langle>y\<rangle>)) ` \<^bold>E \<union> (\<lambda>(x, y). (\<langle>y\<rangle>, \<langle>x\<rangle>)) ` \<^bold>E \<union> (\<lambda>x. (\<langle>x\<rangle>, SINK)) ` A \<Gamma> \<union> (\<lambda>x. (SINK, \<langle>x\<rangle>)) ` A \<Gamma> \<union> {(SOURCE, \<langle>b\<rangle>)}"
      by(auto simp add: edge'_def split: vertex.split_asm)
    moreover have "countable (A \<Gamma>)" using A_vertex by(rule countable_subset) simp
    ultimately show "countable \<^bold>E\<^bsub>\<Psi>\<^esub>" by(auto elim: countable_subset)
  next
    fix v
    assume "v \<noteq> sink \<Psi>"
    then consider (source) "v = SOURCE" | (A) x where "v = \<langle>x\<rangle>" "x \<in> A \<Gamma>"
      | (B) y where "v = \<langle>y\<rangle>" "y \<notin> A \<Gamma>" "y \<in> \<^bold>V" | (outside) x where "v = \<langle>x\<rangle>" "x \<notin> \<^bold>V"
      by(cases v) auto
    then show "d_IN (capacity \<Psi>) v \<noteq> \<top> \<or> d_OUT (capacity \<Psi>) v \<noteq> \<top>"
    proof cases
      case source thus ?thesis by(simp add: d_IN_def)
    next
      case (A x)
      thus ?thesis using capacity_A_weight[of x] by (auto simp: top_unique ennreal_mult_eq_top_iff)
    next
      case (B y)
      have "d_IN (capacity \<Psi>) v \<le> (\<Sum>\<^sup>+ x. h 0 (inner x, y) * indicator (range Inner) x + weight \<Gamma> b * indicator {SOURCE} x)"
        using B bipartite_V
        by(auto 4 4 intro!: nn_integral_mono simp add: diff_le_self_ennreal   d_IN_def notin_range_Inner nn_integral_count_space_indicator currentD_outside[OF h] split: split_indicator dest: bipartite_E)
      also have "\<dots> = (\<Sum>\<^sup>+ x\<in>range Inner. h 0 (inner x, y)) + weight \<Gamma> b"
        by(simp add: nn_integral_add nn_integral_count_space_indicator)
      also have "(\<Sum>\<^sup>+ x\<in>range Inner. h 0 (inner x, y)) = d_IN (h 0) y"
        by(simp add: d_IN_def nn_integral_count_space_reindex)
      also have "d_IN (h 0) y \<le> weight \<Gamma> y" using h by(rule currentD_weight_IN)
      finally show ?thesis by(auto simp add: top_unique add_right_mono split: if_split_asm)
    next
      case outside
      hence "d_OUT (capacity \<Psi>) v = 0" using A_vertex
        by(auto simp add: d_OUT_def nn_integral_0_iff_AE AE_count_space cap_def vertex_def split: vertex.split)
      thus ?thesis by simp
    qed
  next
    show "capacity \<Psi> e \<noteq> \<top>" for e
      by(auto simp add: cap_def max_def vertex_def currentD_finite[OF h] split: vertex.split prod.split)
    show "capacity \<Psi> e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Psi>\<^esub>" for e using that
      by(auto simp add: cap_def max_def split: prod.split; split vertex.split)+
    show "\<not> edge \<Psi> x (source \<Psi>)" for x using b by(auto simp add: B_out)
    show "\<not> edge \<Psi> x x" for x by(cases x)(simp_all add: no_loop)
    show "source \<Psi> \<noteq> sink \<Psi>" by simp
  qed
  then interpret \<Psi>: flow_attainability "\<Psi>" .
  define \<alpha> where "\<alpha> = (SUP f\<in>{f. flow \<Psi> f}. value_flow \<Psi> f)"

  define f
    where "f n xoyo =
    (case xoyo of
      (\<langle>x\<rangle>, \<langle>y\<rangle>) \<Rightarrow> if edge \<Gamma> x y then h 0 (x, y) - h n (x, y) else if edge \<Gamma> y x then h n (y, x) - h 0 (y, x) else 0
    | (SOURCE, \<langle>y\<rangle>) \<Rightarrow> if y = b then d_IN (h n) b - d_IN (h 0) b else 0
    | (\<langle>x\<rangle>, SINK) \<Rightarrow> if x \<in> A \<Gamma> then d_OUT (h n) x - d_OUT (h 0) x else 0
    | (SINK, \<langle>y\<rangle>) \<Rightarrow> if y \<in> A \<Gamma> then d_OUT (h 0) y - d_OUT (h n) y else 0
    | _ \<Rightarrow> 0)" for n xoyo
  have f_cases: thesis if "\<And>x y. e = (\<langle>x\<rangle>, \<langle>y\<rangle>) \<Longrightarrow> thesis" "\<And>y. e = (SOURCE, \<langle>y\<rangle>) \<Longrightarrow> thesis"
    "\<And>x. e = (\<langle>x\<rangle>, SINK) \<Longrightarrow> thesis" "\<And>y. e = (SINK, \<langle>y\<rangle>) \<Longrightarrow> thesis" "e = (SINK, SINK) \<Longrightarrow> thesis"
    "\<And>xo. e = (xo, SOURCE) \<Longrightarrow> thesis" "e = (SOURCE, SINK) \<Longrightarrow> thesis"
    for e :: "'v vertex edge" and thesis
    using that by(cases e; cases "fst e" "snd e" rule: vertex.exhaust[case_product vertex.exhaust]) simp_all
  have f_simps [simp]:
    "f n (\<langle>x\<rangle>, \<langle>y\<rangle>) = (if edge \<Gamma> x y then h 0 (x, y) - h n (x, y) else if edge \<Gamma> y x then h n (y, x) - h 0 (y, x) else 0)"
    "f n (SOURCE, \<langle>y\<rangle>) = (if y = b then d_IN (h n) b - d_IN (h 0) b else 0)"
    "f n (\<langle>x\<rangle>, SINK) = (if x \<in> A \<Gamma> then d_OUT (h n) x - d_OUT (h 0) x else 0)"
    "f n (SINK, \<langle>y\<rangle>) = (if y \<in> A \<Gamma> then d_OUT (h 0) y - d_OUT (h n) y else 0)"
    "f n (SOURCE, SINK) = 0"
    "f n (SINK, SINK) = 0"
    "f n (xo, SOURCE) = 0"
    for n x y xo by(simp_all add: f_def split: vertex.split)
  have OUT_f_SOURCE: "d_OUT (f n) SOURCE = d_IN (h n) b - d_IN (h 0) b" for n
  proof(rule trans)
    show "d_OUT (f n) SOURCE = (\<Sum>\<^sup>+ y. f n (SOURCE, y) * indicator {\<langle>b\<rangle>} y)" unfolding d_OUT_def
      apply(rule nn_integral_cong) subgoal for x by(cases x) auto done
    show "\<dots> = d_IN (h n) b - d_IN (h 0) b" using h0_b[of n]
      by(auto simp add: max_def)
  qed

  have OUT_f_outside: "d_OUT (f n) \<langle>x\<rangle> = 0" if "x \<notin> \<^bold>V" for x n using A_vertex that
    apply(clarsimp simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0)
    subgoal for y by(cases y)(auto simp add: vertex_def)
    done
  have IN_f_outside: "d_IN (f n) \<langle>x\<rangle> = 0" if "x \<notin> \<^bold>V" for x n using b_V that
    apply(clarsimp simp add: d_IN_def nn_integral_0_iff emeasure_count_space_eq_0)
    subgoal for y by(cases y)(auto simp add: currentD_outside_OUT[OF h] vertex_def)
    done

  have f: "flow \<Psi> (f n)" for n
  proof
    show f_le: "f n e \<le> capacity \<Psi> e" for e
      using currentD_weight_out[OF h] currentD_weight_IN[OF h] currentD_weight_OUT[OF h]
      by(cases e rule: f_cases)
        (auto dest: edge_antiparallel simp add: not_le le_max_iff_disj intro: ennreal_minus_mono ennreal_diff_le_mono_left)

    fix xo
    assume "xo \<noteq> source \<Psi>" "xo \<noteq> sink \<Psi>"
    then consider (A) x where "xo = \<langle>x\<rangle>" "x \<in> A \<Gamma>" | (B) x where "xo = \<langle>x\<rangle>" "x \<in> B \<Gamma>" "x \<in> \<^bold>V"
      | (outside) x where "xo = \<langle>x\<rangle>" "x \<notin> \<^bold>V" using bipartite_V by(cases xo) auto
    then show "KIR (f n) xo"
    proof cases
      case outside
      thus ?thesis by(simp add: OUT_f_outside IN_f_outside)
    next
      case A

      have finite1: "(\<Sum>\<^sup>+ y. h n (x, y) * indicator A y) \<noteq> \<top>" for A n
        using currentD_finite_OUT[OF h, of n x, unfolded d_OUT_def]
        by(rule neq_top_trans)(auto intro!: nn_integral_mono simp add: split: split_indicator)

      let ?h0_ge_hn = "{y. h 0 (x, y) \<ge> h n (x, y)}"
      let ?h0_lt_hn = "{y. h 0 (x, y) < h n (x, y)}"

      have "d_OUT (f n) \<langle>x\<rangle> = (\<Sum>\<^sup>+ y. f n (\<langle>x\<rangle>, y) * indicator (range Inner) y + f n (\<langle>x\<rangle>, y) * indicator {SINK} y)"
        unfolding d_OUT_def by(intro nn_integral_cong)(auto split: split_indicator simp add: notin_range_Inner)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. f n (\<langle>x\<rangle>, y)) + f n (\<langle>x\<rangle>, SINK)"
        by(simp add: nn_integral_add nn_integral_count_space_indicator max.left_commute max.commute)
      also have "(\<Sum>\<^sup>+ y\<in>range Inner. f n (\<langle>x\<rangle>, y)) = (\<Sum>\<^sup>+ y. h 0 (x, y) - h n (x, y))" using A
        apply(simp add: nn_integral_count_space_reindex cong: nn_integral_cong_simp outgoing_def)
        apply(auto simp add: nn_integral_count_space_indicator outgoing_def A_in max.absorb1 currentD_outside[OF h] intro!: nn_integral_cong split: split_indicator dest: edge_antiparallel)
        done
      also have "\<dots> = (\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_ge_hn y) - (\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_ge_hn y)"
        apply(subst nn_integral_diff[symmetric])
        apply(simp_all add: AE_count_space finite1 split: split_indicator)
        apply(rule nn_integral_cong; auto simp add: max_def not_le split: split_indicator)
        by (metis diff_eq_0_ennreal le_less not_le top_greatest)
      also have "(\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_ge_hn y) = d_OUT (h n) x - (\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_lt_hn y)"
        unfolding d_OUT_def
        apply(subst nn_integral_diff[symmetric])
        apply(auto simp add: AE_count_space finite1 currentD_finite[OF h] split: split_indicator intro!: nn_integral_cong)
        done
      also have "(\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_ge_hn y) - \<dots> + f n (\<langle>x\<rangle>, SINK) =
        (\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_ge_hn y) + (\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_lt_hn y) - min (d_OUT (h n) x) (d_OUT (h 0) x)"
        using finite1[of n "{_}"] A finite1[of n UNIV]
        apply (subst diff_diff_ennreal')
        apply (auto simp: d_OUT_def finite1 AE_count_space nn_integral_diff[symmetric] top_unique nn_integral_add[symmetric]
                    split: split_indicator intro!: nn_integral_mono ennreal_diff_self)
        apply (simp add: min_def not_le diff_eq_0_ennreal finite1 less_top[symmetric])
        apply (subst diff_add_assoc2_ennreal)
        apply (auto simp: add_diff_eq_ennreal intro!: nn_integral_mono split: split_indicator)
        apply (subst diff_diff_commute_ennreal)
        apply (simp add: ennreal_add_diff_cancel )
        done
      also have "\<dots> = (\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_lt_hn y) - (d_OUT (h 0) x - (\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_ge_hn y)) + f n (SINK, \<langle>x\<rangle>)"
        apply(rule sym)
        using finite1[of 0 "{_}"] A finite1[of 0 UNIV]
        apply (subst diff_diff_ennreal')
        apply (auto simp: d_OUT_def finite1 AE_count_space nn_integral_diff[symmetric] top_unique nn_integral_add[symmetric]
                    split: split_indicator intro!: nn_integral_mono ennreal_diff_self)
        apply (simp add: min_def not_le diff_eq_0_ennreal finite1 less_top[symmetric])
        apply (subst diff_add_assoc2_ennreal)
        apply (auto simp: add_diff_eq_ennreal intro!: nn_integral_mono split: split_indicator)
        apply (subst diff_diff_commute_ennreal)
        apply (simp_all add: ennreal_add_diff_cancel ac_simps)
        done
      also have "d_OUT (h 0) x - (\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_ge_hn y) = (\<Sum>\<^sup>+ y. h 0 (x, y) * indicator ?h0_lt_hn y)"
        unfolding d_OUT_def
        apply(subst nn_integral_diff[symmetric])
        apply(auto simp add: AE_count_space finite1 currentD_finite[OF h] split: split_indicator intro!: nn_integral_cong)
        done
      also have "(\<Sum>\<^sup>+ y. h n (x, y) * indicator ?h0_lt_hn y) - \<dots> = (\<Sum>\<^sup>+ y. h n (x, y) - h 0 (x, y))"
        apply(subst nn_integral_diff[symmetric])
        apply(simp_all add: AE_count_space finite1 order.strict_implies_order split: split_indicator)
        apply(rule nn_integral_cong; auto simp add: currentD_finite[OF h] top_unique less_top[symmetric] not_less split: split_indicator intro!: diff_eq_0_ennreal)
        done
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. f n (y, \<langle>x\<rangle>))" using A
        apply(simp add: nn_integral_count_space_reindex cong: nn_integral_cong_simp outgoing_def)
        apply(auto simp add: nn_integral_count_space_indicator outgoing_def A_in max.commute currentD_outside[OF h] intro!: nn_integral_cong split: split_indicator dest: edge_antiparallel)
        done
      also have "\<dots> + f n (SINK, \<langle>x\<rangle>) = (\<Sum>\<^sup>+ y. f n (y, \<langle>x\<rangle>) * indicator (range Inner) y + f n (y, \<langle>x\<rangle>) * indicator {SINK} y)"
        by(simp add: nn_integral_add nn_integral_count_space_indicator)
      also have "\<dots> = d_IN (f n) \<langle>x\<rangle>"
        using A b disjoint unfolding d_IN_def
        by(intro nn_integral_cong)(auto split: split_indicator simp add: notin_range_Inner)
      finally show ?thesis using A by simp
    next
      case (B x)

      have finite1: "(\<Sum>\<^sup>+ y. h n (y, x) * indicator A y) \<noteq> \<top>" for A n
        using currentD_finite_IN[OF h, of n x, unfolded d_IN_def]
        by(rule neq_top_trans)(auto intro!: nn_integral_mono split: split_indicator)

      have finite_h[simp]: "h n (y, x) < \<top>" for y n
        using finite1[of n "{y}"] by (simp add: less_top)

      let ?h0_gt_hn = "{y. h 0 (y, x) > h n (y, x)}"
      let ?h0_le_hn = "{y. h 0 (y, x) \<le> h n (y, x)}"

      have eq: "d_IN (h 0) x + f n (SOURCE, \<langle>x\<rangle>) = d_IN (h n) x"
      proof(cases "x = b")
        case True with currentD_finite_IN[OF h, of _ b] show ?thesis
          by(simp add: add_diff_self_ennreal h0_b)
      next
        case False
        with B SAT have "x \<in> SAT \<Gamma> (h n)" "x \<in> SAT \<Gamma> (h 0)" by auto
        with B disjoint have "d_IN (h n) x = d_IN (h 0) x" by(auto simp add: currentD_SAT[OF h])
        thus ?thesis using False by(simp add: currentD_finite_IN[OF h])
      qed

      have "d_IN (f n) \<langle>x\<rangle> = (\<Sum>\<^sup>+ y. f n (y, \<langle>x\<rangle>) * indicator (range Inner) y + f n (y, \<langle>x\<rangle>) * indicator {SOURCE} y)"
        using B disjoint unfolding d_IN_def
        by(intro nn_integral_cong)(auto split: split_indicator simp add: notin_range_Inner)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. f n (y, \<langle>x\<rangle>)) + f n (SOURCE, \<langle>x\<rangle>)" using h0_b[of n]
        by(simp add: nn_integral_add nn_integral_count_space_indicator max_def)
      also have "(\<Sum>\<^sup>+ y\<in>range Inner. f n (y, \<langle>x\<rangle>)) = (\<Sum>\<^sup>+ y. h 0 (y, x) - h n (y, x))"
        using B disjoint
        apply(simp add: nn_integral_count_space_reindex cong: nn_integral_cong_simp outgoing_def)
        apply(auto simp add: nn_integral_count_space_indicator outgoing_def B_out max.commute currentD_outside[OF h] intro!: nn_integral_cong split: split_indicator dest: edge_antiparallel)
        done
      also have "\<dots> = (\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_gt_hn y) - (\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_gt_hn y)"
        apply(subst nn_integral_diff[symmetric])
        apply(simp_all add: AE_count_space finite1 order.strict_implies_order split: split_indicator)
        apply(rule nn_integral_cong; auto simp add: currentD_finite[OF h] top_unique less_top[symmetric] not_less split: split_indicator intro!: diff_eq_0_ennreal)
        done
      also have eq_h_0: "(\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_gt_hn y) = d_IN (h 0) x - (\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_le_hn y)"
        unfolding d_IN_def
        apply(subst nn_integral_diff[symmetric])
        apply(auto simp add: AE_count_space finite1 currentD_finite[OF h] split: split_indicator intro!: nn_integral_cong)
        done
      also have eq_h_n: "(\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_gt_hn y) = d_IN (h n) x - (\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_le_hn y)"
        unfolding d_IN_def
        apply(subst nn_integral_diff[symmetric])
        apply(auto simp add: AE_count_space finite1 currentD_finite[OF h] split: split_indicator intro!: nn_integral_cong)
        done
      also have "d_IN (h 0) x - (\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_le_hn y) - (d_IN (h n) x - (\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_le_hn y)) + f n (SOURCE, \<langle>x\<rangle>) =
                (\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_le_hn y) - (\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_le_hn y)"
        apply (subst diff_add_assoc2_ennreal)
        subgoal by (auto simp add: eq_h_0[symmetric] eq_h_n[symmetric] split: split_indicator intro!: nn_integral_mono)
        apply (subst diff_add_assoc2_ennreal)
        subgoal by (auto simp: d_IN_def split: split_indicator intro!: nn_integral_mono)
        apply (subst diff_diff_commute_ennreal)
        apply (subst diff_diff_ennreal')
        subgoal
          by (auto simp: d_IN_def split: split_indicator intro!: nn_integral_mono) []
        subgoal
          unfolding eq_h_n[symmetric]
          by (rule add_increasing2)
             (auto simp add: d_IN_def split: split_indicator intro!: nn_integral_mono)
        apply (subst diff_add_assoc2_ennreal[symmetric])
        unfolding eq
        using currentD_finite_IN[OF h]
        apply simp_all
        done
      also have "(\<Sum>\<^sup>+ y. h n (y, x) * indicator ?h0_le_hn y) - (\<Sum>\<^sup>+ y. h 0 (y, x) * indicator ?h0_le_hn y) = (\<Sum>\<^sup>+ y. h n (y, x) - h 0 (y, x))"
        apply(subst nn_integral_diff[symmetric])
        apply(simp_all add: AE_count_space max_def finite1 split: split_indicator)
        apply(rule nn_integral_cong; auto simp add: not_le split: split_indicator)
        by (metis diff_eq_0_ennreal le_less not_le top_greatest)
      also have "\<dots> = (\<Sum>\<^sup>+ y\<in>range Inner. f n (\<langle>x\<rangle>, y))" using B disjoint
        apply(simp add: nn_integral_count_space_reindex cong: nn_integral_cong_simp outgoing_def)
        apply(auto simp add: B_out currentD_outside[OF h] max.commute intro!: nn_integral_cong split: split_indicator dest: edge_antiparallel)
        done
      also have "\<dots> = (\<Sum>\<^sup>+ y. f n (\<langle>x\<rangle>, y) * indicator (range Inner) y)"
        by(simp add: nn_integral_add nn_integral_count_space_indicator max.left_commute max.commute)
      also have "\<dots> = d_OUT (f n) \<langle>x\<rangle>"  using B disjoint
        unfolding d_OUT_def by(intro nn_integral_cong)(auto split: split_indicator simp add: notin_range_Inner)
      finally show ?thesis using B by(simp)
    qed
  qed

  have "weight \<Gamma> b - d_IN (h 0) b = (SUP n. value_flow \<Psi> (f n))"
    using OUT_f_SOURCE currentD_finite_IN[OF h, of 0 b] IN
    by (simp add: SUP_diff_ennreal less_top)
  also have "(SUP n. value_flow \<Psi> (f n)) \<le> \<alpha>" unfolding \<alpha>_def
    apply(rule SUP_least)
    apply(rule SUP_upper)
    apply(simp add: f)
    done
  also have "\<alpha> \<le> weight \<Gamma> b - d_IN (h 0) b" unfolding \<alpha>_def
  proof(rule SUP_least; clarsimp)
    fix f
    assume f: "flow \<Psi> f"
    have "d_OUT f SOURCE = (\<Sum>\<^sup>+ y. f (SOURCE, y) * indicator {\<langle>b\<rangle>} y)" unfolding d_OUT_def
      apply(rule nn_integral_cong)
      subgoal for x using flowD_capacity[OF f, of "(SOURCE, x)"]
        by(auto split: split_indicator)
      done
    also have "\<dots> = f (SOURCE, \<langle>b\<rangle>)" by(simp add: max_def)
    also have "\<dots> \<le> weight \<Gamma> b - d_IN (h 0) b" using flowD_capacity[OF f, of "(SOURCE, \<langle>b\<rangle>)"] by simp
    finally show "d_OUT f SOURCE \<le> \<dots>" .
  qed
  ultimately have \<alpha>: "\<alpha> = weight \<Gamma> b - d_IN (h 0) b" by(rule antisym[rotated])
  hence \<alpha>_finite: "\<alpha> \<noteq> \<top>" by simp

  from \<Psi>.ex_max_flow
  obtain g where g: "flow \<Psi> g"
    and value_g: "value_flow \<Psi> g = \<alpha>"
    and IN_g: "\<And>x. d_IN g x \<le> value_flow \<Psi> g" unfolding \<alpha>_def by blast

  have g_le_h0: "g (\<langle>x\<rangle>, \<langle>y\<rangle>) \<le> h 0 (x, y)" if "edge \<Gamma> x y" for x y
    using flowD_capacity[OF g, of "(\<langle>x\<rangle>, \<langle>y\<rangle>)"] that by simp
  note [simp] = \<Psi>.flowD_finite[OF g]

  have g_SOURCE: "g (SOURCE, \<langle>x\<rangle>) = (if x = b then \<alpha> else 0)" for x
  proof(cases "x = b")
    case True
    have "g (SOURCE, \<langle>x\<rangle>) = (\<Sum>\<^sup>+ y. g (SOURCE, y) * indicator {\<langle>x\<rangle>} y)" by(simp add: max_def)
    also have "\<dots> = value_flow \<Psi> g" unfolding d_OUT_def using True
      by(intro nn_integral_cong)(auto split: split_indicator intro: \<Psi>.flowD_outside[OF g])
    finally show ?thesis using value_g by(simp add: True)
  qed(simp add: \<Psi>.flowD_outside[OF g])

  let ?g = "\<lambda>(x, y). g (\<langle>y\<rangle>, \<langle>x\<rangle>)"

  define h' where "h' = h 0 \<oplus> ?g"
  have h'_simps: "h' (x, y) = (if edge \<Gamma> x y then h 0 (x, y) + g (\<langle>y\<rangle>, \<langle>x\<rangle>) - g (\<langle>x\<rangle>, \<langle>y\<rangle>) else 0)" for x y
    by(simp add: h'_def)

  have OUT_h'_B [simp]: "d_OUT h' x = 0" if "x \<in> B \<Gamma>" for x using that unfolding d_OUT_def
    by(simp add: nn_integral_0_iff emeasure_count_space_eq_0)(simp add: h'_simps B_out)
  have IN_h'_A [simp]: "d_IN h' x = 0" if "x \<in> A \<Gamma>" for x using that unfolding d_IN_def
    by(simp add: nn_integral_0_iff emeasure_count_space_eq_0)(simp add: h'_simps A_in)
  have h'_outside: "h' e = 0" if "e \<notin> \<^bold>E" for e unfolding h'_def using that by(rule plus_flow_outside)
  have OUT_h'_outside: "d_OUT h' x = 0" and IN_h'_outside: "d_IN h' x = 0" if "x \<notin> \<^bold>V" for x using that
    by(auto simp add: d_OUT_def d_IN_def nn_integral_0_iff emeasure_count_space_eq_0 vertex_def intro: h'_outside)

  have g_le_OUT: "g (SINK, \<langle>x\<rangle>) \<le> d_OUT g \<langle>x\<rangle>" for x
    by (subst flowD_KIR[OF g]) (simp_all add: d_IN_ge_point)

  have OUT_g_A: "d_OUT ?g x = d_OUT g \<langle>x\<rangle> - g (SINK, \<langle>x\<rangle>)" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_OUT ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (y, \<langle>x\<rangle>))"
      by(simp add: nn_integral_count_space_reindex d_OUT_def)
    also have "\<dots> = d_IN g \<langle>x\<rangle> - (\<Sum>\<^sup>+ y. g (y, \<langle>x\<rangle>) * indicator {SINK} y)" unfolding d_IN_def
      using that b disjoint flowD_capacity[OF g, of "(SOURCE, \<langle>x\<rangle>)"]
      by(subst nn_integral_diff[symmetric])
        (auto simp add: nn_integral_count_space_indicator notin_range_Inner max_def intro!: nn_integral_cong split: split_indicator if_split_asm)
    also have "\<dots> = d_OUT g \<langle>x\<rangle> - g (SINK, \<langle>x\<rangle>)" by(simp add: flowD_KIR[OF g] max_def)
    finally show ?thesis .
  qed
  have IN_g_A: "d_IN ?g x = d_OUT g \<langle>x\<rangle> - g (\<langle>x\<rangle>, SINK)" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_IN ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (\<langle>x\<rangle>, y))"
      by(simp add: nn_integral_count_space_reindex d_IN_def)
    also have "\<dots> = d_OUT g \<langle>x\<rangle> - (\<Sum>\<^sup>+ y. g (\<langle>x\<rangle>, y) * indicator {SINK} y)" unfolding d_OUT_def
      using that b disjoint flowD_capacity[OF g, of "(\<langle>x\<rangle>, SOURCE)"]
      by(subst nn_integral_diff[symmetric])
        (auto simp add: nn_integral_count_space_indicator notin_range_Inner max_def intro!: nn_integral_cong split: split_indicator if_split_asm)
    also have "\<dots> = d_OUT g \<langle>x\<rangle> - g (\<langle>x\<rangle>, SINK)" by(simp add: max_def)
    finally show ?thesis .
  qed
  have OUT_g_B: "d_OUT ?g x = d_IN g \<langle>x\<rangle> - g (SOURCE, \<langle>x\<rangle>)" if "x \<in> B \<Gamma>" for x
  proof -
    have "d_OUT ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (y, \<langle>x\<rangle>))"
      by(simp add: nn_integral_count_space_reindex d_OUT_def)
    also have "\<dots> = d_IN g \<langle>x\<rangle> - (\<Sum>\<^sup>+ y. g (y, \<langle>x\<rangle>) * indicator {SOURCE} y)" unfolding d_IN_def
      using that b disjoint flowD_capacity[OF g, of "(SINK, \<langle>x\<rangle>)"]
      by(subst nn_integral_diff[symmetric])
        (auto simp add: nn_integral_count_space_indicator notin_range_Inner max_def intro!: nn_integral_cong split: split_indicator if_split_asm)
    also have "\<dots> = d_IN g \<langle>x\<rangle> - g (SOURCE, \<langle>x\<rangle>)" by(simp add: max_def)
    finally show ?thesis .
  qed
  have IN_g_B: "d_IN ?g x = d_OUT g \<langle>x\<rangle>" if "x \<in> B \<Gamma>" for x
  proof -
    have "d_IN ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (\<langle>x\<rangle>, y))"
      by(simp add: nn_integral_count_space_reindex d_IN_def)
    also have "\<dots> = d_OUT g \<langle>x\<rangle>" unfolding d_OUT_def using that disjoint
      by(auto 4 3 simp add: nn_integral_count_space_indicator notin_range_Inner intro!: nn_integral_cong \<Psi>.flowD_outside[OF g] split: split_indicator)
    finally show ?thesis .
  qed

  have finite_g_IN: "d_IN ?g x \<noteq> \<top>" for x using \<alpha>_finite
  proof(rule neq_top_trans)
    have "d_IN ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (\<langle>x\<rangle>, y))"
      by(auto simp add: d_IN_def nn_integral_count_space_reindex)
    also have "\<dots> \<le> d_OUT g \<langle>x\<rangle>" unfolding d_OUT_def
      by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> = d_IN g \<langle>x\<rangle>" by(rule flowD_KIR[OF g]) simp_all
    also have "\<dots> \<le> \<alpha>" using IN_g value_g by simp
    finally show "d_IN ?g x \<le> \<alpha>" .
  qed

  have OUT_h'_A: "d_OUT h' x = d_OUT (h 0) x + g (\<langle>x\<rangle>, SINK) - g (SINK, \<langle>x\<rangle>)" if "x \<in> A \<Gamma>" for x
  proof -
    have "d_OUT h' x = d_OUT (h 0) x + (\<Sum>\<^sup>+ y. ?g (x, y) * indicator \<^bold>E (x, y)) - (\<Sum>\<^sup>+ y. ?g (y, x) * indicator \<^bold>E (x, y))"
      unfolding h'_def
      apply(subst OUT_plus_flow[of \<Gamma> "h 0" ?g, OF currentD_outside'[OF h]])
      apply(auto simp add: g_le_h0 finite_g_IN)
      done
    also have "(\<Sum>\<^sup>+ y. ?g (x, y) * indicator \<^bold>E (x, y)) = d_OUT ?g x" unfolding d_OUT_def using that
      by(auto simp add: A_in split: split_indicator intro!: nn_integral_cong \<Psi>.flowD_outside[OF g])
    also have "\<dots>  = d_OUT g \<langle>x\<rangle> - g (SINK, \<langle>x\<rangle>)" using that by(rule OUT_g_A)
    also have "(\<Sum>\<^sup>+ y. ?g (y, x) * indicator \<^bold>E (x, y)) = d_IN ?g x" using that unfolding d_IN_def
      by(auto simp add: A_in split: split_indicator intro!: nn_integral_cong \<Psi>.flowD_outside[OF g])
    also have "\<dots> = d_OUT g \<langle>x\<rangle> - g (\<langle>x\<rangle>, SINK)" using that by(rule IN_g_A)
    also have "d_OUT (h 0) x + (d_OUT g \<langle>x\<rangle> - g (SINK, \<langle>x\<rangle>)) - \<dots> = d_OUT (h 0) x + g (\<langle>x\<rangle>, SINK) - g (SINK, \<langle>x\<rangle>)"
      apply(simp add: g_le_OUT add_diff_eq_ennreal d_OUT_ge_point)
      apply(subst diff_diff_commute_ennreal)
      apply(simp add: add_increasing d_OUT_ge_point g_le_OUT diff_diff_ennreal')
      apply(subst add.assoc)
      apply(subst (2) add.commute)
      apply(subst add.assoc[symmetric])
      apply(subst ennreal_add_diff_cancel_right)
      apply(simp_all add: \<Psi>.flowD_finite_OUT[OF g])
      done
    finally show ?thesis .
  qed

  have finite_g_OUT: "d_OUT ?g x \<noteq> \<top>" for x using \<alpha>_finite
  proof(rule neq_top_trans)
    have "d_OUT ?g x = (\<Sum>\<^sup>+ y\<in>range Inner. g (y, \<langle>x\<rangle>))"
      by(auto simp add: d_OUT_def nn_integral_count_space_reindex)
    also have "\<dots> \<le> d_IN g \<langle>x\<rangle>" unfolding d_IN_def
      by(auto simp add: nn_integral_count_space_indicator intro!: nn_integral_mono split: split_indicator)
    also have "\<dots> \<le> \<alpha>" using IN_g value_g by simp
    finally show "d_OUT ?g x \<le> \<alpha>" .
  qed

  have IN_h'_B: "d_IN h' x = d_IN (h 0) x + g (SOURCE, \<langle>x\<rangle>)" if "x \<in> B \<Gamma>" for x
  proof -
    have g_le: "g (SOURCE, \<langle>x\<rangle>) \<le> d_IN g \<langle>x\<rangle>"
      by (rule d_IN_ge_point)

    have "d_IN h' x = d_IN (h 0) x + (\<Sum>\<^sup>+ y. g (\<langle>x\<rangle>, \<langle>y\<rangle>) * indicator \<^bold>E (y, x)) - (\<Sum>\<^sup>+ y. g (\<langle>y\<rangle>, \<langle>x\<rangle>) * indicator \<^bold>E (y, x))"
      unfolding h'_def
      by(subst IN_plus_flow[of \<Gamma> "h 0" ?g, OF currentD_outside'[OF h]])
        (auto simp add: g_le_h0 finite_g_OUT)
    also have "(\<Sum>\<^sup>+ y. g (\<langle>x\<rangle>, \<langle>y\<rangle>) * indicator \<^bold>E (y, x)) = d_IN ?g x" unfolding d_IN_def using that
      by(intro nn_integral_cong)(auto split: split_indicator intro!: \<Psi>.flowD_outside[OF g] simp add: B_out)
    also have "\<dots> = d_OUT g \<langle>x\<rangle>" using that by(rule IN_g_B)
    also have "(\<Sum>\<^sup>+ y. g (\<langle>y\<rangle>, \<langle>x\<rangle>) * indicator \<^bold>E (y, x)) = d_OUT ?g x" unfolding d_OUT_def using that
      by(intro nn_integral_cong)(auto split: split_indicator intro!: \<Psi>.flowD_outside[OF g] simp add: B_out)
    also have "\<dots> = d_IN g \<langle>x\<rangle> - g (SOURCE, \<langle>x\<rangle>)" using that by(rule OUT_g_B)
    also have "d_IN (h 0) x + d_OUT g \<langle>x\<rangle> - \<dots> = d_IN (h 0) x + g (SOURCE, \<langle>x\<rangle>)"
      using \<Psi>.flowD_finite_IN[OF g] g_le
      by(cases "d_IN (h 0) x"; cases "d_IN g \<langle>x\<rangle>"; cases "d_IN g \<langle>x\<rangle>"; cases "g (SOURCE, \<langle>x\<rangle>)")
        (auto simp: flowD_KIR[OF g] top_add ennreal_minus_if ennreal_plus_if simp del: ennreal_plus)
    finally show ?thesis .
  qed

  have h': "current \<Gamma> h'"
  proof
    fix x
    consider (A) "x \<in> A \<Gamma>" | (B) "x \<in> B \<Gamma>" | (outside) "x \<notin> \<^bold>V" using bipartite_V by auto
    note cases = this

    show "d_OUT h' x \<le> weight \<Gamma> x"
    proof(cases rule: cases)
      case A
      then have "d_OUT h' x = d_OUT (h 0) x + g (\<langle>x\<rangle>, SINK) - g (SINK, \<langle>x\<rangle>)" by(simp add: OUT_h'_A)
      also have "\<dots> \<le> d_OUT (h 0) x + g (\<langle>x\<rangle>, SINK)" by(rule diff_le_self_ennreal)
      also have "g (\<langle>x\<rangle>, SINK) \<le> weight \<Gamma> x - d_OUT (h 0) x"
        using flowD_capacity[OF g, of "(\<langle>x\<rangle>, SINK)"] A by simp
      also have "d_OUT (h 0) x + \<dots> = weight \<Gamma> x"
        by(simp add: add_diff_eq_ennreal add_diff_inverse_ennreal  currentD_finite_OUT[OF h] currentD_weight_OUT[OF h])
      finally show ?thesis by(simp add: add_left_mono)
    qed(simp_all add: OUT_h'_outside )

    show "d_IN h' x \<le> weight \<Gamma> x"
    proof(cases rule: cases)
      case B
      hence "d_IN h' x = d_IN (h 0) x + g (SOURCE, \<langle>x\<rangle>)" by(rule IN_h'_B)
      also have "\<dots> \<le> weight \<Gamma> x"
        by(simp add: g_SOURCE \<alpha> currentD_weight_IN[OF h] add_diff_eq_ennreal add_diff_inverse_ennreal currentD_finite_IN[OF h])
      finally show ?thesis .
    qed(simp_all add:  IN_h'_outside)
  next
    show "h' e = 0" if "e \<notin> \<^bold>E" for e using that by(simp split: prod.split_asm add: h'_simps)
  qed
  moreover
  have SAT_h': "B \<Gamma> \<inter> \<^bold>V \<subseteq> SAT \<Gamma> h'"
  proof
    show "x \<in> SAT \<Gamma> h'" if "x \<in> B \<Gamma> \<inter> \<^bold>V" for x using that
    proof(cases "x = b")
      case True
      have "d_IN h' x = weight \<Gamma> x" using that True
        by(simp add: IN_h'_B g_SOURCE \<alpha> currentD_weight_IN[OF h] add_diff_eq_ennreal add_diff_inverse_ennreal currentD_finite_IN[OF h])
      thus ?thesis by(simp add: SAT.simps)
    next
      case False
      have "d_IN h' x = d_IN (h 0) x" using that False by(simp add: IN_h'_B g_SOURCE)
      also have "\<dots> = weight \<Gamma> x"
        using SAT[of 0, THEN subsetD, of x] False that currentD_SAT[OF h, of x 0] disjoint by auto
      finally show ?thesis by(simp add: SAT.simps)
    qed
  qed
  moreover
  have "wave \<Gamma> h'"
  proof
    have "separating \<Gamma> (B \<Gamma> \<inter> \<^bold>V)"
    proof
      fix x y p
      assume x: "x \<in> A \<Gamma>" and y: "y \<in> B \<Gamma>" and p: "path \<Gamma> x p y"
      hence Nil: "p \<noteq> []" using disjoint by(auto simp add: rtrancl_path_simps)
      from rtrancl_path_last[OF p Nil] last_in_set[OF Nil] y rtrancl_path_Range[OF p, of y]
      show "(\<exists>z\<in>set p. z \<in> B \<Gamma> \<inter> \<^bold>V) \<or> x \<in> B \<Gamma> \<inter> \<^bold>V" by(auto intro: vertexI2)
    qed
    moreover have TER: "B \<Gamma> \<inter> \<^bold>V \<subseteq> TER h'" using SAT_h' by(auto simp add: SINK)
    ultimately show "separating \<Gamma> (TER h')" by(rule separating_weakening)
  qed(rule h')
  ultimately show ?thesis by blast
qed

end

lemma countable_bipartite_web_reduce_weight:
  assumes "weight \<Gamma> x \<ge> w"
  shows "countable_bipartite_web (reduce_weight \<Gamma> x w)"
using bipartite_V A_vertex bipartite_E disjoint assms
by unfold_locales (auto 4 3 simp add: weight_outside )

lemma unhinder: \<comment> \<open>Lemma 6.9\<close>
  assumes loose: "loose \<Gamma>"
  and b: "b \<in> B \<Gamma>"
  and wb: "weight \<Gamma> b > 0"
  and \<delta>: "\<delta> > 0"
  shows "\<exists>\<epsilon>>0. \<epsilon> < \<delta> \<and> \<not> hindered (reduce_weight \<Gamma> b \<epsilon>)"
proof(rule ccontr)
  assume "\<not> ?thesis"
  hence hindered: "hindered (reduce_weight \<Gamma> b \<epsilon>)" if "\<epsilon> > 0" "\<epsilon> < \<delta>" for \<epsilon> using that by simp

  from b disjoint have bnA: "b \<notin> A \<Gamma>" by blast

  define wb where "wb = enn2real (weight \<Gamma> b)"
  have wb_conv: "weight \<Gamma> b = ennreal wb" by(simp add: wb_def less_top[symmetric])
  have wb_pos: "wb > 0" using wb by(simp add: wb_conv)

  define \<epsilon> where "\<epsilon> n = min \<delta> wb / (n + 2)" for n :: nat
  have \<epsilon>_pos: "\<epsilon> n > 0" for n using wb_pos \<delta> by(simp add: \<epsilon>_def)
  have \<epsilon>_nonneg: "0 \<le> \<epsilon> n" for n using \<epsilon>_pos[of n] by simp
  have *: "\<epsilon> n \<le> min wb \<delta> / 2" for n using wb_pos \<delta>
    by(auto simp add: \<epsilon>_def field_simps min_def)
  have \<epsilon>_le: "\<epsilon> n \<le> wb" and \<epsilon>_less: "\<epsilon> n < wb" and \<epsilon>_less_\<delta>: "\<epsilon> n < \<delta>" and \<epsilon>_le': "\<epsilon> n \<le> wb / 2" for n
    using *[of n] \<epsilon>_pos[of n] by(auto)

  define \<Gamma>' where "\<Gamma>' n = reduce_weight \<Gamma> b (\<epsilon> n)" for n :: nat
  have \<Gamma>'_sel [simp]:
    "edge (\<Gamma>' n) = edge \<Gamma>"
    "A (\<Gamma>' n) = A \<Gamma>"
    "B (\<Gamma>' n) = B \<Gamma>"
    "weight (\<Gamma>' n) x = weight \<Gamma> x - (if x = b then \<epsilon> n else 0)"
    "essential (\<Gamma>' n) = essential \<Gamma>"
    "roofed_gen (\<Gamma>' n) = roofed_gen \<Gamma>"
    for n x by(simp_all add: \<Gamma>'_def)

  have vertex_\<Gamma>' [simp]: "vertex (\<Gamma>' n) = vertex \<Gamma>" for n
    by(simp add: vertex_def fun_eq_iff)

  from wb have "b \<in> \<^bold>V" using weight_outside[of b] by(auto intro: ccontr)
  interpret \<Gamma>': countable_bipartite_web "\<Gamma>' n" for n unfolding \<Gamma>'_def
    using wb_pos by(intro countable_bipartite_web_reduce_weight)(simp_all add: wb_conv \<epsilon>_le \<epsilon>_nonneg)

  obtain g where g: "\<And>n. current (\<Gamma>' n) (g n)"
    and w: "\<And>n. wave (\<Gamma>' n) (g n)"
    and hind: "\<And>n. hindrance (\<Gamma>' n) (g n)" using hindered[OF \<epsilon>_pos, unfolded wb_conv ennreal_less_iff, OF \<epsilon>_less_\<delta>]
    unfolding hindered.simps \<Gamma>'_def by atomize_elim metis
  from g have g\<Gamma>: "current \<Gamma> (g n)" for n
    by(rule current_weight_mono)(auto simp add: \<epsilon>_nonneg diff_le_self_ennreal)
  note [simp] = currentD_finite[OF g\<Gamma>]

  have b_TER: "b \<in> TER\<^bsub>\<Gamma>' n\<^esub> (g n)" for n
  proof(rule ccontr)
    assume b': "b \<notin> TER\<^bsub>\<Gamma>' n\<^esub> (g n)"
    then have TER: "TER\<^bsub>\<Gamma>' n\<^esub> (g n) = TER (g n)" using b \<epsilon>_nonneg[of n]
      by(auto simp add: SAT.simps split: if_split_asm intro: ennreal_diff_le_mono_left)
    from w[of n] TER have "wave \<Gamma> (g n)" by(simp add: wave.simps separating_gen.simps)
    moreover have "hindrance \<Gamma> (g n)" using hind[of n] TER bnA b'
      by(auto simp add: hindrance.simps split: if_split_asm)
    ultimately show False using loose_unhindered[OF loose] g\<Gamma>[of n] by(auto intro: hindered.intros)
  qed

  have IN_g_b: "d_IN (g n) b = weight \<Gamma> b - \<epsilon> n" for n using b_TER[of n] bnA
    by(auto simp add: currentD_SAT[OF g])

  define factor where "factor n = (wb - \<epsilon> 0) / (wb - \<epsilon> n)" for n
  have factor_le_1: "factor n \<le> 1" for n using wb_pos \<delta> \<epsilon>_less[of n]
    by(auto simp add: factor_def field_simps \<epsilon>_def min_def)
  have factor_pos: "0 < factor n" for n using wb_pos \<delta> * \<epsilon>_less by(simp add: factor_def field_simps)
  have factor: "(wb - \<epsilon> n) * factor n = wb - \<epsilon> 0" for n using \<epsilon>_less[of n]
    by(simp add: factor_def field_simps)

  define g' where "g' = (\<lambda>n (x, y). if y = b then g n (x, y) * factor n else g n (x, y))"
  have g'_simps: "g' n (x, y) = (if y = b then g n (x, y) * factor n else g n (x, y))" for n x y by(simp add: g'_def)
  have g'_le_g: "g' n e \<le> g n e" for n e using factor_le_1[of n]
    by(cases e "g n e" rule: prod.exhaust[case_product ennreal_cases])
      (auto simp add: g'_simps field_simps mult_left_le)

  have "4 + (n * 6 + n * (n * 2)) \<noteq> (0 :: real)" for n :: nat
    by(metis (mono_tags, hide_lams) add_is_0 of_nat_eq_0_iff of_nat_numeral zero_neq_numeral)
  then have IN_g': "d_IN (g' n) x = (if x = b then weight \<Gamma> b - \<epsilon> 0 else d_IN (g n) x)" for x n
    using b_TER[of n] bnA factor_pos[of n] factor[of n] wb_pos \<delta>
    by(auto simp add: d_IN_def g'_simps nn_integral_divide nn_integral_cmult currentD_SAT[OF g] wb_conv \<epsilon>_def field_simps
                      ennreal_minus ennreal_mult'[symmetric] intro!: arg_cong[where f=ennreal])
  have OUT_g': "d_OUT (g' n) x = d_OUT (g n) x - g n (x, b) * (1 - factor n)" for n x
  proof -
    have "d_OUT (g' n) x = (\<Sum>\<^sup>+ y. g n (x, y)) - (\<Sum>\<^sup>+ y. (g n (x, y) * (1 - factor n)) * indicator {b} y)"
      using factor_le_1[of n] factor_pos[of n]
      apply(cases "g n (x, b)")
      apply(subst nn_integral_diff[symmetric])
      apply(auto simp add: g'_simps nn_integral_divide d_OUT_def AE_count_space mult_left_le ennreal_mult_eq_top_iff
                           ennreal_mult'[symmetric] ennreal_minus_if
                 intro!: nn_integral_cong split: split_indicator)
      apply(simp_all add: field_simps)
      done
    also have "\<dots> = d_OUT (g n) x - g n (x, b) * (1 - factor n)" using factor_le_1[of n]
      by(subst nn_integral_indicator_singleton)(simp_all add: d_OUT_def field_simps)
    finally show ?thesis .
  qed

  have g': "current (\<Gamma>' 0) (g' n)" for n
  proof
    show "d_OUT (g' n) x \<le> weight (\<Gamma>' 0) x" for x
      using b_TER[of n] currentD_weight_OUT[OF g, of n x] \<epsilon>_le[of 0] factor_le_1[of n]
      by(auto simp add: OUT_g' SINK.simps ennreal_diff_le_mono_left)
    show "d_IN (g' n) x \<le> weight (\<Gamma>' 0) x" for x
      using d_IN_mono[of "g' n" x, OF g'_le_g] currentD_weight_IN[OF g, of n x] b_TER[of n] b
      by(auto simp add: IN_g' SAT.simps wb_conv \<epsilon>_def)
    show "g' n e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Gamma>' 0\<^esub>" for e using that by(cases e)(clarsimp simp add: g'_simps currentD_outside[OF g])
  qed

  have SINK_g': "SINK (g n) = SINK (g' n)" for n using factor_pos[of n]
    by(auto simp add: SINK.simps currentD_OUT_eq_0[OF g] currentD_OUT_eq_0[OF g'] g'_simps split: if_split_asm)
  have SAT_g': "SAT (\<Gamma>' n) (g n) = SAT (\<Gamma>' 0) (g' n)" for n using b_TER[of n] \<epsilon>_le'[of 0]
    by(auto simp add: SAT.simps wb_conv IN_g' IN_g_b)
  have TER_g': "TER\<^bsub>\<Gamma>' n\<^esub> (g n) = TER\<^bsub>\<Gamma>' 0\<^esub> (g' n)" for n
    using b_TER[of n] by(auto simp add: SAT.simps SINK_g' OUT_g' IN_g' wb_conv \<epsilon>_def)

  have w': "wave (\<Gamma>' 0) (g' n)" for n
  proof
    have "separating (\<Gamma>' 0) (TER\<^bsub>\<Gamma>' n\<^esub> (g n))" using waveD_separating[OF w, of n]
      by(simp add: separating_gen.simps)
    then show "separating (\<Gamma>' 0) (TER\<^bsub>\<Gamma>' 0\<^esub> (g' n))" unfolding TER_g' .
  qed(rule g')

  define f where "f = rec_nat (g 0) (\<lambda>n rec. rec \<frown>\<^bsub>\<Gamma>' 0\<^esub> g' (n + 1))"
  have f_simps [simp]:
    "f 0 = g 0"
    "f (Suc n) = f n \<frown>\<^bsub>\<Gamma>' 0\<^esub> g' (n + 1)"
    for n by(simp_all add: f_def)

  have f: "current (\<Gamma>' 0) (f n)" and fw: "wave (\<Gamma>' 0) (f n)" for n
  proof(induction n)
    case (Suc n)
    { case 1 show ?case unfolding f_simps using Suc.IH g' by(rule current_plus_web) }
    { case 2 show ?case unfolding f_simps using Suc.IH g' w' by(rule wave_plus') }
  qed(simp_all add: g w)

  have f_inc: "n \<le> m \<Longrightarrow> f n \<le> f m" for n m
  proof(induction m rule: dec_induct)
    case (step k)
    note step.IH
    also have "f k \<le> (f k \<frown>\<^bsub>\<Gamma>' 0\<^esub> g' (k + 1))"
      by(rule le_funI plus_web_greater)+
    also have "\<dots> = f (Suc k)" by simp
    finally show ?case .
  qed simp
  have chain_f: "Complete_Partial_Order.chain (\<le>) (range f)"
    by(rule chain_imageI[where le_a="(\<le>)"])(simp_all add: f_inc)
  have "countable (support_flow (f n))" for n using current_support_flow[OF f, of n]
    by(rule countable_subset) simp
  hence supp_f: "countable (support_flow (SUP n. f n))" by(subst support_flow_Sup)simp

  have RF_f: "RF (TER\<^bsub>\<Gamma>' 0\<^esub> (f n)) = RF (\<Union>i\<le>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i))" for n
  proof(induction n)
    case 0 show ?case by(simp add: TER_g')
  next
    case (Suc n)
    have "RF (TER\<^bsub>\<Gamma>' 0\<^esub> (f (Suc n))) = RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (f n \<frown>\<^bsub>\<Gamma>' 0\<^esub> g' (n + 1)))" by simp
    also have "\<dots> = RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (f n) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' (n + 1)))" using f fw g' w'
      by(rule RF_TER_plus_web)
    also have "\<dots> = RF\<^bsub>\<Gamma>' 0\<^esub> (RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (f n)) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' (n + 1)))"
      by(simp add: roofed_idem_Un1)
    also have "RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (f n)) = RF\<^bsub>\<Gamma>' 0\<^esub> (\<Union>i\<le>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i))" by(simp add: Suc.IH)
    also have "RF\<^bsub>\<Gamma>' 0\<^esub> (\<dots> \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' (n + 1))) = RF\<^bsub>\<Gamma>' 0\<^esub> ((\<Union>i\<le>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i)) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' (n + 1)))"
      by(simp add: roofed_idem_Un1)
    also have "(\<Union>i\<le>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i)) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' (n + 1)) = (\<Union>i\<le>Suc n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i))"
      unfolding atMost_Suc UN_insert by(simp add: Un_commute)
    finally show ?case by simp
  qed

  define g\<omega> where "g\<omega> = (SUP n. f n)"
  have g\<omega>: "current (\<Gamma>' 0) g\<omega>" unfolding g\<omega>_def using chain_f
    by(rule current_Sup)(auto simp add: f supp_f)
  have w\<omega>: "wave (\<Gamma>' 0) g\<omega>" unfolding g\<omega>_def using chain_f
    by(rule wave_lub)(auto simp add: fw  supp_f)
  from g\<omega> have g\<omega>': "current (\<Gamma>' n) g\<omega>" for n using wb_pos \<delta>
    by(elim current_weight_mono)(auto simp add: \<epsilon>_le wb_conv \<epsilon>_def field_simps ennreal_minus_if min_le_iff_disj)

  have SINK_g\<omega>: "SINK g\<omega> = (\<Inter>n. SINK (f n))" unfolding g\<omega>_def
    by(subst SINK_Sup[OF chain_f])(simp_all add: supp_f)
  have SAT_g\<omega>: "SAT (\<Gamma>' 0) (f n) \<subseteq> SAT (\<Gamma>' 0) g\<omega>" for n
    unfolding g\<omega>_def by(rule SAT_Sup_upper) simp

  have g_b_out: "g n (b, x) = 0" for n x using b_TER[of n] by(simp add: SINK.simps currentD_OUT_eq_0[OF g])
  have g'_b_out: "g' n (b, x) = 0" for n x by(simp add: g'_simps g_b_out)
  have "f n (b, x) = 0" for n x by(induction n)(simp_all add: g_b_out g'_b_out)
  hence b_SINK_f: "b \<in> SINK (f n)" for n by(simp add: SINK.simps d_OUT_def)
  hence b_SINK_g\<omega>: "b \<in> SINK g\<omega>" by(simp add: SINK_g\<omega>)

  have RF_circ: "RF\<^sup>\<circ>\<^bsub>\<Gamma>' n\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (g' n)) = RF\<^sup>\<circ>\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (g' n))" for n by(simp add: roofed_circ_def)
  have edge_restrict_\<Gamma>': "edge (quotient_web (\<Gamma>' 0) (g' n)) = edge (quotient_web (\<Gamma>' n) (g n))" for n
    by(simp add: fun_eq_iff TER_g' RF_circ)
  have restrict_curr_g': "f \<upharpoonleft> \<Gamma>' 0 / g' n = f \<upharpoonleft> \<Gamma>' n / g n" for n f
    by(simp add: restrict_current_def RF_circ TER_g')

  have RF_restrict: "roofed_gen (quotient_web (\<Gamma>' n) (g n)) = roofed_gen (quotient_web (\<Gamma>' 0) (g' n))" for n
    by(simp add: roofed_def fun_eq_iff edge_restrict_\<Gamma>')

  have g\<omega>r': "current (quotient_web (\<Gamma>' 0) (g' n)) (g\<omega> \<upharpoonleft> \<Gamma>' 0 / g' n)" for n using w' g\<omega>
    by(rule current_restrict_current)
  have g\<omega>r: "current (quotient_web (\<Gamma>' n) (g n)) (g\<omega> \<upharpoonleft> \<Gamma>' n / g n)" for n using w g\<omega>'
    by(rule current_restrict_current)
  have w\<omega>r: "wave (quotient_web (\<Gamma>' n) (g n)) (g\<omega> \<upharpoonleft> \<Gamma>' n / g n)" (is "wave ?\<Gamma>' ?g\<omega>") for n
  proof
    have *: "wave (quotient_web (\<Gamma>' 0) (g' n)) (g\<omega> \<upharpoonleft> \<Gamma>' 0 / g' n)"
      using g' w' g\<omega> w\<omega> by(rule wave_restrict_current)
    have "d_IN (g\<omega> \<upharpoonleft> \<Gamma>' n / g n) b = 0"
      by(rule d_IN_restrict_current_outside roofed_greaterI b_TER)+
    hence SAT_subset: "SAT (quotient_web (\<Gamma>' 0) (g' n)) (g\<omega> \<upharpoonleft> \<Gamma>' n / g n) \<subseteq> SAT ?\<Gamma>' (g\<omega> \<upharpoonleft> \<Gamma>' n / g n)"
      using b_TER[of n] wb_pos
      by(auto simp add: SAT.simps TER_g' RF_circ wb_conv \<epsilon>_def field_simps
                        ennreal_minus_if split: if_split_asm)
    hence TER_subset: "TER\<^bsub>quotient_web (\<Gamma>' 0) (g' n)\<^esub> (g\<omega> \<upharpoonleft> \<Gamma>' n / g n) \<subseteq> TER\<^bsub>?\<Gamma>'\<^esub> (g\<omega> \<upharpoonleft> \<Gamma>' n / g n)"
      using SINK_g' by(auto simp add: restrict_curr_g')

    show "separating ?\<Gamma>' (TER\<^bsub>?\<Gamma>'\<^esub> ?g\<omega>)" (is "separating _ ?TER")
    proof
      fix x y p
      assume xy: "x \<in> A ?\<Gamma>'" "y \<in> B ?\<Gamma>'" and p: "path ?\<Gamma>' x p y"
      from p have p': "path (quotient_web (\<Gamma>' 0) (g' n)) x p y" by(simp add: edge_restrict_\<Gamma>')
      with waveD_separating[OF *, THEN separatingD, simplified, OF p'] TER_g'[of n] SINK_g' SAT_g' restrict_curr_g' SAT_subset xy
      show "(\<exists>z\<in>set p. z \<in> ?TER) \<or> x \<in> ?TER" by auto
    qed

    show "d_OUT (g\<omega> \<upharpoonleft> \<Gamma>' n / g n) x = 0" if "x \<notin> RF\<^bsub>?\<Gamma>'\<^esub> ?TER" for x
      unfolding restrict_curr_g'[symmetric] using TER_subset that
      by(intro waveD_OUT[OF *])(auto simp add: TER_g' restrict_curr_g' RF_restrict intro: in_roofed_mono)
  qed

  have RF_g\<omega>: "RF (TER\<^bsub>\<Gamma>' 0\<^esub> g\<omega>) = RF (\<Union>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' n))"
  proof -
    have "RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> g\<omega>) = RF (\<Union>i. TER\<^bsub>\<Gamma>' 0\<^esub> (f i))"
      unfolding g\<omega>_def by(subst RF_TER_Sup[OF _ _ chain_f])(auto simp add: f fw supp_f)
    also have "\<dots> = RF (\<Union>i. RF (TER\<^bsub>\<Gamma>' 0\<^esub> (f i)))" by(simp add: roofed_UN)
    also have "\<dots> = RF (\<Union>i. \<Union>j\<le>i. TER\<^bsub>\<Gamma>' 0\<^esub> (g' j))" unfolding RF_f roofed_UN by simp
    also have "(\<Union>i. \<Union>j\<le>i. TER\<^bsub>\<Gamma>' 0\<^esub> (g' j)) = (\<Union>i. TER\<^bsub>\<Gamma>' 0\<^esub> (g' i))" by auto
    finally show ?thesis by simp
  qed

  have SAT_plus_\<omega>: "SAT (\<Gamma>' n) (g n \<frown>\<^bsub>\<Gamma>' n\<^esub> g\<omega>) = SAT (\<Gamma>' 0) (g' n \<frown>\<^bsub>\<Gamma>' 0\<^esub> g\<omega>)" for n
    apply(intro set_eqI)
    apply(simp add: SAT.simps IN_plus_current[OF g w g\<omega>r] IN_plus_current[OF g' w' g\<omega>r'] TER_g')
    apply(cases "d_IN (g\<omega> \<upharpoonleft> \<Gamma>' n / g n) b")
    apply(auto simp add: SAT.simps wb_conv d_IN_plus_web IN_g')
    apply(simp_all add: wb_conv IN_g_b restrict_curr_g' \<epsilon>_def field_simps)
    apply(metis TER_g' b_TER roofed_greaterI)+
    done
  have SINK_plus_\<omega>: "SINK (g n \<frown>\<^bsub>\<Gamma>' n\<^esub> g\<omega>) = SINK (g' n \<frown>\<^bsub>\<Gamma>' 0\<^esub> g\<omega>)" for n
    apply(rule set_eqI; simp add: SINK.simps OUT_plus_current[OF g w g\<omega>r] OUT_plus_current[OF g' w'] current_restrict_current[OF w' g\<omega>])
    using factor_pos[of n]
    by(auto simp add: RF_circ TER_g' restrict_curr_g' currentD_OUT_eq_0[OF g] currentD_OUT_eq_0[OF g'] g'_simps split: if_split_asm)
  have TER_plus_\<omega>: "TER\<^bsub>\<Gamma>' n\<^esub> (g n \<frown>\<^bsub>\<Gamma>' n\<^esub> g\<omega>) = TER\<^bsub>\<Gamma>' 0\<^esub> (g' n \<frown>\<^bsub>\<Gamma>' 0\<^esub> g\<omega>)" for n
    by(rule set_eqI iffI)+(simp_all add: SAT_plus_\<omega> SINK_plus_\<omega>)

  define h where "h n = g n \<frown>\<^bsub>\<Gamma>' n\<^esub> g\<omega>" for n
  have h: "current (\<Gamma>' n) (h n)" for n unfolding h_def using g w
    by(rule current_plus_current)(rule current_restrict_current[OF w g\<omega>'])
  have hw: "wave (\<Gamma>' n) (h n)" for n unfolding h_def using g w g\<omega>' w\<omega>r by(rule wave_plus)

  define T where "T = TER\<^bsub>\<Gamma>' 0\<^esub> g\<omega>"
  have RF_h: "RF (TER\<^bsub>\<Gamma>' n\<^esub> (h n)) = RF T" for n
  proof -
    have "RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' n\<^esub> (h n)) = RF\<^bsub>\<Gamma>' 0\<^esub> (RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> g\<omega>) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' n))"
      unfolding h_def TER_plus_\<omega> RF_TER_plus_web[OF g' w' g\<omega> w\<omega>] roofed_idem_Un1 by(simp add: Un_commute)
    also have "\<dots> = RF ((\<Union>n. TER\<^bsub>\<Gamma>' 0\<^esub> (g' n)) \<union> TER\<^bsub>\<Gamma>' 0\<^esub> (g' n))"
      by(simp add: RF_g\<omega> roofed_idem_Un1)
    also have "\<dots> = RF\<^bsub>\<Gamma>' 0\<^esub> T" unfolding T_def
      by(auto simp add: RF_g\<omega> intro!: arg_cong2[where f=roofed] del: equalityI) auto
    finally show ?thesis by simp
  qed
  have OUT_h_nT: "d_OUT (h n) x = 0" if "x \<notin> RF T" for n x
    by(rule waveD_OUT[OF hw])(simp add: RF_h that)
  have IN_h_nT: "d_IN (h n) x = 0" if "x \<notin> RF T" for n x
    by(rule wave_not_RF_IN_zero[OF h hw])(simp add: RF_h that)
  have OUT_h_b: "d_OUT (h n) b = 0" for n using b_TER[of n] b_SINK_g\<omega>[THEN in_SINK_restrict_current]
    by(auto simp add: h_def OUT_plus_current[OF g w g\<omega>r] SINK.simps)
  have OUT_h_\<E>: "d_OUT (h n) x = 0" if "x \<in> \<E> T" for x n using that
    apply(subst (asm) \<E>_RF[symmetric])
    apply(subst (asm) (1 2) RF_h[symmetric, of n])
    apply(subst (asm) \<E>_RF)
    apply(simp add: SINK.simps)
    done
  have IN_h_\<E>: "d_IN (h n) x = weight (\<Gamma>' n) x" if "x \<in> \<E> T" "x \<notin> A \<Gamma>" for x n using that
    apply(subst (asm) \<E>_RF[symmetric])
    apply(subst (asm) (1 2) RF_h[symmetric, of n])
    apply(subst (asm) \<E>_RF)
    apply(simp add: currentD_SAT[OF h])
    done

  have b_SAT: "b \<in> SAT (\<Gamma>' 0) (h 0)" using b_TER[of 0]
    by(auto simp add: h_def SAT.simps d_IN_plus_web intro: order_trans)
  have b_T: "b \<in> T" using b_SINK_g\<omega> b_TER by(simp add: T_def)(metis SAT_g\<omega> subsetD f_simps(1))

  have essential: "b \<in> \<E> T"
  proof(rule ccontr)
    assume "b \<notin> \<E> T"
    hence b: "b \<notin> \<E> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0))"
    proof(rule contrapos_nn)
      assume "b \<in> \<E> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0))"
      then obtain p y where p: "path \<Gamma> b p y" and y: "y \<in> B \<Gamma>" and distinct: "distinct (b # p)"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0))" by(rule \<E>_E_RF) auto
      from bypass have bypass': "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> T" unfolding RF_h by(auto intro: roofed_greaterI)
      have "essential \<Gamma> (B \<Gamma>) T b" using p y by(rule essentialI)(auto dest: bypass')
      then show "b \<in> \<E> T" using b_T by simp
    qed

    have h0: "current \<Gamma> (h 0)" using h[of 0] by(rule current_weight_mono)(simp_all add: wb_conv \<epsilon>_nonneg)
    moreover have "wave \<Gamma> (h 0)"
    proof
      have "separating (\<Gamma>' 0) (\<E>\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)))" by(rule separating_essential)(rule waveD_separating[OF hw])
      then have "separating \<Gamma> (\<E> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)))" by(simp add: separating_gen.simps)
      moreover have subset: "\<E> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)) \<subseteq> TER (h 0)" using \<epsilon>_nonneg[of 0] b
        by(auto simp add: SAT.simps wb_conv split: if_split_asm)
      ultimately show "separating \<Gamma> (TER (h 0))" by(rule separating_weakening)
    qed(rule h0)
    ultimately have "h 0 = zero_current" by(rule looseD_wave[OF loose])
    then have "d_IN (h 0) b = 0" by(simp)
    with b_SAT wb \<open>b \<notin> A \<Gamma>\<close> show False by(simp add: SAT.simps wb_conv \<epsilon>_def ennreal_minus_if split: if_split_asm)
  qed

  define S where "S = {x \<in> RF (T \<inter> B \<Gamma>) \<inter> A \<Gamma>. essential \<Gamma> (T \<inter> B \<Gamma>) (RF (T \<inter> B \<Gamma>) \<inter> A \<Gamma>) x}"
  define \<Gamma>_h where "\<Gamma>_h = \<lparr> edge = \<lambda>x y. edge \<Gamma> x y \<and> x \<in> S \<and> y \<in> T \<and> y \<in> B \<Gamma>, weight = \<lambda>x. weight \<Gamma> x * indicator (S \<union> T \<inter> B \<Gamma>) x, A = S, B = T \<inter> B \<Gamma>\<rparr>"
  have \<Gamma>_h_sel [simp]:
    "edge \<Gamma>_h x y \<longleftrightarrow> edge \<Gamma> x y \<and> x \<in> S \<and> y \<in> T \<and> y \<in> B \<Gamma>"
    "A \<Gamma>_h = S"
    "B \<Gamma>_h = T \<inter> B \<Gamma>"
    "weight \<Gamma>_h x = weight \<Gamma> x * indicator (S \<union> T \<inter> B \<Gamma>) x"
    for x y
    by(simp_all add: \<Gamma>_h_def)

  have vertex_\<Gamma>_hD: "x \<in> S \<union> (T \<inter> B \<Gamma>)" if "vertex \<Gamma>_h x" for x
    using that by(auto simp add: vertex_def)
  have S_vertex: "vertex \<Gamma>_h x" if "x \<in> S" for x
  proof -
    from that have a: "x \<in> A \<Gamma>" and RF: "x \<in> RF (T \<inter> B \<Gamma>)" and ess: "essential \<Gamma> (T \<inter> B \<Gamma>) (RF (T \<inter> B \<Gamma>) \<inter> A \<Gamma>) x"
      by(simp_all add: S_def)
    from ess obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and yT: "y \<in> T"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (T \<inter> B \<Gamma>) \<inter> A \<Gamma>" by(rule essentialE_RF)(auto intro: roofed_greaterI)
    from p a y disjoint have "edge \<Gamma> x y"
      by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
    with that y yT show ?thesis by(auto intro!: vertexI1)
  qed
  have OUT_not_S: "d_OUT (h n) x = 0" if "x \<notin> S" for x n
  proof(rule classical)
    assume *: "d_OUT (h n) x \<noteq> 0"
    consider (A) "x \<in> A \<Gamma>" | (B) "x \<in> B \<Gamma>" | (outside) "x \<notin> A \<Gamma>" "x \<notin> B \<Gamma>" by blast
    then show ?thesis
    proof cases
      case B with currentD_OUT[OF h, of x n] show ?thesis by simp
    next
      case outside with currentD_outside_OUT[OF h, of x n] show ?thesis by(simp add: not_vertex)
    next
      case A
      from * obtain y where xy: "h n (x, y) \<noteq> 0" using currentD_OUT_eq_0[OF h, of n x] by auto
      then have edge: "edge \<Gamma> x y" using currentD_outside[OF h] by(auto)
      hence p: "path \<Gamma> x [y] y" by(simp add: rtrancl_path_simps)

      from bipartite_E[OF edge] have x: "x \<in> A \<Gamma>" and y: "y \<in> B \<Gamma>" by simp_all
      moreover have "x \<in> RF (RF (T \<inter> B \<Gamma>))"
      proof
        fix p y'
        assume p: "path \<Gamma> x p y'" and y': "y' \<in> B \<Gamma>"
        from p x y' disjoint have py: "p = [y']"
          by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
        have "separating (\<Gamma>' 0) (RF\<^bsub>\<Gamma>' 0\<^esub> (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)))" unfolding separating_RF
          by(rule waveD_separating[OF hw])
        from separatingD[OF this, of x p y'] py p x y'
        have "x \<in> RF T \<or> y' \<in> RF T" by(auto simp add: RF_h)
        thus "(\<exists>z\<in>set p. z \<in> RF (T \<inter> B \<Gamma>)) \<or> x \<in> RF (T \<inter> B \<Gamma>)"
        proof cases
          case right with y' py show ?thesis by(simp add: RF_in_B)
        next
          case left
          have "x \<notin> \<E> T" using OUT_h_\<E>[of x n] xy by(auto simp add: currentD_OUT_eq_0[OF h])
          with left have "x \<in> RF\<^sup>\<circ> T" by(simp add: roofed_circ_def)
          from RF_circ_edge_forward[OF this, of y'] p py have "y' \<in> RF T" by(simp add: rtrancl_path_simps)
          with y' have "y' \<in> T" by(simp add: RF_in_B)
          with y' show ?thesis using py by(auto intro: roofed_greaterI)
        qed
      qed
      moreover have "y \<in> T" using IN_h_nT[of y n] y xy by(auto simp add: RF_in_B currentD_IN_eq_0[OF h])
      with p x y disjoint have "essential \<Gamma> (T \<inter> B \<Gamma>) (RF (T \<inter> B \<Gamma>) \<inter> A \<Gamma>) x" by(auto intro!: essentialI)
      ultimately have "x \<in> S" unfolding roofed_idem by(simp add: S_def)
      with that show ?thesis by contradiction
    qed
  qed

  have B_vertex: "vertex \<Gamma>_h y" if T: "y \<in> T" and B: "y \<in> B \<Gamma>" and w: "weight \<Gamma> y > 0" for y
  proof -
    from T B disjoint \<epsilon>_less[of 0] w
    have "d_IN (h 0) y > 0" using IN_h_\<E>[of y 0] by(cases "y \<in> A \<Gamma>")(auto simp add: essential_BI wb_conv ennreal_minus_if)
    then obtain x where xy: "h 0 (x, y) \<noteq> 0" using currentD_IN_eq_0[OF h, of 0 y] by(auto)
    then have edge: "edge \<Gamma> x y" using currentD_outside[OF h] by(auto)
    from xy have "d_OUT (h 0) x \<noteq> 0" by(auto simp add: currentD_OUT_eq_0[OF h])
    hence "x \<in> S" using OUT_not_S[of x 0] by(auto)
    with edge T B show ?thesis by(simp add: vertexI2)
  qed

  have \<Gamma>_h: "countable_bipartite_web \<Gamma>_h"
  proof
    show "\<^bold>V\<^bsub>\<Gamma>_h\<^esub> \<subseteq> A \<Gamma>_h \<union> B \<Gamma>_h" by(auto simp add: vertex_def)
    show "A \<Gamma>_h \<subseteq> \<^bold>V\<^bsub>\<Gamma>_h\<^esub>" using S_vertex by auto
    show "x \<in> A \<Gamma>_h \<and> y \<in> B \<Gamma>_h" if "edge \<Gamma>_h x y" for x y using that by auto
    show "A \<Gamma>_h \<inter> B \<Gamma>_h = {}" using disjoint by(auto simp add: S_def)
    have "\<^bold>E\<^bsub>\<Gamma>_h\<^esub> \<subseteq> \<^bold>E" by auto
    thus "countable \<^bold>E\<^bsub>\<Gamma>_h\<^esub>" by(rule countable_subset) simp
    show "weight \<Gamma>_h x \<noteq> \<top>" for x by(simp split: split_indicator)
    show "weight \<Gamma>_h x = 0" if "x \<notin> \<^bold>V\<^bsub>\<Gamma>_h\<^esub>" for x
      using that S_vertex B_vertex[of x]
      by(cases "weight \<Gamma>_h x > 0")(auto split: split_indicator)
  qed
  then interpret \<Gamma>_h: countable_bipartite_web \<Gamma>_h .

  have essential_T: "essential \<Gamma> (B \<Gamma>) T = essential \<Gamma> (B \<Gamma>) (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0))"
  proof(rule ext iffI)+
    fix x
    assume "essential \<Gamma> (B \<Gamma>) T x"
    then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and distinct: "distinct (x # p)"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF T" by(rule essentialE_RF)auto
    from bypass have bypass': "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)"
      unfolding RF_h[of 0, symmetric] by(blast intro: roofed_greaterI)
    show "essential \<Gamma> (B \<Gamma>) (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)) x" using p y
      by(blast intro: essentialI dest: bypass')
  next
    fix x
    assume "essential \<Gamma> (B \<Gamma>) (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0)) x"
    then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and distinct: "distinct (x # p)"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER\<^bsub>\<Gamma>' 0\<^esub> (h 0))" by(rule essentialE_RF)auto
    from bypass have bypass': "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> T"
      unfolding RF_h[of 0] by(blast intro: roofed_greaterI)
    show "essential \<Gamma> (B \<Gamma>) T x" using p y
      by(blast intro: essentialI dest: bypass')
  qed

  have h': "current \<Gamma>_h (h n)" for n
  proof
    show "d_OUT (h n) x \<le> weight \<Gamma>_h x" for x
      using currentD_weight_OUT[OF h, of n x] \<epsilon>_nonneg[of n] \<Gamma>'.currentD_OUT'[OF h, of x n] OUT_not_S
      by(auto split: split_indicator if_split_asm elim: order_trans intro: diff_le_self_ennreal in_roofed_mono simp add: OUT_h_b  roofed_circ_def)

    show "d_IN (h n) x \<le> weight \<Gamma>_h x" for x
      using currentD_weight_IN[OF h, of n x] currentD_IN[OF h, of x n] \<epsilon>_nonneg[of n] b_T b \<Gamma>'.currentD_IN'[OF h, of x n] IN_h_nT[of x n]
      by(cases "x \<in> B \<Gamma>")(auto 4 3 split: split_indicator split: if_split_asm elim: order_trans intro: diff_le_self_ennreal simp add: S_def  roofed_circ_def RF_in_B)

    show "h n e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Gamma>_h\<^esub>" for e
      using that OUT_not_S[of "fst e" n] currentD_outside'[OF h, of e n] \<Gamma>'.currentD_IN'[OF h, of "snd e" n] disjoint
      apply(cases "e \<in> \<^bold>E")
      apply(auto split: prod.split_asm simp add: currentD_OUT_eq_0[OF h] currentD_IN_eq_0[OF h])
      apply(cases "fst e \<in> S"; clarsimp simp add: S_def)
      apply(frule RF_circ_edge_forward[rotated])
      apply(erule roofed_circI, blast)
      apply(drule bipartite_E)
      apply(simp add: RF_in_B)
      done
  qed

  have SAT_h': "B \<Gamma>_h \<inter> \<^bold>V\<^bsub>\<Gamma>_h\<^esub> - {b} \<subseteq> SAT \<Gamma>_h (h n)" for n
  proof
    fix x
    assume "x \<in> B \<Gamma>_h \<inter> \<^bold>V\<^bsub>\<Gamma>_h\<^esub> - {b}"
    then have x: "x \<in> T" and B: "x \<in> B \<Gamma>" and b: "x \<noteq> b" and vertex: "x \<in> \<^bold>V\<^bsub>\<Gamma>_h\<^esub>" by auto
    from B disjoint have xnA: "x \<notin> A \<Gamma>" by blast
    from x B have "x \<in> \<E> T" by(simp add: essential_BI)
    hence "d_IN (h n) x = weight (\<Gamma>' n) x" using xnA by(rule IN_h_\<E>)
    with xnA b x B show "x \<in> SAT \<Gamma>_h (h n)" by(simp add: currentD_SAT[OF h'])
  qed
  moreover have "b \<in> B \<Gamma>_h" using b essential by simp
  moreover have "(\<lambda>n. min \<delta> wb * (1 / (real (n + 2)))) \<longlonglongrightarrow> 0"
    apply(rule LIMSEQ_ignore_initial_segment)
    apply(rule tendsto_mult_right_zero)
    apply(rule lim_1_over_real_power[where s=1, simplified])
    done
  then have "(INF n. ennreal (\<epsilon> n)) = 0" using wb_pos \<delta>
    apply(simp add: \<epsilon>_def)
    apply(rule INF_Lim)
    apply(rule decseq_SucI)
    apply(simp add: field_simps min_def)
    apply(simp add: add.commute ennreal_0[symmetric] del: ennreal_0)
    done
  then have "(SUP n. d_IN (h n) b) = weight \<Gamma>_h b" using essential b bnA wb IN_h_\<E>[of b]
    by(simp add: SUP_const_minus_ennreal)
  moreover have "d_IN (h 0) b \<le> d_IN (h n) b" for n using essential b bnA wb_pos \<delta> IN_h_\<E>[of b]
    by(simp add: wb_conv \<epsilon>_def field_simps ennreal_minus_if min_le_iff_disj)
  moreover have b_V: "b \<in> \<^bold>V\<^bsub>\<Gamma>_h\<^esub>" using b wb essential by(auto dest: B_vertex)
  ultimately have "\<exists>h'. current \<Gamma>_h h' \<and> wave \<Gamma>_h h' \<and> B \<Gamma>_h \<inter> \<^bold>V\<^bsub>\<Gamma>_h\<^esub> \<subseteq> SAT \<Gamma>_h h'"
    by(rule \<Gamma>_h.unhinder_bipartite[OF h'])
  then obtain h' where h': "current \<Gamma>_h h'" and h'w: "wave \<Gamma>_h h'"
    and B_SAT': "B \<Gamma>_h \<inter> \<^bold>V\<^bsub>\<Gamma>_h\<^esub> \<subseteq> SAT \<Gamma>_h h'" by blast

  have h'': "current \<Gamma> h'"
  proof
    show "d_OUT h' x \<le> weight \<Gamma> x" for x using currentD_weight_OUT[OF h', of x]
      by(auto split: split_indicator_asm elim: order_trans intro: )
    show "d_IN h' x \<le> weight \<Gamma> x" for x using currentD_weight_IN[OF h', of x]
      by(auto split: split_indicator_asm elim: order_trans intro: )
    show "h' e = 0" if "e \<notin> \<^bold>E" for e using currentD_outside'[OF h', of e] that by auto
  qed
  moreover have "wave \<Gamma> h'"
  proof
    have "separating (\<Gamma>' 0) T" unfolding T_def by(rule waveD_separating[OF w\<omega>])
    hence "separating \<Gamma> T" by(simp add: separating_gen.simps)
    hence *: "separating \<Gamma> (\<E> T)" by(rule separating_essential)
    show "separating \<Gamma> (TER h')"
    proof
      fix x p y
      assume x: "x \<in> A \<Gamma>" and p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
      from p x y disjoint have py: "p = [y]"
        by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
      from separatingD[OF * p x y] py have "x \<in> \<E> T \<or> y \<in> \<E> T" by auto
      then show "(\<exists>z\<in>set p. z \<in> TER h') \<or> x \<in> TER h'"
      proof cases
        case left
        then have "x \<notin> \<^bold>V\<^bsub>\<Gamma>_h\<^esub>" using x disjoint
          by(auto 4 4 dest!: vertex_\<Gamma>_hD simp add: S_def elim: essentialE_RF intro!: roofed_greaterI dest: roofedD)
        hence "d_OUT h' x = 0" by(intro currentD_outside_OUT[OF h'])
        with x have "x \<in> TER h'" by(auto simp add: SAT.A SINK.simps)
        thus ?thesis ..
      next
        case right
        have "y \<in> SAT \<Gamma> h'"
        proof(cases "weight \<Gamma> y > 0")
          case True
          with py x y right have "vertex \<Gamma>_h y" by(auto intro: B_vertex)
          hence "y \<in> SAT \<Gamma>_h h'" using B_SAT' right y by auto
          with right y disjoint show ?thesis
            by(auto simp add: currentD_SAT[OF h'] currentD_SAT[OF h''] S_def)
        qed(auto simp add: SAT.simps)
        with currentD_OUT[OF h', of y] y right have "y \<in> TER h'" by(auto simp add: SINK)
        thus ?thesis using py by simp
      qed
    qed
  qed(rule h'')
  ultimately have "h' = zero_current" by(rule looseD_wave[OF loose])
  hence "d_IN h' b = 0" by simp
  moreover from essential b b_V B_SAT' have "b \<in> SAT \<Gamma>_h h'" by(auto)
  ultimately show False using wb b essential disjoint by(auto simp add: SAT.simps S_def)
qed

end

subsection \<open>Single-vertex saturation in unhindered bipartite webs\<close>

text \<open>
  The proof of lemma 6.10 in @{cite "AharoniBergerGeorgakopoulusPerlsteinSpruessel2011JCT"} is flawed.
  The transfinite steps (taking the least upper bound) only preserves unhinderedness, but not looseness.
  However, the single steps to non-limit ordinals assumes that \<open>\<Omega> - f\<^sub>i\<close> is loose in order to
  apply Lemma 6.9.

  Counterexample: The bipartite web with three nodes \<open>a\<^sub>1\<close>, \<open>a\<^sub>2\<close>, \<open>a\<^sub>3\<close> in \<open>A\<close>
  and two nodes \<open>b\<^sub>1\<close>, \<open>b\<^sub>2\<close> in \<open>B\<close> and edges \<open>(a\<^sub>1, b\<^sub>1)\<close>, \<open>(a\<^sub>2, b\<^sub>1)\<close>,
  \<open>(a\<^sub>2, b\<^sub>2)\<close>, \<open>(a\<^sub>3, b\<^sub>2)\<close> and weights \<open>a\<^sub>1 = a\<^sub>3 = 1\<close> and \<open>a\<^sub>2 = 2\<close> and
  \<open>b\<^sub>1 = 3\<close> and \<open>b\<^sub>2 = 2\<close>.
  Then, we can get a sequence of weight reductions on \<open>b\<^sub>2\<close> from \<open>2\<close> to \<open>1.5\<close>,
  \<open>1.25\<close>, \<open>1.125\<close>, etc. with limit \<open>1\<close>.
  All maximal waves in the restricted webs in the sequence are @{term [source] zero_current}, so in
  the limit, we get \<open>k = 0\<close> and \<open>\<epsilon> = 1\<close> for \<open>a\<^sub>2\<close> and \<open>b\<^sub>2\<close>. Now, the
  restricted web for the two is not loose because it contains the wave which assigns 1 to \<open>(a\<^sub>3, b\<^sub>2)\<close>.

  We prove a stronger version which only assumes and ensures on unhinderedness.
\<close>
context countable_bipartite_web begin

lemma web_flow_iff: "web_flow \<Gamma> f \<longleftrightarrow> current \<Gamma> f"
using bipartite_V by(auto simp add: web_flow.simps)

lemma countable_bipartite_web_minus_web:
  assumes f: "current \<Gamma> f"
  shows "countable_bipartite_web (\<Gamma> \<ominus> f)"
using bipartite_V A_vertex bipartite_E disjoint currentD_finite_OUT[OF f] currentD_weight_OUT[OF f] currentD_weight_IN[OF f] currentD_outside_OUT[OF f] currentD_outside_IN[OF f]
by unfold_locales (auto simp add:  weight_outside)

lemma current_plus_current_minus:
  assumes f: "current \<Gamma> f"
  and g: "current (\<Gamma> \<ominus> f) g"
  shows "current \<Gamma> (plus_current f g)" (is "current _ ?fg")
proof
  interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> f" using f by(rule countable_bipartite_web_minus_web)
  show "d_OUT ?fg x \<le> weight \<Gamma> x" for x
    using currentD_weight_OUT[OF g, of x] currentD_OUT[OF g, of x] currentD_finite_OUT[OF f, of x] currentD_OUT[OF f, of x] currentD_outside_IN[OF f, of x] currentD_outside_OUT[OF f, of x] currentD_weight_OUT[OF f, of x]
    by(cases "x \<in> A \<Gamma> \<or> x \<in> B \<Gamma>")(auto simp add: add.commute d_OUT_def nn_integral_add not_vertex ennreal_le_minus_iff split: if_split_asm)
  show "d_IN ?fg x \<le> weight \<Gamma> x" for x
    using currentD_weight_IN[OF g, of x] currentD_IN[OF g, of x] currentD_finite_IN[OF f, of x] currentD_OUT[OF f, of x] currentD_outside_IN[OF f, of x] currentD_outside_OUT[OF f, of x] currentD_weight_IN[OF f, of x]
    by(cases "x \<in> A \<Gamma> \<or> x \<in> B \<Gamma>")(auto simp add: add.commute  d_IN_def nn_integral_add not_vertex ennreal_le_minus_iff split: if_split_asm)
  show "?fg e = 0" if "e \<notin> \<^bold>E" for e using that currentD_outside'[OF f, of e] currentD_outside'[OF g, of e] by(cases e) simp
qed

lemma wave_plus_current_minus:
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and g: "current (\<Gamma> \<ominus> f) g"
  and w': "wave (\<Gamma> \<ominus> f) g"
  shows "wave \<Gamma> (plus_current f g)" (is "wave _ ?fg")
proof
  show fg: "current \<Gamma> ?fg" using f g by(rule current_plus_current_minus)
  show sep: "separating \<Gamma> (TER ?fg)"
  proof
    fix x p y
    assume x: "x \<in> A \<Gamma>" and p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
    from p x y disjoint have py: "p = [y]"
      by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
    with waveD_separating[THEN separatingD, OF w p x y] have "x \<in> TER f \<or> y \<in> TER f" by auto
    thus "(\<exists>z\<in>set p. z \<in> TER ?fg) \<or> x \<in> TER ?fg"
    proof cases
      case right
      with y disjoint have "y \<in> TER ?fg" using currentD_OUT[OF fg y]
        by(auto simp add: SAT.simps SINK.simps d_IN_def nn_integral_add not_le add_increasing2)
      thus ?thesis using py by simp
    next
      case x': left
      from p have "path (\<Gamma> \<ominus> f) x p y" by simp
      from waveD_separating[THEN separatingD, OF w' this] x y py
      have "x \<in> TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g \<or> y \<in> TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g" by auto
      thus ?thesis
      proof cases
        case left
        hence "x \<in> TER ?fg" using x x'
          by(auto simp add: SAT.simps SINK.simps d_OUT_def nn_integral_add)
        thus ?thesis ..
      next
        case right
        hence "y \<in> TER ?fg" using disjoint y currentD_OUT[OF fg y] currentD_OUT[OF f y] currentD_finite_IN[OF f, of y]
          by(auto simp add: add.commute SINK.simps SAT.simps d_IN_def nn_integral_add ennreal_minus_le_iff split: if_split_asm)
        with py show ?thesis by auto
      qed
    qed
  qed
qed

lemma minus_plus_current:
  assumes f: "current \<Gamma> f"
  and g: "current (\<Gamma> \<ominus> f) g"
  shows "\<Gamma> \<ominus> plus_current f g = \<Gamma> \<ominus> f \<ominus> g" (is "?lhs = ?rhs")
proof(rule web.equality)
  have "weight ?lhs x = weight ?rhs x" for x
    using currentD_weight_IN[OF f, of x] currentD_weight_IN[OF g, of x]
    by (auto simp add: d_IN_def d_OUT_def nn_integral_add diff_add_eq_diff_diff_swap_ennreal add_increasing2 diff_add_assoc2_ennreal add.assoc)
  thus "weight ?lhs = weight ?rhs" ..
qed simp_all

lemma unhindered_minus_web:
  assumes unhindered: "\<not> hindered \<Gamma>"
  and f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  shows "\<not> hindered (\<Gamma> \<ominus> f)"
proof
  assume "hindered (\<Gamma> \<ominus> f)"
  then obtain g where g: "current (\<Gamma> \<ominus> f) g"
    and w': "wave (\<Gamma> \<ominus> f) g"
    and hind: "hindrance (\<Gamma> \<ominus> f) g" by cases
  let ?fg = "plus_current f g"
  have fg: "current \<Gamma> ?fg" using f g by(rule current_plus_current_minus)
  moreover have "wave \<Gamma> ?fg" using f w g w' by(rule wave_plus_current_minus)
  moreover from hind obtain a where a: "a \<in> A \<Gamma>" and n\<E>: "a \<notin> \<E>\<^bsub>\<Gamma> \<ominus> f\<^esub> (TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g)"
    and wa: "d_OUT g a < weight (\<Gamma> \<ominus> f) a" by cases auto
  from a have "hindrance \<Gamma> ?fg"
  proof
    show "a \<notin> \<E> (TER ?fg)"
    proof
      assume \<E>: "a \<in> \<E> (TER ?fg)"
      then obtain p y where p: "path \<Gamma> a p y" and y: "y \<in> B \<Gamma>"
        and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER ?fg)" by(rule \<E>_E_RF) blast
      from p a y disjoint have py: "p = [y]"
        by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
      from bypass[of y] py have "y \<notin> TER ?fg" by(auto intro: roofed_greaterI)
      with currentD_OUT[OF fg y] have "y \<notin> SAT \<Gamma> ?fg" by(auto simp add: SINK.simps)
      hence "y \<notin> SAT (\<Gamma> \<ominus> f) g" using y currentD_OUT[OF f y] currentD_finite_IN[OF f, of y]
        by(auto simp add: SAT.simps d_IN_def nn_integral_add ennreal_minus_le_iff add.commute)
      hence "essential (\<Gamma> \<ominus> f) (B (\<Gamma> \<ominus> f)) (TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g) a" using p py y
        by(auto intro!: essentialI)
      moreover from \<E> a have "a \<in> TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g"
        by(auto simp add: SAT.A SINK_plus_current)
      ultimately have "a \<in> \<E>\<^bsub>\<Gamma> \<ominus> f\<^esub> (TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g)" by blast
      thus False using n\<E> by contradiction
    qed
    show "d_OUT ?fg a < weight \<Gamma> a" using a wa currentD_finite_OUT[OF f, of a]
      by(simp add: d_OUT_def less_diff_eq_ennreal less_top add.commute nn_integral_add)
  qed
  ultimately have "hindered \<Gamma>" by(blast intro: hindered.intros)
  with unhindered show False by contradiction
qed

lemma loose_minus_web:
  assumes unhindered: "\<not> hindered \<Gamma>"
  and f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and maximal: "\<And>w. \<lbrakk> current \<Gamma> w; wave \<Gamma> w; f \<le> w \<rbrakk> \<Longrightarrow> f = w"
  shows "loose (\<Gamma> \<ominus> f)" (is "loose ?\<Gamma>")
proof
  fix g
  assume g: "current ?\<Gamma> g" and w': "wave ?\<Gamma> g"
  let ?g = "plus_current f g"
  from f g have "current \<Gamma> ?g" by(rule current_plus_current_minus)
  moreover from f w g w' have "wave \<Gamma> ?g" by(rule wave_plus_current_minus)
  moreover have "f \<le> ?g" by(clarsimp simp add: le_fun_def)
  ultimately have eq: "f = ?g" by(rule maximal)
  have "g e = 0" for e
  proof(cases e)
    case (Pair x y)
    have "f e \<le> d_OUT f x" unfolding d_OUT_def Pair by(rule nn_integral_ge_point) simp
    also have "\<dots> \<le> weight \<Gamma> x" by(rule currentD_weight_OUT[OF f])
    also have "\<dots> < \<top>" by(simp add: less_top[symmetric])
    finally show "g e = 0" using Pair eq[THEN fun_cong, of e]
      by(cases "f e" "g e" rule: ennreal2_cases)(simp_all add: fun_eq_iff)
  qed
  thus "g = (\<lambda>_. 0)" by(simp add: fun_eq_iff)
next
  show "\<not> hindrance ?\<Gamma> zero_current" using unhindered
  proof(rule contrapos_nn)
    assume "hindrance ?\<Gamma> zero_current"
    then obtain x where a: "x \<in> A ?\<Gamma>" and \<E>: "x \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> zero_current)"
      and weight: "d_OUT zero_current x < weight ?\<Gamma> x" by cases
    have "hindrance \<Gamma> f"
    proof
      show a': "x \<in> A \<Gamma>" using a by simp
      with weight show "d_OUT f x < weight \<Gamma> x"
        by(simp add: less_diff_eq_ennreal less_top[symmetric] currentD_finite_OUT[OF f])
      show "x \<notin> \<E> (TER f)"
      proof
        assume "x \<in> \<E> (TER f)"
        then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
          and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER f)" by(rule \<E>_E_RF) auto
        from p a' y disjoint have py: "p = [y]"
          by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
        hence "y \<notin> (TER f)" using bypass[of y] by(auto intro: roofed_greaterI)
        hence "weight ?\<Gamma> y > 0" using currentD_OUT[OF f y] disjoint y
          by(auto simp add: SINK.simps SAT.simps diff_gr0_ennreal)
        hence "y \<notin> TER\<^bsub>?\<Gamma>\<^esub> zero_current" using y disjoint by(auto)
        hence "essential ?\<Gamma> (B ?\<Gamma>) (TER\<^bsub>?\<Gamma>\<^esub> zero_current) x" using p y py by(auto intro!: essentialI)
        with a have "x \<in> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> zero_current)" by simp
        with \<E> show False by contradiction
      qed
    qed
    thus "hindered \<Gamma>" using f w ..
  qed
qed

lemma weight_minus_web:
  assumes f: "current \<Gamma> f"
  shows "weight (\<Gamma> \<ominus> f) x = (if x \<in> A \<Gamma> then weight \<Gamma> x - d_OUT f x else weight \<Gamma> x - d_IN f x)"
proof(cases "x \<in> B \<Gamma>")
  case True
  with currentD_OUT[OF f True] disjoint show ?thesis by auto
next
  case False
  hence "d_IN f x = 0" "d_OUT f x = 0" if "x \<notin> A \<Gamma>"
    using currentD_outside_OUT[OF f, of x] currentD_outside_IN[OF f, of x] bipartite_V that by auto
  then show ?thesis by simp
qed


lemma (in -) separating_minus_web [simp]: "separating_gen (G \<ominus> f) = separating_gen G"
by(simp add: separating_gen.simps fun_eq_iff)

lemma current_minus:
  assumes f: "current \<Gamma> f"
  and g: "current \<Gamma> g"
  and le: "\<And>e. g e \<le> f e"
  shows "current (\<Gamma> \<ominus> g) (f - g)"
proof -
  interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> g" using g by(rule countable_bipartite_web_minus_web)
  note [simp del] = minus_web_sel(2)
    and [simp] = weight_minus_web[OF g]
  show ?thesis
  proof
    show "d_OUT (f - g) x \<le> weight (\<Gamma> \<ominus> g) x" for x unfolding fun_diff_def
      using currentD_weight_OUT[OF f, of x] currentD_weight_IN[OF g, of x]
      by(subst d_OUT_diff)(simp_all add: le currentD_finite_OUT[OF g] currentD_OUT'[OF f] currentD_OUT'[OF g] ennreal_minus_mono)
    show "d_IN (f - g) x \<le> weight (\<Gamma> \<ominus> g) x" for x unfolding fun_diff_def
      using currentD_weight_IN[OF f, of x] currentD_weight_OUT[OF g, of x]
      by(subst d_IN_diff)(simp_all add: le currentD_finite_IN[OF g] currentD_IN[OF f] currentD_IN[OF g] ennreal_minus_mono)
    show "(f - g) e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Gamma> \<ominus> g\<^esub>" for e using that currentD_outside'[OF f] currentD_outside'[OF g] by simp
  qed
qed

lemma
  assumes w: "wave \<Gamma> f"
  and g: "current \<Gamma> g"
  and le: "\<And>e. g e \<le> f e"
  shows wave_minus: "wave (\<Gamma> \<ominus> g) (f - g)"
  and TER_minus: "TER f \<subseteq> TER\<^bsub>\<Gamma> \<ominus> g\<^esub> (f - g)"
proof
  have "x \<in> SINK f \<Longrightarrow> x \<in> SINK (f - g)" for x using d_OUT_mono[of g _ f, OF le, of x]
    by(auto simp add: SINK.simps fun_diff_def d_OUT_diff le currentD_finite_OUT[OF g])
  moreover have "x \<in> SAT \<Gamma> f \<Longrightarrow> x \<in> SAT (\<Gamma> \<ominus> g) (f - g)" for x
    by(auto simp add: SAT.simps currentD_OUT'[OF g] fun_diff_def d_IN_diff le currentD_finite_IN[OF g] ennreal_minus_mono)
  ultimately show TER: "TER f \<subseteq> TER\<^bsub>\<Gamma> \<ominus> g\<^esub> (f - g)" by(auto)

  from w have "separating \<Gamma> (TER f)" by(rule waveD_separating)
  thus "separating (\<Gamma> \<ominus> g) (TER\<^bsub>\<Gamma> \<ominus> g\<^esub> (f - g))" using TER by(simp add: separating_weakening)

  fix x
  assume "x \<notin> RF\<^bsub>\<Gamma> \<ominus> g\<^esub> (TER\<^bsub>\<Gamma> \<ominus> g\<^esub> (f - g))"
  hence "x \<notin> RF (TER f)" using TER by(auto intro: in_roofed_mono)
  hence "d_OUT f x = 0" by(rule waveD_OUT[OF w])
  moreover have "0 \<le> f e" for e using le[of e] by simp
  ultimately show "d_OUT (f - g) x = 0" unfolding d_OUT_def
    by(simp add: nn_integral_0_iff emeasure_count_space_eq_0)
qed

lemma (in -) essential_minus_web [simp]: "essential (\<Gamma> \<ominus> f) = essential \<Gamma>"
by(simp add: essential_def fun_eq_iff)

lemma (in -) RF_in_essential: fixes B shows "essential \<Gamma> B S x \<Longrightarrow> x \<in> roofed_gen \<Gamma> B S \<longleftrightarrow> x \<in> S"
by(auto intro: roofed_greaterI elim!: essentialE_RF dest: roofedD)

lemma (in -) d_OUT_fun_upd:
  assumes "f (x, y) \<noteq> \<top>" "f (x, y) \<ge> 0" "k \<noteq> \<top>" "k \<ge> 0"
  shows "d_OUT (f((x, y) := k)) x' = (if x = x' then d_OUT f x - f (x, y) + k else d_OUT f x')"
  (is "?lhs = ?rhs")
proof(cases "x = x'")
  case True
  have "?lhs = (\<Sum>\<^sup>+ y'. f (x, y') + k * indicator {y} y') - (\<Sum>\<^sup>+ y'. f (x, y') * indicator {y} y')"
    unfolding d_OUT_def using assms True
    by(subst nn_integral_diff[symmetric])
      (auto intro!: nn_integral_cong simp add: AE_count_space split: split_indicator)
  also have "(\<Sum>\<^sup>+ y'. f (x, y') + k * indicator {y} y') = d_OUT f x + (\<Sum>\<^sup>+ y'. k * indicator {y} y')"
    unfolding d_OUT_def using assms
    by(subst nn_integral_add[symmetric])
      (auto intro!: nn_integral_cong split: split_indicator)
  also have "\<dots> - (\<Sum>\<^sup>+ y'. f (x, y') * indicator {y} y') = ?rhs" using True assms
    by(subst diff_add_assoc2_ennreal[symmetric])(auto simp add: d_OUT_def intro!: nn_integral_ge_point)
  finally show ?thesis .
qed(simp add: d_OUT_def)

lemma unhindered_saturate1: \<comment> \<open>Lemma 6.10\<close>
  assumes unhindered: "\<not> hindered \<Gamma>"
  and a: "a \<in> A \<Gamma>"
  shows "\<exists>f. current \<Gamma> f \<and> d_OUT f a = weight \<Gamma> a \<and> \<not> hindered (\<Gamma> \<ominus> f)"
proof -
  from a A_vertex have a_vertex: "vertex \<Gamma> a" by auto
  from unhindered have "\<not> hindrance \<Gamma> zero_current" by(auto intro!: hindered.intros simp add: )
  then have a_\<E>: "a \<in> \<E> (A \<Gamma>)" if "weight \<Gamma> a > 0"
  proof(rule contrapos_np)
    assume "a \<notin> \<E> (A \<Gamma>)"
    with a have "\<not> essential \<Gamma> (B \<Gamma>) (A \<Gamma>) a" by simp
    hence "\<not> essential \<Gamma> (B \<Gamma>) (A \<Gamma> \<union> {x. weight \<Gamma> x \<le> 0}) a"
      by(rule contrapos_nn)(erule essential_mono; simp)
    with a that show "hindrance \<Gamma> zero_current" by(auto intro: hindrance)
  qed

  define F where "F = (\<lambda>(\<epsilon>, h :: 'v current). plus_current \<epsilon> h)"
  have F_simps: "F (\<epsilon>, h) = plus_current \<epsilon> h" for \<epsilon> h by(simp add: F_def)
  define Fld where "Fld = {(\<epsilon>, h).
     current \<Gamma> \<epsilon> \<and> (\<forall>x. x \<noteq> a \<longrightarrow> d_OUT \<epsilon> x = 0) \<and>
     current (\<Gamma> \<ominus> \<epsilon>) h \<and> wave (\<Gamma> \<ominus> \<epsilon>) h \<and>
     \<not> hindered (\<Gamma> \<ominus> F (\<epsilon>, h))}"
  define leq where "leq = restrict_rel Fld {(f, f'). f \<le> f'}"
  have Fld: "Field leq = Fld" by(auto simp add: leq_def)
  have F_I [intro?]: "(\<epsilon>, h) \<in> Field leq"
    if "current \<Gamma> \<epsilon>" and "\<And>x. x \<noteq> a \<Longrightarrow> d_OUT \<epsilon> x = 0"
    and "current (\<Gamma> \<ominus> \<epsilon>) h" and "wave (\<Gamma> \<ominus> \<epsilon>) h"
    and "\<not> hindered (\<Gamma> \<ominus> F (\<epsilon>, h))"
    for \<epsilon> h using that by(simp add: Fld Fld_def)
  have \<epsilon>_curr: "current \<Gamma> \<epsilon>" if "(\<epsilon>, h) \<in> Field leq" for \<epsilon> h using that by(simp add: Fld Fld_def)
  have OUT_\<epsilon>: "\<And>x. x \<noteq> a \<Longrightarrow> d_OUT \<epsilon> x = 0" if "(\<epsilon>, h) \<in> Field leq" for \<epsilon> h using that by(simp add: Fld Fld_def)
  have h: "current (\<Gamma> \<ominus> \<epsilon>) h" if "(\<epsilon>, h) \<in> Field leq" for \<epsilon> h using that by(simp add: Fld Fld_def)
  have h_w: "wave (\<Gamma> \<ominus> \<epsilon>) h" if "(\<epsilon>, h) \<in> Field leq" for \<epsilon> h using that by(simp add: Fld Fld_def)
  have unhindered': "\<not> hindered (\<Gamma> \<ominus> F \<epsilon>h)" if "\<epsilon>h \<in> Field leq" for \<epsilon>h using that by(simp add: Fld Fld_def split: prod.split_asm)
  have f: "current \<Gamma> (F \<epsilon>h)" if "\<epsilon>h \<in> Field leq" for \<epsilon>h using \<epsilon>_curr h that
    by(cases \<epsilon>h)(simp add: F_simps current_plus_current_minus)
  have out_\<epsilon>: "\<epsilon> (x, y) = 0" if "(\<epsilon>, h) \<in> Field leq" "x \<noteq> a" for \<epsilon> h x y
  proof(rule antisym)
    have "\<epsilon> (x, y) \<le> d_OUT \<epsilon> x" unfolding d_OUT_def by(rule nn_integral_ge_point) simp
    with OUT_\<epsilon>[OF that] show "\<epsilon> (x, y) \<le> 0" by simp
  qed simp
  have IN_\<epsilon>: "d_IN \<epsilon> x = \<epsilon> (a, x)" if "(\<epsilon>, h) \<in> Field leq" for \<epsilon> h x
  proof(rule trans)
    show "d_IN \<epsilon> x = (\<Sum>\<^sup>+ y. \<epsilon> (y, x) * indicator {a} y)" unfolding d_IN_def
      by(rule nn_integral_cong)(simp add: out_\<epsilon>[OF that] split: split_indicator)
  qed(simp add: max_def \<epsilon>_curr[OF that])
  have leqI: "((\<epsilon>, h), (\<epsilon>', h')) \<in> leq" if "\<epsilon> \<le> \<epsilon>'" "h \<le> h'" "(\<epsilon>, h) \<in> Field leq" "(\<epsilon>', h') \<in> Field leq" for \<epsilon> h \<epsilon>' h'
    using that unfolding Fld by(simp add: leq_def in_restrict_rel_iff)

  have chain_Field: "Sup M \<in> Field leq" if M: "M \<in> Chains leq" and nempty: "M \<noteq> {}" for M
    unfolding Sup_prod_def
  proof
    from nempty obtain \<epsilon> h where in_M: "(\<epsilon>, h) \<in> M" by auto
    with M have Field: "(\<epsilon>, h) \<in> Field leq" by(rule Chains_FieldD)

    from M have chain: "Complete_Partial_Order.chain (\<lambda>\<epsilon> \<epsilon>'. (\<epsilon>, \<epsilon>') \<in> leq) M"
      by(intro Chains_into_chain) simp
    hence chain': "Complete_Partial_Order.chain (\<le>) M"
      by(auto simp add: chain_def leq_def in_restrict_rel_iff)
    hence chain1: "Complete_Partial_Order.chain (\<le>) (fst ` M)"
      and chain2: "Complete_Partial_Order.chain (\<le>) (snd ` M)"
      by(rule chain_imageI; auto)+

    have outside1: "Sup (fst ` M) (x, y) = 0" if "\<not> edge \<Gamma> x y" for x y using that
      by(auto intro!: SUP_eq_const simp add: nempty dest!: Chains_FieldD[OF M] \<epsilon>_curr currentD_outside)
    then have "support_flow (Sup (fst ` M)) \<subseteq> \<^bold>E" by(auto elim!: support_flow.cases intro: ccontr)
    hence supp_flow1: "countable (support_flow (Sup (fst ` M)))" by(rule countable_subset) simp

    show SM1: "current \<Gamma> (Sup (fst ` M))"
      by(rule current_Sup[OF chain1 _ _ supp_flow1])(auto dest: Chains_FieldD[OF M, THEN \<epsilon>_curr] simp add: nempty)
    show OUT1_na: "d_OUT (Sup (fst ` M)) x = 0" if "x \<noteq> a" for x using that
      by(subst d_OUT_Sup[OF chain1 _ supp_flow1])(auto simp add: nempty intro!: SUP_eq_const dest: Chains_FieldD[OF M, THEN OUT_\<epsilon>])

    interpret SM1: countable_bipartite_web "\<Gamma> \<ominus> Sup (fst ` M)"
      using SM1 by(rule countable_bipartite_web_minus_web)

    let ?h = "Sup (snd ` M)"
    have outside2: "?h (x, y) = 0" if "\<not> edge \<Gamma> x y" for x y using that
      by(auto intro!: SUP_eq_const simp add: nempty dest!: Chains_FieldD[OF M] h currentD_outside)
    then have "support_flow ?h \<subseteq> \<^bold>E" by(auto elim!: support_flow.cases intro: ccontr)
    hence supp_flow2: "countable (support_flow ?h)" by(rule countable_subset) simp

    have OUT1: "d_OUT (Sup (fst ` M)) x = (SUP (\<epsilon>, h)\<in>M. d_OUT \<epsilon> x)" for x
      by (subst d_OUT_Sup [OF chain1 _ supp_flow1])
        (simp_all add: nempty split_beta image_comp)
    have OUT1': "d_OUT (Sup (fst ` M)) x = (if x = a then SUP (\<epsilon>, h)\<in>M. d_OUT \<epsilon> a else 0)" for x
      unfolding OUT1 by(auto intro!: SUP_eq_const simp add: nempty OUT_\<epsilon> dest!: Chains_FieldD[OF M])
    have OUT1_le: "(\<Squnion>\<epsilon>h\<in>M. d_OUT (fst \<epsilon>h) x) \<le> weight \<Gamma> x" for x
      using currentD_weight_OUT[OF SM1, of x] OUT1[of x] by(simp add: split_beta)
    have OUT1_nonneg: "0 \<le> (\<Squnion>\<epsilon>h\<in>M. d_OUT (fst \<epsilon>h) x)" for x using in_M by(rule SUP_upper2)(simp add: )
    have IN1: "d_IN (Sup (fst ` M)) x = (SUP (\<epsilon>, h)\<in>M. d_IN \<epsilon> x)" for x
      by (subst d_IN_Sup [OF chain1 _ supp_flow1])
        (simp_all add: nempty split_beta image_comp)
    have IN1_le: "(\<Squnion>\<epsilon>h\<in>M. d_IN (fst \<epsilon>h) x) \<le> weight \<Gamma> x" for x
      using currentD_weight_IN[OF SM1, of x] IN1[of x] by(simp add: split_beta)
    have IN1_nonneg: "0 \<le> (\<Squnion>\<epsilon>h\<in>M. d_IN (fst \<epsilon>h) x)" for x using in_M by(rule SUP_upper2) simp
    have IN1': "d_IN (Sup (fst ` M)) x = (SUP (\<epsilon>, h)\<in>M. \<epsilon> (a, x))" for x
      unfolding IN1 by(rule SUP_cong[OF refl])(auto dest!: Chains_FieldD[OF M] IN_\<epsilon>)

    have directed: "\<exists>\<epsilon>k''\<in>M. F (snd \<epsilon>k) + F (fst \<epsilon>k') \<le> F (snd \<epsilon>k'') + F (fst \<epsilon>k'')"
      if mono: "\<And>f g. (\<And>z. f z \<le> g z) \<Longrightarrow> F f \<le> F g" "\<epsilon>k \<in> M" "\<epsilon>k' \<in> M"
      for \<epsilon>k \<epsilon>k' and F :: "_ \<Rightarrow> ennreal"
      using chainD[OF chain that(2-3)]
    proof cases
      case left
      hence "snd \<epsilon>k \<le> snd \<epsilon>k'" by(simp add: leq_def less_eq_prod_def in_restrict_rel_iff)
      hence "F (snd \<epsilon>k) + F (fst \<epsilon>k') \<le> F (snd \<epsilon>k') + F (fst \<epsilon>k')"
        by(intro add_right_mono mono)(clarsimp simp add: le_fun_def)
      with that show ?thesis by blast
    next
      case right
      hence "fst \<epsilon>k' \<le> fst \<epsilon>k" by(simp add: leq_def less_eq_prod_def in_restrict_rel_iff)
      hence "F (snd \<epsilon>k) + F (fst \<epsilon>k') \<le> F (snd \<epsilon>k) + F (fst \<epsilon>k)"
        by(intro add_left_mono mono)(clarsimp simp add: le_fun_def)
      with that show ?thesis by blast
    qed
    have directed_OUT: "\<exists>\<epsilon>k''\<in>M. d_OUT (snd \<epsilon>k) x + d_OUT (fst \<epsilon>k') x \<le> d_OUT (snd \<epsilon>k'') x + d_OUT (fst \<epsilon>k'') x"
      if "\<epsilon>k \<in> M" "\<epsilon>k' \<in> M" for x \<epsilon>k \<epsilon>k' by(rule directed; rule d_OUT_mono that)
    have directed_IN: "\<exists>\<epsilon>k''\<in>M. d_IN (snd \<epsilon>k) x + d_IN (fst \<epsilon>k') x \<le> d_IN (snd \<epsilon>k'') x + d_IN (fst \<epsilon>k'') x"
      if "\<epsilon>k \<in> M" "\<epsilon>k' \<in> M" for x \<epsilon>k \<epsilon>k' by(rule directed; rule d_IN_mono that)

    let ?\<Gamma> = "\<Gamma> \<ominus> Sup (fst ` M)"

    have hM2: "current ?\<Gamma> h" if \<epsilon>h: "(\<epsilon>, h) \<in> M" for \<epsilon> h
    proof
      from \<epsilon>h have Field: "(\<epsilon>, h) \<in> Field leq" by(rule Chains_FieldD[OF M])
      then have H: "current (\<Gamma> \<ominus> \<epsilon>) h" and \<epsilon>_curr': "current \<Gamma> \<epsilon>" by(rule h \<epsilon>_curr)+
      from \<epsilon>_curr' interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> \<epsilon>" by(rule countable_bipartite_web_minus_web)

      fix x
      have "d_OUT h x \<le> d_OUT ?h x" using \<epsilon>h by(intro d_OUT_mono)(auto intro: SUP_upper2)
      also have OUT: "\<dots> = (SUP h\<in>snd ` M. d_OUT h x)" using chain2 _ supp_flow2
        by(rule d_OUT_Sup)(simp_all add: nempty)
      also have "\<dots> = \<dots> + (SUP \<epsilon>\<in>fst ` M. d_OUT \<epsilon> x) - (SUP \<epsilon>\<in>fst ` M. d_OUT \<epsilon> x)"
        using OUT1_le[of x]
        by (intro ennreal_add_diff_cancel_right[symmetric] neq_top_trans[OF weight_finite, of _ x])
          (simp add: image_comp)
      also have "\<dots> = (SUP (\<epsilon>, k)\<in>M. d_OUT k x + d_OUT \<epsilon> x) - (SUP \<epsilon>\<in>fst ` M. d_OUT \<epsilon> x)" unfolding split_def
        by (subst SUP_add_directed_ennreal[OF directed_OUT])
          (simp_all add: image_comp)
      also have "(SUP (\<epsilon>, k)\<in>M. d_OUT k x + d_OUT \<epsilon> x) \<le> weight \<Gamma> x"
        apply(clarsimp dest!: Chains_FieldD[OF M] intro!: SUP_least)
        subgoal premises that for \<epsilon> h
          using currentD_weight_OUT[OF h[OF that], of x] currentD_weight_OUT[OF \<epsilon>_curr[OF that], of x]
             countable_bipartite_web_minus_web[OF \<epsilon>_curr, THEN countable_bipartite_web.currentD_OUT', OF that h[OF that], where x=x]
          by (auto simp add: ennreal_le_minus_iff split: if_split_asm)
        done
      also have "(SUP \<epsilon>\<in>fst ` M. d_OUT \<epsilon> x) = d_OUT (Sup (fst ` M)) x" using OUT1
        by (simp add: split_beta image_comp)
      finally show "d_OUT h x \<le> weight ?\<Gamma> x"
        using \<Gamma>.currentD_OUT'[OF h[OF Field], of x] currentD_weight_IN[OF SM1, of x] by(auto simp add: ennreal_minus_mono)

      have "d_IN h x \<le> d_IN ?h x" using \<epsilon>h by(intro d_IN_mono)(auto intro: SUP_upper2)
      also have IN: "\<dots> = (SUP h\<in>snd ` M. d_IN h x)" using chain2 _ supp_flow2
        by(rule d_IN_Sup)(simp_all add: nempty)
      also have "\<dots> = \<dots> + (SUP \<epsilon>\<in>fst ` M. d_IN \<epsilon> x) - (SUP \<epsilon>\<in>fst ` M. d_IN \<epsilon> x)"
        using IN1_le[of x]
        by (intro ennreal_add_diff_cancel_right [symmetric] neq_top_trans [OF weight_finite, of _ x])
          (simp add: image_comp)
      also have "\<dots> = (SUP (\<epsilon>, k)\<in>M. d_IN k x + d_IN \<epsilon> x) - (SUP \<epsilon>\<in>fst ` M. d_IN \<epsilon> x)" unfolding split_def
        by (subst SUP_add_directed_ennreal [OF directed_IN])
          (simp_all add: image_comp)
      also have "(SUP (\<epsilon>, k)\<in>M. d_IN k x + d_IN \<epsilon> x) \<le> weight \<Gamma> x"
        apply(clarsimp dest!: Chains_FieldD[OF M] intro!: SUP_least)
        subgoal premises that for \<epsilon> h
          using currentD_weight_OUT[OF h, OF that, where x=x] currentD_weight_IN[OF h, OF that, where x=x]
            countable_bipartite_web_minus_web[OF \<epsilon>_curr, THEN countable_bipartite_web.currentD_OUT', OF that h[OF that], where x=x]
            currentD_OUT'[OF \<epsilon>_curr, OF that, where x=x] currentD_IN[OF \<epsilon>_curr, OF that, of x] currentD_weight_IN[OF \<epsilon>_curr, OF that, where x=x]
          by (auto simp add: ennreal_le_minus_iff image_comp
                     split: if_split_asm intro: add_increasing2 order_trans [rotated])
        done
      also have "(SUP \<epsilon>\<in>fst ` M. d_IN \<epsilon> x) = d_IN (Sup (fst ` M)) x"
        using IN1 by (simp add: split_beta image_comp)
      finally show "d_IN h x \<le> weight ?\<Gamma> x"
        using currentD_IN[OF h[OF Field], of x] currentD_weight_OUT[OF SM1, of x]
        by(auto simp add: ennreal_minus_mono)
          (auto simp add: ennreal_le_minus_iff add_increasing2)
      show "h e = 0" if "e \<notin> \<^bold>E\<^bsub>?\<Gamma>\<^esub>" for e using currentD_outside'[OF H, of e] that by simp
    qed

    from nempty have "snd ` M \<noteq> {}" by simp
    from chain2 this _ supp_flow2 show current: "current ?\<Gamma> ?h"
      by(rule current_Sup)(clarify; rule hM2; simp)

    have wM: "wave ?\<Gamma> h" if "(\<epsilon>, h) \<in> M" for \<epsilon> h
    proof
      let ?\<Gamma>' = "\<Gamma> \<ominus> \<epsilon>"
      have subset: "TER\<^bsub>?\<Gamma>'\<^esub> h \<subseteq> TER\<^bsub>?\<Gamma>\<^esub> h"
        using currentD_OUT'[OF SM1] currentD_OUT'[OF \<epsilon>_curr[OF Chains_FieldD[OF M that]]] that
        by(auto 4 7 elim!: SAT.cases intro: SAT.intros elim!: order_trans[rotated] intro: ennreal_minus_mono d_IN_mono intro!: SUP_upper2 split: if_split_asm)

      from h_w[OF Chains_FieldD[OF M], OF that] have "separating ?\<Gamma>' (TER\<^bsub>?\<Gamma>'\<^esub> h)" by(rule waveD_separating)
      then show "separating ?\<Gamma> (TER\<^bsub>?\<Gamma>\<^esub> h)" using subset by(auto intro: separating_weakening)
    qed(rule hM2[OF that])
    show wave: "wave ?\<Gamma> ?h" using chain2 \<open>snd ` M \<noteq> {}\<close> _ supp_flow2
      by(rule wave_lub)(clarify; rule wM; simp)

    define f where "f = F (Sup (fst ` M), Sup (snd ` M))"
    have supp_flow: "countable (support_flow f)"
      using supp_flow1 supp_flow2 support_flow_plus_current[of "Sup (fst ` M)" ?h]
      unfolding f_def F_simps by(blast intro: countable_subset)
    have f_alt: "f = Sup ((\<lambda>(\<epsilon>, h). plus_current \<epsilon> h) ` M)"
      apply (simp add: fun_eq_iff split_def f_def nempty F_def image_comp)
      apply (subst (1 2) add.commute)
      apply (subst SUP_add_directed_ennreal)
      apply (rule directed)
      apply (auto dest!: Chains_FieldD [OF M])
      done
    have f_curr: "current \<Gamma> f" unfolding f_def F_simps using SM1 current by(rule current_plus_current_minus)
    have IN_f: "d_IN f x = d_IN (Sup (fst ` M)) x + d_IN (Sup (snd ` M)) x" for x
      unfolding f_def F_simps plus_current_def
      by(rule d_IN_add SM1 current)+
    have OUT_f: "d_OUT f x = d_OUT (Sup (fst ` M)) x + d_OUT (Sup (snd ` M)) x" for x
      unfolding f_def F_simps plus_current_def
      by(rule d_OUT_add SM1 current)+

    show "\<not> hindered (\<Gamma> \<ominus> f)" (is "\<not> hindered ?\<Omega>") \<comment> \<open>Assertion 6.11\<close>
    proof
      assume hindered: "hindered ?\<Omega>"
      then obtain g where g: "current ?\<Omega> g" and g_w: "wave ?\<Omega> g" and hindrance: "hindrance ?\<Omega> g" by cases
      from hindrance obtain z where z: "z \<in> A \<Gamma>" and z\<E>: "z \<notin> \<E>\<^bsub>?\<Omega>\<^esub> (TER\<^bsub>?\<Omega>\<^esub> g)"
        and OUT_z: "d_OUT g z < weight ?\<Omega> z" by cases auto
      define \<delta> where "\<delta> = weight ?\<Omega> z - d_OUT g z"
      have \<delta>_pos: "\<delta> > 0" using OUT_z by(simp add: \<delta>_def diff_gr0_ennreal del: minus_web_sel)
      then have \<delta>_finite[simp]: "\<delta> \<noteq> \<top>" using z
        by(simp_all add: \<delta>_def)

      have "\<exists>(\<epsilon>, h) \<in> M. d_OUT f a < d_OUT (plus_current \<epsilon> h) a + \<delta>"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence greater: "d_OUT (plus_current \<epsilon> h) a + \<delta> \<le> d_OUT f a" if "(\<epsilon>, h) \<in> M" for \<epsilon> h using that by auto

        have chain'': "Complete_Partial_Order.chain (\<le>) ((\<lambda>(\<epsilon>, h). plus_current \<epsilon> h) ` M)"
          using chain' by(rule chain_imageI)(auto simp add: le_fun_def add_mono)

        have "d_OUT f a + 0 < d_OUT f a + \<delta>"
          using currentD_finite_OUT[OF f_curr, of a] by (simp add: \<delta>_pos)
        also have "d_OUT f a + \<delta> = (SUP (\<epsilon>, h)\<in>M. d_OUT (plus_current \<epsilon> h) a) + \<delta>"
          using chain'' nempty supp_flow
          unfolding f_alt by (subst d_OUT_Sup)
            (simp_all add: plus_current_def [abs_def] split_def image_comp)
        also have "\<dots> \<le> d_OUT f a"
          unfolding ennreal_SUP_add_left[symmetric, OF nempty]
        proof(rule SUP_least, clarify)
          show "d_OUT (plus_current \<epsilon> h) a + \<delta> \<le> d_OUT f a" if "(\<epsilon>, h) \<in> M" for \<epsilon> h
            using greater[OF that] currentD_finite_OUT[OF Chains_FieldD[OF M that, THEN f], of a]
            by(auto simp add: ennreal_le_minus_iff add.commute F_def)
        qed
        finally show False by simp
      qed
      then obtain \<epsilon> h where hM: "(\<epsilon>, h) \<in> M" and close: "d_OUT f a < d_OUT (plus_current \<epsilon> h) a + \<delta>" by blast
      have Field: "(\<epsilon>, h) \<in> Field leq" using hM by(rule Chains_FieldD[OF M])
      then have \<epsilon>: "current \<Gamma> \<epsilon>"
        and unhindered_h: "\<not> hindered (\<Gamma> \<ominus> F (\<epsilon>, h))"
        and h_curr: "current (\<Gamma> \<ominus> \<epsilon>) h"
        and h_w: "wave (\<Gamma> \<ominus> \<epsilon>) h"
        and OUT_\<epsilon>: "x \<noteq> a \<Longrightarrow> d_OUT \<epsilon> x = 0" for x
        by(rule \<epsilon>_curr OUT_\<epsilon> h h_w unhindered')+
      let ?\<epsilon>h = "plus_current \<epsilon> h"
      have \<epsilon>h_curr: "current \<Gamma> ?\<epsilon>h" using Field unfolding F_simps[symmetric] by(rule f)

      interpret h: countable_bipartite_web "\<Gamma> \<ominus> \<epsilon>" using \<epsilon> by(rule countable_bipartite_web_minus_web)
      interpret \<epsilon>h: countable_bipartite_web "\<Gamma> \<ominus> ?\<epsilon>h" using \<epsilon>h_curr by(rule countable_bipartite_web_minus_web)
      note [simp del] = minus_web_sel(2)
        and [simp] = weight_minus_web[OF \<epsilon>h_curr] weight_minus_web[OF SM1, simplified]

      define k where "k e = Sup (fst ` M) e - \<epsilon> e" for e
      have k_simps: "k (x, y) = Sup (fst ` M) (x, y) - \<epsilon> (x, y)" for x y by(simp add: k_def)
      have k_alt: "k (x, y) = (if x = a \<and> edge \<Gamma> x y then Sup (fst ` M) (a, y) - \<epsilon> (a, y) else 0)" for x y
        by (cases "x = a")
          (auto simp add: k_simps out_\<epsilon> [OF Field] currentD_outside [OF \<epsilon>] image_comp
           intro!: SUP_eq_const [OF nempty] dest!: Chains_FieldD [OF M]
           intro: currentD_outside [OF \<epsilon>_curr] out_\<epsilon>)
      have OUT_k: "d_OUT k x = (if x = a then d_OUT (Sup (fst ` M)) a - d_OUT \<epsilon> a else 0)" for x
      proof -
        have "d_OUT k x = (if x = a then (\<Sum>\<^sup>+ y. Sup (fst ` M) (a, y) - \<epsilon> (a, y)) else 0)"
          using currentD_outside[OF SM1] currentD_outside[OF \<epsilon>]
          by(auto simp add: k_alt d_OUT_def intro!: nn_integral_cong)
        also have "(\<Sum>\<^sup>+ y. Sup (fst ` M) (a, y) - \<epsilon> (a, y)) = d_OUT (Sup (fst `M)) a - d_OUT \<epsilon> a"
          using currentD_finite_OUT[OF \<epsilon>, of a] hM unfolding d_OUT_def
          by(subst nn_integral_diff[symmetric])(auto simp add: AE_count_space intro!: SUP_upper2)
        finally show ?thesis .
      qed
      have IN_k: "d_IN k y = (if edge \<Gamma> a y then Sup (fst ` M) (a, y) - \<epsilon> (a, y) else 0)" for y
      proof -
        have "d_IN k y = (\<Sum>\<^sup>+ x. (if edge \<Gamma> x y then Sup (fst ` M) (a, y) - \<epsilon> (a, y) else 0) * indicator {a} x)"
          unfolding d_IN_def by(rule nn_integral_cong)(auto simp add: k_alt outgoing_def split: split_indicator)
        also have "\<dots> = (if edge \<Gamma> a y then Sup (fst ` M) (a, y) - \<epsilon> (a, y) else 0)" using hM
          by(auto simp add: max_def intro!: SUP_upper2)
        finally show ?thesis .
      qed

      have OUT_\<epsilon>h: "d_OUT ?\<epsilon>h x = d_OUT \<epsilon> x + d_OUT h x" for x
        unfolding plus_current_def by(rule d_OUT_add)+
      have IN_\<epsilon>h: "d_IN ?\<epsilon>h x = d_IN \<epsilon> x + d_IN h x" for x
        unfolding plus_current_def by(rule d_IN_add)+

      have OUT1_le': "d_OUT (Sup (fst`M)) x \<le> weight \<Gamma> x" for x
        using OUT1_le[of x] unfolding OUT1 by (simp add: split_beta')

      have k: "current (\<Gamma> \<ominus> ?\<epsilon>h) k"
      proof
        fix x
        show "d_OUT k x \<le> weight (\<Gamma> \<ominus> ?\<epsilon>h) x"
          using a OUT1_na[of x] currentD_weight_OUT[OF hM2[OF hM], of x] currentD_weight_IN[OF \<epsilon>h_curr, of x]
            currentD_weight_IN[OF \<epsilon>, of x] OUT1_le'[of x]
          apply(auto simp add: diff_add_eq_diff_diff_swap_ennreal diff_add_assoc2_ennreal[symmetric]
                               OUT_k OUT_\<epsilon> OUT_\<epsilon>h IN_\<epsilon>h currentD_OUT'[OF \<epsilon>] IN_\<epsilon>[OF Field] h.currentD_OUT'[OF h_curr])
          apply(subst diff_diff_commute_ennreal)
          apply(intro ennreal_minus_mono)
          apply(auto simp add: ennreal_le_minus_iff ac_simps less_imp_le OUT1)
          done

        have *: "(\<Squnion>xa\<in>M. fst xa (a, x)) \<le> d_IN (Sup (fst`M)) x"
          unfolding IN1 by (intro SUP_subset_mono) (auto simp: split_beta' d_IN_ge_point)
        also have "\<dots> \<le> weight \<Gamma> x"
          using IN1_le[of x] IN1 by (simp add: split_beta')
        finally show "d_IN k x \<le> weight (\<Gamma> \<ominus> ?\<epsilon>h) x"
          using currentD_weight_IN[OF \<epsilon>h_curr, of x] currentD_weight_OUT[OF \<epsilon>h_curr, of x]
            currentD_weight_IN[OF hM2[OF hM], of x] IN_\<epsilon>[OF Field, of x] *
          apply (auto simp add: IN_k outgoing_def IN_\<epsilon>h IN_\<epsilon> A_in diff_add_eq_diff_diff_swap_ennreal)
          apply (subst diff_diff_commute_ennreal)
          apply (intro ennreal_minus_mono[OF _ order_refl])
          apply (auto simp add: ennreal_le_minus_iff ac_simps image_comp intro: order_trans add_mono)
          done
        show "k e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Gamma> \<ominus> ?\<epsilon>h\<^esub>" for e
          using that by (cases e) (simp add: k_alt)
      qed

      define q where "q = (\<Sum>\<^sup>+ y\<in>B (\<Gamma> \<ominus> ?\<epsilon>h). d_IN k y - d_OUT k y)"
      have q_alt: "q = (\<Sum>\<^sup>+ y\<in>- A (\<Gamma> \<ominus> ?\<epsilon>h). d_IN k y - d_OUT k y)" using disjoint
        by(auto simp add: q_def nn_integral_count_space_indicator currentD_outside_OUT[OF k] currentD_outside_IN[OF k] not_vertex split: split_indicator intro!: nn_integral_cong)
      have q_simps: "q = d_OUT (Sup (fst ` M)) a - d_OUT \<epsilon> a"
      proof -
        have "q = (\<Sum>\<^sup>+ y. d_IN k y)" using a IN1 OUT1 OUT1_na unfolding q_alt
          by(auto simp add: nn_integral_count_space_indicator OUT_k IN_\<epsilon>[OF Field] OUT_\<epsilon> currentD_outside[OF \<epsilon>] outgoing_def no_loop A_in IN_k intro!: nn_integral_cong split: split_indicator)
        also have "\<dots> = d_OUT (Sup (fst ` M)) a - d_OUT \<epsilon> a" using currentD_finite_OUT[OF \<epsilon>, of a] hM currentD_outside[OF SM1] currentD_outside[OF \<epsilon>]
          by(subst d_OUT_diff[symmetric])(auto simp add: d_OUT_def IN_k intro!: SUP_upper2 nn_integral_cong)
        finally show ?thesis .
      qed
      have q_finite: "q \<noteq> \<top>" using currentD_finite_OUT[OF SM1, of a]
        by(simp add: q_simps)
      have q_nonneg: "0 \<le> q" using hM by(auto simp add: q_simps intro!: d_OUT_mono SUP_upper2)
      have q_less_\<delta>: "q < \<delta>" using close
        unfolding q_simps \<delta>_def OUT_\<epsilon>h OUT_f
      proof -
        let ?F = "d_OUT (Sup (fst`M)) a" and ?S = "d_OUT (Sup (snd`M)) a"
          and ?\<epsilon> = "d_OUT \<epsilon> a" and ?h = "d_OUT h a" and ?w = "weight (\<Gamma> \<ominus> f) z - d_OUT g z"
        have "?F + ?h \<le> ?F + ?S"
          using hM by (auto intro!: add_mono d_OUT_mono SUP_upper2)
        also assume "?F + ?S < ?\<epsilon> + ?h + ?w"
        finally have "?h + ?F < ?h + (?w + ?\<epsilon>)"
          by (simp add: ac_simps)
        then show "?F - ?\<epsilon> < ?w"
          using currentD_finite_OUT[OF \<epsilon>, of a] hM unfolding ennreal_add_left_cancel_less
          by (subst minus_less_iff_ennreal) (auto intro!: d_OUT_mono SUP_upper2 simp: less_top)
      qed

      define g' where "g' = plus_current g (Sup (snd ` M) - h)"
      have g'_simps: "g' e = g e + Sup (snd ` M) e - h e" for e
        using hM by(auto simp add: g'_def intro!: add_diff_eq_ennreal intro: SUP_upper2)
      have OUT_g': "d_OUT g' x = d_OUT g x + (d_OUT (Sup (snd ` M)) x - d_OUT h x)" for x
        unfolding g'_simps[abs_def] using \<epsilon>h.currentD_finite_OUT[OF k] hM h.currentD_finite_OUT[OF h_curr] hM
        apply(subst d_OUT_diff)
         apply(auto simp add: add_diff_eq_ennreal[symmetric] k_simps intro: add_increasing intro!: SUP_upper2)
        apply(subst d_OUT_add)
         apply(auto simp add: add_diff_eq_ennreal[symmetric] k_simps intro: add_increasing intro!:)
        apply(simp add: add_diff_eq_ennreal SUP_apply[abs_def])
        apply(auto simp add: g'_def image_comp intro!: add_diff_eq_ennreal[symmetric] d_OUT_mono intro: SUP_upper2)
        done
      have IN_g': "d_IN g' x = d_IN g x + (d_IN (Sup (snd ` M)) x - d_IN h x)" for x
        unfolding g'_simps[abs_def] using \<epsilon>h.currentD_finite_IN[OF k] hM h.currentD_finite_IN[OF h_curr] hM
        apply(subst d_IN_diff)
         apply(auto simp add: add_diff_eq_ennreal[symmetric] k_simps intro: add_increasing intro!: SUP_upper2)
        apply(subst d_IN_add)
         apply(auto simp add: add_diff_eq_ennreal[symmetric] k_simps intro: add_increasing intro!: SUP_upper)
        apply(auto simp add: g'_def SUP_apply[abs_def] image_comp intro!: add_diff_eq_ennreal[symmetric] d_IN_mono intro: SUP_upper2)
        done

      have h': "current (\<Gamma> \<ominus> Sup (fst ` M)) h" using hM by(rule hM2)

      let ?\<Gamma> = "\<Gamma> \<ominus> ?\<epsilon>h \<ominus> k"
      interpret \<Gamma>: web ?\<Gamma> using k by(rule \<epsilon>h.web_minus_web)
      note [simp] = \<epsilon>h.weight_minus_web[OF k] h.weight_minus_web[OF h_curr]
        weight_minus_web[OF f_curr] SM1.weight_minus_web[OF h', simplified]

      interpret \<Omega>: countable_bipartite_web "\<Gamma> \<ominus> f" using f_curr by(rule countable_bipartite_web_minus_web)

      have *: "\<Gamma> \<ominus> f = \<Gamma> \<ominus> Sup (fst ` M) \<ominus> Sup (snd ` M)" unfolding f_def F_simps
        using SM1 current by(rule minus_plus_current)
      have OUT_\<epsilon>k: "d_OUT (Sup (fst ` M)) x = d_OUT \<epsilon> x + d_OUT k x" for x
        using OUT1'[of x] currentD_finite_OUT[OF \<epsilon>] hM
        by(auto simp add: OUT_k OUT_\<epsilon> add_diff_self_ennreal SUP_upper2)
      have IN_\<epsilon>k: "d_IN (Sup (fst ` M)) x = d_IN \<epsilon> x + d_IN k x" for x
        using IN1'[of x] currentD_finite_IN[OF \<epsilon>] currentD_outside[OF \<epsilon>] currentD_outside[OF \<epsilon>_curr]
        by(auto simp add: IN_k IN_\<epsilon>[OF Field] add_diff_self_ennreal split_beta nempty image_comp
                dest!: Chains_FieldD[OF M] intro!: SUP_eq_const intro: SUP_upper2[OF hM])
      have **: "?\<Gamma> = \<Gamma> \<ominus> Sup (fst ` M) \<ominus> h"
      proof(rule web.equality)
        show "weight ?\<Gamma> = weight (\<Gamma> \<ominus> Sup (fst ` M) \<ominus> h)"
          using OUT_\<epsilon>k OUT_\<epsilon>h currentD_finite_OUT[OF \<epsilon>] IN_\<epsilon>k IN_\<epsilon>h currentD_finite_IN[OF \<epsilon>]
          by(auto simp add: diff_add_eq_diff_diff_swap_ennreal diff_diff_commute_ennreal)
      qed simp_all
      have g'_alt: "g' = plus_current (Sup (snd ` M)) g - h"
        by(simp add: fun_eq_iff g'_simps add_diff_eq_ennreal add.commute)

      have "current (\<Gamma> \<ominus> Sup (fst ` M)) (plus_current (Sup (snd ` M)) g)" using current g unfolding *
        by(rule SM1.current_plus_current_minus)
      hence g': "current ?\<Gamma> g'" unfolding * ** g'_alt using hM2[OF hM]
        by(rule SM1.current_minus)(auto intro!: add_increasing2 SUP_upper2 hM)

      have "wave (\<Gamma> \<ominus> Sup (fst ` M)) (plus_current (Sup (snd ` M)) g)" using current wave g g_w
        unfolding * by(rule SM1.wave_plus_current_minus)
      then have g'_w: "wave ?\<Gamma> g'" unfolding * ** g'_alt using hM2[OF hM]
        by(rule SM1.wave_minus)(auto intro!: add_increasing2 SUP_upper2 hM)

      have "hindrance_by ?\<Gamma> g' q"
      proof
        show "z \<in> A ?\<Gamma>" using z by simp
        show "z \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> g')"
        proof
          assume "z \<in> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> g')"
          hence OUT_z: "d_OUT g' z = 0"
            and ess: "essential ?\<Gamma> (B \<Gamma>) (TER\<^bsub>?\<Gamma>\<^esub> g') z" by(simp_all add: SINK.simps)
          from ess obtain p y where p: "path \<Gamma> z p y" and y: "y \<in> B \<Gamma>"
            and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF (TER\<^bsub>?\<Gamma>\<^esub> g')" by(rule essentialE_RF) auto
          from y have y': "y \<notin> A \<Gamma>" using disjoint by blast
          from p z y obtain py: "p = [y]" and edge: "edge \<Gamma> z y" using disjoint
            by(cases)(auto 4 3 elim: rtrancl_path.cases dest: bipartite_E)
          hence yRF: "y \<notin> RF (TER\<^bsub>?\<Gamma>\<^esub> g')" using bypass[of y] by(auto)
          with wave_not_RF_IN_zero[OF g' g'_w, of y] have IN_g'_y: "d_IN g' y = 0"
            by(auto intro: roofed_greaterI)
          with yRF y y' have w_y: "weight ?\<Gamma> y > 0" using currentD_OUT[OF g', of y]
            by(auto simp add: RF_in_B currentD_SAT[OF g'] SINK.simps zero_less_iff_neq_zero)
          have "y \<notin> SAT (\<Gamma> \<ominus> f) g"
          proof
            assume "y \<in> SAT (\<Gamma> \<ominus> f) g"
            with y disjoint have IN_g_y: "d_IN g y = weight (\<Gamma> \<ominus> f) y" by(auto simp add: currentD_SAT[OF g])
            have "0 < weight \<Gamma> y - d_IN (\<Squnion>x\<in>M. fst x) y - d_IN h y"
              using y' w_y unfolding ** by auto
            have "d_IN g' y > 0"
              using y' w_y hM unfolding **
              apply(simp add: IN_g' IN_f IN_g_y diff_add_eq_diff_diff_swap_ennreal)
              apply(subst add_diff_eq_ennreal)
              apply(auto intro!: SUP_upper2 d_IN_mono simp: diff_add_self_ennreal diff_gt_0_iff_gt_ennreal)
              done
            with IN_g'_y show False by simp
          qed
          then have "y \<notin> TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g" by simp
          with p y py have "essential \<Gamma> (B \<Gamma>) (TER\<^bsub>\<Gamma> \<ominus> f\<^esub> g) z" by(auto intro: essentialI)
          moreover with z waveD_separating[OF g_w, THEN separating_RF_A] have "z \<in> \<E>\<^bsub>?\<Omega>\<^esub> (TER\<^bsub>?\<Omega>\<^esub> g)"
            by(auto simp add: RF_in_essential)
          with z\<E> show False by contradiction
        qed
        have "\<delta> \<le> weight ?\<Gamma> z - d_OUT g' z"
          unfolding ** OUT_g' using z
          apply (simp add: \<delta>_def OUT_f diff_add_eq_diff_diff_swap_ennreal)
          apply (subst (5) diff_diff_commute_ennreal)
          apply (rule ennreal_minus_mono[OF _ order_refl])
          apply (auto simp add: ac_simps diff_add_eq_diff_diff_swap_ennreal[symmetric] add_diff_self_ennreal image_comp
                      intro!: ennreal_minus_mono[OF order_refl] SUP_upper2[OF hM] d_OUT_mono)
          done
        then show q_z: "q < weight ?\<Gamma> z - d_OUT g' z" using q_less_\<delta> by simp
        then show "d_OUT g' z < weight ?\<Gamma> z" using q_nonneg z
          by(auto simp add: less_diff_eq_ennreal less_top[symmetric] ac_simps \<Gamma>.currentD_finite_OUT[OF g']
                  intro: le_less_trans[rotated] add_increasing)
      qed
      then have hindered_by: "hindered_by (\<Gamma> \<ominus> ?\<epsilon>h \<ominus> k) q" using g' g'_w by(rule hindered_by.intros)
      then have "hindered (\<Gamma> \<ominus> ?\<epsilon>h)" using q_finite unfolding q_def by -(rule \<epsilon>h.hindered_reduce_current[OF k])
      with unhindered_h show False unfolding F_simps by contradiction
    qed
  qed

  define sat where "sat =
    (\<lambda>(\<epsilon>, h).
      let
        f = F (\<epsilon>, h);
        k = SOME k. current (\<Gamma> \<ominus> f) k \<and> wave (\<Gamma> \<ominus> f) k \<and> (\<forall>k'. current (\<Gamma> \<ominus> f) k' \<and> wave (\<Gamma> \<ominus> f) k' \<and> k \<le> k' \<longrightarrow> k = k')
      in
        if d_OUT (plus_current f k) a < weight \<Gamma> a then
          let
            \<Omega> = \<Gamma> \<ominus> f \<ominus> k;
            y = SOME y. y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Omega>\<^esub> a \<and> weight \<Omega> y > 0;
            \<delta> = SOME \<delta>. \<delta> > 0 \<and> \<delta> < enn2real (min (weight \<Omega> a) (weight \<Omega> y)) \<and> \<not> hindered (reduce_weight \<Omega> y \<delta>)
          in
            (plus_current \<epsilon> (zero_current((a, y) := \<delta>)), plus_current h k)
        else (\<epsilon>, h))"

  have zero: "(zero_current, zero_current) \<in> Field leq"
    by(rule F_I)(simp_all add: unhindered  F_def)

  have a_TER: "a \<in> TER\<^bsub>\<Gamma> \<ominus> F \<epsilon>h\<^esub> k"
    if that: "\<epsilon>h \<in> Field leq"
    and k: "current (\<Gamma> \<ominus> F \<epsilon>h) k" and k_w: "wave (\<Gamma> \<ominus> F \<epsilon>h) k"
    and less: "d_OUT (plus_current (F \<epsilon>h) k) a < weight \<Gamma> a" for \<epsilon>h k
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence \<E>: "a \<notin> \<E>\<^bsub>\<Gamma> \<ominus> F \<epsilon>h\<^esub> (TER\<^bsub>\<Gamma> \<ominus> F \<epsilon>h\<^esub> k)" by auto
    from that have f: "current \<Gamma> (F \<epsilon>h)" and unhindered: "\<not> hindered (\<Gamma> \<ominus> F \<epsilon>h)"
       by(cases \<epsilon>h; simp add: f unhindered'; fail)+

    from less have "d_OUT k a < weight (\<Gamma> \<ominus> F \<epsilon>h) a" using a currentD_finite_OUT[OF f, of a]
      by(simp add: d_OUT_def nn_integral_add less_diff_eq_ennreal add.commute less_top[symmetric])
    with _ \<E> have "hindrance (\<Gamma> \<ominus> F \<epsilon>h) k" by(rule hindrance)(simp add: a)
    then have "hindered (\<Gamma> \<ominus> F \<epsilon>h)" using k k_w ..
    with unhindered show False by contradiction
  qed

  note minus_web_sel(2)[simp del]

  let ?P_y = "\<lambda>\<epsilon>h k y. y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Gamma> \<ominus> F \<epsilon>h \<ominus> k\<^esub> a \<and> weight (\<Gamma> \<ominus> F \<epsilon>h \<ominus> k) y > 0"
  have Ex_y: "Ex (?P_y \<epsilon>h k)"
    if that: "\<epsilon>h \<in> Field leq"
    and k: "current (\<Gamma> \<ominus> F \<epsilon>h) k" and k_w: "wave (\<Gamma> \<ominus> F \<epsilon>h) k"
    and less: "d_OUT (plus_current (F \<epsilon>h) k) a < weight \<Gamma> a" for \<epsilon>h k
  proof(rule ccontr)
    let ?\<Omega> = "\<Gamma> \<ominus> F \<epsilon>h \<ominus> k"
    assume *: "\<not> ?thesis"

    interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> F \<epsilon>h" using f[OF that] by(rule countable_bipartite_web_minus_web)
    note [simp] = weight_minus_web[OF f[OF that]] \<Gamma>.weight_minus_web[OF k]

    have "hindrance ?\<Omega> zero_current"
    proof
      show "a \<in> A ?\<Omega>" using a by simp
      show "a \<notin> \<E>\<^bsub>?\<Omega>\<^esub> (TER\<^bsub>?\<Omega>\<^esub> zero_current)" (is "a \<notin> \<E>\<^bsub>_\<^esub> ?TER")
      proof
        assume "a \<in> \<E>\<^bsub>?\<Omega>\<^esub> ?TER"
        then obtain p y where p: "path ?\<Omega> a p y" and y: "y \<in> B ?\<Omega>"
          and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> RF\<^bsub>?\<Omega>\<^esub> ?TER" by(rule \<E>_E_RF)(auto)
        from a p y disjoint have Nil: "p \<noteq> []" by(auto simp add: rtrancl_path_simps)
        hence "edge ?\<Omega> a (p ! 0)" "p ! 0 \<notin> RF\<^bsub>?\<Omega>\<^esub> ?TER"
          using rtrancl_path_nth[OF p, of 0] bypass by auto
        with * show False by(auto simp add: not_less outgoing_def intro: roofed_greaterI)
      qed

      have "d_OUT (plus_current (F \<epsilon>h) k) x = d_OUT (F \<epsilon>h) x + d_OUT k x" for x
        by(simp add: d_OUT_def nn_integral_add)
      then show "d_OUT zero_current a < weight ?\<Omega> a" using less a_TER[OF that k k_w less] a
        by(simp add: SINK.simps diff_gr0_ennreal)
    qed
    hence "hindered ?\<Omega>"
      by(auto intro!: hindered.intros order_trans[OF currentD_weight_OUT[OF k]] order_trans[OF currentD_weight_IN[OF k]])
    moreover have "\<not> hindered ?\<Omega>" using unhindered'[OF that] k k_w by(rule \<Gamma>.unhindered_minus_web)
    ultimately show False by contradiction
  qed

  have increasing: "\<epsilon>h \<le> sat \<epsilon>h \<and> sat \<epsilon>h \<in> Field leq" if "\<epsilon>h \<in> Field leq" for \<epsilon>h
  proof(cases \<epsilon>h)
    case (Pair \<epsilon> h)
    with that have that: "(\<epsilon>, h) \<in> Field leq" by simp
    have f: "current \<Gamma> (F (\<epsilon>, h))" and unhindered: "\<not> hindered (\<Gamma> \<ominus> F (\<epsilon>, h))"
      and \<epsilon>: "current \<Gamma> \<epsilon>"
      and h: "current (\<Gamma> \<ominus> \<epsilon>) h" and h_w: "wave (\<Gamma> \<ominus> \<epsilon>) h" and OUT_\<epsilon>: "x \<noteq> a \<Longrightarrow> d_OUT \<epsilon> x = 0" for x
      using that by(rule f unhindered' \<epsilon>_curr OUT_\<epsilon> h h_w)+
    interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> F (\<epsilon>, h)" using f by(rule countable_bipartite_web_minus_web)
    note [simp] = weight_minus_web[OF f]

    let ?P_k = "\<lambda>k. current (\<Gamma> \<ominus> F (\<epsilon>, h)) k \<and> wave (\<Gamma> \<ominus> F (\<epsilon>, h)) k \<and> (\<forall>k'. current (\<Gamma> \<ominus> F (\<epsilon>, h)) k' \<and> wave (\<Gamma> \<ominus> F (\<epsilon>, h)) k' \<and> k \<le> k' \<longrightarrow> k = k')"
    define k where "k = Eps ?P_k"
    have "Ex ?P_k" by(intro ex_maximal_wave)(simp_all)
    hence "?P_k k" unfolding k_def by(rule someI_ex)
    hence k: "current (\<Gamma> \<ominus> F (\<epsilon>, h)) k" and k_w: "wave (\<Gamma> \<ominus> F (\<epsilon>, h)) k"
      and maximal: "\<And>k'. \<lbrakk> current (\<Gamma> \<ominus> F (\<epsilon>, h)) k'; wave (\<Gamma> \<ominus> F (\<epsilon>, h)) k'; k \<le> k' \<rbrakk> \<Longrightarrow> k = k'" by blast+
    note [simp] = \<Gamma>.weight_minus_web[OF k]

    let ?fk = "plus_current (F (\<epsilon>, h)) k"
    have IN_fk: "d_IN ?fk x = d_IN (F (\<epsilon>, h)) x + d_IN k x" for x
      by(simp add: d_IN_def nn_integral_add)
    have OUT_fk: "d_OUT ?fk x = d_OUT (F (\<epsilon>, h)) x + d_OUT k x" for x
      by(simp add: d_OUT_def nn_integral_add)
    have fk: "current \<Gamma> ?fk" using f k by(rule current_plus_current_minus)

    show ?thesis
    proof(cases "d_OUT ?fk a < weight \<Gamma> a")
      case less: True

      define \<Omega> where "\<Omega> = \<Gamma> \<ominus> F (\<epsilon>, h) \<ominus> k"
      have B_\<Omega> [simp]: "B \<Omega> = B \<Gamma>" by(simp add: \<Omega>_def)

      have loose: "loose \<Omega>" unfolding \<Omega>_def using unhindered k k_w maximal by(rule \<Gamma>.loose_minus_web)
      interpret \<Omega>: countable_bipartite_web \<Omega> using k unfolding \<Omega>_def
        by(rule \<Gamma>.countable_bipartite_web_minus_web)

      have a_\<E>: "a \<in> TER\<^bsub>\<Gamma> \<ominus> F (\<epsilon>, h)\<^esub> k" using that k k_w less by(rule a_TER)
      then have weight_\<Omega>_a: "weight \<Omega> a = weight \<Gamma> a - d_OUT (F (\<epsilon>, h)) a"
        using a disjoint by(auto simp add: roofed_circ_def \<Omega>_def SINK.simps)
      then have weight_a: "0 < weight \<Omega> a" using less a_\<E>
        by(simp add: OUT_fk SINK.simps diff_gr0_ennreal)

      let ?P_y = "\<lambda>y. y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Omega>\<^esub> a \<and> weight \<Omega> y > 0"
      define y where "y = Eps ?P_y"
      have "Ex ?P_y" using that k k_w less unfolding \<Omega>_def by(rule Ex_y)
      hence "?P_y y" unfolding y_def by(rule someI_ex)
      hence y_OUT: "y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Omega>\<^esub> a" and weight_y: "weight \<Omega> y > 0" by blast+
      from y_OUT have y_B: "y \<in> B \<Omega>" by(auto simp add: outgoing_def \<Omega>_def dest: bipartite_E)
      with weight_y have yRF: "y \<notin> RF\<^bsub>\<Gamma> \<ominus> F (\<epsilon>, h)\<^esub> (TER\<^bsub>\<Gamma> \<ominus> F (\<epsilon>, h)\<^esub> k)"
        unfolding \<Omega>_def using currentD_OUT[OF k, of y] disjoint
        by(auto split: if_split_asm simp add: SINK.simps currentD_SAT[OF k] roofed_circ_def RF_in_B \<Gamma>.currentD_finite_IN[OF k])
      hence IN_k_y: "d_IN k y = 0" by(rule wave_not_RF_IN_zero[OF k k_w])

      define bound where "bound = enn2real (min (weight \<Omega> a) (weight \<Omega> y))"
      have bound_pos: "bound > 0" using weight_y weight_a using \<Omega>.weight_finite
        by(cases "weight \<Omega> a" "weight \<Omega> y" rule: ennreal2_cases)
          (simp_all add: bound_def min_def split: if_split_asm)

      let ?P_\<delta> = "\<lambda>\<delta>. \<delta> > 0 \<and> \<delta> < bound \<and> \<not> hindered (reduce_weight \<Omega> y \<delta>)"
      define \<delta> where "\<delta> = Eps ?P_\<delta>"
      let ?\<Omega> = "reduce_weight \<Omega> y \<delta>"

      from \<Omega>.unhinder[OF loose _ weight_y bound_pos] y_B disjoint
      have "Ex ?P_\<delta>" by(auto simp add: \<Omega>_def)
      hence "?P_\<delta> \<delta>" unfolding \<delta>_def by(rule someI_ex)
      hence \<delta>_pos: "0 < \<delta>" and \<delta>_le_bound: "\<delta> < bound" and unhindered': "\<not> hindered ?\<Omega>" by blast+
      from \<delta>_pos have \<delta>_nonneg: "0 \<le> \<delta>" by simp
      from \<delta>_le_bound \<delta>_pos have \<delta>_le_a: "\<delta> < weight \<Omega> a" and \<delta>_le_y: "\<delta> < weight \<Omega> y"
        by(cases "weight \<Omega> a" "weight \<Omega> y" rule: ennreal2_cases;
           simp add: bound_def min_def ennreal_less_iff split: if_split_asm)+

      let ?\<Gamma> = "\<Gamma> \<ominus> ?fk"
      interpret \<Gamma>': countable_bipartite_web ?\<Gamma> by(rule countable_bipartite_web_minus_web fk)+
      note [simp] = weight_minus_web[OF fk]

      let ?g = "zero_current((a, y) := \<delta>)"
      have OUT_g: "d_OUT ?g x = (if x = a then \<delta> else 0)" for x
      proof(rule trans)
        show "d_OUT ?g x = (\<Sum>\<^sup>+ z. (if x = a then \<delta> else 0) * indicator {y} z)" unfolding d_OUT_def
          by(rule nn_integral_cong) simp
        show "\<dots> = (if x = a then \<delta> else 0)" using \<delta>_pos by(simp add: max_def)
      qed
      have IN_g: "d_IN ?g x = (if x = y then \<delta> else 0)" for x
      proof(rule trans)
        show "d_IN ?g x = (\<Sum>\<^sup>+ z. (if x = y then \<delta> else 0) * indicator {a} z)" unfolding d_IN_def
          by(rule nn_integral_cong) simp
        show "\<dots> = (if x = y then \<delta> else 0)" using \<delta>_pos by(simp add: max_def)
      qed

      have g: "current ?\<Gamma> ?g"
      proof
        show "d_OUT ?g x \<le> weight ?\<Gamma> x" for x
        proof(cases "x = a")
          case False
          then show ?thesis using currentD_weight_OUT[OF fk, of x] currentD_weight_IN[OF fk, of x]
            by(auto simp add: OUT_g zero_ennreal_def[symmetric])
        next
          case True
          then show ?thesis using \<delta>_le_a a a_\<E> \<delta>_pos unfolding OUT_g
            by(simp add: OUT_g \<Omega>_def SINK.simps OUT_fk split: if_split_asm)
        qed
        show "d_IN ?g x \<le> weight ?\<Gamma> x" for x
        proof(cases "x = y")
          case False
          then show ?thesis using currentD_weight_OUT[OF fk, of x] currentD_weight_IN[OF fk, of x]
            by(auto simp add: IN_g zero_ennreal_def[symmetric])
        next
          case True
          then show ?thesis using \<delta>_le_y y_B a_\<E> \<delta>_pos currentD_OUT[OF k, of y] IN_k_y
            by(simp add: OUT_g \<Omega>_def SINK.simps OUT_fk IN_fk IN_g split: if_split_asm)
        qed
        show "?g e = 0" if "e \<notin> \<^bold>E\<^bsub>?\<Gamma>\<^esub>" for e using y_OUT that by(auto simp add: \<Omega>_def outgoing_def)
      qed
      interpret \<Gamma>'': web "\<Gamma> \<ominus> ?fk \<ominus> ?g" using g by(rule \<Gamma>'.web_minus_web)

      let ?\<epsilon>' = "plus_current \<epsilon> (zero_current((a, y) := \<delta>))"
      let ?h' = "plus_current h k"
      have F': "F (?\<epsilon>', ?h') = plus_current (plus_current (F (\<epsilon>, h)) k) (zero_current((a, y) := \<delta>))" (is "_ = ?f'")
        by(auto simp add: F_simps fun_eq_iff add_ac)
      have sat: "sat (\<epsilon>, h) = (?\<epsilon>', ?h')" using less
        by(simp add: sat_def k_def \<Omega>_def Let_def y_def bound_def \<delta>_def)

      have le: "(\<epsilon>, h) \<le> (?\<epsilon>', ?h')" using \<delta>_pos
        by(auto simp add: le_fun_def add_increasing2 add_increasing)

      have "current (\<Gamma> \<ominus> \<epsilon>) ((\<lambda>_. 0)((a, y) := ennreal \<delta>))" using g
        by(rule current_weight_mono)(auto simp add: weight_minus_web[OF \<epsilon>] intro!: ennreal_minus_mono d_OUT_mono d_IN_mono, simp_all add: F_def add_increasing2)
      with \<epsilon> have \<epsilon>': "current \<Gamma> ?\<epsilon>'" by(rule current_plus_current_minus)
      moreover have eq_0: "d_OUT ?\<epsilon>' x = 0" if "x \<noteq> a" for x unfolding plus_current_def using that
        by(subst d_OUT_add)(simp_all add: \<delta>_nonneg d_OUT_fun_upd OUT_\<epsilon>)
      moreover
      from \<epsilon>' interpret \<epsilon>': countable_bipartite_web "\<Gamma> \<ominus> ?\<epsilon>'" by(rule countable_bipartite_web_minus_web)
      from \<epsilon> interpret \<epsilon>: countable_bipartite_web "\<Gamma> \<ominus> \<epsilon>" by(rule countable_bipartite_web_minus_web)
      have g': "current (\<Gamma> \<ominus> \<epsilon>) ?g" using g
        apply(rule current_weight_mono)
        apply(auto simp add: weight_minus_web[OF \<epsilon>] intro!: ennreal_minus_mono d_OUT_mono d_IN_mono)
        apply(simp_all add: F_def add_increasing2)
        done
      have k': "current (\<Gamma> \<ominus> \<epsilon> \<ominus> h) k" using k unfolding F_simps minus_plus_current[OF \<epsilon> h] .
      with h have "current (\<Gamma> \<ominus> \<epsilon>) (plus_current h k)" by(rule \<epsilon>.current_plus_current_minus)
      hence "current (\<Gamma> \<ominus> \<epsilon>) (plus_current (plus_current h k) ?g)" using g unfolding minus_plus_current[OF f k]
        unfolding F_simps minus_plus_current[OF \<epsilon> h] \<epsilon>.minus_plus_current[OF h k', symmetric]
        by(rule \<epsilon>.current_plus_current_minus)
      then have "current (\<Gamma> \<ominus> \<epsilon> \<ominus> ?g) (plus_current (plus_current h k) ?g - ?g)" using g'
        by(rule \<epsilon>.current_minus)(auto simp add: add_increasing)
      then have h'': "current (\<Gamma> \<ominus> ?\<epsilon>') ?h'"
        by(rule arg_cong2[where f=current, THEN iffD1, rotated -1])
          (simp_all add: minus_plus_current[OF \<epsilon> g'] fun_eq_iff add_diff_eq_ennreal[symmetric])
      moreover have "wave (\<Gamma> \<ominus> ?\<epsilon>') ?h'"
      proof
        have "separating (\<Gamma> \<ominus> \<epsilon>) (TER\<^bsub>\<Gamma> \<ominus> \<epsilon>\<^esub> (plus_current h k))"
          using k k_w unfolding F_simps minus_plus_current[OF \<epsilon> h]
          by(intro waveD_separating \<epsilon>.wave_plus_current_minus[OF h h_w])
        moreover have "TER\<^bsub>\<Gamma> \<ominus> \<epsilon>\<^esub> (plus_current h k) \<subseteq> TER\<^bsub>\<Gamma> \<ominus> ?\<epsilon>'\<^esub> (plus_current h k)"
          by(auto 4 4 simp add: SAT.simps weight_minus_web[OF \<epsilon>] weight_minus_web[OF \<epsilon>'] split: if_split_asm elim: order_trans[rotated] intro!: ennreal_minus_mono d_IN_mono add_increasing2 \<delta>_nonneg)
        ultimately show sep: "separating (\<Gamma> \<ominus> ?\<epsilon>') (TER\<^bsub>\<Gamma> \<ominus> ?\<epsilon>'\<^esub> ?h')"
          by(simp add: minus_plus_current[OF \<epsilon> g'] separating_weakening)
      qed(rule h'')
      moreover
      have "\<not> hindered (\<Gamma> \<ominus> F (?\<epsilon>', ?h'))" using unhindered'
      proof(rule contrapos_nn)
        assume "hindered (\<Gamma> \<ominus> F (?\<epsilon>', ?h'))"
        thus "hindered ?\<Omega>"
        proof(rule hindered_mono_web[rotated -1])
          show "weight ?\<Omega> z = weight (\<Gamma> \<ominus> F (?\<epsilon>', ?h')) z" if "z \<notin> A (\<Gamma> \<ominus> F (?\<epsilon>', ?h'))" for z
            using that unfolding F'
            apply(cases "z = y")
            apply(simp_all add: \<Omega>_def minus_plus_current[OF fk g] \<Gamma>'.weight_minus_web[OF g] IN_g)
            apply(simp_all add: plus_current_def d_IN_add diff_add_eq_diff_diff_swap_ennreal currentD_finite_IN[OF f])
            done
          have "y \<noteq> a" using y_B a disjoint by auto
          then show "weight (\<Gamma> \<ominus> F (?\<epsilon>', ?h')) z \<le> weight ?\<Omega> z" if "z \<in> A (\<Gamma> \<ominus> F (?\<epsilon>', ?h'))" for z
            using that y_B disjoint \<delta>_nonneg unfolding F'
            apply(cases "z = a")
            apply(simp_all add: \<Omega>_def minus_plus_current[OF fk g] \<Gamma>'.weight_minus_web[OF g] OUT_g)
            apply(auto simp add: plus_current_def d_OUT_add diff_add_eq_diff_diff_swap_ennreal currentD_finite_OUT[OF f])
            done
        qed(simp_all add: \<Omega>_def)
      qed
      ultimately have "(?\<epsilon>', ?h') \<in> Field leq" by-(rule F_I)
      with Pair le sat that show ?thesis by(auto)
    next
      case False
      with currentD_weight_OUT[OF fk, of a] have "d_OUT ?fk a = weight \<Gamma> a" by simp
      have "sat \<epsilon>h = \<epsilon>h" using False Pair by(simp add: sat_def k_def)
      thus ?thesis using that Pair by(auto)
    qed
  qed

  have "bourbaki_witt_fixpoint Sup leq sat" using increasing chain_Field unfolding leq_def
    by(intro bourbaki_witt_fixpoint_restrict_rel)(auto intro: Sup_upper Sup_least)
  then interpret bourbaki_witt_fixpoint Sup leq sat .

  define f where "f = fixp_above (zero_current, zero_current)"
  have Field: "f \<in> Field leq" using fixp_above_Field[OF zero] unfolding f_def .
  then have f: "current \<Gamma> (F f)" and unhindered: "\<not> hindered (\<Gamma> \<ominus> F f)"
    by(cases f; simp add: f unhindered'; fail)+
  interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> F f" using f by(rule countable_bipartite_web_minus_web)
  note [simp] = weight_minus_web[OF f]
  have Field': "(fst f, snd f) \<in> Field leq" using Field by simp

  let ?P_k = "\<lambda>k. current (\<Gamma> \<ominus> F f) k \<and> wave (\<Gamma> \<ominus> F f) k \<and> (\<forall>k'. current (\<Gamma> \<ominus> F f) k' \<and> wave (\<Gamma> \<ominus> F f) k' \<and> k \<le> k' \<longrightarrow> k = k')"
  define k where "k = Eps ?P_k"
  have "Ex ?P_k" by(intro ex_maximal_wave)(simp_all)
  hence "?P_k k" unfolding k_def by(rule someI_ex)
  hence k: "current (\<Gamma> \<ominus> F f) k" and k_w: "wave (\<Gamma> \<ominus> F f) k"
    and maximal: "\<And>k'. \<lbrakk> current (\<Gamma> \<ominus> F f) k'; wave (\<Gamma> \<ominus> F f) k'; k \<le> k' \<rbrakk> \<Longrightarrow> k = k'" by blast+
  note [simp] = \<Gamma>.weight_minus_web[OF k]

  let ?fk = "plus_current (F f) k"
  have IN_fk: "d_IN ?fk x = d_IN (F f) x + d_IN k x" for x
    by(simp add: d_IN_def nn_integral_add)
  have OUT_fk: "d_OUT ?fk x = d_OUT (F f) x + d_OUT k x" for x
    by(simp add: d_OUT_def nn_integral_add)
  have fk: "current \<Gamma> ?fk" using f k by(rule current_plus_current_minus)

  have "d_OUT ?fk a \<ge> weight \<Gamma> a"
  proof(rule ccontr)
    assume "\<not> ?thesis"
    hence less: "d_OUT ?fk a < weight \<Gamma> a" by simp

    define \<Omega> where "\<Omega> = \<Gamma> \<ominus> F f \<ominus> k"
    have B_\<Omega> [simp]: "B \<Omega> = B \<Gamma>" by(simp add: \<Omega>_def)

    have loose: "loose \<Omega>" unfolding \<Omega>_def using unhindered k k_w maximal by(rule \<Gamma>.loose_minus_web)
    interpret \<Omega>: countable_bipartite_web \<Omega> using k unfolding \<Omega>_def
      by(rule \<Gamma>.countable_bipartite_web_minus_web)

    have a_\<E>: "a \<in> TER\<^bsub>\<Gamma> \<ominus> F f\<^esub> k" using Field k k_w less by(rule a_TER)
    then have "weight \<Omega> a = weight \<Gamma> a - d_OUT (F f) a"
      using a disjoint by(auto simp add: roofed_circ_def \<Omega>_def SINK.simps)
    then have weight_a: "0 < weight \<Omega> a" using less a_\<E>
      by(simp add: OUT_fk SINK.simps diff_gr0_ennreal)

    let ?P_y = "\<lambda>y. y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Omega>\<^esub> a \<and> weight \<Omega> y > 0"
    define y where "y = Eps ?P_y"
    have "Ex ?P_y" using Field k k_w less unfolding \<Omega>_def by(rule Ex_y)
    hence "?P_y y" unfolding y_def by(rule someI_ex)
    hence "y \<in> \<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Omega>\<^esub> a" and weight_y: "weight \<Omega> y > 0" by blast+
    then have y_B: "y \<in> B \<Omega>" by(auto simp add: outgoing_def \<Omega>_def dest: bipartite_E)

    define bound where "bound = enn2real (min (weight \<Omega> a) (weight \<Omega> y))"
    have bound_pos: "bound > 0" using weight_y weight_a \<Omega>.weight_finite
      by(cases "weight \<Omega> a" "weight \<Omega> y" rule: ennreal2_cases)
        (simp_all add: bound_def min_def split: if_split_asm)

    let ?P_\<delta> = "\<lambda>\<delta>. \<delta> > 0 \<and> \<delta> < bound \<and> \<not> hindered (reduce_weight \<Omega> y \<delta>)"
    define \<delta> where "\<delta> = Eps ?P_\<delta>"
    from \<Omega>.unhinder[OF loose _ weight_y bound_pos] y_B disjoint have "Ex ?P_\<delta>" by(auto simp add: \<Omega>_def)
    hence "?P_\<delta> \<delta>" unfolding \<delta>_def by(rule someI_ex)
    hence \<delta>_pos: "0 < \<delta>" by blast+

    let ?f' = "(plus_current (fst f) (zero_current((a, y) := \<delta>)), plus_current (snd f) k)"
    have sat: "?f' = sat f" using less by(simp add: sat_def k_def \<Omega>_def Let_def y_def bound_def \<delta>_def split_def)
    also have "\<dots> = f" unfolding f_def using fixp_above_unfold[OF zero] by simp
    finally have "fst ?f' (a, y) = fst f (a, y)" by simp
    hence "\<delta> = 0" using currentD_finite[OF \<epsilon>_curr[OF Field']] \<delta>_pos
      by(cases "fst f (a, y)") simp_all
    with \<delta>_pos show False by simp
  qed

  with currentD_weight_OUT[OF fk, of a] have "d_OUT ?fk a = weight \<Gamma> a" by simp
  moreover have "current \<Gamma> ?fk" using f k by(rule current_plus_current_minus)
  moreover have "\<not> hindered (\<Gamma> \<ominus> ?fk)" unfolding minus_plus_current[OF f k]
    using unhindered k k_w by(rule \<Gamma>.unhindered_minus_web)
  ultimately show ?thesis by blast
qed

end

subsection \<open>Linkability of unhindered bipartite webs\<close>

context countable_bipartite_web begin

theorem unhindered_linkable:
  assumes unhindered: "\<not> hindered \<Gamma>"
  shows "linkable \<Gamma>"
proof(cases "A \<Gamma> = {}")
  case True
  thus ?thesis by(auto intro!: exI[where x="zero_current"] linkage.intros simp add: web_flow_iff )
next
  case nempty: False

  let ?P = "\<lambda>f a f'. current (\<Gamma> \<ominus> f) f' \<and> d_OUT f' a = weight (\<Gamma> \<ominus> f) a \<and> \<not> hindered (\<Gamma> \<ominus> f \<ominus> f')"

  define enum where "enum = from_nat_into (A \<Gamma>)"
  have enum_A: "enum n \<in> A \<Gamma>" for n using from_nat_into[OF nempty, of n] by(simp add: enum_def)
  have vertex_enum [simp]: "vertex \<Gamma> (enum n)" for n using enum_A[of n] A_vertex by blast

  define f where "f = rec_nat zero_current (\<lambda>n f. let f' = SOME f'. ?P f (enum n) f' in plus_current f f')"
  have f_0 [simp]: "f 0 = zero_current" by(simp add: f_def)
  have f_Suc: "f (Suc n) = plus_current (f n) (Eps (?P (f n) (enum n)))" for n by(simp add: f_def)

  have f: "current \<Gamma> (f n)"
    and sat: "\<And>m. m < n \<Longrightarrow> d_OUT (f n) (enum m) = weight \<Gamma> (enum m)"
    and unhindered: "\<not> hindered (\<Gamma> \<ominus> f n)" for n
  proof(induction n)
    case 0
    { case 1 thus ?case by(simp add: ) }
    { case 2 thus ?case by simp }
    { case 3 thus ?case using unhindered by simp }
  next
    case (Suc n)
    interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> f n" using Suc.IH(1) by(rule countable_bipartite_web_minus_web)

    define f' where "f' = Eps (?P (f n) (enum n))"
    have "Ex (?P (f n) (enum n))" using Suc.IH(3) by(rule \<Gamma>.unhindered_saturate1)(simp add: enum_A)
    hence "?P (f n) (enum n) f'" unfolding f'_def by(rule someI_ex)
    hence f': "current (\<Gamma> \<ominus> f n) f'"
      and OUT: "d_OUT f' (enum n) = weight (\<Gamma> \<ominus> f n) (enum n)"
      and unhindered': "\<not> hindered (\<Gamma> \<ominus> f n \<ominus> f')" by blast+
    have f_Suc: "f (Suc n) = plus_current (f n) f'" by(simp add: f'_def f_Suc)
    { case 1 show ?case unfolding f_Suc using Suc.IH(1) f' by(rule current_plus_current_minus) }
    note f'' = this
    { case (2 m)
      have "d_OUT (f (Suc n)) (enum m) \<le> weight \<Gamma> (enum m)" using f'' by(rule currentD_weight_OUT)
      moreover have "weight \<Gamma> (enum m) \<le> d_OUT (f (Suc n)) (enum m)"
      proof(cases "m = n")
        case True
        then show ?thesis unfolding f_Suc using OUT True
          by(simp add: d_OUT_def nn_integral_add enum_A add_diff_self_ennreal less_imp_le)
      next
        case False
        hence "m < n" using 2 by simp
        thus ?thesis using Suc.IH(2)[OF \<open>m < n\<close>] unfolding f_Suc
          by(simp add: d_OUT_def nn_integral_add add_increasing2 )
      qed
      ultimately show ?case by(rule antisym) }
    { case 3 show ?case unfolding f_Suc minus_plus_current[OF Suc.IH(1) f'] by(rule unhindered') }
  qed
  interpret \<Gamma>: countable_bipartite_web "\<Gamma> \<ominus> f n" for n using f by(rule countable_bipartite_web_minus_web)

  have Ex_P: "Ex (?P (f n) (enum n))" for n using unhindered by(rule \<Gamma>.unhindered_saturate1)(simp add: enum_A)
  have f_mono: "f n \<le> f (Suc n)" for n using someI_ex[OF Ex_P, of n]
    by(auto simp add: le_fun_def f_Suc enum_A intro: add_increasing2 dest: )
  hence incseq: "incseq f" by(rule incseq_SucI)
  hence chain: "Complete_Partial_Order.chain (\<le>) (range f)" by(rule incseq_chain_range)

  define g where "g = Sup (range f)"
  have "support_flow g \<subseteq> \<^bold>E"
    by (auto simp add: g_def support_flow.simps currentD_outside [OF f] image_comp elim: contrapos_pp)
  then have countable_g: "countable (support_flow g)" by(rule countable_subset) simp
  with chain _ _ have g: "current \<Gamma> g" unfolding g_def  by(rule current_Sup)(auto simp add: f)
  moreover
  have "d_OUT g x = weight \<Gamma> x" if "x \<in> A \<Gamma>" for x
  proof(rule antisym)
    show "d_OUT g x \<le> weight \<Gamma> x" using g by(rule currentD_weight_OUT)
    have "countable (A \<Gamma>)" using A_vertex by(rule countable_subset) simp
    from that subset_range_from_nat_into[OF this] obtain n where "x = enum n" unfolding enum_def by blast
    with sat[of n "Suc n"] have "d_OUT (f (Suc n)) x \<ge> weight \<Gamma> x" by simp
    then show "weight \<Gamma> x \<le> d_OUT g x" using countable_g unfolding g_def
      by(subst d_OUT_Sup[OF chain])(auto intro: SUP_upper2)
  qed
  ultimately show ?thesis by(auto simp add: web_flow_iff linkage.simps)
qed

end

section \<open>The Max-Flow Min-Cut theorem\<close>

subsection \<open>Reduction to bipartite webs\<close>

definition bipartite_web_of :: "('v, 'more) web_scheme \<Rightarrow> ('v + 'v, 'more) web_scheme"
where
  "bipartite_web_of \<Gamma> =
  \<lparr>edge = \<lambda>uv uv'. case (uv, uv') of (Inl u, Inr v) \<Rightarrow> edge \<Gamma> u v \<or> u = v \<and> u \<in> vertices \<Gamma> \<and> u \<notin> A \<Gamma> \<and> v \<notin> B \<Gamma> | _ \<Rightarrow> False,
   weight = \<lambda>uv. case uv of Inl u \<Rightarrow> if u \<in> B \<Gamma> then 0 else weight \<Gamma> u | Inr u \<Rightarrow> if u \<in> A \<Gamma> then 0 else weight \<Gamma> u,
   A = Inl ` (vertices \<Gamma> - B \<Gamma>),
   B = Inr ` (- A \<Gamma>),
   \<dots> = web.more \<Gamma>\<rparr>"

lemma bipartite_web_of_sel [simp]: fixes \<Gamma> (structure) shows
  "edge (bipartite_web_of \<Gamma>) (Inl u) (Inr v) \<longleftrightarrow> edge \<Gamma> u v \<or> u = v \<and> u \<in> \<^bold>V \<and> u \<notin> A \<Gamma> \<and> v \<notin> B \<Gamma>"
  "edge (bipartite_web_of \<Gamma>) uv (Inl u) \<longleftrightarrow> False"
  "edge (bipartite_web_of \<Gamma>) (Inr v) uv \<longleftrightarrow> False"
  "weight (bipartite_web_of \<Gamma>) (Inl u) = (if u \<in> B \<Gamma> then 0 else weight \<Gamma> u)"
  "weight (bipartite_web_of \<Gamma>) (Inr v) = (if v \<in> A \<Gamma> then 0 else weight \<Gamma> v)"
  "A (bipartite_web_of \<Gamma>) = Inl ` (\<^bold>V - B \<Gamma>)"
  "B (bipartite_web_of \<Gamma>) = Inr ` (- A \<Gamma>)"
by(simp_all add: bipartite_web_of_def split: sum.split)

lemma edge_bipartite_webI1: "edge \<Gamma> u v \<Longrightarrow> edge (bipartite_web_of \<Gamma>) (Inl u) (Inr v)"
by(auto)

lemma edge_bipartite_webI2:
  "\<lbrakk> u \<in> \<^bold>V\<^bsub>\<Gamma>\<^esub>; u \<notin> A \<Gamma>; u \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> edge (bipartite_web_of \<Gamma>) (Inl u) (Inr u)"
by(auto)

lemma edge_bipartite_webE:
  fixes \<Gamma> (structure)
  assumes "edge (bipartite_web_of \<Gamma>) uv uv'"
  obtains u v where "uv = Inl u" "uv' = Inr v" "edge \<Gamma> u v"
    | u where "uv = Inl u" "uv' = Inr u" "u \<in> \<^bold>V" "u \<notin> A \<Gamma>" "u \<notin> B \<Gamma>"
using assms by(cases uv uv' rule: sum.exhaust[case_product sum.exhaust]) auto

lemma E_bipartite_web:
  fixes \<Gamma> (structure) shows
  "\<^bold>E\<^bsub>bipartite_web_of \<Gamma>\<^esub> = (\<lambda>(x, y). (Inl x, Inr y)) ` \<^bold>E \<union> (\<lambda>x. (Inl x, Inr x)) ` (\<^bold>V - A \<Gamma> - B \<Gamma>)"
by(auto elim: edge_bipartite_webE)

context web begin

lemma vertex_bipartite_web [simp]:
  "vertex (bipartite_web_of \<Gamma>) (Inl x) \<longleftrightarrow> vertex \<Gamma> x \<and> x \<notin> B \<Gamma>"
  "vertex (bipartite_web_of \<Gamma>) (Inr x) \<longleftrightarrow> vertex \<Gamma> x \<and> x \<notin> A \<Gamma>"
by(auto 4 4 simp add: vertex_def dest: B_out A_in intro: edge_bipartite_webI1 edge_bipartite_webI2 elim!: edge_bipartite_webE)

definition separating_of_bipartite :: "('v + 'v) set \<Rightarrow> 'v set"
where
  "separating_of_bipartite S =
  (let A_S = Inl -` S; B_S = Inr -` S in (A_S \<inter> B_S) \<union> (A \<Gamma> \<inter> A_S) \<union> (B \<Gamma> \<inter> B_S))"

context
  fixes S :: "('v + 'v) set"
  assumes sep: "separating (bipartite_web_of \<Gamma>) S"
begin

text \<open>Proof of separation follows @{cite Aharoni1983EJC}\<close>

lemma separating_of_bipartite_aux:
  assumes p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>"
  and x: "x \<in> A \<Gamma> \<or> Inr x \<in> S"
  shows "(\<exists>z\<in>set p. z \<in> separating_of_bipartite S) \<or> x \<in> separating_of_bipartite S"
proof(cases "p = []")
  case True
  with p have "x = y" by cases auto
  with y x have "x \<in> separating_of_bipartite S" using disjoint
    by(auto simp add: separating_of_bipartite_def Let_def)
  thus ?thesis ..
next
  case nNil: False
  define inmarked where "inmarked x \<longleftrightarrow> x \<in> A \<Gamma> \<or> Inr x \<in> S" for x
  define outmarked where "outmarked x \<longleftrightarrow> x \<in> B \<Gamma> \<or> Inl x \<in> S" for x
  let ?\<Gamma> = "bipartite_web_of \<Gamma>"
  let ?double = "\<lambda>x. inmarked x \<and> outmarked x"
  define tailmarked where "tailmarked = (\<lambda>(x, y :: 'v). outmarked x)"
  define headmarked where "headmarked = (\<lambda>(x :: 'v, y). inmarked y)"

  have marked_E: "tailmarked e \<or> headmarked e" if "e \<in> \<^bold>E" for e \<comment> \<open>Lemma 1b\<close>
  proof(cases e)
    case (Pair x y)
    with that have "path ?\<Gamma> (Inl x) [Inr y] (Inr y)" by(auto intro!: rtrancl_path.intros)
    from separatingD[OF sep this] that Pair show ?thesis
      by(fastforce simp add: vertex_def inmarked_def outmarked_def tailmarked_def headmarked_def)
  qed

  have "\<exists>z\<in>set (x # p). ?double z" \<comment> \<open>Lemma 2\<close>
  proof -
    have "inmarked ((x # p) ! (i + 1)) \<or> outmarked ((x # p) ! i)" if "i < length p" for i
      using rtrancl_path_nth[OF p that] marked_E[of "((x # p) ! i, p ! i)"] that
      by(auto simp add: tailmarked_def headmarked_def nth_Cons split: nat.split)
    hence "{i. i < length p \<and> inmarked (p ! i)} \<union> {i. i < length (x # butlast p) \<and> outmarked ((x # butlast p) ! i)} = {i. i < length p}"
      (is "?in \<union> ?out = _") using nNil
      by(force simp add: nth_Cons' nth_butlast elim: meta_allE[where x=0] cong del: old.nat.case_cong_weak)
    hence "length p + 2 = card (?in \<union> ?out) + 2" by simp
    also have "\<dots> \<le> (card ?in + 1) + (card ?out + 1)" by(simp add: card_Un_le)
    also have "card ?in = card ((\<lambda>i. Inl (i + 1) :: _ + nat) ` ?in)"
      by(rule card_image[symmetric])(simp add: inj_on_def)
    also have "\<dots> + 1 = card (insert (Inl 0) {Inl (Suc i) :: _ + nat|i. i < length p \<and> inmarked (p ! i)})"
      by(subst card_insert_if)(auto intro!: arg_cong[where f=card])
    also have "\<dots> = card {Inl i :: nat + nat|i. i < length (x # p) \<and> inmarked ((x # p) ! i)}" (is "_ = card ?in")
      using x by(intro arg_cong[where f=card])(auto simp add: nth_Cons inmarked_def split: nat.split_asm)
    also have "card ?out = card ((Inr :: _ \<Rightarrow> nat + _) ` ?out)" by(simp add: card_image)
    also have "\<dots> + 1 = card (insert (Inr (length p)) {Inr i :: nat + _|i. i < length p \<and> outmarked ((x # p) ! i)})"
      using nNil by(subst card_insert_if)(auto intro!: arg_cong[where f=card] simp add: nth_Cons nth_butlast cong: nat.case_cong)
    also have "\<dots> = card {Inr i :: nat + _|i. i < length (x # p) \<and> outmarked ((x # p) ! i)}" (is "_ = card ?out")
      using nNil rtrancl_path_last[OF p nNil] y
      by(intro arg_cong[where f=card])(auto simp add: outmarked_def last_conv_nth)
    also have "card ?in + card ?out = card (?in \<union> ?out)"
      by(rule card_Un_disjoint[symmetric]) auto
    also let ?f = "case_sum id id"
    have "?f ` (?in \<union> ?out) \<subseteq> {i. i < length (x # p)}" by auto
    from card_mono[OF _ this] have "card (?f ` (?in \<union> ?out)) \<le> length p + 1" by simp
    ultimately have "\<not> inj_on ?f (?in \<union> ?out)" by(intro pigeonhole) simp
    then obtain i where "i < length (x # p)" "?double ((x # p) ! i)"
      by(auto simp add: inj_on_def)
    thus ?thesis by(auto simp add: set_conv_nth)
  qed
  moreover have "z \<in> separating_of_bipartite S" if "?double z" for z using that disjoint
    by(auto simp add: separating_of_bipartite_def Let_def inmarked_def outmarked_def)
  ultimately show ?thesis by auto
qed

lemma separating_of_bipartite:
  "separating \<Gamma> (separating_of_bipartite S)"
by(rule separating_gen.intros)(erule (1) separating_of_bipartite_aux; simp)

end

lemma current_bipartite_web_finite:
  assumes f: "current (bipartite_web_of \<Gamma>) f" (is "current ?\<Gamma> _")
  shows "f e \<noteq> \<top>"
proof(cases e)
  case (Pair x y)
  have "f e \<le> d_OUT f x" unfolding Pair d_OUT_def by(rule nn_integral_ge_point) simp
  also have "\<dots> \<le> weight ?\<Gamma> x" by(rule currentD_weight_OUT[OF f])
  also have "\<dots> < \<top>" by(cases x)(simp_all add: less_top[symmetric])
  finally show ?thesis by simp
qed

definition current_of_bipartite :: "('v + 'v) current \<Rightarrow> 'v current"
where "current_of_bipartite f = (\<lambda>(x, y). f (Inl x, Inr y) * indicator \<^bold>E (x, y))"

lemma current_of_bipartite_simps [simp]: "current_of_bipartite f (x, y) = f (Inl x, Inr y) * indicator \<^bold>E (x, y)"
by(simp add: current_of_bipartite_def)

lemma d_OUT_current_of_bipartite:
  assumes f: "current (bipartite_web_of \<Gamma>) f"
  shows "d_OUT (current_of_bipartite f) x = d_OUT f (Inl x) - f (Inl x, Inr x)"
proof -
  have "d_OUT (current_of_bipartite f) x = \<integral>\<^sup>+ y. f (Inl x, y) * indicator \<^bold>E (x, projr y) \<partial>count_space (range Inr)"
    by(simp add: d_OUT_def nn_integral_count_space_reindex)
  also have "\<dots> = d_OUT f (Inl x) - \<integral>\<^sup>+ y. f (Inl x, y) * indicator {Inr x} y \<partial>count_space UNIV" (is "_ = _ - ?rest")
    unfolding d_OUT_def by(subst nn_integral_diff[symmetric])(auto 4 4 simp add: current_bipartite_web_finite[OF f] AE_count_space nn_integral_count_space_indicator no_loop split: split_indicator intro!: nn_integral_cong intro: currentD_outside[OF f] elim: edge_bipartite_webE)
  finally show ?thesis by simp
qed

lemma d_IN_current_of_bipartite:
  assumes f: "current (bipartite_web_of \<Gamma>) f"
  shows "d_IN (current_of_bipartite f) x = d_IN f (Inr x) - f (Inl x, Inr x)"
proof -
  have "d_IN (current_of_bipartite f) x = \<integral>\<^sup>+ y. f (y, Inr x) * indicator \<^bold>E (projl y, x) \<partial>count_space (range Inl)"
    by(simp add: d_IN_def nn_integral_count_space_reindex)
  also have "\<dots> = d_IN f (Inr x) - \<integral>\<^sup>+ y. f (y, Inr x) * indicator {Inl x} y \<partial>count_space UNIV" (is "_ = _ - ?rest")
    unfolding d_IN_def by(subst nn_integral_diff[symmetric])(auto 4 4 simp add: current_bipartite_web_finite[OF f] AE_count_space nn_integral_count_space_indicator no_loop split: split_indicator intro!: nn_integral_cong intro: currentD_outside[OF f] elim: edge_bipartite_webE)
  finally show ?thesis by simp
qed

lemma current_current_of_bipartite: \<comment> \<open>Lemma 6.3\<close>
  assumes f: "current (bipartite_web_of \<Gamma>) f" (is "current ?\<Gamma> _")
  and w: "wave (bipartite_web_of \<Gamma>) f"
  shows "current \<Gamma> (current_of_bipartite f)" (is "current _ ?f")
proof
  fix x
  have "d_OUT ?f x \<le> d_OUT f (Inl x)"
    by(simp add: d_OUT_current_of_bipartite[OF f] diff_le_self_ennreal)
  also have "\<dots> \<le> weight \<Gamma> x"
    using currentD_weight_OUT[OF f, of "Inl x"]
    by(simp split: if_split_asm)
  finally show "d_OUT ?f x \<le> weight \<Gamma> x" .
next
  fix x
  have "d_IN ?f x \<le> d_IN f (Inr x)"
    by(simp add: d_IN_current_of_bipartite[OF f] diff_le_self_ennreal)
  also have "\<dots> \<le> weight \<Gamma> x"
    using currentD_weight_IN[OF f, of "Inr x"]
    by(simp split: if_split_asm)
  finally show "d_IN ?f x \<le> weight \<Gamma> x" .
next
  have OUT: "d_OUT ?f b = 0" if "b \<in> B \<Gamma>" for b using that
    by(auto simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 intro!: currentD_outside[OF f] dest: B_out)
  show "d_OUT ?f x \<le> d_IN ?f x" if A: "x \<notin> A \<Gamma>" for x
  proof(cases "x \<in> B \<Gamma> \<or> x \<notin> \<^bold>V")
    case True
    then show ?thesis
    proof
      assume "x \<in> B \<Gamma>"
      with OUT[OF this] show ?thesis by auto
    next
      assume "x \<notin> \<^bold>V"
      hence "d_OUT ?f x = 0" by(auto simp add: d_OUT_def vertex_def nn_integral_0_iff emeasure_count_space_eq_0 intro!: currentD_outside[OF f])
      thus ?thesis by simp
    qed
  next
    case B [simplified]: False
    have "d_OUT ?f x = d_OUT f (Inl x) - f (Inl x, Inr x)" (is "_ = _ - ?rest")
      by(simp add: d_OUT_current_of_bipartite[OF f])
    also have "d_OUT f (Inl x) \<le> d_IN f (Inr x)"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence *: "d_IN f (Inr x) < d_OUT f (Inl x)" by(simp add: not_less)
      also have "\<dots> \<le> weight \<Gamma> x" using currentD_weight_OUT[OF f, of "Inl x"] B by simp
      finally have "Inr x \<notin> TER\<^bsub>?\<Gamma>\<^esub> f" using A by(auto elim!: SAT.cases)
      moreover have "Inl x \<notin> TER\<^bsub>?\<Gamma>\<^esub> f" using * by(auto simp add: SINK.simps)
      moreover have "path ?\<Gamma> (Inl x) [Inr x] (Inr x)"
        by(rule rtrancl_path.step)(auto intro!: rtrancl_path.base simp add: no_loop A B)
      ultimately show False using waveD_separating[OF w] A B by(auto dest!: separatingD)
    qed
    hence "d_OUT f (Inl x) - ?rest \<le> d_IN f (Inr x) - ?rest" by(rule ennreal_minus_mono) simp
    also have "\<dots> =  d_IN ?f x" by(simp add: d_IN_current_of_bipartite[OF f])
    finally show ?thesis .
  qed
  show "?f e = 0" if "e \<notin> \<^bold>E" for e using that by(cases e)(auto)
qed

lemma TER_current_of_bipartite: \<comment> \<open>Lemma 6.3\<close>
  assumes f: "current (bipartite_web_of \<Gamma>) f" (is "current ?\<Gamma> _")
  and w: "wave (bipartite_web_of \<Gamma>) f"
  shows "TER (current_of_bipartite f) = separating_of_bipartite (TER\<^bsub>bipartite_web_of \<Gamma>\<^esub> f)"
    (is "TER ?f = separating_of_bipartite ?TER")
proof(rule set_eqI)
  fix x
  consider (A) "x \<in> A \<Gamma>" "x \<in> \<^bold>V" | (B) "x \<in> B \<Gamma>" "x \<in> \<^bold>V"
    | (inner) "x \<notin> A \<Gamma>" "x \<notin> B \<Gamma>" "x \<in> \<^bold>V" | (outside) "x \<notin> \<^bold>V" by auto
  thus "x \<in> TER ?f \<longleftrightarrow> x \<in> separating_of_bipartite ?TER"
  proof cases
    case A
    hence "d_OUT ?f x = d_OUT f (Inl x)" using currentD_outside[OF f, of "Inl x" "Inr x"]
      by(simp add: d_OUT_current_of_bipartite[OF f] no_loop)
    thus ?thesis using A disjoint
      by(auto simp add: separating_of_bipartite_def Let_def SINK.simps intro!: SAT.A imageI)
  next
    case B
    then have "d_IN ?f x = d_IN f (Inr x)"
      using currentD_outside[OF f, of "Inl x" "Inr x"]
      by(simp add: d_IN_current_of_bipartite[OF f] no_loop)
    moreover have "d_OUT ?f x = 0" using B currentD_outside[OF f, of "Inl x" "Inr x"]
      by(simp add: d_OUT_current_of_bipartite[OF f] no_loop)(auto simp add: d_OUT_def nn_integral_0_iff emeasure_count_space_eq_0 intro!: currentD_outside[OF f] elim!: edge_bipartite_webE dest: B_out)
    moreover have "d_OUT f (Inr x) = 0" using B disjoint by(intro currentD_OUT[OF f]) auto
    ultimately show ?thesis using B
      by(auto simp add: separating_of_bipartite_def Let_def SINK.simps SAT.simps)
  next
    case outside
    with current_current_of_bipartite[OF f w] have "d_OUT ?f x = 0" "d_IN ?f x = 0"
      by(rule currentD_outside_OUT currentD_outside_IN)+
    moreover from outside have "Inl x \<notin> vertices ?\<Gamma>" "Inr x \<notin> vertices ?\<Gamma>" by auto
    hence "d_OUT f (Inl x) = 0" "d_IN f (Inl x) = 0" "d_OUT f (Inr x) = 0" "d_IN f (Inr x) = 0"
      by(blast intro: currentD_outside_OUT[OF f] currentD_outside_IN[OF f])+
    ultimately show ?thesis using outside weight_outside[of x]
      by(auto simp add: separating_of_bipartite_def Let_def SINK.simps SAT.simps not_le)
  next
    case inner
    show ?thesis
    proof
      assume "x \<in> separating_of_bipartite ?TER"
      with inner have l: "Inl x \<in> ?TER" and r: "Inr x \<in> ?TER"
        by(auto simp add: separating_of_bipartite_def Let_def)
      have "f (Inl x, Inr x) \<le> d_OUT f (Inl x)"
        unfolding d_OUT_def by(rule nn_integral_ge_point) simp
      with l have 0: "f (Inl x, Inr x) = 0"
        by(auto simp add: SINK.simps)
      with l have "x \<in> SINK ?f"  by(simp add: SINK.simps d_OUT_current_of_bipartite[OF f])
      moreover from r have "Inr x \<in> SAT ?\<Gamma> f" by auto
      with inner have "x \<in> SAT \<Gamma> ?f"
        by(auto elim!: SAT.cases intro!: SAT.IN simp add: 0 d_IN_current_of_bipartite[OF f])
      ultimately show "x \<in> TER ?f" by simp
    next
      assume *: "x \<in> TER ?f"
      have "d_IN f (Inr x) \<le> weight ?\<Gamma> (Inr x)" using f by(rule currentD_weight_IN)
      also have "\<dots> \<le> weight \<Gamma> x" using inner by simp
      also have "\<dots> \<le> d_IN ?f x" using inner * by(auto elim: SAT.cases)
      also have "\<dots> \<le> d_IN f (Inr x)"
        by(simp add: d_IN_current_of_bipartite[OF f] max_def diff_le_self_ennreal)
      ultimately have eq: "d_IN ?f x = d_IN f (Inr x)" by simp
      hence 0: "f (Inl x, Inr x) = 0"
        using ennreal_minus_cancel_iff[of "d_IN f (Inr x)" "f (Inl x, Inr x)" 0] currentD_weight_IN[OF f, of "Inr x"] inner
          d_IN_ge_point[of f "Inl x" "Inr x"]
        by(auto simp add: d_IN_current_of_bipartite[OF f] top_unique)
      have "Inl x \<in> ?TER" "Inr x \<in> ?TER" using inner * currentD_OUT[OF f, of "Inr x"]
        by(auto simp add: SAT.simps SINK.simps d_OUT_current_of_bipartite[OF f] 0 eq)
      thus "x \<in> separating_of_bipartite ?TER" unfolding separating_of_bipartite_def Let_def by blast
    qed
  qed
qed

lemma wave_current_of_bipartite: \<comment> \<open>Lemma 6.3\<close>
  assumes f: "current (bipartite_web_of \<Gamma>) f" (is "current ?\<Gamma> _")
  and w: "wave (bipartite_web_of \<Gamma>) f"
  shows "wave \<Gamma> (current_of_bipartite f)" (is "wave _ ?f")
proof
  have sep': "separating \<Gamma> (separating_of_bipartite (TER\<^bsub>?\<Gamma>\<^esub> f))"
    by(rule separating_of_bipartite)(rule waveD_separating[OF w])
  then show sep: "separating \<Gamma> (TER (current_of_bipartite f))"
    by(simp add: TER_current_of_bipartite[OF f w])

  fix x
  assume "x \<notin> RF (TER ?f)"
  then obtain p y where p: "path \<Gamma> x p y" and y: "y \<in> B \<Gamma>" and x: "x \<notin> TER ?f"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER ?f"
    by(auto simp add: roofed_def elim: rtrancl_path_distinct)
  from p obtain p' where p': "path \<Gamma> x p' y" and distinct: "distinct (x # p')"
    and subset: "set p' \<subseteq> set p" by(auto elim: rtrancl_path_distinct)
  consider (outside) "x \<notin> \<^bold>V" | (A) "x \<in> A \<Gamma>" | (B) "x \<in> B \<Gamma>" | (inner) "x \<in> \<^bold>V" "x \<notin> A \<Gamma>" "x \<notin> B \<Gamma>" by auto
  then show "d_OUT ?f x = 0"
  proof cases
    case outside
    with f w show ?thesis by(rule currentD_outside_OUT[OF current_current_of_bipartite])
  next
    case A
    from separatingD[OF sep p A y] bypass have "x \<in> TER ?f" by blast
    thus ?thesis by(simp add: SINK.simps)
  next
    case B
    with f w show ?thesis by(rule currentD_OUT[OF current_current_of_bipartite])
  next
    case inner
    hence "path ?\<Gamma> (Inl x) [Inr x] (Inr x)" by(auto intro!: rtrancl_path.intros)
    from inner waveD_separating[OF w, THEN separatingD, OF this]
    consider (Inl) "Inl x \<in> TER\<^bsub>?\<Gamma>\<^esub> f" | (Inr) "Inr x \<in> TER\<^bsub>?\<Gamma>\<^esub> f" by auto
    then show ?thesis
    proof cases
      case Inl
      thus ?thesis
        by(auto simp add: SINK.simps d_OUT_current_of_bipartite[OF f] max_def)
    next
      case Inr
      with separating_of_bipartite_aux[OF waveD_separating[OF w] p y] x bypass
      have False unfolding TER_current_of_bipartite[OF f w] by blast
      thus ?thesis ..
    qed
  qed
qed

end

context countable_web begin

lemma countable_bipartite_web_of: "countable_bipartite_web (bipartite_web_of \<Gamma>)" (is "countable_bipartite_web ?\<Gamma>")
proof
  show "\<^bold>V\<^bsub>?\<Gamma>\<^esub> \<subseteq> A ?\<Gamma> \<union> B ?\<Gamma>"
    apply(rule subsetI)
    subgoal for x by(cases x) auto
    done
  show "A ?\<Gamma> \<subseteq> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" by auto
  show "x \<in> A ?\<Gamma> \<and> y \<in> B ?\<Gamma>" if "edge ?\<Gamma> x y" for x y using that
    by(cases x y rule: sum.exhaust[case_product sum.exhaust])(auto simp add: inj_image_mem_iff vertex_def B_out A_in)
  show "A ?\<Gamma> \<inter> B ?\<Gamma> = {}" by auto
  show "countable \<^bold>E\<^bsub>?\<Gamma>\<^esub>" by(simp add: E_bipartite_web)
  show "weight ?\<Gamma> x \<noteq> \<top>" for x by(cases x) simp_all
  show "weight (bipartite_web_of \<Gamma>) x = 0" if "x \<notin> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" for x using that
    by(cases x)(auto simp add: weight_outside)
qed

end

context web begin

lemma unhindered_bipartite_web_of:
  assumes loose: "loose \<Gamma>"
  shows "\<not> hindered (bipartite_web_of \<Gamma>)"
proof
  assume "hindered (bipartite_web_of \<Gamma>)" (is "hindered ?\<Gamma>")
  then obtain f where f: "current ?\<Gamma> f" and w: "wave ?\<Gamma> f" and hind: "hindrance ?\<Gamma> f" by cases
  from f w have "current \<Gamma> (current_of_bipartite f)" by(rule current_current_of_bipartite)
  moreover from f w have "wave \<Gamma> (current_of_bipartite f)" by(rule wave_current_of_bipartite)
  ultimately have *: "current_of_bipartite f = zero_current" by(rule looseD_wave[OF loose])
  have zero: "f (Inl x, Inr y) = 0" if "x \<noteq> y" for x y using that *[THEN fun_cong, of "(x, y)"]
     by(cases "edge \<Gamma> x y")(auto intro: currentD_outside[OF f])

  have OUT: "d_OUT f (Inl x) = f (Inl x, Inr x)" for x
  proof -
    have "d_OUT f (Inl x) = (\<Sum>\<^sup>+ y. f (Inl x, y) * indicator {Inr x} y)" unfolding d_OUT_def
      using zero currentD_outside[OF f]
      apply(intro nn_integral_cong)
      subgoal for y by(cases y)(auto split: split_indicator)
      done
    also have "\<dots> = f (Inl x, Inr x)" by simp
    finally show ?thesis .
  qed
  have IN: "d_IN f (Inr x) = f (Inl x, Inr x)" for x
  proof -
    have "d_IN f (Inr x) = (\<Sum>\<^sup>+ y. f (y, Inr x) * indicator {Inl x} y)" unfolding d_IN_def
      using zero currentD_outside[OF f]
      apply(intro nn_integral_cong)
      subgoal for y by(cases y)(auto split: split_indicator)
      done
    also have "\<dots> = f (Inl x, Inr x)" by simp
    finally show ?thesis .
  qed

  let ?TER = "TER\<^bsub>?\<Gamma>\<^esub> f"
  from hind obtain a where a: "a \<in> A ?\<Gamma>" and n\<E>: "a \<notin> \<E>\<^bsub>?\<Gamma>\<^esub> (TER\<^bsub>?\<Gamma>\<^esub> f)"
    and OUT_a: "d_OUT f a < weight ?\<Gamma> a" by cases
  from a obtain a' where a': "a = Inl a'" and v: "vertex \<Gamma> a'" and b: "a' \<notin> B \<Gamma>" by auto
  have A: "a' \<in> A \<Gamma>"
  proof(rule ccontr)
    assume A: "a' \<notin> A \<Gamma>"
    hence "edge ?\<Gamma> (Inl a') (Inr a')" using v b by simp
    hence p: "path ?\<Gamma> (Inl a') [Inr a'] (Inr a')" by(simp add: rtrancl_path_simps)
    from separatingD[OF waveD_separating[OF w] this] b v A
    have "Inl a' \<in> ?TER \<or> Inr a' \<in> ?TER" by auto
    thus False
    proof cases
      case left
      hence "d_OUT f (Inl a') = 0" by(simp add: SINK.simps)
      moreover hence "d_IN f (Inr a') = 0" by(simp add: OUT IN)
      ultimately have "Inr a' \<notin> ?TER" using v b A OUT_a a' by(auto simp add: SAT.simps)
      then have "essential ?\<Gamma> (B ?\<Gamma>) ?TER (Inl a')" using A
        by(intro essentialI[OF p]) simp_all
      with n\<E> left a' show False by simp
    next
      case right
      hence "d_IN f (Inr a') = weight \<Gamma> a'" using A by(auto simp add: currentD_SAT[OF f])
      hence "d_OUT f (Inl a') = weight \<Gamma> a'" by(simp add: IN OUT)
      with OUT_a a' b show False by simp
    qed
  qed
  moreover

  from A have "d_OUT f (Inl a') = 0" using currentD_outside[OF f, of "Inl a'" "Inr a'"]
    by(simp add: OUT no_loop)
  with b v have TER: "Inl a' \<in> ?TER" by(simp add: SAT.A SINK.simps)
  with n\<E> a' have ness: "\<not> essential ?\<Gamma> (B ?\<Gamma>) ?TER (Inl a')" by simp

  have "a' \<notin> \<E> (TER zero_current)"
  proof
    assume "a' \<in> \<E> (TER zero_current)"
    then obtain p y where p: "path \<Gamma> a' p y" and y: "y \<in> B \<Gamma>"
      and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> TER zero_current"
      by(rule \<E>_E_RF)(auto intro: roofed_greaterI)

    from p show False
    proof cases
      case base with y A disjoint show False by auto
    next
      case (step x p')
      from step(2) have "path ?\<Gamma> (Inl a') [Inr x] (Inr x)" by(simp add: rtrancl_path_simps)
      from not_essentialD[OF ness this] bypass[of x] step(1)
      have "Inr x \<in> ?TER" by simp
      with bypass[of x] step(1) have "d_IN f (Inr x) > 0"
        by(auto simp add: currentD_SAT[OF f] zero_less_iff_neq_zero)
      hence x: "Inl x \<notin> ?TER" by(auto simp add: SINK.simps OUT IN)
      from step(1) have "set (x # p') \<subseteq> set p" by auto
      with \<open>path \<Gamma> x p' y\<close> x y show False
      proof induction
        case (base x)
        thus False using currentD_outside_IN[OF f, of "Inl x"] currentD_outside_OUT[OF f, of "Inl x"]
          by(auto simp add: currentD_SAT[OF f] SINK.simps dest!: bypass)
      next
        case (step x z p' y)
        from step.prems(3) bypass[of x] weight_outside[of x] have x: "vertex \<Gamma> x" by(auto)
        from \<open>edge \<Gamma> x z\<close> have "path ?\<Gamma> (Inl x) [Inr z] (Inr z)" by(simp add: rtrancl_path_simps)
        from separatingD[OF waveD_separating[OF w] this] step.prems(1) step.prems(3) bypass[of z] x \<open>edge \<Gamma> x z\<close>
        have "Inr z \<in> ?TER" by(force simp add: B_out inj_image_mem_iff)
        with bypass[of z] step.prems(3) \<open>edge \<Gamma> x z\<close> have "d_IN f (Inr z) > 0"
          by(auto simp add: currentD_SAT[OF f] A_in zero_less_iff_neq_zero)
        hence x: "Inl z \<notin> ?TER" by(auto simp add: SINK.simps OUT IN)
        with step.IH[OF this] step.prems(2,3) show False by auto
      qed
    qed
  qed
  moreover have "d_OUT zero_current a' < weight \<Gamma> a'"
    using OUT_a a' b by (auto simp: zero_less_iff_neq_zero)
  ultimately have "hindrance \<Gamma> zero_current" by(rule hindrance)
  with looseD_hindrance[OF loose] show False by contradiction
qed

lemma (in -) divide_less_1_iff_ennreal: "a / b < (1::ennreal) \<longleftrightarrow> (0 < b \<and> a < b \<or> b = 0 \<and> a = 0 \<or> b = top)"
  by (cases a; cases b; cases "b = 0")
     (auto simp: divide_ennreal ennreal_less_iff ennreal_top_divide)

lemma linkable_bipartite_web_ofD:
  assumes link: "linkable (bipartite_web_of \<Gamma>)" (is "linkable ?\<Gamma>")
  and countable: "countable \<^bold>E"
  shows "linkable \<Gamma>"
proof -
  from link obtain f where wf: "web_flow ?\<Gamma> f" and link: "linkage ?\<Gamma> f" by blast
  from wf have f: "current ?\<Gamma> f" by(rule web_flowD_current)
  define f' where "f' = current_of_bipartite f"

  have IN_le_OUT: "d_IN f' x \<le> d_OUT f' x" if "x \<notin> B \<Gamma>" for x
  proof(cases "x \<in> \<^bold>V")
    case True
    have "d_IN f' x = d_IN f (Inr x) - f (Inl x, Inr x)" (is "_ = _ - ?rest")
      by(simp add: f'_def d_IN_current_of_bipartite[OF f])
    also have "\<dots> \<le> weight ?\<Gamma> (Inr x) - ?rest"
      using currentD_weight_IN[OF f, of "Inr x"] by(rule ennreal_minus_mono) simp
    also have "\<dots> \<le> weight ?\<Gamma> (Inl x) - ?rest" using that ennreal_minus_mono by(auto)
    also have "weight ?\<Gamma> (Inl x) = d_OUT f (Inl x)" using that linkageD[OF link, of "Inl x"] True by auto
    also have "\<dots> - ?rest = d_OUT f' x"
      by(simp add: f'_def d_OUT_current_of_bipartite[OF f])
    finally show ?thesis .
  next
    case False
    with currentD_outside_OUT[OF f, of "Inl x"] currentD_outside_IN[OF f, of "Inr x"]
    show ?thesis by(simp add: f'_def d_IN_current_of_bipartite[OF f] d_OUT_current_of_bipartite[OF f])
  qed
  have link: "linkage \<Gamma> f'"
  proof
    show "d_OUT f' a = weight \<Gamma> a" if "a \<in> A \<Gamma>" for a
    proof(cases "a \<in> \<^bold>V")
      case True
      from that have "a \<notin> B \<Gamma>" using disjoint by auto
      with that True linkageD[OF link, of "Inl a"] ennreal_minus_cancel_iff[of _ _ 0] currentD_outside[OF f, of "Inl a" "Inr a"]
      show ?thesis by(clarsimp simp add: f'_def d_OUT_current_of_bipartite[OF f] max_def no_loop)
    next
      case False
      with weight_outside[OF this] currentD_outside[OF f, of "Inl a" "Inr a"] currentD_outside_OUT[OF f, of "Inl a"]
      show ?thesis by(simp add: f'_def d_OUT_current_of_bipartite[OF f] no_loop)
    qed
  qed

  define F where "F = {g. (\<forall>e. 0 \<le> g e) \<and> (\<forall>e. e \<notin> \<^bold>E \<longrightarrow> g e = 0) \<and>
    (\<forall>x. x \<notin> B \<Gamma> \<longrightarrow> d_IN g x \<le> d_OUT g x) \<and>
    linkage \<Gamma> g \<and>
    (\<forall>x\<in>A \<Gamma>. d_IN g x = 0) \<and>
    (\<forall>x. d_OUT g x \<le> weight \<Gamma> x) \<and>
    (\<forall>x. d_IN g x \<le> weight \<Gamma> x) \<and>
    (\<forall>x\<in>B \<Gamma>. d_OUT g x = 0) \<and> g \<le> f'}"
  define leq where "leq = restrict_rel F {(f, f'). f' \<le> f}"
  have F: "Field leq = F" by(auto simp add: leq_def)
  have F_I [intro?]: "f \<in> Field leq" if "\<And>e. 0 \<le> f e" and "\<And>e. e \<notin> \<^bold>E \<Longrightarrow> f e = 0"
    and "\<And>x. x \<notin> B \<Gamma> \<Longrightarrow> d_IN f x \<le> d_OUT f x" and "linkage \<Gamma> f"
    and "\<And>x. x \<in> A \<Gamma> \<Longrightarrow> d_IN f x = 0" and "\<And>x. d_OUT f x \<le> weight \<Gamma> x"
    and "\<And>x. d_IN f x \<le> weight \<Gamma> x" and "\<And>x. x \<in> B \<Gamma> \<Longrightarrow> d_OUT f x = 0"
    and "f \<le> f'" for f using that by(simp add: F F_def)
  have F_nonneg: "0 \<le> f e" if "f \<in> Field leq" for f e using that by(cases e)(simp add: F F_def)
  have F_outside: "f e = 0" if "f \<in> Field leq" "e \<notin> \<^bold>E" for f e using that by(cases e)(simp add: F F_def)
  have F_IN_OUT: "d_IN f x \<le> d_OUT f x" if "f \<in> Field leq" "x \<notin> B \<Gamma>" for f x using that by(simp add: F F_def)
  have F_link: "linkage \<Gamma> f" if "f \<in> Field leq" for f using that by(simp add: F F_def)
  have F_IN: "d_IN f x = 0" if "f \<in> Field leq" "x \<in> A \<Gamma>" for f x using that by(simp add: F F_def)
  have F_OUT: "d_OUT f x = 0" if "f \<in> Field leq" "x \<in> B \<Gamma>" for f x using that by(simp add: F F_def)
  have F_weight_OUT: "d_OUT f x \<le> weight \<Gamma> x" if "f \<in> Field leq" for f x using that by(simp add: F F_def)
  have F_weight_IN: "d_IN f x \<le> weight \<Gamma> x" if "f \<in> Field leq" for f x using that by(simp add: F F_def)
  have F_le: "f e \<le> f' e" if "f \<in> Field leq" for f e using that by(cases e)(simp add: F F_def le_fun_def)

  have F_finite_OUT: "d_OUT f x \<noteq> \<top>" if "f \<in> Field leq" for f x
  proof -
    have "d_OUT f x \<le> weight \<Gamma> x" by(rule F_weight_OUT[OF that])
    also have "\<dots> < \<top>" by(simp add: less_top[symmetric])
    finally show ?thesis by simp
  qed

  have F_finite: "f e \<noteq> \<top>" if "f \<in> Field leq" for f e
  proof(cases e)
    case (Pair x y)
    have "f e \<le> d_OUT f x" unfolding Pair d_OUT_def by(rule nn_integral_ge_point) simp
    also have "\<dots> < \<top>" by(simp add: F_finite_OUT[OF that] less_top[symmetric])
    finally show ?thesis by simp
  qed

  have f': "f' \<in> Field leq"
  proof
    show "0 \<le> f' e" for e by(cases e)(simp add: f'_def)
    show "f' e = 0" if "e \<notin> \<^bold>E" for e using that by(clarsimp split: split_indicator_asm simp add: f'_def)
    show "d_IN f' x \<le> d_OUT f' x" if "x \<notin> B \<Gamma>" for x using that by(rule IN_le_OUT)
    show "linkage \<Gamma> f'" by(rule link)
    show "d_IN f' x = 0" if "x \<in> A \<Gamma>" for x using that currentD_IN[OF f, of "Inl x"] disjoint
      currentD_outside[OF f, of "Inl x" "Inr x"] currentD_outside_IN[OF f, of "Inr x"]
      by(cases "x \<in> \<^bold>V")(auto simp add: d_IN_current_of_bipartite[OF f] no_loop f'_def)
    show "d_OUT f' x = 0" if "x \<in> B \<Gamma>" for x using that currentD_OUT[OF f, of "Inr x"] disjoint
      currentD_outside[OF f, of "Inl x" "Inr x"] currentD_outside_OUT[OF f, of "Inl x"]
      by(cases "x \<in> \<^bold>V")(auto simp add: d_OUT_current_of_bipartite[OF f] no_loop f'_def)
    show "d_OUT f' x \<le> weight \<Gamma> x" for x using currentD_weight_OUT[OF f, of "Inl x"]
      by(simp add: d_OUT_current_of_bipartite[OF f] ennreal_diff_le_mono_left f'_def split: if_split_asm)
    show "d_IN f' x \<le> weight \<Gamma> x" for x using currentD_weight_IN[OF f, of "Inr x"]
      by(simp add: d_IN_current_of_bipartite[OF f] ennreal_diff_le_mono_left f'_def split: if_split_asm)
  qed simp

  have F_leI: "g \<in> Field leq" if f: "f \<in> Field leq" and le: "\<And>e. g e \<le> f e"
    and nonneg: "\<And>e. 0 \<le> g e" and IN_OUT: "\<And>x. x \<notin> B \<Gamma> \<Longrightarrow> d_IN g x \<le> d_OUT g x"
    and link: "linkage \<Gamma> g"
    for f g
  proof
    show "g e = 0" if "e \<notin> \<^bold>E" for e using nonneg[of e] F_outside[OF f that] le[of e] by simp
    show "d_IN g a = 0" if "a \<in> A \<Gamma>" for a
      using d_IN_mono[of g a f, OF le] F_IN[OF f that] by auto
    show "d_OUT g b = 0" if "b \<in> B \<Gamma>" for b
      using d_OUT_mono[of g b f, OF le] F_OUT[OF f that] by auto
    show "d_OUT g x \<le> weight \<Gamma> x" for x
      using d_OUT_mono[of g x f, OF le] F_weight_OUT[OF f] by(rule order_trans)
    show "d_IN g x \<le> weight \<Gamma> x" for x
      using d_IN_mono[of g x f, OF le] F_weight_IN[OF f] by(rule order_trans)
    show "g \<le> f'" using order_trans[OF le F_le[OF f]] by(auto simp add: le_fun_def)
  qed(blast intro: IN_OUT link nonneg)+

  have chain_Field: "Inf M \<in> F" if M: "M \<in> Chains leq" and nempty: "M \<noteq> {}" for M
  proof -
    from nempty obtain g0 where g0_in_M: "g0 \<in> M" by auto
    with M have g0: "g0 \<in> Field leq" by(rule Chains_FieldD)

    from M have "M \<in> Chains {(g, g'). g' \<le> g}"
      by(rule mono_Chains[THEN subsetD, rotated])(auto simp add: leq_def in_restrict_rel_iff)
    then have "Complete_Partial_Order.chain (\<ge>) M" by(rule Chains_into_chain)
    hence chain': "Complete_Partial_Order.chain (\<le>) M" by(simp add: chain_dual)

    have "support_flow f' \<subseteq> \<^bold>E" using F_outside[OF f'] by(auto intro: ccontr simp add: support_flow.simps)
    then have countable': "countable (support_flow f')"
      by(rule countable_subset)(simp add: E_bipartite_web countable "\<^bold>V_def")

    have finite_OUT: "d_OUT f' x \<noteq> \<top>" for x using weight_finite[of x]
      by(rule neq_top_trans)(rule F_weight_OUT[OF f'])
    have finite_IN: "d_IN f' x \<noteq> \<top>" for x using weight_finite[of x]
      by(rule neq_top_trans)(rule F_weight_IN[OF f'])
    have OUT_M: "d_OUT (Inf M) x = (INF g\<in>M. d_OUT g x)" for x using chain' nempty countable' _ finite_OUT
      by(rule d_OUT_Inf)(auto dest!: Chains_FieldD[OF M] simp add: leq_def F_nonneg F_le)
    have IN_M: "d_IN (Inf M) x = (INF g\<in>M. d_IN g x)" for x using chain' nempty countable' _ finite_IN
      by(rule d_IN_Inf)(auto dest!: Chains_FieldD[OF M] simp add: leq_def F_nonneg F_le)

    show "Inf M \<in> F" using g0 unfolding F[symmetric]
    proof(rule F_leI)
      show "(Inf M) e \<le> g0 e" for e using g0_in_M by(auto intro: INF_lower)
      show "0 \<le> (Inf M) e" for e by(auto intro!: INF_greatest dest: F_nonneg dest!: Chains_FieldD[OF M])
      show "d_IN (Inf M) x \<le> d_OUT (Inf M) x" if "x \<notin> B \<Gamma>" for x using that
        by(auto simp add: IN_M OUT_M intro!: INF_mono dest: Chains_FieldD[OF M] intro: F_IN_OUT[OF _ that])
      show "linkage \<Gamma> (Inf M)" using nempty
        by(simp add: linkage.simps OUT_M F_link[THEN linkageD] Chains_FieldD[OF M] cong: INF_cong)
    qed
  qed

  let ?P = "\<lambda>g z. z \<notin> A \<Gamma> \<and> z \<notin> B \<Gamma> \<and> d_OUT g z > d_IN g z"

  define link
    where "link g =
      (if \<exists>z. ?P g z then
        let z = SOME z. ?P g z; factor = d_IN g z / d_OUT g z
        in (\<lambda>(x, y). (if x = z then factor else 1) * g (x, y))
       else g)" for g
  have increasing: "link g \<le> g \<and> link g \<in> Field leq" if g: "g \<in> Field leq" for g
  proof(cases "\<exists>z. ?P g z")
    case False
    thus ?thesis using that by(auto simp add: link_def leq_def)
  next
    case True
    define z where "z = Eps (?P g)"
    from True have "?P g z" unfolding z_def by(rule someI_ex)
    hence A: "z \<notin> A \<Gamma>" and B: "z \<notin> B \<Gamma>" and less: "d_IN g z < d_OUT g z" by simp_all
    let ?factor = "d_IN g z / d_OUT g z"
    have link [simp]: "link g (x, y) = (if x = z then ?factor else 1) * g (x, y)" for x y
      using True by(auto simp add: link_def z_def Let_def)

    have "?factor \<le> 1" (is "?factor \<le> _") using less
      by(cases "d_OUT g z" "d_IN g z" rule: ennreal2_cases) (simp_all add: ennreal_less_iff divide_ennreal)
    hence le': "?factor * g (x, y) \<le> 1 * g (x, y)" for y x
      by(rule mult_right_mono)(simp add: F_nonneg[OF g])
    hence le: "link g e \<le> g e" for e by(cases e)simp
    have "link g \<in> Field leq" using g le
    proof(rule F_leI)
      show nonneg: "0 \<le> link g e" for e
        using F_nonneg[OF g, of e] by(cases e) simp
      show "linkage \<Gamma> (link g)" using that A F_link[OF g] by(clarsimp simp add: linkage.simps d_OUT_def)

      fix x
      assume x: "x \<notin> B \<Gamma>"
      have "d_IN (link g) x \<le> d_IN g x" unfolding d_IN_def using le' by(auto intro: nn_integral_mono)
      also have "\<dots> \<le> d_OUT (link g) x"
      proof(cases "x = z")
        case True
        have "d_IN g x = d_OUT (link g) x" unfolding d_OUT_def
          using True F_weight_IN[OF g, of x] F_IN_OUT[OF g x] F_finite_OUT F_finite_OUT[OF g, of x]
          by(cases "d_OUT g z = 0")
            (auto simp add: nn_integral_divide nn_integral_cmult d_OUT_def[symmetric] ennreal_divide_times less_top)
        thus ?thesis by simp
      next
        case False
        have "d_IN g x \<le> d_OUT g x" using x by(rule F_IN_OUT[OF g])
        also have "\<dots> \<le> d_OUT (link g) x" unfolding d_OUT_def using False by(auto intro!: nn_integral_mono)
        finally show ?thesis .
      qed
      finally show "d_IN (link g) x \<le> d_OUT (link g) x" .
    qed
    with le g show ?thesis unfolding F by(simp add: leq_def le_fun_def del: link)
  qed

  have "bourbaki_witt_fixpoint Inf leq link" using chain_Field increasing unfolding leq_def
    by(intro bourbaki_witt_fixpoint_restrict_rel)(auto intro: Inf_greatest Inf_lower)
  then interpret bourbaki_witt_fixpoint Inf leq link .

  define g where "g = fixp_above f'"

  have g: "g \<in> Field leq" using f' unfolding g_def by(rule fixp_above_Field)
  hence "linkage \<Gamma> g" by(rule F_link)
  moreover
  have "web_flow \<Gamma> g"
  proof(intro web_flow.intros current.intros)
    show "d_OUT g x \<le> weight \<Gamma> x" for x using g by(rule F_weight_OUT)
    show "d_IN g x \<le> weight \<Gamma> x" for x using g by(rule F_weight_IN)
    show "d_IN g x = 0" if "x \<in> A \<Gamma>" for x using g that by(rule F_IN)
    show B: "d_OUT g x = 0" if "x \<in> B \<Gamma>" for x using g that by(rule F_OUT)
    show "g e = 0" if "e \<notin> \<^bold>E" for e using g that by(rule F_outside)

    show KIR: "KIR g x" if A: "x \<notin> A \<Gamma>" and B: "x \<notin> B \<Gamma>" for x
    proof(rule ccontr)
      define z where "z = Eps (?P g)"
      assume "\<not> KIR g x"
      with F_IN_OUT[OF g B] have "d_OUT g x > d_IN g x" by simp
      with A B have Ex: "\<exists>x. ?P g x" by blast
      then have "?P g z" unfolding z_def by(rule someI_ex)
      hence A: "z \<notin> A \<Gamma>" and B: "z \<notin> B \<Gamma>" and less: "d_IN g z < d_OUT g z" by simp_all
      let ?factor = "d_IN g z / d_OUT g z"
      have "\<exists>y. edge \<Gamma> z y \<and> g (z, y) > 0"
      proof(rule ccontr)
        assume "\<not> ?thesis"
        hence "d_OUT g z = 0" using F_outside[OF g]
          by(force simp add: d_OUT_def nn_integral_0_iff_AE AE_count_space not_less)
        with less show False by simp
      qed
      then obtain y where y: "edge \<Gamma> z y" and gr0: "g (z, y) > 0" by blast
      have "?factor < 1" (is "?factor < _") using less
        by(cases "d_OUT g z" "d_IN g z" rule: ennreal2_cases)
          (auto simp add: ennreal_less_iff divide_ennreal)

      hence le': "?factor * g (z, y) < 1 * g (z, y)" using gr0 F_finite[OF g]
        by(intro ennreal_mult_strict_right_mono) (auto simp: less_top)
      hence "link g (z, y) \<noteq> g (z, y)" using Ex by(auto simp add: link_def z_def Let_def)
      hence "link g \<noteq> g" by(auto simp add: fun_eq_iff)
      moreover have "link g = g" using f' unfolding g_def by(rule fixp_above_unfold[symmetric])
      ultimately show False by contradiction
    qed
    show "d_OUT g x \<le> d_IN g x" if "x \<notin> A \<Gamma>" for x using KIR[of x] that B[of x]
      by(cases "x \<in> B \<Gamma>") auto
  qed
  ultimately show ?thesis by blast
qed

end

subsection \<open>Loose webs are linkable\<close>

lemma linkage_quotient_webD:
  fixes \<Gamma> :: "('v, 'more) web_scheme" (structure) and h g
  defines "k \<equiv> plus_current h g"
  assumes f: "current \<Gamma> f"
  and w: "wave \<Gamma> f"
  and wg: "web_flow (quotient_web \<Gamma> f) g" (is "web_flow ?\<Gamma> _")
  and link: "linkage (quotient_web \<Gamma> f) g"
  and trim: "trimming \<Gamma> f h"
  shows "web_flow \<Gamma> k"
  and "orthogonal_current \<Gamma> k (\<E> (TER f))"
proof -
  from wg have g: "current ?\<Gamma> g" by(rule web_flowD_current)

  from trim obtain h: "current \<Gamma> h" and w': "wave \<Gamma> h" and h_le_f: "\<And>e. h e \<le> f e"
    and KIR: "\<And>x. \<lbrakk>x \<in> RF\<^sup>\<circ> (TER f); x \<notin> A \<Gamma>\<rbrakk> \<Longrightarrow> KIR h x"
    and TER: "TER h \<supseteq> \<E> (TER f) - A \<Gamma>"
    by(cases)(auto simp add: le_fun_def)

  have eq: "quotient_web \<Gamma> f = quotient_web \<Gamma> h" using w trim by(rule quotient_web_trimming)

  let ?T = "\<E> (TER f)"

  have RFc: "RF\<^sup>\<circ> (TER h) = RF\<^sup>\<circ> (TER f)"
    by(subst (1 2) roofed_circ_essential[symmetric])(simp only: trimming_\<E>[OF w trim])
  have OUT_k: "d_OUT k x = (if x \<in> RF\<^sup>\<circ> (TER f) then d_OUT h x else d_OUT g x)" for x
    using OUT_plus_current[OF h w', of g] web_flowD_current[OF wg] unfolding eq k_def RFc by simp
  have RF: "RF (TER h) = RF (TER f)"
    by(subst (1 2) RF_essential[symmetric])(simp only: trimming_\<E>[OF w trim])
  have IN_k: "d_IN k x = (if x \<in> RF (TER f) then d_IN h x else d_IN g x)" for x
    using IN_plus_current[OF h w', of g] web_flowD_current[OF wg] unfolding eq k_def RF by simp

  have k: "current \<Gamma> k" unfolding k_def using h w' g unfolding eq by(rule current_plus_current)
  then show wk: "web_flow \<Gamma> k"
  proof(rule web_flow)
    fix x
    assume "x \<in> \<^bold>V" and A: "x \<notin> A \<Gamma>" and B: "x \<notin> B \<Gamma>"
    show "KIR k x"
    proof(cases "x \<in> \<E> (TER f)")
      case False
      thus ?thesis using A KIR[of x] web_flowD_KIR[OF wg, of x] B by(auto simp add: OUT_k IN_k roofed_circ_def)
    next
      case True
      with A TER have [simp]: "d_OUT h x = 0" and "d_IN h x \<ge> weight \<Gamma> x"
        by(auto simp add: SINK.simps elim: SAT.cases)
      with currentD_weight_IN[OF h, of x] have [simp]: "d_IN h x = weight \<Gamma> x" by auto
      from linkageD[OF link, of x] True currentD_IN[OF g, of x] B
      have "d_OUT g x = weight \<Gamma> x" "d_IN g x = 0" by(auto simp add: roofed_circ_def)
      thus ?thesis using True by(auto simp add: IN_k OUT_k roofed_circ_def intro: roofed_greaterI)
    qed
  qed

  have h_le_k: "h e \<le> k e" for e unfolding k_def plus_current_def by(rule add_increasing2) simp_all
  hence "SAT \<Gamma> h \<subseteq> SAT \<Gamma> k" by(rule SAT_mono)
  hence SAT: "?T \<subseteq> SAT \<Gamma> k" using TER by(auto simp add: elim!: SAT.cases intro: SAT.intros)
  show "orthogonal_current \<Gamma> k ?T"
  proof(rule orthogonal_current)
    show "weight \<Gamma> x \<le> d_IN k x" if "x \<in> ?T" "x \<notin> A \<Gamma>" for x
      using subsetD[OF SAT, of x] that by(auto simp add: currentD_SAT[OF k])
  next
    fix x
    assume x: "x \<in> ?T" and A: "x \<in> A \<Gamma>" and B: "x \<notin> B \<Gamma>"
    with d_OUT_mono[of h x f, OF h_le_f] have "d_OUT h x = 0" by(auto simp add: SINK.simps)
    moreover from linkageD[OF link, of x] x A have "d_OUT g x = weight ?\<Gamma> x" by simp
    ultimately show "d_OUT k x = weight \<Gamma> x" using x A currentD_IN[OF f A] B
      by(auto simp add: d_OUT_add roofed_circ_def k_def plus_current_def )
  next
    fix u v
    assume v: "v \<in> RF ?T" and u: "u \<notin> RF\<^sup>\<circ> ?T"
    have "h (u, v) \<le> f (u, v)" by(rule h_le_f)
    also have "\<dots> \<le> d_OUT f u" unfolding d_OUT_def by(rule nn_integral_ge_point) simp
    also have "\<dots> = 0" using u using RF_essential[of \<Gamma> "TER f"]
      by(auto simp add: roofed_circ_def SINK.simps intro: waveD_OUT[OF w])
    finally have "h (u, v) = 0" by simp
    moreover have "g (u, v) = 0" using g v RF_essential[of \<Gamma> "TER f"]
      by(auto intro: currentD_outside simp add: roofed_circ_def)
    ultimately show "k (u, v) = 0" by(simp add: k_def)
  qed
qed

context countable_web begin

theorem loose_linkable: \<comment> \<open>Theorem 6.2\<close>
  assumes "loose \<Gamma>"
  shows "linkable \<Gamma>"
proof -
  interpret bi: countable_bipartite_web "bipartite_web_of \<Gamma>" by(rule countable_bipartite_web_of)
  have "\<not> hindered (bipartite_web_of \<Gamma>)" using assms by(rule unhindered_bipartite_web_of)
  then have "linkable (bipartite_web_of \<Gamma>)"
    by(rule bi.unhindered_linkable)
  then show ?thesis by(rule linkable_bipartite_web_ofD) simp
qed

lemma ex_orthogonal_current: \<comment> \<open>Lemma 4.15\<close>
  "\<exists>f S. web_flow \<Gamma> f \<and> separating \<Gamma> S \<and> orthogonal_current \<Gamma> f S"
proof -
  from ex_maximal_wave[OF countable]
  obtain f where f: "current \<Gamma> f"
    and w: "wave \<Gamma> f"
    and maximal: "\<And>w. \<lbrakk> current \<Gamma> w; wave \<Gamma> w; f \<le> w \<rbrakk> \<Longrightarrow> f = w" by blast
  from ex_trimming[OF f w countable weight_finite] obtain h where h: "trimming \<Gamma> f h" ..

  let ?\<Gamma> = "quotient_web \<Gamma> f"
  interpret \<Gamma>: countable_web "?\<Gamma>" by(rule countable_web_quotient_web)
  have "loose ?\<Gamma>" using f w maximal by(rule loose_quotient_web[OF  weight_finite])
  then have "linkable ?\<Gamma>" by(rule \<Gamma>.loose_linkable)
  then obtain g where wg: "web_flow ?\<Gamma> g" and link: "linkage ?\<Gamma> g" by blast

  let ?k = "plus_current h g"
  have "web_flow \<Gamma> ?k" "orthogonal_current \<Gamma> ?k (\<E> (TER f))"
    by(rule linkage_quotient_webD[OF f w wg link h])+
  moreover have "separating \<Gamma> (\<E> (TER f))"
    using waveD_separating[OF w] by(rule separating_essential)
  ultimately show ?thesis by blast
qed

end

subsection \<open>Reduction of networks to webs\<close>

definition web_of_network :: "('v, 'more) network_scheme \<Rightarrow> ('v edge, 'more) web_scheme"
where
  "web_of_network \<Delta> =
   \<lparr>edge = \<lambda>(x, y) (y', z). y' = y \<and> edge \<Delta> x y \<and> edge \<Delta> y z,
    weight = capacity \<Delta>,
    A = {(source \<Delta>, x)|x. edge \<Delta> (source \<Delta>) x},
    B = {(x, sink \<Delta>)|x. edge \<Delta> x (sink \<Delta>)},
    \<dots> = network.more \<Delta>\<rparr>"

lemma web_of_network_sel [simp]:
  fixes \<Delta> (structure) shows
  "edge (web_of_network \<Delta>) e e' \<longleftrightarrow> e \<in> \<^bold>E \<and> e' \<in> \<^bold>E \<and> snd e = fst e'"
  "weight (web_of_network \<Delta>) e = capacity \<Delta> e"
  "A (web_of_network \<Delta>) = {(source \<Delta>, x)|x. edge \<Delta> (source \<Delta>) x}"
  "B (web_of_network \<Delta>) = {(x, sink \<Delta>)|x. edge \<Delta> x (sink \<Delta>)}"
by(auto simp add: web_of_network_def split: prod.split)

lemma vertex_web_of_network [simp]:
  "vertex (web_of_network \<Delta>) (x, y) \<longleftrightarrow> edge \<Delta> x y \<and> (\<exists>z. edge \<Delta> y z \<or> edge \<Delta> z x)"
by(auto simp add: vertex_def Domainp.simps Rangep.simps)

definition flow_of_current :: "('v, 'more) network_scheme \<Rightarrow> 'v edge current \<Rightarrow> 'v flow"
where "flow_of_current \<Delta> f e = max (d_OUT f e) (d_IN f e)"

lemma flow_flow_of_current:
  fixes \<Delta> (structure) and \<Gamma>
  defines [simp]: "\<Gamma> \<equiv> web_of_network \<Delta>"
  assumes fw: "web_flow \<Gamma> f"
  shows "flow \<Delta> (flow_of_current \<Delta> f)" (is "flow _ ?f")
proof
  from fw have f: "current \<Gamma> f" and KIR: "\<And>x. \<lbrakk> x \<notin> A \<Gamma>; x \<notin> B \<Gamma> \<rbrakk> \<Longrightarrow> KIR f x"
    by(auto 4 3 dest: web_flowD_current web_flowD_KIR)

  show "?f e \<le> capacity \<Delta> e" for e
    using currentD_weight_OUT[OF f, of e] currentD_weight_IN[OF f, of e]
    by(simp add: flow_of_current_def)

  fix x
  assume x: "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>"
  have "d_OUT ?f x = (\<Sum>\<^sup>+ y. d_IN f (x, y))" unfolding d_OUT_def
    by(simp add: flow_of_current_def max_absorb2 currentD_OUT_IN[OF f] x)
  also have "\<dots> = (\<Sum>\<^sup>+ y. \<Sum>\<^sup>+ e\<in>range (\<lambda>z. (z, x)). f (e, x, y))"
    by(auto simp add: nn_integral_count_space_indicator d_IN_def intro!: nn_integral_cong currentD_outside[OF f] split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ z\<in>UNIV. \<Sum>\<^sup>+ y. f ((z, x), x, y))"
    by(subst nn_integral_snd_count_space[of "case_prod _", simplified])
      (simp add: nn_integral_count_space_reindex nn_integral_fst_count_space[of "case_prod _", simplified])
  also have "\<dots> = (\<Sum>\<^sup>+ z. \<Sum>\<^sup>+ e\<in>range (Pair x). f ((z, x), e))"
    by(simp add: nn_integral_count_space_reindex)
  also have "\<dots> = (\<Sum>\<^sup>+ z. d_OUT f (z, x))"
    by(auto intro!: nn_integral_cong currentD_outside[OF f] simp add: d_OUT_def nn_integral_count_space_indicator split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ z\<in>{z. edge \<Delta> z x}. d_OUT f (z, x))"
    by(auto intro!: nn_integral_cong currentD_outside_OUT[OF f] simp add: nn_integral_count_space_indicator split: split_indicator)
  also have "\<dots> = (\<Sum>\<^sup>+ z\<in>{z. edge \<Delta> z x}. max (d_OUT f (z, x)) (d_IN f (z, x)))"
  proof(rule nn_integral_cong)
    show "d_OUT f (z, x) = max (d_OUT f (z, x)) (d_IN f (z, x))"
      if "z \<in> space (count_space {z. edge \<Delta> z x})" for z using currentD_IN[OF f] that
      by(cases "z = source \<Delta>")(simp_all add: max_absorb1  currentD_IN[OF f] KIR x)
  qed
  also have "\<dots> = (\<Sum>\<^sup>+ z. max (d_OUT f (z, x)) (d_IN f (z, x)))"
    by(auto intro!: nn_integral_cong currentD_outside_OUT[OF f] currentD_outside_IN[OF f] simp add: nn_integral_count_space_indicator max_def split: split_indicator)
  also have "\<dots> = d_IN ?f x" by(simp add: flow_of_current_def d_IN_def)
  finally show "KIR ?f x" .
qed

text \<open>
  The reduction of Conjecture 1.2 to Conjecture 3.6 is flawed in @{cite "AharoniBergerGeorgakopoulusPerlsteinSpruessel2011JCT"}.
  Not every essential A-B separating set of vertices in @{term "web_of_network \<Delta>"} is an s-t-cut in
  @{term \<Delta>}, as the following counterexample shows.

  The network @{term \<Delta>} has five nodes @{term "s"}, @{term "t"}, @{term "x"}, @{term "y"} and @{term "z"}
  and edges @{term "(s, x)"}, @{term "(x, y)"}, @{term "(y, z)"}, @{term "(y, t)"} and @{term "(z, t)"}.
  For @{term "web_of_network \<Delta>"}, the set @{term "S = {(x, y), (y, z)}"} is essential and A-B separating.
  (@{term "(x, y)"} is essential due to the path @{term "[(y, z)]"} and @{term "(y, z)"} is essential
  due to the path @{term "[(z, t)]"}). However, @{term S} is not a cut in @{term \<Delta>} because the node @{term y}
  has an outgoing edge that is in @{term S} and one that is not in @{term S}.

  However, this can be remedied if all edges carry positive capacity. Then, orthogonality of the current
  rules out the above possibility.
\<close>
lemma cut_RF_separating:
  fixes \<Delta> (structure)
  assumes sep: "separating_network \<Delta> V"
  and sink: "sink \<Delta> \<notin> V"
  shows "cut \<Delta> (RF\<^sup>N V)"
proof
  show "source \<Delta> \<in> RF\<^sup>N V" by(rule roofedI)(auto dest: separatingD[OF sep])
  show "sink \<Delta> \<notin> RF\<^sup>N V" using sink by(auto dest: roofedD[OF _ rtrancl_path.base])
qed

context
  fixes \<Delta> :: "('v, 'more) network_scheme" and \<Gamma> (structure)
  defines \<Gamma>_def: "\<Gamma> \<equiv> web_of_network \<Delta>"
begin

lemma separating_network_cut_of_sep:
  assumes sep: "separating \<Gamma> S"
  and source_sink: "source \<Delta> \<noteq> sink \<Delta>"
  shows "separating_network \<Delta> (fst ` \<E> S)"
proof
  define s t where "s = source \<Delta>" and "t = sink \<Delta>"
  fix p
  assume p: "path \<Delta> s p t"
  with p source_sink have "p \<noteq> []" by cases(auto simp add: s_def t_def)
  with p have p': "path \<Gamma> (s, hd p) (zip p (tl p)) (last (s # butlast p), t)"
  proof(induction)
    case (step x y p z)
    then show ?case by(cases p)(auto elim: rtrancl_path.cases intro: rtrancl_path.intros simp add: \<Gamma>_def)
  qed simp
  from sep have "separating \<Gamma> (\<E> S)" by(rule separating_essential)
  from this p' have "(\<exists>z\<in>set (zip p (tl p)). z \<in> \<E> S) \<or> (s, hd p) \<in> \<E> S"
    apply(rule separatingD)
    using rtrancl_path_nth[OF p, of 0] rtrancl_path_nth[OF p, of "length p - 1"] \<open>p \<noteq> []\<close> rtrancl_path_last[OF p]
    apply(auto simp add: \<Gamma>_def s_def t_def hd_conv_nth last_conv_nth nth_butlast nth_Cons' cong: if_cong split: if_split_asm)
    apply(metis One_nat_def Suc_leI cancel_comm_monoid_add_class.diff_cancel le_antisym length_butlast length_greater_0_conv list.size(3))+
    done
  then show "(\<exists>z\<in>set p. z \<in> fst ` \<E> S) \<or> s \<in> fst ` \<E> S"
    by(auto dest!: set_zip_leftD intro: rev_image_eqI)
qed

definition cut_of_sep :: "('v \<times> 'v) set \<Rightarrow> 'v set"
where "cut_of_sep S = RF\<^sup>N\<^bsub>\<Delta>\<^esub> (fst ` \<E> S)"

lemma separating_cut:
  assumes sep: "separating \<Gamma> S"
  and neq: "source \<Delta> \<noteq> sink \<Delta>"
  and sink_out: "\<And>x. \<not> edge \<Delta> (sink \<Delta>) x"
  shows "cut \<Delta> (cut_of_sep S)"
  unfolding cut_of_sep_def
proof(rule cut_RF_separating)
  show "separating_network \<Delta> (fst ` \<E> S)" using sep neq by(rule separating_network_cut_of_sep)

  show "sink \<Delta> \<notin> fst ` \<E> S"
  proof
    assume "sink \<Delta> \<in> fst ` \<E> S"
    then obtain x where "(sink \<Delta>, x) \<in> \<E> S" by auto
    hence "(sink \<Delta>, x) \<in> \<^bold>V" by(auto simp add: \<Gamma>_def dest!: essential_vertex)
    then show False by(simp add: \<Gamma>_def sink_out)
  qed
qed

context
  fixes f :: "'v edge current" and S
  assumes wf: "web_flow \<Gamma> f"
  and ortho: "orthogonal_current \<Gamma> f S"
  and sep: "separating \<Gamma> S"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E\<^bsub>\<Delta>\<^esub> \<Longrightarrow> capacity \<Delta> e > 0"
begin

private lemma f: "current \<Gamma> f" using wf by(rule web_flowD_current)

lemma orthogonal_leave_RF:
  assumes e: "edge \<Delta> x y"
  and x: "x \<in> (cut_of_sep S)"
  and y: "y \<notin> (cut_of_sep S)"
  shows "(x, y) \<in> S"
proof -
  from y obtain p where p: "path \<Delta> y p (sink \<Delta>)" and y': "y \<notin> fst ` \<E> S"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> fst ` \<E> S" by(auto simp add: roofed_def cut_of_sep_def \<Gamma>_def[symmetric])
  from e p have p': "path \<Delta> x (y # p) (sink \<Delta>)" ..
  from roofedD[OF x[unfolded cut_of_sep_def] this] y' bypass have "x \<in> fst ` \<E> S" by(auto simp add: \<Gamma>_def[symmetric])
  then obtain z where xz: "(x, z) \<in> \<E> S" by auto
  then obtain q b where q: "path \<Gamma> (x, z) q b" and b: "b \<in> B \<Gamma>"
    and distinct: "distinct ((x, z) # q)" and bypass': "\<And>z. z \<in> set q \<Longrightarrow> z \<notin> RF S"
    by(rule \<E>_E_RF) blast

  define p' where "p' = y # p"
  hence "p' \<noteq> []" by simp
  with p' have "path \<Gamma> (x, hd p') (zip p' (tl p')) (last (x # butlast p'), sink \<Delta>)"
    unfolding p'_def[symmetric]
  proof(induction)
    case (step x y p z)
    then show ?case
      by(cases p)(auto elim: rtrancl_path.cases intro: rtrancl_path.intros simp add: \<Gamma>_def)
  qed simp
  then have p'': "path \<Gamma> (x, y) (zip (y # p) p) (last (x # butlast (y # p)), sink \<Delta>)" (is "path _ ?y ?p ?t")
    by(simp add: p'_def)
  have "(?y # ?p) ! length p = ?t" using rtrancl_path_last[OF p'] p rtrancl_path_last[OF p]
    apply(auto split: if_split_asm simp add: nth_Cons butlast_conv_take take_Suc_conv_app_nth split: nat.split elim: rtrancl_path.cases)
    apply(simp add: last_conv_nth)
    done
  moreover have "length p < length (?y # ?p)" by simp
  ultimately have t: "?t \<in> B \<Gamma>" using rtrancl_path_nth[OF p'', of "length p - 1"] e
    by(cases p)(simp_all add: \<Gamma>_def split: if_split_asm)

  show S: "(x, y) \<in> S"
  proof(cases "x = source \<Delta>")
    case True
    from separatingD[OF separating_essential, OF sep p'' _ t] e True
    consider (z) z z' where "(z, z') \<in> set ?p" "(z, z') \<in> \<E> S" | "(x, y) \<in> S" by(auto simp add: \<Gamma>_def)
    thus ?thesis
    proof cases
      case (z z)
      hence "z \<in> set p" "z \<in> fst ` \<E> S"
        using y' by(auto dest!: set_zip_leftD intro: rev_image_eqI)
      hence False by(auto dest: bypass)
      thus ?thesis ..
    qed
  next
    case False
    have "\<exists>e. edge \<Gamma> e (x, z) \<and> f (e, (x, z)) > 0"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      then have "d_IN f (x, z) = 0" unfolding d_IN_def using currentD_outside[OF f, of _ "(x, z)"]
        by(force simp add: nn_integral_0_iff_AE AE_count_space not_less)
      moreover
      from xz have "(x, z) \<in> S" by auto
      hence "(x, z) \<in> SAT \<Gamma> f" by(rule orthogonal_currentD_SAT[OF ortho])
      with False have "d_IN f (x, z) \<ge> capacity \<Delta> (x, z)" by(auto simp add: SAT.simps \<Gamma>_def)
      ultimately have "\<not> capacity \<Delta> (x, z) > 0" by auto
      hence "\<not> edge \<Delta> x z" using capacity_pos[of "(x, z)"] by auto
      moreover with q have "b = (x, z)" by cases(auto simp add: \<Gamma>_def)
      with b have "edge \<Delta> x z" by(simp add: \<Gamma>_def)
      ultimately show False by contradiction
    qed
    then obtain u where ux: "edge \<Delta> u x" and xz': "edge \<Delta> x z" and uxz: "edge \<Gamma> (u, x) (x, z)"
      and gt0: "f ((u, x), (x, z)) > 0" by(auto simp add: \<Gamma>_def)
    have "(u, x) \<in> RF\<^sup>\<circ> S" using orthogonal_currentD_in[OF ortho, of "(x, z)" "(u, x)"] gt0 xz
      by(fastforce intro: roofed_greaterI)
    hence ux_RF: "(u, x) \<in> RF (\<E> S)" and ux_\<E>: "(u, x) \<notin> \<E> S" unfolding RF_essential by(simp_all add: roofed_circ_def)

    from ux e have "edge \<Gamma> (u, x) (x, y)" by(simp add: \<Gamma>_def)
    hence "path \<Gamma> (u, x) ((x, y) # ?p) ?t" using p'' ..
    from roofedD[OF ux_RF this t] ux_\<E>
    consider "(x, y) \<in> S" | (z) z z' where "(z, z') \<in> set ?p" "(z, z') \<in> \<E> S" by auto
    thus ?thesis
    proof cases
      case (z z)
      with bypass[of z] y' have False by(fastforce dest!: set_zip_leftD intro: rev_image_eqI)
      thus ?thesis ..
    qed
  qed
qed

lemma orthogonal_flow_of_current:
  assumes source_sink: "source \<Delta> \<noteq> sink \<Delta>"
  and sink_out: "\<And>x. \<not> edge \<Delta> (sink \<Delta>) x"
  and no_direct_edge: "\<not> edge \<Delta> (source \<Delta>) (sink \<Delta>)" \<comment> \<open>Otherwise, @{const A} and @{const B} of the web would not be disjoint.\<close>
  shows "orthogonal \<Delta> (flow_of_current \<Delta> f) (cut_of_sep S)" (is "orthogonal _ ?f ?S")
proof
  fix x y
  assume e: "edge \<Delta> x y" and "x \<in> ?S" and "y \<notin> ?S"
  then have S: "(x, y) \<in> S"by(rule orthogonal_leave_RF)

  show "?f (x, y) = capacity \<Delta> (x, y)"
  proof(cases "x = source \<Delta>")
    case False
    with orthogonal_currentD_SAT[OF ortho S]
    have "weight \<Gamma> (x, y) \<le> d_IN f (x, y)" by cases(simp_all add: \<Gamma>_def)
    with False currentD_OUT_IN[OF f, of "(x, y)"] currentD_weight_IN[OF f, of "(x, y)"]
    show ?thesis by(simp add: flow_of_current_def \<Gamma>_def max_def)
  next
    case True
    with orthogonal_currentD_A[OF ortho S] e currentD_weight_IN[OF f, of "(x, y)"] no_direct_edge
    show ?thesis by(auto simp add: flow_of_current_def \<Gamma>_def max_def)
  qed
next
  from sep source_sink sink_out have cut: "cut \<Delta> ?S" by(rule separating_cut)

  fix x y
  assume xy: "edge \<Delta> x y"
    and x: "x \<notin> ?S"
    and y: "y \<in> ?S"
  from x obtain p where p: "path \<Delta> x p (sink \<Delta>)" and x': "x \<notin> fst ` \<E> S"
    and bypass: "\<And>z. z \<in> set p \<Longrightarrow> z \<notin> fst ` \<E> S" by(auto simp add: roofed_def cut_of_sep_def)
  have source: "x \<noteq> source \<Delta>"
  proof
    assume "x = source \<Delta>"
    have "separating_network \<Delta> (fst ` \<E> S)" using sep source_sink by(rule separating_network_cut_of_sep)
    from separatingD[OF this p] \<open>x = source \<Delta>\<close> x show False
      by(auto dest: bypass intro: roofed_greaterI simp add: cut_of_sep_def)
  qed
  hence A: "(x, y) \<notin> A \<Gamma>" by(simp add: \<Gamma>_def)

  have "f ((u, v), x, y) = 0" for u v
  proof(cases "edge \<Gamma> (u, v) (x, y)")
    case False with f show ?thesis by(rule currentD_outside)
  next
    case True
    hence [simp]: "v = x" and ux: "edge \<Delta> u x" by(auto simp add: \<Gamma>_def)
    have "(x, y) \<in> RF S"
    proof
      fix q b
      assume q: "path \<Gamma> (x, y) q b" and b: "b \<in> B \<Gamma>"
      define xy where "xy = (x, y)"
      from q have "path \<Delta> (snd xy) (map snd q) (snd b)" unfolding xy_def[symmetric]
        by(induction)(auto intro: rtrancl_path.intros simp add: \<Gamma>_def)
      with b have "path \<Delta> y (map snd q) (sink \<Delta>)" by(auto simp add: xy_def \<Gamma>_def)
      from roofedD[OF y[unfolded cut_of_sep_def] this] have "\<exists>z\<in>set (y # map snd q). z \<in> ?S"
        by(auto intro: roofed_greaterI simp add: cut_of_sep_def)
      from split_list_last_prop[OF this] obtain xs z ys where decomp: "y # map snd q = xs @ z # ys"
        and z: "z \<in> ?S" and last: "\<And>z. z \<in> set ys \<Longrightarrow> z \<notin> ?S" by auto
      from decomp obtain x' xs' z'' ys' where decomp': "(x', y) # q = xs' @ (z'', z) # ys'"
        and "xs = map snd xs'" and ys: "ys = map snd ys'" and x': "xs' = [] \<Longrightarrow> x' = x"
        by(fastforce simp add: Cons_eq_append_conv map_eq_append_conv)
      from cut z have z_sink: "z \<noteq> sink \<Delta>" by cases(auto)
      then have "ys' \<noteq> []" using rtrancl_path_last[OF q] decomp' b x' q
        by(auto simp add: Cons_eq_append_conv \<Gamma>_def elim: rtrancl_path.cases)
      then obtain w z''' ys'' where ys': "ys' = (w, z''') # ys''" by(auto simp add: neq_Nil_conv)
      from q[THEN rtrancl_path_nth, of "length xs'"] decomp' ys' x' have "edge \<Gamma> (z'', z) (w, z''')"
        by(auto simp add: Cons_eq_append_conv nth_append)
      hence w: "w = z" and zz''': "edge \<Delta> z z'''" by(auto simp add: \<Gamma>_def)
      from ys' ys last[of z'''] have "z''' \<notin> ?S" by simp
      with zz''' z have "(z, z''') \<in> S" by(rule orthogonal_leave_RF)
      moreover have "(z, z''') \<in> set q" using decomp' ys' w by(auto simp add: Cons_eq_append_conv)
      ultimately show "(\<exists>z\<in>set q. z \<in> S) \<or> (x, y) \<in> S" by blast
    qed
    moreover
    have "(u, x) \<notin> RF\<^sup>\<circ> S"
    proof
      assume "(u, x) \<in> RF\<^sup>\<circ> S"
      hence ux_RF: "(u, x) \<in> RF (\<E> S)" and ux_\<E>: "(u, x) \<notin> \<E> S"
        unfolding RF_essential by(simp_all add: roofed_circ_def)

      have "x \<noteq> sink \<Delta>" using p xy by cases(auto simp add: sink_out)
      with p have nNil: "p \<noteq> []" by(auto elim: rtrancl_path.cases)
      with p have "edge \<Delta> x (hd p)" by cases auto
      with ux have "edge \<Gamma> (u, x) (x, hd p)" by(simp add: \<Gamma>_def)
      moreover
      from p nNil have "path \<Gamma> (x, hd p) (zip p (tl p)) (last (x # butlast p), sink \<Delta>)" (is "path _ ?x ?p ?t")
      proof(induction)
        case (step x y p z)
        then show ?case
          by(cases p)(auto elim: rtrancl_path.cases intro: rtrancl_path.intros simp add: \<Gamma>_def)
      qed simp
      ultimately have p': "path \<Gamma> (u, x) (?x # ?p) ?t" ..

      have "(?x # ?p) ! (length p - 1) = ?t" using rtrancl_path_last[OF p] p nNil
        apply(auto split: if_split_asm simp add: nth_Cons butlast_conv_take take_Suc_conv_app_nth not_le split: nat.split elim: rtrancl_path.cases)
        apply(simp add: last_conv_nth nth_tl)
        done
      moreover have "length p - 1 < length (?x # ?p)" by simp
      ultimately have t: "?t \<in> B \<Gamma>" using rtrancl_path_nth[OF p', of "length p - 1"]
        by(cases p)(simp_all add: \<Gamma>_def split: if_split_asm)
      from roofedD[OF ux_RF p' t] ux_\<E> consider (X) "(x, hd p) \<in> \<E> S"
        | (z) z z' where "(z, z') \<in> set (zip p (tl p))" "(z, z') \<in> \<E> S" by auto
      thus False
      proof cases
        case X with x' show False by(auto simp add: cut_of_sep_def intro: rev_image_eqI)
      next
        case (z z)
        with bypass[of z] show False by(auto 4 3 simp add: cut_of_sep_def intro: rev_image_eqI dest!: set_zip_leftD)
      qed
    qed
    ultimately show ?thesis unfolding \<open>v = x\<close> by(rule orthogonal_currentD_in[OF ortho])
  qed
  then have "d_IN f (x, y) = 0" unfolding d_IN_def
    by(simp add: nn_integral_0_iff emeasure_count_space_eq_0)
  with currentD_OUT_IN[OF f A] show "flow_of_current \<Delta> f (x, y) = 0"
    by(simp add: flow_of_current_def max_def)
qed

end

end

subsection \<open>The theorem\<close>

context antiparallel_edges begin

abbreviation cut' :: "'a vertex set \<Rightarrow> 'a set" where "cut' S \<equiv> Vertex -` S"

lemma cut_cut': "cut \<Delta>'' S \<Longrightarrow> cut \<Delta> (cut' S)"
by(auto simp add: cut.simps)

lemma IN_Edge: "\<^bold>I\<^bold>N\<^bsub>\<Delta>''\<^esub> (Edge x y) = (if edge \<Delta> x y then {Vertex x} else {})"
by(auto simp add: incoming_def)

lemma OUT_Edge: "\<^bold>O\<^bold>U\<^bold>T\<^bsub>\<Delta>''\<^esub> (Edge x y) = (if edge \<Delta> x y then {Vertex y} else {})"
by(auto simp add: outgoing_def)

interpretation \<Delta>'': countable_network \<Delta>'' by(rule \<Delta>''_countable_network)

lemma d_IN_Edge:
  assumes f: "flow \<Delta>'' f"
  shows "d_IN f (Edge x y) = f (Vertex x, Edge x y)"
by(subst d_IN_alt_def[OF \<Delta>''.flowD_outside[OF f], of _ \<Delta>''])(simp_all add: IN_Edge nn_integral_count_space_indicator max_def \<Delta>''.flowD_outside[OF f])

lemma d_OUT_Edge:
  assumes f: "flow \<Delta>'' f"
  shows "d_OUT f (Edge x y) = f (Edge x y, Vertex y)"
by(subst d_OUT_alt_def[OF \<Delta>''.flowD_outside[OF f], of _ \<Delta>''])(simp_all add: OUT_Edge nn_integral_count_space_indicator max_def \<Delta>''.flowD_outside[OF f])

lemma orthogonal_cut':
  assumes ortho: "orthogonal \<Delta>'' f S"
  and f: "flow \<Delta>'' f"
  shows "orthogonal \<Delta> (collect f) (cut' S)"
proof
  show "collect f (x, y) = capacity \<Delta> (x, y)" if edge: "edge \<Delta> x y" and x: "x \<in> cut' S" and y: "y \<notin> cut' S" for x y
  proof(cases "Edge x y \<in> S")
    case True
    from y have "Vertex y \<notin> S" by auto
    from orthogonalD_out[OF ortho _ True this] edge show ?thesis by simp
  next
    case False
    from x have "Vertex x \<in> S" by auto
    from orthogonalD_out[OF ortho _ this False] edge
    have "capacity \<Delta> (x, y) = d_IN f (Edge x y)" by(simp add: d_IN_Edge[OF f])
    also have "\<dots> = d_OUT f (Edge x y)" by(simp add: flowD_KIR[OF f])
    also have "\<dots> = f (Edge x y, Vertex y)" using edge by(simp add: d_OUT_Edge[OF f])
    finally show ?thesis by simp
  qed

  show "collect f (x, y) = 0" if edge: "edge \<Delta> x y" and x: "x \<notin> cut' S" and y: "y \<in> cut' S" for x y
  proof(cases "Edge x y \<in> S")
    case True
    from x have "Vertex x \<notin> S" by auto
    from orthogonalD_in[OF ortho _ this True] edge have "0 = d_IN f (Edge x y)" by(simp add: d_IN_Edge[OF f])
    also have "\<dots> = d_OUT f (Edge x y)" by(simp add: flowD_KIR[OF f])
    also have "\<dots> = f (Edge x y, Vertex y)" using edge by(simp add: d_OUT_Edge[OF f])
    finally show ?thesis by simp
  next
    case False
    from y have "Vertex y \<in> S" by auto
    from orthogonalD_in[OF ortho _ False this] edge show ?thesis by simp
  qed
qed

end

context countable_network begin

context begin

qualified lemma max_flow_min_cut':
  assumes source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and undead: "\<And>x y. edge \<Delta> x y \<Longrightarrow> (\<exists>z. edge \<Delta> y z) \<or> (\<exists>z. edge \<Delta> z x)"
  and source_sink: "\<not> edge \<Delta> (source \<Delta>) (sink \<Delta>)"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  and edge_antiparallel: "\<And>x y. edge \<Delta> x y \<Longrightarrow> \<not> edge \<Delta> y x"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E \<Longrightarrow> capacity \<Delta> e > 0"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  let ?\<Gamma> = "web_of_network \<Delta>"
  interpret web: countable_web ?\<Gamma>
  proof
    show "\<not> edge ?\<Gamma> y x" if "x \<in> A ?\<Gamma>" for x y using that by(clarsimp simp add: source_in)
    show "\<not> edge ?\<Gamma> x y" if "x \<in> B ?\<Gamma>" for x y using that by(clarsimp simp add: sink_out)
    show "A ?\<Gamma> \<subseteq> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" by(auto 4 3 dest: undead)
    show "A ?\<Gamma> \<inter> B ?\<Gamma> = {}" using source_sink by auto
    show "\<not> edge ?\<Gamma> x x" for x by(auto simp add: no_loop)
    show "weight ?\<Gamma> x = 0" if "x \<notin> \<^bold>V\<^bsub>?\<Gamma>\<^esub>" for x using that undead
      by(cases x)(auto intro!: capacity_outside)
    show "weight ?\<Gamma> x \<noteq> \<top>" for x using capacity_finite[of x] by(cases x) simp
    show "\<not> edge ?\<Gamma> y x" if "edge ?\<Gamma> x y" for x y using that by(auto simp add: edge_antiparallel)
    have "\<^bold>E\<^bsub>?\<Gamma>\<^esub> \<subseteq> \<^bold>E \<times> \<^bold>E" by auto
    thus "countable \<^bold>E\<^bsub>?\<Gamma>\<^esub>" by(rule countable_subset)(simp)
  qed
  from web.ex_orthogonal_current obtain f S
    where f: "web_flow (web_of_network \<Delta>) f"
    and S: "separating (web_of_network \<Delta>) S"
    and ortho: "orthogonal_current (web_of_network \<Delta>) f S" by blast+
  let ?f = "flow_of_current \<Delta> f" and ?S = "cut_of_sep \<Delta> S"
  from f have "flow \<Delta> ?f" by(rule flow_flow_of_current)
  moreover have "cut \<Delta> ?S" using S source_neq_sink sink_out by(rule separating_cut)
  moreover have "orthogonal \<Delta> ?f ?S" using f ortho S capacity_pos source_neq_sink sink_out source_sink
    by(rule orthogonal_flow_of_current)
  ultimately show ?thesis by blast
qed

qualified lemma max_flow_min_cut'':
  assumes sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and no_loop: "\<And>x. \<not> edge \<Delta> x x"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E \<Longrightarrow> capacity \<Delta> e > 0"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  interpret antiparallel_edges \<Delta> ..
  interpret \<Delta>'': countable_network \<Delta>'' by(rule \<Delta>''_countable_network)
  have "\<exists>f S. flow \<Delta>'' f \<and> cut \<Delta>'' S \<and> orthogonal \<Delta>'' f S"
    by(rule \<Delta>''.max_flow_min_cut')(auto simp add: sink_out source_in no_loop capacity_pos elim: edg.cases)
  then obtain f S where f: "flow \<Delta>'' f" and cut: "cut \<Delta>'' S" and ortho: "orthogonal \<Delta>'' f S" by blast
  have "flow \<Delta> (collect f)" using f by(rule flow_collect)
  moreover have "cut \<Delta> (cut' S)" using cut by(rule cut_cut')
  moreover have "orthogonal \<Delta> (collect f) (cut' S)" using ortho f by(rule orthogonal_cut')
  ultimately show ?thesis by blast
qed

qualified lemma max_flow_min_cut''':
  assumes sink_out: "\<And>y. \<not> edge \<Delta> (sink \<Delta>) y"
  and source_in: "\<And>x. \<not> edge \<Delta> x (source \<Delta>)"
  and capacity_pos: "\<And>e. e \<in> \<^bold>E \<Longrightarrow> capacity \<Delta> e > 0"
  shows "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  interpret antiparallel_edges \<Delta> ..
  interpret \<Delta>'': countable_network \<Delta>'' by(rule \<Delta>''_countable_network)
  have "\<exists>f S. flow \<Delta>'' f \<and> cut \<Delta>'' S \<and> orthogonal \<Delta>'' f S"
    by(rule \<Delta>''.max_flow_min_cut'')(auto simp add: sink_out source_in capacity_pos elim: edg.cases)
  then obtain f S where f: "flow \<Delta>'' f" and cut: "cut \<Delta>'' S" and ortho: "orthogonal \<Delta>'' f S" by blast
  have "flow \<Delta> (collect f)" using f by(rule flow_collect)
  moreover have "cut \<Delta> (cut' S)" using cut by(rule cut_cut')
  moreover have "orthogonal \<Delta> (collect f) (cut' S)" using ortho f by(rule orthogonal_cut')
  ultimately show ?thesis by blast
qed

theorem max_flow_min_cut:
  "\<exists>f S. flow \<Delta> f \<and> cut \<Delta> S \<and> orthogonal \<Delta> f S"
proof -
  define \<Delta>' where "\<Delta>' =
    \<lparr>edge = \<lambda>x y. edge \<Delta> x y \<and> capacity \<Delta> (x, y) > 0 \<and> y \<noteq> source \<Delta> \<and> x \<noteq> sink \<Delta>,
      capacity = \<lambda>(x, y). if x = sink \<Delta> \<or> y = source \<Delta> then 0 else capacity \<Delta> (x, y),
      source = source \<Delta>,
      sink = sink \<Delta>\<rparr>"
  have \<Delta>'_sel [simp]:
    "edge \<Delta>' x y \<longleftrightarrow> edge \<Delta> x y \<and> capacity \<Delta> (x, y) > 0 \<and> y \<noteq> source \<Delta> \<and> x \<noteq> sink \<Delta>"
    "capacity \<Delta>' (x, y) = (if x = sink \<Delta> \<or> y = source \<Delta> then 0 else capacity \<Delta> (x, y))"
    "source \<Delta>' = source \<Delta>"
    "sink \<Delta>' = sink \<Delta>"
    for x y by(simp_all add: \<Delta>'_def)

  interpret \<Delta>': countable_network \<Delta>'
  proof(unfold_locales)
    have "\<^bold>E\<^bsub>\<Delta>'\<^esub> \<subseteq> \<^bold>E" by auto
    then show "countable \<^bold>E\<^bsub>\<Delta>'\<^esub>" by(rule countable_subset) simp
    show "capacity \<Delta>' e = 0" if "e \<notin> \<^bold>E\<^bsub>\<Delta>'\<^esub>" for e
      using capacity_outside[of e] that by(auto split: if_split_asm intro: ccontr)
  qed(auto simp add: split: if_split_asm)

  have "\<exists>f S. flow \<Delta>' f \<and> cut \<Delta>' S \<and> orthogonal \<Delta>' f S" by(rule \<Delta>'.max_flow_min_cut''') auto
  then obtain f S where f: "flow \<Delta>' f" and cut: "cut \<Delta>' S" and ortho: "orthogonal \<Delta>' f S" by blast
  have "flow \<Delta> f"
  proof
    show "f e \<le> capacity \<Delta> e" for e using flowD_capacity[OF f, of e]
      by(cases e)(simp split: if_split_asm)
    show "KIR f x" if "x \<noteq> source \<Delta>" "x \<noteq> sink \<Delta>" for x using flowD_KIR[OF f, of x] that by simp
  qed
  moreover have "cut \<Delta> S" using cut by(simp add: cut.simps)
  moreover have "orthogonal \<Delta> f S"
  proof
    show "f (x, y) = capacity \<Delta> (x, y)" if edge: "edge \<Delta> x y" and x: "x \<in> S" and y: "y \<notin> S" for x y
    proof(cases "edge \<Delta>' x y")
      case True
      with orthogonalD_out[OF ortho this x y] show ?thesis by simp
    next
      case False
      from cut y x have xy: "y \<noteq> source \<Delta> \<and> x \<noteq> sink \<Delta>" by(cases) auto
      with xy edge False have "capacity \<Delta> (x, y) = 0" by simp
      with \<Delta>'.flowD_outside[OF f, of "(x, y)"] False show ?thesis by simp
    qed

    show "f (x, y) = 0" if edge: "edge \<Delta> x y" and x: "x \<notin> S" and y: "y \<in> S" for x y
      using orthogonalD_in[OF ortho _ x y] \<Delta>'.flowD_outside[OF f, of "(x, y)"]
      by(cases "edge \<Delta>' x y")simp_all
  qed
  ultimately show ?thesis by blast
qed

end

end

hide_const (open) A B weight

end
