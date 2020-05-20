theory Reachability_Analysis
imports
  Flow
  Poincare_Map
begin

lemma not_mem_eq_mem_not: "a \<notin> A \<longleftrightarrow> a \<in> - A"
  by auto

lemma continuous_orderD:
  fixes g::"'b::t2_space \<Rightarrow> 'c::order_topology"
  assumes "continuous (at x within S) g"
  shows "g x > c \<Longrightarrow> \<forall>\<^sub>F y in at x within S. g y > c"
    "g x < c \<Longrightarrow> \<forall>\<^sub>F y in at x within S. g y < c"
  using order_tendstoD[OF assms[unfolded continuous_within]]
  by auto

lemma frontier_halfspace_component_ge: "n \<noteq> 0 \<Longrightarrow> frontier {x. c \<le> x \<bullet> n} = plane n c"
  apply (subst (1) inner_commute)
  apply (subst (2) inner_commute)
  apply (subst frontier_halfspace_ge[of n c])
  by auto

lemma closed_Collect_le_within:
  fixes f g :: "'a :: topological_space \<Rightarrow> 'b::linorder_topology"
  assumes f: "continuous_on UNIV f"
    and g: "continuous_on UNIV g"
    and "closed R"
  shows "closed {x \<in> R. f x \<le> g x}"
proof -
  have *: "- R \<union> {x. g x < f x} = - {x \<in> R. f x \<le> g x}"
    by auto
  have "open (-R)" using assms by auto
  from open_Un[OF this open_Collect_less [OF g f], unfolded *]
  show ?thesis
    by (simp add: closed_open)
qed

subsection \<open>explicit representation of hyperplanes / halfspaces\<close>

datatype 'a sctn = Sctn (normal: 'a) (pstn: real)

definition "le_halfspace sctn x \<longleftrightarrow> x \<bullet> normal sctn \<le> pstn sctn"

definition "lt_halfspace sctn x \<longleftrightarrow> x \<bullet> normal sctn < pstn sctn"

definition "ge_halfspace sctn x \<longleftrightarrow> x \<bullet> normal sctn \<ge> pstn sctn"

definition "gt_halfspace sctn x \<longleftrightarrow> x \<bullet> normal sctn > pstn sctn"

definition "plane_of sctn = {x. x \<bullet> normal sctn = pstn sctn}"

definition "above_halfspace sctn = Collect (ge_halfspace sctn)"

definition "below_halfspace sctn = Collect (le_halfspace sctn)"

definition "sbelow_halfspace sctn = Collect (lt_halfspace sctn)"

definition "sabove_halfspace sctn = Collect (gt_halfspace sctn)"


subsection \<open>explicit H representation of polytopes (mind \<open>Polytopes.thy\<close>)\<close>

definition below_halfspaces
where "below_halfspaces sctns = \<Inter>(below_halfspace ` sctns)"

definition sbelow_halfspaces
where "sbelow_halfspaces sctns = \<Inter>(sbelow_halfspace ` sctns)"

definition above_halfspaces
where "above_halfspaces sctns = \<Inter>(above_halfspace ` sctns)"

definition sabove_halfspaces
where "sabove_halfspaces sctns = \<Inter>(sabove_halfspace ` sctns)"

lemmas halfspace_simps =
  above_halfspace_def
  sabove_halfspace_def
  below_halfspace_def
  sbelow_halfspace_def
  below_halfspaces_def
  sbelow_halfspaces_def
  above_halfspaces_def
  sabove_halfspaces_def
  ge_halfspace_def[abs_def]
  gt_halfspace_def[abs_def]
  le_halfspace_def[abs_def]
  lt_halfspace_def[abs_def]

subsection \<open>predicates for reachability analysis\<close>

context c1_on_open_euclidean
begin

definition flowpipe ::
  "(('a::euclidean_space) \<times> ('a \<Rightarrow>\<^sub>L 'a)) set \<Rightarrow> real \<Rightarrow> real \<Rightarrow>
   ('a \<times> ('a \<Rightarrow>\<^sub>L 'a)) set \<Rightarrow> ('a \<times> ('a \<Rightarrow>\<^sub>L 'a)) set \<Rightarrow> bool"
where "flowpipe X0 hl hu CX X1 \<longleftrightarrow> 0 \<le> hl \<and> hl \<le> hu \<and> fst ` X0 \<subseteq> X \<and> fst ` CX \<subseteq> X \<and> fst ` X1 \<subseteq> X \<and>
  (\<forall>(x0, d0) \<in> X0. \<forall>h \<in> {hl .. hu}.
    h \<in> existence_ivl0 x0 \<and> (flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> X1 \<and> (\<forall>h' \<in> {0 .. h}. (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX))"

lemma flowpipeD:
  assumes "flowpipe X0 hl hu CX X1"
  shows flowpipe_safeD: "fst ` X0 \<union> fst ` CX \<union> fst ` X1 \<subseteq> X"
    and flowpipe_nonneg: "0 \<le> hl" "hl \<le> hu"
    and flowpipe_exivl: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> (x0, d0) \<in> X0 \<Longrightarrow> h \<in> existence_ivl0 x0"
    and flowpipe_discrete: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> (x0, d0) \<in> X0 \<Longrightarrow> (flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> X1"
    and flowpipe_cont: "hl \<le> h \<Longrightarrow> h \<le> hu \<Longrightarrow> (x0, d0) \<in> X0 \<Longrightarrow> 0 \<le> h' \<Longrightarrow> h' \<le> h \<Longrightarrow> (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX"
  using assms
  by (auto simp: flowpipe_def)

lemma flowpipe_source_subset: "flowpipe X0 hl hu CX X1 \<Longrightarrow> X0 \<subseteq> CX"
  apply (auto dest: bspec[where x=hl] bspec[where x=0] simp: flowpipe_def)
  apply (drule bspec)
   apply (assumption)
  apply auto
  apply (drule bspec[where x=hl])
   apply auto
  apply (drule bspec[where x=0])
  by (auto simp: flow_initial_time_if)

definition "flowsto X0 T CX X1 \<longleftrightarrow>
  (\<forall>(x0, d0) \<in> X0. \<exists>h \<in> T. h \<in> existence_ivl0 x0 \<and> (flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> X1 \<and> (\<forall>h' \<in> open_segment 0 h. (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX))"

lemma flowsto_to_empty_iff[simp]: "flowsto a t b {} \<longleftrightarrow> a = {}"
  by (auto simp: simp: flowsto_def)

lemma flowsto_from_empty_iff[simp]: "flowsto {} t b c"
  by (auto simp: simp: flowsto_def)

lemma flowsto_empty_time_iff[simp]: "flowsto a {} b c \<longleftrightarrow> a = {}"
  by (auto simp: simp: flowsto_def)

lemma flowstoE:
  assumes "flowsto X0 T CX X1" "(x0, d0) \<in> X0"
  obtains h where "h \<in> T" "h \<in> existence_ivl0 x0" "(flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> X1"
    "\<And>h'. h' \<in> open_segment 0 h \<Longrightarrow> (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX"
  using assms
  by (auto simp: flowsto_def)

lemma flowsto_safeD: "flowsto X0 T CX X1 \<Longrightarrow> fst ` X0 \<subseteq> X"
  by (auto simp: flowsto_def split_beta' mem_existence_ivl_iv_defined)

lemma flowsto_union:
  assumes 1: "flowsto X0 T CX Y" and 2: "flowsto Z S CZ W"
  shows "flowsto (X0 \<union> Z) (T \<union> S) (CX \<union> CZ) (Y \<union> W)"
  using assms unfolding flowsto_def
  by force

lemma flowsto_subset:
  assumes "flowsto X0 T CX Y"
  assumes "Z \<subseteq> X0" "T \<subseteq> S" "CX \<subseteq> CZ" "Y \<subseteq> W"
  shows "flowsto Z S CZ W"
  unfolding flowsto_def
  using assms
  by (auto elim!: flowstoE) blast

lemmas flowsto_unionI = flowsto_subset[OF flowsto_union]

lemma flowsto_unionE:
  assumes "flowsto X0 T CX (Y \<union> Z)"
  obtains X1 X2 where "X0 = X1 \<union> X2" "flowsto X1 T CX Y" "flowsto X2 T CX Z"
proof -
  let ?X1 = "{x\<in>X0. flowsto {x} T CX Y}"
  let ?X2 = "{x\<in>X0. flowsto {x} T CX Z}"
  from assms have "X0 = ?X1 \<union> ?X2" "flowsto ?X1 T CX Y" "flowsto ?X2 T CX Z"
    by (auto simp: flowsto_def)
  thus ?thesis ..
qed

lemma flowsto_trans:
  assumes A: "flowsto A S B C" and C: "flowsto C T D E"
  shows "flowsto A {s + t |s t. s \<in> S \<and> t \<in> T} (B \<union> D \<union> C) E"
  unfolding flowsto_def
proof safe
  fix x0 d0 assume x0: "(x0, d0) \<in> A"
  from flowstoE[OF A x0]
  obtain h where h: "h \<in> S" "h \<in> existence_ivl0 x0" "(flow0 x0 h, (Dflow x0 h) o\<^sub>L d0) \<in> C"
    "\<And>h'. h' \<in> {0<--<h} \<Longrightarrow> (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> B"
    by auto
  from h(2) have x0[simp]: "x0 \<in> X" by auto
  from flowstoE[OF C \<open>_ \<in> C\<close>]
  obtain i where i: "i \<in> T" "i \<in> existence_ivl0 (flow0 x0 h)"
    "(flow0 (flow0 x0 h) i, Dflow (flow0 x0 h) i o\<^sub>L Dflow x0 h o\<^sub>L d0) \<in> E"
    "\<And>h'. h' \<in> {0<--<i} \<Longrightarrow> (flow0 (flow0 x0 h) h', Dflow (flow0 x0 h) h' o\<^sub>L (Dflow x0 h o\<^sub>L d0)) \<in> D"
    by (auto simp: ac_simps)
  have hi: "h + i \<in> existence_ivl0 x0"
    using \<open>h \<in> existence_ivl0 x0\<close> \<open>i \<in> existence_ivl0 (flow0 x0 h)\<close> existence_ivl_trans by blast
  moreover have "(flow0 x0 (h + i), Dflow x0 (h + i) o\<^sub>L d0) \<in> E"
    apply (subst flow_trans)
      apply fact apply fact
    apply (subst Dflow_trans)
      apply fact apply fact
    apply fact
    done
  moreover have "(flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> B \<union> D \<union> C" if "h'\<in>{0<--<h + i}" for h'
  proof cases
    assume "h' \<in> {0 <--< h}"
    then show ?thesis using h by simp
  next
    assume "h' \<notin> {0 <--< h}"
    with that have h': "h' - h \<in> {0 <--< i}" if "h' \<noteq> h"
      using that
      by (auto simp: open_segment_eq_real_ivl closed_segment_eq_real_ivl split: if_splits)
    from i(4)[OF this]
    show ?thesis
      apply (cases "h' = h")
      subgoal using h by force
      subgoal
        apply simp
        apply (subst (asm) flow_trans[symmetric])
        subgoal by (rule h)
        subgoal using \<open>_ \<Longrightarrow> h' - h \<in> {0<--<i}\<close> i(2) local.in_existence_between_zeroI
          apply auto
          using open_closed_segment by blast
        subgoal
          unfolding blinfun_compose_assoc[symmetric]
          apply (subst (asm) Dflow_trans[symmetric])
            apply auto
           apply fact+
          done
        done
      done
  qed
  ultimately show "\<exists>h\<in>{s + t |s t. s \<in> S \<and> t \<in> T}.
      h \<in> existence_ivl0 x0 \<and> (flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> E \<and> (\<forall>h'\<in>{0<--<h}. (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> B \<union> D \<union> C)"
    using \<open>h \<in> S\<close> \<open>i \<in> T\<close>
    by (auto intro!: bexI[where x="h + i"])
qed

lemma flowsto_step:
  assumes A: "flowsto A S B C"
  assumes D: "flowsto D T E F"
  shows "flowsto A (S \<union> {s + t |s t. s \<in> S \<and> t \<in> T}) (B \<union> E \<union> C \<inter> D) (C - D \<union> F)"
proof -
  have "C = (C \<inter> D) \<union> (C - D)" (is "_ = ?C1 \<union> ?C2")
    by auto
  then have "flowsto A S B (?C1 \<union> ?C2)" using A by simp
  from flowsto_unionE[OF this]
  obtain A1 A2 where "A = A1 \<union> A2" and A1: "flowsto A1 S B ?C1" and A2: "flowsto A2 S B ?C2"
    by auto
  have "flowsto ?C1 T E F"
    using D by (rule flowsto_subset) auto
  from flowsto_union[OF flowsto_trans[OF A1 this] A2]
  show ?thesis by (auto simp add: \<open>A = _\<close> ac_simps)
qed

lemma
  flowsto_stepI:
    "flowsto X0 U B C \<Longrightarrow>
    flowsto D T E F \<Longrightarrow>
    Z \<subseteq> X0 \<Longrightarrow>
    (\<And>s. s \<in> U \<Longrightarrow> s \<in> S) \<Longrightarrow>
    (\<And>s t. s \<in> U \<Longrightarrow> t \<in> T \<Longrightarrow> s + t \<in> S) \<Longrightarrow>
    B \<union> E \<union> D \<inter> C \<subseteq> CZ \<Longrightarrow> C - D \<union> F \<subseteq> W \<Longrightarrow> flowsto Z S CZ W"
  by (rule flowsto_subset[OF flowsto_step]) auto

lemma flowsto_imp_flowsto:
  "flowpipe Y h h CY Z \<Longrightarrow> flowsto Y {h} (CY) Z"
  unfolding flowpipe_def flowsto_def
  by (auto simp: open_segment_eq_real_ivl split_beta')

lemma connected_below_halfspace:
  assumes "x \<in> below_halfspace sctn"
  assumes "x \<in> S" "connected S"
  assumes "S \<inter> plane_of sctn = {}"
  shows "S \<subseteq> below_halfspace sctn"
proof -
  note \<open>connected S\<close>
  moreover
  have "open {x. x \<bullet> normal sctn < pstn sctn}" (is "open ?X")
    and "open {x. x \<bullet> normal sctn > pstn sctn}" (is "open ?Y")
    by (auto intro!: open_Collect_less continuous_intros)
  moreover have "?X \<inter> ?Y \<inter> S = {}" "S \<subseteq> ?X \<union> ?Y"
    using assms by (auto simp: plane_of_def)
  ultimately have "?X \<inter> S = {} \<or> ?Y \<inter> S = {}"
    by (rule connectedD)
  then show ?thesis
    using assms
    by (force simp: below_halfspace_def le_halfspace_def plane_of_def)
qed

lemma
  inter_Collect_eq_empty:
  assumes "\<And>x. x \<in> X0 \<Longrightarrow> \<not> g x" shows "X0 \<inter> Collect g = {}"
  using assms by auto


subsection \<open>Poincare Map\<close>

lemma closed_plane_of[simp]: "closed (plane_of sctn)"
  by (auto simp: plane_of_def intro!: closed_Collect_eq continuous_intros)

definition "poincare_mapsto P X0 S CX Y \<longleftrightarrow> (\<forall>(x, d) \<in> X0.
  returns_to P x \<and> fst ` X0 \<subseteq> S \<and>
  (return_time P differentiable at x within S) \<and>
  (\<exists>D. (poincare_map P has_derivative blinfun_apply D) (at x within S) \<and>
       (poincare_map P x, D o\<^sub>L d) \<in> Y) \<and>
  (\<forall>t\<in>{0<..<return_time P x}. flow0 x t \<in> CX))"

lemma poincare_mapsto_empty[simp]:
  "poincare_mapsto P {} S CX Y"
  by (auto simp: poincare_mapsto_def)

lemma flowsto_eventually_mem_cont:
  assumes "flowsto X0 T CX Y" "(x, d) \<in> X0" "T \<subseteq> {0<..}"
  shows "\<forall>\<^sub>F t in at_right 0. (flow0 x t, Dflow x t o\<^sub>L d) \<in> CX"
proof -
  from flowstoE[OF assms(1,2)] assms(3)
  obtain h where h: "0 < h" "h \<in> T" "h \<in> existence_ivl0 x" "(flow0 x h, (Dflow x h) o\<^sub>L d) \<in> Y" "\<And>h'. h' \<in> {0<--<h} \<Longrightarrow> (flow0 x h', (Dflow x h') o\<^sub>L d) \<in> CX"
    by (auto simp: subset_iff)
  have "\<forall>\<^sub>F x in at_right 0. 0 < x \<and> x < h"
    apply (rule eventually_conj[OF eventually_at_right_less])
    using eventually_at_right h(1) by blast
  then show ?thesis
    by eventually_elim (auto intro!: h simp: open_segment_eq_real_ivl)
qed

lemma frontier_aux_lemma:
  fixes R :: "'n::euclidean_space set"
  assumes "closed R" "R \<subseteq> {x. x \<bullet> n = c}" and [simp]: "n \<noteq> 0"
  shows "frontier {x \<in> R. c \<le> x \<bullet> n} = {x \<in> R. c = x \<bullet> n}"
  apply (auto simp: frontier_closures)
  subgoal by (metis (full_types) Collect_subset assms(1) closure_minimal subsetD)
  subgoal premises prems for x
  proof -
    note prems
    have "closed {x \<in> R. c \<le> x \<bullet> n}"
      by (auto intro!: closed_Collect_le_within continuous_intros assms)
    from closure_closed[OF this] prems(1)
    have "x \<in> R" "c \<le> x \<bullet> n" by auto
    with assms show ?thesis by auto
  qed
  subgoal for x
    using closure_subset by fastforce
  subgoal premises prems for x
  proof -
    note prems
    have *: "{xa \<in> R. x \<bullet> n \<le> xa \<bullet> n} = R"
      using assms prems by auto
    have "interior R \<subseteq> interior (plane n c)"
      by (rule interior_mono) (use assms in auto)
    also have "\<dots> = {}"
      by (subst inner_commute) simp
    finally have R: "interior R = {}" by simp
    have "x \<in> closure (- R)"
      unfolding closure_complement
      by (auto simp: R)
    then show ?thesis
      unfolding * by simp
  qed
  done

lemma blinfun_minus_comp_distrib: "(a - b) o\<^sub>L c = (a o\<^sub>L c) - (b o\<^sub>L c)"
  by (auto intro!: blinfun_eqI simp: blinfun.bilinear_simps)


lemma flowpipe_split_at_above_halfspace:
  assumes "flowpipe X0 hl t CX Y" "fst ` X0 \<inter> {x. x \<bullet> n \<ge> c} = {}" and [simp]: "n \<noteq> 0"
  assumes cR: "closed R" and Rs: "R \<subseteq> plane n c"
  assumes PDP: "\<And>x d. (x, d) \<in> CX \<Longrightarrow> x \<bullet> n = c \<Longrightarrow> (x,
     d - (blinfun_scaleR_left (f (x)) o\<^sub>L (blinfun_scaleR_left (inverse (f x \<bullet> n)) o\<^sub>L (blinfun_inner_left n o\<^sub>L d)))) \<in> PDP"
  assumes PDP_nz: "\<And>x d. (x, d) \<in> PDP \<Longrightarrow> f x \<bullet> n \<noteq> 0"
  assumes PDP_inR: "\<And>x d. (x, d) \<in> PDP \<Longrightarrow> x \<in> R"
  assumes PDP_in: "\<And>x d. (x, d) \<in> PDP \<Longrightarrow> \<forall>\<^sub>F x in at x within plane n c. x \<in> R"
  obtains X1 X2 where "X0 = X1 \<union> X2"
    "flowsto X1 {0<..t} (CX \<inter> {x. x \<bullet> n < c} \<times> UNIV) (CX \<inter> {x \<in> R. x \<bullet> n = c} \<times> UNIV)"
    "flowsto X2 {hl .. t} (CX \<inter> {x. x \<bullet> n < c} \<times> UNIV) (Y \<inter> ({x. x \<bullet> n < c} \<times> UNIV))"
    "poincare_mapsto {x \<in> R. x \<bullet> n = c} X1 UNIV (fst ` CX \<inter> {x. x \<bullet> n < c}) PDP"
proof -
  let ?sB = "{x. x \<bullet> n < c}"
  let ?A = "{x. x \<bullet> n \<ge> c}"
  let ?P = "{x \<in> R. x \<bullet> n = c}"
  have [intro]: "closed ?A" "closed ?P"
    by (auto intro!: closed_Collect_le_within closed_levelset_within continuous_intros cR
        closed_halfspace_component_ge)
  let ?CX = "CX \<inter> ?sB \<times> UNIV"
  let ?X1 = "{x\<in>X0. flowsto {x} {0 <.. t} ?CX (CX \<inter> (?P \<times> UNIV))}"
  let ?X2 = "{x\<in>X0. flowsto {x} {hl .. t} ?CX (Y \<inter> (?sB \<times> UNIV))}"
  have "(x, d) \<in> ?X1 \<or> (x, d) \<in> ?X2" if "(x, d) \<in> X0" for x d
  proof -
    from that assms have
      t: "t \<in> existence_ivl0 x" "\<And>s. 0 \<le> s \<Longrightarrow> s \<le> t \<Longrightarrow> (flow0 x s, Dflow x s o\<^sub>L d) \<in> CX" "(flow0 x t, Dflow x t o\<^sub>L d) \<in> Y"
        apply (auto simp: flowpipe_def dest!: bspec[where x=t])
      apply (drule bspec[where x="(x, d)"], assumption)
      apply simp
      apply (drule bspec[where x=t], force)
      apply auto
      done
    show ?thesis
    proof (cases "\<forall>s\<in>{0..t}. flow0 x s \<in> ?sB")
      case True
      then have "(x, d) \<in> ?X2" using assms t \<open>(x, d) \<in> X0\<close>
        by (auto simp: flowpipe_def flowsto_def open_segment_eq_real_ivl dest!: bspec[where x="(x, d)"])
      then show ?thesis ..
    next
      case False
      then obtain s where s: "0 \<le> s" "s \<le> t" "flow0 x s \<in> ?A"
        by (auto simp: not_less)
      let ?I = "flow0 x -` ?A \<inter> {0 .. s}"
      from s have exivlI: "0 \<le> s' \<Longrightarrow> s' \<le> s \<Longrightarrow> s' \<in> existence_ivl0 x" for s'
        using ivl_subset_existence_ivl[OF \<open>t \<in> existence_ivl0 x\<close>]
        by auto
      then have "compact ?I"
        unfolding compact_eq_bounded_closed
        by (intro conjI bounded_Int bounded_closed_interval disjI2 closed_vimage_Int)
          (auto intro!: continuous_intros closed_Collect_le_within cR)
      moreover
      from s have "?I \<noteq> {}" by auto
      ultimately have "\<exists>s\<in>?I. \<forall>t\<in>?I. s \<le> t"
        by (rule compact_attains_inf)
      then obtain s' where s': "\<And>s''. 0 \<le> s'' \<Longrightarrow> s'' < s' \<Longrightarrow> flow0 x s'' \<notin> ?A"
          "flow0 x s' \<in> ?A" "0 \<le> s'" "s' \<le> s"
        by (force simp: Ball_def)
      have "flow0 x 0 = x" using local.mem_existence_ivl_iv_defined(2) t(1) by auto
      also have "\<dots> \<notin> ?A" using assms \<open>(x, d) \<in> X0\<close> by auto
      finally have "s' \<noteq> 0" using s' by auto
      then have "0 < s'" using \<open>s' \<ge> 0\<close> by simp
      have False if "flow0 x s' \<in> interior ?A"
      proof -
        from that obtain e where "e > 0" and subset: "ball (flow0 x s') e \<subseteq> ?A"
          by (auto simp: mem_interior)
        from subset have "\<forall>\<^sub>F s'' in at_left s'. ball (flow0 x s') e \<subseteq> ?A" by simp
        moreover
        from flow_continuous[OF exivlI[OF \<open>0 \<le> s'\<close> \<open>s' \<le> s\<close>]]
        have "flow0 x \<midarrow>s'\<rightarrow> flow0 x s'" unfolding isCont_def .
        from tendstoD[OF this \<open>0 < e\<close>]
        have "\<forall>\<^sub>F xa in at_left s'. dist (flow0 x xa) (flow0 x s') < e"
          using eventually_at_split by blast
        then have "\<forall>\<^sub>F s'' in at_left s'. flow0 x s'' \<in> ball (flow0 x s') e"
          by (simp add: dist_commute)
        moreover
        have "\<forall>\<^sub>F s'' in at_left s'. 0 < s''"
          using \<open>0 < s'\<close>
          using eventually_at_left by blast
        moreover
        have "\<forall>\<^sub>F s'' in at_left s'. s'' < s'"
          by (auto simp: eventually_at_filter)
        ultimately
        have "\<forall>\<^sub>F s'' in at_left s'. False"
          by eventually_elim (use s' in auto)
        then show False
          by auto
      qed
      then have "flow0 x s' \<in> frontier ?A"
        unfolding frontier_def
        using \<open>closed ?A\<close> s'
        by auto
      with s' have "(x, d) \<in> ?X1" using assms that s t \<open>0 < s'\<close>
        ivl_subset_existence_ivl[OF \<open>t \<in> existence_ivl0 x\<close>]
        frontier_subset_closed[OF \<open>closed ?A\<close>]
        apply (auto simp: flowsto_def flowpipe_def open_segment_eq_real_ivl frontier_halfspace_component_ge
            intro!:
            dest!: bspec[where x="(x, d)"]
            intro: exivlI)
        apply (safe intro!: bexI[where x=s'])
        subgoal by force
        subgoal premises prems
        proof -
          have CX: "(flow0 x s', Dflow x s' o\<^sub>L d) \<in> CX"
            using prems
            by (auto intro!: prems)
          have "flow0 x s' \<bullet> n = c" using prems by auto
          from PDP_inR[OF PDP[OF CX this]]
          show "flow0 x s' \<in> R" .
        qed
        subgoal by (auto simp: not_le)
        subgoal by force
        done
      then show ?thesis ..
    qed
  qed
  then have "X0 = ?X1 \<union> ?X2" by auto
  moreover
  have X1: "flowsto ?X1 {0 <.. t} ?CX (CX \<inter> (?P \<times> UNIV))"
    and X2: "flowsto ?X2 {hl .. t} ?CX (Y \<inter> (?sB \<times> UNIV))"
    by (auto simp: flowsto_def flowpipe_def)
  moreover
  from assms(2) X1 have "poincare_mapsto ?P ?X1 UNIV (fst ` CX \<inter> {x. x \<bullet> n < c}) PDP"
    unfolding poincare_mapsto_def flowsto_def
    apply clarsimp
    subgoal premises prems for x d t
    proof -
      note prems
      have ret: "returns_to ?P x"
        apply (rule returns_to_outsideI[where t=t])
        using prems \<open>closed ?P\<close>
        by auto
      moreover
      have ret_le: "return_time ?P x \<le> t"
        apply (rule return_time_le[OF ret _ _ \<open>0 < t\<close>])
        using prems \<open>closed ?P\<close> by auto
      from prems have CX: "(flow0 x h', (Dflow x h') o\<^sub>L d) \<in> CX" if "0 < h'" "h' \<le> t" for h'
        using that by (auto simp: open_segment_eq_real_ivl)
      have PDP: "(poincare_map ?P x, Dpoincare_map' n c R x o\<^sub>L d) \<in> PDP"
        unfolding poincare_map_def Dpoincare_map'_def
        unfolding blinfun_compose_assoc blinfun_minus_comp_distrib
        apply (rule PDP)
        using poincare_map_returns[OF ret \<open>closed ?P\<close>] ret_le
        by (auto simp: poincare_map_def intro!: CX return_time_pos ret)
      have "eventually (returns_to ({x \<in> R. x \<bullet> n - c = 0})) (at x)"
        apply (rule eventually_returns_to)
        using PDP_nz[OF PDP] assms(2) \<open>(x, d) \<in> X0\<close> cR PDP_in[OF PDP]
        by (auto intro!: ret derivative_eq_intros blinfun_inner_left.rep_eq[symmetric]
            simp: eventually_at_filter)
      moreover have "return_time ?P differentiable at x"
        apply (rule differentiableI)
        apply (rule return_time_plane_has_derivative)
        using prems ret PDP_nz[OF PDP] PDP cR PDP_in[OF PDP]
        by (auto simp: eventually_at_filter)
      moreover
      have "(\<exists>D. (poincare_map ?P has_derivative blinfun_apply D) (at x) \<and> (poincare_map ?P x, D o\<^sub>L d) \<in> PDP)"
        apply (intro exI[where x="Dpoincare_map' n c R x"])
        using prems ret PDP_nz[OF PDP] PDP cR PDP_in[OF PDP]
        by (auto simp: eventually_at_filter intro!: poincare_map_plane_has_derivative)
      moreover have
        "flow0 x h \<in> fst ` CX \<and> (c > flow0 x h \<bullet> n)"
        if "0 < h" "h < return_time ?P x" for h
        using CX[of h] ret that ret_le \<open>0 < h\<close>
        apply (auto simp: open_segment_eq_real_ivl intro!: image_eqI[where x="(flow0 x h, (Dflow x h) o\<^sub>L d)"])
        using prems
        by (auto simp add: open_segment_eq_real_ivl dest!: bspec[where x=t])
      ultimately show ?thesis
        unfolding prems(7)[symmetric]
        by force
    qed
    done
  ultimately show ?thesis ..
qed

lemma poincare_map_has_derivative_step:
  assumes Deriv: "(poincare_map P has_derivative blinfun_apply D) (at (flow0 x0 h))"
  assumes ret: "returns_to P x0"
  assumes cont: "continuous (at x0 within S) (return_time P)"
  assumes less: "0 \<le> h" "h < return_time P x0"
  assumes cP: "closed P" and x0: "x0 \<in> S"
  shows "((\<lambda>x. poincare_map P x) has_derivative (D o\<^sub>L Dflow x0 h)) (at x0 within S)"
proof (rule has_derivative_transform_eventually)
  note return_time_tendsto = cont[unfolded continuous_within, rule_format]
  have "return_time P x0 \<in> existence_ivl0 x0"
    by (auto intro!: return_time_exivl cP ret)
  from ivl_subset_existence_ivl[OF this] less
  have hex: "h \<in> existence_ivl0 x0" by auto
  from eventually_mem_existence_ivl[OF this]
  have "\<forall>\<^sub>F x in at x0 within S. h \<in> existence_ivl0 x"
    by (auto simp: eventually_at)
  moreover
  have "\<forall>\<^sub>F x in at x0 within S. h < return_time P x"
    apply (rule order_tendstoD)
     apply (rule return_time_tendsto)
    by (auto intro!: x0 less)
  moreover have evret: "eventually (returns_to P) (at x0 within S)"
    by (rule eventually_returns_to_continuousI; fact)
  ultimately
  show "\<forall>\<^sub>F x in at x0 within S. poincare_map P (flow0 x h) = poincare_map P x"
    apply eventually_elim
    apply (cases "h = 0")
    subgoal by auto
    subgoal for x
      apply (rule poincare_map_step_flow)
      using \<open>0 \<le> h\<close> return_time_least[of P x ]
      by (auto simp: \<open>closed P\<close>)
    done
  show "poincare_map P (flow0 x0 h) = poincare_map P x0"
    using less ret x0 cP hex
    apply (cases "h = 0")
    subgoal by auto
    subgoal
      apply (rule poincare_map_step_flow)
      using \<open>0 \<le> h\<close> return_time_least[of P x0] ret
      by (auto simp: \<open>closed P\<close>)
    done
  show "x0 \<in> S" by fact
  show "((\<lambda>x. poincare_map P (flow0 x h)) has_derivative blinfun_apply (D o\<^sub>L Dflow x0 h)) (at x0 within S)"
    apply (rule has_derivative_compose[where g="poincare_map P" and f="\<lambda>x. flow0 x h", OF _ Deriv,
        THEN has_derivative_eq_rhs])
    by (auto intro!: derivative_eq_intros simp: hex flowderiv_def)
qed

lemma poincare_mapsto_trans:
  assumes "poincare_mapsto p1 X0 S    CX P1"
  assumes "poincare_mapsto p2 P1 UNIV CY P2"
  assumes "CX \<union> CY \<union> fst ` P1 \<subseteq> CZ"
  assumes "p2 \<inter> (CX \<union> fst ` P1) = {}"
  assumes [intro, simp]: "closed p1"
  assumes [intro, simp]: "closed p2"
  assumes cont: "\<And>x d. (x, d) \<in> X0 \<Longrightarrow> continuous (at x within S) (return_time p2)"
  shows "poincare_mapsto p2 X0 S CZ P2"
  unfolding poincare_mapsto_def
proof (auto, goal_cases)
  fix x0 d0 assume x0: "(x0, d0) \<in> X0"
  from assms(1) x0 obtain D1 dR1 where 1:
    "returns_to p1 x0"
    "fst ` X0 \<subseteq> S"
    "(return_time p1 has_derivative dR1) (at x0 within S)"
    "(poincare_map p1 has_derivative blinfun_apply D1) (at x0 within S)"
    "(poincare_map p1 x0, D1 o\<^sub>L d0) \<in> P1"
    "\<And>t. 0 < t \<Longrightarrow> t < return_time p1 x0 \<Longrightarrow> flow0 x0 t \<in> CX"
    by (auto simp: poincare_mapsto_def differentiable_def)
  then have crt1: "continuous (at x0 within S) (return_time p1)"
    by (auto intro!: has_derivative_continuous)
  show "x0 \<in> S"
    using 1 x0 by auto
  let ?x0 = "poincare_map p1 x0"
  from assms(2) x0 \<open>_ \<in> P1\<close>
  obtain D2 dR2 where 2:
    "returns_to p2 ?x0"
    "(return_time p2 has_derivative dR2) (at ?x0)"
    "(poincare_map p2 has_derivative blinfun_apply D2) (at ?x0)"
    "(poincare_map p2 ?x0, D2 o\<^sub>L (D1 o\<^sub>L d0)) \<in> P2"
    "\<And>t. t\<in>{0<..<return_time p2 ?x0} \<Longrightarrow> flow0 ?x0 t \<in> CY"
    by (auto simp: poincare_mapsto_def differentiable_def)

  have "\<forall>\<^sub>F t in at_right 0. t < return_time p1 x0"
    by (rule order_tendstoD) (auto intro!: return_time_pos 1)
  moreover have "\<forall>\<^sub>F t in at_right 0. 0 < t"
    by (auto simp: eventually_at_filter)
  ultimately have evnotp2: "\<forall>\<^sub>F t in at_right 0. flow0 x0 t \<notin> p2"
    by eventually_elim (use assms 1 in auto)
  from 2(1)
  show ret2: "returns_to p2 x0"
    unfolding poincare_map_def
    by (rule returns_to_earlierI)
       (use evnotp2 in \<open>auto intro!: less_imp_le return_time_pos 1 return_time_exivl\<close>)
  have not_p2: "0 < t \<Longrightarrow> t \<le> return_time p1 x0 \<Longrightarrow> flow0 x0 t \<notin> p2" for t
    using 1(5) 1(6)[of t] assms(4)
    by (force simp: poincare_map_def set_eq_iff)
  have pm_eq: "poincare_map p2 x0 = poincare_map p2 (poincare_map p1 x0)"
    using not_p2
    apply (auto simp: poincare_map_def)
    apply (subst flow_trans[symmetric])
      apply (auto intro!: return_time_exivl 1 2[unfolded poincare_map_def])
    apply (subst return_time_step)
    by (auto simp: return_time_step
        intro!: return_time_exivl 1 2[unfolded poincare_map_def] return_time_pos)

  have evret2: "\<forall>\<^sub>F x in at ?x0. returns_to p2 x"
    by (auto intro!: eventually_returns_to_continuousI 2 has_derivative_continuous)

  have evret1: "\<forall>\<^sub>F x in at x0 within S. returns_to p1 x"
    by (auto intro!: eventually_returns_to_continuousI 1 has_derivative_continuous)
  moreover
  from evret2[unfolded eventually_at_topological] 2(1)
  obtain U where U: "open U" "poincare_map p1 x0 \<in> U" "\<And>x. x \<in> U \<Longrightarrow> returns_to p2 x"
    by force
  have "continuous (at x0 within S) (poincare_map p1)"
    by (rule has_derivative_continuous) (rule 1)
  note [tendsto_intros] = this[unfolded continuous_within]
  have "eventually (\<lambda>x. poincare_map p1 x \<in> U) (at x0 within S)"
    by (rule topological_tendstoD) (auto intro!: tendsto_eq_intros U)
  then have evret_flow: "\<forall>\<^sub>F x in at x0 within S. returns_to p2 (flow0 x (return_time p1 x))"
    unfolding poincare_map_def[symmetric]
    apply eventually_elim
    apply (rule U)
    apply auto
    done
  moreover
  have h_less_rt: "return_time p1 x0 < return_time p2 x0"
    by (rule return_time_gt; fact)
  then have "0 < return_time p2 x0 - return_time p1 x0"
    by (simp )
  from _ this have "\<forall>\<^sub>F x in at x0 within S. 0 < return_time p2 x - return_time p1 x"
    apply (rule order_tendstoD)
    using cont \<open>(x0, _) \<in> _\<close>
    by (auto intro!: tendsto_eq_intros crt1 simp: continuous_within[symmetric] continuous_on_def)
  then have evpm2: "\<forall>\<^sub>F x in at x0 within S. \<forall>s. 0 < s \<longrightarrow> s \<le> return_time p1 x \<longrightarrow> flow0 x s \<notin> p2"
    apply eventually_elim
    apply safe
    subgoal for x s
      using return_time_least[of p2 x s]
      by (auto simp add: return_time_pos_returns_to)
    done
  ultimately
  have pm_eq_at: "\<forall>\<^sub>F x in at x0 within S.
    poincare_map p2 (poincare_map p1 x) = poincare_map p2 x"
    apply (eventually_elim)
    apply (auto simp: poincare_map_def)
    apply (subst flow_trans[symmetric])
      apply (auto intro!: return_time_exivl)
    apply (subst return_time_step)
    by (auto simp: return_time_step
        intro!: return_time_exivl return_time_pos)
  from _ this have "(poincare_map p2 has_derivative blinfun_apply (D2 o\<^sub>L D1)) (at x0 within S)"
    apply (rule has_derivative_transform_eventually)
      apply (rule has_derivative_compose[OF 1(4) 2(3), THEN has_derivative_eq_rhs])
    by (auto simp: \<open>x0 \<in> S\<close> pm_eq)
  moreover have "(poincare_map p2 x0, (D2 o\<^sub>L D1) o\<^sub>L d0) \<in> P2"
    using 2(4) unfolding pm_eq blinfun_compose_assoc .
  ultimately
  show "\<exists>D. (poincare_map p2 has_derivative blinfun_apply D) (at x0 within S) \<and>
               (poincare_map p2 x0, D o\<^sub>L d0) \<in> P2"
    by auto
  show "0 < t \<Longrightarrow> t < return_time p2 x0 \<Longrightarrow> flow0 x0 t \<in> CZ" for t
    apply (cases "t < return_time p1 x0")
    subgoal
      apply (drule 1)
      using assms
      by auto
    subgoal
      apply (cases "t = return_time p1 x0")
      subgoal using 1(5) assms by (auto simp: poincare_map_def)
      subgoal premises prems
      proof -
        have "flow0 x0 t = flow0 ?x0 (t - return_time p1 x0)"
          unfolding poincare_map_def
          apply (subst flow_trans[symmetric])
          using prems
          by (auto simp:
              intro!: return_time_exivl 1 diff_existence_ivl_trans
              less_return_time_imp_exivl[OF _ ret2])
        also have "\<dots> \<in> CY"
          apply (rule 2)
          using prems
          apply auto
          using "1"(1) "2"(1) assms poincare_map_def ret2 return_time_exivl
            return_time_least return_time_pos return_time_step
          by auto
        also have "\<dots> \<subseteq> CZ" using assms by auto
        finally show "flow0 x0 t \<in> CZ"
          by simp
      qed
      done
    done
  have rt_eq: "return_time p2 (poincare_map p1 x0) + return_time p1 x0 = return_time p2 x0"
    apply (auto simp: poincare_map_def)
    apply (subst return_time_step)
    by (auto simp: return_time_step poincare_map_def[symmetric] not_p2
        intro!: return_time_exivl return_time_pos 1 2)
  have evrt_eq: "\<forall>\<^sub>F x in at x0 within S.
    return_time p2 (poincare_map p1 x) + return_time p1 x = return_time p2 x"
    using evret_flow evret1 evpm2
    apply (eventually_elim)
    apply (auto simp: poincare_map_def)
    apply (subst return_time_step)
    by (auto simp: return_time_step
        intro!: return_time_exivl return_time_pos)
  from _ evrt_eq
  have "(return_time p2 has_derivative (\<lambda>x. dR2 (blinfun_apply D1 x) + dR1 x)) (at x0 within S)"
    by (rule has_derivative_transform_eventually)
      (auto intro!: derivative_eq_intros has_derivative_compose[OF 1(4) 2(2)] 1(3) \<open>x0 \<in> S\<close>
        simp: rt_eq)
  then show "return_time p2 differentiable at x0 within S" by (auto intro!: differentiableI)
qed

lemma flowsto_poincare_trans:\<comment> \<open>TODO: the proof is close to @{thm poincare_mapsto_trans}\<close>
  assumes f: "flowsto            X0 T     CX P1"
  assumes "poincare_mapsto p2 P1 UNIV CY P2"
  assumes nn: "\<And>t. t \<in> T \<Longrightarrow> t \<ge> 0"
  assumes "fst ` CX \<union> CY \<union> fst ` P1 \<subseteq> CZ"
  assumes "p2 \<inter> (fst ` CX \<union> fst ` P1) = {}"
  assumes [intro, simp]: "closed p2"
  assumes cont: "\<And>x d. (x, d) \<in> X0 \<Longrightarrow> continuous (at x within S) (return_time p2)"
  assumes subset: "fst ` X0 \<subseteq> S"
  shows "poincare_mapsto p2 X0 S CZ P2"
  unfolding poincare_mapsto_def
proof (auto, goal_cases)
  fix x0 d0 assume x0: "(x0, d0) \<in> X0"
  from flowstoE[OF f x0] obtain h where 1:
    "h \<in> T" "h \<in> existence_ivl0 x0"
    "(flow0 x0 h, Dflow x0 h o\<^sub>L d0) \<in> P1" (is "(?x0, _) \<in> _")
    "(\<And>h'. h' \<in> {0<--<h} \<Longrightarrow> (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX)"
    by auto
  then have CX: "(\<And>h'. 0 < h' \<Longrightarrow> h' < h \<Longrightarrow> (flow0 x0 h', Dflow x0 h' o\<^sub>L d0) \<in> CX)"
    by (auto simp: nn open_segment_eq_real_ivl)
  from 1 have "0 \<le> h" by (auto simp: nn)
  from assms have CX_p2D: "x \<in> CX \<Longrightarrow> fst x \<notin> p2" for x by auto
  from assms have P1_p2D: "x \<in> P1 \<Longrightarrow> fst x \<notin> p2" for x by auto
  show "x0 \<in> S"
    using x0 1 subset by auto
  let ?D1 = "Dflow x0 h"
  from assms(2) x0 \<open>_ \<in> P1\<close>
  obtain D2 dR2 where 2:
    "returns_to p2 ?x0"
    "(return_time p2 has_derivative dR2) (at ?x0)"
    "(poincare_map p2 has_derivative blinfun_apply D2) (at ?x0)"
    "(poincare_map p2 ?x0, D2 o\<^sub>L (?D1 o\<^sub>L d0)) \<in> P2"
    "\<And>t. t\<in>{0<..<return_time p2 ?x0} \<Longrightarrow> flow0 ?x0 t \<in> CY"
    by (auto simp: poincare_mapsto_def differentiable_def)

  {
    assume pos: "h > 0"
    have "\<forall>\<^sub>F t in at_right 0. t < h"
      by (rule order_tendstoD) (auto intro!: return_time_pos 1 pos)
    moreover have "\<forall>\<^sub>F t in at_right 0. 0 < t"
      by (auto simp: eventually_at_filter)
    ultimately have "\<forall>\<^sub>F t in at_right 0. flow0 x0 t \<notin> p2"
      by eventually_elim (use assms in \<open>force dest: CX CX_p2D\<close>)
  } note evnotp2 = this
  from 2(1)
  show ret2: "returns_to p2 x0"
    apply (cases "h = 0")
    subgoal using 1 by auto
    unfolding poincare_map_def
    by (rule returns_to_earlierI)
       (use evnotp2 \<open>0 \<le> h\<close> in \<open>auto intro!: less_imp_le return_time_pos 1 return_time_exivl \<close>)
  have not_p2: "0 < t \<Longrightarrow> t \<le> h \<Longrightarrow> flow0 x0 t \<notin> p2" for t
    using 1(1-3) CX[of t] assms(4) CX_p2D P1_p2D
    by (cases "h = t") (auto simp: poincare_map_def set_eq_iff subset_iff)
  have pm_eq: "poincare_map p2 x0 = poincare_map p2 ?x0"
    apply (cases "h = 0", use 1 in force)
    using not_p2 \<open>0 \<le> h\<close>
    apply (auto simp: poincare_map_def)
    apply (subst flow_trans[symmetric])
      apply (auto intro!: return_time_exivl 1 2[unfolded poincare_map_def])
    apply (subst return_time_step)
    by (auto simp: return_time_step 
        intro!: return_time_exivl 1 2[unfolded poincare_map_def] return_time_pos)

  have evret2: "\<forall>\<^sub>F x in at ?x0. returns_to p2 x"
    by (auto intro!: eventually_returns_to_continuousI 2 has_derivative_continuous)

  have "\<forall>\<^sub>F x in at x0. h \<in> existence_ivl0 x"
    by (simp add: 1 eventually_mem_existence_ivl)
  then have evex: "\<forall>\<^sub>F x in at x0 within S. h \<in> existence_ivl0 x"
    by (auto simp: eventually_at)
  moreover
  from evret2[unfolded eventually_at_topological] 2(1)
  obtain U where U: "open U" "flow0 x0 h \<in> U" "\<And>x. x \<in> U \<Longrightarrow> returns_to p2 x"
    by force
  note [tendsto_intros] = this[unfolded continuous_within]
  have "eventually (\<lambda>x. flow0 x h \<in> U) (at x0 within S)"
    by (rule topological_tendstoD) (auto intro!: tendsto_eq_intros U 1)
  then have evret_flow: "\<forall>\<^sub>F x in at x0 within S. returns_to p2 (flow0 x h)"
    unfolding poincare_map_def[symmetric]
    apply eventually_elim
    apply (rule U)
    apply auto
    done
  moreover
  have h_less_rt: "h < return_time p2 x0"
    by (rule return_time_gt; fact)
  then have "0 < return_time p2 x0 - h"
    by (simp )
  from _ this have "\<forall>\<^sub>F x in at x0 within S. 0 < return_time p2 x - h"
    apply (rule order_tendstoD)
    using cont \<open>(x0, _) \<in> _\<close>
    by (auto intro!: tendsto_eq_intros simp: continuous_within[symmetric] continuous_on_def)
  then have evpm2: "\<forall>\<^sub>F x in at x0 within S. \<forall>s. 0 < s \<longrightarrow> s \<le> h \<longrightarrow> flow0 x s \<notin> p2"
    apply eventually_elim
    apply safe
    subgoal for x s
      using return_time_least[of p2 x s]
      by (auto simp add: return_time_pos_returns_to)
    done
  ultimately
  have pm_eq_at: "\<forall>\<^sub>F x in at x0 within S.
    poincare_map p2 (flow0 x h) = poincare_map p2 x"
    apply (eventually_elim)
    apply (cases "h = 0") subgoal by auto
    apply (auto simp: poincare_map_def)
    apply (subst flow_trans[symmetric])
      apply (auto intro!: return_time_exivl)
    apply (subst return_time_step)
    using \<open>0 \<le> h\<close>
    by (auto simp: return_time_step intro!: return_time_exivl return_time_pos)
  from _ this have "(poincare_map p2 has_derivative blinfun_apply (D2 o\<^sub>L ?D1)) (at x0 within S)"
    apply (rule has_derivative_transform_eventually)
    apply (rule has_derivative_at_withinI)
    apply (rule has_derivative_compose[OF flow_has_space_derivative 2(3), THEN has_derivative_eq_rhs])
    by (auto simp: \<open>x0 \<in> S\<close> pm_eq 1)
  moreover have "(poincare_map p2 x0, (D2 o\<^sub>L ?D1) o\<^sub>L d0) \<in> P2"
    using 2(4) unfolding pm_eq blinfun_compose_assoc .
  ultimately
  show "\<exists>D. (poincare_map p2 has_derivative blinfun_apply D) (at x0 within S) \<and>
               (poincare_map p2 x0, D o\<^sub>L d0) \<in> P2"
    by auto
  show "0 < t \<Longrightarrow> t < return_time p2 x0 \<Longrightarrow> flow0 x0 t \<in> CZ" for t
    apply (cases "t < h")
    subgoal
      apply (drule CX)
      using assms
      by auto
    subgoal
      apply (cases "t = h")
      subgoal using 1 assms by (auto simp: poincare_map_def)
      subgoal premises prems
      proof -
        have "flow0 x0 t = flow0 ?x0 (t - h)"
          unfolding poincare_map_def
          apply (subst flow_trans[symmetric])
          using prems
          by (auto simp:
              intro!: return_time_exivl 1 diff_existence_ivl_trans
              less_return_time_imp_exivl[OF _ ret2])
        also have "\<dots> \<in> CY"
          apply (cases "h = 0")
          subgoal using "1"(2) "2"(5) prems(1) prems(2) by auto
          subgoal
            apply (rule 2)
            using prems
            apply auto
            apply (subst return_time_step)
                 apply (rule returns_to_laterI)
            using ret2 \<open>0 \<le> h\<close> \<open>h \<in> existence_ivl0 x0\<close> not_p2
            by auto
          done
          also have "\<dots> \<subseteq> CZ" using assms by auto
        finally show "flow0 x0 t \<in> CZ"
          by simp
      qed
      done
    done
  have rt_eq: "return_time p2 ?x0 + h = return_time p2 x0"
    apply (cases "h = 0")
    subgoal using 1 by auto
    subgoal
      apply (subst return_time_step)
      using \<open>0 \<le> h\<close>
      by (auto simp: return_time_step poincare_map_def[symmetric] not_p2
          intro!: return_time_exivl return_time_pos 1 2)
    done
  have evrt_eq: "\<forall>\<^sub>F x in at x0 within S.
    return_time p2 (flow0 x h) + h = return_time p2 x"
    using evret_flow evpm2 evex
    apply (eventually_elim)
    apply (cases "h = 0")
    subgoal using 1 by auto
    subgoal
      apply (subst return_time_step)
      using \<open>0 \<le> h\<close>
      by (auto simp: return_time_step
          intro!: return_time_exivl return_time_pos)
    done
  from _ evrt_eq
  have "(return_time p2 has_derivative (\<lambda>x. dR2 (blinfun_apply ?D1 x))) (at x0 within S)"
    apply (rule has_derivative_transform_eventually)
      apply (rule has_derivative_at_withinI)
    by (auto intro!: derivative_eq_intros has_derivative_compose[OF flow_has_space_derivative 2(2)] 1 \<open>x0 \<in> S\<close>
        simp: rt_eq)
  then show "return_time p2 differentiable at x0 within S" by (auto intro!: differentiableI)
qed



subsection \<open>conditions for continuous return time\<close>


definition "section s Ds S \<longleftrightarrow>
  (\<forall>x. (s has_derivative blinfun_apply (Ds x)) (at x)) \<and>
  (\<forall>x. isCont Ds x) \<and>
  (\<forall>x \<in> S. s x = (0::real) \<longrightarrow> Ds x (f x) \<noteq> 0) \<and>
  closed S \<and> S \<subseteq> X"

lemma sectionD:
  assumes "section s Ds S"
  shows "(s has_derivative blinfun_apply (Ds x)) (at x)"
    "isCont Ds x"
    "x \<in> S \<Longrightarrow> s x = 0 \<Longrightarrow> Ds x (f x) \<noteq> 0"
    "closed S" "S \<subseteq> X"
  using assms by (auto simp: section_def)

definition "transversal p \<longleftrightarrow> (\<forall>x \<in> p. \<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> p)"

lemma transversalD: "transversal p \<Longrightarrow> x \<in> p \<Longrightarrow> \<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> p"
  by (auto simp: transversal_def)

lemma transversal_section:
  fixes c::real
  assumes "section s Ds S"
  shows "transversal {x \<in> S. s x = 0}"
  using assms
  unfolding section_def transversal_def
proof (safe, goal_cases)
  case (1 x)
  then have "x \<in> X" by auto
  have "\<forall>\<^sub>F t in at_right 0. flow0 x t \<notin> {xa \<in> S. s xa = 0}"
    by (rule flow_avoids_surface_eventually_at_right)
      (rule disjI2 assms 1[rule_format] refl \<open>x \<in> X\<close>)+
  then show ?case
    by simp
qed

lemma section_closed[intro, simp]: "section s Ds S \<Longrightarrow> closed {x \<in> S. s x = 0}"
  by (auto intro!: closed_levelset_within simp: section_def
      intro!: has_derivative_continuous_on has_derivative_at_withinI[where s=S])


lemma return_time_continuous_belowI:
  assumes ft: "flowsto X0 T CX X1"
  assumes pos: "\<And>t. t \<in> T \<Longrightarrow> t > 0"
  assumes X0: "fst ` X0 \<subseteq> {x \<in> S. s x = 0}"
  assumes CX: "fst ` CX \<inter> {x \<in> S. s x = 0} = {}"
  assumes X1: "fst ` X1 \<subseteq> {x \<in> S. s x = 0}"
  assumes sec: "section s Ds S"
  assumes nz: "\<And>x. x \<in> S \<Longrightarrow> s x = 0 \<Longrightarrow> Ds x (f x) \<noteq> 0"
  assumes Dneg: "(\<lambda>x. (Ds x) (f x)) ` fst ` X0 \<subseteq> {..<0}"
  assumes rel_int: "\<And>x. x \<in> fst ` X1 \<Longrightarrow> \<forall>\<^sub>F x in at x. s x = 0 \<longrightarrow> x \<in> S"
  assumes "(x, d) \<in> X0"
  shows "continuous (at x within {x. s x \<le> 0}) (return_time {x \<in> S. s x = 0})"
proof (rule return_time_continuous_below)
  from assms have "x \<in> S" "s x = 0" "x \<in> {x \<in> S. s x = 0}" by auto
  note cs = section_closed[OF sec]
  note sectionD[OF sec]
  from flowstoE[OF ft \<open>(x, d) \<in> X0\<close>] obtain h
    where h: "h \<in> T"
      "h \<in> existence_ivl0 x"
      "(flow0 x h, Dflow x h o\<^sub>L d) \<in> X1"
      "(\<And>h'. h' \<in> {0<--<h} \<Longrightarrow> (flow0 x h', Dflow x h' o\<^sub>L d) \<in> CX)"
    by blast
  show ret: "returns_to {x \<in> S. s x = 0} x"
    apply (rule returns_toI)
        apply (rule pos)
        apply (rule h)
    subgoal by (rule h)
    subgoal using h(3) X1 by auto
    subgoal apply (intro transversalD) apply (rule transversal_section) apply (rule sec)
      apply fact
      done
    subgoal by fact
    done
  show "(s has_derivative blinfun_apply (Ds x)) (at x)" for x by fact
  show "closed S" by fact
  show "isCont Ds x" for x by fact
  show "x \<in> S" "s x = 0" by fact+
  let ?p = "poincare_map {x \<in> S. s x = 0} x"
  have "?p \<in> {x \<in> S. s x = 0}" using poincare_map_returns[OF ret cs] .
  with nz show "Ds ?p (f ?p) \<noteq> 0" by auto
  from Dneg \<open>(x, _) \<in> X0\<close> show "Ds x (f x) < 0" by force
  from \<open>_ \<in> X1\<close> X1 CX h
  have "return_time {x \<in> S. s x = 0} x = h"
    by (fastforce intro!: return_time_eqI cs pos h simp: open_segment_eq_real_ivl)
  then have "?p \<in> fst ` X1"
    using \<open>_ \<in> X1\<close> by (force simp: poincare_map_def)
  from rel_int[OF this] show " \<forall>\<^sub>F x in at (poincare_map {x \<in> S. s x = 0} x). s x = 0 \<longrightarrow> x \<in> S"
    by auto
qed

end

end
