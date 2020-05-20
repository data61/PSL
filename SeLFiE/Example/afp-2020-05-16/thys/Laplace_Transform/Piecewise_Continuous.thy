section \<open>Piecewise Continous Functions\<close>
theory Piecewise_Continuous
  imports
    Laplace_Transform_Library
begin

subsection \<open>at within filters\<close>

lemma at_within_self_singleton[simp]: "at i within {i} = bot"
  by (auto intro!: antisym filter_leI simp: eventually_at_filter)

lemma at_within_t1_space_avoid:
  "(at x within X - {i}) = (at x within X)" if "x \<noteq> i" for x i::"'a::t1_space"
proof (safe intro!: antisym filter_leI)
  fix P
  assume "eventually P (at x within X - {i})"
  moreover have "eventually (\<lambda>x. x \<noteq> i) (nhds x)"
    by (rule t1_space_nhds) fact
  ultimately
  show "eventually P (at x within X)"
    unfolding eventually_at_filter
    by eventually_elim auto
qed (simp add: eventually_mono order.order_iff_strict eventually_at_filter)

lemma at_within_t1_space_avoid_finite:
  "(at x within X - I) = (at x within X)" if "finite I" "x \<notin> I" for x::"'a::t1_space"
  using that
proof (induction I)
  case (insert i I)
  then show ?case
    by auto (metis Diff_insert at_within_t1_space_avoid)
qed simp

lemma at_within_interior:
  "NO_MATCH (UNIV::'a set) (S::'a::topological_space set) \<Longrightarrow> x \<in> interior S \<Longrightarrow> at x within S = at x"
  by (rule at_within_interior)


subsection \<open>intervals\<close>

lemma Compl_Icc: "- {a .. b} = {..<a} \<union> {b<..}" for a b::"'a::linorder"
  by auto

lemma interior_Icc[simp]: "interior {a..b} = {a<..<b}"
  for a b::"'a::{linorder_topology, dense_order, no_bot, no_top}"
    \<comment> \<open>TODO: is \<open>no_bot\<close> and \<open>no_top\<close> really required?\<close>
  by (auto simp add: Compl_Icc interior_closure)

lemma closure_finite[simp]: "closure X = X" if "finite X" for X::"'a::t1_space set"
  using that
  by (induction X) (simp_all add: closure_insert)

definition piecewise_continuous_on :: "'a::linorder_topology \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> ('a \<Rightarrow> 'b::topological_space) \<Rightarrow> bool"
where "piecewise_continuous_on a b I f \<longleftrightarrow>
  (continuous_on ({a .. b} - I) f \<and> finite I \<and>
    (\<forall>i\<in>I. (i \<in> {a<..b} \<longrightarrow> (\<exists>l. (f \<longlongrightarrow> l) (at_left i))) \<and>
      (i \<in> {a..<b} \<longrightarrow> (\<exists>u. (f \<longlongrightarrow> u) (at_right i)))))"

lemma piecewise_continuous_on_subset:
  "piecewise_continuous_on a b I f \<Longrightarrow> {c .. d} \<subseteq> {a .. b} \<Longrightarrow> piecewise_continuous_on c d I f"
  by (force simp add: piecewise_continuous_on_def intro: continuous_on_subset)

lemma piecewise_continuous_onE:
  assumes "piecewise_continuous_on a b I f"
  obtains l u
  where "finite I"
      and "continuous_on ({a..b} - I) f"
      and "(\<And>i. i \<in> I \<Longrightarrow> a < i \<Longrightarrow> i \<le> b \<Longrightarrow> (f \<longlongrightarrow> l i) (at_left i))"
      and "(\<And>i. i \<in> I \<Longrightarrow> a \<le> i \<Longrightarrow> i < b \<Longrightarrow> (f \<longlongrightarrow> u i) (at_right i))"
  using assms
  by (auto simp: piecewise_continuous_on_def Ball_def) metis

lemma piecewise_continuous_onI:
  assumes "finite I" "continuous_on ({a..b} - I) f"
    and "(\<And>i. i \<in> I \<Longrightarrow> a < i \<Longrightarrow> i \<le> b \<Longrightarrow> (f \<longlongrightarrow> l i) (at_left i))"
    and "(\<And>i. i \<in> I \<Longrightarrow> a \<le> i \<Longrightarrow> i < b \<Longrightarrow> (f \<longlongrightarrow> u i) (at_right i))"
  shows "piecewise_continuous_on a b I f"
  using assms
  by (force simp: piecewise_continuous_on_def)

lemma piecewise_continuous_onI':
  fixes a b::"'a::{linorder_topology, dense_order, no_bot, no_top}"
  assumes "finite I" "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> isCont f x"
    and "a \<notin> I \<Longrightarrow> continuous (at_right a) f"
    and "b \<notin> I \<Longrightarrow> continuous (at_left b) f"
    and "(\<And>i. i \<in> I \<Longrightarrow> a < i \<Longrightarrow> i \<le> b \<Longrightarrow> (f \<longlongrightarrow> l i) (at_left i))"
    and "(\<And>i. i \<in> I \<Longrightarrow> a \<le> i \<Longrightarrow> i < b \<Longrightarrow> (f \<longlongrightarrow> u i) (at_right i))"
  shows "piecewise_continuous_on a b I f"
proof (rule piecewise_continuous_onI)
  have "x \<notin> I \<Longrightarrow> a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> (f \<longlongrightarrow> f x) (at x within {a..b})" for x
    using assms(2)[of x] assms(3,4)
    by (cases "a = x"; cases "b = x"; cases "x \<in> {a<..<b}")
      (auto simp: at_within_Icc_at_left at_within_Icc_at_right isCont_def
        continuous_within filterlim_at_split at_within_interior)
  then show "continuous_on ({a .. b} - I) f"
    by (auto simp: continuous_on_def \<open>finite I\<close> at_within_t1_space_avoid_finite)
qed fact+

lemma piecewise_continuous_onE':
  fixes a b::"'a::{linorder_topology, dense_order, no_bot, no_top}"
  assumes "piecewise_continuous_on a b I f"
  obtains l u
  where "finite I"
      and "\<And>x. a < x \<Longrightarrow> x < b \<Longrightarrow> x \<notin> I \<Longrightarrow> isCont f x"
      and "(\<And>x. a < x \<Longrightarrow> x \<le> b \<Longrightarrow> (f \<longlongrightarrow> l x) (at_left x))"
      and "(\<And>x. a \<le> x \<Longrightarrow> x < b \<Longrightarrow> (f \<longlongrightarrow> u x) (at_right x))"
      and "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> x \<notin> I \<Longrightarrow> f x = l x"
      and "\<And>x. a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> x \<notin> I \<Longrightarrow> f x = u x"
proof -
  from piecewise_continuous_onE[OF assms] obtain l u
    where "finite I"
      and continuous: "continuous_on ({a..b} - I) f"
      and left: "(\<And>i. i \<in> I \<Longrightarrow> a < i \<Longrightarrow> i \<le> b \<Longrightarrow> (f \<longlongrightarrow> l i) (at_left i))"
      and right: "(\<And>i. i \<in> I \<Longrightarrow> a \<le> i \<Longrightarrow> i < b \<Longrightarrow> (f \<longlongrightarrow> u i) (at_right i))"
    by metis
  define l' where "l' x = (if x \<in> I then l x else f x)" for x
  define u' where "u' x = (if x \<in> I then u x else f x)" for x
  note \<open>finite I\<close>
  moreover from continuous
  have "a < x \<Longrightarrow> x < b \<Longrightarrow> x \<notin> I \<Longrightarrow> isCont f x" for x
    by (rule continuous_on_interior) (auto simp: interior_diff \<open>finite I\<close>)
  moreover
  from continuous have "a < x \<Longrightarrow> x \<le> b \<Longrightarrow> x \<notin> I \<Longrightarrow> (f \<longlongrightarrow> f x) (at_left x)" for x
    by (cases "x = b")
     (auto simp: continuous_on_def at_within_t1_space_avoid_finite \<open>finite I\<close>
        at_within_Icc_at_left at_within_interior filterlim_at_split
        dest!: bspec[where x=x])
  then have "a < x \<Longrightarrow> x \<le> b \<Longrightarrow> (f \<longlongrightarrow> l' x) (at_left x)" for x
    by (auto simp: l'_def left)
  moreover
  from continuous have "a \<le> x \<Longrightarrow> x < b \<Longrightarrow> x \<notin> I \<Longrightarrow> (f \<longlongrightarrow> f x) (at_right x)" for x
    by (cases "x = a")
     (auto simp: continuous_on_def at_within_t1_space_avoid_finite \<open>finite I\<close>
        at_within_Icc_at_right at_within_interior filterlim_at_split
        dest!: bspec[where x=x])
  then have "a \<le> x \<Longrightarrow> x < b \<Longrightarrow> (f \<longlongrightarrow> u' x) (at_right x)" for x
    by (auto simp: u'_def right)
  moreover have "a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> x \<notin> I \<Longrightarrow> f x = l' x" for x by (auto simp: l'_def)
  moreover have "a \<le> x \<Longrightarrow> x \<le> b \<Longrightarrow> x \<notin> I \<Longrightarrow> f x = u' x" for x by (auto simp: u'_def)
  ultimately show ?thesis ..
qed

lemma tendsto_avoid_at_within:
  "(f \<longlongrightarrow> l) (at x within X)"
  if "(f \<longlongrightarrow> l) (at x within X - {x})"
  using that
  by (auto simp: eventually_at_filter dest!: topological_tendstoD intro!: topological_tendstoI)

lemma tendsto_within_subset_eventuallyI:
  "(f \<longlongrightarrow> fx) (at x within X)"
  if g: "(g \<longlongrightarrow> gy) (at y within Y)"
    and ev: "\<forall>\<^sub>F x in (at y within Y). f x = g x"
    and xy: "x = y"
    and fxgy: "fx = gy"
    and XY: "X - {x} \<subseteq> Y"
  apply (rule tendsto_avoid_at_within)
  apply (rule tendsto_within_subset[where S = "Y"])
  unfolding xy
   apply (subst tendsto_cong[OF ev ])
   apply (rule g[folded fxgy])
  apply (rule XY[unfolded xy])
  done

lemma piecewise_continuous_on_insertE:
  assumes "piecewise_continuous_on a b (insert i I) f"
  assumes "i \<in> {a .. b}"
  obtains g h where
    "piecewise_continuous_on a i I g"
    "piecewise_continuous_on i b I h"
    "\<And>x. a \<le> x \<Longrightarrow> x < i \<Longrightarrow> g x = f x"
    "\<And>x. i < x \<Longrightarrow> x \<le> b \<Longrightarrow> h x = f x"
proof -
  from piecewise_continuous_onE[OF assms(1)] \<open>i \<in> {a .. b}\<close> obtain l u where
        finite: "finite I"
    and cf: "continuous_on ({a..b} - insert i I) f"
    and l: "(\<And>i. i \<in> I \<Longrightarrow> a < i \<Longrightarrow> i \<le> b \<Longrightarrow> (f \<longlongrightarrow> l i) (at_left i))" "i > a \<Longrightarrow> (f \<longlongrightarrow> l i) (at_left i)"
    and u: "(\<And>i. i \<in> I \<Longrightarrow> a \<le> i \<Longrightarrow> i < b \<Longrightarrow> (f \<longlongrightarrow> u i) (at_right i))" "i < b \<Longrightarrow> (f \<longlongrightarrow> u i) (at_right i)"
    by auto (metis (mono_tags))

  have fl: "(f(i := x) \<longlongrightarrow> l j) (at_left j)" if "j \<in> I" "a < j" "j \<le> b" for j x
    using l(1)
    apply (rule tendsto_within_subset_eventuallyI)
        apply (auto simp: eventually_at_filter that)
    apply (cases "j \<noteq> i")
    subgoal premises prems
      using t1_space_nhds[OF prems]
      by eventually_elim auto
    subgoal by simp
    done
  have fr: "(f(i := x) \<longlongrightarrow> u j) (at_right j)" if "j \<in> I" "a \<le> j" "j < b" for j x
    using u(1)
    apply (rule tendsto_within_subset_eventuallyI)
        apply (auto simp: eventually_at_filter that)
    apply (cases "j \<noteq> i")
    subgoal premises prems
      using t1_space_nhds[OF prems]
      by eventually_elim auto
    subgoal by simp
    done
  from cf have tendsto: "(f \<longlongrightarrow> f x) (at x within {a..b} - insert i I)"
    if "x \<in> {a .. b} - insert i I" for x using that
    by (auto simp: continuous_on_def)
  have "continuous_on ({a..i} - I) (f(i:=l i))"
    apply (cases "a = i")
    subgoal by (auto simp: continuous_on_def Diff_triv)
    unfolding continuous_on_def
    apply safe
    subgoal for x
      apply (cases "x = i")
      subgoal
        apply (rule tendsto_within_subset_eventuallyI)
            apply (rule l(2))
        by (auto simp: eventually_at_filter)
      subgoal
        apply (subst at_within_t1_space_avoid[symmetric], assumption)
        apply (rule tendsto_within_subset_eventuallyI[where y=x])
            apply (rule tendsto)
        using \<open>i \<in> {a .. b}\<close> by (auto simp: eventually_at_filter)
      done
    done
  then have "piecewise_continuous_on a i I (f(i:=l i))"
    using \<open>i \<in> {a .. b}\<close>
    by (auto intro!: piecewise_continuous_onI finite fl fr)

  moreover
  have "continuous_on ({i..b} - I) (f(i:=u i))"
    apply (cases "b = i")
    subgoal by (auto simp: continuous_on_def Diff_triv)
    unfolding continuous_on_def
    apply safe
    subgoal for x
      apply (cases "x = i")
      subgoal
        apply (rule tendsto_within_subset_eventuallyI)
            apply (rule u(2))
        by (auto simp: eventually_at_filter)
      subgoal
        apply (subst at_within_t1_space_avoid[symmetric], assumption)
        apply (rule tendsto_within_subset_eventuallyI[where y=x])
            apply (rule tendsto)
        using \<open>i \<in> {a .. b}\<close> by (auto simp: eventually_at_filter)
      done
    done
  then have "piecewise_continuous_on i b I (f(i:=u i))"
    using \<open>i \<in> {a .. b}\<close>
    by (auto intro!: piecewise_continuous_onI finite fl fr)
  moreover have "(f(i:=l i)) x = f x" if "a \<le> x" "x < i" for x
    using that by auto
  moreover have "(f(i:=u i)) x = f x" if "i < x" "x \<le> b" for x
    using that by auto
  ultimately show ?thesis ..
qed

lemma eventually_avoid_finite:
  "\<forall>\<^sub>F x in at y within Y. x \<notin> I" if "finite I" for y::"'a::t1_space"
  using that
proof (induction)
  case empty
  then show ?case by simp
next
  case (insert x F)
  then show ?case
    apply (auto intro!: eventually_conj)
    apply (cases "y = x")
    subgoal by (simp add: eventually_at_filter)
    subgoal by (rule tendsto_imp_eventually_ne) (rule tendsto_ident_at)
    done
qed

lemma eventually_at_left_linorder:\<comment> \<open>TODO: generalize @{thm eventually_at_left_real}\<close>
  "a > (b :: 'a :: linorder_topology) \<Longrightarrow> eventually (\<lambda>x. x \<in> {b<..<a}) (at_left a)"
  unfolding eventually_at_left
  by auto

lemma eventually_at_right_linorder:\<comment> \<open>TODO: generalize @{thm eventually_at_right_real}\<close>
  "a > (b :: 'a :: linorder_topology) \<Longrightarrow> eventually (\<lambda>x. x \<in> {b<..<a}) (at_right b)"
  unfolding eventually_at_right
  by auto

lemma piecewise_continuous_on_congI:
  "piecewise_continuous_on a b I g"
  if "piecewise_continuous_on a b I f"
    and eq: "\<And>x. x \<in> {a .. b} - I \<Longrightarrow> g x = f x"
proof -
  from piecewise_continuous_onE[OF that(1)]
  obtain l u where finite: "finite I"
    and *:
    "continuous_on ({a..b} - I) f"
    "(\<And>i. i \<in> I \<Longrightarrow> a < i \<Longrightarrow> i \<le> b \<Longrightarrow> (f \<longlongrightarrow> l i) (at_left i))"
    "\<And>i. i \<in> I \<Longrightarrow> a \<le> i \<Longrightarrow> i < b \<Longrightarrow> (f \<longlongrightarrow> u i) (at_right i)"
    by blast
  note finite
  moreover
  from * have "continuous_on ({a..b} - I) g"
    using that(2)
    by (auto simp: eq cong: continuous_on_cong) (subst continuous_on_cong[OF refl eq]; assumption)
  moreover
  have "\<forall>\<^sub>F x in at_left i. f x = g x" if "a < i" "i \<le> b" for i
    using eventually_avoid_finite[OF \<open>finite I\<close>, of i "{..<i}"]
      eventually_at_left_linorder[OF \<open>a < i\<close>]
    by eventually_elim (subst eq, use that in auto)
  then have "i \<in> I \<Longrightarrow> a < i \<Longrightarrow> i \<le> b \<Longrightarrow> (g \<longlongrightarrow> l i) (at_left i)" for i
    using *(2)
    by (rule Lim_transform_eventually[rotated]) auto
  moreover
  have "\<forall>\<^sub>F x in at_right i. f x = g x" if "a \<le> i" "i < b" for i
    using eventually_avoid_finite[OF \<open>finite I\<close>, of i "{i<..}"]
      eventually_at_right_linorder[OF \<open>i < b\<close>]
    by eventually_elim (subst eq, use that in auto)
  then have "i \<in> I \<Longrightarrow> a \<le> i \<Longrightarrow> i < b \<Longrightarrow> (g \<longlongrightarrow> u i) (at_right i)" for i
    using *(3)
    by (rule Lim_transform_eventually[rotated]) auto
  ultimately
  show ?thesis
    by (rule piecewise_continuous_onI) auto
qed

lemma piecewise_continuous_on_cong[cong]:
  "piecewise_continuous_on a b I f \<longleftrightarrow> piecewise_continuous_on c d J g"
  if "a = c"
    "b = d"
    "I = J"
    "\<And>x. c \<le> x \<Longrightarrow> x \<le> d \<Longrightarrow> x \<notin> J \<Longrightarrow> f x = g x"
  using that
  by (auto intro: piecewise_continuous_on_congI)

lemma tendsto_at_left_continuous_on_avoidI: "(f \<longlongrightarrow> g i) (at_left i)"
  if g: "continuous_on ({a..i} - I) g"
    and gf: "\<And>x. a < x \<Longrightarrow> x < i \<Longrightarrow> g x = f x"
    "i \<notin> I" "finite I" "a < i"
  for i::"'a::linorder_topology"
proof (rule Lim_transform_eventually)
  from that have "i \<in> {a .. i}" by auto
  from g have "(g \<longlongrightarrow> g i) (at i within {a..i} - I)"
    using \<open>i \<notin> I\<close> \<open>i \<in> {a .. i}\<close>
    by (auto elim!: piecewise_continuous_onE simp: continuous_on_def)
  then show "(g \<longlongrightarrow> g i) (at_left i)"
    by (metis that at_within_Icc_at_left at_within_t1_space_avoid_finite
        greaterThanLessThan_iff)
  show "\<forall>\<^sub>F x in at_left i. g x = f x"
    using eventually_at_left_linorder[OF \<open>a < i\<close>]
    by eventually_elim (auto simp: \<open>a < i\<close> gf)
qed

lemma tendsto_at_right_continuous_on_avoidI: "(f \<longlongrightarrow> g i) (at_right i)"
  if g: "continuous_on ({i..b} - I) g"
    and gf: "\<And>x. i < x \<Longrightarrow> x < b \<Longrightarrow> g x = f x"
    "i \<notin> I" "finite I" "i < b"
  for i::"'a::linorder_topology"
proof (rule Lim_transform_eventually)
  from that have "i \<in> {i .. b}" by auto
  from g have "(g \<longlongrightarrow> g i) (at i within {i..b} - I)"
    using \<open>i \<notin> I\<close> \<open>i \<in> {i .. b}\<close>
    by (auto elim!: piecewise_continuous_onE simp: continuous_on_def)
  then show "(g \<longlongrightarrow> g i) (at_right i)"
    by (metis that at_within_Icc_at_right at_within_t1_space_avoid_finite
        greaterThanLessThan_iff)
  show "\<forall>\<^sub>F x in at_right i. g x = f x"
    using eventually_at_right_linorder[OF \<open>i < b\<close>]
    by eventually_elim (auto simp: \<open>i < b\<close> gf)
qed

lemma piecewise_continuous_on_insert_leftI:
  "piecewise_continuous_on a b (insert a I) f" if "piecewise_continuous_on a b I f"
  apply (cases "a \<in> I")
  subgoal using that by (auto dest: insert_absorb)
  subgoal
    using that
    apply (rule piecewise_continuous_onE)
    subgoal for l u
      apply (rule piecewise_continuous_onI[where u="u(a:=f a)"])
         apply (auto intro: continuous_on_subset )
      apply (rule tendsto_at_right_continuous_on_avoidI, assumption)
         apply auto
      done
    done
  done

lemma piecewise_continuous_on_insert_rightI:
  "piecewise_continuous_on a b (insert b I) f" if "piecewise_continuous_on a b I f"
  apply (cases "b \<in> I")
  subgoal using that by (auto dest: insert_absorb)
  subgoal
    using that
    apply (rule piecewise_continuous_onE)
    subgoal for l u
      apply (rule piecewise_continuous_onI[where l="l(b:=f b)"])
         apply (auto intro: continuous_on_subset )
      apply (rule tendsto_at_left_continuous_on_avoidI, assumption)
         apply auto
      done
    done
  done

theorem piecewise_continuous_on_induct[consumes 1, case_names empty combine weaken]:
  assumes pc: "piecewise_continuous_on a b I f"
  assumes 1: "\<And>a b f. continuous_on {a .. b} f \<Longrightarrow> P a b {} f"
  assumes 2: "\<And>a i b I f1 f2 f. a \<le> i \<Longrightarrow> i \<le> b \<Longrightarrow> i \<notin> I \<Longrightarrow> P a i I f1 \<Longrightarrow> P i b I f2 \<Longrightarrow>
    piecewise_continuous_on a i I f1 \<Longrightarrow>
    piecewise_continuous_on i b I f2 \<Longrightarrow>
    (\<And>x. a \<le> x \<Longrightarrow> x < i \<Longrightarrow> f1 x = f x) \<Longrightarrow>
    (\<And>x. i < x \<Longrightarrow> x \<le> b \<Longrightarrow> f2 x = f x) \<Longrightarrow>
    (i > a \<Longrightarrow> (f \<longlongrightarrow> f1 i) (at_left i)) \<Longrightarrow>
    (i < b \<Longrightarrow> (f \<longlongrightarrow> f2 i) (at_right i)) \<Longrightarrow>
    P a b (insert i I) f"
  assumes 3: "\<And>a b i I f. P a b I f \<Longrightarrow> finite I \<Longrightarrow> i \<notin> I \<Longrightarrow> P a b (insert i I) f"
  shows "P a b I f"
proof -
  from pc have "finite I"
    by (auto simp: piecewise_continuous_on_def)
  then show ?thesis
    using pc
  proof (induction I arbitrary: a b f)
    case empty
    then show ?case
      by (auto simp: piecewise_continuous_on_def 1)
  next
    case (insert i I)
    show ?case
    proof (cases "i \<in> {a .. b}")
      case True
      from insert.prems[THEN piecewise_continuous_on_insertE, OF \<open>i \<in> {a .. b}\<close>]
      obtain g h
        where g: "piecewise_continuous_on a i I g"
          and h: "piecewise_continuous_on i b I h"
          and gf: "\<And>x. a \<le> x \<Longrightarrow> x < i \<Longrightarrow> g x = f x"
          and hf: "\<And>x. i < x \<Longrightarrow> x \<le> b \<Longrightarrow> h x = f x"
        by metis
      from g have pcg: "piecewise_continuous_on a i I (f(i:=g i))"
        by (rule piecewise_continuous_on_congI) (auto simp: gf)
      from h have pch: "piecewise_continuous_on i b I (f(i:=h i))"
        by (rule piecewise_continuous_on_congI) (auto simp: hf)

      have fg: "(f \<longlongrightarrow> g i) (at_left i)" if "a < i"
        apply (rule tendsto_at_left_continuous_on_avoidI[where a=a and I=I])
        using g \<open>i \<notin> I\<close> \<open>a < i\<close>
        by (auto elim!: piecewise_continuous_onE simp: gf)
      have fh: "(f \<longlongrightarrow> h i) (at_right i)" if "i < b"
        apply (rule tendsto_at_right_continuous_on_avoidI[where b=b and I=I])
        using h \<open>i \<notin> I\<close> \<open>i < b\<close>
        by (auto elim!: piecewise_continuous_onE simp: hf)
      show ?thesis
        apply (rule 2)
        using True apply force
        using True apply force
                apply (rule insert)
               apply (rule insert.IH, rule pcg)
              apply (rule insert.IH, rule pch)
             apply fact
            apply fact
        using 3
        by (auto simp: fg fh)
    next
      case False
      with insert.prems
      have "piecewise_continuous_on a b I f"
        by (auto simp: piecewise_continuous_on_def)
      from insert.IH[OF this] show ?thesis
        by (rule 3) fact+
    qed
  qed
qed

lemma continuous_on_imp_piecewise_continuous_on:
  "continuous_on {a .. b} f \<Longrightarrow> piecewise_continuous_on a b {} f"
  by (auto simp: piecewise_continuous_on_def)

lemma piecewise_continuous_on_imp_absolutely_integrable:
  fixes a b::real and f::"real \<Rightarrow> 'a::euclidean_space"
  assumes "piecewise_continuous_on a b I f"
  shows "f absolutely_integrable_on {a..b}"
  using assms
proof (induction rule: piecewise_continuous_on_induct)
  case (empty a b f)
  show ?case
    by (auto intro!: absolutely_integrable_onI integrable_continuous_interval
          continuous_intros empty)
next
  case (combine a i b I f1 f2 f)
  from combine(10)
  have "f absolutely_integrable_on {a..i}"
    by (rule absolutely_integrable_spike[where S="{i}"]) (auto simp: combine)
  moreover
  from combine(11)
  have "f absolutely_integrable_on {i..b}"
    by (rule absolutely_integrable_spike[where S="{i}"]) (auto simp: combine)
  ultimately
  show ?case
    by (rule absolutely_integrable_on_combine) fact+
qed

lemma piecewise_continuous_on_integrable:
  fixes a b::real and f::"real \<Rightarrow> 'a::euclidean_space"
  assumes "piecewise_continuous_on a b I f"
  shows "f integrable_on {a..b}"
  using piecewise_continuous_on_imp_absolutely_integrable[OF assms]
  unfolding absolutely_integrable_on_def by auto

lemma piecewise_continuous_on_comp:
  assumes p: "piecewise_continuous_on a b I f"
  assumes c: "\<And>x. isCont (\<lambda>(x, y). g x y) x"
  shows "piecewise_continuous_on a b I (\<lambda>x. g x (f x))"
proof -
  from piecewise_continuous_onE[OF p]
  obtain l u
    where I: "finite I"
      and cf: "continuous_on ({a..b} - I) f"
      and l: "(\<And>i. i \<in> I \<Longrightarrow> a < i \<Longrightarrow> i \<le> b \<Longrightarrow> (f \<longlongrightarrow> l i) (at_left i))"
      and u: "(\<And>i. i \<in> I \<Longrightarrow> a \<le> i \<Longrightarrow> i < b \<Longrightarrow> (f \<longlongrightarrow> u i) (at_right i))"
    by metis
  note \<open>finite I\<close>
  moreover
  from c have cg: "continuous_on UNIV (\<lambda>(x, y). g x y)"
    using c by (auto simp: continuous_on_def isCont_def intro: tendsto_within_subset)
  then have "continuous_on ({a..b} - I) (\<lambda>x. g x (f x))"
    by (intro continuous_on_compose2[OF cg, where f="\<lambda>x. (x, f x)", simplified])
      (auto intro!: continuous_intros cf)
  moreover
  note tendstcomp = tendsto_compose[OF c[unfolded isCont_def], where f="\<lambda>x. (x, f x)", simplified, THEN tendsto_eq_rhs]
  have "((\<lambda>x. g x (f x)) \<longlongrightarrow> g i (u i)) (at_right i)" if "i \<in> I" "a \<le> i" "i < b" for i
    by (rule tendstcomp) (auto intro!: tendsto_eq_intros u[OF \<open>i \<in> I\<close>] that)
  moreover
  have "((\<lambda>x. g x (f x)) \<longlongrightarrow> g i (l i)) (at_left i)" if "i \<in> I" "a < i" "i \<le> b" for i
    by (rule tendstcomp) (auto intro!: tendsto_eq_intros l[OF \<open>i \<in> I\<close>] that)
  ultimately show ?thesis
    by (intro piecewise_continuous_onI)
qed

lemma bounded_piecewise_continuous_image:
  "bounded (f ` {a .. b})"
  if "piecewise_continuous_on a b I f" for a b::real
  using that
proof (induction rule: piecewise_continuous_on_induct)
  case (empty a b f)
  then show ?case by (auto intro!: compact_imp_bounded compact_continuous_image)
next
  case (combine a i b I f1 f2 f)
  have "(f ` {a..b}) \<subseteq> (insert (f i) (f1 ` {a..i} \<union> f2 ` {i..b}))"
    using combine
    by (auto simp: image_iff) (metis antisym_conv atLeastAtMost_iff le_cases not_less)
  also have "bounded \<dots>"
    using combine by auto
  finally (bounded_subset[rotated]) show ?case .
qed

lemma tendsto_within_eventually:
  "(f \<longlongrightarrow> l) (at x within X)"
  if
    "(f \<longlongrightarrow> l) (at x within Y)"
    "\<forall>\<^sub>F y in at x within X. y \<in> Y"
  using _ that(1)
proof (rule tendsto_mono)
  show "at x within X \<le> at x within Y"
  proof (rule filter_leI)
    fix P
    assume "eventually P (at x within Y)"
    with that(2) show "eventually P (at x within X)"
      unfolding eventually_at_filter
      by eventually_elim auto
  qed
qed

lemma at_within_eq_bot_lemma:
  "at x within {b..c} = (if x < b \<or> b > c then bot else at x within {b..c})"
  for x b c::"'a::linorder_topology"
  by (auto intro!: not_in_closure_trivial_limitI)

lemma at_within_eq_bot_lemma2:
  "at x within {a..b} = (if x > b \<or> a > b then bot else at x within {a..b})"
  for x a b::"'a::linorder_topology"
  by (auto intro!: not_in_closure_trivial_limitI)

lemma piecewise_continuous_on_combine:
  "piecewise_continuous_on a c J f"
  if "piecewise_continuous_on a b J f" "piecewise_continuous_on b c J f"
  using that
  apply (auto elim!: piecewise_continuous_onE)
  subgoal for l u l' u'
    apply (rule piecewise_continuous_onI[where
          l="\<lambda>i. if i \<le> b then l i else l' i" and
          u="\<lambda>i. if i < b then u i else u' i"])
    subgoal by force
    subgoal
      apply (rule continuous_on_subset[where s="({a .. b} \<union> {b .. c} - J)"])
      apply (auto simp: continuous_on_def at_within_t1_space_avoid_finite)
       apply (rule Lim_Un)
      subgoal by auto
      subgoal by (subst at_within_eq_bot_lemma) auto
      apply (rule Lim_Un)
      subgoal by (subst at_within_eq_bot_lemma2) auto
      subgoal by auto
      done
    by auto
  done

lemma piecewise_continuous_on_finite_superset:
  "piecewise_continuous_on a b I f \<Longrightarrow> I \<subseteq> J \<Longrightarrow> finite J \<Longrightarrow> piecewise_continuous_on a b J f"
  for a b::"'a::{linorder_topology, dense_order, no_bot, no_top}"
  apply (auto simp add: piecewise_continuous_on_def)
    apply (rule continuous_on_subset, assumption, force)
  subgoal for i
    apply (cases "i \<in> I")
     apply (auto simp: continuous_on_def at_within_t1_space_avoid_finite)
    apply (drule bspec[where x=i])
     apply (auto simp: at_within_t1_space_avoid)
    apply (cases "i = b")
     apply (auto simp: at_within_Icc_at_left )
    apply (subst (asm) at_within_interior[where x=i])
    by (auto simp: filterlim_at_split)
  subgoal for i
    apply (cases "i \<in> I")
     apply (auto simp: continuous_on_def at_within_t1_space_avoid_finite)
    apply (drule bspec[where x=i])
     apply (auto simp: at_within_t1_space_avoid)
    apply (cases "i = a")
     apply (auto simp: at_within_Icc_at_right)
    apply (subst (asm) at_within_interior[where x=i])
    subgoal by (simp add: interior_Icc)
    by (auto simp: filterlim_at_split)
  done

lemma piecewise_continuous_on_splitI:
  "piecewise_continuous_on a c K f"
  if
    "piecewise_continuous_on a b I f"
    "piecewise_continuous_on b c J f"
    "I \<subseteq> K" "J \<subseteq> K" "finite K"
  for a b::"'a::{linorder_topology, dense_order, no_bot, no_top}"
  apply (rule piecewise_continuous_on_combine[where b=b])
  subgoal
    by (rule piecewise_continuous_on_finite_superset, fact)
    (use that in \<open>auto elim!: piecewise_continuous_onE\<close>)
  subgoal
    by (rule piecewise_continuous_on_finite_superset, fact)
    (use that in \<open>auto elim!: piecewise_continuous_onE\<close>)
  done

end