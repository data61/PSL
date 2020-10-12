theory PTA_Reachability
  imports PTA
begin

section \<open>Classifying Regions for Divergence\<close>

subsection \<open>Pairwise\<close>

coinductive pairwise :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a stream \<Rightarrow> bool" for P where
  "P a b \<Longrightarrow> pairwise P (b ## xs) \<Longrightarrow> pairwise P (a ## b ## xs)"

lemma pairwise_Suc:
  "pairwise P xs \<Longrightarrow> P (xs !! i) (xs !! (Suc i))"
  by (induction i arbitrary: xs) (force elim: pairwise.cases)+

lemma Suc_pairwise:
  "\<forall> i. P (xs !! i) (xs !! (Suc i)) \<Longrightarrow> pairwise P xs"
  apply (coinduction arbitrary: xs)
  apply (subst stream.collapse[symmetric])
  apply (rewrite in "stl _" stream.collapse[symmetric])
  apply (intro exI conjI, rule HOL.refl)
   apply (erule allE[where x = 0]; simp; fail)
  by simp (metis snth.simps(2))

lemma pairwise_iff:
  "pairwise P xs \<longleftrightarrow> (\<forall> i. P (xs !! i) (xs !! (Suc i)))"
using pairwise_Suc Suc_pairwise by blast

lemma pairwise_stlD:
  "pairwise P xs \<Longrightarrow> pairwise P (stl xs)"
by (auto elim: pairwise.cases)

lemma pairwise_pairD:
  "pairwise P xs \<Longrightarrow> P (shd xs) (shd (stl xs))"
by (auto elim: pairwise.cases)

lemma pairwise_mp:
  assumes "pairwise P xs" and lift: "\<And> x y. x \<in> sset xs \<Longrightarrow> y \<in> sset xs \<Longrightarrow> P x y \<Longrightarrow> Q x y"
  shows "pairwise Q xs" using assms
 apply (coinduction arbitrary: xs)
 subgoal for xs
 apply (subst stream.collapse[symmetric])
 apply (rewrite in "stl _" stream.collapse[symmetric])
 apply (intro exI conjI)
  apply (rule HOL.refl)
 by (auto intro: stl_sset dest: pairwise_pairD pairwise_stlD)
done

lemma pairwise_sdropD:
  "pairwise P (sdrop i xs)" if "pairwise P xs"
  using that
proof (coinduction arbitrary: i xs)
  case (pairwise i xs)
  then show ?case
    apply (inst_existentials "shd (sdrop i xs)" "shd (stl (sdrop i xs))" "stl (stl (sdrop i xs))")
    subgoal
      by (auto dest: pairwise_Suc) (metis sdrop_simps(1) sdrop_stl stream.collapse)
    subgoal
      by (inst_existentials "i - 1" "stl xs") (auto dest: pairwise_Suc pairwise_stlD)
    by (metis sdrop_simps(2) stream.collapse)
qed


subsection \<open>Regions\<close>

(* XXX Move. Rename? *)
lemma gt_GreaterD:
  assumes "u \<in> region X I r" "valid_region X k I r" "c \<in> X" "u c > k c"
  shows "I c = Greater (k c)"
proof -
  from assms have "intv_elem c u (I c)" "valid_intv (k c) (I c)" by auto
  with assms(4) show ?thesis by (cases "I c") auto
qed

lemma const_ConstD:
  assumes "u \<in> region X I r" "valid_region X k I r" "c \<in> X" "u c = d" "d \<le> k c"
  shows "I c = Const d"
proof -
  from assms have "intv_elem c u (I c)" "valid_intv (k c) (I c)" by auto
  with assms(4,5) show ?thesis by (cases "I c") auto
qed

lemma not_Greater_bounded:
  assumes "I x \<noteq> Greater (k x)" "x \<in> X" "valid_region X k I r" "u \<in> region X I r"
  shows "u x \<le> k x"
proof -
  from assms have "intv_elem x u (I x)" "valid_intv (k x) (I x)" by auto
  with assms(1) show "u x \<le> k x" by (cases "I x") auto
qed

lemma Greater_closed:
  fixes t :: "real"
  assumes "u \<in> region X I r" "valid_region X k I r" "c \<in> X" "I c = Greater (k c)" "t > k c"
  shows "u(c := t) \<in> region X I r"
  using assms
  apply (intro region.intros)
     apply (auto; fail)
    apply standard
  subgoal for x
    by (cases "x = c"; cases "I x"; force intro!: intv_elem.intros)
  by auto

lemma Greater_unbounded_aux:
  assumes "finite X" "valid_region X k I r" "c \<in> X" "I c = Greater (k c)"
  shows "\<exists> u \<in> region X I r. u c > t"
using assms Greater_closed[OF _ assms(2-4)] 
proof -
  let ?R = "region X I r"
  let ?t = "if t > k c then t + 1 else k c + 1"
  have t: "?t > k c" by auto
  from region_not_empty[OF assms(1,2)] obtain u where u: "u \<in> ?R" by auto
  from Greater_closed[OF this assms(2-4) t] have "u(c:=?t) \<in> ?R" by auto
  with t show ?thesis by (inst_existentials "u(c:=?t)") auto
qed


subsection \<open>Unbounded and Zero Regions\<close>

definition "unbounded x R \<equiv> \<forall> t. \<exists> u \<in> R. u x > t"

definition "zero x R \<equiv> \<forall> u \<in> R. u x = 0"

lemma Greater_unbounded:
  assumes "finite X" "valid_region X k I r" "c \<in> X" "I c = Greater (k c)"
  shows "unbounded c (region X I r)"
using Greater_unbounded_aux[OF assms] unfolding unbounded_def by blast

lemma unbounded_Greater:
  assumes "valid_region X k I r" "c \<in> X" "unbounded c (region X I r)"
  shows "I c = Greater (k c)"
using assms unfolding unbounded_def by (auto intro: gt_GreaterD)

lemma Const_zero:
  assumes "c \<in> X" "I c = Const 0"
  shows "zero c (region X I r)"
using assms unfolding zero_def by force

lemma zero_Const:
  assumes "finite X" "valid_region X k I r" "c \<in> X" "zero c (region X I r)"
  shows "I c = Const 0"
proof -
  from assms obtain u where "u \<in> region X I r" by atomize_elim (auto intro: region_not_empty)
  with assms show ?thesis unfolding zero_def by (auto intro: const_ConstD)
qed

lemma zero_all:
  assumes "finite X" "valid_region X k I r" "c \<in> X" "u \<in> region X I r" "u c = 0"
  shows "zero c (region X I r)"
proof -
  from assms have "intv_elem c u (I c)" "valid_intv (k c) (I c)" by auto
  then have "I c = Const 0" using assms(5) by cases auto
  with assms have "u' c = 0" if "u' \<in> region X I r" for u' using that by force
  then show ?thesis unfolding zero_def by blast
qed


section \<open>Reachability\<close>

subsection \<open>Definitions\<close>

locale Probabilistic_Timed_Automaton_Regions_Reachability =
  Probabilistic_Timed_Automaton_Regions k v n not_in_X A
    for k v n not_in_X and A :: "('c, t, 's) pta" +
  fixes \<phi> \<psi> :: "('s * ('c, t) cval) \<Rightarrow> bool" fixes s
  assumes \<phi>: "\<And> x y. x \<in> S \<Longrightarrow> x ~ y \<Longrightarrow> \<phi> x \<longleftrightarrow> \<phi> y"
  assumes \<psi>: "\<And> x y. x \<in> S \<Longrightarrow> x ~ y \<Longrightarrow> \<psi> x \<longleftrightarrow> \<psi> y"
  assumes s[intro, simp]: "s \<in> S"
begin

definition "\<phi>' \<equiv> absp \<phi>"
definition "\<psi>' \<equiv> absp \<psi>"
definition "s' \<equiv> abss s"

lemma s_s'_cfg_on[intro]:
  assumes "cfg \<in> MDP.cfg_on s"
  shows "absc cfg \<in> R_G.cfg_on s'"
proof -
  from assms s have "cfg \<in> valid_cfg" unfolding MDP.valid_cfg_def by auto
  then have "absc cfg \<in> R_G.cfg_on (state (absc cfg))" by (auto intro: R_G.valid_cfgD)
  with assms show ?thesis unfolding s'_def by (auto simp: state_absc)
qed

lemma s'_\<S>[simp, intro]:
  "s' \<in> \<S>"
  unfolding s'_def using s by auto

lemma s'_s_cfg_on[intro]:
  assumes "cfg \<in> R_G.cfg_on s'"
  shows "repcs s cfg \<in> MDP.cfg_on s"
proof -
  from assms s have "cfg \<in> R_G.valid_cfg" unfolding R_G.valid_cfg_def by auto
  with assms have "repcs s cfg \<in> valid_cfg" by (auto simp: s'_def intro: R_G.valid_cfgD)
  then show ?thesis by (auto dest: MDP.valid_cfgD)
qed

lemma (in Probabilistic_Timed_Automaton_Regions) compatible_stream:
  assumes \<phi>: "\<And> x y. x \<in> S \<Longrightarrow> x ~ y \<Longrightarrow> \<phi> x \<longleftrightarrow> \<phi> y"
  assumes "pred_stream (\<lambda>s. s \<in> S) xs"
      and [intro]: "x \<in> S"
    shows "pred_stream (\<lambda>s. \<phi> (reps (abss s)) = \<phi> s) (x ## xs)"
unfolding stream.pred_set proof clarify
  fix l u
  assume A: "(l, u) \<in> sset (x ## xs)"
  from assms have "pred_stream (\<lambda>s. s \<in> S) (x ## xs)" by auto
  with A have "(l, u) \<in> S" by (fastforce simp: stream.pred_set)
  then have "abss (l, u) \<in> \<S>" by auto
  then have "reps (abss (l, u)) ~ (l, u)" by simp
  with \<phi> \<open>(l, u) \<in> S\<close> show "\<phi> (reps (abss (l, u))) = \<phi> (l, u)" by blast
qed

lemma \<phi>_stream':
  "pred_stream (\<lambda>s. \<phi> (reps (abss s)) = \<phi> s) (x ## xs)" if "pred_stream (\<lambda>s. s \<in> S) xs" "x \<in> S"
  using compatible_stream[of \<phi>, OF \<phi> that] .

lemma \<psi>_stream':
  "pred_stream (\<lambda>s. \<psi> (reps (abss s)) = \<psi> s) (x ## xs)" if "pred_stream (\<lambda>s. s \<in> S) xs" "x \<in> S"
  using compatible_stream[of \<psi>, OF \<psi> that] .

lemmas \<phi>_stream = compatible_stream[of \<phi>, OF \<phi>]
lemmas \<psi>_stream = compatible_stream[of \<psi>, OF \<psi>]

subsection \<open>Easier Result on All Configurations\<close>

(* TODO: Rename *)
lemma suntil_reps:
  assumes
    "\<forall>s\<in>sset (smap abss y). s \<in> \<S>"
    "(holds \<phi>' suntil holds \<psi>') (s' ## smap abss y)"
  shows "(holds \<phi> suntil holds \<psi>) (s ## y)"
  using assms
  by (subst region_compatible_suntil[symmetric]; (intro \<phi>_stream \<psi>_stream)?)
     (auto simp: \<phi>'_def \<psi>'_def absp_def stream.pred_set \<S>_abss_S s'_def comp_def)

(* TODO: Rename *)
lemma suntil_abss:
  assumes
    "\<forall>s\<in>sset y. s \<in> S"
    "(holds \<phi> suntil holds \<psi>) (s ## y)"
  shows
    "(holds \<phi>' suntil holds \<psi>') (s' ## smap abss y)"
  using assms
  by (subst (asm) region_compatible_suntil[symmetric]; (intro \<phi>_stream \<psi>_stream)?)
     (auto simp: \<phi>'_def \<psi>'_def absp_def stream.pred_set s'_def comp_def)

(* TODO: Generalize to CTL formulae *)
theorem P_sup_sunitl_eq:
  notes [measurable] = in_space_UNIV and [iff] = pred_stream_iff
  shows
    "(MDP.P_sup s  (\<lambda>x. (holds \<phi> suntil holds \<psi>)   (s  ## x)))
   = (R_G.P_sup s' (\<lambda>x. (holds \<phi>' suntil holds \<psi>') (s' ## x)))"
  unfolding MDP.P_sup_def R_G.P_sup_def
proof (rule SUP_eq, goal_cases)
  case prems: (1 cfg)
  let ?cfg' = "absc cfg"
  from prems have "cfg \<in> valid_cfg" by (auto intro: MDP.valid_cfgI)
  then have "?cfg' \<in> R_G.valid_cfg" by (auto intro: R_G.valid_cfgI)
  from \<open>cfg \<in> valid_cfg\<close> have alw_S: "almost_everywhere (MDP.T cfg) (pred_stream (\<lambda>s. s \<in> S))"
    by (rule MDP.alw_S)
  from \<open>?cfg'\<in> R_G.valid_cfg\<close> have alw_\<S>: "almost_everywhere (R_G.T ?cfg') (pred_stream (\<lambda>s. s \<in> \<S>))"
    by (rule R_G.alw_S)
  have "emeasure (MDP.T cfg) {x \<in> space MDP.St. (holds \<phi> suntil holds \<psi>) (s ## x)}
       = emeasure (R_G.T ?cfg') {x \<in> space R_G.St. (holds \<phi>' suntil holds \<psi>') (s' ## x)}"
    apply (rule path_measure_eq_absc1_new[symmetric, where P = "pred_stream (\<lambda> s. s \<in> \<S>)"
          and Q = "pred_stream (\<lambda> s. s \<in> S)"]
        )
    using prems alw_S alw_\<S> apply (auto intro: MDP.valid_cfgI simp: )[7]
    by (auto simp: S_abss_\<S> intro: \<S>_abss_S intro!: suntil_abss suntil_reps, measurable)
  with prems show ?case by (inst_existentials ?cfg') auto
next
  case prems: (2 cfg)
  let ?cfg' = "repcs s cfg"
  have "s = state ?cfg'" by simp
  from prems have "s' = state cfg" by auto
  have "pred_stream (\<lambda>s. \<phi> (reps (abss s)) = \<phi> s) (state (repcs s cfg) ## x)"
    if "pred_stream (\<lambda>s. s \<in> S) x" for x
    using prems that by (intro \<phi>_stream) auto
  moreover
  have "pred_stream (\<lambda>s. \<psi> (reps (abss s)) = \<psi> s) (state (repcs s cfg) ## x)"
    if "pred_stream (\<lambda>s. s \<in> S) x" for x
    using prems that by (intro \<psi>_stream) auto
  ultimately
  have "emeasure (R_G.T cfg) {x \<in> space R_G.St. (holds \<phi>' suntil holds \<psi>') (s' ## x)}
    = emeasure (MDP.T (repcs s cfg)) {x \<in> space MDP.St. (holds \<phi> suntil holds \<psi>) (s ## x)}"
    apply (rewrite in "s ## _" \<open>s = _\<close>)
    apply (subst \<open>s' = _\<close>)
    unfolding \<phi>'_def \<psi>'_def s'_def
    apply (rule path_measure_eq_repcs''_new)
    using prems by (auto 4 3 simp: s'_def intro: R_G.valid_cfgI MDP.valid_cfgI)
  with prems show ?case by (inst_existentials ?cfg') auto
qed

end (* PTA Reachability Problem *)


subsection \<open>Divergent Adversaries\<close>

context Probabilistic_Timed_Automaton
begin

  definition "elapsed u u' \<equiv> Max ({u' c - u c | c. c \<in> \<X>} \<union> {0})"

  definition "eq_elapsed u u' \<equiv> elapsed u u' > 0 \<longrightarrow> (\<forall> c \<in> \<X>. u' c - u c = elapsed u u')"

  fun dur :: "('c, t) cval stream \<Rightarrow> nat \<Rightarrow> t" where
    "dur _ 0 = 0" |
    "dur (x ## y ## xs) (Suc i) = elapsed x y + dur (y ## xs) i"

  definition "divergent \<omega> \<equiv> \<forall> t. \<exists> n. dur \<omega> n > t"

  definition "div_cfg cfg \<equiv> AE \<omega> in MDP.MC.T cfg. divergent (smap (snd o state) \<omega>)"

  definition "\<R>_div \<omega> \<equiv>
    \<forall>x \<in> \<X>. (\<forall> i. (\<exists> j \<ge> i. zero x (\<omega> !! j)) \<and> (\<exists> j \<ge> i. \<not> zero x (\<omega> !! j)))
      \<or> (\<exists> i. \<forall> j \<ge> i. unbounded x (\<omega> !! j))"

  definition "R_G_div_cfg cfg \<equiv> AE \<omega> in MDP.MC.T cfg. \<R>_div (smap (snd o state) \<omega>)"

end

context Probabilistic_Timed_Automaton_Regions
begin

definition "cfg_on_div st \<equiv> MDP.cfg_on st \<inter> {cfg. div_cfg cfg}"

definition "R_G_cfg_on_div st \<equiv> R_G.cfg_on st \<inter> {cfg. R_G_div_cfg cfg}"

lemma measurable_\<R>_div[measurable]: "Measurable.pred MDP.MC.S \<R>_div"
  unfolding \<R>_div_def
  by (intro
        pred_intros_finite[OF beta_interp.finite]
        pred_intros_logic pred_intros_countable
        measurable_count_space_const measurable_compose[OF measurable_snth]
     ) measurable

lemma elapsed_ge0[simp]: "elapsed x y \<ge> 0"
  unfolding elapsed_def using finite(1) by auto

lemma dur_pos:
  "dur xs i \<ge> 0"
 apply (induction i arbitrary: xs)
 apply (auto; fail)
 subgoal for i xs
   apply (subst stream.collapse[symmetric])
   apply (rewrite at "stl xs" stream.collapse[symmetric])
   apply (subst dur.simps)
 by simp
done

lemma dur_mono:
  "i \<le> j \<Longrightarrow> dur xs i \<le> dur xs j"
proof (induction i arbitrary: xs j)
  case 0 show ?case by (auto intro: dur_pos)
next
  case (Suc i xs j)
  obtain x y ys where xs: "xs = x ## y ## ys" using stream.collapse by metis
  from Suc obtain j' where j': "j = Suc j'" by (cases j) auto
  with xs have "dur xs j = elapsed x y + dur (y ## ys) j'" by auto
  also from Suc j' have "\<dots> \<ge> elapsed x y + dur (y ## ys) i" by auto
  also have "elapsed x y + dur (y ## ys) i = dur xs (Suc i)" by (simp add: xs)
  finally show ?case .
qed

lemma dur_monoD:
  assumes "dur xs i < dur xs j"
  shows "i < j" using assms
 by - (rule ccontr; auto 4 4 dest: leI dur_mono[where xs = xs])

lemma elapsed_0D:
  assumes "c \<in> \<X>" "elapsed u u' \<le> 0"
  shows "u' c - u c \<le> 0"
proof -
  from assms have "u' c - u c \<in> {u' c - u c | c. c \<in> \<X>} \<union> {0}" by auto
  with finite(1) have "u' c - u c \<le> Max ({u' c - u c | c. c \<in> \<X>} \<union> {0})" by auto
  with assms(2) show ?thesis unfolding elapsed_def by auto
qed

lemma elapsed_ge:
  assumes "eq_elapsed u u'" "c \<in> \<X>"
  shows "elapsed u u' \<ge> u' c - u c"
  using assms unfolding eq_elapsed_def by (auto intro: elapsed_ge0 order.trans[OF elapsed_0D])

lemma elapsed_eq:
  assumes "eq_elapsed u u'" "c \<in> \<X>" "u' c - u c \<ge> 0"
  shows "elapsed u u' = u' c - u c"
  using elapsed_ge[OF assms(1,2)] assms unfolding eq_elapsed_def by auto

lemma dur_shift:
  "dur \<omega> (i + j) = dur \<omega> i + dur (sdrop i \<omega>) j"
 apply (induction i arbitrary: \<omega>)
  apply simp
 subgoal for i \<omega>
  apply simp
  apply (subst stream.collapse[symmetric])
  apply (rewrite at "stl \<omega>" stream.collapse[symmetric])
  apply (subst dur.simps)
  apply (rewrite in "dur \<omega>" stream.collapse[symmetric])
  apply (rewrite in "dur (_ ## \<hole>) (Suc _)" stream.collapse[symmetric])
  apply (subst dur.simps)
  apply simp
 done
done

lemma dur_zero:
  assumes
    "\<forall> i. xs !! i \<in> \<omega> !! i" "\<forall> j \<le> i. zero x (\<omega> !! j)" "x \<in> \<X>"
    "\<forall> i. eq_elapsed (xs !! i) (xs !! Suc i)"
  shows "dur xs i = 0" using assms
proof (induction i arbitrary: xs \<omega>)
  case 0
  then show ?case by simp
next
  case (Suc i xs \<omega>)
  let ?x = "xs !! 0"
  let ?y = "xs !! 1"
  let ?ys = "stl (stl xs)"
  have xs: "xs = ?x ## ?y ## ?ys" by auto
  from Suc.prems have
    "\<forall> i. (?y ## ?ys) !! i \<in> stl \<omega> !! i" "\<forall> j \<le> i. zero x (stl \<omega> !! j)"
    "\<forall> i. eq_elapsed (stl xs !! i) (stl xs !! Suc i)"
    by (metis snth.simps(2) | auto)+
  from Suc.IH[OF this(1,2) \<open>x \<in> _\<close>] this(3) have [simp]: "dur (stl xs) i = 0" by auto
  from Suc.prems(1,2) have "?y x = 0" "?x x = 0" unfolding zero_def by force+
  then have *: "?y x - ?x x = 0" by simp
  have "dur xs (Suc i) = elapsed ?x ?y"
    apply (subst xs)
    apply (subst dur.simps)
    by simp
  also have "\<dots> = 0"
    apply (subst elapsed_eq[OF _ \<open>x \<in> _\<close>])
    unfolding One_nat_def using Suc.prems(4) apply blast
    using * by auto
  finally show ?case .
qed

lemma dur_zero_tail:
  assumes "\<forall> i. xs !! i \<in> \<omega> !! i" "\<forall> k \<ge> i. k \<le> j \<longrightarrow> zero x (\<omega> !! k)" "x \<in> \<X>" "j \<ge> i"
          "\<forall> i. eq_elapsed (xs !! i) (xs !! Suc i)"
  shows "dur xs j = dur xs i"
proof -
  from \<open>j \<ge> i\<close> dur_shift[of xs i "j - i"] have
    "dur xs j = dur xs i + dur (sdrop i xs) (j - i)"
  by simp
  also have "\<dots> = dur xs i"
    using assms
    by (rewrite in "dur (sdrop _ _) _" dur_zero[where \<omega> = "sdrop i \<omega>"])
       (auto dest: prop_nth_sdrop_pair[of eq_elapsed] prop_nth_sdrop prop_nth_sdrop_pair[of "(\<in>)"])
  finally show ?thesis .
qed

lemma elapsed_ge_pos:
  fixes u :: "('c, t) cval"
  assumes "eq_elapsed u u'" "c \<in> \<X>" "u \<in> V" "u' \<in> V"
  shows "elapsed u u' \<le> u' c"
proof (cases "elapsed u u' = 0")
  case True
  with assms show ?thesis by (auto simp: V_def)
next
  case False
  from \<open>u \<in> V\<close> \<open>c \<in> \<X> \<close> have "u c \<ge> 0" by (auto simp: V_def)
  from False assms have "elapsed u u' = u' c - u c"
    unfolding eq_elapsed_def by (auto simp add: less_le)
  also from \<open>u c \<ge> 0\<close> have "\<dots> \<le> u' c" by simp
  finally show ?thesis .
qed

lemma dur_Suc:
  "dur xs (Suc i) - dur xs i = elapsed (xs !! i) (xs !! Suc i)"
 apply (induction i arbitrary: xs)
  apply simp
  apply (subst stream.collapse[symmetric])
  apply (rewrite in "stl _" stream.collapse[symmetric])
  apply (subst dur.simps)
  apply simp
 apply simp
 subgoal for i xs
  apply (subst stream.collapse[symmetric])
  apply (rewrite in "stl _" stream.collapse[symmetric])
  apply (subst dur.simps)
  apply simp
  apply (rewrite in "dur xs (Suc _)" stream.collapse[symmetric])
  apply (rewrite at "stl xs" in "_ ## stl xs" stream.collapse[symmetric])
  apply (subst dur.simps)
  apply simp
 done
done

inductive trans where
  succ: "t \<ge> 0 \<Longrightarrow> u' = u \<oplus> t \<Longrightarrow> trans u u'" |
  reset: "set l \<subseteq> \<X> \<Longrightarrow> u' = clock_set l 0 u \<Longrightarrow> trans u u'" |
  id: "u = u' \<Longrightarrow> trans u u'"

abbreviation "stream_trans \<equiv> pairwise trans"

lemma K_cfg_trans:
  assumes "cfg \<in> MDP.cfg_on (l, R)" "cfg' \<in> K_cfg cfg" "state cfg' = (l', R')"
  shows "trans R R'"
using assms
 apply (simp add: set_K_cfg)
 apply (drule MDP.cfg_onD_action)
 apply (cases rule: K.cases)
    apply (auto intro: trans.intros)
using admissible_targets_clocks(2) by (blast intro: trans.intros(2))

lemma enabled_stream_trans:
  assumes "cfg \<in> valid_cfg" "MDP.MC.enabled cfg xs"
  shows "stream_trans (smap (snd o state) xs)"
  using assms
proof (coinduction arbitrary: cfg xs)
  case prems: (pairwise cfg xs)
  let ?xs = "stl (stl xs)" let ?x = "shd xs" let ?y = "shd (stl xs)"
  from MDP.pred_stream_cfg_on[OF prems] have *:
    "pred_stream (\<lambda>cfg. state cfg \<in> S \<and> cfg \<in> MDP.cfg_on (state cfg)) xs" .
  obtain l R l' R' where eq: "state ?x = (l, R)" "state ?y = (l', R')" by force
  moreover from * have "?x \<in> MDP.cfg_on (state ?x)" "?x \<in> valid_cfg"
    by (auto intro: MDP.valid_cfgI simp: stream.pred_set)
  moreover from prems(2) have "?y \<in> K_cfg ?x" by (auto elim: MDP.MC.enabled.cases)
  ultimately have "trans R R'"
    by (intro K_cfg_trans[where cfg = ?x and cfg' = ?y and l = l and l' = l']) metis+
  with \<open>?x \<in> valid_cfg\<close> prems(2) show ?case
    apply (inst_existentials R R' "smap (snd o state) ?xs")
      apply (simp add: eq; fail)+
    apply (rule disjI1, inst_existentials ?x "stl xs")
    by (auto simp: eq elim: MDP.MC.enabled.cases)
qed

lemma stream_trans_trans:
  assumes "stream_trans xs"
  shows "trans (xs !! i) (stl xs !! i)"
using pairwise_Suc assms by auto

lemma trans_eq_elapsed:
  assumes "trans u u'" "u \<in> V"
  shows "eq_elapsed u u'"
using assms
proof cases
  case (succ t)
  with finite(1) show ?thesis by (auto simp: cval_add_def elapsed_def max_def eq_elapsed_def)
next
  case prems: (reset l)
  then have "u' c - u c \<le> 0" if "c \<in> \<X>" for c
  using that \<open>u \<in> V\<close> by (cases "c \<in> set l") (auto simp: V_def)
  then have "elapsed u u' = 0" unfolding elapsed_def using finite(1)
   apply simp
   apply (subst Max_insert2)
  by auto
  then show ?thesis by (auto simp: eq_elapsed_def)
next
  case id
  then show ?thesis
    using finite(1) by (auto simp: Max_gr_iff elapsed_def eq_elapsed_def)
qed

lemma pairwise_trans_eq_elapsed:
  assumes "stream_trans xs" "pred_stream (\<lambda> u. u \<in> V) xs"
  shows "pairwise eq_elapsed xs"
using trans_eq_elapsed assms by (auto intro: pairwise_mp simp: stream.pred_set)

lemma not_reset_dur:
  assumes "\<forall>k>i. k \<le> j \<longrightarrow> \<not> zero c ([xs !! k]\<^sub>\<R>)" "j \<ge> i" "c \<in> \<X>" "stream_trans xs"
    "\<forall> i. eq_elapsed (xs !! i) (xs !! Suc i)" "\<forall> i. xs !! i \<in> V"
  shows "dur xs j - dur xs i = (xs !! j) c - (xs !! i) c"
  using assms
proof (induction j)
  case 0 then show ?case by simp
next
  case (Suc j)
  from stream_trans_trans[OF Suc.prems(4)] have trans: "trans (xs !! j) (xs !! Suc j)" by auto
  from Suc.prems have *:
    "\<not> zero c ([xs !! Suc j]\<^sub>\<R>)" "eq_elapsed (xs !! j) (xs !! Suc j)" if "Suc j > i"
    using that by auto
  from Suc.prems(6) have "xs !! j \<in> V" "xs !! Suc j \<in> V" by blast+
  then have regions: "[xs !! j]\<^sub>\<R> \<in> \<R>" "[xs !! Suc j]\<^sub>\<R> \<in> \<R>" by auto
  from trans have "(xs !! Suc j) c - (xs !! j) c \<ge> 0" if "Suc j > i"
  proof (cases)
    case succ
    with regions show ?thesis by (auto simp: cval_add_def)
  next
    case prems: (reset l)
    show ?thesis
    proof (cases "c \<in> set l")
      case False
      with prems show ?thesis by auto
    next
      case True
      with prems have "(xs !! Suc j) c = 0" by auto
      moreover from assms have "xs !! Suc j \<in> [xs !! Suc j]\<^sub>\<R>" by blast
      ultimately have
        "zero c ([xs !! Suc j]\<^sub>\<R>)"
        using zero_all[OF finite(1) _ \<open>c \<in> \<X>\<close>] regions(2) by (auto simp: \<R>_def)
      with * that show ?thesis by auto
    qed
  next
    case id then show ?thesis by simp
  qed
  with * \<open>c \<in> \<X>\<close> elapsed_eq have
    *: "elapsed (xs !! j) (xs !! Suc j) = (xs !! Suc j) c - (xs !! j) c"
    if "Suc j > i"
    using that by blast
  show ?case
  proof (cases "i = Suc j")
    case False
    with Suc have
      "dur xs (Suc j) - dur xs i = dur xs (Suc j) - dur xs j + (xs !! j) c - (xs !! i) c"
      by auto
    also have "\<dots> = elapsed (xs !! j) (xs !! Suc j) + (xs !! j) c - (xs !! i) c"
      by (simp add: dur_Suc)
    also have
      "\<dots> = (xs !! Suc j) c - (xs !! j) c  + (xs !! j) c - (xs !! i) c"
      using * False Suc.prems by auto
    also have "\<dots> = (xs !! Suc j) c - (xs !! i) c" by simp
    finally show ?thesis by auto
  next
    case True
    then show ?thesis by simp
  qed
qed

lemma not_reset_dur':
  assumes "\<forall>j\<ge>i. \<not> zero c ([xs !! j]\<^sub>\<R>)" "j \<ge> i" "c \<in> \<X>" "stream_trans xs"
          "\<forall> i. eq_elapsed (xs !! i) (xs !! Suc i)" "\<forall> j. xs !! j \<in> V"
  shows "dur xs j - dur xs i = (xs !! j) c - (xs !! i) c"
using assms not_reset_dur by auto

lemma not_reset_unbounded:
  assumes "\<forall>j\<ge>i. \<not> zero c ([xs !! j]\<^sub>\<R>)" "j \<ge> i" "c \<in> \<X>" "stream_trans xs"
          "\<forall> i. eq_elapsed (xs !! i) (xs !! Suc i)" "\<forall> j. xs !! j \<in> V"
          "unbounded c ([xs !! i]\<^sub>\<R>)"
  shows "unbounded c ([xs !! j]\<^sub>\<R>)"
proof -
  let ?u = "xs !! i" let ?u' = "xs !! j" let ?R = "[xs !! i]\<^sub>\<R>"
  from assms have "?u \<in> ?R" by auto
  from assms(6) have "?R \<in> \<R>" by auto
  then obtain I r where "?R = region \<X> I r" "valid_region \<X> k I r" unfolding \<R>_def by auto
  with assms(3,7) unbounded_Greater \<open>?u \<in> ?R\<close> have "?u c > k c" by force
  also from not_reset_dur'[OF assms(1-6)] dur_mono[OF \<open>j \<ge> i\<close>, of xs] have "?u' c \<ge> ?u c" by auto
  finally have "?u' c > k c" by auto
  let ?R' = "[xs !! j]\<^sub>\<R>"
  from assms have "?u' \<in> ?R'" by auto
  from assms(6) have "?R' \<in> \<R>" by auto
  then obtain I r where "?R' = region \<X> I r" "valid_region \<X> k I r" unfolding \<R>_def by auto
  moreover with \<open>?u' c > _\<close> \<open>?u' \<in> _\<close> gt_GreaterD \<open>c \<in> \<X>\<close> have "I c = Greater (k c)" by auto
  ultimately show ?thesis using Greater_unbounded[OF finite(1) _ \<open>c \<in> \<X>\<close>] by auto
qed

lemma gt_unboundedD:
  assumes "u \<in> R"
    and "R \<in> \<R>"
    and "c \<in> \<X>"
    and "real (k c) < u c"
  shows "unbounded c R"
proof -
  from assms obtain I r where "R = region \<X> I r" "valid_region \<X> k I r"
    unfolding \<R>_def by auto
  with Greater_unbounded[of \<X> k I r c] gt_GreaterD[of u \<X> I r k c] assms finite(1) show ?thesis
    by auto
qed

definition trans' :: "('c, t) cval \<Rightarrow> ('c, t) cval \<Rightarrow> bool" where
  "trans' u u' \<equiv>
    ((\<forall> c \<in> \<X>. u c > k c \<and> u' c > k c \<and> u \<noteq> u') \<longrightarrow> u' = u \<oplus> 0.5) \<and>
    ((\<exists> c \<in> \<X>. u c = 0 \<and> u' c > 0 \<and> (\<forall>c\<in>\<X>. \<nexists>d. d \<le> k c \<and> u' c = real d))
    \<longrightarrow> u' = delayedR ([u']\<^sub>\<R>) u)"

(* XXX Move *)
lemma zeroI:
  assumes "c \<in> \<X>" "u \<in> V" "u c = 0"
  shows "zero c ([u]\<^sub>\<R>)"
proof -
  from assms have "u \<in> [u]\<^sub>\<R>" "[u]\<^sub>\<R> \<in> \<R>" by auto
  then obtain I r where "[u]\<^sub>\<R> = region \<X> I r" "valid_region \<X> k I r" unfolding \<R>_def by auto
  with zero_all[OF finite(1) this(2) \<open>c \<in> \<X>\<close>] \<open>u \<in> [u]\<^sub>\<R>\<close> \<open>u c = 0\<close> show ?thesis by auto
qed

(* XXX Move, rename *)
lemma zeroD:
  "u x = 0" if "zero x ([u]\<^sub>\<R>)" "u \<in> V"
  using that by (metis regions_part_ex(1) zero_def)

lemma not_zeroD:
  assumes "\<not> zero x ([u]\<^sub>\<R>)" "u \<in> V" "x \<in> \<X>"
  shows "u x > 0"
proof -
  from zeroI assms have "u x \<noteq> 0" by auto
  moreover from assms have "u x \<ge> 0" unfolding V_def by auto
  ultimately show ?thesis by auto
qed

(* XXX Move *)
lemma not_const_intv:
  assumes "u \<in> V" "\<forall>c\<in>\<X>. \<nexists>d. d \<le> k c \<and> u c = real d"
  shows "\<forall>c\<in>\<X>. \<forall>u \<in> [u]\<^sub>\<R>. \<nexists>d. d \<le> k c \<and> u c = real d"
proof -
  from assms have "u \<in> [u]\<^sub>\<R>" "[u]\<^sub>\<R> \<in> \<R>" by auto
  then obtain I r where I: "[u]\<^sub>\<R> = region \<X> I r" "valid_region \<X> k I r" unfolding \<R>_def by auto
  have "\<nexists>d. d \<le> k c \<and> u' c = real d" if "c \<in> \<X>" "u' \<in> [u]\<^sub>\<R>" for c u'
  proof safe
    fix d assume A: "d \<le> k c" "u' c = real d"
    from I that have "intv_elem c u' (I c)" "valid_intv (k c) (I c)" by auto
    then show False
      using A I \<open>u \<in> [u]\<^sub>\<R>\<close> \<open>c \<in> \<X>\<close> assms(2) by (cases; fastforce)
  qed
  then show ?thesis by auto
qed

lemma K_cfg_trans':
  assumes "repcs (l, u) cfg \<in> MDP.cfg_on (l, u)" "cfg' \<in> K_cfg (repcs (l, u) cfg)"
          "state cfg' = (l', u')" "(l, u) \<in> S" "cfg \<in> R_G.valid_cfg" "abss (l, u) = state cfg"
  shows "trans' u u'"
using assms
 apply (simp add: set_K_cfg)
 apply (drule MDP.cfg_onD_action)
 apply (cases rule: K.cases)
 apply assumption
proof goal_cases
  case prems: (1 l u t)
  from assms \<open>_ = (l, u)\<close> have "repcs (l, u) cfg \<in> valid_cfg" by (auto intro: MDP.valid_cfgI)
  then have "absc (repcs (l, u) cfg) \<in> R_G.valid_cfg" by auto
  from prems have *: "rept (l, u) (action cfg) = return_pmf (l, u \<oplus> t)" unfolding repcs_def by auto
  from \<open>abss _ = _\<close> \<open>_ = (l, u)\<close> \<open>cfg \<in> R_G.valid_cfg\<close> have
    "action cfg \<in> \<K> (abss (l, u))"
  by (auto dest: R_G_I)
  from abst_rept_id[OF this] * have "action cfg = abst (return_pmf (l, u \<oplus> t))" by auto
  with prems have **: "action cfg = return_pmf (l, [u \<oplus> t]\<^sub>\<R>)" unfolding abst_def by auto
  show ?thesis
  proof (cases "\<forall> c \<in> \<X>. u c > k c")
    case True
    from prems have "u \<oplus> t \<in> [u]\<^sub>\<R>" by (auto intro: upper_right_closed[OF True])
    with prems have "[u \<oplus> t]\<^sub>\<R> = [u]\<^sub>\<R>" by (auto dest: alpha_interp.region_unique_spec)
    with ** have "action cfg = return_pmf (l, [u]\<^sub>\<R>)" by simp
    with True have "rept (l, u) (action cfg) = return_pmf (l, u \<oplus> 0.5)" 
    unfolding rept_def using prems by auto
    with * have "u \<oplus> t = u \<oplus> 0.5" by auto
    moreover from prems have "u' = u \<oplus> t" by auto
    moreover from prems True have "\<forall> c \<in> \<X>. u' c > k c" by (auto simp: cval_add_def)
    ultimately show ?thesis using True \<open>_ = (l, u)\<close> unfolding trans'_def by auto
  next
    case F: False
    show ?thesis
    proof (cases "\<exists>c\<in>\<X>. u c = 0 \<and> 0 < u' c \<and> (\<forall>c\<in>\<X>. \<nexists>d. d \<le> k c \<and> u' c = real d)")
      case True
      from prems have "u' \<in> [u']\<^sub>\<R>" by auto
      from prems have "[u \<oplus> t]\<^sub>\<R> \<in> Succ \<R> ([u]\<^sub>\<R>)" by auto
      from True obtain c where "c \<in> \<X>" "u c = 0" "u' c > 0" by auto
      with zeroI prems have "zero c ([u]\<^sub>\<R>)" by auto
      moreover from \<open>u' \<in> _\<close> \<open>u' c > 0\<close> have "\<not> zero c ([u']\<^sub>\<R>)" unfolding zero_def by fastforce
      ultimately have "[u \<oplus> t]\<^sub>\<R> \<noteq> [u]\<^sub>\<R>" using prems by auto
      moreover from True not_const_intv prems have
        "\<forall> u \<in> [u \<oplus> t]\<^sub>\<R>. \<forall>c\<in>\<X>. \<nexists>d. d \<le> k c \<and> u c = real d"
      by auto
      ultimately have "\<exists>R'. (l, u) \<in> S \<and>
                     action cfg = return_pmf (l, R') \<and>
                     R' \<in> Succ \<R> ([u]\<^sub>\<R>) \<and> [u]\<^sub>\<R> \<noteq> R' \<and> (\<forall>u\<in>R'. \<forall>c\<in>\<X>. \<nexists>d. d \<le> k c \<and> u c = real d)"
       apply -
       apply (rule exI[where x = "[u \<oplus> t]\<^sub>\<R>"])
       apply safe
      using prems ** by auto
      then have
        "rept (l, u) (action cfg)
       = return_pmf (l, delayedR (SOME R'. action cfg = return_pmf (l, R')) u)" 
      unfolding rept_def by auto
      with * ** prems have "u' = delayedR ([u \<oplus> t]\<^sub>\<R>) u" by auto
      with F True prems show ?thesis unfolding trans'_def by auto
    next
      case False
      with F \<open>_ = (l, u)\<close> show ?thesis unfolding trans'_def by auto
    qed
  qed
next
  case prems: (2 _ _ \<tau> \<mu>)
  then obtain X where X: "u' = ([X := 0]u)" "(X, l') \<in> set_pmf \<mu>" by auto
  from \<open>_ \<in> S\<close> have "u \<in> V" by auto
  let ?r = "SOME r. set r = X"
  show ?case
  proof (cases "X = {}")
    case True
    with X have "u = u'" by auto
    with non_empty show ?thesis unfolding trans'_def by auto
  next
    case False
    then obtain x where "x \<in> X" by auto
    moreover have "X \<subseteq> \<X>" using admissible_targets_clocks(1)[OF prems(10) X(2)] by auto
    ultimately have "x \<in> \<X>" by auto
    from \<open>X \<subseteq> \<X>\<close> finite(1) obtain r where "set r = X" using finite_list finite_subset by blast
    then have r: "set ?r = X" by (rule someI)
    with \<open>x \<in> X\<close> X have "u' x = 0" by auto
    from X r \<open>u \<in> V\<close> \<open>X \<subseteq> \<X>\<close> have "u' x \<le> u x" for x
      by (cases "x \<in> X"; auto simp: V_def)
    have False if "u' x > 0 \<and> u x = 0" for x
      using \<open>u' _ \<le> _\<close>[of x] that by auto
    with \<open>u' x = 0\<close> show ?thesis using \<open>x \<in> \<X>\<close> unfolding trans'_def by auto
  qed
next
  case 3
  with non_empty show ?case unfolding trans'_def by auto
qed

coinductive enabled_repcs where
  "enabled_repcs (shd xs) (stl xs) \<Longrightarrow> shd xs = repcs st' cfg' \<Longrightarrow> st' \<in> rept st (action cfg)
  \<Longrightarrow> abss st' = state cfg'
  \<Longrightarrow> cfg' \<in> R_G.valid_cfg
  \<Longrightarrow> enabled_repcs (repcs st cfg) xs"

(* XXX Move *)
lemma K_cfg_rept_in:
assumes "cfg \<in> R_G.valid_cfg"
    and "abss st = state cfg"
    and "cfg' \<in> K_cfg cfg"
  shows "(THE s'. s' \<in> set_pmf (rept st (action cfg)) \<and> abss s' = state cfg')
         \<in> set_pmf (rept st (action cfg))"
proof -
  from assms(1,2) have "action cfg \<in> \<K> (abss st)" by (auto simp: R_G_I)
  from \<open>cfg' \<in> _\<close> have
    "cfg' = cont cfg (state cfg')" "state cfg' \<in> action cfg"
  by (auto simp: set_K_cfg)
  with abst_rept_id[OF \<open>action _ \<in> _\<close>] pmf.set_map have
    "state cfg' \<in> abss ` set_pmf (rept st (action cfg))" unfolding abst_def  by metis
  then obtain st' where
    "st' \<in> rept st (action cfg)" "abss st' = state cfg'"
  unfolding abst_def by auto
  with K_cfg_rept_aux[OF assms(1,2) this(1)] show ?thesis by auto
qed

lemma enabled_repcsI:
  assumes "cfg \<in> R_G.valid_cfg" "abss st = state cfg" "MDP.MC.enabled (repcs st cfg) xs"
  shows "enabled_repcs (repcs st cfg) xs" using assms
proof (coinduction arbitrary: cfg xs st)
  case prems: (enabled_repcs cfg xs st)
  let ?x = "shd xs" and ?y = "shd (stl xs)"
  let ?st = "THE s'. s' \<in> set_pmf (rept st (action cfg)) \<and> abss s' = state (absc ?x)"
  from prems(3) have "?x \<in> K_cfg (repcs st cfg)" by cases
  with K_cfg_map_repcs[OF prems(1,2)] obtain cfg' where
    "cfg' \<in> K_cfg cfg" "?x = repcs (THE s'. s' \<in> rept st (action cfg) \<and> abss s' = state cfg') cfg'"
    by auto
  let ?st = "THE s'. s' \<in> rept st (action cfg) \<and> abss s' = state cfg'"
  from K_cfg_rept_action[OF prems(1,2) \<open>cfg' \<in> _\<close>] have "abss ?st = state cfg'" .
  moreover from K_cfg_rept_in[OF prems(1,2) \<open>cfg' \<in> _\<close>] have "?st \<in> rept st (action cfg)" .
  moreover have "cfg' \<in> R_G.valid_cfg" using \<open>cfg' \<in> K_cfg cfg\<close> prems(1) by blast 
  moreover from absc_repcs_id[OF this \<open>abss ?st = state cfg'\<close>] \<open>?x = _\<close> have "absc ?x = cfg'"
    by auto
  moreover from prems(3) have "MDP.MC.enabled (shd xs) (stl xs)" by cases
  ultimately show ?case
    using \<open>?x = _\<close> by (inst_existentials xs ?st "absc ?x" st cfg) fastforce+
qed

lemma repcs_eq_rept:
  "rept st (action cfg) = rept st'' (action cfg'')" if "repcs st cfg = repcs st'' cfg''"
   by (metis (mono_tags, lifting) action_cfg_corec old.prod.case repcs_def that)

lemma enabled_stream_trans':
  assumes "cfg \<in> R_G.valid_cfg" "abss st = state cfg" "MDP.MC.enabled (repcs st cfg) xs"
  shows "pairwise trans' (smap (snd o state) xs)"
using assms
proof (coinduction arbitrary: cfg xs st)
  case prems: (pairwise cfg xs)
  let ?xs = "stl xs"
  from prems have A: "enabled_repcs (repcs st cfg) xs" by (auto intro: enabled_repcsI)
  then obtain st' cfg' where
    "enabled_repcs (shd xs) (stl xs)" "shd xs = repcs st' cfg'" "st' \<in> rept st (action cfg)"
    "abss st' = state cfg'" "cfg' \<in> R_G.valid_cfg"
   apply atomize_elim
   apply (cases rule: enabled_repcs.cases)
   apply assumption
   subgoal for st' cfg' st'' cfg''
     by (inst_existentials st' cfg') (auto dest: repcs_eq_rept)
  done
  then obtain st'' cfg'' where
    "enabled_repcs (shd ?xs) (stl ?xs)"
    "shd ?xs = repcs st'' cfg''" "st'' \<in> rept st' (action cfg')" "abss st'' = state cfg''"
    by atomize_elim (subst (asm)enabled_repcs.simps, fastforce dest: repcs_eq_rept)
  let ?x = "shd xs" let ?y = "shd (stl xs)"
  let ?cfg = "repcs st cfg"
  from prems have "?cfg \<in> valid_cfg" by auto
  from MDP.pred_stream_cfg_on[OF \<open>?cfg \<in> valid_cfg\<close> prems(3)] have *:
    "pred_stream (\<lambda>cfg. state cfg \<in> S \<and> cfg \<in> MDP.cfg_on (state cfg)) xs" .
  obtain l u l' u' where eq: "st' = (l, u)" "st'' = (l', u')"
    by force
  moreover from * have
    "?x \<in> MDP.cfg_on (state ?x)" "?x \<in> valid_cfg"
    by (auto intro: MDP.valid_cfgI simp: stream.pred_set)
  moreover from prems(3) have "?y \<in> K_cfg ?x" by (auto elim: MDP.MC.enabled.cases)
  ultimately have "trans' u u'"
    using \<open>?x = _\<close> \<open>?y = _\<close> \<open>cfg' \<in> _\<close> \<open>abss st' = _\<close>
    by (intro K_cfg_trans') (auto dest: MDP.valid_cfg_state_in_S)
  with \<open>?x \<in> valid_cfg\<close> \<open>cfg' \<in> R_G.valid_cfg\<close> prems(3) \<open>abss _ = state cfg'\<close> show ?case
    apply (inst_existentials u u' "smap (snd o state) (stl ?xs)")
    apply (simp add: eq \<open>?x = _\<close> \<open>?y = _\<close>; fail)+
    by ((intro disjI1 exI)?; auto simp: \<open>?x = _\<close> \<open>?y = _\<close> eq elim: MDP.MC.enabled.cases)
qed

lemma divergent_\<R>_divergent:
  assumes in_S: "pred_stream (\<lambda> u. u \<in> V) xs"
     and  div:  "divergent xs"
     and trans: "stream_trans xs"
  shows "\<R>_div (smap (\<lambda> u. [u]\<^sub>\<R>) xs)" (is "\<R>_div ?\<omega>")
unfolding \<R>_div_def proof (safe, simp_all)
  fix x i
  assume x: "x \<in> \<X>" and bounded: "\<forall>i. \<exists>j\<ge>i. \<not> unbounded x ([xs !! j]\<^sub>\<R>)"
  from in_S have xs_\<omega>: "\<forall>i. xs !! i \<in> ?\<omega> !! i" by (auto simp: stream.pred_set)
  from trans in_S have elapsed:
    "\<forall> i. eq_elapsed (xs !! i) (xs !! Suc i)"
    by (fastforce intro: pairwise_trans_eq_elapsed pairwise_Suc[where P = eq_elapsed])
  { assume A: "\<forall>j \<ge> i. \<not> zero x ([xs !! j]\<^sub>\<R>)"
    let ?t = "dur xs i + k x"
    from div obtain j where j: "dur xs j > dur xs i + k x" unfolding divergent_def by auto
    then have "k x < dur xs j - dur xs i" by auto
    also with not_reset_dur'[OF A less_imp_le[OF dur_monoD], of xs] \<open>x \<in> \<X>\<close> assms elapsed have
      "\<dots> = (xs !! j) x - (xs !! i) x"
      by (auto simp: stream.pred_set)
    also have "\<dots> \<le> (xs !! j) x"
      using assms(1) \<open>x \<in> \<X>\<close> unfolding V_def by (auto simp: stream.pred_set)
    finally have "unbounded x ([xs !! j]\<^sub>\<R>)"
      using assms \<open>x \<in> \<X>\<close> by (intro gt_unboundedD) (auto simp: stream.pred_set)
    moreover from dur_monoD[of xs i j] j A have "\<forall>j' \<ge> j. \<not> zero x ([xs !! j']\<^sub>\<R>)" by auto
    ultimately have "\<forall>i\<ge>j. unbounded x ([xs !! i]\<^sub>\<R>)"
      using elapsed assms x by (auto intro: not_reset_unbounded simp: stream.pred_set)
    with bounded have False by auto
  }
  then show "\<exists>j\<ge>i. zero x ([xs !! j]\<^sub>\<R>)" by auto
  { assume A: "\<forall>j \<ge> i. zero x ([xs !! j]\<^sub>\<R>)"
    from div obtain j where j: "dur xs j > dur xs i" unfolding divergent_def by auto
    then have "j \<ge> i" by (auto dest: dur_monoD)
    from A have "\<forall>j \<ge> i. zero x (?\<omega> !! j)" by auto
    with dur_zero_tail[OF xs_\<omega> _ x \<open>i \<le> j\<close> elapsed] j have False by simp
  }
  then show "\<exists>j\<ge>i. \<not> zero x ([xs !! j]\<^sub>\<R>)" by auto
qed

lemma (in -)
  fixes f :: "nat \<Rightarrow> real"
  assumes "\<forall> i. f i \<ge> 0" "\<forall> i. \<exists> j \<ge> i. f j > d" "d > 0"
  shows "\<exists> n. (\<Sum> i \<le> n. f i) > t"
  oops

(* TODO: Reduce this proof to a more general theorem *)
lemma dur_ev_exceedsI:
  assumes "\<forall> i. \<exists> j \<ge> i. dur xs j - dur xs i \<ge> d" and "d > 0"
  obtains i where "dur xs i > t"
proof -
  have base: "\<exists> i. dur xs i > t" if "t < d" for t
  proof -
    from assms obtain j where "dur xs j - dur xs 0 \<ge> d" by fastforce
    with dur_pos[of xs 0] have "dur xs j \<ge> d" by simp
    with \<open>d > 0\<close> \<open>t < d\<close> show ?thesis by - (rule exI[where x = j]; auto)
  qed
  have base2: "\<exists> i. dur xs i > t" if "t \<le> d" for t
  proof (cases "t = d")
    case False
    with \<open>t \<le> d\<close> base show ?thesis by simp
  next
    case True
    from base \<open>d > 0\<close> obtain i where "dur xs i > 0" by auto
    moreover from assms obtain j where "dur xs j - dur xs i \<ge> d" by auto
    ultimately have "dur xs j > d" by auto
    with \<open>t = d\<close> show ?thesis by auto
  qed
  show ?thesis
  proof (cases "t \<ge> 0")
    case False
    with dur_pos have "dur xs 0 > t" by auto
    then show ?thesis by (fastforce intro: that)
  next
    case True
    let ?m = "nat \<lceil>t / d\<rceil>"
    from True have "\<exists> i. dur xs i > ?m * d"
    proof (induction ?m arbitrary: t)
      case 0
      with base[OF \<open>0 < d\<close>] show ?case by simp
    next
      case (Suc n t)
      let ?t = "t - d"
      show ?case
      proof (cases "t \<ge> d")
        case True
        have "?t / d = t / d - 1"
        (* Generated by sledgehammer *)
        (* Alternative: by (smt assms(2) diff_divide_distrib divide_self_if) *)
        proof -
          have "t / d + - 1 * ((t + - 1 * d) / d) + - 1 * (d / d) = 0"
            by (simp add: diff_divide_distrib)
          then have "t / d + - 1 * ((t + - 1 * d) / d) = 1"
            using assms(2) by fastforce
          then show ?thesis
            by algebra
        qed
        then have "\<lceil>?t / d\<rceil> = \<lceil>t / d\<rceil> - 1" by simp
        with \<open>Suc n = _\<close> have "n = nat \<lceil>?t / d\<rceil>" by simp
        with Suc \<open>t \<ge> d\<close> obtain i where "nat \<lceil>?t / d\<rceil> * d < dur xs i" by fastforce
        from assms obtain j where "dur xs j - dur xs i \<ge> d" "j \<ge> i" by auto
        with \<open>dur xs i > _\<close> have "nat \<lceil>?t / d\<rceil> * d + d < dur xs j" by simp
        with True have "dur xs j > nat \<lceil>t / d\<rceil> * d"
        by (metis Suc.hyps(2) \<open>n = nat \<lceil>(t - d) / d\<rceil>\<close> add.commute distrib_left mult.commute 
                  mult.right_neutral of_nat_Suc) 
        then show ?thesis by blast
      next
        case False
        with \<open>t \<ge> 0\<close> \<open>d > 0\<close> have "nat \<lceil>t / d\<rceil> \<le> 1" by simp
        then have "nat \<lceil>t / d\<rceil> * d \<le> d"
        by (metis One_nat_def \<open>Suc n = _\<close> Suc_leI add.right_neutral le_antisym mult.commute
                  mult.right_neutral of_nat_0 of_nat_Suc order_refl zero_less_Suc) 
        with base2 show ?thesis by auto
      qed
    qed
    then obtain i where "dur xs i > ?m * d" by atomize_elim
    moreover from \<open>t \<ge> 0\<close> \<open>d > 0\<close> have "?m * d \<ge> t"
      using pos_divide_le_eq real_nat_ceiling_ge by blast
    ultimately show ?thesis using that[of i] by simp
  qed
qed

lemma not_reset_mono:
  assumes "stream_trans xs" "shd xs c1 \<ge> shd xs c2" "stream_all (\<lambda> u. u \<in> V) xs" "c2 \<in> \<X>"
  shows "(holds (\<lambda> u. u c1 \<ge> u c2) until holds (\<lambda> u. u c1 = 0)) xs" using assms
proof (coinduction arbitrary: xs)
  case prems: (UNTIL xs)
  let ?xs = "stl xs"
  let ?x = "shd xs"
  let ?y = "shd ?xs"
  show ?case
  proof (cases "?x c1 = 0")
    case False
    show ?thesis
    proof (cases "?y c1 = 0")
      case False
      from prems have "trans ?x ?y" by (intro pairwise_pairD[of trans])
      then have "?y c1 \<ge> ?y c2"
      proof cases
        case A: (reset t)
        show ?thesis
        proof (cases "c1 \<in> set t")
          case True
          with A False show ?thesis by auto
        next
          case False
          from prems have "?x c2 \<ge> 0" by (auto simp: V_def)
          with A have "?y c2 \<le> ?x c2" by (cases "c2 \<in> set t") auto
          with A False \<open>?x c1 \<ge> ?x c2\<close> show ?thesis by auto
        qed
      qed (use prems in \<open>auto simp: cval_add_def\<close>)
      moreover from prems have "stream_trans ?xs" "stream_all (\<lambda> u. u \<in> V) ?xs"
        by (auto intro: pairwise_stlD stl_sset)
      ultimately show ?thesis
        using prems by auto
    qed (use prems in \<open>auto intro: UNTIL.base\<close>)
  qed auto
qed

lemma \<R>_divergent_divergent_aux:
  fixes xs :: "('c, t) cval stream"
  assumes "stream_trans xs" "stream_all (\<lambda> u. u \<in> V) xs"
          "(xs !! i) c1 = 0" "\<exists> k > i. k \<le> j \<and> (xs !! k) c2 = 0"
          "\<forall> k > i. k \<le> j \<longrightarrow> (xs !! k) c1 \<noteq> 0"
          "c1 \<in> \<X>" "c2 \<in> \<X>"
  shows "(xs !! j) c1 \<ge> (xs !! j) c2"
proof -
  from assms obtain k where k: "k > i" "k \<le> j" "(xs !! k) c2 = 0" by auto
  with assms(5) \<open>k \<le> j\<close> have "(xs !! k) c1 \<noteq> 0" by auto
  moreover from assms(2) \<open>c1 \<in> \<X>\<close> have "(xs !! k) c1 \<ge> 0" by (auto simp: V_def)
  ultimately have "(xs !! k) c1 > 0" by auto
  with \<open>(xs !! k) c2 = 0\<close> have "shd (sdrop k xs) c1 \<ge> shd (sdrop k xs) c2" by auto
  from not_reset_mono[OF _ this] assms have
    "(holds (\<lambda>u. u c2 \<le> u c1) until holds (\<lambda>u. u c1 = 0)) (sdrop k xs)"
  by (auto intro: sset_sdrop pairwise_sdropD)
  from assms(5) k(2) \<open>k > i\<close> have "\<forall> m \<le> j - k. (sdrop k xs !! m) c1 \<noteq> 0" by simp
  with holds_untilD[OF \<open>(_ until _) _\<close>, of "j - k"] have
    "(sdrop k xs !! (j - k)) c2 \<le> (sdrop k xs !! (j - k)) c1" .
  then show "(xs !! j) c2 \<le> (xs !! j) c1" using k(1,2) by simp
qed

lemma unbounded_all:
  assumes "R \<in> \<R>" "u \<in> R" "unbounded x R" "x \<in> \<X>"
  shows "u x > k x"
proof -
  from assms obtain I r where R: "R = region \<X> I r" "valid_region \<X> k I r" unfolding \<R>_def by auto
  with unbounded_Greater \<open>x \<in> \<X>\<close> assms(3) have "I x = Greater (k x)" by simp
  with \<open>u \<in> R\<close> R \<open>x \<in> \<X>\<close> show ?thesis by force
qed

lemma trans_not_delay_mono:
  "u' c \<le> u c" if "trans u u'" "u \<in> V" "x \<in> \<X>" "u' x = 0" "c \<in> \<X>"
  using \<open>trans u u'\<close>
proof (cases)
  case (reset l)
  with that show ?thesis by (cases "c \<in> set l") (auto simp: V_def)
qed (use that in \<open>auto simp: cval_add_def V_def add_nonneg_eq_0_iff\<close>)

lemma dur_reset:
  assumes "pairwise eq_elapsed xs" "pred_stream (\<lambda> u. u \<in> V) xs" "zero x ([xs !! Suc i]\<^sub>\<R>)" "x \<in> \<X>"
  shows "dur xs (Suc i) - dur xs i = 0"
proof -
  from assms(2) have in_V: "xs !! Suc i \<in> V"
    unfolding stream.pred_set by auto (metis snth.simps(2) snth_sset)
  with elapsed_ge_pos[of "xs !! i" "xs !! Suc i" x] pairwise_Suc[OF assms(1)] assms(2-) have
    "elapsed (xs !! i) (xs !! Suc i) \<le> (xs !! Suc i) x"
    unfolding stream.pred_set by auto
  with in_V assms(3) have "elapsed (xs !! i) (xs !! Suc i) \<le> 0" by (auto simp: zeroD)
  with elapsed_ge0[of "xs !! i" "xs !! Suc i"] have "elapsed (xs !! i) (xs !! Suc i) = 0"
    by linarith
  then show ?thesis by (subst dur_Suc)
qed

lemma resets_mono_0':
  assumes "pairwise eq_elapsed xs" "stream_all (\<lambda> u. u \<in> V) xs" "stream_trans xs"
          "\<forall> j \<le> i. zero x ([xs !! j]\<^sub>\<R>)" "x \<in> \<X>" "c \<in> \<X>"
  shows "(xs !! i) c = (xs !! 0) c \<or> (xs !! i) c = 0"
using assms proof (induction i)
  case 0
  then show ?case by auto
next        
  case (Suc i)
  from Suc.prems have *: "(xs !! Suc i) x = 0" "(xs !! i) x = 0"
    by (blast intro: zeroD snth_sset, force intro: zeroD snth_sset)
  from pairwise_Suc[OF Suc.prems(3)] have "trans (xs !! i) (xs !! Suc i)" .
  then show ?case
  proof cases
    case prems: (succ t)
    with * have "t = 0" unfolding cval_add_def by auto
    with prems have "(xs !! Suc i) c = (xs !! i) c" unfolding cval_add_def by auto
    with Suc show ?thesis by auto
  next
    case prems: (reset l)
    then have "(xs !! Suc i) c = 0 \<or> (xs !! Suc i) c = (xs !! i) c" by (cases "c \<in> set l") auto
    with Suc show ?thesis by auto
  next
    case id
    with Suc show ?thesis by auto
  qed
qed

lemma resets_mono':
  assumes "pairwise eq_elapsed xs" "pred_stream (\<lambda> u. u \<in> V) xs" "stream_trans xs"
          "\<forall> k \<ge> i. k \<le> j \<longrightarrow> zero x ([xs !! k]\<^sub>\<R>)" "x \<in> \<X>" "c \<in> \<X>" "i \<le> j"
  shows "(xs !! j) c = (xs !! i) c \<or> (xs !! j) c = 0" using assms
proof -
  from assms have 1: "stream_all (\<lambda> u. u \<in> V) (sdrop i xs)"
    using sset_sdrop unfolding stream.pred_set by force
  from assms have 2: "pairwise eq_elapsed (sdrop i xs)" by (intro pairwise_sdropD)
  from assms have 3: "stream_trans (sdrop i xs)" by (intro pairwise_sdropD)
  from assms have 4:
    "\<forall>k\<le>j - i. zero x ([sdrop i xs !! k]\<^sub>\<R>)"
  by (simp add: Nat.le_diff_conv2 assms(6))
  from resets_mono_0'[OF 2 1 3 4 assms(5,6)] \<open>i \<le> j\<close> show ?thesis by simp
qed

lemma resets_mono:
  assumes "pairwise eq_elapsed xs" "pred_stream (\<lambda> u. u \<in> V) xs" "stream_trans xs"
          "\<forall> k \<ge> i. k \<le> j \<longrightarrow> zero x ([xs !! k]\<^sub>\<R>)" "x \<in> \<X>" "c \<in> \<X>" "i \<le> j"
  shows "(xs !! j) c \<le> (xs !! i) c" using assms
  using assms by (auto simp: V_def dest: resets_mono'[where c = c] simp: stream.pred_set)

lemma \<R>_divergent_divergent_aux2:
  fixes M :: "(nat \<Rightarrow> bool) set"
  assumes "\<forall> i. \<forall> P \<in> M. \<exists> j \<ge> i. P j" "M \<noteq> {}" "finite M"
  shows "\<forall>i.\<exists>j\<ge>i.\<exists>k>j.\<exists> P \<in> M. P j \<and> P k \<and> (\<forall> m < k. j < m \<longrightarrow> \<not> P m)
       \<and> (\<forall> Q \<in> M. \<exists> m \<le> k. j < m \<and> Q m)"
proof
  fix i
  let ?j1 = "Max {LEAST m. m > i \<and> P m | P. P \<in> M}"
  from \<open>M \<noteq> {}\<close> obtain P where "P \<in> M" by auto
  let ?m = "LEAST m. m > i \<and> P m"
  from assms(1) \<open>P \<in> M\<close> obtain j where "j \<ge> Suc i" "P j" by auto
  then have "j > i" "P j" by auto
  with \<open>P \<in> M\<close> have "?m > i \<and> P ?m" by - (rule LeastI; auto)
  moreover with \<open>finite M\<close> \<open>P \<in> M\<close> have "?j1 \<ge> ?m" by - (rule Max_ge; auto)
  ultimately have "?j1 \<ge> i" by simp
  moreover have "\<exists> m > i. m \<le> ?j1 \<and> P m" if "P \<in> M" for P
  proof -
    let ?m = "LEAST m. m > i \<and> P m"
    from assms(1) \<open>P \<in> M\<close> obtain j where "j \<ge> Suc i" "P j" by auto
    then have "j > i" "P j" by auto
    with \<open>P \<in> M\<close> have "?m > i \<and> P ?m" by - (rule LeastI; auto)
    moreover with \<open>finite M\<close> \<open>P \<in> M\<close> have "?j1 \<ge> ?m" by - (rule Max_ge; auto)
    ultimately show ?thesis by auto
  qed
  ultimately obtain j1 where j1: "j1 \<ge> i" "\<forall> P \<in> M. \<exists> m > i. j1 \<ge> m \<and> P m" by auto
  define k where "k Q = (LEAST k. k > j1 \<and> Q k)" for Q
  let ?k = "Max {k Q | Q. Q \<in> M}"
  let ?P = "SOME P. P \<in> M \<and> k P = ?k"
  let ?j = "Max {j. i \<le> j \<and> j \<le> j1 \<and> ?P j}"
  have "?k \<in> {k Q | Q. Q \<in> M}" using assms by - (rule Max_in; auto)
  then obtain P where P: "k P = ?k" "P \<in> M" by auto
  have "?k \<ge> k Q" if "Q \<in> M" for Q using assms that by - (rule Max_ge; auto)
  have *: "?P \<in> M \<and> k ?P = ?k" using P by - (rule someI[where x = P]; auto)
  with j1 have "\<exists> m > i. j1 \<ge> m \<and> ?P m" by auto
  with \<open>finite _\<close> have "?j \<in> {j. i \<le> j \<and> j \<le> j1 \<and> ?P j}" by - (rule Max_in; auto)
  have k: "k Q > j1 \<and> Q (k Q)" if "Q \<in> M" for Q
  proof -
    from assms(1) \<open>Q \<in> M\<close> obtain m where "m \<ge> Suc j1" "Q m" by auto
    then have "m > j1" "Q m" by auto
    then show "k Q > j1 \<and> Q (k Q)" unfolding k_def by - (rule LeastI; blast)
  qed
  with * \<open>?j \<in> _\<close> have "?P ?k" "?j < ?k" by fastforce+
  have "\<not> ?P m" if "?j < m" "m < ?k" for m
  proof (rule ccontr, simp)
    assume "?P m"
    have "m > j1"
    proof (rule ccontr)
      assume "\<not> j1 < m"
      with \<open>?j < m\<close> \<open>?j \<in> _\<close> have "i \<le> m" "m \<le> j1" by auto
      with \<open>?P m\<close> \<open>finite _\<close> have "?j \<ge> m" by - (rule Max_ge; auto)
      with \<open>?j < m\<close> show False by simp
    qed
    with \<open>?P m\<close> \<open>finite _\<close> have "k ?P \<le> m" unfolding k_def by (auto intro: Least_le)
    with * \<open>m < ?k\<close> show False by auto
  qed
  moreover have "\<exists> m \<le> ?k. ?j < m \<and> Q m" if "Q \<in> M" for Q
  proof -
    from k[OF \<open>Q \<in> M\<close>] have "k Q > j1 \<and> Q (k Q)" .
    moreover with \<open>finite _\<close> \<open>Q \<in> M\<close> have "k Q \<le> ?k" by - (rule Max_ge; auto)
    moreover with \<open>?j \<in> _\<close> \<open>k Q > _ \<and> _\<close> have "?j < k Q" by auto
    ultimately show ?thesis by auto
  qed
  ultimately show
    "\<exists>j\<ge>i.\<exists>k>j.\<exists> P \<in> M. P j \<and> P k \<and> (\<forall> m < k. j < m \<longrightarrow> \<not> P m)
       \<and> (\<forall> Q \<in> M. \<exists> m \<le> k. j < m \<and> Q m)"
    using \<open>?j < ?k\<close> \<open>?j \<in> _\<close> \<open>?P ?k\<close> * by (inst_existentials ?j ?k ?P; blast)
qed

lemma \<R>_divergent_divergent:
  assumes in_S: "pred_stream (\<lambda> u. u \<in> V) xs"
    and div: "\<R>_div (smap (\<lambda> u. [u]\<^sub>\<R>) xs)"
    and trans: "stream_trans xs"
    and trans': "pairwise trans' xs"
    and unbounded_not_const:
    "\<forall>u. (\<forall>c\<in>\<X>. real (k c) < u c) \<longrightarrow> \<not> ev (alw (\<lambda>xs. shd xs = u)) xs"
  shows "divergent xs"
  unfolding divergent_def proof
  fix t
  from pairwise_trans_eq_elapsed[OF trans in_S] have eq_elapsed: "pairwise eq_elapsed xs" .
  define X1 where "X1 = {x. x \<in> \<X> \<and> (\<exists>i. \<forall> j \<ge> i. unbounded x ([xs !! j]\<^sub>\<R>))}"
  let ?i = "Max {(SOME i. \<forall> j \<ge> i. unbounded x ([xs !! j]\<^sub>\<R>)) | x. x \<in> \<X>}"
  from finite(1) non_empty have
    "?i \<in> {(SOME i. \<forall> j \<ge> i. unbounded x ([xs !! j]\<^sub>\<R>)) | x. x \<in> \<X>}"
    by (intro Max_in) auto
  have "unbounded x ([xs !! j]\<^sub>\<R>)" if "x \<in> X1" "j \<ge> ?i" for x j
  proof -
    have "X1 \<subseteq> \<X>" unfolding X1_def by auto
    with finite(1) non_empty \<open>x \<in> X1\<close> have *:
      "?i \<ge> (SOME i. \<forall> j \<ge> i. unbounded x ([xs !! j]\<^sub>\<R>))" (is "?i \<ge> ?k")
      by (intro Max_ge) auto
    from \<open>x \<in> X1\<close> have "\<exists> k. \<forall> j \<ge> k. unbounded x ([xs !! j]\<^sub>\<R>)" by (auto simp: X1_def)
    then have "\<forall> j \<ge> ?k. unbounded x ([xs !! j]\<^sub>\<R>)" by (rule someI_ex)
    moreover from \<open>j \<ge> ?i\<close> \<open>?i \<ge> _\<close> have "j \<ge> ?k" by auto
    ultimately show ?thesis by blast
  qed
  then obtain i where unbounded: "\<forall> x \<in> X1. \<forall> j \<ge> i. unbounded x ([xs !! j]\<^sub>\<R>)"
    using finite by auto
  show "\<exists> n. t < dur xs n"
  proof (cases "\<forall> x \<in> \<X>. (\<exists>i. \<forall> j \<ge> i. unbounded x ([xs !! j]\<^sub>\<R>))")
    case True
    then have "X1 = \<X>" unfolding X1_def by auto
    have "\<exists>k\<ge>j. 0.5 \<le> dur xs k - dur xs j" for j
    proof -
      let ?u = "xs !! max i j"
      from in_S have "?u \<in> [?u]\<^sub>\<R>" "[?u]\<^sub>\<R> \<in> \<R>"
        by (auto simp: stream.pred_set)
      moreover from unbounded \<open>X1 = \<X>\<close> have
        "\<forall> x \<in> \<X>. unbounded x ([?u]\<^sub>\<R>)"
        by force
      ultimately have "\<forall> x \<in> \<X>. ?u x > k x"
        by (auto intro: unbounded_all)
      with unbounded_not_const have "\<not> ev (alw (HLD {?u})) xs"
        unfolding HLD_iff by simp
      then obtain r where
        "r \<ge> max i j" "xs !! r \<noteq> xs !! Suc r"
        apply atomize_elim
        apply (simp add: not_ev_iff not_alw_iff)
        apply (drule alw_sdrop[where n = "max i j"])
        apply (drule alwD)
        apply (subst (asm) (3) stream.collapse[symmetric])
        apply simp
        apply (drule ev_neq_start_implies_ev_neq[simplified comp_def])
        using stream.collapse[of "sdrop (max i j) xs"] by (auto 4 3 elim: ev_sdropD)
      let ?k = "Suc r"
      from in_S have "xs !! ?k \<in> V" using snth_sset unfolding stream.pred_set by blast
      with in_S have *:
        "xs !! r \<in> [xs !! r]\<^sub>\<R>" "[xs !! r]\<^sub>\<R> \<in> \<R>"
        "xs !! ?k \<in> [xs !! ?k]\<^sub>\<R>" "[xs !! ?k]\<^sub>\<R> \<in> \<R>"
        by (auto simp: stream.pred_set)
      from \<open>r \<ge> _\<close> have "r \<ge> i" "?k \<ge> i" by auto
      with unbounded \<open>X1 = \<X>\<close> have
        "\<forall> x \<in> \<X>. unbounded x ([xs !! r]\<^sub>\<R>)" "\<forall> x \<in> \<X>. unbounded x ([xs !! ?k]\<^sub>\<R>)"
        by (auto simp del: snth.simps(2))
      with in_S have "\<forall> x \<in> \<X>. (xs !! r) x > k x" "\<forall> x \<in> \<X>. (xs !! ?k) x > k x"
        using * by (auto intro: unbounded_all)
      moreover from trans' have "trans' (xs !! r) (xs !! ?k)"
        using pairwise_Suc by auto
      ultimately have "(xs !! ?k) = (xs !! r) \<oplus> 0.5"
        unfolding trans'_def using \<open>xs !! r \<noteq> _\<close> by auto
      moreover from pairwise_Suc[OF eq_elapsed] have "eq_elapsed (xs !! r) (xs !! ?k)"
        by auto
      ultimately have 
        "dur xs ?k - dur xs r = 0.5"
        using non_empty by (auto simp: cval_add_def dur_Suc elapsed_eq)
      with dur_mono[of j r xs] \<open>r \<ge> max i j\<close> have "dur xs ?k - dur xs j \<ge> 0.5"
        by auto
      with \<open>r \<ge> max i j\<close> show ?thesis by - (rule exI[where x = ?k]; auto)
    qed
    then show ?thesis by - (rule dur_ev_exceedsI[where d = "0.5"]; auto)
  next
    case False
    define X2 where "X2 = \<X> - X1"
    from False have "X2 \<noteq> {}" unfolding X1_def X2_def by fastforce
    have inf_resets:
      "\<forall>i. (\<exists>j\<ge>i. zero x ([xs !! j]\<^sub>\<R>)) \<and> (\<exists>j\<ge>i. \<not> zero x ([xs !! j]\<^sub>\<R>))" if "x \<in> X2" for x
      using that div unfolding X1_def X2_def \<R>_div_def by fastforce
    have "\<exists> j \<ge> i. \<exists> k > j. \<exists> x \<in> X2. zero x ([xs !! j]\<^sub>\<R>) \<and> zero x ([xs !! k]\<^sub>\<R>)
          \<and> (\<forall> m. j < m \<and> m < k \<longrightarrow> \<not> zero x ([xs !! m]\<^sub>\<R>))
          \<and> (\<forall> x \<in> X2. \<exists> m. j < m \<and> m \<le> k \<and> zero x ([xs !! m]\<^sub>\<R>))
          \<and> (\<forall> x \<in> X1. \<forall> m \<ge> j. unbounded x ([xs !! m]\<^sub>\<R>))" for i
    proof -
      from unbounded obtain i' where i': "\<forall> x \<in> X1. \<forall> m \<ge> i'. unbounded x ([xs !! m]\<^sub>\<R>)" by auto
      then obtain i' where i':
        "i' \<ge> i" "\<forall> x \<in> X1. \<forall> m \<ge> i'. unbounded x ([xs !! m]\<^sub>\<R>)"
        by (cases "i' \<ge> i"; auto)
      from finite(1) have "finite X2" unfolding X2_def by auto
      with \<open>X2 \<noteq> {}\<close> \<R>_divergent_divergent_aux2[where M = "{\<lambda> i. zero x ([xs !! i]\<^sub>\<R>) | x. x \<in> X2}"]
        inf_resets
      have "\<exists>j\<ge>i'. \<exists>k>j. \<exists>P\<in>{\<lambda>i. zero x ([xs !! i]\<^sub>\<R>) |x. x \<in> X2}. P j \<and> P k
        \<and> (\<forall>m<k. j < m \<longrightarrow> \<not> P m) \<and> (\<forall>Q\<in>{\<lambda>i. zero x ([xs !! i]\<^sub>\<R>) |x. x \<in> X2}. \<exists>m\<le>k. j < m \<and> Q m)"
        by force
      then obtain j k x where
        "j \<ge> i'" "k > j" "x \<in> X2" "zero x ([xs !! j]\<^sub>\<R>)" "zero x ([xs !! k]\<^sub>\<R>)"
        "\<forall>m. j < m \<and> m < k \<longrightarrow> \<not> zero x ([xs !! m]\<^sub>\<R>)"
        "\<forall>Q\<in>{\<lambda>i. zero x ([xs !! i]\<^sub>\<R>) |x. x \<in> X2}. \<exists>m\<le>k. j < m \<and> Q m"
        by auto
      moreover from this(7) have "\<forall>x\<in>X2. \<exists>m \<le> k. j < m \<and> zero x ([xs !! m]\<^sub>\<R>)" by auto
      ultimately show ?thesis using i'
        by (inst_existentials j k x) auto
    qed
    moreover have "\<exists> j' \<ge> j. dur xs j' - dur xs i \<ge> 0.5"
      if  x: "x \<in> X2" "i < j" "zero x ([xs !! i]\<^sub>\<R>)" "zero x ([xs !! j]\<^sub>\<R>)"
        and not_reset: "\<forall> m. i < m \<and> m < j \<longrightarrow> \<not> zero x ([xs !! m]\<^sub>\<R>)"
        and X2: "\<forall> x \<in> X2. \<exists> m. i < m \<and> m \<le> j \<and> zero x ([xs !! m]\<^sub>\<R>)"
        and X1: "\<forall> x \<in> X1. \<forall> m \<ge> i. unbounded x ([xs !! m]\<^sub>\<R>)"
      for x i j
    proof -
      have "\<exists>j'>j. \<not> zero x ([xs !! j']\<^sub>\<R>)"
      proof -
        from inf_resets[OF x(1)] obtain j' where "j' \<ge> Suc j" "\<not> zero x ([xs !! j']\<^sub>\<R>)" by auto
        then show ?thesis by - (rule exI[where x = j']; auto)
      qed
      from inf_resets[OF x(1)] obtain j' where "j' \<ge> Suc j" "\<not> zero x ([xs !! j']\<^sub>\<R>)" by auto
      with nat_eventually_critical_path[OF x(4) this(2)]
      obtain j' where j':
        "j' > j" "\<not> zero x ([xs !! j']\<^sub>\<R>)" "\<forall> m \<ge> j. m < j' \<longrightarrow> zero x ([xs !! m]\<^sub>\<R>)"
        by auto
      from \<open>x \<in> X2\<close> have "x \<in> \<X>" unfolding X2_def by simp
      with \<open>i < j\<close> not_reset not_reset_dur \<open>stream_trans _\<close> in_S pairwise_Suc[OF eq_elapsed] have
        "dur xs (j - 1) - dur xs i = (xs !! (j - 1)) x - (xs !! i) x" (is "?d1 = ?d2")
        by (auto simp: stream.pred_set)
      moreover from \<open>zero x ([xs !! i]\<^sub>\<R>)\<close> in_S have "(xs !! i) x = 0"
        by (auto intro: zeroD simp: stream.pred_set)
      ultimately have
        "dur xs (j - 1) - dur xs i = (xs !! (j - 1)) x" (is "?d1 = ?d2")
        by simp
      show ?thesis
      proof (cases "?d1 \<ge> 0.5")
        case True
          (* XXX Fix SMT *)
        with dur_mono[of "j - 1" j xs] have
          "5 / 10 \<le> dur xs j - dur xs i"
          by simp
        then show ?thesis by blast
      next
        case False
        have j_c_bound: "(xs !! j) c \<le> ?d2" if "c \<in> X2" for c
        proof (cases "(xs !! j) c = 0")
          case True
          from in_S \<open>j > _\<close> True \<open>x \<in> \<X>\<close> show ?thesis by (auto simp: V_def stream.pred_set)
        next
          case False
          from X2 \<open>c \<in> X2\<close> in_S have "\<exists>k>i. k \<le> j \<and> (xs !! k) c = 0"
            by (force simp: zeroD stream.pred_set)
          with False have
            "\<exists>k>i. k \<le> j - Suc 0 \<and> (xs !! k) c = 0"
            by (metis Suc_le_eq Suc_pred linorder_neqE_nat not_less not_less_zero)
          moreover from that have "c \<in> \<X>" by (auto simp: X2_def)
          moreover from not_reset in_S \<open>x \<in> \<X>\<close> have
            "\<forall>k>i. k \<le> j - 1 \<longrightarrow> (xs !! k) x \<noteq> 0"
            by (auto simp: zeroI stream.pred_set)
          ultimately have
            "(xs !! (j - 1)) c \<le> ?d2"
            using trans in_S \<open>_ x = 0\<close> \<open>x \<in> \<X>\<close>
            by (auto intro: \<R>_divergent_divergent_aux that simp: stream.pred_set)
          moreover from
            trans_not_delay_mono[OF pairwise_Suc[OF trans], of "j - 1"]
            \<open>x \<in> \<X>\<close> \<open>c \<in> \<X>\<close> \<open>j > _\<close> in_S x(4)
          have "(xs !! j) c \<le> (xs !! (j - 1)) c" by (auto simp: zeroD stream.pred_set)
          ultimately show ?thesis by auto
        qed
        moreover from False \<open>?d1 = ?d2\<close> have "?d2 < 1" by auto
        moreover from in_S have "(xs !! j) c \<ge> 0" if "c \<in> \<X>" for c
          using that by (auto simp: V_def stream.pred_set)
        ultimately have frac_bound: "frac ((xs !! j) c) \<le> ?d2" if "c \<in> X2" for c
          using that frac_le_1I by (force simp: X2_def)

        let ?u = "(xs !! j)"
        from in_S have "[xs !! j]\<^sub>\<R> \<in> \<R>" by (auto simp: stream.pred_set)
        then obtain I r where region:
          "[xs !! j]\<^sub>\<R> = region \<X> I r" "valid_region \<X> k I r"
          unfolding \<R>_def by auto
        let ?S = "{frac (?u c) | c. c \<in> \<X> \<and> isIntv (I c)}"
        have \<X>_X2: "c \<in> X2" if "c \<in> \<X>" "isIntv (I c)" for c
        proof -
          from X1 \<open>j > i\<close> have "\<forall>x\<in>X1. unbounded x ([xs !! j]\<^sub>\<R>)" by auto
          with unbounded_Greater[OF region(2) \<open>c \<in> \<X>\<close>] region(1) that(2) have "c \<notin> X1" by auto
          with \<open>c \<in> \<X>\<close> show "c \<in> X2" unfolding X2_def by auto
        qed
        have frac_bound: "frac ((xs !! j) c) \<le> ?d2" if "c \<in> \<X>" "isIntv (I c)" for c
          using frac_bound[OF \<X>_X2] that .
        have "dur xs (j' - 1) = dur xs j" using j' \<open>x \<in> \<X>\<close> in_S eq_elapsed
          by (subst dur_zero_tail[where \<omega> = "smap (\<lambda> u. [u]\<^sub>\<R>) xs"])
            (auto dest: pairwise_Suc simp: stream.pred_set)
        moreover from dur_reset[OF eq_elapsed in_S, of x "j - 1"] \<open>x \<in> \<X>\<close> x(4) \<open>j > _\<close> have
          "dur xs j = dur xs (j - 1)"
          by (auto simp: stream.pred_set)
        ultimately have "dur xs (j' - 1) = dur xs (j - 1)" by auto
        moreover have "dur xs j' - dur xs (j' - 1) \<ge> (1 - ?d2) / 2"
        proof -
          from \<open>j' > _\<close> have "j' > 0" by auto
          with pairwise_Suc[OF trans', of "j' - 1"] have
            "trans' (xs !! (j' - 1)) (xs !! j')"
            by auto
          moreover from j' have
            "(xs !! (j' - 1)) x = 0" "(xs !! j') x > 0"
            using in_S \<open>x \<in> \<X>\<close> by (force intro: zeroD dest: not_zeroD simp: stream.pred_set)+
          moreover note delayedR_aux = calculation
          obtain t where
            "(xs !! j') = (xs !! (j' - 1)) \<oplus> t" "t \<ge> (1 - ?d2) / 2" "t \<ge> 0"
          proof -
            from in_S have "[xs !! j']\<^sub>\<R> \<in> \<R>" by (auto simp: stream.pred_set)
            then obtain I' r' where region':
              "[xs !! j']\<^sub>\<R> = region \<X> I' r'" "valid_region \<X> k I' r'"
              unfolding \<R>_def by auto            
            let ?S' = "{frac ((xs !! (j' - 1)) c) |c. c \<in> \<X> \<and> Regions.isIntv (I' c)}"

            from finite(1) have "?d2 \<ge> Max (?S' \<union> {0})"
              apply -
              apply (rule Max.boundedI)
                apply fastforce
               apply fastforce
              apply safe
              subgoal premises prems for _ c d
              proof -
                from j' have "(xs !! (j' - 1)) c = ?u c \<or> (xs !! (j' - 1)) c = 0"
                  by (intro resets_mono'[OF eq_elapsed in_S trans _ \<open>x \<in> \<X>\<close> \<open>c \<in> \<X>\<close>]; auto)
                then show ?thesis
                proof (standard, goal_cases)
                  case A: 1
                  show ?thesis
                  proof (cases "c \<in> X1")
                    case True
                    with X1 \<open>j' > j\<close> \<open>j > i\<close> have "unbounded c ([xs !! j']\<^sub>\<R>)" by auto
                    with region' \<open>c \<in> \<X>\<close> have "I' c = Greater (k c)"
                      by (auto intro: unbounded_Greater)
                    with prems show ?thesis by auto
                  next
                    case False
                    with \<open>c \<in> \<X>\<close> have "c \<in> X2" unfolding X2_def by auto
                    with j_c_bound have mono: "(xs !! j) c \<le> (xs !! (j - 1)) x" .
                    from in_S \<open>c \<in> \<X>\<close> have "(xs !! (j' - 1)) c \<ge> 0"
                      unfolding V_def stream.pred_set by auto
                    then have
                      "frac ((xs !! (j' - 1)) c) \<le> (xs !! (j' - 1)) c"
                      using frac_le_self by auto
                    with A mono show ?thesis by auto
                  qed
                next
                  case prems: 2
                    (* XXX *)
                  have "frac (0 :: real) = (0 :: real)" by auto
                  then have "frac (0 :: real) \<le> (0 :: real)" by linarith
                  moreover from in_S \<open>x \<in> \<X>\<close> have "(xs !! (j - 1)) x \<ge> 0"
                    unfolding V_def stream.pred_set by auto
                  ultimately show ?thesis using prems by auto
                qed
              qed
              using in_S \<open>x \<in> \<X>\<close> by (auto simp: V_def stream.pred_set)
            then have le: "(1 - ?d2) / 2 \<le> (1 - Max (?S' \<union> {0})) / 2" by simp

            let ?u = "xs !! j'"
            let ?u' = "xs !! (j' - 1)"
            from in_S have *: "?u' \<in> V" "[?u']\<^sub>\<R> \<in> \<R>" "?u \<in> V" "[?u]\<^sub>\<R> \<in> \<R>"
              by (auto simp: stream.pred_set)
            from pairwise_Suc[OF trans, of "j' - 1"] \<open>j' > j\<close> have
              "trans (xs !! (j' - 1)) (xs !! j')"
              by auto
            then have Succ:
              "[xs !! j']\<^sub>\<R> \<in> Succ \<R> ([xs !! (j' - 1)]\<^sub>\<R>) \<and> (\<exists> t\<ge> 0. ?u = ?u' \<oplus> t)"
            proof cases
              case prems: (succ t)
              from * have "?u' \<in> [?u']\<^sub>\<R>" by auto
              with prems * show ?thesis by auto
            next
              case (reset l)
              with \<open>?u' \<in> V\<close> have "?u x \<le> ?u' x" by (cases "x \<in> set l") (auto simp: V_def)
              from j' have "zero x ([?u']\<^sub>\<R>)" by auto
              with \<open>?u' \<in> V\<close> have "?u' x = 0" unfolding zero_def by auto
              with \<open>?u x \<le> _\<close> \<open>?u x > 0\<close> show ?thesis by auto
            next
              case id
              with * Succ_refl[of \<R> \<X> k, folded \<R>_def, OF _ finite(1)] show ?thesis
                unfolding cval_add_def by auto
            qed
            then obtain t where t: "?u = xs !! (j' - 1) \<oplus> t" "t \<ge> 0" by auto
            note Succ = Succ[THEN conjunct1]

            show ?thesis
            proof (cases "\<exists> c \<in> X2. \<exists> d :: nat. ?u c = d")
              case True
              from True obtain c and d :: nat where c:
                "c \<in> \<X>" "c \<in> X2" "?u c = d"
                by (auto simp: X2_def)
              have "?u x > 0" by fact
              from pairwise_Suc[OF eq_elapsed, of "j' - 1"] \<open>j' > j\<close> have
                "eq_elapsed (xs !! (j' - 1)) ?u"
                by auto
              moreover from
                elapsed_eq[OF this \<open>x \<in> \<X>\<close>] \<open>(xs !! (j' - 1)) x = 0\<close> \<open>(xs !! j') x > 0\<close>
              have "elapsed (xs !! (j' - 1)) (xs !! j') > 0"
                by auto
              ultimately have
                "?u c - (xs !! (j' - 1)) c > 0"
                using \<open>c \<in> \<X>\<close> unfolding eq_elapsed_def by auto
              moreover from in_S have "xs !! (j' - 1) \<in> V" by (auto simp: stream.pred_set)
              ultimately have "?u c > 0" using \<open>c \<in> \<X>\<close> unfolding V_def by auto
              from region' in_S \<open>c \<in> \<X>\<close> have "intv_elem c ?u (I' c)"
                by (force simp: stream.pred_set)
              with \<open>?u c = d\<close> \<open>?u c > 0\<close> have "?u c \<ge> 1" by auto
              moreover have "(xs !! (j' - 1)) c \<le> 0.5"
              proof -
                have "(xs !! (j' - 1)) c \<le> (xs !! j) c"
                  (* XXX This proof is duplicated at least once above *)
                  using j'(1,3)
                  by (auto intro: resets_mono[OF eq_elapsed in_S trans _ \<open>x \<in> \<X>\<close> \<open>c \<in> \<X>\<close>])
                also have "\<dots> \<le> ?d2" using j_c_bound[OF \<open>c \<in> X2\<close>] .
                also from \<open>?d1 = ?d2\<close> \<open>\<not> 5 / 10 \<le> _\<close> have "\<dots> \<le> 0.5" by simp
                finally show ?thesis .
              qed
              moreover have "?d2 \<ge> 0" using in_S \<open>x \<in> \<X>\<close> by (auto simp: V_def stream.pred_set)
              ultimately have "?u c - (xs !! (j' - 1)) c \<ge> (1 - ?d2) / 2" by auto
              with t have "t \<ge> (1 - ?d2) / 2" unfolding cval_add_def by auto
              with t show ?thesis by (auto intro: that)
            next
              case F: False
              have not_const: "\<not> isConst (I' c)" if "c \<in> \<X>" for c
              proof (rule ccontr, simp)
                assume A: "isConst (I' c)"
                show False
                proof (cases "c \<in> X1")
                  case True
                  with X1 \<open>j' > j\<close> \<open>j > _\<close> have "unbounded c ([xs !! j']\<^sub>\<R>)" by auto
                  with unbounded_Greater \<open>c \<in> \<X>\<close> region' have "isGreater (I' c)" by force
                  with A show False by auto
                next
                  case False
                  with \<open>c \<in> \<X>\<close> have "c \<in> X2" unfolding X2_def by auto
                  from region' in_S \<open>c \<in> \<X>\<close> have "intv_elem c ?u (I' c)"
                    unfolding stream.pred_set  by force
                  with \<open>c \<in> X2\<close> A False F show False by auto
                qed
              qed
              have "\<nexists>x. x \<le> k c \<and> (xs !! j') c = real x" if "c \<in> \<X>" for c
              proof (cases "c \<in> X2"; safe)
                fix d
                assume "c \<in> X2" "(xs !! j') c = real d"
                with F show False by auto
              next
                fix d
                assume "c \<notin> X2" 
                with that have "c \<in> X1" unfolding X2_def by auto
                with X1 \<open>j' > j\<close> \<open>j > i\<close> have "unbounded c ([?u]\<^sub>\<R>)" by auto
                from unbounded_all[OF _ _ this] \<open>c \<in> \<X>\<close> in_S have "?u c > k c"
                  by (force simp: stream.pred_set)
                moreover assume "?u c = real d" "d \<le> k c"
                ultimately show False by auto
              qed
              with delayedR_aux have
                "(xs !! j') = delayedR ([xs !! j']\<^sub>\<R>) (xs !! (j' - 1))"
                using \<open>x \<in> \<X>\<close> unfolding trans'_def by auto
              from not_const region'(1)  in_S Succ(1) have
                "\<exists>t\<ge>0. delayedR ([xs !! j']\<^sub>\<R>) (xs !! (j' - 1)) = xs !! (j' - 1) \<oplus> t \<and>
                      (1 - Max (?S' \<union> {0})) / 2 \<le> t"
                apply simp
                apply (rule delayedR_correct(2)[OF _ _ region'(2), simplified])
                by (auto simp: stream.pred_set)
              with le \<open>_ = delayedR _ _\<close> show ?thesis by (auto intro: that)
            qed
          qed
          moreover from pairwise_Suc[OF eq_elapsed, of "j' - 1"] \<open>j' > 0\<close> have
            "eq_elapsed (xs !! (j' - 1)) (xs !! j')"
            by auto
          ultimately show "dur xs j' - dur xs (j' - 1) \<ge> (1 - ?d2) / 2" 
            using \<open>j' > 0\<close> dur_Suc[of _ "j' - 1"] \<open>x \<in> \<X>\<close> by (auto simp: cval_add_def elapsed_eq)
        qed
        moreover from dur_mono[of i "j - 1" xs] \<open>i < j\<close> have "dur xs i \<le> dur xs (j - 1)" by simp
        ultimately have "dur xs j' - dur xs i \<ge> 0.5" unfolding \<open>?d1 = ?d2\<close>[symmetric] by auto
        then show ?thesis using \<open>j < j'\<close> by - (rule exI[where x = j']; auto)
      qed
    qed
    moreover
    have "\<exists> j' \<ge> i. dur xs j' - dur xs i \<ge> 0.5" for i
    proof -
      from calculation(1)[of i] obtain j k x where
        "j\<ge>i" "k>j" "x\<in>X2" "zero x ([xs !! j]\<^sub>\<R>)"
        "zero x ([xs !! k]\<^sub>\<R>)"
        "\<forall>m. j < m \<and> m < k \<longrightarrow> \<not> zero x ([xs !! m]\<^sub>\<R>)"
        "\<forall>x\<in>X2. \<exists>m>j. m \<le> k \<and> zero x ([xs !! m]\<^sub>\<R>)"
        "\<forall>x\<in>X1. \<forall>m\<ge>j. unbounded x ([xs !! m]\<^sub>\<R>)"
        by auto
      from calculation(2)[OF this(3,2,4-8)] obtain j' where
        "j'\<ge>k" "5 / 10 \<le> dur xs j' - dur xs j"
        by auto
      with dur_mono[of i j xs] \<open>j \<ge> i\<close> \<open>k > j\<close> show ?thesis by (intro exI[where x = j']; auto)
    qed
    then show ?thesis by - (rule dur_ev_exceedsI[where d = "0.5"]; auto)
  qed
qed

lemma cfg_on_div_absc:
  notes in_space_UNIV[measurable]
  assumes "cfg \<in> cfg_on_div st" "st \<in> S"
  shows "absc cfg \<in> R_G_cfg_on_div (abss st)"
proof -
  from assms have *: "cfg \<in> MDP.cfg_on st" "state cfg = st" "div_cfg cfg"
    unfolding cfg_on_div_def by auto
  with assms have "cfg \<in> valid_cfg" by (auto intro: MDP.valid_cfgI)
  have "almost_everywhere (MDP.MC.T cfg) (MDP.MC.enabled cfg)"
    by (rule MDP.MC.AE_T_enabled)
  moreover from * have "AE x in MDP.MC.T cfg. divergent (smap (snd \<circ> state) x)"
    by (simp add: div_cfg_def)
  ultimately have "AE x in MDP.MC.T cfg. \<R>_div (smap (snd \<circ> state) (smap absc x))"
  proof eventually_elim
    case (elim \<omega>)
    let ?xs = "smap (snd o state) \<omega>"
    from MDP.pred_stream_cfg_on[OF \<open>_ \<in> valid_cfg\<close> \<open>MDP.MC.enabled _ _\<close>] have *:
      "pred_stream (\<lambda> x. x \<in> S) (smap state \<omega>)"
      by (auto simp: stream.pred_set)
    have "[snd (state x)]\<^sub>\<R> = snd (abss (state x))" if "x \<in> sset \<omega>" for x
    proof -
      from * that have "state x \<in> S" by (auto simp: stream.pred_set)
      then have "snd (abss (state x)) = [snd (state x)]\<^sub>\<R>" by (metis abss_S snd_conv surj_pair)
      then show ?thesis ..
    qed
    then have "smap (\<lambda>z. [snd (state z)]\<^sub>\<R>) \<omega> = (smap (\<lambda>z. snd (abss (state z))) \<omega>)" by auto
    from * have  "pred_stream (\<lambda> u. u \<in> V) ?xs"
      apply (simp add: map_def stream.pred_set)
      apply (subst (asm) surjective_pairing)
      using S_V by blast
    moreover have "stream_trans ?xs"
      by (rule enabled_stream_trans \<open>_ \<in> valid_cfg\<close> \<open>MDP.MC.enabled _ _\<close>)+
    ultimately show ?case using \<open>divergent _\<close> \<open>smap _ \<omega> = _\<close>
      by - (drule divergent_\<R>_divergent, auto simp add: stream.map_comp state_absc)
  qed
  with \<open>cfg \<in> valid_cfg\<close> have "R_G_div_cfg (absc cfg)" unfolding R_G_div_cfg_def
    by (subst absc_distr_self) (auto intro: MDP.valid_cfgI simp: AE_distr_iff)
  with R_G.valid_cfgD \<open>cfg \<in> valid_cfg\<close> * show ?thesis unfolding R_G_cfg_on_div_def by auto force
qed

definition
  "alternating cfg = (AE \<omega> in MDP.MC.T cfg.
      alw (ev (HLD {cfg. \<forall>cfg' \<in> K_cfg cfg. fst (state cfg') = fst (state cfg)})) \<omega>)"

lemma K_cfg_same_loc_iff:
  "(\<forall>cfg'\<in> K_cfg cfg. fst (state cfg') = fst (state cfg))
  \<longleftrightarrow> (\<forall>cfg'\<in> K_cfg (absc cfg). fst (state cfg') = fst (state (absc cfg)))"
  if "cfg \<in> valid_cfg"
  using that by (auto simp: state_absc fst_abss K_cfg_map_absc)

lemma (in -) stream_all2_flip:
  "stream_all2 (\<lambda>a b. R b a) xs ys = stream_all2 R ys xs"
  by (standard; coinduction arbitrary: xs ys; auto dest: sym)

(* TODO: Lots of duplication here, e.g. with path_measure_eq_repcs1_new *)
lemma AE_alw_ev_same_loc_iff:
  assumes "cfg \<in> valid_cfg"
  shows "alternating cfg \<longleftrightarrow> alternating (absc cfg)"
  unfolding alternating_def
  apply (simp add: MDP.MC.T.AE_iff_emeasure_eq_1)
  subgoal
  proof -
    show ?thesis (is "(?x = 1) = (?y = 1)")
    proof -
      have *: "stream_all2 (\<lambda>s t. t = absc s) x y = stream_all2 (=) y (smap absc x)" for x y
        by (subst stream_all2_flip) simp
      have "?x = ?y"
        apply (rule T_eq_rel_half[where f = absc and S = valid_cfg, OF HOL.refl, rotated 2])
        subgoal
          apply (simp add: space_stream_space rel_set_strong_def)
          apply (intro allI impI)
          apply (frule stream.rel_mono_strong[where Ra = "\<lambda>s t. t = absc s"])
          by (auto simp: * stream.rel_eq stream_all2_refl alw_holds_pred_stream_iff[symmetric]
              K_cfg_same_loc_iff HLD_def elim!: alw_ev_cong)
        subgoal
          by (rule rel_funI) (auto intro!: rel_pmf_reflI simp: pmf.rel_map(2) K_cfg_map_absc)
        using \<open>cfg \<in> valid_cfg\<close> by simp+
      then show ?thesis
        by simp
    qed
  qed
  done

lemma AE_alw_ev_same_loc_iff':
  assumes "cfg \<in> R_G.cfg_on (abss st)" "st \<in> S"
  shows "alternating cfg \<longleftrightarrow> alternating (repcs st cfg)"
proof -
  from assms have "cfg \<in> R_G.valid_cfg"
    by (auto intro: R_G.valid_cfgI)
  with assms show ?thesis
    by (subst AE_alw_ev_same_loc_iff) (auto simp: absc_repcs_id)
qed

lemma (in -) cval_add_non_id:
  False if "b \<oplus> d = b" "d > 0" for d :: real
proof -
  from that(1) have "(b \<oplus> d) x = b x"
    by (rule fun_cong)
  with \<open>d > 0\<close> show False
    unfolding cval_add_def by simp
qed

lemma repcs_unbounded_AE_non_loop_end_strong:
  assumes "cfg \<in> R_G.cfg_on (abss st)" "st \<in> S"
    and "alternating cfg"
  shows "AE \<omega> in MDP.MC.T (repcs st cfg).
      (\<forall> u :: ('c \<Rightarrow> real). (\<forall> c \<in> \<X>. u c > real (k c)) \<longrightarrow>
      \<not> (ev (alw (\<lambda> xs. shd xs = u))) (smap (snd o state) \<omega>))" (is "AE \<omega> in ?M. ?P \<omega>")
proof -
  from assms have "cfg \<in> R_G.valid_cfg"
    by (auto intro: R_G.valid_cfgI)
  with assms(1) have "repcs st cfg \<in> valid_cfg"
    by auto
  from R_G.valid_cfgD[OF \<open>cfg \<in> R_G.valid_cfg\<close>] have "cfg \<in> R_G.cfg_on (state cfg)" .
  let ?U = "\<lambda> u. \<Union> l \<in> L. {\<mu> \<in> K (l, u). \<mu> \<noteq> return_pmf (l, u) \<and> (\<forall> x \<in> \<mu>. fst x = l)}"
  let ?r = "\<lambda> u. Sup ({0} \<union> (\<lambda> \<mu>. measure_pmf \<mu> {x. snd x = u}) ` ?U u)"
  have lt_1: "?r u < 1" for u
  proof -
    have *: "emeasure (measure_pmf \<mu>) {x. snd x = u} < 1"
      if "\<mu> \<noteq> return_pmf (l, u)" "\<forall>x\<in>set_pmf \<mu>. fst x = l" for \<mu> and l :: 's
    proof (rule ccontr)
      assume "\<not> emeasure (measure_pmf \<mu>) {x. snd x = u} < 1"
      then have "1 = emeasure (measure_pmf \<mu>) {x. snd x = u}"
        using measure_pmf.emeasure_ge_1_iff by force
      also from that(2) have "\<dots> \<le> emeasure (measure_pmf \<mu>) {(l, u)}"
        by (subst emeasure_Int_set_pmf[symmetric]) (auto intro!: emeasure_mono)
      finally show False
        by (simp add: measure_pmf.emeasure_ge_1_iff measure_pmf_eq_1_iff that(1))
    qed
    let ?S =
      "{map_pmf (\<lambda> (X, l). (l, ([X := 0]u))) \<mu> | \<mu> l g. (l, g, \<mu>) \<in> trans_of A}"
    have "(\<lambda> \<mu>. measure_pmf \<mu> {x. snd x = u}) ` ?U u
      \<subseteq> {0, 1} \<union> (\<lambda> \<mu>. measure_pmf \<mu> {x. snd x = u}) ` ?S"
      by (force elim!: K.cases)
    moreover have "finite ?S"
    proof -
      have "?S \<subseteq> (\<lambda> (l, g, \<mu>). map_pmf (\<lambda> (X, l). (l, ([X := 0]u))) \<mu>) ` trans_of A"
        by force
      also from finite(3) have "finite \<dots>" ..
      finally show ?thesis .
    qed
    ultimately have "finite ((\<lambda> \<mu>. measure_pmf \<mu> {x. snd x = u}) ` ?U u)"
      by (auto intro: finite_subset)
    then show ?thesis
      by (fastforce intro: * finite_imp_Sup_less)
  qed
  { fix l :: 's and u :: "'c \<Rightarrow> real" and cfg :: "('s \<times> ('c \<Rightarrow> real) set) cfg"
    assume unbounded: "\<forall> c \<in> \<X>. u c > k c" and "cfg \<in> R_G.cfg_on (abss (l, u))" "abss (l, u) \<in> \<S>"
      and same_loc: "\<forall> cfg' \<in> K_cfg cfg. fst (state cfg') = l"
    then have "cfg \<in> R_G.valid_cfg" "repcs (l, u) cfg \<in> valid_cfg"
      by (auto intro: R_G.valid_cfgI)
    then have cfg_on: "repcs (l, u) cfg \<in> MDP.cfg_on (l, u)"
      by (auto dest: MDP.valid_cfgD)
    from \<open>cfg \<in> R_G.cfg_on _\<close> have "action cfg \<in> \<K> (abss (l, u))"
      by (rule R_G.cfg_onD_action)
        (* TODO: Pull out? *)
    have K_cfg_rept: "state ` K_cfg (repcs (l, u) cfg) = rept (l, u) (action cfg)"
      unfolding K_cfg_def by (force simp: action_repcs)
    have "l \<in> L"
      using MDP.valid_cfg_state_in_S \<open>repcs (l, u) cfg \<in> MDP.valid_cfg\<close> by fastforce
    moreover have "rept (l, u) (action cfg) \<noteq> return_pmf (l, u)"
    proof (rule ccontr, simp)
      assume "rept (l, u) (action cfg) = return_pmf (l, u)"
      then have "action cfg = return_pmf (abss (l, u))"
        using abst_rept_id[OF \<open>action cfg \<in> _\<close>]
        by (simp add: abst_def)
      moreover have "(l, u) \<in> S"
        using \<open>_ \<in> \<S>\<close> by (auto dest: \<S>_abss_S)
      moreover have "abss (l, u) = (l, [u]\<^sub>\<R>)"
        by (metis abss_S calculation(2))
      ultimately show False
        using \<open>rept (l, u) _ = _\<close> unbounded unfolding rept_def by (auto dest: cval_add_non_id)
    qed
    moreover have "rept (l, u) (action cfg) \<in> K (l, u)"
    proof -
      have "action (repcs (l, u) cfg) \<in> K (l, u)"
        using cfg_on by blast
      then show ?thesis
        by (simp add: repcs_def)
    qed
    moreover have "\<forall>x\<in>set_pmf (rept (l, u) (action cfg)). fst x = l"
      using same_loc K_cfg_same_loc_iff[of "repcs (l, u) cfg"]
        \<open>repcs (l, u) _ \<in> valid_cfg\<close> \<open>cfg \<in> R_G.valid_cfg\<close> \<open>cfg \<in> R_G.cfg_on _\<close>
      by (simp add: absc_repcs_id fst_abss K_cfg_rept[symmetric])
    ultimately have "rept (l, u) (action cfg) \<in> ?U u"
      by blast
    then have "measure_pmf (rept (l, u) (action cfg)) {x. snd x = u} \<le> ?r u"
      by (fastforce intro: Sup_upper)
    moreover have "rept (l, u) (action cfg) = action (repcs (l, u) cfg)"
      by (simp add: repcs_def)
    ultimately have "measure_pmf (action (repcs (l, u) cfg)) {x. snd x = u} \<le> ?r u"
      by auto
  }
  note * = this
  let ?S = "{cfg. \<exists> cfg' s. cfg' \<in> R_G.valid_cfg \<and> cfg = repcs s cfg' \<and> abss s = state cfg'}"
  have start: "repcs st cfg \<in> ?S"
    using \<open>cfg \<in> R_G.valid_cfg\<close> assms unfolding R_G_cfg_on_div_def
    by clarsimp (inst_existentials cfg "fst st" "snd st", auto)
  have step: "y \<in> ?S" if "y \<in> K_cfg x" "x \<in> ?S" for x y
    using that apply safe
    subgoal for cfg' l u
      apply (inst_existentials "absc y" "state y")
      subgoal
        by blast
      subgoal
        by (metis
            K_cfg_valid_cfgD R_G.valid_cfgD R_G.valid_cfg_state_in_S absc_repcs_id cont_absc_1
            cont_repcs1 repcs_valid
            )
      subgoal
        by (simp add: state_absc)
      done
    done
  have **: "x \<in> ?S" if "(repcs st cfg, x) \<in> MDP.MC.acc" for x
  proof -
    from MDP.MC.acc_relfunD[OF that] obtain n where "((\<lambda> a b. b \<in> K_cfg a) ^^ n) (repcs st cfg) x" .
    then show ?thesis
    proof (induction n arbitrary: x) (* XXX Extract induction rule *)
      case 0
      with start show ?case
        by simp
    next
      case (Suc n)
      from this(2)[simplified] show ?case
        apply (rule relcomppE)
        apply (erule step)
        apply (erule Suc.IH)
        done
    qed
  qed
  have ***: "almost_everywhere (MDP.MC.T (repcs st cfg)) (alw (HLD ?S))"
    by (rule AE_mp[OF MDP.MC.AE_T_reachable]) (fastforce dest: ** simp: HLD_iff elim: alw_mono)

  from \<open>alternating cfg\<close> assms have "alternating (repcs st cfg)"
    by (simp add: AE_alw_ev_same_loc_iff'[of _ st])
  then have alw_ev_same2: "almost_everywhere (MDP.MC.T (repcs st cfg))
     (alw (\<lambda>\<omega>. HLD (state -` snd -` {u}) \<omega> \<longrightarrow>
      ev (HLD {cfg. \<forall>cfg'\<in>set_pmf (K_cfg cfg). fst (state cfg') = fst (state cfg)}) \<omega>))"
    for u unfolding alternating_def by (auto elim: alw_mono)

  let ?X = "{cfg :: ('s \<times> ('c \<Rightarrow> real)) cfg. \<forall> c \<in> \<X>. snd (state cfg) c > k c}"
  let ?Y = "{cfg. \<forall> cfg' \<in> K_cfg cfg. fst (state cfg') = fst (state cfg)}"

  have "(AE \<omega> in ?M. ?P \<omega>) \<longleftrightarrow>
    (AE \<omega> in ?M. \<forall> u :: ('c \<Rightarrow> real).
      (\<forall> c \<in> \<X>. u c > k c) \<and> u \<in> snd ` state ` (MDP.MC.acc `` {repcs st cfg}) \<longrightarrow>
      \<not> (ev (alw (\<lambda> xs. shd xs = u))) (smap (snd o state) \<omega>))" (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    then show ?R
      by eventually_elim auto
  next
    assume ?R
    with MDP.MC.AE_T_reachable[of "repcs st cfg"] show ?L
    proof (eventually_elim, intro allI impI notI, goal_cases)
      case (1 \<omega> u)
      then show ?case
        by - (intro alw_HLD_smap alw_disjoint_ccontr[where
              S = "(snd o state) ` MDP.MC.acc `` {repcs st cfg}"
              and R = "{u}" and \<omega> = "smap (snd o state) \<omega>"
              ]; auto simp: HLD_iff)
    qed
  qed

  also have "\<dots> \<longleftrightarrow>
      (\<forall> u :: ('c \<Rightarrow> real).
        (\<forall> c \<in> \<X>. u c > k c) \<and> u \<in> snd ` state ` (MDP.MC.acc `` {repcs st cfg}) \<longrightarrow>
        (AE \<omega> in ?M. \<not> (ev (alw (\<lambda> xs. shd xs = u))) (smap (snd o state) \<omega>)))"
    using MDP.MC.countable_reachable[of "repcs st cfg"]
    by - (rule AE_all_imp_countable,
        auto intro: countable_subset[where B = "snd ` state ` MDP.MC.acc `` {repcs st cfg}"])
  also show ?thesis
    unfolding calculation
    apply clarsimp
    subgoal for l u x
      apply (rule
          MDP.non_loop_tail_strong[simplified, of snd "snd (state x)" ?Y ?S "?r (snd (state x))"]
          )
      subgoal
        apply safe
        subgoal premises prems for cfg l1 u1 _ cfg' l2 u2
        proof -
          have [simp]: "l2 = l1" "u2 = u1"
            subgoal
              by (metis MDP.cfg_onD_state Pair_inject prems(4) state_repcs)
            subgoal
              by (metis MDP.cfg_onD_state prems(4) snd_conv state_repcs)
            done
          with prems have [simp]: "u2 = u"
            by (metis \<open>(l, u) = state x\<close> \<open>snd (l1, u1) = snd (state x)\<close> \<open>u2 = u1\<close> snd_conv)
          have [simp]: "snd -` {snd (state x)} = {y. snd y = snd (state x)}"
            by (simp add: vimage_def)
          from prems show ?thesis
            apply simp
            apply (erule *[simplified])
            subgoal
              using prems(1) prems(2)[symmetric] prems(3-) by (auto simp: R_G.valid_cfg_def)
            subgoal
              using prems(1) prems(2)[symmetric] prems(3-) by (auto simp: R_G.valid_cfg_def)
            subgoal
              using K_cfg_same_loc_iff[of "repcs (l1, snd (state x)) cfg'"]
              by (simp add: absc_repcs_id) (metis fst_abss fst_conv repcs_valid)
            done
        qed
        done
      subgoal
        by (auto intro: lt_1[simplified])
        apply (rule MDP.valid_cfgD[OF \<open>repcs st cfg \<in> valid_cfg\<close>]; fail)
      subgoal
        using *** unfolding alw_holds_pred_stream_iff[symmetric] HLD_def .
      subgoal
        by (rule alw_ev_same2)
      done
    done
qed

lemma cfg_on_div_repcs_strong:
  notes in_space_UNIV[measurable]
  assumes "cfg \<in> R_G_cfg_on_div (abss st)" "st \<in> S" and "alternating cfg"
  shows "repcs st cfg \<in> cfg_on_div st"
proof -
  let ?st = "abss st"
  let ?cfg = "repcs st cfg"
  from assms have *:
    "cfg \<in> R_G.cfg_on ?st" "state cfg = ?st" "R_G_div_cfg cfg"
    unfolding R_G_cfg_on_div_def by auto
  with assms have "cfg \<in> R_G.valid_cfg" by (auto intro: R_G.valid_cfgI)
  with \<open>st \<in> S\<close> \<open>_ = ?st\<close> have "?cfg \<in> valid_cfg" by auto
  from *(1) \<open>st \<in> S\<close> \<open>alternating cfg\<close> have
    "AE \<omega> in MDP.MC.T ?cfg. \<forall>u. (\<forall>c\<in>\<X>. real (k c) < u c) \<longrightarrow>
                          \<not> ev (alw (\<lambda>xs. shd xs = u)) (smap (snd \<circ> state) \<omega>)"
    by (rule repcs_unbounded_AE_non_loop_end_strong)
  \<comment> \<open>Move to lower level\<close>
  moreover from *(2,3) have "AE \<omega> in MDP.MC.T ?cfg. \<R>_div (smap (snd \<circ> state) (smap absc \<omega>))"
    unfolding R_G_div_cfg_def
    by (subst (asm) R_G_trace_space_distr_eq[OF \<open>cfg \<in> R_G.valid_cfg\<close>]; simp add: AE_distr_iff)
  ultimately have "div_cfg ?cfg"
    unfolding div_cfg_def using MDP.MC.AE_T_enabled[of ?cfg]
  proof eventually_elim
    case prems: (elim \<omega>)
      let ?xs = "smap (snd o state) \<omega>"
      from MDP.pred_stream_cfg_on[OF \<open>_ \<in> valid_cfg\<close> \<open>MDP.MC.enabled _ _\<close>] have *:
        "pred_stream (\<lambda> x. x \<in> S) (smap state \<omega>)"
        by (auto simp: stream.pred_set)
      have "[snd (state x)]\<^sub>\<R> = snd (abss (state x))" if "x \<in> sset \<omega>" for x
      proof -
        from * that have "state x \<in> S" by (auto simp: stream.pred_set)
        then have "snd (abss (state x)) = [snd (state x)]\<^sub>\<R>" by (metis abss_S snd_conv surj_pair)
        then show ?thesis ..
      qed
      then have "smap (\<lambda>z. [snd (state z)]\<^sub>\<R>) \<omega> = (smap (\<lambda>z. snd (abss (state z))) \<omega>)" by auto
      from * have  "pred_stream (\<lambda> u. u \<in> V) ?xs"
        by (simp add: map_def stream.pred_set, subst (asm) surjective_pairing, blast)
      moreover have "stream_trans ?xs"
        by (rule enabled_stream_trans \<open>_ \<in> valid_cfg\<close> \<open>MDP.MC.enabled _ _\<close>)+
      moreover have "pairwise trans' ?xs"
        using \<open>_ \<in> R_G.valid_cfg\<close> \<open>state cfg = _\<close>[symmetric] \<open>MDP.MC.enabled _ _\<close>
        by (rule enabled_stream_trans')
      moreover from prems(1) have
        "\<forall>u. (\<forall>c\<in>\<X>. real (k c) < u c) \<longrightarrow> \<not> ev (alw (\<lambda>xs. snd (shd xs) = u)) (smap state \<omega>)"
        by simp
      ultimately show ?case using \<open>\<R>_div _\<close>
        by (simp add: stream.map_comp state_absc \<open>smap _ \<omega> = _\<close> \<R>_divergent_divergent)
    qed
  with MDP.valid_cfgD \<open>cfg \<in> R_G.valid_cfg\<close> * show ?thesis unfolding cfg_on_div_def by auto force
qed

lemma repcs_unbounded_AE_non_loop_end:
  assumes "cfg \<in> R_G.cfg_on (abss st)" "st \<in> S"
  shows "AE \<omega> in MDP.MC.T (repcs st cfg).
      (\<forall> s :: ('s \<times> ('c \<Rightarrow> real)). (\<forall> c \<in> \<X>. snd s c > k c) \<longrightarrow>
      \<not> (ev (alw (\<lambda> xs. shd xs = s))) (smap state \<omega>))" (is "AE \<omega> in ?M. ?P \<omega>")
proof -
  from assms have "cfg \<in> R_G.valid_cfg"
    by (auto intro: R_G.valid_cfgI)
  with assms(1) have "repcs st cfg \<in> valid_cfg"
    by auto
  from R_G.valid_cfgD[OF \<open>cfg \<in> R_G.valid_cfg\<close>] have "cfg \<in> R_G.cfg_on (state cfg)" .
  let ?K = "\<lambda> x. {\<mu> \<in> K x. \<mu> \<noteq> return_pmf x}"
  let ?r = "\<lambda> x. Sup ((\<lambda> \<mu>. measure_pmf \<mu> {x}) ` ?K x)"
  have lt_1: "?r x < 1" if "\<mu> \<in> ?K x" for \<mu> x
  proof -
    have *: "emeasure (measure_pmf \<mu>) {x} < 1" if "\<mu> \<noteq> return_pmf x" for \<mu>
    proof (rule ccontr)
      assume "\<not> emeasure (measure_pmf \<mu>) {x} < 1"
      then have "emeasure (measure_pmf \<mu>) {x} = 1"
        using measure_pmf.emeasure_ge_1_iff by force
      with that show False
        by (simp add: measure_pmf_eq_1_iff)
    qed
    let ?S =
      "{map_pmf (\<lambda> (X, l). (l, ([X := 0]u))) \<mu> | \<mu> l u g.
          x = (l, u) \<and> (l, g, \<mu>) \<in> trans_of A}"
    have "(\<lambda> \<mu>. measure_pmf \<mu> {x}) ` ?K x
      \<subseteq> {0, 1} \<union> (\<lambda> \<mu>. measure_pmf \<mu> {x}) ` ?S"
      by (force elim!: K.cases)
    moreover have "finite ?S"
    proof -
      have "?S \<subseteq> (\<lambda> (l, g, \<mu>). map_pmf (\<lambda> (X, l). (l, ([X := 0](snd x)))) \<mu>) ` trans_of A"
        by force
      also from finite(3) have "finite \<dots>" ..
      finally show ?thesis .
    qed
    ultimately have "finite ((\<lambda> \<mu>. measure_pmf \<mu> {x}) ` ?K x)"
      by (auto intro: finite_subset)
    then show ?thesis
      using that by (auto intro: * finite_imp_Sup_less)
  qed
  { fix s :: "'s \<times> ('c \<Rightarrow> real)" and cfg :: "('s \<times> ('c \<Rightarrow> real) set) cfg"
    assume unbounded: "\<forall> c \<in> \<X>. snd s c > k c" and "cfg \<in> R_G.cfg_on (abss s)" "abss s \<in> \<S>"
    then have "repcs s cfg \<in> valid_cfg"
      by (auto intro: R_G.valid_cfgI)
    then have cfg_on: "repcs s cfg \<in> MDP.cfg_on s"
      by (auto dest: MDP.valid_cfgD)
    from \<open>cfg \<in> _\<close> have "action cfg \<in> \<K> (abss s)"
      by (rule R_G.cfg_onD_action)
    have "rept s (action cfg) \<noteq> return_pmf s"
    proof (rule ccontr, simp)
      assume "rept s (action cfg) = return_pmf s"
      then have "action cfg = return_pmf (abss s)"
        using abst_rept_id[OF \<open>action cfg \<in> _\<close>]
        by (simp add: abst_def)
      moreover have "(fst s, snd s) \<in> S"
        using \<open>_ \<in> \<S>\<close> by (auto dest: \<S>_abss_S)
      moreover have "abss s = (fst s, [snd s]\<^sub>\<R>)"
        by (metis abss_S calculation(2) prod.collapse)
      ultimately show False
        using \<open>rept s _ = _\<close> unbounded unfolding rept_def by (cases s) (auto dest: cval_add_non_id)
    qed
    moreover have "rept s (action cfg) \<in> K s"
    proof -
      have "action (repcs s cfg) \<in> K s"
        using cfg_on by blast
      then show ?thesis
        by (simp add: repcs_def)
    qed
    ultimately have "rept s (action cfg) \<in> ?K s"
      by blast
    then have "measure_pmf (rept s (action cfg)) {s} \<le> ?r s"
      by (auto intro: Sup_upper)
    moreover have "rept s (action cfg) = action (repcs s cfg)"
      by (simp add: repcs_def)
    ultimately have "measure_pmf (action (repcs s cfg)) {s} \<le> ?r s"
      by auto
    note this \<open>rept s (action cfg) \<in> ?K s\<close>
  }
  note * = this
  let ?S = "{cfg. \<exists> cfg' s. cfg' \<in> R_G.valid_cfg \<and> cfg = repcs s cfg' \<and> abss s = state cfg'}"
  have start: "repcs st cfg \<in> ?S"
    using \<open>cfg \<in> R_G.valid_cfg\<close> assms unfolding R_G_cfg_on_div_def
    by clarsimp (inst_existentials cfg "fst st" "snd st", auto)
  have step: "y \<in> ?S" if "y \<in> K_cfg x" "x \<in> ?S" for x y
    using that apply safe
    subgoal for cfg' l u
      apply (inst_existentials "absc y" "state y")
      subgoal
        by blast
      subgoal
        by (metis
            K_cfg_valid_cfgD R_G.valid_cfgD R_G.valid_cfg_state_in_S absc_repcs_id cont_absc_1
            cont_repcs1 repcs_valid
            )
      subgoal
        by (simp add: state_absc)
      done
    done
  have **: "x \<in> ?S" if "(repcs st cfg, x) \<in> MDP.MC.acc" for x
  proof -
    from MDP.MC.acc_relfunD[OF that] obtain n where "((\<lambda> a b. b \<in> K_cfg a) ^^ n) (repcs st cfg) x" .
    then show ?thesis
    proof (induction n arbitrary: x) (* XXX Extract induction rule *)
      case 0
      with start show ?case
        by simp
    next
      case (Suc n)
      from this(2)[simplified] show ?case
        by (elim relcomppE step Suc.IH)
    qed
  qed
  have ***: "almost_everywhere (MDP.MC.T (repcs st cfg)) (alw (HLD ?S))"
    by (rule AE_mp[OF MDP.MC.AE_T_reachable]) (fastforce dest: ** simp: HLD_iff elim: alw_mono)

  have "(AE \<omega> in ?M. ?P \<omega>) \<longleftrightarrow>
    (AE \<omega> in ?M. \<forall> s :: ('s \<times> ('c \<Rightarrow> real)).
      (\<forall> c \<in> \<X>. snd s c > k c) \<and> s \<in> state ` (MDP.MC.acc `` {repcs st cfg}) \<longrightarrow>
      \<not> (ev (alw (\<lambda> xs. shd xs = s))) (smap state \<omega>))" (is "?L \<longleftrightarrow> ?R")
  proof
    assume ?L
    then show ?R
      by eventually_elim auto
  next
    assume ?R
    with MDP.MC.AE_T_reachable[of "repcs st cfg"] show ?L
    proof (eventually_elim, intro allI impI notI, goal_cases)
      case (1 \<omega> s)
      from this(1,2,5,6) show ?case
        by (intro alw_HLD_smap alw_disjoint_ccontr[where
              S = "state ` MDP.MC.acc `` {repcs st cfg}" and R = "{s}" and \<omega> = "smap state \<omega>"
              ]; simp add: HLD_iff; blast)
    qed
  qed

  also have "\<dots> \<longleftrightarrow>
      (\<forall> s :: ('s \<times> ('c \<Rightarrow> real)).
        (\<forall> c \<in> \<X>. snd s c > k c) \<and> s \<in> state ` (MDP.MC.acc `` {repcs st cfg}) \<longrightarrow>
        (AE \<omega> in ?M. \<not> (ev (alw (\<lambda> xs. shd xs = s))) (smap state \<omega>)))"
    using MDP.MC.countable_reachable[of "repcs st cfg"]
    by - (rule AE_all_imp_countable,
        auto intro: countable_subset[where B = "state ` MDP.MC.acc `` {repcs st cfg}"])
  also show ?thesis
    unfolding calculation
    apply clarsimp
    subgoal for l u x
      apply (rule MDP.non_loop_tail'[simplified, of "state x" ?S "?r (state x)"])
      subgoal
        apply safe
        subgoal premises prems for cfg cfg' l' u'
        proof -
          from prems have "state x = (l', u')"
            by (metis MDP.cfg_onD_state state_repcs)
          with \<open>_ = state x\<close> have [simp]: "l = l'" "u = u'"
            by auto
          show ?thesis
            unfolding \<open>state x = _\<close> using prems(1,3-) by (auto simp: R_G.valid_cfg_def intro: *)
        qed
        done
      subgoal
        apply (drule **)
        apply clarsimp
        apply (rule lt_1)
        apply (rule *)
        apply (auto dest: R_G.valid_cfg_state_in_S R_G.valid_cfgD)
        done
       apply (rule MDP.valid_cfgD[OF \<open>repcs st cfg \<in> valid_cfg\<close>]; fail)
      using *** unfolding alw_holds_pred_stream_iff[symmetric] HLD_def .
    done
qed

end (* PTA Regions *)


subsection \<open>Main Result\<close> text_raw \<open> \label{thm:minmax} \<close>

context Probabilistic_Timed_Automaton_Regions_Reachability
begin

lemma R_G_cfg_on_valid:
  "cfg \<in> R_G.valid_cfg" if "cfg \<in> R_G_cfg_on_div s'"
  using that unfolding R_G_cfg_on_div_def R_G.valid_cfg_def by auto

lemma cfg_on_valid:
  "cfg \<in> valid_cfg" if "cfg \<in> cfg_on_div s"
  using that unfolding cfg_on_div_def MDP.valid_cfg_def by auto

abbreviation "path_measure P cfg \<equiv> emeasure (MDP.T cfg) {x\<in>space MDP.St. P x}"
abbreviation "R_G_path_measure P cfg \<equiv> emeasure (R_G.T cfg) {x\<in>space R_G.St. P x}"
abbreviation "progressive st \<equiv> cfg_on_div st \<inter> {cfg. alternating cfg}"
abbreviation "R_G_progressive st \<equiv> R_G_cfg_on_div st \<inter> {cfg. alternating cfg}"

text \<open>Summary of our results on divergent configurations:\<close>
lemma absc_valid_cfg_eq:
  "absc ` progressive s = R_G_progressive s'"
  apply safe
  subgoal
    unfolding s'_def by (rule cfg_on_div_absc) auto
  subgoal
    by (simp add: AE_alw_ev_same_loc_iff cfg_on_valid)
  subgoal for cfg
    unfolding s'_def
    by (frule cfg_on_div_repcs_strong)
       (auto 4 4
          simp: s'_def R_G_cfg_on_div_def AE_alw_ev_same_loc_iff'[symmetric]
          intro: R_G_cfg_on_valid absc_repcs_id[symmetric]
       )
  done

text \<open>Main theorem:\<close>
theorem Min_Max_reachability:
  notes in_space_UNIV[measurable] and [iff] = pred_stream_iff
  shows
  "(\<Squnion>cfg\<in> progressive s.      path_measure     (\<lambda> x. (holds \<phi>  suntil holds \<psi>)  (s  ## x)) cfg)
 = (\<Squnion>cfg\<in> R_G_progressive s'. R_G_path_measure (\<lambda> x. (holds \<phi>' suntil holds \<psi>') (s' ## x)) cfg)
 \<and> (\<Sqinter>cfg\<in> progressive s.      path_measure     (\<lambda> x. (holds \<phi>  suntil holds \<psi>)  (s  ## x)) cfg)
 = (\<Sqinter>cfg\<in> R_G_progressive s'. R_G_path_measure (\<lambda> x. (holds \<phi>' suntil holds \<psi>') (s' ## x)) cfg)"
proof (rule SUP_eq_and_INF_eq; rule bexI[rotated]; erule IntE)
  fix cfg assume cfg_div: "cfg \<in> R_G_cfg_on_div s'" and "cfg \<in> Collect alternating"
  then have "alternating cfg"
    by auto
  let ?cfg' = "repcs s cfg"
  from \<open>alternating cfg\<close> cfg_div have "alternating ?cfg'"
    by (simp add: R_G_cfg_on_div_def s'_def AE_alw_ev_same_loc_iff'[of _ s])
  with cfg_div \<open>alternating cfg\<close> show "?cfg' \<in> cfg_on_div s \<inter> Collect alternating"
    by (auto intro: cfg_on_div_repcs_strong simp: s'_def)
  show "emeasure (R_G.T cfg)   {x \<in> space R_G.St. (holds \<phi>' suntil holds \<psi>') (s' ## x)}
      = emeasure (MDP.T ?cfg') {x \<in> space MDP.St. (holds \<phi> suntil holds \<psi>)   (s ## x)}"
     (is "?a = ?b")
  proof -
    from cfg_div have "cfg \<in> R_G.valid_cfg"
      by (rule R_G_cfg_on_valid)
    from cfg_div have "cfg \<in> R_G.cfg_on s'"
      unfolding R_G_cfg_on_div_def by auto
    then have "state cfg = s'"
      by auto
    have "?a = ?b"
      apply (rule
          path_measure_eq_repcs''_new[
            of s cfg \<phi> \<psi>, folded \<phi>'_def \<psi>'_def, unfolded \<open>_ = s'\<close> state_repcs
            ]
          )
      subgoal
        unfolding s'_def ..
      subgoal
        by fact
      subgoal
        using \<open>?cfg' \<in> cfg_on_div s \<inter> _\<close> by (blast intro: cfg_on_valid)
      subgoal premises prems for xs
        using prems s by (intro \<phi>_stream)
      subgoal premises prems
        using prems s by (intro \<psi>_stream)
      done
    then show ?thesis
      by simp
  qed
next
  fix cfg assume cfg_div: "cfg \<in> cfg_on_div s" and "cfg \<in> Collect alternating"
  with absc_valid_cfg_eq show "absc cfg \<in> R_G_cfg_on_div s' \<inter> Collect alternating"
    by auto
  show "emeasure (MDP.T cfg)        {x \<in> space MDP.St. (holds \<phi> suntil holds \<psi>)   (s ## x)}
      = emeasure (R_G.T (absc cfg)) {x \<in> space R_G.St. (holds \<phi>' suntil holds \<psi>') (s' ## x)}"
    (is "?a = ?b")
  proof -
    have "absc cfg \<in> R_G.valid_cfg"
      using R_G_cfg_on_valid \<open>absc cfg \<in> R_G_cfg_on_div s' \<inter> _\<close> by blast
    from cfg_div have "cfg \<in> valid_cfg"
      by (simp add: cfg_on_valid)
    with \<open>absc cfg \<in> R_G.valid_cfg\<close> have "?b = ?a"
      by (intro MDP.alw_S R_G.alw_S path_measure_eq_absc1_new
            [where P = "pred_stream (\<lambda>s. s \<in> \<S>)" and Q = "pred_stream (\<lambda>s. s \<in> S)"]
         )
         (auto simp: S_abss_\<S> intro: \<S>_abss_S intro!: suntil_abss suntil_reps, measurable)
    then show "?a = ?b"
      by simp
  qed
qed

end (* PTA Reachability Problem *)

end (* Theory *)
