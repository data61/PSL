theory Lib
  imports "Timed_Automata.Timed_Automata"
          "Timed_Automata.Approx_Beta"
          "MDP_Aux"
          "Finiteness"
          "Sequence_LTL"
          "Instantiate_Existentials"
          "Graphs"
begin

section \<open>Misc\<close>

lemma measurable_pred_stream[measurable]:
  fixes P shows "Measurable.pred (stream_space (count_space UNIV)) (pred_stream P)"
proof -
  have [measurable]: "Measurable.pred (count_space UNIV) P"
    by measurable
  then show ?thesis
    unfolding stream.pred_set sset_range by simp
qed

lemma pmf_map_pmf_cong:
  fixes f g and \<mu> :: "'a pmf"
  assumes "\<And> x. x \<in> \<mu> \<Longrightarrow> f x = y1 \<longleftrightarrow> g x = y2"
  shows "pmf (map_pmf f \<mu>) y1 = pmf (map_pmf g \<mu>) y2"
  unfolding pmf_map
  by (rule measure_pmf.finite_measure_eq_AE;
      simp add: AE_measure_pmf_iff assms split: split_indicator
     )

lemma collect_pair_finite[intro]:
  notes finite_subset[intro]
  assumes "finite {x. P x}" "finite {x. Q x}"
  shows "finite {(x, y) . P x \<and> Q y \<and> R x y}"
using assms
proof -
  from assms have "finite {(x, y) . P x \<and> Q y}" by auto
  moreover have "{(x, y) . P x \<and> (Q y \<and> R x y)} \<subseteq> {(x, y) . P x \<and> Q y}" by auto
  ultimately show ?thesis by blast
qed

lemma collect_pair_finite'[intro]:
  notes finite_subset[intro]
  assumes "finite {(x, y). P x y}"
  shows "finite {(x, y) . P x y \<and> R x y}"
using assms
proof -
  from assms have "finite {(x, y) . P x y}" by auto
  moreover have "{(x, y) . P x y \<and> R x y} \<subseteq> {(x, y) . P x y}" by auto
  ultimately show ?thesis by blast
qed

text \<open>This is what we actually need in this theory\<close>
lemma collect_pair_finite''[intro]:
  notes finite_subset[intro]
  assumes "finite {(x, y). P x \<and> Q y}"
  shows "finite {(x, y) . P x \<and> Q y \<and> R x y}"
using assms
proof -
  from assms have "finite {(x, y) . P x \<and> Q y}" by auto
  moreover have "{(x, y) . P x \<and> Q y \<and> R x y} \<subseteq> {(x, y) . P x \<and> Q y}" by auto
  ultimately show ?thesis by blast
qed

lemma finite_imageI'[intro]:
  assumes "finite {(x, y). P x y}"
  shows "finite {f x y | x y. P x y}"
proof -
  from assms have "finite ((\<lambda> (x, y). f x y) ` {(x, y). P x y})" by auto
  moreover have "((\<lambda> (x, y). f x y) ` {(x, y). P x y}) = {f x y | x y. P x y}" by auto
  ultimately show ?thesis by auto
qed

lemma finite_imageI''[intro]:
  assumes "finite (A \<times> B)"
  shows "finite {f x y | x y. x \<in> A \<and> y \<in> B \<and> R x y}"
proof -
  from assms have "finite {f x y | x y. x \<in> A \<and> y \<in> B}" by auto
  moreover have "{f x y | x y. x \<in> A \<and> y \<in> B \<and> R x y} \<subseteq> {f x y | x y. x \<in> A \<and> y \<in> B}" by auto
  ultimately show ?thesis by (blast intro: finite_subset)
qed

(* TODO: Move/should be somewhere already *)
lemma pred_stream_stl: "pred_stream \<phi> xs \<longrightarrow> pred_stream \<phi> (stl xs)"
  by (cases xs) auto

(* TODO: Should be somewhere already *)
lemma stream_all_pred_stream:
  "stream_all = pred_stream"
  by (intro ext) (simp add: stream.pred_set)

lemma pred_stream_iff: "pred_stream P s \<longleftrightarrow> Ball (sset s) P"
  using stream_all_iff[unfolded stream_all_pred_stream] .

(* TODO: Move *)
lemma measure_pmf_eq_1_iff:
  "emeasure (measure_pmf \<mu>) {x} = 1 \<longleftrightarrow> \<mu> = return_pmf x"
  using measure_pmf.prob_eq_1[of "{x}" \<mu>] set_pmf_subset_singleton[of \<mu> x]
  by (auto simp: measure_pmf.emeasure_eq_measure AE_measure_pmf_iff)

lemma HLD_mono:
  "HLD S \<omega>" if "HLD R \<omega>" "R \<subseteq> S"
  using that unfolding HLD_iff by auto

lemma alw_HLD_smap:
  "alw (HLD (f ` S)) (smap f \<omega>)" if "alw (HLD S) \<omega>"
  using that by (auto 4 3 elim: HLD_mono alw_mono)

lemma alw_disjoint_ccontr:
  assumes "alw (HLD S) \<omega>" "ev (alw (HLD R)) \<omega>" "R \<inter> S = {}"
  shows False
proof -
  from assms(1,2) obtain \<omega> where "alw (HLD S) \<omega>" "alw (HLD R) \<omega>"
    by (auto intro: alw_sdrop sdrop_wait)
  with \<open>R \<inter> S = {}\<close> show False
    by (auto 4 3 simp: HLD_iff dest: alwD)
qed

(* TODO: Move *)
lemma stream_all2_refl: "stream_all2 P x x = pred_stream (\<lambda> x. P x x) x"
  by (simp add: stream.pred_rel eq_onp_def) (standard; coinduction arbitrary: x; auto)

lemma AE_all_imp_countable:
  assumes "countable {x. Q x}"
  shows "(AE x in M. \<forall>y. Q y \<longrightarrow> P x y) = (\<forall>y. Q y \<longrightarrow> (AE x in M. P x y))"
  using assms by (auto dest: AE_ball_countable)

lemma AE_conj:
  "almost_everywhere M P = almost_everywhere M (\<lambda> x. P x \<and> Q x)" if "almost_everywhere M Q"
  by (auto intro: AE_mp[OF that])

(* TODO: move *)
lemma list_hd_lastD:
  assumes "length xs > 1"
  obtains x y ys where "xs = x # ys @ [y]"
  using assms by atomize_elim (cases xs; simp; metis rev_exhaust)

(* TODO: Move *)
lemma SUP_eq_and_INF_eq:
  assumes "\<And>i. i \<in> A \<Longrightarrow> \<exists>j\<in>B. f i = g j"
      and "\<And>j. j \<in> B \<Longrightarrow> \<exists>i\<in>A. g j = f i"
    shows "\<Squnion>((f :: _ \<Rightarrow> _ :: complete_lattice) ` A) = \<Squnion>(g ` B) \<and> \<Sqinter>(f ` A) = \<Sqinter>(g ` B)"
  by (auto 4 3 intro!: INF_eq SUP_eq dest: assms)

(* TODO: Move *)
lemma measurable_alw_stream[measurable]:
  fixes P assumes [measurable]: "Measurable.pred (stream_space (count_space UNIV)) P"
  shows "Measurable.pred (stream_space (count_space UNIV)) (alw P)"
  unfolding alw_iff_sdrop by measurable

(* TODO: Move *)
lemma ev_neq_start_implies_ev_neq:
  assumes "ev (Not o HLD {y}) (y ## xs)"
  shows "ev (\<lambda> xs. shd xs \<noteq> shd (stl xs)) (y ## xs)"
  using assms
  apply (induction "y ## xs" arbitrary: xs rule: ev.induct)
   apply (simp; fail)
  subgoal for xs
    apply (cases "shd xs = y")
    subgoal
      apply safe
      apply (rule ev.step)
      apply simp
      using stream.collapse[of xs, symmetric]
      by blast
    subgoal
      by auto
    done
  done

(* TODO: Move *)
lemma ev_sdropD:
  assumes "ev P xs"
  obtains i where "P (sdrop i xs)"
  using assms
  apply atomize_elim
  apply (induction rule: ev.induct)
   apply (inst_existentials "0 :: nat"; simp; fail)
  apply (erule exE)
  subgoal for xs i
    by (inst_existentials "i + 1") simp
  done

(* TODO: Move *)
lemma pred_stream_sconst:
  "pred_stream ((=) x) (sconst x)"
  by coinduction simp

(* TODO: Move *)
lemma alw_Stream: "alw P (x ## s) \<longleftrightarrow> P (x ## s) \<and> alw P s"
  by (subst alw.simps) simp

(* TODO: Move *)
lemma alw_True: "alw (\<lambda>x. True) \<omega>"
  by (auto intro: all_imp_alw)

(* TODO: Move *)
lemma alw_conjI:
  "alw (P aand Q) xs" if "alw P xs" "alw Q xs"
  using that by (simp add: alw_aand)

(* TODO: Move *)
lemma alw_ev_cong:
  "alw (ev S) xs = alw (ev R) xs" if "alw P xs" "\<And> x. P x \<Longrightarrow> S x \<longleftrightarrow> R x"
  by (rule alw_cong[where P = "alw P"]) (auto simp: HLD_iff that elim!: ev_cong)

lemma alw_ev_HLD_cong:
  "alw (ev (HLD S)) xs = alw (ev (HLD R)) xs" if "alw (HLD P) xs" "\<And> x. x \<in> P \<Longrightarrow> x \<in> S \<longleftrightarrow> x \<in> R"
  by (rule alw_ev_cong, rule that; simp add: HLD_iff that)

(* TODO: Move *)
lemma measurable_eq_stream_space[measurable (raw)]:
  assumes [measurable]: "f \<in> M \<rightarrow>\<^sub>M stream_space (count_space UNIV)"
  shows "Measurable.pred M (\<lambda>x. f x = c)"
proof -
  have *: "(\<lambda>x. f x = c) = (\<lambda>x. \<forall>i. f x !! i = c !! i)"
    by (auto intro: eqI_snth simp: fun_eq_iff)
  show ?thesis
    unfolding * by measurable
qed

(* TODO: rename, and change to LTL constants i.e. HLD, aand, nxt etc. *)
lemma prop_nth_sdrop:
  assumes "\<forall> i\<ge>j. P (\<omega> !! i)"
  shows "\<forall> i. P (sdrop j \<omega> !! i)"
using assms by (induction j arbitrary: \<omega>) fastforce+

lemma prop_nth_sdrop_pair:
  assumes "\<forall> i. P (\<omega> !! i) (\<omega>' !! i)"
  shows "\<forall> i. P (sdrop j \<omega> !! i) (sdrop j \<omega>' !! i)"
  using assms by (induction j arbitrary: \<omega> \<omega>') (auto, metis snth.simps(2))

lemma prop_nth_stl:
  "\<forall> i. P (xs !! i) \<Longrightarrow> \<forall> i. P (stl xs !! i)"
  by (metis snth.simps(2))

context Graph_Defs
begin

lemma steps_SCons_iff:
  "steps (x # y # xs) \<longleftrightarrow> E x y \<and> steps (y # xs)"
  by (auto elim: steps.cases)

lemma steps_Single_True:
  "steps [x] = True"
  by auto

lemma add_step_iff:
  "(\<forall> xs y. steps (x # xs @ [y]) \<and> length xs = Suc n \<longrightarrow> P xs y)
  \<longleftrightarrow> (\<forall> z xs y. steps (x # z # xs @ [y]) \<and> length xs = n \<longrightarrow> P (z # xs) y)"
  apply safe
   apply fastforce
  subgoal for xs y
    by (cases xs) auto
  done

lemma compower_stepsD:
  assumes "(E ^^ n) s s'"
  obtains xs where "steps xs" "hd xs = s" "last xs = s'" "length xs = n + 1"
  using assms
  apply atomize_elim
proof (induction n arbitrary: s')
  case 0
  then show ?case
    by auto
next
  case (Suc n)
  from Suc.prems show ?case
    by (auto 4 4 intro: steps_append_single dest: Suc.IH)
qed

lemma compower_stepsD':
  assumes "(E ^^ n) s s'" "n > 0"
  obtains xs where "steps (s # xs @ [s'])" "length xs + 1 = n"
  apply (rule compower_stepsD[OF assms(1)])
  subgoal for xs
    by (auto simp: \<open>n > 0\<close> intro: list_hd_lastD[of xs])
  done

end

context MC_syntax
begin

theorem AE_T_iff_n:
  fixes P :: "'s stream \<Rightarrow> bool" 
    and x :: "'s" 
  assumes "Measurable.pred (stream_space (count_space UNIV)) P" "n > 0"
  shows "almost_everywhere (T x) P =
    (\<forall>xs y. Graph_Defs.steps (\<lambda> a b. b \<in> K a) (x # xs @ [y]) \<and> length xs + 1 = n
      \<longrightarrow> (AE \<omega> in T y. P (xs @- y ## \<omega>)))"
  using assms
  apply (induction n arbitrary: x P)
   apply (simp; fail)
  subgoal for n x P
    apply (cases n)
    subgoal
      by (subst AE_T_iff) (auto simp: Graph_Defs.steps_SCons_iff Graph_Defs.steps_Single_True)
    subgoal premises prems for n'
    proof -
      have *: "Measurable.pred (stream_space (count_space UNIV)) (\<lambda> \<omega>. P (y ## \<omega>))" for y
        using prems(2) by measurable
      with prems(1)[OF *] prems(3-) show ?thesis
        by (auto simp: AE_T_iff[OF prems(2)] Graph_Defs.steps_SCons_iff Graph_Defs.add_step_iff)
    qed
    done
  done

lemma AE_alw_accD:
  fixes P assumes P: "Measurable.pred (stream_space (count_space UNIV)) P"
  assumes *: "almost_everywhere (T s) (alw P)" "(s, s') \<in> acc"
  shows "almost_everywhere (T s') (alw P)"
  using *(2,1)
proof induction
  case (step y z)
  then have "almost_everywhere (T y) (alw P)" "z \<in> K y" by auto
  then have "AE \<omega> in T z. alw P (z ## \<omega>)"
    unfolding AE_T_iff[OF measurable_alw_stream[OF P], of y] by auto
  then show ?case
    by eventually_elim auto
qed 

lemma acc_relfunD:
  assumes "(s, s') \<in> acc"
  obtains n where "((\<lambda> a b. b \<in> K a) ^^ n) s s'"
  using assms
  apply atomize_elim
  apply (drule rtrancl_imp_relpow)
  apply (erule exE)
  subgoal for n
    by (inst_existentials n) (induction n arbitrary: s'; auto)
  done

(* TODO: If we can show measurable_alw_stream, then this subsumed by the lemma above *)
lemma AE_all_accD:
  assumes "almost_everywhere (T s) (pred_stream P)" "(s, s') \<in> acc"
  shows "almost_everywhere (T s') (pred_stream P)"
proof -
  from acc_relfunD[OF \<open>_ \<in> acc\<close>] obtain n where *: "((\<lambda> a b. b \<in> K a) ^^ n) s s'" .
  show ?thesis
  proof (cases "n = 0")
    case True
    with * assms(1) show ?thesis
      by auto
  next
    case False
    then have "n > 0"
      by simp
    with * obtain xs where
      "Graph_Defs.steps (\<lambda>a b. b \<in> set_pmf (K a)) (s # xs @ [s'])" "Suc (length xs) = n"
      by (auto elim: Graph_Defs.compower_stepsD')
    with assms(1)[unfolded AE_T_iff_n[OF measurable_pred_stream \<open>n > 0\<close>, of P s]] show ?thesis
      by auto
  qed
qed

lemma AE_T_ev_HLD_infinite_strong':
  assumes "0 \<le> r" "r < 1"
    and r: "\<And>x. x \<in> X \<inter> Y \<Longrightarrow> measure_pmf.prob (K x) Y \<le> r"
    and ae: "AE \<omega> in T x. alw (\<lambda> \<omega>. HLD Y \<omega> \<longrightarrow> ev (HLD X) \<omega>) \<omega>"
  shows "AE \<omega> in T x. ev (HLD (- Y)) \<omega>"
proof -
  define run where "run F = (HLD (Y - X)) suntil ((X \<inter> Y) \<cdot> Y \<cdot> F)" for F

  have le_gfp: "alw (HLD Y) aand alw (\<lambda> \<omega>. HLD Y \<omega> \<longrightarrow> ev (HLD X) \<omega>) \<le> gfp run"
  proof (rule gfp_upperbound; clarsimp)
    fix \<omega> assume "alw (HLD Y) \<omega>" "alw (\<lambda>\<omega>. HLD Y \<omega> \<longrightarrow> ev (HLD X) \<omega>) \<omega>"
    then have "ev (HLD X) \<omega>" "alw (HLD Y) \<omega>" "alw (\<lambda>\<omega>. HLD Y \<omega> \<longrightarrow> ev (HLD X) \<omega>) \<omega>"
      by auto
    then show "run (\<lambda>xs. alw (HLD Y) xs \<and> alw (\<lambda>\<omega>. HLD Y \<omega> \<longrightarrow> ev (HLD X) \<omega>) xs) \<omega>"
    proof (induction \<omega> rule: ev_induct_strong)
      case (base \<omega>) then show ?case by (cases \<omega>) (auto intro!: suntil.base simp: alw_Stream run_def)
    next
      case (step \<omega>)
      show ?case
        unfolding run_def
        using \<open>\<not> HLD X \<omega>\<close> \<open>alw (HLD Y) \<omega>\<close> step(3)[unfolded run_def] step(4,5)
        by (auto 0 4 simp: HLD_def intro: suntil.step)
    qed
  qed

  have cont_run: "inf_continuous run"
    apply (auto simp: inf_continuous_def fun_eq_iff run_def)
    subgoal premises that for M x f
      by (rule suntil_mono[OF _ _ that(2) alw_True]) auto
    subgoal premises that for M x
      using that(2)[THEN spec, of 0] that(2)
      proof (induction rule: suntil_induct_strong)
        case (base \<omega>) then show ?case 
          by (cases \<omega>) (simp add: suntil_Stream)
      next
        case (step \<omega>) then show ?case
          by (cases \<omega>) (simp add: suntil_Stream)
      qed
      done
  have [measurable]: "Measurable.pred (stream_space (count_space UNIV)) (gfp run)"
    apply measurable
    apply (rule measurable_gfp[OF cont_run])
    apply (auto simp: run_def)
    done

  have "emeasure (T x) {\<omega> \<in> space (T x). alw (HLD Y) \<omega>} \<le>
    emeasure (T x) {\<omega> \<in> space (T x). ((alw (HLD Y)) aand (alw (\<lambda> \<omega>. HLD Y \<omega> \<longrightarrow> ev (HLD X) \<omega>))) \<omega>}"
    apply (rule emeasure_mono_AE)
    subgoal using ae by eventually_elim auto
    by measurable
  also have "\<dots> \<le> emeasure (T x) {\<omega> \<in> space (T x). gfp run \<omega>}"
    apply (rule emeasure_mono)
    subgoal using le_gfp by auto
    by measurable
  also have "\<dots> \<le> r ^ n" for n
  proof (induction n arbitrary: x)
    case 0 then show ?case by (simp add: T.emeasure_le_1)
  next
    case (Suc n)
    { fix x 
      have "(\<integral>\<^sup>+ t. \<integral>\<^sup>+ t'. emeasure (T t') {x\<in>space S. t\<in>X \<and> t\<in>Y \<and> t'\<in>Y \<and> gfp run x} \<partial>K t \<partial>K x) \<le>
        (\<integral>\<^sup>+ t. indicator (X \<inter> Y) t * \<integral>\<^sup>+ t'. indicator Y t' * ennreal (r ^ n) \<partial>K t \<partial>K x)"
        using Suc by (auto intro!: nn_integral_mono split: split_indicator)
      also have "\<dots> \<le> (\<integral>\<^sup>+ t. indicator (X \<inter> Y) t * r \<partial>K x) * ennreal (r^n)"
        by (auto intro!: nn_integral_mono mult_right_mono r ennreal_leI split: split_indicator
                 simp: nn_integral_multc mult.assoc[symmetric] measure_pmf.emeasure_eq_measure)
      also have "\<dots> = emeasure (K x) (X \<inter> Y) * r^(Suc n)"
        by (simp add: ennreal_mult \<open>0 \<le> r\<close> nn_integral_multc ennreal_indicator mult.assoc)
      finally have *: "(\<integral>\<^sup>+ t. \<integral>\<^sup>+ t'. emeasure (T t') {x\<in>space S. t \<in> X \<and> t \<in> Y \<and> t' \<in> Y \<and> gfp run x} \<partial>K t \<partial>K x) \<le>
        emeasure (K x) (X \<inter> Y) * r^Suc n" .
  
      have "(\<integral>\<^sup>+ t. \<integral>\<^sup>+ t'. emeasure (T t') {x \<in> space S. t \<in> X \<and> t \<in> Y \<and> t' \<in> Y \<and> gfp run x} \<partial>K t \<partial>K x) +
           ennreal (r^Suc n) * emeasure (measure_pmf (K x)) (Y - X) \<le>
        emeasure (K x) (X \<inter> Y) * ennreal (r^Suc n) + ennreal (r^Suc n) * emeasure (measure_pmf (K x)) (Y - X)"
        by (intro add_mono_left *)
      also have "\<dots> = emeasure (K x) ((X \<inter> Y) \<union> (Y - X)) * ennreal (r^Suc n)"
        by (subst plus_emeasure[symmetric]) (auto simp: field_simps)
      also have "\<dots> \<le> 1 * ennreal (r^Suc n)"
        by (intro mult_right_mono measure_pmf.emeasure_le_1) simp
      finally have "(\<integral>\<^sup>+ t. \<integral>\<^sup>+ t'. emeasure (T t') {x \<in> space MC_syntax.S. t \<in> X \<and> t \<in> Y \<and> t' \<in> Y \<and> gfp run x} \<partial>K t \<partial>K x) +
           ennreal (r^Suc n) * emeasure (measure_pmf (K x)) (Y - X) \<le> 1 * ennreal (r^Suc n)" by simp }
    note * = this
    
    show ?case
      apply (subst gfp_unfold[OF inf_continuous_mono[OF cont_run]])
      apply (subst run_def)
      apply (subst emeasure_suntil_disj)
        apply measurable []
      subgoal for s
        by (rule AE_I2) (auto simp: HLD_iff)
      apply (rule le_funD[of _ _ x])
      apply (rule lfp_lowerbound)
      apply (rule le_funI)
      apply (subst emeasure_Collect_T)
       apply measurable []
      apply (subst emeasure_Collect_T)
      apply simp
      apply (simp add: nn_integral_cmult)
      using * by simp
  qed
  finally have "emeasure (T x) {\<omega> \<in> space (T x). alw (HLD Y) \<omega>} \<le> r^n" for n .
  then have "emeasure (T x) {\<omega> \<in> space (T x). alw (HLD Y) \<omega>} \<le> ennreal 0"
    using \<open>0 \<le> r\<close> \<open>r < 1\<close>
    by (intro LIMSEQ_le_const[OF tendsto_ennrealI[OF LIMSEQ_power_zero[of r]]]) auto
  then have *: "emeasure (T x) {\<omega> \<in> space (T x). alw (HLD Y) \<omega>} = 0"
    by simp
  show ?thesis
    by (rule AE_I[OF _ *]) (auto simp: not_ev_iff not_HLD[symmetric])
qed

end

context Markov_Decision_Process
begin

lemma cfg_on_inv:
  "pred_stream (\<lambda> cfg. cfg \<in> cfg_on (state cfg)) \<omega>" if
  "MC.enabled cfg \<omega>" "cfg \<in> cfg_on s"
  using that proof (coinduction arbitrary: \<omega> cfg s)
  case prems: stream_pred
  note [simp] = \<open>_ = \<omega>\<close>[symmetric]
  from prems(2) have "a \<in> set_pmf (K_cfg cfg)" "MC.enabled a w"
    by (auto simp: MC.enabled_Stream)
  moreover from \<open>a \<in> _\<close> have "a \<in> cont cfg ` set_pmf (action cfg)"
    by (simp add: set_K_cfg)
  ultimately show ?case
    using \<open>cfg \<in> _\<close> by auto
qed

lemma MC_T_not_sconst_strong:
  assumes
    "\<forall> l. \<forall> cfg \<in> (\<Union> x \<in> f -` {u}. cfg_on x) \<inter> Y \<inter> X. measure_pmf (action cfg) (f -` {u}) \<le> r"
    "r < 1" "cfg \<in> cfg_on x"
    "AE \<omega> in MC.T cfg. pred_stream (\<lambda> x. x \<in> X) \<omega>"
    "AE \<omega> in MC.T cfg. alw (\<lambda> \<omega>. HLD (f -` {u}) (smap state \<omega>) \<longrightarrow> ev (HLD Y) \<omega>) \<omega>"
  shows "AE \<omega> in MC.T cfg. smap (f o state) \<omega> \<noteq> sconst u"
proof -
  let ?U = "f -` {u}"
  let ?S = "(\<Union> x \<in> f -` {u}. cfg_on x) \<inter> X"
  let ?T = "Y \<inter> ((\<Union> x \<in> f -` {u}. cfg_on x) \<inter> X)"
  have *: "emeasure (K_cfg cfg) ?S \<le> r" if "cfg \<in> ?T" for cfg
  proof -
    have "emeasure (K_cfg cfg) ?S \<le> emeasure (measure_pmf (action cfg)) ?U"
      unfolding K_cfg_def by (auto dest: cfg_onD_state intro!: emeasure_mono)
    also from assms(1) \<open>cfg \<in> ?T\<close> have "\<dots> \<le> r"
      by auto
    finally show ?thesis .
  qed
  have "AE \<omega> in MC.T cfg. ev (HLD (- ?S)) \<omega>"
    apply (rule MC.AE_T_ev_HLD_infinite_strong'[where r = "enn2real r" and ?X = Y])
    apply (simp; fail)
    subgoal
      using \<open>r < 1\<close>
      by (metis ennreal_enn2real_if ennreal_less_one_iff zero_less_one)
    subgoal for x
     by (drule *)
        (metis Sigma_Algebra.measure_def assms(2) enn2real_mono ennreal_one_less_top less_trans)
    subgoal
      using assms(5)
      by (rule AE_mp) (rule AE_I2, intro impI, auto simp: HLD_iff elim: alw_mono)
    done
  then show ?thesis
    apply (rule AE_mp)
  proof (rule AE_mp[OF assms(4)], rule AE_mp[OF MC.AE_T_enabled], rule AE_I2, safe)
    fix \<omega> assume
      "\<omega> \<in> space (MC.T cfg)" "pred_stream (\<lambda>\<omega>. \<omega> \<in> X) \<omega>"
      "MC.enabled cfg \<omega>" "ev (HLD (- ?S)) \<omega>" "smap (f \<circ> state) \<omega> = sconst u"
    from this(2,3) \<open>cfg \<in> _\<close>
    have "pred_stream (\<lambda> x. x \<in> cfg_on (state x)) \<omega>"
      by (auto dest: cfg_onD_state intro!: cfg_on_inv)
    from \<open>smap _ \<omega> = _\<close> have "pred_stream (\<lambda> y. y \<in> (\<Union> x \<in> ?U. cfg_on x)) \<omega>"
    proof -
      have "(f o state) cfg = u" if "cfg \<in> sset \<omega>" for cfg
        using stream.set_map[of "f o state" \<omega>] that \<open>smap _ \<omega> = _\<close> by fastforce
      with \<open>pred_stream (\<lambda> x. x \<in> cfg_on (state x)) \<omega>\<close> show ?thesis
        by (auto elim!: stream.pred_mono_strong)
    qed
    with \<open>pred_stream (\<lambda>\<omega>. \<omega> \<in> X) \<omega>\<close> have "pred_stream (\<lambda> x. x \<in> ?S) \<omega>"
      by (coinduction arbitrary: \<omega>) auto
    then have "alw (HLD ?S) \<omega>"
      by (simp add: alw_holds_pred_stream_iff HLD_def)
    with \<open>ev (HLD (- ?S)) \<omega>\<close> show False
      unfolding not_ev_not[symmetric] not_HLD by simp
  qed
qed

lemma MC_T_not_sconst:
  assumes
    "\<forall> l. \<forall> cfg \<in> (\<Union> x \<in> f -` {u}. cfg_on x) \<inter> X. measure_pmf (action cfg) (f -` {u}) \<le> r"
    "r < 1" "cfg \<in> cfg_on x"
    "AE \<omega> in MC.T cfg. pred_stream (\<lambda> x. x \<in> X) \<omega>"
  shows "AE \<omega> in MC.T cfg. smap (f o state) \<omega> \<noteq> sconst u"
proof -
  let ?U = "f -` {u}"
  let ?S = "(\<Union> x \<in> f -` {u}. cfg_on x) \<inter> X"
  have *: "emeasure (K_cfg cfg) ?S \<le> r" if "cfg \<in> ?S" for cfg
  proof -
    have "emeasure (K_cfg cfg) ?S \<le> emeasure (measure_pmf (action cfg)) ?U"
      unfolding K_cfg_def by (auto dest: cfg_onD_state intro!: emeasure_mono)
    also from assms(1) \<open>cfg \<in> ?S\<close> have "\<dots> \<le> r"
      by auto
    finally show ?thesis .
  qed
  have "AE \<omega> in MC.T cfg. ev (HLD (- ?S)) \<omega>"
    apply (rule MC.AE_T_ev_HLD_infinite[where r = "enn2real r"])
    subgoal
      using \<open>r < 1\<close>
      by (metis ennreal_enn2real_if ennreal_less_one_iff zero_less_one)
    apply (drule *)
    by (metis Sigma_Algebra.measure_def assms(2) enn2real_mono ennreal_one_less_top less_trans)
  then show ?thesis
    apply (rule AE_mp)
  proof (rule AE_mp[OF assms(4)], rule AE_mp[OF MC.AE_T_enabled], rule AE_I2, safe)
    fix \<omega> assume
      "\<omega> \<in> space (MC.T cfg)" "pred_stream (\<lambda>\<omega>. \<omega> \<in> X) \<omega>"
      "MC.enabled cfg \<omega>" "ev (HLD (- ?S)) \<omega>" "smap (f \<circ> state) \<omega> = sconst u"
    from this(2,3) \<open>cfg \<in> _\<close>
    have "pred_stream (\<lambda> x. x \<in> cfg_on (state x)) \<omega>"
      by (auto dest: cfg_onD_state intro!: cfg_on_inv)
    from \<open>smap _ \<omega> = _\<close> have "pred_stream (\<lambda> y. y \<in> (\<Union> x \<in> ?U. cfg_on x)) \<omega>"
    proof -
      have "(f o state) cfg = u" if "cfg \<in> sset \<omega>" for cfg
        using stream.set_map[of "f o state" \<omega>] that \<open>smap _ \<omega> = _\<close> by fastforce
      with \<open>pred_stream (\<lambda> x. x \<in> cfg_on (state x)) \<omega>\<close> show ?thesis
        by (auto elim!: stream.pred_mono_strong)
    qed
    with \<open>pred_stream (\<lambda>\<omega>. \<omega> \<in> X) \<omega>\<close> have "pred_stream (\<lambda> x. x \<in> ?S) \<omega>"
      by (coinduction arbitrary: \<omega>) auto
    then have "alw (HLD ?S) \<omega>"
      by (simp add: alw_holds_pred_stream_iff HLD_def)
    with \<open>ev (HLD (- ?S)) \<omega>\<close> show False
      unfolding not_ev_not[symmetric] not_HLD by simp
  qed
qed

lemma MC_T_not_sconst':
  assumes
    "\<forall> cfg \<in> cfg_on x \<inter> X. measure_pmf (action cfg) {x} \<le> r" "r < 1" "cfg \<in> cfg_on x'"
    "AE \<omega> in MC.T cfg. pred_stream (\<lambda> x. x \<in> X) \<omega>"
  shows "AE \<omega> in MC.T cfg. smap state \<omega> \<noteq> sconst x"
  using assms by (rule MC_T_not_sconst[where f = id, simplified])

lemma K_cfg_cfg_onI:
  "cfg' \<in> cfg_on (state cfg')" if "cfg \<in> cfg_on x" "cfg' \<in> K_cfg cfg"
  using that by (force simp: set_K_cfg)

lemma MC_acc_cfg_onI:
  "cfg' \<in> cfg_on (state cfg')" if "(cfg, cfg') \<in> MC.acc" "cfg \<in> cfg_on x"
proof -
  from that(1) obtain n where "((\<lambda> a b. b \<in> K_cfg a) ^^ n) cfg cfg'"
    by (erule MC.acc_relfunD)
  with \<open>cfg \<in> cfg_on x\<close> show ?thesis
    by (induction n arbitrary: cfg') (auto intro: K_cfg_cfg_onI)
qed

lemma non_loop_tail_strong:
  assumes
    "\<forall> l. \<forall> cfg \<in> (\<Union> x \<in> f -` {u}. cfg_on x) \<inter> Y \<inter> X. measure_pmf (action cfg) (f -` {u}) \<le> r"
    "r < 1" "cfg \<in> cfg_on x"
    "AE \<omega> in MC.T cfg. pred_stream (\<lambda> x. x \<in> X) \<omega>"
    "AE \<omega> in MC.T cfg. alw (\<lambda> \<omega>. HLD (f -` {u}) (smap state \<omega>) \<longrightarrow> ev (HLD Y) \<omega>) \<omega>"
  shows "AE \<omega> in MC.T cfg. \<not> (ev (alw (\<lambda> xs. shd xs = u))) (smap (f o state) \<omega>)"
    (is "AE \<omega> in ?M. ?P \<omega>")
proof -
  have *: "?P \<omega> \<longleftrightarrow> alw (\<lambda> xs. smap (f o state) xs \<noteq> sconst u) \<omega>" for \<omega>
    apply (simp add: not_ev_iff)
    apply (rule arg_cong2[where f = alw])
     apply (rule ext)
    subgoal for xs
      using MC.alw_HLD_iff_sconst[of u "smap (f o state) xs"] by (simp add: HLD_iff)
    by (rule HOL.refl)
  have "AE \<omega> in ?M. alw (\<lambda> xs. smap (f o state) xs \<noteq> sconst u) \<omega>"
    apply (rule MC.AE_T_alw)
    subgoal by (intro pred_intros_logic measurable_eq_stream_space) measurable
    using assms
    by - (erule MC_T_not_sconst_strong,
        auto intro: MC.AE_all_accD MC.AE_alw_accD elim: MC_acc_cfg_onI
        )
  with * show ?thesis
    by simp
qed

lemma non_loop_tail:
  assumes
    "\<forall> l. \<forall> cfg \<in> (\<Union> x \<in> f -` {u}. cfg_on x) \<inter> X. measure_pmf (action cfg) (f -` {u}) \<le> r"
    "r < 1" "cfg \<in> cfg_on x"
    "AE \<omega> in MC.T cfg. pred_stream (\<lambda> x. x \<in> X) \<omega>"
  shows "AE \<omega> in MC.T cfg. \<not> (ev (alw (\<lambda> xs. shd xs = u))) (smap (f o state) \<omega>)"
    (is "AE \<omega> in ?M. ?P \<omega>")
proof -
  have *: "?P \<omega> \<longleftrightarrow> alw (\<lambda> xs. smap (f o state) xs \<noteq> sconst u) \<omega>" for \<omega>
    apply (simp add: not_ev_iff)
    apply (rule arg_cong2[where f = alw])
     apply (rule ext)
    subgoal for xs
      using MC.alw_HLD_iff_sconst[of u "smap (f o state) xs"] by (simp add: HLD_iff)
    by (rule HOL.refl)
  have "AE \<omega> in ?M. alw (\<lambda> xs. smap (f o state) xs \<noteq> sconst u) \<omega>"
    apply (rule MC.AE_T_alw)
    subgoal by (intro pred_intros_logic measurable_eq_stream_space) measurable
    using assms by - (erule MC_T_not_sconst, auto intro: MC.AE_all_accD elim: MC_acc_cfg_onI)
  with * show ?thesis
    by simp
qed

lemma non_loop_tail':
  assumes
    "\<forall> cfg \<in> cfg_on x \<inter> X. measure_pmf (action cfg) {x} \<le> r" "r < 1"
    "cfg \<in> cfg_on y"
    "AE \<omega> in MC.T cfg. pred_stream (\<lambda> x. x \<in> X) \<omega>"
  shows "AE \<omega> in MC.T cfg. \<not> (ev (alw (\<lambda> xs. shd xs = x))) (smap state \<omega>)"
  using assms by simp (erule non_loop_tail[where f = id, simplified])

end

lemma (in Regions) intv_const_mono:
  assumes "u \<in> region X I r" "c1 \<in> X" "c2 \<in> X" "u c1 \<le> u c2" "\<not> isGreater (I c2)"
  shows "intv_const (I c1) \<le> intv_const (I c2)"
proof -
  from assms have "intv_elem c1 u (I c1)" "intv_elem c2 u (I c2)" by auto
  with \<open>u c1 \<le> u c2\<close> \<open>\<not> _\<close> show ?thesis by (cases "I c1"; cases "I c2"; auto)
qed

lemma sset_sdrop:
  assumes "x \<in> sset (sdrop i xs)"
  shows "x \<in> sset xs"
using assms by (auto simp: sset_range)

lemma holds_untilD:
  assumes "(holds P until holds Q) xs" "\<forall> i \<le> j. \<not> Q (xs !! i)"
  shows "P (xs !! j)"
using assms
proof (induction j arbitrary: xs)
  case 0
  then show ?case by cases auto
next
  case (Suc j)
  from Suc.prems show ?case by cases (auto dest!: Suc.IH)
qed

(* TODO: Move *)
lemma frac_le_self:
  assumes "x \<ge> 0"
  shows "frac x \<le> x"
using assms by (metis dual_order.trans frac_eq frac_lt_1 le_less not_le)

lemma frac_le_1I:
  assumes "0 \<le> x" "x \<le> 1" "x \<le> y"
  shows "frac x \<le> y"
using assms by (metis dual_order.trans frac_eq frac_of_int le_less of_int_simps(2))

lemma frac_le_1I':
  assumes "0 \<le> x" "x \<le> y" "y < 1"
  shows "frac x \<le> frac y"
proof -
  from assms have "frac y = y" by (simp add: frac_eq)
  moreover from assms have "frac x \<le> y" by (auto intro: frac_le_1I)
  ultimately show ?thesis by simp
qed

(* XXX Move *)
lemmas [intro] = order.strict_implies_order[OF frac_lt_1]

lemma nat_eventually_critical:
  assumes "P i" "\<not> P j" "i < j"
  shows "\<exists> k \<ge> i. P k \<and> \<not> P (Suc k)"
using assms by (metis dec_induct less_le)

lemma nat_eventually_critical_path:
  fixes i :: nat
  assumes "P i" "\<not> P j" "i < j"
  shows "\<exists> k > i. k \<le> j \<and> \<not> P k \<and> (\<forall> m \<ge> i. m < k \<longrightarrow> P m)"
proof -
  let ?S = "{k. i < k \<and> k \<le> j \<and> \<not> P k}"
  let ?k = "Min ?S"
  from assms have "j \<in> ?S" by auto
  moreover have "finite ?S" by auto
  ultimately have "i < ?k" "?k \<le> j" "\<not> P ?k" using Min_in[of ?S] by blast+
  moreover have "P m" if "i \<le> m" "m < ?k" for m
  proof (cases "i = m")
    case True with \<open>P i\<close> show ?thesis by simp
  next
    case False
    with \<open>i \<le> m\<close> have "i < m" by simp
    with Min_le[OF \<open>finite _\<close>] \<open>m < ?k\<close> \<open>?k \<le> j\<close> show ?thesis by fastforce
  qed
  ultimately show ?thesis using \<open>P i\<close> by - (rule exI[where x = ?k]; blast)
qed

subsection \<open>MDP Invariant\<close>

locale Markov_Decision_Process_Invariant =
  Markov_Decision_Process K for K :: "'s \<Rightarrow> 's pmf set"+
fixes S :: "'s set"
assumes invariant: "\<And> s D. s \<in> S \<Longrightarrow> D \<in> K s \<Longrightarrow> (\<forall>s' \<in> D. s' \<in> S)"
begin

lemma E_invariant:
  "{s'. (s, s') \<in> E} \<subseteq> S" if "s \<in> S"
  using that by (auto dest: invariant simp: E_def)

definition "valid_cfg = (\<Union>s\<in>S. cfg_on s)"

lemma valid_cfgI: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> cfg \<in> valid_cfg"
  by (auto simp: valid_cfg_def)

lemma valid_cfgD: "cfg \<in> valid_cfg \<Longrightarrow> cfg \<in> cfg_on (state cfg)"
  by (auto simp: valid_cfg_def)

lemma action_closed: "s \<in> S \<Longrightarrow> cfg \<in> cfg_on s \<Longrightarrow> t \<in> action cfg \<Longrightarrow> t \<in> S"
  using cfg_onD_action[of cfg s] invariant[of s] by auto

lemma
  shows valid_cfg_state_in_S: "cfg \<in> valid_cfg \<Longrightarrow> state cfg \<in> S"
    and valid_cfg_action: "cfg \<in> valid_cfg \<Longrightarrow> s \<in> action cfg \<Longrightarrow> s \<in> S"
    and valid_cfg_cont: "cfg \<in> valid_cfg \<Longrightarrow> s \<in> action cfg \<Longrightarrow> cont cfg s \<in> valid_cfg"
  by (auto simp: valid_cfg_def intro!: bexI[of _ s] intro: action_closed)

lemma valid_K_cfg[intro]: "cfg \<in> valid_cfg \<Longrightarrow> cfg' \<in> K_cfg cfg \<Longrightarrow> cfg' \<in> valid_cfg"
  by (auto simp add: K_cfg_def valid_cfg_cont)

lemma pred_stream_valid_cfg:
  assumes valid: "cfg \<in> valid_cfg"
  assumes enabled: "MC.enabled cfg xs"
  shows "pred_stream (\<lambda> cfg. cfg \<in> valid_cfg) xs"
  using assms by (coinduction arbitrary: cfg xs) (subst (asm) MC.enabled_iff; auto)

lemma pred_stream_cfg_on:
  assumes valid: "cfg \<in> valid_cfg"
  assumes enabled: "MC.enabled cfg xs"
  shows "pred_stream (\<lambda> cfg. state cfg \<in> S \<and> cfg \<in> cfg_on (state cfg)) xs"
  using valid pred_stream_valid_cfg[OF _ enabled] unfolding stream.pred_set
  by (auto intro: valid_cfgI dest: valid_cfgD valid_cfg_state_in_S)

lemma alw_S: "almost_everywhere (T cfg) (pred_stream (\<lambda>s. s \<in> S))" if "cfg \<in> valid_cfg"
  unfolding T_def using pred_stream_cfg_on \<open>cfg \<in> valid_cfg\<close>
  by (subst AE_distr_iff) (measurable, auto simp: stream.pred_set intro: AE_mp[OF MC.AE_T_enabled])

end

context Finite_Markov_Decision_Process
begin

sublocale Invariant: Markov_Decision_Process_Invariant
  rewrites "Invariant.valid_cfg = valid_cfg"
proof -
  show "Markov_Decision_Process_Invariant K S"
    by standard (auto dest: set_pmf_closed)
  then show "Markov_Decision_Process_Invariant.valid_cfg K S = valid_cfg"
    by (subst Markov_Decision_Process_Invariant.valid_cfg_def; simp add: valid_cfg_def)
qed

lemmas pred_stream_cfg_on = Invariant.pred_stream_cfg_on
   and pred_stream_valid_cfg = Invariant.pred_stream_valid_cfg
   and alw_S = Invariant.alw_S
   and valid_cfg_state_in_S = Invariant.valid_cfg_state_in_S

end

end
