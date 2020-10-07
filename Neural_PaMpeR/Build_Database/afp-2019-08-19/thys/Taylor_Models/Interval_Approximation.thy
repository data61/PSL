section \<open>Approximate Operations on Intervals of Floating Point Numbers\<close>
theory Interval_Approximation
  imports
    "HOL-Decision_Procs.Approximation_Bounds"
    Interval
begin

lifting_update float.lifting \<comment> \<open>TODO: in Float!\<close>
lifting_forget float.lifting

text \<open>TODO: many of the lemmas should move to theories Float or Approximation
  (the latter should be based on type @{type interval}.\<close>

subsection "Intervals with Floating Point Bounds"

lift_definition round_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval"
  is "\<lambda>p. \<lambda>(l, u). (float_round_down p l, float_round_up p u)"
  by (auto simp: intro!: float_round_down_le float_round_up_le)

lemma lower_round_ivl[simp]: "lower (round_interval p x) = float_round_down p (lower x)"
  by transfer auto
lemma upper_round_ivl[simp]: "upper (round_interval p x) = float_round_up p (upper x)"
  by transfer auto

lemma round_ivl_correct: "set_of A \<subseteq> set_of (round_interval prec A)"
  by (auto simp: set_of_eq float_round_down_le float_round_up_le)

lift_definition truncate_ivl :: "nat \<Rightarrow> real interval \<Rightarrow> real interval"
  is "\<lambda>p. \<lambda>(l, u). (truncate_down p l, truncate_up p u)"
  by (auto intro!: truncate_down_le truncate_up_le)

lemma lower_truncate_ivl[simp]: "lower (truncate_ivl p x) = truncate_down p (lower x)"
  by transfer auto
lemma upper_truncate_ivl[simp]: "upper (truncate_ivl p x) = truncate_up p (upper x)"
  by transfer auto

lemma truncate_ivl_correct: "set_of A \<subseteq> set_of (truncate_ivl prec A)"
  by (auto simp: set_of_eq intro!: truncate_down_le truncate_up_le)

lift_definition real_interval::"float interval \<Rightarrow> real interval"
  is "\<lambda>(l, u). (real_of_float l, real_of_float u)"
  by auto

lemma lower_real_interval[simp]: "lower (real_interval x) = lower x"
  by transfer auto
lemma upper_real_interval[simp]: "upper (real_interval x) = upper x"
  by transfer auto

definition "set_of' x = (case x of None \<Rightarrow> UNIV | Some i \<Rightarrow> set_of (real_interval i))"

lemma real_interval_min_interval[simp]:
  "real_interval (min_interval a b) = min_interval (real_interval a) (real_interval b)"
  by (auto simp: interval_eq_set_of_iff set_of_eq real_of_float_min)

lemma real_interval_max_interval[simp]:
  "real_interval (max_interval a b) = max_interval (real_interval a) (real_interval b)"
  by (auto simp: interval_eq_set_of_iff set_of_eq real_of_float_max)

subsection \<open>Intervals for standard functions\<close>

lift_definition power_float_interval :: "nat \<Rightarrow> nat \<Rightarrow> float interval \<Rightarrow> float interval"
  is "\<lambda>p n (l, u). float_power_bnds p n l u"
  using float_power_bnds
  by (auto simp: bnds_power dest!: float_power_bnds[OF sym])

lemma lower_power_float_interval[simp]:
  "lower (power_float_interval p n x) = fst (float_power_bnds p n (lower x) (upper x))"
  by transfer auto
lemma upper_power_float_interval[simp]:
  "upper (power_float_interval p n x) = snd (float_power_bnds p n (lower x) (upper x))"
  by transfer auto

lemma power_float_intervalI: "x \<in>\<^sub>i real_interval X \<Longrightarrow> x ^ n \<in>\<^sub>i real_interval (power_float_interval p n X)"
  using float_power_bnds[OF prod.collapse]
  by (auto simp: set_of_eq )

lift_definition mult_float_interval::"nat \<Rightarrow> float interval \<Rightarrow> float interval \<Rightarrow> float interval"
  is "\<lambda>prec. \<lambda>(a1, a2). \<lambda>(b1, b2). bnds_mult prec a1 a2 b1 b2"
  by (auto dest!: bnds_mult[OF sym])

lemma lower_mult_float_interval[simp]:
  "lower (mult_float_interval p x y) = fst (bnds_mult p (lower x) (upper x) (lower y) (upper y))"
  by transfer auto
lemma upper_mult_float_interval[simp]:
  "upper (mult_float_interval p x y) = snd (bnds_mult p (lower x) (upper x) (lower y) (upper y))"
  by transfer auto

lemma mult_float_interval:
  "set_of (real_interval A) * set_of (real_interval B) \<subseteq>
    set_of (real_interval (mult_float_interval prec A B))"
proof -
  let ?bm = "bnds_mult prec (lower A) (upper A) (lower B) (upper B)"
  show ?thesis
    using bnds_mult[of "fst ?bm" "snd ?bm", simplified, OF refl]
    by (auto simp: set_of_eq set_times_def)
qed

lemma mult_float_intervalI:
  "x * y \<in>\<^sub>i (real_interval (mult_float_interval prec A B))"
  if "x \<in>\<^sub>i real_interval A" "y \<in>\<^sub>i real_interval B"
  using mult_float_interval[of A B] that
  by (auto simp: )

lift_definition sqrt_float_interval::"nat \<Rightarrow> float interval \<Rightarrow> float interval"
  is "\<lambda>prec. \<lambda>(lx, ux). (lb_sqrt prec lx, ub_sqrt prec ux)"
  using bnds_sqrt'
  by auto (meson order_trans real_sqrt_le_iff)

lemma lower_float_interval[simp]: "lower (sqrt_float_interval prec X) = lb_sqrt prec (lower X)"
  by transfer auto

lemma upper_float_interval[simp]: "upper (sqrt_float_interval prec X) = ub_sqrt prec (upper X)"
  by transfer auto

lemma sqrt_float_interval:
  "sqrt ` set_of (real_interval X) \<subseteq> set_of (real_interval (sqrt_float_interval prec X))"
  using bnds_sqrt
  by (auto simp: set_of_eq)

lemma sqrt_float_intervalI:
  "sqrt x \<in>\<^sub>i real_interval (sqrt_float_interval p X)"
  if "x \<in> set_of (real_interval X)"
  using sqrt_float_interval[of X p] that
  by auto

lemmas [simp del] = lb_arctan.simps ub_arctan.simps

lemma lb_arctan: "arctan (real_of_float x) \<le> y \<Longrightarrow> real_of_float (lb_arctan prec x) \<le> y"
  and ub_arctan: "y \<le> arctan x \<Longrightarrow> y \<le> ub_arctan prec x"
  for x::float and y::real
  using arctan_boundaries[of x prec] by auto

lift_definition arctan_float_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval"
  is "\<lambda>prec. \<lambda>(lx, ux). (lb_arctan prec lx, ub_arctan prec ux)"
  by (auto intro!: lb_arctan ub_arctan arctan_monotone')

lemma lower_arctan_float_interval[simp]: "lower (arctan_float_interval p x) = lb_arctan p (lower x)"
  by transfer auto
lemma upper_arctan_float_interval[simp]: "upper (arctan_float_interval p x) = ub_arctan p (upper x)"
  by transfer auto

lemma arctan_float_interval:
  "arctan ` set_of (real_interval x) \<subseteq> set_of (real_interval (arctan_float_interval p x))"
  by (auto simp: set_of_eq intro!: lb_arctan ub_arctan arctan_monotone')

lemma arctan_float_intervalI:
  "arctan x \<in>\<^sub>i real_interval (arctan_float_interval p X)"
  if "x \<in> set_of (real_interval X)"
  using arctan_float_interval[of X p] that
  by auto

lemma bnds_cos_lower: "\<And>x. real_of_float xl \<le> x \<Longrightarrow> x \<le> real_of_float xu \<Longrightarrow> cos x \<le> y \<Longrightarrow> real_of_float (fst (bnds_cos prec xl xu)) \<le> y"
  and bnds_cos_upper: "\<And>x. real_of_float xl \<le> x \<Longrightarrow> x \<le> real_of_float xu \<Longrightarrow> y \<le> cos x \<Longrightarrow> y \<le> real_of_float (snd (bnds_cos prec xl xu))"
  for xl xu::float and y::real
  using bnds_cos[of "fst (bnds_cos prec xl xu)" "snd (bnds_cos prec xl xu)" prec]
  by force+

lift_definition cos_float_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval"
  is "\<lambda>prec. \<lambda>(lx, ux). bnds_cos prec lx ux"
  using bnds_cos
  by auto (metis (full_types) order_refl order_trans)

lemma lower_cos_float_interval[simp]: "lower (cos_float_interval p x) = fst (bnds_cos p (lower x) (upper x))"
  by transfer auto
lemma upper_cos_float_interval[simp]: "upper (cos_float_interval p x) = snd (bnds_cos p (lower x) (upper x))"
  by transfer auto

lemma cos_float_interval:
  "cos ` set_of (real_interval x) \<subseteq> set_of (real_interval (cos_float_interval p x))"
  by (auto simp: set_of_eq bnds_cos_lower bnds_cos_upper)

lemma cos_float_intervalI:
  "cos x \<in>\<^sub>i real_interval (cos_float_interval p X)"
  if "x \<in> set_of (real_interval X)"
  using cos_float_interval[of X p] that
  by auto

lemma lb_exp: "exp x \<le> y \<Longrightarrow> lb_exp prec x \<le> y"
  and ub_exp: "y \<le> exp x \<Longrightarrow> y \<le> ub_exp prec x"
  for x::float and y::real using exp_boundaries[of x prec] by auto

lift_definition exp_float_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval"
  is "\<lambda>prec. \<lambda>(lx, ux). (lb_exp prec lx, ub_exp prec ux)"
  by (auto simp: lb_exp ub_exp)

lemma lower_exp_float_interval[simp]: "lower (exp_float_interval p x) = lb_exp p (lower x)"
  by transfer auto
lemma upper_exp_float_interval[simp]: "upper (exp_float_interval p x) = ub_exp p (upper x)"
  by transfer auto

lemma exp_float_interval:
  "exp ` set_of (real_interval x) \<subseteq> set_of (real_interval (exp_float_interval p x))"
  using exp_boundaries apply (auto simp: set_of_eq)
  apply (smt exp_le_cancel_iff)
  apply (smt exp_le_cancel_iff)
  done

lemma exp_float_intervalI:
  "exp x \<in>\<^sub>i real_interval (exp_float_interval p X)"
  if "x \<in> set_of (real_interval X)"
  using exp_float_interval[of X p] that
  by auto

lemmas [simp del] = lb_ln.simps ub_ln.simps

lemma lb_lnD:
  "y \<le> ln x \<and> 0 < real_of_float x" if "lb_ln prec x = Some y"
  using lb_ln[OF that[symmetric]] by auto

lemma ub_lnD:
  "ln x \<le> y\<and> 0 < real_of_float x" if "ub_ln prec x = Some y"
  using ub_ln[OF that[symmetric]] by auto

lift_definition(code_dt) ln_float_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval option"
  is "\<lambda>prec. \<lambda>(lx, ux).
    Option.bind (lb_ln prec lx) (\<lambda>l.
      Option.bind (ub_ln prec ux) (\<lambda>u. Some (l, u)))"
  by (auto simp: pred_option_def bind_eq_Some_conv ln_le_cancel_iff[symmetric]
      simp del: ln_le_cancel_iff dest!: lb_lnD ub_lnD)

lemma ln_float_interval_eq_Some_conv[simp]:
  "ln_float_interval p x = Some y \<longleftrightarrow>
    lb_ln p (lower x) = Some (lower y) \<and> ub_ln p (upper x) = Some (upper y)"
  by transfer (auto simp: bind_eq_Some_conv)

lemma ln_float_interval: "ln ` set_of (real_interval x) \<subseteq> set_of (real_interval y)"
  if "ln_float_interval p x = Some y"
  using that
  by (simp add: set_of_eq)
    (smt atLeastAtMost_iff bnds_ln image_subset_iff)

lemma ln_float_intervalI:
  "ln x \<in> set_of' (ln_float_interval p X)"
  if "x \<in>\<^sub>i (real_interval X)"
  using ln_float_interval[of p X] that
  by (auto simp: set_of'_def split: option.splits)

lift_definition(code_dt) powr_float_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval \<Rightarrow> float interval option"
  is "\<lambda>prec. \<lambda>(l1, u1). \<lambda>(l2, u2). bnds_powr prec l1 u1 l2 u2"
  by (auto simp: pred_option_def dest!: bnds_powr[OF sym])

lemma powr_float_interval:
  "{x powr y | x y. x \<in> set_of (real_interval X) \<and> y \<in> set_of (real_interval Y)}
    \<subseteq> set_of (real_interval R)"
  if "powr_float_interval prec X Y = Some R"
  using that
  by transfer (auto dest!: bnds_powr[OF sym])

lemma powr_float_intervalI:
  "x powr y \<in> set_of' (powr_float_interval p X Y)"
  if "x \<in>\<^sub>i real_interval X" "y \<in>\<^sub>i real_interval Y"
  using powr_float_interval[of p X Y] that
  by (auto simp: set_of'_def split: option.splits)

lift_definition(code_dt) inverse_float_interval::"nat \<Rightarrow> float interval \<Rightarrow> float interval option" is
  "\<lambda>prec (l, u). if (0 < l \<or> u < 0) then Some (float_divl prec 1 u, float_divr prec 1 l) else None"
  by (auto intro!: order_trans[OF float_divl] order_trans[OF _ float_divr]
      simp: divide_simps)

lemma inverse_float_interval_eq_Some_conv[simp]:
  defines "one \<equiv> (1::float)"
  shows 
    "inverse_float_interval p X = Some R \<longleftrightarrow>
    (lower X > 0 \<or> upper X < 0) \<and>
    lower R = float_divl p one (upper X) \<and>
    upper R = float_divr p one (lower X)"
  by clarsimp (transfer fixing: one, force simp: one_def split: if_splits)

lemma inverse_float_interval:
  "inverse ` set_of (real_interval X) \<subseteq> set_of (real_interval Y)"
  if "inverse_float_interval p X = Some Y"
  using that
  apply (clarsimp simp: set_of_eq)
  by (intro order_trans[OF float_divl] order_trans[OF _ float_divr] conjI)
    (auto simp: divide_simps)

lemma inverse_float_intervalI:
  "x \<in> set_of (real_interval X) \<Longrightarrow> inverse x \<in> set_of' (inverse_float_interval p X)"
  using inverse_float_interval[of p X]
  by (auto simp: set_of'_def split: option.splits)


lift_definition pi_float_interval::"nat \<Rightarrow> float interval" is "\<lambda>prec. (lb_pi prec, ub_pi prec)"
  using pi_boundaries
  by (auto intro: order_trans)

lemma lower_pi_float_interval[simp]: "lower (pi_float_interval prec) = lb_pi prec"
  by transfer auto
lemma upper_pi_float_interval[simp]: "upper (pi_float_interval prec) = ub_pi prec"
  by transfer auto
lemma pi_float_interval: "pi \<in> set_of (real_interval (pi_float_interval prec))"
  using pi_boundaries
  by (auto simp: set_of_eq)

lemma real_interval_abs_interval[simp]:
  "real_interval (abs_interval x) = abs_interval (real_interval x)"
  by (auto simp: interval_eq_set_of_iff set_of_eq real_of_float_max real_of_float_min)

lift_definition floor_float_interval::"float interval \<Rightarrow> float interval" is
  "\<lambda>(l, u). (floor_fl l, floor_fl u)"
  by (auto intro!: floor_mono simp: floor_fl.rep_eq)

lemma lower_floor_float_interval[simp]: "lower (floor_float_interval x) = floor_fl (lower x)"
  by transfer auto
lemma upper_floor_float_interval[simp]: "upper (floor_float_interval x) = floor_fl (upper x)"
  by transfer auto

lemma floor_float_intervalI: "\<lfloor>x\<rfloor> \<in>\<^sub>i real_interval (floor_float_interval X)"
  if "x \<in>\<^sub>i real_interval X"
  using that by (auto simp: set_of_eq floor_fl_def floor_mono)


lemma in_intervalI:
  "x \<in>\<^sub>i X" if "lower X \<le> x" "x \<le> upper X"
  using that by (auto simp: set_of_eq)

abbreviation in_real_interval ("(_/ \<in>\<^sub>r _)" [51, 51] 50) where
  "x \<in>\<^sub>r X \<equiv> x \<in>\<^sub>i real_interval X"

lemma in_real_intervalI:
  "x \<in>\<^sub>r X" if "lower X \<le> x" "x \<le> upper X" for x::real and X::"float interval"
  using that
  by (intro in_intervalI) auto

lemma lower_Interval: "lower (Interval x) = fst x"
  and upper_Interval: "upper (Interval x) = snd x"
  if "fst x \<le> snd x"
  using that
  by (auto simp: lower_def upper_def Interval_inverse split_beta')

definition all_in_i :: "'a::preorder list \<Rightarrow> 'a interval list \<Rightarrow> bool"
  (infix "(all'_in\<^sub>i)" 50)
  where "x all_in\<^sub>i I = (length x = length I \<and> (\<forall>i < length I. x ! i \<in>\<^sub>i I ! i))"

definition all_in :: "real list \<Rightarrow> float interval list \<Rightarrow> bool"
  (infix "(all'_in)" 50)
  where "x all_in I = (length x = length I \<and> (\<forall>i < length I. x ! i \<in>\<^sub>r I ! i))"

definition all_subset :: "'a::order interval list \<Rightarrow> 'a interval list \<Rightarrow> bool"
  (infix "(all'_subset)" 50)
  where "I all_subset J = (length I = length J \<and> (\<forall>i < length I. set_of (I!i) \<subseteq> set_of (J!i)))"

lemmas [simp] = all_in_def all_subset_def

lemma all_subsetD:
  assumes "I all_subset J"
  assumes "x all_in I"
  shows "x all_in J"
  using assms
  by (auto simp: set_of_eq; fastforce)

lemma plus_down_mono: "plus_down p a b \<le> plus_down p c d" if "a + b \<le> c + d"
  by (auto simp: plus_down_def intro!: truncate_down_mono that)

lemma plus_up_mono: "plus_up p a b \<le> plus_up p c d" if "a + b \<le> c + d"
  by (auto simp: plus_up_def intro!: truncate_up_mono that)

lemma round_interval_mono: "set_of (round_interval prec X) \<subseteq> set_of (round_interval prec Y)"
  if "set_of X \<subseteq> set_of Y"
  using that
  by transfer
    (auto simp: float_round_down.rep_eq float_round_up.rep_eq truncate_down_mono truncate_up_mono)

lemma mult_mono_nonpos_nonneg: "a * b \<le> c * d"
  if  "a \<le> c" "a \<le> 0" "0 \<le> d" "d \<le> b" for a b c d::"'a::ordered_ring"
  apply (rule order_trans[OF mult_left_mono_neg[OF \<open>d \<le> b\<close>]])
  subgoal using that by auto
  by (rule mult_right_mono; fact)

lemma mult_mono_nonneg_nonpos: "b * a \<le> d * c"
  if  "a \<le> c" "c \<le> 0" "0 \<le> d" "d \<le> b" for a b c d::"'a::ordered_ring"
  apply (rule order_trans[OF mult_right_mono_neg[OF \<open>d \<le> b\<close>]])
  subgoal using that by auto
  by (rule mult_left_mono; fact)

lemma mult_mono_nonpos_nonpos: "a * b \<le> c * d"
  if  "a \<ge> c" "a \<le> 0" "b \<ge> d" "d \<le> 0" for a b c d::real
  apply (rule order_trans[OF mult_left_mono_neg[OF \<open>d \<le> b\<close>]])
  subgoal using that by auto
  by (rule mult_right_mono_neg; fact)

lemma mult_float_mono1:
  notes mono_rules = plus_down_mono add_mono nprt_mono nprt_le_zero zero_le_pprt pprt_mono
  shows "a \<le> b \<Longrightarrow> ab \<le> bb \<Longrightarrow>
       aa \<le> a \<Longrightarrow>
       b \<le> ba \<Longrightarrow>
       ac \<le> ab \<Longrightarrow>
       bb \<le> bc \<Longrightarrow>
       plus_down prec (nprt aa * pprt bc)
        (plus_down prec (nprt ba * nprt bc)
          (plus_down prec (pprt aa * pprt ac)
            (pprt ba * nprt ac)))
       \<le> plus_down prec (nprt a * pprt bb)
           (plus_down prec (nprt b * nprt bb)
             (plus_down prec (pprt a * pprt ab)
               (pprt b * nprt ab)))"
  apply (rule order_trans)
  apply (rule mono_rules | assumption)+
  apply (rule mult_mono_nonpos_nonneg)
  apply (rule mono_rules | assumption)+
  apply (rule mult_mono_nonpos_nonpos)
  apply (rule mono_rules | assumption)+
  apply (rule mult_mono)
  apply (rule mono_rules | assumption)+
  apply (rule mult_mono_nonneg_nonpos)
  apply (rule mono_rules | assumption)+
  by (rule order_refl)+

lemma mult_float_mono2:
  notes mono_rules = plus_up_mono add_mono nprt_mono nprt_le_zero zero_le_pprt pprt_mono
  shows "a \<le> b \<Longrightarrow>
       ab \<le> bb \<Longrightarrow>
       aa \<le> a \<Longrightarrow>
       b \<le> ba \<Longrightarrow>
       ac \<le> ab \<Longrightarrow>
       bb \<le> bc \<Longrightarrow>
       plus_up prec (pprt b * pprt bb)
        (plus_up prec (pprt a * nprt bb)
          (plus_up prec (nprt b * pprt ab)
            (nprt a * nprt ab)))
       \<le> plus_up prec (pprt ba * pprt bc)
           (plus_up prec (pprt aa * nprt bc)
             (plus_up prec (nprt ba * pprt ac)
               (nprt aa * nprt ac)))"
  apply (rule order_trans)
  apply (rule mono_rules | assumption)+
  apply (rule mult_mono)
  apply (rule mono_rules | assumption)+
  apply (rule mult_mono_nonneg_nonpos)
  apply (rule mono_rules | assumption)+
  apply (rule mult_mono_nonpos_nonneg)
  apply (rule mono_rules | assumption)+
  apply (rule mult_mono_nonpos_nonpos)
  apply (rule mono_rules | assumption)+
  by (rule order_refl)+

lemma mult_float_interval_mono: "set_of (mult_float_interval prec A B) \<subseteq> set_of (mult_float_interval prec X Y)"
  if "set_of A \<subseteq> set_of X" "set_of B \<subseteq> set_of Y"
  using that
  apply transfer
  unfolding bnds_mult_def atLeastatMost_subset_iff float_plus_down.rep_eq float_plus_up.rep_eq
  by (auto simp: float_plus_down.rep_eq float_plus_up.rep_eq mult_float_mono1 mult_float_mono2)

lemma Ivl_simps[simp]: "lower (Ivl a b) = min a b" "upper (Ivl a b) = b"
  subgoal by transfer simp
  subgoal by transfer simp
  done

lemmas [simp del] = power_down.simps(2) power_up.simps(2)
lemmas power_down_simp = power_down.simps(2)
lemmas power_up_simp = power_up.simps(2)

lemma power_down_even_nonneg: "even n \<Longrightarrow> 0 \<le> power_down p x n"
  by (induct p x n rule: power_down.induct)
    (auto simp: power_down_simp simp del: odd_Suc_div_two intro!: truncate_down_nonneg )

lemma truncate_down_less_zero_iff[simp]: "truncate_down p x < 0 \<longleftrightarrow> x < 0"
  by (metis le_less_trans not_less_iff_gr_or_eq truncate_down truncate_down_pos truncate_down_zero)

lemma truncate_down_nonneg_iff[simp]: "truncate_down p x \<ge> 0 \<longleftrightarrow> x \<ge> 0"
  using truncate_down_less_zero_iff[of p x] truncate_down_nonneg[of x p]
  by linarith

lemma truncate_down_eq_zero_iff[simp]: "truncate_down prec x = 0 \<longleftrightarrow> x = 0"
  by (metis not_less_iff_gr_or_eq truncate_down_less_zero_iff truncate_down_pos truncate_down_zero)

lemma power_down_eq_zero_iff[simp]: "power_down prec b n = 0 \<longleftrightarrow> b = 0 \<and> n \<noteq> 0"
proof (induction n arbitrary: b rule: less_induct)
  case (less x)
  then show ?case
    using power_down_simp[of _ _ "x - 1"]
    by (cases x) (auto simp: sign_simps zero_le_mult_iff div2_less_self)
qed

lemma power_down_nonneg_iff[simp]:
  "power_down prec b n \<ge> 0 \<longleftrightarrow> even n \<or> b \<ge> 0"
proof (induction n arbitrary: b rule: less_induct)
  case (less x)
  show ?case
    using less(1)[of "x - 1" b] power_down_simp[of _ _ "x - 1"]
    by (cases x) (auto simp: sign_simps zero_le_mult_iff)
qed

lemma power_down_neg_iff[simp]:
  "power_down prec b n < 0 \<longleftrightarrow>
    b < 0 \<and> odd n"
  using power_down_nonneg_iff[of prec b n] by (auto simp del: power_down_nonneg_iff)

lemma power_down_nonpos_iff[simp]:
  notes [simp del] = power_down_neg_iff power_down_eq_zero_iff
  shows "power_down prec b n \<le> 0 \<longleftrightarrow> b < 0 \<and> odd n \<or> b = 0 \<and> n \<noteq> 0"
  using power_down_neg_iff[of prec b n] power_down_eq_zero_iff[of prec b n]
  by auto

lemma power_down_mono:
  "power_down prec a n \<le> power_down prec b n"
  if "((0 \<le> a \<and> a \<le> b)\<or>(odd n \<and> a \<le> b) \<or> (even n \<and> a \<le> 0 \<and> b \<le> a))"
  using that
proof (induction n arbitrary: a b rule: less_induct)
  case (less i)
  show ?case
  proof (cases i)
    case j: (Suc j)
    note IH = less[unfolded j even_Suc not_not]
    note [simp del] = power_down.simps
    show ?thesis
    proof cases
      assume [simp]: "even j"
      have "a * power_down prec a j \<le> b * power_down prec b j"
        by (smt IH(1) IH(2) \<open>even j\<close> lessI mult_mono' mult_mono_nonpos_nonneg power_down_even_nonneg)
      then have "truncate_down (Suc prec) (a * power_down prec a j) \<le> truncate_down (Suc prec) (b * power_down prec b j)"
        by (auto intro!: truncate_down_mono simp: abs_le_square_iff[symmetric] abs_real_def)
      then show ?thesis
        unfolding j
        by (simp add: power_down_simp)
    next
      assume [simp]: "odd j"
      have "power_down prec 0 (Suc (j div 2)) \<le> - power_down prec b (Suc (j div 2))"
        if "b < 0" "even (j div 2)"
        apply (rule order_trans[where y=0])
        using IH that by (auto simp: div2_less_self)
      then have "truncate_down (Suc prec) ((power_down prec a (Suc (j div 2)))\<^sup>2)
        \<le> truncate_down (Suc prec) ((power_down prec b (Suc (j div 2)))\<^sup>2)"
        using IH
        by (auto intro!: truncate_down_mono intro: order_trans[where y=0]
            simp: abs_le_square_iff[symmetric] abs_real_def
            div2_less_self)
      then show ?thesis
        unfolding j
        by (simp add: power_down_simp)
    qed
  qed simp
qed

lemma truncate_up_nonneg: "0 \<le> truncate_up p x" if "0 \<le> x"
  by (simp add: that truncate_up_le)

lemma truncate_up_pos: "0 < truncate_up p x" if "0 < x"
  by (meson less_le_trans that truncate_up)

lemma truncate_up_less_zero_iff[simp]: "truncate_up p x < 0 \<longleftrightarrow> x < 0"
proof -
  have f1: "\<forall>n r. truncate_up n r + truncate_down n (- 1 * r) = 0"
    by (simp add: truncate_down_uminus_eq)
  have f2: "(\<forall>v0 v1. truncate_up v0 v1 + truncate_down v0 (- 1 * v1) = 0) = (\<forall>v0 v1. truncate_up v0 v1 = - 1 * truncate_down v0 (- 1 * v1))"
    by (auto simp: truncate_up_eq_truncate_down)
  have f3: "\<forall>x1. ((0::real) < x1) = (\<not> x1 \<le> 0)"
    by fastforce
  have "(- 1 * x \<le> 0) = (0 \<le> x)"
    by force
  then have "0 \<le> x \<or> \<not> truncate_down p (- 1 * x) \<le> 0"
    using f3 by (meson truncate_down_pos)
  then have "(0 \<le> truncate_up p x) \<noteq> (\<not> 0 \<le> x)"
    using f2 f1 truncate_up_nonneg by force
  then show ?thesis
    by linarith
qed

lemma truncate_up_nonneg_iff[simp]: "truncate_up p x \<ge> 0 \<longleftrightarrow> x \<ge> 0"
  using truncate_up_less_zero_iff[of p x] truncate_up_nonneg[of x]
  by linarith

lemma power_up_even_nonneg: "even n \<Longrightarrow> 0 \<le> power_up p x n"
  by (induct p x n rule: power_up.induct)
    (auto simp: power_up.simps simp del: odd_Suc_div_two intro!: )

lemma truncate_up_eq_zero_iff[simp]: "truncate_up prec x = 0 \<longleftrightarrow> x = 0"
  by (metis not_less_iff_gr_or_eq truncate_up_less_zero_iff truncate_up_pos truncate_up_zero)

lemma power_up_eq_zero_iff[simp]: "power_up prec b n = 0 \<longleftrightarrow> b = 0 \<and> n \<noteq> 0"
proof (induction n arbitrary: b rule: less_induct)
  case (less x)
  then show ?case
    using power_up_simp[of _ _ "x - 1"]
    by (cases x) (auto simp: sign_simps zero_le_mult_iff div2_less_self)
qed

lemma power_up_nonneg_iff[simp]:
  "power_up prec b n \<ge> 0 \<longleftrightarrow> even n \<or> b \<ge> 0"
proof (induction n arbitrary: b rule: less_induct)
  case (less x)
  show ?case
    using less(1)[of "x - 1" b] power_up_simp[of _ _ "x - 1"]
    by (cases x) (auto simp: sign_simps zero_le_mult_iff)
qed

lemma power_up_neg_iff[simp]:
  "power_up prec b n < 0 \<longleftrightarrow> b < 0 \<and> odd n"
  using power_up_nonneg_iff[of prec b n] by (auto simp del: power_up_nonneg_iff)

lemma power_up_nonpos_iff[simp]:
  notes [simp del] = power_up_neg_iff power_up_eq_zero_iff
  shows "power_up prec b n \<le> 0 \<longleftrightarrow> b < 0 \<and> odd n \<or> b = 0 \<and> n \<noteq> 0"
  using power_up_neg_iff[of prec b n] power_up_eq_zero_iff[of prec b n]
  by auto

lemma power_up_mono:
  "power_up prec a n \<le> power_up prec b n"
  if "((0 \<le> a \<and> a \<le> b)\<or>(odd n \<and> a \<le> b) \<or> (even n \<and> a \<le> 0 \<and> b \<le> a))"
  using that
proof (induction n arbitrary: a b rule: less_induct)
  case (less i)
  show ?case
  proof (cases i)
    case j: (Suc j)
    note IH = less[unfolded j even_Suc not_not]
    note [simp del] = power_up.simps
    show ?thesis
    proof cases
      assume [simp]: "even j"
      have "a * power_up prec a j \<le> b * power_up prec b j"
        by (smt IH(1) IH(2) \<open>even j\<close> lessI mult_mono' mult_mono_nonpos_nonneg power_up_even_nonneg)
      then have "truncate_up prec (a * power_up prec a j) \<le> truncate_up prec (b * power_up prec b j)"
        by (auto intro!: truncate_up_mono simp: abs_le_square_iff[symmetric] abs_real_def)
      then show ?thesis
        unfolding j
        by (simp add: power_up_simp)
    next
      assume [simp]: "odd j"
      have "power_up prec 0 (Suc (j div 2)) \<le> - power_up prec b (Suc (j div 2))"
        if "b < 0" "even (j div 2)"
        apply (rule order_trans[where y=0])
        using IH that by (auto simp: div2_less_self)
      then have "truncate_up prec ((power_up prec a (Suc (j div 2)))\<^sup>2)
        \<le> truncate_up prec ((power_up prec b (Suc (j div 2)))\<^sup>2)"
        using IH
        by (auto intro!: truncate_up_mono intro: order_trans[where y=0]
            simp: abs_le_square_iff[symmetric] abs_real_def
            div2_less_self)
      then show ?thesis
        unfolding j
        by (simp add: power_up_simp)
    qed
  qed simp
qed

lemma set_of_subset_iff: "set_of X \<subseteq> set_of Y \<longleftrightarrow> lower Y \<le> lower X \<and> upper X \<le> upper Y"
  for X Y::"'a::linorder interval"
  by (auto simp: set_of_eq subset_iff)

lemma power_float_interval_mono:
  "set_of (power_float_interval prec n A)
    \<subseteq> set_of (power_float_interval prec n B)"
  if "set_of A \<subseteq> set_of B"
proof -
  define la where "la = real_of_float (lower A)"
  define ua where "ua = real_of_float (upper A)"
  define lb where "lb = real_of_float (lower B)"
  define ub where "ub = real_of_float (upper B)"
  have ineqs: "lb \<le> la" "la \<le> ua" "ua \<le> ub" "lb \<le> ub"
    using that lower_le_upper[of A] lower_le_upper[of B]
    by (auto simp: la_def ua_def lb_def ub_def set_of_eq)
  show ?thesis
    using ineqs
    by (simp add: set_of_subset_iff float_power_bnds_def max_def
        power_down_fl.rep_eq power_up_fl.rep_eq
        la_def[symmetric] ua_def[symmetric] lb_def[symmetric] ub_def[symmetric])
      (auto intro!: power_down_mono power_up_mono intro: order_trans[where y=0])
qed

lemma bounds_of_interval_eq_lower_upper:
  "bounds_of_interval ivl = (lower ivl, upper ivl)" if "lower ivl \<le> upper ivl"
  using that
  by (auto simp: lower.rep_eq upper.rep_eq)

lemma real_interval_Ivl: "real_interval (Ivl a b) = Ivl a b"
  by transfer (auto simp: min_def)

lemma set_of_mul_contains_real_zero:
  "0 \<in>\<^sub>r (A * B)" if "0 \<in>\<^sub>r A \<or> 0 \<in>\<^sub>r B"
  using that set_of_mul_contains_zero[of A B]
  by (auto simp: set_of_eq)

fun subdivide_interval :: "nat \<Rightarrow> float interval \<Rightarrow> float interval list"
  where "subdivide_interval 0 I = [I]"
  | "subdivide_interval (Suc n) I = (
         let m = mid I
         in (subdivide_interval n (Ivl (lower I) m)) @ (subdivide_interval n (Ivl m (upper I)))
       )"

lemma subdivide_interval_length:
  shows "length (subdivide_interval n I) = 2^n"
  by(induction n arbitrary: I, simp_all add: Let_def)

lemma lower_le_mid: "lower x \<le> mid x" "real_of_float (lower x) \<le> mid x"
  and mid_le_upper: "mid x \<le> upper x" "real_of_float (mid x) \<le> upper x"
  unfolding mid_def
  subgoal by transfer auto
  subgoal by transfer auto
  subgoal by transfer auto
  subgoal by transfer auto
  done

lemma subdivide_interval_correct:
  "list_ex (\<lambda>i. x \<in>\<^sub>r i) (subdivide_interval n I)" if "x \<in>\<^sub>r I" for x::real
  using that
proof(induction n arbitrary: x I)
  case 0
  then show ?case by simp
next
  case (Suc n)
  from \<open>x \<in>\<^sub>r I\<close> consider "x \<in>\<^sub>r Ivl (lower I) (mid I)" | "x \<in>\<^sub>r Ivl (mid I) (upper I)"
    by (cases "x \<le> real_of_float (mid I)")
      (auto simp: set_of_eq min_def lower_le_mid mid_le_upper)
  from this[case_names lower upper] show ?case
    by cases (use Suc.IH in \<open>auto simp: Let_def\<close>)
qed

fun interval_list_union :: "'a::lattice interval list \<Rightarrow> 'a interval"
  where "interval_list_union [] = undefined"
  | "interval_list_union [I] = I"
  | "interval_list_union (I#Is) = sup I (interval_list_union Is)"

lemma interval_list_union_correct:
  assumes "S \<noteq> []"
  assumes "i < length S"
  shows "set_of (S!i) \<subseteq> set_of (interval_list_union S)"
  using assms
proof(induction S arbitrary: i)
  case (Cons a S i)
  thus ?case
  proof(cases S)
    fix b S'
    assume "S = b # S'"
    hence "S \<noteq> []"
      by simp
    show ?thesis
    proof(cases i)
      case 0
      show ?thesis
        apply(cases S)
        using interval_union_mono1
        by (auto simp add: 0)
    next
      case (Suc i_prev)
      hence "i_prev < length S"
        using Cons(3) by simp

      from Cons(1)[OF \<open>S \<noteq> []\<close> this] Cons(1)
      have "set_of ((a # S) ! i) \<subseteq> set_of (interval_list_union S)"
        by (simp add: \<open>i = Suc i_prev\<close>)
      also have "... \<subseteq> set_of (interval_list_union (a # S))"
        using \<open>S \<noteq> []\<close>
        apply(cases S)
        using interval_union_mono2
        by auto
      finally show ?thesis .
    qed
  qed simp
qed simp

lemma split_domain_correct:
  fixes x :: "real list"
  assumes "x all_in I"
  assumes split_correct: "\<And>x a I. x \<in>\<^sub>r I \<Longrightarrow> list_ex (\<lambda>i::float interval. x \<in>\<^sub>r i) (split I)"
  shows "list_ex (\<lambda>s. x all_in s) (split_domain split I)"
  using assms(1)
proof(induction I arbitrary: x)
  case (Cons I Is x)
  have "x \<noteq> []"
    using Cons(2) by auto
  obtain x' xs where x_decomp: "x = x' # xs"
    using \<open>x \<noteq> []\<close> list.exhaust by auto
  hence "x' \<in>\<^sub>r I" "xs all_in Is"
    using Cons(2)
    by auto
  show ?case
    using Cons(1)[OF \<open>xs all_in Is\<close>]
      split_correct[OF \<open>x' \<in>\<^sub>r I\<close>]
    apply(simp add: list_ex_iff set_of_eq)
    by (smt length_Cons less_Suc_eq_0_disj nth_Cons_0 nth_Cons_Suc x_decomp)
qed simp

end