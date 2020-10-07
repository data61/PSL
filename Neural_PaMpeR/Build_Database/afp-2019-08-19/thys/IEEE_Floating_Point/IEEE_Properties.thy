(* Author: Lei Yu, University of Cambridge
   Author: Fabian Hellauer
           Fabian Immler
*)

section \<open>Proofs of Properties about Floating Point Arithmetic\<close>

theory IEEE_Properties
imports IEEE
begin

subsection \<open>Theorems derived from definitions\<close>


lemma valof_eq:
  "valof x =
    (if exponent x = 0
       then (- 1) ^ sign x * (2 / 2 ^ bias TYPE(('a, 'b) float)) *
            (real (fraction x) / 2 ^ LENGTH('b))
       else (- 1) ^ sign x * (2 ^ exponent x / 2 ^ bias TYPE(('a, 'b) float)) *
            (1 + real (fraction x) / 2 ^ LENGTH('b)))"
  for x::"('a, 'b) float"
  unfolding Let_def
  by transfer (auto simp: bias_def divide_simps unat_eq_0)

lemma exponent_le[simp]:
  "exponent a \<le> unat (max_word::'a word)" for a::"('a, _)float"
  by transfer (auto intro!: unat_mono simp: word_le_nat_alt[symmetric])

lemma
  max_word_le_exponent_iff[simp]:
  "unat (max_word::'a word) \<le> exponent a \<longleftrightarrow> unat (max_word::'a word) = exponent a"
  for a::"('a, _)float"
  using le_antisym by fastforce

lemma infinity_simps:
  "sign (plus_infinity::('e, 'f)float) = 0"
  "sign (minus_infinity::('e, 'f)float) = 1"
  "exponent (plus_infinity::('e, 'f)float) = emax TYPE(('e, 'f)float)"
  "exponent (minus_infinity::('e, 'f)float) = emax TYPE(('e, 'f)float)"
  "fraction (plus_infinity::('e, 'f)float) = 0"
  "fraction (minus_infinity::('e, 'f)float) = 0"
  subgoal by transfer auto
  subgoal by transfer auto
  subgoal by transfer (auto simp: emax_def)
  subgoal by transfer (auto simp: emax_def)
  subgoal by transfer auto
  subgoal by transfer auto
  done

lemma zero_simps:
  "sign (0::('e, 'f)float) = 0"
  "sign (- 0::('e, 'f)float) = 1"
  "exponent (0::('e, 'f)float) = 0"
  "exponent (- 0::('e, 'f)float) = 0"
  "fraction (0::('e, 'f)float) = 0"
  "fraction (- 0::('e, 'f)float) = 0"
  subgoal by transfer auto
  subgoal by transfer auto
  subgoal by transfer auto
  subgoal by transfer auto
  subgoal by transfer auto
  subgoal by transfer auto
  done

lemma topfloat_simps:
  "sign (topfloat::('e, 'f)float) = 0"
  "exponent (topfloat::('e, 'f)float) = emax TYPE(('e, 'f)float) - 1"
  "fraction (topfloat::('e, 'f)float) = 2^fracwidth TYPE(('e, 'f)float) - 1"
  and bottomfloat_simps:
  "sign (bottomfloat::('e, 'f)float) = 1"
  "exponent (bottomfloat::('e, 'f)float) = emax TYPE(('e, 'f)float) - 1"
  "fraction (bottomfloat::('e, 'f)float) = 2^fracwidth TYPE(('e, 'f)float) - 1"
  subgoal by transfer auto
  subgoal by transfer (auto simp: emax_def unat_sub)
  subgoal
    apply transfer
    apply safe
    by (metis One_nat_def diff_less lessI minus_one_norm minus_one_word unat_0 unat_lt2p
        unat_of_nat_len)
  subgoal by transfer auto
  subgoal by transfer (auto simp: emax_def unat_sub)
  subgoal
    apply transfer
    apply safe
    by (metis One_nat_def diff_less lessI minus_one_norm minus_one_word unat_0 unat_lt2p
        unat_of_nat_len)
  done

lemma emax_eq: "emax x = 2^LENGTH('e) - 1"
  for x::"('e, 'f)float itself"
  unfolding bias_def emax_def
  by (auto simp: max_word_eq unat_minus word_size)

lemmas float_defs =
  is_finite_def is_infinity_def is_zero_def is_nan_def
  is_normal_def is_denormal_def valof_eq
  less_eq_float_def less_float_def
  flt_def fgt_def fle_def fge_def feq_def
  fcompare_def
  infinity_simps
  zero_simps
  topfloat_simps
  bottomfloat_simps
  float_eq_def

lemma float_cases: "is_nan a \<or> is_infinity a \<or> is_normal a \<or> is_denormal a \<or> is_zero a"
  by (auto simp: emax_def float_defs not_less)

lemma float_cases_finite: "is_nan a \<or> is_infinity a \<or> is_finite a"
  by (simp add: float_cases is_finite_def)

lemma float_zero1[simp]: "is_zero 0"
  unfolding float_defs
  by transfer auto

lemma float_zero2[simp]: "is_zero (- x) \<longleftrightarrow> is_zero x"
  unfolding float_defs
  by transfer auto

lemma emax_pos[simp]: "0 < emax x" "emax x \<noteq> 0"
  by (auto simp: emax_def)

text \<open>The types of floating-point numbers are mutually distinct.\<close>
lemma float_distinct:
  "\<not> (is_nan a \<and> is_infinity a)"
  "\<not> (is_nan a \<and> is_normal a)"
  "\<not> (is_nan a \<and> is_denormal a)"
  "\<not> (is_nan a \<and> is_zero a)"
  "\<not> (is_infinity a \<and> is_normal a)"
  "\<not> (is_infinity a \<and> is_denormal a)"
  "\<not> (is_infinity a \<and> is_zero a)"
  "\<not> (is_normal a \<and> is_denormal a)"
  "\<not> (is_denormal a \<and> is_zero a)"
  by (auto simp: float_defs)

lemma denormal_imp_not_zero: "is_denormal f \<Longrightarrow> \<not>is_zero f"
  by (simp add: is_denormal_def is_zero_def)

lemma normal_imp_not_zero: "is_normal f \<Longrightarrow> \<not>is_zero f"
  by (simp add: is_normal_def is_zero_def)

lemma normal_imp_not_denormal: "is_normal f \<Longrightarrow> \<not>is_denormal f"
  by (simp add: is_normal_def is_denormal_def)

lemma denormal_zero[simp]: "\<not>is_denormal 0" "\<not>is_denormal minus_zero"
  using denormal_imp_not_zero float_zero1 float_zero2 by blast+

lemma normal_zero[simp]: "\<not>is_normal 0" "\<not>is_normal minus_zero"
  using normal_imp_not_zero float_zero1 float_zero2 by blast+

lemma float_distinct_finite: "\<not> (is_nan a \<and> is_finite a)" "\<not>(is_infinity a \<and> is_finite a)"
  by (auto simp: float_defs)

lemma finite_infinity: "is_finite a \<Longrightarrow> \<not> is_infinity a"
  by (auto simp: float_defs)

lemma finite_nan: "is_finite a \<Longrightarrow> \<not> is_nan a"
  by (auto simp: float_defs)

text \<open>For every real number, the floating-point numbers closest to it always exist.\<close>
lemma is_closest_exists:
  fixes v :: "('e, 'f)float \<Rightarrow> real"
    and s :: "('e, 'f)float set"
  assumes finite: "finite s"
    and non_empty: "s \<noteq> {}"
  shows "\<exists>a. is_closest v s x a"
  using finite non_empty
proof (induct s rule: finite_induct)
  case empty
  then show ?case by simp
next
  case (insert z s)
  show ?case
  proof (cases "s = {}")
    case True
    then have "is_closest v (insert z s) x z"
      by (auto simp: is_closest_def)
    then show ?thesis by metis
  next
    case False
    then obtain a where a: "is_closest v s x a"
      using insert by metis
    then show ?thesis
    proof (cases "\<bar>v a - x\<bar>" "\<bar>v z - x\<bar>" rule: le_cases)
      case le
      then show ?thesis
        by (metis insert_iff a is_closest_def)
    next
      case ge
      have "\<forall>b. b \<in> s \<longrightarrow> \<bar>v a - x\<bar> \<le> \<bar>v b - x\<bar>"
        by (metis a is_closest_def)
      then have "\<forall>b. b \<in> insert z s \<longrightarrow> \<bar>v z - x\<bar> \<le> \<bar>v b - x\<bar>"
        by (metis eq_iff ge insert_iff order.trans)
      then show ?thesis using is_closest_def a
        by (metis insertI1)
    qed
  qed
qed

lemma closest_is_everything:
  fixes v :: "('e, 'f)float \<Rightarrow> real"
    and s :: "('e, 'f)float set"
  assumes finite: "finite s"
    and non_empty: "s \<noteq> {}"
  shows "is_closest v s x (closest v p s x) \<and>
    ((\<exists>b. is_closest v s x b \<and> p b) \<longrightarrow> p (closest v p s x))"
  unfolding closest_def
  by (rule someI_ex) (metis assms is_closest_exists [of s v x])

lemma closest_in_set:
  fixes v :: "('e, 'f)float \<Rightarrow> real"
  assumes "finite s" and "s \<noteq> {}"
  shows "closest v p s x \<in> s"
  by (metis assms closest_is_everything is_closest_def)

lemma closest_is_closest_finite:
  fixes v :: "('e, 'f)float \<Rightarrow> real"
  assumes "finite s" and "s \<noteq> {}"
  shows "is_closest v s x (closest v p s x)"
  by (metis closest_is_everything assms)

instance float::(len, len) finite proof qed (transfer, simp)

lemma is_finite_nonempty: "{a. is_finite a} \<noteq> {}"
proof -
  have "0 \<in> {a. is_finite a}"
    unfolding float_defs
    by transfer auto
  then show ?thesis by (metis empty_iff)
qed

lemma closest_is_closest:
  fixes v :: "('e, 'f)float \<Rightarrow> real"
  assumes "s \<noteq> {}"
  shows "is_closest v s x (closest v p s x)"
  by (rule closest_is_closest_finite) (auto simp: assms)


subsection \<open>Properties about ordering and bounding\<close>

text \<open>Lifting of non-exceptional comparisons.\<close>
lemma float_lt [simp]:
  assumes "is_finite a" "is_finite b"
  shows "a < b \<longleftrightarrow> valof a < valof b"
proof
  assume "valof a < valof b"
  moreover have "\<not> is_nan a" and "\<not> is_nan b" and "\<not> is_infinity a" and "\<not> is_infinity b"
    using assms by (auto simp: finite_nan finite_infinity)
  ultimately have "fcompare a b = Lt"
    by (auto simp add: is_infinity_def is_nan_def valof_def fcompare_def)
  then show "a < b" by (auto simp: float_defs)
next
  assume "a < b"
  then have lt: "fcompare a b = Lt"
    by (simp add: float_defs)
  have "\<not> is_nan a" and "\<not> is_nan b" and "\<not> is_infinity a" and "\<not> is_infinity b"
    using assms by (auto simp: finite_nan finite_infinity)
  then show "valof a < valof b"
    using lt assms
    by (simp add: fcompare_def is_nan_def is_infinity_def valof_def split: if_split_asm)
qed

lemma float_eq [simp]:
  assumes "is_finite a" "is_finite b"
  shows "a \<doteq> b \<longleftrightarrow> valof a = valof b"
proof
  assume *: "valof a = valof b"
  have "\<not> is_nan a" and "\<not> is_nan b" and "\<not> is_infinity a" and "\<not> is_infinity b"
    using assms float_distinct_finite by auto
  with * have "fcompare a b = Eq"
    by (auto simp add: is_infinity_def is_nan_def valof_def fcompare_def)
  then show "a \<doteq> b" by (auto simp: float_defs)
next
  assume "a \<doteq> b"
  then have eq: "fcompare a b = Eq"
    by (simp add: float_defs)
  have "\<not> is_nan a" and "\<not> is_nan b" and "\<not> is_infinity a" and "\<not> is_infinity b"
    using assms float_distinct_finite by auto
  then show "valof a = valof b"
    using eq assms
    by (simp add: fcompare_def is_nan_def is_infinity_def valof_def split: if_split_asm)
qed

lemma float_le [simp]:
  assumes "is_finite a" "is_finite b"
  shows "a \<le> b \<longleftrightarrow> valof a \<le> valof b"
proof -
  have "a \<le> b \<longleftrightarrow>  a < b \<or> a \<doteq> b"
    by (auto simp add: float_defs)
  then show ?thesis
    by (auto simp add: assms)
qed

text \<open>Reflexivity of equality for non-NaNs.\<close>
lemma float_eq_refl [simp]: "a \<doteq> a \<longleftrightarrow> \<not> is_nan a"
  by (auto simp: float_defs)

text \<open>Properties about Ordering.\<close>
lemma float_lt_trans: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite c \<Longrightarrow> a < b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  by (auto simp: le_trans)

lemma float_le_less_trans: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite c \<Longrightarrow> a \<le> b \<Longrightarrow> b < c \<Longrightarrow> a < c"
  by (auto simp: le_trans)

lemma float_le_trans: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite c \<Longrightarrow> a \<le> b \<Longrightarrow> b \<le> c \<Longrightarrow> a \<le> c"
  by (auto simp: le_trans)

lemma float_le_neg: "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> \<not> a < b \<longleftrightarrow> b \<le> a"
  by auto


text \<open>Properties about bounding.\<close>

lemma float_le_infinity [simp]: "\<not> is_nan a \<Longrightarrow> a \<le> plus_infinity"
  unfolding float_defs
  by auto

lemma zero_le_topfloat[simp]: "0 \<le> topfloat" "- 0 \<le> topfloat"
  unfolding float_defs
  by (auto simp: sign_simps divide_simps power_gt1_lemma)

lemma LENGTH_contr:
  "Suc 0 < LENGTH('e) \<Longrightarrow> 2 ^ LENGTH('e::len) \<le> Suc (Suc 0) \<Longrightarrow> False"
  by (metis le_antisym len_gt_0 n_less_equal_power_2 not_less_eq numeral_2_eq_2 one_le_numeral
      self_le_power)

lemma valof_topfloat: "valof (topfloat::('e, 'f)float) = largest TYPE(('e, 'f)float)"
  if "LENGTH('e) > 1"
  using that LENGTH_contr
  by (auto simp add: emax_eq largest_def divide_simps float_defs )

lemma float_frac_le: "fraction a \<le> 2^LENGTH('f) - 1"
  for a::"('e, 'f)float"
  unfolding float_defs
  using less_Suc_eq_le
  by transfer fastforce

lemma float_exp_le: "is_finite a \<Longrightarrow> exponent a \<le> emax TYPE(('e, 'f)float) - 1"
  for a::"('e, 'f)float"
  unfolding float_defs
  by auto

lemma float_sign_le: "(-1::real)^(sign a) = 1 \<or> (-1::real)^(sign a) = -1"
  by (metis neg_one_even_power neg_one_odd_power)

lemma exp_less: "a \<le> b \<Longrightarrow> (2::real)^a \<le> 2^b" for a b :: nat
  by auto

lemma div_less: "a \<le> b \<and> c > 0 \<Longrightarrow> a/c \<le> b/c" for a b c :: "'a::linordered_field"
  by (metis divide_le_cancel less_asym)

lemma finite_topfloat: "is_finite topfloat"
  unfolding float_defs
  by auto

lemmas float_leI = float_le[THEN iffD2]

lemma factor_minus: "x * a - x = x * (a - 1)"
  for x a::"'a::comm_semiring_1_cancel"
  by (simp add: algebra_simps)

lemma real_le_power_numeral_diff: "real a \<le> numeral b ^ n - 1 \<longleftrightarrow> a \<le> numeral b ^ n - 1"
  by (metis (mono_tags, lifting) of_nat_1 of_nat_diff of_nat_le_iff of_nat_numeral
      one_le_numeral one_le_power semiring_1_class.of_nat_power)

definition denormal_exponent::"('e, 'f)float itself \<Rightarrow> int" where
  "denormal_exponent x = 1 - (int (LENGTH('f)) + int (bias TYPE(('e, 'f)float)))"

definition normal_exponent::"('e, 'f)float \<Rightarrow> int" where
  "normal_exponent x = int (exponent x) - int (bias TYPE(('e, 'f)float)) - int (LENGTH('f))"

definition denormal_mantissa::"('e, 'f)float \<Rightarrow> int" where
  "denormal_mantissa x = (-1::int)^sign x * int (fraction x)"

definition normal_mantissa::"('e, 'f)float \<Rightarrow> int" where
  "normal_mantissa x = (-1::int)^sign x * (2^LENGTH('f) + int (fraction x))"

lemma unat_one_word_le: "unat a \<le> Suc 0" for a::"1 word"
  using unat_lt2p[of a]
  by auto

lemma one_word_le: "a \<le> 1" for a::"1 word"
  by (auto simp: word_le_nat_alt unat_one_word_le)

lemma sign_cases[case_names pos neg]:
  obtains "sign x = 0" | "sign x = 1"
proof cases
  assume "sign x = 0"
  then show ?thesis ..
next
  assume "sign x \<noteq> 0"
  have "sign x \<le> 1"
    by transfer (auto simp: unat_one_word_le)
  then have "sign x = 1" using \<open>sign x \<noteq> 0\<close>
    by auto
  then show ?thesis ..
qed

lemma is_infinity_cases:
  assumes "is_infinity x"
  obtains "x = plus_infinity" | "x = minus_infinity"
proof (cases rule: sign_cases[of x])
  assume "sign x = 0"
  then have "x = plus_infinity" using assms
    unfolding float_defs
    by transfer (auto simp: emax_def unat_eq_0)
  then show ?thesis ..
next
  assume "sign x = 1"
  then have "x = minus_infinity" using assms
    unfolding float_defs
    by transfer (auto simp: emax_def unat_eq_of_nat)
  then show ?thesis ..
qed

lemma is_zero_cases:
  assumes "is_zero x"
  obtains "x = 0" | "x = - 0"
proof (cases rule: sign_cases[of x])
  assume "sign x = 0"
  then have "x = 0" using assms
    unfolding float_defs
    by transfer (auto simp: emax_def unat_eq_0)
  then show ?thesis ..
next
  assume "sign x = 1"
  then have "x = minus_zero" using assms
    unfolding float_defs
    by transfer (auto simp: emax_def unat_eq_of_nat)
  then show ?thesis ..
qed

lemma minus_minus_float[simp]: "- (-f) = f" for f::"('e, 'f)float"
  by transfer auto

lemma sign_minus_float: "sign (-f) = (1 - sign f)" for f::"('e, 'f)float"
  by transfer (auto simp: unat_eq_1 one_word_le unat_sub)

lemma exponent_uminus[simp]: "exponent (- f) = exponent f" by transfer auto
lemma fraction_uminus[simp]: "fraction (- f) = fraction f" by transfer auto

lemma is_normal_minus_float[simp]: "is_normal (-f) = is_normal f" for f::"('e, 'f)float"
  by (auto simp: is_normal_def)

lemma is_denormal_minus_float[simp]: "is_denormal (-f) = is_denormal f" for f::"('e, 'f)float"
  by (auto simp: is_denormal_def)

lemma bitlen_normal_mantissa:
  "bitlen (abs (normal_mantissa x)) = Suc LENGTH('f)" for x::"('e, 'f)float"
proof -
  have "fraction x < 2 ^ LENGTH('f)"
    using float_frac_le[of x]
    by (metis One_nat_def Suc_pred le_imp_less_Suc pos2 zero_less_power)
  moreover have "- int (fraction x) \<le> 2 ^ LENGTH('f)"
    using negative_zle_0 order_trans zero_le_numeral zero_le_power by blast
  ultimately show ?thesis
    by (cases x rule: sign_cases)
      (auto simp: bitlen_le_iff_power bitlen_ge_iff_power nat_add_distrib abs_mult sign_simps
        add_nonneg_pos normal_mantissa_def intro!: antisym)
qed

lemma less_int_natI: "x < y" if "0 \<le> x" "nat x < nat y"
  using that by arith

lemma normal_exponent_bounds_int:
  "2 - 2 ^ (LENGTH('e) - 1) - int LENGTH('f) \<le> normal_exponent x"
  "normal_exponent x \<le> 2 ^ (LENGTH('e) - 1) - int LENGTH('f) - 1"
  if "is_normal x"
  for x::"('e, 'f)float"
  using that
  unfolding normal_exponent_def is_normal_def emax_eq bias_def
  by (auto simp del: zless_nat_conj intro!: less_int_natI
      simp: nat_add_distrib nat_mult_distrib nat_power_eq
      power_Suc[symmetric])

lemmas of_int_leI = of_int_le_iff[THEN iffD2]

lemma normal_exponent_bounds_real:
  "2 - 2 ^ (LENGTH('e) - 1) - real LENGTH('f) \<le> normal_exponent x"
  "normal_exponent x \<le> 2 ^ (LENGTH('e) - 1) - real LENGTH('f) - 1"
  if "is_normal x"
  for x::"('e, 'f)float"
  subgoal by (rule order_trans[OF _ of_int_leI[OF normal_exponent_bounds_int(1)[OF that]]]) auto
  subgoal by (rule order_trans[OF of_int_leI[OF normal_exponent_bounds_int(2)[OF that]]]) auto
  done

lemma float_eqI:
  "x = y" if "sign x = sign y" "fraction x = fraction y" "exponent x = exponent y"
  using that
  by transfer auto

lemma float_induct[induct type:float, case_names normal denormal neg zero infinity nan]:
  fixes a::"('e, 'f)float"
  assumes normal:
    "\<And>x. is_normal x \<Longrightarrow> valof x = normal_mantissa x * 2 powr normal_exponent x \<Longrightarrow> P x"
  assumes denormal:
    "\<And>x. is_denormal x \<Longrightarrow>
      valof x = denormal_mantissa x * 2 powr denormal_exponent TYPE(('e, 'f)float) \<Longrightarrow>
      P x"
  assumes zero: "P 0" "P minus_zero"
  assumes infty: "P plus_infinity" "P minus_infinity"
  assumes nan: "\<And>x. is_nan x \<Longrightarrow> P x"
  shows "P a"
proof -
  from float_cases[of a]
  consider "is_nan a" | "is_infinity a" | "is_normal a" | "is_denormal a" | "is_zero a" by blast
  then show ?thesis
  proof cases
    case 1
    then show ?thesis by (rule nan)
  next
    case 2
    then consider "a = plus_infinity" | "a = minus_infinity" by (rule is_infinity_cases)
    then show ?thesis
      by cases (auto intro: infty)
  next
    case hyps: 3
    from hyps have "valof a = normal_mantissa a * 2 powr normal_exponent a"
      by (cases a rule: sign_cases)
        (auto simp: valof_eq normal_mantissa_def normal_exponent_def is_normal_def
          powr_realpow[symmetric] powr_diff powr_add divide_simps algebra_simps)
    from hyps this show ?thesis
      by (rule normal)
  next
    case hyps: 4
    from hyps have "valof a = denormal_mantissa a * 2 powr denormal_exponent TYPE(('e, 'f)float)"
      by (cases a rule: sign_cases)
        (auto simp: valof_eq denormal_mantissa_def denormal_exponent_def is_denormal_def
          powr_realpow[symmetric] powr_diff powr_add divide_simps algebra_simps)
    from hyps this show ?thesis
      by (rule denormal)
  next
    case 5
    then consider "a = 0" | "a = minus_zero" by (rule is_zero_cases)
    then show ?thesis
      by cases (auto intro: zero)
  qed
qed

lemma infinite_infinity[simp]: "\<not> is_finite plus_infinity" "\<not> is_finite minus_infinity"
  by (auto simp: is_finite_def is_normal_def infinity_simps is_denormal_def is_zero_def)

lemma nan_not_finite[simp]: "is_nan x \<Longrightarrow> \<not> is_finite x"
  using float_distinct_finite(1) by blast

lemma valof_nonneg:
  "valof x \<ge> 0" if "sign x = 0" for x::"('e, 'f)float"
  by (auto simp: valof_eq that)

lemma valof_nonpos:
  "valof x \<le> 0" if "sign x = 1" for x::"('e, 'f)float"
  using that
  by (auto simp: valof_eq is_finite_def)

lemma real_le_intI: "x \<le> y" if "floor x \<le> floor y" "x \<in> \<int>" for x y::real
  using that(2,1)
  by (induction rule: Ints_induct) (auto elim!: Ints_induct simp: le_floor_iff)

lemma real_of_int_le_2_powr_bitlenI:
  "real_of_int x \<le> 2 powr n - 1" if "bitlen (abs x) \<le> m" "m \<le> n"
proof -
  have "real_of_int x \<le> abs (real_of_int x)" by simp
  also have "\<dots> < 2 powr (bitlen (abs x))"
    by (rule abs_real_le_2_powr_bitlen)
  finally have "real_of_int x \<le> 2 powr (bitlen (abs x)) - 1"
    by (auto simp: powr_real_of_int bitlen_nonneg intro!: real_le_intI)
  also have "\<dots> \<le> 2 powr m - 1"
    by (simp add: that)
  also have "\<dots> \<le> 2 powr n - 1"
    by (simp add: that)
  finally show ?thesis .
qed

lemma largest_eq:
  "largest TYPE(('e, 'f)float) =
    (2 ^ (LENGTH('f) + 1) - 1) * 2 powr real_of_int (2 ^ (LENGTH('e) - 1) - int LENGTH('f) - 1)"
proof -
  have "2 ^ LENGTH('e) - 1 - 1 = (2::nat) ^ LENGTH('e) - 2"
    by arith
  then have "largest TYPE(('e, 'f)float) =
    (2 ^ (LENGTH('f) + 1) - 1) *
    2 powr (real (2 ^ LENGTH('e) - 2) + 1 - real (2 ^ (LENGTH('e) - 1)) - LENGTH('f))"
    unfolding largest_def emax_eq bias_def
    by (auto simp: largest_def powr_realpow[symmetric]
        powr_minus divide_simps algebra_simps powr_diff powr_add)
  also
  have "2 ^ LENGTH('e) \<ge> (2::nat)"
    by (simp add: self_le_power)
  then have "(real (2 ^ LENGTH('e) - 2) + 1 - real (2 ^ (LENGTH('e) - 1)) - LENGTH('f)) =
    (real (2 ^ LENGTH('e)) - 2 ^ (LENGTH('e) - 1) - LENGTH('f)) - 1"
    by auto
  also have "real (2 ^ LENGTH('e)) = 2 ^ LENGTH('e)" by auto
  also have "(2 ^ LENGTH('e) - 2 ^ (LENGTH('e) - 1) - real LENGTH('f) - 1) =
    real_of_int ((2 ^ (LENGTH('e) - 1) - int (LENGTH('f)) - 1))"
    by (simp, subst power_Suc[symmetric], simp)
  finally show ?thesis by simp
qed

lemma bitlen_denormal_mantissa:
  "bitlen (abs (denormal_mantissa x)) \<le> LENGTH('f)" for x::"('e, 'f)float"
proof -
  have "fraction x < 2 ^ LENGTH('f)"
    using float_frac_le[of x]
    by (metis One_nat_def Suc_pred le_imp_less_Suc pos2 zero_less_power)
  moreover have "- int (fraction x) \<le> 2 ^ LENGTH('f)"
    using negative_zle_0 order_trans zero_le_numeral zero_le_power by blast
  ultimately show ?thesis
    by (cases x rule: sign_cases)
      (auto simp: bitlen_le_iff_power nat_add_distrib abs_mult sign_simps
        add_nonneg_pos denormal_mantissa_def intro!: antisym)
qed

lemma float_le_topfloat:
  fixes a::"('e, 'f)float"
  assumes "is_finite a" "LENGTH('e) > 1"
  shows "a \<le> topfloat"
  using assms(1)
proof (induction a rule: float_induct)
  case (normal x)
  note normal(2)
  also have "real_of_int (normal_mantissa x) * 2 powr real_of_int (normal_exponent x) \<le>
    (2 powr (LENGTH('f) + 1) - 1) * 2 powr (2 ^ (LENGTH('e) - 1) - int LENGTH('f) - 1)"
    using normal_exponent_bounds_real(2)[OF \<open>is_normal x\<close>]
    by (auto intro!: mult_mono real_of_int_le_2_powr_bitlenI
        simp: bitlen_normal_mantissa powr_realpow[symmetric] ge_one_powr_ge_zero)
  also have "\<dots> = largest TYPE(('e, 'f) IEEE.float)"
    unfolding largest_eq
    by (auto simp: powr_realpow powr_add)
  also have "\<dots> = valof (topfloat::('e, 'f) float)"
    using assms
    by (simp add: valof_topfloat)
  finally show ?case
    by (intro float_leI normal finite_topfloat)
next
  case (denormal x)
  note denormal(2)
  also
  have "3 \<le> 2 powr (1 + real (LENGTH('e) - Suc 0))"
  proof -
    have "3 \<le> 2 powr (2::real)" by simp
    also have "\<dots> \<le> 2 powr (1 + real (LENGTH('e) - Suc 0))"
      using assms
      by (subst powr_le_cancel_iff) auto
    finally show ?thesis .
  qed
  then have "real_of_int (denormal_mantissa x) * 2 powr real_of_int (denormal_exponent TYPE(('e, 'f)float)) \<le>
    (2 powr (LENGTH('f) + 1) - 1) * 2 powr (2 ^ (LENGTH('e) - 1) - int LENGTH('f) - 1)"
    using bitlen_denormal_mantissa[of x]
    by (auto intro!: mult_mono real_of_int_le_2_powr_bitlenI
        simp: bitlen_normal_mantissa powr_realpow[symmetric] ge_one_powr_ge_zero
        denormal_exponent_def bias_def powr_mult_base)
  also have "\<dots> \<le> largest TYPE(('e, 'f) IEEE.float)"
    unfolding largest_eq
    by (rule mult_mono)
      (auto simp: powr_realpow powr_add power_Suc[symmetric] simp del: power_Suc)
  also have "\<dots> = valof (topfloat::('e, 'f) float)"
    using assms
    by (simp add: valof_topfloat)
  finally show ?case
    by (intro float_leI denormal finite_topfloat)
qed auto

lemma float_val_le_largest:
  "valof a \<le> largest TYPE(('e, 'f)float)"
  if "is_finite a" "LENGTH('e) > 1"
  for a::"('e, 'f)float"
  by (metis that finite_topfloat float_le float_le_topfloat valof_topfloat)

lemma float_val_lt_threshold:
  "valof a < threshold TYPE(('e, 'f)float)"
  if "is_finite a" "LENGTH('e) > 1"
  for a::"('e, 'f)float"
proof -
  have "valof a \<le> largest TYPE(('e, 'f)float)"
    by (rule float_val_le_largest [OF that])
  also have "\<dots> < threshold TYPE(('e, 'f)float)"
    by (auto simp: largest_def threshold_def divide_simps)
  finally show ?thesis .
qed


subsection \<open>Algebraic properties about basic arithmetic\<close>

text \<open>Commutativity of addition.\<close>
lemma
  assumes "is_finite a" "is_finite b"
  shows float_plus_comm_eq: "a + b = b + a"
    and float_plus_comm: "is_finite (a + b) \<Longrightarrow> (a + b) \<doteq> (b + a)"
proof -
  have "\<not> is_nan a" and "\<not> is_nan b" and "\<not> is_infinity a" and "\<not> is_infinity b"
    using assms by (auto simp: finite_nan finite_infinity)
  then show "a + b = b + a"
    by (simp add: float_defs fadd_def plus_float_def add.commute)
  then show "is_finite (a + b) \<Longrightarrow> (a + b) \<doteq> (b + a)"
    by (metis float_eq)
qed

text \<open>The floating-point number a falls into the same category as the negation of \<open>a\<close>.\<close>
lemma is_zero_uminus[simp]: "is_zero (- a) \<longleftrightarrow> is_zero a"
  by (simp add: is_zero_def)

lemma is_infinity_uminus [simp]: "is_infinity (- a) = is_infinity a"
  by (simp add: is_infinity_def)

lemma is_finite_uminus[simp]: "is_finite (- a) \<longleftrightarrow> is_finite a"
  by (simp add: is_finite_def)

lemma is_nan_uminus[simp]: "is_nan (- a) \<longleftrightarrow> is_nan a"
  by (simp add: is_nan_def)

text \<open>The sign of a and the sign of a's negation is different.\<close>
lemma float_neg_sign: "(sign a) \<noteq> (sign (- a))"
  by (cases a rule: sign_cases) (auto simp: sign_minus_float)

lemma float_neg_sign1: "sign a = sign (- b) \<longleftrightarrow> sign a \<noteq> sign b"
  by (metis float_neg_sign sign_cases)

lemma valof_uminus:
  assumes "is_finite a"
  shows "valof (- a) = - valof a" (is "?L = ?R")
  by (cases a rule: sign_cases)  (auto simp: valof_eq sign_minus_float)


text \<open>Showing \<open>a + (- b) = a - b\<close>.\<close>
lemma float_neg_add:
  "is_finite a \<Longrightarrow> is_finite b \<Longrightarrow> is_finite (a - b) \<Longrightarrow> valof a + valof (- b) = valof a - valof b"
  by (simp add: valof_uminus)

lemma float_plus_minus:
  assumes "is_finite a" "is_finite b" "is_finite (a - b)"
  shows "(a + - b) \<doteq> (a - b)"
proof -
  have nab: "\<not> is_nan a" "\<not> is_nan (- b)" "\<not> is_infinity a" "\<not> is_infinity (-  b)"
    using assms by (auto simp: finite_nan finite_infinity)
  have "a - b = (zerosign
        (if is_zero a \<and> is_zero b \<and> sign a \<noteq> sign b then (sign a) else 0)
        (round To_nearest (valof a - valof b)))"
    using nab
    by (auto simp: minus_float_def fsub_def)
  also have "\<dots> =
    (zerosign
        (if is_zero a \<and> is_zero (- b) \<and> sign a = sign (- b) then sign a else 0)
        (round To_nearest (valof a + valof (- b))))"
    using assms
    by (simp add: float_neg_sign1 float_neg_add)
  also have "\<dots> = a + - b"
    using nab by (auto simp: float_defs fadd_def plus_float_def)
  finally show ?thesis
    using assms by (metis float_eq)
qed

lemma finite_bottomfloat: "is_finite bottomfloat"
  by (simp add: finite_topfloat)

lemma bottomfloat_eq_m_largest: "valof (bottomfloat::('e, 'f)float) = - largest TYPE(('e, 'f)float)"
  if "LENGTH('e) > 1"
  using that
  by (auto simp: valof_topfloat valof_uminus finite_topfloat)

lemma float_val_ge_bottomfloat: "valof a \<ge> valof (bottomfloat::('e, 'f)float)"
  if "LENGTH('e) > 1" "is_finite a"
  for a::"('e,'f)float"
proof -
  have "- a \<le> topfloat"
    using that
    by (auto intro: float_le_topfloat)
  then show ?thesis
    using that
    by (auto simp: valof_uminus finite_topfloat)
qed

lemma float_ge_bottomfloat: "is_finite a \<Longrightarrow> a \<ge> bottomfloat"
  if "LENGTH('e) > 1" "is_finite a"
  for a::"('e,'f)float"
  by (metis finite_bottomfloat float_le float_val_ge_bottomfloat that)

lemma float_val_ge_largest:
  fixes a::"('e,'f)float"
  assumes "LENGTH('e) > 1" "is_finite a"
  shows "valof a \<ge> - largest TYPE(('e,'f)float)"
proof -
  have "- largest TYPE(('e,'f)float) = valof (bottomfloat::('e,'f)float)"
    using assms
    by (simp add: bottomfloat_eq_m_largest)
  also have "\<dots> \<le> valof a"
    using assms by (simp add: float_val_ge_bottomfloat)
  finally show ?thesis .
qed

lemma float_val_gt_threshold:
  fixes a::"('e,'f)float"
  assumes "LENGTH('e) > 1" "is_finite a"
  shows "valof a > - threshold TYPE(('e,'f)float)"
proof -
  have largest: "valof a \<ge> -largest TYPE(('e,'f)float)"
    using assms by (metis float_val_ge_largest)
  then have "-largest TYPE(('e,'f)float) > - threshold TYPE(('e,'f)float)"
    by (auto simp: bias_def threshold_def largest_def divide_simps)
  then show ?thesis
    by (metis largest less_le_trans)
qed

text \<open>Showing \<open>abs (- a) = abs a\<close>.\<close>
lemma float_abs [simp]: "\<not> is_nan a \<Longrightarrow> abs (- a) = abs a"
  by (metis IEEE.abs_float_def float_neg_sign1 minus_minus_float zero_simps(1))

lemma neg_zerosign: "- (zerosign s a) = zerosign (1 - s) (- a)"
  by (auto simp: zerosign_def)


subsection \<open>Properties about Rounding Errors\<close>

definition error :: "('e, 'f)float itself \<Rightarrow> real \<Rightarrow> real"
  where "error _ x = valof (round To_nearest x::('e, 'f)float) - x"

lemma bound_at_worst_lemma:
  fixes a::"('e, 'f)float"
  assumes threshold: "\<bar>x\<bar> < threshold TYPE(('e, 'f)float)"
  assumes finite: "is_finite a"
  shows "\<bar>valof (round To_nearest x::('e, 'f)float) - x\<bar> \<le> \<bar>valof a - x\<bar>"
proof -
  have *: "(round To_nearest x::('e,'f)float) =
      closest valof (\<lambda>a. even (fraction a)) {a. is_finite a} x"
    using threshold finite
    by auto
  have "is_closest (valof) {a. is_finite a} x (round To_nearest x::('e,'f)float)"
    using is_finite_nonempty
    unfolding *
    by (intro closest_is_closest) auto
  then show ?thesis
    using finite is_closest_def by (metis mem_Collect_eq)
qed

lemma error_at_worst_lemma:
  fixes a::"('e, 'f)float"
  assumes threshold: "\<bar>x\<bar> < threshold TYPE(('e, 'f)float)"
    and "is_finite a"
  shows "\<bar>error TYPE(('e, 'f)float) x\<bar> \<le> \<bar>valof a - x\<bar> "
  unfolding error_def
  by (rule bound_at_worst_lemma; fact)

lemma error_is_zero [simp]:
  fixes a::"('e, 'f)float"
  assumes "is_finite a" "1 < LENGTH('e)"
  shows "error TYPE(('e, 'f)float) (valof a) = 0"
proof -
  have "\<bar>valof a\<bar> < threshold TYPE(('e, 'f)float)"
    by (metis abs_less_iff minus_less_iff float_val_gt_threshold float_val_lt_threshold assms)
  then show ?thesis
    by (metis abs_le_zero_iff abs_zero diff_self error_at_worst_lemma assms(1))
qed

lemma is_finite_zerosign[simp]: "is_finite (zerosign s a) \<longleftrightarrow> is_finite a"
  by (auto simp: zerosign_def is_finite_def)

lemma is_finite_closest: "is_finite (closest (v::_\<Rightarrow>real) p {a. is_finite a} x)"
  using closest_is_closest[OF is_finite_nonempty, of v x p]
  by (auto simp: is_closest_def)

lemma defloat_float_zerosign_round_finite:
  assumes threshold: "\<bar>x\<bar> < threshold TYPE(('e, 'f)float)"
  shows "is_finite (zerosign s (round To_nearest x::('e, 'f)float))"
proof -
  have "(round To_nearest x::('e, 'f)float) =
      (closest valof (\<lambda>a. even (fraction a)) {a. is_finite a} x)"
    using threshold by (metis (full_types) abs_less_iff leD le_minus_iff round.simps(1))
  then have "is_finite (round To_nearest x::('e, 'f)float)"
    by (metis is_finite_closest)
  then show ?thesis
    using is_finite_zerosign by auto
qed

lemma valof_zero[simp]: "valof 0 = 0" "valof minus_zero = 0"
  by (auto simp add: zerosign_def valof_eq zero_simps)

lemma signzero_zero:
  "is_zero a \<Longrightarrow> valof (zerosign s a) = 0"
  by (auto simp add: zerosign_def)

lemma val_zero: "is_zero a \<Longrightarrow> valof a = 0"
  by (cases a rule: is_zero_cases) auto

lemma float_add:
  fixes a b::"('e, 'f)float"
  assumes "is_finite a"
    and "is_finite b"
    and threshold: "\<bar>valof a + valof b\<bar> < threshold TYPE(('e, 'f)float)"
  shows finite_float_add: "is_finite (a + b)"
    and error_float_add:  "valof (a + b) = valof a + valof b + error TYPE(('e, 'f)float) (valof a + valof b)"
proof -
  have "\<not> is_nan a" and "\<not> is_nan b" and "\<not> is_infinity a" and "\<not> is_infinity b"
    using assms float_distinct_finite by auto
  then have ab: "(a + b) =
    (zerosign
      (if is_zero a \<and> is_zero b \<and> sign a = sign b then (sign a) else 0)
      (round To_nearest (valof a + valof b)))"
    using assms by (auto simp add: float_defs fadd_def plus_float_def)
  then show "is_finite ((a + b))"
    by (metis threshold defloat_float_zerosign_round_finite)
  have val_ab: "valof (a + b) =
    valof (zerosign
      (if is_zero a \<and> is_zero b \<and> sign a = sign b then (sign a) else 0)
      (round To_nearest (valof a + valof b)::('e, 'f)float))"
    by (auto simp: ab is_infinity_def is_nan_def valof_def)
  show "valof (a + b) = valof a + valof b + error TYPE(('e, 'f)float) (valof a + valof b)"
  proof (cases "is_zero (round To_nearest (valof a + valof b)::('e, 'f)float)")
    case True
    have "valof a + valof b + error TYPE(('e, 'f)float) (valof a + valof b) =
        valof (round To_nearest (valof a + valof b)::('e, 'f)float)"
      unfolding error_def
      by simp
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False
    then show ?thesis
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed

lemma float_sub:
  fixes a b::"('e, 'f)float"
  assumes "is_finite a"
    and "is_finite b"
    and threshold: "\<bar>valof a - valof b\<bar> < threshold TYPE(('e, 'f)float)"
  shows finite_float_sub: "is_finite (a - b)"
    and error_float_sub: "valof (a - b) = valof a - valof b + error TYPE(('e, 'f)float) (valof a - valof b)"
proof -
  have "\<not> is_nan a" and "\<not> is_nan b" and "\<not> is_infinity a" and "\<not> is_infinity b"
    using assms by (auto simp: finite_nan finite_infinity)
  then have ab: "a - b =
    (zerosign
      (if is_zero a \<and> is_zero b \<and> sign a \<noteq> sign b then sign a else 0)
      (round To_nearest (valof a - valof b)))"
    using assms by (auto simp add: float_defs fsub_def minus_float_def)
  then show "is_finite (a - b)"
   by (metis threshold defloat_float_zerosign_round_finite)
  have val_ab: "valof (a - b) =
    valof (zerosign
      (if is_zero a \<and> is_zero b \<and> sign a \<noteq> sign b then sign a else 0)
      (round To_nearest (valof a - valof b)::('e, 'f)float))"
    by (auto simp: ab is_infinity_def is_nan_def valof_def)
  show "valof (a - b) = valof a - valof b + error TYPE(('e, 'f)float) (valof a - valof b)"
  proof (cases "is_zero (round To_nearest (valof a - valof b)::('e, 'f)float)")
    case True
    have "valof a - valof b + error TYPE(('e, 'f)float) (valof a - valof b) =
        valof (round To_nearest (valof a - valof b)::('e, 'f)float)"
      unfolding error_def by simp
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False
    then show ?thesis
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed

lemma float_mul:
  fixes a b::"('e, 'f)float"
  assumes "is_finite a"
    and "is_finite b"
    and threshold: "\<bar>valof a * valof b\<bar> < threshold TYPE(('e, 'f)float)"
  shows finite_float_mul: "is_finite (a * b)"
    and error_float_mul: "valof (a * b) = valof a * valof b + error TYPE(('e, 'f)float) (valof a * valof b)"
proof -
  have non: "\<not> is_nan a" "\<not> is_nan b" "\<not> is_infinity a" "\<not> is_infinity b"
    using assms float_distinct_finite by auto
  then have ab: "a * b =
    (zerosign (of_bool (sign a \<noteq> sign b))
      (round To_nearest (valof a * valof b)::('e, 'f)float))"
    using assms by (auto simp: float_defs fmul_def times_float_def)
  then show "is_finite (a * b)"
    by (metis threshold defloat_float_zerosign_round_finite)
  have val_ab: "valof (a * b) =
      valof (zerosign (of_bool (sign a \<noteq> sign b))
        (round To_nearest (valof a * valof b)::('e, 'f)float))"
    by (auto simp: ab float_defs of_bool_def)
  show "valof (a * b) = valof a * valof b + error TYPE(('e, 'f)float) (valof a * valof b)"
  proof (cases "is_zero (round To_nearest (valof a * valof b)::('e, 'f)float)")
    case True
    have "valof a * valof b + error TYPE(('e, 'f)float)  (valof a * valof b) =
        valof (round To_nearest (valof a * valof b)::('e, 'f)float)"
      unfolding error_def
      by simp
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False then show ?thesis
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed

lemma float_div:
  fixes a b::"('e, 'f)float"
  assumes "is_finite a"
    and "is_finite b"
    and not_zero: "\<not> is_zero b"
    and threshold: "\<bar>valof a / valof b\<bar> < threshold TYPE(('e, 'f)float)"
  shows finite_float_div: "is_finite (a / b)"
    and error_float_div: "valof (a / b) = valof a / valof b + error TYPE(('e, 'f)float) (valof a / valof b)"
proof -
  have ab: "a / b =
    (zerosign (of_bool (sign a \<noteq> sign b))
      (round To_nearest (valof a / valof b)))"
     using assms
     by (simp add: divide_float_def fdiv_def finite_infinity finite_nan not_zero float_defs [symmetric])
  then show "is_finite (a / b)"
    by (metis threshold defloat_float_zerosign_round_finite)
  have val_ab: "valof (a / b) =
      valof (zerosign (of_bool (sign a \<noteq> sign b))
        (round To_nearest (valof a / valof b))::('e, 'f)float)"
    by (auto simp: ab float_defs of_bool_def)
  show "valof (a / b) = valof a / valof b + error TYPE(('e, 'f)float)  (valof a / valof b)"
  proof (cases "is_zero (round To_nearest (valof a / valof b)::('e, 'f)float)")
    case True
    have "valof a / valof b + error TYPE(('e, 'f)float) (valof a / valof b) =
        valof (round To_nearest (valof a / valof b)::('e, 'f)float)"
      unfolding error_def
      by simp
    then show ?thesis
      by (metis True signzero_zero val_zero val_ab)
  next
    case False then show ?thesis
      by (metis ab add.commute eq_diff_eq' error_def zerosign_def)
  qed
qed

lemma valof_one[simp]: "valof (1::('e, 'f)float) = (if LENGTH('e) \<le> 1 then 0 else 1)"
  by transfer (auto simp: bias_def unat_sub word_1_le_power p2_eq_1)

end
