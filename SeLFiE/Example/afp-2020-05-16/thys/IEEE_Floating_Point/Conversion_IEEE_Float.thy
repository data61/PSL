(* Author: Fabian Hellauer
           Fabian Immler
*)
theory Conversion_IEEE_Float
  imports
    "HOL-Library.Float"
    IEEE_Properties
    "HOL-Library.Code_Target_Numeral"
begin

definition "of_finite (x::('e, 'f)float) =
  (if is_normal x then (Float (normal_mantissa x) (normal_exponent x))
    else if is_denormal x then (Float (denormal_mantissa x) (denormal_exponent TYPE(('e, 'f)float)))
    else 0)"

lemma float_val_of_finite: "is_finite x \<Longrightarrow> of_finite x = valof x"
  by (induction x) (auto simp: normal_imp_not_denormal of_finite_def)

definition is_normal_Float::"('e, 'f)float itself \<Rightarrow> Float.float \<Rightarrow> bool" where
  "is_normal_Float x f \<longleftrightarrow>
    mantissa f \<noteq> 0 \<and>
    bitlen \<bar>mantissa f\<bar> \<le> fracwidth x + 1 \<and>
    - int (bias x) - bitlen \<bar>mantissa f\<bar> + 1 < Float.exponent f \<and>
    Float.exponent f < 2^(LENGTH('e)) - bitlen \<bar>mantissa f\<bar> - bias x"

definition is_denormal_Float::"('e, 'f)float itself \<Rightarrow> Float.float \<Rightarrow> bool" where
  "is_denormal_Float x f \<longleftrightarrow>
    mantissa f \<noteq> 0 \<and>
    bitlen \<bar>mantissa f\<bar> \<le> 1 - Float.exponent f - int (bias x) \<and>
    1 - 2^(LENGTH('e) - 1) - int LENGTH('f) < Float.exponent f"

lemmas is_denormal_FloatD =
  is_denormal_Float_def[THEN iffD1, THEN conjunct1]
  is_denormal_Float_def[THEN iffD1, THEN conjunct2]

definition is_finite_Float::"('e, 'f)float itself \<Rightarrow> Float.float \<Rightarrow> bool" where
  "is_finite_Float x f \<longleftrightarrow> is_normal_Float x f \<or> is_denormal_Float x f \<or> f = 0"

lemma is_finite_Float_eq:
  "is_finite_Float TYPE(('e, 'f)float) f \<longleftrightarrow>
    (let e = Float.exponent f; bm = bitlen (abs (mantissa f))
    in bm \<le> Suc LENGTH('f) \<and>
     bm \<le> 2 ^ (LENGTH('e) - 1) - e \<and>
     1 - 2 ^ (LENGTH('e) - 1) - int LENGTH('f) < e)"
proof -
  have *: "(2::int) ^ (LENGTH('e) - Suc 0) - 1 < 2 ^ LENGTH('e)"
    by (metis Suc_1 diff_le_self lessI linorder_not_less one_less_numeral_iff
        power_strict_increasing_iff zle_diff1_eq)
  have **: "1 - 2 ^ (LENGTH('e) - Suc 0) < int LENGTH('f)"
    by (smt len_gt_0 of_nat_0_less_iff zero_less_power)
  have ***: "2 ^ (LENGTH('e) - 1) + 1 =
    2 ^ LENGTH('e) - int (bias TYPE(('e, 'f) IEEE.float))"
    by (simp add: bias_def power_Suc[symmetric])
  have rewr: "x \<le> 2 ^ n - e \<longleftrightarrow> x + e < 2 ^ n + 1" for x::int and n e
    by auto
  show ?thesis
    unfolding *** rewr
    using * **
    unfolding is_finite_Float_def is_normal_Float_def is_denormal_Float_def
    by (auto simp: Let_def bias_def mantissa_eq_zero_iff
        intro: le_less_trans[OF add_right_mono])
qed

lift_definition normal_of_Float :: "Float.float \<Rightarrow> ('e, 'f)float"
  is "\<lambda>x. let m = mantissa x; e = Float.exponent x in
    (if m > 0 then 0 else 1,
      word_of_int (e + int (bias TYPE(('e, 'f)float)) + bitlen \<bar>m\<bar> - 1),
      word_of_int (\<bar>m\<bar> * 2 ^ (Suc LENGTH('f) - nat (bitlen \<bar>m\<bar>)) - 2 ^ (LENGTH('f))))"
  .

lemma sign_normal_of_Float:"sign (normal_of_Float x) = (if x > 0 then 0 else 1)"
  by transfer (auto simp: Let_def mantissa_pos_iff)

lemma uints_bitlen_eq: "uints n = {i. 0 \<le> i \<and> bitlen i \<le> n}"
  by (auto simp: uints_num bitlen_le_iff_power)

lemma uint_word_of_int_bitlen_eq:
  "uint (word_of_int x::'a::len0 word) = x" if "bitlen x \<le> LENGTH('a)" "x \<ge> 0"
  by (subst word_uint.Abs_inverse) (simp_all add: uints_bitlen_eq that)

lemma fraction_normal_of_Float:"fraction (normal_of_Float x::('e, 'f)float) =
  (nat \<bar>mantissa x\<bar> * 2 ^ (Suc LENGTH('f) - nat (bitlen \<bar>mantissa x\<bar>)) - 2 ^ LENGTH('f))"
  if "is_normal_Float TYPE(('e, 'f)float) x"
proof -
  from that have bmp: "bitlen \<bar>mantissa x\<bar> > 0"
    by (metis abs_of_nonneg bitlen_bounds bitlen_def is_normal_Float_def nat_code(2) of_nat_0_le_iff
        power.simps(1) zabs_less_one_iff zero_less_abs_iff)
  have mless: "\<bar>mantissa x\<bar> < 2 ^ nat (bitlen \<bar>mantissa x\<bar>)"
    using bitlen_bounds by force
  have lem: "2 ^ nat (bitlen \<bar>mantissa x\<bar> - 1) \<le> \<bar>mantissa x\<bar>"
    using bitlen_bounds is_normal_Float_def that zero_less_abs_iff by blast
  from that have nble: "nat (bitlen \<bar>mantissa x\<bar>) \<le> Suc LENGTH('f)"
    using bitlen_bounds by (auto simp: is_normal_Float_def)
  have nn: "0 \<le> \<bar>mantissa x\<bar> * 2 ^ (Suc LENGTH('f) - nat (bitlen \<bar>mantissa x\<bar>)) - 2 ^ LENGTH('f)"
    apply (rule add_le_imp_le_diff)
    apply (rule order_trans[rotated])
     apply (rule mult_right_mono)
      apply (rule lem, force)
    unfolding power_add[symmetric]
    using nble bmp
    by (auto)
  have "\<bar>mantissa x\<bar> * 2 ^ (Suc LENGTH('f) - nat (bitlen \<bar>mantissa x\<bar>)) < 2 * 2 ^ LENGTH('f)"
    apply (rule less_le_trans)
     apply (rule mult_strict_right_mono)
      apply (rule mless)
     apply force
    unfolding power_add[symmetric] power_Suc[symmetric]
    apply (rule power_increasing)
    using nble
    by auto
  then have "bitlen (\<bar>mantissa x\<bar> * 2 ^ (Suc LENGTH('f) - nat (bitlen \<bar>mantissa x\<bar>)) - 2 ^ LENGTH('f))
    \<le> int LENGTH('f)"
    unfolding bitlen_le_iff_power
    by simp
  then show ?thesis
    apply (transfer fixing: x)
    unfolding Let_def split_beta' fst_conv snd_conv uint_nat[symmetric] unat_def
    using nn
    by (subst uint_word_of_int_bitlen_eq)
      (auto simp: nat_mult_distrib nat_diff_distrib nat_power_eq)
qed

lemma exponent_normal_of_Float:"exponent (normal_of_Float x::('e, 'f)float) =
  nat (Float.exponent x + (bias TYPE(('e, 'f)float)) + bitlen \<bar>mantissa x\<bar> - 1)"
  if "is_normal_Float TYPE(('e, 'f)float) x"
  using that
  by (transfer fixing: x)
    (auto simp: is_normal_Float_def bitlen_le_iff_power uint_word_of_int_bitlen_eq Let_def
      uint_nat[symmetric] unat_def)

lift_definition denormal_of_Float :: "Float.float \<Rightarrow> ('e, 'f)float"
  is "\<lambda>x. let m = mantissa x; e = Float.exponent x in
  (if m \<ge> 0 then 0 else 1, 0,
    word_of_int (\<bar>m\<bar> * 2 ^ nat (e + bias TYPE(('e, 'f)float) + fracwidth TYPE(('e, 'f)float) - 1)))"
  .

lemma sign_denormal_of_Float:"sign (denormal_of_Float x) = (if x \<ge> 0 then 0 else 1)"
  by transfer (auto simp: Let_def mantissa_nonneg_iff)

lemma exponent_denormal_of_Float:"exponent (denormal_of_Float x::('e, 'f)float) = 0"
  by (transfer fixing: x) (auto simp: Let_def)

lemma fraction_denormal_of_Float:"fraction (denormal_of_Float x::('e, 'f)float) =
  (nat \<bar>mantissa x\<bar> * 2 ^ nat (Float.exponent x + bias TYPE(('e, 'f)float) + LENGTH('f) - 1))"
  if "is_denormal_Float TYPE(('e, 'f)float) x"
proof -
  have mless: "\<bar>mantissa x\<bar> < 2 ^ nat (bitlen \<bar>mantissa x\<bar>)"
    using bitlen_bounds by force
  have *: "nat (bitlen \<bar>mantissa x\<bar>) +
    nat (Float.exponent x + (2 ^ (LENGTH('e) - Suc 0) + int LENGTH('f)) - 2)
    \<le> LENGTH('f)"
    using that
    by (auto simp: is_denormal_Float_def nat_diff_distrib' le_diff_conv
        bitlen_nonneg nat_le_iff bias_def nat_add_distrib[symmetric])
  have "\<bar>mantissa x\<bar> *  2 ^ nat (Float.exponent x + int (bias TYPE(('e, 'f)float)) +
    LENGTH('f) - 1) < 2 ^ LENGTH('f)"
    apply (rule less_le_trans)
     apply (rule mult_strict_right_mono)
      apply (rule mless, force)
    unfolding power_add[symmetric] power_Suc[symmetric]
    apply (rule power_increasing)
     apply (auto simp: bias_def)
    using that *
    by (auto simp: is_denormal_Float_def algebra_simps)
  then show ?thesis
    apply (transfer fixing: x)
    unfolding Let_def split_beta' fst_conv snd_conv uint_nat[symmetric] unat_def
    apply (subst uint_word_of_int_bitlen_eq)
    unfolding bitlen_le_iff_power
    by (auto simp: nat_mult_distrib)
qed

definition of_finite_Float :: "Float.float \<Rightarrow> ('e, 'f) float" where
  "of_finite_Float x = (if is_normal_Float TYPE(('e, 'f)float) x then normal_of_Float x
    else if is_denormal_Float TYPE(('e, 'f)float) x then denormal_of_Float x
    else 0)"

lemma valof_normal_of_Float: "valof (normal_of_Float x::('e, 'f)float) = x"
  if "is_normal_Float TYPE(('e, 'f)float) x"
proof -
  have "valof (normal_of_Float x::('e, 'f)float) =
    (- 1) ^ sign (normal_of_Float x::('e, 'f)float) *
    ((1 + real (nat \<bar>mantissa x\<bar> * 2 ^ (Suc LENGTH('f) - nat (bitlen \<bar>mantissa x\<bar>)) - 2 ^ LENGTH('f)) / 2 ^ LENGTH('f)) *
      2 powr (bitlen \<bar>mantissa x\<bar> - 1)) *
    2 powr Float.exponent x"
    (is "_ = ?s * ?m * ?e")
    using that
    by (auto simp: is_normal_Float_def valof_eq fraction_normal_of_Float
        powr_realpow[symmetric] exponent_normal_of_Float powr_diff powr_add)
  also
  have "\<bar>mantissa x\<bar> > 0"
    using that
    by (auto simp: is_normal_Float_def)
  have bound: "2 ^ LENGTH('f) \<le> nat \<bar>mantissa x\<bar> * 2 ^ (Suc LENGTH('f) - nat (bitlen \<bar>mantissa x\<bar>))"
  proof -
    have "(2::nat) ^ LENGTH('f) \<le> 2 ^ nat (bitlen \<bar>mantissa x\<bar> - 1) * 2 ^ (Suc LENGTH('f) - nat (bitlen \<bar>mantissa x\<bar>))"
      by (simp add: power_add[symmetric])
    also have "\<dots> \<le> nat \<bar>mantissa x\<bar> * 2 ^ (Suc LENGTH('f) - nat (bitlen \<bar>mantissa x\<bar>))"
      using bitlen_bounds[of "\<bar>mantissa x\<bar>"] that
      by (auto simp: is_normal_Float_def)
    finally show ?thesis .
  qed
  have "?m = abs (mantissa x)"
    apply (subst of_nat_diff)
    subgoal using bound by auto
    subgoal
      using that
      by (auto simp: powr_realpow[symmetric] powr_add[symmetric]
          is_normal_Float_def bitlen_nonneg of_nat_diff divide_simps)
    done
  finally show ?thesis
    by (auto simp: mantissa_exponent sign_normal_of_Float abs_real_def zero_less_mult_iff)
qed

lemma valof_denormal_of_Float: "valof (denormal_of_Float x::('e, 'f)float) = x"
  if "is_denormal_Float TYPE(('e, 'f)float) x"
proof -
  have less: "0 < Float.exponent x + (int (bias TYPE(('e, 'f) IEEE.float)) + int LENGTH('f))"
    using that
    by (auto simp: is_denormal_Float_def bias_def)
  have "valof (denormal_of_Float x::('e, 'f)float) =
    ((- 1) ^ sign (denormal_of_Float x::('e, 'f)float) * \<bar>real_of_int (mantissa x)\<bar>) *
    (2 powr real (nat (Float.exponent x + int (bias TYPE(('e, 'f) IEEE.float)) + int LENGTH('f) - 1)) /
      (2 powr real (bias TYPE(('e, 'f) IEEE.float)) * 2 powr LENGTH('f)) * 2)"
    (is "_ = ?m * ?e")
    by (auto simp: valof_eq exponent_denormal_of_Float fraction_denormal_of_Float that
        mantissa_exponent powr_realpow[symmetric])
  also have "?m = mantissa x"
    by (auto simp: sign_denormal_of_Float abs_real_def mantissa_neg_iff)
  also have "?e = 2 powr Float.exponent x"
    by (auto simp: powr_add[symmetric] divide_simps powr_mult_base less ac_simps)
  finally show ?thesis by (simp add: mantissa_exponent)
qed

lemma valof_of_finite_Float:
  "is_finite_Float (TYPE(('e, 'f) IEEE.float)) x \<Longrightarrow> valof (of_finite_Float x::('e, 'f)float) = x"
  by (auto simp: of_finite_Float_def is_finite_Float_def valof_denormal_of_Float valof_normal_of_Float)

lemma is_normal_normal_of_Float:
  "is_normal (normal_of_Float x::('e, 'f)float)" if "is_normal_Float TYPE(('e, 'f)float) x"
  using that
  by (auto simp: is_normal_def exponent_normal_of_Float that is_normal_Float_def
      emax_eq nat_less_iff)

lemma is_denormal_denormal_of_Float: "is_denormal (denormal_of_Float x::('e, 'f)float)"
  if "is_denormal_Float TYPE(('e, 'f)float) x"
  using that
  by (auto simp: is_denormal_def exponent_denormal_of_Float that is_denormal_Float_def
      emax_eq fraction_denormal_of_Float le_nat_iff bias_def)

lemma is_finite_of_finite_Float: "is_finite (of_finite_Float x)"
  by (auto simp: is_finite_def of_finite_Float_def is_normal_normal_of_Float
      is_denormal_denormal_of_Float)

lemma Float_eq_zero_iff: "Float m e = 0 \<longleftrightarrow> m = 0"
  by (metis Float.compute_is_float_zero Float_0_eq_0)

lemma bitlen_mantissa_Float:
  shows "bitlen \<bar>mantissa (Float m e)\<bar> = (if m = 0 then 0 else bitlen \<bar>m\<bar> + e) - Float.exponent (Float m e)"
  using bitlen_Float[of m e] by auto

lemma exponent_Float:
  shows "Float.exponent (Float m e) = (if m = 0 then 0 else bitlen \<bar>m\<bar> + e) - bitlen \<bar>mantissa (Float m e)\<bar> "
  using bitlen_Float[of m e] by auto

lemma is_normal_Float_normal:
  "is_normal_Float TYPE(('e, 'f)float) (Float (normal_mantissa x) (normal_exponent x))"
  if "is_normal x" for x::"('e, 'f)float"
proof -
  define f where "f = Float (normal_mantissa x) (normal_exponent x)"
  from that have "f \<noteq> 0"
    by (auto simp: f_def is_normal_def zero_float_def[symmetric]
        Float_eq_zero_iff normal_mantissa_def add_nonneg_eq_0_iff)
  from denormalize_shift[OF f_def this] obtain i where
    i: "normal_mantissa x = mantissa f * 2 ^ i" "normal_exponent x = Float.exponent f - int i"
    by auto
  have "mantissa f \<noteq> 0"
    by (auto simp: \<open>f \<noteq> 0\<close> i mantissa_eq_zero_iff Float_eq_zero_iff)
  moreover
  have "normal_exponent x \<le> Float.exponent f" unfolding i by simp
  then have " bitlen \<bar>mantissa f\<bar> \<le> 1 + int LENGTH('f)"
    unfolding bitlen_mantissa_Float bitlen_normal_mantissa f_def
    by auto
  moreover
  have "- int (bias TYPE(('e, 'f)float)) - bitlen \<bar>mantissa f\<bar> + 1 < Float.exponent f"
    unfolding bitlen_mantissa_Float bitlen_normal_mantissa f_def
    using that
    by (auto simp: mantissa_eq_zero_iff abs_mult bias_def normal_mantissa_def normal_exponent_def
        is_normal_def emax_eq less_diff_conv add_nonneg_eq_0_iff)
  moreover
  have "2 ^ (LENGTH('e) - Suc 0) + - (1::int) * 2 ^ LENGTH('e) \<le> 0"
    by simp
  then have "(2::int) ^ (LENGTH('e) - Suc 0) < 1 + 2 ^ LENGTH('e)" by arith
  then have "Float.exponent f <
      2 ^ LENGTH('e) - bitlen \<bar>mantissa f\<bar> - int (bias TYPE(('e, 'f)float))"
    using normal_exponent_bounds_int[OF that]
    unfolding bitlen_mantissa_Float bitlen_normal_mantissa f_def
    by (auto simp: bias_def algebra_simps power_Suc[symmetric]
        intro: le_less_trans[OF add_right_mono] normal_exponent_bounds_int[OF that])
  ultimately
  show ?thesis
    by (auto simp: is_normal_Float_def f_def)
qed


lemma is_denormal_Float_denormal:
  "is_denormal_Float TYPE(('e, 'f)float)
    (Float (denormal_mantissa x) (denormal_exponent TYPE(('e, 'f)float)))"
  if "is_denormal x" for x::"('e, 'f)float"
proof -
  define f where "f = Float (denormal_mantissa x) (denormal_exponent TYPE(('e, 'f)float))"
  from that have "f \<noteq> 0"
    by (auto simp: f_def is_denormal_def zero_float_def[symmetric]
        Float_eq_zero_iff denormal_mantissa_def add_nonneg_eq_0_iff)
  from denormalize_shift[OF f_def this] obtain i where
    i: "denormal_mantissa x = mantissa f * 2 ^ i" "denormal_exponent TYPE(('e, 'f)float) = Float.exponent f - int i"
    by auto
  have "mantissa f \<noteq> 0"
    by (auto simp: \<open>f \<noteq> 0\<close> i mantissa_eq_zero_iff Float_eq_zero_iff)
  moreover
  have "bitlen \<bar>mantissa f\<bar> \<le> 1 - Float.exponent f - int (bias TYPE(('e, 'f) IEEE.float))"
    using \<open>mantissa f \<noteq> 0\<close>
    unfolding f_def bitlen_mantissa_Float
    using bitlen_denormal_mantissa[of x]
    by (auto simp: denormal_exponent_def)
  moreover
  have "2 - 2 ^ (LENGTH('e) - Suc 0) - int LENGTH('f) \<le> Float.exponent f"
    (is "?l \<le> _")
  proof -
    have "?l \<le> denormal_exponent TYPE(('e, 'f)float) + i"
      using that
      by (auto simp: is_denormal_def bias_def denormal_exponent_def)
    also have "\<dots> = Float.exponent f" unfolding i by auto
    finally show ?thesis .
  qed
  ultimately
  show ?thesis
    unfolding is_denormal_Float_def exponent_Float f_def[symmetric]
    by auto
qed

lemma is_finite_Float_of_finite: "is_finite_Float TYPE(('e, 'f)float) (of_finite x)" for x::"('e, 'f)float"
  by (auto simp: is_finite_Float_def of_finite_def is_normal_Float_normal
      is_denormal_Float_denormal)

end
