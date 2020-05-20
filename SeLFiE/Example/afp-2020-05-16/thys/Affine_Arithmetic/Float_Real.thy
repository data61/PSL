section \<open>Dyadic Rational Representation of Real\<close>
theory Float_Real
imports
  "HOL-Library.Float"
  Optimize_Float
begin
text \<open>\label{sec:floatreal}\<close>

code_datatype real_of_float

abbreviation
  float_of_nat :: "nat \<Rightarrow> float"
where
  "float_of_nat \<equiv> of_nat"

abbreviation
  float_of_int :: "int \<Rightarrow> float"
where
  "float_of_int \<equiv> of_int"

text\<open>Collapse nested embeddings\<close>

text \<open>Operations\<close>

text \<open>Undo code setup for @{term Ratreal}.\<close>

lemma of_rat_numeral_eq [code_abbrev]:
  "real_of_float (numeral w) = Ratreal (numeral w)"
  by simp

lemma zero_real_code [code]:
  "0 = real_of_float 0"
  by simp

lemma one_real_code [code]:
  "1 = real_of_float 1"
  by simp

lemma [code_abbrev]:
  "(real_of_float (of_int a) :: real) = (Ratreal (Rat.of_int a) :: real)"
  by (auto simp: Rat.of_int_def )

lemma [code_abbrev]:
  "real_of_float 0 \<equiv> Ratreal 0"
  by simp

lemma [code_abbrev]:
  "real_of_float 1 = Ratreal 1"
  by simp

lemmas compute_real_of_float[code del]

lemmas [code del] =
  real_equal_code
  real_less_eq_code
  real_less_code
  real_plus_code
  real_times_code
  real_uminus_code
  real_minus_code
  real_inverse_code
  real_divide_code
  real_floor_code
  Float.compute_truncate_down
  Float.compute_truncate_up

lemma real_equal_code [code]:
  "HOL.equal (real_of_float x) (real_of_float y) \<longleftrightarrow> HOL.equal x y"
  by (metis (poly_guards_query) equal real_of_float_inverse)

abbreviation FloatR::"int\<Rightarrow>int\<Rightarrow>real" where
  "FloatR a b \<equiv> real_of_float (Float a b)"

lemma real_less_eq_code' [code]: "real_of_float x \<le> real_of_float y \<longleftrightarrow> x \<le> y"
  and real_less_code' [code]: "real_of_float x < real_of_float y \<longleftrightarrow> x < y"
  and real_plus_code' [code]: "real_of_float x + real_of_float y = real_of_float (x + y)"
  and real_times_code' [code]: "real_of_float x * real_of_float y = real_of_float (x * y)"
  and real_uminus_code' [code]: "- real_of_float x = real_of_float (- x)"
  and real_minus_code' [code]: "real_of_float x - real_of_float y = real_of_float (x - y)"
  and real_inverse_code' [code]: "inverse (FloatR a b) =
    (if FloatR a b = 2 then FloatR 1 (-1) else
    if a = 1 then FloatR 1 (- b) else
    Code.abort (STR ''inverse not of 2'') (\<lambda>_. inverse (FloatR a b)))"
  and real_divide_code' [code]: "FloatR a b / FloatR c d =
    (if FloatR c d = 2 then if a mod 2 = 0 then FloatR (a div 2) b else FloatR a (b - 1) else
    if c = 1 then FloatR a (b - d) else
    Code.abort (STR ''division not by 2'') (\<lambda>_. FloatR a b / FloatR c d))"
  and real_floor_code' [code]: "floor (real_of_float x) = int_floor_fl x"
  and real_abs_code' [code]: "abs (real_of_float x) = real_of_float (abs x)"
  by (auto simp add: int_floor_fl.rep_eq powr_diff powr_minus inverse_eq_divide)

lemma compute_round_down[code]: "round_down prec (real_of_float f) = real_of_float (float_down prec f)"
  by simp

lemma compute_round_up[code]: "round_up prec (real_of_float f) = real_of_float (float_up prec f)"
  by simp

lemma compute_truncate_down[code]:
  "truncate_down prec (real_of_float f) = real_of_float (float_round_down prec f)"
  by (simp add: Float.float_round_down.rep_eq truncate_down_def)

lemma compute_truncate_up[code]:
  "truncate_up prec (real_of_float f) = real_of_float (float_round_up prec f)"
  by (simp add: float_round_up.rep_eq truncate_up_def)

lemma [code]: "real_divl p (real_of_float x) (real_of_float y) = real_of_float (float_divl p x y)"
  by (simp add: float_divl.rep_eq real_divl_def)

lemma [code]: "real_divr p (real_of_float x) (real_of_float y) = real_of_float (float_divr p x y)"
  by (simp add: float_divr.rep_eq real_divr_def)

lemmas [code] = real_of_float_inverse

end
