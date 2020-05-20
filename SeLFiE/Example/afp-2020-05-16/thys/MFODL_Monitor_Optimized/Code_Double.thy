(*<*)
theory Code_Double
  imports IEEE_Floating_Point.IEEE_Properties
    "HOL-Library.Code_Target_Int"
    Containers.Collection_Eq
    Containers.Collection_Order
begin
(*>*)

section \<open>Code adaptation for IEEE double-precision floats\<close>

subsection \<open>copysign\<close>

lift_definition copysign :: "('e, 'f) float \<Rightarrow> ('e, 'f) float \<Rightarrow> ('e, 'f) float" is
  "\<lambda>(_, e::'e word, f::'f word) (s::1 word, _, _). (s, e, f)" .

lemma is_nan_copysign[simp]: "is_nan (copysign x y) \<longleftrightarrow> is_nan x"
  unfolding is_nan_def by transfer auto


subsection \<open>Additional lemmas about generic floats\<close>

lemma is_nan_some_nan[simp]: "is_nan (some_nan :: ('e, 'f) float)"
  unfolding some_nan_def
  by (rule someI[where x="Abs_float (0, max_word :: 'e word, 1)"])
    (auto simp add: is_nan_def exponent_def fraction_def emax_def Abs_float_inverse[simplified])

lemma not_is_nan_0[simp]: "\<not> is_nan 0"
  unfolding is_nan_def by (simp add: zero_simps)

lemma not_is_nan_1[simp]: "\<not> is_nan 1"
  unfolding is_nan_def by transfer simp

lemma is_nan_plus: "is_nan x \<or> is_nan y \<Longrightarrow> is_nan (x + y)"
  unfolding plus_float_def fadd_def by auto

lemma is_nan_minus: "is_nan x \<or> is_nan y \<Longrightarrow> is_nan (x - y)"
  unfolding minus_float_def fsub_def by auto

lemma is_nan_times: "is_nan x \<or> is_nan y \<Longrightarrow> is_nan (x * y)"
  unfolding times_float_def fmul_def by auto

lemma is_nan_divide: "is_nan x \<or> is_nan y \<Longrightarrow> is_nan (x / y)"
  unfolding divide_float_def fdiv_def by auto

lemma is_nan_float_sqrt: "is_nan x \<Longrightarrow> is_nan (float_sqrt x)"
  unfolding float_sqrt_def fsqrt_def by simp

lemma nan_fcompare: "is_nan x \<or> is_nan y \<Longrightarrow> fcompare x y = Und"
  unfolding fcompare_def by simp

lemma nan_not_le: "is_nan x \<or> is_nan y \<Longrightarrow> \<not> x \<le> y"
  unfolding less_eq_float_def fle_def fcompare_def by simp

lemma nan_not_less: "is_nan x \<or> is_nan y \<Longrightarrow> \<not> x < y"
  unfolding less_float_def flt_def fcompare_def by simp

lemma nan_not_zero: "is_nan x \<Longrightarrow> \<not> is_zero x"
  unfolding is_nan_def is_zero_def by simp

lemma nan_not_infinity: "is_nan x \<Longrightarrow> \<not> is_infinity x"
  unfolding is_nan_def is_infinity_def by simp

lemma zero_not_infinity: "is_zero x \<Longrightarrow> \<not> is_infinity x"
  unfolding is_zero_def is_infinity_def by simp

lemma zero_not_nan: "is_zero x \<Longrightarrow> \<not> is_nan x"
  unfolding is_zero_def is_nan_def by simp


lemma minus_one_power_one_word: "(-1 :: real) ^ unat (x :: 1 word) = (if unat x = 0 then 1 else -1)"
proof -
  have "unat x = 0 \<or> unat x = 1"
    using le_SucE[OF unat_one_word_le] by auto
  then show ?thesis by auto
qed

definition valofn :: "('e, 'f) float \<Rightarrow> real" where
  "valofn x = (2^exponent x / 2^bias TYPE(('e, 'f) float)) *
      (1 + real (fraction x) / 2^LENGTH('f))"

definition valofd :: "('e, 'f) float \<Rightarrow> real" where
  "valofd x = (2 / 2^bias TYPE(('e, 'f) float)) * (real (fraction x) / 2^LENGTH('f))"

lemma valof_alt: "valof x = (if exponent x = 0 then
    if sign x = 0 then valofd x else - valofd x
  else if sign x = 0 then valofn x else - valofn x)"
  unfolding valofn_def valofd_def
  by transfer (auto simp: minus_one_power_one_word unat_eq_0 field_simps)

lemma fraction_less_2p: "fraction (x :: ('e, 'f) float) < 2^LENGTH('f)"
  by transfer auto

lemma valofn_ge_0: "0 \<le> valofn x"
  unfolding valofn_def by simp

lemma valofn_ge_2p: "2^exponent (x :: ('e, 'f) float) / 2^bias TYPE(('e, 'f) float) \<le> valofn x"
  unfolding valofn_def by (simp add: field_simps)

lemma valofn_less_2p:
  fixes x :: "('e, 'f) float"
  assumes "exponent x < e"
  shows "valofn x < 2^e / 2^bias TYPE(('e, 'f) float)"
proof -
  have "1 + real (fraction x) / 2^LENGTH('f) < 2"
    by (simp add: fraction_less_2p)
  then have "valofn x < (2^exponent x / 2^bias TYPE(('e, 'f) float)) * 2"
    unfolding valofn_def by (simp add: field_simps)
  also have "... \<le> 2^e / 2^bias TYPE(('e, 'f) float)"
    using assms by (auto simp: less_eq_Suc_le field_simps elim: order_trans[rotated, OF exp_less])
  finally show ?thesis .
qed

lemma valofd_ge_0: "0 \<le> valofd x"
  unfolding valofd_def by simp

lemma valofd_less_2p: "valofd (x :: ('e, 'f) float) < 2 / 2^bias TYPE(('e, 'f) float)"
  unfolding valofd_def
  by (simp add: fraction_less_2p field_simps)

lemma valofn_le_imp_exponent_le:
  fixes x y :: "('e, 'f) float"
  assumes "valofn x \<le> valofn y"
  shows "exponent x \<le> exponent y"
proof (rule ccontr)
  assume "\<not> exponent x \<le> exponent y"
  then have "valofn y < 2^exponent x / 2^bias TYPE(('e, 'f) float)"
    using valofn_less_2p[of y] by auto
  also have "... \<le> valofn x" by (rule valofn_ge_2p)
  finally show False using assms by simp
qed

lemma valofn_eq:
  fixes x y :: "('e, 'f) float"
  assumes "valofn x = valofn y"
  shows "exponent x = exponent y" "fraction x = fraction y"
proof -
  from assms show "exponent x = exponent y"
    by (auto intro!: antisym valofn_le_imp_exponent_le)
  with assms show "fraction x = fraction y"
    unfolding valofn_def by (simp add: field_simps)
qed

lemma valofd_eq:
  fixes x y :: "('e, 'f) float"
  assumes "valofd x = valofd y"
  shows "fraction x = fraction y"
  using assms unfolding valofd_def by (simp add: field_simps)

lemma is_zero_valof_conv: "is_zero x \<longleftrightarrow> valof x = 0"
  unfolding is_zero_def valof_alt
  using valofn_ge_2p[of x] by (auto simp: valofd_def field_simps dest: order.antisym)

lemma valofd_neq_valofn:
  fixes x y :: "('e, 'f) float"
  assumes "exponent y \<noteq> 0"
  shows "valofd x \<noteq> valofn y" "valofn y \<noteq> valofd x"
proof -
  have "valofd x < 2 / 2^bias TYPE(('e, 'f) float)" by (rule valofd_less_2p)
  also have "... \<le> 2 ^ IEEE.exponent y / 2 ^ bias TYPE(('e, 'f) IEEE.float)"
    using assms by (simp add: self_le_power field_simps)
  also have "... \<le> valofn y" by (rule valofn_ge_2p)
  finally show "valofd x \<noteq> valofn y" "valofn y \<noteq> valofd x" by simp_all
qed

lemma sign_gt_0_conv: "0 < sign x \<longleftrightarrow> sign x = 1"
  by (cases x rule: sign_cases) simp_all

lemma valof_eq:
  assumes "\<not> is_zero x \<or> \<not> is_zero y"
  shows "valof x = valof y \<longleftrightarrow> x = y"
proof
  assume *: "valof x = valof y"
  with assms have "valof y \<noteq> 0" by (simp add: is_zero_valof_conv)
  with * show "x = y"
    unfolding valof_alt
    using valofd_ge_0[of x] valofd_ge_0[of y] valofn_ge_0[of x] valofn_ge_0[of y]
    by (auto simp: valofd_neq_valofn sign_gt_0_conv split: if_splits
        intro!: float_eqI elim: valofn_eq valofd_eq)
qed simp

lemma zero_fcompare: "is_zero x \<Longrightarrow> is_zero y \<Longrightarrow> fcompare x y = ccode.Eq"
  unfolding fcompare_def by (simp add: zero_not_infinity zero_not_nan is_zero_valof_conv)


subsection \<open>Doubles with a unified NaN value\<close>

quotient_type double = "(11, 52) float" / "\<lambda>x y. is_nan x \<and> is_nan y \<or> x = y"
  by (auto intro!: equivpI reflpI sympI transpI)

instantiation double :: "{zero, one, plus, minus, uminus, times, ord}"
begin

lift_definition zero_double :: "double" is "0" .
lift_definition one_double :: "double" is "1" .

lift_definition plus_double :: "double \<Rightarrow> double \<Rightarrow> double" is plus
  by (auto simp: is_nan_plus)

lift_definition minus_double :: "double \<Rightarrow> double \<Rightarrow> double" is minus
  by (auto simp: is_nan_minus)

lift_definition uminus_double :: "double \<Rightarrow> double" is uminus
  by auto

lift_definition times_double :: "double \<Rightarrow> double \<Rightarrow> double" is times
  by (auto simp: is_nan_times)

lift_definition less_eq_double :: "double \<Rightarrow> double \<Rightarrow> bool" is "(\<le>)"
  by (auto simp: nan_not_le)

lift_definition less_double :: "double \<Rightarrow> double \<Rightarrow> bool" is "(<)"
  by (auto simp: nan_not_less)

instance ..

end

instantiation double :: inverse
begin

lift_definition divide_double :: "double \<Rightarrow> double \<Rightarrow> double" is divide
  by (auto simp: is_nan_divide)

definition inverse_double :: "double \<Rightarrow> double" where
  "inverse_double x = 1 div x"

instance ..

end

lift_definition sqrt_double :: "double \<Rightarrow> double" is float_sqrt
  by (auto simp: is_nan_float_sqrt)

no_notation plus_infinity ("\<infinity>")

lift_definition infinity :: "double" is plus_infinity .

lift_definition nan :: "double" is some_nan .

lift_definition is_zero :: "double \<Rightarrow> bool" is IEEE.is_zero
  by (auto simp: nan_not_zero)

lift_definition is_infinite :: "double \<Rightarrow> bool" is IEEE.is_infinity
  by (auto simp: nan_not_infinity)

lift_definition is_nan :: "double \<Rightarrow> bool" is IEEE.is_nan
  by auto

lemma is_nan_conv: "is_nan x \<longleftrightarrow> x = nan"
  by transfer auto

lift_definition copysign_double :: "double \<Rightarrow> double \<Rightarrow> double" is
  "\<lambda>x y. if IEEE.is_nan y then some_nan else copysign x y"
  by auto

text \<open>Note: @{const copysign_double} deviates from the IEEE standard in cases where
  the second argument is a NaN.\<close>

lift_definition fcompare_double :: "double \<Rightarrow> double \<Rightarrow> ccode" is fcompare
  by (auto simp: nan_fcompare)

lemma nan_fcompare_double: "is_nan x \<or> is_nan y \<Longrightarrow> fcompare_double x y = Und"
  by transfer (rule nan_fcompare)

consts compare_double :: "double \<Rightarrow> double \<Rightarrow> integer"

specification (compare_double)
  compare_double_less: "compare_double x y < 0 \<longleftrightarrow> is_nan x \<and> \<not> is_nan y \<or> fcompare_double x y = ccode.Lt"
  compare_double_eq: "compare_double x y = 0 \<longleftrightarrow> is_nan x \<and> is_nan y \<or> fcompare_double x y = ccode.Eq"
  compare_double_greater: "compare_double x y > 0 \<longleftrightarrow> \<not> is_nan x \<and> is_nan y \<or> fcompare_double x y = ccode.Gt"
  by (rule exI[where x="\<lambda>x y. if is_nan x then if is_nan y then 0 else -1
    else if is_nan y then 1 else (case fcompare_double x y of ccode.Eq \<Rightarrow> 0 | ccode.Lt \<Rightarrow> -1 | ccode.Gt \<Rightarrow> 1)"],
        transfer, auto simp: fcompare_def)

lemmas compare_double_simps = compare_double_less compare_double_eq compare_double_greater

lemma compare_double_le_0: "compare_double x y \<le> 0 \<longleftrightarrow>
  is_nan x \<or> fcompare_double x y \<in> {ccode.Eq, ccode.Lt}"
  by (rule linorder_cases[of "compare_double x y" 0]; simp)
    (auto simp: compare_double_simps nan_fcompare_double)

lift_definition double_of_integer :: "integer \<Rightarrow> double" is
  "\<lambda>x. zerosign 0 (intround To_nearest (int_of_integer x))" .

definition double_of_int where [code del]: "double_of_int x = double_of_integer (integer_of_int x)"

lemma [code]: "double_of_int (int_of_integer x) = double_of_integer x"
  unfolding double_of_int_def by simp

lift_definition integer_of_double :: "double \<Rightarrow> integer" is
  "\<lambda>x. if IEEE.is_nan x \<or> IEEE.is_infinity x then undefined
     else integer_of_int \<lfloor>valof (intround float_To_zero (valof x) :: (11, 52) float)\<rfloor>"
  by auto

definition int_of_double: "int_of_double x = int_of_integer (integer_of_double x)"


subsection \<open>Linear ordering\<close>

definition lcompare_double :: "double \<Rightarrow> double \<Rightarrow> integer" where
  "lcompare_double x y = (if is_zero x \<and> is_zero y then
      compare_double (copysign_double 1 x) (copysign_double 1 y)
    else compare_double x y)"

lemma fcompare_double_swap: "fcompare_double x y = ccode.Gt \<longleftrightarrow> fcompare_double y x = ccode.Lt"
  by transfer (auto simp: fcompare_def)

lemma fcompare_double_refl: "\<not> is_nan x \<Longrightarrow> fcompare_double x x = ccode.Eq"
  by transfer (auto simp: fcompare_def)

lemma fcompare_double_Eq1: "fcompare_double x y = ccode.Eq \<Longrightarrow> fcompare_double y z = c \<Longrightarrow> fcompare_double x z = c"
  by transfer (auto simp: fcompare_def split: if_splits)

lemma fcompare_double_Eq2: "fcompare_double y z = ccode.Eq \<Longrightarrow> fcompare_double x y = c \<Longrightarrow> fcompare_double x z = c"
  by transfer (auto simp: fcompare_def split: if_splits)

lemma fcompare_double_Lt_trans: "fcompare_double x y = ccode.Lt \<Longrightarrow> fcompare_double y z = ccode.Lt \<Longrightarrow> fcompare_double x z = ccode.Lt"
  by transfer (auto simp: fcompare_def split: if_splits)

lemma fcompare_double_eq: "\<not> is_zero x \<or> \<not> is_zero y \<Longrightarrow> fcompare_double x y = ccode.Eq \<Longrightarrow> x = y"
  by transfer (auto simp: fcompare_def valof_eq IEEE.is_infinity_def split: if_splits intro!: float_eqI)

lemma fcompare_double_Lt_asym: "fcompare_double x y = ccode.Lt \<Longrightarrow> fcompare_double y x = ccode.Lt \<Longrightarrow> False"
  by transfer (auto simp: fcompare_def split: if_splits)

lemma compare_double_swap: "0 < compare_double x y \<longleftrightarrow> compare_double y x < 0"
  by (auto simp: compare_double_simps fcompare_double_swap)

lemma compare_double_refl: "compare_double x x = 0"
  by (auto simp: compare_double_eq intro!: fcompare_double_refl)

lemma compare_double_trans: "compare_double x y \<le> 0 \<Longrightarrow> compare_double y z \<le> 0 \<Longrightarrow> compare_double x z \<le> 0"
  by (fastforce simp: compare_double_le_0 nan_fcompare_double
      dest: fcompare_double_Eq1 fcompare_double_Eq2 fcompare_double_Lt_trans)

lemma compare_double_antisym: "compare_double x y \<le> 0 \<Longrightarrow> compare_double y x \<le> 0 \<Longrightarrow>
  \<not> is_zero x \<or> \<not> is_zero y \<Longrightarrow> x = y"
  unfolding compare_double_le_0
  by (auto simp: nan_fcompare_double is_nan_conv
      intro: fcompare_double_eq fcompare_double_eq[symmetric]
      dest: fcompare_double_Lt_asym)

lemma zero_compare_double_copysign: "compare_double (copysign_double 1 x) (copysign_double 1 y) \<le> 0 \<Longrightarrow>
  is_zero x \<Longrightarrow> is_zero y \<Longrightarrow> compare_double x y \<le> 0"
  unfolding compare_double_le_0
  by transfer (auto simp: nan_not_zero zero_fcompare split: if_splits)

lemma is_zero_double_cases: "is_zero x \<Longrightarrow> (x = 0 \<Longrightarrow> P) \<Longrightarrow> (x = -0 \<Longrightarrow> P) \<Longrightarrow> P"
  by transfer (auto elim!: is_zero_cases)

lemma copysign_1_0[simp]: "copysign_double 1 0 = 1" "copysign_double 1 (-0) = -1"
  by (transfer, simp, transfer, auto)+

lemma is_zero_uminus_double[simp]: "is_zero (- x) \<longleftrightarrow> is_zero x"
  by transfer simp

lemma not_is_zero_one_double[simp]: "\<not> is_zero 1"
  by (transfer, unfold IEEE.is_zero_def, transfer, simp)

lemma uminus_one_neq_one_double[simp]: "- 1 \<noteq> (1 :: double)"
  by (transfer, transfer, simp)

definition lle_double :: "double \<Rightarrow> double \<Rightarrow> bool" where
  "lle_double x y \<longleftrightarrow> lcompare_double x y \<le> 0"

definition lless_double :: "double \<Rightarrow> double \<Rightarrow> bool" where
  "lless_double x y \<longleftrightarrow> lcompare_double x y < 0"

lemma lcompare_double_ge_0: "lcompare_double x y \<ge> 0 \<longleftrightarrow> lle_double y x"
  unfolding lle_double_def lcompare_double_def
  using compare_double_swap not_less by auto

lemma lcompare_double_gt_0: "lcompare_double x y > 0 \<longleftrightarrow> lless_double y x"
  unfolding lless_double_def lcompare_double_def
  using compare_double_swap by auto

lemma lcompare_double_eq_0: "lcompare_double x y = 0 \<longleftrightarrow> x = y"
proof
  assume *: "lcompare_double x y = 0"
  show "x = y" proof (cases "is_zero x \<and> is_zero y")
    case True
    with * show ?thesis
      by (fastforce simp: lcompare_double_def compare_double_simps is_nan_conv
          elim: is_zero_double_cases dest!: fcompare_double_eq[rotated])
  next
    case False
    with * show ?thesis
      by (auto simp: lcompare_double_def linorder_not_less[symmetric] compare_double_swap
          intro!: compare_double_antisym)
  qed
next
  assume "x = y"
  then show "lcompare_double x y = 0"
    by (simp add: lcompare_double_def compare_double_refl)
qed

lemmas lcompare_double_0_folds = lle_double_def[symmetric] lless_double_def[symmetric]
  lcompare_double_ge_0 lcompare_double_gt_0 lcompare_double_eq_0

interpretation double_linorder: linorder lle_double lless_double
proof
  fix x y z :: double
  show "lless_double x y \<longleftrightarrow> lle_double x y \<and> \<not> lle_double y x"
    unfolding lless_double_def lle_double_def lcompare_double_def
    by (auto simp: compare_double_swap not_le)
  show "lle_double x x"
    unfolding lle_double_def lcompare_double_def
    by (auto simp: compare_double_refl)
  show "lle_double x z" if "lle_double x y" and "lle_double y z"
    using that
    by (auto 0 3 simp: lle_double_def lcompare_double_def not_le compare_double_swap
        split: if_splits dest: compare_double_trans zero_compare_double_copysign
        zero_compare_double_copysign[OF less_imp_le] compare_double_antisym)
  show "x = y" if "lle_double x y" and "lle_double y x"
  proof (cases "is_zero x \<and> is_zero y")
    case True
    with that show ?thesis
      by (auto 0 3 simp: lle_double_def lcompare_double_def elim: is_zero_double_cases
          dest!: compare_double_antisym)
  next
    case False
    with that show ?thesis
      by (auto simp: lle_double_def lcompare_double_def elim!: compare_double_antisym)
  qed
  show "lle_double x y \<or> lle_double y x"
    unfolding lle_double_def lcompare_double_def
    by (auto simp: compare_double_swap not_le)
qed

instantiation double :: equal
begin

definition equal_double :: "double \<Rightarrow> double \<Rightarrow> bool" where
  "equal_double x y \<longleftrightarrow> lcompare_double x y = 0"

instance by intro_classes (simp add: equal_double_def lcompare_double_eq_0)

end

derive (eq) ceq double

definition comparator_double :: "double comparator" where
  "comparator_double x y = (let c = lcompare_double x y in
    if c = 0 then order.Eq else if c < 0 then order.Lt else order.Gt)"

lemma comparator_double: "comparator comparator_double"
  unfolding comparator_double_def
  by (auto simp: lcompare_double_0_folds split: if_splits intro!: comparator.intro)

local_setup \<open>
  Comparator_Generator.register_foreign_comparator @{typ double}
    @{term comparator_double}
    @{thm comparator_double}
\<close>

derive ccompare double


subsubsection \<open>Code setup\<close>

declare [[code drop:
      "0 :: double"
      "1 :: double"
      "plus :: double \<Rightarrow> _"
      "minus :: double \<Rightarrow> _"
      "uminus :: double \<Rightarrow> _"
      "times :: double \<Rightarrow> _"
      "less_eq :: double \<Rightarrow> _"
      "less :: double \<Rightarrow> _"
      "divide :: double \<Rightarrow> _"
      sqrt_double infinity nan is_zero is_infinite is_nan copysign_double fcompare_double
      double_of_integer integer_of_double
      ]]

code_printing
  code_module FloatUtil \<rightharpoonup> (OCaml)
\<open>module FloatUtil : sig
  val iszero : float -> bool
  val isinfinite : float -> bool
  val isnan : float -> bool
  val copysign : float -> float -> float
  val compare : float -> float -> Z.t
end = struct
  let iszero x = (Pervasives.classify_float x = Pervasives.FP_zero);;
  let isinfinite x = (Pervasives.classify_float x = Pervasives.FP_infinite);;
  let isnan x = (Pervasives.classify_float x = Pervasives.FP_nan);;
  let copysign x y = if isnan y then Pervasives.nan else Pervasives.copysign x y;;
  let compare x y = Z.of_int (Pervasives.compare x y);;
end;;\<close>

code_reserved OCaml Pervasives FloatUtil

code_printing
  type_constructor double \<rightharpoonup> (OCaml) "float"
  | constant "uminus :: double \<Rightarrow> double" \<rightharpoonup> (OCaml) "Pervasives.(~-.)"
  | constant "(+) :: double \<Rightarrow> double \<Rightarrow> double" \<rightharpoonup> (OCaml) "Pervasives.(+.)"
  | constant "(*) :: double \<Rightarrow> double \<Rightarrow> double" \<rightharpoonup> (OCaml) "Pervasives.( *. )"
  | constant "(/) :: double \<Rightarrow> double \<Rightarrow> double" \<rightharpoonup> (OCaml) "Pervasives.('/.)"
  | constant "(-) :: double \<Rightarrow> double \<Rightarrow> double" \<rightharpoonup> (OCaml) "Pervasives.(-.)"
  | constant "0 :: double" \<rightharpoonup> (OCaml) "0.0"
  | constant "1 :: double" \<rightharpoonup> (OCaml) "1.0"
  | constant "(\<le>) :: double \<Rightarrow> double \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Pervasives.(<=)"
  | constant "(<) :: double \<Rightarrow> double \<Rightarrow> bool" \<rightharpoonup> (OCaml) "Pervasives.(<)"
  | constant "sqrt_double :: double \<Rightarrow> double" \<rightharpoonup> (OCaml) "Pervasives.sqrt"
  | constant "infinity :: double" \<rightharpoonup> (OCaml) "Pervasives.infinity"
  | constant "nan :: double" \<rightharpoonup> (OCaml) "Pervasives.nan"
  | constant "is_zero :: double \<Rightarrow> bool" \<rightharpoonup> (OCaml) "FloatUtil.iszero"
  | constant "is_infinite :: double \<Rightarrow> bool" \<rightharpoonup> (OCaml) "FloatUtil.isinfinite"
  | constant "is_nan :: double \<Rightarrow> bool" \<rightharpoonup> (OCaml) "FloatUtil.isnan"
  | constant "copysign_double :: double \<Rightarrow> double \<Rightarrow> double" \<rightharpoonup> (OCaml) "FloatUtil.copysign"
  | constant "compare_double :: double \<Rightarrow> double \<Rightarrow> integer" \<rightharpoonup> (OCaml) "FloatUtil.compare"
  | constant "double_of_integer :: integer \<Rightarrow> double" \<rightharpoonup> (OCaml) "Z.to'_float"
  | constant "integer_of_double :: double \<Rightarrow> integer" \<rightharpoonup> (OCaml) "Z.of'_float"

hide_const (open) fcompare_double

(*<*)
end
(*>*)

