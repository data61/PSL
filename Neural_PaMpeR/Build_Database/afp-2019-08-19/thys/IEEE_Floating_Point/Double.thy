(* Author: Lei Yu, University of Cambridge *)

section \<open>Code Generation Setup for Floats\<close>

theory Double
  imports
    Conversion_IEEE_Float
    "HOL-Library.Monad_Syntax"
    "HOL-Library.Code_Target_Numeral"
begin

text \<open>A type for code generation to SML/OCaml\<close>

typedef double = "UNIV::(11, 52) float set" ..

setup_lifting type_definition_double

instantiation double :: "{uminus,plus,times,minus,zero,one,abs,ord,inverse}" begin
lift_definition uminus_double::"double \<Rightarrow> double" is uminus .
lift_definition plus_double::"double \<Rightarrow> double \<Rightarrow> double" is plus .
lift_definition times_double::"double \<Rightarrow> double \<Rightarrow> double" is times .
lift_definition divide_double::"double \<Rightarrow> double \<Rightarrow> double" is divide .
lift_definition inverse_double::"double \<Rightarrow> double" is inverse .
lift_definition minus_double::"double \<Rightarrow> double \<Rightarrow> double" is minus .
lift_definition zero_double::"double" is "0" .
lift_definition one_double::"double" is "1" .
lift_definition less_eq_double::"double \<Rightarrow> double \<Rightarrow> bool" is "(\<le>)" .
lift_definition less_double::"double \<Rightarrow> double \<Rightarrow> bool" is "(<)" .
instance proof qed
end

lift_definition eq_double::"double\<Rightarrow>double\<Rightarrow>bool" is float_eq .

lift_definition sqrt_double::"double\<Rightarrow>double" is float_sqrt .

no_notation plus_infinity ("\<infinity>")

lift_definition infinity_double::"double" ("\<infinity>") is plus_infinity .

lift_definition is_normal::"double \<Rightarrow> bool" is IEEE.is_normal .
lift_definition is_zero::"double \<Rightarrow> bool" is IEEE.is_zero .
lift_definition is_finite::"double \<Rightarrow> bool" is IEEE.is_finite .
lift_definition is_nan::"double \<Rightarrow> bool" is IEEE.is_nan .

code_printing type_constructor double \<rightharpoonup>
  (SML) "real" and (OCaml) "float"

code_printing constant "0 :: double" \<rightharpoonup>
  (SML) "0.0" and (OCaml) "0.0"
declare zero_double.abs_eq[code del]

code_printing constant "1 :: double" \<rightharpoonup>
  (SML) "1.0" and (OCaml) "1.0"
declare one_double.abs_eq[code del]

code_printing constant "eq_double :: double \<Rightarrow> double \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.== ((_:real), (_))" and (OCaml) "Pervasives.(=)"
declare eq_double.abs_eq[code del]

code_printing constant "Orderings.less_eq :: double \<Rightarrow> double \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.<= ((_), (_))" and (OCaml) "Pervasives.(<=)"
declare less_double_def [code del]

code_printing constant "Orderings.less :: double \<Rightarrow> double \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.< ((_), (_))" and (OCaml) "Pervasives.(<)"
declare less_eq_double_def[code del]

code_printing constant "(+) :: double \<Rightarrow> double \<Rightarrow> double" \<rightharpoonup>
  (SML) "Real.+ ((_), (_))" and (OCaml) "Pervasives.( +. )"
declare plus_double_def[code del]

code_printing constant "(*) :: double \<Rightarrow> double \<Rightarrow> double" \<rightharpoonup>
  (SML) "Real.* ((_), (_))" and (OCaml) "Pervasives.( *. )"
declare times_double_def [code del]

code_printing constant "(-) :: double \<Rightarrow> double \<Rightarrow> double" \<rightharpoonup>
  (SML) "Real.- ((_), (_))" and (OCaml) "Pervasives.( -. )"
declare minus_double_def [code del]

code_printing constant "uminus :: double \<Rightarrow> double" \<rightharpoonup>
  (SML) "Real.~" and (OCaml) "Pervasives.( ~-. )"

code_printing constant "(/) :: double \<Rightarrow> double \<Rightarrow> double" \<rightharpoonup>
  (SML) "Real.'/ ((_), (_))" and (OCaml) "Pervasives.( '/. )"
declare divide_double_def [code del]

code_printing constant "sqrt_double :: double \<Rightarrow> double" \<rightharpoonup>
  (SML) "Math.sqrt" and (OCaml) "Pervasives.sqrt"
declare sqrt_def[code del]

code_printing constant "infinity_double :: double" \<rightharpoonup>
  (SML) "Real.posInf"
declare infinity_double.abs_eq[code del]

code_printing constant "is_normal :: double \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.isNormal"
declare [[code drop: "is_normal"]]

code_printing constant "is_finite :: double \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.isFinite"
declare [[code drop: "is_finite"]]

code_printing constant "is_nan :: double \<Rightarrow> bool" \<rightharpoonup>
  (SML) "Real.isNan"
declare [[code drop: "is_nan"]]

text \<open>Mapping natural numbers to doubles.\<close>
fun float_of :: "nat \<Rightarrow> double"
where
  "float_of 0 = 0"
| "float_of (Suc n) = float_of n + 1"

lemma "float_of 2 < float_of 3 + float_of 4"
  by eval

export_code float_of in SML

subsection \<open>Conversion from int\<close>

lift_definition double_of_int::"int \<Rightarrow> double" is "\<lambda>i. round To_nearest (real_of_int i)" .

context includes integer.lifting begin
lift_definition double_of_integer::"integer \<Rightarrow> double" is double_of_int .
end

lemma float_of_int[code]:
  "double_of_int i = double_of_integer (integer_of_int i)"
  by (auto simp: double_of_integer_def)

code_printing
  constant "double_of_integer :: integer \<Rightarrow> double" \<rightharpoonup> (SML) "Real.fromLargeInt"
declare [[code drop: double_of_integer]]


subsection \<open>Conversion to and from software floats, extracting information\<close>

text \<open>Need to trust a lot of code here...\<close>

lemma is_finite_double_eq:
  "is_finite_Float TYPE((11, 52)float) f \<longleftrightarrow>
    (let e = Float.exponent f; bm = bitlen (abs (mantissa f))
    in (bm \<le> 53 \<and> e + bm < 1025 \<and> - 1075 < e))"
  unfolding is_finite_Float_eq
  by (auto simp: Let_def)

code_printing
  code_module "IEEE_Mantissa_Exponent" \<rightharpoonup> (SML)
\<open>
structure IEEE_Mantissa_Exponent =
struct
fun to_man_exp_double x =
  if Real.isFinite x
  then case Real.toManExp x of {man = m, exp = e} =>
    SOME (Real.floor (Real.* (m, Math.pow (2.0, 53.0))), IntInf.- (e, 53))
  else NONE
fun normfloat (m, e) =
(if m mod 2 = 0 andalso m <> 0 then normfloat (m div 2, e + 1)
 else if m = 0 then (0, 0) else (m, e))
fun bitlen x = (if 0 < x then bitlen (x div 2) + 1 else 0)
fun is_finite_double_eq m e =
  let
    val (m, e) = normfloat (m, e)
    val bm = bitlen (abs m)
  in bm <= 53 andalso e + bm < 1025 andalso e > ~1075 end
fun from_man_exp_double m e =
  if is_finite_double_eq m e
  then SOME (Real.fromManExp {man = Real.fromLargeInt m, exp = e})
  else NONE
end
\<close>

lift_definition of_finite::"double \<Rightarrow> Float.float" is Conversion_IEEE_Float.of_finite .

definition man_exp_of_double::"double \<Rightarrow> (integer * integer)option" where
  "man_exp_of_double d = (if is_finite d then let f = of_finite d in
    Some (integer_of_int (mantissa f), integer_of_int (Float.exponent f)) else None)"

lift_definition of_finite_Float::"Float.float \<Rightarrow> double" is Conversion_IEEE_Float.of_finite_Float .

definition double_of_man_exp::"integer \<Rightarrow> integer \<Rightarrow> double option" where
  "double_of_man_exp m e = (let f = Float (int_of_integer m) (int_of_integer e) in
    if is_finite_Float TYPE((11, 52)float) f
    then Some (of_finite_Float f)
    else None)"

code_printing
  constant "man_exp_of_double :: double \<Rightarrow> (integer * integer) option" \<rightharpoonup>
    (SML) "IEEE'_Mantissa'_Exponent.to'_man'_exp'_double" |
  constant "double_of_man_exp :: integer \<Rightarrow> integer \<Rightarrow> double option" \<rightharpoonup>
    (SML) "IEEE'_Mantissa'_Exponent.from'_man'_exp'_double"
declare [[code drop: man_exp_of_double]]
declare [[code drop: double_of_man_exp]]

lift_definition Float_of_double::"double \<Rightarrow> Float.float option" is
  "\<lambda>x. if is_finite x then Some (of_finite x) else None" .

lift_definition double_of_Float::"Float.float \<Rightarrow> double option" is
  "\<lambda>x. if is_finite_Float TYPE((11, 52)float) x then Some (of_finite_Float x) else None" .

lemma compute_Float_of_double[code]:
  "Float_of_double x =
    map_option (\<lambda>(m, e). Float (int_of_integer m) (int_of_integer e)) (man_exp_of_double x)"
  apply (rule sym)
  by transfer (auto simp: man_exp_of_double_def Let_def mantissa_exponent[symmetric]
      Float_mantissa_exponent)

lemma compute_double_of_Float[code]:
  "double_of_Float f = double_of_man_exp (integer_of_int (mantissa f)) (integer_of_int (Float.exponent f))"
  unfolding double_of_man_exp_def Let_def Float_mantissa_exponent int_of_integer_integer_of_int
  apply auto
  subgoal by transfer auto
  subgoal by transfer auto
  done

definition "check_conversion m e =
  (let f = Float (int_of_integer m) (int_of_integer e) in
    do {
      d \<leftarrow> double_of_Float f;
      Float_of_double d
    } = (if is_finite_Float TYPE((11, 52)float) f then Some f else None))"

primrec check_all::"nat \<Rightarrow> (nat \<Rightarrow> bool) \<Rightarrow> bool" where
  "check_all 0 P \<longleftrightarrow> True"
| "check_all (Suc i) P \<longleftrightarrow> P i \<and> check_all i P"

definition "check_conversions dm de =
  check_all (nat (2 * de)) (\<lambda>e. check_all (nat (2 * dm)) (\<lambda>m.
    check_conversion (integer_of_int (int m - dm)) (integer_of_int (int e - de))))"

lemma "check_conversions 100 100"
  by eval

end
