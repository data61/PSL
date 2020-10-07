(* Formalization of IEEE-754 Standard for binary floating-point arithmetic *)
(* Author: Lei Yu, University of Cambridge *)

section \<open>Specification of the IEEE standard\<close>

theory IEEE
  imports
    "HOL-Library.Float"
    Word_Lib.Word_Lemmas
begin

typedef (overloaded) ('e::len, 'f::len) float = "UNIV::(1 word \<times> 'e word \<times> 'f word) set"
  by auto

setup_lifting type_definition_float

syntax "_float" :: "type \<Rightarrow> type \<Rightarrow> type" ("'(_, _') float")
text \<open>parse \<open>('a, 'b) float\<close> as ('a::len, 'b::len) float.\<close>

parse_translation \<open>
  let
    fun float t u = Syntax.const @{type_syntax float} $ t $ u;
    fun len_tr u =
      (case Term_Position.strip_positions u of
        v as Free (x, _) =>
          if Lexicon.is_tid x then
            (Syntax.const @{syntax_const "_ofsort"} $ v $
              Syntax.const @{class_syntax len})
          else u
      | _ => u)
    fun len_float_tr [t, u] =
      float (len_tr t) (len_tr u)
  in
    [(@{syntax_const "_float"}, K len_float_tr)]
  end
\<close>

subsection \<open>Derived parameters for floating point formats\<close>

definition wordlength :: "('e, 'f) float itself \<Rightarrow> nat"
  where "wordlength x = LENGTH('e) + LENGTH('f) + 1"

definition bias :: "('e, 'f) float itself \<Rightarrow> nat"
  where "bias x = 2^(LENGTH('e) - 1) - 1"

definition emax :: "('e, 'f) float itself \<Rightarrow> nat"
  where "emax x = unat(max_word::'e word)"

abbreviation fracwidth::"('e, 'f) float itself \<Rightarrow> nat" where
  "fracwidth _ \<equiv> LENGTH('f)"

subsection \<open>Predicates for the four IEEE formats\<close>

definition is_single :: "('e, 'f) float itself \<Rightarrow> bool"
  where "is_single x \<longleftrightarrow> LENGTH('e) = 8 \<and> wordlength x = 32"

definition is_double :: "('e, 'f) float itself \<Rightarrow> bool"
  where "is_double x \<longleftrightarrow> LENGTH('e) = 11 \<and> wordlength x = 64"

definition is_single_extended :: "('e, 'f) float itself \<Rightarrow> bool"
  where "is_single_extended x \<longleftrightarrow> LENGTH('e) \<ge> 11 \<and> wordlength x \<ge> 43"

definition is_double_extended :: "('e, 'f) float itself \<Rightarrow> bool"
  where "is_double_extended x \<longleftrightarrow> LENGTH('e) \<ge> 15 \<and> wordlength x \<ge> 79"


subsection \<open>Extractors for fields\<close>

lift_definition sign::"('e, 'f) float \<Rightarrow> nat" is
  "\<lambda>(s::1 word, _::'e word, _::'f word). unat s" .

lift_definition exponent::"('e, 'f) float \<Rightarrow> nat" is
  "\<lambda>(_, e::'e word, _). unat e" .

lift_definition fraction::"('e, 'f) float \<Rightarrow> nat" is
  "\<lambda>(_, _, f::'f word). unat f" .

abbreviation "real_of_word x \<equiv> real (unat x)"

lift_definition valof :: "('e, 'f) float \<Rightarrow> real"
is "\<lambda>(s, e, f).
    let x = (TYPE(('e, 'f) float)) in
    (if e = 0
     then (-1::real)^(unat s) * (2 / (2^bias x)) * (real_of_word f/2^(LENGTH('f)))
     else (-1::real)^(unat s) * ((2^(unat e)) / (2^bias x)) * (1 + real_of_word f/2^LENGTH('f)))"
  .

subsection \<open>Partition of numbers into disjoint classes\<close>

definition is_nan :: "('e, 'f) float \<Rightarrow> bool"
  where "is_nan a \<longleftrightarrow> exponent a = emax TYPE(('e, 'f)float) \<and> fraction a \<noteq> 0"

definition is_infinity :: "('e, 'f) float \<Rightarrow> bool"
  where "is_infinity a \<longleftrightarrow> exponent a = emax TYPE(('e, 'f)float) \<and> fraction a = 0"

definition is_normal :: "('e, 'f) float \<Rightarrow> bool"
  where "is_normal a \<longleftrightarrow> 0 < exponent a \<and> exponent a < emax TYPE(('e, 'f)float)"

definition is_denormal :: "('e, 'f) float \<Rightarrow> bool"
  where "is_denormal a \<longleftrightarrow> exponent a = 0 \<and> fraction a \<noteq> 0"

definition is_zero :: "('e, 'f) float \<Rightarrow> bool"
  where "is_zero a \<longleftrightarrow> exponent a = 0 \<and> fraction a = 0"

definition is_finite :: "('e, 'f) float \<Rightarrow> bool"
  where "is_finite a \<longleftrightarrow> (is_normal a \<or> is_denormal a \<or> is_zero a)"


subsection \<open>Special values\<close>

lift_definition plus_infinity :: "('e, 'f) float" ("\<infinity>") is "(0, max_word, 0)" .

lift_definition topfloat :: "('e, 'f) float" is "(0, max_word - 1, 2^LENGTH('f) - 1)" .

instantiation float::(len, len) zero begin

lift_definition zero_float :: "('e, 'f) float" is "(0, 0, 0)" .

instance proof qed

end

subsection \<open>Negation operation on floating point values\<close>

instantiation float::(len, len) uminus begin
lift_definition uminus_float :: "('e, 'f) float \<Rightarrow> ('e, 'f) float" is  "\<lambda>(s, e, f). (1 - s, e, f)" .
instance proof qed
end

abbreviation (input) "minus_zero \<equiv> - (0::('e, 'f)float)"
abbreviation (input) "minus_infinity \<equiv> - \<infinity>"
abbreviation (input) "bottomfloat \<equiv> - topfloat"


subsection \<open>Real number valuations\<close>

text \<open>The largest value that can be represented in floating point format.\<close>
definition largest :: "('e, 'f) float itself \<Rightarrow> real"
  where "largest x = (2^(emax x - 1) / 2^bias x) * (2 - 1/(2^fracwidth x))"

text \<open>Threshold, used for checking overflow.\<close>
definition threshold :: "('e, 'f) float itself \<Rightarrow> real"
  where "threshold x = (2^(emax x - 1) / 2^bias x) * (2 - 1/(2^(Suc(fracwidth x))))"

text \<open>Unit of least precision.\<close>

lift_definition one_lp::"('e ,'f) float \<Rightarrow> ('e ,'f) float" is "\<lambda>(s, e, f). (0, e::'e word, 1)" .
lift_definition zero_lp::"('e ,'f) float \<Rightarrow> ('e ,'f) float" is "\<lambda>(s, e, f). (0, e::'e word, 0)" .

definition ulp :: "('e, 'f) float \<Rightarrow> real" where "ulp a = valof (one_lp a) - valof (zero_lp a)"

text \<open>Enumerated type for rounding modes.\<close>
datatype roundmode = To_nearest | float_To_zero | To_pinfinity | To_ninfinity

text \<open>Characterization of best approximation from a set of abstract values.\<close>
definition "is_closest v s x a \<longleftrightarrow> a \<in> s \<and> (\<forall>b. b \<in> s \<longrightarrow> \<bar>v a - x\<bar> \<le> \<bar>v b - x\<bar>)"

text \<open>Best approximation with a deciding preference for multiple possibilities.\<close>
definition "closest v p s x =
  (SOME a. is_closest v s x a \<and> ((\<exists>b. is_closest v s x b \<and> p b) \<longrightarrow> p a))"


subsection \<open>Rounding\<close>

fun round :: "roundmode \<Rightarrow> real \<Rightarrow> ('e ,'f) float"
where
  "round To_nearest y =
   (if y \<le> - threshold TYPE(('e ,'f) float) then minus_infinity
    else if y \<ge> threshold TYPE(('e ,'f) float) then plus_infinity
    else closest (valof) (\<lambda>a. even (fraction a)) {a. is_finite a} y)"
| "round float_To_zero y =
   (if y < - largest TYPE(('e ,'f) float) then bottomfloat
    else if y > largest TYPE(('e ,'f) float) then topfloat
    else closest (valof) (\<lambda>a. True) {a. is_finite a \<and> \<bar>valof a\<bar> \<le> \<bar>y\<bar>} y)"
| "round To_pinfinity y =
   (if y < - largest TYPE(('e ,'f) float) then bottomfloat
    else if y > largest TYPE(('e ,'f) float) then plus_infinity
    else closest (valof) (\<lambda>a. True) {a. is_finite a \<and> valof a \<ge> y} y)"
| "round To_ninfinity y =
   (if y < - largest TYPE(('e ,'f) float) then minus_infinity
    else if y > largest TYPE(('e ,'f) float) then topfloat
    else closest (valof) (\<lambda>a. True) {a. is_finite a \<and> valof a \<le> y} y)"

text \<open>Rounding to integer values in floating point format.\<close>

definition is_integral :: "('e ,'f) float \<Rightarrow> bool"
  where "is_integral a \<longleftrightarrow> is_finite a \<and> (\<exists>n::nat. \<bar>valof a\<bar> = real n)"

fun intround :: "roundmode \<Rightarrow> real \<Rightarrow> ('e ,'f) float"
where
  "intround To_nearest y =
    (if y \<le> - threshold TYPE(('e ,'f) float) then minus_infinity
     else if y \<ge> threshold TYPE(('e ,'f) float) then plus_infinity
     else closest (valof) (\<lambda>a. (\<exists>n::nat. even n \<and> \<bar>valof a\<bar> = real n)) {a. is_integral a} y)"
|"intround float_To_zero y =
    (if y < - largest TYPE(('e ,'f) float) then bottomfloat
     else if y > largest TYPE(('e ,'f) float) then topfloat
     else closest (valof) (\<lambda>x. True) {a. is_integral a \<and> \<bar>valof a\<bar> \<le> \<bar>y\<bar>} y)"
|"intround To_pinfinity y =
    (if y < - largest TYPE(('e ,'f) float) then bottomfloat
     else if y > largest TYPE(('e ,'f) float) then plus_infinity
     else closest (valof) (\<lambda>x. True) {a. is_integral a \<and> valof a \<ge> y} y)"
|"intround To_ninfinity y =
    (if y < - largest TYPE(('e ,'f) float) then minus_infinity
     else if y > largest TYPE(('e ,'f) float) then topfloat
     else closest (valof) (\<lambda>x. True) {a. is_integral a \<and> valof a \<ge> y} y)"

text \<open>Non-standard of NaN.\<close>
definition some_nan :: "('e ,'f) float"
  where "some_nan = (SOME a. is_nan a)"

text \<open>Coercion for signs of zero results.\<close>
definition zerosign :: "nat \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float"
  where "zerosign s a =
    (if is_zero a then (if s = 0 then 0 else - 0) else a)"

text \<open>Remainder operation.\<close>
definition rem :: "real \<Rightarrow> real \<Rightarrow> real"
  where "rem x y =
    (let n = closest id (\<lambda>x. \<exists>n::nat. even n \<and> \<bar>x\<bar> = real n) {x. \<exists>n :: nat. \<bar>x\<bar> = real n} (x / y)
     in x - n * y)"

definition frem :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float"
  where "frem m a b =
    (if is_nan a \<or> is_nan b \<or> is_infinity a \<or> is_zero b then some_nan
     else zerosign (sign a) (round m (rem (valof a) (valof b))))"


subsection \<open>Definitions of the arithmetic operations\<close>

definition fintrnd :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float"
  where "fintrnd m a =
    (if is_nan a then (some_nan)
     else if is_infinity a then a
     else zerosign (sign a) (intround m (valof a)))"

definition fadd :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float"
  where "fadd m a b =
    (if is_nan a \<or> is_nan b \<or> (is_infinity a \<and> is_infinity b \<and> sign a \<noteq> sign b)
     then some_nan
     else if (is_infinity a) then a
     else if (is_infinity b) then b
     else
      zerosign
        (if is_zero a \<and> is_zero b \<and> sign a = sign b then sign a
         else if m = To_ninfinity then 1 else 0)
        (round m (valof a + valof b)))"

definition fsub :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float"
  where "fsub m a b =
    (if is_nan a \<or> is_nan b \<or> (is_infinity a \<and> is_infinity b \<and> sign a = sign b)
     then some_nan
     else if is_infinity a then a
     else if is_infinity b then - b
     else
      zerosign
        (if is_zero a \<and> is_zero b \<and> sign a \<noteq> sign b then sign a
         else if m = To_ninfinity then 1 else 0)
        (round m (valof a - valof b)))"

definition fmul :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float"
  where "fmul m a b =
    (if is_nan a \<or> is_nan b \<or> (is_zero a \<and> is_infinity b) \<or> (is_infinity a \<and> is_zero b)
     then some_nan
     else if is_infinity a \<or> is_infinity b
     then (if sign a = sign b then plus_infinity else minus_infinity)
     else zerosign (if sign a = sign b then 0 else 1 ) (round m (valof a * valof b)))"

definition fdiv :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float"
  where "fdiv m a b =
    (if is_nan a \<or> is_nan b \<or> (is_zero a \<and> is_zero b) \<or> (is_infinity a \<and> is_infinity b)
     then some_nan
     else if is_infinity a \<or> is_zero b
     then (if sign a = sign b then plus_infinity else minus_infinity)
     else if is_infinity b
     then (if sign a = sign b then 0 else - 0)
     else zerosign (if sign a = sign b then 0 else 1) (round m (valof a / valof b)))"

definition fsqrt :: "roundmode \<Rightarrow> ('e ,'f) float \<Rightarrow> ('e ,'f) float"
  where "fsqrt m a =
    (if is_nan a then some_nan
     else if is_zero a \<or> is_infinity a \<and> sign a = 0 then a
     else if sign a = 1 then some_nan
     else zerosign (sign a) (round m (sqrt (valof a))))"


subsection \<open>Comparison operations\<close>

datatype ccode = Gt | Lt | Eq | Und

definition fcompare :: "('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> ccode"
  where "fcompare a b =
    (if is_nan a \<or> is_nan b then Und
     else if is_infinity a \<and> sign a = 1
     then (if is_infinity b \<and> sign b = 1 then Eq else Lt)
     else if is_infinity a \<and> sign a = 0
     then (if is_infinity b \<and> sign b = 0 then Eq else Gt)
     else if is_infinity b \<and> sign b = 1 then Gt
     else if is_infinity b \<and> sign b = 0 then Lt
     else if valof a < valof b then Lt
     else if valof a = valof b then Eq
     else Gt)"

definition flt :: "('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> bool"
  where "flt a b \<longleftrightarrow> fcompare a b = Lt"

definition fle :: "('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> bool"
  where "fle a b \<longleftrightarrow> fcompare a b = Lt \<or> fcompare a b = Eq"

definition fgt :: "('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> bool"
  where "fgt a b \<longleftrightarrow> fcompare a b = Gt"

definition fge :: "('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> bool"
  where "fge a b \<longleftrightarrow> fcompare a b = Gt \<or> fcompare a b = Eq"

definition feq :: "('e ,'f) float \<Rightarrow> ('e ,'f) float \<Rightarrow> bool"
  where "feq a b \<longleftrightarrow> fcompare a b = Eq"


section \<open>Specify float to be double  precision and round to even\<close>

instantiation float :: (len, len) plus
begin

definition plus_float :: "('a, 'b) float \<Rightarrow> ('a, 'b) float \<Rightarrow> ('a, 'b) float"
  where "a + b = fadd To_nearest a b"

instance ..

end

instantiation float :: (len, len) minus
begin

definition minus_float :: "('a, 'b) float \<Rightarrow> ('a, 'b) float \<Rightarrow> ('a, 'b) float"
  where "a - b = fsub To_nearest a b"

instance ..

end

instantiation float :: (len, len) times
begin

definition times_float :: "('a, 'b) float \<Rightarrow> ('a, 'b) float \<Rightarrow> ('a, 'b) float"
  where "a * b = fmul To_nearest a b"

instance ..

end

instantiation float :: (len, len) one
begin

lift_definition one_float :: "('a, 'b) float" is "(0, 2^(LENGTH('a) - 1) - 1, 0)" .

instance ..

end

instantiation float :: (len, len) inverse
begin

definition divide_float :: "('a, 'b) float \<Rightarrow> ('a, 'b) float \<Rightarrow> ('a, 'b) float"
  where "a div b = fdiv To_nearest a b"

definition inverse_float :: "('a, 'b) float \<Rightarrow> ('a, 'b) float"
  where "inverse_float a = fdiv To_nearest 1 a"

instance ..

end

definition float_rem :: "('a, 'b) float \<Rightarrow> ('a, 'b) float \<Rightarrow> ('a, 'b) float"
  where "float_rem a b = frem To_nearest a b"

definition float_sqrt :: "('a, 'b) float \<Rightarrow> ('a, 'b) float"
  where "float_sqrt a = fsqrt To_nearest a"

definition ROUNDFLOAT ::"('a, 'b) float \<Rightarrow> ('a, 'b) float"
  where "ROUNDFLOAT a = fintrnd To_nearest a"


instantiation float :: (len, len) ord
begin

definition less_float :: "('a, 'b) float \<Rightarrow> ('a, 'b) float \<Rightarrow> bool"
  where "a < b \<longleftrightarrow> flt a b"

definition less_eq_float :: "('a, 'b) float \<Rightarrow> ('a, 'b) float \<Rightarrow> bool"
  where "a \<le> b \<longleftrightarrow> fle a b"

instance ..

end

definition float_eq :: "('a, 'b) float \<Rightarrow> ('a, 'b) float \<Rightarrow> bool"  (infixl "\<doteq>" 70)
  where "float_eq a b = feq a b"

instantiation float :: (len, len) abs
begin

definition abs_float :: "('a, 'b) float \<Rightarrow> ('a, 'b) float"
  where "abs_float a = (if sign a = 0 then a else - a)"

instance ..
end

text \<open>The \<open>1 + \<epsilon>\<close> property.\<close>
definition normalizes :: "_ itself \<Rightarrow> real \<Rightarrow> bool"
  where "normalizes float_format x =
    (1/ (2::real)^(bias float_format - 1) \<le> \<bar>x\<bar> \<and> \<bar>x\<bar> < threshold float_format)"

end
