theory FP64
imports
  IEEE
  Word_Lib.Word_Lemmas_64
begin

section \<open>Concrete encodings\<close>

text \<open>Floating point operations defined as operations on words.
  Called ''fixed precision'' (fp) word in HOL4.\<close>

type_synonym float64 = "(11,52)float"
type_synonym fp64 = "64 word"

lift_definition fp64_of_float :: "float64 \<Rightarrow> fp64" is
  "\<lambda>(s::1 word, e::11 word, f::52 word). word_cat s (word_cat e f::63 word)" .

lift_definition float_of_fp64 :: "fp64 \<Rightarrow> float64" is
  "\<lambda>x. apsnd word_split (word_split x::1 word * 63 word)" .

definition "rel_fp64 \<equiv> (\<lambda>x (y::word64). x = float_of_fp64 y)"

definition eq_fp64::"float64 \<Rightarrow> float64 \<Rightarrow> bool" where [simp]: "eq_fp64 \<equiv> (=)"

lemma float_of_fp64_inverse[simp]: "fp64_of_float (float_of_fp64 a) = a"
  by (auto
      simp: fp64_of_float_def float_of_fp64_def Abs_float_inverse apsnd_def map_prod_def word_size
      dest!: word_cat_split_alt[rotated]
      split: prod.splits)

lemma float_of_fp64_inj_iff[simp]: "fp64_of_float r = fp64_of_float s \<longleftrightarrow> r = s"
  using Rep_float_inject
  by (force simp: fp64_of_float_def word_cat_inj word_size split: prod.splits)

lemma fp64_of_float_inverse[simp]: "float_of_fp64 (fp64_of_float a) = a"
  using float_of_fp64_inj_iff float_of_fp64_inverse by blast

lemma Quotientfp: "Quotient eq_fp64 fp64_of_float float_of_fp64 rel_fp64"
  \<comment>\<open>\<^term>\<open>eq_fp64\<close> is a workaround to prevent a (failing -- TODO: why?)
      code setup in \<open>setup_lifting\<close>.\<close>
  by (force intro!: QuotientI simp: rel_fp64_def)

setup_lifting Quotientfp

lift_definition fp64_lessThan::"fp64 \<Rightarrow> fp64 \<Rightarrow> bool" is
  "flt::float64\<Rightarrow>float64\<Rightarrow>bool" by simp

lift_definition fp64_lessEqual::"fp64 \<Rightarrow> fp64 \<Rightarrow> bool" is
  "fle::float64\<Rightarrow>float64\<Rightarrow>bool" by simp

lift_definition fp64_greaterThan::"fp64 \<Rightarrow> fp64 \<Rightarrow> bool" is
  "fgt::float64\<Rightarrow>float64\<Rightarrow>bool" by simp

lift_definition fp64_greaterEqual::"fp64 \<Rightarrow> fp64 \<Rightarrow> bool" is
  "fge::float64\<Rightarrow>float64\<Rightarrow>bool" by simp

lift_definition fp64_equal::"fp64 \<Rightarrow> fp64 \<Rightarrow> bool" is
  "feq::float64\<Rightarrow>float64\<Rightarrow>bool" by simp

lift_definition fp64_abs::"fp64 \<Rightarrow> fp64" is
  "abs::float64\<Rightarrow>float64" by simp

lift_definition fp64_negate::"fp64 \<Rightarrow> fp64" is
  "uminus::float64\<Rightarrow>float64" by simp

lift_definition fp64_sqrt::"roundmode \<Rightarrow> fp64 \<Rightarrow> fp64" is
  "fsqrt::roundmode\<Rightarrow>float64\<Rightarrow>float64" by simp

lift_definition fp64_add::"roundmode \<Rightarrow> fp64 \<Rightarrow> fp64 \<Rightarrow> fp64" is
  "fadd::roundmode\<Rightarrow>float64\<Rightarrow>float64\<Rightarrow>float64" by simp

lift_definition fp64_sub::"roundmode \<Rightarrow> fp64 \<Rightarrow> fp64 \<Rightarrow> fp64" is
  "fsub::roundmode\<Rightarrow>float64\<Rightarrow>float64\<Rightarrow>float64" by simp

lift_definition fp64_mul::"roundmode \<Rightarrow> fp64 \<Rightarrow> fp64 \<Rightarrow> fp64" is
  "fmul::roundmode\<Rightarrow>float64\<Rightarrow>float64\<Rightarrow>float64" by simp

lift_definition fp64_div::"roundmode \<Rightarrow> fp64 \<Rightarrow> fp64 \<Rightarrow> fp64" is
  "fdiv::roundmode\<Rightarrow>float64\<Rightarrow>float64\<Rightarrow>float64" by simp

end
