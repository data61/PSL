section \<open>Data: Integers\<close>

theory Data_Integer
  imports
    Numeral_Cpo
    Data_Bool
begin

domain Integer = MkI (lazy int)

instance Integer :: flat
proof
  fix x y :: Integer
  assume "x \<sqsubseteq> y" then show "x = \<bottom> \<or> x = y"
    by (cases x; cases y) simp_all
qed

instantiation Integer :: "{plus,times,minus,uminus,zero,one}"
begin

definition "0 = MkI\<cdot>0"
definition "1 = MkI\<cdot>1"
definition "a + b = (\<Lambda> (MkI\<cdot>x) (MkI\<cdot>y). MkI\<cdot>(x + y))\<cdot>a\<cdot>b"
definition "a - b = (\<Lambda> (MkI\<cdot>x) (MkI\<cdot>y). MkI\<cdot>(x - y))\<cdot>a\<cdot>b"
definition "a * b = (\<Lambda> (MkI\<cdot>x) (MkI\<cdot>y). MkI\<cdot>(x * y))\<cdot>a\<cdot>b"
definition "- a = (\<Lambda> (MkI\<cdot>x). MkI\<cdot>(uminus x))\<cdot>a"

instance ..

end

lemma Integer_arith_strict [simp]:
  fixes x :: Integer
  shows "\<bottom> + x = \<bottom>" and "x + \<bottom> = \<bottom>"
    and "\<bottom> * x = \<bottom>" and "x * \<bottom> = \<bottom>"
    and "\<bottom> - x = \<bottom>" and "x - \<bottom> = \<bottom>"
    and "- \<bottom> = (\<bottom>::Integer)"
  unfolding plus_Integer_def times_Integer_def
  unfolding minus_Integer_def uminus_Integer_def
  by (cases x, simp, simp)+

lemma Integer_arith_simps [simp]:
  "MkI\<cdot>a + MkI\<cdot>b = MkI\<cdot>(a + b)"
  "MkI\<cdot>a * MkI\<cdot>b = MkI\<cdot>(a * b)"
  "MkI\<cdot>a - MkI\<cdot>b = MkI\<cdot>(a - b)"
  "- MkI\<cdot>a = MkI\<cdot>(uminus a)"
  unfolding plus_Integer_def times_Integer_def
  unfolding minus_Integer_def uminus_Integer_def
  by simp_all

lemma plus_MkI_MkI:
  "MkI\<cdot>x + MkI\<cdot>y = MkI\<cdot>(x + y)"
  unfolding plus_Integer_def by simp

instance Integer :: "{plus_cpo,minus_cpo,times_cpo}"
  by standard (simp_all add: flatdom_strict2cont)

instance Integer :: comm_monoid_add
proof
  fix a b c :: Integer
  show "(a + b) + c = a + (b + c)"
    by (cases a; cases b; cases c) simp_all
  show "a + b = b + a"
    by (cases a; cases b) simp_all
  show "0 + a = a"
    unfolding zero_Integer_def
    by (cases a) simp_all
qed

instance Integer :: comm_monoid_mult
proof
  fix a b c :: Integer
  show "(a * b) * c = a * (b * c)"
    by (cases a; cases b; cases c) simp_all
  show "a * b = b * a"
    by (cases a; cases b) simp_all
  show "1 * a = a"
    unfolding one_Integer_def
    by (cases a) simp_all
qed

instance Integer :: comm_semiring
proof
  fix a b c :: Integer
  show "(a + b) * c = a * c + b * c"
    by (cases a; cases b; cases c) (simp_all add: distrib_right)
qed

instance Integer :: semiring_numeral ..

lemma Integer_add_diff_cancel [simp]:
  "b \<noteq> \<bottom> \<Longrightarrow> (a::Integer) + b - b = a"
  by (cases a; cases b) simp_all

lemma zero_Integer_neq_bottom [simp]: "(0::Integer) \<noteq> \<bottom>"
  by (simp add: zero_Integer_def)

lemma one_Integer_neq_bottom [simp]: "(1::Integer) \<noteq> \<bottom>"
  by (simp add: one_Integer_def)

lemma plus_Integer_eq_bottom_iff [simp]:
  fixes x y :: Integer shows "x + y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x, simp, cases y, simp, simp)

lemma diff_Integer_eq_bottom_iff [simp]:
  fixes x y :: Integer shows "x - y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x, simp, cases y, simp, simp)

lemma mult_Integer_eq_bottom_iff [simp]:
  fixes x y :: Integer shows "x * y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x, simp, cases y, simp, simp)

lemma minus_Integer_eq_bottom_iff [simp]:
  fixes x :: Integer shows "- x = \<bottom> \<longleftrightarrow> x = \<bottom>"
  by (cases x, simp, simp)

lemma numeral_Integer_eq: "numeral k = MkI\<cdot>(numeral k)"
  by (induct k, simp_all only: numeral.simps one_Integer_def plus_MkI_MkI)

lemma numeral_Integer_neq_bottom [simp]: "(numeral k::Integer) \<noteq> \<bottom>"
  unfolding numeral_Integer_eq by simp

text \<open>Symmetric versions are also needed, because the reorient
  simproc does not apply to these comparisons.\<close>

lemma bottom_neq_zero_Integer [simp]: "(\<bottom>::Integer) \<noteq> 0"
  by (simp add: zero_Integer_def)

lemma bottom_neq_one_Integer [simp]: "(\<bottom>::Integer) \<noteq> 1"
  by (simp add: one_Integer_def)

lemma bottom_neq_numeral_Integer [simp]: "(\<bottom>::Integer) \<noteq> numeral k"
  unfolding numeral_Integer_eq by simp

instantiation Integer :: Ord_linear
begin

definition
  "eq = (\<Lambda> (MkI\<cdot>x) (MkI\<cdot>y). if x = y then TT else FF)"

definition
  "compare = (\<Lambda> (MkI\<cdot>x) (MkI\<cdot>y).
    if x < y then LT else if x > y then GT else EQ)"

instance proof
  fix x y z :: Integer
  show "compare\<cdot>\<bottom>\<cdot>y = \<bottom>"
    unfolding compare_Integer_def by simp
  show "compare\<cdot>x\<cdot>\<bottom> = \<bottom>"
    unfolding compare_Integer_def by (cases x, simp_all)
  show "oppOrdering\<cdot>(compare\<cdot>x\<cdot>y) = compare\<cdot>y\<cdot>x"
    unfolding compare_Integer_def
    by (cases x, cases y, simp, simp,
        cases y, simp, simp add: not_less less_imp_le)
  { assume "compare\<cdot>x\<cdot>y = EQ" then show "x = y"
      unfolding compare_Integer_def
      by (cases x, cases y, simp, simp,
          cases y, simp, simp split: if_splits) }
  { assume "compare\<cdot>x\<cdot>y = LT" and "compare\<cdot>y\<cdot>z = LT" then show "compare\<cdot>x\<cdot>z = LT"
      unfolding compare_Integer_def
      by (cases x, simp, cases y, simp, cases z, simp,
          auto split: if_splits) }
  show "eq\<cdot>x\<cdot>y = is_EQ\<cdot>(compare\<cdot>x\<cdot>y)"
    unfolding eq_Integer_def compare_Integer_def
    by (cases x, simp, cases y, simp, auto)
  show "compare\<cdot>x\<cdot>x \<sqsubseteq> EQ"
    unfolding compare_Integer_def
    by (cases x, simp_all)
qed

end

lemma eq_MkI_MkI [simp]:
  "eq\<cdot>(MkI\<cdot>m)\<cdot>(MkI\<cdot>n) = (if m = n then TT else FF)"
  by (simp add: eq_Integer_def)

lemma compare_MkI_MkI [simp]:
  "compare\<cdot>(MkI\<cdot>x)\<cdot>(MkI\<cdot>y) = (if x < y then LT else if x > y then GT else EQ)"
  unfolding compare_Integer_def by simp

lemma lt_MkI_MkI [simp]:
  "lt\<cdot>(MkI\<cdot>x)\<cdot>(MkI\<cdot>y) = (if x < y then TT else FF)"
  unfolding lt_def by simp

lemma le_MkI_MkI [simp]:
  "le\<cdot>(MkI\<cdot>x)\<cdot>(MkI\<cdot>y) = (if x \<le> y then TT else FF)"
  unfolding le_def by simp

lemma eq_Integer_bottom_iff [simp]:
  fixes x y :: Integer shows "eq\<cdot>x\<cdot>y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x, simp, cases y, simp, simp)

lemma compare_Integer_bottom_iff [simp]:
  fixes x y :: Integer shows "compare\<cdot>x\<cdot>y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x, simp, cases y, simp, simp)

lemma lt_Integer_bottom_iff [simp]:
  fixes x y :: Integer shows "lt\<cdot>x\<cdot>y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x, simp, cases y, simp, simp)

lemma le_Integer_bottom_iff [simp]:
  fixes x y :: Integer shows "le\<cdot>x\<cdot>y = \<bottom> \<longleftrightarrow> x = \<bottom> \<or> y = \<bottom>"
  by (cases x, simp, cases y, simp, simp)

lemma compare_refl_Integer [simp]:
  "(x::Integer) \<noteq> \<bottom> \<Longrightarrow> compare\<cdot>x\<cdot>x = EQ"
  by (cases x) simp_all

lemma eq_refl_Integer [simp]:
  "(x::Integer) \<noteq> \<bottom> \<Longrightarrow> eq\<cdot>x\<cdot>x = TT"
  by (cases x) simp_all

lemma lt_refl_Integer [simp]:
  "(x::Integer) \<noteq> \<bottom> \<Longrightarrow> lt\<cdot>x\<cdot>x = FF"
  by (cases x) simp_all

lemma le_refl_Integer [simp]:
  "(x::Integer) \<noteq> \<bottom> \<Longrightarrow> le\<cdot>x\<cdot>x = TT"
  by (cases x) simp_all

lemma eq_Integer_numeral_simps [simp]:
  "eq\<cdot>(0::Integer)\<cdot>0 = TT"
  "eq\<cdot>(0::Integer)\<cdot>1 = FF"
  "eq\<cdot>(1::Integer)\<cdot>0 = FF"
  "eq\<cdot>(1::Integer)\<cdot>1 = TT"
  "eq\<cdot>(0::Integer)\<cdot>(numeral k) = FF"
  "eq\<cdot>(numeral k)\<cdot>(0::Integer) = FF"
  "k \<noteq> Num.One \<Longrightarrow> eq\<cdot>(1::Integer)\<cdot>(numeral k) = FF"
  "k \<noteq> Num.One \<Longrightarrow> eq\<cdot>(numeral k)\<cdot>(1::Integer) = FF"
  "eq\<cdot>(numeral k::Integer)\<cdot>(numeral l) = (if k = l then TT else FF)"
  unfolding zero_Integer_def one_Integer_def numeral_Integer_eq
  by simp_all

lemma compare_Integer_numeral_simps [simp]:
  "compare\<cdot>(0::Integer)\<cdot>0 = EQ"
  "compare\<cdot>(0::Integer)\<cdot>1 = LT"
  "compare\<cdot>(1::Integer)\<cdot>0 = GT"
  "compare\<cdot>(1::Integer)\<cdot>1 = EQ"
  "compare\<cdot>(0::Integer)\<cdot>(numeral k) = LT"
  "compare\<cdot>(numeral k)\<cdot>(0::Integer) = GT"
  "Num.One < k \<Longrightarrow> compare\<cdot>(1::Integer)\<cdot>(numeral k) = LT"
  "Num.One < k \<Longrightarrow> compare\<cdot>(numeral k)\<cdot>(1::Integer) = GT"
  "compare\<cdot>(numeral k::Integer)\<cdot>(numeral l) =
    (if k < l then LT else if k > l then GT else EQ)"
  unfolding zero_Integer_def one_Integer_def numeral_Integer_eq
  by simp_all

lemma lt_Integer_numeral_simps [simp]:
  "lt\<cdot>(0::Integer)\<cdot>0 = FF"
  "lt\<cdot>(0::Integer)\<cdot>1 = TT"
  "lt\<cdot>(1::Integer)\<cdot>0 = FF"
  "lt\<cdot>(1::Integer)\<cdot>1 = FF"
  "lt\<cdot>(0::Integer)\<cdot>(numeral k) = TT"
  "lt\<cdot>(numeral k)\<cdot>(0::Integer) = FF"
  "Num.One < k \<Longrightarrow> lt\<cdot>(1::Integer)\<cdot>(numeral k) = TT"
  "lt\<cdot>(numeral k)\<cdot>(1::Integer) = FF"
  "lt\<cdot>(numeral k::Integer)\<cdot>(numeral l) = (if k < l then TT else FF)"
  unfolding zero_Integer_def one_Integer_def numeral_Integer_eq
  by simp_all

lemma le_Integer_numeral_simps [simp]:
  "le\<cdot>(0::Integer)\<cdot>0 = TT"
  "le\<cdot>(0::Integer)\<cdot>1 = TT"
  "le\<cdot>(1::Integer)\<cdot>0 = FF"
  "le\<cdot>(1::Integer)\<cdot>1 = TT"
  "le\<cdot>(0::Integer)\<cdot>(numeral k) = TT"
  "le\<cdot>(numeral k)\<cdot>(0::Integer) = FF"
  "le\<cdot>(1::Integer)\<cdot>(numeral k) = TT"
  "Num.One < k \<Longrightarrow> le\<cdot>(numeral k)\<cdot>(1::Integer) = FF"
  "le\<cdot>(numeral k::Integer)\<cdot>(numeral l) = (if k \<le> l then TT else FF)"
  unfolding zero_Integer_def one_Integer_def numeral_Integer_eq
  by simp_all

lemma MkI_eq_0_iff [simp]: "MkI\<cdot>n = 0 \<longleftrightarrow> n = 0"
  unfolding zero_Integer_def by simp

lemma MkI_eq_1_iff [simp]: "MkI\<cdot>n = 1 \<longleftrightarrow> n = 1"
  unfolding one_Integer_def by simp

lemma MkI_eq_numeral_iff [simp]: "MkI\<cdot>n = numeral k \<longleftrightarrow> n = numeral k"
  unfolding numeral_Integer_eq by simp

lemma MkI_0: "MkI\<cdot>0 = 0"
  by simp

lemma MkI_1: "MkI\<cdot>1 = 1"
  by simp

lemma le_plus_1:
  fixes m :: "Integer"
  assumes "le\<cdot>m\<cdot>n = TT"
  shows "le\<cdot>m\<cdot>(n + 1) = TT"
proof -
  from assms have "n \<noteq> \<bottom>" by auto
  then have "le\<cdot>n\<cdot>(n + 1) = TT"
    by (cases n) (auto, metis le_MkI_MkI less_add_one less_le_not_le one_Integer_def plus_MkI_MkI)
  with assms show ?thesis by (auto dest: le_trans)
qed

subsection \<open>Induction rules that do not break the abstraction\<close>

lemma nonneg_Integer_induct [consumes 1, case_names 0 step]:
  fixes i :: Integer
  assumes i_nonneg: "le\<cdot>0\<cdot>i = TT"
    and zero: "P 0"
    and step: "\<And>i. le\<cdot>1\<cdot>i = TT \<Longrightarrow> P (i - 1) \<Longrightarrow> P i"
  shows "P i"
proof (cases i)
  case bottom
  then have False using i_nonneg by simp
  then show ?thesis ..
next
  case (MkI integer)
  show ?thesis
  proof (cases integer)
    case neg
    then have False using i_nonneg MkI by (auto simp add: zero_Integer_def one_Integer_def)
    then show ?thesis ..
  next
    case (nonneg nat)
    have "P (MkI\<cdot>(int nat))"
    proof(induct nat)
      case 0
      show ?case using zero by (simp add: zero_Integer_def)
    next
      case (Suc nat)
      have "le\<cdot>1\<cdot>(MkI\<cdot>(int (Suc nat))) = TT"
        by (simp add: one_Integer_def)
      moreover
      have "P (MkI\<cdot>(int (Suc nat)) - 1)"
        using Suc
        by (simp add: one_Integer_def)
      ultimately
      show ?case
        by (rule step)
    qed
    then show ?thesis using nonneg MkI by simp
  qed
qed

end