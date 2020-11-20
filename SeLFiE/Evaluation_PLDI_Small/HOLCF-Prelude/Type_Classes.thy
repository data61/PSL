section \<open>Type Classes\<close>

theory Type_Classes
  imports HOLCF_Main
begin


subsection \<open>Eq class\<close>

class Eq =
  fixes eq :: "'a \<rightarrow> 'a \<rightarrow> tr"

text \<open>
  The Haskell type class does allow /= to be specified separately. For now, we assume
  that all modeled type classes use the default implementation, or an equivalent.
\<close>
fixrec neq :: "'a::Eq \<rightarrow> 'a \<rightarrow> tr" where
  "neq\<cdot>x\<cdot>y = neg\<cdot>(eq\<cdot>x\<cdot>y)"

class Eq_strict = Eq +
  assumes eq_strict [simp]:
    "eq\<cdot>x\<cdot>\<bottom> = \<bottom>"
    "eq\<cdot>\<bottom>\<cdot>y = \<bottom>"

class Eq_sym = Eq_strict +
  assumes eq_sym: "eq\<cdot>x\<cdot>y = eq\<cdot>y\<cdot>x"

class Eq_equiv = Eq_sym +
  assumes eq_self_neq_FF [simp]: "eq\<cdot>x\<cdot>x \<noteq> FF"
    and eq_trans: "eq\<cdot>x\<cdot>y = TT \<Longrightarrow> eq\<cdot>y\<cdot>z = TT \<Longrightarrow> eq\<cdot>x\<cdot>z = TT"
begin

lemma eq_refl: "eq\<cdot>x\<cdot>x \<noteq> \<bottom> \<Longrightarrow> eq\<cdot>x\<cdot>x = TT"
  by (cases "eq\<cdot>x\<cdot>x") simp+

end

class Eq_eq = Eq_sym +
  assumes eq_self_neq_FF': "eq\<cdot>x\<cdot>x \<noteq> FF"
    and eq_TT_dest: "eq\<cdot>x\<cdot>y = TT \<Longrightarrow> x = y"
begin

subclass Eq_equiv
  by standard (auto simp: eq_self_neq_FF' dest: eq_TT_dest)

lemma eqD [dest]:
  "eq\<cdot>x\<cdot>y = TT \<Longrightarrow> x = y"
  "eq\<cdot>x\<cdot>y = FF \<Longrightarrow> x \<noteq> y"
  by (auto elim: eq_TT_dest)

end

subsubsection \<open>Class instances\<close>

instantiation lift :: (countable) Eq_eq
begin

definition "eq \<equiv> (\<Lambda>(Def x) (Def y). Def (x = y))"

instance
  by standard (auto simp: eq_lift_def flift1_def split: lift.splits)

end

lemma eq_ONE_ONE [simp]: "eq\<cdot>ONE\<cdot>ONE = TT"
  unfolding ONE_def eq_lift_def by simp


subsection \<open>Ord class\<close>

domain Ordering = LT | EQ | GT

definition oppOrdering :: "Ordering \<rightarrow> Ordering" where
  "oppOrdering = (\<Lambda> x. case x of LT \<Rightarrow> GT | EQ \<Rightarrow> EQ | GT \<Rightarrow> LT)"

lemma oppOrdering_simps [simp]:
  "oppOrdering\<cdot>LT = GT"
  "oppOrdering\<cdot>EQ = EQ"
  "oppOrdering\<cdot>GT = LT"
  "oppOrdering\<cdot>\<bottom> = \<bottom>"
  unfolding oppOrdering_def by simp_all

class Ord = Eq +
  fixes compare :: "'a \<rightarrow> 'a \<rightarrow> Ordering"
begin

definition lt :: "'a \<rightarrow> 'a \<rightarrow> tr" where
  "lt = (\<Lambda> x y. case compare\<cdot>x\<cdot>y of LT \<Rightarrow> TT | EQ \<Rightarrow> FF | GT \<Rightarrow> FF)"

definition le :: "'a \<rightarrow> 'a \<rightarrow> tr" where
  "le = (\<Lambda> x y. case compare\<cdot>x\<cdot>y of LT \<Rightarrow> TT | EQ \<Rightarrow> TT | GT \<Rightarrow> FF)"

lemma lt_eq_TT_iff: "lt\<cdot>x\<cdot>y = TT \<longleftrightarrow> compare\<cdot>x\<cdot>y = LT"
  by (cases "compare\<cdot>x\<cdot>y") (simp add: lt_def)+

end

class Ord_strict = Ord +
  assumes compare_strict [simp]:
    "compare\<cdot>\<bottom>\<cdot>y = \<bottom>"
    "compare\<cdot>x\<cdot>\<bottom> = \<bottom>"
begin

lemma lt_strict [simp]:
  shows "lt\<cdot>\<bottom>\<cdot>x = \<bottom>"
    and "lt\<cdot>x\<cdot>\<bottom> = \<bottom>"
  by (simp add: lt_def)+

lemma le_strict [simp]:
  shows "le\<cdot>\<bottom>\<cdot>x = \<bottom>"
    and "le\<cdot>x\<cdot>\<bottom> = \<bottom>"
  by (simp add: le_def)+

end

text \<open>TODO: It might make sense to have a class for preorders too,
analogous to class \<open>eq_equiv\<close>.\<close>

class Ord_linear = Ord_strict +
  assumes eq_conv_compare: "eq\<cdot>x\<cdot>y = is_EQ\<cdot>(compare\<cdot>x\<cdot>y)"
    and oppOrdering_compare [simp]:
    "oppOrdering\<cdot>(compare\<cdot>x\<cdot>y) = compare\<cdot>y\<cdot>x"
    and compare_EQ_dest: "compare\<cdot>x\<cdot>y = EQ \<Longrightarrow> x = y"
    and compare_self_below_EQ: "compare\<cdot>x\<cdot>x \<sqsubseteq> EQ"
    and compare_LT_trans:
    "compare\<cdot>x\<cdot>y = LT \<Longrightarrow> compare\<cdot>y\<cdot>z = LT \<Longrightarrow> compare\<cdot>x\<cdot>z = LT"
  (*BH: Is this set of axioms complete?*)
  (*CS: How about totality of the order?*)
begin

lemma eq_TT_dest: "eq\<cdot>x\<cdot>y = TT \<Longrightarrow> x = y"
  by (cases "compare\<cdot>x\<cdot>y") (auto dest: compare_EQ_dest simp: eq_conv_compare)+

lemma le_iff_lt_or_eq:
  "le\<cdot>x\<cdot>y = TT \<longleftrightarrow> lt\<cdot>x\<cdot>y = TT \<or> eq\<cdot>x\<cdot>y = TT"
  by (cases "compare\<cdot>x\<cdot>y") (simp add: le_def lt_def eq_conv_compare)+

lemma compare_sym:
  "compare\<cdot>x\<cdot>y = (case compare\<cdot>y\<cdot>x of LT \<Rightarrow> GT | EQ \<Rightarrow> EQ | GT \<Rightarrow> LT)"
  by (subst oppOrdering_compare [symmetric]) (simp add: oppOrdering_def)

lemma compare_self_neq_LT [simp]: "compare\<cdot>x\<cdot>x \<noteq> LT"
  using compare_self_below_EQ [of x] by clarsimp

lemma compare_self_neq_GT [simp]: "compare\<cdot>x\<cdot>x \<noteq> GT"
  using compare_self_below_EQ [of x] by clarsimp

declare compare_self_below_EQ [simp]

lemma lt_trans: "lt\<cdot>x\<cdot>y = TT \<Longrightarrow> lt\<cdot>y\<cdot>z = TT \<Longrightarrow> lt\<cdot>x\<cdot>z = TT"
  unfolding lt_eq_TT_iff by (rule compare_LT_trans)

lemma compare_GT_iff_LT: "compare\<cdot>x\<cdot>y = GT \<longleftrightarrow> compare\<cdot>y\<cdot>x = LT"
  by (cases "compare\<cdot>x\<cdot>y", simp_all add: compare_sym [of y x])

lemma compare_GT_trans:
  "compare\<cdot>x\<cdot>y = GT \<Longrightarrow> compare\<cdot>y\<cdot>z = GT \<Longrightarrow> compare\<cdot>x\<cdot>z = GT"
  unfolding compare_GT_iff_LT by (rule compare_LT_trans)

lemma compare_EQ_iff_eq_TT:
  "compare\<cdot>x\<cdot>y = EQ \<longleftrightarrow> eq\<cdot>x\<cdot>y = TT"
  by (cases "compare\<cdot>x\<cdot>y") (simp add: is_EQ_def eq_conv_compare)+

lemma compare_EQ_trans:
  "compare\<cdot>x\<cdot>y = EQ \<Longrightarrow> compare\<cdot>y\<cdot>z = EQ \<Longrightarrow> compare\<cdot>x\<cdot>z = EQ"
  by (blast dest: compare_EQ_dest)

lemma le_trans:
  "le\<cdot>x\<cdot>y = TT \<Longrightarrow> le\<cdot>y\<cdot>z = TT \<Longrightarrow> le\<cdot>x\<cdot>z = TT"
  by (auto dest: eq_TT_dest lt_trans simp: le_iff_lt_or_eq)

lemma neg_lt: "neg\<cdot>(lt\<cdot>x\<cdot>y) = le\<cdot>y\<cdot>x"
  by (cases "compare\<cdot>x\<cdot>y", simp_all add: le_def lt_def compare_sym [of y x])

lemma neg_le: "neg\<cdot>(le\<cdot>x\<cdot>y) = lt\<cdot>y\<cdot>x"
  by (cases "compare\<cdot>x\<cdot>y", simp_all add: le_def lt_def compare_sym [of y x])

subclass Eq_eq
proof
  fix x y
  show "eq\<cdot>x\<cdot>y = eq\<cdot>y\<cdot>x"
    unfolding eq_conv_compare
    by (cases "compare\<cdot>x\<cdot>y", simp_all add: compare_sym [of y x])
  show "eq\<cdot>x\<cdot>\<bottom> = \<bottom>"
    unfolding eq_conv_compare by simp
  show "eq\<cdot>\<bottom>\<cdot>y = \<bottom>"
    unfolding eq_conv_compare by simp
  show "eq\<cdot>x\<cdot>x \<noteq> FF"
    unfolding eq_conv_compare
    by (cases "compare\<cdot>x\<cdot>x", simp_all)
  { assume "eq\<cdot>x\<cdot>y = TT" then show "x = y"
      unfolding eq_conv_compare
      by (cases "compare\<cdot>x\<cdot>y", auto dest: compare_EQ_dest) }
qed

end

text \<open>A combinator for defining Ord instances for datatypes.\<close>

definition thenOrdering :: "Ordering \<rightarrow> Ordering \<rightarrow> Ordering" where
  "thenOrdering = (\<Lambda> x y. case x of LT \<Rightarrow> LT | EQ \<Rightarrow> y | GT \<Rightarrow> GT)"

lemma thenOrdering_simps [simp]:
  "thenOrdering\<cdot>LT\<cdot>y = LT"
  "thenOrdering\<cdot>EQ\<cdot>y = y"
  "thenOrdering\<cdot>GT\<cdot>y = GT"
  "thenOrdering\<cdot>\<bottom>\<cdot>y = \<bottom>"
  unfolding thenOrdering_def by simp_all

lemma thenOrdering_LT_iff [simp]:
  "thenOrdering\<cdot>x\<cdot>y = LT \<longleftrightarrow> x = LT \<or> x = EQ \<and> y = LT"
  by (cases x, simp_all)

lemma thenOrdering_EQ_iff [simp]:
  "thenOrdering\<cdot>x\<cdot>y = EQ \<longleftrightarrow> x = EQ \<and> y = EQ"
  by (cases x, simp_all)

lemma thenOrdering_GT_iff [simp]:
  "thenOrdering\<cdot>x\<cdot>y = GT \<longleftrightarrow> x = GT \<or> x = EQ \<and> y = GT"
  by (cases x, simp_all)

lemma thenOrdering_below_EQ_iff [simp]:
  "thenOrdering\<cdot>x\<cdot>y \<sqsubseteq> EQ \<longleftrightarrow> x \<sqsubseteq> EQ \<and> (x = \<bottom> \<or> y \<sqsubseteq> EQ)"
  by (cases x) simp_all

lemma is_EQ_thenOrdering [simp]:
  "is_EQ\<cdot>(thenOrdering\<cdot>x\<cdot>y) = (is_EQ\<cdot>x andalso is_EQ\<cdot>y)"
  by (cases x) simp_all

lemma oppOrdering_thenOrdering:
  "oppOrdering\<cdot>(thenOrdering\<cdot>x\<cdot>y) =
    thenOrdering\<cdot>(oppOrdering\<cdot>x)\<cdot>(oppOrdering\<cdot>y)"
  by (cases x) simp_all

instantiation lift :: ("{linorder,countable}") Ord_linear
begin

definition
  "compare \<equiv> (\<Lambda> (Def x) (Def y).
    if x < y then LT else if x > y then GT else EQ)"

instance proof
  fix x y z :: "'a lift"
  show "compare\<cdot>\<bottom>\<cdot>y = \<bottom>"
    unfolding compare_lift_def by simp
  show "compare\<cdot>x\<cdot>\<bottom> = \<bottom>"
    unfolding compare_lift_def by (cases x, simp_all)
  show "oppOrdering\<cdot>(compare\<cdot>x\<cdot>y) = compare\<cdot>y\<cdot>x"
    unfolding compare_lift_def
    by (cases x, cases y, simp, simp,
      cases y, simp, simp add: not_less less_imp_le)
  { assume "compare\<cdot>x\<cdot>y = EQ" then show "x = y"
      unfolding compare_lift_def
      by (cases x, cases y, simp, simp,
        cases y, simp, simp split: if_splits) }
  { assume "compare\<cdot>x\<cdot>y = LT" and "compare\<cdot>y\<cdot>z = LT" then show "compare\<cdot>x\<cdot>z = LT"
      unfolding compare_lift_def
      by (cases x, simp, cases y, simp, cases z, simp,
        auto split: if_splits) }
  show "eq\<cdot>x\<cdot>y = is_EQ\<cdot>(compare\<cdot>x\<cdot>y)"
    unfolding eq_lift_def compare_lift_def
    by (cases x, simp, cases y, simp, auto)
  show "compare\<cdot>x\<cdot>x \<sqsubseteq> EQ"
    unfolding compare_lift_def
    by (cases x, simp_all)
qed

end

lemma lt_le:
  "lt\<cdot>(x::'a::Ord_linear)\<cdot>y = (le\<cdot>x\<cdot>y andalso neq\<cdot>x\<cdot>y)"
  by (cases "compare\<cdot>x\<cdot>y")
     (auto simp: lt_def le_def eq_conv_compare)

end

