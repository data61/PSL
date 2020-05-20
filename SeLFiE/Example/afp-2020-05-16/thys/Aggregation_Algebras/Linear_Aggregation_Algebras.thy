(* Title:      Algebras for Aggregation and Minimisation with a Linear Order
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Algebras for Aggregation and Minimisation with a Linear Order\<close>

text \<open>
This theory gives several classes of instances of linear aggregation lattices as described in \cite{Guttmann2018a}.
Each of these instances can be used as edge weights and the resulting graphs will form s-algebras and m-algebras as shown in a separate theory.
\<close>

theory Linear_Aggregation_Algebras

imports Matrix_Aggregation_Algebras HOL.Real

begin

no_notation
  inf (infixl "\<sqinter>" 70)
  and uminus ("- _" [81] 80)

subsection \<open>Linearly Ordered Commutative Semigroups\<close>

text \<open>
Any linearly ordered commutative semigroup extended by new least and greatest elements forms a linear aggregation lattice.
The extension is done so that the new least element is a unit of aggregation and the new greatest element is a zero of aggregation.
\<close>

datatype 'a ext =
    Bot
  | Val 'a
  | Top

instantiation ext :: (linordered_ab_semigroup_add) linear_aggregation_kleene_algebra
begin

fun plus_ext :: "'a ext \<Rightarrow> 'a ext \<Rightarrow> 'a ext" where
  "plus_ext Bot x = x"
| "plus_ext (Val x) Bot = Val x"
| "plus_ext (Val x) (Val y) = Val (x + y)"
| "plus_ext (Val _) Top = Top"
| "plus_ext Top _ = Top"

fun sup_ext :: "'a ext \<Rightarrow> 'a ext \<Rightarrow> 'a ext" where
  "sup_ext Bot x = x"
| "sup_ext (Val x) Bot = Val x"
| "sup_ext (Val x) (Val y) = Val (max x y)"
| "sup_ext (Val _) Top = Top"
| "sup_ext Top _ = Top"

fun inf_ext :: "'a ext \<Rightarrow> 'a ext \<Rightarrow> 'a ext" where
  "inf_ext Bot _ = Bot"
| "inf_ext (Val _) Bot = Bot"
| "inf_ext (Val x) (Val y) = Val (min x y)"
| "inf_ext (Val x) Top = Val x"
| "inf_ext Top x = x"

fun times_ext :: "'a ext \<Rightarrow> 'a ext \<Rightarrow> 'a ext" where "times_ext x y = x \<sqinter> y"

fun uminus_ext :: "'a ext \<Rightarrow> 'a ext" where
  "uminus_ext Bot = Top"
| "uminus_ext (Val _) = Bot"
| "uminus_ext Top = Bot"

fun star_ext :: "'a ext \<Rightarrow> 'a ext" where "star_ext _ = Top"

fun conv_ext :: "'a ext \<Rightarrow> 'a ext" where "conv_ext x = x"

definition bot_ext :: "'a ext" where "bot_ext \<equiv> Bot"
definition one_ext :: "'a ext" where "one_ext \<equiv> Top"
definition top_ext :: "'a ext" where "top_ext \<equiv> Top"

fun less_eq_ext :: "'a ext \<Rightarrow> 'a ext \<Rightarrow> bool" where
  "less_eq_ext Bot _ = True"
| "less_eq_ext (Val _) Bot = False"
| "less_eq_ext (Val x) (Val y) = (x \<le> y)"
| "less_eq_ext (Val _) Top = True"
| "less_eq_ext Top Bot = False"
| "less_eq_ext Top (Val _) = False"
| "less_eq_ext Top Top = True"

fun less_ext :: "'a ext \<Rightarrow> 'a ext \<Rightarrow> bool" where "less_ext x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: "'a ext"
  show "(x + y) + z = x + (y + z)"
    by (cases x; cases y; cases z) (simp_all add: add.assoc)
  show "x + y = y + x"
    by (cases x; cases y) (simp_all add: add.commute)
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by simp
  show "x \<le> x"
    using less_eq_ext.elims(3) by fastforce
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y) simp_all
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) simp_all
  show "bot \<le> x"
    by (simp add: bot_ext_def)
  show "x \<le> top"
    by (cases x) (simp_all add: top_ext_def)
  show "x \<noteq> bot \<and> x + bot \<le> y + bot \<longrightarrow> x + z \<le> y + z"
    by (cases x; cases y; cases z) (simp_all add: bot_ext_def add_right_mono)
  show "x + y + bot = x + y"
    by (cases x; cases y) (simp_all add: bot_ext_def)
  show "x + y = bot \<longrightarrow> x = bot"
    by (cases x; cases y) (simp_all add: bot_ext_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) (simp_all add: linear)
  show "-x = (if x = bot then top else bot)"
    by (cases x) (simp_all add: bot_ext_def top_ext_def)
  show "(1::'a ext) = top"
    by (simp add: one_ext_def top_ext_def)
  show "x * y = x \<sqinter> y"
    by simp
  show "x\<^sup>T = x"
    by simp
  show "x\<^sup>\<star> = top"
    by (simp add: top_ext_def)
qed

end

text \<open>
An example of a linearly ordered commutative semigroup is the set of real numbers with standard addition as aggregation.
\<close>

lemma example_real_ext_matrix:
  fixes x :: "('a::enum,real ext) square"
  shows "minarc\<^sub>M x \<preceq> \<ominus>\<ominus>x"
  by (rule agg_square_m_algebra.minarc_below)

text \<open>
Another example of a linearly ordered commutative semigroup is the set of real numbers with maximum as aggregation.
\<close>

datatype real_max = Rmax real

instantiation real_max :: linordered_ab_semigroup_add
begin

fun less_eq_real_max where "less_eq_real_max (Rmax x) (Rmax y) = (x \<le> y)"
fun less_real_max where "less_real_max (Rmax x) (Rmax y) = (x < y)"
fun plus_real_max where "plus_real_max (Rmax x) (Rmax y) = Rmax (max x y)"

instance
proof
  fix x y z :: real_max
  show "(x + y) + z = x + (y + z)"
    by (cases x; cases y; cases z) simp
  show "x + y = y + x"
    by (cases x; cases y) simp
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y) auto
  show "x \<le> x"
    by (cases x) simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp
  show "x \<le> y \<Longrightarrow> z + x \<le> z + y"
    by (cases x; cases y; cases z) simp
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) auto
qed

end

lemma example_real_max_ext_matrix:
  fixes x :: "('a::enum,real_max ext) square"
  shows "minarc\<^sub>M x \<preceq> \<ominus>\<ominus>x"
  by (rule agg_square_m_algebra.minarc_below)

text \<open>
A third example of a linearly ordered commutative semigroup is the set of real numbers with minimum as aggregation.
\<close>

datatype real_min = Rmin real

instantiation real_min :: linordered_ab_semigroup_add
begin

fun less_eq_real_min where "less_eq_real_min (Rmin x) (Rmin y) = (x \<le> y)"
fun less_real_min where "less_real_min (Rmin x) (Rmin y) = (x < y)"
fun plus_real_min where "plus_real_min (Rmin x) (Rmin y) = Rmin (min x y)"

instance
proof
  fix x y z :: real_min
  show "(x + y) + z = x + (y + z)"
    by (cases x; cases y; cases z) simp
  show "x + y = y + x"
    by (cases x; cases y) simp
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y) auto
  show "x \<le> x"
    by (cases x) simp
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp
  show "x \<le> y \<Longrightarrow> z + x \<le> z + y"
    by (cases x; cases y; cases z) simp
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) auto
qed

end

lemma example_real_min_ext_matrix:
  fixes x :: "('a::enum,real_min ext) square"
  shows "minarc\<^sub>M x \<preceq> \<ominus>\<ominus>x"
  by (rule agg_square_m_algebra.minarc_below)

subsection \<open>Linearly Ordered Commutative Monoids\<close>

text \<open>
Any linearly ordered commutative monoid extended by new least and greatest elements forms a linear aggregation lattice.
This is similar to linearly ordered commutative semigroups except that the aggregation $\bot + \bot$ produces the unit of the monoid instead of the least element.
Applied to weighted graphs, this means that the aggregation of the empty graph will be the unit of the monoid (for example, $0$ for real numbers under standard addition, instead of $\bot$).
\<close>

class linordered_comm_monoid_add = linordered_ab_semigroup_add + comm_monoid_add

datatype 'a ext0 =
    Bot
  | Val 'a
  | Top

instantiation ext0 :: (linordered_comm_monoid_add) linear_aggregation_kleene_algebra
begin

fun plus_ext0 :: "'a ext0 \<Rightarrow> 'a ext0 \<Rightarrow> 'a ext0" where
  "plus_ext0 Bot Bot = Val 0"
| "plus_ext0 Bot x = x"
| "plus_ext0 (Val x) Bot = Val x"
| "plus_ext0 (Val x) (Val y) = Val (x + y)"
| "plus_ext0 (Val _) Top = Top"
| "plus_ext0 Top _ = Top"

fun sup_ext0 :: "'a ext0 \<Rightarrow> 'a ext0 \<Rightarrow> 'a ext0" where
  "sup_ext0 Bot x = x"
| "sup_ext0 (Val x) Bot = Val x"
| "sup_ext0 (Val x) (Val y) = Val (max x y)"
| "sup_ext0 (Val _) Top = Top"
| "sup_ext0 Top _ = Top"

fun inf_ext0 :: "'a ext0 \<Rightarrow> 'a ext0 \<Rightarrow> 'a ext0" where
  "inf_ext0 Bot _ = Bot"
| "inf_ext0 (Val _) Bot = Bot"
| "inf_ext0 (Val x) (Val y) = Val (min x y)"
| "inf_ext0 (Val x) Top = Val x"
| "inf_ext0 Top x = x"

fun times_ext0 :: "'a ext0 \<Rightarrow> 'a ext0 \<Rightarrow> 'a ext0" where "times_ext0 x y = x \<sqinter> y"

fun uminus_ext0 :: "'a ext0 \<Rightarrow> 'a ext0" where
  "uminus_ext0 Bot = Top"
| "uminus_ext0 (Val _) = Bot"
| "uminus_ext0 Top = Bot"

fun star_ext0 :: "'a ext0 \<Rightarrow> 'a ext0" where "star_ext0 _ = Top"

fun conv_ext0 :: "'a ext0 \<Rightarrow> 'a ext0" where "conv_ext0 x = x"

definition bot_ext0 :: "'a ext0" where "bot_ext0 \<equiv> Bot"
definition one_ext0 :: "'a ext0" where "one_ext0 \<equiv> Top"
definition top_ext0 :: "'a ext0" where "top_ext0 \<equiv> Top"

fun less_eq_ext0 :: "'a ext0 \<Rightarrow> 'a ext0 \<Rightarrow> bool" where
  "less_eq_ext0 Bot _ = True"
| "less_eq_ext0 (Val _) Bot = False"
| "less_eq_ext0 (Val x) (Val y) = (x \<le> y)"
| "less_eq_ext0 (Val _) Top = True"
| "less_eq_ext0 Top Bot = False"
| "less_eq_ext0 Top (Val _) = False"
| "less_eq_ext0 Top Top = True"

fun less_ext0 :: "'a ext0 \<Rightarrow> 'a ext0 \<Rightarrow> bool" where "less_ext0 x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: "'a ext0"
  show "(x + y) + z = x + (y + z)"
    by (cases x; cases y; cases z) (simp_all add: add.assoc)
  show "x + y = y + x"
    by (cases x; cases y) (simp_all add: add.commute)
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by simp
  show "x \<le> x"
    using less_eq_ext0.elims(3) by fastforce
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y) simp_all
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) simp_all
  show "bot \<le> x"
    by (simp add: bot_ext0_def)
  show "x \<le> top"
    by (cases x) (simp_all add: top_ext0_def)
  show "x \<noteq> bot \<and> x + bot \<le> y + bot \<longrightarrow> x + z \<le> y + z"
    apply (cases x; cases y; cases z)
    prefer 11 using add_right_mono bot_ext0_def apply fastforce
    by (simp_all add: bot_ext0_def add_right_mono)
  show "x + y + bot = x + y"
    by (cases x; cases y) (simp_all add: bot_ext0_def)
  show "x + y = bot \<longrightarrow> x = bot"
    by (cases x; cases y) (simp_all add: bot_ext0_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) (simp_all add: linear)
  show "-x = (if x = bot then top else bot)"
    by (cases x) (simp_all add: bot_ext0_def top_ext0_def)
  show "(1::'a ext0) = top"
    by (simp add: one_ext0_def top_ext0_def)
  show "x * y = x \<sqinter> y"
    by simp
  show "x\<^sup>T = x"
    by simp
  show "x\<^sup>\<star> = top"
    by (simp add: top_ext0_def)
qed

end

text \<open>
An example of a linearly ordered commutative monoid is the set of real numbers with standard addition and unit $0$.
\<close>

instantiation real :: linordered_comm_monoid_add
begin

instance ..

end

subsection \<open>Linearly Ordered Commutative Monoids with a Least Element\<close>

text \<open>
If a linearly ordered commutative monoid already contains a least element which is a unit of aggregation, only a new greatest element has to be added to obtain a linear aggregation lattice.
\<close>

class linordered_comm_monoid_add_bot = linordered_ab_semigroup_add + order_bot +
  assumes bot_zero [simp]: "bot + x = x"
begin

sublocale linordered_comm_monoid_add where zero = bot
  apply unfold_locales
  by simp

end

datatype 'a extT =
    Val 'a
  | Top

instantiation extT :: (linordered_comm_monoid_add_bot) linear_aggregation_kleene_algebra
begin

fun plus_extT :: "'a extT \<Rightarrow> 'a extT \<Rightarrow> 'a extT" where
  "plus_extT (Val x) (Val y) = Val (x + y)"
| "plus_extT (Val _) Top = Top"
| "plus_extT Top _ = Top"

fun sup_extT :: "'a extT \<Rightarrow> 'a extT \<Rightarrow> 'a extT" where
  "sup_extT (Val x) (Val y) = Val (max x y)"
| "sup_extT (Val _) Top = Top"
| "sup_extT Top _ = Top"

fun inf_extT :: "'a extT \<Rightarrow> 'a extT \<Rightarrow> 'a extT" where
  "inf_extT (Val x) (Val y) = Val (min x y)"
| "inf_extT (Val x) Top = Val x"
| "inf_extT Top x = x"

fun times_extT :: "'a extT \<Rightarrow> 'a extT \<Rightarrow> 'a extT" where "times_extT x y = x \<sqinter> y"

fun uminus_extT :: "'a extT \<Rightarrow> 'a extT" where "uminus_extT x = (if x = Val bot then Top else Val bot)"

fun star_extT :: "'a extT \<Rightarrow> 'a extT" where "star_extT _ = Top"

fun conv_extT :: "'a extT \<Rightarrow> 'a extT" where "conv_extT x = x"

definition bot_extT :: "'a extT" where "bot_extT \<equiv> Val bot"
definition one_extT :: "'a extT" where "one_extT \<equiv> Top"
definition top_extT :: "'a extT" where "top_extT \<equiv> Top"

fun less_eq_extT :: "'a extT \<Rightarrow> 'a extT \<Rightarrow> bool" where
  "less_eq_extT (Val x) (Val y) = (x \<le> y)"
| "less_eq_extT Top (Val _) = False"
| "less_eq_extT _ Top = True"

fun less_extT :: "'a extT \<Rightarrow> 'a extT \<Rightarrow> bool" where "less_extT x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: "'a extT"
  show "(x + y) + z = x + (y + z)"
    by (cases x; cases y; cases z) (simp_all add: add.assoc)
  show "x + y = y + x"
    by (cases x; cases y) (simp_all add: add.commute)
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by simp
  show "x \<le> x"
    by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y) simp_all
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) simp_all
  show "bot \<le> x"
    by (cases x) (simp_all add: bot_extT_def)
  show "x \<le> top"
    by (cases x) (simp_all add: top_extT_def)
  show "x \<noteq> bot \<and> x + bot \<le> y + bot \<longrightarrow> x + z \<le> y + z"
    by (cases x; cases y; cases z) (simp_all add: bot_extT_def add_right_mono)
  show "x + y + bot = x + y"
    by (cases x; cases y) (simp_all add: bot_extT_def)
  show "x + y = bot \<longrightarrow> x = bot"
    apply (cases x; cases y)
    apply (metis (mono_tags) add.commute add_right_mono bot.extremum bot.extremum_uniqueI bot_zero extT.inject plus_extT.simps(1) bot_extT_def)
    by (simp_all add: bot_extT_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) (simp_all add: linear)
  show "-x = (if x = bot then top else bot)"
    by (cases x) (simp_all add: bot_extT_def top_extT_def)
  show "(1::'a extT) = top"
    by (simp add: one_extT_def top_extT_def)
  show "x * y = x \<sqinter> y"
    by simp
  show "x\<^sup>T = x"
    by simp
  show "x\<^sup>\<star> = top"
    by (simp add: top_extT_def)
qed

end

text \<open>
An example of a linearly ordered commutative monoid with a least element is the set of real numbers extended by minus infinity with maximum as aggregation.
\<close>

datatype real_max_bot =
    MInfty
  | R real

instantiation real_max_bot :: linordered_comm_monoid_add_bot
begin

definition "bot_real_max_bot \<equiv> MInfty"

fun less_eq_real_max_bot where
  "less_eq_real_max_bot MInfty _ = True"
| "less_eq_real_max_bot (R _) MInfty = False"
| "less_eq_real_max_bot (R x) (R y) = (x \<le> y)"

fun less_real_max_bot where
  "less_real_max_bot _ MInfty = False"
| "less_real_max_bot MInfty (R _) = True"
| "less_real_max_bot (R x) (R y) = (x < y)"

fun plus_real_max_bot where
  "plus_real_max_bot MInfty y = y"
| "plus_real_max_bot x MInfty = x"
| "plus_real_max_bot (R x) (R y) = R (max x y)"

instance
proof
  fix x y z :: real_max_bot
  show "(x + y) + z = x + (y + z)"
    by (cases x; cases y; cases z) simp_all
  show "x + y = y + x"
    by (cases x; cases y) simp_all
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y) auto
  show "x \<le> x"
    by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp_all
  show "x \<le> y \<Longrightarrow> z + x \<le> z + y"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) auto
  show "bot \<le> x"
    by (cases x) (simp_all add: bot_real_max_bot_def)
  show "bot + x = x"
    by (cases x) (simp_all add: bot_real_max_bot_def)
qed

end

subsection \<open>Linearly Ordered Commutative Monoids with a Greatest Element\<close>

text \<open>
If a linearly ordered commutative monoid already contains a greatest element which is a unit of aggregation, only a new least element has to be added to obtain a linear aggregation lattice.
\<close>

class linordered_comm_monoid_add_top = linordered_ab_semigroup_add + order_top +
  assumes top_zero [simp]: "top + x = x"
begin

sublocale linordered_comm_monoid_add where zero = top
  apply unfold_locales
  by simp

lemma add_decreasing: "x + y \<le> x"
  using add_left_mono top.extremum by fastforce

lemma t_min: "x + y \<le> min x y"
  using add_commute add_decreasing by force

end

datatype 'a extB =
    Bot
  | Val 'a

instantiation extB :: (linordered_comm_monoid_add_top) linear_aggregation_kleene_algebra
begin

fun plus_extB :: "'a extB \<Rightarrow> 'a extB \<Rightarrow> 'a extB" where
  "plus_extB Bot Bot = Val top"
| "plus_extB Bot (Val x) = Val x"
| "plus_extB (Val x) Bot = Val x"
| "plus_extB (Val x) (Val y) = Val (x + y)"

fun sup_extB :: "'a extB \<Rightarrow> 'a extB \<Rightarrow> 'a extB" where
  "sup_extB Bot x = x"
| "sup_extB (Val x) Bot = Val x"
| "sup_extB (Val x) (Val y) = Val (max x y)"

fun inf_extB :: "'a extB \<Rightarrow> 'a extB \<Rightarrow> 'a extB" where
  "inf_extB Bot _ = Bot"
| "inf_extB (Val _) Bot = Bot"
| "inf_extB (Val x) (Val y) = Val (min x y)"

fun times_extB :: "'a extB \<Rightarrow> 'a extB \<Rightarrow> 'a extB" where "times_extB x y = x \<sqinter> y"

fun uminus_extB :: "'a extB \<Rightarrow> 'a extB" where
  "uminus_extB Bot = Val top"
| "uminus_extB (Val _) = Bot"

fun star_extB :: "'a extB \<Rightarrow> 'a extB" where "star_extB _ = Val top"

fun conv_extB :: "'a extB \<Rightarrow> 'a extB" where "conv_extB x = x"

definition bot_extB :: "'a extB" where "bot_extB \<equiv> Bot"
definition one_extB :: "'a extB" where "one_extB \<equiv> Val top"
definition top_extB :: "'a extB" where "top_extB \<equiv> Val top"

fun less_eq_extB :: "'a extB \<Rightarrow> 'a extB \<Rightarrow> bool" where
  "less_eq_extB Bot _ = True"
| "less_eq_extB (Val _) Bot = False"
| "less_eq_extB (Val x) (Val y) = (x \<le> y)"

fun less_extB :: "'a extB \<Rightarrow> 'a extB \<Rightarrow> bool" where "less_extB x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: "'a extB"
  show "(x + y) + z = x + (y + z)"
    by (cases x; cases y; cases z) (simp_all add: add.assoc)
  show "x + y = y + x"
    by (cases x; cases y) (simp_all add: add.commute)
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by simp
  show "x \<le> x"
    by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y) simp_all
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) simp_all
  show "bot \<le> x"
    by (simp add: bot_extB_def)
  show 1: "x \<le> top"
    by (cases x) (simp_all add: top_extB_def)
  show "x \<noteq> bot \<and> x + bot \<le> y + bot \<longrightarrow> x + z \<le> y + z"
    apply (cases x; cases y; cases z)
    prefer 6 using 1 apply (metis (mono_tags, lifting) plus_extB.simps(2,4) top_extB_def add_right_mono less_eq_extB.simps(3) top_zero)
    by (simp_all add: bot_extB_def add_right_mono)
  show "x + y + bot = x + y"
    by (cases x; cases y) (simp_all add: bot_extB_def)
  show "x + y = bot \<longrightarrow> x = bot"
    by (cases x; cases y) (simp_all add: bot_extB_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) (simp_all add: linear)
  show "-x = (if x = bot then top else bot)"
    by (cases x) (simp_all add: bot_extB_def top_extB_def)
  show "(1::'a extB) = top"
    by (simp add: one_extB_def top_extB_def)
  show "x * y = x \<sqinter> y"
    by simp
  show "x\<^sup>T = x"
    by simp
  show "x\<^sup>\<star> = top"
    by (simp add: top_extB_def)
qed

end

text \<open>
An example of a linearly ordered commutative monoid with a greatest element is the set of real numbers extended by infinity with minimum as aggregation.
\<close>

datatype real_min_top =
    R real
  | PInfty

instantiation real_min_top :: linordered_comm_monoid_add_top
begin

definition "top_real_min_top \<equiv> PInfty"

fun less_eq_real_min_top where
  "less_eq_real_min_top _ PInfty = True"
| "less_eq_real_min_top PInfty (R _) = False"
| "less_eq_real_min_top (R x) (R y) = (x \<le> y)"

fun less_real_min_top where
  "less_real_min_top PInfty _ = False"
| "less_real_min_top (R _) PInfty = True"
| "less_real_min_top (R x) (R y) = (x < y)"

fun plus_real_min_top where
  "plus_real_min_top PInfty y = y"
| "plus_real_min_top x PInfty = x"
| "plus_real_min_top (R x) (R y) = R (min x y)"

instance
proof
  fix x y z :: real_min_top
  show "(x + y) + z = x + (y + z)"
    by (cases x; cases y; cases z) simp_all
  show "x + y = y + x"
    by (cases x; cases y) simp_all
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by (cases x; cases y) auto
  show "x \<le> x"
    by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp_all
  show "x \<le> y \<Longrightarrow> z + x \<le> z + y"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) auto
  show "x \<le> top"
    by (cases x) (simp_all add: top_real_min_top_def)
  show "top + x = x"
    by (cases x) (simp_all add: top_real_min_top_def)
qed

end

text \<open>
Another example of a linearly ordered commutative monoid with a greatest element is the unit interval of real numbers with any triangular norm (t-norm) as aggregation.
Ideally, we would like to show that the unit interval is an instance of \<open>linordered_comm_monoid_add_top\<close>.
However, this class has an addition operation, so the instantiation would require dependent types.
We therefore show only the order property in general and a particular instance of the class.
\<close>

typedef (overloaded) unit = "{0..1} :: real set"
  by auto

setup_lifting type_definition_unit

instantiation unit :: bounded_linorder
begin

lift_definition bot_unit :: unit is 0
  by simp

lift_definition top_unit :: unit is 1
  by simp

lift_definition less_eq_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" is less_eq .

lift_definition less_unit :: "unit \<Rightarrow> unit \<Rightarrow> bool" is less .

instance
  apply intro_classes
  using bot_unit.rep_eq top_unit.rep_eq less_eq_unit.rep_eq less_unit.rep_eq unit.Rep_unit_inject unit.Rep_unit by auto

end

text \<open>
We give the \L{}ukasiewicz t-norm as a particular instance.
\<close>

instantiation unit :: linordered_comm_monoid_add_top
begin

abbreviation tl :: "real \<Rightarrow> real \<Rightarrow> real" where
  "tl x y \<equiv> max (x + y - 1) 0"

lemma tl_assoc:
  "x \<in> {0..1} \<Longrightarrow> z \<in> {0..1} \<Longrightarrow> tl (tl x y) z = tl x (tl y z)"
  by auto

lemma tl_top_zero:
  "x \<in> {0..1} \<Longrightarrow> tl 1 x = x"
  by auto

lift_definition plus_unit :: "unit \<Rightarrow> unit \<Rightarrow> unit" is tl
  by simp

instance
  apply intro_classes
  apply (metis (mono_tags, lifting) plus_unit.rep_eq unit.Rep_unit_inject unit.Rep_unit tl_assoc)
  using unit.Rep_unit_inject plus_unit.rep_eq apply fastforce
  apply (simp add: less_eq_unit.rep_eq plus_unit.rep_eq)
  by (metis (mono_tags, lifting) top_unit.rep_eq unit.Rep_unit_inject unit.Rep_unit plus_unit.rep_eq tl_top_zero)

end

subsection \<open>Linearly Ordered Commutative Monoids with a Least Element and a Greatest Element\<close>

text \<open>
If a linearly ordered commutative monoid already contains a least element which is a unit of aggregation and a greatest element, it forms a linear aggregation lattice.
\<close>

class linordered_bounded_comm_monoid_add_bot = linordered_comm_monoid_add_bot + order_top
begin

subclass bounded_linorder ..

subclass aggregation_order
  apply unfold_locales
  apply (simp add: add_right_mono)
  apply simp
  by (metis add_0_right add_left_mono bot.extremum bot.extremum_unique)

sublocale linear_aggregation_kleene_algebra where sup = max and inf = min and times = min and conv = id and one = top and star = "\<lambda>x . top" and uminus = "\<lambda>x . if x = bot then top else bot"
  apply unfold_locales
  by simp_all

lemma t_top: "x + top = top"
  by (metis add_right_mono bot.extremum bot_zero top_unique)

lemma add_increasing: "x \<le> x + y"
  using add_left_mono bot.extremum by fastforce

lemma t_max: "max x y \<le> x + y"
  using add_commute add_increasing by force

end

text \<open>
An example of a linearly ordered commutative monoid with a least and a greatest element is the unit interval of real numbers with any triangular conorm (t-conorm) as aggregation.
For the reason outlined above, we show just a particular instance of \<open>linordered_bounded_comm_monoid_add_bot\<close>.
Because the \<open>plus\<close> functions in the two instances given for the unit type are different, we work on a copy of the unit type.
\<close>

typedef (overloaded) unit2 = "{0..1} :: real set"
  by auto

setup_lifting type_definition_unit2

instantiation unit2 :: bounded_linorder
begin

lift_definition bot_unit2 :: unit2 is 0
  by simp

lift_definition top_unit2 :: unit2 is 1
  by simp

lift_definition less_eq_unit2 :: "unit2 \<Rightarrow> unit2 \<Rightarrow> bool" is less_eq .

lift_definition less_unit2 :: "unit2 \<Rightarrow> unit2 \<Rightarrow> bool" is less .

instance
  apply intro_classes
  using bot_unit2.rep_eq top_unit2.rep_eq less_eq_unit2.rep_eq less_unit2.rep_eq unit2.Rep_unit2_inject unit2.Rep_unit2 by auto

end

text \<open>
We give the product t-conorm as a particular instance.
\<close>

instantiation unit2 :: linordered_bounded_comm_monoid_add_bot
begin

abbreviation sp :: "real \<Rightarrow> real \<Rightarrow> real" where
  "sp x y \<equiv> x + y - x * y"

lemma sp_assoc:
  "sp (sp x y) z = sp x (sp y z)"
  by (unfold left_diff_distrib right_diff_distrib distrib_left distrib_right) simp

lemma sp_mono:
  assumes "z \<in> {0..1}"
      and "x \<le> y"
    shows "sp z x \<le> sp z y"
proof -
  have "z + (1 - z) * x \<le> z + (1 - z) * y"
    using assms mult_left_mono by fastforce
  thus ?thesis
    by (unfold left_diff_distrib right_diff_distrib distrib_left distrib_right) simp
qed

lift_definition plus_unit2 :: "unit2 \<Rightarrow> unit2 \<Rightarrow> unit2" is sp
proof -
  fix x y :: real
  assume 1: "x \<in> {0..1}"
  assume 2: "y \<in> {0..1}"
  have "x - x * y \<le> 1 - y"
    using 1 2 by (metis (full_types) atLeastAtMost_iff diff_ge_0_iff_ge left_diff_distrib' mult.commute mult.left_neutral mult_left_le)
  hence 3: "x + y - x * y \<le> 1"
    by simp
  have "y * (x - 1) \<le> 0"
    using 1 2 by (meson atLeastAtMost_iff le_iff_diff_le_0 mult_nonneg_nonpos)
  hence "x + y - x * y \<ge> 0"
    using 1 by (metis (no_types) atLeastAtMost_iff diff_diff_eq2 diff_ge_0_iff_ge left_diff_distrib mult.commute mult.left_neutral order_trans)
  thus "x + y - x * y \<in> {0..1}"
    using 3 by simp
qed

instance
  apply intro_classes
  apply (metis (mono_tags, lifting) plus_unit2.rep_eq unit2.Rep_unit2_inject sp_assoc)
  using unit2.Rep_unit2_inject plus_unit2.rep_eq apply fastforce
  using sp_mono unit2.Rep_unit2 less_eq_unit2.rep_eq plus_unit2.rep_eq apply simp
  using bot_unit2.rep_eq unit2.Rep_unit2_inject plus_unit2.rep_eq by fastforce

end

subsection \<open>Constant Aggregation\<close>

text \<open>
Any linear order with a constant element extended by new least and greatest elements forms a linear aggregation lattice where the aggregation returns the given constant.
\<close>

class pointed_linorder = linorder +
  fixes const :: 'a

datatype 'a extC =
    Bot
  | Val 'a
  | Top

instantiation extC :: (pointed_linorder) linear_aggregation_kleene_algebra
begin

fun plus_extC :: "'a extC \<Rightarrow> 'a extC \<Rightarrow> 'a extC" where "plus_extC x y = Val const"

fun sup_extC :: "'a extC \<Rightarrow> 'a extC \<Rightarrow> 'a extC" where
  "sup_extC Bot x = x"
| "sup_extC (Val x) Bot = Val x"
| "sup_extC (Val x) (Val y) = Val (max x y)"
| "sup_extC (Val _) Top = Top"
| "sup_extC Top _ = Top"

fun inf_extC :: "'a extC \<Rightarrow> 'a extC \<Rightarrow> 'a extC" where
  "inf_extC Bot _ = Bot"
| "inf_extC (Val _) Bot = Bot"
| "inf_extC (Val x) (Val y) = Val (min x y)"
| "inf_extC (Val x) Top = Val x"
| "inf_extC Top x = x"

fun times_extC :: "'a extC \<Rightarrow> 'a extC \<Rightarrow> 'a extC" where "times_extC x y = x \<sqinter> y"

fun uminus_extC :: "'a extC \<Rightarrow> 'a extC" where
  "uminus_extC Bot = Top"
| "uminus_extC (Val _) = Bot"
| "uminus_extC Top = Bot"

fun star_extC :: "'a extC \<Rightarrow> 'a extC" where "star_extC _ = Top"

fun conv_extC :: "'a extC \<Rightarrow> 'a extC" where "conv_extC x = x"

definition bot_extC :: "'a extC" where "bot_extC \<equiv> Bot"
definition one_extC :: "'a extC" where "one_extC \<equiv> Top"
definition top_extC :: "'a extC" where "top_extC \<equiv> Top"

fun less_eq_extC :: "'a extC \<Rightarrow> 'a extC \<Rightarrow> bool" where
  "less_eq_extC Bot _ = True"
| "less_eq_extC (Val _) Bot = False"
| "less_eq_extC (Val x) (Val y) = (x \<le> y)"
| "less_eq_extC (Val _) Top = True"
| "less_eq_extC Top Bot = False"
| "less_eq_extC Top (Val _) = False"
| "less_eq_extC Top Top = True"

fun less_extC :: "'a extC \<Rightarrow> 'a extC \<Rightarrow> bool" where "less_extC x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: "'a extC"
  show "(x + y) + z = x + (y + z)"
    by simp
  show "x + y = y + x"
    by simp
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by simp
  show "x \<le> x"
    by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y) simp_all
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) simp_all
  show "bot \<le> x"
    by (simp add: bot_extC_def)
  show "x \<le> top"
    by (cases x) (simp_all add: top_extC_def)
  show "x \<noteq> bot \<and> x + bot \<le> y + bot \<longrightarrow> x + z \<le> y + z"
    by simp
  show "x + y + bot = x + y"
    by simp
  show "x + y = bot \<longrightarrow> x = bot"
    by (simp add: bot_extC_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) (simp_all add: linear)
  show "-x = (if x = bot then top else bot)"
    by (cases x) (simp_all add: bot_extC_def top_extC_def)
  show "(1::'a extC) = top"
    by (simp add: one_extC_def top_extC_def)
  show "x * y = x \<sqinter> y"
    by simp
  show "x\<^sup>T = x"
    by simp
  show "x\<^sup>\<star> = top"
    by (simp add: top_extC_def)
qed

end

text \<open>
An example of a linear order is the set of real numbers.
Any real number can be chosen as the constant.
\<close>

instantiation real :: pointed_linorder
begin

instance ..

end

text \<open>
The following instance shows that any linear order with a constant forms a linearly ordered commutative semigroup with the alpha-median operation as aggregation.
The alpha-median of two elements is the median of these elements and the given constant.
\<close>

fun median3 :: "'a::ord \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a" where
  "median3 x y z =
    (if x \<le> y \<and> y \<le> z then y else
     if x \<le> z \<and> z \<le> y then z else
     if y \<le> x \<and> x \<le> z then x else
     if y \<le> z \<and> z \<le> x then z else
     if z \<le> x \<and> x \<le> y then x else y)"

interpretation alpha_median: linordered_ab_semigroup_add where plus = "median3 const" and less_eq = less_eq and less = less
proof
  fix a b c :: 'a
  show "median3 const (median3 const a b) c = median3 const a (median3 const b c)"
    by (cases "const \<le> a"; cases "const \<le> b"; cases "const \<le> c"; cases "a \<le> b"; cases "a \<le> c"; cases "b \<le> c") auto
  show "median3 const a b = median3 const b a"
    by (cases "const \<le> a"; cases "const \<le> b"; cases "a \<le> b") auto
  assume "a \<le> b"
  thus "median3 const c a \<le> median3 const c b"
    by (cases "const \<le> a"; cases "const \<le> b"; cases "const \<le> c"; cases "a \<le> c"; cases "b \<le> c") auto
qed

subsection \<open>Counting Aggregation\<close>

text \<open>
Any linear order extended by new least and greatest elements and a copy of the natural numbers forms a linear aggregation lattice where the aggregation counts non-$\bot$ elements using the copy of the natural numbers.
\<close>

datatype 'a extN =
    Bot
  | Val 'a
  | N nat
  | Top

instantiation extN :: (linorder) linear_aggregation_kleene_algebra
begin

fun plus_extN :: "'a extN \<Rightarrow> 'a extN \<Rightarrow> 'a extN" where
  "plus_extN Bot Bot = N 0"
| "plus_extN Bot (Val _) = N 1"
| "plus_extN Bot (N y) = N y"
| "plus_extN Bot Top = N 1"
| "plus_extN (Val _) Bot = N 1"
| "plus_extN (Val _) (Val _) = N 2"
| "plus_extN (Val _) (N y) = N (y + 1)"
| "plus_extN (Val _) Top = N 2"
| "plus_extN (N x) Bot = N x"
| "plus_extN (N x) (Val _) = N (x + 1)"
| "plus_extN (N x) (N y) = N (x + y)"
| "plus_extN (N x) Top = N (x + 1)"
| "plus_extN Top Bot = N 1"
| "plus_extN Top (Val _) = N 2"
| "plus_extN Top (N y) = N (y + 1)"
| "plus_extN Top Top = N 2"

fun sup_extN :: "'a extN \<Rightarrow> 'a extN \<Rightarrow> 'a extN" where
  "sup_extN Bot x = x"
| "sup_extN (Val x) Bot = Val x"
| "sup_extN (Val x) (Val y) = Val (max x y)"
| "sup_extN (Val _) (N y) = N y"
| "sup_extN (Val _) Top = Top"
| "sup_extN (N x) Bot = N x"
| "sup_extN (N x) (Val _) = N x"
| "sup_extN (N x) (N y) = N (max x y)"
| "sup_extN (N _) Top = Top"
| "sup_extN Top _ = Top"

fun inf_extN :: "'a extN \<Rightarrow> 'a extN \<Rightarrow> 'a extN" where
  "inf_extN Bot _ = Bot"
| "inf_extN (Val _) Bot = Bot"
| "inf_extN (Val x) (Val y) = Val (min x y)"
| "inf_extN (Val x) (N _) = Val x"
| "inf_extN (Val x) Top = Val x"
| "inf_extN (N _) Bot = Bot"
| "inf_extN (N _) (Val y) = Val y"
| "inf_extN (N x) (N y) = N (min x y)"
| "inf_extN (N x) Top = N x"
| "inf_extN Top y = y"

fun times_extN :: "'a extN \<Rightarrow> 'a extN \<Rightarrow> 'a extN" where "times_extN x y = x \<sqinter> y"

fun uminus_extN :: "'a extN \<Rightarrow> 'a extN" where
  "uminus_extN Bot = Top"
| "uminus_extN (Val _) = Bot"
| "uminus_extN (N _) = Bot"
| "uminus_extN Top = Bot"

fun star_extN :: "'a extN \<Rightarrow> 'a extN" where "star_extN _ = Top"

fun conv_extN :: "'a extN \<Rightarrow> 'a extN" where "conv_extN x = x"

definition bot_extN :: "'a extN" where "bot_extN \<equiv> Bot"
definition one_extN :: "'a extN" where "one_extN \<equiv> Top"
definition top_extN :: "'a extN" where "top_extN \<equiv> Top"

fun less_eq_extN :: "'a extN \<Rightarrow> 'a extN \<Rightarrow> bool" where
  "less_eq_extN Bot _ = True"
| "less_eq_extN (Val _) Bot = False"
| "less_eq_extN (Val x) (Val y) = (x \<le> y)"
| "less_eq_extN (Val _) (N _) = True"
| "less_eq_extN (Val _) Top = True"
| "less_eq_extN (N _) Bot = False"
| "less_eq_extN (N _) (Val _) = False"
| "less_eq_extN (N x) (N y) = (x \<le> y)"
| "less_eq_extN (N _) Top = True"
| "less_eq_extN Top Bot = False"
| "less_eq_extN Top (Val _) = False"
| "less_eq_extN Top (N _) = False"
| "less_eq_extN Top Top = True"

fun less_extN :: "'a extN \<Rightarrow> 'a extN \<Rightarrow> bool" where "less_extN x y = (x \<le> y \<and> \<not> y \<le> x)"

instance
proof
  fix x y z :: "'a extN"
  show "(x + y) + z = x + (y + z)"
    by (cases x; cases y; cases z) simp_all
  show "x + y = y + x"
    by (cases x; cases y) simp_all
  show "(x < y) = (x \<le> y \<and> \<not> y \<le> x)"
    by simp
  show "x \<le> x"
    by (cases x) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> x"
    by (cases x; cases y) simp_all
  show "x \<sqinter> y \<le> y"
    by (cases x; cases y) simp_all
  show "x \<le> y \<Longrightarrow> x \<le> z \<Longrightarrow> x \<le> y \<sqinter> z"
    by (cases x; cases y; cases z) simp_all
  show "x \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<squnion> y"
    by (cases x; cases y) simp_all
  show "y \<le> x \<Longrightarrow> z \<le> x \<Longrightarrow> y \<squnion> z \<le> x"
    by (cases x; cases y; cases z) simp_all
  show "bot \<le> x"
    by (simp add: bot_extN_def)
  show "x \<le> top"
    by (cases x) (simp_all add: top_extN_def)
  show "x \<noteq> bot \<and> x + bot \<le> y + bot \<longrightarrow> x + z \<le> y + z"
    by (cases x; cases y; cases z) (simp_all add: bot_extN_def)
  show "x + y + bot = x + y"
    by (cases x; cases y) (simp_all add: bot_extN_def)
  show "x + y = bot \<longrightarrow> x = bot"
    by (cases x; cases y) (simp_all add: bot_extN_def)
  show "x \<le> y \<or> y \<le> x"
    by (cases x; cases y) (simp_all add: linear)
  show "-x = (if x = bot then top else bot)"
    by (cases x) (simp_all add: bot_extN_def top_extN_def)
  show "(1::'a extN) = top"
    by (simp add: one_extN_def top_extN_def)
  show "x * y = x \<sqinter> y"
    by simp
  show "x\<^sup>T = x"
    by simp
  show "x\<^sup>\<star> = top"
    by (simp add: top_extN_def)
qed

end

end

