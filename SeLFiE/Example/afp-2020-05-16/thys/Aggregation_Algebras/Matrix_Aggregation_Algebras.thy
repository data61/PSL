(* Title:      Matrix Algebras for Aggregation and Minimisation
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Matrix Algebras for Aggregation and Minimisation\<close>

text \<open>
This theory formalises aggregation orders and lattices as introduced in \cite{Guttmann2018a}.
Aggregation in these algebras is an associative and commutative operation satisfying additional properties related to the partial order and its least element.
We apply the aggregation operation to finite matrices over the aggregation algebras, which shows that they form an s-algebra.
By requiring the aggregation algebras to be linearly ordered, we also obtain that the matrices form an m-algebra.

This is an intermediate step in demonstrating that weighted graphs form an s-algebra and an m-algebra.
The present theory specifies abstract properties for the edge weights and shows that matrices over such weights form an instance of s-algebras and m-algebras.
A second step taken in a separate theory gives concrete instances of edge weights satisfying the abstract properties introduced here.

Lifting the aggregation to matrices requires finite sums over elements taken from commutative semigroups with an element that is a unit on the image of the semigroup operation.
Because standard sums assume a commutative monoid we have to derive a number of properties of these generalised sums as their statements or proofs are different.
\<close>

theory Matrix_Aggregation_Algebras

imports Stone_Kleene_Relation_Algebras.Matrix_Kleene_Algebras Aggregation_Algebras Semigroups_Big

begin

no_notation
  inf (infixl "\<sqinter>" 70)
  and uminus ("- _" [81] 80)

subsection \<open>Aggregation Orders and Finite Sums\<close>

text \<open>
An aggregation order is a partial order with a least element and an associative commutative operation satisfying certain properties.
Axiom \<open>add_add_bot\<close> introduces almost a commutative monoid; we require that \<open>bot\<close> is a unit only on the image of the aggregation operation.
This is necessary since it is not a unit of a number of aggregation operations we are interested in.
Axiom \<open>add_right_isotone\<close> states that aggregation is $\leq$-isotone on the image of the aggregation operation.
Its assumption $x \neq bot$ is necessary because the introduction of new edges can decrease the aggregated value.
Axiom \<open>add_bot\<close> expresses that aggregation is zero-sum-free.
\<close>

class aggregation_order = order_bot + ab_semigroup_add +
  assumes add_right_isotone: "x \<noteq> bot \<and> x + bot \<le> y + bot \<longrightarrow> x + z \<le> y + z"
  assumes add_add_bot [simp]: "x + y + bot = x + y"
  assumes add_bot: "x + y = bot \<longrightarrow> x = bot"
begin

abbreviation "zero \<equiv> bot + bot"

sublocale aggregation: ab_semigroup_add_0 where plus = plus and zero = zero
  apply unfold_locales
  using add_assoc add_add_bot by auto

lemma add_bot_bot_bot:
  "x + bot + bot + bot = x + bot"
  by simp

end

text \<open>
We introduce notation for finite sums over aggregation orders.
The index variable of the summation ranges over the finite universe of its type.
Finite sums are defined recursively using the binary aggregation and $\bot + \bot$ for the empty sum.
\<close>

syntax (xsymbols)
  "_sum_ab_semigroup_add_0" :: "idt \<Rightarrow> 'a::bounded_semilattice_sup_bot \<Rightarrow> 'a" ("(\<Sum>\<^sub>_ _)" [0,10] 10)

translations
  "\<Sum>\<^sub>x t" => "XCONST ab_semigroup_add_0.sum_0 XCONST plus (XCONST plus XCONST bot XCONST bot) (\<lambda>x . t) { x . CONST True }"

text \<open>
The following are basic properties of such sums.
\<close>

lemma agg_sum_bot:
  "(\<Sum>\<^sub>k bot::'a::aggregation_order) = bot + bot"
proof (induct rule: infinite_finite_induct)
  case (infinite A)
  thus ?case
    by simp
next
  case empty
  thus ?case
    by simp
next
  case (insert x F)
  thus ?case
    by (metis add.commute add_add_bot aggregation.sum_0.insert)
qed

lemma agg_sum_bot_bot:
  "(\<Sum>\<^sub>k bot + bot::'a::aggregation_order) = bot + bot"
  by (rule aggregation.sum_0.neutral_const)

lemma agg_sum_not_bot_1:
  fixes f :: "'a::finite \<Rightarrow> 'b::aggregation_order"
  assumes "f i \<noteq> bot"
    shows "(\<Sum>\<^sub>k f k) \<noteq> bot"
  by (metis assms add_bot aggregation.sum_0.remove finite_code mem_Collect_eq)

lemma agg_sum_not_bot:
  fixes f :: "('a::finite,'b::aggregation_order) square"
  assumes "f (i,j) \<noteq> bot"
    shows "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) \<noteq> bot"
  by (metis assms agg_sum_not_bot_1)

lemma agg_sum_distrib:
  fixes f g :: "'a \<Rightarrow> 'b::aggregation_order"
  shows "(\<Sum>\<^sub>k f k + g k) = (\<Sum>\<^sub>k f k) + (\<Sum>\<^sub>k g k)"
  by (rule aggregation.sum_0.distrib)

lemma agg_sum_distrib_2:
  fixes f g :: "('a,'b::aggregation_order) square"
  shows "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l) + g (k,l)) = (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) + (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l))"
proof -
  have "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l) + g (k,l)) = (\<Sum>\<^sub>k (\<Sum>\<^sub>l f (k,l)) + (\<Sum>\<^sub>l g (k,l)))"
    by (metis (no_types) aggregation.sum_0.distrib)
  also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) + (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l))"
    by (metis (no_types) aggregation.sum_0.distrib)
  finally show ?thesis
    .
qed

lemma agg_sum_add_bot:
  fixes f :: "'a \<Rightarrow> 'b::aggregation_order"
  shows "(\<Sum>\<^sub>k f k) = (\<Sum>\<^sub>k f k) + bot"
  by (metis (no_types) add_add_bot aggregation.sum_0.F_one)

lemma agg_sum_add_bot_2:
  fixes f :: "'a \<Rightarrow> 'b::aggregation_order"
  shows "(\<Sum>\<^sub>k f k + bot) = (\<Sum>\<^sub>k f k)"
proof -
  have "(\<Sum>\<^sub>k f k + bot) = (\<Sum>\<^sub>k f k) + (\<Sum>\<^sub>k::'a bot::'b)"
    using agg_sum_distrib by simp
  also have "... = (\<Sum>\<^sub>k f k) + (bot + bot)"
    by (metis agg_sum_bot)
  also have "... = (\<Sum>\<^sub>k f k)"
    by simp
  finally show ?thesis
    by simp
qed

lemma agg_sum_commute:
  fixes f :: "('a,'b::aggregation_order) square"
  shows "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) = (\<Sum>\<^sub>l \<Sum>\<^sub>k f (k,l))"
  by (rule aggregation.sum_0.swap)

lemma agg_delta:
  fixes f :: "'a::finite \<Rightarrow> 'b::aggregation_order"
  shows "(\<Sum>\<^sub>l if l = j then f l else zero) = f j + bot"
  apply (subst aggregation.sum_0.delta)
  apply simp
  by (metis add.commute add.left_commute add_add_bot mem_Collect_eq)

lemma agg_delta_1:
  fixes f :: "'a::finite \<Rightarrow> 'b::aggregation_order"
  shows "(\<Sum>\<^sub>l if l = j then f l else bot) = f j + bot"
proof -
  let ?f = "(\<lambda>l . if l = j then f l else bot)"
  let ?S = "{l::'a . True}"
  show ?thesis
  proof (cases "j \<in> ?S")
    case False
    thus ?thesis by simp
  next
    case True
    let ?A = "?S - {j}"
    let ?B = "{j}"
    from True have eq: "?S = ?A \<union> ?B"
      by blast
    have dj: "?A \<inter> ?B = {}"
      by simp
    have fAB: "finite ?A" "finite ?B"
      by auto
    have "aggregation.sum_0 ?f ?S = aggregation.sum_0 ?f ?A + aggregation.sum_0 ?f ?B"
      using aggregation.sum_0.union_disjoint[OF fAB dj, of ?f, unfolded eq [symmetric]] by simp
    also have "... = aggregation.sum_0 (\<lambda>l . bot) ?A + aggregation.sum_0 ?f ?B"
      by (subst aggregation.sum_0.cong[where ?B="?A"]) simp_all
    also have "... = zero + aggregation.sum_0 ?f ?B"
      by (metis (no_types, lifting) add.commute add_add_bot aggregation.sum_0.F_g_one aggregation.sum_0.neutral)
    also have "... = zero + (f j + zero)"
      by simp
    also have "... = f j + bot"
      by (metis add.commute add.left_commute add_add_bot)
    finally show ?thesis
      .
  qed
qed

lemma agg_delta_2:
  fixes f :: "('a::finite,'b::aggregation_order) square"
  shows "(\<Sum>\<^sub>k \<Sum>\<^sub>l if k = i \<and> l = j then f (k,l) else bot) = f (i,j) + bot"
proof -
  have "\<forall>k . (\<Sum>\<^sub>l if k = i \<and> l = j then f (k,l) else bot) = (if k = i then f (k,j) + bot else zero)"
  proof
    fix k
    have "(\<Sum>\<^sub>l if k = i \<and> l = j then f (k,l) else bot) = (\<Sum>\<^sub>l if l = j then if k = i then f (k,l) else bot else bot)"
      by meson
    also have "... = (if k = i then f (k,j) else bot) + bot"
      by (rule agg_delta_1)
    finally show "(\<Sum>\<^sub>l if k = i \<and> l = j then f (k,l) else bot) = (if k = i then f (k,j) + bot else zero)"
      by simp
  qed
  hence "(\<Sum>\<^sub>k \<Sum>\<^sub>l if k = i \<and> l = j then f (k,l) else bot) = (\<Sum>\<^sub>k if k = i then f (k,j) + bot else zero)"
    using aggregation.sum_0.cong by auto
  also have "... = f (i,j) + bot"
    apply (subst agg_delta)
    by simp
  finally show ?thesis
    .
qed

subsection \<open>Matrix Aggregation\<close>

text \<open>
The following definitions introduce the matrix of unit elements, componentwise aggregation and aggregation on matrices.
The aggregation of a matrix is a single value, but because s-algebras are single-sorted the result has to be encoded as a matrix of the same type (size) as the input.
We store the aggregated matrix value in the `first' entry of a matrix, setting all other entries to the unit value.
The first entry is determined by requiring an enumeration of indices.
It does not have to be the first entry; any fixed location in the matrix would work as well.
\<close>

definition zero_matrix :: "('a,'b::{plus,bot}) square" ("mzero") where "mzero = (\<lambda>e . bot + bot)"

definition plus_matrix :: "('a,'b::plus) square \<Rightarrow> ('a,'b) square \<Rightarrow> ('a,'b) square" (infixl "\<oplus>\<^sub>M" 65) where "plus_matrix f g = (\<lambda>e . f e + g e)"

definition sum_matrix :: "('a::enum,'b::{plus,bot}) square \<Rightarrow> ('a,'b) square" ("sum\<^sub>M _" [80] 80) where "sum_matrix f = (\<lambda>(i,j) . if i = hd enum_class.enum \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l) else bot + bot)"

text \<open>
Basic properties of these operations are given in the following.
\<close>

lemma bot_plus_bot:
  "mbot \<oplus>\<^sub>M mbot = mzero"
  by (simp add: plus_matrix_def bot_matrix_def zero_matrix_def)

lemma sum_bot:
  "sum\<^sub>M (mbot :: ('a::enum,'b::aggregation_order) square) = mzero"
proof (rule ext, rule prod_cases)
  fix i j :: "'a"
  have "(sum\<^sub>M mbot :: ('a,'b) square) (i,j) = (if i = hd enum_class.enum \<and> j = i then \<Sum>\<^sub>(k::'a) \<Sum>\<^sub>(l::'a) bot else bot + bot)"
    by (unfold sum_matrix_def bot_matrix_def) simp
  also have "... = bot + bot"
    using agg_sum_bot aggregation.sum_0.neutral by fastforce
  also have "... = mzero (i,j)"
    by (simp add: zero_matrix_def)
  finally show "(sum\<^sub>M mbot :: ('a,'b) square) (i,j) = mzero (i,j)"
    .
qed

lemma sum_plus_bot:
  fixes f :: "('a::enum,'b::aggregation_order) square"
  shows "sum\<^sub>M f \<oplus>\<^sub>M mbot = sum\<^sub>M f"
proof (rule ext, rule prod_cases)
  let ?h = "hd enum_class.enum"
  fix i j
  have "(sum\<^sub>M f \<oplus>\<^sub>M mbot) (i,j) = (if i = ?h \<and> j = i then (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) + bot else zero + bot)"
    by (simp add: plus_matrix_def bot_matrix_def sum_matrix_def)
  also have "... = (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l) else zero)"
    by (metis (no_types, lifting) add_add_bot aggregation.sum_0.F_one)
  also have "... = (sum\<^sub>M f) (i,j)"
    by (simp add: sum_matrix_def)
  finally show "(sum\<^sub>M f \<oplus>\<^sub>M mbot) (i,j) = (sum\<^sub>M f) (i,j)"
    by simp
qed

lemma sum_plus_zero:
  fixes f :: "('a::enum,'b::aggregation_order) square"
  shows "sum\<^sub>M f \<oplus>\<^sub>M mzero = sum\<^sub>M f"
  by (rule ext, rule prod_cases) (simp add: plus_matrix_def zero_matrix_def sum_matrix_def)

lemma agg_matrix_bot:
  fixes f :: "('a,'b::aggregation_order) square"
  assumes "\<forall>i j . f (i,j) = bot"
    shows "f = mbot"
  apply (unfold bot_matrix_def)
  using assms by auto

text \<open>
We consider a different implementation of matrix aggregation which stores the aggregated value in all entries of the matrix instead of a particular one.
This does not require an enumeration of the indices.
All results continue to hold using this alternative implementation.
\<close>

definition sum_matrix_2 :: "('a,'b::{plus,bot}) square \<Rightarrow> ('a,'b) square" ("sum2\<^sub>M _" [80] 80) where "sum_matrix_2 f = (\<lambda>e . \<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l))"

lemma sum_bot_2:
  "sum2\<^sub>M (mbot :: ('a,'b::aggregation_order) square) = mzero"
proof
  fix e
  have "(sum2\<^sub>M mbot :: ('a,'b) square) e = (\<Sum>\<^sub>(k::'a) \<Sum>\<^sub>(l::'a) bot)"
    by (unfold sum_matrix_2_def bot_matrix_def) simp
  also have "... = bot + bot"
    using agg_sum_bot aggregation.sum_0.neutral by fastforce
  also have "... = mzero e"
    by (simp add: zero_matrix_def)
  finally show "(sum2\<^sub>M mbot :: ('a,'b) square) e = mzero e"
    .
qed

lemma sum_plus_bot_2:
  fixes f :: "('a,'b::aggregation_order) square"
  shows "sum2\<^sub>M f \<oplus>\<^sub>M mbot = sum2\<^sub>M f"
proof
  fix e
  have "(sum2\<^sub>M f \<oplus>\<^sub>M mbot) e = (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) + bot"
    by (simp add: plus_matrix_def bot_matrix_def sum_matrix_2_def)
  also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l))"
    by (metis (no_types, lifting) add_add_bot aggregation.sum_0.F_one)
  also have "... = (sum2\<^sub>M f) e"
    by (simp add: sum_matrix_2_def)
  finally show "(sum2\<^sub>M f \<oplus>\<^sub>M mbot) e = (sum2\<^sub>M f) e"
    by simp
qed

lemma sum_plus_zero_2:
  fixes f :: "('a,'b::aggregation_order) square"
  shows "sum2\<^sub>M f \<oplus>\<^sub>M mzero = sum2\<^sub>M f"
  by (simp add: plus_matrix_def zero_matrix_def sum_matrix_2_def)

subsection \<open>Aggregation Lattices\<close>

text \<open>
We extend aggregation orders to dense bounded distributive lattices.
Axiom \<open>add_lattice\<close> implements the inclusion-exclusion principle at the level of edge weights.
\<close>

class aggregation_lattice = bounded_distrib_lattice + dense_lattice + aggregation_order +
  assumes add_lattice: "x + y = (x \<squnion> y) + (x \<sqinter> y)"

text \<open>
Aggregation lattices form a Stone relation algebra by reusing the meet operation as composition, using identity as converse and a standard implementation of pseudocomplement.
\<close>

class aggregation_algebra = aggregation_lattice + uminus + one + times + conv +
  assumes uminus_def [simp]: "-x = (if x = bot then top else bot)"
  assumes one_def [simp]: "1 = top"
  assumes times_def [simp]: "x * y = x \<sqinter> y"
  assumes conv_def [simp]: "x\<^sup>T = x"
begin

subclass stone_algebra
  apply unfold_locales
  using bot_meet_irreducible bot_unique by auto

subclass stone_relation_algebra
  apply unfold_locales
  prefer 9 using bot_meet_irreducible apply auto[1]
  by (simp_all add: inf.assoc le_infI2 inf_sup_distrib1 inf_sup_distrib2 inf.commute inf.left_commute)

end

text \<open>
We show that matrices over aggregation lattices form an s-algebra using the above operations.
\<close>

interpretation agg_square_s_algebra: s_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix::('a::enum,'b::aggregation_algebra) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and plus = plus_matrix and sum = sum_matrix
proof
  fix f g h :: "('a,'b) square"
  show "f \<noteq> mbot \<and> sum\<^sub>M f \<preceq> sum\<^sub>M g \<longrightarrow> h \<oplus>\<^sub>M sum\<^sub>M f \<preceq> h \<oplus>\<^sub>M sum\<^sub>M g"
  proof
    let ?h = "hd enum_class.enum"
    assume 1: "f \<noteq> mbot \<and> sum\<^sub>M f \<preceq> sum\<^sub>M g"
    hence "\<exists>k l . f (k,l) \<noteq> bot"
      by (meson agg_matrix_bot)
    hence 2: "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) \<noteq> bot"
      using agg_sum_not_bot by blast
    have "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) = (sum\<^sub>M f) (?h,?h)"
      by (simp add: sum_matrix_def)
    also have "... \<le> (sum\<^sub>M g) (?h,?h)"
      using 1 by (simp add: less_eq_matrix_def)
    also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l))"
      by (simp add: sum_matrix_def)
    finally have "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) \<le> (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l))"
      by simp
    hence 3: "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) + bot \<le> (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l)) + bot"
      by (metis (no_types, lifting) add_add_bot aggregation.sum_0.F_one)
    show "h \<oplus>\<^sub>M sum\<^sub>M f \<preceq> h \<oplus>\<^sub>M sum\<^sub>M g"
    proof (unfold less_eq_matrix_def, rule allI, rule prod_cases, unfold plus_matrix_def)
      fix i j
      have 4: "h (i,j) + (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) \<le> h (i,j) + (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l))"
        using 2 3 by (metis (no_types, lifting) add_right_isotone add.commute)
      have "h (i,j) + (sum\<^sub>M f) (i,j) = h (i,j) + (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l) else zero)"
        by (simp add: sum_matrix_def)
      also have "... = (if i = ?h \<and> j = i then h (i,j) + (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) else h (i,j) + zero)"
        by simp
      also have "... \<le> (if i = ?h \<and> j = i then h (i,j) + (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l)) else h (i,j) + zero)"
        using 4 inf.eq_iff by auto
      also have "... = h (i,j) + (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l) else zero)"
        by simp
      finally show "h (i,j) + (sum\<^sub>M f) (i,j) \<le> h (i,j) + (sum\<^sub>M g) (i,j)"
        by (simp add: sum_matrix_def)
    qed
  qed
next
  fix f :: "('a,'b) square"
  show "sum\<^sub>M f \<oplus>\<^sub>M sum\<^sub>M mbot = sum\<^sub>M f"
    by (simp add: sum_bot sum_plus_zero)
next
  fix f g :: "('a,'b) square"
  show "sum\<^sub>M f \<oplus>\<^sub>M sum\<^sub>M g = sum\<^sub>M (f \<oplus> g) \<oplus>\<^sub>M sum\<^sub>M (f \<otimes> g)"
  proof (rule ext, rule prod_cases)
    fix i j
    let ?h = "hd enum_class.enum"
    have "(sum\<^sub>M f \<oplus>\<^sub>M sum\<^sub>M g) (i,j) = (sum\<^sub>M f) (i,j) + (sum\<^sub>M g) (i,j)"
      by (simp add: plus_matrix_def)
    also have "... = (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l) else zero) + (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l) else zero)"
      by (simp add: sum_matrix_def)
    also have "... = (if i = ?h \<and> j = i then (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) + (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l)) else zero)"
      by simp
    also have "... = (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l) + g (k,l) else zero)"
      using agg_sum_distrib_2 by (metis (no_types))
    also have "... = (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l (f (k,l) \<squnion> g (k,l)) + (f (k,l) \<sqinter> g (k,l)) else zero)"
      using add_lattice aggregation.sum_0.cong by (metis (no_types, lifting))
    also have "... = (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l (f \<oplus> g) (k,l) + (f \<otimes> g) (k,l) else zero)"
      by (simp add: sup_matrix_def inf_matrix_def)
    also have "... = (if i = ?h \<and> j = i then (\<Sum>\<^sub>k \<Sum>\<^sub>l (f \<oplus> g) (k,l)) + (\<Sum>\<^sub>k \<Sum>\<^sub>l (f \<otimes> g) (k,l)) else zero)"
      using agg_sum_distrib_2 by (metis (no_types))
    also have "... = (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l (f \<oplus> g) (k,l) else zero) + (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l (f \<otimes> g) (k,l) else zero)"
      by simp
    also have "... = (sum\<^sub>M (f \<oplus> g)) (i,j) + (sum\<^sub>M (f \<otimes> g)) (i,j)"
      by (simp add: sum_matrix_def)
    also have "... = (sum\<^sub>M (f \<oplus> g) \<oplus>\<^sub>M sum\<^sub>M (f \<otimes> g)) (i,j)"
      by (simp add: plus_matrix_def)
    finally show "(sum\<^sub>M f \<oplus>\<^sub>M sum\<^sub>M g) (i,j) = (sum\<^sub>M (f \<oplus> g) \<oplus>\<^sub>M sum\<^sub>M (f \<otimes> g)) (i,j)"
      .
  qed
next
  fix f :: "('a,'b) square"
  show "sum\<^sub>M (f\<^sup>t) = sum\<^sub>M f"
  proof (rule ext, rule prod_cases)
    fix i j
    let ?h = "hd enum_class.enum"
    have "(sum\<^sub>M (f\<^sup>t)) (i,j) = (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l (f\<^sup>t) (k,l) else zero)"
      by (simp add: sum_matrix_def)
    also have "... = (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l (f (l,k))\<^sup>T else zero)"
      by (simp add: conv_matrix_def)
    also have "... = (if i = ?h \<and> j = i then \<Sum>\<^sub>k \<Sum>\<^sub>l f (l,k) else zero)"
      by simp
    also have "... = (if i = ?h \<and> j = i then \<Sum>\<^sub>l \<Sum>\<^sub>k f (l,k) else zero)"
      by (metis agg_sum_commute)
    also have "... = (sum\<^sub>M f) (i,j)"
      by (simp add: sum_matrix_def)
    finally show "(sum\<^sub>M (f\<^sup>t)) (i,j) = (sum\<^sub>M f) (i,j)"
      .
  qed
qed

text \<open>
We show the same for the alternative implementation that stores the result of aggregation in all elements of the matrix.
\<close>

interpretation agg_square_s_algebra_2: s_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix::('a::finite,'b::aggregation_algebra) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and plus = plus_matrix and sum = sum_matrix_2
proof
  fix f g h :: "('a,'b) square"
  show "f \<noteq> mbot \<and> sum2\<^sub>M f \<preceq> sum2\<^sub>M g \<longrightarrow> h \<oplus>\<^sub>M sum2\<^sub>M f \<preceq> h \<oplus>\<^sub>M sum2\<^sub>M g"
  proof
    assume 1: "f \<noteq> mbot \<and> sum2\<^sub>M f \<preceq> sum2\<^sub>M g"
    hence "\<exists>k l . f (k,l) \<noteq> bot"
      by (meson agg_matrix_bot)
    hence 2: "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) \<noteq> bot"
      using agg_sum_not_bot by blast
    obtain c :: 'a where True
      by simp
    have "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) = (sum2\<^sub>M f) (c,c)"
      by (simp add: sum_matrix_2_def)
    also have "... \<le> (sum2\<^sub>M g) (c,c)"
      using 1 by (simp add: less_eq_matrix_def)
    also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l))"
      by (simp add: sum_matrix_2_def)
    finally have "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) \<le> (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l))"
      by simp
    hence 3: "(\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) + bot \<le> (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l)) + bot"
      by (metis (no_types, lifting) add_add_bot aggregation.sum_0.F_one)
    show "h \<oplus>\<^sub>M sum2\<^sub>M f \<preceq> h \<oplus>\<^sub>M sum2\<^sub>M g"
    proof (unfold less_eq_matrix_def, rule allI, unfold plus_matrix_def)
      fix e
      have "h e + (sum2\<^sub>M f) e = h e + (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l))"
        by (simp add: sum_matrix_2_def)
      also have "... \<le> h e + (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l))"
        using 2 3 by (metis (no_types, lifting) add_right_isotone add.commute)
      finally show "h e + (sum2\<^sub>M f) e \<le> h e + (sum2\<^sub>M g) e"
        by (simp add: sum_matrix_2_def)
    qed
  qed
next
  fix f :: "('a,'b) square"
  show "sum2\<^sub>M f \<oplus>\<^sub>M sum2\<^sub>M mbot = sum2\<^sub>M f"
    by (simp add: sum_bot_2 sum_plus_zero_2)
next
  fix f g :: "('a,'b) square"
  show "sum2\<^sub>M f \<oplus>\<^sub>M sum2\<^sub>M g = sum2\<^sub>M (f \<oplus> g) \<oplus>\<^sub>M sum2\<^sub>M (f \<otimes> g)"
  proof
    fix e
    have "(sum2\<^sub>M f \<oplus>\<^sub>M sum2\<^sub>M g) e = (sum2\<^sub>M f) e + (sum2\<^sub>M g) e"
      by (simp add: plus_matrix_def)
    also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l)) + (\<Sum>\<^sub>k \<Sum>\<^sub>l g (k,l))"
      by (simp add: sum_matrix_2_def)
    also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l f (k,l) + g (k,l))"
      using agg_sum_distrib_2 by (metis (no_types))
    also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l (f (k,l) \<squnion> g (k,l)) + (f (k,l) \<sqinter> g (k,l)))"
      using add_lattice aggregation.sum_0.cong by (metis (no_types, lifting))
    also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l (f \<oplus> g) (k,l) + (f \<otimes> g) (k,l))"
      by (simp add: sup_matrix_def inf_matrix_def)
    also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l (f \<oplus> g) (k,l)) + (\<Sum>\<^sub>k \<Sum>\<^sub>l (f \<otimes> g) (k,l))"
      using agg_sum_distrib_2 by (metis (no_types))
    also have "... = (sum2\<^sub>M (f \<oplus> g)) e + (sum2\<^sub>M (f \<otimes> g)) e"
      by (simp add: sum_matrix_2_def)
    also have "... = (sum2\<^sub>M (f \<oplus> g) \<oplus>\<^sub>M sum2\<^sub>M (f \<otimes> g)) e"
      by (simp add: plus_matrix_def)
    finally show "(sum2\<^sub>M f \<oplus>\<^sub>M sum2\<^sub>M g) e = (sum2\<^sub>M (f \<oplus> g) \<oplus>\<^sub>M sum2\<^sub>M (f \<otimes> g)) e"
      .
  qed
next
  fix f :: "('a,'b) square"
  show "sum2\<^sub>M (f\<^sup>t) = sum2\<^sub>M f"
  proof
    fix e
    have "(sum2\<^sub>M (f\<^sup>t)) e = (\<Sum>\<^sub>k \<Sum>\<^sub>l (f\<^sup>t) (k,l))"
      by (simp add: sum_matrix_2_def)
    also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l (f (l,k))\<^sup>T)"
      by (simp add: conv_matrix_def)
    also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l f (l,k))"
      by simp
    also have "... = (\<Sum>\<^sub>l \<Sum>\<^sub>k f (l,k))"
      by (metis agg_sum_commute)
    also have "... = (sum2\<^sub>M f) e"
      by (simp add: sum_matrix_2_def)
    finally show "(sum2\<^sub>M (f\<^sup>t)) e = (sum2\<^sub>M f) e"
      .
  qed
qed

subsection \<open>Matrix Minimisation\<close>

text \<open>
We construct an operation that finds the minimum entry of a matrix.
Because a matrix can have several entries with the same minimum value, we introduce a lexicographic order on the indices to make the operation deterministic.
The order is obtained by enumerating the universe of the index.
\<close>

primrec enum_pos' :: "'a list \<Rightarrow> 'a::enum \<Rightarrow> nat" where
  "enum_pos' Nil x = 0"
| "enum_pos' (y#ys) x = (if x = y then 0 else 1 + enum_pos' ys x)"

lemma enum_pos'_inverse:
  "List.member xs x \<Longrightarrow> xs!(enum_pos' xs x) = x"
  apply (induct xs)
  apply (simp add: member_rec(2))
  by (metis diff_add_inverse enum_pos'.simps(2) less_one member_rec(1) not_add_less1 nth_Cons')

text \<open>
The following function finds the position of an index in the enumerated universe.
\<close>

fun enum_pos :: "'a::enum \<Rightarrow> nat" where "enum_pos x = enum_pos' (enum_class.enum::'a list) x"

lemma enum_pos_inverse [simp]:
  "enum_class.enum!(enum_pos x) = x"
  apply (unfold enum_pos.simps)
  apply (rule enum_pos'_inverse)
  by (metis in_enum List.member_def)

lemma enum_pos_injective [simp]:
  "enum_pos x = enum_pos y \<Longrightarrow> x = y"
  by (metis enum_pos_inverse)

text \<open>
The position in the enumerated universe determines the order.
\<close>

abbreviation enum_pos_less_eq :: "'a::enum \<Rightarrow> 'a \<Rightarrow> bool" where "enum_pos_less_eq x y \<equiv> (enum_pos x \<le> enum_pos y)"
abbreviation enum_pos_less :: "'a::enum \<Rightarrow> 'a \<Rightarrow> bool" where "enum_pos_less x y \<equiv> (enum_pos x < enum_pos y)"

sublocale enum < enum_order: order where less_eq = "\<lambda>x y . enum_pos_less_eq x y" and less = "\<lambda>x y . enum_pos x < enum_pos y"
  apply unfold_locales
  by auto

text \<open>
Based on this, a lexicographic order is defined on pairs, which represent locations in a matrix.
\<close>

abbreviation enum_lex_less :: "'a::enum \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where "enum_lex_less \<equiv> (\<lambda>(i,j) (k,l) . enum_pos_less i k \<or> (i = k \<and> enum_pos_less j l))"
abbreviation enum_lex_less_eq :: "'a::enum \<times> 'a \<Rightarrow> 'a \<times> 'a \<Rightarrow> bool" where "enum_lex_less_eq \<equiv> (\<lambda>(i,j) (k,l) . enum_pos_less i k \<or> (i = k \<and> enum_pos_less_eq j l))"

text \<open>
The $m$-operation determines the location of the non-$\bot$ minimum element which is first in the lexicographic order.
The result is returned as a regular matrix with $\top$ at that location and $\bot$ everywhere else.
In the weighted-graph model, this represents a single unweighted edge of the graph.
\<close>

definition minarc_matrix :: "('a::enum,'b::{bot,ord,plus,top}) square \<Rightarrow> ('a,'b) square" ("minarc\<^sub>M _" [80] 80) where "minarc_matrix f = (\<lambda>e . if f e \<noteq> bot \<and> (\<forall>d . (f d \<noteq> bot \<longrightarrow> (f e + bot \<le> f d + bot \<and> (enum_lex_less d e \<longrightarrow> f e + bot \<noteq> f d + bot)))) then top else bot)"

lemma minarc_at_most_one:
  fixes f :: "('a::enum,'b::{aggregation_order,top}) square"
  assumes "(minarc\<^sub>M f) e \<noteq> bot"
      and "(minarc\<^sub>M f) d \<noteq> bot"
    shows "e = d"
proof -
  have 1: "f e + bot \<le> f d + bot"
    by (metis assms minarc_matrix_def)
  have "f d + bot \<le> f e + bot"
    by (metis assms minarc_matrix_def)
  hence "f e + bot = f d + bot"
    using 1 by simp
  hence "\<not> enum_lex_less d e \<and> \<not> enum_lex_less e d"
    using assms by (unfold minarc_matrix_def) (metis (lifting))
  thus ?thesis
    using enum_pos_injective less_linear by auto
qed

subsection \<open>Linear Aggregation Lattices\<close>

text \<open>
We now assume that the aggregation order is linear and forms a bounded lattice.
It follows that these structures are aggregation lattices.
A linear order on matrix entries is necessary to obtain a unique minimum entry.
\<close>

class linear_aggregation_lattice = linear_bounded_lattice + aggregation_order
begin

subclass aggregation_lattice
  apply unfold_locales
  by (metis add_commute sup_inf_selective)

sublocale heyting: bounded_heyting_lattice where implies = "\<lambda>x y . if x \<le> y then top else y"
  apply unfold_locales
  by (simp add: inf_less_eq)

end

text \<open>
Every non-empty set with a transitive total relation has a least element with respect to this relation.
\<close>

lemma least_order:
  assumes transitive: "\<forall>x y z . le x y \<and> le y z \<longrightarrow> le x z"
      and total: "\<forall>x y . le x y \<or> le y x"
    shows "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<exists>x . x \<in> A \<and> (\<forall>y . y \<in> A \<longrightarrow> le x y)"
proof (induct A rule: finite_ne_induct)
  case singleton
  thus ?case
    using total by auto
next
  case insert
  thus ?case
    by (metis insert_iff transitive total)
qed

lemma minarc_at_least_one:
  fixes f :: "('a::enum,'b::linear_aggregation_lattice) square"
  assumes "f \<noteq> mbot"
    shows "\<exists>e . (minarc\<^sub>M f) e = top"
proof -
  let ?nbe = "{ (e,f e) | e . f e \<noteq> bot }"
  have 1: "finite ?nbe"
    using finite_code finite_image_set by blast
  have 2: "?nbe \<noteq> {}"
    using assms agg_matrix_bot by fastforce
  let ?le = "\<lambda>(e::'a \<times> 'a,fe::'b) (d::'a \<times> 'a,fd) . fe + bot \<le> fd + bot"
  have 3: "\<forall>x y z . ?le x y \<and> ?le y z \<longrightarrow> ?le x z"
    by auto
  have 4: "\<forall>x y . ?le x y \<or> ?le y x"
    by (simp add: linear)
  have "\<exists>x . x \<in> ?nbe \<and> (\<forall>y . y \<in> ?nbe \<longrightarrow> ?le x y)"
    by (rule least_order, rule 3, rule 4, rule 1, rule 2)
  then obtain e fe where 5: "(e,fe) \<in> ?nbe \<and> (\<forall>y . y \<in> ?nbe \<longrightarrow> ?le (e,fe) y)"
    by auto
  let ?me = "{ e . f e \<noteq> bot \<and> f e + bot = fe + bot }"
  have 6: "finite ?me"
    using finite_code finite_image_set by blast
  have 7: "?me \<noteq> {}"
    using 5 by auto
  have 8: "\<forall>x y z . enum_lex_less_eq x y \<and> enum_lex_less_eq y z \<longrightarrow> enum_lex_less_eq x z"
    by auto
  have 9: "\<forall>x y . enum_lex_less_eq x y \<or> enum_lex_less_eq y x"
    by auto
  have "\<exists>x . x \<in> ?me \<and> (\<forall>y . y \<in> ?me \<longrightarrow> enum_lex_less_eq x y)"
    by (rule least_order, rule 8, rule 9, rule 6, rule 7)
  then obtain m where 10: "m \<in> ?me \<and> (\<forall>y . y \<in> ?me \<longrightarrow> enum_lex_less_eq m y)"
    by auto
  have 11: "f m \<noteq> bot"
    using 10 5 by auto
  have 12: "\<forall>d. f d \<noteq> bot \<longrightarrow> f m + bot \<le> f d + bot"
    using 10 5 by simp
  have "\<forall>d. f d \<noteq> bot \<and> enum_lex_less d m \<longrightarrow> f m + bot \<noteq> f d + bot"
    using 10 by fastforce
  hence "(minarc\<^sub>M f) m = top"
    using 11 12 by (simp add: minarc_matrix_def)
  thus ?thesis
    by blast
qed

text \<open>
Linear aggregation lattices form a Stone relation algebra by reusing the meet operation as composition, using identity as converse and a standard implementation of pseudocomplement.
\<close>

class linear_aggregation_algebra = linear_aggregation_lattice + uminus + one + times + conv +
  assumes uminus_def_2 [simp]: "-x = (if x = bot then top else bot)"
  assumes one_def_2 [simp]: "1 = top"
  assumes times_def_2 [simp]: "x * y = x \<sqinter> y"
  assumes conv_def_2 [simp]: "x\<^sup>T = x"
begin

subclass aggregation_algebra
  apply unfold_locales
  using inf_dense by auto

lemma regular_bot_top_2:
  "regular x \<longleftrightarrow> x = bot \<or> x = top"
  by simp

sublocale heyting: heyting_stone_algebra where implies = "\<lambda>x y . if x \<le> y then top else y"
  apply unfold_locales
  apply (simp add: antisym)
  by auto

end

text \<open>
We show that matrices over linear aggregation lattices form an m-algebra using the above operations.
\<close>

interpretation agg_square_m_algebra: m_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix::('a::enum,'b::linear_aggregation_algebra) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and plus = plus_matrix and sum = sum_matrix and minarc = minarc_matrix
proof
  fix f :: "('a,'b) square"
  show "minarc\<^sub>M f \<preceq> \<ominus>\<ominus>f"
  proof (unfold less_eq_matrix_def, rule allI)
    fix e :: "'a \<times> 'a"
    have "(minarc\<^sub>M f) e \<le> (if f e \<noteq> bot then top else --(f e))"
      by (simp add: minarc_matrix_def)
    also have "... = --(f e)"
      by simp
    also have "... = (\<ominus>\<ominus>f) e"
      by (simp add: uminus_matrix_def)
    finally show "(minarc\<^sub>M f) e \<le> (\<ominus>\<ominus>f) e"
      .
  qed
next
  fix f :: "('a,'b) square"
  let ?at = "bounded_distrib_allegory_signature.arc mone times_matrix less_eq_matrix mtop conv_matrix"
  show "f \<noteq> mbot \<longrightarrow> ?at (minarc\<^sub>M f)"
  proof
    assume 1: "f \<noteq> mbot"
    have "minarc\<^sub>M f \<odot> mtop \<odot> (minarc\<^sub>M f \<odot> mtop)\<^sup>t = minarc\<^sub>M f \<odot> mtop \<odot> (minarc\<^sub>M f)\<^sup>t"
      by (metis matrix_bounded_idempotent_semiring.surjective_top_closed matrix_monoid.mult_assoc matrix_stone_relation_algebra.conv_dist_comp matrix_stone_relation_algebra.conv_top)
    also have "... \<preceq> mone"
    proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
      fix i j
      have "(minarc\<^sub>M f \<odot> mtop \<odot> (minarc\<^sub>M f)\<^sup>t) (i,j) = (\<Squnion>\<^sub>l (\<Squnion>\<^sub>k (minarc\<^sub>M f) (i,k) * mtop (k,l)) * ((minarc\<^sub>M f)\<^sup>t) (l,j))"
        by (simp add: times_matrix_def)
      also have "... = (\<Squnion>\<^sub>l (\<Squnion>\<^sub>k (minarc\<^sub>M f) (i,k) * top) * ((minarc\<^sub>M f) (j,l))\<^sup>T)"
        by (simp add: top_matrix_def conv_matrix_def)
      also have "... = (\<Squnion>\<^sub>l \<Squnion>\<^sub>k (minarc\<^sub>M f) (i,k) * top * ((minarc\<^sub>M f) (j,l))\<^sup>T)"
        by (metis comp_right_dist_sum)
      also have "... = (\<Squnion>\<^sub>l \<Squnion>\<^sub>k if i = j \<and> l = k then (minarc\<^sub>M f) (i,k) * top * ((minarc\<^sub>M f) (j,l))\<^sup>T else bot)"
        apply (rule sup_monoid.sum.cong)
        apply simp
        by (metis (no_types, lifting) comp_left_zero comp_right_zero conv_bot prod.inject minarc_at_most_one)
      also have "... = (if i = j then (\<Squnion>\<^sub>l \<Squnion>\<^sub>k if l = k then (minarc\<^sub>M f) (i,k) * top * ((minarc\<^sub>M f) (j,l))\<^sup>T else bot) else bot)"
        by auto
      also have "... \<le> (if i = j then top else bot)"
        by simp
      also have "... = mone (i,j)"
        by (simp add: one_matrix_def)
      finally show "(minarc\<^sub>M f \<odot> mtop \<odot> (minarc\<^sub>M f)\<^sup>t) (i,j) \<le> mone (i,j)"
        .
    qed
    finally have 2: "minarc\<^sub>M f \<odot> mtop \<odot> (minarc\<^sub>M f \<odot> mtop)\<^sup>t \<preceq> mone"
      .
    have 3: "mtop \<odot> (minarc\<^sub>M f \<odot> mtop) = mtop"
    proof (rule ext, rule prod_cases)
      fix i j
      from minarc_at_least_one obtain ei ej where "(minarc\<^sub>M f) (ei,ej) = top"
        using 1 by force
      hence 4: "top * top \<le> (\<Squnion>\<^sub>l (minarc\<^sub>M f) (ei,l) * top)"
        by (metis comp_inf.ub_sum)
      have "top * (\<Squnion>\<^sub>l (minarc\<^sub>M f) (ei,l) * top) \<le> (\<Squnion>\<^sub>k top * (\<Squnion>\<^sub>l (minarc\<^sub>M f) (k,l) * top))"
        by (rule comp_inf.ub_sum)
      hence "top \<le> (\<Squnion>\<^sub>k top * (\<Squnion>\<^sub>l (minarc\<^sub>M f) (k,l) * top))"
        using 4 by auto
      also have "... = (\<Squnion>\<^sub>k mtop (i,k) * (\<Squnion>\<^sub>l (minarc\<^sub>M f) (k,l) * mtop (l,j)))"
        by (simp add: top_matrix_def)
      also have "... = (mtop \<odot> (minarc\<^sub>M f \<odot> mtop)) (i,j)"
        by (simp add: times_matrix_def)
      finally show "(mtop \<odot> (minarc\<^sub>M f \<odot> mtop)) (i,j) = mtop (i,j)"
        by (simp add: eq_iff top_matrix_def)
    qed
    have "(minarc\<^sub>M f)\<^sup>t \<odot> mtop \<odot> ((minarc\<^sub>M f)\<^sup>t \<odot> mtop)\<^sup>t = (minarc\<^sub>M f)\<^sup>t \<odot> mtop \<odot> (minarc\<^sub>M f)"
      by (metis matrix_stone_relation_algebra.comp_associative matrix_stone_relation_algebra.conv_dist_comp matrix_stone_relation_algebra.conv_involutive matrix_stone_relation_algebra.conv_top matrix_bounded_idempotent_semiring.surjective_top_closed)
    also have "... \<preceq> mone"
    proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
      fix i j
      have "((minarc\<^sub>M f)\<^sup>t \<odot> mtop \<odot> minarc\<^sub>M f) (i,j) = (\<Squnion>\<^sub>l (\<Squnion>\<^sub>k ((minarc\<^sub>M f)\<^sup>t) (i,k) * mtop (k,l)) * (minarc\<^sub>M f) (l,j))"
        by (simp add: times_matrix_def)
      also have "... = (\<Squnion>\<^sub>l (\<Squnion>\<^sub>k ((minarc\<^sub>M f) (k,i))\<^sup>T * top) * (minarc\<^sub>M f) (l,j))"
        by (simp add: top_matrix_def conv_matrix_def)
      also have "... = (\<Squnion>\<^sub>l \<Squnion>\<^sub>k ((minarc\<^sub>M f) (k,i))\<^sup>T * top * (minarc\<^sub>M f) (l,j))"
        by (metis comp_right_dist_sum)
      also have "... = (\<Squnion>\<^sub>l \<Squnion>\<^sub>k if i = j \<and> l = k then ((minarc\<^sub>M f) (k,i))\<^sup>T * top * (minarc\<^sub>M f) (l,j) else bot)"
        apply (rule sup_monoid.sum.cong)
        apply simp
        by (metis (no_types, lifting) comp_left_zero comp_right_zero conv_bot prod.inject minarc_at_most_one)
      also have "... = (if i = j then (\<Squnion>\<^sub>l \<Squnion>\<^sub>k if l = k then ((minarc\<^sub>M f) (k,i))\<^sup>T * top * (minarc\<^sub>M f) (l,j) else bot) else bot)"
        by auto
      also have "... \<le> (if i = j then top else bot)"
        by simp
      also have "... = mone (i,j)"
        by (simp add: one_matrix_def)
      finally show "((minarc\<^sub>M f)\<^sup>t \<odot> mtop \<odot> (minarc\<^sub>M f)) (i,j) \<le> mone (i,j)"
        .
    qed
    finally have 5: "(minarc\<^sub>M f)\<^sup>t \<odot> mtop \<odot> ((minarc\<^sub>M f)\<^sup>t \<odot> mtop)\<^sup>t \<preceq> mone"
      .
    have "mtop \<odot> ((minarc\<^sub>M f)\<^sup>t \<odot> mtop) = mtop"
      using 3 by (metis matrix_monoid.mult_assoc matrix_stone_relation_algebra.conv_dist_comp matrix_stone_relation_algebra.conv_top)
    thus "?at (minarc\<^sub>M f)"
      using 2 3 5 by blast
  qed
next
  fix f g :: "('a,'b) square"
  let ?at = "bounded_distrib_allegory_signature.arc mone times_matrix less_eq_matrix mtop conv_matrix"
  show "?at g \<and> g \<otimes> f \<noteq> mbot \<longrightarrow> sum\<^sub>M (minarc\<^sub>M f \<otimes> f) \<preceq> sum\<^sub>M (g \<otimes> f)"
  proof
    assume 1: "?at g \<and> g \<otimes> f \<noteq> mbot"
    hence 2: "g = \<ominus>\<ominus>g"
      using matrix_stone_relation_algebra.arc_regular by blast
    show "sum\<^sub>M (minarc\<^sub>M f \<otimes> f) \<preceq> sum\<^sub>M (g \<otimes> f)"
    proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
      fix i j
      from minarc_at_least_one obtain ei ej where 3: "(minarc\<^sub>M f) (ei,ej) = top"
        using 1 by force
      hence 4: "\<forall>k l . \<not>(k = ei \<and> l = ej) \<longrightarrow> (minarc\<^sub>M f) (k,l) = bot"
        by (metis (mono_tags, hide_lams) bot.extremum inf.bot_unique prod.inject minarc_at_most_one)
      from agg_matrix_bot obtain di dj where 5: "(g \<otimes> f) (di,dj) \<noteq> bot"
        using 1 by force
      hence 6: "g (di,dj) \<noteq> bot"
        by (metis inf_bot_left inf_matrix_def)
      hence 7: "g (di,dj) = top"
        using 2 by (metis uminus_matrix_def uminus_def)
      hence 8: "(g \<otimes> f) (di,dj) = f (di,dj)"
        by (metis inf_matrix_def inf_top.left_neutral)
      have 9: "\<forall>k l . k \<noteq> di \<longrightarrow> g (k,l) = bot"
      proof (intro allI, rule impI)
        fix k l
        assume 10: "k \<noteq> di"
        have "top * (g (k,l))\<^sup>T = g (di,dj) * top * (g\<^sup>t) (l,k)"
          using 7 by (simp add: conv_matrix_def)
        also have "... \<le> (\<Squnion>\<^sub>n g (di,n) * top) * (g\<^sup>t) (l,k)"
          by (metis comp_inf.ub_sum comp_right_dist_sum)
        also have "... \<le> (\<Squnion>\<^sub>m (\<Squnion>\<^sub>n g (di,n) * top) * (g\<^sup>t) (m,k))"
          by (metis comp_inf.ub_sum)
        also have "... = (g \<odot> mtop \<odot> g\<^sup>t) (di,k)"
          by (simp add: times_matrix_def top_matrix_def)
        also have "... \<le> mone (di,k)"
          using 1 by (metis matrix_stone_relation_algebra.arc_expanded less_eq_matrix_def)
        also have "... = bot"
          apply (unfold one_matrix_def)
          using 10 by auto
        finally have "g (k,l) \<noteq> top"
          using 5 by (metis bot.extremum conv_def inf.bot_unique mult.left_neutral one_def)
        thus "g (k,l) = bot"
          using 2 by (metis uminus_def uminus_matrix_def)
      qed
      have "\<forall>k l . l \<noteq> dj \<longrightarrow> g (k,l) = bot"
      proof (intro allI, rule impI)
        fix k l
        assume 11: "l \<noteq> dj"
        have "(g (k,l))\<^sup>T * top = (g\<^sup>t) (l,k) * top * g (di,dj)"
          using 7 by (simp add: comp_associative conv_matrix_def)
        also have "... \<le> (\<Squnion>\<^sub>n (g\<^sup>t) (l,n) * top) * g (di,dj)"
          by (metis comp_inf.ub_sum comp_right_dist_sum)
        also have "... \<le> (\<Squnion>\<^sub>m (\<Squnion>\<^sub>n (g\<^sup>t) (l,n) * top) * g (m,dj))"
          by (metis comp_inf.ub_sum)
        also have "... = (g\<^sup>t \<odot> mtop \<odot> g) (l,dj)"
          by (simp add: times_matrix_def top_matrix_def)
        also have "... \<le> mone (l,dj)"
          using 1 by (metis matrix_stone_relation_algebra.arc_expanded less_eq_matrix_def)
        also have "... = bot"
          apply (unfold one_matrix_def)
          using 11 by auto
        finally have "g (k,l) \<noteq> top"
          using 5 by (metis bot.extremum comp_right_one conv_def one_def top.extremum_unique)
        thus "g (k,l) = bot"
          using 2 by (metis uminus_def uminus_matrix_def)
      qed
      hence 12: "\<forall>k l . \<not>(k = di \<and> l = dj) \<longrightarrow> (g \<otimes> f) (k,l) = bot"
        using 9 by (metis inf_bot_left inf_matrix_def)
      have "(\<Sum>\<^sub>k \<Sum>\<^sub>l (minarc\<^sub>M f \<otimes> f) (k,l)) = (\<Sum>\<^sub>k \<Sum>\<^sub>l if k = ei \<and> l = ej then (minarc\<^sub>M f \<otimes> f) (k,l) else (minarc\<^sub>M f \<otimes> f) (k,l))"
        by simp
      also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l if k = ei \<and> l = ej then (minarc\<^sub>M f \<otimes> f) (k,l) else (minarc\<^sub>M f) (k,l) \<sqinter> f (k,l))"
        by (unfold inf_matrix_def) simp
      also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l if k = ei \<and> l = ej then (minarc\<^sub>M f \<otimes> f) (k,l) else bot)"
        apply (rule aggregation.sum_0.cong)
        apply simp
        using 4 by (metis inf_bot_left)
      also have "... = (minarc\<^sub>M f \<otimes> f) (ei,ej) + bot"
        by (unfold agg_delta_2) simp
      also have "... = f (ei,ej) + bot"
        using 3 by (simp add: inf_matrix_def)
      also have "... \<le> (g \<otimes> f) (di,dj) + bot"
        using 3 5 6 7 8 by (metis minarc_matrix_def)
      also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l if k = di \<and> l = dj then (g \<otimes> f) (k,l) else bot)"
        by (unfold agg_delta_2) simp
      also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l if k = di \<and> l = dj then (g \<otimes> f) (k,l) else (g \<otimes> f) (k,l))"
        apply (rule aggregation.sum_0.cong)
        apply simp
        using 12 by metis
      also have "... = (\<Sum>\<^sub>k \<Sum>\<^sub>l (g \<otimes> f) (k,l))"
        by simp
      finally show "(sum\<^sub>M (minarc\<^sub>M f \<otimes> f)) (i,j) \<le> (sum\<^sub>M (g \<otimes> f)) (i,j)"
        by (simp add: sum_matrix_def)
    qed
  qed
next
  fix f g :: "('a,'b) square"
  let ?h = "hd enum_class.enum"
  show "sum\<^sub>M f \<preceq> sum\<^sub>M g \<or> sum\<^sub>M g \<preceq> sum\<^sub>M f"
  proof (cases "(sum\<^sub>M f) (?h,?h) \<le> (sum\<^sub>M g) (?h,?h)")
    case 1: True
    have "sum\<^sub>M f \<preceq> sum\<^sub>M g"
      apply (unfold less_eq_matrix_def, rule allI, rule prod_cases)
      using 1 by (unfold sum_matrix_def) auto
    thus ?thesis
      by simp
  next
    case False
    hence 2: "(sum\<^sub>M g) (?h,?h) \<le> (sum\<^sub>M f) (?h,?h)"
      by (simp add: linear)
    have "sum\<^sub>M g \<preceq> sum\<^sub>M f"
      apply (unfold less_eq_matrix_def, rule allI, rule prod_cases)
      using 2 by (unfold sum_matrix_def) auto
    thus ?thesis
      by simp
  qed
next
  have "finite { f :: ('a,'b) square . (\<forall>e . regular (f e)) }"
    by (unfold regular_bot_top_2, rule finite_set_of_finite_funs_pred) auto
  thus "finite { f :: ('a,'b) square . matrix_p_algebra.regular f }"
    by (unfold uminus_matrix_def) meson
qed

text \<open>
We show the same for the alternative implementation that stores the result of aggregation in all elements of the matrix.
\<close>

interpretation agg_square_m_algebra_2: m_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix::('a::enum,'b::linear_aggregation_algebra) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and plus = plus_matrix and sum = sum_matrix_2 and minarc = minarc_matrix
proof
  fix f :: "('a,'b) square"
  show "minarc\<^sub>M f \<preceq> \<ominus>\<ominus>f"
    by (simp add: agg_square_m_algebra.minarc_below)
next
  fix f :: "('a,'b) square"
  let ?at = "bounded_distrib_allegory_signature.arc mone times_matrix less_eq_matrix mtop conv_matrix"
  show "f \<noteq> mbot \<longrightarrow> ?at (minarc\<^sub>M f)"
    by (simp add: agg_square_m_algebra.minarc_arc)
next
  fix f g :: "('a,'b) square"
  let ?at = "bounded_distrib_allegory_signature.arc mone times_matrix less_eq_matrix mtop conv_matrix"
  show "?at g \<and> g \<otimes> f \<noteq> mbot \<longrightarrow> sum2\<^sub>M (minarc\<^sub>M f \<otimes> f) \<preceq> sum2\<^sub>M (g \<otimes> f)"
  proof
    let ?h = "hd enum_class.enum"
    assume "?at g \<and> g \<otimes> f \<noteq> mbot"
    hence "sum\<^sub>M (minarc\<^sub>M f \<otimes> f) \<preceq> sum\<^sub>M (g \<otimes> f)"
      by (simp add: agg_square_m_algebra.minarc_min)
    hence "(sum\<^sub>M (minarc\<^sub>M f \<otimes> f)) (?h,?h) \<le> (sum\<^sub>M (g \<otimes> f)) (?h,?h)"
      by (simp add: less_eq_matrix_def)
    thus "sum2\<^sub>M (minarc\<^sub>M f \<otimes> f) \<preceq> sum2\<^sub>M (g \<otimes> f)"
      by (simp add: sum_matrix_def sum_matrix_2_def less_eq_matrix_def)
  qed
next
  fix f g :: "('a,'b) square"
  let ?h = "hd enum_class.enum"
  have "sum\<^sub>M f \<preceq> sum\<^sub>M g \<or> sum\<^sub>M g \<preceq> sum\<^sub>M f"
    by (simp add: agg_square_m_algebra.sum_linear)
  hence "(sum\<^sub>M f) (?h,?h) \<le> (sum\<^sub>M g) (?h,?h) \<or> (sum\<^sub>M g) (?h,?h) \<le> (sum\<^sub>M f) (?h,?h)"
    using less_eq_matrix_def by auto
  thus "sum2\<^sub>M f \<preceq> sum2\<^sub>M g \<or> sum2\<^sub>M g \<preceq> sum2\<^sub>M f"
    by (simp add: sum_matrix_def sum_matrix_2_def less_eq_matrix_def)
next
  show "finite { f :: ('a,'b) square . matrix_p_algebra.regular f }"
    by (simp add: agg_square_m_algebra.finite_regular)
qed

text \<open>
By defining the Kleene star as $\top$ aggregation lattices form a Kleene algebra.
\<close>

class aggregation_kleene_algebra = aggregation_algebra + star +
  assumes star_def [simp]: "x\<^sup>\<star> = top"
begin

subclass stone_kleene_relation_algebra
  apply unfold_locales
  by (simp_all add: inf.assoc le_infI2 inf_sup_distrib1 inf_sup_distrib2)

end

class linear_aggregation_kleene_algebra = linear_aggregation_algebra + star +
  assumes star_def_2 [simp]: "x\<^sup>\<star> = top"
begin

subclass aggregation_kleene_algebra
  apply unfold_locales
  by simp

end

interpretation agg_square_m_kleene_algebra: m_kleene_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix::('a::enum,'b::linear_aggregation_kleene_algebra) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and star = star_matrix and plus = plus_matrix and sum = sum_matrix and minarc = minarc_matrix ..

interpretation agg_square_m_kleene_algebra_2: m_kleene_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix::('a::enum,'b::linear_aggregation_kleene_algebra) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and star = star_matrix and plus = plus_matrix and sum = sum_matrix_2 and minarc = minarc_matrix ..

end

