(* Author: Peter Gammie
   Author: Andreas Lochbihler, ETH Zurich *)

section \<open>The Stern-Brocot Tree\<close>

theory Stern_Brocot_Tree
imports
  HOL.Rat
  "HOL-Library.Sublist"
  Cotree_Algebra
  Applicative_Lifting.Stream_Algebra
begin

text\<open>
  The Stern-Brocot tree is discussed at length by \citet[\S4.5]{GrahamKnuthPatashnik1994CM}.
  In essence the tree enumerates the rational numbers in their lowest terms by constructing the
  \<open>mediant\<close> of two bounding fractions.
\<close>

type_synonym fraction = "nat \<times> nat"

definition mediant :: "fraction \<times> fraction \<Rightarrow> fraction"
where "mediant \<equiv> \<lambda>((a, c), (b, d)). (a + b, c + d)"

definition stern_brocot :: "fraction tree"
where 
  "stern_brocot = unfold_tree
    (\<lambda>(lb, ub). mediant (lb, ub))
    (\<lambda>(lb, ub). (lb, mediant (lb, ub)))
    (\<lambda>(lb, ub). (mediant (lb, ub), ub))
    ((0, 1), (1, 0))"

text\<open>
  This process is visualised in Figure~\ref{fig:stern-brocot-iterate}.
  Intuitively each node is labelled with the mediant of it's rightmost and leftmost ancestors.

  \begin{figure}
    \centering
    \begin{tikzpicture}[auto,thick,node distance=3cm,main node/.style={circle,draw,font=\sffamily\Large\bfseries}]
      \node[main node] (0) at (0, 0) {$\frac{1}{1}$};
      \node[main node] (1) at (-4, 1) {$\frac{0}{1}$};
      \node[main node] (2) at (4, 1) {$\frac{1}{0}$};
      \node[main node] (3) at (-2, -1) {$\frac{1}{2}$};
      \node[main node] (4) at (2, -1) {$\frac{2}{1}$};
      \node[main node] (5) at (-3, -2) {$\frac{1}{3}$};
      \node[main node] (6) at (3, -2) {$\frac{3}{1}$};
      \node[main node] (7) at (-1, -2) {$\frac{2}{3}$};
      \node[main node] (8) at (1, -2) {$\frac{3}{2}$};
      \node (9) at (-3.5, -3) {};
      \node (10) at (-2.5, -3) {};
      \node (11) at (-1.5, -3) {};
      \node (12) at (-0.5, -3) {};
      \node (13) at (0.5, -3) {};
      \node (14) at (1.5, -3) {};
      \node (15) at (2.5, -3) {};
      \node (16) at (3.5, -3) {};
      \path
        (1) edge[dashed] (0)
        (2) edge[dashed] (0)
        (0) edge (3)
        (0) edge (4)
        (3) edge (5)
        (3) edge (7)
        (4) edge (6)
        (4) edge (8)
        (5) edge[dotted] (9)
        (5) edge[dotted] (10)
        (6) edge[dotted] (15)
        (6) edge[dotted] (16)
        (7) edge[dotted] (11)
        (7) edge[dotted] (12)
        (8) edge[dotted] (13)
        (8) edge[dotted] (14);
    \end{tikzpicture}
    \label{fig:stern-brocot-iterate}
    \caption{Constructing the Stern-Brocot tree iteratively.}
  \end{figure}
  
  Our ultimate goal is to show that the Stern-Brocot tree contains all rationals (in lowest terms),
  and that each occurs exactly once in the tree. A proof is sketched in \citet[\S4.5]{GrahamKnuthPatashnik1994CM}.
\<close>

subsection \<open>Specification via a recursion equation\<close>

text \<open>
  \cite{Hinze2009JFP} derives the following recurrence relation for the Stern-Brocot tree. 
  We will show in \S\ref{section:eq:rec:iterative} that his derivation is sound with respect to the
  standard iterative definition of the tree shown above.
\<close>

abbreviation succ :: "fraction \<Rightarrow> fraction"
where "succ \<equiv> \<lambda>(m, n). (m + n, n)"

abbreviation recip :: "fraction \<Rightarrow> fraction"
where "recip \<equiv> \<lambda>(m, n). (n, m)"

corec stern_brocot_recurse :: "fraction tree"
where
  "stern_brocot_recurse =
   Node (1, 1)
     (map_tree recip (map_tree succ (map_tree recip stern_brocot_recurse)))
     (map_tree succ stern_brocot_recurse)"

text \<open>Actually, we would like to write the specification below, but \<open>(\<diamondop>)\<close> cannot be registered as friendly due to varying type parameters\<close>
lemma stern_brocot_unfold:
  "stern_brocot_recurse =
   Node (1, 1)
        (pure recip \<diamondop> (pure succ \<diamondop> (pure recip \<diamondop> stern_brocot_recurse)))
        (pure succ \<diamondop> stern_brocot_recurse)"
by(fact stern_brocot_recurse.code[unfolded map_tree_ap_tree_pure_tree[symmetric]])

lemma stern_brocot_simps [simp]:
  "root stern_brocot_recurse = (1, 1)"
  "left stern_brocot_recurse = pure recip \<diamondop> (pure succ \<diamondop> (pure recip \<diamondop> stern_brocot_recurse))"
  "right stern_brocot_recurse = pure succ \<diamondop> stern_brocot_recurse"
by (subst stern_brocot_unfold, simp)+

lemma stern_brocot_conv:
  "stern_brocot_recurse = tree_recurse (recip \<circ> succ \<circ> recip) succ (1, 1)"
apply(rule tree_recurse.unique)
apply(subst stern_brocot_unfold)
apply(simp add: o_assoc)
apply(rule conjI; applicative_nf; simp)
done

subsection \<open>Basic properties\<close>

text \<open>
  The recursive definition is useful for showing some basic properties of the tree, 
  such as that the pairs of numbers at each node are coprime, and have non-zero denominators.
  Both are simple inductions on the path.
\<close>

lemma stern_brocot_denominator_non_zero:
  "case root (traverse_tree path stern_brocot_recurse) of (m, n) \<Rightarrow> m > 0 \<and> n > 0"
by(induct path)(auto split: dir.splits)

lemma stern_brocot_coprime:
  "case root (traverse_tree path stern_brocot_recurse) of (m, n) \<Rightarrow> coprime m n"
  by (induct path) (auto split: dir.splits simp add: coprime_iff_gcd_eq_1, metis gcd.commute gcd_add1)


subsection \<open>All the rationals\<close>

text\<open>
  For every pair of positive naturals, we can construct a path into the Stern-Brocot tree such that the naturals at the end of the path define the same rational as the pair we started with.
  Intuitively, the choices made by Euclid's algorithm define this path.
\<close>

function mk_path :: "nat \<Rightarrow> nat \<Rightarrow> path" where
  "m = n \<Longrightarrow> mk_path (Suc m) (Suc n) = []"
| "m < n \<Longrightarrow> mk_path (Suc m) (Suc n) = L # mk_path (Suc m) (n - m)"
| "m > n \<Longrightarrow> mk_path (Suc m) (Suc n) = R # mk_path (m - n) (Suc n)"
| "mk_path 0 _ = undefined"
| "mk_path _ 0 = undefined"
by atomize_elim(auto, arith)
termination mk_path by lexicographic_order

lemmas mk_path_induct[case_names equal less greater] = mk_path.induct

abbreviation rat_of :: "fraction \<Rightarrow> rat"
where "rat_of \<equiv> \<lambda>(x, y). Fract (int x) (int y)"

theorem stern_brocot_rationals:
  "\<lbrakk> m > 0; n > 0 \<rbrakk> \<Longrightarrow>
  root (traverse_tree (mk_path m n) (pure rat_of \<diamondop> stern_brocot_recurse)) = Fract (int m) (int n)"
proof(induction m n rule: mk_path_induct)
  case (less m n)
  with stern_brocot_denominator_non_zero[where path="mk_path (Suc m) (n - m)"]
  show ?case
    by (simp add: eq_rat field_simps of_nat_diff split: prod.split_asm)
next
  case (greater m n)
  with stern_brocot_denominator_non_zero[where path="mk_path (m - n) (Suc n)"]
  show ?case
    by (simp add: eq_rat field_simps of_nat_diff split: prod.split_asm)
qed (simp_all add: eq_rat)

subsection \<open>No repetitions\<close>

text \<open>
  We establish that the Stern-Brocot tree does not contain repetitions, i.e.,
  that each rational number appears at most once in it.
  Note that this property is stronger than merely requiring that pairs of naturals not be repeated,
  though it is implied by that property and @{thm [source] "stern_brocot_coprime"}.
  
  Intuitively, the tree enjoys the \emph{binary search tree} ordering property when we map our
  pairs of naturals into rationals. This suffices to show that each rational appears at most once
  in the tree. To establish this seems to require more structure than is present in the recursion
  equations, and so we follow \citet{BackhouseFerreira2008MPC} and \citet{Hinze2009JFP} by
  introducing another definition of the tree, which summarises the path to each node using a matrix.

  We then derive an iterative version and use invariant reasoning on that.
  We begin by defining some matrix machinery.
  This is all elementary and primitive (we do not need much algebra).
\<close>

type_synonym matrix = "fraction \<times> fraction"
type_synonym vector = fraction

definition times_matrix :: "matrix \<Rightarrow> matrix \<Rightarrow> matrix" (infixl "\<otimes>" 70)
where "times_matrix = (\<lambda>((a, c), (b, d)) ((a', c'), (b', d')).
       ((a * a' + b * c', c * a' + d * c'),
        (a * b' + b * d', c * b' + d * d')))"

definition times_vector :: "matrix \<Rightarrow> vector \<Rightarrow> vector" (infixr "\<odot>" 70)
where "times_vector = (\<lambda>((a, c), (b, d)) (a', c'). (a * a' + b * c', c * a' + d * c'))"

context begin

private definition F :: matrix where "F = ((0, 1), (1, 0))"
private definition I :: matrix where "I = ((1, 0), (0, 1))"
private definition LL :: matrix where "LL = ((1, 1), (0, 1))"
private definition UR :: matrix where "UR = ((1, 0), (1, 1))"

definition Det :: "matrix \<Rightarrow> nat" where "Det \<equiv> \<lambda>((a, c), (b, d)). a * d - b * c"

lemma Dets [iff]:
  "Det I = 1"
  "Det LL = 1"
  "Det UR = 1"
unfolding Det_def I_def LL_def UR_def by simp_all

lemma LL_UR_Det:
  "Det m = 1 \<Longrightarrow> Det (m \<otimes> LL) = 1"
  "Det m = 1 \<Longrightarrow> Det (LL \<otimes> m) = 1"
  "Det m = 1 \<Longrightarrow> Det (m \<otimes> UR) = 1"
  "Det m = 1 \<Longrightarrow> Det (UR \<otimes> m) = 1"
by (cases m, simp add: Det_def LL_def UR_def times_matrix_def split_def field_simps)+

lemma mediant_I_F [simp]:
  "mediant F = (1, 1)"
  "mediant I = (1, 1)"
by (simp_all add: F_def I_def mediant_def)

lemma times_matrix_I [simp]:
  "I \<otimes> x = x"
  "x \<otimes> I = x"
by (simp_all add: times_matrix_def I_def split_def)

lemma times_matrix_assoc [simp]:
  "(x \<otimes> y) \<otimes> z = x \<otimes> (y \<otimes> z)"
by (simp add: times_matrix_def field_simps split_def)

lemma LL_UR_pos:
  "0 < snd (mediant m) \<Longrightarrow> 0 < snd (mediant (m \<otimes> LL))"
  "0 < snd (mediant m) \<Longrightarrow> 0 < snd (mediant (m \<otimes> UR))"
by (cases m) (simp_all add: LL_def UR_def times_matrix_def split_def field_simps mediant_def)

lemma recip_succ_recip: "recip \<circ> succ \<circ> recip = (\<lambda>(x, y). (x, x + y))"
by (clarsimp simp: fun_eq_iff)

text \<open>
  \citeauthor{BackhouseFerreira2008MPC} work with the identity matrix @{const "I"} at the root.
  This has the advantage that all relevant matrices have determinants of @{term "1 :: nat"}.
\<close>

definition stern_brocot_iterate_aux :: "matrix \<Rightarrow> matrix tree"
where "stern_brocot_iterate_aux \<equiv> tree_iterate (\<lambda>s. s \<otimes> LL) (\<lambda>s. s \<otimes> UR)"

definition stern_brocot_iterate :: "fraction tree"
where "stern_brocot_iterate \<equiv> map_tree mediant (stern_brocot_iterate_aux I)"

lemma stern_brocot_recurse_iterate: "stern_brocot_recurse = stern_brocot_iterate" (is "?lhs = ?rhs")
proof -
  have "?rhs = map_tree mediant (tree_recurse ((\<otimes>) LL) ((\<otimes>) UR) I)"
    using tree_recurse_iterate[where f="(\<otimes>)" and l="LL" and r="UR" and \<epsilon>="I"]
    by (simp add: stern_brocot_iterate_def stern_brocot_iterate_aux_def)
 also have "\<dots> = tree_recurse ((\<odot>) LL) ((\<odot>) UR) (1, 1)"
   unfolding mediant_I_F(2)[symmetric]
   by (rule tree_recurse_fusion)(simp_all add: fun_eq_iff mediant_def times_matrix_def times_vector_def LL_def UR_def)[2]
 also have "\<dots> = ?lhs"
   by (simp add: stern_brocot_conv recip_succ_recip times_vector_def LL_def UR_def)
 finally show ?thesis by simp
qed

text\<open>
  The following are the key ordering properties derived by \citet{BackhouseFerreira2008MPC}.
  They hinge on the matrices containing only natural numbers.
\<close>

lemma tree_ordering_left:
  assumes DX: "Det X = 1"
  assumes DY: "Det Y = 1"
  assumes MX: "0 < snd (mediant X)"
  shows "rat_of (mediant (X \<otimes> LL \<otimes> Y)) < rat_of (mediant X)"
proof -
  from DX DY have F: "0 < snd (mediant (X \<otimes> LL \<otimes> Y))"
    by (auto simp: Det_def times_matrix_def LL_def split_def mediant_def)
  obtain x11 x12 x21 x22 where X: "X = ((x11, x12), (x21, x22))" by(cases X) auto
  obtain y11 y12 y21 y22 where Y: "Y = ((y11, y12), (y21, y22))" by(cases Y) auto
  from DX DY have *: "(x12 * x21) * (y12 + y22) < (x11 * x22) * (y12 + y22)"
    by(simp add: X Y Det_def)(cases y12, simp_all add: field_simps)
  from DX DY MX F show ?thesis
    apply (simp add: split_def X Y of_nat_mult [symmetric] del: of_nat_mult)
    apply (clarsimp simp: Det_def times_matrix_def LL_def UR_def mediant_def split_def)
    using * by (simp add: field_simps)
qed

lemma tree_ordering_right:
  assumes DX: "Det X = 1"
  assumes DY: "Det Y = 1"
  assumes MX: "0 < snd (mediant X)"
  shows "rat_of (mediant X) < rat_of (mediant (X \<otimes> UR \<otimes> Y))"
proof -
  from DX DY have F: "0 < snd (mediant (X \<otimes> UR \<otimes> Y))"
    by (auto simp: Det_def times_matrix_def UR_def split_def mediant_def)
  obtain x11 x12 x21 x22 where X: "X = ((x11, x12), (x21, x22))" by(cases X) auto
  obtain y11 y12 y21 y22 where Y: "Y = ((y11, y12), (y21, y22))" by(cases Y) auto
  show ?thesis using DX DY MX F
    apply (simp add: X Y split_def of_nat_mult [symmetric] del: of_nat_mult)
    apply (simp add: Det_def times_matrix_def LL_def UR_def mediant_def split_def algebra_simps)
    apply (simp add: add_mult_distrib2[symmetric] mult.assoc[symmetric])
    apply (cases y21; simp)
    done
qed

lemma stern_brocot_iterate_aux_Det:
  assumes "Det m = 1" "0 < snd (mediant m)"
  shows "Det (root (traverse_tree path (stern_brocot_iterate_aux m))) = 1"
  and "0 < snd (mediant (root (traverse_tree path (stern_brocot_iterate_aux m))))"
using assms
by (induct path arbitrary: m)
   (simp_all add: stern_brocot_iterate_aux_def LL_UR_Det LL_UR_pos split: dir.splits)

lemma stern_brocot_iterate_aux_decompose:
  "\<exists>m''. m \<otimes> m'' = root (traverse_tree path (stern_brocot_iterate_aux m)) \<and> Det m'' = 1"
proof(induction path arbitrary: m)
  case Nil show ?case
    by (auto simp add: stern_brocot_iterate_aux_def intro: exI[where x=I] simp del: split_paired_Ex)
next
  case (Cons d ds m)
  from Cons.IH[where m="m \<otimes> UR"] Cons.IH[where m="m \<otimes> LL"] show ?case
    by(simp add: stern_brocot_iterate_aux_def split: dir.splits del: split_paired_Ex)(fastforce simp: LL_UR_Det)
qed

lemma stern_brocot_fractions_not_repeated_strict_prefix:
  assumes "root (traverse_tree path stern_brocot_iterate) = root (traverse_tree path' stern_brocot_iterate)"
  assumes pp': "strict_prefix path path'"
  shows False
proof -
  from pp' obtain d ds where pp': "path' = path @ [d] @ ds" by (auto elim!: strict_prefixE')
  define m where "m = root (traverse_tree path (stern_brocot_iterate_aux I))"
  then have Dm: "Det m = 1" and Pm: "0 < snd (mediant m)"
    using stern_brocot_iterate_aux_Det[where path="path" and m="I"] by simp_all
  define m' where "m' = root (traverse_tree path' (stern_brocot_iterate_aux I))"
  then have Dm': "Det m' = 1"
    using stern_brocot_iterate_aux_Det[where path=path' and m="I"] by simp
  let ?M = "case d of L \<Rightarrow> m \<otimes> LL | R \<Rightarrow> m \<otimes> UR"
  from pp' have "root (traverse_tree ds (stern_brocot_iterate_aux ?M)) = m'"
    by(simp add: m_def m'_def stern_brocot_iterate_aux_def traverse_tree_tree_iterate split: dir.splits)
  then obtain m'' where mm'm'': "?M \<otimes> m''= m'" and Dm'': "Det m'' = 1"
    using stern_brocot_iterate_aux_decompose[where path="ds" and m="?M"] by clarsimp
  hence "case d of L \<Rightarrow> rat_of (mediant m') < rat_of (mediant m) | R \<Rightarrow> rat_of (mediant m) < rat_of (mediant m')"
    using tree_ordering_left[OF Dm Dm'' Pm] tree_ordering_right[OF Dm Dm'' Pm]
    by (simp split: dir.splits)
  with assms show False
    by (simp add: stern_brocot_iterate_def m_def m'_def split: dir.splits)
qed

lemma stern_brocot_fractions_not_repeated_parallel:
  assumes "root (traverse_tree path stern_brocot_iterate) = root (traverse_tree path' stern_brocot_iterate)"
  assumes p: "path = pref @ d # ds"
  assumes p': "path' = pref @ d' # ds'"
  assumes dd': "d \<noteq> d'"
  shows False
proof -
  define m where "m = root (traverse_tree pref (stern_brocot_iterate_aux I))"
  then have Dm: "Det m = 1" and Pm: "0 < snd (mediant m)"
    using stern_brocot_iterate_aux_Det[where path="pref" and m="I"] by simp_all
  define pm where "pm = root (traverse_tree path (stern_brocot_iterate_aux I))"
  then have Dpm: "Det pm = 1"
    using stern_brocot_iterate_aux_Det[where path=path and m="I"] by simp
  let ?M = "case d of L \<Rightarrow> m \<otimes> LL | R \<Rightarrow> m \<otimes> UR"
  from p
  have "root (traverse_tree ds (stern_brocot_iterate_aux ?M)) = pm"
    by(simp add: stern_brocot_iterate_aux_def m_def pm_def traverse_tree_tree_iterate split: dir.splits)
  then obtain pm'
    where pm': "?M \<otimes> pm'= pm" and Dpm': "Det pm' = 1"
    using stern_brocot_iterate_aux_decompose[where path="ds" and m="?M"] by clarsimp
  hence "case d of L \<Rightarrow> rat_of (mediant pm) < rat_of (mediant m) | R \<Rightarrow> rat_of (mediant m) < rat_of (mediant pm)"
    using tree_ordering_left[OF Dm Dpm' Pm, unfolded pm']
          tree_ordering_right[OF Dm Dpm' Pm, unfolded pm']
    by (simp split: dir.splits)
  moreover
  define p'm where "p'm = root (traverse_tree path' (stern_brocot_iterate_aux I))"
  then have Dp'm: "Det p'm = 1"
    using stern_brocot_iterate_aux_Det[where path=path' and m="I"] by simp
  let ?M' = "case d' of L \<Rightarrow> m \<otimes> LL | R \<Rightarrow> m \<otimes> UR"
  from p'
  have "root (traverse_tree ds' (stern_brocot_iterate_aux ?M')) = p'm"
    by(simp add: stern_brocot_iterate_aux_def m_def p'm_def traverse_tree_tree_iterate split: dir.splits)
  then obtain p'm'
    where p'm': "?M' \<otimes> p'm' = p'm" and Dp'm': "Det p'm' = 1"
    using stern_brocot_iterate_aux_decompose[where path="ds'" and m="?M'"] by clarsimp
  hence "case d' of L \<Rightarrow> rat_of (mediant p'm) < rat_of (mediant m) | R \<Rightarrow> rat_of (mediant m) < rat_of (mediant p'm)"
    using tree_ordering_left[OF Dm Dp'm' Pm, unfolded pm']
          tree_ordering_right[OF Dm Dp'm' Pm, unfolded pm']
    by (simp split: dir.splits)
  ultimately show False using pm' p'm' assms
    by(simp add: m_def pm_def p'm_def stern_brocot_iterate_def split: dir.splits)
qed

lemma lists_not_eq:
  assumes "xs \<noteq> ys"
  obtains
    (c1) "strict_prefix xs ys"
  | (c2) "strict_prefix ys xs"
  | (c3) ps x y xs' ys'
          where "xs = ps @ x # xs'" and "ys = ps @ y # ys'" and "x \<noteq> y"
using assms
by (cases xs ys rule: prefix_cases)
   (blast dest: parallel_decomp prefix_order.neq_le_trans)+

lemma stern_brocot_fractions_not_repeated:
  assumes "root (traverse_tree path stern_brocot_iterate) = root (traverse_tree path' stern_brocot_iterate)"
  shows "path = path'"
proof(rule ccontr)
  assume "path \<noteq> path'"
  then show False using assms
    by (cases path path' rule: lists_not_eq)
       (blast intro: stern_brocot_fractions_not_repeated_strict_prefix sym
                     stern_brocot_fractions_not_repeated_parallel)+
qed

text \<open> The function @{const Fract} is injective under certain conditions. \<close>

lemma rat_inv_eq:
  assumes "Fract a b = Fract c d"
  assumes "b > 0"
  assumes "d > 0"
  assumes "coprime a b"
  assumes "coprime c d"
  shows "a = c \<and> b = d"
proof -
  from \<open>b > 0\<close> \<open>d > 0\<close> \<open>Fract a b = Fract c d\<close>
  have *: "a * d = c * b" by (simp add: eq_rat)
  from arg_cong[where f=sgn, OF this] \<open>b > 0\<close> \<open>d > 0\<close>
  have "sgn a = sgn c" by (simp add: sgn_mult)
  with * show ?thesis
    using \<open>b > 0\<close> \<open>d > 0\<close> coprime_crossproduct_int[OF \<open>coprime a b\<close> \<open>coprime c d\<close>]
    by (simp add: abs_sgn)
qed

theorem stern_brocot_rationals_not_repeated:
  assumes "root (traverse_tree path (pure rat_of \<diamondop> stern_brocot_recurse))
         = root (traverse_tree path' (pure rat_of \<diamondop> stern_brocot_recurse))"
  shows "path = path'"
using assms
using stern_brocot_coprime[where path=path]
      stern_brocot_coprime[where path=path']
      stern_brocot_denominator_non_zero[where path=path]
      stern_brocot_denominator_non_zero[where path=path']
by(auto simp: gcd_int_def dest!: rat_inv_eq intro: stern_brocot_fractions_not_repeated simp add: stern_brocot_recurse_iterate[symmetric] split: prod.splits)


subsection \<open>Equivalence of recursive and iterative version \label{section:eq:rec:iterative}\<close>

text \<open>
  \citeauthor{Hinze2009JFP} shows that it does not matter whether we use @{const I} or
  @{const "F"} at the root provided we swap the left and right matrices too.
\<close>

definition stern_brocot_Hinze_iterate :: "fraction tree"
where "stern_brocot_Hinze_iterate = map_tree mediant (tree_iterate (\<lambda>s. s \<otimes> UR) (\<lambda>s. s \<otimes> LL) F)"

lemma mediant_times_F: "mediant \<circ> (\<lambda>s. s \<otimes> F) = mediant"
by(simp add: times_matrix_def F_def mediant_def split_def o_def add.commute)

lemma stern_brocot_iterate: "stern_brocot = stern_brocot_iterate"
proof -
  have "stern_brocot = stern_brocot_Hinze_iterate"
    unfolding stern_brocot_def stern_brocot_Hinze_iterate_def
    by(subst unfold_tree_tree_iterate)(simp add: F_def times_matrix_def mediant_def UR_def LL_def split_def)
  also have "\<dots> = map_tree mediant (map_tree (\<lambda>s. s \<otimes> F) (tree_iterate (\<lambda>s. s \<otimes> LL) (\<lambda>s. s \<otimes> UR) I))"
    unfolding stern_brocot_Hinze_iterate_def
    by(subst tree_iterate_fusion[where l'="\<lambda>s. s \<otimes> UR" and r'="\<lambda>s. s \<otimes> LL"])
      (simp_all add: fun_eq_iff times_matrix_def UR_def LL_def F_def I_def)
  also have "\<dots> = stern_brocot_iterate"
    by(simp only: tree.map_comp mediant_times_F stern_brocot_iterate_def stern_brocot_iterate_aux_def)
  finally show ?thesis .
qed

theorem stern_brocot_mediant_recurse: "stern_brocot = stern_brocot_recurse"
by(simp add: stern_brocot_recurse_iterate stern_brocot_iterate)

end

no_notation times_matrix (infixl "\<otimes>" 70)
  and times_vector (infixl "\<odot>" 70)

section \<open>Linearising the Stern-Brocot Tree\<close>

subsection \<open>Turning a tree into a stream\<close>

corec tree_chop :: "'a tree \<Rightarrow> 'a tree"
where "tree_chop t = Node (root (left t)) (right t) (tree_chop (left t))"

lemma tree_chop_sel [simp]:
  "root (tree_chop t) = root (left t)"
  "left (tree_chop t) = right t"
  "right (tree_chop t) = tree_chop (left t)"
by(subst tree_chop.code; simp; fail)+

text \<open>@{const tree_chop} is a idiom homomorphism\<close>

lemma tree_chop_pure_tree [simp]:
  "tree_chop (pure x) = pure x"
by(coinduction rule: tree.coinduct_strong) auto

lemma tree_chop_ap_tree [simp]:
  "tree_chop (f \<diamondop> x) = tree_chop f \<diamondop> tree_chop x"
by(coinduction arbitrary: f x rule: tree.coinduct_strong) auto

lemma tree_chop_plus: "tree_chop (t + t') = tree_chop t + tree_chop t'"
by(simp add: plus_tree_def)

corec stream :: "'a tree \<Rightarrow> 'a stream"
where "stream t = root t ## stream (tree_chop t)"

lemma stream_sel [simp]:
  "shd (stream t) = root t"
  "stl (stream t) = stream (tree_chop t)"
by(subst stream.code; simp; fail)+

text\<open>@{const "stream"} is an idiom homomorphism.\<close>

lemma stream_pure [simp]: "stream (pure x) = pure x"
by coinduction auto

lemma stream_ap [simp]: "stream (f \<diamondop> x) = stream f \<diamondop> stream x"
by(coinduction arbitrary: f x) auto

lemma stream_plus [simp]: "stream (t + t') = stream t + stream t'"
by(simp add: plus_stream_def plus_tree_def)

lemma stream_minus [simp]: "stream (t - t') = stream t - stream t'"
by(simp add: minus_stream_def minus_tree_def)

lemma stream_times [simp]: "stream (t * t') = stream t * stream t'"
by(simp add: times_stream_def times_tree_def)

lemma stream_mod [simp]: "stream (t mod t') = stream t mod stream t'"
by(simp add: modulo_stream_def modulo_tree_def)

lemma stream_1 [simp]: "stream 1 = 1"
by(simp add: one_tree_def one_stream_def)

lemma stream_numeral [simp]: "stream (numeral n) = numeral n"
by(induct n)(simp_all only: numeral.simps stream_plus stream_1)

subsection \<open>Split the Stern-Brocot tree into numerators and denumerators\<close>

corec num_den :: "bool \<Rightarrow> nat tree"
where
  "num_den x =
   Node 1
     (if x then num_den True else num_den True + num_den False)
     (if x then num_den True + num_den False else num_den False)"

abbreviation num where "num \<equiv> num_den True"
abbreviation den where "den \<equiv> num_den False"

lemma num_unfold: "num = Node 1 num (num + den)"
by(subst num_den.code; simp)

lemma den_unfold: "den = Node 1 (num + den) den"
by(subst num_den.code; simp)

lemma num_simps [simp]:
  "root num = 1"
  "left num = num"
  "right num = num + den"
by(subst num_unfold, simp)+

lemma den_simps [simp]:
  "root den = 1"
  "left den = num + den"
  "right den = den"
by (subst den_unfold, simp)+

lemma stern_brocot_num_den:
  "pure_tree Pair \<diamondop> num \<diamondop> den = stern_brocot_recurse"
apply(rule stern_brocot_recurse.unique)
apply(subst den_unfold)
apply(subst num_unfold)
apply(simp; intro conjI)
apply(applicative_lifting; simp)+
done

lemma den_eq_chop_num: "den = tree_chop num"
by(coinduction rule: tree.coinduct_strong) simp

lemma num_conv: "num = pure fst \<diamondop> stern_brocot_recurse"
unfolding stern_brocot_num_den[symmetric]
apply(simp add: map_tree_ap_tree_pure_tree stern_brocot_num_den[symmetric])
apply(applicative_lifting; simp)
done

lemma den_conv: "den = pure snd \<diamondop> stern_brocot_recurse"
unfolding stern_brocot_num_den[symmetric]
apply(simp add: map_tree_ap_tree_pure_tree stern_brocot_num_den[symmetric])
apply(applicative_lifting; simp)
done

corec num_mod_den :: "nat tree"
where "num_mod_den = Node 0 num num_mod_den"

lemma num_mod_den_simps [simp]:
  "root num_mod_den = 0"
  "left num_mod_den = num"
  "right num_mod_den = num_mod_den"
by(subst num_mod_den.code; simp; fail)+

text\<open>
  The arithmetic transformations need the precondition that @{const den} contains only
  positive numbers, no @{term "0 :: nat"}. \citet[p502]{Hinze2009JFP} gets a bit sloppy here; it is
  not straightforward to adapt his lifting framework \cite{Hinze2010Lifting} to conditional equations.
\<close>

lemma mod_tree_lemma1:
  fixes x :: "nat tree"
  assumes "\<forall>i\<in>set_tree y. 0 < i"
  shows "x mod (x + y) = x"
proof -
  have "rel_tree (=) (x mod (x + y)) x" by applicative_lifting(simp add: assms)
  thus ?thesis by(unfold tree.rel_eq)
qed

lemma mod_tree_lemma2:
  fixes x y :: "'a :: unique_euclidean_semiring tree"
  shows "(x + y) mod y = x mod y"
by applicative_lifting simp

lemma set_tree_pathD: "x \<in> set_tree t \<Longrightarrow> \<exists>p. x = root (traverse_tree p t)"
by(induct rule: set_tree_induct)(auto intro: exI[where x="[]"] exI[where x="L # p" for p] exI[where x="R # p" for p])

lemma den_gt_0: "0 < x" if "x \<in> set_tree den"
proof -
  from that obtain p where "x = root (traverse_tree p den)" by(blast dest: set_tree_pathD)
  with stern_brocot_denominator_non_zero[of p] show "0 < x" by(simp add: den_conv split_beta)
qed

lemma num_mod_den: "num mod den = num_mod_den"
by(rule num_mod_den.unique)(rule tree.expand, simp add: mod_tree_lemma2 mod_tree_lemma1 den_gt_0)

lemma tree_chop_den: "tree_chop den = num + den - 2 * (num mod den)"
proof -
  have le: "0 < y \<Longrightarrow> 2 * (x mod y) \<le> x + y" for x y :: nat
    by (simp add: mult_2 add_mono)

  text \<open>We switch to @{typ int} such that all cancellation laws are available.\<close>
  define den' where "den' = pure int \<diamondop> den"
  define num' where "num' = pure int \<diamondop> num"
  define num_mod_den' where "num_mod_den' = pure int \<diamondop> num_mod_den"

  have [simp]: "root num' = 1" "left num' = num'" unfolding den'_def num'_def by simp_all
  have [simp]: "right num' = num' + den'" unfolding den'_def num'_def ap_tree.sel pure_tree_simps num_simps
    by applicative_lifting simp

  have num_mod_den'_simps [simp]: "root num_mod_den' = 0" "left num_mod_den' = num'" "right num_mod_den' = num_mod_den'"
    by(simp_all add: num_mod_den'_def num'_def)
  have den'_eq_chop_num': "den' = tree_chop num'" by(simp add: den'_def num'_def den_eq_chop_num)
  have num_mod_den'2_unique: "\<And>x. x = Node 0 (2 * num') x \<Longrightarrow> x = 2 * num_mod_den'"
    by(corec_unique)(rule tree.expand; simp)
  have num'_plus_den'_minus_chop_den': "num' + den' - tree_chop den' = 2 * num_mod_den'"
    by(rule num_mod_den'2_unique)(rule tree.expand, simp add: tree_chop_plus den'_eq_chop_num')

  have "tree_chop den = pure nat \<diamondop> (tree_chop den')"
    unfolding den_conv tree_chop_ap_tree tree_chop_pure_tree den'_def by applicative_nf simp
  also have "tree_chop den' = num' + den' - tree_chop den' + tree_chop den' - 2 * num_mod_den'"
    by(subst num'_plus_den'_minus_chop_den') simp
  also have "\<dots> = num' + den' - 2 * (num' mod den')"
    unfolding num_mod_den'_def num'_def den'_def num_mod_den[symmetric]
    by applicative_lifting(simp add: zmod_int)
  also have [unfolded tree.rel_eq]: "rel_tree (=) \<dots> (pure int \<diamondop> (num + den - 2 * (num mod den)))"
    unfolding num'_def den'_def by(applicative_lifting)(simp add: of_nat_diff zmod_int le den_gt_0)
  also have "pure nat \<diamondop> (pure int \<diamondop> (num + den - 2 * (num mod den))) = num + den - 2 * (num mod den)" by(applicative_nf) simp
  finally show ?thesis .
qed

subsection\<open>Loopless linearisation of the Stern-Brocot tree.\<close>

text \<open>
  This is a loopless linearisation of the Stern-Brocot tree that gives Stern's diatomic sequence,
  which is also known as Dijkstra's fusc function \cite{Dijkstra1982EWD570,Dijkstra1982EWD578}.
  Loopless \`a la \cite{Bird2006MPC} means that the first element of the stream can be computed in linear
  time and every further element in constant time.
\<close>

friend_of_corec smap :: "('a \<Rightarrow> 'a) \<Rightarrow> 'a stream \<Rightarrow> 'a stream"
where "smap f xs = SCons (f (shd xs)) (smap f (stl xs))"
subgoal by(rule stream.expand) simp
subgoal by(fold relator_eq)(transfer_prover)
done

definition step :: "nat \<times> nat \<Rightarrow> nat \<times> nat"
where "step = (\<lambda>(n, d). (d, n + d - 2 * (n mod d)))"

corec stern_brocot_loopless :: "fraction stream"
where "stern_brocot_loopless = (1, 1) ## smap step stern_brocot_loopless"

lemmas stern_brocot_loopless_rec = stern_brocot_loopless.code

friend_of_corec plus where "s + s' = (shd s + shd s') ## (stl s + stl s')"
subgoal by (rule stream.expand; simp add: plus_stream_shd plus_stream_stl)
subgoal by transfer_prover
done

friend_of_corec minus where "t - t' = (shd t - shd t') ## (stl t - stl t')"
subgoal by (rule stream.expand; simp add: minus_stream_def)
subgoal by transfer_prover
done

friend_of_corec times where "t * t' = (shd t * shd t') ## (stl t * stl t')"
subgoal by (rule stream.expand; simp add: times_stream_def)
subgoal by transfer_prover
done

friend_of_corec modulo where "t mod t' = (shd t mod shd t') ## (stl t mod stl t')"
subgoal by (rule stream.expand; simp add: modulo_stream_def)
subgoal by transfer_prover
done

corec fusc' :: "nat stream"
where "fusc' = 1 ## (((1 ## fusc') + fusc') - 2 * ((1 ## fusc') mod fusc'))"

definition fusc where "fusc = 1 ## fusc'"

lemma fusc_unfold: "fusc = 1 ## fusc'" by(fact fusc_def)

lemma fusc'_unfold: "fusc' = 1 ## (fusc + fusc' - 2 * (fusc mod fusc'))"
by(subst fusc'.code)(simp add: fusc_def)

lemma fusc_simps [simp]:
  "shd fusc = 1"
  "stl fusc = fusc'"
by(simp_all add: fusc_unfold)

lemma fusc'_simps [simp]:
  "shd fusc' = 1"
  "stl fusc' = fusc + fusc' - 2 * (fusc mod fusc')"
by(subst fusc'_unfold, simp)+

subsection \<open>Equivalence with Dijkstra's fusc function\<close>

lemma stern_brocot_loopless_siterate: "stern_brocot_loopless = siterate step (1, 1)"
by(rule stern_brocot_loopless.unique[symmetric])(rule stream.expand; simp add: smap_siterate[symmetric])

lemma fusc_fusc'_iterate: "pure Pair \<diamondop> fusc \<diamondop> fusc' = stern_brocot_loopless"
apply(rule stern_brocot_loopless.unique)
apply(rule stream.expand; simp add: step_def)
apply(applicative_lifting; simp)
done

theorem stern_brocot_loopless:
  "stream stern_brocot_recurse = stern_brocot_loopless" (is "?lhs = ?rhs")
proof(rule stern_brocot_loopless.unique)
  have eq: "?lhs = stream (pure_tree Pair \<diamondop> num \<diamondop> den)" by (simp only: stern_brocot_num_den)
  have num: "stream num = 1 ## stream den"
    by (rule stream.expand) (simp add: den_eq_chop_num)
  have den: "stream den = 1 ## (stream num + stream den - 2 * (stream num mod stream den))"
    by (rule stream.expand)(simp add: tree_chop_den)
  show "?lhs = (1, 1) ## smap step ?lhs" unfolding eq
    by(rule stream.expand)(simp add: den_eq_chop_num[symmetric] tree_chop_den; applicative_lifting; simp add: step_def)
qed

end
