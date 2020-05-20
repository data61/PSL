(* Title:      Matrix Kleene Algebras
   Author:     Walter Guttmann
   Maintainer: Walter Guttmann <walter.guttmann at canterbury.ac.nz>
*)

section \<open>Matrix Kleene Algebras\<close>

text \<open>
This theory gives a matrix model of Stone-Kleene relation algebras.
The main result is that matrices over Kleene algebras form Kleene algebras.
The automata-based construction is due to Conway \cite{Conway1971}.
An implementation of the construction in Isabelle/HOL that extends \cite{ArmstrongGomesStruthWeber2016} was given in \cite{Asplund2014} without a correctness proof.

For specifying the size of matrices, Isabelle/HOL's type system requires the use of types, not sets.
This creates two issues when trying to implement Conway's recursive construction directly.
First, the matrix size changes for recursive calls, which requires dependent types.
Second, some submatrices used in the construction are not square, which requires typed Kleene algebras \cite{Kozen1998}, that is, categories of Kleene algebras.

Because these instruments are not available in Isabelle/HOL, we use square matrices with a constant size given by the argument of the Kleene star operation.
Smaller, possibly rectangular submatrices are identified by two lists of indices: one for the rows to include and one for the columns to include.
Lists are used to make recursive calls deterministic; otherwise sets would be sufficient.
\<close>

theory Matrix_Kleene_Algebras

imports Stone_Relation_Algebras.Matrix_Relation_Algebras Kleene_Relation_Algebras

begin

subsection \<open>Matrix Restrictions\<close>

text \<open>
In this section we develop a calculus of matrix restrictions.
The restriction of a matrix to specific row and column indices is implemented by the following function, which keeps the size of the matrix and sets all unused entries to \<open>bot\<close>.
\<close>

definition restrict_matrix :: "'a list \<Rightarrow> ('a,'b::bot) square \<Rightarrow> 'a list \<Rightarrow> ('a,'b) square" ("_ \<langle>_\<rangle> _" [90,41,90] 91)
  where "restrict_matrix as f bs = (\<lambda>(i,j) . if List.member as i \<and> List.member bs j then f (i,j) else bot)"

text \<open>
The following function captures Conway's automata-based construction of the Kleene star of a matrix.
An index \<open>k\<close> is chosen and \<open>s\<close> contains all other indices.
The matrix is split into four submatrices \<open>a\<close>, \<open>b\<close>, \<open>c\<close>, \<open>d\<close> including/not including row/column \<open>k\<close>.
Four matrices are computed containing the entries given by Conway's construction.
These four matrices are added to obtain the result.
All matrices involved in the function have the same size, but matrix restriction is used to set irrelevant entries to \<open>bot\<close>.
\<close>

primrec star_matrix' :: "'a list \<Rightarrow> ('a,'b::{star,times,bounded_semilattice_sup_bot}) square \<Rightarrow> ('a,'b) square" where
"star_matrix' Nil g = mbot" |
"star_matrix' (k#s) g = (
  let r = [k] in
  let a = r\<langle>g\<rangle>r in
  let b = r\<langle>g\<rangle>s in
  let c = s\<langle>g\<rangle>r in
  let d = s\<langle>g\<rangle>s in
  let as = r\<langle>star o a\<rangle>r in
  let ds = star_matrix' s d in
  let e = a \<oplus> b \<odot> ds \<odot> c in
  let es = r\<langle>star o e\<rangle>r in
  let f = d \<oplus> c \<odot> as \<odot> b in
  let fs = star_matrix' s f in
  es \<oplus> as \<odot> b \<odot> fs \<oplus> ds \<odot> c \<odot> es \<oplus> fs
)"

text \<open>
The Kleene star of the whole matrix is obtained by taking as indices all elements of the underlying type \<open>'a\<close>.
This is conveniently supplied by the \<open>enum\<close> class.
\<close>

fun star_matrix :: "('a::enum,'b::{star,times,bounded_semilattice_sup_bot}) square \<Rightarrow> ('a,'b) square" ("_\<^sup>\<odot>" [100] 100) where "star_matrix f = star_matrix' (enum_class.enum::'a list) f"

text \<open>
The following lemmas deconstruct matrices with non-empty restrictions.
\<close>

lemma restrict_empty_left:
  "[]\<langle>f\<rangle>ls = mbot"
  by (unfold restrict_matrix_def List.member_def bot_matrix_def) auto

lemma restrict_empty_right:
  "ks\<langle>f\<rangle>[] = mbot"
  by (unfold restrict_matrix_def List.member_def bot_matrix_def) auto

lemma restrict_nonempty_left:
  fixes f :: "('a,'b::bounded_semilattice_sup_bot) square"
  shows "(k#ks)\<langle>f\<rangle>ls = [k]\<langle>f\<rangle>ls \<oplus> ks\<langle>f\<rangle>ls"
  by (unfold restrict_matrix_def List.member_def sup_matrix_def) auto

lemma restrict_nonempty_right:
  fixes f :: "('a,'b::bounded_semilattice_sup_bot) square"
  shows "ks\<langle>f\<rangle>(l#ls) = ks\<langle>f\<rangle>[l] \<oplus> ks\<langle>f\<rangle>ls"
  by (unfold restrict_matrix_def List.member_def sup_matrix_def) auto

lemma restrict_nonempty:
  fixes f :: "('a,'b::bounded_semilattice_sup_bot) square"
  shows "(k#ks)\<langle>f\<rangle>(l#ls) = [k]\<langle>f\<rangle>[l] \<oplus> [k]\<langle>f\<rangle>ls \<oplus> ks\<langle>f\<rangle>[l] \<oplus> ks\<langle>f\<rangle>ls"
  by (unfold restrict_matrix_def List.member_def sup_matrix_def) auto

text \<open>
The following predicate captures that two index sets are disjoint.
This has consequences for composition and the unit matrix.
\<close>

abbreviation "disjoint ks ls \<equiv> \<not>(\<exists>x . List.member ks x \<and> List.member ls x)"

lemma times_disjoint:
  fixes f g :: "('a,'b::idempotent_semiring) square"
  assumes "disjoint ls ms"
    shows "ks\<langle>f\<rangle>ls \<odot> ms\<langle>g\<rangle>ns = mbot"
proof (rule ext, rule prod_cases)
  fix i j
  have "(ks\<langle>f\<rangle>ls \<odot> ms\<langle>g\<rangle>ns) (i,j) = (\<Squnion>\<^sub>k (ks\<langle>f\<rangle>ls) (i,k) * (ms\<langle>g\<rangle>ns) (k,j))"
    by (simp add: times_matrix_def)
  also have "... = (\<Squnion>\<^sub>k (if List.member ks i \<and> List.member ls k then f (i,k) else bot) * (if List.member ms k \<and> List.member ns j then g (k,j) else bot))"
    by (simp add: restrict_matrix_def)
  also have "... = (\<Squnion>\<^sub>k if List.member ms k \<and> List.member ns j then bot * g (k,j) else (if List.member ks i \<and> List.member ls k then f (i,k) else bot) * bot)"
    using assms by (auto intro: sup_monoid.sum.cong)
  also have "... = (\<Squnion>\<^sub>(k::'a) bot)"
    by (simp add: sup_monoid.sum.neutral)
  also have "... = bot"
    by (simp add: eq_iff le_funI)
  also have "... = mbot (i,j)"
    by (simp add: bot_matrix_def)
  finally show "(ks\<langle>f\<rangle>ls \<odot> ms\<langle>g\<rangle>ns) (i,j) = mbot (i,j)"
    .
qed

lemma one_disjoint:
  assumes "disjoint ks ls"
    shows "ks\<langle>(mone::('a,'b::idempotent_semiring) square)\<rangle>ls = mbot"
proof (rule ext, rule prod_cases)
  let ?o = "mone::('a,'b) square"
  fix i j
  have "(ks\<langle>?o\<rangle>ls) (i,j) = (if List.member ks i \<and> List.member ls j then if i = j then 1 else bot else bot)"
    by (simp add: restrict_matrix_def one_matrix_def)
  also have "... = bot"
    using assms by auto
  also have "... = mbot (i,j)"
    by (simp add: bot_matrix_def)
  finally show "(ks\<langle>?o\<rangle>ls) (i,j) = mbot (i,j)"
    .
qed

text \<open>
The following predicate captures that an index set is a subset of another index set.
This has consequences for repeated restrictions.
\<close>

abbreviation "is_sublist ks ls \<equiv> \<forall>x . List.member ks x \<longrightarrow> List.member ls x"

lemma restrict_sublist:
  assumes "is_sublist ls ks"
      and "is_sublist ms ns"
    shows "ls\<langle>ks\<langle>f\<rangle>ns\<rangle>ms = ls\<langle>f\<rangle>ms"
proof (rule ext, rule prod_cases)
  fix i j
  show "(ls\<langle>ks\<langle>f\<rangle>ns\<rangle>ms) (i,j) = (ls\<langle>f\<rangle>ms) (i,j)"
  proof (cases "List.member ls i \<and> List.member ms j")
    case True thus ?thesis
      by (simp add: assms restrict_matrix_def)
  next
    case False thus ?thesis
      by (unfold restrict_matrix_def) auto
  qed
qed

lemma restrict_superlist:
  assumes "is_sublist ls ks"
      and "is_sublist ms ns"
    shows "ks\<langle>ls\<langle>f\<rangle>ms\<rangle>ns = ls\<langle>f\<rangle>ms"
proof (rule ext, rule prod_cases)
  fix i j
  show "(ks\<langle>ls\<langle>f\<rangle>ms\<rangle>ns) (i,j) = (ls\<langle>f\<rangle>ms) (i,j)"
  proof (cases "List.member ls i \<and> List.member ms j")
    case True thus ?thesis
      by (simp add: assms restrict_matrix_def)
  next
    case False thus ?thesis
      by (unfold restrict_matrix_def) auto
  qed
qed

text \<open>
The following lemmas give the sizes of the results of some matrix operations.
\<close>

lemma restrict_sup:
  fixes f g :: "('a,'b::bounded_semilattice_sup_bot) square"
  shows "ks\<langle>f \<oplus> g\<rangle>ls = ks\<langle>f\<rangle>ls \<oplus> ks\<langle>g\<rangle>ls"
  by (unfold restrict_matrix_def sup_matrix_def) auto

lemma restrict_times:
  fixes f g :: "('a,'b::idempotent_semiring) square"
  shows "ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms = ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms"
proof (rule ext, rule prod_cases)
  fix i j
  have "(ks\<langle>(ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms)\<rangle>ms) (i,j) = (if List.member ks i \<and> List.member ms j then (\<Squnion>\<^sub>k (ks\<langle>f\<rangle>ls) (i,k) * (ls\<langle>g\<rangle>ms) (k,j)) else bot)"
    by (simp add: times_matrix_def restrict_matrix_def)
  also have "... = (if List.member ks i \<and> List.member ms j then (\<Squnion>\<^sub>k (if List.member ks i \<and> List.member ls k then f (i,k) else bot) * (if List.member ls k \<and> List.member ms j then g (k,j) else bot)) else bot)"
    by (simp add: restrict_matrix_def)
  also have "... = (if List.member ks i \<and> List.member ms j then (\<Squnion>\<^sub>k if List.member ls k then f (i,k) * g (k,j) else bot) else bot)"
    by (auto intro: sup_monoid.sum.cong)
  also have "... = (\<Squnion>\<^sub>k if List.member ks i \<and> List.member ms j then (if List.member ls k then f (i,k) * g (k,j) else bot) else bot)"
    by auto
  also have "... = (\<Squnion>\<^sub>k (if List.member ks i \<and> List.member ls k then f (i,k) else bot) * (if List.member ls k \<and> List.member ms j then g (k,j) else bot))"
    by (auto intro: sup_monoid.sum.cong)
  also have "... = (\<Squnion>\<^sub>k (ks\<langle>f\<rangle>ls) (i,k) * (ls\<langle>g\<rangle>ms) (k,j))"
    by (simp add: restrict_matrix_def)
  also have "... = (ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms) (i,j)"
    by (simp add: times_matrix_def)
  finally show "(ks\<langle>(ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms)\<rangle>ms) (i,j) = (ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms) (i,j)"
    .
qed

lemma restrict_star:
  fixes g :: "('a,'b::kleene_algebra) square"
  shows "t\<langle>star_matrix' t g\<rangle>t = star_matrix' t g"
proof (induct arbitrary: g rule: list.induct)
  case Nil show ?case
    by (simp add: restrict_empty_left)
next
  case (Cons k s)
  let ?t = "k#s"
  assume "\<And>g::('a,'b) square . s\<langle>star_matrix' s g\<rangle>s = star_matrix' s g"
  hence 1: "\<And>g::('a,'b) square . ?t\<langle>star_matrix' s g\<rangle>?t = star_matrix' s g"
    by (metis member_rec(1) restrict_superlist)
  show "?t\<langle>star_matrix' ?t g\<rangle>?t = star_matrix' ?t g"
  proof -
    let ?r = "[k]"
    let ?a = "?r\<langle>g\<rangle>?r"
    let ?b = "?r\<langle>g\<rangle>s"
    let ?c = "s\<langle>g\<rangle>?r"
    let ?d = "s\<langle>g\<rangle>s"
    let ?as = "?r\<langle>star o ?a\<rangle>?r"
    let ?ds = "star_matrix' s ?d"
    let ?e = "?a \<oplus> ?b \<odot> ?ds \<odot> ?c"
    let ?es = "?r\<langle>star o ?e\<rangle>?r"
    let ?f = "?d \<oplus> ?c \<odot> ?as \<odot> ?b"
    let ?fs = "star_matrix' s ?f"
    have 2: "?t\<langle>?as\<rangle>?t = ?as \<and> ?t\<langle>?b\<rangle>?t = ?b \<and> ?t\<langle>?c\<rangle>?t = ?c \<and> ?t\<langle>?es\<rangle>?t = ?es"
      by (simp add: restrict_superlist member_def)
    have 3: "?t\<langle>?ds\<rangle>?t = ?ds \<and> ?t\<langle>?fs\<rangle>?t = ?fs"
      using 1 by simp
    have 4: "?t\<langle>?t\<langle>?as\<rangle>?t \<odot> ?t\<langle>?b\<rangle>?t \<odot> ?t\<langle>?fs\<rangle>?t\<rangle>?t = ?t\<langle>?as\<rangle>?t \<odot> ?t\<langle>?b\<rangle>?t \<odot> ?t\<langle>?fs\<rangle>?t"
      by (metis (no_types) restrict_times)
    have 5: "?t\<langle>?t\<langle>?ds\<rangle>?t \<odot> ?t\<langle>?c\<rangle>?t \<odot> ?t\<langle>?es\<rangle>?t\<rangle>?t = ?t\<langle>?ds\<rangle>?t \<odot> ?t\<langle>?c\<rangle>?t \<odot> ?t\<langle>?es\<rangle>?t"
      by (metis (no_types) restrict_times)
    have "?t\<langle>star_matrix' ?t g\<rangle>?t = ?t\<langle>?es \<oplus> ?as \<odot> ?b \<odot> ?fs \<oplus> ?ds \<odot> ?c \<odot> ?es \<oplus> ?fs\<rangle>?t"
      by (metis star_matrix'.simps(2))
    also have "... = ?t\<langle>?es\<rangle>?t \<oplus> ?t\<langle>?as \<odot> ?b \<odot> ?fs\<rangle>?t \<oplus> ?t\<langle>?ds \<odot> ?c \<odot> ?es\<rangle>?t \<oplus> ?t\<langle>?fs\<rangle>?t"
      by (simp add: restrict_sup)
    also have "... = ?es \<oplus> ?as \<odot> ?b \<odot> ?fs \<oplus> ?ds \<odot> ?c \<odot> ?es \<oplus> ?fs"
      using 2 3 4 5 by simp
    also have "... = star_matrix' ?t g"
      by (metis star_matrix'.simps(2))
    finally show ?thesis
      .
  qed
qed

lemma restrict_one:
  assumes "\<not> List.member ks k"
    shows "(k#ks)\<langle>(mone::('a,'b::idempotent_semiring) square)\<rangle>(k#ks) = [k]\<langle>mone\<rangle>[k] \<oplus> ks\<langle>mone\<rangle>ks"
  by (subst restrict_nonempty) (simp add: assms member_rec one_disjoint)

lemma restrict_one_left_unit:
  "ks\<langle>(mone::('a::finite,'b::idempotent_semiring) square)\<rangle>ks \<odot> ks\<langle>f\<rangle>ls = ks\<langle>f\<rangle>ls"
proof (rule ext, rule prod_cases)
  let ?o = "mone::('a,'b::idempotent_semiring) square"
  fix i j
  have "(ks\<langle>?o\<rangle>ks \<odot> ks\<langle>f\<rangle>ls) (i,j) = (\<Squnion>\<^sub>k (ks\<langle>?o\<rangle>ks) (i,k) * (ks\<langle>f\<rangle>ls) (k,j))"
    by (simp add: times_matrix_def)
  also have "... = (\<Squnion>\<^sub>k (if List.member ks i \<and> List.member ks k then ?o (i,k) else bot) * (if List.member ks k \<and> List.member ls j then f (k,j) else bot))"
    by (simp add: restrict_matrix_def)
  also have "... = (\<Squnion>\<^sub>k (if List.member ks i \<and> List.member ks k then (if i = k then 1 else bot) else bot) * (if List.member ks k \<and> List.member ls j then f (k,j) else bot))"
    by (unfold one_matrix_def) auto
  also have "... = (\<Squnion>\<^sub>k (if i = k then (if List.member ks i then 1 else bot) else bot) * (if List.member ks k \<and> List.member ls j then f (k,j) else bot))"
    by (auto intro: sup_monoid.sum.cong)
  also have "... = (\<Squnion>\<^sub>k if i = k then (if List.member ks i then 1 else bot) * (if List.member ks i \<and> List.member ls j then f (i,j) else bot) else bot)"
    by (rule sup_monoid.sum.cong) simp_all
  also have "... = (if List.member ks i then 1 else bot) * (if List.member ks i \<and> List.member ls j then f (i,j) else bot)"
    by simp
  also have "... = (if List.member ks i \<and> List.member ls j then f (i,j) else bot)"
    by simp
  also have "... = (ks\<langle>f\<rangle>ls) (i,j)"
    by (simp add: restrict_matrix_def)
  finally show "(ks\<langle>?o\<rangle>ks \<odot> ks\<langle>f\<rangle>ls) (i,j) = (ks\<langle>f\<rangle>ls) (i,j)"
    .
qed

text \<open>
The following lemmas consider restrictions to singleton index sets.
\<close>

lemma restrict_singleton:
  "([k]\<langle>f\<rangle>[l]) (i,j) = (if i = k \<and> j = l then f (i,j) else bot)"
  by (simp add: restrict_matrix_def List.member_def)

lemma restrict_singleton_list:
  "([k]\<langle>f\<rangle>ls) (i,j) = (if i = k \<and> List.member ls j then f (i,j) else bot)"
  by (simp add: restrict_matrix_def List.member_def)

lemma restrict_list_singleton:
  "(ks\<langle>f\<rangle>[l]) (i,j) = (if List.member ks i \<and> j = l then f (i,j) else bot)"
  by (simp add: restrict_matrix_def List.member_def)

lemma restrict_singleton_product:
  fixes f g :: "('a::finite,'b::kleene_algebra) square"
  shows "([k]\<langle>f\<rangle>[l] \<odot> [m]\<langle>g\<rangle>[n]) (i,j) = (if i = k \<and> l = m \<and> j = n then f (i,l) * g (m,j) else bot)"
proof -
  have "([k]\<langle>f\<rangle>[l] \<odot> [m]\<langle>g\<rangle>[n]) (i,j) = (\<Squnion>\<^sub>h ([k]\<langle>f\<rangle>[l]) (i,h) * ([m]\<langle>g\<rangle>[n]) (h,j))"
    by (simp add: times_matrix_def)
  also have "... = (\<Squnion>\<^sub>h (if i = k \<and> h = l then f (i,h) else bot) * (if h = m \<and> j = n then g (h,j) else bot))"
    by (simp add: restrict_singleton)
  also have "... = (\<Squnion>\<^sub>h if h = l then (if i = k then f (i,h) else bot) * (if h = m \<and> j = n then g (h,j) else bot) else bot)"
    by (rule sup_monoid.sum.cong) auto
  also have "... = (if i = k then f (i,l) else bot) * (if l = m \<and> j = n then g (l,j) else bot)"
    by simp
  also have "... = (if i = k \<and> l = m \<and> j = n then f (i,l) * g (m,j) else bot)"
    by simp
  finally show ?thesis
    .
qed

text \<open>
The Kleene star unfold law holds for matrices with a single entry on the diagonal.
\<close>

lemma restrict_star_unfold:
  "[l]\<langle>(mone::('a::finite,'b::kleene_algebra) square)\<rangle>[l] \<oplus> [l]\<langle>f\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l] = [l]\<langle>star o f\<rangle>[l]"
proof (rule ext, rule prod_cases)
  let ?o = "mone::('a,'b::kleene_algebra) square"
  fix i j
  have "([l]\<langle>?o\<rangle>[l] \<oplus> [l]\<langle>f\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l]) (i,j) = ([l]\<langle>?o\<rangle>[l]) (i,j) \<squnion> ([l]\<langle>f\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l]) (i,j)"
    by (simp add: sup_matrix_def)
  also have "... = ([l]\<langle>?o\<rangle>[l]) (i,j) \<squnion> (\<Squnion>\<^sub>k ([l]\<langle>f\<rangle>[l]) (i,k) * ([l]\<langle>star o f\<rangle>[l]) (k,j))"
    by (simp add: times_matrix_def)
  also have "... = ([l]\<langle>?o\<rangle>[l]) (i,j) \<squnion> (\<Squnion>\<^sub>k (if i = l \<and> k = l then f (i,k) else bot) * (if k = l \<and> j = l then (f (k,j))\<^sup>\<star> else bot))"
    by (simp add: restrict_singleton o_def)
  also have "... = ([l]\<langle>?o\<rangle>[l]) (i,j) \<squnion> (\<Squnion>\<^sub>k if k = l then (if i = l then f (i,k) else bot) * (if j = l then (f (k,j))\<^sup>\<star> else bot) else bot)"
    apply (rule arg_cong2[where f=sup])
    apply simp
    by (rule sup_monoid.sum.cong) auto
  also have "... = ([l]\<langle>?o\<rangle>[l]) (i,j) \<squnion> (if i = l then f (i,l) else bot) * (if j = l then (f (l,j))\<^sup>\<star> else bot)"
    by simp
  also have "... = (if i = l \<and> j = l then 1 \<squnion> f (l,l) * (f (l,l))\<^sup>\<star> else bot)"
    by (simp add: restrict_singleton one_matrix_def)
  also have "... = (if i = l \<and> j = l then (f (l,l))\<^sup>\<star> else bot)"
    by (simp add: star_left_unfold_equal)
  also have "... = ([l]\<langle>star o f\<rangle>[l]) (i,j)"
    by (simp add: restrict_singleton o_def)
  finally show "([l]\<langle>?o\<rangle>[l] \<oplus> [l]\<langle>f\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l]) (i,j) = ([l]\<langle>star o f\<rangle>[l]) (i,j)"
    .
qed

lemma restrict_all:
  "enum_class.enum\<langle>f\<rangle>enum_class.enum = f"
  by (simp add: restrict_matrix_def List.member_def enum_UNIV)

text \<open>
The following shows the various components of a matrix product.
It is essentially a recursive implementation of the product.
\<close>

lemma restrict_nonempty_product:
  fixes f g :: "('a::finite,'b::idempotent_semiring) square"
  assumes "\<not> List.member ls l"
    shows "(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms) = ([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> ([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms)"
proof -
  have "(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms) = ([k]\<langle>f\<rangle>[l] \<oplus> [k]\<langle>f\<rangle>ls \<oplus> ks\<langle>f\<rangle>[l] \<oplus> ks\<langle>f\<rangle>ls) \<odot> ([l]\<langle>g\<rangle>[m] \<oplus> [l]\<langle>g\<rangle>ms \<oplus> ls\<langle>g\<rangle>[m] \<oplus> ls\<langle>g\<rangle>ms)"
    by (metis restrict_nonempty)
  also have "... = [k]\<langle>f\<rangle>[l] \<odot> ([l]\<langle>g\<rangle>[m] \<oplus> [l]\<langle>g\<rangle>ms \<oplus> ls\<langle>g\<rangle>[m] \<oplus> ls\<langle>g\<rangle>ms) \<oplus> [k]\<langle>f\<rangle>ls \<odot> ([l]\<langle>g\<rangle>[m] \<oplus> [l]\<langle>g\<rangle>ms \<oplus> ls\<langle>g\<rangle>[m] \<oplus> ls\<langle>g\<rangle>ms) \<oplus> ks\<langle>f\<rangle>[l] \<odot> ([l]\<langle>g\<rangle>[m] \<oplus> [l]\<langle>g\<rangle>ms \<oplus> ls\<langle>g\<rangle>[m] \<oplus> ls\<langle>g\<rangle>ms) \<oplus> ks\<langle>f\<rangle>ls \<odot> ([l]\<langle>g\<rangle>[m] \<oplus> [l]\<langle>g\<rangle>ms \<oplus> ls\<langle>g\<rangle>[m] \<oplus> ls\<langle>g\<rangle>ms)"
    by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
  also have "... = ([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>[l] \<odot> ls\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>[l] \<odot> ls\<langle>g\<rangle>ms) \<oplus> ([k]\<langle>f\<rangle>ls \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>[l] \<odot> ls\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>[l] \<odot> ls\<langle>g\<rangle>ms) \<oplus> (ks\<langle>f\<rangle>ls \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms)"
    by (simp add: matrix_idempotent_semiring.mult_left_dist_sup)
  also have "... = ([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms) \<oplus> ([k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms) \<oplus> (ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms)"
    using assms by (simp add: List.member_def times_disjoint)
  also have "... = ([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> ([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms)"
    by (simp add: matrix_bounded_semilattice_sup_bot.sup_monoid.add_assoc matrix_semilattice_sup.sup_left_commute)
  finally show ?thesis
    .
qed

text \<open>
Equality of matrices is componentwise.
\<close>

lemma restrict_nonempty_eq:
  "(k#ks)\<langle>f\<rangle>(l#ls) = (k#ks)\<langle>g\<rangle>(l#ls) \<longleftrightarrow> [k]\<langle>f\<rangle>[l] = [k]\<langle>g\<rangle>[l] \<and> [k]\<langle>f\<rangle>ls = [k]\<langle>g\<rangle>ls \<and> ks\<langle>f\<rangle>[l] = ks\<langle>g\<rangle>[l] \<and> ks\<langle>f\<rangle>ls = ks\<langle>g\<rangle>ls"
proof
  assume 1: "(k#ks)\<langle>f\<rangle>(l#ls) = (k#ks)\<langle>g\<rangle>(l#ls)"
  have 2: "is_sublist [k] (k#ks) \<and> is_sublist ks (k#ks) \<and> is_sublist [l] (l#ls) \<and> is_sublist ls (l#ls)"
    by (simp add: member_rec)
  hence "[k]\<langle>f\<rangle>[l] = [k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls)\<rangle>[l] \<and> [k]\<langle>f\<rangle>ls = [k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls)\<rangle>ls \<and> ks\<langle>f\<rangle>[l] = ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls)\<rangle>[l] \<and> ks\<langle>f\<rangle>ls = ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls)\<rangle>ls"
    by (simp add: restrict_sublist)
  thus "[k]\<langle>f\<rangle>[l] = [k]\<langle>g\<rangle>[l] \<and> [k]\<langle>f\<rangle>ls = [k]\<langle>g\<rangle>ls \<and> ks\<langle>f\<rangle>[l] = ks\<langle>g\<rangle>[l] \<and> ks\<langle>f\<rangle>ls = ks\<langle>g\<rangle>ls"
    using 1 2 by (simp add: restrict_sublist)
next
  assume 3: "[k]\<langle>f\<rangle>[l] = [k]\<langle>g\<rangle>[l] \<and> [k]\<langle>f\<rangle>ls = [k]\<langle>g\<rangle>ls \<and> ks\<langle>f\<rangle>[l] = ks\<langle>g\<rangle>[l] \<and> ks\<langle>f\<rangle>ls = ks\<langle>g\<rangle>ls"
  show "(k#ks)\<langle>f\<rangle>(l#ls) = (k#ks)\<langle>g\<rangle>(l#ls)"
  proof (rule ext, rule prod_cases)
    fix i j
    have 4: "f (k,l) = g (k,l)"
      using 3 by (metis restrict_singleton)
    have 5: "List.member ls j \<Longrightarrow> f (k,j) = g (k,j)"
      using 3 by (metis restrict_singleton_list)
    have 6: "List.member ks i \<Longrightarrow> f (i,l) = g (i,l)"
      using 3 by (metis restrict_list_singleton)
    have "(ks\<langle>f\<rangle>ls) (i,j) = (ks\<langle>g\<rangle>ls) (i,j)"
      using 3 by simp
    hence 7: "List.member ks i \<Longrightarrow> List.member ls j \<Longrightarrow> f (i,j) = g (i,j)"
      by (simp add: restrict_matrix_def)
    have "((k#ks)\<langle>f\<rangle>(l#ls)) (i,j) = (if (i = k \<or> List.member ks i) \<and> (j = l \<or> List.member ls j) then f (i,j) else bot)"
      by (simp add: restrict_matrix_def List.member_def)
    also have "... = (if i = k \<and> j = l then f (i,j) else if i = k \<and> List.member ls j then f (i,j) else if List.member ks i \<and> j = l then f (i,j) else if List.member ks i \<and> List.member ls j then f (i,j) else bot)"
      by auto
    also have "... = (if i = k \<and> j = l then g (i,j) else if i = k \<and> List.member ls j then g (i,j) else if List.member ks i \<and> j = l then g (i,j) else if List.member ks i \<and> List.member ls j then g (i,j) else bot)"
      using 4 5 6 7 by simp
    also have "... = (if (i = k \<or> List.member ks i) \<and> (j = l \<or> List.member ls j) then g (i,j) else bot)"
      by auto
    also have "... = ((k#ks)\<langle>g\<rangle>(l#ls)) (i,j)"
      by (simp add: restrict_matrix_def List.member_def)
    finally show "((k#ks)\<langle>f\<rangle>(l#ls)) (i,j) = ((k#ks)\<langle>g\<rangle>(l#ls)) (i,j)"
      .
  qed
qed

text \<open>
Inequality of matrices is componentwise.
\<close>

lemma restrict_nonempty_less_eq:
  fixes f g :: "('a,'b::idempotent_semiring) square"
  shows "(k#ks)\<langle>f\<rangle>(l#ls) \<preceq> (k#ks)\<langle>g\<rangle>(l#ls) \<longleftrightarrow> [k]\<langle>f\<rangle>[l] \<preceq> [k]\<langle>g\<rangle>[l] \<and> [k]\<langle>f\<rangle>ls \<preceq> [k]\<langle>g\<rangle>ls \<and> ks\<langle>f\<rangle>[l] \<preceq> ks\<langle>g\<rangle>[l] \<and> ks\<langle>f\<rangle>ls \<preceq> ks\<langle>g\<rangle>ls"
  by (unfold matrix_semilattice_sup.sup.order_iff) (metis (no_types, lifting) restrict_nonempty_eq restrict_sup)

text \<open>
The following lemmas treat repeated restrictions to disjoint index sets.
\<close>

lemma restrict_disjoint_left:
  assumes "disjoint ks ms"
    shows "ms\<langle>ks\<langle>f\<rangle>ls\<rangle>ns = mbot"
proof (rule ext, rule prod_cases)
  fix i j
  have "(ms\<langle>ks\<langle>f\<rangle>ls\<rangle>ns) (i,j) = (if List.member ms i \<and> List.member ns j then if List.member ks i \<and> List.member ls j then f (i,j) else bot else bot)"
    by (simp add: restrict_matrix_def)
  thus "(ms\<langle>ks\<langle>f\<rangle>ls\<rangle>ns) (i,j) = mbot (i,j)"
    using assms by (simp add: bot_matrix_def)
qed

lemma restrict_disjoint_right:
  assumes "disjoint ls ns"
    shows "ms\<langle>ks\<langle>f\<rangle>ls\<rangle>ns = mbot"
proof (rule ext, rule prod_cases)
  fix i j
  have "(ms\<langle>ks\<langle>f\<rangle>ls\<rangle>ns) (i,j) = (if List.member ms i \<and> List.member ns j then if List.member ks i \<and> List.member ls j then f (i,j) else bot else bot)"
    by (simp add: restrict_matrix_def)
  thus "(ms\<langle>ks\<langle>f\<rangle>ls\<rangle>ns) (i,j) = mbot (i,j)"
    using assms by (simp add: bot_matrix_def)
qed

text \<open>
The following lemma expresses the equality of a matrix and a product of two matrices componentwise.
\<close>

lemma restrict_nonempty_product_eq:
  fixes f g h :: "('a::finite,'b::idempotent_semiring) square"
  assumes "\<not> List.member ks k"
      and "\<not> List.member ls l"
      and "\<not> List.member ms m"
    shows "(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms) = (k#ks)\<langle>h\<rangle>(m#ms) \<longleftrightarrow> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] = [k]\<langle>h\<rangle>[m] \<and> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms = [k]\<langle>h\<rangle>ms \<and> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] = ks\<langle>h\<rangle>[m] \<and> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms = ks\<langle>h\<rangle>ms"
proof -
  have 1: "disjoint [k] ks \<and> disjoint [m] ms"
    by (simp add: assms(1,3) member_rec)
  have 2: "[k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>[m] = [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]"
  proof -
    have "[k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>[m] = [k]\<langle>([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> ([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms)\<rangle>[m]"
      by (simp add: assms(2) restrict_nonempty_product)
    also have "... = [k]\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>[m] \<oplus> [k]\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>[m] \<oplus> [k]\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>[m] \<oplus> [k]\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>[m] \<oplus> [k]\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>[m] \<oplus> [k]\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>[m] \<oplus> [k]\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>[m] \<oplus> [k]\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>[m]"
      by (simp add: matrix_bounded_semilattice_sup_bot.sup_monoid.add_assoc restrict_sup)
    also have "... = [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] \<oplus> [k]\<langle>[k]\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>ms\<rangle>[m] \<oplus> [k]\<langle>[k]\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms\<rangle>[m] \<oplus> [k]\<langle>ks\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>[m] \<oplus> [k]\<langle>ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>[m] \<oplus> [k]\<langle>ks\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>ms\<rangle>[m] \<oplus> [k]\<langle>ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms\<rangle>[m]"
      by (simp add: restrict_times)
    also have "... = [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]"
      using 1 by (metis restrict_disjoint_left restrict_disjoint_right matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_right)
    finally show ?thesis
      .
  qed
  have 3: "[k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>ms = [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms"
  proof -
    have "[k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>ms = [k]\<langle>([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> ([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms)\<rangle>ms"
      by (simp add: assms(2) restrict_nonempty_product)
    also have "... = [k]\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>ms \<oplus> [k]\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>ms \<oplus> [k]\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>ms \<oplus> [k]\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms \<oplus> [k]\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>ms \<oplus> [k]\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>ms \<oplus> [k]\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>ms \<oplus> [k]\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms"
      by (simp add: matrix_bounded_semilattice_sup_bot.sup_monoid.add_assoc restrict_sup)
    also have "... = [k]\<langle>[k]\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>ms \<oplus> [k]\<langle>[k]\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>ms \<oplus> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms \<oplus> [k]\<langle>ks\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>ms \<oplus> [k]\<langle>ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>ms \<oplus> [k]\<langle>ks\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>ms\<rangle>ms \<oplus> [k]\<langle>ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms\<rangle>ms"
      by (simp add: restrict_times)
    also have "... = [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms"
      using 1 by (metis restrict_disjoint_left restrict_disjoint_right matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_right matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_left)
    finally show ?thesis
      .
  qed
  have 4: "ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>[m] = ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]"
  proof -
    have "ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>[m] = ks\<langle>([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> ([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms)\<rangle>[m]"
      by (simp add: assms(2) restrict_nonempty_product)
    also have "... = ks\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>[m] \<oplus> ks\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>[m] \<oplus> ks\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>[m] \<oplus> ks\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>[m] \<oplus> ks\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>[m] \<oplus> ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>[m] \<oplus> ks\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>[m] \<oplus> ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>[m]"
      by (simp add: matrix_bounded_semilattice_sup_bot.sup_monoid.add_assoc restrict_sup)
    also have "... = ks\<langle>[k]\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>[m] \<oplus> ks\<langle>[k]\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>[m] \<oplus> ks\<langle>[k]\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>ms\<rangle>[m] \<oplus> ks\<langle>[k]\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms\<rangle>[m] \<oplus> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] \<oplus> ks\<langle>ks\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>ms\<rangle>[m] \<oplus> ks\<langle>ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms\<rangle>[m]"
      by (simp add: restrict_times)
    also have "... = ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]"
      using 1 by (metis restrict_disjoint_left restrict_disjoint_right matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_right matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_left)
    finally show ?thesis
      .
  qed
  have 5: "ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>ms = ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms"
  proof -
    have "ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>ms = ks\<langle>([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> ([k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]) \<oplus> (ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms)\<rangle>ms"
      by (simp add: assms(2) restrict_nonempty_product)
    also have "... = ks\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>ms \<oplus> ks\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>ms \<oplus> ks\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>ms \<oplus> ks\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms \<oplus> ks\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>ms \<oplus> ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>ms \<oplus> ks\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>ms \<oplus> ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms"
      by (simp add: matrix_bounded_semilattice_sup_bot.sup_monoid.add_assoc restrict_sup)
    also have "... = ks\<langle>[k]\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>ms \<oplus> ks\<langle>[k]\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>ms \<oplus> ks\<langle>[k]\<langle>[k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms\<rangle>ms\<rangle>ms \<oplus> ks\<langle>[k]\<langle>[k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms\<rangle>ms\<rangle>ms \<oplus> ks\<langle>ks\<langle>ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>ms \<oplus> ks\<langle>ks\<langle>ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]\<rangle>[m]\<rangle>ms \<oplus> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms"
      by (simp add: restrict_times)
    also have "... = ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms"
      using 1 by (metis restrict_disjoint_left restrict_disjoint_right matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_left)
    finally show ?thesis
      .
  qed
  have "(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms) = (k#ks)\<langle>h\<rangle>(m#ms) \<longleftrightarrow> (k#ks)\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>(m#ms) = (k#ks)\<langle>h\<rangle>(m#ms)"
    by (simp add: restrict_times)
  also have "... \<longleftrightarrow> [k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>[m] = [k]\<langle>h\<rangle>[m] \<and> [k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>ms = [k]\<langle>h\<rangle>ms \<and> ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>[m] = ks\<langle>h\<rangle>[m] \<and> ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>ms = ks\<langle>h\<rangle>ms"
    by (meson restrict_nonempty_eq)
  also have "... \<longleftrightarrow> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] = [k]\<langle>h\<rangle>[m] \<and> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms = [k]\<langle>h\<rangle>ms \<and> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] = ks\<langle>h\<rangle>[m] \<and> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms = ks\<langle>h\<rangle>ms"
    using 2 3 4 5 by simp
  finally show ?thesis
    by simp
qed

text \<open>
The following lemma gives a componentwise characterisation of the inequality of a matrix and a product of two matrices.
\<close>

lemma restrict_nonempty_product_less_eq:
  fixes f g h :: "('a::finite,'b::idempotent_semiring) square"
  assumes "\<not> List.member ks k"
      and "\<not> List.member ls l"
      and "\<not> List.member ms m"
    shows "(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms) \<preceq> (k#ks)\<langle>h\<rangle>(m#ms) \<longleftrightarrow> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] \<preceq> [k]\<langle>h\<rangle>[m] \<and> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms \<preceq> [k]\<langle>h\<rangle>ms \<and> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] \<preceq> ks\<langle>h\<rangle>[m] \<and> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms \<preceq> ks\<langle>h\<rangle>ms"
proof -
  have 1: "[k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>[m] = [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]"
    by (metis assms restrict_nonempty_product_eq restrict_times)
  have 2: "[k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>ms = [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms"
    by (metis assms restrict_nonempty_product_eq restrict_times)
  have 3: "ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>[m] = ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m]"
    by (metis assms restrict_nonempty_product_eq restrict_times)
  have 4: "ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>ms = ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms"
    by (metis assms restrict_nonempty_product_eq restrict_times)
  have "(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms) \<preceq> (k#ks)\<langle>h\<rangle>(m#ms) \<longleftrightarrow> (k#ks)\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>(m#ms) \<preceq> (k#ks)\<langle>h\<rangle>(m#ms)"
    by (simp add: restrict_times)
  also have "... \<longleftrightarrow> [k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>[m] \<preceq> [k]\<langle>h\<rangle>[m] \<and> [k]\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>ms \<preceq> [k]\<langle>h\<rangle>ms \<and> ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>[m] \<preceq> ks\<langle>h\<rangle>[m] \<and> ks\<langle>(k#ks)\<langle>f\<rangle>(l#ls) \<odot> (l#ls)\<langle>g\<rangle>(m#ms)\<rangle>ms \<preceq> ks\<langle>h\<rangle>ms"
    by (meson restrict_nonempty_less_eq)
  also have "... \<longleftrightarrow> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] \<preceq> [k]\<langle>h\<rangle>[m] \<and> [k]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> [k]\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms \<preceq> [k]\<langle>h\<rangle>ms \<and> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>[m] \<preceq> ks\<langle>h\<rangle>[m] \<and> ks\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<oplus> ks\<langle>f\<rangle>ls \<odot> ls\<langle>g\<rangle>ms \<preceq> ks\<langle>h\<rangle>ms"
    using 1 2 3 4 by simp
  finally show ?thesis
    by simp
qed

text \<open>
The Kleene star induction laws hold for matrices with a single entry on the diagonal.
The matrix \<open>g\<close> can actually contain a whole row/colum at the appropriate index.
\<close>

lemma restrict_star_left_induct:
  fixes f g :: "('a::finite,'b::kleene_algebra) square"
  shows "distinct ms \<Longrightarrow> [l]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<preceq> [l]\<langle>g\<rangle>ms \<Longrightarrow> [l]\<langle>star o f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<preceq> [l]\<langle>g\<rangle>ms"
proof (induct ms)
  case Nil thus ?case
    by (simp add: restrict_empty_right)
next
  case (Cons m ms)
  assume 1: "distinct ms \<Longrightarrow> [l]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<preceq> [l]\<langle>g\<rangle>ms \<Longrightarrow> [l]\<langle>star o f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<preceq> [l]\<langle>g\<rangle>ms"
  assume 2: "distinct (m#ms)"
  assume 3: "[l]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>(m#ms) \<preceq> [l]\<langle>g\<rangle>(m#ms)"
  have 4: "[l]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<preceq> [l]\<langle>g\<rangle>[m] \<and> [l]\<langle>f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<preceq> [l]\<langle>g\<rangle>ms"
    using 2 3 by (metis distinct.simps(2) matrix_semilattice_sup.sup.bounded_iff member_def member_rec(2) restrict_nonempty_product_less_eq)
  hence 5: "[l]\<langle>star o f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>ms \<preceq> [l]\<langle>g\<rangle>ms"
    using 1 2 by simp
  have "f (l,l) * g (l,m) \<le> g (l,m)"
    using 4 by (metis restrict_singleton_product restrict_singleton less_eq_matrix_def)
  hence 6: "(f (l,l))\<^sup>\<star> * g (l,m) \<le> g (l,m)"
    by (simp add: star_left_induct_mult)
  have "[l]\<langle>star o f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m] \<preceq> [l]\<langle>g\<rangle>[m]"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j
    have "([l]\<langle>star o f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]) (i,j) = (\<Squnion>\<^sub>k ([l]\<langle>star o f\<rangle>[l]) (i,k) * ([l]\<langle>g\<rangle>[m]) (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k (if i = l \<and> k = l then (f (i,k))\<^sup>\<star> else bot) * (if k = l \<and> j = m then g (k,j) else bot))"
      by (simp add: restrict_singleton o_def)
    also have "... = (\<Squnion>\<^sub>k if k = l then (if i = l then (f (i,k))\<^sup>\<star> else bot) * (if j = m then g (k,j) else bot) else bot)"
      by (rule sup_monoid.sum.cong) auto
    also have "... = (if i = l then (f (i,l))\<^sup>\<star> else bot) * (if j = m then g (l,j) else bot)"
      by simp
    also have "... = (if i = l \<and> j = m then (f (l,l))\<^sup>\<star> * g (l,m) else bot)"
      by simp
    also have "... \<le> ([l]\<langle>g\<rangle>[m]) (i,j)"
      using 6 by (simp add: restrict_singleton)
    finally show "([l]\<langle>star o f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>[m]) (i,j) \<le> ([l]\<langle>g\<rangle>[m]) (i,j)"
      .
  qed
  thus "[l]\<langle>star o f\<rangle>[l] \<odot> [l]\<langle>g\<rangle>(m#ms) \<preceq> [l]\<langle>g\<rangle>(m#ms)"
    using 2 5 by (metis (no_types, hide_lams) matrix_idempotent_semiring.mult_left_dist_sup matrix_semilattice_sup.sup.mono restrict_nonempty_right)
qed

lemma restrict_star_right_induct:
  fixes f g :: "('a::finite,'b::kleene_algebra) square"
  shows "distinct ms \<Longrightarrow> ms\<langle>g\<rangle>[l] \<odot> [l]\<langle>f\<rangle>[l] \<preceq> ms\<langle>g\<rangle>[l] \<Longrightarrow> ms\<langle>g\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l] \<preceq> ms\<langle>g\<rangle>[l]"
proof (induct ms)
  case Nil thus ?case
    by (simp add: restrict_empty_left)
next
  case (Cons m ms)
  assume 1: "distinct ms \<Longrightarrow> ms\<langle>g\<rangle>[l] \<odot> [l]\<langle>f\<rangle>[l] \<preceq> ms\<langle>g\<rangle>[l] \<Longrightarrow> ms\<langle>g\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l] \<preceq> ms\<langle>g\<rangle>[l]"
  assume 2: "distinct (m#ms)"
  assume 3: "(m#ms)\<langle>g\<rangle>[l] \<odot> [l]\<langle>f\<rangle>[l] \<preceq> (m#ms)\<langle>g\<rangle>[l]"
  have 4: "[m]\<langle>g\<rangle>[l] \<odot> [l]\<langle>f\<rangle>[l] \<preceq> [m]\<langle>g\<rangle>[l] \<and> ms\<langle>g\<rangle>[l] \<odot> [l]\<langle>f\<rangle>[l] \<preceq> ms\<langle>g\<rangle>[l]"
    using 2 3 by (metis distinct.simps(2) matrix_semilattice_sup.sup.bounded_iff member_def member_rec(2) restrict_nonempty_product_less_eq)
  hence 5: "ms\<langle>g\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l] \<preceq> ms\<langle>g\<rangle>[l]"
    using 1 2  by simp
  have "g (m,l) * f (l,l) \<le> g (m,l)"
    using 4 by (metis restrict_singleton_product restrict_singleton less_eq_matrix_def)
  hence 6: "g (m,l) * (f (l,l))\<^sup>\<star> \<le> g (m,l)"
    by (simp add: star_right_induct_mult)
  have "[m]\<langle>g\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l] \<preceq> [m]\<langle>g\<rangle>[l]"
  proof (unfold less_eq_matrix_def, rule allI, rule prod_cases)
    fix i j
    have "([m]\<langle>g\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l]) (i,j) = (\<Squnion>\<^sub>k ([m]\<langle>g\<rangle>[l]) (i,k) * ([l]\<langle>star o f\<rangle>[l]) (k,j))"
      by (simp add: times_matrix_def)
    also have "... = (\<Squnion>\<^sub>k (if i = m \<and> k = l then g (i,k) else bot) * (if k = l \<and> j = l then (f (k,j))\<^sup>\<star> else bot))"
      by (simp add: restrict_singleton o_def)
    also have "... = (\<Squnion>\<^sub>k if k = l then (if i = m then g (i,k) else bot) * (if j = l then (f (k,j))\<^sup>\<star> else bot) else bot)"
      by (rule sup_monoid.sum.cong) auto
    also have "... = (if i = m then g (i,l) else bot) * (if j = l then (f (l,j))\<^sup>\<star> else bot)"
      by simp
    also have "... = (if i = m \<and> j = l then g (m,l) * (f (l,l))\<^sup>\<star> else bot)"
      by simp
    also have "... \<le> ([m]\<langle>g\<rangle>[l]) (i,j)"
      using 6 by (simp add: restrict_singleton)
    finally show "([m]\<langle>g\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l]) (i,j) \<le> ([m]\<langle>g\<rangle>[l]) (i,j)"
      .
  qed
  thus "(m#ms)\<langle>g\<rangle>[l] \<odot> [l]\<langle>star o f\<rangle>[l] \<preceq> (m#ms)\<langle>g\<rangle>[l]"
    using 2 5 by (metis (no_types, hide_lams) matrix_idempotent_semiring.mult_right_dist_sup matrix_semilattice_sup.sup.mono restrict_nonempty_left)
qed

lemma restrict_pp:
  fixes f :: "('a,'b::p_algebra) square"
  shows "ks\<langle>\<ominus>\<ominus>f\<rangle>ls = \<ominus>\<ominus>(ks\<langle>f\<rangle>ls)"
  by (unfold restrict_matrix_def uminus_matrix_def) auto

lemma pp_star_commute:
  fixes f :: "('a,'b::stone_kleene_relation_algebra) square"
  shows "\<ominus>\<ominus>(star o f) = star o \<ominus>\<ominus>f"
  by (simp add: uminus_matrix_def o_def pp_dist_star)

subsection \<open>Matrices form a Kleene Algebra\<close>

text \<open>
Matrices over Kleene algebras form a Kleene algebra using Conway's construction.
It remains to prove one unfold and two induction axioms of the Kleene star.
Each proof is by induction over the size of the matrix represented by an index list.
\<close>

interpretation matrix_kleene_algebra: kleene_algebra_var where sup = sup_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix::('a::enum,'b::kleene_algebra) square" and one = one_matrix and times = times_matrix and star = star_matrix
proof
  fix y :: "('a,'b) square"
  let ?e = "enum_class.enum::'a list"
  let ?o = "mone :: ('a,'b) square"
  have "\<forall>g :: ('a,'b) square . distinct ?e \<longrightarrow> (?e\<langle>?o\<rangle>?e \<oplus> ?e\<langle>g\<rangle>?e \<odot> star_matrix' ?e g) = (star_matrix' ?e g)"
  proof (induct rule: list.induct)
    case Nil thus ?case
      by (simp add: restrict_empty_left)
  next
    case (Cons k s)
    let ?t = "k#s"
    assume 1: "\<forall>g :: ('a,'b) square . distinct s \<longrightarrow> (s\<langle>?o\<rangle>s \<oplus> s\<langle>g\<rangle>s \<odot> star_matrix' s g) = (star_matrix' s g)"
    show "\<forall>g :: ('a,'b) square . distinct ?t \<longrightarrow> (?t\<langle>?o\<rangle>?t \<oplus> ?t\<langle>g\<rangle>?t \<odot> star_matrix' ?t g) = (star_matrix' ?t g)"
    proof (rule allI, rule impI)
      fix g :: "('a,'b) square"
      assume 2: "distinct ?t"
      let ?r = "[k]"
      let ?a = "?r\<langle>g\<rangle>?r"
      let ?b = "?r\<langle>g\<rangle>s"
      let ?c = "s\<langle>g\<rangle>?r"
      let ?d = "s\<langle>g\<rangle>s"
      let ?as = "?r\<langle>star o ?a\<rangle>?r"
      let ?ds = "star_matrix' s ?d"
      let ?e = "?a \<oplus> ?b \<odot> ?ds \<odot> ?c"
      let ?es = "?r\<langle>star o ?e\<rangle>?r"
      let ?f = "?d \<oplus> ?c \<odot> ?as \<odot> ?b"
      let ?fs = "star_matrix' s ?f"
      have "s\<langle>?ds\<rangle>s = ?ds \<and> s\<langle>?fs\<rangle>s = ?fs"
        by (simp add: restrict_star)
      hence 3: "?r\<langle>?e\<rangle>?r = ?e \<and> s\<langle>?f\<rangle>s = ?f"
        by (metis (no_types, lifting) restrict_one_left_unit restrict_sup restrict_times)
      have 4: "disjoint s ?r \<and> disjoint ?r s"
        using 2 by (simp add: in_set_member member_rec)
      hence 5: "?t\<langle>?o\<rangle>?t = ?r\<langle>?o\<rangle>?r \<oplus> s\<langle>?o\<rangle>s"
        by (meson member_rec(1) restrict_one)
      have 6: "?t\<langle>g\<rangle>?t \<odot> ?es = ?a \<odot> ?es \<oplus> ?c \<odot> ?es"
      proof -
        have "?t\<langle>g\<rangle>?t \<odot> ?es = (?a \<oplus> ?b \<oplus> ?c \<oplus> ?d) \<odot> ?es"
          by (metis restrict_nonempty)
        also have "... = ?a \<odot> ?es \<oplus> ?b \<odot> ?es \<oplus> ?c \<odot> ?es \<oplus> ?d \<odot> ?es"
          by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
        also have "... = ?a \<odot> ?es \<oplus> ?c \<odot> ?es"
          using 4 by (simp add: times_disjoint)
        finally show ?thesis
          .
      qed
      have 7: "?t\<langle>g\<rangle>?t \<odot> ?as \<odot> ?b \<odot> ?fs = ?a \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?c \<odot> ?as \<odot> ?b \<odot> ?fs"
      proof -
        have "?t\<langle>g\<rangle>?t \<odot> ?as \<odot> ?b \<odot> ?fs = (?a \<oplus> ?b \<oplus> ?c \<oplus> ?d) \<odot> ?as \<odot> ?b \<odot> ?fs"
          by (metis restrict_nonempty)
        also have "... = ?a \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?b \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?c \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?d \<odot> ?as \<odot> ?b \<odot> ?fs"
          by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
        also have "... = ?a \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?c \<odot> ?as \<odot> ?b \<odot> ?fs"
          using 4 by (simp add: times_disjoint)
        finally show ?thesis
          .
      qed
      have 8: "?t\<langle>g\<rangle>?t \<odot> ?ds \<odot> ?c \<odot> ?es = ?b \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?d \<odot> ?ds \<odot> ?c \<odot> ?es"
      proof -
        have "?t\<langle>g\<rangle>?t \<odot> ?ds \<odot> ?c \<odot> ?es = (?a \<oplus> ?b \<oplus> ?c \<oplus> ?d) \<odot> ?ds \<odot> ?c \<odot> ?es"
          by (metis restrict_nonempty)
        also have "... = ?a \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?b \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?c \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?d \<odot> ?ds \<odot> ?c \<odot> ?es"
          by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
        also have "... = ?b \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?d \<odot> ?ds \<odot> ?c \<odot> ?es"
          using 4 by (metis (no_types, lifting) times_disjoint matrix_idempotent_semiring.mult_left_zero restrict_star matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_right matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_left)
        finally show ?thesis
          .
      qed
      have 9: "?t\<langle>g\<rangle>?t \<odot> ?fs = ?b \<odot> ?fs \<oplus> ?d \<odot> ?fs"
      proof -
        have "?t\<langle>g\<rangle>?t \<odot> ?fs = (?a \<oplus> ?b \<oplus> ?c \<oplus> ?d) \<odot> ?fs"
          by (metis restrict_nonempty)
        also have "... = ?a \<odot> ?fs \<oplus> ?b \<odot> ?fs \<oplus> ?c \<odot> ?fs \<oplus> ?d \<odot> ?fs"
          by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
        also have "... = ?b \<odot> ?fs \<oplus> ?d \<odot> ?fs"
          using 4 by (metis (no_types, lifting) times_disjoint restrict_star matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_right matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_left)
        finally show ?thesis
          .
      qed
      have "?t\<langle>?o\<rangle>?t \<oplus> ?t\<langle>g\<rangle>?t \<odot> star_matrix' ?t g = ?t\<langle>?o\<rangle>?t \<oplus> ?t\<langle>g\<rangle>?t \<odot> (?es \<oplus> ?as \<odot> ?b \<odot> ?fs \<oplus> ?ds \<odot> ?c \<odot> ?es \<oplus> ?fs)"
        by (metis star_matrix'.simps(2))
      also have "... = ?t\<langle>?o\<rangle>?t \<oplus> ?t\<langle>g\<rangle>?t \<odot> ?es \<oplus> ?t\<langle>g\<rangle>?t \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?t\<langle>g\<rangle>?t \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?t\<langle>g\<rangle>?t \<odot> ?fs"
        by (simp add: matrix_idempotent_semiring.mult_left_dist_sup matrix_monoid.mult_assoc matrix_semilattice_sup.sup_assoc)
      also have "... = ?r\<langle>?o\<rangle>?r \<oplus> s\<langle>?o\<rangle>s \<oplus> ?a \<odot> ?es \<oplus> ?c \<odot> ?es \<oplus> ?a \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?c \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?b \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?d \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?b \<odot> ?fs \<oplus> ?d \<odot> ?fs"
        using 5 6 7 8 9 by (simp add: matrix_semilattice_sup.sup.assoc)
      also have "... = (?r\<langle>?o\<rangle>?r \<oplus> (?a \<odot> ?es \<oplus> ?b \<odot> ?ds \<odot> ?c \<odot> ?es)) \<oplus> (?b \<odot> ?fs \<oplus> ?a \<odot> ?as \<odot> ?b \<odot> ?fs) \<oplus> (?c \<odot> ?es \<oplus> ?d \<odot> ?ds \<odot> ?c \<odot> ?es) \<oplus> (s\<langle>?o\<rangle>s \<oplus> (?d \<odot> ?fs \<oplus> ?c \<odot> ?as \<odot> ?b \<odot> ?fs))"
        by (simp only: matrix_semilattice_sup.sup_assoc matrix_semilattice_sup.sup_commute matrix_semilattice_sup.sup_left_commute)
      also have "... = (?r\<langle>?o\<rangle>?r \<oplus> (?a \<odot> ?es \<oplus> ?b \<odot> ?ds \<odot> ?c \<odot> ?es)) \<oplus> (?r\<langle>?o\<rangle>?r \<odot> ?b \<odot> ?fs \<oplus> ?a \<odot> ?as \<odot> ?b \<odot> ?fs) \<oplus> (s\<langle>?o\<rangle>s \<odot> ?c \<odot> ?es \<oplus> ?d \<odot> ?ds \<odot> ?c \<odot> ?es) \<oplus> (s\<langle>?o\<rangle>s \<oplus> (?d \<odot> ?fs \<oplus> ?c \<odot> ?as \<odot> ?b \<odot> ?fs))"
        by (simp add: restrict_one_left_unit)
      also have "... = (?r\<langle>?o\<rangle>?r \<oplus> ?e \<odot> ?es) \<oplus> ((?r\<langle>?o\<rangle>?r \<oplus> ?a \<odot> ?as) \<odot> ?b \<odot> ?fs) \<oplus> ((s\<langle>?o\<rangle>s \<oplus> ?d \<odot> ?ds) \<odot> ?c \<odot> ?es) \<oplus> (s\<langle>?o\<rangle>s \<oplus> ?f \<odot> ?fs)"
        by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
      also have "... = (?r\<langle>?o\<rangle>?r \<oplus> ?e \<odot> ?es) \<oplus> ((?r\<langle>?o\<rangle>?r \<oplus> ?a \<odot> ?as) \<odot> ?b \<odot> ?fs) \<oplus> ((s\<langle>?o\<rangle>s \<oplus> ?d \<odot> ?ds) \<odot> ?c \<odot> ?es) \<oplus> ?fs"
        using 1 2 3 by (metis distinct.simps(2))
      also have "... = (?r\<langle>?o\<rangle>?r \<oplus> ?e \<odot> ?es) \<oplus> ((?r\<langle>?o\<rangle>?r \<oplus> ?a \<odot> ?as) \<odot> ?b \<odot> ?fs) \<oplus> (?ds \<odot> ?c \<odot> ?es) \<oplus> ?fs"
        using 1 2 by (metis (no_types, lifting) distinct.simps(2) restrict_superlist)
      also have "... = ?es \<oplus> ((?r\<langle>?o\<rangle>?r \<oplus> ?a \<odot> ?as) \<odot> ?b \<odot> ?fs) \<oplus> (?ds \<odot> ?c \<odot> ?es) \<oplus> ?fs"
        using 3 by (metis restrict_star_unfold)
      also have "... = ?es \<oplus> ?as \<odot> ?b \<odot> ?fs \<oplus> ?ds \<odot> ?c \<odot> ?es \<oplus> ?fs"
        by (metis (no_types, lifting) restrict_one_left_unit restrict_star_unfold restrict_times)
      also have "... = star_matrix' ?t g"
        by (metis star_matrix'.simps(2))
      finally show "?t\<langle>?o\<rangle>?t \<oplus> ?t\<langle>g\<rangle>?t \<odot> star_matrix' ?t g = star_matrix' ?t g"
        .
    qed
  qed
  thus "?o \<oplus> y \<odot> y\<^sup>\<odot> \<preceq> y\<^sup>\<odot>"
    by (simp add: enum_distinct restrict_all)
next
  fix x y z :: "('a,'b) square"
  let ?e = "enum_class.enum::'a list"
  have "\<forall>g h :: ('a,'b) square . \<forall>zs . distinct ?e \<and> distinct zs \<longrightarrow> (?e\<langle>g\<rangle>?e \<odot> ?e\<langle>h\<rangle>zs \<preceq> ?e\<langle>h\<rangle>zs \<longrightarrow> star_matrix' ?e g \<odot> ?e\<langle>h\<rangle>zs \<preceq> ?e\<langle>h\<rangle>zs)"
  proof (induct rule: list.induct)
    case Nil thus ?case
      by (simp add: restrict_empty_left)
    case (Cons k s)
    let ?t = "k#s"
    assume 1: "\<forall>g h :: ('a,'b) square . \<forall>zs . distinct s \<and> distinct zs \<longrightarrow> (s\<langle>g\<rangle>s \<odot> s\<langle>h\<rangle>zs \<preceq> s\<langle>h\<rangle>zs \<longrightarrow> star_matrix' s g \<odot> s\<langle>h\<rangle>zs \<preceq> s\<langle>h\<rangle>zs)"
    show "\<forall>g h :: ('a,'b) square . \<forall>zs . distinct ?t \<and> distinct zs \<longrightarrow> (?t\<langle>g\<rangle>?t \<odot> ?t\<langle>h\<rangle>zs \<preceq> ?t\<langle>h\<rangle>zs \<longrightarrow> star_matrix' ?t g \<odot> ?t\<langle>h\<rangle>zs \<preceq> ?t\<langle>h\<rangle>zs)"
    proof (intro allI)
      fix g h :: "('a,'b) square"
      fix zs :: "'a list"
      show "distinct ?t \<and> distinct zs \<longrightarrow> (?t\<langle>g\<rangle>?t \<odot> ?t\<langle>h\<rangle>zs \<preceq> ?t\<langle>h\<rangle>zs \<longrightarrow> star_matrix' ?t g \<odot> ?t\<langle>h\<rangle>zs \<preceq> ?t\<langle>h\<rangle>zs)"
      proof (cases zs)
        case Nil thus ?thesis
          by (metis restrict_empty_right restrict_star restrict_times)
      next
        case (Cons y ys)
        assume 2: "zs = y#ys"
        show "distinct ?t \<and> distinct zs \<longrightarrow> (?t\<langle>g\<rangle>?t \<odot> ?t\<langle>h\<rangle>zs \<preceq> ?t\<langle>h\<rangle>zs \<longrightarrow> star_matrix' ?t g \<odot> ?t\<langle>h\<rangle>zs \<preceq> ?t\<langle>h\<rangle>zs)"
        proof (intro impI)
          let ?y = "[y]"
          assume 3: "distinct ?t \<and> distinct zs"
          hence 4: "distinct s \<and> distinct ys \<and> \<not> List.member s k \<and> \<not> List.member ys y"
            using 2 by (simp add: List.member_def)
          let ?r = "[k]"
          let ?a = "?r\<langle>g\<rangle>?r"
          let ?b = "?r\<langle>g\<rangle>s"
          let ?c = "s\<langle>g\<rangle>?r"
          let ?d = "s\<langle>g\<rangle>s"
          let ?as = "?r\<langle>star o ?a\<rangle>?r"
          let ?ds = "star_matrix' s ?d"
          let ?e = "?a \<oplus> ?b \<odot> ?ds \<odot> ?c"
          let ?es = "?r\<langle>star o ?e\<rangle>?r"
          let ?f = "?d \<oplus> ?c \<odot> ?as \<odot> ?b"
          let ?fs = "star_matrix' s ?f"
          let ?ha = "?r\<langle>h\<rangle>?y"
          let ?hb = "?r\<langle>h\<rangle>ys"
          let ?hc = "s\<langle>h\<rangle>?y"
          let ?hd = "s\<langle>h\<rangle>ys"
          assume "?t\<langle>g\<rangle>?t \<odot> ?t\<langle>h\<rangle>zs \<preceq> ?t\<langle>h\<rangle>zs"
          hence 5: "?a \<odot> ?ha \<oplus> ?b \<odot> ?hc \<preceq> ?ha \<and> ?a \<odot> ?hb \<oplus> ?b \<odot> ?hd \<preceq> ?hb \<and> ?c \<odot> ?ha \<oplus> ?d \<odot> ?hc \<preceq> ?hc \<and> ?c \<odot> ?hb \<oplus> ?d \<odot> ?hd \<preceq> ?hd"
            using 2 3 4 by (simp add: restrict_nonempty_product_less_eq)
          have 6: "s\<langle>?ds\<rangle>s = ?ds \<and> s\<langle>?fs\<rangle>s = ?fs"
            by (simp add: restrict_star)
          hence 7: "?r\<langle>?e\<rangle>?r = ?e \<and> s\<langle>?f\<rangle>s = ?f"
            by (metis (no_types, lifting) restrict_one_left_unit restrict_sup restrict_times)
          have 8: "disjoint s ?r \<and> disjoint ?r s"
            using 3 by (simp add: in_set_member member_rec(1) member_rec(2))
          have 9: "?es \<odot> ?t\<langle>h\<rangle>zs = ?es \<odot> ?ha \<oplus> ?es \<odot> ?hb"
          proof -
            have "?es \<odot> ?t\<langle>h\<rangle>zs = ?es \<odot> (?ha \<oplus> ?hb \<oplus> ?hc \<oplus> ?hd)"
              using 2 by (metis restrict_nonempty)
            also have "... = ?es \<odot> ?ha \<oplus> ?es \<odot> ?hb \<oplus> ?es \<odot> ?hc \<oplus> ?es \<odot> ?hd"
              by (simp add: matrix_idempotent_semiring.mult_left_dist_sup)
            also have "... = ?es \<odot> ?ha \<oplus> ?es \<odot> ?hb"
              using 8 by (simp add: times_disjoint)
            finally show ?thesis
              .
          qed
          have 10: "?as \<odot> ?b \<odot> ?fs \<odot> ?t\<langle>h\<rangle>zs = ?as \<odot> ?b \<odot> ?fs \<odot> ?hc \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hd"
          proof -
            have "?as \<odot> ?b \<odot> ?fs \<odot> ?t\<langle>h\<rangle>zs = ?as \<odot> ?b \<odot> ?fs \<odot> (?ha \<oplus> ?hb \<oplus> ?hc \<oplus> ?hd)"
              using 2 by (metis restrict_nonempty)
            also have "... = ?as \<odot> ?b \<odot> ?fs \<odot> ?ha \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hb \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hc \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hd"
              by (simp add: matrix_idempotent_semiring.mult_left_dist_sup)
            also have "... = ?as \<odot> ?b \<odot> (?fs \<odot> ?ha) \<oplus> ?as \<odot> ?b \<odot> (?fs \<odot> ?hb) \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hc \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hd"
              by (simp add: matrix_monoid.mult_assoc)
            also have "... = ?as \<odot> ?b \<odot> mbot \<oplus> ?as \<odot> ?b \<odot> mbot \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hc \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hd"
              using 6 8 by (metis (no_types) times_disjoint)
            also have "... = ?as \<odot> ?b \<odot> ?fs \<odot> ?hc \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hd"
              by simp
            finally show ?thesis
              .
          qed
          have 11: "?ds \<odot> ?c \<odot> ?es \<odot> ?t\<langle>h\<rangle>zs = ?ds \<odot> ?c \<odot> ?es \<odot> ?ha \<oplus> ?ds \<odot> ?c \<odot> ?es \<odot> ?hb"
          proof -
            have "?ds \<odot> ?c \<odot> ?es \<odot> ?t\<langle>h\<rangle>zs = ?ds \<odot> ?c \<odot> ?es \<odot> (?ha \<oplus> ?hb \<oplus> ?hc \<oplus> ?hd)"
              using 2 by (metis restrict_nonempty)
            also have "... = ?ds \<odot> ?c \<odot> ?es \<odot> ?ha \<oplus> ?ds \<odot> ?c \<odot> ?es \<odot> ?hb \<oplus> ?ds \<odot> ?c \<odot> ?es \<odot> ?hc \<oplus> ?ds \<odot> ?c \<odot> ?es \<odot> ?hd"
              by (simp add: matrix_idempotent_semiring.mult_left_dist_sup)
            also have "... = ?ds \<odot> ?c \<odot> ?es \<odot> ?ha \<oplus> ?ds \<odot> ?c \<odot> ?es \<odot> ?hb \<oplus> ?ds \<odot> ?c \<odot> (?es \<odot> ?hc) \<oplus> ?ds \<odot> ?c \<odot> (?es \<odot> ?hd)"
              by (simp add: matrix_monoid.mult_assoc)
            also have "... = ?ds \<odot> ?c \<odot> ?es \<odot> ?ha \<oplus> ?ds \<odot> ?c \<odot> ?es \<odot> ?hb \<oplus> ?ds \<odot> ?c \<odot> mbot \<oplus> ?ds \<odot> ?c \<odot> mbot"
              using 8 by (metis times_disjoint)
            also have "... = ?ds \<odot> ?c \<odot> ?es \<odot> ?ha \<oplus> ?ds \<odot> ?c \<odot> ?es \<odot> ?hb"
              by simp
            finally show ?thesis
              .
          qed
          have 12: "?fs \<odot> ?t\<langle>h\<rangle>zs = ?fs \<odot> ?hc \<oplus> ?fs \<odot> ?hd"
          proof -
            have "?fs \<odot> ?t\<langle>h\<rangle>zs = ?fs \<odot> (?ha \<oplus> ?hb \<oplus> ?hc \<oplus> ?hd)"
              using 2 by (metis restrict_nonempty)
            also have "... = ?fs \<odot> ?ha \<oplus> ?fs \<odot> ?hb \<oplus> ?fs \<odot> ?hc \<oplus> ?fs \<odot> ?hd"
              by (simp add: matrix_idempotent_semiring.mult_left_dist_sup)
            also have "... = ?fs \<odot> ?hc \<oplus> ?fs \<odot> ?hd"
              using 6 8 by (metis (no_types) times_disjoint matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_left)
            finally show ?thesis
              .
          qed
          have 13: "?es \<odot> ?ha \<preceq> ?ha"
          proof -
            have "?b \<odot> ?ds \<odot> ?c \<odot> ?ha \<preceq> ?b \<odot> ?ds \<odot> ?hc"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?b \<odot> ?hc"
              using 1 3 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc member_rec(2) restrict_sublist)
            also have "... \<preceq> ?ha"
              using 5 by simp
            finally have "?e \<odot> ?ha \<preceq> ?ha"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
            thus ?thesis
              using 7 by (simp add: restrict_star_left_induct)
          qed
          have 14: "?es \<odot> ?hb \<preceq> ?hb"
          proof -
            have "?b \<odot> ?ds \<odot> ?c \<odot> ?hb \<preceq> ?b \<odot> ?ds \<odot> ?hd"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?b \<odot> ?hd"
              using 1 4 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc restrict_sublist)
            also have "... \<preceq> ?hb"
              using 5 by simp
            finally have "?e \<odot> ?hb \<preceq> ?hb"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
            thus ?thesis
              using 4 7 by (simp add: restrict_star_left_induct)
          qed
          have 15: "?fs \<odot> ?hc \<preceq> ?hc"
          proof -
            have "?c \<odot> ?as \<odot> ?b \<odot> ?hc \<preceq> ?c \<odot> ?as \<odot> ?ha"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?c \<odot> ?ha"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc restrict_star_left_induct restrict_sublist)
            also have "... \<preceq> ?hc"
              using 5 by simp
            finally have "?f \<odot> ?hc \<preceq> ?hc"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
            thus ?thesis
              using 1 3 7 by simp
          qed
          have 16: "?fs \<odot> ?hd \<preceq> ?hd"
          proof -
            have "?c \<odot> ?as \<odot> ?b \<odot> ?hd \<preceq> ?c \<odot> ?as \<odot> ?hb"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?c \<odot> ?hb"
              using 4 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc restrict_star_left_induct restrict_sublist)
            also have "... \<preceq> ?hd"
              using 5 by simp
            finally have "?f \<odot> ?hd \<preceq> ?hd"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
            thus ?thesis
              using 1 4 7 by simp
          qed
          have 17: "?as \<odot> ?b \<odot> ?fs \<odot> ?hc \<preceq> ?ha"
          proof -
            have "?as \<odot> ?b \<odot> ?fs \<odot> ?hc \<preceq> ?as \<odot> ?b \<odot> ?hc"
              using 15 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?as \<odot> ?ha"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?ha"
              using 5 by (simp add: restrict_star_left_induct restrict_sublist)
            finally show ?thesis
              .
          qed
          have 18: "?as \<odot> ?b \<odot> ?fs \<odot> ?hd \<preceq> ?hb"
          proof -
            have "?as \<odot> ?b \<odot> ?fs \<odot> ?hd \<preceq> ?as \<odot> ?b \<odot> ?hd"
              using 16 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?as \<odot> ?hb"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?hb"
              using 4 5 by (simp add: restrict_star_left_induct restrict_sublist)
            finally show ?thesis
              .
          qed
          have 19: "?ds \<odot> ?c \<odot> ?es \<odot> ?ha \<preceq> ?hc"
          proof -
            have "?ds \<odot> ?c \<odot> ?es \<odot> ?ha \<preceq> ?ds \<odot> ?c \<odot> ?ha"
              using 13 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?ds \<odot> ?hc"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?hc"
              using 1 3 5 by (simp add: restrict_sublist)
            finally show ?thesis
              .
          qed
          have 20: "?ds \<odot> ?c \<odot> ?es \<odot> ?hb \<preceq> ?hd"
          proof -
            have "?ds \<odot> ?c \<odot> ?es \<odot> ?hb \<preceq> ?ds \<odot> ?c \<odot> ?hb"
              using 14 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?ds \<odot> ?hd"
              using 5 by (simp add: matrix_idempotent_semiring.mult_right_isotone matrix_monoid.mult_assoc)
            also have "... \<preceq> ?hd"
              using 1 4 5 by (simp add: restrict_sublist)
            finally show ?thesis
              .
          qed
          have 21: "?es \<odot> ?ha \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hc \<preceq> ?ha"
            using 13 17 matrix_semilattice_sup.le_supI by blast
          have 22: "?es \<odot> ?hb \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hd \<preceq> ?hb"
            using 14 18 matrix_semilattice_sup.le_supI by blast
          have 23: "?ds \<odot> ?c \<odot> ?es \<odot> ?ha \<oplus> ?fs \<odot> ?hc \<preceq> ?hc"
            using 15 19 matrix_semilattice_sup.le_supI by blast
          have 24: "?ds \<odot> ?c \<odot> ?es \<odot> ?hb \<oplus> ?fs \<odot> ?hd \<preceq> ?hd"
            using 16 20 matrix_semilattice_sup.le_supI by blast
          have "star_matrix' ?t g \<odot> ?t\<langle>h\<rangle>zs = (?es \<oplus> ?as \<odot> ?b \<odot> ?fs \<oplus> ?ds \<odot> ?c \<odot> ?es \<oplus> ?fs) \<odot> ?t\<langle>h\<rangle>zs"
            by (metis star_matrix'.simps(2))
          also have "... = ?es \<odot> ?t\<langle>h\<rangle>zs \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?t\<langle>h\<rangle>zs \<oplus> ?ds \<odot> ?c \<odot> ?es \<odot> ?t\<langle>h\<rangle>zs \<oplus> ?fs \<odot> ?t\<langle>h\<rangle>zs"
            by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
          also have "... = ?es \<odot> ?ha \<oplus> ?es \<odot> ?hb \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hc \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hd \<oplus> ?ds \<odot> ?c \<odot> ?es \<odot> ?ha \<oplus> ?ds \<odot> ?c \<odot> ?es \<odot> ?hb \<oplus> ?fs \<odot> ?hc \<oplus> ?fs \<odot> ?hd"
            using 9 10 11 12 by (simp only: matrix_semilattice_sup.sup_assoc)
          also have "... = (?es \<odot> ?ha \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hc) \<oplus> (?es \<odot> ?hb \<oplus> ?as \<odot> ?b \<odot> ?fs \<odot> ?hd) \<oplus> (?ds \<odot> ?c \<odot> ?es \<odot> ?ha \<oplus> ?fs \<odot> ?hc) \<oplus> (?ds \<odot> ?c \<odot> ?es \<odot> ?hb \<oplus> ?fs \<odot> ?hd)"
            by (simp only: matrix_semilattice_sup.sup_assoc matrix_semilattice_sup.sup_commute matrix_semilattice_sup.sup_left_commute)
          also have "... \<preceq> ?ha \<oplus> ?hb \<oplus> ?hc \<oplus> ?hd"
            using 21 22 23 24 matrix_semilattice_sup.sup.mono by blast
          also have "... = ?t\<langle>h\<rangle>zs"
            using 2 by (metis restrict_nonempty)
          finally show "star_matrix' ?t g \<odot> ?t\<langle>h\<rangle>zs \<preceq> ?t\<langle>h\<rangle>zs"
            .
        qed
      qed
    qed
  qed
  hence "\<forall>zs . distinct zs \<longrightarrow> (y \<odot> ?e\<langle>x\<rangle>zs \<preceq> ?e\<langle>x\<rangle>zs \<longrightarrow> y\<^sup>\<odot> \<odot> ?e\<langle>x\<rangle>zs \<preceq> ?e\<langle>x\<rangle>zs)"
    by (simp add: enum_distinct restrict_all)
  thus "y \<odot> x \<preceq> x \<longrightarrow> y\<^sup>\<odot> \<odot> x \<preceq> x"
    by (metis restrict_all enum_distinct)
next
  fix x y z :: "('a,'b) square"
  let ?e = "enum_class.enum::'a list"
  have "\<forall>g h :: ('a,'b) square . \<forall>zs . distinct ?e \<and> distinct zs \<longrightarrow> (zs\<langle>h\<rangle>?e \<odot> ?e\<langle>g\<rangle>?e \<preceq> zs\<langle>h\<rangle>?e \<longrightarrow> zs\<langle>h\<rangle>?e \<odot> star_matrix' ?e g \<preceq> zs\<langle>h\<rangle>?e)"
  proof (induct rule:list.induct)
    case Nil thus ?case
      by (simp add: restrict_empty_left)
    case (Cons k s)
    let ?t = "k#s"
    assume 1: "\<forall>g h :: ('a,'b) square . \<forall>zs . distinct s \<and> distinct zs \<longrightarrow> (zs\<langle>h\<rangle>s \<odot> s\<langle>g\<rangle>s \<preceq> zs\<langle>h\<rangle>s \<longrightarrow> zs\<langle>h\<rangle>s \<odot> star_matrix' s g \<preceq> zs\<langle>h\<rangle>s)"
    show "\<forall>g h :: ('a,'b) square . \<forall>zs . distinct ?t \<and> distinct zs \<longrightarrow> (zs\<langle>h\<rangle>?t \<odot> ?t\<langle>g\<rangle>?t \<preceq> zs\<langle>h\<rangle>?t \<longrightarrow> zs\<langle>h\<rangle>?t \<odot> star_matrix' ?t g \<preceq> zs\<langle>h\<rangle>?t)"
    proof (intro allI)
      fix g h :: "('a,'b) square"
      fix zs :: "'a list"
      show "distinct ?t \<and> distinct zs \<longrightarrow> (zs\<langle>h\<rangle>?t \<odot> ?t\<langle>g\<rangle>?t \<preceq> zs\<langle>h\<rangle>?t \<longrightarrow> zs\<langle>h\<rangle>?t \<odot> star_matrix' ?t g \<preceq> zs\<langle>h\<rangle>?t)"
      proof (cases zs)
        case Nil thus ?thesis
          by (metis restrict_empty_left restrict_star restrict_times)
      next
        case (Cons y ys)
        assume 2: "zs = y#ys"
        show "distinct ?t \<and> distinct zs \<longrightarrow> (zs\<langle>h\<rangle>?t \<odot> ?t\<langle>g\<rangle>?t \<preceq> zs\<langle>h\<rangle>?t \<longrightarrow> zs\<langle>h\<rangle>?t \<odot> star_matrix' ?t g \<preceq> zs\<langle>h\<rangle>?t)"
        proof (intro impI)
          let ?y = "[y]"
          assume 3: "distinct ?t \<and> distinct zs"
          hence 4: "distinct s \<and> distinct ys \<and> \<not> List.member s k \<and> \<not> List.member ys y"
            using 2 by (simp add: List.member_def)
          let ?r = "[k]"
          let ?a = "?r\<langle>g\<rangle>?r"
          let ?b = "?r\<langle>g\<rangle>s"
          let ?c = "s\<langle>g\<rangle>?r"
          let ?d = "s\<langle>g\<rangle>s"
          let ?as = "?r\<langle>star o ?a\<rangle>?r"
          let ?ds = "star_matrix' s ?d"
          let ?e = "?a \<oplus> ?b \<odot> ?ds \<odot> ?c"
          let ?es = "?r\<langle>star o ?e\<rangle>?r"
          let ?f = "?d \<oplus> ?c \<odot> ?as \<odot> ?b"
          let ?fs = "star_matrix' s ?f"
          let ?ha = "?y\<langle>h\<rangle>?r"
          let ?hb = "?y\<langle>h\<rangle>s"
          let ?hc = "ys\<langle>h\<rangle>?r"
          let ?hd = "ys\<langle>h\<rangle>s"
          assume "zs\<langle>h\<rangle>?t \<odot> ?t\<langle>g\<rangle>?t \<preceq> zs\<langle>h\<rangle>?t"
          hence 5: "?ha \<odot> ?a \<oplus> ?hb \<odot> ?c \<preceq> ?ha \<and> ?ha \<odot> ?b \<oplus> ?hb \<odot> ?d \<preceq> ?hb \<and> ?hc \<odot> ?a \<oplus> ?hd \<odot> ?c \<preceq> ?hc \<and> ?hc \<odot> ?b \<oplus> ?hd \<odot> ?d \<preceq> ?hd"
            using 2 3 4 by (simp add: restrict_nonempty_product_less_eq)
          have 6: "s\<langle>?ds\<rangle>s = ?ds \<and> s\<langle>?fs\<rangle>s = ?fs"
            by (simp add: restrict_star)
          hence 7: "?r\<langle>?e\<rangle>?r = ?e \<and> s\<langle>?f\<rangle>s = ?f"
            by (metis (no_types, lifting) restrict_one_left_unit restrict_sup restrict_times)
          have 8: "disjoint s ?r \<and> disjoint ?r s"
            using 3 by (simp add: in_set_member member_rec)
          have 9: "zs\<langle>h\<rangle>?t \<odot> ?es = ?ha \<odot> ?es \<oplus> ?hc \<odot> ?es"
          proof -
            have "zs\<langle>h\<rangle>?t \<odot> ?es = (?ha \<oplus> ?hb \<oplus> ?hc \<oplus> ?hd) \<odot> ?es"
              using 2 by (metis restrict_nonempty)
            also have "... = ?ha \<odot> ?es \<oplus> ?hb \<odot> ?es \<oplus> ?hc \<odot> ?es \<oplus> ?hd \<odot> ?es"
              by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
            also have "... = ?ha \<odot> ?es \<oplus> ?hc \<odot> ?es"
              using 8 by (simp add: times_disjoint)
            finally show ?thesis
              .
          qed
          have 10: "zs\<langle>h\<rangle>?t \<odot> ?as \<odot> ?b \<odot> ?fs = ?ha \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hc \<odot> ?as \<odot> ?b \<odot> ?fs"
          proof -
            have "zs\<langle>h\<rangle>?t \<odot> ?as \<odot> ?b \<odot> ?fs = (?ha \<oplus> ?hb \<oplus> ?hc \<oplus> ?hd) \<odot> ?as \<odot> ?b \<odot> ?fs"
              using 2 by (metis restrict_nonempty)
            also have "... = ?ha \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hb \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hc \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hd \<odot> ?as \<odot> ?b \<odot> ?fs"
              by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
            also have "... = ?ha \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> mbot \<odot> ?b \<odot> ?fs \<oplus> ?hc \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> mbot \<odot> ?b \<odot> ?fs"
              using 8 by (metis (no_types) times_disjoint)
            also have "... = ?ha \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hc \<odot> ?as \<odot> ?b \<odot> ?fs"
              by simp
            finally show ?thesis
              .
          qed
          have 11: "zs\<langle>h\<rangle>?t \<odot> ?ds \<odot> ?c \<odot> ?es = ?hb \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?hd \<odot> ?ds \<odot> ?c \<odot> ?es"
          proof -
            have "zs\<langle>h\<rangle>?t \<odot> ?ds \<odot> ?c \<odot> ?es = (?ha \<oplus> ?hb \<oplus> ?hc \<oplus> ?hd) \<odot> ?ds \<odot> ?c \<odot> ?es"
              using 2 by (metis restrict_nonempty)
            also have "... = ?ha \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?hb \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?hc \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?hd \<odot> ?ds \<odot> ?c \<odot> ?es"
              by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
            also have "... = mbot \<odot> ?c \<odot> ?es \<oplus> ?hb \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> mbot \<odot> ?c \<odot> ?es \<oplus> ?hd \<odot> ?ds \<odot> ?c \<odot> ?es"
              using 6 8 by (metis (no_types) times_disjoint)
            also have "... = ?hb \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?hd \<odot> ?ds \<odot> ?c \<odot> ?es"
              by simp
            finally show ?thesis
              .
          qed
          have 12: "zs\<langle>h\<rangle>?t \<odot> ?fs = ?hb \<odot> ?fs \<oplus> ?hd \<odot> ?fs"
          proof -
            have "zs\<langle>h\<rangle>?t \<odot> ?fs = (?ha \<oplus> ?hb \<oplus> ?hc \<oplus> ?hd) \<odot> ?fs"
              using 2 by (metis restrict_nonempty)
            also have "... = ?ha \<odot> ?fs \<oplus> ?hb \<odot> ?fs \<oplus> ?hc \<odot> ?fs \<oplus> ?hd \<odot> ?fs"
              by (simp add: matrix_idempotent_semiring.mult_right_dist_sup)
            also have "... = ?hb \<odot> ?fs \<oplus> ?hd \<odot> ?fs"
              using 6 8 by (metis (no_types) times_disjoint matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_right matrix_bounded_semilattice_sup_bot.sup_monoid.add_0_left)
            finally show ?thesis
              .
          qed
          have 13: "?ha \<odot> ?es \<preceq> ?ha"
          proof -
            have "?ha \<odot> ?b \<odot> ?ds \<odot> ?c \<preceq> ?hb \<odot> ?ds \<odot> ?c"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone)
            also have "... \<preceq> ?hb \<odot> ?c"
              using 1 4 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone restrict_sublist)
            also have "... \<preceq> ?ha"
              using 5 by simp
            finally have "?ha \<odot> ?e \<preceq> ?ha"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_dist_sup matrix_monoid.mult_assoc)
            thus ?thesis
              using 7 by (simp add: restrict_star_right_induct)
          qed
          have 14: "?hb \<odot> ?fs \<preceq> ?hb"
          proof -
            have "?hb \<odot> ?c \<odot> ?as \<odot> ?b \<preceq> ?ha \<odot> ?as \<odot> ?b"
              using 5 by (metis matrix_semilattice_sup.le_supE matrix_idempotent_semiring.mult_left_isotone)
            also have "... \<preceq> ?ha \<odot> ?b"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone restrict_star_right_induct restrict_sublist)
            also have "... \<preceq> ?hb"
              using 5 by simp
            finally have "?hb \<odot> ?f \<preceq> ?hb"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_dist_sup matrix_monoid.mult_assoc)
            thus ?thesis
              using 1 3 7 by simp
          qed
          have 15: "?hc \<odot> ?es \<preceq> ?hc"
          proof -
            have "?hc \<odot> ?b \<odot> ?ds \<odot> ?c \<preceq> ?hd \<odot> ?ds \<odot> ?c"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone)
            also have "... \<preceq> ?hd \<odot> ?c"
              using 1 4 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone restrict_sublist)
            also have "... \<preceq> ?hc"
              using 5 by simp
            finally have "?hc \<odot> ?e \<preceq> ?hc"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_dist_sup matrix_monoid.mult_assoc)
            thus ?thesis
              using 4 7 by (simp add: restrict_star_right_induct)
          qed
          have 16: "?hd \<odot> ?fs \<preceq> ?hd"
          proof -
            have "?hd \<odot> ?c \<odot> ?as \<odot> ?b \<preceq> ?hc \<odot> ?as \<odot> ?b"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone)
            also have "... \<preceq> ?hc \<odot> ?b"
              using 4 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone restrict_star_right_induct restrict_sublist)
            also have "... \<preceq> ?hd"
              using 5 by simp
            finally have "?hd \<odot> ?f \<preceq> ?hd"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_dist_sup matrix_monoid.mult_assoc)
            thus ?thesis
              using 1 4 7 by simp
          qed
          have 17: "?hb \<odot> ?ds \<odot> ?c \<odot> ?es \<preceq> ?ha"
          proof -
            have "?hb \<odot> ?ds \<odot> ?c \<odot> ?es \<preceq> ?hb \<odot> ?c \<odot> ?es"
              using 1 4 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone restrict_sublist)
            also have "... \<preceq> ?ha \<odot> ?es"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone)
            also have "... \<preceq> ?ha"
              using 13 by simp
            finally show ?thesis
              .
          qed
          have 18: "?ha \<odot> ?as \<odot> ?b \<odot> ?fs \<preceq> ?hb"
          proof -
            have "?ha \<odot> ?as \<odot> ?b \<odot> ?fs \<preceq> ?ha \<odot> ?b \<odot> ?fs"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone restrict_star_right_induct restrict_sublist)
            also have "... \<preceq> ?hb \<odot> ?fs"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone)
            also have "... \<preceq> ?hb"
              using 14 by simp
            finally show ?thesis
              by simp
          qed
          have 19: "?hd \<odot> ?ds \<odot> ?c \<odot> ?es \<preceq> ?hc"
          proof -
            have "?hd \<odot> ?ds \<odot> ?c \<odot> ?es \<preceq> ?hd \<odot> ?c \<odot> ?es"
              using 1 4 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone restrict_sublist)
            also have "... \<preceq> ?hc \<odot> ?es"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone)
            also have "... \<preceq> ?hc"
              using 15 by simp
            finally show ?thesis
              by simp
          qed
          have 20: "?hc \<odot> ?as \<odot> ?b \<odot> ?fs \<preceq> ?hd"
          proof -
            have "?hc \<odot> ?as \<odot> ?b \<odot> ?fs \<preceq> ?hc \<odot> ?b \<odot> ?fs"
              using 4 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone restrict_star_right_induct restrict_sublist)
            also have "... \<preceq> ?hd \<odot> ?fs"
              using 5 by (simp add: matrix_idempotent_semiring.mult_left_isotone)
            also have "... \<preceq> ?hd"
              using 16 by simp
            finally show ?thesis
              by simp
          qed
          have 21: "?ha \<odot> ?es \<oplus> ?hb \<odot> ?ds \<odot> ?c \<odot> ?es \<preceq> ?ha"
            using 13 17 matrix_semilattice_sup.le_supI by blast
          have 22: "?ha \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hb \<odot> ?fs \<preceq> ?hb"
            using 14 18 matrix_semilattice_sup.le_supI by blast
          have 23: "?hc \<odot> ?es \<oplus> ?hd \<odot> ?ds \<odot> ?c \<odot> ?es \<preceq> ?hc"
            using 15 19 matrix_semilattice_sup.le_supI by blast
          have 24: "?hc \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hd \<odot> ?fs \<preceq> ?hd"
            using 16 20 matrix_semilattice_sup.le_supI by blast
          have "zs\<langle>h\<rangle>?t \<odot> star_matrix' ?t g = zs\<langle>h\<rangle>?t \<odot> (?es \<oplus> ?as \<odot> ?b \<odot> ?fs \<oplus> ?ds \<odot> ?c \<odot> ?es \<oplus> ?fs)"
            by (metis star_matrix'.simps(2))
          also have "... = zs\<langle>h\<rangle>?t \<odot> ?es \<oplus> zs\<langle>h\<rangle>?t \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> zs\<langle>h\<rangle>?t \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> zs\<langle>h\<rangle>?t \<odot> ?fs"
            by (simp add: matrix_idempotent_semiring.mult_left_dist_sup matrix_monoid.mult_assoc)
          also have "... = ?ha \<odot> ?es \<oplus> ?hc \<odot> ?es \<oplus> ?ha \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hc \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hb \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?hd \<odot> ?ds \<odot> ?c \<odot> ?es \<oplus> ?hb \<odot> ?fs \<oplus> ?hd \<odot> ?fs"
            using 9 10 11 12 by (simp add: matrix_semilattice_sup.sup_assoc)
          also have "... = (?ha \<odot> ?es \<oplus> ?hb \<odot> ?ds \<odot> ?c \<odot> ?es) \<oplus> (?ha \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hb \<odot> ?fs) \<oplus> (?hc \<odot> ?es \<oplus> ?hd \<odot> ?ds \<odot> ?c \<odot> ?es) \<oplus> (?hc \<odot> ?as \<odot> ?b \<odot> ?fs \<oplus> ?hd \<odot> ?fs)"
            using 9 10 11 12 by (simp only: matrix_semilattice_sup.sup_assoc matrix_semilattice_sup.sup_commute matrix_semilattice_sup.sup_left_commute)
          also have "... \<preceq> ?ha \<oplus> ?hb \<oplus> ?hc \<oplus> ?hd"
            using 21 22 23 24 matrix_semilattice_sup.sup.mono by blast
          also have "... = zs\<langle>h\<rangle>?t"
            using 2 by (metis restrict_nonempty)
          finally show "zs\<langle>h\<rangle>?t \<odot> star_matrix' ?t g \<preceq> zs\<langle>h\<rangle>?t"
            .
        qed
      qed
    qed
  qed
  hence "\<forall>zs . distinct zs \<longrightarrow> (zs\<langle>x\<rangle>?e \<odot> y \<preceq> zs\<langle>x\<rangle>?e \<longrightarrow> zs\<langle>x\<rangle>?e \<odot> y\<^sup>\<odot> \<preceq> zs\<langle>x\<rangle>?e)"
    by (simp add: enum_distinct restrict_all)
  thus "x \<odot> y \<preceq> x \<longrightarrow> x \<odot> y\<^sup>\<odot> \<preceq> x"
    by (metis restrict_all enum_distinct)
qed

subsection \<open>Matrices form a Stone-Kleene Relation Algebra\<close>

text \<open>
Matrices over Stone-Kleene relation algebras form a Stone-Kleene relation algebra.
It remains to prove the axiom about the interaction of Kleene star and double complement.
\<close>

interpretation matrix_stone_kleene_relation_algebra: stone_kleene_relation_algebra where sup = sup_matrix and inf = inf_matrix and less_eq = less_eq_matrix and less = less_matrix and bot = "bot_matrix::('a::enum,'b::stone_kleene_relation_algebra) square" and top = top_matrix and uminus = uminus_matrix and one = one_matrix and times = times_matrix and conv = conv_matrix and star = star_matrix
proof
  fix x :: "('a,'b) square"
  let ?e = "enum_class.enum::'a list"
  let ?o = "mone :: ('a,'b) square"
  show "\<ominus>\<ominus>(x\<^sup>\<odot>) = (\<ominus>\<ominus>x)\<^sup>\<odot>"
  proof (rule matrix_order.antisym)
    have "\<forall>g :: ('a,'b) square . distinct ?e \<longrightarrow> \<ominus>\<ominus>(star_matrix' ?e (\<ominus>\<ominus>g)) = star_matrix' ?e (\<ominus>\<ominus>g)"
    proof (induct rule: list.induct)
      case Nil thus ?case
        by simp
    next
      case (Cons k s)
      let ?t = "k#s"
      assume 1: "\<forall>g :: ('a,'b) square . distinct s \<longrightarrow> \<ominus>\<ominus>(star_matrix' s (\<ominus>\<ominus>g)) = star_matrix' s (\<ominus>\<ominus>g)"
      show "\<forall>g :: ('a,'b) square . distinct ?t \<longrightarrow> \<ominus>\<ominus>(star_matrix' ?t (\<ominus>\<ominus>g)) = star_matrix' ?t (\<ominus>\<ominus>g)"
      proof (rule allI, rule impI)
        fix g :: "('a,'b) square"
        assume 2: "distinct ?t"
        let ?r = "[k]"
        let ?a = "?r\<langle>\<ominus>\<ominus>g\<rangle>?r"
        let ?b = "?r\<langle>\<ominus>\<ominus>g\<rangle>s"
        let ?c = "s\<langle>\<ominus>\<ominus>g\<rangle>?r"
        let ?d = "s\<langle>\<ominus>\<ominus>g\<rangle>s"
        let ?as = "?r\<langle>star o ?a\<rangle>?r"
        let ?ds = "star_matrix' s ?d"
        let ?e = "?a \<oplus> ?b \<odot> ?ds \<odot> ?c"
        let ?es = "?r\<langle>star o ?e\<rangle>?r"
        let ?f = "?d \<oplus> ?c \<odot> ?as \<odot> ?b"
        let ?fs = "star_matrix' s ?f"
        have "s\<langle>?ds\<rangle>s = ?ds \<and> s\<langle>?fs\<rangle>s = ?fs"
          by (simp add: restrict_star)
        have 3: "\<ominus>\<ominus>?a = ?a \<and> \<ominus>\<ominus>?b = ?b \<and> \<ominus>\<ominus>?c = ?c \<and> \<ominus>\<ominus>?d = ?d"
          by (metis matrix_p_algebra.regular_closed_p restrict_pp)
        hence 4: "\<ominus>\<ominus>?as = ?as"
          by (metis pp_star_commute restrict_pp)
        hence "\<ominus>\<ominus>?f = ?f"
          using 3 by (metis matrix_stone_algebra.regular_closed_sup matrix_stone_relation_algebra.regular_mult_closed)
        hence 5: "\<ominus>\<ominus>?fs = ?fs"
          using 1 2 by (metis distinct.simps(2))
        have 6: "\<ominus>\<ominus>?ds = ?ds"
          using 1 2 by (simp add: restrict_pp)
        hence "\<ominus>\<ominus>?e = ?e"
          using 3 by (metis matrix_stone_algebra.regular_closed_sup matrix_stone_relation_algebra.regular_mult_closed)
        hence 7: "\<ominus>\<ominus>?es = ?es"
          by (metis pp_star_commute restrict_pp)
        have "\<ominus>\<ominus>(star_matrix' ?t (\<ominus>\<ominus>g)) = \<ominus>\<ominus>(?es \<oplus> ?as \<odot> ?b \<odot> ?fs \<oplus> ?ds \<odot> ?c \<odot> ?es \<oplus> ?fs)"
          by (metis star_matrix'.simps(2))
        also have "... = \<ominus>\<ominus>?es \<oplus> \<ominus>\<ominus>?as \<odot> \<ominus>\<ominus>?b \<odot> \<ominus>\<ominus>?fs \<oplus> \<ominus>\<ominus>?ds \<odot> \<ominus>\<ominus>?c \<odot> \<ominus>\<ominus>?es \<oplus> \<ominus>\<ominus>?fs"
          by (simp add: matrix_stone_relation_algebra.pp_dist_comp)
        also have "... = ?es \<oplus> ?as \<odot> ?b \<odot> ?fs \<oplus> ?ds \<odot> ?c \<odot> ?es \<oplus> ?fs"
          using 3 4 5 6 7 by simp
        finally show "\<ominus>\<ominus>(star_matrix' ?t (\<ominus>\<ominus>g)) = star_matrix' ?t (\<ominus>\<ominus>g)"
          by (metis star_matrix'.simps(2))
      qed
    qed
    hence "(\<ominus>\<ominus>x)\<^sup>\<odot> = \<ominus>\<ominus>((\<ominus>\<ominus>x)\<^sup>\<odot>)"
      by (simp add: enum_distinct restrict_all)
    thus "\<ominus>\<ominus>(x\<^sup>\<odot>) \<preceq> (\<ominus>\<ominus>x)\<^sup>\<odot>"
      by (metis matrix_kleene_algebra.star.circ_isotone matrix_p_algebra.pp_increasing matrix_p_algebra.pp_isotone)
  next
    have "?o \<oplus> \<ominus>\<ominus>x \<odot> \<ominus>\<ominus>(x\<^sup>\<odot>) \<preceq> \<ominus>\<ominus>(x\<^sup>\<odot>)"
      by (metis matrix_kleene_algebra.star_left_unfold_equal matrix_p_algebra.sup_pp_semi_commute matrix_stone_relation_algebra.pp_dist_comp)
    thus "(\<ominus>\<ominus>x)\<^sup>\<odot> \<preceq> \<ominus>\<ominus>(x\<^sup>\<odot>)"
      using matrix_kleene_algebra.star_left_induct by fastforce
  qed
qed

end

