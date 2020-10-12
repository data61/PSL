(*
    Author:   Salomon Sickert
    Author:   Benedikt Seidl
    Author:   Alexander Schimpf (original entry: CAVA/LTL_Rewrite.thy)
    License:  BSD
*)

section \<open>Rewrite Rules for LTL Simplification\<close>

theory Rewriting
imports
  LTL "HOL-Library.Extended_Nat"
begin

text \<open>This theory provides rewrite rules for the simplification of LTL formulas. It supports:
  \begin{itemize}
    \item Constants Removal
    \item @{const Next_ltln}-Normalisation
    \item Modal Simplification (based on pure eventual, pure universal, or suspendable formulas)
    \item Syntactic Implication Checking
  \end{itemize}
  It reuses parts of LTL\_Rewrite.thy (CAVA, LTL\_TO\_GBA). Furthermore, some rules were taken from
  \cite{DBLP:conf/cav/SomenziB00} and \cite{DBLP:conf/tacas/BabiakKRS12}. All functions are defined for @{type ltln}.\<close>



subsection \<open>Constant Eliminating Constructors\<close>

definition mk_and
where
  "mk_and x y \<equiv> case x of false\<^sub>n \<Rightarrow> false\<^sub>n | true\<^sub>n \<Rightarrow> y | _ \<Rightarrow> (case y of false\<^sub>n \<Rightarrow> false\<^sub>n | true\<^sub>n \<Rightarrow> x | _ \<Rightarrow> x and\<^sub>n y)"

definition mk_or
where
  "mk_or x y \<equiv> case x of false\<^sub>n \<Rightarrow> y | true\<^sub>n \<Rightarrow> true\<^sub>n | _ \<Rightarrow> (case y of true\<^sub>n \<Rightarrow> true\<^sub>n | false\<^sub>n \<Rightarrow> x | _ \<Rightarrow> x or\<^sub>n y)"

fun remove_strong_ops
where
  "remove_strong_ops (x U\<^sub>n y) = remove_strong_ops y"
| "remove_strong_ops (x M\<^sub>n y) = x and\<^sub>n y"
| "remove_strong_ops (x or\<^sub>n y) = remove_strong_ops x or\<^sub>n remove_strong_ops y"
| "remove_strong_ops x = x"

fun remove_weak_ops
where
  "remove_weak_ops (x R\<^sub>n y) = remove_weak_ops y"
| "remove_weak_ops (x W\<^sub>n y) = x or\<^sub>n y"
| "remove_weak_ops (x and\<^sub>n y) = remove_weak_ops x and\<^sub>n remove_weak_ops y"
| "remove_weak_ops x = x"

definition mk_finally
where
  "mk_finally x \<equiv> case x of true\<^sub>n \<Rightarrow> true\<^sub>n | false\<^sub>n \<Rightarrow> false\<^sub>n | _ \<Rightarrow> F\<^sub>n (remove_strong_ops x)"

definition mk_globally
where
  "mk_globally x \<equiv> case x of true\<^sub>n \<Rightarrow> true\<^sub>n | false\<^sub>n \<Rightarrow> false\<^sub>n | _ \<Rightarrow> G\<^sub>n (remove_weak_ops x)"

definition mk_until
where
  "mk_until x y \<equiv> case x of false\<^sub>n \<Rightarrow> y
    | true\<^sub>n \<Rightarrow> mk_finally y
    | _ \<Rightarrow> (case y of true\<^sub>n \<Rightarrow> true\<^sub>n | false\<^sub>n \<Rightarrow> false\<^sub>n | _ \<Rightarrow> x U\<^sub>n y)"

definition mk_release
where
  "mk_release x y \<equiv> case x of true\<^sub>n \<Rightarrow> y
    | false\<^sub>n \<Rightarrow> mk_globally y
    | _ \<Rightarrow> (case y of true\<^sub>n \<Rightarrow> true\<^sub>n | false\<^sub>n \<Rightarrow> false\<^sub>n | _ \<Rightarrow> x R\<^sub>n y)"

definition mk_weak_until
where
  "mk_weak_until x y \<equiv> case y of true\<^sub>n \<Rightarrow> true\<^sub>n
    | false\<^sub>n \<Rightarrow> mk_globally x
    | _ \<Rightarrow> (case x of true\<^sub>n \<Rightarrow> true\<^sub>n | false\<^sub>n \<Rightarrow> y | _ \<Rightarrow> x W\<^sub>n y)"

definition mk_strong_release
where
  "mk_strong_release x y \<equiv> case y of false\<^sub>n \<Rightarrow> false\<^sub>n
    | true\<^sub>n \<Rightarrow> mk_finally x
    | _ \<Rightarrow> (case x of true\<^sub>n \<Rightarrow> y | false\<^sub>n \<Rightarrow> false\<^sub>n | _ \<Rightarrow> x M\<^sub>n y)"

definition mk_next
where
  "mk_next x \<equiv> case x of true\<^sub>n \<Rightarrow> true\<^sub>n | false\<^sub>n \<Rightarrow> false\<^sub>n | _ \<Rightarrow> X\<^sub>n x"

definition mk_next_pow ("X\<^sub>n''")
where
  "mk_next_pow n x \<equiv> case x of true\<^sub>n \<Rightarrow> true\<^sub>n | false\<^sub>n \<Rightarrow> false\<^sub>n | _ \<Rightarrow> (Next_ltln ^^ n) x"



lemma mk_and_semantics [simp]:
  "w \<Turnstile>\<^sub>n mk_and x y \<longleftrightarrow> w \<Turnstile>\<^sub>n x and\<^sub>n y"
  unfolding mk_and_def by (cases x; cases y; simp)

lemma mk_or_semantics [simp]:
  "w \<Turnstile>\<^sub>n mk_or x y \<longleftrightarrow> w \<Turnstile>\<^sub>n x or\<^sub>n y"
  unfolding mk_or_def by (cases x; cases y; simp)

lemma remove_strong_ops_sound [simp]:
  "w \<Turnstile>\<^sub>n F\<^sub>n (remove_strong_ops y) \<longleftrightarrow> w \<Turnstile>\<^sub>n F\<^sub>n y"
  by (induction y arbitrary: w) (auto; force)+

lemma remove_weak_ops_sound [simp]:
  "w \<Turnstile>\<^sub>n G\<^sub>n (remove_weak_ops y) \<longleftrightarrow> w \<Turnstile>\<^sub>n G\<^sub>n y"
  by (induction y arbitrary: w) (auto; force)+

lemma mk_finally_semantics [simp]:
  "w \<Turnstile>\<^sub>n mk_finally x \<longleftrightarrow> w \<Turnstile>\<^sub>n F\<^sub>n x"
  by (simp add: mk_finally_def del: semantics_ltln.simps(8,9) remove_strong_ops.simps split: ltln.splits)

lemma mk_globally_semantics [simp]:
  "w \<Turnstile>\<^sub>n mk_globally x \<longleftrightarrow> w \<Turnstile>\<^sub>n G\<^sub>n x"
  by (simp add: mk_globally_def del: semantics_ltln.simps(8,9) remove_weak_ops.simps split: ltln.splits)

lemma mk_until_semantics [simp]:
  "w \<Turnstile>\<^sub>n mk_until x y \<longleftrightarrow> w \<Turnstile>\<^sub>n x U\<^sub>n y"
proof (cases x)
  case (True_ltln)
    show ?thesis
      unfolding True_ltln mk_until_def
      by (cases y) auto
next
  case (False_ltln)
    thus ?thesis
      by (force simp: mk_until_def)
qed (cases y; force simp: mk_until_def)+

lemma mk_release_semantics [simp]:
  "w \<Turnstile>\<^sub>n mk_release x y \<longleftrightarrow> w \<Turnstile>\<^sub>n x R\<^sub>n y"
proof (cases x)
  case (False_ltln)
    thus ?thesis
      unfolding False_ltln mk_release_def
      by (cases y) auto
next
  case (True_ltln)
    thus ?thesis
      by (force simp: mk_release_def)
qed (cases y; force simp: mk_release_def)+

lemma mk_weak_until_semantics [simp]:
  "w \<Turnstile>\<^sub>n mk_weak_until x y \<longleftrightarrow> w \<Turnstile>\<^sub>n x W\<^sub>n y"
proof (cases y)
  case (False_ltln)
    thus ?thesis
      unfolding False_ltln mk_weak_until_def
      by (cases x) auto
next
  case (True_ltln)
    thus ?thesis
      by (force simp: mk_weak_until_def)
qed (cases x; force simp: mk_weak_until_def)+

lemma mk_strong_release_semantics [simp]:
  "w \<Turnstile>\<^sub>n mk_strong_release x y \<longleftrightarrow> w \<Turnstile>\<^sub>n x M\<^sub>n y"
proof (cases y)
  case (True_ltln)
    show ?thesis
      unfolding True_ltln mk_strong_release_def
      by (cases x) auto
next
  case (False_ltln)
    thus ?thesis
      by (force simp: mk_strong_release_def)
qed (cases x; force simp: mk_strong_release_def)+

lemma mk_next_semantics [simp]:
  "w \<Turnstile>\<^sub>n mk_next x \<longleftrightarrow> w \<Turnstile>\<^sub>n X\<^sub>n x"
  unfolding mk_next_def by (cases x; auto)

lemma mk_next_pow_semantics [simp]:
  "w \<Turnstile>\<^sub>n mk_next_pow i x \<longleftrightarrow> suffix i w \<Turnstile>\<^sub>n x"
  by (induction i arbitrary: w; cases x)
     (auto simp: mk_next_pow_def)

lemma mk_next_pow_simp [simp, code_unfold]:
  "mk_next_pow 0 x = x"
  "mk_next_pow 1 x = mk_next x"
  by (cases x; simp add: mk_next_pow_def mk_next_def)+



subsection \<open>Constant Propagation\<close>

fun is_constant :: "'a ltln \<Rightarrow> bool"
where
  "is_constant true\<^sub>n = True"
| "is_constant false\<^sub>n = True"
| "is_constant _ = False"

lemma is_constant_constructorsI:
  "is_constant x \<Longrightarrow> is_constant y \<Longrightarrow> is_constant (mk_and x y)"
  "\<not>is_constant x \<Longrightarrow> \<not>is_constant y \<Longrightarrow> \<not>is_constant (mk_and x y)"
  "is_constant x \<Longrightarrow> is_constant y \<Longrightarrow> is_constant (mk_or x y)"
  "\<not>is_constant x \<Longrightarrow> \<not>is_constant y \<Longrightarrow> \<not>is_constant (mk_or x y)"
  "is_constant x \<Longrightarrow>  is_constant (mk_finally x)"
  "\<not>is_constant x \<Longrightarrow>  \<not>is_constant (mk_finally x)"
  "is_constant x \<Longrightarrow> is_constant (mk_globally x)"
  "\<not>is_constant x \<Longrightarrow>  \<not>is_constant (mk_globally x)"
  "is_constant x \<Longrightarrow> is_constant (mk_until y x)"
  "\<not>is_constant x \<Longrightarrow> \<not>is_constant (mk_until y x)"
  "is_constant x \<Longrightarrow> is_constant (mk_release y x)"
  "\<not>is_constant x \<Longrightarrow> \<not>is_constant (mk_release y x)"
  "is_constant x \<Longrightarrow> is_constant y \<Longrightarrow> is_constant (mk_weak_until x y)"
  "\<not>is_constant x \<Longrightarrow> \<not>is_constant y \<Longrightarrow> \<not>is_constant (mk_weak_until x y)"
  "is_constant x \<Longrightarrow> is_constant y \<Longrightarrow> is_constant (mk_strong_release x y)"
  "\<not>is_constant x \<Longrightarrow> \<not>is_constant y \<Longrightarrow> \<not>is_constant (mk_strong_release x y)"
  "is_constant x \<Longrightarrow> is_constant (mk_next x)"
  "\<not>is_constant x \<Longrightarrow> \<not>is_constant (mk_next x)"
  "is_constant x \<Longrightarrow> is_constant (mk_next_pow n x)"
  by (cases x; cases y; simp add: mk_and_def mk_or_def mk_finally_def mk_globally_def mk_until_def mk_release_def mk_weak_until_def mk_strong_release_def mk_next_def mk_next_pow_def)+

lemma is_constant_constructors_simps:
  "mk_next_pow n x = false\<^sub>n \<longleftrightarrow> x = false\<^sub>n"
  "mk_next_pow n x = true\<^sub>n \<longleftrightarrow> x = true\<^sub>n"
  "is_constant (mk_next_pow n x) \<longleftrightarrow> is_constant x"
  by (induction n) (cases x; simp add: mk_next_pow_def)+

lemma is_constant_constructors_simps2:
  "is_constant (mk_and x y) \<longleftrightarrow> (x = true\<^sub>n \<and> y = true\<^sub>n \<or> x = false\<^sub>n \<or> y = false\<^sub>n)"
  "is_constant (mk_or x y) \<longleftrightarrow> (x = false\<^sub>n \<and> y = false\<^sub>n \<or> x = true\<^sub>n \<or> y = true\<^sub>n)"
  "is_constant (mk_finally x) \<longleftrightarrow> is_constant x"
  "is_constant (mk_globally x) \<longleftrightarrow> is_constant x"
  "is_constant (mk_until y x) \<longleftrightarrow> is_constant x"
  "is_constant (mk_release y x) \<longleftrightarrow> is_constant x"
  "is_constant (mk_next x) \<longleftrightarrow> is_constant x"
  by ((cases x; cases y; simp add: mk_and_def),
      (cases x; cases y; simp add: mk_or_def),
      (meson is_constant_constructorsI)+)

lemma is_constant_constructors_simps3:
  "is_constant (mk_weak_until x y) \<longleftrightarrow> (x = false\<^sub>n \<and> y = false\<^sub>n \<or> x = true\<^sub>n \<or> y = true\<^sub>n)"
  "is_constant (mk_strong_release x y) \<longleftrightarrow> (x = true\<^sub>n \<and> y = true\<^sub>n \<or> x = false\<^sub>n \<or> y = false\<^sub>n)"
  by (cases x; cases y; simp add: mk_weak_until_def mk_strong_release_def is_constant_constructors_simps2)+

lemma is_constant_semantics:
  "is_constant \<phi> \<Longrightarrow> ((\<forall>w. w \<Turnstile>\<^sub>n \<phi>) \<or> \<not>(\<exists>w. w \<Turnstile>\<^sub>n \<phi>))"
  by (cases \<phi>) auto

lemma until_constant_simp:
  "is_constant \<psi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<psi>"
  by (cases \<psi>) auto

lemma release_constant_simp:
  "is_constant \<psi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<psi>"
  by (cases \<psi>) auto

lemma mk_next_pow_dist:
  "mk_next_pow (i + j) \<phi> = mk_next_pow i (mk_next_pow j \<phi>)"
  by (cases j; simp) (cases \<phi>; simp add: mk_next_pow_def funpow_add; simp add: funpow_swap1)

lemma mk_next_pow_until:
  "suffix (min i j) w \<Turnstile>\<^sub>n (mk_next_pow (i - j) \<phi>) U\<^sub>n (mk_next_pow (j - i) \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n (mk_next_pow i \<phi>) U\<^sub>n (mk_next_pow j \<psi>)"
  by (simp add: mk_next_pow_dist min_def add.commute)

lemma mk_next_pow_release:
  "suffix (min i j) w \<Turnstile>\<^sub>n (mk_next_pow (i - j) \<phi>) R\<^sub>n (mk_next_pow (j - i) \<psi>) \<longleftrightarrow> w \<Turnstile>\<^sub>n (mk_next_pow i \<phi>) R\<^sub>n (mk_next_pow j \<psi>)"
  by (simp add: mk_next_pow_dist min_def add.commute)

subsection \<open>X-Normalisation\<close>

text \<open>The following rewrite functions pulls the X-operator up in the syntax tree. This preprocessing
  step enables the removal of X-operators in front of suspendable formulas. Furthermore constants are
  removed as far as possible.\<close>

fun the_enat_0 :: "enat \<Rightarrow> nat"
where
  "the_enat_0 i = i"
| "the_enat_0 \<infinity> = 0"

lemma the_enat_0_simp [simp]:
  "the_enat_0 0 = 0"
  "the_enat_0 1 = 1"
  by (simp add: zero_enat_def one_enat_def)+

fun combine :: "('a ltln \<Rightarrow> 'a ltln \<Rightarrow> 'a ltln) \<Rightarrow> ('a ltln * enat) \<Rightarrow> ('a ltln * enat) \<Rightarrow> ('a ltln * enat)"
where
  "combine binop (\<phi>, i) (\<psi>, j) = (
    let
      \<chi> = binop (mk_next_pow (the_enat_0 (i - j)) \<phi>) (mk_next_pow (the_enat_0 (j - i)) \<psi>)
    in
      (\<chi>, if is_constant \<chi> then \<infinity> else min i j))"

lemma fst_combine:
  "fst (combine binop (\<phi>, i) (\<psi>, j)) = binop (mk_next_pow (the_enat_0 (i - j)) \<phi>) (mk_next_pow (the_enat_0 (j - i)) \<psi>)"
  unfolding combine.simps by (meson fstI)

abbreviation to_ltln :: "('a ltln * enat) \<Rightarrow> 'a ltln"
where
  "to_ltln x \<equiv> mk_next_pow (the_enat_0 (snd x)) (fst x)"

fun rewrite_X_enat :: "'a ltln \<Rightarrow> ('a ltln * enat)"
where
  "rewrite_X_enat true\<^sub>n = (true\<^sub>n, \<infinity>)"
| "rewrite_X_enat false\<^sub>n = (false\<^sub>n, \<infinity>)"
| "rewrite_X_enat prop\<^sub>n(a) = (prop\<^sub>n(a), 0)"
| "rewrite_X_enat nprop\<^sub>n(a) = (nprop\<^sub>n(a), 0)"
| "rewrite_X_enat (\<phi> and\<^sub>n \<psi>) = combine mk_and (rewrite_X_enat \<phi>) (rewrite_X_enat \<psi>)"
| "rewrite_X_enat (\<phi> or\<^sub>n \<psi>) = combine mk_or (rewrite_X_enat \<phi>) (rewrite_X_enat \<psi>)"
| "rewrite_X_enat (\<phi> U\<^sub>n \<psi>) = combine mk_until (rewrite_X_enat \<phi>) (rewrite_X_enat \<psi>)"
| "rewrite_X_enat (\<phi> R\<^sub>n \<psi>) = combine mk_release (rewrite_X_enat \<phi>) (rewrite_X_enat \<psi>)"
| "rewrite_X_enat (\<phi> W\<^sub>n \<psi>) = combine mk_weak_until (rewrite_X_enat \<phi>) (rewrite_X_enat \<psi>)"
| "rewrite_X_enat (\<phi> M\<^sub>n \<psi>) = combine mk_strong_release (rewrite_X_enat \<phi>) (rewrite_X_enat \<psi>)"
| "rewrite_X_enat (X\<^sub>n \<phi>) = (\<lambda>(\<phi>, n). (\<phi>, eSuc n)) (rewrite_X_enat \<phi>)"

definition
  "rewrite_X \<phi> = to_ltln (rewrite_X_enat \<phi>)"

lemma combine_infinity_invariant:
  assumes "i = \<infinity> \<longleftrightarrow> is_constant x"
  assumes "j = \<infinity> \<longleftrightarrow> is_constant y"
  shows "combine mk_and (x, i) (y, j) = (z, k) \<Longrightarrow> (k = \<infinity> \<longleftrightarrow> is_constant z)"
    and "combine mk_or (x, i) (y, j) = (z, k) \<Longrightarrow> (k = \<infinity> \<longleftrightarrow> is_constant z)"
    and "combine mk_until (x, i) (y, j) = (z, k) \<Longrightarrow> (k = \<infinity> \<longleftrightarrow> is_constant z)"
    and "combine mk_release (x, i) (y, j) = (z, k) \<Longrightarrow> (k = \<infinity> \<longleftrightarrow> is_constant z)"
    and "combine mk_weak_until (x, i) (y, j) = (z, k) \<Longrightarrow> (k = \<infinity> \<longleftrightarrow> is_constant z)"
    and "combine mk_strong_release (x, i) (y, j) = (z, k) \<Longrightarrow> (k = \<infinity> \<longleftrightarrow> is_constant z)"
  by (cases i; cases j; simp add: assms Let_def; force intro: is_constant_constructorsI)+

lemma combine_and_or_semantics:
  assumes "i = \<infinity> \<longleftrightarrow> is_constant \<phi>"
  assumes "j = \<infinity> \<longleftrightarrow> is_constant \<psi>"
  shows "w \<Turnstile>\<^sub>n to_ltln (combine mk_and (\<phi>, i) (\<psi>, j)) \<longleftrightarrow> w \<Turnstile>\<^sub>n to_ltln (\<phi>, i) and\<^sub>n to_ltln (\<psi>, j)"
    and "w \<Turnstile>\<^sub>n to_ltln (combine mk_or (\<phi>, i) (\<psi>, j)) \<longleftrightarrow> w \<Turnstile>\<^sub>n to_ltln (\<phi>, i) or\<^sub>n to_ltln (\<psi>, j)"
  by ((cases i; cases j; simp add: min_def is_constant_constructors_simps is_constant_constructors_simps2 assms),
      (cases \<psi>; insert assms; auto),
      (cases \<phi>; insert assms; auto),
      (blast elim!: is_constant.elims))+

lemma combine_until_release_semantics:
  assumes "i = \<infinity> \<longleftrightarrow> is_constant \<phi>"
  assumes "j = \<infinity> \<longleftrightarrow> is_constant \<psi>"
  shows "w \<Turnstile>\<^sub>n to_ltln (combine mk_until (\<phi>, i) (\<psi>, j)) \<longleftrightarrow> w \<Turnstile>\<^sub>n to_ltln (\<phi>, i) U\<^sub>n to_ltln (\<psi>, j)"
    and "w \<Turnstile>\<^sub>n to_ltln (combine mk_release (\<phi>, i) (\<psi>, j)) \<longleftrightarrow> w \<Turnstile>\<^sub>n to_ltln (\<phi>, i) R\<^sub>n to_ltln (\<psi>, j)"
  by ((cases i; cases j; simp add: is_constant_constructors_simps is_constant_constructors_simps2
       until_constant_simp release_constant_simp mk_next_pow_until mk_next_pow_release del: semantics_ltln.simps),
      (blast dest: is_constant_semantics),
      (cases \<psi>; simp add: assms),
      (cases \<phi>; insert assms; auto simp: add.commute))+

(* TODO this proof is a bit slow and could be optimized *)
lemma combine_weak_until_strong_release_semantics:
  assumes "i = \<infinity> \<longleftrightarrow> is_constant \<phi>"
  assumes "j = \<infinity> \<longleftrightarrow> is_constant \<psi>"
  shows "w \<Turnstile>\<^sub>n to_ltln (combine mk_weak_until (\<phi>, i) (\<psi>, j)) \<longleftrightarrow> w \<Turnstile>\<^sub>n to_ltln (\<phi>, i) W\<^sub>n to_ltln (\<psi>, j)"
    and "w \<Turnstile>\<^sub>n to_ltln (combine mk_strong_release (\<phi>, i) (\<psi>, j)) \<longleftrightarrow> w \<Turnstile>\<^sub>n to_ltln (\<phi>, i) M\<^sub>n to_ltln (\<psi>, j)"
  by ((cases i; cases j; simp add: min_def is_constant_constructors_simps is_constant_constructors_simps3 del: semantics_ltln.simps),
      (cases \<phi>; simp add: assms),
      (cases \<psi>; insert assms; auto simp: add.commute))+



lemma rewrite_X_enat_infinity_invariant:
  "snd (rewrite_X_enat \<phi>) = \<infinity> \<longleftrightarrow> is_constant (fst (rewrite_X_enat \<phi>))"
proof (induction \<phi>)
  case (And_ltln \<phi> \<psi>)
    thus ?case
      by (simp add: combine_infinity_invariant[OF And_ltln(1,2), unfolded prod.collapse])
next
  case (Or_ltln \<phi> \<psi>)
    thus ?case
      by (simp add: combine_infinity_invariant[OF Or_ltln(1,2), unfolded prod.collapse])
next
  case (Until_ltln \<phi> \<psi>)
    thus ?case
      by (simp add: combine_infinity_invariant[OF Until_ltln(1,2), unfolded prod.collapse])
next
  case (Release_ltln \<phi> \<psi>)
    thus ?case
      by (simp add: combine_infinity_invariant[OF Release_ltln(1,2), unfolded prod.collapse])
next
  case (WeakUntil_ltln \<phi> \<psi>)
    thus ?case
      by (simp add: combine_infinity_invariant[OF WeakUntil_ltln(1,2), unfolded prod.collapse])
next
  case (StrongRelease_ltln \<phi> \<psi>)
    thus ?case
      by (simp add: combine_infinity_invariant[OF StrongRelease_ltln(1,2), unfolded prod.collapse])
next
  case (Next_ltln \<phi>)
    thus ?case
      by (simp add: split_def) (metis eSuc_infinity eSuc_inject)
qed auto

lemma rewrite_X_enat_correct:
  "w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n to_ltln (rewrite_X_enat \<phi>)"
proof (induction \<phi> arbitrary: w)
  case (And_ltln \<phi> \<psi>)
    thus ?case
      using combine_and_or_semantics[OF rewrite_X_enat_infinity_invariant rewrite_X_enat_infinity_invariant] by fastforce
next
  case (Or_ltln \<phi> \<psi>)
    thus ?case
      using combine_and_or_semantics[OF rewrite_X_enat_infinity_invariant rewrite_X_enat_infinity_invariant] by fastforce
next
  case (Until_ltln \<phi> \<psi>)
    thus ?case
      unfolding rewrite_X_enat.simps combine_until_release_semantics[OF rewrite_X_enat_infinity_invariant rewrite_X_enat_infinity_invariant, unfolded prod.collapse] by fastforce
next
  case (Release_ltln \<phi> \<psi>)
    thus ?case
      unfolding rewrite_X_enat.simps combine_until_release_semantics[OF rewrite_X_enat_infinity_invariant rewrite_X_enat_infinity_invariant, unfolded prod.collapse] by fastforce
next
  case (WeakUntil_ltln \<phi> \<psi>)
    thus ?case
      unfolding rewrite_X_enat.simps combine_weak_until_strong_release_semantics[OF rewrite_X_enat_infinity_invariant rewrite_X_enat_infinity_invariant, unfolded prod.collapse] by fastforce
next
  case (StrongRelease_ltln \<phi> \<psi>)
    thus ?case
      unfolding rewrite_X_enat.simps combine_weak_until_strong_release_semantics[OF rewrite_X_enat_infinity_invariant rewrite_X_enat_infinity_invariant, unfolded prod.collapse] by fastforce
next
  case (Next_ltln \<phi>)
  moreover
    have " w \<Turnstile>\<^sub>n to_ltln (rewrite_X_enat (X\<^sub>n \<phi>)) \<longleftrightarrow> suffix 1 w \<Turnstile>\<^sub>n to_ltln (rewrite_X_enat \<phi>)"
      by (simp add: split_def; cases "snd (rewrite_X_enat \<phi>) \<noteq> \<infinity>")
         (auto simp: eSuc_def, auto simp: rewrite_X_enat_infinity_invariant eSuc_def dest: is_constant_semantics)
    ultimately
    show ?case
       using semantics_ltln.simps(7) by blast
qed auto

lemma rewrite_X_sound [simp]:
  "w \<Turnstile>\<^sub>n rewrite_X \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  using rewrite_X_enat_correct unfolding rewrite_X_def Let_def by auto

subsection \<open>Pure Eventual, Pure Universal, and Suspendable Formulas\<close>

fun pure_eventual :: "'a ltln \<Rightarrow> bool"
where
  "pure_eventual true\<^sub>n = True"
| "pure_eventual false\<^sub>n = True"
| "pure_eventual (\<mu> and\<^sub>n \<mu>') = (pure_eventual \<mu> \<and> pure_eventual \<mu>')"
| "pure_eventual (\<mu> or\<^sub>n \<mu>') = (pure_eventual \<mu> \<and> pure_eventual \<mu>')"
| "pure_eventual (\<mu> U\<^sub>n \<mu>') = (\<mu> = true\<^sub>n \<or> pure_eventual \<mu>')"
| "pure_eventual (\<mu> R\<^sub>n \<mu>') = (pure_eventual \<mu> \<and> pure_eventual \<mu>')"
| "pure_eventual (\<mu> W\<^sub>n \<mu>') = (pure_eventual \<mu> \<and> pure_eventual \<mu>')"
| "pure_eventual (\<mu> M\<^sub>n \<mu>') = (pure_eventual \<mu> \<and> pure_eventual \<mu>' \<or> \<mu>' = true\<^sub>n)"
| "pure_eventual (X\<^sub>n \<mu>) = pure_eventual \<mu>"
| "pure_eventual _ = False"

fun pure_universal :: "'a ltln \<Rightarrow> bool"
where
  "pure_universal true\<^sub>n = True"
| "pure_universal false\<^sub>n = True"
| "pure_universal (\<nu> and\<^sub>n \<nu>') = (pure_universal \<nu> \<and> pure_universal \<nu>')"
| "pure_universal (\<nu> or\<^sub>n \<nu>') = (pure_universal \<nu> \<and> pure_universal \<nu>')"
| "pure_universal (\<nu> U\<^sub>n \<nu>') = (pure_universal \<nu> \<and> pure_universal \<nu>')"
| "pure_universal (\<nu> R\<^sub>n \<nu>') = (\<nu> = false\<^sub>n \<or> pure_universal \<nu>')"
| "pure_universal (\<nu> W\<^sub>n \<nu>') = (pure_universal \<nu> \<and> pure_universal \<nu>' \<or> \<nu>' = false\<^sub>n)"
| "pure_universal (\<nu> M\<^sub>n \<nu>') = (pure_universal \<nu> \<and> pure_universal \<nu>')"
| "pure_universal (X\<^sub>n \<nu>) = pure_universal \<nu>"
| "pure_universal _ = False"

fun suspendable :: "'a ltln \<Rightarrow> bool"
where
  "suspendable true\<^sub>n = True"
| "suspendable false\<^sub>n = True"
| "suspendable (\<xi> and\<^sub>n \<xi>') = (suspendable \<xi> \<and> suspendable \<xi>')"
| "suspendable (\<xi> or\<^sub>n \<xi>') = (suspendable \<xi> \<and> suspendable \<xi>')"
| "suspendable (\<phi> U\<^sub>n \<xi>) = (\<phi> = true\<^sub>n \<and> pure_universal \<xi> \<or> suspendable \<xi>)"
| "suspendable (\<phi> R\<^sub>n \<xi>) = (\<phi> = false\<^sub>n \<and> pure_eventual \<xi> \<or> suspendable \<xi>)"
| "suspendable (\<phi> W\<^sub>n \<xi>) = (suspendable \<phi> \<and> suspendable \<xi> \<or> pure_eventual \<phi> \<and> \<xi> = false\<^sub>n)"
| "suspendable (\<phi> M\<^sub>n \<xi>) = (suspendable \<phi> \<and> suspendable \<xi> \<or> pure_universal \<phi> \<and> \<xi> = true\<^sub>n)"
| "suspendable (X\<^sub>n \<xi>) = suspendable \<xi>"
| "suspendable _ = False"

lemma pure_eventual_left_append:
  "pure_eventual \<mu> \<Longrightarrow> w \<Turnstile>\<^sub>n \<mu> \<Longrightarrow> (u \<frown> w) \<Turnstile>\<^sub>n \<mu>"
proof (induction \<mu> arbitrary: u w)
  case (Until_ltln \<mu> \<mu>')
    moreover
    then obtain i where "suffix i w \<Turnstile>\<^sub>n \<mu>'"
      by auto
    hence "\<mu> = true\<^sub>n \<Longrightarrow> ?case"
      by simp (metis suffix_conc_length suffix_suffix)
    moreover
    have "pure_eventual \<mu>' \<Longrightarrow> (u \<frown> w) \<Turnstile>\<^sub>n \<mu>'"
      by (metis \<open>suffix i w \<Turnstile>\<^sub>n \<mu>'\<close> Until_ltln(2) prefix_suffix)
    hence "pure_eventual \<mu>' \<Longrightarrow> ?case"
      by force
    ultimately
    show ?case
      by fastforce
next
  case (Release_ltln \<mu> \<mu>')
    thus ?case
      by (cases "\<forall>i. suffix i w \<Turnstile>\<^sub>n \<mu>'"; simp_all)
         (metis linear suffix_conc_snd gr0I not_less0 prefix_suffix suffix_0)+
next
  case (WeakUntil_ltln \<mu> \<mu>')
    thus ?case
      by (cases "\<forall>i. suffix i w \<Turnstile>\<^sub>n \<mu>'"; simp_all)
         (metis zero_le le0 nat_le_linear prefix_suffix suffix_0 suffix_conc_length suffix_conc_snd suffix_subseq_join)+
next
  case (StrongRelease_ltln \<mu> \<mu>')
    moreover
    then obtain i where "suffix i w \<Turnstile>\<^sub>n \<mu> and\<^sub>n \<mu>'"
      by auto
    hence "\<mu>' = true\<^sub>n \<Longrightarrow> ?case"
      by simp (metis suffix_conc_length suffix_suffix)
    moreover
    have "pure_eventual \<mu> \<Longrightarrow> pure_eventual \<mu>' \<Longrightarrow> (u \<frown> w) \<Turnstile>\<^sub>n \<mu> and\<^sub>n \<mu>'"
      by (metis \<open>suffix i w \<Turnstile>\<^sub>n \<mu> and\<^sub>n \<mu>'\<close> calculation(1) calculation(2) prefix_suffix semantics_ltln.simps(5))
    hence "pure_eventual \<mu> \<Longrightarrow> pure_eventual \<mu>' \<Longrightarrow> ?case"
      by force
    ultimately
    show ?case
      by fastforce
qed (auto, metis diff_zero le_0_eq not_less_eq_eq suffix_conc_length suffix_conc_snd word_split)

lemma pure_universal_suffix_closed:
  "pure_universal \<nu> \<Longrightarrow> (u \<frown> w) \<Turnstile>\<^sub>n \<nu> \<Longrightarrow> w \<Turnstile>\<^sub>n \<nu>"
proof (induction \<nu> arbitrary: u w)
  case (Until_ltln \<nu> \<nu>')
    hence "\<exists>i. suffix i (u \<frown> w) \<Turnstile>\<^sub>n \<nu>' \<and> (\<forall>j<i. suffix j (u \<frown> w) \<Turnstile>\<^sub>n \<nu>)"
      using semantics_ltln.simps(8) by blast
    thus ?case
      by simp (metis Until_ltln(1-3) le_0_eq le_eq_less_or_eq le_less_linear prefix_suffix pure_universal.simps(5) suffix_conc_fst suffix_conc_snd)
next
  case (Release_ltln \<nu> \<nu>')
    moreover
    hence "\<forall>i. suffix i (u \<frown> w) \<Turnstile>\<^sub>n \<nu>' \<or> (\<exists>j<i. suffix j (u \<frown> w) \<Turnstile>\<^sub>n \<nu>)"
      by simp
    ultimately
    show ?case
      by simp (metis semantics_ltln.simps(2) not_less0 prefix_suffix suffix_0 suffix_conc_length suffix_suffix)
next
  case (WeakUntil_ltln \<nu> \<nu>')
    moreover
    hence "\<forall>i. suffix i (u \<frown> w) \<Turnstile>\<^sub>n \<nu> \<or> (\<exists>j\<le>i. suffix j (u \<frown> w) \<Turnstile>\<^sub>n \<nu>')"
      by simp
    ultimately
    show ?case
      by simp (metis (full_types) le_antisym prefix_suffix semantics_ltln.simps(2) suffix_0 suffix_conc_length suffix_suffix zero_le)
next
  case (StrongRelease_ltln \<nu> \<nu>')
    hence "\<exists>i. suffix i (u \<frown> w) \<Turnstile>\<^sub>n \<nu> \<and> (\<forall>j\<le>i. suffix j (u \<frown> w) \<Turnstile>\<^sub>n \<nu>')"
      using semantics_ltln.simps(11) by blast
    thus ?case
      by simp (metis StrongRelease_ltln(1-3) diff_is_0_eq nat_le_linear prefix_conc_length prefix_suffix pure_universal.simps(8) subsequence_length suffix_conc_snd suffix_subseq_join)
next
  case (Next_ltln \<mu>)
    thus ?case
      by (metis prefix_suffix pure_universal.simps(9) semantics_ltln.simps(7) semiring_normalization_rules(24) suffix_conc_length suffix_suffix)
qed auto

lemma suspendable_prefix_invariant:
  "suspendable \<xi> \<Longrightarrow> (u \<frown> w) \<Turnstile>\<^sub>n \<xi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<xi>"
proof (induction \<xi> arbitrary: u w)
  case (Until_ltln \<xi> \<xi>')
    show ?case
    proof (cases "suspendable \<xi>'")
      case False
        hence "\<xi> = true\<^sub>n" and "pure_universal \<xi>'"
          using Until_ltln by simp+
        thus ?thesis
          by (simp; metis (no_types) linear pure_universal_suffix_closed suffix_conc_fst suffix_conc_length suffix_conc_snd suffix_suffix)
    qed (simp; metis Until_ltln(2) not_less0 prefix_suffix)
next
  case (Release_ltln \<xi> \<xi>')
    show ?case
    proof (cases "suspendable \<xi>'")
      case False
        hence "\<xi> = false\<^sub>n" and "pure_eventual \<xi>'"
          using Release_ltln by simp+
        thus ?thesis
          by (simp; metis (no_types) le_iff_add add_diff_cancel_left' linear pure_eventual_left_append suffix_0 suffix_conc_fst suffix_conc_snd)
    qed (simp; metis Release_ltln(2) not_less0 prefix_suffix)
next
  case (WeakUntil_ltln \<xi> \<xi>')
    show ?case
    proof (cases "suspendable \<xi> \<and> suspendable \<xi>'")
      case False
        hence "\<xi>' = false\<^sub>n" and "pure_eventual \<xi>"
          using WeakUntil_ltln by simp+
        thus ?thesis
          by (simp; metis (no_types) le_iff_add add_diff_cancel_left' linear pure_eventual_left_append suffix_0 suffix_conc_fst suffix_conc_snd)
      qed (simp; metis (full_types) WeakUntil_ltln.IH prefix_suffix)
next
  case (StrongRelease_ltln \<xi> \<xi>')
    show ?case
    proof (cases "suspendable \<xi> \<and> suspendable \<xi>'")
      case False
        hence "\<xi>' = true\<^sub>n" and "pure_universal \<xi>"
          using StrongRelease_ltln by simp+
        thus ?thesis
          by (simp; metis (no_types) linear pure_universal_suffix_closed suffix_conc_fst suffix_conc_length suffix_conc_snd suffix_suffix)
    qed (simp; metis (full_types) StrongRelease_ltln.IH(1) StrongRelease_ltln.IH(2) prefix_suffix)
qed (simp_all, metis prefix_suffix)

theorem pure_eventual_until_simp:
  assumes "pure_eventual \<mu>"
  shows "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<mu> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<mu>"
proof -
  have "\<And>i. suffix i w \<Turnstile>\<^sub>n \<mu> \<Longrightarrow> w \<Turnstile>\<^sub>n \<mu>"
    using pure_eventual_left_append[OF assms] prefix_suffix by metis
  thus ?thesis
    by force
qed

theorem pure_universal_release_simp:
  assumes "pure_universal \<nu>"
  shows "w \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<nu> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<nu>"
proof -
  have "\<And>i. w \<Turnstile>\<^sub>n \<nu> \<Longrightarrow> suffix i w \<Turnstile>\<^sub>n \<nu>"
    using pure_universal_suffix_closed[OF assms] prefix_suffix by metis
  thus ?thesis
    by force
qed

theorem pure_universal_weak_until_simp:
  assumes "pure_universal \<phi>" and "pure_universal \<psi>"
  shows "w \<Turnstile>\<^sub>n \<phi> W\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi> or\<^sub>n \<psi>"
proof -
  have "\<And>i. w \<Turnstile>\<^sub>n \<phi> \<Longrightarrow> suffix i w \<Turnstile>\<^sub>n \<phi>" and "\<And>i. w \<Turnstile>\<^sub>n \<psi> \<Longrightarrow> suffix i w \<Turnstile>\<^sub>n \<psi>"
    using assms pure_universal_suffix_closed prefix_suffix by metis+
  thus ?thesis
    by force
qed

theorem pure_eventual_strong_release_simp:
  assumes "pure_eventual \<phi>" and "pure_eventual \<psi>"
  shows "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi> and\<^sub>n \<psi>"
proof -
  have "\<And>i. suffix i w \<Turnstile>\<^sub>n \<phi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi>" and "\<And>i. suffix i w \<Turnstile>\<^sub>n \<psi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<psi>"
    using assms pure_eventual_left_append prefix_suffix by metis+
  thus ?thesis
    by force
qed


theorem suspendable_formula_simp:
  assumes "suspendable \<xi>"
  shows "w \<Turnstile>\<^sub>n X\<^sub>n \<xi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<xi>" (is ?t1)
    and "w \<Turnstile>\<^sub>n \<phi> U\<^sub>n \<xi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<xi>" (is ?t2)
    and "w \<Turnstile>\<^sub>n \<phi> R\<^sub>n \<xi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<xi>" (is ?t3)
proof -
  have "\<And>i. suffix i w \<Turnstile>\<^sub>n \<xi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<xi>"
    using suspendable_prefix_invariant[OF assms] prefix_suffix by metis
  thus ?t1 ?t2 ?t3
    by force+
qed

theorem suspendable_formula_simp2:
  assumes "suspendable \<phi>" and "suspendable \<psi>"
  shows "w \<Turnstile>\<^sub>n \<phi> W\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi> or\<^sub>n \<psi>" (is ?t1)
    and "w \<Turnstile>\<^sub>n \<phi> M\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi> and\<^sub>n \<psi>" (is ?t2)
proof -
  have "\<And>i. suffix i w \<Turnstile>\<^sub>n \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>" and "\<And>i. suffix i w \<Turnstile>\<^sub>n \<psi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<psi>"
    using assms suspendable_prefix_invariant prefix_suffix by metis+
  thus ?t1 ?t2
    by force+
qed

fun rewrite_modal :: "'a ltln \<Rightarrow> 'a ltln"
where
  "rewrite_modal true\<^sub>n = true\<^sub>n"
| "rewrite_modal false\<^sub>n = false\<^sub>n"
| "rewrite_modal (\<phi> and\<^sub>n \<psi>) = (rewrite_modal \<phi> and\<^sub>n rewrite_modal \<psi>)"
| "rewrite_modal (\<phi> or\<^sub>n \<psi>) = (rewrite_modal \<phi> or\<^sub>n rewrite_modal \<psi>)"
| "rewrite_modal (\<phi> U\<^sub>n \<psi>) = (if pure_eventual \<psi> \<or> suspendable \<psi> then rewrite_modal \<psi> else (rewrite_modal \<phi> U\<^sub>n rewrite_modal \<psi>))"
| "rewrite_modal (\<phi> R\<^sub>n \<psi>) = (if pure_universal \<psi> \<or> suspendable \<psi> then rewrite_modal \<psi> else (rewrite_modal \<phi> R\<^sub>n rewrite_modal \<psi>))"
| "rewrite_modal (\<phi> W\<^sub>n \<psi>) = (if pure_universal \<phi> \<and> pure_universal \<psi> \<or> suspendable \<phi> \<and> suspendable \<psi> then (rewrite_modal \<phi> or\<^sub>n rewrite_modal \<psi>) else (rewrite_modal \<phi> W\<^sub>n rewrite_modal \<psi>))"
| "rewrite_modal (\<phi> M\<^sub>n \<psi>) = (if pure_eventual \<phi> \<and> pure_eventual \<psi> \<or> suspendable \<phi> \<and> suspendable \<psi> then (rewrite_modal \<phi> and\<^sub>n rewrite_modal \<psi>) else (rewrite_modal \<phi> M\<^sub>n rewrite_modal \<psi>))"
| "rewrite_modal (X\<^sub>n \<phi>) = (if suspendable \<phi> then rewrite_modal \<phi> else X\<^sub>n (rewrite_modal \<phi>))"
| "rewrite_modal \<phi> = \<phi>"

lemma rewrite_modal_sound [simp]:
  "w \<Turnstile>\<^sub>n rewrite_modal \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof (induction \<phi> arbitrary: w)
  case (Until_ltln \<phi> \<psi>)
    thus ?case
      apply (cases "pure_eventual \<psi> \<or> suspendable \<psi>")
      apply (insert pure_eventual_until_simp[of \<psi>] suspendable_formula_simp[of \<psi>])
      apply fastforce+
      done
next
  case (Release_ltln \<phi> \<psi>)
    thus ?case
      apply (cases "pure_universal \<psi> \<or> suspendable \<psi>")
      apply (insert pure_universal_release_simp[of \<psi>] suspendable_formula_simp[of \<psi>])
      apply fastforce+
      done
next
  case (WeakUntil_ltln \<phi> \<psi>)
    thus ?case
      apply (cases "pure_universal \<phi> \<and> pure_universal \<psi> \<or> suspendable \<phi> \<and> suspendable \<psi>")
      apply (insert pure_universal_weak_until_simp[of \<phi> \<psi>] suspendable_formula_simp2[of \<phi> \<psi>])
      apply fastforce+
      done
next
  case (StrongRelease_ltln \<phi> \<psi>)
    thus ?case
      apply (cases "pure_eventual \<phi> \<and> pure_eventual \<psi> \<or> suspendable \<phi> \<and> suspendable \<psi>")
      apply (insert pure_eventual_strong_release_simp[of \<phi> \<psi>] suspendable_formula_simp2[of \<phi> \<psi>])
      apply fastforce+
      done
next
  case (Next_ltln \<phi>)
    thus ?case
      apply (cases "suspendable \<phi>")
      apply (insert suspendable_formula_simp[of \<phi>])
      apply fastforce+
      done
qed auto

lemma rewrite_modal_size:
  "size (rewrite_modal \<phi>) \<le> size \<phi>"
  by (induction \<phi>) auto

subsection \<open>Syntactical Implication Based Simplification\<close>

inductive syntactical_implies :: "'a ltln \<Rightarrow> 'a ltln \<Rightarrow> bool" ("_ \<turnstile>\<^sub>s _" [80, 80])
where
  "_ \<turnstile>\<^sub>s true\<^sub>n"
| "false\<^sub>n \<turnstile>\<^sub>s _"
| "\<phi> = \<phi> \<Longrightarrow> \<phi> \<turnstile>\<^sub>s \<phi>"

| "\<phi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> (\<phi> and\<^sub>n \<psi>) \<turnstile>\<^sub>s \<chi>"
| "\<psi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> (\<phi> and\<^sub>n \<psi>) \<turnstile>\<^sub>s \<chi>"
| "\<phi> \<turnstile>\<^sub>s \<psi> \<Longrightarrow> \<phi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> \<phi> \<turnstile>\<^sub>s (\<psi> and\<^sub>n \<chi>)"

| "\<phi> \<turnstile>\<^sub>s \<psi> \<Longrightarrow> \<phi> \<turnstile>\<^sub>s (\<psi> or\<^sub>n \<chi>)"
| "\<phi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> \<phi> \<turnstile>\<^sub>s (\<psi> or\<^sub>n \<chi>)"
| "\<phi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> \<psi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> (\<phi> or\<^sub>n \<psi>) \<turnstile>\<^sub>s \<chi>"

| "\<phi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> \<phi> \<turnstile>\<^sub>s (\<psi> U\<^sub>n \<chi>)"
| "\<phi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> \<psi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> (\<phi> U\<^sub>n \<psi>) \<turnstile>\<^sub>s \<chi>"
| "\<phi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> \<psi> \<turnstile>\<^sub>s \<nu> \<Longrightarrow> (\<phi> U\<^sub>n \<psi>) \<turnstile>\<^sub>s (\<chi> U\<^sub>n \<nu>)"

| "\<chi> \<turnstile>\<^sub>s \<phi> \<Longrightarrow> (\<psi> R\<^sub>n \<chi>) \<turnstile>\<^sub>s \<phi>"
| "\<chi> \<turnstile>\<^sub>s \<phi> \<Longrightarrow> \<chi> \<turnstile>\<^sub>s \<psi> \<Longrightarrow> \<chi> \<turnstile>\<^sub>s (\<phi> R\<^sub>n \<psi>)"
| "\<phi> \<turnstile>\<^sub>s \<chi> \<Longrightarrow> \<psi> \<turnstile>\<^sub>s \<nu> \<Longrightarrow> (\<phi> R\<^sub>n \<psi>) \<turnstile>\<^sub>s (\<chi> R\<^sub>n \<nu>)"

| "(false\<^sub>n R\<^sub>n \<phi>) \<turnstile>\<^sub>s \<psi> \<Longrightarrow> (false\<^sub>n R\<^sub>n \<phi>) \<turnstile>\<^sub>s X\<^sub>n \<psi>"
| "\<phi> \<turnstile>\<^sub>s (true\<^sub>n U\<^sub>n \<psi>) \<Longrightarrow> (X\<^sub>n \<phi>) \<turnstile>\<^sub>s (true\<^sub>n U\<^sub>n \<psi>)"
| "\<phi> \<turnstile>\<^sub>s \<psi> \<Longrightarrow> (X\<^sub>n \<phi>) \<turnstile>\<^sub>s (X\<^sub>n \<psi>)"

lemma syntactical_implies_correct:
  "\<phi> \<turnstile>\<^sub>s \<psi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<phi> \<Longrightarrow> w \<Turnstile>\<^sub>n \<psi>"
  by (induction arbitrary: w rule: syntactical_implies.induct; auto; force)

fun rewrite_syn_imp
where
  "rewrite_syn_imp (\<phi> and\<^sub>n \<psi>) = (
    if \<phi> \<turnstile>\<^sub>s \<psi> then
      rewrite_syn_imp \<phi>
    else if \<psi> \<turnstile>\<^sub>s \<phi> then
      rewrite_syn_imp \<psi>
    else if \<phi> \<turnstile>\<^sub>s (not\<^sub>n \<psi>) \<or> \<psi> \<turnstile>\<^sub>s (not\<^sub>n \<phi>) then
      false\<^sub>n
    else
      mk_and (rewrite_syn_imp \<phi>) (rewrite_syn_imp \<psi>))"
| "rewrite_syn_imp (\<phi> or\<^sub>n \<psi>) = (
    if \<phi> \<turnstile>\<^sub>s \<psi> then
      rewrite_syn_imp \<psi>
    else if \<psi> \<turnstile>\<^sub>s \<phi> then
      rewrite_syn_imp \<phi>
    else if (not\<^sub>n \<phi>) \<turnstile>\<^sub>s \<psi> \<or> (not\<^sub>n \<psi>) \<turnstile>\<^sub>s \<phi> then
      true\<^sub>n
    else
      mk_or (rewrite_syn_imp \<phi>) (rewrite_syn_imp \<psi>))"
| "rewrite_syn_imp (\<phi> U\<^sub>n \<psi>) = (
    if \<phi> \<turnstile>\<^sub>s \<psi> then
      rewrite_syn_imp \<psi>
    else if (not\<^sub>n \<phi>) \<turnstile>\<^sub>s \<psi> then
      mk_finally (rewrite_syn_imp \<psi>)
    else
      mk_until (rewrite_syn_imp \<phi>) (rewrite_syn_imp \<psi>))"
| "rewrite_syn_imp (\<phi> R\<^sub>n \<psi>) = (
    if \<psi> \<turnstile>\<^sub>s \<phi> then
      rewrite_syn_imp \<psi>
    else if \<psi> \<turnstile>\<^sub>s (not\<^sub>n \<phi>) then
      mk_globally (rewrite_syn_imp \<psi>)
    else
      mk_release (rewrite_syn_imp \<phi>) (rewrite_syn_imp \<psi>))"
| "rewrite_syn_imp (X\<^sub>n \<phi>) = mk_next (rewrite_syn_imp \<phi>)"
| "rewrite_syn_imp \<phi> = \<phi>"

lemma rewrite_syn_imp_sound:
  "w \<Turnstile>\<^sub>n rewrite_syn_imp \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
proof (induction \<phi> arbitrary: w)
  case And_ltln
    thus ?case
      by (simp add: Let_def; metis syntactical_implies_correct not\<^sub>n_semantics)
next
  case (Or_ltln \<phi> \<psi>)
    moreover
    have "(not\<^sub>n \<phi>) \<turnstile>\<^sub>s \<psi> \<Longrightarrow> \<forall>w. w \<Turnstile>\<^sub>n \<phi> or\<^sub>n \<psi>"
      by (auto intro: syntactical_implies_correct[of "not\<^sub>n \<phi>"])
    moreover
    have "(not\<^sub>n \<psi>) \<turnstile>\<^sub>s \<phi> \<Longrightarrow> \<forall>w. w \<Turnstile>\<^sub>n \<phi> or\<^sub>n \<psi>"
      by (auto intro: syntactical_implies_correct[of "not\<^sub>n \<psi>"])
    ultimately
    show ?case
      by (auto intro: syntactical_implies_correct)
next
  case (Until_ltln \<phi> \<psi>)
    moreover
    have "\<phi> \<turnstile>\<^sub>s \<psi> \<Longrightarrow> ?case"
      by (force simp add: Until_ltln dest: syntactical_implies_correct)
    moreover
    {
      assume A: "(not\<^sub>n \<phi>) \<turnstile>\<^sub>s \<psi>" and B: "\<not> \<phi> \<turnstile>\<^sub>s \<psi>"
      hence [simp]: "rewrite_syn_imp (\<phi> U\<^sub>n \<psi>) = mk_finally (rewrite_syn_imp \<psi>)"
        by simp
      {
        assume "\<exists>i. suffix i w \<Turnstile>\<^sub>n \<psi>"
        moreover
        define i where "i \<equiv> LEAST i. suffix i w \<Turnstile>\<^sub>n \<psi>"
        ultimately
        have "\<forall>j < i. \<not>suffix j w \<Turnstile>\<^sub>n \<psi>" and "suffix i w \<Turnstile>\<^sub>n \<psi>"
          by (blast dest: not_less_Least , metis LeastI \<open>\<exists>i. suffix i w \<Turnstile>\<^sub>n \<psi>\<close> i_def)
        hence "\<forall>j < i. suffix j w \<Turnstile>\<^sub>n \<phi>" and "suffix i w \<Turnstile>\<^sub>n \<psi>"
          using syntactical_implies_correct[OF A] by auto
      }
      hence ?case
        by (simp del: rewrite_syn_imp.simps; unfold Until_ltln(2)) blast
    }
    ultimately
    show ?case
      by fastforce
next
  case (Release_ltln \<phi> \<psi>)
    moreover
    have "\<psi> \<turnstile>\<^sub>s \<phi> \<Longrightarrow> ?case"
      by (force simp add: Release_ltln dest: syntactical_implies_correct)
    moreover
    {
      assume A: "\<psi> \<turnstile>\<^sub>s (not\<^sub>n \<phi>)" and B: "\<not> \<psi> \<turnstile>\<^sub>s \<phi>"
      hence [simp]: "rewrite_syn_imp (\<phi> R\<^sub>n \<psi>) = mk_globally (rewrite_syn_imp \<psi>)"
        by simp
      {
        assume "\<exists>i. \<not>suffix i w \<Turnstile>\<^sub>n \<psi>"
        moreover
        define i where "i \<equiv> LEAST i. \<not>suffix i w \<Turnstile>\<^sub>n \<psi>"
        ultimately
        have "\<forall>j < i. suffix j w \<Turnstile>\<^sub>n \<psi>" and "\<not> suffix i w \<Turnstile>\<^sub>n \<psi>"
          by (blast dest: not_less_Least , metis LeastI \<open>\<exists>i. \<not>suffix i w \<Turnstile>\<^sub>n \<psi>\<close> i_def)
        hence "\<forall>j < i. \<not>suffix j w \<Turnstile>\<^sub>n \<phi>" and "\<not> suffix i w \<Turnstile>\<^sub>n \<psi>"
          using syntactical_implies_correct[OF A] by auto
      }
      hence ?case
        by (simp del: rewrite_syn_imp.simps; unfold Release_ltln(2)) blast
    }
    ultimately
    show ?case
      by fastforce
qed auto

subsection \<open>Iterated Rewriting\<close>

fun iterate
where
  "iterate f x 0 = x"
| "iterate f x (Suc n) = (let x' = f x in if x = x' then x else iterate f x' n)"

definition
  "rewrite_iter_fast \<phi> \<equiv> iterate (rewrite_modal o rewrite_X) \<phi> (size \<phi>)"

definition
  "rewrite_iter_slow \<phi> \<equiv> iterate (rewrite_syn_imp o rewrite_modal o rewrite_X) \<phi> (size \<phi>)"

text \<open>The rewriting functions defined in the previous subsections can be used as-is. However, in the
  most cases one wants to iterate these rules until the formula cannot be simplified further.
  @{const rewrite_iter_fast} pulls X operators up in the syntax tree and the uses the
  "modal" simplification rules. @{const rewrite_iter_slow} additionally tries to simplify the
  formula using syntactic implication checking.\<close>

lemma iterate_sound:
  assumes "\<And>\<phi>. w \<Turnstile>\<^sub>n f \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  shows "w \<Turnstile>\<^sub>n iterate f \<phi> n \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  by (induction n arbitrary: \<phi>; simp add: assms Let_def)

theorem rewrite_iter_fast_sound [simp]:
  "w \<Turnstile>\<^sub>n rewrite_iter_fast \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  using iterate_sound[of _ "rewrite_modal o rewrite_X"]
  unfolding comp_def rewrite_modal_sound rewrite_X_sound rewrite_iter_fast_def
  by blast

theorem rewrite_iter_slow_sound [simp]:
  "w \<Turnstile>\<^sub>n rewrite_iter_slow \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  using iterate_sound[of _ "rewrite_syn_imp o rewrite_modal o rewrite_X"]
  unfolding comp_def rewrite_modal_sound rewrite_X_sound rewrite_syn_imp_sound rewrite_iter_slow_def
  by blast

subsection \<open>Preservation of atoms\<close>

lemma iterate_atoms:
  assumes
    "\<And>\<phi>. atoms_ltln (f \<phi>) \<subseteq> atoms_ltln \<phi>"
  shows
    "atoms_ltln (iterate f \<phi> n) \<subseteq> atoms_ltln \<phi>"
  by (induction n arbitrary: \<phi>) (auto, metis (mono_tags, lifting) assms in_mono)

lemma rewrite_modal_atoms:
  "atoms_ltln (rewrite_modal \<phi>) \<subseteq> atoms_ltln \<phi>"
  by (induction \<phi>) auto

lemma mk_and_atoms:
  "atoms_ltln (mk_and \<phi> \<psi>) \<subseteq> atoms_ltln \<phi> \<union> atoms_ltln \<psi>"
  by (auto simp: mk_and_def split: ltln.splits)

lemma mk_or_atoms:
  "atoms_ltln (mk_or \<phi> \<psi>) \<subseteq> atoms_ltln \<phi> \<union> atoms_ltln \<psi>"
  by (auto simp: mk_or_def split: ltln.splits)

lemma remove_strong_ops_atoms:
  "atoms_ltln (remove_strong_ops \<phi>) \<subseteq> atoms_ltln \<phi>"
  by (induction \<phi>) auto

lemma remove_weak_ops_atoms:
  "atoms_ltln (remove_weak_ops \<phi>) \<subseteq> atoms_ltln \<phi>"
  by (induction \<phi>) auto

lemma mk_finally_atoms:
  "atoms_ltln (mk_finally \<phi>) \<subseteq> atoms_ltln \<phi>"
  by (auto simp: mk_finally_def split: ltln.splits) (insert remove_strong_ops_atoms, fast+)

lemma mk_globally_atoms:
  "atoms_ltln (mk_globally \<phi>) \<subseteq> atoms_ltln \<phi>"
  by (auto simp: mk_globally_def split: ltln.splits) (insert remove_weak_ops_atoms, fast+)

lemma mk_until_atoms:
  "atoms_ltln (mk_until \<phi> \<psi>) \<subseteq> atoms_ltln \<phi> \<union> atoms_ltln \<psi>"
  by (auto simp: mk_until_def split: ltln.splits) (insert mk_finally_atoms, fastforce+)

lemma mk_release_atoms:
  "atoms_ltln (mk_release \<phi> \<psi>) \<subseteq> atoms_ltln \<phi> \<union> atoms_ltln \<psi>"
  by (auto simp: mk_release_def split: ltln.splits) (insert mk_globally_atoms, fastforce+)

lemma mk_weak_until_atoms:
  "atoms_ltln (mk_weak_until \<phi> \<psi>) \<subseteq> atoms_ltln \<phi> \<union> atoms_ltln \<psi>"
  by (auto simp: mk_weak_until_def split: ltln.splits) (insert mk_globally_atoms, fastforce+)

lemma mk_strong_release_atoms:
  "atoms_ltln (mk_strong_release \<phi> \<psi>) \<subseteq> atoms_ltln \<phi> \<union> atoms_ltln \<psi>"
  by (auto simp: mk_strong_release_def split: ltln.splits) (insert mk_finally_atoms, fastforce+)

lemma mk_next_atoms:
  "atoms_ltln (mk_next \<phi>) = atoms_ltln \<phi>"
  by (auto simp: mk_next_def split: ltln.splits)

lemma mk_next_pow_atoms:
  "atoms_ltln (mk_next_pow n \<phi>) = atoms_ltln \<phi>"
  by (induction n) (auto simp: mk_next_pow_def split: ltln.splits)

lemma combine_atoms:
  assumes
    "\<And>\<phi> \<psi>. atoms_ltln (f \<phi> \<psi>) \<subseteq> atoms_ltln \<phi> \<union> atoms_ltln \<psi>"
  shows
    "atoms_ltln (fst (combine f x y)) \<subseteq> atoms_ltln (fst x) \<union> atoms_ltln (fst y)"
  by (metis assms fst_combine mk_next_pow_atoms prod.collapse)

lemmas combine_mk_atoms =
  combine_atoms[OF mk_and_atoms]
  combine_atoms[OF mk_or_atoms]
  combine_atoms[OF mk_until_atoms]
  combine_atoms[OF mk_release_atoms]
  combine_atoms[OF mk_weak_until_atoms]
  combine_atoms[OF mk_strong_release_atoms]

lemma rewrite_X_enat_atoms:
  "atoms_ltln (fst (rewrite_X_enat \<phi>)) \<subseteq> atoms_ltln \<phi>"
  by (induction \<phi>) (simp_all add: case_prod_beta, insert combine_mk_atoms, fast+)

lemma rewrite_X_atoms:
  "atoms_ltln (rewrite_X \<phi>) \<subseteq> atoms_ltln \<phi>"
  by (induction \<phi>) (simp_all add: rewrite_X_def mk_next_pow_atoms case_prod_beta, insert combine_mk_atoms, fast+)

lemma rewrite_syn_imp_atoms:
  "atoms_ltln (rewrite_syn_imp \<phi>) \<subseteq> atoms_ltln \<phi>"
proof (induction \<phi>)
  case (And_ltln \<phi>1 \<phi>2)
  then show ?case
    using mk_and_atoms by simp fast
next
  case (Or_ltln \<phi>1 \<phi>2)
  then show ?case
    using mk_or_atoms by simp fast
next
  case (Next_ltln \<phi>)
  then show ?case
    using mk_next_atoms by simp fast
next
  case (Until_ltln \<phi>1 \<phi>2)
  then show ?case
    using mk_finally_atoms mk_until_atoms by simp fast
next
  case (Release_ltln \<phi>1 \<phi>2)
  then show ?case
    using mk_globally_atoms mk_release_atoms by simp fast
qed simp_all

lemma rewrite_iter_fast_atoms:
  "atoms_ltln (rewrite_iter_fast \<phi>) \<subseteq> atoms_ltln \<phi>"
proof -
  have 1: "\<And>\<phi>. atoms_ltln (rewrite_modal (rewrite_X \<phi>)) \<subseteq> atoms_ltln \<phi>"
    using rewrite_modal_atoms rewrite_X_atoms by force

  show ?thesis
    by (simp add: rewrite_iter_fast_def 1 iterate_atoms)
qed

lemma rewrite_iter_slow_atoms:
  "atoms_ltln (rewrite_iter_slow \<phi>) \<subseteq> atoms_ltln \<phi>"
proof -
  have 1: "\<And>\<phi>. atoms_ltln (rewrite_syn_imp (rewrite_modal (rewrite_X \<phi>))) \<subseteq> atoms_ltln \<phi>"
    using rewrite_syn_imp_atoms rewrite_modal_atoms rewrite_X_atoms by force

  show ?thesis
    by (simp add: rewrite_iter_slow_def 1 iterate_atoms)
qed

subsection \<open>Simplifier\<close>

text \<open>We now define a convenience wrapper for the rewriting engine\<close>

datatype mode = Nop | Fast | Slow

fun simplify :: "mode \<Rightarrow> 'a ltln \<Rightarrow> 'a ltln"
where
  "simplify Nop = id"
| "simplify Fast = rewrite_iter_fast"
| "simplify Slow = rewrite_iter_slow"

theorem simplify_correct:
  "w \<Turnstile>\<^sub>n simplify m \<phi> \<longleftrightarrow> w \<Turnstile>\<^sub>n \<phi>"
  by (cases m) simp+

lemma simplify_atoms:
  "atoms_ltln (simplify m \<phi>) \<subseteq> atoms_ltln \<phi>"
  by (cases m) (insert rewrite_iter_fast_atoms rewrite_iter_slow_atoms, fastforce+)

subsection \<open>Code Generation\<close>

code_pred syntactical_implies .

export_code simplify checking

lemma "rewrite_iter_fast (F\<^sub>n (G\<^sub>n (X\<^sub>n prop\<^sub>n(''a'')))) = (F\<^sub>n (G\<^sub>n prop\<^sub>n(''a'')))"
  by eval

lemma "rewrite_iter_fast (X\<^sub>n prop\<^sub>n(''a'') U\<^sub>n (X\<^sub>n nprop\<^sub>n(''a''))) = X\<^sub>n (prop\<^sub>n(''a'') U\<^sub>n nprop\<^sub>n(''a''))"
  by eval

lemma "rewrite_iter_slow (X\<^sub>n prop\<^sub>n(''a'') U\<^sub>n (X\<^sub>n nprop\<^sub>n(''a''))) = X\<^sub>n (F\<^sub>n nprop\<^sub>n(''a''))"
  by eval

end
