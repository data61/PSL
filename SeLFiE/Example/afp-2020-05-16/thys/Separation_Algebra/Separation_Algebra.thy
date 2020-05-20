(* Authors: Gerwin Klein and Rafal Kolanski, 2012
   Maintainers: Gerwin Klein <kleing at cse.unsw.edu.au>
                Rafal Kolanski <rafal.kolanski at nicta.com.au>
*)

section "Abstract Separation Algebra"

theory Separation_Algebra
imports Main
begin


text \<open>This theory is the main abstract separation algebra development\<close>


section \<open>Input syntax for lifting boolean predicates to separation predicates\<close>

abbreviation (input)
  pred_and :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "and" 35) where
  "a and b \<equiv> \<lambda>s. a s \<and> b s"

abbreviation (input)
  pred_or :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "or" 30) where
  "a or b \<equiv> \<lambda>s. a s \<or> b s"

abbreviation (input)
  pred_not :: "('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" ("not _" [40] 40) where
  "not a \<equiv> \<lambda>s. \<not>a s"

abbreviation (input)
  pred_imp :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (infixr "imp" 25) where
  "a imp b \<equiv> \<lambda>s. a s \<longrightarrow> b s"

abbreviation (input)
  pred_K :: "'b \<Rightarrow> 'a \<Rightarrow> 'b" ("\<langle>_\<rangle>") where
  "\<langle>f\<rangle> \<equiv> \<lambda>s. f"

abbreviation (input)
  pred_ex :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "EXS " 10) where
  "EXS x. P x \<equiv> \<lambda>s. \<exists>x. P x s"

abbreviation (input)
  pred_all :: "('b \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> bool" (binder "ALLS " 10) where
  "ALLS x. P x \<equiv> \<lambda>s. \<forall>x. P x s"


section \<open>Associative/Commutative Monoid Basis of Separation Algebras\<close>

class pre_sep_algebra = zero + plus +
  fixes sep_disj :: "'a => 'a => bool" (infix "##" 60)

  assumes sep_disj_zero [simp]: "x ## 0"
  assumes sep_disj_commuteI: "x ## y \<Longrightarrow> y ## x"

  assumes sep_add_zero [simp]: "x + 0 = x"
  assumes sep_add_commute: "x ## y \<Longrightarrow> x + y = y + x"

  assumes sep_add_assoc:
    "\<lbrakk> x ## y; y ## z; x ## z \<rbrakk> \<Longrightarrow> (x + y) + z = x + (y + z)"
begin

lemma sep_disj_commute: "x ## y = y ## x"
  by (blast intro: sep_disj_commuteI)

lemma sep_add_left_commute:
  assumes a: "a ## b" "b ## c" "a ## c"
  shows "b + (a + c) = a + (b + c)" (is "?lhs = ?rhs")
proof -
  have "?lhs = b + a + c" using a
    by (simp add: sep_add_assoc[symmetric] sep_disj_commute)
  also have "... = a + b + c" using a
    by (simp add: sep_add_commute sep_disj_commute)
  also have "... = ?rhs" using a
    by (simp add: sep_add_assoc sep_disj_commute)
  finally show ?thesis .
qed

lemmas sep_add_ac = sep_add_assoc sep_add_commute sep_add_left_commute
                    sep_disj_commute (* nearly always necessary *)

end


section \<open>Separation Algebra as Defined by Calcagno et al.\<close>

class sep_algebra = pre_sep_algebra +
  assumes sep_disj_addD1: "\<lbrakk> x ## y + z; y ## z \<rbrakk> \<Longrightarrow> x ## y"
  assumes sep_disj_addI1: "\<lbrakk> x ## y + z; y ## z \<rbrakk> \<Longrightarrow> x + y ##  z"
begin

subsection \<open>Basic Construct Definitions and Abbreviations\<close>

definition
  sep_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixr "**" 35)
  where
  "P ** Q \<equiv> \<lambda>h. \<exists>x y. x ## y \<and> h = x + y \<and> P x \<and> Q y"

notation
  sep_conj (infixr "\<and>*" 35)

definition
  sep_empty :: "'a \<Rightarrow> bool" ("\<box>") where
  "\<box> \<equiv> \<lambda>h. h = 0"

definition
  sep_impl :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixr "\<longrightarrow>*" 25)
  where
  "P \<longrightarrow>* Q \<equiv> \<lambda>h. \<forall>h'. h ## h' \<and> P h' \<longrightarrow> Q (h + h')"

definition
  sep_substate :: "'a => 'a => bool" (infix "\<preceq>" 60) where
  "x \<preceq> y \<equiv> \<exists>z. x ## z \<and> x + z = y"

(* We want these to be abbreviations not definitions, because basic True and
   False will occur by simplification in sep_conj terms *)
abbreviation
  "sep_true \<equiv> \<langle>True\<rangle>"

abbreviation
  "sep_false \<equiv> \<langle>False\<rangle>"

definition
  sep_list_conj :: "('a \<Rightarrow> bool) list \<Rightarrow> ('a \<Rightarrow> bool)"  ("\<And>* _" [60] 90) where
  "sep_list_conj Ps \<equiv> foldl (**) \<box> Ps"


subsection \<open>Disjunction/Addition Properties\<close>

lemma disjoint_zero_sym [simp]: "0 ## x"
  by (simp add: sep_disj_commute)

lemma sep_add_zero_sym [simp]: "0 + x = x"
  by (simp add: sep_add_commute)

lemma sep_disj_addD2: "\<lbrakk> x ## y + z; y ## z \<rbrakk> \<Longrightarrow> x ## z"
  by (metis sep_disj_addD1 sep_add_ac)

lemma sep_disj_addD: "\<lbrakk> x ## y + z; y ## z \<rbrakk> \<Longrightarrow> x ## y \<and> x ## z"
  by (metis sep_disj_addD1 sep_disj_addD2)

lemma sep_add_disjD: "\<lbrakk> x + y ## z; x ## y \<rbrakk> \<Longrightarrow> x ## z \<and> y ## z"
  by (metis sep_disj_addD sep_disj_commuteI)

lemma sep_disj_addI2:
  "\<lbrakk> x ## y + z; y ## z \<rbrakk> \<Longrightarrow> x + z ## y"
  by (metis sep_add_ac sep_disj_addI1)

lemma sep_add_disjI1:
  "\<lbrakk> x + y ## z; x ## y \<rbrakk> \<Longrightarrow> x + z ## y"
  by (metis sep_add_ac sep_add_disjD sep_disj_addI2)

lemma sep_add_disjI2:
  "\<lbrakk> x + y ## z; x ## y \<rbrakk> \<Longrightarrow> z + y ## x"
  by (metis sep_add_ac sep_add_disjD sep_disj_addI2)

lemma sep_disj_addI3:
   "x + y ## z \<Longrightarrow> x ## y \<Longrightarrow> x ## y + z"
   by (metis sep_add_ac sep_add_disjD sep_add_disjI2)

lemma sep_disj_add:
  "\<lbrakk> y ## z; x ## y \<rbrakk> \<Longrightarrow> x ## y + z = x + y ## z"
  by (metis sep_disj_addI1 sep_disj_addI3)


subsection \<open>Substate Properties\<close>

lemma sep_substate_disj_add:
  "x ## y \<Longrightarrow> x \<preceq> x + y"
  unfolding sep_substate_def by blast

lemma sep_substate_disj_add':
  "x ## y \<Longrightarrow> x \<preceq> y + x"
  by (simp add: sep_add_ac sep_substate_disj_add)


subsection \<open>Separating Conjunction Properties\<close>

lemma sep_conjD:
  "(P \<and>* Q) h \<Longrightarrow> \<exists>x y. x ## y \<and> h = x + y \<and> P x \<and> Q y"
  by (simp add: sep_conj_def)

lemma sep_conjE:
  "\<lbrakk> (P ** Q) h; \<And>x y. \<lbrakk> P x; Q y; x ## y; h = x + y \<rbrakk> \<Longrightarrow> X \<rbrakk> \<Longrightarrow> X"
  by (auto simp: sep_conj_def)

lemma sep_conjI:
  "\<lbrakk> P x; Q y; x ## y; h = x + y \<rbrakk> \<Longrightarrow> (P ** Q) h"
  by (auto simp: sep_conj_def)

lemma sep_conj_commuteI:
  "(P ** Q) h \<Longrightarrow> (Q ** P) h"
  by (auto intro!: sep_conjI elim!: sep_conjE simp: sep_add_ac)

lemma sep_conj_commute:
  "(P ** Q) = (Q ** P)"
  by (rule ext) (auto intro: sep_conj_commuteI)

lemma sep_conj_assoc:
  "((P ** Q) ** R) = (P ** Q ** R)" (is "?lhs = ?rhs")
proof (rule ext, rule iffI)
  fix h
  assume a: "?lhs h"
  then obtain x y z where "P x" and "Q y" and "R z"
                      and "x ## y" and "x ## z" and "y ## z" and "x + y ## z"
                      and "h = x + y + z"
    by (auto dest!: sep_conjD dest: sep_add_disjD)
  moreover
  then have "x ## y + z"
    by (simp add: sep_disj_add)
  ultimately
  show "?rhs h"
    by (auto simp: sep_add_ac intro!: sep_conjI)
next
  fix h
  assume a: "?rhs h"
  then obtain x y z where "P x" and "Q y" and "R z"
                      and "x ## y" and "x ## z" and "y ## z" and "x ## y + z"
                      and "h = x + y + z"
    by (fastforce elim!: sep_conjE simp: sep_add_ac dest: sep_disj_addD)
  thus "?lhs h"
    by (metis sep_conj_def sep_disj_addI1)
qed

lemma sep_conj_impl:
  "\<lbrakk> (P ** Q) h; \<And>h. P h \<Longrightarrow> P' h; \<And>h. Q h \<Longrightarrow> Q' h \<rbrakk> \<Longrightarrow> (P' ** Q') h"
  by (erule sep_conjE, auto intro!: sep_conjI)

lemma sep_conj_impl1:
  assumes P: "\<And>h. P h \<Longrightarrow> I h"
  shows "(P ** R) h \<Longrightarrow> (I ** R) h"
  by (auto intro: sep_conj_impl P)

lemma sep_globalise:
  "\<lbrakk> (P ** R) h; (\<And>h. P h \<Longrightarrow> Q h) \<rbrakk> \<Longrightarrow> (Q ** R) h"
  by (fast elim: sep_conj_impl)

lemma sep_conj_trivial_strip2:
  "Q = R \<Longrightarrow> (Q ** P) = (R ** P)" by simp

lemma disjoint_subheaps_exist:
  "\<exists>x y. x ## y \<and> h = x + y"
  by (rule_tac x=0 in exI, auto)

lemma sep_conj_left_commute: (* for permutative rewriting *)
  "(P ** (Q ** R)) = (Q ** (P ** R))" (is "?x = ?y")
proof -
  have "?x = ((Q ** R) ** P)" by (simp add: sep_conj_commute)
  also have "\<dots> = (Q ** (R ** P))" by (subst sep_conj_assoc, simp)
  finally show ?thesis by (simp add: sep_conj_commute)
qed

lemmas sep_conj_ac = sep_conj_commute sep_conj_assoc sep_conj_left_commute

lemma ab_semigroup_mult_sep_conj: "class.ab_semigroup_mult (**)"
  by (unfold_locales)
     (auto simp: sep_conj_ac)

lemma sep_empty_zero [simp,intro!]: "\<box> 0"
  by (simp add: sep_empty_def)


subsection \<open>Properties of \<open>sep_true\<close> and \<open>sep_false\<close>\<close>

lemma sep_conj_sep_true:
  "P h \<Longrightarrow> (P ** sep_true) h"
  by (simp add: sep_conjI[where y=0])

lemma sep_conj_sep_true':
  "P h \<Longrightarrow> (sep_true ** P) h"
  by (simp add: sep_conjI[where x=0])

lemma sep_conj_true [simp]:
  "(sep_true ** sep_true) = sep_true"
  unfolding sep_conj_def
  by (auto intro!: ext intro: disjoint_subheaps_exist)

lemma sep_conj_false_right [simp]:
  "(P ** sep_false) = sep_false"
  by (force elim: sep_conjE intro!: ext)

lemma sep_conj_false_left [simp]:
  "(sep_false ** P) = sep_false"
  by (subst sep_conj_commute) (rule sep_conj_false_right)



subsection \<open>Properties of zero (@{const sep_empty})\<close>

lemma sep_conj_empty [simp]:
  "(P ** \<box>) = P"
  by (simp add: sep_conj_def sep_empty_def)

lemma sep_conj_empty'[simp]:
  "(\<box> ** P) = P"
  by (subst sep_conj_commute, rule sep_conj_empty)

lemma sep_conj_sep_emptyI:
  "P h \<Longrightarrow> (P ** \<box>) h"
  by simp

lemma sep_conj_sep_emptyE:
  "\<lbrakk> P s; (P ** \<box>) s \<Longrightarrow> (Q ** R) s \<rbrakk> \<Longrightarrow> (Q ** R) s"
  by simp

lemma monoid_add: "class.monoid_add ((**)) \<box>"
  by (unfold_locales) (auto simp: sep_conj_ac)

lemma comm_monoid_add: "class.comm_monoid_add (**) \<box>"
  by (unfold_locales) (auto simp: sep_conj_ac)


subsection \<open>Properties of top (\<open>sep_true\<close>)\<close>

lemma sep_conj_true_P [simp]:
  "(sep_true ** (sep_true ** P)) = (sep_true ** P)"
  by (simp add: sep_conj_assoc[symmetric])

lemma sep_conj_disj:
  "((P or Q) ** R) = ((P ** R) or (Q ** R))"
  by (auto simp: sep_conj_def intro!: ext)

lemma sep_conj_sep_true_left:
  "(P ** Q) h \<Longrightarrow> (sep_true ** Q) h"
  by (erule sep_conj_impl, simp+)

lemma sep_conj_sep_true_right:
  "(P ** Q) h \<Longrightarrow> (P ** sep_true) h"
  by (subst (asm) sep_conj_commute, drule sep_conj_sep_true_left,
      simp add: sep_conj_ac)


subsection \<open>Separating Conjunction with Quantifiers\<close>

lemma sep_conj_conj:
  "((P and Q) ** R) h \<Longrightarrow> ((P ** R) and (Q ** R)) h"
  by (force intro: sep_conjI elim!: sep_conjE)

lemma sep_conj_exists1:
  "((EXS x. P x) ** Q) = (EXS x. (P x ** Q))"
  by (force intro!: ext intro: sep_conjI elim: sep_conjE)

lemma sep_conj_exists2:
  "(P ** (EXS x. Q x)) = (EXS x. P ** Q x)"
  by (force intro!: sep_conjI ext elim!: sep_conjE)

lemmas sep_conj_exists = sep_conj_exists1 sep_conj_exists2

lemma sep_conj_spec:
  "((ALLS x. P x) ** Q) h \<Longrightarrow> (P x ** Q) h"
  by (force intro: sep_conjI elim: sep_conjE)


subsection \<open>Properties of Separating Implication\<close>

lemma sep_implI:
  assumes a: "\<And>h'. \<lbrakk> h ## h'; P h' \<rbrakk> \<Longrightarrow> Q (h + h')"
  shows "(P \<longrightarrow>* Q) h"
  unfolding sep_impl_def by (auto elim: a)

lemma sep_implD:
  "(x \<longrightarrow>* y) h \<Longrightarrow> \<forall>h'. h ## h' \<and> x h' \<longrightarrow> y (h + h')"
  by (force simp: sep_impl_def)

lemma sep_implE:
  "(x \<longrightarrow>* y) h \<Longrightarrow> (\<forall>h'. h ## h' \<and> x h' \<longrightarrow> y (h + h') \<Longrightarrow> Q) \<Longrightarrow> Q"
  by (auto dest: sep_implD)

lemma sep_impl_sep_true [simp]:
  "(P \<longrightarrow>* sep_true) = sep_true"
  by (force intro!: sep_implI ext)

lemma sep_impl_sep_false [simp]:
  "(sep_false \<longrightarrow>* P) = sep_true"
  by (force intro!: sep_implI ext)

lemma sep_impl_sep_true_P:
  "(sep_true \<longrightarrow>* P) h \<Longrightarrow> P h"
  by (clarsimp dest!: sep_implD elim!: allE[where x=0])

lemma sep_impl_sep_true_false [simp]:
  "(sep_true \<longrightarrow>* sep_false) = sep_false"
  by (force intro!: ext dest: sep_impl_sep_true_P)

lemma sep_conj_sep_impl:
  "\<lbrakk> P h; \<And>h. (P ** Q) h \<Longrightarrow> R h \<rbrakk> \<Longrightarrow> (Q \<longrightarrow>* R) h"
proof (rule sep_implI)
  fix h' h
  assume "P h" and "h ## h'" and "Q h'"
  hence "(P ** Q) (h + h')" by (force intro: sep_conjI)
  moreover assume "\<And>h. (P ** Q) h \<Longrightarrow> R h"
  ultimately show "R (h + h')" by simp
qed

lemma sep_conj_sep_impl2:
  "\<lbrakk> (P ** Q) h; \<And>h. P h \<Longrightarrow> (Q \<longrightarrow>* R) h \<rbrakk> \<Longrightarrow> R h"
  by (force dest: sep_implD elim: sep_conjE)

lemma sep_conj_sep_impl_sep_conj2:
  "(P ** R) h \<Longrightarrow> (P ** (Q \<longrightarrow>* (Q ** R))) h"
  by (erule (1) sep_conj_impl, erule sep_conj_sep_impl, simp add: sep_conj_ac)


subsection \<open>Pure assertions\<close>

definition
  pure :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "pure P \<equiv> \<forall>h h'. P h = P h'"

lemma pure_sep_true:
  "pure sep_true"
  by (simp add: pure_def)

lemma pure_sep_false:
  "pure sep_true"
  by (simp add: pure_def)

lemma pure_split:
  "pure P = (P = sep_true \<or> P = sep_false)"
  by (force simp: pure_def intro!: ext)

lemma pure_sep_conj:
  "\<lbrakk> pure P; pure Q \<rbrakk> \<Longrightarrow> pure (P \<and>* Q)"
  by (force simp: pure_split)

lemma pure_sep_impl:
  "\<lbrakk> pure P; pure Q \<rbrakk> \<Longrightarrow> pure (P \<longrightarrow>* Q)"
  by (force simp: pure_split)

lemma pure_conj_sep_conj:
  "\<lbrakk> (P and Q) h; pure P \<or> pure Q \<rbrakk> \<Longrightarrow> (P \<and>* Q) h"
  by (metis pure_def sep_add_zero sep_conjI sep_conj_commute sep_disj_zero)

lemma pure_sep_conj_conj:
  "\<lbrakk> (P \<and>* Q) h; pure P; pure Q \<rbrakk> \<Longrightarrow> (P and Q) h"
  by (force simp: pure_split)

lemma pure_conj_sep_conj_assoc:
  "pure P \<Longrightarrow> ((P and Q) \<and>* R) = (P and (Q \<and>* R))"
  by (auto simp: pure_split)

lemma pure_sep_impl_impl:
  "\<lbrakk> (P \<longrightarrow>* Q) h; pure P \<rbrakk> \<Longrightarrow> P h \<longrightarrow> Q h"
  by (force simp: pure_split dest: sep_impl_sep_true_P)

lemma pure_impl_sep_impl:
  "\<lbrakk> P h \<longrightarrow> Q h; pure P; pure Q \<rbrakk> \<Longrightarrow> (P \<longrightarrow>* Q) h"
  by (force simp: pure_split)

lemma pure_conj_right: "(Q \<and>* (\<langle>P'\<rangle> and Q')) = (\<langle>P'\<rangle> and (Q \<and>* Q'))"
  by (rule ext, rule, rule, clarsimp elim!: sep_conjE)
     (erule sep_conj_impl, auto)

lemma pure_conj_right': "(Q \<and>* (P' and \<langle>Q'\<rangle>)) = (\<langle>Q'\<rangle> and (Q \<and>* P'))"
  by (simp add: conj_comms pure_conj_right)

lemma pure_conj_left: "((\<langle>P'\<rangle> and Q') \<and>* Q) = (\<langle>P'\<rangle> and (Q' \<and>* Q))"
  by (simp add: pure_conj_right sep_conj_ac)

lemma pure_conj_left': "((P' and \<langle>Q'\<rangle>) \<and>* Q) = (\<langle>Q'\<rangle> and (P' \<and>* Q))"
  by (subst conj_comms, subst pure_conj_left, simp)

lemmas pure_conj = pure_conj_right pure_conj_right' pure_conj_left
    pure_conj_left'

declare pure_conj[simp add]


subsection \<open>Intuitionistic assertions\<close>

definition intuitionistic :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "intuitionistic P \<equiv> \<forall>h h'. P h \<and> h \<preceq> h' \<longrightarrow> P h'"

lemma intuitionisticI:
  "(\<And>h h'. \<lbrakk> P h; h \<preceq> h' \<rbrakk> \<Longrightarrow> P h') \<Longrightarrow> intuitionistic P"
  by (unfold intuitionistic_def, fast)

lemma intuitionisticD:
  "\<lbrakk> intuitionistic P; P h; h \<preceq> h' \<rbrakk> \<Longrightarrow> P h'"
  by (unfold intuitionistic_def, fast)

lemma pure_intuitionistic:
  "pure P \<Longrightarrow> intuitionistic P"
  by (clarsimp simp: intuitionistic_def pure_def, fast)

lemma intuitionistic_conj:
  "\<lbrakk> intuitionistic P; intuitionistic Q \<rbrakk> \<Longrightarrow> intuitionistic (P and Q)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_disj:
  "\<lbrakk> intuitionistic P; intuitionistic Q \<rbrakk> \<Longrightarrow> intuitionistic (P or Q)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_forall:
  "(\<And>x. intuitionistic (P x)) \<Longrightarrow> intuitionistic (ALLS x. P x)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_exists:
  "(\<And>x. intuitionistic (P x)) \<Longrightarrow> intuitionistic (EXS x. P x)"
  by (force intro: intuitionisticI dest: intuitionisticD)

lemma intuitionistic_sep_conj_sep_true:
  "intuitionistic (sep_true \<and>* P)"
proof (rule intuitionisticI)
  fix h h' r
  assume a: "(sep_true \<and>* P) h"
  then obtain x y where P: "P y" and h: "h = x + y" and xyd: "x ## y"
    by - (drule sep_conjD, clarsimp)
  moreover assume a2: "h \<preceq> h'"
  then obtain z where h': "h' = h + z" and hzd: "h ## z"
    by (clarsimp simp: sep_substate_def)

  moreover have "(P \<and>* sep_true) (y + (x + z))"
    using P h hzd xyd
    by (metis sep_add_disjI1 sep_disj_commute sep_conjI)
  ultimately show "(sep_true \<and>* P) h'" using hzd
    by (auto simp: sep_conj_commute sep_add_ac dest!: sep_disj_addD)
qed

lemma intuitionistic_sep_impl_sep_true:
  "intuitionistic (sep_true \<longrightarrow>* P)"
proof (rule intuitionisticI)
  fix h h'
  assume imp: "(sep_true \<longrightarrow>* P) h" and hh': "h \<preceq> h'"

  from hh' obtain z where h': "h' = h + z" and hzd: "h ## z"
    by (clarsimp simp: sep_substate_def)
  show "(sep_true \<longrightarrow>* P) h'" using imp h' hzd
    apply (clarsimp dest!: sep_implD)
    apply (metis sep_add_assoc sep_add_disjD sep_disj_addI3 sep_implI)
    done
qed

lemma intuitionistic_sep_conj:
  assumes ip: "intuitionistic (P::('a \<Rightarrow> bool))"
  shows "intuitionistic (P \<and>* Q)"
proof (rule intuitionisticI)
  fix h h'
  assume sc: "(P \<and>* Q) h" and hh': "h \<preceq> h'"

  from hh' obtain z where h': "h' = h + z" and hzd: "h ## z"
    by (clarsimp simp: sep_substate_def)

  from sc obtain x y where px: "P x" and qy: "Q y"
                       and h: "h = x + y" and xyd: "x ## y"
    by (clarsimp simp: sep_conj_def)

  have "x ## z" using hzd h xyd
    by (metis sep_add_disjD)

  with ip px have "P (x + z)"
    by (fastforce elim: intuitionisticD sep_substate_disj_add)

  thus "(P \<and>* Q) h'" using h' h hzd qy xyd
    by (metis (full_types) sep_add_commute sep_add_disjD sep_add_disjI2
              sep_add_left_commute sep_conjI)
qed

lemma intuitionistic_sep_impl:
  assumes iq: "intuitionistic Q"
  shows "intuitionistic (P \<longrightarrow>* Q)"
proof (rule intuitionisticI)
  fix h h'
  assume imp: "(P \<longrightarrow>* Q) h" and hh': "h \<preceq> h'"

  from hh' obtain z where h': "h' = h + z" and hzd: "h ## z"
    by (clarsimp simp: sep_substate_def)

  {
    fix x
    assume px: "P x" and hzx: "h + z ## x"

    have "h + x \<preceq> h + x + z" using hzx hzd
    by (metis sep_add_disjI1 sep_substate_def)

    with imp hzd iq px hzx
    have "Q (h + z + x)"
    by (metis intuitionisticD sep_add_assoc sep_add_ac sep_add_disjD sep_implE)
  }

  with imp h' hzd iq show "(P \<longrightarrow>* Q) h'"
    by (fastforce intro: sep_implI)
qed

lemma strongest_intuitionistic:
  "\<not> (\<exists>Q. (\<forall>h. (Q h \<longrightarrow> (P \<and>* sep_true) h)) \<and> intuitionistic Q \<and>
      Q \<noteq> (P \<and>* sep_true) \<and> (\<forall>h. P h \<longrightarrow> Q h))"
  by (fastforce intro!: ext sep_substate_disj_add
                dest!: sep_conjD intuitionisticD)

lemma weakest_intuitionistic:
  "\<not> (\<exists>Q. (\<forall>h. ((sep_true \<longrightarrow>* P) h \<longrightarrow> Q h)) \<and> intuitionistic Q \<and>
      Q \<noteq> (sep_true \<longrightarrow>* P) \<and> (\<forall>h. Q h \<longrightarrow> P h))"
  apply (clarsimp intro!: ext)
  apply (rule iffI)
   apply (rule sep_implI)
   apply (drule_tac h="x" and h'="x + h'" in intuitionisticD)
     apply (clarsimp simp: sep_add_ac sep_substate_disj_add)+
  done

lemma intuitionistic_sep_conj_sep_true_P:
  "\<lbrakk> (P \<and>* sep_true) s; intuitionistic P \<rbrakk> \<Longrightarrow> P s"
  by (force dest: intuitionisticD elim: sep_conjE sep_substate_disj_add)

lemma intuitionistic_sep_conj_sep_true_simp:
  "intuitionistic P \<Longrightarrow> (P \<and>* sep_true) = P"
  by (fast intro!: sep_conj_sep_true ext
           elim: intuitionistic_sep_conj_sep_true_P)

lemma intuitionistic_sep_impl_sep_true_P:
  "\<lbrakk> P h; intuitionistic P \<rbrakk> \<Longrightarrow> (sep_true \<longrightarrow>* P) h"
  by (force intro!: sep_implI dest: intuitionisticD
            intro: sep_substate_disj_add)

lemma intuitionistic_sep_impl_sep_true_simp:
  "intuitionistic P \<Longrightarrow> (sep_true \<longrightarrow>* P) = P"
  by (fast intro!: ext
           elim: sep_impl_sep_true_P intuitionistic_sep_impl_sep_true_P)


subsection \<open>Strictly exact assertions\<close>

definition strictly_exact :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "strictly_exact P \<equiv> \<forall>h h'. P h \<and> P h' \<longrightarrow> h = h'"

lemma strictly_exactD:
  "\<lbrakk> strictly_exact P; P h; P h' \<rbrakk> \<Longrightarrow> h = h'"
  by (unfold strictly_exact_def, fast)

lemma strictly_exactI:
  "(\<And>h h'. \<lbrakk> P h; P h' \<rbrakk> \<Longrightarrow> h = h') \<Longrightarrow> strictly_exact P"
  by (unfold strictly_exact_def, fast)

lemma strictly_exact_sep_conj:
  "\<lbrakk> strictly_exact P; strictly_exact Q \<rbrakk> \<Longrightarrow> strictly_exact (P \<and>* Q)"
  apply (rule strictly_exactI)
  apply (erule sep_conjE)+
  apply (drule_tac h="x" and h'="xa" in strictly_exactD, assumption+)
  apply (drule_tac h="y" and h'="ya" in strictly_exactD, assumption+)
  apply clarsimp
  done

lemma strictly_exact_conj_impl:
  "\<lbrakk> (Q \<and>* sep_true) h; P h; strictly_exact Q \<rbrakk> \<Longrightarrow> (Q \<and>* (Q \<longrightarrow>* P)) h"
  by (force intro: sep_conjI sep_implI dest: strictly_exactD elim!: sep_conjE
            simp: sep_add_commute sep_add_assoc)

end

interpretation sep: ab_semigroup_mult "(**)"
  by (rule ab_semigroup_mult_sep_conj)

interpretation sep: comm_monoid_add "(**)" \<box>
  by (rule comm_monoid_add)


section \<open>Separation Algebra with Stronger, but More Intuitive Disjunction Axiom\<close>

class stronger_sep_algebra = pre_sep_algebra +
  assumes sep_add_disj_eq [simp]: "y ## z \<Longrightarrow> x ## y + z = (x ## y \<and> x ## z)"
begin

lemma sep_disj_add_eq [simp]: "x ## y \<Longrightarrow> x + y ## z = (x ## z \<and> y ## z)"
  by (metis sep_add_disj_eq sep_disj_commute)

subclass sep_algebra by standard auto

end


section \<open>Folding separating conjunction over lists of predicates\<close>

lemma sep_list_conj_Nil [simp]: "\<And>* [] = \<box>"
  by (simp add: sep_list_conj_def)

(* apparently these two are rarely used and had to be removed from List.thy *)
lemma (in semigroup_add) foldl_assoc:
shows "foldl (+) (x+y) zs = x + (foldl (+) y zs)"
by (induct zs arbitrary: y) (simp_all add:add.assoc)

lemma (in monoid_add) foldl_absorb0:
shows "x + (foldl (+) 0 zs) = foldl (+) x zs"
by (induct zs) (simp_all add:foldl_assoc)

lemma sep_list_conj_Cons [simp]: "\<And>* (x#xs) = (x ** \<And>* xs)"
  by (simp add: sep_list_conj_def sep.foldl_absorb0)

lemma sep_list_conj_append [simp]: "\<And>* (xs @ ys) = (\<And>* xs ** \<And>* ys)"
  by (simp add: sep_list_conj_def sep.foldl_absorb0)

lemma (in comm_monoid_add) foldl_map_filter:
  "foldl (+) 0 (map f (filter P xs)) +
     foldl (+) 0 (map f (filter (not P) xs))
   = foldl (+) 0 (map f xs)"
proof (induct xs)
  case Nil thus ?case by clarsimp
next
  case (Cons x xs)
  hence IH: "foldl (+) 0 (map f xs) =
               foldl (+) 0 (map f (filter P xs)) +
               foldl (+) 0 (map f [x\<leftarrow>xs . \<not> P x])"
               by (simp only: eq_commute)

  have foldl_Cons':
    "\<And>x xs. foldl (+) 0 (x # xs) = x + (foldl (+) 0 xs)"
    by (simp, subst foldl_absorb0[symmetric], rule refl)

  { assume "P x"
    hence ?case by (auto simp del: foldl_Cons simp add: foldl_Cons' IH ac_simps)
  } moreover {
    assume "\<not> P x"
    hence ?case by (auto simp del: foldl_Cons simp add: foldl_Cons' IH ac_simps)
  }
  ultimately show ?case by blast
qed


section \<open>Separation Algebra with a Cancellative Monoid (for completeness)\<close>

text \<open>
  Separation algebra with a cancellative monoid. The results of being a precise
  assertion (distributivity over separating conjunction) require this.
  although we never actually use this property in our developments, we keep
  it here for completeness.
\<close>
class cancellative_sep_algebra = sep_algebra +
  assumes sep_add_cancelD: "\<lbrakk> x + z = y + z ; x ## z ; y ## z \<rbrakk> \<Longrightarrow> x = y"
begin

definition
  (* In any heap, there exists at most one subheap for which P holds *)
  precise :: "('a \<Rightarrow> bool) \<Rightarrow> bool" where
  "precise P = (\<forall>h hp hp'. hp \<preceq> h \<and> P hp \<and> hp' \<preceq> h \<and> P hp' \<longrightarrow> hp = hp')"

lemma "precise ((=) s)"
  by (metis (full_types) precise_def)

lemma sep_add_cancel:
  "x ## z \<Longrightarrow> y ## z \<Longrightarrow> (x + z = y + z) = (x = y)"
  by (metis sep_add_cancelD)

lemma precise_distribute:
  "precise P = (\<forall>Q R. ((Q and R) \<and>* P) = ((Q \<and>* P) and (R \<and>* P)))"
proof (rule iffI)
  assume pp: "precise P"
  {
    fix Q R
    fix h hp hp' s

    { assume a: "((Q and R) \<and>* P) s"
      hence "((Q \<and>* P) and (R \<and>* P)) s"
        by (fastforce dest!: sep_conjD elim: sep_conjI)
    }
    moreover
    { assume qs: "(Q \<and>* P) s" and qr: "(R \<and>* P) s"

      from qs obtain x y where sxy: "s = x + y" and xy: "x ## y"
                           and x: "Q x" and y: "P y"
        by (fastforce dest!: sep_conjD)
      from qr obtain x' y' where sxy': "s = x' + y'" and xy': "x' ## y'"
                           and x': "R x'" and y': "P y'"
        by (fastforce dest!: sep_conjD)

      from sxy have ys: "y \<preceq> x + y" using xy
        by (fastforce simp: sep_substate_disj_add' sep_disj_commute)
      from sxy' have ys': "y' \<preceq> x' + y'" using xy'
        by (fastforce simp: sep_substate_disj_add' sep_disj_commute)

      from pp have yy: "y = y'" using sxy sxy' xy xy' y y' ys ys'
        by (fastforce simp: precise_def)

      hence "x = x'" using sxy sxy' xy xy'
        by (fastforce dest!: sep_add_cancelD)

      hence "((Q and R) \<and>* P) s" using sxy x x' yy y' xy'
        by (fastforce intro: sep_conjI)
    }
    ultimately
    have "((Q and R) \<and>* P) s = ((Q \<and>* P) and (R \<and>* P)) s" using pp by blast
  }
  thus "\<forall>Q R. ((Q and R) \<and>* P) = ((Q \<and>* P) and (R \<and>* P))" by (blast intro!: ext)

next
  assume a: "\<forall>Q R. ((Q and R) \<and>* P) = ((Q \<and>* P) and (R \<and>* P))"
  thus "precise P"
  proof (clarsimp simp: precise_def)
    fix h hp hp' Q R
    assume hp: "hp \<preceq> h" and hp': "hp' \<preceq> h" and php: "P hp" and php': "P hp'"

    obtain z where hhp: "h = hp + z" and hpz: "hp ## z" using hp
      by (clarsimp simp: sep_substate_def)
    obtain z' where hhp': "h = hp' + z'" and hpz': "hp' ## z'" using hp'
      by (clarsimp simp: sep_substate_def)

    have h_eq: "z' + hp' = z + hp" using hhp hhp' hpz hpz'
      by (fastforce simp: sep_add_ac)

    from hhp hhp' a hpz hpz' h_eq
    have "\<forall>Q R. ((Q and R) \<and>* P) (z + hp) = ((Q \<and>* P) and (R \<and>* P)) (z' + hp')"
      by (fastforce simp: h_eq sep_add_ac sep_conj_commute)

    hence "(((=) z and (=) z') \<and>* P) (z + hp) =
           (((=) z \<and>* P) and ((=) z' \<and>* P)) (z' + hp')" by blast

    thus  "hp = hp'" using php php' hpz hpz' h_eq
      by (fastforce dest!: iffD2 cong: conj_cong
                    simp: sep_add_ac sep_add_cancel sep_conj_def)
  qed
qed

lemma strictly_precise: "strictly_exact P \<Longrightarrow> precise P"
  by (metis precise_def strictly_exactD)

end

end
