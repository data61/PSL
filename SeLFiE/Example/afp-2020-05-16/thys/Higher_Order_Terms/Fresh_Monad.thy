chapter \<open>A monad for generating fresh names\<close>

theory Fresh_Monad
imports
  "HOL-Library.State_Monad"
  Term_Utils
begin

text \<open>
  Generation of fresh names in general can be thought of as picking a string that is not an element
  of a (finite) set of already existing names. For Isabelle, the \<^emph>\<open>Nominal\<close> framework
  @{cite urban2008nominal and urban2013nominal} provides support for reasoning over fresh names, but
  unfortunately, its definitions are not executable.

  Instead, I chose to model generation of fresh names as a monad based on @{type state}. With this,
  it becomes possible to write programs using \<open>do\<close>-notation. This is implemented abstractly as a
  @{command locale} that expects two operations:

  \<^item> \<open>next\<close> expects a value and generates a larger value, according to @{class linorder}
  \<^item> \<open>arb\<close> produces any value, similarly to @{const undefined}, but executable
\<close>

locale fresh =
  fixes "next" :: "'a::linorder \<Rightarrow> 'a" and arb :: 'a
  assumes next_ge: "next x > x"
begin

abbreviation update_next :: "('a, unit) state" where
"update_next \<equiv> State_Monad.update next"

lemma update_next_strict_mono[simp, intro]: "strict_mono_state update_next"
using next_ge by (auto intro: update_strict_mono)

lemma update_next_mono[simp, intro]: "mono_state update_next"
by (rule strict_mono_implies_mono) (rule update_next_strict_mono)

definition create :: "('a, 'a) state" where
"create = update_next \<bind> (\<lambda>_. State_Monad.get)"

lemma create_alt_def[code]: "create = State (\<lambda>a. (next a, next a))"
unfolding create_def State_Monad.update_def State_Monad.get_def State_Monad.set_def State_Monad.bind_def
by simp

abbreviation fresh_in :: "'a set \<Rightarrow> 'a \<Rightarrow> bool" where
"fresh_in S s \<equiv> Ball S ((\<ge>) s)"

lemma next_ge_all: "finite S \<Longrightarrow> fresh_in S s \<Longrightarrow> next s \<notin> S"
by (metis antisym less_imp_le less_irrefl next_ge)

definition Next :: "'a set \<Rightarrow> 'a" where
"Next S = (if S = {} then arb else next (Max S))"

lemma Next_ge_max: "finite S \<Longrightarrow> S \<noteq> {} \<Longrightarrow> Next S > Max S"
unfolding Next_def using next_ge by simp

lemma Next_not_member_subset: "finite S' \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> Next S' \<notin> S"
unfolding Next_def using next_ge
by (metis Max_ge Max_mono empty_iff finite_subset leD less_le_trans subset_empty)

lemma Next_not_member: "finite S \<Longrightarrow> Next S \<notin> S"
by (rule Next_not_member_subset) auto

lemma Next_geq_not_member: "finite S \<Longrightarrow> s \<ge> Next S \<Longrightarrow> s \<notin> S"
unfolding Next_def using next_ge
by (metis (full_types) Max_ge all_not_in_conv leD le_less_trans)

lemma next_not_member: "finite S \<Longrightarrow> s \<ge> Next S \<Longrightarrow> next s \<notin> S"
by (meson Next_geq_not_member less_imp_le next_ge order_trans)

lemma create_mono[simp, intro]: "mono_state create"
unfolding create_def
by (auto intro: bind_mono_strong)

lemma create_strict_mono[simp, intro]: "strict_mono_state create"
unfolding create_def
by (rule bind_strict_mono_strong2) auto

abbreviation run_fresh where
"run_fresh m S \<equiv> fst (run_state m (Next S))"

abbreviation fresh_fin :: "'a fset \<Rightarrow> 'a \<Rightarrow> bool" where
"fresh_fin S s \<equiv> fBall S ((\<ge>) s)"

context includes fset.lifting begin

lemma next_ge_fall: "fresh_fin S s \<Longrightarrow> next s |\<notin>| S"
by (transfer fixing: "next") (rule next_ge_all)

lift_definition fNext :: "'a fset \<Rightarrow> 'a" is Next .

lemma fNext_ge_max: "S \<noteq> {||} \<Longrightarrow> fNext S > fMax S"
by transfer (rule Next_ge_max)

lemma next_not_fmember: "s \<ge> fNext S \<Longrightarrow> next s |\<notin>| S"
by transfer (rule next_not_member)

lemma fNext_geq_not_member: "s \<ge> fNext S \<Longrightarrow> s |\<notin>| S"
by transfer (rule Next_geq_not_member)

lemma fNext_not_member: "fNext S |\<notin>| S"
by transfer (rule Next_not_member)

lemma fNext_not_member_subset: "S |\<subseteq>| S' \<Longrightarrow> fNext S' |\<notin>| S"
by transfer (rule Next_not_member_subset)

abbreviation frun_fresh where
"frun_fresh m S \<equiv> fst (run_state m (fNext S))"

end

end

end