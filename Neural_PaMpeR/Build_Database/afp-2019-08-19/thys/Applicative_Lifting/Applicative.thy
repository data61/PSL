(* Author: Joshua Schneider, ETH Zurich *)

section \<open>Lifting with applicative functors\<close>

theory Applicative
imports Main
keywords "applicative" :: thy_goal and "print_applicative" :: diag
begin

subsection \<open>Equality restricted to a set\<close>

definition eq_on :: "'a set \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool"
where [simp]: "eq_on A = (\<lambda>x y. x \<in> A \<and> x = y)"

lemma rel_fun_eq_onI: "(\<And>x. x \<in> A \<Longrightarrow> R (f x) (g x)) \<Longrightarrow> rel_fun (eq_on A) R f g"
by auto


subsection \<open>Proof automation\<close>

lemma arg1_cong: "x = y \<Longrightarrow> f x z = f y z"
by (rule arg_cong)

lemma UNIV_E: "x \<in> UNIV \<Longrightarrow> P \<Longrightarrow> P" .

context begin

private named_theorems combinator_unfold
private named_theorems combinator_repr

private definition "B g f x \<equiv> g (f x)"
private definition "C f x y \<equiv> f y x"
private definition "I x \<equiv> x"
private definition "K x y \<equiv> x"
private definition "S f g x \<equiv> (f x) (g x)"
private definition "T x f \<equiv> f x"
private definition "W f x \<equiv> f x x"

lemmas [abs_def, combinator_unfold] = B_def C_def I_def K_def S_def T_def W_def
lemmas [combinator_repr] = combinator_unfold

private definition "cpair \<equiv> Pair"
private definition "cuncurry \<equiv> case_prod"

private lemma uncurry_pair: "cuncurry f (cpair x y) = f x y"
unfolding cpair_def cuncurry_def by simp

ML_file "applicative.ML"

local_setup \<open>Applicative.setup_combinators
 [("B", @{thm B_def}),
  ("C", @{thm C_def}),
  ("I", @{thm I_def}),
  ("K", @{thm K_def}),
  ("S", @{thm S_def}),
  ("T", @{thm T_def}),
  ("W", @{thm W_def})]\<close>

private attribute_setup combinator_eq =
  \<open>Scan.lift (Scan.option (Args.$$$ "weak" |--
    Scan.optional (Args.colon |-- Scan.repeat1 Args.name) []) >>
    Applicative.combinator_rule_attrib)\<close>

lemma [combinator_eq]: "B \<equiv> S (K S) K" unfolding combinator_unfold .
lemma [combinator_eq]: "C \<equiv> S (S (K (S (K S) K)) S) (K K)" unfolding combinator_unfold .
lemma [combinator_eq]: "I \<equiv> W K" unfolding combinator_unfold .
lemma [combinator_eq]: "I \<equiv> C K ()" unfolding combinator_unfold .
lemma [combinator_eq]: "S \<equiv> B (B W) (B B C)" unfolding combinator_unfold .
lemma [combinator_eq]: "T \<equiv> C I" unfolding combinator_unfold .
lemma [combinator_eq]: "W \<equiv> S S (S K)" unfolding combinator_unfold .

lemma [combinator_eq weak: C]:
  "C \<equiv> C (B B (B B (B W (C (B C (B (B B) (C B (cuncurry (K I))))) (cuncurry K))))) cpair"
unfolding combinator_unfold uncurry_pair .

end (* context *)


method_setup applicative_unfold =
  \<open>Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.unfold_wrapper_tac ctxt opt_af))\<close>
  "unfold into an applicative expression"

method_setup applicative_fold =
  \<open>Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.fold_wrapper_tac ctxt opt_af))\<close>
  "fold an applicative expression"

method_setup applicative_nf =
  \<open>Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.normalize_wrapper_tac ctxt opt_af))\<close>
  "prove an equation that has been lifted to an applicative functor, using normal forms"

method_setup applicative_lifting =
  \<open>Applicative.parse_opt_afun >> (fn opt_af => fn ctxt =>
    SIMPLE_METHOD' (Applicative.lifting_wrapper_tac ctxt opt_af))\<close>
  "prove an equation that has been lifted to an applicative functor"

ML \<open>Outer_Syntax.local_theory_to_proof @{command_keyword "applicative"}
  "register applicative functors"
  (Parse.binding --
    Scan.optional (@{keyword "("} |-- Parse.list Parse.short_ident --| @{keyword ")"}) [] --
    (@{keyword "for"} |-- Parse.reserved "pure" |-- @{keyword ":"} |-- Parse.term) --
    (Parse.reserved "ap" |-- @{keyword ":"} |-- Parse.term) --
    Scan.option (Parse.reserved "rel" |-- @{keyword ":"} |-- Parse.term) --
    Scan.option (Parse.reserved "set" |-- @{keyword ":"} |-- Parse.term) >>
    Applicative.applicative_cmd)\<close>

ML \<open>Outer_Syntax.command @{command_keyword "print_applicative"}
  "print registered applicative functors"
  (Scan.succeed (Toplevel.keep (Applicative.print_afuns o Toplevel.context_of)))\<close>

attribute_setup applicative_unfold =
  \<open>Scan.lift (Scan.option Parse.name >> Applicative.add_unfold_attrib)\<close>
  "register rules for unfolding into applicative expressions"

attribute_setup applicative_lifted =
  \<open>Scan.lift (Parse.name >> Applicative.forward_lift_attrib)\<close>
  "lift an equation to an applicative functor"


subsection \<open>Overloaded applicative operators\<close>

consts
  pure :: "'a \<Rightarrow> 'b"
  ap :: "'a \<Rightarrow> 'b \<Rightarrow> 'c"

bundle applicative_syntax
begin
  notation ap (infixl "\<diamondop>" 70)
end

hide_const (open) ap

end
