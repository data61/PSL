(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section "Language Primitives"

theory Primitives imports "../pGCL" begin

text \<open>Programs in pGCL are probabilistic automata.  They can do anything a traditional program
can, plus, they may make truly probabilistic choices.\<close>

subsection \<open>The Basics\<close>

text \<open>Imagine flipping a pair of fair coins: @{term a} and @{term b}. Using a record type for the
state allows a number of syntactic niceties, which we describe shortly:\<close>

datatype coin = Heads | Tails

record coins =
  a :: coin
  b :: coin

text \<open>The primitive state operation is @{term Apply}, which takes a state transformer as an
argument, constructs the pGCL equivalent. Thus @{term "Apply (\<lambda>s. s\<lparr> a := Heads \<rparr>)"} sets the value
of coin @{term a} to @{term Heads}. As records are so common as state types, we introduce syntax to
make these update neater: The same program may be defined more simply as @{term "a := (\<lambda>s. Heads)"}
(note that the syntax translation involved does not apply to Latex output, and thus this lemma
appears trivial):
\<close>

lemma
  "Apply (\<lambda>s. s \<lparr> a := Heads \<rparr>) = (a := (\<lambda>s. Heads))"
  by(simp)

text \<open>We can treat the record's fields as the names of \emph{variables}. Note that the right-hand
side of an assignment is always a function of the current state. Thus we may use a record accessor
directly, for example @{term "a := b"}, which updates @{term a} with the current value of @{term b}.
If we wish to formally establish that the previous statement is correct i.e. that in the final
state, @{term a} really will have whatever value @{term b} had in the initial state, we must first
introduce the assertion language.\<close>

subsection \<open>Assertion and Annotation\<close>

text \<open>Assertions in pGCL are real-valued functions of the state, which are often interpreted as a
probability distribution over possible outcomes. These functions are termed \emph{expectations}, for
reasons which shortly be clear. Initially, however, we need only consider \emph{standard}
expectations: those derived from a binary predicate. A predicate @{term_type "P::'s \<Rightarrow> bool"} is
embedded as @{term_type "\<guillemotleft>P::'s \<Rightarrow> bool\<guillemotright>"}, such that @{term "P s \<longrightarrow> \<guillemotleft>P\<guillemotright> s = 1 \<and> \<not> P s \<longrightarrow> \<guillemotleft>P\<guillemotright> s = 0"}.

  An annotation consists of an assertion on the initial state and one on the final state, which for
  standard expectations may be interpreted as `if @{term P} holds in the initial state, then @{term
  Q} will hold in the final state'. These are in weakest-precondition form: we assert that the
  precondition implies the \emph{weakest precondition}: the weakest assertion on the initial state,
  which implies that the postcondition must hold on the final state. So far, this is identical to
  the standard approach. Remember, however, that we are working with \emph{real-valued} assertions.
  For standard expectations, the logic is nevertheless identical, if the implication @{term "\<forall>s. P s
  \<longrightarrow> Q s"} is substituted with the equivalent expectation entailment @{term "\<guillemotleft>P\<guillemotright> \<tturnstile> \<guillemotleft>Q\<guillemotright>"}, @{thm
  entails_implies}. Thus a valid specification of @{term "a := b"} is:\<close>

lemma
  "\<And>x. \<guillemotleft>\<lambda>s. b s = x\<guillemotright> \<tturnstile> wp (a := b) \<guillemotleft>\<lambda>s. a s = x\<guillemotright>"
  by(pvcg, simp add:o_def)

text \<open>Any ordinary computation and its associated annotation can be expressed in this form.\<close>

subsection \<open>Probability\<close>

text \<open>Next, we introduce the syntax @{term "x ;; y"} for the sequential composition of @{term x}
and @{term y}, and also demonstrate that one can operate directly on a real-valued (and thus
infinite) state space:\<close>

lemma
  "\<guillemotleft>\<lambda>s::real. s \<noteq> 0\<guillemotright> \<tturnstile> wp (Apply ((*) 2) ;; Apply (\<lambda>s. s / s)) \<guillemotleft>\<lambda>s. s = 1\<guillemotright>"
  by(pvcg, simp add:o_def)

text \<open>So far, we haven't done anything that required probabilities, or expectations other than 0
and 1. As an example of both, we show that a single coin toss is fair. We introduce the syntax
@{term "x \<^bsub>p\<^esub>\<oplus> y"} for a probabilistic choice between @{term x} and @{term y}. This program behaves
as @{term x} with probability @{term p}, and as @{term y} with probability @{term "1-p"}. The
probability may depend on the state, and is therefore of type @{typ "'s \<Rightarrow> real"}. The following
annotation states that the probability of heads is exactly 1/2:\<close>

definition
  flip_a :: "real \<Rightarrow> coins prog"
where
  "flip_a p = a := (\<lambda>_. Heads) \<^bsub>(\<lambda>s. p)\<^esub>\<oplus> a := (\<lambda>_. Tails)"

lemma
  "(\<lambda>s. 1/2) = wp (flip_a (1/2)) \<guillemotleft>\<lambda>s. a s = Heads\<guillemotright>"
  unfolding flip_a_def
  txt \<open>Sufficiently small problems can be handled by the simplifier, by symbolic evaluation.\<close>
  by(simp add:wp_eval o_def)

subsection \<open>Nondeterminism\<close>

text \<open>We can also under-specify a program, using the \emph{nondeterministic choice} operator,
@{term "x \<Sqinter> y"}. This is interpreted demonically, giving the pointwise \emph{minimum} of the
pre-expectations for @{term x} and @{term y}: the chance of seeing heads, if your opponent is
allowed choose between a pair of coins, one biased 2/3 heads and one 2/3 tails, and then flips it,
is \emph{at least} 1/3, but we can make no stronger statement:\<close>

lemma
  "\<lambda>s. 1/3 \<tturnstile> wp (flip_a (2/3) \<Sqinter> flip_a (1/3)) \<guillemotleft>\<lambda>s. a s = Heads\<guillemotright>"
  unfolding flip_a_def
  by(pvcg, simp add:o_def le_funI)

subsection \<open>Properties of Expectations\<close>

text \<open>The probabilities of independent events combine as usual, by multiplying: The chance
of getting heads on two separate coins is @{term "1/4"}.\<close>

definition
  flip_b :: "real \<Rightarrow> coins prog"
where
  "flip_b p = b := (\<lambda>_. Heads) \<^bsub>(\<lambda>s. p)\<^esub>\<oplus> b := (\<lambda>_. Tails)"

lemma
  "(\<lambda>s. 1/4) = wp (flip_a (1/2) ;; flip_b (1/2))
                  \<guillemotleft>\<lambda>s. a s = Heads \<and> b s = Heads\<guillemotright>"
  unfolding flip_a_def flip_b_def
  by(simp add:wp_eval o_def)

text \<open>If, rather than two coins, we use two dice, we can make some slightly more involved
calculations.  We see that the weakest pre-expectation of the value on the face of the die after
rolling is its \emph{expected value} in the initial state, which justifies the use of the term
expectation.
\<close>

record dice =
  red  :: nat
  blue :: nat

definition Puniform :: "'a set \<Rightarrow> ('a \<Rightarrow> real)"
where "Puniform S = (\<lambda>x. if x \<in> S then 1 / card S else 0)"

lemma Puniform_in:
  "x \<in> S \<Longrightarrow> Puniform S x = 1 / card S"
  by(simp add:Puniform_def)

lemma Puniform_out:
  "x \<notin> S \<Longrightarrow> Puniform S x = 0"
  by(simp add:Puniform_def)

lemma supp_Puniform:
  "finite S \<Longrightarrow> supp (Puniform S) = S"
  by(auto simp:Puniform_def supp_def)

text \<open>The expected value of a roll of a six-sided die is @{term "7/2"}:\<close>

lemma
  "(\<lambda>s. 7/2) = wp (bind v at (\<lambda>s. Puniform {1..6} v) in red := (\<lambda>_. v)) red"
  by(simp add:wp_eval supp_Puniform sum.atLeast_Suc_atMost Puniform_in)

text \<open>The expectations of independent variables add:\<close>

lemma
  "(\<lambda>s. 7) = wp ((bind v at (\<lambda>s. Puniform {1..6} v) in red := (\<lambda>s. v)) ;;
                 (bind v at (\<lambda>s. Puniform {1..6} v) in blue := (\<lambda>s. v)))
                (\<lambda>s. red s + blue s)"
  by(simp add:wp_eval supp_Puniform sum.atLeast_Suc_atMost Puniform_in)

end
