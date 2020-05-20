(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section "Expectation Transformers"

theory Transformers imports Expectations begin

text_raw \<open>\label{s:transformers}\<close>

type_synonym 's trans = "'s expect \<Rightarrow> 's expect"

text \<open>Transformers are functions from expectations to expectations i.e. @{typ "('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow>
real"}. 

The set of \emph{healthy} transformers is the universe into which we place our semantic
interpretation of pGCL programs. In its standard presentation, the healthiness condition for pGCL
programs is \emph{sublinearity}, for demonic programs, and \emph{superlinearity} for angelic
programs. We extract a minimal core property, consisting of monotonicity, feasibility and scaling to
form our healthiness property, which holds across all programs. The additional components of
sublinearity are broken out separately, and shown later. The two reasons for this are firstly to
avoid the effort of establishing sub-(super-)linearity globally, and to allow us to define
primitives whose sublinearity, and indeed healthiness, depend on context.

Consider again the automaton of \autoref{f:automaton_1}. Here, the effect of executing the automaton
from its initial state ($a$) until it reaches some final state ($b$ or $c$) is to \emph{transform}
the expectation on final states ($P$), into one on initial states, giving the \emph{expected} value
of the function on termination. Here, the transformation is linear: $P_\text{prior}(a) = 0.7 *
P_\text{post}(b) + 0.3 * P_\text{post}(c)$, but this need not be the case.

\begin{figure}
\begin{center}
\mbox{
\xymatrix{
*++[o][F=]{b} & & *++[o][F=]{c} \\
 *++[o][F-]{a} \ar[u]^{0.7} \ar[urr]_(0.25){0.3}  & & *++[o][F-]{d} \ar[ull]^(0.25){0.5} \ar[u]_{0.5}\\
  & *++[o][F-]{e}\ar[ul] \ar[ur] \\
  & \ar[u]
}
}
\end{center}
\caption{\label{f:automaton_2}A nondeterministic-probabilistic automaton.}
\end{figure}

Consider the automaton of \autoref{f:automaton_2}. Here, we have extended that of
\autoref{f:automaton_1} with two additional states, $d$ and $e$, and a pair of silent (unlabelled)
transitions. From the initial state, $e$, this automaton is free to transition either to the
original starting state ($a$), and thence behave exactly as the previous automaton did, or to $d$,
which has the same set of available transitions, now with different probabilities. Where previously
we could state that the automaton would terminate in state $b$ with probability 0.7 (and in $c$ with
probability 0.3), this now depends on the outcome of the \emph{nondeterministic} transition from $e$
to either $a$ or $d$. The most we can now say is that we must reach $b$ with probability \emph{at
least} 0.5 (the minimum from either $a$ or $d$) and $c$ with at least probability 0.3. Note that
these probabilities do not sum to one (although the sum will still always be less than one). The
associated expectation transformer is now \emph{sub-}linear: $P_\text{prior}(e) = 0.5 *
P_\text{post}(b) + 0.3 * P_\text{post}(c)$.\<close>

text_raw \<open>
\begin{figure}
\begin{center}
\mbox{
\xymatrix{
*++[o][F=]{b} & & *++[o][F=]{c} \\
      *++[o][F-]{a} \ar@(dl,ul)[] \ar[u]^{0.5} \ar[urr]_{0.3}
  & & *++[o][F-]{d} \ar@(dr,ur)[] \\
  & *++[o][F-]{e}\ar[ul]^{0.5} \ar[ur]_{0.5} \\
  & \ar[u]
}
}
\end{center}
\caption{\label{f:automaton_3}A diverging automaton.}
\end{figure}
\<close>

text \<open>
Finally, \autoref{f:automaton_3} shows the other way in which strict sublinearity arises:
divergence.  This automaton transitions with probability 0.5 to state $d$, from which it never
escapes.  Once there, the probability of reaching any terminating state is zero, and thus the
probabilty of terminating from the initial state ($e$) is no higher than 0.5.  If it instead
takes the edge to state $a$, we again see a self loop, and thus in theory an infinite trace.  In
this case, however, every time the automaton reaches state $a$, with probability $0.5 + 0.3 = 0.8$,
it transitions to a terminating state.  An infinite trace of transitions $a \rightarrow a
\rightarrow \ldots$ thus has probability 0, and the automaton terminates with probability 1.  We
formalise such probabilistic termination arguments in \autoref{s:termination}.

Having reached $a$, the automaton will proceed to $b$ with probability $0.5 * (1 / (0.5 + 0.3)) =
0.625$, and to $c$ with probability $0.375$.  As $a$ is in turn reached half the time, the final
probability of ending in $b$ is $0.3125$, and in $c$, $0.1875$, which sum to only $0.5$.  The
remaining probability is that the automaton diverges via $d$.  We view nondeterminism and
divergence demonically: we take the \emph{least} probability of reaching a given final state, and
use it to calculate the expectation.  Thus for this automaton, $P_\text{prior}(e) = 0.3125 *
P_\text{post}(b) + 0.1875 * P_\text{post}(c)$.  The end result is the same as for nondeterminism:
a sublinear transformation (the weights sum to less than one).  The two outcomes are thus unified
in the semantic interpretation, although as we will establish in \autoref{s:prog_determ}, the two
have slightly different algebraic properties.

This pattern holds for all pGCL programs: probabilistic choices are always linear, while struct
sublinearity is introduced both nondeterminism and divergence.

Healthiness, again, is the combination of three properties: feasibility, monotonicity and
scaling. Feasibility requires that a transformer take non-negative expectations to non-negative
expectations, and preserve bounds. Thus, starting with an expectation bounded between 0 and some
bound, $b$, after applying any number of feasible transformers, the result will still be bounded
between 0 and $b$. This closure property allows us to treat expectations almost as a complete
lattice. Specifically, for any $b$, the set of expectations bounded by $b$ is a complete lattice
($\bot = (\lambda s. 0)$, $\top = (\lambda s. b)$), and is closed under the action of feasible
transformers, including $\sqcap$ and $\sqcup$, which are themselves feasible. We are thus able to
define both least and greatest fixed points on this set, and thus give semantics to recursive
programs built from feasible components.\<close>

subsection \<open>Comparing Transformers\<close>

text \<open>Transformers are compared pointwise, but only on @{term sound} expectations. From the
preorder so generated, we define equivalence by antisymmetry, giving a partial order.\<close>

definition
  le_trans :: "'s trans \<Rightarrow> 's trans \<Rightarrow> bool"
where
  "le_trans t u \<equiv> \<forall>P. sound P \<longrightarrow> t P \<le> u P"

text \<open>We also need to define relations restricted to @{term unitary} transformers, for the
liberal (wlp) semantics.\<close>

definition
  le_utrans :: "'s trans \<Rightarrow> 's trans \<Rightarrow> bool"
where
  "le_utrans t u \<longleftrightarrow> (\<forall>P. unitary P \<longrightarrow> t P \<le> u P)"

lemma le_transI[intro]:
  "\<lbrakk> \<And>P. sound P \<Longrightarrow> t P \<le> u P \<rbrakk> \<Longrightarrow> le_trans t u"
  by(simp add:le_trans_def)

lemma le_utransI[intro]:
  "\<lbrakk> \<And>P. unitary P \<Longrightarrow> t P \<le> u P \<rbrakk> \<Longrightarrow> le_utrans t u"
  by(simp add:le_utrans_def)

lemma  le_transD[dest]:
  "\<lbrakk> le_trans t u; sound P \<rbrakk> \<Longrightarrow> t P \<le> u P"
  by(simp add:le_trans_def)
  
lemma le_utransD[dest]:
  "\<lbrakk> le_utrans t u; unitary P \<rbrakk> \<Longrightarrow> t P \<le> u P"
  by(simp add:le_utrans_def)

lemma le_trans_trans[trans]:
  "\<lbrakk> le_trans x y; le_trans y z \<rbrakk> \<Longrightarrow> le_trans x z"
  unfolding le_trans_def by(blast dest:order_trans)
  
lemma le_utrans_trans[trans]:
  "\<lbrakk> le_utrans x y; le_utrans y z \<rbrakk> \<Longrightarrow> le_utrans x z"
  unfolding le_utrans_def by(blast dest:order_trans)

lemma le_trans_refl[iff]:
  "le_trans x x"
  by(simp add:le_trans_def)
  
lemma le_utrans_refl[iff]:
  "le_utrans x x"
  by(simp add:le_utrans_def)
  
lemma le_trans_le_utrans[dest]:
  "le_trans t u \<Longrightarrow> le_utrans t u"
  unfolding le_trans_def le_utrans_def by(auto)

definition
  l_trans :: "'s trans \<Rightarrow> 's trans \<Rightarrow> bool"
where
  "l_trans t u \<longleftrightarrow> le_trans t u \<and> \<not> le_trans u t"

text \<open>Transformer equivalence is induced by comparison:\<close>

definition
  equiv_trans :: "'s trans \<Rightarrow> 's trans \<Rightarrow> bool"
where
  "equiv_trans t u \<longleftrightarrow> le_trans t u \<and> le_trans u t"

definition
  equiv_utrans :: "'s trans \<Rightarrow> 's trans \<Rightarrow> bool"
where
  "equiv_utrans t u \<longleftrightarrow> le_utrans t u \<and> le_utrans u t"

lemma equiv_transI[intro]:
  "\<lbrakk> \<And>P. sound P \<Longrightarrow> t P = u P \<rbrakk> \<Longrightarrow> equiv_trans t u"
  unfolding equiv_trans_def by(force)

lemma equiv_utransI[intro]:
  "\<lbrakk> \<And>P. sound P \<Longrightarrow> t P = u P \<rbrakk> \<Longrightarrow> equiv_utrans t u"
  unfolding equiv_utrans_def by(force)

lemma equiv_transD[dest]:
  "\<lbrakk> equiv_trans t u; sound P \<rbrakk> \<Longrightarrow> t P = u P"
  unfolding equiv_trans_def by(blast intro:antisym)

lemma equiv_utransD[dest]:
  "\<lbrakk> equiv_utrans t u; unitary P \<rbrakk> \<Longrightarrow> t P = u P"
  unfolding equiv_utrans_def by(blast intro:antisym)

lemma equiv_trans_refl[iff]:
  "equiv_trans t t"
  by(blast)

lemma equiv_utrans_refl[iff]:
  "equiv_utrans t t"
  by(blast)

lemma le_trans_antisym:
  "\<lbrakk> le_trans x y; le_trans y x \<rbrakk> \<Longrightarrow> equiv_trans x y"
  unfolding equiv_trans_def by(simp)

lemma le_utrans_antisym:
  "\<lbrakk> le_utrans x y; le_utrans y x \<rbrakk> \<Longrightarrow> equiv_utrans x y"
  unfolding equiv_utrans_def by(simp)

lemma equiv_trans_comm[ac_simps]:
  "equiv_trans t u \<longleftrightarrow> equiv_trans u t"
  unfolding equiv_trans_def by(blast)

lemma equiv_utrans_comm[ac_simps]:
  "equiv_utrans t u \<longleftrightarrow> equiv_utrans u t"
  unfolding equiv_utrans_def by(blast)

lemma equiv_imp_le[intro]:
  "equiv_trans t u \<Longrightarrow> le_trans t u"
  unfolding equiv_trans_def by(clarify)

lemma equivu_imp_le[intro]:
  "equiv_utrans t u \<Longrightarrow> le_utrans t u"
  unfolding equiv_utrans_def by(clarify)

lemma equiv_imp_le_alt:
  "equiv_trans t u \<Longrightarrow> le_trans u t"
  by(force simp:ac_simps)

lemma equiv_uimp_le_alt:
  "equiv_utrans t u \<Longrightarrow> le_utrans u t"
  by(force simp:ac_simps)

lemma le_trans_equiv_rsp[simp]:
  "equiv_trans t u \<Longrightarrow> le_trans t v \<longleftrightarrow> le_trans u v"
  unfolding equiv_trans_def by(blast intro:le_trans_trans)

lemma le_utrans_equiv_rsp[simp]:
  "equiv_utrans t u \<Longrightarrow> le_utrans t v \<longleftrightarrow> le_utrans u v"
  unfolding equiv_utrans_def by(blast intro:le_utrans_trans)

lemma equiv_trans_le_trans[trans]:
  "\<lbrakk> equiv_trans t u; le_trans u v \<rbrakk> \<Longrightarrow> le_trans t v"
  by(simp)

lemma equiv_utrans_le_utrans[trans]:
  "\<lbrakk> equiv_utrans t u; le_utrans u v \<rbrakk> \<Longrightarrow> le_utrans t v"
  by(simp)

lemma le_trans_equiv_rsp_right[simp]:
  "equiv_trans t u \<Longrightarrow> le_trans v t \<longleftrightarrow> le_trans v u"
  unfolding equiv_trans_def by(blast intro:le_trans_trans)

lemma le_utrans_equiv_rsp_right[simp]:
  "equiv_utrans t u \<Longrightarrow> le_utrans v t \<longleftrightarrow> le_utrans v u"
  unfolding equiv_utrans_def by(blast intro:le_utrans_trans)

lemma le_trans_equiv_trans[trans]:
  "\<lbrakk> le_trans t u; equiv_trans u v \<rbrakk> \<Longrightarrow> le_trans t v"
  by(simp)

lemma le_utrans_equiv_utrans[trans]:
  "\<lbrakk> le_utrans t u; equiv_utrans u v \<rbrakk> \<Longrightarrow> le_utrans t v"
  by(simp)

lemma equiv_trans_trans[trans]:
  assumes xy: "equiv_trans x y"
      and yz: "equiv_trans y z"
  shows "equiv_trans x z"
proof(rule le_trans_antisym)
  from xy have "le_trans x y" by(blast)
  also from yz have "le_trans y z" by(blast)
  finally show "le_trans x z" .
  from yz have "le_trans z y" by(force simp:ac_simps)
  also from xy have "le_trans y x" by(force simp:ac_simps)
  finally show "le_trans z x" .
qed

lemma equiv_utrans_trans[trans]:
  assumes xy: "equiv_utrans x y"
      and yz: "equiv_utrans y z"
  shows "equiv_utrans x z"
proof(rule le_utrans_antisym)
  from xy have "le_utrans x y" by(blast)
  also from yz have "le_utrans y z" by(blast)
  finally show "le_utrans x z" .
  from yz have "le_utrans z y" by(force simp:ac_simps)
  also from xy have "le_utrans y x" by(force simp:ac_simps)
  finally show "le_utrans z x" .
qed

lemma equiv_trans_equiv_utrans[dest]:
  "equiv_trans t u \<Longrightarrow> equiv_utrans t u"
  by(auto)

subsection \<open>Healthy Transformers\<close>

subsubsection \<open>Feasibility\<close>

definition feasible :: "(('a \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> real)) \<Rightarrow> bool"
where     "feasible t \<longleftrightarrow> (\<forall>P b. bounded_by b P \<and> nneg P \<longrightarrow>
                               bounded_by b (t P) \<and> nneg (t P))"

text \<open>A @{term feasible} transformer preserves non-negativity, and bounds. A @{term feasible}
transformer always takes its argument `closer to 0' (or leaves it where it is). Note that any
particular value of the expectation may increase, but no element of the new expectation may exceed
any bound on the old. This is thus a relatively weak condition.\<close>

lemma feasibleI[intro]:
  "\<lbrakk> \<And>b P. \<lbrakk> bounded_by b P; nneg P \<rbrakk> \<Longrightarrow> bounded_by b (t P);
     \<And>b P. \<lbrakk> bounded_by b P; nneg P \<rbrakk> \<Longrightarrow> nneg (t P) \<rbrakk> \<Longrightarrow> feasible t"
  by(force simp:feasible_def)

lemma feasible_boundedD[dest]:
  "\<lbrakk> feasible t; bounded_by b P; nneg P \<rbrakk> \<Longrightarrow> bounded_by b (t P)"
  by(simp add:feasible_def)

lemma feasible_nnegD[dest]:
  "\<lbrakk> feasible t; bounded_by b P; nneg P \<rbrakk> \<Longrightarrow> nneg (t P)"
  by(simp add:feasible_def)

lemma feasible_sound[dest]:
  "\<lbrakk> feasible t; sound P \<rbrakk> \<Longrightarrow> sound (t P)"
  by(rule soundI, unfold sound_def, (blast)+)

lemma feasible_pr_0[simp]:
  fixes t::"('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"
  assumes ft: "feasible t"
  shows "t (\<lambda>x. 0) = (\<lambda>x. 0)"
proof(rule ext, rule antisym)
  fix s

  have "bounded_by 0 (\<lambda>_::'s. 0::real)" by(blast)
  with ft have "bounded_by 0 (t (\<lambda>_. 0))" by(blast)
  thus "t (\<lambda>_. 0) s \<le> 0" by(blast)

  have "nneg (\<lambda>_::'s. 0::real)" by(blast)
  with ft have "nneg (t (\<lambda>_. 0))" by(blast)
  thus "0 \<le> t (\<lambda>_. 0) s" by(blast)
qed

lemma feasible_id:
  "feasible (\<lambda>x. x)"
  unfolding feasible_def by(blast)

lemma feasible_bounded_by[dest]:
  "\<lbrakk> feasible t; sound P; bounded_by b P \<rbrakk> \<Longrightarrow> bounded_by b (t P)"
  by(auto)

lemma feasible_fixes_top:
  "feasible t \<Longrightarrow> t (\<lambda>s. 1) \<le> (\<lambda>s. (1::real))"
  by(drule bounded_byD2[OF feasible_bounded_by], auto)

lemma feasible_fixes_bot:
  assumes ft: "feasible t"
  shows "t (\<lambda>s. 0) = (\<lambda>s. 0)"
proof(rule antisym)
  have sb: "sound (\<lambda>s. 0)" by(auto)
  with ft show "(\<lambda>s. 0) \<le> t (\<lambda>s. 0)" by(auto)
  thm bound_of_const
  from sb have "bounded_by (bound_of (\<lambda>s. 0::real)) (\<lambda>s. 0)" by(auto)
  hence "bounded_by 0 (\<lambda>s. 0::real)" by(simp add:bound_of_const)
  with ft have "bounded_by 0 (t (\<lambda>s. 0))" by(auto)
  thus "t (\<lambda>s. 0) \<le> (\<lambda>s. 0)" by(auto)
qed

lemma feasible_unitaryD[dest]:
  assumes ft: "feasible t" and uP: "unitary P"
  shows "unitary (t P)"
proof(rule unitaryI)
  from uP have "sound P" by(auto)
  with ft show "sound (t P)" by(auto)
  from assms show "bounded_by 1 (t P)" by(auto)
qed

subsubsection \<open>Monotonicity\<close>

definition
  mono_trans :: "(('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real)) \<Rightarrow> bool"
where
  "mono_trans t \<equiv> \<forall>P Q. (sound P \<and> sound Q \<and> P \<le> Q) \<longrightarrow> t P \<le> t Q"

text \<open>Monotonicity allows us to compose transformers, and thus model sequential computation.
Recall the definition of predicate entailment (\autoref{s:entailment}) as less-than-or-equal. The
statement @{term "Q \<tturnstile> t R"} means that @{term Q} is everywhere below @{term "t R"}. For standard
expectations (\autoref{s:standard}), this simply means that @{term Q} \emph{implies} @{term "t R"},
the \emph{weakest precondition} of @{term R} under @{term t}.

Given another, monotonic, transformer @{term u}, we have that @{term "u Q \<tturnstile> u (t R)"}, or that the
weakest precondition of @{term Q} under @{term u} entails that of @{term R} under the composition
@{term "u o t"}.  If we additionally know that @{term "P \<tturnstile> u Q"}, then by transitivity we have
@{term "P \<tturnstile> u (t R)"}.  We thus derive a probabilistic form of the standard rule for sequential
composition: @{term "\<lbrakk> mono_trans t; P \<tturnstile> u Q; Q \<tturnstile> t R \<rbrakk> \<Longrightarrow> P \<tturnstile> u (t R)"}.
\<close>

lemma mono_transI[intro]:
  "\<lbrakk> \<And>P Q. \<lbrakk> sound P; sound Q; P \<le> Q \<rbrakk> \<Longrightarrow>  t P \<le> t Q \<rbrakk> \<Longrightarrow> mono_trans t"
  by(simp add:mono_trans_def)

lemma mono_transD[dest]:
  "\<lbrakk> mono_trans t; sound P; sound Q; P \<le> Q \<rbrakk> \<Longrightarrow> t P \<le> t Q"
  by(simp add:mono_trans_def)

subsubsection \<open>Scaling\<close>
text_raw \<open>\label{s:scaling}\<close>

text \<open>A healthy transformer commutes with scaling by a non-negative constant.\<close>

definition
  scaling :: "(('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real)) \<Rightarrow> bool"
where
  "scaling t \<equiv> \<forall>P c x. sound P \<and> 0 \<le> c \<longrightarrow> c * t P x = t (\<lambda>x. c * P x) x"

text \<open>The @{term scaling} and feasibility properties together allow us to treat transformers as a
complete lattice, when operating on bounded expectations. The action of a transformer on such a
bounded expectation is completely determined by its action on \emph{unitary} expectations (those
bounded by 1): @{term "t P s = bound_of P * t (\<lambda>s. P s / bound_of P) s"}. Feasibility in turn
ensures that the lattice of unitary expectations is closed under the action of a healthy
transformer. We take advantage of this fact in \autoref{s:induction}, in order to define the fixed
points of healthy transformers.\<close>

lemma scalingI[intro]:
  "\<lbrakk> \<And>P c x. \<lbrakk> sound P; 0 \<le> c \<rbrakk> \<Longrightarrow> c * t P x = t (\<lambda>x. c * P x) x \<rbrakk> \<Longrightarrow> scaling t"
  by(simp add:scaling_def)

lemma scalingD[dest]:
  "\<lbrakk> scaling t; sound P; 0 \<le> c \<rbrakk>  \<Longrightarrow> c * t P x = t (\<lambda>x. c * P x) x"
  by(simp add:scaling_def)

lemma right_scalingD:
  assumes st: "scaling t"
      and sP: "sound P"
      and nnc: "0 \<le> c"
  shows "t P s * c = t (\<lambda>s. P s * c) s"
proof -
  have "t P s * c = c * t P s" by(simp add:algebra_simps)
  also from assms have "... = t (\<lambda>s. c * P s) s" by(rule scalingD)
  also have "... = t (\<lambda>s. P s * c) s" by(simp add:algebra_simps)
  finally show ?thesis .
qed

subsubsection \<open>Healthiness\<close>

text \<open>Healthy transformers are feasible and monotonic, and respect scaling\<close>

definition
  healthy :: "(('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real)) \<Rightarrow> bool"
where
  "healthy t \<longleftrightarrow> feasible t \<and> mono_trans t \<and> scaling t"

lemma healthyI[intro]:
  "\<lbrakk> feasible t; mono_trans t; scaling t \<rbrakk> \<Longrightarrow> healthy t"
  by(simp add:healthy_def)

lemmas healthy_parts = healthyI[OF feasibleI mono_transI scalingI]

lemma healthy_monoD[dest]:
  "healthy t \<Longrightarrow> mono_trans t"
  by(simp add:healthy_def)

lemmas healthy_monoD2 = mono_transD[OF healthy_monoD]

lemma healthy_feasibleD[dest]:
  "healthy t \<Longrightarrow> feasible t"
  by(simp add:healthy_def)

lemma healthy_scalingD[dest]:
  "healthy t \<Longrightarrow> scaling t"
  by(simp add:healthy_def)

lemma healthy_bounded_byD[intro]:
  "\<lbrakk> healthy t; bounded_by b P; nneg P \<rbrakk> \<Longrightarrow> bounded_by b (t P)"
   by(blast)

lemma healthy_bounded_byD2:
  "\<lbrakk> healthy t; bounded_by b P; sound P \<rbrakk> \<Longrightarrow> bounded_by b (t P)"
  by(blast)

lemma healthy_boundedD[dest,simp]:
  "\<lbrakk> healthy t; sound P \<rbrakk> \<Longrightarrow> bounded (t P)"
  by(blast)

lemma healthy_nnegD[dest,simp]:
  "\<lbrakk> healthy t; sound P \<rbrakk> \<Longrightarrow> nneg (t P)"
  by(blast intro!:feasible_nnegD)

lemma healthy_nnegD2[dest,simp]:
  "\<lbrakk> healthy t; bounded_by b P; nneg P \<rbrakk> \<Longrightarrow> nneg (t P)"
  by(blast)

lemma healthy_sound[intro]:
  "\<lbrakk> healthy t; sound P \<rbrakk> \<Longrightarrow> sound (t P)"
  by(rule soundI, blast, blast intro:feasible_nnegD)

lemma healthy_unitary[intro]:
  "\<lbrakk> healthy t; unitary P \<rbrakk> \<Longrightarrow> unitary (t P)"
  by(blast intro!:unitaryI dest:unitary_bound healthy_bounded_byD)

lemma healthy_id[simp,intro!]:
  "healthy id"
  by(simp add:healthyI feasibleI mono_transI scalingI)

lemmas healthy_fixes_bot = feasible_fixes_bot[OF healthy_feasibleD]

text \<open>Some additional results on @{term le_trans}, specific to
@{term healthy} transformers.\<close>

lemma le_trans_bot[intro,simp]:
  "healthy t \<Longrightarrow> le_trans (\<lambda>P s. 0) t"
  by(blast intro:le_funI)

lemma le_trans_top[intro,simp]:
  "healthy t \<Longrightarrow> le_trans t (\<lambda>P s. bound_of P)"
  by(blast intro!:le_transI[OF le_funI])

lemma healthy_pr_bot[simp]:
  "healthy t \<Longrightarrow> t (\<lambda>s. 0) = (\<lambda>s. 0)"
  by(blast intro:feasible_pr_0)

text \<open>The first significant result is that healthiness is preserved by equivalence:\<close>

lemma healthy_equivI:
  fixes t::"('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real" and u
  assumes equiv:   "equiv_trans t u"
      and healthy: "healthy t"
  shows "healthy u"
proof
  have le_t_u: "le_trans t u" by(blast intro:equiv)
  have le_u_t: "le_trans u t" by(simp add:equiv_imp_le ac_simps equiv)
  from equiv have eq_u_t: "equiv_trans u t" by(simp add:ac_simps)

  show "feasible u"
  proof
    fix b and P::"'s \<Rightarrow> real"
    assume bP: "bounded_by b P" and nP: "nneg P"
    hence sP: "sound P" by(blast)
    with healthy have "\<And>s. 0 \<le> t P s" by(blast)
    also from sP and le_t_u have "\<And>s. ... s \<le> u P s" by(blast)
    finally show "nneg (u P)" by(blast)

    from sP and le_u_t have "\<And>s. u P s \<le> t P s" by(blast)
    also from healthy and sP and bP have "\<And>s. t P s \<le> b" by(blast)
    finally show "bounded_by b (u P)" by(blast)
  qed

  show "mono_trans u"
  proof
    fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real"
    assume sP: "sound P" and sQ: "sound Q"
       and le: "P \<tturnstile> Q"
    from sP and le_u_t have "u P \<tturnstile> t P" by(blast)
    also from sP and sQ and le and healthy have "t P \<tturnstile> t Q" by(blast)
    also from sQ and le_t_u have "t Q \<tturnstile> u Q" by(blast)
    finally show "u P \<tturnstile> u Q" .
  qed

  show "scaling u"
  proof
    fix P::"'s \<Rightarrow> real" and c::real and x::'s
    assume sound: "sound P"
       and pos:   "0 \<le> c"

    hence "bounded_by (c * bound_of P) (\<lambda>x. c * P x)"
      by(blast intro!:mult_left_mono dest!:less_imp_le)
    hence sc_bounded: "bounded (\<lambda>x. c * P x)"
      by(blast)
    moreover from sound and pos have sc_nneg: "nneg (\<lambda>x. c * P x)"
      by(blast intro:mult_nonneg_nonneg less_imp_le)
    ultimately have sc_sound: "sound (\<lambda>x. c * P x)" by(blast)
        
    show "c * u P x = u (\<lambda>x. c * P x) x"
    proof -
      from sound have "c * u P x = c * t P x"
        by(simp add:equiv_transD[OF eq_u_t])

      also have "... = t (\<lambda>x. c * P x) x"
        using healthy and sound and pos
        by(blast intro: scalingD)

      also from sc_sound and equiv have "... = u (\<lambda>x. c * P x) x"
        by(blast intro:fun_cong)

      finally show ?thesis .
    qed
  qed
qed

lemma healthy_equiv:
  "equiv_trans t u \<Longrightarrow> healthy t \<longleftrightarrow> healthy u"
  by(rule iffI, rule healthy_equivI, assumption+,
     simp add:healthy_equivI ac_simps)

lemma healthy_scale:
  fixes t::"('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"
  assumes ht: "healthy t" and nc: "0 \<le> c" and bc: "c \<le> 1"
  shows "healthy (\<lambda>P s. c * t P s)"
proof
  show "feasible (\<lambda>P s. c * t P s)"
  proof
    fix b and P::"'s \<Rightarrow> real"
    assume nnP: "nneg P" and bP: "bounded_by b P"

    from ht nnP bP have "\<And>s. t P s \<le> b" by(blast)
    with nc have "\<And>s. c * t P s \<le> c * b" by(blast intro:mult_left_mono)
    also {
      from nnP and bP have "0 \<le> b" by(auto)
      with bc have "c * b \<le> 1 * b" by(blast intro:mult_right_mono)
      hence "c * b \<le> b" by(simp)
    }
    finally show "bounded_by b (\<lambda>s. c * t P s)" by(blast)

    from ht nnP bP have "\<And>s. 0 \<le> t P s" by(blast)
    with nc have "\<And>s. 0 \<le> c * t P s" by(rule mult_nonneg_nonneg)
    thus "nneg (\<lambda>s. c * t P s)" by(blast)
  qed
  show "mono_trans (\<lambda>P s. c * t P s)"
  proof
    fix P::"'s \<Rightarrow> real" and Q
    assume sP: "sound P" and sQ: "sound Q" and le: "P \<tturnstile> Q"
    with ht have "\<And>s. t P s \<le> t Q s" by(auto intro:le_funD)
    with nc have "\<And>s. c * t P s \<le> c * t Q s"
      by(blast intro:mult_left_mono)
    thus "\<lambda>s. c * t P s \<tturnstile> \<lambda>s. c * t Q s" by(blast)
  qed
  from ht show "scaling (\<lambda>P s. c * t P s)"
    by(auto simp:scalingD healthy_scalingD ht)
qed

lemma healthy_top[iff]:
  "healthy (\<lambda>P s. bound_of P)"
  by(auto intro!:healthy_parts)

lemma healthy_bot[iff]:
  "healthy (\<lambda>P s. 0)"
  by(auto intro!:healthy_parts)

text \<open>This weaker healthiness condition is for the liberal (wlp) semantics. We only insist that
the transformer preserves \emph{unitarity} (bounded by 1), and drop scaling (it is unnecessary in
establishing the lattice structure here, unlike for the strict semantics).\<close>

definition
  nearly_healthy :: "(('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real)) \<Rightarrow> bool"
where
  "nearly_healthy t \<longleftrightarrow> (\<forall>P. unitary P \<longrightarrow> unitary (t P)) \<and>
                        (\<forall>P Q. unitary P \<longrightarrow> unitary Q \<longrightarrow> P \<tturnstile> Q \<longrightarrow> t P \<tturnstile> t Q)"

lemma nearly_healthyI[intro]:
  "\<lbrakk> \<And>P. unitary P \<Longrightarrow> unitary (t P);
     \<And>P Q. \<lbrakk> unitary P; unitary Q; P \<tturnstile> Q \<rbrakk> \<Longrightarrow> t P \<tturnstile> t Q \<rbrakk> \<Longrightarrow> nearly_healthy t"
  by(simp add:nearly_healthy_def)

lemma nearly_healthy_monoD[dest]:
  "\<lbrakk> nearly_healthy t; P \<tturnstile> Q; unitary P; unitary Q \<rbrakk> \<Longrightarrow> t P \<tturnstile> t Q"
  by(simp add:nearly_healthy_def)

lemma nearly_healthy_unitaryD[dest]:
  "\<lbrakk> nearly_healthy t; unitary P \<rbrakk> \<Longrightarrow> unitary (t P)"
  by(simp add:nearly_healthy_def)

lemma healthy_nearly_healthy[dest]:
  assumes ht: "healthy t"
  shows "nearly_healthy t"
  by(intro nearly_healthyI, auto intro:mono_transD[OF healthy_monoD, OF ht] ht)

lemmas nearly_healthy_id[iff] =
  healthy_nearly_healthy[OF healthy_id, unfolded id_def]

subsection \<open>Sublinearity\<close>

text \<open>As already mentioned, the core healthiness property (aside from feasibility and continuity)
for transformers is \emph{sublinearity}: The transformation of a quasi-linear combination of sound
expectations is greater than the same combination applied to the transformation of the expectations
themselves. The term @{term "x \<ominus> y"} represents \emph{truncated subtraction} i.e. @{term "max (x-y)
0"} (see \autoref{s:trunc_sub}).\<close>

definition sublinear ::
  "(('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real)) \<Rightarrow> bool"
where
  "sublinear t \<longleftrightarrow> (\<forall>a b c P Q s. (sound P \<and> sound Q \<and> 0 \<le> a \<and> 0 \<le> b \<and> 0 \<le> c) \<longrightarrow>
                  a * t P s + b * t Q s \<ominus> c
                  \<le> t (\<lambda>s'. a * P s' + b * Q s' \<ominus> c) s)"

lemma sublinearI[intro]:
  "\<lbrakk> \<And>a b c P Q s. \<lbrakk> sound P; sound Q; 0 \<le> a; 0 \<le> b; 0 \<le> c \<rbrakk> \<Longrightarrow>
     a * t P s + b * t Q s \<ominus> c \<le>
     t (\<lambda>s'. a * P s' + b * Q s' \<ominus> c) s \<rbrakk> \<Longrightarrow> sublinear t"
  by(simp add:sublinear_def)

lemma sublinearD[dest]:
  "\<lbrakk> sublinear t; sound P; sound Q; 0 \<le> a; 0 \<le> b; 0 \<le> c \<rbrakk> \<Longrightarrow>
   a * t P s + b * t Q s \<ominus> c \<le>
   t (\<lambda>s'. a * P s' + b * Q s' \<ominus> c) s"
  by(simp add:sublinear_def)

text \<open>It is easier to see the relevance of sublinearity by breaking it into several component
properties, as in the following sections.\<close>

subsubsection \<open>Sub-additivity\<close>
text_raw \<open>\label{s:subadd}\<close>

definition sub_add ::
  "(('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real)) \<Rightarrow> bool"
where
  "sub_add t \<longleftrightarrow> (\<forall>P Q s. (sound P \<and> sound Q) \<longrightarrow>
                t P s + t Q s \<le> t (\<lambda>s'. P s' + Q s') s)"

text \<open>
\begin{figure}
\begin{center}
\begin{displaymath}
\begin{xy}
0;<1cm,0cm>:
(-0.25,0); (10,0) **\dir{-} *\dir{>},
(0,-0.25); (0,6) **\dir{-} *\dir{>},
(0.1,5.5)="Ps";  (9.9,1.5)="Pe"  **\dir{-} ?(0.1)+<0em,1em> *{P},
(0.1,4.0)="tPs"; (9.9,1.0)="tPe" **\dir{} ?(0.1)+<0em,1em> *{tP},
(0.1,0.5)="uPs"; (9.9,5.0)="uPe" **\dir{} ?(0.9)+<0em,1em> *{uP}
?!{"tPs";"tPe"}="inter";
    "tPs" **\dir{--}, "uPe" **\dir{--},
    "tPe" **\dir{-}, "uPs" **\dir{-} ?(0.5)+<0em,1.5em> *{Q=tP \sqcap uP},
(1,0)="x"; "x"-<0em,1em>*{x};
"x"; (1,6) **{}, ?!{"uPs";"uPe"}="uPx" *{\bullet} -<0em,1em>*{Q(x)},
(9,0)="y"; "y"-<0em,1em>*{y};
"y"; (9,6) **{}, ?!{"tPs";"tPe"}="tPy" *{\bullet} -<0em,1em>*{Q(y)},
"uPx"; "tPy" **\dir{.},
(5,0)="xy"; (5,6) **{},
    ?!{"tPs";"tPe"}="tPxy" *{\bullet} -<0em,1.5em>*{Q(\frac{x+y}{2})},
    ?!{"uPx";"tPy"}="tPuP" *{\bullet} -<0em,1em>*{\frac{Q(x)+Q(y)}{2}},
\end{xy}
\end{displaymath}
\end{center}
\caption{\label{f:subadd_plot}A graphical depiction of sub-additivity as convexity.}
\end{figure}
\<close>

text \<open>Sub-additivity, together with scaling (\autoref{s:scaling}) gives the \emph{linear} portion
of sublinearity. Together, these two properties are equivalent to \emph{convexity}, as
\autoref{f:subadd_plot} illustrates by analogy.

Here $P$ is an affine function (expectation) @{typ "real \<Rightarrow> real"}, restricted to some finite
interval. In practice the state space (the left-hand type) is typically discrete and
multi-dimensional, but on the reals we have a convenient geometrical intuition. The lines $tP$ and
$uP$ represent the effect of two healthy transformers (again affine). Neither monotonicity nor
scaling are represented, but both are feasible: Both lines are bounded above by the greatest value
of $P$.

The curve $Q$ is the pointwise minimum of $tP$ and $tQ$, written $tP \sqcap tQ$.  This is, not
coincidentally, the syntax for a binary nondeterministic choice in pGCL: The probability that some
property is established by the choice between programs $a$ and $b$ cannot be guaranteed to be any
higher than either the probability under $a$, or that under $b$.

The original curve, $P$, is trivially convex---it is linear.  Also, both $t$ and $u$, and the
operator $\sqcap$ preserve convexity.  A probabilistic choice will also preserve it.  The
preservation of convexity is a property of sub-additive transformers that respect scaling.  Note
the form of the definition of convexity:
\begin{displaymath}
\forall x,y. \frac{Q(x) + Q(y)}{2} \le Q(\frac{x+y}{2})
\end{displaymath}
Were we to replace $Q$ by some sub-additive transformer $v$, and $x$ and $y$ by expectations $R$
and $S$, the equivalent expression:
\begin{displaymath}
\frac{vR + vS}{2} \le v(\frac{R+S}{2})
\end{displaymath}
Can be rewritten, using scaling, to:
\begin{displaymath}
\frac{1}{2}(vR + vS) \le \frac{1}{2}v(R+S)
\end{displaymath}
Which holds everywhere exactly when $v$ is sub-additive i.e.:
\begin{displaymath}
vR + vS \le v(R+S)
\end{displaymath}
\<close>

lemma sub_addI[intro]:
  "\<lbrakk> \<And>P Q s. \<lbrakk> sound P; sound Q \<rbrakk> \<Longrightarrow>
             t P s + t Q s \<le> t (\<lambda>s'. P s' + Q s') s \<rbrakk> \<Longrightarrow> sub_add t"
  by(simp add:sub_add_def)

lemma sub_addI2:
  "\<lbrakk>\<And>P Q. \<lbrakk> sound P; sound Q \<rbrakk> \<Longrightarrow>
          \<lambda>s. t P s + t Q s \<tturnstile> t (\<lambda>s. P s + Q s)\<rbrakk> \<Longrightarrow>
   sub_add t"
  by(auto)

lemma sub_addD[dest]:
  "\<lbrakk> sub_add t; sound P; sound Q \<rbrakk> \<Longrightarrow> t P s + t Q s \<le> t (\<lambda>s'. P s' + Q s') s"
  by(simp add:sub_add_def)

lemma equiv_sub_add:
  fixes t::"('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"
  assumes eq: "equiv_trans t u"
      and sa: "sub_add t"
  shows "sub_add u"
proof
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::"'s"
  assume sP: "sound P" and sQ: "sound Q"

  with eq have "u P s + u Q s = t P s + t Q s"
    by(simp add:equiv_transD)
  also from sP sQ sa have "t P s + t Q s \<le> t (\<lambda>s. P s + Q s) s"
    by(auto)
  also {
    from sP sQ have "sound (\<lambda>s. P s + Q s)" by(auto)
    with eq have "t (\<lambda>s. P s + Q s) s = u (\<lambda>s. P s + Q s) s"
      by(simp add:equiv_transD)
  }
  finally show "u P s + u Q s \<le> u (\<lambda>s. P s + Q s) s" .
qed

text \<open>Sublinearity and feasibility imply sub-additivity.\<close>
lemma sublinear_subadd:
  fixes t::"('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"
  assumes slt: "sublinear t"
      and ft:  "feasible t"
  shows "sub_add t"
proof
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s
  assume sP: "sound P" and sQ: "sound Q"

  with ft have "sound (t P)" "sound (t Q)" by(auto)
  hence "0 \<le> t P s" and "0 \<le> t Q s" by(auto)
  hence "0 \<le> t P s + t Q s" by(auto)
  hence "... = ...\<ominus> 0" by(simp)

  also from sP sQ
  have "... \<le> t (\<lambda>s. P s + Q s \<ominus> 0) s"
    by(rule sublinearD[OF slt, where a=1 and b=1 and c=0, simplified])

  also {
    from sP sQ have "\<And>s. 0 \<le> P s" and "\<And>s. 0 \<le> Q s" by(auto)
    hence "\<And>s. 0 \<le> P s + Q s" by(auto)
    hence "t (\<lambda>s. P s + Q s \<ominus> 0) s = t (\<lambda>s. P s + Q s) s"
      by(simp)
  }

  finally show "t P s + t Q s \<le> t (\<lambda>s. P s + Q s) s" .
qed

text \<open>A few properties following from sub-additivity:\<close>
lemma standard_negate:
  assumes ht: "healthy t"
      and sat: "sub_add t"
  shows "t \<guillemotleft>P\<guillemotright> s + t \<guillemotleft>\<N> P\<guillemotright> s \<le> 1"
proof -
  from sat have "t \<guillemotleft>P\<guillemotright> s + t \<guillemotleft>\<N> P\<guillemotright> s \<le> t (\<lambda>s. \<guillemotleft>P\<guillemotright> s + \<guillemotleft>\<N> P\<guillemotright> s) s" by(auto)
  also have "... = t (\<lambda>s. 1) s" by(simp add:negate_embed)
  also {
    from ht have "bounded_by 1 (t (\<lambda>s. 1))" by(auto)
    hence "t (\<lambda>s. 1) s \<le> 1" by(auto)
  }
  finally show ?thesis .
qed

lemma sub_add_sum:
  fixes t::"'s trans" and S::"'a set"
  assumes sat: "sub_add t"
      and ht: "healthy t"
      and sP: "\<And>x. sound (P x)"
  shows "(\<lambda>x. \<Sum>y\<in>S. t (P y) x) \<le> t (\<lambda>x. \<Sum>y\<in>S. P y x)"
proof(cases "infinite S", simp_all add:ht)
  assume fS: "finite S"
  show ?thesis
  proof(rule finite_induct[OF fS le_funI le_funI], simp_all)
    fix s::'s
    from ht have "sound (t (\<lambda>s. 0))" by(auto)
    thus "0 \<le> t (\<lambda>s. 0) s" by(auto)

    fix F::"'a set" and x::'a
    assume IH: "\<lambda>a. \<Sum>y\<in>F. t (P y) a \<tturnstile> t (\<lambda>x. \<Sum>y\<in>F. P y x)"
    hence "t (P x) s + (\<Sum>y\<in>F. t (P y) s) \<le>
           t (P x) s + t (\<lambda>x. \<Sum>y\<in>F. P y x) s"
      by(auto intro:add_left_mono)
    also from sat sP
    have "... \<le> t (\<lambda>xa. P x xa + (\<Sum>y\<in>F. P y xa)) s"
      by(auto intro!:sub_addD[OF sat] sum_sound)
    finally
    show "t (P x) s + (\<Sum>y\<in>F. t (P y) s) \<le>
          t (\<lambda>xa. P x xa + (\<Sum>y\<in>F. P y xa)) s" .
  qed
qed

lemma sub_add_guard_split:
  fixes t::"'s::finite trans" and P::"'s expect" and s::'s
  assumes sat: "sub_add t"
      and ht: "healthy t"
      and sP: "sound P"
  shows "(\<Sum>y\<in>{s. G s}.  P y * t \<guillemotleft> \<lambda>z. z = y \<guillemotright> s) +
         (\<Sum>y\<in>{s. \<not>G s}. P y * t \<guillemotleft> \<lambda>z. z = y \<guillemotright> s) \<le> t P s"
proof -
  have "{s. G s} \<inter> {s. \<not>G s} = {}" by(blast)
  hence "(\<Sum>y\<in>{s. G s}.  P y * t \<guillemotleft> \<lambda>z. z = y \<guillemotright> s) +
         (\<Sum>y\<in>{s. \<not>G s}. P y * t \<guillemotleft> \<lambda>z. z = y \<guillemotright> s) =
         (\<Sum>y\<in>({s. G s} \<union> {s. \<not>G s}). P y * t \<guillemotleft> \<lambda>z. z = y \<guillemotright> s)"
    by(auto intro: sum.union_disjoint[symmetric])
  also {
    have "{s. G s} \<union> {s. \<not>G s} = UNIV" by (blast)
    hence "(\<Sum>y\<in>({s. G s} \<union> {s. \<not>G s}). P y * t \<guillemotleft> \<lambda>z. z = y \<guillemotright> s) =
           (\<lambda>x. \<Sum>y\<in>UNIV. P y * t (\<lambda>x. \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) x) s"
      by(simp)
  }
  also {
    from sP have "\<And>y. 0 \<le> P y" by(auto)
    with healthy_scalingD[OF ht]
    have "(\<lambda>x. \<Sum>y\<in>UNIV. P y * t (\<lambda>x. \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) x) s =
          (\<lambda>x. \<Sum>y\<in>UNIV. t (\<lambda>x. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) x) s"
      by(simp add:scalingD)
  }
  also {
    from sat ht sP
    have "(\<lambda>x. \<Sum>y\<in>UNIV. t (\<lambda>x. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) x) \<le>
          t (\<lambda>x. \<Sum>y\<in>UNIV. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x)"
      by(intro sub_add_sum sound_intros, auto)
    hence "(\<lambda>x. \<Sum>y\<in>UNIV. t (\<lambda>x. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) x) s \<le>
          t (\<lambda>x. \<Sum>y\<in>UNIV. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) s" by(auto)
  }
  also {
    have rw1: "(\<lambda>x. \<Sum>y\<in>UNIV. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) =
               (\<lambda>x. \<Sum>y\<in>UNIV. if y = x then P y else 0)"
      by (rule ext [OF sum.cong]) auto
    also from sP have "... \<tturnstile> P"
      by(cases "finite (UNIV::'s set)", auto simp:sum.delta)
    finally have leP: "\<lambda>x. \<Sum>y\<in>UNIV. P y * \<guillemotleft> \<lambda>z. z = y \<guillemotright> x \<tturnstile> P" .
    moreover have "sound (\<lambda>x. \<Sum>y\<in>UNIV. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x)"
    proof(intro soundI2 bounded_byI nnegI sum_nonneg ballI)
      fix x
      from leP have "(\<Sum>y\<in>UNIV. P y * \<guillemotleft> \<lambda>z. z = y \<guillemotright> x) \<le> P x" by(auto)
      also from sP have "... \<le> bound_of P" by(auto)
      finally show "(\<Sum>y\<in>UNIV. P y * \<guillemotleft> \<lambda>z. z = y \<guillemotright> x) \<le> bound_of P" .
      fix y
      from sP show "0 \<le> P y * \<guillemotleft> \<lambda>z. z = y \<guillemotright> x"
        by(auto intro:mult_nonneg_nonneg)
    qed
    ultimately have "t (\<lambda>x. \<Sum>y\<in>UNIV. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) s \<le> t P s"
      using sP by(auto intro:le_funD[OF mono_transD, OF healthy_monoD, OF ht])
  }
  finally show ?thesis .
qed

subsubsection \<open>Sub-distributivity\<close>

definition sub_distrib ::
  "(('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real)) \<Rightarrow> bool"
where
  "sub_distrib t \<longleftrightarrow> (\<forall>P s. sound P \<longrightarrow> t P s \<ominus> 1 \<le> t (\<lambda>s'. P s' \<ominus> 1) s)"

lemma sub_distribI[intro]:
  "\<lbrakk> \<And>P s. sound P \<Longrightarrow> t P s \<ominus> 1 \<le> t (\<lambda>s'. P s' \<ominus> 1) s \<rbrakk> \<Longrightarrow> sub_distrib t"
  by(simp add:sub_distrib_def)
  
lemma sub_distribI2:
  "\<lbrakk> \<And>P. sound P \<Longrightarrow> \<lambda>s. t P s \<ominus> 1 \<tturnstile> t (\<lambda>s. P s \<ominus> 1) \<rbrakk> \<Longrightarrow> sub_distrib t"
  by(auto)

lemma sub_distribD[dest]:
  "\<lbrakk> sub_distrib t; sound P \<rbrakk> \<Longrightarrow> t P s \<ominus> 1 \<le> t (\<lambda>s'. P s' \<ominus> 1) s"
  by(simp add:sub_distrib_def)

lemma equiv_sub_distrib:
  fixes t::"('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"
  assumes eq: "equiv_trans t u"
      and sd: "sub_distrib t"
  shows "sub_distrib u"
proof
  fix P::"'s \<Rightarrow> real" and s::"'s"
  assume sP: "sound P"

  with eq have "u P s \<ominus> 1 = t P s \<ominus> 1" by(simp add:equiv_transD)
  also from sP sd have "... \<le> t (\<lambda>s. P s \<ominus> 1) s" by(auto)
  also from sP eq have "... = u (\<lambda>s. P s \<ominus> 1) s"
    by(simp add:equiv_transD tminus_sound)
  finally show "u P s \<ominus> 1 \<le> u (\<lambda>s. P s \<ominus> 1) s" .
qed

text \<open>Sublinearity implies sub-distributivity:\<close>
lemma sublinear_sub_distrib:
  fixes t::"('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"
  assumes slt: "sublinear t"
  shows "sub_distrib t"
proof
  fix P::"'s \<Rightarrow> real" and s::'s
  assume sP: "sound P"
  moreover have "sound (\<lambda>_. 0)" by(auto)
  ultimately show "t P s \<ominus> 1 \<le> t (\<lambda>s. P s \<ominus> 1) s"
    by(rule sublinearD[OF slt, where a=1 and b=0 and c=1, simplified])
qed

text \<open>Healthiness, sub-additivity and sub-distributivity imply
  sublinearity.  This is how we usually show sublinearity.\<close>
lemma sd_sa_sublinear:
  fixes t::"('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"
  assumes sdt: "sub_distrib t" and sat: "sub_add t" and ht: "healthy t"
  shows "sublinear t"
proof
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s::'s
  and a::real and b::real and c::real
  assume sP: "sound P" and sQ: "sound Q"
     and nna: "0 \<le> a" and nnb: "0 \<le> b" and nnc: "0 \<le> c"

  from ht sP sQ nna nnb
  have saP: "sound (\<lambda>s. a * P s)" and staP: "sound (\<lambda>s. a * t P s)"
   and sbQ: "sound (\<lambda>s. b * Q s)" and stbQ: "sound (\<lambda>s. b * t Q s)"
    by(auto intro:sc_sound)
  hence sabPQ:  "sound (\<lambda>s. a * P s + b * Q s)"
    and stabPQ: "sound (\<lambda>s. a * t P s + b * t Q s)"
    by(auto intro:sound_sum)

  from ht sP sQ nna nnb
  have "a * t P s + b * t Q s = t (\<lambda>s. a * P s) s + t (\<lambda>s. b * Q s) s"
    by(simp add:scalingD healthy_scalingD)
  also from saP sbQ sat
  have "t (\<lambda>s. a * P s) s + t (\<lambda>s. b * Q s) s \<le>
        t (\<lambda>s. a * P s + b * Q s) s" by(blast)
  finally
  have notm: "a * t P s + b * t Q s \<le> t (\<lambda>s. a * P s + b * Q s) s" .

  show "a * t P s + b * t Q s \<ominus> c \<le> t (\<lambda>s'. a * P s' + b * Q s' \<ominus> c) s"
  proof(cases "c = 0")
    case True note z = this
    from stabPQ have "\<And>s. 0 \<le> a * t P s + b * t Q s" by(auto)
    moreover from sabPQ
    have "\<And>s. 0 \<le> a * P s + b * Q s" by(auto)
    ultimately show ?thesis by(simp add:z notm)
  next
    case False note nz = this
    from nz and nnc have nni: "0 \<le> inverse c" by(auto)

    have "\<And>s. (inverse c * a) * P s + (inverse c * b) * Q s =
              inverse c * (a * P s + b * Q s)"
      by(simp add: divide_simps)
    with sabPQ and nni
    have si: "sound (\<lambda>s. (inverse c * a) * P s + (inverse c * b) * Q s)"
      by(auto intro:sc_sound)
    hence sim: "sound (\<lambda>s. (inverse c * a) * P s + (inverse c * b) * Q s \<ominus> 1)"
      by(auto intro!:tminus_sound)

    from nz
    have "a * t P s + b * t Q s \<ominus> c =
          (c * inverse c) * a * t P s +
          (c * inverse c) * b * t Q s \<ominus> c"
      by(simp)
    also
    have "... = c * (inverse c * a * t P s) +
                c * (inverse c * b * t Q s) \<ominus> c"
      by(simp add:field_simps)
    also from nnc
    have "... = c * (inverse c * a * t P s + inverse c * b * t Q s \<ominus> 1)"
      by(simp add:distrib_left tminus_left_distrib)
    also {
      have X: "\<And>s. (inverse c * a) * t P s + (inverse c * b) * t Q s =
                   inverse c * (a * t P s + b * t Q s)" by(simp add: divide_simps)
      also from nni and notm
      have "inverse c * (a * t P s + b * t Q s) \<le>
            inverse c * (t (\<lambda>s. a * P s + b * Q s) s)"
        by(blast intro:mult_left_mono)
      also from nni ht sabPQ
      have "... = t (\<lambda>s. (inverse c * a) * P s + (inverse c * b) * Q s) s"
        by(simp add:scalingD[OF healthy_scalingD, OF ht] algebra_simps)
      finally
      have "(inverse c * a) * t P s + (inverse c * b) * t Q s \<ominus> 1 \<le>
            t (\<lambda>s. (inverse c * a) * P s + (inverse c * b) * Q s) s \<ominus> 1"
        by(rule tminus_left_mono)
      also {
        from sdt si
        have "t (\<lambda>s. (inverse c * a) * P s + (inverse c * b) * Q s) s \<ominus> 1 \<le>
              t (\<lambda>s. (inverse c * a) * P s + (inverse c * b) * Q s \<ominus> 1) s"
          by(blast)
      }
      finally
      have "c * (inverse c * a * t P s + inverse c * b * t Q s \<ominus> 1) \<le>
            c * t (\<lambda>s. inverse c * a * P s + inverse c * b * Q s \<ominus> 1) s"
        using nnc by(blast intro:mult_left_mono)
    }
    also from nnc ht sim
    have "c * t (\<lambda>s. inverse c * a * P s + inverse c * b * Q s \<ominus> 1) s
          = t (\<lambda>s. c * (inverse c * a * P s + inverse c * b * Q s \<ominus> 1)) s"
      by(simp add:scalingD healthy_scalingD)
    also from nnc
    have "... = t (\<lambda>s. c * (inverse c * a * P s) +
                       c * (inverse c * b * Q s) \<ominus> c) s"
      by(simp add:distrib_left tminus_left_distrib)
    also have "... = t (\<lambda>s. (c * inverse c) * a * P s +
                            (c * inverse c) * b * Q s \<ominus> c) s"
      by(simp add:field_simps)
    finally
    show "a * t P s + b * t Q s \<ominus> c \<le> t (\<lambda>s'. a * P s' + b * Q s' \<ominus> c) s"
      using nz by(simp)
  qed
qed

subsubsection \<open>Sub-conjunctivity\<close>
definition
  sub_conj :: "(('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real) \<Rightarrow> bool"
where
  "sub_conj t \<equiv> \<forall>P Q. (sound P \<and> sound Q) \<longrightarrow>
                       t P && t Q \<tturnstile> t (P && Q)"

lemma sub_conjI[intro]:
  "\<lbrakk> \<And>P Q. \<lbrakk> sound P; sound Q \<rbrakk> \<Longrightarrow>
           t P && t Q \<tturnstile> t (P && Q) \<rbrakk> \<Longrightarrow> sub_conj t"
  unfolding sub_conj_def by(simp)

lemma sub_conjD[dest]:
  "\<lbrakk> sub_conj t; sound P; sound Q \<rbrakk> \<Longrightarrow> t P && t Q \<tturnstile> t (P && Q)"
  unfolding sub_conj_def by(simp)

lemma sub_conj_wp_twice:
  fixes f::"'s \<Rightarrow> (('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real)"
  assumes all: "\<forall>s. sub_conj (f s)"
  shows "sub_conj (\<lambda>P s. f s P s)"
proof(rule sub_conjI, rule le_funI)
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real" and s
  assume sP: "sound P" and sQ: "sound Q"

  have "((\<lambda>s. f s P s) && (\<lambda>s. f s Q s)) s = (f s P && f s Q) s"
    by(simp add:exp_conj_def)
  also {
    from all have "sub_conj (f s)" by(blast)
    with sP and sQ have "(f s P && f s Q) s \<le> f s (P && Q) s"
      by(blast)
  }
  finally show "((\<lambda>s. f s P s) && (\<lambda>s. f s Q s)) s \<le> f s (P && Q) s" .
qed

text \<open>Sublinearity implies sub-conjunctivity:\<close>
lemma sublinear_sub_conj:
  fixes t::"('s \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"
  assumes slt: "sublinear t"
  shows "sub_conj t"
proof(rule sub_conjI, rule le_funI, unfold exp_conj_def pconj_def)
  fix P::"'s \<Rightarrow> real" and Q::"'s \<Rightarrow> real"and s::'s
  assume sP: "sound P" and sQ: "sound Q"
  thus "t P s + t Q s \<ominus> 1 \<le> t (\<lambda>s. P s + Q s \<ominus> 1) s"
    by(rule sublinearD[OF slt, where a=1 and b=1 and c=1, simplified])
qed

subsubsection \<open>Sublinearity under equivalence\<close>

text \<open>Sublinearity is preserved by equivalence.\<close>
lemma equiv_sublinear:
  "\<lbrakk> equiv_trans t u; sublinear t; healthy t \<rbrakk> \<Longrightarrow> sublinear u"
  by(iprover intro:sd_sa_sublinear healthy_equivI
             dest:equiv_sub_distrib equiv_sub_add
                  sublinear_sub_distrib sublinear_subadd
                  healthy_feasibleD)

subsection \<open>Determinism\<close>

text \<open>Transformers which are both additive, and maximal among those that
satisfy feasibility are \emph{deterministic}, and will turn out to be maximal
in the refinement order.\<close>

subsubsection \<open>Additivity\<close>
text \<open>Full additivity is not generally satisfied.  It holds for
  (sub-)probabilistic transformers however.\<close>
definition
  additive :: "(('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
where
  "additive t \<equiv> \<forall>P Q. (sound P \<and> sound Q) \<longrightarrow>
                      t (\<lambda>s. P s + Q s) = (\<lambda>s. t P s + t Q s)"

lemma additiveD:
  "\<lbrakk> additive t; sound P; sound Q \<rbrakk> \<Longrightarrow> t (\<lambda>s. P s + Q s) = (\<lambda>s. t P s + t Q s)"
  by(simp add:additive_def)

lemma additiveI[intro]:
  "\<lbrakk> \<And>P Q s. \<lbrakk> sound P; sound Q \<rbrakk> \<Longrightarrow> t (\<lambda>s. P s + Q s) s = t P s + t Q s \<rbrakk> \<Longrightarrow>
   additive t"
  unfolding additive_def by(blast)

text \<open>Additivity is strictly stronger than sub-additivity.\<close>
lemma additive_sub_add:
  "additive t \<Longrightarrow> sub_add t"
  by(simp add:sub_addI additiveD)

text \<open>The additivity property extends to finite summation.\<close>
lemma additive_sum:
  fixes S::"'s set"
  assumes additive: "additive t"
      and healthy:  "healthy t"
      and finite:   "finite S"
      and sPz:      "\<And>z. sound (P z)"
  shows "t (\<lambda>x. \<Sum>y\<in>S. P y x) = (\<lambda>x. \<Sum>y\<in>S. t (P y) x)"
proof(rule finite_induct, simp_all add:assms)
  fix z::'s and T::"'s set"
  assume finT: "finite T"
     and IH: "t (\<lambda>x. \<Sum>y\<in>T. P y x) = (\<lambda>x. \<Sum>y\<in>T. t (P y) x)"

  from additive sPz
  have "t (\<lambda>x. P z x + (\<Sum>y\<in>T. P y x)) =
        (\<lambda>x. t (P z) x +  t (\<lambda>x. \<Sum>y\<in>T. P y x) x)"
    by(auto intro!:sum_sound additiveD)
  also from IH
  have "... = (\<lambda>x. t (P z) x + (\<Sum>y\<in>T. t (P y) x))"
    by(simp)
  finally show "t (\<lambda>x. P z x + (\<Sum>y\<in>T. P y x)) =
                (\<lambda>x. t (P z) x + (\<Sum>y\<in>T. t (P y) x))" .
qed

text \<open>An additive transformer (over a finite state space) is linear: it is
  simply the weighted sum of final expectation values, the weights being the
  probability of reaching a given final state.  This is useful for reasoning
  using the forward, or ``gambling game'' interpretation.\<close>
lemma additive_delta_split:
  fixes t::"('s::finite \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"
  assumes additive: "additive t"
      and ht: "healthy t"
      and sP: "sound P"
  shows "t P x = (\<Sum>y\<in>UNIV. P y * t \<guillemotleft>\<lambda>z. z = y\<guillemotright> x)"
proof -
  have "\<And>x. (\<Sum>y\<in>UNIV. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) =
            (\<Sum>y\<in>UNIV. if y = x then P y else 0)"
    by (rule sum.cong) auto
  also have "\<And>x. ... x = P x"
    by(simp add:sum.delta)
  finally
  have "t P x = t (\<lambda>x. \<Sum>y\<in>UNIV. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) x"
    by(simp)
  also {
    from sP have "\<And>z. sound (\<lambda>a. P z * \<guillemotleft> \<lambda>za. za = z \<guillemotright> a)"
      by(auto intro!:mult_sound)
    hence "t (\<lambda>x. \<Sum>y\<in>UNIV. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) x =
           (\<Sum>y\<in>UNIV. t (\<lambda>x. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) x)"
      by(subst additive_sum, simp_all add:assms)
  }
  also from sP
  have "(\<Sum>y\<in>UNIV. t (\<lambda>x. P y * \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) x) =
        (\<Sum>y\<in>UNIV. P y * t \<guillemotleft>\<lambda>z. z = y\<guillemotright> x)"
    by(subst scalingD[OF healthy_scalingD, OF ht], auto)
  finally show "t P x = (\<Sum>y\<in>UNIV. P y * t \<guillemotleft> \<lambda>z. z = y \<guillemotright> x)" .
qed

text \<open>We can group the states in the linear form, to split on the value
  of a predicate (guard).\<close>
lemma additive_guard_split:
  fixes t::"('s::finite \<Rightarrow> real) \<Rightarrow> 's \<Rightarrow> real"
  assumes additive: "additive t"
      and ht: "healthy t"
      and sP: "sound P"
  shows "t P x = (\<Sum>y\<in>{s.   G s}. P y * t \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) +
                 (\<Sum>y\<in>{s. \<not> G s}. P y * t \<guillemotleft>\<lambda>z. z = y\<guillemotright> x)"
proof -
  from assms
  have "t P x = (\<Sum>y\<in>UNIV. P y * t \<guillemotleft>\<lambda>z. z = y\<guillemotright> x)"
    by(rule additive_delta_split)
  also {
    have "UNIV = {s. G s} \<union> {s. \<not> G s}"
      by(auto)
    hence "(\<Sum>y\<in>UNIV. P y * t \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) =
           (\<Sum>y\<in>{s. G s} \<union> {s. \<not> G s}. P y * t \<guillemotleft>\<lambda>z. z = y\<guillemotright> x)"
      by(simp)
  }
  also
  have "(\<Sum>y\<in>{s. G s} \<union> {s. \<not> G s}. P y * t \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) =
        (\<Sum>y\<in>{s.   G s}. P y * t \<guillemotleft>\<lambda>z. z = y\<guillemotright> x) +
        (\<Sum>y\<in>{s. \<not> G s}. P y * t \<guillemotleft>\<lambda>z. z = y\<guillemotright> x)"
    by(auto intro:sum.union_disjoint)
  finally show ?thesis .
qed

subsubsection \<open>Maximality\<close>
definition
  maximal :: "(('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
where
  "maximal t \<equiv> \<forall>c. 0 \<le> c \<longrightarrow> t (\<lambda>_. c) = (\<lambda>_. c)"

lemma maximalI[intro]:
  "\<lbrakk> \<And>c. 0 \<le> c \<Longrightarrow> t (\<lambda>_. c) = (\<lambda>_. c) \<rbrakk> \<Longrightarrow> maximal t"
  by(simp add:maximal_def)

lemma maximalD[dest]:
  "\<lbrakk> maximal t; 0 \<le> c \<rbrakk>  \<Longrightarrow> t (\<lambda>_. c) = (\<lambda>_. c)"
  by(simp add:maximal_def)

text \<open>A transformer that is both additive and maximal is deterministic:\<close>
definition determ :: "(('a \<Rightarrow> real) \<Rightarrow> 'a \<Rightarrow> real) \<Rightarrow> bool"
where
  "determ t \<equiv> additive t \<and> maximal t"

lemma determI[intro]:
  "\<lbrakk> additive t; maximal t \<rbrakk> \<Longrightarrow> determ t"
  by(simp add:determ_def)

lemma determ_additiveD[intro]:
  "determ t \<Longrightarrow> additive t"
  by(simp add:determ_def)

lemma determ_maximalD[intro]:
  "determ t \<Longrightarrow> maximal t"
  by(simp add:determ_def)

text \<open>For a fully-deterministic transformer, a transformed standard
  expectation, and its transformed negation are complementary.\<close>
lemma determ_negate:
  assumes determ:  "determ t"
  shows "t \<guillemotleft>P\<guillemotright> s + t \<guillemotleft>\<N> P\<guillemotright> s = 1"
proof -
  have "t \<guillemotleft>P\<guillemotright> s + t \<guillemotleft>\<N> P\<guillemotright> s = t (\<lambda>s. \<guillemotleft>P\<guillemotright> s + \<guillemotleft>\<N> P\<guillemotright> s) s"
    by(simp add:additiveD determ determ_additiveD)
  also {
    have "\<And>s. \<guillemotleft>P\<guillemotright> s + \<guillemotleft>\<N> P\<guillemotright> s = 1"
      by(case_tac "P s", simp_all)
    hence "t (\<lambda>s. \<guillemotleft>P\<guillemotright> s + \<guillemotleft>\<N> P\<guillemotright> s) = t (\<lambda>s. 1)"
      by(simp)
  }
  also have "t (\<lambda>s. 1) = (\<lambda>s. 1)"
    by(simp add:maximalD determ determ_maximalD)
  finally show ?thesis .
qed

subsection \<open>Modular Reasoning\<close>

text \<open>The emphasis of a mechanised logic is on automation, and letting
  the computer tackle the large, uninteresting problems.  However, as
  terms generally grow exponentially in the size of a program, it is
  still essential to break up a proof and reason in a modular fashion.

  The following rules allow proof decomposition, and later will be
  incorporated into a verification condition generator.\<close>

lemma entails_combine:
  assumes wp1: "P \<tturnstile> t R"
      and wp2: "Q \<tturnstile> t S"
      and sc:  "sub_conj t"
      and sR:  "sound R"
      and sS:  "sound S"
  shows "P && Q \<tturnstile> t (R && S)"
proof -
  from wp1 and wp2 have "P && Q \<tturnstile> t R && t S"
    by(blast intro:entails_frame)
  also from sc and sR and sS have "... \<le> t (R && S)"
    by(rule sub_conjD)
  finally show ?thesis .
qed

text \<open>These allow mismatched results to be composed\<close>

lemma entails_strengthen_post:
  "\<lbrakk> P \<tturnstile> t Q; healthy t; sound R; Q \<tturnstile> R; sound Q \<rbrakk> \<Longrightarrow> P \<tturnstile> t R"
  by(blast intro:entails_trans)

lemma entails_weaken_pre:
  "\<lbrakk> Q \<tturnstile> t R; P \<tturnstile> Q \<rbrakk> \<Longrightarrow> P \<tturnstile> t R"
  by(blast intro:entails_trans)

text \<open>This rule is unique to pGCL.  Use it to scale the post-expectation
        of a rule to 'fit under' the precondition you need to satisfy.\<close>
lemma entails_scale:
  assumes wp: "P \<tturnstile> t Q" and h: "healthy t"
      and sQ: "sound Q" and pos: "0 \<le> c"
  shows "(\<lambda>s. c * P s) \<tturnstile> t (\<lambda>s. c * Q s)"
proof(rule le_funI)
  fix s
  from pos and wp have "c * P s \<le> c * t Q s"
    by(auto intro:mult_left_mono)
  with sQ pos h show "c * P s \<le> t (\<lambda>s. c * Q s) s"
    by(simp add:scalingD healthy_scalingD)
qed

subsection \<open>Transforming Standard Expectations\<close>

text \<open>Reasoning with \emph{standard} expectations, those obtained
  by embedding a predicate, is often easier, as the analogues of
  many familiar boolean rules hold in modified form.\<close>

text \<open>One may use a standard pre-expectation as an assumption:\<close>
lemma use_premise:
  assumes h: "healthy t" and wP: "\<And>s. P s \<Longrightarrow> 1 \<le> t \<guillemotleft>Q\<guillemotright> s"
  shows "\<guillemotleft>P\<guillemotright> \<tturnstile> t \<guillemotleft>Q\<guillemotright>"
proof(rule entailsI)
  fix s show "\<guillemotleft>P\<guillemotright> s \<le> t \<guillemotleft>Q\<guillemotright> s"
  proof(cases "P s")
    case True with wP show ?thesis by(auto)
  next
    case False with h show ?thesis by(auto)
  qed
qed

text \<open>The other direction works too.\<close>
lemma fold_premise:
  assumes ht: "healthy t"
  and wp: "\<guillemotleft>P\<guillemotright> \<tturnstile> t \<guillemotleft>Q\<guillemotright>"
  shows "\<forall>s. P s \<longrightarrow> 1 \<le> t \<guillemotleft>Q\<guillemotright> s"
proof(clarify)
  fix s assume "P s"
  hence "1 = \<guillemotleft>P\<guillemotright> s" by(simp)
  also from wp have "... \<le> t \<guillemotleft>Q\<guillemotright> s" by(auto)
  finally show "1 \<le> t \<guillemotleft>Q\<guillemotright> s" .
qed

text \<open>Predicate conjunction behaves as expected:\<close>
lemma conj_post:
  "\<lbrakk> P \<tturnstile> t \<guillemotleft>\<lambda>s. Q s \<and> R s\<guillemotright>; healthy t \<rbrakk> \<Longrightarrow> P \<tturnstile> t \<guillemotleft>Q\<guillemotright>"
  by(blast intro:entails_strengthen_post implies_entails)

text \<open>Similar to @{thm use_premise}, but more general.\<close>
lemma entails_pconj_assumption:
  assumes f: "feasible t" and wP: "\<And>s. P s \<Longrightarrow> Q s \<le> t R s"
      and uQ: "unitary Q" and uR: "unitary R"
  shows "\<guillemotleft>P\<guillemotright> && Q \<tturnstile> t R"
  unfolding exp_conj_def
proof(rule entailsI)
  fix s show "\<guillemotleft>P\<guillemotright> s .& Q s \<le> t R s"
  proof(cases "P s")
    case True
    moreover from uQ have "0 \<le> Q s" by(auto)
    ultimately show ?thesis by(simp add:pconj_lone wP)
  next
    case False
    moreover from uQ have "Q s \<le> 1" by(auto)
    ultimately show ?thesis using assms by auto
  qed
qed

end
