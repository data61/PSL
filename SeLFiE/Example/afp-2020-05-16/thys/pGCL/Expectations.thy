(*
 * Copyright (C) 2014 NICTA
 * All rights reserved.
 *)

(* Author: David Cock - David.Cock@nicta.com.au *)

section "Expectations"

theory Expectations imports Misc begin

text_raw \<open>\label{s:expectations}\<close>

type_synonym 's expect = "'s \<Rightarrow> real"

text \<open>Expectations are a real-valued generalisation of boolean predicates: An expectation on state
@{typ 's} is a function @{typ "'s \<Rightarrow> real"}. A predicate @{term P} on @{typ 's} is embedded as an
expectation by mapping @{term True} to 1 and @{term False} to 0.  Under this embedding, implication
becomes comparison, as the truth tables demonstrate:
\begin{center}
\begin{tabular}{ccc|ccc}
$a$ & $b$ & $a \rightarrow b$ & $x$ & $y$ & $x \le y$ \\
 F  &  F  &  T                &  0  &  0  &  T \\
 F  &  T  &  T                &  0  &  1  &  T \\
 T  &  F  &  F                &  1  &  0  &  F \\
 T  &  T  &  T                &  1  &  1  &  T
\end{tabular}
\end{center}

\begin{figure}
\begin{center}
\mbox{
\xymatrix{
*++[o][F=]{b} & & *++[o][F=]{c} \\
  & *++[o][F-]{a} \ar[ul]^{0.7} \ar[ur]_{0.3} \\
  & \ar[u]
}
}
\end{center}
\caption{\label{f:automaton_1}A probabilistic automaton}
\end{figure}

For probabilistic automata, an expectation gives the current expected value of some expression, if
it were to be evaluated in the final state. For example, consider the automaton of
\autoref{f:automaton_1}, with transition probabilities affixed to edges. Let $P\ b = 2.0$ and $P\ c
= 3.0$. Both states $b$ and $c$ are final (accepting) states, and thus the `final expected value' of
$P$ in state $b$ is $2.0$ and in state $c$ is $3.0$. The expected value from state $a$ is the
weighted sum of these, or $0.7 \times 2.0 + 0.3 \times 3.0 = 2.3$.

All expectations must be non-negative and bounded i.e. $\forall s.~0 \le P\ s$ and $\exists b.
\forall s. P\ s \le b$. Note that although every expectation must have a bound, there is no bound on
all expectations; In particular, the following series has no global bound, although each element is
clearly bounded:
\begin{displaymath}
P_i = \lambda s.\ i\quad\text{where}\ i \in \mathbb{N}
\end{displaymath}
\<close>

subsection \<open>Bounded Functions\<close>

definition bounded_by :: "real \<Rightarrow> ('a \<Rightarrow> real) \<Rightarrow> bool"
where     "bounded_by b P \<equiv> \<forall>x. P x \<le> b"

text \<open>By instantiating the classical reasoner, both establishing and appealing to boundedness
is largely automatic.\<close>

lemma bounded_byI[intro]:
  "\<lbrakk> \<And>x. P x \<le> b \<rbrakk> \<Longrightarrow> bounded_by b P"
  by (simp add:bounded_by_def)

lemma bounded_byI2[intro]:
  "P \<le> (\<lambda>s. b) \<Longrightarrow> bounded_by b P"
  by (blast dest:le_funD)

lemma bounded_byD[dest]:
  "bounded_by b P \<Longrightarrow> P x \<le> b"
  by (simp add:bounded_by_def)

lemma bounded_byD2[dest]:
  "bounded_by b P \<Longrightarrow> P \<le> (\<lambda>s. b)"
  by (blast intro:le_funI)

text \<open>A function is bounded if there exists at least one upper bound on it.\<close>

definition bounded :: "('a \<Rightarrow> real) \<Rightarrow> bool"
where     "bounded P \<equiv> (\<exists>b. bounded_by b P)"

text \<open>In the reals, if there exists any upper bound, then there must exist a least upper bound.\<close>

definition bound_of :: "('a \<Rightarrow> real) \<Rightarrow> real"
where     "bound_of P \<equiv> Sup (P ` UNIV)"

lemma bounded_bdd_above[intro]:
  assumes bP: "bounded P"
  shows "bdd_above (range P)"
proof
  fix x assume "x \<in> range P"
  with bP show "x \<le> Inf {b. bounded_by b P}"
    unfolding bounded_def by(auto intro:cInf_greatest)
qed

text \<open>The least upper bound has the usual properties:\<close>
lemma bound_of_least[intro]:
  assumes bP: "bounded_by b P"
  shows "bound_of P \<le> b"
  unfolding bound_of_def
  using bP by(intro cSup_least, auto)

lemma bounded_by_bound_of[intro!]:
  fixes P::"'a \<Rightarrow> real"
  assumes bP: "bounded P"
  shows "bounded_by (bound_of P) P"
  unfolding bound_of_def
  using bP by(intro bounded_byI cSup_upper bounded_bdd_above, auto)

lemma bound_of_greater[intro]:
  "bounded P \<Longrightarrow> P x \<le> bound_of P"
  by (blast intro:bounded_byD)

lemma bounded_by_mono:
  "\<lbrakk> bounded_by a P; a \<le> b \<rbrakk> \<Longrightarrow> bounded_by b P"
  unfolding bounded_by_def by(blast intro:order_trans)

lemma bounded_by_imp_bounded[intro]:
  "bounded_by b P \<Longrightarrow> bounded P"
  unfolding bounded_def by(blast)

text \<open>This is occasionally easier to apply:\<close>

lemma bounded_by_bound_of_alt:
  "\<lbrakk> bounded P; bound_of P = a \<rbrakk> \<Longrightarrow> bounded_by a P"
  by (blast)

lemma bounded_const[simp]:
  "bounded (\<lambda>x. c)"
  by (blast)

lemma bounded_by_const[intro]:
  "c \<le> b \<Longrightarrow> bounded_by b (\<lambda>x. c)"
  by (blast)

lemma bounded_by_mono_alt[intro]:
  "\<lbrakk> bounded_by b Q; P \<le> Q \<rbrakk> \<Longrightarrow> bounded_by b P"
  by (blast intro:order_trans dest:le_funD)

lemma bound_of_const[simp, intro]:
  "bound_of (\<lambda>x. c) = (c::real)"
  unfolding bound_of_def
  by(intro antisym cSup_least cSup_upper bounded_bdd_above bounded_const, auto)

lemma bound_of_leI:
  assumes "\<And>x. P x \<le> (c::real)"
  shows "bound_of P \<le> c"
  unfolding bound_of_def
  using assms by(intro cSup_least, auto)

lemma bound_of_mono[intro]:
  "\<lbrakk> P \<le> Q; bounded P; bounded Q \<rbrakk> \<Longrightarrow> bound_of P \<le> bound_of Q"
  by (blast intro:order_trans dest:le_funD)

lemma bounded_by_o[intro,simp]:
  "\<And>b. bounded_by b P \<Longrightarrow> bounded_by b (P o f)"
  unfolding o_def by(blast)

lemma le_bound_of[intro]:
  "\<And>x. bounded f \<Longrightarrow> f x \<le> bound_of f"
  by(blast)

subsection \<open>Non-Negative Functions.\<close>

text \<open>The definitions for non-negative functions are analogous to those for bounded functions.\<close>

definition
  nneg :: "('a \<Rightarrow> 'b::{zero,order}) \<Rightarrow> bool"
where
  "nneg P \<longleftrightarrow> (\<forall>x. 0 \<le> P x)"

lemma nnegI[intro]:
  "\<lbrakk> \<And>x. 0 \<le> P x \<rbrakk> \<Longrightarrow> nneg P"
  by (simp add:nneg_def)

lemma nnegI2[intro]:
  "(\<lambda>s. 0) \<le> P \<Longrightarrow> nneg P"
  by (blast dest:le_funD)

lemma nnegD[dest]:
  "nneg P \<Longrightarrow> 0 \<le> P x"
  by (simp add:nneg_def)

lemma nnegD2[dest]:
  "nneg P \<Longrightarrow> (\<lambda>s. 0) \<le> P"
  by (blast intro:le_funI)

lemma nneg_bdd_below[intro]:
  "nneg P \<Longrightarrow> bdd_below (range P)"
  by(auto)

lemma nneg_const[iff]:
  "nneg (\<lambda>x. c) \<longleftrightarrow> 0 \<le> c"
  by (simp add:nneg_def)

lemma nneg_o[intro,simp]:
  "nneg P \<Longrightarrow> nneg (P o f)"
  by (force)

lemma nneg_bound_nneg[intro]:
  "\<lbrakk> bounded P; nneg P \<rbrakk> \<Longrightarrow> 0 \<le> bound_of P"
  by (blast intro:order_trans)

lemma nneg_bounded_by_nneg[dest]:
  "\<lbrakk> bounded_by b P; nneg P \<rbrakk> \<Longrightarrow> 0 \<le> (b::real)"
  by (blast intro:order_trans)

lemma bounded_by_nneg[dest]:
  fixes P::"'s \<Rightarrow> real"
  shows "\<lbrakk> bounded_by b P; nneg P \<rbrakk> \<Longrightarrow> 0 \<le> b"
  by (blast intro:order_trans)

subsection \<open>Sound Expectations\<close>

definition sound :: "('s \<Rightarrow> real) \<Rightarrow> bool"
where "sound P \<equiv> bounded P \<and> nneg P"

text \<open>Combining @{term nneg} and @{term bounded}, we have @{term sound} expectations. We set up
the classical reasoner and the simplifier, such that showing soundess, or deriving a simple
consequence (e.g. @{term "sound P \<Longrightarrow> 0 \<le> P s"}) will usually follow by blast, force or simp.\<close>

lemma soundI:
  "\<lbrakk> bounded P; nneg P \<rbrakk> \<Longrightarrow> sound P"
  by (simp add:sound_def)

lemma soundI2[intro]:
  "\<lbrakk> bounded_by b P; nneg P \<rbrakk> \<Longrightarrow> sound P"
  by(blast intro:soundI)

lemma sound_bounded[dest]:
  "sound P \<Longrightarrow> bounded P"
  by (simp add:sound_def)

lemma sound_nneg[dest]:
  "sound P \<Longrightarrow> nneg P"
  by (simp add:sound_def)

lemma bound_of_sound[intro]:
  assumes sP: "sound P"
  shows "0 \<le> bound_of P"
  using assms by(auto)

text \<open>This proof demonstrates the use of the classical reasoner (specifically blast), to both
introduce and eliminate soundness terms.\<close>

lemma sound_sum[simp,intro]:
  assumes sP: "sound P" and sQ: "sound Q"
  shows "sound (\<lambda>s. P s + Q s)"
proof
  from sP have "\<And>s. P s \<le> bound_of P" by(blast)
  moreover from sQ have "\<And>s. Q s \<le> bound_of Q" by(blast)
  ultimately have "\<And>s. P s + Q s \<le> bound_of P + bound_of Q"
    by(rule add_mono)
  thus "bounded_by (bound_of P + bound_of Q) (\<lambda>s. P s + Q s)"
    by(blast)

  from sP have "\<And>s. 0 \<le> P s" by(blast)
  moreover from sQ have "\<And>s. 0 \<le> Q s" by(blast)
  ultimately have "\<And>s. 0 \<le> P s + Q s" by(simp add:add_mono)
  thus "nneg (\<lambda>s. P s + Q s)" by(blast)
qed

lemma mult_sound:
  assumes sP: "sound P" and sQ: "sound Q"
  shows "sound (\<lambda>s. P s * Q s)"
proof
  from sP have "\<And>s. P s \<le> bound_of P" by(blast)
  moreover from sQ have "\<And>s. Q s \<le> bound_of Q" by(blast)
  ultimately have "\<And>s. P s * Q s \<le> bound_of P * bound_of Q"
    using sP and sQ by(blast intro:mult_mono)
  thus "bounded_by (bound_of P * bound_of Q) (\<lambda>s. P s * Q s)" by(blast)

  from sP and sQ show "nneg (\<lambda>s. P s * Q s)"
    by(blast intro:mult_nonneg_nonneg)
qed

lemma div_sound:
  assumes sP: "sound P" and cpos: "0 < c"
  shows "sound (\<lambda>s. P s / c)"
proof
  from sP and cpos have "\<And>s. P s / c \<le> bound_of P / c"
    by(blast intro:divide_right_mono less_imp_le)
  thus "bounded_by (bound_of P / c) (\<lambda>s. P s / c)" by(blast)
  from assms show "nneg (\<lambda>s. P s / c)"
    by(blast intro:divide_nonneg_pos)
qed

lemma tminus_sound:
  assumes sP: "sound P" and nnc: "0 \<le> c"
  shows "sound (\<lambda>s. P s \<ominus> c)"
proof(rule soundI)
  from sP have "\<And>s. P s \<le> bound_of P" by(blast)
  with nnc have "\<And>s. P s \<ominus> c \<le> bound_of P \<ominus> c"
    by(blast intro:tminus_left_mono)
  thus "bounded (\<lambda>s. P s \<ominus> c)" by(blast)
  show "nneg (\<lambda>s. P s \<ominus> c)" by(blast)
qed

lemma const_sound:
  "0 \<le> c \<Longrightarrow> sound (\<lambda>s. c)"
  by (blast)

lemma sound_o[intro,simp]:
  "sound P \<Longrightarrow> sound (P o f)"
  unfolding o_def by(blast)

lemma sc_bounded_by[intro,simp]:
  "\<lbrakk> sound P; 0 \<le> c \<rbrakk> \<Longrightarrow> bounded_by (c * bound_of P) (\<lambda>x. c * P x)"
  by(blast intro!:mult_left_mono)

lemma sc_bounded[intro,simp]:
  assumes sP:  "sound P" and pos: "0 \<le> c"
  shows "bounded (\<lambda>x. c * P x)"
  using assms by(blast)

lemma sc_bound[simp]:
  assumes sP: "sound P"
      and cnn: "0 \<le> c"
  shows "c * bound_of P = bound_of (\<lambda>x. c * P x)"
proof(cases "c = 0")
  case True then show ?thesis by(simp)
next
  case False with cnn have cpos: "0 < c" by(auto)
  show ?thesis
  proof (rule antisym)
    from sP and cnn have "bounded (\<lambda>x. c * P x)" by(simp)
    hence "\<And>x. c * P x \<le> bound_of (\<lambda>x. c * P x)"
      by(rule le_bound_of)
    with cpos have "\<And>x. P x \<le> inverse c * bound_of (\<lambda>x. c * P x)"
      by(force intro:mult_div_mono_right)
    hence "bound_of P \<le> inverse c * bound_of (\<lambda>x. c * P x)"
      by(blast)
    with cpos show "c * bound_of P \<le> bound_of (\<lambda>x. c * P x)"
      by(force intro:mult_div_mono_left)
  next
    from sP and cpos have "\<And>x. c * P x \<le> c * bound_of P"
      by(blast intro:mult_left_mono less_imp_le)
    thus "bound_of (\<lambda>x. c * P x) \<le> c * bound_of P"
      by(blast)
  qed
qed

lemma sc_sound:
  "\<lbrakk> sound P; 0 \<le> c \<rbrakk> \<Longrightarrow> sound (\<lambda>s. c * P s)"
  by (blast intro:mult_nonneg_nonneg)

lemma bounded_by_mult:
  assumes sP: "sound P" and bP: "bounded_by a P"
      and sQ: "sound Q" and bQ: "bounded_by b Q"
  shows "bounded_by (a * b) (\<lambda>s. P s * Q s)"
  using assms by(intro bounded_byI, auto intro:mult_mono)

lemma bounded_by_add:
  fixes P::"'s \<Rightarrow> real" and Q
  assumes bP: "bounded_by a P"
      and bQ: "bounded_by b Q"
  shows "bounded_by (a + b) (\<lambda>s. P s + Q s)"
  using assms by(intro bounded_byI, auto intro:add_mono)

lemma sound_unit[intro!,simp]:
  "sound (\<lambda>s. 1)"
  by(auto)

lemma unit_mult[intro]:
  assumes sP: "sound P" and bP: "bounded_by 1 P"
      and sQ: "sound Q" and bQ: "bounded_by 1 Q"
  shows "bounded_by 1 (\<lambda>s. P s * Q s)"
proof(rule bounded_byI)
  fix s
  have "P s * Q s \<le> 1 * 1"
    using assms by(blast dest:bounded_by_mult)
  thus "P s * Q s \<le> 1" by(simp)
qed

lemma sum_sound:
  assumes sP: "\<forall>x\<in>S. sound (P x)"
  shows "sound (\<lambda>s. \<Sum>x\<in>S. P x s)"
proof(rule soundI2)
  from sP show "bounded_by (\<Sum>x\<in>S. bound_of (P x)) (\<lambda>s. \<Sum>x\<in>S. P x s)"
    by(auto intro!:sum_mono)
  from sP show "nneg (\<lambda>s. \<Sum>x\<in>S. P x s)"
    by(auto intro!:sum_nonneg)
qed

subsection \<open>Unitary expectations\<close>

text \<open>A unitary expectation is a sound expectation that is additionally bounded by one.  This
is the domain on which the \emph{liberal} (partial correctness) semantics operates.\<close>

definition unitary :: "'s expect \<Rightarrow> bool"
where "unitary P \<longleftrightarrow> sound P \<and> bounded_by 1 P"

lemma unitaryI[intro]:
  "\<lbrakk> sound P; bounded_by 1 P \<rbrakk> \<Longrightarrow> unitary P"
  by(simp add:unitary_def)

lemma unitaryI2:
  "\<lbrakk> nneg P; bounded_by 1 P \<rbrakk> \<Longrightarrow> unitary P"
  by(auto)

lemma unitary_sound[dest]:
  "unitary P \<Longrightarrow> sound P"
  by(simp add:unitary_def)
  
lemma unitary_bound[dest]:
  "unitary P \<Longrightarrow> bounded_by 1 P"
  by(simp add:unitary_def)

subsection \<open>Standard Expectations\<close>
text_raw \<open>\label{s:standard}\<close>

definition
  embed_bool :: "('s \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> real" ("\<guillemotleft> _ \<guillemotright>" 1000)
where
  "\<guillemotleft>P\<guillemotright> \<equiv> (\<lambda>s. if P s then 1 else 0)"

text \<open>Standard expectations are the embeddings of boolean predicates, mapping @{term False} to 0
and @{term True} to 1. We write @{term "\<guillemotleft>P\<guillemotright>"} rather than @{term "[P]"} (the syntax employed by
\citet{McIver_M_04}) for boolean embedding to avoid clashing with the HOL syntax for lists.\<close>

lemma embed_bool_nneg[simp,intro]:
  "nneg \<guillemotleft>P\<guillemotright>"
  unfolding embed_bool_def by(force)

lemma embed_bool_bounded_by_1[simp,intro]:
  "bounded_by 1 \<guillemotleft>P\<guillemotright>"
  unfolding embed_bool_def by(force)

lemma embed_bool_bounded[simp,intro]:
  "bounded \<guillemotleft>P\<guillemotright>"
  by (blast)

text \<open>Standard expectations have a number of convenient properties, which mostly follow from
boolean algebra.\<close>

lemma embed_bool_idem:
  "\<guillemotleft>P\<guillemotright> s * \<guillemotleft>P\<guillemotright> s = \<guillemotleft>P\<guillemotright> s"
  by (simp add:embed_bool_def)

lemma eval_embed_true[simp]:
  "P s \<Longrightarrow> \<guillemotleft>P\<guillemotright> s = 1"
  by (simp add:embed_bool_def)

lemma eval_embed_false[simp]:
  "\<not>P s \<Longrightarrow> \<guillemotleft>P\<guillemotright> s = 0"
  by (simp add:embed_bool_def)

lemma embed_ge_0[simp,intro]:
  "0 \<le> \<guillemotleft>G\<guillemotright> s"
  by (simp add:embed_bool_def)

lemma embed_le_1[simp,intro]:
  "\<guillemotleft>G\<guillemotright> s \<le> 1"
  by(simp add:embed_bool_def)

lemma embed_le_1_alt[simp,intro]:
  "0 \<le> 1 - \<guillemotleft>G\<guillemotright> s"
  by(subst add_le_cancel_right[where c="\<guillemotleft>G\<guillemotright> s", symmetric], simp)

lemma expect_1_I:
  "P x \<Longrightarrow> 1 \<le> \<guillemotleft>P\<guillemotright> x"
  by(simp)

lemma standard_sound[intro,simp]:
  "sound \<guillemotleft>P\<guillemotright>"
  by(blast)

lemma embed_o[simp]:
  "\<guillemotleft>P\<guillemotright> o f = \<guillemotleft>P o f\<guillemotright>"
  unfolding embed_bool_def o_def by(simp)

text \<open>Negating a predicate has the expected effect in its
embedding as an expectation:\<close>

definition negate :: "('s \<Rightarrow> bool) \<Rightarrow> 's \<Rightarrow> bool" ("\<N>")
where     "negate P = (\<lambda>s. \<not> P s)"

lemma negateI:
  "\<not> P s \<Longrightarrow> \<N> P s"
  by (simp add:negate_def)

lemma embed_split:
  "f s = \<guillemotleft>P\<guillemotright> s * f s + \<guillemotleft>\<N> P\<guillemotright> s * f s"
  by (simp add:negate_def embed_bool_def)

lemma negate_embed:
  "\<guillemotleft>\<N> P\<guillemotright> s = 1 - \<guillemotleft>P\<guillemotright> s"
  by (simp add:embed_bool_def negate_def)

lemma eval_nembed_true[simp]:
  "P s \<Longrightarrow> \<guillemotleft>\<N> P\<guillemotright> s = 0"
  by (simp add:embed_bool_def negate_def)

lemma eval_nembed_false[simp]:
  "\<not>P s \<Longrightarrow> \<guillemotleft>\<N> P\<guillemotright> s = 1"
  by (simp add:embed_bool_def negate_def)

lemma negate_Not[simp]:
  "\<N> Not = (\<lambda>x. x)"
  by(simp add:negate_def)

lemma negate_negate[simp]:
  "\<N> (\<N> P) = P"
  by(simp add:negate_def)

lemma embed_bool_cancel:
  "\<guillemotleft>G\<guillemotright> s * \<guillemotleft>\<N> G\<guillemotright> s = 0"
  by(cases "G s", simp_all)

subsection \<open>Entailment\<close>
text_raw \<open>\label{s:entailment}\<close>

text \<open>Entailment on expectations is a generalisation of that on predicates, and is defined by
pointwise comparison:\<close>

abbreviation entails :: "('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real) \<Rightarrow> bool" ("_ \<tturnstile> _" 50)
where "P \<tturnstile> Q \<equiv> P \<le> Q"

lemma entailsI[intro]:
  "\<lbrakk>\<And>s. P s \<le> Q s\<rbrakk> \<Longrightarrow> P \<tturnstile> Q"
  by(simp add:le_funI)

lemma entailsD[dest]:
  "P \<tturnstile> Q \<Longrightarrow> P s \<le> Q s"
  by(simp add:le_funD)

lemma eq_entails[intro]:
  "P = Q \<Longrightarrow> P \<tturnstile> Q"
  by(blast)

lemma entails_trans[trans]:
  "\<lbrakk> P \<tturnstile> Q; Q \<tturnstile> R \<rbrakk> \<Longrightarrow> P \<tturnstile> R"
  by(blast intro:order_trans)

text \<open>For standard expectations, both notions of entailment coincide. This result justifies the
above claim that our definition generalises predicate entailment:\<close>

lemma implies_entails:
  "\<lbrakk> \<And>s. P s \<Longrightarrow> Q s \<rbrakk> \<Longrightarrow> \<guillemotleft>P\<guillemotright> \<tturnstile> \<guillemotleft>Q\<guillemotright>"
  by(rule entailsI, case_tac "P s", simp_all)

lemma entails_implies:
  "\<And>s. \<lbrakk> \<guillemotleft>P\<guillemotright> \<tturnstile> \<guillemotleft>Q\<guillemotright>; P s \<rbrakk> \<Longrightarrow> Q s"
  by(rule ccontr, drule_tac s=s in entailsD, simp)

subsection \<open>Expectation Conjunction\<close>

definition
  pconj :: "real \<Rightarrow> real \<Rightarrow>  real" (infixl ".&" 71)
where
  "p .& q \<equiv> p + q \<ominus> 1"

definition
  exp_conj :: "('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real) \<Rightarrow> ('s \<Rightarrow> real)" (infixl "&&" 71)
where "a && b \<equiv> \<lambda>s. (a s .& b s)"

text \<open>Expectation conjunction likewise generalises (boolean) predicate conjunction. We show that
the expected properties are preserved, and instantiate both the classical reasoner, and the
simplifier (in the case of associativity and commutativity).\<close>

lemma pconj_lzero[intro,simp]:
  "b \<le> 1 \<Longrightarrow> 0 .& b = 0"
  by(simp add:pconj_def tminus_def)

lemma pconj_rzero[intro,simp]:
  "b \<le> 1 \<Longrightarrow> b .& 0 = 0"
  by(simp add:pconj_def tminus_def)

lemma pconj_lone[intro,simp]:
  "0 \<le> b \<Longrightarrow> 1 .& b = b"
  by(simp add:pconj_def tminus_def)

lemma pconj_rone[intro,simp]:
  "0 \<le> b \<Longrightarrow> b .& 1 = b"
  by(simp add:pconj_def tminus_def)

lemma pconj_bconj:
  "\<guillemotleft>a\<guillemotright> s .& \<guillemotleft>b\<guillemotright> s = \<guillemotleft>\<lambda>s. a s \<and> b s\<guillemotright> s"
  unfolding embed_bool_def pconj_def tminus_def by(force)

lemma pconj_comm[ac_simps]:
  "a .& b = b .& a"
  by(simp add:pconj_def ac_simps)

lemma pconj_assoc:
  "\<lbrakk> 0 \<le> a; a \<le> 1; 0 \<le> b; b \<le> 1; 0 \<le> c; c \<le> 1 \<rbrakk> \<Longrightarrow>
   a .& (b .& c) = (a .& b) .& c"
  unfolding pconj_def tminus_def by(simp)

lemma pconj_mono:
  "\<lbrakk> a \<le> b; c \<le> d \<rbrakk> \<Longrightarrow> a .& c \<le> b .& d"
  unfolding pconj_def tminus_def by(simp)

lemma pconj_nneg[intro,simp]:
  "0 \<le> a .& b"
  unfolding pconj_def tminus_def by(auto)

lemma min_pconj:
  "(min a b) .& (min c d) \<le> min (a .& c) (b .& d)"
  by(cases "a \<le> b",
     (cases "c \<le> d",
      simp_all add:min.absorb1 min.absorb2 pconj_mono)[],
     (cases "c \<le> d",
      simp_all add:min.absorb1 min.absorb2 pconj_mono))

lemma pconj_less_one[simp]:
  "a + b < 1 \<Longrightarrow> a .& b = 0"
  unfolding pconj_def by(simp)

lemma pconj_ge_one[simp]:
  "1 \<le> a + b \<Longrightarrow> a .& b = a + b - 1"
  unfolding pconj_def by(simp)

lemma pconj_idem[simp]:
  "\<guillemotleft>P\<guillemotright> s .& \<guillemotleft>P\<guillemotright> s = \<guillemotleft>P\<guillemotright> s"
  unfolding pconj_def by(cases "P s", simp_all)

subsection \<open>Rules Involving Conjunction.\<close>

lemma exp_conj_mono_left:
  "P \<tturnstile> Q \<Longrightarrow> P && R \<tturnstile> Q && R"
  unfolding exp_conj_def pconj_def
  by(auto intro:tminus_left_mono add_right_mono)

lemma exp_conj_mono_right:
  "Q \<tturnstile> R \<Longrightarrow> P && Q \<tturnstile> P && R"
  unfolding exp_conj_def pconj_def
  by(auto intro:tminus_left_mono add_left_mono)

lemma exp_conj_comm[ac_simps]:
  "a && b = b && a"
  by(simp add:exp_conj_def ac_simps)

lemma exp_conj_bounded_by[intro,simp]:
  assumes bP: "bounded_by 1 P"
      and bQ: "bounded_by 1 Q"
  shows "bounded_by 1 (P && Q)"
proof(rule bounded_byI, unfold exp_conj_def pconj_def)
  fix x
  from bP have "P x \<le> 1" by(blast)
  moreover from bQ have "Q x \<le> 1" by(blast)
  ultimately have "P x + Q x \<le> 2" by(auto)
  thus "P x + Q x \<ominus> 1 \<le> 1"
    unfolding tminus_def by(simp)
qed

lemma exp_conj_o_distrib[simp]:
  "(P && Q) o f = (P o f) && (Q o f)"
  unfolding exp_conj_def o_def by(simp)

lemma exp_conj_assoc:
  assumes "unitary P" and "unitary Q" and "unitary R"
  shows "P && (Q && R) = (P && Q) && R"
  unfolding exp_conj_def
proof(rule ext)
  fix s
  from assms have "0 \<le> P s" by(blast)
  moreover from assms have "0 \<le> Q s" by(blast)
  moreover from assms have "0 \<le> R s" by(blast)
  moreover from assms have "P s \<le> 1" by(blast)
  moreover from assms have "Q s \<le> 1" by(blast)
  moreover from assms have "R s \<le> 1" by(blast)
  ultimately
  show "P s .& (Q s .& R s) = (P s .& Q s) .& R s"
    by(simp add:pconj_assoc)
qed

lemma exp_conj_top_left[simp]:
  "sound P \<Longrightarrow> \<guillemotleft>\<lambda>_. True\<guillemotright> && P = P"
  unfolding exp_conj_def by(force)

lemma exp_conj_top_right[simp]:
  "sound P \<Longrightarrow> P && \<guillemotleft>\<lambda>_. True\<guillemotright> = P"
  unfolding exp_conj_def by(force)

lemma exp_conj_idem[simp]:
  "\<guillemotleft>P\<guillemotright> && \<guillemotleft>P\<guillemotright> = \<guillemotleft>P\<guillemotright>"
  unfolding exp_conj_def
  by(rule ext, cases "P s", simp_all)

lemma exp_conj_nneg[intro,simp]:
  "(\<lambda>s. 0) \<le> P && Q"
  unfolding exp_conj_def
  by(blast intro:le_funI)

lemma exp_conj_sound[intro,simp]:
  assumes s_P: "sound P"
      and s_Q: "sound Q"
  shows "sound (P && Q)"
  unfolding exp_conj_def
proof(rule soundI)
  from s_P and s_Q have "\<And>s. 0 \<le> P s + Q s" by(blast intro:add_nonneg_nonneg)
  hence "\<And>s. P s .& Q s \<le> P s + Q s"
    unfolding pconj_def by(force intro:tminus_less)
  also from assms have "\<And>s. ... s \<le> bound_of P + bound_of Q"
    by(blast intro:add_mono)
  finally have "bounded_by (bound_of P + bound_of Q) (\<lambda>s. P s .& Q s)"
    by(blast)
  thus "bounded (\<lambda>s. P s .& Q s)" by(blast)

  show "nneg (\<lambda>s. P s .& Q s)"
    unfolding pconj_def tminus_def by(force)
qed

lemma exp_conj_rzero[simp]:
  "bounded_by 1 P \<Longrightarrow> P && (\<lambda>s. 0) = (\<lambda>s. 0)"
  unfolding exp_conj_def by(force)

lemma exp_conj_1_right[simp]:
  assumes nn: "nneg A"
  shows "A && (\<lambda>_. 1) = A"
  unfolding exp_conj_def pconj_def tminus_def
proof(rule ext, simp)
  fix s
  from nn have "0 \<le> A s" by(blast)
  thus "max (A s) 0 = A s" by(force)
qed

lemma exp_conj_std_split:
  "\<guillemotleft>\<lambda>s. P s \<and> Q s\<guillemotright> = \<guillemotleft>P\<guillemotright> && \<guillemotleft>Q\<guillemotright>"
  unfolding exp_conj_def embed_bool_def pconj_def
  by(auto)

subsection \<open>Rules Involving Entailment and Conjunction Together\<close>

text \<open>Meta-conjunction distributes over expectaton entailment,
becoming expectation conjunction:\<close>
lemma entails_frame:
  assumes ePR: "P \<tturnstile> R"
      and eQS: "Q \<tturnstile> S"
  shows "P && Q \<tturnstile> R && S"
proof(rule le_funI)
  fix s
  from ePR have "P s \<le> R s" by(blast)
  moreover from eQS have "Q s \<le> S s" by(blast)
  ultimately have "P s + Q s \<le> R s + S s" by(rule add_mono)
  hence "P s + Q s \<ominus> 1 \<le> R s + S s \<ominus> 1" by(rule tminus_left_mono)
  thus "(P && Q) s \<le> (R && S) s"
    unfolding exp_conj_def pconj_def .
qed

text \<open>This rule allows something very much akin to a case distinction
on the pre-expectation.\<close>
lemma pentails_cases:
  assumes PQe: "\<And>x. P x \<tturnstile> Q x"
      and exhaust: "\<And>s. \<exists>x. P (x s) s = 1"
      and framed: "\<And>x. P x && R \<tturnstile> Q x && S"
      and sR: "sound R" and sS: "sound S"
      and bQ: "\<And>x. bounded_by 1 (Q x)"
  shows "R \<tturnstile> S"
proof(rule le_funI)
  fix s
  from exhaust obtain x where P_xs: "P x s = 1" by(blast)
  moreover {
    hence "1 = P x s" by(simp)
    also from PQe have "P x s \<le> Q x s" by(blast dest:le_funD)
    finally have "Q x s = 1"
      using bQ by(blast intro:antisym)
  }
  moreover note le_funD[OF framed[where x=x], where x=s]
  moreover from sR have "0 \<le> R s" by(blast)
  moreover from sS have "0 \<le> S s" by(blast)
  ultimately show "R s \<le> S s" by(simp add:exp_conj_def)
qed

lemma unitary_bot[iff]:
  "unitary (\<lambda>s. 0::real)"
  by(auto)

lemma unitary_top[iff]:
  "unitary (\<lambda>s. 1::real)"
  by(auto)

lemma unitary_embed[iff]:
  "unitary \<guillemotleft>P\<guillemotright>"
  by(auto)

lemma unitary_const[iff]:
  "\<lbrakk> 0 \<le> c; c \<le> 1 \<rbrakk> \<Longrightarrow> unitary (\<lambda>s. c)"
  by(auto)

lemma unitary_mult:
  assumes uA: "unitary A" and uB: "unitary B"
  shows "unitary (\<lambda>s. A s * B s)"
proof(intro unitaryI2 nnegI bounded_byI)
  fix s
  from assms have nnA: "0 \<le> A s" and nnB: "0 \<le> B s" by(auto)
  thus "0 \<le> A s * B s" by(rule mult_nonneg_nonneg)
  from assms have "A s \<le> 1" and "B s \<le> 1" by(auto)
  with nnB have "A s * B s \<le> 1 * 1" by(intro mult_mono, auto)
  also have "... = 1" by(simp)
  finally show "A s * B s \<le> 1" .
qed

lemma exp_conj_unitary:
  "\<lbrakk> unitary P; unitary Q \<rbrakk> \<Longrightarrow> unitary (P && Q)"
  by(intro unitaryI2 nnegI2, auto)

lemma unitary_comp[simp]:
  "unitary P \<Longrightarrow> unitary (P o f)"
  by(intro unitaryI2 nnegI bounded_byI, auto simp:o_def)

lemmas unitary_intros =
  unitary_bot unitary_top unitary_embed unitary_mult exp_conj_unitary
  unitary_comp unitary_const

lemmas sound_intros =
  mult_sound div_sound const_sound sound_o sound_sum
  tminus_sound sc_sound exp_conj_sound sum_sound

end
