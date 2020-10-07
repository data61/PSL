section \<open>Minsky machines\<close>

theory Minsky
  imports Recursive_Inseparability "Abstract-Rewriting.Abstract_Rewriting"
begin

text \<open>We formalize Minksy machines, and relate them to recursive functions. In our flavor of
Minsky machines, a machine has a set of registers and a set of labels, and a program is a set of
labeled operations. There are two operations, @{term Inc} and @{term Dec}; the former takes a
register and a label, and the latter takes a register and two labels. When an @{term Inc}
instruction is executed, the register is incremented and execution continues at the provided label.
The @{term Dec} instruction checks the register. If it is non-zero, the register and continues
execution at the first label. Otherwise, the register remains at zero and execution continues at
the second label.

We continue to show that Minksy machines can implement any primitive recursive function. Based on
that, we encode recursively enumerable sets as Minsky machines, and finally show that
\begin{enumerate}
\item The set of Minsky configurations such that from state $1$, state $0$ can be reached,
  is undecidable;
\item There is a deterministic Minsky machine $U$ such that the set of values $x$ such that
  $(2, \lambda n.\, \text{if $n = 0$ then $x$ else $0$})$ reach state $0$ is recursively
  inseparable from those that reach state $1$; and
\item As a corollary, the set of Minsky configurations that reach state $0$ but not state $1$ is
  recursively inseparable from the configurations that reach state $1$ but not state $0$.
\end{enumerate}\<close>

subsection \<open>Deterministic relations\<close>

text \<open>A relation $\to$ is \emph{deterministic} if $t \from s \to u'$ implies $t = u$.
This abstract rewriting notion is useful for talking about deterministic Minsky machines.\<close>

definition
  "deterministic R \<longleftrightarrow> R\<inverse> O R \<subseteq> Id"

lemma deterministicD:
  "deterministic R \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> (x, z) \<in> R \<Longrightarrow> y = z"
  by (auto simp: deterministic_def)

lemma deterministic_empty [simp]:
  "deterministic {}"
  by (auto simp: deterministic_def)

lemma deterministic_singleton [simp]:
  "deterministic {p}"
  by (auto simp: deterministic_def)

lemma deterministic_imp_weak_diamond [intro]:
  "deterministic R \<Longrightarrow> w\<diamond> R"
  by (auto simp: weak_diamond_def deterministic_def)

lemmas deterministic_imp_CR = deterministic_imp_weak_diamond[THEN weak_diamond_imp_CR]

lemma deterministic_union:
  "fst ` S \<inter> fst ` R = {} \<Longrightarrow> deterministic S \<Longrightarrow> deterministic R \<Longrightarrow> deterministic (S \<union> R)"
  by (fastforce simp add: deterministic_def disjoint_iff_not_equal)

lemma deterministic_map:
  "inj_on f (fst ` R) \<Longrightarrow> deterministic R \<Longrightarrow> deterministic (map_prod f g ` R)"
  by (auto simp add: deterministic_def dest!: inj_onD; force)


subsection \<open>Minsky machine definition\<close>

text \<open>A Minsky operation either decrements a register (testing for zero, with two possible
successor states), or increments a register (with one successor state). A Minsky machine is a
set of pairs of states and operations.\<close>

datatype ('s, 'v) Op = Dec (op_var: 'v) 's 's | Inc (op_var: 'v) 's

type_synonym ('s, 'v) minsky = "('s \<times> ('s, 'v) Op) set"

text \<open>Semantics: A Minsky machine operates on pairs consisting of a state and an assignment of
the registers; in each step, either a register is incremented, or a register is decremented,
provided it is non-zero. We write $\alpha$ for assignments; $\alpha[v]$ for the value of the
register $v$ in $\alpha$ and $\alpha[v := n]$ for the update of $v$ to $n$. Thus, the semantics
is as follows:
\begin{enumerate}
\item if $(s, Inc\ v\ s') \in M$ then $(s, \alpha) \to (s', \alpha[v := \alpha[v] + 1]$);
\item if $(s, Dec\ v\ s_n\ s_z) \in M$ and $\alpha[v] > 0$ then $(s, \alpha) \to (s_n, \alpha[v := \alpha[v] - 1]$); and
\item if $(s, Dec\ v\ s_n\ s_z) \in M$ and $\alpha[v] = 0$ then $(s, \alpha) \to (s_z, \alpha)$.
\end{enumerate}
A state is finite if there is no operation associated with it.\<close>

inductive_set step :: "('s, 'v) minsky \<Rightarrow> ('s \<times> ('v \<Rightarrow> nat)) rel" for M :: "('s, 'v) minsky" where
  inc: "(s, Inc v s') \<in> M \<Longrightarrow> ((s, vs), (s', \<lambda>x. if x = v then Suc (vs v) else vs x)) \<in> step M"
| decn: "(s, Dec v sn sz) \<in> M \<Longrightarrow> vs v = Suc n \<Longrightarrow> ((s, vs), (sn, \<lambda>x. if x = v then n else vs x)) \<in> step M"
| decz: "(s, Dec v sn sz) \<in> M \<Longrightarrow> vs v = 0 \<Longrightarrow> ((s, vs), (sz, vs)) \<in> step M"

lemma step_mono:
  "M \<subseteq> M' \<Longrightarrow> step M \<subseteq> step M'"
  by (auto elim: step.cases intro: step.intros)

lemmas steps_mono = rtrancl_mono[OF step_mono]

text \<open>A Minsky machine has deterministic steps if its defining relation between states and
operations is deterministic.\<close>

lemma deterministic_stepI [intro]:
  assumes "deterministic M" shows "deterministic (step M)"
proof -
  { fix s vs s1 vs1 s2 vs2
    assume s: "((s, vs), (s1, vs1)) \<in> step M" "((s, vs), (s2, vs2)) \<in> step M"
    have "(s1, vs1) = (s2, vs2)" using deterministicD[OF assms]
      by (cases rule: step.cases[OF s(1)]; cases rule: step.cases[OF s(2)]) fastforce+ }
  then show ?thesis by (auto simp: deterministic_def)
qed

text \<open>A Minksy machine halts when it reaches a state with no associated operation.\<close>

lemma NF_stepI [intro]:
  "s \<notin> fst ` M \<Longrightarrow> (s, vs) \<in> NF (step M)"
  by (auto intro!: no_step elim!: step.cases simp: rev_image_eqI)

text \<open>Deterministic Minsky machines enjoy unique normal forms.\<close>

lemmas deterministic_minsky_UN =
  join_NF_imp_eq[OF CR_divergence_imp_join[OF deterministic_imp_CR[OF deterministic_stepI]] NF_stepI NF_stepI]

text \<open>We will rename states and variables.\<close>

definition map_minsky where
  "map_minsky f g M = map_prod f (map_Op f g) ` M"

lemma map_minsky_id:
  "map_minsky id id M = M"
  by (simp add: map_minsky_def Op.map_id0 map_prod.id)

lemma map_minsky_comp:
  "map_minsky f g (map_minsky f' g' M) = map_minsky (f \<circ> f') (g \<circ> g') M"
  unfolding map_minsky_def image_comp Op.map_comp map_prod.comp comp_def[of "map_Op _ _"] ..

text \<open>When states and variables are renamed, computations carry over from the original machine,
provided that variables are renamed injectively.\<close>

lemma map_step:
  assumes "inj g" "vs = vs' \<circ> g" "((s, vs), (t, ws)) \<in> step M"
  shows "((f s, vs'), (f t, \<lambda>x. if x \<in> range g then ws (inv g x) else vs' x)) \<in> step (map_minsky f g M)"
  using assms(3)
proof (cases rule: step.cases)
  case (inc v) note [simp] = inc(1)
  let ?ws' = "\<lambda>w. if w = g v then Suc (vs' (g v)) else vs' w"
  have "((f s, vs'), (f t, ?ws')) \<in> step (map_minsky f g M)"
    using inc(2) step.inc[of "f s" "g v" "f t" "map_minsky f g M" vs']
    by (force simp: map_minsky_def)
  moreover have "(\<lambda>x. if x \<in> range g then ws (inv g x) else vs' x) = ?ws'"
    using assms(1,2) by (auto intro!: ext simp: injD image_def)
  ultimately show ?thesis by auto
next
  case (decn v sz n) note [simp] = decn(1)
  let ?ws' = "\<lambda>x. if x = g v then n else vs' x"
  have "((f s, vs'), (f t, ?ws')) \<in> step (map_minsky f g M)"
    using assms(2) decn(2-) step.decn[of "f s" "g v" "f t" "f sz" "map_minsky f g M" vs' n]
    by (force simp: map_minsky_def)
  moreover have "(\<lambda>x. if x \<in> range g then ws (inv g x) else vs' x) = ?ws'"
    using assms(1,2) by (auto intro!: ext simp: injD image_def)
  ultimately show ?thesis by auto
next
  case (decz v sn) note [simp] = decz(1)
  have "((f s, vs'), (f t, vs')) \<in> step (map_minsky f g M)"
    using assms(2) decz(2-) step.decz[of "f s" "g v" "f sn" "f t" "map_minsky f g M" vs']
    by (force simp: map_minsky_def)
  moreover have "(\<lambda>x. if x \<in> range g then ws (inv g x) else vs' x) = vs'"
    using assms(1,2) by (auto intro!: ext simp: injD image_def)
  ultimately show ?thesis by auto
qed

lemma map_steps:
  assumes "inj g" "vs = ws \<circ> g" "((s, vs), (t, vs')) \<in> (step M)\<^sup>*"
  shows "((f s, ws), (f t, \<lambda>x. if x \<in> range g then vs' (inv g x) else ws x)) \<in> (step (map_minsky f g M))\<^sup>*"
  using assms(3,2)
proof (induct "(s, vs)" arbitrary: s vs ws rule: converse_rtrancl_induct)
  case base
  then have "(\<lambda>x. if x \<in> range g then vs' (inv g x) else ws x) = ws"
    using assms(1) by (auto intro!: ext simp: injD image_def)
  then show ?case by auto
next
  case (step y)
  have "snd y = (\<lambda>x. if x \<in> range g then snd y (inv g x) else ws x) \<circ> g" (is "_ = ?ys' \<circ> _")
    using assms(1) by auto
  then show ?case  using map_step[OF assms(1) step(4), of s "fst y" "snd y" M f] step(1)
    step(3)[OF prod.collapse[symmetric], of ?ys'] by (auto cong: if_cong)
qed

subsection \<open>Concrete Minsky machines\<close>

text \<open>The following definition expresses when a Minsky machine $M$ implements a specification $P$.
We adopt the convention that computations always start out in state $1$ and end in state $0$, which
must be a final state. The specification $P$ relates initial assignments to final assignments.\<close>

definition mk_minsky_wit :: "(nat, nat) minsky \<Rightarrow> ((nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> bool" where
  "mk_minsky_wit M P \<equiv> finite M \<and> deterministic M \<and> 0 \<notin> fst ` M \<and>
     (\<forall>vs. \<exists>vs'. ((Suc 0, vs), (0, vs')) \<in> (step M)\<^sup>* \<and> P vs vs')"

abbreviation mk_minsky :: "((nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> bool) \<Rightarrow> bool" where
  "mk_minsky P \<equiv> \<exists>M. mk_minsky_wit M P"

lemmas mk_minsky_def = mk_minsky_wit_def

lemma mk_minsky_mono:
  shows "mk_minsky P \<Longrightarrow> (\<And>vs vs'. P vs vs' \<Longrightarrow> Q vs vs') \<Longrightarrow> mk_minsky Q"
  unfolding mk_minsky_def by meson

lemma mk_minsky_sound:
  assumes "mk_minsky_wit M P" "((Suc 0, vs), (0, vs')) \<in> (step M)\<^sup>*"
  shows "P vs vs'"
proof -
  have M: "deterministic M" "0 \<notin> fst ` M" "\<And>vs. \<exists>vs'. ((Suc 0, vs), 0, vs') \<in> (step M)\<^sup>* \<and> P vs vs'"
    using assms(1) by (auto simp: mk_minsky_wit_def)
  obtain vs'' where vs'': "((Suc 0, vs), (0, vs'')) \<in> (step M)\<^sup>*" "P vs vs''" using M(3) by blast
  have "(0 :: nat, vs') = (0, vs'')" using M(1,2)
    by (intro deterministic_minsky_UN[OF _ assms(2) vs''(1)])
  then show ?thesis using vs''(2) by simp
qed

text \<open>Realizability of $n$-ary functions for $n = 1 \dots 3$. Here we use the convention that the
arguments are passed in registers $1 \dots 3$, and the result is stored in register $0$.\<close>

abbreviation mk_minsky1 where
  "mk_minsky1 f \<equiv> mk_minsky (\<lambda>vs vs'. vs' 0 = f (vs 1))"

abbreviation mk_minsky2 where
  "mk_minsky2 f \<equiv> mk_minsky (\<lambda>vs vs'. vs' 0 = f (vs 1) (vs 2))"

abbreviation mk_minsky3 where
  "mk_minsky3 f \<equiv> mk_minsky (\<lambda>vs vs'. vs' 0 = f (vs 1) (vs 2) (vs 3))"

subsection \<open>Trivial building blocks\<close>

text \<open>We can increment and decrement any register.\<close>

lemma mk_minsky_inc:
  shows "mk_minsky (\<lambda>vs vs'. vs' = (\<lambda>x. if x = v then Suc (vs v) else vs x))"
  using step.inc[of "Suc 0" v 0]
  by (auto simp: deterministic_def mk_minsky_def intro!: exI[of _ "{(1, Inc v 0)} :: (nat, nat) minsky"])

lemma mk_minsky_dec:
  shows "mk_minsky (\<lambda>vs vs'. vs' = (\<lambda>x. if x = v then vs v - 1 else vs x))"
proof -
  let ?M = "{(1, Dec v 0 0)} :: (nat, nat) minsky"
  show ?thesis unfolding mk_minsky_def
  proof (intro exI[of _ ?M] allI conjI, goal_cases)
    case (4 vs)
    have [simp]: "vs v = 0 \<Longrightarrow> (\<lambda>x. if x = v then 0 else vs x) = vs" by auto
    show ?case using step.decz[of "Suc 0" v 0 0 ?M] step.decn[of "Suc 0" v 0 0 ?M]
      by (cases "vs v") (auto cong: if_cong)
  qed auto
qed

subsection \<open>Sequential composition\<close>

text \<open>The following lemma has two useful corollaries (which we prove simultaneously because they
share much of the proof structure): First, if $P$ and $Q$ are realizable, then so is $P \circ Q$.
Secondly, if we rename variables by an injective function $f$ in a Minksy machine, then the
variables outside the range of $f$ remain unchanged.\<close>

lemma mk_minsky_seq_map:
  assumes "mk_minsky P" "mk_minsky Q" "inj g"
    "\<And>vs vs' vs''. P vs vs' \<Longrightarrow> Q vs' vs'' \<Longrightarrow> R vs vs''"
  shows "mk_minsky (\<lambda>vs vs'. R (vs \<circ> g) (vs' \<circ> g) \<and> (\<forall>x. x \<notin> range g \<longrightarrow> vs x = vs' x))"
proof -
  obtain M where M: "finite M" "deterministic M" "0 \<notin> fst ` M"
    "\<And>vs. \<exists>vs'. ((Suc 0, vs), 0, vs') \<in> (step M)\<^sup>* \<and> P vs vs'"
    using assms(1) by (auto simp: mk_minsky_def)
  obtain N where N: "finite N" "deterministic N" "0 \<notin> fst ` N"
    "\<And>vs. \<exists>vs'. ((Suc 0, vs), 0, vs') \<in> (step N)\<^sup>* \<and> Q vs vs'"
    using assms(2) by (auto simp: mk_minsky_def)
  let ?fM = "\<lambda>s. if s = 0 then 2 else if s = 1 then 1 else 2 * s + 1" \<comment> \<open>M: from 1 to 2\<close>
  let ?fN = "\<lambda>s. 2 * s"                                               \<comment> \<open>N: from 2 to 0\<close>
  let ?M = "map_minsky ?fM g M \<union> map_minsky ?fN g N"
  show ?thesis unfolding mk_minsky_def
  proof (intro exI[of _ ?M] conjI allI, goal_cases)
    case 1 show ?case using M(1) N(1) by (auto simp: map_minsky_def)
  next
    case 2 show ?case using M(2,3) N(2) unfolding map_minsky_def
      by (intro deterministic_union deterministic_map)
        (auto simp: inj_on_def rev_image_eqI Suc_double_not_eq_double split: if_splits)
  next
    case 3 show ?case using N(3) by (auto simp: rev_image_eqI map_minsky_def split: if_splits)
  next
    case (4 vs)
    obtain vsM where M': "((Suc 0, vs \<circ> g), 0, vsM) \<in> (step M)\<^sup>*" "P (vs \<circ> g) vsM"
      using M(4) by blast
    obtain vsN where N': "((Suc 0, vsM), 0, vsN) \<in> (step N)\<^sup>*" "Q vsM vsN"
      using N(4) by blast
    note * = subsetD[OF steps_mono, of _ ?M]
      map_steps[OF _ _ M'(1), of g vs ?fM, simplified]
      map_steps[OF _ _ N'(1), of g _ ?fN, simplified]
    show ?case
      using assms(3,4) M'(2) N'(2) rtrancl_trans[OF *(1)[OF _ *(2)] *(1)[OF _ *(3)]]
      by (auto simp: comp_def)
  qed
qed

text \<open>Sequential composition.\<close>

lemma mk_minsky_seq:
  assumes "mk_minsky P" "mk_minsky Q"
    "\<And>vs vs' vs''. P vs vs' \<Longrightarrow> Q vs' vs'' \<Longrightarrow> R vs vs''"
  shows "mk_minsky R"
  using mk_minsky_seq_map[OF assms(1,2), of id] assms(3) by simp

lemma mk_minsky_seq':
  assumes "mk_minsky P" "mk_minsky Q"
  shows "mk_minsky (\<lambda>vs vs''. (\<exists>vs'. P vs vs' \<and> Q vs' vs''))"
  by (intro mk_minsky_seq[OF assms]) blast

text \<open>We can do nothing (besides transitioning from state 1 to state 0).\<close>

lemma mk_minsky_nop:
  "mk_minsky (\<lambda>vs vs'. vs = vs')"
  by (intro mk_minsky_seq[OF mk_minsky_inc mk_minsky_dec]) auto

text \<open>Renaming variables.\<close>

lemma mk_minsky_map:
  assumes "mk_minsky P" "inj f"
  shows "mk_minsky (\<lambda>vs vs'. P (vs \<circ> f) (vs' \<circ> f) \<and> (\<forall>x. x \<notin> range f \<longrightarrow> vs x = vs' x))"
  using mk_minsky_seq_map[OF assms(1) mk_minsky_nop assms(2)] by simp

lemma inj_shift [simp]:
  fixes a b :: nat
  assumes "a < b"
  shows "inj (\<lambda>x. if x = 0 then a else x + b)"
  using assms by (auto simp: inj_on_def)

subsection \<open>Bounded loop\<close>

text \<open>In the following lemma, $P$ is the specification of a loop body, and $Q$ the specification
of the loop itself (a loop invariant). The loop variable is $v$. $Q$ can be realized provided that
\begin{enumerate}
\item $P$ can be realized;
\item $P$ ensures that the loop variable is not changed by the loop body; and
\item $Q$ follows by induction on the loop variable:
  \begin{enumerate}
  \item $\alpha\,Q\,\alpha$ holds when $\alpha[v] = 0$; and
  \item $\alpha[v := n]\,P\,\alpha'$ and $\alpha'\,Q\,\alpha''$ imply $\alpha\,Q\,alpha''$
    when $\alpha[v] = n+1$.
  \end{enumerate}
\end{enumerate}\<close>

lemma mk_minsky_loop:
  assumes "mk_minsky P"
    "\<And>vs vs'. P vs vs' \<Longrightarrow> vs' v = vs v"
    "\<And>vs. vs v = 0 \<Longrightarrow> Q vs vs"
    "\<And>n vs vs' vs''. vs v = Suc n \<Longrightarrow> P (\<lambda>x. if x = v then n else vs x) vs' \<Longrightarrow> Q vs' vs'' \<Longrightarrow> Q vs vs''"
  shows "mk_minsky Q"
proof -
  obtain M where M: "finite M" "deterministic M" "0 \<notin> fst ` M"
    "\<And>vs. \<exists>vs'. ((Suc 0, vs), 0, vs') \<in> (step M)\<^sup>* \<and> P vs vs'"
    using assms(1) by (auto simp: mk_minsky_def)
  let ?M = "{(1, Dec v 2 0)} \<union> map_minsky Suc id M"
  show ?thesis unfolding mk_minsky_def
  proof (intro exI[of _ ?M] conjI allI, goal_cases)
    case 1 show ?case using M(1) by (auto simp: map_minsky_def)
  next
    case 2 show ?case using M(2,3) unfolding map_minsky_def
      by (intro deterministic_union deterministic_map) (auto simp: rev_image_eqI)
  next
    case 3 show ?case by (auto simp: map_minsky_def)
  next
    case (4 vs) show ?case
    proof (induct "vs v" arbitrary: vs)
      case 0 then show ?case using assms(3)[of vs] step.decz[of 1 v 2 0 ?M vs]
        by (auto simp: id_def)
    next
      case (Suc n)
      obtain vs' where M': "((Suc 0, \<lambda>x. if x = v then n else vs x), 0, vs') \<in> (step M)\<^sup>*"
        "P (\<lambda>x. if x = v then n else vs x) vs'" using M(4) by blast
      obtain vs'' where D: "((Suc 0, vs'), 0, vs'') \<in> (step ?M)\<^sup>*" "Q vs' vs''"
        using Suc(1)[of vs'] assms(2)[OF M'(2)] by auto
      note * = subsetD[OF steps_mono, of _ ?M]
        r_into_rtrancl[OF decn[of "Suc 0" v 2 0 ?M vs n]]
        map_steps[OF _ _ M'(1), of id _ Suc, simplified, OF refl, simplified, folded numeral_2_eq_2]
      show ?case using rtrancl_trans[OF rtrancl_trans, OF *(2) *(1)[OF _ *(3)] D(1)]
        D(2) Suc(2) assms(4)[OF _ M'(2), of vs''] by auto
    qed
  qed
qed

subsection \<open>Copying values\<close>

text \<open>We work up to copying values in several steps.
\begin{enumerate}
\item Clear a register. This is a loop that decrements the register until it reaches $0$.
\item Add a register to another one. This is a loop that decrements one register, and increments
  the other register, until the first register reaches 0.
\item Add a register to two others. This is the same, except that two registers are incremented.
\item Move a register: set a register to 0, then add another register to it.
\item Copy a register destructively: clear two registers, then add another register to them.
\end{enumerate}\<close>

lemma mk_minsky_zero:
  shows "mk_minsky (\<lambda>vs vs'. vs' = (\<lambda>x. if x = v then 0 else vs x))"
  by (intro mk_minsky_loop[where v = v, OF \<comment> \<open> while v[v]$--$: \<close>
    mk_minsky_nop]) auto                   \<comment> \<open>   pass          \<close>

lemma mk_minsky_add1:
  assumes "v \<noteq> w"
  shows "mk_minsky (\<lambda>vs vs'. vs' = (\<lambda>x. if x = v then 0 else if x = w then vs v + vs w else vs x))"
  using assms by (intro mk_minsky_loop[where v = v, OF \<comment> \<open> while v[v]$--$: \<close>
    mk_minsky_inc[of w]]) auto                         \<comment> \<open>   v[w]++        \<close>

lemma mk_minsky_add2:
  assumes "u \<noteq> v" "u \<noteq> w" "v \<noteq> w"
  shows "mk_minsky (\<lambda>vs vs'. vs' =
    (\<lambda>x. if x = u then 0 else if x = v then vs u + vs v else if x = w then vs u + vs w else vs x))"
  using assms by (intro mk_minsky_loop[where v = u, OF mk_minsky_seq'[OF \<comment> \<open> while v[u]$--$: \<close>
    mk_minsky_inc[of v]                                                  \<comment> \<open>   v[v]++        \<close>
    mk_minsky_inc[of w]]]) auto                                          \<comment> \<open>   v[w]++        \<close>

lemma mk_minsky_copy1:
  assumes "v \<noteq> w"
  shows "mk_minsky (\<lambda>vs vs'. vs' = (\<lambda>x. if x = v then 0 else if x = w then vs v else vs x))"
  using assms by (intro mk_minsky_seq[OF
    mk_minsky_zero[of w]          \<comment> \<open> v[w] := 0                      \<close>
    mk_minsky_add1[of v w]]) auto \<comment> \<open> v[w] := v[w] + v[v], v[v] := 0 \<close>

lemma mk_minsky_copy2:
  assumes "u \<noteq> v" "u \<noteq> w" "v \<noteq> w"
  shows "mk_minsky (\<lambda>vs vs'. vs' =
    (\<lambda>x. if x = u then 0 else if x = v then vs u else if x = w then vs u else vs x))"
  using assms by (intro mk_minsky_seq[OF mk_minsky_seq', OF
    mk_minsky_zero[of v]            \<comment> \<open> v[v] := 0                                           \<close>
    mk_minsky_zero[of w]            \<comment> \<open> v[w] := 0                                           \<close>
    mk_minsky_add2[of u v w]]) auto \<comment> \<open> v[v] := v[v] + v[u], v[w] := v[w] + v[u], v[u] := 0 \<close>

lemma mk_minsky_copy:
  assumes "u \<noteq> v" "u \<noteq> w" "v \<noteq> w"
  shows "mk_minsky (\<lambda>vs vs'. vs' = (\<lambda>x. if x = v then vs u else if x = w then 0 else vs x))"
  using assms by (intro mk_minsky_seq[OF
    mk_minsky_copy2[of u v w]      \<comment> \<open> v[v] := v[u], v[w] := v[u], v[u] := 0 \<close>
    mk_minsky_copy1[of w u]]) auto \<comment> \<open> v[u] := v[w], v[w] := 0               \<close>

subsection \<open>Primitive recursive functions\<close>

text \<open>Nondestructive apply: compute $f$ on arguments $\alpha[u]$, $\alpha[v]$, $\alpha[w]$,
storing the result in $\alpha[t]$ and preserving all other registers below $k$. This is easy
now that we can copy values.\<close>

lemma mk_minsky_apply3:
  assumes "mk_minsky3 f" "t < k" "u < k" "v < k" "w < k"
  shows "mk_minsky (\<lambda>vs vs'. \<forall>x < k. vs' x = (if x = t then f (vs u) (vs v) (vs w) else vs x))"
  using assms(2-)
  by (intro mk_minsky_seq[OF mk_minsky_seq'[OF mk_minsky_seq'], OF
    mk_minsky_copy[of u "1 + k" k] \<comment> \<open> v[1+k] := v[u] \<close>
    mk_minsky_copy[of v "2 + k" k] \<comment> \<open> v[2+k] := v[v] \<close>
    mk_minsky_copy[of w "3 + k" k] \<comment> \<open> v[3+k] := v[w] \<close>
    mk_minsky_map[OF assms(1), of "\<lambda>x. if x = 0 then t else x + k"]]) (auto 0 2)
                                   \<comment> \<open> v[t] := f v[1+k] v[2+k] v[3+k] \<close>

text \<open>Composition is just four non-destructive applies.\<close>

lemma mk_minsky_comp3_3:
  assumes "mk_minsky3 f" "mk_minsky3 g" "mk_minsky3 h" "mk_minsky3 k"
  shows "mk_minsky3 (\<lambda>x y z. f (g x y z) (h x y z) (k x y z))"
  by (rule mk_minsky_seq[OF mk_minsky_seq'[OF mk_minsky_seq'], OF
    mk_minsky_apply3[OF assms(2), of 4 7 1 2 3]        \<comment> \<open> v[4] := g v[1] v[2] v[3] \<close>
    mk_minsky_apply3[OF assms(3), of 5 7 1 2 3]        \<comment> \<open> v[5] := h v[1] v[2] v[3] \<close>
    mk_minsky_apply3[OF assms(4), of 6 7 1 2 3]        \<comment> \<open> v[6] := k v[1] v[2] v[3] \<close>
    mk_minsky_apply3[OF assms(1), of 0 7 4 5 6]]) auto \<comment> \<open> v[0] := f v[4] v[5] v[6] \<close>

text \<open>Primitive recursion is a non-destructive apply followed by a loop with another
non-destructive apply. The key to the proof is the loop invariant, which we can specify
as part of composing the various \<open>mk_minsky_*\<close> lemmas.\<close>

lemma mk_minsky_prim_rec:
  assumes "mk_minsky1 g" "mk_minsky3 h"
  shows "mk_minsky2 (PrimRecOp g h)"
  by (intro mk_minsky_seq[OF mk_minsky_seq', OF
    mk_minsky_apply3[OF assms(1), of 0 4 2 2 2]       \<comment> \<open> v[0] := g v[2]             \<close>
    mk_minsky_zero[of 3]                              \<comment> \<open> v[3] := 0                  \<close>
    mk_minsky_loop[where v = 1, OF mk_minsky_seq', OF \<comment> \<open> while v[1]$--$:            \<close>
      mk_minsky_apply3[OF assms(2), of 0 4 3 0 2]     \<comment> \<open>   v[0] := h v[3] v[0] v[2] \<close>
      mk_minsky_inc[of 3],                            \<comment> \<open>   v[3]++                   \<close>
      of "\<lambda>vs vs'. vs 0 = PrimRecOp g h (vs 3) (vs 2) \<longrightarrow> vs' 0 = PrimRecOp g h (vs 3 + vs 1) (vs 2)"
    ]]) auto

text \<open>With these building blocks we can easily show that all primitive recursive functions can
be realized by a Minsky machine.\<close>

lemma mk_minsky_PrimRec:
  "f \<in> PrimRec1 \<Longrightarrow> mk_minsky1 f"
  "g \<in> PrimRec2 \<Longrightarrow> mk_minsky2 g"
  "h \<in> PrimRec3 \<Longrightarrow> mk_minsky3 h"
proof (goal_cases)
  have *: "(f \<in> PrimRec1 \<longrightarrow> mk_minsky1 f) \<and> (g \<in> PrimRec2 \<longrightarrow> mk_minsky2 g) \<and> (h \<in> PrimRec3 \<longrightarrow> mk_minsky3 h)"
  proof (induction rule: PrimRec1_PrimRec2_PrimRec3.induct)
    case zero show ?case by (intro mk_minsky_mono[OF mk_minsky_zero]) auto
  next
    case suc show ?case by (intro mk_minsky_seq[OF mk_minsky_copy1[of 1 0] mk_minsky_inc[of 0]]) auto
  next
    case id1_1 show ?case by (intro mk_minsky_mono[OF mk_minsky_copy1[of 1 0]]) auto
  next
    case id2_1 show ?case by (intro mk_minsky_mono[OF mk_minsky_copy1[of 1 0]]) auto
  next
    case id2_2 show ?case by (intro mk_minsky_mono[OF mk_minsky_copy1[of 2 0]]) auto
  next
    case id3_1 show ?case by (intro mk_minsky_mono[OF mk_minsky_copy1[of 1 0]]) auto
  next
    case id3_2 show ?case by (intro mk_minsky_mono[OF mk_minsky_copy1[of 2 0]]) auto
  next
    case id3_3 show ?case by (intro mk_minsky_mono[OF mk_minsky_copy1[of 3 0]]) auto
  next
    case (comp1_1 f g) then show ?case using mk_minsky_comp3_3 by fast
  next
    case (comp1_2 f g) then show ?case using mk_minsky_comp3_3 by fast
  next
    case (comp1_3 f g) then show ?case using mk_minsky_comp3_3 by fast
  next
    case (comp2_1 f g h) then show ?case using mk_minsky_comp3_3 by fast
  next
    case (comp3_1 f g h k) then show ?case using mk_minsky_comp3_3 by fast
  next
    case (comp2_2 f g h) then show ?case using mk_minsky_comp3_3 by fast
  next
    case (comp2_3 f g h) then show ?case using mk_minsky_comp3_3 by fast
  next
    case (comp3_2 f g h k) then show ?case using mk_minsky_comp3_3 by fast
  next
    case (comp3_3 f g h k) then show ?case using mk_minsky_comp3_3 by fast
  next
    case (prim_rec g h) then show ?case using mk_minsky_prim_rec by blast
  qed
  { case 1 thus ?case using * by blast next
    case 2 thus ?case using * by blast next
    case 3 thus ?case using * by blast }
qed

subsection \<open>Recursively enumerable sets as Minsky machines\<close>

text \<open>The following is the most complicated lemma of this theory: Given two r.e.\ sets $A$ and $B$
we want to construct a Minsky machine that reaches the final state $0$ for input $x$ if $x \in A$
and final state $1$ if $x \in B$, and never reaches either of these states if $x \notin A \cup B$.
(If $x \in A \cap B$, then either state $0$ or state $1$ may be reached.) We consider two
r.e.\ sets rather than one because we target recursive inseparability.

For the r.e.\ set $A$, there is a primitive recursive function $f$ such that
$x \in A \iff \exists y.\, f(x,y) = 0$. Similarly there is a primitive recursive function $g$ for
$B$ such that $x \in B \iff \exists y.\, f(x,y) = 0$. Our Minsky machine takes $x$ in register
$0$ and $y$ in register $1$ (initially $0$) and works as follows.
\begin{enumerate}
\item evaluate $f(x,y)$; if the result is $0$, transition to state $0$; otherwise,
\item evaluate $g(x,y)$; if the result is $0$, transition to state $1$; otherwise,
\item increment $y$ and start over.
\end{enumerate}\<close>

lemma ce_set_pair_by_minsky:
  assumes "A \<in> ce_sets" "B \<in> ce_sets"
  obtains M :: "(nat, nat) minsky" where
    "finite M" "deterministic M" "0 \<notin> fst ` M" "Suc 0 \<notin> fst ` M"
    "\<And>x vs. vs 0 = x \<Longrightarrow> vs 1 = 0 \<Longrightarrow> x \<in> A \<union> B \<Longrightarrow>
     \<exists>vs'. ((2, vs), (0, vs')) \<in> (step M)\<^sup>* \<or> ((2, vs), (Suc 0, vs')) \<in> (step M)\<^sup>*"
    "\<And>x vs vs'. vs 0 = x \<Longrightarrow> vs 1 = 0 \<Longrightarrow> ((2, vs), (0, vs')) \<in> (step M)\<^sup>* \<Longrightarrow> x \<in> A"
    "\<And>x vs vs'. vs 0 = x \<Longrightarrow> vs 1 = 0 \<Longrightarrow> ((2, vs), (Suc 0, vs')) \<in> (step M)\<^sup>* \<Longrightarrow> x \<in> B"
proof -
  obtain g where g: "g \<in> PrimRec2" "\<And>x. x \<in> A \<longleftrightarrow> (\<exists>y. g x y = 0)"
    using assms(1) by (auto simp: ce_sets_def fn_to_set_def)
  obtain h where h: "h \<in> PrimRec2" "\<And>x. x \<in> B \<longleftrightarrow> (\<exists>y. h x y = 0)"
    using assms(2) by (auto simp: ce_sets_def fn_to_set_def)
  have "mk_minsky (\<lambda>vs vs'. vs' 0 = vs 0 \<and> vs' 1 = vs 1 \<and> vs' 2 = g (vs 0) (vs 1))"
    using mk_minsky_seq[OF
      mk_minsky_apply3[OF mk_minsky_PrimRec(2)[OF g(1)], of 2 3 0 1 0] \<comment> \<open> v[2] := g v[0] v[1] \<close>
      mk_minsky_nop] by auto                                           \<comment> \<open> pass                \<close>
  then obtain M :: "(nat, nat) minsky" where M: "finite M" "deterministic M" "0 \<notin> fst ` M"
    "\<And>vs. \<exists>vs'. ((Suc 0, vs), 0, vs') \<in> (step M)\<^sup>* \<and>
    vs' 0 = vs 0 \<and> vs' 1 = vs 1 \<and> vs' 2 = g (vs 0) (vs 1)"
    unfolding mk_minsky_def by blast
  have "mk_minsky (\<lambda>vs vs'. vs' 0 = vs 0 \<and> vs' 1 = vs 1 + 1 \<and> vs' 2 = h (vs 0) (vs 1))"
    using mk_minsky_seq[OF
      mk_minsky_apply3[OF mk_minsky_PrimRec(2)[OF h(1)], of 2 3 0 1 0] \<comment> \<open> v[2] := h v[0] v[1] \<close>
      mk_minsky_inc[of 1]] by auto                                     \<comment> \<open> v[1] := v[1] + 1    \<close>
  then obtain N :: "(nat, nat) minsky" where N: "finite N" "deterministic N" "0 \<notin> fst ` N"
    "\<And>vs. \<exists>vs'. ((Suc 0, vs), 0, vs') \<in> (step N)\<^sup>* \<and>
    vs' 0 = vs 0 \<and> vs' 1 = vs 1 + 1 \<and> vs' 2 = h (vs 0) (vs 1)"
    unfolding mk_minsky_def by blast
  let ?f = "\<lambda>s. if s = 0 then 3 else 2 * s" \<comment> \<open>M: from state 4 to state 3\<close>
  let ?g = "\<lambda>s. 2 * s + 5"                  \<comment> \<open>N: from state 7 to state 5\<close>
  define X where "X = map_minsky ?f id M \<union> map_minsky ?g id N \<union> {(3, Dec 2 7 0)} \<union> {(5, Dec 2 2 1)}"
  have MX: "map_minsky ?f id M \<subseteq> X" by (auto simp: X_def)
  have NX: "map_minsky ?g id N \<subseteq> X" by (auto simp: X_def)
  have DX: "(3, Dec 2 7 0) \<in> X" "(5, Dec 2 2 1) \<in> X" by (auto simp: X_def)
  have X1: "finite X" using M(1) N(1) by (auto simp: map_minsky_def X_def)
  have X2: "deterministic X" unfolding X_def using M(2,3) N(2,3)
    apply (intro deterministic_union)
    by (auto simp: map_minsky_def rev_image_eqI inj_on_def split: if_splits
      intro!: deterministic_map) presburger+
  have X3: "0 \<notin> fst ` X" "Suc 0 \<notin> fst ` X" using M(3) N(3)
    by (auto simp: X_def map_minsky_def split: if_splits)
  have X4: "\<exists>vs'. g (vs 0) (vs 1) = 0 \<and> ((2, vs), (0, vs')) \<in> (step X)\<^sup>* \<or>
    h (vs 0) (vs 1) = 0 \<and> ((2, vs), (1, vs')) \<in> (step X)\<^sup>* \<or>
    g (vs 0) (vs 1) \<noteq> 0 \<and> h (vs 0) (vs 1) \<noteq> 0 \<and> vs' 0 = vs 0 \<and> vs' 1 = vs 1 + 1 \<and>
    ((2, vs), (2, vs')) \<in> (step X)\<^sup>+" for vs
  proof -
    guess vs' using M(4)[of vs] by (elim exE conjE) note vs' = this
    have 1: "((2, vs), (3, vs')) \<in> (step X)\<^sup>*"
      using subsetD[OF steps_mono[OF MX], OF map_steps[OF _ _ vs'(1), of id vs ?f]] by simp
    show ?thesis
    proof (cases "vs' 2")
      case 0 then show ?thesis using decz[OF DX(1), of vs'] vs' 1
        by (auto intro: rtrancl_into_rtrancl)
    next
      case (Suc n) note Suc' = Suc
      let ?vs = "\<lambda>x. if x = 2 then n else vs' x"
      have 2: "((2, vs), (7, ?vs)) \<in> (step X)\<^sup>*"
        using 1 decn[OF DX(1), of vs'] Suc by (auto intro: rtrancl_into_rtrancl)
      guess vs'' using N(4)[of "?vs"] by (elim exE conjE) note vs'' = this
      have 3: "((2, vs), (5, vs'')) \<in> (step X)\<^sup>*"
        using 2 subsetD[OF steps_mono[OF NX], OF map_steps[OF _ _ vs''(1), of id ?vs ?g]] by simp
      show ?thesis
      proof (cases "vs'' 2")
        case 0 then show ?thesis using 3 decz[OF DX(2), of vs''] vs''(2-) vs'(2-)
          by (auto intro: rtrancl_into_rtrancl)
      next
        case (Suc m)
        let ?vs = "\<lambda>x. if x = 2 then m else vs'' x"
        have 4: "((2, vs), (2, ?vs)) \<in> (step X)\<^sup>+" using 3 decn[OF DX(2), of vs'' m] Suc by auto
        then show ?thesis using vs''(2-) vs'(2-) Suc Suc' by (auto intro!: exI[of _ ?vs])
      qed
    qed
  qed
  have *: "vs 1 \<le> y \<Longrightarrow> g (vs 0) y = 0 \<or> h (vs 0) y = 0 \<Longrightarrow>
    \<exists>vs'. ((2, vs), (0, vs')) \<in> (step X)\<^sup>* \<or> ((2, vs), (1, vs')) \<in> (step X)\<^sup>*" for vs y
  proof (induct "vs 1" arbitrary: vs rule: inc_induct, goal_cases base step)
    case (base vs) then show ?case using X4[of vs] by auto
  next
    case (step vs)
    guess vs' using X4[of vs] by (elim exE)
    then show ?case unfolding ex_disj_distrib using step(4) step(3)[of vs']
      by (auto dest!: trancl_into_rtrancl) (meson rtrancl_trans)+
  qed
  have **: "((s, vs), (t, ws)) \<in> (step X)\<^sup>* \<Longrightarrow> t \<in> {0, 1} \<Longrightarrow> ((s, vs), (2, ws')) \<in> (step X)\<^sup>* \<Longrightarrow>
    \<exists>y. if t = 0 then g (ws' 0) y = 0 else h (ws' 0) y = 0" for s t vs ws' ws
  proof (induct arbitrary: ws' rule: converse_rtrancl_induct2)
    case refl show ?case using refl(1) NF_not_suc[OF refl(2) NF_stepI] X3 by auto
  next
    case (step s vs s' vs')
    show ?case using step(5)
    proof (cases rule: converse_rtranclE[case_names base' step'])
      case base'
      note *** = deterministic_minsky_UN[OF X2 _ _ X3]
      show ?thesis using X4[of ws']
      proof (elim exE disjE conjE, goal_cases)
        case (1 vs'') then show ?case using step(1,2,4) ***[of "(2,ws')" vs'' ws]
          by (auto simp: base' intro: converse_rtrancl_into_rtrancl)
      next
        case (2 vs'') then show ?case using step(1,2,4) ***[of "(2,ws')" ws vs'']
          by (auto simp: base' intro: converse_rtrancl_into_rtrancl)
      next
        case (3 vs'') then show ?case using step(2) step(3)[of vs'', OF step(4)]
          deterministicD[OF deterministic_stepI[OF X2], OF _ step(1)]
          by (auto simp: base' if_bool_eq_conj trancl_unfold_left)
      qed
    next
      case (step' y) then show ?thesis
        by (metis deterministicD[OF deterministic_stepI[OF X2]] step(1) step(3)[OF step(4)])
    qed
  qed
  show ?thesis
  proof (intro that[of X] X1 X2 X3, goal_cases)
    case (1 x vs) then show ?case using *[of vs] by (auto simp: g(2) h(2))
  next
    case (2 x vs vs') then show ?case using **[of 2 vs 0 vs' vs] by (auto simp: g(2) h(2))
  next
    case (3 x vs vs') then show ?case using **[of 2 vs 1 vs' vs] by (auto simp: g(2) h(2))
  qed
qed

text \<open>For r.e.\ sets we obtain the following lemma as a special case (taking $B = \varnothing$,
and swapping states $1$ and $2$).\<close>

lemma ce_set_by_minsky:
  assumes "A \<in> ce_sets"
  obtains M :: "(nat, nat) minsky" where
    "finite M" "deterministic M" "0 \<notin> fst ` M"
    "\<And>x vs. vs 0 = x \<Longrightarrow> vs 1 = 0 \<Longrightarrow> x \<in> A \<Longrightarrow> \<exists>vs'. ((Suc 0, vs), (0, vs')) \<in> (step M)\<^sup>*"
    "\<And>x vs vs'. vs 0 = x \<Longrightarrow> vs 1 = 0 \<Longrightarrow> ((Suc 0, vs), (0, vs')) \<in> (step M)\<^sup>* \<Longrightarrow> x \<in> A"
proof -
  guess M using ce_set_pair_by_minsky[OF assms(1) ce_empty] . note M = this
  let ?f = "\<lambda>s. if s = 1 then 2 else if s = 2 then 1 else s" \<comment> \<open>swap states 1 and 2\<close>
  have "?f \<circ> ?f = id" by auto
  define N where "N = map_minsky ?f id M"
  have M_def: "M = map_minsky ?f id N"
    unfolding N_def map_minsky_comp \<open>?f \<circ> ?f = id\<close> map_minsky_id o_id ..
  show ?thesis using M(1-3)
  proof (intro that[of N], goal_cases)
    case (4 x vs) show ?case using M(5)[OF 4(4,5)] 4(6) M(7)[OF 4(4,5)]
      map_steps[of id vs vs 2 0 _ M ?f] by (auto simp: N_def)
  next
    case (5 x vs vs') show ?case
      using M(6)[OF 5(4,5)] 5(6) map_steps[of id vs vs 1 0 _ N ?f] by (auto simp: M_def)
  qed (auto simp: N_def map_minsky_def inj_on_def rev_image_eqI deterministic_map split: if_splits)
qed

subsection \<open>Encoding of Minsky machines\<close>

text \<open>So far, Minsky machines have been sets of pairs of states and operations. We now provide an
encoding of Minsky machines as natural numbers, so that we can talk about them as r.e.\ or
computable sets. First we encode operations.\<close>

primrec encode_Op :: "(nat, nat) Op \<Rightarrow> nat" where
  "encode_Op (Dec v s s') = c_pair 0 (c_pair v (c_pair s s'))"
| "encode_Op (Inc v s) = c_pair 1 (c_pair v s)"

definition decode_Op :: "nat \<Rightarrow> (nat, nat) Op" where
  "decode_Op n = (if c_fst n = 0
   then Dec (c_fst (c_snd n)) (c_fst (c_snd (c_snd n))) (c_snd (c_snd (c_snd n)))
   else Inc (c_fst (c_snd n)) (c_snd (c_snd n)))"

lemma encode_Op_inv [simp]:
  "decode_Op (encode_Op x) = x"
  by (cases x) (auto simp: decode_Op_def)

text \<open>Minsky machines are encoded via lists of pairs of states and operations.\<close>

definition encode_minsky :: "(nat \<times> (nat, nat) Op) list \<Rightarrow> nat" where
  "encode_minsky M = list_to_nat (map (\<lambda>x. c_pair (fst x) (encode_Op (snd x))) M)"

definition decode_minsky :: "nat \<Rightarrow> (nat \<times> (nat, nat) Op) list" where
  "decode_minsky n = map (\<lambda>n. (c_fst n, decode_Op (c_snd n))) (nat_to_list n)"

lemma encode_minsky_inv [simp]:
  "decode_minsky (encode_minsky M) = M"
  by (auto simp: encode_minsky_def decode_minsky_def comp_def)

text \<open>Assignments are stored as lists (starting with register 0).\<close>

definition decode_regs :: "nat \<Rightarrow> (nat \<Rightarrow> nat)" where
  "decode_regs n = (\<lambda>i. let xs = nat_to_list n in if i < length xs then nat_to_list n ! i else 0)"

text \<open>The undecidability results talk about Minsky configurations (pairs of Minsky machines and
assignments). This means that we do not have to construct any recursive functions that modify
Minsky machines (for example in order to initialize variables), keeping the proofs simple.\<close>

definition decode_minsky_state :: "nat \<Rightarrow> ((nat, nat) minsky \<times> (nat \<Rightarrow> nat))" where
  "decode_minsky_state n = (set (decode_minsky (c_fst n)), (decode_regs (c_snd n)))"

subsection \<open>Undecidablity results\<close>

text \<open>We conclude with some undecidability results. First we show that it is undecidable whether
a Minksy machine starting at state 1 terminates in state 0.\<close>

definition minsky_reaching_0 where
  "minsky_reaching_0 = {n |n M vs vs'. (M, vs) = decode_minsky_state n \<and> ((Suc 0, vs), (0, vs')) \<in> (step M)\<^sup>*}"

lemma minsky_reaching_0_not_computable:
  "\<not> computable minsky_reaching_0"
proof -
  guess U using ce_set_by_minsky[OF univ_is_ce] . note U = this
  obtain us where [simp]: "set us = U" using finite_list[OF U(1)] by blast
  let ?f = "\<lambda>n. c_pair (encode_minsky us) (c_cons n 0)"
  have "?f \<in> PrimRec1"
    using comp2_1[OF c_pair_is_pr const_is_pr comp2_1[OF c_cons_is_pr id1_1 const_is_pr]] by simp
  moreover have "?f x \<in> minsky_reaching_0 \<longleftrightarrow> x \<in> univ_ce" for x
    using U(4,5)[of "\<lambda>i. if i = 0 then x else 0"]
    by (auto simp: minsky_reaching_0_def decode_minsky_state_def decode_regs_def c_cons_def cong: if_cong)
  ultimately have "many_reducible_to univ_ce minsky_reaching_0"
    by (auto simp: many_reducible_to_def many_reducible_to_via_def dest: pr_is_total_rec)
  then show ?thesis by (rule many_reducible_lm_1)
qed

text \<open>The remaining results are resursive inseparability results. We start be showing that there
is a Minksy machine $U$ with final states $0$ and $1$ such that it is not possible to recursively
separate inputs reaching state $0$ from inputs reaching state $1$.\<close>

lemma rec_inseparable_0not1_1not0:
  "rec_inseparable {p. 0 \<in> nat_to_ce_set p \<and> 1 \<notin> nat_to_ce_set p} {p. 0 \<notin> nat_to_ce_set p \<and> 1 \<in> nat_to_ce_set p}"
proof -
  obtain n where n: "nat_to_ce_set n = {0}" using nat_to_ce_set_srj[OF ce_finite[of "{0}"]] by auto
  obtain m where m: "nat_to_ce_set m = {1}" using nat_to_ce_set_srj[OF ce_finite[of "{1}"]] by auto
  show ?thesis by (rule rec_inseparable_mono[OF Rice_rec_inseparable[of n m]]) (auto simp: n m)
qed

lemma ce_sets_containing_n_ce:
  "{p. n \<in> nat_to_ce_set p} \<in> ce_sets"
  using ce_set_lm_5[OF univ_is_ce comp2_1[OF c_pair_is_pr id1_1 const_is_pr[of n]]]
  by (auto simp: univ_ce_lm_1)

lemma rec_inseparable_fixed_minsky_reaching_0_1:
  obtains U :: "(nat, nat) minsky" where
    "finite U" "deterministic U" "0 \<notin> fst ` U" "1 \<notin> fst ` U"
    "rec_inseparable {x |x vs'. ((2, (\<lambda>n. if n = 0 then x else 0)), (0, vs')) \<in> (step U)\<^sup>*}
      {x |x vs'. ((2, (\<lambda>n. if n = 0 then x else 0)), (1, vs')) \<in> (step U)\<^sup>*}"
proof -
  guess U using ce_set_pair_by_minsky[OF ce_sets_containing_n_ce ce_sets_containing_n_ce, of 0 1] .
  from this(1-4) this(5-7)[of "\<lambda>n. if n = 0 then _ else 0"]
  show ?thesis by (auto 0 0 intro!: that[of U] rec_inseparable_mono[OF rec_inseparable_0not1_1not0]
      pr_is_total_rec simp: rev_image_eqI cong: if_cong) meson+
qed

text \<open>Consequently, it is impossible to separate Minsky configurations with determistic machines
and final states $0$ and $1$ that reach state $0$ from those that reach state $1$.\<close>

definition minsky_reaching_s where
  "minsky_reaching_s s = {m |M m vs vs'. (M, vs) = decode_minsky_state m \<and>
    deterministic M \<and> 0 \<notin> fst ` M \<and> 1 \<notin> fst ` M \<and> ((2, vs), (s, vs')) \<in> (step M)\<^sup>*}"

lemma rec_inseparable_minsky_reaching_0_1:
  "rec_inseparable (minsky_reaching_s 0) (minsky_reaching_s 1)"
proof -
  guess U using rec_inseparable_fixed_minsky_reaching_0_1 . note U = this
  obtain us where [simp]: "set us = U" using finite_list[OF U(1)] by blast
  let ?f = "\<lambda>n. c_pair (encode_minsky us) (c_cons n 0)"
  have "?f \<in> PrimRec1"
    using comp2_1[OF c_pair_is_pr const_is_pr comp2_1[OF c_cons_is_pr id1_1 const_is_pr]] by simp
  then show ?thesis
    using U(1-4) rec_inseparable_many_reducible[of ?f, OF _ rec_inseparable_mono[OF U(5)]]
    by (auto simp: pr_is_total_rec minsky_reaching_s_def decode_minsky_state_def rev_image_eqI
      decode_regs_def c_cons_def cong: if_cong)
qed

text \<open>As a corollary, it is impossible to separate Minsky configurations that reach state 0 but not
state 1 from those that reach state 1 but not state 0.\<close>

definition minsky_reaching_s_not_t where
  "minsky_reaching_s_not_t s t = {m |M m vs vs'. (M, vs) = decode_minsky_state m \<and>
    ((2, vs), (s, vs')) \<in> (step M)\<^sup>* \<and> ((2, vs), (t, vs')) \<notin> (step M)\<^sup>*}"

lemma minsky_reaching_s_imp_minsky_reaching_s_not_t:
  assumes "s \<in> {0,1}" "t \<in> {0,1}" "s \<noteq> t"
  shows "minsky_reaching_s s \<subseteq> minsky_reaching_s_not_t s t"
proof -
  have [dest!]: "((2, vs), (0, vs')) \<notin> (step M)\<^sup>* \<or> ((2, vs), (1, vs')) \<notin> (step M)\<^sup>*"
    if "deterministic M" "0 \<notin> fst ` M" "1 \<notin> fst ` M" for M :: "(nat, nat) minsky" and vs vs'
    using deterministic_minsky_UN[OF that(1) _ _ that(2,3)] by auto
  show ?thesis using assms
    by (auto simp: minsky_reaching_s_def minsky_reaching_s_not_t_def rev_image_eqI)
qed

lemma rec_inseparable_minsky_reaching_0_not_1_1_not_0:
  "rec_inseparable (minsky_reaching_s_not_t 0 1) (minsky_reaching_s_not_t 1 0)"
  by (intro rec_inseparable_mono[OF rec_inseparable_minsky_reaching_0_1]
    minsky_reaching_s_imp_minsky_reaching_s_not_t) simp_all

end
