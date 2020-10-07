(*
Author:  Jérémy Dubut (2019)
Author:  Akihisa Yamada (2019)
License: LGPL (see file COPYING.LESSER)
*)
section \<open>Knaster--Tarski-Style Fixed-Point Theorem\<close>

theory Fixed_Points
  imports Complete_Relations
begin

text \<open>Given a monotone map
$f : A \to A$ on a complete lattice $\tp{A,\SLE}$,
the Knaster--Tarski theorem~\cite{tarski55} states that
\begin{enumerate}
\item $f$ has a fixed point in $A$, and
\item the set of fixed points forms a complete lattice.
\end{enumerate}
Stauti and Maaden \cite{SM13} generalized statement (1) where $\tp{A,\SLE}$
is a complete \emph{trellis}---a complete pseudo-order---%
relaxing transitivity.
They also proved a restricted version of (2),
namely there exists a least (and by duality a greatest) fixed point in $A$.

In the following Section~\ref{sec:qfp-exists} we further generalize claim (1)
so that any complete relation
admits a \emph{quasi-fixed point} $f(x) \sim x$, that is, $f(x) \SLE x$ and $x \SLE f(x)$.
Quasi-fixed points are fixed points for antisymmetric relations;
hence the Stauti--Maaden theorem is further generalized by relaxing reflexivity.

In Section \ref{sec:qfp-complete}
we also generalize claim (2) so that only a mild condition, which we call \emph{attractivity},
is assumed. In this attractive setting quasi-fixed points are complete.
Since attractivity is implied by either of transitivity or antisymmetry,
in particular fixed points are complete in complete trellis,
thus completing Stauti and Maaden's result. We then further generalize the result, proving that
antisymmetry is sufficient for \emph{strict} fixed points
$f(x) = x$ to be complete.\<close>

subsection \<open>Completeness of a Subset\<close>

text \<open>We start by formalizing what it means for a subset to have an extreme bound inside 
a set, and for this subset to be complete. We prove that this completeness is also auto-dual.\<close>

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

interpretation less_eq_dualize.

abbreviation "extreme_bound_in S X \<equiv> extreme (\<sqsupseteq>) {b \<in> S. bound (\<sqsubseteq>) X b}"

lemma extreme_bound_inI[intro]:
  assumes "\<And>b. bound (\<sqsubseteq>) X b \<Longrightarrow> b \<in> S \<Longrightarrow> s \<sqsubseteq> b" and "s \<in> S" and "\<And>x. x \<in> X \<Longrightarrow> x \<sqsubseteq> s"
  shows "extreme_bound_in S X s"
  using assms by auto

definition "complete_in S \<equiv> \<forall>X \<subseteq> S. Ex (extreme_bound_in S X)"

lemma complete_inE[elim]:
  assumes "complete_in S" and "(\<And>X. X \<subseteq> S \<Longrightarrow> Ex (extreme_bound_in S X)) \<Longrightarrow> thesis"
  shows "thesis"
  using assms by (auto simp: complete_in_def)

lemma complete_inD:
  shows "complete_in S \<Longrightarrow> X \<subseteq> S \<Longrightarrow> Ex (extreme_bound_in S X)"
  by (auto simp: complete_in_def)

lemma complete_inI[intro?]:
  assumes "\<And>X. X \<subseteq> S \<Longrightarrow> Ex (extreme_bound_in S X)"
  shows "complete_in S"
  using assms by (auto simp: complete_in_def)

end

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

interpretation less_eq_dualize.

lemma complete_in_dual:
  assumes complete: "complete_in (\<sqsubseteq>) S" shows "complete_in (\<sqsupseteq>) S"
proof
  fix A :: "'a set"
  assume AS: "A \<subseteq> S"
  define B where "B \<equiv> {b\<in>S. bound (\<sqsupseteq>) A b}"
  then have "B \<subseteq> S" by auto
  then obtain b where "extreme_bound_in (\<sqsubseteq>) S B b"
    using complete by force
  with AS show "Ex (extreme_bound_in (\<sqsupseteq>) S A)"
    apply (intro exI[of _ b], unfold extreme_def B_def) by auto
qed

end

subsection \<open>Existence of Quasi-Fixed Points\<close>
text \<open>\label{sec:qfp-exists}\<close>

text \<open>The following proof is simplified and generalized from
  Stouti--Maaden \cite{SM13}. We generalize so that the underlying 
relation is not even reflexive or antisymmetric.\<close>

locale fixed_point_proof = less_eq_dualize
begin

context
  fixes f :: "'a \<Rightarrow> 'a" and S :: "'a set"
  assumes mono: "monotone (\<sqsubseteq>) (\<sqsubseteq>) f"
  assumes f_closed_S: "f ` S \<subseteq> S"
  assumes S_comp: "complete_in (\<sqsubseteq>) S"
begin

definition AA where "AA \<equiv>
  {A. A \<subseteq> S \<and> f ` A \<subseteq> A \<and> (\<forall>B \<subseteq> A. \<forall>b. extreme_bound_in (\<sqsubseteq>) S B b \<longrightarrow> b \<in> A)}"
definition C where "C \<equiv> \<Inter> AA"

qualified lemma S_AA: "S \<in> AA" by (auto simp: AA_def f_closed_S)

qualified lemma C_AA: "C \<in> AA"
proof (unfold  AA_def, intro CollectI conjI allI impI)
  show "C \<subseteq> S" using C_def S_AA f_closed_S by auto
  show "f ` C \<subseteq> C" unfolding C_def AA_def by auto
  fix B b assume BC: "B \<subseteq> C" and EBS: "extreme_bound_in (\<sqsubseteq>) S B b"
  { fix X assume "X \<in> AA"
    with EBS have "b\<in>X" 
      apply (unfold AA_def,safe) by (metis BC C_def Inf_lower subset_trans)
  }
  then show "b \<in> C" by (auto simp: C_def AA_def)
qed

lemma quasi_fixed_point_in_C: "\<exists>c \<in> C. f c \<sim> c"
proof-
  obtain c where c: "extreme_bound_in (\<sqsubseteq>) S C c" 
    using S_comp unfolding complete_in_def C_def
    by (metis InterE S_AA subset_iff)
  then have cS: "c \<in> S" by auto
  show "\<exists>c \<in> C. f c \<sim> c"
  proof (intro conjI bexI)
    show cCS: "c \<in> C" using AA_def C_AA c by auto
    then have "f c \<in> C" using AA_def C_AA by auto
    then show "f c \<sqsubseteq> c" using f_closed_S cS c by auto
    show "c \<sqsubseteq> f c"
    proof-
      define D where "D \<equiv> {x \<in> C. x \<sqsubseteq> f c}"
      have "D \<in> AA"
      proof (unfold  AA_def, intro CollectI conjI allI impI)
        show "D \<subseteq> S"
          unfolding D_def C_def using S_AA f_closed_S by auto
        have fxC: "x \<in> C \<Longrightarrow> x \<sqsubseteq> f c \<Longrightarrow> f x \<in> C" for x using C_AA by (auto simp: AA_def)
        show "f ` D \<subseteq> D"
        proof (unfold D_def, safe intro!: fxC)
          fix x assume xC: "x \<in> C"
          have "x \<sqsubseteq> c" using c xC by auto
          then show "f x \<sqsubseteq> f c" using mono by (auto dest:monotoneD)
        qed
        have DC: "D \<subseteq> C" unfolding D_def by auto
        fix B b assume BD: "B \<subseteq> D" and BS: "extreme_bound_in (\<sqsubseteq>) S B b"
        have "B \<subseteq> C" using DC BD by auto
        then have bC: "b \<in> C" using C_AA BS by (auto simp: AA_def)
        have bfc: "\<forall>a\<in>B. a \<sqsubseteq> f c" using BD unfolding D_def by auto
        with f_closed_S cS BS
        have "b \<sqsubseteq> f c" by (auto simp: extreme_def image_subset_iff)
        with bC show "b \<in> D" unfolding D_def by auto
      qed
      then have "C \<subseteq> D" unfolding C_def by auto
      then show "c \<sqsubseteq> f c" using cCS unfolding D_def by auto
    qed
  qed
qed

lemma quasi_fixed_point: "\<exists>s \<in> S. f s \<sim> s" using quasi_fixed_point_in_C S_AA C_def by auto

lemma ex_extreme_quasi_fixed_point:
  assumes attract: "\<forall>q x. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
  shows "Ex (extreme (\<sqsupseteq>) {q \<in> S. f q \<sim> q})"
proof-
  define A where "A \<equiv> {a \<in> S. \<forall>s \<in> S. f s \<sim> s \<longrightarrow> a \<sqsubseteq> s}"
  have "A \<in> AA" 
  proof (unfold AA_def, intro CollectI conjI allI impI)
    show AS: "A \<subseteq> S" unfolding A_def by auto  
    { fix x assume xA: "x \<in> A"
      have "f x \<in> A"
      proof (unfold A_def, intro CollectI conjI)
        have "x \<in> S" using xA unfolding A_def by auto 
        then show "f x \<in> S" using f_closed_S by auto
        { fix s assume sS: "s \<in> S" and sf: "f s \<sim> s"
          then have "x \<sqsubseteq> s" using xA sS sf A_def by auto
          then have "f x \<sqsubseteq> s" using attract mono  
            unfolding A_def by (meson monotoneD sf)
        }
        then show "\<forall>s\<in>S. f s \<sim> s \<longrightarrow> f x \<sqsubseteq> s" by auto
      qed 
    }
    then show "f ` A \<subseteq> A" by auto
    fix B b assume BA: "B \<subseteq> A" and b: "extreme_bound_in (\<sqsubseteq>) S B b"
    then have "B \<subseteq> S" unfolding A_def using BA AS by auto
    with BA b have bS: "b \<in> S" by auto
    { fix s assume sS: "s \<in> S" and sf: "f s \<sim> s"
      have "bound (\<sqsubseteq>) B s"  using sS BA b A_def sf by auto
    }
    with b have "\<forall>s\<in>S. f s \<sim> s \<longrightarrow> b \<sqsubseteq> s" by auto
    then show "b \<in> A" using bS by (auto simp: A_def)
  qed
  then have "C \<subseteq> A" by (simp add: C_def Inf_lower)
  then have "\<exists>a \<in> A. f a \<sim> a" 
    using quasi_fixed_point_in_C by auto
  then obtain a where aA: "a \<in> A" and faa: "f a \<sim> a" by auto
  with aA A_def have "extreme (\<sqsupseteq>) {q \<in> S. f q \<sim> q} a" by (auto simp: extreme_def)
  then show ?thesis by auto
qed

end

end


context complete begin

lemma complete_in_UNIV[intro!]: "complete_in (\<sqsubseteq>) UNIV"
  unfolding complete_in_def using complete by auto

interpretation fixed_point_proof.

theorem monotone_imp_ex_quasi_fixed_point:
  assumes mono: "monotone (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "\<exists>s. f s \<sim> s"
proof-
  have Ucl: "f ` UNIV \<subseteq> UNIV" by auto
  obtain s where sC: "s \<in> C f UNIV" and fss: "f s \<sim> s" 
    using quasi_fixed_point_in_C[OF mono Ucl complete_in_UNIV] by auto
  show "\<exists>s. f s \<sim> s" using fss by auto
qed

end

context complete_antisymmetric begin

corollary monotone_imp_ex_fixed_point:
  assumes mono: "monotone (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "\<exists>s. f s = s"
  using monotone_imp_ex_quasi_fixed_point[OF mono] by auto

end

subsection \<open>Completeness of Quasi-Fixed Points\<close>
text \<open>\label{sec:qfp-complete}\<close>

text \<open>We now show that fixed points are complete in a complete trellis,
which strengthens the existing result by Stouti and Maaden who showed the existence of
the least fixed point. Below we derive an even more general result by dropping reflexivity.\<close>

text \<open>We first prove that, under attractivity, the set of quasi-fixed points is complete.\<close>

context fixed_point_proof begin

lemma attract_imp_qfp_complete:
  assumes comp: "complete (\<sqsubseteq>)"
  assumes mono: "monotone (\<sqsubseteq>) (\<sqsubseteq>) f"
  assumes attract: "\<forall>q x. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
  assumes dual_attract: "\<forall>q x. f q \<sim> q \<longrightarrow> f q \<sqsubseteq> x \<longrightarrow> q \<sqsubseteq> x"
  shows "complete_in (\<sqsubseteq>) {s. f s \<sim> s}"
proof (intro complete_inI)
  interpret complete using comp.
  fix A assume Afix: "A \<subseteq> {s. f s \<sim> s}"
  define S where "S \<equiv> {s. \<forall>a \<in> A. a \<sqsubseteq> s}"
  { fix s a assume as: "\<forall>a \<in> A. a \<sqsubseteq> s" and aA: "a \<in> A"
    have "a \<sqsubseteq> f s"
    proof (rule dual_attract[rule_format])
      have "a \<sqsubseteq> s" using as aA by auto
      then show "f a \<sqsubseteq> f s" using mono by (simp add: monotone_def)
      show "f a \<sim> a" using Afix aA by auto
    qed
  }
  then have f_closed_S: "f ` S \<subseteq> S" unfolding S_def by auto
  have comp_S_dual: "complete_in (\<sqsupseteq>) S"
  proof (unfold complete_in_def, intro allI impI)
    fix B assume BS: "B \<subseteq> S"
    then obtain b where bB: "extreme_bound (\<sqsupseteq>) B b" using dual.complete by auto
    show "Ex (extreme_bound_in (\<sqsupseteq>) S B)"
    proof (intro exI extreme_bound_inI)
      { fix a assume aA: "a \<in> A"
        then have "\<forall>c \<in> B. a \<sqsubseteq> c" using BS aA S_def by auto
        then have "a \<sqsubseteq> b" using bB by blast
      }
      then show "b \<in> S" unfolding S_def by auto
      show "x \<in> B \<Longrightarrow> b \<sqsubseteq> x" for x using bB by auto
      fix c assume "bound (\<sqsupseteq>) B c"
      then show "c \<sqsubseteq> b" using bB by blast
    qed
  qed
  then have comp_S: "complete_in (\<sqsubseteq>) S" using complete_in_dual by auto
  then obtain L where LefpS: "extreme (\<sqsupseteq>) {q \<in> S. f q \<sim> q} L"
    using ex_extreme_quasi_fixed_point[OF mono f_closed_S comp_S attract]
    by auto
  show "Ex (extreme_bound_in (\<sqsubseteq>) {s. f s \<sim> s} A)"
  proof (intro exI extreme_bound_inI)
    show "L \<in> {s. f s \<sim> s}" using LefpS by auto
    fix a assume "a \<in> A"
    with LefpS show "a \<sqsubseteq> L" by (auto simp: S_def)
  next
    fix c assume c: "bound (\<sqsubseteq>) A c" and cfix: "c \<in> {s. f s \<sim> s}"
    from c have "c \<in> S" by (auto simp: S_def)
    with cfix show "L \<sqsubseteq> c" using LefpS c by auto
  qed
qed

end

context complete_attractive begin

interpretation fixed_point_proof.

theorem monotone_imp_quasi_fixed_points_complete:
  assumes mono: "monotone (\<sqsubseteq>) (\<sqsubseteq>) f"
  shows "complete_in (\<sqsubseteq>) {s. f s \<sim> s}"
  by (rule attract_imp_qfp_complete[OF complete_axioms mono], auto dest: attract dual.attract)

end


text \<open>The next lemma shows that in a complete relation, two related sets of
strict fixed points have a quasi-fixed point in between.\<close>

context fixed_point_proof begin

lemma qfp_interpolant:
  assumes comp: "complete (\<sqsubseteq>)" and mono: "monotone (\<sqsubseteq>) (\<sqsubseteq>) f"
    and AB: "\<forall>a \<in> A. \<forall>b \<in> B. a \<sqsubseteq> b"
    and Afp: "\<forall>a \<in> A. f a = a"
    and Bfp: "\<forall>b \<in> B. f b = b"
  shows "\<exists>t. (f t \<sim> t) \<and> (\<forall>a \<in> A. a \<sqsubseteq> t) \<and> (\<forall>b \<in> B. t \<sqsubseteq> b)"
proof-
  interpret complete using comp. 
  define T where "T \<equiv> {t. (\<forall>a \<in> A. a \<sqsubseteq> t) \<and> (\<forall>b \<in> B. t \<sqsubseteq> b)}"
  have f_closed_T: "f ` T \<subseteq> T"
  proof safe
    fix t assume tT: "t \<in> T"
    show "f t \<in> T"
    proof (unfold T_def, safe)
      fix a assume aA: "a \<in> A"
      with tT monotoneD[OF mono]
      have "f a \<sqsubseteq> f t" by (auto simp: T_def)
      with Afp aA show "a \<sqsubseteq> f t" by auto
    next
      fix b assume bB: "b \<in> B"
      with tT monotoneD[OF mono]
      have "f t \<sqsubseteq> f b" by (auto simp: T_def)
      with Bfp bB show "f t \<sqsubseteq> b" by auto
    qed
  qed
  have T_comp: "complete_in (\<sqsubseteq>) T"
  proof
    fix U assume UT: "U \<subseteq> T"
    obtain k where k: "extreme_bound (\<sqsubseteq>) (U \<union> A) k" using complete by auto
    have "extreme_bound_in (\<sqsubseteq>) T U k"
    proof (intro extreme_bound_inI)
      { fix b assume "b \<in> B"
        with AB T_def UT have "\<forall>x \<in> U \<union> A. x \<sqsubseteq> b" by auto
        with k have "k \<sqsubseteq> b" by auto
      }
      with k T_def show "k \<in> T" by auto
    next
      fix x assume "x \<in> U"
      with k show "x \<sqsubseteq> k" by auto
    next
      fix l
      assume "bound (\<sqsubseteq>) U l" and "l \<in> T"
      then have "\<forall>a \<in> U \<union> A. a \<sqsubseteq> l" by (auto simp: T_def)
      with k show "k \<sqsubseteq> l" by auto
    qed
    then show "Ex (extreme_bound_in (\<sqsubseteq>) T U)" by auto
  qed
  obtain t where "t \<in> T" and "f t \<sim> t"
    using quasi_fixed_point 
    by (meson T_comp f_closed_T mono)
  then show ?thesis by (auto simp: T_def)
qed

end

text \<open>From this, we deduce that the set of strict fixed-points is also complete, assuming
only antisymmetry and attractivity.\<close>

context complete_antisymmetric begin

interpretation fixed_point_proof.

context
  fixes f assumes mono: "monotone (\<sqsubseteq>) (\<sqsubseteq>) f"
begin

theorem monotone_imp_fixed_points_complete:
  shows "complete_in (\<sqsubseteq>) {s. f s = s}"
proof
  fix A assume "A \<subseteq> {s. f s = s}"
  then have Afp: "\<forall>a\<in>A. f a = a" by auto
  define S where "S \<equiv> {s. \<forall>a \<in> A. a \<sqsubseteq> s}"
  have f_closed_S: "f ` S \<subseteq> S"
  proof safe
    fix s assume sS: "s \<in> S"
    show "f s \<in> S"
    proof(unfold S_def, safe)
      fix a assume aA: "a \<in> A"
      then have "f a \<sqsubseteq> f s" using S_def sS mono by (auto dest:monotoneD)
      then show "a \<sqsubseteq> f s" using Afp aA by auto
    qed
  qed
  have "complete_in (\<sqsupseteq>) S"
  proof
    fix B assume BS: "B \<subseteq> S"
    obtain L where BL: "extreme_bound (\<sqsupseteq>) B L" using  dual.complete by blast
    have "extreme_bound_in (\<sqsupseteq>) S B L"
    proof (intro extreme_bound_inI)
      { fix a assume aA: "a \<in> A"
        then have "\<forall>s \<in> B. a \<sqsubseteq> s" using BS S_def by auto
      }
      then have "\<forall>a \<in> A. a \<sqsubseteq> L" using BL by (simp add: extreme_bound_iff)
      then show "L \<in> S" using S_def by auto
      show "b \<in> B \<Longrightarrow> L \<sqsubseteq> b" for b using BL by auto
      show "\<And>c. bound (\<sqsupseteq>) B c \<Longrightarrow> c \<sqsubseteq> L" using BL by (auto elim!: boundE)
    qed
    then show "Ex (extreme_bound_in (\<sqsupseteq>) S B)" by auto
  qed
  then have comp_S: "complete_in (\<sqsubseteq>) S" using complete_in_dual by auto
  have "Ex (extreme (\<sqsupseteq>) {q \<in> S. f q \<sim> q})"
    apply (rule ex_extreme_quasi_fixed_point[OF mono f_closed_S comp_S])
    by auto
  then obtain q where q: "extreme (\<sqsupseteq>) {q \<in> S. f q \<sqsubseteq> q \<and> q \<sqsubseteq> f q} q" by auto
  have "extreme_bound_in (\<sqsubseteq>) {s. f s = s} A q"
  proof (intro extreme_bound_inI)
    show qfp: "q \<in> {s. f s = s}" using q by auto
    show Aq: "\<And>a. a \<in> A \<Longrightarrow> a \<sqsubseteq> q" using q S_def by auto
    fix c assume "bound (\<sqsubseteq>) A c" and "c \<in> {s. f s = s}"
    then have cfp: "f c = c" and Ac: "\<forall>a \<in> A. a \<sqsubseteq> c" by auto
    define D where [simp]: "D \<equiv> {c,q}"
    have AD: "\<forall>a \<in> A. \<forall>d \<in> D. a \<sqsubseteq> d" using Aq Ac by auto
    then have Dfp: "\<forall>d\<in>D. f d = d" using qfp cfp by auto 
    then obtain t where t: "(f t \<sim> t) \<and> (\<forall>a \<in> A. a \<sqsubseteq> t) \<and> (\<forall>d \<in> D. t \<sqsubseteq> d)"
      using qfp_interpolant[OF complete_axioms mono AD Afp Dfp]
      by auto
    then have tq: "t \<sqsubseteq> q" by auto
    have "q \<sqsubseteq> t" using t q by (auto simp: S_def)
    with tq have "q = t" by auto
    also have "t \<sqsubseteq> c" using t by auto
    finally show "q \<sqsubseteq> c".
  qed
  then show "Ex (extreme_bound_in (\<sqsubseteq>) {s. f s = s} A)" by auto
qed

corollary monotone_imp_ex_extreme_fixed_point:
  shows "Ex (extreme (\<sqsupseteq>) {s. f s = s})"
  using complete_inD[OF monotone_imp_fixed_points_complete, of "{}"]
  by auto

end

end

section \<open>Kleene-Style Fixed Point Theorem\<close>

text \<open>Kleene's fixed-point theorem states that,
for a pointed directed complete partial order $\tp{A,\SLE}$
and a Scott-continous map $f: A \to A$,
the supremum of $\set{f^n(\bot) \mid n\in\Nat}$ exists in $A$ and is a least 
fixed point.
Mashburn \cite{mashburn83} generalized the result so that
$\tp{A,\SLE}$ is a $\omega$-complete partial order
and $f$ is $\omega$-continuous.

In this section we further generalize the result and show that
for $\omega$-complete relation $\tp{A,\SLE}$
and for every bottom element $\bot \in A$,
the set $\set{f^n(\bot) \mid n\in\Nat}$ has suprema (not necessarily unique, of 
course) and, 
they are quasi-fixed points.
Moreover, if $(\SLE)$ is attractive, then the suprema are precisely the least 
quasi-fixed points.\<close>

subsection \<open>Scott Continuity, $\omega$-Completeness, $\omega$-Continuity\<close>

text \<open>In this Section, we formalize $\omega$-completeness, Scott continuity and $\omega$-continuity.
We then prove that a Scott continuous map is $\omega$-continuous and that an $\omega$-continuous 
map is ``nearly'' monotone.\<close>

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

definition "omega_continuous f \<equiv> \<forall>c :: nat \<Rightarrow> 'a. \<forall> b.
  monotone (\<le>) (\<sqsubseteq>) c \<longrightarrow>
  extreme_bound (\<sqsubseteq>) (range c) b \<longrightarrow> extreme_bound (\<sqsubseteq>) (f ` range c) (f b)"

lemma omega_continuousI[intro?]:
  assumes "\<And>c :: nat \<Rightarrow> 'a. \<And> b.
   monotone (\<le>) (\<sqsubseteq>) c \<Longrightarrow>
   extreme_bound (\<sqsubseteq>) (range c) b \<Longrightarrow> extreme_bound (\<sqsubseteq>) (f ` range c) (f b)"
  shows "omega_continuous f"
  using assms by (auto simp: omega_continuous_def)

lemma omega_continuousE[elim]:
  assumes "omega_continuous f"
    and "(\<And>c :: nat \<Rightarrow> 'a. \<And> b. monotone (\<le>) (\<sqsubseteq>) c \<Longrightarrow>
         extreme_bound (\<sqsubseteq>) (range c) b \<Longrightarrow> extreme_bound (\<sqsubseteq>) (f ` range c) (f b)
         ) \<Longrightarrow> thesis"
  shows "thesis"
  using assms by (auto simp: omega_continuous_def)

lemma omega_continuous_imp_mono_refl:
  assumes cont: "omega_continuous f"
    and xy: "x \<sqsubseteq> y" and xx: "x \<sqsubseteq> x" and yy: "y \<sqsubseteq> y"
  shows "f x \<sqsubseteq> f y"
proof-
  define c :: "nat \<Rightarrow> 'a" where "c \<equiv> \<lambda>i. if i = 0 then x else y"
  from xx xy yy have monoc: "monotone (\<le>) (\<sqsubseteq>) c"
    by (auto simp: c_def intro!: monotoneI)
  have "extreme_bound (\<sqsubseteq>) (range c) y" using xy yy by (auto simp: c_def)
  then have fboy: "extreme_bound (\<sqsubseteq>) (f ` range c) (f y)" using monoc cont by auto
  then show "f x \<sqsubseteq> f y" by (auto simp: c_def)
qed

definition "scott_continuous f \<equiv>
  \<forall>D b. directed (\<sqsubseteq>) D \<longrightarrow> extreme_bound (\<sqsubseteq>) D b \<longrightarrow> extreme_bound (\<sqsubseteq>) (f ` D) (f b)"

lemma scott_continuousI[intro?]:
  assumes "\<And>D b. directed (\<sqsubseteq>) D \<Longrightarrow> extreme_bound (\<sqsubseteq>) D b \<Longrightarrow> extreme_bound (\<sqsubseteq>) (f ` D) (f b)"
  shows "scott_continuous f"
  using assms by (auto simp: scott_continuous_def)

lemma scott_continuousE[elim]:
  assumes "scott_continuous f"
    and "(\<And>D b. directed (\<sqsubseteq>) D \<Longrightarrow>
         extreme_bound (\<sqsubseteq>) D b \<Longrightarrow> extreme_bound (\<sqsubseteq>) (f ` D) (f b)) \<Longrightarrow> thesis"
  shows "thesis"
  using assms by (auto simp: scott_continuous_def)

lemma scott_continous_imp_mono_refl:
  assumes scott: "scott_continuous f"
    and xy: "x \<sqsubseteq> y" and yy: "y \<sqsubseteq> y"
  shows "f x \<sqsubseteq> f y"
proof-
  define D where "D \<equiv> {x,y}"
  from xy yy have dir_D
: "directed (\<sqsubseteq>) D" by (auto simp: D_def intro!: bexI[of _ y])
  have "extreme_bound (\<sqsubseteq>) D y" using xy yy by (auto simp: D_def)
  then have fboy: "extreme_bound (\<sqsubseteq>) (f ` D) (f y)" using dir_D scott by auto
  then show "f x \<sqsubseteq> f y" by (auto simp: D_def)
qed

lemma scott_continous_imp_omega_continous:
  assumes scott: "scott_continuous f" shows "omega_continuous f"
proof
  fix c :: "nat \<Rightarrow> 'a"
  assume "monotone (\<le>) (\<sqsubseteq>) c"
  from monotone_directed_image[OF this order.dual.dual.directed_UNIV] scott
  show "extreme_bound (\<sqsubseteq>) (range c) b \<Longrightarrow> extreme_bound (\<sqsubseteq>) (f ` range c) (f b)" for b
    by auto
qed

end

subsection \<open>Kleene's Fixed-Point Theorem\<close>

text \<open>The first part of Kleene's theorem demands to prove that the set 
$\set{f^n(\bot) \mid n \in \Nat}$ has a supremum and 
that all such are quasi-fixed points. We prove this claim without assuming 
anything on the relation $\SLE$ besides $\omega$-completeness and one bottom element.\<close>

context fixed_point_proof begin

context
  fixes f
  assumes comp: "omega_complete (\<sqsubseteq>)"
  assumes cont: "omega_continuous (\<sqsubseteq>) f"
  fixes bot ("\<^bold>\<bottom>")
  assumes bot: "\<forall>q. \<^bold>\<bottom> \<sqsubseteq> q"
begin

interpretation omega_complete "(\<sqsubseteq>)" using comp.

abbreviation(input) fn where "fn n \<equiv> (f ^^ n) \<^bold>\<bottom>"

abbreviation(input) "Fn \<equiv> range fn"

lemma fn_ref: "fn n \<sqsubseteq> fn n"
  using omega_continuous_imp_mono_refl[OF cont] bot by (induct n, auto)

lemma fn_monotone: "monotone (\<le>) (\<sqsubseteq>) fn"
proof
  fix n m :: nat
  assume "n \<le> m"
  from le_Suc_ex[OF this] obtain k where m: "m = n + k" by auto
  from bot fn_ref omega_continuous_imp_mono_refl[OF cont]
  show "fn n \<sqsubseteq> fn m" by (unfold m, induct n, auto)
qed

lemma ex_kleene_fixed_point:
  shows "Ex (extreme_bound (\<sqsubseteq>) Fn)" 
  using monotone_seq_complete[OF fn_monotone] by auto

lemma kleene_fixed_point_is_fixed:
  assumes q: "extreme_bound (\<sqsubseteq>) Fn q"
  shows "f q \<sim> q"
proof
  have fq: "extreme_bound (\<sqsubseteq>) (f ` Fn) (f q)"
    using q cont fn_monotone by auto
  with bot have nq: "fn n \<sqsubseteq> f q" for n
    by(induct n, auto simp: extreme_bound_iff)
  then show "q \<sqsubseteq> f q" using q by blast
  have "f (fn n) \<in> range fn" for n by (auto intro!: range_eqI[of _ _ "Suc n"])
  then have "f ` Fn \<subseteq> Fn" by auto
  then show "f q \<sqsubseteq> q" using q fq
    by (metis (no_types, lifting) bound_cmono extreme_def mem_Collect_eq)
qed

lemma kleene_fixed_point_is_dual_extreme:
  assumes attract: "\<forall>q x. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
  assumes q: "extreme_bound (\<sqsubseteq>) Fn q"
  shows "extreme (\<sqsupseteq>) {s. f s \<sim> s} q"
proof(intro extremeI, unfold mem_Collect_eq, intro kleene_fixed_point_is_fixed[OF q])
  fix c assume cqfp: "f c \<sim> c"
  {
    fix n::nat
    have "fn n \<sqsubseteq> c"
    proof(induct n)
      case 0
      show ?case using bot by auto
    next
      case IH: (Suc n)
      have "c \<sqsubseteq> c" using attract cqfp by blast
      with IH have "fn (Suc n) \<sqsubseteq> f c"
        using omega_continuous_imp_mono_refl[OF cont] fn_ref by auto
      then show ?case using attract cqfp by blast 
    qed
  }
  then show "q \<sqsubseteq> c" using q by blast
qed

lemma kleene_fixed_point_iff_dual_extreme:
  assumes attract: "\<forall>q x. f q \<sim> q \<longrightarrow> x \<sqsubseteq> f q \<longrightarrow> x \<sqsubseteq> q"
  assumes dual_attract: "\<forall>p q x. p \<sim> q \<longrightarrow> q \<sqsubseteq> x \<longrightarrow> p \<sqsubseteq> x"
  shows "extreme_bound (\<sqsubseteq>) Fn = extreme (\<sqsupseteq>) {s. f s \<sim> s}"
proof (intro ext iffI kleene_fixed_point_is_dual_extreme[OF attract])
  fix q
  assume q: "extreme (\<sqsupseteq>) {s. f s \<sim> s} q"
  from q have fqq: "f q \<sim> q" by auto
  from ex_kleene_fixed_point obtain k where k: "extreme_bound (\<sqsubseteq>) Fn k" by auto
  have qk: "q \<sim> k"
  proof
    from kleene_fixed_point_is_fixed[OF k] q
    show "q \<sqsubseteq> k" by auto
    from kleene_fixed_point_is_dual_extreme[OF _ k] q attract
    show "k \<sqsubseteq> q" by blast
  qed
  show "extreme_bound (\<sqsubseteq>) Fn q"
  proof (intro extreme_boundI,safe)
    fix n
    show "(f ^^ n) \<^bold>\<bottom> \<sqsubseteq> q"
      apply (induct n, auto intro: bot[rule_format])
      by (meson attract fn_ref fqq omega_continuous_imp_mono_refl[OF cont])
  next
    fix x
    assume "bound (\<sqsubseteq>) Fn x"
    with k have kx: "k \<sqsubseteq> x" by auto
    with dual_attract[rule_format, OF qk]
    show "q \<sqsubseteq> x" by auto
  qed
qed

end

end

context omega_complete begin

interpretation fixed_point_proof.

theorem kleene_quasi_fixed_point:
  assumes "omega_continuous (\<sqsubseteq>) f" and "\<forall>x. bo \<sqsubseteq> x"
  shows "\<exists>p. extreme_bound (\<sqsubseteq>) {(f ^^ n) bo |. n :: nat} p"
    and "extreme_bound (\<sqsubseteq>) {(f ^^ n) bo |. n :: nat} p \<Longrightarrow> f p \<sim> p"
  using ex_kleene_fixed_point[OF omega_complete_axioms assms]
  using kleene_fixed_point_is_fixed[OF omega_complete_axioms assms].

end

text \<open>Kleene's theorem also states that the quasi-fixed point found this way is a least one.
Again, attractivity is needed to prove this statement.\<close>

context attractive begin

interpretation fixed_point_proof.

corollary kleene_quasi_fixed_point_dual_extreme:
  assumes "omega_complete (\<sqsubseteq>)" and "omega_continuous (\<sqsubseteq>) f" and "\<forall>x. bo \<sqsubseteq> x"
  shows "extreme_bound (\<sqsubseteq>) {(f ^^ n) bo |. n :: nat} = extreme (\<sqsupseteq>) {s. f s \<sim> s}"
  apply (rule kleene_fixed_point_iff_dual_extreme[OF assms])
  by (auto dest: attract dual.attract)

end

context antisymmetric begin

interpretation fixed_point_proof.

corollary kleene_fixed_point_is_fixed:
  assumes "omega_complete (\<sqsubseteq>)" and "omega_continuous (\<sqsubseteq>) f" and "\<forall>x. bo \<sqsubseteq> x"
    and "extreme_bound (\<sqsubseteq>) {(f ^^ n) bo |. n :: nat} p"
  shows "f p = p"
  using kleene_fixed_point_is_fixed[OF assms] by auto

end

end