(*
Author:  Akihisa Yamada (2018-2019)
License: LGPL (see file COPYING.LESSER)
*)
section \<open> Completeness of Relations \<close>

text \<open>Here we formalize various order-theoretic completeness conditions.\<close>

theory Complete_Relations
  imports HOL.Real Binary_Relations
begin

subsection \<open>Completeness Conditions\<close>

text \<open>Order-theoretic completeness demands certain subsets of elements to admit suprema or infima.

A related set $\tp{A,\SLE}$ is called \emph{bounded} if there is a ``top'' element $\top \in A$,
a greatest element in $A$.
Note that there might be multiple tops if $(\SLE)$ is not antisymmetric.\<close>

locale bounded = less_eq_syntax + assumes bounded: "\<exists>t. \<forall>x. x \<sqsubseteq> t"
begin

lemma ex_bound[intro!]: "Ex (bound (\<sqsubseteq>) X)" using bounded by auto

lemma ex_extreme_UNIV[intro!]: "Ex (extreme (\<sqsubseteq>) UNIV)" using bounded by auto

lemma UNIV_complete[intro!]: "Ex (extreme_bound (\<sqsubseteq>) UNIV)" using bounded by blast

lemma dual_empty_complete[intro!]: "Ex (extreme_bound (\<sqsubseteq>)\<^sup>- {})" by (auto simp: bound_empty)

end

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

lemma bounded_iff_extreme_UNIV: "bounded (\<sqsubseteq>) \<longleftrightarrow> Ex (extreme (\<sqsubseteq>) UNIV)"
  by (auto simp:bounded_def)

text\<open>Boundedness can be also seen as a completeness condition,
since it is equivalent to saying that the universe has a supremum.\<close>

lemma bounded_iff_UNIV_complete: "bounded (\<sqsubseteq>) \<longleftrightarrow> Ex (extreme_bound (\<sqsubseteq>) UNIV)"
  by (unfold bounded_def, blast)

text \<open>The dual notion of bounded is called ``pointed'', equivalently ensuring a supremum
of the empty set.\<close>

lemma pointed_iff_empty_complete: "bounded (\<sqsubseteq>) \<longleftrightarrow> Ex (extreme_bound (\<sqsubseteq>)\<^sup>- {})"
  by (auto simp:bounded_def)

end


text \<open>One of the most well-studied notion of completeness would be the semilattice condition:
every pair of elements $x$ and $y$ has a supremum $x \sqcup y$
(not necessarily unique if the underlying relation is not antisymmetric).\<close>

locale pair_complete = less_eq_syntax +
  assumes pair_complete: "Ex (extreme_bound (\<sqsubseteq>) {x,y})"
begin

lemma directed_UNIV[intro!]: "directed (\<sqsubseteq>) UNIV"
proof
  fix x y :: 'a
  from pair_complete[of x y] show "\<exists>z \<in> UNIV. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" by auto
qed

end

sublocale total_reflexive \<subseteq> pair_complete
proof (unfold_locales)
  fix x y
  show "Ex (extreme_bound (\<sqsubseteq>) {x, y})" by (cases x y rule:comparable_cases, auto)
qed

text \<open>The next one assumes that every nonempty finite set has a supremum.\<close>

locale finite_complete = less_eq_syntax +
  assumes finite_nonempty_complete: "finite X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Ex (extreme_bound (\<sqsubseteq>) X)"

sublocale finite_complete \<subseteq> pair_complete
  by (unfold_locales, intro finite_nonempty_complete, auto)

text \<open>The next one assumes that every nonempty bounded set has a supremum.
It is also called the Dedekind completeness.\<close>

locale conditionally_complete = less_eq_syntax +
  assumes bounded_nonempty_complete:
  "Ex (bound (\<sqsubseteq>) X) \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Ex (extreme_bound (\<sqsubseteq>) X)"
begin

lemma bounded_nonemptyE[elim!]:
  assumes "Ex (bound (\<sqsubseteq>) X)" and "X \<noteq> {}"
    and "Ex (extreme_bound (\<sqsubseteq>) X) \<Longrightarrow> X \<noteq> {} \<Longrightarrow> thesis"
  shows thesis
  using assms bounded_nonempty_complete by auto

lemma nonempty_imp_complete_iff_bounded:
  assumes "X \<noteq> {}" shows "Ex (extreme_bound (\<sqsubseteq>) X) \<longleftrightarrow> Ex (bound (\<sqsubseteq>) X)"
  using assms by (auto intro: bounded_nonempty_complete)

end

text \<open>The $\omega$-completeness condition demands a supremum for an $\omega$-chain,
  $a_1 \sqsubseteq a_2 \sqsubseteq \dots$.
  We model $\omega$-chain as the range of a monotone map $f : i \mapsto a_i$.\<close>

locale omega_complete = less_eq_syntax +
  assumes monotone_seq_complete:
    "\<And>f :: nat \<Rightarrow> 'a. monotone (\<le>) (\<sqsubseteq>) f \<Longrightarrow> Ex (extreme_bound (\<sqsubseteq>) (range f))"

locale chain_complete = less_eq_syntax +
  assumes chain_nonempty_complete: "chain (\<sqsubseteq>) X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Ex (extreme_bound (\<sqsubseteq>) X)"
begin

lemma monotone_chain_complete:
  assumes C0: "C \<noteq> {}" and chain: "chain r C" and mono: "monotone r (\<sqsubseteq>) f"
  shows "Ex (extreme_bound (\<sqsubseteq>) (f ` C))"
  apply (rule chain_nonempty_complete[OF monotone_chain_image[OF mono chain]])
  using C0 by auto

end

sublocale chain_complete \<subseteq> omega_complete
  by (unfold_locales, rule monotone_chain_complete, auto intro:chainI)

text\<open>\emph{Directed completeness} is an important notion in domain theory~\cite{abramski94},
asserting that every nonempty directed set has a supremum.
Here, a set $X$ is \emph{directed} if any pair of two elements in $X$ has a bound in $X$.\<close>

locale directed_complete = less_eq_syntax +
  assumes directed_nonempty_complete: "directed (\<sqsubseteq>) X \<Longrightarrow> X \<noteq> {} \<Longrightarrow> Ex (extreme_bound (\<sqsubseteq>) X)"
begin

lemma monotone_directed_complete:
  assumes dir: "directed r C" and c0: "C \<noteq> {}" and mono: "monotone r (\<sqsubseteq>) f"
  shows "Ex (extreme_bound (\<sqsubseteq>) (f ` C))"
  apply (rule directed_nonempty_complete[OF monotone_directed_image[OF mono dir]])
  using c0 by auto

end

sublocale directed_complete \<subseteq> chain_complete
  by (unfold_locales, intro directed_nonempty_complete, auto dest: chain_imp_directed)

text \<open>The next one is quite complete, only the empty set may fail to have a supremum.
The terminology follows \cite{Bergman2015},
although there it is defined more generally depending on a cardinal $\alpha$
such that a nonempty set $X$ of cardinality below $\alpha$ has a supremum.\<close>

locale semicomplete = less_eq_syntax +
  assumes nonempty_complete: "X \<noteq> {} \<Longrightarrow> Ex (extreme_bound (\<sqsubseteq>) X)"

sublocale semicomplete \<subseteq> conditionally_complete + finite_complete + directed_complete
  by (unfold_locales, auto intro!: nonempty_complete)

sublocale semicomplete \<subseteq> bounded
  unfolding bounded_iff_UNIV_complete using nonempty_complete[of UNIV] by auto

subsection \<open>Pointed Ones\<close>

text \<open>The term `pointed' refers to the dual notion of boundedness, i.e., there is a global least element.
  This serves as the supremum of the empty set.\<close>

locale pointed_chain_complete = chain_complete + dual: bounded "(\<sqsubseteq>)\<^sup>-"
begin

lemma chain_complete: "chain (\<sqsubseteq>) X \<Longrightarrow> Ex (extreme_bound (\<sqsubseteq>) X)"
  by (cases "X = {}", auto intro:chain_nonempty_complete)

end

lemma pointed_chain_complete_def':
  fixes less_eq (infix "\<sqsubseteq>" 50)
  shows "pointed_chain_complete (\<sqsubseteq>) \<equiv> \<forall>X. chain (\<sqsubseteq>) X \<longrightarrow> Ex (extreme_bound (\<sqsubseteq>) X)" (is "?l \<equiv> ?r")
  apply (unfold atomize_eq, intro iffI)
  apply (force intro: pointed_chain_complete.chain_complete)
  by (unfold_locales, auto intro!: chain_empty simp: pointed_iff_empty_complete[unfolded bounded_def])

locale pointed_directed_complete = directed_complete + dual: bounded "(\<sqsubseteq>)\<^sup>-"
begin

lemma directed_complete: "directed (\<sqsubseteq>) X \<Longrightarrow> Ex (extreme_bound (\<sqsubseteq>) X)"
  by (cases "X = {}", auto intro: directed_nonempty_complete)

sublocale pointed_chain_complete ..

end

lemma pointed_directed_complete_def':
  fixes less_eq (infix "\<sqsubseteq>" 50)
  shows "pointed_directed_complete (\<sqsubseteq>) \<equiv> \<forall>X. directed (\<sqsubseteq>) X \<longrightarrow> Ex (extreme_bound (\<sqsubseteq>) X)"
  apply (unfold atomize_eq, intro iffI)
  apply (force intro: pointed_directed_complete.directed_complete)
  by (unfold_locales, auto simp: pointed_iff_empty_complete[unfolded bounded_def])

text \<open>``Bounded complete'' refers to pointed conditional complete,
but this notion is just the dual of semicompleteness. We prove this later.

Following is the strongest completeness that requires any subset of elements to have suprema
and infima.\<close>

locale complete = less_eq_syntax + assumes complete: "Ex (extreme_bound (\<sqsubseteq>) X)"
begin

sublocale semicomplete + pointed_directed_complete
  by (auto simp: pointed_directed_complete_def' intro: semicomplete.intro complete)

end

subsection \<open>Relations between Completeness Conditions\<close>

context
  fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

interpretation less_eq_dualize.

text \<open>Pair-completeness implies that the universe is directed. Thus, with directed completeness
implies boundedness.\<close>

proposition directed_complete_pair_complete_imp_bounded:
  assumes "directed_complete (\<sqsubseteq>)" and "pair_complete (\<sqsubseteq>)"
  shows "bounded (\<sqsubseteq>)"
proof-
  from assms interpret directed_complete + pair_complete by auto
  have "Ex (extreme_bound (\<sqsubseteq>) UNIV)" by (rule directed_nonempty_complete, auto)
  then obtain t where "extreme_bound (\<sqsubseteq>) UNIV t" by auto
  then have "\<forall>x. x \<sqsubseteq> t" by auto
  then show ?thesis by (unfold_locales, auto)
qed

text \<open>Semicomplete is conditional complete and bounded.\<close>

proposition semicomplete_iff_conditionally_complete_bounded:
  "semicomplete (\<sqsubseteq>) \<longleftrightarrow> conditionally_complete (\<sqsubseteq>) \<and> bounded (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof
  assume ?r
  then interpret conditionally_complete "(\<sqsubseteq>)" + bounded "(\<sqsubseteq>)" by auto
  show ?l by (unfold_locales, rule bounded_nonempty_complete, auto)
next
  assume ?l
  then interpret semicomplete.
  show ?r by (intro conjI, unfold_locales)
qed

proposition complete_iff_pointed_semicomplete:
  "complete (\<sqsubseteq>) \<longleftrightarrow> semicomplete (\<sqsubseteq>) \<and> bounded (\<sqsupseteq>)" (is "?l \<longleftrightarrow> ?r")
proof
  assume "complete (\<sqsubseteq>)"
  then interpret complete.
  show ?r by (intro conjI, unfold_locales)
next
  assume ?r
  then interpret semicomplete + bounded "(\<sqsupseteq>)" by auto
  show ?l
  proof
    fix X show "Ex (extreme_bound (\<sqsubseteq>) X)" by (cases "X = {}", auto intro:nonempty_complete)
  qed
qed

text \<open>Conditional completeness only lacks top and bottom to be complete.\<close>

proposition complete_iff_conditionally_complete_bounded_pointed:
  "complete (\<sqsubseteq>) \<longleftrightarrow> conditionally_complete (\<sqsubseteq>) \<and> bounded (\<sqsubseteq>) \<and> bounded (\<sqsupseteq>)"
  unfolding complete_iff_pointed_semicomplete
    semicomplete_iff_conditionally_complete_bounded by auto

end


text \<open>If the universe is directed, then every pair is bounded, and thus has a supremum.
  On the other hand, supremum gives an upper bound, witnessing directedness.\<close>

proposition (in conditionally_complete) pair_complete_iff_directed:
  "pair_complete (\<sqsubseteq>) \<longleftrightarrow> directed (\<sqsubseteq>) UNIV"
proof(intro iffI)
  assume "directed (\<sqsubseteq>) UNIV"
  then show "pair_complete (\<sqsubseteq>)"
    by (unfold_locales, intro bounded_nonempty_complete, auto elim: directedE)
next
  assume "pair_complete (\<sqsubseteq>)"
  then interpret pair_complete.
  show "directed (\<sqsubseteq>) UNIV"
  proof (intro directedI)
    fix x y
    from pair_complete obtain z where "extreme_bound (\<sqsubseteq>) {x,y} z" by auto
    then show "\<exists>z\<in>UNIV. x \<sqsubseteq> z \<and> y \<sqsubseteq> z" by auto
  qed
qed


subsection \<open>Completeness Results Requiring Order-Like Properties\<close>

text \<open>Above results hold without any assumption on the relation.
This part demands some order-like properties.\<close>

text \<open>It is well known that in a semilattice, i.e., a pair-complete partial order,
every finite nonempty subset of elements has a supremum.
We prove the result assuming transitivity, but only that.\<close>

locale trans_semilattice = transitive + pair_complete

sublocale trans_semilattice \<subseteq> finite_complete
  apply (unfold_locales)
  subgoal for X
  proof (induct X rule:finite_induct)
    case empty
    then show ?case by auto
  next
    case (insert x X)
    show ?case
    proof (cases "X = {}")
      case True
      obtain x' where "extreme_bound (\<sqsubseteq>) {x,x} x'" using pair_complete[of x x] by auto
      with True show ?thesis by (auto intro!: exI[of _ x'])
    next
      case False
      with insert obtain b where b: "extreme_bound (\<sqsubseteq>) X b" by auto
      from pair_complete obtain c where c: "extreme_bound (\<sqsubseteq>) {x,b} c" by auto
      show ?thesis
      proof (intro exI extreme_boundI)
        from c have "x \<sqsubseteq> c" and "b \<sqsubseteq> c" by auto
        with b show "xb \<in> insert x X \<Longrightarrow> xb \<sqsubseteq> c" for xb by (auto dest: trans)
        fix d assume "bound (\<sqsubseteq>) (insert x X) d"
        with b have "bound (\<sqsubseteq>) {x,b} d" by auto
        with c show "c \<sqsubseteq> d" by auto
      qed
    qed
  qed
done


text \<open>Gierz et al.~\cite{gierz03} showed that a directed complete partial order is semicomplete
if and only if it is also a semilattice.
We generalize the claim so that the underlying relation is only transitive.\<close>

proposition(in transitive) semicomplete_iff_directed_complete_pair_complete:
  "semicomplete (\<sqsubseteq>) \<longleftrightarrow> directed_complete (\<sqsubseteq>) \<and> pair_complete (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI semicomplete.intro)
  assume ?l
  then interpret semicomplete.
  show ?r by (intro conjI, unfold_locales)
next
  assume ?r
  then interpret directed_complete + pair_complete by auto
  interpret trans_semilattice ..
  fix X :: "'a set"
  have 1: "directed (\<sqsubseteq>) {x. \<exists>Y \<subseteq> X. finite Y \<and> Y \<noteq> {} \<and> extreme_bound (\<sqsubseteq>) Y x}" (is "directed _ ?B")
  proof (intro directedI)
    fix a b assume a: "a \<in> ?B" and b: "b \<in> ?B"
    from a obtain A where A: "extreme_bound (\<sqsubseteq>) A a" "finite A" "A \<noteq> {}" "A \<subseteq> X" by auto
    from b obtain B where B: "extreme_bound (\<sqsubseteq>) B b" "finite B" "B \<noteq> {}" "B \<subseteq> X" by auto
    from A B have AB: "finite (A \<union> B)" "A \<union> B \<noteq> {}" "A \<union> B \<subseteq> X" by auto
    with finite_nonempty_complete have "Ex (extreme_bound (\<sqsubseteq>) (A \<union> B))" by auto
    then obtain c where c: "extreme_bound (\<sqsubseteq>) (A \<union> B) c" by auto
    show "\<exists>c \<in> ?B. a \<sqsubseteq> c \<and> b \<sqsubseteq> c"
    proof (intro bexI conjI)
      from A B c show "a \<sqsubseteq> c" and "b \<sqsubseteq> c" by (auto simp: extreme_bound_iff)
      from AB c show "c \<in> ?B" by (auto intro!: exI[of _ "A \<union> B"])
    qed
  qed
  assume "X \<noteq> {}"
  then obtain x where xX: "x \<in> X" by auto
  from finite_nonempty_complete[of "{x}"]
  obtain x' where "extreme_bound (\<sqsubseteq>) {x} x'" by auto
  with xX have x'B: "x' \<in> ?B" by (auto intro!: exI[of _ "{x}"] extreme_boundI)
  then have 2: "?B \<noteq> {}" by auto
  from directed_nonempty_complete[OF 1 2]
  obtain b where b: "extreme_bound (\<sqsubseteq>) ?B b" by auto
  show "Ex (extreme_bound (\<sqsubseteq>) X)"
  proof (intro exI extreme_boundI UNIV_I)
    fix x
    assume xX: "x \<in> X"
    from finite_nonempty_complete[of "{x}"]
    obtain c where c: "extreme_bound (\<sqsubseteq>) {x} c" by auto
    then have xc: "x \<sqsubseteq> c" by auto
    from c xX have cB: "c \<in> ?B" by (auto intro!: exI[of _ "{x}"] extreme_boundI)
    with b have cb: "c \<sqsubseteq> b" by auto
    from xc cb show "x \<sqsubseteq> b" by (rule trans) text\<open> Here transitivity is needed. \<close>
  next
    fix x
    assume Xx: "bound (\<sqsubseteq>) X x"
    have "bound (\<sqsubseteq>) ?B x"
    proof (intro boundI UNIV_I, clarify)
      fix c Y
      assume "finite Y" and YX: "Y \<subseteq> X" and "Y \<noteq> {}" and c: "extreme_bound (\<sqsubseteq>) Y c"
      from YX Xx have "bound (\<sqsubseteq>) Y x" by auto
      with c show "c \<sqsubseteq> x" by auto
    qed
    with b show "b \<sqsubseteq> x" by auto
  qed
qed

text\<open>The last argument in the above proof requires transitivity,
but if we had reflexivity then $x$ itself is a supremum of $\set{x}$
(see @{thm reflexive.extreme_bound_singleton}) and so $x \SLE s$ would be immediate.
Thus we can replace transitivity by reflexivity,
but then pair-completeness does not imply finite completeness.
We obtain the following result.\<close>

proposition (in reflexive) semicomplete_iff_directed_complete_finite_complete:
  "semicomplete (\<sqsubseteq>) \<longleftrightarrow> directed_complete (\<sqsubseteq>) \<and> finite_complete (\<sqsubseteq>)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI semicomplete.intro)
  assume ?l
  then interpret semicomplete.
  show ?r by (safe, unfold_locales)
next
  assume ?r
  then interpret directed_complete + finite_complete by auto
  fix X :: "'a set"
  have 1: "directed (\<sqsubseteq>) {x. \<exists>Y \<subseteq> X. finite Y \<and> Y \<noteq> {} \<and> extreme_bound (\<sqsubseteq>) Y x}" (is "directed _ ?B")
  proof (intro directedI)
    fix a b assume a: "a \<in> ?B" and b: "b \<in> ?B"
    from a obtain A where A: "extreme_bound (\<sqsubseteq>) A a" "finite A" "A \<noteq> {}" "A \<subseteq> X" by auto
    from b obtain B where B: "extreme_bound (\<sqsubseteq>) B b" "finite B" "B \<noteq> {}" "B \<subseteq> X" by auto
    from A B have AB: "finite (A \<union> B)" "A \<union> B \<noteq> {}" "A \<union> B \<subseteq> X" by auto
    with finite_nonempty_complete have "Ex (extreme_bound (\<sqsubseteq>) (A \<union> B))" by auto
    then obtain c where c: "extreme_bound (\<sqsubseteq>) (A \<union> B) c" by auto
    show "\<exists>c \<in> ?B. a \<sqsubseteq> c \<and> b \<sqsubseteq> c"
    proof (intro bexI conjI)
      from A B c show "a \<sqsubseteq> c" and "b \<sqsubseteq> c" by (auto simp: extreme_bound_iff)
      from AB c show "c \<in> ?B" by (auto intro!: exI[of _ "A \<union> B"])
    qed
  qed
  assume "X \<noteq> {}"
  then obtain x where xX: "x \<in> X" by auto
  then have "extreme_bound (\<sqsubseteq>) {x} x" by auto
  with xX have xB: "x \<in> ?B" by (auto intro!: exI[of _ "{x}"])
  then have 2: "?B \<noteq> {}" by auto
  from directed_nonempty_complete[OF 1 2]
  obtain b where b: "extreme_bound (\<sqsubseteq>) ?B b" by auto
  show "Ex (extreme_bound (\<sqsubseteq>) X)"
  proof (intro exI extreme_boundI UNIV_I)
    fix x
    assume xX: "x \<in> X"
    have x: "extreme_bound (\<sqsubseteq>) {x} x" by auto
    from x xX have cB: "x \<in> ?B" by (auto intro!: exI[of _ "{x}"])
    with b show "x \<sqsubseteq> b" by auto
  next
    fix x
    assume Xx: "bound (\<sqsubseteq>) X x"
    have "bound (\<sqsubseteq>) ?B x"
    proof (intro boundI UNIV_I, clarify)
      fix c Y
      assume "finite Y" and YX: "Y \<subseteq> X" and "Y \<noteq> {}" and c: "extreme_bound (\<sqsubseteq>) Y c"
      from YX Xx have "bound (\<sqsubseteq>) Y x" by auto
      with c show "c \<sqsubseteq> x" by auto
    qed
    with b show "b \<sqsubseteq> x" by auto
  qed
qed

locale complete_attractive = complete + attractive

locale complete_antisymmetric = complete + antisymmetric

sublocale complete_antisymmetric \<subseteq> complete_attractive ..

text \<open>Complete pseudo orders are called complete trellises~\cite{trellis},
but let us reserve the name for introducing classes (in the future).\<close>

locale complete_pseudo_order = complete + pseudo_order

sublocale complete_pseudo_order \<subseteq> complete_antisymmetric ..

text \<open>Finally, we (re)define complete lattices as a complete partial order.\<close>

locale complete_partial_order = complete + partial_order

sublocale complete_partial_order \<subseteq> trans_semilattice + complete_pseudo_order ..

subsection \<open>Relating to Classes\<close>

class ccomplete = ord + assumes "conditionally_complete (\<le>)"
begin

sublocale order: conditionally_complete using ccomplete_axioms unfolding class.ccomplete_def.

end

class complete_ord = ord + assumes "complete (\<le>)"
begin

interpretation order: complete using complete_ord_axioms unfolding class.complete_ord_def.

subclass ccomplete ..

sublocale order: complete ..

end

text \<open>Isabelle's class @{class conditionally_complete_lattice} is @{class ccomplete}.
The other direction does not hold, since for the former,
@{term "Sup {}"} and @{term "Inf {}"} are arbitrary even if there are top or bottom elements.\<close>

subclass (in conditionally_complete_lattice) ccomplete
proof
  fix X
  assume "Ex (upper_bound X)" and X0: "X \<noteq> {}"
  from this(1) have "bdd_above X" by auto
  from cSup_upper[OF _ this] cSup_least[OF X0]
  have "supremum X (Sup X)" by (intro extremeI boundI, auto)
  then show "Ex (supremum X)" by auto
qed

text \<open>Isabelle's class @{class complete_lattice} is precisely @{locale complete_partial_order}.\<close>

context complete_lattice begin

interpretation order: complete_partial_order
  by (unfold_locales, auto intro!: Sup_upper Sup_least Inf_lower Inf_greatest)

subclass complete_ord ..

sublocale order: complete_partial_order ..

end


subsection \<open>Duality of Completeness Conditions\<close>

text \<open>Conditional completeness is symmetric.\<close>

sublocale conditionally_complete \<subseteq> dual: conditionally_complete "(\<sqsubseteq>)\<^sup>-"
proof
  interpret less_eq_dualize.
  fix X :: "'a set"
  assume bound: "Ex (bound (\<sqsupseteq>) X)" and nonemp: "X \<noteq> {}"
  then have "Ex (bound (\<sqsubseteq>) {b. bound (\<sqsupseteq>) X b})" and "{b. bound (\<sqsupseteq>) X b} \<noteq> {}" by auto
  from bounded_nonempty_complete[OF this]
  obtain s where "extreme_bound (\<sqsubseteq>) {b. bound (\<sqsupseteq>) X b} s" by auto
  then show "Ex (extreme_bound (\<sqsupseteq>) X)" by (intro exI[of _ s] extremeI, auto)
qed

text \<open>Full completeness is symmetric.\<close>

sublocale complete \<subseteq> dual: complete "(\<sqsubseteq>)\<^sup>-"
proof
  fix X :: "'a set"
  obtain s where "extreme_bound (\<sqsubseteq>) {b. bound (\<sqsubseteq>)\<^sup>- X b} s" using complete by auto
  then show "Ex (extreme_bound (\<sqsubseteq>)\<^sup>- X)" by (intro exI[of _ s] extreme_boundI, auto)
qed

sublocale complete_attractive \<subseteq> dual: complete_attractive "(\<sqsubseteq>)\<^sup>-" ..

sublocale complete_antisymmetric \<subseteq> dual: complete_antisymmetric "(\<sqsubseteq>)\<^sup>-" ..

sublocale complete_pseudo_order \<subseteq> dual: complete_pseudo_order "(\<sqsubseteq>)\<^sup>-" ..

sublocale complete_partial_order \<subseteq> dual: complete_partial_order "(\<sqsubseteq>)\<^sup>-" ..

text \<open>Now we show that bounded completeness is the dual of semicompleteness.\<close>

context fixes less_eq :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<sqsubseteq>" 50)
begin

interpretation less_eq_dualize.

definition "bounded_complete \<equiv> \<forall>X. Ex (bound (\<sqsubseteq>) X) \<longrightarrow> Ex (extreme_bound (\<sqsubseteq>) X)"

lemma pointed_conditionally_complete_iff_bounded_complete:
  "conditionally_complete (\<sqsubseteq>) \<and> bounded (\<sqsupseteq>) \<longleftrightarrow> bounded_complete"
proof safe
  assume "bounded_complete"
  note * = this[unfolded bounded_complete_def, rule_format]
  from * show "conditionally_complete (\<sqsubseteq>)" by (unfold_locales, auto)
  from *[of "{}"] show "bounded (\<sqsupseteq>)" by (unfold_locales, auto simp:bound_empty)
next
  assume "conditionally_complete (\<sqsubseteq>)" and "bounded (\<sqsupseteq>)"
  then interpret conditionally_complete "(\<sqsubseteq>)" + dual: bounded "(\<sqsupseteq>)".
  show "bounded_complete" unfolding bounded_complete_def
  proof (intro allI impI)
    fix X
    assume X: "Ex (bound (\<sqsubseteq>) X)"
    show "Ex (extreme_bound (\<sqsubseteq>) X)"
    proof (cases "X = {}")
    case True
    then show ?thesis by auto
    next
      case False
      with bounded_nonempty_complete X show ?thesis by auto
    qed
  qed
qed

proposition bounded_complete_iff_dual_semicomplete:
  "bounded_complete \<longleftrightarrow> semicomplete (\<sqsupseteq>)"
proof (fold pointed_conditionally_complete_iff_bounded_complete, safe)
  assume "conditionally_complete (\<sqsubseteq>)" and "bounded (\<sqsupseteq>)"
  then interpret conditionally_complete + bounded "(\<sqsupseteq>)".
  from dual.conditionally_complete_axioms bounded_axioms
    semicomplete_iff_conditionally_complete_bounded
  show "semicomplete (\<sqsupseteq>)" by auto
next
  assume "semicomplete (\<sqsupseteq>)"
  then interpret semicomplete "(\<sqsupseteq>)".
  show "conditionally_complete (\<sqsubseteq>)" ..
  show "bounded (\<sqsupseteq>)" ..
qed

end


subsection \<open>Completeness in Function Spaces\<close>

text \<open>Here we lift completeness to functions. As we do not assume an operator to choose suprema,
we need the axiom of choice for most of the following results. In antisymmetric cases we do not
need the axiom but we do not formalize this fact.\<close>

lemma (in bounded) bounded_fun[intro!]: "bounded (fun_ord (\<sqsubseteq>))"
proof-
  from bounded obtain t where "\<forall>x. x \<sqsubseteq> t" by auto
  then have "\<forall>f. fun_ord (\<sqsubseteq>) f (\<lambda>x. t)" by (auto intro: fun_ordI)
  then show ?thesis by (auto intro: bounded.intro)
qed

lemma (in pair_complete) pair_complete_fun[intro!]:
  "pair_complete (fun_ord (\<sqsubseteq>) :: ('i \<Rightarrow> _) \<Rightarrow> _)"
proof
  fix f g :: "'i \<Rightarrow> _"
  from pair_complete have "\<forall>x. \<exists>sx. extreme_bound (\<sqsubseteq>) {f x, g x} sx" by auto
  from choice[OF this]
  obtain s where "\<forall>x. extreme_bound (\<sqsubseteq>) {f x, g x} (s x)" by auto
  then show "Ex (extreme_bound (fun_ord (\<sqsubseteq>)) {f, g})"
    by (unfold fun_extreme_bound_iff, intro exI[of _ s], auto 1 4)
qed

lemma (in finite_complete) finite_complete_fun[intro!]:
  "finite_complete (fun_ord (\<sqsubseteq>) :: ('i \<Rightarrow> 'a) \<Rightarrow> _)"
proof
  fix F :: "('i \<Rightarrow> 'a) set"
  assume "finite F" and "F \<noteq> {}"
  with finite_nonempty_complete
  have "\<forall>x. \<exists>sx. extreme_bound (\<sqsubseteq>) {f x |. f \<in> F} sx" by auto
  from choice[OF this]
  show "Ex (extreme_bound (fun_ord (\<sqsubseteq>)) F)" by (unfold fun_extreme_bound_iff, auto)
qed

lemma (in omega_complete) omega_complete_fun[intro!]:
  "omega_complete (fun_ord (\<sqsubseteq>) :: ('i \<Rightarrow> 'a) \<Rightarrow> _)"
proof
  fix ff :: "nat \<Rightarrow> 'i \<Rightarrow> 'a"
  assume ff: "monotone (\<le>) (fun_ord (\<sqsubseteq>)) ff"
  then have "\<forall>i. Ex (extreme_bound (\<sqsubseteq>) {ff n i |. n})"
    by (intro allI monotone_seq_complete, auto simp: monotone_def fun_ord_def)
  from choice[OF this]
  obtain s where "\<forall>i. extreme_bound (\<sqsubseteq>) {ff n i |. n} (s i)" by auto
  then have "extreme_bound (fun_ord (\<sqsubseteq>)) (range ff) s"
    by (auto simp: fun_extreme_bound_iff image_image)
  then show "Ex (extreme_bound (fun_ord (\<sqsubseteq>)) (range ff))" by auto
qed

lemma (in chain_complete) chain_complete_fun[intro!]:
  "chain_complete (fun_ord (\<sqsubseteq>) :: ('i \<Rightarrow> 'a) \<Rightarrow> _)"
proof
  fix F :: "('i \<Rightarrow> 'a) set"
  assume F: "chain (fun_ord (\<sqsubseteq>)) F" and "F \<noteq> {}"
  then have "\<forall>i. Ex (extreme_bound (\<sqsubseteq>) {f i |. f \<in> F})"
    by (intro allI chain_nonempty_complete, auto simp: chain_def fun_ord_def)
  from choice[OF this]
  obtain s where "\<forall>i. extreme_bound (\<sqsubseteq>) {f i |. f \<in> F} (s i)" by auto
  then show "Ex (extreme_bound (fun_ord (\<sqsubseteq>)) F)" by (auto simp: fun_extreme_bound_iff)
qed

lemma (in directed_complete) directed_complete_fun[intro!]:
  "directed_complete (fun_ord (\<sqsubseteq>) :: ('i \<Rightarrow> 'a) \<Rightarrow> _)"
proof
  fix F :: "('i \<Rightarrow> 'a) set"
  assume dir: "directed (fun_ord (\<sqsubseteq>)) F" and F0: "F \<noteq> {}"
  have "\<forall>i. Ex (extreme_bound (\<sqsubseteq>) {f i |. f \<in> F})"
  proof (intro allI directed_nonempty_complete directedI, safe)
    fix i f g assume "f \<in> F" "g \<in> F"
    with dir obtain h
      where h: "h \<in> F" and "fun_ord (\<sqsubseteq>) f h" and "fun_ord (\<sqsubseteq>) g h" by (auto elim:directedE)
    then have "f i \<sqsubseteq> h i" and "g i \<sqsubseteq> h i" by (auto dest: fun_ordD)
    with h show "\<exists>hi\<in>{f i |. f \<in> F}. f i \<sqsubseteq> hi \<and> g i \<sqsubseteq> hi" by (intro bexI[of _ "h i"], auto)
  qed (insert F0, auto)
  from choice[OF this]
  obtain s where "\<forall>i. extreme_bound (\<sqsubseteq>) {f i |. f \<in> F} (s i)" by auto
  then show "Ex (extreme_bound (fun_ord (\<sqsubseteq>)) F)" by (auto simp: fun_extreme_bound_iff)
qed

lemma (in conditionally_complete) conditionally_complete_fun[intro!]:
  "conditionally_complete (fun_ord (\<sqsubseteq>) :: ('i \<Rightarrow> 'a) \<Rightarrow> _)"
proof
  fix F :: "('i \<Rightarrow> 'a) set"
  assume bF: "Ex (bound (fun_ord (\<sqsubseteq>)) F)" and F: "F \<noteq> {}"
  from bF obtain b where b: "bound (fun_ord (\<sqsubseteq>)) F b" by auto
  have "\<forall>x. \<exists>sx. extreme_bound (\<sqsubseteq>) {f x |. f \<in> F} sx"
  proof
    fix x
    from b have "bound (\<sqsubseteq>) {f x |. f \<in> F} (b x)" by (auto simp: fun_ord_def)
    with bounded_nonempty_complete F
    show "Ex (extreme_bound (\<sqsubseteq>) {f x |. f \<in> F})" by auto
  qed
  from choice[OF this]
  show "Ex (extreme_bound (fun_ord (\<sqsubseteq>)) F)" by (unfold fun_extreme_bound_iff, auto)
qed

lemma (in semicomplete) semicomplete_fun[intro!]: "semicomplete (fun_ord (\<sqsubseteq>))"
  by (auto simp: semicomplete_iff_conditionally_complete_bounded)

lemma (in pointed_chain_complete) pointed_chain_complete_fun[intro!]:
  "pointed_chain_complete (fun_ord (\<sqsubseteq>))"
  by (auto intro!: pointed_chain_complete.intro simp: dual_fun_ord)

lemma (in pointed_directed_complete) pointed_directed_complete_fun[intro!]:
  "pointed_directed_complete (fun_ord (\<sqsubseteq>))"
  by (auto intro!: pointed_directed_complete.intro simp: dual_fun_ord)

lemma (in complete) complete_fun[intro!]: "complete (fun_ord (\<sqsubseteq>))"
  by (auto simp: complete_iff_pointed_semicomplete dual_fun_ord)

subsection \<open>Interpretations\<close>

context complete_lattice begin

lemma Sup_eq_The_supremum: "Sup X = The (supremum X)"
  using order.complete[unfolded order.dual.ex_extreme_iff_ex1]
  by (rule the1_equality[symmetric], auto intro!: Sup_upper Sup_least)

lemma Inf_eq_The_infimum: "Inf X = The (infimum X)"
  using order.dual.complete[unfolded order.ex_extreme_iff_ex1]
  by (rule the1_equality[symmetric], auto intro!: Inf_lower Inf_greatest)

end

instance real :: ccomplete by (intro_classes, unfold_locales)

instance "fun" :: (type, ccomplete) ccomplete by (intro_classes, fold fun_ord_le, auto)

instance "fun" :: (type, complete_ord) complete_ord by (intro_classes, fold fun_ord_le, auto)

end