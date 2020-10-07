(*<*)

theory Sotomayor
imports
  Main
begin

(*>*)
section\<open> \citet{Sotomayor:1996}: A non-constructive proof of the existence of stable marriages \label{sec:sotomayor} \<close>

text\<open>

We set the scene with a non-constructive proof of the existence of
stable matches due to \citet{Sotomayor:1996}. This approach is
pleasantly agnostic about the strictness of preferences, and moreover
avoids getting bogged down in reasoning about programs; most existing
proofs involve such but omit formal treatments of the requisite
assertions. This tradition started with \citet{GaleShapley:1962}; see
\citet{Bijlsma:1991} for a rigorous treatment.

The following contains the full details of an Isabelle/HOL
formalization of her proof, and aims to introduce the machinery we
will make heavy use of later. Further developments will elide many of
the more tedious technicalities that we include here.

The scenario consists of disjoint finite sets of men @{term "M"} and
women @{term "W"}, represented as types \<open>'m::finite"\<close> and
\<open>'w::finite\<close> respectively. We diverge from
\citeauthor{Sotomayor:1996} by having each man and woman rank only
acceptable partners in a way that is transitive and complete. (Here
completeness requires @{const "Refl"} in addition to @{const "Total"}
as the latter does not imply the former, and so we end up with a total
preorder.) Such orders therefore include cycles of indifference, i.e.,
are not antisymmetric.

Also matches are treated as relations rather than functions.

We model this scenario in a @{theory_text "locale"}, a sectioning
mechanism for stating a series of lemmas relative to a set of fixed
variables (@{theory_text "fixes"}) and assumptions (@{theory_text
"assumes"}) that can later be instantiated and discharged.

\<close>

type_synonym ('m, 'w) match = "('m \<times> 'w) set"

locale StableMarriage =
  fixes Pm :: "'m::finite \<Rightarrow> 'w::finite rel"
  fixes Pw :: "'w \<Rightarrow> 'm rel"
  assumes Pm_pref: "\<forall>m. Preorder (Pm m) \<and> Total (Pm m)"
  assumes Pw_pref: "\<forall>w. Preorder (Pw w) \<and> Total (Pw w)"
begin

text\<open>

A @{emph \<open>match\<close>} assigns at most one man to each woman, and
vice-versa. It is also @{emph \<open>individually rational\<close>}, i.e., the
partners are acceptable to each other. The constant @{const "Field"}
is the union of the @{const "Domain"} and @{const "Range"} of a
relation.

\<close>

definition match :: "('m, 'w) match \<Rightarrow> bool" where
  "match \<mu> \<longleftrightarrow> inj_on fst \<mu> \<and> inj_on snd \<mu> \<and> \<mu> \<subseteq> (\<Union>m. {m} \<times> Field (Pm m)) \<inter> (\<Union>w. Field (Pw w) \<times> {w})"

text\<open>

A woman @{emph \<open>prefers\<close>} one man to another if her preference order
ranks the former over the latter, and @{emph \<open>strictly prefers\<close>} him if
additionally the latter is not ranked over the former, and similarly
for the men.

\<close>

(* AboveS doesn't work in the following: consider a cycle of
   indifference of length > 1. Two things may be not-equal but agent
   is indifferent. Suggests AboveS is for antisym rels only. *)

abbreviation (input) "m_for w \<mu> \<equiv> {m. (m, w) \<in> \<mu>}"
abbreviation (input) "w_for m \<mu> \<equiv> {w. (m, w) \<in> \<mu>}"

definition m_prefers :: "'m \<Rightarrow> ('m, 'w) match \<Rightarrow> 'w set" where
  "m_prefers m \<mu> = {w' \<in> Field (Pm m). \<forall>w\<in>w_for m \<mu>. (w, w') \<in> Pm m}"

definition w_prefers :: "'w \<Rightarrow> ('m, 'w) match \<Rightarrow> 'm set" where
  "w_prefers w \<mu> = {m' \<in> Field (Pw w). \<forall>m\<in>m_for w \<mu>. (m, m') \<in> Pw w}"

definition m_strictly_prefers :: "'m \<Rightarrow> ('m, 'w) match \<Rightarrow> 'w set" where
  "m_strictly_prefers m \<mu> = {w' \<in> Field (Pm m). \<forall>w\<in>w_for m \<mu>. (w, w') \<in> Pm m \<and> (w', w) \<notin> Pm m}"

definition w_strictly_prefers :: "'w \<Rightarrow> ('m, 'w) match \<Rightarrow> 'm set" where
  "w_strictly_prefers w \<mu> = {m' \<in> Field (Pw w). \<forall>m\<in>m_for w \<mu>. (m, m') \<in> Pw w \<and> (m', m) \<notin> Pw w}"

text\<open>

A couple @{emph \<open>blocks\<close>} a match \<open>\<mu>\<close> if both strictly
prefer each other to anyone they are matched with in
\<open>\<mu>\<close>.

\<close>

definition blocks :: "'m \<Rightarrow> 'w \<Rightarrow> ('m, 'w) match \<Rightarrow> bool" where
  "blocks m w \<mu> \<longleftrightarrow> w \<in> m_strictly_prefers m \<mu> \<and> m \<in> w_strictly_prefers w \<mu>"

text\<open>

We say a match is @{emph \<open>stable\<close>} if there are no blocking couples.

\<close>

definition stable :: "('m, 'w) match \<Rightarrow> bool" where
  "stable \<mu> \<longleftrightarrow> match \<mu> \<and> (\<forall>m w. \<not> blocks m w \<mu>)"

lemma stable_match:
  assumes "stable \<mu>"
  shows "match \<mu>"
using assms unfolding stable_def by blast

text\<open>

Our goal is to show that for every preference order there is a stable
match. Stable matches in this scenario form a lattice, and this proof
implicitly adopts the traditional view that men propose and women
choose.

The definitions above form the trust basis for this existence theorem;
the following are merely part of the proof apparatus, and Isabelle/HOL
enforces their soundness with respect to the argument. We will see
these concepts again in later developments.

Firstly, a match is @{emph \<open>simple\<close>} if every woman party to a blocking
pair is single. The most obvious such match leaves everyone single.

\<close>

definition simple :: "('m, 'w) match \<Rightarrow> bool" where
  "simple \<mu> \<longleftrightarrow> match \<mu> \<and> (\<forall>m w. blocks m w \<mu> \<longrightarrow> w \<notin> Range \<mu>)"

lemma simple_match:
  assumes "simple \<mu>"
  shows "match \<mu>"
using assms unfolding simple_def by blast

lemma simple_ex:
  "\<exists>\<mu>. simple \<mu>"
unfolding simple_def blocks_def match_def by auto

text\<open>

\citeauthor{Sotomayor:1996} observes the following:

\<close>

lemma simple_no_single_women_stable:
  assumes "simple \<mu>"
  assumes "\<forall>w. w \<in> Range \<mu>" \<comment> \<open>No woman is single\<close>
  shows "stable \<mu>"
using assms unfolding simple_def stable_def by blast

lemma stable_simple:
  assumes "stable \<mu>"
  shows "simple \<mu>"
using assms unfolding simple_def stable_def by blast

text\<open>

Secondly, a @{emph \<open>weakly Pareto optimal match for men (among all
simple matches)\<close>} is one for which there is no other match that all men
like as much and some man likes more.

\<close>

definition m_weakly_prefers :: "'m \<Rightarrow> ('m, 'w) match \<Rightarrow> 'w set" where
  "m_weakly_prefers m \<mu> = {w' \<in> Field (Pm m). \<forall>w\<in>w_for m \<mu>. (w, w') \<in> Pm m}"

definition weakly_preferred_by_men :: "('m, 'w) match \<Rightarrow> ('m, 'w) match \<Rightarrow> bool" where
  "weakly_preferred_by_men \<mu> \<mu>'
     \<longleftrightarrow> (\<forall>m. \<forall>w\<in>w_for m \<mu>. \<exists>w'\<in>w_for m \<mu>'. w' \<in> m_weakly_prefers m \<mu>)"

definition strictly_preferred_by_a_man  :: "('m, 'w) match \<Rightarrow> ('m, 'w) match \<Rightarrow> bool" where
  "strictly_preferred_by_a_man \<mu> \<mu>'
     \<longleftrightarrow> (\<exists>m. \<exists>w\<in>w_for m \<mu>'. w \<in> m_strictly_prefers m \<mu>)"

definition weakly_Pareto_optimal_for_men :: "('m, 'w) match \<Rightarrow> bool" where
  "weakly_Pareto_optimal_for_men \<mu>
     \<longleftrightarrow> simple \<mu> \<and> \<not>(\<exists>\<mu>'. simple \<mu>' \<and> weakly_preferred_by_men \<mu> \<mu>' \<and> strictly_preferred_by_a_man \<mu> \<mu>')"

text\<open>

We will often provide @{emph \<open>introduction rules\<close>} for more complex
predicates, and sometimes derive these by elementary syntactic
manipulations expressed by the @{emph \<open>attributes\<close>}
enclosed in square brackets after a use-mention of a lemma. The
@{command "lemmas"} command binds a name to the result. To conform
with the Isar structured proof language, we use meta-logic (``Pure''
in Isabelle terminology) connectives: \<open>\<And>\<close> denotes
universal quantification, and \<open>\<Longrightarrow>\<close>
implication.

\<close>

lemma weakly_preferred_by_menI:
  assumes "\<And>m w. (m, w) \<in> \<mu> \<Longrightarrow> \<exists>w'. (m, w') \<in> \<mu>' \<and> w' \<in> m_weakly_prefers m \<mu>"
  shows "weakly_preferred_by_men \<mu> \<mu>'"
using assms unfolding weakly_preferred_by_men_def by blast

lemmas simpleI = iffD2[OF simple_def, unfolded conj_imp_eq_imp_imp, rule_format]

lemma weakly_Pareto_optimal_for_men_simple:
  assumes "weakly_Pareto_optimal_for_men \<mu>"
  shows "simple \<mu>"
using assms unfolding weakly_Pareto_optimal_for_men_def by simp

text\<open>

Later we will elide obvious technical lemmas like the following. The
more obscure proofs are typically generated automatically by
sledgehammer \citep{Blanchette:2016}.

\<close>

lemma m_weakly_prefers_Pm:
  assumes "match \<mu>"
  assumes "(m, w) \<in> \<mu>"
  shows "w' \<in> m_weakly_prefers m \<mu> \<longleftrightarrow> (w, w') \<in> Pm m"
using spec[OF Pm_pref, where x=m] assms unfolding m_weakly_prefers_def match_def preorder_on_def
by simp (metis (no_types, hide_lams) FieldI2 fst_conv inj_on_contraD snd_conv)

lemma match_Field:
  assumes "match \<mu>"
  assumes "(m, w) \<in> \<mu>"
  shows "w \<in> Field (Pm m)"
    and "m \<in> Field (Pw w)"
using assms unfolding match_def by blast+

lemma weakly_preferred_by_men_refl:
  assumes "match \<mu>"
  shows "weakly_preferred_by_men \<mu> \<mu>"
using assms unfolding weakly_preferred_by_men_def m_weakly_prefers_def
by clarsimp (meson Pm_pref m_weakly_prefers_Pm match_Field(1) preorder_on_def refl_onD)

text\<open>

\citeauthor[p137]{Sotomayor:1996} provides an alternative definition
of @{const "weakly_preferred_by_men"}. The syntax @{theory_text "(is
?lhs \<longleftrightarrow> pat)"} binds the @{emph \<open>schematic
variables\<close>} \<open>?lhs\<close> and \<open>?rhs\<close> to the terms
separated by \<open>\<longleftrightarrow>\<close>.

\<close>

lemma weakly_preferred_by_men_strictly_preferred_by_a_man:
  assumes "match \<mu>"
  assumes "match \<mu>'"
  shows "weakly_preferred_by_men \<mu> \<mu>' \<longleftrightarrow> \<not>strictly_preferred_by_a_man \<mu>' \<mu>" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs then show ?rhs
    unfolding weakly_preferred_by_men_def strictly_preferred_by_a_man_def
              m_weakly_prefers_def m_strictly_prefers_def by fastforce
next
  assume ?rhs show ?lhs
  proof(rule weakly_preferred_by_menI)
    fix m w assume "(m, w) \<in> \<mu>"
    from assms \<open>?rhs\<close> \<open>(m, w) \<in> \<mu>\<close> obtain w' where XXX: "(m, w') \<in> \<mu>'" "(w', w) \<in> Pm m \<longrightarrow> (w, w') \<in> Pm m"
      unfolding match_def strictly_preferred_by_a_man_def m_strictly_prefers_def by blast
    with spec[OF Pm_pref, where x=m] assms \<open>(m, w) \<in> \<mu>\<close>
    show "\<exists>w'. (m, w') \<in> \<mu>' \<and> w' \<in> m_weakly_prefers m \<mu>"
      unfolding preorder_on_def total_on_def by (metis m_weakly_prefers_Pm match_Field(1) refl_onD)
  qed
qed

lemma weakly_Pareto_optimal_for_men_def2:
  "weakly_Pareto_optimal_for_men \<mu>
     \<longleftrightarrow> simple \<mu> \<and> (\<forall>\<mu>'. simple \<mu>' \<and> strictly_preferred_by_a_man \<mu> \<mu>' \<longrightarrow> strictly_preferred_by_a_man \<mu>' \<mu>)"
unfolding weakly_Pareto_optimal_for_men_def simple_def
by (meson weakly_preferred_by_men_strictly_preferred_by_a_man)

text\<open>

\citeauthor{Sotomayor:1996} claims that the existence of such a weakly
Pareto optimal match for men is ``guaranteed by the fact that
@{emph \<open>the set of simple matchings is nonempty\<close>} [our @{thm [source]
"simple_ex"} lemma] @{emph \<open>and finite and the preferences are
transitive.\<close>}'' The following lemmas express this intuition:

\<close>

lemma trans_finite_has_maximal_elt:
  assumes "trans r"
  assumes "finite (Field r)"
  assumes "Field r \<noteq> {}"
  shows "\<exists>x\<in>Field r. (\<forall>y\<in>Field r. (x, y) \<in> r \<longrightarrow> (y, x) \<in> r)"
using assms(2,1,3) by induct (auto elim: transE)

lemma weakly_Pareto_optimal_for_men_ex:
  "\<exists>\<mu>. weakly_Pareto_optimal_for_men \<mu>"
proof -
  let ?r = "{(\<mu>, \<mu>'). simple \<mu> \<and> simple \<mu>' \<and> weakly_preferred_by_men \<mu> \<mu>'}"
  from trans_finite_has_maximal_elt[where r="?r"]
  obtain x where "x \<in> Field ?r" "\<forall>y\<in>Field ?r. (x, y) \<in> ?r \<longrightarrow> (y, x) \<in> ?r"
  proof
    from Pm_pref show "trans ?r"
      unfolding trans_def weakly_preferred_by_men_def m_weakly_prefers_def m_strictly_prefers_def
      by simp (meson order_on_defs(1) transE)
    from simple_ex weakly_preferred_by_men_refl[OF simple_match] show "Field ?r \<noteq> {}"
      unfolding Field_def by force
  qed simp_all
  then show ?thesis
    unfolding weakly_Pareto_optimal_for_men_def Field_def
    using simple_match weakly_preferred_by_men_strictly_preferred_by_a_man by auto
qed

text\<open>

The main result proceeds by contradiction.

\<close>

lemma weakly_Pareto_optimal_for_men_stable:
  assumes "weakly_Pareto_optimal_for_men \<mu>"
  shows "stable \<mu>"
proof(rule ccontr)
  assume "\<not>stable \<mu>"
  from \<open>weakly_Pareto_optimal_for_men \<mu>\<close> have "simple \<mu>" by (rule weakly_Pareto_optimal_for_men_simple)
  from \<open>\<not>stable \<mu>\<close> \<open>simple \<mu>\<close> obtain m' w where "blocks m' w \<mu>" and "w \<notin> Range \<mu>"
    unfolding simple_def stable_def by blast+
  \<comment> \<open>Choose an \<open>m\<close> that \<open>w\<close> weakly prefers to any blocking man.\<close>
  \<comment> \<open>We restrict the preference order \<open>Pw w\<close> to the men who strictly prefer \<open>w\<close> over their match in \<open>\<mu>\<close>.\<close>
  let ?r = "Restr (Pw w) {m. w \<in> m_strictly_prefers m \<mu>}"
  from trans_finite_has_maximal_elt[where r="?r"]
  obtain m where "m \<in> Field ?r" "\<forall>m'\<in>Field ?r. (m, m') \<in> ?r \<longrightarrow> (m', m) \<in> ?r"
  proof
    from Pw_pref show "trans ?r"
      unfolding preorder_on_def by (blast intro: trans_Restr)
    from Pw_pref \<open>blocks m' w \<mu>\<close> have "(m', m') \<in> ?r"
      unfolding blocks_def w_strictly_prefers_def preorder_on_def by (blast dest: refl_onD)
    then show "Field ?r \<noteq> {}" by (metis FieldI2 empty_iff)
  qed simp_all
  with \<open>blocks m' w \<mu>\<close> \<open>w \<notin> Range \<mu>\<close>
  have "blocks m w \<mu>" and "\<forall>m'. blocks m' w \<mu> \<and> (m, m') \<in> Pw w \<longrightarrow> (m', m) \<in> Pw w"
    unfolding blocks_def w_strictly_prefers_def Field_def by auto
  \<comment> \<open>Construct a new (simple) match containing the blocking pair\ldots\<close>
  let ?\<mu>' = "\<mu> - {(m, w') |w'. True} \<union> {(m, w)}"
  \<comment> \<open>{\ldots}and show that it is a Pareto improvement for men over \<open>\<mu>\<close>.\<close>
  have "simple ?\<mu>'"
  proof(rule simpleI)
    from \<open>simple \<mu>\<close> \<open>blocks m w \<mu>\<close> show "match ?\<mu>'"
      unfolding blocks_def match_def simple_def m_strictly_prefers_def w_strictly_prefers_def
      by (safe; clarsimp simp: inj_on_diff; blast)
    fix m' w' assume "blocks m' w' ?\<mu>'"
    from \<open>blocks m' w' ?\<mu>'\<close> \<open>\<forall>m'. blocks m' w \<mu> \<and> (m, m') \<in> Pw w \<longrightarrow> (m', m) \<in> Pw w\<close>
    have "w' \<noteq> w"
      unfolding blocks_def m_strictly_prefers_def w_strictly_prefers_def by auto
    show "w' \<notin> Range ?\<mu>'"
    proof(cases "(m, w') \<in> \<mu>")
      case True
      from \<open>simple \<mu>\<close> \<open>blocks m' w' ?\<mu>'\<close> \<open>w' \<noteq> w\<close> \<open>(m, w') \<in> \<mu>\<close>
      show ?thesis
        unfolding simple_def match_def
        by clarsimp (metis (no_types, hide_lams) fst_conv inj_on_contraD snd_conv)
    next
      case False
      from Pm_pref \<open>blocks m w \<mu>\<close> \<open>blocks m' w' ?\<mu>'\<close> \<open>(m, w') \<notin> \<mu>\<close>
      have "blocks m' w' \<mu>"
        unfolding preorder_on_def blocks_def m_strictly_prefers_def w_strictly_prefers_def
        by simp (metis transE)
      with \<open>simple \<mu>\<close> \<open>w' \<noteq> w\<close> show ?thesis unfolding simple_def by blast
    qed
  qed
  moreover have "weakly_preferred_by_men \<mu> ?\<mu>'"
  proof(rule weakly_preferred_by_menI)
    fix m' w' assume "(m', w') \<in> \<mu>"
    then show "\<exists>w'. (m', w') \<in> ?\<mu>' \<and> w' \<in> m_weakly_prefers m' \<mu>"
    proof(cases "m' = m")
      case True
      from \<open>blocks m w \<mu>\<close> \<open>(m', w') \<in> \<mu>\<close> \<open>m' = m\<close> show ?thesis
        unfolding m_weakly_prefers_def blocks_def m_strictly_prefers_def by blast
    next
      case False
      from Pm_pref \<open>simple \<mu>\<close> \<open>(m', w') \<in> \<mu>\<close> \<open>m' \<noteq> m\<close> show ?thesis
        by clarsimp (meson m_weakly_prefers_Pm match_Field preorder_on_def refl_onD simple_match)
    qed
  qed
  moreover from \<open>blocks m w \<mu>\<close> have "strictly_preferred_by_a_man \<mu> ?\<mu>'"
    unfolding strictly_preferred_by_a_man_def blocks_def by blast
  moreover note \<open>weakly_Pareto_optimal_for_men \<mu>\<close>
  ultimately show False
    unfolding weakly_Pareto_optimal_for_men_def by blast
qed

theorem stable_ex:
  "\<exists>\<mu>. stable \<mu>"
using weakly_Pareto_optimal_for_men_stable weakly_Pareto_optimal_for_men_ex by blast

text\<open>

We can exit the locale context and later re-enter it.

\<close>

end

text\<open>

We @{emph \<open>interpret\<close>} the locale by supplying constants that instantiate
the variables we fixed earlier, and proving that these satisfy the
assumptions. In this case we provide concrete preference orders, and
by doing so we demonstrate that our theory is non-vacuous. We
arbitrarily choose \citet[Example~2.15]{RothSotomayor:1990} which
demonstrates the non-existence of man- or woman-optimal matches if
preferences are non-strict. (We define optimality shortly.) The
following bunch of types eases the description of this particular
scenario.

\<close>

datatype M = M1 | M2 | M3
datatype W = W1 | W2 | W3

lemma M_UNIV: "UNIV = set [M1, M2, M3]" using M.exhaust by auto
lemma W_UNIV: "UNIV = set [W1, W2, W3]" using W.exhaust by auto

instance M :: finite by standard (simp add: M_UNIV)
instance W :: finite by standard (simp add: W_UNIV)

lemma M_All:
  shows "(\<forall>m. P m) \<longleftrightarrow> (\<forall>m\<in>set [M1, M2, M3]. P m)"
by (metis M_UNIV UNIV_I)

lemma W_All:
  shows "(\<forall>w. P w) \<longleftrightarrow> (\<forall>w\<in>set [W1, W2, W3]. P w)"
by (metis W_UNIV UNIV_I)

primrec Pm :: "M \<Rightarrow> W rel" where
  "Pm M1 = { (W1, W1), (W1, W2), (W1, W3), (W2, W2), (W2, W3), (W3, W3), (W3, W2) }"
| "Pm M2 = { (W1, W1), (W1, W2), (W2, W2) }"
| "Pm M3 = { (W1, W1), (W1, W3), (W3, W3) }"

primrec Pw :: "W \<Rightarrow> M rel" where
  "Pw W1 = { (M3, M3), (M3, M2), (M3, M1), (M2, M2), (M2, M1), (M1, M1) }"
| "Pw W2 = { (M2, M2), (M2, M1), (M1, M1) }"
| "Pw W3 = { (M3, M3), (M3, M1), (M1, M1) }"

lemma Pm: "Preorder (Pm m) \<and> Total (Pm m)"
unfolding preorder_on_def refl_on_def trans_def total_on_def
by (cases m) (safe, auto)

lemma Pw: "Preorder (Pw w) \<and> Total (Pw w)"
unfolding preorder_on_def refl_on_def trans_def total_on_def
by (cases w) (safe, auto)

interpretation Non_Strict: StableMarriage Pm Pw
using Pm Pw by unfold_locales blast+

text\<open>

We demonstrate that there are only two stable matches in this
scenario.  Isabelle/HOL does not have any special support for these
types of model checking problems, so we simply try all combinations of
men and women. Clearly this does not scale, and for larger domains we
need to be a bit cleverer (see \S\ref{sec:bossiness}).

\<close>

lemma Non_Strict_stable1:
  shows "Non_Strict.stable {(M1, W2), (M2, W1), (M3, W3)}"
unfolding Non_Strict.stable_def Non_Strict.match_def Non_Strict.blocks_def Non_Strict.m_strictly_prefers_def
          Non_Strict.w_strictly_prefers_def
by clarsimp (metis M.exhaust)

lemma Non_Strict_stable2:
  shows "Non_Strict.stable {(M1, W3), (M2, W2), (M3, W1)}"
unfolding Non_Strict.stable_def Non_Strict.match_def Non_Strict.blocks_def Non_Strict.m_strictly_prefers_def
          Non_Strict.w_strictly_prefers_def
by clarsimp (metis M.exhaust)

lemma Non_Strict_stable_matches:
  "Non_Strict.stable \<mu>
     \<longleftrightarrow> \<mu> = {(M1, W2), (M2, W1), (M3, W3)}
     \<or> \<mu> = {(M1, W3), (M2, W2), (M3, W1)}" (is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs
  have "\<mu> \<in> set ` set (subseqs (List.product [M1, M2, M3] [W1, W2, W3]))"
    by (subst subseqs_powset; clarsimp; metis M.exhaust W.exhaust)
  with \<open>?lhs\<close> show ?rhs
    unfolding Non_Strict.stable_def Non_Strict.match_def
    apply (simp cong: INF_cong_simp SUP_cong_simp cong del: image_cong_simp)
    apply (elim disjE)
    apply (simp_all cong: INF_cong_simp SUP_cong_simp cong del: image_cong_simp)
    apply (simp_all add: M_All W_All Non_Strict.blocks_def Non_Strict.m_strictly_prefers_def
                         Non_Strict.w_strictly_prefers_def cong: INF_cong_simp SUP_cong_simp cong del: image_cong_simp)
    done
next
  assume ?rhs with Non_Strict_stable1 Non_Strict_stable2 show ?lhs by blast
qed

text\<open>

So far the only interesting result in this interpretation of
\<open>StableMarriage\<close> is the @{thm [source]
"Non_Strict.stable_ex"} theorem, i.e., that there is a stable
match. We now add the notion of @{emph \<open>optimality\<close>} to our locale, and
all interpretations will automatically inherit it. Later we will also
extend locales by adding new fixed variables and assumptions.

Following \citet[Definition~2.11]{RothSotomayor:1990}, a stable match
is @{emph \<open>optimal for men\<close>} if every man likes it at least as much as
any other stable match (and similarly for an @{emph \<open>optimal for
women\<close>} match).

\<close>

context StableMarriage
begin

definition optimal_for_men :: "('m, 'w) match \<Rightarrow> bool" where
  "optimal_for_men \<mu>
     \<longleftrightarrow> stable \<mu> \<and> (\<forall>\<mu>'. stable \<mu>' \<longrightarrow> weakly_preferred_by_men \<mu>' \<mu>)"

definition w_weakly_prefers :: "'w \<Rightarrow> ('m, 'w) match \<Rightarrow> 'm set" where
  "w_weakly_prefers w \<mu> = {m' \<in> Field (Pw w). \<forall>m\<in>m_for w \<mu>. (m, m') \<in> Pw w}"

definition weakly_preferred_by_women :: "('m, 'w) match \<Rightarrow> ('m, 'w) match \<Rightarrow> bool" where
  "weakly_preferred_by_women \<mu> \<mu>'
     \<longleftrightarrow> (\<forall>w. \<forall>m\<in>m_for w \<mu>. \<exists>m'\<in>m_for w \<mu>'. m' \<in> w_weakly_prefers w \<mu>)"

definition optimal_for_women :: "('m, 'w) match \<Rightarrow> bool" where
  "optimal_for_women \<mu>
     \<longleftrightarrow> stable \<mu> \<and> (\<forall>\<mu>'. stable \<mu>' \<longrightarrow> weakly_preferred_by_women \<mu> \<mu>')"

end

text\<open>

We can show that there is no optimal stable match for these
preferences:

\<close>

lemma NonStrict_not_optimal:
  assumes "Non_Strict.stable \<mu>"
  shows "\<not>Non_Strict.optimal_for_men \<mu> \<and> \<not>Non_Strict.optimal_for_women \<mu>"
proof -
  from assms[unfolded Non_Strict_stable_matches] show ?thesis
  proof(rule disjE)
    assume "\<mu> = {(M1, W2), (M2, W1), (M3, W3)}"
    with assms show ?thesis
      unfolding Non_Strict.optimal_for_men_def Non_Strict.weakly_preferred_by_men_def
                Non_Strict.m_weakly_prefers_def Non_Strict.optimal_for_women_def
                Non_Strict.weakly_preferred_by_women_def Non_Strict.w_weakly_prefers_def
                Non_Strict_stable_matches
      by clarsimp (rule conjI; rule exI[where x="{(M1, W3), (M2, W2), (M3, W1)}"]; blast)
  next
    assume "\<mu> = {(M1, W3), (M2, W2), (M3, W1)}"
    with assms show ?thesis
      unfolding Non_Strict.optimal_for_men_def Non_Strict.weakly_preferred_by_men_def
                Non_Strict.m_weakly_prefers_def Non_Strict.optimal_for_women_def
                Non_Strict.weakly_preferred_by_women_def Non_Strict.w_weakly_prefers_def
                Non_Strict_stable_matches
      by clarsimp (rule conjI; rule exI[where x="{(M1, W2), (M2, W1), (M3, W3)}"]; blast)
  qed
qed

text\<open>

\citet{Sotomayor:1996} remarks that, if the preferences are strict,
there is only one weakly Pareto optimal match for men, and that it is
man-optimal. (This is the match found by the classic man-proposing
deferred acceptance algorithm due to \citet{GaleShapley:1962}.)
However she omits a proof that the man-optimal match actually exists
under strict preferences.

The easiest way to show this and further results is to exhibit the
lattice structure of the stable matches discovered by Conway (see
\citet[Theorem~2.16]{RothSotomayor:1990}), where the men- and
women-optimal matches are the extremal points. This suggests looking
for a monotonic function whose fixed points are this lattice, which is
the essence of the analysis of matching with contracts in
\S\ref{sec:contracts}.

\<close>
(*<*)

end
(*>*)
