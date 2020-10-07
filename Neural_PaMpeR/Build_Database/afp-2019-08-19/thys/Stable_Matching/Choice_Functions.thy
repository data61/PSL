(*<*)
theory Choice_Functions
imports
  Basis
begin
(*>*)

section\<open> Choice Functions \label{sec:cf} \<close>

text\<open>

We now develop a few somewhat general results about choice functions,
following \citet{Moulin:1985,Sen:1970,Border:2012}.
\citet{sep-preferences} provide some philosophical background on this
topic. While this material is foundational to the story we tell about
stable matching, it is perhaps best skipped over on a first reading.

The game here is to study conditions on functions that yield
acceptable choices from a given set of alternatives drawn from some
universe (a set, often a type in HOL). We adopt the Isabelle
convention of attaching the suffix @{emph \<open>on\<close>} to
predicates that are defined on subsets of their types.

\<close>

type_synonym 'a cfun = "'a set \<Rightarrow> 'a set"

text\<open>

Most results require that the choice function yield a subset of its
argument:

\<close>

definition f_range_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "f_range_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. f B \<subseteq> B)"

abbreviation f_range :: "'a cfun \<Rightarrow> bool" where
  "f_range \<equiv> f_range_on UNIV"
(*<*)

lemma f_range_onI:
  "(\<And>B. B \<subseteq> A \<Longrightarrow> f B \<subseteq> B) \<Longrightarrow> f_range_on A f"
unfolding f_range_on_def by blast

lemmas f_range_onD = iffD1[OF f_range_on_def, rule_format]
lemmas f_range_onD' = subsetD[OF f_range_onD, rotated -1]

lemma f_range_on_antimono:
  assumes "f_range_on B f"
  assumes "A \<subseteq> B"
  shows "f_range_on A f"
using assms unfolding f_range_on_def by blast

(*>*)
text\<open>

Economists typically assume that the universe is finite, and @{term
"f"} is @{emph \<open>decisive\<close>}, i.e., yields non-empty sets when given
non-empty sets.

\<close>

definition decisive_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "decisive_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. B \<noteq> {} \<longrightarrow> f B \<noteq> {})"

abbreviation decisive :: "'a cfun \<Rightarrow> bool" where
  "decisive \<equiv> decisive_on UNIV"
(*<*)

lemmas decisive_onD = iffD1[OF decisive_on_def, rule_format]
lemmas decisive_onI = iffD2[OF decisive_on_def, rule_format]

lemma decisive_on_empty:
  shows "decisive_on {} f"
unfolding decisive_on_def by simp

lemma decisive_on_mono:
  assumes "decisive_on A f"
  assumes "B \<subseteq> A"
  shows "decisive_on B f"
using assms order_trans unfolding decisive_on_def by auto

(*>*)
text\<open>

Often we can mildly generalise existing results by not requiring that
@{term "f"} be @{const "decisive"}, and by dropping the finiteness
hypothesis. We make essential use of the former generalization in
\S\ref{sec:contracts}.

Some choice functions, such as those arising from linear orders
(\S\ref{sec:cf-linear}), are @{emph \<open>resolute\<close>}: these always yield a
single choice.

\<close>

definition resolute_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "resolute_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. B \<noteq> {} \<longrightarrow> (\<exists>a. f B = {a}))"

abbreviation resolute :: "'a cfun \<Rightarrow> bool" where
  "resolute \<equiv> resolute_on UNIV"

lemma resolute_on_decisive_on:
  assumes "resolute_on A f"
  shows "decisive_on A f"
using %invisible assms unfolding resolute_on_def by - (rule decisive_onI; auto)

text\<open>

Often we talk about the choices that are rejected by \<open>f\<close>:

\label{sec:cf-rf}

\<close>

abbreviation Rf :: "'a cfun \<Rightarrow> 'a cfun" where
  "Rf f X \<equiv> X - f X"

text\<open>

Typically there are many (almost-)equivalent formulations of each
property in the literature. We try to formulate our rules in terms of
the most general of these.

\<close>


subsection\<open> The @{emph \<open>substitutes\<close>} condition, AKA @{emph \<open>independence of irrelevant alternatives\<close>} \label{sec:cf-substitutes} AKA @{emph \<open>Chernoff\<close>} \<close>

text\<open>

Loosely speaking, the @{emph \<open>substitutes\<close>} condition asserts that an
alternative that is rejected from @{term "A"} shall remain rejected
when there is ``increased competition,'' i.e., from all sets that
contain @{term "A"}.

\citet{HatfieldMilgrom:2005} define this property as simply the
monotonicity of @{const "Rf"}. \citet{AygunSonmez:2012-WP2} instead
use the complicated condition shown here. Condition
\<open>\<alpha>\<close>, due to \citet[p17, see below]{Sen:1970}, is
the most general and arguably the most perspicuous.

\<close>

definition substitutes_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "substitutes_on A f \<longleftrightarrow> \<not>(\<exists>B\<subseteq>A. \<exists>a b. {a, b} \<subseteq> A - B \<and> b \<notin> f (B \<union> {b}) \<and> b \<in> f (B \<union> {a, b}))"

abbreviation substitutes :: "'a cfun \<Rightarrow> bool" where
  "substitutes \<equiv> substitutes_on UNIV"

lemma substitutes_on_def2[simplified]:
  "substitutes_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>a\<in>A. \<forall>b\<in>A. b \<notin> f (B \<union> {b}) \<longrightarrow> b \<notin> f (B \<union> {a, b}))"
(*<*)
(is "?lhs \<longleftrightarrow> ?rhs")
proof (rule iffI, clarsimp)
  fix B a b
  assume lhs: ?lhs and XXX: "B \<subseteq> A" "a \<in> A" "b \<in> A" "b \<notin> f (insert b B)" "b \<in> f (insert a (insert b B))"
  show False
  proof(cases "a \<in> B")
    case True with XXX show ?thesis by (simp add: insert_absorb)
  next
    case False with lhs XXX show ?thesis
      unfolding substitutes_on_def
      by (cases "b \<in> B") (fastforce dest: spec[where x="B - {a, b}"] simp: insert_commute insert_absorb)+
  qed
qed (fastforce simp: substitutes_on_def)

lemmas substitutes_onI = iffD2[OF substitutes_on_def2, rule_format, simplified]
lemmas substitutes_onD = iffD1[OF substitutes_on_def2, rule_format, simplified]

lemmas substitutesD = substitutes_onD[where A=UNIV, simplified]

(*>*)
text\<open>\<close>

lemma substitutes_on_union:
  assumes "a \<notin> f (B \<union> {a})"
  assumes "substitutes_on (A \<union> B \<union> {a}) f"
  assumes "finite A"
  shows "a \<notin> f (A \<union> B \<union> {a})"
using %invisible assms(3,1-2) by induct (simp_all add: insert_commute substitutes_on_def2 le_iff_sup)

lemma substitutes_on_antimono:
  assumes "substitutes_on B f"
  assumes "A \<subseteq> B"
  shows "substitutes_on A f"
using %invisible assms unfolding substitutes_on_def2 by auto

text\<open>

The equivalence with the monotonicity of alternative-rejection
requires a finiteness constraint.

\<close>

lemma substitutes_on_Rf_mono_on:
  assumes "substitutes_on A f"
  assumes "finite A"
  shows "mono_on (Pow A) (Rf f)"
proof %invisible (rule mono_onI, rule subsetI)
  fix B C x assume "B \<in> Pow A" "C \<in> Pow A" "B \<subseteq> C" "x \<in> Rf f B"
  with assms substitutes_on_union[where a=x and A=C and B=B and f=f] show "x \<in> Rf f C"
    by (clarsimp simp: insert_absorb) (metis rev_finite_subset subsetCE substitutes_on_antimono sup.orderE)
qed

lemma Rf_mono_on_substitutes:
  assumes "mono_on (Pow A) (Rf f)"
  shows "substitutes_on A f"
proof %invisible (rule substitutes_onI)
  fix B a b assume "B \<subseteq> A" "a \<in> A" "b \<in> A" "b \<notin> f (insert b B)"
  with assms show "b \<notin> f (insert a (insert b B))"
    by (auto elim: mono_onE[where x="insert b B" and y="insert a (insert b B)"])
qed

text\<open>

The above substitutes condition is equivalent to the
@{emph \<open>independence of irrelevant alternatives\<close>}, AKA condition
\<open>\<alpha>\<close> due to \citet{Sen:1970}. Intuitively if
\<open>a\<close> is chosen from a set \<open>A\<close>, then it must
be chosen from every subset of \<open>A\<close> that it belongs
to. Note the lack of finiteness assumptions here.

\<close>

definition iia_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "iia_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>C\<subseteq>B. \<forall>a\<in>C. a \<in> f B \<longrightarrow> a \<in> f C)"

abbreviation iia :: "'a cfun \<Rightarrow> bool" where
  "iia \<equiv> iia_on UNIV"

lemmas %invisible iia_onI = iffD2[OF iia_on_def, rule_format, unfolded conj_imp_eq_imp_imp]
lemmas %invisible iia_onD = iffD1[OF iia_on_def, rule_format, unfolded conj_imp_eq_imp_imp]

lemma Rf_mono_on_iia_on:
  shows "mono_on (Pow A) (Rf f) \<longleftrightarrow> iia_on A f"
unfolding %invisible iia_on_def by (rule iffI) (blast elim: mono_onE intro!: mono_onI)+

lemma Rf_mono_iia:
  shows "mono (Rf f) \<longleftrightarrow> iia f"
using %invisible Rf_mono_on_iia_on[of UNIV f] mono_on_mono by (simp add: fun_eq_iff) blast

lemma substitutes_iia:
  assumes "finite A"
  shows "substitutes_on A f \<longleftrightarrow> iia_on A f"
using %invisible Rf_mono_on_iia_on Rf_mono_on_substitutes substitutes_on_Rf_mono_on[OF _ assms] by blast

text\<open>

One key result is that the choice function must be idempotent if it
satisfies @{const "iia"} or any of the equivalent conditions.

\<close>

lemma iia_f_idem:
  assumes "f_range_on A f"
  assumes "iia_on A f"
  assumes "B \<subseteq> A"
  shows "f (f B) = f B"
using %invisible assms unfolding iia_on_def
by (meson f_range_onD f_range_on_antimono subset_antisym subset_eq)

text\<open>

\citet[p914, bottom right]{HatfieldMilgrom:2005} claim that the
@{const "substitutes"} condition coincides with the
@{emph \<open>substitutable preferences\<close>} condition for the college admissions
problem of \citet[Definition~6.2]{RothSotomayor:1990}, which is
similar to @{const "iia"}:

\<close>

definition substitutable_preferences_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "substitutable_preferences_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>a\<in>B. \<forall>b\<in>B. a \<noteq> b \<and> a \<in> f B \<longrightarrow> a \<in> f (B - {b}))"

lemmas %invisible substitutable_preferences_onI = iffD2[OF substitutable_preferences_on_def, rule_format, unfolded conj_imp_eq_imp_imp]

lemma substitutable_preferences_on_substitutes_on:
  shows "substitutable_preferences_on A f \<longleftrightarrow> substitutes_on A f" (is "?lhs \<longleftrightarrow> ?rhs")
proof %invisible (rule iffI)
  assume ?lhs then show ?rhs
    unfolding substitutable_preferences_on_def
    by - (rule substitutes_onI; metis Diff_insert_absorb insertCI insert_absorb insert_subset)
next
  assume ?rhs show ?lhs
  proof(rule substitutable_preferences_onI)
    fix B a b
    assume XXX: "B \<subseteq> A" "a \<in> B" "b \<in> B" "a \<noteq> b" "a \<in> f B"
    then have "a \<in> A" "b \<in> A" "B - {b} - {a} \<subseteq> A" by blast+
    with \<open>?rhs\<close> XXX show "a \<in> f (B - {b})"
      unfolding substitutes_on_def2 by (metis insertE insert_Diff)
  qed
qed

text\<open>

\citet[p152]{Moulin:1985} defines an equivalent @{emph \<open>Chernoff\<close>}
condition. Intuitively this captures the idea that ``a best choice in
some issue [set of alternatives] is still best if the issue shrinks.''

\<close>

definition Chernoff_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "Chernoff_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>C\<subseteq>B. f B \<inter> C \<subseteq> f C)"

abbreviation Chernoff :: "'a cfun \<Rightarrow> bool" where
  "Chernoff \<equiv> Chernoff_on UNIV"

lemmas Chernoff_onI = iffD2[OF Chernoff_on_def, rule_format]
lemmas Chernoff_def = Chernoff_on_def[where A=UNIV, simplified]

lemma Chernoff_on_iia_on:
  shows "Chernoff_on A f \<longleftrightarrow> iia_on A f"
unfolding %invisible Chernoff_on_def iia_on_def by blast

lemma Chernoff_on_union:
  assumes "Chernoff_on A f"
  assumes "f_range_on A f"
  assumes "B \<subseteq> A" "C \<subseteq> A"
  shows "f (B \<union> C) \<subseteq> f B \<union> f C"
using %invisible assms unfolding Chernoff_on_def f_range_on_def
by clarsimp (metis (mono_tags, lifting) Int_iff Un_iff Un_subset_iff contra_subsetD inf_sup_ord(3,4))

text\<open>

\citet[p159]{Moulin:1985} states a series of equivalent formulations
of the @{const "Chernoff"} condition. He also claims that these hold
if the two sets are disjoint.

\<close>

lemma Chernoff_a:
  assumes "f_range_on A f"
  shows "Chernoff_on A f \<longleftrightarrow> (\<forall>B C. B \<subseteq> A \<and> C \<subseteq> A \<longrightarrow> f (B \<union> C) \<subseteq> f B \<union> C)" (is "?lhs \<longleftrightarrow> ?rhs")
proof %invisible (rule iffI)
  assume ?lhs with \<open>f_range_on A f\<close> show ?rhs by (auto dest: f_range_onD' Chernoff_on_union)
next
  assume ?rhs show ?lhs
  proof(rule Chernoff_onI)
    fix B C assume "B \<subseteq> A" "C \<subseteq> B"
    with spec[OF spec[OF \<open>?rhs\<close>, where x="C"], where x="B - C"] show "f B \<inter> C \<subseteq> f C"
      by (fastforce simp add: Un_absorb1)
  qed
qed

lemma Chernoff_b: \<comment> \<open>essentially the converse of @{thm [source] Chernoff_on_union}\<close>
  assumes "f_range_on A f"
  shows "Chernoff_on A f \<longleftrightarrow> (\<forall>B C. B \<subseteq> A \<and> C \<subseteq> A \<longrightarrow> f (B \<union> C) \<subseteq> f B \<union> f C)" (is "?lhs \<longleftrightarrow> ?rhs")
proof %invisible (rule iffI)
  assume ?lhs with \<open>f_range_on A f\<close> show ?rhs using Chernoff_on_union by blast
next
  assume ?rhs show ?lhs
  proof(rule Chernoff_onI)
    fix B C assume "B \<subseteq> A" "C \<subseteq> B"
    with \<open>f_range_on A f\<close> spec[OF spec[OF \<open>?rhs\<close>, where x="C"], where x="B - C"]
    show "f B \<inter> C \<subseteq> f C" by (clarsimp simp: Un_absorb1) (blast dest: f_range_onD')
  qed
qed

lemma Chernoff_c:
  assumes "f_range_on A f"
  shows "Chernoff_on A f \<longleftrightarrow> (\<forall>B C. B \<subseteq> A \<and> C \<subseteq> A \<longrightarrow> f (B \<union> C) \<subseteq> f (f B \<union> C))" (is "?lhs \<longleftrightarrow> ?rhs")
proof %invisible (rule iffI)
  assume ?lhs show ?rhs
  proof(safe)
    fix B C x
    assume B: "B \<subseteq> A" and C: "C \<subseteq> A" and x: "x \<in> f (B \<union> C)"
    from B C have "f (B \<union> C) \<subseteq> f B \<union> f C" by (rule Chernoff_on_union[OF \<open>?lhs\<close> \<open>f_range_on A f\<close>])
    with \<open>f_range_on A f\<close> C x have "x \<in> f B \<union> C" by (blast dest: f_range_onD)
    moreover from \<open>f_range_on A f\<close> B have "f B \<union> C \<subseteq> B \<union> C" by (blast dest: f_range_onD)
    moreover note B C x
    ultimately show "x \<in> f (f B \<union> C)"
      using iia_onD[OF iffD1[OF Chernoff_on_iia_on \<open>?lhs\<close>]] by (metis Un_subset_iff)
  qed
next
  assume ?rhs with \<open>f_range_on A f\<close> show ?lhs
    unfolding f_range_on_def
    by (clarsimp simp: Chernoff_a[OF \<open>f_range_on A f\<close>])
       (metis (no_types, lifting) Un_iff Un_subset_iff rev_subsetD subset_trans)
qed

lemma Chernoff_d:
  assumes "f_range_on A f"
  shows "Chernoff_on A f \<longleftrightarrow> (\<forall>B C. B \<subseteq> A \<and> C \<subseteq> A \<longrightarrow> f (B \<union> C) \<subseteq> f (f B \<union> f C))" (is "?lhs \<longleftrightarrow> ?rhs")
proof %invisible (rule iffI)
  assume ?lhs show ?rhs
  proof(intro allI impI)
    fix B C x
    assume BC: "B \<subseteq> A \<and> C \<subseteq> A"
    with \<open>f_range_on A f\<close> \<open>?lhs\<close> have "f (B \<union> C) \<subseteq> f (f B \<union> C)" by (metis Chernoff_c Un_commute)
    with \<open>f_range_on A f\<close> BC show "f (B \<union> C) \<subseteq> f (f B \<union> f C)"
      using iffD1[OF Chernoff_c[OF \<open>f_range_on A f\<close>] \<open>?lhs\<close>]
      unfolding f_range_on_def by (metis Un_commute inf.absorb_iff2 le_infI1)
  qed
next
  assume ?rhs with \<open>f_range_on A f\<close> show ?lhs
    unfolding f_range_on_def
    by (clarsimp simp: Chernoff_a[OF assms])
       (metis (no_types, lifting) Un_iff Un_subset_iff rev_subsetD subset_trans)
qed


subsection\<open> The @{emph \<open>irrelevance of rejected contracts\<close>} condition AKA @{emph \<open>consistency\<close>} AKA @{emph \<open>Aizerman\<close>} \label{sec:cf-irc} \<close>

text\<open>

\citet[\S4]{AygunSonmez:2012-WP2} propose to repair the results of
\citet{HatfieldMilgrom:2005} by imposing the @{emph \<open>irrelevance of
rejected contracts\<close>} (IRC) condition. Intuitively this requires the
choice function @{term "f"} to ignore unchosen alternatives.

\<close>

definition irc_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "irc_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>a\<in>A. a \<notin> f (B \<union> {a}) \<longrightarrow> f (B \<union> {a}) = f B)"

abbreviation irc :: "'a cfun \<Rightarrow> bool" where
  "irc \<equiv> irc_on UNIV"

lemmas %invisible irc_onI = iffD2[OF irc_on_def, rule_format, simplified]
lemmas %invisible irc_onD = iffD1[OF irc_on_def, rule_format, simplified]
lemmas %invisible irc_def = irc_on_def[where A=UNIV, simplified]
lemmas %invisible ircI = iffD2[OF irc_def, rule_format, simplified]
lemmas %invisible ircD = iffD1[OF irc_def, rule_format, simplified]

lemma irc_on_discard:
  assumes "irc_on A f"
  assumes "finite C"
  assumes "B \<union> C \<subseteq> A"
  assumes "f (B \<union> C) \<inter> C = {}"
  shows "f (B \<union> C) = f B"
using %invisible assms(2,3,4)
proof induct
  case (insert c C) with assms(1) show ?case
    unfolding irc_on_def by simp (metis Un_subset_iff)
qed simp

text\<open>

An equivalent condition is called @{emph \<open>consistency\<close>} by some
(\citet[Definition~2]{ChambersYenmez:2013},
\citet[Equation~(14)]{Fleiner:2002}). Like @{const "iia"}, this
formulation generalizes to infinite universes.

\<close>

definition consistency_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "consistency_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>C\<subseteq>B. f B \<subseteq> C \<longrightarrow> f B = f C)"

abbreviation consistency :: "'a cfun \<Rightarrow> bool" where
  "consistency \<equiv> consistency_on UNIV"

lemmas %invisible consistency_onI = iffD2[OF consistency_on_def, rule_format, unfolded conj_imp_eq_imp_imp]
lemmas %invisible consistency_onD = iffD1[OF consistency_on_def, rule_format, unfolded conj_imp_eq_imp_imp]
lemmas %invisible consistency_def = consistency_on_def[where A=UNIV, simplified]
lemmas %invisible consistencyD = iffD1[OF consistency_def, rule_format, unfolded conj_imp_eq_imp_imp]

lemma irc_on_consistency_on:
  assumes "irc_on A f"
  assumes "finite A"
  shows "consistency_on A f"
proof %invisible (rule consistency_onI)
  fix B C assume "B \<subseteq>A" "f B \<subseteq> C" "C \<subseteq> B"
  then have "C \<union> (B - f B) = B" by blast
  with \<open>B \<subseteq>A\<close> \<open>finite A\<close> show "f B = f C"
    using irc_on_discard[OF assms(1), where B=C and C="B - f B"] by (simp add: finite_subset)
qed

lemma consistency_on_irc_on:
  assumes "f_range_on A f"
  assumes "consistency_on A f"
  shows "irc_on A f"
proof %invisible (rule irc_onI)
  fix B b assume "B \<subseteq> A" "b \<in> A" "b \<notin> f (insert b B)"
  with assms show "f (insert b B) = f B"
    by - (erule consistency_onD; blast dest: f_range_onD')
qed

text\<open>

These conditions imply that @{term "f"} is idempotent:

\<close>

lemma consistency_on_f_idem:
  assumes "f_range_on A f"
  assumes "consistency_on A f"
  assumes "B \<subseteq> A"
  shows "f (f B) = f B"
using %invisible assms by (metis consistency_onD f_range_onD order_refl)

text\<open>

\citet[p154]{Moulin:1985} defines a similar but weaker property he
calls @{emph \<open>Aizerman\<close>}:

\<close>

definition Aizerman_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "Aizerman_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>C\<subseteq>B. f B \<subseteq> C \<longrightarrow> f C \<subseteq> f B)"

abbreviation Aizerman :: "'a cfun \<Rightarrow> bool" where
  "Aizerman \<equiv> Aizerman_on UNIV"

lemmas %invisible Aizerman_onI = iffD2[OF Aizerman_on_def, rule_format, unfolded conj_imp_eq_imp_imp]
lemmas %invisible Aizerman_onD = iffD1[OF Aizerman_on_def, rule_format, unfolded conj_imp_eq_imp_imp]
lemmas %invisible Aizerman_def = Aizerman_on_def[where A=UNIV, simplified]

lemma consistency_on_Aizerman_on:
  assumes "consistency_on A f"
  shows "Aizerman_on A f"
using %invisible assms by (metis Aizerman_onI consistency_onD order_refl)

text\<open>

The converse requires @{term "f"} to be idempotent
\citep[p157]{Moulin:1985}:

\<close>

lemma Aizerman_on_idem_on_consistency_on:
  assumes "Aizerman_on A f"
  assumes "\<forall>B\<subseteq>A. f (f B) = f B"
  shows "consistency_on A f"
by %invisible (rule consistency_onI) (metis inf.coboundedI2 le_iff_inf set_eq_subset Aizerman_onD[OF assms(1)] assms(2))


subsection\<open> The @{emph \<open>law of aggregate demand\<close>} condition aka @{emph \<open>size monotonicity\<close>} \label{sec:cf-lad} \<close>

text\<open>

\citet[{\S}III]{HatfieldMilgrom:2005} impose the @{emph \<open>law of
aggregate demand\<close>} (aka @{emph \<open>size monotonicity\<close>}) to obtain the rural
hospitals theorem (\S\ref{sec:contracts-rh}). It captures the
following intuition:
\begin{quote}

[...] Roughly, this law states that as the price falls, agents should
demand more of a good. Here, price falls correspond to more contracts
being available, and more demand corresponds to taking on (weakly)
more contracts.

\end{quote}

The @{const "card"} function takes a finite set into its cardinality
(as a natural number).

\<close>

definition lad_on :: "'a set \<Rightarrow> 'a::finite cfun \<Rightarrow> bool" where
  "lad_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>C\<subseteq>B. card (f C) \<le> card (f B))"

abbreviation lad :: "'a::finite cfun \<Rightarrow> bool" where
  "lad \<equiv> lad_on UNIV"

text\<open>

This definition is identical amongst
\citet[{\S}III]{HatfieldMilgrom:2005}, \citet[(20)]{Fleiner:2002}, and
\citet[Definition~4]{AygunSonmez:2012-WP2}.

\<close>
(*<*)

lemma lad_onD:
  assumes "lad_on A f"
  assumes "C \<subseteq> B"
  assumes "B \<subseteq> A"
  shows "card (f C) \<le> card (f B)"
using assms unfolding lad_on_def by blast

lemma ladD:
  assumes "lad f"
  assumes "\<And>x. x \<in> C \<Longrightarrow> x \<in> B"
  shows "card (f C) \<le> card (f B)"
using assms unfolding lad_on_def by (simp add: subsetI)

(*>*)
text\<open>

\citet[\S5, Proposition~1]{AygunSonmez:2012-WP2} show that @{const
"substitutes"} and @{const "lad"} imply @{const "irc"}, which
therefore rescues many results in the matching-with-contracts
literature.

\<close>

lemma lad_on_substitutes_on_irc_on:
  assumes "f_range_on A f"
  assumes "substitutes_on A f"
  assumes "lad_on A f"
  shows "irc_on A f"
proof %invisible (rule irc_onI, rule card_seteq)
  fix B b assume bB: "B \<subseteq> A" "b \<in> A" "b \<notin> f (insert b B)"
  show "finite (f B)" by simp
  show "f (insert b B) \<subseteq> f B"
  proof
    fix x assume x: "x \<in> f (insert b B)"
    with \<open>f_range_on A f\<close> bB have "insert x B = B \<or> x = b"
      by clarsimp (blast dest: f_range_onD')
    with \<open>substitutes_on A f\<close> bB x show "x \<in> f B"
      by (metis insert_subset substitutes_onD)
  qed
  from \<open>lad_on A f\<close> bB show "card (f B) \<le> card (f (insert b B))"
    unfolding lad_on_def by (simp add: subset_insertI)
qed

text\<open>

The converse does not hold.

\<close>


subsection\<open> The @{emph \<open>expansion\<close>} condition \<close>

text\<open>

According to \citet[p152]{Moulin:1985}, a choice function satifies
@{emph \<open>expansion\<close>} if an alternative chosen from two sets is also chosen
from their union.

\<close>

definition expansion_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "expansion_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>C\<subseteq>A. f B \<inter> f C \<subseteq> f (B \<union> C))"

abbreviation expansion :: "'a cfun \<Rightarrow> bool" where
  "expansion \<equiv> expansion_on UNIV"

lemmas %invisible expansion_onI = iffD2[OF expansion_on_def, rule_format]
lemmas %invisible expansion_onD = iffD1[OF expansion_on_def, rule_format, THEN subsetD, simplified, unfolded conj_imp_eq_imp_imp]

text\<open>

Condition \<open>\<gamma>\<close> due to \citet{Sen:1971} generalizes
@{const "expansion"} to collections of sets of choices.

\<close>

definition expansion_gamma_on :: "'a set \<Rightarrow> 'a set set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "expansion_gamma_on A As f \<longleftrightarrow> (\<Union>As\<subseteq>A \<and> As \<noteq> {} \<longrightarrow> (\<Inter>A\<in>As. f A) \<subseteq> f (\<Union>As))"

definition expansion_gamma :: "'a set set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "expansion_gamma \<equiv> expansion_gamma_on UNIV"

lemmas %invisible expansion_gamma_onI = iffD2[OF expansion_gamma_on_def, rule_format, unfolded conj_imp_eq_imp_imp]
lemmas %invisible expansion_gamma_onE = iffD1[OF expansion_gamma_on_def, rule_format, THEN subsetD, simplified, unfolded conj_imp_eq_imp_imp]

lemma expansion_gamma_expansion:
  assumes "\<forall>As. expansion_gamma_on A As f"
  shows "expansion_on A f"
proof %invisible (rule expansion_onI, rule subsetI)
  fix B C x
  assume "B \<subseteq> A" "C \<subseteq> A" "x \<in> f B \<inter> f C" then show "x \<in> f (B \<union> C)"
    using expansion_gamma_onE[OF spec[OF assms], where As="{B,C}"] by simp
qed

lemma expansion_expansion_gamma:
  assumes "expansion_on A f"
  assumes "finite As"
  shows "expansion_gamma_on A As f"
proof %invisible (rule expansion_gamma_onI[OF subsetI])
  fix x assume "\<Union>As \<subseteq> A" "As \<noteq> {}" "x \<in> (\<Inter>A\<in>As. f A)"
  from \<open>finite As\<close> this show "x \<in> f (\<Union>As)"
  proof induct
    case (insert b B) with assms show ?case by (cases "B = {}") (auto dest: expansion_onD)
  qed simp
qed

text\<open>

The @{const "expansion"} condition plays a major role in the study of
the @{emph \<open>rationalizability\<close>} of choice functions, which we explore
next.

\<close>


subsection\<open> Axioms of revealed preference \label{sec:cf-revealed_preference} \<close>

text\<open>

We digress from our taxonomy of conditions on choice functions to
discuss @{emph \<open>rationalizability\<close>}. A choice function is
@{emph \<open>rationalizable\<close>} if there exists some binary relation that generates
it, typically by taking the @{emph \<open>greatest\<close>} or @{emph \<open>maximal\<close>} elements
of the given set of alternatives:

\<close>

definition greatest :: "'a rel \<Rightarrow> 'a cfun" where
  "greatest r X = {x\<in>X. \<forall>y\<in>X. (y, x) \<in> r}"

definition maximal :: "'a rel \<Rightarrow> 'a cfun" where
  "maximal r X = {x\<in>X. \<forall>y\<in>X. \<not>(x, y) \<in> r}"

lemma (in MaxR) greatest:
  shows "set_option (MaxR_opt X) = greatest r (X \<inter> Field r)"
using %invisible greatest_is_MaxR_opt MaxR_opt_is_greatest unfolding greatest_def by (blast dest: range_Some)
(*<*)

lemma greatest_r_mono:
  assumes "Above r X \<subseteq> Above r' X"
  shows "greatest r X \<subseteq> greatest r' X"
using assms unfolding greatest_def Above_def by (fast intro: FieldI1)

lemmas greatest_r_mono' = subsetD[OF greatest_r_mono, rotated]

lemma greatest_Above:
  shows "greatest r X = Above r X \<inter> X"
unfolding greatest_def Above_def by (blast intro: FieldI1)

(*>*)
text\<open>

Note that @{const "greatest"} requires the relation to be reflexive
and total, and @{const "maximal"} requires it to be irreflexive, for
the choice functions to ever yield non-empty sets.

This game of uncovering the preference relations (if any) underlying a
choice function goes by the name of @{emph \<open>revealed preference\<close>}. (In
contrast, later we show how these conditions guarantee the existence
of stable many-to-one matches.) See \citet{Moulin:1985} and
\citet{Border:2012} for background, intuition and critique, and
\citet{Sen:1971} for further classical results and proofs.

We adopt the following notion here:

\<close>

definition rationalizes_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "rationalizes_on A f r \<longleftrightarrow> (\<forall>B\<subseteq>A. f B = greatest r B)"

abbreviation rationalizes :: "'a cfun \<Rightarrow> 'a rel \<Rightarrow> bool" where
  "rationalizes \<equiv> rationalizes_on UNIV"

lemma %invisible rationalizes_onI:
  assumes "f_range_on A f"
  assumes "\<And>B x y. \<lbrakk>B \<subseteq> A; x \<in> f B; y \<in> B\<rbrakk> \<Longrightarrow> (y, x) \<in> r"
  assumes "\<And>B x. \<lbrakk>B \<subseteq> A; x \<in> B; \<forall>y\<in>B. (y, x) \<in> r\<rbrakk> \<Longrightarrow> x \<in> f B"
  shows "rationalizes_on A f r"
using assms unfolding rationalizes_on_def greatest_def by (auto dest: f_range_onD)

text\<open>

In words, relation @{term "r"} rationalizes the choice function @{term
"f"} over universe @{term "A"} if @{term "f B"} picks out the @{term
"greatest"} elements of @{term "B \<subseteq> A"} with respect to
@{term "r"}. At this point @{term "r"} can be any relation that does
the job, but soon enough we will ask that it satisfy some familiar
ordering properties.

The analysis begins by determining under what constraints @{term "f"}
can be rationalized, continues by establishing some properties of all
rationalizable choice functions, and concludes by considering what it
takes to establish stronger properties.

Following \citet[\S5, Definition~2]{Border:2012} and
\citet[Definition~2]{Sen:1971}, we can generate the @{emph \<open>revealed
weakly preferred\<close>} relation for the choice function @{term "f"}:

\<close>

definition rwp_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> 'a rel" where
  "rwp_on A f = {(x, y). \<exists>B\<subseteq>A. x \<in> B \<and> y \<in> f B}"

abbreviation rwp :: "'a cfun \<Rightarrow> 'a rel" where
  "rwp \<equiv> rwp_on UNIV"

lemma %invisible rwp_on_Field:
  assumes "f_range_on A f"
  shows "Field (rwp_on A f) \<subseteq> A"
using assms unfolding f_range_on_def rwp_on_def Field_def by auto

lemma rwp_on_refl_on:
  assumes "f_range_on A f"
  assumes "decisive_on A f"
  shows "refl_on A (rwp_on A f)"
proof %invisible (rule refl_onI)
  from \<open>f_range_on A f\<close> show "rwp_on A f \<subseteq> A \<times> A"
    unfolding rwp_on_def f_range_on_def by blast
  fix x assume "x \<in> A"
  with assms show "(x, x) \<in> rwp_on A f"
    unfolding rwp_on_def decisive_on_def f_range_on_def
    by (fast dest: spec[where x="{x}"] intro: exI[where x="{x}"])
qed

text\<open>

In words, if it is ever possible that @{term "x \<in> B"} is available
and @{term "f B"} chooses @{term "y"}, then @{term "y"} is taken to
always be at least as good as @{term "x"}.

The @{emph \<open>V-axiom\<close>} asserts that whatever is revealed to be at least as
good as anything else on offer is chosen:

\<close>

definition V_axiom_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "V_axiom_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>y\<in>B. (\<forall>x \<in> B. (x, y) \<in> rwp_on A f) \<longrightarrow> y \<in> f B)"

abbreviation V_axiom :: "'a cfun \<Rightarrow> bool" where
  "V_axiom \<equiv> V_axiom_on UNIV"

text\<open>

This axiom characterizes rationality; see
\citet[Theorem~7]{Border:2012}. \citet[\S3]{Sen:1971} calls a decisive
choice function that satisfies @{const "V_axiom"} @{emph \<open>normal\<close>}.

\<close>

lemma rationalizes_on_f_range_on_V_axiom_on:
  assumes "rationalizes_on A f r"
  shows "f_range_on A f"
    and "V_axiom_on A f"
using %invisible assms unfolding V_axiom_on_def rationalizes_on_def greatest_def f_range_on_def rwp_on_def by simp_all blast+

lemma f_range_on_V_axiom_on_rationalizes_on:
  assumes "f_range_on A f"
  assumes "V_axiom_on A f"
  shows "rationalizes_on A f (rwp_on A f)"
using %invisible assms rwp_on_Field[OF assms(1)]
unfolding V_axiom_on_def rationalizes_on_def greatest_def f_range_on_def rwp_on_def
by auto

theorem V_axiom_on_rationalizes_on:
  shows "(f_range_on A f \<and> V_axiom_on A f) \<longleftrightarrow> (\<exists>r. rationalizes_on A f r)"
using %invisible rationalizes_on_f_range_on_V_axiom_on f_range_on_V_axiom_on_rationalizes_on by blast

text\<open>

We could also ask that @{term "f"} be determined directly by how it
behaves on pairs (\citet{Sen:1971}, \citet[p151]{Moulin:1985}), which
turns out to be equivalent:

\<close>

definition rationalizable_binary_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "rationalizable_binary_on A f \<longleftrightarrow> (\<forall>B\<subseteq>A. f B = {y \<in> B. \<forall>x\<in>B. y \<in> f {x, y}})"

abbreviation rationalizable_binary :: "'a cfun \<Rightarrow> bool" where
  "rationalizable_binary \<equiv> rationalizable_binary_on UNIV"

lemma %invisible rationalizable_binary_onI:
  assumes "f_range_on A f"
  assumes "\<And>B x y. \<lbrakk>B \<subseteq> A; y \<in> f B; x \<in> B; y \<in> B\<rbrakk> \<Longrightarrow> y \<in> f {x, y}"
  assumes "\<And>B y. \<lbrakk>B \<subseteq> A; y \<in> B; \<forall>x\<in>B. y \<in> f {x, y}\<rbrakk> \<Longrightarrow> y \<in> f B"
  shows "rationalizable_binary_on A f"
unfolding rationalizable_binary_on_def using assms by (blast dest: f_range_onD' intro: FieldI1)

theorem V_axiom_realizable_binary:
  assumes "f_range_on A f"
  shows "V_axiom_on A f \<longleftrightarrow> rationalizable_binary_on A f"
(*<*)
(is "?lhs = ?rhs")
proof (rule iffI)
  assume lhs: ?lhs show ?rhs
  proof(rule rationalizable_binary_onI[OF assms])
    fix B x y assume "B \<subseteq> A" "y \<in> f B" "x \<in> B" "y \<in> B"
    with lhs show "y \<in> f {x, y}"
      unfolding V_axiom_on_def rwp_on_def by (auto dest: spec[where x="{x, y}"])
  next
    fix B y assume "B \<subseteq> A" "y \<in> B" "\<forall>x\<in>B. y \<in> f {x, y}"
    with lhs show "y \<in> f B"
      unfolding V_axiom_on_def rwp_on_def
      by clarsimp (metis Un_subset_iff insertI1 insert_is_Un mk_disjoint_insert)
  qed
next
  assume ?rhs then show ?lhs
    unfolding V_axiom_on_def rwp_on_def rationalizable_binary_on_def by force
qed

(*>*)
text\<open>

All rationalizable choice functions satisfy @{const "iia"} and @{const
"expansion"} (\citet{Sen:1971}, \citet[p152]{Moulin:1985}).

\<close>

lemma rationalizable_binary_on_iia_on:
  assumes "f_range_on A f"
  assumes "rationalizable_binary_on A f"
  shows "iia_on A f"
using %invisible assms unfolding iia_on_def rationalizable_binary_on_def f_range_on_def
by simp (meson contra_subsetD)

lemma rationalizable_binary_on_expansion_on:
  assumes "f_range_on A f"
  assumes "rationalizable_binary_on A f"
  shows "expansion_on A f"
using  %invisible assms unfolding rationalizable_binary_on_def f_range_on_def
by - (rule expansion_onI; auto)

text\<open>

The converse requires the set of alternatives to be finite, and
moreover fails if the choice function is not @{const "decisive"}.

\<close>

lemma rationalizable_binary_on_converse:
  fixes f :: "'a::finite cfun"
  assumes "f_range_on A f"
  assumes "decisive_on A f"
  assumes "iia_on A f"
  assumes "expansion_on A f"
  shows "rationalizable_binary_on A f"
proof %invisible (rule rationalizable_binary_onI[OF assms(1)])
  fix B x y
  assume "B \<subseteq> A" "y \<in> f B" "x \<in> B" "y \<in> B" with \<open>iia_on A f\<close> show "y \<in> f {x, y}"
    unfolding iia_on_def by fastforce
next
  fix B y
  assume XXX: "y \<in> B" and YYY: "\<forall>x\<in>B. y \<in> f {x, y}" "B \<subseteq> A"
  have "y \<in> f (insert y C)" if "C \<subseteq> B" for C
  using finite[of C] that XXX YYY
  proof induct
    case empty with \<open>decisive_on A f\<close> show ?case
      unfolding decisive_on_def by force
  next
    case (insert b C) with \<open>expansion_on A f\<close> show ?case
      by (force dest!: expansion_onD[where C="{b, y}" and B="insert y C"] simp: insert_commute)
  qed
  note this[OF subset_refl]
  with XXX show "y \<in> f B" by (simp add: insert_absorb)
qed

text\<open>

That settles the issue of existence, but it is not clear that the
relation is really ``rational'' (for instance, @{term "rwp_on A f"}
need not be transitive). Therefore the analysis continues by further
constraining the choice function so that it is rationalized by
familiar ordering relations.

For instance, the following shows that the @{emph \<open>axioms of revealed
preference\<close>} are rationalized by total preorders \citep[Definitions~8
and~13]{Sen:1971}\footnote{For \citet[p9]{Sen:1970}, an ordering is
complete (total), reflexive, and transitive. Alternative names are:
complete pre-ordering, complete quasi-ordering, and weak
ordering.}. These are alo equivalent to some congruence axioms due to
Samuelson \citep{Border:2012}.

We define @{term "x"} to be @{emph \<open>strictly revealed-preferred to\<close>}
@{term "y"} if there is a situation where both are on offer and only
@{term "y"} is chosen:

\<close>

definition rsp_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> 'a rel" where \<comment> \<open>\citep[Definition~8]{Sen:1971}\<close>
  "rsp_on A f = {(x, y). \<exists>B\<subseteq>A. x \<in> Rf f B \<and> y \<in> f B}"

abbreviation rsp :: "'a cfun \<Rightarrow> 'a rel" where
  "rsp \<equiv> rsp_on UNIV"

text\<open>

This relation is typically denoted by @{term "P"}, for strict
preference. The not-worse-than relation @{term "R"} is recovered by:

\<close>

definition rspR_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> 'a rel" where \<comment> \<open>\citep[Definition~9]{Sen:1971}\<close>
  "rspR_on A f = {(x, y). {x, y} \<subseteq> A \<and> (y, x) \<notin> rsp_on A f}"

abbreviation rspR :: "'a cfun \<Rightarrow> 'a rel" where
  "rspR \<equiv> rspR_on UNIV"

lemma %invisible rsp_on_range:
  assumes "f_range_on A f"
  shows "rsp_on A f \<subseteq> A \<times> A"
using assms unfolding rsp_on_def f_range_on_def by blast

text\<open>

\citet[p309]{Sen:1971} defines the @{emph \<open>weak axiom of revealed
preference\<close>} (WARP) as follows:

\<close>

definition warp_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "warp_on A f \<longleftrightarrow> (\<forall>(x, y)\<in>rsp_on A f. (y, x) \<notin> rwp_on A f)"

abbreviation warp :: "'a cfun \<Rightarrow> bool" where
  "warp \<equiv> warp_on UNIV"

text\<open>

The @{emph \<open>strong axiom of revealed preference\<close>} (SARP) is essentially
the transitive closure of @{const "warp"} \citep[p309]{Sen:1971}:

\<close>

definition sarp_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "sarp_on A f \<longleftrightarrow> (\<forall>(x, y)\<in>(rsp_on A f)\<^sup>+. (y, x) \<notin> rwp_on A f)"

abbreviation sarp :: "'a cfun \<Rightarrow> bool" where
  "sarp \<equiv> sarp_on UNIV"

lemma %invisible sarp_onI:
  assumes "\<And>x y. (x, y) \<in> (rsp_on A f)\<^sup>+ \<Longrightarrow> (y, x) \<notin> rwp_on A f"
  shows "sarp_on A f"
using assms unfolding sarp_on_def by blast

lemma sarp_on_warp_on: \<comment> \<open>\citet[T.3 part]{Sen:1970}\<close>
  assumes "sarp_on A f"
  shows "warp_on A f"
using %invisible assms unfolding sarp_on_def warp_on_def rwp_on_def rsp_on_def by blast

lemma rsp_on_irrefl:
  "A \<noteq> {} \<Longrightarrow> irrefl (rsp_on A f)"
unfolding %invisible rsp_on_def irrefl_def by fastforce

text\<open>

For decisive choice functions, @{const "warp"} implies @{const
"sarp"}. We show this following \citet{Sen:1971}, via the @{emph \<open>weak
congruence axiom\<close>} (WCA): if @{term "f"} chooses @{term "x"} from some
set @{term "B"} and @{term "y"} is revealed to be weakly preferred,
then @{term "f"} must choose @{term "y"} from @{term "B"} as well.

\<close>

definition wca_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "wca_on A f \<longleftrightarrow> (\<forall>(x, y)\<in>rwp_on A f. \<forall>B\<subseteq>A. x \<in> f B \<and> y \<in> B \<longrightarrow> y \<in> f B)"

abbreviation wca :: "'a cfun \<Rightarrow> bool" where
  "wca \<equiv> wca_on UNIV"

lemma %invisible wca_onI:
  assumes "\<And>B x y. \<lbrakk> B \<subseteq> A; (x, y) \<in> rwp_on A f; x \<in> f B; y \<in> B \<rbrakk> \<Longrightarrow> y \<in> f B"
  shows "wca_on A f"
unfolding wca_on_def using assms by blast

text\<open>

Decisive choice functions that satisfy @{const "wca"} are rationalized
by total preorders, in particular @{const "rwp"}, and the converse
obtains if they are normal.

\<close>

lemma wca_on_V_axiom_on:
  assumes "wca_on A f"
  assumes "f_range_on A f"
  assumes "decisive_on A f"
  shows "V_axiom_on A f"
using %invisible assms unfolding V_axiom_on_def wca_on_def rwp_on_def
by clarsimp (metis (mono_tags) ex_in_conv f_range_onD'[where A=A and f=f] decisive_onD[where A=A and f=f])

lemma wca_on_total_on:
  assumes "wca_on A f"
  assumes "f_range_on A f"
  assumes "decisive_on A f"
  shows "total_on A (rwp_on A f)"
proof %invisible(rule total_onI)
 fix x y
 assume "x \<in> A" "y \<in> A" "x \<noteq> y"
 with assms show "(x, y) \<in> rwp_on A f \<or> (y, x) \<in> rwp_on A f"
  unfolding wca_on_def decisive_on_def rwp_on_def total_on_def f_range_on_def
  by (fast dest: spec[where x="{x,y}"] intro: exI[where x="{x,y}"])
qed

lemma rwp_on_trans:
  assumes "wca_on A f"
  assumes "f_range_on A f"
  assumes "decisive_on A f"
  shows "trans (rwp_on A f)"
proof %invisible (rule transI)
  fix x y z assume "(x, y) \<in> rwp_on A f" "(y, z) \<in> rwp_on A f"
  then obtain B C where "B \<union> C \<subseteq> A" "x \<in> B" "y \<in> f B" "y \<in> C" "z \<in> f C"
    unfolding rwp_on_def by blast
  from \<open>x \<in> B\<close> have "x \<in> B \<union> C" by blast
  moreover
  have "z \<in> f (B \<union> C)"
  proof(cases "y \<in> f (B \<union> C)")
    case True
    with \<open>wca_on A f\<close> \<open>f_range_on A f\<close> \<open>y \<in> C\<close> \<open>z \<in> f C\<close> \<open>B \<union> C \<subseteq> A\<close>
    show ?thesis
      unfolding wca_on_def rwp_on_def
      by simp (meson \<open>B \<union> C \<subseteq> A\<close> f_range_onD' inf_sup_ord(4) subsetCE)
  next
    case False
    with assms \<open>B \<union> C \<subseteq> A\<close> \<open>y \<in> f B\<close> \<open>z \<in> f C\<close>
    obtain w where "w \<in> f (B \<union> C) \<and> w \<in> C"
      unfolding wca_on_def decisive_on_def rwp_on_def
      by (clarsimp simp: ex_in_conv[symmetric] dest!: spec[where x="B \<union> C"])
         (metis Un_iff \<open>B \<union> C \<subseteq> A\<close> f_range_onD')
    with \<open>wca_on A f\<close> \<open>f_range_on A f\<close> \<open>B \<union> C \<subseteq> A\<close> \<open>z \<in> f C\<close> show ?thesis
      unfolding wca_on_def rwp_on_def
      by simp (meson \<open>B \<union> C \<subseteq> A\<close> f_range_onD' inf_sup_ord(4) subsetCE)
  qed
  moreover note \<open>B \<union> C \<subseteq> A\<close>
  ultimately show "(x, z) \<in> rwp_on A f" unfolding rwp_on_def by blast
qed

lemma wca_on_V_axiom_on_preorder_on: \<comment> \<open>\citet[T.1, T.3 part]{Sen:1970}\<close>
  assumes "f_range_on A f"
  assumes "decisive_on A f"
  shows "wca_on A f \<longleftrightarrow> V_axiom_on A f \<and> preorder_on A (rwp_on A f) \<and> total_on A (rwp_on A f)"
(*<*)
(is "?lhs \<longleftrightarrow> ?rhs")
proof(rule iffI)
  assume ?lhs with rwp_on_refl_on rwp_on_trans wca_on_V_axiom_on wca_on_total_on assms show ?rhs
    unfolding preorder_on_def by blast
next
  assume rhs: ?rhs
  show ?lhs
  proof(rule wca_onI)
    fix B x y assume "B \<subseteq> A" "(x, y) \<in> rwp_on A f" "x \<in> f B" "y \<in> B"
    from \<open>B \<subseteq> A\<close> \<open>x \<in> f B\<close> have "\<forall>z\<in>B. (z, x) \<in> rwp_on A f"
      unfolding rwp_on_def by blast
    with rhs \<open>(x, y) \<in> rwp_on A f\<close> have "\<forall>z\<in>B. (z, y) \<in> rwp_on A f"
      unfolding preorder_on_def by (blast elim: transE)
    with rhs \<open>B \<subseteq> A\<close> \<open>y \<in> B\<close> show "y \<in> f B"
      unfolding V_axiom_on_def by blast
  qed
qed

(*>*)
text\<open>\<close>

lemma wca_on_rwp_on_rspR_on: \<comment> \<open>\citet[T.2]{Sen:1970}\<close>
  assumes "wca_on A f"
  assumes "f_range_on A f"
  assumes "decisive_on A f"
  shows "rwp_on A f = rspR_on A f"
(*<*)
(is "?lhs = ?rhs")
proof(rule set_elem_equalityI)
  fix x assume "x \<in> ?lhs"
  with \<open>wca_on A f\<close> rwp_on_refl_on[OF assms(2,3)] show "x \<in> ?rhs"
    unfolding wca_on_def rsp_on_def rspR_on_def by (force dest: refl_onD1 refl_onD2)
next
  fix x assume "x \<in> ?rhs"
  with assms show "x \<in> ?lhs"
    unfolding wca_on_def rsp_on_def rspR_on_def rwp_on_def decisive_on_def
    by (auto 3 0 simp: split_def
               intro!: exI[where x="{fst x, snd x}"]
                dest!: spec[where x="{fst x, snd x}"]
                 dest: f_range_onD')
qed
(*>*)
text\<open>\<close>

lemma rwp_on_rspR_on_wca_on: \<comment> \<open>\citet[T.2]{Sen:1970}\<close>
  assumes "rwp_on A f = rspR_on A f"
  shows "wca_on A f"
using %invisible assms unfolding wca_on_def rsp_on_def rspR_on_def by blast

lemma wca_on_warp_on: \<comment> \<open>\citet[T.3 part]{Sen:1970}\<close>
  shows "wca_on A f \<longleftrightarrow> warp_on A f"
unfolding %invisible warp_on_def wca_on_def rsp_on_def rwp_on_def by blast

lemma warp_on_sarp_on: \<comment> \<open>\citet[T.3 part]{Sen:1970}\<close>
  assumes "warp_on A f"
  assumes "f_range_on A f"
  assumes "decisive_on A f"
  shows "sarp_on A f"
proof(rule sarp_onI)
  from \<open>warp_on A f\<close> have "wca_on A f" unfolding wca_on_warp_on .
  then have XXX: "rwp_on A f = rspR_on A f"
        and YYY: "preorder_on A (rspR_on A f)"
        and ZZZ: "total_on A (rspR_on A f)"
    using %invisible wca_on_rwp_on_rspR_on[OF _ assms(2,3)] wca_on_V_axiom_on_preorder_on[OF assms(2,3)] wca_on_total_on[OF _ assms(2,3)] by fastforce+
  fix a b assume "(a, b) \<in> (rsp_on A f)\<^sup>+"
  then have "{a, b} \<subseteq> A" and "(b, a) \<notin> rspR_on A f"
  proof(induct a b)
    case (r_into_trancl a b)
    { case 1 from r_into_trancl rsp_on_range[OF assms(2)] show ?case by blast }
    { case 2 from r_into_trancl show ?case by (simp add: rspR_on_def) }
  next
    case (trancl_into_trancl a b c)
    { case 1 from trancl_into_trancl rsp_on_range[OF assms(2)] show ?case by blast }
    { case 2 from trancl_into_trancl rsp_on_range[OF assms(2)] YYY ZZZ show ?case
        unfolding total_on_def preorder_on_def
        by clarsimp (metis (no_types, lifting) case_prodD mem_Collect_eq rspR_on_def transD) }
  qed
  with XXX show "(b, a) \<notin> rwp_on A f" by simp
qed

text\<open>

The @{const "decisive"} constraint here is necessary: consider a
Condorcet cycle over @{term "{x, y, z}"}: forcing @{term "f {x, y,
z}"} to be non-empty resolves this.

\citet{Sen:1971} proves that these and other conditions on choice
functions are equivalent (under the @{const "decisive"} hypothesis).

\<close>


subsubsection\<open> The @{emph \<open>strong axiom of revealed preference\<close>} ala \citet{AygunSonmez:2012-WP2} \<close>

text\<open>

\citet[\S6]{AygunSonmez:2012-WP2} adopt a different definition for a
@{emph \<open>strong axiom of revealed preference\<close>} and show that it holds for
all choice functions that satisfy @{const "iia"} and @{const
"consistency"}.

\<close>

abbreviation nth_mod :: "'a list \<Rightarrow> nat \<Rightarrow> 'a" (infixl "!%" 100) where
  "xs !% i \<equiv> xs ! (i mod length xs)"

definition mwc_sarp :: "'a cfun \<Rightarrow> bool" where
  "mwc_sarp f \<longleftrightarrow>
    \<not>(\<exists>Xs. length Xs > 1 \<and> distinct (map f Xs) \<and> (\<forall>i. f (Xs!%i) \<subset> Xs!%i \<inter> Xs!%(i+1)))"

lemma %invisible mwc_sarpI:
  assumes "\<And>Xs. \<lbrakk>length Xs > 1; distinct (map f Xs); \<forall>i. f (Xs!%i) \<subset> Xs!%i \<inter> Xs!%(i+1)\<rbrakk> \<Longrightarrow> False"
  shows "mwc_sarp f"
unfolding mwc_sarp_def using assms by blast

lemma iia_consistency_mwc_sarp:
  assumes "f_range f"
  assumes "iia f" \<comment> \<open>@{const "substitutes"}\<close>
  assumes "consistency f" \<comment> \<open>@{const "irc"}\<close>
  shows "mwc_sarp f"
proof(rule mwc_sarpI)
  fix Xs
  assume LLL: "length Xs > 1"
     and EEE: "distinct (map f Xs)"
     and AAA: "\<forall>i. f (Xs!%i) \<subset> Xs!%i \<inter> Xs!%(i+1)"
  have 6: "f (\<Union>(set Xs)) \<subseteq> (\<Inter>X\<in>set Xs. f X)"
  proof -
    have 4: "x \<notin> f (\<Union>(set Xs))" if "x \<in> \<Union>(set Xs) - (\<Union>X\<in>set Xs. f X)" for x
      using that \<open>iia f\<close> unfolding iia_on_def by simp blast
    have 5: "x \<notin> f (\<Union>(set Xs))" if "x \<in> (\<Union>X\<in>set Xs. f X) - (\<Inter>X\<in>set Xs. f X)" for x
    proof -
      from that obtain j k where "x \<in> f (Xs ! j)" "x \<notin> f (Xs ! k)" "j < length Xs" "k < length Xs"
        by (clarsimp simp: in_set_conv_nth)
      with AAA LLL ex_least_nat_le[where n="k + length Xs - j" and P="\<lambda>i. x \<notin> f (Xs !% (i + j))"]
      obtain i where "x \<in> f (Xs !% i) - f (Xs !% (i+1))"
        by %invisible auto (metis One_nat_def add_eq_if diff_diff_cancel diff_is_0_eq' lessI mod_less nat_le_linear zero_less_diff)
      with AAA have "x \<in> Rf f (Xs!%(i+1))" by auto
      with LLL show "x \<notin> f (\<Union>(set Xs))"
        using \<open>iia f\<close> unfolding iia_on_def by clarsimp (meson Suc_lessD Sup_upper mod_less_divisor nth_mem)
    qed
    from 4 5 have "x \<notin> f (\<Union>(set Xs))" if "x \<in> (\<Union>(set Xs)) - (\<Inter>X\<in>set Xs. f X)" for x
      using that by blast
    with \<open>f_range f\<close> show ?thesis by (blast dest: f_range_onD)
  qed
  moreover have "\<forall>i. (\<Inter>X\<in>set Xs. f X) \<subset> f (Xs!%i)"
  proof -
    from \<open>f_range f\<close> LLL have "\<Inter>(f ` set Xs) \<subseteq> Xs ! 1"
      using nth_mem f_range_onD by fastforce
    with \<open>consistency f\<close> LLL 6 have f4: "f (\<Union>(set Xs)) = f (Xs ! 1)"
      by - (rule consistencyD[where f=f], force+)
    with \<open>f_range f\<close> LLL 6 have "f (Xs ! 1) \<subseteq> Xs ! 0"
      using f_range_onD by (metis INT_lower One_nat_def Suc_lessD subset_trans nth_mem top.extremum)
    with \<open>consistency f\<close> EEE LLL f4 show ?thesis
      by (metis One_nat_def Suc_lessD Sup_upper consistencyD length_map nth_eq_iff_index_eq nth_map nth_mem zero_neq_one)
  qed
  moreover have "\<forall>i. f (Xs!%i) = f (\<Union>(set Xs))"
  proof -
    from AAA have "\<forall>i. f (Xs!%i) \<subseteq> Xs!%i" by auto
    moreover from LLL have "\<forall>i. Xs!%i \<subseteq> \<Union>(set Xs)"
      by (metis One_nat_def Suc_lessD Sup_upper mod_less_divisor nth_mem)
    moreover note 6 \<open>\<forall>i. (\<Inter>X\<in>set Xs. f X) \<subset> f (Xs !% i)\<close>
    ultimately show "\<forall>i. f (Xs!%i) = f (\<Union>(set Xs))"
      by - (clarsimp; rule consistencyD[OF \<open>consistency f\<close>, symmetric]; meson dual_order.trans psubsetE)
  qed
  ultimately show False by force
qed


subsection\<open> Choice functions arising from linear orders \label{sec:cf-linear} \<close>

text\<open>

An obvious way to construct a choice function is to derive one from a
linear order, i.e., a list of strict preferences. We allow such
rankings to omit some alternatives, which means the resulting function
is not decisive.

We work with a finite universe here.

\<close>

locale linear_cf =
  fixes r :: "'a::finite rel"
  fixes linear_cf :: "'a cfun"
  assumes r_linear: "Linear_order r"
  assumes linear_cf_def: "linear_cf X \<equiv> set_option (MaxR.MaxR_opt r X)"
begin

interpretation MaxR: MaxR r by unfold_locales (rule r_linear)

(*<*)

lemmas maxR_code = MaxR.maxR_def
lemmas MaxR_f_code = MaxR.MaxR_f_def
lemma code:
  shows "linear_cf (set X) = set_option (fold MaxR.MaxR_f X None)"
unfolding linear_cf_def using MaxR.MaxR_opt_code by simp

lemma simps [nitpick_simp]:
  shows "linear_cf {} = {}"
        "linear_cf (insert x X) = (if x \<in> Field r then if linear_cf X = {} then {x} else {MaxR.maxR x y |y. y \<in> linear_cf X} else linear_cf X)"
unfolding linear_cf_def by (simp_all add: MaxR.insert split: option.splits)

(*>*)

lemma range:
  shows "linear_cf X \<subseteq> X \<inter> Field r"
unfolding %invisible linear_cf_def using MaxR.range[of X] finite[of X] by fastforce

lemmas range' = rev_subsetD[OF _ range, of x] for x

lemma singleton:
  shows "x \<in> linear_cf X \<longleftrightarrow> linear_cf X = {x}"
unfolding %invisible linear_cf_def by fastforce

lemma subset:
  assumes "linear_cf Y \<subseteq> X"
  assumes "X \<subseteq> Y"
  shows "linear_cf Y = linear_cf X"
using %invisible assms MaxR.subset unfolding linear_cf_def by simp

lemma union:
  shows "linear_cf (X \<union> Y) = (if linear_cf X = {} then linear_cf Y else if linear_cf Y = {} then linear_cf X else {MaxR.maxR x y |x y. x \<in> linear_cf X \<and> y \<in> linear_cf Y})"
unfolding %invisible linear_cf_def by (auto simp: MaxR.union)

lemma mono:
  assumes "x \<in> linear_cf X"
  shows "\<exists>y \<in> linear_cf (X \<union> Y). (x, y) \<in> r"
using %invisible MaxR.mono assms unfolding linear_cf_def by (metis elem_set)

lemmas greatest = MaxR.greatest[folded linear_cf_def]

lemma preferred:
  assumes "(x, y) \<in> r"
  assumes "x \<in> linear_cf X"
  assumes "y \<in> X"
  shows "y = x"
using %invisible assms FieldI2 MaxR.MaxR_opt_is_greatest MaxR.maxR_absorb1 maxR_code unfolding linear_cf_def by fastforce

lemma card_le:
  shows "card (linear_cf X) \<le> 1"
unfolding %invisible linear_cf_def by (cases "MaxR.MaxR_opt X") simp_all

lemma card:
  shows "card (linear_cf X) = (if X \<inter> Field r = {} then 0 else 1)"
unfolding %invisible linear_cf_def by (cases "MaxR.MaxR_opt X") (auto dest: MaxR.range_None MaxR.range_Some)

lemma f_range:
  shows "f_range_on X linear_cf"
unfolding %invisible f_range_on_def using range by blast

lemma domain:
  shows "linear_cf (X \<inter> Field r) = linear_cf X"
by %invisible (metis inf.cobounded1 range subset)

lemma decisive_on:
  shows "decisive_on (Field r) linear_cf"
unfolding %invisible decisive_on_def linear_cf_def
by (metis Int_absorb2 empty_subsetI MaxR.range_None MaxR.empty MaxR.subset)

lemma resolute_on:
  shows "resolute_on (Field r) linear_cf"
unfolding %invisible resolute_on_def linear_cf_def using mk_disjoint_insert by (force simp: MaxR.insert)

lemma Rf_mono_on:
  shows "mono_on X (Rf linear_cf)"
by %invisible (rule mono_onI) (clarsimp; metis contra_subsetD empty_subsetI insert_subset singleton subset)

lemmas iia = iffD1[OF Rf_mono_on_iia_on Rf_mono_on]

lemma Chernoff:
  shows "Chernoff_on X linear_cf"
using %invisible Rf_mono_on range Rf_mono_on_iia_on[of X linear_cf, symmetric] Chernoff_on_iia_on by blast

lemma irc:
  shows "irc_on X linear_cf"
unfolding %invisible irc_on_def linear_cf_def
by (clarsimp simp: MaxR.insert dest!: MaxR.maxR_rangeD split: option.splits)

lemma consistency:
  shows "consistency_on X linear_cf"
using %invisible irc by (rule irc_on_consistency_on) simp

lemma lad:
  shows "lad_on X linear_cf"
unfolding %invisible lad_on_def by (cases "X \<inter> Field r = {}") (auto simp: card)

end


subsection\<open> Plott's @{emph \<open>path independence\<close>} condition \label{sec:cf-path-independence}\<close>

text\<open>

As recognised by \citet[\S4]{Fleiner:2002} and
\citet{ChambersYenmez:2013} in the context of matching with contracts,
the @{const "irc"} and @{const "substitutes"} conditions together are
equivalent to @{emph \<open>path independence\<close>}, a condition introduced to the
social choice setting by
\citet{Plott:1973}. \citet[Lemma~6]{Moulin:1985} ascribes this
equivalence result to \citet{AizermanMalishevski:1981}.

\<close>

definition path_independent_on :: "'a set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "path_independent_on A f \<longleftrightarrow> (\<forall>B C. B \<subseteq> A \<and> C \<subseteq> A \<longrightarrow> f (B \<union> C) = f (B \<union> f C))"

abbreviation path_independent :: "'a cfun \<Rightarrow> bool" where
  "path_independent \<equiv> path_independent_on UNIV"

(*<*)

lemmas path_independent_onI = iffD2[OF path_independent_on_def, rule_format]
lemmas path_independent_onD = iffD1[OF path_independent_on_def, rule_format, unfolded conj_imp_eq_imp_imp]
lemmas path_independent_def = path_independent_on_def[where A=UNIV, simplified]

(*>*)
text\<open>

Intuitively a choice function satisfying this condition ignores the
order in which choices are made in the following sense:

\<close>

lemma path_independent_on_symmetric:
  assumes "f_range_on A f"
  shows "path_independent_on A f \<longleftrightarrow> (\<forall>B C. B \<subseteq> A \<and> C \<subseteq> A \<longrightarrow> f (B \<union> C) = f (f B \<union> f C))"
using %invisible assms unfolding path_independent_on_def f_range_on_def
by - (rule iffI, metis subset_trans Un_commute, metis (full_types) Un_subset_iff empty_subsetI sup.orderE Un_commute)

lemmas %invisible path_independent_on_symmetricI = iffD2[OF path_independent_on_symmetric, rule_format, unfolded conj_imp_eq_imp_imp]
lemmas %invisible path_independent_on_symmetricD = iffD1[OF path_independent_on_symmetric, rule_format, unfolded conj_imp_eq_imp_imp]

lemma path_independent_on_Chernoff_on:
  assumes "path_independent_on A f"
  assumes "f_range_on A f"
  shows "Chernoff_on A f"
proof %invisible (rule Chernoff_onI[OF subsetI])
  fix B C x assume XXX: "B \<subseteq> A" "C \<subseteq> B" "x \<in> f B \<inter> C"
  from \<open>f_range_on A f\<close> XXX have "f C \<subseteq> B" by - (erule subset_trans[OF f_range_onD], simp_all)
  with \<open>f_range_on A f\<close> XXX have YYY: "f (B - C \<union> f C) \<subseteq> B - C \<union> f C" by (fastforce elim!: f_range_onD)
  from XXX YYY path_independent_onD[OF \<open>path_independent_on A f\<close>, where B="B - C" and C="C"] \<open>f_range_on A f\<close>
  show "x \<in> f C"
    unfolding f_range_on_def by (auto simp: Un_absorb2)
qed

lemma path_independent_on_consistency_on:
  assumes "path_independent_on A f"
  shows "consistency_on A f"
using %invisible assms unfolding path_independent_on_def
by - (rule consistency_onI; metis Un_subset_iff le_iff_sup sup_commute)

lemma Chernoff_on_consistency_on_path_independent_on:
  assumes "f_range_on A f"
  shows "Chernoff_on A f \<and> consistency_on A f \<longleftrightarrow> path_independent_on A f"
(*<*)
(is "?lhs \<longleftrightarrow> ?rhs")
proof %invisible (rule iffI)
  assume LHS: ?lhs show ?rhs
  proof(rule path_independent_on_symmetricI[OF assms])
    fix B C assume BC: "B \<subseteq> A" "C \<subseteq> A"
    with LHS assms show "f (B \<union> C) = f (f B \<union> f C)"
      by - (rule consistency_onD[where A=A and f=f, OF _ _ _ Chernoff_on_union[OF _ assms]];
            blast dest: f_range_onD)
  qed
next
  assume ?rhs with assms path_independent_on_Chernoff_on path_independent_on_consistency_on
  show ?lhs by blast
qed

lemmas path_independent_onI2 =
  iffD1[OF Chernoff_on_consistency_on_path_independent_on, unfolded conj_imp_eq_imp_imp]

(*>*)
text\<open>\<close>

lemma (in linear_cf) path_independent:
  shows "path_independent linear_cf"
using %invisible f_range Chernoff consistency by (blast intro: path_independent_onI2)


subsubsection\<open> Path independence and decomposition into orderings \label{sec:cf-path-independence-orderings} \<close>

text\<open>

We now show that a choice function over a finite universe satisfying
@{const "path_independent"} is characterized by taking the maximum
elements of some finite set of orderings.

\citet[Definition~12]{Moulin:1985} says that a choice function is
@{emph \<open>pseudo-rationalized\<close>} by the orderings @{term "Rs"} if @{term
"f"} chooses all of the @{term "greatest r"} elements of @{term "B"}
for each @{term "r \<in> Rs"}:

\<close>

definition pseudo_rationalizable_on :: "'a::finite set \<Rightarrow> 'a rel set \<Rightarrow> 'a cfun \<Rightarrow> bool" where
  "pseudo_rationalizable_on A Rs f
     \<longleftrightarrow> (\<forall>r\<in>Rs. Linear_order r) \<and> (\<forall>B\<subseteq>A. f B = (\<Union>r\<in>Rs. greatest r (B \<inter> Field r)))"

lemma pseudo_rationalizable_on_def2:
  "pseudo_rationalizable_on A Rs f
     \<longleftrightarrow> (\<forall>r\<in>Rs. Linear_order r) \<and> (\<forall>B\<subseteq>A. f B = (\<Union>r\<in>Rs. set_option (MaxR.MaxR_opt r B)))"
unfolding %invisible pseudo_rationalizable_on_def
by (metis (no_types, lifting) MaxR.greatest MaxR.intro SUP_cong)

lemmas %invisible pseudo_rationalizable_onI = iffD2[OF pseudo_rationalizable_on_def2, unfolded conj_imp_eq_imp_imp, rule_format]

text\<open>

We deviate from \citeauthor{Moulin:1985} in using non-total linear
orders, where his are total, asymmetric, and transitive; in other
words, strict total linear orders. This allows us to treat
non-decisive choice functions, and we later show that the choice
function is decisive iff the orders are total.

\citet[Theorem~5]{Moulin:1985} assumes @{const "Aizerman"} and @{const
"Chernoff"}, which are equivalent to @{const "path_independent"}.

\<close>

lemma Aizerman_on_Chernoff_on_path_independent_on:
  assumes "f_range_on A f"
  shows "Aizerman_on A f \<and> Chernoff_on A f \<longleftrightarrow> path_independent_on A f"
using %invisible Chernoff_on_consistency_on_path_independent_on[OF assms] consistency_on_Aizerman_on Aizerman_on_idem_on_consistency_on iia_f_idem[OF assms] Chernoff_on_iia_on
by blast

text\<open>

It is straightforward to show that pseudo-rationalizable choice
functions satisfy @{const "path_independent"} using the properties of
@{const "MaxR.MaxR_opt"}:

\<close>

lemma pseudo_rationalizable_on_path_independent_on:
  assumes "pseudo_rationalizable_on A Rs f"
  shows "path_independent_on A f"
proof %invisible (rule path_independent_onI2)
  from assms show "f_range_on A f"
    unfolding f_range_on_def pseudo_rationalizable_on_def2
    using MaxR.range_Some[unfolded MaxR_def] by fastforce
  from assms show "Chernoff_on A f"
    unfolding pseudo_rationalizable_on_def2
    by - (rule Chernoff_onI; clarsimp; metis MaxR.intro MaxR.subset empty_subsetI insert_subset option.simps(15))
  from assms show "consistency_on A f"
    unfolding pseudo_rationalizable_on_def2
    by - (rule consistency_onI; simp; metis (no_types, lifting) MaxR.intro MaxR.subset SUP_cong SUP_le_iff)
qed

text\<open>

The converse requires that we construct a suitable set of orderings
that rationalize @{term "f C"} for each @{term "C \<subseteq> A"}. We
do this by finding a set @{term "B \<subseteq> A"} where @{term "f B
\<subseteq> C"} by successively removing elements in @{term "f A - f
C"}. (As these elements are chosen by @{term "f"} from supersets of
@{term "B"}, we rank these above all of those in @{term "f B"}.)  By
@{const "consistency"} (\S\ref{sec:cf-irc}), @{term "f C = f B"}. We
generate one order for each element of @{term "f C"}. Some extra care
takes care of @{const "decisive"} choice functions.

Termination is guaranteed by the finiteness of @{term "A"} and the
@{const "f_range_on"} hypothesis.

\<close>

context
  fixes A :: "'a::finite set"
  fixes f :: "'a cfun"
  notes conj_cong[fundef_cong]
begin

function (domintros) mk_linear_orders :: "'a set \<Rightarrow> 'a set \<Rightarrow> 'a list set" where
  "mk_linear_orders C B =
   (if f B = {} then {[]}
    else if f B \<subseteq> C
         then {b # cs |b cs. b \<in> f B \<and> cs \<in> mk_linear_orders {} (B - {b})}
         else let b = SOME x. x \<in> f B - C in {b # cs |cs. cs \<in> mk_linear_orders C (B - {b})})"
by %invisible pat_completeness auto

context
  assumes "f_range_on A f"
begin

(*<*)

private lemma mk_linear_orders_termination:
  assumes "B \<subseteq> A"
  shows "mk_linear_orders_dom (C, B)"
using \<open>B \<subseteq> A\<close>
proof(induct t \<equiv> "card B" arbitrary: B C)
  case (0 B) with \<open>f_range_on A f\<close> show ?case
    unfolding f_range_on_def by (auto intro: mk_linear_orders.domintros)
next
  case (Suc i B)
  have "mk_linear_orders_dom ({}, B - {b})" if "b \<in> f B" for b
    using \<open>f_range_on A f\<close> Suc.hyps(2) Suc.prems Suc.hyps(1)[where B="B - {b}" and C="{}"] finite[of B] that
      unfolding f_range_on_def by (metis Diff_subset card_Diff_singleton contra_subsetD diff_Suc_1 subset_trans)
  moreover
  have "mk_linear_orders_dom (C, B - {SOME x. x \<in> f B - C})" if "b \<in> f B" and "b \<notin> C" for b
    using \<open>f_range_on A f\<close> Suc.hyps(2) Suc.prems Suc.hyps(1)[where B="B - {SOME x. x \<in> f B - C}" and C="C"] that
    by (clarsimp simp: card_Diff_singleton_if) (metis (mono_tags, lifting) contra_subsetD diff_Suc_1 f_range_onD someI subset_insertI2 subset_insert_iff)
  ultimately show ?case by (auto intro: mk_linear_orders.domintros) (* the simplifier has made a mess of the rule *)
qed

private lemma mk_linear_orders_induct[consumes 2, case_names base step1 step2]:
  assumes "r \<in> mk_linear_orders C B"
  assumes "B \<subseteq> A"
  assumes base: "\<And>C B. \<lbrakk>B \<subseteq> A; f B = {}\<rbrakk> \<Longrightarrow> P C B []"
  assumes step1: "\<And>C B b cs. \<lbrakk>B \<subseteq> A; cs \<in> mk_linear_orders {} (B - {b}); b \<in> f B; f B \<subseteq> C; P {} (B - {b}) cs\<rbrakk>
                          \<Longrightarrow> P C B (b # cs)"
  assumes step2: "\<And>C B b cs. \<lbrakk>B \<subseteq> A; cs \<in> mk_linear_orders C (B - {SOME x. x \<in> f B - C}); b \<in> f B; b \<notin> C; P C (B - {SOME x. x \<in> f B - C}) cs\<rbrakk>
                          \<Longrightarrow> P C B ((SOME x. x \<in> f B - C) # cs)"
  shows "P C B r"
using mk_linear_orders_termination[OF \<open>B \<subseteq> A\<close>, where C=C] assms(1,2)
proof(induct arbitrary: r rule: mk_linear_orders.pinduct)
  case (1 C B r) then show ?case
    by (fastforce simp: mk_linear_orders.psimps Let_def base split: if_splits
                intro!: step1 step2[simplified] 1)
qed

(*>*)

lemma mk_linear_orders_non_empty:
  assumes "B \<subseteq> A"
  shows "\<exists>r. r \<in> mk_linear_orders C B"
using %invisible assms
proof(induct t \<equiv> "card B" arbitrary: B C rule: nat_less_induct)
  case (1 B C)
  { assume "f B \<subseteq> C" "f B \<noteq> {}"
    with \<open>f_range_on A f\<close> 1 have "\<exists>b. b \<in> f B \<and> (\<exists>cs. cs \<in> local.mk_linear_orders {} (B - {b}))"
      by safe (metis Diff_subset card_Diff1_less dual_order.trans finite f_range_onD') }
  moreover
  { assume "\<not> f B \<subseteq> C" "f B \<noteq> {}"
    with \<open>f_range_on A f\<close> "1.prems" have "(SOME x. x \<in> f B - C) \<in> B \<and> B - {SOME a. a \<in> f B - C} \<subseteq> A"
      using someI[where P="\<lambda>x. x \<in> f B - C"] by (auto dest: f_range_onD')
    with "1.hyps"[rule_format, where x="B - {SOME x. x \<in> f B - C}" and xa=C, OF _ refl]
    have "\<exists>cs. cs \<in> local.mk_linear_orders C (B - {SOME x. x \<in> f B \<and> x \<notin> C})"
      by clarsimp (metis card_gt_0_iff diff_Suc_less equals0D finite) }
  ultimately show ?case
    by (clarsimp simp: mk_linear_orders.psimps[OF mk_linear_orders_termination[OF \<open>B \<subseteq>A\<close>]] Let_def)
qed

lemma mk_linear_orders_range:
  assumes "r \<in> mk_linear_orders C B"
  assumes "B \<subseteq> A"
  shows "set r \<subseteq> B"
using %invisible assms
proof(induct rule: mk_linear_orders_induct)
  case (base C B) with \<open>f_range_on A f\<close> show ?case by (simp add: f_range_on_def)
next
  case (step1 C B b cs) with \<open>f_range_on A f\<close> show ?case by (auto dest: f_range_onD)
next
  case (step2 C B b cs) with \<open>f_range_on A f\<close> show ?case
    by clarsimp (metis (mono_tags, lifting) Diff_subset someI_ex subset_eq f_range_onD)
qed

lemma mk_linear_orders_nth:
  assumes "r \<in> mk_linear_orders C B"
  assumes "B \<subseteq> A"
  assumes "i < length r"
  shows "r ! i \<in> f (B - set (take i r))"
using %invisible assms
proof(induct arbitrary: i rule: mk_linear_orders_induct)
  case (step1 C B b cs i) then show ?case
    by (cases i) (simp_all add: Diff_insert2[symmetric])
next
  case (step2 C B b cs i) then show ?case
    by (cases i) (auto simp: Diff_insert2[symmetric] intro: someI2)
qed simp

lemma mk_linear_orders_distinct:
  assumes "r \<in> mk_linear_orders C B"
  assumes "B \<subseteq> A"
  shows "distinct r"
using %invisible assms
proof(induct rule: mk_linear_orders_induct)
  case (step1 C B b cs) then show ?case
    by simp (metis Diff_eq_empty_iff Diff_subset Diff_subset_conv le_iff_sup mk_linear_orders_range subset_Diff_insert)
next
  case (step2 C B b cs) then show ?case
    by simp (meson Diff_subset order.trans mk_linear_orders_range subset_Diff_insert)
qed simp

lemma mk_linear_orders_Linear_order:
  assumes "r \<in> mk_linear_orders C A"
  shows "Linear_order (linord_of_list r)"
using %invisible mk_linear_orders_distinct[OF assms(1)] linord_of_list_Linear_order by fastforce

lemma mk_linear_orders_decisive_on_set_r:
  assumes "r \<in> mk_linear_orders C B"
  assumes "decisive_on A f"
  assumes "B \<subseteq> A"
  shows "set r = B"
using %invisible assms(1,3)
proof(induct rule: mk_linear_orders_induct)
  case (base C B) with \<open>decisive_on A f\<close> show ?case by (auto dest: decisive_onD)
next
  case (step1 C B b cs) with \<open>f_range_on A f\<close> show ?case by (auto dest: f_range_onD)
next
  case (step2 C B b cs) with \<open>f_range_on A f\<close> show ?case
    unfolding f_range_on_def
    by clarsimp (metis (no_types, lifting) Un_iff insert_Diff insert_Diff_single someI subset_Un_eq)
qed

lemma mk_linear_orders_decisive_on_refl_on:
  assumes "r \<in> mk_linear_orders C A"
  assumes "decisive_on A f"
  shows "refl_on A (linord_of_list r)"
using %invisible linord_of_list_refl_on mk_linear_orders_decisive_on_set_r[OF assms] by blast

lemma mk_linear_orders_decisive_on_total_on:
  assumes "r \<in> mk_linear_orders C A"
  assumes "decisive_on A f"
  shows "total_on A (linord_of_list r)"
using %invisible linord_of_list_total_on mk_linear_orders_decisive_on_set_r[OF assms] by blast

lemma mk_linear_orders_set_r_decisive_on:
  assumes "r \<in> mk_linear_orders C B"
  assumes "B \<subseteq> A"
  assumes "B \<subseteq> set r"
  assumes "iia_on A f"
  shows "decisive_on B f"
using %invisible assms(1-3)
proof(induct rule: mk_linear_orders_induct)
  case (base C B) with decisive_on_empty[of f] show ?case by simp
next
  case (step1 C B b cs)
  with mk_linear_orders_range[OF step1.hyps(2)] have "set cs \<subseteq> B - {b}" "decisive_on (B - {b}) f"
    by fastforce+
  with step1 \<open>iia_on A f\<close> show ?case
    by - (rule decisive_onI; metis (no_types, lifting) Diff_empty Diff_insert0 insert_Diff insert_not_empty subset_insert_iff decisive_onD iia_onD)
next
  case (step2 C B b cs)
  then have XXX: "decisive_on (B - {SOME x. x \<in> f B - C}) f" by force
  show ?case
  proof(rule decisive_onI)
    fix D assume "D \<subseteq> B" "D \<noteq> {}"
    with \<open>iia_on A f\<close> step2 XXX show "f D \<noteq> {}"
      by (cases "(SOME x. x \<in> f B - C) \<in> D")
         (simp_all, metis (no_types, lifting) emptyE iia_onD someI_ex, blast dest: decisive_onD)
  qed
qed

lemma mk_linear_orders_total_on_decisive_on:
  assumes "r \<in> mk_linear_orders C A"
  assumes "A \<subseteq> set r"
  assumes "iia_on A f"
  shows "decisive_on A f"
using %invisible mk_linear_orders_set_r_decisive_on[OF assms(1) _ _ assms(3)] linord_of_list_Field[of r] \<open>A \<subseteq> set r\<close> by simp

lemma mk_linear_orders_MaxR_opt_f:
  assumes "r \<in> mk_linear_orders C A"
  assumes "MaxR.MaxR_opt (linord_of_list r) D = Some x"
  assumes "iia_on A f"
  assumes "D \<subseteq> A"
  shows "x \<in> f D"
proof %invisible -
  from linord_of_list_Linear_order[OF mk_linear_orders_distinct[OF assms(1) subset_refl]]
  have "MaxR (linord_of_list r)" by (rule MaxR.intro) simp
  with assms(2)
  have "x \<in> greatest (linord_of_list r) (D \<inter> Field (linord_of_list r))"
    using MaxR.greatest elem_set by blast
  then obtain i where "x = r ! i" and "i < length r" and "\<forall>j<i. r ! j \<notin> D"
    unfolding greatest_def using mk_linear_orders_distinct[OF assms(1) subset_refl] linord_of_list_nth[where xs=r]
    by atomize_elim (clarsimp simp: set_conv_nth; metis IntI less_trans not_le nth_mem set_conv_nth)
  with \<open>iia_on A f\<close> \<open>D \<subseteq> A\<close> show ?thesis
    using mk_linear_orders_nth[OF assms(1), where i=i]
          iia_onD[of A f, where B="A - set (take i r)" and C=D and a=x]
          MaxR.range_Some[rule_format, OF \<open>MaxR (linord_of_list r)\<close> assms(2)]
    by (fastforce simp: nth_image[symmetric])
qed

lemma mk_linear_orders_f_MaxR_opt:
  assumes "x \<in> f C"
  assumes "consistency_on A f"
  assumes "B \<subseteq> A"
  assumes "C \<subseteq> B"
  shows "\<exists>r\<in>mk_linear_orders C B. MaxR.MaxR_opt (linord_of_list r) C = Some x"
using %invisible \<open>B \<subseteq> A\<close> \<open>C \<subseteq> B\<close>
proof(induct t \<equiv> "card B" arbitrary: B rule: nat_less_induct)
  case (1 B) show ?case
  proof(cases "f B = {}")
    case True
    with consistency_onD[OF assms(2), where B=B and C=C] "1.prems" \<open>x \<in> f C\<close>
    show ?thesis by simp
  next
    case False show ?thesis
    proof(cases "f B \<subseteq> C")
      case True
      from \<open>B \<subseteq> A\<close> obtain r where r: "r \<in> mk_linear_orders {} (B - {x})"
        using mk_linear_orders_non_empty by (meson Diff_subset_conv le_supI2)
      from True consistency_onD[OF assms(2), where B=B and C=C] "1.prems" \<open>x \<in> f C\<close>
      have x: "x \<in> f B" by blast
      from \<open>f B \<noteq> {}\<close> True \<open>B \<subseteq> A\<close> r x have XXX: "x # r \<in> mk_linear_orders C B"
        using mk_linear_orders_termination[of B C]
        by (simp add: mk_linear_orders.psimps card_eq_0_iff split: if_splits)
      show ?thesis
      proof(rule bexI[OF _ XXX])
        from \<open>f_range_on A f\<close> True r x \<open>B \<subseteq> A\<close> \<open>C \<subseteq> B\<close>  \<open>x \<in> f C\<close>
        show "MaxR.MaxR_opt (linord_of_list (x # r)) C = Some x"
          using linord_of_list_Linear_order[OF mk_linear_orders_distinct[OF XXX \<open>B \<subseteq> A\<close>]]
          unfolding Option.elem_set[symmetric] by (auto simp: MaxR.greatest MaxR_def greatest_def linord_of_list_linord_of_listP dest: f_range_onD)
      qed
    next
      case False
      let ?b = "SOME x. x \<in> f B - C"
      let ?B' = "B - {?b}"
      from False \<open>B \<subseteq> A\<close> obtain a where "a \<in> f B - C" by blast
      with \<open>f_range_on A f\<close> \<open>B \<subseteq> A\<close> have "card ?B' < card B"
        unfolding f_range_on_def
        by (clarsimp simp: card_Diff_singleton_if) (metis (no_types, lifting) One_nat_def card_Diff1_less card_Diff_singleton finite someI_ex subsetCE)
      from \<open>C \<subseteq> B\<close> \<open>a \<in> f B - C\<close>
      have "C \<subseteq> B - {SOME x. x \<in> f B - C}" by (metis Diff_empty Diff_iff someI subset_Diff_insert)
      with 1(1)[rule_format, OF \<open>card ?B' < card B\<close> refl] \<open>B \<subseteq> A\<close>
      obtain r where r: "r \<in> mk_linear_orders C ?B'" "MaxR.MaxR_opt (linord_of_list r) C = Some x" by blast
      with \<open>f B \<noteq> {}\<close> False \<open>B \<subseteq> A\<close> have "?b # r \<in> mk_linear_orders C B"
        using mk_linear_orders_termination[of B C]
        by (simp add: mk_linear_orders.psimps Let_def card_eq_0_iff split: if_splits)
      moreover
      have "MaxR.MaxR_opt (linord_of_list (?b # r)) C = Some x"
      proof(rule MaxR.greatest_is_MaxR_opt)
        from linord_of_list_Linear_order[OF mk_linear_orders_distinct[OF \<open>?b # r \<in> mk_linear_orders C B\<close> \<open>B \<subseteq> A\<close>]]
        show "MaxR (linord_of_list (?b # r))" by (simp add: MaxR.intro)
        from \<open>f_range_on A f\<close> r \<open>B \<subseteq> A\<close>
        show "x \<in> C \<inter> Field (linord_of_list (?b # r))"
          by clarsimp (metis (no_types, lifting) Choice_Functions.mk_linear_orders_Linear_order Diff_subset IntD2 Int_iff MaxR.intro MaxR.range_Some f_range_on_antimono linord_of_list_Field)
        from \<open>f_range_on A f\<close> r \<open>a \<in> f B - C\<close> \<open>B \<subseteq> A\<close>
        show "\<forall>y\<in>C \<inter> Field (linord_of_list (?b # r)). (y, x) \<in> linord_of_list (?b # r)"
          using someI[where P="\<lambda>x. x \<in> f B - C"]
          by (auto simp: linord_of_list_linord_of_listP intro: MaxR.intro intro: f_range_on_antimono dest!: MaxR.MaxR_opt_is_greatest[rotated] Choice_Functions.mk_linear_orders_Linear_order[rotated])
      qed
      ultimately show ?thesis by blast
    qed
  qed
qed

end

end

lemma path_independent_on_pseudo_rationalizable_on:
  fixes f :: "'a::finite cfun"
  assumes "path_independent_on A f"
  assumes "f_range_on A f"
  assumes Rs_def[simp]: "Rs = (\<Union>C\<in>Pow A. linord_of_list ` mk_linear_orders f C A)"
  shows "pseudo_rationalizable_on A Rs f \<and> (\<forall>r\<in>Rs. refl_on A r \<and> total_on A r \<longleftrightarrow> decisive_on A f)"
proof %invisible -
  have "pseudo_rationalizable_on A Rs f"
  proof(rule pseudo_rationalizable_onI)
    fix r assume "r \<in> Rs" then show "Linear_order r"
      using mk_linear_orders_Linear_order[OF \<open>f_range_on A f\<close>] by clarsimp
  next
    fix B assume "B \<subseteq> A" show "f B = (\<Union>r\<in>Rs. set_option (MaxR.MaxR_opt r B))" (is "?lhs = ?rhs")
    proof(rule set_elem_equalityI)
      fix x assume "x \<in> ?lhs" with \<open>B \<subseteq> A\<close> show "x \<in> ?rhs"
        using path_independent_on_consistency_on[OF assms(1)]
              mk_linear_orders_f_MaxR_opt[OF \<open>f_range_on A f\<close>] by fastforce
    next
      fix x assume "x \<in> ?rhs" with \<open>B \<subseteq> A\<close> show "x \<in> ?lhs"
        using path_independent_on_Chernoff_on[OF assms(1,2)] Chernoff_on_iia_on
              mk_linear_orders_MaxR_opt_f[OF \<open>f_range_on A f\<close>] by simp blast
    qed
  qed
  moreover
  from path_independent_on_Chernoff_on[OF assms(1,2)] Chernoff_on_iia_on
  have "iia_on A f" by blast
  then have "\<forall>r\<in>Rs. refl_on A r \<and> total_on A r \<longleftrightarrow> decisive_on A f"
    using mk_linear_orders_total_on_decisive_on[OF assms(2)]
          mk_linear_orders_decisive_on_refl_on[OF assms(2)]
          mk_linear_orders_decisive_on_total_on[OF assms(2)]
    by clarsimp (meson linord_of_list_refl_on refl_onD refl_onD1 subsetI)
  ultimately show ?thesis by blast
qed

text\<open>

Our top-level theorem is essentially \citet[Theorem~5]{Moulin:1985}:

\<close>

theorem pseudo_rationalizable:
  assumes "f_range_on A f"
  shows "path_independent_on A f
           \<longleftrightarrow> (\<exists>Rs. pseudo_rationalizable_on A Rs f \<and> (\<forall>r\<in>Rs. refl_on A r \<and> total_on A r \<longleftrightarrow> decisive_on A f))"
using %invisible pseudo_rationalizable_on_path_independent_on path_independent_on_pseudo_rationalizable_on[OF _ assms] by fastforce
(*<*)

end
(*>*)
