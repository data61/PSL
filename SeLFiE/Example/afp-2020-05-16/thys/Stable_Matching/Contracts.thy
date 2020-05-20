(*<*)
theory Contracts
imports
  Choice_Functions
  "HOL-Library.Dual_Ordered_Lattice"
  "HOL-Library.Bourbaki_Witt_Fixpoint"
  "HOL-Library.While_Combinator"
  "HOL-Library.Product_Order"
begin

(*>*)
section\<open> \citet{HatfieldMilgrom:2005}: Matching with contracts \label{sec:contracts} \<close>

text\<open>

We take the original paper on matching with contracts by
\citet{HatfieldMilgrom:2005} as our roadmap, which follows a similar
path to \citet[\S2.5]{RothSotomayor:1990}. We defer further motivation
to these texts. Our first move is to capture the scenarios described
in their {\S}I(A) (p916) in a locale.

\<close>

locale Contracts =
  fixes Xd :: "'x::finite \<Rightarrow> 'd::finite"
  fixes Xh :: "'x \<Rightarrow> 'h::finite"
  fixes Pd :: "'d \<Rightarrow> 'x rel"
  fixes Ch :: "'h \<Rightarrow> 'x cfun"
  assumes Pd_linear: "\<forall>d. Linear_order (Pd d)"
  assumes Pd_range: "\<forall>d. Field (Pd d) \<subseteq> {x. Xd x = d}"
  assumes Ch_range: "\<forall>h. \<forall>X. Ch h X \<subseteq> {x\<in>X. Xh x = h}"
  assumes Ch_singular: "\<forall>h. \<forall>X. inj_on Xd (Ch h X)"
begin

text \<open>

The set of contracts is modelled by the type @{typ "'x"}, a free type
variable that will later be interpreted by some non-empty
set. Similarly @{typ "'d"} and @{typ "'h"} track the names of doctors
and hospitals respectively. All of these are finite by virtue of
belonging to the \<open>finite\<close> type class.

We fix four constants:
\begin{itemize}

\item \<open>Xd\<close> (\<open>Xh\<close>) projects the name of the
  relevant doctor (hospital) from a contract;

\item \<open>Pd\<close> maps doctors to their linear preferences over
  some subset of contracts that name them (assumptions @{thm [source]
  Pd_linear} and @{thm [source] Pd_range}); and

\item \<open>Ch\<close> maps hospitals to their choice functions
  (\S\ref{sec:cf}), which are similarly constrained to contracts that
  name them (assumption @{thm [source] Ch_range}). Moreover their
  choices must name each doctor at most once, i.e., \<open>Xd\<close>
  must be injective on these (assumption @{thm [source]
  "Ch_singular"}).

\end{itemize}

The reader familiar with the literature will note that we do not have
a null contract (also said to represent the @{emph \<open>outside option\<close>} of
unemployment), and instead use partiality of the doctors'
preferences. This provides two benefits: firstly, \<open>Xh\<close> is
a total function here, and secondly we achieve some economy of
description when instantiating this locale as \<open>Pd\<close> only
has to rank the relevant contracts.

We note in passing that neither the doctors' nor hospitals' choice
functions are required to be decisive, unlike the standard literature
on choice functions (\S\ref{sec:cf}).

In addition to the above, the following constitute the definitions
that must be trusted for the results we prove to be meaningful.

\<close>

definition Cd :: "'d \<Rightarrow> 'x cfun" where
  "Cd d \<equiv> set_option \<circ> MaxR.MaxR_opt (Pd d)"

definition CD_on :: "'d set \<Rightarrow> 'x cfun" where
  "CD_on ds X = (\<Union>d\<in>ds. Cd d X)"

abbreviation CD :: "'x set \<Rightarrow> 'x set" where
  "CD \<equiv> CD_on UNIV"

definition CH :: "'x cfun" where
  "CH X = (\<Union>h. Ch h X)"

text\<open>

The function @{const "Cd"} constructs a choice function from the
doctor's linear preferences (see \S\ref{sec:cf-linear}). Both @{const
"CD"} and @{const "CH"} simply aggregate opinions in the obvious
way. The functions @{const "CD_on"} is parameterized with a set of
doctors to support the proofs of \S\ref{sec:contracts-vacancy-chain}.

We also define \<open>RD\<close> (\<open>Rh\<close>,
\<open>RH\<close>) to be the subsets of a given set of contracts that
are rejected by the doctors (hospitals). (The abbreviation @{const
"Rf"} is defined in \S\ref{sec:cf-rf}.)

\<close>

abbreviation (input) RD_on :: "'d set \<Rightarrow> 'x cfun" where
  "RD_on ds \<equiv> Rf (CD_on ds)"

abbreviation (input) RD :: "'x cfun" where
  "RD \<equiv> RD_on UNIV"

abbreviation (input) Rh :: "'h \<Rightarrow> 'x cfun" where
  "Rh h \<equiv> Rf (Ch h)"

abbreviation (input) RH :: "'x cfun" where
  "RH \<equiv> Rf CH"

text \<open>

A @{emph \<open>mechanism\<close>} maps doctor and hospital preferences into a match
(here a set of contracts).

\<close>

type_synonym (in -) ('d, 'h, 'x) mechanism = "('d \<Rightarrow> 'x rel) \<Rightarrow> ('h \<Rightarrow> 'x cfun) \<Rightarrow> 'd set \<Rightarrow> 'x set"
(*<*)

(* Pd *)

lemmas Pd_linear' = Pd_linear[rule_format]
lemmas Pd_range' = subsetD[OF Pd_range[rule_format], simplified, of x d] for x d

lemma Pd_refl:
  assumes "x \<in> Field (Pd d)"
  shows "(x, x) \<in> Pd d"
using assms Pd_linear' by (meson subset_refl underS_incl_iff)

lemma Pd_Xd:
  assumes "(x, y) \<in> Pd d"
  shows "Xd x = d \<and> Xd y = d"
using assms Pd_range contra_subsetD unfolding Field_def by blast

lemma Above_Pd_Xd:
  assumes "x \<in> Above (Pd d) X"
  shows "Xd x = d"
using assms by (blast dest: Above_Field Pd_range')

lemma AboveS_Pd_Xd:
  assumes "x \<in> AboveS (Pd d) X"
  shows "Xd x = d"
using assms by (blast dest: AboveS_Field Pd_range')

(* Cd *)

interpretation Cd: linear_cf "Pd d" "Cd d" for d
using Cd_def Pd_linear by unfold_locales simp_all

lemmas Cd_domain = Cd.domain
lemmas Cd_f_range = Cd.f_range
lemmas Cd_range = Cd.range
lemmas Cd_range' = Cd.range'
lemmas Rf_Cd_mono = Cd.Rf_mono_on[of UNIV, unfolded mono_on_mono]
lemmas Cd_Chernoff = Cd.Chernoff
lemmas Cd_path_independent = Cd.path_independent
lemmas Cd_iia = Cd.iia
lemmas Cd_irc = Cd.irc
lemmas Cd_lad = Cd.lad
lemmas Cd_mono = Cd.mono
lemmas Cd_greatest = Cd.greatest
lemmas Cd_preferred = Cd.preferred
lemmas Cd_singleton = Cd.singleton
lemmas Cd_union = Cd.union
lemmas Cd_idem = iia_f_idem[OF Cd.f_range[of UNIV d, folded Cd_def] Cd_iia[of UNIV], simplified] for d

lemma Cd_Xd:
  shows "x \<in> Cd d X \<Longrightarrow> Xd x = d"
using Pd_range Cd_range by fastforce

lemma Cd_inj_on_Xd:
  shows "inj_on Xd (Cd d X)"
by (rule inj_onI) (clarsimp simp: Cd_Xd Cd_singleton)

lemma Cd_range_disjoint:
  assumes "d \<noteq> d'"
  shows "Cd d A \<inter> Cd d' A = {}"
using assms Cd_range Pd_range by blast

lemma Cd_single:
  assumes "x \<in> X"
  assumes "inj_on Xd X"
  assumes "x \<in> Field (Pd d)"
  shows "x \<in> Cd d X"
using assms Pd_linear unfolding Cd_greatest greatest_def
by clarsimp (metis Pd_Xd inj_on_eq_iff subset_refl underS_incl_iff)

lemma Cd_Above:
  shows "Cd d X = Above (Pd d) (X \<inter> Field (Pd d)) \<inter> X"
unfolding Cd_greatest greatest_Above Above_def by blast

(* Code generator setup. Repeats a lot of stuff. *)

definition maxR :: "'d \<Rightarrow> 'x \<Rightarrow> 'x \<Rightarrow> 'x" where
  "maxR d x y = (if (x, y) \<in> Pd d then y else x)"

definition MaxR_f :: "'d \<Rightarrow> 'x \<Rightarrow> 'x option \<Rightarrow> 'x option" where
  "MaxR_f d = (\<lambda>x acc. if x \<in> Field (Pd d) then Some (case acc of None \<Rightarrow> x | Some y \<Rightarrow> maxR d x y) else acc)"

lemma MaxR_maxR:
  shows "MaxR.maxR (Pd d) = maxR d"
by (simp add: fun_eq_iff maxR_def Cd.maxR_code)

lemma MaxR_MaxR_f:
  shows "MaxR.MaxR_f (Pd d) = MaxR_f d"
by (simp add: fun_eq_iff Cd.MaxR_f_code MaxR_f_def MaxR_maxR cong: option.case_cong)

lemmas Cd_code[code] = Cd.code[unfolded MaxR_MaxR_f]

lemma Cd_simps[simp, nitpick_simp]:
  shows "Cd d {} = {}"
        "Cd d (insert x A) = (if x \<in> Field (Pd d) then if Cd d A = {} then {x} else {maxR d x y |y. y \<in> Cd d A} else Cd d A)"
unfolding Cd.simps MaxR_maxR by simp_all

(* CD *)

lemma CD_on_def2:
  shows "CD_on ds A = (\<Union>d\<in>ds. Cd d (A \<inter> Field (Pd d)))"
using Cd_domain unfolding CD_on_def by blast

lemma CD_on_Xd:
  assumes "x \<in> CD_on ds A"
  shows "Xd x \<in> ds"
using assms Cd_Xd unfolding CD_on_def by blast

lemma mem_CD_on_Cd:
  shows "x \<in> CD_on ds X \<longleftrightarrow> (x \<in> Cd (Xd x) X \<and> Xd x \<in> ds)"
unfolding CD_on_def using Cd_range Cd_Xd by blast

lemma CD_on_domain:
  assumes "d \<in> ds"
  shows "CD_on ds A \<inter> Field (Pd d) = Cd d (A \<inter> Field (Pd d))"
unfolding CD_on_def2 using assms Cd_range by (force dest: Pd_range')

lemma CD_on_range:
  shows "CD_on ds A \<subseteq> A \<inter> (\<Union>d\<in>ds. Field (Pd d))"
using Cd_range unfolding CD_on_def by blast

lemmas CD_on_range' = subsetD[OF CD_on_range]

lemma CD_on_f_range_on:
  shows "f_range_on A (CD_on ds)"
by (rule f_range_onI) (meson CD_on_range Int_subset_iff)

lemma RD_on_mono:
  shows "mono (RD_on ds)"
unfolding CD_on_def by (rule monoI) (auto dest: monoD[OF Rf_Cd_mono])

lemma CD_on_Chernoff:
  shows "Chernoff (CD_on ds)"
using mono_on_mono RD_on_mono[of ds] Rf_mono_on_iia_on[of UNIV] Chernoff_on_iia_on by (simp add: fun_eq_iff) blast

lemma CD_on_irc:
  shows "irc (CD_on ds)"
by (rule ircI) (fastforce simp: CD_on_def ircD[OF Cd_irc] simp del: Cd_simps cong: SUP_cong)

lemmas CD_on_consistency = irc_on_consistency_on[OF CD_on_irc, simplified]

lemma CD_on_path_independent:
  shows "path_independent (\<lambda>X. CD_on ds X)"
using CD_on_f_range_on CD_on_Chernoff CD_on_consistency by (blast intro: path_independent_onI2)

lemma CD_on_simps:
  shows "CD_on ds {} = {}"
using CD_on_range by blast

lemmas CD_on_iia = RD_on_mono[unfolded Rf_mono_iia]
lemmas CD_on_idem = iia_f_idem[OF CD_on_f_range_on CD_on_iia, simplified]

lemma CD_on_inj_on_Xd:
  shows "inj_on Xd (CD_on ds X)"
unfolding CD_on_def by (rule inj_onI) (clarsimp simp: Cd_Xd Cd_singleton)

lemma CD_on_card:
  shows "card (CD_on ds X) = (\<Sum>d\<in>ds. card (Cd d X))"
unfolding CD_on_def by (simp add: card_UN_disjoint Cd_range_disjoint)

lemma CD_on_closed:
  assumes "inj_on Xd X"
  assumes "X \<subseteq> (\<Union>d\<in>ds. Field (Pd d))"
  shows "CD_on ds X = X"
using assms Cd_domain Cd_single[OF _ assms(1)] unfolding CD_on_def2 by (force dest: Cd_range')

(* Ch *)

lemmas Ch_singular' = Ch_singular[rule_format]
lemmas Ch_range' = subsetD[OF Ch_range[rule_format], simplified, of x h X] for x h X

lemma Ch_simps:
  shows "Ch h {} = {}"
using Ch_range by blast

lemma Ch_range_disjoint:
  assumes "h \<noteq> h'"
  shows "Ch h A \<inter> Ch h' A = {}"
using assms Ch_range by blast

lemma Ch_f_range:
  shows "f_range (Ch h)"
using Ch_range unfolding f_range_on_def by blast

(* CH *)

lemma CH_card:
  shows "card (CH X) = (\<Sum>h\<in>UNIV. card (Ch h X))"
unfolding CH_def by (simp add: card_UN_disjoint Ch_range_disjoint)

lemma CH_simps:
  shows "CH {} = {}"
unfolding CH_def by (simp add: Ch_simps)

lemma CH_range:
  shows "CH A \<subseteq> A"
unfolding CH_def using Ch_range by blast

lemmas CH_range' = subsetD[OF CH_range]
lemmas CH_f_range_on = f_range_onI[OF CH_range]

lemma mem_CH_Ch:
  shows "x \<in> CH X \<longleftrightarrow> x \<in> Ch (Xh x) X"
unfolding CH_def using Ch_range by blast

lemma mem_Ch_CH:
  assumes "x \<in> Ch h X"
  shows "x \<in> CH X"
unfolding CH_def using assms Ch_range by blast

(*>*)
text\<open>

An @{emph \<open>allocation\<close>} is a set of contracts where each names a distinct
doctor. (Hospitals can contract multiple doctors.)

\<close>

abbreviation (input) allocation :: "'x set \<Rightarrow> bool" where
  "allocation \<equiv> inj_on Xd"

text\<open>

We often wish to extract a doctor's or a hospital's contract from an
@{const "allocation"}.

\<close>

definition dX :: "'x set \<Rightarrow> 'd \<Rightarrow> 'x set" where
  "dX X d = {x \<in> X. Xd x = d}"

definition hX :: "'x set \<Rightarrow> 'h \<Rightarrow> 'x set" where
  "hX X h = {x \<in> X. Xh x = h}"
(*<*)

lemma dX_union:
  shows "dX (X \<union> Y) d = dX X d \<union> dX Y d"
unfolding dX_def by auto

lemma dX_range:
  shows "\<forall>d. dX X d \<subseteq> {x. Xd x = d}"
unfolding dX_def by clarsimp

lemma dX_range':
  assumes "x \<in> dX X d"
  shows "x \<in> X \<and> Xd x = d"
using assms unfolding dX_def by simp

lemma dX_empty_or_singleton:
  assumes "allocation X"
  shows "\<forall>d. dX X d = {} \<or> (\<exists>x. dX X d = {x})"
unfolding dX_def using \<open>allocation X\<close> by (fastforce dest: inj_onD)

lemma dX_linear:
  assumes "allocation X"
  shows "Linear_order (dX X d \<times> dX X d)"
using spec[OF dX_empty_or_singleton[OF \<open>allocation X\<close>], where x=d] by fastforce

lemma dX_singular:
  assumes "allocation X"
  assumes "x \<in> X"
  assumes "d = Xd x"
  shows "dX X d = {x}"
using assms unfolding dX_def by (fastforce dest: inj_onD)

lemma dX_Int_Field_Pd:
  assumes "dX X d \<subseteq> Field (Pd d)"
  shows "X \<inter> Field (Pd d) = dX X d"
using assms unfolding dX_def by (fastforce dest: Pd_range')

lemma Cd_Above_dX:
  assumes "dX X d \<subseteq> Field (Pd d)"
  shows "Cd d X = Above (Pd d) (dX X d) \<inter> X"
using assms unfolding Cd_greatest greatest_Above Above_def dX_def by (auto dest: Pd_range')

(*>*)
text\<open>

@{emph \<open>Stability\<close>} is the key property we look for in a match (here a
set of contracts), and consists of two parts.

Firstly, we ask that it be @{emph \<open>individually rational\<close>}, i.e., the
contracts in the match are actually acceptable to all
participants. Note that this implies the match is an @{const
"allocation"}.

\<close>

definition individually_rational_on :: "'d set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "individually_rational_on ds X \<longleftrightarrow> CD_on ds X = X \<and> CH X = X"

abbreviation individually_rational :: "'x set \<Rightarrow> bool" where
  "individually_rational \<equiv> individually_rational_on UNIV"

text\<open>

The second condition requires that there be no coalition of a hospital
and one or more doctors who prefer another set of contracts involving
them; the hospital strictly, the doctors weakly. Contrast this
definition with the classical one for stable marriages given in
\S\ref{sec:sotomayor}.

\<close>

definition blocking_on :: "'d set \<Rightarrow> 'x set \<Rightarrow> 'h \<Rightarrow> 'x set \<Rightarrow> bool" where
  "blocking_on ds X h X' \<longleftrightarrow> X' \<noteq> Ch h X \<and> X' = Ch h (X \<union> X') \<and> X' \<subseteq> CD_on ds (X \<union> X')"

definition stable_no_blocking_on :: "'d set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "stable_no_blocking_on ds X \<longleftrightarrow> (\<forall>h X'. \<not>blocking_on ds X h X')"

abbreviation stable_no_blocking :: "'x set \<Rightarrow> bool" where
  "stable_no_blocking \<equiv> stable_no_blocking_on UNIV"

definition stable_on :: "'d set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "stable_on ds X \<longleftrightarrow> individually_rational_on ds X \<and> stable_no_blocking_on ds X"

abbreviation stable :: "'x set \<Rightarrow> bool" where
  "stable \<equiv> stable_on UNIV"
(*<*)

lemma stable_onI:
  assumes "individually_rational_on ds X"
  assumes "stable_no_blocking_on ds X"
  shows "stable_on ds X"
unfolding stable_on_def using assms by blast

lemma individually_rational_onI:
  assumes "CD_on ds X = X"
  assumes "CH X = X"
  shows "individually_rational_on ds X"
unfolding individually_rational_on_def using assms by blast

lemma individually_rational_on_CD_on:
  assumes "individually_rational_on ds X"
  shows "CD_on ds X = X"
using assms unfolding individually_rational_on_def by blast

lemma individually_rational_on_Cd:
  assumes "individually_rational_on ds X"
  shows "Cd d X = dX X d"
using individually_rational_on_CD_on[OF assms]
by (auto simp: dX_def mem_CD_on_Cd dest: Cd_range' Cd_Xd)

lemma individually_rational_on_empty:
  shows "individually_rational_on ds {}"
by (simp add: CD_on_simps CH_simps individually_rational_onI)

lemma blocking_onI:
  assumes "X'' \<noteq> Ch h X"
  assumes "X'' = Ch h (X \<union> X'')"
  assumes "\<And>x. x \<in> X'' \<Longrightarrow> x \<in> CD_on ds (X \<union> X'')"
  shows "blocking_on ds X h X''"
unfolding blocking_on_def using assms by blast

lemma blocking_on_imp_not_stable:
  assumes "blocking_on ds X h X''"
  shows "\<not>stable_on ds X"
unfolding stable_on_def stable_no_blocking_on_def using assms by blast

lemma blocking_on_allocation:
  assumes "blocking_on ds X h X''"
  shows "allocation X''"
using assms unfolding blocking_on_def by (metis Ch_singular')

lemma blocking_on_Field:
  assumes "blocking_on ds X h X''"
  shows "dX X'' d \<subseteq> Field (Pd d)"
using assms blocking_on_allocation[OF assms] unfolding blocking_on_def dX_def
by (force simp: Pd_range' dest: CD_on_range')

lemma blocking_on_CD_on:
  assumes "blocking_on ds X h X''"
  shows "X'' \<subseteq> CD_on ds (X \<union> X'')"
using assms unfolding blocking_on_def by blast

lemma blocking_on_CD_on':
  assumes "blocking_on ds X h X''"
  assumes "x \<in> X''"
  shows "x \<in> CD_on ds (X \<union> X'')"
using assms unfolding blocking_on_def by blast

lemma blocking_on_Cd:
  assumes "blocking_on ds X h X''"
  shows "dX X'' d \<subseteq> Cd d (X \<union> X'')"
using assms unfolding blocking_on_def by (force dest: dX_range' simp: mem_CD_on_Cd)

lemma stable_no_blocking_onI:
  assumes "\<And>h X''. \<lbrakk>X'' = Ch h (X \<union> X''); X'' \<noteq> Ch h X; X'' \<subseteq> CD_on ds (X \<union> X'')\<rbrakk> \<Longrightarrow> False"
  shows "stable_no_blocking_on ds X"
unfolding stable_no_blocking_on_def blocking_on_def using assms by blast

lemma stable_no_blocking_onI2:
  assumes "\<And>h X''. blocking_on ds X h X'' \<Longrightarrow> False"
  shows "stable_no_blocking_on ds X"
unfolding stable_no_blocking_on_def using assms by blast

lemma "stable_no_blocking_on ds UNIV"
using stable_no_blocking_onI by fastforce

lemma
  assumes "stable_on ds X"
  shows stable_on_CD_on: "CD_on ds X = X"
    and stable_on_Xd: "x \<in> X \<Longrightarrow> Xd x \<in> ds"
    and stable_on_range': "x \<in> X \<Longrightarrow> x \<in> Field (Pd (Xd x))"
    and stable_on_CH: "CH X = X"
    and stable_on_no_blocking_on: "stable_no_blocking_on ds X"
using assms mem_CD_on_Cd Cd_range' Pd_range'
unfolding stable_on_def individually_rational_on_def by blast+

lemma stable_on_allocation:
  assumes "stable_on ds X"
  shows "allocation X"
using assms unfolding stable_on_def individually_rational_on_def by (metis CD_on_inj_on_Xd)

lemma stable_on_blocking_onD:
  assumes "stable_on ds X"
  shows "\<lbrakk>X'' = Ch h (X \<union> X''); X'' \<subseteq> CD_on ds (X \<union> X'')\<rbrakk> \<Longrightarrow> X'' = Ch h X"
using \<open>stable_on ds X\<close> unfolding stable_on_def individually_rational_on_def stable_no_blocking_on_def blocking_on_def by blast

lemma not_stable_on_cases[consumes 1, case_names not_individually_rational not_no_blocking]:
  assumes "\<not> stable_on ds X"
  assumes "\<not> individually_rational_on ds X \<Longrightarrow> P"
  assumes "\<not> stable_no_blocking_on ds X \<Longrightarrow> P"
  shows "P"
using assms unfolding stable_on_def by blast

(*>*)
text\<open>\<close>

end


subsection\<open> Theorem~1: Existence of stable pairs \<close>

text\<open>

We proceed to define a function whose fixed points capture all stable
matches. \citet[I(B), p917]{HatfieldMilgrom:2005} provide the
following intuition:
\begin{quote}

The first theorem states that a set of contracts is stable if any
alternative contract would be rejected by some doctor or some hospital
from its suitably defined opportunity set. In the formulas below,
think of the doctors' opportunity set as @{term "XD"} and the
hospitals' opportunity set as @{term "XH"}. If @{term "X'"} is the
corresponding stable set, then @{term "XD"} must include, in addition
to @{term "X'"}, all contracts that would not be rejected by the
hospitals, and @{term "XH"} must similarly include @{term "X'"} and
all contracts that would not be rejected by the doctors. If @{term
"X'"} is stable, then every alternative contract is rejected by
somebody, so @{term "X = XH \<union> XD"} [where @{term "X"} is the
set of all contracts]. This logic is summarized in the first theorem.

\end{quote}
See also \citet[p6,\S4]{Fleiner:2003} and \citet[\S2]{Fleiner:2002},
from whom we adopt the term @{emph \<open>stable pair\<close>}.

\<close>

context Contracts
begin

definition stable_pair_on :: "'d set \<Rightarrow> 'x set \<times> 'x set \<Rightarrow> bool" where
  "stable_pair_on ds = (\<lambda>(XD, XH). XD = - RH XH \<and> XH = - RD_on ds XD)"

abbreviation stable_pair :: "'x set \<times> 'x set \<Rightarrow> bool" where
  "stable_pair \<equiv> stable_pair_on UNIV"

abbreviation match :: "'x set \<times> 'x set \<Rightarrow> 'x set" where
  "match X \<equiv> fst X \<inter> snd X"

text \<open>

\citet[Theorem~1]{HatfieldMilgrom:2005} state that every solution
@{term "(XD, XH)"} of @{const "stable_pair"} yields a stable match
@{term "XD \<inter> XH"}, and conversely, i.e., every stable match is
the intersection of some stable pair. \citet{AygunSonmez:2012-WP2}
show that neither is the case without further restrictions on the
hospitals' choice functions @{term "Ch"}; we exhibit their
counterexample below.

Even so we can establish some properties in the present setting:

\<close>

lemma stable_pair_on_CD_on:
  assumes "stable_pair_on ds XD_XH"
  shows "match XD_XH = CD_on ds (fst XD_XH)"
using %invisible assms CD_on_range unfolding stable_pair_on_def split_def fst_conv snd_conv
by blast

lemma stable_pair_on_CH:
  assumes "stable_pair_on ds XD_XH"
  shows "match XD_XH = CH (snd XD_XH)"
using %invisible assms CH_range unfolding stable_pair_on_def split_def fst_conv snd_conv
by blast

lemma stable_pair_on_CD_on_CH:
  assumes "stable_pair_on ds XD_XH"
  shows "CD_on ds (fst XD_XH) = CH (snd XD_XH)"
using %invisible assms stable_pair_on_CD_on stable_pair_on_CH by blast

lemma stable_pair_on_allocation:
  assumes "stable_pair_on ds XD_XH"
  shows "allocation (match XD_XH)"
unfolding %invisible stable_pair_on_CD_on[OF assms] by (rule CD_on_inj_on_Xd)
(*<*)

lemma stable_pair_onI:
  assumes "fst XD_XH = - RH (snd XD_XH)"
  assumes "snd XD_XH = - RD_on ds (fst XD_XH)"
  shows "stable_pair_on ds XD_XH"
using assms unfolding stable_pair_on_def split_def by blast

lemma stable_pair_onE:
  shows "\<lbrakk>stable_pair_on ds XD_XH; \<lbrakk>- RH (snd XD_XH) = fst XD_XH; - RD_on ds (fst XD_XH) = snd XD_XH\<rbrakk> \<Longrightarrow> P\<rbrakk> \<Longrightarrow> P"
unfolding stable_pair_on_def split_def by blast

lemma stable_pair_on_Cd:
  assumes "stable_pair_on ds XD_XH"
  assumes "d \<in> ds"
  shows "Cd d (fst XD_XH) = match XD_XH \<inter> Field (Pd d)"
using stable_pair_on_CD_on[OF \<open>stable_pair_on ds XD_XH\<close>] CD_on_domain Cd_domain \<open>d \<in> ds\<close> by simp

lemma stable_pair_on_Cd_match:
  assumes "stable_pair_on ds XD_XH"
  assumes "d \<in> ds"
  shows "Cd d (match XD_XH) = Cd d (fst XD_XH)"
using assms by (metis Cd_domain Cd_idem stable_pair_on_Cd)

lemma stable_pair_on_Xd:
  assumes "stable_pair_on ds XD_XH"
  assumes "x \<in> match XD_XH"
  shows "Xd x \<in> ds"
using assms CD_on_Xd unfolding stable_pair_on_def split_def by blast

lemma stable_pair_on_match_Cd:
  assumes "stable_pair_on ds XD_XH"
  assumes "x \<in> match XD_XH"
  shows "x \<in> Cd (Xd x) (match XD_XH)"
using assms by (metis (full_types) CD_on_def Cd_Xd UN_iff stable_pair_on_CD_on stable_pair_on_Cd_match)

(*>*)
text\<open>

We run out of steam on the following two lemmas, which are the
remaining requirements for stability.

\<close>

lemma
  assumes "stable_pair_on ds XD_XH"
  shows "individually_rational_on ds (match XD_XH)"
oops

lemma
  assumes "stable_pair_on ds XD_XH"
  shows "stable_no_blocking (match XD_XH)"
oops

text\<open>

\citet{HatfieldMilgrom:2005} also claim that the converse holds:

\<close>

lemma
  assumes "stable_on ds X"
  obtains XD_XH where "stable_pair_on ds XD_XH" and "X = match XD_XH"
oops

text\<open>

Again, the following counterexample shows that the @{const
substitutes} condition on @{term "Ch"} is too weak to guarantee
this. We show it holds under stronger assumptions in
\S\ref{sec:contracts-t1-converse}.

\<close>

end


subsubsection\<open> Theorem~1 does not hold \citep{AygunSonmez:2012-WP2} \label{sec:contracts-t1-counterexample} \<close>

text\<open>

The following counterexample, due to \citet[\S3:
Example~2]{AygunSonmez:2012-WP2}, comprehensively demonstrates that
\citet[Theorem~1]{HatfieldMilgrom:2005} does not hold.

We create three types: \<open>D2\<close> consists of two elements,
representing the doctors, and \<open>H\<close> is the type of the single
hospital. There are four contracts in the type \<open>X4\<close>.

\<close>

datatype D2 = D1 | D2
datatype H1 = H
datatype X4 = Xd1 | Xd1' | Xd2 | Xd2'
(*<*)

lemma D2_UNIV:
  shows "UNIV = set [D1, D2]"
using D2.exhaust by auto

instantiation D2 :: enum
begin

definition "enum_class.enum = [D1, D2]"
definition "enum_class.enum_all P = (P D1 \<and> P D2)"
definition "enum_class.enum_ex P = (P D1 \<or> P D2)"

instance
by standard (simp_all add: enum_D2_def enum_all_D2_def enum_ex_D2_def D2_UNIV)

end

lemma D2_ALL:
  shows "(\<forall>d. P d) = (\<forall>d\<in>{D1, D2}. P d)"
using D2_UNIV by auto

lemma D2_UNION:
  shows "(\<Union>d. P d) = (\<Union>d\<in>{D1, D2}. P d)"
using D2_UNIV by auto

instance H1 :: finite
by standard (metis (full_types) H1.exhaust ex_new_if_finite finite.intros(1) finite_insert insert_subset subset_insertI)

lemma X4_UNIV:
  shows "UNIV = set [Xd1, Xd1', Xd2, Xd2']"
using X4.exhaust by auto

lemmas X4_pow = subset_subseqs[OF subset_trans[OF subset_UNIV Set.equalityD1[OF X4_UNIV]]]

instance X4 :: finite
by standard (simp add: X4_UNIV)

lemma X4_ALL:
  shows "(\<forall>X''. P X'') \<longleftrightarrow> (\<forall>X''\<in>set ` set (subseqs [Xd1, Xd1', Xd2, Xd2']). P X'')"
using X4_pow by blast

(*>*)

primrec X4d :: "X4 \<Rightarrow> D2" where
  "X4d Xd1 = D1"
| "X4d Xd1' = D1"
| "X4d Xd2 = D2"
| "X4d Xd2' = D2"

abbreviation X4h :: "X4 \<Rightarrow> H1" where
  "X4h _ \<equiv> H"

primrec PX4d :: "D2 \<Rightarrow> X4 rel" where
  "PX4d D1 = linord_of_list [Xd1', Xd1]"
| "PX4d D2 = linord_of_list [Xd2, Xd2']"

function CX4h :: "H1 \<Rightarrow> X4 cfun" where
  "CX4h _ {Xd1} = {Xd1}"
| "CX4h _ {Xd1'} = {Xd1'}"
| "CX4h _ {Xd2} = {Xd2}"
| "CX4h _ {Xd2'} = {Xd2'}"
| "CX4h _ {Xd1, Xd1'} = {Xd1}"
| "CX4h _ {Xd1, Xd2} = {Xd1, Xd2}"
| "CX4h _ {Xd1, Xd2'} = {Xd2'}"
| "CX4h _ {Xd1', Xd2} = {Xd1'}"
| "CX4h _ {Xd1', Xd2'} = {Xd1', Xd2'}"
| "CX4h _ {Xd2, Xd2'} = {Xd2}"
| "CX4h _ {Xd1, Xd1', Xd2} = {}"
| "CX4h _ {Xd1, Xd1', Xd2'} = {}"
| "CX4h _ {Xd1, Xd2, Xd2'} = {}"
| "CX4h _ {Xd1', Xd2, Xd2'} = {}"
| "CX4h _ {Xd1, Xd1', Xd2, Xd2'} = {}"
| "CX4h _ {} = {}"
apply %invisible (case_tac x)
apply (cut_tac X=b in X4_pow)
apply auto
done
(*<*)

termination by %invisible lexicographic_order

lemma PX4d_linear:
  shows "Linear_order (PX4d d)"
by (cases d) (simp_all add: linord_of_list_Linear_order)

lemma PX4d_range:
  shows "Field (PX4d d) \<subseteq> {x. X4d x = d}"
by (cases d) simp_all

lemma CX4h_range:
  shows "CX4h h X \<subseteq> {x \<in> X. H = h}"
by (cases "(h, X)" rule: CX4h.cases) (auto simp: spec[OF H1.nchotomy, of h])

lemma CX4h_singular:
  shows "inj_on X4d (CX4h h X)"
by (cases "(h, X)" rule: CX4h.cases) auto

(*>*)
text\<open>\<close>

interpretation StableNoDecomp: Contracts X4d X4h PX4d CX4h
using %invisible PX4d_linear PX4d_range CX4h_range CX4h_singular by unfold_locales blast+

text\<open>

There are two stable matches in this model.

\<close>
(*<*)

lemma Xd1_Xd2_stable:
  shows "StableNoDecomp.stable {Xd1, Xd2}"
proof(rule StableNoDecomp.stable_onI)
  show "StableNoDecomp.individually_rational {Xd1, Xd2}"
    by (simp add: StableNoDecomp.individually_rational_on_def StableNoDecomp.CD_on_def
      StableNoDecomp.CH_def insert_commute D2_UNION cong add: SUP_cong_simp)
  show "StableNoDecomp.stable_no_blocking {Xd1, Xd2}"
    apply (rule StableNoDecomp.stable_no_blocking_onI)
    apply (rule_tac x="(H, X'')" in CX4h.cases)
    apply (simp_all add: insert_commute)
    done
qed

lemma Xd1'_Xd2'_stable:
  shows "StableNoDecomp.stable {Xd1', Xd2'}"
proof(rule StableNoDecomp.stable_onI)
  show "StableNoDecomp.individually_rational {Xd1', Xd2'}"
    by (simp add: StableNoDecomp.individually_rational_on_def StableNoDecomp.CD_on_def
      StableNoDecomp.CH_def insert_commute D2_UNION cong add: SUP_cong_simp)
  show "StableNoDecomp.stable_no_blocking {Xd1', Xd2'}"
    apply (rule StableNoDecomp.stable_no_blocking_onI)
    apply (rule_tac x="(H, X'')" in CX4h.cases)
    apply (simp_all add: insert_commute)
    done
qed

(*>*)
text\<open>\<close>

lemma stable:
  shows "StableNoDecomp.stable X \<longleftrightarrow> X = {Xd1, Xd2} \<or> X = {Xd1', Xd2'}"
(*<*)
(is "?lhs = ?rhs")
proof(rule iffI)
  assume ?lhs then show ?rhs
    using X4_pow[where X=X]
    unfolding StableNoDecomp.stable_on_def StableNoDecomp.individually_rational_on_def
              StableNoDecomp.stable_no_blocking_on_def StableNoDecomp.blocking_on_def
              StableNoDecomp.CD_on_def StableNoDecomp.CH_def
    by simp (elim disjE, simp_all add: D2_UNION X4_ALL insert_commute StableNoDecomp.maxR_def cong add: SUP_cong_simp)
next
  assume ?rhs then show ?lhs
    using Xd1_Xd2_stable Xd1'_Xd2'_stable by blast
qed
(*>*)

text\<open>

However neither arises from a pair \<open>XD, XH\<close> that satisfy
@{const "StableNoDecomp.stable_pair"}:

\<close>

lemma StableNoDecomp_XD_XH:
  shows "StableNoDecomp.stable_pair (XD, XH) \<longleftrightarrow> (XD = {} \<and> XH = {Xd1, Xd1', Xd2, Xd2'})"
(*<*)
(is "?lhs = ?rhs")
proof(rule iffI)
  note image_cong_simp [cong del] note INF_cong_simp [cong] note SUP_cong_simp [cong]
  assume ?lhs then show ?rhs (* Expand the Cartesian product and check. *)
  using X4_pow [of XD] X4_pow [of XH]
    apply simp
    apply (erule StableNoDecomp.stable_pair_onE)
    apply (elim disjE)
    apply (simp_all add: StableNoDecomp.CD_on_def StableNoDecomp.CH_def)
    unfolding X4_UNIV [simplified]
    apply (auto simp: D2_ALL D2_UNION X4_ALL insert_commute StableNoDecomp.maxR_def linord_of_list_linord_of_listP)
    done
next
  assume ?rhs then show ?lhs
    unfolding StableNoDecomp.stable_pair_on_def using X4.exhaust by (auto simp: StableNoDecomp.CH_def)
qed

(*>*)
text\<open>\<close>

proposition
  assumes "StableNoDecomp.stable_pair (XD, XH)"
  shows "\<not>StableNoDecomp.stable (XD \<inter> XH)"
using %invisible assms
apply (subst (asm) StableNoDecomp_XD_XH)
apply (simp add: StableNoDecomp.stable_on_def StableNoDecomp.stable_no_blocking_on_def StableNoDecomp.blocking_on_def StableNoDecomp.individually_rational_on_empty)
apply (auto simp: StableNoDecomp.mem_CD_on_Cd MaxR_def exI[where x=D1] exI[where x=H] exI[where x="{Xd1}"])
done

text\<open>

Moreover the converse of Theorem~1 does not hold either: the single
decomposition that satisfies @{const "StableNoDecomp.stable_pair"} (@{thm
[source] "StableNoDecomp_XD_XH"}) does not yield a stable match:

\<close>

proposition
  assumes "StableNoDecomp.stable X"
  shows "\<not>(\<exists>XD XH. StableNoDecomp.stable_pair (XD, XH) \<and> X = XD \<inter> XH)"
using %invisible assms StableNoDecomp_XD_XH stable by fastforce

text\<open>

So there is not hope for \citet[Theorem~1]{HatfieldMilgrom:2005} as it
stands. Note that the counterexample satisfies the @{const "substitutes"}
condition (see \S\ref{sec:cf-substitutes}):

\<close>

lemma
  shows "substitutes (CX4h H)"
proof %invisible (rule substitutes_onI)
  fix A a b assume "b \<notin> CX4h H (insert b A)"
  then show "b \<notin> CX4h H (insert a (insert b A))"
    apply (case_tac [!] a)
    apply (case_tac [!] b)
    apply ( (rule CX4h.cases[of "(H, A)"], auto simp: insert_commute)[1] )+
    done
qed

text\<open>

Therefore while @{const "substitutes"} supports the monotonicity argument
that underpins their deferred-acceptance algorithm (see
\S\ref{sec:contracts-algorithmics}), it is not enough to rescue
Theorem~1. One way forward is to constrain the hospitals'
choice functions, which we discuss in the next section.

\<close>


subsubsection\<open> Theorem 1 holds with @{emph \<open>independence of rejected contracts\<close>} \label{sec:contracts-irc} \<close>

text\<open>

\citet{AygunSonmez:2012-WP2} propose to rectify this issue by
requiring hospitals' choices to satisfy @{const "irc"}
(\S\ref{sec:cf-irc}). Reassuringly their counterexample fails to
satisfy it:

\<close>

lemma
  shows "\<not>irc (CX4h H)"
by %invisible (fastforce simp: insert_commute dest: irc_onD[where a="Xd2" and B="{Xd1, Xd1'}"])

text\<open>

We adopt this hypothesis by extending the @{const "Contracts"} locale:

\<close>

locale ContractsWithIRC = Contracts +
  assumes Ch_irc: "\<forall>h. irc (Ch h)"
begin

text\<open>

This property requires that \<open>Ch\<close> behave, for example, as
follows:

\<close>

lemma Ch_domain:
  shows "Ch h (A \<inter> {x. Xh x = h}) = Ch h A"
using %invisible irc_on_discard[OF spec[OF Ch_irc, of h], where B="A \<inter> {x. Xh x = h}" and C="A - {x. Xh x = h}"]
by (fastforce simp: Un_Diff_Int ac_simps dest: Ch_range')

lemma %invisible CH_domain:
  shows "CH A \<inter> {x. Xh x = h} = Ch h (A \<inter> {x. Xh x = h})"
unfolding CH_def using Ch_range by (auto simp: Ch_domain)

lemma %invisible stable_pair_on_Ch:
  assumes "stable_pair_on ds XD_XH"
  shows "Ch h (snd XD_XH) = match XD_XH \<inter> {x. Xh x = h}"
using stable_pair_on_CH[OF assms] CH_domain Ch_domain by simp

lemmas %invisible Ch_consistency = irc_on_consistency_on[OF spec[OF Ch_irc], simplified, of h] for h

lemmas Ch_irc_idem = consistency_on_f_idem[OF Ch_f_range Ch_consistency, simplified]

lemma CH_irc_idem:
  shows "CH (CH A) = CH A"
unfolding %invisible CH_def by (metis CH_def CH_domain Ch_domain Ch_irc_idem)

lemma Ch_CH_irc_idem:
  shows "Ch h (CH A) = Ch h A"
using %invisible CH_domain CH_irc_idem Ch_domain by blast

text\<open>

This suffices to show the left-to-right direction of Theorem~1.

\<close>

lemma stable_pair_on_individually_rational:
  assumes "stable_pair_on ds XD_XH"
  shows "individually_rational_on ds (match XD_XH)"
by %invisible (metis CD_on_idem CH_irc_idem stable_pair_on_CD_on stable_pair_on_CD_on_CH assms individually_rational_onI)

lemma stable_pair_on_stable_no_blocking_on:
  assumes "stable_pair_on ds XD_XH"
  shows "stable_no_blocking_on ds (match XD_XH)"
proof(rule stable_no_blocking_onI)
  fix h X''
  assume C: "X'' = Ch h (match XD_XH \<union> X'')"
  assume NE: "X'' \<noteq> Ch h (match XD_XH)"
  assume CD: "X'' \<subseteq> CD_on ds (match XD_XH \<union> X'')"
  have "X'' \<subseteq> snd XD_XH"
  proof -
    from CD have "X'' \<subseteq> CD_on ds (CD_on ds (fst XD_XH) \<union> X'')" by (simp only: stable_pair_on_CD_on[OF assms])
    then have "X'' \<subseteq> CD_on ds (fst XD_XH \<union> X'')"
      using CD_on_path_independent unfolding path_independent_def by (simp add: Un_commute)
    moreover have "fst XD_XH \<inter> CD_on ds (fst XD_XH \<union> X'') \<subseteq> CD_on ds (fst XD_XH)"
      using CD_on_Chernoff unfolding Chernoff_on_def by (simp add: inf_commute)
    ultimately show ?thesis using assms unfolding stable_pair_on_def split_def by blast
  qed
  then have "Ch h (snd XD_XH) = Ch h (Ch h (snd XD_XH) \<union> X'')"
    by (force intro!: consistencyD[OF Ch_consistency] dest: Ch_range')
  moreover from NE have "X'' \<noteq> Ch h (snd XD_XH)"
    using stable_pair_on_CH[OF assms] CH_domain[of _ h] Ch_domain[of h] by (metis Ch_irc_idem)
  ultimately have "X'' \<noteq> Ch h (match XD_XH \<union> X'')"
    using stable_pair_on_CH[OF assms] CH_domain[of _ h] Ch_domain[of h]
    by (metis (no_types, lifting) inf.right_idem inf_sup_distrib2)
  with C show False by blast
qed

theorem stable_pair_on_stable_on:
  assumes "stable_pair_on ds XD_XH"
  shows "stable_on ds (match XD_XH)"
using %invisible assms stable_pair_on_allocation stable_pair_on_individually_rational stable_pair_on_stable_no_blocking_on
by (blast intro: stable_onI)

end


subsubsection\<open> The converse of Theorem~1 \label{sec:contracts-t1-converse} \<close>

text (in Contracts) \<open>

The forward direction of Theorem~1 gives us a way of finding stable
matches by computing fixed points of a function closely related to
@{const "stable_pair"} (see \S\ref{sec:contracts-algorithmics}). The
converse says that every stable match can be decomposed in this way,
which implies that the stable matches form a lattice (see also
\S\ref{sec:contracts-algorithmics}).

The following proofs assume that the hospitals' choice functions
satisfy @{const "substitutes"} and @{const "irc"}.

\<close>

context ContractsWithIRC
begin

context
  fixes ds :: "'b set"
  fixes X :: "'a set"
begin

text\<open>

Following \citet[Proof of Theorem~1]{HatfieldMilgrom:2005}, we
partition the set of all contracts into @{term "[X, XD_smallest - X,
XH_largest - X]"} with careful definitions of the two sets @{term
"XD_smallest"} and @{term "XH_largest"}. Specifically @{term
"XH_largest"} contains all contracts ranked at least as good as those
in @{term "X"} by the doctors, considering unemployment and
unacceptable contracts. Similarly @{term "XD_smallest"} contains those
ranked at least as poorly.

\<close>

definition XH_largest :: "'a set" where
  "XH_largest =
     {y. Xd y \<in> ds
       \<and> y \<in> Field (Pd (Xd y))
       \<and> (\<forall>x \<in> dX X (Xd y). (x, y) \<in> Pd (Xd y))}"

definition XD_smallest :: "'a set" where
  "XD_smallest = - (XH_largest - X)"

context
  assumes "stable_on ds X"
begin

lemma Ch_XH_largest_Field:
  assumes "x \<in> Ch h XH_largest"
  shows "x \<in> Field (Pd (Xd x))"
using assms unfolding XH_largest_def by (blast dest: Ch_range')

lemma Ch_XH_largest_Xd:
  assumes "x \<in> Ch h XH_largest"
  shows "Xd x \<in> ds"
using assms unfolding XH_largest_def by (blast dest: Ch_range')

lemma X_subseteq_XH_largest:
  shows "X \<subseteq> XH_largest"
proof(rule subsetI)
  fix x assume "x \<in> X"
  then obtain d where "d \<in> ds" "x \<in> Cd d X" using stable_on_CD_on[OF \<open>stable_on ds X\<close>] unfolding CD_on_def by blast
  with \<open>stable_on ds X\<close> show "x \<in> XH_largest"
    using Pd_linear' Pd_range' Cd_range subset_Image1_Image1_iff[of "Pd d"] stable_on_allocation[of ds X]
    unfolding XH_largest_def linear_order_on_def partial_order_on_def stable_on_def inj_on_def dX_def
    by simp blast
qed

lemma X_subseteq_XD_smallest:
  shows "X \<subseteq> XD_smallest"
unfolding XD_smallest_def by blast

lemma X_XD_smallest_XH_largest:
  shows "X = XD_smallest \<inter> XH_largest"
using X_subseteq_XH_largest unfolding XD_smallest_def by blast

text\<open>

The goal of the next few lemmas is to show the constituents of @{term
"stable_pair_on ds (XD_smallest, XH_largest)"}.

Intuitively, if a doctor has a contract @{term "x"} in @{term "X"},
then all of their contracts in @{const "XH_largest"} are at least as
desirable as @{term "x"}, and so the @{const
"stable_no_blocking"} hypothesis guarantees the hospitals choose
@{term "x"} from @{const "XH_largest"}, and similarly the doctors
@{term "x"} from @{const "XD_smallest"}.

\<close>

lemma XH_largestCdXXH_largest:
  assumes "x \<in> Ch h XH_largest"
  shows "x \<in> Cd (Xd x) (X \<union> Ch h XH_largest)"
proof -
  from assms have "(y, x) \<in> Pd (Xd x)" if "Xd y = Xd x" and "y \<in> X" for y
    using that by (fastforce simp: XH_largest_def dX_def dest: Ch_range')
  with Ch_XH_largest_Field[OF assms] Pd_linear Pd_range show ?thesis
    using assms Ch_XH_largest_Field[OF assms]
    by (clarsimp simp: Cd_greatest greatest_def)
       (metis Ch_singular Pd_range' inj_onD subset_refl underS_incl_iff)
qed

lemma CH_XH_largest:
  shows "CH XH_largest = X"
proof -
  have "Ch h XH_largest \<subseteq> CD_on ds (X \<union> Ch h XH_largest)" for h
    using XH_largestCdXXH_largest Ch_XH_largest_Xd Ch_XH_largest_Field unfolding CD_on_def by blast
  from \<open>stable_on ds X\<close> have "Ch h XH_largest = Ch h X" for h
    using \<open>Ch h XH_largest \<subseteq> CD_on ds (X \<union> Ch h XH_largest)\<close> X_subseteq_XH_largest
    by - (erule stable_on_blocking_onD[where h=h and X''="Ch h XH_largest"];
          force intro!: consistencyD[OF Ch_consistency] dest: Ch_range')
  with stable_on_CH[OF \<open>stable_on ds X\<close>] show ?thesis unfolding CH_def by simp
qed

lemma Cd_XD_smallest:
  assumes "d \<in> ds"
  shows "Cd d (XD_smallest \<inter> Field (Pd d)) = Cd d (X \<inter> Field (Pd d))"
proof(cases "X \<inter> Field (Pd d) = {}")
  case True
  with Pd_range' Cd_range'[where X=X] stable_on_CD_on[OF \<open>stable_on ds X\<close>] mem_CD_on_Cd assms
  have "- XH_largest \<inter> Field (Pd d) = {}"
    unfolding XH_largest_def dX_def by auto blast
  then show ?thesis
    unfolding XD_smallest_def by (simp add: Int_Un_distrib2)
next
  case False
  with Pd_linear'[of d] \<open>stable_on ds X\<close> stable_on_CD_on stable_on_allocation assms
  show ?thesis
    unfolding XD_smallest_def order_on_defs total_on_def
    by (auto 0 0 simp: Int_Un_distrib2 Cd_greatest greatest_def XH_largest_def dX_def)
       (metis (mono_tags, lifting) IntI Pd_range' UnCI inj_onD)+
qed

lemma CD_on_XD_smallest:
  shows "CD_on ds XD_smallest = X"
using stable_on_CD_on[OF \<open>stable_on ds X\<close>] unfolding CD_on_def2 by (simp add: Cd_XD_smallest)

theorem stable_on_stable_pair_on:
  shows "stable_pair_on ds (XD_smallest, XH_largest)"
proof(rule stable_pair_onI, simp_all only: prod.sel)
  from CH_XH_largest have "- RH XH_largest = - (XH_largest - X)" by blast
  also from X_XD_smallest_XH_largest have "\<dots> = XD_smallest" unfolding XD_smallest_def by blast
  finally show "XD_smallest = -RH XH_largest" by blast
next
  from CD_on_XD_smallest have "-RD_on ds XD_smallest = -(XD_smallest - X)" by simp
  also have "\<dots> = XH_largest" unfolding XD_smallest_def using X_subseteq_XH_largest by blast
  finally show "XH_largest = -RD_on ds XD_smallest" by blast
qed

end

end

text\<open>

Our ultimate statement of Theorem~1 of \cite{HatfieldMilgrom:2005} ala
\citet{AygunSonmez:2012-WP2} goes as follows, bearing in mind that we
are working in the @{const "ContractsWithIRC"} locale:

\<close>

theorem T1:
  shows "stable_on ds X \<longleftrightarrow> (\<exists>XD_XH. stable_pair_on ds XD_XH \<and> X = match XD_XH)"
using stable_pair_on_stable_on stable_on_stable_pair_on X_XD_smallest_XH_largest by fastforce

end


subsection\<open> Theorem~3: Algorithmics \label{sec:contracts-algorithmics} \<close>

text (in Contracts) \<open>

Having revived Theorem~1, we reformulate @{const "stable_pair"} as a
monotone (aka @{emph \<open>isotone\<close>}) function and exploit the lattice
structure of its fixed points, following \citet[{\S}II,
Theorem~3]{HatfieldMilgrom:2005}. This underpins all of their results
that we formulate here. \citet[\S2]{Fleiner:2002} provides an
intuitive gloss of these definitions.

\<close>

context Contracts
begin

definition F1 :: "'x cfun" where
  "F1 X' = - RH X'"

definition F2 :: "'d set \<Rightarrow> 'x cfun" where
  "F2 ds X' = - RD_on ds X'"

definition F :: "'d set \<Rightarrow> 'x set \<times> 'x set dual \<Rightarrow> 'x set \<times> 'x set dual" where
  "F ds = (\<lambda>(XD, XH). (F1 (undual XH), dual (F2 ds (F1 (undual XH)))))"

text\<open>

We exploit Isabelle/HOL's ordering type classes (over the type
constructors @{typ "'a set"} and @{typ "'a \<times> 'b"}) to define
@{const "F"}. As @{const "F"} is @{const "antimono"} (where @{thm
"antimono_def"} for a lattice order \<open>\<le>\<close>) on its
second argument \<open>XH\<close>, we adopt the dual lattice order
using the type constructor @{typ "'a dual"}, where @{const "dual"} and
@{const "undual"} mediate the isomorphism on values, to satisfy
Isabelle/HOL's @{const "mono"} predicate. Note we work under the
@{const "substitutes"} hypothesis here.

Relating this function to @{const "stable_pair"} is syntactically
awkward but straightforward:

\<close>

lemma fix_F_stable_pair_on:
  assumes "X = F ds X"
  shows "stable_pair_on ds (map_prod id undual X)"
  using %invisible assms
  by (cases X) (simp add: F_def F1_def F2_def stable_pair_on_def dual_eq_iff)

lemma stable_pair_on_fix_F:
  assumes "stable_pair_on ds X"
  shows "map_prod id dual X = F ds (map_prod id dual X)"
using %invisible assms
unfolding F_def F1_def F2_def stable_pair_on_def split_def
by (metis fst_map_prod id_apply prod.collapse snd_map_prod undual_dual)

end

text (in Contracts) \<open>

The function @{const F} is monotonic under @{const substitutes}.

\<close>

locale ContractsWithSubstitutes = Contracts +
  assumes Ch_substitutes: "\<forall>h. substitutes (Ch h)"
begin

(*<*)

lemma Rh_mono:
  shows "mono (Rh h)"
using %invisible substitutes_on_Rf_mono_on[OF spec[OF Ch_substitutes]] mono_on_mono by (simp add: fun_eq_iff) blast

lemmas Ch_iia = Rh_mono[unfolded Rf_mono_iia]
lemmas Ch_Chernoff = Ch_iia[unfolded Chernoff_on_iia_on[symmetric]]
lemmas Ch_subsitutes_idem = iia_f_idem[OF Ch_f_range Ch_iia, simplified]

lemma RH_mono:
  shows "mono RH"
unfolding %invisible CH_def by (rule monoI) (auto dest: monoD[OF Rh_mono])

lemmas CH_iia = RH_mono[unfolded Rf_mono_iia]
lemmas CH_Chernoff = CH_iia[unfolded Chernoff_on_iia_on[symmetric]]
lemmas CH_substitutes_idem = iia_f_idem[OF CH_f_range_on CH_iia, simplified]

(*>*)
text\<open>\<close>

lemma F1_antimono:
  shows "antimono F1"
by %invisible (rule antimonoI) (auto simp: F1_def dest: Diff_mono[OF _ monoD[OF RH_mono]])

lemma F2_antimono:
  shows "antimono (F2 ds)"
by %invisible (rule antimonoI) (auto simp: F2_def dest: Diff_mono[OF _ monoD[OF RD_on_mono]])

lemma F_mono:
  shows "mono (F ds)"
unfolding %invisible F_def using antimonoD[OF F1_antimono] antimonoD[OF F2_antimono]
by (auto intro: monoI simp: less_eq_dual_def)

text\<open>

We define the extremal fixed points using Isabelle/HOL's least and
greatest fixed point operators:

\<close>

definition gfp_F :: "'b set \<Rightarrow> 'a set \<times> 'a set" where
  "gfp_F ds = map_prod id undual (gfp (F ds))"

definition lfp_F :: "'b set \<Rightarrow> 'a set \<times> 'a set" where
  "lfp_F ds = map_prod id undual (lfp (F ds))"

lemmas gfp_F_stable_pair_on = fix_F_stable_pair_on[OF gfp_unfold[OF F_mono], folded gfp_F_def]
lemmas lfp_F_stable_pair_on = fix_F_stable_pair_on[OF lfp_unfold[OF F_mono], folded lfp_F_def]

text\<open>

These last two lemmas show that the least and greatest fixed points do
satisfy @{const "stable_pair"}.

Using standard fixed-point properties, we can establish:

\<close>

lemma F2_o_F1_mono:
  shows "mono (F2 ds \<circ> F1)"
by %invisible (metis F2_antimono F1_antimono antimono_def comp_apply monoI)

lemmas F2_F1_mono = F2_o_F1_mono[unfolded o_def]

lemma gfp_F_lfp_F:
  shows "gfp_F ds = (F1 (lfp (F2 ds \<circ> F1)), lfp (F2 ds \<circ> F1))"
proof %invisible -
  let ?F' = "dual \<circ> F2 ds \<circ> F1 \<circ> undual"
  have "gfp (F ds) = (F1 (undual (gfp ?F')), gfp ?F')"
    by (subst gfp_prod[OF F_mono]) (simp add: F_def o_def gfp_const)
  also have "gfp ?F' = dual (lfp (F2 ds \<circ> F1))"
    by (simp add: lfp_dual_gfp[OF F2_o_F1_mono, simplified o_assoc])
  finally show ?thesis unfolding gfp_F_def by simp
qed

end

text\<open>

We need hospital CFs to satisfy both @{const substitutes} and @{const irc}
to relate these fixed points to stable matches.

\<close>

locale ContractsWithSubstitutesAndIRC =
  ContractsWithSubstitutes + ContractsWithIRC
begin

lemmas gfp_F_stable_on = stable_pair_on_stable_on[OF gfp_F_stable_pair_on]
lemmas lfp_F_stable_on = stable_pair_on_stable_on[OF lfp_F_stable_pair_on]

end

text\<open>

\label{sec:contracts-codegen-gfp_F}

We demonstrate the effectiveness of our definitions by executing an
example due to \citet[p920]{HatfieldMilgrom:2005} using Isabelle/HOL's
code generator \citep{Haftmann-Nipkow:2010:code}. Note that, while
adequate for this toy instance, the representations used here are
hopelessly n{\"a}ive: sets are represented by lists and operations
typically traverse the entire contract space. It is feasible, with
more effort, to derive efficient algorithms; see, for instance,
\citet{Bijlsma:1991,Bulwahn-et-al:2008:imp_HOL}.

\<close>

context ContractsWithSubstitutes
begin

lemma gfp_F_code[code]:
  shows "gfp_F ds = map_prod id undual (while (\<lambda>A. F ds A \<noteq> A) (F ds) top)"
using %invisible gfp_F_def gfp_while_lattice[OF F_mono] by simp

lemma lfp_F_code[code]:
  shows "lfp_F ds = map_prod id undual (while (\<lambda>A. F ds A \<noteq> A) (F ds) bot)"
using %invisible lfp_F_def lfp_while_lattice[OF F_mono] by simp

end

text\<open>

There are two hospitals and two doctors.

\<close>

datatype H2 = H1 | H2

text\<open>

The contract space is simply the Cartesian product @{typ "D2 \<times>
H2"}.

\<close>

type_synonym X_D2_H2 = "D2 \<times> H2"

text\<open>

Doctor @{const "D1"} prefers \<open>H1 \<succ> H2\<close>, doctor @{const
"D2"} the same \<open>H1 \<succ> H2\<close> (but over different
contracts).

\<close>

primrec P_D2_H2_d :: "D2 \<Rightarrow> X_D2_H2 rel" where
  "P_D2_H2_d D1 = linord_of_list [(D1, H1), (D1, H2)]"
| "P_D2_H2_d D2 = linord_of_list [(D2, H1), (D2, H2)]"

text\<open>

Hospital @{const "H1"} prefers \<open>{D1} \<succ> {D2} \<succ>
\<emptyset>\<close>, and hospital @{const "H2"} \<open>{D1, D2}
\<succ> {D1} \<succ> {D2} \<succ> \<emptyset>\<close>. We interpret
these constraints as follows:

\<close>

definition P_D2_H2_H1 :: "X_D2_H2 cfun" where
  "P_D2_H2_H1 A = (if (D1, H1) \<in> A then {(D1, H1)} else if (D2, H1) \<in> A then {(D2, H1)} else {})"

definition P_D2_H2_H2 :: "X_D2_H2 cfun" where
  "P_D2_H2_H2 A =
     (if {(D1, H2), (D2, H2)} \<subseteq> A then {(D1, H2), (D2, H2)} else
      if (D1, H2) \<in> A then {(D1, H2)} else if (D2, H2) \<in> A then {(D2, H2)} else {})"

primrec P_D2_H2_h :: "H2 \<Rightarrow> X_D2_H2 cfun" where
  "P_D2_H2_h H1 = P_D2_H2_H1"
| "P_D2_H2_h H2 = P_D2_H2_H2"
(*<*)

lemma H2_UNIV:
  shows "UNIV = set [H1, H2]"
using H2.exhaust by auto

instantiation H2 :: enum
begin

definition "enum_class.enum = [H1, H2]"
definition "enum_class.enum_all P = (P H1 \<and> P H2)"
definition "enum_class.enum_ex P = (P H1 \<or> P H2)"

instance
by standard (simp_all add: enum_H2_def enum_all_H2_def enum_ex_H2_def H2_UNIV)

end

lemma H2_ALL [simp]:
  shows "(\<forall>h. P h) = (\<forall>h\<in>{H1, H2}. P h)"
using H2_UNIV by auto

lemma H2_UNION:
  shows "(\<Union>h. P h) = (\<Union>h\<in>{H1, H2}. P h)"
using H2_UNIV by auto

lemma P_D2_H2_d_linear:
  shows "Linear_order (P_D2_H2_d d)"
by (cases d) (simp_all add: linord_of_list_Linear_order)

lemma P_D2_H2_d_range:
  shows "Field (P_D2_H2_d d) \<subseteq> {x. fst x = d}"
by (cases d) simp_all

lemma P_D2_H2_h_substitutes:
  shows "substitutes (P_D2_H2_h h)"
by %invisible (cases h) (auto intro!: substitutes_onI simp: P_D2_H2_H1_def P_D2_H2_H2_def split: if_splits)

(*>*)
text\<open>

Isabelle's code generator requires us to hoist the relevant
definitions from the locale to the top-level (see the \verb!codegen!
documentation, \S7.3).

\<close>

global_interpretation P920_example:
  ContractsWithSubstitutes fst snd P_D2_H2_d P_D2_H2_h
defines P920_example_gfp_F = P920_example.gfp_F
    and P920_example_lfp_F = P920_example.lfp_F
    and P920_example_F = P920_example.F
    and P920_example_F1 = P920_example.F1
    and P920_example_F2 = P920_example.F2
    and P920_example_maxR = P920_example.maxR
    and P920_example_MaxR_f = P920_example.MaxR_f
    and P920_example_Cd = P920_example.Cd
    and P920_example_CD_on = P920_example.CD_on
    and P920_example_CH = P920_example.CH
using %invisible P_D2_H2_d_linear P_D2_H2_h_substitutes
by %invisible unfold_locales (simp_all, simp_all add: D2_ALL P_D2_H2_H1_def P_D2_H2_H2_def)

(*<*)

(*

Codegen hackery: avoid the CoSet constructor as some operations do not
handle it.

*)

declare UNIV_coset[code del]
declare UNIV_enum[code]

declare compl_set[code del] compl_coset[code del]
declare Compl_eq_Diff_UNIV[code]

(*
code_thms P920_example_gfp_F
export_code P920_example_gfp_F in SML module_name F file "F.sml"
value "P920_example_gfp_F UNIV"
*)

lemma P920_example_gfp_F_value:
  shows "P920_example_gfp_F UNIV = ({(D1, H1), (D1, H2), (D2, H2)}, {(D1, H1), (D2, H1), (D2, H2)})"
by eval

lemma P920_example_gfp_F_match_value:
  shows "P920_example.match (P920_example_gfp_F UNIV) = {(D1, H1), (D2, H2)}"
unfolding P920_example_gfp_F_value by simp

lemma P920_example_lfp_F_value:
  shows "P920_example_lfp_F UNIV = ({(D1, H1), (D1, H2), (D2, H2)}, {(D1, H1), (D2, H1), (D2, H2)})"
by eval

(*>*)
text\<open>

We can now evaluate the @{const "gfp"} of @{const "P920_example.F"}
(i.e., \<open>F\<close> specialized to the above constants) using
Isabelle's \verb!value! antiquotation or \verb!eval! method. This
yields the \<open>(XD, XH)\<close> pair:

\begin{center}
  @{thm (rhs) "P920_example_gfp_F_value"}
\end{center}

The stable match is therefore @{thm (rhs) "P920_example_gfp_F_match_value"}.

The @{const "lfp"} of @{const "P920_example.F"} is identical to the
@{const "gfp"}:

\begin{center}
  @{thm (rhs) "P920_example_lfp_F_value"}
\end{center}

This implies that there is only one stable match in this scenario.

\<close>


subsection\<open> Theorem~4: Optimality \label{sec:contracts-optimality} \<close>

text (in ContractsWithSubstitutes) \<open>

\citet[Theorem~4]{HatfieldMilgrom:2005} assert that the greatest fixed
point @{const "gfp_F"} of @{const "F"} yields the stable match most
preferred by the doctors in the following sense:

\<close>

context Contracts
begin

definition doctor_optimal_match :: "'d set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "doctor_optimal_match ds Y
    \<longleftrightarrow> (stable_on ds Y \<and> (\<forall>X. \<forall>x\<in>X. stable_on ds X \<longrightarrow> (\<exists>y \<in> Y. (x, y) \<in> Pd (Xd x))))"

(*<*)

lemmas doctor_optimal_matchI = iffD2[OF doctor_optimal_match_def, unfolded conj_imp_eq_imp_imp, rule_format]
lemmas doctor_optimal_match_stable_on = iffD1[OF doctor_optimal_match_def, THEN conjunct1]
lemmas doctor_optimal_match_optimal = iffD1[OF doctor_optimal_match_def, THEN conjunct2, rule_format]

lemma doctor_optimal_match_unique:
  assumes "doctor_optimal_match ds X"
  assumes "doctor_optimal_match ds Y"
  shows "X = Y"
proof(rule iffD2[OF set_eq_iff, rule_format])
  fix x
  from Pd_linear'[where d="Xd x"] Pd_Xd[where d="Xd x"]
       stable_on_allocation[OF doctor_optimal_match_stable_on[OF assms(1)]]
       stable_on_allocation[OF doctor_optimal_match_stable_on[OF assms(2)]]
       assms
  show "x \<in> X \<longleftrightarrow> x \<in> Y"
    unfolding doctor_optimal_match_def order_on_defs
      by - (rule iffI; metis antisymD inj_on_eq_iff)
qed

(*>*)

end

text (in ContractsWithSubstitutes) \<open>

In a similar sense, @{const "lfp_F"} is the doctor-pessimal match.

We state a basic doctor-optimality result in terms of @{const
"stable_pair"} in the @{const "ContractsWithSubstitutes"} locale for
generality; we can establish @{const "doctor_optimal_match"} only
under additional constraints on hospital choice functions (see
\S\ref{sec:contracts-irc}).

\<close>

context ContractsWithSubstitutes
begin

context
  fixes XD_XH :: "'a set \<times> 'a set"
  fixes ds :: "'b set"
  assumes "stable_pair_on ds XD_XH"
begin

lemma gfp_F_upperbound:
  shows "(fst XD_XH, dual (snd XD_XH)) \<le> gfp (F ds)"
proof %invisible -
  have "(fst XD_XH, dual (snd XD_XH)) = F ds (fst XD_XH, dual (snd XD_XH))"
    using stable_pair_on_fix_F[OF \<open>stable_pair_on ds XD_XH\<close>] by (metis id_apply map_prod_simp prod.collapse)
  then show ?thesis by (fastforce intro: gfp_upperbound)
qed

lemma XD_XH_gfp_F:
  shows "fst XD_XH \<subseteq> fst (gfp_F ds)"
    and "snd (gfp_F ds) \<subseteq> snd XD_XH"
using %invisible gfp_F_upperbound
unfolding gfp_F_def by (simp_all add: less_eq_dual_def less_eq_prod_def)

lemma lfp_F_upperbound:
  shows "lfp (F ds) \<le> (fst XD_XH, dual (snd XD_XH))"
proof %invisible -
  have "(fst XD_XH, dual (snd XD_XH)) = F ds (fst XD_XH, dual (snd XD_XH))"
    using stable_pair_on_fix_F[OF \<open>stable_pair_on ds XD_XH\<close>] by (metis id_apply map_prod_simp prod.collapse)
  then show ?thesis by (fastforce intro: lfp_lowerbound)
qed

lemma XD_XH_lfp_F:
  shows "fst (lfp_F ds) \<subseteq> fst XD_XH"
    and "snd XD_XH \<subseteq> snd (lfp_F ds)"
using %invisible lfp_F_upperbound
unfolding lfp_F_def by (simp_all add: less_eq_dual_def less_eq_prod_def)

text\<open>

We appeal to the doctors' linear preferences to show the optimality
(pessimality) of @{const "gfp_F"} (@{const "lfp_F"}) for doctors.

\<close>

theorem gfp_f_doctor_optimal:
  assumes "x \<in> match XD_XH"
  shows "\<exists>y \<in> match (gfp_F ds). (x, y) \<in> Pd (Xd x)"
using %invisible assms gfp_F_stable_pair_on[where ds=ds] \<open>stable_pair_on ds XD_XH\<close>
      stable_pair_on_CD_on stable_pair_on_Xd Cd_Xd mem_CD_on_Cd
      XD_XH_gfp_F(1) Cd_mono[where d="Xd x" and x=x and X="fst XD_XH" and Y="fst (gfp_F ds)"]
by (metis sup.absorb_iff2)

theorem lfp_f_doctor_pessimal:
  assumes "x \<in> match (lfp_F ds)"
  shows "\<exists>y \<in> match XD_XH. (x, y) \<in> Pd (Xd x)"
using %invisible assms lfp_F_stable_pair_on[where ds=ds] \<open>stable_pair_on ds XD_XH\<close>
      stable_pair_on_CD_on stable_pair_on_Xd Cd_Xd mem_CD_on_Cd
      XD_XH_lfp_F(1) Cd_mono[where d="Xd x" and x=x and X="fst (lfp_F ds)" and Y="fst XD_XH"]
by (metis sup.absorb_iff2)

end

end

theorem (in ContractsWithSubstitutesAndIRC) gfp_F_doctor_optimal_match:
  shows "doctor_optimal_match ds (match (gfp_F ds))"
by %invisible (rule doctor_optimal_matchI[OF gfp_F_stable_on]) (auto simp: T1 elim: gfp_f_doctor_optimal)

text (in ContractsWithSubstitutesAndIRC) \<open>

Conversely @{const "lfp_F"} is most preferred by the hospitals in a
revealed-preference sense, and @{const "gfp_F"} least preferred. These
results depend on @{thm [source] Ch_domain} and hence the @{const
"irc"} hypothesis on hospital choice functions.

\<close>

context ContractsWithSubstitutesAndIRC
begin

theorem lfp_f_hospital_optimal:
  assumes "stable_pair_on ds XD_XH"
  assumes "x \<in> Ch h (match (lfp_F ds))"
  shows "x \<in> Ch h (match (lfp_F ds) \<union> match XD_XH)"
proof %invisible -
  from \<open>stable_pair_on ds XD_XH\<close> have "match (lfp_F ds) \<union> match XD_XH \<subseteq> snd (lfp_F ds)"
    by (simp add: XD_XH_lfp_F(2) le_infI2)
  with \<open>x \<in> Ch h (match (lfp_F ds))\<close> lfp_F_stable_pair_on stable_pair_on_Ch Ch_range show ?thesis
    by - (rule iia_onD[OF Ch_iia[where h=h], where B="snd (lfp_F ds)", simplified]; blast)
qed

theorem gfp_f_hospital_pessimal:
  assumes "stable_pair_on ds XD_XH"
  assumes "x \<in> Ch h (match XD_XH)"
  shows "x \<in> Ch h (match (gfp_F ds) \<union> match XD_XH)"
proof %invisible -
  from \<open>stable_pair_on ds XD_XH\<close> have "match (gfp_F ds) \<union> match XD_XH \<subseteq> snd XD_XH"
    by (simp add: XD_XH_gfp_F(2) le_infI2)
  with assms lfp_F_stable_pair_on stable_pair_on_Ch Ch_range show ?thesis
    by - (rule iia_onD[OF Ch_iia[where h=h], where B="snd XD_XH", simplified]; blast+)
qed

end

text\<open>

The general lattice-theoretic results of e.g. \citet{Fleiner:2002}
depend on the full Tarski-Knaster fixed point theorem, which is
difficult to state in the present type class-based setting. (The
theorem itself is available in the Isabelle/HOL distribution but
requires working with less convenient machinery.)

\<close>


subsection\<open> Theorem~5 does not hold \citep{HatfieldKojima:2008} \<close>

text (in Contracts) \<open>

\citet[Theorem~5]{HatfieldMilgrom:2005} claim that:
\begin{quote}

Suppose \<open>H\<close> contains at least two hospitals, which we
denote by \<open>h\<close> and \<open>h'\<close>. Further suppose that
@{term "Rh h"} is not isotone, that is, contracts are not @{const
"substitutes"} for \<open>h\<close>. Then there exist preference
orderings for the doctors in set \<open>D\<close>, a preference
ordering for a hospital \<open>h'\<close> with a single job opening
such that, regardless of the preferences of the other hospitals, no
stable set of contracts exists.

\end{quote}

\citet[Observation~1]{HatfieldKojima:2008} show this is not true:
there can be stable matches even if hospital choice functions violate
@{const "substitutes"}. This motivates looking for conditions weaker
than @{const "substitutes"} that still guarantee stable matches, a
project taken up by \citet{HatfieldKojima:2010}; see
\S\ref{sec:cop}. We omit their counterexample to this incorrect claim.

\<close>


subsection\<open> Theorem~6: ``Vacancy chain'' dynamics \label{sec:contracts-vacancy-chain} \<close>

text (in ContractsWithSubstitutesAndIRC) \<open>

\citet[II(C), p923]{HatfieldMilgrom:2005} propose a model for updating
a stable match @{term "X"} when a doctor @{term "d'"}
retires. Intuitively the contracts mentioning @{term "d'"} are
discarded and a modified algorithm run from the @{const "XH_largest"}
and @{const "XD_smallest"} sets determined from @{term "X"}. The
result is another stable match where the remaining doctors @{term "ds
- {d'}"} are (weakly) better off and the hospitals (weakly) worse off
than they were in the initial state. The proofs are essentially the
same as for optimality (\S\ref{sec:contracts-optimality}).

\<close>

context ContractsWithSubstitutesAndIRC
begin

context
  fixes X :: "'a set"
  fixes d' :: "'b"
  fixes ds :: "'b set"
begin

text\<open>

\citeauthor{HatfieldMilgrom:2005} do not motivate why the process uses
this functional and not @{const "F"}.

\<close>

definition F' :: "'a set \<times> 'a set dual \<Rightarrow> 'a set \<times> 'a set dual" where
  "F' = (\<lambda>(XD, XH). (- RH (undual XH), dual (- RD_on (ds-{d'}) XD)))"

lemma F'_apply:
  "F' (XD, XH) = (- RH (undual XH), dual (- RD_on (ds - {d'}) XD))"
  by (simp add: F'_def)

lemma %invisible F1'_antimono:
  shows "antimono (\<lambda>XH. - RH XH)"
by %invisible (rule antimonoI) (auto simp: F1_def dest: Diff_mono[OF _ monoD[OF RH_mono]])

lemma %invisible F2'_antimono:
  shows "antimono (\<lambda>XD. - RD_on (ds-{d'}) XD)"
by %invisible (rule antimonoI) (auto simp: F2_def dest: Diff_mono[OF _ monoD[OF RD_on_mono]])

lemma F'_mono:
  shows "mono F'"
unfolding %invisible F'_def using antimonoD[OF F1'_antimono] antimonoD[OF F2'_antimono]
by (auto intro: monoI simp: less_eq_dual_def)

lemma fix_F'_stable_pair_on:
  "stable_pair_on (ds - {d'}) (map_prod id undual A)"
  if "A = F' A"
proof %invisible -
  obtain x y where "A = (x, y)"
    by (cases A)
  with that have "F' (x, y) = (x, y)"
    by simp
  then have "- Rf CH (undual y) = x" and
    "dual (- Rf (CD_on (ds - {d'})) x) = y"
    by (simp_all only: F'_apply prod_eq_iff fst_conv snd_conv)
  with \<open>A = (x, y)\<close> show ?thesis
    by (simp add: stable_pair_on_def dual_eq_iff)
qed

text\<open>

We model their update process using the @{const "while"} combinator,
as we cannot connect it to the extremal fixed points as we did in
\S\ref{sec:contracts-algorithmics} because we begin computing from the
stable match @{term "X"}.

\<close>

definition F'_iter :: "'a set \<times> 'a set dual" where
  "F'_iter = (while (\<lambda>A. F' A \<noteq> A) F' (XD_smallest ds X, dual (XH_largest ds X)))"

abbreviation F'_iter_match :: "'a set" where
  "F'_iter_match \<equiv> match (map_prod id undual F'_iter)"

context
  assumes "stable_on ds X"
begin

lemma F_start:
  shows "F ds (XD_smallest ds X, dual (XH_largest ds X)) = (XD_smallest ds X, dual (XH_largest ds X))"
using %invisible CH_XH_largest[OF \<open>stable_on ds X\<close>] CD_on_XD_smallest[OF \<open>stable_on ds X\<close>] X_subseteq_XH_largest[OF \<open>stable_on ds X\<close>]
unfolding F_def F1_def F2_def XD_smallest_def by (auto simp add: dual_eq_iff)

lemma F'_start:
  shows "(XD_smallest ds X, dual (XH_largest ds X)) \<le> F' (XD_smallest ds X, dual (XH_largest ds X))"
using %invisible F_start unfolding F_def F1_def F2_def F'_def
unfolding CD_on_def XD_smallest_def by (auto simp add: dual_eq_iff dual_less_eq_iff)

lemma
  shows F'_iter_stable_pair_on: "stable_pair_on (ds-{d'}) (map_prod id undual F'_iter)" (is "?thesis1")
    and F'_start_le_F'_iter: "(XD_smallest ds X, dual (XH_largest ds X)) \<le> F'_iter" (is "?thesis2")
proof %invisible -
  obtain P where XXX: "while_option (\<lambda>A. F' A \<noteq> A) F' ((XD_smallest ds X), dual (XH_largest ds X)) = Some P"
    using while_option_finite_increasing_Some[OF F'_mono _ F'_start, simplified] by blast
  with while_option_stop2[OF XXX] fix_F'_stable_pair_on[where A=P]
  show ?thesis1 and ?thesis2
    using funpow_mono2[OF F'_mono _ order.refl F'_start, where i=0]
    unfolding F'_iter_def while_def by auto
qed

lemma F'_iter_match_stable_on:
  shows "stable_on (ds-{d'}) F'_iter_match"
by %invisible (rule stable_pair_on_stable_on) (metis F'_iter_stable_pair_on)

theorem F'_iter_match_doctors_weakly_better_off:
  assumes "x \<in> Cd d X"
  assumes "d \<noteq> d'"
  shows "\<exists>y \<in> Cd d F'_iter_match. (x, y) \<in> Pd d"
proof %invisible -
  from \<open>stable_on ds X\<close> assms
  have "d \<in> ds" by (blast dest: Cd_Xd Cd_range' stable_on_Xd)
  with assms \<open>stable_on ds X\<close> stable_on_stable_pair_on[OF \<open>stable_on ds X\<close>]
  have "\<exists>y\<in>Cd d (XD_smallest ds X \<union> fst F'_iter). (x, y) \<in> Pd d"
    by - (rule Cd_mono; fastforce dest: X_XD_smallest_XH_largest stable_pair_on_Cd_match)
  with F'_iter_stable_pair_on F'_start_le_F'_iter
  have "\<exists>y\<in>Cd d (fst F'_iter). (x, y) \<in> Pd d"
    by (metis Pair_le Un_absorb1 prod.collapse)
  with \<open>d \<noteq> d'\<close> \<open>d \<in> ds\<close>
  show ?thesis
    using stable_pair_on_Cd[OF F'_iter_stable_pair_on, symmetric, of d]
    by (subst Cd_domain[symmetric]) (simp add: Cd_idem)
qed

theorem F'_iter_match_hospitals_weakly_worse_off:
  assumes "x \<in> Ch h X"
  shows "x \<in> Ch h (F'_iter_match \<union> X)"
proof %invisible -
  from F'_iter_stable_pair_on F'_start_le_F'_iter stable_on_stable_pair_on[OF \<open>stable_on ds X\<close>] X_subseteq_XH_largest[OF \<open>stable_on ds X\<close>]
  have "F'_iter_match \<union> X \<subseteq> XH_largest ds X"
    by (simp add: less_eq_prod_def le_infI2 less_eq_dual_def)
  with assms Ch_range \<open>stable_on ds X\<close> show ?thesis
    by - (rule iia_onD[OF Ch_iia, where B="XH_largest ds X"], auto, metis Ch_CH_irc_idem CH_XH_largest)
qed

text\<open>

\citeauthor{HatfieldMilgrom:2005} observe but do not prove that
@{const "F'_iter_match"} is not necessarily doctor-optimal wrt the new
set of doctors, even if @{term "X"} was.

These results seem incomplete. One might expect that the process of
reacting to a doctor's retirement would involve considering new
entrants to the workforce and allowing the set of possible contracts
to be refined. There are also the questions of hospitals opening and
closing.

\<close>

end

end

end

subsection\<open> Theorems~8~and~9: A ``rural hospitals'' theorem \label{sec:contracts-rh} \<close>

text\<open>

Given that some hospitals are less desirable than others, the question
arises of whether there is a mechanism that can redistribute doctors
to under-resourced hospitals while retaining the stability of the
match. Roth's @{emph \<open>rural hospitals theorem\<close>}
\citep[Theorem~5.12]{RothSotomayor:1990} resolves this in the negative
by showing that each doctor and hospital signs the same number of
contracts in every stable match. In the context of contracts the
theorem relies on the further hypothesis that hospital choices satisfy
the law of aggregate demand (\S\ref{sec:cf-lad}).

\<close>

locale ContractsWithLAD = Contracts +
  assumes Ch_lad: "\<forall>h. lad (Ch h)"

locale ContractsWithSubstitutesAndLAD =
  ContractsWithSubstitutes + ContractsWithLAD

text\<open>

We can use results that hold under @{const "irc"} by discharging that
hypothesis against @{const "lad"} using the @{thm [source]
"lad_on_substitutes_on_irc_on"} lemma. This is the effect of the
following \<open>sublocale\<close> command:

\<close>

sublocale ContractsWithSubstitutesAndLAD < ContractsWithSubstitutesAndIRC
using Ch_range Ch_substitutes Ch_lad by unfold_locales (blast intro: lad_on_substitutes_on_irc_on f_range_onI)

context ContractsWithSubstitutesAndLAD
begin

text\<open>

The following results lead to \citet[Theorem~8]{HatfieldMilgrom:2005},
and the proofs go as they say. Again we state these with respect to an
arbitrary solution to @{const "stable_pair"}.

\<close>

context
  fixes XD_XH :: "'a set \<times> 'a set"
  fixes ds :: "'b set"
  assumes "stable_pair_on ds XD_XH"
begin

lemma Cd_XD_gfp_F_card:
  assumes "d \<in> ds"
  shows "card (Cd d (fst XD_XH)) \<le> card (Cd d (fst (gfp_F ds)))"
using %invisible assms Cd_lad XD_XH_gfp_F(1)[OF \<open>stable_pair_on ds XD_XH\<close>]
unfolding lad_on_def by blast

lemma Ch_gfp_F_XH_card:
  shows "card (Ch h (snd (gfp_F ds))) \<le> card (Ch h (snd XD_XH))"
using %invisible Ch_lad XD_XH_gfp_F(2)[OF \<open>stable_pair_on ds XD_XH\<close>]
unfolding lad_on_def by blast

theorem Theorem_8:
  shows "d \<in> ds \<Longrightarrow> card (Cd d (fst XD_XH)) = card (Cd d (fst (gfp_F ds)))"
    and "card (Ch h (snd XD_XH)) = card (Ch h (snd (gfp_F ds)))"
proof %invisible -
  let ?Sum_Cd_gfp = "\<Sum>d\<in>ds. card (Cd d (fst (gfp_F ds)))"
  let ?Sum_Ch_gfp = "\<Sum>h\<in>UNIV. card (Ch h (snd (gfp_F ds)))"
  let ?Sum_Cd_XD = "\<Sum>d\<in>ds. card (Cd d (fst XD_XH))"
  let ?Sum_Ch_XH = "\<Sum>h\<in>UNIV. card (Ch h (snd XD_XH))"

  have "?Sum_Cd_gfp = ?Sum_Ch_gfp"
    using stable_pair_on_CD_on_CH[OF gfp_F_stable_pair_on] CD_on_card[symmetric] CH_card[symmetric] by simp
  also have "\<dots> \<le> ?Sum_Ch_XH"
    using Ch_gfp_F_XH_card by (simp add: sum_mono)
  also have "\<dots> = ?Sum_Cd_XD"
    using stable_pair_on_CD_on_CH[OF \<open>stable_pair_on ds XD_XH\<close>] CD_on_card[symmetric] CH_card[symmetric] by simp
  finally have "?Sum_Cd_XD = ?Sum_Cd_gfp"
    using Cd_XD_gfp_F_card by (simp add: eq_iff sum_mono)
  with Cd_XD_gfp_F_card show "d \<in> ds \<Longrightarrow> card (Cd d (fst XD_XH)) = card (Cd d (fst (gfp_F ds)))"
    by (fastforce elim: sum_mono_inv)

  have "?Sum_Ch_XH = ?Sum_Cd_XD"
    using stable_pair_on_CD_on_CH[OF \<open>stable_pair_on ds XD_XH\<close>] CD_on_card[symmetric] CH_card[symmetric] by simp
  also have "\<dots> \<le> ?Sum_Cd_gfp"
    using Cd_XD_gfp_F_card by (simp add: sum_mono)
  also have "\<dots> = ?Sum_Ch_gfp"
    using stable_pair_on_CD_on_CH[OF gfp_F_stable_pair_on] CD_on_card[symmetric] CH_card[symmetric] by simp
  finally have "?Sum_Ch_gfp = ?Sum_Ch_XH"
    using Ch_gfp_F_XH_card by (simp add: eq_iff sum_mono)
  with Ch_gfp_F_XH_card show "card (Ch h (snd XD_XH)) = card (Ch h (snd (gfp_F ds)))"
    by (fastforce elim: sym[OF sum_mono_inv])
qed

end

text\<open>

Their result may be more easily understood when phrased in terms of
arbitrary stable matches:

\<close>

corollary rural_hospitals_theorem:
  assumes "stable_on ds X"
  assumes "stable_on ds Y"
  shows "d \<in> ds \<Longrightarrow> card (Cd d X) = card (Cd d Y)"
    and "card (Ch h X) = card (Ch h Y)"
using %invisible assms T1[of ds X] T1[of ds Y] Theorem_8 stable_pair_on_Cd_match Ch_CH_irc_idem stable_pair_on_CH
by force+

end

text\<open>

\citet[Theorem~9]{HatfieldMilgrom:2005} show that without @{const
"lad"}, the rural hospitals theorem does not hold. Their proof does
not seem to justify the theorem as stated (for instance, the contracts
\<open>x'\<close>, \<open>y'\<close> and \<open>z'\<close> need not
exist), and so we instead simply provide a counterexample (discovered
by \verb!nitpick!) to the same effect.

\<close>

lemma (in ContractsWithSubstitutesAndIRC) Theorem_9_counterexample:
  assumes "stable_on ds Y"
  assumes "stable_on ds Z"
  shows "card (Ch h Y) = card (Ch h Z)"
oops

datatype X3 = Xd1 | Xd1' | Xd2
(*<*)

lemma X3_UNIV:
  shows "UNIV = set [Xd1, Xd1', Xd2]"
using X3.exhaust by auto

lemmas X3_pow = subset_subseqs[OF subset_trans[OF subset_UNIV Set.equalityD1[OF X3_UNIV]]]

instance X3 :: finite
by standard (simp add: X3_UNIV)

lemma X3_all_pow:
  shows "(\<forall>X''. P X'') \<longleftrightarrow> (\<forall>X''\<in>set ` set (subseqs [Xd1, Xd1', Xd2]). P X'')"
using X3_pow by blast

(*>*)

primrec X3d :: "X3 \<Rightarrow> D2" where
  "X3d Xd1 = D1"
| "X3d Xd1' = D1"
| "X3d Xd2 = D2"

abbreviation X3h :: "X3 \<Rightarrow> H1" where
  "X3h _ \<equiv> H"

primrec PX3d :: "D2 \<Rightarrow> X3 rel" where
  "PX3d D1 = linord_of_list [Xd1, Xd1']"
| "PX3d D2 = linord_of_list [Xd2]"

function CX3h :: "H1 \<Rightarrow> X3 set \<Rightarrow> X3 set" where
  "CX3h _ {Xd1} = {Xd1}"
| "CX3h _ {Xd1'} = {Xd1'}"
| "CX3h _ {Xd2} = {Xd2}"
| "CX3h _ {Xd1, Xd1'} = {Xd1'}"
| "CX3h _ {Xd1, Xd2} = {Xd1, Xd2}"
| "CX3h _ {Xd1', Xd2} = {Xd1'}"
| "CX3h _ {Xd1, Xd1', Xd2} = {Xd1'}"
| "CX3h _ {} = {}"
apply %invisible (case_tac x)
apply (cut_tac X=b in X3_pow)
apply auto
done

(*<*)

termination by lexicographic_order

lemma PX3d_linear:
  shows "Linear_order (PX3d d)"
by (cases d) (simp_all add: linord_of_list_Linear_order)

lemma PX3d_range:
  shows "Field (PX3d d) \<subseteq> {x. X3d x = d}"
by (cases d) simp_all

lemma CX3h_range:
  shows "CX3h h X \<subseteq> {x\<in>X. X3h x = h}"
by (cases "(h, X)" rule: CX3h.cases; simp; metis (mono_tags) H1.exhaust)

lemma CX3h_singular:
  shows "inj_on X3d (CX3h h X)"
by (cases "(h, X)" rule: CX3h.cases) auto

lemma CX3h_substitutes:
  shows "substitutes (CX3h h)"
apply (rule substitutes_onI)
apply (cases h)
apply (cut_tac X=B in X3_pow)
apply (case_tac b)
apply (case_tac [!] a)
apply (auto simp: insert_commute)
done

lemma CX3h_irc:
  shows "irc (CX3h h)"
apply (rule ircI)
apply (cases h)
apply (cut_tac X=B in X3_pow)
apply (case_tac a)
apply (auto simp: insert_commute)
done

(*>*)

interpretation Theorem_9: ContractsWithSubstitutesAndIRC X3d X3h PX3d CX3h
using %invisible PX3d_linear PX3d_range CX3h_range CX3h_singular CX3h_substitutes CX3h_irc
by unfold_locales blast+

lemma Theorem_9_stable_Xd1':
  shows "Theorem_9.stable_on UNIV {Xd1'}"
proof %invisible (rule Theorem_9.stable_onI)
  note image_cong_simp [cong del] note INF_cong_simp [cong] note SUP_cong_simp [cong]
  show "Theorem_9.individually_rational_on UNIV {Xd1'}"
    by (rule Theorem_9.individually_rational_onI)
       (simp_all add: D2_UNION Theorem_9.CD_on_def Theorem_9.CH_def)
  show "Theorem_9.stable_no_blocking_on UNIV {Xd1'}"
    apply (rule Theorem_9.stable_no_blocking_onI)
    apply (case_tac h)
    apply (cut_tac X=X'' in X3_pow)
    apply simp
    apply safe
    apply (simp_all add: insert_commute)
    done
qed

lemma Theorem_9_stable_Xd1_Xd2:
  shows "Theorem_9.stable_on UNIV {Xd1, Xd2}"
proof %invisible (rule Theorem_9.stable_onI)
  note image_cong_simp [cong del] note INF_cong_simp [cong] note SUP_cong_simp [cong]
  show "Theorem_9.individually_rational_on UNIV {Xd1, Xd2}"
    by (rule Theorem_9.individually_rational_onI)
       (simp_all add: D2_UNION Theorem_9.CD_on_def Theorem_9.CH_def insert_commute)
  show "Theorem_9.stable_no_blocking_on UNIV {Xd1, Xd2}"
    apply (rule Theorem_9.stable_no_blocking_onI)
    apply (case_tac h)
    apply (cut_tac X=X'' in X3_pow)
    apply simp
    apply safe
    apply (simp_all add: D2_UNION Theorem_9.CD_on_def Theorem_9.maxR_def linord_of_list_linord_of_listP insert_commute)
    done
qed

text \<open>

This violates the rural hospitals theorem:

\<close>

theorem
  shows "card (Theorem_9.CH {Xd1'}) \<noteq> card (Theorem_9.CH {Xd1, Xd2})"
using %invisible Theorem_9_stable_Xd1' Theorem_9_stable_Xd1_Xd2 Theorem_9.stable_on_CH by simp

text\<open>

{\ldots}which is attributed to the failure of the hospitals' choice
functions to satisfy @{const "lad"}:

\<close>

lemma CX3h_not_lad:
  shows "\<not>lad (CX3h h)"
unfolding %invisible lad_on_def
apply (cases h)
apply clarsimp
apply (rule exI[where x="{Xd1, Xd1', Xd2}"])
apply (rule exI[where x="{Xd1, Xd2}"])
apply simp
done

text\<open>

\citet{CiupanHatfieldKominers:2016} discuss an alternative approach to
this result in a marriage market.

\<close>


subsection\<open> Theorems~15 and 16: Cumulative Offer Processes \label{sec:contracts-cop} \<close>

text\<open>

The goal of \citet[{\S}V]{HatfieldMilgrom:2005} is to connect this
theory of contracts with matching to earlier work on auctions by the
first of the authors, in particular by eliminating the @{const
"substitutes"} hypothesis. They do so by defining a @{emph \<open>cumulative
offer process\<close>} (COP):

\<close>

context Contracts
begin

definition cop_F_HM :: "'d set \<Rightarrow> 'x set \<times> 'x set \<Rightarrow> 'x set \<times> 'x set" where
  "cop_F_HM ds = (\<lambda>(XD, XH). (- RH XH, XH \<union> CD_on ds (- RH XH)))"

text\<open>

Intuitively all of the doctors simultaneously offer their most
preferred contracts that have yet to be rejected by the hospitals, and
the hospitals choose amongst these and all that have been offered
previously. Asking hospital choice functions to satisfy the @{const
"substitutes"} condition effectively forces hospitals to consider only
the contracts they have previously not rejected.

This definition is neither monotonic nor increasing (i.e., it is not
the case that @{term "\<forall>x. x \<le> cop_F_HM ds x"}). We rectify
this by focusing on the second part of the definition.

\<close>

definition cop_F :: "'d set \<Rightarrow> 'x set \<Rightarrow> 'x set" where
  "cop_F ds XH = XH \<union> CD_on ds (- RH XH)"

lemma cop_F_HM_cop_F:
  shows "cop_F_HM ds XD_XH = (- RH (snd XD_XH), cop_F ds (snd XD_XH))"
unfolding cop_F_HM_def cop_F_def split_def by simp

lemma cop_F_increasing:
  shows "x \<le> cop_F ds x"
unfolding %invisible cop_F_def by simp

text\<open>

We have the following straightforward case distinction principles:

\<close>

lemma cop_F_cases:
  assumes "x \<in> cop_F ds fp"
  obtains (fp) "x \<in> fp" | (CD_on) "x \<in> CD_on ds (-RH fp) - fp"
using assms unfolding cop_F_def by blast

lemma CH_cop_F_cases:
  assumes "x \<in> CH (cop_F ds fp)"
  obtains (CH) "x \<in> CH fp" | (RH_fp) "x \<in> RH fp" | (CD_on) "x \<in> CD_on ds (-RH fp) - fp"
using assms CH_range cop_F_def by auto

text\<open>

The existence of fixed points for our earlier definitions
(\S\ref{sec:contracts-algorithmics}) was guaranteed by the
Tarski-Knaster theorem, which relies on the monotonicity of the
defining functional. As @{const "cop_F"} lacks this property, we
appeal instead to the Bourbaki-Witt theorem for increasing
functions.

\<close>

interpretation COP: bourbaki_witt_fixpoint Sup "{(x, y). x \<le> y}" "cop_F ds" for ds
by %invisible (rule bourbaki_witt_fixpoint_complete_latticeI[OF cop_F_increasing])

definition fp_cop_F :: "'d set \<Rightarrow> 'x set" where
  "fp_cop_F ds = COP.fixp_above ds {}"

abbreviation "cop ds \<equiv> CH (fp_cop_F ds)"
(*<*)

lemmas fp_cop_F_unfold = COP.fixp_above_unfold[where a="{}", folded fp_cop_F_def, simplified Field_def, simplified]
lemmas fp_cop_F_code = COP.fixp_above_conv_while[where a="{}", folded fp_cop_F_def, simplified Field_def, simplified]

(*>*)
text\<open>

Given that the set of contracts is finite, we avoid continuity and
admissibility issues; we have the following straightforward induction
principle:

\<close>

lemma fp_cop_F_induct[case_names base step]:
  assumes "P {}"
  assumes "\<And>fp. P fp \<Longrightarrow> P (cop_F ds fp)"
  shows "P (fp_cop_F ds)"
using %invisible assms
by (induct rule: COP.fixp_above_induct[where a="{}", folded fp_cop_F_def])
   (fastforce intro: admissible_chfin)+

text\<open>

An alternative is to use the @{const "while"} combinator, which is
equivalent to the above by @{thm [source] COP.fixp_above_conv_while}.

In any case, invariant reasoning is essential to verifying the
properties of the COP, no matter how we phrase it. We develop a small
program logic to ease the reuse of the invariants we
prove.

\<close>

definition
  valid :: "'d set \<Rightarrow> ('d set \<Rightarrow> 'x set \<Rightarrow> bool) \<Rightarrow> ('d set \<Rightarrow> 'x set \<Rightarrow> bool) \<Rightarrow> bool"
where
  "valid ds P Q = (Q ds {} \<and> (\<forall>fp. P ds fp \<and> Q ds fp \<longrightarrow> Q ds (cop_F ds fp)))"

abbreviation
  invariant :: "'d set \<Rightarrow> ('d set \<Rightarrow> 'x set \<Rightarrow> bool) \<Rightarrow> bool"
where
  "invariant ds P \<equiv> valid ds (\<lambda>_ _. True) P"

text\<open>

Intuitively @{term "valid ds P Q"} asserts that the COP satisfies
@{term "Q"} assuming that it satisfies @{term "P"}. This allows us to
decompose our invariant proofs. By setting the precondition to @{term
"True"}, @{term "invariant ds P"} captures the proof obligations of
@{term "fp_cop_F_induct"} exactly.

The following lemmas ease the syntactic manipulation of these facts.

\<close>

lemma validI[case_names base step]:
  assumes "Q ds {}"
  assumes "\<And>fp. \<lbrakk>P ds fp; Q ds fp\<rbrakk> \<Longrightarrow> Q ds (cop_F ds fp)"
  shows "valid ds P Q"
using %invisible assms unfolding valid_def by blast

lemma invariant_cop_FD:
  assumes "invariant ds P"
  assumes "P ds fp"
  shows "P ds (cop_F ds fp)"
using %invisible assms unfolding valid_def by blast

lemma invariantD:
  assumes "invariant ds P"
  shows "P ds (fp_cop_F ds)"
using %invisible assms fp_cop_F_induct unfolding valid_def by blast

lemma valid_pre:
  assumes "valid ds P' Q"
  assumes "\<And>fp. P ds fp \<Longrightarrow> P' ds fp"
  shows "valid ds P Q"
using %invisible assms unfolding valid_def by blast

lemma valid_invariant:
  assumes "valid ds P Q"
  assumes "invariant ds P"
  shows "invariant ds (\<lambda> ds fp. P ds fp \<and> Q ds fp)"
using %invisible assms unfolding valid_def by blast

lemma valid_conj:
  assumes "valid ds (\<lambda>ds fp. R ds fp \<and> P ds fp \<and> Q ds fp) P"
  assumes "valid ds (\<lambda>ds fp. R ds fp \<and> P ds fp \<and> Q ds fp) Q"
  shows "valid ds R (\<lambda> ds fp. P ds fp \<and> Q ds fp)"
using %invisible assms unfolding valid_def by blast

end

text (in ContractsWithSubstitutes) \<open>

\citet[Theorem~15]{HatfieldMilgrom:2005} assert that @{const
"fp_cop_F"} is equivalent to the doctor-offering algorithm @{const
"gfp_F"}, assuming @{const "substitutes"}. (Note that the fixed points
generated by increasing functions do not necessarily form a lattice,
so there is not necessarily a hospital-optimal match, and indeed in
general these do not exist.)  Our proof is eased by the decomposition
lemma @{thm [source] gfp_F_lfp_F} and the standard properties of fixed
points in a lattice.

\<close>

context ContractsWithSubstitutes
begin

lemma lfp_F2_o_F1_fp_cop_F:
  shows "lfp (F2 ds \<circ> F1) = fp_cop_F ds"
proof(rule antisym)
  have "(F2 ds \<circ> F1) (fp_cop_F ds) \<subseteq> cop_F ds (fp_cop_F ds)"
    by (clarsimp simp: F2_def F1_def cop_F_def)
  then show "lfp (F2 ds \<circ> F1) \<subseteq> fp_cop_F ds"
    by (simp add: lfp_lowerbound fp_cop_F_unfold[symmetric])
next
  show "fp_cop_F ds \<subseteq> lfp (F2 ds \<circ> F1)"
  proof(induct rule: fp_cop_F_induct)
    case base then show ?case by simp
  next
    case (step fp) note IH = \<open>fp \<subseteq> lfp (F2 ds \<circ> F1)\<close>
    then have "CD_on ds (- RH fp) \<subseteq> lfp (F2 ds \<circ> F1)"
      by (subst lfp_unfold[OF F2_o_F1_mono])
         (metis (no_types, lifting) Compl_Diff_eq F1_antimono F2_antimono F1_def F2_def Un_subset_iff antimonoD comp_apply)
    with IH show ?case
      unfolding cop_F_def by blast
  qed
qed

theorem Theorem_15:
  shows "gfp_F ds = (- RH (fp_cop_F ds), fp_cop_F ds)"
using lfp_F2_o_F1_fp_cop_F unfolding gfp_F_lfp_F F1_def by simp

theorem Theorem_15_match:
  shows "match (gfp_F ds) = CH (fp_cop_F ds)"
using Theorem_15 by (fastforce dest: subsetD[OF CH_range])

end

text\<open>

\label{sec:contracts-codegen-fp_cop_F}

With some auxiliary definitions, we can evaluate the COP on the
example from \S\ref{sec:contracts-codegen-gfp_F}.

\<close>

(*<*)

definition "P920_example_cop_F = P920_example.cop_F"
definition "P920_example_fp_cop_F = P920_example.fp_cop_F"
lemmas P920_example_cop_F_code[code] = P920_example.cop_F_def[folded P920_example_cop_F_def]
lemmas P920_example_fp_cop_F_code[code] = P920_example.fp_cop_F_code[folded P920_example_fp_cop_F_def P920_example_cop_F_def]

(*>*)

lemma P920_example_fp_cop_F_value:
  shows "P920_example_CH (P920_example_fp_cop_F UNIV) = {(D1, H1), (D2, H2)}"
by eval

text\<open>

\citet[Theorem~16]{HatfieldMilgrom:2005} assert that this process
yields a stable match when we have a single hospital (now called an
auctioneer) with unrestricted preferences. As before, this holds
provided the auctioneer's preferences satisfy @{const "irc"}.

We begin by establishing two obvious invariants of the COP that
hold in general.

\<close>

context Contracts
begin

lemma %invisible CH_Ch_singular:
  assumes "(UNIV::'h set) = {h}"
  shows "CH A = Ch h A"
unfolding CH_def using assms by auto

definition cop_F_range_inv :: "'d set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "cop_F_range_inv ds fp \<longleftrightarrow> (\<forall>x\<in>fp. x \<in> Field (Pd (Xd x)) \<and> Xd x \<in> ds)"

definition cop_F_closed_inv :: "'d set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "cop_F_closed_inv ds fp \<longleftrightarrow> (\<forall>x\<in>fp. above (Pd (Xd x)) x \<subseteq> fp)"

text\<open>

The first, @{const "cop_F_range_inv"}, simply states that the result
of the COP respects the structural conditions for doctors. The second
@{const "cop_F_closed_inv"} states that the COP is upwards-closed with
respect to the doctors' preferences.

\<close>

lemma cop_F_range_inv:
  shows "invariant ds cop_F_range_inv"
unfolding valid_def cop_F_range_inv_def cop_F_def by (fastforce simp: mem_CD_on_Cd dest: Cd_range')

lemma cop_F_closed_inv:
  shows "invariant ds cop_F_closed_inv"
unfolding valid_def cop_F_closed_inv_def cop_F_def above_def
by (clarsimp simp: subset_iff) (metis Cd_preferred ComplI Un_upper1 mem_CD_on_Cd subsetCE)

lemmas fp_cop_F_range_inv = invariantD[OF cop_F_range_inv]
lemmas fp_cop_F_range_inv' = fp_cop_F_range_inv[unfolded cop_F_range_inv_def, rule_format]
lemmas fp_cop_F_closed_inv = invariantD[OF cop_F_closed_inv]
lemmas fp_cop_F_closed_inv' = subsetD[OF bspec[OF invariantD[OF cop_F_closed_inv, unfolded cop_F_closed_inv_def, simplified]]]

text\<open>

The only challenge in showing that the COP yields a stable match is in
establishing @{const "stable_no_blocking_on"}. Our key lemma states
that that if @{const "CH"} rejects all contracts for doctor
\<open>d\<close> in @{const "fp_cop_F"}, then all contracts for
\<open>d\<close> are in @{const "fp_cop_F"}.

\<close>

lemma cop_F_RH:
  assumes "d \<in> ds"
  assumes "x \<in> Field (Pd d)"
  assumes "aboveS (Pd d) x \<subseteq> RH fp"
  shows "x \<in> cop_F ds fp"
using %invisible assms Pd_linear unfolding cop_F_def
by (clarsimp simp: mem_CD_on_Cd Cd_greatest greatest_def aboveS_def order_on_defs total_on_def subset_iff)
   (metis Compl_Diff_eq Compl_iff Diff_iff IntE Pd_Xd refl_onD)

lemma fp_cop_F_all:
  assumes "d \<in> ds"
  assumes "d \<notin> Xd ` CH (fp_cop_F ds)"
  shows "Field (Pd d) \<subseteq> fp_cop_F ds"
proof %invisible (rule subsetI)
  fix x assume "x \<in> Field (Pd d)"
  from spec[OF Pd_linear] this finite[of "Pd d"] show "x \<in> fp_cop_F ds"
  proof(induct rule: finite_Linear_order_induct)
    case (step x)
    with assms Pd_range Pd_Xd cop_F_RH[of d ds _ "fp_cop_F ds", unfolded fp_cop_F_unfold[symmetric]]
    show ?case unfolding aboveS_def by (fastforce iff: image_iff)
  qed
qed

text\<open>

\citet{AygunSonmez:2012-WP2} observe that any blocking contract must
be weakly preferred by its doctor to anything in the outcome of the
@{const "fp_cop_F"}:

\<close>

lemma fp_cop_F_preferred:
  assumes "y \<in> CD_on ds (CH (fp_cop_F ds) \<union> X'')"
  assumes "x \<in> CH (fp_cop_F ds)"
  assumes "Xd x = Xd y"
  shows "(x, y) \<in> Pd (Xd x)"
using %invisible assms fp_cop_F_range_inv'[OF CH_range'[OF assms(2)]] Pd_Xd Pd_linear
by (clarsimp simp: CD_on_def Cd_greatest greatest_def) (metis Int_iff Un_iff subset_refl underS_incl_iff)

text\<open>

The headline lemma cobbles these results together.

\<close>

lemma X''_closed:
  assumes "X'' \<subseteq> CD_on ds (CH (fp_cop_F ds) \<union> X'')"
  shows "X'' \<subseteq> fp_cop_F ds"
proof(rule subsetI)
  fix x assume "x \<in> X''"
  show "x \<in> fp_cop_F ds"
  proof(cases "Xd x \<in> Xd ` CH (fp_cop_F ds)")
    case True
    then obtain y where "Xd y = Xd x" and "y \<in> CH (fp_cop_F ds)" by clarsimp
    with assms \<open>x \<in> X''\<close> show ?thesis
      using CH_range fp_cop_F_closed_inv' fp_cop_F_preferred unfolding above_def by blast
  next
    case False with assms \<open>x \<in> X''\<close> show ?thesis
      by (meson Cd_range' IntD2 fp_cop_F_all mem_CD_on_Cd rev_subsetD)
  qed
qed

text (in Contracts) \<open>

The @{const "irc"} constraint on the auctioneer's preferences is
needed for @{const "stable_no_blocking"} and their part of @{const
"individually_rational"}.

\<close>

end

context ContractsWithIRC
begin

lemma cop_stable_no_blocking_on:
  shows "stable_no_blocking_on ds (cop ds)"
proof(rule stable_no_blocking_onI)
  fix h X''
  assume C: "X'' = Ch h (CH (fp_cop_F ds) \<union> X'')"
  assume NE: "X'' \<noteq> Ch h (CH (fp_cop_F ds))"
  assume CD: "X'' \<subseteq> CD_on ds (CH (fp_cop_F ds) \<union> X'')"
  from CD have "X'' \<subseteq> fp_cop_F ds" by (rule X''_closed)
  then have X: "CH (fp_cop_F ds) \<union> X'' \<subseteq> fp_cop_F ds" using CH_range by simp
  from C NE Ch_CH_irc_idem[of h]  show False
    using consistency_onD[OF Ch_consistency _ X] CH_domain Ch_domain by blast
qed

theorem Theorem_16:
  assumes h: "(UNIV::'c set) = {h}"
  shows "stable_on ds (cop ds)" (is "stable_on ds ?fp")
proof(rule stable_onI)
  show "individually_rational_on ds ?fp"
  proof(rule individually_rational_onI)
    from h have "allocation ?fp" by (simp add: Ch_singular CH_Ch_singular)
    then show "CD_on ds ?fp = ?fp"
      by (rule CD_on_closed) (blast dest: CH_range' fp_cop_F_range_inv')
    show "CH (CH (fp_cop_F ds)) = CH (fp_cop_F ds)" by (simp add: CH_irc_idem)
  qed
  show "stable_no_blocking_on ds ?fp" by (rule cop_stable_no_blocking_on)
qed

end


subsection\<open> Concluding remarks \<close>

text\<open>

From \citet{HatfieldMilgrom:2005}, we have not shown Theorems~2, 7, 13
and~14, all of which are intended to position their results against
prior work in this space. We delay establishing their strategic
results (Theorems~10, 11 and~12) to \S\ref{sec:strategic}, after we
have developed more useful invariants for the COP.

By assuming \isa{irc}, \citet{AygunSonmez:2012-WP2} are essentially
trading on Plott's path independence condition
(\S\ref{sec:cf-path-independence}), as observed by
\citet{ChambersYenmez:2013}. The latter show that these results
generalize naturally to many-to-many matches, where doctors also use
path-independent choice functions; see also \citet{Fleiner:2003}.

For many applications, however, @{const "substitutes"} proves to be
too strong a condition. The COP of \S\ref{sec:contracts-cop} provides
a way forward, as we discuss in the next section.

\<close>
(*<*)

end
(*>*)
