(*<*)
theory Strategic
imports
  COP
begin

(*>*)
section\<open> Strategic results \label{sec:strategic} \<close>

text (in ContractsWithSubstitutes) \<open>

We proceed to establish a series of strategic results for the COP (see
\S\ref{sec:contracts-cop} and \S\ref{sec:cop}), making use of the
invariants we developed for it. These results also apply to the
matching-with-contracts setting of \S\ref{sec:contracts}, and where
possible we specialize our lemmas to it.

\<close>


subsection\<open> \citet{HatfieldMilgrom:2005}: Theorems~10 and~11: Truthful revelation as a Dominant Strategy \label{sec:strategic-contracts} \<close>

text (in ContractsWithSubstitutes) \<open>

Theorems~10 and 11 demonstrate that doctors cannot obtain better
results for themselves in the doctor-optimal match (i.e., @{term "cop ds"}, equal to @{term "match (gfp_F ds)"} by @{thm [source]
"Theorem_15_match"} assuming hospital preferences satisfy @{const
"substitutes"}) by misreporting their preferences. (See
\citet[\S4.2]{RothSotomayor:1990} for a discussion about the
impossibility of a mechanism being strategy-proof for all agents.)

\citet[{\S}III(B)]{HatfieldMilgrom:2005} provide the
following intuition:
\begin{quote}

We will show the positive incentive result for the doctor-offering
algorithm in two steps which highlight the different roles of the two
preference assumptions. First, we show that the @{const "substitutes"}
condition, by itself, guarantees that doctors cannot benefit by
exaggerating the ranking of an unattainable contract. More precisely,
if there exists a preferences list for a doctor @{term "d"} such that
@{term "d"} obtains contract @{term "x"} by submitting this list, then
@{term "d"} can also obtain @{term "x"} by submitting a preference
list that includes only contract @{term "x"} [Theorem~10]. Second, we
will show that adding the law of aggregate demand guarantees that a
doctor does at least as well as reporting truthfully as by reporting
any singleton [Theorem~11]. Together, these are the dominant strategy
result.

\end{quote}

We prove Theorem~10 via a lemma that states that the contracts above
@{term "x \<in> X"} for some stable match @{term "X"} with respect to
manipulated preferences @{term "Pd (Xd x)"} do not improve the outcome
for doctor @{term "Xd x"} with respect to their true preferences
@{term "Pd' (Xd x)"} in the doctor-optimal match for @{term "Pd'"}.

This is weaker than \citet[Lemma~1]{HatfieldKojima:2009} (see
\S\ref{sec:strategic-hk2010-lemma1}) as we do not guarantee that the
allocation does not change. By the bossiness result of
\S\ref{sec:bossiness}, such manipulations can change the outcomes of
the other doctors; this lemma establishes that only weak improvements
are possible.

\<close>

context ContractsWithUnilateralSubstitutesAndIRC
begin

context
  fixes d' :: "'b"
  fixes Pd' :: "'b \<Rightarrow> 'a rel"
  assumes Pd'_d'_linear: "Linear_order (Pd' d')"
  assumes Pd'_d'_range: "Field (Pd' d') \<subseteq> {y. Xd y = d'}"
  assumes Pd': "\<forall>d. d\<noteq>d' \<longrightarrow> Pd' d = Pd d"
begin

(*<*)

lemma PdXXX_linear:
  shows "Linear_order (Pd' d)"
using Pd_linear Pd'_d'_linear Pd' by (cases "d = d'") simp_all

lemma PdXXX_range:
  shows "Field (Pd' d) \<subseteq> {x. Xd x = d}"
using Pd_range Pd'_d'_range Pd' by (cases "d = d'") simp_all

lemmas PdXXX_range' = subsetD[OF PdXXX_range, simplified, of x] for x

(*>*)

interpretation PdXXX: ContractsWithUnilateralSubstitutesAndIRC Xd Xh Pd' Ch
using %invisible PdXXX_linear PdXXX_range Ch_range Ch_singular Ch_unilateral_substitutes Ch_irc
by unfold_locales blast+

theorem Pd_above_irrelevant:
  assumes d'_Field: "dX X d' \<subseteq> Field (Pd' d')"
  assumes d'_Above: "Above (Pd' d') (dX X d') \<subseteq> Above (Pd d') (dX X d')"
  assumes "x \<in> X"
  assumes "stable_on ds X"
  shows "\<exists>y \<in> PdXXX.cop ds. (x, y) \<in> Pd' (Xd x)"
proof(rule PdXXX.Theorem_5[OF ccontr \<open>x \<in> X\<close>])
  assume "\<not>PdXXX.stable_on ds X"
  then show False
  proof(cases rule: PdXXX.not_stable_on_cases)
    case not_individually_rational
    from Pd' \<open>stable_on ds X\<close> d'_Field have "x \<in> PdXXX.Cd (Xd x) X" if "x \<in> X" for x
      using that unfolding dX_def by (force simp: stable_on_range' stable_on_allocation PdXXX.Cd_single)
    with \<open>stable_on ds X\<close> not_individually_rational show False
      unfolding PdXXX.individually_rational_on_def
      by (auto simp: PdXXX.mem_CD_on_Cd stable_on_Xd dest: stable_on_CH PdXXX.CD_on_range')
  next
    case not_no_blocking
    then obtain h X'' where "PdXXX.blocking_on ds X h X''"
      unfolding PdXXX.stable_no_blocking_on_def by blast
    have "blocking_on ds X h X''"
    proof(rule blocking_onI)
      fix x assume "x \<in> X''"
      note Pbos = PdXXX.blocking_on_Field[OF \<open>PdXXX.blocking_on ds X h X''\<close>]
                  PdXXX.blocking_on_allocation[OF \<open>PdXXX.blocking_on ds X h X''\<close>]
                  PdXXX.blocking_on_CD_on'[OF \<open>PdXXX.blocking_on ds X h X''\<close> \<open>x \<in> X''\<close>]
      show "x \<in> CD_on ds (X \<union> X'')"
      proof(cases "Xd x = d'")
        case True
        from Pd_linear' d'_Field d'_Above \<open>x \<in> X''\<close> \<open>Xd x = d'\<close> Pbos
        have "dX X'' (Xd x) \<subseteq> Field (Pd (Xd x))"
          by (force simp: PdXXX.mem_CD_on_Cd PdXXX.Cd_Above PdXXX.dX_Int_Field_Pd Above_union
                          Int_Un_distrib2 dX_singular intro: Above_Field)
        moreover from \<open>stable_on ds X\<close> have "dX X (Xd x) \<subseteq> Field (Pd (Xd x))"
          by (force dest: dX_range' stable_on_range')
        moreover note Pd_linear' Pd_range PdXXX_range d'_Field d'_Above \<open>x \<in> X''\<close> \<open>Xd x = d'\<close> Pbos
        ultimately show ?thesis
          by (clarsimp simp: PdXXX.mem_CD_on_Cd PdXXX.Cd_Above_dX mem_CD_on_Cd Cd_Above_dX
                             Above_union dX_union Int_Un_distrib2)
             (fastforce simp: dX_singular intro: Above_Linear_singleton)
      next
        case False
        with \<open>x \<in> PdXXX.CD_on ds (X \<union> X'')\<close> show ?thesis
          by (clarsimp simp: Pd' PdXXX.mem_CD_on_Cd mem_CD_on_Cd PdXXX.Cd_greatest Cd_greatest)
      qed
    qed (use \<open>PdXXX.blocking_on ds X h X''\<close> in \<open>simp_all add: PdXXX.blocking_on_def\<close>)
    with \<open>stable_on ds X\<close> show False by (simp add: blocking_on_imp_not_stable)
  qed
qed

end

end

text\<open>

We now specialize this lemma to Theorem~10 by defining a preference
order for the doctors where distinguished doctors @{term "ds"} submit
single preferences for the contracts they receive in the
doctor-optimal match.

The function @{thm "override_on_def"} denotes function update at
several points.

\<close>

context Contracts
begin

definition Pd_singletons_for_ds :: "'x set \<Rightarrow> 'd set \<Rightarrow> 'd \<Rightarrow> 'x rel" where
  "Pd_singletons_for_ds X ds \<equiv> override_on Pd (\<lambda>d. dX X d \<times> dX X d) ds"

(*<*)

lemma Pd_singletons_for_ds_range:
  shows "Field (Pd_singletons_for_ds X ds d) \<subseteq> {x. Xd x = d}"
using Pd_range dX_range unfolding Pd_singletons_for_ds_def
by (clarsimp simp: Field_def override_on_def) blast

lemma Pd_singletons_for_ds_linear:
  assumes "allocation X"
  shows "Linear_order (Pd_singletons_for_ds X ds d)"
unfolding Pd_singletons_for_ds_def using Pd_linear dX_linear[OF assms] by (simp add: override_on_def)

lemma Pd_singletons_for_ds_simps:
  shows "d \<in> ds \<Longrightarrow> Pd_singletons_for_ds X ds d = dX X d \<times> dX X d"
    and "d \<notin> ds \<Longrightarrow> Pd_singletons_for_ds X ds d = Pd d"
unfolding Pd_singletons_for_ds_def by simp_all

(*>*)

end

text\<open>

We interpret our @{const "ContractsWithUnilateralSubstitutesAndIRC"}
locale with respect to this updated preference order, which gives us
the stable match and properties of it.

\<close>

context ContractsWithUnilateralSubstitutesAndIRC
begin

context
  fixes ds :: "'b set"
  fixes X :: "'a set"
  assumes "stable_on ds X"
begin

interpretation
  Singleton_for_d: ContractsWithUnilateralSubstitutesAndIRC Xd Xh "Pd_singletons_for_ds X {d}" Ch for d
using %invisible Pd_singletons_for_ds_linear Pd_singletons_for_ds_range Ch_range Ch_singular Ch_unilateral_substitutes Ch_irc
                 stable_on_allocation[OF \<open>stable_on ds X\<close>]
by unfold_locales blast+

text\<open>

Our version of \citet[Theorem~10]{HatfieldMilgrom:2005} (for the COP)
states that if a doctor submits a preference order containing just
@{term "x"}, where @{term "x"} is their contract in some stable match
@{term "X"}, then that doctor receives exactly @{term "x"} in the
doctor-optimal match and all other doctors do at least as well.

\<close>

theorem Theorem_10_fp_cop_F:
  assumes "x \<in> X"
  shows "\<exists>y \<in> Singleton_for_d.cop d ds. (x, y) \<in> Pd_singletons_for_ds X {d} (Xd x)"
proof(rule Pd_above_irrelevant[where ds=ds and d'=d and X=X])
  from stable_on_allocation \<open>stable_on ds X\<close>
  show "Above (Pd_singletons_for_ds X {d} d) (Singleton_for_d.dX X d) \<subseteq> Above (Pd d) (Singleton_for_d.dX X d)"
    by (clarsimp simp: Above_def Pd_singletons_for_ds_simps dX_def) (metis inj_on_eq_iff stable_on_range' Pd_refl)
qed (use stable_on_allocation \<open>stable_on ds X\<close> Pd_singletons_for_ds_linear Pd_singletons_for_ds_range assms
     in \<open>simp_all, simp_all add: Pd_singletons_for_ds_simps dX_def\<close>)

end

end

text (in ContractsWithSubstitutesAndIRC) \<open>

We can recover the original Theorem~10 by specializing this result to
@{const "gfp_F"}.

\<close>

context ContractsWithSubstitutesAndIRC
begin

interpretation
  Singleton_for_d: ContractsWithSubstitutesAndIRC Xd Xh "Pd_singletons_for_ds (match (gfp_F ds)) {d}" Ch
for ds d
using %invisible Pd_singletons_for_ds_linear Pd_singletons_for_ds_range Ch_range Ch_singular Ch_substitutes Ch_irc gfp_F_stable_on
                 stable_on_allocation[OF gfp_F_stable_on[of ds]]
by unfold_locales blast+

theorem Theorem_10:
  assumes "x \<in> match (gfp_F ds)"
  shows "\<exists>y \<in> match (Singleton_for_d.gfp_F ds d ds). (x, y) \<in> Pd_singletons_for_ds (match (gfp_F ds)) {d} (Xd x)"
using Theorem_10_fp_cop_F Singleton_for_d.Theorem_15_match Theorem_15_match gfp_F_stable_on assms by simp

corollary Theorem_10_d:
  assumes "x \<in> match (gfp_F ds)"
  shows "x \<in> match (Singleton_for_d.gfp_F ds (Xd x) ds)"
using gfp_F_stable_on[of ds] Theorem_10[OF assms(1), of "Xd x"] assms
by (clarsimp simp: Pd_singletons_for_ds_simps dX_def inj_on_eq_iff dest!: stable_on_allocation)

end

text (in ContractsWithSubstitutes) \<open>

The second theorem \citep[Theorem~11]{HatfieldMilgrom:2005} depends on
both Theorem~10 and the rural hospitals theorem
(\S\ref{sec:contracts-rh}, \S\ref{sec:cop-rh}). It shows that,
assuming everything else is fixed, if doctor @{term "d'"} obtains
contract @{term "x"} with (manipulated) preferences @{term "Pd d'"} in
the doctor-optimal match, then they will obtain a contract at least as
good by submitting their true preferences @{term "Pd' d'"} (with
respect to these true preferences).

\<close>

locale TruePrefs = Contracts +
  fixes x :: "'a"
  fixes X :: "'a set"
  fixes ds :: "'b set"
  fixes Pd' :: "'b \<Rightarrow> 'a rel"
  assumes x: "x \<in> X"
  assumes X: "stable_on ds X"
  assumes Pd'_d'_x: "x \<in> Field (Pd' (Xd x))"
  assumes Pd'_d'_linear: "Linear_order (Pd' (Xd x))"
  assumes Pd'_d'_range: "Field (Pd' (Xd x)) \<subseteq> {y. Xd y = Xd x}"
  assumes Pd': "\<forall>d. d\<noteq>Xd x \<longrightarrow> Pd' d = Pd d"

(*<*)

begin

lemma Pd'_linear:
  shows "Linear_order (Pd' d)"
using Pd_linear Pd'_d'_linear Pd' by (cases "d = Xd x") simp_all

lemma Pd'_range:
  shows "Field (Pd' d) \<subseteq> {x. Xd x = d}"
using Pd_range Pd'_d'_range Pd' by (cases "d = Xd x") simp_all

definition Pd'_tax :: "'b \<Rightarrow> 'a rel" where
  "Pd'_tax = (Pd'(Xd x := Restr (Pd' (Xd x)) (above (Pd' (Xd x)) x)))"

lemma Pd'_tax_linear:
  shows "Linear_order (Pd'_tax d)"
using Pd'_linear Pd'_d'_linear Linear_order_Restr unfolding Pd'_tax_def by auto

lemma Pd'_tax_Pd':
  shows "Pd'_tax d \<subseteq> Pd' d"
unfolding Pd'_tax_def by simp

lemma Pd'_tax_range:
  shows "Field (Pd'_tax d) \<subseteq> {x. Xd x = d}"
using Pd'_range Pd'_tax_Pd' by (meson mono_Field subset_trans)

lemma Pd'_tax_x:
  shows "x \<in> Field (Pd'_tax (Xd x))"
using Pd'_d'_x Pd'_d'_linear unfolding Pd'_tax_def above_def order_on_defs
by (fastforce intro: FieldI2 dest: refl_onD)

lemma Pd'_Above:
  assumes "Y \<subseteq> above (Pd' (Xd x)) x"
  assumes "Y \<noteq> {}"
  shows "Above (Pd' d) Y \<subseteq> Above (Pd'_tax d) Y"
using Pd'_d'_linear assms unfolding Above_def Pd'_tax_def above_def order_on_defs
by (auto simp: Refl_Field_Restr subset_eq elim: transE)

end

(*>*)

locale ContractsWithUnilateralSubstitutesAndIRCAndLADAndTruePrefs =
  ContractsWithUnilateralSubstitutesAndIRCAndLAD + TruePrefs
begin

interpretation TruePref: ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh Pd' Ch
using %invisible Pd'_linear Pd'_range Ch_range Ch_singular Ch_unilateral_substitutes Ch_irc Ch_lad
by unfold_locales blast+

interpretation TruePref_tax: ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh Pd'_tax Ch
using %invisible Pd'_tax_linear Pd'_tax_range Ch_range Ch_singular Ch_unilateral_substitutes Ch_irc Ch_lad
by unfold_locales blast+

interpretation
  Singleton_for_d: ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh "Pd_singletons_for_ds X {Xd x}" Ch
using %invisible Pd_singletons_for_ds_linear Pd_singletons_for_ds_range Ch_range Ch_singular Ch_unilateral_substitutes Ch_irc Ch_lad X stable_on_allocation[OF X]
by unfold_locales blast+

(*<*)

lemma Xd_x_ds:
  shows "Xd x \<in> ds"
using %invisible X stable_on_Xd x by blast

lemma TruePref_tax_Cd_not_x:
  assumes "d \<noteq> Xd x"
  shows "TruePref_tax.Cd d = Singleton_for_d.Cd d"
using assms spec[OF Pd', of d] stable_on_allocation[OF X]
unfolding TruePref_tax.Cd_def Singleton_for_d.Cd_def by (simp add: Pd'_tax_def Pd_singletons_for_ds_simps)

(*>*)

lemma Theorem_11_Pd'_tax:
  shows "\<exists>y\<in>TruePref_tax.cop ds. (x, y) \<in> Pd'_tax (Xd x)"
proof(rule ccontr)
  let ?Z = "TruePref_tax.cop ds"
  assume "\<not>?thesis" then have "Xd x \<notin> Xd ` ?Z"
    using Pd'_range Pd'_linear[of "Xd x"] Pd'_d'_x unfolding order_on_defs
    by - (clarsimp, drule (1) bspec,
          fastforce simp: Pd'_tax_def above_def Refl_Field_Restr dest: refl_onD
                   dest!: CH_range' TruePref_tax.fp_cop_F_range_inv')
  show False
  proof(cases "Singleton_for_d.stable_on ds ?Z")
    case True
    moreover
    from Theorem_10_fp_cop_F[OF X x, of "Xd x"] X
    have "x \<in> CH (Singleton_for_d.fp_cop_F ds)"
      by (force simp: Pd_singletons_for_ds_simps dX_def dest: inj_onD stable_on_allocation)
    with Singleton_for_d.fp_cop_F_allocation
    have "Singleton_for_d.Cd (Xd x) (Singleton_for_d.cop ds) = {x}"
      by (meson Singleton_for_d.Cd_single Singleton_for_d.Cd_singleton Singleton_for_d.fp_cop_F_range_inv'
                TruePref_tax.CH_range')
    with Singleton_for_d.Theorem_1[of ds]
    have "x \<in> Y" if "Singleton_for_d.stable_on ds Y" for Y
      using Singleton_for_d.Theorem_6_fp_cop_F(1)[where ds="ds" and X="Y" and d="Xd x"] that Xd_x_ds x
            card_Suc_eq[where A="Singleton_for_d.Cd (Xd x) Y" and k=0] stable_on_allocation[OF X]
      by (fastforce simp: Singleton_for_d.Cd_singleton[symmetric] Pd_singletons_for_ds_simps dX_def
                    dest: Singleton_for_d.Cd_range' inj_onD)
    moreover note \<open>Xd x \<notin> Xd ` ?Z\<close>
    ultimately show False by blast
  next
    case False note \<open>\<not>Singleton_for_d.stable_on ds ?Z\<close>
    then show False
    proof(cases rule: Singleton_for_d.not_stable_on_cases)
      case not_individually_rational
      with TruePref_tax.Theorem_1[of ds] \<open>Xd x \<notin> Xd ` ?Z\<close>
      show False
        unfolding TruePref_tax.stable_on_def Singleton_for_d.individually_rational_on_def
                  TruePref_tax.individually_rational_on_def Singleton_for_d.CD_on_def
        by (auto dest: Singleton_for_d.Cd_range')
           (metis TruePref_tax.mem_CD_on_Cd TruePref_tax_Cd_not_x image_eqI)
    next
      case not_no_blocking
      then obtain h X'' where "Singleton_for_d.blocking_on ds ?Z h X''"
        unfolding Singleton_for_d.stable_no_blocking_on_def by blast
      have "TruePref_tax.blocking_on ds ?Z h X''"
      proof(rule TruePref_tax.blocking_onI)
        fix y assume "y \<in> X''"
        with \<open>Singleton_for_d.blocking_on ds ?Z h X''\<close> have YYY: "y \<in> Singleton_for_d.CD_on ds (?Z \<union> X'')"
          unfolding Singleton_for_d.blocking_on_def by blast
        show "y \<in> TruePref_tax.CD_on ds (?Z \<union> X'')"
        proof(cases "Xd y = Xd x")
          case True
          with inj_on_eq_iff[OF stable_on_allocation x] X YYY have "y = x"
            by (fastforce simp: Singleton_for_d.mem_CD_on_Cd Pd_singletons_for_ds_simps dX_def
                          dest: Singleton_for_d.Cd_range')
          with X Xd_x_ds TruePref_tax.Theorem_1[of ds] \<open>Xd x \<notin> Xd ` ?Z\<close> \<open>y \<in> X''\<close>
          show ?thesis
            using Singleton_for_d.blocking_on_allocation[OF \<open>Singleton_for_d.blocking_on ds ?Z h X''\<close>]
            by (clarsimp simp: TruePref_tax.mem_CD_on_Cd TruePref_tax.Cd_greatest greatest_def Pd'_tax_x)
               (metis TruePref_tax.Pd_range' image_eqI inj_on_contraD TruePref_tax.Pd_refl)
        next
          case False with YYY show ?thesis
            by (simp add: Singleton_for_d.mem_CD_on_Cd TruePref_tax.mem_CD_on_Cd TruePref_tax_Cd_not_x)
        qed
      qed (use \<open>Singleton_for_d.blocking_on ds ?Z h X''\<close> in \<open>simp_all add: Singleton_for_d.blocking_on_def\<close>)
      with TruePref_tax.Theorem_1[of ds] show False by (simp add: TruePref_tax.blocking_on_imp_not_stable)
    qed
  qed
qed

theorem Theorem_11_fp_cop_F:
  shows "\<exists>y\<in>TruePref.cop ds. (x, y) \<in> Pd' (Xd x)"
proof -
  from Theorem_11_Pd'_tax
  obtain y where y: "y \<in> CH (TruePref_tax.fp_cop_F ds)"
            and xy: "(x, y) \<in> Pd'_tax (Xd x)" ..
  from TruePref_tax.stable_on_range'[OF TruePref_tax.Theorem_1]
  have "dX (CH (TruePref_tax.fp_cop_F ds)) (Xd x) \<subseteq> Field (Pd' (Xd x))"
    by (clarsimp simp: dX_def) (metis (no_types, hide_lams) Pd'_tax_Pd' contra_subsetD mono_Field)
  moreover
  from TruePref_tax.fp_cop_F_allocation[of ds] Pd'_tax_Pd' y xy
  have "Above (Pd' (Xd x)) (dX (CH (TruePref_tax.fp_cop_F ds)) (Xd x))
     \<subseteq> Above (Pd'_tax (Xd x)) (dX (CH (TruePref_tax.fp_cop_F ds)) (Xd x))"
    by - (rule Pd'_Above; fastforce simp: dX_singular above_def dest: TruePref_tax.Pd_Xd)
  moreover note Pd'_linear Pd'_range TruePref_tax.Theorem_1[of ds] y
  ultimately have z: "\<exists>z\<in>CH (TruePref.fp_cop_F ds). (y, z) \<in> Pd' (Xd y)"
    by - (rule TruePref_tax.Pd_above_irrelevant[where d'="Xd x" and X="CH (TruePref_tax.fp_cop_F ds)"];
          simp add: Pd'_tax_def)
  from Pd'_linear xy z show ?thesis
    unfolding Pd'_tax_def order_on_defs by clarsimp (metis TruePref.Pd_Xd transE)
qed

end

locale ContractsWithSubstitutesAndLADAndTruePrefs =
  ContractsWithSubstitutesAndLAD + TruePrefs

sublocale ContractsWithSubstitutesAndLADAndTruePrefs
        < ContractsWithUnilateralSubstitutesAndIRCAndLADAndTruePrefs
by %invisible unfold_locales

context ContractsWithSubstitutesAndLADAndTruePrefs
begin

interpretation TruePref: ContractsWithSubstitutesAndLAD Xd Xh Pd' Ch
using %invisible Pd'_linear Pd'_range Ch_range Ch_singular Ch_substitutes Ch_irc Ch_lad
by unfold_locales blast+

theorem Theorem_11:
  shows "\<exists>y\<in>match (TruePref.gfp_F ds). (x, y) \<in> Pd' (Xd x)"
using Theorem_11_fp_cop_F TruePref.Theorem_15_match by simp

end

text\<open>

Note that this theorem depends on the hypotheses introduced by the
@{const "TruePrefs"} locale, and only applies to doctor @{term "Xd
x"}. The following sections show more general and syntactically
self-contained results.

We omit \citet[Theorem~12]{HatfieldMilgrom:2005}, which demonstrates
the almost-necessity of LAD for truth revelation to be the dominant
strategy for doctors.

\<close>


subsection\<open> \citet{HatfieldKojima:2009,HatfieldKojima:2010}: The doctor-optimal match is group strategy-proof \label{sec:strategic-gsp} \<close>

text \<open>

\citet[Theorem~7]{HatfieldKojima:2010} assert that the COP is group
strategy-proof, which we define below. We begin by focusing on a
single agent \citep{HatfieldKojima:2009}: \begin{quote}

A mechanism @{term "\<phi>"} is @{emph \<open>strategy-proof\<close>} if, for any
preference profile @{term "Pd"}, there is no doctor @{term "d"} and
preferences @{term "Pd'"} such that @{term "d"} strictly prefers
@{term "y\<^sub>d"} to @{term "x\<^sub>d"} according to @{term "Pd
d"}, where @{term "x\<^sub>d"} and @{term "y\<^sub>d"} are the
(possibly null) contracts for @{term "d"} in @{term "\<phi> Pd"} and
\<open>\<phi> Pd(d := Pd')\<close>, respectively.

\end{quote}

The syntax @{thm "fun_upd_def"} denotes function update at a point.

We make this definition in the \<open>Contracts\<close> locale to
avail ourselves of some types and the \<open>Xd\<close> and
\<open>Xh\<close> constants. We also restrict hospital preferences to
those that guarantee our earlier strategic results.  As @{term
"gfp_F"} requires these to satisfy the stronger @{const "substitutes"}
constraint for stable matches to exist, we now deal purely with the
COP.

\<close>

context Contracts
begin

abbreviation (input) mechanism_domain :: "('d \<Rightarrow> 'x rel) \<Rightarrow> ('h \<Rightarrow> 'x cfun) \<Rightarrow> bool" where
  "mechanism_domain \<equiv> ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh"

definition strategy_proof :: "'d set \<Rightarrow> ('d, 'h, 'x) mechanism \<Rightarrow> bool" where
  "strategy_proof ds \<phi> \<longleftrightarrow>
    (\<forall>Pd Ch. mechanism_domain Pd Ch \<longrightarrow>
     \<not>(\<exists>d\<in>ds. \<exists>Pd'. mechanism_domain (Pd(d:=Pd')) Ch
       \<and> (\<exists>y\<in>\<phi> (Pd(d:=Pd')) Ch ds. y \<in> AboveS (Pd d) (dX (\<phi> Pd Ch ds) d))))"

(*<*)

lemma strategy_proofI:
  assumes "\<And>Pd Pd' Ch d y. \<lbrakk> mechanism_domain Pd Ch; mechanism_domain (Pd(d:=Pd')) Ch; d \<in> ds;
                             y \<in> \<phi> (Pd(d := Pd')) Ch ds; y \<in> Field (Pd d);
                             \<forall>x\<in>dX (\<phi> Pd Ch ds) d. x \<noteq> y \<and> (x, y) \<in> Pd d \<rbrakk> \<Longrightarrow> False"
  shows "strategy_proof ds \<phi>"
unfolding strategy_proof_def AboveS_def using assms by blast

(*>*)
text\<open>\<close>

theorem fp_cop_F_strategy_proof:
  shows "strategy_proof ds Contracts.cop" (is "strategy_proof _ ?\<phi>")
proof %invisible (rule strategy_proofI)
  fix Pd Pd' Ch d y
  assume A: "mechanism_domain Pd Ch" and B: "mechanism_domain (Pd(d:=Pd')) Ch"
     and y: "y \<in> ?\<phi> (Pd(d := Pd')) Ch ds" "y \<in> Field (Pd d)" "\<forall>x\<in>dX (?\<phi> Pd Ch ds) d. x \<noteq> y \<and> (x, y) \<in> Pd d"
  from A interpret TruePref: ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh Pd Ch .
  from B interpret ManiPref: ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh "Pd(d := Pd')" Ch .
  from B y interpret ManiPref: ContractsWithUnilateralSubstitutesAndIRCAndLADAndTruePrefs Xd Xh "Pd(d := Pd')" Ch y "?\<phi> (Pd(d := Pd')) Ch ds" ds Pd
    by unfold_locales (simp_all add: FieldI2 TruePref.Pd_Xd TruePref.Pd_linear TruePref.Pd_range' subsetI ManiPref.Theorem_1)
  from ManiPref.Theorem_11_fp_cop_F obtain z where "z \<in> TruePref.cop ds" "(y, z) \<in> Pd (Xd y)" ..
  with TruePref.Pd_linear TruePref.stable_on_allocation[OF TruePref.Theorem_1[of ds]] TruePref.Pd_Xd TruePref.Pd_range' y
  show False
    unfolding order_on_defs antisym_def dX_def by (metis (mono_tags, lifting) mem_Collect_eq)
qed

end

text\<open>

The adaptation to groups is straightforward
\citep{HatfieldKojima:2009,HatfieldKojima:2010}:
\begin{quote}

A mechanism @{term "\<phi>"} is @{emph \<open>group strategy-proof\<close>} if, for
any preference profile @{term "Pd"}, there is no group of doctors
@{term "ds' \<subseteq> ds"} and a preference profile @{term "Pd'"}
such that every @{term "d \<in> ds'"} strictly prefers @{term
"y\<^sub>d"} to @{term "x\<^sub>d"} according to @{term "Pd d"}, where
@{term "x\<^sub>d"} and @{term "y\<^sub>d"} are the (possibly null)
contracts for @{term "d"} in @{term "\<phi> Pd"} and \<open>\<phi>
Pd(d\<^sub>1 := Pd' d\<^sub>1, \<dots>, d\<^sub>n := Pd' d\<^sub>n)\<close>,
respectively.

\end{quote}

This definition requires all doctors in the coalition to strictly
prefer the outcome with manipulated preferences, as
\citeauthor{Kojima:2010}'s bossiness results (see
\S\ref{sec:bossiness}) show that a doctor may influence other doctors'
allocations without affecting their own. See
\citet[\S3]{HatfieldKojima:2009} for discussion, and also
\citet[Chapter~4]{RothSotomayor:1990}; in particular their \S4.3.1
discusses the robustness of these results and exogenous transfers.

\<close>

context Contracts
begin

definition group_strategy_proof :: "'d set \<Rightarrow> ('d, 'h, 'x) mechanism \<Rightarrow> bool" where
  "group_strategy_proof ds \<phi> \<longleftrightarrow>
    (\<forall>Pd Ch. mechanism_domain Pd Ch \<longrightarrow>
     \<not>(\<exists>ds'\<subseteq>ds. ds' \<noteq> {} \<and> (\<exists>Pd'. mechanism_domain (override_on Pd Pd' ds') Ch
       \<and> (\<forall>d\<in>ds'. \<exists>y\<in>\<phi> (override_on Pd Pd' ds') Ch ds. y \<in> AboveS (Pd d) (dX (\<phi> Pd Ch ds) d)))))"

(*<*)

lemma group_strategy_proofI:
  assumes "\<And>Pd Pd' Ch ds'. \<lbrakk> mechanism_domain Pd Ch; mechanism_domain (override_on Pd Pd' ds') Ch; ds' \<subseteq> ds; ds' \<noteq> {};
                             \<forall>d\<in>ds'. \<exists>y\<in>\<phi> (override_on Pd Pd' ds') Ch ds. y \<in> AboveS (Pd d) (dX (\<phi> Pd Ch ds) d) \<rbrakk> \<Longrightarrow> False"
  shows "group_strategy_proof ds \<phi>"
unfolding group_strategy_proof_def using assms by blast

lemmas group_strategy_proofD = iffD1[OF group_strategy_proof_def, simplified, unfolded disj_imp, simplified, rule_format]

(*>*)

lemma group_strategy_proof_strategy_proof:
  assumes "group_strategy_proof ds \<phi>"
  shows "strategy_proof ds \<phi>"
proof %invisible (rule strategy_proofI)
  fix Pd Pd' Ch d y
  assume "mechanism_domain Pd Ch" "mechanism_domain (Pd(d := Pd')) Ch" "d \<in> ds"
         "y \<in> \<phi> (Pd(d := Pd')) Ch ds" "y \<in> Field (Pd d)" "\<forall>x\<in>dX (\<phi> Pd Ch ds) d. x \<noteq> y \<and> (x, y) \<in> Pd d"
  with assms show False
    unfolding group_strategy_proof_def
    by (clarsimp dest!: spec[where x=Pd] spec[where x=Ch])
       (fastforce simp: override_on_insert AboveS_def dest!: spec[where x="{d}"])
qed

end

text\<open>

\label{sec:strategic-hk2010-lemma1}

Perhaps surprisingly, \citet[Lemma~1, for a single
doctor]{HatfieldKojima:2010} assert that shuffling any contract above
the doctor-optimal one to the top of a doctor's preference order
preserves exactly the doctor-optimal match, which on the face of it
seems to contradict the bossiness result of \S\ref{sec:bossiness}: by
the earlier strategy-proofness results, this cannot affect the outcome
for that particular doctor, but by bossiness it may affect others.
The key observation is that this manipulation preserves blocking
coalitions in the presence of @{const "lad"}.

This result is central to showing the group-strategy-proofness of the
COP.

\<close>

context Contracts
begin

definition shuffle_to_top :: "'x set \<Rightarrow> 'd \<Rightarrow> 'x rel" where
  "shuffle_to_top Y = (\<lambda>d. Pd d - dX Y d \<times> UNIV \<union> (Domain (Pd d) \<union> dX Y d) \<times> dX Y d)"

definition Pd_shuffle_to_top :: "'d set \<Rightarrow> 'x set \<Rightarrow> 'd \<Rightarrow> 'x rel" where
  "Pd_shuffle_to_top ds' Y = override_on Pd (shuffle_to_top Y) ds'"

(*<*)

lemma shuffle_to_top_Field:
  assumes "allocation Y"
  shows "Field (shuffle_to_top Y d) = Field (Pd d) \<union> dX Y d"
unfolding shuffle_to_top_def Field_def using dX_empty_or_singleton[OF assms]
by (auto simp: Domain.simps; meson FieldI2 equalityE Pd_refl)

lemma shuffle_to_top_Total:
  assumes "allocation Y"
  shows "Total (shuffle_to_top Y d)"
using Pd_linear'[of d] dX_empty_or_singleton[OF assms]
unfolding order_on_defs total_on_def shuffle_to_top_Field[OF assms]
by (auto simp: shuffle_to_top_def Domain.simps dest: refl_onD)

lemma shuffle_to_top_linear:
  assumes "allocation Y"
  shows "Linear_order (shuffle_to_top Y d)"
using Pd_linear'[of d] dX_empty_or_singleton[OF assms] shuffle_to_top_Total[OF assms]
unfolding shuffle_to_top_def order_on_defs
by (auto simp: Field_def intro!: antisymI refl_onI transI dest: refl_onD antisymD elim: transE)

lemma shuffle_to_top_range:
  shows "Field (shuffle_to_top Y d) \<subseteq> {x. Xd x = d}"
unfolding shuffle_to_top_def using Pd_range dX_range by (force simp: Field_def)

lemma shuffle_to_top_range':
  assumes "(x, y) \<in> shuffle_to_top Y d"
  shows "x \<in> Field (Pd d) \<union> dX Y d \<and> y \<in> Field (Pd d) \<union> dX Y d"
using assms unfolding shuffle_to_top_def by (auto intro: FieldI1 FieldI2)

lemma Pd_shuffle_to_top_linear:
  assumes "allocation Y"
  shows "Linear_order (Pd_shuffle_to_top ds' Y d)"
unfolding Pd_shuffle_to_top_def using Pd_linear shuffle_to_top_linear[OF assms] by (cases "d \<in> ds'") simp_all

lemma Pd_shuffle_to_top_range:
  shows "Field (Pd_shuffle_to_top ds' Y d) \<subseteq> {x. Xd x = d}"
unfolding Pd_shuffle_to_top_def using Pd_range shuffle_to_top_range by (cases "d \<in> ds'") simp_all

lemma Pd_shuffle_to_top_simps:
  shows "Pd_shuffle_to_top (insert d ds') Y = (Pd_shuffle_to_top ds' Y)(d := shuffle_to_top Y d)"
    and "d \<in> ds' \<Longrightarrow> Pd_shuffle_to_top ds' Y d = shuffle_to_top Y d"
    and "d \<notin> ds' \<Longrightarrow> Pd_shuffle_to_top ds' Y d = Pd d"
unfolding Pd_shuffle_to_top_def by (simp_all add: override_on_insert)

lemma Pd_shuffle_to_top_Field:
  assumes "allocation Y"
  shows "Field (Pd_shuffle_to_top ds' Y d) = Field (Pd d) \<union> (if d \<in> ds' then dX Y d else {})"
by (simp add: Pd_shuffle_to_top_simps shuffle_to_top_Field[OF assms])

lemma Above_shuffle_to_top:
  assumes "x \<in> Above (shuffle_to_top Y (Xd x)) X"
  assumes "y \<in> Y"
  assumes "allocation Y"
  assumes "y \<in> X"
  shows "x = y"
using assms unfolding Above_def shuffle_to_top_def
by (fastforce simp: dX_singular dest: Pd_Xd dX_range' Pd_range' inj_onD)

(*>*)

end

context ContractsWithUnilateralSubstitutesAndIRCAndLAD
begin

lemma Lemma_1:
  assumes "allocation Y"
  assumes III: "\<forall>d\<in>ds''. \<exists>y\<in>Y. y \<in> AboveS (Pd d) (dX (cop ds) d)"
  shows "cop ds = Contracts.cop (Pd_shuffle_to_top ds'' Y) Ch ds"
using finite[of ds''] subset_refl
proof(induct ds'' rule: finite_subset_induct')
  case empty show ?case by (simp add: Pd_shuffle_to_top_simps)
next
  case (insert d ds')
  from insert
  interpret Pds': ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh "Pd_shuffle_to_top ds' Y" Ch
    using %invisible Pd_shuffle_to_top_linear[OF \<open>allocation Y\<close>] Pd_shuffle_to_top_range Ch_range Ch_singular Ch_unilateral_substitutes Ch_irc Ch_lad
    by unfold_locales simp_all
  let ?Z = "CH (Pds'.fp_cop_F ds)"
  note IH = \<open>cop ds = ?Z\<close>
  let ?Pd_shuffle_to_top = "Pd_shuffle_to_top (insert d ds') Y"
  from insert interpret Pdds': ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh ?Pd_shuffle_to_top Ch
    using %invisible Pd_shuffle_to_top_linear[OF \<open>allocation Y\<close>] Pd_shuffle_to_top_range Ch_range Ch_singular Ch_unilateral_substitutes Ch_irc Ch_lad
    by unfold_locales (simp_all add: Pd_shuffle_to_top_simps(1)[symmetric])
  \<comment> \<open>\citet[Lemma~1, for a single doctor]{HatfieldKojima:2010}\<close>
  have XXX: "?Z = CH (Pdds'.fp_cop_F ds)"
  proof(rule Pdds'.doctor_optimal_match_unique[OF Pdds'.doctor_optimal_matchI Pdds'.fp_cop_F_doctor_optimal_match])
    show "Pdds'.stable_on ds ?Z"
    proof(rule Pdds'.stable_onI)
      show "Pdds'.individually_rational_on ds ?Z"
      proof(rule Pdds'.individually_rational_onI)
        show "Pdds'.CD_on ds ?Z = ?Z" (is "?lhs = ?rhs")
        proof(rule set_elem_equalityI)
          fix x assume "x \<in> ?rhs"
          with \<open>allocation Y\<close> IH Pds'.Theorem_1[of ds] \<open>d \<notin> ds'\<close> show "x \<in> ?lhs"
            by (clarsimp simp: Pds'.stable_on_Xd Pdds'.mem_CD_on_Cd Pdds'.Cd_greatest greatest_def
                               Pd_shuffle_to_top_Field[OF \<open>allocation Y\<close>],
                simp add: Pd_shuffle_to_top_simps shuffle_to_top_def dX_def Set.Ball_def,
                metis stable_on_range'[OF Theorem_1[of ds]] inj_on_contraD[OF Pds'.fp_cop_F_allocation[of ds]]
                      fp_cop_F_worst[of _ ds] Pd_range' Pds'.CH_range')
        qed (meson IntE Pdds'.CD_on_range')
        show "CH ?Z = ?Z" by (simp add: CH_irc_idem)
      qed
      show "Pdds'.stable_no_blocking_on ds ?Z"
      proof(rule Pdds'.stable_no_blocking_onI2)
        fix h X'' assume Pbo: "Pdds'.blocking_on ds ?Z h X''"
        have "Pds'.blocking_on ds ?Z h X''"
        proof(rule Pds'.blocking_onI)
          fix x assume "x \<in> X''"
          note Pbos = Pdds'.blocking_on_allocation[OF \<open>Pdds'.blocking_on ds ?Z h X''\<close>]
                      Pdds'.blocking_on_CD_on'[OF \<open>Pdds'.blocking_on ds ?Z h X''\<close> \<open>x \<in> X''\<close>]
                      Pdds'.blocking_on_Cd[OF \<open>Pdds'.blocking_on ds ?Z h X''\<close>, where d="Xd x"]
          show "x \<in> Pds'.CD_on ds (?Z \<union> X'')"
          proof(cases "Xd x = d")
            case True
            from \<open>allocation Y\<close> III \<open>d \<in> ds''\<close> \<open>Xd x = d\<close>
            have "dX Y (Xd x) \<subseteq> Field (Pd (Xd x))"
                by clarsimp (metis AboveS_Pd_Xd AboveS_Field dX_range' inj_on_eq_iff)
            moreover with \<open>allocation Y\<close> \<open>d \<notin> ds'\<close>
                          Pdds'.blocking_on_Field[OF \<open>Pdds'.blocking_on ds ?Z h X''\<close>, where d=d] \<open>Xd x = d\<close>
            have "dX X'' (Xd x) \<subseteq> Field (Pd (Xd x))"
              by (force simp: Pd_shuffle_to_top_simps shuffle_to_top_Field)
            moreover note \<open>allocation Y\<close> bspec[OF III[unfolded IH] \<open>d \<in> ds''\<close>] \<open>d \<notin> ds'\<close> \<open>x \<in> X''\<close> \<open>Xd x = d\<close>
                          Pds'.stable_on_allocation[OF Pds'.Theorem_1] Pbos
            ultimately show ?thesis
              by (clarsimp simp: Pdds'.mem_CD_on_Cd Pds'.mem_CD_on_Cd Pds'.Cd_Above Pdds'.Cd_Above
                                 Int_Un_distrib2 Pd_shuffle_to_top_Field)
                 (clarsimp simp: Pd_shuffle_to_top_simps dX_singular dX_Int_Field_Pd;
                  fastforce simp: Above_def AboveS_def Pd_refl shuffle_to_top_def dX_def intro: FieldI1 dest: Pd_range' iff: inj_on_eq_iff)
         next
            case False
            from Pbos \<open>Xd x \<noteq> d\<close>
            show ?thesis
              by (simp add: Pdds'.mem_CD_on_Cd Pds'.mem_CD_on_Cd Pds'.Cd_greatest Pdds'.Cd_greatest)
                 (simp add: Pd_shuffle_to_top_simps)
          qed
        qed (use \<open>Pdds'.blocking_on ds ?Z h X''\<close> in \<open>simp_all add: Pdds'.blocking_on_def\<close>)
        with Pds'.Theorem_1[of ds] show False by (simp add: Pds'.blocking_on_imp_not_stable)
      qed
    qed
  next
    fix W w assume "Pdds'.stable_on ds W" "w \<in> W"
      from III \<open>d \<in> ds''\<close> IH
      obtain y where Y: "y \<in> Y" "y \<in> AboveS (Pd d) (dX (Pds'.cop ds) d)" "Xd y = d"
        by (metis AboveS_Pd_Xd)
      show "\<exists>z\<in>Pds'.cop ds. (w, z) \<in> Pd_shuffle_to_top (insert d ds') Y (Xd w)"
      proof(cases "y \<in> W")
        case True note \<open>y \<in> W\<close>
        from \<open>d \<notin> ds'\<close> \<open>Pdds'.stable_on ds W\<close> Y \<open>y \<in> W\<close>
        interpret Pdds': ContractsWithUnilateralSubstitutesAndIRCAndLADAndTruePrefs
                           Xd Xh "Pd_shuffle_to_top (insert d ds') Y" Ch y W ds "Pd_shuffle_to_top ds' Y"
          using %invisible Pds'.Pd_linear Pds'.Pd_range Pd_shuffle_to_top_simps Pd_range' unfolding AboveS_def
          by unfold_locales auto
        from \<open>d \<notin> ds'\<close> Y Pdds'.Theorem_11_fp_cop_F have False
          using Pds'.stable_on_allocation[OF Pds'.Theorem_1[of ds]] Pd_linear Pd_range'
          unfolding order_on_defs antisym_def AboveS_def dX_def
          by (clarsimp simp: Pd_shuffle_to_top_simps) (blast dest: Pd_Xd)
        then show ?thesis ..
      next
        case False note \<open>y \<notin> W\<close>
        show ?thesis
        proof (cases "Pds'.stable_on ds W")
          case True note \<open>Pds'.stable_on ds W\<close>
          with \<open>allocation Y\<close> \<open>d \<notin> ds'\<close> Y \<open>w \<in> W\<close> \<open>y \<notin> W\<close> show ?thesis
            using Pds'.Theorem_5[OF \<open>Pds'.stable_on ds W\<close> \<open>w \<in> W\<close>]
            by (auto 0 2 simp: Pd_shuffle_to_top_simps shuffle_to_top_def dX_def AboveS_def dest: Pd_range' inj_onD)
        next
          case False note \<open>\<not>Pds'.stable_on ds W\<close>
          then show ?thesis
          proof(cases rule: Pds'.not_stable_on_cases)
            case not_individually_rational
            note Psos = Pdds'.stable_on_allocation[OF \<open>Pdds'.stable_on ds W\<close>]
                        Pdds'.stable_on_CH[OF \<open>Pdds'.stable_on ds W\<close>]
                        Pdds'.stable_on_Xd[OF \<open>Pdds'.stable_on ds W\<close>]
            have "x \<in> Pds'.Cd (Xd x) W" if "x \<in> W" for x
            proof(cases "Xd x = d")
              case True
              with \<open>allocation Y\<close> \<open>allocation W\<close> Y(1,3) \<open>y \<notin> W\<close>
                   Pdds'.stable_on_range'[OF \<open>Pdds'.stable_on ds W\<close> \<open>x \<in> W\<close>] \<open>x \<in> W\<close>
              show ?thesis by (force simp: Pd_shuffle_to_top_Field dest: dX_range' inj_onD intro: Pds'.Cd_single)
            next
              case False
              with \<open>allocation Y\<close> \<open>allocation W\<close> Pdds'.stable_on_range'[OF \<open>Pdds'.stable_on ds W\<close> \<open>x \<in> W\<close>] \<open>x \<in> W\<close>
              show ?thesis by (auto simp: Pd_shuffle_to_top_Field intro!: Pds'.Cd_single)
            qed
            with not_individually_rational \<open>Pdds'.CH W = W\<close> Psos(3) show ?thesis
              unfolding Pds'.individually_rational_on_def by (auto simp: Pds'.mem_CD_on_Cd dest: Pds'.Cd_range')
        next
          case not_no_blocking
          then obtain h X'' where Pbo: "Pds'.blocking_on ds W h X''"
            unfolding Pds'.stable_no_blocking_on_def by blast
          have "Pdds'.blocking_on ds W h X''"
          proof(rule Pdds'.blocking_onI)
            fix x assume "x \<in> X''"
            note Pbos = Pds'.blocking_on_allocation[OF \<open>Pds'.blocking_on ds W h X''\<close>]
                        Pds'.blocking_on_CD_on'[OF \<open>Pds'.blocking_on ds W h X''\<close> \<open>x \<in> X''\<close>]
                        Pds'.blocking_on_Field[OF \<open>Pds'.blocking_on ds W h X''\<close>, where d=d]
            show "x \<in> Pdds'.CD_on ds (W \<union> X'')"
            proof(cases "Xd x = d")
              case True
              from \<open>allocation Y\<close> III \<open>d \<in> ds''\<close>  \<open>Xd x = d\<close>
              have "dX Y (Xd x) \<subseteq> Field (Pd (Xd x))"
                by clarsimp (metis AboveS_Pd_Xd AboveS_Field dX_range' inj_on_eq_iff)
              moreover with \<open>d \<notin> ds'\<close> \<open>Xd x = d\<close> Pbos
              have "dX X'' (Xd x) \<subseteq> Field (Pd (Xd x))"
                by (clarsimp simp: Pd_shuffle_to_top_simps)
              moreover note \<open>allocation Y\<close> \<open>d \<notin> ds'\<close> \<open>y \<notin> W\<close> \<open>Xd y = d\<close> \<open>x \<in> X''\<close> Pbos
              ultimately show ?thesis
                by (clarsimp simp: Pdds'.mem_CD_on_Cd Pds'.mem_CD_on_Cd Pds'.Cd_Above Pdds'.Cd_Above
                                   Int_Un_distrib2)
                   (clarsimp simp: Pd_shuffle_to_top_simps shuffle_to_top_Field dX_singular dX_Int_Field_Pd Un_absorb2,
                    force simp: \<open>y \<in> Y\<close> shuffle_to_top_def dX_def Above_def dest: inj_onD intro: FieldI1)
            next
              case False
              from Pbos \<open>Xd x \<noteq> d\<close> show ?thesis
                by (simp add: Pdds'.mem_CD_on_Cd Pds'.mem_CD_on_Cd Pds'.Cd_greatest Pdds'.Cd_greatest)
                   (simp add: Pd_shuffle_to_top_simps)
            qed
          qed (use \<open>Pds'.blocking_on ds W h X''\<close> in \<open>simp_all add: Pds'.blocking_on_def\<close>)
          with \<open>Pdds'.stable_on ds W\<close> have False by (simp add: Pdds'.blocking_on_imp_not_stable)
          then show ?thesis ..
        qed
      qed
    qed
  qed
  from \<open>?Z = CH (Pdds'.fp_cop_F ds)\<close> IH show "cop ds = Pdds'.cop ds" by simp
qed

text\<open>

The top-level theorem states that the COP is group strategy proof. To
account for the quantification over preferences, we directly use the
raw constants from the @{const "Contracts"} locale.

\<close>

theorem fp_cop_F_group_strategy_proof:
  shows "group_strategy_proof ds Contracts.cop"
        (is "group_strategy_proof _ ?\<phi>")
proof(rule group_strategy_proofI)
  fix Pd Pds' Ch ds'
  assume XXX: "mechanism_domain Pd Ch" "mechanism_domain (override_on Pd Pds' ds') Ch"
     and YYY: "ds' \<subseteq> ds" "ds' \<noteq> {}"
     and ZZZ: "\<forall>d\<in>ds'. \<exists>y\<in>?\<phi> (override_on Pd Pds' ds') Ch ds. y \<in> AboveS (Pd d) (dX (?\<phi> Pd Ch ds) d)"
  from XXX(1) interpret TruePref: ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh Pd Ch .
  from XXX(2) interpret
    ManiPref: ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh "override_on Pd Pds' ds'" Ch .
  let ?Y = "ManiPref.cop ds"
  let ?Z = "TruePref.cop ds"
  let ?Pd_shuffle_to_top = "TruePref.Pd_shuffle_to_top ds' ?Y"
  interpret ManiPref': ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh ?Pd_shuffle_to_top Ch
    using TruePref.Ch_unilateral_substitutes TruePref.Ch_irc TruePref.Ch_lad TruePref.Ch_range TruePref.Ch_singular
          TruePref.Pd_shuffle_to_top_linear ManiPref.stable_on_allocation[OF ManiPref.Theorem_1[of ds]]
          TruePref.Pd_shuffle_to_top_range ManiPref.dX_range
    by unfold_locales simp_all
  let ?Y' = "ManiPref'.cop ds"
  have "ManiPref'.stable_on ds ?Y"
  proof(rule ManiPref'.stable_onI)
    show "ManiPref'.individually_rational_on ds ?Y"
    proof(rule ManiPref'.individually_rational_onI)
      show "ManiPref'.CD_on ds ?Y = ?Y" (is "?lhs = ?rhs")
      proof(rule set_elem_equalityI)
        fix x assume "x \<in> ?rhs"
        then have "Xd x \<in> ds \<and> (Xd x \<notin> ds' \<longrightarrow> x \<in> Field (Pd (Xd x)))"
          by (metis ManiPref.fp_cop_F_range_inv' TruePref.CH_range' override_on_apply_notin)
        with ManiPref.Theorem_1[of ds] \<open>x \<in> ?rhs\<close> show "x \<in> ?lhs"
          by (fastforce dest: ManiPref.stable_on_allocation
                    simp: ManiPref'.Cd_single ManiPref'.mem_CD_on_Cd TruePref.Pd_shuffle_to_top_Field dX_def)
      qed (meson IntE ManiPref'.CD_on_range')
      show "ManiPref'.CH ?Y = ?Y" by (simp add: ManiPref'.CH_irc_idem)
    qed
    show "ManiPref'.stable_no_blocking_on ds ?Y"
    proof(rule ManiPref'.stable_no_blocking_onI2)
      fix h X'' assume "ManiPref'.blocking_on ds ?Y h X''"
      have "ManiPref.blocking_on ds ?Y h X''"
      proof(rule ManiPref.blocking_onI)
        fix x assume "x \<in> X''"
        note Pbos = ManiPref'.blocking_on_Field[OF \<open>ManiPref'.blocking_on ds ?Y h X''\<close>, where d="Xd x"]
                    ManiPref'.blocking_on_allocation[OF \<open>ManiPref'.blocking_on ds ?Y h X''\<close>]
                    ManiPref'.blocking_on_CD_on'[OF \<open>ManiPref'.blocking_on ds ?Y h X''\<close> \<open>x \<in> X''\<close>]
                    ManiPref'.blocking_on_Cd[OF \<open>ManiPref'.blocking_on ds ?Y h X''\<close>, where d="Xd x"]
        show "x \<in> ManiPref.CD_on ds (?Y \<union> X'')"
        proof(cases "Xd x \<in> ds'")
          case True
          from ManiPref.fp_cop_F_allocation[of ds] \<open>x \<in> X''\<close> \<open>Xd x \<in> ds'\<close> Pbos bspec[OF ZZZ \<open>Xd x \<in> ds'\<close>]
          have "dX X'' (Xd x) \<subseteq> Field (Pds' (Xd x))"
            by (clarsimp simp: dX_singular ManiPref'.mem_CD_on_Cd ManiPref'.Cd_Above TruePref.Pd_shuffle_to_top_Field)
               (fastforce simp: TruePref.Pd_shuffle_to_top_simps dX_singular dest: TruePref.AboveS_Pd_Xd
                          dest: ManiPref.fp_cop_F_range_inv' ManiPref.CH_range' TruePref.Above_shuffle_to_top)
          moreover from ManiPref.stable_on_range'[OF ManiPref.Theorem_1] \<open>Xd x \<in> ds'\<close>
          have "dX ?Y (Xd x) \<subseteq> Field (Pds' (Xd x))"
            by (metis dX_range' override_on_apply_in subsetI)
          moreover note bspec[OF ZZZ \<open>Xd x \<in> ds'\<close>] \<open>x \<in> X''\<close> \<open>Xd x \<in> ds'\<close> Pbos
          ultimately show ?thesis
            using ManiPref.Pd_linear'[of "Xd x"] ManiPref.fp_cop_F_allocation[of ds]
                  ManiPref'.fp_cop_F_allocation[of ds]
            by (clarsimp simp: ManiPref'.mem_CD_on_Cd ManiPref'.Cd_Above_dX ManiPref.mem_CD_on_Cd
                               ManiPref.Cd_Above_dX dX_union dX_singular
                               TruePref.Pd_shuffle_to_top_Field TruePref.AboveS_Pd_Xd)
               (force simp: TruePref.Pd_shuffle_to_top_simps insert_absorb elim: Above_Linear_singleton
                     dest!: TruePref.Above_shuffle_to_top)
        next
          case False
          with Pbos show ?thesis
            by (fastforce simp: ManiPref'.mem_CD_on_Cd ManiPref'.Cd_greatest ManiPref.mem_CD_on_Cd
                                ManiPref.Cd_greatest TruePref.Pd_shuffle_to_top_simps)
        qed
      qed (use \<open>ManiPref'.blocking_on ds ?Y h X''\<close> in \<open>simp_all add: ManiPref'.blocking_on_def\<close>)
      with ManiPref.Theorem_1[of ds] show False by (simp add: ManiPref.blocking_on_imp_not_stable)
    qed
  qed
  with ManiPref'.stable_on_allocation have "{x \<in> ?Y. Xd x \<in> ds'} \<subseteq> {x \<in> ?Y'. Xd x \<in> ds'}"
    by (force dest: ManiPref'.Theorem_5[of ds]
              simp: TruePref.Pd_shuffle_to_top_simps TruePref.shuffle_to_top_def dX_def dest: inj_onD)
  moreover
  from ManiPref.stable_on_allocation[OF ManiPref.Theorem_1] ZZZ
  have "?Z = ?Y'" by (rule TruePref.Lemma_1)
  moreover note YYY ZZZ
  ultimately show False
    unfolding AboveS_def dX_def by (fastforce simp: ex_in_conv[symmetric] dest: TruePref.Pd_range')
qed

end

text (in ContractsWithSubstitutes) \<open>

Again, this result does not directly apply to @{term "gfp_F"} due to
the mechanism domain hypothesis.

Finally, \citet[Corollary~2]{HatfieldKojima:2010} (respectively,
\citet[Corollary~1]{HatfieldKojima:2009}) assert that the COP (@{const
"gfp_F"}) is ``weakly Pareto optimal'', i.e., that there is no @{const
"individually_rational"} allocation that every doctor strictly prefers
to the doctor-optimal match.

\<close>

context ContractsWithUnilateralSubstitutesAndIRCAndLAD
begin

theorem Corollary_2:
  assumes "ds \<noteq> {}"
  shows "\<not>(\<exists>Y. individually_rational_on ds Y
        \<and> (\<forall>d\<in>ds. \<exists>y\<in>Y. y \<in> AboveS (Pd d) (dX (cop ds) d)))"
proof(unfold individually_rational_on_def, safe)
  fix Y assume "CD_on ds Y = Y" "CH Y = Y"
           and Z: "\<forall>d\<in>ds. \<exists>y\<in>Y. y \<in> AboveS (Pd d) (dX (cop ds) d)"
  from \<open>CD_on ds Y = Y\<close> have "allocation Y" by (metis CD_on_inj_on_Xd)
  from \<open>CD_on ds Y = Y\<close>
  interpret Y: ContractsWithUnilateralSubstitutesAndIRCAndLAD Xd Xh "Pd_singletons_for_ds Y ds" Ch
    using Ch_unilateral_substitutes Ch_irc Ch_lad Ch_range Ch_singular Pd_singletons_for_ds_range
          Pd_singletons_for_ds_linear[OF CD_on_inj_on_Xd]
    by unfold_locales (simp_all, metis)
  from Y.fp_cop_F_doctor_optimal_match Y.doctor_optimal_matchI
  have "CH (Y.fp_cop_F ds) = Y"
  proof(rule Y.doctor_optimal_match_unique)
    show "Y.stable_on ds Y"
    proof(rule Y.stable_onI)
      show "Y.individually_rational_on ds Y"
      proof(rule Y.individually_rational_onI)
        from \<open>CD_on ds Y = Y\<close> CD_on_Xd[where A=Y and ds=ds] show "Y.CD_on ds Y = Y"
          unfolding Y.CD_on_def CD_on_def
          by (force simp: Y.Cd_greatest Cd_greatest greatest_def Pd_singletons_for_ds_simps dX_def)
        from \<open>CH Y = Y\<close> show "Y.CH Y = Y" .
      qed
      show "Y.stable_no_blocking_on ds Y"
        by (rule Y.stable_no_blocking_onI,
            drule subset_trans[OF _ Y.CD_on_range],
            clarsimp simp: Pd_singletons_for_ds_def dX_def Un_absorb1 subset_eq sup_commute)
    qed
  next
    fix x X assume "x \<in> X" "Y.stable_on ds X"
    with Y.Theorem_5[of ds X x] Pd_singletons_for_ds_linear[OF \<open>allocation Y\<close>]
    show "\<exists>y\<in>Y. (x, y) \<in> Pd_singletons_for_ds Y ds (Xd x)"
      by (fastforce simp: Pd_singletons_for_ds_simps Y.stable_on_Xd dX_def)
  qed
  from Z \<open>CH (Y.fp_cop_F ds) = Y\<close> show False
    using group_strategy_proofD[OF
      fp_cop_F_group_strategy_proof
      ContractsWithUnilateralSubstitutesAndIRCAndLAD_axioms subset_refl
      \<open>ds \<noteq> {}\<close>
      Y.ContractsWithUnilateralSubstitutesAndIRCAndLAD_axioms[unfolded Pd_singletons_for_ds_def]]
    unfolding Pd_singletons_for_ds_def by force
qed

end

text\<open>

\citet[\S4.4]{RothSotomayor:1990} discuss how the non-proposing agents
can strategise to improve their outcomes in one-to-one matches.

\<close>
(*<*)

end
(*>*)
