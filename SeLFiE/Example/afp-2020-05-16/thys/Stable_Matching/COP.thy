(*<*)
theory COP
imports
  Contracts
begin

(*>*)
section\<open> \citet{HatfieldKojima:2010}: Substitutes and stability for matching with contracts \label{sec:cop} \<close>

text\<open>

\citet{HatfieldKojima:2010} set about weakening @{const "substitutes"}
and therefore making the @{emph \<open>cumulative offer processes\<close>} (COPs,
\S\ref{sec:contracts-cop}) applicable to more matching problems. In
doing so they lose the lattice structure of the stable matches, which
necessitates redeveloping the results of \S\ref{sec:contracts}.

In contrast to the COP of \S\ref{sec:contracts-cop},
\citet{HatfieldKojima:2010} develop and analyze a @{emph
\<open>single-offer\<close>} variant, where only one doctor (who has
no held contract) proposes per round. The order of doctors making
offers is not specified. We persist with the simultaneous-offer COP as
it is deterministic. See \citet{HirataKasuya:2014} for equivalence
arguments.

We begin with some observations due to
\citeauthor{AygunSonmez:2012-WP}. Firstly, as for the
matching-with-contracts setting of \S\ref{sec:contracts},
\citet{AygunSonmez:2012-WP} demonstrate that these results depend on
hospital preferences satisfying @{const "irc"}. We do not formalize
their examples. Secondly, an alternative to hospitals having choice
functions (as we have up to now) is for the hospitals to have
preference orders over sets, which is suggested by both
\citet{HatfieldMilgrom:2005} (weakly) and \citet{HatfieldKojima:2010}.
\citet[\S2]{AygunSonmez:2012-WP} argue that this approach is
under-specified and propose to define \<open>Ch\<close> as choosing
amongst maximal elements of some non-strict preference order (i.e.,
including indifference). They then claim that this is equivalent to
taking \<open>Ch\<close> as primitive, and so we continue down that
path.

\<close>


subsection\<open> Theorem~1: the COP yields a stable match under @{emph \<open>bilateral substitutes\<close>} \<close>

text\<open>

The weakest replacement condition suggested by
\citet[\S1]{HatfieldKojima:2010} for the @{const "substitutes"}
condition on hospital choice functions is termed @{emph \<open>bilateral
substitutes\<close>}:
\begin{quote}

Contracts are @{emph \<open>bilateral substitutes\<close>} for a hospital if there are
no two contracts \<open>x\<close> and \<open>z\<close> and a set of
contracts \<open>Y\<close> with other doctors than those associated
with \<open>x\<close> and \<open>z\<close> such that the hospital that
regards \<open>Y\<close> as available wants to sign \<open>z\<close>
if and only if \<open>x\<close> becomes available. In other words,
contracts are bilateral substitutes when any hospital, presented with
an offer from a doctor he does not currently employ, never wishes to
also hire another doctor he does not currently employ at a contract he
previously rejected.

\end{quote}

Note that this constraint is specific to this matching-with-contracts
setting, unlike those of \S\ref{sec:cf}.

\<close>

context Contracts
begin

definition bilateral_substitutes_on :: "'x set \<Rightarrow> 'x cfun \<Rightarrow> bool" where
  "bilateral_substitutes_on A f
     \<longleftrightarrow> \<not>(\<exists>B\<subseteq>A. \<exists>a b. {a, b} \<subseteq> A \<and> Xd a \<notin> Xd ` B \<and> Xd b \<notin> Xd ` B
                     \<and> b \<notin> f (B \<union> {b}) \<and> b \<in> f (B \<union> {a, b}))"

abbreviation bilateral_substitutes :: "'x cfun \<Rightarrow> bool" where
  "bilateral_substitutes \<equiv> bilateral_substitutes_on UNIV"

lemma bilateral_substitutes_on_def2:
  "bilateral_substitutes_on A f
     \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>a\<in>A. \<forall>b\<in>A. Xd a \<notin> Xd ` B \<and> Xd b \<notin> Xd ` B \<and> b \<notin> f (B \<union> {b}) \<longrightarrow> b \<notin> f (B \<union> {a, b}))"
(*<*)
(is "?lhs \<longleftrightarrow> ?rhs")
proof %invisible (rule iffI, clarsimp)
  fix B a b
  assume lhs: ?lhs and XXX: "B \<subseteq> A" "a \<in> A" "b \<in> A" "Xd a \<notin> Xd ` B" "Xd b \<notin> Xd ` B" "b \<notin> f (insert b B)" "b \<in> f (insert a (insert b B))"
  show False
  proof(cases "a \<in> B")
    case True with XXX show ?thesis by (simp add: insert_absorb)
  next
    case False with lhs XXX show ?thesis
      unfolding bilateral_substitutes_on_def
      by (cases "b \<in> B") (auto simp: insert_commute insert_absorb)
  qed
qed (fastforce simp: bilateral_substitutes_on_def)

lemmas bilateral_substitutes_onI = iffD2[OF bilateral_substitutes_on_def2, rule_format]
lemmas bilateral_substitutes_onD = iffD1[OF bilateral_substitutes_on_def2, rule_format, simplified, unfolded conj_imp_eq_imp_imp]

lemmas bilateral_substitutes_def = bilateral_substitutes_on_def2[where A=UNIV, simplified]
lemmas bilateral_substitutesI = iffD2[OF bilateral_substitutes_def, rule_format]
lemmas bilateral_substitutesD = iffD1[OF bilateral_substitutes_def, rule_format, simplified, unfolded conj_imp_eq_imp_imp]

(*>*)
text\<open>\<close>

lemma substitutes_on_bilateral_substitutes_on:
  assumes "substitutes_on A f"
  shows "bilateral_substitutes_on A f"
using %invisible assms by (auto intro!: bilateral_substitutes_onI dest: substitutes_onD[rotated -1])

text\<open>

\citet[\S4, Definition~5]{AygunSonmez:2012-WP} give the following
equivalent definition:

\<close>

lemma bilateral_substitutes_on_def3:
  "bilateral_substitutes_on A f
     \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>a\<in>A. \<forall>b\<in>A. b \<notin> f (B \<union> {b}) \<and> b \<in> f (B \<union> {a, b}) \<longrightarrow> Xd a \<in> Xd ` B \<or> Xd b \<in> Xd ` B)"
unfolding %invisible bilateral_substitutes_on_def2 by blast

end

text\<open>

As before, we define a series of locales that capture the relevant
hypotheses about hospital choice functions.

\<close>

locale ContractsWithBilateralSubstitutes = Contracts +
  assumes Ch_bilateral_substitutes: "\<forall>h. bilateral_substitutes (Ch h)"

sublocale ContractsWithSubstitutes < ContractsWithBilateralSubstitutes
using %invisible Ch_substitutes by unfold_locales (blast intro: substitutes_on_bilateral_substitutes_on)

locale ContractsWithBilateralSubstitutesAndIRC =
  ContractsWithBilateralSubstitutes + ContractsWithIRC

sublocale ContractsWithSubstitutesAndIRC < ContractsWithBilateralSubstitutesAndIRC
by %invisible unfold_locales

context ContractsWithBilateralSubstitutesAndIRC
begin

text\<open>

The key difficulty in showing the stability of the result of the COP
under this condition \citep[Theorem~1]{HatfieldKojima:2010} is in
proving that it ensures we get an @{const "allocation"}; the remainder
of the proof of \S\ref{sec:contracts-cop} (for a single hospital,
where this property is trivial) goes through unchanged. We avail
ourselves of \citet[Lemma]{HirataKasuya:2014}, which they say is a
restatement of the proof of
\citet[Theorem~1]{HatfieldKojima:2010}. See also
\citet[Appendix~A]{AygunSonmez:2012-WP}.

\<close>

lemma bilateral_substitutes_lemma:
  assumes "Xd x \<notin> Xd ` Ch h X"
  assumes "d \<notin> Xd ` Ch h X"
  assumes "d \<noteq> Xd x"
  shows "d \<notin> Xd ` Ch h (insert x X)"
proof(rule notI)
  assume "d \<in> Xd ` Ch h (insert x X)"
  then obtain x' where x': "x' \<in> Ch h (insert x X)" "Xd x' = d" by blast
  with Ch_irc \<open>d \<notin> Xd ` Ch h X\<close>
  have "x \<in> Ch h (insert x X)" unfolding irc_def by blast
  let ?X' = "{y \<in> X. Xd y \<notin> {Xd x, d}}"
  from Ch_range \<open>Xd x \<notin> Xd ` Ch h X\<close> \<open>d \<notin> Xd ` Ch h X\<close> \<open>d \<noteq> Xd x\<close> x'
  have "Ch h (insert x' ?X') = Ch h X"
    using consistencyD[OF Ch_consistency[where h=h], where B="X" and C="insert x' ?X'"]
    by (fastforce iff: image_iff) (* slow *)
  moreover from Ch_range Ch_singular \<open>d \<notin> Xd ` Ch h X\<close> x' \<open>x \<in> Ch h (insert x X)\<close>
  have "Ch h (insert x (insert x' ?X')) = Ch h (insert x X)"
    using consistencyD[OF Ch_consistency[where h=h], where B="insert x X" and C="insert x (insert x' ?X')"]
    by (clarsimp simp: insert_commute) (blast dest: inj_onD)
  moreover note \<open>d \<notin> Xd ` Ch h X\<close> x'
  ultimately show False
    using bilateral_substitutesD[OF spec[OF Ch_bilateral_substitutes, of h], where a=x and b=x' and B="?X'"] by fastforce
qed

text \<open>

Our proof essentially adds the inductive details these earlier efforts
skipped over. It is somewhat complicated by our use of the
simultaneous-offer COP.

\<close>

lemma bilateral_substitutes_lemma_union:
  assumes "Xd ` Ch h X \<inter> Xd ` Y = {}"
  assumes "d \<notin> Xd ` Ch h X"
  assumes "d \<notin> Xd ` Y"
  assumes "allocation Y"
  shows "d \<notin> Xd ` Ch h (X \<union> Y)"
using %invisible finite[of Y] assms by (induct arbitrary: d) (simp_all add: bilateral_substitutes_lemma)

lemma cop_F_CH_CD_on_disjoint:
  assumes "cop_F_closed_inv ds fp"
  assumes "cop_F_range_inv ds fp"
  shows "Xd ` CH fp \<inter> Xd ` (CD_on ds (- RH fp) - fp) = {}"
using %invisible assms CH_range unfolding cop_F_range_inv_def cop_F_closed_inv_def above_def
by (fastforce simp: set_eq_iff mem_CD_on_Cd Cd_greatest greatest_def)

text\<open>

Our key lemma shows that we effectively have @{const "substitutes"}
for rejected contracts, provided the relevant doctor does not have a
contract held with the relevant hospital. Note the similarity to
Theorem~4 (\S\ref{sec:cop-theorem-4}).

\<close>

lemma cop_F_RH_mono:
  assumes "cop_F_closed_inv ds fp"
  assumes "cop_F_range_inv ds fp"
  assumes "Xd x \<notin> Xd ` Ch (Xh x) fp"
  assumes "x \<in> RH fp"
  shows "x \<in> RH (cop_F ds fp)"
proof(safe)
  from \<open>x \<in> RH fp\<close> show "x \<in> cop_F ds fp" using cop_F_increasing by blast
next
  assume "x \<in> CH (cop_F ds fp)"
  from Ch_singular \<open>x \<in> CH (cop_F ds fp)\<close> \<open>x \<in> RH fp\<close>
  have "Ch (Xh x) (cop_F ds fp) = Ch (Xh x) (fp \<union> (CD_on ds (-RH fp) - fp - {z. Xd z = Xd x}))"
    unfolding cop_F_def
    by - (rule consistencyD[OF Ch_consistency], auto simp: mem_CH_Ch dest: Ch_range' inj_onD)
  with cop_F_CH_CD_on_disjoint[OF \<open>cop_F_closed_inv ds fp\<close> \<open>cop_F_range_inv ds fp\<close>]
  have "Xd x \<notin> Xd ` Ch (Xh x) (cop_F ds fp)"
    by simp (rule bilateral_substitutes_lemma_union[OF _ \<open>Xd x \<notin> Xd ` Ch (Xh x) fp\<close>],
             auto simp: CH_def CD_on_inj_on_Xd inj_on_diff)
  with \<open>x \<in> CH (cop_F ds fp)\<close> show False by (simp add: mem_CH_Ch)
qed

lemma cop_F_allocation_inv:
  "valid ds (\<lambda>ds fp. cop_F_range_inv ds fp \<and> cop_F_closed_inv ds fp) (\<lambda>ds fp. allocation (CH fp))"
proof(induct rule: validI)
  case base show ?case by (simp add: CH_simps)
next
  case (step fp)
  then have "allocation (CH fp)"
        and "cop_F_closed_inv ds fp"
        and "cop_F_range_inv ds fp" by blast+
  note cop_F_CH_CD_on_disjoint = cop_F_CH_CD_on_disjoint[OF \<open>cop_F_closed_inv ds fp\<close> \<open>cop_F_range_inv ds fp\<close>]
  note cop_F_RH_mono = cop_F_RH_mono[OF \<open>cop_F_closed_inv ds fp\<close> \<open>cop_F_range_inv ds fp\<close>]
  show ?case
  proof(rule inj_onI)
    fix x y
    assume "x \<in> CH (cop_F ds fp)" and "y \<in> CH (cop_F ds fp)" and "Xd x = Xd y"
    show "x = y"
    proof(cases "Xh y = Xh x")
      case True with Ch_singular \<open>x \<in> CH (cop_F ds fp)\<close> \<open>y \<in> CH (cop_F ds fp)\<close> \<open>Xd x = Xd y\<close>
      show ?thesis by (fastforce simp: mem_CH_Ch dest: inj_onD)
    next
      case False note \<open>Xh y \<noteq> Xh x\<close>
      from \<open>x \<in> CH (cop_F ds fp)\<close> show ?thesis
      proof(cases x rule: CH_cop_F_cases)
        case CH note \<open>x \<in> CH fp\<close>
        from \<open>y \<in> CH (cop_F ds fp)\<close> show ?thesis
        proof(cases y rule: CH_cop_F_cases)
          case CH note \<open>y \<in> CH fp\<close>
          with \<open>allocation (CH fp)\<close> \<open>Xd x = Xd y\<close> \<open>x \<in> CH fp\<close>
          show ?thesis by (blast dest: inj_onD)
        next
          case RH_fp note \<open>y \<in> RH fp\<close>
          from \<open>allocation (CH fp)\<close> \<open>Xd x = Xd y\<close> \<open>Xh y \<noteq> Xh x\<close> \<open>x \<in> CH fp\<close> have "Xd y \<notin> Xd ` Ch (Xh y) fp"
            by clarsimp (metis Ch_CH_irc_idem Ch_range' inj_on_contraD)
          with \<open>y \<in> CH (cop_F ds fp)\<close> \<open>y \<in> RH fp\<close> cop_F_RH_mono show ?thesis by blast
        next
          case CD_on note y' = \<open>y \<in> CD_on ds (- RH fp) - fp\<close>
          with cop_F_CH_CD_on_disjoint \<open>Xd x = Xd y\<close> \<open>x \<in> CH fp\<close> show ?thesis by blast
        qed
      next
        case RH_fp note \<open>x \<in> RH fp\<close>
        from \<open>y \<in> CH (cop_F ds fp)\<close> show ?thesis
        proof(cases y rule: CH_cop_F_cases)
          case CH note \<open>y \<in> CH fp\<close>
          from \<open>allocation (CH fp)\<close> \<open>Xd x = Xd y\<close> \<open>Xh y \<noteq> Xh x\<close> \<open>y \<in> CH fp\<close> have "Xd x \<notin> Xd ` Ch (Xh x) fp"
            by clarsimp (metis Ch_CH_irc_idem Ch_range' inj_on_contraD)
          with \<open>x \<in> CH (cop_F ds fp)\<close> \<open>x \<in> RH fp\<close> cop_F_RH_mono show ?thesis by blast
        next
          case RH_fp note \<open>y \<in> RH fp\<close>
          show ?thesis
          proof(cases "Xd x \<in> Xd ` Ch (Xh x) fp")
            case True
            with \<open>allocation (CH fp)\<close> \<open>Xd x = Xd y\<close> \<open>Xh y \<noteq> Xh x\<close> have "Xd y \<notin> Xd ` Ch (Xh y) fp"
              by clarsimp (metis Ch_range' inj_onD mem_CH_Ch)
            with \<open>y \<in> CH (cop_F ds fp)\<close> \<open>y \<in> RH fp\<close> cop_F_RH_mono show ?thesis by blast
          next
            case False note \<open>Xd x \<notin> Xd ` Ch (Xh x) fp\<close>
            with \<open>x \<in> CH (cop_F ds fp)\<close> \<open>x \<in> RH fp\<close> cop_F_RH_mono show ?thesis by blast
          qed
        next
          case CD_on note \<open>y \<in> CD_on ds (- RH fp) - fp\<close>
          from cop_F_CH_CD_on_disjoint \<open>Xd x = Xd y\<close> \<open>y \<in> CD_on ds (- RH fp) - fp\<close>
          have "Xd x \<notin> Xd ` Ch (Xh x) fp" by (auto simp: CH_def dest: Ch_range')
          with \<open>x \<in> CH (cop_F ds fp)\<close> \<open>x \<in> RH fp\<close> cop_F_RH_mono show ?thesis by blast
        qed
      next
        case CD_on note \<open>x \<in> CD_on ds (- RH fp) - fp\<close>
        from \<open>y \<in> CH (cop_F ds fp)\<close> show ?thesis
        proof(cases y rule: CH_cop_F_cases)
          case CH note \<open>y \<in> CH fp\<close>
          with cop_F_CH_CD_on_disjoint \<open>Xd x = Xd y\<close> \<open>x \<in> CD_on ds (- RH fp) - fp\<close> show ?thesis by blast
        next
          case RH_fp note \<open>y \<in> RH fp\<close>
          from cop_F_CH_CD_on_disjoint \<open>Xd x = Xd y\<close> \<open>x \<in> CD_on ds (- RH fp) - fp\<close>
          have "Xd y \<notin> Xd ` Ch (Xh y) fp" unfolding CH_def by clarsimp (blast dest: Ch_range')
          with \<open>y \<in> CH (cop_F ds fp)\<close> \<open>y \<in> RH fp\<close> cop_F_RH_mono show ?thesis by blast
        next
          case CD_on note \<open>y \<in> CD_on ds (- RH fp) - fp\<close>
          with \<open>Xd x = Xd y\<close> \<open>x \<in> CD_on ds (- RH fp) - fp\<close> show ?thesis
            by (meson CD_on_inj_on_Xd DiffD1 inj_on_eq_iff)
        qed
      qed
    qed
  qed
qed

lemma fp_cop_F_allocation:
  shows "allocation (cop ds)"
proof %invisible -
  have "invariant ds (\<lambda>ds fp. cop_F_range_inv ds fp \<and> cop_F_closed_inv ds fp \<and> allocation (CH fp))"
    using cop_F_range_inv cop_F_closed_inv cop_F_allocation_inv
    by - (rule valid_conj | blast | rule valid_pre)+
  then show ?thesis by (blast dest: invariantD)
qed

theorem Theorem_1:
  shows "stable_on ds (cop ds)"
proof %invisible (rule stable_onI)
  show "individually_rational_on ds (cop ds)"
  proof(rule individually_rational_onI)
    from fp_cop_F_allocation show "CD_on ds (cop ds) = cop ds"
      by (rule CD_on_closed) (blast dest: fp_cop_F_range_inv' CH_range')
    show "CH (cop ds) = cop ds" by (simp add: CH_irc_idem)
  qed
  show "stable_no_blocking_on ds (cop ds)" by (rule cop_stable_no_blocking_on)
qed

end

text (in ContractsWithBilateralSubstitutesAndIRC) \<open>

\citet[\S3.1]{HatfieldKojima:2010} provide an example that shows that
the traditional optimality and strategic results do not hold under
@{const "bilateral_substitutes"}, which motivates looking for a
stronger condition that remains weaker than @{const "substitutes"}.

Their example involves two doctors, two hospitals, and five contracts.

\<close>

datatype X5 = Xd1 | Xd1' | Xd2 | Xd2' | Xd2''

primrec X5d :: "X5 \<Rightarrow> D2" where
  "X5d Xd1 = D1"
| "X5d Xd1' = D1"
| "X5d Xd2 = D2"
| "X5d Xd2' = D2"
| "X5d Xd2'' = D2"

primrec X5h :: "X5 \<Rightarrow> H2" where
  "X5h Xd1 = H1"
| "X5h Xd1' = H1"
| "X5h Xd2 = H1"
| "X5h Xd2' = H2"
| "X5h Xd2'' = H1"

primrec PX5d :: "D2 \<Rightarrow> X5 rel" where
  "PX5d D1 = linord_of_list [Xd1, Xd1']"
| "PX5d D2 = linord_of_list [Xd2, Xd2', Xd2'']"

primrec CX5h :: "H2 \<Rightarrow> X5 cfun" where
  "CX5h H1 A =
     (if {Xd1', Xd2} \<subseteq> A then {Xd1', Xd2} else
      if {Xd2''} \<subseteq> A then {Xd2''} else
      if {Xd1} \<subseteq> A then {Xd1} else
      if {Xd1'} \<subseteq> A then {Xd1'} else
      if {Xd2} \<subseteq> A then {Xd2} else {})"
| "CX5h H2 A = { x . x \<in> A \<and> x = Xd2' }"

(*<*)

lemma X5_UNIV:
  shows "UNIV = set [Xd1, Xd1', Xd2, Xd2', Xd2'']"
using X5.exhaust by auto

lemmas X5_pow = subset_subseqs[OF subset_trans[OF subset_UNIV Set.equalityD1[OF X5_UNIV]]]

instance X5 :: finite
by standard (simp add: X5_UNIV)

lemma X5_ALL:
  shows "(\<forall>X''. P X'') \<longleftrightarrow> (\<forall>X''\<in>set ` set (subseqs [Xd1, Xd1', Xd2, Xd2', Xd2'']). P X'')"
using X5_pow by blast

lemma PX5d_linear:
  shows "Linear_order (PX5d d)"
by (cases d) (simp_all add: linord_of_list_Linear_order)

lemma PX5d_range:
  shows "Field (PX5d d) \<subseteq> {x. X5d x = d}"
by (cases d) simp_all

lemma CX5h_range:
  shows "CX5h h X \<subseteq> {x \<in> X. X5h x = h}"
by (cases h) auto

lemma CX5h_singular:
  shows "inj_on X5d (CX5h h X)"
by (cases h) (auto intro: inj_onI)

(*>*)
text\<open>\<close>

interpretation BSI: Contracts X5d X5h PX5d CX5h
using %invisible PX5d_linear PX5d_range CX5h_range CX5h_singular by unfold_locales blast+

lemma CX5h_bilateral_substitutes:
  shows "BSI.bilateral_substitutes (CX5h h)"
unfolding BSI.bilateral_substitutes_def by (cases h) (auto simp: X5_ALL)

lemma CX5h_irc:
  shows "irc (CX5h h)"
unfolding irc_def by (cases h) (auto simp: X5_ALL)

interpretation BSI: ContractsWithBilateralSubstitutesAndIRC X5d X5h PX5d CX5h
using %invisible CX5h_bilateral_substitutes CX5h_irc by unfold_locales blast+

text\<open>

There are two stable matches in this model.

\<close>
(*<*)

lemma Xd1_Xd2'_stable:
  shows "BSI.stable {Xd1, Xd2'}"
proof(rule BSI.stable_onI)
  note image_cong_simp [cong del] note INF_cong_simp [cong] note SUP_cong_simp [cong]
  show "BSI.individually_rational {Xd1, Xd2'}"
    unfolding BSI.individually_rational_on_def BSI.CD_on_def BSI.CH_def
    by (auto simp: insert_commute D2_UNION H2_UNION)
  show "BSI.stable_no_blocking {Xd1, Xd2'}"
    unfolding BSI.stable_no_blocking_on_def
    by (auto simp: X5_ALL BSI.blocking_on_def BSI.mem_CD_on_Cd BSI.maxR_def linord_of_list_linord_of_listP)
qed

lemma Xd1'_Xd2_stable:
  shows "BSI.stable {Xd1', Xd2}"
proof(rule BSI.stable_onI)
  note image_cong_simp [cong del] note INF_cong_simp [cong] note SUP_cong_simp [cong]
  show "BSI.individually_rational {Xd1', Xd2}"
    unfolding BSI.individually_rational_on_def BSI.CD_on_def BSI.CH_def
    by (auto simp: insert_commute D2_UNION H2_UNION)
  show "BSI.stable_no_blocking {Xd1', Xd2}"
    unfolding BSI.stable_no_blocking_on_def
    by (auto simp: X5_ALL BSI.blocking_on_def BSI.mem_CD_on_Cd BSI.maxR_def linord_of_list_linord_of_listP)
qed

(*>*)
text\<open>\<close>

lemma BSI_stable:
  shows "BSI.stable X \<longleftrightarrow> X = {Xd1, Xd2'} \<or> X = {Xd1', Xd2}"
(*<*)
(is "?lhs = ?rhs")
proof(rule iffI)
  assume ?lhs then show ?rhs
    using X5_pow[where X=X] BSI.stable_on_allocation[OF \<open>?lhs\<close>]
    apply clarsimp
    apply (elim disjE; simp add: insert_eq_iff)
    apply (simp_all only: BSI.stable_on_def BSI.individually_rational_on_def BSI.stable_no_blocking_on_def BSI.blocking_on_def BSI.CH_def)
    apply (auto 0 1 simp: D2_UNION H2_UNION X5_ALL BSI.mem_CD_on_Cd BSI.maxR_def linord_of_list_linord_of_listP)
    done
next
  assume ?rhs then show ?lhs
    using Xd1'_Xd2_stable Xd1_Xd2'_stable by blast
qed

(*>*)
text (in Contracts) \<open>

Therefore there is no doctor-optimal match under these preferences:

\<close>

lemma
  "\<not>(\<exists> (Y::X5 set). BSI.doctor_optimal_match UNIV Y)"
unfolding BSI.doctor_optimal_match_def BSI_stable
apply clarsimp
apply (cut_tac X=Y in X5_pow)
apply clarsimp
apply (elim disjE; simp add: insert_eq_iff; simp add: X5_ALL linord_of_list_linord_of_listP)
done


subsection\<open> Theorem~3: @{emph \<open>pareto separability\<close>} relates @{emph \<open>unilateral substitutes\<close>} and @{emph \<open>substitutes\<close>} \<close>

text\<open>

\citet[\S4]{HatfieldKojima:2010} proceed to define @{emph \<open>unilateral
substitutes\<close>}:
\begin{quote}

[P]references satisfy @{emph \<open>unilateral substitutes\<close>} if whenever a
hospital rejects the contract @{term "z"} when that is the only
contract with @{term "Xd z"} available, it still rejects the contract
@{term "z"} when the choice set expands.

\end{quote}

\<close>

context Contracts
begin

definition unilateral_substitutes_on :: "'x set \<Rightarrow> 'x cfun \<Rightarrow> bool" where
  "unilateral_substitutes_on A f
     \<longleftrightarrow> \<not>(\<exists>B\<subseteq>A. \<exists>a b. {a, b} \<subseteq> A \<and> Xd b \<notin> Xd ` B \<and> b \<notin> f (B \<union> {b}) \<and> b \<in> f (B \<union> {a, b}))"

abbreviation unilateral_substitutes :: "'x cfun \<Rightarrow> bool" where
  "unilateral_substitutes \<equiv> unilateral_substitutes_on UNIV"

lemma unilateral_substitutes_on_def2:
  "unilateral_substitutes_on A f
     \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>a\<in>A. \<forall>b\<in>A. Xd b \<notin> Xd ` B \<and> b \<notin> f (B \<union> {b}) \<longrightarrow> b \<notin> f (B \<union> {a, b}))"
(*<*)
(is "?lhs \<longleftrightarrow> ?rhs")
proof %invisible (rule iffI, clarsimp)
  fix B a b
  assume lhs: ?lhs and XXX: "B \<subseteq> A" "a \<in> A" "b \<in> A" "Xd b \<notin> Xd ` B" "b \<notin> f (insert b B)" "b \<in> f (insert a (insert b B))"
  show False
  proof(cases "a \<in> B")
    case True with XXX show ?thesis by (simp add: insert_absorb)
  next
    case False with lhs XXX show ?thesis
      unfolding unilateral_substitutes_on_def
      by (cases "b \<in> B") (auto simp: insert_commute insert_absorb)
  qed
qed (fastforce simp: unilateral_substitutes_on_def)

lemmas %invisible unilateral_substitutes_onI = iffD2[OF unilateral_substitutes_on_def2, rule_format, simplified, unfolded conj_imp_eq_imp_imp]
lemmas %invisible unilateral_substitutes_onD = iffD1[OF unilateral_substitutes_on_def2, rule_format, simplified, unfolded conj_imp_eq_imp_imp]

lemmas %invisible unilateral_substitutes_def = unilateral_substitutes_on_def2[where A=UNIV, simplified]
lemmas %invisible unilateral_substitutesI = iffD2[OF unilateral_substitutes_def, rule_format, simplified, unfolded conj_imp_eq_imp_imp]
lemmas %invisible unilateral_substitutesD = iffD1[OF unilateral_substitutes_def, rule_format, simplified, unfolded conj_imp_eq_imp_imp]

(*>*)
text\<open>

\citet[\S4, Definition~6]{AygunSonmez:2012-WP} give the following equivalent definition:

\<close>

lemma unilateral_substitutes_on_def3:
  "unilateral_substitutes_on A f
     \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>a\<in>A. \<forall>b\<in>A. b \<notin> f (B \<union> {b}) \<and> b \<in> f (B \<union> {a, b}) \<longrightarrow> Xd b \<in> Xd ` B)"
(*<*)
unfolding %invisible unilateral_substitutes_on_def2 by blast

lemmas %invisible unilateral_substitutes_def3 = unilateral_substitutes_on_def3[where A=UNIV, simplified]
lemmas %invisible unilateral_substitutesD3 = iffD1[OF unilateral_substitutes_def3, rule_format, simplified, unfolded conj_imp_eq_imp_imp]

(*>*)
text\<open>\<close>

lemma substitutes_on_unilateral_substitutes_on:
  assumes "substitutes_on A f"
  shows "unilateral_substitutes_on A f"
using %invisible assms by (auto intro!: unilateral_substitutes_onI dest: substitutes_onD)

lemma unilateral_substitutes_on_bilateral_substitutes_on:
  assumes "unilateral_substitutes_on A f"
  shows "bilateral_substitutes_on A f"
using %invisible assms by (auto intro!: bilateral_substitutes_onI dest: unilateral_substitutes_onD[rotated -1])

text\<open>

The following defines locales for the @{const
"unilateral_substitutes"} hypothesis, and inserts these between those
for @{const "substitutes"} and @{const "bilateral_substitutes"}.

\<close>

end

locale ContractsWithUnilateralSubstitutes = Contracts +
  assumes Ch_unilateral_substitutes: "\<forall>h. unilateral_substitutes (Ch h)"

sublocale ContractsWithUnilateralSubstitutes < ContractsWithBilateralSubstitutes
using %invisible Ch_unilateral_substitutes by unfold_locales (blast intro: unilateral_substitutes_on_bilateral_substitutes_on)

sublocale ContractsWithSubstitutes < ContractsWithUnilateralSubstitutes
using %invisible Ch_substitutes by unfold_locales (blast intro: substitutes_on_unilateral_substitutes_on)

locale ContractsWithUnilateralSubstitutesAndIRC =
  ContractsWithUnilateralSubstitutes + ContractsWithIRC

sublocale ContractsWithUnilateralSubstitutesAndIRC < ContractsWithBilateralSubstitutesAndIRC
by %invisible unfold_locales

sublocale ContractsWithSubstitutesAndIRC < ContractsWithUnilateralSubstitutesAndIRC
by %invisible unfold_locales

text (in Contracts) \<open>

\citet[Theorem~3]{HatfieldKojima:2010} relate @{const
"unilateral_substitutes"} to @{const "substitutes"} using @{emph
\<open>Pareto separability\<close>}:
\begin{quote}

Preferences are @{emph \<open>Pareto separable\<close>} for a hospital if the
hospital's choice between \<open>x\<close> and \<open>x'\<close>, two
[distinct] contracts with the same doctor, does not depend on what
other contracts the hospital has access to.

\end{quote}
This result also depends on @{const "irc"}.

\<close>

context Contracts
begin

definition pareto_separable_on :: "'x set \<Rightarrow> bool" where
  "pareto_separable_on A
     \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>C\<subseteq>A. \<forall>a b. {a, b} \<subseteq> A \<and> a \<noteq> b \<and> Xd a = Xd b \<and> Xh a = Xh b
                     \<and> a \<in> Ch (Xh b) (B \<union> {a, b}) \<longrightarrow> b \<notin> Ch (Xh b) (C \<union> {a, b}))"

abbreviation pareto_separable :: "bool" where
  "pareto_separable \<equiv> pareto_separable_on UNIV"

lemmas %invisible pareto_separable_def = pareto_separable_on_def[where A=UNIV, simplified]

lemmas %invisible pareto_separable_onI = iffD2[OF pareto_separable_on_def, rule_format, simplified, unfolded conj_imp_eq_imp_imp]
lemmas %invisible pareto_separable_onD = iffD1[OF pareto_separable_on_def, rule_format, simplified, unfolded conj_imp_eq_imp_imp]

lemma substitutes_on_pareto_separable_on:
  assumes "\<forall>h. substitutes_on A (Ch h)"
  shows "pareto_separable_on A"
proof(rule pareto_separable_onI)
  fix B C a b
  assume XXX: "B \<subseteq> A" "C \<subseteq> A" "a \<in> A" "b \<in> A" "a \<noteq> b" "Xd a = Xd b" "Xh a = Xh b" "a \<in> Ch (Xh b) (insert a (insert b B))"
  note Ch_iiaD = iia_onD[OF iffD1[OF substitutes_iia spec[OF \<open>\<forall>h. substitutes_on A (Ch h)\<close>]], rotated -1, simplified]
  from XXX have "a \<in> Ch (Xh b) {a, b}" by (fast elim: Ch_iiaD)
  with XXX have "b \<notin> Ch (Xh b) {a, b}" by (meson Ch_singular inj_on_eq_iff)
  with XXX have "b \<notin> Ch (Xh b) (C \<union> {a, b})" by (blast dest: Ch_iiaD)
  with XXX show "b \<notin> Ch (Xh b) (insert a (insert b C))" by simp
qed

lemma unilateral_substitutes_on_pareto_separable_on_substitutes_on:
  assumes "\<forall>h. unilateral_substitutes_on A (Ch h)"
  assumes "\<forall>h. irc_on A (Ch h)"
  assumes "pareto_separable_on A"
  shows "substitutes_on A (Ch h)"
proof(rule substitutes_onI)
  fix B a b
  assume XXX: "B \<subseteq> A" "a \<in> A" "b \<in> A" "b \<notin> Ch h (insert b B)"
  show "b \<notin> Ch h (insert a (insert b B))"
  proof(cases "Xd b \<in> Xd ` B")
    case True show ?thesis
    proof(cases "Xd b \<in> Xd ` Ch h (insert b B)")
      case True
      then obtain x where "x \<in> Ch h (insert b B)" "Xd x = Xd b" by force
      moreover with XXX have "x \<in> B" "x \<noteq> b" using Ch_range by blast+
      moreover note \<open>pareto_separable_on A\<close> XXX
      ultimately show ?thesis
        using pareto_separable_onD[where A=A and B="B - {x}" and a=x and b=b and C="insert a (B - {x})"] Ch_range
        by (cases "Xh b = h") (auto simp: insert_commute insert_absorb)
    next
      case False
      let ?B' = "{x \<in> B . Xd x \<noteq> Xd b}"
      from False have "b \<notin> Ch h (insert b B)" by blast
      with \<open>\<forall>h. irc_on A (Ch h)\<close> XXX False have "b \<notin> Ch h (insert b ?B')"
        using consistency_onD[OF irc_on_consistency_on[where f="Ch h"], where B="insert b B" and C="insert b ?B'"] Ch_range
        by (fastforce iff: image_iff)
      with \<open>\<forall>h. unilateral_substitutes_on A (Ch h)\<close> XXX False have "b \<notin> Ch h (insert a (insert b ?B'))"
        using unilateral_substitutes_onD[where f="Ch h" and B="?B'"]
        by (fastforce iff: image_iff)
      with \<open>\<forall>h. irc_on A (Ch h)\<close> XXX False show ?thesis
        using consistency_onD[OF irc_on_consistency_on[where f="Ch h"],
                              where A=A and B="insert a (insert b B)" and C="insert a (insert b ?B')"]
              Ch_range'[of _ h "insert a (insert b B)"] Ch_singular
        by simp (blast dest: inj_on_contraD)
    qed
  next
    case False
    with \<open>\<forall>h. unilateral_substitutes_on A (Ch h)\<close> XXX show ?thesis by (blast dest: unilateral_substitutes_onD)
  qed
qed

theorem Theorem_3:
  assumes "\<forall>h. irc_on A (Ch h)"
  shows "(\<forall>h. substitutes_on A (Ch h)) \<longleftrightarrow> (\<forall>h. unilateral_substitutes_on A (Ch h) \<and> pareto_separable_on A)"
using %invisible assms
      unilateral_substitutes_on_pareto_separable_on_substitutes_on substitutes_on_pareto_separable_on
      substitutes_on_unilateral_substitutes_on
by blast

end


subsubsection\<open> \citet{AfacanTurhan:2015}: @{emph \<open>doctor separability\<close>} relates bi- and unilateral substitutes \<close>

context Contracts
begin

text \<open>

\citet[Theorem~1]{AfacanTurhan:2015} relate @{const
"bilateral_substitutes"} and @{const "unilateral_substitutes"} using
@{emph \<open>doctor separability\<close>}:
\begin{quote}

@{emph \<open>[Doctor separability (DS)]\<close>} says that if a doctor is not chosen
from a set of contracts in the sense that no contract of him is
selected, then that doctor should still not be chosen unless a
contract of a new doctor (that is, doctor having no contract in the
given set of contracts) becomes available. For practical purposes, we
can consider DS as capturing contracts where certain groups of doctors
are substitutes. [footnote: If \<open>Xd x \<notin> Xd ` Ch h (Y
\<union> {x, z})\<close>, then doctor \<open>Xd x\<close> is not
chosen. And under DS, he continues not to be chosen unless a new
doctor comes. Hence, we can interpret it as the doctors in the given
set of contracts are substitutes.]

\end{quote}

\<close>

definition doctor_separable_on :: "'x set \<Rightarrow> 'x cfun \<Rightarrow> bool" where
  "doctor_separable_on A f
     \<longleftrightarrow> (\<forall>B\<subseteq>A. \<forall>a b c. {a, b, c} \<subseteq> A \<and> Xd a \<noteq> Xd b \<and> Xd b = Xd c \<and> Xd a \<notin> Xd ` f (B \<union> {a, b})
         \<longrightarrow> Xd a \<notin> Xd ` f (B \<union> {a, b, c}))"

abbreviation doctor_separable :: "'x cfun \<Rightarrow> bool" where
  "doctor_separable \<equiv> doctor_separable_on UNIV"

(*<*)

lemmas doctor_separable_def = doctor_separable_on_def[where A=UNIV, simplified]

lemmas doctor_separable_onI = iffD2[OF doctor_separable_on_def, rule_format, simplified, unfolded conj_imp_eq_imp_imp]
lemmas doctor_separable_onD = iffD1[OF doctor_separable_on_def, rule_format, simplified, unfolded conj_imp_eq_imp_imp, rotated -1]

(*>*)

lemma unilateral_substitutes_on_doctor_separable_on:
  assumes "unilateral_substitutes_on A f"
  assumes "irc_on A f"
  assumes "\<forall>B\<subseteq>A. allocation (f B)"
  assumes "f_range_on A f"
  shows "doctor_separable_on A f"
proof(rule doctor_separable_onI)
  fix B a b c
  assume XXX: "B \<subseteq> A" "a \<in> A" "b \<in> A" "c \<in> A" "Xd a \<noteq> Xd b" "Xd b = Xd c" "Xd a \<notin> Xd ` f (insert a (insert b B))"
  have "a \<notin> f (insert a (insert b (insert c B)))"
  proof(rule notI)
    assume a: "a \<in> f (insert a (insert b (insert c B)))"
    let ?C = "{x \<in> B . Xd x \<noteq> Xd a \<or> x = a}"
    from \<open>irc_on A f\<close> \<open>f_range_on A f\<close> XXX(1-3,7)
    have "f (insert a (insert b B)) = f (insert a (insert b ?C))"
      by - (rule consistency_onD[OF irc_on_consistency_on[where A=A and f=f]];
            fastforce dest: f_range_onD[where A=A and f=f and B="insert a (insert b B)"] simp: rev_image_eqI)
    with \<open>unilateral_substitutes_on A f\<close> XXX
    have abcC: "a \<notin> f (insert a (insert b (insert c ?C)))"
      using unilateral_substitutes_onD[where A=A and f=f and a=c and b=a and B="insert b ?C - {a}"]
      by (force simp: insert_commute)
    from \<open>irc_on A f\<close> \<open>\<forall>B\<subseteq>A. allocation (f B)\<close> \<open>f_range_on A f\<close> XXX(1-4) a
    have "f (insert a (insert b (insert c B))) = f (insert a (insert b (insert c ?C)))"
      by - (rule consistency_onD[OF irc_on_consistency_on[where A=A and f=f]], (auto)[4],
            clarsimp, rule conjI, blast dest!: f_range_onD'[where A=A], metis inj_on_contraD insert_subset)
    with a abcC show False by simp
  qed
  moreover
  have "a' \<notin> f (insert a (insert b (insert c B)))" if a': "a' \<in> B" "Xd a' = Xd a" for a'
  proof(rule notI)
    assume a'X: "a' \<in> f (insert a (insert b (insert c B)))"
    let ?B = "insert a B - {a'}"
    from XXX a'
    have XXX_7': "Xd a \<notin> Xd ` f (insert a' (insert b ?B))"
      by clarsimp (metis imageI insert_Diff_single insert_absorb insert_commute)
    let ?C = "{x \<in> ?B . Xd x \<noteq> Xd a \<or> x = a'}"
    from \<open>irc_on A f\<close> \<open>f_range_on A f\<close> XXX(1-3) a' XXX_7'
    have "f (insert a' (insert b ?B)) = f (insert a' (insert b ?C))"
      by - (rule consistency_onD[OF irc_on_consistency_on[where A=A and f=f]];
            fastforce dest: f_range_onD[where A=A and f=f and B="insert a' (insert b ?B)"] simp: rev_image_eqI)
    with \<open>unilateral_substitutes_on A f\<close> XXX(1-6) XXX_7' a'
    have abcC: "a' \<notin> f (insert a' (insert b (insert c ?C)))"
      using unilateral_substitutes_onD[where A=A and f=f and a=c and b=a' and B="insert b ?C - {a'}"]
      by (force simp: insert_commute rev_image_eqI)
    have "f (insert a' (insert b (insert c ?B))) = f (insert a' (insert b (insert c ?C)))"
    proof(rule consistency_onD[OF irc_on_consistency_on[where A=A and f=f]])
      from a' have "insert a' (insert b (insert c ?B)) = insert a (insert b (insert c B))" by blast
      with \<open>\<forall>B\<subseteq>A. allocation (f B)\<close> \<open>f_range_on A f\<close> XXX(1-4) a' a'X
      show "f (insert a' (insert b (insert c ?B))) \<subseteq> insert a' (insert b (insert c {x \<in> ?B. Xd x \<noteq> Xd a \<or> x = a'}))"
        by clarsimp (rule conjI, blast dest!: f_range_onD'[where A=A], metis inj_on_contraD insert_subset)
    qed (use \<open>irc_on A f\<close> XXX(1-4) a' in auto)
    with a' a'X abcC show False by simp (metis insert_Diff insert_Diff_single insert_commute)
  qed
  moreover note \<open>f_range_on A f\<close> XXX
  ultimately show "Xd a \<notin> Xd ` f (insert a (insert b (insert c B)))"
    by (fastforce dest: f_range_onD[where B="insert a (insert b (insert c B))"])
qed

lemma bilateral_substitutes_on_doctor_separable_on_unilateral_substitutes_on:
  assumes "bilateral_substitutes_on A f"
  assumes "doctor_separable_on A f"
  assumes "f_range_on A f"
  shows "unilateral_substitutes_on A f"
proof(rule unilateral_substitutes_onI)
  fix B a b
  assume XXX: "B \<subseteq> A" "a \<in> A" "b \<in> A" "Xd b \<notin> Xd ` B" "b \<notin> f (insert b B)"
  show "b \<notin> f (insert a (insert b B))"
  proof(cases "Xd a \<in> Xd ` B")
    case True
    then obtain C c where Cc: "B = insert c C" "c \<notin> C" "Xd c = Xd a" by (metis Set.set_insert image_iff)
    from \<open>b \<notin> f (insert b B)\<close> Cc have "b \<notin> f (insert b (insert c C))" by simp
    with \<open>f_range_on A f\<close> XXX Cc have "Xd b \<notin> Xd ` f (insert b (insert c C))"
      by clarsimp (metis f_range_onD' image_eqI insertE insert_subset)
    with \<open>doctor_separable_on A f\<close> XXX Cc show ?thesis
      by (auto simp: insert_commute dest: doctor_separable_onD)
  qed (use \<open>bilateral_substitutes_on A f\<close> XXX in \<open>simp add: bilateral_substitutes_onD\<close>)
qed

theorem unilateral_substitutes_on_doctor_separable_on_bilateral_substitutes_on:
  assumes "irc_on A f"
  assumes "\<forall>B\<subseteq>A. allocation (f B)" \<comment> \<open>A rephrasing of @{thm [source] "Ch_singular"}.\<close>
  assumes "f_range_on A f"
  shows "unilateral_substitutes_on A f \<longleftrightarrow> bilateral_substitutes_on A f \<and> doctor_separable_on A f"
using %invisible assms
      unilateral_substitutes_on_bilateral_substitutes_on
      unilateral_substitutes_on_doctor_separable_on
      bilateral_substitutes_on_doctor_separable_on_unilateral_substitutes_on
by metis

text\<open>

\citet[Remark~2]{AfacanTurhan:2015} observe the independence of the
@{const "doctor_separable"}, @{const "pareto_separable"} and @{const
"bilateral_substitutes"} conditions.

\<close>

end


subsection\<open> Theorems~4 and 5: Doctor optimality \<close>

context ContractsWithUnilateralSubstitutesAndIRC
begin

text \<open>

We return to analyzing the COP following
\citet{HatfieldKojima:2010}. The next goal is to establish a
doctor-optimality result for it in the spirit of
\S\ref{sec:contracts-optimality}.

We first show that, with hospital choice functions satisfying @{const
"unilateral_substitutes"}, we effectively have the @{const
"substitutes"} condition for all contracts that have been rejected. In
other words, hospitals never renegotiate with doctors.

The proof is by induction over the finite set @{term "Y"}.

\<close>

lemma
  assumes "Xd x \<notin> Xd ` Ch h X"
  assumes "x \<in> X"
  shows no_renegotiation_union: "x \<notin> Ch h (X \<union> Y)"
    and "x \<notin> Ch h (insert x ((X \<union> Y) - {z. Xd z = Xd x}))"
using %invisible finite[of Y]
proof induct
  case empty
  { case 1 from \<open>Xd x \<notin> Xd ` Ch h X\<close> show ?case by clarsimp }
  { case 2 from assms show ?case
      by - (clarsimp, drule subsetD[OF equalityD2[OF consistencyD[OF Ch_consistency[of h], where B=X]], rotated -1], auto simp: image_iff dest: Ch_range') }
next
  case (insert y Y)
  { case 1 show ?case
    proof(cases "y \<in> Ch h (insert y (X \<union> Y))")
      case True note \<open>y \<in> Ch h (insert y (X \<union> Y))\<close>
      show ?thesis
      proof(cases "Xd y = Xd x")
        case True with \<open>x \<in> X\<close> \<open>x \<notin> Ch h (X \<union> Y)\<close> \<open>y \<in> Ch h (insert y (X \<union> Y))\<close> show ?thesis
          by clarsimp (metis Ch_singular Un_iff inj_onD insert_absorb)
      next
        case False note xy = \<open>Xd y \<noteq> Xd x\<close>
        show ?thesis
        proof(rule notI)
          assume "x \<in> Ch h (X \<union> insert y Y)"
          with \<open>x \<in> X\<close> have "x \<in> Ch h (insert y (insert x ((X \<union> Y) - {z. Xd z = Xd x})))"
            by - (rule subsetD[OF equalityD1[OF consistencyD[OF Ch_consistency[of h]]], rotated -1],
                  assumption, clarsimp+, metis Ch_range' Ch_singular Un_iff inj_onD insertE)
          with \<open>x \<notin> Ch h (insert x (X \<union> Y - {z. Xd z = Xd x}))\<close> show False
            by (force dest: unilateral_substitutesD3[OF spec[OF Ch_unilateral_substitutes, of h], rotated])
        qed
      qed
    next
      case False with \<open>x \<notin> Ch h (X \<union> Y)\<close> show ?thesis
        using Ch_irc unfolding irc_def by simp
    qed }
  { case 2 from insert(4) show ?case
      by (auto simp: insert_commute insert_Diff_if split: if_splits
               dest: unilateral_substitutesD3[OF spec[OF Ch_unilateral_substitutes, of h], where a=y]) }
qed

text\<open>

To discharge the first antecedent of this lemma, we need an invariant
for the COP that asserts that, for each doctor @{term "d"}, there is a
subset of the contracts currently offered by @{term "d"} that was
previously uniformly rejected by the COP, for each contract that is
rejected at the current step. To support a later theorem (see
\S\ref{sec:cop-worst}) we require these subsets to be upwards-closed
with respect to the doctor's preferences.

\<close>

definition
  cop_F_rejected_inv :: "'b set \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "cop_F_rejected_inv ds fp \<longleftrightarrow> (\<forall>x\<in>RH fp. \<exists>fp'\<subseteq>fp. x \<in> fp' \<and> above (Pd (Xd x)) x \<subseteq> fp' \<and> Xd x \<notin> Xd ` CH fp')"

(*<*)

lemmas cop_F_rejected_invI = iffD2[OF cop_F_rejected_inv_def, rule_format, simplified, unfolded conj_imp_eq_imp_imp]

(*>*)

lemma cop_F_rejected_inv:
  shows "valid ds (\<lambda>ds fp. cop_F_range_inv ds fp \<and> cop_F_closed_inv ds fp \<and> allocation (CH fp)) cop_F_rejected_inv"
proof %invisible (induct rule: validI)
  case base show ?case unfolding cop_F_rejected_inv_def by simp
next
  case (step fp)
  then have "cop_F_closed_inv ds fp"
        and "cop_F_range_inv ds fp"
        and "allocation (CH fp)"
        and "cop_F_rejected_inv ds fp" by blast+
  show ?case
  proof(rule cop_F_rejected_invI)
    fix x assume x: "x \<in> cop_F ds fp" "x \<notin> CH (cop_F ds fp)"
    show "\<exists>fp'\<subseteq>cop_F ds fp. x \<in> fp' \<and> above (Pd (Xd x)) x \<subseteq> fp' \<and> Xd x \<notin> Xd ` CH fp'"
    proof(cases "Xd x \<in> Xd ` CH (cop_F ds fp)")
      case True
      with \<open>x \<notin> CH (cop_F ds fp)\<close> obtain y
        where y: "Xd y = Xd x" "y \<in> CH (cop_F ds fp)" "x \<noteq> y" by (metis imageE)
      from \<open>x \<in> cop_F ds fp\<close> show ?thesis
      proof(cases x rule: cop_F_cases)
        case fp note \<open>x \<in> fp\<close>
        from \<open>y \<in> CH (cop_F ds fp)\<close>
        show ?thesis
        proof(cases y rule: CH_cop_F_cases)
          case CH note \<open>y \<in> CH fp\<close>
          with \<open>allocation (CH fp)\<close> y(1,3) have "x \<notin> CH fp" by (metis inj_on_eq_iff)
          with \<open>cop_F_rejected_inv ds fp\<close> \<open>x \<in> fp\<close> show ?thesis
            unfolding cop_F_rejected_inv_def by (metis Diff_iff Un_upper1 cop_F_def subset_refl subset_trans)
        next
          case RH_fp note \<open>y \<in> RH fp\<close>
          with \<open>cop_F_rejected_inv ds fp\<close>
          obtain fp' where "fp' \<subseteq> fp \<and> y \<in> fp' \<and> above (Pd (Xd y)) y \<subseteq> fp' \<and> Xd y \<notin> Xd ` CH fp'"
            unfolding cop_F_rejected_inv_def by (fastforce simp: mem_CH_Ch)
          with \<open>y \<in> CH (cop_F ds fp)\<close> show ?thesis
            using no_renegotiation_union[where x=y and X="fp'" and Y="cop_F ds fp"] cop_F_increasing
            by (clarsimp simp: mem_Ch_CH image_iff) (metis Un_absorb1 mem_CH_Ch subset_trans)
        next
          case CD_on note \<open>y \<in> CD_on ds (- RH fp) - fp\<close>
          with cop_F_increasing \<open>cop_F_closed_inv ds fp\<close> cop_F_CH_CD_on_disjoint[OF \<open>cop_F_closed_inv ds fp\<close> \<open>cop_F_range_inv ds fp\<close>] \<open>x \<in> fp\<close> y(1) show ?thesis
            unfolding cop_F_closed_inv_def by - (rule exI[where x=fp]; clarsimp; blast)
        qed
      next
        case CD_on
        { fix z assume z: "z \<in> CH (cop_F ds fp)" "Xd z = Xd x"
          from \<open>allocation (CH fp)\<close> x(2) z have "z \<noteq> x" by blast
          from z(1) have False
          proof(cases z rule: CH_cop_F_cases)
            case CH
            with \<open>cop_F_range_inv ds fp\<close> \<open>cop_F_closed_inv ds fp\<close> \<open>x \<in> CD_on ds (- RH fp) - fp\<close> z(2) \<open>z \<noteq> x\<close>
            show False
              using cop_F_CH_CD_on_disjoint by blast
          next
            case RH_fp note \<open>z \<in> RH fp\<close>
            with \<open>cop_F_rejected_inv ds fp\<close>
            obtain fp' where "fp' \<subseteq> fp \<and> z \<in> fp' \<and> above (Pd (Xd z)) z \<subseteq> fp' \<and> Xd z \<notin> Xd ` CH fp'"
              unfolding cop_F_rejected_inv_def by (fastforce simp: mem_CH_Ch)
            with \<open>z \<in> CH (cop_F ds fp)\<close> show ?thesis
              using no_renegotiation_union[where x=z and X="fp'" and Y="cop_F ds fp"] cop_F_increasing
              by (clarsimp simp: mem_Ch_CH image_iff) (metis Un_absorb1 mem_CH_Ch subset_trans)
          next
            case CD_on note \<open>z \<in> CD_on ds (- RH fp) - fp\<close>
            with z(2) \<open>x \<in> CD_on ds (- RH fp) - fp\<close> \<open>z \<noteq> x\<close> show False
              by (meson CD_on_inj_on_Xd DiffD1 inj_onD)
          qed }
        with True have False by clarsimp blast
        then show ?thesis ..
      qed
    next
      case False note \<open>Xd x \<notin> Xd ` CH (cop_F ds fp)\<close>
      with cop_F_closed_inv \<open>cop_F_closed_inv ds fp\<close> \<open>x \<in> cop_F ds fp\<close>
      show ?thesis by (metis cop_F_closed_inv_def subsetI valid_def)
    qed
  qed
qed

lemma fp_cop_F_rejected_inv:
  shows "cop_F_rejected_inv ds (fp_cop_F ds)"
proof %invisible -
  have "invariant ds (\<lambda>ds fp. cop_F_range_inv ds fp \<and> cop_F_closed_inv ds fp \<and> allocation (CH fp) \<and> cop_F_rejected_inv ds fp)"
    using cop_F_range_inv cop_F_closed_inv cop_F_allocation_inv cop_F_rejected_inv
    by - (rule valid_conj | blast | rule valid_pre)+
  then show ?thesis by (blast dest: invariantD)
qed

text\<open>

\label{sec:cop-theorem-4}

\citet[Theorem~4]{HatfieldKojima:2010} assert that we effectively
recover @{const "substitutes"} for the contracts relevant to the
COP. We cannot adopt their phrasing as it talks about the execution
traces of the COP, and not just its final state. Instead we present
the result we use, which relates two consecutive states in an
execution trace of the COP:

\<close>

theorem Theorem_4:
  assumes "cop_F_rejected_inv ds fp"
  assumes "x \<in> RH fp"
  shows "x \<in> RH (cop_F ds fp)"
using %invisible bspec[OF assms[unfolded cop_F_rejected_inv_def]] cop_F_increasing[of fp ds]
      no_renegotiation_union[where x=x and h="Xh x" and Y="cop_F ds fp"]
by (auto simp: mem_CH_Ch image_iff Ch_CH_irc_idem) (metis le_iff_sup mem_Ch_CH sup.coboundedI1)

text\<open>

\label{sec:cop-worst}

Another way to interpret @{const "cop_F_rejected_inv"} is to observe
that the doctor-optimal match contains the least preferred of the
contracts that the doctors have offered.

\<close>

corollary fp_cop_F_worst:
  assumes "x \<in> cop ds"
  assumes "y \<in> fp_cop_F ds"
  assumes "Xd y = Xd x"
  shows "(x, y) \<in> Pd (Xd x)"
proof %invisible (rule ccontr)
  assume "(x, y) \<notin> Pd (Xd x)"
  with assms have "(y, x) \<in> Pd (Xd x) \<and> x \<noteq> y"
    by (metis CH_range' Pd_linear eq_iff fp_cop_F_range_inv' order_on_defs(3) total_on_def underS_incl_iff)
  with assms have "y \<notin> (cop ds)"
    using fp_cop_F_allocation by (blast dest: inj_onD)
  with fp_cop_F_rejected_inv[of ds] \<open>y \<in> fp_cop_F ds\<close>
  obtain fp' where "fp' \<subseteq> fp_cop_F ds \<and> y \<in> fp' \<and> above (Pd (Xd y)) y \<subseteq> fp' \<and> Xd y \<notin> Xd ` CH fp'"
    unfolding cop_F_rejected_inv_def by fastforce
  with \<open>(y, x) \<in> Pd (Xd x) \<and> x \<noteq> y\<close> assms show False
    using no_renegotiation_union[where x=x and h="Xh x" and X=fp' and Y="fp_cop_F ds"]
    unfolding above_def
    by (clarsimp simp: mem_CH_Ch image_iff) (metis contra_subsetD le_iff_sup mem_Ch_CH mem_Collect_eq)
qed

text\<open>

The doctor optimality result, Theorem~5, hinges on showing that no
contract in any stable match is ever rejected.

\<close>

definition
  theorem_5_inv :: "'b set \<Rightarrow> 'a set \<Rightarrow> bool"
where
  "theorem_5_inv ds fp \<longleftrightarrow> RH fp \<inter> \<Union>{X. stable_on ds X} = {}"

(*<*)

lemma theorem_5_invI:
  assumes "\<And>z X. \<lbrakk>z \<in> RH fp; z \<in> X; stable_on ds X\<rbrakk> \<Longrightarrow> False"
  shows "theorem_5_inv ds fp"
unfolding theorem_5_inv_def using assms by blast

(*>*)

lemma theorem_5_inv:
  shows "valid ds (\<lambda>ds fp. cop_F_range_inv ds fp \<and> cop_F_closed_inv ds fp
                     \<and> allocation (CH fp) \<and> cop_F_rejected_inv ds fp) theorem_5_inv"
proof(induct rule: validI)
  case base show ?case unfolding theorem_5_inv_def by simp
next
  case (step fp)
  then have "cop_F_range_inv ds fp"
        and "cop_F_closed_inv ds fp"
        and "allocation (CH fp)"
        and "cop_F_rejected_inv ds fp"
        and "theorem_5_inv ds fp" by blast+
  show ?case
  proof(rule theorem_5_invI)
    fix z X assume z: "z \<in> RH (cop_F ds fp)" and "z \<in> X" and "stable_on ds X"
    from \<open>theorem_5_inv ds fp\<close> \<open>z \<in> X\<close> \<open>stable_on ds X\<close>
    have z': "z \<notin> RH fp" unfolding theorem_5_inv_def by blast
    define Y where "Y \<equiv> Ch (Xh z) (cop_F ds fp)"
    from z have YYY: "z \<notin> Ch (Xh z) (insert z Y)"
      using consistencyD[OF Ch_consistency]
      by (simp add: mem_CH_Ch Y_def)
         (metis Ch_f_range f_range_on_def insert_subset subset_insertI top_greatest)
    have yRx: "(x, y) \<in> Pd (Xd y)" if "x \<in> X" and "y \<in> Y" and "Xd y = Xd x" for x y
    proof(rule ccontr)
      assume "(x, y) \<notin> Pd (Xd y)"
      with Pd_linear \<open>cop_F_range_inv ds fp\<close> \<open>stable_on ds X\<close> that
      have BBB: "(y, x) \<in> Pd (Xd y) \<and> x \<noteq> y"
        unfolding Y_def cop_F_def cop_F_range_inv_def order_on_defs total_on_def
        by (clarsimp simp: mem_CD_on_Cd dest!: Ch_range') (metis Cd_range' Int_iff refl_onD stable_on_range')
      from \<open>stable_on ds X\<close> \<open>cop_F_closed_inv ds fp\<close> \<open>theorem_5_inv ds fp\<close> BBB that have "x \<in> fp \<and> y \<in> fp"
        unfolding cop_F_def cop_F_closed_inv_def theorem_5_inv_def above_def Y_def
        by (fastforce simp: mem_CD_on_Cd dest: Ch_range' Cd_preferred)
      with \<open>stable_on ds X\<close> \<open>theorem_5_inv ds fp\<close> \<open>x \<in> X\<close> have "x \<in> Ch (Xh x) fp"
        unfolding theorem_5_inv_def by (force simp: mem_CH_Ch)
      with \<open>allocation (CH fp)\<close> \<open>Xd y = Xd x\<close> BBB have "y \<notin> Ch (Xh z) fp"
        by (metis Ch_range' inj_onD mem_CH_Ch)
      with \<open>y \<in> Y\<close> \<open>x \<in> fp \<and> y \<in> fp\<close> show False
        unfolding Y_def using Theorem_4[OF \<open>cop_F_rejected_inv ds fp\<close>, where x=y]
        by (metis Ch_range' Diff_iff mem_CH_Ch)
    qed
    have "Xd z \<notin> Xd ` Y"
    proof(safe)
      fix w assume w: "Xd z = Xd w" "w \<in> Y"
      show False
      proof(cases "z \<in> fp")
        case True note \<open>z \<in> fp\<close>
        show False
        proof(cases "w \<in> fp")
          case True note \<open>w \<in> fp\<close>
          from \<open>Xd z = Xd w\<close> \<open>w \<in> Y\<close> z' \<open>z \<in> fp\<close> have "w \<notin> CH fp"
            by (metis Ch_irc_idem DiffI YYY Y_def \<open>allocation (CH fp)\<close> inj_on_eq_iff insert_absorb)
          with Theorem_4[OF \<open>cop_F_rejected_inv ds fp\<close>, where x=w] \<open>w \<in> Y\<close> \<open>w \<in> fp\<close> show False
            unfolding Y_def CH_def by simp
        next
          case False note \<open>w \<notin> fp\<close>
          with \<open>w \<in> Y\<close> have "w \<notin> Ch (Xh z) fp \<and> w \<in> cop_F ds fp \<and> Xh w = Xh z"
            unfolding Y_def by (blast dest: Ch_range')
          with \<open>cop_F_closed_inv ds fp\<close> \<open>cop_F_range_inv ds fp\<close> \<open>z \<notin> RH fp\<close> \<open>w \<notin> fp\<close> \<open>z \<in> fp\<close> \<open>Xd z = Xd w\<close>
          show False
            unfolding cop_F_closed_inv_def cop_F_range_inv_def above_def
            by (fastforce simp: cop_F_def mem_CD_on_Cd Cd_greatest greatest_def)
        qed
      next
        case False note \<open>z \<notin> fp\<close>
        from \<open>cop_F_range_inv ds fp\<close> \<open>cop_F_closed_inv ds fp\<close> z \<open>z \<notin> fp\<close> have "Xd z \<notin> Xd ` Ch (Xh z) fp"
          unfolding cop_F_range_inv_def cop_F_closed_inv_def above_def
          by (clarsimp simp: mem_CD_on_Cd Cd_greatest greatest_def dest!: mem_Ch_CH elim!: cop_F_cases)
             (blast dest: CH_range')
        with w \<open>z \<in> RH (cop_F ds fp)\<close> \<open>z \<notin> fp\<close> show False
          by (clarsimp simp: Y_def cop_F_def mem_CH_Ch)
             (metis CD_on_inj_on_Xd Ch_range' Un_iff inj_onD no_renegotiation_union)
      qed
    qed
    show False
    proof(cases "z \<in> Ch (Xh z) (X \<union> Y)")
      case True note \<open>z \<in> Ch (Xh z) (X \<union> Y)\<close>
      with \<open>z \<in> X\<close> have "Xd z \<in> Xd ` Ch (Xh z) (insert z Y)"
        using no_renegotiation_union[where X="insert z Y" and Y="X - {z}" and x=z and h="Xh z"]
        by clarsimp (metis Un_insert_right insert_Diff Un_commute)
      with \<open>Xd z \<notin> Xd ` Y\<close> \<open>z \<notin> Ch (Xh z) (insert z Y)\<close> show False by (blast dest: Ch_range')
    next
      case False note \<open>z \<notin> Ch (Xh z) (X \<union> Y)\<close>
      have "\<not>stable_on ds X"
      proof(rule blocking_on_imp_not_stable[OF blocking_onI])
        from False \<open>z \<in> X\<close> \<open>stable_on ds X\<close>
        show "Ch (Xh z) (X \<union> Y) \<noteq> Ch (Xh z) X"
          using mem_CH_Ch stable_on_CH by blast
        show "Ch (Xh z) (X \<union> Y) = Ch (Xh z) (X \<union> Ch (Xh z) (X \<union> Y))"
          using Ch_range' by (blast intro!: consistencyD[OF Ch_consistency])
      next
        fix x assume "x \<in> Ch (Xh z) (X \<union> Y)"
        with Ch_singular'[of "Xh z" "X \<union> Ch (Xh z) (cop_F ds fp)"]
             invariant_cop_FD[OF cop_F_range_inv \<open>cop_F_range_inv ds fp\<close>]
             stable_on_allocation[OF \<open>stable_on ds X\<close>] stable_on_Xd[OF \<open>stable_on ds X\<close>]
             stable_on_range'[OF \<open>stable_on ds X\<close>]
        show "x \<in> CD_on ds (X \<union> Ch (Xh z) (X \<union> Y))"
          unfolding cop_F_range_inv_def
          by (clarsimp simp: mem_CD_on_Cd Cd_greatest greatest_def)
             (metis Ch_range' IntE Pd_range' Pd_refl Un_iff Y_def inj_onD yRx)
      qed
      with \<open>stable_on ds X\<close> show False by blast
    qed
  qed
qed

lemma fp_cop_F_theorem_5_inv:
  shows "theorem_5_inv ds (fp_cop_F ds)"
proof %invisible -
  have "invariant ds (\<lambda>ds fp. cop_F_range_inv ds fp \<and> cop_F_closed_inv ds fp \<and> allocation (CH fp) \<and> cop_F_rejected_inv ds fp \<and> theorem_5_inv ds fp)"
    using cop_F_range_inv cop_F_closed_inv cop_F_allocation_inv cop_F_rejected_inv theorem_5_inv
    by - (rule valid_conj | blast | rule valid_pre)+
  then show ?thesis by (blast dest: invariantD)
qed

theorem Theorem_5:
  assumes "stable_on ds X"
  assumes "x \<in> X"
  shows "\<exists>y \<in> cop ds. (x, y) \<in> Pd (Xd x)"
proof -
  from fp_cop_F_theorem_5_inv assms
  have x: "x \<notin> RH (fp_cop_F ds)"
    unfolding theorem_5_inv_def by blast
  show ?thesis
  proof(cases "Xd x \<in> Xd ` cop ds")
    case True
    then obtain z where z: "z \<in> cop ds" "Xd z = Xd x" by auto
    show ?thesis
    proof(cases "(x, z) \<in> Pd (Xd x)")
      case True with z show ?thesis by blast
    next
      case False
      with Pd_linear'[where d="Xd x"] fp_cop_F_range_inv'[of z ds] assms z
      have "(z, x) \<in> Pd (Xd x)"
        unfolding order_on_defs total_on_def by (metis CH_range' refl_onD stable_on_range')
      with fp_cop_F_closed_inv'[of z ds x] x z have "x \<in> fp_cop_F ds"
        unfolding above_def by (force simp: mem_CH_Ch dest: Ch_range')
      with fp_cop_F_allocation x z have "z = x" by (fastforce dest: inj_onD)
      with Pd_linear assms z show ?thesis
        by (meson equalityD2 stable_on_range' underS_incl_iff)
    qed
  next
    case False note \<open>Xd x \<notin> Xd ` cop ds\<close>
    with assms x show ?thesis
      by (metis DiffI Diff_eq_empty_iff fp_cop_F_all emptyE imageI stable_on_Xd stable_on_range')
  qed
qed

theorem fp_cop_F_doctor_optimal_match:
  shows "doctor_optimal_match ds (cop ds)"
by %invisible (rule doctor_optimal_matchI[OF Theorem_1 Theorem_5]) auto

end

text\<open>

\label{sec:cop-opposition-of-interests}

The next lemma demonstrates the @{emph \<open>opposition of interests\<close>} of
doctors and hospitals: if all doctors weakly prefer one stable match
to another, then the hospitals weakly prefer the converse.

As we do not have linear preferences for hospitals, we use revealed
preference and hence assume @{const "irc"} holds of hospital choice
functions. Our definition of the doctor-preferred ordering @{term
"dpref"} follows the Isabelle/HOL convention of putting the larger
(more preferred) element on the right, and takes care with
unemployment.

\<close>

context Contracts
begin

definition dpref :: "'x set \<Rightarrow> 'x set \<Rightarrow> bool" where
  "dpref X Y = (\<forall>x\<in>X. \<exists>y\<in>Y. (x, y) \<in> Pd (Xd x))"

lemmas %invisible dprefI = iffD2[OF dpref_def, rule_format]

end

context ContractsWithIRC
begin

theorem Lemma_1:
  assumes "stable_on ds Y"
  assumes "stable_on ds Z"
  assumes "dpref Z Y"
  assumes "x \<in> Ch h Z"
  shows "x \<in> Ch h (Y \<union> Z)"
proof(rule ccontr)
  assume "x \<notin> Ch h (Y \<union> Z)"
  from \<open>x \<in> Ch h Z\<close> \<open>x \<notin> Ch h (Y \<union> Z)\<close>
  have "Ch h (Y \<union> Z) \<noteq> Ch h Z" by blast
  moreover
  have "Ch h (Y \<union> Z) = Ch h (Z \<union> Ch h (Y \<union> Z))"
   by (rule consistency_onD[OF Ch_consistency]; auto dest: Ch_range')
  moreover
  have "y \<in> CD_on ds (Z \<union> Ch h (Y \<union> Z))" if "y \<in> Ch h (Y \<union> Z)" for y
  proof -
    from \<open>stable_on ds Y\<close> \<open>stable_on ds Z\<close> that
    have "Xd y \<in> ds \<and> y \<in> Field (Pd (Xd y))"
      using stable_on_Xd stable_on_range' Ch_range' by (meson Un_iff)
    with Pd_linear'[of "Xd y"] Ch_singular \<open>stable_on ds Y\<close> \<open>stable_on ds Z\<close> \<open>dpref Z Y\<close> that show ?thesis
      unfolding dpref_def
      by (clarsimp simp: mem_CD_on_Cd Cd_greatest greatest_def)
         (metis Ch_range' Pd_Xd Un_iff eq_iff inj_on_contraD stable_on_allocation underS_incl_iff)
  qed
  ultimately show False by (blast dest: stable_on_blocking_onD[OF \<open>stable_on ds Z\<close>])
qed

end

text (in Contracts) \<open>

\citet[Corollary~1 (of Theorem~5 and Lemma~1)]{HatfieldKojima:2010}:
@{const "unilateral_substitutes"} implies there is a hospital-pessimal
match, which is indeed the doctor-optimal one.

\<close>

context ContractsWithUnilateralSubstitutesAndIRC
begin

theorem Corollary_1:
  assumes "stable_on ds Z"
  shows "dpref Z (cop ds)"
    and "x \<in> Z \<Longrightarrow> x \<in> Ch (Xh x) (cop ds \<union> Z)"
proof -
  show "dpref Z (cop ds)"
    by (rule dprefI[OF Theorem_5[OF \<open>stable_on ds Z\<close>]])
  fix x assume "x \<in> Z" with assms show "x \<in> Ch (Xh x) (cop ds \<union> Z)"
    using Lemma_1[OF Theorem_1 assms \<open>dpref Z (cop ds)\<close>] stable_on_CH
    by (fastforce simp: mem_CH_Ch)
qed

text\<open>

\citet[p1717]{HatfieldKojima:2010} show that there is not always a
hospital-optimal/doctor-pessimal match when hospital preferences
satisfy @{const "unilateral_substitutes"}, in contrast to the
situation under @{const "substitutes"} (see
\S\ref{sec:contracts-optimality}). This reflects the loss of the
lattice structure.

\<close>

end


subsection\<open> Theorem~6: A ``rural hospitals'' theorem \label{sec:cop-rh} \<close>

text (in Contracts) \<open>

\citet[Theorem~6]{HatfieldKojima:2010} demonstrates a ``rural
hospitals'' theorem for the COP assuming hospital choice functions
satisfy @{const "unilateral_substitutes"} and @{const "lad"}, as for
\S\ref{sec:contracts-rh}. However \citet[\S4,
Example~1]{AygunSonmez:2012-WP} observe that @{thm [source]
"lad_on_substitutes_on_irc_on"} does not hold with @{const
"bilateral_substitutes"} instead of @{const "substitutes"}, and their
Example~3 similarly for @{const "unilateral_substitutes"}. Moreover
@{const "fp_cop_F"} can yield an unstable allocation with just these
two hypotheses. Ergo we need to assume @{const "irc"} even when we
have @{const "lad"}, unlike before (see \S\ref{sec:contracts-rh}).

This theorem is the foundation for all later strategic results.

\<close>

locale ContractsWithUnilateralSubstitutesAndIRCAndLAD = ContractsWithUnilateralSubstitutesAndIRC + ContractsWithLAD

sublocale ContractsWithSubstitutesAndLAD < ContractsWithUnilateralSubstitutesAndIRCAndLAD
using %invisible Ch_lad by unfold_locales

context ContractsWithUnilateralSubstitutesAndIRCAndLAD
begin

context
  fixes ds :: "'b set"
  fixes X :: "'a set"
  assumes "stable_on ds X"
begin

text\<open>

The proofs of these first two lemmas are provided by
\citet[Theorem~6]{HatfieldKojima:2010}. We treat unemployment in the
definition of the function @{term "A"} as we did in
\S\ref{sec:contracts-t1-converse}.

\<close>

lemma RHT_Cd_card:
  assumes "d \<in> ds"
  shows "card (Cd d X) \<le> card (Cd d (cop ds))"
proof %invisible (cases "d \<in> Xd ` X")
  case True
  then obtain x where "x \<in> X" "Xd x = d" by blast
  with \<open>stable_on ds X\<close> have "Cd d X = {x}"
    using Cd_singleton mem_CD_on_Cd stable_on_CD_on by blast
  moreover
  from Theorem_5[OF \<open>stable_on ds X\<close> \<open>x \<in> X\<close>] obtain y where "Cd d (cop ds) = {y}"
    using Cd_single Cd_singleton FieldI2 \<open>Xd x = d\<close> fp_cop_F_allocation by metis
  ultimately show ?thesis by simp
next
  case False
  then have "Cd d X = {}"
    using Cd_Xd Cd_range' by blast
  then show ?thesis by simp
qed

lemma RHT_Ch_card:
  shows "card (Ch h (fp_cop_F ds)) \<le> card (Ch h X)"
proof -
  define A where "A \<equiv> \<lambda>X. {y |y. Xd y \<in> ds \<and> y \<in> Field (Pd (Xd y)) \<and> (\<forall>x \<in> X. Xd x = Xd y \<longrightarrow> (x, y) \<in> Pd (Xd x))}"
  have "A (cop ds) = fp_cop_F ds" (is "?lhs = ?rhs")
  proof(rule set_elem_equalityI)
    fix x assume "x \<in> ?lhs"
    show "x \<in> ?rhs"
    proof(cases "Xd x \<in> Xd ` cop ds")
      case True with \<open>x \<in> ?lhs\<close> show ?thesis
        unfolding A_def by clarsimp (metis CH_range' above_def fp_cop_F_closed_inv' mem_Collect_eq)
    next
      case False with \<open>x \<in> ?lhs\<close> fp_cop_F_all show ?thesis
        unfolding A_def by blast
    qed
  next
    fix x assume "x \<in> ?rhs"
    with fp_cop_F_worst show "x \<in> ?lhs"
      unfolding A_def using fp_cop_F_range_inv'[OF \<open>x \<in> ?rhs\<close>] by fastforce
  qed
  moreover
  have "CH (A X) = X"
  proof(rule ccontr)
    assume "CH (A X) \<noteq> X"
    then have "CH (A X) \<noteq> CH X" using \<open>stable_on ds X\<close> stable_on_CH by blast
    then obtain h where XXX: "Ch h (A X) \<noteq> Ch h X" using mem_CH_Ch by blast
    have "\<not>stable_on ds X"
    proof(rule blocking_on_imp_not_stable[OF blocking_onI])
      show "Ch h (A X) \<noteq> Ch h X" by fact
      from Pd_linear \<open>stable_on ds X\<close> show "Ch h (A X) = Ch h (X \<union> Ch h (A X))"
        unfolding A_def
        by - (rule consistencyD[OF Ch_consistency],
              auto 10 0 dest: Ch_range' stable_on_Xd stable_on_range' stable_on_allocation inj_onD underS_incl_iff)
    next
      fix x assume "x \<in> Ch h (A X)"
      with Ch_singular Pd_linear show "x \<in> CD_on ds (X \<union> Ch h (A X))"
        unfolding A_def
        by (auto 9 3 simp: mem_CD_on_Cd Cd_greatest greatest_def
                     dest: Ch_range' Pd_range' Cd_Xd Cd_single inj_onD underS_incl_iff
                    intro: FieldI1)
    qed
    with \<open>stable_on ds X\<close> show False by blast
  qed
  moreover
  from Pd_linear Theorem_5[OF \<open>stable_on ds X\<close>] \<open>stable_on ds X\<close> have "A (cop ds) \<subseteq> A X"
    unfolding A_def order_on_defs by (fastforce dest: Pd_Xd elim: transE)
  then have "card (Ch h (A (cop ds))) \<le> card (Ch h (A X))"
    by (fastforce intro: ladD[OF spec[OF Ch_lad]])
  ultimately show ?thesis by (metis (no_types, lifting) Ch_CH_irc_idem)
qed

text\<open>

The top-level proof is the same as in \S\ref{sec:contracts-rh}.

\<close>

lemma Theorem_6_fp_cop_F:
  shows "d \<in> ds \<Longrightarrow> card (Cd d X) = card (Cd d (cop ds))"
    and "card (Ch h X) = card (Ch h (fp_cop_F ds))"
proof -
  let ?Sum_Cd_COP = "\<Sum>d\<in>ds. card (Cd d (cop ds))"
  let ?Sum_Ch_COP = "\<Sum>h\<in>UNIV. card (Ch h (fp_cop_F ds))"
  let ?Sum_Cd_X = "\<Sum>d\<in>ds. card (Cd d X)"
  let ?Sum_Ch_X = "\<Sum>h\<in>UNIV. card (Ch h X)"

  have "?Sum_Cd_COP = ?Sum_Ch_COP"
    using Theorem_1 stable_on_CD_on CD_on_card[symmetric] CH_card[symmetric] by simp
  also have "\<dots> \<le> ?Sum_Ch_X"
    using RHT_Ch_card by (simp add: sum_mono)
  also have "\<dots> = ?Sum_Cd_X"
    using CD_on_card[symmetric] CH_card[symmetric]
    using \<open>stable_on ds X\<close> stable_on_CD_on stable_on_CH by auto
  finally have "?Sum_Cd_X = ?Sum_Cd_COP"
    using RHT_Cd_card by (simp add: eq_iff sum_mono)
  with RHT_Cd_card show "d \<in> ds \<Longrightarrow> card (Cd d X) = card (Cd d (cop ds))"
    by (fastforce elim: sum_mono_inv)

  have "?Sum_Ch_X = ?Sum_Cd_X"
    using \<open>stable_on ds X\<close> stable_on_CD_on stable_on_CH CD_on_card[symmetric] CH_card[symmetric] by simp
  also have "\<dots> \<le> ?Sum_Cd_COP"
    using RHT_Cd_card by (simp add: sum_mono)
  also have "\<dots> = ?Sum_Ch_COP"
    using CD_on_card[symmetric] CH_card[symmetric]
    using Theorem_1 stable_on_CD_on stable_on_CH by auto
  finally have "?Sum_Ch_COP = ?Sum_Ch_X"
    using RHT_Ch_card by (simp add: eq_iff sum_mono)
  with RHT_Ch_card show "card (Ch h X) = card (Ch h (fp_cop_F ds))"
    by (fastforce elim: sym[OF sum_mono_inv])
qed

end

theorem Theorem_6:
  assumes "stable_on ds X"
  assumes "stable_on ds Y"
  shows "d \<in> ds \<Longrightarrow> card (Cd d X) = card (Cd d Y)"
    and "card (Ch h X) = card (Ch h Y)"
using %invisible Theorem_6_fp_cop_F assms by simp_all

end


subsection\<open> Concluding remarks \<close>

text\<open>

We next discuss a kind of interference between doctors termed
@{emph \<open>bossiness\<close>} in \S\ref{sec:bossiness}. This has some implications
for the strategic issues we discuss in \S\ref{sec:strategic}.

\<close>
(*<*)

end
(*>*)
