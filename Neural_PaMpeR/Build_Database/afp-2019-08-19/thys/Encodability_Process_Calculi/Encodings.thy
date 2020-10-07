theory Encodings
  imports ProcessCalculi
begin

section \<open>Encodings\<close>

text \<open>In the simplest case an encoding from a source into a target language is a mapping from
        source into target terms. Encodability criteria describe properties on such mappings. To
        analyse encodability criteria we map them on conditions on relations between source and
        target terms. More precisely, we consider relations on pairs of the disjoint union of
        source and target terms. We denote this disjoint union of source and target terms by Proc.
\<close>

datatype ('procS, 'procT) Proc =
  SourceTerm 'procS |
  TargetTerm 'procT

definition STCal
    :: "'procS processCalculus \<Rightarrow> 'procT processCalculus
        \<Rightarrow> (('procS, 'procT) Proc) processCalculus"
  where
  "STCal Source Target \<equiv>
   \<lparr>Reductions = \<lambda>P P'.
   (\<exists>SP SP'. P = SourceTerm SP \<and> P' = SourceTerm SP' \<and> Reductions Source SP SP') \<or>
   (\<exists>TP TP'. P = TargetTerm TP \<and> P' = TargetTerm TP' \<and> Reductions Target TP TP')\<rparr>"

definition STCalWB
    :: "('procS, 'barbs) calculusWithBarbs \<Rightarrow> ('procT, 'barbs) calculusWithBarbs
        \<Rightarrow> (('procS, 'procT) Proc, 'barbs) calculusWithBarbs"
  where
  "STCalWB Source Target \<equiv>
   \<lparr>Calculus = STCal (calculusWithBarbs.Calculus Source) (calculusWithBarbs.Calculus Target),
   HasBarb   = \<lambda>P a. (\<exists>SP. P = SourceTerm SP \<and> (calculusWithBarbs.HasBarb Source) SP a) \<or>
                     (\<exists>TP. P = TargetTerm TP \<and> (calculusWithBarbs.HasBarb Target) TP a)\<rparr>"

text \<open>An encoding consists of a source language, a target language, and a mapping from source
        into target terms.\<close>

locale encoding =
  fixes Source :: "'procS processCalculus"
    and Target :: "'procT processCalculus"
    and Enc    :: "'procS \<Rightarrow> 'procT"
begin

abbreviation enc :: "'procS \<Rightarrow> 'procT" ("\<lbrakk>_\<rbrakk>" [65] 70) where
  "\<lbrakk>S\<rbrakk> \<equiv> Enc S"

abbreviation isSource :: "('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<in> ProcS" [70] 80) where
  "P \<in> ProcS \<equiv> (\<exists>S. P = SourceTerm S)"

abbreviation isTarget :: "('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<in> ProcT" [70] 80) where
  "P \<in> ProcT \<equiv> (\<exists>T. P = TargetTerm T)"

abbreviation getSource
    :: "'procS \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<in>S _" [70, 70] 80)
  where
  "S \<in>S P \<equiv> (P = SourceTerm S)"

abbreviation getTarget
    :: "'procT \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<in>T _" [70, 70] 80)
  where
  "T \<in>T P \<equiv> (P = TargetTerm T)"

text \<open>A step of a term in Proc is either a source term step or a target term step.\<close>

abbreviation stepST
    :: "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<longmapsto>ST _" [70, 70] 80)
  where
  "P \<longmapsto>ST P' \<equiv>
   (\<exists>S S'. S \<in>S P \<and> S' \<in>S P' \<and> S \<longmapsto>Source S') \<or> (\<exists>T T'. T \<in>T P \<and> T' \<in>T P' \<and> T \<longmapsto>Target T')"

lemma stepST_STCal_step:
  fixes P P' :: "('procS, 'procT) Proc"
  shows "P \<longmapsto>(STCal Source Target) P' = P \<longmapsto>ST P'"
    by (simp add: STCal_def)

lemma STStep_step:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<longmapsto>ST P' = (\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source S')"
    and "TargetTerm T \<longmapsto>ST P' = (\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target T')"
    by blast+

lemma STCal_step:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<longmapsto>(STCal Source Target) P' = (\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source S')"
    and "TargetTerm T \<longmapsto>(STCal Source Target) P' = (\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target T')"
    by (simp add: STCal_def)+

text \<open>A sequence of steps of a term in Proc is either a sequence of source term steps or a
        sequence of target term steps.\<close>

abbreviation stepsST
    :: "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<longmapsto>ST* _" [70, 70] 80)
  where
  "P \<longmapsto>ST* P' \<equiv>
   (\<exists>S S'. S \<in>S P \<and> S' \<in>S P' \<and> S \<longmapsto>Source* S') \<or> (\<exists>T T'. T \<in>T P \<and> T' \<in>T P' \<and> T \<longmapsto>Target* T')"

lemma STSteps_steps:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<longmapsto>ST* P' = (\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source* S')"
    and "TargetTerm T \<longmapsto>ST* P' = (\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target* T')"
    by blast+

lemma STCal_steps:
  fixes S  :: "'procS"
    and T  :: "'procT"
    and P' :: "('procS, 'procT) Proc"
  shows "SourceTerm S \<longmapsto>(STCal Source Target)* P' = (\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source* S')"
    and "TargetTerm T \<longmapsto>(STCal Source Target)* P' = (\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target* T')"
proof auto
  assume "SourceTerm S \<longmapsto>(STCal Source Target)* P'"
  from this obtain n where "SourceTerm S \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P'"
    by (auto simp add: steps_def)
  thus "\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source* S'"
  proof (induct n arbitrary: P')
    case 0
    assume "SourceTerm S \<longmapsto>(STCal Source Target)\<^bsup>0\<^esup> P'"
    hence "S \<in>S P'"
      by simp
    moreover have "S \<longmapsto>Source* S"
      by (rule steps_refl)
    ultimately show "\<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source* S'"
      by blast
  next
    case (Suc n P'')
    assume "SourceTerm S \<longmapsto>(STCal Source Target)\<^bsup>Suc n\<^esup> P''"
    from this obtain P' where A1: "SourceTerm S \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P'"
                          and A2: "P' \<longmapsto>(STCal Source Target) P''"
      by auto
    assume "\<And>P'. SourceTerm S \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P' \<Longrightarrow> \<exists>S'. S' \<in>S P' \<and> S \<longmapsto>Source* S'"
    with A1 obtain S' where A3: "S' \<in>S P'" and A4: "S \<longmapsto>Source* S'"
      by blast
    from A2 A3 obtain S'' where A5: "S'' \<in>S P''" and A6: "S' \<longmapsto>Source S''"
        using STCal_step(1)[where S="S'" and P'="P''"]
      by blast
    from A4 A6 have "S \<longmapsto>Source* S''"
        using step_to_steps[where Cal="Source" and P="S'" and P'="S''"]
      by (simp add: steps_add[where Cal="Source" and P="S" and Q="S'" and R="S''"])
    with A5 show "\<exists>S''. S'' \<in>S P'' \<and> S \<longmapsto>Source* S''"
      by blast
  qed
next
  fix S'
  assume "S \<longmapsto>Source* S'"
  from this obtain n where "S \<longmapsto>Source\<^bsup>n\<^esup> S'"
    by (auto simp add: steps_def)
  thus "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
  proof (induct n arbitrary: S')
    case 0
    assume "S \<longmapsto>Source\<^bsup>0\<^esup> S'"
    hence "S = S'"
      by auto
    thus "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
      by (simp add: steps_refl)
  next
    case (Suc n S'')
    assume "S \<longmapsto>Source\<^bsup>Suc n\<^esup> S''"
    from this obtain S' where B1: "S \<longmapsto>Source\<^bsup>n\<^esup> S'" and B2: "S' \<longmapsto>Source S''"
      by auto
    assume "\<And>S'. S \<longmapsto>Source\<^bsup>n\<^esup> S' \<Longrightarrow> SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
    with B1 have "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S')"
      by blast
    moreover from B2 have "SourceTerm S' \<longmapsto>(STCal Source Target)* (SourceTerm S'')"
        using step_to_steps[where Cal="STCal Source Target" and P="SourceTerm S'"]
      by (simp add: STCal_def)
    ultimately show "SourceTerm S \<longmapsto>(STCal Source Target)* (SourceTerm S'')"
      by (rule steps_add)
  qed
next
  assume "TargetTerm T \<longmapsto>(STCal Source Target)* P'"
  from this obtain n where "TargetTerm T \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P'"
    by (auto simp add: steps_def)
  thus "\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target* T'"
  proof (induct n arbitrary: P')
    case 0
    assume "TargetTerm T \<longmapsto>(STCal Source Target)\<^bsup>0\<^esup> P'"
    hence "T \<in>T P'"
      by simp
    moreover have "T \<longmapsto>Target* T"
      by (rule steps_refl)
    ultimately show "\<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target* T'"
      by blast
  next
    case (Suc n P'')
    assume "TargetTerm T \<longmapsto>(STCal Source Target)\<^bsup>Suc n\<^esup> P''"
    from this obtain P' where A1: "TargetTerm T \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P'"
                          and A2: "P' \<longmapsto>(STCal Source Target) P''"
      by auto
    assume "\<And>P'. TargetTerm T \<longmapsto>(STCal Source Target)\<^bsup>n\<^esup> P' \<Longrightarrow> \<exists>T'. T' \<in>T P' \<and> T \<longmapsto>Target* T'"
    with A1 obtain T' where A3: "T' \<in>T P'" and A4: "T \<longmapsto>Target* T'"
      by blast
    from A2 A3 obtain T'' where A5: "T'' \<in>T P''" and A6: "T' \<longmapsto>Target T''"
        using STCal_step(2)[where T="T'" and P'="P''"]
      by blast
    from A4 A6 have "T \<longmapsto>Target* T''"
        using step_to_steps[where Cal="Target" and P="T'" and P'="T''"]
      by (simp add: steps_add[where Cal="Target" and P="T" and Q="T'" and R="T''"])
    with A5 show "\<exists>T''. T'' \<in>T P'' \<and> T \<longmapsto>Target* T''"
      by blast
  qed
next
  fix T'
  assume "T \<longmapsto>Target* T'"
  from this obtain n where "T \<longmapsto>Target\<^bsup>n\<^esup> T'"
    by (auto simp add: steps_def)
  thus "TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T')"
  proof (induct n arbitrary: T')
    case 0
    assume "T \<longmapsto>Target\<^bsup>0\<^esup> T'"
    hence "T = T'"
      by auto
    thus "TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T')"
      by (simp add: steps_refl)
  next
    case (Suc n T'')
    assume "T \<longmapsto>Target\<^bsup>Suc n\<^esup> T''"
    from this obtain T' where B1: "T \<longmapsto>Target\<^bsup>n\<^esup> T'" and B2: "T' \<longmapsto>Target T''"
      by auto
    assume "\<And>T'. T \<longmapsto>Target\<^bsup>n\<^esup> T' \<Longrightarrow> TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T')"
    with B1 have "TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T')"
      by blast
    moreover from B2 have "TargetTerm T' \<longmapsto>(STCal Source Target)* (TargetTerm T'')"
        using step_to_steps[where Cal="STCal Source Target" and P="TargetTerm T'"]
      by (simp add: STCal_def)
    ultimately show "TargetTerm T \<longmapsto>(STCal Source Target)* (TargetTerm T'')"
      by (rule steps_add)
  qed
qed

lemma stepsST_STCal_steps:
  fixes P P' :: "('procS, 'procT) Proc"
  shows "P \<longmapsto>(STCal Source Target)* P' = P \<longmapsto>ST* P'"
proof (cases P)
  case (SourceTerm SP)
  assume "SP \<in>S P"
  thus "P \<longmapsto>(STCal Source Target)* P' = P \<longmapsto>ST* P'"
      using STCal_steps(1)[where S="SP" and P'="P'"] STSteps_steps(1)[where S="SP" and P'="P'"]
    by blast
next
  case (TargetTerm TP)
  assume "TP \<in>T P"
  thus "P \<longmapsto>(STCal Source Target)* P' = P \<longmapsto>ST* P'"
      using STCal_steps(2)[where T="TP" and P'="P'"] STSteps_steps(2)[where T="TP" and P'="P'"]
    by blast
qed

lemma stepsST_refl:
  fixes P :: "('procS, 'procT) Proc"
  shows "P \<longmapsto>ST* P"
    by (cases P, simp_all add: steps_refl)

lemma stepsST_add:
  fixes P Q R :: "('procS, 'procT) Proc"
  assumes A1: "P \<longmapsto>ST* Q"
      and A2: "Q \<longmapsto>ST* R"
  shows "P \<longmapsto>ST* R"
proof -
  from A1 have "P \<longmapsto>(STCal Source Target)* Q"
    by (simp add: stepsST_STCal_steps)
  moreover from A2 have "Q \<longmapsto>(STCal Source Target)* R"
    by (simp add: stepsST_STCal_steps)
  ultimately have "P \<longmapsto>(STCal Source Target)* R"
    by (rule steps_add)
  thus "P \<longmapsto>ST* R"
    by (simp add: stepsST_STCal_steps)
qed

text \<open>A divergent term of Proc is either a divergent source term or a divergent target term.\<close>

abbreviation divergentST
    :: "('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<longmapsto>ST\<omega>" [70] 80)
  where
  "P \<longmapsto>ST\<omega> \<equiv> (\<exists>S. S \<in>S P \<and> S \<longmapsto>(Source)\<omega>) \<or> (\<exists>T. T \<in>T P \<and> T \<longmapsto>(Target)\<omega>)"

lemma STCal_divergent:
  fixes S  :: "'procS"
    and T  :: "'procT"
  shows "SourceTerm S \<longmapsto>(STCal Source Target)\<omega> = S \<longmapsto>(Source)\<omega>"
    and "TargetTerm T \<longmapsto>(STCal Source Target)\<omega> = T \<longmapsto>(Target)\<omega>"
      using STCal_steps
    by (auto simp add: STCal_def divergent_def)

lemma divergentST_STCal_divergent:
  fixes P :: "('procS, 'procT) Proc"
  shows "P \<longmapsto>(STCal Source Target)\<omega> = P \<longmapsto>ST\<omega>"
proof (cases P)
  case (SourceTerm SP)
  assume "SP \<in>S P"
  thus "P \<longmapsto>(STCal Source Target)\<omega> = P \<longmapsto>ST\<omega>"
      using STCal_divergent(1)
    by simp
next
  case (TargetTerm TP)
  assume "TP \<in>T P"
  thus "P \<longmapsto>(STCal Source Target)\<omega> = P \<longmapsto>ST\<omega>"
      using STCal_divergent(2)
    by simp
qed

text \<open>Similar to relations we define what it means for an encoding to preserve, reflect, or
        respect a predicate. An encoding preserves some predicate P if P(S) implies P(enc S) for
        all source terms S.\<close>

abbreviation enc_preserves_pred :: "(('procS, 'procT) Proc \<Rightarrow> bool) \<Rightarrow> bool" where
  "enc_preserves_pred Pred \<equiv> \<forall>S. Pred (SourceTerm S) \<longrightarrow> Pred (TargetTerm (\<lbrakk>S\<rbrakk>))"

abbreviation enc_preserves_binary_pred
    :: "(('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "enc_preserves_binary_pred Pred \<equiv> \<forall>S x. Pred (SourceTerm S) x \<longrightarrow> Pred (TargetTerm (\<lbrakk>S\<rbrakk>)) x"

text \<open>An encoding reflects some predicate P if P(S) implies P(enc S) for all source terms S.\<close>

abbreviation enc_reflects_pred :: "(('procS, 'procT) Proc \<Rightarrow> bool) \<Rightarrow> bool" where
  "enc_reflects_pred Pred \<equiv> \<forall>S. Pred (TargetTerm (\<lbrakk>S\<rbrakk>)) \<longrightarrow> Pred (SourceTerm S)"

abbreviation enc_reflects_binary_pred
    :: "(('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "enc_reflects_binary_pred Pred \<equiv> \<forall>S x. Pred (TargetTerm (\<lbrakk>S\<rbrakk>)) x \<longrightarrow> Pred (SourceTerm S) x"

text \<open>An encoding respects a predicate if it preserves and reflects it.\<close>

abbreviation enc_respects_pred :: "(('procS, 'procT) Proc \<Rightarrow> bool) \<Rightarrow> bool" where
  "enc_respects_pred Pred \<equiv> enc_preserves_pred Pred \<and> enc_reflects_pred Pred"

abbreviation enc_respects_binary_pred
    :: "(('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> bool"
  where
  "enc_respects_binary_pred Pred \<equiv>
   enc_preserves_binary_pred Pred \<and> enc_reflects_binary_pred Pred"

end

text \<open>To compare source terms and target terms w.r.t. their barbs or observables we assume that
        each languages defines its own predicate for the existence of barbs.\<close>

locale encoding_wrt_barbs =
  encoding Source Target Enc
  for Source :: "'procS processCalculus"
  and Target :: "'procT processCalculus"
  and Enc    :: "'procS \<Rightarrow> 'procT" +
  fixes SWB :: "('procS, 'barbs) calculusWithBarbs"
    and TWB :: "('procT, 'barbs) calculusWithBarbs"
  assumes calS: "calculusWithBarbs.Calculus SWB = Source"
      and calT: "calculusWithBarbs.Calculus TWB = Target"
begin

lemma STCalWB_STCal:
  shows "Calculus (STCalWB SWB TWB) = STCal Source Target"
      unfolding STCalWB_def using calS calT
    by auto

text \<open>We say a term P of Proc has some barbs a if either P is a source term that has barb a or P
        is a target term that has the barb b. For simplicity we assume that the sets of barbs is
        large enough to contain all barbs of the source terms, the target terms, and all barbs they
        might have in common.\<close>

abbreviation hasBarbST
    :: "('procS, 'procT) Proc \<Rightarrow> 'barbs \<Rightarrow> bool" ("_\<down>._" [70, 70] 80)
  where
  "P\<down>.a \<equiv> (\<exists>S. S \<in>S P \<and> S\<down><SWB>a) \<or> (\<exists>T. T \<in>T P \<and> T\<down><TWB>a)"

lemma STCalWB_hasBarbST:
  fixes P :: "('procS, 'procT) Proc"
    and a :: "'barbs"
  shows "P\<down><STCalWB SWB TWB>a = P\<down>.a"
    by (simp add: STCalWB_def)

lemma preservation_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes preservation: "rel_preserves_barbs Rel (STCalWB SWB TWB)"
      and rel:          "(P, Q) \<in> Rel"
      and barb:         "P\<down>.a"
  shows "Q\<down>.a"
      using preservation rel barb
    by (simp add: STCalWB_def)

lemma reflection_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes reflection: "rel_reflects_barbs Rel (STCalWB SWB TWB)"
      and rel:        "(P, Q) \<in> Rel"
      and barb:       "Q\<down>.a"
  shows "P\<down>.a"
      using reflection rel barb
    by (simp add: STCalWB_def)

lemma respection_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes respection: "rel_respects_barbs Rel (STCalWB SWB TWB)"
      and rel:        "(P, Q) \<in> Rel"
  shows "P\<down>.a = Q\<down>.a"
      using preservation_of_barbs_in_barbed_encoding[where Rel="Rel" and P="P" and Q="Q" and a="a"]
            reflection_of_barbs_in_barbed_encoding[where Rel="Rel" and P="P" and Q="Q" and a="a"]
            respection rel
    by blast

text \<open>A term P of Proc reaches a barb a if either P is a source term that reaches a or P is a
        target term that reaches a.\<close>

abbreviation reachesBarbST
    :: "('procS, 'procT) Proc \<Rightarrow> 'barbs \<Rightarrow> bool" ("_\<Down>._" [70, 70] 80)
  where
  "P\<Down>.a \<equiv> (\<exists>S. S \<in>S P \<and> S\<Down><SWB>a) \<or> (\<exists>T. T \<in>T P \<and> T\<Down><TWB>a)"

lemma STCalWB_reachesBarbST:
  fixes P :: "('procS, 'procT) Proc"
    and a :: "'barbs"
  shows "P\<Down><STCalWB SWB TWB>a = P\<Down>.a"
proof -
  have "\<forall>S. SourceTerm S\<Down><STCalWB SWB TWB>a = SourceTerm S\<Down>.a"
      using STCal_steps(1)
    by (auto simp add: STCalWB_def calS calT)
  moreover have "\<forall>T. TargetTerm T\<Down><STCalWB SWB TWB>a = TargetTerm T\<Down>.a"
      using STCal_steps(2)
    by (auto simp add: STCalWB_def calS calT)
  ultimately show "P\<Down><STCalWB SWB TWB>a = P\<Down>.a"
    by (cases P, simp+)
qed

lemma weak_preservation_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes preservation: "rel_weakly_preserves_barbs Rel (STCalWB SWB TWB)"
      and rel:          "(P, Q) \<in> Rel"
      and barb:         "P\<Down>.a"
  shows "Q\<Down>.a"
proof -
  from barb have "P\<Down><STCalWB SWB TWB>a"
    by (simp add: STCalWB_reachesBarbST)
  with preservation rel have "Q\<Down><STCalWB SWB TWB>a"
    by blast
  thus "Q\<Down>.a"
    by (simp add: STCalWB_reachesBarbST)
qed

lemma weak_reflection_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes reflection: "rel_weakly_reflects_barbs Rel (STCalWB SWB TWB)"
      and rel:        "(P, Q) \<in> Rel"
      and barb:       "Q\<Down>.a"
  shows "P\<Down>.a"
proof -
  from barb have "Q\<Down><STCalWB SWB TWB>a"
    by (simp add: STCalWB_reachesBarbST)
  with reflection rel have "P\<Down><STCalWB SWB TWB>a"
    by blast
  thus "P\<Down>.a"
    by (simp add: STCalWB_reachesBarbST)
qed

lemma weak_respection_of_barbs_in_barbed_encoding:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and P Q :: "('procS, 'procT) Proc"
    and a   :: "'barbs"
  assumes respection: "rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
      and rel:        "(P, Q) \<in> Rel"
  shows "P\<Down>.a = Q\<Down>.a"
proof (rule iffI)
  assume "P\<Down>.a"
  with respection rel show "Q\<Down>.a"
      using weak_preservation_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
next
  assume "Q\<Down>.a"
  with respection rel show "P\<Down>.a"
      using weak_reflection_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
qed

end

end
