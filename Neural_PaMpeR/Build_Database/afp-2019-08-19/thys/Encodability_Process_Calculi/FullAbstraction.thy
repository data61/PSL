theory FullAbstraction
  imports SourceTargetRelation
begin

section \<open>Full Abstraction\<close>

text \<open>An encoding is fully abstract w.r.t. some source term relation SRel and some target term
        relation TRel if two source terms S1 and S2 form a pair (S1, S2) in SRel iff their literal
        translations form a pair (enc S1, enc S2) in TRel.\<close>

abbreviation (in encoding) fully_abstract
    :: "('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set \<Rightarrow> bool"
  where
  "fully_abstract SRel TRel \<equiv> \<forall>S1 S2. (S1, S2) \<in> SRel \<longleftrightarrow> (\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"

subsection \<open>Trivial Full Abstraction Results\<close>

text \<open>We start with some trivial full abstraction results. Each injective encoding is fully
        abstract w.r.t. to the identity relation on the source and the identity relation on the
        target.\<close>

lemma (in encoding) inj_enc_is_fully_abstract_wrt_identities:
  assumes injectivity: "\<forall>S1 S2. \<lbrakk>S1\<rbrakk> = \<lbrakk>S2\<rbrakk> \<longrightarrow> S1 = S2"
  shows "fully_abstract {(S1, S2). S1 = S2} {(T1, T2). T1 = T2}"
    by (auto simp add: injectivity)

text \<open>Each encoding is fully abstract w.r.t. the empty relation on the source and the target.\<close>

lemma (in encoding) fully_abstract_wrt_empty_relation:
  shows "fully_abstract {} {}"
    by auto

text \<open>Similarly, each encoding is fully abstract w.r.t. the all-relation on the source and the
        target.\<close>

lemma (in encoding) fully_abstract_wrt_all_relation:
  shows "fully_abstract {(S1, S2). True} {(T1, T2). True}"
    by auto

text \<open>If the encoding is injective then for each source term relation RelS there exists a target
        term relation RelT such that the encoding is fully abstract w.r.t. RelS and RelT.\<close>

lemma (in encoding) fully_abstract_wrt_source_relation:
  fixes RelS :: "('procS \<times> 'procS) set"
  assumes injectivity: "\<forall>S1 S2. \<lbrakk>S1\<rbrakk> = \<lbrakk>S2\<rbrakk> \<longrightarrow> S1 = S2"
  shows "\<exists>RelT. fully_abstract RelS RelT"
proof -
  define RelT where "RelT = {(T1, T2). \<exists>S1 S2. (S1, S2) \<in> RelS \<and> T1 = \<lbrakk>S1\<rbrakk> \<and> T2 = \<lbrakk>S2\<rbrakk>}"
  with injectivity have "fully_abstract RelS RelT"
    by blast
  thus "\<exists>RelT. fully_abstract RelS RelT"
    by blast
qed

text \<open>If all source terms that are translated to the same target term are related by a trans
        source term relation RelS, then there exists a target term relation RelT such that the
        encoding is fully abstract w.r.t. RelS and RelT.\<close>

lemma (in encoding) fully_abstract_wrt_trans_source_relation:
  fixes RelS :: "('procS \<times> 'procS) set"
  assumes encRelS: "\<forall>S1 S2. \<lbrakk>S1\<rbrakk> = \<lbrakk>S2\<rbrakk> \<longrightarrow> (S1, S2) \<in> RelS"
      and transS:  "trans RelS"
  shows "\<exists>RelT. fully_abstract RelS RelT"
proof -
  define RelT where "RelT = {(T1, T2). \<exists>S1 S2. (S1, S2) \<in> RelS \<and> T1 = \<lbrakk>S1\<rbrakk> \<and> T2 = \<lbrakk>S2\<rbrakk>}"
  have "fully_abstract RelS RelT"
  proof auto
    fix S1 S2
    assume "(S1, S2) \<in> RelS"
    with RelT_def show "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> RelT"
      by blast
  next
    fix S1 S2
    assume "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> RelT"
    with RelT_def obtain S1' S2' where A1: "(S1', S2') \<in> RelS" and A2: "\<lbrakk>S1\<rbrakk> = \<lbrakk>S1'\<rbrakk>"
                               and A3: "\<lbrakk>S2\<rbrakk> = \<lbrakk>S2'\<rbrakk>"
      by blast
    from A2 encRelS have "(S1, S1') \<in> RelS"
      by simp
    from this A1 transS have "(S1, S2') \<in> RelS"
        unfolding trans_def
      by blast
    moreover from A3 encRelS have "(S2', S2) \<in> RelS"
      by simp
    ultimately show "(S1, S2) \<in> RelS"
        using transS
        unfolding trans_def
      by blast
  qed
  thus "\<exists>RelT. fully_abstract RelS RelT"
    by blast
qed

lemma (in encoding) fully_abstract_wrt_trans_closure_of_source_relation:
  fixes RelS :: "('procS \<times> 'procS) set"
  assumes encRelS: "\<forall>S1 S2. \<lbrakk>S1\<rbrakk> = \<lbrakk>S2\<rbrakk> \<longrightarrow> (S1, S2) \<in> RelS\<^sup>+"
  shows "\<exists>RelT. fully_abstract (RelS\<^sup>+) RelT"
      using encRelS trans_trancl[of RelS]
            fully_abstract_wrt_trans_source_relation[where RelS="RelS\<^sup>+"]
    by blast

text \<open>For every encoding and every target term relation RelT there exists a source term relation
        RelS such that the encoding is fully abstract w.r.t. RelS and RelT.\<close>

lemma (in encoding) fully_abstract_wrt_target_relation:
  fixes RelT :: "('procT \<times> 'procT) set"
  shows "\<exists>RelS. fully_abstract RelS RelT"
proof -
  define RelS where "RelS = {(S1, S2). (\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> RelT}"
  hence "fully_abstract RelS RelT"
    by simp
  thus "\<exists>RelS. fully_abstract RelS RelT"
    by blast
qed

subsection \<open>Fully Abstract Encodings\<close>

text \<open>Thus, as long as we can choose one of the two relations, full abstraction is trivial. For
        fixed source and target term relations encodings are not trivially fully abstract. For all
        encodings and relations SRel and TRel we can construct a relation on the disjunctive union
        of source and target terms, whose reduction to source terms is SRel and whose reduction to
        target terms is TRel. But full abstraction ensures that each trans relation that
        relates source terms and their literal translations in both directions includes SRel iff it
        includes TRel restricted to translated source terms.\<close>

lemma (in encoding) full_abstraction_and_trans_relation_contains_SRel_impl_TRel:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and encR:    "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and srel:    "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
      and trans:   "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
  shows "\<forall>S1 S2. (\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel \<longleftrightarrow> (TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
proof auto
  fix S1 S2
  define Rel' where "Rel' = Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
  hence "(TargetTerm (\<lbrakk>S1\<rbrakk>), SourceTerm S1) \<in> Rel'"
    by simp
  moreover assume "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"
  with fullAbs have "(S1, S2) \<in> SRel"
    by simp
  with srel Rel'_def have "(SourceTerm S1, SourceTerm S2) \<in> Rel'"
    by simp
  moreover from encR Rel'_def have "(SourceTerm S2, TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel'"
    by simp
  ultimately show "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
      using trans Rel'_def
      unfolding trans_def
    by blast
next
  fix S1 S2
  define Rel' where "Rel' = Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
  from encR Rel'_def have "(SourceTerm S1, TargetTerm (\<lbrakk>S1\<rbrakk>)) \<in> Rel'"
    by simp
  moreover assume "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
  with Rel'_def have "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel'"
    by simp
  moreover from Rel'_def have "(TargetTerm (\<lbrakk>S2\<rbrakk>), SourceTerm S2) \<in> Rel'"
    by simp
  ultimately have "(SourceTerm S1, SourceTerm S2) \<in> Rel"
      using trans Rel'_def
      unfolding trans_def
    by blast
  with srel have "(S1, S2) \<in> SRel"
    by simp
  with fullAbs show "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"
    by simp
qed

lemma (in encoding) full_abstraction_and_trans_relation_contains_TRel_impl_SRel:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and encR:    "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trel:    "\<forall>S1 S2. (\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel \<longleftrightarrow> (TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
      and trans:   "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
  shows "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
proof auto
  fix S1 S2
  define Rel' where "Rel' = Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
  from encR Rel'_def have "(SourceTerm S1, TargetTerm (\<lbrakk>S1\<rbrakk>)) \<in> Rel'"
    by simp
  moreover assume "(S1, S2) \<in> SRel"
  with fullAbs have "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"
    by simp
  with trel Rel'_def have "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel'"
    by simp
  moreover from Rel'_def have "(TargetTerm (\<lbrakk>S2\<rbrakk>), SourceTerm S2) \<in> Rel'"
    by simp
  ultimately show "(SourceTerm S1, SourceTerm S2) \<in> Rel"
      using trans Rel'_def
      unfolding trans_def
    by blast
next
  fix S1 S2
  define Rel' where "Rel' = Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
  hence "(TargetTerm (\<lbrakk>S1\<rbrakk>), SourceTerm S1) \<in> Rel'"
    by simp
  moreover assume "(SourceTerm S1, SourceTerm S2) \<in> Rel"
  with Rel'_def have "(SourceTerm S1, SourceTerm S2) \<in> Rel'"
    by simp
  moreover from encR Rel'_def have "(SourceTerm S2, TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel'"
    by simp
  ultimately have "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
      using trans Rel'_def
      unfolding trans_def
    by blast
  with trel have "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"
    by simp
  with fullAbs show "(S1, S2) \<in> SRel"
    by simp
qed

lemma (in encoding) full_abstraction_impl_trans_relation_contains_SRel_iff_TRel:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and encR:    "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trans:   "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
  shows "(\<forall>S1 S2. (\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel \<longleftrightarrow> (TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel)
         \<longleftrightarrow> (SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel})"
proof
  assume "\<forall>S1 S2. ((\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel) = ((TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel)"
  thus "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
      using assms full_abstraction_and_trans_relation_contains_TRel_impl_SRel[where
            SRel="SRel" and TRel="TRel"]
    by blast
next
  assume "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
  thus "\<forall>S1 S2. (\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel \<longleftrightarrow> (TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
      using assms full_abstraction_and_trans_relation_contains_SRel_impl_TRel[where
            SRel="SRel" and TRel="TRel"]
    by blast
qed

lemma (in encoding) full_abstraction_impl_trans_relation_contains_SRel_iff_TRel_encRL:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and encR:    "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and encL:    "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
      and trans:   "trans Rel"
  shows "(\<forall>S1 S2. (\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel \<longleftrightarrow> (TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel)
         \<longleftrightarrow> (SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel})"
proof -
  from encL have "Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} = Rel"
    by auto
  with fullAbs encR trans show ?thesis
      using full_abstraction_impl_trans_relation_contains_SRel_iff_TRel[where Rel="Rel"
            and SRel="SRel" and TRel="TRel"]
    by simp
qed

text \<open>Full abstraction ensures that SRel and TRel satisfy the same basic properties that can be
        defined on their pairs. In particular:
        (1) SRel is refl iff TRel reduced to translated source terms is refl
        (2) if the encoding is surjective then SRel is refl iff TRel is refl
        (3) SRel is sym iff TRel reduced to translated source terms is sym
        (4) SRel is trans iff TRel reduced to translated source terms is trans\<close>

lemma (in encoding) full_abstraction_impl_SRel_iff_TRel_is_refl:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
  shows "refl SRel \<longleftrightarrow> (\<forall>S. (\<lbrakk>S\<rbrakk>, \<lbrakk>S\<rbrakk>) \<in> TRel)"
      unfolding refl_on_def
    by (simp add: fullAbs)

lemma (in encoding) full_abstraction_and_surjectivity_impl_SRel_iff_TRel_is_refl:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and surj:    "\<forall>T. \<exists>S. T = \<lbrakk>S\<rbrakk>"
  shows "refl SRel \<longleftrightarrow> refl TRel"
proof
  assume reflS: "refl SRel"
  show "refl TRel"
    unfolding refl_on_def
  proof auto
    fix T
    from surj obtain S where "T = \<lbrakk>S\<rbrakk>"
      by blast
    moreover from reflS have "(S, S) \<in> SRel"
        unfolding refl_on_def
      by simp
    with fullAbs have "(\<lbrakk>S\<rbrakk>, \<lbrakk>S\<rbrakk>) \<in> TRel"
      by simp
    ultimately show "(T, T) \<in> TRel"
      by simp
  qed
next
  assume "refl TRel"
  with fullAbs show "refl SRel"
      unfolding refl_on_def
    by simp
qed

lemma (in encoding) full_abstraction_impl_SRel_iff_TRel_is_sym:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
  shows "sym SRel \<longleftrightarrow> sym {(T1, T2). \<exists>S1 S2. T1 = \<lbrakk>S1\<rbrakk> \<and> T2 = \<lbrakk>S2\<rbrakk> \<and> (T1, T2) \<in> TRel}"
      unfolding sym_def
    by (simp add: fullAbs, blast)

lemma (in encoding) full_abstraction_and_surjectivity_impl_SRel_iff_TRel_is_sym:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and surj:    "\<forall>T. \<exists>S. T = \<lbrakk>S\<rbrakk>"
  shows "sym SRel \<longleftrightarrow> sym TRel"
      using fullAbs surj
            full_abstraction_impl_SRel_iff_TRel_is_sym[where SRel="SRel" and TRel="TRel"]
    by auto

lemma (in encoding) full_abstraction_impl_SRel_iff_TRel_is_trans:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
  shows "trans SRel \<longleftrightarrow> trans {(T1, T2). \<exists>S1 S2. T1 = \<lbrakk>S1\<rbrakk> \<and> T2 = \<lbrakk>S2\<rbrakk> \<and> (T1, T2) \<in> TRel}"
      unfolding trans_def
    by (simp add: fullAbs, blast)

lemma (in encoding) full_abstraction_and_surjectivity_impl_SRel_iff_TRel_is_trans:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and surj:    "\<forall>T. \<exists>S. T = \<lbrakk>S\<rbrakk>"
  shows "trans SRel \<longleftrightarrow> trans TRel"
      using fullAbs surj
            full_abstraction_impl_SRel_iff_TRel_is_trans[where SRel="SRel" and TRel="TRel"]
    by auto

text \<open>Similarly, a fully abstract encoding that respects a predicate ensures the this predicate
        is preserved, reflected, or respected by SRel iff it is preserved, reflected, or respected
        by TRel.\<close>

lemma (in encoding) full_abstraction_and_enc_respects_pred_impl_SRel_iff_TRel_preserve:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  assumes fullAbs: "fully_abstract SRel TRel"
      and encP:    "enc_respects_pred Pred"
  shows "rel_preserves_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred
         \<longleftrightarrow> rel_preserves_pred {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
proof
  assume presS: "rel_preserves_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred"
  show "rel_preserves_pred {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
  proof clarify
    fix SP SQ
    assume "Pred (TargetTerm (\<lbrakk>SP\<rbrakk>))"
    with encP have "Pred (SourceTerm SP)"
      by simp
    moreover assume "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    with fullAbs have "(SP, SQ) \<in> SRel"
      by simp
    ultimately have "Pred (SourceTerm SQ)"
        using presS
      by blast
    with encP show "Pred (TargetTerm (\<lbrakk>SQ\<rbrakk>))"
      by simp
  qed
next
  assume presT:
    "rel_preserves_pred {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
  show "rel_preserves_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred"
  proof clarify
    fix SP SQ
    assume "Pred (SourceTerm SP)"
    with encP have "Pred (TargetTerm (\<lbrakk>SP\<rbrakk>))"
      by simp
    moreover assume "(SP, SQ) \<in> SRel"
    with fullAbs have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
      by simp
    ultimately have "Pred (TargetTerm (\<lbrakk>SQ\<rbrakk>))"
        using presT
      by blast
    with encP show "Pred (SourceTerm SQ)"
      by simp
  qed
qed

lemma (in encoding) full_abstraction_and_enc_respects_binary_pred_impl_SRel_iff_TRel_preserve:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  assumes fullAbs: "fully_abstract SRel TRel"
      and encP:    "enc_respects_binary_pred Pred"
  shows "rel_preserves_binary_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred
         \<longleftrightarrow> rel_preserves_binary_pred
             {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
proof
  assume presS:
    "rel_preserves_binary_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred"
  show "rel_preserves_binary_pred
        {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
  proof clarify
    fix x SP SQ
    assume "Pred (TargetTerm (\<lbrakk>SP\<rbrakk>)) x"
    with encP have "Pred (SourceTerm SP) x"
      by simp
    moreover assume "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    with fullAbs have "(SP, SQ) \<in> SRel"
      by simp
    ultimately have "Pred (SourceTerm SQ) x"
        using presS
      by blast
    with encP show "Pred (TargetTerm (\<lbrakk>SQ\<rbrakk>)) x"
      by simp
  qed
next
  assume presT:
    "rel_preserves_binary_pred {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
  show "rel_preserves_binary_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred"
  proof clarify
    fix x SP SQ
    assume "Pred (SourceTerm SP) x"
    with encP have "Pred (TargetTerm (\<lbrakk>SP\<rbrakk>)) x"
      by simp
    moreover assume "(SP, SQ) \<in> SRel"
    with fullAbs have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
      by simp
    ultimately have "Pred (TargetTerm (\<lbrakk>SQ\<rbrakk>)) x"
        using presT
      by blast
    with encP show "Pred (SourceTerm SQ) x"
      by simp
  qed
qed

lemma (in encoding) full_abstraction_and_enc_respects_pred_impl_SRel_iff_TRel_reflects:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  assumes fullAbs: "fully_abstract SRel TRel"
      and encP:    "enc_respects_pred Pred"
  shows "rel_reflects_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred
         \<longleftrightarrow> rel_reflects_pred {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
proof
  assume reflS: "rel_reflects_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred"
  show "rel_reflects_pred {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
  proof clarify
    fix SP SQ
    assume "Pred (TargetTerm (\<lbrakk>SQ\<rbrakk>))"
    with encP have "Pred (SourceTerm SQ)"
      by simp
    moreover assume "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    with fullAbs have "(SP, SQ) \<in> SRel"
      by simp
    ultimately have "Pred (SourceTerm SP)"
        using reflS
      by blast
    with encP show "Pred (TargetTerm (\<lbrakk>SP\<rbrakk>))"
      by simp
  qed
next
  assume reflT:
    "rel_reflects_pred {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
  show "rel_reflects_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred"
  proof clarify
    fix SP SQ
    assume "Pred (SourceTerm SQ)"
    with encP have "Pred (TargetTerm (\<lbrakk>SQ\<rbrakk>))"
      by simp
    moreover assume "(SP, SQ) \<in> SRel"
    with fullAbs have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
      by simp
    ultimately have "Pred (TargetTerm (\<lbrakk>SP\<rbrakk>))"
        using reflT
      by blast
    with encP show "Pred (SourceTerm SP)"
      by simp
  qed
qed

lemma (in encoding) full_abstraction_and_enc_respects_binary_pred_impl_SRel_iff_TRel_reflects:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  assumes fullAbs: "fully_abstract SRel TRel"
      and encP:    "enc_respects_binary_pred Pred"
  shows "rel_reflects_binary_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred
         \<longleftrightarrow> rel_reflects_binary_pred
             {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
proof
  assume reflS:
    "rel_reflects_binary_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred"
  show "rel_reflects_binary_pred
        {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
  proof clarify
    fix x SP SQ
    assume "Pred (TargetTerm (\<lbrakk>SQ\<rbrakk>)) x"
    with encP have "Pred (SourceTerm SQ) x"
      by simp
    moreover assume "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    with fullAbs have "(SP, SQ) \<in> SRel"
      by simp
    ultimately have "Pred (SourceTerm SP) x"
        using reflS
      by blast
    with encP show "Pred (TargetTerm (\<lbrakk>SP\<rbrakk>)) x"
      by simp
  qed
next
  assume reflT:
    "rel_reflects_binary_pred {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
  show "rel_reflects_binary_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred"
  proof clarify
    fix x SP SQ
    assume "Pred (SourceTerm SQ) x"
    with encP have "Pred (TargetTerm (\<lbrakk>SQ\<rbrakk>)) x"
      by simp
    moreover assume "(SP, SQ) \<in> SRel"
    with fullAbs have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
      by simp
    ultimately have "Pred (TargetTerm (\<lbrakk>SP\<rbrakk>)) x"
        using reflT
      by blast
    with encP show "Pred (SourceTerm SP) x"
      by simp
  qed
qed

lemma (in encoding) full_abstraction_and_enc_respects_pred_impl_SRel_iff_TRel_respects:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  assumes fullAbs: "fully_abstract SRel TRel"
      and encP:    "enc_respects_pred Pred"
  shows "rel_respects_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred
         \<longleftrightarrow> rel_respects_pred {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
      using assms full_abstraction_and_enc_respects_pred_impl_SRel_iff_TRel_preserve[where
                    SRel="SRel" and TRel="TRel" and Pred="Pred"]
            full_abstraction_and_enc_respects_pred_impl_SRel_iff_TRel_reflects[where
              SRel="SRel" and TRel="TRel" and Pred="Pred"]
    by auto

lemma (in encoding) full_abstraction_and_enc_respects_binary_pred_impl_SRel_iff_TRel_respects:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  assumes fullAbs: "fully_abstract SRel TRel"
      and encP:    "enc_respects_binary_pred Pred"
  shows "rel_respects_binary_pred {(P, Q). \<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel} Pred
         \<longleftrightarrow> rel_respects_binary_pred
             {(P, Q). \<exists>SP SQ. \<lbrakk>SP\<rbrakk> \<in>T P \<and> \<lbrakk>SQ\<rbrakk> \<in>T Q \<and> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel} Pred"
      using assms full_abstraction_and_enc_respects_binary_pred_impl_SRel_iff_TRel_preserve[where
                    SRel="SRel" and TRel="TRel" and Pred="Pred"]
            full_abstraction_and_enc_respects_binary_pred_impl_SRel_iff_TRel_reflects[where
              SRel="SRel" and TRel="TRel" and Pred="Pred"]
    by auto

subsection \<open>Full Abstraction w.r.t. Preorders\<close>

text \<open>If there however exists a trans relation Rel that relates source terms and their
        literal translations in both directions, then the encoding is fully abstract with respect
        to the reduction of Rel to source terms and the reduction of Rel to target terms.\<close>

lemma (in encoding) trans_source_target_relation_impl_full_abstraction:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes enc:   "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                  \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
      and trans: "trans Rel"
  shows "fully_abstract {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
          {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
proof auto
  fix S1 S2
  assume "(SourceTerm S1, SourceTerm S2) \<in> Rel"
  with enc trans show "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
      unfolding trans_def
    by blast
next
  fix S1 S2
  assume "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
  with enc trans show "(SourceTerm S1, SourceTerm S2) \<in> Rel"
      unfolding trans_def
    by blast
qed

lemma (in encoding) source_target_relation_impl_full_abstraction_wrt_trans_closures:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes enc: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
  shows "fully_abstract {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel\<^sup>+}
          {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel\<^sup>+}"
proof auto
  fix S1 S2
  from enc have "(TargetTerm (\<lbrakk>S1\<rbrakk>), SourceTerm S1) \<in> Rel\<^sup>+"
    by blast
  moreover assume "(SourceTerm S1, SourceTerm S2) \<in> Rel\<^sup>+"
  ultimately have "(TargetTerm (\<lbrakk>S1\<rbrakk>), SourceTerm S2) \<in> Rel\<^sup>+"
    by simp
  moreover from enc have "(SourceTerm S2, TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel\<^sup>+"
    by blast
  ultimately show "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel\<^sup>+"
    by simp
next
  fix S1 S2
  from enc have "(SourceTerm S1, TargetTerm (\<lbrakk>S1\<rbrakk>)) \<in> Rel\<^sup>+"
    by blast
  moreover assume "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel\<^sup>+"
  ultimately have "(SourceTerm S1, TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel\<^sup>+"
    by simp
  moreover from enc have "(TargetTerm (\<lbrakk>S2\<rbrakk>), SourceTerm S2) \<in> Rel\<^sup>+"
    by blast
  ultimately show "(SourceTerm S1, SourceTerm S2) \<in> Rel\<^sup>+"
    by simp
qed

lemma (in encoding) quasi_trans_source_target_relation_impl_full_abstraction:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes enc:   "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                  \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
      and srel:  "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
      and trel:  "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      and trans: "\<forall>P Q R. (P, Q) \<in> Rel \<and> (Q, R) \<in> Rel \<and> ((P \<in> ProcS \<and> Q \<in> ProcT)
                  \<or> (P \<in> ProcT \<and> Q \<in> ProcS)) \<longrightarrow> (P, R) \<in> Rel"
  shows "fully_abstract SRel TRel"
proof auto
  fix S1 S2
  from enc have "(TargetTerm (\<lbrakk>S1\<rbrakk>), SourceTerm S1) \<in> Rel"
    by simp
  moreover assume "(S1, S2) \<in> SRel"
  with srel have "(SourceTerm S1, SourceTerm S2) \<in> Rel"
    by simp
  ultimately have "(TargetTerm (\<lbrakk>S1\<rbrakk>), SourceTerm S2) \<in> Rel"
      using trans
    by blast
  moreover from enc have "(SourceTerm S2, TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
    by simp
  ultimately have "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
      using trans
    by blast
  with trel show "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"
    by simp
next
  fix S1 S2
  from enc have "(SourceTerm S1, TargetTerm (\<lbrakk>S1\<rbrakk>)) \<in> Rel"
    by simp
  moreover assume "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"
  with trel have "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
    by simp
  ultimately have "(SourceTerm S1, TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
      using trans
    by blast
  moreover from enc have "(TargetTerm (\<lbrakk>S2\<rbrakk>), SourceTerm S2) \<in> Rel"
    by simp
  ultimately have "(SourceTerm S1, SourceTerm S2) \<in> Rel"
      using trans
    by blast
  with srel show "(S1, S2) \<in> SRel"
    by simp
qed

text \<open>If an encoding is fully abstract w.r.t. SRel and TRel, then we can conclude from a pair in
        indRelRTPO or indRelSTEQ on a pair in TRel and SRel.\<close>

lemma (in encoding) full_abstraction_impl_indRelRSTPO_to_SRel_and_TRel:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and P Q  :: "('procS, 'procT) Proc"
  assumes fullAbs: "fully_abstract SRel TRel"
      and rel:     "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q"
  shows "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel\<^sup>+"
    and "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel\<^sup>*"
proof -
  have fullAbsT: "\<forall>S1 S2. (S1, S2) \<in> SRel\<^sup>+ \<longrightarrow> (\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel\<^sup>+"
  proof clarify
    fix S1 S2
    assume "(S1, S2) \<in> SRel\<^sup>+"
    thus "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel\<^sup>+"
    proof induct
      fix S2
      assume "(S1, S2) \<in> SRel"
      with fullAbs show "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel\<^sup>+"
        by simp
    next
      case (step S2 S3)
      assume "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel\<^sup>+"
      moreover assume "(S2, S3) \<in> SRel"
      with fullAbs have "(\<lbrakk>S2\<rbrakk>, \<lbrakk>S3\<rbrakk>) \<in> TRel\<^sup>+"
        by simp
      ultimately show "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S3\<rbrakk>) \<in> TRel\<^sup>+"
        by simp
    qed
  qed
  with rel show "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel\<^sup>+"
      using indRelRSTPO_to_SRel_and_TRel(1)[where SRel="SRel" and TRel="TRel"]
    by simp
  show "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel\<^sup>*"
  proof clarify
    fix SP TQ
    assume "SP \<in>S P" and "TQ \<in>T Q"
    with rel obtain S where A1: "(SP, S) \<in> SRel\<^sup>*"
                        and A2: "(\<lbrakk>S\<rbrakk>, TQ) \<in> TRel\<^sup>*"
        using indRelRSTPO_to_SRel_and_TRel(2)[where SRel="SRel" and TRel="TRel"]
      by blast
    from A1 have "SP = S \<or> (SP, S) \<in> SRel\<^sup>+"
        using rtrancl_eq_or_trancl[of SP S SRel]
      by blast
    with fullAbsT have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>*"
      by fast
    from this A2 show "(\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel\<^sup>*"
      by simp
  qed
qed

lemma (in encoding) full_abstraction_wrt_preorders_impl_indRelSTEQ_to_SRel_and_TRel:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and P Q  :: "('procS, 'procT) Proc"
  assumes fA:     "fully_abstract SRel TRel"
      and transT: "trans TRel"
      and reflS:  "refl SRel"
      and rel:    "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
  shows "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> (SP, SQ) \<in> SRel"
    and "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    and "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
    and "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    and "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel"
      using rel
proof induct
  case (encR S)
  show "\<forall>SP SQ. SP \<in>S SourceTerm S \<and> SQ \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> (SP, SQ) \<in> SRel"
   and "\<forall>SP SQ. SP \<in>S SourceTerm S \<and> SQ \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
   and "\<forall>TP SQ. TP \<in>T SourceTerm S \<and> SQ \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
   and "\<forall>TP TQ. TP \<in>T SourceTerm S \<and> TQ \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> (TP, TQ) \<in> TRel"
    by simp+
  from reflS fA show "\<forall>SP TQ. SP \<in>S SourceTerm S \<and> TQ \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
      unfolding refl_on_def
    by simp
next
  case (encL S)
  show "\<forall>SP SQ. SP \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<and> SQ \<in>S SourceTerm S \<longrightarrow> (SP, SQ) \<in> SRel"
   and "\<forall>SP SQ. SP \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<and> SQ \<in>S SourceTerm S \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
   and "\<forall>SP TQ. SP \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TQ \<in>T SourceTerm S \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
   and "\<forall>TP TQ. TP \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TQ \<in>T SourceTerm S \<longrightarrow> (TP, TQ) \<in> TRel"
    by simp+
  with reflS fA show "\<forall>TP SQ. TP \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<and> SQ \<in>S SourceTerm S \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
      unfolding refl_on_def
    by simp
next
  case (source S1 S2)
  show "\<forall>SP TQ. SP \<in>S SourceTerm S1 \<and> TQ \<in>T SourceTerm S2 \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
   and "\<forall>TP SQ. TP \<in>T SourceTerm S1 \<and> SQ \<in>S SourceTerm S2 \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
   and "\<forall>TP TQ. TP \<in>T SourceTerm S1 \<and> TQ \<in>T SourceTerm S2 \<longrightarrow> (TP, TQ) \<in> TRel"
    by simp+
  assume "(S1, S2) \<in> SRel"
  thus "\<forall>SP SQ. SP \<in>S SourceTerm S1 \<and> SQ \<in>S SourceTerm S2 \<longrightarrow> (SP, SQ) \<in> SRel"
    by simp
  with fA show "\<forall>SP SQ. SP \<in>S SourceTerm S1 \<and> SQ \<in>S SourceTerm S2 \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    by simp
next
  case (target T1 T2)
  show "\<forall>SP SQ. SP \<in>S TargetTerm T1 \<and> SQ \<in>S TargetTerm T2 \<longrightarrow> (SP, SQ) \<in> SRel"
   and "\<forall>SP SQ. SP \<in>S TargetTerm T1 \<and> SQ \<in>S TargetTerm T2 \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
   and "\<forall>SP TQ. SP \<in>S TargetTerm T1 \<and> TQ \<in>T TargetTerm T2 \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
   and "\<forall>TP SQ. TP \<in>T TargetTerm T1 \<and> SQ \<in>S TargetTerm T2 \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    by simp+
  assume "(T1, T2) \<in> TRel"
  thus "\<forall>TP TQ. TP \<in>T TargetTerm T1 \<and> TQ \<in>T TargetTerm T2 \<longrightarrow> (TP, TQ) \<in> TRel"
    by simp
next
  case (trans P Q R)
  assume A1: "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
     and A2: "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
     and A3: "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
     and A4: "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel"
     and A5: "\<forall>SQ SR. SQ \<in>S Q \<and> SR \<in>S R \<longrightarrow> (\<lbrakk>SQ\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
     and A6: "\<forall>SQ TR. SQ \<in>S Q \<and> TR \<in>T R \<longrightarrow> (\<lbrakk>SQ\<rbrakk>, TR) \<in> TRel"
     and A7: "\<forall>TQ SR. TQ \<in>T Q \<and> SR \<in>S R \<longrightarrow> (TQ, \<lbrakk>SR\<rbrakk>) \<in> TRel"
     and A8: "\<forall>TQ TR. TQ \<in>T Q \<and> TR \<in>T R \<longrightarrow> (TQ, TR) \<in> TRel"
  show "\<forall>SP SR. SP \<in>S P \<and> SR \<in>S R \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
  proof clarify
    fix SP SR
    assume A9: "SP \<in>S P" and A10: "SR \<in>S R"
    show "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
    proof (cases Q)
      case (SourceTerm SQ)
      assume A11: "SQ \<in>S Q"
      with A1 A9 have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
        by blast
      moreover from A5 A10 A11 have "(\<lbrakk>SQ\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
        by blast
      ultimately show "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          using transT
          unfolding trans_def
        by blast
    next
      case (TargetTerm TQ)
      assume A11: "TQ \<in>T Q"
      with A2 A9 have "(\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
        by blast
      moreover from A7 A10 A11 have "(TQ, \<lbrakk>SR\<rbrakk>) \<in> TRel"
        by blast
      ultimately show "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          using transT
          unfolding trans_def
        by blast
    qed
  qed
  with fA show "\<forall>SP SR. SP \<in>S P \<and> SR \<in>S R \<longrightarrow> (SP, SR) \<in> SRel"
    by simp
  show "\<forall>SP TR. SP \<in>S P \<and> TR \<in>T R \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TR) \<in> TRel"
  proof clarify
    fix SP TR
    assume A9: "SP \<in>S P" and A10: "TR \<in>T R"
    show "(\<lbrakk>SP\<rbrakk>, TR) \<in> TRel"
    proof (cases Q)
      case (SourceTerm SQ)
      assume A11: "SQ \<in>S Q"
      with A1 A9 have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
        by blast
      moreover from A6 A10 A11 have "(\<lbrakk>SQ\<rbrakk>, TR) \<in> TRel"
        by blast
      ultimately show "(\<lbrakk>SP\<rbrakk>, TR) \<in> TRel"
          using transT
          unfolding trans_def
        by blast
    next
      case (TargetTerm TQ)
      assume A11: "TQ \<in>T Q"
      with A2 A9 have "(\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
        by blast
      moreover from A8 A10 A11 have "(TQ, TR) \<in> TRel"
        by blast
      ultimately show "(\<lbrakk>SP\<rbrakk>, TR) \<in> TRel"
          using transT
          unfolding trans_def
        by blast
    qed
  qed
  show "\<forall>TP SR. TP \<in>T P \<and> SR \<in>S R \<longrightarrow> (TP, \<lbrakk>SR\<rbrakk>) \<in> TRel"
  proof clarify
    fix TP SR
    assume A9: "TP \<in>T P" and A10: "SR \<in>S R"
    show "(TP, \<lbrakk>SR\<rbrakk>) \<in> TRel"
    proof (cases Q)
      case (SourceTerm SQ)
      assume A11: "SQ \<in>S Q"
      with A3 A9 have "(TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
        by blast
      moreover from A5 A10 A11 have "(\<lbrakk>SQ\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
        by blast
      ultimately show "(TP, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          using transT
          unfolding trans_def
        by blast
    next
      case (TargetTerm TQ)
      assume A11: "TQ \<in>T Q"
      with A4 A9 have "(TP, TQ) \<in> TRel"
        by blast
      moreover from A7 A10 A11 have "(TQ, \<lbrakk>SR\<rbrakk>) \<in> TRel"
        by blast
      ultimately show "(TP, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          using transT
          unfolding trans_def
        by blast
    qed
  qed
  show "\<forall>TP TR. TP \<in>T P \<and> TR \<in>T R \<longrightarrow> (TP, TR) \<in> TRel"
  proof clarify
    fix TP TR
    assume A9: "TP \<in>T P" and A10: "TR \<in>T R"
    show "(TP, TR) \<in> TRel"
    proof (cases Q)
      case (SourceTerm SQ)
      assume A11: "SQ \<in>S Q"
      with A3 A9 have "(TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
        by blast
      moreover from A6 A10 A11 have "(\<lbrakk>SQ\<rbrakk>, TR) \<in> TRel"
        by blast
      ultimately show "(TP, TR) \<in> TRel"
          using transT
          unfolding trans_def
        by blast
    next
      case (TargetTerm TQ)
      assume A11: "TQ \<in>T Q"
      with A4 A9 have "(TP, TQ) \<in> TRel"
        by blast
      moreover from A8 A10 A11 have "(TQ, TR) \<in> TRel"
        by blast
      ultimately show "(TP, TR) \<in> TRel"
          using transT
          unfolding trans_def
        by blast
    qed
  qed
qed

text \<open>If an encoding is fully abstract w.r.t. a preorder SRel on the source and a trans
        relation TRel on the target, then there exists a trans relation, namely indRelSTEQ,
        that relates source terms and their literal translations in both direction such that its
        reductions to source terms is SRel and its reduction to target terms is TRel.\<close>

lemma (in encoding) full_abstraction_wrt_preorders_impl_trans_source_target_relation:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and reflS:   "refl SRel"
      and transT:  "trans TRel"
  shows "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                     \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                \<and> trans Rel"
proof -
  have "\<forall>S. SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>S\<rbrakk>)
        \<and> TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S"
      using indRelSTEQ.encR[where SRel="SRel" and TRel="TRel"]
            indRelSTEQ.encL[where SRel="SRel" and TRel="TRel"]
    by blast
  moreover have "SRel = {(S1, S2). SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2}"
  proof auto
    fix S1 S2
    assume "(S1, S2) \<in> SRel"
    thus "SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2"
      by (rule indRelSTEQ.source[where SRel="SRel" and TRel="TRel"])
  next
    fix S1 S2
    assume "SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2"
    with fullAbs reflS transT show "(S1, S2) \<in> SRel"
        using full_abstraction_wrt_preorders_impl_indRelSTEQ_to_SRel_and_TRel(1)[where SRel="SRel"
                and TRel="TRel"]
      by blast
  qed
  moreover have "TRel =  {(T1, T2). TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2}"
  proof auto
    fix T1 T2
    assume "(T1, T2) \<in> TRel"
    thus "TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2"
      by (rule indRelSTEQ.target[where SRel="SRel" and TRel="TRel"])
  next
    fix T1 T2
    assume "TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2"
    with fullAbs reflS transT show "(T1, T2) \<in> TRel"
        using full_abstraction_wrt_preorders_impl_indRelSTEQ_to_SRel_and_TRel(5)[where SRel="SRel"
                and TRel="TRel"]
      by blast
  qed
  moreover have "trans (indRelSTEQ SRel TRel)"
      using indRelSTEQ.trans[where SRel="SRel" and TRel="TRel"]
      unfolding trans_def
    by blast
  ultimately show ?thesis
    by blast
qed

text \<open>Thus an encoding is fully abstract w.r.t. a preorder SRel on the source and a trans
        relation TRel on the target iff there exists a trans relation that relates source
        terms and their literal translations in both directions and whose reduction to
        source/target terms is SRel/TRel.\<close>

theorem (in encoding) fully_abstract_wrt_preorders_iff_source_target_relation_is_trans:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  shows "(fully_abstract SRel TRel \<and> refl SRel \<and> trans TRel) =
         (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                      \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                \<and> trans Rel)"
proof (rule iffI)
  assume "fully_abstract SRel TRel \<and> refl SRel \<and> trans TRel"
  thus "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                \<and> trans Rel"
      using full_abstraction_wrt_preorders_impl_trans_source_target_relation[where SRel="SRel"
              and TRel="TRel"]
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                 \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                \<and> trans Rel"
  from this obtain Rel
    where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
      and A2: "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
      and A3: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}" and A4: "trans Rel"
    by blast
  hence "fully_abstract SRel TRel"
      using trans_source_target_relation_impl_full_abstraction[where Rel="Rel"]
    by blast
  moreover have "refl SRel"
    unfolding refl_on_def
  proof auto
    fix S
    from A1 have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by blast
    moreover from A1 have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
      by blast
    ultimately have "(SourceTerm S, SourceTerm S) \<in> Rel"
        using A4
        unfolding trans_def
      by blast
    with A2 show "(S, S) \<in> SRel"
      by blast
  qed
  moreover from A3 A4 have "trans TRel"
      unfolding trans_def
    by blast
  ultimately show "fully_abstract SRel TRel \<and> refl SRel \<and> trans TRel"
    by blast
qed

subsection \<open>Full Abstraction w.r.t. Equivalences\<close>

text \<open>If there exists a relation Rel that relates source terms and their literal translations
        and whose sym closure is trans, then the encoding is fully abstract with respect
        to the reduction of the sym closure of Rel to source/target terms.\<close>

lemma (in encoding) source_target_relation_with_trans_symcl_impl_full_abstraction:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes enc:   "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trans: "trans (symcl Rel)"
  shows "fully_abstract {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}
          {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}"
proof auto
  fix S1 S2
  from enc have "(TargetTerm (\<lbrakk>S1\<rbrakk>), SourceTerm S1) \<in> symcl Rel"
    by (simp add: symcl_def)
  moreover assume "(SourceTerm S1, SourceTerm S2) \<in> symcl Rel"
  moreover from enc have "(SourceTerm S2, TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> symcl Rel"
    by (simp add: symcl_def)
  ultimately show "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> symcl Rel"
      using trans
      unfolding trans_def
    by blast
next
  fix S1 S2
  from enc have "(SourceTerm S1, TargetTerm (\<lbrakk>S1\<rbrakk>)) \<in> symcl Rel"
    by (simp add: symcl_def)
  moreover assume "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> symcl Rel"
  moreover from enc have "(TargetTerm (\<lbrakk>S2\<rbrakk>), SourceTerm S2) \<in> symcl Rel"
    by (simp add: symcl_def)
  ultimately show "(SourceTerm S1, SourceTerm S2) \<in> symcl Rel"
      using trans
      unfolding trans_def
    by blast
qed

text \<open>If an encoding is fully abstract w.r.t. the equivalences SRel and TRel, then there exists a
        preorder, namely indRelRSTPO, that relates source terms and their literal translations such
        that its reductions to source terms is SRel and its reduction to target terms is TRel.\<close>

lemma (in encoding) fully_abstract_wrt_equivalences_impl_symcl_source_target_relation_is_preorder:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and reflT:   "refl TRel"
      and symmT:   "sym TRel"
      and transT:  "trans TRel"
  shows "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}
                \<and> preorder (symcl Rel)"
proof -
  from fullAbs reflT have reflS: "refl SRel"
      unfolding refl_on_def
    by auto
  from fullAbs symmT have symmS: "sym SRel"
      unfolding sym_def
    by auto
  from fullAbs transT have transS: "trans SRel"
      unfolding trans_def
    by blast
  have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      using indRelRSTPO.encR[where SRel="SRel" and TRel="TRel"]
    by blast
  moreover
  have "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl (indRelRSTPO SRel TRel)}"
  proof auto
    fix S1 S2
    assume "(S1, S2) \<in> SRel"
    thus "(SourceTerm S1, SourceTerm S2) \<in> symcl (indRelRSTPO SRel TRel)"
      by (simp add: symcl_def indRelRSTPO.source[where SRel="SRel" and TRel="TRel"])
  next
    fix S1 S2
    assume "(SourceTerm S1, SourceTerm S2) \<in> symcl (indRelRSTPO SRel TRel)"
    moreover from transS
    have "SourceTerm S1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> SourceTerm S2 \<Longrightarrow> (S1, S2) \<in> SRel"
        using indRelRSTPO_to_SRel_and_TRel(1)[where SRel="SRel" and TRel="TRel"]
              trancl_id[of SRel]
      by blast
    moreover from symmS transS
    have "SourceTerm S2 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> SourceTerm S1 \<Longrightarrow> (S1, S2) \<in> SRel"
        using indRelRSTPO_to_SRel_and_TRel(1)[where SRel="SRel" and TRel="TRel"]
              trancl_id[of SRel]
        unfolding sym_def
      by blast
    ultimately show "(S1, S2) \<in> SRel"
      by (auto simp add: symcl_def)
  qed
  moreover
  have "TRel =  {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl (indRelRSTPO SRel TRel)}"
  proof auto
    fix T1 T2
    assume "(T1, T2) \<in> TRel"
    thus "(TargetTerm T1, TargetTerm T2) \<in> symcl (indRelRSTPO SRel TRel)"
      by (simp add: symcl_def indRelRSTPO.target[where SRel="SRel" and TRel="TRel"])
  next
    fix T1 T2
    assume "(TargetTerm T1, TargetTerm T2) \<in> symcl (indRelRSTPO SRel TRel)"
    moreover from transT
    have "TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> TargetTerm T2 \<Longrightarrow> (T1, T2) \<in> TRel"
        using indRelRSTPO_to_SRel_and_TRel(4)[where SRel="SRel" and TRel="TRel"]
              trancl_id[of TRel]
      by blast
    moreover from symmT transT
    have "TargetTerm T2 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> TargetTerm T1 \<Longrightarrow> (T1, T2) \<in> TRel"
        using indRelRSTPO_to_SRel_and_TRel(4)[where SRel="SRel" and TRel="TRel"]
              trancl_id[of TRel]
        unfolding sym_def
      by blast
    ultimately show "(T1, T2) \<in> TRel"
      by (auto simp add: symcl_def)
  qed
  moreover have "refl (symcl (indRelRSTPO SRel TRel))"
    unfolding refl_on_def
  proof auto
    fix P
    show "(P, P) \<in> symcl (indRelRSTPO SRel TRel)"
    proof (cases P)
      case (SourceTerm SP)
      assume "SP \<in>S P"
      with reflS show "(P, P) \<in> symcl (indRelRSTPO SRel TRel)"
          unfolding refl_on_def
        by (simp add: symcl_def indRelRSTPO.source)
    next
      case (TargetTerm TP)
      assume "TP \<in>T P"
      with reflT show "(P, P) \<in> symcl (indRelRSTPO SRel TRel)"
          unfolding refl_on_def
        by (simp add: symcl_def indRelRSTPO.target)
    qed
  qed
  moreover have "trans (symcl (indRelRSTPO SRel TRel))"
  proof -
    have "\<forall>P Q R. P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q \<and> R \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q \<and> (P, R) \<notin> (indRelRSTPO SRel TRel)
          \<longrightarrow> Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P \<or> Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R"
    proof clarify
      fix P Q R
      assume A1: "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q" and A2: "R \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q"
         and A3: "(P, R) \<notin> (indRelRSTPO SRel TRel)" and A4: "(Q, R) \<notin> (indRelRSTPO SRel TRel)"
      show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
      proof (cases P)
        case (SourceTerm SP)
        assume A5: "SP \<in>S P"
        show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
        proof (cases Q)
          case (SourceTerm SQ)
          assume A6: "SQ \<in>S Q"
          with transS A1 A5 have "(SP, SQ) \<in> SRel"
              using indRelRSTPO_to_SRel_and_TRel(1)[where SRel="SRel" and TRel="TRel"]
                    trancl_id[of SRel]
            by blast
          with symmS A5 A6 show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
              unfolding sym_def
            by (simp add: indRelRSTPO.source)
        next
          case (TargetTerm TQ)
          assume A6: "TQ \<in>T Q"
          show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
          proof (cases R)
            case (SourceTerm SR)
            assume A7: "SR \<in>S R"
            with fullAbs A2 A6 have "(\<lbrakk>SR\<rbrakk>, TQ) \<in> TRel\<^sup>*"
                using full_abstraction_impl_indRelRSTPO_to_SRel_and_TRel(2)[where SRel="SRel"
                       and TRel="TRel"] trancl_id[of "TRel\<^sup>="] reflcl_of_refl_rel[of TRel]
                      trancl_reflcl[of TRel]
                unfolding trans_def
              by blast
            with transT reflT have "(\<lbrakk>SR\<rbrakk>, TQ) \<in> TRel"
                using trancl_id[of "TRel\<^sup>="] reflcl_of_refl_rel[of TRel] trancl_reflcl[of TRel]
              by auto
            with symmT have "(TQ, \<lbrakk>SR\<rbrakk>) \<in> TRel"
                unfolding sym_def
              by simp
            moreover from fullAbs A1 A5 A6 have "(\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel\<^sup>*"
                using full_abstraction_impl_indRelRSTPO_to_SRel_and_TRel(2)[where SRel="SRel"
                       and TRel="TRel"]
                unfolding trans_def
              by blast
            with transT reflT have "(\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
                using trancl_id[of "TRel\<^sup>="] reflcl_of_refl_rel[of TRel] trancl_reflcl[of TRel]
              by auto
            ultimately have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
                using transT
                unfolding trans_def
              by blast
            with fullAbs have "(SP, SR) \<in> SRel"
              by simp
            with A3 A5 A7 show ?thesis
              by (simp add: indRelRSTPO.source)
          next
            case (TargetTerm TR)
            assume A7: "TR \<in>T R"
            with transT A2 A6 have "(TR, TQ) \<in> TRel"
                using indRelRSTPO_to_SRel_and_TRel(4)[where SRel="SRel" and TRel="TRel"]
                      trancl_id[of "TRel"]
              by blast
            with symmT have "(TQ, TR) \<in> TRel"
                unfolding sym_def
              by simp
            with A4 A6 A7 show ?thesis
              by (simp add: indRelRSTPO.target)
          qed
        qed
      next
        case (TargetTerm TP)
        assume A5: "TP \<in>T P"
        show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
        proof (cases Q)
          case (SourceTerm SQ)
          assume "SQ \<in>S Q"
          with A1 A5 show ?thesis
              using indRelRSTPO_to_SRel_and_TRel(3)[where SRel="SRel" and TRel="TRel"]
            by blast
        next
          case (TargetTerm TQ)
          assume A6: "TQ \<in>T Q"
          with transT A1 A5 have "(TP, TQ) \<in> TRel"
              using indRelRSTPO_to_SRel_and_TRel(4)[where SRel="SRel" and TRel="TRel"]
                    trancl_id[of "TRel"]
            by blast
          with symmT have "(TQ, TP) \<in> TRel"
              unfolding sym_def
            by simp
          with A5 A6 show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
            by (simp add: indRelRSTPO.target)
        qed
      qed
    qed
    moreover
    have "\<forall>P Q R. P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q \<and> P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R \<and> (Q, R) \<notin> (indRelRSTPO SRel TRel)
          \<longrightarrow> Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P \<or> R \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
    proof clarify
      fix P Q R
      assume A1: "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q" and A2: "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R"
         and A3: "(Q, R) \<notin> (indRelRSTPO SRel TRel)" and A4: "(R, P) \<notin> (indRelRSTPO SRel TRel)"
      show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
      proof (cases P)
        case (SourceTerm SP)
        assume A5: "SP \<in>S P"
        show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
        proof (cases Q)
          case (SourceTerm SQ)
          assume A6: "SQ \<in>S Q"
          with transS A1 A5 have "(SP, SQ) \<in> SRel"
              using indRelRSTPO_to_SRel_and_TRel(1)[where SRel="SRel" and TRel="TRel"]
                    trancl_id[of "SRel"]
            by blast
          with symmS A5 A6 show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
              unfolding sym_def
            by (simp add: indRelRSTPO.source)
        next
          case (TargetTerm TQ)
          assume A6: "TQ \<in>T Q"
          show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
          proof (cases R)
            case (SourceTerm SR)
            assume A7: "SR \<in>S R"
            with transS A2 A5 have "(SP, SR) \<in> SRel"
                using indRelRSTPO_to_SRel_and_TRel(1)[where SRel="SRel" and TRel="TRel"]
                      trancl_id[of "SRel"]
              by blast
            with symmS have "(SR, SP) \<in> SRel"
                unfolding sym_def
              by simp
            with A4 A5 A7 show ?thesis
              by (simp add: indRelRSTPO.source)
          next
            case (TargetTerm TR)
            from fullAbs A1 A5 A6 have "(\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel\<^sup>*"
                using full_abstraction_impl_indRelRSTPO_to_SRel_and_TRel(2)[where SRel="SRel" and
                       TRel="TRel"]
                unfolding trans_def
              by blast
            with transT reflT have "(\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
                using trancl_id[of "TRel\<^sup>="] reflcl_of_refl_rel[of TRel] trancl_reflcl[of TRel]
              by auto
            with symmT have "(TQ, \<lbrakk>SP\<rbrakk>) \<in> TRel"
                unfolding sym_def
              by simp
            moreover assume A7: "TR \<in>T R"
            with fullAbs A2 A5 have "(\<lbrakk>SP\<rbrakk>, TR) \<in> TRel\<^sup>*"
                using full_abstraction_impl_indRelRSTPO_to_SRel_and_TRel(2)[where SRel="SRel" and
                        TRel="TRel"]
                unfolding trans_def
              by blast
            with transT reflT have "(\<lbrakk>SP\<rbrakk>, TR) \<in> TRel"
                using trancl_id[of "TRel\<^sup>="] reflcl_of_refl_rel[of TRel] trancl_reflcl[of TRel]
              by auto
            ultimately have "(TQ, TR) \<in> TRel"
                using transT
                unfolding trans_def
              by blast
            with A3 A6 A7 show ?thesis
              by (simp add: indRelRSTPO.target)
          qed
        qed
      next
        case (TargetTerm TP)
        assume A5: "TP \<in>T P"
        show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
        proof (cases Q)
          case (SourceTerm SQ)
          assume "SQ \<in>S Q"
          with A1 A5 show ?thesis
              using indRelRSTPO_to_SRel_and_TRel(3)[where SRel="SRel" and TRel="TRel"]
            by blast
        next
          case (TargetTerm TQ)
          assume A6: "TQ \<in>T Q"
          with transT A1 A5 have "(TP, TQ) \<in> TRel"
              using indRelRSTPO_to_SRel_and_TRel(4)[where SRel="SRel" and TRel="TRel"]
                    trancl_id[of "TRel"]
            by blast
          with symmT have "(TQ, TP) \<in> TRel"
              unfolding sym_def
            by simp
          with A5 A6 show "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
            by (simp add: indRelRSTPO.target)
        qed
      qed
    qed
    moreover from reflS reflT have "refl (indRelRSTPO SRel TRel)"
        using indRelRSTPO_refl[where SRel="SRel" and TRel="TRel"]
      by blast
    moreover have "trans (indRelRSTPO SRel TRel)"
        using indRelRSTPO.trans[where SRel="SRel" and TRel="TRel"]
        unfolding trans_def
      by blast
    ultimately show "trans (symcl (indRelRSTPO SRel TRel))"
        using symm_closure_of_preorder_is_trans[where Rel="indRelRSTPO SRel TRel"]
      by blast
  qed
  ultimately show ?thesis
      unfolding preorder_on_def
    by blast
qed

lemma (in encoding) fully_abstract_impl_symcl_source_target_relation_is_preorder:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract ((symcl (SRel\<^sup>=))\<^sup>+) ((symcl (TRel\<^sup>=))\<^sup>+)"
  shows "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> ((symcl (SRel\<^sup>=))\<^sup>+) = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}
                \<and> ((symcl (TRel\<^sup>=))\<^sup>+) = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}
                \<and> preorder (symcl Rel)"
proof -
  have "refl ((symcl (TRel\<^sup>=))\<^sup>+)"
      using refl_symm_trans_closure_is_symm_refl_trans_closure[of TRel]
            refl_rtrancl[of TRel]
      unfolding sym_def refl_on_def
    by auto
  moreover have "sym ((symcl (TRel\<^sup>=))\<^sup>+)"
      using sym_symcl[of "TRel\<^sup>="] sym_trancl[of "symcl (TRel\<^sup>=)"]
    by simp
  moreover have "trans ((symcl (TRel\<^sup>=))\<^sup>+)"
    by simp
  ultimately show ?thesis
      using fully_abstract_wrt_equivalences_impl_symcl_source_target_relation_is_preorder[where
             SRel="(symcl (SRel\<^sup>=))\<^sup>+" and TRel="(symcl (TRel\<^sup>=))\<^sup>+"] fullAbs
            refl_symm_closure_is_symm_refl_closure
      unfolding preorder_on_def
    by blast
qed

lemma (in encoding) fully_abstract_wrt_preorders_impl_source_target_relation_is_trans:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
  shows "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                \<and> ((refl SRel \<and> trans TRel)
                   \<longleftrightarrow> trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}))"
proof -
  define Rel where "Rel = (indRelSTEQ SRel TRel) - ({(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}
                 \<union> {(P, Q). \<exists>S1 S2. S1 \<in>S P \<and> S2 \<in>S Q \<and> (S1, S2) \<notin> SRel}
                 \<union> {(P, Q). \<exists>T1 T2. T1 \<in>T P \<and> T2 \<in>T Q \<and> (T1, T2) \<notin> TRel})"
  from Rel_def have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelSTEQ.encR[where SRel="SRel" and TRel="TRel"])
  moreover from Rel_def have "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
  proof auto
    fix S1 S2
    assume "(S1, S2) \<in> SRel"
    thus "SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2"
      by (simp add: indRelSTEQ.source[where SRel="SRel" and TRel="TRel"])
  qed
  moreover from Rel_def have "TRel =  {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
  proof auto
    fix T1 T2
    assume "(T1, T2) \<in> TRel"
    thus "TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2"
      by (simp add: indRelSTEQ.target[where SRel="SRel" and TRel="TRel"])
  qed
  moreover
  have "(refl SRel \<and> trans TRel) \<longleftrightarrow> trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
  proof (rule iffI, erule conjE)
    assume reflS: "refl SRel" and transT: "trans TRel"
    have "Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} = indRelSTEQ SRel TRel"
    proof (auto simp add: Rel_def)
      fix S
      show "TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S"
        by (rule indRelSTEQ.encL)
    next
      fix S1 S2
      assume "SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2"
      with fullAbs reflS transT have "(S1, S2) \<in> SRel"
          using full_abstraction_wrt_preorders_impl_indRelSTEQ_to_SRel_and_TRel(1)[where
                SRel="SRel" and TRel="TRel"]
        by blast
      moreover assume "(S1, S2) \<notin> SRel"
      ultimately show False
        by simp
    next
      fix T1 T2
      assume "TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2"
      with fullAbs reflS transT have "(T1, T2) \<in> TRel"
          using full_abstraction_wrt_preorders_impl_indRelSTEQ_to_SRel_and_TRel(5)[where
                SRel="SRel" and TRel="TRel"]
        by blast
      moreover assume "(T1, T2) \<notin> TRel"
      ultimately show False
        by simp
    qed
    thus "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
        using indRelSTEQ_trans[where SRel="SRel" and TRel="TRel"]
        unfolding trans_def
      by blast
  next
    assume transR: "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
    show "refl SRel \<and> trans TRel"
      unfolding trans_def refl_on_def
    proof auto
      fix S
      from Rel_def have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
        by (simp add: indRelSTEQ.encR)
      moreover have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
        by simp
      ultimately have "(SourceTerm S, SourceTerm S) \<in> Rel"
          using transR
          unfolding trans_def
        by blast
      with Rel_def show "(S, S) \<in> SRel"
        by simp
    next
      fix TP TQ TR
      assume "(TP, TQ) \<in> TRel"
      with Rel_def have "(TargetTerm TP, TargetTerm TQ) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
        by (simp add: indRelSTEQ.target)
      moreover assume "(TQ, TR) \<in> TRel"
      with Rel_def have "(TargetTerm TQ, TargetTerm TR) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
        by (simp add: indRelSTEQ.target)
      ultimately have "(TargetTerm TP, TargetTerm TR) \<in> Rel"
          using transR
          unfolding trans_def
        by blast
      with Rel_def show "(TP, TR) \<in> TRel"
        by simp
    qed
  qed
  ultimately show ?thesis
    by blast
qed

lemma (in encoding) fully_abstract_wrt_preorders_impl_source_target_relation_is_trans_B:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and reflT:   "refl TRel"
      and transT:  "trans TRel"
  shows "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                \<and> trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
proof -
  define Rel where "Rel = (indRelSTEQ SRel TRel) - {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
  from fullAbs reflT have reflS: "refl SRel"
      unfolding refl_on_def
    by auto
  from Rel_def have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelSTEQ.encR[where SRel="SRel" and TRel="TRel"])
  moreover from Rel_def have "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
  proof auto
    fix S1 S2
    assume "(S1, S2) \<in> SRel"
    thus "SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2"
      by (simp add: indRelSTEQ.source[where SRel="SRel" and TRel="TRel"])
  next
    fix S1 S2
    assume "SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2"
    with fullAbs transT reflS show "(S1, S2) \<in> SRel"
        using full_abstraction_wrt_preorders_impl_indRelSTEQ_to_SRel_and_TRel(1)[where SRel="SRel"
              and TRel="TRel"]
      by blast
  qed
  moreover from Rel_def have "TRel =  {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
  proof auto
    fix T1 T2
    assume "(T1, T2) \<in> TRel"
    thus "TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2"
      by (simp add: indRelSTEQ.target[where SRel="SRel" and TRel="TRel"])
  next
    fix T1 T2
    assume "TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2"
    with fullAbs transT reflS show "(T1, T2) \<in> TRel"
        using full_abstraction_wrt_preorders_impl_indRelSTEQ_to_SRel_and_TRel(5)[where SRel="SRel"
              and TRel="TRel"]
      by blast
  qed
  moreover from Rel_def have "Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} = indRelSTEQ SRel TRel"
    by (auto simp add: indRelSTEQ.encL)
  hence "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
      using indRelSTEQ.trans[where SRel="SRel" and TRel="TRel"]
      unfolding trans_def
    by auto
  ultimately show ?thesis
    by blast
qed

text \<open>Thus an encoding is fully abstract w.r.t. an equivalence SRel on the source and an
        equivalence TRel on the target iff there exists a relation that relates source terms and
        their literal translations, whose sym closure is a preorder such that the reduction
        of this sym closure to source/target terms is SRel/TRel.\<close>

lemma (in encoding) fully_abstract_wrt_equivalences_iff_symcl_source_target_relation_is_preorder:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  shows "(fully_abstract SRel TRel \<and> equivalence TRel) =
         (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}
                \<and> preorder (symcl Rel))"
proof (rule iffI)
  assume "fully_abstract SRel TRel \<and> equivalence TRel"
  thus "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}
                \<and> preorder (symcl Rel)"
      using fully_abstract_wrt_equivalences_impl_symcl_source_target_relation_is_preorder[where
             SRel="SRel" and TRel="TRel"]
      unfolding equiv_def
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}
                \<and> preorder (symcl Rel)"
  from this obtain Rel
    where     "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and     "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}"
      and A1: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}"
      and A2: "preorder (symcl Rel)"
    by blast
  hence A5: "fully_abstract SRel TRel"
      using source_target_relation_with_trans_symcl_impl_full_abstraction[where Rel="Rel"]
      unfolding preorder_on_def
    by blast
  moreover have "equivalence TRel"
    unfolding trans_def equiv_def sym_def refl_on_def
  proof auto
    fix T
    from A1 A2 show "(T, T) \<in> TRel"
        unfolding preorder_on_def refl_on_def
      by blast
  next
    fix T1 T2
    assume "(T1, T2) \<in> TRel"
    with A1 show "(T2, T1) \<in> TRel"
      by (auto simp add: symcl_def)
  next
    fix T1 T2 T3
    assume "(T1, T2) \<in> TRel" and "(T2, T3) \<in> TRel"
    with A1 A2 show "(T1, T3) \<in> TRel"
        unfolding trans_def preorder_on_def
      by blast
  qed
  ultimately show "fully_abstract SRel TRel \<and> equivalence TRel"
    by blast
qed

lemma (in encoding) fully_abstract_iff_symcl_source_target_relation_is_preorder:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  shows "fully_abstract ((symcl (SRel\<^sup>=))\<^sup>+) ((symcl (TRel\<^sup>=))\<^sup>+) =
         (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> (symcl (SRel\<^sup>=))\<^sup>+ = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}
                \<and> (symcl (TRel\<^sup>=))\<^sup>+ = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}
                \<and> preorder (symcl Rel))"
proof (rule iffI)
  assume "fully_abstract ((symcl (SRel\<^sup>=))\<^sup>+) ((symcl (TRel\<^sup>=))\<^sup>+)"
  thus "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> (symcl (SRel\<^sup>=))\<^sup>+ = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}
                \<and> (symcl (TRel\<^sup>=))\<^sup>+ = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}
                \<and> preorder (symcl Rel)"
      using fully_abstract_impl_symcl_source_target_relation_is_preorder[where SRel="SRel" and
             TRel="TRel"]
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> (symcl (SRel\<^sup>=))\<^sup>+ = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}
                \<and> (symcl (TRel\<^sup>=))\<^sup>+ = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}
                \<and> preorder (symcl Rel)"
  from this obtain Rel
    where     "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and     "(symcl (SRel\<^sup>=))\<^sup>+ = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> symcl Rel}"
      and A1: "(symcl (TRel\<^sup>=))\<^sup>+ = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> symcl Rel}"
      and A2: "preorder (symcl Rel)"
    by blast
  thus "fully_abstract ((symcl (SRel\<^sup>=))\<^sup>+) ((symcl (TRel\<^sup>=))\<^sup>+)"
      using source_target_relation_with_trans_symcl_impl_full_abstraction[where Rel="Rel"]
      unfolding preorder_on_def
    by blast
qed

subsection \<open>Full Abstraction without Relating Translations to their Source Terms\<close>

text \<open>Let Rel be the result of removing from indRelSTEQ all pairs of two source or two target
        terms that are not contained in SRel or TRel. Then a fully abstract encoding ensures that
        Rel is trans iff SRel is refl and TRel is trans.\<close>

lemma (in encoding) full_abstraction_impl_indRelSTEQ_is_trans:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and rel:     "Rel = ((indRelSTEQ SRel TRel)
                    - {(P, Q). (P \<in> ProcS \<and> Q \<in> ProcS) \<or> (P \<in> ProcT \<and> Q \<in> ProcT)})
                    \<union> {(P, Q). (\<exists>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<and> (SP, SQ) \<in> SRel)
                        \<or> (\<exists>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<and> (TP, TQ) \<in> TRel)}"
  shows "(refl SRel \<and> trans TRel) = trans Rel"
    unfolding trans_def
proof auto
  fix P Q R
  assume A1: "refl SRel" and A2: "\<forall>x y. (x, y) \<in> TRel \<longrightarrow> (\<forall>z. (y, z) \<in> TRel \<longrightarrow> (x, z) \<in> TRel)"
     and A3: "(P, Q) \<in> Rel" and A4: "(Q, R) \<in> Rel"
  from fullAbs rel have A5: "\<forall>SP SQ. (SourceTerm SP, SourceTerm SQ) \<in> Rel \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    by simp
  from rel have A6: "\<forall>TP TQ. (TargetTerm TP, TargetTerm TQ) \<in> Rel \<longrightarrow> (TP, TQ) \<in> TRel"
    by simp
  have A7: "\<forall>SP TQ. (SourceTerm SP, TargetTerm TQ) \<in> Rel \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
  proof clarify
    fix SP TQ
    assume "(SourceTerm SP, TargetTerm TQ) \<in> Rel"
    with rel have "SourceTerm SP \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm TQ"
      by simp
    with A1 A2 fullAbs show "(\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
        using full_abstraction_wrt_preorders_impl_indRelSTEQ_to_SRel_and_TRel(3)[where
              SRel="SRel" and TRel="TRel"]
        unfolding trans_def
      by blast
  qed
  have A8: "\<forall>TP SQ. (TargetTerm TP, SourceTerm SQ) \<in> Rel \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
  proof clarify
    fix TP SQ
    assume "(TargetTerm TP, SourceTerm SQ) \<in> Rel"
    with rel have "TargetTerm TP \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm SQ"
      by simp
    with A1 A2 fullAbs show "(TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
        using full_abstraction_wrt_preorders_impl_indRelSTEQ_to_SRel_and_TRel(4)[where
              SRel="SRel" and TRel="TRel"]
        unfolding trans_def
      by blast
  qed
  show "(P, R) \<in> Rel"
  proof (cases P)
    case (SourceTerm SP)
    assume A9: "SP \<in>S P"
    show "(P, R) \<in> Rel"
    proof (cases Q)
      case (SourceTerm SQ)
      assume A10: "SQ \<in>S Q"
      with A3 A5 A9 have A11: "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
        by simp
      show "(P, R) \<in> Rel"
      proof (cases R)
        case (SourceTerm SR)
        assume A12: "SR \<in>S R"
        with A4 A5 A10 have "(\<lbrakk>SQ\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          by simp
        with A2 A11 have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          by blast
        with fullAbs have "(SP, SR) \<in> SRel"
          by simp
        with rel A9 A12 show "(P, R) \<in> Rel"
          by simp
      next
        case (TargetTerm TR)
        assume A12: "TR \<in>T R"
        from A9 have "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>SP\<rbrakk>)"
          by (simp add: indRelSTEQ.encR)
        moreover from A4 A7 A10 A12 have "(\<lbrakk>SQ\<rbrakk>, TR) \<in> TRel"
          by simp
        with A2 A11 have "(\<lbrakk>SP\<rbrakk>, TR) \<in> TRel"
          by blast
        with A12 have "TargetTerm (\<lbrakk>SP\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (simp add: indRelSTEQ.target)
        ultimately have "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel, TRel> R"
          by (rule indRelSTEQ.trans)
        with rel A9 A12 show "(P, R) \<in> Rel"
          by simp
      qed
    next
      case (TargetTerm TQ)
      assume A10: "TQ \<in>T Q"
      with A3 A7 A9 have A11: "(\<lbrakk>SP\<rbrakk>, TQ) \<in> TRel"
        by simp
      show "(P, R) \<in> Rel"
      proof (cases R)
        case (SourceTerm SR)
        assume A12: "SR \<in>S R"
        with A4 A8 A10 have "(TQ, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          by simp
        with A2 A11 have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          by blast
        with fullAbs have "(SP, SR) \<in> SRel"
          by simp
        with rel A9 A12 show "(P, R) \<in> Rel"
          by simp
      next
        case (TargetTerm TR)
        assume A12: "TR \<in>T R"
        from A9 have "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>SP\<rbrakk>)"
          by (simp add: indRelSTEQ.encR)
        moreover from A4 A6 A10 A12 have "(TQ, TR) \<in> TRel"
          by simp
        with A2 A11 have "(\<lbrakk>SP\<rbrakk>, TR) \<in> TRel"
          by blast
        with A12 have "TargetTerm (\<lbrakk>SP\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (simp add: indRelSTEQ.target)
        ultimately have "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (rule indRelSTEQ.trans)
        with A9 A12 rel show "(P, R) \<in> Rel"
          by simp
      qed
    qed
  next
    case (TargetTerm TP)
    assume A9: "TP \<in>T P"
    show "(P, R) \<in> Rel"
    proof (cases Q)
      case (SourceTerm SQ)
      assume A10: "SQ \<in>S Q"
      with A3 A8 A9 have A11: "(TP, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
        by simp
      show "(P, R) \<in> Rel"
      proof (cases R)
        case (SourceTerm SR)
        assume A12: "SR \<in>S R"
        with A4 A5 A10 have "(\<lbrakk>SQ\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          by simp
        with A2 A11 have "(TP, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          by blast
        with A9 have "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>SR\<rbrakk>)"
          by (simp add: indRelSTEQ.target)
        moreover from A12 have "TargetTerm (\<lbrakk>SR\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (simp add: indRelSTEQ.encL)
        ultimately have "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (rule indRelSTEQ.trans)
        with rel A9 A12 show "(P, R) \<in> Rel"
          by simp
      next
        case (TargetTerm TR)
        assume A12: "TR \<in>T R"
        with A4 A7 A10 have "(\<lbrakk>SQ\<rbrakk>, TR) \<in> TRel"
          by simp
        with A2 A11 have "(TP, TR) \<in> TRel"
          by blast
        with rel A9 A12 show "(P, R) \<in> Rel"
          by simp
      qed
    next
      case (TargetTerm TQ)
      assume A10: "TQ \<in>T Q"
      with A3 A6 A9 have A11: "(TP, TQ) \<in> TRel"
        by simp
      show "(P, R) \<in> Rel"
      proof (cases R)
        case (SourceTerm SR)
        assume A12: "SR \<in>S R"
        with A4 A8 A10 have "(TQ, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          by simp
        with A2 A11 have "(TP, \<lbrakk>SR\<rbrakk>) \<in> TRel"
          by blast
        with A9 have "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>SR\<rbrakk>)"
          by (simp add: indRelSTEQ.target)
        moreover from A12 have "TargetTerm (\<lbrakk>SR\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (simp add: indRelSTEQ.encL)
        ultimately have "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (rule indRelSTEQ.trans)
        with rel A9 A12 show "(P, R) \<in> Rel"
          by simp
      next
        case (TargetTerm TR)
        assume A12: "TR \<in>T R"
        with A4 A6 A10 have "(TQ, TR) \<in> TRel"
          by simp
        with A2 A11 have "(TP, TR) \<in> TRel"
          by blast
        with A9 A12 rel show "(P, R) \<in> Rel"
          by simp
      qed
    qed
  qed
next
  assume B: "\<forall>x y. (x, y) \<in> Rel \<longrightarrow> (\<forall>z. (y, z) \<in> Rel \<longrightarrow> (x, z) \<in> Rel)"
  thus "refl SRel"
    unfolding refl_on_def
  proof auto
    fix S
    from rel have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by (simp add: indRelSTEQ.encR)
    moreover from rel have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
      by (simp add: indRelSTEQ.encL)
    ultimately have "(SourceTerm S, SourceTerm S) \<in> Rel"
        using B
      by blast
    with rel show "(S, S) \<in> SRel"
      by simp
  qed
next
  fix TP TQ TR
  assume "\<forall>x y. (x, y) \<in> Rel \<longrightarrow> (\<forall>z. (y, z) \<in> Rel \<longrightarrow> (x, z) \<in> Rel)"
  moreover assume "(TP, TQ) \<in> TRel"
  with rel have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
    by simp
  moreover assume "(TQ, TR) \<in> TRel"
  with rel have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
    by simp
  ultimately have "(TargetTerm TP, TargetTerm TR) \<in> Rel"
    by blast
  with rel show "(TP, TR) \<in> TRel"
    by simp
qed

text \<open>Whenever an encoding induces a trans relation that includes SRel and TRel and relates
        source terms to their literal translations in both directions, the encoding is fully
        abstract w.r.t. SRel and TRel.\<close>

lemma (in encoding) trans_source_target_relation_impl_fully_abstract:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes enc:   "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
                  \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
      and srel:  "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
      and trel:  "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      and trans: "trans Rel"
  shows "fully_abstract SRel TRel"
proof auto
  fix S1 S2
  assume "(S1, S2) \<in> SRel"
  with srel have "(SourceTerm S1, SourceTerm S2) \<in> Rel"
    by simp
  with enc trans have "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
      unfolding trans_def
    by blast
  with trel show "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"
    by simp
next
  fix S1 S2
  assume "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"
  with trel have "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
    by simp
  with enc trans have "(SourceTerm S1, SourceTerm S2) \<in> Rel"
      unfolding trans_def
    by blast
  with srel show "(S1, S2) \<in> SRel"
    by simp
qed

text \<open>Assume TRel is a preorder. Then an encoding is fully abstract w.r.t. SRel and TRel iff
        there exists a relation that relates add least all source terms to their literal
        translations, includes SRel and TRel, and whose union with the relation that relates
        exactly all literal translations to their source terms is trans.\<close>

lemma (in encoding) source_target_relation_with_trans_impl_full_abstraction:
  fixes Rel :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes enc:   "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and trans: "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
  shows "fully_abstract {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
          {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
proof auto
  fix S1 S2
  define Rel' where "Rel' = Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
  from Rel'_def have "(TargetTerm (\<lbrakk>S1\<rbrakk>), SourceTerm S1) \<in> Rel'"
    by simp
  moreover assume "(SourceTerm S1, SourceTerm S2) \<in> Rel"
  with Rel'_def have "(SourceTerm S1, SourceTerm S2) \<in> Rel'"
    by simp
  moreover from enc Rel'_def have "(SourceTerm S2, TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel'"
    by simp
  ultimately show "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
      using trans Rel'_def
      unfolding trans_def
    by blast
next
  fix S1 S2
  define Rel' where "Rel' = Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}"
  from enc Rel'_def have "(SourceTerm S1, TargetTerm (\<lbrakk>S1\<rbrakk>)) \<in> Rel'"
    by simp
  moreover assume "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel"
  with Rel'_def have "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel'"
    by simp
  moreover from Rel'_def have "(TargetTerm (\<lbrakk>S2\<rbrakk>), SourceTerm S2) \<in> Rel'"
    by simp
  ultimately show "(SourceTerm S1, SourceTerm S2) \<in> Rel"
      using trans Rel'_def
      unfolding trans_def
    by blast
qed

lemma (in encoding) fully_abstract_wrt_preorders_iff_source_target_relation_is_transB:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes preord: "preorder TRel"
  shows "fully_abstract SRel TRel =
         (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                \<and> trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q}))"
proof (rule iffI)
  assume "fully_abstract SRel TRel"
  with preord show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                \<and> trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
      using fully_abstract_wrt_preorders_impl_source_target_relation_is_trans[where SRel="SRel"
            and TRel="TRel"]
      unfolding preorder_on_def refl_on_def
    by auto
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
                \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                \<and> trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
  from this obtain Rel
    where "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
      and "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      and "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
    by blast
  thus "fully_abstract SRel TRel"
      using source_target_relation_with_trans_impl_full_abstraction[where Rel="Rel"]
    by blast
qed

text \<open>The same holds if to obtain transitivity the union may contain additional pairs that do
        neither relate two source nor two target terms.\<close>

lemma (in encoding) fully_abstract_wrt_preorders_iff_source_target_relation_union_is_trans:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  shows "(fully_abstract SRel TRel \<and> refl SRel \<and> trans TRel) =
         (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<exists>Rel'. (\<forall>(P, Q) \<in> Rel'. P \<in> ProcS \<longleftrightarrow> Q \<in> ProcT)
             \<and> trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel')))"
proof (rule iffI, (erule conjE)+)
  assume "fully_abstract SRel TRel" and "refl SRel" and "trans TRel"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                         and A2: "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
                         and A3: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
                         and A4: "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
      using fully_abstract_wrt_preorders_impl_source_target_relation_is_trans[where SRel="SRel"
            and TRel="TRel"]
    by blast
  have "\<forall>(P, Q) \<in> {}. P \<in> ProcS \<longleftrightarrow> Q \<in> ProcT"
    by simp
  moreover from A4 have "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> {})"
      unfolding trans_def
    by blast
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
                   \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
                   \<and> (\<exists>Rel'. (\<forall>(P, Q) \<in> Rel'. P \<in> ProcS \<longleftrightarrow> Q \<in> ProcT)
                      \<and> trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel'))"
      using A1 A2 A3
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<exists>Rel'. (\<forall>(P, Q) \<in> Rel'. P \<in> ProcS \<longleftrightarrow> Q \<in> ProcT)
             \<and> trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel'))"
  from this obtain Rel Rel'
    where B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and B2: "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
      and B3: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      and B4: "\<forall>(P, Q) \<in> Rel'. P \<in> ProcS \<longleftrightarrow> Q \<in> ProcT"
      and B5: "trans (Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel')"
    by blast
  have "fully_abstract SRel TRel"
  proof auto
    fix S1 S2
    have "(TargetTerm (\<lbrakk>S1\<rbrakk>), SourceTerm S1) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel'"
      by simp
    moreover assume "(S1, S2) \<in> SRel"
    with B2 have "(SourceTerm S1, SourceTerm S2) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel'"
      by simp
    moreover from B1
    have "(SourceTerm S2, TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel'"
      by simp
    ultimately have "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel \<union> Rel'"
        using B5
        unfolding trans_def
      by blast
    with B3 B4 show "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"
      by blast
  next
    fix S1 S2
    from B1
    have "(SourceTerm S1, TargetTerm (\<lbrakk>S1\<rbrakk>)) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel'"
      by simp
    moreover assume "(\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel"
    with B3
    have "(TargetTerm (\<lbrakk>S1\<rbrakk>), TargetTerm (\<lbrakk>S2\<rbrakk>)) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel'"
      by simp
    moreover
    have "(TargetTerm (\<lbrakk>S2\<rbrakk>), SourceTerm S2) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel'"
      by simp
    ultimately have "(SourceTerm S1, SourceTerm S2) \<in> Rel \<union> Rel'"
        using B5
        unfolding trans_def
      by blast
    with B2 B4 show "(S1, S2) \<in> SRel"
      by blast
  qed
  moreover have "refl SRel"
    unfolding refl_on_def
  proof auto
    fix S
    from B1 have "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel'"
      by simp
    moreover
    have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} \<union> Rel'"
      by simp
    ultimately have "(SourceTerm S, SourceTerm S) \<in> Rel \<union> Rel'"
        using B5
        unfolding trans_def
      by blast
    with B2 B4 show "(S, S) \<in> SRel"
      by blast
  qed
  moreover have "trans TRel"
    unfolding trans_def
  proof clarify
    fix TP TQ TR
    assume "(TP, TQ) \<in> TRel" and "(TQ, TR) \<in> TRel"
    with B3 B4 B5 show "(TP, TR) \<in> TRel"
        unfolding trans_def
      by blast
  qed
  ultimately show "fully_abstract SRel TRel \<and> refl SRel \<and> trans TRel"
    by blast
qed

end
