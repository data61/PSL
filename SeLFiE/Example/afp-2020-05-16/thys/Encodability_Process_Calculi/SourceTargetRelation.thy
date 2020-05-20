theory SourceTargetRelation
  imports Encodings SimulationRelations
begin

section \<open>Relation between Source and Target Terms\<close>

subsection \<open>Relations Induced by the Encoding Function\<close>

text \<open>We map encodability criteria on conditions of relations between source and target terms.
        The encoding function itself induces such relations. To analyse the preservation of source
        term behaviours we use relations that contain the pairs (S, enc S) for all source terms S.
\<close>

inductive_set (in encoding) indRelR
    :: "((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
  where
  encR: "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelR"

abbreviation (in encoding) indRelRinfix ::
    "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<R>\<lbrakk>\<cdot>\<rbrakk>R _" [75, 75] 80)
  where
  "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q \<equiv> (P, Q) \<in> indRelR"

inductive_set (in encoding) indRelRPO
    :: "((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
  where
  encR:   "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRPO" |
  source: "(SourceTerm S, SourceTerm S) \<in> indRelRPO" |
  target: "(TargetTerm T, TargetTerm T) \<in> indRelRPO" |
  trans:  "\<lbrakk>(P, Q) \<in> indRelRPO; (Q, R) \<in> indRelRPO\<rbrakk> \<Longrightarrow> (P, R) \<in> indRelRPO"

abbreviation (in encoding) indRelRPOinfix ::
    "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R _" [75, 75] 80)
  where
  "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R Q \<equiv> (P, Q) \<in> indRelRPO"

lemma (in encoding) indRelRPO_refl:
  shows "refl indRelRPO"
    unfolding refl_on_def
proof auto
  fix P
  show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R P"
  proof (cases P)
    case (SourceTerm SP)
    assume "SP \<in>S P"
    thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R P"
      by (simp add: indRelRPO.source)
  next
    case (TargetTerm TP)
    assume "TP \<in>T P"
    thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R P"
      by (simp add: indRelRPO.target)
  qed
qed

lemma (in encoding) indRelRPO_is_preorder:
  shows "preorder indRelRPO"
    unfolding preorder_on_def
proof
  show "refl indRelRPO"
    by (rule indRelRPO_refl)
next
  show "trans indRelRPO"
    unfolding trans_def
  proof clarify
    fix P Q R
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R Q" and "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R R"
    thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R R"
      by (rule indRelRPO.trans)
  qed
qed

lemma (in encoding) refl_trans_closure_of_indRelR:
  shows "indRelRPO = indRelR\<^sup>*"
proof auto
  fix P Q
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R Q"
  thus "(P, Q) \<in> indRelR\<^sup>*"
  proof induct
    case (encR S)
    show "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelR\<^sup>*"
        using indRelR.encR[of S]
      by simp
  next
    case (source S)
    show "(SourceTerm S, SourceTerm S) \<in> indRelR\<^sup>*"
      by simp
  next
    case (target T)
    show "(TargetTerm T, TargetTerm T) \<in> indRelR\<^sup>*"
      by simp
  next
    case (trans P Q R)
    assume "(P, Q) \<in> indRelR\<^sup>*" and "(Q, R) \<in> indRelR\<^sup>*"
    thus "(P, R) \<in> indRelR\<^sup>*"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> indRelR\<^sup>*"
  thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R Q"
  proof induct
    show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R P"
        using indRelRPO_refl
        unfolding refl_on_def
      by simp
  next
    case (step Q R)
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R Q"
    moreover assume "Q \<R>\<lbrakk>\<cdot>\<rbrakk>R R"
    hence "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R R"
      by (induct, simp add: indRelRPO.encR)
    ultimately show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R R"
      by (rule indRelRPO.trans)
  qed
qed

text \<open>The relation indRelR is the smallest relation that relates all source terms and their
        literal translations. Thus there exists a relation that relates source terms and their
        literal translations and satisfies some predicate on its pairs iff the predicate holds for
        the pairs of indRelR.\<close>

lemma (in encoding) indRelR_impl_exists_source_target_relation:
  fixes PredA :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set \<Rightarrow> bool"
    and PredB :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  shows "PredA indRelR \<Longrightarrow> \<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> PredA Rel"
    and "\<forall>(P, Q) \<in> indRelR. PredB (P, Q)
         \<Longrightarrow> \<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> (\<forall>(P, Q) \<in> Rel. PredB (P, Q))"
proof -
  have A: "\<forall>S. SourceTerm S \<R>\<lbrakk>\<cdot>\<rbrakk>R TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelR.encR)
  thus "PredA indRelR \<Longrightarrow> \<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> PredA Rel"
    by blast
  with A show "\<forall>(P, Q) \<in> indRelR. PredB (P, Q)
   \<Longrightarrow> \<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> (\<forall>(P, Q) \<in> Rel. PredB (P, Q))"
    by blast
qed

lemma (in encoding) source_target_relation_impl_indRelR:
  fixes Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
    and Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  assumes encRRel: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      and condRel: "\<forall>(P, Q) \<in> Rel. Pred (P, Q)"
  shows "\<forall>(P, Q) \<in> indRelR. Pred (P, Q)"
proof clarify
  fix P Q
  assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q"
  with encRRel have "(P, Q) \<in> Rel"
    by (auto simp add: indRelR.simps)
  with condRel show "Pred (P, Q)"
    by simp
qed

lemma (in encoding) indRelR_iff_exists_source_target_relation:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  shows "(\<forall>(P, Q) \<in> indRelR. Pred (P, Q))
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> (\<forall>(P, Q) \<in> Rel. Pred (P, Q)))"
      using indRelR_impl_exists_source_target_relation(2)[where PredB="Pred"]
            source_target_relation_impl_indRelR[where Pred="Pred"]
    by blast

lemma (in encoding) indRelR_modulo_pred_impl_indRelRPO_modulo_pred:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  assumes reflCond:  "\<forall>P. Pred (P, P)"
      and transCond: "\<forall>P Q R. Pred (P, Q) \<and> Pred (Q, R) \<longrightarrow> Pred (P, R)"
  shows "(\<forall>(P, Q) \<in> indRelR. Pred (P, Q)) = (\<forall>(P, Q) \<in> indRelRPO. Pred (P, Q))"
proof auto
  fix P Q
  assume A: "\<forall>x \<in> indRelR. Pred x"
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R Q"
  thus "Pred (P, Q)"
  proof induct
    case (encR S)
    have "SourceTerm S \<R>\<lbrakk>\<cdot>\<rbrakk>R TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (simp add: indRelR.encR)
    with A show "Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>))"
      by simp
  next
    case (source S)
    from reflCond show "Pred (SourceTerm S, SourceTerm S)"
      by simp
  next
    case (target T)
    from reflCond show "Pred (TargetTerm T, TargetTerm T)"
      by simp
  next
    case (trans P Q R)
    assume "Pred (P, Q)" and "Pred (Q, R)"
    with transCond show "Pred (P, R)"
      by blast
  qed
next
  fix P Q
  assume "\<forall>x \<in> indRelRPO. Pred x" and "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q"
  thus "Pred (P, Q)"
    by (auto simp add: indRelRPO.encR indRelR.simps)
qed

lemma (in encoding) indRelRPO_iff_exists_source_target_relation:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  shows "(\<forall>(P, Q) \<in> indRelRPO. Pred (P, Q)) = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
         \<and> (\<forall>(P, Q) \<in> Rel. Pred (P, Q)) \<and> preorder Rel)"
proof (rule iffI)
  have "\<forall>S. SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (simp add: indRelRPO.encR)
  moreover have "preorder indRelRPO"
      using indRelRPO_is_preorder
    by blast
  moreover assume "\<forall>(P, Q) \<in> indRelRPO. Pred (P, Q)"
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>(P, Q) \<in> Rel. Pred (P, Q)) \<and> preorder Rel"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>(P, Q) \<in> Rel. Pred (P, Q)) \<and> preorder Rel"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                         and A2: "\<forall>(P, Q) \<in> Rel. Pred (P, Q)" and A3: "preorder Rel"
    by blast
  show "\<forall>(P, Q) \<in> indRelRPO. Pred (P, Q)"
  proof clarify
    fix P Q
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R Q"
    hence "(P, Q) \<in> Rel"
    proof induct
      case (encR S)
      from A1 show "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
        by simp
    next
      case (source S)
      from A3 show "(SourceTerm S, SourceTerm S) \<in> Rel"
          unfolding preorder_on_def refl_on_def
        by simp
    next
      case (target T)
      from A3 show "(TargetTerm T, TargetTerm T) \<in> Rel"
          unfolding preorder_on_def refl_on_def
        by simp
    next
      case (trans P Q R)
      assume "(P, Q) \<in> Rel" and "(Q, R) \<in> Rel"
      with A3 show "(P, R) \<in> Rel"
          unfolding preorder_on_def trans_def
        by blast
    qed
    with A2 show "Pred (P, Q)"
      by simp
  qed
qed

text \<open>An encoding preserves, reflects, or respects a predicate iff indRelR preserves, reflects,
        or respects this predicate.\<close>

lemma (in encoding) enc_satisfies_pred_impl_indRelR_satisfies_pred:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  assumes encCond: "\<forall>S. Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>))"
  shows "\<forall>(P, Q) \<in> indRelR. Pred (P, Q)"
    by (auto simp add: encCond indRelR.simps)

lemma (in encoding) indRelR_satisfies_pred_impl_enc_satisfies_pred:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  assumes relCond: "\<forall>(P, Q) \<in> indRelR. Pred (P, Q)"
  shows "\<forall>S. Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>))"
      using relCond indRelR.encR
    by simp

lemma (in encoding) enc_satisfies_pred_iff_indRelR_satisfies_pred:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  shows "(\<forall>S. Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>))) = (\<forall>(P, Q) \<in> indRelR. Pred (P, Q))"
      using enc_satisfies_pred_impl_indRelR_satisfies_pred[where Pred="Pred"]
            indRelR_satisfies_pred_impl_enc_satisfies_pred[where Pred="Pred"]
    by blast

lemma (in encoding) enc_satisfies_binary_pred_iff_indRelR_satisfies_binary_pred:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> 'b \<Rightarrow> bool"
  shows "(\<forall>S a. Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) a) = (\<forall>(P, Q) \<in> indRelR. \<forall>a. Pred (P, Q) a)"
      using enc_satisfies_pred_iff_indRelR_satisfies_pred
    by simp

lemma (in encoding) enc_preserves_pred_iff_indRelR_preserves_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_preserves_pred Pred = rel_preserves_pred indRelR Pred"
      using enc_satisfies_pred_iff_indRelR_satisfies_pred[where Pred="\<lambda>(P, Q). Pred P \<longrightarrow> Pred Q"]
    by blast

lemma (in encoding) enc_preserves_binary_pred_iff_indRelR_preserves_binary_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "enc_preserves_binary_pred Pred = rel_preserves_binary_pred indRelR Pred"
      using enc_satisfies_binary_pred_iff_indRelR_satisfies_binary_pred[where
             Pred="\<lambda>(P, Q) a. Pred P a \<longrightarrow> Pred Q a"]
    by blast

lemma (in encoding) enc_preserves_pred_iff_indRelRPO_preserves_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_preserves_pred Pred = rel_preserves_pred indRelRPO Pred"
      using enc_preserves_pred_iff_indRelR_preserves_pred[where Pred="Pred"]
            indRelR_modulo_pred_impl_indRelRPO_modulo_pred[where
             Pred="\<lambda>(P, Q). Pred P \<longrightarrow> Pred Q"]
    by blast

lemma (in encoding) enc_reflects_pred_iff_indRelR_reflects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_reflects_pred Pred = rel_reflects_pred indRelR Pred"
      using enc_satisfies_pred_iff_indRelR_satisfies_pred[where Pred="\<lambda>(P, Q). Pred Q \<longrightarrow> Pred P"]
    by blast

lemma (in encoding) enc_reflects_binary_pred_iff_indRelR_reflects_binary_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "enc_reflects_binary_pred Pred = rel_reflects_binary_pred indRelR Pred"
      using enc_satisfies_binary_pred_iff_indRelR_satisfies_binary_pred[where
             Pred="\<lambda>(P, Q) a. Pred Q a \<longrightarrow> Pred P a"]
    by blast

lemma (in encoding) enc_reflects_pred_iff_indRelRPO_reflects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_reflects_pred Pred = rel_reflects_pred indRelRPO Pred"
      using enc_reflects_pred_iff_indRelR_reflects_pred[where Pred="Pred"]
            indRelR_modulo_pred_impl_indRelRPO_modulo_pred[where
             Pred="\<lambda>(P, Q). Pred Q \<longrightarrow> Pred P"]
    by blast

lemma (in encoding) enc_respects_pred_iff_indRelR_respects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_respects_pred Pred = rel_respects_pred indRelR Pred"
      using enc_preserves_pred_iff_indRelR_preserves_pred[where Pred="Pred"]
            enc_reflects_pred_iff_indRelR_reflects_pred[where Pred="Pred"]
    by blast

lemma (in encoding) enc_respects_binary_pred_iff_indRelR_respects_binary_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "enc_respects_binary_pred Pred = rel_respects_binary_pred indRelR Pred"
      using enc_preserves_binary_pred_iff_indRelR_preserves_binary_pred[where Pred="Pred"]
            enc_reflects_binary_pred_iff_indRelR_reflects_binary_pred[where Pred="Pred"]
    by blast

lemma (in encoding) enc_respects_pred_iff_indRelRPO_respects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_respects_pred Pred = rel_respects_pred indRelRPO Pred"
      using enc_respects_pred_iff_indRelR_respects_pred[where Pred="Pred"]
            indRelR_modulo_pred_impl_indRelRPO_modulo_pred[where Pred="\<lambda>(P, Q). Pred Q = Pred P"]
    apply simp by blast

text \<open>Accordingly an encoding preserves, reflects, or respects a predicate iff there exists a
        relation that relates source terms with their literal translations and preserves, reflects,
        or respects this predicate.\<close>

lemma (in encoding) enc_satisfies_pred_iff_source_target_satisfies_pred:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  shows "(\<forall>S. Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)))
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> (\<forall>(P, Q) \<in> Rel. Pred (P, Q)))"
    and "\<lbrakk>\<forall>P Q R. Pred (P, Q) \<and> Pred (Q, R) \<longrightarrow> Pred (P, R); \<forall>P. Pred (P, P)\<rbrakk> \<Longrightarrow>
         (\<forall>S. Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>))) = (\<exists>Rel. (\<forall>S.
         (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> (\<forall>(P, Q) \<in> Rel. Pred (P, Q)) \<and> preorder Rel)"
proof -
  show "(\<forall>S. Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)))
        = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> (\<forall>(P, Q) \<in> Rel. Pred (P, Q)))"
      using enc_satisfies_pred_iff_indRelR_satisfies_pred[where Pred="Pred"]
            indRelR_iff_exists_source_target_relation[where Pred="Pred"]
    by simp
next
  have "(\<forall>S. Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>))) = (\<forall>(P, Q) \<in> indRelR. Pred (P, Q))"
      using enc_satisfies_pred_iff_indRelR_satisfies_pred[where Pred="Pred"]
    by simp
  moreover assume "\<forall>P Q R. Pred (P, Q) \<and> Pred (Q, R) \<longrightarrow> Pred (P, R)" and "\<forall>P. Pred (P, P)"
  hence "(\<forall>(P, Q) \<in> indRelR. Pred (P, Q)) = (\<forall>(P, Q) \<in> indRelRPO. Pred (P, Q))"
      using indRelR_modulo_pred_impl_indRelRPO_modulo_pred[where Pred="Pred"]
    by blast
  ultimately show "(\<forall>S. Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>))) = (\<exists>Rel.
   (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> (\<forall>(P, Q) \<in> Rel. Pred (P, Q)) \<and> preorder Rel)"
      using indRelRPO_iff_exists_source_target_relation[where Pred="Pred"]
    by simp
qed

lemma (in encoding) enc_preserves_pred_iff_source_target_rel_preserves_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_preserves_pred Pred
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_preserves_pred Rel Pred)"
    and "enc_preserves_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
         \<and> rel_preserves_pred Rel Pred \<and> preorder Rel)"
proof -
  have A1: "enc_preserves_pred Pred
            = (\<forall>S. (\<lambda>(P, Q). Pred P \<longrightarrow> Pred Q) (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)))"
    by blast
  moreover have A2: "\<And>Rel. rel_preserves_pred Rel Pred
                     = (\<forall>(P, Q) \<in> Rel. (\<lambda>(P, Q). Pred P \<longrightarrow> Pred Q) (P, Q))"
    by blast
  ultimately show "enc_preserves_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> rel_preserves_pred Rel Pred)"
      using enc_satisfies_pred_iff_source_target_satisfies_pred(1)[where
             Pred="\<lambda>(P, Q). Pred P \<longrightarrow> Pred Q"]
    by simp
  from A1 A2 show "enc_preserves_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> rel_preserves_pred Rel Pred \<and> preorder Rel)"
      using enc_satisfies_pred_iff_source_target_satisfies_pred(2)[where
             Pred="\<lambda>(P, Q). Pred P \<longrightarrow> Pred Q"]
    by simp
qed

lemma (in encoding) enc_preserves_binary_pred_iff_source_target_rel_preserves_binary_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "enc_preserves_binary_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
         \<and> rel_preserves_binary_pred Rel Pred)"
proof -
  have "enc_preserves_binary_pred Pred
        = (\<forall>S. (\<lambda>(P, Q). \<forall>a. Pred P a \<longrightarrow> Pred Q a) (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)))"
    by blast
  moreover have "\<And>Rel. rel_preserves_binary_pred Rel Pred
                 = (\<forall>(P, Q) \<in> Rel. (\<lambda>(P, Q). \<forall>a. Pred P a \<longrightarrow> Pred Q a) (P, Q))"
    by blast
  ultimately show "enc_preserves_binary_pred Pred = (\<exists>Rel. (\<forall>S.
                   (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_preserves_binary_pred Rel Pred)"
      using enc_satisfies_pred_iff_source_target_satisfies_pred(1)[where
             Pred="\<lambda>(P, Q). \<forall>a. Pred P a \<longrightarrow> Pred Q a"]
    by simp
qed

lemma (in encoding) enc_reflects_pred_iff_source_target_rel_reflects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_reflects_pred Pred
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_pred Rel Pred)"
    and "enc_reflects_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
         \<and> rel_reflects_pred Rel Pred \<and> preorder Rel)"
proof -
  have A1: "enc_reflects_pred Pred
        = (\<forall>S. (\<lambda>(P, Q). Pred Q \<longrightarrow> Pred P) (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)))"
    by blast
  moreover have A2: "\<And>Rel. rel_reflects_pred Rel Pred
                     = (\<forall>(P, Q) \<in> Rel. (\<lambda>(P, Q). Pred Q \<longrightarrow> Pred P) (P, Q))"
    by blast
  ultimately show "enc_reflects_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> rel_reflects_pred Rel Pred)"
      using enc_satisfies_pred_iff_source_target_satisfies_pred(1)[where
             Pred="\<lambda>(P, Q). Pred Q \<longrightarrow> Pred P"]
    by simp
  from A1 A2 show "enc_reflects_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> rel_reflects_pred Rel Pred \<and> preorder Rel)"
      using enc_satisfies_pred_iff_source_target_satisfies_pred(2)[where
             Pred="\<lambda>(P, Q). Pred Q \<longrightarrow> Pred P"]
    by simp
qed

lemma (in encoding) enc_reflects_binary_pred_iff_source_target_rel_reflects_binary_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "enc_reflects_binary_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
         \<and> rel_reflects_binary_pred Rel Pred)"
proof -
  have "enc_reflects_binary_pred Pred
        = (\<forall>S. (\<lambda>(P, Q). \<forall>a. Pred Q a \<longrightarrow> Pred P a) (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)))"
    by blast
  moreover have "\<And>Rel. rel_reflects_binary_pred Rel Pred
                 = (\<forall>(P, Q) \<in> Rel. (\<lambda>(P, Q). \<forall>a. Pred Q a \<longrightarrow> Pred P a) (P, Q))"
    by blast
  ultimately show "enc_reflects_binary_pred Pred = (\<exists>Rel. (\<forall>S.
                   (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_binary_pred Rel Pred)"
      using enc_satisfies_pred_iff_source_target_satisfies_pred(1)[where
             Pred="\<lambda>(P, Q). \<forall>a. Pred Q a \<longrightarrow> Pred P a"]
    by simp
qed

lemma (in encoding) enc_respects_pred_iff_source_target_rel_respects_pred_encR:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_respects_pred Pred
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel Pred)"
    and "enc_respects_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
         \<and> rel_respects_pred Rel Pred \<and> preorder Rel)"
proof -
  have A1: "enc_respects_pred Pred
            = (\<forall>S. (\<lambda>(P, Q). Pred P = Pred Q) (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)))"
    by blast
  moreover
  have A2: "\<And>Rel. rel_respects_pred Rel Pred = (\<forall>(P, Q) \<in> Rel. (\<lambda>(P, Q). Pred P = Pred Q) (P, Q))"
    by blast
  ultimately show "enc_respects_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> rel_respects_pred Rel Pred)"
      using enc_satisfies_pred_iff_source_target_satisfies_pred(1)[where
             Pred="\<lambda>(P, Q). Pred P = Pred Q"]
    by simp
  from A1 A2 show "enc_respects_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> rel_respects_pred Rel Pred \<and> preorder Rel)"
      using enc_satisfies_pred_iff_source_target_satisfies_pred(2)[where
             Pred="\<lambda>(P, Q). Pred P = Pred Q"]
    by simp
qed

lemma (in encoding) enc_respects_binary_pred_iff_source_target_rel_respects_binary_pred_encR:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "enc_respects_binary_pred Pred = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
         \<and> rel_respects_binary_pred Rel Pred)"
proof -
  have "enc_respects_binary_pred Pred
        = (\<forall>S. (\<lambda>(P, Q). \<forall>a. Pred P a = Pred Q a) (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)))"
    by blast
  moreover have "\<And>Rel. rel_respects_binary_pred Rel Pred
                 = (\<forall>(P, Q) \<in> Rel. (\<lambda>(P, Q). \<forall>a. Pred P a = Pred Q a) (P, Q))"
    by blast
  ultimately show "enc_respects_binary_pred Pred = (\<exists>Rel. (\<forall>S.
                   (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_binary_pred Rel Pred)"
      using enc_satisfies_pred_iff_source_target_satisfies_pred(1)[where
             Pred="\<lambda>(P, Q). \<forall>a. Pred P a = Pred Q a"]
    by simp
qed

text \<open>To analyse the reflection of source term behaviours we use relations that contain the pairs
        (enc S, S) for all source terms S.\<close>

inductive_set (in encoding) indRelL
    :: "((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
  where
  encL: "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelL"

abbreviation (in encoding) indRelLinfix ::
    "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<R>\<lbrakk>\<cdot>\<rbrakk>L _" [75, 75] 80)
  where
  "P \<R>\<lbrakk>\<cdot>\<rbrakk>L Q \<equiv> (P, Q) \<in> indRelL"

inductive_set (in encoding) indRelLPO
    :: "((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
  where
  encL:   "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelLPO" |
  source: "(SourceTerm S, SourceTerm S) \<in> indRelLPO" |
  target: "(TargetTerm T, TargetTerm T) \<in> indRelLPO" |
  trans:  "\<lbrakk>(P, Q) \<in> indRelLPO; (Q, R) \<in> indRelLPO\<rbrakk> \<Longrightarrow> (P, R) \<in> indRelLPO"

abbreviation (in encoding) indRelLPOinfix ::
    "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L _" [75, 75] 80)
  where
  "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L Q \<equiv> (P, Q) \<in> indRelLPO"

lemma (in encoding) indRelLPO_refl:
  shows "refl indRelLPO"
    unfolding refl_on_def
proof auto
  fix P
  show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L P"
  proof (cases P)
    case (SourceTerm SP)
    assume "SP \<in>S P"
    thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L P"
      by (simp add: indRelLPO.source)
  next
    case (TargetTerm TP)
    assume "TP \<in>T P"
    thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L P"
      by (simp add: indRelLPO.target)
  qed
qed

lemma (in encoding) indRelLPO_is_preorder:
  shows "preorder indRelLPO"
    unfolding preorder_on_def
proof
  show "refl indRelLPO"
    by (rule indRelLPO_refl)
next
  show "trans indRelLPO"
    unfolding trans_def
  proof clarify
    fix P Q R
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L Q" and "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L R"
    thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L R"
      by (rule indRelLPO.trans)
  qed
qed

lemma (in encoding) refl_trans_closure_of_indRelL:
  shows "indRelLPO = indRelL\<^sup>*"
proof auto
  fix P Q
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L Q"
  thus "(P, Q) \<in> indRelL\<^sup>*"
  proof induct
    case (encL S)
    show "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelL\<^sup>*"
        using indRelL.encL[of S]
      by simp
  next
    case (source S)
    show "(SourceTerm S, SourceTerm S) \<in> indRelL\<^sup>*"
      by simp
  next
    case (target T)
    show "(TargetTerm T, TargetTerm T) \<in> indRelL\<^sup>*"
      by simp
  next
    case (trans P Q R)
    assume "(P, Q) \<in> indRelL\<^sup>*" and "(Q, R) \<in> indRelL\<^sup>*"
    thus "(P, R) \<in> indRelL\<^sup>*"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> indRelL\<^sup>*"
  thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L Q"
  proof induct
    show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L P"
        using indRelLPO_refl
        unfolding refl_on_def
      by simp
  next
    case (step Q R)
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L Q"
    moreover assume "Q \<R>\<lbrakk>\<cdot>\<rbrakk>L R"
    hence "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L R"
      by (induct, simp add: indRelLPO.encL)
    ultimately show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L R"
      by (simp add: indRelLPO.trans[of P Q R])
  qed
qed

text \<open>The relations indRelR and indRelL are dual. indRelR preserves some predicate iff indRelL
        reflects it. indRelR reflects some predicate iff indRelL reflects it. indRelR respects some
        predicate iff indRelL does.\<close>

lemma (in encoding) indRelR_preserves_pred_iff_indRelL_reflects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "rel_preserves_pred indRelR Pred = rel_reflects_pred indRelL Pred"
proof
  assume preservation: "rel_preserves_pred indRelR Pred"
  show "rel_reflects_pred indRelL Pred"
  proof clarify
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>L Q"
    from this obtain S where "S \<in>S Q" and "\<lbrakk>S\<rbrakk> \<in>T P"
      by (induct, blast)
    hence "Q \<R>\<lbrakk>\<cdot>\<rbrakk>R P"
      by (simp add: indRelR.encR)
    moreover assume "Pred Q"
    ultimately show "Pred P"
        using preservation
      by blast
  qed
next
  assume reflection: "rel_reflects_pred indRelL Pred"
  show "rel_preserves_pred indRelR Pred"
  proof clarify
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q"
    from this obtain S where "S \<in>S P" and "\<lbrakk>S\<rbrakk> \<in>T Q"
      by (induct, blast)
    hence "Q \<R>\<lbrakk>\<cdot>\<rbrakk>L P"
      by (simp add: indRelL.encL)
    moreover assume "Pred P"
    ultimately show "Pred Q"
        using reflection
      by blast
  qed
qed

lemma (in encoding) indRelR_preserves_binary_pred_iff_indRelL_reflects_binary_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "rel_preserves_binary_pred indRelR Pred = rel_reflects_binary_pred indRelL Pred"
proof
  assume preservation: "rel_preserves_binary_pred indRelR Pred"
  show "rel_reflects_binary_pred indRelL Pred"
  proof clarify
    fix P Q x
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>L Q"
    from this obtain S where "S \<in>S Q" and "\<lbrakk>S\<rbrakk> \<in>T P"
      by (induct, blast)
    hence "Q \<R>\<lbrakk>\<cdot>\<rbrakk>R P"
      by (simp add: indRelR.encR)
    moreover assume "Pred Q x"
    ultimately show "Pred P x"
        using preservation
      by blast
  qed
next
  assume reflection: "rel_reflects_binary_pred indRelL Pred"
  show "rel_preserves_binary_pred indRelR Pred"
  proof clarify
    fix P Q x
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q"
    from this obtain S where "S \<in>S P" and "\<lbrakk>S\<rbrakk> \<in>T Q"
      by (induct, blast)
    hence "Q \<R>\<lbrakk>\<cdot>\<rbrakk>L P"
      by (simp add: indRelL.encL)
    moreover assume "Pred P x"
    ultimately show "Pred Q x"
        using reflection
      by blast
  qed
qed

lemma (in encoding) indRelR_reflects_pred_iff_indRelL_preserves_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "rel_reflects_pred indRelR Pred = rel_preserves_pred indRelL Pred"
proof
  assume reflection: "rel_reflects_pred indRelR Pred"
  show "rel_preserves_pred indRelL Pred"
  proof clarify
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>L Q"
    from this obtain S where "S \<in>S Q" and "\<lbrakk>S\<rbrakk> \<in>T P"
      by (induct, blast)
    hence "Q \<R>\<lbrakk>\<cdot>\<rbrakk>R P"
      by (simp add: indRelR.encR)
    moreover assume "Pred P"
    ultimately show "Pred Q"
        using reflection
      by blast
  qed
next
  assume preservation: "rel_preserves_pred indRelL Pred"
  show "rel_reflects_pred indRelR Pred"
  proof clarify
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q"
    from this obtain S where "S \<in>S P" and "\<lbrakk>S\<rbrakk> \<in>T Q"
      by (induct, blast)
    hence "Q \<R>\<lbrakk>\<cdot>\<rbrakk>L P"
      by (simp add: indRelL.encL)
    moreover assume "Pred Q"
    ultimately show "Pred P"
        using preservation
      by blast
  qed
qed

lemma (in encoding) indRelR_reflects_binary_pred_iff_indRelL_preserves_binary_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "rel_reflects_binary_pred indRelR Pred = rel_preserves_binary_pred indRelL Pred"
proof
  assume reflection: "rel_reflects_binary_pred indRelR Pred"
  show "rel_preserves_binary_pred indRelL Pred"
  proof clarify
    fix P Q x
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>L Q"
    from this obtain S where "S \<in>S Q" and "\<lbrakk>S\<rbrakk> \<in>T P"
      by (induct, blast)
    hence "Q \<R>\<lbrakk>\<cdot>\<rbrakk>R P"
      by (simp add: indRelR.encR)
    moreover assume "Pred P x"
    ultimately show "Pred Q x"
        using reflection
      by blast
  qed
next
  assume preservation: "rel_preserves_binary_pred indRelL Pred"
  show "rel_reflects_binary_pred indRelR Pred"
  proof clarify
    fix P Q x
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q"
    from this obtain S where "S \<in>S P" and "\<lbrakk>S\<rbrakk> \<in>T Q"
      by (induct, blast)
    hence "Q \<R>\<lbrakk>\<cdot>\<rbrakk>L P"
      by (simp add: indRelL.encL)
    moreover assume "Pred Q x"
    ultimately show "Pred P x"
        using preservation
      by blast
  qed
qed

lemma (in encoding) indRelR_respects_pred_iff_indRelL_respects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "rel_respects_pred indRelR Pred = rel_respects_pred indRelL Pred"
      using indRelR_preserves_pred_iff_indRelL_reflects_pred[where Pred="Pred"]
            indRelR_reflects_pred_iff_indRelL_preserves_pred[where Pred="Pred"]
    by blast

lemma (in encoding) indRelR_respects_binary_pred_iff_indRelL_respects_binary_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow>'b \<Rightarrow> bool"
  shows "rel_respects_binary_pred indRelR Pred = rel_respects_binary_pred indRelL Pred"
      using indRelR_preserves_binary_pred_iff_indRelL_reflects_binary_pred[where Pred="Pred"]
            indRelR_reflects_binary_pred_iff_indRelL_preserves_binary_pred[where Pred="Pred"]
    by blast

lemma (in encoding) indRelR_cond_preservation_iff_indRelL_cond_reflection:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "(\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_preserves_pred Rel Pred)
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_reflects_pred Rel Pred)"
proof
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_preserves_pred Rel Pred"
  then obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                    and A2: "rel_preserves_pred Rel Pred"
    by blast
  from A1 have "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover from A2 have "rel_reflects_pred (Rel\<inverse>) Pred"
    by simp
  ultimately show "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_reflects_pred Rel Pred"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_reflects_pred Rel Pred"
  then obtain Rel where B1: "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
                    and B2: "rel_reflects_pred Rel Pred"
    by blast
  from B1 have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel\<inverse>"
    by simp
  moreover from B2 have "rel_preserves_pred (Rel\<inverse>) Pred"
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_preserves_pred Rel Pred"
    by blast
qed

lemma (in encoding) indRelR_cond_binary_preservation_iff_indRelL_cond_binary_reflection:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "(\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_preserves_binary_pred Rel Pred)
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
            \<and> rel_reflects_binary_pred Rel Pred)"
proof
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_preserves_binary_pred Rel Pred"
  then obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                    and A2: "rel_preserves_binary_pred Rel Pred"
    by blast
  from A1 have "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover from A2 have "rel_reflects_binary_pred (Rel\<inverse>) Pred"
    by simp
  ultimately
  show "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_reflects_binary_pred Rel Pred"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_reflects_binary_pred Rel Pred"
  then obtain Rel where B1: "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
                    and B2: "rel_reflects_binary_pred Rel Pred"
    by blast
  from B1 have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel\<inverse>"
    by simp
  moreover from B2 have "rel_preserves_binary_pred (Rel\<inverse>) Pred"
    by simp
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_preserves_binary_pred Rel Pred"
    by blast
qed

lemma (in encoding) indRelR_cond_reflection_iff_indRelL_cond_preservation:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "(\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_pred Rel Pred)
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_preserves_pred Rel Pred)"
proof
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_pred Rel Pred"
  then obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                    and A2: "rel_reflects_pred Rel Pred"
    by blast
  from A1 have "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover from A2 have "rel_preserves_pred (Rel\<inverse>) Pred"
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_preserves_pred Rel Pred"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_preserves_pred Rel Pred"
  then obtain Rel where B1: "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
                    and B2: "rel_preserves_pred Rel Pred"
    by blast
  from B1 have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel\<inverse>"
    by simp
  moreover from B2 have "rel_reflects_pred (Rel\<inverse>) Pred"
    by simp
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_pred Rel Pred"
    by blast
qed

lemma (in encoding) indRelR_cond_binary_reflection_iff_indRelL_cond_binary_preservation:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "(\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_binary_pred Rel Pred)
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
            \<and> rel_preserves_binary_pred Rel Pred)"
proof
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_binary_pred Rel Pred"
  then obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                    and A2: "rel_reflects_binary_pred Rel Pred"
    by blast
  from A1 have "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel\<inverse>"
    by simp
  moreover from A2 have "rel_preserves_binary_pred (Rel\<inverse>) Pred"
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_preserves_binary_pred Rel Pred"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_preserves_binary_pred Rel Pred"
  then obtain Rel where B1: "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
                    and B2: "rel_preserves_binary_pred Rel Pred"
    by blast
  from B1 have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel\<inverse>"
    by simp
  moreover from B2 have "rel_reflects_binary_pred (Rel\<inverse>) Pred"
    by simp
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_binary_pred Rel Pred"
    by blast
qed

lemma (in encoding) indRelR_cond_respection_iff_indRelL_cond_respection:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "(\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel Pred)
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_respects_pred Rel Pred)"
proof
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel Pred"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                         and A2: "rel_respects_pred Rel Pred"
    by blast
  from A1 have "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> {(a, b). (b, a) \<in> Rel}"
    by simp
  moreover from A2 have "rel_respects_pred {(a, b). (b, a) \<in> Rel} Pred"
    by blast
  ultimately show "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_respects_pred Rel Pred"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_respects_pred Rel Pred"
  from this obtain Rel where A1: "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
                         and A2: "rel_respects_pred Rel Pred"
    by blast
  from A1 have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> {(a, b). (b, a) \<in> Rel}"
    by simp
  moreover from A2 have "rel_respects_pred {(a, b). (b, a) \<in> Rel} Pred"
    by blast
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel Pred"
    by blast
qed

lemma (in encoding) indRelR_cond_binary_respection_iff_indRelL_cond_binary_respection:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "(\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_binary_pred Rel Pred)
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
            \<and> rel_respects_binary_pred Rel Pred)"
proof
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_binary_pred Rel Pred"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                         and A2: "rel_respects_binary_pred Rel Pred"
    by blast
  from A1 have "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> {(a, b). (b, a) \<in> Rel}"
    by simp
  moreover from A2 have "rel_respects_binary_pred {(a, b). (b, a) \<in> Rel} Pred"
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_respects_binary_pred Rel Pred"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_respects_binary_pred Rel Pred"
  from this obtain Rel where A1: "\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
                         and A2: "rel_respects_binary_pred Rel Pred"
    by blast
  from A1 have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> {(a, b). (b, a) \<in> Rel}"
    by simp
  moreover from A2 have "rel_respects_binary_pred {(a, b). (b, a) \<in> Rel} Pred"
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_binary_pred Rel Pred"
    by blast
qed

text \<open>An encoding preserves, reflects, or respects a predicate iff indRelL reflects, preserves,
        or respects this predicate.\<close>

lemma (in encoding) enc_preserves_pred_iff_indRelL_reflects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_preserves_pred Pred = rel_reflects_pred indRelL Pred"
      using enc_preserves_pred_iff_indRelR_preserves_pred[where Pred="Pred"]
            indRelR_preserves_pred_iff_indRelL_reflects_pred[where Pred="Pred"]
    by blast

lemma (in encoding) enc_reflects_pred_iff_indRelL_preserves_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_reflects_pred Pred = rel_preserves_pred indRelL Pred"
      using enc_reflects_pred_iff_indRelR_reflects_pred[where Pred="Pred"]
            indRelR_reflects_pred_iff_indRelL_preserves_pred[where Pred="Pred"]
    by blast

lemma (in encoding) enc_respects_pred_iff_indRelL_respects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_respects_pred Pred = rel_respects_pred indRelL Pred"
      using enc_preserves_pred_iff_indRelL_reflects_pred[where Pred="Pred"]
            enc_reflects_pred_iff_indRelL_preserves_pred[where Pred="Pred"]
    by blast

text \<open>An encoding preserves, reflects, or respects a predicate iff there exists a relation,
        namely indRelL, that relates literal translations with their source terms and reflects,
        preserves, or respects this predicate.\<close>

lemma (in encoding) enc_preserves_pred_iff_source_target_rel_reflects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_preserves_pred Pred
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_reflects_pred Rel Pred)"
      using enc_preserves_pred_iff_source_target_rel_preserves_pred[where Pred="Pred"]
            indRelR_cond_preservation_iff_indRelL_cond_reflection[where Pred="Pred"]
    by simp

lemma (in encoding) enc_reflects_pred_iff_source_target_rel_preserves_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_reflects_pred Pred
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_preserves_pred Rel Pred)"
      using enc_reflects_pred_iff_source_target_rel_reflects_pred[where Pred="Pred"]
            indRelR_cond_reflection_iff_indRelL_cond_preservation[where Pred="Pred"]
    by simp

lemma (in encoding) enc_respects_pred_iff_source_target_rel_respects_pred_encL:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_respects_pred Pred
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_respects_pred Rel Pred)"
      using enc_respects_pred_iff_source_target_rel_respects_pred_encR[where Pred="Pred"]
            indRelR_cond_respection_iff_indRelL_cond_respection[where Pred="Pred"]
    by simp

text \<open>To analyse the respection of source term behaviours we use relations that contain both kind
        of pairs: (S, enc S) as well as (enc S, S) for all source terms S.\<close>

inductive_set (in encoding) indRel
    :: "((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
  where
  encR: "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRel" |
  encL: "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRel"

abbreviation (in encoding) indRelInfix ::
    "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<R>\<lbrakk>\<cdot>\<rbrakk> _" [75, 75] 80)
  where
  "P \<R>\<lbrakk>\<cdot>\<rbrakk> Q \<equiv> (P, Q) \<in> indRel"

lemma (in encoding) indRel_symm:
  shows "sym indRel"
      unfolding sym_def
    by (auto simp add: indRel.simps indRel.encR indRel.encL)

inductive_set (in encoding) indRelEQ
    :: "((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
  where
  encR:   "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelEQ" |
  encL:   "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelEQ" |
  target: "(TargetTerm T, TargetTerm T) \<in> indRelEQ" |
  trans:  "\<lbrakk>(P, Q) \<in> indRelEQ; (Q, R) \<in> indRelEQ\<rbrakk> \<Longrightarrow> (P, R) \<in> indRelEQ"

abbreviation (in encoding) indRelEQinfix ::
    "('procS, 'procT) Proc \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<sim>\<lbrakk>\<cdot>\<rbrakk> _" [75, 75] 80)
  where
  "P \<sim>\<lbrakk>\<cdot>\<rbrakk> Q \<equiv> (P, Q) \<in> indRelEQ"

lemma (in encoding) indRelEQ_refl:
  shows "refl indRelEQ"
    unfolding refl_on_def
proof auto
  fix P
  show "P \<sim>\<lbrakk>\<cdot>\<rbrakk> P"
  proof (cases P)
    case (SourceTerm SP)
    assume "SP \<in>S P"
    moreover have "SourceTerm SP \<sim>\<lbrakk>\<cdot>\<rbrakk> TargetTerm (\<lbrakk>SP\<rbrakk>)"
      by (rule indRelEQ.encR)
    moreover have "TargetTerm (\<lbrakk>SP\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk> SourceTerm SP"
      by (rule indRelEQ.encL)
    ultimately show "P \<sim>\<lbrakk>\<cdot>\<rbrakk> P"
      by (simp add: indRelEQ.trans[where P="SourceTerm SP" and Q="TargetTerm (\<lbrakk>SP\<rbrakk>)"])
  next
    case (TargetTerm TP)
    assume "TP \<in>T P"
    thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk> P"
      by (simp add: indRelEQ.target)
  qed
qed

lemma (in encoding) indRelEQ_is_preorder:
  shows "preorder indRelEQ"
    unfolding preorder_on_def
proof
  show "refl indRelEQ"
    by (rule indRelEQ_refl)
next
  show "trans indRelEQ"
    unfolding trans_def
  proof clarify
    fix P Q R
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk> R"
    thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk> R"
      by (rule indRelEQ.trans)
  qed
qed

lemma (in encoding) indRelEQ_symm:
  shows "sym indRelEQ"
    unfolding sym_def
proof clarify
  fix P Q
  assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk> Q"
  thus "Q \<sim>\<lbrakk>\<cdot>\<rbrakk> P"
  proof induct
    case (encR S)
    show "TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk> SourceTerm S"
      by (rule indRelEQ.encL)
  next
    case (encL S)
    show "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelEQ.encR)
  next
    case (target T)
    show "TargetTerm T \<sim>\<lbrakk>\<cdot>\<rbrakk> TargetTerm T"
      by (rule indRelEQ.target)
  next
    case (trans P Q R)
    assume "R \<sim>\<lbrakk>\<cdot>\<rbrakk> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk> P"
    thus "R \<sim>\<lbrakk>\<cdot>\<rbrakk> P"
      by (rule indRelEQ.trans)
  qed
qed

lemma (in encoding) indRelEQ_is_equivalence:
  shows "equivalence indRelEQ"
      using indRelEQ_is_preorder indRelEQ_symm
      unfolding equiv_def preorder_on_def
    by blast

lemma (in encoding) refl_trans_closure_of_indRel:
  shows "indRelEQ = indRel\<^sup>*"
proof auto
  fix P Q
  assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk> Q"
  thus "(P, Q) \<in> indRel\<^sup>*"
  proof induct
    case (encR S)
    show "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRel\<^sup>*"
        using indRel.encR[of S]
      by simp
  next
    case (encL S)
    show "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRel\<^sup>*"
        using indRel.encL[of S]
      by simp
  next
    case (target T)
    show "(TargetTerm T, TargetTerm T) \<in> indRel\<^sup>*"
      by simp
  next
    case (trans P Q R)
    assume "(P, Q) \<in> indRel\<^sup>*" and "(Q, R) \<in> indRel\<^sup>*"
    thus "(P, R) \<in> indRel\<^sup>*"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> indRel\<^sup>*"
  thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk> Q"
  proof induct
    show "P \<sim>\<lbrakk>\<cdot>\<rbrakk> P"
        using indRelEQ_refl
        unfolding refl_on_def
      by simp
  next
    case (step Q R)
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk> Q"
    moreover assume "Q \<R>\<lbrakk>\<cdot>\<rbrakk> R"
    hence "Q \<sim>\<lbrakk>\<cdot>\<rbrakk> R"
      by (induct, simp_all add: indRelEQ.encR indRelEQ.encL)
    ultimately show "P \<sim>\<lbrakk>\<cdot>\<rbrakk> R"
      by (rule indRelEQ.trans)
  qed
qed

lemma (in encoding) refl_symm_trans_closure_of_indRel:
  shows "indRelEQ = (symcl (indRel\<^sup>=))\<^sup>+"
proof -
  have "(symcl (indRel\<^sup>=))\<^sup>+ = (symcl indRel)\<^sup>*"
    by (rule refl_symm_trans_closure_is_symm_refl_trans_closure[where Rel="indRel"])
  moreover have "symcl indRel = indRel"
    by (simp add: indRel_symm symm_closure_of_symm_rel[where Rel="indRel"])
  ultimately show "indRelEQ = (symcl (indRel\<^sup>=))\<^sup>+"
    by (simp add: refl_trans_closure_of_indRel)
qed

lemma (in encoding) symm_closure_of_indRelR:
  shows "indRel = symcl indRelR"
    and "indRelEQ = (symcl (indRelR\<^sup>=))\<^sup>+"
proof -
  show "indRel = symcl indRelR"
  proof auto
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk> Q"
    thus "(P, Q) \<in> symcl indRelR"
      by (induct, simp_all add: symcl_def indRelR.encR)
  next
    fix P Q
    assume "(P, Q) \<in> symcl indRelR"
    thus "P \<R>\<lbrakk>\<cdot>\<rbrakk> Q"
      by (auto simp add: symcl_def indRelR.simps indRel.encR indRel.encL)
  qed
  thus "indRelEQ = (symcl (indRelR\<^sup>=))\<^sup>+"
      using refl_symm_trans_closure_is_symm_refl_trans_closure[where Rel="indRelR"]
            refl_trans_closure_of_indRel
    by simp
qed

lemma (in encoding) symm_closure_of_indRelL:
  shows "indRel = symcl indRelL"
    and "indRelEQ = (symcl (indRelL\<^sup>=))\<^sup>+"
proof -
  show "indRel = symcl indRelL"
  proof auto
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk> Q"
    thus "(P, Q) \<in> symcl indRelL"
     by (induct, simp_all add: symcl_def indRelL.encL)
  next
    fix P Q
    assume "(P, Q) \<in> symcl indRelL"
    thus "P \<R>\<lbrakk>\<cdot>\<rbrakk> Q"
      by (auto simp add: symcl_def indRelL.simps indRel.encR indRel.encL)
  qed
  thus "indRelEQ = (symcl (indRelL\<^sup>=))\<^sup>+"
      using refl_symm_trans_closure_is_symm_refl_trans_closure[where Rel="indRelL"]
            refl_trans_closure_of_indRel
    by simp
qed

text \<open>The relation indRel is a combination of indRelL and indRelR. indRel respects a predicate
        iff indRelR (or indRelL) respects it.\<close>

lemma (in encoding) indRel_respects_pred_iff_indRelR_respects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "rel_respects_pred indRel Pred = rel_respects_pred indRelR Pred"
proof
  assume respection: "rel_respects_pred indRel Pred"
  show "rel_respects_pred indRelR Pred"
  proof auto
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q"
    from this obtain S where "S \<in>S P" and "\<lbrakk>S\<rbrakk> \<in>T Q"
      by (induct, blast)
    hence "P \<R>\<lbrakk>\<cdot>\<rbrakk> Q"
      by (simp add: indRel.encR)
    moreover assume "Pred P"
    ultimately show "Pred Q"
        using respection
      by blast
  next
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q"
    from this obtain S where "S \<in>S P" and "\<lbrakk>S\<rbrakk> \<in>T Q"
      by (induct, blast)
    hence "P \<R>\<lbrakk>\<cdot>\<rbrakk> Q"
      by (simp add: indRel.encR)
    moreover assume "Pred Q"
    ultimately show "Pred P"
        using respection
      by blast
  qed
next
  assume "rel_respects_pred indRelR Pred"
  thus "rel_respects_pred indRel Pred"
      using symm_closure_of_indRelR(1)
            respection_and_closures(2)[where Rel="indRelR" and Pred="Pred"]
    by blast
qed

lemma (in encoding) indRel_respects_binary_pred_iff_indRelR_respects_binary_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "rel_respects_binary_pred indRel Pred = rel_respects_binary_pred indRelR Pred"
proof
  assume respection: "rel_respects_binary_pred indRel Pred"
  show "rel_respects_binary_pred indRelR Pred"
  proof auto
    fix P Q x
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q"
    from this obtain S where "S \<in>S P" and "\<lbrakk>S\<rbrakk> \<in>T Q"
      by (induct, blast)
    hence "P \<R>\<lbrakk>\<cdot>\<rbrakk> Q"
      by (simp add: indRel.encR)
    moreover assume "Pred P x"
    ultimately show "Pred Q x"
        using respection
      by blast
  next
    fix P Q x
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>R Q"
    from this obtain S where "S \<in>S P" and "\<lbrakk>S\<rbrakk> \<in>T Q"
      by (induct, blast)
    hence "P \<R>\<lbrakk>\<cdot>\<rbrakk> Q"
      by (simp add: indRel.encR)
    moreover assume "Pred Q x"
    ultimately show "Pred P x"
        using respection
      by blast
  qed
next
  assume "rel_respects_binary_pred indRelR Pred"
  thus "rel_respects_binary_pred indRel Pred"
      using symm_closure_of_indRelR(1)
            respection_of_binary_predicates_and_closures(2)[where Rel="indRelR" and Pred="Pred"]
    by blast
qed

lemma (in encoding) indRel_cond_respection_iff_indRelR_cond_respection:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "(\<exists>Rel.
          (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
          \<and> rel_respects_pred Rel Pred)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel Pred)"
proof
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
          \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_respects_pred Rel Pred"
  from this obtain Rel
    where "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
    and "rel_respects_pred Rel Pred"
    by blast
  thus "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel Pred"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel Pred"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                         and A2: "rel_respects_pred Rel Pred"
    by blast
  from A1 have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> symcl Rel
                \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> symcl Rel"
    by (simp add: symcl_def)
  moreover from A2 have "rel_respects_pred (symcl Rel) Pred"
      using respection_and_closures(2)[where Rel="Rel" and Pred="Pred"]
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
        \<and> rel_respects_pred Rel Pred"
    by blast
qed

lemma (in encoding) indRel_cond_binary_respection_iff_indRelR_cond_binary_respection:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> 'b \<Rightarrow> bool"
  shows "(\<exists>Rel.
          (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
          \<and> rel_respects_binary_pred Rel Pred)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_respects_binary_pred Rel Pred)"
proof
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel
          \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel) \<and> rel_respects_binary_pred Rel Pred"
  from this obtain Rel
    where "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
    and "rel_respects_binary_pred Rel Pred"
    by blast
  thus "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_binary_pred Rel Pred"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_binary_pred Rel Pred"
  from this obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
                         and A2: "rel_respects_binary_pred Rel Pred"
    by blast
  from A1 have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> symcl Rel
                \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> symcl Rel"
    by (simp add: symcl_def)
  moreover from A2 have "rel_respects_binary_pred (symcl Rel) Pred"
      using respection_of_binary_predicates_and_closures(2)[where Rel="Rel" and Pred="Pred"]
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
        \<and> rel_respects_binary_pred Rel Pred"
    by blast
qed

text \<open>An encoding respects a predicate iff indRel respects this predicate.\<close>

lemma (in encoding) enc_respects_pred_iff_indRel_respects_pred:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_respects_pred Pred = rel_respects_pred indRel Pred"
      using enc_respects_pred_iff_indRelR_respects_pred[where Pred="Pred"]
            indRel_respects_pred_iff_indRelR_respects_pred[where Pred="Pred"]
    by simp

text \<open>An encoding respects a predicate iff there exists a relation, namely indRel, that relates
        source terms and their literal translations in both directions and respects this predicate.
\<close>

lemma (in encoding) enc_respects_pred_iff_source_target_rel_respects_pred_encRL:
  fixes Pred :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "enc_respects_pred Pred
         = (\<exists>Rel.
            (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
            \<and> rel_respects_pred Rel Pred)"
      using enc_respects_pred_iff_source_target_rel_respects_pred_encR[where Pred="Pred"]
            indRel_cond_respection_iff_indRelR_cond_respection[where Pred="Pred"]
    by simp

subsection \<open>Relations Induced by the Encoding and a Relation on Target Terms\<close>

text \<open>Some encodability like e.g. operational correspondence are defined w.r.t. a relation on
        target terms. To analyse such criteria we include the respective target term relation in
        the considered relation on the disjoint union of source and target terms.\<close>

inductive_set (in encoding) indRelRT
    :: "('procT \<times> 'procT) set \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for TRel :: "('procT \<times> 'procT) set"
  where
  encR:   "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRT TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelRT TRel"

abbreviation (in encoding) indRelRTinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procT \<times> 'procT) set \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"
       ("_ \<R>\<lbrakk>\<cdot>\<rbrakk>RT<_> _" [75, 75, 75] 80)
  where
  "P \<R>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q \<equiv> (P, Q) \<in> indRelRT TRel"

inductive_set (in encoding) indRelRTPO
    :: "('procT \<times> 'procT) set \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for TRel :: "('procT \<times> 'procT) set"
  where
  encR:   "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRTPO TRel" |
  source: "(SourceTerm S, SourceTerm S) \<in> indRelRTPO TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelRTPO TRel" |
  trans:  "\<lbrakk>(P, Q) \<in> indRelRTPO TRel; (Q, R) \<in> indRelRTPO TRel\<rbrakk> \<Longrightarrow> (P, R) \<in> indRelRTPO TRel"

abbreviation (in encoding) indRelRTPOinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procT \<times> 'procT) set \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"
       ("_ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<_> _" [75, 75, 75] 80)
  where
  "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q \<equiv> (P, Q) \<in> indRelRTPO TRel"

lemma (in encoding) indRelRTPO_refl:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes refl: "refl TRel"
  shows "refl (indRelRTPO TRel)"
    unfolding refl_on_def
proof auto
  fix P
  show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P"
  proof (cases P)
    case (SourceTerm SP)
    assume "SP \<in>S P"
    thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P"
      by (simp add: indRelRTPO.source)
  next
    case (TargetTerm TP)
    assume "TP \<in>T P"
    with refl show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P"
        unfolding refl_on_def
      by (simp add: indRelRTPO.target)
  qed
qed

lemma (in encoding) refl_trans_closure_of_indRelRT:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes refl: "refl TRel"
  shows "indRelRTPO TRel = (indRelRT TRel)\<^sup>*"
proof auto
  fix P Q
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
  thus "(P, Q) \<in> (indRelRT TRel)\<^sup>*"
  proof induct
    case (encR S)
    show "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> (indRelRT TRel)\<^sup>*"
        using indRelRT.encR[of S TRel]
      by simp
  next
    case (source S)
    show "(SourceTerm S, SourceTerm S) \<in> (indRelRT TRel)\<^sup>*"
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    thus "(TargetTerm T1, TargetTerm T2) \<in> (indRelRT TRel)\<^sup>*"
        using indRelRT.target[of T1 T2 TRel]
      by simp
  next
    case (trans P Q R)
    assume "(P, Q) \<in> (indRelRT TRel)\<^sup>*" and "(Q, R) \<in> (indRelRT TRel)\<^sup>*"
    thus "(P, R) \<in> (indRelRT TRel)\<^sup>*"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> (indRelRT TRel)\<^sup>*"
  thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
  proof induct
    from refl show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> P"
        using indRelRTPO_refl[of TRel]
        unfolding refl_on_def
      by simp
  next
    case (step Q R)
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
    moreover assume "Q \<R>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
    hence "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
      by (induct, simp_all add: indRelRTPO.encR indRelRTPO.target)
    ultimately show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
      by (rule indRelRTPO.trans)
  qed
qed

lemma (in encoding) indRelRTPO_is_preorder:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes reflT: "refl TRel"
  shows "preorder (indRelRTPO TRel)"
    unfolding preorder_on_def
proof
  from reflT show "refl (indRelRTPO TRel)"
    by (rule indRelRTPO_refl)
next
  show "trans (indRelRTPO TRel)"
    unfolding trans_def
  proof clarify
    fix P Q R
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
    thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> R"
        using indRelRTPO.trans
      by blast
  qed
qed

lemma (in encoding) transitive_closure_of_TRel_to_indRelRTPO:
  fixes TRel  :: "('procT \<times> 'procT) set"
    and TP TQ :: "'procT"
  shows "(TP, TQ) \<in> TRel\<^sup>+ \<Longrightarrow> TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
proof -
  assume "(TP, TQ) \<in> TRel\<^sup>+"
  thus "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
  proof induct
    fix TQ
    assume "(TP, TQ) \<in> TRel"
    thus "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
      by (rule indRelRTPO.target)
  next
    case (step TQ TR)
    assume "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
    moreover assume "(TQ, TR) \<in> TRel"
    hence "TargetTerm TQ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
      by (simp add: indRelRTPO.target)
    ultimately show "TargetTerm TP \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TR"
      by (rule indRelRTPO.trans)
  qed
qed

text \<open>The relation indRelRT is the smallest relation that relates all source terms and their
        literal translations and contains TRel. Thus there exists a relation that relates source
        terms and their literal translations and satisfies some predicate on its pairs iff the
        predicate holds for the pairs of indRelR.\<close>

lemma (in encoding) indRelR_modulo_pred_impl_indRelRT_modulo_pred:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  shows "(\<forall>(P, Q) \<in> indRelR. Pred (P, Q)) = (\<forall>TRel. (\<forall>(TP, TQ) \<in> TRel.
         Pred (TargetTerm TP, TargetTerm TQ)) \<longleftrightarrow> (\<forall>(P, Q) \<in> indRelRT TRel. Pred (P, Q)))"
proof (rule iffI)
  assume A: "\<forall>(P, Q) \<in> indRelR. Pred (P, Q)"
  show "\<forall>TRel. (\<forall>(TP, TQ) \<in> TRel. Pred (TargetTerm TP, TargetTerm TQ))
        = (\<forall>(P, Q) \<in> indRelRT TRel. Pred (P, Q))"
  proof (rule allI, rule iffI)
    fix TRel
    assume "\<forall>(TP, TQ) \<in> TRel. Pred (TargetTerm TP, TargetTerm TQ)"
    with A show "\<forall>(P, Q) \<in> indRelRT TRel. Pred (P, Q)"
      by (auto simp add: indRelR.encR indRelRT.simps)
  next
    fix TRel
    assume "\<forall>(P, Q) \<in> indRelRT TRel. Pred (P, Q)"
    thus "\<forall>(TP, TQ) \<in> TRel. Pred (TargetTerm TP, TargetTerm TQ)"
      by (auto simp add: indRelRT.target)
  qed
next
  assume "\<forall>TRel. (\<forall>(TP, TQ) \<in> TRel. Pred (TargetTerm TP, TargetTerm TQ))
          \<longleftrightarrow> (\<forall>(P, Q) \<in> indRelRT TRel. Pred (P, Q))"
  hence B: "\<And>TRel. (\<forall>(TP, TQ) \<in> TRel. Pred (TargetTerm TP, TargetTerm TQ))
            \<longleftrightarrow> (\<forall>(P, Q) \<in> indRelRT TRel. Pred (P, Q))"
    by blast
  have "\<And>S. Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>))"
      using B[of "{}"]
    by (simp add: indRelRT.simps)
  thus "\<forall>(P, Q) \<in> indRelR. Pred (P, Q)"
    by (auto simp add: indRelR.simps)
qed

lemma (in encoding) indRelRT_iff_exists_source_target_relation:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  shows "(\<forall>TRel. (\<forall>(TP, TQ) \<in> TRel. Pred (TargetTerm TP, TargetTerm TQ))
          \<longleftrightarrow> (\<forall>(P, Q) \<in> indRelRT TRel. Pred (P, Q)))
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> (\<forall>(P, Q) \<in> Rel. Pred (P, Q)))"
      using indRelR_iff_exists_source_target_relation[where Pred="Pred"]
            indRelR_modulo_pred_impl_indRelRT_modulo_pred[where Pred="Pred"]
    by simp

lemma (in encoding) indRelRT_modulo_pred_impl_indRelRTPO_modulo_pred:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  assumes reflCond:  "\<forall>P. Pred (P, P)"
      and transCond: "\<forall>P Q R. Pred (P, Q) \<and> Pred (Q, R) \<longrightarrow> Pred (P, R)"
  shows "(\<forall>(P, Q) \<in> indRelRT TRel. Pred (P, Q)) = (\<forall>(P, Q) \<in> indRelRTPO TRel. Pred (P, Q))"
proof auto
  fix P Q
  assume A: "\<forall>x \<in> indRelRT TRel. Pred x"
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
  thus "Pred (P, Q)"
  proof induct
    case (encR S)
    have "SourceTerm S \<R>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (simp add: indRelRT.encR)
    with A show "Pred (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>))"
      by simp
  next
    case (source S)
    from reflCond show "Pred (SourceTerm S, SourceTerm S)"
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    hence "TargetTerm T1 \<R>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
      by (simp add: indRelRT.target)
    with A show "Pred (TargetTerm T1, TargetTerm T2)"
      by simp
  next
    case (trans P Q R)
    assume "Pred (P, Q)" and "Pred (Q, R)"
    with transCond show "Pred (P, R)"
      by blast
  qed
next
  fix P Q
  assume "\<forall>x \<in> indRelRTPO TRel. Pred x" and "P \<R>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
  thus "Pred (P, Q)"
    by (auto simp add: indRelRTPO.encR indRelRTPO.target indRelRT.simps)
qed

lemma (in encoding) indRelR_modulo_pred_impl_indRelRTPO_modulo_pred:
  fixes Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) \<Rightarrow> bool"
  assumes "\<forall>P. Pred (P, P)"
      and "\<forall>P Q R. Pred (P, Q) \<and> Pred (Q, R) \<longrightarrow> Pred (P, R)"
  shows "(\<forall>(P, Q) \<in> indRelR. Pred (P, Q))
         = (\<forall>TRel. (\<forall>(TP, TQ) \<in> TRel. Pred (TargetTerm TP, TargetTerm TQ))
            \<longleftrightarrow> (\<forall>(P, Q) \<in> indRelRTPO TRel. Pred (P, Q)))"
proof -
  have "(\<forall>(P, Q)\<in>indRelR. Pred (P, Q)) = (\<forall>TRel. (\<forall>(TP, TQ) \<in> TRel.
        Pred (TargetTerm TP, TargetTerm TQ)) \<longleftrightarrow> (\<forall>(P, Q) \<in> indRelRT TRel. Pred (P, Q)))"
      using indRelR_modulo_pred_impl_indRelRT_modulo_pred[where Pred="Pred"]
    by simp
  moreover
  have "\<forall>TRel. (\<forall>(P, Q)\<in>indRelRT TRel. Pred (P, Q)) = (\<forall>(P, Q)\<in>indRelRTPO TRel. Pred (P, Q))"
      using assms indRelRT_modulo_pred_impl_indRelRTPO_modulo_pred[where Pred="Pred"]
    by blast
  ultimately show ?thesis
    by simp
qed

text \<open>The relation indRelLT includes TRel and relates literal translations and their source
        terms.\<close>

inductive_set (in encoding) indRelLT
    :: "('procT \<times> 'procT) set \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for TRel :: "('procT \<times> 'procT) set"
  where
  encL:   "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelLT TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelLT TRel"

abbreviation (in encoding) indRelLTinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procT \<times> 'procT) set \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"
       ("_ \<R>\<lbrakk>\<cdot>\<rbrakk>LT<_> _" [75, 75, 75] 80)
  where
  "P \<R>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> Q \<equiv> (P, Q) \<in> indRelLT TRel"

inductive_set (in encoding) indRelLTPO
    :: "('procT \<times> 'procT) set \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for TRel :: "('procT \<times> 'procT) set"
  where
  encL:   "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelLTPO TRel" |
  source: "(SourceTerm S, SourceTerm S) \<in> indRelLTPO TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelLTPO TRel" |
  trans:  "\<lbrakk>(P, Q) \<in> indRelLTPO TRel; (Q, R) \<in> indRelLTPO TRel\<rbrakk> \<Longrightarrow> (P, R) \<in> indRelLTPO TRel"

abbreviation (in encoding) indRelLTPOinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procT \<times> 'procT) set \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"
       ("_ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<_> _" [75, 75, 75] 80)
  where
  "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> Q \<equiv> (P, Q) \<in> indRelLTPO TRel"

lemma (in encoding) indRelLTPO_refl:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes refl: "refl TRel"
  shows "refl (indRelLTPO TRel)"
    unfolding refl_on_def
proof auto
  fix P
  show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> P"
  proof (cases P)
    case (SourceTerm SP)
    assume "SP \<in>S P"
    thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> P"
      by (simp add: indRelLTPO.source)
  next
    case (TargetTerm TP)
    assume "TP \<in>T P"
    with refl show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> P"
        using indRelLTPO.target[of TP TP TRel]
        unfolding refl_on_def
      by simp
  qed
qed

lemma (in encoding) refl_trans_closure_of_indRelLT:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes refl: "refl TRel"
  shows "indRelLTPO TRel = (indRelLT TRel)\<^sup>*"
proof auto
  fix P Q
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> Q"
  thus "(P, Q) \<in> (indRelLT TRel)\<^sup>*"
  proof induct
    case (encL S)
    show "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> (indRelLT TRel)\<^sup>*"
        using indRelLT.encL[of S TRel]
      by simp
  next
    case (source S)
    show "(SourceTerm S, SourceTerm S) \<in> (indRelLT TRel)\<^sup>*"
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    thus "(TargetTerm T1, TargetTerm T2) \<in> (indRelLT TRel)\<^sup>*"
        using indRelLT.target[of T1 T2 TRel]
      by simp
  next
    case (trans P Q R)
    assume "(P, Q) \<in> (indRelLT TRel)\<^sup>*" and "(Q, R) \<in> (indRelLT TRel)\<^sup>*"
    thus "(P, R) \<in> (indRelLT TRel)\<^sup>*"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> (indRelLT TRel)\<^sup>*"
  thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> Q"
  proof induct
    from refl show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> P"
        using indRelLTPO_refl[of TRel]
        unfolding refl_on_def
      by simp
  next
    case (step Q R)
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> Q"
    moreover assume "Q \<R>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> R"
    hence "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> R"
      by (induct, simp_all add: indRelLTPO.encL indRelLTPO.target)
    ultimately show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> R"
      by (rule indRelLTPO.trans)
  qed
qed

inductive_set (in encoding) indRelT
    :: "('procT \<times> 'procT) set \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for TRel :: "('procT \<times> 'procT) set"
  where
  encR:   "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelT TRel" |
  encL:   "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelT TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelT TRel"

abbreviation (in encoding) indRelTinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procT \<times> 'procT) set \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"
       ("_ \<R>\<lbrakk>\<cdot>\<rbrakk>T<_> _" [75, 75, 75] 80)
  where
  "P \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q \<equiv> (P, Q) \<in> indRelT TRel"

lemma (in encoding) indRelT_symm:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes symm: "sym TRel"
  shows "sym (indRelT TRel)"
    unfolding sym_def
proof clarify
  fix P Q
  assume "(P, Q) \<in> indRelT TRel"
  thus "(Q, P) \<in> indRelT TRel"
      using symm
      unfolding sym_def
    by (induct, simp_all add: indRelT.encL indRelT.encR indRelT.target)
qed

inductive_set (in encoding) indRelTEQ
    :: "('procT \<times> 'procT) set \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for TRel :: "('procT \<times> 'procT) set"
  where
  encR:   "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelTEQ TRel" |
  encL:   "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelTEQ TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelTEQ TRel" |
  trans:  "\<lbrakk>(P, Q) \<in> indRelTEQ TRel; (Q, R) \<in> indRelTEQ TRel\<rbrakk> \<Longrightarrow> (P, R) \<in> indRelTEQ TRel"

abbreviation (in encoding) indRelTEQinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procT \<times> 'procT) set \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool"
       ("_ \<sim>\<lbrakk>\<cdot>\<rbrakk>T<_> _" [75, 75, 75] 80)
  where
  "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q \<equiv> (P, Q) \<in> indRelTEQ TRel"

lemma (in encoding) indRelTEQ_refl:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes refl: "refl TRel"
  shows "refl (indRelTEQ TRel)"
    unfolding refl_on_def
proof auto
  fix P
  show "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P"
  proof (cases P)
    case (SourceTerm SP)
    assume "SP \<in>S P"
    moreover have "SourceTerm SP \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>SP\<rbrakk>)"
      by (rule indRelTEQ.encR)
    moreover have "TargetTerm (\<lbrakk>SP\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm SP"
      by (rule indRelTEQ.encL)
    ultimately show "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P"
      by (simp add: indRelTEQ.trans[where P="SourceTerm SP" and Q="TargetTerm (\<lbrakk>SP\<rbrakk>)"])
  next
    case (TargetTerm TP)
    assume "TP \<in>T P"
    with refl show "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P"
        unfolding refl_on_def
      by (simp add: indRelTEQ.target)
  qed
qed

lemma (in encoding) indRelTEQ_symm:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes symm: "sym TRel"
  shows "sym (indRelTEQ TRel)"
    unfolding sym_def
proof clarify
  fix P Q
  assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q"
  thus "Q \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P"
  proof induct
    case (encR S)
    show "TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S"
      by (rule indRelTEQ.encL)
  next
    case (encL S)
    show "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelTEQ.encR)
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    with symm show "TargetTerm T2 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T1"
        unfolding sym_def
      by (simp add: indRelTEQ.target)
  next
    case (trans P Q R)
    assume "R \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P"
    thus "R \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P"
      by (rule indRelTEQ.trans)
  qed
qed

lemma (in encoding) refl_trans_closure_of_indRelT:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes refl: "refl TRel"
  shows "indRelTEQ TRel = (indRelT TRel)\<^sup>*"
proof auto
  fix P Q
  assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q"
  thus "(P, Q) \<in> (indRelT TRel)\<^sup>*"
  proof induct
    case (encR S)
    show "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> (indRelT TRel)\<^sup>*"
        using indRelT.encR[of S TRel]
      by simp
  next
    case (encL S)
    show "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> (indRelT TRel)\<^sup>*"
        using indRelT.encL[of S TRel]
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    thus "(TargetTerm T1, TargetTerm T2) \<in> (indRelT TRel)\<^sup>*"
        using indRelT.target[of T1 T2 TRel]
      by simp
  next
    case (trans P Q R)
    assume "(P, Q) \<in> (indRelT TRel)\<^sup>*" and "(Q, R) \<in> (indRelT TRel)\<^sup>*"
    thus "(P, R) \<in> (indRelT TRel)\<^sup>*"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> (indRelT TRel)\<^sup>*"
  thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q"
  proof induct
    from refl show "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> P"
        using indRelTEQ_refl[of TRel]
        unfolding refl_on_def
      by simp
  next
    case (step Q R)
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q"
    moreover assume "Q \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R"
    hence "Q \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R"
      by (induct, simp_all add: indRelTEQ.encR indRelTEQ.encL indRelTEQ.target)
    ultimately show "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> R"
      by (rule indRelTEQ.trans)
  qed
qed

lemma (in encoding) refl_symm_trans_closure_of_indRelT:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes refl: "refl TRel"
      and symm: "sym TRel"
  shows "indRelTEQ TRel = (symcl ((indRelT TRel)\<^sup>=))\<^sup>+"
proof -
  have "(symcl ((indRelT TRel)\<^sup>=))\<^sup>+ = (symcl (indRelT TRel))\<^sup>*"
    by (rule refl_symm_trans_closure_is_symm_refl_trans_closure[where Rel="indRelT TRel"])
  moreover from symm have "symcl (indRelT TRel) = indRelT TRel"
      using indRelT_symm[where TRel="TRel"] symm_closure_of_symm_rel[where Rel="indRelT TRel"]
    by blast
  ultimately show "indRelTEQ TRel = (symcl ((indRelT TRel)\<^sup>=))\<^sup>+"
      using refl refl_trans_closure_of_indRelT[where TRel="TRel"]
    by simp
qed

lemma (in encoding) symm_closure_of_indRelRT:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes refl: "refl TRel"
      and symm: "sym TRel"
  shows "indRelT TRel = symcl (indRelRT TRel)"
    and "indRelTEQ TRel = (symcl ((indRelRT TRel)\<^sup>=))\<^sup>+"
proof -
  show "indRelT TRel = symcl (indRelRT TRel)"
  proof auto
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q"
    thus "(P, Q) \<in> symcl (indRelRT TRel)"
      by (induct, simp_all add: symcl_def indRelRT.encR indRelRT.target)
  next
    fix P Q
    assume "(P, Q) \<in> symcl (indRelRT TRel)"
    thus "P \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q"
    proof (auto simp add: symcl_def indRelRT.simps)
      fix S
      show "SourceTerm S \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
        by (rule indRelT.encR)
    next
      fix T1 T2
      assume "(T1, T2) \<in> TRel"
      thus "TargetTerm T1 \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2"
        by (rule indRelT.target)
    next
      fix S
      show "TargetTerm (\<lbrakk>S\<rbrakk>) \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S"
        by (rule indRelT.encL)
    next
      fix T1 T2
      assume "(T1, T2) \<in> TRel"
      with symm show "TargetTerm T2 \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T1"
          unfolding sym_def
        by (simp add: indRelT.target)
    qed
  qed
  with refl show "indRelTEQ TRel = (symcl ((indRelRT TRel)\<^sup>=))\<^sup>+"
      using refl_symm_trans_closure_is_symm_refl_trans_closure[where Rel="indRelRT TRel"]
            refl_trans_closure_of_indRelT
    by simp
qed

lemma (in encoding) symm_closure_of_indRelLT:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes refl: "refl TRel"
      and symm: "sym TRel"
  shows "indRelT TRel = symcl (indRelLT TRel)"
    and "indRelTEQ TRel = (symcl ((indRelLT TRel)\<^sup>=))\<^sup>+"
proof -
  show "indRelT TRel = symcl (indRelLT TRel)"
  proof auto
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q"
    thus "(P, Q) \<in> symcl (indRelLT TRel)"
      by (induct, simp_all add: symcl_def indRelLT.encL indRelLT.target)
  next
    fix P Q
    assume "(P, Q) \<in> symcl (indRelLT TRel)"
    thus "P \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q"
    proof (auto simp add: symcl_def indRelLT.simps)
      fix S
      show "SourceTerm S \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
        by (rule indRelT.encR)
    next
      fix T1 T2
      assume "(T1, T2) \<in> TRel"
      thus "TargetTerm T1 \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2"
        by (rule indRelT.target)
    next
      fix S
      show "TargetTerm (\<lbrakk>S\<rbrakk>) \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S"
        by (rule indRelT.encL)
    next
      fix T1 T2
      assume "(T1, T2) \<in> TRel"
      with symm show "TargetTerm T2 \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T1"
          unfolding sym_def
        by (simp add: indRelT.target)
    qed
  qed
  with refl show "indRelTEQ TRel = (symcl ((indRelLT TRel)\<^sup>=))\<^sup>+"
      using refl_symm_trans_closure_is_symm_refl_trans_closure[where Rel="indRelLT TRel"]
            refl_trans_closure_of_indRelT
    by simp
qed

text \<open>If the relations indRelRT, indRelLT, or indRelT contain a pair of target terms, then this
        pair is also related by the considered target term relation.\<close>

lemma (in encoding) indRelRT_to_TRel:
  fixes TRel  :: "('procT \<times> 'procT) set"
    and TP TQ :: "'procT"
  assumes rel: "TargetTerm TP \<R>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm TQ"
  shows "(TP, TQ) \<in> TRel"
      using rel
    by (simp add: indRelRT.simps)

lemma (in encoding) indRelLT_to_TRel:
  fixes TRel  :: "('procT \<times> 'procT) set"
    and TP TQ :: "'procT"
  assumes rel: "TargetTerm TP \<R>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> TargetTerm TQ"
  shows "(TP, TQ) \<in> TRel"
      using rel
    by (simp add: indRelLT.simps)

lemma (in encoding) indRelT_to_TRel:
  fixes TRel  :: "('procT \<times> 'procT) set"
    and TP TQ :: "'procT"
  assumes rel: "TargetTerm TP \<R>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm TQ"
  shows "(TP, TQ) \<in> TRel"
      using rel
    by (simp add: indRelT.simps)

text \<open>If the preorders indRelRTPO, indRelLTPO, or the equivalence indRelTEQ contain a pair of
        terms, then the pair of target terms that is related to these two terms is also related by
        the reflexive and transitive closure of the considered target term relation.\<close>

lemma (in encoding) indRelRTPO_to_TRel:
  fixes TRel :: "('procT \<times> 'procT) set"
    and P Q  :: "('procS, 'procT) Proc"
  assumes rel: "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
  shows "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> SP = SQ"
    and "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q
         \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    and "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q \<longrightarrow> False"
    and "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
proof -
  have reflTRel: "\<forall>S. (\<lbrakk>S\<rbrakk>, \<lbrakk>S\<rbrakk>) \<in> TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>}"
    by auto
  from rel show "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> SP = SQ"
            and "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q
                 \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            and "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q \<longrightarrow> False"
            and "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
  proof induct
    case (encR S)
    show "\<forall>SP SQ. SP \<in>S SourceTerm S \<and> SQ \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> SP = SQ"
     and "\<forall>TP SQ. TP \<in>T SourceTerm S \<and> SQ \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> False"
     and "\<forall>TP TQ. TP \<in>T SourceTerm S \<and> TQ \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
      by simp_all
    from reflTRel show "\<forall>SP TQ. SP \<in>S SourceTerm S \<and> TQ \<in>T TargetTerm (\<lbrakk>S\<rbrakk>)
                        \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      by blast
  next
    case (source S)
    show "\<forall>SP SQ. SP \<in>S SourceTerm S \<and> SQ \<in>S SourceTerm S \<longrightarrow> SP = SQ"
      by simp
    show "\<forall>SP TQ. SP \<in>S SourceTerm S \<and> TQ \<in>T SourceTerm S
          \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
     and "\<forall>TP SQ. TP \<in>T SourceTerm S \<and> SQ \<in>S SourceTerm S \<longrightarrow> False"
     and "\<forall>TP TQ. TP \<in>T SourceTerm S \<and> TQ \<in>T SourceTerm S \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
      by simp_all
  next
    case (target T1 T2)
    show "\<forall>SP SQ. SP \<in>S TargetTerm T1 \<and> SQ \<in>S TargetTerm T2 \<longrightarrow> SP = SQ"
     and "\<forall>SP TQ. SP \<in>S TargetTerm T1 \<and> TQ \<in>T TargetTerm T2
          \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
     and "\<forall>TP SQ. TP \<in>T TargetTerm T1 \<and> SQ \<in>S TargetTerm T2 \<longrightarrow> False"
      by simp_all
    assume "(T1, T2) \<in> TRel"
    thus "\<forall>TP TQ. TP \<in>T TargetTerm T1 \<and> TQ \<in>T TargetTerm T2 \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
      by simp
  next
    case (trans P Q R)
    assume A1: "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> SP = SQ"
       and A2: "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q
                \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A3: "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q \<longrightarrow> False"
       and A4: "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
       and A5: "\<forall>SQ SR. SQ \<in>S Q \<and> SR \<in>S R \<longrightarrow> SQ = SR"
       and A6: "\<forall>SQ TR. SQ \<in>S Q \<and> TR \<in>T R
                \<longrightarrow> (\<lbrakk>SQ\<rbrakk>, TR) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A7: "\<forall>TQ SR. TQ \<in>T Q \<and> SR \<in>S R \<longrightarrow> False"
       and A8: "\<forall>TQ TR. TQ \<in>T Q \<and> TR \<in>T R \<longrightarrow> (TQ, TR) \<in> TRel\<^sup>+"
    show "\<forall>SP SR. SP \<in>S P \<and> SR \<in>S R \<longrightarrow> SP = SR"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A1 A5 show "\<forall>SP SR. SP \<in>S P \<and> SR \<in>S R \<longrightarrow> SP = SR"
        by blast
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A7 show ?thesis
        by blast
    qed
    show "\<forall>SP TR. SP \<in>S P \<and> TR \<in>T R
          \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TR) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A1 A6 show ?thesis
        by blast
    next
      case (TargetTerm TQ)
      assume A9: "TQ \<in>T Q"
      show "\<forall>SP TR. SP \<in>S P \<and> TR \<in>T R
            \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TR) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      proof clarify
        fix SP TR
        assume "SP \<in>S P"
        with A2 A9 have "(\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
          by simp
        moreover assume "TR \<in>T R"
        with A8 A9 have "(TQ, TR) \<in> TRel\<^sup>+"
          by simp
        hence "(TQ, TR) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
        proof induct
          fix T2
          assume "(TQ, T2) \<in> TRel"
          thus "(TQ, T2) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            by blast
        next
          case (step T2 T3)
          assume "(TQ, T2) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
          moreover assume "(T2, T3) \<in> TRel"
          hence "(T2, T3) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            by blast
          ultimately show "(TQ, T3) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            by simp
        qed
        ultimately show "(\<lbrakk>SP\<rbrakk>, TR) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
          by simp
      qed
    qed
    show "\<forall>TP SR. TP \<in>T P \<and> SR \<in>S R \<longrightarrow> False"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A3 show ?thesis
        by blast
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A7 show ?thesis
        by blast
    qed
    show "\<forall>TP TR. TP \<in>T P \<and> TR \<in>T R \<longrightarrow> (TP, TR) \<in> TRel\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A3 show ?thesis
        by blast
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A4 A8 show "\<forall>TP TR. TP \<in>T P \<and> TR \<in>T R \<longrightarrow> (TP, TR) \<in> TRel\<^sup>+"
        by auto
    qed
  qed
qed

lemma (in encoding) indRelLTPO_to_TRel:
  fixes TRel :: "('procT \<times> 'procT) set"
    and P Q  :: "('procS, 'procT) Proc"
  assumes rel: "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>LT<TRel> Q"
  shows "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> SP = SQ"
    and "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> False"
    and "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q
         \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    and "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
proof -
  have reflTRel: "\<forall>S. (\<lbrakk>S\<rbrakk>, \<lbrakk>S\<rbrakk>) \<in> TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>}"
    by auto
  from rel show "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> SP = SQ"
            and "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> False"
            and "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q
                 \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            and "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
  proof induct
    case (encL S)
    show "\<forall>SP SQ. SP \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<and> SQ \<in>S SourceTerm S  \<longrightarrow> SP = SQ"
     and "\<forall>SP TQ. SP \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TQ \<in>T SourceTerm S \<longrightarrow> False"
     and "\<forall>TP TQ. TP \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TQ \<in>T SourceTerm S \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
      by simp_all
    from reflTRel show "\<forall>TP SQ. TP \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<and> SQ \<in>S SourceTerm S
                        \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      by blast
  next
    case (source S)
    show "\<forall>SP SQ. SP \<in>S SourceTerm S \<and> SQ \<in>S SourceTerm S \<longrightarrow> SP = SQ"
      by simp
    show "\<forall>SP TQ. SP \<in>S SourceTerm S \<and> TQ \<in>T SourceTerm S \<longrightarrow> False"
     and "\<forall>TP SQ. TP \<in>T SourceTerm S \<and> SQ \<in>S SourceTerm S
          \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
     and "\<forall>TP TQ. TP \<in>T SourceTerm S \<and> TQ \<in>T SourceTerm S \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
      by simp_all
  next
    case (target T1 T2)
    show "\<forall>SP SQ. SP \<in>S TargetTerm T1 \<and> SQ \<in>S TargetTerm T2 \<longrightarrow> SP = SQ"
     and "\<forall>SP TQ. SP \<in>S TargetTerm T1 \<and> TQ \<in>T TargetTerm T2 \<longrightarrow> False"
     and "\<forall>TP SQ. TP \<in>T TargetTerm T1 \<and> SQ \<in>S TargetTerm T2
          \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      by simp_all
    assume "(T1, T2) \<in> TRel"
    thus "\<forall>TP TQ. TP \<in>T TargetTerm T1 \<and> TQ \<in>T TargetTerm T2 \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
      by simp
  next
    case (trans P Q R)
    assume A1: "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> SP = SQ"
       and A2: "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> False"
       and A3: "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q
                \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A4: "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
       and A5: "\<forall>SQ SR. SQ \<in>S Q \<and> SR \<in>S R \<longrightarrow> SQ = SR"
       and A6: "\<forall>SQ TR. SQ \<in>S Q \<and> TR \<in>T R \<longrightarrow> False"
       and A7: "\<forall>TQ SR. TQ \<in>T Q \<and> SR \<in>S R
                \<longrightarrow> (TQ, \<lbrakk>SR\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A8: "\<forall>TQ TR. TQ \<in>T Q \<and> TR \<in>T R \<longrightarrow> (TQ, TR) \<in> TRel\<^sup>+"
    show "\<forall>SP SR. SP \<in>S P \<and> SR \<in>S R \<longrightarrow> SP = SR"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A1 A5 show "\<forall>SP SR. SP \<in>S P \<and> SR \<in>S R \<longrightarrow> SP = SR"
        by blast
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A2 show ?thesis
        by blast
    qed
    show "\<forall>SP TR. SP \<in>S P \<and> TR \<in>T R \<longrightarrow> False"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A6 show ?thesis
        by blast
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A2 show ?thesis
        by blast
    qed
    show "\<forall>TP SR. TP \<in>T P \<and> SR \<in>S R
          \<longrightarrow> (TP, \<lbrakk>SR\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A3 A5 show "\<forall>TP SR. TP \<in>T P \<and> SR \<in>S R
                       \<longrightarrow> (TP, \<lbrakk>SR\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
        by blast
    next
      case (TargetTerm TQ)
      assume A9: "TQ \<in>T Q"
      show "\<forall>TP SR. TP \<in>T P \<and> SR \<in>S R
            \<longrightarrow> (TP, \<lbrakk>SR\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      proof clarify
        fix TP SR
        assume "TP \<in>T P"
        with A4 A9 have "(TP, TQ) \<in> TRel\<^sup>+"
          by simp
        hence "(TP, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
        proof induct
          fix T2
          assume "(TP, T2) \<in> TRel"
          thus "(TP, T2) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            by blast
        next
          case (step T2 T3)
          assume "(TP, T2) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
          moreover assume "(T2, T3) \<in> TRel"
          hence "(T2, T3) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            by blast
          ultimately show "(TP, T3) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            by simp
        qed
        moreover assume "SR \<in>S R"
        with A7 A9 have "(TQ, \<lbrakk>SR\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
          by simp
        ultimately show "(TP, \<lbrakk>SR\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
          by simp
      qed
    qed
    show "\<forall>TP TR. TP \<in>T P \<and> TR \<in>T R \<longrightarrow> (TP, TR) \<in> TRel\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A6 show ?thesis
        by blast
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A4 A8 show "\<forall>TP TR. TP \<in>T P \<and> TR \<in>T R \<longrightarrow> (TP, TR) \<in> TRel\<^sup>+"
        by auto
    qed
  qed
qed

lemma (in encoding) indRelTEQ_to_TRel:
  fixes TRel :: "('procT \<times> 'procT) set"
    and P Q  :: "('procS, 'procT) Proc"
  assumes rel: "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q"
  shows "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q
         \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    and "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q
         \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    and "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q
         \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    and "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q
         \<longrightarrow> (TP, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
proof -
  have reflTRel: "\<forall>S. (\<lbrakk>S\<rbrakk>, \<lbrakk>S\<rbrakk>) \<in> TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>}"
    by auto
  from rel show "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q
                 \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            and "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q
                 \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            and "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q
                 \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
            and "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q
                 \<longrightarrow> (TP, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
  proof induct
    case (encR S)
    show "\<forall>SP SQ. SP \<in>S SourceTerm S \<and> SQ \<in>S TargetTerm (\<lbrakk>S\<rbrakk>)
          \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
     and "\<forall>TP SQ. TP \<in>T SourceTerm S \<and> SQ \<in>S TargetTerm (\<lbrakk>S\<rbrakk>)
          \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
     and "\<forall>TP TQ. TP \<in>T SourceTerm S \<and> TQ \<in>T TargetTerm (\<lbrakk>S\<rbrakk>)
          \<longrightarrow> (TP, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      by simp+
    from reflTRel show "\<forall>SP TQ. SP \<in>S SourceTerm S \<and> TQ \<in>T TargetTerm (\<lbrakk>S\<rbrakk>)
                        \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      by blast
  next
    case (encL S)
    show "\<forall>SP SQ. SP \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<and> SQ \<in>S SourceTerm S
          \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
     and "\<forall>SP TQ. SP \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TQ \<in>T SourceTerm S
          \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
     and "\<forall>TP TQ. TP \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TQ \<in>T SourceTerm S
          \<longrightarrow> (TP, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      by simp+
    from reflTRel show "\<forall>TP SQ. TP \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<and> SQ \<in>S SourceTerm S
                        \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      by blast
  next
    case (target T1 T2)
    show "\<forall>SP SQ. SP \<in>S TargetTerm T1 \<and> SQ \<in>S TargetTerm T2
          \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
     and "\<forall>SP TQ. SP \<in>S TargetTerm T1 \<and> TQ \<in>T TargetTerm T2
          \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
     and "\<forall>TP SQ. TP \<in>T TargetTerm T1 \<and> SQ \<in>S TargetTerm T2
          \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      by simp+
    assume "(T1, T2) \<in> TRel"
    thus "\<forall>TP TQ. TP \<in>T TargetTerm T1 \<and> TQ \<in>T TargetTerm T2
          \<longrightarrow> (TP, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
      by blast
  next
    case (trans P Q R)
    assume A1: "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q
                \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A2: "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q
                \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A3: "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q
                \<longrightarrow> (TP, \<lbrakk>SQ\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A4: "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q
                \<longrightarrow> (TP, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A5: "\<forall>SQ SR. SQ \<in>S Q \<and> SR \<in>S R
                \<longrightarrow> (\<lbrakk>SQ\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A6: "\<forall>SQ TR. SQ \<in>S Q \<and> TR \<in>T R
                \<longrightarrow> (\<lbrakk>SQ\<rbrakk>, TR) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A7: "\<forall>TQ SR. TQ \<in>T Q \<and> SR \<in>S R
                \<longrightarrow> (TQ, \<lbrakk>SR\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
       and A8: "\<forall>TQ TR. TQ \<in>T Q \<and> TR \<in>T R
                \<longrightarrow> (TQ, TR) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    show "\<forall>SP SR. SP \<in>S P \<and> SR \<in>S R
          \<longrightarrow> (\<lbrakk>SP\<rbrakk>, \<lbrakk>SR\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A1 A5 show ?thesis
        by auto
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A2 A7 show ?thesis
        by auto
    qed
    show "\<forall>SP TR. SP \<in>S P \<and> TR \<in>T R \<longrightarrow> (\<lbrakk>SP\<rbrakk>, TR) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A1 A6 show ?thesis
        by auto
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A2 A8 show ?thesis
        by auto
    qed
    show "\<forall>TP SR. TP \<in>T P \<and> SR \<in>S R \<longrightarrow> (TP, \<lbrakk>SR\<rbrakk>) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A3 A5 show ?thesis
        by auto
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A4 A7 show ?thesis
        by auto
    qed
    show "\<forall>TP TR. TP \<in>T P \<and> TR \<in>T R \<longrightarrow> (TP, TR) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A3 A6 show ?thesis
        by auto
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A4 A8 show ?thesis
        by auto
    qed
  qed
qed

lemma (in encoding) trans_closure_of_TRel_refl_cond:
  fixes TRel  :: "('procT \<times> 'procT) set"
    and TP TQ :: "'procT"
  assumes "(TP, TQ) \<in> (TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>})\<^sup>+"
  shows "(TP, TQ) \<in> TRel\<^sup>*"
    using assms
proof induct
  fix TQ
  assume "(TP, TQ) \<in> TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>}"
  thus "(TP, TQ) \<in> TRel\<^sup>*"
    by auto
next
  case (step TQ TR)
  assume "(TP, TQ) \<in> TRel\<^sup>*"
  moreover assume "(TQ, TR) \<in> TRel \<union> {(T1, T2). \<exists>S. T1 = \<lbrakk>S\<rbrakk> \<and> T2 = \<lbrakk>S\<rbrakk>}"
  hence "(TQ, TR) \<in> TRel\<^sup>*"
    by blast
  ultimately show "(TP, TR) \<in> TRel\<^sup>*"
    by simp
qed

text \<open>Note that if indRelRTPO relates a source term S to a target term T, then the translation of
        S is equal to T or indRelRTPO also relates the translation of S to T.\<close>

lemma (in encoding) indRelRTPO_relates_source_target:
  fixes TRel :: "('procT \<times> 'procT) set"
    and S    :: "'procS"
    and T    :: "'procT"
  assumes pair: "SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T"
  shows "(TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> (indRelRTPO TRel)\<^sup>="
proof -
  from pair have "(\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"] trans_closure_of_TRel_refl_cond
    by simp
  hence "\<lbrakk>S\<rbrakk> = T \<or> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>+"
      using rtrancl_eq_or_trancl[of "\<lbrakk>S\<rbrakk>" T TRel]
    by blast
  moreover have "\<lbrakk>S\<rbrakk> = T \<Longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> (indRelRTPO TRel)\<^sup>="
    by simp
  moreover
  have "(\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>+ \<Longrightarrow> (TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> (indRelRTPO TRel)\<^sup>="
      using transitive_closure_of_TRel_to_indRelRTPO[where TRel="TRel"]
    by simp
  ultimately show "(TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> (indRelRTPO TRel)\<^sup>="
    by blast
qed

text \<open>If indRelRTPO, indRelLTPO, or indRelTPO preserves barbs then so does the corresponding
        target term relation.\<close>

lemma (in encoding_wrt_barbs) rel_with_target_impl_TRel_preserves_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes preservation: "rel_preserves_barbs Rel (STCalWB SWB TWB)"
      and targetInRel:  "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
  shows "rel_preserves_barbs TRel TWB"
proof clarify
  fix TP TQ a
  assume "(TP, TQ) \<in> TRel"
  with targetInRel have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
    by blast
  moreover assume "TP\<down><TWB>a"
  hence "TargetTerm TP\<down>.a"
    by simp
  ultimately have "TargetTerm TQ\<down>.a"
      using preservation preservation_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
  thus "TQ\<down><TWB>a"
    by simp
qed

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_preserves_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_preserves_barbs (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "rel_preserves_barbs TRel TWB"
      using preservation
            rel_with_target_impl_TRel_preserves_barbs[where Rel="indRelRTPO TRel" and TRel="TRel"]
    by (simp add: indRelRTPO.target)

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_preserves_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_preserves_barbs (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "rel_preserves_barbs TRel TWB"
      using preservation
            rel_with_target_impl_TRel_preserves_barbs[where Rel="indRelLTPO TRel" and TRel="TRel"]
    by (simp add: indRelLTPO.target)

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_preserves_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_preserves_barbs (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "rel_preserves_barbs TRel TWB"
      using preservation
            rel_with_target_impl_TRel_preserves_barbs[where Rel="indRelTEQ TRel" and TRel="TRel"]
    by (simp add: indRelTEQ.target)

lemma (in encoding_wrt_barbs) rel_with_target_impl_TRel_weakly_preserves_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes preservation: "rel_weakly_preserves_barbs Rel (STCalWB SWB TWB)"
      and targetInRel:  "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
  shows "rel_weakly_preserves_barbs TRel TWB"
proof clarify
  fix TP TQ a TP'
  assume "(TP, TQ) \<in> TRel"
  with targetInRel have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
    by blast
  moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>a"
  hence "TargetTerm TP\<Down>.a"
    by blast
  ultimately have "TargetTerm TQ\<Down>.a"
      using preservation weak_preservation_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
  thus "TQ\<Down><TWB>a"
    by simp
qed

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_weakly_preserves_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_weakly_preserves_barbs (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_preserves_barbs TRel TWB"
      using preservation rel_with_target_impl_TRel_weakly_preserves_barbs[where
                          Rel="indRelRTPO TRel" and TRel="TRel"]
    by (simp add: indRelRTPO.target)

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_weakly_preserves_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_weakly_preserves_barbs (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_preserves_barbs TRel TWB"
      using preservation rel_with_target_impl_TRel_weakly_preserves_barbs[where
                          Rel="indRelLTPO TRel" and TRel="TRel"]
    by (simp add: indRelLTPO.target)

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_weakly_preserves_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_weakly_preserves_barbs (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_preserves_barbs TRel TWB"
      using preservation rel_with_target_impl_TRel_weakly_preserves_barbs[where
                          Rel="indRelTEQ TRel" and TRel="TRel"]
    by (simp add: indRelTEQ.target)

text \<open>If indRelRTPO, indRelLTPO, or indRelTPO reflects barbs then so does the corresponding
        target term relation.\<close>

lemma (in encoding_wrt_barbs) rel_with_target_impl_TRel_reflects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes reflection: "rel_reflects_barbs Rel (STCalWB SWB TWB)"
      and targetInRel:  "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
  shows "rel_reflects_barbs TRel TWB"
proof clarify
  fix TP TQ a
  assume "(TP, TQ) \<in> TRel"
  with targetInRel have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
    by blast
  moreover assume "TQ\<down><TWB>a"
  hence "TargetTerm TQ\<down>.a"
    by simp
  ultimately have "TargetTerm TP\<down>.a"
      using reflection reflection_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
  thus "TP\<down><TWB>a"
    by simp
qed

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_reflects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_reflects_barbs (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "rel_reflects_barbs TRel TWB"
      using reflection
            rel_with_target_impl_TRel_reflects_barbs[where Rel="indRelRTPO TRel" and TRel="TRel"]
    by (simp add: indRelRTPO.target)

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_reflects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_reflects_barbs (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "rel_reflects_barbs TRel TWB"
      using reflection
            rel_with_target_impl_TRel_reflects_barbs[where Rel="indRelLTPO TRel" and TRel="TRel"]
    by (simp add: indRelLTPO.target)

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_reflects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_reflects_barbs (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "rel_reflects_barbs TRel TWB"
      using reflection
            rel_with_target_impl_TRel_reflects_barbs[where Rel="indRelTEQ TRel" and TRel="TRel"]
    by (simp add: indRelTEQ.target)

lemma (in encoding_wrt_barbs) rel_with_target_impl_TRel_weakly_reflects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes reflection: "rel_weakly_reflects_barbs Rel (STCalWB SWB TWB)"
      and targetInRel:  "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
  shows "rel_weakly_reflects_barbs TRel TWB"
proof clarify
  fix TP TQ a TQ'
  assume "(TP, TQ) \<in> TRel"
  with targetInRel have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
    by blast
  moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>a"
  hence "TargetTerm TQ\<Down>.a"
    by blast
  ultimately have "TargetTerm TP\<Down>.a"
      using reflection weak_reflection_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
  thus "TP\<Down><TWB>a"
    by simp
qed

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_weakly_reflects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_weakly_reflects_barbs (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_reflects_barbs TRel TWB"
      using reflection rel_with_target_impl_TRel_weakly_reflects_barbs[where
                        Rel="indRelRTPO TRel" and TRel="TRel"]
    by (simp add: indRelRTPO.target)

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_weakly_reflects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_weakly_reflects_barbs (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_reflects_barbs TRel TWB"
      using reflection rel_with_target_impl_TRel_weakly_reflects_barbs[where
                        Rel="indRelLTPO TRel" and TRel="TRel"]
    by (simp add: indRelLTPO.target)

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_weakly_reflects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_weakly_reflects_barbs (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_reflects_barbs TRel TWB"
      using reflection rel_with_target_impl_TRel_weakly_reflects_barbs[where
                        Rel="indRelTEQ TRel" and TRel="TRel"]
    by (simp add: indRelTEQ.target)

text \<open>If indRelRTPO, indRelLTPO, or indRelTPO respects barbs then so does the corresponding
        target term relation.\<close>

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_respects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_respects_barbs (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "rel_respects_barbs TRel TWB"
      using respection indRelRTPO_impl_TRel_preserves_barbs[where TRel="TRel"]
            indRelRTPO_impl_TRel_reflects_barbs[where TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_respects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_respects_barbs (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "rel_respects_barbs TRel TWB"
      using respection indRelLTPO_impl_TRel_preserves_barbs[where TRel="TRel"]
            indRelLTPO_impl_TRel_reflects_barbs[where TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_respects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_respects_barbs (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "rel_respects_barbs TRel TWB"
      using respection indRelTEQ_impl_TRel_preserves_barbs[where TRel="TRel"]
            indRelTEQ_impl_TRel_reflects_barbs[where TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_weakly_respects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_weakly_respects_barbs (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_respects_barbs TRel TWB"
      using respection indRelRTPO_impl_TRel_weakly_preserves_barbs[where TRel="TRel"]
            indRelRTPO_impl_TRel_weakly_reflects_barbs[where TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_weakly_respects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_weakly_respects_barbs (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_respects_barbs TRel TWB"
      using respection indRelLTPO_impl_TRel_weakly_preserves_barbs[where TRel="TRel"]
            indRelLTPO_impl_TRel_weakly_reflects_barbs[where TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_weakly_respects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_weakly_respects_barbs (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_respects_barbs TRel TWB"
      using respection indRelTEQ_impl_TRel_weakly_preserves_barbs[where TRel="TRel"]
            indRelTEQ_impl_TRel_weakly_reflects_barbs[where TRel="TRel"]
    by blast

text \<open>If indRelRTPO, indRelLTPO, or indRelTEQ is a simulation then so is the corresponding target
        term relation.\<close>

lemma (in encoding) rel_with_target_impl_transC_TRel_is_weak_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes sim:    "weak_reduction_simulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
  shows "weak_reduction_simulation (TRel\<^sup>+) Target"
proof clarify
  fix TP TQ TP'
  assume "(TP, TQ) \<in> TRel\<^sup>+" and "TP \<longmapsto>Target* TP'"
  thus "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> TRel\<^sup>+"
  proof (induct arbitrary: TP')
    fix TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with target have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>Target* TP'"
    hence "TargetTerm TP \<longmapsto>(STCal Source Target)* (TargetTerm TP')"
      by (simp add: STCal_steps)
    ultimately obtain Q' where A2: "TargetTerm TQ \<longmapsto>(STCal Source Target)* Q'"
                           and A3: "(TargetTerm TP', Q') \<in> Rel"
        using sim
      by blast
    from A2 obtain TQ' where A4: "TQ \<longmapsto>Target* TQ'" and A5: "TQ' \<in>T Q'"
      by (auto simp add: STCal_steps)
    from A3 A5 trel have "(TP', TQ') \<in> TRel\<^sup>+"
      by simp
    with A4 show "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> TRel\<^sup>+"
      by blast
  next
    case (step TQ TR)
    assume "TP \<longmapsto>Target* TP'"
       and "\<And>TP'. TP \<longmapsto>Target* TP' \<Longrightarrow> \<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> TRel\<^sup>+"
    from this obtain TQ' where B1: "TQ \<longmapsto>Target* TQ'" and B2: "(TP', TQ') \<in> TRel\<^sup>+"
      by blast
    assume "(TQ, TR) \<in> TRel"
    with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
      by simp
    moreover from B1 have "TargetTerm TQ \<longmapsto>(STCal Source Target)* (TargetTerm TQ')"
      by (simp add: STCal_steps)
    ultimately obtain R' where B3: "TargetTerm TR \<longmapsto>(STCal Source Target)* R'"
                           and B4: "(TargetTerm TQ', R') \<in> Rel"
        using sim
      by blast
    from B3 obtain TR' where B5: "TR' \<in>T R'" and B6: "TR \<longmapsto>Target* TR'"
      by (auto simp add: STCal_steps)
    from B4 B5 trel have "(TQ', TR') \<in> TRel\<^sup>+"
      by simp
    with B2 have "(TP', TR') \<in> TRel\<^sup>+"
      by simp
    with B6 show "\<exists>TR'. TR \<longmapsto>Target* TR' \<and> (TP', TR') \<in> TRel\<^sup>+"
      by blast
  qed
qed

lemma (in encoding) indRelRTPO_impl_TRel_is_weak_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "weak_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
  shows "weak_reduction_simulation (TRel\<^sup>+) Target"
      using sim indRelRTPO.target[where TRel="TRel"] indRelRTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_weak_reduction_simulation[where
             Rel="indRelRTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) indRelLTPO_impl_TRel_is_weak_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "weak_reduction_simulation (indRelLTPO TRel) (STCal Source Target)"
  shows "weak_reduction_simulation (TRel\<^sup>+) Target"
      using sim indRelLTPO.target[where TRel="TRel"] indRelLTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_weak_reduction_simulation[where
             Rel="indRelLTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) rel_with_target_impl_transC_TRel_is_weak_reduction_simulation_rev:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes sim:    "weak_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
  shows "weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
proof clarify
  fix TP TQ TP'
  assume "(TQ, TP) \<in> TRel\<^sup>+"
  moreover assume "TP \<longmapsto>Target* TP'"
  ultimately show "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> (TRel\<^sup>+)\<inverse>"
  proof (induct arbitrary: TP')
    fix TP TP'
    assume "(TQ, TP) \<in> TRel"
    with target have "(TargetTerm TP, TargetTerm TQ) \<in> Rel\<inverse>"
      by simp
    moreover assume "TP \<longmapsto>Target* TP'"
    hence "TargetTerm TP \<longmapsto>(STCal Source Target)* (TargetTerm TP')"
      by (simp add: STCal_steps)
    ultimately obtain Q' where A2: "TargetTerm TQ \<longmapsto>(STCal Source Target)* Q'"
                           and A3: "(TargetTerm TP', Q') \<in> Rel\<inverse>"
        using sim
      by blast
    from A2 obtain TQ' where A4: "TQ \<longmapsto>Target* TQ'" and A5: "TQ' \<in>T Q'"
      by (auto simp add: STCal_steps(2))
    from A3 A5 trel have "(TP', TQ') \<in> (TRel\<^sup>+)\<inverse>"
      by simp
    with A4 show "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> (TRel\<^sup>+)\<inverse>"
      by blast
  next
    case (step TR TP TP')
    assume "TP \<longmapsto>Target* TP'"
    hence "TargetTerm TP \<longmapsto>(STCal Source Target)* (TargetTerm TP')"
      by (simp add: STCal_steps)
    moreover assume "(TR, TP) \<in> TRel"
    with target have "(TargetTerm TP, TargetTerm TR) \<in> Rel\<inverse>"
      by simp
    ultimately obtain R' where B1: "TargetTerm TR \<longmapsto>(STCal Source Target)* R'"
                           and B2: "(TargetTerm TP', R') \<in> Rel\<inverse>"
        using sim
      by blast
    from B1 obtain TR' where B3: "TR' \<in>T R'" and B4: "TR \<longmapsto>Target* TR'"
      by (auto simp add: STCal_steps)
    assume "\<And>TR'. TR \<longmapsto>Target* TR' \<Longrightarrow> \<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TR', TQ') \<in> (TRel\<^sup>+)\<inverse>"
    with B4 obtain TQ' where B5: "TQ \<longmapsto>Target* TQ'" and B6: "(TR', TQ') \<in> (TRel\<^sup>+)\<inverse>"
      by blast
    from B6 have "(TQ', TR') \<in> TRel\<^sup>+"
      by simp
    moreover from B2 B3 trel have "(TR', TP') \<in> TRel\<^sup>+"
      by simp
    ultimately have "(TP', TQ') \<in> (TRel\<^sup>+)\<inverse>"
      by simp
    with B5 show "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> (TRel\<^sup>+)\<inverse>"
      by blast
  qed
qed

lemma (in encoding) indRelRTPO_impl_TRel_is_weak_reduction_simulation_rev:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "weak_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
  shows "weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
      using sim indRelRTPO.target[where TRel="TRel"] indRelRTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_weak_reduction_simulation_rev[where
             Rel="indRelRTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) indRelLTPO_impl_TRel_is_weak_reduction_simulation_rev:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "weak_reduction_simulation ((indRelLTPO TRel)\<inverse>) (STCal Source Target)"
  shows "weak_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
      using sim indRelLTPO.target[where TRel="TRel"] indRelLTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_weak_reduction_simulation_rev[where
             Rel="indRelLTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) rel_with_target_impl_reflC_transC_TRel_is_weak_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes sim:    "weak_reduction_simulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>*"
  shows "weak_reduction_simulation (TRel\<^sup>*) Target"
proof clarify
  fix TP TQ TP'
  assume "(TP, TQ) \<in> TRel\<^sup>*" and "TP \<longmapsto>Target* TP'"
  thus "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> TRel\<^sup>*"
  proof (induct arbitrary: TP')
    fix TP'
    assume "TP \<longmapsto>Target* TP'"
    moreover have "(TP', TP') \<in> TRel\<^sup>*"
      by simp
    ultimately show "\<exists>TQ'. TP \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> TRel\<^sup>*"
      by blast
  next
    case (step TQ TR)
    assume "TP \<longmapsto>Target* TP'"
       and "\<And>TP'. TP \<longmapsto>Target* TP' \<Longrightarrow> \<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> TRel\<^sup>*"
    from this obtain TQ' where B1: "TQ \<longmapsto>Target* TQ'" and B2: "(TP', TQ') \<in> TRel\<^sup>*"
      by blast
    assume "(TQ, TR) \<in> TRel"
    with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
      by simp
    moreover from B1 have "TargetTerm TQ \<longmapsto>(STCal Source Target)* (TargetTerm TQ')"
      by (simp add: STCal_steps)
    ultimately obtain R' where B3: "TargetTerm TR \<longmapsto>(STCal Source Target)* R'"
                           and B4: "(TargetTerm TQ', R') \<in> Rel"
        using sim
      by blast
    from B3 obtain TR' where B5: "TR' \<in>T R'" and B6: "TR \<longmapsto>Target* TR'"
      by (auto simp add: STCal_steps)
    from B4 B5 trel have "(TQ', TR') \<in> TRel\<^sup>*"
      by simp
    with B2 have "(TP', TR') \<in> TRel\<^sup>*"
      by simp
    with B6 show "\<exists>TR'. TR \<longmapsto>Target* TR' \<and> (TP', TR') \<in> TRel\<^sup>*"
      by blast
  qed
qed

lemma (in encoding) indRelTEQ_impl_TRel_is_weak_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "weak_reduction_simulation (indRelTEQ TRel) (STCal Source Target)"
  shows "weak_reduction_simulation (TRel\<^sup>*) Target"
      using sim indRelTEQ.target[where TRel="TRel"] indRelTEQ_to_TRel(4)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond
            rel_with_target_impl_reflC_transC_TRel_is_weak_reduction_simulation[where
             Rel="indRelTEQ TRel" and TRel="TRel"]
    by blast

lemma (in encoding) rel_with_target_impl_transC_TRel_is_strong_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes sim:    "strong_reduction_simulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
  shows "strong_reduction_simulation (TRel\<^sup>+) Target"
proof clarify
  fix TP TQ TP'
  assume "(TP, TQ) \<in> TRel\<^sup>+" and "TP \<longmapsto>Target TP'"
  thus "\<exists>TQ'. TQ \<longmapsto>Target TQ' \<and> (TP', TQ') \<in> TRel\<^sup>+"
  proof (induct arbitrary: TP')
    fix TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with target have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>Target TP'"
    hence "TargetTerm TP \<longmapsto>(STCal Source Target) (TargetTerm TP')"
      by (simp add: STCal_step)
    ultimately obtain Q' where A2: "TargetTerm TQ \<longmapsto>(STCal Source Target) Q'"
                           and A3: "(TargetTerm TP', Q') \<in> Rel"
        using sim
      by blast
    from A2 obtain TQ' where A4: "TQ \<longmapsto>Target TQ'" and A5: "TQ' \<in>T Q'"
      by (auto simp add: STCal_step)
    from A3 A5 trel have "(TP', TQ') \<in> TRel\<^sup>+"
      by simp
    with A4 show "\<exists>TQ'. TQ \<longmapsto>Target TQ' \<and> (TP', TQ') \<in> TRel\<^sup>+"
      by blast
  next
    case (step TQ TR)
    assume "TP \<longmapsto>Target TP'"
       and "\<And>TP'. TP \<longmapsto>Target TP' \<Longrightarrow> \<exists>TQ'. TQ \<longmapsto>Target TQ' \<and> (TP', TQ') \<in> TRel\<^sup>+"
    from this obtain TQ' where B1: "TQ \<longmapsto>Target TQ'" and B2: "(TP', TQ') \<in> TRel\<^sup>+"
      by blast
    assume "(TQ, TR) \<in> TRel"
    with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
      by simp
    moreover from B1 have "TargetTerm TQ \<longmapsto>(STCal Source Target) (TargetTerm TQ')"
      by (simp add: STCal_step)
    ultimately obtain R' where B3: "TargetTerm TR \<longmapsto>(STCal Source Target) R'"
                           and B4: "(TargetTerm TQ', R') \<in> Rel"
        using sim
      by blast
    from B3 obtain TR' where B5: "TR' \<in>T R'" and B6: "TR \<longmapsto>Target TR'"
      by (auto simp add: STCal_step)
    from B4 B5 trel have "(TQ', TR') \<in> TRel\<^sup>+"
      by simp
    with B2 have "(TP', TR') \<in> TRel\<^sup>+"
      by simp
    with B6 show "\<exists>TR'. TR \<longmapsto>Target TR' \<and> (TP', TR') \<in> TRel\<^sup>+"
      by blast
  qed
qed

lemma (in encoding) indRelRTPO_impl_TRel_is_strong_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "strong_reduction_simulation (indRelRTPO TRel) (STCal Source Target)"
  shows "strong_reduction_simulation (TRel\<^sup>+) Target"
      using sim indRelRTPO.target[where TRel="TRel"] indRelRTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_strong_reduction_simulation[where
             Rel="indRelRTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) indRelLTPO_impl_TRel_is_strong_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "strong_reduction_simulation (indRelLTPO TRel) (STCal Source Target)"
  shows "strong_reduction_simulation (TRel\<^sup>+) Target"
      using sim indRelLTPO.target[where TRel="TRel"] indRelLTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_strong_reduction_simulation[where
             Rel="indRelLTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) rel_with_target_impl_transC_TRel_is_strong_reduction_simulation_rev:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes sim:    "strong_reduction_simulation (Rel\<inverse>) (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
  shows "strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
proof clarify
  fix TP TQ TP'
  assume "(TQ, TP) \<in> TRel\<^sup>+"
  moreover assume "TP \<longmapsto>Target TP'"
  ultimately show "\<exists>TQ'. TQ \<longmapsto>Target TQ' \<and> (TP', TQ') \<in> (TRel\<^sup>+)\<inverse>"
  proof (induct arbitrary: TP')
    fix TP TP'
    assume "(TQ, TP) \<in> TRel"
    with target have "(TargetTerm TP, TargetTerm TQ) \<in> Rel\<inverse>"
      by simp
    moreover assume "TP \<longmapsto>Target TP'"
    hence "TargetTerm TP \<longmapsto>(STCal Source Target) (TargetTerm TP')"
      by (simp add: STCal_step)
    ultimately obtain Q' where A2: "TargetTerm TQ \<longmapsto>(STCal Source Target) Q'"
                           and A3: "(TargetTerm TP', Q') \<in> Rel\<inverse>"
        using sim
      by blast
    from A2 obtain TQ' where A4: "TQ \<longmapsto>Target TQ'" and A5: "TQ' \<in>T Q'"
      by (auto simp add: STCal_step(2))
    from A3 A5 trel have "(TP', TQ') \<in> (TRel\<^sup>+)\<inverse>"
      by simp
    with A4 show "\<exists>TQ'. TQ \<longmapsto>Target TQ' \<and> (TP', TQ') \<in> (TRel\<^sup>+)\<inverse>"
      by blast
  next
    case (step TP TR TR')
    assume "(TP, TR) \<in> TRel"
    with target have "(TargetTerm TP, TargetTerm TR) \<in> Rel"
      by simp
    moreover assume "TR \<longmapsto>Target TR'"
    hence "TargetTerm TR \<longmapsto>(STCal Source Target) (TargetTerm TR')"
      by (simp add: STCal_step)
    ultimately obtain P' where B1: "TargetTerm TP \<longmapsto>(STCal Source Target) P'"
                           and B2: "(P', TargetTerm TR') \<in> Rel"
        using sim
      by blast
    from B1 obtain TP' where B3: "TP' \<in>T P'" and B4: "TP \<longmapsto>Target TP'"
      by (auto simp add: STCal_step)
    assume "\<And>TP'. TP \<longmapsto>Target TP' \<Longrightarrow> \<exists>TQ'. TQ \<longmapsto>Target TQ' \<and> (TP', TQ') \<in> (TRel\<^sup>+)\<inverse>"
    with B4 obtain TQ' where B5: "TQ \<longmapsto>Target TQ'" and B6: "(TP', TQ') \<in> (TRel\<^sup>+)\<inverse>"
      by blast
    from B2 B3 trel have "(TP', TR') \<in> TRel\<^sup>+"
      by simp
    with B6 have "(TR', TQ') \<in> (TRel\<^sup>+)\<inverse>"
      by simp
    with B5 show "\<exists>TQ'. TQ \<longmapsto>Target TQ' \<and> (TR', TQ') \<in> (TRel\<^sup>+)\<inverse>"
      by blast
  qed
qed

lemma (in encoding) indRelRTPO_impl_TRel_is_strong_reduction_simulation_rev:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "strong_reduction_simulation ((indRelRTPO TRel)\<inverse>) (STCal Source Target)"
  shows "strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
      using sim indRelRTPO.target[where TRel="TRel"] indRelRTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_strong_reduction_simulation_rev[where
             Rel="indRelRTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) indRelLTPO_impl_TRel_is_strong_reduction_simulation_rev:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "strong_reduction_simulation ((indRelLTPO TRel)\<inverse>) (STCal Source Target)"
  shows "strong_reduction_simulation ((TRel\<^sup>+)\<inverse>) Target"
      using sim indRelLTPO.target[where TRel="TRel"] indRelLTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_strong_reduction_simulation_rev[where
             Rel="indRelLTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) rel_with_target_impl_reflC_transC_TRel_is_strong_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes sim:    "strong_reduction_simulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel
                   \<longrightarrow> (T1, T2) \<in> TRel\<^sup>*"
  shows "strong_reduction_simulation (TRel\<^sup>*) Target"
proof clarify
  fix TP TQ TP'
  assume "(TP, TQ) \<in> TRel\<^sup>*" and "TP \<longmapsto>Target TP'"
  thus "\<exists>TQ'. TQ \<longmapsto>Target TQ' \<and> (TP', TQ') \<in> TRel\<^sup>*"
  proof (induct arbitrary: TP')
    fix TP'
    assume "TP \<longmapsto>Target TP'"
    moreover have "(TP', TP') \<in> TRel\<^sup>*"
      by simp
    ultimately show "\<exists>TQ'. TP \<longmapsto>Target TQ' \<and> (TP', TQ') \<in> TRel\<^sup>*"
      by blast
  next
    case (step TQ TR TP')
    assume "TP \<longmapsto>Target TP'"
       and "\<And>TP'. TP \<longmapsto>Target TP' \<Longrightarrow> \<exists>TQ'. TQ \<longmapsto>Target TQ' \<and> (TP', TQ') \<in> TRel\<^sup>*"
    from this obtain TQ' where B1: "TQ \<longmapsto>Target TQ'" and B2: "(TP', TQ') \<in> TRel\<^sup>*"
      by blast
    assume "(TQ, TR) \<in> TRel"
    with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
      by simp
    moreover from B1 have "TargetTerm TQ \<longmapsto>(STCal Source Target) (TargetTerm TQ')"
      by (simp add: STCal_step)
    ultimately obtain R' where B3: "TargetTerm TR \<longmapsto>(STCal Source Target) R'"
                           and B4: "(TargetTerm TQ', R') \<in> Rel"
        using sim
      by blast
    from B3 obtain TR' where B5: "TR' \<in>T R'" and B6: "TR \<longmapsto>Target TR'"
      by (auto simp add: STCal_step)
    from B4 B5 trel have "(TQ', TR') \<in> TRel\<^sup>*"
      by simp
    with B2 have "(TP', TR') \<in> TRel\<^sup>*"
      by simp
    with B6 show "\<exists>TR'. TR \<longmapsto>Target TR' \<and> (TP', TR') \<in> TRel\<^sup>*"
      by blast
  qed
qed

lemma (in encoding) indRelTEQ_impl_TRel_is_strong_reduction_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "strong_reduction_simulation (indRelTEQ TRel) (STCal Source Target)"
  shows "strong_reduction_simulation (TRel\<^sup>*) Target"
      using sim indRelTEQ.target[where TRel="TRel"] indRelTEQ_to_TRel(4)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond
            rel_with_target_impl_reflC_transC_TRel_is_strong_reduction_simulation[where
             Rel="indRelTEQ TRel" and TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_is_weak_barbed_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "weak_barbed_simulation (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_simulation (TRel\<^sup>+) TWB"
proof
  from sim show "weak_reduction_simulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelRTPO_impl_TRel_is_weak_reduction_simulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from sim show "rel_weakly_preserves_barbs (TRel\<^sup>+) TWB"
      using indRelRTPO_impl_TRel_weakly_preserves_barbs[where TRel="TRel"]
            weak_preservation_of_barbs_and_closures(2)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_is_weak_barbed_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "weak_barbed_simulation (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_simulation (TRel\<^sup>+) TWB"
proof
  from sim show "weak_reduction_simulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelLTPO_impl_TRel_is_weak_reduction_simulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from sim show "rel_weakly_preserves_barbs (TRel\<^sup>+) TWB"
      using indRelLTPO_impl_TRel_weakly_preserves_barbs[where TRel="TRel"]
            weak_preservation_of_barbs_and_closures(2)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_is_weak_barbed_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "weak_barbed_simulation (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_simulation (TRel\<^sup>*) TWB"
proof
  from sim show "weak_reduction_simulation (TRel\<^sup>*) (Calculus TWB)"
      using indRelTEQ_impl_TRel_is_weak_reduction_simulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from sim show "rel_weakly_preserves_barbs (TRel\<^sup>*) TWB"
      using indRelTEQ_impl_TRel_weakly_preserves_barbs[where TRel="TRel"]
            weak_preservation_of_barbs_and_closures(3)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_is_strong_barbed_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "strong_barbed_simulation (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "strong_barbed_simulation (TRel\<^sup>+) TWB"
proof
  from sim show "strong_reduction_simulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelRTPO_impl_TRel_is_strong_reduction_simulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from sim show "rel_preserves_barbs (TRel\<^sup>+) TWB"
      using indRelRTPO_impl_TRel_preserves_barbs[where TRel="TRel"]
            preservation_of_barbs_and_closures(2)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_is_strong_barbed_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "strong_barbed_simulation (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "strong_barbed_simulation (TRel\<^sup>+) TWB"
proof
  from sim refl show "strong_reduction_simulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelLTPO_impl_TRel_is_strong_reduction_simulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from sim show "rel_preserves_barbs (TRel\<^sup>+) TWB"
      using indRelLTPO_impl_TRel_preserves_barbs[where TRel="TRel"]
            preservation_of_barbs_and_closures(2)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_is_strong_barbed_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes sim: "strong_barbed_simulation (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "strong_barbed_simulation (TRel\<^sup>*) TWB"
proof
  from sim refl show "strong_reduction_simulation (TRel\<^sup>*) (Calculus TWB)"
      using indRelTEQ_impl_TRel_is_strong_reduction_simulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from sim show "rel_preserves_barbs (TRel\<^sup>*) TWB"
      using indRelTEQ_impl_TRel_preserves_barbs[where TRel="TRel"]
            preservation_of_barbs_and_closures(3)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

text \<open>If indRelRTPO, indRelLTPO, or indRelTEQ is a contrasimulation then so is the corresponding
        target term relation.\<close>

lemma (in encoding) rel_with_target_impl_transC_TRel_is_weak_reduction_contrasimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes conSim: "weak_reduction_contrasimulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
  shows "weak_reduction_contrasimulation (TRel\<^sup>+) Target"
proof clarify
  fix TP TQ TP'
  assume "(TP, TQ) \<in> TRel\<^sup>+" and "TP \<longmapsto>Target* TP'"
  thus "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TQ', TP') \<in> TRel\<^sup>+"
  proof (induct arbitrary: TP')
    fix TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with target have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>Target* TP'"
    hence "TargetTerm TP \<longmapsto>(STCal Source Target)* (TargetTerm TP')"
      by (simp add: STCal_steps)
    ultimately obtain Q' where A2: "TargetTerm TQ \<longmapsto>(STCal Source Target)* Q'"
                           and A3: "(Q', TargetTerm TP') \<in> Rel"
        using conSim
      by blast
    from A2 obtain TQ' where A4: "TQ \<longmapsto>Target* TQ'" and A5: "TQ' \<in>T Q'"
      by (auto simp add: STCal_steps)
    from A3 A5 trel have "(TQ', TP') \<in> TRel\<^sup>+"
      by simp
    with A4 show "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TQ', TP') \<in> TRel\<^sup>+"
      by blast
  next
    case (step TQ TR)
    assume "TP \<longmapsto>Target* TP'"
       and "\<And>TP'. TP \<longmapsto>Target* TP' \<Longrightarrow> \<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TQ', TP') \<in> TRel\<^sup>+"
    from this obtain TQ' where B1: "TQ \<longmapsto>Target* TQ'" and B2: "(TQ', TP') \<in> TRel\<^sup>+"
      by blast
    assume "(TQ, TR) \<in> TRel"
    with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
      by simp
    moreover from B1 have "TargetTerm TQ \<longmapsto>(STCal Source Target)* (TargetTerm TQ')"
      by (simp add: STCal_steps)
    ultimately obtain R' where B3: "TargetTerm TR \<longmapsto>(STCal Source Target)* R'"
                           and B4: "(R', TargetTerm TQ') \<in> Rel"
        using conSim
      by blast
    from B3 obtain TR' where B5: "TR' \<in>T R'" and B6: "TR \<longmapsto>Target* TR'"
      by (auto simp add: STCal_steps)
    from B4 B5 trel have "(TR', TQ') \<in> TRel\<^sup>+"
      by simp
    from this B2 have "(TR', TP') \<in> TRel\<^sup>+"
      by simp
    with B6 show "\<exists>TR'. TR \<longmapsto>Target* TR' \<and> (TR', TP') \<in> TRel\<^sup>+"
      by blast
  qed
qed

lemma (in encoding) indRelRTPO_impl_TRel_is_weak_reduction_contrasimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes conSim: "weak_reduction_contrasimulation (indRelRTPO TRel) (STCal Source Target)"
  shows "weak_reduction_contrasimulation (TRel\<^sup>+) Target"
      using conSim indRelRTPO.target[where TRel="TRel"] indRelRTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_weak_reduction_contrasimulation[where
             Rel="indRelRTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) indRelLTPO_impl_TRel_is_weak_reduction_contrasimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes conSim: "weak_reduction_contrasimulation (indRelLTPO TRel) (STCal Source Target)"
  shows "weak_reduction_contrasimulation (TRel\<^sup>+) Target"
      using conSim indRelLTPO.target[where TRel="TRel"] indRelLTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_weak_reduction_contrasimulation[where
             Rel="indRelLTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) rel_with_target_impl_reflC_transC_TRel_is_weak_reduction_contrasimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes conSim: "weak_reduction_contrasimulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>*"
  shows "weak_reduction_contrasimulation (TRel\<^sup>*) Target"
proof clarify
  fix TP TQ TP'
  assume "(TP, TQ) \<in> TRel\<^sup>*" and "TP \<longmapsto>Target* TP'"
  thus "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TQ', TP') \<in> TRel\<^sup>*"
  proof (induct arbitrary: TP')
    fix TP'
    assume "TP \<longmapsto>Target* TP'"
    moreover have "(TP', TP') \<in> TRel\<^sup>*"
      by simp
    ultimately show "\<exists>TQ'. TP \<longmapsto>Target* TQ' \<and> (TQ', TP') \<in> TRel\<^sup>*"
      by blast
  next
    case (step TQ TR)
    assume "TP \<longmapsto>Target* TP'"
       and "\<And>TP'. TP \<longmapsto>Target* TP' \<Longrightarrow> \<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TQ', TP') \<in> TRel\<^sup>*"
    from this obtain TQ' where B1: "TQ \<longmapsto>Target* TQ'" and B2: "(TQ', TP') \<in> TRel\<^sup>*"
      by blast
    assume "(TQ, TR) \<in> TRel"
    with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
      by simp
    moreover from B1 have "TargetTerm TQ \<longmapsto>(STCal Source Target)* (TargetTerm TQ')"
      by (simp add: STCal_steps)
    ultimately obtain R' where B3: "TargetTerm TR \<longmapsto>(STCal Source Target)* R'"
                           and B4: "(R', TargetTerm TQ') \<in> Rel"
        using conSim
      by blast
    from B3 obtain TR' where B5: "TR' \<in>T R'" and B6: "TR \<longmapsto>Target* TR'"
      by (auto simp add: STCal_steps)
    from B4 B5 trel have "(TR', TQ') \<in> TRel\<^sup>*"
      by simp
    from this B2 have "(TR', TP') \<in> TRel\<^sup>*"
      by simp
    with B6 show "\<exists>TR'. TR \<longmapsto>Target* TR' \<and> (TR', TP') \<in> TRel\<^sup>*"
      by blast
  qed
qed

lemma (in encoding) indRelTEQ_impl_TRel_is_weak_reduction_contrasimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes conSim: "weak_reduction_contrasimulation (indRelTEQ TRel) (STCal Source Target)"
  shows "weak_reduction_contrasimulation (TRel\<^sup>*) Target"
      using conSim indRelTEQ.target[where TRel="TRel"] indRelTEQ_to_TRel(4)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond
            rel_with_target_impl_reflC_transC_TRel_is_weak_reduction_contrasimulation[where
             Rel="indRelTEQ TRel" and TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_is_weak_barbed_contrasimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes conSim: "weak_barbed_contrasimulation (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_contrasimulation (TRel\<^sup>+) TWB"
proof
  from conSim show "weak_reduction_contrasimulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelRTPO_impl_TRel_is_weak_reduction_contrasimulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from conSim show "rel_weakly_preserves_barbs (TRel\<^sup>+) TWB"
      using indRelRTPO_impl_TRel_weakly_preserves_barbs[where TRel="TRel"]
            weak_preservation_of_barbs_and_closures(2)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_is_weak_barbed_contrasimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes conSim: "weak_barbed_contrasimulation (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_contrasimulation (TRel\<^sup>+) TWB"
proof
  from conSim show "weak_reduction_contrasimulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelLTPO_impl_TRel_is_weak_reduction_contrasimulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from conSim show "rel_weakly_preserves_barbs (TRel\<^sup>+) TWB"
      using indRelLTPO_impl_TRel_weakly_preserves_barbs[where TRel="TRel"]
            weak_preservation_of_barbs_and_closures(2)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_is_weak_barbed_contrasimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes conSim: "weak_barbed_contrasimulation (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_contrasimulation (TRel\<^sup>*) TWB"
proof
  from conSim show "weak_reduction_contrasimulation (TRel\<^sup>*) (Calculus TWB)"
      using indRelTEQ_impl_TRel_is_weak_reduction_contrasimulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from conSim show "rel_weakly_preserves_barbs (TRel\<^sup>*) TWB"
      using indRelTEQ_impl_TRel_weakly_preserves_barbs[where TRel="TRel"]
            weak_preservation_of_barbs_and_closures(3)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

text \<open>If indRelRTPO, indRelLTPO, or indRelTEQ is a coupled simulation then so is the
        corresponding target term relation.\<close>

lemma (in encoding) indRelRTPO_impl_TRel_is_weak_reduction_coupled_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes couSim: "weak_reduction_coupled_simulation (indRelRTPO TRel) (STCal Source Target)"
  shows "weak_reduction_coupled_simulation (TRel\<^sup>+) Target"
      using couSim weak_reduction_coupled_simulation_versus_simulation_and_contrasimulation
            refl indRelRTPO_impl_TRel_is_weak_reduction_simulation[where TRel="TRel"]
            indRelRTPO_impl_TRel_is_weak_reduction_contrasimulation[where TRel="TRel"]
    by blast

lemma (in encoding) indRelLTPO_impl_TRel_is_weak_reduction_coupled_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes couSim: "weak_reduction_coupled_simulation (indRelLTPO TRel) (STCal Source Target)"
  shows "weak_reduction_coupled_simulation (TRel\<^sup>+) Target"
      using couSim weak_reduction_coupled_simulation_versus_simulation_and_contrasimulation
            refl indRelLTPO_impl_TRel_is_weak_reduction_simulation[where TRel="TRel"]
            indRelLTPO_impl_TRel_is_weak_reduction_contrasimulation[where TRel="TRel"]
    by blast

lemma (in encoding) indRelTEQ_impl_TRel_is_weak_reduction_coupled_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes couSim: "weak_reduction_coupled_simulation (indRelTEQ TRel) (STCal Source Target)"
  shows "weak_reduction_coupled_simulation (TRel\<^sup>*) Target"
      using couSim weak_reduction_coupled_simulation_versus_simulation_and_contrasimulation
            refl indRelTEQ_impl_TRel_is_weak_reduction_simulation[where TRel="TRel"]
            indRelTEQ_impl_TRel_is_weak_reduction_contrasimulation[where TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_is_weak_barbed_coupled_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes couSim: "weak_barbed_coupled_simulation (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_coupled_simulation (TRel\<^sup>+) TWB"
      using couSim weak_barbed_coupled_simulation_versus_simulation_and_contrasimulation
            refl indRelRTPO_impl_TRel_is_weak_barbed_simulation[where TRel="TRel"]
            indRelRTPO_impl_TRel_is_weak_barbed_contrasimulation[where TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_is_weak_barbed_coupled_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes couSim: "weak_barbed_coupled_simulation (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_coupled_simulation (TRel\<^sup>+) TWB"
      using couSim weak_barbed_coupled_simulation_versus_simulation_and_contrasimulation
            refl indRelLTPO_impl_TRel_is_weak_barbed_simulation[where TRel="TRel"]
            indRelLTPO_impl_TRel_is_weak_barbed_contrasimulation[where TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_is_weak_barbed_coupled_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes couSim: "weak_barbed_coupled_simulation (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_coupled_simulation (TRel\<^sup>*) TWB"
      using couSim weak_barbed_coupled_simulation_versus_simulation_and_contrasimulation
            refl indRelTEQ_impl_TRel_is_weak_barbed_simulation[where TRel="TRel"]
            indRelTEQ_impl_TRel_is_weak_barbed_contrasimulation[where TRel="TRel"]
    by blast

text \<open>If indRelRTPO, indRelLTPO, or indRelTEQ is a correspondence simulation then so is the
        corresponding target term relation.\<close>

lemma (in encoding) rel_with_target_impl_transC_TRel_is_weak_reduction_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes corSim: "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
  shows "weak_reduction_correspondence_simulation (TRel\<^sup>+) Target"
proof -
  from corSim target trel have A: "weak_reduction_simulation (TRel\<^sup>+) Target"
      using rel_with_target_impl_transC_TRel_is_weak_reduction_simulation[where TRel="TRel"
             and Rel="Rel"]
    by blast
  moreover have "\<forall>P Q Q'. (P, Q) \<in> TRel\<^sup>+ \<and> Q \<longmapsto>Target* Q'
                 \<longrightarrow> (\<exists>P'' Q''. P \<longmapsto>Target* P'' \<and> Q' \<longmapsto>Target* Q'' \<and> (P'', Q'') \<in> TRel\<^sup>+)"
  proof clarify
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel\<^sup>+" and "TQ \<longmapsto>Target* TQ'"
    thus "\<exists>TP'' TQ''. TP \<longmapsto>Target* TP'' \<and> TQ' \<longmapsto>Target* TQ'' \<and> (TP'', TQ'') \<in> TRel\<^sup>+"
    proof (induct arbitrary: TQ')
      fix TQ TQ'
      assume "(TP, TQ) \<in> TRel"
      with target have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
        by blast
      moreover assume "TQ \<longmapsto>Target* TQ'"
      hence "TargetTerm TQ \<longmapsto>(STCal Source Target)* (TargetTerm TQ')"
        by (simp add: STCal_steps)
      ultimately obtain P'' Q'' where A2: "TargetTerm TP \<longmapsto>(STCal Source Target)* P''"
        and A3: "TargetTerm TQ' \<longmapsto>(STCal Source Target)* Q''" and A4: "(P'', Q'') \<in> Rel"
          using corSim
        by blast
      from A2 obtain TP'' where A5: "TP \<longmapsto>Target* TP''" and A6: "TP'' \<in>T P''"
        by (auto simp add: STCal_steps)
      from A3 obtain TQ'' where A7: "TQ' \<longmapsto>Target* TQ''" and A8: "TQ'' \<in>T Q''"
        by (auto simp add: STCal_steps)
      from A4 A6 A8 trel have "(TP'', TQ'') \<in> TRel\<^sup>+"
        by blast
      with A5 A7
      show "\<exists>TP'' TQ''. TP \<longmapsto>Target* TP'' \<and> TQ' \<longmapsto>Target* TQ'' \<and> (TP'', TQ'') \<in> TRel\<^sup>+"
        by blast
    next
      case (step TQ TR TR')
      assume "\<And>TQ'. TQ \<longmapsto>Target* TQ'\<Longrightarrow> \<exists>TP'' TQ''. TP \<longmapsto>Target* TP'' \<and> TQ' \<longmapsto>Target* TQ''
              \<and> (TP'', TQ'') \<in> TRel\<^sup>+"
      moreover assume "(TQ, TR) \<in> TRel"
      hence "\<And>TR'. TR \<longmapsto>Target* TR'
             \<longrightarrow> (\<exists>TQ'' TR''. TQ \<longmapsto>Target* TQ'' \<and> TR' \<longmapsto>Target* TR'' \<and> (TQ'', TR'') \<in> TRel\<^sup>+)"
      proof clarify
        fix TR'
        assume "(TQ, TR) \<in> TRel"
        with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
          by simp
        moreover assume "TR \<longmapsto>Target* TR'"
        hence "TargetTerm TR \<longmapsto>(STCal Source Target)* (TargetTerm TR')"
          by (simp add: STCal_steps)
        ultimately obtain Q'' R'' where B1: "TargetTerm TQ \<longmapsto>(STCal Source Target)* Q''"
         and B2: "TargetTerm TR' \<longmapsto>(STCal Source Target)* R''" and B3: "(Q'', R'') \<in> Rel"
            using corSim
          by blast
        from B1 obtain TQ'' where B4: "TQ'' \<in>T Q''" and B5: "TQ \<longmapsto>Target* TQ''"
          by (auto simp add: STCal_steps)
        from B2 obtain TR'' where B6: "TR'' \<in>T R''" and B7: "TR' \<longmapsto>Target* TR''"
          by (auto simp add: STCal_steps)
        from B3 B4 B6 trel have "(TQ'', TR'') \<in> TRel\<^sup>+"
          by simp
        with B5 B7
        show "\<exists>TQ'' TR''. TQ \<longmapsto>Target* TQ'' \<and> TR' \<longmapsto>Target* TR'' \<and> (TQ'', TR'') \<in> TRel\<^sup>+"
          by blast
      qed
      moreover have "trans (TRel\<^sup>+)"
        by simp
      moreover assume "TR \<longmapsto>Target* TR'"
      ultimately
      show "\<exists>TP'' TR''. TP \<longmapsto>Target* TP'' \<and> TR' \<longmapsto>Target* TR'' \<and> (TP'', TR'') \<in> TRel\<^sup>+"
        using A reduction_correspondence_simulation_condition_trans[where Rel="TRel\<^sup>+"
                and Cal="Target"]
        by blast
    qed
  qed
  ultimately show ?thesis
    by simp
qed

lemma (in encoding) indRelRTPO_impl_TRel_is_weak_reduction_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes cSim: "weak_reduction_correspondence_simulation (indRelRTPO TRel) (STCal Source Target)"
  shows "weak_reduction_correspondence_simulation (TRel\<^sup>+) Target"
      using cSim indRelRTPO.target[where TRel="TRel"] indRelRTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_weak_reduction_correspondence_simulation[where
              Rel="indRelRTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) indRelLTPO_impl_TRel_is_weak_reduction_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes cSim: "weak_reduction_correspondence_simulation (indRelLTPO TRel) (STCal Source Target)"
  shows "weak_reduction_correspondence_simulation (TRel\<^sup>+) Target"
      using cSim indRelLTPO.target[where TRel="TRel"] indRelLTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_weak_reduction_correspondence_simulation[where
              Rel="indRelLTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding)
  rel_with_target_impl_reflC_transC_TRel_is_weak_reduction_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes corSim: "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>*"
  shows "weak_reduction_correspondence_simulation (TRel\<^sup>*) Target"
proof -
  from corSim target trel have A: "weak_reduction_simulation (TRel\<^sup>*) Target"
      using rel_with_target_impl_reflC_transC_TRel_is_weak_reduction_simulation[where TRel="TRel"
             and Rel="Rel"]
    by blast
  moreover have "\<forall>P Q Q'. (P, Q) \<in> TRel\<^sup>* \<and> Q \<longmapsto>Target* Q' \<longrightarrow>
    (\<exists>P'' Q''. P \<longmapsto>Target* P'' \<and> Q' \<longmapsto>Target* Q'' \<and> (P'', Q'') \<in> TRel\<^sup>*)"
  proof clarify
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel\<^sup>*" and "TQ \<longmapsto>Target* TQ'"
    thus "\<exists>TP'' TQ''. TP \<longmapsto>Target* TP'' \<and> TQ' \<longmapsto>Target* TQ'' \<and> (TP'', TQ'') \<in> TRel\<^sup>*"
    proof (induct arbitrary: TQ')
      fix TQ'
      assume "TP \<longmapsto>Target* TQ'"
      moreover have "TQ' \<longmapsto>Target* TQ'"
        by (simp add: steps_refl)
      moreover have "(TQ', TQ') \<in> TRel\<^sup>*"
        by simp
      ultimately show "\<exists>TP'' TQ''. TP \<longmapsto>Target* TP'' \<and> TQ' \<longmapsto>Target* TQ'' \<and> (TP'', TQ'') \<in> TRel\<^sup>*"
        by blast
    next
      case (step TQ TR TR')
      assume "\<And>TQ'. TQ \<longmapsto>Target* TQ'\<Longrightarrow> \<exists>TP'' TQ''. TP \<longmapsto>Target* TP'' \<and> TQ' \<longmapsto>Target* TQ''
              \<and> (TP'', TQ'') \<in> TRel\<^sup>*"
      moreover assume "(TQ, TR) \<in> TRel"
      with corSim have "\<And>TR'. TR \<longmapsto>Target* TR' \<Longrightarrow> \<exists>TQ'' TR''. TQ \<longmapsto>Target* TQ''
                        \<and> TR' \<longmapsto>Target* TR'' \<and> (TQ'', TR'') \<in> TRel\<^sup>*"
      proof clarify
        fix TR'
        assume "(TQ, TR) \<in> TRel"
        with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
          by simp
        moreover assume "TR \<longmapsto>Target* TR'"
        hence "TargetTerm TR \<longmapsto>(STCal Source Target)* (TargetTerm TR')"
          by (simp add: STCal_steps)
        ultimately obtain Q'' R'' where B1: "TargetTerm TQ \<longmapsto>(STCal Source Target)* Q''"
         and B2: "TargetTerm TR' \<longmapsto>(STCal Source Target)* R''" and B3: "(Q'', R'') \<in> Rel"
            using corSim
          by blast
        from B1 obtain TQ'' where B4: "TQ'' \<in>T Q''" and B5: "TQ \<longmapsto>Target* TQ''"
          by (auto simp add: STCal_steps)
        from B2 obtain TR'' where B6: "TR'' \<in>T R''" and B7: "TR' \<longmapsto>Target* TR''"
          by (auto simp add: STCal_steps)
        from B3 B4 B6 trel have "(TQ'', TR'') \<in> TRel\<^sup>*"
          by simp
        with B5 B7
        show "\<exists>TQ'' TR''. TQ \<longmapsto>Target* TQ'' \<and> TR' \<longmapsto>Target* TR'' \<and> (TQ'', TR'') \<in> TRel\<^sup>*"
          by blast
      qed
      moreover assume "TR \<longmapsto>Target* TR'"
      moreover have "trans (TRel\<^sup>*)"
          using trans_rtrancl[of TRel]
        by simp
      ultimately show "\<exists>TP'' TR''. TP \<longmapsto>Target* TP'' \<and> TR' \<longmapsto>Target* TR'' \<and> (TP'', TR'') \<in> TRel\<^sup>*"
        using A reduction_correspondence_simulation_condition_trans[where Rel="TRel\<^sup>*"
                and Cal="Target"]
        by blast
    qed
  qed
  ultimately show ?thesis
    by simp
qed

lemma (in encoding) indRelTEQ_impl_TRel_is_weak_reduction_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes corSim: "weak_reduction_correspondence_simulation (indRelTEQ TRel) (STCal Source Target)"
  shows "weak_reduction_correspondence_simulation (TRel\<^sup>*) Target"
      using corSim indRelTEQ.target[where TRel="TRel"] indRelTEQ_to_TRel(4)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond
            rel_with_target_impl_reflC_transC_TRel_is_weak_reduction_correspondence_simulation[
              where Rel="indRelTEQ TRel" and TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_is_weak_barbed_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes corSim: "weak_barbed_correspondence_simulation (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_correspondence_simulation (TRel\<^sup>+) TWB"
proof
  from corSim show "weak_reduction_correspondence_simulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelRTPO_impl_TRel_is_weak_reduction_correspondence_simulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from corSim show "rel_weakly_respects_barbs (TRel\<^sup>+) TWB"
      using indRelRTPO_impl_TRel_weakly_respects_barbs[where TRel="TRel"]
            weak_respection_of_barbs_and_closures(3)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_is_weak_barbed_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes corSim: "weak_barbed_correspondence_simulation (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_correspondence_simulation (TRel\<^sup>+) TWB"
proof
  from corSim show "weak_reduction_correspondence_simulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelLTPO_impl_TRel_is_weak_reduction_correspondence_simulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from corSim show "rel_weakly_respects_barbs (TRel\<^sup>+) TWB"
      using indRelLTPO_impl_TRel_weakly_respects_barbs[where TRel="TRel"]
            weak_respection_of_barbs_and_closures(3)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_is_weak_barbed_correspondence_simulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes corSim: "weak_barbed_correspondence_simulation (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_correspondence_simulation (TRel\<^sup>*) TWB"
proof
  from corSim show "weak_reduction_correspondence_simulation (TRel\<^sup>*) (Calculus TWB)"
      using indRelTEQ_impl_TRel_is_weak_reduction_correspondence_simulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from corSim show "rel_weakly_respects_barbs (TRel\<^sup>*) TWB"
      using indRelTEQ_impl_TRel_weakly_respects_barbs[where TRel="TRel"]
            weak_respection_of_barbs_and_closures(5)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

text \<open>If indRelRTPO, indRelLTPO, or indRelTEQ is a bisimulation then so is the corresponding
        target term relation.\<close>

lemma (in encoding) rel_with_target_impl_transC_TRel_is_weak_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim:  "weak_reduction_bisimulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
  shows "weak_reduction_bisimulation (TRel\<^sup>+) Target"
proof
  from bisim target trel show "weak_reduction_simulation (TRel\<^sup>+) Target"
      using rel_with_target_impl_transC_TRel_is_weak_reduction_simulation[where TRel="TRel"
             and Rel="Rel"]
    by blast
next
  show "\<forall>P Q Q'. (P, Q) \<in> TRel\<^sup>+ \<and> Q \<longmapsto>Target* Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target* P' \<and> (P', Q') \<in> TRel\<^sup>+)"
  proof clarify
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel\<^sup>+" and "TQ \<longmapsto>Target* TQ'"
    thus "\<exists>TP'. TP \<longmapsto>Target* TP' \<and> (TP', TQ') \<in> TRel\<^sup>+"
    proof (induct arbitrary: TQ')
      fix TQ TQ'
      assume "(TP, TQ) \<in> TRel"
      with target have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
        by simp
      moreover assume "TQ \<longmapsto>Target* TQ'"
      hence "TargetTerm TQ \<longmapsto>(STCal Source Target)* (TargetTerm TQ')"
        by (simp add: STCal_steps)
      ultimately obtain P' where A2: "TargetTerm TP \<longmapsto>(STCal Source Target)* P'"
                             and A3: "(P', TargetTerm TQ') \<in> Rel"
          using bisim
        by blast
      from A2 obtain TP' where A4: "TP \<longmapsto>Target* TP'" and A5: "TP' \<in>T P'"
        by (auto simp add: STCal_steps)
      from A3 A5 trel have "(TP', TQ') \<in> TRel\<^sup>+"
        by simp
      with A4 show "\<exists>TP'. TP \<longmapsto>Target* TP' \<and> (TP', TQ') \<in> TRel\<^sup>+"
        by blast
    next
      case (step TQ TR TR')
      assume "(TQ, TR) \<in> TRel"
      with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
        by simp
      moreover assume "TR \<longmapsto>Target* TR'"
      hence "TargetTerm TR \<longmapsto>(STCal Source Target)* (TargetTerm TR')"
        by (simp add: STCal_steps)
      ultimately obtain Q' where B1: "TargetTerm TQ \<longmapsto>(STCal Source Target)* Q'"
                             and B2: "(Q', TargetTerm TR') \<in> Rel"
          using bisim
        by blast
      from B1 obtain TQ' where B3: "TQ' \<in>T Q'" and B4: "TQ \<longmapsto>Target* TQ'"
        by (auto simp add: STCal_steps)
      assume "\<And>TQ'. TQ \<longmapsto>Target* TQ' \<Longrightarrow> \<exists>TP'. TP \<longmapsto>Target* TP' \<and> (TP', TQ') \<in> TRel\<^sup>+"
      with B4 obtain TP' where B5: "TP \<longmapsto>Target* TP'" and B6: "(TP', TQ') \<in> TRel\<^sup>+"
        by blast
      from B2 B3 trel have "(TQ', TR') \<in> TRel\<^sup>+"
        by simp
      with B6 have "(TP', TR') \<in> TRel\<^sup>+"
        by simp
      with B5 show "\<exists>TP'. TP \<longmapsto>Target* TP' \<and> (TP', TR') \<in> TRel\<^sup>+"
        by blast
    qed
  qed
qed

lemma (in encoding) indRelRTPO_impl_TRel_is_weak_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "weak_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
  shows "weak_reduction_bisimulation (TRel\<^sup>+) Target"
      using bisim indRelRTPO.target[where TRel="TRel"] indRelRTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_weak_reduction_bisimulation[where
             Rel="indRelRTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) indRelLTPO_impl_TRel_is_weak_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "weak_reduction_bisimulation (indRelLTPO TRel) (STCal Source Target)"
  shows "weak_reduction_bisimulation (TRel\<^sup>+) Target"
      using bisim indRelLTPO.target[where TRel="TRel"] indRelLTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_weak_reduction_bisimulation[where
             Rel="indRelLTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) rel_with_target_impl_reflC_transC_TRel_is_weak_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim:  "weak_reduction_bisimulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>*"
  shows "weak_reduction_bisimulation (TRel\<^sup>*) Target"
proof
  from bisim target trel show "weak_reduction_simulation (TRel\<^sup>*) Target"
      using rel_with_target_impl_reflC_transC_TRel_is_weak_reduction_simulation[where TRel="TRel"
             and Rel="Rel"]
    by blast
next
  show "\<forall>P Q Q'. (P, Q) \<in> TRel\<^sup>* \<and> Q \<longmapsto>Target* Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target* P' \<and> (P', Q') \<in> TRel\<^sup>*)"
  proof clarify
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel\<^sup>*" and "TQ \<longmapsto>Target* TQ'"
    thus "\<exists>TP'. TP \<longmapsto>Target* TP' \<and> (TP', TQ') \<in> TRel\<^sup>*"
    proof (induct arbitrary: TQ')
      fix TQ'
      assume "TP \<longmapsto>Target* TQ'"
      moreover have "(TQ', TQ') \<in> TRel\<^sup>*"
        by simp
      ultimately show "\<exists>TP'. TP \<longmapsto>Target* TP' \<and> (TP', TQ') \<in> TRel\<^sup>*"
        by blast
    next
      case (step TQ TR TR')
      assume "(TQ, TR) \<in> TRel"
      with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
        by simp
      moreover assume "TR \<longmapsto>Target* TR'"
      hence "TargetTerm TR \<longmapsto>(STCal Source Target)* (TargetTerm TR')"
        by (simp add: STCal_steps)
      ultimately obtain Q' where B1: "TargetTerm TQ \<longmapsto>(STCal Source Target)* Q'"
                             and B2: "(Q', TargetTerm TR') \<in> Rel"
          using bisim
        by blast
      from B1 obtain TQ' where B3: "TQ' \<in>T Q'" and B4: "TQ \<longmapsto>Target* TQ'"
        by (auto simp add: STCal_steps)
      assume "\<And>TQ'. TQ \<longmapsto>Target* TQ' \<Longrightarrow> \<exists>TP'. TP \<longmapsto>Target* TP' \<and> (TP', TQ') \<in> TRel\<^sup>*"
      with B4 obtain TP' where B5: "TP \<longmapsto>Target* TP'" and B6: "(TP', TQ') \<in> TRel\<^sup>*"
        by blast
      from B2 B3 trel have "(TQ', TR') \<in> TRel\<^sup>*"
        by simp
      with B6 have "(TP', TR') \<in> TRel\<^sup>*"
        by simp
      with B5 show "\<exists>TP'. TP \<longmapsto>Target* TP' \<and> (TP', TR') \<in> TRel\<^sup>*"
        by blast
    qed
  qed
qed

lemma (in encoding) indRelTEQ_impl_TRel_is_weak_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "weak_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
  shows "weak_reduction_bisimulation (TRel\<^sup>*) Target"
      using bisim indRelTEQ.target[where TRel="TRel"] indRelTEQ_to_TRel(4)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond
            rel_with_target_impl_reflC_transC_TRel_is_weak_reduction_bisimulation[where
             Rel="indRelTEQ TRel" and TRel="TRel"]
    by blast

lemma (in encoding) rel_with_target_impl_transC_TRel_is_strong_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim:  "strong_reduction_bisimulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
  shows "strong_reduction_bisimulation (TRel\<^sup>+) Target"
proof
  from bisim target trel show "strong_reduction_simulation (TRel\<^sup>+) Target"
      using rel_with_target_impl_transC_TRel_is_strong_reduction_simulation[where Rel="Rel"
              and TRel="TRel"]
    by blast
next
  show "\<forall>P Q Q'. (P, Q) \<in> TRel\<^sup>+ \<and> Q \<longmapsto>Target Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target P' \<and> (P', Q') \<in> TRel\<^sup>+)"
  proof clarify
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel\<^sup>+" and "TQ \<longmapsto>Target TQ'"
    thus "\<exists>TP'. TP \<longmapsto>Target TP' \<and> (TP', TQ') \<in> TRel\<^sup>+"
    proof (induct arbitrary: TQ')
      fix TQ TQ'
      assume "(TP, TQ) \<in> TRel"
      with target have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
        by simp
      moreover assume "TQ \<longmapsto>Target TQ'"
      hence "TargetTerm TQ \<longmapsto>(STCal Source Target) (TargetTerm TQ')"
        by (simp add: STCal_step)
      ultimately obtain P' where A2: "TargetTerm TP \<longmapsto>(STCal Source Target) P'"
                             and A3: "(P', TargetTerm TQ') \<in> Rel"
          using bisim
        by blast
      from A2 obtain TP' where A4: "TP \<longmapsto>Target TP'" and A5: "TP' \<in>T P'"
        by (auto simp add: STCal_step)
      from A3 A5 trel have "(TP', TQ') \<in> TRel\<^sup>+"
        by simp
      with A4 show "\<exists>TP'. TP \<longmapsto>Target TP' \<and> (TP', TQ') \<in> TRel\<^sup>+"
        by blast
    next
      case (step TQ TR TR')
      assume "(TQ, TR) \<in> TRel"
      with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
        by simp
      moreover assume "TR \<longmapsto>Target TR'"
      hence "TargetTerm TR \<longmapsto>(STCal Source Target) (TargetTerm TR')"
        by (simp add: STCal_step)
      ultimately obtain Q' where B1: "TargetTerm TQ \<longmapsto>(STCal Source Target) Q'"
                             and B2: "(Q', TargetTerm TR') \<in> Rel"
          using bisim
        by blast
      from B1 obtain TQ' where B3: "TQ' \<in>T Q'" and B4: "TQ \<longmapsto>Target TQ'"
        by (auto simp add: STCal_step)
      assume "\<And>TQ'. TQ \<longmapsto>Target TQ' \<Longrightarrow> \<exists>TP'. TP \<longmapsto>Target TP' \<and> (TP', TQ') \<in> TRel\<^sup>+"
      with B4 obtain TP' where B5: "TP \<longmapsto>Target TP'" and B6: "(TP', TQ') \<in> TRel\<^sup>+"
        by blast
      from B2 B3 trel have "(TQ', TR') \<in> TRel\<^sup>+"
        by simp
      with B6 have "(TP', TR') \<in> TRel\<^sup>+"
        by simp
      with B5 show "\<exists>TP'. TP \<longmapsto>Target TP' \<and> (TP', TR') \<in> TRel\<^sup>+"
        by blast
    qed
  qed
qed

lemma (in encoding) indRelRTPO_impl_TRel_is_strong_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "strong_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
  shows "strong_reduction_bisimulation (TRel\<^sup>+) Target"
      using bisim indRelRTPO.target[where TRel="TRel"] indRelRTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_strong_reduction_bisimulation[where
             Rel="indRelRTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) indRelLTPO_impl_TRel_is_strong_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "strong_reduction_bisimulation (indRelLTPO TRel) (STCal Source Target)"
  shows "strong_reduction_bisimulation (TRel\<^sup>+) Target"
      using bisim indRelLTPO.target[where TRel="TRel"] indRelLTPO_to_TRel(4)[where TRel="TRel"]
            rel_with_target_impl_transC_TRel_is_strong_reduction_bisimulation[where
             Rel="indRelLTPO TRel" and TRel="TRel"]
    by blast

lemma (in encoding) rel_with_target_impl_reflC_transC_TRel_is_strong_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes bisim:  "strong_reduction_bisimulation Rel (STCal Source Target)"
      and target: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      and trel:   "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>*"
  shows "strong_reduction_bisimulation (TRel\<^sup>*) Target"
proof
  from bisim target trel show "strong_reduction_simulation (TRel\<^sup>*) Target"
      using rel_with_target_impl_reflC_transC_TRel_is_strong_reduction_simulation[where Rel="Rel"
              and TRel="TRel"]
    by blast
next
  show "\<forall>P Q Q'. (P, Q) \<in> TRel\<^sup>* \<and> Q \<longmapsto>Target Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target P' \<and> (P', Q') \<in> TRel\<^sup>*)"
  proof clarify
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel\<^sup>*" and "TQ \<longmapsto>Target TQ'"
    thus "\<exists>TP'. TP \<longmapsto>Target TP' \<and> (TP', TQ') \<in> TRel\<^sup>*"
    proof (induct arbitrary: TQ')
      fix TQ'
      assume "TP \<longmapsto>Target TQ'"
      thus "\<exists>TP'. TP \<longmapsto>Target TP' \<and> (TP', TQ') \<in> TRel\<^sup>*"
        by blast
    next
      case (step TQ TR TR')
      assume "(TQ, TR) \<in> TRel"
      with target have "(TargetTerm TQ, TargetTerm TR) \<in> Rel"
        by simp
      moreover assume "TR \<longmapsto>Target TR'"
      hence "TargetTerm TR \<longmapsto>(STCal Source Target) (TargetTerm TR')"
        by (simp add: STCal_step)
      ultimately obtain Q' where B1: "TargetTerm TQ \<longmapsto>(STCal Source Target) Q'"
                             and B2: "(Q', TargetTerm TR') \<in> Rel"
          using bisim
        by blast
      from B1 obtain TQ' where B3: "TQ' \<in>T Q'" and B4: "TQ \<longmapsto>Target TQ'"
        by (auto simp add: STCal_step)
      assume "\<And>TQ'. TQ \<longmapsto>Target TQ' \<Longrightarrow> \<exists>TP'. TP \<longmapsto>Target TP' \<and> (TP', TQ') \<in> TRel\<^sup>*"
      with B4 obtain TP' where B5: "TP \<longmapsto>Target TP'" and B6: "(TP', TQ') \<in> TRel\<^sup>*"
        by blast
      from B2 B3 trel have "(TQ', TR') \<in> TRel\<^sup>*"
        by simp
      with B6 have "(TP', TR') \<in> TRel\<^sup>*"
        by simp
      with B5 show "\<exists>TP'. TP \<longmapsto>Target TP' \<and> (TP', TR') \<in> TRel\<^sup>*"
        by blast
    qed
  qed
qed

lemma (in encoding) indRelTEQ_impl_TRel_is_strong_reduction_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "strong_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
  shows "strong_reduction_bisimulation (TRel\<^sup>*) Target"
      using bisim indRelTEQ.target[where TRel="TRel"] indRelTEQ_to_TRel(4)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond
            rel_with_target_impl_reflC_transC_TRel_is_strong_reduction_bisimulation[where
             Rel="indRelTEQ TRel" and TRel="TRel"]
    by blast

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_is_weak_barbed_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "weak_barbed_bisimulation (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_bisimulation (TRel\<^sup>+) TWB"
proof
  from bisim show "weak_reduction_bisimulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelRTPO_impl_TRel_is_weak_reduction_bisimulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from bisim show "rel_weakly_respects_barbs (TRel\<^sup>+) TWB"
      using indRelRTPO_impl_TRel_weakly_respects_barbs[where TRel="TRel"]
            weak_respection_of_barbs_and_closures(3)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_is_weak_barbed_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "weak_barbed_bisimulation (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_bisimulation (TRel\<^sup>+) TWB"
proof
  from bisim show "weak_reduction_bisimulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelLTPO_impl_TRel_is_weak_reduction_bisimulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from bisim show "rel_weakly_respects_barbs (TRel\<^sup>+) TWB"
      using indRelLTPO_impl_TRel_weakly_respects_barbs[where TRel="TRel"]
            weak_respection_of_barbs_and_closures(3)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_is_weak_barbed_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "weak_barbed_bisimulation (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "weak_barbed_bisimulation (TRel\<^sup>*) TWB"
proof
  from bisim show "weak_reduction_bisimulation (TRel\<^sup>*) (Calculus TWB)"
      using indRelTEQ_impl_TRel_is_weak_reduction_bisimulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from bisim show "rel_weakly_respects_barbs (TRel\<^sup>*) TWB"
      using indRelTEQ_impl_TRel_weakly_respects_barbs[where TRel="TRel"]
            weak_respection_of_barbs_and_closures(5)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelRTPO_impl_TRel_is_strong_barbed_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "strong_barbed_bisimulation (indRelRTPO TRel) (STCalWB SWB TWB)"
  shows "strong_barbed_bisimulation (TRel\<^sup>+) TWB"
proof
  from bisim show "strong_reduction_bisimulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelRTPO_impl_TRel_is_strong_reduction_bisimulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from bisim show "rel_respects_barbs (TRel\<^sup>+) TWB"
      using indRelRTPO_impl_TRel_respects_barbs[where TRel="TRel"]
            respection_of_barbs_and_closures(3)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelLTPO_impl_TRel_is_strong_barbed_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "strong_barbed_bisimulation (indRelLTPO TRel) (STCalWB SWB TWB)"
  shows "strong_barbed_bisimulation (TRel\<^sup>+) TWB"
proof
  from bisim refl show "strong_reduction_bisimulation (TRel\<^sup>+) (Calculus TWB)"
      using indRelLTPO_impl_TRel_is_strong_reduction_bisimulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from bisim show "rel_respects_barbs (TRel\<^sup>+) TWB"
      using indRelLTPO_impl_TRel_respects_barbs[where TRel="TRel"]
            respection_of_barbs_and_closures(3)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelTEQ_impl_TRel_is_strong_barbed_bisimulation:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes bisim: "strong_barbed_bisimulation (indRelTEQ TRel) (STCalWB SWB TWB)"
  shows "strong_barbed_bisimulation (TRel\<^sup>*) TWB"
proof
  from bisim refl show "strong_reduction_bisimulation (TRel\<^sup>*) (Calculus TWB)"
      using indRelTEQ_impl_TRel_is_strong_reduction_bisimulation[where TRel="TRel"]
    by (simp add: STCalWB_def calS calT)
next
  from bisim show "rel_respects_barbs (TRel\<^sup>*) TWB"
      using indRelTEQ_impl_TRel_respects_barbs[where TRel="TRel"]
            respection_of_barbs_and_closures(5)[where Rel="TRel" and CWB="TWB"]
    by blast
qed

subsection \<open>Relations Induced by the Encoding and Relations on Source Terms and Target Terms\<close>

text \<open>Some encodability like e.g. full abstraction are defined w.r.t. a relation on source terms
        and a relation on target terms. To analyse such criteria we include these two relations in
        the considered relation on the disjoint union of source and target terms.\<close>

inductive_set (in encoding) indRelRST
    :: "('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  where
  encR:   "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRST SRel TRel" |
  source: "(S1, S2) \<in> SRel \<Longrightarrow> (SourceTerm S1, SourceTerm S2) \<in> indRelRST SRel TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelRST SRel TRel"

abbreviation (in encoding) indRelRSTinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<R>\<lbrakk>\<cdot>\<rbrakk>R<_,_> _" [75, 75, 75, 75] 80)
  where
  "P \<R>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q \<equiv> (P, Q) \<in> indRelRST SRel TRel"

inductive_set (in encoding) indRelRSTPO
    :: "('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  where
  encR:   "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelRSTPO SRel TRel" |
  source: "(S1, S2) \<in> SRel \<Longrightarrow> (SourceTerm S1, SourceTerm S2) \<in> indRelRSTPO SRel TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelRSTPO SRel TRel" |
  trans:  "\<lbrakk>(P, Q) \<in> indRelRSTPO SRel TRel; (Q, R) \<in> indRelRSTPO SRel TRel\<rbrakk>
           \<Longrightarrow> (P, R) \<in> indRelRSTPO SRel TRel"

abbreviation (in encoding) indRelRSTPOinfix ::
    "('procS, 'procT) Proc \<Rightarrow> ('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
     \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<_,_> _" [75, 75, 75, 75] 80)
  where
  "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q \<equiv> (P, Q) \<in> indRelRSTPO SRel TRel"

lemma (in encoding) indRelRSTPO_refl:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflS: "refl SRel"
      and reflT: "refl TRel"
  shows "refl (indRelRSTPO SRel TRel)"
    unfolding refl_on_def
proof auto
  fix P
  show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
  proof (cases P)
    case (SourceTerm SP)
    assume "SP \<in>S P"
    with reflS show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
        unfolding refl_on_def
      by (simp add: indRelRSTPO.source)
  next
    case (TargetTerm TP)
    assume "TP \<in>T P"
    with reflT show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
        unfolding refl_on_def
      by (simp add: indRelRSTPO.target)
  qed
qed

lemma (in encoding) indRelRSTPO_trans:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  shows "trans (indRelRSTPO SRel TRel)"
    unfolding trans_def
proof clarify
  fix P Q R
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q" and "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R"
  thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R"
    by (rule indRelRSTPO.trans)
qed

lemma (in encoding) refl_trans_closure_of_indRelRST:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflS: "refl SRel"
      and reflT: "refl TRel"
  shows "indRelRSTPO SRel TRel = (indRelRST SRel TRel)\<^sup>*"
proof auto
  fix P Q
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q"
  thus "(P, Q) \<in> (indRelRST SRel TRel)\<^sup>*"
  proof induct
    case (encR S)
    show "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> (indRelRST SRel TRel)\<^sup>*"
        using indRelRST.encR[of S SRel TRel]
      by simp
  next
    case (source S1 S2)
    assume "(S1, S2) \<in> SRel"
    thus "(SourceTerm S1, SourceTerm S2) \<in> (indRelRST SRel TRel)\<^sup>*"
        using indRelRST.source[of S1 S2 SRel TRel]
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    thus "(TargetTerm T1, TargetTerm T2) \<in> (indRelRST SRel TRel)\<^sup>*"
        using indRelRST.target[of T1 T2 TRel SRel]
      by simp
  next
    case (trans P Q R)
    assume "(P, Q) \<in> (indRelRST SRel TRel)\<^sup>*" and "(Q, R) \<in> (indRelRST SRel TRel)\<^sup>*"
    thus "(P, R) \<in> (indRelRST SRel TRel)\<^sup>*"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> (indRelRST SRel TRel)\<^sup>*"
  thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q"
  proof induct
    from reflS reflT show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
        using indRelRSTPO_refl[of SRel TRel]
        unfolding refl_on_def
      by simp
  next
    case (step Q R)
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q"
    moreover assume "Q \<R>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R"
    hence "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R"
      by (induct, simp_all add: indRelRSTPO.intros)
    ultimately show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R"
      by (rule indRelRSTPO.trans)
  qed
qed

inductive_set (in encoding) indRelLST
    :: "('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  where
  encL:   "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelLST SRel TRel" |
  source: "(S1, S2) \<in> SRel \<Longrightarrow> (SourceTerm S1, SourceTerm S2) \<in> indRelLST SRel TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelLST SRel TRel"

abbreviation (in encoding) indRelLSTinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<R>\<lbrakk>\<cdot>\<rbrakk>L<_,_> _" [75, 75, 75, 75] 80)
  where
  "P \<R>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> Q \<equiv> (P, Q) \<in> indRelLST SRel TRel"

inductive_set (in encoding) indRelLSTPO
    :: "('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  where
  encL:   "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelLSTPO SRel TRel" |
  source: "(S1, S2) \<in> SRel \<Longrightarrow> (SourceTerm S1, SourceTerm S2) \<in> indRelLSTPO SRel TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelLSTPO SRel TRel" |
  trans:  "\<lbrakk>(P, Q) \<in> indRelLSTPO SRel TRel; (Q, R) \<in> indRelLSTPO SRel TRel\<rbrakk>
           \<Longrightarrow> (P, R) \<in> indRelLSTPO SRel TRel"

abbreviation (in encoding) indRelLSTPOinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<_,_> _" [75, 75, 75, 75] 80)
  where
  "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> Q \<equiv> (P, Q) \<in> indRelLSTPO SRel TRel"

lemma (in encoding) indRelLSTPO_refl:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflS: "refl SRel"
      and reflT: "refl TRel"
  shows "refl (indRelLSTPO SRel TRel)"
    unfolding refl_on_def
proof auto
  fix P
  show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> P"
  proof (cases P)
    case (SourceTerm SP)
    assume "SP \<in>S P"
    with reflS show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> P"
        unfolding refl_on_def
      by (simp add: indRelLSTPO.source)
  next
    case (TargetTerm TP)
    assume "TP \<in>T P"
    with reflT show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> P"
        unfolding refl_on_def
      by (simp add: indRelLSTPO.target)
  qed
qed

lemma (in encoding) indRelLSTPO_trans:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  shows "trans (indRelLSTPO SRel TRel)"
    unfolding trans_def
proof clarify
  fix P Q R
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> Q" and "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> R"
  thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> R"
    by (rule indRelLSTPO.trans)
qed

lemma (in encoding) refl_trans_closure_of_indRelLST:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflS: "refl SRel"
      and reflT: "refl TRel"
  shows "indRelLSTPO SRel TRel = (indRelLST SRel TRel)\<^sup>*"
proof auto
  fix P Q
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> Q"
  thus "(P, Q) \<in> (indRelLST SRel TRel)\<^sup>*"
  proof induct
    case (encL S)
    show "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> (indRelLST SRel TRel)\<^sup>*"
        using indRelLST.encL[of S SRel TRel]
      by simp
  next
    case (source S1 S2)
    assume "(S1, S2) \<in> SRel"
    thus "(SourceTerm S1, SourceTerm S2) \<in> (indRelLST SRel TRel)\<^sup>*"
        using indRelLST.source[of S1 S2 SRel TRel]
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    thus "(TargetTerm T1, TargetTerm T2) \<in> (indRelLST SRel TRel)\<^sup>*"
        using indRelLST.target[of T1 T2 TRel SRel]
      by simp
  next
    case (trans P Q R)
    assume "(P, Q) \<in> (indRelLST SRel TRel)\<^sup>*" and "(Q, R) \<in> (indRelLST SRel TRel)\<^sup>*"
    thus "(P, R) \<in> (indRelLST SRel TRel)\<^sup>*"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> (indRelLST SRel TRel)\<^sup>*"
  thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> Q"
  proof induct
    from reflS reflT show " P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> P"
        using indRelLSTPO_refl[of SRel TRel]
        unfolding refl_on_def
      by simp
  next
    case (step Q R)
    assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> Q"
    moreover assume "Q \<R>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> R"
    hence "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> R"
      by (induct, simp_all add: indRelLSTPO.intros)
    ultimately show "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> R"
      by (rule indRelLSTPO.trans)
  qed
qed

inductive_set (in encoding) indRelST
    :: "('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  where
  encR:   "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelST SRel TRel" |
  encL:   "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelST SRel TRel" |
  source: "(S1, S2) \<in> SRel \<Longrightarrow> (SourceTerm S1, SourceTerm S2) \<in> indRelST SRel TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelST SRel TRel"

abbreviation (in encoding) indRelSTinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<R>\<lbrakk>\<cdot>\<rbrakk><_,_> _" [75, 75, 75, 75] 80)
  where
  "P \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q \<equiv> (P, Q) \<in> indRelST SRel TRel"

lemma (in encoding) indRelST_symm:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes symmS: "sym SRel"
      and symmT: "sym TRel"
  shows "sym (indRelST SRel TRel)"
    unfolding sym_def
proof clarify
  fix P Q
  assume "(P, Q) \<in> indRelST SRel TRel"
  thus "(Q, P) \<in> indRelST SRel TRel"
  proof induct
    case (encR S)
    show "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelST SRel TRel"
      by (rule indRelST.encL)
  next
    case (encL S)
    show "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelST SRel TRel"
      by (rule indRelST.encR)
  next
    case (source S1 S2)
    assume "(S1, S2) \<in> SRel"
    with symmS show "(SourceTerm S2, SourceTerm S1) \<in> indRelST SRel TRel"
        unfolding sym_def
      by (simp add: indRelST.source)
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    with symmT show "(TargetTerm T2, TargetTerm T1) \<in> indRelST SRel TRel"
        unfolding sym_def
      by (simp add: indRelST.target)
  qed
qed

inductive_set (in encoding) indRelSTEQ
    :: "('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ((('procS, 'procT) Proc) \<times> (('procS, 'procT) Proc)) set"
    for SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  where
  encR:   "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelSTEQ SRel TRel" |
  encL:   "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> indRelSTEQ SRel TRel" |
  source: "(S1, S2) \<in> SRel \<Longrightarrow> (SourceTerm S1, SourceTerm S2) \<in> indRelSTEQ SRel TRel" |
  target: "(T1, T2) \<in> TRel \<Longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> indRelSTEQ SRel TRel" |
  trans:  "\<lbrakk>(P, Q) \<in> indRelSTEQ SRel TRel; (Q, R) \<in> indRelSTEQ SRel TRel\<rbrakk>
           \<Longrightarrow> (P, R) \<in> indRelSTEQ SRel TRel"

abbreviation (in encoding) indRelSTEQinfix
    :: "('procS, 'procT) Proc \<Rightarrow> ('procS \<times> 'procS) set \<Rightarrow> ('procT \<times> 'procT) set
        \<Rightarrow> ('procS, 'procT) Proc \<Rightarrow> bool" ("_ \<sim>\<lbrakk>\<cdot>\<rbrakk><_,_> _" [75, 75, 75, 75] 80)
  where
  "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q \<equiv> (P, Q) \<in> indRelSTEQ SRel TRel"

lemma (in encoding) indRelSTEQ_refl:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflT: "refl TRel"
  shows "refl (indRelSTEQ SRel TRel)"
    unfolding refl_on_def
proof auto
  fix P
  show "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> P"
  proof (cases P)
    case (SourceTerm SP)
    assume "SP \<in>S P"
    moreover have "SourceTerm SP \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>SP\<rbrakk>)"
      by (rule indRelSTEQ.encR)
    moreover have "TargetTerm (\<lbrakk>SP\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm SP"
      by (rule indRelSTEQ.encL)
    ultimately show "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> P"
      by (simp add: indRelSTEQ.trans[where P="SourceTerm SP" and Q="TargetTerm (\<lbrakk>SP\<rbrakk>)"])
  next
    case (TargetTerm TP)
    assume "TP \<in>T P"
    with reflT show "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> P"
        unfolding refl_on_def
      by (simp add: indRelSTEQ.target)
  qed
qed

lemma (in encoding) indRelSTEQ_symm:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes symmS: "sym SRel"
      and symmT: "sym TRel"
  shows "sym (indRelSTEQ SRel TRel)"
    unfolding sym_def
proof clarify
  fix P Q
  assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
  thus "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> P"
  proof induct
    case (encR S)
    show "TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S"
      by (rule indRelSTEQ.encL)
  next
    case (encL S)
    show "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelSTEQ.encR)
  next
    case (source S1 S2)
    assume "(S1, S2) \<in> SRel"
    with symmS show "SourceTerm S2 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S1"
        unfolding sym_def
      by (simp add: indRelSTEQ.source)
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    with symmT show "TargetTerm T2 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T1"
        unfolding sym_def
      by (simp add: indRelSTEQ.target)
  next
    case (trans P Q R)
    assume "R \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> P"
    thus "R \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> P"
      by (rule indRelSTEQ.trans)
  qed
qed

lemma (in encoding) indRelSTEQ_trans:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  shows "trans (indRelSTEQ SRel TRel)"
    unfolding trans_def
proof clarify
  fix P Q R
  assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
  thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
    by (rule indRelSTEQ.trans)
qed

lemma (in encoding) refl_trans_closure_of_indRelST:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflT: "refl TRel"
  shows "indRelSTEQ SRel TRel = (indRelST SRel TRel)\<^sup>*"
proof auto
  fix P Q
  assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
  thus "(P, Q) \<in> (indRelST SRel TRel)\<^sup>*"
  proof induct
    case (encR S)
    show "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> (indRelST SRel TRel)\<^sup>*"
        using indRelST.encR[of S SRel TRel]
      by simp
  next
    case (encL S)
    show "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> (indRelST SRel TRel)\<^sup>*"
        using indRelST.encL[of S SRel TRel]
      by simp
  next
    case (source S1 S2)
    assume "(S1, S2) \<in> SRel"
    thus "(SourceTerm S1, SourceTerm S2) \<in> (indRelST SRel TRel)\<^sup>*"
        using indRelST.source[of S1 S2 SRel TRel]
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    thus "(TargetTerm T1, TargetTerm T2) \<in> (indRelST SRel TRel)\<^sup>*"
        using indRelST.target[of T1 T2 TRel SRel]
      by simp
  next
    case (trans P Q R)
    assume "(P, Q) \<in> (indRelST SRel TRel)\<^sup>*" and "(Q, R) \<in> (indRelST SRel TRel)\<^sup>*"
    thus "(P, R) \<in> (indRelST SRel TRel)\<^sup>*"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> (indRelST SRel TRel)\<^sup>*"
  thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
  proof induct
    from reflT show "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> P"
        using indRelSTEQ_refl[of TRel SRel]
        unfolding refl_on_def
      by simp
  next
    case (step Q R)
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
    moreover assume "Q \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
    hence "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
      by (induct, simp_all add: indRelSTEQ.intros)
    ultimately show "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
      by (rule indRelSTEQ.trans)
  qed
qed

lemma (in encoding) refl_symm_trans_closure_of_indRelST:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflT: "refl TRel"
      and symmS: "sym SRel"
      and symmT: "sym TRel"
  shows "indRelSTEQ SRel TRel = (symcl ((indRelST SRel TRel)\<^sup>=))\<^sup>+"
proof -
  have "(symcl ((indRelST SRel TRel)\<^sup>=))\<^sup>+ = (symcl (indRelST SRel TRel))\<^sup>*"
    by (rule refl_symm_trans_closure_is_symm_refl_trans_closure[where Rel="indRelST SRel TRel"])
  moreover from symmS symmT have "symcl (indRelST SRel TRel) = indRelST SRel TRel"
      using indRelST_symm[where SRel="SRel" and TRel="TRel"]
            symm_closure_of_symm_rel[where Rel="indRelST SRel TRel"]
    by blast
  ultimately show "indRelSTEQ SRel TRel = (symcl ((indRelST SRel TRel)\<^sup>=))\<^sup>+"
      using reflT refl_trans_closure_of_indRelST[where SRel="SRel" and TRel="TRel"]
    by simp
qed

lemma (in encoding) symm_closure_of_indRelRST:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflT: "refl TRel"
      and symmS: "sym SRel"
      and symmT: "sym TRel"
  shows "indRelST SRel TRel = symcl (indRelRST SRel TRel)"
    and "indRelSTEQ SRel TRel = (symcl ((indRelRST SRel TRel)\<^sup>=))\<^sup>+"
proof -
  show "indRelST SRel TRel = symcl (indRelRST SRel TRel)"
  proof auto
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
    thus "(P, Q) \<in> symcl (indRelRST SRel TRel)"
      by (induct, simp_all add: symcl_def indRelRST.intros)
  next
    fix P Q
    assume "(P, Q) \<in> symcl (indRelRST SRel TRel)"
    thus "P \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
    proof (auto simp add: symcl_def indRelRST.simps)
      fix S
      show "SourceTerm S \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
        by (rule indRelST.encR)
    next
      fix S1 S2
      assume "(S1, S2) \<in> SRel"
      thus "SourceTerm S1 \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2"
        by (rule indRelST.source)
    next
      fix T1 T2
      assume "(T1, T2) \<in> TRel"
      thus "TargetTerm T1 \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2"
        by (rule indRelST.target)
    next
      fix S
      show "TargetTerm (\<lbrakk>S\<rbrakk>) \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S"
        by (rule indRelST.encL)
    next
      fix S1 S2
      assume "(S1, S2) \<in> SRel"
      with symmS show "SourceTerm S2 \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S1"
          unfolding sym_def
        by (simp add: indRelST.source)
    next
      fix T1 T2
      assume "(T1, T2) \<in> TRel"
      with symmT show "(TargetTerm T2, TargetTerm T1) \<in> indRelST SRel TRel"
          unfolding sym_def
        by (simp add: indRelST.target)
    qed
  qed
  with reflT show "indRelSTEQ SRel TRel = (symcl ((indRelRST SRel TRel)\<^sup>=))\<^sup>+"
      using refl_symm_trans_closure_is_symm_refl_trans_closure[where Rel="indRelRST SRel TRel"]
            refl_trans_closure_of_indRelST
    by simp
qed

lemma (in encoding) symm_closure_of_indRelLST:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflT: "refl TRel"
      and symmS: "sym SRel"
      and symmT: "sym TRel"
  shows "indRelST SRel TRel = symcl (indRelLST SRel TRel)"
    and "indRelSTEQ SRel TRel = (symcl ((indRelLST SRel TRel)\<^sup>=))\<^sup>+"
proof -
  show "indRelST SRel TRel = symcl (indRelLST SRel TRel)"
  proof auto
    fix P Q
    assume "P \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
    thus "(P, Q) \<in> symcl (indRelLST SRel TRel)"
      by (induct, simp_all add: symcl_def indRelLST.intros)
  next
    fix P Q
    assume "(P, Q) \<in> symcl (indRelLST SRel TRel)"
    thus "P \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
    proof (auto simp add: symcl_def indRelLST.simps)
      fix S
      show "SourceTerm S \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
        by (rule indRelST.encR)
    next
      fix S1 S2
      assume "(S1, S2) \<in> SRel"
      thus "SourceTerm S1 \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2"
        by (rule indRelST.source)
    next
      fix T1 T2
      assume "(T1, T2) \<in> TRel"
      thus "TargetTerm T1 \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2"
        by (rule indRelST.target)
    next
      fix S
      show "TargetTerm (\<lbrakk>S\<rbrakk>) \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S"
        by (rule indRelST.encL)
    next
      fix S1 S2
      assume "(S1, S2) \<in> SRel"
      with symmS show "SourceTerm S2 \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S1"
          unfolding sym_def
        by (simp add: indRelST.source)
    next
      fix T1 T2
      assume "(T1, T2) \<in> TRel"
      with symmT show "TargetTerm T2 \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T1"
          unfolding sym_def
        by (simp add: indRelST.target)
    qed
  qed
  with reflT show "indRelSTEQ SRel TRel = (symcl ((indRelLST SRel TRel)\<^sup>=))\<^sup>+"
      using refl_symm_trans_closure_is_symm_refl_trans_closure[where Rel="indRelLST SRel TRel"]
            refl_trans_closure_of_indRelST
    by simp
qed

lemma (in encoding) symm_trans_closure_of_indRelRSTPO:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes symmS: "sym SRel"
      and symmT: "sym TRel"
  shows "indRelSTEQ SRel TRel = (symcl (indRelRSTPO SRel TRel))\<^sup>+"
proof auto
  fix P Q
  assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
  thus "(P, Q) \<in> (symcl (indRelRSTPO SRel TRel))\<^sup>+"
  proof induct
    case (encR S)
    show "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> (symcl (indRelRSTPO SRel TRel))\<^sup>+"
        using indRelRSTPO.encR[of S SRel TRel]
        unfolding symcl_def
      by auto
  next
    case (encL S)
    show "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> (symcl (indRelRSTPO SRel TRel))\<^sup>+"
        using indRelRSTPO.encR[of S SRel TRel]
        unfolding symcl_def
      by auto
  next
    case (source S1 S2)
    assume "(S1, S2) \<in> SRel"
    thus "(SourceTerm S1, SourceTerm S2) \<in> (symcl (indRelRSTPO SRel TRel))\<^sup>+"
        using indRelRSTPO.source[of S1 S2 SRel TRel]
        unfolding symcl_def
      by auto
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    thus "(TargetTerm T1, TargetTerm T2) \<in> (symcl (indRelRSTPO SRel TRel))\<^sup>+"
        using indRelRSTPO.target[of T1 T2 TRel SRel]
        unfolding symcl_def
      by auto
  next
    case (trans P Q R)
    assume "(P, Q) \<in> (symcl (indRelRSTPO SRel TRel))\<^sup>+"
       and "(Q, R) \<in> (symcl (indRelRSTPO SRel TRel))\<^sup>+"
    thus "(P, R) \<in> (symcl (indRelRSTPO SRel TRel))\<^sup>+"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> (symcl (indRelRSTPO SRel TRel))\<^sup>+"
  thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
  proof induct
    fix Q
    assume "(P, Q) \<in> symcl (indRelRSTPO SRel TRel)"
    thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
    proof (cases "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q", simp_all add: symcl_def)
      assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q"
      thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
      proof induct
        case (encR S)
        show "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
          by (rule indRelSTEQ.encR)
      next
        case (source S1 S2)
        assume "(S1, S2) \<in> SRel"
        thus "SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2"
          by (rule indRelSTEQ.source)
      next
        case (target T1 T2)
        assume "(T1, T2) \<in> TRel"
        thus "TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2"
          by (rule indRelSTEQ.target)
      next
        case (trans P Q R)
        assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
        thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (rule indRelSTEQ.trans)
      qed
    next
      assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> P"
      thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
      proof induct
        case (encR S)
        show "TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S"
          by (rule indRelSTEQ.encL)
      next
        case (source S1 S2)
        assume "(S1, S2) \<in> SRel"
        with symmS show "SourceTerm S2 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S1"
            unfolding sym_def
          by (simp add: indRelSTEQ.source)
      next
        case (target T1 T2)
        assume "(T1, T2) \<in> TRel"
        with symmT show "TargetTerm T2 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T1"
            unfolding sym_def
          by (simp add: indRelSTEQ.target)
      next
        case (trans P Q R)
        assume "R \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> P"
        thus "R \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> P"
          by (rule indRelSTEQ.trans)
      qed
    qed
  next
    case (step Q R)
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
    moreover assume "(Q, R) \<in> symcl (indRelRSTPO SRel TRel)"
    hence "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
    proof (auto simp add: symcl_def)
      assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R"
      thus "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
      proof (induct, simp add: indRelSTEQ.encR, simp add: indRelSTEQ.source,
             simp add: indRelSTEQ.target)
        case (trans P Q R)
        assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
        thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (rule indRelSTEQ.trans)
      qed
    next
      assume "R \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q"
      hence "R \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
      proof (induct, simp add: indRelSTEQ.encR, simp add: indRelSTEQ.source,
             simp add: indRelSTEQ.target)
        case (trans P Q R)
        assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
        thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (rule indRelSTEQ.trans)
      qed
      with symmS symmT show "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          using indRelSTEQ_symm[of SRel TRel]
          unfolding sym_def
        by blast
    qed
    ultimately show "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
      by (rule indRelSTEQ.trans)
  qed
qed

lemma (in encoding) symm_trans_closure_of_indRelLSTPO:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes symmS: "sym SRel"
      and symmT: "sym TRel"
  shows "indRelSTEQ SRel TRel = (symcl (indRelLSTPO SRel TRel))\<^sup>+"
proof auto
  fix P Q
  assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
  thus "(P, Q) \<in> (symcl (indRelLSTPO SRel TRel))\<^sup>+"
  proof induct
    case (encR S)
    show "(SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> (symcl (indRelLSTPO SRel TRel))\<^sup>+"
        using indRelLSTPO.encL[of S SRel TRel]
        unfolding symcl_def
      by blast
  next
    case (encL S)
    show "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> (symcl (indRelLSTPO SRel TRel))\<^sup>+"
        using indRelLSTPO.encL[of S SRel TRel]
        unfolding symcl_def
      by blast
  next
    case (source S1 S2)
    assume "(S1, S2) \<in> SRel"
    thus "(SourceTerm S1, SourceTerm S2) \<in> (symcl (indRelLSTPO SRel TRel))\<^sup>+"
        using indRelLSTPO.source[of S1 S2 SRel TRel]
        unfolding symcl_def
      by blast
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    thus "(TargetTerm T1, TargetTerm T2) \<in> (symcl (indRelLSTPO SRel TRel))\<^sup>+"
        using indRelLSTPO.target[of T1 T2 TRel SRel]
        unfolding symcl_def
      by blast
  next
    case (trans P Q R)
    assume "(P, Q) \<in> (symcl (indRelLSTPO SRel TRel))\<^sup>+"
       and "(Q, R) \<in> (symcl (indRelLSTPO SRel TRel))\<^sup>+"
    thus "(P, R) \<in> (symcl (indRelLSTPO SRel TRel))\<^sup>+"
      by simp
  qed
next
  fix P Q
  assume "(P, Q) \<in> (symcl (indRelLSTPO SRel TRel))\<^sup>+"
  thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
  proof induct
    fix Q
    assume "(P, Q) \<in> symcl (indRelLSTPO SRel TRel)"
    thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
      unfolding symcl_def
    proof auto
      assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> Q"
      thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
      proof (induct, simp add: indRelSTEQ.encL, simp add: indRelSTEQ.source,
             simp add: indRelSTEQ.target)
        case (trans P Q R)
        assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
        thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (rule indRelSTEQ.trans)
      qed
    next
      assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> P"
      hence "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> P"
      proof (induct, simp add: indRelSTEQ.encL, simp add: indRelSTEQ.source,
             simp add: indRelSTEQ.target)
        case (trans P Q R)
        assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
        thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (rule indRelSTEQ.trans)
      qed
      with symmS symmT show "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
          using indRelSTEQ_symm[of SRel TRel]
          unfolding sym_def
        by blast
    qed
  next
    case (step Q R)
    assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
    moreover assume "(Q, R) \<in> symcl (indRelLSTPO SRel TRel)"
    hence "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
      unfolding symcl_def
    proof auto
      assume "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> R"
      thus "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
      proof (induct, simp add: indRelSTEQ.encL, simp add: indRelSTEQ.source,
             simp add: indRelSTEQ.target)
        case (trans P Q R)
        assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
        thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (rule indRelSTEQ.trans)
      qed
    next
      assume "R \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> Q"
      hence "R \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
      proof (induct, simp add: indRelSTEQ.encL, simp add: indRelSTEQ.source,
             simp add: indRelSTEQ.target)
        case (trans P Q R)
        assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
        thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          by (rule indRelSTEQ.trans)
      qed
      with symmS symmT show "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
          using indRelSTEQ_symm[of SRel TRel]
          unfolding sym_def
        by blast
    qed
    ultimately show "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
      by (rule indRelSTEQ.trans)
  qed
qed

text \<open>If the relations indRelRST, indRelLST, or indRelST contain a pair of target terms, then
        this pair is also related by the considered target term relation. Similarly a pair of
        source terms is related by the considered source term relation.\<close>

lemma (in encoding) indRelRST_to_SRel:
  fixes SRel  :: "('procS \<times> 'procS) set"
    and TRel  :: "('procT \<times> 'procT) set"
    and SP SQ :: "'procS"
  assumes rel: "SourceTerm SP \<R>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> SourceTerm SQ"
  shows "(SP, SQ) \<in> SRel"
      using rel
    by (simp add: indRelRST.simps)

lemma (in encoding) indRelRST_to_TRel:
  fixes SRel  :: "('procS \<times> 'procS) set"
    and TRel  :: "('procT \<times> 'procT) set"
    and TP TQ :: "'procT"
  assumes rel: "TargetTerm TP \<R>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> TargetTerm TQ"
  shows "(TP, TQ) \<in> TRel"
      using rel
    by (simp add: indRelRST.simps)

lemma (in encoding) indRelLST_to_SRel:
  fixes SRel  :: "('procS \<times> 'procS) set"
    and TRel  :: "('procT \<times> 'procT) set"
    and SP SQ :: "'procS"
  assumes rel: "SourceTerm SP \<R>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> SourceTerm SQ"
  shows "(SP, SQ) \<in> SRel"
      using rel
    by (simp add: indRelLST.simps)

lemma (in encoding) indRelLST_to_TRel:
  fixes SRel  :: "('procS \<times> 'procS) set"
    and TRel  :: "('procT \<times> 'procT) set"
    and TP TQ :: "'procT"
  assumes rel: "TargetTerm TP \<R>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> TargetTerm TQ"
  shows "(TP, TQ) \<in> TRel"
      using rel
    by (simp add: indRelLST.simps)

lemma (in encoding) indRelST_to_SRel:
  fixes SRel  :: "('procS \<times> 'procS) set"
    and TRel  :: "('procT \<times> 'procT) set"
    and SP SQ :: "'procS"
  assumes rel: "SourceTerm SP \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm SQ"
  shows "(SP, SQ) \<in> SRel"
      using rel
    by (simp add: indRelST.simps)

lemma (in encoding) indRelST_to_TRel:
  fixes SRel  :: "('procS \<times> 'procS) set"
    and TRel  :: "('procT \<times> 'procT) set"
    and TP TQ :: "'procT"
  assumes rel: "TargetTerm TP \<R>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm TQ"
  shows "(TP, TQ) \<in> TRel"
      using rel
    by (simp add: indRelST.simps)

text \<open>If the relations indRelRSTPO or indRelLSTPO contain a pair of target terms, then this pair
        is also related by the transitive closure of the considered target term relation. Similarly
        a pair of source terms is related by the transitive closure of the source term relation. A
        pair of a source and a target term results from the combination of pairs in the source
        relation, the target relation, and the encoding function. Note that, because of the
        symmetry, no similar condition holds for indRelSTEQ.\<close>

lemma (in encoding) indRelRSTPO_to_SRel_and_TRel:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and P Q  :: "('procS, 'procT) Proc"
  assumes "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q"
  shows "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> (SP, SQ) \<in> SRel\<^sup>+"
    and "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> (\<exists>S. (SP, S) \<in> SRel\<^sup>* \<and> (\<lbrakk>S\<rbrakk>, TQ) \<in> TRel\<^sup>*)"
    and "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q \<longrightarrow> False"
    and "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
      using assms
proof induct
  case (encR S)
  show "\<forall>SP SQ. SP \<in>S SourceTerm S \<and> SQ \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> (SP, SQ) \<in> SRel\<^sup>+"
   and "\<forall>TP SQ. TP \<in>T SourceTerm S \<and> SQ \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> False"
   and "\<forall>TP TQ. TP \<in>T SourceTerm S \<and> TQ \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
    by simp+
  have "(S, S) \<in> SRel\<^sup>*"
    by simp
  moreover have "(\<lbrakk>S\<rbrakk>, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>*"
    by simp
  ultimately show "\<forall>SP TQ. SP \<in>S SourceTerm S \<and> TQ \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<longrightarrow>
                   (\<exists>S. (SP, S) \<in> SRel\<^sup>* \<and> (\<lbrakk>S\<rbrakk>, TQ) \<in> TRel\<^sup>*)"
    by blast
next
  case (source S1 S2)
  assume "(S1, S2) \<in> SRel"
  thus "\<forall>SP SQ. SP \<in>S SourceTerm S1 \<and> SQ \<in>S SourceTerm S2 \<longrightarrow> (SP, SQ) \<in> SRel\<^sup>+"
    by simp
  show "\<forall>SP TQ. SP \<in>S SourceTerm S1 \<and> TQ \<in>T SourceTerm S2 \<longrightarrow>
        (\<exists>S. (SP, S) \<in> SRel\<^sup>* \<and> (\<lbrakk>S\<rbrakk>, TQ) \<in> TRel\<^sup>*)"
   and "\<forall>TP SQ. TP \<in>T SourceTerm S1 \<and> SQ \<in>S SourceTerm S2 \<longrightarrow> False"
   and "\<forall>TP TQ. TP \<in>T SourceTerm S1 \<and> TQ \<in>T SourceTerm S2 \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
    by simp+
next
  case (target T1 T2)
  show "\<forall>SP SQ. SP \<in>S TargetTerm T1 \<and> SQ \<in>S TargetTerm T2 \<longrightarrow> (SP, SQ) \<in> SRel\<^sup>+"
   and "\<forall>SP TQ. SP \<in>S TargetTerm T1 \<and> TQ \<in>T TargetTerm T2
        \<longrightarrow> (\<exists>S. (SP, S) \<in> SRel\<^sup>* \<and> (\<lbrakk>S\<rbrakk>, TQ) \<in> TRel\<^sup>*)"
   and "\<forall>TP SQ. TP \<in>T TargetTerm T1 \<and> SQ \<in>S TargetTerm T2 \<longrightarrow> False"
    by simp+
  assume "(T1, T2) \<in> TRel"
  thus "\<forall>TP TQ. TP \<in>T TargetTerm T1 \<and> TQ \<in>T TargetTerm T2 \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
    by simp
next
  case (trans P Q R)
  assume A1: "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> (SP, SQ) \<in> SRel\<^sup>+"
     and A2: "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> (\<exists>S. (SP, S) \<in> SRel\<^sup>* \<and> (\<lbrakk>S\<rbrakk>, TQ) \<in> TRel\<^sup>*)"
     and A3: "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q \<longrightarrow> False"
     and A4: "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
     and A5: "\<forall>SQ SR. SQ \<in>S Q \<and> SR \<in>S R \<longrightarrow> (SQ, SR) \<in> SRel\<^sup>+"
     and A6: "\<forall>SQ TR. SQ \<in>S Q \<and> TR \<in>T R \<longrightarrow> (\<exists>S. (SQ, S) \<in> SRel\<^sup>* \<and> (\<lbrakk>S\<rbrakk>, TR) \<in> TRel\<^sup>*)"
     and A7: "\<forall>TQ SR. TQ \<in>T Q \<and> SR \<in>S R \<longrightarrow> False"
     and A8: "\<forall>TQ TR. TQ \<in>T Q \<and> TR \<in>T R \<longrightarrow> (TQ, TR) \<in> TRel\<^sup>+"
  show "\<forall>SP SR. SP \<in>S P \<and> SR \<in>S R \<longrightarrow> (SP, SR) \<in> SRel\<^sup>+"
  proof clarify
    fix SP SR
    assume A9: "SP \<in>S P" and A10: "SR \<in>S R"
    show "(SP, SR) \<in> SRel\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume A11: "SQ \<in>S Q"
      with A1 A9 have "(SP, SQ) \<in> SRel\<^sup>+"
        by simp
      moreover from A5 A10 A11 have "(SQ, SR) \<in> SRel\<^sup>+"
        by simp
      ultimately show "(SP, SR) \<in> SRel\<^sup>+"
        by simp
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A7 A10 show "(SP, SR) \<in> SRel\<^sup>+"
        by blast
    qed
  qed
  show "\<forall>SP TR. SP \<in>S P \<and> TR \<in>T R
        \<longrightarrow> (\<exists>S. (SP, S) \<in> SRel\<^sup>* \<and> (\<lbrakk>S\<rbrakk>, TR) \<in> TRel\<^sup>*)"
  proof clarify
    fix SP TR
    assume A9: "SP \<in>S P" and A10: "TR \<in>T R"
    show "\<exists>S. (SP, S) \<in> SRel\<^sup>* \<and> (\<lbrakk>S\<rbrakk>, TR) \<in> TRel\<^sup>*"
    proof (cases Q)
      case (SourceTerm SQ)
      assume A11: "SQ \<in>S Q"
      with A6 A10 obtain S where A12: "(SQ, S) \<in> SRel\<^sup>*"
                             and A13: "(\<lbrakk>S\<rbrakk>, TR) \<in> TRel\<^sup>*"
        by blast
      from A1 A9 A11 have "(SP, SQ) \<in> SRel\<^sup>*"
        by simp
      from this A12 have "(SP, S) \<in> SRel\<^sup>*"
        by simp
      with A13 show "\<exists>S. (SP, S) \<in> SRel\<^sup>* \<and> (\<lbrakk>S\<rbrakk>, TR) \<in> TRel\<^sup>*"
        by blast
    next
      case (TargetTerm TQ)
      assume A11: "TQ \<in>T Q"
      with A2 A9 obtain S where A12: "(SP, S) \<in> SRel\<^sup>*"
                            and A13: "(\<lbrakk>S\<rbrakk>, TQ) \<in> TRel\<^sup>*"
        by blast
      from A8 A10 A11 have "(TQ, TR) \<in> TRel\<^sup>*"
        by simp
      with A13 have "(\<lbrakk>S\<rbrakk>, TR) \<in> TRel\<^sup>*"
        by simp
      with A12 show "\<exists>S. (SP, S) \<in> SRel\<^sup>* \<and> (\<lbrakk>S\<rbrakk>, TR) \<in> TRel\<^sup>*"
        by blast
    qed
  qed
  show "\<forall>TP SR. TP \<in>T P \<and> SR \<in>S R \<longrightarrow> False"
  proof clarify
    fix TP SR
    assume A9: "TP \<in>T P" and A10: "SR \<in>S R"
    show "False"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A3 A9 show "False"
        by blast
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A7 A10 show "False"
        by blast
    qed
  qed
  show "\<forall>TP TR. TP \<in>T P \<and> TR \<in>T R \<longrightarrow> (TP, TR) \<in> TRel\<^sup>+"
  proof clarify
    fix TP TR
    assume A9: "TP \<in>T P" and A10: "TR \<in>T R"
    show "(TP, TR) \<in> TRel\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A3 A9 show "(TP, TR) \<in> TRel\<^sup>+"
        by blast
    next
      case (TargetTerm TQ)
      assume A11: "TQ \<in>T Q"
      with A4 A9 have "(TP, TQ) \<in> TRel\<^sup>+"
        by simp
      moreover from A8 A10 A11 have "(TQ, TR) \<in> TRel\<^sup>+"
        by simp
      ultimately show "(TP, TR) \<in> TRel\<^sup>+"
        by simp
    qed
  qed
qed

lemma (in encoding) indRelLSTPO_to_SRel_and_TRel:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and P Q  :: "('procS, 'procT) Proc"
  assumes "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>L<SRel,TRel> Q"
  shows "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> (SP, SQ) \<in> SRel\<^sup>+"
    and "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> False"
    and "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q \<longrightarrow> (\<exists>S. (TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>* \<and> (S, SQ) \<in> SRel\<^sup>*)"
    and "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
      using assms
proof induct
  case (encL S)
  show "\<forall>SP SQ. SP \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<and> SQ \<in>S SourceTerm S \<longrightarrow> (SP, SQ) \<in> SRel\<^sup>+"
   and "\<forall>SP TQ. SP \<in>S TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TQ \<in>T SourceTerm S \<longrightarrow> False"
   and "\<forall>TP TQ. TP \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TQ \<in>T SourceTerm S \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
    by simp+
  have "(\<lbrakk>S\<rbrakk>, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>*"
    by simp
  moreover have "(S, S) \<in> SRel\<^sup>*"
    by simp
  ultimately show "\<forall>TP SQ. TP \<in>T TargetTerm (\<lbrakk>S\<rbrakk>) \<and> SQ \<in>S SourceTerm S \<longrightarrow>
                   (\<exists>S. (TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>* \<and> (S, SQ) \<in> SRel\<^sup>*)"
    by blast
next
  case (source S1 S2)
  assume "(S1, S2) \<in> SRel"
  thus "\<forall>SP SQ. SP \<in>S SourceTerm S1 \<and> SQ \<in>S SourceTerm S2 \<longrightarrow> (SP, SQ) \<in> SRel\<^sup>+"
    by simp
  show "\<forall>SP TQ. SP \<in>S SourceTerm S1 \<and> TQ \<in>T SourceTerm S2 \<longrightarrow> False"
   and "\<forall>TP SQ. TP \<in>T SourceTerm S1 \<and> SQ \<in>S SourceTerm S2
        \<longrightarrow> (\<exists>S. (TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>* \<and> (S, SQ) \<in> SRel\<^sup>*)"
   and "\<forall>TP TQ. TP \<in>T SourceTerm S1 \<and> TQ \<in>T SourceTerm S2 \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
    by simp+
next
  case (target T1 T2)
  show "\<forall>SP SQ. SP \<in>S TargetTerm T1 \<and> SQ \<in>S TargetTerm T2 \<longrightarrow> (SP, SQ) \<in> SRel\<^sup>+"
   and "\<forall>SP TQ. SP \<in>S TargetTerm T1 \<and> TQ \<in>T TargetTerm T2 \<longrightarrow> False"
   and "\<forall>TP SQ. TP \<in>T TargetTerm T1 \<and> SQ \<in>S TargetTerm T2
        \<longrightarrow> (\<exists>S. (TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>* \<and> (S, SQ) \<in> SRel\<^sup>*)"
    by simp+
  assume "(T1, T2) \<in> TRel"
  thus "\<forall>TP TQ. TP \<in>T TargetTerm T1 \<and> TQ \<in>T TargetTerm T2 \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
    by simp
next
  case (trans P Q R)
  assume A1: "\<forall>SP SQ. SP \<in>S P \<and> SQ \<in>S Q \<longrightarrow> (SP, SQ) \<in> SRel\<^sup>+"
     and A2: "\<forall>SP TQ. SP \<in>S P \<and> TQ \<in>T Q \<longrightarrow> False"
     and A3: "\<forall>TP SQ. TP \<in>T P \<and> SQ \<in>S Q
              \<longrightarrow> (\<exists>S. (TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>* \<and> (S, SQ) \<in> SRel\<^sup>*)"
     and A4: "\<forall>TP TQ. TP \<in>T P \<and> TQ \<in>T Q \<longrightarrow> (TP, TQ) \<in> TRel\<^sup>+"
     and A5: "\<forall>SQ SR. SQ \<in>S Q \<and> SR \<in>S R \<longrightarrow> (SQ, SR) \<in> SRel\<^sup>+"
     and A6: "\<forall>SQ TR. SQ \<in>S Q \<and> TR \<in>T R \<longrightarrow> False"
     and A7: "\<forall>TQ SR. TQ \<in>T Q \<and> SR \<in>S R \<longrightarrow> (\<exists>S. (TQ, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>* \<and> (S, SR) \<in> SRel\<^sup>*)"
     and A8: "\<forall>TQ TR. TQ \<in>T Q \<and> TR \<in>T R \<longrightarrow> (TQ, TR) \<in> TRel\<^sup>+"
  show "\<forall>SP SR. SP \<in>S P \<and> SR \<in>S R \<longrightarrow> (SP, SR) \<in> SRel\<^sup>+"
  proof clarify
    fix SP SR
    assume A9: "SP \<in>S P" and A10: "SR \<in>S R"
    show "(SP, SR) \<in> SRel\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume A11: "SQ \<in>S Q"
      with A1 A9 have "(SP, SQ) \<in> SRel\<^sup>+"
        by simp
      moreover from A5 A10 A11 have "(SQ, SR) \<in> SRel\<^sup>+"
        by simp
      ultimately show "(SP, SR) \<in> SRel\<^sup>+"
        by simp
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A2 A9 show "(SP, SR) \<in> SRel\<^sup>+"
        by blast
    qed
  qed
  show "\<forall>SP TR. SP \<in>S P \<and> TR \<in>T R \<longrightarrow> False"
  proof clarify
    fix SP TR
    assume A9: "SP \<in>S P" and A10: "TR \<in>T R"
    show "False"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A6 A10 show "False"
        by blast
    next
      case (TargetTerm TQ)
      assume "TQ \<in>T Q"
      with A2 A9 show "False"
        by blast
    qed
  qed
  show "\<forall>TP SR. TP \<in>T P \<and> SR \<in>S R \<longrightarrow> (\<exists>S. (TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>* \<and> (S, SR) \<in> SRel\<^sup>*)"
  proof clarify
    fix TP SR
    assume A9: "TP \<in>T P" and A10: "SR \<in>S R"
    show "\<exists>S. (TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>* \<and> (S, SR) \<in> SRel\<^sup>*"
    proof (cases Q)
      case (SourceTerm SQ)
      assume A11: "SQ \<in>S Q"
      with A3 A9 obtain S where A12: "(TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>*" and A13: "(S, SQ) \<in> SRel\<^sup>*"
        by blast
      from A5 A10 A11 have "(SQ, SR) \<in> SRel\<^sup>*"
        by simp
      with A13 have "(S, SR) \<in> SRel\<^sup>*"
        by simp
      with A12 show "\<exists>S. (TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>* \<and> (S, SR) \<in> SRel\<^sup>*"
        by blast
    next
      case (TargetTerm TQ)
      assume A11: "TQ \<in>T Q"
      with A7 A10 obtain S where A12: "(TQ, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>*" and A13: "(S, SR) \<in> SRel\<^sup>*"
        by blast
      from A4 A9 A11 have "(TP, TQ) \<in> TRel\<^sup>*"
        by simp
      from this A12 have "(TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>*"
        by simp
      with A13 show "\<exists>S. (TP, \<lbrakk>S\<rbrakk>) \<in> TRel\<^sup>* \<and> (S, SR) \<in> SRel\<^sup>*"
        by blast
    qed
  qed
  show "\<forall>TP TR. TP \<in>T P \<and> TR \<in>T R \<longrightarrow> (TP, TR) \<in> TRel\<^sup>+"
  proof clarify
    fix TP TR
    assume A9: "TP \<in>T P" and A10: "TR \<in>T R"
    show "(TP, TR) \<in> TRel\<^sup>+"
    proof (cases Q)
      case (SourceTerm SQ)
      assume "SQ \<in>S Q"
      with A6 A10 show "(TP, TR) \<in> TRel\<^sup>+"
        by blast
    next
      case (TargetTerm TQ)
      assume A11: "TQ \<in>T Q"
      with A4 A9 have "(TP, TQ) \<in> TRel\<^sup>+"
        by simp
      moreover from A8 A10 A11 have "(TQ, TR) \<in> TRel\<^sup>+"
        by simp
      ultimately show "(TP, TR) \<in> TRel\<^sup>+"
        by simp
    qed
  qed
qed

text \<open>If indRelRSTPO, indRelLSTPO, or indRelSTPO preserves barbs then so do the corresponding
        source term and target term relations.\<close>

lemma (in encoding_wrt_barbs) rel_with_source_impl_SRel_preserves_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes preservation: "rel_preserves_barbs Rel (STCalWB SWB TWB)"
      and sourceInRel:  "\<forall>S1 S2. (S1, S2) \<in> SRel \<longrightarrow> (SourceTerm S1, SourceTerm S2) \<in> Rel"
  shows "rel_preserves_barbs SRel SWB"
proof clarify
  fix SP SQ a
  assume "(SP, SQ) \<in> SRel"
  with sourceInRel have "(SourceTerm SP, SourceTerm SQ) \<in> Rel"
    by blast
  moreover assume "SP\<down><SWB>a"
  hence "SourceTerm SP\<down>.a"
    by simp
  ultimately have "SourceTerm SQ\<down>.a"
      using preservation preservation_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
  thus "SQ\<down><SWB>a"
    by simp
qed

lemma (in encoding_wrt_barbs) indRelRSTPO_impl_SRel_and_TRel_preserve_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_preserves_barbs (indRelRSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_preserves_barbs SRel SWB"
    and "rel_preserves_barbs TRel TWB"
proof -
  show "rel_preserves_barbs SRel SWB"
      using preservation rel_with_source_impl_SRel_preserves_barbs[where
                          Rel="indRelRSTPO SRel TRel" and SRel="SRel"]
    by (simp add: indRelRSTPO.source)
next
  show "rel_preserves_barbs TRel TWB"
      using preservation rel_with_target_impl_TRel_preserves_barbs[where
                          Rel="indRelRSTPO SRel TRel" and TRel="TRel"]
    by (simp add: indRelRSTPO.target)
qed

lemma (in encoding_wrt_barbs) indRelLSTPO_impl_SRel_and_TRel_preserve_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_preserves_barbs (indRelLSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_preserves_barbs SRel SWB"
    and "rel_preserves_barbs TRel TWB"
proof -
  show "rel_preserves_barbs SRel SWB"
      using preservation rel_with_source_impl_SRel_preserves_barbs[where
                          Rel="indRelLSTPO SRel TRel" and SRel="SRel"]
    by (simp add: indRelLSTPO.source)
next
  show "rel_preserves_barbs TRel TWB"
      using preservation rel_with_target_impl_TRel_preserves_barbs[where
                          Rel="indRelLSTPO SRel TRel" and TRel="TRel"]
    by (simp add: indRelLSTPO.target)
qed

lemma (in encoding_wrt_barbs) indRelSTEQ_impl_SRel_and_TRel_preserve_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_preserves_barbs (indRelSTEQ SRel TRel) (STCalWB SWB TWB)"
  shows "rel_preserves_barbs SRel SWB"
    and "rel_preserves_barbs TRel TWB"
proof -
  show "rel_preserves_barbs SRel SWB"
      using preservation rel_with_source_impl_SRel_preserves_barbs[where
                          Rel="indRelSTEQ SRel TRel" and SRel="SRel"]
    by (simp add: indRelSTEQ.source)
next
  show "rel_preserves_barbs TRel TWB"
      using preservation rel_with_target_impl_TRel_preserves_barbs[where
                          Rel="indRelSTEQ SRel TRel" and TRel="TRel"]
    by (simp add: indRelSTEQ.target)
qed

lemma (in encoding_wrt_barbs) rel_with_source_impl_SRel_weakly_preserves_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes preservation: "rel_weakly_preserves_barbs Rel (STCalWB SWB TWB)"
      and sourceInRel:  "\<forall>S1 S2. (S1, S2) \<in> SRel \<longrightarrow> (SourceTerm S1, SourceTerm S2) \<in> Rel"
  shows "rel_weakly_preserves_barbs SRel SWB"
proof clarify
  fix SP SQ a SP'
  assume "(SP, SQ) \<in> SRel"
  with sourceInRel have "(SourceTerm SP, SourceTerm SQ) \<in> Rel"
    by blast
  moreover assume "SP \<longmapsto>(Calculus SWB)* SP'" and "SP'\<down><SWB>a"
  hence "SourceTerm SP\<Down>.a"
    by blast
  ultimately have "SourceTerm SQ\<Down>.a"
      using preservation weak_preservation_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
  thus "SQ\<Down><SWB>a"
    by simp
qed

lemma (in encoding_wrt_barbs) indRelRSTPO_impl_SRel_and_TRel_weakly_preserve_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_weakly_preserves_barbs (indRelRSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_preserves_barbs SRel SWB"
    and "rel_weakly_preserves_barbs TRel TWB"
proof -
  show "rel_weakly_preserves_barbs SRel SWB"
      using preservation rel_with_source_impl_SRel_weakly_preserves_barbs[where
                          Rel="indRelRSTPO SRel TRel" and SRel="SRel"]
    by (simp add: indRelRSTPO.source)
next
  show "rel_weakly_preserves_barbs TRel TWB"
      using preservation rel_with_target_impl_TRel_weakly_preserves_barbs[where
                          Rel="indRelRSTPO SRel TRel" and TRel="TRel"]
    by (simp add: indRelRSTPO.target)
qed

lemma (in encoding_wrt_barbs) indRelLSTPO_impl_SRel_and_TRel_weakly_preserve_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_weakly_preserves_barbs (indRelLSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_preserves_barbs SRel SWB"
    and "rel_weakly_preserves_barbs TRel TWB"
proof -
  show "rel_weakly_preserves_barbs SRel SWB"
      using preservation rel_with_source_impl_SRel_weakly_preserves_barbs[where
                          Rel="indRelLSTPO SRel TRel" and SRel="SRel"]
    by (simp add: indRelLSTPO.source)
next
  show "rel_weakly_preserves_barbs TRel TWB"
      using preservation rel_with_target_impl_TRel_weakly_preserves_barbs[where
                          Rel="indRelLSTPO SRel TRel" and TRel="TRel"]
    by (simp add: indRelLSTPO.target)
qed

lemma (in encoding_wrt_barbs) indRelSTEQ_impl_SRel_and_TRel_weakly_preserve_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes preservation: "rel_weakly_preserves_barbs (indRelSTEQ SRel TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_preserves_barbs SRel SWB"
    and "rel_weakly_preserves_barbs TRel TWB"
proof -
  show "rel_weakly_preserves_barbs SRel SWB"
      using preservation rel_with_source_impl_SRel_weakly_preserves_barbs[where
                          Rel="indRelSTEQ SRel TRel" and SRel="SRel"]
    by (simp add: indRelSTEQ.source)
next
  show "rel_weakly_preserves_barbs TRel TWB"
      using preservation rel_with_target_impl_TRel_weakly_preserves_barbs[where
                          Rel="indRelSTEQ SRel TRel" and TRel="TRel"]
    by (simp add: indRelSTEQ.target)
qed

text \<open>If indRelRSTPO, indRelLSTPO, or indRelSTPO reflects barbs then so do the corresponding
        source term and target term relations.\<close>

lemma (in encoding_wrt_barbs) rel_with_source_impl_SRel_reflects_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes reflection: "rel_reflects_barbs Rel (STCalWB SWB TWB)"
      and sourceInRel:  "\<forall>S1 S2. (S1, S2) \<in> SRel \<longrightarrow> (SourceTerm S1, SourceTerm S2) \<in> Rel"
  shows "rel_reflects_barbs SRel SWB"
proof clarify
  fix SP SQ a
  assume "(SP, SQ) \<in> SRel"
  with sourceInRel have "(SourceTerm SP, SourceTerm SQ) \<in> Rel"
    by blast
  moreover assume "SQ\<down><SWB>a"
  hence "SourceTerm SQ\<down>.a"
    by simp
  ultimately have "SourceTerm SP\<down>.a"
      using reflection reflection_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
  thus "SP\<down><SWB>a"
    by simp
qed

lemma (in encoding_wrt_barbs) indRelRSTPO_impl_SRel_and_TRel_reflect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_reflects_barbs (indRelRSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_reflects_barbs SRel SWB"
    and "rel_reflects_barbs TRel TWB"
proof -
  show "rel_reflects_barbs SRel SWB"
      using reflection rel_with_source_impl_SRel_reflects_barbs[where
                        Rel="indRelRSTPO SRel TRel" and SRel="SRel"]
    by (simp add: indRelRSTPO.source)
next
  show "rel_reflects_barbs TRel TWB"
      using reflection rel_with_target_impl_TRel_reflects_barbs[where
                        Rel="indRelRSTPO SRel TRel" and TRel="TRel"]
    by (simp add: indRelRSTPO.target)
qed

lemma (in encoding_wrt_barbs) indRelLSTPO_impl_SRel_and_TRel_reflect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_reflects_barbs (indRelLSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_reflects_barbs SRel SWB"
    and "rel_reflects_barbs TRel TWB"
proof -
  show "rel_reflects_barbs SRel SWB"
      using reflection rel_with_source_impl_SRel_reflects_barbs[where
                        Rel="indRelLSTPO SRel TRel" and SRel="SRel"]
    by (simp add: indRelLSTPO.source)
next
  show "rel_reflects_barbs TRel TWB"
      using reflection rel_with_target_impl_TRel_reflects_barbs[where
                        Rel="indRelLSTPO SRel TRel" and TRel="TRel"]
    by (simp add: indRelLSTPO.target)
qed

lemma (in encoding_wrt_barbs) indRelSTEQ_impl_SRel_and_TRel_reflect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_reflects_barbs (indRelSTEQ SRel TRel) (STCalWB SWB TWB)"
  shows "rel_reflects_barbs SRel SWB"
    and "rel_reflects_barbs TRel TWB"
proof -
  show "rel_reflects_barbs SRel SWB"
      using reflection rel_with_source_impl_SRel_reflects_barbs[where
                        Rel="indRelSTEQ SRel TRel" and SRel="SRel"]
    by (simp add: indRelSTEQ.source)
next
  show "rel_reflects_barbs TRel TWB"
      using reflection rel_with_target_impl_TRel_reflects_barbs[where
                        Rel="indRelSTEQ SRel TRel" and TRel="TRel"]
    by (simp add: indRelSTEQ.target)
qed

lemma (in encoding_wrt_barbs) rel_with_source_impl_SRel_weakly_reflects_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and Rel  :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set"
  assumes reflection: "rel_weakly_reflects_barbs Rel (STCalWB SWB TWB)"
      and sourceInRel:  "\<forall>S1 S2. (S1, S2) \<in> SRel \<longrightarrow> (SourceTerm S1, SourceTerm S2) \<in> Rel"
  shows "rel_weakly_reflects_barbs SRel SWB"
proof clarify
  fix SP SQ a SQ'
  assume "(SP, SQ) \<in> SRel"
  with sourceInRel have "(SourceTerm SP, SourceTerm SQ) \<in> Rel"
    by blast
  moreover assume "SQ \<longmapsto>(Calculus SWB)* SQ'" and "SQ'\<down><SWB>a"
  hence "SourceTerm SQ\<Down>.a"
    by blast
  ultimately have "SourceTerm SP\<Down>.a"
      using reflection weak_reflection_of_barbs_in_barbed_encoding[where Rel="Rel"]
    by blast
  thus "SP\<Down><SWB>a"
    by simp
qed

lemma (in encoding_wrt_barbs) indRelRSTPO_impl_SRel_and_TRel_weakly_reflect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_weakly_reflects_barbs (indRelRSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_reflects_barbs SRel SWB"
    and "rel_weakly_reflects_barbs TRel TWB"
proof -
  show "rel_weakly_reflects_barbs SRel SWB"
      using reflection rel_with_source_impl_SRel_weakly_reflects_barbs[where
                        Rel="indRelRSTPO SRel TRel" and SRel="SRel"]
    by (simp add: indRelRSTPO.source)
next
  show "rel_weakly_reflects_barbs TRel TWB"
      using reflection rel_with_target_impl_TRel_weakly_reflects_barbs[where
                          Rel="indRelRSTPO SRel TRel" and TRel="TRel"]
    by (simp add: indRelRSTPO.target)
qed

lemma (in encoding_wrt_barbs) indRelLSTPO_impl_SRel_and_TRel_weakly_reflect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_weakly_reflects_barbs (indRelLSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_reflects_barbs SRel SWB"
    and "rel_weakly_reflects_barbs TRel TWB"
proof -
  show "rel_weakly_reflects_barbs SRel SWB"
      using reflection rel_with_source_impl_SRel_weakly_reflects_barbs[where
                        Rel="indRelLSTPO SRel TRel" and SRel="SRel"]
    by (simp add: indRelLSTPO.source)
next
  show "rel_weakly_reflects_barbs TRel TWB"
      using reflection rel_with_target_impl_TRel_weakly_reflects_barbs[where
                        Rel="indRelLSTPO SRel TRel" and TRel="TRel"]
    by (simp add: indRelLSTPO.target)
qed

lemma (in encoding_wrt_barbs) indRelSTEQ_impl_SRel_and_TRel_weakly_reflect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes reflection: "rel_weakly_reflects_barbs (indRelSTEQ SRel TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_reflects_barbs SRel SWB"
    and "rel_weakly_reflects_barbs TRel TWB"
proof -
  show "rel_weakly_reflects_barbs SRel SWB"
      using reflection rel_with_source_impl_SRel_weakly_reflects_barbs[where
                        Rel="indRelSTEQ SRel TRel" and SRel="SRel"]
    by (simp add: indRelSTEQ.source)
next
  show "rel_weakly_reflects_barbs TRel TWB"
      using reflection rel_with_target_impl_TRel_weakly_reflects_barbs[where
                        Rel="indRelSTEQ SRel TRel" and TRel="TRel"]
    by (simp add: indRelSTEQ.target)
qed

text \<open>If indRelRSTPO, indRelLSTPO, or indRelSTPO respects barbs then so do the corresponding
        source term and target term relations.\<close>

lemma (in encoding_wrt_barbs) indRelRSTPO_impl_SRel_and_TRel_respect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_respects_barbs (indRelRSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_respects_barbs SRel SWB"
    and "rel_respects_barbs TRel TWB"
proof -
  show "rel_respects_barbs SRel SWB"
      using respection
            indRelRSTPO_impl_SRel_and_TRel_preserve_barbs(1)[where SRel="SRel" and TRel="TRel"]
            indRelRSTPO_impl_SRel_and_TRel_reflect_barbs(1)[where SRel="SRel" and TRel="TRel"]
    by blast
next
  show "rel_respects_barbs TRel TWB"
      using respection
            indRelRSTPO_impl_SRel_and_TRel_preserve_barbs(2)[where SRel="SRel" and TRel="TRel"]
            indRelRSTPO_impl_SRel_and_TRel_reflect_barbs(2)[where SRel="SRel" and TRel="TRel"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelLSTPO_impl_SRel_and_TRel_respect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_respects_barbs (indRelLSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_respects_barbs SRel SWB"
    and "rel_respects_barbs TRel TWB"
proof -
  show "rel_respects_barbs SRel SWB"
      using respection
            indRelLSTPO_impl_SRel_and_TRel_preserve_barbs(1)[where SRel="SRel" and TRel="TRel"]
            indRelLSTPO_impl_SRel_and_TRel_reflect_barbs(1)[where SRel="SRel" and TRel="TRel"]
    by blast
next
  show "rel_respects_barbs TRel TWB"
      using respection
            indRelLSTPO_impl_SRel_and_TRel_preserve_barbs(2)[where SRel="SRel" and TRel="TRel"]
            indRelLSTPO_impl_SRel_and_TRel_reflect_barbs(2)[where SRel="SRel" and TRel="TRel"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelSTEQ_impl_SRel_and_TRel_respect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_respects_barbs (indRelSTEQ SRel TRel) (STCalWB SWB TWB)"
  shows "rel_respects_barbs SRel SWB"
    and "rel_respects_barbs TRel TWB"
proof -
  show "rel_respects_barbs SRel SWB"
      using respection
            indRelSTEQ_impl_SRel_and_TRel_preserve_barbs(1)[where SRel="SRel" and TRel="TRel"]
            indRelSTEQ_impl_SRel_and_TRel_reflect_barbs(1)[where SRel="SRel" and TRel="TRel"]
    by blast
next
  show "rel_respects_barbs TRel TWB"
      using respection
            indRelSTEQ_impl_SRel_and_TRel_preserve_barbs(2)[where SRel="SRel" and TRel="TRel"]
            indRelSTEQ_impl_SRel_and_TRel_reflect_barbs(2)[where SRel="SRel" and TRel="TRel"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelRSTPO_impl_SRel_and_TRel_weakly_respect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_weakly_respects_barbs (indRelRSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_respects_barbs SRel SWB"
    and "rel_weakly_respects_barbs TRel TWB"
proof -
  show "rel_weakly_respects_barbs SRel SWB"
      using respection indRelRSTPO_impl_SRel_and_TRel_weakly_preserve_barbs(1)[where SRel="SRel"
                        and TRel="TRel"]
            indRelRSTPO_impl_SRel_and_TRel_weakly_reflect_barbs(1)[where SRel="SRel"
              and TRel="TRel"]
    by blast
next
  show "rel_weakly_respects_barbs TRel TWB"
      using respection indRelRSTPO_impl_SRel_and_TRel_weakly_preserve_barbs(2)[where SRel="SRel"
                        and TRel="TRel"]
            indRelRSTPO_impl_SRel_and_TRel_weakly_reflect_barbs(2)[where SRel="SRel"
              and TRel="TRel"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelLSTPO_impl_SRel_and_TRel_weakly_respect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_weakly_respects_barbs (indRelLSTPO SRel TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_respects_barbs SRel SWB"
    and "rel_weakly_respects_barbs TRel TWB"
proof -
  show "rel_weakly_respects_barbs SRel SWB"
      using respection indRelLSTPO_impl_SRel_and_TRel_weakly_preserve_barbs(1)[where SRel="SRel"
                        and TRel="TRel"]
            indRelLSTPO_impl_SRel_and_TRel_weakly_reflect_barbs(1)[where SRel="SRel"
              and TRel="TRel"]
    by blast
next
  show "rel_weakly_respects_barbs TRel TWB"
      using respection indRelLSTPO_impl_SRel_and_TRel_weakly_preserve_barbs(2)[where SRel="SRel"
                        and TRel="TRel"]
            indRelLSTPO_impl_SRel_and_TRel_weakly_reflect_barbs(2)[where SRel="SRel"
              and TRel="TRel"]
    by blast
qed

lemma (in encoding_wrt_barbs) indRelSTEQ_impl_SRel_and_TRel_weakly_respect_barbs:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes respection: "rel_weakly_respects_barbs (indRelSTEQ SRel TRel) (STCalWB SWB TWB)"
  shows "rel_weakly_respects_barbs SRel SWB"
    and "rel_weakly_respects_barbs TRel TWB"
proof -
  show "rel_weakly_respects_barbs SRel SWB"
      using respection indRelSTEQ_impl_SRel_and_TRel_weakly_preserve_barbs(1)[where SRel="SRel"
                        and TRel="TRel"]
            indRelSTEQ_impl_SRel_and_TRel_weakly_reflect_barbs(1)[where SRel="SRel"
              and TRel="TRel"]
    by blast
next
  show "rel_weakly_respects_barbs TRel TWB"
      using respection indRelSTEQ_impl_SRel_and_TRel_weakly_preserve_barbs(2)[where SRel="SRel"
                        and TRel="TRel"]
            indRelSTEQ_impl_SRel_and_TRel_weakly_reflect_barbs(2)[where SRel="SRel"
              and TRel="TRel"]
    by blast
qed

text \<open>If TRel is reflexive then ind relRTPO is a subrelation of indRelTEQ. If SRel is reflexive
        then indRelRTPO is a subrelation of indRelRTPO. Moreover, indRelRSTPO is a subrelation of
        indRelSTEQ.\<close>

lemma (in encoding) indRelRTPO_to_indRelTEQ:
  fixes TRel :: "('procT \<times> 'procT) set"
    and P Q  :: "('procS, 'procT) Proc"
  assumes rel:   "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
      and reflT: "refl TRel"
  shows "P \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> Q"
    using rel
proof induct
  case (encR S)
  show "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (rule indRelTEQ.encR)
next
  case (source S)
  from reflT show "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S"
      using indRelTEQ_refl[of TRel]
      unfolding refl_on_def
    by simp
next
  case (target T1 T2)
  assume "(T1, T2) \<in> TRel"
  thus "TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2"
    by (rule indRelTEQ.target)
next
  case (trans TP TQ TR)
  assume "TP \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TQ" and "TQ \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TR"
  thus "TP \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TR"
    by (rule indRelTEQ.trans)
qed

lemma (in encoding) indRelRTPO_to_indRelRSTPO:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and P Q  :: "('procS, 'procT) Proc"
  assumes rel:   "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q"
      and reflS: "refl SRel"
  shows "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q"
    using rel
proof induct
  case (encR S)
  show "SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (rule indRelRSTPO.encR)
next
  case (source S)
  from reflS show "SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> SourceTerm S"
      unfolding refl_on_def
    by (simp add: indRelRSTPO.source)
next
  case (target T1 T2)
  assume "(T1, T2) \<in> TRel"
  thus "TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> TargetTerm T2"
    by (rule indRelRSTPO.target)
next
  case (trans P Q R)
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q" and "Q \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R"
  thus "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R"
    by (rule indRelRSTPO.trans)
qed

lemma (in encoding) indRelRSTPO_to_indRelSTEQ:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
    and P Q  :: "('procS, 'procT) Proc"
  assumes rel: "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q"
  shows "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q"
    using rel
proof induct
  case (encR S)
  show "SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
    by (rule indRelSTEQ.encR)
next
  case (source S1 S2)
  assume "(S1, S2) \<in> SRel"
  thus "SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> SourceTerm S2"
    by (rule indRelSTEQ.source)
next
  case (target T1 T2)
  assume "(T1, T2) \<in> TRel"
  thus "TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> TargetTerm T2"
    by (rule indRelSTEQ.target)
next
  case (trans P Q R)
  assume "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> Q" and "Q \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
  thus "P \<sim>\<lbrakk>\<cdot>\<rbrakk><SRel,TRel> R"
    by (rule indRelSTEQ.trans)
qed

text \<open>If indRelRTPO is a bisimulation and SRel is a reflexive bisimulation then also indRelRSTPO
        is a bisimulation.\<close>

lemma (in encoding) indRelRTPO_weak_reduction_bisimulation_impl_indRelRSTPO_bisimulation:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes bisimT: "weak_reduction_bisimulation (indRelRTPO TRel) (STCal Source Target)"
      and bisimS: "weak_reduction_bisimulation SRel Source"
      and reflS:  "refl SRel"
  shows "weak_reduction_bisimulation (indRelRSTPO SRel TRel) (STCal Source Target)"
proof auto
  fix P Q P'
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q" and "P \<longmapsto>(STCal Source Target)* P'"
  thus "\<exists>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
  proof (induct arbitrary: P')
    case (encR S)
    have "SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelRTPO.encR)
    moreover assume "SourceTerm S \<longmapsto>(STCal Source Target)* P'"
    ultimately obtain Q' where A1: "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* Q'"
                           and A2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        using bisimT
      by blast
    from reflS A2 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by (simp add: indRelRTPO_to_indRelRSTPO)
    with A1 show "\<exists>Q'. TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by blast
  next
    case (source S1 S2)
    assume "SourceTerm S1 \<longmapsto>(STCal Source Target)* P'"
    from this obtain S1' where B1: "S1' \<in>S P'" and B2: "S1 \<longmapsto>Source* S1'"
      by (auto simp add: STCal_steps(1))
    assume "(S1, S2) \<in> SRel"
    with B2 bisimS obtain S2' where B3: "S2 \<longmapsto>Source* S2'" and B4: "(S1', S2') \<in> SRel"
      by blast
    from B3 have "SourceTerm S2 \<longmapsto>(STCal Source Target)* (SourceTerm S2')"
      by (simp add: STCal_steps(1))
    moreover from B1 B4 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> SourceTerm S2'"
      by (simp add: indRelRSTPO.source)
    ultimately show "\<exists>Q'. SourceTerm S2 \<longmapsto>(STCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by blast
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    hence "TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
      by (rule indRelRTPO.target)
    moreover assume "TargetTerm T1 \<longmapsto>(STCal Source Target)* P'"
    ultimately obtain Q' where C1: "TargetTerm T2 \<longmapsto>(STCal Source Target)* Q'"
                           and C2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        using bisimT
      by blast
    from reflS C2 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by (simp add: indRelRTPO_to_indRelRSTPO)
    with C1 show "\<exists>Q'. TargetTerm T2 \<longmapsto>(STCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by blast
  next
    case (trans P Q R)
    assume "P \<longmapsto>(STCal Source Target)* P'"
       and "\<And>P'. P \<longmapsto>(STCal Source Target)* P'
            \<Longrightarrow> \<exists>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
    from this obtain Q' where D1: "Q \<longmapsto>(STCal Source Target)* Q'" and D2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by blast
    assume "\<And>Q'. Q \<longmapsto>(STCal Source Target)* Q'
            \<Longrightarrow> \<exists>R'. R \<longmapsto>(STCal Source Target)* R' \<and> Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R'"
    with D1 obtain R' where D3: "R \<longmapsto>(STCal Source Target)* R'" and D4: "Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R'"
      by blast
    from D2 D4 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R'"
      by (rule indRelRSTPO.trans)
    with D3 show "\<exists>R'. R \<longmapsto>(STCal Source Target)* R' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R'"
      by blast
  qed
next
  fix P Q Q'
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q" and "Q \<longmapsto>(STCal Source Target)* Q'"
  thus "\<exists>P'. P \<longmapsto>(STCal Source Target)* P' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
  proof (induct arbitrary: Q')
    case (encR S)
    have "SourceTerm S \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm (\<lbrakk>S\<rbrakk>)"
      by (rule indRelRTPO.encR)
    moreover assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)* Q'"
    ultimately obtain P' where E1: "SourceTerm S \<longmapsto>(STCal Source Target)* P'"
                           and E2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        using bisimT
      by blast
    from reflS E2 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by (simp add: indRelRTPO_to_indRelRSTPO)
    with E1 show "\<exists>P'. SourceTerm S \<longmapsto>(STCal Source Target)* P' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by blast
  next
    case (source S1 S2)
    assume "SourceTerm S2 \<longmapsto>(STCal Source Target)* Q'"
    from this obtain S2' where F1: "S2' \<in>S Q'" and F2: "S2 \<longmapsto>Source* S2'"
      by (auto simp add: STCal_steps(1))
    assume "(S1, S2) \<in> SRel"
    with F2 bisimS obtain S1' where F3: "S1 \<longmapsto>Source* S1'" and F4: "(S1', S2') \<in> SRel"
      by blast
    from F3 have "SourceTerm S1 \<longmapsto>(STCal Source Target)* (SourceTerm S1')"
      by (simp add: STCal_steps(1))
    moreover from F1 F4 have "SourceTerm S1' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by (simp add: indRelRSTPO.source)
    ultimately show "\<exists>P'. SourceTerm S1 \<longmapsto>(STCal Source Target)* P' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by blast
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    hence "TargetTerm T1 \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> TargetTerm T2"
      by (rule indRelRTPO.target)
    moreover assume "TargetTerm T2 \<longmapsto>(STCal Source Target)* Q'"
    ultimately obtain P' where G1: "TargetTerm T1 \<longmapsto>(STCal Source Target)* P'"
                           and G2: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q'"
        using bisimT
      by blast
    from reflS G2 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by (simp add: indRelRTPO_to_indRelRSTPO)
    with G1 show "\<exists>P'. TargetTerm T1 \<longmapsto>(STCal Source Target)* P' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by blast
  next
    case (trans P Q R R')
    assume "R \<longmapsto>(STCal Source Target)* R'"
       and "\<And>R'. R \<longmapsto>(STCal Source Target)* R'
            \<Longrightarrow> \<exists>Q'. Q \<longmapsto>(STCal Source Target)* Q' \<and> Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R'"
    from this obtain Q' where H1: "Q \<longmapsto>(STCal Source Target)* Q'" and H2: "Q' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R'"
      by blast
    assume "\<And>Q'. Q \<longmapsto>(STCal Source Target)* Q'
            \<Longrightarrow> \<exists>P'. P \<longmapsto>(STCal Source Target)* P' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
    with H1 obtain P' where H3: "P \<longmapsto>(STCal Source Target)* P'" and H4: "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> Q'"
      by blast
    from H4 H2 have "P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R'"
      by (rule indRelRSTPO.trans)
    with H3 show "\<exists>P'. P \<longmapsto>(STCal Source Target)* P' \<and> P' \<lesssim>\<lbrakk>\<cdot>\<rbrakk>R<SRel,TRel> R'"
      by blast
  qed
qed

end
