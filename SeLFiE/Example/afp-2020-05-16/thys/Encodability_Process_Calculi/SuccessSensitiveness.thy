theory SuccessSensitiveness
  imports SourceTargetRelation
begin

section \<open>Success Sensitiveness and Barbs\<close>

text \<open>To compare the abstract behavior of two terms, often some notion of success or successful
        termination is used. Daniele Gorla assumes a constant process (similar to the empty
        process) that represents successful termination in order to compare the behavior of source
        terms with their literal translations. Then an encoding is success sensitive if, for all
        source terms S, S reaches success iff the translation of S reaches success. Successful
        termination can be considered as some special kind of barb. Accordingly we generalize
        successful termination to the respection of an arbitrary subset of barbs. An encoding
        respects a set of barbs if, for every source term S and all considered barbs a, S reaches a
        iff the translation of S reaches a.\<close>

abbreviation (in encoding_wrt_barbs) enc_weakly_preserves_barb_set :: "'barbs set \<Rightarrow> bool" where
  "enc_weakly_preserves_barb_set Barbs \<equiv> enc_preserves_binary_pred (\<lambda>P a. a \<in> Barbs \<and> P\<Down>.a)"

abbreviation (in encoding_wrt_barbs) enc_weakly_preserves_barbs :: "bool" where
  "enc_weakly_preserves_barbs \<equiv> enc_preserves_binary_pred (\<lambda>P a. P\<Down>.a)"

lemma (in encoding_wrt_barbs) enc_weakly_preserves_barbs_and_barb_set:
  shows "enc_weakly_preserves_barbs = (\<forall>Barbs. enc_weakly_preserves_barb_set Barbs)"
    by blast

abbreviation (in encoding_wrt_barbs) enc_weakly_reflects_barb_set :: "'barbs set \<Rightarrow> bool" where
  "enc_weakly_reflects_barb_set Barbs \<equiv> enc_reflects_binary_pred (\<lambda>P a. a \<in> Barbs \<and> P\<Down>.a)"

abbreviation (in encoding_wrt_barbs) enc_weakly_reflects_barbs :: "bool" where
  "enc_weakly_reflects_barbs \<equiv> enc_reflects_binary_pred (\<lambda>P a. P\<Down>.a)"

lemma (in encoding_wrt_barbs) enc_weakly_reflects_barbs_and_barb_set:
  shows "enc_weakly_reflects_barbs = (\<forall>Barbs. enc_weakly_reflects_barb_set Barbs)"
    by blast

abbreviation (in encoding_wrt_barbs) enc_weakly_respects_barb_set :: "'barbs set \<Rightarrow> bool" where
  "enc_weakly_respects_barb_set Barbs \<equiv>
   enc_weakly_preserves_barb_set Barbs \<and> enc_weakly_reflects_barb_set Barbs"

abbreviation (in encoding_wrt_barbs) enc_weakly_respects_barbs :: "bool" where
  "enc_weakly_respects_barbs \<equiv> enc_weakly_preserves_barbs \<and> enc_weakly_reflects_barbs"

lemma (in encoding_wrt_barbs) enc_weakly_respects_barbs_and_barb_set:
  shows "enc_weakly_respects_barbs = (\<forall>Barbs. enc_weakly_respects_barb_set Barbs)"
proof -
  have "(\<forall>Barbs. enc_weakly_respects_barb_set Barbs)
        = (\<forall>Barbs. (\<forall>S x. x \<in> Barbs \<and> S\<Down><SWB>x \<longrightarrow> \<lbrakk>S\<rbrakk>\<Down><TWB>x)
          \<and> (\<forall>S x. x \<in> Barbs \<and> \<lbrakk>S\<rbrakk>\<Down><TWB>x \<longrightarrow> S\<Down><SWB>x))"
    by simp
  hence "(\<forall>Barbs. enc_weakly_respects_barb_set Barbs)
        = ((\<forall>Barbs. enc_weakly_preserves_barb_set Barbs)
            \<and> (\<forall>Barbs. enc_weakly_reflects_barb_set Barbs))"
    apply simp by fast
  thus ?thesis
    apply simp by blast
qed

text \<open>An encoding strongly respects some set of barbs if, for every source term S and all
        considered barbs a, S has a iff the translation of S has a.\<close>

abbreviation (in encoding_wrt_barbs) enc_preserves_barb_set :: "'barbs set \<Rightarrow> bool" where
  "enc_preserves_barb_set Barbs \<equiv> enc_preserves_binary_pred (\<lambda>P a. a \<in> Barbs \<and> P\<down>.a)"

abbreviation (in encoding_wrt_barbs) enc_preserves_barbs :: "bool" where
  "enc_preserves_barbs \<equiv> enc_preserves_binary_pred (\<lambda>P a. P\<down>.a)"

lemma (in encoding_wrt_barbs) enc_preserves_barbs_and_barb_set:
  shows "enc_preserves_barbs = (\<forall>Barbs. enc_preserves_barb_set Barbs)"
    by blast

abbreviation (in encoding_wrt_barbs) enc_reflects_barb_set :: "'barbs set \<Rightarrow> bool" where
  "enc_reflects_barb_set Barbs \<equiv> enc_reflects_binary_pred (\<lambda>P a. a \<in> Barbs \<and> P\<down>.a)"

abbreviation (in encoding_wrt_barbs) enc_reflects_barbs :: "bool" where
  "enc_reflects_barbs \<equiv> enc_reflects_binary_pred (\<lambda>P a. P\<down>.a)"

lemma (in encoding_wrt_barbs) enc_reflects_barbs_and_barb_set:
  shows "enc_reflects_barbs = (\<forall>Barbs. enc_reflects_barb_set Barbs)"
    by blast

abbreviation (in encoding_wrt_barbs) enc_respects_barb_set :: "'barbs set \<Rightarrow> bool" where
  "enc_respects_barb_set Barbs \<equiv> enc_preserves_barb_set Barbs \<and> enc_reflects_barb_set Barbs"

abbreviation (in encoding_wrt_barbs) enc_respects_barbs :: "bool" where
  "enc_respects_barbs \<equiv> enc_preserves_barbs \<and> enc_reflects_barbs"

lemma (in encoding_wrt_barbs) enc_respects_barbs_and_barb_set:
  shows "enc_respects_barbs = (\<forall>Barbs. enc_respects_barb_set Barbs)"
proof -
  have "(\<forall>Barbs. enc_respects_barb_set Barbs)
        = ((\<forall>Barbs. enc_preserves_barb_set Barbs)
            \<and> (\<forall>Barbs. enc_reflects_barb_set Barbs))"
    apply simp by fast
  thus ?thesis
    apply simp by blast
qed

text \<open>An encoding (weakly) preserves barbs iff
        (1) there exists a relation, like indRelR, that relates source terms and their literal
            translations and preserves (reachability/)existence of barbs, or
        (2) there exists a relation, like indRelL, that relates literal translations and their
            source terms and reflects (reachability/)existence of barbs.\<close>

lemma (in encoding_wrt_barbs) enc_weakly_preserves_barb_set_iff_source_target_rel:
  fixes Barbs :: "'barbs set"
    and TRel  :: "('procT \<times> 'procT) set"
  shows "enc_weakly_preserves_barb_set Barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_weakly_preserves_barb_set Rel (STCalWB SWB TWB) Barbs)"
      using enc_preserves_binary_pred_iff_source_target_rel_preserves_binary_pred[where
             Pred="\<lambda>P a. a \<in> Barbs \<and> P\<Down><STCalWB SWB TWB>a"] STCalWB_reachesBarbST
    by simp

lemma (in encoding_wrt_barbs) enc_weakly_preserves_barbs_iff_source_target_rel:
  shows "enc_weakly_preserves_barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_weakly_preserves_barbs Rel (STCalWB SWB TWB))"
      using enc_preserves_binary_pred_iff_source_target_rel_preserves_binary_pred[where
             Pred="\<lambda>P a. P\<Down><STCalWB SWB TWB>a"] STCalWB_reachesBarbST
    by simp

lemma (in encoding_wrt_barbs) enc_preserves_barb_set_iff_source_target_rel:
  fixes Barbs :: "'barbs set"
  shows "enc_preserves_barb_set Barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_preserves_barb_set Rel (STCalWB SWB TWB) Barbs)"
      using enc_preserves_binary_pred_iff_source_target_rel_preserves_binary_pred[where
             Pred="\<lambda>P a. a \<in> Barbs \<and> P\<down><STCalWB SWB TWB>a"] STCalWB_hasBarbST
    by simp

lemma (in encoding_wrt_barbs) enc_preserves_barbs_iff_source_target_rel:
  shows "enc_preserves_barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_preserves_barbs Rel (STCalWB SWB TWB))"
      using enc_preserves_binary_pred_iff_source_target_rel_preserves_binary_pred[where
             Pred="\<lambda>P a. P\<down><STCalWB SWB TWB>a"] STCalWB_hasBarbST
    by simp

text \<open>An encoding (weakly) reflects barbs iff
        (1) there exists a relation, like indRelR, that relates source terms and their literal
            translations and reflects (reachability/)existence of barbs, or
        (2) there exists a relation, like indRelL, that relates literal translations and their
            source terms and preserves (reachability/)existence of barbs.\<close>

lemma (in encoding_wrt_barbs) enc_weakly_reflects_barb_set_iff_source_target_rel:
  fixes Barbs :: "'barbs set"
  shows "enc_weakly_reflects_barb_set Barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_weakly_reflects_barb_set Rel (STCalWB SWB TWB) Barbs)"
      using enc_reflects_binary_pred_iff_source_target_rel_reflects_binary_pred[where
             Pred="\<lambda>P a. a \<in> Barbs \<and> P\<Down><STCalWB SWB TWB>a"] STCalWB_reachesBarbST
    by simp

lemma (in encoding_wrt_barbs) enc_weakly_reflects_barbs_iff_source_target_rel:
  shows "enc_weakly_reflects_barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_weakly_reflects_barbs Rel (STCalWB SWB TWB))"
      using enc_reflects_binary_pred_iff_source_target_rel_reflects_binary_pred[where
             Pred="\<lambda>P a. P\<Down><STCalWB SWB TWB>a"] STCalWB_reachesBarbST
    by simp

lemma (in encoding_wrt_barbs) enc_reflects_barb_set_iff_source_target_rel:
  fixes Barbs :: "'barbs set"
  shows "enc_reflects_barb_set Barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_reflects_barb_set Rel (STCalWB SWB TWB) Barbs)"
      using enc_reflects_binary_pred_iff_source_target_rel_reflects_binary_pred[where
             Pred="\<lambda>P a. a \<in> Barbs \<and> P\<down><STCalWB SWB TWB>a"] STCalWB_hasBarbST
    by simp

lemma (in encoding_wrt_barbs) enc_reflects_barbs_iff_source_target_rel:
  shows "enc_reflects_barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_reflects_barbs Rel (STCalWB SWB TWB))"
      using enc_reflects_binary_pred_iff_source_target_rel_reflects_binary_pred[where
             Pred="\<lambda>P a. P\<down><STCalWB SWB TWB>a"] STCalWB_hasBarbST
    by simp

text \<open>An encoding (weakly) respects barbs iff
        (1) there exists a relation, like indRelR, that relates source terms and their literal
            translations and respects (reachability/)existence of barbs, or
        (2) there exists a relation, like indRelL, that relates literal translations and their
            source terms and respects (reachability/)existence of barbs, or
        (3) there exists a relation, like indRel, that relates source terms and their literal
            translations in both directions and respects (reachability/)existence of barbs.\<close>

lemma (in encoding_wrt_barbs) enc_weakly_respects_barb_set_iff_source_target_rel:
  fixes Barbs :: "'barbs set"
  shows "enc_weakly_respects_barb_set Barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) Barbs)"
      using enc_respects_binary_pred_iff_source_target_rel_respects_binary_pred_encR[where
             Pred="\<lambda>P a. a \<in> Barbs \<and> P\<Down><STCalWB SWB TWB>a"] STCalWB_reachesBarbST
    by simp

lemma (in encoding_wrt_barbs) enc_weakly_respects_barbs_iff_source_target_rel:
  shows "enc_weakly_respects_barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB))"
      using enc_respects_binary_pred_iff_source_target_rel_respects_binary_pred_encR[where
             Pred="\<lambda>P a. P\<Down><STCalWB SWB TWB>a"] STCalWB_reachesBarbST
    by simp

lemma (in encoding_wrt_barbs) enc_respects_barb_set_iff_source_target_rel:
  fixes Barbs :: "'barbs set"
  shows "enc_respects_barb_set Barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) Barbs)"
      using enc_respects_binary_pred_iff_source_target_rel_respects_binary_pred_encR[where
             Pred="\<lambda>P a. a \<in> Barbs \<and> P\<down><STCalWB SWB TWB>a"] STCalWB_hasBarbST
    by simp

lemma (in encoding_wrt_barbs) enc_respects_barbs_iff_source_target_rel:
  shows "enc_respects_barbs
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_respects_barbs Rel (STCalWB SWB TWB))"
      using enc_respects_binary_pred_iff_source_target_rel_respects_binary_pred_encR[where
             Pred="\<lambda>P a. P\<down><STCalWB SWB TWB>a"] STCalWB_hasBarbST
    by simp

text \<open>Accordingly an encoding is success sensitive iff there exists such a relation between
        source and target terms that weakly respects the barb success.\<close>

lemma (in encoding_wrt_barbs) success_sensitive_cond:
  fixes success :: "'barbs"
  shows "enc_weakly_respects_barb_set {success} = (\<forall>S. S\<Down><SWB>success \<longleftrightarrow> \<lbrakk>S\<rbrakk>\<Down><TWB>success)"
    by auto

lemma (in encoding_wrt_barbs) success_sensitive_iff_source_target_rel_weakly_respects_success:
  fixes success :: "'barbs"
  shows "enc_weakly_respects_barb_set {success}
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success})"
    by (rule enc_weakly_respects_barb_set_iff_source_target_rel[where Barbs="{success}"])+

lemma (in encoding_wrt_barbs) success_sensitive_iff_source_target_rel_respects_success:
  fixes success :: "'barbs"
  shows "enc_respects_barb_set {success}
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success})"
    by (rule enc_respects_barb_set_iff_source_target_rel[where Barbs="{success}"])

end
