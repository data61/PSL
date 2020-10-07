theory DivergenceReflection
  imports SourceTargetRelation
begin

section \<open>Divergence Reflection\<close>

text \<open>Divergence reflection forbids for encodings that introduce loops of internal actions. Thus
        they determine the practicability of encodings in particular with respect to
        implementations. An encoding reflects divergence if each loop in a target term result from
        the translation of a divergent source term.\<close>

abbreviation (in encoding) enc_preserves_divergence :: "bool" where
  "enc_preserves_divergence \<equiv> enc_preserves_pred (\<lambda>P. P \<longmapsto>ST\<omega>)"

lemma (in encoding) divergence_preservation_cond:
  shows "enc_preserves_divergence = (\<forall>S. S \<longmapsto>(Source)\<omega> \<longrightarrow> \<lbrakk>S\<rbrakk> \<longmapsto>(Target)\<omega>)"
    by simp

abbreviation (in encoding) enc_reflects_divergence :: "bool" where
  "enc_reflects_divergence \<equiv> enc_reflects_pred (\<lambda>P. P \<longmapsto>ST\<omega>)"

lemma (in encoding) divergence_reflection_cond:
  shows "enc_reflects_divergence = (\<forall>S. \<lbrakk>S\<rbrakk> \<longmapsto>(Target)\<omega> \<longrightarrow> S \<longmapsto>(Source)\<omega>)"
    by simp

abbreviation rel_preserves_divergence
    :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> bool"
  where
  "rel_preserves_divergence Rel Cal \<equiv> rel_preserves_pred Rel (\<lambda>P. P \<longmapsto>(Cal)\<omega>)"

abbreviation rel_reflects_divergence
    :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> bool"
  where
  "rel_reflects_divergence Rel Cal \<equiv> rel_reflects_pred Rel (\<lambda>P. P \<longmapsto>(Cal)\<omega>)"

text \<open>Apart from divergence reflection we consider divergence respection. An encoding respects
        divergence if each divergent source term is translated into a divergent target term and
        each divergent target term result from the translation of a divergent source term.\<close>

abbreviation (in encoding) enc_respects_divergence :: "bool" where
  "enc_respects_divergence \<equiv> enc_respects_pred (\<lambda>P. P \<longmapsto>ST\<omega>)"

lemma (in encoding) divergence_respection_cond:
  shows "enc_respects_divergence = (\<forall>S. \<lbrakk>S\<rbrakk> \<longmapsto>(Target)\<omega> \<longleftrightarrow> S \<longmapsto>(Source)\<omega>)"
    by auto

abbreviation rel_respects_divergence
    :: "('proc \<times> 'proc) set \<Rightarrow> 'proc processCalculus \<Rightarrow> bool"
  where
  "rel_respects_divergence Rel Cal \<equiv> rel_respects_pred Rel (\<lambda>P. P \<longmapsto>(Cal)\<omega>)"

text \<open>An encoding preserves divergence iff
        (1) there exists a relation that relates source terms and their literal translations and
            preserves divergence, or
        (2) there exists a relation that relates literal translations and their source terms and
            reflects divergence.\<close>

lemma (in encoding) divergence_preservation_iff_source_target_rel_preserves_divergence:
  shows "enc_preserves_divergence
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_preserves_divergence Rel (STCal Source Target))"
      using enc_preserves_pred_iff_source_target_rel_preserves_pred(1)[where Pred="\<lambda>P. P \<longmapsto>ST\<omega>"]
            divergentST_STCal_divergent
    by simp

lemma (in encoding) divergence_preservation_iff_source_target_rel_reflects_divergence:
  shows "enc_preserves_divergence
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
            \<and> rel_reflects_divergence Rel (STCal Source Target))"
      using enc_preserves_pred_iff_source_target_rel_reflects_pred(1)[where Pred="\<lambda>P. P \<longmapsto>ST\<omega>"]
            divergentST_STCal_divergent
    by simp

text \<open>An encoding reflects divergence iff
        (1) there exists a relation that relates source terms and their literal translations and
            reflects divergence, or
        (2) there exists a relation that relates literal translations and their source terms and
            preserves divergence.\<close>

lemma (in encoding) divergence_reflection_iff_source_target_rel_reflects_divergence:
  shows "enc_reflects_divergence
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_reflects_divergence Rel (STCal Source Target))"
      using enc_reflects_pred_iff_source_target_rel_reflects_pred[where Pred="\<lambda>P. P \<longmapsto>ST\<omega>"]
            divergentST_STCal_divergent
    by simp

lemma (in encoding) divergence_reflection_iff_source_target_rel_preserves_divergence:
  shows "enc_reflects_divergence
         = (\<exists>Rel. (\<forall>S. (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
            \<and> rel_preserves_divergence Rel (STCal Source Target))"
      using enc_reflects_pred_iff_source_target_rel_preserves_pred[where Pred="\<lambda>P. P \<longmapsto>ST\<omega>"]
            divergentST_STCal_divergent
    by simp

text \<open>An encoding respects divergence iff there exists a relation that relates source terms and
        their literal translations in both directions and respects divergence.\<close>

lemma (in encoding) divergence_respection_iff_source_target_rel_respects_divergence:
  shows "enc_respects_divergence = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
         \<and> rel_respects_divergence Rel (STCal Source Target))"
  and   "enc_respects_divergence = (\<exists>Rel.
         (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
         \<and> rel_respects_divergence Rel (STCal Source Target))"
proof -
  show "enc_respects_divergence = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> rel_respects_divergence Rel (STCal Source Target))"
      using enc_respects_pred_iff_source_target_rel_respects_pred_encR[where Pred="\<lambda>P. P \<longmapsto>ST\<omega>"]
            divergentST_STCal_divergent
    by simp
next
  show "enc_respects_divergence = (\<exists>Rel.
        (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
        \<and> rel_respects_divergence Rel (STCal Source Target))"
      using enc_respects_pred_iff_source_target_rel_respects_pred_encRL[where Pred="\<lambda>P. P \<longmapsto>ST\<omega>"]
            divergentST_STCal_divergent
    by simp
qed

end
