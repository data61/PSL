theory CombinedCriteria
  imports DivergenceReflection SuccessSensitiveness FullAbstraction OperationalCorrespondence
begin

section \<open>Combining Criteria\<close>

text \<open>So far we considered the effect of single criteria on encodings. Often the quality of an
        encoding is prescribed by a set of different criteria. In the following we analyse the
        combined effect of criteria. This way we can compare criteria as well as identify side
        effects that result from combinations of criteria. We start with some technical lemmata. To
        combine the effect of different criteria we combine the conditions they induce. If their
        effect can be described by a predicate on the pairs of the relation, as in the case of
        success sensitiveness or divergence reflection, combining the effects is simple.\<close>

lemma (in encoding) criterion_iff_source_target_relation_impl_indRelR:
  fixes Cond :: "('procS \<Rightarrow> 'procT) \<Rightarrow> bool"
    and Pred :: "(('procS, 'procT) Proc \<times> ('procS, 'procT) Proc) set \<Rightarrow> bool"
  assumes "Cond enc = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> Pred Rel)"
  shows "Cond enc = (\<exists>Rel'. Pred (indRelR \<union> Rel'))"
proof (rule iffI)
  assume "Cond enc"
  with assms obtain Rel where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel" and A2: "Pred Rel"
    by blast
  from A1 have "Rel = indRelR \<union> (Rel - indRelR)"
    by (auto simp add: indRelR.simps)
  with A2 have "Pred (indRelR \<union> (Rel - indRelR))"
    by simp
  thus "\<exists>Rel'. Pred (indRelR \<union> Rel')"
    by blast
next
  assume "\<exists>Rel'. Pred (indRelR \<union> Rel')"
  from this obtain Rel' where "Pred (indRelR \<union> Rel')"
    by blast
  moreover have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> (indRelR \<union> Rel')"
    by (simp add: indRelR.encR)
  ultimately show "Cond enc"
      using assms
    by blast
qed

lemma (in encoding) combine_conditions_on_pairs_of_relations:
  fixes RelA RelB   :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) set"
    and CondA CondB :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) \<Rightarrow> bool"
  assumes "\<forall>(P, Q) \<in> RelA. CondA (P, Q)"
      and "\<forall>(P, Q) \<in> RelB. CondB (P, Q)"
  shows "(\<forall>(P, Q) \<in> RelA \<inter> RelB. CondA (P, Q)) \<and> (\<forall>(P, Q) \<in> RelA \<inter> RelB. CondB (P, Q))"
      using assms
    by blast

lemma (in encoding) combine_conditions_on_sets_of_relations:
  fixes Rel RelA :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) set"
    and Cond     :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) set \<Rightarrow> bool"
    and CondA    :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) \<Rightarrow> bool"
  assumes "\<forall>(P, Q) \<in> RelA. CondA (P, Q)"
      and "Cond Rel \<and> Rel \<subseteq> RelA"
  shows "Cond Rel \<and> (\<forall>(P, Q) \<in> Rel. CondA (P, Q))"
      using assms
    by blast

lemma (in encoding) combine_conditions_on_sets_and_pairs_of_relations:
  fixes Rel RelA RelB :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) set"
    and Cond          :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) set \<Rightarrow> bool"
    and CondA CondB   :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) \<Rightarrow> bool"
  assumes "\<forall>(P, Q) \<in> RelA. CondA (P, Q)"
      and "\<forall>(P, Q) \<in> RelB. CondB (P, Q)"
      and "Cond Rel \<and> Rel \<subseteq> RelA \<and> Rel \<subseteq> RelB"
  shows "Cond Rel \<and> (\<forall>(P, Q) \<in> Rel. CondA (P, Q)) \<and> (\<forall>(P, Q) \<in> Rel. CondB (P, Q))"
      using assms
    by blast

text \<open>We mapped several criteria on conditions on relations that relate at least all source terms
        and their literal translations. The following lemmata help us to combine such conditions by
        switching to the witness indRelR.\<close>

lemma (in encoding) combine_conditions_on_relations_indRelR:
  fixes RelA RelB   :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) set"
    and Cond        :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) set \<Rightarrow> bool"
    and CondA CondB :: "(('procS, 'procT) Proc \<times>('procS, 'procT) Proc) \<Rightarrow> bool"
  assumes A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> RelA"
      and A2: "\<forall>(P, Q) \<in> RelA. CondA (P, Q)"
      and A3: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> RelB"
      and A4: "\<forall>(P, Q) \<in> RelB. CondB (P, Q)"
  shows "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> (\<forall>(P, Q) \<in> Rel. CondA (P, Q))
          \<and> (\<forall>(P, Q) \<in> Rel. CondB (P, Q))"
    and "Cond indRelR \<Longrightarrow> (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
         \<and> (\<forall>(P, Q) \<in> Rel. CondA (P, Q)) \<and> (\<forall>(P, Q) \<in> Rel. CondB (P, Q)) \<and> Cond Rel)"
proof -
  have A5: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> indRelR"
    by (simp add: indRelR.encR)
  moreover have A6: "indRelR \<subseteq> RelA"
  proof clarify
    fix P Q
    assume "(P, Q) \<in> indRelR"
    from this A1 show "(P, Q) \<in> RelA"
      by (induct, simp)
  qed
  moreover have A7: "indRelR \<subseteq> RelB"
  proof clarify
    fix P Q
    assume "(P, Q) \<in> indRelR"
    from this A3 show "(P, Q) \<in> RelB"
      by (induct, simp)
  qed
  ultimately show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>(P, Q) \<in> Rel. CondA (P, Q)) \<and> (\<forall>(P, Q) \<in> Rel. CondB (P, Q))"
      using combine_conditions_on_sets_and_pairs_of_relations[where RelA="RelA" and RelB="RelB"
            and CondA="CondA" and CondB="CondB" and Rel="indRelR"
            and Cond="\<lambda>R. \<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> R"] A2 A4
    by blast
  from A2 A4 A5 A6 A7
  show "Cond indRelR \<Longrightarrow> (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> (\<forall>(P, Q) \<in> Rel. CondA (P, Q)) \<and> (\<forall>(P, Q) \<in> Rel. CondB (P, Q)) \<and> Cond Rel)"
      using combine_conditions_on_sets_and_pairs_of_relations[where RelA="RelA" and RelB="RelB"
            and CondA="CondA" and CondB="CondB" and Rel="indRelR"
            and Cond="\<lambda>R. \<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> R \<and> Cond R"]
    by blast
qed

lemma (in encoding) indRelR_cond_respects_predA_and_reflects_predB:
  fixes PredA PredB :: "('procS, 'procT) Proc \<Rightarrow> bool"
  shows "((\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel PredA)
          \<and> (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_pred Rel PredB))
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel PredA
            \<and> rel_reflects_pred Rel PredB)"
proof (rule iffI, erule conjE)
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel PredA"
  from this obtain RelA where A1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> RelA"
                          and A2: "rel_respects_pred RelA PredA"
    by blast
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_pred Rel PredB"
  from this obtain RelB where A3: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> RelB"
                          and A4: "rel_reflects_pred RelB PredB"
    by blast
  from A2 have "\<forall>(P, Q) \<in> RelA. PredA P \<longleftrightarrow> PredA Q"
    by blast
  moreover from A4 have "\<forall>(P, Q) \<in> RelB. PredB Q \<longrightarrow> PredB P"
    by blast
  ultimately have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                   \<and> (\<forall>(P, Q)\<in>Rel. PredA P = PredA Q) \<and> (\<forall>(P, Q)\<in>Rel. PredB Q \<longrightarrow> PredB P)"
      using combine_conditions_on_relations_indRelR(1)[where RelA="RelA" and RelB="RelB" and
            CondA="\<lambda>(P, Q). PredA P \<longleftrightarrow> PredA Q" and CondB="\<lambda>(P, Q). PredB Q \<longrightarrow> PredB P"] A1 A3
    by simp
  thus "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel PredA
        \<and> rel_reflects_pred Rel PredB"
    by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel PredA
          \<and> rel_reflects_pred Rel PredB"
  thus "(\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_respects_pred Rel PredA) \<and>
        (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel) \<and> rel_reflects_pred Rel PredB)"
    by blast
qed

subsection \<open>Divergence Reflection and Success Sensitiveness\<close>

text \<open>We combine results on divergence reflection and success sensitiveness to analyse their
        combined effect on an encoding function. An encoding is success sensitive and reflects
        divergence iff there exists a relation that relates source terms and their literal
        translations that reflects divergence and respects success.\<close>

lemma (in encoding_wrt_barbs) WSS_DR_iff_source_target_rel:
  fixes success :: "'barbs"
  shows "(enc_weakly_respects_barb_set {success} \<and> enc_reflects_divergence)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
            \<and> rel_reflects_divergence Rel (STCal Source Target))"
proof -
  have "\<forall>Rel. rel_reflects_divergence Rel (STCal Source Target)
        = rel_reflects_pred Rel divergentST"
    by (simp add: divergentST_STCal_divergent)
  moreover have "\<forall>Rel. (rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
                 = rel_respects_pred Rel (\<lambda>P. P\<Down>.success))"
    by (simp add: STCalWB_reachesBarbST)
  ultimately show "(enc_weakly_respects_barb_set {success} \<and> enc_reflects_divergence)
    = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
       \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
       \<and> rel_reflects_divergence Rel (STCal Source Target))"
      using success_sensitive_iff_source_target_rel_weakly_respects_success(1)
            divergence_reflection_iff_source_target_rel_reflects_divergence
            indRelR_cond_respects_predA_and_reflects_predB[where
              PredA="\<lambda>P. P\<Down>.success" and PredB="divergentST"]
    by simp
qed

lemma (in encoding_wrt_barbs) SS_DR_iff_source_target_rel:
  fixes success :: "'barbs"
  shows "(enc_respects_barb_set {success} \<and> enc_reflects_divergence)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}
            \<and> rel_reflects_divergence Rel (STCal Source Target))"
proof -
  have "\<forall>Rel. rel_reflects_divergence Rel (STCal Source Target)
        = rel_reflects_pred Rel divergentST"
    by (simp add: divergentST_STCal_divergent)
  moreover have "\<forall>Rel. (rel_respects_barb_set Rel (STCalWB SWB TWB) {success}
                 = rel_respects_pred Rel (\<lambda>P. P\<down>.success))"
    by (simp add: STCalWB_hasBarbST)
  ultimately show "(enc_respects_barb_set {success} \<and> enc_reflects_divergence)
    = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
       \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}
       \<and> rel_reflects_divergence Rel (STCal Source Target))"
      using success_sensitive_iff_source_target_rel_respects_success(1)
            divergence_reflection_iff_source_target_rel_reflects_divergence
            indRelR_cond_respects_predA_and_reflects_predB[where
              PredA="\<lambda>P. P\<down>.success" and PredB="divergentST"]
    by simp
qed

subsection \<open>Adding Operational Correspondence\<close>

text \<open>The effect of operational correspondence includes conditions (TRel is included,
        transitivity) that require a witness like indRelRTPO. In order to combine operational
        correspondence with success sensitiveness, we show that if the encoding and TRel (weakly)
        respects barbs than indRelRTPO (weakly) respects barbs. Since success is only a specific
        kind of barbs, the same holds for success sensitiveness.\<close>

lemma (in encoding_wrt_barbs) enc_and_TRel_impl_indRelRTPO_weakly_respects_success:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  assumes encRS:  "enc_weakly_respects_barb_set {success}"
      and trelPS: "rel_weakly_preserves_barb_set TRel TWB {success}"
      and trelRS: "rel_weakly_reflects_barb_set TRel TWB {success}"
  shows "rel_weakly_respects_barb_set (indRelRTPO TRel) (STCalWB SWB TWB) {success}"
proof auto
  fix P Q P'
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "P \<longmapsto>(Calculus (STCalWB SWB TWB))* P'"
     and "P'\<down><STCalWB SWB TWB>success"
  thus "Q\<Down><STCalWB SWB TWB>success"
  proof (induct arbitrary: P')
    case (encR S)
    assume "SourceTerm S \<longmapsto>(Calculus (STCalWB SWB TWB))* P'" and "P'\<down><STCalWB SWB TWB>success"
    hence "S\<Down><SWB>success"
        using STCalWB_reachesBarbST
      by blast
    with encRS have "\<lbrakk>S\<rbrakk>\<Down><TWB>success"
      by simp
    thus "TargetTerm (\<lbrakk>S\<rbrakk>)\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    case (source S)
    assume "SourceTerm S \<longmapsto>(Calculus (STCalWB SWB TWB))* P'" and "P'\<down><STCalWB SWB TWB>success"
    thus "SourceTerm S\<Down><STCalWB SWB TWB>success"
      by blast
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    moreover assume "TargetTerm T1 \<longmapsto>(Calculus (STCalWB SWB TWB))* P'"
                and "P'\<down><STCalWB SWB TWB>success"
    hence "T1\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "T2\<Down><TWB>success"
        using trelPS
      by simp
    thus "TargetTerm T2\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    case (trans P Q R)
    assume "P \<longmapsto>(Calculus (STCalWB SWB TWB))* P'" and "P'\<down><STCalWB SWB TWB>success"
       and "\<And>P'. P \<longmapsto>(Calculus (STCalWB SWB TWB))* P' \<Longrightarrow> P'\<down><STCalWB SWB TWB>success
            \<Longrightarrow> Q\<Down><STCalWB SWB TWB>success"
    hence "Q\<Down><STCalWB SWB TWB>success"
      by simp
    moreover assume "\<And>Q'. Q \<longmapsto>(Calculus (STCalWB SWB TWB))* Q' \<Longrightarrow> Q'\<down><STCalWB SWB TWB>success
                     \<Longrightarrow> R\<Down><STCalWB SWB TWB>success"
    ultimately show "R\<Down><STCalWB SWB TWB>success"
      by blast
  qed
next
  fix P Q Q'
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "Q \<longmapsto>(Calculus (STCalWB SWB TWB))* Q'"
     and "Q'\<down><STCalWB SWB TWB>success"
  thus "P\<Down><STCalWB SWB TWB>success"
  proof (induct arbitrary: Q')
    case (encR S)
    assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(Calculus (STCalWB SWB TWB))* Q'"
       and "Q'\<down><STCalWB SWB TWB>success"
    hence "\<lbrakk>S\<rbrakk>\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
    with encRS have "S\<Down><SWB>success"
        by simp
    thus "SourceTerm S\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    case (source S)
    assume "SourceTerm S \<longmapsto>(Calculus (STCalWB SWB TWB))* Q'" and "Q'\<down><STCalWB SWB TWB>success"
    thus "SourceTerm S\<Down><STCalWB SWB TWB>success"
      by blast
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    moreover assume "TargetTerm T2 \<longmapsto>(Calculus (STCalWB SWB TWB))* Q'"
                and "Q'\<down><STCalWB SWB TWB>success"
    hence "T2\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "T1\<Down><TWB>success"
        using trelRS
      by blast
  thus "TargetTerm T1\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    case (trans P Q R R')
    assume "R \<longmapsto>(Calculus (STCalWB SWB TWB))* R'" and "R'\<down><STCalWB SWB TWB>success"
       and "\<And>R'. R \<longmapsto>(Calculus (STCalWB SWB TWB))* R' \<Longrightarrow> R'\<down><STCalWB SWB TWB>success
            \<Longrightarrow> Q\<Down><STCalWB SWB TWB>success"
    hence "Q\<Down><STCalWB SWB TWB>success"
      by simp
    moreover assume "\<And>Q'. Q \<longmapsto>(Calculus (STCalWB SWB TWB))* Q' \<Longrightarrow> Q'\<down><STCalWB SWB TWB>success
                     \<Longrightarrow> P\<Down><STCalWB SWB TWB>success"
    ultimately show "P\<Down><STCalWB SWB TWB>success"
      by blast
  qed
qed

lemma (in encoding_wrt_barbs) enc_and_TRel_impl_indRelRTPO_weakly_respects_barbs:
  fixes TRel :: "('procT \<times> 'procT) set"
  assumes encRS:  "enc_weakly_respects_barbs"
      and trelPS: "rel_weakly_preserves_barbs TRel TWB"
      and trelRS: "rel_weakly_reflects_barbs TRel TWB"
  shows "rel_weakly_respects_barbs (indRelRTPO TRel) (STCalWB SWB TWB)"
proof auto
  fix P Q x P'
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "P \<longmapsto>(Calculus (STCalWB SWB TWB))* P'"
     and "P'\<down><STCalWB SWB TWB>x"
  thus "Q\<Down><STCalWB SWB TWB>x"
  proof (induct arbitrary: P')
    case (encR S)
    assume "SourceTerm S \<longmapsto>(Calculus (STCalWB SWB TWB))* P'" and "P'\<down><STCalWB SWB TWB>x"
    hence "S\<Down><SWB>x"
        using STCalWB_reachesBarbST
      by blast
    with encRS have "\<lbrakk>S\<rbrakk>\<Down><TWB>x"
      by simp
    thus "TargetTerm (\<lbrakk>S\<rbrakk>)\<Down><STCalWB SWB TWB>x"
        using STCalWB_reachesBarbST
      by blast
  next
    case (source S)
    assume "SourceTerm S \<longmapsto>(Calculus (STCalWB SWB TWB))* P'" and "P'\<down><STCalWB SWB TWB>x"
    thus "SourceTerm S\<Down><STCalWB SWB TWB>x"
      by blast
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    moreover assume "TargetTerm T1 \<longmapsto>(Calculus (STCalWB SWB TWB))* P'"
                and "P'\<down><STCalWB SWB TWB>x"
    hence "T1\<Down><TWB>x"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "T2\<Down><TWB>x"
        using trelPS
      by simp
    thus "TargetTerm T2\<Down><STCalWB SWB TWB>x"
        using STCalWB_reachesBarbST
      by blast
  next
    case (trans P Q R)
    assume "P \<longmapsto>(Calculus (STCalWB SWB TWB))* P'" and "P'\<down><STCalWB SWB TWB>x"
       and "\<And>P'. P \<longmapsto>(Calculus (STCalWB SWB TWB))* P' \<Longrightarrow> P'\<down><STCalWB SWB TWB>x
            \<Longrightarrow> Q\<Down><STCalWB SWB TWB>x"
    hence "Q\<Down><STCalWB SWB TWB>x"
      by simp
    moreover assume "\<And>Q'. Q \<longmapsto>(Calculus (STCalWB SWB TWB))* Q' \<Longrightarrow> Q'\<down><STCalWB SWB TWB>x
                     \<Longrightarrow> R\<Down><STCalWB SWB TWB>x"
    ultimately show "R\<Down><STCalWB SWB TWB>x"
      by blast
  qed
next
  fix P Q x Q'
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "Q \<longmapsto>(Calculus (STCalWB SWB TWB))* Q'"
     and "Q'\<down><STCalWB SWB TWB>x"
  thus "P\<Down><STCalWB SWB TWB>x"
  proof (induct arbitrary: Q')
    case (encR S)
    assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(Calculus (STCalWB SWB TWB))* Q'"
       and "Q'\<down><STCalWB SWB TWB>x"
    hence "\<lbrakk>S\<rbrakk>\<Down><TWB>x"
        using STCalWB_reachesBarbST
      by blast
    with encRS have "S\<Down><SWB>x"
        by simp
    thus "SourceTerm S\<Down><STCalWB SWB TWB>x"
        using STCalWB_reachesBarbST
      by blast
  next
    case (source S)
    assume "SourceTerm S \<longmapsto>(Calculus (STCalWB SWB TWB))* Q'" and "Q'\<down><STCalWB SWB TWB>x"
    thus "SourceTerm S\<Down><STCalWB SWB TWB>x"
      by blast
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    moreover assume "TargetTerm T2 \<longmapsto>(Calculus (STCalWB SWB TWB))* Q'"
                and "Q'\<down><STCalWB SWB TWB>x"
    hence "T2\<Down><TWB>x"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "T1\<Down><TWB>x"
        using trelRS
      by blast
  thus "TargetTerm T1\<Down><STCalWB SWB TWB>x"
        using STCalWB_reachesBarbST
      by blast
  next
    case (trans P Q R R')
    assume "R \<longmapsto>(Calculus (STCalWB SWB TWB))* R'" and "R'\<down><STCalWB SWB TWB>x"
       and "\<And>R'. R \<longmapsto>(Calculus (STCalWB SWB TWB))* R' \<Longrightarrow> R'\<down><STCalWB SWB TWB>x
            \<Longrightarrow> Q\<Down><STCalWB SWB TWB>x"
    hence "Q\<Down><STCalWB SWB TWB>x"
      by simp
    moreover assume "\<And>Q'. Q \<longmapsto>(Calculus (STCalWB SWB TWB))* Q' \<Longrightarrow> Q'\<down><STCalWB SWB TWB>x
                     \<Longrightarrow> P\<Down><STCalWB SWB TWB>x"
    ultimately show "P\<Down><STCalWB SWB TWB>x"
      by blast
  qed
qed

lemma (in encoding_wrt_barbs) enc_and_TRel_impl_indRelRTPO_respects_success:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  assumes encRS:  "enc_respects_barb_set {success}"
      and trelPS: "rel_preserves_barb_set TRel TWB {success}"
      and trelRS: "rel_reflects_barb_set TRel TWB {success}"
  shows "rel_respects_barb_set (indRelRTPO TRel) (STCalWB SWB TWB) {success}"
proof auto
  fix P Q
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "P\<down><STCalWB SWB TWB>success"
  thus "Q\<down><STCalWB SWB TWB>success"
  proof induct
    case (encR S)
    assume "SourceTerm S\<down><STCalWB SWB TWB>success"
    hence "S\<down><SWB>success"
        using STCalWB_hasBarbST
      by blast
    with encRS have "\<lbrakk>S\<rbrakk>\<down><TWB>success"
      by simp
    thus "TargetTerm (\<lbrakk>S\<rbrakk>)\<down><STCalWB SWB TWB>success"
        using STCalWB_hasBarbST
      by blast
  next
    case (source S)
    assume "SourceTerm S\<down><STCalWB SWB TWB>success"
    thus "SourceTerm S\<down><STCalWB SWB TWB>success"
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    moreover assume "TargetTerm T1\<down><STCalWB SWB TWB>success"
    hence "T1\<down><TWB>success"
        using STCalWB_hasBarbST
      by blast
    ultimately have "T2\<down><TWB>success"
        using trelPS
      by simp
    thus "TargetTerm T2\<down><STCalWB SWB TWB>success"
        using STCalWB_hasBarbST
      by blast
  next
    case (trans P Q R)
    assume "P\<down><STCalWB SWB TWB>success"
       and "P\<down><STCalWB SWB TWB>success \<Longrightarrow> Q\<down><STCalWB SWB TWB>success"
       and "Q\<down><STCalWB SWB TWB>success \<Longrightarrow> R\<down><STCalWB SWB TWB>success"
    thus "R\<down><STCalWB SWB TWB>success"
      by simp
  qed
next
  fix P Q
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "Q\<down><STCalWB SWB TWB>success"
  thus "P\<down><STCalWB SWB TWB>success"
  proof induct
    case (encR S)
    assume "TargetTerm (\<lbrakk>S\<rbrakk>)\<down><STCalWB SWB TWB>success"
    hence "\<lbrakk>S\<rbrakk>\<down><TWB>success"
        using STCalWB_hasBarbST
      by blast
    with encRS have "S\<down><SWB>success"
        by simp
    thus "SourceTerm S\<down><STCalWB SWB TWB>success"
        using STCalWB_hasBarbST
      by blast
  next
    case (source S)
    assume "SourceTerm S\<down><STCalWB SWB TWB>success"
    thus "SourceTerm S\<down><STCalWB SWB TWB>success"
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    moreover assume "TargetTerm T2\<down><STCalWB SWB TWB>success"
    hence "T2\<down><TWB>success"
        using STCalWB_hasBarbST
      by blast
    ultimately have "T1\<down><TWB>success"
        using trelRS
      by blast
  thus "TargetTerm T1\<down><STCalWB SWB TWB>success"
        using STCalWB_hasBarbST
      by blast
  next
    case (trans P Q R)
    assume "R\<down><STCalWB SWB TWB>success"
       and "R\<down><STCalWB SWB TWB>success \<Longrightarrow> Q\<down><STCalWB SWB TWB>success"
       and "Q\<down><STCalWB SWB TWB>success \<Longrightarrow> P\<down><STCalWB SWB TWB>success"
    thus "P\<down><STCalWB SWB TWB>success"
      by simp
  qed
qed

lemma (in encoding_wrt_barbs) enc_and_TRel_impl_indRelRTPO_respects_barbs:
  fixes TRel    :: "('procT \<times> 'procT) set"
  assumes encRS:  "enc_respects_barbs"
      and trelPS: "rel_preserves_barbs TRel TWB"
      and trelRS: "rel_reflects_barbs TRel TWB"
  shows "rel_respects_barbs (indRelRTPO TRel) (STCalWB SWB TWB)"
proof auto
  fix P Q x
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "P\<down><STCalWB SWB TWB>x"
  thus "Q\<down><STCalWB SWB TWB>x"
  proof induct
    case (encR S)
    assume "SourceTerm S\<down><STCalWB SWB TWB>x"
    hence "S\<down><SWB>x"
        using STCalWB_hasBarbST
      by blast
    with encRS have "\<lbrakk>S\<rbrakk>\<down><TWB>x"
      by simp
    thus "TargetTerm (\<lbrakk>S\<rbrakk>)\<down><STCalWB SWB TWB>x"
        using STCalWB_hasBarbST
      by blast
  next
    case (source S)
    assume "SourceTerm S\<down><STCalWB SWB TWB>x"
    thus "SourceTerm S\<down><STCalWB SWB TWB>x"
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    moreover assume "TargetTerm T1\<down><STCalWB SWB TWB>x"
    hence "T1\<down><TWB>x"
        using STCalWB_hasBarbST
      by blast
    ultimately have "T2\<down><TWB>x"
        using trelPS
      by simp
    thus "TargetTerm T2\<down><STCalWB SWB TWB>x"
        using STCalWB_hasBarbST
      by blast
  next
    case (trans P Q R)
    assume "P\<down><STCalWB SWB TWB>x"
       and "P\<down><STCalWB SWB TWB>x \<Longrightarrow> Q\<down><STCalWB SWB TWB>x"
       and "Q\<down><STCalWB SWB TWB>x \<Longrightarrow> R\<down><STCalWB SWB TWB>x"
    thus "R\<down><STCalWB SWB TWB>x"
      by simp
  qed
next
  fix P Q x
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "Q\<down><STCalWB SWB TWB>x"
  thus "P\<down><STCalWB SWB TWB>x"
  proof induct
    case (encR S)
    assume "TargetTerm (\<lbrakk>S\<rbrakk>)\<down><STCalWB SWB TWB>x"
    hence "\<lbrakk>S\<rbrakk>\<down><TWB>x"
        using STCalWB_hasBarbST
      by blast
    with encRS have "S\<down><SWB>x"
        by simp
    thus "SourceTerm S\<down><STCalWB SWB TWB>x"
        using STCalWB_hasBarbST
      by blast
  next
    case (source S)
    assume "SourceTerm S\<down><STCalWB SWB TWB>x"
    thus "SourceTerm S\<down><STCalWB SWB TWB>x"
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    moreover assume "TargetTerm T2\<down><STCalWB SWB TWB>x"
    hence "T2\<down><TWB>x"
        using STCalWB_hasBarbST
      by blast
    ultimately have "T1\<down><TWB>x"
        using trelRS
      by blast
  thus "TargetTerm T1\<down><STCalWB SWB TWB>x"
        using STCalWB_hasBarbST
      by blast
  next
    case (trans P Q R)
    assume "R\<down><STCalWB SWB TWB>x"
       and "R\<down><STCalWB SWB TWB>x \<Longrightarrow> Q\<down><STCalWB SWB TWB>x"
       and "Q\<down><STCalWB SWB TWB>x \<Longrightarrow> P\<down><STCalWB SWB TWB>x"
    thus "P\<down><STCalWB SWB TWB>x"
      by simp
  qed
qed

text \<open>An encoding is success sensitive and operational corresponding w.r.t. a bisimulation TRel
        that respects success iff there exists a bisimultion that includes TRel and respects
        success. The same holds if we consider not only success sensitiveness but barb
        sensitiveness in general.\<close>

lemma (in encoding_wrt_barbs) OC_SS_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding (TRel\<^sup>*)
          \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target
          \<and> enc_weakly_respects_barb_set {success}
          \<and> rel_weakly_respects_barb_set TRel TWB {success})
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_reduction_bisimulation Rel (STCal Source Target)
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success})"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_weakly_preserves_barb_set TRel TWB {success}"
     and A2: "rel_weakly_reflects_barb_set TRel TWB {success}"
     and A3: "enc_weakly_preserves_barb_set {success}"
     and A4: "enc_weakly_reflects_barb_set {success}"
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def have B2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    by (simp add: indRelRTPO.target)
  from Rel_def have B3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    by (simp add: indRelRTPO_to_TRel(4)[where TRel="TRel"])
  from Rel_def have B4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "operational_complete (TRel\<^sup>*)"
     and "operational_sound (TRel\<^sup>*)"
     and "weak_reduction_simulation (TRel\<^sup>+) Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel\<^sup>+ \<and> Q \<longmapsto>Target* Q'
          \<longrightarrow> (\<exists>P'. P \<longmapsto>Target* P' \<and> (P', Q') \<in> TRel\<^sup>+)"
  with Rel_def have B5: "weak_reduction_bisimulation Rel (STCal Source Target)"
      using OC_iff_indRelRTPO_is_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  from Rel_def A1 A2 A3 A4 have B6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_success[where TRel="TRel"
            and success="success"]
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
        \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
        \<and> weak_reduction_bisimulation Rel (STCal Source Target)
        \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_reduction_bisimulation Rel (STCal Source Target)
          \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
  from this obtain Rel where C1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and C2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and C3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and C4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
   and C5: "weak_reduction_bisimulation Rel (STCal Source Target)"
   and C6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
   \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "operational_corresponding (TRel\<^sup>*)
        \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target"
      using OC_iff_weak_reduction_bisimulation[where TRel="TRel"]
    by auto
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using C1 C6 by blast
  hence "enc_weakly_respects_barb_set {success}"
      using success_sensitive_iff_source_target_rel_weakly_respects_success
    by auto
  moreover have "rel_weakly_respects_barb_set TRel TWB {success}"
  proof auto
    fix TP TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>success"
    hence "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TQ\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>success"
    hence "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TP\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  qed
  ultimately show "operational_corresponding (TRel\<^sup>*)
   \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target
   \<and> enc_weakly_respects_barb_set {success} \<and> rel_weakly_respects_barb_set TRel TWB {success}"
    by fast
qed

lemma (in encoding_wrt_barbs) OC_SS_RB_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding (TRel\<^sup>*)
          \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target
          \<and> enc_weakly_respects_barbs \<and> enc_weakly_respects_barb_set {success}
          \<and> rel_weakly_respects_barbs TRel TWB \<and> rel_weakly_respects_barb_set TRel TWB {success})
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_reduction_bisimulation Rel (STCal Source Target)
            \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success})"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_weakly_preserves_barb_set TRel TWB {success}"
     and A2: "rel_weakly_reflects_barb_set TRel TWB {success}"
     and A3: "enc_weakly_preserves_barb_set {success}"
     and A4: "enc_weakly_reflects_barb_set {success}"
     and A5: "rel_weakly_preserves_barbs TRel TWB" and A6: "rel_weakly_reflects_barbs TRel TWB"
     and A7: "enc_weakly_preserves_barbs" and A8: "enc_weakly_reflects_barbs"
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def have B2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    by (simp add: indRelRTPO.target)
  from Rel_def have B3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    by (simp add: indRelRTPO_to_TRel(4)[where TRel="TRel"])
  from Rel_def have B4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "operational_complete (TRel\<^sup>*)"
     and "operational_sound (TRel\<^sup>*)"
     and "weak_reduction_simulation (TRel\<^sup>+) Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel\<^sup>+ \<and> Q \<longmapsto>Target* Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target* P' \<and> (P', Q') \<in> TRel\<^sup>+)"
  with Rel_def have B5: "weak_reduction_bisimulation Rel (STCal Source Target)"
      using OC_iff_indRelRTPO_is_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  from Rel_def A1 A2 A3 A4 have B6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_success[where TRel="TRel"
            and success="success"]
    by blast
  from Rel_def A5 A6 A7 A8 have B7: "rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_barbs[where TRel="TRel"]
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
        \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
        \<and> weak_reduction_bisimulation Rel (STCal Source Target)
        \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)
        \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 B7 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_reduction_bisimulation Rel (STCal Source Target)
          \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)
          \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
  from this obtain Rel where C: "(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_reduction_bisimulation Rel (STCal Source Target)
          \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)
          \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    by auto
  hence C1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by simp
  from C have C2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    by simp
  from C have C3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    by simp
  from C have C4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    by simp
  from C have C5: "weak_reduction_bisimulation Rel (STCal Source Target)"
    by simp
  from C have C7: "rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
    apply (rule conjE) apply (erule conjE)+ by blast
  from C have C6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule conjE) apply (erule conjE)+ by blast
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
   \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "operational_corresponding (TRel\<^sup>*)
        \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target"
      using OC_iff_weak_reduction_bisimulation[where TRel="TRel"]
    by auto
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using C1 C6 by blast
  hence "enc_weakly_respects_barb_set {success}"
      using success_sensitive_iff_source_target_rel_weakly_respects_success
    by auto
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
    apply (rule exI) using C1 C7 by blast
  hence "enc_weakly_respects_barbs"
      using enc_weakly_respects_barbs_iff_source_target_rel
    by auto
  moreover have "rel_weakly_respects_barb_set TRel TWB {success}"
  proof auto
    fix TP TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>success"
    hence "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TQ\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>success"
    hence "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TP\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  qed
  moreover have "rel_weakly_respects_barbs TRel TWB"
  proof auto
    fix TP TQ x TP'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>x"
    hence "TargetTerm TP\<Down><STCalWB SWB TWB>x"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TQ\<Down><STCalWB SWB TWB>x"
        using C7
      by blast
    thus "TQ\<Down><TWB>x"
        using STCalWB_reachesBarbST
      by blast
  next
    fix TP TQ x TQ'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>x"
    hence "TargetTerm TQ\<Down><STCalWB SWB TWB>x"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TP\<Down><STCalWB SWB TWB>x"
        using C7
      by blast
    thus "TP\<Down><TWB>x"
        using STCalWB_reachesBarbST
      by blast
  qed
  ultimately show "operational_corresponding (TRel\<^sup>*)
   \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target
   \<and> enc_weakly_respects_barbs \<and> enc_weakly_respects_barb_set {success}
   \<and> rel_weakly_respects_barbs TRel TWB \<and> rel_weakly_respects_barb_set TRel TWB {success}"
    by fast
qed

lemma (in encoding_wrt_barbs) OC_SS_wrt_preorder_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding TRel \<and> preorder TRel \<and> weak_reduction_bisimulation TRel Target
          \<and> enc_weakly_respects_barb_set {success}
          \<and> rel_weakly_respects_barb_set TRel TWB {success})
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> weak_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success})"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_weakly_preserves_barb_set TRel TWB {success}"
     and A2: "rel_weakly_reflects_barb_set TRel TWB {success}"
     and A3: "enc_weakly_preserves_barb_set {success}"
     and A4: "enc_weakly_reflects_barb_set {success}"
     and A5: "preorder TRel"
  from A5 have A6: "TRel\<^sup>+ = TRel"
      using trancl_id[of TRel] preorder_on_def
    by blast
  from A5 have A7: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding refl_on_def preorder_on_def
    by auto
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def A6 have B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by (auto simp add: indRelRTPO.target)
  from Rel_def A7 have B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "operational_complete TRel" and "operational_sound TRel"
     and "weak_reduction_simulation TRel Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel \<and> Q \<longmapsto>Target* Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target* P' \<and> (P', Q') \<in> TRel)"
  with Rel_def A6 A7 have B4: "weak_reduction_bisimulation Rel (STCal Source Target)"
      using OC_iff_indRelRTPO_is_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  from Rel_def A5 have B5: "preorder Rel"
      using indRelRTPO_is_preorder[where TRel="TRel"]
      unfolding preorder_on_def
    by blast
  from Rel_def A1 A2 A3 A4 have B6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_success[where TRel="TRel"
            and success="success"]
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
        \<and> weak_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
        \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> weak_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
          \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
  from this obtain Rel where C1: "(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)"
   and C2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and C3: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)"
   and C4: "weak_reduction_bisimulation Rel (STCal Source Target)" and C5: "preorder Rel"
   and C6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel})
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel) \<and> preorder Rel
   \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "operational_corresponding TRel \<and> preorder TRel \<and> weak_reduction_bisimulation TRel Target"
      using OC_wrt_preorder_iff_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using C1 C6 by blast
  hence "enc_weakly_respects_barb_set {success}"
      using success_sensitive_iff_source_target_rel_weakly_respects_success
    by simp
  moreover have "rel_weakly_respects_barb_set TRel TWB {success}"
  proof auto
    fix TP TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>success"
    hence "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TQ\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>success"
    hence "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TP\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  qed
  ultimately show "operational_corresponding TRel \<and> preorder TRel
   \<and> weak_reduction_bisimulation TRel Target
   \<and> enc_weakly_respects_barb_set {success} \<and> rel_weakly_respects_barb_set TRel TWB {success}"
    by fast
qed

lemma (in encoding_wrt_barbs) OC_SS_RB_wrt_preorder_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding TRel \<and> preorder TRel \<and> weak_reduction_bisimulation TRel Target
          \<and> enc_weakly_respects_barbs \<and> rel_weakly_respects_barbs TRel TWB
          \<and> enc_weakly_respects_barb_set {success}
          \<and> rel_weakly_respects_barb_set TRel TWB {success})
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> weak_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
            \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success})"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_weakly_preserves_barbs TRel TWB" and A2: "rel_weakly_reflects_barbs TRel TWB"
     and A3: "enc_weakly_preserves_barbs" and A4: "enc_weakly_reflects_barbs"
     and A5: "preorder TRel"
  from A5 have A6: "TRel\<^sup>+ = TRel"
      using trancl_id[of TRel]
      unfolding preorder_on_def
    by blast
  from A5 have A7: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding preorder_on_def refl_on_def
    by auto
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def A6 have B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by (auto simp add: indRelRTPO.target)
  from Rel_def A7 have B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "operational_complete TRel" and "operational_sound TRel"
     and "weak_reduction_simulation TRel Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel \<and> Q \<longmapsto>Target* Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target* P' \<and> (P', Q') \<in> TRel)"
  with Rel_def A6 A7 have B4: "weak_reduction_bisimulation Rel (STCal Source Target)"
      using OC_iff_indRelRTPO_is_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  from Rel_def A5 have B5: "preorder Rel"
      using indRelRTPO_is_preorder[where TRel="TRel"]
      unfolding preorder_on_def
    by blast
  from Rel_def A1 A2 A3 A4 have B6: "rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_barbs[where TRel="TRel"]
    by blast
  hence B7: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
        \<and> weak_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
        \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)
        \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 B7 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> weak_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
          \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)
          \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
  from this obtain Rel where C1: "(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)"
   and C2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and C3: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)"
   and C4: "weak_reduction_bisimulation Rel (STCal Source Target)" and C5: "preorder Rel"
   and C6: "rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel})
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel) \<and> preorder Rel
   \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "operational_corresponding TRel \<and> preorder TRel \<and> weak_reduction_bisimulation TRel Target"
      using OC_wrt_preorder_iff_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
    apply (rule exI) using C1 C6 by blast
  hence "enc_weakly_respects_barbs"
      using enc_weakly_respects_barbs_iff_source_target_rel
    by simp
  moreover hence "enc_weakly_respects_barb_set {success}"
    by simp
  moreover have "rel_weakly_respects_barbs TRel TWB"
  proof auto
    fix TP TQ x TP'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>x"
    hence "TargetTerm TP\<Down><STCalWB SWB TWB>x"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TQ\<Down><STCalWB SWB TWB>x"
        using C6
      by blast
    thus "TQ\<Down><TWB>x"
        using STCalWB_reachesBarbST
      by blast
  next
    fix TP TQ x TQ'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>x"
    hence "TargetTerm TQ\<Down><STCalWB SWB TWB>x"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TP\<Down><STCalWB SWB TWB>x"
        using C6
      by blast
    thus "TP\<Down><TWB>x"
        using STCalWB_reachesBarbST
      by blast
  qed
  moreover hence "rel_weakly_respects_barb_set TRel TWB {success}"
    by blast
  ultimately show "operational_corresponding TRel \<and> preorder TRel
   \<and> weak_reduction_bisimulation TRel Target
   \<and> enc_weakly_respects_barbs \<and> rel_weakly_respects_barbs TRel TWB 
   \<and> enc_weakly_respects_barb_set {success} \<and> rel_weakly_respects_barb_set TRel TWB {success}"
    by fast
qed

text \<open>An encoding is success sensitive and weakly operational corresponding w.r.t. a
        correspondence simulation TRel that respects success iff there exists a correspondence
        simultion that includes TRel and respects success. The same holds if we consider not only
        success sensitiveness but barb sensitiveness in general.\<close>

lemma (in encoding_wrt_barbs) WOC_SS_wrt_preorder_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(weakly_operational_corresponding TRel \<and> preorder TRel
          \<and> weak_reduction_correspondence_simulation TRel Target
          \<and> enc_weakly_respects_barb_set {success}
          \<and> rel_weakly_respects_barb_set TRel TWB {success})
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target) \<and> preorder Rel
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success})"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_weakly_preserves_barb_set TRel TWB {success}"
     and A2: "rel_weakly_reflects_barb_set TRel TWB {success}"
     and A3: "enc_weakly_preserves_barb_set {success}"
     and A4: "enc_weakly_reflects_barb_set {success}"
     and A5: "preorder TRel"
  from A5 have A6: "TRel\<^sup>+ = TRel"
      using trancl_id[of TRel]
      unfolding preorder_on_def
    by blast
  from A5 A6 have A7: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding preorder_on_def refl_on_def
    by auto
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def A6 have B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by (auto simp add: indRelRTPO.target)
  from Rel_def A7 have B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "operational_complete TRel" and "weakly_operational_sound TRel"
     and "weak_reduction_simulation TRel Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel \<and> Q \<longmapsto>Target* Q'
          \<longrightarrow> (\<exists>P'' Q''. P \<longmapsto>Target* P'' \<and> Q' \<longmapsto>Target* Q'' \<and> (P'', Q'') \<in> TRel)"
  with Rel_def A6 A7 have B4: "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
      using WOC_iff_indRelRTPO_is_reduction_correspondence_simulation[where TRel="TRel"]
    by simp
  from Rel_def A5 have B5: "preorder Rel"
      using indRelRTPO_is_preorder[where TRel="TRel"]
      unfolding preorder_on_def
    by blast
  from Rel_def A1 A2 A3 A4 have B6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_success[where TRel="TRel"
            and success="success"]
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
        \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target) \<and> preorder Rel
        \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target) \<and> preorder Rel
          \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
  from this obtain Rel where C1: "(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)"
   and C2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and C3: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)"
   and C4: "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
   and C5: "preorder Rel" and C6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel})
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel) \<and> preorder Rel
   \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target)"
    by blast
  hence "weakly_operational_corresponding TRel \<and> preorder TRel
         \<and> weak_reduction_correspondence_simulation TRel Target"
      using WOC_wrt_preorder_iff_reduction_correspondence_simulation[where TRel="TRel"]
    by simp
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using C1 C6 by blast
  hence "enc_weakly_respects_barb_set {success}"
      using success_sensitive_iff_source_target_rel_weakly_respects_success
    by simp
  moreover have "rel_weakly_respects_barb_set TRel TWB {success}"
  proof auto
    fix TP TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>success"
    hence "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TQ\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>success"
    hence "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TP\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  qed
  ultimately show "weakly_operational_corresponding TRel \<and> preorder TRel
   \<and> weak_reduction_correspondence_simulation TRel Target
   \<and> enc_weakly_respects_barb_set {success} \<and> rel_weakly_respects_barb_set TRel TWB {success}"
    by fast
qed

lemma (in encoding_wrt_barbs) WOC_SS_RB_wrt_preorder_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(weakly_operational_corresponding TRel \<and> preorder TRel
          \<and> weak_reduction_correspondence_simulation TRel Target
          \<and> enc_weakly_respects_barbs \<and> enc_weakly_respects_barb_set {success}
          \<and> rel_weakly_respects_barbs TRel TWB \<and> rel_weakly_respects_barb_set TRel TWB {success})
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target) \<and> preorder Rel
            \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success})"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_weakly_preserves_barb_set TRel TWB {success}"
     and A2: "rel_weakly_reflects_barb_set TRel TWB {success}"
     and A3: "enc_weakly_preserves_barb_set {success}"
     and A4: "enc_weakly_reflects_barb_set {success}"
     and A5: "preorder TRel"
     and A1': "rel_weakly_preserves_barbs TRel TWB" and A2': "rel_weakly_reflects_barbs TRel TWB"
     and A3': "enc_weakly_preserves_barbs" and A4': "enc_weakly_reflects_barbs"
  from A5 have A6: "TRel\<^sup>+ = TRel"
      using trancl_id[of TRel]
      unfolding preorder_on_def
    by blast
  from A5 A6 have A7: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding preorder_on_def refl_on_def
    by auto
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def A6 have B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by (auto simp add: indRelRTPO.target)
  from Rel_def A7 have B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "operational_complete TRel" and "weakly_operational_sound TRel"
     and "weak_reduction_simulation TRel Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel \<and> Q \<longmapsto>Target* Q'
          \<longrightarrow> (\<exists>P'' Q''. P \<longmapsto>Target* P'' \<and> Q' \<longmapsto>Target* Q'' \<and> (P'', Q'') \<in> TRel)"
  with Rel_def A6 A7 have B4: "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
      using WOC_iff_indRelRTPO_is_reduction_correspondence_simulation[where TRel="TRel"]
    by simp
  from Rel_def A5 have B5: "preorder Rel"
      using indRelRTPO_is_preorder[where TRel="TRel"]
      unfolding preorder_on_def
    by blast
  from Rel_def A1 A2 A3 A4 have B6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_success[where TRel="TRel"
            and success="success"]
    by blast
  from Rel_def A1' A2' A3' A4' have B7: "rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_barbs[where TRel="TRel"]
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
        \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target) \<and> preorder Rel
        \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)
        \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 B7 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target) \<and> preorder Rel
          \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)
          \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
  from this obtain Rel where C1: "(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)"
   and C2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and C3: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)"
   and C4: "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
   and C5: "preorder Rel" and C7: "rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel})
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel) \<and> preorder Rel
   \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target)"
    by blast
  hence "weakly_operational_corresponding TRel \<and> preorder TRel
         \<and> weak_reduction_correspondence_simulation TRel Target"
      using WOC_wrt_preorder_iff_reduction_correspondence_simulation[where TRel="TRel"]
    by simp
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_weakly_respects_barbs Rel (STCalWB SWB TWB)"
    apply (rule exI) using C1 C7 by blast
  hence D1: "enc_weakly_respects_barbs"
      using enc_weakly_respects_barbs_iff_source_target_rel
    by simp
  moreover from D1 have "enc_weakly_respects_barb_set {success}"
    by simp
  moreover have D2: "rel_weakly_respects_barbs TRel TWB"
  proof auto
    fix TP TQ x TP'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>x"
    hence "TargetTerm TP\<Down><STCalWB SWB TWB>x"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TQ\<Down><STCalWB SWB TWB>x"
        using C7
      by blast
    thus "TQ\<Down><TWB>x"
        using STCalWB_reachesBarbST
      by blast
  next
    fix TP TQ x TQ'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>x"
    hence "TargetTerm TQ\<Down><STCalWB SWB TWB>x"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TP\<Down><STCalWB SWB TWB>x"
        using C7
      by blast
    thus "TP\<Down><TWB>x"
        using STCalWB_reachesBarbST
      by blast
  qed
  moreover from D2 have "rel_weakly_respects_barb_set TRel TWB {success}"
    by blast
  ultimately show "weakly_operational_corresponding TRel \<and> preorder TRel
   \<and> weak_reduction_correspondence_simulation TRel Target
   \<and> enc_weakly_respects_barbs \<and> enc_weakly_respects_barb_set {success}
   \<and> rel_weakly_respects_barbs TRel TWB \<and> rel_weakly_respects_barb_set TRel TWB {success}"
    by fast
qed

text \<open>An encoding is strongly success sensitive and strongly operational corresponding w.r.t. a
        strong bisimulation TRel that strongly respects success iff there exists a strong
        bisimultion that includes TRel and strongly respects success. The same holds if we consider
        not only strong success sensitiveness but strong barb sensitiveness in general.\<close>

lemma (in encoding_wrt_barbs) SOC_SS_wrt_preorder_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_corresponding TRel \<and> preorder TRel
          \<and> strong_reduction_bisimulation TRel Target
          \<and> enc_respects_barb_set {success} \<and> rel_respects_barb_set TRel TWB {success})
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> strong_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
            \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success})"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_preserves_barb_set TRel TWB {success}"
     and A2: "rel_reflects_barb_set TRel TWB {success}"
     and A3: "enc_preserves_barb_set {success}" and A4: "enc_reflects_barb_set {success}"
     and A5: "preorder TRel"
  from A5 have A6: "TRel\<^sup>+ = TRel"
      using trancl_id[of TRel]
      unfolding preorder_on_def
    by blast
  from A5 A6 have A7: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding preorder_on_def refl_on_def
    by auto
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def A6 have B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by (auto simp add: indRelRTPO.target)
  from Rel_def A7 have B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "strongly_operational_complete TRel" and "strongly_operational_sound TRel"
     and "strong_reduction_simulation TRel Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel \<and> Q \<longmapsto>Target Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target P' \<and> (P', Q') \<in> TRel)"
  with Rel_def A6 A7 have B4: "strong_reduction_bisimulation Rel (STCal Source Target)"
      using SOC_iff_indRelRTPO_is_strong_reduction_bisimulation[where TRel="TRel"]
    by simp
  from Rel_def A5 have B5: "preorder Rel"
      using indRelRTPO_is_preorder[where TRel="TRel"]
      unfolding preorder_on_def
    by blast
  from Rel_def A1 A2 A3 A4 have B6: "rel_respects_barb_set Rel (STCalWB SWB TWB) {success}"
      using enc_and_TRel_impl_indRelRTPO_respects_success[where TRel="TRel" and success="success"]
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
        \<and> strong_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
        \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> strong_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
          \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}"
  from this obtain Rel where C1: "(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)"
   and C2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and C3: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)"
   and C4: "strong_reduction_bisimulation Rel (STCal Source Target)" and C5: "preorder Rel"
   and C6: "rel_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel})
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel) \<and> preorder Rel
   \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "strongly_operational_corresponding TRel \<and> preorder TRel
         \<and> strong_reduction_bisimulation TRel Target"
      using SOC_wrt_preorder_iff_strong_reduction_bisimulation[where TRel="TRel"]
    by simp
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using C1 C6 by blast
  hence "enc_respects_barb_set {success}"
      using success_sensitive_iff_source_target_rel_respects_success
    by simp
  moreover have "rel_respects_barb_set TRel TWB {success}"
  proof auto
    fix TP TQ
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP\<down><TWB>success"
    hence "TargetTerm TP\<down><STCalWB SWB TWB>success"
        using STCalWB_hasBarbST
      by blast
    ultimately have "TargetTerm TQ\<down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TQ\<down><TWB>success"
        using STCalWB_hasBarbST
      by blast
  next
    fix TP TQ
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ\<down><TWB>success"
    hence "TargetTerm TQ\<down><STCalWB SWB TWB>success"
        using STCalWB_hasBarbST
      by blast
    ultimately have "TargetTerm TP\<down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TP\<down><TWB>success"
        using STCalWB_hasBarbST
      by blast
  qed
  ultimately show "strongly_operational_corresponding TRel \<and> preorder TRel
   \<and> strong_reduction_bisimulation TRel Target
   \<and> enc_respects_barb_set {success} \<and> rel_respects_barb_set TRel TWB {success}"
    by fast
qed

lemma (in encoding_wrt_barbs) SOC_SS_RB_wrt_preorder_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_corresponding TRel \<and> preorder TRel
          \<and> strong_reduction_bisimulation TRel Target
          \<and> enc_respects_barbs \<and> rel_respects_barbs TRel TWB
          \<and> enc_respects_barb_set {success} \<and> rel_respects_barb_set TRel TWB {success})
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> strong_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
            \<and> rel_respects_barbs Rel (STCalWB SWB TWB)
            \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success})"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_preserves_barbs TRel TWB" and A2: "rel_reflects_barbs TRel TWB"
     and A3: "enc_preserves_barbs" and A4: "enc_reflects_barbs"
     and A5: "preorder TRel"
  from A5 have A6: "TRel\<^sup>+ = TRel"
      using trancl_id[of TRel]
      unfolding preorder_on_def
    by blast
  from A5 have A7: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding preorder_on_def refl_on_def
    by auto
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def A6 have B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by (auto simp add: indRelRTPO.target)
  from Rel_def A7 have B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "strongly_operational_complete TRel" and "strongly_operational_sound TRel"
     and "strong_reduction_simulation TRel Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel \<and> Q \<longmapsto>Target Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target P' \<and> (P', Q') \<in> TRel)"
  with Rel_def A6 A7 have B4: "strong_reduction_bisimulation Rel (STCal Source Target)"
      using SOC_iff_indRelRTPO_is_strong_reduction_bisimulation[where TRel="TRel"]
    by simp
  from Rel_def A5 have B5: "preorder Rel"
      using indRelRTPO_is_preorder[where TRel="TRel"]
      unfolding preorder_on_def
    by blast
  from Rel_def A1 A2 A3 A4 have B6: "rel_respects_barbs Rel (STCalWB SWB TWB)"
      using enc_and_TRel_impl_indRelRTPO_respects_barbs[where TRel="TRel"]
    by blast
  hence B7: "rel_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
        \<and> strong_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
        \<and> rel_respects_barbs Rel (STCalWB SWB TWB)
        \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> strong_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
          \<and> rel_respects_barbs Rel (STCalWB SWB TWB)
          \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}"
  from this obtain Rel where C1: "(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)"
   and C2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and C3: "(\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)"
   and C4: "strong_reduction_bisimulation Rel (STCal Source Target)" and C5: "preorder Rel"
   and C6: "rel_respects_barbs Rel (STCalWB SWB TWB)"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel})
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel) \<and> preorder Rel
   \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "strongly_operational_corresponding TRel \<and> preorder TRel
         \<and> strong_reduction_bisimulation TRel Target"
      using SOC_wrt_preorder_iff_strong_reduction_bisimulation[where TRel="TRel"]
    by simp
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_respects_barbs Rel (STCalWB SWB TWB)"
    apply (rule exI) using C1 C6 by blast
  hence "enc_respects_barbs"
      using enc_respects_barbs_iff_source_target_rel
    by simp
  moreover hence "enc_respects_barb_set {success}"
    by simp
  moreover have "rel_respects_barbs TRel TWB"
  proof auto
    fix TP TQ x
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP\<down><TWB>x"
    hence "TargetTerm TP\<down><STCalWB SWB TWB>x"
        using STCalWB_hasBarbST
      by blast
    ultimately have "TargetTerm TQ\<down><STCalWB SWB TWB>x"
        using C6
      by blast
    thus "TQ\<down><TWB>x"
        using STCalWB_hasBarbST
      by blast
  next
    fix TP TQ x
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ\<down><TWB>x"
    hence "TargetTerm TQ\<down><STCalWB SWB TWB>x"
        using STCalWB_hasBarbST
      by blast
    ultimately have "TargetTerm TP\<down><STCalWB SWB TWB>x"
        using C6
      by blast
    thus "TP\<down><TWB>x"
        using STCalWB_hasBarbST
      by blast
  qed
  moreover hence "rel_respects_barb_set TRel TWB {success}"
    by blast
  ultimately show "strongly_operational_corresponding TRel \<and> preorder TRel
   \<and> strong_reduction_bisimulation TRel Target
   \<and> enc_respects_barbs \<and> rel_respects_barbs TRel TWB
   \<and> enc_respects_barb_set {success} \<and> rel_respects_barb_set TRel TWB {success}"
    by fast
qed

text \<open>Next we also add divergence reflection to operational correspondence and success
        sensitiveness.\<close>

lemma (in encoding) enc_and_TRelimpl_indRelRTPO_reflect_divergence:
  fixes TRel    :: "('procT \<times> 'procT) set"
  assumes encRD:  "enc_reflects_divergence"
      and trelRD: "rel_reflects_divergence TRel Target"
  shows "rel_reflects_divergence (indRelRTPO TRel) (STCal Source Target)"
proof auto
  fix P Q
  assume "P \<lesssim>\<lbrakk>\<cdot>\<rbrakk>RT<TRel> Q" and "Q \<longmapsto>(STCal Source Target)\<omega>"
  thus "P \<longmapsto>(STCal Source Target)\<omega>"
  proof induct
    case (encR S)
    assume "TargetTerm (\<lbrakk>S\<rbrakk>) \<longmapsto>(STCal Source Target)\<omega>"
    hence "\<lbrakk>S\<rbrakk> \<longmapsto>(Target)\<omega>"
      by (simp add: STCal_divergent(2))
    with encRD have "S \<longmapsto>(Source)\<omega>"
      by simp
    thus "SourceTerm S \<longmapsto>(STCal Source Target)\<omega>"
      by (simp add: STCal_divergent(1))
  next
    case (source S)
    assume "SourceTerm S \<longmapsto>(STCal Source Target)\<omega>"
    thus "SourceTerm S \<longmapsto>(STCal Source Target)\<omega>"
      by simp
  next
    case (target T1 T2)
    assume "(T1, T2) \<in> TRel"
    moreover assume "TargetTerm T2 \<longmapsto>(STCal Source Target)\<omega>"
    hence "T2 \<longmapsto>(Target)\<omega>"
      by (simp add: STCal_divergent(2))
    ultimately have "T1 \<longmapsto>(Target)\<omega>"
        using trelRD
      by blast
    thus "TargetTerm T1 \<longmapsto>(STCal Source Target)\<omega>"
      by (simp add: STCal_divergent(2))
  next
    case (trans P Q R)
    assume "R \<longmapsto>(STCal Source Target)\<omega>"
       and "R \<longmapsto>(STCal Source Target)\<omega> \<Longrightarrow> Q \<longmapsto>(STCal Source Target)\<omega>"
       and "Q \<longmapsto>(STCal Source Target)\<omega> \<Longrightarrow> P \<longmapsto>(STCal Source Target)\<omega>"
    thus "P \<longmapsto>(STCal Source Target)\<omega>"
      by simp
  qed
qed

lemma (in encoding_wrt_barbs) OC_SS_DR_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding (TRel\<^sup>*)
          \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target
          \<and> enc_weakly_respects_barb_set {success}
          \<and> rel_weakly_respects_barb_set TRel TWB {success}
          \<and> enc_reflects_divergence \<and> rel_reflects_divergence TRel Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
            \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
            \<and> weak_reduction_bisimulation Rel (STCal Source Target)
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
            \<and> rel_reflects_divergence Rel (STCal Source Target))"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_weakly_preserves_barb_set TRel TWB {success}"
     and A2: "rel_weakly_reflects_barb_set TRel TWB {success}"
     and A3: "enc_weakly_preserves_barb_set {success}"
     and A4: "enc_weakly_reflects_barb_set {success}"
     and A5: "rel_reflects_divergence TRel Target" and A6: "enc_reflects_divergence"
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def have B2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
    by (simp add: indRelRTPO.target)
  from Rel_def have B3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
    by (simp add: indRelRTPO_to_TRel(4)[where TRel="TRel"])
  from Rel_def have B4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "operational_complete (TRel\<^sup>*)"
     and "operational_sound (TRel\<^sup>*)"
     and "weak_reduction_simulation (TRel\<^sup>+) Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel\<^sup>+ \<and> Q \<longmapsto>Target* Q'
          \<longrightarrow> (\<exists>P'. P \<longmapsto>Target* P' \<and> (P', Q') \<in> TRel\<^sup>+)"
  with Rel_def have B5: "weak_reduction_bisimulation Rel (STCal Source Target)"
      using OC_iff_indRelRTPO_is_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  from Rel_def A1 A2 A3 A4 have B6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_success[where TRel="TRel"
            and success="success"]
    by blast
  from Rel_def A5 A6 have B7: "rel_reflects_divergence Rel (STCal Source Target)"
      using enc_and_TRelimpl_indRelRTPO_reflect_divergence[where TRel="TRel"]
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
        \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
        \<and> weak_reduction_bisimulation Rel (STCal Source Target)
        \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
        \<and> rel_reflects_divergence Rel (STCal Source Target)"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 B7 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
          \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
          \<and> weak_reduction_bisimulation Rel (STCal Source Target)
          \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
          \<and> rel_reflects_divergence Rel (STCal Source Target)"
  from this obtain Rel where C1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and C2: "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
   and C3: "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
   and C4: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
   and C5: "weak_reduction_bisimulation Rel (STCal Source Target)"
   and C6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
   and C7: "rel_reflects_divergence Rel (STCal Source Target)"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
   \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
   \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "operational_corresponding (TRel\<^sup>*)
        \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target"
      using OC_iff_weak_reduction_bisimulation[where TRel="TRel"]
    by auto
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
                 \<and> rel_reflects_divergence Rel (STCal Source Target)"
    apply (rule exI) using C1 C6 C7 by blast
  hence "enc_weakly_respects_barb_set {success} \<and> enc_reflects_divergence"
      using WSS_DR_iff_source_target_rel
    by auto
  moreover have "rel_weakly_respects_barb_set TRel TWB {success}"
  proof auto
    fix TP TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>success"
    hence "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TQ\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>success"
    hence "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TP\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  qed
  moreover from C2 C7 have "rel_reflects_divergence TRel Target"
      using STCal_divergent(2)
    by blast
  ultimately show "operational_corresponding (TRel\<^sup>*)
   \<and> weak_reduction_bisimulation (TRel\<^sup>+) Target
   \<and> enc_weakly_respects_barb_set {success} \<and> rel_weakly_respects_barb_set TRel TWB {success}
   \<and> enc_reflects_divergence \<and> rel_reflects_divergence TRel Target"
    by fast
qed

lemma (in encoding_wrt_barbs) WOC_SS_DR_wrt_preorder_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(weakly_operational_corresponding TRel \<and> preorder TRel
          \<and> weak_reduction_correspondence_simulation TRel Target
          \<and> enc_weakly_respects_barb_set {success}
          \<and> rel_weakly_respects_barb_set TRel TWB {success}
          \<and> enc_reflects_divergence \<and> rel_reflects_divergence TRel Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target) \<and> preorder Rel
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
            \<and> rel_reflects_divergence Rel (STCal Source Target))"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_weakly_preserves_barb_set TRel TWB {success}"
     and A2: "rel_weakly_reflects_barb_set TRel TWB {success}"
     and A3: "enc_weakly_preserves_barb_set {success}"
     and A4: "enc_weakly_reflects_barb_set {success}"
     and A5: "rel_reflects_divergence TRel Target" and A6: "enc_reflects_divergence"
     and A7: "preorder TRel"
  from A7 have A8: "TRel\<^sup>+ = TRel"
      using trancl_id[of TRel]
      unfolding preorder_on_def
    by blast
  from A7 have A9: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding preorder_on_def refl_on_def
    by auto
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def A8 have B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by (auto simp add: indRelRTPO.target)
  from Rel_def A9 have B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "operational_complete TRel" and "weakly_operational_sound TRel" and "preorder TRel"
     and "weak_reduction_simulation TRel Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel \<and> Q \<longmapsto>Target* Q'
          \<longrightarrow> (\<exists>P'' Q''. P \<longmapsto>Target* P'' \<and> Q' \<longmapsto>Target* Q'' \<and> (P'', Q'') \<in> TRel)"
  with Rel_def A8 A9 have B4: "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
      using WOC_iff_indRelRTPO_is_reduction_correspondence_simulation[where TRel="TRel"]
    by simp
  from Rel_def A7 have B5: "preorder Rel"
      using indRelRTPO_is_preorder[where TRel="TRel"]
      unfolding preorder_on_def
    by simp
  from Rel_def A1 A2 A3 A4 have B6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_success[where TRel="TRel"
            and success="success"]
    by blast
  from Rel_def A5 A6 have B7: "rel_reflects_divergence Rel (STCal Source Target)"
      using enc_and_TRelimpl_indRelRTPO_reflect_divergence[where TRel="TRel"]
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
        \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target) \<and> preorder Rel
        \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
        \<and> rel_reflects_divergence Rel (STCal Source Target)"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 B7 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target) \<and> preorder Rel
          \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
          \<and> rel_reflects_divergence Rel (STCal Source Target)"
  from this obtain Rel where C1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and C2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and C3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
   and C4: "weak_reduction_correspondence_simulation Rel (STCal Source Target)"
   and C5: "preorder Rel" and C6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
   and C7: "rel_reflects_divergence Rel (STCal Source Target)"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel) \<and> preorder Rel
   \<and> weak_reduction_correspondence_simulation Rel (STCal Source Target)"
    by blast
  hence "weakly_operational_corresponding TRel \<and> preorder TRel
         \<and> weak_reduction_correspondence_simulation TRel Target"
      using WOC_wrt_preorder_iff_reduction_correspondence_simulation[where TRel="TRel"]
    by simp
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
                 \<and> rel_reflects_divergence Rel (STCal Source Target)"
    apply (rule exI) using C1 C6 C7 by blast
  hence "enc_weakly_respects_barb_set {success} \<and> enc_reflects_divergence"
      using WSS_DR_iff_source_target_rel
    by simp
  moreover have "rel_weakly_respects_barb_set TRel TWB {success}"
  proof auto
    fix TP TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>success"
    hence "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TQ\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>success"
    hence "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TP\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  qed
  moreover from C2 C7 have "rel_reflects_divergence TRel Target"
      using STCal_divergent(2)
    by blast
  ultimately
  show "weakly_operational_corresponding TRel \<and> preorder TRel
   \<and> weak_reduction_correspondence_simulation TRel Target
   \<and> enc_weakly_respects_barb_set {success} \<and> rel_weakly_respects_barb_set TRel TWB {success}
   \<and> enc_reflects_divergence \<and> rel_reflects_divergence TRel Target"
    by fast
qed

lemma (in encoding_wrt_barbs) OC_SS_DR_wrt_preorder_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(operational_corresponding TRel \<and> preorder TRel \<and> weak_reduction_bisimulation TRel Target
          \<and> enc_weakly_respects_barb_set {success}
          \<and> rel_weakly_respects_barb_set TRel TWB {success}
          \<and> enc_reflects_divergence \<and> rel_reflects_divergence TRel Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> weak_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
            \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
            \<and> rel_reflects_divergence Rel (STCal Source Target))"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_weakly_preserves_barb_set TRel TWB {success}"
     and A2: "rel_weakly_reflects_barb_set TRel TWB {success}"
     and A3: "enc_weakly_preserves_barb_set {success}"
     and A4: "enc_weakly_reflects_barb_set {success}"
     and A5: "rel_reflects_divergence TRel Target" and A6: "enc_reflects_divergence"
     and A7: "preorder TRel"
  from A7 have A8: "TRel\<^sup>+ = TRel"
      using trancl_id[of TRel]
      unfolding preorder_on_def
    by blast
  from A7 have A9: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding preorder_on_def refl_on_def
    by auto
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def A8 have B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by (auto simp add: indRelRTPO.target)
  from Rel_def A9 have B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "operational_complete TRel" and "operational_sound TRel" and "preorder TRel"
     and "weak_reduction_simulation TRel Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel \<and> Q \<longmapsto>Target* Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target* P' \<and> (P', Q') \<in> TRel)"
  with Rel_def A8 A9 have B4: "weak_reduction_bisimulation Rel (STCal Source Target)"
      using OC_iff_indRelRTPO_is_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  from Rel_def A7 have B5: "preorder Rel"
      using indRelRTPO_is_preorder[where TRel="TRel"]
      unfolding preorder_on_def
    by simp
  from Rel_def A1 A2 A3 A4 have B6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
      using enc_and_TRel_impl_indRelRTPO_weakly_respects_success[where TRel="TRel"
            and success="success"]
    by blast
  from Rel_def A5 A6 have B7: "rel_reflects_divergence Rel (STCal Source Target)"
      using enc_and_TRelimpl_indRelRTPO_reflect_divergence[where TRel="TRel"]
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
        \<and> weak_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
        \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
        \<and> rel_reflects_divergence Rel (STCal Source Target)"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 B7 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> weak_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
          \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
          \<and> rel_reflects_divergence Rel (STCal Source Target)"
  from this obtain Rel where C1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and C2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and C3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
   and C4: "weak_reduction_bisimulation Rel (STCal Source Target)" and C5: "preorder Rel"
   and C6: "rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}"
   and C7: "rel_reflects_divergence Rel (STCal Source Target)"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel) \<and> preorder Rel
   \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "operational_corresponding TRel \<and> preorder TRel \<and> weak_reduction_bisimulation TRel Target"
      using OC_wrt_preorder_iff_weak_reduction_bisimulation[where TRel="TRel"]
    by simp
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_weakly_respects_barb_set Rel (STCalWB SWB TWB) {success}
                 \<and> rel_reflects_divergence Rel (STCal Source Target)"
    apply (rule exI) using C1 C6 C7 by blast
  hence "enc_weakly_respects_barb_set {success} \<and> enc_reflects_divergence"
      using WSS_DR_iff_source_target_rel
    by simp
  moreover have "rel_weakly_respects_barb_set TRel TWB {success}"
  proof auto
    fix TP TQ TP'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP \<longmapsto>(Calculus TWB)* TP'" and "TP'\<down><TWB>success"
    hence "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TQ\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  next
    fix TP TQ TQ'
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ \<longmapsto>(Calculus TWB)* TQ'" and "TQ'\<down><TWB>success"
    hence "TargetTerm TQ\<Down><STCalWB SWB TWB>success"
        using STCalWB_reachesBarbST
      by blast
    ultimately have "TargetTerm TP\<Down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TP\<Down><TWB>success"
        using STCalWB_reachesBarbST
      by blast
  qed
  moreover from C2 C7 have "rel_reflects_divergence TRel Target"
      using STCal_divergent(2)
    by blast
  ultimately
  show "operational_corresponding TRel \<and> preorder TRel \<and> weak_reduction_bisimulation TRel Target
   \<and> enc_weakly_respects_barb_set {success} \<and> rel_weakly_respects_barb_set TRel TWB {success}
   \<and> enc_reflects_divergence \<and> rel_reflects_divergence TRel Target"
    by fast
qed

lemma (in encoding_wrt_barbs) SOC_SS_DR_wrt_preorder_iff_source_target_rel:
  fixes success :: "'barbs"
    and TRel    :: "('procT \<times> 'procT) set"
  shows "(strongly_operational_corresponding TRel \<and> preorder TRel
          \<and> strong_reduction_bisimulation TRel Target
          \<and> enc_respects_barb_set {success} \<and> rel_respects_barb_set TRel TWB {success}
          \<and> enc_reflects_divergence \<and> rel_reflects_divergence TRel Target)
         = (\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
            \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
            \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
            \<and> strong_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
            \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}
            \<and> rel_reflects_divergence Rel (STCal Source Target))"
proof (rule iffI, (erule conjE)+)
  assume A1: "rel_preserves_barb_set TRel TWB {success}"
     and A2: "rel_reflects_barb_set TRel TWB {success}"
     and A3: "enc_preserves_barb_set {success}" and A4: "enc_reflects_barb_set {success}"
     and A5: "rel_reflects_divergence TRel Target" and A6: "enc_reflects_divergence"
     and A7: "preorder TRel"
  from A7 have A8: "TRel\<^sup>+ = TRel"
      using trancl_id[of TRel]
      unfolding preorder_on_def
    by blast
  from A7 have A9: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding preorder_on_def refl_on_def
    by auto
  define Rel where "Rel = indRelRTPO TRel"
  hence B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
    by (simp add: indRelRTPO.encR)
  from Rel_def A8 have B2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
      using indRelRTPO_to_TRel(4)[where TRel="TRel"]
    by (auto simp add: indRelRTPO.target)
  from Rel_def A9 have B3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
      using indRelRTPO_to_TRel(2)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by simp
  assume "strongly_operational_complete TRel" and "strongly_operational_sound TRel"
     and "preorder TRel" and "strong_reduction_simulation TRel Target"
     and "\<forall>P Q Q'. (P, Q) \<in> TRel \<and> Q \<longmapsto>Target Q' \<longrightarrow> (\<exists>P'. P \<longmapsto>Target P' \<and> (P', Q') \<in> TRel)"
  with Rel_def A8 A9 have B4: "strong_reduction_bisimulation Rel (STCal Source Target)"
      using SOC_iff_indRelRTPO_is_strong_reduction_bisimulation[where TRel="TRel"]
    by simp
  from Rel_def A7 have B5: "preorder Rel"
      using indRelRTPO_is_preorder[where TRel="TRel"]
      unfolding preorder_on_def
    by simp
  from Rel_def A1 A2 A3 A4 have B6: "rel_respects_barb_set Rel (STCalWB SWB TWB) {success}"
      using enc_and_TRel_impl_indRelRTPO_respects_success[where TRel="TRel" and success="success"]
    by blast
  from Rel_def A5 A6 have B7: "rel_reflects_divergence Rel (STCal Source Target)"
      using enc_and_TRelimpl_indRelRTPO_reflect_divergence[where TRel="TRel"]
    by blast
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
        \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
        \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
        \<and> strong_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
        \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}
        \<and> rel_reflects_divergence Rel (STCal Source Target)"
    apply (rule exI) using B1 B2 B3 B4 B5 B6 B7 by blast
next
  assume "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
          \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
          \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel)
          \<and> strong_reduction_bisimulation Rel (STCal Source Target) \<and> preorder Rel
          \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}
          \<and> rel_reflects_divergence Rel (STCal Source Target)"
  from this obtain Rel where C1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
   and C2: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and C3: "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel"
   and C4: "strong_reduction_bisimulation Rel (STCal Source Target)" and C5: "preorder Rel"
   and C6: "rel_respects_barb_set Rel (STCalWB SWB TWB) {success}"
   and C7: "rel_reflects_divergence Rel (STCal Source Target)"
    by auto
  from C1 C2 C3 C4 C5 have "\<exists>Rel.(\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
   \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
   \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel) \<and> preorder Rel
   \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  hence "strongly_operational_corresponding TRel \<and> preorder TRel
         \<and> strong_reduction_bisimulation TRel Target"
      using SOC_wrt_preorder_iff_strong_reduction_bisimulation[where TRel="TRel"]
    by simp
  moreover have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
                 \<and> rel_respects_barb_set Rel (STCalWB SWB TWB) {success}
                 \<and> rel_reflects_divergence Rel (STCal Source Target)"
    apply (rule exI) using C1 C6 C7 by blast
  hence "enc_respects_barb_set {success} \<and> enc_reflects_divergence"
      using SS_DR_iff_source_target_rel
    by simp
  moreover have "rel_respects_barb_set TRel TWB {success}"
  proof auto
    fix TP TQ
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TP\<down><TWB>success"
    hence "TargetTerm TP\<down><STCalWB SWB TWB>success"
        using STCalWB_hasBarbST
      by blast
    ultimately have "TargetTerm TQ\<down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TQ\<down><TWB>success"
        using STCalWB_hasBarbST
      by blast
  next
    fix TP TQ
    assume "(TP, TQ) \<in> TRel"
    with C2 have "(TargetTerm TP, TargetTerm TQ) \<in> Rel"
      by simp
    moreover assume "TQ\<down><TWB>success"
    hence "TargetTerm TQ\<down><STCalWB SWB TWB>success"
        using STCalWB_hasBarbST
      by blast
    ultimately have "TargetTerm TP\<down><STCalWB SWB TWB>success"
        using C6
      by blast
    thus "TP\<down><TWB>success"
        using STCalWB_hasBarbST
      by blast
  qed
  moreover from C2 C7 have "rel_reflects_divergence TRel Target"
      using STCal_divergent(2)
    by blast
  ultimately show "strongly_operational_corresponding TRel \<and> preorder TRel
   \<and> strong_reduction_bisimulation TRel Target
   \<and> enc_respects_barb_set {success} \<and> rel_respects_barb_set TRel TWB {success}
   \<and> enc_reflects_divergence \<and> rel_reflects_divergence TRel Target"
    by fast
qed

subsection \<open>Full Abstraction and Operational Correspondence\<close>

text \<open>To combine full abstraction and operational correspondence we consider a symmetric version
        of the induced relation and assume that the relations SRel and TRel are equivalences. Then
        an encoding is fully abstract w.r.t. SRel and TRel and operationally corresponding w.r.t.
        TRel such that TRel is a bisimulation iff the induced relation contains both SRel and TRel
        and is a transitive bisimulation.\<close>

lemma (in encoding) FS_OC_modulo_equivalences_iff_source_target_relation:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes eqS: "equivalence SRel"
      and eqT: "equivalence TRel"
  shows "fully_abstract SRel TRel
         \<and> operational_corresponding TRel \<and> weak_reduction_bisimulation TRel Target
         \<longleftrightarrow> (\<exists>Rel.
         (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
         \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
         \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
         \<and> trans Rel \<and> weak_reduction_bisimulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE, erule conjE)
  assume A1: "fully_abstract SRel TRel" and A2: "operational_corresponding TRel"
     and A3: "weak_reduction_bisimulation TRel Target"
  from eqT have A4: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
    by auto
  have A5:
   "\<forall>S. SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S"
    by (simp add: indRelTEQ.encR indRelTEQ.encL)
  moreover from A4 have A6: "TRel = {(T1, T2). TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2}"
      using indRelTEQ_to_TRel(4)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by (auto simp add: indRelTEQ.target)
  moreover have A7: "trans (indRelTEQ TRel)"
      using indRelTEQ.trans[where TRel="TRel"]
      unfolding trans_def
    by blast
  moreover have "SRel = {(S1, S2). SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S2}"
  proof -
    from A6 have "\<forall>S1 S2. ((\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel) = TargetTerm (\<lbrakk>S1\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S2\<rbrakk>)"
      by blast
    moreover have "indRelTEQ TRel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} = indRelTEQ TRel"
      by (auto simp add: indRelTEQ.encL)
    with A7 have "trans (indRelTEQ TRel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
        unfolding trans_def
      by blast
    ultimately show "SRel = {(S1, S2). SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S2}"
        using A1 A5 full_abstraction_and_trans_relation_contains_TRel_impl_SRel[where
                    SRel="SRel" and TRel="TRel" and Rel="indRelTEQ TRel"]
      by blast
  qed
  moreover from eqT A2 A3 have "weak_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
      using OC_wrt_equivalence_iff_indRelTEQ_weak_reduction_bisimulation[where TRel="TRel"]
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
         \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
         \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
         \<and> trans Rel \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
next
  assume
   "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
    \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
    \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}
    \<and> trans Rel \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
  from this obtain Rel where
       B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
   and B2: "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
   and B3: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}"
   and B4: "trans Rel" and B5: "weak_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  from B1 B2 B3 B4 have "fully_abstract SRel TRel"
      using trans_source_target_relation_impl_fully_abstract[where Rel="Rel" and SRel="SRel"
            and TRel="TRel"]
    by blast
  moreover have "operational_corresponding TRel \<and> weak_reduction_bisimulation TRel Target"
  proof -
    from eqT have C1: "TRel\<^sup>+ = TRel"
        using trancl_id[of TRel]
        unfolding equiv_def
      by blast
    from eqT have C2: "TRel\<^sup>* = TRel"
        using reflcl_trancl[of TRel] trancl_id[of TRel]
        unfolding equiv_def refl_on_def
      by auto
    from B1 have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    moreover from B3 have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      by simp
    moreover from B3 C1 have "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
      by simp
    moreover have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    proof clarify
      fix S T
      from B1 have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
        by simp
      moreover assume "(SourceTerm S, TargetTerm T) \<in> Rel"
      ultimately have "(TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel"
          using B4
          unfolding trans_def
        by blast
      with B3 C2 show "(\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
        by simp
    qed
    ultimately have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
     \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
     \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
     \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
     \<and> weak_reduction_bisimulation Rel (STCal Source Target)"
           using B5
         by blast
    with C1 C2 show "operational_corresponding TRel \<and> weak_reduction_bisimulation TRel Target"
        using OC_iff_weak_reduction_bisimulation[where TRel="TRel"]
      by auto
  qed
  ultimately show "fully_abstract SRel TRel \<and> operational_corresponding TRel
                   \<and> weak_reduction_bisimulation TRel Target"
    by simp
qed

lemma (in encoding) FA_SOC_modulo_equivalences_iff_source_target_relation:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes eqS: "equivalence SRel"
      and eqT: "equivalence TRel"
  shows "fully_abstract SRel TRel \<and> strongly_operational_corresponding TRel
         \<and> strong_reduction_bisimulation TRel Target \<longleftrightarrow> (\<exists>Rel.
         (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
         \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
         \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
         \<and> strong_reduction_bisimulation Rel (STCal Source Target))"
proof (rule iffI, erule conjE, erule conjE)
  assume A1: "fully_abstract SRel TRel" and A2: "strongly_operational_corresponding TRel"
     and A3: "strong_reduction_bisimulation TRel Target"
  from eqT have A4: "TRel\<^sup>* = TRel"
      using reflcl_trancl[of TRel] trancl_id[of TRel]
      unfolding equiv_def refl_on_def
    by auto
  have A5:
   "\<forall>S. SourceTerm S \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S\<rbrakk>) \<and> TargetTerm (\<lbrakk>S\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S"
    by (simp add: indRelTEQ.encR indRelTEQ.encL)
  moreover from A4 have A6: "TRel = {(T1, T2). TargetTerm T1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm T2}"
      using indRelTEQ_to_TRel(4)[where TRel="TRel"]
            trans_closure_of_TRel_refl_cond[where TRel="TRel"]
    by (auto simp add: indRelTEQ.target)
  moreover have A7: "trans (indRelTEQ TRel)"
      using indRelTEQ.trans[where TRel="TRel"]
      unfolding trans_def
    by blast
  moreover have "SRel = {(S1, S2). SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S2}"
  proof -
    from A6 have "\<forall>S1 S2. ((\<lbrakk>S1\<rbrakk>, \<lbrakk>S2\<rbrakk>) \<in> TRel) = TargetTerm (\<lbrakk>S1\<rbrakk>) \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> TargetTerm (\<lbrakk>S2\<rbrakk>)"
      by blast
    moreover have "indRelTEQ TRel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q} = indRelTEQ TRel"
      by (auto simp add: indRelTEQ.encL)
    with A7 have "trans (indRelTEQ TRel \<union> {(P, Q). \<exists>S. \<lbrakk>S\<rbrakk> \<in>T P \<and> S \<in>S Q})"
        unfolding trans_def
      by blast
    ultimately show "SRel = {(S1, S2). SourceTerm S1 \<sim>\<lbrakk>\<cdot>\<rbrakk>T<TRel> SourceTerm S2}"
        using A1 A5 full_abstraction_and_trans_relation_contains_TRel_impl_SRel[where
                    SRel="SRel" and TRel="TRel" and Rel="indRelTEQ TRel"]
      by blast
  qed
  moreover from eqT A2 A3 have "strong_reduction_bisimulation (indRelTEQ TRel) (STCal Source Target)"
      using SOC_wrt_equivalence_iff_indRelTEQ_strong_reduction_bisimulation[where TRel="TRel"]
    by blast
  ultimately
  show "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
         \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
         \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
         \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
next
  assume
   "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel)
    \<and> SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}
    \<and> TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel} \<and> trans Rel
    \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
  from this obtain Rel where
       B1: "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel \<and> (TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
   and B2: "SRel = {(S1, S2). (SourceTerm S1, SourceTerm S2) \<in> Rel}"
   and B3: "TRel = {(T1, T2). (TargetTerm T1, TargetTerm T2) \<in> Rel}" and B4: "trans Rel"
   and B5: "strong_reduction_bisimulation Rel (STCal Source Target)"
    by blast
  from B1 B2 B3 B4 have "fully_abstract SRel TRel"
      using trans_source_target_relation_impl_fully_abstract[where Rel="Rel" and SRel="SRel"
            and TRel="TRel"]
    by blast
  moreover
  have "strongly_operational_corresponding TRel \<and> strong_reduction_bisimulation TRel Target"
  proof -
    from eqT have C1: "TRel\<^sup>+ = TRel"
        using trancl_id[of TRel]
        unfolding equiv_def refl_on_def
      by blast
    from eqT have C2: "TRel\<^sup>* = TRel"
        using reflcl_trancl[of TRel] trancl_id[of TRel]
        unfolding equiv_def refl_on_def
      by auto
    from B1 have "\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel"
      by simp
    moreover from B3 have "\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel"
      by simp
    moreover from B3 C1
    have "\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+"
      by simp
    moreover have "\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
    proof clarify
      fix S T
      from B1 have "(TargetTerm (\<lbrakk>S\<rbrakk>), SourceTerm S) \<in> Rel"
        by simp
      moreover assume "(SourceTerm S, TargetTerm T) \<in> Rel"
      ultimately have "(TargetTerm (\<lbrakk>S\<rbrakk>), TargetTerm T) \<in> Rel"
          using B4
          unfolding trans_def
        by blast
      with B3 C2 show "(\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*"
        by simp
    qed
    ultimately have "\<exists>Rel. (\<forall>S. (SourceTerm S, TargetTerm (\<lbrakk>S\<rbrakk>)) \<in> Rel)
     \<and> (\<forall>T1 T2. (T1, T2) \<in> TRel \<longrightarrow> (TargetTerm T1, TargetTerm T2) \<in> Rel)
     \<and> (\<forall>T1 T2. (TargetTerm T1, TargetTerm T2) \<in> Rel \<longrightarrow> (T1, T2) \<in> TRel\<^sup>+)
     \<and> (\<forall>S T. (SourceTerm S, TargetTerm T) \<in> Rel \<longrightarrow> (\<lbrakk>S\<rbrakk>, T) \<in> TRel\<^sup>*)
     \<and> strong_reduction_bisimulation Rel (STCal Source Target)"
           using B5
         by blast
    with C1 C2
    show "strongly_operational_corresponding TRel \<and> strong_reduction_bisimulation TRel Target"
        using SOC_iff_strong_reduction_bisimulation[where TRel="TRel"]
      by auto
  qed
  ultimately show "fully_abstract SRel TRel \<and> strongly_operational_corresponding TRel
                   \<and> strong_reduction_bisimulation TRel Target"
    by simp
qed

text \<open>An encoding that is fully abstract w.r.t. the equivalences SRel and TRel and operationally
        corresponding w.r.t. TRel ensures that SRel is a bisimulation iff TRel is a bisimulation.
\<close>

lemma (in encoding) FA_and_OC_and_TRel_impl_SRel_bisimulation:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and opCom:   "operational_complete TRel"
      and opSou:   "operational_sound TRel"
      and symmT:   "sym TRel"
      and transT:  "trans TRel"
      and bisimT:  "weak_reduction_bisimulation TRel Target"
  shows "weak_reduction_bisimulation SRel Source"
proof auto
  fix SP SQ SP'
  assume "SP \<longmapsto>Source* SP'"
  with opCom obtain TP' where A1: "\<lbrakk>SP\<rbrakk> \<longmapsto>Target* TP'" and A2: "(\<lbrakk>SP'\<rbrakk>, TP') \<in> TRel"
    by blast
  assume "(SP, SQ) \<in> SRel"
  with fullAbs have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    by simp
  with bisimT A1 obtain TQ' where A3: "\<lbrakk>SQ\<rbrakk> \<longmapsto>Target* TQ'" and A4: "(TP', TQ') \<in> TRel"
    by blast
  from A3 opSou obtain SQ' where A5: "SQ \<longmapsto>Source* SQ'" and A6: "(\<lbrakk>SQ'\<rbrakk>, TQ') \<in> TRel"
    by blast
  from A2 A4 A6 symmT transT have "(\<lbrakk>SP'\<rbrakk>, \<lbrakk>SQ'\<rbrakk>) \<in> TRel"
      unfolding trans_def sym_def
    by blast
  with fullAbs A5 show "\<exists>SQ'. SQ \<longmapsto>Source* SQ' \<and> (SP', SQ') \<in> SRel"
    by blast
next
  fix SP SQ SQ'
  assume "SQ \<longmapsto>Source* SQ'"
  with opCom obtain TQ' where B1: "\<lbrakk>SQ\<rbrakk> \<longmapsto>Target* TQ'" and B2: "(\<lbrakk>SQ'\<rbrakk>, TQ') \<in> TRel"
    by blast
  assume "(SP, SQ) \<in> SRel"
  with fullAbs have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    by simp
  with bisimT B1 obtain TP' where B3: "\<lbrakk>SP\<rbrakk> \<longmapsto>Target* TP'" and B4: "(TP', TQ') \<in> TRel"
    by blast
  from B3 opSou obtain SP' where B5: "SP \<longmapsto>Source* SP'" and B6: "(\<lbrakk>SP'\<rbrakk>, TP') \<in> TRel"
    by blast
  from B2 B4 B6 symmT transT have "(\<lbrakk>SP'\<rbrakk>, \<lbrakk>SQ'\<rbrakk>) \<in> TRel"
      unfolding trans_def sym_def
    by blast
  with fullAbs B5 show "\<exists>SP'. SP \<longmapsto>Source* SP' \<and> (SP', SQ') \<in> SRel"
    by blast
qed

lemma (in encoding) FA_and_SOC_and_TRel_impl_SRel_strong_bisimulation:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and opCom:   "strongly_operational_complete TRel"
      and opSou:   "strongly_operational_sound TRel"
      and symmT:   "sym TRel"
      and transT:  "trans TRel"
      and bisimT:  "strong_reduction_bisimulation TRel Target"
  shows "strong_reduction_bisimulation SRel Source"
proof auto
  fix SP SQ SP'
  assume "SP \<longmapsto>Source SP'"
  with opCom obtain TP' where A1: "\<lbrakk>SP\<rbrakk> \<longmapsto>Target TP'" and A2: "(\<lbrakk>SP'\<rbrakk>, TP') \<in> TRel"
    by blast
  assume "(SP, SQ) \<in> SRel"
  with fullAbs have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    by simp
  with bisimT A1 obtain TQ' where A3: "\<lbrakk>SQ\<rbrakk> \<longmapsto>Target TQ'" and A4: "(TP', TQ') \<in> TRel"
    by blast
  from A3 opSou obtain SQ' where A5: "SQ \<longmapsto>Source SQ'" and A6: "(\<lbrakk>SQ'\<rbrakk>, TQ') \<in> TRel"
    by blast
  from A2 A4 A6 symmT transT have "(\<lbrakk>SP'\<rbrakk>, \<lbrakk>SQ'\<rbrakk>) \<in> TRel"
      unfolding trans_def sym_def
    by blast
  with fullAbs A5 show "\<exists>SQ'. SQ \<longmapsto>Source SQ' \<and> (SP', SQ') \<in> SRel"
    by blast
next
  fix SP SQ SQ'
  assume "SQ \<longmapsto>Source SQ'"
  with opCom obtain TQ' where B1: "\<lbrakk>SQ\<rbrakk> \<longmapsto>Target TQ'" and B2: "(\<lbrakk>SQ'\<rbrakk>, TQ') \<in> TRel"
    by blast
  assume "(SP, SQ) \<in> SRel"
  with fullAbs have "(\<lbrakk>SP\<rbrakk>, \<lbrakk>SQ\<rbrakk>) \<in> TRel"
    by simp
  with bisimT B1 obtain TP' where B3: "\<lbrakk>SP\<rbrakk> \<longmapsto>Target TP'" and B4: "(TP', TQ') \<in> TRel"
    by blast
  from B3 opSou obtain SP' where B5: "SP \<longmapsto>Source SP'" and B6: "(\<lbrakk>SP'\<rbrakk>, TP') \<in> TRel"
    by blast
  from B2 B4 B6 symmT transT have "(\<lbrakk>SP'\<rbrakk>, \<lbrakk>SQ'\<rbrakk>) \<in> TRel"
      unfolding trans_def sym_def
    by blast
  with fullAbs B5 show "\<exists>SP'. SP \<longmapsto>Source SP' \<and> (SP', SQ') \<in> SRel"
    by blast
qed

lemma (in encoding) FA_and_OC_impl_SRel_iff_TRel_bisimulation:
  fixes SRel :: "('procS \<times> 'procS) set"
    and TRel :: "('procT \<times> 'procT) set"
  assumes fullAbs: "fully_abstract SRel TRel"
      and opCor:   "operational_corresponding TRel"
      and symmT:   "sym TRel"
      and transT:  "trans TRel"
      and surj:    "\<forall>T. \<exists>S. T = \<lbrakk>S\<rbrakk>"
  shows "weak_reduction_bisimulation SRel Source \<longleftrightarrow> weak_reduction_bisimulation TRel Target"
proof
  assume bisimS: "weak_reduction_bisimulation SRel Source"
  have "weak_reduction_simulation TRel Target"
  proof clarify
    fix TP TQ TP'
    from surj have "\<exists>S. TP = \<lbrakk>S\<rbrakk>"
      by simp
    from this obtain SP where A1: "\<lbrakk>SP\<rbrakk> = TP"
      by blast
    from surj have "\<exists>S. TQ = \<lbrakk>S\<rbrakk>"
      by simp
    from this obtain SQ where A2: "\<lbrakk>SQ\<rbrakk> = TQ"
      by blast
    assume "TP \<longmapsto>Target* TP'"
    with opCor A1 obtain SP' where A3: "SP \<longmapsto>Source* SP'" and A4: "(\<lbrakk>SP'\<rbrakk>, TP') \<in> TRel"
      by blast
    assume "(TP, TQ) \<in> TRel"
    with fullAbs A1 A2 have "(SP, SQ) \<in> SRel"
      by simp
    with bisimS A3 obtain SQ' where A5: "SQ \<longmapsto>Source* SQ'" and A6: "(SP', SQ') \<in> SRel"
      by blast
    from opCor A2 A5 obtain TQ' where A7: "TQ \<longmapsto>Target* TQ'" and A8: "(\<lbrakk>SQ'\<rbrakk>, TQ') \<in> TRel"
      by blast
    from symmT A4 have "(TP', \<lbrakk>SP'\<rbrakk>) \<in> TRel"
        unfolding sym_def
      by simp
    moreover from fullAbs A6 have "(\<lbrakk>SP'\<rbrakk>, \<lbrakk>SQ'\<rbrakk>) \<in> TRel"
      by simp
    ultimately have "(TP', TQ') \<in> TRel"
        using transT A8
        unfolding trans_def
      by blast
    with A7 show "\<exists>TQ'. TQ \<longmapsto>Target* TQ' \<and> (TP', TQ') \<in> TRel"
      by blast
  qed
  with symmT show "weak_reduction_bisimulation TRel Target"
      using symm_weak_reduction_simulation_is_bisimulation[where Rel="TRel" and Cal="Target"]
    by blast
next
  assume "weak_reduction_bisimulation TRel Target"
  with fullAbs opCor symmT transT show "weak_reduction_bisimulation SRel Source"
      using FA_and_OC_and_TRel_impl_SRel_bisimulation[where SRel="SRel" and TRel="TRel"]
    by blast
qed

end
