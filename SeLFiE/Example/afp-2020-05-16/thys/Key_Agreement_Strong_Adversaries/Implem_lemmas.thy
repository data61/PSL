(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Implem_lemmas.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Implem_lemmas.thy 132885 2016-12-23 18:41:32Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Auxiliary notions and lemmas for channel implementations.
  - message abstraction = inverse of (valid) impl, lifted to sets
  - extractable messages (those of non-confidential and "broken" channels)
  - lemmas for proving L2-L3 intruder refinement

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Lemmas Following from Channel Message Implementation Assumptions\<close>

theory Implem_lemmas
imports Implem
begin

text \<open>These lemmas require the assumptions added in the @{locale "valid_implem"} locale.\<close>

context semivalid_implem
begin
(**************************************************************************************************)
subsection \<open>Message implementations and abstractions\<close>
(**************************************************************************************************)

text \<open>Abstracting a set of messages into channel messages.\<close>

definition
  abs :: "msg set \<Rightarrow> chan set"
where
  "abs S \<equiv> {Chan x A B M | x A B M. M \<in> payload \<and> implem (Chan x A B M) \<in> S}"

lemma absE [elim]: 
  "\<lbrakk> X \<in> abs H;
     \<And> x A B M. X = Chan x A B M \<Longrightarrow> M \<in> payload \<Longrightarrow> implem X \<in> H \<Longrightarrow> P \<rbrakk>
  \<Longrightarrow> P"
by (auto simp add: abs_def)

lemma absI [intro]: "M \<in> payload \<Longrightarrow> implem (Chan x A B M) \<in> H \<Longrightarrow> Chan x A B M \<in> abs H"
by (auto simp add: abs_def)

lemma abs_mono: "G \<subseteq> H \<Longrightarrow> abs G \<subseteq> abs H"
by (auto simp add: abs_def)

lemmas abs_monotone [simp] = abs_mono [THEN [2] rev_subsetD]

lemma abs_empty [simp]: "abs {} = {}"
by (auto simp add: abs_def)

lemma abs_Un_eq: "abs (G \<union> H) = abs G \<union> abs H"
by (auto simp add: abs_def)

text \<open>General lemmas about implementations and @{term abs}.\<close>
lemma abs_insert_payload [simp]: "M \<in> payload \<Longrightarrow> abs (insert M S) = abs S"
by (auto simp add: abs_def)

lemma abs_insert_impl [simp]:
  "M \<in> payload \<Longrightarrow> abs (insert (implem (Chan x A B M)) S) = insert (Chan x A B M) (abs S)"
by (auto simp add: abs_def)

lemma extr_payload [simp, intro]:
  "\<lbrakk> X \<in> extr Bad NI (abs I); NI \<subseteq> payload \<rbrakk> \<Longrightarrow> X \<in> payload"
by (erule extr.induct, blast, auto)

lemma abs_Un_LtK:
  "K \<subseteq> range LtK \<Longrightarrow> abs (K \<union> S) = abs S"
by (auto simp add: abs_Un_eq)

lemma abs_Un_keys_of [simp]:
  "abs (keys_of A \<union> S) = abs S"
by (auto intro!: abs_Un_LtK)


text \<open>Lemmas about @{term valid} and @{term abs}\<close>

lemma abs_validSet: "abs (S \<inter> valid) = abs S"
by (auto elim: absE intro: validI)

lemma valid_abs: "M \<in> valid \<Longrightarrow> \<exists> M'. M' \<in> abs {M}"
by (auto elim: validE)


(**************************************************************************************************)
subsection \<open>Extractable messages\<close>
(**************************************************************************************************)

text \<open>\<open>extractable K I\<close>: subset of messages in $I$ which are implementations 
(not necessarily valid since we do not require that they are payload) and can be extracted 
using the keys in K. It corresponds to L2 @{term extr}.\<close>

definition
  extractable :: "msg set \<Rightarrow> msg set \<Rightarrow> msg set"
where
  "extractable K I \<equiv>
    {implInsec A B M | A B M. implInsec A B M \<in> I} \<union>
    {implAuth A B M | A B M. implAuth A B M \<in> I} \<union>
    {implConfid A B M | A B M. implConfid A B M \<in> I \<and> (A, B) \<in> broken K} \<union>
    {implSecure A B M | A B M. implSecure A B M \<in> I \<and> (A, B) \<in> broken K}"

lemma extractable_red: "extractable K I \<subseteq> I"
by (auto simp add: extractable_def)

lemma extractableI:
  "implem (Chan x A B M) \<in> I \<Longrightarrow>
   x = insec \<or> x = auth \<or> ((x = confid \<or> x = secure) \<and> (A, B) \<in> broken K) \<Longrightarrow>   
   implem (Chan x A B M) \<in> extractable K I"
by (auto simp add: extractable_def)

lemma extractableE:
  "X \<in> extractable K I \<Longrightarrow>
   (\<And>A B M. X = implInsec A B M \<Longrightarrow> X \<in> I \<Longrightarrow> P) \<Longrightarrow>
   (\<And>A B M. X = implAuth A B M \<Longrightarrow> X \<in> I \<Longrightarrow> P) \<Longrightarrow>
   (\<And>A B M. X = implConfid A B M \<Longrightarrow> X \<in> I \<Longrightarrow> (A, B) \<in> broken K \<Longrightarrow> P) \<Longrightarrow>
   (\<And>A B M. X = implSecure A B M \<Longrightarrow> X \<in> I \<Longrightarrow> (A, B) \<in> broken K \<Longrightarrow> P) \<Longrightarrow>
  P"
by (auto simp add: extractable_def brokenI)

text \<open>General lemmas about implementations and extractable.\<close>
lemma implem_extractable [simp]:
  "\<lbrakk> Keys_bad K Bad; implem (Chan x A B M) \<in> extractable K I; M \<in> payload \<rbrakk> 
 \<Longrightarrow> M \<in> extr Bad NI (abs I)"
by (erule extractableE, auto)


text \<open>Auxiliary lemmas about extractable messages: they are implementations.\<close>
lemma valid_extractable [simp]: "I \<subseteq> valid \<Longrightarrow> extractable K I \<subseteq> valid"
by (auto intro: subset_trans extractable_red del: subsetI)

lemma LtKeys_parts_extractable:
  "I \<subseteq> valid \<Longrightarrow> parts (extractable K I) \<inter> range LtK = {}"
by (auto dest: valid_extractable intro!: parts_valid_LtKeys_disjoint)

lemma LtKeys_parts_extractable_elt [simp]:  
  "I \<subseteq> valid \<Longrightarrow> LtK ltk \<notin> parts (extractable K I)"
by (blast dest: LtKeys_parts_extractable)


lemma LtKeys_parts_implSecureSet:   (* FIX: possibly problematic: not in normal form *)
  "parts (implSecureSet Ag payload) \<inter> range LtK = {}"
by (auto intro!: parts_valid_LtKeys_disjoint intro: validI)

lemma LtKeys_parts_implSecureSet_elt: 
  "LtK K \<notin> parts (implSecureSet Ag payload)"
using LtKeys_parts_implSecureSet
by auto

lemmas LtKeys_parts = LtKeys_parts_payload parts_valid_LtKeys_disjoint
                      LtKeys_parts_extractable LtKeys_parts_implSecureSet 
                      LtKeys_parts_implSecureSet_elt


subsubsection\<open>Partition $I$ to keep only the extractable messages\<close>
(**************************************************************************************************)

text \<open>Partition the implementation set.\<close>

lemma impl_partition:
  "\<lbrakk> NI \<subseteq> payload; I \<subseteq> valid \<rbrakk> \<Longrightarrow>
  I \<subseteq> extractable K I \<union>
      implConfidSet (UNIV - broken K) payload \<union>
      implSecureSet (UNIV - broken K) payload"
by (auto dest!: subsetD [where A=I] elim!: valid_cases intro:  extractableI)


subsubsection \<open>Partition of @{term "extractable"}\<close>
(**************************************************************************************************)

text \<open>We partition the @{term "extractable"} set into insecure, confidential, authentic 
implementations.\<close>

lemma extractable_partition:
  "\<lbrakk>Keys_bad K Bad; NI \<subseteq> payload; I \<subseteq> valid\<rbrakk> \<Longrightarrow>
  extractable K I \<subseteq> 
  implInsecSet (extr Bad NI (abs I)) \<union>
  implConfidSet UNIV (extr Bad NI (abs I)) \<union>
  implAuthSet (extr Bad NI (abs I)) \<union>
  implSecureSet UNIV (extr Bad NI (abs I))"
apply (rule, frule valid_extractable, drule subsetD [where A="extractable K I"], fast)
apply (erule valid_cases, auto)
done


(**************************************************************************************************)
subsection \<open>Lemmas for proving intruder refinement (L2-L3)\<close>
(**************************************************************************************************)

text \<open>Chain of lemmas used to prove the refinement for \<open>l3_dy\<close>. 
The ultimate goal is to show @{prop [display] 
  "synth (analz (NI \<union> I \<union> K \<union> Tags)) \<subseteq> synth (analz (extr Bad NI (abs I))) \<union> -payload"
}\<close>

subsubsection \<open>First: we only keep the extractable messages\<close>

\<comment> \<open>the \<open>synth\<close> is probably not needed\<close>
lemma analz_NI_I_K_analz_NI_EI:
assumes HNI: "NI \<subseteq> payload"
    and HK: "K \<subseteq> range LtK"
    and HI: "I \<subseteq> valid"
shows "analz (NI \<union> I \<union> K \<union> Tags) \<subseteq>
       synth (analz (NI \<union> extractable K I \<union> K \<union> Tags)) \<union> -payload"
proof -
  from HNI HI
  have "analz (NI \<union> I \<union> K \<union> Tags) \<subseteq> 
        analz (NI \<union> (extractable K I \<union>
                     implConfidSet (UNIV - broken K) payload \<union>
                     implSecureSet (UNIV - broken K) payload)
                \<union> K \<union> Tags)"
    by (intro analz_mono Un_mono impl_partition, simp_all)
  also have "... \<subseteq> analz (implConfidSet (UNIV - broken K) payload \<union>
                    (implSecureSet (UNIV - broken K) payload \<union>
                    (extractable K I \<union> NI \<union> K \<union> Tags)))"
    by (auto)
  also have "... \<subseteq> synth (analz (implSecureSet (UNIV - broken K) payload \<union>
                  (extractable K I \<union> NI \<union> K \<union> Tags))) \<union> -payload"
    proof (rule analz_Un_implConfidSet_2)
      show "Enc_keys_clean (implSecureSet (UNIV - broken K) payload 
                              \<union> (extractable K I \<union> NI \<union> K \<union> Tags))"
        by (auto simp add: HNI HI HK intro: validI)
    next
      from HK HI HNI 
      show "(UNIV - broken K) \<inter> 
            broken (parts (
              implSecureSet (UNIV - broken K) payload \<union>
              (extractable K I \<union> NI \<union> K \<union> Tags)) \<inter> range LtK)  = {}"
        by (auto simp add: LtKeys_parts 
               LtKeys_parts_implSecureSet_elt [where Ag="- broken K", simplified])
    qed (auto)
  also have "... \<subseteq> synth (analz (extractable K I \<union> NI \<union> K \<union> Tags)) \<union> -payload"
    proof (rule Un_least, rule synth_idem_payload)
      show "analz (implSecureSet (UNIV - broken K) payload \<union> 
                   (extractable K I \<union> NI \<union> K \<union> Tags))
            \<subseteq> synth (analz (extractable K I \<union> NI \<union> K \<union> Tags)) \<union> -payload"
        proof (rule analz_Un_implSecureSet_2)
          show "Enc_keys_clean (extractable K I \<union> NI \<union> K \<union> Tags)"
            using HNI HK HI by auto
        next  
          from HI HK HNI 
          show "(UNIV - broken K) \<inter> 
                broken (parts (extractable K I \<union> NI \<union> K \<union> Tags) \<inter> range LtK) = {}"
          by (auto simp add: LtKeys_parts)
        qed (auto)
    next
      show "-payload \<subseteq> synth (analz (extractable K I \<union> NI \<union> K \<union> Tags)) \<union> -payload"
        by auto
    qed
  also have "... \<subseteq> synth (analz (NI \<union> extractable K I \<union> K \<union> Tags)) \<union> -payload"
    by (simp add: sup.left_commute sup_commute)
  finally show ?thesis .
qed


subsubsection \<open>Only keep the extracted messages (instead of extractable)\<close>
(**************************************************************************************************)

lemma analz_NI_EI_K_synth_analz_NI_E_K:
assumes HNI: "NI \<subseteq> payload"
    and HK: "K \<subseteq> range LtK"
    and HI: "I \<subseteq> valid"
    and Hbad: "Keys_bad K Bad"
shows "analz (NI \<union> extractable K I \<union> K \<union> Tags)
    \<subseteq> synth (analz (extr Bad NI (abs I) \<union> K \<union> Tags)) \<union> -payload"
proof -
  from HNI HI Hbad
  have "analz (NI \<union> extractable K I \<union> K \<union> Tags) \<subseteq> 
        analz (NI \<union> (implInsecSet (extr Bad NI (abs I)) \<union>
                     implConfidSet UNIV (extr Bad NI (abs I)) \<union>
                     implAuthSet (extr Bad NI (abs I)) \<union>
                     implSecureSet UNIV (extr Bad NI (abs I))) \<union>
                    K \<union> Tags)"
    by (intro analz_mono Un_mono extractable_partition) (auto)

  also have "... \<subseteq> analz (implInsecSet (extr Bad NI (abs I)) \<union>
                     (implConfidSet UNIV (extr Bad NI (abs I)) \<union>
                     (implAuthSet (extr Bad NI (abs I)) \<union>
                     (implSecureSet UNIV (extr Bad NI (abs I)) \<union>
                     (NI \<union> K \<union> Tags)))))"
    by (auto)
  also have "... \<subseteq> synth (analz (extr Bad NI (abs I) \<union>
                   (implConfidSet UNIV (extr Bad NI (abs I)) \<union>
                   (implAuthSet (extr Bad NI (abs I)) \<union>
                   (implSecureSet UNIV (extr Bad NI (abs I)) \<union> (NI \<union> K \<union> Tags)))))) 
                 \<union> -payload"
    by (rule analz_Un_implInsecSet)
       (auto simp only: Un_commute [of "extr _ _ _" _] Un_assoc Un_absorb, 
        auto simp add: HNI HK HI intro!: validI)
  also have "... \<subseteq> synth (analz (extr Bad NI (abs I) \<union>
                   (implAuthSet (extr Bad NI (abs I)) \<union>
                   (implSecureSet UNIV (extr Bad NI (abs I)) \<union> (NI \<union> K \<union> Tags))))) 
                 \<union> -payload"
    proof (rule Un_least, rule synth_idem_payload)
      have "analz (implConfidSet UNIV (extr Bad NI (abs I)) \<union>
                   (implAuthSet (extr Bad NI (abs I)) \<union>
                   (implSecureSet UNIV (extr Bad NI (abs I)) \<union> 
                   (NI \<union> (K \<union> extr Bad NI (abs I) \<union> Tags)))))
            \<subseteq> synth (analz (extr Bad NI (abs I) \<union>
                           (implAuthSet (extr Bad NI (abs I)) \<union>
                           (implSecureSet UNIV (extr Bad NI (abs I)) \<union> 
                           (NI \<union> (K \<union> extr Bad NI (abs I) \<union> Tags)))))) 
              \<union> -payload"
        by (rule analz_Un_implConfidSet)
           (auto simp only: Un_commute [of "extr _ _ _" _] Un_assoc Un_absorb,
            auto simp add: HK HI HNI  intro!: validI)
      then show "analz (extr Bad NI (abs I) \<union>
                        (implConfidSet UNIV (extr Bad NI (abs I)) \<union>
                        (implAuthSet (extr Bad NI (abs I)) \<union>
                        (implSecureSet UNIV (extr Bad NI (abs I)) \<union> (NI \<union> K \<union> Tags)))))
                 \<subseteq> synth (analz (extr Bad NI (abs I) \<union>
                         (implAuthSet (extr Bad NI (abs I)) \<union>
                         (implSecureSet UNIV (extr Bad NI (abs I)) \<union> 
                         (NI \<union> K \<union> Tags))))) 
                   \<union> -payload"
        by (simp add: inf_sup_aci(6) inf_sup_aci(7))
    next
      show "-payload
            \<subseteq> synth (analz (extr Bad NI (abs I) \<union>
                           (implAuthSet (extr Bad NI (abs I)) \<union>
                           (implSecureSet UNIV (extr Bad NI (abs I)) \<union> (NI \<union> K \<union> Tags))))) 
              \<union> -payload"
        by blast
    qed
  also have "... \<subseteq> synth (analz (extr Bad NI (abs I) \<union>
                   (implSecureSet UNIV (extr Bad NI (abs I)) \<union> (NI \<union> K \<union> Tags)))) 
                 \<union> -payload"
    proof (rule Un_least, rule synth_idem_payload)
      have "analz (implAuthSet (extr Bad NI (abs I)) \<union>
                   (implSecureSet UNIV (extr Bad NI (abs I)) \<union> 
                   (NI \<union> (K \<union> (extr Bad NI (abs I) \<union> Tags)))))
            \<subseteq> synth (analz (extr Bad NI (abs I) \<union>
                           (implSecureSet UNIV (extr Bad NI (abs I)) \<union> 
                           (NI \<union> (K \<union> (extr Bad NI (abs I) \<union> Tags)))))) 
              \<union> -payload"
        by (rule analz_Un_implAuthSet)
           (auto simp only: Un_commute [of "extr _ _ _" _] Un_assoc Un_absorb,
            auto simp add: HI HNI HK intro!: validI)
      then show "analz (extr Bad NI (abs I) \<union>
                        (implAuthSet (extr Bad NI (abs I)) \<union>
                        (implSecureSet UNIV (extr Bad NI (abs I)) \<union> (NI \<union> K \<union> Tags))))
                 \<subseteq> synth (analz (extr Bad NI (abs I) \<union>
                         (implSecureSet UNIV (extr Bad NI (abs I)) \<union> 
                         (NI \<union> K \<union> Tags)))) 
                   \<union> -payload"
        by (simp add: inf_sup_aci(6) inf_sup_aci(7))
    next
      show "-payload
            \<subseteq> synth (analz (extr Bad NI (abs I) \<union>
                           (implSecureSet UNIV (extr Bad NI (abs I)) 
                            \<union> (NI \<union> K \<union> Tags))))  
              \<union> -payload"
        by blast
    qed
  also have "... \<subseteq> synth (analz (extr Bad NI (abs I) \<union> (NI \<union> K \<union> Tags))) 
                 \<union> -payload"
    proof (rule Un_least, rule synth_idem_payload)
      have "analz (implSecureSet UNIV (extr Bad NI (abs I)) \<union> 
                   (NI \<union> (K \<union> (extr Bad NI (abs I) \<union> Tags))))
            \<subseteq> synth (analz (extr Bad NI (abs I) \<union>
                           (NI \<union> (K \<union> (extr Bad NI (abs I) \<union> Tags))))) 
               \<union> -payload"
        by (rule analz_Un_implSecureSet)
           (auto simp only: Un_commute [of "extr _ _ _" _] Un_assoc Un_absorb,
            auto simp add: HI HNI HK intro!: validI)
      then show "analz (extr Bad NI (abs I) \<union>
                        (implSecureSet UNIV (extr Bad NI (abs I)) \<union> (NI \<union> K \<union> Tags)))
                 \<subseteq> synth (analz (extr Bad NI (abs I) \<union> (NI \<union> K \<union> Tags))) 
                   \<union> -payload"
        by (simp add: inf_sup_aci(6) inf_sup_aci(7))
    next
      show "-payload
            \<subseteq> synth (analz (extr Bad NI (abs I)\<union> (NI \<union> K \<union> Tags))) 
              \<union> -payload"
        by blast
    qed
  also have "... \<subseteq> synth (analz (extr Bad NI (abs I) \<union> K \<union> Tags)) \<union> -payload"
    by (metis IK_subset_extr inf_sup_aci(6) set_eq_subset sup.absorb1)
  finally show ?thesis .
qed


subsubsection \<open>Keys and Tags can be moved out of the @{term "analz"}\<close>

lemma analz_LtKeys_Tag:
assumes "NI \<subseteq> payload" and "K \<subseteq> range LtK"
shows "analz (NI \<union> K \<union> Tags) \<subseteq> analz NI \<union> K \<union> Tags"
proof 
  fix X
  assume H: "X \<in> analz (NI \<union> K \<union> Tags) "
  thus "X \<in> analz NI \<union> K \<union> Tags" 
  proof (induction X rule: analz.induct)
    case (Dec X Y) 
    hence "Enc X Y \<in> payload" using assms by auto
    moreover
    from Dec.IH(2) have "Y \<in> synth (analz NI \<union> (K \<union> Tags))"
      by (auto simp add: Collect_disj_eq dest!: synth_Int2 )
    ultimately show ?case using Dec.IH(1) assms(2) 
      by (auto dest!: synth_payload [THEN [2] rev_subsetD])
  next
    case (Adec_lt X Y)
    hence "Aenc X (pubK Y) \<in> payload \<union> range LtK \<union> Tags" using assms
      by auto
    then show ?case by auto
  next
    case (Sign_getmsg X Y)
    hence "Sign X (priK Y) \<in> payload \<union> range LtK \<union> Tags" using assms by auto
    then show ?case by auto
  next
    case (Adec_eph X Y)
    then show ?case using assms by (auto dest!: EpriK_synth)
  qed (insert assms, auto)
qed

lemma analz_NI_E_K_analz_NI_E:
  "\<lbrakk> NI \<subseteq> payload; K \<subseteq> range LtK; I \<subseteq> valid \<rbrakk> 
 \<Longrightarrow> analz (extr Bad NI (abs I) \<union> K \<union> Tags) \<subseteq> analz (extr Bad NI (abs I)) \<union> K \<union> Tags"
by (rule analz_LtKeys_Tag) auto


subsubsection \<open>Final lemmas, using all the previous ones\<close>
(**************************************************************************************************)

lemma analz_NI_I_K_synth_analz_NI_E:
assumes
  Hbad: "Keys_bad K Bad" and 
  HNI: "NI \<subseteq> payload" and 
  HK:  "K \<subseteq> range LtK" and 
  HI: "I \<subseteq> valid"
shows 
  "analz (NI \<union> I \<union> K \<union> Tags) \<subseteq> synth (analz (extr Bad NI (abs I))) \<union> -payload"
proof -
  from HNI HK HI have "analz (NI \<union> I \<union> K \<union> Tags) \<subseteq>
        synth (analz (NI \<union> extractable K I \<union> K \<union> Tags)) \<union> -payload"
    by (rule analz_NI_I_K_analz_NI_EI)
  also have "... \<subseteq> synth (analz (extr Bad NI (abs I) \<union> K \<union> Tags)) \<union> -payload"
    proof (rule Un_least, simp_all)
      from Hbad HNI HK HI have "analz (NI \<union> extractable K I \<union> K \<union> Tags) \<subseteq>
            synth (analz (extr Bad NI (abs I) \<union> K \<union> Tags)) \<union> -payload"
        by (intro analz_NI_EI_K_synth_analz_NI_E_K)
      then show "synth (analz (NI \<union> extractable K I \<union> K \<union> Tags)) \<subseteq>
                 synth (analz (extr Bad NI (abs I) \<union> K \<union> Tags)) \<union> -payload"
        by (rule synth_idem_payload)
    qed
  also have "... \<subseteq> synth (analz (extr Bad NI (abs I))) \<union> -payload"
    proof (rule Un_least, simp_all)
      from HNI HK HI have "analz (extr Bad NI (abs I) \<union> K \<union> Tags) \<subseteq>
                           analz (extr Bad NI (abs I)) \<union> K \<union> Tags"
        by (rule analz_NI_E_K_analz_NI_E)
      also from HK have "... \<subseteq> analz (extr Bad NI (abs I)) \<union> -payload"
        by auto
      also have "... \<subseteq> synth (analz (extr Bad NI (abs I))) \<union> -payload"
        by auto
      finally show "synth (analz (extr Bad NI (abs I) \<union> K \<union> Tags)) \<subseteq>
                  synth (analz (extr Bad NI (abs I))) \<union> -payload"
        by (rule synth_idem_payload)
    qed
  finally show ?thesis .
qed


text \<open>Lemma actually used to prove the refinement.\<close>
lemma synth_analz_NI_I_K_synth_analz_NI_E:
  "\<lbrakk> Keys_bad K Bad; NI \<subseteq> payload; K \<subseteq> range LtK; I \<subseteq> valid\<rbrakk>
 \<Longrightarrow> synth (analz (NI \<union> I \<union> K \<union> Tags)) 
   \<subseteq> synth (analz (extr Bad NI (abs I))) \<union> -payload"
by (intro synth_idem_payload analz_NI_I_K_synth_analz_NI_E) (assumption+)


subsubsection \<open>Partitioning @{term "analz (ik)"}\<close>
(**************************************************************************************************)
text \<open>Two lemmas useful for proving the invariant
  @{term [display] "analz ik \<subseteq> synth (analz (ik \<inter> payload \<union> ik \<inter> valid \<union> ik \<inter> range LtK \<union> Tags))"}
\<close>

lemma analz_Un_partition:
  "analz S \<subseteq> synth (analz ((S \<inter> payload) \<union> (S \<inter> valid) \<union> (S \<inter> range LtK) \<union> Tags)) \<Longrightarrow>
  H \<subseteq> payload \<union> valid \<union> range LtK \<Longrightarrow>
  analz (H \<union> S) \<subseteq>
    synth (analz (((H \<union> S) \<inter> payload) \<union> ((H \<union> S) \<inter> valid) \<union> ((H \<union> S) \<inter> range LtK) \<union> Tags))"
proof -
  assume "H \<subseteq> payload \<union> valid \<union> range LtK"
  then have HH:"H = (H \<inter> payload) \<union> (H \<inter> valid) \<union> (H \<inter> range LtK)"
    by auto
  assume HA:
    "analz S \<subseteq> synth (analz ((S \<inter> payload) \<union> (S \<inter> valid) \<union> (S \<inter> range LtK) \<union> Tags))"
  then have 
   "analz (H \<union> S) \<subseteq> 
    synth (analz (H \<union> ((S \<inter> payload) \<union> (S \<inter> valid) \<union> (S \<inter> range LtK) \<union> Tags)))"
    by (rule analz_synth_subset_Un2)
  also with HH have 
    "... \<subseteq> synth (analz (((H \<inter> payload) \<union> (H \<inter> valid) \<union> (H \<inter> range LtK)) \<union> 
                         ((S \<inter> payload) \<union> (S \<inter> valid) \<union> (S \<inter> range LtK) \<union> Tags)))"
    by auto
  also have "... = synth (analz (((H \<union> S) \<inter> payload) \<union> ((H \<union> S) \<inter> valid) \<union> 
                                 ((H \<union> S) \<inter> range LtK) \<union> Tags))"
    by (simp add: Un_left_commute sup.commute Int_Un_distrib2)
  finally show ?thesis .
qed

lemma analz_insert_partition:
  "analz S \<subseteq> synth (analz ((S \<inter> payload) \<union> (S \<inter> valid) \<union> (S \<inter> range LtK) \<union> Tags)) \<Longrightarrow>
  x \<in> payload \<union> valid \<union> range LtK \<Longrightarrow>
  analz (insert x S) \<subseteq>
    synth (analz (((insert x S) \<inter> payload) \<union> ((insert x S) \<inter> valid) \<union> 
                  ((insert x S) \<inter> range LtK) \<union> Tags))"
by (simp only: insert_is_Un [of x S], erule analz_Un_partition, auto)

end
end
