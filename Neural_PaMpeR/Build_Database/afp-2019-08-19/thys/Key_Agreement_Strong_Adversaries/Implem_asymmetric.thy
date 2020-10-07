(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Implem_asymmetric.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Implem_asymmetric.thy 132885 2016-12-23 18:41:32Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Asymmetric channel implementation (local interpretation) using
  public-key encryption and signatures.

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Asymmetric Implementation of Channel Messages\<close>

theory Implem_asymmetric
imports Implem
begin

(**************************************************************************************************)
subsection \<open>Implementation of channel messages\<close>
(**************************************************************************************************)

fun implem_asym :: "chan \<Rightarrow> msg" where
  "implem_asym (Insec A B M) = \<langle>InsecTag, Agent A, Agent B, M\<rangle>"
 |"implem_asym (Confid A B M) = Aenc \<langle>Agent A, M\<rangle> (pubK B)"
 |"implem_asym (Auth A B M) = Sign \<langle>Agent B, M\<rangle> (priK A)"
 |"implem_asym (Secure A B M) = Sign (Aenc \<langle>SecureTag, Agent A, M\<rangle> (pubK B)) (priK A)"


text \<open>
First step: @{locale "basic_implem"}. 
Trivial as there are no assumption, this locale just defines some useful abbreviations and valid.
\<close>
interpretation asym: basic_implem implem_asym
done


text \<open>Second step: @{locale "semivalid_implem"}.
Here we prove some basic properties such as injectivity and some properties about the 
interaction of sets of implementation messages with @{term analz}; these properties are 
proved as separate lemmas as the proofs are more complex. 
\<close>

text \<open>Auxiliary: simpler definitions of the \<open>implSets\<close> for the proofs, using the 
\<open>msgSet\<close> definitions. 
\<close>

abbreviation implInsecSet_aux :: "msg set \<Rightarrow> msg set"
where "implInsecSet_aux G \<equiv> PairSet Tags (PairSet AgentSet (PairSet AgentSet G))"

abbreviation implAuthSet_aux :: "msg set \<Rightarrow> msg set"
where "implAuthSet_aux G \<equiv> SignSet (PairSet AgentSet G) (range priK)"

abbreviation implConfidSet_aux :: "(agent * agent) set \<Rightarrow> msg set \<Rightarrow> msg set"
where "implConfidSet_aux Ag G \<equiv> AencSet (PairSet AgentSet G) (pubK` (Ag `` UNIV))"

abbreviation implSecureSet_aux :: "(agent * agent) set \<Rightarrow> msg set \<Rightarrow> msg set"
where "implSecureSet_aux Ag G \<equiv>
  SignSet (AencSet (PairSet Tags (PairSet AgentSet G)) (pubK` (Ag `` UNIV))) (range priK)"

text \<open>These auxiliary definitions are overapproximations.\<close>

lemma implInsecSet_implInsecSet_aux: "asym.implInsecSet G \<subseteq> implInsecSet_aux G"
by auto

lemma implAuthSet_implAuthSet_aux: "asym.implAuthSet G \<subseteq> implAuthSet_aux G"
by auto

lemma implConfidSet_implConfidSet_aux: "asym.implConfidSet Ag G \<subseteq> implConfidSet_aux Ag G"
by (auto, blast)

lemma implSecureSet_implSecureSet_aux: "asym.implSecureSet Ag G \<subseteq> implSecureSet_aux Ag G"
by (auto, blast)

lemmas implSet_implSet_aux =
  implInsecSet_implInsecSet_aux implAuthSet_implAuthSet_aux
  implConfidSet_implConfidSet_aux implSecureSet_implSecureSet_aux

declare Enc_keys_clean_msgSet_Un [intro]


(**************************************************************************************************)
subsection \<open>Lemmas to pull implementation sets out of @{term analz}\<close>
(**************************************************************************************************)

text \<open>
All these proofs are similar:
\begin{enumerate}
\item prove the lemma for the @{term "implSet_aux"} and with the set added outside of  
  @{term analz} given explicitly,
\item prove the lemma for the @{term "implSet_aux"} but with payload, and
\item prove the lemma for the @{term "implSet"}.
\end{enumerate}
There  are two cases for the confidential and secure messages:
the general case (the payloads stay in @{term  analz}) and the case where the key is unknown
(the messages cannot be opened and are completely removed from the @{term analz}).
\<close>


subsubsection \<open>Pull @{term PairAgentSet} out of \<open>analz\<close>\<close>
(**************************************************************************************************)

lemma analz_Un_PairAgentSet:
shows
  "analz (PairSet AgentSet G \<union> H) \<subseteq> PairSet AgentSet G \<union> AgentSet \<union> analz (G \<union> H)"
proof -
  have "analz (PairSet AgentSet G \<union> H) \<subseteq> PairSet AgentSet G \<union> analz (AgentSet \<union> G \<union> H)"
    by (rule analz_Un_PairSet)
  also have "... \<subseteq> PairSet AgentSet G \<union> AgentSet \<union> analz (G \<union> H)"
    apply (simp only: Un_assoc)
    apply (intro Un_mono analz_Un_AgentSet, fast)
    done 
  finally show ?thesis .
qed


subsubsection \<open>Pull @{term implInsecSet} out of @{term analz}\<close>
(**************************************************************************************************)

lemma analz_Un_implInsecSet_aux_aux:
assumes "Enc_keys_clean (G \<union> H)"
shows "analz (implInsecSet_aux G \<union> H) \<subseteq> implInsecSet_aux G \<union> Tags \<union> synth (analz (G \<union> H))"
proof -
   have "analz (implInsecSet_aux G \<union> H) \<subseteq> 
         implInsecSet_aux G \<union> analz (Tags \<union> PairSet AgentSet (PairSet AgentSet G) \<union> H)"
     by (rule analz_Un_PairSet)
   also have "... \<subseteq> implInsecSet_aux G \<union> Tags \<union> analz (PairSet AgentSet (PairSet AgentSet G) \<union> H)"
     using assms
     apply - 
     apply (simp only: Un_assoc, rule Un_mono, fast)
     apply (rule analz_Un_Tag, blast)
     done
   also have "... \<subseteq> implInsecSet_aux G \<union> Tags \<union> PairSet AgentSet (PairSet AgentSet G) \<union> AgentSet 
                     \<union> analz (PairSet AgentSet G \<union> H)"
     apply -
     apply (simp only: Un_assoc, (rule Un_mono, fast)+)
     apply (simp only: Un_assoc [symmetric], rule analz_Un_PairAgentSet)
     done
   also have 
     "... \<subseteq> implInsecSet_aux G \<union> Tags \<union> PairSet AgentSet (PairSet AgentSet G) \<union> AgentSet 
            \<union> PairSet AgentSet G \<union> AgentSet \<union> analz (G \<union> H)"
     apply -
     apply (simp only: Un_assoc, (rule Un_mono, fast)+)
     apply (simp only: Un_assoc [symmetric], rule analz_Un_PairAgentSet)
     done
   also have "... \<subseteq> implInsecSet_aux G \<union> Tags \<union> synth (analz (G \<union> H))"
     apply - 
     apply (simp only: Un_assoc, (rule Un_mono, fast)+, auto)
     done
   finally show ?thesis .
qed

lemma analz_Un_implInsecSet_aux:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implInsecSet_aux G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
by (rule subset_trans [OF analz_Un_implInsecSet_aux_aux], auto)

lemma analz_Un_implInsecSet:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (asym.implInsecSet G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
apply (rule subset_trans [of _ "analz (implInsecSet_aux G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
apply (blast dest: analz_Un_implInsecSet_aux)
done


subsection \<open>Pull @{term implConfidSet} out of @{term analz}\<close>
(**************************************************************************************************)

lemma analz_Un_implConfidSet_aux_aux:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
  analz (implConfidSet_aux Ag G \<union> H) \<subseteq> 
  implConfidSet_aux Ag G \<union> PairSet AgentSet G \<union>
  synth (analz (G \<union> H))"
apply (rule subset_trans [OF analz_Un_AencSet], blast, blast)
apply (simp only: Un_assoc, rule Un_mono, simp)
apply (rule subset_trans [OF analz_Un_PairAgentSet], blast)
done

lemma analz_Un_implConfidSet_aux:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
  analz (implConfidSet_aux Ag G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
by (rule subset_trans [OF analz_Un_implConfidSet_aux_aux], auto)

lemma analz_Un_implConfidSet:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (asym.implConfidSet Ag G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
apply (rule subset_trans [of _ "analz (implConfidSet_aux Ag G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implConfidSet_aux apply blast
done

text \<open>Pull @{term implConfidSet} out of @{term analz}, 2nd case where the agents are honest.\<close>

lemma analz_Un_implConfidSet_aux_aux_2:
  "Enc_keys_clean H \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (implConfidSet_aux Ag G \<union> H) \<subseteq> implConfidSet_aux Ag G \<union> synth (analz H)"
apply (rule subset_trans [OF analz_Un_AencSet2], simp)
apply (auto dest:analz_into_parts)
done

lemma analz_Un_implConfidSet_aux_2:
  "Enc_keys_clean H \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (implConfidSet_aux Ag G \<union> H) \<subseteq> synth (analz H) \<union> -payload"
by (rule subset_trans [OF analz_Un_implConfidSet_aux_aux_2], auto)

lemma analz_Un_implConfidSet_2:
  "Enc_keys_clean H \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (asym.implConfidSet Ag G \<union> H) \<subseteq> synth (analz H) \<union> -payload"
apply (rule subset_trans [of _ "analz (implConfidSet_aux Ag G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implConfidSet_aux_2 apply auto
done


subsection \<open>Pull @{term implAuthSet} out of @{term analz}\<close>
(**************************************************************************************************)

lemma analz_Un_implAuthSet_aux_aux:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implAuthSet_aux G \<union> H) \<subseteq> implAuthSet_aux G \<union> synth (analz (G \<union> H))"
apply (rule subset_trans [OF analz_Un_SignSet], blast, blast)
apply (rule Un_mono, blast)
apply (rule subset_trans [OF analz_Un_PairAgentSet], blast)
done

lemma analz_Un_implAuthSet_aux:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implAuthSet_aux G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
by (rule subset_trans [OF analz_Un_implAuthSet_aux_aux], auto)

lemma analz_Un_implAuthSet:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (asym.implAuthSet G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
apply (rule subset_trans [of _ "analz (implAuthSet_aux G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implAuthSet_aux apply blast
done


subsection \<open>Pull @{term implSecureSet} out of @{term analz}\<close>
(**************************************************************************************************)

lemma analz_Un_implSecureSet_aux_aux:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implSecureSet_aux Ag G \<union> H) \<subseteq>
   implSecureSet_aux Ag G \<union> AencSet (PairSet Tags (PairSet AgentSet G)) (pubK` (Ag`` UNIV)) \<union> 
   PairSet Tags (PairSet AgentSet G) \<union> Tags \<union> PairSet AgentSet G \<union>
   synth (analz (G \<union> H))"
apply (rule subset_trans [OF analz_Un_SignSet], blast, blast)
apply (simp only:Un_assoc, rule Un_mono, simp)
apply (rule subset_trans [OF analz_Un_AencSet], blast, blast)
apply (rule Un_mono, simp)
apply (rule subset_trans [OF analz_Un_PairSet], rule Un_mono, simp, simp only: Un_assoc)
apply (rule subset_trans [OF analz_Un_Tag], blast)
apply (rule Un_mono, simp)
apply (rule subset_trans [OF analz_Un_PairAgentSet], blast)
done

lemma analz_Un_implSecureSet_aux:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
  analz (implSecureSet_aux Ag G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
by (rule subset_trans [OF analz_Un_implSecureSet_aux_aux], auto)

lemma analz_Un_implSecureSet:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (asym.implSecureSet Ag G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
apply (rule subset_trans [of _ "analz (implSecureSet_aux Ag G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implSecureSet_aux apply blast
done

text \<open>
Pull @{term implSecureSet} out of @{term analz}, 2nd case, where the agents are honest. 
\<close>
lemma analz_Un_implSecureSet_aux_aux_2:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (implSecureSet_aux Ag G \<union> H) \<subseteq> 
   implSecureSet_aux Ag G \<union> AencSet (PairSet Tags (PairSet AgentSet G)) (pubK` (Ag`` UNIV)) \<union>
   synth (analz H)"
apply (rule subset_trans [OF analz_Un_SignSet], blast, blast)
apply (simp only: Un_assoc, rule Un_mono, simp)
apply (rule subset_trans [OF analz_Un_AencSet2], simp)
apply (auto dest: analz_into_parts)
done

lemma analz_Un_implSecureSet_aux_2:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (implSecureSet_aux Ag G \<union> H) \<subseteq> synth (analz H) \<union> -payload"
by (rule subset_trans [OF analz_Un_implSecureSet_aux_aux_2], auto)

lemma analz_Un_implSecureSet_2:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (asym.implSecureSet Ag G \<union> H) \<subseteq>
   synth (analz H) \<union> -payload"
apply (rule subset_trans [of _ "analz (implSecureSet_aux Ag G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implSecureSet_aux_2 apply auto
done

declare Enc_keys_clean_msgSet_Un [rule del]


subsection \<open>Locale interpretations\<close>
(**************************************************************************************************)

interpretation asym: semivalid_implem implem_asym
proof (unfold_locales)
  fix x A B M x' A' B' M'
  show "implem_asym (Chan x A B M) = implem_asym (Chan x' A' B' M') \<longleftrightarrow>
        x = x' \<and> A = A' \<and> B = B' \<and> M = M'"
    by (cases x, (cases x', auto)+)
next
  fix M' M x x' A A' B B'
  assume "M' \<in> payload" "implem_asym (Chan x A B M) \<in> parts {implem_asym (Chan x' A' B' M')}"
  then show "x = x' \<and> A = A' \<and> B = B' \<and> M = M'"
    by (cases "x", auto,(cases x', auto)+)
next
  fix I
  assume "I \<subseteq> asym.valid"
  then show "Enc_keys_clean I"
    proof (simp add: Enc_keys_clean_def, intro allI impI)
      fix X Y
      assume "Enc X Y \<in> parts I"
      obtain x A B M where "M \<in> payload" and "Enc X Y \<in> parts {implem_asym (Chan x A B M)}"
      using parts_singleton [OF \<open>Enc X Y \<in> parts I\<close>] \<open>I \<subseteq> asym.valid\<close>
        by (auto elim!: asym.validE)
      then show "Y \<in> range LtK \<or> Y \<in> payload" by (cases x, auto)
    qed
next
  fix Z
  show "composed (implem_asym Z)"
    proof (cases Z, simp)
      fix x A B M
      show "composed (implem_asym (Chan x A B M))" by (cases x, auto)
    qed
next
  fix x A B M
  show "implem_asym (Chan x A B M) \<notin> payload"
    by (cases x, auto)
next
  fix X K
  assume "X \<in> asym.valid"
  then obtain x A B M where "M \<in> payload" "X = implem_asym (Chan x A B M)" 
    by (auto elim: asym.validE)
  then show "LtK K \<notin> parts {X}"
  by (cases x, auto)
next
  fix G H
  assume "G \<subseteq> payload" "Enc_keys_clean H"
  hence "Enc_keys_clean (G \<union> H)" by (auto intro: Enc_keys_clean_Un)
  then show "analz ({implem_asym (Insec A B M) |A B M. M \<in> G} \<union> H) \<subseteq> 
               synth (analz (G \<union> H)) \<union> - payload"
    by (rule analz_Un_implInsecSet)
next
  fix G H
  assume "G \<subseteq> payload" "Enc_keys_clean H"
  hence "Enc_keys_clean (G \<union> H)" by (auto intro: Enc_keys_clean_Un)
  then show "analz ({implem_asym (Auth A B M) |A B M. M \<in> G} \<union> H) \<subseteq> 
               synth (analz (G \<union> H)) \<union> - payload"
    by (rule analz_Un_implAuthSet)
next
  fix G H Ag
  assume "G \<subseteq> payload" "Enc_keys_clean H"
  hence "Enc_keys_clean (G \<union> H)" by (auto intro: Enc_keys_clean_Un)
  then show "analz ({implem_asym (Confid A B M) |A B M. (A, B) \<in> Ag \<and> M \<in> G} \<union> H) \<subseteq> 
               synth (analz (G \<union> H)) \<union> - payload"
    by (rule analz_Un_implConfidSet)
next
  fix G H Ag
  assume "G \<subseteq> payload" "Enc_keys_clean H"
  hence "Enc_keys_clean (G \<union> H)" by (auto intro: Enc_keys_clean_Un)
  then show "analz ({implem_asym (Secure A B M) |A B M. (A, B) \<in> Ag \<and> M \<in> G} \<union> H) \<subseteq> 
               synth (analz (G \<union> H)) \<union> - payload"
    by (rule analz_Un_implSecureSet)
next
  fix G H Ag
  assume "G \<subseteq> payload" (*unused*)
  assume "Enc_keys_clean H"
  moreover assume "Ag \<inter> broken (parts H \<inter> range LtK) = {}"
  ultimately show "analz ({implem_asym (Confid A B M) |A B M. (A, B) \<in> Ag \<and> M \<in> G} \<union> H) \<subseteq> 
               synth (analz H) \<union> - payload"
    by (rule analz_Un_implConfidSet_2)
next
  fix G H Ag
  assume "G \<subseteq> payload" "Enc_keys_clean H"
  hence "Enc_keys_clean (G \<union> H)" by (auto intro: Enc_keys_clean_Un)
  moreover assume "Ag \<inter> broken (parts H \<inter> range LtK) = {}"
  ultimately 
    show "analz ({implem_asym (Secure A B M) |A B M. (A, B) \<in> Ag \<and> M \<in> G} \<union> H) \<subseteq> 
          synth (analz H) \<union> - payload"
    by (rule analz_Un_implSecureSet_2)
qed


text \<open>
Third step: @{locale "valid_implem"}. The lemmas giving conditions on $M$, $A$ and $B$ for 
@{prop [display] "implXXX A B M \<in> synth (analz Z)"}.
\<close>

lemma implInsec_synth_analz:
  "H \<subseteq> payload \<union> asym.valid \<union> range LtK \<union> Tags \<Longrightarrow>
   asym.implInsec A B M \<in> synth (analz H) \<Longrightarrow>
   asym.implInsec A B M \<in> I \<or> M \<in> synth (analz H)"
apply (erule synth.cases, auto)
done

lemma implConfid_synth_analz:
  "H \<subseteq> payload \<union> asym.valid \<union> range LtK \<union> Tags \<Longrightarrow>
   asym.implConfid A B M \<in> synth (analz H) \<Longrightarrow>
   asym.implConfid A B M \<in> H \<or> M \<in> synth (analz H)"
apply (erule synth.cases, auto)
apply (frule asym.analz_valid [where x=confid], auto)
done

lemma implAuth_synth_analz:
  "H \<subseteq> payload \<union> asym.valid \<union> range LtK \<union> Tags \<Longrightarrow>
   asym.implAuth A B M \<in> synth (analz H) \<Longrightarrow>
   asym.implAuth A B M \<in> H \<or> (M \<in> synth (analz H) \<and> (A, B) \<in> broken H)"
apply (erule synth.cases, auto)
apply (frule asym.analz_valid [where x=auth], auto)
apply (frule asym.analz_valid [where x=auth], auto)
apply (blast dest: asym.analz_LtKeys)
done

lemma implSecure_synth_analz:
  "H \<subseteq> payload \<union> asym.valid \<union> range LtK \<union> Tags \<Longrightarrow>
   asym.implSecure A B M \<in> synth (analz H) \<Longrightarrow>
   asym.implSecure A B M \<in> H \<or> (M \<in> synth (analz H) \<and> (A, B) \<in> broken H)"
proof (erule synth.cases, simp_all)
  fix X
  assume H:"H \<subseteq> payload \<union> asym.valid \<union> range LtK \<union> Tags"
  assume H':"Sign (Aenc \<langle>SecureTag, Agent A, M\<rangle> (pubK B)) (priK A) = X"
            " X \<in> analz H"
  hence "asym.implSecure A B M \<in> analz H" by auto
  with H have "asym.implSecure A B M \<in> H" by (rule asym.analz_valid)
  with H' show "X \<in> H \<or> M \<in> synth (analz H) \<and> (A, B) \<in> broken H"
    by auto
next
  fix X Y
  assume H:"H \<subseteq> payload \<union> asym.valid \<union> range LtK \<union> Tags"
  assume H':"Aenc \<langle>SecureTag, Agent A, M\<rangle> (pubK B) = X \<and> priK A = Y"
            "X \<in> synth (analz H)" "Y \<in> synth (analz H)"
  hence "priK A \<in> analz H" by auto
  with H have HAgents:"(A, B) \<in> broken H " by (auto dest: asym.analz_LtKeys)
  from H' have "Aenc \<langle>SecureTag, Agent A, M\<rangle> (pubK B) \<in> synth (analz H)" by auto
  then have "Aenc \<langle>SecureTag, Agent A, M\<rangle> (pubK B) \<in> analz H \<or> 
             M \<in> synth (analz H)"
    by (rule synth.cases, auto)
  then show "Sign X Y \<in> H \<or> M \<in> synth (analz H) \<and> (A, B) \<in> broken H"
    proof
      assume "M \<in> synth (analz H)"
      with HAgents show ?thesis by auto
    next
      assume "Aenc \<langle>SecureTag, Agent A, M\<rangle> (pubK B) \<in> analz H"
      hence "Aenc \<langle>SecureTag, Agent A, M\<rangle> (pubK B) \<in> parts H" by (rule analz_into_parts)
      from H obtain Z where 
        "Z \<in> H" and H'':"Aenc \<langle>SecureTag, Agent A, M\<rangle> (pubK B) \<in> parts {Z}"
        using parts_singleton [OF \<open>Aenc \<langle>SecureTag, Agent A, M\<rangle> (pubK B) \<in> parts H\<close>] 
        by blast
      moreover with H have "Z \<in> asym.valid" by (auto dest!: subsetD)
      moreover with H'' have "Z = asym.implSecure A B M"
        by (auto) (erule asym.valid_cases, auto)
      ultimately have "asym.implSecure A B M \<in> H" by auto
      with H' show ?thesis by auto
    qed
qed



interpretation asym: valid_implem implem_asym
proof (unfold_locales)
  fix H A B M
  assume "H \<subseteq> payload \<union> asym.valid \<union> range LtK \<union> Tags"
         "implem_asym (Insec A B M) \<in> synth (analz H)"
  then show "implem_asym (Insec A B M) \<in> H \<or> M \<in> synth (analz H)"
    by (rule implInsec_synth_analz)
next
  fix H A B M
  assume "H \<subseteq> payload \<union> asym.valid \<union> range LtK \<union> Tags"
         "implem_asym (Confid A B M) \<in> synth (analz H)"
  then show "implem_asym (Confid A B M) \<in> H \<or> M \<in> synth (analz H)"
    by (rule implConfid_synth_analz)
next
  fix H A B M
  assume "H \<subseteq> payload \<union> asym.valid \<union> range LtK \<union> Tags"
         "implem_asym (Auth A B M) \<in> synth (analz H)"
  then show "implem_asym (Auth A B M) \<in> H \<or> 
             M \<in> synth (analz H) \<and> (A, B) \<in> broken H"
    by (rule implAuth_synth_analz)
next
  fix H A B M
  assume "H \<subseteq> payload \<union> asym.valid \<union> range LtK \<union> Tags"
         "implem_asym (Secure A B M) \<in> synth (analz H)"
  then show "implem_asym (Secure A B M) \<in> H \<or> 
             M \<in> synth (analz H) \<and> (A, B) \<in> broken H"
    by (rule implSecure_synth_analz)
qed

end
