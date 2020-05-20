(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Implem_symmetric.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Implem_symmetric.thy 132885 2016-12-23 18:41:32Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Symmetric channel implementation (locale interpretation) using
  symmetric encryption and HMACs

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Symmetric Implementation of Channel Messages\<close>

theory Implem_symmetric
imports Implem
begin

(**************************************************************************************************)
subsection \<open>Implementation of channel messages\<close>
(**************************************************************************************************)

fun implem_sym :: "chan \<Rightarrow> msg" where
  "implem_sym (Insec A B M) = \<langle>InsecTag, Agent A, Agent B, M\<rangle>"
 |"implem_sym (Confid A B M) = Enc \<langle>ConfidTag, M\<rangle> (shrK A B)"
 |"implem_sym (Auth A B M) = \<langle>M, hmac \<langle>AuthTag, M\<rangle> (shrK A B)\<rangle>"
 |"implem_sym (Secure A B M) = Enc \<langle>SecureTag, M\<rangle> (shrK A B)"


text \<open>
First step: @{locale "basic_implem"}. 
Trivial as there are no assumption, this locale just defines some useful abbreviations and valid.
\<close>
interpretation sym: basic_implem implem_sym
done


text \<open>Second step: @{locale "semivalid_implem"}.
Here we prove some basic properties such as injectivity and some properties about the 
interaction of sets of implementation messages with @{term analz}; these properties are 
proved as separate lemmas as the proofs are more complex. 
\<close>

text \<open>Auxiliary: simpler definitions of the \<open>implSets\<close> for the proofs, using the 
\<open>msgSet\<close> definitions. 
\<close>

abbreviation implInsecSet_aux :: "msg set \<Rightarrow> msg set" where 
  "implInsecSet_aux G \<equiv> PairSet Tags (PairSet (range Agent) (PairSet (range Agent) G))"

abbreviation implAuthSet_aux :: "msg set \<Rightarrow> msg set" where 
  "implAuthSet_aux G \<equiv> PairSet G (HashSet (PairSet (PairSet Tags G) (range (case_prod shrK))))"

abbreviation implConfidSet_aux :: "(agent * agent) set \<Rightarrow> msg set \<Rightarrow> msg set" where 
  "implConfidSet_aux Ag G \<equiv> EncSet (PairSet Tags G) (case_prod shrK`Ag)"

abbreviation implSecureSet_aux :: "(agent * agent) set \<Rightarrow> msg set \<Rightarrow> msg set" where 
"implSecureSet_aux Ag G \<equiv> EncSet (PairSet Tags G) (case_prod shrK`Ag)"

text \<open>These auxiliary definitions are overapproximations.\<close>

lemma implInsecSet_implInsecSet_aux: "sym.implInsecSet G \<subseteq> implInsecSet_aux G"
by auto

lemma implAuthSet_implAuthSet_aux: "sym.implAuthSet G \<subseteq> implAuthSet_aux G"
by (auto, auto)

lemma implConfidSet_implConfidSet_aux: "sym.implConfidSet Ag G \<subseteq> implConfidSet_aux Ag G"
by (auto)

lemma implSecureSet_implSecureSet_aux: "sym.implSecureSet Ag G \<subseteq> implSecureSet_aux Ag G"
by (auto)

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


subsubsection \<open>Pull @{term implInsecSet} out of @{term analz}\<close>
(**************************************************************************************************)

lemma analz_Un_implInsecSet_aux_1:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implInsecSet_aux G \<union> H) \<subseteq> 
     implInsecSet_aux G \<union> Tags \<union>
     PairSet (range Agent) (PairSet (range Agent) G) \<union>
     PairSet (range Agent) G \<union>
     analz (range Agent \<union> G \<union> (range Agent \<union> H))"
proof -
  assume H:"Enc_keys_clean (G \<union> H)"
  have "analz (implInsecSet_aux G \<union> H) \<subseteq> implInsecSet_aux G \<union>
          analz (Tags \<union> PairSet (range Agent) (PairSet (range Agent) G) \<union> H)"
    by (rule analz_Un_PairSet)
  also have "... = implInsecSet_aux G \<union> 
            analz (Tags \<union> (PairSet (range Agent) (PairSet (range Agent) G) \<union> H))"
    by (simp only: Un_assoc)
  also have "... \<subseteq> implInsecSet_aux G \<union>
          (Tags \<union> analz (PairSet (range Agent) (PairSet (range Agent) G) \<union> H))"
    by (rule Un_mono, blast, rule analz_Un_Tag, blast intro: H)
  also have "... = implInsecSet_aux G \<union> Tags \<union>
                  analz (PairSet (range Agent) (PairSet (range Agent) G) \<union> H)"
    by auto
  also have "... \<subseteq> implInsecSet_aux G \<union> Tags \<union> (PairSet (range Agent) (PairSet (range Agent) G) \<union>
                  analz (range Agent \<union> PairSet (range Agent) G \<union> H))"
    by (rule Un_mono, blast, rule analz_Un_PairSet)
  also have "... = implInsecSet_aux G \<union> Tags \<union> PairSet (range Agent) (PairSet (range Agent) G) \<union>
                  analz (PairSet (range Agent) G \<union> (range Agent \<union> H))"
    by (auto simp add: Un_assoc Un_commute)
  also have "... \<subseteq> implInsecSet_aux G \<union> Tags \<union> PairSet (range Agent) (PairSet (range Agent) G) \<union>
                  (PairSet (range Agent) G \<union> analz (range Agent \<union> G \<union> (range Agent \<union> H)))"
    by (rule Un_mono, blast, rule analz_Un_PairSet)
  also have "... = implInsecSet_aux G \<union> Tags \<union> (PairSet (range Agent) (PairSet (range Agent) G) \<union>
                  PairSet (range Agent) G) \<union> analz (range Agent \<union> G \<union> (range Agent \<union> H))"
    by (simp only: Un_assoc Un_commute)
   finally show ?thesis by auto
qed

lemma analz_Un_implInsecSet_aux_2:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implInsecSet_aux G \<union> H) \<subseteq> 
     implInsecSet_aux G \<union> Tags \<union> 
     synth (analz (G \<union> H))"
proof -
  assume H:"Enc_keys_clean (G \<union> H)"
  have HH:"PairSet (range Agent) (PairSet (range Agent) G) \<union>
                  PairSet (range Agent) G \<subseteq> synth (analz (G \<union> H))"
    by auto
  have HHH:"analz (range Agent \<union> G \<union> (range Agent \<union> H)) \<subseteq> synth (analz (G \<union> H))"
    proof -
      have "analz (range Agent \<union> G \<union> (range Agent \<union> H)) \<subseteq> 
            synth (analz (range Agent \<union> G \<union> (range Agent \<union> H)))"
        by auto
      also have "... = synth (analz (synth (range Agent \<union> G \<union> (range Agent \<union> H))))" by auto
      also have "... \<subseteq> synth (analz (synth (G \<union> H)))"
        proof (rule synth_analz_mono)
          have "range Agent \<union> G \<union> (range Agent \<union> H) \<subseteq> synth (G \<union> H)" by auto
          then have "synth (range Agent \<union> G \<union> (range Agent \<union> H)) \<subseteq> synth (synth (G \<union> H))"
            by (rule synth_mono)
          then show "synth (range Agent \<union> G \<union> (range Agent \<union> H)) \<subseteq> synth (G \<union> H)" by auto
        qed
      also have "... = synth (analz (G \<union> H))" by auto
      finally show ?thesis .
    qed
  from H have 
   "analz (implInsecSet_aux G \<union> H) \<subseteq>  
      implInsecSet_aux G \<union> Tags \<union> PairSet (range Agent) (PairSet (range Agent) G) \<union>
      PairSet (range Agent) G \<union> analz (range Agent \<union> G \<union> (range Agent \<union> H))"
    by (rule analz_Un_implInsecSet_aux_1)
  also have "... = implInsecSet_aux G \<union> Tags \<union> 
                   (PairSet (range Agent) (PairSet (range Agent) G) \<union>
                   PairSet (range Agent) G) \<union> analz (range Agent \<union> G \<union> (range Agent \<union> H))"
    by (simp only: Un_assoc Un_commute)
  also have "... \<subseteq> implInsecSet_aux G \<union> Tags \<union> synth (analz (G \<union> H)) \<union> 
                    synth (analz (G \<union> H))"
     by ((rule Un_mono)+, auto simp add: HH HHH)
  finally show ?thesis by auto
qed

lemma analz_Un_implInsecSet_aux_3:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implInsecSet_aux G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
by (rule subset_trans [OF analz_Un_implInsecSet_aux_2], auto)

lemma analz_Un_implInsecSet:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (sym.implInsecSet G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
apply (rule subset_trans [of _ "analz (implInsecSet_aux G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implInsecSet_aux_3 apply blast
done


subsection \<open>Pull @{term implConfidSet} out of @{term analz}\<close>
(**************************************************************************************************)

lemma analz_Un_implConfidSet_aux_1:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implConfidSet_aux Ag G \<union> H) \<subseteq> 
     implConfidSet_aux Ag G \<union> PairSet Tags G \<union> Tags \<union>
     analz (G \<union> H)"
proof -
  assume H:"Enc_keys_clean (G \<union> H)"
  have "analz (implConfidSet_aux Ag G \<union> H) \<subseteq> 
        implConfidSet_aux Ag G \<union> analz (PairSet Tags G \<union> H)"
    by (rule analz_Un_EncSet, fast, blast intro: H)
  also have "... \<subseteq> implConfidSet_aux Ag G \<union> (PairSet Tags G \<union> analz (Tags \<union> G \<union> H))"
    by (rule Un_mono, blast, rule analz_Un_PairSet)
  also have "... = implConfidSet_aux Ag G \<union> PairSet Tags G \<union> analz (Tags \<union> (G \<union> H))"
    by (simp only: Un_assoc)
  also have "... \<subseteq> implConfidSet_aux Ag G \<union> PairSet Tags G \<union> (Tags \<union> analz (G \<union> H))"
    by (rule Un_mono, blast, rule analz_Un_Tag, blast intro: H)
   finally show ?thesis by auto
qed

lemma analz_Un_implConfidSet_aux_2:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implConfidSet_aux Ag G \<union> H) \<subseteq> 
     implConfidSet_aux Ag G \<union> PairSet Tags G \<union> Tags \<union>
     synth (analz (G \<union> H))"
proof -
  assume H:"Enc_keys_clean (G \<union> H)"
  from H have "analz (implConfidSet_aux Ag G \<union> H) \<subseteq> 
                implConfidSet_aux Ag G \<union> PairSet Tags G \<union> Tags \<union> analz (G \<union> H)"
    by (rule analz_Un_implConfidSet_aux_1)
  also have "... \<subseteq> implConfidSet_aux Ag G \<union> PairSet Tags G \<union> Tags \<union> synth (analz (G \<union> H))"
     by auto
  finally show ?thesis by auto
qed

lemma analz_Un_implConfidSet_aux_3:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
  analz (implConfidSet_aux Ag G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
by (rule subset_trans [OF analz_Un_implConfidSet_aux_2], auto)

lemma analz_Un_implConfidSet:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (sym.implConfidSet Ag G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
apply (rule subset_trans [of _ "analz (implConfidSet_aux Ag G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implConfidSet_aux_3 apply blast
done

text \<open>Pull @{term implConfidSet} out of @{term analz}, 2nd case where the agents are honest.\<close>

lemma analz_Un_implConfidSet_2_aux_1:
  "Enc_keys_clean H \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (implConfidSet_aux Ag G \<union> H) \<subseteq> implConfidSet_aux Ag G \<union> synth (analz H)"
apply (rule subset_trans [OF analz_Un_EncSet2], simp)
apply (auto dest:analz_into_parts)
done

lemma analz_Un_implConfidSet_2_aux_3:
  "Enc_keys_clean H \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (implConfidSet_aux Ag G \<union> H) \<subseteq> synth (analz H) \<union> -payload"
by (rule subset_trans [OF analz_Un_implConfidSet_2_aux_1], auto)

lemma analz_Un_implConfidSet_2:
  "Enc_keys_clean H \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (sym.implConfidSet Ag G \<union> H) \<subseteq> synth (analz H) \<union> -payload"
apply (rule subset_trans [of _ "analz (implConfidSet_aux Ag G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implConfidSet_2_aux_3 apply auto
done


subsection \<open>Pull @{term implSecureSet} out of @{term analz}\<close>
(**************************************************************************************************)

lemma analz_Un_implSecureSet_aux_1:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implSecureSet_aux Ag G \<union> H) \<subseteq> 
     implSecureSet_aux Ag G \<union> PairSet Tags G \<union> Tags \<union>
     analz (G \<union> H)"
proof -
  assume H:"Enc_keys_clean (G \<union> H)"
  have "analz (implSecureSet_aux Ag G \<union> H) \<subseteq> 
        implSecureSet_aux Ag G \<union> analz (PairSet Tags G \<union> H)"
    by (rule analz_Un_EncSet, fast, blast intro: H)
  also have "... \<subseteq> implSecureSet_aux Ag G \<union> (PairSet Tags G \<union> analz (Tags \<union> G \<union> H))"
    by (rule Un_mono, blast, rule analz_Un_PairSet)
  also have "... = implSecureSet_aux Ag G \<union> PairSet Tags G \<union> analz (Tags \<union> (G \<union> H))"
    by (simp only: Un_assoc)
  also have "... \<subseteq> implSecureSet_aux Ag G \<union> PairSet Tags G \<union> (Tags \<union> analz (G \<union> H))"
    by (rule Un_mono, blast, rule analz_Un_Tag, blast intro: H)
   finally show ?thesis by auto
qed

lemma analz_Un_implSecureSet_aux_2:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implSecureSet_aux Ag G \<union> H) \<subseteq> 
     implSecureSet_aux Ag G \<union> PairSet Tags G \<union> Tags \<union>
     synth (analz (G \<union> H))"
proof -
  assume H:"Enc_keys_clean (G \<union> H)"
  from H have "analz (implSecureSet_aux Ag G \<union> H) \<subseteq> 
                implSecureSet_aux Ag G \<union> PairSet Tags G \<union> Tags \<union> analz (G \<union> H)"
    by (rule analz_Un_implSecureSet_aux_1)
  also have "... \<subseteq> implSecureSet_aux Ag G \<union> PairSet Tags G \<union> Tags \<union> synth (analz (G \<union> H))"
     by auto
  finally show ?thesis by auto
qed

lemma analz_Un_implSecureSet_aux_3:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
  analz (implSecureSet_aux Ag G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
by (rule subset_trans [OF analz_Un_implSecureSet_aux_2], auto)

lemma analz_Un_implSecureSet:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (sym.implSecureSet Ag G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
apply (rule subset_trans [of _ "analz (implSecureSet_aux Ag G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implSecureSet_aux_3 apply blast
done

text \<open>
Pull @{term implSecureSet} out of @{term analz}, 2nd case, where the agents are honest. 
\<close>
lemma analz_Un_implSecureSet_2_aux_1:
  "Enc_keys_clean H \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (implSecureSet_aux Ag G \<union> H) \<subseteq> implSecureSet_aux Ag G \<union> synth (analz H)"
apply (rule subset_trans [OF analz_Un_EncSet2], simp)
apply (auto dest:analz_into_parts)
done

lemma analz_Un_implSecureSet_2_aux_3:
  "Enc_keys_clean H \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (implSecureSet_aux Ag G \<union> H) \<subseteq> synth (analz H) \<union> -payload"
by (rule subset_trans [OF analz_Un_implSecureSet_2_aux_1], auto)

lemma analz_Un_implSecureSet_2:
  "Enc_keys_clean H \<Longrightarrow>
   Ag \<inter> broken (parts H \<inter> range LtK) = {} \<Longrightarrow>
   analz (sym.implSecureSet Ag G \<union> H) \<subseteq> synth (analz H) \<union> -payload"
apply (rule subset_trans [of _ "analz (implSecureSet_aux Ag G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implSecureSet_2_aux_3 apply auto
done


subsection \<open>Pull @{term implAuthSet} out of @{term analz}\<close>
(**************************************************************************************************)

lemma analz_Un_implAuthSet_aux_1:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implAuthSet_aux G \<union> H) \<subseteq> 
     implAuthSet_aux G \<union> HashSet (PairSet (PairSet Tags G) (range (case_prod shrK))) \<union>
     analz (G \<union> H)"
proof -
  assume H:"Enc_keys_clean (G \<union> H)"
  have "analz (implAuthSet_aux G \<union> H) \<subseteq> implAuthSet_aux G \<union>
          analz (G \<union> HashSet (PairSet (PairSet Tags G) (range (case_prod shrK))) \<union> H)"
    by (rule analz_Un_PairSet)
  also have "... = implAuthSet_aux G \<union>
          analz (HashSet (PairSet (PairSet Tags G) (range (case_prod shrK))) \<union> G \<union> H)"
    by (simp only: Un_assoc Un_commute)
  also have "... = implAuthSet_aux G \<union>
          analz (HashSet (PairSet (PairSet Tags G) (range (case_prod shrK))) \<union> (G \<union> H))"
    by (simp only: Un_assoc)
  also have 
    "... \<subseteq> implAuthSet_aux G \<union> 
            (HashSet (PairSet (PairSet Tags G) (range (case_prod shrK))) \<union>
             analz (G \<union> H))"
    by (rule Un_mono, blast, rule analz_Un_HashSet, blast intro: H, auto)
  also have "... = implAuthSet_aux G \<union> 
                   HashSet (PairSet (PairSet Tags G) (range (case_prod shrK))) \<union>
                   analz (G \<union> H)"
    by auto
   finally show ?thesis by auto
qed

lemma analz_Un_implAuthSet_aux_2:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (implAuthSet_aux G \<union> H) \<subseteq>
     implAuthSet_aux G \<union> HashSet (PairSet (PairSet Tags G) (range (case_prod shrK))) \<union>
     synth (analz (G \<union> H))"
proof -
  assume H:"Enc_keys_clean (G \<union> H)"
  from H have 
    "analz (implAuthSet_aux G \<union> H) \<subseteq> 
       implAuthSet_aux G \<union> 
       HashSet (PairSet (PairSet Tags G) (range (case_prod shrK))) \<union>
       analz (G \<union> H)"
    by (rule analz_Un_implAuthSet_aux_1)
  also have 
    "... \<subseteq> implAuthSet_aux G \<union> 
            HashSet (PairSet (PairSet Tags G) (range (case_prod shrK))) \<union>
            synth (analz (G \<union> H))"
     by auto
  finally show ?thesis by auto
qed

lemma analz_Un_implAuthSet_aux_3:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
  analz (implAuthSet_aux G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
by (rule subset_trans [OF analz_Un_implAuthSet_aux_2], auto)

lemma analz_Un_implAuthSet:
  "Enc_keys_clean (G \<union> H) \<Longrightarrow>
   analz (sym.implAuthSet G \<union> H) \<subseteq> synth (analz (G \<union> H)) \<union> -payload"
apply (rule subset_trans [of _ "analz (implAuthSet_aux G \<union> H)" _])
apply (rule analz_mono, rule Un_mono, blast intro!: implSet_implSet_aux, simp)
using analz_Un_implAuthSet_aux_3 apply blast
done

declare Enc_keys_clean_msgSet_Un [rule del]


subsection \<open>Locale interpretations\<close>
(**************************************************************************************************)

interpretation sym: semivalid_implem implem_sym
proof (unfold_locales)
  fix x A B M x' A' B' M'
  show "implem_sym (Chan x A B M) = implem_sym (Chan x' A' B' M') \<longleftrightarrow>
        x = x' \<and> A = A' \<and> B = B' \<and> M = M'"
    by (cases x, (cases x', auto)+)
next
  fix M' M x x' A A' B B'
  assume H: "M' \<in> payload"
  then have A1: "\<And>y. y \<in> parts {M'} \<Longrightarrow> y \<in> payload" 
        and A2: "\<And>y. M' = y \<Longrightarrow> y \<in> payload" by auto
  assume "implem_sym (Chan x A B M) \<in> parts {implem_sym (Chan x' A' B' M')}"
  then show "x = x' \<and> A = A' \<and> B = B' \<and> M = M'"
    by (cases "x", (cases x', auto dest!: A1 A2)+)
next
  fix I
  assume "I \<subseteq> sym.valid"
  then show "Enc_keys_clean I"
    proof (simp add: Enc_keys_clean_def, intro allI impI)
      fix X Y
      assume "Enc X Y \<in> parts I"
      obtain x A B M where "M \<in> payload" and "Enc X Y \<in> parts {implem_sym (Chan x A B M)}"
      using parts_singleton [OF \<open>Enc X Y \<in> parts I\<close>] \<open>I \<subseteq> sym.valid\<close>
        by (auto elim!: sym.validE)
      then show "Y \<in> range LtK \<or> Y \<in> payload" by (cases x, auto)
    qed
next
  fix Z
  show "composed (implem_sym Z)"
    proof (cases Z, simp)
      fix x A B M
      show "composed (implem_sym (Chan x A B M))" by (cases x, auto)
    qed
next
  fix x A B M
  show "implem_sym (Chan x A B M) \<notin> payload"
    by (cases x, auto)
next
  fix X K
  assume "X \<in> sym.valid"
  then obtain x A B M where "M \<in> payload" "X = implem_sym (Chan x A B M)" 
    by (auto elim: sym.validE)
  then show "LtK K \<notin> parts {X}"
  by (cases x, auto)

next
  fix G H
  assume "G \<subseteq> payload" "Enc_keys_clean H"
  hence "Enc_keys_clean (G \<union> H)" by (auto intro: Enc_keys_clean_Un)
  then show "analz ({implem_sym (Insec A B M) |A B M. M \<in> G} \<union> H) \<subseteq> 
               synth (analz (G \<union> H)) \<union> - payload"
    by (rule analz_Un_implInsecSet)
next
  fix G H
  assume "G \<subseteq> payload" "Enc_keys_clean H"
  hence "Enc_keys_clean (G \<union> H)" by (auto intro: Enc_keys_clean_Un)
  then show "analz ({implem_sym (Auth A B M) |A B M. M \<in> G} \<union> H) \<subseteq> 
               synth (analz (G \<union> H)) \<union> - payload"
    by (rule analz_Un_implAuthSet)
next
  fix G H Ag
  assume "G \<subseteq> payload" "Enc_keys_clean H"
  hence "Enc_keys_clean (G \<union> H)" by (auto intro: Enc_keys_clean_Un)
  then show "analz ({implem_sym (Confid A B M) |A B M. (A, B) \<in> Ag \<and> M \<in> G} \<union> H) \<subseteq> 
               synth (analz (G \<union> H)) \<union> - payload"
    by (rule analz_Un_implConfidSet)
next
  fix G H Ag
  assume "G \<subseteq> payload" "Enc_keys_clean H"
  hence "Enc_keys_clean (G \<union> H)" by (auto intro: Enc_keys_clean_Un)
  then show "analz ({implem_sym (Secure A B M) |A B M. (A, B) \<in> Ag \<and> M \<in> G} \<union> H) \<subseteq> 
               synth (analz (G \<union> H)) \<union> - payload"
    by (rule analz_Un_implSecureSet)
next
  fix G H Ag
  assume "Enc_keys_clean H"
  hence "Enc_keys_clean H" by auto
  moreover assume "Ag \<inter> broken (parts H \<inter> range LtK) = {}"
  ultimately show "analz ({implem_sym (Confid A B M) |A B M. (A, B) \<in> Ag \<and> M \<in> G} \<union> H) \<subseteq> 
               synth (analz H) \<union> - payload"
    by (rule analz_Un_implConfidSet_2)
next
  fix G H Ag
  assume "Enc_keys_clean H"
  moreover assume "Ag \<inter> broken (parts H \<inter> range LtK) = {}"
  ultimately show "analz ({implem_sym (Secure A B M) |A B M. (A, B) \<in> Ag \<and> M \<in> G} \<union> H) \<subseteq> 
               synth (analz H) \<union> - payload"
    by (rule analz_Un_implSecureSet_2)
qed

text \<open>
Third step: @{locale "valid_implem"}.
The lemmas giving conditions on $M$, $A$ and $B$ for 
@{prop "implXXX A B M \<in> synth (analz Z)"}.
\<close>

lemma implInsec_synth_analz:
  "H \<subseteq> payload \<union> sym.valid \<union> range LtK \<union> Tags \<Longrightarrow>
   sym.implInsec A B M \<in> synth (analz H) \<Longrightarrow>
   sym.implInsec A B M \<in> H \<or> M \<in> synth (analz H)"
apply (erule synth.cases, auto)
done

lemma implConfid_synth_analz:
  "H \<subseteq> payload \<union> sym.valid \<union> range LtK \<union> Tags \<Longrightarrow>
   sym.implConfid A B M \<in> synth (analz H) \<Longrightarrow>
   sym.implConfid A B M \<in> H \<or> M \<in> synth (analz H)"
apply (erule synth.cases, auto)
\<comment> \<open>1 subgoal\<close>
apply (frule sym.analz_valid [where x=confid], auto)
done

lemma implAuth_synth_analz:
  "H \<subseteq> payload \<union> sym.valid \<union> range LtK \<union> Tags \<Longrightarrow>
   sym.implAuth A B M \<in> synth (analz H) \<Longrightarrow>
   sym.implAuth A B M \<in> H \<or> (M \<in> synth (analz H) \<and> (A, B) \<in> broken H)"
proof (erule synth.cases, simp_all)
  fix X
  assume H:  "H \<subseteq> payload \<union> sym.valid \<union> range LtK \<union> Tags"
  assume H':"\<langle>M, hmac \<langle>AuthTag, M\<rangle> (shrK A B)\<rangle> = X" " X \<in> analz H"
  hence "sym.implAuth A B M \<in> analz H" by auto
  with H have "sym.implAuth A B M \<in> H" by (rule sym.analz_valid)
  with H' show "X \<in> H \<or> M \<in> synth (analz H) \<and> (A, B) \<in> broken H"
    by auto
next
  fix X Y
  assume H:"H \<subseteq> payload \<union> sym.valid \<union> range LtK \<union> Tags"
  assume H':"M = X \<and> hmac \<langle>AuthTag, M\<rangle> (shrK A B) = Y" "Y \<in> synth (analz H)"
  hence "hmac \<langle>AuthTag, M\<rangle> (shrK A B) \<in> synth (analz H)" by auto
  then have "hmac \<langle>AuthTag, M\<rangle> (shrK A B) \<in> analz H \<or> 
             shrK A B \<in> synth (analz H)"
    by (rule synth.cases, auto)
  then show "\<langle>X, hmac \<langle>AuthTag, X\<rangle> (shrK A B)\<rangle> \<in> H \<or> (A, B) \<in> broken H"
    proof
      assume "shrK A B \<in> synth (analz H)"
      with H have "(A, B) \<in> broken H" by (auto dest:sym.analz_LtKeys)
      then show ?thesis by auto
    next
      assume "hmac \<langle>AuthTag, M\<rangle> (shrK A B) \<in> analz H"
      hence "hmac \<langle>AuthTag, M\<rangle> (shrK A B) \<in> parts H" by (rule analz_into_parts)
      with H have "hmac \<langle>AuthTag, M\<rangle> (shrK A B) \<in> parts H" 
        by (auto dest!:payload_parts elim!:payload_Hash)
      from H obtain Z where "Z \<in> H" and H'':"hmac \<langle>AuthTag, M\<rangle> (shrK A B) \<in> parts {Z}"
        using parts_singleton [OF \<open>hmac \<langle>AuthTag, M\<rangle> (shrK A B) \<in> parts H\<close>] by blast
      moreover with H have "Z \<in> sym.valid" by (auto dest!: subsetD)
      moreover with H'' have "Z = sym.implAuth A B M"
        by (auto) (erule sym.valid_cases, auto)
      ultimately have "sym.implAuth A B M \<in> H" by auto
      with H' show ?thesis by auto
    qed
qed

lemma implSecure_synth_analz:
  "H \<subseteq> payload \<union> sym.valid \<union> range LtK \<union> Tags \<Longrightarrow>
   sym.implSecure A B M \<in> synth (analz H) \<Longrightarrow>
   sym.implSecure A B M \<in> H \<or> (M \<in> synth (analz H) \<and> (A, B) \<in> broken H)"
apply (erule synth.cases, auto)
(* 1 subgoal*)
apply (frule sym.analz_valid [where x=secure], auto)
apply (frule sym.analz_valid [where x=secure], auto)
apply (auto dest:sym.analz_LtKeys)
done


interpretation sym: valid_implem implem_sym
proof (unfold_locales)
  fix H A B M
  assume "H \<subseteq> payload \<union> sym.valid \<union> range LtK \<union> Tags"
         "implem_sym (Insec A B M) \<in> synth (analz H)"
  then show "implem_sym (Insec A B M) \<in> H \<or> M \<in> synth (analz H)"
    by (rule implInsec_synth_analz)
next
  fix H A B M
  assume "H \<subseteq> payload \<union> sym.valid \<union> range LtK \<union> Tags"
         "implem_sym (Confid A B M) \<in> synth (analz H)"
  then show "implem_sym (Confid A B M) \<in> H \<or> M \<in> synth (analz H)"
    by (rule implConfid_synth_analz)
next
  fix H A B M
  assume "H \<subseteq> payload \<union> sym.valid \<union> range LtK \<union> Tags"
         "implem_sym (Auth A B M) \<in> synth (analz H)"
  then show "implem_sym (Auth A B M) \<in> H \<or> 
             M \<in> synth (analz H) \<and> (A, B) \<in> broken H"
    by (rule implAuth_synth_analz)
next
  fix H A B M
  assume "H \<subseteq> payload \<union> sym.valid \<union> range LtK \<union> Tags"
         "implem_sym (Secure A B M) \<in> synth (analz H)"
  then show "implem_sym (Secure A B M) \<in> H \<or> 
             M \<in> synth (analz H) \<and> (A, B) \<in> broken H"
    by (rule implSecure_synth_analz)
qed

end
