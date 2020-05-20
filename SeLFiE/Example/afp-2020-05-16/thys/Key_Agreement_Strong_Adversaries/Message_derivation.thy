(*******************************************************************************

  Project: Refining Authenticated Key Agreement with Strong Adversaries

  Module:  Message_derivation.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Message_derivation.thy 132885 2016-12-23 18:41:32Z csprenge $
  Author:  Joseph Lallemand, INRIA Nancy <joseph.lallemand@loria.fr>
           Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  A theory of message derivations (analz, synth, parts).
  Based on Larry Paulson's theory HOL/Auth/Message.thy, but extended with
  - composed keys
  - including ephemeral asymmetric keys
  - Diffie-Hellman exponentiation and associated equational theory

  Copyright (c) 2015-2016 Joseph Lallemand and Christoph Sprenger
  Licence: LGPL

*******************************************************************************)

section \<open>Message theory\<close> 

theory Message_derivation
imports Messages
begin

text \<open>This theory is adapted from Larry Paulson's original Message theory.\<close>


(****************************************************************************************)
subsection \<open>Message composition\<close>
(****************************************************************************************)

text \<open>Dolev-Yao message synthesis.\<close>

inductive_set
  synth :: "msg set \<Rightarrow> msg set"   
  for H :: "msg set"
  where
    Ax [intro]: "X \<in> H \<Longrightarrow> X \<in> synth H"
  | Agent [simp, intro]: "Agent A \<in> synth H"
  | Number [simp, intro]: "Number n \<in> synth H"
  | NonceA [simp, intro]: "NonceA n \<in> synth H"
  | EpubKA [simp, intro]: "epubKA n \<in> synth H"
  | EpriKA [simp, intro]: "epriKA n \<in> synth H"
  | Hash [intro]: "X \<in> synth H \<Longrightarrow> Hash X \<in> synth H"
  | Pair [intro]: "X \<in> synth H \<Longrightarrow> Y \<in> synth H \<Longrightarrow> (Pair X Y) \<in> synth H"
  | Enc [intro]: "X \<in> synth H \<Longrightarrow> Y \<in> synth H \<Longrightarrow> (Enc X Y) \<in> synth H"
  | Aenc [intro]: "X \<in> synth H \<Longrightarrow> Y \<in> synth H \<Longrightarrow> (Aenc X Y) \<in> synth H"
  | Sign [intro]: "X \<in> synth H \<Longrightarrow> Y \<in> synth H \<Longrightarrow> Sign X Y \<in> synth H"
  | Exp [intro]: "X \<in> synth H \<Longrightarrow> Y \<in> synth H \<Longrightarrow> (Exp X Y) \<in> synth H"


text \<open>Lemmas about Dolev-Yao message synthesis.\<close>

lemma synth_mono [mono_set]: "G \<subseteq> H \<Longrightarrow> synth G \<subseteq> synth H"
  by (auto, erule synth.induct, auto) 

lemmas synth_monotone = synth_mono [THEN [2] rev_subsetD]

\<comment> \<open>\<open>[elim!]\<close> slows down certain proofs, e.g., \<open>\<lbrakk> synth H \<inter> B \<subseteq> {} \<rbrakk> \<Longrightarrow> P\<close>\<close>
inductive_cases NonceF_synth: "NonceF n \<in> synth H"
inductive_cases LtK_synth: "LtK K \<in> synth H"
inductive_cases EpubKF_synth: "epubKF K \<in> synth H"
inductive_cases EpriKF_synth: "epriKF K \<in> synth H"
inductive_cases Hash_synth: "Hash X \<in> synth H"
inductive_cases Pair_synth: "Pair X Y \<in> synth H"
inductive_cases Enc_synth: "Enc X K \<in> synth H"
inductive_cases Aenc_synth: "Aenc X K \<in> synth H"
inductive_cases Sign_synth: "Sign X K \<in> synth H"
inductive_cases Tag_synth: "Tag t \<in> synth H"

lemma EpriK_synth [elim]: "epriK K \<in> synth H \<Longrightarrow>
       epriK K \<in> H \<or> (\<exists> N. epriK K = epriKA N)"
by (cases K, auto elim: EpriKF_synth)

lemma EpubK_synth [elim]: "epubK K \<in> synth H \<Longrightarrow>
       epubK K \<in> H \<or> (\<exists> N. epubK K = epubKA N)"
by (cases K, auto elim: EpubKF_synth)

lemmas synth_inversion [elim] = 
  NonceF_synth LtK_synth EpubKF_synth EpriKF_synth Hash_synth Pair_synth 
  Enc_synth Aenc_synth Sign_synth Tag_synth


lemma synth_increasing: "H \<subseteq> synth H"
by blast

lemma synth_Int1: "x \<in> synth (A \<inter> B) \<Longrightarrow> x \<in> synth A "
  by (erule synth.induct) (auto)

lemma synth_Int2: "x \<in> synth (A \<inter> B) \<Longrightarrow> x \<in> synth B"
  by (erule synth.induct) (auto)

lemma synth_Int: "x \<in> synth (A \<inter> B) \<Longrightarrow> x \<in> synth A \<inter> synth B"
  by (blast intro: synth_Int1 synth_Int2)

lemma synth_Un: "synth G \<union> synth H \<subseteq> synth (G \<union> H)"
by (intro Un_least synth_mono Un_upper1 Un_upper2)

lemma synth_insert: "insert X (synth H) \<subseteq> synth (insert X H)"
by (blast intro: synth_mono [THEN [2] rev_subsetD])

lemma synth_synthD [dest!]: "X \<in> synth (synth H) \<Longrightarrow> X \<in> synth H"
by (erule synth.induct, blast+)

lemma synth_idem [simp]: "synth (synth H) = synth H"
by blast

lemma synth_subset_iff: "synth G \<subseteq> synth H \<longleftrightarrow> G \<subseteq> synth H"
by (blast dest: synth_mono)

lemma synth_trans: "\<lbrakk> X \<in> synth G; G \<subseteq> synth H \<rbrakk> \<Longrightarrow> X \<in> synth H"
by (drule synth_mono, blast)

lemma synth_cut: "\<lbrakk> Y \<in> synth (insert X H); X \<in> synth H \<rbrakk> \<Longrightarrow> Y \<in> synth H"
by (erule synth_trans, blast)


lemma Nonce_synth_eq [simp]: "(NonceF N \<in> synth H) = (NonceF N \<in> H)"
by blast

lemma LtK_synth_eq [simp]: "(LtK K \<in> synth H) = (LtK K \<in> H)"
by blast

lemma EpubKF_synth_eq [simp]: "(epubKF K \<in> synth H) = (epubKF K \<in> H)"
by blast

lemma EpriKF_synth_eq [simp]: "(epriKF K \<in> synth H) = (epriKF K \<in> H)"
by blast

lemma Enc_synth_eq1 [simp]:
     "K \<notin> synth H \<Longrightarrow> (Enc X K \<in> synth H) = (Enc X K \<in> H)"
by blast

lemma Enc_synth_eq2 [simp]:
     "X \<notin> synth H \<Longrightarrow> (Enc X K \<in> synth H) = (Enc X K \<in> H)"
by blast

lemma Aenc_synth_eq1 [simp]:
     "K \<notin> synth H \<Longrightarrow> (Aenc X K \<in> synth H) = (Aenc X K \<in> H)"
by blast

lemma Aenc_synth_eq2 [simp]:
     "X \<notin> synth H \<Longrightarrow> (Aenc X K \<in> synth H) = (Aenc X K \<in> H)"
by blast

lemma Sign_synth_eq1 [simp]:
     "K \<notin> synth H \<Longrightarrow> (Sign X K \<in> synth H) = (Sign X K \<in> H)"
by blast

lemma Sign_synth_eq2 [simp]:
     "X \<notin> synth H \<Longrightarrow> (Sign X K \<in> synth H) = (Sign X K \<in> H)"
by blast

(****************************************************************************************)
subsection \<open>Message decomposition\<close>
(****************************************************************************************)

text \<open>Dolev-Yao message decomposition using known keys.\<close>

inductive_set
  analz :: "msg set \<Rightarrow> msg set"
  for H :: "msg set"
  where
    Ax [intro]: "X \<in> H \<Longrightarrow> X \<in> analz H"
  | Fst: "Pair X Y \<in> analz H \<Longrightarrow> X \<in> analz H"
  | Snd: "Pair X Y \<in> analz H \<Longrightarrow> Y \<in> analz H"
  | Dec [dest]: 
      "\<lbrakk> Enc X Y \<in> analz H; Y \<in> synth (analz H) \<rbrakk> \<Longrightarrow> X \<in> analz H"
  | Adec_lt [dest]: 
      "\<lbrakk> Aenc X (LtK (publK Y)) \<in> analz H; priK Y \<in> analz H \<rbrakk> \<Longrightarrow> X \<in> analz H"
  | Adec_eph [dest]: 
      "\<lbrakk> Aenc X (EphK (epublK Y)) \<in> analz H; epriK Y \<in> synth (analz H) \<rbrakk> \<Longrightarrow> X \<in> analz H"
  | Sign_getmsg [dest]: 
      "Sign X (priK Y) \<in> analz H \<Longrightarrow> pubK Y \<in> analz H \<Longrightarrow> X \<in> analz H"


text \<open>Lemmas about Dolev-Yao message decomposition.\<close>

lemma analz_mono: "G \<subseteq> H \<Longrightarrow> analz(G) \<subseteq> analz(H)"
by (safe, erule analz.induct) (auto dest: Fst Snd synth_Int2)

lemmas analz_monotone = analz_mono [THEN [2] rev_subsetD]


lemma Pair_analz [elim!]:
  "\<lbrakk> Pair X Y \<in> analz H; \<lbrakk> X \<in> analz H; Y \<in> analz H \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by (blast dest: analz.Fst analz.Snd)


lemma analz_empty [simp]: "analz {} = {}"
by (safe, erule analz.induct) (blast+)

lemma analz_increasing: "H \<subseteq> analz(H)"
by auto

lemma analz_analzD [dest!]: "X \<in> analz (analz H) \<Longrightarrow> X \<in> analz H"
by (induction X rule: analz.induct) (auto dest: synth_monotone)

lemma analz_idem [simp]: "analz (analz H) = analz H"
by auto


lemma analz_Un: "analz G \<union> analz H \<subseteq> analz (G \<union> H)"
by (intro Un_least analz_mono Un_upper1 Un_upper2)

lemma analz_insertI: "X \<in> analz H \<Longrightarrow> X \<in> analz (insert Y H)"
by (blast intro: analz_monotone)

lemma analz_insert: "insert X (analz H) \<subseteq> analz (insert X H)"
by (blast intro: analz_monotone)

lemmas analz_insert_eq_I = equalityI [OF subsetI analz_insert]


lemma analz_subset_iff [simp]: "analz G \<subseteq> analz H \<longleftrightarrow> G \<subseteq> analz H"
by (blast dest: analz_mono)

lemma analz_trans: "X \<in> analz G \<Longrightarrow>  G \<subseteq> analz H \<Longrightarrow> X \<in> analz H"
by (drule analz_mono) blast

lemma analz_cut: "Y \<in> analz (insert X H) \<Longrightarrow>  X \<in> analz H \<Longrightarrow> Y \<in> analz H"
by (erule analz_trans) blast

lemma analz_insert_eq: "X \<in> analz H \<Longrightarrow> analz (insert X H) = analz H"
by (blast intro: analz_cut analz_insertI)


lemma analz_subset_cong:
  "analz G \<subseteq> analz G' \<Longrightarrow>
   analz H \<subseteq> analz H' \<Longrightarrow> 
   analz (G \<union> H) \<subseteq> analz (G' \<union> H')"
apply simp
apply (iprover intro: conjI subset_trans analz_mono Un_upper1 Un_upper2) 
done

lemma analz_cong:
  "analz G = analz G' \<Longrightarrow>
   analz H = analz H' \<Longrightarrow>
   analz (G \<union> H) = analz (G' \<union> H')"
by (intro equalityI analz_subset_cong, simp_all) 

lemma analz_insert_cong:
  "analz H = analz H' \<Longrightarrow>
   analz (insert X H) = analz (insert X H')"
by (force simp only: insert_def intro!: analz_cong)

lemma analz_trivial:
  "\<forall>X Y. Pair X Y \<notin> H \<Longrightarrow>
   \<forall>X Y. Enc X Y \<notin> H \<Longrightarrow>
   \<forall>X Y. Aenc X Y \<notin> H \<Longrightarrow>
   \<forall>X Y. Sign X Y \<notin> H \<Longrightarrow>
   analz H = H"
apply safe
apply (erule analz.induct, blast+)
done


lemma analz_analz_Un [simp]: "analz (analz G \<union> H) = analz (G \<union> H)"
apply (intro equalityI analz_subset_cong)+
apply simp_all
done

lemma analz_Un_analz [simp]: "analz (G \<union> analz H) = analz (G \<union> H)"
by (subst Un_commute, auto)+


text \<open>Lemmas about analz and insert.\<close> 

lemma analz_insert_Agent [simp]:
  "analz (insert (Agent A) H) = insert (Agent A) (analz H)"
apply (rule analz_insert_eq_I) 
apply (erule analz.induct)
thm analz.induct
apply fastforce
apply fastforce
apply fastforce
defer 1
apply fastforce
defer 1
apply fastforce

apply (rename_tac x X Y)
apply (subgoal_tac "Y \<in> synth (analz H)", auto)
apply (thin_tac "Enc X Y \<in> Z" for Z)+
apply (drule synth_Int2, auto)
apply (erule synth.induct, auto)

apply (rename_tac X Y)
apply (subgoal_tac "epriK Y \<in> synth (analz H)", auto)
apply (thin_tac "Aenc X (epubK Y) \<in> Z" for Z)+
apply (erule synth.induct, auto)
done



(****************************************************************************************)
subsection \<open>Lemmas about combined composition/decomposition\<close>
(****************************************************************************************)

lemma synth_analz_incr: "H \<subseteq> synth (analz H)"
by auto

lemmas synth_analz_increasing = synth_analz_incr [THEN [2] rev_subsetD] 

lemma synth_analz_mono: "G \<subseteq> H \<Longrightarrow> synth (analz G) \<subseteq> synth (analz H)"
by (blast intro!: analz_mono synth_mono)

lemmas synth_analz_monotone = synth_analz_mono [THEN [2] rev_subsetD]

lemma lem1: 
  "Y \<in> synth (analz (synth G \<union> H) \<inter> (analz (G \<union> H) \<union> synth G)) 
\<Longrightarrow> Y \<in> synth (analz (G \<union> H))"
apply (rule subsetD, auto simp add: synth_subset_iff intro: analz_increasing synth_monotone)
done

lemma lem2: "{a. a \<in> analz (G \<union> H) \<or> a \<in> synth G} = analz (G \<union> H) \<union> synth G" by auto

lemma analz_synth_Un: "analz (synth G \<union> H) = analz (G \<union> H) \<union> synth G"
proof (intro equalityI subsetI)
  fix x
  assume "x \<in> analz (synth G \<union> H)" 
  thus "x \<in> analz (G \<union> H) \<union> synth G"
  by (induction x rule: analz.induct)
     (auto simp add: lem2 intro: analz_monotone Fst Snd Dec Adec_eph Adec_lt Sign_getmsg 
           dest: lem1)
next 
  fix x
  assume "x \<in> analz (G \<union> H) \<union> synth G" 
  thus "x \<in> analz (synth G \<union> H)" 
    by (blast intro: analz_monotone) 
qed


lemma analz_synth: "analz (synth H) = analz H \<union> synth H"
by (rule analz_synth_Un [where H="{}", simplified])


lemma analz_synth_Un2 [simp]: "analz (G \<union> synth H) = analz (G \<union> H) \<union> synth H"
by (subst Un_commute, auto simp add: analz_synth_Un)+


lemma synth_analz_synth [simp]: "synth (analz (synth H)) = synth (analz H)"
by (auto del:subsetI) (auto simp add: synth_subset_iff analz_synth)

lemma analz_synth_analz [simp]: "analz (synth (analz H)) = synth (analz H)"
by (auto simp add: analz_synth)

lemma synth_analz_idem [simp]: "synth (analz (synth (analz H))) = synth (analz H)"
by (simp only: analz_synth_analz) simp


lemma insert_subset_synth_analz [simp]: 
  "X \<in> synth (analz H) \<Longrightarrow> insert X H \<subseteq> synth (analz H)"
by auto


lemma synth_analz_insert [simp]: 
  assumes "X \<in> synth (analz H)"
  shows "synth (analz (insert X H)) = synth (analz H)"
using assms
proof (intro equalityI subsetI)
  fix Z
  assume "Z \<in> synth (analz (insert X H))"
  hence "Z \<in> synth (analz (synth (analz H)))" using assms 
    by - (erule synth_analz_monotone, rule insert_subset_synth_analz)
  thus "Z \<in> synth (analz H)" using assms by simp
qed (auto intro: synth_analz_monotone)


(****************************************************************************************)
subsection \<open>Accessible message parts\<close>
(****************************************************************************************)

text \<open>Accessible message parts: all subterms that are in principle extractable
by the Dolev-Yao attacker, i.e., provided he knows all keys. Note that keys in
key positions and messages under hashes are not message parts in this sense.\<close>

inductive_set
  parts :: "msg set => msg set"
  for H :: "msg set"
where
    Inj [intro]: "X \<in> H \<Longrightarrow> X \<in> parts H"
  | Fst [intro]: "Pair X Y \<in> parts H \<Longrightarrow> X \<in> parts H"
  | Snd [intro]: "Pair X Y \<in> parts H \<Longrightarrow> Y \<in> parts H"
  | Dec [intro]: "Enc X Y \<in> parts H \<Longrightarrow> X \<in> parts H"
  | Adec [intro]: "Aenc X Y \<in> parts H \<Longrightarrow> X \<in> parts H"
  | Sign_getmsg [intro]: "Sign X Y \<in> parts H \<Longrightarrow> X \<in> parts H"


text \<open>Lemmas about accessible message parts.\<close>

lemma parts_mono [mono_set]: "G \<subseteq> H \<Longrightarrow> parts G \<subseteq> parts H"
by (auto, erule parts.induct, auto)

lemmas parts_monotone = parts_mono [THEN [2] rev_subsetD]


lemma Pair_parts [elim]:
  "\<lbrakk> Pair X Y \<in> parts H; \<lbrakk> X \<in> parts H; Y \<in> parts H \<rbrakk> \<Longrightarrow> P \<rbrakk> \<Longrightarrow> P"
by blast 


lemma parts_increasing: "H \<subseteq> parts H"
by blast

lemmas parts_insertI = subset_insertI [THEN parts_mono, THEN subsetD]

lemma parts_empty [simp]: "parts {} = {}"
by (safe, erule parts.induct, auto)

lemma parts_atomic [simp]: "atomic x \<Longrightarrow> parts {x} = {x}"
by (auto, erule parts.induct, auto)
 
lemma parts_InsecTag [simp]: "parts {Tag t} = {Tag t}" 
by (safe, erule parts.induct) (auto)

lemma parts_emptyE [elim!]: "X \<in> parts {} \<Longrightarrow> P"
by simp

lemma parts_Tags [simp]:
  "parts Tags = Tags"
by (rule, rule, erule parts.induct, auto) 

lemma parts_singleton: "X \<in> parts H \<Longrightarrow> \<exists> Y\<in>H. X \<in> parts {Y}"
by (erule parts.induct, blast+)

lemma parts_Agents [simp]:
  "parts (Agent` G) = Agent` G"
by (auto elim: parts.induct)

lemma parts_Un [simp]: "parts (G \<union> H) = parts G \<union> parts H"
proof 
  show "parts (G \<union> H) \<subseteq> parts G \<union> parts H"
    by (rule, erule parts.induct) (auto)
next 
  show "parts G \<union> parts H \<subseteq> parts (G \<union> H)" 
    by (intro Un_least parts_mono Un_upper1 Un_upper2)
qed 

lemma parts_insert_subset_Un: 
  assumes "X \<in> G" 
  shows "parts (insert X H) \<subseteq> parts G \<union> parts H"
proof -
  from assms have "parts (insert X H) \<subseteq> parts (G \<union> H)" by (blast intro!: parts_mono) 
  thus ?thesis by simp
qed 

lemma parts_insert: "parts (insert X H) = parts {X} \<union> parts H"
by (blast intro!: parts_insert_subset_Un intro: parts_monotone)

lemma parts_insert2:
  "parts (insert X (insert Y H)) = parts {X} \<union> parts {Y} \<union> parts H"
apply (simp add: Un_assoc)
apply (simp add: parts_insert [symmetric])
done


lemma parts_UN [simp]: "parts (\<Union>x\<in>A. H x) = (\<Union>x\<in>A. parts(H x))" (is "?X = ?Y")
proof 
  show "?X \<subseteq> ?Y" by (rule subsetI, erule parts.induct) (blast+)
next 
  show "?Y \<subseteq> ?X" by (intro UN_least parts_mono UN_upper)
qed


lemmas in_parts_UnE [elim!] = parts_Un [THEN equalityD1, THEN subsetD, THEN UnE] 


lemma parts_insert_subset: "insert X (parts H) \<subseteq> parts (insert X H)"
by (blast intro: parts_mono [THEN [2] rev_subsetD])


lemma parts_partsD [dest!]: "X \<in> parts (parts H) \<Longrightarrow> X \<in> parts H"
by (erule parts.induct, blast+)

lemma parts_idem [simp]: "parts (parts H) = parts H"
by blast

lemma parts_subset_iff [simp]: "(parts G \<subseteq> parts H) \<longleftrightarrow> (G \<subseteq> parts H)"
by (blast dest: parts_mono)

lemma parts_trans: "X \<in> parts G \<Longrightarrow>  G \<subseteq> parts H \<Longrightarrow> X \<in> parts H"
by (drule parts_mono, blast)


lemma parts_cut:
  "Y \<in> parts (insert X G) \<Longrightarrow>  X \<in> parts H \<Longrightarrow> Y \<in> parts (G \<union> H)" 
by (blast intro: parts_trans)


lemma parts_cut_eq [simp]: "X \<in> parts H \<Longrightarrow> parts (insert X H) = parts H"
by (force dest!: parts_cut intro: parts_insertI)


lemmas parts_insert_eq_I = equalityI [OF subsetI parts_insert_subset]


lemma parts_insert_Agent [simp]:
  "parts (insert (Agent agt) H) = insert (Agent agt) (parts H)"
by (rule parts_insert_eq_I, erule parts.induct, auto)

lemma parts_insert_Nonce [simp]:
  "parts (insert (Nonce N) H) = insert (Nonce N) (parts H)"
by (rule parts_insert_eq_I, erule parts.induct, auto)

lemma parts_insert_Number [simp]:
  "parts (insert (Number N) H) = insert (Number N) (parts H)"
by (rule parts_insert_eq_I, erule parts.induct, auto)

lemma parts_insert_LtK [simp]:
  "parts (insert (LtK K) H) = insert (LtK K) (parts H)"
by (rule parts_insert_eq_I, erule parts.induct, auto)

lemma parts_insert_Hash [simp]:
  "parts (insert (Hash X) H) = insert (Hash X) (parts H)"
by (rule parts_insert_eq_I, erule parts.induct, auto)


lemma parts_insert_Enc [simp]:
  "parts (insert (Enc X Y) H) = insert (Enc X Y) (parts {X} \<union> parts H)"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
done

lemma parts_insert_Aenc [simp]:
  "parts (insert (Aenc X Y) H) = insert (Aenc X Y) (parts {X} \<union> parts H)"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
done

lemma parts_insert_Sign [simp]:
  "parts (insert (Sign X Y) H) = insert (Sign X Y) (parts {X} \<union> parts H)"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
done

lemma parts_insert_Pair [simp]:
  "parts (insert (Pair X Y) H) = insert (Pair X Y) (parts {X} \<union> parts {Y} \<union> parts H)"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct, auto)
done


subsubsection \<open>Lemmas about combinations with composition and decomposition\<close>
(****************************************************************************************)

lemma analz_subset_parts: "analz H \<subseteq> parts H"
apply (rule subsetI)
apply (erule analz.induct, blast+)
done

lemmas analz_into_parts [simp] = analz_subset_parts [THEN subsetD]

lemmas not_parts_not_analz = analz_subset_parts [THEN contra_subsetD]


lemma parts_analz [simp]: "parts (analz H) = parts H"
apply (rule equalityI)
apply (rule analz_subset_parts [THEN parts_mono, THEN subset_trans], simp)
apply (blast intro: analz_increasing [THEN parts_mono, THEN subsetD])
done

lemma analz_parts [simp]: "analz (parts H) = parts H"
apply auto
apply (erule analz.induct, auto)
done


lemma parts_synth [simp]: "parts (synth H) = parts H \<union> synth H"
apply (rule equalityI)
apply (rule subsetI)
apply (erule parts.induct)
apply (blast intro: synth_increasing [THEN parts_mono, THEN subsetD] )+
done

lemma Fake_parts_insert:
  "X \<in> synth (analz H) \<Longrightarrow> parts (insert X H) \<subseteq> synth (analz H) \<union> parts H"
apply (drule parts_insert_subset_Un)
apply (simp (no_asm_use))
apply blast
done

lemma Fake_parts_insert_in_Un:
  "Z \<in> parts (insert X H) \<Longrightarrow>
   X \<in> synth (analz H) \<Longrightarrow>
   Z \<in>  synth (analz H) \<union> parts H"
by (blast dest: Fake_parts_insert [THEN subsetD, dest])


lemma analz_conj_parts [simp]:
  "X \<in> analz H \<and> X \<in> parts H \<longleftrightarrow> X \<in> analz H"
by (blast intro: analz_subset_parts [THEN subsetD])

lemma analz_disj_parts [simp]:
  "X \<in> analz H \<or> X \<in> parts H \<longleftrightarrow> X \<in> parts H"
by (blast intro: analz_subset_parts [THEN subsetD])


(****************************************************************************************)
subsection \<open>More lemmas about combinations of closures\<close>
(****************************************************************************************)

text \<open>Combinations of @{term synth} and @{term analz}.\<close>

lemma Pair_synth_analz [simp]:
  "Pair X Y \<in> synth (analz H) \<longleftrightarrow> X \<in> synth (analz H) \<and> Y \<in> synth (analz H)"
by blast

lemma Enc_synth_analz:
  "Y \<in> synth (analz H) \<Longrightarrow>
   (Enc X Y \<in> synth (analz H)) \<longleftrightarrow> (X \<in> synth (analz H))"
by blast

lemma Hash_synth_analz [simp]:
  "X \<notin> synth (analz H) \<Longrightarrow>
   (Hash (Pair X Y) \<in> synth (analz H)) \<longleftrightarrow> (Hash (Pair X Y) \<in> analz H)"
by blast


lemma gen_analz_insert_eq:
  "\<lbrakk> X \<in> analz G; G \<subseteq> H \<rbrakk> \<Longrightarrow> analz (insert X H) = analz H"
by (blast intro: analz_cut analz_insertI analz_monotone)

lemma synth_analz_insert_eq:
  "\<lbrakk> X \<in> synth (analz G); G \<subseteq> H \<rbrakk> \<Longrightarrow> synth (analz (insert X H)) = synth (analz H)"
by (blast intro!: synth_analz_insert synth_analz_monotone)

lemma Fake_parts_sing:
  "X \<in> synth (analz H) \<Longrightarrow> parts {X} \<subseteq> synth (analz H) \<union> parts H"
apply (rule subset_trans)
apply (erule_tac [2] Fake_parts_insert)
apply (rule parts_mono, blast)
done

lemmas Fake_parts_sing_imp_Un = Fake_parts_sing [THEN [2] rev_subsetD]


lemma analz_hash_nonce [simp]: 
  "analz {M. \<exists>N. M = Hash (Nonce N)} = {M. \<exists>N. M = Hash (Nonce N)}"
by (auto, rule analz.induct, auto)

lemma synth_analz_hash_nonce [simp]: 
  "NonceF N \<notin> synth (analz {M. \<exists>N. M = Hash (Nonce N)})"
by auto

lemma synth_analz_idem_mono:
  "S \<subseteq> synth (analz S') \<Longrightarrow> synth (analz S) \<subseteq> synth (analz S')"
by (frule synth_analz_mono, auto)

lemmas synth_analz_idem_monoI =
  synth_analz_idem_mono [THEN [2] rev_subsetD]



lemma analz_synth_subset:
  "analz X \<subseteq> synth (analz X') \<Longrightarrow>
   analz Y \<subseteq> synth (analz Y') \<Longrightarrow>
   analz (X \<union> Y) \<subseteq> synth (analz (X' \<union> Y'))"
proof -
  assume "analz X \<subseteq> synth (analz X')"
  then have HX:"analz X \<subseteq> analz (synth (analz X'))" by blast
  assume "analz Y \<subseteq> synth (analz Y')"
  then have HY:"analz Y \<subseteq> analz (synth (analz Y'))" by blast
  from analz_subset_cong [OF HX HY] 
  have "analz (X \<union> Y) \<subseteq> analz (synth (analz X') \<union> synth (analz Y'))"
    by blast
  also have "... \<subseteq> analz (synth (analz X' \<union> analz Y'))"
    by (intro analz_mono synth_Un)
  also have "... \<subseteq> analz (synth (analz (X' \<union> Y')))"
    by (intro synth_mono analz_mono analz_Un)
  also have "... \<subseteq> synth (analz (X' \<union> Y'))"
    by auto
  finally show "analz (X \<union> Y) \<subseteq> synth (analz (X' \<union> Y'))"
    by auto
qed


lemma analz_synth_subset_Un1 :
  "analz X \<subseteq> synth (analz X') \<Longrightarrow> analz (X \<union> Y) \<subseteq> synth (analz (X' \<union> Y))"
using analz_synth_subset by blast

lemma analz_synth_subset_Un2 :
  "analz X \<subseteq> synth (analz X') \<Longrightarrow> analz (Y \<union> X) \<subseteq> synth (analz (Y \<union> X'))"
using analz_synth_subset by blast

lemma analz_synth_insert:
  "analz X \<subseteq> synth (analz X') \<Longrightarrow> analz (insert Y X) \<subseteq> synth (analz (insert Y X'))"
by (metis analz_synth_subset_Un2 insert_def)

lemma Fake_analz_insert_Un:
  assumes "Y \<in> analz (insert X H)" and "X \<in> synth (analz G)" 
  shows "Y \<in> synth (analz G) \<union> analz (G \<union> H)"
proof -
  from assms have "Y \<in> analz (synth (analz G) \<union> H)"
    by (blast intro: analz_mono [THEN [2] rev_subsetD] 
                     analz_mono [THEN synth_mono, THEN [2] rev_subsetD])
  thus ?thesis by (simp add: sup.commute) 
qed



end
