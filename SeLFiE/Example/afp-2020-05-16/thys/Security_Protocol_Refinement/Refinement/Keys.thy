(*******************************************************************************  

  Project: Development of Security Protocols by Refinement

  Module:  Refinement/Keys.thy (Isabelle/HOL 2016-1)
  ID:      $Id: Keys.thy 132773 2016-12-09 15:30:22Z csprenge $
  Author:  Christoph Sprenger, ETH Zurich <sprenger@inf.ethz.ch>
  
  Symmetric (shared) and asymmetric (public/private) keys.
  (based on Larry Paulson's theory Public.thy)

  Copyright (c) 2012-2016 Christoph Sprenger 
  Licence: LGPL

*******************************************************************************)

section \<open>Symmetric and Assymetric Keys\<close>

theory Keys imports Agents begin

text \<open>Divide keys into session and long-term keys. Define different kinds
of long-term keys in second step.\<close>

datatype ltkey =    \<comment> \<open>long-term keys\<close>
  sharK "agent"     \<comment> \<open>key shared with server\<close>
| publK "agent"     \<comment> \<open>agent's public key\<close>
| privK "agent"     \<comment> \<open>agent's private key\<close>

datatype key = 
  sesK "fresh_t"   \<comment> \<open>session key\<close>
| ltK "ltkey"      \<comment> \<open>long-term key\<close>

abbreviation
  shrK :: "agent \<Rightarrow> key" where
  "shrK A \<equiv> ltK (sharK A)"

abbreviation
  pubK :: "agent \<Rightarrow> key" where
  "pubK A \<equiv> ltK (publK A)"

abbreviation
  priK :: "agent \<Rightarrow> key" where
  "priK A \<equiv> ltK (privK A)"


text\<open>The inverse of a symmetric key is itself; that of a public key
       is the private key and vice versa\<close>

fun invKey :: "key \<Rightarrow> key" where
  "invKey (ltK (publK A)) = priK A"
| "invKey (ltK (privK A)) = pubK A"
| "invKey K = K"

definition
  symKeys :: "key set" where
  "symKeys \<equiv> {K. invKey K = K}"

lemma invKey_K: "K \<in> symKeys \<Longrightarrow> invKey K = K"
by (simp add: symKeys_def)


text \<open>Most lemmas we need come for free with the inductive type definition:
injectiveness and distinctness.\<close>

lemma invKey_invKey_id [simp]: "invKey (invKey K) = K"
by (cases K, auto) 
   (rename_tac ltk, case_tac ltk, auto)

lemma invKey_eq [simp]: "(invKey K = invKey K') = (K=K')"
apply (safe)
apply (drule_tac f=invKey in arg_cong, simp)
done


text \<open>We get most lemmas below for free from the inductive definition
of type @{typ key}. Many of these are just proved as a reality check.\<close>


subsection\<open>Asymmetric Keys\<close>
(******************************************************************************)

text \<open>No private key equals any public key (essential to ensure that private
keys are private!). A similar statement an axiom in Paulson's theory!\<close>

lemma privateKey_neq_publicKey: "priK A \<noteq> pubK A'"
by auto

lemma publicKey_neq_privateKey: "pubK A \<noteq> priK A'"
by auto


subsection\<open>Basic properties of @{term pubK} and @{term priK}\<close>

lemma publicKey_inject [iff]: "(pubK A = pubK A') = (A = A')"
by (auto)

lemma not_symKeys_pubK [iff]: "pubK A \<notin> symKeys"
by (simp add: symKeys_def)

lemma not_symKeys_priK [iff]: "priK A \<notin> symKeys"
by (simp add: symKeys_def)

lemma symKey_neq_priK: "K \<in> symKeys \<Longrightarrow> K \<noteq> priK A"
by (auto simp add: symKeys_def)

lemma symKeys_neq_imp_neq: "(K \<in> symKeys) \<noteq> (K' \<in> symKeys) \<Longrightarrow> K \<noteq> K'"
by blast

lemma symKeys_invKey_iff [iff]: "(invKey K \<in> symKeys) = (K \<in> symKeys)"
by (unfold symKeys_def, auto)


subsection\<open>"Image" equations that hold for injective functions\<close>

lemma invKey_image_eq [simp]: "(invKey x \<in> invKey`A) = (x \<in> A)"
by auto

(*holds because invKey is injective*)

lemma invKey_pubK_image_priK_image [simp]: "invKey ` pubK ` AS = priK ` AS"
by (auto simp add: image_def)

lemma publicKey_notin_image_privateKey: "pubK A \<notin> priK ` AS"
by auto

lemma privateKey_notin_image_publicKey: "priK x \<notin> pubK ` AA"
by auto

lemma publicKey_image_eq [simp]: "(pubK x \<in> pubK ` AA) = (x \<in> AA)"
by auto

lemma privateKey_image_eq [simp]: "(priK A \<in> priK ` AS) = (A \<in> AS)"
by auto



subsection\<open>Symmetric Keys\<close>
(******************************************************************************)

text \<open>The following was stated as an axiom in Paulson's theory.\<close>

lemma sym_sesK: "sesK f \<in> symKeys"   \<comment> \<open>All session keys are symmetric\<close>
by (simp add: symKeys_def)

lemma sym_shrK: "shrK X \<in> symKeys"   \<comment> \<open>All shared keys are symmetric\<close>
by (simp add: symKeys_def)


text \<open>Symmetric keys and inversion\<close>

lemma symK_eq_invKey: "\<lbrakk> SK = invKey K; SK \<in> symKeys \<rbrakk> \<Longrightarrow> K = SK" 
by (auto simp add: symKeys_def)


text \<open>Image-related lemmas.\<close>

lemma publicKey_notin_image_shrK: "pubK x \<notin> shrK ` AA"
by auto

lemma privateKey_notin_image_shrK: "priK x \<notin> shrK ` AA"
by auto

lemma shrK_notin_image_publicKey: "shrK x \<notin> pubK ` AA"
by auto

lemma shrK_notin_image_privateKey: "shrK x \<notin> priK ` AA" 
by auto

lemma sesK_notin_image_shrK [simp]: "sesK K \<notin> shrK`AA"
by (auto)

lemma shrK_notin_image_sesK [simp]: "shrK K \<notin> sesK`AA"
by (auto)

lemma sesK_image_eq [simp]: "(sesK x \<in> sesK ` AA) = (x \<in> AA)"
by auto

lemma shrK_image_eq [simp]: "(shrK x \<in> shrK ` AA) = (x \<in> AA)"
by auto


end


