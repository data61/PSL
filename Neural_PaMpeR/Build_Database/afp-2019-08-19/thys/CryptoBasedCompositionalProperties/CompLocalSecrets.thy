(*
   Title:  Theory  CompLocalSecrets.thy
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)
section \<open>Local Secrets of a component\<close>

theory CompLocalSecrets
imports Secrecy 
begin

\<comment> \<open>Set of local secrets: the set of secrets which does not belong to\<close>
\<comment> \<open>the set of private keys and unguessable values, but are transmitted\<close>
\<comment> \<open>via local channels or belongs to the local secrets of its subcomponents\<close>
axiomatization
  LocalSecrets :: "specID  \<Rightarrow> KS set"
where
LocalSecretsDef:
 "LocalSecrets A =
  {(m :: KS). m \<notin> specKeysSecrets A  \<and> 
              ((\<exists> x y. ((x \<in> loc A) \<and> m = (kKS y) \<and> (exprChannel x (kE y)))) 
              |(\<exists> x z. ((x \<in> loc A) \<and> m = (sKS z) \<and> (exprChannel x (sE z)) )) )} 
   \<union>  (\<Union> (LocalSecrets ` (subcomponents A) ))"

lemma LocalSecretsComposition1:
assumes "ls \<in> LocalSecrets P"
       and "subcomponents PQ = {P, Q}"
shows    "ls \<in> LocalSecrets PQ"
using assms by (simp (no_asm) only: LocalSecretsDef, auto)

lemma  LocalSecretsComposition_exprChannel_k:
assumes "exprChannel x (kE Keys)"
       and "\<not> ine P (kE Keys)"
       and "\<not> ine Q (kE Keys)"
       and "\<not> (x \<notin> ins P \<and> x \<notin> ins Q)"
shows "False"
using assms by (metis ine_def)

lemma  LocalSecretsComposition_exprChannel_s:
assumes "exprChannel x (sE Secrets)"
       and "\<not> ine P (sE Secrets)"
       and "\<not> ine Q (sE Secrets)"
       and "\<not> (x \<notin> ins P \<and> x \<notin> ins Q)"
shows "False"
using assms by (metis ine_ins_neg1)

lemma LocalSecretsComposition_neg1_k:
assumes "subcomponents PQ = {P, Q}"
       and "correctCompositionLoc PQ"
       and "\<not> ine P (kE Keys)"
       and "\<not> ine Q (kE Keys)"
       and "kKS Keys \<notin> LocalSecrets P"
       and "kKS Keys \<notin> LocalSecrets Q"
shows    "kKS Keys \<notin> LocalSecrets PQ"
proof - 
  from assms show ?thesis 
    apply (simp (no_asm) only: LocalSecretsDef, 
           simp add: correctCompositionLoc_def, clarify)
    by (rule LocalSecretsComposition_exprChannel_k, auto)
qed

lemma LocalSecretsComposition_neg_k:
assumes "subcomponents PQ = {P,Q}"
       and "correctCompositionLoc PQ"
       and "correctCompositionKS PQ"
       and "(kKS m) \<notin> specKeysSecrets P"
       and "(kKS m) \<notin> specKeysSecrets Q"
       and "\<not> ine P (kE m)"
       and "\<not> ine Q (kE m)"
       and "(kKS m) \<notin> ((LocalSecrets P) \<union> (LocalSecrets Q))"
shows    "(kKS m) \<notin> (LocalSecrets PQ)"
proof -
  from assms show ?thesis 
    apply (simp (no_asm) only: LocalSecretsDef, 
           simp add: correctCompositionLoc_def, clarify)
    by (rule LocalSecretsComposition_exprChannel_k, auto)
qed  

lemma LocalSecretsComposition_neg_s:
assumes subPQ:"subcomponents PQ = {P,Q}"
       and cCompLoc:"correctCompositionLoc PQ"
       and cCompKS:"correctCompositionKS PQ"
       and notKSP:"(sKS m) \<notin> specKeysSecrets P"
       and notKSQ:"(sKS m) \<notin> specKeysSecrets Q"
       and "\<not> ine P (sE m)"
       and "\<not> ine Q (sE m)"
       and notLocSeqPQ:"(sKS m) \<notin> ((LocalSecrets P) \<union> (LocalSecrets Q))"
shows   "(sKS m) \<notin> (LocalSecrets PQ)"
proof -
  from subPQ and cCompKS and notKSP and notKSQ
  have sg1:"sKS m \<notin> specKeysSecrets PQ"
    by (simp add: correctCompositionKS_neg1) 
  from subPQ and cCompLoc and notLocSeqPQ have sg2:
   "sKS m \<notin>  \<Union> (LocalSecrets ` subcomponents PQ)"
    by simp
  from sg1 and sg2 and assms show ?thesis 
    apply (simp (no_asm) only: LocalSecretsDef, 
           simp add: correctCompositionLoc_def, clarify)
    by (rule LocalSecretsComposition_exprChannel_s, auto)
qed  

lemma LocalSecretsComposition_neg:
assumes "subcomponents PQ = {P,Q}" 
       and "correctCompositionLoc PQ" 
       and "correctCompositionKS PQ"
       and "ks \<notin> specKeysSecrets P"
       and "ks \<notin> specKeysSecrets Q"
       and h1:"\<forall> m. ks = kKS m \<longrightarrow> (\<not> ine P (kE m) \<and> \<not> ine Q (kE m))"
       and h2:"\<forall> m. ks = sKS m \<longrightarrow> (\<not> ine P (sE m) \<and> \<not> ine Q (sE m))"
       and "ks \<notin> ((LocalSecrets P) \<union> (LocalSecrets Q))"
shows   "ks \<notin> (LocalSecrets PQ)"
proof (cases "ks")
  fix m
  assume a1:"ks = kKS m"
  from this and h1 have "\<not> ine P (kE m) \<and> \<not> ine Q (kE m)" by simp
  from this and a1 and assms show ?thesis
    by (simp add: LocalSecretsComposition_neg_k)
next
  fix m
  assume a2:"ks = sKS m"
  from this and h2 have "\<not> ine P (sE m) \<and> \<not> ine Q (sE m)" by simp
  from this and a2 and assms show ?thesis
    by (simp add: LocalSecretsComposition_neg_s)
qed

lemma LocalSecretsComposition_neg1_s:
assumes "subcomponents PQ = {P, Q}"
       and "correctCompositionLoc PQ"
       and "\<not> ine P (sE s)"
       and "\<not> ine Q (sE s)"
       and "sKS s \<notin> LocalSecrets P" 
       and "sKS s \<notin> LocalSecrets Q"
shows    "sKS s \<notin> LocalSecrets PQ"
proof - 
  from assms have 
   "sKS s \<notin>  \<Union> (LocalSecrets ` subcomponents PQ)"
    by simp
    from  assms and this show ?thesis 
    apply (simp (no_asm) only: LocalSecretsDef, 
              simp add: correctCompositionLoc_def, clarify)
    by (rule LocalSecretsComposition_exprChannel_s, auto)
qed  

lemma LocalSecretsComposition_neg1:
assumes "subcomponents PQ = {P, Q}"
       and "correctCompositionLoc PQ"
       and h1:"\<forall> m. ks = kKS m \<longrightarrow> (\<not> ine P (kE m) \<and> \<not> ine Q (kE m))" 
       and h2:"\<forall> m. ks = sKS m \<longrightarrow> (\<not> ine P (sE m) \<and> \<not> ine Q (sE m))"
       and "ks \<notin> LocalSecrets P"
       and "ks \<notin> LocalSecrets Q"
shows    "ks \<notin> LocalSecrets PQ"
proof (cases "ks")
  fix m
  assume a1:"ks = kKS m"
  from this and h1 have "\<not> ine P (kE m) \<and> \<not> ine Q (kE m)" by simp
  from this and a1 and assms show ?thesis 
    by (simp add: LocalSecretsComposition_neg1_k)
next
  fix m
  assume a2:"ks = sKS m"
  from this and h2 have "\<not> ine P (sE m) \<and> \<not> ine Q (sE m)" by simp
  from this and a2 and assms show ?thesis 
    by (simp add: LocalSecretsComposition_neg1_s)
qed

lemma LocalSecretsComposition_ine1_k:
assumes "kKS k \<in> LocalSecrets PQ" 
       and "subcomponents PQ = {P, Q}"
       and "correctCompositionLoc PQ" 
       and "\<not> ine Q (kE k)"
       and "kKS k \<notin> LocalSecrets P"
       and "kKS k \<notin> LocalSecrets Q"
shows    "ine P (kE k)"
using assms by (metis LocalSecretsComposition_neg1_k)

lemma LocalSecretsComposition_ine1_s:
assumes "sKS s \<in> LocalSecrets PQ" 
       and "subcomponents PQ = {P, Q}"
       and "correctCompositionLoc PQ" 
       and "\<not> ine Q (sE s)"
       and "sKS s \<notin> LocalSecrets P"
       and "sKS s \<notin> LocalSecrets Q"
shows    "ine P (sE s)"
using assms by (metis LocalSecretsComposition_neg1_s)

lemma LocalSecretsComposition_ine2_k:
assumes "kKS k \<in> LocalSecrets PQ"
       and "subcomponents PQ = {P, Q}"
       and "correctCompositionLoc PQ"
       and "\<not> ine P (kE k)"
       and "kKS k \<notin> LocalSecrets P"
       and "kKS k \<notin> LocalSecrets Q"
shows   "ine Q (kE k)" 
using assms  by (metis LocalSecretsComposition_ine1_k)

lemma LocalSecretsComposition_ine2_s:
assumes "sKS s \<in> LocalSecrets PQ" 
       and "subcomponents PQ = {P, Q}"
       and "correctCompositionLoc PQ"
       and "\<not> ine P (sE s)"
       and "sKS s \<notin> LocalSecrets P"
       and "sKS s \<notin> LocalSecrets Q"
shows    "ine Q (sE s)"
using assms by (metis LocalSecretsComposition_ine1_s)

lemma LocalSecretsComposition_neg_loc_k:
assumes "kKS key \<notin> LocalSecrets P"
       and "exprChannel ch (kE key)"
       and "kKS key \<notin> specKeysSecrets P"
shows    "ch \<notin> loc P"
using assms by (simp only: LocalSecretsDef, auto)

lemma LocalSecretsComposition_neg_loc_s:
assumes "sKS secret \<notin> LocalSecrets P"
       and "exprChannel ch (sE secret)"
       and "sKS secret \<notin> specKeysSecrets P"
shows    "ch \<notin> loc P"
using assms by (simp only: LocalSecretsDef, auto)

lemma correctCompositionKS_exprChannel_k_P:
assumes "subcomponents PQ = {P,Q}" 
       and "correctCompositionKS PQ"
       and "kKS key \<notin> LocalSecrets PQ"
       and "ch \<in> ins P"
       and "exprChannel ch (kE key)"
       and "kKS key \<notin> specKeysSecrets PQ"
       and "correctCompositionIn PQ"
shows    "ch \<in> ins PQ \<and> exprChannel ch (kE key)"
using assms
by (metis LocalSecretsComposition_neg_loc_k correctCompositionIn_L1)

lemma correctCompositionKS_exprChannel_k_Pex:
assumes "subcomponents PQ = {P,Q}" 
       and "correctCompositionKS PQ"
       and "kKS key \<notin> LocalSecrets PQ"
       and "ch \<in> ins P"
       and "exprChannel ch (kE key)"
       and "kKS key \<notin> specKeysSecrets PQ"
       and "correctCompositionIn PQ"
shows    "\<exists>ch. ch \<in> ins PQ \<and> exprChannel ch (kE key)"
using assms
by (metis correctCompositionKS_exprChannel_k_P)

lemma correctCompositionKS_exprChannel_k_Q:
assumes "subcomponents PQ = {P,Q}" 
       and "correctCompositionKS PQ"
       and "kKS key \<notin> LocalSecrets PQ"
       and "ch \<in> ins Q"
       and h1:"exprChannel ch (kE key)"
       and "kKS key \<notin> specKeysSecrets PQ"
       and "correctCompositionIn PQ"
shows    "ch \<in> ins PQ \<and> exprChannel ch (kE key)"
proof - 
  from assms have "ch \<notin> loc PQ" 
    by (simp add: LocalSecretsComposition_neg_loc_k)
  from this and assms have "ch \<in> ins PQ" 
    by (simp add: correctCompositionIn_def) 
  from this and h1 show ?thesis by simp
qed

lemma correctCompositionKS_exprChannel_k_Qex:
assumes "subcomponents PQ = {P,Q}" 
        and "correctCompositionKS PQ"
        and "kKS key \<notin> LocalSecrets PQ"
        and "ch \<in> ins Q"
        and "exprChannel ch (kE key)"
        and "kKS key \<notin> specKeysSecrets PQ"
        and "correctCompositionIn PQ"
shows    "\<exists>ch. ch \<in> ins PQ \<and> exprChannel ch (kE key)"
using assms
by (metis correctCompositionKS_exprChannel_k_Q)

lemma correctCompositionKS_exprChannel_s_P:
assumes "subcomponents PQ = {P,Q}" 
       and "correctCompositionKS PQ"
       and "sKS secret \<notin> LocalSecrets PQ"
       and "ch \<in> ins P"
       and "exprChannel ch (sE secret)"
       and "sKS secret \<notin> specKeysSecrets PQ"
       and "correctCompositionIn PQ"
shows    "ch \<in> ins PQ \<and> exprChannel ch (sE secret)"
using assms
by (metis LocalSecretsComposition_neg_loc_s correctCompositionIn_L1)

lemma correctCompositionKS_exprChannel_s_Pex:
assumes "subcomponents PQ = {P,Q}" 
       and "correctCompositionKS PQ"
       and "sKS secret \<notin> LocalSecrets PQ"
       and "ch \<in> ins P"
       and "exprChannel ch (sE secret)"
       and "sKS secret \<notin> specKeysSecrets PQ"
       and "correctCompositionIn PQ"
shows    "\<exists>ch. ch \<in> ins PQ \<and> exprChannel ch (sE secret)"
using assms  
by (metis correctCompositionKS_exprChannel_s_P)

lemma correctCompositionKS_exprChannel_s_Q:
assumes "subcomponents PQ = {P,Q}" 
       and "correctCompositionKS PQ"
       and "sKS secret \<notin> LocalSecrets PQ"
       and "ch \<in> ins Q"
       and h1:"exprChannel ch (sE secret)"
       and "sKS secret \<notin> specKeysSecrets PQ"
       and "correctCompositionIn PQ"
shows    "ch \<in> ins PQ \<and> exprChannel ch (sE secret)"
proof - 
  from assms have "ch \<notin> loc PQ" 
    by (simp add: LocalSecretsComposition_neg_loc_s)
  from this and assms have "ch \<in> ins PQ" 
    by (simp add: correctCompositionIn_def) 
  from this and h1 show ?thesis by simp
qed

lemma correctCompositionKS_exprChannel_s_Qex:
assumes "subcomponents PQ = {P,Q}" 
       and "correctCompositionKS PQ"
       and "sKS secret \<notin> LocalSecrets PQ"
       and "ch \<in> ins Q"
       and "exprChannel ch (sE secret)"
       and "sKS secret \<notin> specKeysSecrets PQ"
       and "correctCompositionIn PQ"
shows    "\<exists>ch. ch \<in> ins PQ \<and> exprChannel ch (sE secret)"
using assms
by (metis correctCompositionKS_exprChannel_s_Q)

end
