(*
   Title:  Theory AdvKnowledge.thy
   Author: Maria Spichkova <maria.spichkova at rmit.edu.au>, 2014
*)
section \<open>Knowledge of Keys and Secrets\<close>

theory KnowledgeKeysSecrets
imports CompLocalSecrets 
begin

text_raw \<open>
~\\
An component $A$ knows a secret $m$ (or some secret expression $m$)  that does not belong to its local sectrets , if
\begin{itemize}
  \item %
  $A$  may eventually get the secret $m$,
  \item 
  $m$ belongs to the set $LS_A$ of its local secrets, 
  \item %
  $A$ knows some list of expressions $m_2$ which is an concatenations of $m$ and some list of expressions $m_1$,
  \item %
  $m$ is a concatenation of some lists of secrets $m_1$ and $m_2$, and $A$ knows both these secrets,
  \item %
  $A$ knows some secret key $k^{-1}$ and the result of the encryption of the $m$ with the corresponding public key,
  \item %
  $A$ knows some public key $k$ and the result of the signature creation of the $m$ with the corresponding private key,%
  \item %
  $m$ is an encryption of some secret $m_1$ with a public key $k$, and $A$ knows both $m_1$ and $k$,
  \item %
  $m$ is the result of the signature creation of the $m_1$ with the key $k$, and $A$ knows both $m_1$ and $k$.
  %($m = Sign(k, m_1)  \wedge \knows{A}{m_1} \wedge \knows{A}{k}$).
\end{itemize}
\<close>

primrec
  know :: "specID \<Rightarrow> KS \<Rightarrow> bool"
where 
 "know A (kKS m) = 
  ((ine A (kE m)) \<or> ((kKS m) \<in> (LocalSecrets A)))" | 
 "know A (sKS m) = 
  ((ine A (sE m)) \<or> ((sKS m) \<in> (LocalSecrets A)))"

axiomatization
  knows :: "specID \<Rightarrow> Expression list \<Rightarrow> bool"
where
knows_emptyexpression:
  "knows C [] = True" and
know1k: 
  "knows C [KS2Expression (kKS m1)] = know C (kKS m1)" and
know1s:
  "knows C [KS2Expression (sKS m2)] = know C (sKS m2)" and
knows2a: 
  "knows A (e1 @ e) \<longrightarrow> knows A e" and
knows2b: 
  "knows A (e @ e1) \<longrightarrow> knows A e" and
knows3: 
  "(knows A e1) \<and> (knows A e2) \<longrightarrow> knows A (e1 @ e2)" and
knows4: 
  "(IncrDecrKeys k1 k2) \<and> (know A (kKS k2)) \<and> (knows A (Enc k1 e))
   \<longrightarrow> knows A e" 
and
knows5: 
  "(IncrDecrKeys k1 k2) \<and> (know A (kKS k1)) \<and> (knows A (Sign k2 e))
   \<longrightarrow> knows A e"
and
knows6: 
  "(know A (kKS k)) \<and> (knows A e1) \<longrightarrow> knows A (Enc k e1)"
and
knows7: 
  "(know A (kKS k)) \<and> (knows A e1) \<longrightarrow> knows A (Sign k e1)"

primrec  eoutKnowCorrect :: "specID \<Rightarrow> KS \<Rightarrow> bool"
where
eout_know_k: 
  "eoutKnowCorrect C (kKS m) = 
  ((eout  C (kE m)) \<longleftrightarrow> (m \<in> (specKeys C) \<or> (know C (kKS m))) )"  |
eout_know_s: 
   "eoutKnowCorrect C (sKS m) = 
  ((eout  C (sE m)) \<longleftrightarrow>  (m \<in> (specSecrets C) \<or> (know C (sKS m))) )"

definition eoutKnowsECorrect :: "specID \<Rightarrow> Expression \<Rightarrow> bool"
where
  "eoutKnowsECorrect C e \<equiv>
   ((eout  C e) \<longleftrightarrow>
   ((\<exists> k. e = (kE k) \<and> (k \<in> specKeys C)) \<or> 
    (\<exists> s. e = (sE s) \<and> (s \<in> specSecrets C)) \<or>
    (knows C [e])))"

lemma eoutKnowCorrect_L1k:
assumes "eoutKnowCorrect C (kKS m)"  
       and "eout  C (kE m)"
shows    "m \<in> (specKeys C) \<or> (know C (kKS m))" 
using assms by (metis eout_know_k)

lemma eoutKnowCorrect_L1s:
assumes "eoutKnowCorrect C (sKS m)" 
       and "eout  C (sE m)"
shows    "m \<in> (specSecrets C) \<or> (know C (sKS m))" 
using assms by (metis eout_know_s)

lemma eoutKnowsECorrect_L1:
assumes "eoutKnowsECorrect C e" 
       and "eout  C e"
shows "(\<exists> k. e = (kE k) \<and> (k \<in> specKeys C)) \<or> 
            (\<exists> s. e = (sE s) \<and> (s \<in> specSecrets C)) \<or>
            (knows C [e])" 
using assms by (metis eoutKnowsECorrect_def)
 
lemma know2knows_k: 
assumes "know A (kKS m)"
shows    "knows A [kE m]" 
using assms
by (metis KS2Expression.simps(1) know1k)

lemma knows2know_k: 
assumes "knows A [kE m]" 
shows    "know A (kKS m)"
using assms
by (metis KS2Expression.simps(1) know1k)

lemma know2knowsPQ_k: 
assumes "know P (kKS m) \<or> know Q (kKS m)"
shows    "knows P [kE m] \<or> knows Q [kE m]" 
using assms by (metis know2knows_k)

lemma knows2knowPQ_k: 
assumes "knows P [kE m] \<or> knows Q [kE m]"
shows     "know P (kKS m) \<or> know Q (kKS m)"
using assms  by (metis knows2know_k)

lemma knows1k: 
 "know A (kKS m) = knows A [kE m]"
by (metis know2knows_k knows2know_k) 

lemma know2knows_neg_k: 
assumes  "\<not> know A (kKS m)"
shows     "\<not> knows A [kE m]"
using assms by (metis knows1k) 

lemma knows2know_neg_k: 
assumes "\<not> knows A [kE m]" 
shows    "\<not> know A (kKS m)"
using assms by (metis know2knowsPQ_k)

lemma know2knows_s: 
assumes "know A (sKS m)"
shows    "knows A [sE m]"
using assms
by (metis KS2Expression.simps(2) know1s) 

lemma knows2know_s: 
assumes "knows A [sE m]" 
shows    "know A (sKS m)"
using assms
by (metis KS2Expression.simps(2) know1s) 

lemma know2knowsPQ_s: 
assumes "know P (sKS m) \<or> know Q (sKS m)"
shows    "knows P [sE m] \<or> knows Q [sE m]" 
using assms by (metis know2knows_s)

lemma knows2knowPQ_s: 
assumes "knows P [sE m] \<or> knows Q [sE m]"
shows    "know P (sKS m) \<or> know Q (sKS m)"
using assms by (metis knows2know_s)

lemma knows1s:
  "know A (sKS m) = knows A [sE m]"
by (metis know2knows_s knows2know_s) 

lemma know2knows_neg_s: 
assumes "\<not> know A (sKS m)"
shows    "\<not> knows A [sE m]" 
using assms by (metis knows2know_s) 

lemma knows2know_neg_s: 
assumes "\<not> knows A [sE m]" 
shows    "\<not> know A (sKS m)"
using assms by (metis  know2knows_s)

lemma knows2: 
assumes "e2 = e1 @ e \<or> e2 = e @ e1" 
       and "knows A e2" 
shows    "knows A e"
using assms by (metis knows2a knows2b)
 
lemma correctCompositionInLoc_exprChannel:
assumes "subcomponents PQ = {P, Q}"
       and "correctCompositionIn PQ"
       and "ch : ins P"
       and "exprChannel ch m"
       and "\<forall> x. x \<in> ins PQ \<longrightarrow> \<not> exprChannel x m"
shows    "ch : loc PQ"
using assms by (simp add: correctCompositionIn_def, auto)

lemma eout_know_nonKS_k: 
assumes "m \<notin> specKeys A"
        and "eout A (kE m)"
        and "eoutKnowCorrect A (kKS m)"
shows     "know A (kKS m)"
using assms by (metis eoutKnowCorrect_L1k)

lemma  eout_know_nonKS_s:
assumes "m \<notin> specSecrets A"
        and "eout A (sE m)"
        and "eoutKnowCorrect A (sKS m)"
shows    "know A (sKS m)"
using assms by (metis eoutKnowCorrect_L1s)

lemma not_know_k_not_ine:
assumes "\<not> know A (kKS m)"
shows    "\<not> ine A (kE m)"
using assms by simp

lemma not_know_s_not_ine:
assumes "\<not> know A (sKS m)"
shows    "\<not> ine A (sE m)"
using assms by simp

lemma not_know_k_not_eout:
assumes "m \<notin> specKeys A"
        and "\<not> know A (kKS m)" 
        and "eoutKnowCorrect A (kKS m)"
shows     "\<not> eout A (kE m)"
using assms by (metis eout_know_k)

lemma not_know_s_not_eout:
assumes "m \<notin> specSecrets A"
        and "\<not> know A (sKS m)"
        and "eoutKnowCorrect A (sKS m)"
shows     "\<not> eout A (sE m)"
using assms by (metis eout_know_nonKS_s)

lemma adv_not_know1:
assumes "out P \<subseteq> ins A"
        and "\<not> know A (kKS m)" 
shows    "\<not> eout P (kE m)" 
using assms
by (metis (full_types) eout_def ine_ins_neg1 not_know_k_not_ine rev_subsetD)

lemma  adv_not_know2:
assumes "out P \<subseteq> ins A"
       and "\<not> know A (sKS m)"
shows    "\<not> eout P (sE m)"
using assms
by (metis (full_types) eout_def ine_ins_neg1 not_know_s_not_ine rev_subsetD)

lemma LocalSecrets_L1:
assumes "(kKS) key \<in> LocalSecrets P"  
       and "(kKS key) \<notin> \<Union>(LocalSecrets ` subcomponents P)"
shows    "kKS key \<notin> specKeysSecrets P"
using assms by (simp only: LocalSecretsDef, auto)

lemma LocalSecrets_L2:
assumes "kKS key \<in> LocalSecrets P"  
       and "kKS key \<in> specKeysSecrets P"
shows    "kKS key \<in> \<Union>(LocalSecrets ` subcomponents P)"
using assms by (simp only: LocalSecretsDef, auto)

lemma know_composition1:
assumes notKSP:"m \<notin> specKeysSecrets P"
       and notKSQ:"m \<notin> specKeysSecrets Q"
       and "know P m"
       and subPQ:"subcomponents PQ = {P,Q}" 
       and cCompI:"correctCompositionIn PQ"
       and cCompKS:"correctCompositionKS PQ"
shows    "know PQ m"
proof (cases m)
  fix key
  assume a1:"m = kKS key"
  show ?thesis
  proof (cases  "ine P (kE key)") 
     assume a11:"ine P (kE key)" 
     from this have a11ext:"ine P (kE key) | ine Q (kE key)" by simp
     from subPQ and cCompKS and notKSP and notKSQ 
       have "m \<notin> specKeysSecrets PQ" 
       by (rule correctCompositionKS_neg1) 
     from this and a1 have sg1:"kKS key \<notin> specKeysSecrets PQ" by simp
     from a1 and a11ext and cCompKS  show ?thesis
     proof (cases "loc PQ = {}")
       assume a11locE:"loc PQ = {}"
       from a11ext and subPQ and cCompI and a11locE have "ine PQ (kE key)" 
         by (rule TBtheorem4a_empty) 
       from this and a1 show ?thesis by auto
     next 
       assume a11locNE:"loc PQ \<noteq> {}"
       from a1 and a11 and sg1 and assms show ?thesis
         apply (simp add: ine_def, auto)
         by (simp add: correctCompositionKS_exprChannel_k_Pex) 
     qed
   next
     assume a12:"\<not> ine P (kE key)"
     from this and a1 and assms show ?thesis
       by (auto, simp add:  LocalSecretsComposition1)
   qed
 next
  fix secret
  assume a2:"m = sKS secret"
  show ?thesis
  proof (cases  "ine P (sE secret)") 
     assume a21:"ine P (sE secret)" 
     from this have a21ext:"ine P (sE secret) | ine Q (sE secret)" by simp
     from subPQ and cCompKS and notKSP and notKSQ have "m \<notin> specKeysSecrets PQ" 
       by (rule correctCompositionKS_neg1) 
     from this and a2 have sg2:"sKS secret \<notin> specKeysSecrets PQ" by simp
     from a2 and a21ext and cCompKS  show ?thesis
     proof (cases "loc PQ = {}")
       assume a21locE:"loc PQ = {}"
       from a21ext and subPQ and cCompI and a21locE have "ine PQ (sE secret)" 
         by (rule TBtheorem4a_empty) 
       from this and a2 show ?thesis by auto
     next 
       assume a21locNE:"loc PQ \<noteq> {}"
       from a2 and a21 and sg2 and assms show ?thesis
         apply (simp add: ine_def, auto)
         by (simp add: correctCompositionKS_exprChannel_s_Pex) 
     qed
   next
     assume a12:"\<not> ine P (sE secret)"
     from this and a2 and assms show ?thesis
     by (metis LocalSecretsComposition1 know.simps(2))
   qed
qed

lemma know_composition2:
assumes "m \<notin> specKeysSecrets P"
       and "m \<notin> specKeysSecrets Q"
       and "know Q m"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "correctCompositionKS PQ"
shows    "know PQ m"
using assms by (metis insert_commute know_composition1)

lemma know_composition:
assumes "m \<notin> specKeysSecrets P"
        and "m \<notin> specKeysSecrets Q"
        and "know P m \<or> know Q m"
        and "subcomponents PQ = {P,Q}" 
        and "correctCompositionIn PQ"
        and "correctCompositionKS PQ"
shows    "know PQ m"
using assms by (metis know_composition1 know_composition2)

theorem know_composition_neg_ine_k:
assumes "\<not> know P (kKS key)"
       and "\<not> know Q (kKS key)"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
shows    "\<not> (ine PQ (kE key))"
using assms by (metis TBtheorem3a not_know_k_not_ine)

theorem know_composition_neg_ine_s:
assumes "\<not> know P (sKS secret)"
       and "\<not> know Q (sKS secret)"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
shows    "\<not> (ine PQ (sE secret))"
using assms by (metis TBtheorem3a not_know_s_not_ine)

lemma know_composition_neg1:
assumes notknowP:"\<not> know P m"
       and notknowQ:"\<not> know Q m"
       and subPQ:"subcomponents PQ = {P,Q}"
       and cCompLoc:"correctCompositionLoc PQ"
       and cCompI:"correctCompositionIn PQ"
shows    "\<not> know PQ m"
proof (cases m)
  fix key
  assume a1:"m = kKS key"
  from notknowP and a1 have sg1:"\<not> know P (kKS key)" by simp
  then have sg1a:"\<not> ine P (kE key)" by simp
  from sg1 have sg1b:"kKS key \<notin> LocalSecrets P" by simp
  from notknowQ and a1 have sg2:"\<not> know Q (kKS key)" by simp
  then  have sg2a:"\<not> ine Q (kE key)" by simp
  from sg2 have sg2b:"kKS key \<notin> LocalSecrets Q" by simp
  from sg1 and sg2 and subPQ and cCompI have sg3:"\<not> ine PQ (kE key)"
    by (rule know_composition_neg_ine_k)
  from subPQ and cCompLoc and sg1a and sg2a and sg1b and sg2b have sg4:
  "kKS key \<notin> LocalSecrets PQ" 
    by (rule LocalSecretsComposition_neg1_k)
  from sg3 and sg4 and a1 show ?thesis by simp
next 
  fix secret
  assume a2:"m = sKS secret"
  from notknowP and a2 have sg1:"\<not> know P (sKS secret)" by simp
  then have sg1a:"\<not> ine P (sE secret)" by simp
  from sg1 have sg1b:"sKS secret \<notin> LocalSecrets P" by simp
  from notknowQ and a2 have sg2:"\<not> know Q (sKS secret)" by simp
  then have sg2a:"\<not> ine Q (sE secret)" by simp
  from sg2 have sg2b:"sKS secret \<notin> LocalSecrets Q" by simp
  from sg1 and sg2 and subPQ and cCompI have sg3:"\<not> ine PQ (sE secret)"
    by (rule know_composition_neg_ine_s) 
  from subPQ and cCompLoc and sg1a and sg2a and sg1b and sg2b have sg4:
  "sKS secret \<notin> LocalSecrets PQ"  
    by (rule LocalSecretsComposition_neg1_s)
  from sg3 and sg4 and a2 show ?thesis by simp
qed

lemma know_decomposition:
assumes knowPQ:"know PQ m"
       and subPQ:"subcomponents PQ = {P,Q}" 
       and cCompI:"correctCompositionIn PQ"
       and cCompLoc:"correctCompositionLoc PQ"
shows "know P m \<or> know Q m"
proof (cases m)
  fix key
  assume a1:"m = kKS key"
  from this show ?thesis
  proof (cases "ine PQ (kE key)")
    assume a11:"ine PQ (kE key)"
    from this and subPQ and cCompI and a1 have 
     "ine P (kE key)  \<or> ine Q (kE key)"
      by (simp add: TBtheorem1a)
    from this and a1 show ?thesis by auto
  next
    assume a12:"\<not> ine PQ (kE key)"
    from this and knowPQ and a1 have sg2:"kKS key \<in> LocalSecrets PQ" by auto
    show ?thesis 
    proof (cases "know Q m")
      assume "know Q m"
      from this show ?thesis by simp
    next 
      assume not_knowQm:"\<not> know Q m"
      from not_knowQm and a1 have sg3a:"\<not> ine Q (kE key)" by simp
      from not_knowQm and a1 have sg3b:"kKS key \<notin> LocalSecrets Q" by simp
      show ?thesis
      proof (cases "kKS key \<in> LocalSecrets P")
        assume "kKS key \<in> LocalSecrets P"
        from this and a1 show ?thesis by simp
      next
        assume "kKS key \<notin> LocalSecrets P"
        from sg2 and subPQ and cCompLoc and sg3a and this and sg3b have "ine P (kE key)"
          by (simp add: LocalSecretsComposition_ine1_k)
        from this and a1 show ?thesis by simp
      qed
    qed
  qed
next
  fix secret
  assume a2:"m = sKS secret"
  from this show ?thesis
  proof (cases "ine PQ (sE secret)")
    assume a21:"ine PQ (sE secret)"
    from this and subPQ and cCompI and a2 have
     "ine P (sE secret)  \<or> ine Q (sE secret)"
      by (simp add: TBtheorem1a)
    from this and a2 show ?thesis by auto
  next
    assume a22:"\<not> ine PQ (sE secret)"
    from this and knowPQ and a2 have sg5:
     "sKS secret \<in> LocalSecrets PQ" by auto
    show ?thesis 
    proof (cases "know Q m")
      assume "know Q m"
      from this show ?thesis by simp
    next 
      assume not_knowQm:"\<not> know Q m"
      from not_knowQm and a2 have sg6a:"\<not> ine Q (sE secret)" by simp
      from not_knowQm and a2 have sg6b:"sKS secret \<notin> LocalSecrets Q" by simp
      show ?thesis
      proof (cases "sKS secret \<in> LocalSecrets P")
        assume "sKS secret \<in> LocalSecrets P"
        from this and a2 show ?thesis by simp
      next
        assume "sKS secret \<notin> LocalSecrets P"
        from sg5 and subPQ and cCompLoc and sg6a and this and sg6b have 
         "ine P (sE secret)"
          by (simp add: LocalSecretsComposition_ine1_s)
        from this and a2 show ?thesis by simp
      qed
    qed
  qed
qed

lemma eout_knows_nonKS_k:
 assumes "m \<notin> (specKeys A)"
         and "eout A (kE m)"
         and "eoutKnowsECorrect A (kE m)"
   shows "knows A [kE m]"
using assms
by (metis Expression.distinct(1) Expression.inject(1) eoutKnowsECorrect_L1)

lemma eout_knows_nonKS_s:
 assumes h1:"m \<notin> specSecrets A"
         and h2:"eout A (sE m)"
         and h3:"eoutKnowsECorrect A (sE m)"
   shows "knows A [sE m]"
using assms
by (metis Expression.distinct(1) Expression.inject(2) eoutKnowsECorrect_def)

lemma not_knows_k_not_ine:
assumes "\<not> knows A [kE m]"
shows    "\<not> ine A (kE m)"
using assms by (metis knows2know_neg_k not_know_k_not_ine) 

lemma not_knows_s_not_ine:
assumes "\<not> knows A [sE m]"
shows    "\<not> ine A (sE m)"
using assms by (metis knows2know_neg_s not_know_s_not_ine) 

lemma not_knows_k_not_eout:
assumes "m \<notin> specKeys A"
       and "\<not> knows A [kE m]"
       and "eoutKnowsECorrect A (kE m)"
shows    "\<not> eout A (kE m)"
using assms by (metis eout_knows_nonKS_k)

lemma not_knows_s_not_eout:
assumes "m \<notin> specSecrets A"
       and "\<not> knows A [sE m]"
       and "eoutKnowsECorrect A (sE m)"
shows    "\<not> eout A (sE m)"
using assms by (metis eout_knows_nonKS_s) 

lemma  adv_not_knows1:
assumes "out P \<subseteq> ins A"
       and "\<not> knows A [kE m]"
shows    "\<not> eout P (kE m)"
using assms by (metis adv_not_know1 knows2know_neg_k)

lemma adv_not_knows2:
assumes "out P  \<subseteq> ins A"
        and "\<not> knows A [sE m]" 
shows    "\<not> eout P (sE m)"
using assms by (metis adv_not_know2 knows2know_neg_s)

lemma knows_decomposition_1_k:
assumes "kKS a \<notin> specKeysSecrets P"
       and "kKS a \<notin> specKeysSecrets Q"
       and "subcomponents PQ = {P, Q}"
       and "knows PQ [kE a]"
       and "correctCompositionIn PQ"
       and "correctCompositionLoc PQ"
shows "knows P [kE a] \<or> knows Q [kE a]"
using assms by (metis know_decomposition knows1k)

lemma knows_decomposition_1_s:
assumes "sKS a \<notin> specKeysSecrets P"
       and "sKS a \<notin> specKeysSecrets Q"
       and "subcomponents PQ = {P, Q}"
       and "knows PQ [sE a]"
       and "correctCompositionIn PQ"
       and "correctCompositionLoc PQ"
shows "knows P [sE a] \<or> knows Q [sE a]"
using assms by (metis know_decomposition knows1s)

lemma knows_decomposition_1:
assumes "subcomponents PQ = {P, Q}"
       and "knows PQ [a]"
       and "correctCompositionIn PQ"
       and "correctCompositionLoc PQ"
       and "(\<exists> z. a = kE z) \<or> (\<exists> z. a = sE z)"
       and "\<forall> z. a = kE z \<longrightarrow> 
         kKS z \<notin> specKeysSecrets P \<and> kKS z \<notin> specKeysSecrets Q"
       and h7:"\<forall> z. a = sE z \<longrightarrow> 
         sKS z \<notin> specKeysSecrets P \<and> sKS z \<notin> specKeysSecrets Q"
shows "knows P [a] \<or> knows Q [a]"
using assms
by (metis knows_decomposition_1_k knows_decomposition_1_s) 

lemma knows_composition1_k:
assumes "(kKS m) \<notin> specKeysSecrets P"
       and "(kKS m) \<notin> specKeysSecrets Q"
       and "knows P [kE m]"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ" 
       and "correctCompositionKS PQ"
shows "knows PQ [kE m]"
using assms by (metis know_composition knows1k)

lemma knows_composition1_s:
assumes "(sKS m) \<notin> specKeysSecrets P"
       and "(sKS m) \<notin> specKeysSecrets Q"
       and "knows P [sE m]"
       and "subcomponents PQ = {P,Q}" 
       and "correctCompositionIn PQ"
       and "correctCompositionKS PQ"
shows "knows PQ [sE m]"
using assms by (metis know_composition knows1s)

lemma knows_composition2_k:
assumes "(kKS m) \<notin> specKeysSecrets P"
       and "(kKS m) \<notin> specKeysSecrets Q"
       and "knows Q [kE m]"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ" 
       and "correctCompositionKS PQ"
shows "knows PQ [kE m]"
using assms
by (metis know2knowsPQ_k know_composition knows2know_k)

lemma knows_composition2_s:
assumes "(sKS m) \<notin> specKeysSecrets P"
       and "(sKS m) \<notin> specKeysSecrets Q"
       and "knows Q [sE m]"
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "correctCompositionKS PQ" 
shows "knows PQ [sE m]"
using assms
by (metis know2knowsPQ_s know_composition knows2know_s)

lemma knows_composition_neg1_k:
assumes "kKS m \<notin> specKeysSecrets P"
       and "kKS m \<notin> specKeysSecrets Q"
       and "\<not> knows P [kE m]"
       and "\<not> knows Q [kE m]" 
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionLoc PQ"
       and "correctCompositionIn PQ"
       and "correctCompositionKS PQ" 
shows "\<not> knows PQ [kE m]"
using assms by (metis know_decomposition knows1k)

lemma knows_composition_neg1_s:
assumes "sKS m \<notin> specKeysSecrets P"
       and "sKS m \<notin> specKeysSecrets Q"
       and "\<not> knows P [sE m]"
       and "\<not> knows Q [sE m]" 
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionLoc PQ"
       and "correctCompositionIn PQ"
       and "correctCompositionKS PQ" 
shows "\<not> knows PQ [sE m]"
using assms by (metis knows_decomposition_1_s)

lemma knows_concat_1:
assumes "knows P (a # e)"
shows    "knows P [a]"
using assms by (metis append_Cons append_Nil knows2)

lemma knows_concat_2:
assumes "knows P (a # e)"
shows    "knows P e"
using assms by (metis append_Cons append_Nil knows2a)

lemma knows_concat_3:
assumes "knows P [a]"
       and "knows P e"
shows "knows P (a # e)"
using assms by (metis append_Cons append_Nil knows3)

lemma not_knows_conc_knows_elem_not_knows_tail:
assumes "\<not> knows P (a # e)"
       and "knows P [a]"
shows "\<not> knows P e"
using assms by (metis knows_concat_3)
    
lemma not_knows_conc_not_knows_elem_tail:
assumes "\<not> knows P (a#e)"
shows    "\<not> knows P [a] \<or> \<not> knows P e"
using assms by (metis append_Cons append_Nil knows3)

lemma not_knows_elem_not_knows_conc:
assumes "\<not> knows P [a]"
shows    "\<not> knows P (a # e)"
using assms by (metis knows_concat_1)

lemma not_knows_tail_not_knows_conc:
assumes "\<not> knows P e"
shows    "\<not> knows P (a # e)"
using assms by (metis knows_concat_2)

lemma knows_composition3:
 fixes e::"Expression list"
 assumes "knows P e"
     and subPQ:"subcomponents PQ = {P,Q}"
     and cCompI:"correctCompositionIn PQ"
     and cCompKS:"correctCompositionKS PQ"
     and "\<forall> (m::Expression). ((m mem e) \<longrightarrow> 
            ((\<exists> z1. m = (kE z1)) \<or> (\<exists> z2. m = (sE z2))))"
     and "notSpecKeysSecretsExpr P e"
     and "notSpecKeysSecretsExpr Q e" 
 shows "knows PQ e"
using assms
proof (induct e)
  case Nil 
  from this show ?case by (simp only: knows_emptyexpression)
next
  fix a l 
  case (Cons a l)
  from Cons have sg1:"knows P [a]" by (simp add: knows_concat_1)
  from Cons have sg2:"knows P l" by (simp only: knows_concat_2)
  from sg1 have sg3:"a mem (a # l)" by simp
  from Cons and sg2 have sg2a:"knows PQ l" 
    by (simp add: notSpecKeysSecretsExpr_L2)
  from Cons and sg1 and sg2 and sg3 show ?case
  proof (cases "\<exists> z1. a = kE z1")
    assume "\<exists> z1. a = (kE z1)"
    from this obtain z where a1:"a = (kE z)" by auto
    from a1 and Cons have sg4:"(kKS z) \<notin> specKeysSecrets P"
      by (simp add: notSpecKeysSecretsExpr_def)
    from a1 and Cons have sg5:"(kKS z) \<notin> specKeysSecrets Q" 
      by (simp add: notSpecKeysSecretsExpr_def)
    from sg1 and a1 have sg6:"knows P [kE z]" by simp
    from sg4 and sg5 and sg6 and subPQ and cCompI and cCompKS  
      have "knows PQ [kE z]" 
      by (rule knows_composition1_k)
    from this and sg2a and a1 show ?case by (simp add: knows_concat_3)
  next 
    assume "\<not> (\<exists>z1. a = kE z1)"
    from this and Cons and sg3 have "\<exists> z2. a = (sE z2)" by auto
    from this obtain z where a2:"a = (sE z)" by auto
    from a2 and Cons have sg8:"(sKS z) \<notin> specKeysSecrets P" 
      by (simp add: notSpecKeysSecretsExpr_def)
    from a2 and Cons have sg9:"(sKS z) \<notin> specKeysSecrets Q"
      by (simp add: notSpecKeysSecretsExpr_def)
    from sg1 and a2 have sg10:"knows P [sE z]" by simp 
    from sg8 and sg9 and sg10 and subPQ and cCompI and cCompKS  
      have "knows PQ [sE z]" 
      by (rule knows_composition1_s)
    from this and sg2a and a2 show ?case by (simp add: knows_concat_3)
  qed 
qed 
 
lemma knows_composition4:
 assumes "knows Q e"
     and subPQ:"subcomponents PQ = {P,Q}" 
     and cCompI:"correctCompositionIn PQ"
     and cCompKS:"correctCompositionKS PQ"
     and "\<forall> m. m mem e \<longrightarrow> ((\<exists> z. m = kE z) \<or> (\<exists> z. m = sE z))"
     and "notSpecKeysSecretsExpr P e"
     and "notSpecKeysSecretsExpr Q e" 
 shows "knows PQ e"
using assms
proof (induct e)
  case Nil 
  from this show ?case by (simp only: knows_emptyexpression)
next
  fix a l 
  case (Cons a l)
  from Cons have sg1:"knows Q [a]" by (simp add: knows_concat_1)
  from Cons have sg2:"knows Q l" by (simp only: knows_concat_2)
  from sg1 have sg3:"a mem (a # l)" by simp
  from Cons and sg2 have sg2a:"knows PQ l" 
    by (simp add: notSpecKeysSecretsExpr_L2)
  from Cons and sg1 and sg2 and sg3 show ?case
  proof (cases "\<exists> z1. a = kE z1")
    assume "\<exists> z1. a = (kE z1)"
    from this obtain z where a1:"a = (kE z)" by auto
    from a1 and Cons have sg4:"(kKS z) \<notin> specKeysSecrets P"
      by (simp add: notSpecKeysSecretsExpr_def)
    from a1 and Cons have sg5:"(kKS z) \<notin> specKeysSecrets Q"
      by (simp add: notSpecKeysSecretsExpr_def)
    from sg1 and a1 have sg6:"knows Q [kE z]" by simp
    from sg4 and sg5 and sg6 and subPQ and cCompI and cCompKS 
      have "knows PQ [kE z]" 
      by (rule knows_composition2_k)
    from this and sg2a and a1 show ?case by (simp add: knows_concat_3)
  next 
    assume "\<not> (\<exists>z1. a = kE z1)"
    from this and Cons and sg3 have "\<exists> z2. a = (sE z2)" by auto
    from this obtain z where a2:"a = (sE z)" by auto
    from a2 and Cons have sg8:"(sKS z) \<notin> specKeysSecrets P"
      by (simp add: notSpecKeysSecretsExpr_def)
    from a2 and Cons have sg9:"(sKS z) \<notin> specKeysSecrets Q"
      by (simp add: notSpecKeysSecretsExpr_def)
    from sg1 and a2 have sg10:"knows Q [sE z]" by simp 
    from sg8 and sg9 and sg10 and subPQ and cCompI and cCompKS  
      have "knows PQ [sE z]" 
      by (rule knows_composition2_s)
    from this and sg2a and a2 show ?case by (simp add: knows_concat_3)
  qed 
qed

lemma knows_composition5:
assumes "knows P e \<or> knows Q e" 
       and "subcomponents PQ = {P,Q}"
       and "correctCompositionIn PQ"
       and "correctCompositionKS PQ"
       and "\<forall> m. m mem e \<longrightarrow> ((\<exists> z. m = kE z) \<or> (\<exists> z. m = sE z))"
       and "notSpecKeysSecretsExpr P e"
       and "notSpecKeysSecretsExpr Q e" 
shows "knows PQ e"
using assms 
by (metis knows_composition3 knows_composition4)

end 
