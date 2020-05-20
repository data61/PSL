section\<open>Inductive Study of Confidentiality against the General Attacker\<close>

theory  ConfidentialityGA imports NS_Public_Bad_GA begin

text\<open>New subsidiary lemmas to reason on a generic agent initial state\<close>

lemma parts_initState: "parts(initState C) = initState C"
by (cases C, simp)

lemma analz_initState: "analz(initState C) = initState C"
by (cases C, force dest: analz_into_parts)


text\<open>Generalising over all initial secrets the existing treatment, which is limited to private encryption keys\<close>

definition staticSecret :: "agent \<Rightarrow> msg set" where
 [simp]: "staticSecret A == {Key (priEK A), Key (priSK A), Key (shrK A)}"


text\<open>More subsidiary lemmas combining initial secrets and knowledge of generic agent\<close>

lemma staticSecret_in_initState [simp]:
"staticSecret A \<subseteq> initState A"
by (cases A, simp)
thm parts_insert

lemma staticSecretA_notin_initStateB:
"m \<in> staticSecret A \<Longrightarrow> m \<in> initState B = (A=B)"
by (cases B, auto)

lemma staticSecretA_notin_parts_initStateB:
"m \<in> staticSecret A \<Longrightarrow> m \<in> parts(initState B) = (A=B)"
by (cases B, auto)

lemma staticSecretA_notin_analz_initStateB:
"m \<in> staticSecret A \<Longrightarrow> m \<in> analz(initState B) = (A=B)"
by (cases B, force dest: analz_into_parts)

lemma staticSecret_synth_eq: 
"m \<in> staticSecret A \<Longrightarrow> (m \<in> synth H) = (m \<in> H)"
apply force
done

declare staticSecret_def [simp del]

lemma nonce_notin_analz_initState:
  "Nonce N \<notin> analz(initState A)" 
by(cases A, auto dest: analz_into_parts)


subsection\<open>Protocol independent study\<close>

lemma staticSecret_parts_agent:
 "\<lbrakk>m \<in> parts (knows C evs); m \<in> staticSecret A\<rbrakk> \<Longrightarrow>  
   A=C \<or> 
  (\<exists>D E X. Says D E X \<in> set evs \<and> m \<in> parts{X}) \<or>
  (\<exists>Y. Notes C Y \<in> set evs \<and> m \<in> parts{Y})"
apply (erule rev_mp)
apply (induct_tac evs)
txt\<open>@{subgoals [display,indent =1]}\<close>
apply (simp add: staticSecretA_notin_parts_initStateB)
apply (induct_tac a)
(*Says*) 
apply (rule impI) 
apply simp
apply (drule parts_insert [THEN equalityD1, THEN subsetD])
apply blast
(*Gets*)
apply simp
(*Notes*)
apply simp
apply clarify 
txt\<open>@{subgoals [display,indent =1]}\<close>
apply (drule parts_insert [THEN equalityD1, THEN subsetD])
apply blast
done

lemma staticSecret_analz_agent:
 "\<lbrakk>m \<in> analz (knows C evs); m \<in> staticSecret A\<rbrakk> \<Longrightarrow>  
   A=C \<or> 
  (\<exists>D E X. Says D E X \<in> set evs \<and> m \<in> parts{X}) \<or>
  (\<exists>Y. Notes C Y \<in> set evs \<and> m \<in> parts{Y})"
by (drule analz_into_parts [THEN staticSecret_parts_agent])

lemma secret_parts_agent:
 "m \<in> parts (knows C evs)  \<Longrightarrow> m \<in> initState C \<or>
 (\<exists>A B X. Says A B X \<in> set evs \<and> m \<in> parts{X}) \<or>
 (\<exists>Y. Notes C Y \<in> set evs \<and> m \<in> parts{Y})"
apply (erule rev_mp)
apply (induct_tac "evs")
apply (simp add: parts_initState)
apply (induct_tac "a")
(*Says*)
apply (rule impI)
apply simp
apply (drule parts_insert [THEN equalityD1, THEN subsetD])
apply blast
(*Gets*)
apply simp
(*Notes*)
apply simp 
apply clarify
apply (drule parts_insert [THEN equalityD1, THEN subsetD])
apply blast
done

subsection\<open>Protocol dependent study\<close>

(*NS_no_Notes moved up in NS_Public_Bad_GA.thy so that it's visible to a sibling theory of this one's

As with DolevYao, studying a guarantee similar to
NS_no_Says_staticSecret makes the specialisation proof strategy collapse, because it elicits the same assumptions of the theorem that should be specified.
*)

lemma NS_staticSecret_parts_agent_weak:
 "\<lbrakk>m \<in> parts (knows C evs); m \<in> staticSecret A; 
   evs \<in> ns_public\<rbrakk> \<Longrightarrow>
  A=C \<or> (\<exists>D E X. Says D E X \<in> set evs \<and> m \<in> parts{X})"
apply (blast dest: NS_no_Notes staticSecret_parts_agent)
done

text\<open>Can't prove the homologous theorem of NS\_Says\_Spy\_staticSecret, hence the specialisation proof strategy cannot be applied\<close>

(*Simple though illustrative corollary*)
(*note use of Says_imp_knows, an enforcement of the threat model*)
lemma NS_staticSecret_parts_agent_parts:
"\<lbrakk>m \<in> parts (knows C evs); m \<in> staticSecret A; A\<noteq>C; evs \<in> ns_public\<rbrakk> \<Longrightarrow>
  m \<in> parts(knows D evs)"
apply (blast dest: NS_staticSecret_parts_agent_weak Says_imp_knows [THEN parts.Inj] parts_trans)
(*Alternative proof
apply (blast dest: staticSecret_parts_agent NS_no_Notes Says_imp_knows [THEN parts.Inj] parts_trans)*)
done

text\<open>
The previous theorems show that in general any agent could send anybody's initial secret, namely the threat model does not impose anything against it. However, the actual protocol specification will, where agents either follow the protocol or build messages out of their traffic analysis - this is actually the same in DY

Therefore, we are only left with the direct proof strategy.
\<close>

lemma NS_staticSecret_parts_agent:
 "\<lbrakk>m \<in> parts (knows C evs); m \<in> staticSecret A; 
   C\<noteq>A; evs \<in> ns_public\<rbrakk>
 \<Longrightarrow> \<exists> B X. Says A B X \<in> set evs \<and> m \<in> parts {X}"
apply (erule rev_mp, erule ns_public.induct)
(*Nil*)
apply (simp add: staticSecretA_notin_parts_initStateB)
(*Fake*)
apply simp
apply clarify
apply (drule parts_insert [THEN equalityD1, THEN subsetD])(*shot1*)
apply (case_tac "Aa=A") 
apply clarify
txt\<open>@{subgoals [display,indent=1,goals_limit=2]}\<close>
apply blast
(*Aa\<noteq>A*)
apply simp
apply clarify (*applies induction hypothesis!*)(*shot2*)
txt\<open>@{subgoals [display,indent=1,goals_limit=1]}\<close>
apply (drule Fake_parts_sing [THEN subsetD], simp)  (*shot3*)
apply (simp add: staticSecret_synth_eq) 
txt\<open>@{subgoals [display,indent=1,goals_limit=1]}\<close>
apply (blast dest: NS_staticSecret_parts_agent_parts)
(*rest!*)
apply (force simp add: staticSecret_def)+
done


lemma NS_agent_see_staticSecret:
 "\<lbrakk>m \<in> staticSecret A; C\<noteq>A; evs \<in> ns_public\<rbrakk>
 \<Longrightarrow> m \<in> parts (knows C evs) = (\<exists> B X. Says A B X \<in> set evs \<and> m \<in> parts {X})"
apply (force dest: NS_staticSecret_parts_agent Says_imp_knows [THEN parts.Inj] intro: parts_trans)
done


declare analz.Decrypt [rule del]

lemma analz_insert_analz: "
\<lbrakk> c \<notin> parts{Z}; \<forall>K. Key K \<notin> parts{Z}; c \<in> analz(insert Z H)\<rbrakk> \<Longrightarrow> c \<in> analz H"
apply (erule rev_mp, erule rev_mp)
apply (erule analz.induct)
prefer 4
apply clarify
txt\<open>@{subgoals [display,indent=1,goals_limit=1]}\<close>
apply (blast dest: parts.Body analz.Decrypt)
apply blast+
done

lemma Agent_not_see_NA:
     "\<lbrakk> Key (priEK B) \<notin> analz(knows C evs); 
        Key (priEK A) \<notin> analz(knows C evs);
        \<forall>S R Y. Says S R Y \<in> set evs \<longrightarrow> 
         Y = Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<or>
         Y = Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace> \<or>
         Nonce NA \<notin> parts{Y} \<and> (\<forall>K. Key K \<notin> parts{Y});
        C\<noteq>A; C\<noteq>B;  evs \<in> ns_public\<rbrakk>                     
       \<Longrightarrow> Nonce NA \<notin> analz (knows C evs)"
apply (erule rev_mp, erule rev_mp, erule rev_mp, erule ns_public.induct) 
apply (simp add: nonce_notin_analz_initState)
apply clarify
apply simp
(*fixing confidentiality of both private keys*)
apply (drule subset_insertI [THEN analz_mono, THEN contra_subsetD])+
txt\<open>@{subgoals [display,indent=1,goals_limit=1]}\<close>
apply (subgoal_tac "
        \<forall>S R Y.
           (S = Aa \<and> R = Ba \<and> Y = X \<longrightarrow>
            X = Crypt (pubK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<or>
            X = Crypt (pubK A) \<lbrace>Nonce NA, Nonce NB\<rbrace> \<or>
            Nonce NA \<notin> parts {X} \<and> (\<forall>K. Key K \<notin> parts {X}))")
prefer 2 
apply blast 
apply simp
txt\<open>@{subgoals [display,indent=1,goals_limit=1]}\<close>
apply (force dest!: analz_insert_analz)
(*Alternative proof
apply (erule disjE) apply simp 
apply (erule disjE) apply simp 
apply (blast dest: analz_insert_analz)
*)
apply auto
done



end

