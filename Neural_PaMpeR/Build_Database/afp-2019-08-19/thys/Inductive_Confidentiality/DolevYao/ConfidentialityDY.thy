section\<open>Inductive Study of Confidentiality against Dolev-Yao\<close>

theory ConfidentialityDY imports NS_Public_Bad begin

section\<open>Existing study - fully spelled out\<close>

text\<open>In order not to leave hidden anything of the line of reasoning, we cancel some relevant lemmas that were installed previously\<close>

declare Spy_see_priEK [simp del]
        Spy_analz_priEK [simp del]
        analz_into_parts [rule del]
        
subsection\<open>On static secrets\<close>

lemma Spy_see_priEK: 
      "evs \<in> ns_public \<Longrightarrow> (Key (priEK A) \<in> parts (spies evs)) = (A \<in> bad)"
apply (erule ns_public.induct, simp_all)
(*Fake: screenshot1*)
apply (cases "A:bad")
thm ccontr
(*apply (rule ccontr) apply simp*)
apply blast (*Spy knows bad agents' keys since start*)
apply clarify (*screenshot2*)
thm Fake_parts_insert [THEN subsetD]
apply (drule Fake_parts_insert [THEN subsetD], simp)(*screenshot3*)
apply (blast dest: analz_into_parts)
done

lemma Spy_analz_priEK: 
      "evs \<in> ns_public \<Longrightarrow> (Key (priEK A) \<in> analz (spies evs)) = (A \<in> bad)"
(*apply (auto simp: Spy_see_priEK dest: analz_into_parts)*)
apply (erule ns_public.induct, simp_all)
(*Nil*)
thm analz_image_freshK_simps
apply (simp add: analz_image_freshK_simps)
(*Fake*)
(*apply spy_analz would close, alternatively:*)
apply (cases "A:bad")
apply clarify apply simp
apply blast (*Spy knows bad agents' keys since start*)
apply clarsimp 
apply (drule Fake_analz_insert [THEN subsetD], simp)
apply clarsimp
done

subsection\<open>On dynamic secrets\<close>

lemma Spy_not_see_NA: 
"\<lbrakk>Says A B (Crypt(pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs;
  A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                     
  \<Longrightarrow> Nonce NA \<notin> analz (spies evs)"
apply (erule rev_mp, erule ns_public.induct) 
apply (simp_all add: Spy_analz_priEK)
(*screenshot1*)
thm conjI
apply (rule conjI)
apply clarify
apply clarify
(*screenshot2*)
apply (drule Fake_analz_insert [THEN subsetD], simp)
(*screenshot3*)
apply simp
apply (blast dest: unique_NA analz_into_parts intro: no_nonce_NS1_NS2)+
done

lemma Spy_not_see_NB:
"\<lbrakk>Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs;   
 \<forall>C. Says A C (Crypt (pubEK C) (Nonce NB)) \<notin> set evs;      
 A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                      
 \<Longrightarrow> Nonce NB \<notin> analz (spies evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule ns_public.induct)
apply (simp_all add: Spy_analz_priEK)
txt\<open>apply @{term spy_analz}  
   is replaced here with the following list...\<close>
apply (rule ccontr)
apply clarsimp
apply (erule disjE)
apply simp
apply simp
apply clarify
apply (drule Fake_analz_insert [THEN subsetD], simp)
apply simp
txt\<open>...of commands!\<close>
apply (simp_all add: all_conj_distrib) txt\<open>speeds up next\<close>
apply (blast dest: analz_into_parts intro: no_nonce_NS1_NS2)+
done


section\<open>Novel study\<close>

text\<open>Generalising over all initial secrets the existing treatment, which is limited to private encryption keys\<close>

definition staticSecret :: "agent \<Rightarrow> msg set" where
 [simp]: "staticSecret A \<equiv> {Key (priEK A), Key (priSK A), Key (shrK A)}"


subsection\<open>Protocol independent study\<close>

text\<open>Converse doesn't hold because something that is said or noted is not necessarily an initial secret\<close>
lemma staticSecret_parts_Spy:
"\<lbrakk>m \<in> parts (knows Spy evs); m \<in> staticSecret A\<rbrakk>  \<Longrightarrow>
 A \<in> bad \<or>
 (\<exists>C B X. Says C B X \<in> set evs \<and> m \<in> parts{X}) \<or>
 (\<exists>C Y. Notes C Y \<in> set evs \<and> C \<in> bad \<and> m \<in> parts{Y})"
apply (erule rev_mp)
apply (induct_tac "evs") 
apply force
apply (induct_tac "a")
txt\<open>Says\<close>
txt\<open>@{subgoals [display,indent=1]}\<close>
apply (rule impI)
apply simp
txt\<open>@{subgoals [display,indent=1]}\<close>
apply (drule parts_insert [THEN equalityD1, THEN subsetD])
txt\<open>@{subgoals [display,indent=1]}\<close>
apply blast
txt\<open>Gets\<close>
apply simp
txt\<open>Notes\<close>
apply (rule impI)
apply simp
apply (rename_tac agent msg)
apply (case_tac "agent\<notin>bad") 
apply simp apply blast
apply simp
apply (drule parts_insert [THEN equalityD1, THEN subsetD])
apply blast
done

lemma staticSecret_analz_Spy:
"\<lbrakk>m \<in> analz (knows Spy evs); m \<in> staticSecret A\<rbrakk>  \<Longrightarrow>
 A \<in> bad \<or>
 (\<exists>C B X. Says C B X \<in> set evs \<and> m \<in> parts{X}) \<or>
 (\<exists>C Y. Notes C Y \<in> set evs \<and> C \<in> bad \<and> m \<in> parts{Y})"
by (drule analz_into_parts [THEN staticSecret_parts_Spy])


lemma secret_parts_Spy:
"m \<in> parts (knows Spy evs)  \<Longrightarrow>
 m \<in> initState Spy \<or>
 (\<exists>C B X. Says C B X \<in> set evs \<and> m \<in> parts{X}) \<or>
 (\<exists>C Y. Notes C Y \<in> set evs \<and> C \<in> bad \<and> m \<in> parts{Y})"
apply (erule rev_mp)
apply (induct_tac "evs")
apply simp
apply (induct_tac "a")
txt\<open>Says\<close>
apply (rule impI)
apply (simp del: initState_Spy)
apply (drule parts_insert [THEN equalityD1, THEN subsetD])
apply (simp only: Un_iff)
apply blast
txt\<open>Gets\<close>
apply simp
txt\<open>Notes\<close>
apply (rule impI)
apply (simp del: initState_Spy)
apply (rename_tac agent msg)
apply (case_tac "agent\<notin>bad")
apply (simp del: initState_Spy)
apply blast
apply (simp del: initState_Spy)
apply (drule parts_insert [THEN equalityD1, THEN subsetD])
apply blast
done

lemma secret_parts_Spy_converse:
" m \<in> initState Spy \<or>
 (\<exists>C B X. Says C B X \<in> set evs \<and> m \<in> parts{X}) \<or>
 (\<exists>C Y. Notes C Y \<in> set evs \<and> C \<in> bad \<and> m \<in> parts{Y})
 \<Longrightarrow> m \<in> parts(knows Spy evs)"
apply (erule disjE) 
apply force
apply (erule disjE)
apply (blast dest: Says_imp_knows_Spy [THEN parts.Inj] parts_trans)
 apply (blast dest: Notes_imp_knows_Spy [THEN parts.Inj] parts_trans)
done


lemma secret_analz_Spy:
"m \<in> analz (knows Spy evs)  \<Longrightarrow>
 m \<in> initState Spy \<or>
 (\<exists>C B X. Says C B X \<in> set evs \<and> m \<in> parts{X}) \<or>
 (\<exists>C Y. Notes C Y \<in> set evs \<and> C \<in> bad \<and> m \<in> parts{Y})"
by (blast dest: analz_into_parts secret_parts_Spy)

subsection\<open>Protocol-dependent study\<close>

text\<open>Proving generalised version of @{thm Spy_see_priEK} using same strategy, the "direct" strategy\<close>

lemma NS_Spy_see_staticSecret:
 "\<lbrakk>m \<in> staticSecret A; evs \<in> ns_public\<rbrakk> \<Longrightarrow>
   m \<in> parts(knows Spy evs) = (A \<in> bad)"
apply (erule ns_public.induct)
apply simp_all
prefer 2
apply (cases "A:bad")
apply blast (*Spy knows bad agents' keys since start*)
apply clarify
apply (drule Fake_parts_insert [THEN subsetD], simp)
txt\<open>@{subgoals [display,indent=1,goals_limit=1]}\<close>
apply (blast dest: analz_into_parts)
apply force+
done

text\<open>Seeking a proof of @{thm NS_Spy_see_staticSecret} using an alternative, "specialisation" strategy\<close>

lemma NS_no_Notes:
 "evs \<in> ns_public \<Longrightarrow> Notes A X \<notin> set evs"
apply (erule ns_public.induct)
apply simp_all
done

lemma NS_staticSecret_parts_Spy_weak:
"\<lbrakk>m \<in> parts (knows Spy evs); m \<in> staticSecret A;
  evs \<in> ns_public\<rbrakk> \<Longrightarrow> A \<in> bad \<or>
 (\<exists>C B X. Says C B X \<in> set evs \<and> m \<in> parts{X})"
apply (blast dest: staticSecret_parts_Spy NS_no_Notes)
done

lemma NS_Says_staticSecret:
 "\<lbrakk>Says A B X \<in> set evs; m \<in> staticSecret C; m \<in> parts{X};
   evs \<in> ns_public\<rbrakk> \<Longrightarrow> A=Spy"
apply (erule rev_mp)
apply (erule ns_public.induct)
apply force+
done

text\<open>This generalises @{thm Key_synth_eq}\<close>
lemma staticSecret_synth_eq: 
"m \<in> staticSecret A \<Longrightarrow> (m \<in> synth H) = (m \<in> H)"
apply force
done

lemma NS_Says_Spy_staticSecret:
 "\<lbrakk>Says Spy B X \<in> set evs; m \<in> parts{X};
   m \<in> staticSecret A; evs \<in> ns_public\<rbrakk> \<Longrightarrow> A \<in> bad"
(*
txt{*Alternative start to appreciate that it reduces to @{thm NS_Spy_see_staticSecret}*}
apply (erule rev_mp, erule ns_public.induct)
apply (simp_all del: staticSecret_def)
apply clarify 
txt{*@{subgoals [display,indent=1,goals_limit=1]}*}
apply (drule Fake_parts_sing [THEN subsetD], simp) 
txt{*@{subgoals [display,indent=1,goals_limit=1]}*}
apply (simp del: staticSecret_def add: staticSecret_synth_eq)
txt{*@{subgoals [display,indent=1,goals_limit=1]}*}
oops 
*)
apply (drule Says_imp_knows_Spy [THEN parts.Inj]) 
txt\<open>@{subgoals [display,indent=1,goals_limit=1]}\<close>
apply (drule parts_trans, simp)
apply (rotate_tac -1)
txt\<open>@{subgoals [display,indent=1,goals_limit=1]}\<close>
apply (erule rev_mp)
apply (erule ns_public.induct)
apply simp_all
prefer 2
apply (cases "A:bad")
apply blast (*Spy knows bad agents' keys since start*)
apply clarsimp
apply (drule Fake_parts_insert [THEN subsetD], simp)
apply (blast dest: analz_into_parts)
apply force+
done


text\<open>Here's the specialised version of @{thm staticSecret_parts_Spy}\<close>
lemma NS_staticSecret_parts_Spy:
"\<lbrakk>m \<in> parts (knows Spy evs); m \<in> staticSecret A;
  evs \<in> ns_public\<rbrakk> \<Longrightarrow> A \<in> bad"
apply (drule staticSecret_parts_Spy)
apply assumption
txt\<open>@{subgoals  [display,indent=1]}\<close>
apply (erule disjE) 
(*Case A bad*) 
apply assumption
apply (erule disjE) 
(*Case: Says*)
apply (erule exE)+
txt\<open>@{subgoals  [display,indent=1]}\<close>
apply (case_tac "C=Spy")
apply (blast dest: NS_Says_Spy_staticSecret)
apply (blast dest: NS_Says_staticSecret)
apply (blast dest: NS_no_Notes)
done

text\<open>Concluding the specialisation proof strategy...\<close>
lemma NS_Spy_see_staticSecret_spec:
"\<lbrakk>m \<in> staticSecret A; evs \<in> ns_public\<rbrakk> \<Longrightarrow>
 m \<in> parts (knows Spy evs) = (A \<in> bad)"
txt\<open>one line proof:
apply (force dest: @{term NS_staticSecret_parts_Spy})
\<close>
apply safe
apply (blast dest: NS_staticSecret_parts_Spy)
txt\<open>one line proof: force\<close>
apply simp
apply (erule disjE)
apply clarify
apply (drule_tac b=Encryption and evs=evs in Spy_spies_bad_privateKey)
apply (drule parts.Inj, assumption)
apply (erule disjE)
apply clarify
apply (drule_tac b=Signature and evs=evs in Spy_spies_bad_privateKey)
apply (drule parts.Inj, assumption)
apply clarify
apply (drule_tac evs=evs in Spy_spies_bad_shrK)
apply (drule parts.Inj, assumption)
done


lemma NS_Spy_analz_staticSecret:
"\<lbrakk>m \<in> staticSecret A; evs \<in> ns_public\<rbrakk> \<Longrightarrow>
 m \<in> analz (knows Spy evs) = (A \<in> bad)"
apply (force dest: analz_into_parts NS_staticSecret_parts_Spy)
done

lemma NS_staticSecret_subset_parts_knows_Spy:
"evs \<in> ns_public \<Longrightarrow>
 staticSecret A \<subseteq> parts (knows Spy evs) = (A \<in> bad)"
apply (force dest: NS_staticSecret_parts_Spy)
done

lemma NS_staticSecret_subset_analz_knows_Spy: 
"evs \<in> ns_public \<Longrightarrow>
 staticSecret A \<subseteq> analz (knows Spy evs) = (A \<in> bad)"
apply (force dest: analz_into_parts NS_staticSecret_parts_Spy)
done


end


