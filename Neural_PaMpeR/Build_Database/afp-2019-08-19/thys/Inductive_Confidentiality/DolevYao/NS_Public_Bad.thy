section\<open>The Needham-Schroeder Public-Key Protocol against Dolev-Yao --- with Gets event, hence with Reception rule\<close>

theory NS_Public_Bad imports Public begin

inductive_set ns_public :: "event list set"
  where
         (*Initial trace is empty*)
   Nil:  "[] \<in> ns_public"

         (*The spy MAY say anything he CAN say.  We do not expect him to
           invent new nonces here, but he can also use NS1.  Common to
           all similar protocols.*)
 | Fake: "\<lbrakk>evsf \<in> ns_public;  X \<in> synth (analz (knows Spy evsf))\<rbrakk>
          \<Longrightarrow> Says Spy B X  # evsf \<in> ns_public"

         (*A message that is sent may be received*)
 | Reception: "\<lbrakk>evsr \<in> ns_public; Says A B X \<in> set evsr\<rbrakk>
                \<Longrightarrow> Gets B X # evsr \<in> ns_public"

         (*Alice initiates a protocol run, sending a nonce to Bob*)
 | NS1:  "\<lbrakk>evs1 \<in> ns_public;  Nonce NA \<notin> used evs1\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>)
                # evs1  \<in>  ns_public"

         (*Bob responds to Alice's message with a further nonce*)
 | NS2:  "\<lbrakk>evs2 \<in> ns_public;  Nonce NB \<notin> used evs2;
           Gets B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs2\<rbrakk>
          \<Longrightarrow> Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>)
                # evs2  \<in>  ns_public"

         (*Alice proves her existence by sending NB back to Bob.*)
 | NS3:  "\<lbrakk>evs3 \<in> ns_public;
           Says A  B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs3;
           Gets A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs3\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubEK B) (Nonce NB)) # evs3 \<in> ns_public"

declare knows_Spy_partsEs [elim] thm knows_Spy_partsEs
declare analz_into_parts [dest]
declare Fake_parts_insert_in_Un [dest]

(*A "possibility property": there are traces that reach the end*)
lemma "\<exists>NB. \<exists>evs \<in> ns_public. Says A B (Crypt (pubEK B) (Nonce NB)) \<in> set evs"
apply (intro exI bexI)
apply (rule_tac [2] ns_public.Nil [THEN ns_public.NS1, THEN ns_public.Reception, 
                                   THEN ns_public.NS2, THEN ns_public.Reception, 
                                   THEN ns_public.NS3])
by possibility


text\<open>Lemmas about reception invariant: if a message is received it certainly
was sent\<close>
lemma Gets_imp_Says :
     "\<lbrakk> Gets B X \<in> set evs; evs \<in> ns_public \<rbrakk> \<Longrightarrow> \<exists>A. Says A B X \<in> set evs"
apply (erule rev_mp)
apply (erule ns_public.induct)
apply auto
done

lemma Gets_imp_knows_Spy: 
     "\<lbrakk> Gets B X \<in> set evs; evs \<in> ns_public \<rbrakk>  \<Longrightarrow> X \<in> knows Spy evs"
apply (blast dest!: Gets_imp_Says Says_imp_knows_Spy)
done

lemma Gets_imp_knows_Spy_parts[dest]:
    "\<lbrakk> Gets B X \<in> set evs; evs \<in> ns_public \<rbrakk>  \<Longrightarrow> X \<in> parts (knows Spy evs)"
apply (blast dest: Gets_imp_knows_Spy [THEN parts.Inj])
done

(**** Inductive proofs about ns_public ****)

(** Theorems of the form X \<notin> parts (knows Spy evs) imply that NOBODY
    sends messages containing X! **)

(*Spy never sees another agent's private key! (unless it's bad at start)*)
lemma Spy_see_priEK [simp]: 
      "evs \<in> ns_public \<Longrightarrow> (Key (priEK A) \<in> parts (knows Spy evs)) = (A \<in> bad)"
by (erule ns_public.induct, auto)

lemma Spy_analz_priEK [simp]: 
      "evs \<in> ns_public \<Longrightarrow> (Key (priEK A) \<in> analz (knows Spy evs)) = (A \<in> bad)"
by auto


(*** Authenticity properties obtained from NS2 ***)

(*It is impossible to re-use a nonce in both NS1 and NS2, provided the nonce
  is secret.  (Honest users generate fresh nonces.)*)
lemma no_nonce_NS1_NS2 [rule_format]: 
      "evs \<in> ns_public 
       \<Longrightarrow> Crypt (pubEK C) \<lbrace>NA', Nonce NA\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>
           Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>  
           Nonce NA \<in> analz (knows Spy evs)"
apply (erule ns_public.induct, simp_all)
apply (blast intro: analz_insertI)+
done


(*Unicity for NS1: nonce NA identifies agents A and B*)
lemma unique_NA: 
     "\<lbrakk>Crypt(pubEK B)  \<lbrace>Nonce NA, Agent A \<rbrace> \<in> parts(knows Spy evs);  
       Crypt(pubEK B') \<lbrace>Nonce NA, Agent A'\<rbrace> \<in> parts(knows Spy evs);  
       Nonce NA \<notin> analz (knows Spy evs); evs \<in> ns_public\<rbrakk>
      \<Longrightarrow> A=A' \<and> B=B'"
apply (erule rev_mp, erule rev_mp, erule rev_mp)   
apply (erule ns_public.induct, simp_all)
(*Fake, NS1*)
apply (blast intro!: analz_insertI)+
done


(*Secrecy: Spy does not see the nonce sent in msg NS1 if A and B are secure
  The major premise "Says A B ..." makes it a dest-rule, so we use
  (erule rev_mp) rather than rule_format. *)
theorem Spy_not_see_NA: 
      "\<lbrakk>Says A B (Crypt(pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs;
        A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                     
       \<Longrightarrow> Nonce NA \<notin> analz (knows Spy evs)"
apply (erule rev_mp)   
apply (erule ns_public.induct, simp_all, spy_analz)
apply (blast dest: unique_NA intro: no_nonce_NS1_NS2)+
done


(*Authentication for A: if she receives message 2 and has used NA
  to start a run, then B has sent message 2.*)
lemma A_trusts_NS2_lemma [rule_format]: 
   "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                     
    \<Longrightarrow> Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>
        Says A B (Crypt(pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs \<longrightarrow>
        Says B A (Crypt(pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs"
apply (erule ns_public.induct)
apply (auto dest: Spy_not_see_NA unique_NA)
done

theorem A_trusts_NS2: 
     "\<lbrakk>Says A  B (Crypt(pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs;   
       Gets A (Crypt(pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs;
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                     
      \<Longrightarrow> Says B A (Crypt(pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs"
by (blast intro: A_trusts_NS2_lemma)


(*If the encrypted message appears then it originated with Alice in NS1*)
lemma B_trusts_NS1 [rule_format]:
     "evs \<in> ns_public                                         
      \<Longrightarrow> Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace> \<in> parts (knows Spy evs) \<longrightarrow>
          Nonce NA \<notin> analz (knows Spy evs) \<longrightarrow>
          Says A B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs"
apply (erule ns_public.induct, simp_all)
(*Fake*)
apply (blast intro!: analz_insertI)
done



(*** Authenticity properties obtained from NS2 ***)

(*Unicity for NS2: nonce NB identifies nonce NA and agent A
  [proof closely follows that for unique_NA] *)
lemma unique_NB [dest]: 
     "\<lbrakk>Crypt(pubEK A)  \<lbrace>Nonce NA, Nonce NB\<rbrace> \<in> parts(knows Spy evs);
       Crypt(pubEK A') \<lbrace>Nonce NA', Nonce NB\<rbrace> \<in> parts(knows Spy evs);
       Nonce NB \<notin> analz (knows Spy evs); evs \<in> ns_public\<rbrakk>
     \<Longrightarrow> A=A' \<and> NA=NA'"
apply (erule rev_mp, erule rev_mp, erule rev_mp)   
apply (erule ns_public.induct, simp_all)
(*Fake, NS2*)
apply (blast intro!: analz_insertI)+
done


(*NB remains secret PROVIDED Alice never responds with round 3*)
theorem Spy_not_see_NB [dest]:
     "\<lbrakk>Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs;   
       \<forall>C. Says A C (Crypt (pubEK C) (Nonce NB)) \<notin> set evs;       
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                      
     \<Longrightarrow> Nonce NB \<notin> analz (knows Spy evs)"
apply (erule rev_mp, erule rev_mp)
apply (erule ns_public.induct, simp_all, spy_analz)
apply (simp_all add: all_conj_distrib) (*speeds up the next step*)
apply (blast intro: no_nonce_NS1_NS2)+
done


(*Authentication for B: if he receives message 3 and has used NB
  in message 2, then A has sent message 3--to somebody....*)

lemma B_trusts_NS3_lemma [rule_format]:
     "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                    
      \<Longrightarrow> Crypt (pubEK B) (Nonce NB) \<in> parts (knows Spy evs) \<longrightarrow>
          Says B A  (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs \<longrightarrow>
          (\<exists>C. Says A C (Crypt (pubEK C) (Nonce NB)) \<in> set evs)"
apply (erule ns_public.induct, auto)
by (blast intro: no_nonce_NS1_NS2)+

theorem B_trusts_NS3:
     "\<lbrakk>Says B A  (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs;
       Gets B (Crypt (pubEK B) (Nonce NB)) \<in> set evs;             
       A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>                    
      \<Longrightarrow> \<exists>C. Says A C (Crypt (pubEK C) (Nonce NB)) \<in> set evs"
by (blast intro: B_trusts_NS3_lemma)


(*Can we strengthen the secrecy theorem Spy_not_see_NB?  NO*)
lemma "\<lbrakk>A \<notin> bad;  B \<notin> bad;  evs \<in> ns_public\<rbrakk>            
       \<Longrightarrow> Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs  
           \<longrightarrow> Nonce NB \<notin> analz (knows Spy evs)"
apply (erule ns_public.induct, simp_all, spy_analz)
(*NS1: by freshness*)
apply blast
(*NS2: by freshness and unicity of NB*)
apply (blast intro: no_nonce_NS1_NS2)
(*NS3: unicity of NB identifies A and NA, but not B*)
apply clarify
apply (frule_tac A' = A in 
       Says_imp_knows_Spy [THEN parts.Inj, THEN unique_NB], auto)
apply (rename_tac evs3 B' C)
txt\<open>This is the attack!
@{subgoals[display,indent=0,margin=65]}
\<close>
oops

end
