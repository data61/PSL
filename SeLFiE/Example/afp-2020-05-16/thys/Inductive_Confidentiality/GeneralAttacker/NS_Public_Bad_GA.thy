section\<open>The Needham-Schroeder Public-Key Protocol against the General Attacker\<close>

theory NS_Public_Bad_GA imports PublicGA begin

inductive_set ns_public :: "event list set"
  where

   Nil:  "[] \<in> ns_public"

 | Fake: "\<lbrakk>evsf \<in> ns_public;  X \<in> synth (analz (knows A evsf))\<rbrakk>
          \<Longrightarrow> Says A B X  # evsf \<in> ns_public"

 | Reception: "\<lbrakk> evsr \<in> ns_public; Says A B X \<in> set evsr \<rbrakk>
                \<Longrightarrow> Gets B X # evsr \<in> ns_public"

 | NS1:  "\<lbrakk>evs1 \<in> ns_public;  Nonce NA \<notin> used evs1\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>)
                # evs1  \<in>  ns_public"

 | NS2:  "\<lbrakk>evs2 \<in> ns_public;  Nonce NB \<notin> used evs2;
           Gets B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs2\<rbrakk>
          \<Longrightarrow> Says B A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>)
                # evs2  \<in>  ns_public"

 | NS3:  "\<lbrakk>evs3 \<in> ns_public;
           Says A  B (Crypt (pubEK B) \<lbrace>Nonce NA, Agent A\<rbrace>) \<in> set evs3;
           Gets A (Crypt (pubEK A) \<lbrace>Nonce NA, Nonce NB\<rbrace>) \<in> set evs3\<rbrakk>
          \<Longrightarrow> Says A B (Crypt (pubEK B) (Nonce NB)) # evs3 \<in> ns_public"


lemma NS_no_Notes:
 "evs \<in> ns_public \<Longrightarrow> Notes A X \<notin> set evs"
apply (erule ns_public.induct)
apply (simp_all)
done

text\<open>Confidentiality treatment in separate theory file\<close>

end
