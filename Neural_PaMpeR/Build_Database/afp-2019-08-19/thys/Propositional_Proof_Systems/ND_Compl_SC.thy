subsection\<open>An alternate proof of ND completeness\<close>
theory ND_Compl_SC
imports SC_Sema ND_Sound SCND Compactness
begin

lemma ND_sound_complete_countable:
  fixes \<Gamma> :: "'a :: countable formula set"
  shows "\<Gamma> \<turnstile> F \<longleftrightarrow> \<Gamma> \<TTurnstile> F" (is "?n \<longleftrightarrow> ?s")
proof
  assume ?n thus ?s by (fact ND_sound)
next
  assume s: ?s
  with compact_entailment obtain \<Gamma>' where 0: "finite \<Gamma>'" "\<Gamma>' \<TTurnstile> F" "\<Gamma>' \<subseteq> \<Gamma>" 
    unfolding entailment_def by metis
  then obtain \<Gamma>'' where \<Gamma>'': "\<Gamma>' = set_mset \<Gamma>''" using finite_set_mset_mset_set by blast
  have su: "set_mset \<Gamma>'' \<subseteq> \<Gamma>" using 0  \<Gamma>'' by fast
  from 0 have "\<Turnstile> \<Gamma>'' \<Rightarrow> {#F#}" unfolding sequent_semantics_def entailment_def \<Gamma>'' by simp
  with SC_sound_complete have "\<Gamma>'' \<Rightarrow> {#F#}" by blast
  with SCND have "set_mset \<Gamma>'' \<union> \<^bold>\<not> ` set_mset {#F#} \<turnstile> \<bottom>" .
  thus ?n using ND.CC Weaken[OF _ su[THEN insert_mono]] by force
qed
  
text\<open>If you do not like the requirement that our atoms are countable,
you can also restrict yourself to a finite set of assumptions.\<close>
  
lemma ND_sound_complete_finite:
  assumes "finite \<Gamma>"
  shows "\<Gamma> \<turnstile> F \<longleftrightarrow> \<Gamma> \<TTurnstile> F" (is "?n \<longleftrightarrow> ?s")
proof
  assume ?n thus ?s by (fact ND_sound)
next
  assume s: ?s
  then obtain \<Gamma>'' where \<Gamma>'': "\<Gamma> = set_mset \<Gamma>''" using finite_set_mset_mset_set assms by blast
  have su: "set_mset \<Gamma>'' \<subseteq> \<Gamma>" using \<Gamma>'' by fast
  have "\<Turnstile> \<Gamma>'' \<Rightarrow> {#F#}" using s unfolding sequent_semantics_def entailment_def \<Gamma>'' by auto
  with SC_sound_complete have "\<Gamma>'' \<Rightarrow> {#F#}" by blast
  with SCND have "set_mset \<Gamma>'' \<union> \<^bold>\<not> ` set_mset {#F#} \<turnstile> \<bottom>" .
  thus ?n using ND.CC Weaken[OF _ su[THEN insert_mono]] by force
qed

end
