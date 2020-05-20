theory ND_Sound
imports ND Sema
begin

lemma BigAndImp: "A \<Turnstile> (\<^bold>\<And>P \<^bold>\<rightarrow> G) \<longleftrightarrow> ((\<forall>F \<in> set P. A \<Turnstile> F) \<longrightarrow> A \<Turnstile> G)"
  by(induction P; simp add: entailment_def)

lemma ND_sound: "\<Gamma> \<turnstile> F \<Longrightarrow> \<Gamma> \<TTurnstile> F"
  by(induction rule: ND.induct; simp add: entailment_def; blast)
(* yeah, Isabelle's facilities are very good with this kind of problem\<dots> maybe we should show one or the other case. *)

end
