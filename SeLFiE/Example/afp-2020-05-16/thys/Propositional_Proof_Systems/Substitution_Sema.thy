theory Substitution_Sema
imports Substitution Sema
begin

lemma substitution_lemma: "\<A> \<Turnstile> F[G / n] \<longleftrightarrow> \<A>(n := \<A> \<Turnstile> G) \<Turnstile> F" by(induction F; simp)

end
