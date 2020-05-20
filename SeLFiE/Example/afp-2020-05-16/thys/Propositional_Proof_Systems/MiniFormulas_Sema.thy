theory MiniFormulas_Sema
imports MiniFormulas Sema
begin

lemma "A \<Turnstile> F \<longleftrightarrow> A \<Turnstile> to_mini_formula F"
  by(induction F) auto

end
