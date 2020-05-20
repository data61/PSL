subsection \<open>Binders for the option type \label{sect:binders}\<close>

theory Option_Binders
  imports Main
begin

text \<open>
  The following functions are used as binders in the theorems that are proven.
  At all times, when a result is None, the theorem becomes vacuously true.
  The expression ``$m \rightharpoonup \alpha$'' means ``First compute $m$, if it is None then return True, otherwise pass the result to $\alpha$''.
  B2 is a short hand for sequentially doing two independent computations. The following syntax is associated to B2:
  ``$m_1 || m_2 \rightharpoonup \alpha$'' represents ``First compute $m_1$ and $m_2$, if one of them is None then return True, otherwise pass the result to $\alpha$''.
\<close>
definition B :: "'a option \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> bool" (infixl "\<rightharpoonup>" 65)
where "B m \<alpha> \<equiv> case m of None \<Rightarrow> True | (Some a) \<Rightarrow> \<alpha> a"

definition B2 :: "'a option \<Rightarrow> 'a option \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
where "B2 m1 m2 \<alpha> \<equiv> m1 \<rightharpoonup> (\<lambda> a . m2 \<rightharpoonup> (\<lambda> b . \<alpha> a b))"

syntax "B2" :: "['a option, 'a option, ('a \<Rightarrow> 'a \<Rightarrow> bool)] => bool" ("(_ \<parallel> _ \<rightharpoonup> _)"  [0, 0, 10] 10)


  
text \<open>
  Some rewriting rules for the binders
\<close>
lemma rewrite_B2_to_cases[simp]:
  shows "B2 s t f = (case s of None \<Rightarrow> True | (Some s1) \<Rightarrow> (case t of None \<Rightarrow> True | (Some t1) \<Rightarrow> f s1 t1))"
unfolding B2_def B_def by(cases s,cases t,simp+)
lemma rewrite_B_None[simp]:
  shows "None \<rightharpoonup> \<alpha> = True"
unfolding B_def by(auto)
lemma rewrite_B_m_True[simp]:
  shows "m \<rightharpoonup> (\<lambda> a . True) = True"
unfolding B_def by(cases m,simp+)
lemma rewrite_B2_cases:
  shows "(case a of None \<Rightarrow> True | (Some s) \<Rightarrow> (case b of None \<Rightarrow> True | (Some t) \<Rightarrow> f s t))
          = (\<forall> s t . a = (Some s) \<and> b = (Some t) \<longrightarrow> f s t)"
by(cases a,simp,cases b,simp+)

definition strict_equal :: "'a option \<Rightarrow> 'a \<Rightarrow> bool"
where "strict_equal m a \<equiv> case m of None \<Rightarrow> False | (Some a') \<Rightarrow> a' = a"

end
