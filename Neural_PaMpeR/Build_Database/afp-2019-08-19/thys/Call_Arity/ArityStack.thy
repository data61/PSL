theory ArityStack
imports Arity SestoftConf
begin

fun Astack :: "stack \<Rightarrow> Arity"
  where "Astack [] = 0"
      | "Astack (Arg x # S) = inc\<cdot>(Astack S)"
      | "Astack (Alts e1 e2 # S) = 0"
      | "Astack (Upd x # S) = 0"
      | "Astack (Dummy x # S) = 0"

lemma Astack_restr_stack_below:
  "Astack (restr_stack V S) \<sqsubseteq> Astack S"
  by (induction V S rule: restr_stack.induct) auto

lemma Astack_map_Dummy[simp]:
  "Astack (map Dummy l) = 0"
by (induction l) auto

lemma Astack_append_map_Dummy[simp]:
  "Astack S' = 0 \<Longrightarrow> Astack (S @ S') = Astack S"
by (induction S rule: Astack.induct) auto


end
