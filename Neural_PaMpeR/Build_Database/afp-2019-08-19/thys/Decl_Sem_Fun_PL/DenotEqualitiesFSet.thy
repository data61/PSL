subsection "Denotational equalities regarding reduction" 

theory DenotEqualitiesFSet
  imports DenotCongruenceFSet
begin

theorem eval_prim[simp]: assumes e1:"E e1 = E (ENat n1)" and e2:"E e2 = E (ENat n2)" 
  shows "E(EPrim f e1 e2)=E(ENat (f n1 n2))"
    using e1 e2 by auto 

theorem eval_ifz[simp]: assumes e1: "E e1  = E(ENat 0)" shows "E(EIf e1 e2 e3) = E(e3)"
  using e1 by auto 
 
theorem eval_ifnz[simp]: assumes e1: "E(e1) = E(ENat n)" and nz: "n \<noteq> 0"
  shows "E(EIf e1 e2 e3) = E(e2)"
  using e1 nz by auto 

theorem eval_app_lam: assumes vv: "is_val v"
  shows "E(EApp (ELam x e) v) = E (subst x v e)"
  apply (rule ext) apply (rule equalityI) apply (rule subsetI) 
   apply (subgoal_tac "EApp (ELam x e) v \<longrightarrow> subst x v e") prefer 2 apply (rule beta)
  using vv apply assumption apply (rule subject_reduction) apply assumption apply assumption
  apply (rule subsetI) 
  apply (subgoal_tac "EApp (ELam x e) v \<longrightarrow> subst x v e") prefer 2 apply (rule beta)
  using vv apply assumption apply (rule reverse_step_pres_denot) apply assumption
  apply assumption
  done
  
end
