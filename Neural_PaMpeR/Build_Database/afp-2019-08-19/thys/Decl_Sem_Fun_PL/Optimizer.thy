section "Correctness of an optimizer"

theory Optimizer
  imports Lambda DenotEqualitiesFSet
begin

fun is_value :: "exp \<Rightarrow> bool" where
  "is_value (ENat n) = True" |
  "is_value (ELam x e) = (FV e = {})" |
  "is_value _ = False"

lemma is_value_is_val[simp]: "is_value e \<Longrightarrow> isval e \<and> FV e = {}"
  by (case_tac e) auto

fun opt :: "exp \<Rightarrow> nat \<Rightarrow> exp" where
  "opt (EVar x) k = EVar x" |
  "opt (ENat n) k = ENat n" |
  "opt (ELam x e) k = ELam x (opt e k)" |
  "opt (EApp e1 e2) 0 = EApp (opt e1 0) (opt e2 0)" | 
  "opt (EApp e1 e2) (Suc k) = 
    (let e1' = opt e1 (Suc k) in let e2' = opt e2 (Suc k) in
     (case e1' of
        ELam x e \<Rightarrow> if is_value e2' then opt (subst x e2' e) k
                   else EApp e1' e2'
     | _ \<Rightarrow> EApp e1' e2'))" |
  "opt (EPrim f e1 e2) k = 
    (let e1' = opt e1 k in let e2' = opt e2 k in
    (case (e1', e2') of
       (ENat n1, ENat n2) \<Rightarrow> ENat (f n1 n2)
    | _ \<Rightarrow> EPrim f e1' e2'))" |
  "opt (EIf e1 e2 e3) k = 
    (let e1' = opt e1 k in let e2' = opt e2 k in let e3' = opt e3 k in
    (case e1' of
      ENat n \<Rightarrow> if n = 0 then e3' else e2'
    | _ \<Rightarrow> EIf e1' e2' e3'))"

lemma opt_correct_aux: "E e = E (opt e k)"
proof (induction e k rule: opt.induct)
  case (5 e1 e2 k)
  then show ?case
    apply (cases "opt e1 (Suc k)") 
         apply force
        apply force
       prefer 2 apply force
      prefer 2 apply force
     prefer 2 apply force
    apply (rename_tac x e)
    apply (cases "is_value (opt e2 (Suc k))")   
     apply (subgoal_tac "E (EApp (ELam x e) (opt e2 (Suc k))) 
                       = E (subst x (opt e2 (Suc k)) e)")
      prefer 2 apply (rule eval_app_lam)
      apply (simp del: E.simps) 
     apply (subgoal_tac "E(EApp e1 e2) = E(EApp (ELam x e) (opt e2 (Suc k)))")
      prefer 2 
      apply (rule e_app_cong)
       apply force+ done
next
  case (6 f e1 e2 k)
  then show ?case apply auto apply (cases "opt e1 k") apply auto
    apply (cases "opt e2 k") apply auto done
next
  case (7 e1 e2 e3 k)
  then show ?case by (cases "opt e1 k") auto
qed auto

theorem opt_correct: "e \<simeq> opt e k"
  using opt_correct_aux denot_sound_wrt_ctx_equiv by blast
   
end
