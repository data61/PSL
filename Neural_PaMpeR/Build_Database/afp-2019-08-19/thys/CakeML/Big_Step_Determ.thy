chapter "Relational big-step semantics"

section "Determinism"

theory Big_Step_Determ
imports Semantic_Extras
begin

lemma evaluate_determ:
  "evaluate_match ck env s v pes v' r1a \<Longrightarrow> evaluate_match ck env s v pes v' r1b \<Longrightarrow> r1a = r1b"
  "evaluate_list ck env s es r2a \<Longrightarrow> evaluate_list ck env s es r2b \<Longrightarrow> r2a = r2b"
  "evaluate ck env s e r3a \<Longrightarrow> evaluate ck env s e r3b \<Longrightarrow> r3a = r3b"
proof (induction arbitrary: r1b and r2b and r3b rule: evaluate_match_evaluate_list_evaluate.inducts)
  case (raise1 ck s1 e env s2 v1)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (Raise e) r3b", auto)
next
  case (raise2 ck s1 e env s2 err)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (Raise e) r3b", auto)
next
  case (handle1 ck env s2 s1 e v1 pes)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (Handle e pes) r3b", auto)
next
  case (handle2 ck s1 s2 env e pes v1 bv)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (Handle e pes) r3b"; fastforce)
next
  case (handle3 ck s1 s2 env e pes a)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (Handle e pes) r3b"; auto)
next
  case (con1 ck env cn es vs s s' v1)
  then show ?case
    by - (ind_cases "evaluate ck env s (Con cn es) r3b"; fastforce)
next
  case (con2 ck env cn es s)
  then show ?case
    by - (ind_cases "evaluate ck env s (Con cn es) r3b", auto)
next
  case (con3 ck env cn es err s s')
  then show ?case
    by - (ind_cases "evaluate ck env s (Con cn es) r3b", auto)
next
  case (app1 ck env es vs env' e bv s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (App Opapp es) r3b"; fastforce)
next
  case (app2 ck env es vs env' e s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (App Opapp es) r3b"; force)
next
  case (app3 ck env es vs s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (App Opapp es) r3b"; force)
next
  case (app4 ck env op0 es vs res s1 s2 refs' ffi')
  then show ?case
    by - (ind_cases "evaluate ck env s1 (App op0 es) r3b"; fastforce)
next
  case (app5 ck env op0 es vs s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (App op0 es) r3b"; force)
next
  case (app6 ck env op0 es err s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (App op0 es) r3b"; force)
next
  case (log1 ck env op0 e1 e2 v1 e' bv s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (Log op0 e1 e2) r3b"; fastforce)
next
  case (log2 ck env op0 e1 e2 v1 bv s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (Log op0 e1 e2) r3b"; force)
next
  case (log3 ck env op0 e1 e2 v1 s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (Log op0 e1 e2) r3b"; force)
next
  case (log4 ck env op0 e1 e2 err s s')
  then show ?case
    by - (ind_cases "evaluate ck env s (Log op0 e1 e2) r3b"; auto)
next
  case (if1 ck env e1 e2 e3 v1 e' bv s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (If e1 e2 e3) r3b"; fastforce)
next
  case (if2 ck env e1 e2 e3 v1 s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (If e1 e2 e3) r3b"; force)
next
  case (if3 ck env e1 e2 e3 err s s')
  then show ?case
    by - (ind_cases "evaluate ck env s (If e1 e2 e3) r3b", auto)
next
  case (mat1 ck env e pes v1 bv s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (Mat e pes) r3b"; fastforce)
next
  case (mat2 ck env e pes err s s')
  then show ?case
    by - (ind_cases "evaluate ck env s (Mat e pes) r3b", auto)
next
  case (let1 ck env n e1 e2 v1 bv s1 s2)
  then show ?case
    by - (ind_cases "evaluate ck env s1 (Let n e1 e2) r3b"; fastforce)
next
  case (let2 ck env n e1 e2 err s s')
  then show ?case
    by - (ind_cases "evaluate ck env s (Let n e1 e2) r3b", auto)
next
  case (letrec1 ck env funs e bv s)
  then show ?case
    by - (ind_cases "evaluate ck env s (Letrec funs e) r3b"; fastforce)
next
  case (letrec2 ck env funs e s)
  then show ?case
    by - (ind_cases "evaluate ck env s (Letrec funs e) r3b", auto)
next
  case (tannot ck env e t0 s bv)
  then show ?case
    by - (ind_cases "evaluate ck env s (Tannot e t0) r3b", auto)
next
  case (locannot ck env e l s bv)
  then show ?case
    by - (ind_cases "evaluate ck env s (Lannot e l) r3b", auto)
next
  case (cons1 ck env e es v1 vs s1 s2 s3)
  then show ?case
    by - (ind_cases "evaluate_list ck env s1 (e # es) r2b", auto)
next
  case (cons2 ck env e es err s s')
  then show ?case
    by - (ind_cases "evaluate_list ck env s (e # es) r2b", auto)
next
  case (cons3 ck env e es v1 err s1 s2 s3)
  then show ?case
    by - (ind_cases "evaluate_list ck env s1 (e # es) r2b", auto)
next
  case (mat_cons1 ck env env' v1 p pes e bv err_v s)
  then show ?case
    by - (ind_cases "evaluate_match ck env s v1 ((p, e) # pes) err_v r1b"; fastforce)
next
  case (mat_cons2 ck env v1 p e pes bv s err_v)
  then show ?case
    by - (ind_cases "evaluate_match ck env s v1 ((p, e) # pes) err_v r1b"; fastforce)
next
  case (mat_cons3 ck env v1 p e pes s err_v)
  then show ?case
    by - (ind_cases "evaluate_match ck env s v1 ((p, e) # pes) err_v r1b", auto)
next
  case (mat_cons4 ck env v1 p e pes s err_v)
  then show ?case
    by - (ind_cases "evaluate_match ck env s v1 ((p, e) # pes) err_v r1b", auto)
qed (auto elim: evaluate.cases evaluate_list.cases evaluate_match.cases)

end