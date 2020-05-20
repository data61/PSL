section \<open>Small-step semantics of CBV lambda calculus\<close>

theory SmallStepLam
  imports Lambda
begin
  
text\<open>
  The following substitution function is not capture avoiding, so it has a precondition
  that $v$ is closed. With hindsight, we should have used DeBruijn indices instead
  because we also use substitution in the optimizing compiler.
\<close>
fun subst :: "name \<Rightarrow> exp \<Rightarrow> exp \<Rightarrow> exp" where
  "subst x v (EVar y) = (if x = y then v else EVar y)" |
  "subst x v (ENat n) = ENat n" |
  "subst x v (ELam y e) = (if x = y then ELam y e else ELam y (subst x v e))" |
  "subst x v (EApp e1 e2) = EApp (subst x v e1) (subst x v e2)" |
  "subst x v (EPrim f e1 e2) = EPrim f (subst x v e1) (subst x v e2)" |
  "subst x v (EIf e1 e2 e3) = EIf (subst x v e1) (subst x v e2) (subst x v e3)"

inductive isval :: "exp \<Rightarrow> bool" where
  valnat[intro!]: "isval (ENat n)" |
  vallam[intro!]: "isval (ELam x e)"

inductive_cases
  isval_var_inv[elim!]: "isval (EVar x)" and
  isval_app_inv[elim!]: "isval (EApp e1 e2)" and
  isval_prim_inv[elim!]: "isval (EPrim f e1 e2)" and
  isval_if_inv[elim!]: "isval (EIf e1 e2 e3)" 

definition is_val :: "exp \<Rightarrow> bool" where
  "is_val v \<equiv> isval v \<and> FV v = {}"
declare is_val_def[simp]

inductive reduce :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longrightarrow>" 55) where
  beta[intro!]: "\<lbrakk> is_val v \<rbrakk> \<Longrightarrow> EApp (ELam x e) v \<longrightarrow> (subst x v e)" |
  app_left[intro!]: "\<lbrakk> e1 \<longrightarrow> e1' \<rbrakk> \<Longrightarrow> EApp e1 e2 \<longrightarrow> EApp e1' e2" |
  app_right[intro!]: "\<lbrakk> e2 \<longrightarrow> e2' \<rbrakk> \<Longrightarrow> EApp e1 e2 \<longrightarrow> EApp e1 e2'" |
  delta[intro!]: "EPrim f (ENat n1) (ENat n2) \<longrightarrow> ENat (f n1 n2)" |
  prim_left[intro!]: "\<lbrakk> e1 \<longrightarrow> e1' \<rbrakk> \<Longrightarrow> EPrim f e1 e2 \<longrightarrow> EPrim f e1' e2" |
  prim_right[intro!]: "\<lbrakk> e2 \<longrightarrow> e2' \<rbrakk> \<Longrightarrow> EPrim f e1 e2 \<longrightarrow> EPrim f e1 e2'" |
  if_zero[intro!]: "EIf (ENat 0) thn els \<longrightarrow> els" |
  if_nz[intro!]: "n \<noteq> 0 \<Longrightarrow> EIf (ENat n) thn els \<longrightarrow> thn" |
  if_cond[intro!]: "\<lbrakk> cond \<longrightarrow> cond' \<rbrakk> \<Longrightarrow> 
    EIf cond thn els \<longrightarrow> EIf cond' thn els" 

inductive_cases
  red_var_inv[elim!]: "EVar x \<longrightarrow> e" and
  red_int_inv[elim!]: "ENat n \<longrightarrow> e" and
  red_lam_inv[elim!]: "ELam x e \<longrightarrow> e'" and
  red_app_inv[elim!]: "EApp e1 e2 \<longrightarrow> e'"
  
inductive multi_step :: "exp \<Rightarrow> exp \<Rightarrow> bool" (infix "\<longrightarrow>*" 55) where
  ms_nil[intro!]: "e \<longrightarrow>* e" |
  ms_cons[intro!]: "\<lbrakk> e1 \<longrightarrow> e2; e2 \<longrightarrow>* e3 \<rbrakk> \<Longrightarrow> e1 \<longrightarrow>* e3"

definition diverge :: "exp \<Rightarrow> bool" where
  "diverge e \<equiv> (\<forall> e'. e \<longrightarrow>* e' \<longrightarrow> (\<exists> e''. e' \<longrightarrow> e''))"
  
definition stuck :: "exp \<Rightarrow> bool" where
  "stuck e \<equiv> \<not> (\<exists> e'. e \<longrightarrow> e')" 
declare stuck_def[simp]

definition goes_wrong :: "exp \<Rightarrow> bool" where
  "goes_wrong e \<equiv> \<exists> e'. e \<longrightarrow>* e' \<and> stuck e' \<and> \<not> isval e'"
declare goes_wrong_def[simp]

datatype obs = ONat nat | OFun | OBad

fun observe :: "exp \<Rightarrow> obs \<Rightarrow> bool" where
  "observe (ENat n) (ONat n') = (n = n')" |
  "observe (ELam x e) OFun = True" |
  "observe e ob = False" 

definition run :: "exp \<Rightarrow> obs \<Rightarrow> bool" (infix "\<Down>" 52) where
  "run e ob \<equiv> ((\<exists> v. e \<longrightarrow>* v \<and> observe v ob)
              \<or> ((diverge e \<or> goes_wrong e) \<and> ob = OBad))"

lemma val_stuck: fixes e::exp assumes val_e: "isval e" shows "stuck e"
proof (rule classical)
  assume "\<not> stuck e"
  from this obtain e' where red: "e \<longrightarrow> e'" by auto 
  from val_e red have "False" by (case_tac e) auto
  from this show ?thesis ..
qed

lemma subst_fv_aux: assumes fvv: "FV v = {}" shows "FV (subst x v e) \<subseteq> FV e - {x}"
  using fvv
proof (induction e arbitrary: x v rule: exp.induct)
  case (EVar x)
  then show ?case by auto
next
  case (ENat x)
  then show ?case by auto
next
  case (ELam y e)
  then show ?case by (cases "x = y") auto
qed (simp,blast)+
    
lemma subst_fv:  assumes fv_e: "FV e \<subseteq> {x}" and fv_v: "FV v = {}" 
  shows "FV (subst x v e) = {}"
  using fv_e fv_v subst_fv_aux by blast
    
lemma red_pres_fv:  fixes e::exp assumes red: "e \<longrightarrow> e'" and fv: "FV e = {}" shows "FV e' = {}"
  using red fv
proof (induction rule: reduce.induct)
  case (beta v x e)
  then show ?case using subst_fv by auto
qed fastforce+
    
lemma reduction_pres_fv: fixes e::exp assumes r: "e \<longrightarrow>* e'" and fv: "FV e = {}" shows "FV e' = {}"
  using r fv
proof (induction)
  case (ms_nil e)
  then show ?case by blast
next
  case (ms_cons e1 e2 e3)
  then show ?case using red_pres_fv by auto
qed

end
