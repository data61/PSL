section \<open>Execution rules for kernels\<close>

theory KPL_execution_kernel imports 
  KPL_execution_group
begin

text \<open>Inter-group race detection\<close>
definition kernel_race 
  :: "gid set \<Rightarrow> (gid \<rightharpoonup> group_state) \<Rightarrow> bool"
where "kernel_race G \<kappa> \<equiv> 
  \<exists>i \<in> G. \<exists>j \<in> G. i \<noteq> j \<and> 
  (snd ` (W_group (the (\<kappa> i)))) \<inter> 
  (snd ` (R_group (the (\<kappa> j))) \<union> snd ` (W_group (the (\<kappa> j)))) \<noteq> {}"

text \<open>Replaces top-level @{term Break} with \<open>v := true\<close>\<close>
fun belim :: "stmt \<Rightarrow> V \<Rightarrow> stmt"
where 
  "belim (Basic b) v = Basic b"
| "belim (S1 ;; S2) v = (belim S1 v ;; belim S2 v)"
| "belim (Local n S) v = Local n (belim S v)"
| "belim (If e S1 S2) v = If e (belim S1 v) (belim S2 v)"
| "belim (While e S) v = While e S" (* only top-level *)
(* belim (WhileDyn e S) v = undefined *)
| "belim (Call f e) v = Call f e"
| "belim Barrier v = Barrier"
| "belim Break v = Basic (Assign (Var v) eTrue)"
| "belim Continue v = Continue"
| "belim Return v = Return"

text \<open>Replaces top-level @{term Continue} with \<open>v := true\<close>\<close>
fun celim :: "stmt \<Rightarrow> V \<Rightarrow> stmt"
where 
  "celim (Basic b) v = Basic b"
| "celim (S1 ;; S2) v = (celim S1 v ;; celim S2 v)"
| "celim (Local n S) v = Local n (celim S v)"
| "celim (If e S1 S2) v = If e (celim S1 v) (celim S2 v)"
| "celim (While e S) v = While e S" (* only top-level *)
(* celim (WhileDyn e S) v = undefined *)
| "celim (Call f e) v = Call f e"
| "celim Barrier v = Barrier"
| "celim Break v = Break"
| "celim Continue v = Basic (Assign (Var v) eTrue)"
| "celim Return v = Return"

text \<open>@{term "subst_basic_stmt n v loc"} replaces @{term n} with @{term v} inside @{term loc}\<close>
fun subst_loc :: "name \<Rightarrow> V \<Rightarrow> loc \<Rightarrow> loc"
where
  "subst_loc n v (Var w) = Var w"
| "subst_loc n v (Name m) = (if n = m then Var v else Name m)"

text \<open>@{term "subst_local_expr n v e"} replaces @{term n} with @{term v} inside @{term e}\<close>
fun subst_local_expr 
  :: "name \<Rightarrow> V \<Rightarrow> local_expr \<Rightarrow> local_expr"
where
  "subst_local_expr n v (Loc loc) = Loc (subst_loc n v loc)"
| "subst_local_expr n v Gid = Gid"
| "subst_local_expr n v Lid = Lid"
| "subst_local_expr n v eTrue = eTrue"
| "subst_local_expr n v (e1 \<and>* e2) = 
  (subst_local_expr n v e1 \<and>* subst_local_expr n v e2)"
| "subst_local_expr n v (\<not>* e) = \<not>* (subst_local_expr n v e)"

text \<open>@{term "subst_basic_stmt n v b"} replaces @{term n} with @{term v} inside @{term b}\<close>
fun subst_basic_stmt :: "name \<Rightarrow> V \<Rightarrow> basic_stmt \<Rightarrow> basic_stmt"
where 
  "subst_basic_stmt n v (Assign loc e) = 
  Assign (subst_loc n v loc) (subst_local_expr n v e)"
| "subst_basic_stmt n v (Read loc e) =
  Read (subst_loc n v loc) (subst_local_expr n v e)"
| "subst_basic_stmt n v (Write e1 e2) =
  Write (subst_local_expr n v e1) (subst_local_expr n v e2)"

text \<open>@{term "subst_stmt n v s t"} holds if @{term t} is the result 
  of replacing @{term n} with @{term v} inside @{term s}\<close>
inductive subst_stmt :: "name \<Rightarrow> V \<Rightarrow> stmt \<Rightarrow> stmt \<Rightarrow> bool"
where 
  "subst_stmt n v (Basic b) (Basic (subst_basic_stmt n v b))"
| "\<lbrakk> subst_stmt n v S1 S1' ; subst_stmt n v S2 S2' \<rbrakk> \<Longrightarrow>
  subst_stmt n v (S1 ;; S2) (S1' ;; S2')"
| "\<lbrakk> m \<noteq> n ; subst_stmt n v S S' \<rbrakk> \<Longrightarrow> 
  subst_stmt n v (Local m S) (Local m S')"
| "\<lbrakk> subst_stmt n v S1 S1' ; subst_stmt n v S2 S2' \<rbrakk> \<Longrightarrow> 
  subst_stmt n v (If e S1 S2) (If e S1' S2')"
| "subst_stmt n v S S' \<Longrightarrow> subst_stmt n v (While e S) (While e S')" 
(* subst_stmt n v (WhileDyn e S) undefined *)
| "subst_stmt n v (Call f e) (Call f e)"
| "subst_stmt n v Barrier Barrier"
| "subst_stmt n v Break Break"
| "subst_stmt n v Continue Continue"
| "subst_stmt n v Return Return"

text \<open>@{term "param_subst f u"} replaces @{term f}'s parameter with @{term u}\<close>
definition param_subst :: "proc list \<Rightarrow> proc_name \<Rightarrow> V \<Rightarrow> stmt"
where "param_subst fs f u \<equiv> 
  let proc = THE proc. proc \<in> set fs \<and> proc_name proc = f in
  THE S'. subst_stmt (param proc) u (body proc) S'"

text \<open>Replace @{term "Return"} with \<open>v := true\<close>\<close>
fun relim :: "stmt \<Rightarrow> V \<Rightarrow> stmt"
where 
  "relim (Basic b) v = Basic b"
(* Additional rule for adversarial abstraction (Fig 7b) *)
| "relim (S1 ;; S2) v = (relim S1 v ;; relim S2 v)"
| "relim (Local n S) v = Local n (relim S v)"
| "relim (If e S1 S2) v = If e (relim S1 v) (relim S2 v)"
| "relim (While e S) v = While e (relim S v)"
(* relim (WhileDyn e S) v = undefined *)
| "relim (Call f e) v = Call f e"
| "relim Barrier v = Barrier"
| "relim Break v = Break"
| "relim Continue v = Continue"
| "relim Return v = Basic (Assign (Var v) eTrue)"

text \<open>Fresh variables\<close>
definition fresh :: "V \<Rightarrow> V list \<Rightarrow> bool"
where "fresh v vs \<equiv> v \<notin> set vs"

text \<open>The rules of Figure 6\<close>
inductive step_k
  :: "abs_level \<Rightarrow> proc list \<Rightarrow> threadset \<Rightarrow> kernel_state \<Rightarrow> kernel_state option \<Rightarrow> bool"
where
  K_Inter_Group_Race:
  "\<lbrakk> \<forall>i \<in> G. step_g a i T (the (\<kappa> i), (Basic b, p)) (Some (the (\<kappa>' i))) ;
     kernel_race P \<kappa>' \<rbrakk> \<Longrightarrow>
  step_k a fs (G,T) (\<kappa>, (Basic b, p) # ss, vs) None"
| K_Intra_Group_Race:
  "\<lbrakk> i \<in> G; step_g a i T (the (\<kappa> i), (Basic s, p)) None \<rbrakk> \<Longrightarrow>
  step_k a fs (G,T) (\<kappa>, (Basic s, p) # ss, vs) None"
| K_Basic:
  "\<lbrakk> \<forall>i \<in> G. step_g a i T (the (\<kappa> i), (Basic b, p)) (Some (the (\<kappa>' i))) ;
     \<not> (kernel_race G \<kappa>') \<rbrakk> \<Longrightarrow>
  step_k a fs (G,T) (\<kappa>, (Basic b, p) # ss, vs) (Some (\<kappa>',ss, vs))"
| K_Divergence:
  "\<lbrakk> i \<in> G; step_g a i T (the (\<kappa> i), (Barrier, p)) None \<rbrakk> \<Longrightarrow>
  step_k a fs (G,T) (\<kappa>, (Barrier, p) # ss, vs) None"
| K_Sync:
  "\<lbrakk> \<forall>i \<in> G. step_g a i T (the (\<kappa> i), (Barrier, p)) (Some (the (\<kappa>' i))) ;
     \<not> (kernel_race G \<kappa>') \<rbrakk> \<Longrightarrow>
  step_k a fs (G,T) (\<kappa>, (Barrier, p) # ss, vs) (Some (\<kappa>',ss, vs))"
| K_Seq:
  "step_k a fs (G,T) (\<kappa>, (S1 ;; S2, p) # ss, vs) 
  (Some (\<kappa>, (S1, p) # (S2, p) # ss, vs))"
| K_Var:
  "fresh v vs \<Longrightarrow> 
  step_k a fs (G,T) (\<kappa>, (Local n S, p) # ss, vs)  
  (Some (\<kappa>, (THE S'. subst_stmt n v S S', p) # ss, v # vs))"
| K_If: 
  "fresh v vs \<Longrightarrow> 
  step_k a fs (G,T) (\<kappa>, (If e S1 S2, p) # ss, vs) (Some (\<kappa>, 
  (Basic (Assign (Var v) e), p) 
  # (S1, p \<and>* Loc (Var v)) 
  # (S2, p \<and>* \<not>* (Loc (Var v))) # ss, v # vs))"
| K_Open:
  "fresh v vs \<Longrightarrow>
  step_k a fs (G,T) (\<kappa>, (While e S, p) # ss, vs) (Some (\<kappa>, 
  (WhileDyn e (belim S v), p \<and>* \<not>* (Loc (Var v))) # ss, v # vs))"
| K_Iter:
  "\<lbrakk> i \<in> G ; j \<in> the (T i) ; 
  eval_bool (p \<and>* e) (the ((the (\<kappa> i))\<^sub>t\<^sub>s j)) ; 
  fresh u vs ; fresh v vs; u \<noteq> v \<rbrakk> \<Longrightarrow>
  step_k a fs (G,T) (\<kappa>, (WhileDyn e S, p) # ss, vs) (Some (\<kappa>, 
  (Basic (Assign (Var u) e), p) 
  # (celim S v, p \<and>* Loc (Var u) \<and>* \<not>* (Loc (Var v))) 
  # (WhileDyn e S, p) # ss, u # v # vs))"
| K_Done:
  "\<forall>i \<in> G. \<forall>j \<in> the (T i). 
  \<not> (eval_bool (p \<and>* e) (the ((the (\<kappa> i))\<^sub>t\<^sub>s j))) \<Longrightarrow>
  step_k a fs (G,T) (\<kappa>, (WhileDyn e S, p) # ss, vs) (Some (\<kappa>, ss, vs))"
| K_Call: 
  "\<lbrakk> fresh u vs ; fresh v vs ; u \<noteq> v ; s = param_subst fs f u \<rbrakk> \<Longrightarrow>
  step_k a fs (G,T) (\<kappa>, (Call f e, p) # ss, vs ) 
  (Some (\<kappa>, (Basic (Assign (Var u) e) ;; relim s v, 
  p \<and>* \<not>* (Loc (Var v))) # ss, u # v # vs))"



end
