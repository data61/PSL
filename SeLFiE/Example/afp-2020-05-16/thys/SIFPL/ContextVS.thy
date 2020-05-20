(*File: ContextVS.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory ContextVS imports VS begin
subsection\<open>Contextual closure\<close>

text\<open>\label{sec:contextVS}We show that the notion of security is closed w.r.t.~low
attacking contexts, i.e.~contextual programs into which a
secure program can be substituted and which itself employs only
\emph{obviously} low variables.\<close>

text\<open>Contexts are {\bf IMP} programs with (multiple) designated holes
(represented by constructor $\mathit{Ctxt\_Here}$).\<close>

datatype CtxtProg =
  Ctxt_Hole
| Ctxt_Skip
| Ctxt_Assign Var Expr
| Ctxt_Comp CtxtProg CtxtProg
| Ctxt_If BExpr CtxtProg CtxtProg
| Ctxt_While BExpr CtxtProg
| Ctxt_Call

text\<open>We let $C$, $D$ range over contextual programs. The substitution
operation is defined by structural recursion.\<close>

primrec Fill::"CtxtProg \<Rightarrow> IMP \<Rightarrow> IMP"
where
"Fill Ctxt_Hole c = c" |
"Fill Ctxt_Skip c = Skip" |
"Fill (Ctxt_Assign x e) c = Assign x e" |
"Fill (Ctxt_Comp C1 C2) c = Comp (Fill C1 c) (Fill C2 c)" |
"Fill (Ctxt_If b C1 C2) c = Iff b (Fill C1 c) (Fill C2 c)" |
"Fill (Ctxt_While b C) c = While b (Fill C c)" |
"Fill Ctxt_Call c = Call"

text\<open>Equally obvious are the definitions of the (syntactically)
mentioned variables of arithmetic and boolean expressions.\<close>

primrec EVars::"Expr \<Rightarrow> Var set"
where
"EVars (varE x) = {x}" |
"EVars (valE v) = {}" |
"EVars (opE f e1 e2) = EVars e1 \<union> EVars e2"

lemma low_Eval[rule_format]:
 "(\<forall> x . x \<in> EVars e \<longrightarrow> CONTEXT x = low) \<longrightarrow> 
  (\<forall> s t . s \<approx> t \<longrightarrow> evalE e s = evalE e t)"
(*<*)
apply (induct e)
apply (simp add: twiddle_def)
apply simp
apply clarsimp
done
(*>*)

primrec BVars::"BExpr \<Rightarrow> Var set"
where
"BVars (compB f e1 e2) = EVars e1 \<union> EVars e2"

lemma low_EvalB[rule_format]:
 "(\<forall> x . x \<in> BVars b \<longrightarrow> CONTEXT x = low) \<longrightarrow> 
  (\<forall> s t . s \<approx> t \<longrightarrow> evalB b s = evalB b t)"
(*<*)
apply (induct b)
apply (rename_tac Expr1 Expr2)
apply clarsimp
apply (subgoal_tac "evalE Expr1 s = evalE Expr1 t")
prefer 2 apply (rule low_Eval) apply fast apply assumption
apply (subgoal_tac "evalE Expr2 s = evalE Expr2 t")
prefer 2 apply (rule low_Eval) apply fast apply assumption
apply simp
done
(*>*) 

text\<open>The variables possibly read from during the evaluation of $c$
are denoted by $\mathit{Vars\; c}$. Note that in the clause for
assignments the variable that is assigned to is not included in the
set.\<close>

primrec Vars::"IMP \<Rightarrow> Var set"
where
"Vars Skip = {}" |
"Vars (Assign x e) = EVars e" |
"Vars (Comp c d) = Vars c \<union> Vars d" |
"Vars (While b c) = BVars b \<union> Vars c" |
"Vars (Iff b c d) = BVars b \<union> Vars c \<union> Vars d" |
"Vars Call = {}"

text\<open>For contexts, we define when a set $X$ of variables is an upper
bound for the variables read from.\<close>

primrec CtxtVars::"Var set \<Rightarrow> CtxtProg \<Rightarrow> bool"
where
"CtxtVars X Ctxt_Hole = True" |
"CtxtVars X Ctxt_Skip = True" |
"CtxtVars X (Ctxt_Assign x e) = (EVars e \<subseteq> X)" |
"CtxtVars X (Ctxt_Comp C1 C2) = (CtxtVars X C1 \<and> CtxtVars X C2)" |
"CtxtVars X (Ctxt_If b C1 C2) = (BVars b \<subseteq> X \<and> CtxtVars X C1
                                             \<and>  CtxtVars X C2)" |
"CtxtVars X (Ctxt_While b C) = (BVars b \<subseteq> X \<and> CtxtVars X C)" |
"CtxtVars X Ctxt_Call = True"

(*<*)
lemma Secure_comp: "\<lbrakk>secure c1; secure c2\<rbrakk> \<Longrightarrow> secure (Comp c1 c2)"
apply (unfold secure_def)
apply (rule, rule, rule, rule)
apply (rule, rule, rule)
apply (unfold Sem_def)
apply (erule exE)+
apply (erule Sem_eval_cases)
apply (erule Sem_eval_cases)
apply (erule_tac x=s in allE, rotate_tac -1)
apply (erule_tac x=t in allE, rotate_tac -1)
apply (erule_tac x=r in allE, rotate_tac -1)
apply (erule_tac x=ra in allE)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply (erule_tac x=r in allE, rotate_tac -1)
apply (erule_tac x=ra in allE, rotate_tac -1)
apply (erule_tac x=ss in allE, rotate_tac -1)
apply (erule_tac x=tt in allE)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply assumption
done

lemma Secure_iff:
" \<lbrakk>secure c1; secure c2;
   \<forall> s ss. s \<approx> ss \<longrightarrow> evalB b s = evalB b ss\<rbrakk>
  \<Longrightarrow> secure (Iff b c1 c2)"
apply (unfold secure_def)
apply (rule, rule, rule, rule)
apply (rule, rule, rule)
apply (unfold Sem_def)
apply (erule exE)+
apply (erule_tac x=s in allE, erule_tac x=t in allE, erule impE, assumption)
apply (erule Sem_eval_cases)
apply (erule Sem_eval_cases)
apply (erule_tac x=s in allE, rotate_tac -1)
apply (erule_tac x=t in allE, rotate_tac -1)
apply (erule_tac x=ss in allE, rotate_tac -1)
apply (erule_tac x=tt in allE)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply assumption
apply fast
apply (erule Sem_eval_cases)
apply fast
apply (erule thin_rl)
apply (erule_tac x=s in allE, rotate_tac -1)
apply (erule_tac x=t in allE, rotate_tac -1)
apply (erule_tac x=ss in allE, rotate_tac -1)
apply (erule_tac x=tt in allE)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply assumption
done

lemma secure_while_aux[rule_format]:
"\<forall> n m . n \<le> k \<longrightarrow> m \<le> k \<longrightarrow> 
  (\<forall> s t ss tt . (s , While b c \<rightarrow>\<^sub>n  ss) \<longrightarrow>  
                 (t , While b c \<rightarrow>\<^sub>m  tt) \<longrightarrow> 
                 secure c \<longrightarrow> 
                 (\<forall>s ss. s \<approx> ss \<longrightarrow> evalB b s = evalB b ss) \<longrightarrow> 
                 s \<approx> t \<longrightarrow> ss \<approx> tt)"
apply (induct k)
apply clarsimp apply (drule Sem_no_zero_height_derivs, clarsimp)
apply clarsimp
  apply (subgoal_tac "evalB b s = evalB b t")
  prefer 2 apply (erule thin_rl, fast)
  apply (erule Sem_eval_cases)
  prefer 2 apply (erule Sem_eval_cases, simp, simp) 
  apply (erule Sem_eval_cases) prefer 2 apply simp
    apply clarsimp 
    apply (subgoal_tac "r \<approx> ra", clarsimp) 
    apply (erule thin_rl, unfold secure_def Sem_def) apply fast
done

lemma Secure_while:
" \<lbrakk>secure c;
   \<forall> s ss. s \<approx> ss \<longrightarrow> evalB b s = evalB b ss\<rbrakk>
  \<Longrightarrow> secure (While b c)"
apply (simp (no_asm_simp) add: secure_def)
apply (rule, rule, rule, rule)
apply (rule, rule, rule)
apply (unfold Sem_def) apply (erule exE)+
apply (rule secure_while_aux) 
prefer 3 apply assumption
prefer 6 apply assumption
prefer 3 apply assumption
prefer 3 apply assumption
prefer 3 apply fast
apply (subgoal_tac "n \<le> n + na", assumption) apply (simp, simp)
done
(*>*)

text\<open>A constant representing the procedure body with holes.\<close>

consts Ctxt_Body::CtxtProg

text\<open>The following predicate expresses that all variables read from
by a command $c$ are contained in the set $X$ of low variables.\<close>

definition LOW::"Var set \<Rightarrow> CtxtProg \<Rightarrow> bool"
where "LOW X C = (CtxtVars X C \<and> (\<forall> x . x : X \<longrightarrow> CONTEXT x = low))"

(*<*)
lemma secureI_secureFillI_Aux[rule_format]:
"\<forall> n m . n \<le> k \<longrightarrow> m \<le> k \<longrightarrow> 
       (\<forall> C d s t ss tt X . (s , d \<rightarrow>\<^sub>n t) \<longrightarrow>  
                          (ss , d \<rightarrow>\<^sub>m  tt) \<longrightarrow> 
                          s \<approx> ss \<longrightarrow>  
                          d = Fill C c \<longrightarrow>
                          LOW X C \<longrightarrow>
                          LOW X Ctxt_Body \<longrightarrow>
                          body = Fill Ctxt_Body c \<longrightarrow> secure c \<longrightarrow> t \<approx> tt)"
apply (induct k)
apply clarsimp apply (drule Sem_no_zero_height_derivs, clarsimp)
apply clarsimp
apply (case_tac C)
(*Ctxt_Hole*)
apply clarsimp defer 1 
(*Ctxt_Skip*)
apply clarsimp
  apply (erule Sem_eval_cases)+ apply clarsimp
(*Ctxt_Assign*)
apply clarsimp
  apply (erule thin_rl)
  apply (erule Sem_eval_cases)+ apply clarsimp
  apply (simp add: update_def LOW_def twiddle_def) apply clarsimp apply (rule low_Eval) 
      apply fast
    apply (simp add: twiddle_def)
(*Ctxt_Comp*)
apply clarsimp apply (erule Sem_eval_cases) apply (erule Sem_eval_cases) apply clarsimp 
  apply (subgoal_tac "r \<approx> ra")
  prefer 2 apply (simp add: LOW_def) 
           apply (erule_tac x=na in allE, clarsimp)
  apply (simp add: LOW_def) 
           apply (erule_tac x=ma in allE, clarsimp)
(*Ctxt_If*)
apply (rename_tac BExpr u v)
apply clarsimp
  apply (subgoal_tac "evalB BExpr s = evalB BExpr ss")
  prefer 2 apply (erule thin_rl, case_tac BExpr, clarsimp)
           apply (rename_tac Expr1 Expr2)
           apply (subgoal_tac "evalE Expr1 s = evalE Expr1 ss", clarsimp)
           apply (subgoal_tac "evalE Expr2 s = evalE Expr2 ss", clarsimp)
           apply (rule low_Eval) apply (simp add: LOW_def) apply fast apply clarsimp
           apply (rule low_Eval) apply (simp add: LOW_def) apply fast apply clarsimp
  apply (erule Sem_eval_cases) apply (erule Sem_eval_cases) prefer 2 apply clarsimp apply clarsimp
  apply (simp add: LOW_def) 
           apply (erule_tac x=na in allE, clarsimp)
  apply (erule Sem_eval_cases) apply clarsimp
  apply (simp add: LOW_def) 
           apply (erule_tac x=na in allE, clarsimp)
(*Ctxt_While*)
apply (rename_tac BExpr CtxtProg)
apply clarsimp 
  apply (subgoal_tac "evalB BExpr s = evalB BExpr ss")
  prefer 2 apply (erule thin_rl, case_tac BExpr, clarsimp)
           apply (rename_tac Expr1 Expr2)
           apply (subgoal_tac "evalE Expr1 s = evalE Expr1 ss", clarsimp)
           apply (subgoal_tac "evalE Expr2 s = evalE Expr2 ss", clarsimp)
           apply (rule low_Eval) apply (simp add: LOW_def) apply fast apply clarsimp
           apply (rule low_Eval) apply (simp add: LOW_def) apply fast apply clarsimp 
  apply (erule Sem_eval_cases) apply (erule Sem_eval_cases) prefer 2 apply clarsimp
  apply (subgoal_tac "r \<approx> ra")
  prefer 2 
    apply (simp add: LOW_def)
           apply (erule_tac x=na in allE, clarsimp)
  apply (erule_tac x=ma in allE, clarsimp)
           apply (erule_tac x=mb in allE, clarsimp)
           apply (erule_tac x="Ctxt_While BExpr CtxtProg" in allE)
           apply (erule_tac x="While BExpr (Fill CtxtProg c)" in allE, clarsimp)

  apply (erule Sem_eval_cases) apply clarsimp
  apply clarsimp
(*Ctxt_Call*)
apply clarsimp apply (erule Sem_eval_cases) apply (erule Sem_eval_cases)
  apply (erule_tac x=na in allE, clarsimp) 

(*The deferred goal from Ctxt\_Hole*)
  apply (unfold secure_def Sem_def) 
  apply (erule thin_rl) apply fast
done
(*>*)

text\<open>By induction on the maximal height of the operational judgement
(hidden in the definition of $\mathit{secure}$) we can prove that the
security of $c$ implies that of $\mathit{Fill}\ C\ c$, provided that
the context and the procedure-context satisfy the $\mathit{LOW}$
predicate for some $X$, and that the "real" body is obtained by
substituting $c$ into the procedure context.\<close>

lemma secureI_secureFillI: 
  "\<lbrakk>secure c; LOW X C; LOW X Ctxt_Body; body = Fill Ctxt_Body c\<rbrakk>
  \<Longrightarrow> secure (Fill C c)"
(*<*)
apply (simp (no_asm_simp) add: secure_def Sem_def) 
apply clarsimp
apply (rule secureI_secureFillI_Aux) 
prefer 3 apply assumption
prefer 4 apply assumption
prefer 3 apply assumption
apply (subgoal_tac "n \<le> n+na", assumption)
apply (erule thin_rl, simp)
apply (erule thin_rl, simp)
apply (erule thin_rl,fastforce)
apply assumption
apply assumption
apply assumption
apply assumption
done
(*>*)

text\<open>Consequently, a (low) variable representing the result of
the attacking context does not leak any unwanted information.\<close>

consts res::Var

theorem
  "\<lbrakk> secure c; LOW X C;  LOW X Ctxt_Body; s \<approx> ss; s,(Fill C c)\<Down>t; 
     ss,(Fill C c)\<Down>tt; body = Fill Ctxt_Body c; CONTEXT res = low\<rbrakk>
  \<Longrightarrow> t res = tt res"
(*<*)
apply (drule secureI_secureFillI) apply assumption apply assumption apply assumption
apply (unfold secure_def)
apply (erule_tac x=s in allE, erule_tac x=ss in allE)
apply (erule_tac x=t in allE, erule_tac x=tt in allE, clarsimp)
apply (simp add: twiddle_def)
done
(*>*)
text\<open>End of theory ContextVS\<close>
end
