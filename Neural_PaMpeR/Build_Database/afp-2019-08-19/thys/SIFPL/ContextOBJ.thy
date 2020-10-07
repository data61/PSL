(*File: ContextOBJ.thy*)
(*Authors: Lennart Beringer and Martin Hofmann, LMU Munich 2008*)
theory ContextOBJ imports VS_OBJ begin
subsection\<open>Contextual closure\<close>

text\<open>\label{sec:contextObj}We first define contexts with multiple holes.\<close>

datatype CtxtProg =
  Ctxt_Here
| Ctxt_Skip
| Ctxt_Assign Var Expr
| Ctxt_New Var Class
| Ctxt_Get Var Var Field
| Ctxt_Put Var Field Expr
| Ctxt_Comp CtxtProg CtxtProg
| Ctxt_If BExpr CtxtProg CtxtProg
| Ctxt_While BExpr CtxtProg
| Ctxt_Call

text\<open>The definition of a procedure body with holes.\<close>

consts Ctxt_Body::CtxtProg

text\<open>Next, the substitution of a command into a context:\<close>

primrec Fill::"CtxtProg \<Rightarrow> OBJ \<Rightarrow> OBJ"
where
"Fill Ctxt_Here J = J" |
"Fill Ctxt_Skip J = Skip" |
"Fill (Ctxt_Assign x e) J = Assign x e" |
"Fill (Ctxt_New x c) J = New x c" |
"Fill (Ctxt_Get x y f) J = Get x y f" |
"Fill (Ctxt_Put x f e) J = Put x f e" |
"Fill (Ctxt_Comp C D) J = Comp (Fill C J) (Fill D J)" |
"Fill (Ctxt_If b C D) J = Iff b (Fill C J) (Fill D J)" |
"Fill (Ctxt_While b C) J = While b (Fill C J)" |
"Fill Ctxt_Call J = Call"

text\<open>The variables mentioned by an expression:\<close>

primrec EVars::"Expr \<Rightarrow> Var set"
where
"EVars (varE x) = {x}" |
"EVars (valE v) = {}" |
"EVars (opE f e1 e2) = EVars e1 \<union> EVars e2"

primrec BVars::"BExpr \<Rightarrow> Var set"
where
"BVars (compB f e1 e2) = EVars e1 \<union> EVars e2"

text\<open>The variables possibly read from during the evaluation of $I$
are denoted by $\mathit{Vars\; I}$.\<close>

primrec Vars::"OBJ \<Rightarrow> Var set"
where
"Vars Skip = {}" |
"Vars (Assign x e) = EVars e" |
"Vars (New x C) = {}" |
"Vars (Get x y f) = {y}" |
"Vars (Put x f e) = EVars e" |
"Vars (Comp I J) = Vars I \<union> Vars J" |
"Vars (While b I) = BVars b \<union> Vars I" |
"Vars (Iff b I J) = BVars b \<union> Vars I \<union> Vars J" |
"Vars Call = {}"

(*<*)
lemma Secure_comp: "\<lbrakk>secure C; secure D\<rbrakk> \<Longrightarrow> secure (Comp C D)"
apply (unfold secure_def)
apply (rule, rule, rule, rule)
apply (rule, rule, rule, rule)
apply (unfold Sem_def)
apply (erule exE)+
apply (erule Sem_eval_cases)
apply (erule Sem_eval_cases)
apply (erule_tac x=s in allE, rotate_tac -1)
apply (erule_tac x=ss in allE, rotate_tac -1)
apply (erule_tac x=r in allE, rotate_tac -1)
apply (erule_tac x=ra in allE, rotate_tac -1)
apply (erule_tac x=\<beta> in allE)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply (erule exE, erule conjE)
apply (erule_tac x=r in allE, rotate_tac -1)
apply (erule_tac x=ra in allE, rotate_tac -1)
apply (erule_tac x=t in allE, rotate_tac -1)
apply (erule_tac x=tt in allE, rotate_tac -1)
apply (erule_tac x=\<gamma> in allE)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply (erule exE, erule conjE)
apply (rule, rule, assumption)
apply (erule Pbij_extends_transitive, assumption)
done

lemma Secure_iff:
" \<lbrakk>secure C; secure D;
   \<forall> s t \<beta>. s \<equiv>\<^sub>\<beta> t \<longrightarrow> evalB b (fst s) = evalB b (fst t)\<rbrakk>
  \<Longrightarrow> secure (Iff b C D)"
apply (unfold secure_def)
apply (rule, rule, rule, rule)
apply (rule, rule, rule, rule)
apply (unfold Sem_def)
apply (erule exE)+
apply (erule_tac x=s in allE, erule_tac x=ss in allE, erule_tac x=\<beta> in allE, erule impE, assumption)
apply (erule Sem_eval_cases)
apply (erule Sem_eval_cases)
apply (erule_tac x=s in allE, rotate_tac -1)
apply (erule_tac x=ss in allE, rotate_tac -1)
apply (erule_tac x=t in allE, rotate_tac -1)
apply (erule_tac x=tt in allE, rotate_tac -1)
apply (erule_tac x=\<beta> in allE)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply assumption
apply fast
apply (erule Sem_eval_cases)
apply fast
apply (erule thin_rl)
apply (erule_tac x=s in allE, rotate_tac -1)
apply (erule_tac x=ss in allE, rotate_tac -1)
apply (erule_tac x=t in allE, rotate_tac -1)
apply (erule_tac x=tt in allE, rotate_tac -1)
apply (erule_tac x=\<beta> in allE)
apply (erule impE, assumption)
apply (erule impE, rule, assumption)
apply (erule impE, rule, assumption)
apply assumption
done

lemma secure_while_aux[rule_format]:
"\<forall> n m . n \<le> k \<longrightarrow> m \<le> k \<longrightarrow> 
  (\<forall> s t ss tt . (s , While b C \<rightarrow>\<^sub>n  ss) \<longrightarrow>  
                 (t , While b C \<rightarrow>\<^sub>m  tt) \<longrightarrow> 
                 secure C \<longrightarrow> 
                 (\<forall>s ss \<beta>. s \<equiv>\<^sub>\<beta> ss \<longrightarrow> evalB b (fst s) = evalB b (fst ss)) \<longrightarrow> 
                 (\<forall> \<beta> . s \<equiv>\<^sub>\<beta> t \<longrightarrow> 
                     (\<exists> \<gamma> . ss \<equiv>\<^sub>\<gamma> tt \<and> Pbij_extends \<gamma> \<beta>)))"
apply (induct k)
apply clarsimp apply (drule Sem_no_zero_height_derivs, clarsimp)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (rule, rule, rule)
apply (rule, rule)
  apply (subgoal_tac "evalB b (fst s) = evalB b (fst t)")
  prefer 2 apply (erule thin_rl, fast)
  apply (erule Sem_eval_cases)
  apply (erule Sem_eval_cases) prefer 2 apply simp
    apply (subgoal_tac "\<exists>\<gamma>. r \<equiv>\<^sub>\<gamma> ra \<and> Pbij_extends \<gamma> \<beta>") 
      apply (erule exE, erule conjE) 
      apply (erule_tac x=ma in allE, erule_tac x=mb in allE)
      apply (erule impE, simp)
      apply (erule impE, simp)
      apply (rotate_tac -1, erule_tac x=r in allE)
      apply (rotate_tac -1, erule_tac x=ra in allE)
      apply (rotate_tac -1, erule_tac x=ss in allE)
      apply (rotate_tac -1, erule_tac x=tt in allE)
      apply (erule impE, assumption)
      apply (erule impE, assumption)
      apply (erule impE, assumption)
      apply (erule impE, assumption)
      apply (rotate_tac -1, erule_tac x=\<gamma> in allE)
      apply (erule impE, assumption)
      apply (erule exE, erule conjE)
      apply (rule, rule, assumption)
      apply (erule Pbij_extends_transitive, assumption)
      defer 1
  apply (erule thin_rl)
  apply (erule Sem_eval_cases) apply simp
  apply clarify apply (rule, rule, assumption) apply (rule Pbij_extends_reflexive)
apply (erule thin_rl, unfold secure_def Sem_def) apply fast
done

lemma Secure_while:
" \<lbrakk>secure C;
   \<forall> s t \<beta>. s \<equiv>\<^sub>\<beta> t \<longrightarrow> evalB b (fst s) = evalB b (fst t)\<rbrakk>
  \<Longrightarrow> secure (While b C)"
apply (unfold secure_def)
apply (rule, rule, rule, rule)
apply (rule, rule, rule, rule)
apply (unfold Sem_def) apply (erule exE)+
apply (rule secure_while_aux) 
prefer 3 apply assumption
prefer 6 apply assumption
prefer 3 apply assumption
prefer 3 apply (unfold secure_def Sem_def) apply assumption
prefer 3 apply fast
apply (subgoal_tac "n \<le> n + na", assumption) apply (simp, simp)
done
(*>*)


text\<open>An abbreviating definition saying when a value is not a constant
location.\<close>

definition ValIsNoLoc ::"Val => bool"
where "ValIsNoLoc v = (v = RVal Nullref \<or> (\<exists> i . v = IVal i))"

text\<open>Expressions satisfying the following predicate are guaranteed
not to return a state-independent location.\<close>

primrec Expr_noLoc::"Expr \<Rightarrow> bool"
where
"Expr_noLoc (varE x) = True" |
"Expr_noLoc (valE v) = ValIsNoLoc v" |
"Expr_noLoc (opE f e1 e2) =
   (Expr_noLoc e1 \<and> Expr_noLoc e2 \<and> opEGood f)"

primrec BExpr_noLoc::"BExpr \<Rightarrow> bool"
where
"BExpr_noLoc (compB f e1 e2) =
   (Expr_noLoc e1 \<and> Expr_noLoc e2 \<and> compBGood f)"

text\<open>By induction on $e$ one may show the following three properties.\<close>

lemma Expr_lemma1[rule_format]:
  "Expr_noLoc e \<longrightarrow> EVars e \<subseteq> X \<longrightarrow> 
   (\<forall>x. x \<in> X \<longrightarrow> CONTEXT x = low) \<longrightarrow> Expr_low e"
(*<*)
apply (induct e)
apply (simp_all add:Expr_low_def)
(*VarE*)
apply (simp add: twiddleStore_def)
(*ValE*)
apply (simp add: ValIsNoLoc_def)
apply rule
  apply clarsimp apply (rule twiddleVal_Null)
  apply clarsimp apply (rule twiddleVal_IVal) apply simp
(*opE*)
apply clarsimp
  apply (erule_tac x=s in allE, erule_tac x=t in allE, erule_tac x=\<beta> in allE, clarsimp)
  apply (erule_tac x=s in allE, erule_tac x=t in allE, erule_tac x=\<beta> in allE, clarsimp)
  apply (simp add: opEGood_def)
done
(*>*)

lemma Expr_lemma2[rule_format]:
  "noLowDPs (s, h) \<longrightarrow>
       EVars e \<subseteq> X \<longrightarrow>  Expr_noLoc e \<longrightarrow> 
       (\<forall>x. x \<in> X \<longrightarrow> CONTEXT x = low) \<longrightarrow>
       s \<approx>\<^sub>\<beta> t \<longrightarrow> twiddleHeap \<beta> h k \<longrightarrow>
       noLowDPs (\<lambda>y. if x = y then evalE e s else s y, h)"
(*<*)
apply (induct e)
(*VarE*)
apply (simp add: noLowDPs_def) apply clarsimp
  apply (rename_tac Var l)
  apply (erule_tac x=Var in allE, erule impE, assumption)
  apply (erule_tac x=Var in allE, erule impE, assumption)
  apply (erule_tac x=l in allE, erule mp, assumption)
(*ValE*)
apply (simp add: ValIsNoLoc_def noLowDPs_def) apply clarsimp
(*opE*)
apply clarsimp 
apply (simp add: noLowDPs_def)
 apply clarsimp
apply (drule Expr_lemma1) apply assumption apply fast 
apply (drule Expr_lemma1) apply assumption apply fast
apply (subgoal_tac "(\<beta>,evalE e1 s,evalE e1 t): twiddleVal")
prefer 2 apply (simp add: Expr_low_def)
apply (subgoal_tac "(\<beta>,evalE e2 s,evalE e2 t): twiddleVal")
prefer 2 apply (simp add: Expr_low_def)
apply (simp add: opEGood_def)
apply (erule_tac x=\<beta> in allE, erule_tac x="evalE e1 s" in allE, erule_tac x="evalE e1 t" in allE, erule impE, assumption)
apply (erule_tac x="evalE e2 s" in allE, erule_tac x="evalE e2 t" in allE, erule impE, assumption)
apply clarsimp apply (rotate_tac -1, erule twiddleVal.cases, simp_all) apply clarsimp
apply (simp add: twiddleHeap_def Pbij_Dom_def) apply clarsimp apply fast
done
(*>*)

lemma Expr_lemma3[rule_format]:
 "noLowDPs (s,h) \<longrightarrow>  EVars e \<subseteq> X \<longrightarrow> Expr_noLoc e \<longrightarrow>
   lookup h l = Some (C, Flds) \<longrightarrow>
   (\<forall>x. x \<in> X \<longrightarrow> CONTEXT x = low) \<longrightarrow> 
   s \<approx>\<^sub>\<beta> t \<longrightarrow> twiddleHeap \<beta> h k \<longrightarrow>
   noLowDPs (s, (l, C, (f, evalE e s) # Flds) # h)"
(*<*)
apply (induct e)
(*VarE*)
apply (simp add: noLowDPs_def) apply clarsimp
  apply (rule, clarsimp) apply (simp add: Dom_def)
  apply (rule, rule, clarsimp)
    apply (rule, clarsimp) apply (rename_tac Var la) apply (erule_tac x=Var in allE, clarsimp) apply (simp add: Dom_def)
    apply clarsimp  apply (erule_tac x=l in allE, clarsimp) apply (erule_tac x=fa in allE, clarsimp)
     apply (simp add: Dom_def)
  apply clarsimp apply (erule_tac x=ll in allE, clarsimp) apply (erule_tac x=fa in allE, clarsimp) apply (simp add: Dom_def)
(*ValE*)
apply (simp add: ValIsNoLoc_def noLowDPs_def) apply clarsimp
  apply (rule,clarsimp)
    apply (rule, clarsimp) apply (simp add: Dom_def)
    apply (rule, rule, clarsimp) apply (simp add: Dom_def)
    apply (simp add: Dom_def)
  apply clarsimp 
    apply (rule, clarsimp) apply (simp add: Dom_def)
    apply (rule, rule, clarsimp) apply (simp add: Dom_def)
    apply (simp add: Dom_def)
(*opE*)
apply clarsimp 
apply (simp add: noLowDPs_def)
apply (rule, clarsimp) apply (simp add: Dom_def)
apply clarsimp
apply (rule, clarsimp)
  apply (rule, clarsimp)
    apply (subgoal_tac "la:Dom h", simp add: Dom_def)
    apply (drule Expr_lemma1) apply assumption apply fast 
    apply (drule Expr_lemma1) apply assumption apply fast
    apply (subgoal_tac "(\<beta>,evalE e1 s,evalE e1 t): twiddleVal")
    prefer 2 apply (simp add: Expr_low_def)
    apply (subgoal_tac "(\<beta>,evalE e2 s,evalE e2 t): twiddleVal")
    prefer 2 apply (simp add: Expr_low_def)
    apply (simp add: opEGood_def)
    apply (erule_tac x=\<beta> in allE, erule_tac x="evalE e1 s" in allE, erule_tac x="evalE e1 t" in allE, erule impE, assumption)
    apply (erule_tac x="evalE e2 s" in allE, erule_tac x="evalE e2 t" in allE, erule impE, assumption)
    apply clarsimp apply (rotate_tac -1, erule twiddleVal.cases, simp_all) apply clarsimp
    apply (simp add: twiddleHeap_def,clarsimp) apply (subgoal_tac "l1:Pbij_Dom \<beta>") apply fast
                                               apply(simp add:Pbij_Dom_def, rule, assumption)
  apply clarsimp apply (erule_tac x=l in allE, clarsimp) 
    apply (erule_tac x=fa in allE, clarsimp) apply (simp add: Dom_def)
apply clarsimp apply (erule_tac x=ll in allE, clarsimp)
  apply (erule_tac x=fa in allE, clarsimp)
  apply (simp add: Dom_def)
done
(*>*)

text\<open>The first of these can be lifted to boolean expressions.\<close>

lemma BExpr_lemma:
"\<lbrakk>BVars b \<subseteq> X; \<forall>x. x \<in> X \<longrightarrow> CONTEXT x = low; BExpr_noLoc b\<rbrakk> \<Longrightarrow> BExpr_low b"
(*<*)
apply (case_tac b, clarsimp)
apply (drule Expr_lemma1, assumption) apply fast
apply (drule Expr_lemma1, assumption) apply fast
apply (simp add: BExpr_low_def Expr_low_def compBGood_def, clarsimp) apply fast
done
(*>*)

text\<open>For contexts, we define when a set $X$ of variables is an upper
bound for the variables read from. In addition, the \<open>noLoc\<close>
condition is imposed on expressions occurring in assignments and field
modifications in order to express that if these expressions evaluate
to locations then these must stem from lookup operations in the
state.\<close>

primrec CtxtVars::"Var set \<Rightarrow> CtxtProg \<Rightarrow> bool"
where
"CtxtVars X Ctxt_Here = True" |
"CtxtVars X Ctxt_Skip = True" |
"CtxtVars X (Ctxt_Assign x e) = (EVars e \<subseteq> X \<and> Expr_noLoc e)" |
"CtxtVars X (Ctxt_New x c) = True" |
"CtxtVars X (Ctxt_Get x y f) = (y : X \<and> GAMMA f = low)" |
"CtxtVars X (Ctxt_Put x f e) =
   (EVars e \<subseteq> X \<and> CONTEXT x = low \<and> Expr_noLoc e)" |
"CtxtVars X (Ctxt_Comp C D) = (CtxtVars X C \<and> CtxtVars X D)" |
"CtxtVars X (Ctxt_If b C D) =
   (BVars b \<subseteq> X \<and> CtxtVars X C \<and> CtxtVars X D \<and> BExpr_noLoc b)" |
"CtxtVars X (Ctxt_While b C) =
   (BVars b \<subseteq> X \<and> CtxtVars X C \<and> BExpr_noLoc b)" |
"CtxtVars X Ctxt_Call = True"

text\<open>A context is "obviously" low if all accessed variables are
(contained in a set $X$ whose members are) low.\<close>

definition LOW::"Var set \<Rightarrow> CtxtProg \<Rightarrow> bool"
where "LOW X C = (CtxtVars X C \<and> (\<forall> x . x : X \<longrightarrow> CONTEXT x = low))"

(*<*)
lemma secureI_secureFillI_Aux[rule_format]:
"\<forall> n m . n \<le> k \<longrightarrow> m \<le> k \<longrightarrow> 
       (\<forall> C J s t ss tt \<beta> X . (s , J \<rightarrow>\<^sub>n t) \<longrightarrow>  
                          (ss , J \<rightarrow>\<^sub>m  tt) \<longrightarrow> 
                          s \<equiv>\<^sub>\<beta> ss \<longrightarrow>  
                          J = Fill C I \<longrightarrow>
                          LOW X C \<longrightarrow>
                          LOW X Ctxt_Body \<longrightarrow>
                          body = Fill Ctxt_Body I \<longrightarrow> secure I \<longrightarrow> 
                          (\<exists> \<gamma> . t \<equiv>\<^sub>\<gamma> tt \<and> Pbij_extends \<gamma> \<beta>))"
apply (induct k)
apply clarsimp apply (drule Sem_no_zero_height_derivs, clarsimp)
apply (rule, rule, rule, rule)
apply (rule, rule, rule, rule)
apply (rule, rule, rule, rule)
apply (rule, rule, rule, rule)
apply (rule, rule, rule, rule)
apply (case_tac C)
(*Ctxt_Here*)
  apply (unfold secure_def Sem_def) 
  apply (erule thin_rl) 
  apply simp apply fast 
(*Ctxt_Skip*)
apply clarsimp
  apply (erule thin_rl)
  apply (erule Sem_eval_cases)+ apply clarsimp apply (rule, rule,  assumption) 
  apply (rule Pbij_extends_reflexive) 
(*Ctxt_Assign*)
apply clarsimp
  apply (erule thin_rl) apply (rotate_tac -1, erule thin_rl)
  apply (erule Sem_eval_cases)+ apply clarsimp
  apply (simp add: update_def twiddle_def) apply clarsimp
    apply (rule, simp only: LOW_def, clarsimp) apply (erule Expr_lemma2, assumption+) apply fast apply assumption+ 
    apply (rule, simp only: LOW_def, clarsimp) apply (erule Expr_lemma2, assumption+) apply fast 
      apply (erule twiddleStore_inverse) apply (erule twiddleHeap_inverse)
    apply (rule, rule) 
    prefer 2 apply (rule, assumption) apply (rule Pbij_extends_reflexive)
    apply (simp (no_asm_simp) add: twiddleStore_def)
    apply rule
    apply (simp add: LOW_def) apply clarsimp 
      apply (rule, clarsimp) apply (rename_tac Expr x) apply (subgoal_tac "Expr_low Expr") apply (simp add: Expr_low_def)
                             apply (erule Expr_lemma1) apply assumption+ apply fast 
      apply clarsimp apply (simp add: twiddleStore_def) 
(*New*)
  apply (erule thin_rl, clarsimp)
  apply (rotate_tac -1, erule thin_rl)
  apply (erule Sem_eval_cases)
  apply (erule Sem_eval_cases)
  apply clarsimp
  apply (rule_tac x="{(l,la)} \<union> \<beta>" in exI)
  apply rule
    prefer 2 
      apply (simp add: Pbij_extends_def twiddle_def twiddleHeap_def) apply clarsimp
    apply (frule isPBij) 
    apply (simp add: twiddle_def) 
    apply (rule, simp add: noLowDPs_def update_def) 
      apply (rule, clarsimp)
        apply (rule, simp add: Dom_def)
        apply clarsimp apply (erule_tac x=x in allE, erule impE, assumption)
                       apply (erule_tac x=lb in allE, erule impE, assumption)
                       apply (simp add: Dom_def)
        apply clarsimp apply (erule_tac x=ll in allE, clarsimp)
                       apply (erule_tac x=f in allE, clarsimp)
                       apply (simp add: Dom_def)
    apply (rule, simp add: noLowDPs_def update_def) 
      apply (rule, clarsimp)
        apply (rule, simp add: Dom_def)
        apply clarsimp apply (erule_tac x=x in allE, erule impE, assumption,
                              erule_tac x=lb in allE, erule impE, assumption)
                       apply (simp add: Dom_def)
        apply clarsimp apply (erule_tac x=ll in allE, erule_tac x=c in allE, erule_tac x=F in allE, erule impE, assumption,
                              erule_tac x=f in allE, clarsimp)
                       apply (simp add: Dom_def)
    apply rule 
      apply (simp add: twiddleStore_def)
       apply clarsimp apply (simp add: update_def)
         apply rule apply clarsimp apply (rule twiddleVal_Loc) apply simp
         apply clarsimp apply (rotate_tac -4, erule_tac x=x in allE, clarsimp) 
           apply (erule twiddleVal_betaExtend) apply (simp add: Pbij_extends_def) apply fast
     apply (simp add: twiddleHeap_def)
     apply (rule, simp add: Pbij_def) apply clarsimp apply (rule, clarsimp) apply (simp add: Pbij_Dom_def Pbij_Rng_def) apply (rotate_tac -2, erule thin_rl) apply rule apply fast apply fast
        apply clarsimp apply (simp add: Pbij_Dom_def Pbij_Rng_def) apply rule apply fast apply fast
     apply (rule, simp add: Pbij_Dom_def Dom_def) apply fast
     apply (rule, simp add: Pbij_Rng_def Dom_def) apply fast
     apply clarsimp 
     apply rule apply clarsimp
       apply (simp add: twiddleObj_def) 
     apply clarsimp 
     apply rule apply (simp add: Pbij_Dom_def) apply fast 
                apply (simp add: Pbij_Dom_def) apply fast 
     apply clarsimp 
     apply rule apply clarsimp apply (simp add: Pbij_Rng_def) apply fast 
     apply clarsimp  
       apply (erule_tac x=lb in allE, erule_tac x=ll in allE, clarsimp) 
       apply (erule twiddleObj_betaExtend) 
       apply (simp add: Pbij_extends_def) apply fast
(*Get*)
  apply (erule thin_rl, clarsimp)
  apply (rotate_tac -1, erule thin_rl)
  apply (erule Sem_eval_cases)
  apply (erule Sem_eval_cases)
  apply clarsimp
  apply (rule, rule)
  prefer 2 apply (rule Pbij_extends_reflexive) 
  apply (simp add: twiddle_def)
  apply (rule, simp add: noLowDPs_def update_def LOW_def, clarsimp)
  apply (rule, simp add: noLowDPs_def update_def LOW_def, clarsimp)
  apply (simp add: twiddleStore_def)
  apply clarsimp apply (simp add: update_def, clarsimp)
  apply (simp add: twiddleHeap_def, clarsimp)
  apply (rotate_tac 4, rename_tac Var2 x53 l C Flds v la Ca Fldsa va x, erule_tac x=Var2 in allE,
    simp add: LOW_def) apply clarsimp
  apply (erule twiddleVal.cases) apply clarsimp prefer 2 apply clarsimp apply clarsimp
  apply (erule_tac x=l1 in allE)
  apply (erule_tac x=l2 in allE)
  apply clarsimp apply (simp add: twiddleObj_def) 
(*Put*)
 apply (rename_tac Var Field Expr)
 apply (erule thin_rl, clarsimp)
  apply (rotate_tac -1, erule thin_rl)
  apply (erule Sem_eval_cases)
  apply (erule Sem_eval_cases)
  apply clarsimp
  apply (rule, rule)
  prefer 2 apply (rule Pbij_extends_reflexive) 
  apply (simp add: update_def twiddle_def, clarsimp)
    apply (rule, simp only: LOW_def, clarsimp) apply (erule  Expr_lemma3, assumption+) apply fast apply assumption+
    apply (rule, simp only: LOW_def, clarsimp) apply (erule  Expr_lemma3, assumption+) apply fast 
      apply (erule twiddleStore_inverse) apply (erule twiddleHeap_inverse) 
  apply (simp add: twiddleHeap_def)
  apply clarsimp 
  apply rule apply (rotate_tac -1, erule thin_rl) apply (simp add: Dom_def) apply fast 
  apply rule apply (rotate_tac -1, erule thin_rl) apply (simp add: Dom_def) apply fast 
  apply clarsimp
  apply rule apply clarsimp
    apply rule apply clarsimp apply (erule_tac x=lb in allE, erule_tac x=ll in allE, clarsimp) 
      apply (simp add: twiddleObj_def)
      apply rule apply clarsimp apply (rotate_tac -1, erule thin_rl) apply (simp add: LowDom_def)
        apply rule apply fastforce apply fastforce
      apply (simp add: LOW_def, clarsimp)
        apply (subgoal_tac "Expr_low Expr") apply (simp add: Expr_low_def)
        apply (erule Expr_lemma1) apply assumption apply fast
    apply clarsimp 
      apply (simp add: LOW_def twiddleStore_def) apply clarsimp 
      apply (erule_tac x=Var in allE, clarsimp)
      apply (erule twiddleVal.cases) apply clarsimp prefer 2 apply clarsimp apply clarsimp
      apply (simp add: Pbij_def)
      apply (erule_tac x=l1 in allE)
      apply (rotate_tac -1, erule_tac x=ll in allE, erule impE, assumption)
      apply (rotate_tac -1, erule_tac x=l1 in allE)
      apply (rotate_tac -1, erule_tac x=l2 in allE, erule impE, assumption)
      apply clarsimp
  apply clarsimp 
    apply (simp add: LOW_def twiddleStore_def) apply (erule_tac x=Var in allE, clarsimp)
    apply (erule twiddleVal.cases) apply clarsimp prefer 2 apply clarsimp apply clarsimp
       apply (drule Pbij_injective) apply (rotate_tac -1, erule_tac x=l2 in allE)
         apply (rotate_tac -1, erule_tac x=l1 in allE)
         apply (rotate_tac -1, erule_tac x=lb in allE, clarsimp)
(*Ctxt_Comp*)
apply (rename_tac CtxtProg1 CtxtProg2)
apply clarsimp apply (erule Sem_eval_cases) apply (erule Sem_eval_cases) apply clarsimp 
  apply (subgoal_tac "\<exists> \<gamma> . (ad,bd) \<equiv>\<^sub>\<gamma> (ae,be) \<and> Pbij_extends \<gamma> \<beta>")
  prefer 2
           apply (erule_tac x=na in allE, clarsimp)
           apply (erule_tac x=nb in allE, clarsimp)
           apply (erule_tac x=CtxtProg1 in allE)
           apply (erule_tac x="Fill CtxtProg1 I" in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=a in allE)
           apply (rotate_tac -1, erule_tac x=b in allE)
           apply (rotate_tac -1, erule_tac x=ad in allE)
           apply (rotate_tac -1, erule_tac x=bd in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=ab in allE)
           apply (rotate_tac -1, erule_tac x=bb in allE)
           apply (rotate_tac -1, erule_tac x=ae in allE)
           apply (rotate_tac -1, erule_tac x=be in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=\<beta> in allE, erule impE, assumption)
           apply (rotate_tac -1, erule_tac x=X in allE, clarsimp) apply (simp add: LOW_def)
        apply clarsimp
           apply (erule_tac x=ma in allE, clarsimp)
           apply (erule_tac x=mb in allE, clarsimp)
           apply (erule_tac x=CtxtProg2 in allE)
           apply (erule_tac x="Fill CtxtProg2 I" in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=ad in allE)
           apply (rotate_tac -1, erule_tac x=bd in allE)
           apply (rotate_tac -1, erule_tac x=aa in allE)
           apply (rotate_tac -1, erule_tac x=ba in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=ae in allE)
           apply (rotate_tac -1, erule_tac x=be in allE)
           apply (rotate_tac -1, erule_tac x=ac in allE)
           apply (rotate_tac -1, erule_tac x=bc in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=\<gamma> in allE, erule impE, assumption)
           apply (rotate_tac -1, erule_tac x=X in allE, clarsimp)  apply (simp add: LOW_def, clarsimp)
        apply (rule, rule) prefer 2 apply (rule Pbij_extends_transitive) prefer 2 apply assumption apply assumption apply assumption
(*Ctxt_If*)
apply (rename_tac BExpr CtxtProg1 CtxtProg2)
apply clarsimp 
  apply (subgoal_tac "evalB BExpr a = evalB BExpr ab")
  prefer 2 apply (erule thin_rl) apply (rotate_tac -1, erule thin_rl)
           apply (simp add: LOW_def, clarsimp)
           apply (drule BExpr_lemma) apply assumption apply assumption
           apply (simp add: BExpr_low_def twiddle_def, clarsimp) 
           apply (erule_tac x=a in allE, erule_tac x=ab in allE, erule mp) apply (rule, assumption)
  apply (erule Sem_eval_cases) apply (erule Sem_eval_cases) prefer 2 apply clarsimp apply clarsimp
           apply (erule_tac x=na in allE, clarsimp)
           apply (erule_tac x=nb in allE, clarsimp)
           apply (erule_tac x=CtxtProg1 in allE)
           apply (erule_tac x="Fill CtxtProg1 I" in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=a in allE)
           apply (rotate_tac -1, erule_tac x=b in allE)
           apply (rotate_tac -1, erule_tac x=aa in allE)
           apply (rotate_tac -1, erule_tac x=ba in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=ab in allE)
           apply (rotate_tac -1, erule_tac x=bb in allE)
           apply (rotate_tac -1, erule_tac x=ac in allE)
           apply (rotate_tac -1, erule_tac x=bc in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=\<beta> in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=X in allE, clarsimp) apply (simp add: LOW_def)
         apply (erule Sem_eval_cases) apply clarsimp apply clarsimp
           apply (erule_tac x=na in allE, clarsimp)
           apply (erule_tac x=nb in allE, clarsimp)
           apply (erule_tac x=CtxtProg2 in allE)
           apply (erule_tac x="Fill CtxtProg2 I" in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=a in allE)
           apply (rotate_tac -1, erule_tac x=b in allE)
           apply (rotate_tac -1, erule_tac x=aa in allE)
           apply (rotate_tac -1, erule_tac x=ba in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=ab in allE)
           apply (rotate_tac -1, erule_tac x=bb in allE)
           apply (rotate_tac -1, erule_tac x=ac in allE)
           apply (rotate_tac -1, erule_tac x=bc in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=\<beta> in allE, clarsimp)
           apply (rotate_tac -1, erule_tac x=X in allE, clarsimp) apply (simp add: LOW_def)
(*Ctxt_While*)
apply (rename_tac BExpr CtxtProg)
apply clarsimp 
  apply (subgoal_tac "evalB BExpr a = evalB BExpr ab")
  prefer 2 apply (erule thin_rl) apply (rotate_tac -1, erule thin_rl)
           apply (simp add: LOW_def, clarsimp)
           apply (drule BExpr_lemma) apply assumption apply assumption
           apply (simp add: BExpr_low_def twiddle_def, clarsimp) 
           apply (erule_tac x=a in allE, erule_tac x=ab in allE, erule mp) apply (rule, assumption)
  apply (erule Sem_eval_cases) 
    apply (erule Sem_eval_cases) prefer 2 apply clarsimp
    apply (subgoal_tac "\<exists> \<gamma> . r \<equiv>\<^sub>\<gamma> ra \<and> Pbij_extends \<gamma> \<beta>")
    prefer 2 apply (erule_tac x=na in allE, clarsimp)
             apply (erule_tac x=nb in allE, clarsimp)
             apply (erule_tac x=CtxtProg in allE)
             apply (erule_tac x="Fill CtxtProg I" in allE, clarsimp)
             apply (rotate_tac 4, erule thin_rl)
             apply (rotate_tac -3, erule_tac x=a in allE)
             apply (rotate_tac -1, erule_tac x=b in allE)
             apply (rotate_tac -1, erule_tac x=ad in allE)
             apply (rotate_tac -1, erule_tac x=bd in allE, clarsimp)
             apply (rotate_tac -1, erule_tac x=ab in allE)
             apply (rotate_tac -1, erule_tac x=bb in allE)
             apply (rotate_tac -1, erule_tac x=ae in allE)
             apply (rotate_tac -1, erule_tac x=be in allE, clarsimp)
             apply (rotate_tac -1, erule_tac x=\<beta> in allE, clarsimp)
             apply (rotate_tac -1, erule_tac x=X in allE, clarsimp, simp add: LOW_def) 
    apply clarsimp
    apply (erule_tac x=ma in allE, clarsimp)
    apply (erule_tac x=mb in allE, clarsimp)
    apply (erule_tac x="Ctxt_While BExpr CtxtProg" in allE)
    apply (erule_tac x="While BExpr (Fill CtxtProg I)" in allE, clarsimp)
    apply (rotate_tac 4, erule thin_rl)
    apply (rotate_tac -3, erule_tac x=ad in allE)
    apply (rotate_tac -1, erule_tac x=bd in allE)
    apply (rotate_tac -1, erule_tac x=aa in allE)
    apply (rotate_tac -1, erule_tac x=ba in allE, clarsimp)
    apply (rotate_tac -1, erule_tac x=ae in allE)
    apply (rotate_tac -1, erule_tac x=be in allE)
    apply (rotate_tac -1, erule_tac x=ac in allE)
    apply (rotate_tac -1, erule_tac x=bc in allE, clarsimp)
    apply (rotate_tac -1, erule_tac x=\<gamma> in allE, clarsimp)
    apply (rotate_tac -1, erule_tac x=X in allE, clarsimp, simp add: LOW_def)
    apply (rule_tac x=\<gamma>' in exI, simp) apply (erule Pbij_extends_transitive) apply assumption
  apply clarsimp apply (erule Sem_eval_cases) apply clarsimp apply clarsimp 
    apply (rule_tac x=\<beta> in exI, simp) apply (rule Pbij_extends_reflexive) 
(*Ctxt_Call*)
apply clarsimp apply (erule Sem_eval_cases) apply (erule Sem_eval_cases)
  apply (erule_tac x=na in allE, clarsimp) 
done
(*>*)

text\<open>Finally, we obtain the following result by induction on an upper
bound on the derivation heights of the two executions of $Fill\ C\
I$.\<close>

theorem secureI_secureFillI: 
 "\<lbrakk>secure I; LOW X C; LOW X Ctxt_Body; body = Fill Ctxt_Body I\<rbrakk>
 \<Longrightarrow> secure (Fill C I)"
(*<*)
apply (unfold secure_def Sem_def) 
apply (rule, rule, rule, rule)
apply (rule, rule, rule, rule)
apply (erule exE)+
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
apply (simp add: secure_def Sem_def)
done
(*>*)

text\<open>For a variable\<close>

consts res::Var

text\<open>representing the output of the attacking context, the result specialises to\<close>

theorem SecureForAttackingContext:
 "\<lbrakk> secure I; LOW X C;  LOW X Ctxt_Body; s \<equiv>\<^sub>\<beta> ss;
    s,(Fill C I)\<Down>t; ss,(Fill C I)\<Down>tt; body = Fill Ctxt_Body I;
    CONTEXT res = low\<rbrakk> 
  \<Longrightarrow> \<exists> \<gamma>. (\<gamma>,(fst t) res,(fst tt) res):twiddleVal \<and> Pbij_extends \<gamma> \<beta>"
(*<*)
apply (drule secureI_secureFillI) apply assumption apply assumption apply assumption
apply (unfold secure_def)
apply (erule_tac x=s in allE, erule_tac x=ss in allE)
apply (erule_tac x=t in allE, erule_tac x=tt in allE)
apply (erule_tac x=\<beta> in allE, clarsimp)
apply (simp add: twiddle_def twiddleStore_def) apply fast
done
(*>*)

text\<open>End of theory ContextObj\<close>
end
