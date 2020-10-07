section \<open>Some tactics\<close>

(* author: Andrei Popescu *)

theory MyTactics imports Main 
begin 

(* ML {* clarsimp_tac *}


ML{* val x = [1] @ [2] *}

ML {* simp_tac *}  *)


ML\<open>
val impI = @{thm impI}  
val allI = @{thm allI} 
val ballI = @{thm ballI}
val conjE = @{thm conjE}
val conjI = @{thm conjI}
val exE = @{thm exE}
val disjE = @{thm disjE}


fun mclarTacs ctxt i =
  [resolve_tac ctxt [impI] i,
   resolve_tac ctxt [allI] i,
   resolve_tac ctxt [ballI] i,
   eresolve_tac ctxt [conjE] i,
   eresolve_tac ctxt [exE] i];

fun mclarify_all_tac ctxt = REPEAT(SOMEGOAL(fn i => FIRST (mclarTacs ctxt i)));
fun mclarsimp_all_tac ctxt = TRY (mclarify_all_tac ctxt) THEN TRYALL (asm_full_simp_tac ctxt)

fun mautoTacs ctxt i = mclarTacs ctxt i @ [resolve_tac ctxt [conjI] i, eresolve_tac ctxt [disjE] i]
fun mauto_no_simp_tac ctxt = REPEAT(SOMEGOAL(fn i => FIRST (mautoTacs ctxt i)))

fun clarify_all_tac ctxt = TRYALL (clarify_tac ctxt)
\<close>

text\<open>Above, "m" stands for "mild" -- mainly, disjunctions are left untouched.\<close>




(* Note: The variables @{simpset} and @{claset} are *statically bound*, 
hence they refer to the contents of the simp and classical databases at this 
definition time.  For the classical database, this is OK for my purpose, 
since all I care is that it includes HOL_cs.  However, for the simp database 
I shall need to use the current version each time, since the database changes 
continuously with simpliication rules for the newly defined concepts -- thereore 
I shall need to pass that current version as an explicit parameter, which will 
typically be (the current value of) @{simpset}.  *)



(*  Tests: 
lemma "(\<forall> i j k. P \<longrightarrow> (Q1 \<or> Q2  \<and> [] @ L = L)) \<and> (\<forall> a b. G a \<and> G b \<longrightarrow> Q) \<and> D"
apply(tactic {* REPEAT(SOMEGOAL(rtac @{thm conjI})) *})
apply(tactic {* mclarify_all_tac *})
oops


lemma "V \<and> (\<forall> i j k. P \<longrightarrow> (Q1 \<or> Q2 \<and> [] @ L = L)) \<and> (\<forall> a b. G a \<and> G b \<longrightarrow> Q) \<and> D"
apply(tactic {* REPEAT(SOMEGOAL(rtac @{thm conjI})) *})
apply(tactic {* mclarsimp_all_tac @{simpset}*})
oops


lemma "V \<and> (\<forall> i j k. P \<longrightarrow> (Q1 \<or> Q2)) \<and> (\<forall> a b. G a \<and> G b \<longrightarrow> Q) \<and> D"
apply(tactic {* REPEAT(SOMEGOAL(rtac @{thm conjI})) *})
apply(tactic {* clarify_all_tac *})
apply(rule disjE)
oops


lemma "V \<and> (\<forall> i j k. P \<longrightarrow> (Q1 \<or> Q2 \<and> x = x)) \<and> (\<forall> a b. G a \<and> G b \<longrightarrow> Q) \<and> D"
apply(tactic {* REPEAT(SOMEGOAL(rtac @{thm conjI})) *})
apply(tactic {* clarsimp_all_tac @{simpset} *})
oops


lemma "(\<forall> i j k. P \<longrightarrow> Q) \<and> (\<forall> a b. G a \<and> G b \<longrightarrow> (Q \<and> R)) \<and> D"
apply(tactic {* REPEAT(SOMEGOAL(rtac @{thm conjI})) *})
apply(tactic {* mauto_no_simp_tac @{context} *})
oops


lemma test: "(\<forall> i j k. P \<longrightarrow> Q) \<and> (\<forall> a b. G a \<and> G b \<longrightarrow> Q)"
apply(tactic {* mauto_no_simp_tac @{context} *})
apply(rule disjE)
oops

*)


end
