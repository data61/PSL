(*File: AssocLists.thy
  Author: L Beringer & M Hofmann, LMU Munich
  Date: 05/12/2008
  Purpose: Representation of partial maps by association lists         
*)
(*<*)
theory AssocLists imports Main begin
(*>*)

section\<open>Preliminaries: association lists \label{sec:preliminaries}\<close>

text\<open>Finite maps are used frequently, both in the representation of
syntax and in the program logics. Instead of restricting Isabelle's
partial map type $\alpha \rightharpoonup \beta$ to finite domains, we
found it easier for the present development to use the following adhoc
data type of association lists.\<close>

type_synonym ('a,'b) AssList = "('a \<times> 'b) list"

primrec lookup::"('a, 'b) AssList \<Rightarrow> 'a \<Rightarrow> ('b option)" ("_\<down>_" [90,0] 90)
where
"lookup [] l = None" |
"lookup (h # t) l = (if fst h = l then Some(snd h) else lookup t l)"

(*<*)
lemma AL_lookup1[rule_format]:"\<forall> a b . (L\<down>a = Some b) \<longrightarrow> ((a,b) \<in> set L)"
by (induct L, simp_all)(* add: set_mem_eq)*)

lemma AL_Triv1:"a=b \<Longrightarrow> L\<down>a = L\<down>b" by simp

lemma AL_Triv2: "\<lbrakk>L\<down>a = X; L\<down>a = Y\<rbrakk> \<Longrightarrow> X=Y" by simp

lemma AL_Triv3:"\<lbrakk>L=M ; M\<down>b = X\<rbrakk> \<Longrightarrow> L\<down>b = X" by clarsimp

lemma AL_Triv4:"\<lbrakk>L=M ; L\<down>b = X\<rbrakk> \<Longrightarrow> M\<down>b = X" by clarsimp
(*>*)

text\<open>The statement following the type declaration of \<open>lookup\<close>
indicates that we may use the infix notation \<open>L\<down>a\<close> for the
lookup operation, and asserts some precedence for bracketing. In a
similar way, shorthands are introduced for various operations
throughout this document.\<close>

primrec delete::"('a, 'b) AssList \<Rightarrow> 'a \<Rightarrow> ('a, 'b) AssList"
where
"delete [] a = []" |
"delete (h # t) a = (if (fst h) = a then delete t a else (h # (delete t a)))"

(*<*)
lemma AL_delete1: "(delete L a) \<down> a = None"
by (induct L, auto)

lemma AL_delete2[rule_format]:"b \<noteq> a \<longrightarrow> (delete l a)\<down>b = l\<down>b"
by (induct l, simp, simp)

lemma AL_delete3: "L\<down>a = None \<Longrightarrow> delete L a = L"
apply (induct L)
apply simp
apply clarsimp
apply (subgoal_tac "L\<down>a = None", clarsimp)
apply (case_tac "aa=a", clarsimp) apply clarsimp
done

lemma AL_delete4[simp]: "length(delete t a) < Suc(length t)"
by (induct t, simp+) 

lemma AL_delete5[rule_format]:"[|b \<noteq> a; l\<down>b = x|] ==> (delete l a)\<down>b = x"
by (drule_tac l=l in AL_delete2, simp)

lemma AL_delete_idempotent: "delete M x = delete (delete M x) x"
by (induct M, auto)

lemma AL_delete_commutative: "delete (delete M c) x = delete (delete M x) c"
apply (induct M)
apply simp
apply simp
done
(*>*)

definition upd::"('a, 'b) AssList \<Rightarrow> 'a \<Rightarrow> 'b \<Rightarrow> ('a, 'b) AssList"
         ("_[_\<mapsto>_]" [1000,0,0] 1000)
where "upd L a b = (a,b) # (delete L a)"
(*<*)
lemma AL_update1: "(L::('a, 'b) AssList)[a\<mapsto>b]\<down>a = Some b"
by (simp add: upd_def)

lemma AL_update1a: "a=c \<Longrightarrow> (L::('a, 'b) AssList)[a\<mapsto>b]\<down>c = Some b" by (simp add: AL_update1)

lemma AL_update2: "a \<noteq> b \<Longrightarrow> (L::('a, 'b) AssList)[a\<mapsto>v]\<down>b = L\<down>b"
by (induct L, simp_all add: upd_def)

lemma AL_update3: "\<lbrakk>(L::('a, 'b) AssList)[a\<mapsto>v]\<down>b = X; a \<noteq> b\<rbrakk> \<Longrightarrow> L\<down>b=X"
by (subgoal_tac "(L::('a, 'b) AssList)[a\<mapsto>v]\<down>b = L\<down>b", clarsimp,erule AL_update2) 

lemma AL_update4:"\<lbrakk> (L::('a, 'b) AssList)\<down>b = Some X; a \<noteq> b\<rbrakk>\<Longrightarrow> L[a\<mapsto>v]\<down>b = Some X"
by (subgoal_tac "(L::('a, 'b) AssList)[a\<mapsto>v]\<down>b = L\<down>b", clarsimp, erule AL_update2)

lemma AL_update5: "\<lbrakk>(L::('a, 'b) AssList)\<down>b = M; a \<noteq> b\<rbrakk> \<Longrightarrow> L[a\<mapsto>X]\<down>b = M"
apply (subgoal_tac "(L::('a, 'b) AssList)[a\<mapsto>X]\<down>b = L\<down>b", simp)
apply (erule AL_update2)
done
(*>*)

text\<open>The empty map is represented by the empty list.\<close>

definition emp::"('a, 'b)AssList"
where "emp = []"
(*<*)
lemma AL_emp1: "emp\<down>a = None"
by (simp add: emp_def)

definition AL_isEmp::"('a,'b) AssList \<Rightarrow> bool"
where "AL_isEmp l = (\<forall> a . l\<down>a = None)"
(*>*)

definition contained::"('a,'b) AssList \<Rightarrow> ('a,'b) AssList \<Rightarrow> bool"
where "contained L M = (\<forall> a b . L\<down>a = Some b \<longrightarrow> M\<down>a = Some b)"

text\<open>The following operation defined the cardinality of a map.\<close>

fun AL_Size :: "('a, 'b) AssList \<Rightarrow> nat"  ("|_|" [1000] 1000) where
  "AL_Size [] = 0"
| "AL_Size (h # t) = Suc (AL_Size (delete t (fst h)))"

(*<*)
lemma AL_Size_Zero: "|L| = 0 \<Longrightarrow> None = L\<down>a"
by (induct L, simp, simp)

lemma AL_Size_Suc: "\<forall> n . |L| = Suc n \<longrightarrow> (\<exists> a b . L\<down>a = Some b)"
apply (induct L)
apply clarsimp 
apply clarsimp
apply (rule_tac x=a in exI, simp)
done

lemma AL_Size_UpdateSuc:"L\<down>a = None \<Longrightarrow> |L[a\<mapsto>b]| = Suc |L|"
apply (induct L)
apply (simp add: upd_def)
apply (simp add: upd_def)
apply clarsimp
apply (case_tac "aa=a", clarsimp) 
apply clarsimp
apply (drule AL_delete3) apply clarsimp
done

lemma AL_Size_SucSplit[rule_format]:
"\<forall> n . |L| = Suc n \<longrightarrow> 
  (\<exists> a b M . |M| = n \<and> M\<down>a = None \<and> L\<down>a = Some b \<and> (\<forall> c . c\<noteq> a \<longrightarrow> M\<down>c = L\<down>c))"
apply (induct L)
apply clarsimp
apply clarsimp
apply (rule_tac x=a in exI)  apply simp
apply (rule_tac x="delete L a" in exI, clarsimp)
  apply rule  apply (rule AL_delete1)
apply clarsimp apply (erule AL_delete2)
done

lemma updSizeAux[rule_format]: 
"\<forall> h a obj obj1 . |h[a\<mapsto>obj1]| = n \<longrightarrow> h\<down>a = Some obj \<longrightarrow> |h| = n"
apply (induct n)
apply clarsimp
  apply (drule_tac a=a in AL_Size_Zero) apply (simp add: AL_update1)
apply clarify
  apply (case_tac h, clarify) apply (erule thin_rl) apply (simp add: AL_emp1)
  apply clarify
  apply (case_tac "aa=a", clarify) apply (erule thin_rl) apply (simp add: upd_def)
    apply (subgoal_tac "(delete list a) = (delete (delete list a) a)", simp) 
    apply (rule AL_delete_idempotent)
  apply (erule_tac x="delete list aa" in allE, erule_tac x=a in allE)
  apply (erule_tac x=obj in allE, erule_tac x=obj1 in allE)
  apply (erule impE) apply (simp add: upd_def)
    apply (subgoal_tac "(delete (delete (delete list aa) a) a) = (delete (delete (delete list a) a) aa)", simp)
    apply (subgoal_tac "(delete (delete list a) a) = (delete list a)", simp)
      apply (subgoal_tac "delete (delete (delete list aa) a) a = delete (delete list aa) a", simp)
        apply (rule AL_delete_commutative)
      apply (subgoal_tac "delete (delete list aa) a = delete (delete (delete list aa) a) a", simp)
      apply (rule AL_delete_idempotent)
    apply (subgoal_tac "delete list a = delete (delete list a) a", simp)
    apply (rule AL_delete_idempotent)
  apply (erule impE) apply (simp add: upd_def) apply (rule AL_delete5) apply fast apply assumption
  apply simp
done

lemma updSize: "h\<down>a = Some obj \<Longrightarrow> |h[a\<mapsto>obj1]| = |h|"
by (insert updSizeAux [of h a obj1 "|h[a\<mapsto>obj1]|" obj], simp)
(*>*)

text\<open>Some obvious basic properties of association lists and their
operations are easily proven, but have been suppressed
during the document preparation.\<close>

(*<*)
end
(*>*)
