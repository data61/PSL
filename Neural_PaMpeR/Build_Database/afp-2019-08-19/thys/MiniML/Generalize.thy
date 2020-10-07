(* Title:     HOL/MiniML/Generalize.thy
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

section "Generalizing type schemes with respect to a context"

theory Generalize
imports Instance
begin

\<comment> \<open>@{text gen}: binding (generalising) the variables which are not free in the context\<close>

type_synonym ctxt = "type_scheme list"
    
primrec gen :: "[ctxt, typ] => type_scheme" where
  "gen A (TVar n) = (if (n:(free_tv A)) then (FVar n) else (BVar n))"
| "gen A (t1 -> t2) = (gen A t1) =-> (gen A t2)"

\<comment> \<open>executable version of @{text gen}: implementation with @{text free_tv_ML}\<close>

primrec gen_ML_aux :: "[nat list, typ] => type_scheme" where
  "gen_ML_aux A (TVar n) = (if (n: set A) then (FVar n) else (BVar n))"
| "gen_ML_aux A (t1 -> t2) = (gen_ML_aux A t1) =-> (gen_ML_aux A t2)"

definition gen_ML :: "[ctxt, typ] => type_scheme" where
  gen_ML_def: "gen_ML A t = gen_ML_aux (free_tv_ML A) t"

declare equalityE [elim!]

lemma gen_eq_on_free_tv: 
    "free_tv A = free_tv B \<Longrightarrow> gen A t = gen B t"
  by (induct t) simp_all

lemma gen_without_effect [simp]:
    "(free_tv t) \<subseteq> (free_tv sch) \<Longrightarrow> gen sch t = (mk_scheme t)"
  by (induct t) auto

lemma free_tv_gen [simp]: 
  "free_tv (gen ($ S A) t) = free_tv t Int free_tv ($ S A)"
by (induct t) auto

lemma free_tv_gen_cons [simp]: 
  "free_tv (gen ($ S A) t # $ S A) = free_tv ($ S A)"
  by fastforce

lemma bound_tv_gen [simp]: 
  "bound_tv (gen A t1) = (free_tv t1) - (free_tv A)"
  by (induct t1) auto

lemma new_tv_compatible_gen: "new_tv n t \<Longrightarrow> new_tv n (gen A t)"
  by (induct t) auto

lemma gen_eq_gen_ML: "gen A t = gen_ML A t"
apply (unfold gen_ML_def)
apply (induct t)
 apply (simp add: free_tv_ML_scheme_list)
apply (simp add: free_tv_ML_scheme_list)
done

lemma gen_subst_commutes [rule_format]: 
  "(free_tv S) Int ((free_tv t) - (free_tv A)) = {}  
      \<longrightarrow> gen ($ S A) ($ S t) = $ S (gen A t)"
apply (induct t)
 apply (intro strip)
 apply (rename_tac nat)
 apply (case_tac "nat : (free_tv A) ")
  apply (simp (no_asm_simp))
 apply simp
 apply (subgoal_tac "nat \<notin> free_tv S")
  prefer 2 apply (fast)
 apply (simp add: free_tv_subst dom_def)
 apply (cut_tac free_tv_app_subst_scheme_list)
 apply fast
apply simp
apply blast
done

lemma bound_typ_inst_gen [simp]:
    "free_tv(t::typ) \<subseteq> free_tv(A) \<Longrightarrow> bound_typ_inst S (gen A t) = t"
  by (induct t) simp_all

lemma gen_bound_typ_instance: 
  "gen ($ S A) ($ S t) \<le> $ S (gen A t)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply safe
apply (rename_tac "R")
apply (rule_tac x = " (\<lambda>a. bound_typ_inst R (gen ($S A) (S a))) " in exI)
apply (induct_tac "t")
 apply simp
apply simp
done

lemma free_tv_subset_gen_le: 
  "free_tv B \<subseteq> free_tv A \<Longrightarrow> gen A t \<le> gen B t"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply safe
apply (rename_tac "S")
apply (rule_tac x = "\<lambda>b. if b:free_tv A then TVar b else S b" in exI)
apply (induct_tac "t")
 apply fastforce
apply simp
done

lemma gen_t_le_gen_alpha_t [rule_format, simp]: 
  "new_tv n A \<longrightarrow>  
   gen A t \<le> gen A ($ (\<lambda>x. TVar (if x \<in> free_tv A then x else n + x)) t)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (intro strip)
apply (erule exE)
apply (hypsubst)
apply (rule_tac x = " (\<lambda>x. S (if n \<le> x then x - n else x))" in exI)
apply (induct t)
apply (simp (no_asm))
apply (rename_tac nat S)
apply (case_tac "nat \<in> free_tv A")
apply (simp (no_asm_simp))
apply (simp (no_asm_simp))
apply (subgoal_tac "n \<le> n + nat")
apply (frule_tac t = "A" in new_tv_le)
apply assumption
apply (drule new_tv_not_free_tv)
apply (drule new_tv_not_free_tv)
apply (simp add: diff_add_inverse)
apply (simp add: le_add1)
apply simp
done

end
