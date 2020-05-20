(* Title:     HOL/MiniML/MiniML.thy
   Author:    Dieter Nazareth, Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

section "MiniML with type inference rules"

theory MiniML
imports Generalize
begin

\<comment> \<open>expressions\<close>
datatype
  expr = Var nat | Abs expr | App expr expr | LET expr expr

\<comment> \<open>type inference rules\<close>
inductive
  has_type :: "[ctxt, expr, typ] => bool"
                  ("((_) |-/ (_) :: (_))" [60,0,60] 60)
where
  VarI: "[| n < length A; t <| A!n |] ==> A |- Var n :: t"
| AbsI: "[| (mk_scheme t1)#A |- e :: t2 |] ==> A |- Abs e :: t1 -> t2"
| AppI: "[| A |- e1 :: t2 -> t1; A |- e2 :: t2 |] 
         ==> A |- App e1 e2 :: t1"
| LETI: "[| A |- e1 :: t1; (gen A t1)#A |- e2 :: t |] ==> A |- LET e1 e2 :: t"

declare has_type.intros [simp]
declare Un_upper1 [simp] Un_upper2 [simp]
declare is_bound_typ_instance_closed_subst [simp]

lemma s'_t_equals_s_t: 
  "\<And>t::typ. $(\<lambda>n. if n : (free_tv A) Un (free_tv t) then (S n) else (TVar n)) t = $S t"
apply (rule typ_substitutions_only_on_free_variables)
apply (simp add: Ball_def)
done

declare s'_t_equals_s_t [simp]

lemma s'_a_equals_s_a: 
  "\<And>A::type_scheme list. $(\<lambda>n. if n : (free_tv A) Un (free_tv t) then (S n) else (TVar n)) A = $S A"
apply (rule scheme_list_substitutions_only_on_free_variables)
apply (simp add: Ball_def)
done

declare s'_a_equals_s_a [simp]

lemma replace_s_by_s': 
 "$(\<lambda>n. if n : (free_tv A) Un (free_tv t) then S n else TVar n) A |-  
     e :: $(\<lambda>n. if n : (free_tv A) Un (free_tv t) then S n else TVar n) t  
  \<Longrightarrow> $S A |- e :: $S t"
apply (rule_tac P = "\<lambda>A. A |- e :: $S t" in ssubst)
apply (rule s'_a_equals_s_a [symmetric])
apply (rule_tac P = "\<lambda>t. $ (\<lambda>n. if n : free_tv A Un free_tv (t2 S) then S n else TVar n) A |- e :: t" for t2 in ssubst)
apply (rule s'_t_equals_s_t [symmetric])
apply simp
done

lemma alpha_A': 
  "\<And>A::type_scheme list. $ (\<lambda>x. TVar (if x : free_tv A then x else n + x)) A = $ id_subst A"
apply (rule scheme_list_substitutions_only_on_free_variables)
apply (simp add: id_subst_def)
done

lemma alpha_A: 
  "\<And>A::type_scheme list. $ (\<lambda>x. TVar (if x : free_tv A then x else n + x)) A = A"
apply (rule alpha_A' [THEN ssubst])
apply simp
done

lemma S_o_alpha_typ: 
  "$ (S \<circ> alpha) (t::typ) = $ S ($ (\<lambda>x. TVar (alpha x)) t)"
apply (induct_tac "t")
apply (simp_all)
done

lemma S_o_alpha_typ': 
  "$ (\<lambda>u. (S \<circ> alpha) u) (t::typ) = $ S ($ (\<lambda>x. TVar (alpha x)) t)"
apply (induct_tac "t")
apply (simp_all)
done

lemma S_o_alpha_type_scheme: 
  "$ (S \<circ> alpha) (sch::type_scheme) = $ S ($ (\<lambda>x. TVar (alpha x)) sch)"
apply (induct_tac "sch")
apply (simp_all)
done

lemma S_o_alpha_type_scheme_list: 
  "$ (S \<circ> alpha) (A::type_scheme list) = $ S ($ (\<lambda>x. TVar (alpha x)) A)"
apply (induct_tac "A")
apply (simp_all) 
apply (rule S_o_alpha_type_scheme [unfolded o_def])
done

lemma S'_A_eq_S'_alpha_A: "\<And>A::type_scheme list.  
      $ (\<lambda>n. if n : free_tv A Un free_tv t then S n else TVar n) A =  
      $ ((\<lambda>x. if x : free_tv A Un free_tv t then S x else TVar x) \<circ>  
         (\<lambda>x. if x : free_tv A then x else n + x)) A"
apply (subst S_o_alpha_type_scheme_list)
apply (subst alpha_A)
apply (rule refl)
done

lemma dom_S': 
 "dom (\<lambda>n. if n : free_tv A Un free_tv t then S n else TVar n) \<subseteq>  
  free_tv A Un free_tv t"
apply (unfold free_tv_subst dom_def)
apply (simp (no_asm))
apply fast
done

lemma cod_S': 
  "\<And>(A::type_scheme list) (t::typ).   
   cod (\<lambda>n. if n : free_tv A Un free_tv t then S n else TVar n) \<subseteq>  
   free_tv ($ S A) Un free_tv ($ S t)"
apply (unfold free_tv_subst cod_def subset_eq)
apply (rule ballI)
apply (erule UN_E)
apply (drule dom_S' [THEN subsetD])
apply simp
apply (fast dest: free_tv_of_substitutions_extend_to_scheme_lists intro: free_tv_of_substitutions_extend_to_types [THEN subsetD])
done

lemma free_tv_S': 
 "\<And>(A::type_scheme list) (t::typ).  
  free_tv (\<lambda>n. if n : free_tv A Un free_tv t then S n else TVar n) \<subseteq>  
  free_tv A Un free_tv ($ S A) Un free_tv t Un free_tv ($ S t)"
apply (unfold free_tv_subst)
apply (fast dest: dom_S' [THEN subsetD] cod_S' [THEN subsetD])
done

lemma free_tv_alpha: "\<And>t1::typ.  
      (free_tv ($ (\<lambda>x. TVar (if x : free_tv A then x else n + x)) t1) - free_tv A) \<subseteq>  
          {x. \<exists>y. x = n + y}"
apply (induct_tac "t1")
apply (simp (no_asm))
apply fast
apply (simp (no_asm))
apply fast
done

lemma new_tv_Int_free_tv_empty_type: "\<And>t::typ. new_tv n t \<Longrightarrow> {x. \<exists>y. x = n + y} Int free_tv t = {}"
apply safe
apply (cut_tac le_add1)
apply (drule new_tv_le)
apply assumption
apply (rotate_tac 1)
apply (drule new_tv_not_free_tv)
apply fast
done

lemma new_tv_Int_free_tv_empty_scheme: "\<And>sch::type_scheme. new_tv n sch \<Longrightarrow> {x. \<exists>y. x = n + y} Int free_tv sch = {}"
apply safe
apply (cut_tac le_add1)
apply (drule new_tv_le)
apply assumption
apply (rotate_tac 1)
apply (drule new_tv_not_free_tv)
apply fast
done

lemma new_tv_Int_free_tv_empty_scheme_list: "\<forall>A::type_scheme list. new_tv n A \<longrightarrow> {x. \<exists>y. x = n + y} Int free_tv A = {}"
apply (rule allI)
apply (induct_tac "A")
apply (simp (no_asm))
apply (simp (no_asm))
apply (fast dest: new_tv_Int_free_tv_empty_scheme)
done

lemma gen_t_le_gen_alpha_t [rule_format (no_asm)]: 
   "new_tv n A \<longrightarrow> gen A t \<le> gen A ($ (\<lambda>x. TVar (if x : free_tv A then x else n + x)) t)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (intro strip)
apply (erule exE)
apply (hypsubst)
apply (rule_tac x = " (\<lambda>x. S (if n \<le> x then x - n else x))" in exI)
apply (induct_tac t)
apply (simp (no_asm))
apply (rename_tac nat)
apply (case_tac "nat : free_tv A")
apply (simp (no_asm_simp))
apply (subgoal_tac "n \<le> n + nat")
apply (drule new_tv_le)
apply assumption
apply (drule new_tv_not_free_tv)
apply (drule new_tv_not_free_tv)
apply (simp (no_asm_simp) add: diff_add_inverse)
apply (simp (no_asm))
apply (simp (no_asm_simp))
done

declare has_type.intros [intro!]

lemma has_type_le_env [rule_format (no_asm)]: "A |- e::t \<Longrightarrow> \<forall>B. A \<le> B \<longrightarrow> B |- e::t"
apply (erule has_type.induct)
   apply (simp (no_asm) add: le_env_def)
   apply (fastforce elim: bound_typ_instance_trans)
  apply simp
 apply fast
apply (slow elim: le_env_free_tv [THEN free_tv_subset_gen_le])
done

\<comment> \<open>@{text has_type} is closed w.r.t. substitution\<close>
lemma has_type_cl_sub: "A |- e :: t \<Longrightarrow> \<forall>S. $S A |- e :: $S t"
apply (erule has_type.induct)
(* case VarI *)
   apply (rule allI)
   apply (rule has_type.VarI)
    apply (simp add: app_subst_list)
   apply (simp (no_asm_simp) add: app_subst_list)
  (* case AbsI *)
  apply (rule allI)
  apply (simp (no_asm))
  apply (rule has_type.AbsI)
  apply simp
 (* case AppI *)
 apply (rule allI)
 apply (rule has_type.AppI)
  apply simp
  apply (erule spec)
 apply (erule spec)
(* case LetI *)
apply (rule allI)
apply (rule replace_s_by_s')
apply (cut_tac A = "$ S A" and A' = "A" and t = "t" and t' = "$ S t" in ex_fresh_variable)
apply (erule exE)
apply (erule conjE)+ 
apply (rule_tac ?t1.0 = "$ ((\<lambda>x. if x : free_tv A Un free_tv t then S x else TVar x) \<circ> (\<lambda>x. if x : free_tv A then x else n + x)) t1" in has_type.LETI)
 apply (drule_tac x = " (\<lambda>x. if x : free_tv A Un free_tv t then S x else TVar x) \<circ> (\<lambda>x. if x : free_tv A then x else n + x) " in spec)
 apply (subst S'_A_eq_S'_alpha_A)
 apply assumption
apply (subst S_o_alpha_typ)
apply (subst gen_subst_commutes)
 apply (rule subset_antisym)
  apply (rule subsetI)
  apply (erule IntE)
  apply (drule free_tv_S' [THEN subsetD])
  apply (drule free_tv_alpha [THEN subsetD])
  apply (simp del: full_SetCompr_eq)
  apply (erule exE)
  apply (hypsubst)
  apply (subgoal_tac "new_tv (n + y) ($ S A) ")
   apply (subgoal_tac "new_tv (n + y) ($ S t) ")
    apply (subgoal_tac "new_tv (n + y) A")
     apply (subgoal_tac "new_tv (n + y) t")
      apply (drule new_tv_not_free_tv)+
      apply fast
     apply (rule new_tv_le) prefer 2 apply assumption apply simp
    apply (rule new_tv_le) prefer 2 apply assumption apply simp
   apply (rule new_tv_le) prefer 2 apply assumption apply simp
  apply (rule new_tv_le) prefer 2 apply assumption apply simp
 apply fast
apply (rule has_type_le_env)
 apply (drule spec)
 apply (drule spec)
 apply assumption
apply (rule app_subst_Cons [THEN subst])
apply (rule S_compatible_le_scheme_lists)
apply (simp (no_asm_simp))
done


end
