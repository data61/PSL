(* Title:     HOL/MiniML/W.thy
   Author:    Dieter Nazareth, Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

section "Correctness and completeness of type inference algorithm W"

theory W
imports MiniML
begin

type_synonym result_W = "(subst * typ * nat) option"

\<comment> \<open>type inference algorithm W\<close>
primrec W :: "[expr, ctxt, nat] => result_W" where
  "W (Var i) A n =  
     (if i < length A then Some( id_subst,   
                                 bound_typ_inst (\<lambda>b. TVar(b+n)) (A!i),   
                                 n + (min_new_bound_tv (A!i)) )  
                      else None)"
  
| "W (Abs e) A n = ( (S,t,m) := W e ((FVar n)#A) (Suc n);
                     Some( S, (S n) -> t, m) )"
  
| "W (App e1 e2) A n = ( (S1,t1,m1) := W e1 A n;
                         (S2,t2,m2) := W e2 ($S1 A) m1;
                         U := mgu ($S2 t1) (t2 -> (TVar m2));
                         Some( $U \<circ> $S2 \<circ> S1, U m2, Suc m2) )"
  
| "W (LET e1 e2) A n = ( (S1,t1,m1) := W e1 A n;
                         (S2,t2,m2) := W e2 ((gen ($S1 A) t1)#($S1 A)) m1;
                         Some( $S2 \<circ> S1, t2, m2) )"


declare Suc_le_lessD [simp]

inductive_cases has_type_casesE:
"A |- Var n :: t"
"A |- Abs e :: t"
"A |- App e1 e2 ::t"
"A |- LET e1 e2 ::t"


\<comment> \<open>the resulting type variable is always greater or equal than the given one\<close>
lemma W_var_ge [rule_format (no_asm)]: 
  "\<forall>A n S t m. W e A n  = Some (S,t,m) \<longrightarrow> n\<le>m"
apply (induct_tac "e")
(* case Var(n) *)
apply (simp (no_asm) split: split_option_bind)
(* case Abs e *)
apply (simp (no_asm) split: split_option_bind)
apply (fast dest: Suc_leD)
(* case App e1 e2 *)
apply (simp (no_asm) split: split_option_bind)
apply (blast intro: le_SucI le_trans)
(* case LET e1 e2 *)
apply (simp (no_asm) split: split_option_bind)
apply (blast intro: le_trans)
done

declare W_var_ge [simp]

lemma W_var_geD: 
  "Some (S,t,m) = W e A n \<Longrightarrow> n\<le>m"
apply (simp add: eq_sym_conv)
done

lemma new_tv_compatible_W: 
  "new_tv n A \<Longrightarrow> Some (S,t,m) = W e A n \<Longrightarrow> new_tv m A"
apply (drule W_var_geD)
apply (rule new_scheme_list_le)
apply assumption
apply assumption
done

lemma new_tv_bound_typ_inst_sch [rule_format (no_asm)]: 
  "new_tv n sch \<longrightarrow> new_tv (n + (min_new_bound_tv sch)) (bound_typ_inst (\<lambda>b. TVar (b + n)) sch)"
apply (induct_tac "sch")
  apply simp
 apply (simp add: add.commute)
apply (intro strip)
apply simp
apply (erule conjE)
apply (rule conjI)
 apply (rule new_tv_le)
  prefer 2 apply (assumption)
 apply (rule add_le_mono)
  apply (simp (no_asm))
 apply (simp (no_asm) add: max_def)
apply (rule new_tv_le)
 prefer 2 apply (assumption)
apply (rule add_le_mono)
 apply (simp (no_asm))
apply (simp (no_asm) add: max_def)
done

declare new_tv_bound_typ_inst_sch [simp]

\<comment> \<open>resulting type variable is new\<close>
lemma new_tv_W [rule_format (no_asm)]: 
  "\<forall>n A S t m. new_tv n A \<longrightarrow> W e A n = Some (S,t,m) \<longrightarrow>     
               new_tv m S \<and> new_tv m t"
proof (induct e)
  case Var then show ?case
    apply (simp (no_asm) split: split_option_bind)
    apply (intro strip)
    apply (drule new_tv_nth_nat_A)
    apply assumption
    apply (simp (no_asm_simp))
    done
next
  case Abs then show ?case
    apply (simp (no_asm) add: new_tv_subst new_tv_Suc_list split: split_option_bind)
    apply (intro strip)
    apply (erule_tac x = "Suc n" in allE)
    apply (erule_tac x = " (FVar n) #A" in allE)
    apply (fastforce simp add: new_tv_subst new_tv_Suc_list)
    done
next
  case App then show ?case
    apply (simp (no_asm) split: split_option_bind)
    apply (intro strip)
    apply (rename_tac S1 t1 n1 S2 t2 n2 S3)
    apply (erule_tac x = "n" in allE)
    apply (erule_tac x = "A" in allE)
    apply (erule_tac x = "S1" in allE)
    apply (erule_tac x = "t1" in allE)
    apply (erule_tac x = "n1" in allE)
    apply (erule_tac x = "n1" in allE)
    apply (simp add: eq_sym_conv del: all_simps)
    apply (erule_tac x = "$S1 A" in allE)
    apply (erule_tac x = "S2" in allE)
    apply (erule_tac x = "t2" in allE)
    apply (erule_tac x = "n2" in allE)
    apply ( simp add: o_def rotate_Some)
    apply (rule conjI)
    apply (rule new_tv_subst_comp_2)
    apply (rule new_tv_subst_comp_2)
    apply (rule lessI [THEN less_imp_le, THEN new_tv_le])
    apply (rule_tac n = "n1" in new_tv_subst_le)
    apply (simp add: rotate_Some)
    apply (simp (no_asm_simp))
    apply (fast dest: W_var_geD intro: new_scheme_list_le new_tv_subst_scheme_list lessI [THEN less_imp_le [THEN new_tv_subst_le]])
    apply (erule sym [THEN mgu_new])
    apply (blast dest!: W_var_geD
      intro: lessI [THEN less_imp_le, THEN new_tv_le] new_tv_subst_te 
      new_tv_subst_scheme_list new_scheme_list_le new_tv_le)

    apply (erule impE)
    apply (blast dest: W_var_geD intro: new_tv_subst_scheme_list new_scheme_list_le new_tv_le)
    apply clarsimp

    apply (rule lessI [THEN new_tv_subst_var])
    apply (erule sym [THEN mgu_new])
    apply (blast dest!: W_var_geD
      intro: lessI [THEN less_imp_le, THEN new_tv_le] new_tv_subst_te 
      new_tv_subst_scheme_list new_scheme_list_le new_tv_le)

    apply (erule impE)
    apply (blast dest: W_var_geD intro: new_tv_subst_scheme_list new_scheme_list_le new_tv_le)
    apply clarsimp
    done
next
  case LET then show ?case
    apply (simp (no_asm) split: split_option_bind)
    apply (intro strip)
    apply (erule allE,erule allE,erule allE,erule allE,erule allE, erule impE, assumption, erule impE, assumption) 
    apply (erule conjE)
    apply (erule allE,erule allE,erule allE,erule allE,erule allE, erule impE, erule_tac [2] notE impE,
      tactic "assume_tac @{context} 2")
    apply (simp only: new_tv_def)
    apply (simp (no_asm_simp))
    apply (drule W_var_ge)+
    apply (rule allI)
    apply (intro strip)
    apply (simp only: free_tv_subst)
    apply (drule free_tv_app_subst_scheme_list [THEN subsetD])
    apply (best elim: less_le_trans)
    apply (erule conjE)
    apply (rule conjI)
    apply (simp only: o_def)
    apply (rule new_tv_subst_comp_2)
    apply (erule W_var_ge [THEN new_tv_subst_le])
    apply assumption
    apply assumption
    apply assumption
    done
qed

lemma free_tv_bound_typ_inst1 [rule_format (no_asm)]: 
  "(v \<notin> free_tv sch) \<longrightarrow> (v \<in> free_tv (bound_typ_inst (TVar \<circ> S) sch)) \<longrightarrow> (\<exists>x. v = S x)"
apply (induct_tac "sch")
apply simp
apply simp
apply (intro strip)
apply (rule exI)
apply (rule refl)
apply simp
done

declare free_tv_bound_typ_inst1 [simp]

lemma free_tv_W [rule_format (no_asm)]: 
  "\<forall>n A S t m v. W e A n = Some (S,t,m) \<longrightarrow>             
          (v\<in>free_tv S \<or> v\<in>free_tv t) \<longrightarrow> v<n \<longrightarrow> v\<in>free_tv A"
proof (induct e)
  case (Var n) then show ?case
    apply (simp (no_asm) add: free_tv_subst split: split_option_bind)
    apply (intro strip)
    apply (case_tac "v : free_tv (A!n)")
    apply simp
    apply (drule free_tv_bound_typ_inst1)
    apply (simp (no_asm) add: o_def)
    apply (erule exE)
    apply simp
    done
  case Abs then show ?case
    apply (simp add: free_tv_subst split: split_option_bind del: all_simps)
    apply (intro strip)
    apply (rename_tac S t n1 v)
    apply (erule_tac x = "Suc n" in allE)
    apply (erule_tac x = "FVar n # A" in allE)
    apply (erule_tac x = "S" in allE)
    apply (erule_tac x = "t" in allE)
    apply (erule_tac x = "n1" in allE)
    apply (erule_tac x = "v" in allE)
    apply (bestsimp intro: cod_app_subst simp add: less_Suc_eq)
    done
  case App then show ?case
    apply (simp (no_asm) split: split_option_bind del: all_simps)
    apply (intro strip)
    apply (rename_tac S t n1 S1 t1 n2 S2 v)
    apply (erule_tac x = "n" in allE)
    apply (erule_tac x = "A" in allE)
    apply (erule_tac x = "S" in allE)
    apply (erule_tac x = "t" in allE)
    apply (erule_tac x = "n1" in allE)
    apply (erule_tac x = "n1" in allE)
    apply (erule_tac x = "v" in allE)
    (* second case *)
    apply (erule_tac x = "$ S A" in allE)
    apply (erule_tac x = "S1" in allE)
    apply (erule_tac x = "t1" in allE)
    apply (erule_tac x = "n2" in allE)
    apply (erule_tac x = "v" in allE)
    apply (intro conjI impI | elim conjE)+
    apply (simp add: rotate_Some o_def)
    apply (drule W_var_geD)
    apply (drule W_var_geD)
    apply ( (frule less_le_trans) , (assumption))
    apply clarsimp 
    apply (drule free_tv_comp_subst [THEN subsetD])
    apply (drule sym [THEN mgu_free])
    apply clarsimp 
    apply (fastforce dest: free_tv_comp_subst [THEN subsetD] sym [THEN mgu_free] codD free_tv_app_subst_te [THEN subsetD] free_tv_app_subst_scheme_list [THEN subsetD] less_le_trans less_not_refl2 subsetD)
    apply simp
    apply (drule sym [THEN W_var_geD])
    apply (drule sym [THEN W_var_geD])
    apply ( (frule less_le_trans) , (assumption))
    apply clarsimp
    apply (drule mgu_free)
    apply (fastforce dest: mgu_free codD free_tv_subst_var [THEN subsetD] free_tv_app_subst_te [THEN subsetD] free_tv_app_subst_scheme_list [THEN subsetD] less_le_trans subsetD)
    done
next
  case LET then show ?case
    apply (simp (no_asm) split: split_option_bind del: all_simps)
    apply (intro strip)
    apply (rename_tac S1 t1 n2 S2 t2 n3 v)
    apply (erule_tac x = "n" in allE)
    apply (erule_tac x = "A" in allE)
    apply (erule_tac x = "S1" in allE)
    apply (erule_tac x = "t1" in allE)
    apply (rotate_tac -1)
    apply (erule_tac x = "n2" in allE)
    apply (rotate_tac -1)
    apply (erule_tac x = "v" in allE)
    apply (erule (1) notE impE)
    apply (erule allE,erule allE,erule allE,erule allE,erule allE,erule_tac  x = "v" in allE)
    apply (erule (1) notE impE)
    apply simp
    apply (rule conjI)
    apply (fast dest!: codD free_tv_app_subst_scheme_list [THEN subsetD] free_tv_o_subst [THEN subsetD] W_var_ge dest: less_le_trans)
    apply (fast dest!: codD free_tv_app_subst_scheme_list [THEN subsetD] W_var_ge dest: less_le_trans)
    done
qed

lemma weaken_A_Int_B_eq_empty: "(\<forall>x. x \<in> A \<longrightarrow> x \<notin> B) \<Longrightarrow> A \<inter> B = {}"
apply fast
done

lemma weaken_not_elem_A_minus_B: "x \<notin> A \<or> x \<in> B \<Longrightarrow> x \<notin> A - B"
apply fast
done

\<comment> \<open>correctness of W with respect to @{text has_type}\<close>
lemma W_correct_lemma [rule_format (no_asm)]: "\<forall>A S t m n . new_tv n A \<longrightarrow> Some (S,t,m) = W e A n \<longrightarrow> $S A |- e :: t"
apply (induct_tac "e")
(* case Var n *)
apply simp
apply (intro strip)
apply (rule has_type.VarI)
apply (simp (no_asm))
apply (simp (no_asm) add: is_bound_typ_instance)
apply (rule exI)
apply (rule refl)
(* case Abs e *)
apply (simp add: app_subst_list split: split_option_bind)
apply (intro strip)
apply (erule_tac x = " (mk_scheme (TVar n)) # A" in allE)
apply simp
apply (rule has_type.AbsI)
apply (drule le_refl [THEN le_SucI, THEN new_scheme_list_le])
apply (drule sym)
apply (erule allE)+
apply (erule impE)
apply (erule_tac [2] notE impE, tactic "assume_tac @{context} 2")
apply (simp (no_asm_simp))
apply assumption
(* case App e1 e2 *)
apply (simp (no_asm) split: split_option_bind)
apply (intro strip)
apply (rename_tac S1 t1 n1 S2 t2 n2 S3)
apply (rule_tac ?t2.0 = "$ S3 t2" in has_type.AppI)
apply (rule_tac S1 = "S3" in app_subst_TVar [THEN subst])
apply (rule app_subst_Fun [THEN subst])
apply (rule_tac t = "$S3 (t2 -> (TVar n2))" and s = "$S3 ($S2 t1) " in subst)
apply simp
apply (simp only: subst_comp_scheme_list [symmetric] o_def) 
apply ((rule has_type_cl_sub [THEN spec]) , (rule has_type_cl_sub [THEN spec]))
apply (simp add: eq_sym_conv)
apply (simp add: subst_comp_scheme_list [symmetric] o_def has_type_cl_sub eq_sym_conv)
apply (rule has_type_cl_sub [THEN spec])
apply (frule new_tv_W)
apply assumption
apply (drule conjunct1)
apply (frule new_tv_subst_scheme_list)
apply (rule new_scheme_list_le)
apply (rule W_var_ge)
apply assumption
apply assumption
apply (erule thin_rl)
apply (erule allE)+
apply (drule sym)
apply (drule sym)
apply (erule thin_rl)
apply (erule thin_rl)
apply (erule (1) notE impE)
apply (erule (1) notE impE)
apply assumption
(* case Let e1 e2 *)
apply (simp (no_asm) split: split_option_bind)
apply (intro strip)
(*by (rename_tac "w q m1 S1 t1 m2 S2 t n2" 1); *)
apply (rename_tac S1 t1 m1 S2)
apply (rule_tac ?t1.0 = "$ S2 t1" in has_type.LETI)
 apply (simp (no_asm) add: o_def)
 apply (simp only: subst_comp_scheme_list [symmetric])
 apply (rule has_type_cl_sub [THEN spec])
 apply (drule_tac x = "A" in spec)
 apply (drule_tac x = "S1" in spec)
 apply (drule_tac x = "t1" in spec)
 apply (drule_tac x = "m1" in spec)
 apply (drule_tac x = "n" in spec)
 apply (erule (1) notE impE)
 apply (simp add: eq_sym_conv)
apply (simp (no_asm) add: o_def)
apply (simp only: subst_comp_scheme_list [symmetric])
apply (rule gen_subst_commutes [symmetric, THEN subst])
 apply (rule_tac [2] app_subst_Cons [THEN subst])
 apply (erule_tac [2] thin_rl)
 apply (drule_tac [2] x = "gen ($S1 A) t1 # $ S1 A" in spec)
 apply (drule_tac [2] x = "S2" in spec)
 apply (drule_tac [2] x = "t" in spec)
 apply (drule_tac [2] x = "m" in spec)
 apply (drule_tac [2] x = "m1" in spec)
 apply (frule_tac [2] new_tv_W)
  prefer 2 apply (assumption)
 apply (drule_tac [2] conjunct1)
 apply (frule_tac [2] new_tv_subst_scheme_list)
  apply (rule_tac [2] new_scheme_list_le)
   apply (rule_tac [2] W_var_ge)
   prefer 2 apply (assumption)
  prefer 2 apply (assumption)
 apply (erule_tac [2] impE)
  apply (rule_tac [2] A = "$ S1 A" in new_tv_only_depends_on_free_tv_scheme_list)
   prefer 2 apply simp
   apply (fast)
  prefer 2 apply (assumption)
 prefer 2 apply simp
apply (rule weaken_A_Int_B_eq_empty)
apply (rule allI)
apply (intro strip)
apply (rule weaken_not_elem_A_minus_B)
apply (case_tac "x < m1")
 apply (rule disjI2)
 apply (rule free_tv_gen_cons [THEN subst])
 apply (rule free_tv_W)
   apply assumption
  apply simp
 apply assumption
apply (rule disjI1)
apply (drule new_tv_W)
apply assumption
apply (drule conjunct2)
apply (rule new_tv_not_free_tv)
apply (rule new_tv_le)
 prefer 2 apply (assumption)
apply (simp add: linorder_not_less)
done

\<comment> \<open>Completeness of W w.r.t. @{text has_type}\<close>
lemma W_complete_lemma [rule_format (no_asm)]: 
  "\<forall>S' A t' n. $S' A |- e :: t' \<longrightarrow> new_tv n A \<longrightarrow>
               (\<exists>S t. (\<exists>m. W e A n = Some (S,t,m)) \<and>
                       (\<exists>R. $S' A = $R ($S A) \<and> t' = $R t))"
apply (induct e)
   (* case Var n *)
   apply (intro strip)
   apply (simp (no_asm) cong add: conj_cong)
   apply (erule has_type_casesE)
   apply (simp add: is_bound_typ_instance)
   apply (erule exE)
   apply (hypsubst)
   apply (rename_tac "S")
   apply (rule_tac x = "\<lambda>x. (if x < n then S' x else S (x - n))" in exI)
   apply (rule conjI)
   apply (simp (no_asm_simp))
   apply (simp (no_asm_simp) add: bound_typ_inst_composed_subst [symmetric] new_tv_nth_nat_A o_def nth_subst 
                             del: bound_typ_inst_composed_subst)

  (* case Abs e *)
  apply (intro strip)
  apply (erule has_type_casesE)
  apply (erule_tac x = "\<lambda>x. if x=n then t1 else (S' x) " in allE)
  apply (erule_tac x = " (FVar n) #A" in allE)
  apply (erule_tac x = "t2" in allE)
  apply (erule_tac x = "Suc n" in allE)
  apply (bestsimp dest!: mk_scheme_injective cong: conj_cong split: split_option_bind)

 (* case App e1 e2 *)
 apply (intro strip)
 apply (erule has_type_casesE)
 apply (erule_tac x = "S'" in allE)
 apply (erule_tac x = "A" in allE)
 apply (erule_tac x = "t2 -> t'" in allE)
 apply (erule_tac x = "n" in allE)
 apply safe
 apply (erule_tac x = "R" in allE)
 apply (erule_tac x = "$ S A" in allE)
 apply (erule_tac x = "t2" in allE)
 apply (erule_tac x = "m" in allE)
 apply simp
 apply safe
  apply (blast intro: sym [THEN W_var_geD] new_tv_W [THEN conjunct1] new_scheme_list_le new_tv_subst_scheme_list)
 
 (** LEVEL 33 **)
apply (subgoal_tac "$ (\<lambda>x. if x=ma then t' else (if x: (free_tv t - free_tv Sa) then R x else Ra x)) ($ Sa t) = $ (\<lambda>x. if x=ma then t' else (if x: (free_tv t - free_tv Sa) then R x else Ra x)) (ta -> (TVar ma))")
apply (rule_tac [2] t = "$ (\<lambda>x. if x = ma then t' else (if x: (free_tv t - free_tv Sa) then R x else Ra x)) ($ Sa t) " and s = " ($ Ra ta) -> t'" in ssubst)
prefer 2 apply (simp (no_asm_simp) add: subst_comp_te) prefer 2
apply (rule_tac [2] eq_free_eq_subst_te)
prefer 2 apply (intro strip) prefer 2
apply (subgoal_tac [2] "na \<noteq>ma")
 prefer 3 apply (best dest: new_tv_W sym [THEN W_var_geD] new_tv_not_free_tv new_tv_le)
apply (case_tac [2] "na:free_tv Sa")
(* n1 \<notin> free_tv S1 *)
apply (frule_tac [3] not_free_impl_id)
 prefer 3 apply (simp)
(* na : free_tv Sa *)
apply (drule_tac [2] A1 = "$ S A" in trans [OF _ subst_comp_scheme_list])
apply (drule_tac [2] eq_subst_scheme_list_eq_free)
 prefer 2 apply (fast intro: free_tv_W free_tv_le_new_tv dest: new_tv_W)
prefer 2 apply (simp (no_asm_simp)) prefer 2
apply (case_tac [2] "na:dom Sa")
(* na \<notin> dom Sa *)
 prefer 3 apply (simp add: dom_def)
(* na : dom Sa *)
apply (rule_tac [2] eq_free_eq_subst_te)
prefer 2 apply (intro strip) prefer 2
apply (subgoal_tac [2] "nb \<noteq> ma")
apply (frule_tac [3] new_tv_W) prefer 3 apply assumption
apply (erule_tac [3] conjE)
apply (drule_tac [3] new_tv_subst_scheme_list)
   prefer 3 apply (fast intro: new_scheme_list_le dest: sym [THEN W_var_geD])
  prefer 3 apply (fastforce dest: new_tv_W new_tv_not_free_tv simp add: cod_def free_tv_subst)
 prefer 2 apply (fastforce simp add: cod_def free_tv_subst)
prefer 2 apply (simp (no_asm)) prefer 2
apply (rule_tac [2] eq_free_eq_subst_te)
prefer 2 apply (intro strip) prefer 2
apply (subgoal_tac [2] "na \<noteq> ma")
apply (frule_tac [3] new_tv_W) prefer 3 apply assumption
apply (erule_tac [3] conjE)
apply (drule_tac [3] sym [THEN W_var_geD])
 prefer 3 apply (fast dest: new_scheme_list_le new_tv_subst_scheme_list new_tv_W new_tv_not_free_tv)
apply (case_tac [2] "na: free_tv t - free_tv Sa")
(* case na \<notin> free_tv t - free_tv Sa *)
 prefer 3 
 apply simp
 apply fast
(* case na : free_tv t - free_tv Sa *)
prefer 2 apply simp prefer 2
apply (drule_tac [2] A1 = "$ S A" and r = "$ R ($ S A)" in trans [OF _ subst_comp_scheme_list])
apply (drule_tac [2] eq_subst_scheme_list_eq_free)
 prefer 2 
 apply (fast intro: free_tv_W free_tv_le_new_tv dest: new_tv_W)
(** LEVEL 73 **)
 prefer 2 apply (simp add: free_tv_subst dom_def)
apply (simp (no_asm_simp) split: split_option_bind)
apply safe
apply (drule mgu_Some)
 apply fastforce  
(** LEVEL 78 *)
apply (drule mgu_mg, assumption)
apply (erule exE)
apply (rule_tac x = "Rb" in exI)
apply (rule conjI)
apply (drule_tac [2] x = "ma" in fun_cong)
 prefer 2 apply (simp add: eq_sym_conv)
apply (simp (no_asm) add: subst_comp_scheme_list)
apply (simp (no_asm) add: subst_comp_scheme_list [symmetric])
apply (rule_tac A1 = "($ Sa ($ S A))" in trans [OF _ subst_comp_scheme_list [symmetric]])
apply (simp add: o_def eq_sym_conv)
apply (drule_tac s = "Some _" in sym)
apply (rule eq_free_eq_subst_scheme_list)
apply safe
apply (subgoal_tac "ma \<noteq> na")
apply (frule_tac [2] new_tv_W) prefer 2 apply assumption
apply (erule_tac [2] conjE)
apply (drule_tac [2] new_tv_subst_scheme_list)
 prefer 2 apply (fast intro: new_scheme_list_le dest: sym [THEN W_var_geD])
apply (frule_tac [2] n = "m" in new_tv_W) prefer 2 apply assumption
apply (erule_tac [2] conjE)
apply (drule_tac [2] free_tv_app_subst_scheme_list [THEN subsetD])
 apply (tactic \<open>
    (fast_tac (put_claset (claset_of @{theory_context Fun}) @{context}
      addDs [sym RS @{thm W_var_geD}, @{thm new_scheme_list_le}, @{thm codD},
        @{thm new_tv_not_free_tv}]) 2)\<close>)
apply (case_tac "na: free_tv t - free_tv Sa")
(* case na \<notin> free_tv t - free_tv Sa *)
 prefer 2 apply simp apply blast
(* case na : free_tv t - free_tv Sa *)
apply simp
apply (drule free_tv_app_subst_scheme_list [THEN subsetD])
 apply (fastforce dest: codD trans [OF _ subst_comp_scheme_list]
                       eq_subst_scheme_list_eq_free 
             simp add: free_tv_subst dom_def)
(* case Let e1 e2 *)
apply (erule has_type_casesE)
apply (erule_tac x = "S'" in allE)
apply (erule_tac x = "A" in allE)
apply (erule_tac x = "t1" in allE)
apply (erule_tac x = "n" in allE)
apply (erule (1) notE impE)
apply (erule (1) notE impE)
apply safe  
apply (simp (no_asm_simp))
apply (erule_tac x = "R" in allE)
apply (erule_tac x = "gen ($ S A) t # $ S A" in allE)
apply (erule_tac x = "t'" in allE)
apply (erule_tac x = "m" in allE)
apply simp
apply (drule mp)
apply (rule has_type_le_env)
apply assumption
apply (simp (no_asm))
apply (rule gen_bound_typ_instance)
apply (drule mp)
apply (frule new_tv_compatible_W)
apply (rule sym)
apply assumption
apply (fast dest: new_tv_compatible_gen new_tv_subst_scheme_list new_tv_W)
apply safe
apply simp
apply (rule_tac x = "Ra" in exI)
apply (simp (no_asm) add: o_def subst_comp_scheme_list [symmetric])
done


lemma W_complete: 
  "[] |- e :: t' \<Longrightarrow> (\<exists>S t. (\<exists>m. W e [] n = Some(S,t,m)) \<and>
                     (\<exists>R. t' = $ R t))"
apply (cut_tac A = "[]" and S' = "id_subst" and e = "e" and t' = "t'" in W_complete_lemma)
apply simp_all
done

end
