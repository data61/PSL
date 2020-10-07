(* Title:     HOL/MiniML/Instance.thy
   Author:    Wolfgang Naraschewski and Tobias Nipkow
   Copyright  1996 TU Muenchen
*)

section "Instances of type schemes"

theory Instance
imports Type
begin

primrec bound_typ_inst :: "[subst, type_scheme] => typ" where
  "bound_typ_inst S (FVar n) = (TVar n)"
| "bound_typ_inst S (BVar n) = (S n)"
| "bound_typ_inst S (sch1 =-> sch2) = ((bound_typ_inst S sch1) -> (bound_typ_inst S sch2))"

primrec bound_scheme_inst :: "[nat => type_scheme, type_scheme] => type_scheme" where
  "bound_scheme_inst S (FVar n) = (FVar n)"
| "bound_scheme_inst S (BVar n) = (S n)"
| "bound_scheme_inst S (sch1 =-> sch2) = ((bound_scheme_inst S sch1) =-> (bound_scheme_inst S sch2))"
  
definition is_bound_typ_instance :: "[typ, type_scheme] => bool"  (infixr "<|" 70) where
  is_bound_typ_instance: "t <| sch = (\<exists>S. t = (bound_typ_inst S sch))"

instantiation type_scheme :: ord
begin

definition
  le_type_scheme_def: "sch' \<le> (sch::type_scheme) \<longleftrightarrow> (\<forall>t. t <| sch' \<longrightarrow> t <| sch)"

definition
  "(sch' < (sch :: type_scheme)) \<longleftrightarrow> sch' \<le> sch \<and> sch' \<noteq> sch"

instance ..

end

primrec subst_to_scheme :: "[nat => type_scheme, typ] => type_scheme" where
  "subst_to_scheme B (TVar n) = (B n)"
| "subst_to_scheme B (t1 -> t2) = ((subst_to_scheme B t1) =-> (subst_to_scheme B t2))"
  
instantiation list :: (ord) ord
begin

definition
  le_env_def: "A \<le> B \<longleftrightarrow> length B = length A \<and> (\<forall>i. i < length A \<longrightarrow> A!i \<le> B!i)"

definition
  "(A < (B :: 'a list)) \<longleftrightarrow> A \<le> B \<and> A \<noteq> B"

instance ..

end

text "lemmas for instatiation"

lemma bound_typ_inst_mk_scheme [simp]: "bound_typ_inst S (mk_scheme t) = t"
  by (induct t) simp_all

lemma bound_typ_inst_composed_subst [simp]:
    "bound_typ_inst ($S \<circ> R) ($S sch) = $S (bound_typ_inst R sch)"
  by (induct sch) simp_all

lemma bound_typ_inst_eq:
    "S = S' \<Longrightarrow> sch = sch' \<Longrightarrow> bound_typ_inst S sch = bound_typ_inst S' sch'"
  by simp

lemma bound_scheme_inst_mk_scheme [simp]:
    "bound_scheme_inst B (mk_scheme t) = mk_scheme t"
  by (induct t) simp_all

lemma substitution_lemma: "$S (bound_scheme_inst B sch) = (bound_scheme_inst ($S \<circ> B) ($ S sch))"
  by (induct sch) simp_all

lemma bound_scheme_inst_type [rule_format]: "\<forall>t. mk_scheme t = bound_scheme_inst B sch \<longrightarrow>  
          (\<exists>S. \<forall>x\<in>bound_tv sch. B x = mk_scheme (S x))"
apply (induct_tac "sch")
apply (simp (no_asm))
apply safe
apply (rule exI)
apply (rule ballI)
apply (rule sym)
apply simp
apply (rename_tac type_scheme1 type_scheme2 t)
apply simp
apply (drule mk_scheme_Fun)
apply (erule exE)+
apply (erule conjE)
apply (drule sym)
apply (drule sym)
apply (drule mp, fast)+
apply safe
apply (rename_tac S1 S2)
apply (rule_tac x = "\<lambda>x. if x:bound_tv type_scheme1 then (S1 x) else (S2 x) " in exI)
apply auto
done

lemma subst_to_scheme_inverse: 
  "new_tv n sch \<Longrightarrow>
    subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k)  
      (bound_typ_inst (\<lambda>k. TVar (k + n)) sch) = sch"
  apply (induct sch)
    apply (simp add: not_le)
   apply (simp add: le_add2 diff_add_inverse2)
  apply simp
  done

lemma aux: "t = t' \<Longrightarrow>  
      subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k) t =  
      subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k) t'"
  by blast

lemma aux2: "new_tv n sch \<Longrightarrow>
  subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k) (bound_typ_inst S sch) =  
    bound_scheme_inst ((subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k)) \<circ> S) sch"
    by (induct sch) auto

lemma le_type_scheme_def2:
  fixes sch sch' :: type_scheme
  shows "(sch' \<le> sch) = (\<exists>B. sch' = bound_scheme_inst B sch)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (rule iffI)
apply (cut_tac sch = "sch" in fresh_variable_type_schemes)
apply (cut_tac sch = "sch'" in fresh_variable_type_schemes)
apply (drule make_one_new_out_of_two)
apply assumption
apply (erule_tac V = "\<exists>n. new_tv n sch'" in thin_rl)
apply (erule exE)
apply (erule allE)
apply (drule mp)
apply (rule_tac x = " (\<lambda>k. TVar (k + n))" in exI)
apply (rule refl)
apply (erule exE)
apply (erule conjE)+
apply (drule_tac n = "n" in aux)
apply (simp add: subst_to_scheme_inverse)
apply (rule_tac x = " (subst_to_scheme (\<lambda>k. if n \<le> k then BVar (k - n) else FVar k)) \<circ> S" in exI)
apply (simp (no_asm_simp) add: aux2)
apply safe
apply (rule_tac x = "\<lambda>n. bound_typ_inst S (B n) " in exI)
apply (induct_tac "sch")
apply (simp (no_asm))
apply (simp (no_asm))
apply (simp (no_asm_simp))
done

lemma le_type_eq_is_bound_typ_instance [rule_format]: "(mk_scheme t) \<le> sch = t <| sch"
apply (unfold is_bound_typ_instance)
apply (simp (no_asm) add: le_type_scheme_def2)
apply (rule iffI)
apply (erule exE)
apply (frule bound_scheme_inst_type)
apply (erule exE)
apply (rule exI)
apply (rule mk_scheme_injective)
apply simp
apply (rotate_tac 1)
apply (rule mp)
prefer 2 apply (assumption)
apply (induct_tac "sch")
apply (simp (no_asm))
apply simp
apply fast
apply (intro strip)
apply simp
apply (erule exE)
apply simp
apply (rule exI)
apply (induct_tac "sch")
apply (simp (no_asm))
apply (simp (no_asm))
apply simp
done

lemma le_env_Cons [iff]: 
  "(sch # A \<le> sch' # B) = (sch \<le> (sch'::type_scheme) \<and> A \<le> B)"
apply (unfold le_env_def)
apply (simp (no_asm))
apply (rule iffI)
 apply clarify
 apply (rule conjI) 
  apply (erule_tac x = "0" in allE)
  apply simp
 apply (rule conjI, assumption)
 apply clarify
 apply (erule_tac x = "Suc i" in allE) 
 apply simp
apply (rule conjI)
 apply fast
apply (rule allI)
apply (induct_tac "i")
apply simp_all
done

lemma is_bound_typ_instance_closed_subst: "t <| sch \<Longrightarrow> $S t <| $S sch"
apply (unfold is_bound_typ_instance)
apply (erule exE)
apply (rename_tac "SA") 
apply simp
apply (rule_tac x = "$S \<circ> SA" in exI)
apply simp
done

lemma S_compatible_le_scheme:
  fixes sch sch' :: type_scheme
  shows "sch' \<le> sch \<Longrightarrow> $S sch' \<le> $ S sch"
apply (simp add: le_type_scheme_def2)
apply (erule exE)
apply (simp add: substitution_lemma)
apply fast
done

lemma S_compatible_le_scheme_lists: 
  fixes A A' :: "type_scheme list"
  shows "A' \<le> A \<Longrightarrow> $S A' \<le> $ S A"
apply (unfold le_env_def app_subst_list)
apply (simp cong add: conj_cong)
apply (fast intro!: S_compatible_le_scheme)
done

lemma bound_typ_instance_trans: "[| t <| sch; sch \<le> sch' |] ==> t <| sch'"
  unfolding le_type_scheme_def by blast

lemma le_type_scheme_refl [iff]: "sch \<le> (sch::type_scheme)"
  unfolding le_type_scheme_def by blast

lemma le_env_refl [iff]: "A \<le> (A::type_scheme list)"
  unfolding le_env_def by blast

lemma bound_typ_instance_BVar [iff]: "sch \<le> BVar n"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (intro strip)
apply (rule_tac x = "\<lambda>a. t" in exI)
apply simp
done

lemma le_FVar [simp]: "(sch \<le> FVar n) = (sch = FVar n)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply (induct_tac "sch")
apply auto
done

lemma not_FVar_le_Fun [iff]: "~(FVar n \<le> sch1 =-> sch2)"
  unfolding le_type_scheme_def is_bound_typ_instance by simp

lemma not_BVar_le_Fun [iff]: "~(BVar n \<le> sch1 =-> sch2)"
apply (unfold le_type_scheme_def is_bound_typ_instance)
apply simp
apply (rule_tac x = "TVar n" in exI)
apply fastforce
done

lemma Fun_le_FunD: 
  "(sch1 =-> sch2 \<le> sch1' =-> sch2') \<Longrightarrow> sch1 \<le> sch1' \<and> sch2 \<le> sch2'"
  unfolding le_type_scheme_def is_bound_typ_instance by fastforce

lemma scheme_le_Fun: "(sch' \<le> sch1 =-> sch2) \<Longrightarrow> \<exists>sch'1 sch'2. sch' = sch'1 =-> sch'2"
  by (induct sch') auto

lemma le_type_scheme_free_tv [rule_format]:
  "\<forall>sch'::type_scheme. sch \<le> sch' \<longrightarrow> free_tv sch' \<le> free_tv sch"
apply (induct_tac "sch")
  apply (rule allI)
  apply (induct_tac "sch'")
    apply (simp (no_asm))
   apply (simp (no_asm))
  apply (simp (no_asm))
 apply (rule allI)
 apply (induct_tac "sch'")
   apply (simp (no_asm))
  apply (simp (no_asm))
 apply (simp (no_asm))
apply (rule allI)
apply (induct_tac "sch'")
  apply (simp (no_asm))
 apply (simp (no_asm))
apply simp
apply (intro strip)
apply (drule Fun_le_FunD)
apply fast
done

lemma le_env_free_tv [rule_format]:
  "\<forall>A::type_scheme list. A \<le> B \<longrightarrow> free_tv B \<le> free_tv A"
apply (induct_tac "B")
 apply (simp (no_asm))
apply (rule allI)
apply (induct_tac "A")
 apply (simp (no_asm) add: le_env_def)
apply (simp (no_asm))
apply (fast dest: le_type_scheme_free_tv)
done

end
