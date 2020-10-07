section "Soundness"

theory Soundness imports Completeness begin

lemma permutation_validS: "fs <~~> gs --> (validS fs = validS gs)"
  apply(simp add: validS_def)
  apply(simp add: evalS_def)
  apply(simp add: perm_set_eq)
  done

lemma modelAssigns_vblcase: "phi \<in> modelAssigns M \<Longrightarrow>  x \<in> objects M \<Longrightarrow> vblcase x phi \<in> modelAssigns M"
  apply (simp add: modelAssigns_def, rule)
  apply(erule_tac rangeE)
  apply(case_tac xaa rule: vbl_casesE, auto)
  done

lemma tmp: "(!x : A. P x | Q) ==> (! x : A. P x) | Q " by blast

lemma soundnessFAll: "!!Gamma.
  [| u ~: freeVarsFL (FAll Pos A # Gamma); 
  validS (instanceF u A # Gamma) |] 
  ==> validS (FAll Pos A # Gamma)"
  apply (simp add: validS_def, rule)
  apply (drule_tac x=M in spec, rule)
  apply(simp add: evalF_instance)
  apply (rule tmp, rule)
  apply(drule_tac x="% y. if y = u then x else phi y" in bspec)
   apply(simp add: modelAssigns_def) apply force
  apply(erule disjE)
   apply (rule disjI1, simp)
   apply(subgoal_tac "evalF M (vblcase x (\<lambda>y. if y = u then x else phi y)) A = evalF M (vblcase x phi) A")
    apply force
   apply(rule evalF_equiv)
   apply(rule equalOn_vblcaseI)
    apply(rule,rule)
   apply(simp add: freeVarsFL_cons)
   apply (rule equalOnI, force)
  apply(rule disjI2)
  apply(subgoal_tac "evalS M (\<lambda>y. if y = u then x else phi y) Gamma = evalS M phi Gamma")
   apply force
  apply(rule evalS_equiv)
  apply(rule equalOnI)
  apply(force simp: freeVarsFL_cons)
  done

lemma soundnessFEx: "validS (instanceF x A # Gamma) ==> validS (FAll Neg A # Gamma)"
  apply(simp add: validS_def)
  apply (simp add: evalF_instance, rule, rule)
  apply(drule_tac x=M in spec)
  apply (drule_tac x=phi in bspec, assumption)
  apply(erule disjE)
  apply(rule disjI1)
  apply (rule_tac x="phi x" in bexI, assumption)
  apply(force dest: modelAssignsD subsetD)
  apply (rule disjI2, assumption)
  done

lemma soundnessFCut: "[| validS (C # Gamma); validS (FNot C # Delta) |] ==> validS (Gamma @ Delta)"
(*  apply(force simp: validS_def evalS_append evalS_cons evalF_FNot)*)
  apply (simp add: validS_def, rule, rule)
  apply(drule_tac x=M in spec)
  apply(drule_tac x=M in spec)
  apply(drule_tac x=phi in bspec) apply assumption
  apply(drule_tac x=phi in bspec) apply assumption
  apply (simp add: evalS_append evalF_FNot, blast)
  done

lemma soundness: "fs : deductions(PC) ==> (validS fs)"  
  apply(erule_tac deductions.induct)
  apply(drule_tac PowD)
  apply(subgoal_tac "prems \<subseteq>  {x. validS x}") prefer 2 apply force apply(thin_tac "prems \<subseteq> deductions PC \<inter> {x. validS x}")
  apply(simp add: subset_eq)
  apply(simp add: PC_def)
  apply(elim disjE)
          apply(force simp add: Perms_def permutation_validS)
         apply(force simp: Axioms_def validS_def evalS_def)
        apply(force simp: Conjs_def validS_def evalS_def)
       apply(force simp: Disjs_def validS_def evalS_def)
      apply(simp add: Alls_def)
      apply(force intro: soundnessFAll)
     apply(simp add: Exs_def)
     apply(force intro: soundnessFEx)
    apply(force simp: Weaks_def validS_def evalS_def)
   apply(force simp: Contrs_def validS_def evalS_def)
  apply(force simp: Cuts_def intro: soundnessFCut)
  done

lemma completeness: "fs : deductions (PC) = validS fs"
  apply rule
   apply(rule soundness) apply assumption
  apply(subgoal_tac "fs : deductions CutFreePC")
   apply(rule subsetD) prefer 2 apply assumption 
   apply(rule mono_deductions)
   apply(simp add: PC_def CutFreePC_def) apply blast
  apply(rule adequacy)
  by assumption

end
