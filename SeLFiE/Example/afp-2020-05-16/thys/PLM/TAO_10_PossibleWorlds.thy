(*<*)
theory TAO_10_PossibleWorlds
imports TAO_9_PLM
begin
(*>*)

section\<open>Possible Worlds\<close>
text\<open>\label{TAO_PossibleWorlds}\<close>

locale PossibleWorlds = PLM
begin

subsection\<open>Definitions\<close>
text\<open>\label{TAO_PossibleWorlds_Definitions}\<close>

  definition Situation where
    "Situation x \<equiv> \<lparr>A!,x\<rparr> \<^bold>& (\<^bold>\<forall> F. \<lbrace>x,F\<rbrace> \<^bold>\<rightarrow> Propositional F)"

  definition EncodeProposition (infixl "\<^bold>\<Sigma>" 70) where
    "x\<^bold>\<Sigma>p \<equiv> \<lparr>A!,x\<rparr> \<^bold>& \<lbrace>x, \<^bold>\<lambda> x . p\<rbrace>"
  definition TrueInSituation (infixl "\<^bold>\<Turnstile>" 10) where
    "x \<^bold>\<Turnstile> p \<equiv> Situation x \<^bold>& x\<^bold>\<Sigma>p"
  definition PossibleWorld where
    "PossibleWorld x \<equiv> Situation x \<^bold>& \<^bold>\<diamond>(\<^bold>\<forall> p . x\<^bold>\<Sigma>p \<^bold>\<equiv> p)"

subsection\<open>Auxiliary Lemmas\<close>
text\<open>\label{TAO_PossibleWorlds_Aux}\<close>

  lemma possit_sit_1:
    "[Situation (x\<^sup>P) \<^bold>\<equiv> \<^bold>\<box>(Situation (x\<^sup>P)) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[Situation (x\<^sup>P) in v]"
      hence 1: "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<rightarrow> Propositional F) in v]"
        unfolding Situation_def by auto
      have "[\<^bold>\<box>\<lparr>A!,x\<^sup>P\<rparr> in v]"
        using 1[conj1, THEN oa_facts_2[deduction]] .
      moreover have "[\<^bold>\<box>(\<^bold>\<forall> F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<rightarrow> Propositional F) in v]"
         using 1[conj2] unfolding Propositional_def
         by (rule enc_prop_nec_2[deduction])
      ultimately show "[\<^bold>\<box>Situation (x\<^sup>P) in v]"
        unfolding Situation_def
        apply cut_tac apply (rule KBasic_3[equiv_rl])
        by (rule intro_elim_1)
    next
      assume "[\<^bold>\<box>Situation (x\<^sup>P) in v]"
      thus "[Situation (x\<^sup>P) in v]"
        using qml_2[axiom_instance, deduction] by auto
    qed

  lemma possworld_nec:
    "[PossibleWorld (x\<^sup>P) \<^bold>\<equiv> \<^bold>\<box>(PossibleWorld (x\<^sup>P)) in v]"
    apply (rule "\<^bold>\<equiv>I"; rule CP)
     subgoal unfolding PossibleWorld_def
     apply (rule KBasic_3[equiv_rl])
     apply (rule intro_elim_1)
      using possit_sit_1[equiv_lr] "\<^bold>&E"(1) apply blast
     using qml_3[axiom_instance, deduction] "\<^bold>&E"(2) by blast
    using qml_2[axiom_instance,deduction] by auto

  lemma TrueInWorldNecc:
    "[((x\<^sup>P) \<^bold>\<Turnstile> p) \<^bold>\<equiv> \<^bold>\<box>((x\<^sup>P) \<^bold>\<Turnstile> p) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[x\<^sup>P \<^bold>\<Turnstile> p in v]"
      hence "[Situation (x\<^sup>P) \<^bold>& (\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace>) in v]"
        unfolding TrueInSituation_def EncodeProposition_def .
      hence "[(\<^bold>\<box>Situation (x\<^sup>P) \<^bold>& \<^bold>\<box>\<lparr>A!,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<box>\<lbrace>x\<^sup>P, \<^bold>\<lambda>x. p\<rbrace> in v]"
        using "\<^bold>&I" "\<^bold>&E" possit_sit_1[equiv_lr] oa_facts_2[deduction]
              encoding[axiom_instance,deduction] by metis
      thus "[\<^bold>\<box>((x\<^sup>P) \<^bold>\<Turnstile> p) in v]"
        unfolding TrueInSituation_def EncodeProposition_def
        using KBasic_3[equiv_rl] "\<^bold>&I" "\<^bold>&E" by metis
    next
      assume "[\<^bold>\<box>(x\<^sup>P \<^bold>\<Turnstile> p) in v]"
      thus "[x\<^sup>P \<^bold>\<Turnstile> p in v]"
        using qml_2[axiom_instance,deduction] by auto
    qed


  lemma PossWorldAux:
    "[(\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . (\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> (\<^bold>\<exists> p . p \<^bold>& (F \<^bold>= (\<^bold>\<lambda> x . p))))))
       \<^bold>\<rightarrow> (PossibleWorld (x\<^sup>P)) in v]"
    proof (rule CP)
      assume DefX: "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . (\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv>
            (\<^bold>\<exists> p . p \<^bold>& (F \<^bold>= (\<^bold>\<lambda> x . p))))) in v]"
    
      have "[Situation (x\<^sup>P) in v]"
      proof -
        have "[\<lparr>A!,x\<^sup>P\<rparr> in v]"
          using DefX[conj1] .
        moreover have "[(\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<rightarrow> Propositional F) in v]"
          proof (rule "\<^bold>\<forall>I"; rule CP)
            fix F
            assume "[\<lbrace>x\<^sup>P,F\<rbrace> in v]"
            moreover have "[\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> (\<^bold>\<exists> p . p \<^bold>& (F \<^bold>= (\<^bold>\<lambda> x . p))) in v]"
              using DefX[conj2] cqt_1[axiom_instance, deduction] by auto
            ultimately have "[(\<^bold>\<exists> p . p \<^bold>& (F \<^bold>= (\<^bold>\<lambda> x . p))) in v]"
              using "\<^bold>\<equiv>E"(1) by blast
            then obtain p where "[p \<^bold>& (F \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
              by (rule "\<^bold>\<exists>E")
            hence "[(F \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
              by (rule "\<^bold>&E"(2))
            hence "[(\<^bold>\<exists> p . (F \<^bold>= (\<^bold>\<lambda> x . p))) in v]"
              by PLM_solver
            thus "[Propositional F in v]"
              unfolding Propositional_def .
          qed
        ultimately show "[Situation (x\<^sup>P) in v]"
          unfolding Situation_def by (rule "\<^bold>&I")
      qed
      moreover have "[\<^bold>\<diamond>(\<^bold>\<forall>p. x\<^sup>P \<^bold>\<Sigma> p \<^bold>\<equiv> p) in v]"
        unfolding EncodeProposition_def
        proof (rule TBasic[deduction]; rule "\<^bold>\<forall>I")
          fix q
          have EncodeLambda:
            "[\<lbrace>x\<^sup>P, \<^bold>\<lambda>x. q\<rbrace> \<^bold>\<equiv> (\<^bold>\<exists> p . p \<^bold>& ((\<^bold>\<lambda>x. q) \<^bold>= (\<^bold>\<lambda> x . p))) in v]"
            using DefX[conj2] by (rule cqt_1[axiom_instance, deduction])
          moreover {
             assume "[q in v]"
             moreover have "[(\<^bold>\<lambda>x. q) \<^bold>= (\<^bold>\<lambda> x . q) in v]"
              using id_eq_prop_prop_1 by auto
             ultimately have "[q \<^bold>& ((\<^bold>\<lambda>x. q) \<^bold>= (\<^bold>\<lambda> x . q)) in v]"
               by (rule "\<^bold>&I")
             hence "[\<^bold>\<exists> p . p \<^bold>& ((\<^bold>\<lambda>x. q) \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
               by PLM_solver
             moreover have "[\<lparr>A!,x\<^sup>P\<rparr> in v]"
               using DefX[conj1] .
             ultimately have "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lbrace>x\<^sup>P, \<^bold>\<lambda>x. q\<rbrace> in v]"
               using EncodeLambda[equiv_rl] "\<^bold>&I" by auto
          }
          moreover {
            assume "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lbrace>x\<^sup>P, \<^bold>\<lambda>x. q\<rbrace> in v]"
            hence "[\<lbrace>x\<^sup>P, \<^bold>\<lambda>x. q\<rbrace> in v]"
              using "\<^bold>&E"(2) by auto
            hence "[\<^bold>\<exists> p . p \<^bold>& ((\<^bold>\<lambda>x. q) \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
              using EncodeLambda[equiv_lr] by auto
            then obtain p where p_and_lambda_q_is_lambda_p:
              "[p \<^bold>& ((\<^bold>\<lambda>x. q) \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
              by (rule "\<^bold>\<exists>E")
            have "[\<lparr>(\<^bold>\<lambda> x . p), x\<^sup>P\<rparr> \<^bold>\<equiv> p in v]"
              apply (rule beta_C_meta_1)
              by show_proper
            hence "[\<lparr>(\<^bold>\<lambda> x . p), x\<^sup>P\<rparr> in v]"
              using p_and_lambda_q_is_lambda_p[conj1] "\<^bold>\<equiv>E"(2) by auto
            hence "[\<lparr>(\<^bold>\<lambda> x . q), x\<^sup>P\<rparr> in v]"
              using p_and_lambda_q_is_lambda_p[conj2, THEN id_eq_prop_prop_2[deduction]]
                l_identity[axiom_instance, deduction, deduction] by fast
            moreover have "[\<lparr>(\<^bold>\<lambda> x . q), x\<^sup>P\<rparr> \<^bold>\<equiv> q in v]"
              apply (rule beta_C_meta_1) by show_proper
            ultimately have "[q in v]"
              using "\<^bold>\<equiv>E"(1) by blast
          }
          ultimately show "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lbrace>x\<^sup>P,\<^bold>\<lambda>x. q\<rbrace> \<^bold>\<equiv> q in v]"
            using "\<^bold>&I" "\<^bold>\<equiv>I" CP by auto
        qed
    
      ultimately show "[PossibleWorld (x\<^sup>P) in v]"
        unfolding PossibleWorld_def by (rule "\<^bold>&I")
    qed

subsection\<open>For every syntactic Possible World there is a semantic Possible World\<close>
text\<open>\label{TAO_PossibleWorlds_SyntacticSemantic}\<close>

  theorem SemanticPossibleWorldForSyntacticPossibleWorlds:
    "\<forall> x . [PossibleWorld (x\<^sup>P) in w] \<longrightarrow>
     (\<exists> v . \<forall> p . [(x\<^sup>P \<^bold>\<Turnstile> p) in w] \<longleftrightarrow> [p in v])"
    proof
      fix x
      {
        assume PossWorldX: "[PossibleWorld (x\<^sup>P) in w]"
        hence SituationX: "[Situation (x\<^sup>P) in w]"
          unfolding PossibleWorld_def apply cut_tac by PLM_solver
        have PossWorldExpanded:
          "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<rightarrow> (\<^bold>\<exists>p. F \<^bold>= (\<^bold>\<lambda>x. p)))
            \<^bold>& \<^bold>\<diamond>(\<^bold>\<forall>p. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace> \<^bold>\<equiv> p) in w]"
           using PossWorldX
           unfolding PossibleWorld_def Situation_def
                     Propositional_def EncodeProposition_def .
        have AbstractX: "[\<lparr>A!,x\<^sup>P\<rparr> in w]"
          using PossWorldExpanded[conj1,conj1] .
        
        have "[\<^bold>\<diamond>(\<^bold>\<forall>p. \<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace> \<^bold>\<equiv> p) in w]"
          apply (PLM_subst_method
                 "\<lambda>p. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace>"
                 "\<lambda> p . \<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace>")
           subgoal using PossWorldExpanded[conj1,conj1,THEN oa_facts_2[deduction]]
                   using Semantics.T6 apply cut_tac by PLM_solver
          using PossWorldExpanded[conj2] .
    
        hence "\<exists>v. \<forall>p. ([\<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace> in v])
                        = [p in v]"
         unfolding diamond_def equiv_def conj_def
         apply (simp add: Semantics.T4 Semantics.T6 Semantics.T5
                          Semantics.T8)
         by auto
    
        then obtain v where PropsTrueInSemWorld:
          "\<forall>p. ([\<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace> in v]) = [p in v]"
          by auto
        {
          fix p
          {
            assume "[((x\<^sup>P) \<^bold>\<Turnstile> p) in w]"
            hence "[((x\<^sup>P) \<^bold>\<Turnstile> p) in v]"
              using TrueInWorldNecc[equiv_lr] Semantics.T6 by simp
            hence "[Situation (x\<^sup>P) \<^bold>& (\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace>) in v]"
              unfolding TrueInSituation_def EncodeProposition_def .
            hence "[\<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace> in v]"
              using "\<^bold>&E"(2) by blast
            hence "[p in v]"
              using PropsTrueInSemWorld by blast
          }
          moreover {
            assume "[p in v]"
            hence "[\<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace> in v]"
              using PropsTrueInSemWorld by blast
            hence "[(x\<^sup>P) \<^bold>\<Turnstile> p in v]"
              apply cut_tac unfolding TrueInSituation_def EncodeProposition_def
              apply (rule "\<^bold>&I") using SituationX[THEN possit_sit_1[equiv_lr]]
              subgoal using Semantics.T6 by auto
              apply (rule "\<^bold>&I")
              subgoal using AbstractX[THEN oa_facts_2[deduction]]
                using Semantics.T6 by auto
              by assumption
            hence "[\<^bold>\<box>((x\<^sup>P) \<^bold>\<Turnstile> p) in v]"
              using TrueInWorldNecc[equiv_lr] by simp
            hence "[(x\<^sup>P) \<^bold>\<Turnstile> p in w]"
              using Semantics.T6 by simp
          }
          ultimately have "[p in v] \<longleftrightarrow> [(x\<^sup>P) \<^bold>\<Turnstile> p in w]"
            by auto
        }
        hence "(\<exists> v . \<forall> p . [p in v] \<longleftrightarrow> [(x\<^sup>P) \<^bold>\<Turnstile> p in w])"
          by blast
      }
      thus "[PossibleWorld (x\<^sup>P) in w] \<longrightarrow>
            (\<exists>v. \<forall> p . [(x\<^sup>P) \<^bold>\<Turnstile> p in w] \<longleftrightarrow> [p in v])"
        by blast
    qed

subsection\<open>For every semantic Possible World there is a syntactic Possible World\<close>
text\<open>\label{TAO_PossibleWorlds_SemanticSyntactic}\<close>

  theorem SyntacticPossibleWorldForSemanticPossibleWorlds:
    "\<forall> v . \<exists> x . [PossibleWorld (x\<^sup>P) in w] \<and>
     (\<forall> p . [p in v] \<longleftrightarrow> [((x\<^sup>P) \<^bold>\<Turnstile> p) in w])"
    proof
      fix v
      have "[\<^bold>\<exists>x. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . (\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv>
            (\<^bold>\<exists> p . p \<^bold>& (F \<^bold>= (\<^bold>\<lambda> x . p))))) in v]"
        using A_objects[axiom_instance] by fast
      then obtain x where DefX:
        "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . (\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> (\<^bold>\<exists> p . p \<^bold>& (F \<^bold>= (\<^bold>\<lambda> x . p))))) in v]"
        by (rule "\<^bold>\<exists>E")
      hence PossWorldX: "[PossibleWorld (x\<^sup>P) in v]"
        using PossWorldAux[deduction] by blast
      hence "[PossibleWorld (x\<^sup>P) in w]"
        using possworld_nec[equiv_lr] Semantics.T6 by auto
      moreover have "(\<forall> p . [p in v] \<longleftrightarrow> [(x\<^sup>P) \<^bold>\<Turnstile> p in w])"
      proof
        fix q
        {
           assume "[q in v]"
           moreover have "[(\<^bold>\<lambda> x . q) \<^bold>= (\<^bold>\<lambda> x . q) in v]"
             using id_eq_prop_prop_1 by auto
           ultimately have "[q \<^bold>& (\<^bold>\<lambda> x . q) \<^bold>= (\<^bold>\<lambda> x . q) in v]"
             using "\<^bold>&I" by auto
           hence "[(\<^bold>\<exists> p . p \<^bold>& ((\<^bold>\<lambda> x . q) \<^bold>= (\<^bold>\<lambda> x . p))) in v]"
             by PLM_solver
           hence 4: "[\<lbrace>x\<^sup>P, (\<^bold>\<lambda> x . q)\<rbrace> in v]"
             using cqt_1[axiom_instance,deduction, OF DefX[conj2], equiv_rl]
             by blast
           have "[(x\<^sup>P \<^bold>\<Turnstile> q) in v]"
             unfolding TrueInSituation_def apply (rule "\<^bold>&I")
              using PossWorldX unfolding PossibleWorld_def
              using "\<^bold>&E"(1) apply blast
             unfolding EncodeProposition_def apply (rule "\<^bold>&I")
              using DefX[conj1] apply simp
             using 4 .
          hence "[(x\<^sup>P \<^bold>\<Turnstile> q) in w]"
            using TrueInWorldNecc[equiv_lr] Semantics.T6 by auto
        }
        moreover {
          assume "[(x\<^sup>P \<^bold>\<Turnstile> q) in w]"
          hence "[(x\<^sup>P \<^bold>\<Turnstile> q) in v]"
             using TrueInWorldNecc[equiv_lr] Semantics.T6
             by auto
          hence "[\<lbrace>x\<^sup>P, (\<^bold>\<lambda> x . q)\<rbrace> in v]"
            unfolding TrueInSituation_def EncodeProposition_def
            using "\<^bold>&E"(2) by blast
          hence "[(\<^bold>\<exists> p . p \<^bold>& ((\<^bold>\<lambda> x . q) \<^bold>= (\<^bold>\<lambda> x . p))) in v]"
            using cqt_1[axiom_instance,deduction, OF DefX[conj2], equiv_lr]
            by blast
          then obtain p where 4:
            "[(p \<^bold>& ((\<^bold>\<lambda> x . q) \<^bold>= (\<^bold>\<lambda> x . p))) in v]"
            by (rule "\<^bold>\<exists>E")
          have "[\<lparr>(\<^bold>\<lambda> x . p),x\<^sup>P\<rparr> \<^bold>\<equiv> p in v]"
            apply (rule beta_C_meta_1)
            by show_proper
          hence "[\<lparr>(\<^bold>\<lambda> x . q),x\<^sup>P\<rparr> \<^bold>\<equiv> p in v]"
              using l_identity[where \<beta>="(\<^bold>\<lambda> x . q)" and \<alpha>="(\<^bold>\<lambda> x . p)",
                               axiom_instance, deduction, deduction]
              using 4[conj2,THEN id_eq_prop_prop_2[deduction]] by meson
          hence "[\<lparr>(\<^bold>\<lambda> x . q),x\<^sup>P\<rparr> in v]" using 4[conj1] "\<^bold>\<equiv>E"(2) by blast
          moreover have "[\<lparr>(\<^bold>\<lambda> x . q),x\<^sup>P\<rparr> \<^bold>\<equiv> q in v]"
            apply (rule beta_C_meta_1)
            by show_proper
          ultimately have "[q in v]"
            using "\<^bold>\<equiv>E"(1) by blast
        }
        ultimately show "[q in v] \<longleftrightarrow> [(x\<^sup>P) \<^bold>\<Turnstile> q in w]"
          by blast
      qed
      ultimately show "\<exists> x . [PossibleWorld (x\<^sup>P) in w]
                           \<and> (\<forall> p . [p in v] \<longleftrightarrow> [(x\<^sup>P) \<^bold>\<Turnstile> p in w])"
        by auto
    qed
end

(*<*)
end
(*>*)
