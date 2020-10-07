theory TAO_99_Paradox
imports TAO_9_PLM TAO_98_ArtificialTheorems
begin

section\<open>Paradox\<close>

(*<*)
locale Paradox = PLM
begin
(*>*)

text\<open>
\label{TAO_Paradox_paradox}
Under the additional assumption that expressions of the form
@{term "(\<lambda>x . \<lparr>G,\<^bold>\<iota>y . \<phi> y x\<rparr>)"} for arbitrary \<open>\<phi>\<close> are
\emph{proper maps}, for which \<open>\<beta>\<close>-conversion holds,
the theory becomes inconsistent.
\<close>

subsection\<open>Auxiliary Lemmas\<close>

  lemma exe_impl_exists:
    "[\<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p), \<^bold>\<iota>y . \<phi> y x\<rparr> \<^bold>\<equiv> (\<^bold>\<exists>!y . \<^bold>\<A>\<phi> y x) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      fix \<phi> :: "\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>" and x :: \<nu> and v :: i
      assume "[\<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p),\<^bold>\<iota>y . \<phi> y x\<rparr> in v]"
      hence "[\<^bold>\<exists>y. \<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y)
              \<^bold>& \<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p), y\<^sup>P\<rparr> in v]"
        using nec_russell_axiom[equiv_lr] SimpleExOrEnc.intros by auto
      then obtain y where
        "[\<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y)
          \<^bold>& \<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p), y\<^sup>P\<rparr> in v]"
        by (rule Instantiate)
      hence "[\<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y) in v]"
        using "\<^bold>&E" by blast
      hence "[\<^bold>\<exists>y . \<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y) in v]"
        by (rule existential)
      thus "[\<^bold>\<exists>!y. \<^bold>\<A>\<phi> y x in v]"
        unfolding exists_unique_def by simp
    next
      fix \<phi> :: "\<nu>\<Rightarrow>\<nu>\<Rightarrow>\<o>" and x :: \<nu> and v :: i
      assume "[\<^bold>\<exists>!y. \<^bold>\<A>\<phi> y x in v]"
      hence "[\<^bold>\<exists>y. \<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y) in v]"
        unfolding exists_unique_def by simp
      then obtain y where
        "[\<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y) in v]"
        by (rule Instantiate)
      moreover have "[\<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p),y\<^sup>P\<rparr> in v]"
        apply (rule beta_C_meta_1[equiv_rl])
          apply show_proper
        by PLM_solver
      ultimately have "[\<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y)
                        \<^bold>& \<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p),y\<^sup>P\<rparr> in v]"
        using "\<^bold>&I" by blast
      hence "[\<^bold>\<exists> y . \<^bold>\<A>\<phi> y x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z x \<^bold>\<rightarrow> z \<^bold>= y)
              \<^bold>& \<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p),y\<^sup>P\<rparr> in v]"
        by (rule existential)
      thus "[\<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p), \<^bold>\<iota>y. \<phi> y x\<rparr> in v]"
        using nec_russell_axiom[equiv_rl]
          SimpleExOrEnc.intros by auto
    qed

  lemma exists_unique_actual_equiv:
    "[(\<^bold>\<exists>!y . \<^bold>\<A>(y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P))) \<^bold>\<equiv> \<^bold>\<A>\<psi> (x\<^sup>P) in v]"
  proof (rule "\<^bold>\<equiv>I"; rule CP)
    fix x v
    let ?\<phi> = "\<lambda> y x. y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)"
    assume "[\<^bold>\<exists>!y. \<^bold>\<A>?\<phi> y x in v]"
    hence "[\<^bold>\<exists>\<alpha>. \<^bold>\<A>?\<phi> \<alpha> x \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>?\<phi> \<beta> x \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
      unfolding exists_unique_def by simp
    then obtain \<alpha> where
      "[\<^bold>\<A>?\<phi> \<alpha> x \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>?\<phi> \<beta> x \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
      by (rule Instantiate)
    hence "[\<^bold>\<A>(\<alpha> \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)) in v]"
      using "\<^bold>&E" by blast
    thus "[\<^bold>\<A>(\<psi> (x\<^sup>P)) in v]"
      using Act_Basic_2[equiv_lr] "\<^bold>&E" by blast
  next
    fix x v
    let ?\<phi> = "\<lambda> y x. y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)"
    assume 1: "[\<^bold>\<A>\<psi> (x\<^sup>P) in v]"
    have "[x \<^bold>= x in v]"
      using id_eq_1[where 'a=\<nu>] by simp
    hence "[\<^bold>\<A>(x \<^bold>= x) in v]"
      using id_act_3[equiv_lr] by fast
    hence "[\<^bold>\<A>(x \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)) in v]"
      using 1 Act_Basic_2[equiv_rl] "\<^bold>&I" by blast
    hence "[\<^bold>\<A>?\<phi> x x in v]"
      by simp
    moreover have "[\<^bold>\<forall>\<beta>. \<^bold>\<A>?\<phi> \<beta> x \<^bold>\<rightarrow> \<beta> \<^bold>= x in v]"
    proof (rule "\<^bold>\<forall>I"; rule CP)
      fix \<beta>
      assume "[\<^bold>\<A>?\<phi> \<beta> x in v]"
      hence "[\<^bold>\<A>(\<beta> \<^bold>= x) in v]"
        using Act_Basic_2[equiv_lr] "\<^bold>&E" by fast
      thus "[\<beta> \<^bold>= x in v]" using id_act_3[equiv_rl] by fast
    qed      
    ultimately have "[\<^bold>\<A>?\<phi> x x \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>?\<phi> \<beta> x \<^bold>\<rightarrow> \<beta> \<^bold>= x) in v]"
      using "\<^bold>&I" by fast
    hence "[\<^bold>\<exists>\<alpha>. \<^bold>\<A>?\<phi> \<alpha> x \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>?\<phi> \<beta> x \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
      by (rule existential)
    thus "[\<^bold>\<exists>!y. \<^bold>\<A>?\<phi> y x in v]"
      unfolding exists_unique_def by simp
  qed

subsection\<open>Fake $\beta$-Conversion using Description Backdoor\<close>
text\<open>
  \label{TAO_Paradox_description_backdoor}
\<close>
    
  definition backdoor where
    "backdoor \<equiv> \<lambda> \<psi> . \<^bold>\<lambda>x . \<lparr>(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p), \<^bold>\<iota>y . y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)\<rparr>"
    
  lemma fake_beta:
    assumes "\<And> G \<phi>. IsProperInX (\<lambda>x . \<lparr>G,\<^bold>\<iota>y . \<phi> y x\<rparr>)"
    shows "[\<lparr>backdoor (\<lambda> x . \<psi> x), x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<A>\<psi> (x\<^sup>P) in v]"
  proof (rule "\<^bold>\<equiv>I"; rule CP)
    assume "[\<lparr>backdoor \<psi>,x\<^sup>P\<rparr> in v]"
    hence "[\<lparr>\<^bold>\<lambda>x. \<^bold>\<forall>p. p \<^bold>\<rightarrow> p,\<^bold>\<iota>y. y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)\<rparr> in v]"
      using beta_C_meta_1[equiv_lr, OF assms]
      unfolding backdoor_def identity_\<nu>_def by fast
    hence "[\<^bold>\<exists>!y. \<^bold>\<A> (y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)) in v]"
      using exe_impl_exists[equiv_lr] by fast
    thus "[\<^bold>\<A>\<psi> (x\<^sup>P) in v]"
      using exists_unique_actual_equiv[equiv_lr] by blast
  next
    assume "[\<^bold>\<A>\<psi> (x\<^sup>P) in v]"
    hence "[\<^bold>\<exists>!y. \<^bold>\<A> (y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)) in v]"
      using exists_unique_actual_equiv[equiv_rl] by blast
    hence "[\<lparr>\<^bold>\<lambda>x. \<^bold>\<forall>p. p \<^bold>\<rightarrow> p,\<^bold>\<iota>y. y \<^bold>= x \<^bold>& \<psi> (x\<^sup>P)\<rparr> in v]"
      using exe_impl_exists[equiv_rl] by fast
    thus "[\<lparr>backdoor \<psi>,x\<^sup>P\<rparr> in v]"
      using beta_C_meta_1[equiv_rl, OF assms]
      unfolding backdoor_def unfolding identity_\<nu>_def by fast
  qed

  lemma fake_beta_act:
    assumes "\<And> G \<phi>. IsProperInX (\<lambda>x . \<lparr>G,\<^bold>\<iota>y . \<phi> y x\<rparr>)"
    shows "[\<lparr>backdoor (\<lambda> x . \<psi> x), x\<^sup>P\<rparr> \<^bold>\<equiv> \<psi> (x\<^sup>P) in dw]"
    using fake_beta[OF assms]
      logic_actual[necessitation_averse_axiom_instance]
      intro_elim_6_e by blast

subsection\<open>Resulting Paradox\<close>

text\<open>
  \label{TAO_Paradox_russell-paradox}
\<close>
  
  lemma paradox:
    assumes "\<And> G \<phi>. IsProperInX (\<lambda>x . \<lparr>G,\<^bold>\<iota>y . \<phi> y x\<rparr>)"
    shows "False"
  proof -
    obtain K where K_def:
      "K = backdoor (\<lambda> x . \<^bold>\<exists> F . \<lbrace>x,F\<rbrace> \<^bold>& \<^bold>\<not>\<lparr>F,x\<rparr>)" by auto
    have "[\<^bold>\<exists>x. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> (F \<^bold>= K)) in dw]"
      using A_objects[axiom_instance] by fast
    then obtain x where x_prop:
      "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> (F \<^bold>= K)) in dw]"
      by (rule Instantiate)
    {
      assume "[\<lparr>K,x\<^sup>P\<rparr> in dw]"
      hence "[\<^bold>\<exists> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>& \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr> in dw]"
        unfolding K_def using fake_beta_act[OF assms, equiv_lr]
        by blast
      then obtain F where F_def:
        "[\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>& \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr> in dw]" by (rule Instantiate)
      hence "[F \<^bold>= K in dw]"
        using x_prop[conj2, THEN "\<^bold>\<forall>E"[where \<beta>=F], equiv_lr]
          "\<^bold>&E" unfolding K_def by blast
      hence "[\<^bold>\<not>\<lparr>K,x\<^sup>P\<rparr> in dw]"
        using l_identity[axiom_instance,deduction,deduction]
             F_def[conj2] by fast
    }
    hence 1: "[\<^bold>\<not>\<lparr>K,x\<^sup>P\<rparr> in dw]"
      using reductio_aa_1 by blast
    hence "[\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>& \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) in dw]"
      using fake_beta_act[OF assms,
            THEN oth_class_taut_5_d[equiv_lr],
            equiv_lr]
      unfolding K_def by blast
    hence "[\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<rightarrow> \<lparr>F,x\<^sup>P\<rparr> in dw]"
      apply - unfolding exists_def by PLM_solver
    moreover have "[\<lbrace>x\<^sup>P,K\<rbrace> in dw]"
      using x_prop[conj2, THEN "\<^bold>\<forall>E"[where \<beta>=K], equiv_rl]
            id_eq_1 by blast
    ultimately have "[\<lparr>K,x\<^sup>P\<rparr> in dw]"
      using "\<^bold>\<forall>E" vdash_properties_10 by blast
    hence "\<And>\<phi>. [\<phi> in dw]"
      using raa_cor_2 1 by blast
    thus "False" using Semantics.T4 by auto
  qed

subsection\<open>Original Version of the Paradox\<close>

text\<open>
  \label{TAO_Paradox_original-paradox}
  Originally the paradox was discovered using the following
  construction based on the comprehension theorem for relations
  without the explicit construction of the description backdoor
  and the resulting fake-\<open>\<beta>\<close>-conversion.
\<close>
  
  lemma assumes "\<And> G \<phi>. IsProperInX (\<lambda>x . \<lparr>G,\<^bold>\<iota>y . \<phi> y x\<rparr>)"
  shows Fx_equiv_xH: "[\<^bold>\<forall> H . \<^bold>\<exists> F . \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lbrace>x\<^sup>P,H\<rbrace>) in v]"
  proof (rule "\<^bold>\<forall>I")
    fix H
    let ?G = "(\<^bold>\<lambda>x . \<^bold>\<forall> p . p \<^bold>\<rightarrow> p)"
    obtain \<phi> where \<phi>_def: "\<phi> = (\<lambda> y x . (y\<^sup>P) \<^bold>= x \<^bold>& \<lbrace>x,H\<rbrace>)" by auto
    have "[\<^bold>\<exists>F. \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>?G,\<^bold>\<iota>y . \<phi> y (x\<^sup>P)\<rparr>) in v]"
      using relations_1[OF assms] by simp
    hence 1: "[\<^bold>\<exists>F. \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> (\<^bold>\<exists>!y . \<^bold>\<A>\<phi> y (x\<^sup>P))) in v]"
      apply - apply (PLM_subst_method
          "\<lambda> x . \<lparr>?G,\<^bold>\<iota>y . \<phi> y (x\<^sup>P)\<rparr>" "\<lambda> x . (\<^bold>\<exists>!y. \<^bold>\<A>\<phi> y (x\<^sup>P))")
      using exe_impl_exists by auto
    then obtain F where F_def: "[\<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> (\<^bold>\<exists>!y . \<^bold>\<A>\<phi> y (x\<^sup>P))) in v]"
      by (rule Instantiate)
    moreover have 2: "\<And> v x . [(\<^bold>\<exists>!y . \<^bold>\<A>\<phi> y (x\<^sup>P)) \<^bold>\<equiv> \<lbrace>x\<^sup>P,H\<rbrace> in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      fix x v
      assume "[\<^bold>\<exists>!y. \<^bold>\<A>\<phi> y (x\<^sup>P) in v]"
      hence "[\<^bold>\<exists>\<alpha>. \<^bold>\<A>\<phi> \<alpha> (x\<^sup>P) \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>\<phi> \<beta> (x\<^sup>P) \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
        unfolding exists_unique_def by simp
      then obtain \<alpha> where "[\<^bold>\<A>\<phi> \<alpha> (x\<^sup>P) \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>\<phi> \<beta> (x\<^sup>P) \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
        by (rule Instantiate)
      hence "[\<^bold>\<A>(\<alpha>\<^sup>P \<^bold>= x\<^sup>P \<^bold>& \<lbrace>x\<^sup>P,H\<rbrace>) in v]"
        unfolding \<phi>_def using "\<^bold>&E" by blast
      hence "[\<^bold>\<A>(\<lbrace>x\<^sup>P,H\<rbrace>) in v]"
        using Act_Basic_2[equiv_lr] "\<^bold>&E" by blast
      thus "[\<lbrace>x\<^sup>P,H\<rbrace> in v]"
        using en_eq_10[equiv_lr] by simp
    next
      fix x v
      assume "[\<lbrace>x\<^sup>P,H\<rbrace> in v]"
      hence 1: "[\<^bold>\<A>(\<lbrace>x\<^sup>P,H\<rbrace>) in v]"
        using en_eq_10[equiv_rl] by blast
      have "[x \<^bold>= x in v]"
        using id_eq_1[where 'a=\<nu>] by simp
      hence "[\<^bold>\<A>(x \<^bold>= x) in v]"
        using id_act_3[equiv_lr] by fast
      hence "[\<^bold>\<A>(x\<^sup>P \<^bold>= x\<^sup>P \<^bold>& \<lbrace>x\<^sup>P,H\<rbrace>) in v]"
        unfolding identity_\<nu>_def using 1 Act_Basic_2[equiv_rl] "\<^bold>&I" by blast
      hence "[\<^bold>\<A>\<phi> x (x\<^sup>P) in v]"
        unfolding \<phi>_def by simp
      moreover have "[\<^bold>\<forall>\<beta>. \<^bold>\<A>\<phi> \<beta> (x\<^sup>P) \<^bold>\<rightarrow> \<beta> \<^bold>= x in v]"
      proof (rule "\<^bold>\<forall>I"; rule CP)
        fix \<beta>
        assume "[\<^bold>\<A>\<phi> \<beta> (x\<^sup>P) in v]"
        hence "[\<^bold>\<A>(\<beta> \<^bold>= x) in v]"
          unfolding \<phi>_def identity_\<nu>_def
          using Act_Basic_2[equiv_lr] "\<^bold>&E" by fast
        thus "[\<beta> \<^bold>= x in v]" using id_act_3[equiv_rl] by fast
      qed      
      ultimately have "[\<^bold>\<A>\<phi> x (x\<^sup>P) \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>\<phi> \<beta> (x\<^sup>P) \<^bold>\<rightarrow> \<beta> \<^bold>= x) in v]"
        using "\<^bold>&I" by fast
      hence "[\<^bold>\<exists>\<alpha>. \<^bold>\<A>\<phi> \<alpha> (x\<^sup>P) \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>\<phi> \<beta> (x\<^sup>P) \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
        by (rule existential)
      thus "[\<^bold>\<exists>!y. \<^bold>\<A>\<phi> y (x\<^sup>P) in v]"
        unfolding exists_unique_def by simp
    qed
    have "[\<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lbrace>x\<^sup>P,H\<rbrace>) in v]"
      apply (PLM_subst_goal_method
          "\<lambda>\<phi> . \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> x)"
          "\<lambda> x . (\<^bold>\<exists>!y . \<^bold>\<A>\<phi> y (x\<^sup>P))")
      using 2 F_def by auto
    thus "[\<^bold>\<exists> F . \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lbrace>x\<^sup>P,H\<rbrace>) in v]"
      by (rule existential)
  qed

            
  lemma
    assumes is_propositional: "(\<And>G \<phi>. IsProperInX (\<lambda>x. \<lparr>G,\<^bold>\<iota>y. \<phi> y x\<rparr>))"
        and Abs_x: "[\<lparr>A!,x\<^sup>P\<rparr> in v]"
        and Abs_y: "[\<lparr>A!,y\<^sup>P\<rparr> in v]"
        and noteq: "[x \<^bold>\<noteq> y in v]"
  shows diffprop: "[\<^bold>\<exists> F . \<^bold>\<not>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
  proof -
    have "[\<^bold>\<exists> F . \<^bold>\<not>(\<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P, F\<rbrace>) in v]"
      using noteq unfolding exists_def
    proof (rule reductio_aa_2)
      assume 1: "[\<^bold>\<forall>F. \<^bold>\<not>\<^bold>\<not>(\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>) in v]"
      {
        fix F
        have "[(\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>) in v]"
          using 1[THEN "\<^bold>\<forall>E"] useful_tautologies_1[deduction] by blast
      }
      hence "[\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace> in v]" by (rule "\<^bold>\<forall>I")
      thus "[x \<^bold>= y in v]"
        unfolding identity_\<nu>_def
        using ab_obey_1[deduction, deduction]
              Abs_x Abs_y "\<^bold>&I" by blast
    qed
    then obtain H where H_def: "[\<^bold>\<not>(\<lbrace>x\<^sup>P, H\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P, H\<rbrace>) in v]"
      by (rule Instantiate)
    hence 2: "[(\<lbrace>x\<^sup>P, H\<rbrace> \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P, H\<rbrace>) \<^bold>\<or> (\<^bold>\<not>\<lbrace>x\<^sup>P, H\<rbrace> \<^bold>& \<lbrace>y\<^sup>P, H\<rbrace>) in v]"
      apply - by PLM_solver
    have "[\<^bold>\<exists>F. \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lbrace>x\<^sup>P,H\<rbrace>) in v]"
      using Fx_equiv_xH[OF is_propositional, THEN "\<^bold>\<forall>E"] by simp
    then obtain F where "[\<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lbrace>x\<^sup>P,H\<rbrace>) in v]"
      by (rule Instantiate)
    hence F_prop: "[\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lbrace>x\<^sup>P,H\<rbrace> in v]"
      using qml_2[axiom_instance, deduction] by blast
    hence a: "[\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lbrace>x\<^sup>P,H\<rbrace> in v]"
      using "\<^bold>\<forall>E" by blast
    have b: "[\<lparr>F,y\<^sup>P\<rparr> \<^bold>\<equiv> \<lbrace>y\<^sup>P,H\<rbrace> in v]"
      using F_prop "\<^bold>\<forall>E" by blast
    {
      assume 1: "[\<lbrace>x\<^sup>P, H\<rbrace> \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P, H\<rbrace> in v]"
      hence "[\<lparr>F,x\<^sup>P\<rparr> in v]"
        using a[equiv_rl] "\<^bold>&E" by blast
      moreover have "[\<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr> in v]"
        using b[THEN oth_class_taut_5_d[equiv_lr], equiv_rl] 1[conj2] by auto
      ultimately have "[\<lparr>F,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr>) in v]"
        by (rule "\<^bold>&I")
      hence "[(\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr>) \<^bold>\<or> (\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<lparr>F,y\<^sup>P\<rparr>) in v]"
        using "\<^bold>\<or>I" by blast
      hence "[\<^bold>\<not>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
        using oth_class_taut_5_j[equiv_rl] by blast
    }
    moreover {
      assume 1: "[\<^bold>\<not>\<lbrace>x\<^sup>P, H\<rbrace> \<^bold>& \<lbrace>y\<^sup>P, H\<rbrace> in v]"
      hence "[\<lparr>F,y\<^sup>P\<rparr> in v]"
        using b[equiv_rl] "\<^bold>&E" by blast
      moreover have "[\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr> in v]"
        using a[THEN oth_class_taut_5_d[equiv_lr], equiv_rl] 1[conj1] by auto
      ultimately have "[\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<lparr>F,y\<^sup>P\<rparr> in v]"
        using "\<^bold>&I" by blast
      hence "[(\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr>) \<^bold>\<or> (\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<lparr>F,y\<^sup>P\<rparr>) in v]"
        using "\<^bold>\<or>I" by blast
      hence "[\<^bold>\<not>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
        using oth_class_taut_5_j[equiv_rl] by blast
    }
    ultimately have "[\<^bold>\<not>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
      using 2 intro_elim_4_b reductio_aa_1 by blast
    thus "[\<^bold>\<exists> F . \<^bold>\<not>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
      by (rule existential)
  qed
      
  lemma original_paradox:
    assumes is_propositional: "(\<And>G \<phi>. IsProperInX (\<lambda>x. \<lparr>G,\<^bold>\<iota>y. \<phi> y x\<rparr>))"
    shows "False"
  proof -
    fix v
    have "[\<^bold>\<exists>x y. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y \<^bold>& (\<^bold>\<forall>F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
      using aclassical2 by auto
    then obtain x where
      "[\<^bold>\<exists> y. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y \<^bold>& (\<^bold>\<forall>F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
      by (rule Instantiate)
    then obtain y where xy_def:
      "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y \<^bold>& (\<^bold>\<forall>F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
      by (rule Instantiate)
    have "[\<^bold>\<exists> F . \<^bold>\<not>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
      using diffprop[OF assms, OF xy_def[conj1,conj1,conj1],
                     OF xy_def[conj1,conj1,conj2],
                     OF xy_def[conj1,conj2]]
      by auto
    then obtain F where "[\<^bold>\<not>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
      by (rule Instantiate)
    moreover have "[\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr> in v]"
      using xy_def[conj2] by (rule "\<^bold>\<forall>E")
    ultimately have "\<And>\<phi>.[\<phi> in v]"
      using PLM.raa_cor_2 by blast
    thus "False"
      using Semantics.T4 by auto
  qed

(*<*)
end
(*>*)

end
