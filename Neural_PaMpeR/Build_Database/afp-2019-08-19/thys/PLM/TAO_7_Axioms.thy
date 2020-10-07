(*<*)
theory TAO_7_Axioms
imports TAO_6_Identifiable
begin
(*>*)

section\<open>The Axioms of PLM\<close>
text\<open>\label{TAO_Axioms}\<close>

text\<open>
\begin{remark}
  The axioms of PLM can now be derived from the Semantics
  and the model structure.
\end{remark}
\<close>

(* TODO: why is this needed again here? The syntax should already
         have been disabled in TAO_Semantics. *)
(* disable list syntax [] to replace it with truth evaluation *)
(*<*) no_syntax "_list" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 
(*<*) no_syntax "__listcompr" :: "args \<Rightarrow> 'a list" ("[(_)]") (*>*) 

locale Axioms
begin
  interpretation MetaSolver .
  interpretation Semantics .
  named_theorems axiom

text\<open>
\begin{remark}
  The special syntax \<open>[[_]]\<close> is introduced for stating the axioms.
  Modally-fragile axioms are stated with the syntax for actual validity \<open>[_]\<close>.
\end{remark}
\<close>

  definition axiom :: "\<o>\<Rightarrow>bool" ("[[_]]") where "axiom \<equiv> \<lambda> \<phi> . \<forall> v . [\<phi> in v]"

  method axiom_meta_solver = ((((unfold axiom_def)?, rule allI) | (unfold actual_validity_def)?), meta_solver,
                              (simp | (auto; fail))?)

subsection\<open>Closures\<close>
text\<open>\label{TAO_Axioms_Closures}\<close>

  text\<open>
\begin{remark}
  Rules resembling the concepts of closures in PLM are derived. Theorem attributes are introduced
  to aid in the instantiation of the axioms.
\end{remark}
\<close>

  lemma axiom_instance[axiom]: "[[\<phi>]] \<Longrightarrow> [\<phi> in v]"
    unfolding axiom_def by simp
  lemma closures_universal[axiom]: "(\<And>x.[[\<phi> x]]) \<Longrightarrow> [[\<^bold>\<forall> x. \<phi> x]]"
    by axiom_meta_solver
  lemma closures_actualization[axiom]: "[[\<phi>]] \<Longrightarrow> [[\<^bold>\<A> \<phi>]]"
    by axiom_meta_solver
  lemma closures_necessitation[axiom]: "[[\<phi>]] \<Longrightarrow> [[\<^bold>\<box> \<phi>]]"
    by axiom_meta_solver
  lemma necessitation_averse_axiom_instance[axiom]: "[\<phi>] \<Longrightarrow> [\<phi> in dw]"
    by axiom_meta_solver
  lemma necessitation_averse_closures_universal[axiom]: "(\<And>x.[\<phi> x]) \<Longrightarrow> [\<^bold>\<forall> x. \<phi> x]"
    by axiom_meta_solver

  attribute_setup axiom_instance = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm axiom_instance}))
\<close>

  attribute_setup necessitation_averse_axiom_instance = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm necessitation_averse_axiom_instance}))
\<close>

  attribute_setup axiom_necessitation = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm closures_necessitation}))
\<close>

  attribute_setup axiom_actualization = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm closures_actualization}))
\<close>

  attribute_setup axiom_universal = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm closures_universal}))
\<close>

subsection\<open>Axioms for Negations and Conditionals\<close>
text\<open>\label{TAO_Axioms_NegationsAndConditionals}\<close>

  lemma pl_1[axiom]:
    "[[\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<phi>)]]"
    by axiom_meta_solver
  lemma pl_2[axiom]:
    "[[(\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>))]]"
    by axiom_meta_solver
  lemma pl_3[axiom]:
    "[[(\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<phi>)]]"
    by axiom_meta_solver

subsection\<open>Axioms of Identity\<close>
text\<open>\label{TAO_Axioms_Identity}\<close>

  lemma l_identity[axiom]:
    "[[\<alpha> \<^bold>= \<beta> \<^bold>\<rightarrow> (\<phi> \<alpha> \<^bold>\<rightarrow> \<phi> \<beta>)]]"
    using l_identity apply - by axiom_meta_solver

subsection\<open>Axioms of Quantification\<close>
text\<open>\label{TAO_Axioms_Quantification}\<close>

  lemma cqt_1[axiom]:
    "[[(\<^bold>\<forall> \<alpha>. \<phi> \<alpha>) \<^bold>\<rightarrow> \<phi> \<alpha>]]"
    by axiom_meta_solver
  lemma cqt_1_\<kappa>[axiom]:
    "[[(\<^bold>\<forall> \<alpha>. \<phi> (\<alpha>\<^sup>P)) \<^bold>\<rightarrow> ((\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<alpha>) \<^bold>\<rightarrow> \<phi> \<alpha>)]]"
    proof -
      {
        fix v
        assume 1: "[(\<^bold>\<forall> \<alpha>. \<phi> (\<alpha>\<^sup>P)) in v]"
        assume "[(\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<alpha>) in v]"
        then obtain \<beta> where 2:
          "[(\<beta>\<^sup>P) \<^bold>= \<alpha> in v]" by (rule ExERule)
        hence "[\<phi> (\<beta>\<^sup>P) in v]" using 1 AllE by fast
        hence "[\<phi> \<alpha> in v]"
          using l_identity[where \<phi>=\<phi>, axiom_instance]
          ImplS 2 by simp
      }
      thus "[[(\<^bold>\<forall> \<alpha>. \<phi> (\<alpha>\<^sup>P)) \<^bold>\<rightarrow> ((\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<alpha>) \<^bold>\<rightarrow> \<phi> \<alpha>)]]"
        unfolding axiom_def using ImplI by blast
    qed
  lemma cqt_3[axiom]:
    "[[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<psi> \<alpha>))]]"
    by axiom_meta_solver
  lemma cqt_4[axiom]:
    "[[\<phi> \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<phi>)]]"
    by axiom_meta_solver

  inductive SimpleExOrEnc
    where "SimpleExOrEnc (\<lambda> x . \<lparr>F,x\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,x,y\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,y,x\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,x,y,z\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,y,x,z\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lparr>F,y,z,x\<rparr>)"
        | "SimpleExOrEnc (\<lambda> x . \<lbrace>x,F\<rbrace>)"

  lemma cqt_5[axiom]:
    assumes "SimpleExOrEnc \<psi>"
    shows "[[(\<psi> (\<^bold>\<iota>x . \<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<exists> \<alpha>. (\<alpha>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<phi> x))]]"
    proof -
      have "\<forall> w . ([(\<psi> (\<^bold>\<iota>x . \<phi> x)) in w] \<longrightarrow> (\<exists> o\<^sub>1 . Some o\<^sub>1 = d\<^sub>\<kappa> (\<^bold>\<iota>x . \<phi> x)))"
        using assms apply induct by (meta_solver;metis)+
     thus ?thesis
      apply - unfolding identity_\<kappa>_def
      apply axiom_meta_solver
      using d\<^sub>\<kappa>_proper by auto
    qed

  lemma cqt_5_mod[axiom]:
    assumes "SimpleExOrEnc \<psi>"
    shows "[[\<psi> \<tau> \<^bold>\<rightarrow> (\<^bold>\<exists> \<alpha> . (\<alpha>\<^sup>P) \<^bold>= \<tau>)]]"
    proof -
      have "\<forall> w . ([(\<psi> \<tau>) in w] \<longrightarrow> (\<exists> o\<^sub>1 . Some o\<^sub>1 = d\<^sub>\<kappa> \<tau>))"
        using assms apply induct by (meta_solver;metis)+
      thus ?thesis
        apply - unfolding identity_\<kappa>_def
        apply axiom_meta_solver
        using d\<^sub>\<kappa>_proper by auto
    qed

subsection\<open>Axioms of Actuality\<close>
text\<open>\label{TAO_Axioms_Actuality}\<close>

  lemma logic_actual[axiom]: "[(\<^bold>\<A>\<phi>) \<^bold>\<equiv> \<phi>]"
    by axiom_meta_solver
  lemma "[[(\<^bold>\<A>\<phi>) \<^bold>\<equiv> \<phi>]]"
    nitpick[user_axioms, expect = genuine, card = 1, card i = 2]
    oops \<comment> \<open>Counter-model by nitpick\<close>

  lemma logic_actual_nec_1[axiom]:
    "[[\<^bold>\<A>\<^bold>\<not>\<phi> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>\<phi>]]"
    by axiom_meta_solver
  lemma logic_actual_nec_2[axiom]:
    "[[(\<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>\<equiv> (\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<psi>)]]"
    by axiom_meta_solver
  lemma logic_actual_nec_3[axiom]:
    "[[\<^bold>\<A>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall>\<alpha>. \<^bold>\<A>(\<phi> \<alpha>))]]"
    by axiom_meta_solver
  lemma logic_actual_nec_4[axiom]:
    "[[\<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<^bold>\<A>\<phi>]]"
    by axiom_meta_solver

subsection\<open>Axioms of Necessity\<close>
text\<open>\label{TAO_Axioms_Necessity}\<close>

  lemma qml_1[axiom]:
    "[[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)]]"
    by axiom_meta_solver
  lemma qml_2[axiom]:
    "[[\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi>]]"
    by axiom_meta_solver
  lemma qml_3[axiom]:
    "[[\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi>]]"
    by axiom_meta_solver
  lemma qml_4[axiom]:
    "[[\<^bold>\<diamond>(\<^bold>\<exists>x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<exists>x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>)]]"
     unfolding axiom_def
     using PossiblyContingentObjectExistsAxiom
           PossiblyNoContingentObjectExistsAxiom
     apply (simp add: meta_defs meta_aux conn_defs forall_\<nu>_def
                 split: \<nu>.split \<upsilon>.split)
     by (metis \<nu>\<upsilon>_\<omega>\<nu>_is_\<omega>\<upsilon> \<upsilon>.distinct(1) \<upsilon>.inject(1))

subsection\<open>Axioms of Necessity and Actuality\<close>
text\<open>\label{TAO_Axioms_NecessityAndActuality}\<close>

  lemma qml_act_1[axiom]:
    "[[\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi>]]"
    by axiom_meta_solver
  lemma qml_act_2[axiom]:
    "[[\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<box>\<phi>)]]"
    by axiom_meta_solver

subsection\<open>Axioms of Descriptions\<close>
text\<open>\label{TAO_Axioms_Descriptions}\<close>

  lemma descriptions[axiom]:
    "[[x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) \<^bold>\<equiv> (\<^bold>\<forall>z.(\<^bold>\<A>(\<phi> z) \<^bold>\<equiv> z \<^bold>= x))]]"
    unfolding axiom_def
    proof (rule allI, rule EquivI; rule)
      fix v
      assume "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
      moreover hence 1:
        "\<exists>o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> (x\<^sup>P) \<and> Some o\<^sub>2 = d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x) \<and> o\<^sub>1 = o\<^sub>2"
        apply - unfolding identity_\<kappa>_def by meta_solver
      then obtain o\<^sub>1 o\<^sub>2 where 2:
        "Some o\<^sub>1 = d\<^sub>\<kappa> (x\<^sup>P) \<and> Some o\<^sub>2 = d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x) \<and> o\<^sub>1 = o\<^sub>2"
        by auto
      hence 3:
        "(\<exists> x .((w\<^sub>0 \<Turnstile> \<phi> x) \<and> (\<forall>y. (w\<^sub>0 \<Turnstile> \<phi> y) \<longrightarrow> y = x)))
         \<and> d\<^sub>\<kappa> (\<^bold>\<iota>x. \<phi> x) = Some (THE x. (w\<^sub>0 \<Turnstile> \<phi> x))"
        using D3 by (metis option.distinct(1))
      then obtain X where 4:
        "((w\<^sub>0 \<Turnstile> \<phi> X) \<and> (\<forall>y. (w\<^sub>0 \<Turnstile> \<phi> y) \<longrightarrow> y = X))"
        by auto
      moreover have "o\<^sub>1 = (THE x. (w\<^sub>0 \<Turnstile> \<phi> x))"
        using 2 3 by auto
      ultimately have 5: "X = o\<^sub>1"
        by (metis (mono_tags) theI)
      have "\<forall> z . [\<^bold>\<A>\<phi> z in v] = [(z\<^sup>P) \<^bold>= (x\<^sup>P) in v]"
      proof
        fix z
        have "[\<^bold>\<A>\<phi> z in v] \<Longrightarrow> [(z\<^sup>P) \<^bold>= (x\<^sup>P) in v]"
          unfolding identity_\<kappa>_def apply meta_solver
          using 4 5 2 d\<^sub>\<kappa>_proper w\<^sub>0_def by auto
        moreover have "[(z\<^sup>P) \<^bold>= (x\<^sup>P) in v] \<Longrightarrow> [\<^bold>\<A>\<phi> z in v]"
          unfolding identity_\<kappa>_def apply meta_solver
          using 2 4 5 
          by (simp add: d\<^sub>\<kappa>_proper w\<^sub>0_def)
        ultimately show "[\<^bold>\<A>\<phi> z in v] = [(z\<^sup>P) \<^bold>= (x\<^sup>P) in v]"
          by auto
      qed
      thus "[\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> (z) \<^bold>= (x) in v]"
        unfolding identity_\<nu>_def
        by (simp add: AllI EquivS)
    next
      fix v
      assume "[\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> (z) \<^bold>= (x) in v]"
      hence "\<And>z. (dw \<Turnstile> \<phi> z) = (\<exists>o\<^sub>1 o\<^sub>2. Some o\<^sub>1 = d\<^sub>\<kappa> (z\<^sup>P)
                \<and> Some o\<^sub>2 = d\<^sub>\<kappa> (x\<^sup>P) \<and> o\<^sub>1 = o\<^sub>2)"
        apply - unfolding identity_\<nu>_def identity_\<kappa>_def by meta_solver
      hence "\<forall> z . (dw \<Turnstile> \<phi> z) = (z = x)"
        by (simp add: d\<^sub>\<kappa>_proper)
      moreover hence "x = (THE z . (dw \<Turnstile> \<phi> z))" by simp
      ultimately have "x\<^sup>P = (\<^bold>\<iota>x. \<phi> x)"
        using D3 d\<^sub>\<kappa>_inject d\<^sub>\<kappa>_proper w\<^sub>0_def by presburger
      thus "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
        using Eq\<kappa>S unfolding identity_\<kappa>_def by (metis d\<^sub>\<kappa>_proper)
    qed

subsection\<open>Axioms for Complex Relation Terms\<close>
text\<open>\label{TAO_Axioms_ComplexRelationTerms}\<close>

  lemma lambda_predicates_1[axiom]:
    "(\<^bold>\<lambda> x . \<phi> x) = (\<^bold>\<lambda> y . \<phi> y)" ..

  lemma lambda_predicates_2_1[axiom]:
    assumes "IsProperInX \<phi>"
    shows "[[\<lparr>\<^bold>\<lambda> x . \<phi> (x\<^sup>P), x\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P)]]"
    apply axiom_meta_solver
    using D5_1[OF assms] d\<^sub>\<kappa>_proper propex\<^sub>1
    by metis

  lemma lambda_predicates_2_2[axiom]:
    assumes "IsProperInXY \<phi>"
    shows "[[\<lparr>(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<phi> (x\<^sup>P) (y\<^sup>P))), x\<^sup>P, y\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) (y\<^sup>P)]]"
    apply axiom_meta_solver
    using D5_2[OF assms] d\<^sub>\<kappa>_proper propex\<^sub>2
    by metis

  lemma lambda_predicates_2_3[axiom]:
    assumes "IsProperInXYZ \<phi>"
    shows "[[\<lparr>(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P))),x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)]]"
    proof -
      have "[[\<lparr>(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P))),x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr> \<^bold>\<rightarrow> \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)]]"
        apply axiom_meta_solver using D5_3[OF assms] by auto
      moreover have
        "[[\<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) \<^bold>\<rightarrow> \<lparr>(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P))),x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>]]"
        apply axiom_meta_solver
        using D5_3[OF assms] d\<^sub>\<kappa>_proper propex\<^sub>3
        by (metis (no_types, lifting))
      ultimately show ?thesis unfolding axiom_def equiv_def ConjS by blast
    qed

  lemma lambda_predicates_3_0[axiom]:
    "[[(\<^bold>\<lambda>\<^sup>0 \<phi>) \<^bold>= \<phi>]]"
    unfolding identity_defs
    apply axiom_meta_solver
    by (simp add: meta_defs meta_aux)

  lemma lambda_predicates_3_1[axiom]:
    "[[(\<^bold>\<lambda> x . \<lparr>F, x\<^sup>P\<rparr>) \<^bold>= F]]"
    unfolding axiom_def
    apply (rule allI)
    unfolding identity_\<Pi>\<^sub>1_def apply (rule Eq\<^sub>1I)
    using D4_1 d\<^sub>1_inject by simp

  lemma lambda_predicates_3_2[axiom]:
    "[[(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<lparr>F, x\<^sup>P, y\<^sup>P\<rparr>)) \<^bold>= F]]"
    unfolding axiom_def
    apply (rule allI)
    unfolding identity_\<Pi>\<^sub>2_def apply (rule Eq\<^sub>2I)
    using D4_2 d\<^sub>2_inject by simp

  lemma lambda_predicates_3_3[axiom]:
    "[[(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<lparr>F, x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>)) \<^bold>= F]]"
    unfolding axiom_def
    apply (rule allI)
    unfolding identity_\<Pi>\<^sub>3_def apply (rule Eq\<^sub>3I)
    using D4_3 d\<^sub>3_inject by simp

  lemma lambda_predicates_4_0[axiom]:
    assumes "\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]"
    shows "[[(\<^bold>\<lambda>\<^sup>0 (\<chi> (\<^bold>\<iota>x. \<phi> x)) \<^bold>= \<^bold>\<lambda>\<^sup>0 (\<chi> (\<^bold>\<iota>x. \<psi> x)))]]"
    unfolding axiom_def identity_\<o>_def apply - apply (rule allI; rule Eq\<^sub>0I)
    using TheEqI[OF assms[THEN ActualE, THEN EquivE]] by auto

  lemma lambda_predicates_4_1[axiom]:
    assumes "\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]"
    shows "[[((\<^bold>\<lambda> x . \<chi> (\<^bold>\<iota>x. \<phi> x) x) \<^bold>= (\<^bold>\<lambda> x . \<chi> (\<^bold>\<iota>x. \<psi> x) x))]]"
    unfolding axiom_def identity_\<Pi>\<^sub>1_def apply - apply (rule allI; rule Eq\<^sub>1I)
    using TheEqI[OF assms[THEN ActualE, THEN EquivE]] by auto

  lemma lambda_predicates_4_2[axiom]:
    assumes "\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]"
    shows "[[((\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<chi> (\<^bold>\<iota>x. \<phi> x) x y)) \<^bold>= (\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<chi> (\<^bold>\<iota>x. \<psi> x) x y)))]]"
    unfolding axiom_def identity_\<Pi>\<^sub>2_def apply - apply (rule allI; rule Eq\<^sub>2I)
    using TheEqI[OF assms[THEN ActualE, THEN EquivE]] by auto

  lemma lambda_predicates_4_3[axiom]:
    assumes "\<And>x.[(\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x)) in v]"
    shows "[[(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<chi> (\<^bold>\<iota>x. \<phi> x) x y z)) \<^bold>= (\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<chi> (\<^bold>\<iota>x. \<psi> x) x y z))]]"
    unfolding axiom_def identity_\<Pi>\<^sub>3_def apply - apply (rule allI; rule Eq\<^sub>3I)
    using TheEqI[OF assms[THEN ActualE, THEN EquivE]] by auto

subsection\<open>Axioms of Encoding\<close>
text\<open>\label{TAO_Axioms_Encoding}\<close>

  lemma encoding[axiom]:
    "[[\<lbrace>x,F\<rbrace> \<^bold>\<rightarrow> \<^bold>\<box>\<lbrace>x,F\<rbrace>]]"
    by axiom_meta_solver
  lemma nocoder[axiom]:
    "[[\<lparr>O!,x\<rparr> \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x,F\<rbrace>)]]"
    unfolding axiom_def
    apply (rule allI, rule ImplI, subst (asm) OrdS)
    apply meta_solver unfolding en_def
    by (metis \<nu>.simps(5) mem_Collect_eq option.sel)
  lemma A_objects[axiom]:
    "[[\<^bold>\<exists>x. \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . (\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F))]]"
    unfolding axiom_def
    proof (rule allI, rule ExIRule)
      fix v
      let ?x = "\<alpha>\<nu> { F . [\<phi> F in v]}"
      have "[\<lparr>A!,?x\<^sup>P\<rparr> in v]" by (simp add: AbsS d\<^sub>\<kappa>_proper)
      moreover have "[(\<^bold>\<forall>F. \<lbrace>?x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
        apply meta_solver unfolding en_def
        using d\<^sub>1.rep_eq d\<^sub>\<kappa>_def d\<^sub>\<kappa>_proper eval\<Pi>\<^sub>1_inverse by auto
      ultimately show "[\<lparr>A!,?x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>?x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
        by (simp only: ConjS)
    qed

end

(*<*)
end
(*>*)
