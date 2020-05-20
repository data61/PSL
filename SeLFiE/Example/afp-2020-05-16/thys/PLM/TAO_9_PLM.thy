(*<*)
theory TAO_9_PLM
imports 
  TAO_8_Definitions 
  "HOL-Eisbach.Eisbach_Tools"
begin
(*>*)

section\<open>The Deductive System PLM\<close>
text\<open>\label{TAO_PLM}\<close>

declare meta_defs[no_atp] meta_aux[no_atp]

locale PLM = Axioms
begin

subsection\<open>Automatic Solver\<close>
text\<open>\label{TAO_PLM_Solver}\<close>

  named_theorems PLM
  named_theorems PLM_intro
  named_theorems PLM_elim
  named_theorems PLM_dest
  named_theorems PLM_subst

  method PLM_solver declares PLM_intro PLM_elim PLM_subst PLM_dest PLM
    = ((assumption | (match axiom in A: "[[\<phi>]]" for \<phi> \<Rightarrow> \<open>fact A[axiom_instance]\<close>)
        | fact PLM | rule PLM_intro | subst PLM_subst | subst (asm) PLM_subst
        | fastforce | safe | drule PLM_dest | erule PLM_elim); (PLM_solver)?)

subsection\<open>Modus Ponens\<close>
text\<open>\label{TAO_PLM_ModusPonens}\<close>

  lemma modus_ponens[PLM]:
    "\<lbrakk>[\<phi> in v]; [\<phi> \<^bold>\<rightarrow> \<psi> in v]\<rbrakk> \<Longrightarrow> [\<psi> in v]"
    by (simp add: Semantics.T5)

subsection\<open>Axioms\<close>
text\<open>\label{TAO_PLM_Axioms}\<close>

  interpretation Axioms .
  declare axiom[PLM]
  declare conn_defs[PLM]

subsection\<open>(Modally Strict) Proofs and Derivations\<close>
text\<open>\label{TAO_PLM_ProofsAndDerivations}\<close>

  lemma vdash_properties_6[no_atp]:
    "\<lbrakk>[\<phi> in v]; [\<phi> \<^bold>\<rightarrow> \<psi> in v]\<rbrakk> \<Longrightarrow> [\<psi> in v]"
    using modus_ponens .
  lemma vdash_properties_9[PLM]:
    "[\<phi> in v] \<Longrightarrow> [\<psi> \<^bold>\<rightarrow> \<phi> in v]"
    using modus_ponens pl_1[axiom_instance] by blast
  lemma vdash_properties_10[PLM]:
    "[\<phi> \<^bold>\<rightarrow> \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<Longrightarrow> [\<psi> in v])"
    using vdash_properties_6 .

  attribute_setup deduction = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm vdash_properties_10}))
\<close>

subsection\<open>GEN and RN\<close>
text\<open>\label{TAO_PLM_GEN_RN}\<close>

  lemma rule_gen[PLM]:
    "\<lbrakk>\<And>\<alpha> . [\<phi> \<alpha> in v]\<rbrakk> \<Longrightarrow> [\<^bold>\<forall>\<alpha> . \<phi> \<alpha> in v]"
    by (simp add: Semantics.T8)

  lemma RN_2[PLM]:
    "(\<And> v . [\<psi> in v] \<Longrightarrow> [\<phi> in v]) \<Longrightarrow> ([\<^bold>\<box>\<psi> in v] \<Longrightarrow> [\<^bold>\<box>\<phi> in v])"
    by (simp add: Semantics.T6)

  lemma RN[PLM]:
    "(\<And> v . [\<phi> in v]) \<Longrightarrow> [\<^bold>\<box>\<phi> in v]"
    using qml_3[axiom_necessitation, axiom_instance] RN_2 by blast

subsection\<open>Negations and Conditionals\<close>
text\<open>\label{TAO_PLM_NegationsAndConditionals}\<close>

  lemma if_p_then_p[PLM]:
    "[\<phi> \<^bold>\<rightarrow> \<phi> in v]"
    using pl_1 pl_2 vdash_properties_10 axiom_instance by blast

  lemma deduction_theorem[PLM,PLM_intro]:
    "\<lbrakk>[\<phi> in v] \<Longrightarrow> [\<psi> in v]\<rbrakk> \<Longrightarrow> [\<phi> \<^bold>\<rightarrow> \<psi> in v]"
    by (simp add: Semantics.T5)
  lemmas CP = deduction_theorem

  lemma ded_thm_cor_3[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<rightarrow> \<psi> in v]; [\<psi> \<^bold>\<rightarrow> \<chi> in v]\<rbrakk> \<Longrightarrow> [\<phi> \<^bold>\<rightarrow> \<chi> in v]"
    by (meson pl_2 vdash_properties_10 vdash_properties_9 axiom_instance)
  lemma ded_thm_cor_4[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>) in v]; [\<psi> in v]\<rbrakk> \<Longrightarrow> [\<phi> \<^bold>\<rightarrow> \<chi> in v]"
    by (meson pl_2 vdash_properties_10 vdash_properties_9 axiom_instance)

  lemma useful_tautologies_1[PLM]:
    "[\<^bold>\<not>\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<phi> in v]"
    by (meson pl_1 pl_3 ded_thm_cor_3 ded_thm_cor_4 axiom_instance)
  lemma useful_tautologies_2[PLM]:
    "[\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<^bold>\<not>\<phi> in v]"
    by (meson pl_1 pl_3 ded_thm_cor_3 useful_tautologies_1
              vdash_properties_10 axiom_instance)
  lemma useful_tautologies_3[PLM]:
    "[\<^bold>\<not>\<phi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
    by (meson pl_1 pl_2 pl_3 ded_thm_cor_3 ded_thm_cor_4 axiom_instance)
  lemma useful_tautologies_4[PLM]:
    "[(\<^bold>\<not>\<psi> \<^bold>\<rightarrow> \<^bold>\<not>\<phi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
    by (meson pl_1 pl_2 pl_3 ded_thm_cor_3 ded_thm_cor_4 axiom_instance)
  lemma useful_tautologies_5[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<not>\<psi> \<^bold>\<rightarrow> \<^bold>\<not>\<phi>) in v]"
    by (metis CP useful_tautologies_4 vdash_properties_10)
  lemma useful_tautologies_6[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<^bold>\<not>\<phi>) in v]"
    by (metis CP useful_tautologies_4 vdash_properties_10)
  lemma useful_tautologies_7[PLM]:
    "[(\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<not>\<psi> \<^bold>\<rightarrow> \<phi>) in v]"
    using ded_thm_cor_3 useful_tautologies_4 useful_tautologies_5
          useful_tautologies_6 by blast
  lemma useful_tautologies_8[PLM]:
    "[\<phi> \<^bold>\<rightarrow> (\<^bold>\<not>\<psi> \<^bold>\<rightarrow> \<^bold>\<not>(\<phi> \<^bold>\<rightarrow> \<psi>)) in v]"
    by (meson ded_thm_cor_3 CP useful_tautologies_5)
  lemma useful_tautologies_9[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<psi>) in v]"
    by (metis CP useful_tautologies_4 vdash_properties_10)
  lemma useful_tautologies_10[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi>) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> \<^bold>\<not>\<phi>) in v]"
    by (metis ded_thm_cor_3 CP useful_tautologies_6)

  lemma modus_tollens_1[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<rightarrow> \<psi> in v]; [\<^bold>\<not>\<psi> in v]\<rbrakk> \<Longrightarrow> [\<^bold>\<not>\<phi> in v]"
    by (metis ded_thm_cor_3 ded_thm_cor_4 useful_tautologies_3
              useful_tautologies_7 vdash_properties_10)
  lemma modus_tollens_2[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi> in v]; [\<psi> in v]\<rbrakk> \<Longrightarrow> [\<^bold>\<not>\<phi> in v]"
    using modus_tollens_1 useful_tautologies_2
          vdash_properties_10 by blast

  lemma contraposition_1[PLM]:
    "[\<phi> \<^bold>\<rightarrow> \<psi> in v] = [\<^bold>\<not>\<psi> \<^bold>\<rightarrow> \<^bold>\<not>\<phi> in v]"
    using useful_tautologies_4 useful_tautologies_5
          vdash_properties_10 by blast
  lemma contraposition_2[PLM]:
    "[\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi> in v] = [\<psi> \<^bold>\<rightarrow> \<^bold>\<not>\<phi> in v]"
    using contraposition_1 ded_thm_cor_3
          useful_tautologies_1 by blast

  lemma reductio_aa_1[PLM]:
    "\<lbrakk>[\<^bold>\<not>\<phi> in v] \<Longrightarrow> [\<^bold>\<not>\<psi> in v]; [\<^bold>\<not>\<phi> in v] \<Longrightarrow> [\<psi> in v]\<rbrakk> \<Longrightarrow> [\<phi> in v]"
    using CP modus_tollens_2 useful_tautologies_1
          vdash_properties_10 by blast
  lemma reductio_aa_2[PLM]:
    "\<lbrakk>[\<phi> in v] \<Longrightarrow> [\<^bold>\<not>\<psi> in v]; [\<phi> in v] \<Longrightarrow> [\<psi> in v]\<rbrakk> \<Longrightarrow> [\<^bold>\<not>\<phi> in v]"
    by (meson contraposition_1 reductio_aa_1)
  lemma reductio_aa_3[PLM]:
    "\<lbrakk>[\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi> in v]; [\<^bold>\<not>\<phi> \<^bold>\<rightarrow> \<psi> in v]\<rbrakk> \<Longrightarrow> [\<phi> in v]"
    using reductio_aa_1 vdash_properties_10 by blast
  lemma reductio_aa_4[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<rightarrow> \<^bold>\<not>\<psi> in v]; [\<phi> \<^bold>\<rightarrow> \<psi> in v]\<rbrakk> \<Longrightarrow> [\<^bold>\<not>\<phi> in v]"
    using reductio_aa_2 vdash_properties_10 by blast

  lemma raa_cor_1[PLM]:
    "\<lbrakk>[\<phi> in v]; [\<^bold>\<not>\<psi> in v] \<Longrightarrow> [\<^bold>\<not>\<phi> in v]\<rbrakk> \<Longrightarrow> ([\<phi> in v] \<Longrightarrow> [\<psi> in v])"
    using reductio_aa_1 vdash_properties_9 by blast
  lemma raa_cor_2[PLM]:
    "\<lbrakk>[\<^bold>\<not>\<phi> in v]; [\<^bold>\<not>\<psi> in v] \<Longrightarrow> [\<phi> in v]\<rbrakk> \<Longrightarrow> ([\<^bold>\<not>\<phi> in v] \<Longrightarrow> [\<psi> in v])"
    using reductio_aa_1 vdash_properties_9 by blast
  lemma raa_cor_3[PLM]:
    "\<lbrakk>[\<phi> in v]; [\<^bold>\<not>\<psi> \<^bold>\<rightarrow> \<^bold>\<not>\<phi> in v]\<rbrakk> \<Longrightarrow> ([\<phi> in v] \<Longrightarrow> [\<psi> in v])"
    using raa_cor_1 vdash_properties_10 by blast
  lemma raa_cor_4[PLM]:
    "\<lbrakk>[\<^bold>\<not>\<phi> in v]; [\<^bold>\<not>\<psi> \<^bold>\<rightarrow> \<phi> in v]\<rbrakk> \<Longrightarrow> ([\<^bold>\<not>\<phi> in v] \<Longrightarrow> [\<psi> in v])"
    using raa_cor_2 vdash_properties_10 by blast

text\<open>
\begin{remark}
  In contrast to PLM the classical introduction and elimination rules are proven
  before the tautologies. The statements proven so far are sufficient
  for the proofs and using the derived rules the tautologies can be derived
  automatically.
\end{remark}
\<close>

  lemma intro_elim_1[PLM]:
    "\<lbrakk>[\<phi> in v]; [\<psi> in v]\<rbrakk> \<Longrightarrow> [\<phi> \<^bold>& \<psi> in v]"
    unfolding conj_def using ded_thm_cor_4 if_p_then_p modus_tollens_2 by blast
  lemmas "\<^bold>&I" = intro_elim_1
  lemma intro_elim_2_a[PLM]:
    "[\<phi> \<^bold>& \<psi> in v] \<Longrightarrow> [\<phi> in v]"
    unfolding conj_def using CP reductio_aa_1 by blast
  lemma intro_elim_2_b[PLM]:
    "[\<phi> \<^bold>& \<psi> in v] \<Longrightarrow> [\<psi> in v]"
    unfolding conj_def using pl_1 CP reductio_aa_1 axiom_instance by blast
  lemmas "\<^bold>&E" = intro_elim_2_a intro_elim_2_b
  lemma intro_elim_3_a[PLM]:
    "[\<phi> in v] \<Longrightarrow> [\<phi> \<^bold>\<or> \<psi> in v]"
    unfolding disj_def using ded_thm_cor_4 useful_tautologies_3 by blast
  lemma intro_elim_3_b[PLM]:
    "[\<psi> in v] \<Longrightarrow> [\<phi> \<^bold>\<or> \<psi> in v]"
    by (simp only: disj_def vdash_properties_9)
  lemmas "\<^bold>\<or>I" = intro_elim_3_a intro_elim_3_b
  lemma intro_elim_4_a[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<or> \<psi> in v]; [\<phi> \<^bold>\<rightarrow> \<chi> in v]; [\<psi> \<^bold>\<rightarrow> \<chi> in v]\<rbrakk> \<Longrightarrow> [\<chi> in v]"
    unfolding disj_def by (meson reductio_aa_2 vdash_properties_10)
  lemma intro_elim_4_b[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<or> \<psi> in v]; [\<^bold>\<not>\<phi> in v]\<rbrakk> \<Longrightarrow> [\<psi> in v]"
    unfolding disj_def using vdash_properties_10 by blast
  lemma intro_elim_4_c[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<or> \<psi> in v]; [\<^bold>\<not>\<psi> in v]\<rbrakk> \<Longrightarrow> [\<phi> in v]"
    unfolding disj_def using raa_cor_2 vdash_properties_10 by blast
  lemma intro_elim_4_d[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<or> \<psi> in v]; [\<phi> \<^bold>\<rightarrow> \<chi> in v]; [\<psi> \<^bold>\<rightarrow> \<Theta> in v]\<rbrakk> \<Longrightarrow> [\<chi> \<^bold>\<or> \<Theta> in v]"
    unfolding disj_def using contraposition_1 ded_thm_cor_3 by blast
  lemma intro_elim_4_e[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<or> \<psi> in v]; [\<phi> \<^bold>\<equiv> \<chi> in v]; [\<psi> \<^bold>\<equiv> \<Theta> in v]\<rbrakk> \<Longrightarrow> [\<chi> \<^bold>\<or> \<Theta> in v]"
    unfolding equiv_def using "\<^bold>&E"(1) intro_elim_4_d by blast
  lemmas "\<^bold>\<or>E" = intro_elim_4_a intro_elim_4_b intro_elim_4_c intro_elim_4_d
  lemma intro_elim_5[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<rightarrow> \<psi> in v]; [\<psi> \<^bold>\<rightarrow> \<phi> in v]\<rbrakk> \<Longrightarrow> [\<phi> \<^bold>\<equiv> \<psi> in v]"
    by (simp only: equiv_def "\<^bold>&I")
  lemmas "\<^bold>\<equiv>I" = intro_elim_5
  lemma intro_elim_6_a[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<equiv> \<psi> in v]; [\<phi> in v]\<rbrakk> \<Longrightarrow> [\<psi> in v]"
    unfolding equiv_def using "\<^bold>&E"(1) vdash_properties_10 by blast
  lemma intro_elim_6_b[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<equiv> \<psi> in v]; [\<psi> in v]\<rbrakk> \<Longrightarrow> [\<phi> in v]"
    unfolding equiv_def using "\<^bold>&E"(2) vdash_properties_10 by blast
  lemma intro_elim_6_c[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<equiv> \<psi> in v]; [\<^bold>\<not>\<phi> in v]\<rbrakk> \<Longrightarrow> [\<^bold>\<not>\<psi> in v]"
    unfolding equiv_def using "\<^bold>&E"(2) modus_tollens_1 by blast
  lemma intro_elim_6_d[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<equiv> \<psi> in v]; [\<^bold>\<not>\<psi> in v]\<rbrakk> \<Longrightarrow> [\<^bold>\<not>\<phi> in v]"
    unfolding equiv_def using "\<^bold>&E"(1) modus_tollens_1 by blast
  lemma intro_elim_6_e[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<equiv> \<psi> in v]; [\<psi> \<^bold>\<equiv> \<chi> in v]\<rbrakk> \<Longrightarrow> [\<phi> \<^bold>\<equiv> \<chi> in v]"
    by (metis equiv_def ded_thm_cor_3 "\<^bold>&E" "\<^bold>\<equiv>I")
  lemma intro_elim_6_f[PLM]:
    "\<lbrakk>[\<phi> \<^bold>\<equiv> \<psi> in v]; [\<phi> \<^bold>\<equiv> \<chi> in v]\<rbrakk> \<Longrightarrow> [\<chi> \<^bold>\<equiv> \<psi> in v]"
    by (metis equiv_def ded_thm_cor_3 "\<^bold>&E" "\<^bold>\<equiv>I")
  lemmas "\<^bold>\<equiv>E" = intro_elim_6_a intro_elim_6_b intro_elim_6_c
                intro_elim_6_d intro_elim_6_e intro_elim_6_f
  lemma intro_elim_7[PLM]:
    "[\<phi> in v] \<Longrightarrow> [\<^bold>\<not>\<^bold>\<not>\<phi> in v]"
    using if_p_then_p modus_tollens_2 by blast
  lemmas "\<^bold>\<not>\<^bold>\<not>I" = intro_elim_7
  lemma intro_elim_8[PLM]:
    "[\<^bold>\<not>\<^bold>\<not>\<phi> in v] \<Longrightarrow> [\<phi> in v]"
    using if_p_then_p raa_cor_2 by blast
  lemmas "\<^bold>\<not>\<^bold>\<not>E" = intro_elim_8

  context
  begin
    private lemma NotNotI[PLM_intro]:
      "[\<phi> in v] \<Longrightarrow> [\<^bold>\<not>(\<^bold>\<not>\<phi>) in v]"
      by (simp add: "\<^bold>\<not>\<^bold>\<not>I")
    private lemma NotNotD[PLM_dest]:
      "[\<^bold>\<not>(\<^bold>\<not>\<phi>) in v] \<Longrightarrow> [\<phi> in v]"
      using "\<^bold>\<not>\<^bold>\<not>E" by blast

    private lemma ImplI[PLM_intro]:
      "([\<phi> in v] \<Longrightarrow> [\<psi> in v]) \<Longrightarrow> [\<phi> \<^bold>\<rightarrow> \<psi> in v]"
      using CP .
    private lemma ImplE[PLM_elim, PLM_dest]:
      "[\<phi> \<^bold>\<rightarrow> \<psi> in v] \<Longrightarrow> ([\<phi> in v] \<Longrightarrow> [\<psi> in v])"
      using modus_ponens .
    private lemma ImplS[PLM_subst]:
      "[\<phi> \<^bold>\<rightarrow> \<psi> in v] = ([\<phi> in v] \<longrightarrow> [\<psi> in v])"
      using ImplI ImplE by blast

    private lemma NotI[PLM_intro]:
      "([\<phi> in v] \<Longrightarrow> (\<And>\<psi> .[\<psi> in v])) \<Longrightarrow> [\<^bold>\<not>\<phi> in v]"
      using CP modus_tollens_2 by blast
    private lemma NotE[PLM_elim,PLM_dest]:
      "[\<^bold>\<not>\<phi> in v] \<Longrightarrow> ([\<phi> in v] \<longrightarrow> (\<forall>\<psi> .[\<psi> in v]))"
      using "\<^bold>\<or>I"(2) "\<^bold>\<or>E"(3) by blast
    private lemma NotS[PLM_subst]:
      "[\<^bold>\<not>\<phi> in v] = ([\<phi> in v] \<longrightarrow> (\<forall>\<psi> .[\<psi> in v]))"
      using NotI NotE by blast

    private lemma ConjI[PLM_intro]:
      "\<lbrakk>[\<phi> in v]; [\<psi> in v]\<rbrakk> \<Longrightarrow> [\<phi> \<^bold>& \<psi> in v]"
      using "\<^bold>&I" by blast
    private lemma ConjE[PLM_elim,PLM_dest]:
      "[\<phi> \<^bold>& \<psi> in v] \<Longrightarrow> (([\<phi> in v] \<and> [\<psi> in v]))"
      using CP "\<^bold>&E" by blast
    private lemma ConjS[PLM_subst]:
      "[\<phi> \<^bold>& \<psi> in v] = (([\<phi> in v] \<and> [\<psi> in v]))"
      using ConjI ConjE by blast

    private lemma DisjI[PLM_intro]:
      "[\<phi> in v] \<or> [\<psi> in v] \<Longrightarrow> [\<phi> \<^bold>\<or> \<psi> in v]"
      using "\<^bold>\<or>I" by blast
    private lemma DisjE[PLM_elim,PLM_dest]:
      "[\<phi> \<^bold>\<or> \<psi> in v] \<Longrightarrow> [\<phi> in v] \<or> [\<psi> in v]"
      using CP "\<^bold>\<or>E"(1) by blast
    private lemma DisjS[PLM_subst]:
      "[\<phi> \<^bold>\<or> \<psi> in v] = ([\<phi> in v] \<or> [\<psi> in v])"
      using DisjI DisjE by blast

    private lemma EquivI[PLM_intro]:
      "\<lbrakk>[\<phi> in v] \<Longrightarrow> [\<psi> in v];[\<psi> in v] \<Longrightarrow> [\<phi> in v]\<rbrakk> \<Longrightarrow> [\<phi> \<^bold>\<equiv> \<psi> in v]"
      using CP "\<^bold>\<equiv>I" by blast
    private lemma EquivE[PLM_elim,PLM_dest]:
      "[\<phi> \<^bold>\<equiv> \<psi> in v] \<Longrightarrow> (([\<phi> in v] \<longrightarrow> [\<psi> in v]) \<and> ([\<psi> in v] \<longrightarrow> [\<phi> in v]))"
      using "\<^bold>\<equiv>E"(1) "\<^bold>\<equiv>E"(2) by blast
    private lemma EquivS[PLM_subst]:
      "[\<phi> \<^bold>\<equiv> \<psi> in v] = ([\<phi> in v] \<longleftrightarrow> [\<psi> in v])"
      using EquivI EquivE by blast

    private lemma NotOrD[PLM_dest]:
      "\<not>[\<phi> \<^bold>\<or> \<psi> in v] \<Longrightarrow> \<not>[\<phi> in v] \<and> \<not>[\<psi> in v]"
      using "\<^bold>\<or>I" by blast
    private lemma NotAndD[PLM_dest]:
      "\<not>[\<phi> \<^bold>& \<psi> in v] \<Longrightarrow> \<not>[\<phi> in v] \<or> \<not>[\<psi> in v]"
      using "\<^bold>&I" by blast
    private lemma NotEquivD[PLM_dest]:
      "\<not>[\<phi> \<^bold>\<equiv> \<psi> in v] \<Longrightarrow> [\<phi> in v] \<noteq> [\<psi> in v]"
      by (meson NotI contraposition_1 "\<^bold>\<equiv>I" vdash_properties_9)

    private lemma BoxI[PLM_intro]:
      "(\<And> v . [\<phi> in v]) \<Longrightarrow> [\<^bold>\<box>\<phi> in v]"
      using RN by blast
    private lemma NotBoxD[PLM_dest]:
      "\<not>[\<^bold>\<box>\<phi> in v] \<Longrightarrow> (\<exists> v . \<not>[\<phi> in v])"
      using BoxI by blast

    private lemma AllI[PLM_intro]:
      "(\<And> x . [\<phi> x in v]) \<Longrightarrow> [\<^bold>\<forall> x . \<phi> x in v]"
      using rule_gen by blast
    lemma NotAllD[PLM_dest]:
      "\<not>[\<^bold>\<forall> x . \<phi> x in v] \<Longrightarrow> (\<exists> x . \<not>[\<phi> x in v])"
      using AllI by fastforce
  end

  lemma oth_class_taut_1_a[PLM]:
    "[\<^bold>\<not>(\<phi> \<^bold>& \<^bold>\<not>\<phi>) in v]"
    by PLM_solver
  lemma oth_class_taut_1_b[PLM]:
    "[\<^bold>\<not>(\<phi> \<^bold>\<equiv> \<^bold>\<not>\<phi>) in v]"
    by PLM_solver
  lemma oth_class_taut_2[PLM]:
    "[\<phi> \<^bold>\<or> \<^bold>\<not>\<phi> in v]"
    by PLM_solver
  lemma oth_class_taut_3_a[PLM]:
    "[(\<phi> \<^bold>& \<phi>) \<^bold>\<equiv> \<phi> in v]"
    by PLM_solver
  lemma oth_class_taut_3_b[PLM]:
    "[(\<phi> \<^bold>& \<psi>) \<^bold>\<equiv> (\<psi> \<^bold>& \<phi>) in v]"
    by PLM_solver
  lemma oth_class_taut_3_c[PLM]:
    "[(\<phi> \<^bold>& (\<psi> \<^bold>& \<chi>)) \<^bold>\<equiv> ((\<phi> \<^bold>& \<psi>) \<^bold>& \<chi>) in v]"
    by PLM_solver
  lemma oth_class_taut_3_d[PLM]:
    "[(\<phi> \<^bold>\<or> \<phi>) \<^bold>\<equiv> \<phi> in v]"
    by PLM_solver
  lemma oth_class_taut_3_e[PLM]:
    "[(\<phi> \<^bold>\<or> \<psi>) \<^bold>\<equiv> (\<psi> \<^bold>\<or> \<phi>) in v]"
    by PLM_solver
  lemma oth_class_taut_3_f[PLM]:
    "[(\<phi> \<^bold>\<or> (\<psi> \<^bold>\<or> \<chi>)) \<^bold>\<equiv> ((\<phi> \<^bold>\<or> \<psi>) \<^bold>\<or> \<chi>) in v]"
    by PLM_solver
  lemma oth_class_taut_3_g[PLM]:
    "[(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<equiv> (\<psi> \<^bold>\<equiv> \<phi>) in v]"
    by PLM_solver
  lemma oth_class_taut_3_i[PLM]:
    "[(\<phi> \<^bold>\<equiv> (\<psi> \<^bold>\<equiv> \<chi>)) \<^bold>\<equiv> ((\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<equiv> \<chi>) in v]"
    by PLM_solver
  lemma oth_class_taut_4_a[PLM]:
    "[\<phi> \<^bold>\<equiv> \<phi> in v]"
    by PLM_solver
  lemma oth_class_taut_4_b[PLM]:
    "[\<phi> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<not>\<phi> in v]"
    by PLM_solver
  lemma oth_class_taut_5_a[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<equiv> \<^bold>\<not>(\<phi> \<^bold>& \<^bold>\<not>\<psi>) in v]"
    by PLM_solver
  lemma oth_class_taut_5_b[PLM]:
    "[\<^bold>\<not>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<equiv> (\<phi> \<^bold>& \<^bold>\<not>\<psi>) in v]"
    by PLM_solver
  lemma oth_class_taut_5_c[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> ((\<psi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_5_d[PLM]:
    "[(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<equiv> (\<^bold>\<not>\<phi> \<^bold>\<equiv> \<^bold>\<not>\<psi>) in v]"
    by PLM_solver
  lemma oth_class_taut_5_e[PLM]:
    "[(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<equiv> (\<psi> \<^bold>\<rightarrow> \<chi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_5_f[PLM]:
    "[(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<rightarrow> ((\<chi> \<^bold>\<rightarrow> \<phi>) \<^bold>\<equiv> (\<chi> \<^bold>\<rightarrow> \<psi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_5_g[PLM]:
    "[(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<equiv> \<chi>) \<^bold>\<equiv> (\<psi> \<^bold>\<equiv> \<chi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_5_h[PLM]:
    "[(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<rightarrow> ((\<chi> \<^bold>\<equiv> \<phi>) \<^bold>\<equiv> (\<chi> \<^bold>\<equiv> \<psi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_5_i[PLM]:
    "[(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<equiv> ((\<phi> \<^bold>& \<psi>) \<^bold>\<or> (\<^bold>\<not>\<phi> \<^bold>& \<^bold>\<not>\<psi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_5_j[PLM]:
    "[(\<^bold>\<not>(\<phi> \<^bold>\<equiv> \<psi>)) \<^bold>\<equiv> ((\<phi> \<^bold>& \<^bold>\<not>\<psi>) \<^bold>\<or> (\<^bold>\<not>\<phi> \<^bold>& \<psi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_5_k[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<equiv> (\<^bold>\<not>\<phi> \<^bold>\<or> \<psi>) in v]"
    by PLM_solver

  lemma oth_class_taut_6_a[PLM]:
    "[(\<phi> \<^bold>& \<psi>) \<^bold>\<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>) in v]"
    by PLM_solver
  lemma oth_class_taut_6_b[PLM]:
    "[(\<phi> \<^bold>\<or> \<psi>) \<^bold>\<equiv> \<^bold>\<not>(\<^bold>\<not>\<phi> \<^bold>& \<^bold>\<not>\<psi>) in v]"
    by PLM_solver
  lemma oth_class_taut_6_c[PLM]:
    "[\<^bold>\<not>(\<phi> \<^bold>& \<psi>) \<^bold>\<equiv> (\<^bold>\<not>\<phi> \<^bold>\<or> \<^bold>\<not>\<psi>) in v]"
    by PLM_solver
  lemma oth_class_taut_6_d[PLM]:
    "[\<^bold>\<not>(\<phi> \<^bold>\<or> \<psi>) \<^bold>\<equiv> (\<^bold>\<not>\<phi> \<^bold>& \<^bold>\<not>\<psi>) in v]"
    by PLM_solver

  lemma oth_class_taut_7_a[PLM]:
    "[(\<phi> \<^bold>& (\<psi> \<^bold>\<or> \<chi>)) \<^bold>\<equiv> ((\<phi> \<^bold>& \<psi>) \<^bold>\<or> (\<phi> \<^bold>& \<chi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_7_b[PLM]:
    "[(\<phi> \<^bold>\<or> (\<psi> \<^bold>& \<chi>)) \<^bold>\<equiv> ((\<phi> \<^bold>\<or> \<psi>) \<^bold>& (\<phi> \<^bold>\<or> \<chi>)) in v]"
    by PLM_solver

  lemma oth_class_taut_8_a[PLM]:
    "[((\<phi> \<^bold>& \<psi>) \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_8_b[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<rightarrow> ((\<phi> \<^bold>& \<psi>) \<^bold>\<rightarrow> \<chi>) in v]"
    by PLM_solver

  lemma oth_class_taut_9_a[PLM]:
    "[(\<phi> \<^bold>& \<psi>) \<^bold>\<rightarrow> \<phi> in v]"
    by PLM_solver
  lemma oth_class_taut_9_b[PLM]:
    "[(\<phi> \<^bold>& \<psi>) \<^bold>\<rightarrow> \<psi> in v]"
    by PLM_solver

  lemma oth_class_taut_10_a[PLM]:
    "[\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> (\<phi> \<^bold>& \<psi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_10_b[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<rightarrow> \<chi>)) \<^bold>\<equiv> (\<psi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> \<chi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_10_c[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>& \<chi>))) in v]"
    by PLM_solver
  lemma oth_class_taut_10_d[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> ((\<psi> \<^bold>\<rightarrow> \<chi>) \<^bold>\<rightarrow> ((\<phi> \<^bold>\<or> \<psi>) \<^bold>\<rightarrow> \<chi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_10_e[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> ((\<chi> \<^bold>\<rightarrow> \<Theta>) \<^bold>\<rightarrow> ((\<phi> \<^bold>& \<chi>) \<^bold>\<rightarrow> (\<psi> \<^bold>& \<Theta>))) in v]"
    by PLM_solver
  lemma oth_class_taut_10_f[PLM]:
    "[((\<phi> \<^bold>& \<psi>) \<^bold>\<equiv> (\<phi> \<^bold>& \<chi>)) \<^bold>\<equiv> (\<phi> \<^bold>\<rightarrow> (\<psi> \<^bold>\<equiv> \<chi>)) in v]"
    by PLM_solver
  lemma oth_class_taut_10_g[PLM]:
    "[((\<phi> \<^bold>& \<psi>) \<^bold>\<equiv> (\<chi> \<^bold>& \<psi>)) \<^bold>\<equiv> (\<psi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<equiv> \<chi>)) in v]"
    by PLM_solver

  attribute_setup equiv_lr = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm "\<^bold>\<equiv>E"(1)}))
\<close>

  attribute_setup equiv_rl = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm "\<^bold>\<equiv>E"(2)}))
\<close>

  attribute_setup equiv_sym = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm oth_class_taut_3_g[equiv_lr]}))
\<close>

  attribute_setup conj1 = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm "\<^bold>&E"(1)}))
\<close>

  attribute_setup conj2 = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm "\<^bold>&E"(2)}))
\<close>

  attribute_setup conj_sym = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm oth_class_taut_3_b[equiv_lr]}))
\<close>

  
subsection\<open>Identity\<close>
text\<open>\label{TAO_PLM_Identity}\<close>

  lemma id_eq_prop_prop_1[PLM]:
    "[(F::\<Pi>\<^sub>1) \<^bold>= F in v]"
    unfolding identity_defs by PLM_solver 
  lemma id_eq_prop_prop_2[PLM]:
    "[((F::\<Pi>\<^sub>1) \<^bold>= G) \<^bold>\<rightarrow> (G \<^bold>= F) in v]"
    by (meson id_eq_prop_prop_1 CP ded_thm_cor_3 l_identity[axiom_instance])
  lemma id_eq_prop_prop_3[PLM]:
    "[(((F::\<Pi>\<^sub>1) \<^bold>= G) \<^bold>& (G \<^bold>= H)) \<^bold>\<rightarrow> (F \<^bold>= H) in v]"
    by (metis l_identity[axiom_instance] ded_thm_cor_4 CP "\<^bold>&E")
  lemma id_eq_prop_prop_4_a[PLM]:
    "[(F::\<Pi>\<^sub>2) \<^bold>= F in v]"
    unfolding identity_defs by PLM_solver
  lemma id_eq_prop_prop_4_b[PLM]:
    "[(F::\<Pi>\<^sub>3) \<^bold>= F in v]"
    unfolding identity_defs by PLM_solver
  lemma id_eq_prop_prop_5_a[PLM]:
    "[((F::\<Pi>\<^sub>2) \<^bold>= G) \<^bold>\<rightarrow> (G \<^bold>= F) in v]"
    by (meson id_eq_prop_prop_4_a CP ded_thm_cor_3 l_identity[axiom_instance])
  lemma id_eq_prop_prop_5_b[PLM]:
    "[((F::\<Pi>\<^sub>3) \<^bold>= G) \<^bold>\<rightarrow> (G \<^bold>= F) in v]"
    by (meson id_eq_prop_prop_4_b CP ded_thm_cor_3 l_identity[axiom_instance])
  lemma id_eq_prop_prop_6_a[PLM]:
    "[(((F::\<Pi>\<^sub>2) \<^bold>= G) \<^bold>& (G \<^bold>= H)) \<^bold>\<rightarrow> (F \<^bold>= H) in v]"
    by (metis l_identity[axiom_instance] ded_thm_cor_4 CP "\<^bold>&E")
  lemma id_eq_prop_prop_6_b[PLM]:
    "[(((F::\<Pi>\<^sub>3) \<^bold>= G) \<^bold>& (G \<^bold>= H)) \<^bold>\<rightarrow> (F \<^bold>= H) in v]"
    by (metis l_identity[axiom_instance] ded_thm_cor_4 CP "\<^bold>&E")
  lemma id_eq_prop_prop_7[PLM]:
    "[(p::\<Pi>\<^sub>0) \<^bold>= p in v]"
    unfolding identity_defs by PLM_solver
  lemma id_eq_prop_prop_7_b[PLM]:
    "[(p::\<o>) \<^bold>= p in v]"
    unfolding identity_defs by PLM_solver
  lemma id_eq_prop_prop_8[PLM]:
    "[((p::\<Pi>\<^sub>0) \<^bold>= q) \<^bold>\<rightarrow> (q \<^bold>= p) in v]"
    by (meson id_eq_prop_prop_7 CP ded_thm_cor_3 l_identity[axiom_instance])
  lemma id_eq_prop_prop_8_b[PLM]:
    "[((p::\<o>) \<^bold>= q) \<^bold>\<rightarrow> (q \<^bold>= p) in v]"
    by (meson id_eq_prop_prop_7_b CP ded_thm_cor_3 l_identity[axiom_instance])
  lemma id_eq_prop_prop_9[PLM]:
    "[(((p::\<Pi>\<^sub>0) \<^bold>= q) \<^bold>& (q \<^bold>= r)) \<^bold>\<rightarrow> (p \<^bold>= r) in v]"
    by (metis l_identity[axiom_instance] ded_thm_cor_4 CP "\<^bold>&E")
  lemma id_eq_prop_prop_9_b[PLM]:
    "[(((p::\<o>) \<^bold>= q) \<^bold>& (q \<^bold>= r)) \<^bold>\<rightarrow> (p \<^bold>= r) in v]"
    by (metis l_identity[axiom_instance] ded_thm_cor_4 CP "\<^bold>&E")

  lemma eq_E_simple_1[PLM]:
    "[(x \<^bold>=\<^sub>E y) \<^bold>\<equiv> (\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume 1: "[x \<^bold>=\<^sub>E y in v]"
      have "[\<^bold>\<forall> x y . ((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) \<^bold>\<equiv> (\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr>
              \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>)) in v]"
        unfolding identity\<^sub>E_infix_def identity\<^sub>E_def
        apply (rule lambda_predicates_2_2[axiom_universal, axiom_universal, axiom_instance])
        by show_proper
      moreover have "[\<^bold>\<exists> \<alpha> . (\<alpha>\<^sup>P) \<^bold>= x in v]"
        apply (rule cqt_5_mod[where \<psi>="\<lambda> x . x \<^bold>=\<^sub>E y", axiom_instance,deduction])
        unfolding identity\<^sub>E_infix_def
        apply (rule SimpleExOrEnc.intros)
        using 1 unfolding identity\<^sub>E_infix_def by auto
      moreover have "[\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= y in v]"
        apply (rule cqt_5_mod[where \<psi>="\<lambda> y . x \<^bold>=\<^sub>E y",axiom_instance,deduction])
        unfolding identity\<^sub>E_infix_def
        apply (rule SimpleExOrEnc.intros) using 1
        unfolding identity\<^sub>E_infix_def by auto
      ultimately have "[(x \<^bold>=\<^sub>E y) \<^bold>\<equiv> (\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr>
                        \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)) in v]"
        using cqt_1_\<kappa>[axiom_instance,deduction, deduction] by meson
      thus "[(\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)) in v]"
        using 1 "\<^bold>\<equiv>E"(1) by blast
    next
      assume 1: "[\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) in v]"
      have "[\<^bold>\<forall> x y . ((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) \<^bold>\<equiv> (\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr>
              \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>)) in v]"
        unfolding identity\<^sub>E_def identity\<^sub>E_infix_def
        apply (rule lambda_predicates_2_2[axiom_universal, axiom_universal, axiom_instance])
        by show_proper
      moreover have "[\<^bold>\<exists> \<alpha> . (\<alpha>\<^sup>P) \<^bold>= x in v]"
        apply (rule cqt_5_mod[where \<psi>="\<lambda> x . \<lparr>O!,x\<rparr>",axiom_instance,deduction])
        apply (rule SimpleExOrEnc.intros)
        using 1[conj1,conj1] by auto
      moreover have "[\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= y in v]"
        apply (rule cqt_5_mod[where \<psi>="\<lambda> y . \<lparr>O!,y\<rparr>",axiom_instance,deduction])
         apply (rule SimpleExOrEnc.intros)
        using 1[conj1,conj2] by auto
      ultimately have "[(x \<^bold>=\<^sub>E y) \<^bold>\<equiv> (\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr>
                        \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)) in v]"
      using cqt_1_\<kappa>[axiom_instance,deduction, deduction] by meson
      thus "[(x \<^bold>=\<^sub>E y) in v]" using 1 "\<^bold>\<equiv>E"(2) by blast
    qed
  lemma eq_E_simple_2[PLM]:
    "[(x \<^bold>=\<^sub>E y) \<^bold>\<rightarrow> (x \<^bold>= y) in v]"
    unfolding identity_defs by PLM_solver
  lemma eq_E_simple_3[PLM]:
    "[(x \<^bold>= y) \<^bold>\<equiv> ((\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>))
               \<^bold>\<or> (\<lparr>A!,x\<rparr> \<^bold>& \<lparr>A!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,F\<rbrace>))) in v]"
    using eq_E_simple_1
    apply - unfolding identity_defs
    by PLM_solver

  lemma id_eq_obj_1[PLM]: "[(x\<^sup>P) \<^bold>= (x\<^sup>P) in v]"
    proof -
      have "[(\<^bold>\<diamond>\<lparr>E!, x\<^sup>P\<rparr>) \<^bold>\<or> (\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!, x\<^sup>P\<rparr>) in v]"
        using PLM.oth_class_taut_2 by simp
      hence "[(\<^bold>\<diamond>\<lparr>E!, x\<^sup>P\<rparr>) in v] \<or> [(\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!, x\<^sup>P\<rparr>) in v]"
        using CP "\<^bold>\<or>E"(1) by blast
      moreover {
        assume "[(\<^bold>\<diamond>\<lparr>E!, x\<^sup>P\<rparr>) in v]"
        hence "[\<lparr>\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr> in v]"
          apply (rule lambda_predicates_2_1[axiom_instance, equiv_rl, rotated])
          by show_proper
        hence "[\<lparr>\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr> \<^bold>& \<lparr>\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>
                \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,x\<^sup>P\<rparr>) in v]"
          apply - by PLM_solver
        hence "[(x\<^sup>P) \<^bold>=\<^sub>E (x\<^sup>P) in v]"
          using eq_E_simple_1[equiv_rl] unfolding Ordinary_def by fast
      }
      moreover {
        assume "[(\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!, x\<^sup>P\<rparr>) in v]"
        hence "[\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr> in v]"
          apply (rule lambda_predicates_2_1[axiom_instance, equiv_rl, rotated])
          by show_proper
        hence "[\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr> \<^bold>& \<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>
                \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,F\<rbrace>) in v]"
          apply - by PLM_solver
      }
      ultimately show ?thesis unfolding identity_defs Ordinary_def Abstract_def
        using "\<^bold>\<or>I" by blast
    qed
  lemma id_eq_obj_2[PLM]:
    "[((x\<^sup>P) \<^bold>= (y\<^sup>P)) \<^bold>\<rightarrow> ((y\<^sup>P) \<^bold>= (x\<^sup>P)) in v]"
    by (meson l_identity[axiom_instance] id_eq_obj_1 CP ded_thm_cor_3)
  lemma id_eq_obj_3[PLM]:
    "[((x\<^sup>P) \<^bold>= (y\<^sup>P)) \<^bold>& ((y\<^sup>P) \<^bold>= (z\<^sup>P)) \<^bold>\<rightarrow> ((x\<^sup>P) \<^bold>= (z\<^sup>P)) in v]"
    by (metis l_identity[axiom_instance] ded_thm_cor_4 CP "\<^bold>&E")
end

text\<open>
\begin{remark}
  To unify the statements of the properties of equality a type class is introduced.
\end{remark}
\<close>

class id_eq = quantifiable_and_identifiable +
  assumes id_eq_1: "[(x :: 'a) \<^bold>= x in v]"
  assumes id_eq_2: "[((x :: 'a) \<^bold>= y) \<^bold>\<rightarrow> (y \<^bold>= x) in v]"
  assumes id_eq_3: "[((x :: 'a) \<^bold>= y) \<^bold>& (y \<^bold>= z) \<^bold>\<rightarrow> (x \<^bold>= z) in v]"

instantiation \<nu> :: id_eq
begin
  instance proof
    fix x :: \<nu> and v
    show "[x \<^bold>= x in v]"
      using PLM.id_eq_obj_1
      by (simp add: identity_\<nu>_def)
  next
    fix x y::\<nu> and v
    show "[x \<^bold>= y \<^bold>\<rightarrow> y \<^bold>= x in v]"
      using PLM.id_eq_obj_2
      by (simp add: identity_\<nu>_def)
  next
    fix x y z::\<nu> and v
    show "[((x \<^bold>= y) \<^bold>& (y \<^bold>= z)) \<^bold>\<rightarrow> x \<^bold>= z in v]"
      using PLM.id_eq_obj_3
      by (simp add: identity_\<nu>_def)
  qed
end

instantiation \<o> :: id_eq
begin
  instance proof
    fix x :: \<o> and v
    show "[x \<^bold>= x in v]"
      using PLM.id_eq_prop_prop_7 .
  next
    fix x y :: \<o> and v
    show "[x \<^bold>= y \<^bold>\<rightarrow> y \<^bold>= x in v]"
      using PLM.id_eq_prop_prop_8 .
  next
    fix x y z :: \<o> and v
    show "[((x \<^bold>= y) \<^bold>& (y \<^bold>= z)) \<^bold>\<rightarrow> x \<^bold>= z in v]"
      using PLM.id_eq_prop_prop_9 .
  qed
end

instantiation \<Pi>\<^sub>1 :: id_eq
begin
  instance proof
    fix x :: \<Pi>\<^sub>1 and v
    show "[x \<^bold>= x in v]"
      using PLM.id_eq_prop_prop_1 .
  next
    fix x y :: \<Pi>\<^sub>1 and v
    show "[x \<^bold>= y \<^bold>\<rightarrow> y \<^bold>= x in v]"
      using PLM.id_eq_prop_prop_2 .
  next
    fix x y z :: \<Pi>\<^sub>1 and v
    show "[((x \<^bold>= y) \<^bold>& (y \<^bold>= z)) \<^bold>\<rightarrow> x \<^bold>= z in v]"
      using PLM.id_eq_prop_prop_3 .
  qed
end

instantiation \<Pi>\<^sub>2 :: id_eq
begin
  instance proof
    fix x :: \<Pi>\<^sub>2 and v
    show "[x \<^bold>= x in v]"
      using PLM.id_eq_prop_prop_4_a .
  next
    fix x y :: \<Pi>\<^sub>2 and v
    show "[x \<^bold>= y \<^bold>\<rightarrow> y \<^bold>= x in v]"
      using PLM.id_eq_prop_prop_5_a .
  next
    fix x y z :: \<Pi>\<^sub>2 and v
    show "[((x \<^bold>= y) \<^bold>& (y \<^bold>= z)) \<^bold>\<rightarrow> x \<^bold>= z in v]"
      using PLM.id_eq_prop_prop_6_a .
  qed
end

instantiation \<Pi>\<^sub>3 :: id_eq
begin
  instance proof
    fix x :: \<Pi>\<^sub>3 and v
    show "[x \<^bold>= x in v]"
      using PLM.id_eq_prop_prop_4_b .
  next
    fix x y :: \<Pi>\<^sub>3 and v
    show "[x \<^bold>= y \<^bold>\<rightarrow> y \<^bold>= x in v]"
      using PLM.id_eq_prop_prop_5_b .
  next
    fix x y z :: \<Pi>\<^sub>3 and v
    show "[((x \<^bold>= y) \<^bold>& (y \<^bold>= z)) \<^bold>\<rightarrow> x \<^bold>= z in v]"
      using PLM.id_eq_prop_prop_6_b .
  qed
end

context PLM
begin
  lemma id_eq_1[PLM]:
    "[(x::'a::id_eq) \<^bold>= x in v]"
    using id_eq_1 .
  lemma id_eq_2[PLM]:
    "[((x::'a::id_eq) \<^bold>= y) \<^bold>\<rightarrow> (y \<^bold>= x) in v]"
    using id_eq_2 .
  lemma id_eq_3[PLM]:
    "[((x::'a::id_eq) \<^bold>= y) \<^bold>& (y \<^bold>= z) \<^bold>\<rightarrow> (x \<^bold>= z) in v]"
    using id_eq_3 .

  attribute_setup eq_sym = \<open>
    Scan.succeed (Thm.rule_attribute [] 
      (fn _ => fn thm => thm RS @{thm id_eq_2[deduction]}))
\<close>


  lemma all_self_eq_1[PLM]:
    "[\<^bold>\<box>(\<^bold>\<forall> \<alpha> :: 'a::id_eq . \<alpha> \<^bold>= \<alpha>) in v]"
    by PLM_solver
  lemma all_self_eq_2[PLM]:
    "[\<^bold>\<forall>\<alpha> :: 'a::id_eq . \<^bold>\<box>(\<alpha> \<^bold>= \<alpha>) in v]"
    by PLM_solver

  lemma t_id_t_proper_1[PLM]:
    "[\<tau> \<^bold>= \<tau>' \<^bold>\<rightarrow> (\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<tau>) in v]"
    proof (rule CP)
      assume "[\<tau> \<^bold>= \<tau>' in v]"
      moreover {
        assume "[\<tau> \<^bold>=\<^sub>E \<tau>' in v]"
        hence "[\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<tau> in v]"
          apply -
          apply (rule cqt_5_mod[where \<psi>="\<lambda> \<tau> . \<tau> \<^bold>=\<^sub>E \<tau>'", axiom_instance, deduction])
           subgoal unfolding identity_defs by (rule SimpleExOrEnc.intros)
          by simp
      }
      moreover {
        assume "[\<lparr>A!,\<tau>\<rparr> \<^bold>& \<lparr>A!,\<tau>'\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>\<tau>,F\<rbrace> \<^bold>\<equiv> \<lbrace>\<tau>',F\<rbrace>) in v]"
        hence "[\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<tau> in v]"
          apply -
          apply (rule cqt_5_mod[where \<psi>="\<lambda> \<tau> . \<lparr>A!,\<tau>\<rparr>", axiom_instance, deduction])
           subgoal unfolding identity_defs by (rule SimpleExOrEnc.intros)
          by PLM_solver
      }
      ultimately show "[\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<tau> in v]" unfolding identity\<^sub>\<kappa>_def
        using intro_elim_4_b reductio_aa_1 by blast
    qed

  lemma t_id_t_proper_2[PLM]: "[\<tau> \<^bold>= \<tau>' \<^bold>\<rightarrow> (\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<tau>') in v]"
  proof (rule CP)
    assume "[\<tau> \<^bold>= \<tau>' in v]"
    moreover {
      assume "[\<tau> \<^bold>=\<^sub>E \<tau>' in v]"
      hence "[\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<tau>' in v]"
        apply -
        apply (rule cqt_5_mod[where \<psi>="\<lambda> \<tau>' . \<tau> \<^bold>=\<^sub>E \<tau>'", axiom_instance, deduction])
         subgoal unfolding identity_defs by (rule SimpleExOrEnc.intros)
        by simp
    }
    moreover {
      assume "[\<lparr>A!,\<tau>\<rparr> \<^bold>& \<lparr>A!,\<tau>'\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall>F. \<lbrace>\<tau>,F\<rbrace> \<^bold>\<equiv> \<lbrace>\<tau>',F\<rbrace>) in v]"
      hence "[\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<tau>' in v]"
        apply -
        apply (rule cqt_5_mod[where \<psi>="\<lambda> \<tau> . \<lparr>A!,\<tau>\<rparr>", axiom_instance, deduction])
         subgoal unfolding identity_defs by (rule SimpleExOrEnc.intros)
        by PLM_solver
    }
    ultimately show "[\<^bold>\<exists> \<beta> . (\<beta>\<^sup>P) \<^bold>= \<tau>' in v]" unfolding identity\<^sub>\<kappa>_def
      using intro_elim_4_b reductio_aa_1 by blast
  qed

  lemma id_nec[PLM]: "[((\<alpha>::'a::id_eq) \<^bold>= (\<beta>)) \<^bold>\<equiv> \<^bold>\<box>((\<alpha>) \<^bold>= (\<beta>)) in v]"
    apply (rule "\<^bold>\<equiv>I")
     using l_identity[where \<phi> = "(\<lambda> \<beta> .  \<^bold>\<box>((\<alpha>) \<^bold>= (\<beta>)))", axiom_instance]
           id_eq_1 RN ded_thm_cor_4 unfolding identity_\<nu>_def
     apply blast
    using qml_2[axiom_instance] by blast

  lemma id_nec_desc[PLM]:
    "[((\<^bold>\<iota>x. \<phi> x) \<^bold>= (\<^bold>\<iota>x. \<psi> x)) \<^bold>\<equiv> \<^bold>\<box>((\<^bold>\<iota>x. \<phi> x) \<^bold>= (\<^bold>\<iota>x. \<psi> x)) in v]"
    proof (cases "[(\<^bold>\<exists> \<alpha>. (\<alpha>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<phi> x)) in v] \<and> [(\<^bold>\<exists> \<beta>. (\<beta>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<psi> x)) in v]")
      assume "[(\<^bold>\<exists> \<alpha>. (\<alpha>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<phi> x)) in v] \<and> [(\<^bold>\<exists> \<beta>. (\<beta>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<psi> x)) in v]"
      then obtain \<alpha> and \<beta> where
        "[(\<alpha>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<phi> x) in v] \<and> [(\<beta>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<psi> x) in v]"
        apply - unfolding conn_defs by PLM_solver
      moreover {
        moreover have "[(\<alpha>) \<^bold>= (\<beta>) \<^bold>\<equiv> \<^bold>\<box>((\<alpha>) \<^bold>= (\<beta>)) in v]" by PLM_solver
        ultimately have "[((\<^bold>\<iota>x. \<phi> x) \<^bold>= (\<beta>\<^sup>P) \<^bold>\<equiv> \<^bold>\<box>((\<^bold>\<iota>x. \<phi> x) \<^bold>= (\<beta>\<^sup>P))) in v]"
          using l_identity[where \<phi>="\<lambda> \<alpha> . (\<alpha>) \<^bold>= (\<beta>\<^sup>P) \<^bold>\<equiv> \<^bold>\<box>((\<alpha>) \<^bold>= (\<beta>\<^sup>P))", axiom_instance]
          modus_ponens unfolding identity_\<nu>_def by metis
      }
      ultimately show ?thesis
        using l_identity[where \<phi>="\<lambda> \<alpha> . (\<^bold>\<iota>x . \<phi> x) \<^bold>= (\<alpha>)
                                   \<^bold>\<equiv> \<^bold>\<box>((\<^bold>\<iota>x . \<phi> x) \<^bold>= (\<alpha>))", axiom_instance]
        modus_ponens by metis
    next
      assume "\<not>([(\<^bold>\<exists> \<alpha>. (\<alpha>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<phi> x)) in v] \<and> [(\<^bold>\<exists> \<beta>. (\<beta>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<psi> x)) in v])"
      hence "\<not>[\<lparr>A!,(\<^bold>\<iota>x . \<phi> x)\<rparr> in v] \<and> \<not>[(\<^bold>\<iota>x . \<phi> x) \<^bold>=\<^sub>E (\<^bold>\<iota>x . \<psi> x) in v]
           \<or> \<not>[\<lparr>A!,(\<^bold>\<iota>x . \<psi> x)\<rparr> in v] \<and> \<not>[(\<^bold>\<iota>x . \<phi> x) \<^bold>=\<^sub>E (\<^bold>\<iota>x . \<psi> x) in v]"
      unfolding identity\<^sub>E_infix_def
      using cqt_5[axiom_instance] PLM.contraposition_1 SimpleExOrEnc.intros
            vdash_properties_10 by meson
      hence "\<not>[(\<^bold>\<iota>x . \<phi> x) \<^bold>= (\<^bold>\<iota>x . \<psi> x) in v]"
        apply - unfolding identity_defs by PLM_solver
      thus ?thesis apply - apply PLM_solver
        using qml_2[axiom_instance, deduction] by auto
    qed

subsection\<open>Quantification\<close>
text\<open>\label{TAO_PLM_Quantification}\<close>

  lemma rule_ui[PLM,PLM_elim,PLM_dest]:
    "[\<^bold>\<forall>\<alpha> . \<phi> \<alpha> in v] \<Longrightarrow> [\<phi> \<beta> in v]"
    by (meson cqt_1[axiom_instance, deduction])
  lemmas "\<^bold>\<forall>E" = rule_ui

  lemma rule_ui_2[PLM,PLM_elim,PLM_dest]:
    "\<lbrakk>[\<^bold>\<forall>\<alpha> . \<phi> (\<alpha>\<^sup>P) in v]; [\<^bold>\<exists> \<alpha> . (\<alpha>)\<^sup>P \<^bold>= \<beta> in v]\<rbrakk> \<Longrightarrow> [\<phi> \<beta> in v]"
    using cqt_1_\<kappa>[axiom_instance, deduction, deduction] by blast

  lemma cqt_orig_1[PLM]:
    "[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<rightarrow> \<phi> \<beta> in v]"
    by PLM_solver
  lemma cqt_orig_2[PLM]:
    "[(\<^bold>\<forall>\<alpha>. \<phi> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>\<rightarrow> (\<phi> \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<psi> \<alpha>)) in v]"
    by PLM_solver

  lemma universal[PLM]:
    "(\<And>\<alpha> . [\<phi> \<alpha> in v]) \<Longrightarrow> [\<^bold>\<forall> \<alpha> . \<phi> \<alpha> in v]"
    using rule_gen .
  lemmas "\<^bold>\<forall>I" = universal

  lemma cqt_basic_1[PLM]:
    "[(\<^bold>\<forall>\<alpha>. (\<^bold>\<forall>\<beta> . \<phi> \<alpha> \<beta>)) \<^bold>\<equiv> (\<^bold>\<forall>\<beta>. (\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<beta>)) in v]"
    by PLM_solver
  lemma cqt_basic_2[PLM]:
    "[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>) \<^bold>\<equiv> ((\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>& (\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<rightarrow> \<phi> \<alpha>)) in v]"
    by PLM_solver
  lemma cqt_basic_3[PLM]:
    "[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall>\<alpha>. \<psi> \<alpha>)) in v]"
    by PLM_solver
  lemma cqt_basic_4[PLM]:
    "[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>& \<psi> \<alpha>) \<^bold>\<equiv> ((\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>& (\<^bold>\<forall>\<alpha>. \<psi> \<alpha>)) in v]"
    by PLM_solver
  lemma cqt_basic_6[PLM]:
    "[(\<^bold>\<forall>\<alpha>. (\<^bold>\<forall>\<alpha>. \<phi> \<alpha>)) \<^bold>\<equiv> (\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) in v]"
    by PLM_solver
  lemma cqt_basic_7[PLM]:
    "[(\<phi> \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha> . \<psi> \<alpha>)) \<^bold>\<equiv> (\<^bold>\<forall>\<alpha>.(\<phi> \<^bold>\<rightarrow> \<psi> \<alpha>)) in v]"
    by PLM_solver
  lemma cqt_basic_8[PLM]:
    "[((\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<or> (\<^bold>\<forall>\<alpha>. \<psi> \<alpha>)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. (\<phi> \<alpha> \<^bold>\<or> \<psi> \<alpha>)) in v]"
    by PLM_solver
  lemma cqt_basic_9[PLM]:
    "[((\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>& (\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<rightarrow> \<chi> \<alpha>)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<chi> \<alpha>) in v]"
    by PLM_solver
  lemma cqt_basic_10[PLM]:
    "[((\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>) \<^bold>& (\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<equiv> \<chi> \<alpha>)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<chi> \<alpha>) in v]"
    by PLM_solver
  lemma cqt_basic_11[PLM]:
    "[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<equiv> \<phi> \<alpha>) in v]"
    by PLM_solver
  lemma cqt_basic_12[PLM]:
    "[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall>\<beta>. \<phi> \<beta>) in v]"
    by PLM_solver

  lemma existential[PLM,PLM_intro]:
    "[\<phi> \<alpha> in v] \<Longrightarrow> [\<^bold>\<exists> \<alpha>. \<phi> \<alpha> in v]"
    unfolding exists_def by PLM_solver
  lemmas "\<^bold>\<exists>I" = existential
  lemma instantiation_[PLM,PLM_elim,PLM_dest]:
    "\<lbrakk>[\<^bold>\<exists>\<alpha> . \<phi> \<alpha> in v]; (\<And>\<alpha>.[\<phi> \<alpha> in v] \<Longrightarrow> [\<psi> in v])\<rbrakk> \<Longrightarrow> [\<psi> in v]"
    unfolding exists_def by PLM_solver

  lemma Instantiate:
    assumes "[\<^bold>\<exists> x . \<phi> x  in v]"
    obtains x where "[\<phi> x in v]"
    apply (insert assms) unfolding exists_def by PLM_solver
  lemmas "\<^bold>\<exists>E" = Instantiate

  lemma cqt_further_1[PLM]:
    "[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<exists>\<alpha>. \<phi> \<alpha>) in v]"
    by PLM_solver
  lemma cqt_further_2[PLM]:
    "[(\<^bold>\<not>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>)) \<^bold>\<equiv> (\<^bold>\<exists>\<alpha>. \<^bold>\<not>\<phi> \<alpha>) in v]"
    unfolding exists_def by PLM_solver
  lemma cqt_further_3[PLM]:
    "[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<equiv> \<^bold>\<not>(\<^bold>\<exists>\<alpha>. \<^bold>\<not>\<phi> \<alpha>) in v]"
    unfolding exists_def by PLM_solver
  lemma cqt_further_4[PLM]:
    "[(\<^bold>\<not>(\<^bold>\<exists>\<alpha>. \<phi> \<alpha>)) \<^bold>\<equiv> (\<^bold>\<forall>\<alpha>. \<^bold>\<not>\<phi> \<alpha>) in v]"
    unfolding exists_def by PLM_solver
  lemma cqt_further_5[PLM]:
    "[(\<^bold>\<exists>\<alpha>. \<phi> \<alpha> \<^bold>& \<psi> \<alpha>) \<^bold>\<rightarrow> ((\<^bold>\<exists>\<alpha>. \<phi> \<alpha>) \<^bold>& (\<^bold>\<exists>\<alpha>. \<psi> \<alpha>)) in v]"
      unfolding exists_def by PLM_solver
  lemma cqt_further_6[PLM]:
    "[(\<^bold>\<exists>\<alpha>. \<phi> \<alpha> \<^bold>\<or> \<psi> \<alpha>) \<^bold>\<equiv> ((\<^bold>\<exists>\<alpha>. \<phi> \<alpha>) \<^bold>\<or> (\<^bold>\<exists>\<alpha>. \<psi> \<alpha>)) in v]"
    unfolding exists_def by PLM_solver
  lemma cqt_further_10[PLM]:
    "[(\<phi> (\<alpha>::'a::id_eq) \<^bold>& (\<^bold>\<forall> \<beta> . \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>)) \<^bold>\<equiv> (\<^bold>\<forall> \<beta> . \<phi> \<beta> \<^bold>\<equiv> \<beta> \<^bold>= \<alpha>) in v]"
    apply PLM_solver
     using l_identity[axiom_instance, deduction, deduction] id_eq_2[deduction]
     apply blast
    using id_eq_1 by auto
  lemma cqt_further_11[PLM]:
    "[((\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>& (\<^bold>\<forall>\<alpha>. \<psi> \<alpha>)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>) in v]"
    by PLM_solver
  lemma cqt_further_12[PLM]:
    "[((\<^bold>\<not>(\<^bold>\<exists>\<alpha>. \<phi> \<alpha>)) \<^bold>& (\<^bold>\<not>(\<^bold>\<exists>\<alpha>. \<psi> \<alpha>))) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>) in v]"
    unfolding exists_def by PLM_solver
  lemma cqt_further_13[PLM]:
    "[((\<^bold>\<exists>\<alpha>. \<phi> \<alpha>) \<^bold>& (\<^bold>\<not>(\<^bold>\<exists>\<alpha>. \<psi> \<alpha>))) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>)) in v]"
    unfolding exists_def by PLM_solver
  lemma cqt_further_14[PLM]:
    "[(\<^bold>\<exists>\<alpha>. \<^bold>\<exists>\<beta>. \<phi> \<alpha> \<beta>) \<^bold>\<equiv> (\<^bold>\<exists>\<beta>. \<^bold>\<exists>\<alpha>. \<phi> \<alpha> \<beta>) in v]"
    unfolding exists_def by PLM_solver

  lemma nec_exist_unique[PLM]:
    "[(\<^bold>\<forall> x. \<phi> x \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> ((\<^bold>\<exists>!x. \<phi> x) \<^bold>\<rightarrow> (\<^bold>\<exists>!x. \<^bold>\<box>(\<phi> x))) in v]"
    proof (rule CP)
      assume a: "[\<^bold>\<forall>x. \<phi> x \<^bold>\<rightarrow> \<^bold>\<box>\<phi> x in v]"
      show "[(\<^bold>\<exists>!x. \<phi> x) \<^bold>\<rightarrow> (\<^bold>\<exists>!x. \<^bold>\<box>\<phi> x) in v]"
      proof (rule CP)
        assume "[(\<^bold>\<exists>!x. \<phi> x) in v]"
        hence "[\<^bold>\<exists>\<alpha>. \<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
          by (simp only: exists_unique_def)
        then obtain \<alpha> where 1:
          "[\<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
          by (rule "\<^bold>\<exists>E")
        {
          fix \<beta>
          have "[\<^bold>\<box>\<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha> in v]"
            using 1 "\<^bold>&E"(2) qml_2[axiom_instance]
              ded_thm_cor_3 "\<^bold>\<forall>E" by fastforce
        }
        hence "[\<^bold>\<forall>\<beta>. \<^bold>\<box>\<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha> in v]" by (rule "\<^bold>\<forall>I")
        moreover have "[\<^bold>\<box>(\<phi> \<alpha>) in v]"
          using 1 "\<^bold>&E"(1) a vdash_properties_10 cqt_orig_1[deduction]
          by fast
        ultimately have "[\<^bold>\<exists>\<alpha>. \<^bold>\<box>(\<phi> \<alpha>) \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<box>\<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
          using "\<^bold>&I" "\<^bold>\<exists>I" by fast
        thus "[(\<^bold>\<exists>!x. \<^bold>\<box>\<phi> x) in v]"
          unfolding exists_unique_def by assumption
      qed
    qed


subsection\<open>Actuality and Descriptions\<close>
text\<open>\label{TAO_PLM_ActualityAndDescriptions}\<close>

  lemma nec_imp_act[PLM]: "[\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<phi> in v]"
    apply (rule CP)
    using qml_act_2[axiom_instance, equiv_lr]
          qml_2[axiom_actualization, axiom_instance]
          logic_actual_nec_2[axiom_instance, equiv_lr, deduction]
    by blast
  lemma act_conj_act_1[PLM]:
    "[\<^bold>\<A>(\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<phi>) in v]"
    using equiv_def logic_actual_nec_2[axiom_instance]
          logic_actual_nec_4[axiom_instance] "\<^bold>&E"(2) "\<^bold>\<equiv>E"(2)
    by metis
  lemma act_conj_act_2[PLM]:
    "[\<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<phi>) in v]"
    using logic_actual_nec_2[axiom_instance] qml_act_1[axiom_instance]
          ded_thm_cor_3 "\<^bold>\<equiv>E"(2) nec_imp_act
    by blast
  lemma act_conj_act_3[PLM]:
    "[(\<^bold>\<A>\<phi> \<^bold>& \<^bold>\<A>\<psi>) \<^bold>\<rightarrow> \<^bold>\<A>(\<phi> \<^bold>& \<psi>) in v]"
    unfolding conn_defs
    by (metis logic_actual_nec_2[axiom_instance]
              logic_actual_nec_1[axiom_instance]
              "\<^bold>\<equiv>E"(2) CP "\<^bold>\<equiv>E"(4) reductio_aa_2
              vdash_properties_10)
  lemma act_conj_act_4[PLM]:
    "[\<^bold>\<A>(\<^bold>\<A>\<phi> \<^bold>\<equiv> \<phi>) in v]"
    unfolding equiv_def
    by (PLM_solver PLM_intro: act_conj_act_3[where \<phi>="\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<phi>"
                                and \<psi>="\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<phi>", deduction])
  lemma closure_act_1a[PLM]:
    "[\<^bold>\<A>\<^bold>\<A>(\<^bold>\<A>\<phi> \<^bold>\<equiv> \<phi>) in v]"
    using logic_actual_nec_4[axiom_instance]
          act_conj_act_4 "\<^bold>\<equiv>E"(1)
    by blast
  lemma closure_act_1b[PLM]:
    "[\<^bold>\<A>\<^bold>\<A>\<^bold>\<A>(\<^bold>\<A>\<phi> \<^bold>\<equiv> \<phi>) in v]"
    using logic_actual_nec_4[axiom_instance]
          act_conj_act_4 "\<^bold>\<equiv>E"(1)
    by blast
  lemma closure_act_1c[PLM]:
    "[\<^bold>\<A>\<^bold>\<A>\<^bold>\<A>\<^bold>\<A>(\<^bold>\<A>\<phi> \<^bold>\<equiv> \<phi>) in v]"
    using logic_actual_nec_4[axiom_instance]
          act_conj_act_4 "\<^bold>\<equiv>E"(1)
    by blast
  lemma closure_act_2[PLM]:
    "[\<^bold>\<forall>\<alpha>. \<^bold>\<A>(\<^bold>\<A>(\<phi> \<alpha>) \<^bold>\<equiv> \<phi> \<alpha>) in v]"
    by PLM_solver

  lemma closure_act_3[PLM]:
    "[\<^bold>\<A>(\<^bold>\<forall>\<alpha>. \<^bold>\<A>(\<phi> \<alpha>) \<^bold>\<equiv> \<phi> \<alpha>) in v]"
    by (PLM_solver PLM_intro: logic_actual_nec_3[axiom_instance, equiv_rl])
  lemma closure_act_4[PLM]:
    "[\<^bold>\<A>(\<^bold>\<forall>\<alpha>\<^sub>1 \<alpha>\<^sub>2. \<^bold>\<A>(\<phi> \<alpha>\<^sub>1 \<alpha>\<^sub>2) \<^bold>\<equiv> \<phi> \<alpha>\<^sub>1 \<alpha>\<^sub>2) in v]"
    by (PLM_solver PLM_intro: logic_actual_nec_3[axiom_instance, equiv_rl])
  lemma closure_act_4_b[PLM]:
    "[\<^bold>\<A>(\<^bold>\<forall>\<alpha>\<^sub>1 \<alpha>\<^sub>2 \<alpha>\<^sub>3. \<^bold>\<A>(\<phi> \<alpha>\<^sub>1 \<alpha>\<^sub>2 \<alpha>\<^sub>3) \<^bold>\<equiv> \<phi> \<alpha>\<^sub>1 \<alpha>\<^sub>2 \<alpha>\<^sub>3) in v]"
    by (PLM_solver PLM_intro: logic_actual_nec_3[axiom_instance, equiv_rl])
  lemma closure_act_4_c[PLM]:
    "[\<^bold>\<A>(\<^bold>\<forall>\<alpha>\<^sub>1 \<alpha>\<^sub>2 \<alpha>\<^sub>3 \<alpha>\<^sub>4. \<^bold>\<A>(\<phi> \<alpha>\<^sub>1 \<alpha>\<^sub>2 \<alpha>\<^sub>3 \<alpha>\<^sub>4) \<^bold>\<equiv> \<phi> \<alpha>\<^sub>1 \<alpha>\<^sub>2 \<alpha>\<^sub>3 \<alpha>\<^sub>4) in v]"
    by (PLM_solver PLM_intro: logic_actual_nec_3[axiom_instance, equiv_rl])

  lemma RA[PLM,PLM_intro]:
    "([\<phi> in dw]) \<Longrightarrow> [\<^bold>\<A>\<phi> in dw]"
    using logic_actual[necessitation_averse_axiom_instance, equiv_rl] .

  lemma RA_2[PLM,PLM_intro]:
    "([\<psi> in dw] \<Longrightarrow> [\<phi> in dw]) \<Longrightarrow> ([\<^bold>\<A>\<psi> in dw] \<Longrightarrow> [\<^bold>\<A>\<phi> in dw])"
    using RA logic_actual[necessitation_averse_axiom_instance] intro_elim_6_a by blast

  context
  begin
    private lemma ActualE[PLM,PLM_elim,PLM_dest]:
      "[\<^bold>\<A>\<phi> in dw] \<Longrightarrow> [\<phi> in dw]"
      using logic_actual[necessitation_averse_axiom_instance, equiv_lr] .
    
    private lemma NotActualD[PLM_dest]:
      "\<not>[\<^bold>\<A>\<phi> in dw] \<Longrightarrow> \<not>[\<phi> in dw]"
      using RA by metis
    
    private lemma ActualImplI[PLM_intro]:
      "[\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<psi> in v] \<Longrightarrow> [\<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
      using logic_actual_nec_2[axiom_instance, equiv_rl] .
    private lemma ActualImplE[PLM_dest, PLM_elim]:
      "[\<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>) in v] \<Longrightarrow> [\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<psi> in v]"
      using logic_actual_nec_2[axiom_instance, equiv_lr] .
    private lemma NotActualImplD[PLM_dest]:
      "\<not>[\<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>) in v] \<Longrightarrow> \<not>[\<^bold>\<A>\<phi> \<^bold>\<rightarrow> \<^bold>\<A>\<psi> in v]"
      using ActualImplI by blast
    
    private lemma ActualNotI[PLM_intro]:
      "[\<^bold>\<not>\<^bold>\<A>\<phi> in v] \<Longrightarrow> [\<^bold>\<A>\<^bold>\<not>\<phi> in v]"
      using logic_actual_nec_1[axiom_instance, equiv_rl] .
    lemma ActualNotE[PLM_elim,PLM_dest]:
      "[\<^bold>\<A>\<^bold>\<not>\<phi> in v] \<Longrightarrow> [\<^bold>\<not>\<^bold>\<A>\<phi> in v]"
      using logic_actual_nec_1[axiom_instance, equiv_lr] .
    lemma NotActualNotD[PLM_dest]:
      "\<not>[\<^bold>\<A>\<^bold>\<not>\<phi> in v] \<Longrightarrow> \<not>[\<^bold>\<not>\<^bold>\<A>\<phi> in v]"
      using ActualNotI by blast
    
    private  lemma ActualConjI[PLM_intro]:
      "[\<^bold>\<A>\<phi> \<^bold>& \<^bold>\<A>\<psi> in v] \<Longrightarrow> [\<^bold>\<A>(\<phi> \<^bold>& \<psi>) in v]"
      unfolding equiv_def
      by (PLM_solver PLM_intro: act_conj_act_3[deduction])
    private lemma ActualConjE[PLM_elim,PLM_dest]:
      "[\<^bold>\<A>(\<phi> \<^bold>& \<psi>) in v] \<Longrightarrow> [\<^bold>\<A>\<phi> \<^bold>& \<^bold>\<A>\<psi> in v]"
      unfolding conj_def by PLM_solver
    
    private lemma ActualEquivI[PLM_intro]:
      "[\<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<psi> in v] \<Longrightarrow> [\<^bold>\<A>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
      unfolding equiv_def
      by (PLM_solver PLM_intro: act_conj_act_3[deduction])
    private lemma ActualEquivE[PLM_elim, PLM_dest]:
      "[\<^bold>\<A>(\<phi> \<^bold>\<equiv> \<psi>) in v] \<Longrightarrow> [\<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<psi> in v]"
      unfolding equiv_def by PLM_solver

    private lemma ActualBoxI[PLM_intro]:
      "[\<^bold>\<box>\<phi> in v] \<Longrightarrow> [\<^bold>\<A>(\<^bold>\<box>\<phi>) in v]"
      using qml_act_2[axiom_instance, equiv_lr] .
    private lemma ActualBoxE[PLM_elim, PLM_dest]:
      "[\<^bold>\<A>(\<^bold>\<box>\<phi>) in v] \<Longrightarrow> [\<^bold>\<box>\<phi> in v]"
      using qml_act_2[axiom_instance, equiv_rl] .
    private lemma NotActualBoxD[PLM_dest]:
      "\<not>[\<^bold>\<A>(\<^bold>\<box>\<phi>) in v] \<Longrightarrow> \<not>[\<^bold>\<box>\<phi> in v]"
      using ActualBoxI by blast

    private lemma ActualDisjI[PLM_intro]:
      "[\<^bold>\<A>\<phi> \<^bold>\<or> \<^bold>\<A>\<psi> in v] \<Longrightarrow> [\<^bold>\<A>(\<phi> \<^bold>\<or> \<psi>) in v]"
      unfolding disj_def by PLM_solver
    private lemma ActualDisjE[PLM_elim,PLM_dest]:
      "[\<^bold>\<A>(\<phi> \<^bold>\<or> \<psi>) in v] \<Longrightarrow> [\<^bold>\<A>\<phi> \<^bold>\<or> \<^bold>\<A>\<psi> in v]"
      unfolding disj_def by PLM_solver
    private lemma NotActualDisjD[PLM_dest]:
      "\<not>[\<^bold>\<A>(\<phi> \<^bold>\<or> \<psi>) in v] \<Longrightarrow> \<not>[\<^bold>\<A>\<phi> \<^bold>\<or> \<^bold>\<A>\<psi> in v]"
      using ActualDisjI by blast

    private lemma ActualForallI[PLM_intro]:
      "[\<^bold>\<forall> x . \<^bold>\<A>(\<phi> x) in v] \<Longrightarrow> [\<^bold>\<A>(\<^bold>\<forall> x . \<phi> x) in v]"
      using logic_actual_nec_3[axiom_instance, equiv_rl] .
    lemma ActualForallE[PLM_elim,PLM_dest]:
      "[\<^bold>\<A>(\<^bold>\<forall> x . \<phi> x) in v] \<Longrightarrow> [\<^bold>\<forall> x . \<^bold>\<A>(\<phi> x) in v]"
      using logic_actual_nec_3[axiom_instance, equiv_lr] .
    lemma NotActualForallD[PLM_dest]:
      "\<not>[\<^bold>\<A>(\<^bold>\<forall> x . \<phi> x) in v] \<Longrightarrow> \<not>[\<^bold>\<forall> x . \<^bold>\<A>(\<phi> x) in v]"
      using ActualForallI by blast

    lemma ActualActualI[PLM_intro]:
      "[\<^bold>\<A>\<phi> in v] \<Longrightarrow> [\<^bold>\<A>\<^bold>\<A>\<phi> in v]"
      using logic_actual_nec_4[axiom_instance, equiv_lr] .
    lemma ActualActualE[PLM_elim,PLM_dest]:
      "[\<^bold>\<A>\<^bold>\<A>\<phi> in v] \<Longrightarrow> [\<^bold>\<A>\<phi> in v]"
      using logic_actual_nec_4[axiom_instance, equiv_rl] .
    lemma NotActualActualD[PLM_dest]:
      "\<not>[\<^bold>\<A>\<^bold>\<A>\<phi> in v] \<Longrightarrow> \<not>[\<^bold>\<A>\<phi> in v]"
      using ActualActualI by blast
  end

  lemma ANeg_1[PLM]:
    "[\<^bold>\<not>\<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<not>\<phi> in dw]"
    by PLM_solver
  lemma ANeg_2[PLM]:
    "[\<^bold>\<not>\<^bold>\<A>\<^bold>\<not>\<phi> \<^bold>\<equiv> \<phi> in dw]"
    by PLM_solver
  lemma Act_Basic_1[PLM]:
    "[\<^bold>\<A>\<phi> \<^bold>\<or> \<^bold>\<A>\<^bold>\<not>\<phi> in v]"
    by PLM_solver
  lemma Act_Basic_2[PLM]:
    "[\<^bold>\<A>(\<phi> \<^bold>& \<psi>) \<^bold>\<equiv> (\<^bold>\<A>\<phi> \<^bold>& \<^bold>\<A>\<psi>) in v]"
    by PLM_solver
  lemma Act_Basic_3[PLM]:
    "[\<^bold>\<A>(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<equiv> ((\<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>)) \<^bold>& (\<^bold>\<A>(\<psi> \<^bold>\<rightarrow> \<phi>))) in v]"
    by PLM_solver
  lemma Act_Basic_4[PLM]:
    "[(\<^bold>\<A>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>& \<^bold>\<A>(\<psi> \<^bold>\<rightarrow> \<phi>)) \<^bold>\<equiv> (\<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<psi>) in v]"
    by PLM_solver
  lemma Act_Basic_5[PLM]:
    "[\<^bold>\<A>(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<equiv> (\<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<A>\<psi>) in v]"
    by PLM_solver
  lemma Act_Basic_6[PLM]:
    "[\<^bold>\<diamond>\<phi> \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<diamond>\<phi>) in v]"
    unfolding diamond_def by PLM_solver
  lemma Act_Basic_7[PLM]:
    "[\<^bold>\<A>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<^bold>\<A>\<phi> in v]"
    by (simp add: qml_2[axiom_instance] qml_act_1[axiom_instance] "\<^bold>\<equiv>I")
  lemma Act_Basic_8[PLM]:
    "[\<^bold>\<A>(\<^bold>\<box>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi> in v]"
    by (metis qml_act_2[axiom_instance] CP Act_Basic_7 "\<^bold>\<equiv>E"(1)
              "\<^bold>\<equiv>E"(2) nec_imp_act vdash_properties_10)
  lemma Act_Basic_9[PLM]:
    "[\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<A>\<phi> in v]"
    using qml_act_1[axiom_instance] ded_thm_cor_3 nec_imp_act by blast
  lemma Act_Basic_10[PLM]:
    "[\<^bold>\<A>(\<phi> \<^bold>\<or> \<psi>) \<^bold>\<equiv> \<^bold>\<A>\<phi> \<^bold>\<or> \<^bold>\<A>\<psi> in v]"
    by PLM_solver

  lemma Act_Basic_11[PLM]:
    "[\<^bold>\<A>(\<^bold>\<exists>\<alpha>. \<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<exists>\<alpha>.\<^bold>\<A>(\<phi> \<alpha>)) in v]"
    proof -
      have "[\<^bold>\<A>(\<^bold>\<forall> \<alpha> . \<^bold>\<not>\<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall> \<alpha> . \<^bold>\<A>\<^bold>\<not>\<phi> \<alpha>) in v]"
        using logic_actual_nec_3[axiom_instance] by blast
      hence "[\<^bold>\<not>\<^bold>\<A>(\<^bold>\<forall> \<alpha> . \<^bold>\<not>\<phi> \<alpha>) \<^bold>\<equiv> \<^bold>\<not>(\<^bold>\<forall> \<alpha> . \<^bold>\<A>\<^bold>\<not>\<phi> \<alpha>) in v]"
        using oth_class_taut_5_d[equiv_lr] by blast
      moreover have "[\<^bold>\<A>\<^bold>\<not>(\<^bold>\<forall> \<alpha> . \<^bold>\<not>\<phi> \<alpha>) \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>(\<^bold>\<forall> \<alpha> . \<^bold>\<not>\<phi> \<alpha>) in v]"
        using logic_actual_nec_1[axiom_instance] by blast
      ultimately have "[\<^bold>\<A>\<^bold>\<not>(\<^bold>\<forall> \<alpha> . \<^bold>\<not>\<phi> \<alpha>) \<^bold>\<equiv> \<^bold>\<not>(\<^bold>\<forall> \<alpha> . \<^bold>\<A>\<^bold>\<not>\<phi> \<alpha>) in v]"
        using "\<^bold>\<equiv>E"(5) by auto
      moreover {
        have "[\<^bold>\<forall> \<alpha> . \<^bold>\<A>\<^bold>\<not>\<phi> \<alpha> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<A>\<phi> \<alpha> in v]"
          using logic_actual_nec_1[axiom_universal, axiom_instance] by blast 
        hence "[(\<^bold>\<forall> \<alpha> . \<^bold>\<A>\<^bold>\<not>\<phi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall> \<alpha> . \<^bold>\<not>\<^bold>\<A>\<phi> \<alpha>) in v]"
          using cqt_basic_3[deduction] by fast
        hence "[(\<^bold>\<not>(\<^bold>\<forall> \<alpha> . \<^bold>\<A>\<^bold>\<not>\<phi> \<alpha>)) \<^bold>\<equiv> \<^bold>\<not>(\<^bold>\<forall> \<alpha> . \<^bold>\<not>\<^bold>\<A>\<phi> \<alpha>) in v]"
          using oth_class_taut_5_d[equiv_lr] by blast
      }
      ultimately show ?thesis unfolding exists_def using "\<^bold>\<equiv>E"(5) by auto
    qed

  lemma act_quant_uniq[PLM]:
    "[(\<^bold>\<forall> z . \<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= x) \<^bold>\<equiv> (\<^bold>\<forall> z . \<phi> z \<^bold>\<equiv> z \<^bold>= x) in dw]"
    by PLM_solver

  lemma fund_cont_desc[PLM]:
    "[(x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<equiv> (\<^bold>\<forall> z . \<phi> z \<^bold>\<equiv> (z \<^bold>= x)) in dw]"
    using descriptions[axiom_instance] act_quant_uniq "\<^bold>\<equiv>E"(5) by fast

  lemma hintikka[PLM]:
    "[(x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<equiv> (\<phi> x \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= x)) in dw]"
    proof -
      have "[(\<^bold>\<forall> z . \<phi> z \<^bold>\<equiv> z \<^bold>= x) \<^bold>\<equiv> (\<phi> x \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= x)) in dw]"
        unfolding identity_\<nu>_def apply PLM_solver using id_eq_obj_1 apply simp
        using l_identity[where \<phi>="\<lambda> x . \<phi> x", axiom_instance,
                          deduction, deduction]
        using id_eq_obj_2[deduction] unfolding identity_\<nu>_def by fastforce
      thus ?thesis using "\<^bold>\<equiv>E"(5) fund_cont_desc by blast
    qed

  lemma russell_axiom_a[PLM]:
    "[(\<lparr>F, \<^bold>\<iota>x. \<phi> x\<rparr>) \<^bold>\<equiv> (\<^bold>\<exists> x . \<phi> x \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= x) \<^bold>& \<lparr>F, x\<^sup>P\<rparr>) in dw]"
    (is "[?lhs \<^bold>\<equiv> ?rhs in dw]")
    proof -
      {
        assume 1: "[?lhs in dw]"
        hence "[\<^bold>\<exists>\<alpha>. \<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in dw]"
        using cqt_5[axiom_instance, deduction]
              SimpleExOrEnc.intros
        by blast
        then obtain \<alpha> where 2:
          "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in dw]"
          using "\<^bold>\<exists>E" by auto          
        hence 3: "[\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= \<alpha>) in dw]"
          using hintikka[equiv_lr] by simp
        from 2 have "[(\<^bold>\<iota>x. \<phi> x) \<^bold>= (\<alpha>\<^sup>P)  in dw]"
          using l_identity[where \<alpha>="\<alpha>\<^sup>P" and \<beta>="\<^bold>\<iota>x. \<phi> x" and \<phi>="\<lambda> x . x \<^bold>= \<alpha>\<^sup>P",
                axiom_instance, deduction, deduction]
                id_eq_obj_1[where x=\<alpha>] by auto
        hence "[\<lparr>F, \<alpha>\<^sup>P\<rparr> in dw]"
        using 1 l_identity[where \<beta>="\<alpha>\<^sup>P" and \<alpha>="\<^bold>\<iota>x. \<phi> x" and \<phi>="\<lambda> x . \<lparr>F,x\<rparr>",
                           axiom_instance, deduction, deduction] by auto
        with 3 have "[\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= \<alpha>) \<^bold>& \<lparr>F, \<alpha>\<^sup>P\<rparr> in dw]" by (rule "\<^bold>&I")
        hence "[?rhs in dw]" using "\<^bold>\<exists>I"[where \<alpha>=\<alpha>] by simp
      }
      moreover {
        assume "[?rhs in dw]"
        then obtain \<alpha> where 4:
          "[\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= \<alpha>) \<^bold>& \<lparr>F, \<alpha>\<^sup>P\<rparr> in dw]"
          using "\<^bold>\<exists>E" by auto
        hence "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> x) in dw] \<and> [\<lparr>F, \<alpha>\<^sup>P\<rparr> in dw]"
          using hintikka[equiv_rl] "\<^bold>&E" by blast
        hence "[?lhs in dw]"
          using l_identity[axiom_instance, deduction, deduction]
          by blast
      }
      ultimately show ?thesis by PLM_solver
    qed

  lemma russell_axiom_g[PLM]:
    "[\<lbrace>\<^bold>\<iota>x. \<phi> x,F\<rbrace> \<^bold>\<equiv> (\<^bold>\<exists> x . \<phi> x \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= x) \<^bold>& \<lbrace>x\<^sup>P, F\<rbrace>) in dw]"
    (is "[?lhs \<^bold>\<equiv> ?rhs in dw]")
    proof -
      {
        assume 1: "[?lhs in dw]"
        hence "[\<^bold>\<exists>\<alpha>. \<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in dw]"
        using cqt_5[axiom_instance, deduction] SimpleExOrEnc.intros by blast
        then obtain \<alpha> where 2: "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in dw]" by (rule "\<^bold>\<exists>E")
        hence 3: "[(\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= \<alpha>)) in dw]"
          using hintikka[equiv_lr] by simp
        from 2 have "[(\<^bold>\<iota>x. \<phi> x) \<^bold>= \<alpha>\<^sup>P  in dw]"
          using l_identity[where \<alpha>="\<alpha>\<^sup>P" and \<beta>="\<^bold>\<iota>x. \<phi> x" and \<phi>="\<lambda> x . x \<^bold>= \<alpha>\<^sup>P",
                axiom_instance, deduction, deduction]
                id_eq_obj_1[where x=\<alpha>] by auto
        hence "[\<lbrace>\<alpha>\<^sup>P, F\<rbrace> in dw]"
        using 1 l_identity[where \<beta>="\<alpha>\<^sup>P" and \<alpha>="\<^bold>\<iota>x. \<phi> x" and \<phi>="\<lambda> x . \<lbrace>x,F\<rbrace>",
                           axiom_instance, deduction, deduction] by auto
        with 3 have "[(\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= \<alpha>)) \<^bold>& \<lbrace>\<alpha>\<^sup>P, F\<rbrace> in dw]"
          using "\<^bold>&I" by auto
        hence "[?rhs in dw]" using "\<^bold>\<exists>I"[where \<alpha>=\<alpha>] by (simp add: identity_defs)
      }
      moreover {
        assume "[?rhs in dw]"
        then obtain \<alpha> where 4:
          "[\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= \<alpha>) \<^bold>& \<lbrace>\<alpha>\<^sup>P, F\<rbrace> in dw]"
          using "\<^bold>\<exists>E" by auto
        hence "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> x) in dw] \<and> [\<lbrace>\<alpha>\<^sup>P, F\<rbrace> in dw]"
          using hintikka[equiv_rl] "\<^bold>&E" by blast
        hence "[?lhs in dw]"
          using l_identity[axiom_instance, deduction, deduction]
          by fast
      }
      ultimately show ?thesis by PLM_solver
    qed

  lemma russell_axiom[PLM]:
    assumes "SimpleExOrEnc \<psi>"
    shows "[\<psi> (\<^bold>\<iota>x. \<phi> x) \<^bold>\<equiv> (\<^bold>\<exists> x . \<phi> x \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= x) \<^bold>& \<psi> (x\<^sup>P)) in dw]"
    (is "[?lhs \<^bold>\<equiv> ?rhs in dw]")
    proof -
      {
        assume 1: "[?lhs in dw]"
        hence "[\<^bold>\<exists>\<alpha>. \<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in dw]"
        using cqt_5[axiom_instance, deduction] assms by blast
        then obtain \<alpha> where 2: "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in dw]" by (rule "\<^bold>\<exists>E")
        hence 3: "[(\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= \<alpha>)) in dw]"
          using hintikka[equiv_lr] by simp
        from 2 have "[(\<^bold>\<iota>x. \<phi> x) \<^bold>= (\<alpha>\<^sup>P)  in dw]"
          using l_identity[where \<alpha>="\<alpha>\<^sup>P" and \<beta>="\<^bold>\<iota>x. \<phi> x" and \<phi>="\<lambda> x . x \<^bold>= \<alpha>\<^sup>P",
                axiom_instance, deduction, deduction]
                id_eq_obj_1[where x=\<alpha>] by auto
        hence "[\<psi> (\<alpha>\<^sup>P) in dw]"
          using 1 l_identity[where \<beta>="\<alpha>\<^sup>P" and \<alpha>="\<^bold>\<iota>x. \<phi> x" and \<phi>="\<lambda> x . \<psi> x",
                             axiom_instance, deduction, deduction] by auto
        with 3 have "[\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= \<alpha>) \<^bold>& \<psi> (\<alpha>\<^sup>P) in dw]"
          using "\<^bold>&I" by auto
        hence "[?rhs in dw]" using "\<^bold>\<exists>I"[where \<alpha>=\<alpha>] by (simp add: identity_defs)
      }
      moreover {
        assume "[?rhs in dw]"
        then obtain \<alpha> where 4:
          "[\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<phi> z \<^bold>\<rightarrow> z \<^bold>= \<alpha>) \<^bold>& \<psi> (\<alpha>\<^sup>P) in dw]"
          using "\<^bold>\<exists>E" by auto
        hence "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> x) in dw] \<and> [\<psi> (\<alpha>\<^sup>P) in dw]"
          using hintikka[equiv_rl] "\<^bold>&E" by blast
        hence "[?lhs in dw]"
          using l_identity[axiom_instance, deduction, deduction]
          by fast
      }
      ultimately show ?thesis by PLM_solver
    qed

  lemma unique_exists[PLM]:
    "[(\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<equiv> (\<^bold>\<exists>!x . \<phi> x) in dw]"     
    proof((rule "\<^bold>\<equiv>I", rule CP, rule_tac[2] CP))
      assume "[\<^bold>\<exists>y. y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in dw]"
      then obtain \<alpha> where
        "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in dw]"
        by (rule "\<^bold>\<exists>E")
      hence "[\<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in dw]"
        using hintikka[equiv_lr] by auto
      thus "[\<^bold>\<exists>!x . \<phi> x in dw]"
        unfolding exists_unique_def using "\<^bold>\<exists>I" by fast
    next
      assume "[\<^bold>\<exists>!x . \<phi> x in dw]"
      then obtain \<alpha> where
        "[\<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in dw]"
        unfolding exists_unique_def by (rule "\<^bold>\<exists>E")
      hence "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in dw]"
        using hintikka[equiv_rl] by auto
      thus "[\<^bold>\<exists>y. y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in dw]"
        using "\<^bold>\<exists>I" by fast
    qed

  lemma y_in_1[PLM]:
    "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi>) \<^bold>\<rightarrow> \<phi> in dw]"
    using hintikka[equiv_lr, conj1] by (rule CP)

  lemma y_in_2[PLM]:
    "[z\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> x) \<^bold>\<rightarrow> \<phi> z in dw]"
    using hintikka[equiv_lr, conj1] by (rule CP)

  lemma y_in_3[PLM]:
    "[(\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> (x\<^sup>P))) \<^bold>\<rightarrow> \<phi> (\<^bold>\<iota>x . \<phi> (x\<^sup>P)) in dw]"
    proof (rule CP)
      assume "[(\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> (x\<^sup>P))) in dw]"
      then obtain y where 1:
        "[y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> (x\<^sup>P)) in dw]"
        by (rule "\<^bold>\<exists>E")
      hence "[\<phi> (y\<^sup>P) in dw]"
        using y_in_2[deduction] unfolding identity_\<nu>_def by blast
      thus "[\<phi> (\<^bold>\<iota>x. \<phi> (x\<^sup>P)) in dw]"
        using l_identity[axiom_instance, deduction,
                         deduction] 1 by fast
    qed

  lemma act_quant_nec[PLM]:
    "[(\<^bold>\<forall>z . (\<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= x)) \<^bold>\<equiv> (\<^bold>\<forall>z. \<^bold>\<A>\<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= x) in v]"
    by PLM_solver

  lemma equi_desc_descA_1[PLM]:
    "[(x\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> x)) \<^bold>\<equiv> (x\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<^bold>\<A>\<phi> x)) in v]"
    using descriptions[axiom_instance] apply (rule "\<^bold>\<equiv>E"(5))
    using act_quant_nec apply (rule "\<^bold>\<equiv>E"(5))
    using descriptions[axiom_instance]
    by (meson "\<^bold>\<equiv>E"(6) oth_class_taut_4_a)

  lemma equi_desc_descA_2[PLM]:
    "[(\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<rightarrow> ((\<^bold>\<iota>x . \<phi> x) \<^bold>= (\<^bold>\<iota>x . \<^bold>\<A>\<phi> x)) in v]"
    proof (rule CP)
      assume "[\<^bold>\<exists>y. y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
      then obtain y where
        "[y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
        by (rule "\<^bold>\<exists>E")
      moreover hence "[y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<^bold>\<A>\<phi> x) in v]"
        using equi_desc_descA_1[equiv_lr] by auto
      ultimately show "[(\<^bold>\<iota>x. \<phi> x) \<^bold>= (\<^bold>\<iota>x. \<^bold>\<A>\<phi> x) in v]"
        using l_identity[axiom_instance, deduction, deduction]
        by fast
    qed

  lemma equi_desc_descA_3[PLM]:
    assumes "SimpleExOrEnc \<psi>"
    shows "[\<psi> (\<^bold>\<iota>x. \<phi> x) \<^bold>\<rightarrow> (\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<^bold>\<A>\<phi> x)) in v]"
    proof (rule CP)
      assume "[\<psi> (\<^bold>\<iota>x. \<phi> x) in v]"
      hence "[\<^bold>\<exists>\<alpha>. \<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
        using cqt_5[OF assms, axiom_instance, deduction] by auto
      then obtain \<alpha> where "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]" by (rule "\<^bold>\<exists>E")
      hence "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<^bold>\<A>\<phi> x) in v]"
        using equi_desc_descA_1[equiv_lr] by auto
      thus "[\<^bold>\<exists>y. y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<^bold>\<A>\<phi> x) in v]"
        using "\<^bold>\<exists>I" by fast
    qed

  lemma equi_desc_descA_4[PLM]:
    assumes "SimpleExOrEnc \<psi>"
    shows "[\<psi> (\<^bold>\<iota>x. \<phi> x) \<^bold>\<rightarrow> ((\<^bold>\<iota>x. \<phi> x) \<^bold>= (\<^bold>\<iota>x. \<^bold>\<A>\<phi> x)) in v]"
    proof (rule CP)
      assume "[\<psi> (\<^bold>\<iota>x. \<phi> x) in v]"
      hence "[\<^bold>\<exists>\<alpha>. \<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
        using cqt_5[OF assms, axiom_instance, deduction] by auto
      then obtain \<alpha> where "[\<alpha>\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]" by (rule "\<^bold>\<exists>E")
      moreover hence "[\<alpha>\<^sup>P  \<^bold>= (\<^bold>\<iota>x . \<^bold>\<A>\<phi> x) in v]"
        using equi_desc_descA_1[equiv_lr] by auto
      ultimately show "[(\<^bold>\<iota>x. \<phi> x)  \<^bold>= (\<^bold>\<iota>x . \<^bold>\<A>\<phi> x) in v]"
        using l_identity[axiom_instance, deduction, deduction] by fast
    qed

  lemma nec_hintikka_scheme[PLM]:
    "[(x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<equiv> (\<^bold>\<A>\<phi> x \<^bold>& (\<^bold>\<forall> z . \<^bold>\<A>\<phi> z \<^bold>\<rightarrow> z \<^bold>= x)) in v]"
    using descriptions[axiom_instance]
    apply (rule "\<^bold>\<equiv>E"(5))
    apply PLM_solver
     using id_eq_obj_1 apply simp
     using id_eq_obj_2[deduction]
           l_identity[where \<alpha>="x", axiom_instance, deduction, deduction]
     unfolding identity_\<nu>_def
     apply blast
    using l_identity[where \<alpha>="x", axiom_instance, deduction, deduction]
    id_eq_2[where 'a=\<nu>, deduction] unfolding identity_\<nu>_def by meson

  lemma equiv_desc_eq[PLM]:
    assumes "\<And>x.[\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x) in v]"
    shows "[(\<^bold>\<forall> x . ((x\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> x)) \<^bold>\<equiv> (x\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<psi> x)))) in v]"
    proof(rule "\<^bold>\<forall>I")
      fix x
      {
        assume "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> x) in v]"
        hence 1: "[\<^bold>\<A>\<phi> x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<rightarrow> z \<^bold>= x) in v]"
          using nec_hintikka_scheme[equiv_lr] by auto
        hence 2: "[\<^bold>\<A>\<phi> x in v] \<and> [(\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<rightarrow> z \<^bold>= x) in v]"
          using "\<^bold>&E" by blast
        {
           fix z
           {
             assume "[\<^bold>\<A>\<psi> z in v]"
             hence "[\<^bold>\<A>\<phi> z in v]"
              using assms[where x=z] apply - by PLM_solver
             moreover have "[\<^bold>\<A>\<phi> z \<^bold>\<rightarrow> z \<^bold>= x in v]"
               using 2 cqt_1[axiom_instance,deduction] by auto
             ultimately have "[z \<^bold>= x in v]"
              using vdash_properties_10 by auto
           }
           hence "[\<^bold>\<A>\<psi> z \<^bold>\<rightarrow> z \<^bold>= x in v]" by (rule CP)
        }
        hence "[(\<^bold>\<forall> z . \<^bold>\<A>\<psi> z \<^bold>\<rightarrow> z \<^bold>= x) in v]" by (rule "\<^bold>\<forall>I")
        moreover have "[\<^bold>\<A>\<psi> x in v]"
          using 1[conj1] assms[where x=x]
          apply - by PLM_solver
        ultimately have "[\<^bold>\<A>\<psi> x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<psi> z \<^bold>\<rightarrow> z \<^bold>= x) in v]"
          by PLM_solver
        hence "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<psi> x) in v]"
         using nec_hintikka_scheme[where \<phi>="\<psi>", equiv_rl] by auto
      }
      moreover {
        assume "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<psi> x) in v]"
        hence 1: "[\<^bold>\<A>\<psi> x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<psi> z \<^bold>\<rightarrow> z \<^bold>= x) in v]"
          using nec_hintikka_scheme[equiv_lr] by auto
        hence 2: "[\<^bold>\<A>\<psi> x in v] \<and> [(\<^bold>\<forall>z. \<^bold>\<A>\<psi> z \<^bold>\<rightarrow> z \<^bold>= x) in v]"
          using "\<^bold>&E" by blast
        {
          fix z
          {
            assume "[\<^bold>\<A>\<phi> z in v]"
            hence "[\<^bold>\<A>\<psi> z in v]"
              using assms[where x=z]
              apply - by PLM_solver
            moreover have "[\<^bold>\<A>\<psi> z \<^bold>\<rightarrow> z \<^bold>= x in v]"
              using 2 cqt_1[axiom_instance,deduction] by auto
            ultimately have "[z \<^bold>= x in v]"
              using vdash_properties_10 by auto
          }
          hence "[\<^bold>\<A>\<phi> z \<^bold>\<rightarrow> z \<^bold>= x in v]" by (rule CP)
        }
        hence "[(\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<rightarrow> z \<^bold>= x) in v]" by (rule "\<^bold>\<forall>I")
        moreover have "[\<^bold>\<A>\<phi> x in v]"
          using 1[conj1] assms[where x=x]
          apply - by PLM_solver
        ultimately have "[\<^bold>\<A>\<phi> x \<^bold>& (\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<rightarrow> z \<^bold>= x) in v]"
          by PLM_solver
        hence "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
          using nec_hintikka_scheme[where \<phi>="\<phi>",equiv_rl]
          by auto
      }
      ultimately show "[x\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x) \<^bold>\<equiv> (x\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<psi> x) in v]"
        using "\<^bold>\<equiv>I" CP by auto
    qed

  lemma UniqueAux:
    assumes "[(\<^bold>\<A>\<phi> (\<alpha>::\<nu>) \<^bold>& (\<^bold>\<forall> z . \<^bold>\<A>(\<phi> z) \<^bold>\<rightarrow> z \<^bold>= \<alpha>)) in v]"
    shows "[(\<^bold>\<forall> z . (\<^bold>\<A>(\<phi> z) \<^bold>\<equiv> (z \<^bold>= \<alpha>))) in v]"
    proof -
      {
        fix z
        {
          assume "[\<^bold>\<A>(\<phi> z) in v]"
          hence "[z \<^bold>= \<alpha> in v]"
            using assms[conj2, THEN cqt_1[where \<alpha>=z,
                          axiom_instance, deduction],
                        deduction] by auto
        }
        moreover {
          assume "[z \<^bold>= \<alpha> in v]"
          hence "[\<alpha> \<^bold>= z in v]"
            unfolding identity_\<nu>_def
            using id_eq_obj_2[deduction] by fast
          hence "[\<^bold>\<A>(\<phi> z) in v]" using assms[conj1]
            using l_identity[axiom_instance, deduction,
                             deduction] by fast
        }
        ultimately have "[(\<^bold>\<A>(\<phi> z) \<^bold>\<equiv> (z \<^bold>= \<alpha>)) in v]"
          using "\<^bold>\<equiv>I" CP by auto
      }
      thus "[(\<^bold>\<forall> z . (\<^bold>\<A>(\<phi> z) \<^bold>\<equiv> (z \<^bold>= \<alpha>))) in v]"
      by (rule "\<^bold>\<forall>I")
    qed

  lemma nec_russell_axiom[PLM]:
    assumes "SimpleExOrEnc \<psi>"
    shows "[(\<psi> (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<equiv> (\<^bold>\<exists> x . (\<^bold>\<A>\<phi> x \<^bold>& (\<^bold>\<forall> z . \<^bold>\<A>(\<phi> z) \<^bold>\<rightarrow> z \<^bold>= x))
                              \<^bold>& \<psi> (x\<^sup>P)) in v]"
    (is "[?lhs \<^bold>\<equiv> ?rhs in v]")
    proof -
      {
        assume 1: "[?lhs in v]"
        hence "[\<^bold>\<exists>\<alpha>. (\<alpha>\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
          using cqt_5[axiom_instance, deduction] assms by blast
        then obtain \<alpha> where 2: "[(\<alpha>\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]" by (rule "\<^bold>\<exists>E")
        hence "[(\<^bold>\<forall> z . (\<^bold>\<A>(\<phi> z) \<^bold>\<equiv> (z \<^bold>= \<alpha>))) in v]"
          using descriptions[axiom_instance, equiv_lr] by auto
        hence 3: "[(\<^bold>\<A>\<phi> \<alpha>) \<^bold>& (\<^bold>\<forall> z . (\<^bold>\<A>(\<phi> z) \<^bold>\<rightarrow> (z \<^bold>= \<alpha>))) in v]"
          using cqt_1[where \<alpha>=\<alpha> and \<phi>="\<lambda> z . (\<^bold>\<A>(\<phi> z) \<^bold>\<equiv> (z \<^bold>= \<alpha>))",
                      axiom_instance, deduction, equiv_rl]
          using id_eq_obj_1[where x=\<alpha>] unfolding identity_\<nu>_def
          using hintikka[equiv_lr] cqt_basic_2[equiv_lr,conj1]
          "\<^bold>&I" by fast
        from 2 have "[(\<^bold>\<iota>x. \<phi> x) \<^bold>= (\<alpha>\<^sup>P)  in v]"
          using l_identity[where \<beta>="(\<^bold>\<iota>x. \<phi> x)" and \<phi>="\<lambda> x . x \<^bold>= (\<alpha>\<^sup>P)",
                axiom_instance, deduction, deduction]
                id_eq_obj_1[where x=\<alpha>] by auto
        hence "[\<psi> (\<alpha>\<^sup>P) in v]"
          using 1 l_identity[where \<alpha>="(\<^bold>\<iota>x. \<phi> x)" and \<phi>="\<lambda> x . \<psi> x",
                             axiom_instance, deduction,
                             deduction] by auto
        with 3 have "[(\<^bold>\<A>\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<^bold>\<A>(\<phi> z) \<^bold>\<rightarrow> (z \<^bold>= \<alpha>))) \<^bold>& \<psi> (\<alpha>\<^sup>P) in v]"
          using "\<^bold>&I" by simp
        hence "[?rhs in v]"
          using "\<^bold>\<exists>I"[where \<alpha>=\<alpha>]
          by (simp add: identity_defs)
      }
      moreover {
        assume "[?rhs in v]"
        then obtain \<alpha> where 4:
          "[(\<^bold>\<A>\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> z . \<^bold>\<A>(\<phi> z) \<^bold>\<rightarrow> z \<^bold>= \<alpha>)) \<^bold>& \<psi> (\<alpha>\<^sup>P) in v]"
          using "\<^bold>\<exists>E" by auto
        hence "[(\<^bold>\<forall> z . (\<^bold>\<A>(\<phi> z) \<^bold>\<equiv> (z \<^bold>= \<alpha>))) in v]"
          using UniqueAux "\<^bold>&E"(1) by auto
        hence "[(\<alpha>\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<phi> x) in v] \<and> [\<psi> (\<alpha>\<^sup>P) in v]"
          using descriptions[axiom_instance, equiv_rl]
                4[conj2] by blast
        hence "[?lhs in v]"
          using l_identity[axiom_instance, deduction,
                           deduction]
          by fast
      }
      ultimately show ?thesis by PLM_solver
    qed

  lemma actual_desc_1[PLM]:
    "[(\<^bold>\<exists> y . (y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<equiv> (\<^bold>\<exists>! x . \<^bold>\<A>(\<phi> x)) in v]" (is "[?lhs \<^bold>\<equiv> ?rhs in v]")
    proof -
      {
        assume "[?lhs in v]"
        then obtain \<alpha> where
          "[((\<alpha>\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x)) in v]"
          by (rule "\<^bold>\<exists>E")
        hence "[\<lparr>A!,(\<^bold>\<iota>x. \<phi> x)\<rparr> in v] \<or> [(\<alpha>\<^sup>P) \<^bold>=\<^sub>E (\<^bold>\<iota>x. \<phi> x) in v]"
          apply - unfolding identity_defs by PLM_solver
        then obtain x where
          "[((\<^bold>\<A>\<phi> x \<^bold>& (\<^bold>\<forall> z . \<^bold>\<A>(\<phi> z) \<^bold>\<rightarrow> z \<^bold>= x))) in v]"
          using nec_russell_axiom[where \<psi>="\<lambda>x . \<lparr>A!,x\<rparr>", equiv_lr, THEN "\<^bold>\<exists>E"]
          using nec_russell_axiom[where \<psi>="\<lambda>x . (\<alpha>\<^sup>P) \<^bold>=\<^sub>E x", equiv_lr, THEN "\<^bold>\<exists>E"]
          using SimpleExOrEnc.intros unfolding identity\<^sub>E_infix_def
          by (meson "\<^bold>&E")
        hence "[?rhs in v]" unfolding exists_unique_def by (rule "\<^bold>\<exists>I")
      }
      moreover {
        assume "[?rhs in v]"
        then obtain x where
          "[((\<^bold>\<A>\<phi> x \<^bold>& (\<^bold>\<forall> z . \<^bold>\<A>(\<phi> z) \<^bold>\<rightarrow> z \<^bold>= x))) in v]"
          unfolding exists_unique_def by (rule "\<^bold>\<exists>E")
        hence "[\<^bold>\<forall>z. \<^bold>\<A>\<phi> z \<^bold>\<equiv> z \<^bold>= x in v]"
          using UniqueAux by auto
        hence "[(x\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
          using descriptions[axiom_instance, equiv_rl] by auto
        hence "[?lhs in v]" by (rule "\<^bold>\<exists>I")
      }
      ultimately show ?thesis
        using "\<^bold>\<equiv>I" CP by auto
    qed

  lemma actual_desc_2[PLM]:
    "[(x\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi>) \<^bold>\<rightarrow> \<^bold>\<A>\<phi> in v]"
    using nec_hintikka_scheme[equiv_lr, conj1]
    by (rule CP)

  lemma actual_desc_3[PLM]:
    "[(z\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) \<^bold>\<rightarrow> \<^bold>\<A>(\<phi> z) in v]"
    using nec_hintikka_scheme[equiv_lr, conj1]
    by (rule CP)

  lemma actual_desc_4[PLM]:
    "[(\<^bold>\<exists> y . ((y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> (x\<^sup>P)))) \<^bold>\<rightarrow> \<^bold>\<A>(\<phi> (\<^bold>\<iota>x. \<phi> (x\<^sup>P))) in v]"
    proof (rule CP)
      assume "[(\<^bold>\<exists> y . (y\<^sup>P) \<^bold>= (\<^bold>\<iota>x . \<phi> (x\<^sup>P))) in v]"
      then obtain y where 1:
        "[y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> (x\<^sup>P)) in v]"
        by (rule "\<^bold>\<exists>E")
      hence "[\<^bold>\<A>(\<phi> (y\<^sup>P)) in v]" using actual_desc_3[deduction] by fast
      thus "[\<^bold>\<A>(\<phi> (\<^bold>\<iota>x. \<phi> (x\<^sup>P))) in v]"
        using l_identity[axiom_instance, deduction,
                         deduction] 1 by fast
    qed

  lemma unique_box_desc_1[PLM]:
    "[(\<^bold>\<exists>!x . \<^bold>\<box>(\<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<forall> y . (y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) \<^bold>\<rightarrow> \<phi> y) in v]"
    proof (rule CP)
      assume "[(\<^bold>\<exists>!x . \<^bold>\<box>(\<phi> x)) in v]"
      then obtain \<alpha> where 1:
        "[\<^bold>\<box>\<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<box>(\<phi> \<beta>) \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
        unfolding exists_unique_def by (rule "\<^bold>\<exists>E")
      {
        fix y
        {
          assume "[(y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
          hence "[\<^bold>\<A>\<phi> \<alpha> \<^bold>\<rightarrow> \<alpha> \<^bold>= y in v]"
            using nec_hintikka_scheme[where x="y" and \<phi>="\<phi>", equiv_lr, conj2,
                          THEN cqt_1[where \<alpha>=\<alpha>,axiom_instance, deduction]] by simp
          hence "[\<alpha> \<^bold>= y in v]"
            using 1[conj1] nec_imp_act vdash_properties_10 by blast
          hence "[\<phi> y in v]"
            using 1[conj1] qml_2[axiom_instance, deduction]
                  l_identity[axiom_instance, deduction, deduction]
            by fast
        }
        hence "[(y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) \<^bold>\<rightarrow> \<phi> y in v]"
          by (rule CP)
      }
      thus "[\<^bold>\<forall> y . (y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) \<^bold>\<rightarrow> \<phi> y in v]"
        by (rule "\<^bold>\<forall>I")
    qed

  lemma unique_box_desc[PLM]:
    "[(\<^bold>\<forall> x . (\<phi> x \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> x))) \<^bold>\<rightarrow> ((\<^bold>\<exists>!x . \<phi> x)
      \<^bold>\<rightarrow> (\<^bold>\<forall> y . (y\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> x)) \<^bold>\<rightarrow> \<phi> y)) in v]"
    apply (rule CP, rule CP)
    using nec_exist_unique[deduction, deduction]
          unique_box_desc_1[deduction] by blast

subsection\<open>Necessity\<close>
text\<open>\label{TAO_PLM_Necessity}\<close>

  lemma RM_1[PLM]:
    "(\<And>v.[\<phi> \<^bold>\<rightarrow> \<psi> in v]) \<Longrightarrow> [\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi> in v]"
    using RN qml_1[axiom_instance] vdash_properties_10 by blast

  lemma RM_1_b[PLM]:
    "(\<And>v.[\<chi> in v] \<Longrightarrow> [\<phi> \<^bold>\<rightarrow> \<psi> in v]) \<Longrightarrow> ([\<^bold>\<box>\<chi> in v] \<Longrightarrow> [\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi> in v])"
    using RN_2 qml_1[axiom_instance] vdash_properties_10 by blast

  lemma RM_2[PLM]:
    "(\<And>v.[\<phi> \<^bold>\<rightarrow> \<psi> in v]) \<Longrightarrow> [\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi> in v]"
    unfolding diamond_def
    using RM_1 contraposition_1 by auto

  lemma RM_2_b[PLM]:
    "(\<And>v.[\<chi> in v] \<Longrightarrow> [\<phi> \<^bold>\<rightarrow> \<psi> in v]) \<Longrightarrow> ([\<^bold>\<box>\<chi> in v] \<Longrightarrow> [\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi> in v])"
    unfolding diamond_def
    using RM_1_b contraposition_1 by blast

  lemma KBasic_1[PLM]:
    "[\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>(\<psi> \<^bold>\<rightarrow> \<phi>) in v]"
    by (simp only: pl_1[axiom_instance] RM_1)
  lemma KBasic_2[PLM]:
    "[\<^bold>\<box>(\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
    by (simp only: RM_1 useful_tautologies_3)
  lemma KBasic_3[PLM]:
    "[\<^bold>\<box>(\<phi> \<^bold>& \<psi>) \<^bold>\<equiv> \<^bold>\<box>\<phi> \<^bold>& \<^bold>\<box>\<psi> in v]"
    apply (rule "\<^bold>\<equiv>I")
     apply (rule CP)
     apply (rule "\<^bold>&I")
      using RM_1 oth_class_taut_9_a vdash_properties_6 apply blast
     using RM_1 oth_class_taut_9_b vdash_properties_6 apply blast
    using qml_1[axiom_instance] RM_1 ded_thm_cor_3 oth_class_taut_10_a
          oth_class_taut_8_b vdash_properties_10
    by blast
  lemma KBasic_4[PLM]:
    "[\<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<equiv> (\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>& \<^bold>\<box>(\<psi> \<^bold>\<rightarrow> \<phi>)) in v]"
    apply (rule "\<^bold>\<equiv>I")
     unfolding equiv_def using KBasic_3 PLM.CP "\<^bold>\<equiv>E"(1)
     apply blast
    using KBasic_3 PLM.CP "\<^bold>\<equiv>E"(2)
    by blast
  lemma KBasic_5[PLM]:
    "[(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>& \<^bold>\<box>(\<psi> \<^bold>\<rightarrow> \<phi>)) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<psi>) in v]"
    by (metis qml_1[axiom_instance] CP "\<^bold>&E" "\<^bold>\<equiv>I" vdash_properties_10)
  lemma KBasic_6[PLM]:
    "[\<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<psi>) in v]"
    using KBasic_4 KBasic_5 by (metis equiv_def ded_thm_cor_3 "\<^bold>&E"(1))
  lemma "[(\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<psi>) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
    nitpick[expect=genuine, user_axioms, card = 1, card i = 2]
    oops \<comment> \<open>countermodel as desired\<close>
  lemma KBasic_7[PLM]:
    "[(\<^bold>\<box>\<phi> \<^bold>& \<^bold>\<box>\<psi>) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
    proof (rule CP)
      assume "[\<^bold>\<box>\<phi> \<^bold>& \<^bold>\<box>\<psi> in v]"
      hence "[\<^bold>\<box>(\<psi> \<^bold>\<rightarrow> \<phi>) in v] \<and> [\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
        using "\<^bold>&E" KBasic_1 vdash_properties_10 by blast
      thus "[\<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
        using KBasic_4 "\<^bold>\<equiv>E"(2) intro_elim_1 by blast
    qed

  lemma KBasic_8[PLM]:
    "[\<^bold>\<box>(\<phi> \<^bold>& \<psi>) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
    using KBasic_7 KBasic_3
    by (metis equiv_def PLM.ded_thm_cor_3 "\<^bold>&E"(1))
  lemma KBasic_9[PLM]:
    "[\<^bold>\<box>((\<^bold>\<not>\<phi>) \<^bold>& (\<^bold>\<not>\<psi>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
    proof (rule CP)
      assume "[\<^bold>\<box>((\<^bold>\<not>\<phi>) \<^bold>& (\<^bold>\<not>\<psi>)) in v]"
      hence "[\<^bold>\<box>((\<^bold>\<not>\<phi>) \<^bold>\<equiv> (\<^bold>\<not>\<psi>)) in v]"
        using KBasic_8 vdash_properties_10 by blast
      moreover have "\<And>v.[((\<^bold>\<not>\<phi>) \<^bold>\<equiv> (\<^bold>\<not>\<psi>)) \<^bold>\<rightarrow> (\<phi> \<^bold>\<equiv> \<psi>) in v]"
        using CP "\<^bold>\<equiv>E"(2) oth_class_taut_5_d by blast
      ultimately show "[\<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
        using RM_1 PLM.vdash_properties_10 by blast
    qed

  lemma rule_sub_lem_1_a[PLM]:
    "[\<^bold>\<box>(\<psi> \<^bold>\<equiv> \<chi>) in v] \<Longrightarrow> [(\<^bold>\<not>\<psi>) \<^bold>\<equiv> (\<^bold>\<not>\<chi>) in v]"
    using qml_2[axiom_instance] "\<^bold>\<equiv>E"(1) oth_class_taut_5_d
          vdash_properties_10
    by blast
  lemma rule_sub_lem_1_b[PLM]:
    "[\<^bold>\<box>(\<psi> \<^bold>\<equiv> \<chi>) in v] \<Longrightarrow> [(\<psi> \<^bold>\<rightarrow> \<Theta>) \<^bold>\<equiv> (\<chi> \<^bold>\<rightarrow> \<Theta>) in v]"
    by (metis equiv_def contraposition_1 CP "\<^bold>&E"(2) "\<^bold>\<equiv>I"
              "\<^bold>\<equiv>E"(1) rule_sub_lem_1_a)
  lemma rule_sub_lem_1_c[PLM]:
    "[\<^bold>\<box>(\<psi> \<^bold>\<equiv> \<chi>) in v] \<Longrightarrow> [(\<Theta> \<^bold>\<rightarrow> \<psi>) \<^bold>\<equiv> (\<Theta> \<^bold>\<rightarrow> \<chi>) in v]"
    by (metis CP "\<^bold>\<equiv>I" "\<^bold>\<equiv>E"(3) "\<^bold>\<equiv>E"(4) "\<^bold>\<not>\<^bold>\<not>I"
              "\<^bold>\<not>\<^bold>\<not>E" rule_sub_lem_1_a)
  lemma rule_sub_lem_1_d[PLM]:
    "(\<And>x.[\<^bold>\<box>(\<psi> x \<^bold>\<equiv> \<chi> x) in v]) \<Longrightarrow> [(\<^bold>\<forall>\<alpha>. \<psi> \<alpha>) \<^bold>\<equiv> (\<^bold>\<forall>\<alpha>. \<chi> \<alpha>) in v]" 
    by (metis equiv_def "\<^bold>\<forall>I" CP "\<^bold>&E" "\<^bold>\<equiv>I" raa_cor_1
              vdash_properties_10 rule_sub_lem_1_a "\<^bold>\<forall>E")
  lemma rule_sub_lem_1_e[PLM]:
    "[\<^bold>\<box>(\<psi> \<^bold>\<equiv> \<chi>) in v] \<Longrightarrow> [\<^bold>\<A>\<psi> \<^bold>\<equiv> \<^bold>\<A>\<chi> in v]"
    using Act_Basic_5 "\<^bold>\<equiv>E"(1) nec_imp_act
          vdash_properties_10
    by blast
  lemma rule_sub_lem_1_f[PLM]:
    "[\<^bold>\<box>(\<psi> \<^bold>\<equiv> \<chi>) in v] \<Longrightarrow> [\<^bold>\<box>\<psi> \<^bold>\<equiv> \<^bold>\<box>\<chi> in v]" 
    using KBasic_6 "\<^bold>\<equiv>I" "\<^bold>\<equiv>E"(1) vdash_properties_9
    by blast


  named_theorems Substable_intros
  
  definition Substable :: "('a\<Rightarrow>'a\<Rightarrow>bool)\<Rightarrow>('a\<Rightarrow>\<o>) \<Rightarrow> bool"
    where "Substable \<equiv> (\<lambda> cond \<phi> . \<forall> \<psi> \<chi> v . (cond \<psi> \<chi>) \<longrightarrow> [\<phi> \<psi> \<^bold>\<equiv> \<phi> \<chi> in v])"
  
  lemma Substable_intro_const[Substable_intros]:
    "Substable cond (\<lambda> \<phi> . \<Theta>)"
    unfolding Substable_def using oth_class_taut_4_a by blast

  lemma Substable_intro_not[Substable_intros]:
    assumes "Substable cond \<psi>"
    shows "Substable cond (\<lambda> \<phi> . \<^bold>\<not>(\<psi> \<phi>))"
    using assms unfolding Substable_def
    using rule_sub_lem_1_a RN_2 "\<^bold>\<equiv>E" oth_class_taut_5_d by metis
  lemma Substable_intro_impl[Substable_intros]:
    assumes "Substable cond \<psi>"
        and "Substable cond \<chi>"
    shows "Substable cond (\<lambda> \<phi> . \<psi> \<phi> \<^bold>\<rightarrow> \<chi> \<phi>)"
    using assms unfolding Substable_def
    by (metis "\<^bold>\<equiv>I" CP intro_elim_6_a intro_elim_6_b)
  lemma Substable_intro_box[Substable_intros]:
    assumes "Substable cond \<psi>"
    shows "Substable cond (\<lambda> \<phi> . \<^bold>\<box>(\<psi> \<phi>))"
    using assms unfolding Substable_def
    using rule_sub_lem_1_f RN by meson
  lemma Substable_intro_actual[Substable_intros]:
    assumes "Substable cond \<psi>"
    shows "Substable cond (\<lambda> \<phi> . \<^bold>\<A>(\<psi> \<phi>))"
    using assms unfolding Substable_def
    using rule_sub_lem_1_e RN by meson
  lemma Substable_intro_all[Substable_intros]:
    assumes "\<forall> x . Substable cond (\<psi> x)"
    shows "Substable cond (\<lambda> \<phi> . \<^bold>\<forall> x . \<psi> x \<phi>)"
    using assms unfolding Substable_def
    by (simp add: RN rule_sub_lem_1_d)

  named_theorems Substable_Cond_defs
end

class Substable =
  fixes Substable_Cond :: "'a\<Rightarrow>'a\<Rightarrow>bool"
  assumes rule_sub_nec:
    "\<And> \<phi> \<psi> \<chi> \<Theta> v . \<lbrakk>PLM.Substable Substable_Cond \<phi>; Substable_Cond \<psi> \<chi>\<rbrakk>
      \<Longrightarrow> \<Theta> [\<phi> \<psi> in v] \<Longrightarrow> \<Theta> [\<phi> \<chi> in v]"

instantiation \<o> :: Substable
begin
  definition Substable_Cond_\<o> where [PLM.Substable_Cond_defs]:
    "Substable_Cond_\<o> \<equiv> \<lambda> \<phi> \<psi> . \<forall> v . [\<phi> \<^bold>\<equiv> \<psi> in v]"
  instance proof
    interpret PLM .
    fix \<phi> :: "\<o> \<Rightarrow> \<o>" and  \<psi> \<chi> :: \<o> and \<Theta> :: "bool \<Rightarrow> bool" and v::i
    assume "Substable Substable_Cond \<phi>"
    moreover assume "Substable_Cond \<psi> \<chi>"
    ultimately have "[\<phi> \<psi> \<^bold>\<equiv> \<phi> \<chi> in v]"
    unfolding Substable_def by blast
    hence "[\<phi> \<psi> in v] = [\<phi> \<chi> in v]" using "\<^bold>\<equiv>E" by blast
    moreover assume "\<Theta> [\<phi> \<psi> in v]"
    ultimately show "\<Theta> [\<phi> \<chi> in v]" by simp
  qed
end

instantiation "fun" :: (type, Substable) Substable
begin
  definition Substable_Cond_fun where [PLM.Substable_Cond_defs]:
    "Substable_Cond_fun \<equiv> \<lambda> \<phi> \<psi> . \<forall> x . Substable_Cond (\<phi> x) (\<psi> x)"
  instance proof
    interpret PLM .
    fix \<phi>:: "('a \<Rightarrow> 'b) \<Rightarrow> \<o>" and  \<psi> \<chi> :: "'a \<Rightarrow> 'b" and \<Theta> v
    assume "Substable Substable_Cond \<phi>"
    moreover assume "Substable_Cond \<psi> \<chi>"
    ultimately have "[\<phi> \<psi> \<^bold>\<equiv> \<phi> \<chi> in v]"
      unfolding Substable_def by blast
    hence "[\<phi> \<psi> in v] = [\<phi> \<chi> in v]" using "\<^bold>\<equiv>E" by blast
    moreover assume "\<Theta> [\<phi> \<psi> in v]"
    ultimately show "\<Theta> [\<phi> \<chi> in v]" by simp
  qed
end

context PLM
begin

  lemma Substable_intro_equiv[Substable_intros]:
    assumes "Substable cond \<psi>"
        and "Substable cond \<chi>"
    shows "Substable cond (\<lambda> \<phi> . \<psi> \<phi> \<^bold>\<equiv> \<chi> \<phi>)"
    unfolding conn_defs by (simp add: assms Substable_intros)
  lemma Substable_intro_conj[Substable_intros]:
    assumes "Substable cond \<psi>"
        and "Substable cond \<chi>"
    shows "Substable cond (\<lambda> \<phi> . \<psi> \<phi> \<^bold>& \<chi> \<phi>)"
    unfolding conn_defs by (simp add: assms Substable_intros)
  lemma Substable_intro_disj[Substable_intros]:
    assumes "Substable cond \<psi>"
        and "Substable cond \<chi>"
    shows "Substable cond (\<lambda> \<phi> . \<psi> \<phi> \<^bold>\<or> \<chi> \<phi>)"
    unfolding conn_defs by (simp add: assms Substable_intros)
  lemma Substable_intro_diamond[Substable_intros]:
    assumes "Substable cond \<psi>"
    shows "Substable cond (\<lambda> \<phi> . \<^bold>\<diamond>(\<psi> \<phi>))"
    unfolding conn_defs by (simp add: assms Substable_intros)
  lemma Substable_intro_exist[Substable_intros]:
    assumes "\<forall> x . Substable cond (\<psi> x)"
    shows "Substable cond (\<lambda> \<phi> . \<^bold>\<exists> x . \<psi> x \<phi>)"
    unfolding conn_defs by (simp add: assms Substable_intros)

  lemma Substable_intro_id_\<o>[Substable_intros]:
    "Substable Substable_Cond (\<lambda> \<phi> . \<phi>)"
    unfolding Substable_def Substable_Cond_\<o>_def by blast
  lemma Substable_intro_id_fun[Substable_intros]:
    assumes "Substable Substable_Cond \<psi>"
    shows "Substable Substable_Cond (\<lambda> \<phi> . \<psi> (\<phi> x))"
    using assms unfolding Substable_def Substable_Cond_fun_def
    by blast

  method PLM_subst_method for \<psi>::"'a::Substable" and \<chi>::"'a::Substable" =
    (match conclusion in "\<Theta> [\<phi> \<chi> in v]" for \<Theta> and \<phi> and v \<Rightarrow>
      \<open>(rule rule_sub_nec[where \<Theta>=\<Theta> and \<chi>=\<chi> and \<psi>=\<psi> and \<phi>=\<phi> and v=v],
        ((fast intro: Substable_intros, ((assumption)+)?)+; fail),
        unfold Substable_Cond_defs)\<close>)

  method PLM_autosubst =
    (match premises in "\<And>v . [\<psi> \<^bold>\<equiv> \<chi> in v]" for \<psi> and \<chi> \<Rightarrow>
      \<open> match conclusion in "\<Theta> [\<phi> \<chi> in v]" for \<Theta> \<phi> and v \<Rightarrow>
        \<open>(rule rule_sub_nec[where \<Theta>=\<Theta> and \<chi>=\<chi> and \<psi>=\<psi> and \<phi>=\<phi> and v=v],
          ((fast intro: Substable_intros, ((assumption)+)?)+; fail),
          unfold Substable_Cond_defs)\<close> \<close>)

  method PLM_autosubst1 =
    (match premises in "\<And>v x . [\<psi> x \<^bold>\<equiv> \<chi> x in v]"
      for \<psi>::"'a::type\<Rightarrow>\<o>" and \<chi>::"'a\<Rightarrow>\<o>" \<Rightarrow>
      \<open> match conclusion in "\<Theta> [\<phi> \<chi> in v]" for \<Theta> \<phi> and v \<Rightarrow>
        \<open>(rule rule_sub_nec[where \<Theta>=\<Theta> and \<chi>=\<chi> and \<psi>=\<psi> and \<phi>=\<phi> and v=v],
          ((fast intro: Substable_intros, ((assumption)+)?)+; fail),
          unfold Substable_Cond_defs)\<close> \<close>)

  method PLM_autosubst2 =
    (match premises in "\<And>v x y . [\<psi> x y \<^bold>\<equiv> \<chi> x y in v]"
      for \<psi>::"'a::type\<Rightarrow>'a\<Rightarrow>\<o>" and \<chi>::"'a::type\<Rightarrow>'a\<Rightarrow>\<o>" \<Rightarrow>
      \<open> match conclusion in "\<Theta> [\<phi> \<chi> in v]" for \<Theta> \<phi> and v \<Rightarrow>
        \<open>(rule rule_sub_nec[where \<Theta>=\<Theta> and \<chi>=\<chi> and \<psi>=\<psi> and \<phi>=\<phi> and v=v],
          ((fast intro: Substable_intros, ((assumption)+)?)+; fail),
          unfold Substable_Cond_defs)\<close> \<close>)

  method PLM_subst_goal_method for \<phi>::"'a::Substable\<Rightarrow>\<o>" and \<psi>::"'a" =
    (match conclusion in "\<Theta> [\<phi> \<chi> in v]" for \<Theta> and \<chi> and v \<Rightarrow>
      \<open>(rule rule_sub_nec[where \<Theta>=\<Theta> and \<chi>=\<chi> and \<psi>=\<psi> and \<phi>=\<phi> and v=v],
        ((fast intro: Substable_intros, ((assumption)+)?)+; fail),
        unfold Substable_Cond_defs)\<close>)

(*
  text{* \begin{TODO}
            This can only be proven using the Semantics of the Box operator.
            As it is not needed for the further reasoning it remains commented for now.
         \end{TODO} *}
  lemma rule_sub_lem_2:
    assumes "Substable Substable_Cond \<phi>"
    shows "[\<^bold>\<box>(\<psi> \<^bold>\<equiv> \<chi>) in v] \<Longrightarrow> [\<phi> \<psi> \<^bold>\<equiv> \<phi> \<chi> in v]"
    using assms unfolding Substable_def Substable_Cond_defs
    using Semantics.T6 by fast
*)

  lemma rule_sub_nec[PLM]:
    assumes "Substable Substable_Cond \<phi>"
    shows "(\<And>v.[(\<psi> \<^bold>\<equiv> \<chi>) in v]) \<Longrightarrow> \<Theta> [\<phi> \<psi> in v] \<Longrightarrow> \<Theta> [\<phi> \<chi> in v]"
    proof -
      assume "(\<And>v.[(\<psi> \<^bold>\<equiv> \<chi>) in v])"
      hence "[\<phi> \<psi> in v] = [\<phi> \<chi> in v]"
        using assms RN unfolding Substable_def Substable_Cond_defs
        using "\<^bold>\<equiv>I" CP "\<^bold>\<equiv>E"(1) "\<^bold>\<equiv>E"(2) by meson
      thus "\<Theta> [\<phi> \<psi> in v] \<Longrightarrow> \<Theta> [\<phi> \<chi> in v]" by auto
    qed

  lemma rule_sub_nec1[PLM]:
    assumes "Substable Substable_Cond \<phi>"
    shows "(\<And>v x .[(\<psi> x \<^bold>\<equiv> \<chi> x) in v]) \<Longrightarrow> \<Theta> [\<phi> \<psi> in v] \<Longrightarrow> \<Theta> [\<phi> \<chi> in v]"
    proof -
      assume "(\<And>v x.[(\<psi> x \<^bold>\<equiv> \<chi> x) in v])"
      hence "[\<phi> \<psi> in v] = [\<phi> \<chi> in v]"
        using assms RN unfolding Substable_def Substable_Cond_defs
        using "\<^bold>\<equiv>I" CP "\<^bold>\<equiv>E"(1) "\<^bold>\<equiv>E"(2) by metis
      thus "\<Theta> [\<phi> \<psi> in v] \<Longrightarrow> \<Theta> [\<phi> \<chi> in v]" by auto
    qed

  lemma rule_sub_nec2[PLM]:
    assumes "Substable Substable_Cond \<phi>"
    shows "(\<And>v x y .[\<psi> x y \<^bold>\<equiv> \<chi> x y in v]) \<Longrightarrow> \<Theta> [\<phi> \<psi> in v] \<Longrightarrow> \<Theta> [\<phi> \<chi> in v]"
    proof -
      assume "(\<And>v x y .[\<psi> x y \<^bold>\<equiv> \<chi> x y in v])"
      hence "[\<phi> \<psi> in v] = [\<phi> \<chi> in v]"
        using assms RN unfolding Substable_def Substable_Cond_defs
        using "\<^bold>\<equiv>I" CP "\<^bold>\<equiv>E"(1) "\<^bold>\<equiv>E"(2) by metis
      thus "\<Theta> [\<phi> \<psi> in v] \<Longrightarrow> \<Theta> [\<phi> \<chi> in v]" by auto
    qed

  lemma rule_sub_remark_1_autosubst:
    assumes "(\<And>v.[\<lparr>A!,x\<rparr> \<^bold>\<equiv> (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<rparr>)) in v])"
        and "[\<^bold>\<not>\<lparr>A!,x\<rparr> in v]"
    shows"[\<^bold>\<not>\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr> in v]"
    apply (insert assms) apply PLM_autosubst by auto

  lemma rule_sub_remark_1:
    assumes "(\<And>v.[\<lparr>A!,x\<rparr> \<^bold>\<equiv> (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<rparr>)) in v])"
        and "[\<^bold>\<not>\<lparr>A!,x\<rparr> in v]"
      shows"[\<^bold>\<not>\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<rparr> in v]"
    apply (PLM_subst_method "\<lparr>A!,x\<rparr>" "(\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<rparr>))")
     apply (simp add: assms(1))
    by (simp add: assms(2))

  lemma rule_sub_remark_2:
    assumes "(\<And>v.[\<lparr>R,x,y\<rparr> \<^bold>\<equiv> (\<lparr>R,x,y\<rparr> \<^bold>& (\<lparr>Q,a\<rparr> \<^bold>\<or> (\<^bold>\<not>\<lparr>Q,a\<rparr>))) in v])"
        and "[p \<^bold>\<rightarrow> \<lparr>R,x,y\<rparr> in v]"
    shows"[p \<^bold>\<rightarrow> (\<lparr>R,x,y\<rparr> \<^bold>& (\<lparr>Q,a\<rparr> \<^bold>\<or> (\<^bold>\<not>\<lparr>Q,a\<rparr>)))  in v]"
    apply (insert assms) apply PLM_autosubst by auto

  lemma rule_sub_remark_3_autosubst:
    assumes "(\<And>v x.[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>\<equiv> (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>)) in v])"
        and "[\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr> in v]"
    shows"[\<^bold>\<exists> x . (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>))  in v]"
    apply (insert assms) apply PLM_autosubst1 by auto

  lemma rule_sub_remark_3:
    assumes "(\<And>v x.[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>\<equiv> (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>)) in v])"
        and "[\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr> in v]"
    shows "[\<^bold>\<exists> x . (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>))  in v]"
    apply (PLM_subst_method "\<lambda>x . \<lparr>A!,x\<^sup>P\<rparr>" "\<lambda>x . (\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>))")
     apply (simp add: assms(1))
    by (simp add: assms(2))

  lemma rule_sub_remark_4:
    assumes "\<And>v x.[(\<^bold>\<not>(\<^bold>\<not>\<lparr>P,x\<^sup>P\<rparr>)) \<^bold>\<equiv> \<lparr>P,x\<^sup>P\<rparr> in v]"
        and "[\<^bold>\<A>(\<^bold>\<not>(\<^bold>\<not>\<lparr>P,x\<^sup>P\<rparr>)) in v]"
    shows "[\<^bold>\<A>\<lparr>P,x\<^sup>P\<rparr> in v]"
    apply (insert assms) apply PLM_autosubst1 by auto

  lemma rule_sub_remark_5:
    assumes "\<And>v.[(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<equiv> ((\<^bold>\<not>\<psi>) \<^bold>\<rightarrow> (\<^bold>\<not>\<phi>)) in v]"
        and "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
    shows "[\<^bold>\<box>((\<^bold>\<not>\<psi>) \<^bold>\<rightarrow> (\<^bold>\<not>\<phi>)) in v]"
    apply (insert assms) apply PLM_autosubst by auto

  lemma rule_sub_remark_6:
    assumes "\<And>v.[\<psi> \<^bold>\<equiv> \<chi> in v]"
        and "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
    shows "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<chi>) in v]"
    apply (insert assms) apply PLM_autosubst by auto

  lemma rule_sub_remark_7:
    assumes "\<And>v.[\<phi> \<^bold>\<equiv> (\<^bold>\<not>(\<^bold>\<not>\<phi>)) in v]"
        and "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<phi>) in v]"
    shows "[\<^bold>\<box>((\<^bold>\<not>(\<^bold>\<not>\<phi>)) \<^bold>\<rightarrow> \<phi>) in v]"
    apply (insert assms) apply PLM_autosubst by auto

  lemma rule_sub_remark_8:
    assumes "\<And>v.[\<^bold>\<A>\<phi> \<^bold>\<equiv> \<phi> in v]"
        and "[\<^bold>\<box>(\<^bold>\<A>\<phi>) in v]"
    shows "[\<^bold>\<box>(\<phi>) in v]"
    apply (insert assms) apply PLM_autosubst by auto

  lemma rule_sub_remark_9:
    assumes "\<And>v.[\<lparr>P,a\<rparr> \<^bold>\<equiv> (\<lparr>P,a\<rparr> \<^bold>& (\<lparr>Q,b\<rparr> \<^bold>\<or> (\<^bold>\<not>\<lparr>Q,b\<rparr>))) in v]"
        and "[\<lparr>P,a\<rparr> \<^bold>= \<lparr>P,a\<rparr> in v]"
    shows "[\<lparr>P,a\<rparr> \<^bold>= (\<lparr>P,a\<rparr> \<^bold>& (\<lparr>Q,b\<rparr> \<^bold>\<or> (\<^bold>\<not>\<lparr>Q,b\<rparr>))) in v]"
      unfolding identity_defs apply (insert assms)
      apply PLM_autosubst oops \<comment> \<open>no match as desired\<close>

  \<comment> \<open>@{text "dr_alphabetic_rules"} implicitly holds\<close>
  \<comment> \<open>@{text "dr_alphabetic_thm"} implicitly holds\<close>

  lemma KBasic2_1[PLM]:
    "[\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<box>(\<^bold>\<not>(\<^bold>\<not>\<phi>)) in v]"
    apply (PLM_subst_method "\<phi>" "(\<^bold>\<not>(\<^bold>\<not>\<phi>))")
     by PLM_solver+

  lemma KBasic2_2[PLM]:
    "[(\<^bold>\<not>(\<^bold>\<box>\<phi>)) \<^bold>\<equiv> \<^bold>\<diamond>(\<^bold>\<not>\<phi>) in v]"
    unfolding diamond_def
    apply (PLM_subst_method "\<phi>" "\<^bold>\<not>(\<^bold>\<not>\<phi>)")
     by PLM_solver+

  lemma KBasic2_3[PLM]:
    "[\<^bold>\<box>\<phi> \<^bold>\<equiv> (\<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<not>\<phi>))) in v]"
    unfolding diamond_def
    apply (PLM_subst_method "\<phi>" "\<^bold>\<not>(\<^bold>\<not>\<phi>)")
     apply PLM_solver
    by (simp add: oth_class_taut_4_b)
  lemmas "Df\<^bold>\<box>" = KBasic2_3

  lemma KBasic2_4[PLM]:
    "[\<^bold>\<box>(\<^bold>\<not>(\<phi>)) \<^bold>\<equiv> (\<^bold>\<not>(\<^bold>\<diamond>\<phi>)) in v]"
    unfolding diamond_def
    by (simp add: oth_class_taut_4_b)

  lemma KBasic2_5[PLM]:
    "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi>) in v]"
    by (simp only: CP RM_2_b)
  lemmas "K\<^bold>\<diamond>" = KBasic2_5

  lemma KBasic2_6[PLM]:
    "[\<^bold>\<diamond>(\<phi> \<^bold>\<or> \<psi>) \<^bold>\<equiv> (\<^bold>\<diamond>\<phi> \<^bold>\<or> \<^bold>\<diamond>\<psi>) in v]"
    proof -
      have "[\<^bold>\<box>((\<^bold>\<not>\<phi>) \<^bold>& (\<^bold>\<not>\<psi>)) \<^bold>\<equiv> (\<^bold>\<box>(\<^bold>\<not>\<phi>) \<^bold>& \<^bold>\<box>(\<^bold>\<not>\<psi>)) in v]"
        using KBasic_3 by blast
      hence "[(\<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<not>((\<^bold>\<not>\<phi>) \<^bold>& (\<^bold>\<not>\<psi>))))) \<^bold>\<equiv> (\<^bold>\<box>(\<^bold>\<not>\<phi>) \<^bold>& \<^bold>\<box>(\<^bold>\<not>\<psi>)) in v]"
        using "Df\<^bold>\<box>" by (rule "\<^bold>\<equiv>E"(6))
      hence "[(\<^bold>\<not>(\<^bold>\<diamond>(\<^bold>\<not>((\<^bold>\<not>\<phi>) \<^bold>& (\<^bold>\<not>\<psi>))))) \<^bold>\<equiv> ((\<^bold>\<not>(\<^bold>\<diamond>\<phi>)) \<^bold>& (\<^bold>\<not>(\<^bold>\<diamond>\<psi>))) in v]"
        apply - apply (PLM_subst_method "\<^bold>\<box>(\<^bold>\<not>\<phi>)" "\<^bold>\<not>(\<^bold>\<diamond>\<phi>)")
         apply (simp add: KBasic2_4)
        apply (PLM_subst_method "\<^bold>\<box>(\<^bold>\<not>\<psi>)" "\<^bold>\<not>(\<^bold>\<diamond>\<psi>)")
         apply (simp add: KBasic2_4)
        unfolding diamond_def by assumption
      hence "[(\<^bold>\<not>(\<^bold>\<diamond>(\<phi> \<^bold>\<or> \<psi>))) \<^bold>\<equiv> ((\<^bold>\<not>(\<^bold>\<diamond>\<phi>)) \<^bold>& (\<^bold>\<not>(\<^bold>\<diamond>\<psi>))) in v]"
        apply - apply (PLM_subst_method "\<^bold>\<not>((\<^bold>\<not>\<phi>) \<^bold>& (\<^bold>\<not>\<psi>))" "\<phi> \<^bold>\<or> \<psi>")
        using oth_class_taut_6_b[equiv_sym] by auto
      hence "[(\<^bold>\<not>(\<^bold>\<not>(\<^bold>\<diamond>(\<phi> \<^bold>\<or> \<psi>)))) \<^bold>\<equiv> (\<^bold>\<not>((\<^bold>\<not>(\<^bold>\<diamond>\<phi>))\<^bold>&(\<^bold>\<not>(\<^bold>\<diamond>\<psi>)))) in v]"
        by (rule oth_class_taut_5_d[equiv_lr])
      hence "[\<^bold>\<diamond>(\<phi> \<^bold>\<or> \<psi>) \<^bold>\<equiv> (\<^bold>\<not>((\<^bold>\<not>(\<^bold>\<diamond>\<phi>)) \<^bold>& (\<^bold>\<not>(\<^bold>\<diamond>\<psi>)))) in v]"
        apply - apply (PLM_subst_method "\<^bold>\<not>(\<^bold>\<not>(\<^bold>\<diamond>(\<phi> \<^bold>\<or> \<psi>)))" "\<^bold>\<diamond>(\<phi> \<^bold>\<or> \<psi>)")
        using oth_class_taut_4_b[equiv_sym] by auto
      thus ?thesis
        apply - apply (PLM_subst_method "\<^bold>\<not>((\<^bold>\<not>(\<^bold>\<diamond>\<phi>)) \<^bold>& (\<^bold>\<not>(\<^bold>\<diamond>\<psi>)))" "(\<^bold>\<diamond>\<phi>) \<^bold>\<or> (\<^bold>\<diamond>\<psi>)")
        using oth_class_taut_6_b[equiv_sym] by auto
    qed

  lemma KBasic2_7[PLM]:
    "[(\<^bold>\<box>\<phi> \<^bold>\<or> \<^bold>\<box>\<psi>) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<or> \<psi>) in v]"
    proof -
      have "\<And> v . [\<phi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<or> \<psi>) in v]"
        by (metis contraposition_1 contraposition_2 useful_tautologies_3 disj_def)
      hence "[\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<or> \<psi>) in v]" using RM_1 by auto
      moreover {
          have "\<And> v . [\<psi> \<^bold>\<rightarrow> (\<phi> \<^bold>\<or> \<psi>) in v]"
            by (simp only: pl_1[axiom_instance] disj_def)
          hence "[\<^bold>\<box>\<psi> \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<or> \<psi>) in v]"
            using RM_1 by auto
      }
      ultimately show ?thesis
        using oth_class_taut_10_d vdash_properties_10 by blast
    qed

  lemma KBasic2_8[PLM]:
    "[\<^bold>\<diamond>(\<phi> \<^bold>& \<psi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<phi> \<^bold>& \<^bold>\<diamond>\<psi>) in v]"
    by (metis CP RM_2 "\<^bold>&I" oth_class_taut_9_a
              oth_class_taut_9_b vdash_properties_10)

  lemma KBasic2_9[PLM]:
    "[\<^bold>\<diamond>(\<phi> \<^bold>\<rightarrow> \<psi>) \<^bold>\<equiv> (\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi>) in v]"
    apply (PLM_subst_method "(\<^bold>\<not>(\<^bold>\<box>\<phi>)) \<^bold>\<or> (\<^bold>\<diamond>\<psi>)" "\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<psi>")
     using oth_class_taut_5_k[equiv_sym] apply simp
    apply (PLM_subst_method "(\<^bold>\<not>\<phi>) \<^bold>\<or> \<psi>" "\<phi> \<^bold>\<rightarrow> \<psi>")
     using oth_class_taut_5_k[equiv_sym] apply simp
    apply (PLM_subst_method "\<^bold>\<diamond>(\<^bold>\<not>\<phi>)" "\<^bold>\<not>(\<^bold>\<box>\<phi>)")
     using KBasic2_2[equiv_sym] apply simp
    using KBasic2_6 .

  lemma KBasic2_10[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<box>\<phi>) \<^bold>\<equiv> (\<^bold>\<not>(\<^bold>\<box>\<^bold>\<diamond>(\<^bold>\<not>\<phi>))) in v]"
    unfolding diamond_def apply (PLM_subst_method "\<phi>" "\<^bold>\<not>\<^bold>\<not>\<phi>")
    using oth_class_taut_4_b oth_class_taut_4_a by auto

  lemma KBasic2_11[PLM]:
    "[\<^bold>\<diamond>\<^bold>\<diamond>\<phi> \<^bold>\<equiv> (\<^bold>\<not>(\<^bold>\<box>\<^bold>\<box>(\<^bold>\<not>\<phi>))) in v]"
    unfolding diamond_def
    apply (PLM_subst_method "\<^bold>\<box>(\<^bold>\<not>\<phi>)" "\<^bold>\<not>(\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not>\<phi>)))")
    using oth_class_taut_4_b oth_class_taut_4_a by auto

  lemma KBasic2_12[PLM]: "[\<^bold>\<box>(\<phi> \<^bold>\<or> \<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<or> \<^bold>\<diamond>\<psi>) in v]"
    proof -
      have "[\<^bold>\<box>(\<psi> \<^bold>\<or> \<phi>) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<not>\<psi>) \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) in v]"
        using CP RM_1_b "\<^bold>\<or>E"(2) by blast
      hence "[\<^bold>\<box>(\<psi> \<^bold>\<or> \<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<psi> \<^bold>\<or> \<^bold>\<box>\<phi>) in v]"
        unfolding diamond_def disj_def
        by (meson CP "\<^bold>\<not>\<^bold>\<not>E" vdash_properties_6)
      thus ?thesis apply -
        apply (PLM_subst_method "(\<^bold>\<diamond>\<psi> \<^bold>\<or> \<^bold>\<box>\<phi>)" "(\<^bold>\<box>\<phi> \<^bold>\<or> \<^bold>\<diamond>\<psi>)")
         apply (simp add: PLM.oth_class_taut_3_e)
        apply (PLM_subst_method "(\<psi> \<^bold>\<or> \<phi>)" "(\<phi> \<^bold>\<or> \<psi>)")
         apply (simp add: PLM.oth_class_taut_3_e)
        by assumption
    qed

  lemma TBasic[PLM]:
    "[\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi> in v]"
    unfolding diamond_def
    apply (subst contraposition_1)
    apply (PLM_subst_method "\<^bold>\<box>\<^bold>\<not>\<phi>" "\<^bold>\<not>\<^bold>\<not>\<^bold>\<box>\<^bold>\<not>\<phi>")
     apply (simp add: PLM.oth_class_taut_4_b)
    using qml_2[where \<phi>="\<^bold>\<not>\<phi>", axiom_instance]
    by simp
  lemmas "T\<^bold>\<diamond>" = TBasic

  lemma S5Basic_1[PLM]:
    "[\<^bold>\<diamond>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi> in v]"
    proof (rule CP)
      assume "[\<^bold>\<diamond>\<^bold>\<box>\<phi> in v]"
      hence "[\<^bold>\<not>\<^bold>\<box>\<^bold>\<diamond>\<^bold>\<not>\<phi> in v]"
        using KBasic2_10[equiv_lr] by simp
      moreover have "[\<^bold>\<diamond>(\<^bold>\<not>\<phi>) \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>(\<^bold>\<not>\<phi>) in v]"
        by (simp add: qml_3[axiom_instance])
      ultimately have "[\<^bold>\<not>\<^bold>\<diamond>\<^bold>\<not>\<phi> in v]"
        by (simp add: PLM.modus_tollens_1)
      thus "[\<^bold>\<box>\<phi> in v]"
        unfolding diamond_def apply -
        apply (PLM_subst_method "\<^bold>\<not>\<^bold>\<not>\<phi>" "\<phi>")
         using oth_class_taut_4_b[equiv_sym] apply simp
        unfolding diamond_def using oth_class_taut_4_b[equiv_rl]
        by simp
    qed
  lemmas "5\<^bold>\<diamond>" = S5Basic_1

  lemma S5Basic_2[PLM]:
    "[\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<diamond>\<^bold>\<box>\<phi> in v]"
    using "5\<^bold>\<diamond>" "T\<^bold>\<diamond>" "\<^bold>\<equiv>I" by blast

  lemma S5Basic_3[PLM]:
    "[\<^bold>\<diamond>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<^bold>\<diamond>\<phi> in v]"
    using qml_3[axiom_instance] qml_2[axiom_instance] "\<^bold>\<equiv>I" by blast

  lemma S5Basic_4[PLM]:
    "[\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<diamond>\<phi> in v]"
    using "T\<^bold>\<diamond>"[deduction, THEN S5Basic_3[equiv_lr]]
    by (rule CP)

  lemma S5Basic_5[PLM]:
    "[\<^bold>\<diamond>\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<phi> in v]"
    using S5Basic_2[equiv_rl, THEN qml_2[axiom_instance, deduction]]
    by (rule CP)
  lemmas "B\<^bold>\<diamond>" = S5Basic_5

  lemma S5Basic_6[PLM]:
    "[\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<^bold>\<box>\<phi> in v]"
    using S5Basic_4[deduction] RM_1[OF S5Basic_1, deduction] CP by auto
  lemmas "4\<^bold>\<box>" = S5Basic_6

  lemma S5Basic_7[PLM]:
    "[\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<^bold>\<box>\<phi> in v]"
    using "4\<^bold>\<box>" qml_2[axiom_instance] by (rule "\<^bold>\<equiv>I")

  lemma S5Basic_8[PLM]:
    "[\<^bold>\<diamond>\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi> in v]"
    using S5Basic_6[where \<phi>="\<^bold>\<not>\<phi>", THEN contraposition_1[THEN iffD1], deduction]
          KBasic2_11[equiv_lr] CP unfolding diamond_def by auto
  lemmas "4\<^bold>\<diamond>" = S5Basic_8

  lemma S5Basic_9[PLM]:
    "[\<^bold>\<diamond>\<^bold>\<diamond>\<phi> \<^bold>\<equiv> \<^bold>\<diamond>\<phi> in v]"
    using "4\<^bold>\<diamond>" "T\<^bold>\<diamond>" by (rule "\<^bold>\<equiv>I")

  lemma S5Basic_10[PLM]:
    "[\<^bold>\<box>(\<phi> \<^bold>\<or> \<^bold>\<box>\<psi>) \<^bold>\<equiv> (\<^bold>\<box>\<phi> \<^bold>\<or> \<^bold>\<box>\<psi>) in v]"
    apply (rule "\<^bold>\<equiv>I")
     apply (PLM_subst_goal_method "\<lambda> \<chi> . \<^bold>\<box>(\<phi> \<^bold>\<or> \<^bold>\<box>\<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<or> \<chi>)" "\<^bold>\<diamond>\<^bold>\<box>\<psi>")
      using S5Basic_2[equiv_sym] apply simp
     using KBasic2_12 apply assumption
    apply (PLM_subst_goal_method "\<lambda> \<chi> .(\<^bold>\<box>\<phi> \<^bold>\<or> \<chi>) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<or> \<^bold>\<box>\<psi>)" "\<^bold>\<box>\<^bold>\<box>\<psi>")
     using S5Basic_7[equiv_sym] apply simp
    using KBasic2_7 by auto

  lemma S5Basic_11[PLM]:
    "[\<^bold>\<box>(\<phi> \<^bold>\<or> \<^bold>\<diamond>\<psi>) \<^bold>\<equiv> (\<^bold>\<box>\<phi> \<^bold>\<or> \<^bold>\<diamond>\<psi>) in v]"
    apply (rule "\<^bold>\<equiv>I")
     apply (PLM_subst_goal_method "\<lambda> \<chi> . \<^bold>\<box>(\<phi> \<^bold>\<or> \<^bold>\<diamond>\<psi>) \<^bold>\<rightarrow> (\<^bold>\<box>\<phi> \<^bold>\<or> \<chi>)" "\<^bold>\<diamond>\<^bold>\<diamond>\<psi>")
      using S5Basic_9 apply simp
     using KBasic2_12 apply assumption
    apply (PLM_subst_goal_method "\<lambda> \<chi> .(\<^bold>\<box>\<phi> \<^bold>\<or> \<chi>) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<or> \<^bold>\<diamond>\<psi>)" "\<^bold>\<box>\<^bold>\<diamond>\<psi>")
     using S5Basic_3[equiv_sym] apply simp
    using KBasic2_7 by assumption

  lemma S5Basic_12[PLM]:
    "[\<^bold>\<diamond>(\<phi> \<^bold>& \<^bold>\<diamond>\<psi>) \<^bold>\<equiv> (\<^bold>\<diamond>\<phi> \<^bold>& \<^bold>\<diamond>\<psi>) in v]"
    proof -
      have "[\<^bold>\<box>((\<^bold>\<not>\<phi>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<not>\<psi>)) \<^bold>\<equiv> (\<^bold>\<box>(\<^bold>\<not>\<phi>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<not>\<psi>)) in v]"
        using S5Basic_10 by auto
      hence 1: "[(\<^bold>\<not>\<^bold>\<box>((\<^bold>\<not>\<phi>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<not>\<psi>))) \<^bold>\<equiv> \<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not>\<phi>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<not>\<psi>)) in v]"
        using oth_class_taut_5_d[equiv_lr] by auto
      have 2: "[(\<^bold>\<diamond>(\<^bold>\<not>((\<^bold>\<not>\<phi>) \<^bold>\<or> (\<^bold>\<not>(\<^bold>\<diamond>\<psi>))))) \<^bold>\<equiv> (\<^bold>\<not>((\<^bold>\<not>(\<^bold>\<diamond>\<phi>)) \<^bold>\<or> (\<^bold>\<not>(\<^bold>\<diamond>\<psi>)))) in v]"
        apply (PLM_subst_method "\<^bold>\<box>\<^bold>\<not>\<psi>" "\<^bold>\<not>\<^bold>\<diamond>\<psi>")
         using KBasic2_4 apply simp
        apply (PLM_subst_method "\<^bold>\<box>\<^bold>\<not>\<phi>" "\<^bold>\<not>\<^bold>\<diamond>\<phi>")
         using KBasic2_4 apply simp
        apply (PLM_subst_method "(\<^bold>\<not>\<^bold>\<box>((\<^bold>\<not>\<phi>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<not>\<psi>)))" "(\<^bold>\<diamond>(\<^bold>\<not>((\<^bold>\<not>\<phi>) \<^bold>\<or> (\<^bold>\<box>(\<^bold>\<not>\<psi>)))))")
         unfolding diamond_def
         apply (simp add: RN oth_class_taut_4_b rule_sub_lem_1_a rule_sub_lem_1_f)
        using 1 by assumption
      show ?thesis
        apply (PLM_subst_method "\<^bold>\<not>((\<^bold>\<not>\<phi>) \<^bold>\<or> (\<^bold>\<not>\<^bold>\<diamond>\<psi>))" "\<phi> \<^bold>& \<^bold>\<diamond>\<psi>")
         using oth_class_taut_6_a[equiv_sym] apply simp
        apply (PLM_subst_method "\<^bold>\<not>((\<^bold>\<not>(\<^bold>\<diamond>\<phi>)) \<^bold>\<or> (\<^bold>\<not>\<^bold>\<diamond>\<psi>))" "\<^bold>\<diamond>\<phi> \<^bold>& \<^bold>\<diamond>\<psi>")
         using oth_class_taut_6_a[equiv_sym] apply simp
        using 2 by assumption
    qed

  lemma S5Basic_13[PLM]:
    "[\<^bold>\<diamond>(\<phi> \<^bold>& (\<^bold>\<box>\<psi>)) \<^bold>\<equiv> (\<^bold>\<diamond>\<phi> \<^bold>& (\<^bold>\<box>\<psi>)) in v]"
    apply (PLM_subst_method "\<^bold>\<diamond>\<^bold>\<box>\<psi>" "\<^bold>\<box>\<psi>")
     using S5Basic_2[equiv_sym] apply simp
    using S5Basic_12 by simp

  lemma S5Basic_14[PLM]:
    "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> (\<^bold>\<box>\<psi>)) \<^bold>\<equiv> \<^bold>\<box>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>) in v]"
      moreover {
        have "\<And>v.[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
          proof (rule CP)
            fix v
            assume "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>) in v]"
            hence "[\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<psi> in v]"
              using "K\<^bold>\<diamond>"[deduction] by auto
            thus "[\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi> in v]"
              using "B\<^bold>\<diamond>" ded_thm_cor_3 by blast
          qed
        hence "[\<^bold>\<box>(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi>)) in v]"
          by (rule RN)
        hence "[\<^bold>\<box>(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)) \<^bold>\<rightarrow> \<^bold>\<box>((\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi>)) in v]"
          using qml_1[axiom_instance, deduction] by auto
      }
      ultimately show "[\<^bold>\<box>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
        using S5Basic_6 CP vdash_properties_10 by meson
    next
      assume "[\<^bold>\<box>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
      moreover {
        fix v
        {
          assume "[\<^bold>\<box>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi>) in v]"
          hence 1: "[\<^bold>\<box>\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi> in v]"
            using qml_1[axiom_instance, deduction] by auto
          assume "[\<phi> in v]"
          hence "[\<^bold>\<box>\<^bold>\<diamond>\<phi> in v]"
            using S5Basic_4[deduction] by auto
          hence "[\<^bold>\<box>\<psi> in v]"
            using 1[deduction] by auto
        }
        hence "[\<^bold>\<box>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi>) in v] \<Longrightarrow> [\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi> in v]"
          using CP by auto
      }
      ultimately show "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>) in v]"
        using S5Basic_6 RN_2 vdash_properties_10 by blast
    qed

  lemma sc_eq_box_box_1[PLM]:
    "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) \<^bold>\<rightarrow> (\<^bold>\<diamond>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<phi>) in v]"
    proof(rule CP)
      assume 1: "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) in v]"
      hence "[\<^bold>\<box>(\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<phi>) in v]"
        using S5Basic_14[equiv_lr] by auto
      hence "[\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<phi> in v]"
        using qml_2[axiom_instance, deduction] by auto
      moreover from 1 have "[\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi> in v]"
        using qml_2[axiom_instance, deduction] by auto
      ultimately have "[\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi> in v]"
        using ded_thm_cor_3 by auto
      moreover have "[\<^bold>\<box>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<phi> in v]"
        using qml_2[axiom_instance] "T\<^bold>\<diamond>"
        by (rule ded_thm_cor_3)
      ultimately show "[\<^bold>\<diamond>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<phi> in v]"
        by (rule "\<^bold>\<equiv>I")
    qed

  lemma sc_eq_box_box_2[PLM]:
    "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) \<^bold>\<rightarrow> ((\<^bold>\<not>\<^bold>\<box>\<phi>) \<^bold>\<equiv> (\<^bold>\<box>(\<^bold>\<not>\<phi>))) in v]"
    proof (rule CP)
      assume "[\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) in v]"
      hence "[(\<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>\<phi>)) \<^bold>\<equiv> \<^bold>\<box>\<phi> in v]"
        using sc_eq_box_box_1[deduction] unfolding diamond_def by auto
      thus "[((\<^bold>\<not>\<^bold>\<box>\<phi>) \<^bold>\<equiv> (\<^bold>\<box>(\<^bold>\<not>\<phi>))) in v]"
        by (meson CP "\<^bold>\<equiv>I" "\<^bold>\<equiv>E"(3)
                  "\<^bold>\<equiv>E"(4) "\<^bold>\<not>\<^bold>\<not>I" "\<^bold>\<not>\<^bold>\<not>E")
    qed

  lemma sc_eq_box_box_3[PLM]:
    "[(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) \<^bold>& \<^bold>\<box>(\<psi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)) \<^bold>\<rightarrow> ((\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<psi>) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>)) in v]"
    proof (rule CP)
      assume 1: "[(\<^bold>\<box>(\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<phi>) \<^bold>& \<^bold>\<box>(\<psi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi>)) in v]"
      {
        assume "[\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<psi> in v]"
        hence "[(\<^bold>\<box>\<phi> \<^bold>& \<^bold>\<box>\<psi>) \<^bold>\<or> ((\<^bold>\<not>(\<^bold>\<box>\<phi>)) \<^bold>& (\<^bold>\<not>(\<^bold>\<box>\<psi>))) in v]"
          using oth_class_taut_5_i[equiv_lr] by auto
        moreover {
          assume "[\<^bold>\<box>\<phi> \<^bold>& \<^bold>\<box>\<psi> in v]"
          hence "[\<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
            using KBasic_7[deduction] by auto
        }
        moreover {
          assume "[(\<^bold>\<not>(\<^bold>\<box>\<phi>)) \<^bold>& (\<^bold>\<not>(\<^bold>\<box>\<psi>)) in v]"
          hence "[\<^bold>\<box>(\<^bold>\<not>\<phi>) \<^bold>& \<^bold>\<box>(\<^bold>\<not>\<psi>) in v]"
             using 1 "\<^bold>&E" "\<^bold>&I" sc_eq_box_box_2[deduction, equiv_lr]
             by metis
          hence "[\<^bold>\<box>((\<^bold>\<not>\<phi>) \<^bold>& (\<^bold>\<not>\<psi>)) in v]"
            using KBasic_3[equiv_rl] by auto
          hence "[\<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
            using KBasic_9[deduction] by auto
        }
        ultimately have "[\<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
          using CP "\<^bold>\<or>E"(1) by blast
      }
      thus "[\<^bold>\<box>\<phi> \<^bold>\<equiv> \<^bold>\<box>\<psi> \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<^bold>\<equiv> \<psi>) in v]"
        using CP by auto
    qed

  lemma derived_S5_rules_1_a[PLM]:
    assumes "\<And>v. [\<chi> in v] \<Longrightarrow> [\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi> in v]"
    shows "[\<^bold>\<box>\<chi> in v] \<Longrightarrow> [\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi> in v]"
    proof -
      have "[\<^bold>\<box>\<chi> in v] \<Longrightarrow> [\<^bold>\<box>\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi> in v]"
        using assms RM_1_b by metis
      thus "[\<^bold>\<box>\<chi> in v] \<Longrightarrow> [\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi> in v]"
        using S5Basic_4 vdash_properties_10 CP by metis
    qed

  lemma derived_S5_rules_1_b[PLM]:
    assumes "\<And>v. [\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi> in v]"
    shows "[\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi> in v]"
    using derived_S5_rules_1_a all_self_eq_1 assms by blast

  lemma derived_S5_rules_2_a[PLM]:
    assumes "\<And>v. [\<chi> in v] \<Longrightarrow> [\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi> in v]"
    shows "[\<^bold>\<box>\<chi> in v] \<Longrightarrow> [\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi> in v]"
    proof -
      have "[\<^bold>\<box>\<chi> in v] \<Longrightarrow> [\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>\<psi> in v]"
        using RM_2_b assms by metis
      thus "[\<^bold>\<box>\<chi> in v] \<Longrightarrow> [\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi> in v]"
        using "B\<^bold>\<diamond>" vdash_properties_10 CP by metis
    qed

  lemma derived_S5_rules_2_b[PLM]:
    assumes "\<And>v. [\<phi> \<^bold>\<rightarrow> \<^bold>\<box>\<psi> in v]"
    shows "[\<^bold>\<diamond>\<phi> \<^bold>\<rightarrow> \<psi> in v]"
    using assms derived_S5_rules_2_a all_self_eq_1 by blast

  lemma BFs_1[PLM]: "[(\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<phi> \<alpha>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) in v]"
    proof (rule derived_S5_rules_1_b)
      fix v
      {
        fix \<alpha>
        have "\<And>v.[(\<^bold>\<forall>\<alpha> . \<^bold>\<box>(\<phi> \<alpha>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<alpha>) in v]"
          using cqt_orig_1 by metis
        hence "[\<^bold>\<diamond>(\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<phi> \<alpha>)) \<^bold>\<rightarrow> \<^bold>\<diamond>\<^bold>\<box>(\<phi> \<alpha>) in v]"
          using RM_2 by metis
        moreover have "[\<^bold>\<diamond>\<^bold>\<box>(\<phi> \<alpha>) \<^bold>\<rightarrow> (\<phi> \<alpha>) in v]"
          using "B\<^bold>\<diamond>" by auto
        ultimately have "[\<^bold>\<diamond>(\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<phi> \<alpha>)) \<^bold>\<rightarrow> (\<phi> \<alpha>) in v]"
          using ded_thm_cor_3 by auto
      }
      hence "[\<^bold>\<forall> \<alpha> . \<^bold>\<diamond>(\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<phi> \<alpha>)) \<^bold>\<rightarrow> (\<phi> \<alpha>) in v]"
        using "\<^bold>\<forall>I" by metis
      thus "[\<^bold>\<diamond>(\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<phi> \<alpha>)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) in v]"
        using cqt_orig_2[deduction] by auto
    qed
  lemmas BF = BFs_1

  lemma BFs_2[PLM]:
    "[\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<phi> \<alpha>)) in v]"
    proof -
      {
        fix \<alpha>
        {
           fix v
           have "[(\<^bold>\<forall>\<alpha>. \<phi> \<alpha>) \<^bold>\<rightarrow> \<phi> \<alpha> in v]" using cqt_orig_1 by metis
        }
        hence "[\<^bold>\<box>(\<^bold>\<forall>\<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<alpha>) in v]" using RM_1 by auto
      }
      hence "[\<^bold>\<forall>\<alpha> . \<^bold>\<box>(\<^bold>\<forall>\<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> \<alpha>) in v]" using "\<^bold>\<forall>I" by metis
      thus ?thesis using cqt_orig_2[deduction] by metis
    qed
  lemmas CBF = BFs_2

  lemma BFs_3[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<exists> \<alpha>. \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<exists> \<alpha> . \<^bold>\<diamond>(\<phi> \<alpha>)) in v]"
    proof -
      have "[(\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<^bold>\<not>(\<phi> \<alpha>)) in v]"
        using BF by metis
      hence 1: "[(\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<^bold>\<not>(\<phi> \<alpha>)))) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>)))) in v]"
        using contraposition_1 by simp
      have 2: "[\<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<forall>\<alpha>. \<^bold>\<not>(\<phi> \<alpha>))) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>)))) in v]"
        apply (PLM_subst_method "\<^bold>\<not>\<^bold>\<box>(\<^bold>\<forall>\<alpha> . \<^bold>\<not>(\<phi> \<alpha>))" "\<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<forall>\<alpha>. \<^bold>\<not>(\<phi> \<alpha>)))")
        using KBasic2_2 1 by simp+
      have "[\<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<forall>\<alpha>. \<^bold>\<not>(\<phi> \<alpha>))) \<^bold>\<rightarrow> (\<^bold>\<exists> \<alpha> . \<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>)))) in v]"
        apply (PLM_subst_method "\<^bold>\<not>(\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>)))" "\<^bold>\<exists> \<alpha>. \<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>)))")
         using cqt_further_2 apply metis
        using 2 by metis
      thus ?thesis
        unfolding exists_def diamond_def by auto
    qed
  lemmas "BF\<^bold>\<diamond>" = BFs_3

  lemma BFs_4[PLM]:
    "[(\<^bold>\<exists> \<alpha> . \<^bold>\<diamond>(\<phi> \<alpha>)) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<exists> \<alpha>. \<phi> \<alpha>) in v]"
    proof -
      have 1: "[\<^bold>\<box>(\<^bold>\<forall>\<alpha> . \<^bold>\<not>(\<phi> \<alpha>)) \<^bold>\<rightarrow> (\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>))) in v]"
        using CBF by auto
      have 2: "[(\<^bold>\<exists> \<alpha> . (\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>))))) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<^bold>\<not>(\<phi> \<alpha>)))) in v]"
        apply (PLM_subst_method "\<^bold>\<not>(\<^bold>\<forall>\<alpha>. \<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>)))" "(\<^bold>\<exists> \<alpha> . (\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>)))))")
         using cqt_further_2 apply blast
        using 1 using contraposition_1 by metis
      have "[(\<^bold>\<exists> \<alpha> . (\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<not>(\<phi> \<alpha>))))) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<forall> \<alpha> . \<^bold>\<not>(\<phi> \<alpha>))) in v]"
        apply (PLM_subst_method "\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<^bold>\<not>(\<phi> \<alpha>)))" "\<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<forall>\<alpha>. \<^bold>\<not>(\<phi> \<alpha>)))")
         using KBasic2_2 apply blast
        using 2 by assumption
      thus ?thesis
        unfolding diamond_def exists_def by auto
    qed
  lemmas "CBF\<^bold>\<diamond>" = BFs_4

  lemma sign_S5_thm_1[PLM]:
    "[(\<^bold>\<exists> \<alpha>. \<^bold>\<box>(\<phi> \<alpha>)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists> \<alpha>. \<phi> \<alpha>) in v]"
    proof (rule CP)
      assume "[\<^bold>\<exists>  \<alpha> . \<^bold>\<box>(\<phi> \<alpha>) in v]"
      then obtain \<tau> where "[\<^bold>\<box>(\<phi> \<tau>) in v]"
        by (rule "\<^bold>\<exists>E")
      moreover {
        fix v
        assume "[\<phi> \<tau> in v]"
        hence "[\<^bold>\<exists> \<alpha> . \<phi> \<alpha> in v]"
          by (rule "\<^bold>\<exists>I")
      }
      ultimately show "[\<^bold>\<box>(\<^bold>\<exists>  \<alpha> . \<phi> \<alpha>) in v]"
        using RN_2 by blast
    qed
  lemmas Buridan = sign_S5_thm_1

  lemma sign_S5_thm_2[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> (\<^bold>\<forall> \<alpha> . \<^bold>\<diamond>(\<phi> \<alpha>)) in v]"
    proof -
      {
        fix \<alpha>
        {
          fix v
          have "[(\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> \<phi> \<alpha> in v]"
            using cqt_orig_1 by metis
        }
        hence "[\<^bold>\<diamond>(\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<phi> \<alpha>) in v]"
          using RM_2 by metis
      }
      hence "[\<^bold>\<forall> \<alpha> . \<^bold>\<diamond>(\<^bold>\<forall> \<alpha> . \<phi> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<diamond>(\<phi> \<alpha>) in v]"
        using "\<^bold>\<forall>I" by metis
      thus ?thesis
        using cqt_orig_2[deduction] by metis
    qed
  lemmas "Buridan\<^bold>\<diamond>" = sign_S5_thm_2

  lemma sign_S5_thm_3[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<exists> \<alpha> . \<phi> \<alpha> \<^bold>& \<psi> \<alpha>) \<^bold>\<rightarrow> \<^bold>\<diamond>((\<^bold>\<exists> \<alpha> . \<phi> \<alpha>) \<^bold>& (\<^bold>\<exists> \<alpha> . \<psi> \<alpha>)) in v]"
    by (simp only: RM_2 cqt_further_5)

  lemma sign_S5_thm_4[PLM]:
    "[((\<^bold>\<box>(\<^bold>\<forall> \<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>)) \<^bold>& (\<^bold>\<box>(\<^bold>\<forall> \<alpha> . \<psi> \<alpha> \<^bold>\<rightarrow> \<chi> \<alpha>))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<chi> \<alpha>) in v]"
    proof (rule CP)
      assume "[\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<rightarrow> \<chi> \<alpha>) in v]"
      hence "[\<^bold>\<box>((\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>& (\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<rightarrow> \<chi> \<alpha>)) in v]"
        using KBasic_3[equiv_rl] by blast
      moreover {
        fix v
        assume "[((\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<psi> \<alpha>) \<^bold>& (\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<rightarrow> \<chi> \<alpha>)) in v]"
        hence "[(\<^bold>\<forall> \<alpha> . \<phi> \<alpha> \<^bold>\<rightarrow> \<chi> \<alpha>) in v]"
          using cqt_basic_9[deduction] by blast
      }
      ultimately show "[\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<rightarrow> \<chi> \<alpha>) in v]"
        using RN_2 by blast
    qed

  lemma sign_S5_thm_5[PLM]:
    "[((\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>)) \<^bold>& (\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<equiv> \<chi> \<alpha>))) \<^bold>\<rightarrow> (\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<chi> \<alpha>)) in v]"
    proof (rule CP)
      assume "[\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>) \<^bold>& \<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<equiv> \<chi> \<alpha>) in v]"
      hence "[\<^bold>\<box>((\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>) \<^bold>& (\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<equiv> \<chi> \<alpha>)) in v]"
        using KBasic_3[equiv_rl] by blast
      moreover {
        fix v
        assume "[((\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<psi> \<alpha>) \<^bold>& (\<^bold>\<forall>\<alpha>. \<psi> \<alpha> \<^bold>\<equiv> \<chi> \<alpha>)) in v]"
        hence "[(\<^bold>\<forall> \<alpha> . \<phi> \<alpha> \<^bold>\<equiv> \<chi> \<alpha>) in v]"
          using cqt_basic_10[deduction] by blast
      }
      ultimately show "[\<^bold>\<box>(\<^bold>\<forall>\<alpha>. \<phi> \<alpha> \<^bold>\<equiv> \<chi> \<alpha>) in v]"
        using RN_2 by blast
    qed
  
  lemma id_nec2_1[PLM]:
    "[\<^bold>\<diamond>((\<alpha>::'a::id_eq) \<^bold>= \<beta>) \<^bold>\<equiv> (\<alpha> \<^bold>= \<beta>) in v]"
    apply (rule "\<^bold>\<equiv>I"; rule CP)
     using id_nec[equiv_lr] derived_S5_rules_2_b CP modus_ponens apply blast
    using "T\<^bold>\<diamond>"[deduction] by auto

  lemma id_nec2_2_Aux:
    "[(\<^bold>\<diamond>\<phi>) \<^bold>\<equiv> \<psi> in v] \<Longrightarrow> [(\<^bold>\<not>\<psi>) \<^bold>\<equiv> \<^bold>\<box>(\<^bold>\<not>\<phi>) in v]"
    proof -
      assume "[(\<^bold>\<diamond>\<phi>) \<^bold>\<equiv> \<psi> in v]"
      moreover have "\<And>\<phi> \<psi>. [(\<^bold>\<not>\<phi>) \<^bold>\<equiv> \<psi> in v] \<Longrightarrow> [(\<^bold>\<not>\<psi>) \<^bold>\<equiv> \<phi> in v]"
        by PLM_solver
      ultimately show ?thesis
        unfolding diamond_def by blast
    qed

  lemma id_nec2_2[PLM]:
    "[((\<alpha>::'a::id_eq) \<^bold>\<noteq> \<beta>) \<^bold>\<equiv> \<^bold>\<box>(\<alpha> \<^bold>\<noteq> \<beta>) in v]"
    using id_nec2_1[THEN id_nec2_2_Aux] by auto

  lemma id_nec2_3[PLM]:
    "[(\<^bold>\<diamond>((\<alpha>::'a::id_eq) \<^bold>\<noteq> \<beta>)) \<^bold>\<equiv> (\<alpha> \<^bold>\<noteq> \<beta>) in v]"
    using "T\<^bold>\<diamond>" "\<^bold>\<equiv>I" id_nec2_2[equiv_lr]
          CP derived_S5_rules_2_b by metis

  lemma exists_desc_box_1[PLM]:
    "[(\<^bold>\<exists> y . (y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<rightarrow> (\<^bold>\<exists> y . \<^bold>\<box>((y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x))) in v]"
    proof (rule CP)
      assume "[\<^bold>\<exists>y. (y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
      then obtain y where "[(y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x) in v]"
        by (rule "\<^bold>\<exists>E")
      hence "[\<^bold>\<box>(y\<^sup>P \<^bold>= (\<^bold>\<iota>x. \<phi> x)) in v]"
        using l_identity[axiom_instance, deduction, deduction]
              cqt_1[axiom_instance] all_self_eq_2[where 'a=\<nu>]
              modus_ponens unfolding identity_\<nu>_def by fast
      thus "[\<^bold>\<exists>y. \<^bold>\<box>((y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x)) in v]"
        by (rule "\<^bold>\<exists>I")
    qed

  lemma exists_desc_box_2[PLM]:
    "[(\<^bold>\<exists> y . (y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x)) \<^bold>\<rightarrow>  \<^bold>\<box>(\<^bold>\<exists> y .((y\<^sup>P) \<^bold>= (\<^bold>\<iota>x. \<phi> x))) in v]"
    using exists_desc_box_1 Buridan ded_thm_cor_3 by fast

  lemma en_eq_1[PLM]:
    "[\<^bold>\<diamond>\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<^bold>\<box>\<lbrace>x,F\<rbrace> in v]"
    using encoding[axiom_instance] RN
          sc_eq_box_box_1 modus_ponens by blast
  lemma en_eq_2[PLM]:
    "[\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<^bold>\<box>\<lbrace>x,F\<rbrace> in v]"
    using encoding[axiom_instance] qml_2[axiom_instance] by (rule "\<^bold>\<equiv>I")
  lemma en_eq_3[PLM]:
    "[\<^bold>\<diamond>\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>x,F\<rbrace> in v]"
    using encoding[axiom_instance] derived_S5_rules_2_b "\<^bold>\<equiv>I" "T\<^bold>\<diamond>" by auto
  lemma en_eq_4[PLM]:
    "[(\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,G\<rbrace>) \<^bold>\<equiv> (\<^bold>\<box>\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<^bold>\<box>\<lbrace>y,G\<rbrace>) in v]"
    by (metis CP en_eq_2 "\<^bold>\<equiv>I" "\<^bold>\<equiv>E"(1) "\<^bold>\<equiv>E"(2))
  lemma en_eq_5[PLM]:
    "[\<^bold>\<box>(\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,G\<rbrace>) \<^bold>\<equiv> (\<^bold>\<box>\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<^bold>\<box>\<lbrace>y,G\<rbrace>) in v]"
    using "\<^bold>\<equiv>I" KBasic_6 encoding[axiom_necessitation, axiom_instance]
    sc_eq_box_box_3[deduction] "\<^bold>&I" by simp
  lemma en_eq_6[PLM]:
    "[(\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,G\<rbrace>) \<^bold>\<equiv> \<^bold>\<box>(\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>y,G\<rbrace>) in v]"
    using en_eq_4 en_eq_5 oth_class_taut_4_a "\<^bold>\<equiv>E"(6) by meson
  lemma en_eq_7[PLM]:
    "[(\<^bold>\<not>\<lbrace>x,F\<rbrace>) \<^bold>\<equiv> \<^bold>\<box>(\<^bold>\<not>\<lbrace>x,F\<rbrace>) in v]"
    using en_eq_3[THEN id_nec2_2_Aux] by blast
  lemma en_eq_8[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<not>\<lbrace>x,F\<rbrace>) \<^bold>\<equiv> (\<^bold>\<not>\<lbrace>x,F\<rbrace>) in v]"
     unfolding diamond_def apply (PLM_subst_method "\<lbrace>x,F\<rbrace>" "\<^bold>\<not>\<^bold>\<not>\<lbrace>x,F\<rbrace>")
      using oth_class_taut_4_b apply simp
     apply (PLM_subst_method "\<lbrace>x,F\<rbrace>" "\<^bold>\<box>\<lbrace>x,F\<rbrace>")
      using en_eq_2 apply simp
     using oth_class_taut_4_a by assumption
  lemma en_eq_9[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<not>\<lbrace>x,F\<rbrace>) \<^bold>\<equiv> \<^bold>\<box>(\<^bold>\<not>\<lbrace>x,F\<rbrace>) in v]"
    using en_eq_8 en_eq_7 "\<^bold>\<equiv>E"(5) by blast
  lemma en_eq_10[PLM]:
    "[\<^bold>\<A>\<lbrace>x,F\<rbrace> \<^bold>\<equiv> \<lbrace>x,F\<rbrace> in v]"
    apply (rule "\<^bold>\<equiv>I")
     using encoding[axiom_actualization, axiom_instance,
                    THEN logic_actual_nec_2[axiom_instance, equiv_lr],
                    deduction, THEN qml_act_2[axiom_instance, equiv_rl],
                    THEN en_eq_2[equiv_rl]] CP
     apply simp
    using encoding[axiom_instance] nec_imp_act ded_thm_cor_3 by blast

subsection\<open>The Theory of Relations\<close> 
text\<open>\label{TAO_PLM_Relations}\<close>

  lemma beta_equiv_eq_1_1[PLM]:
    assumes "IsProperInX \<phi>"
        and "IsProperInX \<psi>"
        and "\<And>x.[\<phi> (x\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) in v]"
    shows "[\<lparr>\<^bold>\<lambda> y. \<phi> (y\<^sup>P), x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>\<^bold>\<lambda> y. \<psi> (y\<^sup>P), x\<^sup>P\<rparr> in v]"
    using lambda_predicates_2_1[OF assms(1), axiom_instance]
    using lambda_predicates_2_1[OF assms(2), axiom_instance]
    using assms(3) by (meson "\<^bold>\<equiv>E"(6) oth_class_taut_4_a)

  lemma beta_equiv_eq_1_2[PLM]:
    assumes "IsProperInXY \<phi>"
        and "IsProperInXY \<psi>"
        and "\<And>x y.[\<phi> (x\<^sup>P) (y\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) (y\<^sup>P) in v]"
    shows "[\<lparr>\<^bold>\<lambda>\<^sup>2 (\<lambda> x y. \<phi> (x\<^sup>P) (y\<^sup>P)), x\<^sup>P, y\<^sup>P\<rparr>
            \<^bold>\<equiv> \<lparr>\<^bold>\<lambda>\<^sup>2 (\<lambda> x y. \<psi> (x\<^sup>P) (y\<^sup>P)), x\<^sup>P, y\<^sup>P\<rparr> in v]"
    using lambda_predicates_2_2[OF assms(1), axiom_instance]
    using lambda_predicates_2_2[OF assms(2), axiom_instance]
    using assms(3) by (meson "\<^bold>\<equiv>E"(6) oth_class_taut_4_a)

  lemma beta_equiv_eq_1_3[PLM]:
    assumes "IsProperInXYZ \<phi>"
        and "IsProperInXYZ \<psi>"
        and "\<And>x y z.[\<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) in v]"
    shows "[\<lparr>\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z. \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)), x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>
            \<^bold>\<equiv> \<lparr>\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z. \<psi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)), x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr> in v]"
    using lambda_predicates_2_3[OF assms(1), axiom_instance]
    using lambda_predicates_2_3[OF assms(2), axiom_instance]
    using assms(3) by (meson "\<^bold>\<equiv>E"(6) oth_class_taut_4_a)

  lemma beta_equiv_eq_2_1[PLM]:
    assumes "IsProperInX \<phi>"
        and "IsProperInX \<psi>"
    shows "[(\<^bold>\<box>(\<^bold>\<forall> x . \<phi> (x\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P))) \<^bold>\<rightarrow>
            (\<^bold>\<box>(\<^bold>\<forall> x . \<lparr>\<^bold>\<lambda> y. \<phi> (y\<^sup>P), x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>\<^bold>\<lambda> y. \<psi> (y\<^sup>P), x\<^sup>P\<rparr>)) in v]"
     apply (rule qml_1[axiom_instance, deduction])
     apply (rule RN)
     proof (rule CP, rule "\<^bold>\<forall>I")
      fix v x
      assume "[\<^bold>\<forall>x. \<phi> (x\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) in v]"
      hence "\<And>x.[\<phi> (x\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) in v]"
        by PLM_solver
      thus "[\<lparr>\<^bold>\<lambda> y. \<phi> (y\<^sup>P), x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>\<^bold>\<lambda> y. \<psi> (y\<^sup>P), x\<^sup>P\<rparr> in v]"
        using assms beta_equiv_eq_1_1 by auto
     qed

  lemma beta_equiv_eq_2_2[PLM]:
    assumes "IsProperInXY \<phi>"
        and "IsProperInXY \<psi>"
    shows "[(\<^bold>\<box>(\<^bold>\<forall> x y . \<phi> (x\<^sup>P) (y\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) (y\<^sup>P))) \<^bold>\<rightarrow>
            (\<^bold>\<box>(\<^bold>\<forall> x y . \<lparr>\<^bold>\<lambda>\<^sup>2 (\<lambda> x y. \<phi> (x\<^sup>P) (y\<^sup>P)), x\<^sup>P, y\<^sup>P\<rparr>
              \<^bold>\<equiv> \<lparr>\<^bold>\<lambda>\<^sup>2 (\<lambda> x y. \<psi> (x\<^sup>P) (y\<^sup>P)), x\<^sup>P, y\<^sup>P\<rparr>)) in v]"
    apply (rule qml_1[axiom_instance, deduction])
    apply (rule RN)
    proof (rule CP, rule "\<^bold>\<forall>I", rule "\<^bold>\<forall>I")
      fix v x y
      assume "[\<^bold>\<forall>x y. \<phi> (x\<^sup>P) (y\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) (y\<^sup>P) in v]"
      hence "(\<And>x y.[\<phi> (x\<^sup>P) (y\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) (y\<^sup>P) in v])"
        by (meson "\<^bold>\<forall>E")
      thus "[\<lparr>\<^bold>\<lambda>\<^sup>2 (\<lambda> x y. \<phi> (x\<^sup>P) (y\<^sup>P)), x\<^sup>P, y\<^sup>P\<rparr>
            \<^bold>\<equiv> \<lparr>\<^bold>\<lambda>\<^sup>2 (\<lambda> x y. \<psi> (x\<^sup>P) (y\<^sup>P)), x\<^sup>P, y\<^sup>P\<rparr> in v]"
        using assms beta_equiv_eq_1_2 by auto
    qed

  lemma beta_equiv_eq_2_3[PLM]:
    assumes "IsProperInXYZ \<phi>"
        and "IsProperInXYZ \<psi>"
    shows "[(\<^bold>\<box>(\<^bold>\<forall> x y z . \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P))) \<^bold>\<rightarrow>
            (\<^bold>\<box>(\<^bold>\<forall> x y z . \<lparr>\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z. \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)), x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>
                \<^bold>\<equiv> \<lparr>\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z. \<psi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)), x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>)) in v]"
    apply (rule qml_1[axiom_instance, deduction])
    apply (rule RN)
    proof (rule CP, rule "\<^bold>\<forall>I", rule "\<^bold>\<forall>I", rule "\<^bold>\<forall>I")
      fix v x y z
      assume "[\<^bold>\<forall>x y z. \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) in v]"
      hence "(\<And>x y z.[\<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) \<^bold>\<equiv> \<psi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) in v])"
        by (meson "\<^bold>\<forall>E")
      thus "[\<lparr>\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z. \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)), x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>
              \<^bold>\<equiv> \<lparr>\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z. \<psi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)), x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr> in v]"
        using assms beta_equiv_eq_1_3 by auto
    qed

  lemma beta_C_meta_1[PLM]:
    assumes "IsProperInX \<phi>"
    shows "[\<lparr>\<^bold>\<lambda> y. \<phi> (y\<^sup>P), x\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) in v]"
    using lambda_predicates_2_1[OF assms, axiom_instance] by auto

  lemma beta_C_meta_2[PLM]:
    assumes "IsProperInXY \<phi>"
    shows "[\<lparr>\<^bold>\<lambda>\<^sup>2 (\<lambda> x y. \<phi> (x\<^sup>P) (y\<^sup>P)), x\<^sup>P, y\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) (y\<^sup>P) in v]"
    using lambda_predicates_2_2[OF assms, axiom_instance] by auto

  lemma beta_C_meta_3[PLM]:
    assumes "IsProperInXYZ \<phi>"
    shows "[\<lparr>\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z. \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)), x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P) in v]"
    using lambda_predicates_2_3[OF assms, axiom_instance] by auto

  lemma relations_1[PLM]:
    assumes "IsProperInX \<phi>"
    shows "[\<^bold>\<exists> F. \<^bold>\<box>(\<^bold>\<forall> x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P)) in v]"
    using assms apply - by PLM_solver

  lemma relations_2[PLM]:
    assumes "IsProperInXY \<phi>"
    shows "[\<^bold>\<exists> F. \<^bold>\<box>(\<^bold>\<forall> x y. \<lparr>F,x\<^sup>P,y\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) (y\<^sup>P)) in v]"
    using assms apply - by PLM_solver

  lemma relations_3[PLM]:
    assumes "IsProperInXYZ \<phi>"
    shows "[\<^bold>\<exists> F. \<^bold>\<box>(\<^bold>\<forall> x y z. \<lparr>F,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr> \<^bold>\<equiv> \<phi> (x\<^sup>P) (y\<^sup>P) (z\<^sup>P)) in v]"
    using assms apply - by PLM_solver

  lemma prop_equiv[PLM]:
    shows "[(\<^bold>\<forall> x . (\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,G\<rbrace>)) \<^bold>\<rightarrow> F \<^bold>= G in v]"
    proof (rule CP)
      assume 1: "[\<^bold>\<forall>x. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,G\<rbrace> in v]"
      {
        fix x
        have "[\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,G\<rbrace> in v]"
          using 1 by (rule "\<^bold>\<forall>E")
        hence "[\<^bold>\<box>(\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,G\<rbrace>) in v]"
          using PLM.en_eq_6 "\<^bold>\<equiv>E"(1) by blast
      }
      hence "[\<^bold>\<forall>x. \<^bold>\<box>(\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,G\<rbrace>) in v]"
        by (rule "\<^bold>\<forall>I")
      thus "[F \<^bold>= G in v]"
        unfolding identity_defs
        by (rule BF[deduction])
    qed

  lemma propositions_lemma_1[PLM]:
    "[\<^bold>\<lambda>\<^sup>0 \<phi> \<^bold>= \<phi> in v]"
    using lambda_predicates_3_0[axiom_instance] .

  lemma propositions_lemma_2[PLM]:
    "[\<^bold>\<lambda>\<^sup>0 \<phi> \<^bold>\<equiv> \<phi> in v]"
    using lambda_predicates_3_0[axiom_instance, THEN id_eq_prop_prop_8_b[deduction]]
    apply (rule l_identity[axiom_instance, deduction, deduction])
    by PLM_solver

  lemma propositions_lemma_4[PLM]:
    assumes "\<And>x.[\<^bold>\<A>(\<phi> x \<^bold>\<equiv> \<psi> x) in v]"
    shows "[(\<chi>::\<kappa>\<Rightarrow>\<o>) (\<^bold>\<iota>x. \<phi> x) \<^bold>= \<chi> (\<^bold>\<iota>x. \<psi> x) in v]"
    proof -
      have "[\<^bold>\<lambda>\<^sup>0 (\<chi> (\<^bold>\<iota>x. \<phi> x)) \<^bold>= \<^bold>\<lambda>\<^sup>0 (\<chi> (\<^bold>\<iota>x. \<psi> x)) in v]"
        using assms lambda_predicates_4_0[axiom_instance]
        by blast
      hence "[(\<chi> (\<^bold>\<iota>x. \<phi> x)) \<^bold>= \<^bold>\<lambda>\<^sup>0 (\<chi> (\<^bold>\<iota>x. \<psi> x)) in v]"
        using propositions_lemma_1[THEN id_eq_prop_prop_8_b[deduction]]
              id_eq_prop_prop_9_b[deduction] "\<^bold>&I"
        by blast
      thus ?thesis
        using propositions_lemma_1 id_eq_prop_prop_9_b[deduction] "\<^bold>&I"
        by blast
    qed

  lemma propositions[PLM]:
    "[\<^bold>\<exists> p . \<^bold>\<box>(p \<^bold>\<equiv> p') in v]"
    by PLM_solver

  lemma pos_not_equiv_then_not_eq[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<not>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>)) \<^bold>\<rightarrow> F \<^bold>\<noteq> G in v]"
    unfolding diamond_def
    proof (subst contraposition_1[symmetric], rule CP)
      assume "[F \<^bold>= G in v]"
      thus "[\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<not>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>G,x\<^sup>P\<rparr>))) in v]"
        apply (rule l_identity[axiom_instance, deduction, deduction])
        by PLM_solver
    qed

  lemma thm_relation_negation_1_1[PLM]:
    "[\<lparr>F\<^sup>-, x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<lparr>F, x\<^sup>P\<rparr> in v]"
    unfolding propnot_defs
    apply (rule lambda_predicates_2_1[axiom_instance])
    by show_proper

  lemma thm_relation_negation_1_2[PLM]:
    "[\<lparr>F\<^sup>-, x\<^sup>P, y\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<lparr>F, x\<^sup>P, y\<^sup>P\<rparr> in v]"
    unfolding propnot_defs
    apply (rule lambda_predicates_2_2[axiom_instance])
    by show_proper

  lemma thm_relation_negation_1_3[PLM]:
    "[\<lparr>F\<^sup>-, x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<lparr>F, x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr> in v]"
    unfolding propnot_defs
    apply (rule lambda_predicates_2_3[axiom_instance])
    by show_proper

  lemma thm_relation_negation_2_1[PLM]:
    "[(\<^bold>\<not>\<lparr>F\<^sup>-, x\<^sup>P\<rparr>) \<^bold>\<equiv> \<lparr>F, x\<^sup>P\<rparr> in v]"
    using thm_relation_negation_1_1[THEN oth_class_taut_5_d[equiv_lr]]
    apply - by PLM_solver

  lemma thm_relation_negation_2_2[PLM]:
    "[(\<^bold>\<not>\<lparr>F\<^sup>-, x\<^sup>P, y\<^sup>P\<rparr>) \<^bold>\<equiv> \<lparr>F, x\<^sup>P, y\<^sup>P\<rparr> in v]"
    using thm_relation_negation_1_2[THEN oth_class_taut_5_d[equiv_lr]]
    apply - by PLM_solver

  lemma thm_relation_negation_2_3[PLM]:
    "[(\<^bold>\<not>\<lparr>F\<^sup>-, x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr>) \<^bold>\<equiv> \<lparr>F, x\<^sup>P, y\<^sup>P, z\<^sup>P\<rparr> in v]"
    using thm_relation_negation_1_3[THEN oth_class_taut_5_d[equiv_lr]]
    apply - by PLM_solver

  lemma thm_relation_negation_3[PLM]:
    "[(p)\<^sup>- \<^bold>\<equiv> \<^bold>\<not>p in v]"
    unfolding propnot_defs
    using propositions_lemma_2 by simp

  lemma thm_relation_negation_4[PLM]:
    "[(\<^bold>\<not>((p::\<o>)\<^sup>-)) \<^bold>\<equiv> p in v]"
    using thm_relation_negation_3[THEN oth_class_taut_5_d[equiv_lr]]
    apply - by PLM_solver

  lemma thm_relation_negation_5_1[PLM]:
    "[(F::\<Pi>\<^sub>1) \<^bold>\<noteq> (F\<^sup>-) in v]"
    using id_eq_prop_prop_2[deduction]
          l_identity[where \<phi>="\<lambda> G . \<lparr>G,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F\<^sup>-,x\<^sup>P\<rparr>", axiom_instance,
                      deduction, deduction]
          oth_class_taut_4_a thm_relation_negation_1_1 "\<^bold>\<equiv>E"(5)
          oth_class_taut_1_b modus_tollens_1 CP
    by meson

  lemma thm_relation_negation_5_2[PLM]:
    "[(F::\<Pi>\<^sub>2) \<^bold>\<noteq> (F\<^sup>-) in v]"
    using id_eq_prop_prop_5_a[deduction]
          l_identity[where \<phi>="\<lambda> G . \<lparr>G,x\<^sup>P,y\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F\<^sup>-,x\<^sup>P,y\<^sup>P\<rparr>", axiom_instance,
                      deduction, deduction]
          oth_class_taut_4_a thm_relation_negation_1_2 "\<^bold>\<equiv>E"(5)
          oth_class_taut_1_b modus_tollens_1 CP
    by meson

  lemma thm_relation_negation_5_3[PLM]:
    "[(F::\<Pi>\<^sub>3) \<^bold>\<noteq> (F\<^sup>-) in v]"
    using id_eq_prop_prop_5_b[deduction]
          l_identity[where \<phi>="\<lambda> G . \<lparr>G,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F\<^sup>-,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>",
                     axiom_instance, deduction, deduction]
          oth_class_taut_4_a thm_relation_negation_1_3 "\<^bold>\<equiv>E"(5)
          oth_class_taut_1_b modus_tollens_1 CP
    by meson

  lemma thm_relation_negation_6[PLM]:
    "[(p::\<o>) \<^bold>\<noteq> (p\<^sup>-) in v]"
    using id_eq_prop_prop_8_b[deduction]
          l_identity[where \<phi>="\<lambda> G . G \<^bold>\<equiv> (p\<^sup>-)", axiom_instance,
                      deduction, deduction]
          oth_class_taut_4_a thm_relation_negation_3 "\<^bold>\<equiv>E"(5)
          oth_class_taut_1_b modus_tollens_1 CP
    by meson

  lemma thm_relation_negation_7[PLM]:
    "[((p::\<o>)\<^sup>-) \<^bold>= \<^bold>\<not>p in v]"
    unfolding propnot_defs using propositions_lemma_1 by simp

  lemma thm_relation_negation_8[PLM]:
    "[(p::\<o>) \<^bold>\<noteq> \<^bold>\<not>p in v]"
    unfolding propnot_defs 
    using id_eq_prop_prop_8_b[deduction]
          l_identity[where \<phi>="\<lambda> G . G \<^bold>\<equiv> \<^bold>\<not>(p)", axiom_instance,
                      deduction, deduction]
          oth_class_taut_4_a oth_class_taut_1_b
          modus_tollens_1 CP
    by meson

  lemma thm_relation_negation_9[PLM]:
    "[((p::\<o>) \<^bold>= q) \<^bold>\<rightarrow> ((\<^bold>\<not>p) \<^bold>= (\<^bold>\<not>q)) in v]"
    using l_identity[where \<alpha>="p" and \<beta>="q" and \<phi>="\<lambda> x . (\<^bold>\<not>p) \<^bold>= (\<^bold>\<not>x)",
                      axiom_instance, deduction]
          id_eq_prop_prop_7_b using CP modus_ponens by blast

  lemma thm_relation_negation_10[PLM]:
    "[((p::\<o>) \<^bold>= q) \<^bold>\<rightarrow> ((p\<^sup>-) \<^bold>= (q\<^sup>-)) in v]"
    using l_identity[where \<alpha>="p" and \<beta>="q" and \<phi>="\<lambda> x . (p\<^sup>-) \<^bold>= (x\<^sup>-)",
                      axiom_instance, deduction]
          id_eq_prop_prop_7_b using CP modus_ponens by blast

  lemma thm_cont_prop_1[PLM]:
    "[NonContingent (F::\<Pi>\<^sub>1) \<^bold>\<equiv> NonContingent (F\<^sup>-) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[NonContingent F in v]"
      hence "[\<^bold>\<box>(\<^bold>\<forall>x.\<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<forall>x.\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) in v]"
        unfolding NonContingent_def Necessary_defs Impossible_defs .
      hence "[\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) in v]"
        apply -
        apply (PLM_subst_method "\<lambda> x . \<lparr>F,x\<^sup>P\<rparr>" "\<lambda> x . \<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>")
        using thm_relation_negation_2_1[equiv_sym] by auto
      hence "[\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F\<^sup>-,x\<^sup>P\<rparr>) in v]"
        apply -
        apply (PLM_subst_goal_method
               "\<lambda> \<phi> . \<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<forall>x. \<phi> x)" "\<lambda> x . \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>")
        using thm_relation_negation_1_1[equiv_sym] by auto
      hence "[\<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F\<^sup>-,x\<^sup>P\<rparr>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>) in v]"
        by (rule oth_class_taut_3_e[equiv_lr])
      thus "[NonContingent (F\<^sup>-) in v]"
        unfolding NonContingent_def Necessary_defs Impossible_defs .
    next
      assume "[NonContingent (F\<^sup>-) in v]"
      hence "[\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F\<^sup>-,x\<^sup>P\<rparr>) in v]"
        unfolding NonContingent_def Necessary_defs Impossible_defs
        by (rule oth_class_taut_3_e[equiv_lr])
      hence "[\<^bold>\<box>(\<^bold>\<forall>x.\<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<forall>x.\<lparr>F\<^sup>-,x\<^sup>P\<rparr>) in v]"
        apply -
        apply (PLM_subst_method  "\<lambda> x . \<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>" "\<lambda> x . \<lparr>F,x\<^sup>P\<rparr>")
        using thm_relation_negation_2_1 by auto
      hence "[\<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) in v]"
        apply -
        apply (PLM_subst_method "\<lambda> x . \<lparr>F\<^sup>-,x\<^sup>P\<rparr>" "\<lambda> x . \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>")
        using thm_relation_negation_1_1 by auto
      thus "[NonContingent F in v]"
        unfolding NonContingent_def Necessary_defs Impossible_defs .
    qed

  lemma thm_cont_prop_2[PLM]:
    "[Contingent F \<^bold>\<equiv> \<^bold>\<diamond>(\<^bold>\<exists> x . \<lparr>F,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>(\<^bold>\<exists> x . \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[Contingent F in v]"
      hence "[\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<forall>x.\<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<forall>x.\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) in v]"
        unfolding Contingent_def Necessary_defs Impossible_defs .
      hence "[(\<^bold>\<not>\<^bold>\<box>(\<^bold>\<forall>x.\<lparr>F,x\<^sup>P\<rparr>)) \<^bold>& (\<^bold>\<not>\<^bold>\<box>(\<^bold>\<forall>x.\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) in v]"
        by (rule oth_class_taut_6_d[equiv_lr])
      hence "[(\<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<forall>x.\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) \<^bold>& (\<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<forall>x.\<lparr>F,x\<^sup>P\<rparr>)) in v]"
        using KBasic2_2[equiv_lr] "\<^bold>&I" "\<^bold>&E" by meson
      thus "[(\<^bold>\<diamond>(\<^bold>\<exists> x.\<lparr>F,x\<^sup>P\<rparr>)) \<^bold>& (\<^bold>\<diamond>(\<^bold>\<exists>x. \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) in v]"
        unfolding exists_def apply -
        apply (PLM_subst_method "\<lambda> x . \<lparr>F,x\<^sup>P\<rparr>" "\<lambda> x . \<^bold>\<not>\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>")
        using oth_class_taut_4_b by auto
    next
      assume "[(\<^bold>\<diamond>(\<^bold>\<exists> x.\<lparr>F,x\<^sup>P\<rparr>)) \<^bold>& (\<^bold>\<diamond>(\<^bold>\<exists>x. \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) in v]"
      hence "[(\<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<forall>x.\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) \<^bold>& (\<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<forall>x.\<lparr>F,x\<^sup>P\<rparr>)) in v]"
        unfolding exists_def apply -
        apply (PLM_subst_goal_method
               "\<lambda> \<phi> . (\<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<forall>x.\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) \<^bold>& (\<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<forall>x. \<phi> x))" "\<lambda> x . \<^bold>\<not>\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>")
        using oth_class_taut_4_b[equiv_sym] by auto
      hence "[(\<^bold>\<not>\<^bold>\<box>(\<^bold>\<forall>x.\<lparr>F,x\<^sup>P\<rparr>)) \<^bold>& (\<^bold>\<not>\<^bold>\<box>(\<^bold>\<forall>x.\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) in v]"
        using KBasic2_2[equiv_rl] "\<^bold>&I" "\<^bold>&E" by meson
      hence "[\<^bold>\<not>(\<^bold>\<box>(\<^bold>\<forall>x.\<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<forall>x.\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) in v]"
        by (rule oth_class_taut_6_d[equiv_rl])
      thus "[Contingent F in v]"
        unfolding Contingent_def Necessary_defs Impossible_defs .
    qed

  lemma thm_cont_prop_3[PLM]:
    "[Contingent (F::\<Pi>\<^sub>1) \<^bold>\<equiv> Contingent (F\<^sup>-) in v]"
    using thm_cont_prop_1
    unfolding NonContingent_def Contingent_def
    by (rule oth_class_taut_5_d[equiv_lr])

  lemma lem_cont_e[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<exists> x . \<lparr>F,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>))) \<^bold>\<equiv> \<^bold>\<diamond>(\<^bold>\<exists> x . ((\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr>))in v]"
    proof -
      have "[\<^bold>\<diamond>(\<^bold>\<exists> x . \<lparr>F,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>))) in v]
             = [(\<^bold>\<exists> x . \<^bold>\<diamond>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>))) in v]"
        using "BF\<^bold>\<diamond>"[deduction] "CBF\<^bold>\<diamond>"[deduction] by fast
      also have "... = [\<^bold>\<exists> x . (\<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) in v]"
        apply (PLM_subst_method
               "\<lambda> x . \<^bold>\<diamond>(\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>))"
               "\<lambda> x . \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)")
        using S5Basic_12 by auto
      also have "... = [\<^bold>\<exists> x . \<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr> in v]" 
        apply (PLM_subst_method
               "\<lambda> x . \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)"
               "\<lambda> x . \<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr>")
        using oth_class_taut_3_b by auto
      also have "... = [\<^bold>\<exists> x . \<^bold>\<diamond>((\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr>) in v]"
        apply (PLM_subst_method
               "\<lambda> x . \<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr>"
               "\<lambda> x . \<^bold>\<diamond>((\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr>)")
        using S5Basic_12[equiv_sym] by auto
      also have "... = [\<^bold>\<diamond> (\<^bold>\<exists> x . ((\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr>)) in v]"
        using "CBF\<^bold>\<diamond>"[deduction] "BF\<^bold>\<diamond>"[deduction] by fast
      finally show ?thesis using "\<^bold>\<equiv>I" CP by blast
    qed

  lemma lem_cont_e_2[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<exists> x . \<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)) \<^bold>\<equiv> \<^bold>\<diamond>(\<^bold>\<exists> x . \<lparr>F\<^sup>-,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>)) in v]"
    apply (PLM_subst_method "\<lambda> x . \<lparr>F,x\<^sup>P\<rparr>" "\<lambda> x . \<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>")
     using thm_relation_negation_2_1[equiv_sym] apply simp
    apply (PLM_subst_method "\<lambda> x . \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>" "\<lambda> x . \<lparr>F\<^sup>-,x\<^sup>P\<rparr>")
     using thm_relation_negation_1_1[equiv_sym] apply simp
    using lem_cont_e by simp

  lemma thm_cont_e_1[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<exists> x . ((\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>) \<^bold>& (\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>))) in v]"
    using lem_cont_e[where F="E!", equiv_lr] qml_4[axiom_instance,conj1]
    by blast

  lemma thm_cont_e_2[PLM]:
    "[Contingent (E!) in v]"
    using thm_cont_prop_2[equiv_rl] "\<^bold>&I" qml_4[axiom_instance, conj1]
          KBasic2_8[deduction, OF sign_S5_thm_3[deduction], conj1]
          KBasic2_8[deduction, OF sign_S5_thm_3[deduction, OF thm_cont_e_1], conj1]
    by fast

  lemma thm_cont_e_3[PLM]:
    "[Contingent (E!\<^sup>-) in v]"
    using thm_cont_e_2 thm_cont_prop_3[equiv_lr] by blast

  lemma thm_cont_e_4[PLM]:
    "[\<^bold>\<exists> (F::\<Pi>\<^sub>1) G . (F \<^bold>\<noteq> G \<^bold>& Contingent F \<^bold>& Contingent G) in v]"
    apply (rule_tac \<alpha>="E!" in "\<^bold>\<exists>I", rule_tac \<alpha>="E!\<^sup>-" in "\<^bold>\<exists>I")
    using thm_cont_e_2 thm_cont_e_3 thm_relation_negation_5_1 "\<^bold>&I" by auto

  context
  begin
    qualified definition L where "L \<equiv> (\<^bold>\<lambda> x . \<lparr>E!, x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<lparr>E!, x\<^sup>P\<rparr>)"
    
    lemma thm_noncont_e_e_1[PLM]:
      "[Necessary L in v]"
      unfolding Necessary_defs L_def apply (rule RN, rule "\<^bold>\<forall>I")
      apply (rule lambda_predicates_2_1[axiom_instance, equiv_rl])
        apply show_proper
      using if_p_then_p .

    lemma thm_noncont_e_e_2[PLM]:
      "[Impossible (L\<^sup>-) in v]"
      unfolding Impossible_defs L_def apply (rule RN, rule "\<^bold>\<forall>I")
      apply (rule thm_relation_negation_2_1[equiv_rl])
      apply (rule lambda_predicates_2_1[axiom_instance, equiv_rl])
       apply show_proper
      using if_p_then_p .

    lemma thm_noncont_e_e_3[PLM]:
      "[NonContingent (L) in v]"
      unfolding NonContingent_def using thm_noncont_e_e_1
      by (rule "\<^bold>\<or>I"(1))

    lemma thm_noncont_e_e_4[PLM]:
      "[NonContingent (L\<^sup>-) in v]"
      unfolding NonContingent_def using thm_noncont_e_e_2
      by (rule "\<^bold>\<or>I"(2))

    lemma thm_noncont_e_e_5[PLM]:
      "[\<^bold>\<exists> (F::\<Pi>\<^sub>1) G . F \<^bold>\<noteq> G \<^bold>& NonContingent F \<^bold>& NonContingent G in v]"
      apply (rule_tac \<alpha>="L" in "\<^bold>\<exists>I", rule_tac \<alpha>="L\<^sup>-" in "\<^bold>\<exists>I")
      using "\<^bold>\<exists>I" thm_relation_negation_5_1 thm_noncont_e_e_3
            thm_noncont_e_e_4 "\<^bold>&I"
      by simp


  lemma four_distinct_1[PLM]:
    "[NonContingent (F::\<Pi>\<^sub>1) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> G . (Contingent G \<^bold>& G \<^bold>= F)) in v]"
    proof (rule CP)
      assume "[NonContingent F in v]"
      hence "[\<^bold>\<not>(Contingent F) in v]"
        unfolding NonContingent_def Contingent_def
        apply - by PLM_solver
      moreover {
         assume "[\<^bold>\<exists> G . Contingent G \<^bold>& G \<^bold>= F in v]"
         then obtain P where "[Contingent P \<^bold>& P \<^bold>= F in v]"
          by (rule "\<^bold>\<exists>E")
         hence "[Contingent F in v]"
           using "\<^bold>&E" l_identity[axiom_instance, deduction, deduction]
           by blast
      }
      ultimately show "[\<^bold>\<not>(\<^bold>\<exists>G. Contingent G \<^bold>& G \<^bold>= F) in v]"
        using modus_tollens_1 CP by blast
    qed

  lemma four_distinct_2[PLM]:
    "[Contingent (F::\<Pi>\<^sub>1) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> G . (NonContingent G \<^bold>& G \<^bold>= F)) in v]"
    proof (rule CP)
      assume "[Contingent F in v]"
      hence "[\<^bold>\<not>(NonContingent F) in v]"
        unfolding NonContingent_def Contingent_def
        apply - by PLM_solver
      moreover {
         assume "[\<^bold>\<exists> G . NonContingent G \<^bold>& G \<^bold>= F in v]"
         then obtain P where "[NonContingent P \<^bold>& P \<^bold>= F in v]"
          by (rule "\<^bold>\<exists>E")
         hence "[NonContingent F in v]"
           using "\<^bold>&E" l_identity[axiom_instance, deduction, deduction]
           by blast
      }
      ultimately show "[\<^bold>\<not>(\<^bold>\<exists>G. NonContingent G \<^bold>& G \<^bold>= F) in v]"
        using modus_tollens_1 CP by blast
    qed

    lemma four_distinct_3[PLM]:
      "[L \<^bold>\<noteq> (L\<^sup>-) \<^bold>& L \<^bold>\<noteq> E! \<^bold>& L \<^bold>\<noteq> (E!\<^sup>-) \<^bold>& (L\<^sup>-) \<^bold>\<noteq> E!
        \<^bold>& (L\<^sup>-) \<^bold>\<noteq> (E!\<^sup>-) \<^bold>& E! \<^bold>\<noteq> (E!\<^sup>-) in v]"
      proof (rule "\<^bold>&I")+
        show "[L \<^bold>\<noteq> (L\<^sup>-) in v]"
        by (rule thm_relation_negation_5_1)
      next
        {
          assume "[L \<^bold>= E! in v]"
          hence "[NonContingent L \<^bold>& L \<^bold>= E! in v]"
            using thm_noncont_e_e_3 "\<^bold>&I" by auto
          hence "[\<^bold>\<exists> G . NonContingent G \<^bold>& G \<^bold>= E! in v]"
            using thm_noncont_e_e_3 "\<^bold>&I" "\<^bold>\<exists>I" by fast
        }
        thus "[L \<^bold>\<noteq> E! in v]"
          using four_distinct_2[deduction, OF thm_cont_e_2]
                modus_tollens_1 CP
          by blast
      next
        {
          assume "[L \<^bold>= (E!\<^sup>-) in v]"
          hence "[NonContingent L \<^bold>& L \<^bold>= (E!\<^sup>-) in v]"
            using thm_noncont_e_e_3 "\<^bold>&I" by auto
          hence "[\<^bold>\<exists> G . NonContingent G \<^bold>& G \<^bold>= (E!\<^sup>-) in v]"
            using thm_noncont_e_e_3 "\<^bold>&I" "\<^bold>\<exists>I" by fast
        }
        thus "[L \<^bold>\<noteq> (E!\<^sup>-) in v]"
          using four_distinct_2[deduction, OF thm_cont_e_3]
                modus_tollens_1 CP
          by blast
      next
        {
          assume "[(L\<^sup>-) \<^bold>= E! in v]"
          hence "[NonContingent (L\<^sup>-) \<^bold>& (L\<^sup>-) \<^bold>= E! in v]"
            using thm_noncont_e_e_4 "\<^bold>&I" by auto
          hence "[\<^bold>\<exists> G . NonContingent G \<^bold>& G \<^bold>= E! in v]"
            using thm_noncont_e_e_3 "\<^bold>&I" "\<^bold>\<exists>I" by fast
        }
        thus "[(L\<^sup>-) \<^bold>\<noteq> E! in v]"
          using four_distinct_2[deduction, OF thm_cont_e_2]
                modus_tollens_1 CP
          by blast
      next
        {
          assume "[(L\<^sup>-) \<^bold>= (E!\<^sup>-) in v]"
          hence "[NonContingent (L\<^sup>-) \<^bold>& (L\<^sup>-) \<^bold>= (E!\<^sup>-) in v]"
            using thm_noncont_e_e_4 "\<^bold>&I" by auto
          hence "[\<^bold>\<exists> G . NonContingent G \<^bold>& G \<^bold>= (E!\<^sup>-) in v]"
            using thm_noncont_e_e_3 "\<^bold>&I" "\<^bold>\<exists>I" by fast
        }
        thus "[(L\<^sup>-) \<^bold>\<noteq> (E!\<^sup>-) in v]"
          using four_distinct_2[deduction, OF thm_cont_e_3]
                modus_tollens_1 CP
          by blast
      next
        show "[E! \<^bold>\<noteq> (E!\<^sup>-) in v]"
          by (rule thm_relation_negation_5_1)
      qed
  end

  lemma thm_cont_propos_1[PLM]:
    "[NonContingent (p::\<o>) \<^bold>\<equiv> NonContingent (p\<^sup>-) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[NonContingent p in v]"
      hence "[\<^bold>\<box>p \<^bold>\<or> \<^bold>\<box>\<^bold>\<not>p in v]"
        unfolding NonContingent_def Necessary_defs Impossible_defs .
      hence "[\<^bold>\<box>(\<^bold>\<not>(p\<^sup>-)) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<not>p) in v]"
        apply -
        apply (PLM_subst_method "p" "\<^bold>\<not>(p\<^sup>-)")
        using thm_relation_negation_4[equiv_sym] by auto
      hence "[\<^bold>\<box>(\<^bold>\<not>(p\<^sup>-)) \<^bold>\<or> \<^bold>\<box>(p\<^sup>-) in v]"
        apply -
        apply (PLM_subst_goal_method "\<lambda>\<phi> . \<^bold>\<box>(\<^bold>\<not>(p\<^sup>-)) \<^bold>\<or> \<^bold>\<box>(\<phi>)" "\<^bold>\<not>p")
        using thm_relation_negation_3[equiv_sym] by auto
      hence "[\<^bold>\<box>(p\<^sup>-) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<not>(p\<^sup>-)) in v]"
        by (rule oth_class_taut_3_e[equiv_lr])
      thus "[NonContingent (p\<^sup>-) in v]"
        unfolding NonContingent_def Necessary_defs Impossible_defs .
    next
      assume "[NonContingent (p\<^sup>-) in v]"
      hence "[\<^bold>\<box>(\<^bold>\<not>(p\<^sup>-)) \<^bold>\<or> \<^bold>\<box>(p\<^sup>-) in v]"
        unfolding NonContingent_def Necessary_defs Impossible_defs
        by (rule oth_class_taut_3_e[equiv_lr])
      hence "[\<^bold>\<box>(p) \<^bold>\<or> \<^bold>\<box>(p\<^sup>-) in v]"
        apply -
        apply (PLM_subst_goal_method  "\<lambda>\<phi> . \<^bold>\<box>\<phi> \<^bold>\<or> \<^bold>\<box>(p\<^sup>-)" "\<^bold>\<not>(p\<^sup>-)")
        using thm_relation_negation_4 by auto
      hence "[\<^bold>\<box>(p) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<not>p) in v]"
        apply -
        apply (PLM_subst_method "p\<^sup>-" "\<^bold>\<not>p")
        using thm_relation_negation_3 by auto
      thus "[NonContingent p in v]"
        unfolding NonContingent_def Necessary_defs Impossible_defs .
    qed

  lemma thm_cont_propos_2[PLM]:
    "[Contingent p \<^bold>\<equiv> \<^bold>\<diamond>p \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>p) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[Contingent p in v]"
      hence "[\<^bold>\<not>(\<^bold>\<box>p \<^bold>\<or> \<^bold>\<box>(\<^bold>\<not>p)) in v]"
        unfolding Contingent_def Necessary_defs Impossible_defs .
      hence "[(\<^bold>\<not>\<^bold>\<box>p) \<^bold>& (\<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>p)) in v]"
        by (rule oth_class_taut_6_d[equiv_lr])
      hence "[(\<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<not>p)) \<^bold>& (\<^bold>\<diamond>\<^bold>\<not>p) in v]"
        using KBasic2_2[equiv_lr] "\<^bold>&I" "\<^bold>&E" by meson
      thus "[(\<^bold>\<diamond>p) \<^bold>& (\<^bold>\<diamond>(\<^bold>\<not>p)) in v]"
        apply - apply PLM_solver
        apply (PLM_subst_method "\<^bold>\<not>\<^bold>\<not>p" "p")
        using oth_class_taut_4_b[equiv_sym] by auto
    next
      assume "[(\<^bold>\<diamond>p) \<^bold>& (\<^bold>\<diamond>\<^bold>\<not>(p)) in v]"
      hence "[(\<^bold>\<diamond>\<^bold>\<not>(\<^bold>\<not>p)) \<^bold>& (\<^bold>\<diamond>\<^bold>\<not>(p)) in v]"
        apply - apply PLM_solver
        apply (PLM_subst_method "p" "\<^bold>\<not>\<^bold>\<not>p")
        using oth_class_taut_4_b by auto
      hence "[(\<^bold>\<not>\<^bold>\<box>p) \<^bold>& (\<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>p)) in v]"
        using KBasic2_2[equiv_rl] "\<^bold>&I" "\<^bold>&E" by meson
      hence "[\<^bold>\<not>(\<^bold>\<box>(p) \<^bold>\<or> \<^bold>\<box>(\<^bold>\<not>p)) in v]"
        by (rule oth_class_taut_6_d[equiv_rl])
      thus "[Contingent p in v]"
        unfolding Contingent_def Necessary_defs Impossible_defs .
    qed

  lemma thm_cont_propos_3[PLM]:
    "[Contingent (p::\<o>) \<^bold>\<equiv> Contingent (p\<^sup>-) in v]"
    using thm_cont_propos_1
    unfolding NonContingent_def Contingent_def
    by (rule oth_class_taut_5_d[equiv_lr])

  context
  begin
    private definition p\<^sub>0 where
      "p\<^sub>0 \<equiv> \<^bold>\<forall>x. \<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<lparr>E!,x\<^sup>P\<rparr>"

    lemma thm_noncont_propos_1[PLM]:
      "[Necessary p\<^sub>0 in v]"
      unfolding Necessary_defs p\<^sub>0_def
      apply (rule RN, rule "\<^bold>\<forall>I")
      using if_p_then_p .

    lemma thm_noncont_propos_2[PLM]:
      "[Impossible (p\<^sub>0\<^sup>-) in v]"
      unfolding Impossible_defs
      apply (PLM_subst_method "\<^bold>\<not>p\<^sub>0" "p\<^sub>0\<^sup>-")
       using thm_relation_negation_3[equiv_sym] apply simp
      apply (PLM_subst_method "p\<^sub>0" "\<^bold>\<not>\<^bold>\<not>p\<^sub>0")
       using oth_class_taut_4_b apply simp
      using thm_noncont_propos_1 unfolding Necessary_defs
      by simp

    lemma thm_noncont_propos_3[PLM]:
      "[NonContingent (p\<^sub>0) in v]"
      unfolding NonContingent_def using thm_noncont_propos_1
      by (rule "\<^bold>\<or>I"(1))

    lemma thm_noncont_propos_4[PLM]:
      "[NonContingent (p\<^sub>0\<^sup>-) in v]"
      unfolding NonContingent_def using thm_noncont_propos_2
      by (rule "\<^bold>\<or>I"(2))

    lemma thm_noncont_propos_5[PLM]:
      "[\<^bold>\<exists> (p::\<o>) q . p \<^bold>\<noteq> q \<^bold>& NonContingent p \<^bold>& NonContingent q in v]"
      apply (rule_tac \<alpha>="p\<^sub>0" in "\<^bold>\<exists>I", rule_tac \<alpha>="p\<^sub>0\<^sup>-" in "\<^bold>\<exists>I")
      using "\<^bold>\<exists>I" thm_relation_negation_6 thm_noncont_propos_3
            thm_noncont_propos_4 "\<^bold>&I" by simp

    private definition q\<^sub>0 where
      "q\<^sub>0 \<equiv> \<^bold>\<exists> x . \<lparr>E!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>)"

    lemma basic_prop_1[PLM]:
      "[\<^bold>\<exists> p . \<^bold>\<diamond>p \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>p) in v]"
      apply (rule_tac \<alpha>="q\<^sub>0" in "\<^bold>\<exists>I") unfolding q\<^sub>0_def
      using qml_4[axiom_instance] by simp

    lemma basic_prop_2[PLM]:
      "[Contingent q\<^sub>0 in v]"
      unfolding Contingent_def Necessary_defs Impossible_defs
      apply (rule oth_class_taut_6_d[equiv_rl])
      apply (PLM_subst_goal_method "\<lambda> \<phi> . (\<^bold>\<not>\<^bold>\<box>(\<phi>)) \<^bold>& \<^bold>\<not>\<^bold>\<box>\<^bold>\<not>q\<^sub>0" "\<^bold>\<not>\<^bold>\<not>q\<^sub>0")
       using oth_class_taut_4_b[equiv_sym] apply simp
      using qml_4[axiom_instance,conj_sym]
      unfolding q\<^sub>0_def diamond_def by simp

    lemma basic_prop_3[PLM]:
      "[Contingent (q\<^sub>0\<^sup>-) in v]"
      apply (rule thm_cont_propos_3[equiv_lr])
      using basic_prop_2 .

    lemma basic_prop_4[PLM]:
      "[\<^bold>\<exists> (p::\<o>) q . p \<^bold>\<noteq> q \<^bold>& Contingent p \<^bold>& Contingent q in v]"
      apply (rule_tac \<alpha>="q\<^sub>0" in "\<^bold>\<exists>I", rule_tac \<alpha>="q\<^sub>0\<^sup>-" in "\<^bold>\<exists>I")
      using thm_relation_negation_6 basic_prop_2 basic_prop_3 "\<^bold>&I" by simp

    lemma four_distinct_props_1[PLM]:
      "[NonContingent (p::\<Pi>\<^sub>0) \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<exists> q . Contingent q \<^bold>& q \<^bold>= p)) in v]"
      proof (rule CP)
        assume "[NonContingent p in v]"
        hence "[\<^bold>\<not>(Contingent p) in v]"
          unfolding NonContingent_def Contingent_def
          apply - by PLM_solver
        moreover {
           assume "[\<^bold>\<exists> q . Contingent q \<^bold>& q \<^bold>= p in v]"
           then obtain r where "[Contingent r \<^bold>& r \<^bold>= p in v]"
            by (rule "\<^bold>\<exists>E")
           hence "[Contingent p in v]"
             using "\<^bold>&E" l_identity[axiom_instance, deduction, deduction]
             by blast
        }
        ultimately show "[\<^bold>\<not>(\<^bold>\<exists>q. Contingent q \<^bold>& q \<^bold>= p) in v]"
          using modus_tollens_1 CP by blast
      qed

    lemma four_distinct_props_2[PLM]:
      "[Contingent (p::\<o>) \<^bold>\<rightarrow> \<^bold>\<not>(\<^bold>\<exists> q . (NonContingent q \<^bold>& q \<^bold>= p)) in v]"
      proof (rule CP)
        assume "[Contingent p in v]"
        hence "[\<^bold>\<not>(NonContingent p) in v]"
          unfolding NonContingent_def Contingent_def
          apply - by PLM_solver
        moreover {
           assume "[\<^bold>\<exists> q . NonContingent q \<^bold>& q \<^bold>= p in v]"
           then obtain r where "[NonContingent r \<^bold>& r \<^bold>= p in v]"
            by (rule "\<^bold>\<exists>E")
           hence "[NonContingent p in v]"
             using "\<^bold>&E" l_identity[axiom_instance, deduction, deduction]
             by blast
        }
        ultimately show "[\<^bold>\<not>(\<^bold>\<exists>q. NonContingent q \<^bold>& q \<^bold>= p) in v]"
          using modus_tollens_1 CP by blast
      qed

    lemma four_distinct_props_4[PLM]:
      "[p\<^sub>0 \<^bold>\<noteq> (p\<^sub>0\<^sup>-) \<^bold>& p\<^sub>0 \<^bold>\<noteq> q\<^sub>0 \<^bold>& p\<^sub>0 \<^bold>\<noteq> (q\<^sub>0\<^sup>-) \<^bold>& (p\<^sub>0\<^sup>-) \<^bold>\<noteq> q\<^sub>0
        \<^bold>& (p\<^sub>0\<^sup>-) \<^bold>\<noteq> (q\<^sub>0\<^sup>-) \<^bold>& q\<^sub>0 \<^bold>\<noteq> (q\<^sub>0\<^sup>-) in v]"
      proof (rule "\<^bold>&I")+
        show "[p\<^sub>0 \<^bold>\<noteq> (p\<^sub>0\<^sup>-) in v]"
          by (rule thm_relation_negation_6)
        next
          {
            assume "[p\<^sub>0 \<^bold>= q\<^sub>0 in v]"
            hence "[\<^bold>\<exists> q . NonContingent q \<^bold>& q \<^bold>= q\<^sub>0 in v]"
              using "\<^bold>&I" thm_noncont_propos_3 "\<^bold>\<exists>I"[where \<alpha>=p\<^sub>0]
              by simp
          }
          thus "[p\<^sub>0 \<^bold>\<noteq> q\<^sub>0 in v]"
            using four_distinct_props_2[deduction, OF basic_prop_2]
                  modus_tollens_1 CP
            by blast
        next
          {
            assume "[p\<^sub>0 \<^bold>= (q\<^sub>0\<^sup>-) in v]"
            hence "[\<^bold>\<exists> q . NonContingent q \<^bold>& q \<^bold>= (q\<^sub>0\<^sup>-) in v]"
              using thm_noncont_propos_3 "\<^bold>&I" "\<^bold>\<exists>I"[where \<alpha>=p\<^sub>0] by simp
          }
          thus "[p\<^sub>0 \<^bold>\<noteq> (q\<^sub>0\<^sup>-) in v]"
            using four_distinct_props_2[deduction, OF basic_prop_3]
                  modus_tollens_1 CP
          by blast
        next
          {
            assume "[(p\<^sub>0\<^sup>-) \<^bold>= q\<^sub>0 in v]"
            hence "[\<^bold>\<exists> q . NonContingent q \<^bold>& q \<^bold>= q\<^sub>0 in v]"
              using thm_noncont_propos_4 "\<^bold>&I" "\<^bold>\<exists>I"[where \<alpha>="p\<^sub>0\<^sup>-"] by auto
          }
          thus "[(p\<^sub>0\<^sup>-) \<^bold>\<noteq> q\<^sub>0 in v]"
            using four_distinct_props_2[deduction, OF basic_prop_2]
                  modus_tollens_1 CP
            by blast
        next
          {
            assume "[(p\<^sub>0\<^sup>-) \<^bold>= (q\<^sub>0\<^sup>-) in v]"
            hence "[\<^bold>\<exists> q . NonContingent q \<^bold>& q \<^bold>= (q\<^sub>0\<^sup>-) in v]"
              using thm_noncont_propos_4 "\<^bold>&I" "\<^bold>\<exists>I"[where \<alpha>="p\<^sub>0\<^sup>-"] by auto
          }
          thus "[(p\<^sub>0\<^sup>-) \<^bold>\<noteq> (q\<^sub>0\<^sup>-) in v]"
            using four_distinct_props_2[deduction, OF basic_prop_3]
                  modus_tollens_1 CP
            by blast
        next
          show "[q\<^sub>0 \<^bold>\<noteq> (q\<^sub>0\<^sup>-) in v]"
            by (rule thm_relation_negation_6)
        qed

    lemma cont_true_cont_1[PLM]:
      "[ContingentlyTrue p \<^bold>\<rightarrow> Contingent p in v]"
      apply (rule CP, rule thm_cont_propos_2[equiv_rl])
      unfolding ContingentlyTrue_def
      apply (rule "\<^bold>&I", drule "\<^bold>&E"(1))
       using "T\<^bold>\<diamond>"[deduction] apply simp
      by (rule "\<^bold>&E"(2))
  
    lemma cont_true_cont_2[PLM]:
      "[ContingentlyFalse p \<^bold>\<rightarrow> Contingent p in v]"
      apply (rule CP, rule thm_cont_propos_2[equiv_rl])
      unfolding ContingentlyFalse_def
      apply (rule "\<^bold>&I", drule "\<^bold>&E"(2))
       apply simp
      apply (drule "\<^bold>&E"(1))
      using "T\<^bold>\<diamond>"[deduction] by simp
  
    lemma cont_true_cont_3[PLM]:
      "[ContingentlyTrue p \<^bold>\<equiv> ContingentlyFalse (p\<^sup>-) in v]"
      unfolding ContingentlyTrue_def ContingentlyFalse_def
      apply (PLM_subst_method "\<^bold>\<not>p" "p\<^sup>-")
       using thm_relation_negation_3[equiv_sym] apply simp
      apply (PLM_subst_method "p" "\<^bold>\<not>\<^bold>\<not>p")
      by PLM_solver+
  
    lemma cont_true_cont_4[PLM]:
      "[ContingentlyFalse p \<^bold>\<equiv> ContingentlyTrue (p\<^sup>-) in v]"
      unfolding ContingentlyTrue_def ContingentlyFalse_def
      apply (PLM_subst_method "\<^bold>\<not>p" "p\<^sup>-")
       using thm_relation_negation_3[equiv_sym] apply simp
      apply (PLM_subst_method "p" "\<^bold>\<not>\<^bold>\<not>p")
      by PLM_solver+

    lemma cont_tf_thm_1[PLM]:
      "[ContingentlyTrue q\<^sub>0 \<^bold>\<or> ContingentlyFalse q\<^sub>0 in v]"
      proof -
        have "[q\<^sub>0 \<^bold>\<or> \<^bold>\<not>q\<^sub>0 in v]"
          by PLM_solver
        moreover {
          assume "[q\<^sub>0 in v]"
          hence "[q\<^sub>0 \<^bold>& \<^bold>\<diamond>\<^bold>\<not>q\<^sub>0 in v]"
            unfolding q\<^sub>0_def
            using qml_4[axiom_instance,conj2] "\<^bold>&I"
            by auto
        }
        moreover {
          assume "[\<^bold>\<not>q\<^sub>0 in v]"
          hence "[(\<^bold>\<not>q\<^sub>0) \<^bold>& \<^bold>\<diamond>q\<^sub>0 in v]"
            unfolding q\<^sub>0_def
            using qml_4[axiom_instance,conj1] "\<^bold>&I"
            by auto
        }
        ultimately show ?thesis
          unfolding ContingentlyTrue_def ContingentlyFalse_def
          using "\<^bold>\<or>E"(4) CP by auto
      qed

    lemma cont_tf_thm_2[PLM]:
      "[ContingentlyFalse q\<^sub>0 \<^bold>\<or> ContingentlyFalse (q\<^sub>0\<^sup>-) in v]"
      using cont_tf_thm_1 cont_true_cont_3[where p="q\<^sub>0"]
            cont_true_cont_4[where p="q\<^sub>0"]
      apply - by PLM_solver

    lemma cont_tf_thm_3[PLM]:
      "[\<^bold>\<exists> p . ContingentlyTrue p in v]"
      proof (rule "\<^bold>\<or>E"(1); (rule CP)?)
        show "[ContingentlyTrue q\<^sub>0 \<^bold>\<or> ContingentlyFalse q\<^sub>0 in v]"
          using cont_tf_thm_1 .
      next
        assume "[ContingentlyTrue q\<^sub>0 in v]"
        thus ?thesis
          using "\<^bold>\<exists>I" by metis
      next
        assume "[ContingentlyFalse q\<^sub>0 in v]"
        hence "[ContingentlyTrue (q\<^sub>0\<^sup>-) in v]"
          using cont_true_cont_4[equiv_lr] by simp
        thus ?thesis
          using "\<^bold>\<exists>I" by metis
      qed

    lemma cont_tf_thm_4[PLM]:
      "[\<^bold>\<exists> p . ContingentlyFalse p in v]"
      proof (rule "\<^bold>\<or>E"(1); (rule CP)?)
        show "[ContingentlyTrue q\<^sub>0 \<^bold>\<or> ContingentlyFalse q\<^sub>0 in v]"
          using cont_tf_thm_1 .
      next
        assume "[ContingentlyTrue q\<^sub>0 in v]"
        hence "[ContingentlyFalse (q\<^sub>0\<^sup>-) in v]"
          using cont_true_cont_3[equiv_lr] by simp
        thus ?thesis
          using "\<^bold>\<exists>I" by metis
      next
        assume "[ContingentlyFalse q\<^sub>0 in v]"
        thus ?thesis
          using "\<^bold>\<exists>I" by metis
      qed

    lemma cont_tf_thm_5[PLM]:
      "[ContingentlyTrue p \<^bold>& Necessary q \<^bold>\<rightarrow> p \<^bold>\<noteq> q in v]"
      proof (rule CP)
        assume "[ContingentlyTrue p \<^bold>& Necessary q in v]"
        hence 1: "[\<^bold>\<diamond>(\<^bold>\<not>p) \<^bold>& \<^bold>\<box> q in v]"
          unfolding ContingentlyTrue_def Necessary_defs
          using "\<^bold>&E" "\<^bold>&I" by blast
        hence "[\<^bold>\<not>\<^bold>\<box>p in v]"
          apply - apply (drule "\<^bold>&E"(1))
          unfolding diamond_def
          apply (PLM_subst_method "\<^bold>\<not>\<^bold>\<not>p" "p")
          using oth_class_taut_4_b[equiv_sym] by auto
        moreover {
          assume "[p \<^bold>= q in v]"
          hence "[\<^bold>\<box>p in v]"
            using l_identity[where \<alpha>="q" and \<beta>="p" and \<phi>="\<lambda> x . \<^bold>\<box> x",
                             axiom_instance, deduction, deduction]
                  1[conj2] id_eq_prop_prop_8_b[deduction]
            by blast
        }
        ultimately show "[p \<^bold>\<noteq> q in v]"
          using modus_tollens_1 CP by blast
      qed

    lemma cont_tf_thm_6[PLM]:
      "[(ContingentlyFalse p \<^bold>& Impossible q) \<^bold>\<rightarrow> p \<^bold>\<noteq> q in v]"
      proof (rule CP)
        assume "[ContingentlyFalse p \<^bold>& Impossible q in v]"
        hence 1: "[\<^bold>\<diamond>p \<^bold>& \<^bold>\<box>(\<^bold>\<not>q) in v]"
          unfolding ContingentlyFalse_def Impossible_defs
          using "\<^bold>&E" "\<^bold>&I" by blast
        hence "[\<^bold>\<not>\<^bold>\<diamond>q in v]"
          unfolding diamond_def apply - by PLM_solver
        moreover {
          assume "[p \<^bold>= q in v]"
          hence "[\<^bold>\<diamond>q in v]"
            using l_identity[axiom_instance, deduction, deduction] 1[conj1]
                  id_eq_prop_prop_8_b[deduction]
            by blast
        }
        ultimately show "[p \<^bold>\<noteq> q in v]"
          using modus_tollens_1 CP by blast
      qed
  end

  lemma oa_contingent_1[PLM]:
    "[O! \<^bold>\<noteq> A! in v]"
    proof -
      {
        assume "[O! \<^bold>= A! in v]"
        hence "[(\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>) in v]"
          unfolding Ordinary_def Abstract_def .
        moreover have "[\<lparr>(\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>), x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
          apply (rule beta_C_meta_1)
          by show_proper
        ultimately have "[\<lparr>(\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>), x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
          using l_identity[axiom_instance, deduction, deduction] by fast
        moreover have "[\<lparr>(\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>), x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
          apply (rule beta_C_meta_1)
          by show_proper
        ultimately have "[\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
          apply - by PLM_solver
      }
      thus ?thesis
        using oth_class_taut_1_b modus_tollens_1 CP
        by blast
    qed

  lemma oa_contingent_2[PLM]:
    "[\<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr> in v]"
    proof -
        have "[\<lparr>(\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>), x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
          apply (rule beta_C_meta_1)
          by show_proper
        hence "[(\<^bold>\<not>\<lparr>(\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>), x\<^sup>P\<rparr>) \<^bold>\<equiv> \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
          using oth_class_taut_5_d[equiv_lr] oth_class_taut_4_b[equiv_sym]
                "\<^bold>\<equiv>E"(5) by blast
        moreover have "[\<lparr>(\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>), x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
          apply (rule beta_C_meta_1)
          by show_proper
        ultimately show ?thesis
          unfolding Ordinary_def Abstract_def
          apply - by PLM_solver
    qed

  lemma oa_contingent_3[PLM]:
    "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr> in v]"
    using oa_contingent_2
    apply - by PLM_solver

  lemma oa_contingent_4[PLM]:
    "[Contingent O! in v]"
    apply (rule thm_cont_prop_2[equiv_rl], rule "\<^bold>&I")
    subgoal
      unfolding Ordinary_def
      apply (PLM_subst_method "\<lambda> x . \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>" "\<lambda> x . \<lparr>\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>")
       apply (safe intro!: beta_C_meta_1[equiv_sym])
        apply show_proper
      using "BF\<^bold>\<diamond>"[deduction, OF thm_cont_prop_2[equiv_lr, OF thm_cont_e_2, conj1]]
      by (rule "T\<^bold>\<diamond>"[deduction])
    subgoal
      apply (PLM_subst_method "\<lambda> x . \<lparr>A!,x\<^sup>P\<rparr>" "\<lambda> x . \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr>")
       using oa_contingent_3 apply simp
      using cqt_further_5[deduction,conj1, OF A_objects[axiom_instance]]
      by (rule "T\<^bold>\<diamond>"[deduction])
    done

  lemma oa_contingent_5[PLM]:
    "[Contingent A! in v]"
    apply (rule thm_cont_prop_2[equiv_rl], rule "\<^bold>&I")
    subgoal
      using cqt_further_5[deduction,conj1, OF A_objects[axiom_instance]]
      by (rule "T\<^bold>\<diamond>"[deduction])
    subgoal
      unfolding Abstract_def
      apply (PLM_subst_method "\<lambda> x . \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>" "\<lambda> x . \<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>")
       apply (safe intro!: beta_C_meta_1[equiv_sym])
        apply show_proper
      apply (PLM_subst_method "\<lambda> x . \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>" "\<lambda> x . \<^bold>\<not>\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>")
       using oth_class_taut_4_b apply simp
      using "BF\<^bold>\<diamond>"[deduction, OF thm_cont_prop_2[equiv_lr, OF thm_cont_e_2, conj1]]
      by (rule "T\<^bold>\<diamond>"[deduction])
    done

  lemma oa_contingent_6[PLM]:
    "[(O!\<^sup>-) \<^bold>\<noteq> (A!\<^sup>-) in v]"
    proof -
      {
        assume "[(O!\<^sup>-) \<^bold>= (A!\<^sup>-) in v]"
        hence "[(\<^bold>\<lambda>x. \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>x. \<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr>) in v]"
          unfolding propnot_defs .
        moreover have "[\<lparr>(\<^bold>\<lambda>x. \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr>), x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr> in v]"
          apply (rule beta_C_meta_1)
          by show_proper
        ultimately have "[\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr> \<^bold>\<equiv>  \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr> in v]"
          using l_identity[axiom_instance, deduction, deduction]
          by fast
        hence "[(\<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr>) \<^bold>\<equiv> \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr> in v]"
          apply -
          apply (PLM_subst_method "\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>" "(\<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr>)")
           apply (safe intro!: beta_C_meta_1)
          by show_proper
        hence "[\<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr> in v]"
          using oa_contingent_2 apply - by PLM_solver
      }
      thus ?thesis
        using oth_class_taut_1_b modus_tollens_1 CP
        by blast
    qed

  lemma oa_contingent_7[PLM]:
    "[\<lparr>O!\<^sup>-,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<lparr>A!\<^sup>-,x\<^sup>P\<rparr> in v]"
    proof -
      have "[(\<^bold>\<not>\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>) \<^bold>\<equiv> \<lparr>A!,x\<^sup>P\<rparr> in v]"
        apply (PLM_subst_method "(\<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr>)" "\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>")
         apply (safe intro!: beta_C_meta_1[equiv_sym])
          apply show_proper
        using oth_class_taut_4_b[equiv_sym] by auto
      moreover have "[\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr> in v]"
        apply (rule beta_C_meta_1)
        by show_proper
      ultimately show ?thesis
        unfolding propnot_defs
        using oa_contingent_3
        apply - by PLM_solver
    qed

  lemma oa_contingent_8[PLM]:
    "[Contingent (O!\<^sup>-) in v]"
    using oa_contingent_4 thm_cont_prop_3[equiv_lr] by auto

  lemma oa_contingent_9[PLM]:
    "[Contingent (A!\<^sup>-) in v]"
    using oa_contingent_5 thm_cont_prop_3[equiv_lr] by auto

  lemma oa_facts_1[PLM]:
    "[\<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>O!,x\<^sup>P\<rparr> in v]"
    proof (rule CP)
      assume "[\<lparr>O!,x\<^sup>P\<rparr> in v]"
      hence "[\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
        unfolding Ordinary_def apply -
        apply (rule beta_C_meta_1[equiv_lr])
        by show_proper
      hence "[\<^bold>\<box>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
        using qml_3[axiom_instance, deduction] by auto
      thus "[\<^bold>\<box>\<lparr>O!,x\<^sup>P\<rparr> in v]"
        unfolding Ordinary_def
        apply -
        apply (PLM_subst_method "\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>" "\<lparr>\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>")
         apply (safe intro!: beta_C_meta_1[equiv_sym])
        by show_proper
    qed

  lemma oa_facts_2[PLM]:
    "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>A!,x\<^sup>P\<rparr> in v]"
    proof (rule CP)
      assume "[\<lparr>A!,x\<^sup>P\<rparr> in v]"
      hence "[\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
        unfolding Abstract_def apply -
        apply (rule beta_C_meta_1[equiv_lr])
        by show_proper
      hence "[\<^bold>\<box>\<^bold>\<box>\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr> in v]"
        using KBasic2_4[equiv_rl] "4\<^bold>\<box>"[deduction] by auto
      hence "[\<^bold>\<box>\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
        apply -
        apply (PLM_subst_method "\<^bold>\<box>\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>" "\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>")
        using KBasic2_4 by auto
      thus "[\<^bold>\<box>\<lparr>A!,x\<^sup>P\<rparr> in v]"
        unfolding Abstract_def
        apply -
        apply (PLM_subst_method "\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>" "\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>")
         apply (safe intro!: beta_C_meta_1[equiv_sym])
        by show_proper
    qed

  lemma oa_facts_3[PLM]:
    "[\<^bold>\<diamond>\<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<lparr>O!,x\<^sup>P\<rparr> in v]"
    using oa_facts_1 by (rule derived_S5_rules_2_b)

  lemma oa_facts_4[PLM]:
    "[\<^bold>\<diamond>\<lparr>A!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<lparr>A!,x\<^sup>P\<rparr> in v]"
    using oa_facts_2 by (rule derived_S5_rules_2_b)

  lemma oa_facts_5[PLM]:
    "[\<^bold>\<diamond>\<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<box>\<lparr>O!,x\<^sup>P\<rparr> in v]"
    using oa_facts_1[deduction, OF oa_facts_3[deduction]]
      "T\<^bold>\<diamond>"[deduction, OF qml_2[axiom_instance, deduction]]
      "\<^bold>\<equiv>I" CP by blast

  lemma oa_facts_6[PLM]:
    "[\<^bold>\<diamond>\<lparr>A!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<box>\<lparr>A!,x\<^sup>P\<rparr> in v]"
    using oa_facts_2[deduction, OF oa_facts_4[deduction]]
      "T\<^bold>\<diamond>"[deduction, OF qml_2[axiom_instance, deduction]]
      "\<^bold>\<equiv>I" CP by blast

  lemma oa_facts_7[PLM]:
    "[\<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<A>\<lparr>O!,x\<^sup>P\<rparr> in v]"
    apply (rule "\<^bold>\<equiv>I"; rule CP)
     apply (rule nec_imp_act[deduction, OF oa_facts_1[deduction]]; assumption)
    proof -
      assume "[\<^bold>\<A>\<lparr>O!,x\<^sup>P\<rparr> in v]"
      hence "[\<^bold>\<A>(\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>) in v]"
        unfolding Ordinary_def  apply -
        apply (PLM_subst_method "\<lparr>\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>" "\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>")
        apply (safe intro!: beta_C_meta_1)
        by show_proper
      hence "[\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
        using Act_Basic_6[equiv_rl] by auto
      thus "[\<lparr>O!,x\<^sup>P\<rparr> in v]"
        unfolding Ordinary_def apply -
        apply (PLM_subst_method "\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>" "\<lparr>\<^bold>\<lambda>x. \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>")
         apply (safe intro!: beta_C_meta_1[equiv_sym])
        by show_proper
    qed

  lemma oa_facts_8[PLM]:
    "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<^bold>\<A>\<lparr>A!,x\<^sup>P\<rparr> in v]"
    apply (rule "\<^bold>\<equiv>I"; rule CP)
     apply (rule nec_imp_act[deduction, OF oa_facts_2[deduction]]; assumption)
    proof -
      assume "[\<^bold>\<A>\<lparr>A!,x\<^sup>P\<rparr> in v]"
      hence "[\<^bold>\<A>(\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>) in v]"
        unfolding Abstract_def apply -
        apply (PLM_subst_method "\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>" "\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>")
        apply (safe intro!: beta_C_meta_1)
        by show_proper
      hence "[\<^bold>\<A>(\<^bold>\<box>\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>) in v]"
        apply -
        apply (PLM_subst_method "(\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>)" "(\<^bold>\<box>\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>)")
        using KBasic2_4[equiv_sym] by auto
      hence "[\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
        using qml_act_2[axiom_instance, equiv_rl] KBasic2_4[equiv_lr] by auto
      thus "[\<lparr>A!,x\<^sup>P\<rparr> in v]"
        unfolding Abstract_def apply -
        apply (PLM_subst_method "\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>" "\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>")
        apply (safe intro!: beta_C_meta_1[equiv_sym])
        by show_proper
    qed

  lemma cont_nec_fact1_1[PLM]:
    "[WeaklyContingent F \<^bold>\<equiv> WeaklyContingent (F\<^sup>-) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[WeaklyContingent F in v]"
      hence wc_def: "[Contingent F \<^bold>& (\<^bold>\<forall> x . (\<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>F,x\<^sup>P\<rparr>)) in v]"
        unfolding WeaklyContingent_def .
      have "[Contingent (F\<^sup>-) in v]"
        using wc_def[conj1] by (rule thm_cont_prop_3[equiv_lr])
      moreover {
        {
          fix x
          assume "[\<^bold>\<diamond>\<lparr>F\<^sup>-,x\<^sup>P\<rparr> in v]"
          hence "[\<^bold>\<not>\<^bold>\<box>\<lparr>F,x\<^sup>P\<rparr> in v]"
            unfolding diamond_def apply -
            apply (PLM_subst_method "\<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>" "\<lparr>F,x\<^sup>P\<rparr>")
             using thm_relation_negation_2_1 by auto
          moreover {
            assume "[\<^bold>\<not>\<^bold>\<box>\<lparr>F\<^sup>-,x\<^sup>P\<rparr> in v]"
            hence "[\<^bold>\<not>\<^bold>\<box>\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>,x\<^sup>P\<rparr> in v]"
              unfolding propnot_defs .
            hence "[\<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr> in v]"
              unfolding diamond_def
              apply - apply (PLM_subst_method "\<lparr>\<^bold>\<lambda>x. \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>,x\<^sup>P\<rparr>" "\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>")
              apply (safe intro!: beta_C_meta_1)
              by show_proper
            hence "[\<^bold>\<box>\<lparr>F,x\<^sup>P\<rparr> in v]"
              using wc_def[conj2] cqt_1[axiom_instance, deduction]
                    modus_ponens by fast
          }
          ultimately have "[\<^bold>\<box>\<lparr>F\<^sup>-, x\<^sup>P\<rparr> in v]"
            using "\<^bold>\<not>\<^bold>\<not>E" modus_tollens_1 CP by blast
        }
        hence "[\<^bold>\<forall> x . \<^bold>\<diamond>\<lparr>F\<^sup>-,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>F\<^sup>-, x\<^sup>P\<rparr> in v]"
          using "\<^bold>\<forall>I" CP by fast
      }
      ultimately show "[WeaklyContingent (F\<^sup>-) in v]"
        unfolding WeaklyContingent_def by (rule "\<^bold>&I")
    next
      assume "[WeaklyContingent (F\<^sup>-) in v]"
      hence wc_def: "[Contingent (F\<^sup>-) \<^bold>& (\<^bold>\<forall> x . (\<^bold>\<diamond>\<lparr>F\<^sup>-,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>)) in v]"
        unfolding WeaklyContingent_def .
      have "[Contingent F in v]"
        using wc_def[conj1] by (rule thm_cont_prop_3[equiv_rl])
      moreover {
        {
          fix x
          assume "[\<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr> in v]"
          hence "[\<^bold>\<not>\<^bold>\<box>\<lparr>F\<^sup>-,x\<^sup>P\<rparr> in v]"
            unfolding diamond_def apply -
            apply (PLM_subst_method "\<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>" "\<lparr>F\<^sup>-,x\<^sup>P\<rparr>")
            using thm_relation_negation_1_1[equiv_sym] by auto
          moreover {
            assume "[\<^bold>\<not>\<^bold>\<box>\<lparr>F,x\<^sup>P\<rparr> in v]"
            hence "[\<^bold>\<diamond>\<lparr>F\<^sup>-,x\<^sup>P\<rparr> in v]"
              unfolding diamond_def
              apply - apply (PLM_subst_method "\<lparr>F,x\<^sup>P\<rparr>" "\<^bold>\<not>\<lparr>F\<^sup>-,x\<^sup>P\<rparr>")
              using thm_relation_negation_2_1[equiv_sym] by auto
            hence "[\<^bold>\<box>\<lparr>F\<^sup>-,x\<^sup>P\<rparr> in v]"
              using wc_def[conj2] cqt_1[axiom_instance, deduction]
                    modus_ponens by fast
          }
          ultimately have "[\<^bold>\<box>\<lparr>F, x\<^sup>P\<rparr> in v]"
            using "\<^bold>\<not>\<^bold>\<not>E" modus_tollens_1 CP by blast
        }
        hence "[\<^bold>\<forall> x . \<^bold>\<diamond>\<lparr>F,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>F, x\<^sup>P\<rparr> in v]"
          using "\<^bold>\<forall>I" CP by fast
      }
      ultimately show "[WeaklyContingent (F) in v]"
        unfolding WeaklyContingent_def by (rule "\<^bold>&I")
    qed

  lemma cont_nec_fact1_2[PLM]:
    "[(WeaklyContingent F \<^bold>& \<^bold>\<not>(WeaklyContingent G)) \<^bold>\<rightarrow> (F \<^bold>\<noteq> G) in v]"
    using l_identity[axiom_instance,deduction,deduction] "\<^bold>&E" "\<^bold>&I"
          modus_tollens_1 CP by metis

  lemma cont_nec_fact2_1[PLM]:
    "[WeaklyContingent (O!) in v]"
    unfolding WeaklyContingent_def
    apply (rule "\<^bold>&I")
     using oa_contingent_4 apply simp
    using oa_facts_5 unfolding equiv_def
    using "\<^bold>&E"(1) "\<^bold>\<forall>I" by fast

  lemma cont_nec_fact2_2[PLM]:
    "[WeaklyContingent (A!) in v]"
    unfolding WeaklyContingent_def
    apply (rule "\<^bold>&I")
     using oa_contingent_5 apply simp
    using oa_facts_6 unfolding equiv_def
    using "\<^bold>&E"(1) "\<^bold>\<forall>I" by fast

  lemma cont_nec_fact2_3[PLM]:
    "[\<^bold>\<not>(WeaklyContingent (E!)) in v]"
    proof (rule modus_tollens_1, rule CP)
      assume "[WeaklyContingent E! in v]"
      thus "[\<^bold>\<forall> x . \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr> in v]"
      unfolding WeaklyContingent_def using "\<^bold>&E"(2) by fast
    next
      {
        assume 1: "[\<^bold>\<forall> x . \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr> in v]"
        have "[\<^bold>\<exists> x . \<^bold>\<diamond>(\<lparr>E!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>)) in v]"
          using qml_4[axiom_instance,conj1, THEN BFs_3[deduction]] .
        then obtain x where "[\<^bold>\<diamond>(\<lparr>E!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>)) in v]"
          by (rule "\<^bold>\<exists>E")
        hence "[\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>) in v]"
          using KBasic2_8[deduction] S5Basic_8[deduction]
                "\<^bold>&I" "\<^bold>&E" by blast
        hence "[\<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<not>\<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr>) in v]"
          using 1[THEN "\<^bold>\<forall>E", deduction] "\<^bold>&E" "\<^bold>&I"
                KBasic2_2[equiv_rl] by blast
        hence "[\<^bold>\<not>(\<^bold>\<forall> x . \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr>) in v]"
          using oth_class_taut_1_a modus_tollens_1 CP by blast
      }
      thus "[\<^bold>\<not>(\<^bold>\<forall> x . \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>\<lparr>E!,x\<^sup>P\<rparr>) in v]"
        using reductio_aa_2 if_p_then_p CP by meson
    qed

  lemma cont_nec_fact2_4[PLM]:
    "[\<^bold>\<not>(WeaklyContingent (PLM.L)) in v]"
    proof -
      {
        assume "[WeaklyContingent PLM.L in v]"
        hence "[Contingent PLM.L in v]"
          unfolding WeaklyContingent_def using "\<^bold>&E"(1) by blast
      }
      thus ?thesis
        using thm_noncont_e_e_3
        unfolding Contingent_def NonContingent_def
        using modus_tollens_2 CP by blast
    qed

  lemma cont_nec_fact2_5[PLM]:
    "[O! \<^bold>\<noteq> E! \<^bold>& O! \<^bold>\<noteq> (E!\<^sup>-) \<^bold>& O! \<^bold>\<noteq> PLM.L \<^bold>& O! \<^bold>\<noteq> (PLM.L\<^sup>-) in v]"
    proof ((rule "\<^bold>&I")+)
      show "[O! \<^bold>\<noteq> E! in v]"
        using cont_nec_fact2_1 cont_nec_fact2_3
              cont_nec_fact1_2[deduction] "\<^bold>&I" by simp
    next
      have "[\<^bold>\<not>(WeaklyContingent (E!\<^sup>-)) in v]"
        using cont_nec_fact1_1[THEN oth_class_taut_5_d[equiv_lr], equiv_lr]
              cont_nec_fact2_3 by auto
      thus "[O! \<^bold>\<noteq> (E!\<^sup>-) in v]"
        using cont_nec_fact2_1 cont_nec_fact1_2[deduction] "\<^bold>&I" by simp
    next
      show "[O! \<^bold>\<noteq> PLM.L in v]"
        using cont_nec_fact2_1 cont_nec_fact2_4
              cont_nec_fact1_2[deduction] "\<^bold>&I" by simp
    next
      have "[\<^bold>\<not>(WeaklyContingent (PLM.L\<^sup>-)) in v]"
        using cont_nec_fact1_1[THEN oth_class_taut_5_d[equiv_lr], equiv_lr]
              cont_nec_fact2_4 by auto
      thus "[O! \<^bold>\<noteq> (PLM.L\<^sup>-) in v]"
        using cont_nec_fact2_1 cont_nec_fact1_2[deduction] "\<^bold>&I" by simp
    qed

  lemma cont_nec_fact2_6[PLM]:
    "[A! \<^bold>\<noteq> E! \<^bold>& A! \<^bold>\<noteq> (E!\<^sup>-) \<^bold>& A! \<^bold>\<noteq> PLM.L \<^bold>& A! \<^bold>\<noteq> (PLM.L\<^sup>-) in v]"
    proof ((rule "\<^bold>&I")+)
      show "[A! \<^bold>\<noteq> E! in v]"
        using cont_nec_fact2_2 cont_nec_fact2_3
              cont_nec_fact1_2[deduction] "\<^bold>&I" by simp
    next
      have "[\<^bold>\<not>(WeaklyContingent (E!\<^sup>-)) in v]"
        using cont_nec_fact1_1[THEN oth_class_taut_5_d[equiv_lr], equiv_lr]
              cont_nec_fact2_3 by auto
      thus "[A! \<^bold>\<noteq> (E!\<^sup>-) in v]"
        using cont_nec_fact2_2 cont_nec_fact1_2[deduction] "\<^bold>&I" by simp
    next
      show "[A! \<^bold>\<noteq> PLM.L in v]"
        using cont_nec_fact2_2 cont_nec_fact2_4
              cont_nec_fact1_2[deduction] "\<^bold>&I" by simp
    next
      have "[\<^bold>\<not>(WeaklyContingent (PLM.L\<^sup>-)) in v]"
        using cont_nec_fact1_1[THEN oth_class_taut_5_d[equiv_lr],
                equiv_lr] cont_nec_fact2_4 by auto
      thus "[A! \<^bold>\<noteq> (PLM.L\<^sup>-) in v]"
        using cont_nec_fact2_2 cont_nec_fact1_2[deduction] "\<^bold>&I" by simp
    qed

  lemma id_nec3_1[PLM]:
    "[((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) \<^bold>\<equiv> (\<^bold>\<box>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)))  in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[(x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P) in v]"
      hence "[\<lparr>O!,x\<^sup>P\<rparr> in v] \<and> [\<lparr>O!,y\<^sup>P\<rparr> in v] \<and> [\<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
        using eq_E_simple_1[equiv_lr] using "\<^bold>&E" by blast
      hence "[\<^bold>\<box>\<lparr>O!,x\<^sup>P\<rparr> in v] \<and> [\<^bold>\<box>\<lparr>O!,y\<^sup>P\<rparr> in v]
             \<and> [\<^bold>\<box>\<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
        using oa_facts_1[deduction] S5Basic_6[deduction] by blast
      hence "[\<^bold>\<box>(\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>)) in v]"
        using "\<^bold>&I" KBasic_3[equiv_rl] by presburger
      thus "[\<^bold>\<box>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) in v]"
        apply -
        apply (PLM_subst_method
               "(\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>))"
               "(x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)")
        using eq_E_simple_1[equiv_sym] by auto
    next
      assume "[\<^bold>\<box>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) in v]"
      thus "[((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) in v]"
      using qml_2[axiom_instance,deduction] by simp
    qed

  lemma id_nec3_2[PLM]:
    "[\<^bold>\<diamond>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) \<^bold>\<equiv> ((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[\<^bold>\<diamond>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) in v]"
      thus "[(x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P) in v]"
        using derived_S5_rules_2_b[deduction] id_nec3_1[equiv_lr]
              CP modus_ponens by blast
    next
      assume "[(x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P) in v]"
      thus "[\<^bold>\<diamond>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) in v]"
        by (rule TBasic[deduction])
    qed

  lemma thm_neg_eqE[PLM]:
    "[((x\<^sup>P) \<^bold>\<noteq>\<^sub>E (y\<^sup>P)) \<^bold>\<equiv> (\<^bold>\<not>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P))) in v]"
    proof -
      have "[(x\<^sup>P) \<^bold>\<noteq>\<^sub>E (y\<^sup>P) in v] = [\<lparr>(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . (x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)))\<^sup>-, x\<^sup>P, y\<^sup>P\<rparr> in v]"
        unfolding not_identical\<^sub>E_def by simp
      also have "... = [\<^bold>\<not>\<lparr>(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . (x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P))), x\<^sup>P, y\<^sup>P\<rparr> in v]"
        unfolding propnot_defs
        apply (safe intro!: beta_C_meta_2[equiv_lr] beta_C_meta_2[equiv_rl])
        by show_proper+
      also have "... = [\<^bold>\<not>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) in v]"
        apply (PLM_subst_method
               "\<lparr>(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . (x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P))), x\<^sup>P, y\<^sup>P\<rparr>"
               "(x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)")
         apply (safe intro!: beta_C_meta_2)
        unfolding identity_defs by show_proper
      finally show ?thesis
        using "\<^bold>\<equiv>I" CP by presburger
    qed

  lemma id_nec4_1[PLM]:
    "[((x\<^sup>P) \<^bold>\<noteq>\<^sub>E (y\<^sup>P)) \<^bold>\<equiv> \<^bold>\<box>((x\<^sup>P) \<^bold>\<noteq>\<^sub>E (y\<^sup>P)) in v]"
    proof -
      have "[(\<^bold>\<not>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P))) \<^bold>\<equiv> \<^bold>\<box>(\<^bold>\<not>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P))) in v]"
        using id_nec3_2[equiv_sym] oth_class_taut_5_d[equiv_lr]
        KBasic2_4[equiv_sym] intro_elim_6_e by fast
      thus ?thesis
        apply -
        apply (PLM_subst_method "(\<^bold>\<not>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)))" "(x\<^sup>P) \<^bold>\<noteq>\<^sub>E (y\<^sup>P)")
        using thm_neg_eqE[equiv_sym] by auto
    qed

  lemma id_nec4_2[PLM]:
    "[\<^bold>\<diamond>((x\<^sup>P) \<^bold>\<noteq>\<^sub>E (y\<^sup>P)) \<^bold>\<equiv> ((x\<^sup>P) \<^bold>\<noteq>\<^sub>E (y\<^sup>P)) in v]"
    using "\<^bold>\<equiv>I" id_nec4_1[equiv_lr] derived_S5_rules_2_b CP "T\<^bold>\<diamond>" by simp

  lemma id_act_1[PLM]:
    "[((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) \<^bold>\<equiv> (\<^bold>\<A>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P))) in v]"
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[(x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P) in v]"
      hence "[\<^bold>\<box>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) in v]"
        using id_nec3_1[equiv_lr] by auto
      thus "[\<^bold>\<A>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) in v]"
        using nec_imp_act[deduction] by fast
    next
      assume "[\<^bold>\<A>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) in v]"
      hence "[\<^bold>\<A>(\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>)) in v]"
        apply -
        apply (PLM_subst_method
               "(x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)"
               "(\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>))")
        using eq_E_simple_1 by auto
      hence "[\<^bold>\<A>\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<A>\<lparr>O!,y\<^sup>P\<rparr> \<^bold>& \<^bold>\<A>(\<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>)) in v]"
        using Act_Basic_2[equiv_lr] "\<^bold>&I" "\<^bold>&E" by meson
      thus "[(x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P) in v]"
        apply - apply (rule eq_E_simple_1[equiv_rl])
        using oa_facts_7[equiv_rl] qml_act_2[axiom_instance, equiv_rl]
              "\<^bold>&I" "\<^bold>&E" by meson
    qed

  lemma id_act_2[PLM]:
    "[((x\<^sup>P) \<^bold>\<noteq>\<^sub>E (y\<^sup>P)) \<^bold>\<equiv> (\<^bold>\<A>((x\<^sup>P) \<^bold>\<noteq>\<^sub>E (y\<^sup>P))) in v]"
    apply (PLM_subst_method "(\<^bold>\<not>((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)))" "((x\<^sup>P) \<^bold>\<noteq>\<^sub>E (y\<^sup>P))")
     using thm_neg_eqE[equiv_sym] apply simp
    using id_act_1 oth_class_taut_5_d[equiv_lr] thm_neg_eqE intro_elim_6_e
          logic_actual_nec_1[axiom_instance,equiv_sym] by meson

end

class id_act = id_eq +
  assumes id_act_prop: "[\<^bold>\<A>(\<alpha> \<^bold>= \<beta>) in v] \<Longrightarrow> [(\<alpha> \<^bold>= \<beta>) in v]"

instantiation \<nu> :: id_act
begin
  instance proof
    interpret PLM .
    fix x::\<nu> and y::\<nu> and v::i
    assume "[\<^bold>\<A>(x \<^bold>= y) in v]"
    hence "[\<^bold>\<A>(((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P)) \<^bold>\<or> (\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr>
            \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>))) in v]"
      unfolding identity_defs by auto
    hence "[\<^bold>\<A>(((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P))) \<^bold>\<or> \<^bold>\<A>((\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr>
            \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>))) in v]"
      using Act_Basic_10[equiv_lr] by auto
    moreover {
       assume "[\<^bold>\<A>(((x\<^sup>P) \<^bold>=\<^sub>E (y\<^sup>P))) in v]"
       hence "[(x\<^sup>P) \<^bold>= (y\<^sup>P) in v]"
        using id_act_1[equiv_rl] eq_E_simple_2[deduction] by auto
    }
    moreover {
       assume "[\<^bold>\<A>(\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>)) in v]"
       hence "[\<^bold>\<A>\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<A>\<lparr>A!,y\<^sup>P\<rparr> \<^bold>& \<^bold>\<A>(\<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>)) in v]"
         using Act_Basic_2[equiv_lr] "\<^bold>&I" "\<^bold>&E" by meson
       hence "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (\<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P,F\<rbrace>)) in v]"
         using oa_facts_8[equiv_rl] qml_act_2[axiom_instance,equiv_rl]
           "\<^bold>&I" "\<^bold>&E" by meson
       hence "[(x\<^sup>P) \<^bold>= (y\<^sup>P) in v]"
        unfolding identity_defs using "\<^bold>\<or>I" by auto
    }
    ultimately have "[(x\<^sup>P) \<^bold>= (y\<^sup>P) in v]"
      using intro_elim_4_a CP by meson
    thus "[x \<^bold>= y in v]"
      unfolding identity_defs by auto
  qed
end

instantiation \<Pi>\<^sub>1 :: id_act
begin
  instance proof
    interpret PLM .
    fix F::\<Pi>\<^sub>1 and G::\<Pi>\<^sub>1 and v::i
    show "[\<^bold>\<A>(F \<^bold>= G) in v] \<Longrightarrow> [(F \<^bold>= G) in v]" 
      unfolding identity_defs
      using qml_act_2[axiom_instance,equiv_rl] by auto
  qed
end

instantiation \<o> :: id_act
begin
  instance proof
    interpret PLM .
    fix p :: \<o> and q :: \<o> and v::i
    show "[\<^bold>\<A>(p \<^bold>= q) in v] \<Longrightarrow> [p \<^bold>= q in v]"
      unfolding identity\<^sub>\<o>_def using id_act_prop by blast
  qed
end

instantiation \<Pi>\<^sub>2 :: id_act
begin
  instance proof
    interpret PLM .
    fix F::\<Pi>\<^sub>2 and G::\<Pi>\<^sub>2 and v::i
    assume a: "[\<^bold>\<A>(F \<^bold>= G) in v]"
    {
      fix x
      have "[\<^bold>\<A>((\<^bold>\<lambda>y. \<lparr>F,x\<^sup>P,y\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G,x\<^sup>P,y\<^sup>P\<rparr>)
             \<^bold>& (\<^bold>\<lambda>y. \<lparr>F,y\<^sup>P,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G,y\<^sup>P,x\<^sup>P\<rparr>)) in v]"
        using a logic_actual_nec_3[axiom_instance, equiv_lr] cqt_basic_4[equiv_lr] "\<^bold>\<forall>E"
        unfolding identity\<^sub>2_def by fast
      hence "[((\<^bold>\<lambda>y. \<lparr>F,x\<^sup>P,y\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G,x\<^sup>P,y\<^sup>P\<rparr>))
              \<^bold>& ((\<^bold>\<lambda>y. \<lparr>F,y\<^sup>P,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>y. \<lparr>G,y\<^sup>P,x\<^sup>P\<rparr>)) in v]"
        using "\<^bold>&I" "\<^bold>&E" id_act_prop Act_Basic_2[equiv_lr] by metis
    }
    thus "[F \<^bold>= G in v]" unfolding identity_defs by (rule "\<^bold>\<forall>I")
  qed
end

instantiation \<Pi>\<^sub>3 :: id_act
begin
  instance proof
    interpret PLM .
    fix F::\<Pi>\<^sub>3 and G::\<Pi>\<^sub>3 and v::i
    assume a: "[\<^bold>\<A>(F \<^bold>= G) in v]"
    let ?p = "\<lambda> x y . (\<^bold>\<lambda>z. \<lparr>F,z\<^sup>P,x\<^sup>P,y\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,z\<^sup>P,x\<^sup>P,y\<^sup>P\<rparr>)
                    \<^bold>& (\<^bold>\<lambda>z. \<lparr>F,x\<^sup>P,z\<^sup>P,y\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,x\<^sup>P,z\<^sup>P,y\<^sup>P\<rparr>)
                    \<^bold>& (\<^bold>\<lambda>z. \<lparr>F,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>G,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>)"
    {
      fix x
      {
        fix y
        have "[\<^bold>\<A>(?p x y) in v]"
          using a logic_actual_nec_3[axiom_instance, equiv_lr]
                cqt_basic_4[equiv_lr] "\<^bold>\<forall>E"[where 'a=\<nu>]
          unfolding identity\<^sub>3_def by blast
        hence "[?p x y in v]"
          using "\<^bold>&I" "\<^bold>&E" id_act_prop Act_Basic_2[equiv_lr] by metis
      }
      hence "[\<^bold>\<forall> y . ?p x y in v]"
        by (rule "\<^bold>\<forall>I")
    }
    thus "[F \<^bold>= G in v]"
      unfolding identity\<^sub>3_def by (rule "\<^bold>\<forall>I")
  qed
end

context PLM
begin
  lemma id_act_3[PLM]:
    "[((\<alpha>::('a::id_act)) \<^bold>= \<beta>) \<^bold>\<equiv> \<^bold>\<A>(\<alpha> \<^bold>= \<beta>) in v]"
    using "\<^bold>\<equiv>I" CP id_nec[equiv_lr, THEN nec_imp_act[deduction]]
          id_act_prop by metis

  lemma id_act_4[PLM]:
    "[((\<alpha>::('a::id_act)) \<^bold>\<noteq> \<beta>) \<^bold>\<equiv> \<^bold>\<A>(\<alpha> \<^bold>\<noteq> \<beta>) in v]"
    using id_act_3[THEN oth_class_taut_5_d[equiv_lr]]
          logic_actual_nec_1[axiom_instance, equiv_sym]
          intro_elim_6_e by blast

  lemma id_act_desc[PLM]:
    "[(y\<^sup>P) \<^bold>= (\<^bold>\<iota>x . x \<^bold>= y) in v]"
    using descriptions[axiom_instance,equiv_rl]
          id_act_3[equiv_sym] "\<^bold>\<forall>I" by fast

  lemma eta_conversion_lemma_1[PLM]:
    "[(\<^bold>\<lambda> x . \<lparr>F,x\<^sup>P\<rparr>) \<^bold>= F in v]"
    using lambda_predicates_3_1[axiom_instance] .

  lemma eta_conversion_lemma_0[PLM]:
    "[(\<^bold>\<lambda>\<^sup>0 p) \<^bold>= p in v]"
    using lambda_predicates_3_0[axiom_instance] .

  lemma eta_conversion_lemma_2[PLM]:
    "[(\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<lparr>F,x\<^sup>P,y\<^sup>P\<rparr>)) \<^bold>= F in v]"
    using lambda_predicates_3_2[axiom_instance] .

  lemma eta_conversion_lemma_3[PLM]:
    "[(\<^bold>\<lambda>\<^sup>3 (\<lambda> x y z . \<lparr>F,x\<^sup>P,y\<^sup>P,z\<^sup>P\<rparr>)) \<^bold>= F in v]"
    using lambda_predicates_3_3[axiom_instance] .

  lemma lambda_p_q_p_eq_q[PLM]:
    "[((\<^bold>\<lambda>\<^sup>0 p) \<^bold>= (\<^bold>\<lambda>\<^sup>0 q)) \<^bold>\<equiv> (p \<^bold>= q) in v]"
    using eta_conversion_lemma_0
          l_identity[axiom_instance, deduction, deduction]
          eta_conversion_lemma_0[eq_sym] "\<^bold>\<equiv>I" CP
    by metis

subsection\<open>The Theory of Objects\<close>
text\<open>\label{TAO_PLM_Objects}\<close>

  lemma partition_1[PLM]:
    "[\<^bold>\<forall> x . \<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<or> \<lparr>A!,x\<^sup>P\<rparr> in v]"
    proof (rule "\<^bold>\<forall>I")
      fix x
      have "[\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<or> \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> in v]"
        by PLM_solver
      moreover have "[\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>\<^bold>\<lambda> y . \<^bold>\<diamond>\<lparr>E!,y\<^sup>P\<rparr>, x\<^sup>P\<rparr> in v]"
        apply (rule beta_C_meta_1[equiv_sym])
        by show_proper
      moreover have "[(\<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>) \<^bold>\<equiv> \<lparr>\<^bold>\<lambda> y . \<^bold>\<not>\<^bold>\<diamond>\<lparr>E!,y\<^sup>P\<rparr>, x\<^sup>P\<rparr> in v]"
        apply (rule beta_C_meta_1[equiv_sym])
        by show_proper
      ultimately show "[\<lparr>O!, x\<^sup>P\<rparr> \<^bold>\<or> \<lparr>A!, x\<^sup>P\<rparr> in v]"
        unfolding Ordinary_def Abstract_def by PLM_solver
    qed

  lemma partition_2[PLM]:
    "[\<^bold>\<not>(\<^bold>\<exists> x . \<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,x\<^sup>P\<rparr>) in v]"
    proof -
      {
        assume "[\<^bold>\<exists> x . \<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,x\<^sup>P\<rparr> in v]"
        then obtain b where "[\<lparr>O!,b\<^sup>P\<rparr> \<^bold>& \<lparr>A!,b\<^sup>P\<rparr> in v]"
          by (rule "\<^bold>\<exists>E")
        hence ?thesis
          using "\<^bold>&E" oa_contingent_2[equiv_lr]
                reductio_aa_2 by fast
      }
      thus ?thesis
        using reductio_aa_2 by blast
    qed

  lemma ord_eq_Eequiv_1[PLM]:
    "[\<lparr>O!,x\<rparr> \<^bold>\<rightarrow> (x \<^bold>=\<^sub>E x) in v]"
    proof (rule CP)
      assume "[\<lparr>O!,x\<rparr> in v]"
      moreover have "[\<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,x\<rparr>) in v]"
        by PLM_solver
      ultimately show "[(x) \<^bold>=\<^sub>E (x) in v]"
        using "\<^bold>&I" eq_E_simple_1[equiv_rl] by blast
    qed

  lemma ord_eq_Eequiv_2[PLM]:
    "[(x \<^bold>=\<^sub>E y) \<^bold>\<rightarrow> (y \<^bold>=\<^sub>E x) in v]"
    proof (rule CP)
      assume "[x \<^bold>=\<^sub>E y in v]"
      hence 1: "[\<lparr>O!,x\<rparr> \<^bold>& \<lparr>O!,y\<rparr> \<^bold>& \<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) in v]"
        using eq_E_simple_1[equiv_lr] by simp
      have "[\<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,x\<rparr>) in v]"
        apply (PLM_subst_method
               "\<lambda> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>"
               "\<lambda> F . \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,x\<rparr>")
        using oth_class_taut_3_g 1[conj2] by auto
      thus "[y \<^bold>=\<^sub>E x in v]"
        using eq_E_simple_1[equiv_rl] 1[conj1]
              "\<^bold>&E" "\<^bold>&I" by meson
    qed

  lemma ord_eq_Eequiv_3[PLM]:
    "[((x \<^bold>=\<^sub>E y) \<^bold>& (y \<^bold>=\<^sub>E z)) \<^bold>\<rightarrow> (x \<^bold>=\<^sub>E z) in v]"
    proof (rule CP)
      assume a: "[(x \<^bold>=\<^sub>E y) \<^bold>& (y \<^bold>=\<^sub>E z) in v]"
      have "[\<^bold>\<box>((\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) \<^bold>& (\<^bold>\<forall> F . \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>)) in v]"
        using KBasic_3[equiv_rl] a[conj1, THEN eq_E_simple_1[equiv_lr,conj2]]
              a[conj2, THEN eq_E_simple_1[equiv_lr,conj2]] "\<^bold>&I" by blast
      moreover {
        {
          fix w
          have "[((\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) \<^bold>& (\<^bold>\<forall> F . \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>))
                  \<^bold>\<rightarrow> (\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>) in w]"
            by PLM_solver
        }
        hence "[\<^bold>\<box>(((\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>) \<^bold>& (\<^bold>\<forall> F . \<lparr>F,y\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>))
                \<^bold>\<rightarrow> (\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>)) in v]"
          by (rule RN)
      }
      ultimately have "[\<^bold>\<box>(\<^bold>\<forall> F . \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,z\<rparr>) in v]"
        using qml_1[axiom_instance,deduction,deduction] by blast
      thus "[x \<^bold>=\<^sub>E z in v]"
        using a[conj1, THEN eq_E_simple_1[equiv_lr,conj1,conj1]]
        using a[conj2, THEN eq_E_simple_1[equiv_lr,conj1,conj2]]
              eq_E_simple_1[equiv_rl] "\<^bold>&I"
        by presburger
    qed

  lemma ord_eq_E_eq[PLM]:
    "[(\<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<or> \<lparr>O!,y\<^sup>P\<rparr>) \<^bold>\<rightarrow> ((x\<^sup>P \<^bold>= y\<^sup>P) \<^bold>\<equiv> (x\<^sup>P \<^bold>=\<^sub>E y\<^sup>P)) in v]"
    proof (rule CP)
      assume "[\<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<or> \<lparr>O!,y\<^sup>P\<rparr> in v]"
      moreover {
        assume "[\<lparr>O!,x\<^sup>P\<rparr> in v]"
        hence "[(x\<^sup>P \<^bold>= y\<^sup>P) \<^bold>\<equiv> (x\<^sup>P \<^bold>=\<^sub>E y\<^sup>P) in v]"
          using "\<^bold>\<equiv>I" CP l_identity[axiom_instance, deduction, deduction]
                ord_eq_Eequiv_1[deduction] eq_E_simple_2[deduction] by metis
      }
      moreover {
        assume "[\<lparr>O!,y\<^sup>P\<rparr> in v]"
        hence "[(x\<^sup>P \<^bold>= y\<^sup>P) \<^bold>\<equiv> (x\<^sup>P \<^bold>=\<^sub>E y\<^sup>P) in v]"
          using "\<^bold>\<equiv>I" CP l_identity[axiom_instance, deduction, deduction]
                ord_eq_Eequiv_1[deduction] eq_E_simple_2[deduction] id_eq_2[deduction]
                ord_eq_Eequiv_2[deduction] identity_\<nu>_def by metis
      }
      ultimately show "[(x\<^sup>P \<^bold>= y\<^sup>P) \<^bold>\<equiv> (x\<^sup>P \<^bold>=\<^sub>E y\<^sup>P) in v]"
        using intro_elim_4_a CP by blast
    qed

  lemma ord_eq_E[PLM]:
    "[(\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr>) \<^bold>\<rightarrow> ((\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) \<^bold>\<rightarrow> x\<^sup>P \<^bold>=\<^sub>E y\<^sup>P) in v]"
    proof (rule CP; rule CP)
      assume ord_xy: "[\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr> in v]"
      assume "[\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr> in v]"
      hence "[\<lparr>\<^bold>\<lambda> z . z\<^sup>P \<^bold>=\<^sub>E x\<^sup>P, x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>\<^bold>\<lambda> z . z\<^sup>P \<^bold>=\<^sub>E x\<^sup>P, y\<^sup>P\<rparr> in v]"
        by (rule "\<^bold>\<forall>E")
      moreover have "[\<lparr>\<^bold>\<lambda> z . z\<^sup>P \<^bold>=\<^sub>E x\<^sup>P, x\<^sup>P\<rparr> in v]"
        apply (rule beta_C_meta_1[equiv_rl])
        unfolding identity\<^sub>E_infix_def
         apply show_proper
        using ord_eq_Eequiv_1[deduction] ord_xy[conj1]
        unfolding identity\<^sub>E_infix_def by simp
      ultimately have "[\<lparr>\<^bold>\<lambda> z . z\<^sup>P \<^bold>=\<^sub>E x\<^sup>P, y\<^sup>P\<rparr> in v]"
        using "\<^bold>\<equiv>E" by blast
      hence "[y\<^sup>P \<^bold>=\<^sub>E x\<^sup>P in v]"
        unfolding identity\<^sub>E_infix_def
        apply (safe intro!:
            beta_C_meta_1[where \<phi> = "\<lambda> z . \<lparr>basic_identity\<^sub>E,z,x\<^sup>P\<rparr>", equiv_lr])
        by show_proper
      thus "[x\<^sup>P \<^bold>=\<^sub>E y\<^sup>P in v]"
        by (rule ord_eq_Eequiv_2[deduction])
    qed

  lemma ord_eq_E2[PLM]:
    "[(\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr>) \<^bold>\<rightarrow>
      ((x\<^sup>P \<^bold>\<noteq> y\<^sup>P) \<^bold>\<equiv> (\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E x\<^sup>P) \<^bold>\<noteq> (\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E y\<^sup>P)) in v]"
    proof (rule CP; rule "\<^bold>\<equiv>I"; rule CP)
      assume ord_xy: "[\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr> in v]"
      assume "[x\<^sup>P \<^bold>\<noteq> y\<^sup>P in v]"
      hence "[\<^bold>\<not>(x\<^sup>P \<^bold>=\<^sub>E y\<^sup>P) in v]"
        using eq_E_simple_2 modus_tollens_1 by fast
      moreover {
        assume "[(\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E x\<^sup>P) \<^bold>= (\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E y\<^sup>P) in v]"
        moreover have "[\<lparr>\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E x\<^sup>P, x\<^sup>P\<rparr> in v]"
          apply (rule beta_C_meta_1[equiv_rl])
          unfolding identity\<^sub>E_infix_def
           apply show_proper
          using ord_eq_Eequiv_1[deduction] ord_xy[conj1]
          unfolding identity\<^sub>E_infix_def by presburger
        ultimately have "[\<lparr>\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E y\<^sup>P, x\<^sup>P\<rparr> in v]"
          using l_identity[axiom_instance, deduction, deduction] by fast
        hence "[x\<^sup>P \<^bold>=\<^sub>E y\<^sup>P in v]"
          unfolding identity\<^sub>E_infix_def
          apply (safe intro!:
              beta_C_meta_1[where \<phi> = "\<lambda> z . \<lparr>basic_identity\<^sub>E,z,y\<^sup>P\<rparr>", equiv_lr])
          by show_proper
      }
      ultimately show "[(\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E x\<^sup>P) \<^bold>\<noteq> (\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E y\<^sup>P) in v]"
        using modus_tollens_1 CP by blast
    next
      assume ord_xy: "[\<lparr>O!,x\<^sup>P\<rparr> \<^bold>& \<lparr>O!,y\<^sup>P\<rparr> in v]"
      assume "[(\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E x\<^sup>P) \<^bold>\<noteq> (\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E y\<^sup>P) in v]"
      moreover {
        assume "[x\<^sup>P \<^bold>= y\<^sup>P in v]"
        hence "[(\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E x\<^sup>P) \<^bold>= (\<^bold>\<lambda>z . z\<^sup>P \<^bold>=\<^sub>E y\<^sup>P) in v]"
          using id_eq_1 l_identity[axiom_instance, deduction, deduction]
          by fast
      }
      ultimately show "[x\<^sup>P \<^bold>\<noteq> y\<^sup>P in v]"
        using modus_tollens_1 CP by blast
    qed

  lemma ab_obey_1[PLM]:
    "[(\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr>) \<^bold>\<rightarrow> ((\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P, F\<rbrace>) \<^bold>\<rightarrow> x\<^sup>P \<^bold>= y\<^sup>P) in v]"
    proof(rule CP; rule CP)
      assume abs_xy: "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> in v]"
      assume enc_equiv: "[\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P, F\<rbrace> in v]"
      {
        fix P
        have "[\<lbrace>x\<^sup>P, P\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P, P\<rbrace> in v]"
          using enc_equiv by (rule "\<^bold>\<forall>E")
        hence "[\<^bold>\<box>(\<lbrace>x\<^sup>P, P\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P, P\<rbrace>) in v]"
          using en_eq_2 intro_elim_6_e intro_elim_6_f
                en_eq_5[equiv_rl] by meson
      }
      hence "[\<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P, F\<rbrace>) in v]"
        using BF[deduction] "\<^bold>\<forall>I" by fast
      thus "[x\<^sup>P \<^bold>= y\<^sup>P in v]"
        unfolding identity_defs
        using "\<^bold>\<or>I"(2) abs_xy "\<^bold>&I" by presburger
    qed

  lemma ab_obey_2[PLM]:
    "[(\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr>) \<^bold>\<rightarrow> ((\<^bold>\<exists> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P, F\<rbrace>) \<^bold>\<rightarrow> x\<^sup>P \<^bold>\<noteq> y\<^sup>P) in v]"
    proof(rule CP; rule CP)
      assume abs_xy: "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> in v]"
      assume "[\<^bold>\<exists> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P, F\<rbrace> in v]"
      then obtain P where P_prop:
        "[\<lbrace>x\<^sup>P, P\<rbrace> \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P, P\<rbrace> in v]"
        by (rule "\<^bold>\<exists>E")
      {
        assume "[x\<^sup>P \<^bold>= y\<^sup>P in v]"
        hence "[\<lbrace>x\<^sup>P, P\<rbrace> \<^bold>\<equiv> \<lbrace>y\<^sup>P, P\<rbrace> in v]"
          using l_identity[axiom_instance, deduction, deduction]
                oth_class_taut_4_a by fast
        hence "[\<lbrace>y\<^sup>P, P\<rbrace> in v]"
          using P_prop[conj1] by (rule "\<^bold>\<equiv>E")
      }
      thus "[x\<^sup>P \<^bold>\<noteq> y\<^sup>P in v]"
        using P_prop[conj2] modus_tollens_1 CP by blast
    qed

  lemma ordnecfail[PLM]:
    "[\<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x\<^sup>P, F\<rbrace>)) in v]"
    proof (rule CP)
      assume "[\<lparr>O!,x\<^sup>P\<rparr> in v]"
      hence "[\<^bold>\<box>\<lparr>O!,x\<^sup>P\<rparr> in v]"
        using oa_facts_1[deduction] by simp
      moreover hence "[\<^bold>\<box>(\<lparr>O!,x\<^sup>P\<rparr> \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x\<^sup>P, F\<rbrace>))) in v]"
        using nocoder[axiom_necessitation, axiom_instance] by simp
      ultimately show "[\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x\<^sup>P, F\<rbrace>)) in v]"
        using qml_1[axiom_instance, deduction, deduction] by fast
    qed

  lemma o_objects_exist_1[PLM]:
    "[\<^bold>\<diamond>(\<^bold>\<exists> x . \<lparr>E!,x\<^sup>P\<rparr>) in v]"
    proof -
      have "[\<^bold>\<diamond>(\<^bold>\<exists> x . \<lparr>E!,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>)) in v]"
        using qml_4[axiom_instance, conj1] .
      hence "[\<^bold>\<diamond>((\<^bold>\<exists> x . \<lparr>E!,x\<^sup>P\<rparr>) \<^bold>& (\<^bold>\<exists> x . \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>))) in v]"
        using sign_S5_thm_3[deduction] by fast
      hence "[\<^bold>\<diamond>(\<^bold>\<exists> x . \<lparr>E!,x\<^sup>P\<rparr>) \<^bold>& \<^bold>\<diamond>(\<^bold>\<exists> x . \<^bold>\<diamond>(\<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>)) in v]"
        using KBasic2_8[deduction] by blast
      thus ?thesis using "\<^bold>&E" by blast
    qed

  lemma o_objects_exist_2[PLM]:
    "[\<^bold>\<box>(\<^bold>\<exists> x . \<lparr>O!,x\<^sup>P\<rparr>) in v]"
    apply (rule RN) unfolding Ordinary_def
    apply (PLM_subst_method  "\<lambda> x . \<^bold>\<diamond>\<lparr>E!,x\<^sup>P\<rparr>" "\<lambda> x . \<lparr>\<^bold>\<lambda>y. \<^bold>\<diamond>\<lparr>E!,y\<^sup>P\<rparr>, x\<^sup>P\<rparr>")
     apply (safe intro!: beta_C_meta_1[equiv_sym])
     apply show_proper
    using o_objects_exist_1 "BF\<^bold>\<diamond>"[deduction] by blast

  lemma o_objects_exist_3[PLM]:
    "[\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<forall> x . \<lparr>A!,x\<^sup>P\<rparr>)) in v]"
    apply (PLM_subst_method "(\<^bold>\<exists>x. \<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr>)" "\<^bold>\<not>(\<^bold>\<forall>x. \<lparr>A!,x\<^sup>P\<rparr>)")
     using cqt_further_2[equiv_sym] apply fast
    apply (PLM_subst_method "\<lambda> x . \<lparr>O!,x\<^sup>P\<rparr>" "\<lambda> x . \<^bold>\<not>\<lparr>A!,x\<^sup>P\<rparr>")
    using oa_contingent_2 o_objects_exist_2 by auto

  lemma a_objects_exist_1[PLM]:
    "[\<^bold>\<box>(\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr>) in v]"
    proof -
      {
        fix v
        have "[\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> (F \<^bold>= F)) in v]"
          using A_objects[axiom_instance] by simp
        hence "[\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr> in v]"
          using cqt_further_5[deduction,conj1] by fast
      }
      thus ?thesis by (rule RN)
    qed

  lemma a_objects_exist_2[PLM]:
    "[\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<forall> x . \<lparr>O!,x\<^sup>P\<rparr>)) in v]"
    apply (PLM_subst_method "(\<^bold>\<exists>x. \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr>)" "\<^bold>\<not>(\<^bold>\<forall>x. \<lparr>O!,x\<^sup>P\<rparr>)")
     using cqt_further_2[equiv_sym] apply fast
    apply (PLM_subst_method "\<lambda> x . \<lparr>A!,x\<^sup>P\<rparr>" "\<lambda> x . \<^bold>\<not>\<lparr>O!,x\<^sup>P\<rparr>")
     using oa_contingent_3 a_objects_exist_1 by auto

  lemma a_objects_exist_3[PLM]:
    "[\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<forall> x . \<lparr>E!,x\<^sup>P\<rparr>)) in v]"
    proof -
      {
        fix v
        have "[\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> (F \<^bold>= F)) in v]"
          using A_objects[axiom_instance] by simp
        hence "[\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr> in v]"
          using cqt_further_5[deduction,conj1] by fast
        then obtain a where
          "[\<lparr>A!,a\<^sup>P\<rparr> in v]"
          by (rule "\<^bold>\<exists>E")
        hence "[\<^bold>\<not>(\<^bold>\<diamond>\<lparr>E!,a\<^sup>P\<rparr>) in v]"
          unfolding Abstract_def
          apply (safe intro!: beta_C_meta_1[equiv_lr])
          by show_proper
        hence "[(\<^bold>\<not>\<lparr>E!,a\<^sup>P\<rparr>) in v]"
          using KBasic2_4[equiv_rl] qml_2[axiom_instance,deduction]
          by simp
        hence "[\<^bold>\<not>(\<^bold>\<forall> x . \<lparr>E!,x\<^sup>P\<rparr>) in v]"
          using "\<^bold>\<exists>I" cqt_further_2[equiv_rl]
          by fast  
      }
      thus ?thesis
        by (rule RN)
    qed

  lemma encoders_are_abstract[PLM]:
    "[(\<^bold>\<exists> F . \<lbrace>x\<^sup>P, F\<rbrace>) \<^bold>\<rightarrow> \<lparr>A!,x\<^sup>P\<rparr> in v]"
    using nocoder[axiom_instance] contraposition_2
          oa_contingent_2[THEN oth_class_taut_5_d[equiv_lr], equiv_lr]
          useful_tautologies_1[deduction]
          vdash_properties_10 CP by metis

  lemma A_objects_unique[PLM]:
    "[\<^bold>\<exists>! x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
    proof -
      have "[\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
        using A_objects[axiom_instance] by simp
      then obtain a where a_prop:
        "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>a\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]" by (rule "\<^bold>\<exists>E")
      moreover have "[\<^bold>\<forall> y . \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>y\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F) \<^bold>\<rightarrow> (y \<^bold>= a) in v]"
        proof (rule "\<^bold>\<forall>I"; rule CP)
          fix b
          assume b_prop: "[\<lparr>A!,b\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>b\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
          {
            fix P
            have "[\<lbrace>b\<^sup>P,P\<rbrace> \<^bold>\<equiv> \<lbrace>a\<^sup>P, P\<rbrace> in v]"
              using a_prop[conj2] b_prop[conj2] "\<^bold>\<equiv>I" "\<^bold>\<equiv>E"(1) "\<^bold>\<equiv>E"(2)
                    CP vdash_properties_10 "\<^bold>\<forall>E" by metis
          }
          hence "[\<^bold>\<forall> F . \<lbrace>b\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>a\<^sup>P, F\<rbrace> in v]"
            using "\<^bold>\<forall>I" by fast
          thus "[b \<^bold>= a in v]"
            unfolding identity_\<nu>_def
            using ab_obey_1[deduction, deduction]
                  a_prop[conj1] b_prop[conj1] "\<^bold>&I" by blast
        qed
      ultimately show ?thesis
        unfolding exists_unique_def
        using "\<^bold>&I" "\<^bold>\<exists>I" by fast
    qed

  lemma obj_oth_1[PLM]:
    "[\<^bold>\<exists>! x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<lparr>F, y\<^sup>P\<rparr>) in v]"
    using A_objects_unique .

  lemma obj_oth_2[PLM]:
    "[\<^bold>\<exists>! x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> (\<lparr>F, y\<^sup>P\<rparr> \<^bold>& \<lparr>F, z\<^sup>P\<rparr>)) in v]"
    using A_objects_unique .

  lemma obj_oth_3[PLM]:
    "[\<^bold>\<exists>! x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> (\<lparr>F, y\<^sup>P\<rparr> \<^bold>\<or> \<lparr>F, z\<^sup>P\<rparr>)) in v]"
    using A_objects_unique .

  lemma obj_oth_4[PLM]:
    "[\<^bold>\<exists>! x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> (\<^bold>\<box>\<lparr>F, y\<^sup>P\<rparr>)) in v]"
    using A_objects_unique .

  lemma obj_oth_5[PLM]:
    "[\<^bold>\<exists>! x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> (F \<^bold>= G)) in v]"
    using A_objects_unique .

  lemma obj_oth_6[PLM]:
    "[\<^bold>\<exists>! x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<^bold>\<box>(\<^bold>\<forall> y . \<lparr>G, y\<^sup>P\<rparr> \<^bold>\<rightarrow> \<lparr>F, y\<^sup>P\<rparr>)) in v]"
    using A_objects_unique .

  lemma A_Exists_1[PLM]:
    "[\<^bold>\<A>(\<^bold>\<exists>! x :: ('a :: id_act) . \<phi> x) \<^bold>\<equiv> (\<^bold>\<exists>! x . \<^bold>\<A>(\<phi> x)) in v]"
    unfolding exists_unique_def
    proof (rule "\<^bold>\<equiv>I"; rule CP)
      assume "[\<^bold>\<A>(\<^bold>\<exists>\<alpha>. \<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>)) in v]"
      hence "[\<^bold>\<exists>\<alpha>. \<^bold>\<A>(\<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>)) in v]"
        using Act_Basic_11[equiv_lr] by blast
      then obtain \<alpha> where
        "[\<^bold>\<A>(\<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>)) in v]"
        by (rule "\<^bold>\<exists>E")
      hence 1: "[\<^bold>\<A>(\<phi> \<alpha>) \<^bold>& \<^bold>\<A>(\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
        using Act_Basic_2[equiv_lr] by blast
      have 2: "[\<^bold>\<forall>\<beta>. \<^bold>\<A>(\<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
        using 1[conj2] logic_actual_nec_3[axiom_instance, equiv_lr] by blast
      {
        fix \<beta>
        have "[\<^bold>\<A>(\<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
          using 2 by (rule "\<^bold>\<forall>E")
        hence "[\<^bold>\<A>(\<phi> \<beta>) \<^bold>\<rightarrow> (\<beta> \<^bold>= \<alpha>) in v]"
          using logic_actual_nec_2[axiom_instance, equiv_lr, deduction]
                id_act_3[equiv_rl] CP by blast
      }
      hence "[\<^bold>\<forall> \<beta> . \<^bold>\<A>(\<phi> \<beta>) \<^bold>\<rightarrow> (\<beta> \<^bold>= \<alpha>) in v]"
        by (rule "\<^bold>\<forall>I")
      thus "[\<^bold>\<exists>\<alpha>. \<^bold>\<A>\<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>\<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
        using 1[conj1] "\<^bold>&I" "\<^bold>\<exists>I" by fast
    next
      assume "[\<^bold>\<exists>\<alpha>. \<^bold>\<A>\<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>\<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
      then obtain \<alpha> where 1:
        "[\<^bold>\<A>\<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<^bold>\<A>\<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
        by (rule "\<^bold>\<exists>E")
      {
        fix \<beta>
        have "[\<^bold>\<A>(\<phi> \<beta>) \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha> in v]"
          using 1[conj2] by (rule "\<^bold>\<forall>E")
        hence "[\<^bold>\<A>(\<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
          using logic_actual_nec_2[axiom_instance, equiv_rl] id_act_3[equiv_lr]
                vdash_properties_10 CP by blast
      }
      hence "[\<^bold>\<forall> \<beta> . \<^bold>\<A>(\<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
        by (rule "\<^bold>\<forall>I")
      hence "[\<^bold>\<A>(\<^bold>\<forall> \<beta> . \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>) in v]"
        using logic_actual_nec_3[axiom_instance, equiv_rl] by fast
      hence "[\<^bold>\<A>(\<phi> \<alpha> \<^bold>& (\<^bold>\<forall> \<beta> . \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>)) in v]"
        using 1[conj1] Act_Basic_2[equiv_rl] "\<^bold>&I" by blast
      hence "[\<^bold>\<exists>\<alpha>. \<^bold>\<A>(\<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>)) in v]"
        using "\<^bold>\<exists>I" by fast
      thus "[\<^bold>\<A>(\<^bold>\<exists>\<alpha>. \<phi> \<alpha> \<^bold>& (\<^bold>\<forall>\<beta>. \<phi> \<beta> \<^bold>\<rightarrow> \<beta> \<^bold>= \<alpha>)) in v]"
        using Act_Basic_11[equiv_rl] by fast
    qed

  lemma A_Exists_2[PLM]:
    "[(\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<phi> x)) \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<exists>!x . \<phi> x) in v]"
    using actual_desc_1 A_Exists_1[equiv_sym]
          intro_elim_6_e by blast

  lemma A_descriptions[PLM]:
    "[\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F)) in v]"
    using A_objects_unique[THEN RN, THEN nec_imp_act[deduction]]
          A_Exists_2[equiv_rl] by auto

  lemma thm_can_terms2[PLM]:
    "[(y\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F)))
      \<^bold>\<rightarrow> (\<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>y\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F)) in dw]"
    using y_in_2 by auto

  lemma can_ab2[PLM]:
    "[(y\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F))) \<^bold>\<rightarrow> \<lparr>A!,y\<^sup>P\<rparr> in v]"
    proof (rule CP)
      assume "[y\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F)) in v]"
      hence "[\<^bold>\<A>\<lparr>A!,y\<^sup>P\<rparr> \<^bold>& \<^bold>\<A>(\<^bold>\<forall> F . \<lbrace>y\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
        using nec_hintikka_scheme[equiv_lr, conj1]
              Act_Basic_2[equiv_lr] by blast
      thus "[\<lparr>A!,y\<^sup>P\<rparr> in v]"
        using oa_facts_8[equiv_rl] "\<^bold>&E" by blast
    qed

  lemma desc_encode[PLM]:
    "[\<lbrace>\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F), G\<rbrace> \<^bold>\<equiv> \<phi> G in dw]"
    proof -
      obtain a where
        "[a\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F)) in dw]"
        using A_descriptions by (rule "\<^bold>\<exists>E")
      moreover hence "[\<lbrace>a\<^sup>P, G\<rbrace> \<^bold>\<equiv> \<phi> G in dw]"
        using hintikka[equiv_lr, conj1] "\<^bold>&E" "\<^bold>\<forall>E" by fast
      ultimately show ?thesis
        using l_identity[axiom_instance, deduction, deduction] by fast
    qed

  lemma desc_nec_encode[PLM]:
    "[\<lbrace>\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F), G\<rbrace> \<^bold>\<equiv> \<^bold>\<A>(\<phi> G) in v]"
    proof -
      obtain a where
        "[a\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F)) in v]"
        using A_descriptions by (rule "\<^bold>\<exists>E")
      moreover {
        hence "[\<^bold>\<A>(\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>a\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F)) in v]"
          using nec_hintikka_scheme[equiv_lr, conj1] by fast
        hence "[\<^bold>\<A>(\<^bold>\<forall> F . \<lbrace>a\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
          using Act_Basic_2[equiv_lr,conj2] by blast
        hence "[\<^bold>\<forall> F . \<^bold>\<A>( \<lbrace>a\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
          using logic_actual_nec_3[axiom_instance, equiv_lr] by blast
        hence "[\<^bold>\<A>(\<lbrace>a\<^sup>P, G\<rbrace> \<^bold>\<equiv> \<phi> G) in v]"
          using "\<^bold>\<forall>E" by fast
        hence "[\<^bold>\<A>\<lbrace>a\<^sup>P, G\<rbrace> \<^bold>\<equiv> \<^bold>\<A>(\<phi> G) in v]"
          using Act_Basic_5[equiv_lr] by fast
        hence "[\<lbrace>a\<^sup>P, G\<rbrace> \<^bold>\<equiv> \<^bold>\<A>(\<phi> G) in v]"
          using en_eq_10[equiv_sym] intro_elim_6_e by blast
      }
      ultimately show ?thesis
        using l_identity[axiom_instance, deduction, deduction] by fast
    qed

  notepad
  begin
      fix v
      let ?x = "\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> (\<^bold>\<exists> q . q \<^bold>& F \<^bold>= (\<^bold>\<lambda> y . q)))"
      have "[\<^bold>\<box>(\<^bold>\<exists> p . ContingentlyTrue p) in v]"
        using cont_tf_thm_3 RN by auto
      hence "[\<^bold>\<A>(\<^bold>\<exists> p . ContingentlyTrue p) in v]"
        using nec_imp_act[deduction] by simp
      hence "[\<^bold>\<exists> p . \<^bold>\<A>(ContingentlyTrue p) in v]"
        using Act_Basic_11[equiv_lr] by auto
      then obtain p\<^sub>1 where
        "[\<^bold>\<A>(ContingentlyTrue p\<^sub>1) in v]"
        by (rule "\<^bold>\<exists>E")
      hence "[\<^bold>\<A>p\<^sub>1 in v]"
        unfolding ContingentlyTrue_def
        using Act_Basic_2[equiv_lr] "\<^bold>&E" by fast
      hence "[\<^bold>\<A>p\<^sub>1 \<^bold>& \<^bold>\<A>((\<^bold>\<lambda> y . p\<^sub>1) \<^bold>= (\<^bold>\<lambda> y . p\<^sub>1)) in v]"
        using "\<^bold>&I" id_eq_1[THEN RN, THEN nec_imp_act[deduction]] by fast
      hence "[\<^bold>\<A>(p\<^sub>1 \<^bold>& (\<^bold>\<lambda> y . p\<^sub>1) \<^bold>= (\<^bold>\<lambda> y . p\<^sub>1)) in v]"
        using Act_Basic_2[equiv_rl] by fast
      hence "[\<^bold>\<exists> q . \<^bold>\<A>( q \<^bold>& (\<^bold>\<lambda> y . p\<^sub>1) \<^bold>= (\<^bold>\<lambda> y . q)) in v]"
        using "\<^bold>\<exists>I" by fast
      hence "[\<^bold>\<A>(\<^bold>\<exists> q . q \<^bold>& (\<^bold>\<lambda> y . p\<^sub>1) \<^bold>= (\<^bold>\<lambda> y . q)) in v]"
        using Act_Basic_11[equiv_rl] by fast
      moreover have "[\<lbrace>?x, \<^bold>\<lambda> y . p\<^sub>1\<rbrace> \<^bold>\<equiv> \<^bold>\<A>(\<^bold>\<exists> q . q \<^bold>& (\<^bold>\<lambda> y . p\<^sub>1) \<^bold>= (\<^bold>\<lambda> y . q)) in v]"
        using desc_nec_encode by fast
      ultimately have "[\<lbrace>?x, \<^bold>\<lambda> y . p\<^sub>1\<rbrace> in v]"
        using "\<^bold>\<equiv>E" by blast
  end

  lemma Box_desc_encode_1[PLM]:
    "[\<^bold>\<box>(\<phi> G) \<^bold>\<rightarrow> \<lbrace>(\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)), G\<rbrace> in v]"
    proof (rule CP)
      assume "[\<^bold>\<box>(\<phi> G) in v]"
      hence "[\<^bold>\<A>(\<phi> G) in v]"
        using nec_imp_act[deduction] by auto
      thus "[\<lbrace>\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F), G\<rbrace> in v]"
        using desc_nec_encode[equiv_rl] by simp
    qed

  lemma Box_desc_encode_2[PLM]:
    "[\<^bold>\<box>(\<phi> G) \<^bold>\<rightarrow> \<^bold>\<box>(\<lbrace>(\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)), G\<rbrace> \<^bold>\<equiv> \<phi> G) in v]"
    proof (rule CP)
      assume a: "[\<^bold>\<box>(\<phi> G) in v]"
      hence "[\<^bold>\<box>(\<lbrace>(\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)), G\<rbrace> \<^bold>\<rightarrow> \<phi> G) in v]"
        using KBasic_1[deduction] by simp
      moreover {
        have "[\<lbrace>(\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)), G\<rbrace> in v]"
          using a Box_desc_encode_1[deduction] by auto
        hence "[\<^bold>\<box>\<lbrace>(\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)), G\<rbrace> in v]"
          using encoding[axiom_instance,deduction] by blast
        hence "[\<^bold>\<box>(\<phi> G \<^bold>\<rightarrow>  \<lbrace>(\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)), G\<rbrace>) in v]"
          using KBasic_1[deduction] by simp
      }
      ultimately show "[\<^bold>\<box>(\<lbrace>(\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)), G\<rbrace>
                        \<^bold>\<equiv> \<phi> G) in v]"
        using "\<^bold>&I" KBasic_4[equiv_rl] by blast
    qed

  lemma box_phi_a_1[PLM]:
    assumes "[\<^bold>\<box>(\<^bold>\<forall> F . \<phi> F \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> F)) in v]"
    shows "[(\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)) \<^bold>\<rightarrow> \<^bold>\<box>(\<lparr>A!,x\<^sup>P\<rparr>
            \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)) in v]"
    proof (rule CP)
      assume a: "[(\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)) in v]"
      have "[\<^bold>\<box>\<lparr>A!,x\<^sup>P\<rparr> in v]"
        using oa_facts_2[deduction] a[conj1] by auto
      moreover have "[\<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
        proof (rule BF[deduction]; rule "\<^bold>\<forall>I")
          fix F
          have \<theta>: "[\<^bold>\<box>(\<phi> F \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> F)) in v]"
            using assms[THEN CBF[deduction]] by (rule "\<^bold>\<forall>E")
          moreover have "[\<^bold>\<box>(\<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<rightarrow> \<^bold>\<box>\<lbrace>x\<^sup>P, F\<rbrace>) in v]"
            using encoding[axiom_necessitation, axiom_instance] by simp
          moreover have "[\<^bold>\<box>\<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<^bold>\<box>(\<phi> F) in v]"
            proof (rule "\<^bold>\<equiv>I"; rule CP)
              assume "[\<^bold>\<box>\<lbrace>x\<^sup>P, F\<rbrace> in v]"
              hence "[\<lbrace>x\<^sup>P, F\<rbrace> in v]"
                using qml_2[axiom_instance, deduction] by blast
              hence "[\<phi> F in v]"
                using a[conj2] "\<^bold>\<forall>E"[where 'a=\<Pi>\<^sub>1] "\<^bold>\<equiv>E" by blast
              thus "[\<^bold>\<box>(\<phi> F) in v]"
                using \<theta>[THEN qml_2[axiom_instance, deduction], deduction] by simp
            next
              assume "[\<^bold>\<box>(\<phi> F) in v]"
              hence "[\<phi> F in v]"
                using qml_2[axiom_instance, deduction] by blast
              hence "[\<lbrace>x\<^sup>P, F\<rbrace> in v]"
                using a[conj2] "\<^bold>\<forall>E"[where 'a=\<Pi>\<^sub>1] "\<^bold>\<equiv>E" by blast
              thus "[\<^bold>\<box>\<lbrace>x\<^sup>P, F\<rbrace> in v]"
                using encoding[axiom_instance, deduction] by simp
            qed
          ultimately show "[\<^bold>\<box>(\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
            using sc_eq_box_box_3[deduction, deduction] "\<^bold>&I" by blast
        qed
      ultimately show "[\<^bold>\<box>(\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<phi> F)) in v]"
       using "\<^bold>&I" KBasic_3[equiv_rl] by blast
    qed

  lemma box_phi_a_2[PLM]:
    assumes "[\<^bold>\<box>(\<^bold>\<forall> F . \<phi> F \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> F)) in v]"
    shows "[y\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F. \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F))
            \<^bold>\<rightarrow> (\<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>y\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)) in v]"
    proof -
      let ?\<psi> = "\<lambda> x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)"
      have "[\<^bold>\<forall> x . ?\<psi> x \<^bold>\<rightarrow> \<^bold>\<box>(?\<psi> x) in v]"
        using box_phi_a_1[OF assms] "\<^bold>\<forall>I" by fast
      hence "[(\<^bold>\<exists>! x . ?\<psi> x) \<^bold>\<rightarrow> (\<^bold>\<forall> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . ?\<psi> x) \<^bold>\<rightarrow> ?\<psi> y) in v]"
        using unique_box_desc[deduction] by fast
      hence "[(\<^bold>\<forall> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . ?\<psi> x) \<^bold>\<rightarrow> ?\<psi> y) in v]"
        using A_objects_unique modus_ponens by blast
      thus ?thesis by (rule "\<^bold>\<forall>E")
   qed

  lemma box_phi_a_3[PLM]:
    assumes "[\<^bold>\<box>(\<^bold>\<forall> F . \<phi> F \<^bold>\<rightarrow> \<^bold>\<box>(\<phi> F)) in v]"
    shows "[\<lbrace>\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F), G\<rbrace> \<^bold>\<equiv> \<phi> G in v]"
    proof -
      obtain a where
        "[a\<^sup>P \<^bold>= (\<^bold>\<iota>x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F)) in v]"
        using A_descriptions by (rule "\<^bold>\<exists>E")
      moreover {
        hence "[(\<^bold>\<forall> F . \<lbrace>a\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<phi> F) in v]"
          using box_phi_a_2[OF assms, deduction, conj2] by blast
        hence "[\<lbrace>a\<^sup>P, G\<rbrace> \<^bold>\<equiv> \<phi> G in v]" by (rule "\<^bold>\<forall>E")
      }
      ultimately show ?thesis
        using l_identity[axiom_instance, deduction, deduction] by fast
    qed

  lemma null_uni_uniq_1[PLM]:
    "[\<^bold>\<exists>! x . Null (x\<^sup>P) in v]"
    proof -
      have "[\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> (F \<^bold>\<noteq> F)) in v]"
        using A_objects[axiom_instance] by simp
      then obtain a where a_prop:
        "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>a\<^sup>P, F\<rbrace> \<^bold>\<equiv> (F \<^bold>\<noteq> F)) in v]"
        by (rule "\<^bold>\<exists>E")
      have 1: "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>a\<^sup>P, F\<rbrace>)) in v]"
        using a_prop[conj1] apply (rule "\<^bold>&I")
        proof -
          {
            assume "[\<^bold>\<exists> F . \<lbrace>a\<^sup>P, F\<rbrace> in v]"
            then obtain P where
              "[\<lbrace>a\<^sup>P, P\<rbrace> in v]" by (rule "\<^bold>\<exists>E")
            hence "[P \<^bold>\<noteq> P in v]"
              using a_prop[conj2, THEN "\<^bold>\<forall>E", equiv_lr] by simp
            hence "[\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>a\<^sup>P, F\<rbrace>) in v]"
              using id_eq_1 reductio_aa_1 by fast
          }
          thus "[\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>a\<^sup>P, F\<rbrace>) in v]"
            using reductio_aa_1 by blast
        qed
      moreover have "[\<^bold>\<forall> y . (\<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>y\<^sup>P, F\<rbrace>))) \<^bold>\<rightarrow> y \<^bold>= a in v]"
        proof (rule "\<^bold>\<forall>I"; rule CP)
          fix y
          assume 2: "[\<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>y\<^sup>P, F\<rbrace>)) in v]"
          have "[\<^bold>\<forall> F . \<lbrace>y\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<lbrace>a\<^sup>P, F\<rbrace> in v]"
            using cqt_further_12[deduction] 1[conj2] 2[conj2] "\<^bold>&I" by blast
          thus "[y \<^bold>= a in v]"
            using ab_obey_1[deduction, deduction]
            "\<^bold>&I"[OF 2[conj1] 1[conj1]] identity_\<nu>_def by presburger
        qed
      ultimately show ?thesis
        using "\<^bold>&I" "\<^bold>\<exists>I"
        unfolding Null_def exists_unique_def by fast
    qed

  lemma null_uni_uniq_2[PLM]:
    "[\<^bold>\<exists>! x . Universal (x\<^sup>P) in v]"
    proof -
      have "[\<^bold>\<exists> x . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<equiv> (F \<^bold>= F)) in v]"
        using A_objects[axiom_instance] by simp
      then obtain a where a_prop:
        "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>a\<^sup>P, F\<rbrace> \<^bold>\<equiv> (F \<^bold>= F)) in v]"
        by (rule "\<^bold>\<exists>E")
      have 1: "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>a\<^sup>P, F\<rbrace>) in v]"
        using a_prop[conj1] apply (rule "\<^bold>&I")
        using "\<^bold>\<forall>I" a_prop[conj2, THEN "\<^bold>\<forall>E", equiv_rl] id_eq_1 by fast
      moreover have "[\<^bold>\<forall> y . (\<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>y\<^sup>P, F\<rbrace>)) \<^bold>\<rightarrow> y \<^bold>= a in v]"
        proof (rule "\<^bold>\<forall>I"; rule CP)
          fix y
          assume 2: "[\<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>y\<^sup>P, F\<rbrace>) in v]"
          have "[\<^bold>\<forall> F . \<lbrace>y\<^sup>P, F\<rbrace> \<^bold>\<equiv> \<lbrace>a\<^sup>P, F\<rbrace> in v]"
            using cqt_further_11[deduction] 1[conj2] 2[conj2] "\<^bold>&I" by blast
          thus "[y \<^bold>= a in v]"
            using ab_obey_1[deduction, deduction]
              "\<^bold>&I"[OF 2[conj1] 1[conj1]] identity_\<nu>_def
            by presburger
        qed
      ultimately show ?thesis
        using "\<^bold>&I" "\<^bold>\<exists>I"
        unfolding Universal_def exists_unique_def by fast
    qed

  lemma null_uni_uniq_3[PLM]:
    "[\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . Null (x\<^sup>P)) in v]"
    using null_uni_uniq_1[THEN RN, THEN nec_imp_act[deduction]]
          A_Exists_2[equiv_rl] by auto

  lemma null_uni_uniq_4[PLM]:
    "[\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . Universal (x\<^sup>P)) in v]"
    using null_uni_uniq_2[THEN RN, THEN nec_imp_act[deduction]]
          A_Exists_2[equiv_rl] by auto

  lemma null_uni_facts_1[PLM]:
    "[Null (x\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<box>(Null (x\<^sup>P)) in v]"
    proof (rule CP)
      assume "[Null (x\<^sup>P) in v]"
      hence 1: "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x\<^sup>P,F\<rbrace>)) in v]"
        unfolding Null_def .
      have "[\<^bold>\<box>\<lparr>A!,x\<^sup>P\<rparr> in v]"
        using 1[conj1] oa_facts_2[deduction] by simp
      moreover have "[\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x\<^sup>P,F\<rbrace>)) in v]"
        proof -
          {
            assume "[\<^bold>\<not>\<^bold>\<box>(\<^bold>\<not>(\<^bold>\<exists> F . \<lbrace>x\<^sup>P,F\<rbrace>)) in v]"
            hence "[\<^bold>\<diamond>(\<^bold>\<exists> F . \<lbrace>x\<^sup>P,F\<rbrace>) in v]"
              unfolding diamond_def .
            hence "[\<^bold>\<exists> F . \<^bold>\<diamond>\<lbrace>x\<^sup>P,F\<rbrace> in v]"
              using "BF\<^bold>\<diamond>"[deduction] by blast
            then obtain P where "[\<^bold>\<diamond>\<lbrace>x\<^sup>P,P\<rbrace> in v]"
              by (rule "\<^bold>\<exists>E")
            hence "[\<lbrace>x\<^sup>P, P\<rbrace> in v]"
              using en_eq_3[equiv_lr] by simp
            hence "[\<^bold>\<exists>  F . \<lbrace>x\<^sup>P, F\<rbrace> in v]"
              using "\<^bold>\<exists>I" by fast
          }
          thus ?thesis
            using 1[conj2] modus_tollens_1 CP
                  useful_tautologies_1[deduction] by metis
        qed
      ultimately show "[\<^bold>\<box>Null (x\<^sup>P) in v]"
        unfolding Null_def
        using "\<^bold>&I" KBasic_3[equiv_rl] by blast
    qed

  lemma null_uni_facts_2[PLM]:
    "[Universal (x\<^sup>P) \<^bold>\<rightarrow> \<^bold>\<box>(Universal (x\<^sup>P)) in v]"
    proof (rule CP)
      assume "[Universal (x\<^sup>P) in v]"
      hence 1: "[\<lparr>A!,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace>) in v]"
        unfolding Universal_def .
      have "[\<^bold>\<box>\<lparr>A!,x\<^sup>P\<rparr> in v]"
        using 1[conj1] oa_facts_2[deduction] by simp
      moreover have "[\<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x\<^sup>P,F\<rbrace>) in v]"
        proof (rule BF[deduction]; rule "\<^bold>\<forall>I")
          fix F
          have "[\<lbrace>x\<^sup>P, F\<rbrace> in v]"
            using 1[conj2] by (rule "\<^bold>\<forall>E")
          thus "[\<^bold>\<box>\<lbrace>x\<^sup>P, F\<rbrace> in v]"
            using encoding[axiom_instance, deduction] by auto
        qed
      ultimately show "[\<^bold>\<box>Universal (x\<^sup>P) in v]"
        unfolding Universal_def
        using "\<^bold>&I" KBasic_3[equiv_rl] by blast
    qed

  lemma null_uni_facts_3[PLM]:
    "[Null (\<^bold>a\<^sub>\<emptyset>) in v]"
    proof -
      let ?\<psi> = "\<lambda> x . Null x"
      have "[((\<^bold>\<exists>! x . ?\<psi> (x\<^sup>P)) \<^bold>\<rightarrow> (\<^bold>\<forall> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . ?\<psi> (x\<^sup>P)) \<^bold>\<rightarrow> ?\<psi> (y\<^sup>P))) in v]"
        using unique_box_desc[deduction] null_uni_facts_1[THEN "\<^bold>\<forall>I"] by fast
      have 1: "[(\<^bold>\<forall> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . ?\<psi> (x\<^sup>P)) \<^bold>\<rightarrow> ?\<psi> (y\<^sup>P)) in v]"
        using unique_box_desc[deduction, deduction] null_uni_uniq_1
              null_uni_facts_1[THEN "\<^bold>\<forall>I"] by fast
      have "[\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>a\<^sub>\<emptyset>) in v]"
        unfolding NullObject_def using null_uni_uniq_3 .
      then obtain y where "[y\<^sup>P \<^bold>= (\<^bold>a\<^sub>\<emptyset>) in v]"
        by (rule "\<^bold>\<exists>E")
      moreover hence "[?\<psi> (y\<^sup>P) in v]"
        using 1[THEN "\<^bold>\<forall>E", deduction] unfolding NullObject_def by simp
      ultimately show "[?\<psi> (\<^bold>a\<^sub>\<emptyset>) in v]"
        using l_identity[axiom_instance, deduction, deduction] by blast
    qed

  lemma null_uni_facts_4[PLM]:
    "[Universal (\<^bold>a\<^sub>V) in v]"
    proof -
      let ?\<psi> = "\<lambda> x . Universal x"
      have "[((\<^bold>\<exists>! x . ?\<psi> (x\<^sup>P)) \<^bold>\<rightarrow> (\<^bold>\<forall> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . ?\<psi> (x\<^sup>P)) \<^bold>\<rightarrow> ?\<psi> (y\<^sup>P))) in v]"
        using unique_box_desc[deduction] null_uni_facts_2[THEN "\<^bold>\<forall>I"] by fast
      have 1: "[(\<^bold>\<forall> y . y\<^sup>P \<^bold>= (\<^bold>\<iota>x . ?\<psi> (x\<^sup>P)) \<^bold>\<rightarrow> ?\<psi> (y\<^sup>P)) in v]"
        using unique_box_desc[deduction, deduction] null_uni_uniq_2
              null_uni_facts_2[THEN "\<^bold>\<forall>I"] by fast
      have "[\<^bold>\<exists> y . y\<^sup>P \<^bold>= (\<^bold>a\<^sub>V) in v]"
        unfolding UniversalObject_def using null_uni_uniq_4 .
      then obtain y where "[y\<^sup>P \<^bold>= (\<^bold>a\<^sub>V) in v]"
        by (rule "\<^bold>\<exists>E")
      moreover hence "[?\<psi> (y\<^sup>P) in v]"
        using 1[THEN "\<^bold>\<forall>E", deduction]
        unfolding UniversalObject_def by simp
      ultimately show "[?\<psi> (\<^bold>a\<^sub>V) in v]"
        using l_identity[axiom_instance, deduction, deduction] by blast
    qed

  lemma aclassical_1[PLM]:
    "[\<^bold>\<forall> R . \<^bold>\<exists> x y . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (x \<^bold>\<noteq> y)
      \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,y\<^sup>P\<rparr>) in v]"
    proof (rule "\<^bold>\<forall>I")
      fix R
      obtain a where \<theta>:
        "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>a\<^sup>P, F\<rbrace> \<^bold>\<equiv> (\<^bold>\<exists> y . \<lparr>A!,y\<^sup>P\<rparr>
          \<^bold>& F \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,y\<^sup>P\<rparr>) \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P, F\<rbrace>)) in v]"
        using A_objects[axiom_instance] by (rule "\<^bold>\<exists>E")
      {
        assume "[\<^bold>\<not>\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>)\<rbrace> in v]"
        hence "[\<^bold>\<not>(\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>)
                \<^bold>& \<^bold>\<not>\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>)\<rbrace>) in v]"
          using \<theta>[conj2, THEN "\<^bold>\<forall>E", THEN oth_class_taut_5_d[equiv_lr], equiv_lr]
                cqt_further_4[equiv_lr] "\<^bold>\<forall>E" by fast
        hence "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>)
                \<^bold>\<rightarrow> \<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>)\<rbrace> in v]"
          apply - by PLM_solver
        hence "[\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>)\<rbrace> in v]"
          using \<theta>[conj1] id_eq_1 "\<^bold>&I" vdash_properties_10 by fast
      }
      hence 1: "[\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>)\<rbrace> in v]"
        using reductio_aa_1 CP if_p_then_p by blast
      then obtain b where \<xi>:
        "[\<lparr>A!,b\<^sup>P\<rparr> \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,b\<^sup>P\<rparr>)
          \<^bold>& \<^bold>\<not>\<lbrace>b\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>)\<rbrace> in v]"
        using \<theta>[conj2, THEN "\<^bold>\<forall>E", equiv_lr] "\<^bold>\<exists>E" by blast
      have "[a \<^bold>\<noteq> b in v]"
        proof -
          {
            assume "[a \<^bold>= b in v]"
            hence "[\<lbrace>b\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>)\<rbrace> in v]"
              using 1 l_identity[axiom_instance, deduction, deduction] by fast
            hence ?thesis
              using \<xi>[conj2] reductio_aa_1 by blast
          }
          thus ?thesis using reductio_aa_1 by blast
        qed
      hence "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& \<lparr>A!,b\<^sup>P\<rparr> \<^bold>& a \<^bold>\<noteq> b
              \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,z\<^sup>P,b\<^sup>P\<rparr>) in v]"
        using \<theta>[conj1] \<xi>[conj1, conj1] \<xi>[conj1, conj2] "\<^bold>&I" by presburger
      hence "[\<^bold>\<exists> y . \<lparr>A!,a\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& a \<^bold>\<noteq> y
              \<^bold>& (\<^bold>\<lambda>z. \<lparr>R,z\<^sup>P,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>R,z\<^sup>P,y\<^sup>P\<rparr>) in v]"
        using "\<^bold>\<exists>I" by fast
      thus "[\<^bold>\<exists> x y . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y
             \<^bold>& (\<^bold>\<lambda>z. \<lparr>R,z\<^sup>P,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>R,z\<^sup>P,y\<^sup>P\<rparr>) in v]"
        using "\<^bold>\<exists>I" by fast
    qed

  lemma aclassical_2[PLM]:
    "[\<^bold>\<forall> R . \<^bold>\<exists> x y . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (x \<^bold>\<noteq> y)
      \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,x\<^sup>P,z\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,y\<^sup>P,z\<^sup>P\<rparr>) in v]"
    proof (rule "\<^bold>\<forall>I")
      fix R
      obtain a where \<theta>:
        "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>a\<^sup>P, F\<rbrace> \<^bold>\<equiv> (\<^bold>\<exists> y . \<lparr>A!,y\<^sup>P\<rparr>
          \<^bold>& F \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,y\<^sup>P,z\<^sup>P\<rparr>) \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P, F\<rbrace>)) in v]"
        using A_objects[axiom_instance] by (rule "\<^bold>\<exists>E")
      {
        assume "[\<^bold>\<not>\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>)\<rbrace> in v]"
        hence "[\<^bold>\<not>(\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>)
                \<^bold>& \<^bold>\<not>\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>)\<rbrace>) in v]"
          using \<theta>[conj2, THEN "\<^bold>\<forall>E", THEN oth_class_taut_5_d[equiv_lr], equiv_lr]
                cqt_further_4[equiv_lr] "\<^bold>\<forall>E" by fast
        hence "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>)
                \<^bold>\<rightarrow> \<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>)\<rbrace> in v]"
          apply - by PLM_solver
        hence "[\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>)\<rbrace> in v]"
          using \<theta>[conj1] id_eq_1 "\<^bold>&I" vdash_properties_10 by fast
      }
      hence 1: "[\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>)\<rbrace> in v]"
        using reductio_aa_1 CP if_p_then_p by blast
      then obtain b where \<xi>:
        "[\<lparr>A!,b\<^sup>P\<rparr> \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,b\<^sup>P,z\<^sup>P\<rparr>)
          \<^bold>& \<^bold>\<not>\<lbrace>b\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>)\<rbrace> in v]"
        using \<theta>[conj2, THEN "\<^bold>\<forall>E", equiv_lr] "\<^bold>\<exists>E" by blast
      have "[a \<^bold>\<noteq> b in v]"
        proof -
          {
            assume "[a \<^bold>= b in v]"
            hence "[\<lbrace>b\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>)\<rbrace> in v]"
              using 1 l_identity[axiom_instance, deduction, deduction] by fast
            hence ?thesis using \<xi>[conj2] reductio_aa_1 by blast
          }
          thus ?thesis using \<xi>[conj2] reductio_aa_1 by blast
        qed
      hence "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& \<lparr>A!,b\<^sup>P\<rparr> \<^bold>& a \<^bold>\<noteq> b
              \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,b\<^sup>P,z\<^sup>P\<rparr>) in v]"
        using \<theta>[conj1] \<xi>[conj1, conj1] \<xi>[conj1, conj2] "\<^bold>&I" by presburger
      hence "[\<^bold>\<exists> y . \<lparr>A!,a\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& a \<^bold>\<noteq> y
              \<^bold>& (\<^bold>\<lambda>z. \<lparr>R,a\<^sup>P,z\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>R,y\<^sup>P,z\<^sup>P\<rparr>) in v]"
        using "\<^bold>\<exists>I" by fast
      thus "[\<^bold>\<exists> x y . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y
             \<^bold>& (\<^bold>\<lambda>z. \<lparr>R,x\<^sup>P,z\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>R,y\<^sup>P,z\<^sup>P\<rparr>) in v]"
        using "\<^bold>\<exists>I" by fast
    qed

  lemma aclassical_3[PLM]:
    "[\<^bold>\<forall> F . \<^bold>\<exists> x y . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& (x \<^bold>\<noteq> y)
      \<^bold>& ((\<^bold>\<lambda>\<^sup>0 \<lparr>F,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>\<^sup>0 \<lparr>F,y\<^sup>P\<rparr>)) in v]"
    proof (rule "\<^bold>\<forall>I")
      fix R
      obtain a where \<theta>:
        "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<forall> F . \<lbrace>a\<^sup>P, F\<rbrace> \<^bold>\<equiv> (\<^bold>\<exists> y . \<lparr>A!,y\<^sup>P\<rparr>
          \<^bold>& F \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,y\<^sup>P\<rparr>) \<^bold>& \<^bold>\<not>\<lbrace>y\<^sup>P, F\<rbrace>)) in v]"
        using A_objects[axiom_instance] by (rule "\<^bold>\<exists>E")
      {
        assume "[\<^bold>\<not>\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>)\<rbrace> in v]"
        hence "[\<^bold>\<not>(\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>)
                \<^bold>& \<^bold>\<not>\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>)\<rbrace>) in v]"
          using \<theta>[conj2, THEN "\<^bold>\<forall>E", THEN oth_class_taut_5_d[equiv_lr], equiv_lr]
                cqt_further_4[equiv_lr] "\<^bold>\<forall>E" by fast
        hence "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>)
                \<^bold>\<rightarrow> \<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>)\<rbrace> in v]"
          apply - by PLM_solver
        hence "[\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>)\<rbrace> in v]"
          using \<theta>[conj1] id_eq_1 "\<^bold>&I" vdash_properties_10 by fast
      }
      hence 1: "[\<lbrace>a\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>)\<rbrace> in v]"
        using reductio_aa_1 CP if_p_then_p by blast
      then obtain b where \<xi>:
        "[\<lparr>A!,b\<^sup>P\<rparr> \<^bold>& (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda> z . \<lparr>R,b\<^sup>P\<rparr>)
          \<^bold>& \<^bold>\<not>\<lbrace>b\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>)\<rbrace> in v]"
        using \<theta>[conj2, THEN "\<^bold>\<forall>E", equiv_lr] "\<^bold>\<exists>E" by blast
      have "[a \<^bold>\<noteq> b in v]"
        proof -
          {
            assume "[a \<^bold>= b in v]"
            hence "[\<lbrace>b\<^sup>P, (\<^bold>\<lambda> z . \<lparr>R,a\<^sup>P\<rparr>)\<rbrace> in v]"
              using 1 l_identity[axiom_instance, deduction, deduction] by fast
            hence ?thesis
              using \<xi>[conj2] reductio_aa_1 by blast
          }
          thus ?thesis using reductio_aa_1 by blast
        qed
      moreover {
        have "[\<lparr>R,a\<^sup>P\<rparr> \<^bold>= \<lparr>R,b\<^sup>P\<rparr> in v]"
          unfolding identity\<^sub>\<o>_def
          using \<xi>[conj1, conj2] by auto
        hence "[(\<^bold>\<lambda>\<^sup>0 \<lparr>R,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>\<^sup>0 \<lparr>R,b\<^sup>P\<rparr>) in v]"
          using lambda_p_q_p_eq_q[equiv_rl] by simp
      }
      ultimately have "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& \<lparr>A!,b\<^sup>P\<rparr> \<^bold>& a \<^bold>\<noteq> b
                \<^bold>& ((\<^bold>\<lambda>\<^sup>0 \<lparr>R,a\<^sup>P\<rparr>) \<^bold>=(\<^bold>\<lambda>\<^sup>0 \<lparr>R,b\<^sup>P\<rparr>)) in v]"
        using \<theta>[conj1] \<xi>[conj1, conj1] \<xi>[conj1, conj2] "\<^bold>&I"
        by presburger
      hence "[\<^bold>\<exists> y . \<lparr>A!,a\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& a \<^bold>\<noteq> y
              \<^bold>& (\<^bold>\<lambda>\<^sup>0 \<lparr>R,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>\<^sup>0 \<lparr>R,y\<^sup>P\<rparr>) in v]"
        using "\<^bold>\<exists>I" by fast
      thus "[\<^bold>\<exists> x y . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y
             \<^bold>& (\<^bold>\<lambda>\<^sup>0 \<lparr>R,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>\<^sup>0 \<lparr>R,y\<^sup>P\<rparr>) in v]"
        using "\<^bold>\<exists>I" by fast
    qed

  lemma aclassical2[PLM]:
    "[\<^bold>\<exists> x y . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y \<^bold>& (\<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
    proof -
      let ?R\<^sub>1 = "\<^bold>\<lambda>\<^sup>2 (\<lambda> x y . \<^bold>\<forall> F . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>)"
      have "[\<^bold>\<exists> x y . \<lparr>A!,x\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& x \<^bold>\<noteq> y
             \<^bold>& (\<^bold>\<lambda>z. \<lparr>?R\<^sub>1,z\<^sup>P,x\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>?R\<^sub>1,z\<^sup>P,y\<^sup>P\<rparr>) in v]"
        using aclassical_1 by (rule "\<^bold>\<forall>E")
      then obtain a where
        "[\<^bold>\<exists> y . \<lparr>A!,a\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& a \<^bold>\<noteq> y
          \<^bold>& (\<^bold>\<lambda>z. \<lparr>?R\<^sub>1,z\<^sup>P,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>?R\<^sub>1,z\<^sup>P,y\<^sup>P\<rparr>) in v]"
        by (rule "\<^bold>\<exists>E")
      then obtain b where ab_prop:
        "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& \<lparr>A!,b\<^sup>P\<rparr> \<^bold>& a \<^bold>\<noteq> b
          \<^bold>& (\<^bold>\<lambda>z. \<lparr>?R\<^sub>1,z\<^sup>P,a\<^sup>P\<rparr>) \<^bold>= (\<^bold>\<lambda>z. \<lparr>?R\<^sub>1,z\<^sup>P,b\<^sup>P\<rparr>) in v]"
        by (rule "\<^bold>\<exists>E")
      have "[\<lparr>?R\<^sub>1, a\<^sup>P, a\<^sup>P\<rparr> in v]"
        apply (rule beta_C_meta_2[equiv_rl])
         apply show_proper
        using oth_class_taut_4_a[THEN "\<^bold>\<forall>I"] by fast
      hence "[\<lparr>\<^bold>\<lambda> z . \<lparr>?R\<^sub>1, z\<^sup>P, a\<^sup>P\<rparr>, a\<^sup>P\<rparr> in v]"
        apply - apply (rule beta_C_meta_1[equiv_rl])
         apply show_proper
        by auto
      hence "[\<lparr>\<^bold>\<lambda> z . \<lparr>?R\<^sub>1, z\<^sup>P, b\<^sup>P\<rparr>, a\<^sup>P\<rparr> in v]"
        using ab_prop[conj2] l_identity[axiom_instance, deduction, deduction]
        by fast
      hence "[\<lparr>?R\<^sub>1, a\<^sup>P, b\<^sup>P\<rparr> in v]"
        apply (safe intro!: beta_C_meta_1[where \<phi>=
               "\<lambda>z . \<lparr>\<^bold>\<lambda>\<^sup>2 (\<lambda>x y. \<^bold>\<forall>F. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>),z,b\<^sup>P\<rparr>", equiv_lr])
        by show_proper
      moreover have "IsProperInXY (\<lambda>x y. \<^bold>\<forall>F. \<lparr>F,x\<rparr> \<^bold>\<equiv> \<lparr>F,y\<rparr>)"
        by show_proper
      ultimately have "[\<^bold>\<forall>F. \<lparr>F,a\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,b\<^sup>P\<rparr> in v]"
        using beta_C_meta_2[equiv_lr] by blast
      hence "[\<lparr>A!,a\<^sup>P\<rparr> \<^bold>& \<lparr>A!,b\<^sup>P\<rparr> \<^bold>& a \<^bold>\<noteq> b \<^bold>& (\<^bold>\<forall>F. \<lparr>F,a\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,b\<^sup>P\<rparr>) in v]"
        using ab_prop[conj1] "\<^bold>&I" by presburger
      hence "[\<^bold>\<exists> y . \<lparr>A!,a\<^sup>P\<rparr> \<^bold>& \<lparr>A!,y\<^sup>P\<rparr> \<^bold>& a \<^bold>\<noteq> y \<^bold>& (\<^bold>\<forall>F. \<lparr>F,a\<^sup>P\<rparr> \<^bold>\<equiv> \<lparr>F,y\<^sup>P\<rparr>) in v]"
        using "\<^bold>\<exists>I" by fast
      thus ?thesis using "\<^bold>\<exists>I" by fast
    qed

subsection\<open>Propositional Properties\<close>
text\<open>\label{TAO_PLM_PropositionalProperties}\<close>

  lemma prop_prop2_1:
    "[\<^bold>\<forall> p . \<^bold>\<exists> F . F \<^bold>= (\<^bold>\<lambda> x . p) in v]"
    proof (rule "\<^bold>\<forall>I")
      fix p
      have "[(\<^bold>\<lambda> x . p) \<^bold>= (\<^bold>\<lambda> x . p) in v]"
        using id_eq_prop_prop_1 by auto
      thus "[\<^bold>\<exists>  F . F \<^bold>= (\<^bold>\<lambda> x . p) in v]"
        by PLM_solver
    qed

  lemma prop_prop2_2:
    "[F \<^bold>= (\<^bold>\<lambda> x . p) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall> x . \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> p) in v]"
    proof (rule CP)
      assume 1: "[F \<^bold>= (\<^bold>\<lambda> x . p) in v]"
      {
        fix v
        {
          fix x
          have "[\<lparr>(\<^bold>\<lambda> x . p), x\<^sup>P\<rparr> \<^bold>\<equiv> p in v]"
            apply (rule beta_C_meta_1)
            by show_proper
        }
        hence "[\<^bold>\<forall> x . \<lparr>(\<^bold>\<lambda> x . p), x\<^sup>P\<rparr> \<^bold>\<equiv> p in v]"
          by (rule "\<^bold>\<forall>I")
      }
      hence "[\<^bold>\<box>(\<^bold>\<forall> x . \<lparr>(\<^bold>\<lambda> x . p), x\<^sup>P\<rparr> \<^bold>\<equiv> p) in v]"
        by (rule RN)
      thus "[\<^bold>\<box>(\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr> \<^bold>\<equiv> p) in v]"
        using l_identity[axiom_instance,deduction,deduction,
              OF 1[THEN id_eq_prop_prop_2[deduction]]] by fast
    qed

  lemma prop_prop2_3:
    "[Propositional F \<^bold>\<rightarrow> \<^bold>\<box>(Propositional F) in v]"
    proof (rule CP)
      assume "[Propositional F in v]"
      hence "[\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p) in v]"
        unfolding Propositional_def .
      then obtain q where "[F \<^bold>= (\<^bold>\<lambda> x . q) in v]"
        by (rule "\<^bold>\<exists>E")
      hence "[\<^bold>\<box>(F \<^bold>= (\<^bold>\<lambda> x . q)) in v]"
        using id_nec[equiv_lr] by auto
      hence "[\<^bold>\<exists> p . \<^bold>\<box>(F \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
        using "\<^bold>\<exists>I" by fast
      thus "[\<^bold>\<box>(Propositional F) in v]"
        unfolding Propositional_def
        using sign_S5_thm_1[deduction] by fast
    qed


  lemma prop_indis:
    "[Indiscriminate F \<^bold>\<rightarrow> (\<^bold>\<not>(\<^bold>\<exists> x y . \<lparr>F,x\<^sup>P\<rparr> \<^bold>& (\<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr>))) in v]"
    proof (rule CP)
      assume "[Indiscriminate F in v]"
      hence 1: "[\<^bold>\<box>((\<^bold>\<exists>x. \<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<rightarrow> (\<^bold>\<forall>x. \<lparr>F,x\<^sup>P\<rparr>)) in v]"
        unfolding Indiscriminate_def .
      {
        assume "[\<^bold>\<exists> x y . \<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr> in v]"
        then obtain x where "[\<^bold>\<exists> y . \<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr> in v]"
          by (rule "\<^bold>\<exists>E")
        then obtain y where 2: "[\<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr> in v]"
          by (rule "\<^bold>\<exists>E")
        hence "[\<^bold>\<exists> x . \<lparr>F, x\<^sup>P\<rparr> in v]"
          using "\<^bold>&E"(1) "\<^bold>\<exists>I" by fast
        hence "[\<^bold>\<forall> x . \<lparr>F,x\<^sup>P\<rparr> in v]"
          using 1[THEN qml_2[axiom_instance, deduction], deduction] by fast
        hence "[\<lparr>F,y\<^sup>P\<rparr> in v]"
          using cqt_orig_1[deduction] by fast
        hence "[\<lparr>F,y\<^sup>P\<rparr> \<^bold>& (\<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr>) in v]"
          using 2 "\<^bold>&I" "\<^bold>&E" by fast
        hence "[\<^bold>\<not>(\<^bold>\<exists> x y . \<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr>) in v]"
          using pl_1[axiom_instance, deduction, THEN modus_tollens_1]
                oth_class_taut_1_a by blast
      }
      thus "[\<^bold>\<not>(\<^bold>\<exists> x y . \<lparr>F,x\<^sup>P\<rparr> \<^bold>& \<^bold>\<not>\<lparr>F,y\<^sup>P\<rparr>) in v]"
        using reductio_aa_2 if_p_then_p deduction_theorem by blast
    qed


  lemma prop_in_thm:
    "[Propositional F \<^bold>\<rightarrow> Indiscriminate F in v]"
    proof (rule CP)
      assume "[Propositional F in v]"
      hence "[\<^bold>\<box>(Propositional F) in v]"
        using prop_prop2_3[deduction] by auto
      moreover {
        fix w
        assume "[\<^bold>\<exists> p . (F \<^bold>= (\<^bold>\<lambda> y . p)) in w]"
        then obtain q where q_prop: "[F \<^bold>= (\<^bold>\<lambda> y . q) in w]"
          by (rule "\<^bold>\<exists>E")
        {
          assume "[\<^bold>\<exists> x . \<lparr>F,x\<^sup>P\<rparr> in w]"
          then obtain a where "[\<lparr>F,a\<^sup>P\<rparr> in w]"
            by (rule "\<^bold>\<exists>E")
          hence "[\<lparr>\<^bold>\<lambda> y . q, a\<^sup>P\<rparr> in w]"
            using q_prop l_identity[axiom_instance,deduction,deduction] by fast
          hence q: "[q in w]"
            apply (safe intro!: beta_C_meta_1[where \<phi>="\<lambda>y. q", equiv_lr])
             apply show_proper
            by simp
          {
            fix x
            have "[\<lparr>\<^bold>\<lambda> y . q, x\<^sup>P\<rparr> in w]"
              apply (safe intro!: q beta_C_meta_1[equiv_rl])
              by show_proper
            hence "[\<lparr>F,x\<^sup>P\<rparr> in w]"
              using q_prop[eq_sym] l_identity[axiom_instance, deduction, deduction]
              by fast
          }
          hence "[\<^bold>\<forall> x . \<lparr>F,x\<^sup>P\<rparr> in w]"
            by (rule "\<^bold>\<forall>I")
        }
        hence "[(\<^bold>\<exists> x . \<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<rightarrow> (\<^bold>\<forall> x . \<lparr>F, x\<^sup>P\<rparr>) in w]"
          by (rule CP)
      }
      ultimately show "[Indiscriminate F in v]"
        unfolding Propositional_def Indiscriminate_def
        using RM_1[deduction] deduction_theorem by blast
    qed

  lemma prop_in_f_1:
    "[Necessary F \<^bold>\<rightarrow> Indiscriminate F in v]"
    unfolding Necessary_defs Indiscriminate_def
    using pl_1[axiom_instance, THEN RM_1] by simp

  lemma prop_in_f_2:
    "[Impossible F \<^bold>\<rightarrow> Indiscriminate F in v]"
    proof -
      {
        fix w
        have "[(\<^bold>\<not>(\<^bold>\<exists> x . \<lparr>F,x\<^sup>P\<rparr>)) \<^bold>\<rightarrow> ((\<^bold>\<exists> x . \<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<rightarrow> (\<^bold>\<forall> x . \<lparr>F,x\<^sup>P\<rparr>)) in w]"
          using useful_tautologies_3 by auto
        hence "[(\<^bold>\<forall> x . \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<rightarrow> ((\<^bold>\<exists> x . \<lparr>F,x\<^sup>P\<rparr>) \<^bold>\<rightarrow> (\<^bold>\<forall> x . \<lparr>F,x\<^sup>P\<rparr>)) in w]"
          apply - apply (PLM_subst_method "\<^bold>\<not>(\<^bold>\<exists> x. \<lparr>F,x\<^sup>P\<rparr>)" "(\<^bold>\<forall> x. \<^bold>\<not>\<lparr>F,x\<^sup>P\<rparr>)")
          using cqt_further_4 unfolding exists_def by fast+
      }
      thus ?thesis
        unfolding Impossible_defs Indiscriminate_def using RM_1 CP by blast
    qed

  lemma prop_in_f_3_a:
    "[\<^bold>\<not>(Indiscriminate (E!)) in v]"
    proof (rule reductio_aa_2)
      show "[\<^bold>\<box>\<^bold>\<not>(\<^bold>\<forall>x. \<lparr>E!,x\<^sup>P\<rparr>) in v]"
        using a_objects_exist_3 .
    next
      assume "[Indiscriminate E! in v]"
      thus "[\<^bold>\<not>\<^bold>\<box>\<^bold>\<not>(\<^bold>\<forall> x . \<lparr>E!,x\<^sup>P\<rparr>) in v]"
        unfolding Indiscriminate_def
        using o_objects_exist_1 KBasic2_5[deduction,deduction]
        unfolding diamond_def by blast
    qed

  lemma prop_in_f_3_b:
    "[\<^bold>\<not>(Indiscriminate (E!\<^sup>-)) in v]"
    proof (rule reductio_aa_2)
      assume "[Indiscriminate (E!\<^sup>-) in v]"
      moreover have "[\<^bold>\<box>(\<^bold>\<exists> x . \<lparr>E!\<^sup>-, x\<^sup>P\<rparr>) in v]"
        apply (PLM_subst_method "\<lambda> x . \<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>" "\<lambda> x . \<lparr>E!\<^sup>-, x\<^sup>P\<rparr>")
         using thm_relation_negation_1_1[equiv_sym] apply simp
        unfolding exists_def
        apply (PLM_subst_method "\<lambda> x . \<lparr>E!, x\<^sup>P\<rparr>" "\<lambda> x . \<^bold>\<not>\<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>")
         using oth_class_taut_4_b apply simp
        using a_objects_exist_3 by auto
      ultimately have "[\<^bold>\<box>(\<^bold>\<forall>x. \<lparr>E!\<^sup>-,x\<^sup>P\<rparr>) in v]"
        unfolding Indiscriminate_def
        using qml_1[axiom_instance, deduction, deduction] by blast
      thus "[\<^bold>\<box>(\<^bold>\<forall>x. \<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>) in v]"
        apply -
        apply (PLM_subst_method "\<lambda> x . \<lparr>E!\<^sup>-, x\<^sup>P\<rparr>" "\<lambda> x . \<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>")
        using thm_relation_negation_1_1 by auto
    next
      show "[\<^bold>\<not>\<^bold>\<box>(\<^bold>\<forall> x . \<^bold>\<not>\<lparr>E!, x\<^sup>P\<rparr>) in v]"
        using o_objects_exist_1
        unfolding diamond_def exists_def
        apply -
        apply (PLM_subst_method "\<^bold>\<not>\<^bold>\<not>(\<^bold>\<forall>x. \<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>)" "\<^bold>\<forall>x. \<^bold>\<not>\<lparr>E!,x\<^sup>P\<rparr>")
        using oth_class_taut_4_b[equiv_sym] by auto
    qed

  lemma prop_in_f_3_c:
    "[\<^bold>\<not>(Indiscriminate (O!)) in v]"
    proof (rule reductio_aa_2)
      show "[\<^bold>\<not>(\<^bold>\<forall> x . \<lparr>O!,x\<^sup>P\<rparr>) in v]"
        using a_objects_exist_2[THEN qml_2[axiom_instance, deduction]]
              by blast
    next
      assume "[Indiscriminate O! in v]"
      thus "[(\<^bold>\<forall> x . \<lparr>O!,x\<^sup>P\<rparr>) in v]"
        unfolding Indiscriminate_def
        using o_objects_exist_2 qml_1[axiom_instance, deduction, deduction]
              qml_2[axiom_instance, deduction] by blast
    qed

  lemma prop_in_f_3_d:
    "[\<^bold>\<not>(Indiscriminate (A!)) in v]"
    proof (rule reductio_aa_2)
      show "[\<^bold>\<not>(\<^bold>\<forall> x . \<lparr>A!,x\<^sup>P\<rparr>) in v]"
        using o_objects_exist_3[THEN qml_2[axiom_instance, deduction]]
              by blast
    next
      assume "[Indiscriminate A! in v]"
      thus "[(\<^bold>\<forall> x . \<lparr>A!,x\<^sup>P\<rparr>) in v]"
        unfolding Indiscriminate_def
        using a_objects_exist_1 qml_1[axiom_instance, deduction, deduction]
              qml_2[axiom_instance, deduction] by blast
    qed

  lemma prop_in_f_4_a:
    "[\<^bold>\<not>(Propositional E!) in v]"
    using prop_in_thm[deduction] prop_in_f_3_a modus_tollens_1 CP
    by meson

  lemma prop_in_f_4_b:
    "[\<^bold>\<not>(Propositional (E!\<^sup>-)) in v]"
    using prop_in_thm[deduction] prop_in_f_3_b modus_tollens_1 CP
    by meson

  lemma prop_in_f_4_c:
    "[\<^bold>\<not>(Propositional (O!)) in v]"
    using prop_in_thm[deduction] prop_in_f_3_c modus_tollens_1 CP
    by meson

  lemma prop_in_f_4_d:
    "[\<^bold>\<not>(Propositional (A!)) in v]"
    using prop_in_thm[deduction] prop_in_f_3_d modus_tollens_1 CP
    by meson

  lemma prop_prop_nec_1:
    "[\<^bold>\<diamond>(\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p)) \<^bold>\<rightarrow> (\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
    proof (rule CP)
      assume "[\<^bold>\<diamond>(\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
      hence "[\<^bold>\<exists> p . \<^bold>\<diamond>(F \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
        using "BF\<^bold>\<diamond>"[deduction] by auto
      then obtain p where "[\<^bold>\<diamond>(F \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
        by (rule "\<^bold>\<exists>E")
      hence "[\<^bold>\<diamond>\<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace>) in v]"
        unfolding identity_defs .
      hence "[\<^bold>\<box>(\<^bold>\<forall>x. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<equiv> \<lbrace>x\<^sup>P,\<^bold>\<lambda>x. p\<rbrace>) in v]"
        using "5\<^bold>\<diamond>"[deduction] by auto
      hence "[(F \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
        unfolding identity_defs .
      thus "[\<^bold>\<exists> p . (F \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
        by PLM_solver
    qed

  lemma prop_prop_nec_2:
    "[(\<^bold>\<forall> p . F \<^bold>\<noteq> (\<^bold>\<lambda> x . p)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall> p . F \<^bold>\<noteq> (\<^bold>\<lambda> x . p)) in v]"
    apply (PLM_subst_method
           "\<^bold>\<not>(\<^bold>\<exists>  p . (F \<^bold>= (\<^bold>\<lambda> x . p)))"
           "(\<^bold>\<forall> p . \<^bold>\<not>(F \<^bold>= (\<^bold>\<lambda> x . p)))")
     using cqt_further_4 apply blast
    apply (PLM_subst_method
           "\<^bold>\<not>\<^bold>\<diamond>(\<^bold>\<exists>p. F \<^bold>= (\<^bold>\<lambda>x. p))"
           "\<^bold>\<box>\<^bold>\<not>(\<^bold>\<exists>p. F \<^bold>= (\<^bold>\<lambda>x. p))")
     using KBasic2_4[equiv_sym] prop_prop_nec_1
           contraposition_1 by auto

  lemma prop_prop_nec_3:
    "[(\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p)) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p)) in v]"
    using prop_prop_nec_1 derived_S5_rules_1_b by simp

  lemma prop_prop_nec_4:
    "[\<^bold>\<diamond>(\<^bold>\<forall> p . F \<^bold>\<noteq> (\<^bold>\<lambda> x . p)) \<^bold>\<rightarrow> (\<^bold>\<forall> p . F \<^bold>\<noteq> (\<^bold>\<lambda> x . p)) in v]"
    using prop_prop_nec_2 derived_S5_rules_2_b by simp

  lemma enc_prop_nec_1:
    "[\<^bold>\<diamond>(\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<rightarrow> (\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p)))
      \<^bold>\<rightarrow> (\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<rightarrow> (\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p))) in v]"
    proof (rule CP)
      assume "[\<^bold>\<diamond>(\<^bold>\<forall>F. \<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<rightarrow> (\<^bold>\<exists>p. F \<^bold>= (\<^bold>\<lambda>x. p))) in v]"
      hence 1: "[(\<^bold>\<forall>F. \<^bold>\<diamond>(\<lbrace>x\<^sup>P,F\<rbrace> \<^bold>\<rightarrow> (\<^bold>\<exists>p. F \<^bold>= (\<^bold>\<lambda>x. p)))) in v]"
        using "Buridan\<^bold>\<diamond>"[deduction] by auto
      {
        fix Q
        assume "[\<lbrace>x\<^sup>P,Q\<rbrace> in v]"
        hence "[\<^bold>\<box>\<lbrace>x\<^sup>P,Q\<rbrace> in v]"
          using encoding[axiom_instance, deduction] by auto
        moreover have "[\<^bold>\<diamond>(\<lbrace>x\<^sup>P,Q\<rbrace> \<^bold>\<rightarrow> (\<^bold>\<exists>p. Q \<^bold>= (\<^bold>\<lambda>x. p))) in v]"
          using cqt_1[axiom_instance, deduction] 1 by fast
        ultimately have "[\<^bold>\<diamond>(\<^bold>\<exists>p. Q \<^bold>= (\<^bold>\<lambda>x. p)) in v]"
          using KBasic2_9[equiv_lr,deduction] by auto
        hence "[(\<^bold>\<exists>p. Q \<^bold>= (\<^bold>\<lambda>x. p)) in v]"
          using prop_prop_nec_1[deduction] by auto
      }
      thus "[(\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<rightarrow> (\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p))) in v]"
        apply - by PLM_solver
    qed

  lemma enc_prop_nec_2:
    "[(\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace> \<^bold>\<rightarrow> (\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p))) \<^bold>\<rightarrow> \<^bold>\<box>(\<^bold>\<forall> F . \<lbrace>x\<^sup>P, F\<rbrace>
      \<^bold>\<rightarrow> (\<^bold>\<exists> p . F \<^bold>= (\<^bold>\<lambda> x . p))) in v]"
    using derived_S5_rules_1_b enc_prop_nec_1 by blast
end
end
