section \<open>Refinement and Simulation\<close>

theory Refinement
imports Denotational_Semantics Circus_Syntax 
begin


subsection \<open>Definitions\<close>

text \<open>In the following, data (state) simulation and functional backwards simulation
 are defined. The simulation is defined as a function $S$, that corresponds to a state 
 abstraction function.\<close>

definition "Simul S b = extend (make (ok b) (wait b) (tr b) (ref b)) (S (more b))"

definition 
Simulation::"('\<theta>::ev_eq,'\<sigma>) action \<Rightarrow> ('\<sigma>1 \<Rightarrow> '\<sigma>) \<Rightarrow> ('\<theta>, '\<sigma>1) action \<Rightarrow> bool" ("_ \<preceq>_ _") 
where
"A \<preceq>S B \<equiv> \<forall> a b. (relation_of B) (a, b) \<longrightarrow> (relation_of A) (Simul S a, Simul S b)"

subsection \<open>Proofs\<close>

text \<open>In order to simplify refinement proofs, some general refinement laws are 
defined to deal with the refinement of Circus actions at operators level and not at UTP level. 
Using these laws, and exploiting the advantages of a shallow embedding, the automated proof of
refinement becomes surprisingly simple.\<close>

lemma Stop_Sim: "Stop \<preceq>S Stop"
by (auto simp: Simulation_def relation_of_Stop rp_defs design_defs Simul_def alpha_rp.defs 
         split: cond_splits)

lemma Skip_Sim: "Skip \<preceq>S Skip"
by (auto simp: Simulation_def relation_of_Skip design_def rp_defs Simul_def alpha_rp.defs 
         split: cond_splits)

lemma Chaos_Sim: "Chaos \<preceq>S Chaos"
by (auto simp: Simulation_def relation_of_Chaos rp_defs design_defs Simul_def alpha_rp.defs 
         split: cond_splits)

lemma Ndet_Sim:
  assumes A: "P  \<preceq>S Q" and B: "P' \<preceq>S Q'"
  shows "(P \<sqinter> P') \<preceq>S (Q \<sqinter> Q')"
by (insert A B, auto simp: Simulation_def relation_of_Ndet)

lemma Det_Sim:
  assumes A: "P  \<preceq>S Q" and B: "P' \<preceq>S Q'"
  shows "(P \<box> P') \<preceq>S (Q \<box> Q')"
by (auto simp: Simulation_def relation_of_Det design_def rp_defs Simul_def alpha_rp.defs spec_def
         split: cond_splits
         dest: A[simplified Simulation_def Simul_def, rule_format]
               B[simplified Simulation_def Simul_def, rule_format])

lemma Schema_Sim:
  assumes A: "\<And> a. (Pre sc1) (S a) \<Longrightarrow> (Pre sc2) a"
  and B: "\<And> a b. \<lbrakk>Pre sc1 (S a) ; sc2 (a, b)\<rbrakk> \<Longrightarrow> sc1 (S a, S b)"
  shows "(Schema sc1) \<preceq>S (Schema sc2)"
by (auto simp: Simulation_def Simul_def relation_of_Schema rp_defs design_defs alpha_rp.defs A B
         split: cond_splits)

lemma SUb_Sim:
  assumes A: "\<And> a. (Pre sc1) (S a) \<Longrightarrow> (Pre sc2) a"
  and B: "\<And> a b. \<lbrakk>Pre sc1 (S a) ; sc2 (a, b)\<rbrakk> \<Longrightarrow> sc1 (S a, S b)"
  and C: "P \<preceq>S Q"
  shows "(state_update_before sc1 P) \<preceq>S (state_update_before sc2 Q)"
apply (auto simp: Simulation_def Simul_def relation_of_state_update_before rp_defs design_defs alpha_rp.defs A B
         split: cond_splits)
apply (drule C[simplified Simulation_def, rule_format])
apply (rule_tac b="Simul S ba" in comp_intro)
apply (auto simp: A B Simul_def alpha_rp.defs)
apply (clarsimp split: cond_splits)+
apply (drule C[simplified Simulation_def, rule_format])
apply (rule_tac b="Simul S ba" in comp_intro)
apply (auto simp: A B Simul_def alpha_rp.defs)
apply (clarsimp split: cond_splits)+
apply (case_tac "ok aa", simp_all)
apply (erule notE) back
apply (drule C[simplified Simulation_def, rule_format])
apply (rule_tac b="Simul S ba" in comp_intro)
apply (auto simp: A B Simul_def alpha_rp.defs)
apply (clarsimp split: cond_splits)+
apply (rule A)
apply (case_tac "Pre sc1 (S (alpha_rp.more aa))", simp_all)
apply (erule notE) back
apply (drule C[simplified Simulation_def, rule_format])
apply (rule_tac b="Simul S ba" in comp_intro)
apply (auto simp: A B Simul_def alpha_rp.defs)
apply (clarsimp split: cond_splits)+
apply (drule C[simplified Simulation_def, rule_format])
apply (rule_tac b="Simul S ba" in comp_intro)
apply (auto simp: A B Simul_def alpha_rp.defs)
apply (clarsimp split: cond_splits)+
apply (rule B, auto)
done

lemma Seq_Sim:
  assumes A: "P \<preceq>S Q" and B: "P' \<preceq>S Q'"
  shows "(P `;` P') \<preceq>S (Q `;` Q')"
by (auto simp: Simulation_def relation_of_Seq dest: A[simplified Simulation_def, rule_format]
                                                    B[simplified Simulation_def, rule_format])


lemma Par_Sim:
  assumes A: " P  \<preceq>S Q" and B: " P' \<preceq>S Q'"
  and C: "\<And> a b. S (ns'2 a b) = ns2 (S a) (S b)"
  and D: "\<And> a b. S (ns'1 a b) = ns1 (S a) (S b)"
  shows "(P \<lbrakk> ns1 | cs | ns2 \<rbrakk> P') \<preceq>S (Q \<lbrakk> ns'1 | cs | ns'2 \<rbrakk> Q')"
  apply (auto simp: Simulation_def relation_of_Par fun_eq_iff rp_defs Simul_def design_defs spec_def
                    alpha_rp.defs
              dest: A[simplified Simulation_def Simul_def, rule_format] 
                    B[simplified Simulation_def Simul_def, rule_format])
  apply (split cond_splits)+
  apply (simp, erule disjE, rule disjI1, simp, rule disjI2, simp_all, rule impI)
  apply (auto)
  apply (erule_tac x="tr ba" in allE, auto)
  apply (erule notE) back
  apply (rule_tac b="Simul S ba\<lparr>ok := False\<rparr>" in comp_intro)
  apply (auto simp: Simul_def alpha_rp.defs dest: A[simplified Simulation_def Simul_def, rule_format])
  apply (erule_tac x="tr bb" in allE, auto)
  apply (erule notE) back
  apply (rule_tac b="Simul S bb\<lparr>ok := False\<rparr>" in comp_intro)
  apply (auto simp: Simul_def alpha_rp.defs dest: B[simplified Simulation_def Simul_def, rule_format])
  apply (erule_tac x="tr ba" in allE, auto)
  apply (erule notE) back
  apply (rule_tac b="Simul S ba\<lparr>ok := False\<rparr>" in comp_intro)
  apply (auto simp: Simul_def alpha_rp.defs dest: A[simplified Simulation_def Simul_def, rule_format])
  apply (erule_tac x="tr bb" in allE, auto)
  apply (erule notE) back
  apply (rule_tac b="Simul S bb\<lparr>ok := False\<rparr>" in comp_intro)
  apply (auto simp: Simul_def alpha_rp.defs dest: B[simplified Simulation_def Simul_def, rule_format])
  apply (rule_tac x="Simul S s1" in exI)
  apply (rule_tac x="Simul S s2" in exI)
  apply (auto simp: Simul_def alpha_rp.defs 
              dest!: B[simplified Simulation_def Simul_def, rule_format]
                     A[simplified Simulation_def Simul_def, rule_format]
              split: cond_splits)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (auto simp add: M_par_def alpha_rp.defs diff_tr_def fun_eq_iff ParMerge_def Simul_def
            split : cond_splits)
  apply (rule_tac b="\<lparr>ok = ok bb, wait = wait bb, tr = tr bb, ref = ref bb, 
              \<dots> = S (alpha_rp.more bb)\<rparr>" in comp_intro, auto)
  apply (subst D[where a="(alpha_rp.more s1)" and b="(alpha_rp.more aa)", symmetric], simp)
  apply (subst C[where a="(alpha_rp.more s2)" and b="(alpha_rp.more bb)", symmetric], simp)
  apply (rule_tac b="\<lparr>ok = ok bb, wait = wait bb, tr = tr bb, ref = ref bb, 
              \<dots> = S (alpha_rp.more bb)\<rparr>" in comp_intro, auto)
  apply (subst D[where a="(alpha_rp.more s1)" and b="(alpha_rp.more aa)", symmetric], simp)
  apply (subst C[where a="(alpha_rp.more s2)" and b="(alpha_rp.more bb)", symmetric], simp)
done

lemma Assign_Sim:
  assumes A: "\<And> A. vy A = vx (S A)"
  and B: "\<And> ff A. (S (y_update ff A)) = x_update ff (S A)"
  shows "(x `:=` vx) \<preceq>S (y `:=` vy)"
by (auto simp: Simulation_def relation_of_Assign update_def rp_defs design_defs Simul_def A B
                   alpha_rp.defs split: cond_splits)

lemma Var_Sim:
  assumes A: "P \<preceq>S Q" and B: "\<And> ff A. (S ((snd b) ff A)) = (snd a) ff (S A)"
  shows "(Var a P) \<preceq>S (Var b Q)"
  apply (auto simp: Simulation_def relation_of_Var rp_defs design_defs fun_eq_iff Simul_def B
                    alpha_rp.defs increase_def decrease_def)
  apply (rule_tac b="Simul S ab" in comp_intro)
  apply (split cond_splits)+
  apply (auto simp: B alpha_rp.defs Simul_def elim!: alpha_rp_eqE)
  apply (rule_tac b="Simul S bb" in comp_intro)
  apply (split cond_splits)+
  apply (auto simp: B alpha_rp.defs Simul_def 
              elim!: alpha_rp_eqE dest!: A[simplified Simulation_def Simul_def, rule_format])
  apply (split cond_splits)+
  apply (simp add: alpha_rp.defs)
  apply (erule disjE, rule disjI1, simp, rule disjI2, simp)
  apply (simp_all add: alpha_rp.defs true_def)
  apply (rule impI, (erule conjE | simp)+)
  apply (simp add: B)
  apply (split cond_splits)+
  apply (simp add: alpha_rp.defs)
  apply (erule disjE, rule disjI1, simp, rule disjI2, simp_all)
  apply (rule impI, (erule conjE | simp)+)
  apply (simp add: B)
done

lemma Guard_Sim:
  assumes A: "P \<preceq>S Q" and B: "\<And> A. h A = g (S A)"
  shows "(g `&` P) \<preceq>S (h `&` Q)"
apply (auto simp: Simulation_def)
apply (case_tac "h (alpha_rp.more a)")
defer
apply (case_tac "g (S (alpha_rp.more a))")
apply (auto simp: true_Guard1 false_Guard1 Simul_def alpha_rp.defs Simulation_def B
            dest!: A[simplified, rule_format] Stop_Sim[simplified, rule_format])
done

lemma Write0_Sim:
  assumes A: "P \<preceq>S Q"
  shows "a \<rightarrow> P \<preceq>S a \<rightarrow> Q "
  using   A
  apply (auto simp: Simulation_def write0_def relation_of_Prefix0 design_defs rp_defs)
  apply (erule_tac x="ba" in allE)
  apply (erule_tac x="c" in allE, auto)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (auto split: cond_splits simp: Simul_def alpha_rp.defs do_def)
done

lemma Read_Sim:
  assumes A: " P \<preceq>S Q" and B: "\<And> A. (d A) = c (S A)"
  shows "a`?`c \<rightarrow> P \<preceq>S a`?`d \<rightarrow> Q"
  using A
  apply (auto simp: Simulation_def read_def relation_of_iPrefix design_defs rp_defs)
  apply (erule_tac x="ba" in allE, erule_tac x="ca" in allE, simp)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (auto split: cond_splits simp: Simul_def alpha_rp.defs do_I_def select_def B)
done

lemma Read1_Sim:
  assumes A: " P \<preceq>S Q" and B: "\<And> A. (d A) = c (S A)"
  shows "a`?`c`:`s \<rightarrow> P \<preceq>S a`?`d`:`s \<rightarrow> Q"
  using A
  apply (auto simp: Simulation_def read1_def relation_of_iPrefix design_defs rp_defs)
  apply (erule_tac x="ba" in allE, erule_tac x="ca" in allE, simp)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (auto split: cond_splits simp: Simul_def alpha_rp.defs do_I_def select_def B)
done

lemma Read1S_Sim:
  assumes A: " P \<preceq>S Q" and B: "\<And> A. (d A) = c (S A)" and C: "\<And> A. (s' A) = s (S A)"
  shows "a`?`c`\<in>`s \<rightarrow> P \<preceq>S a`?`d`\<in>`s' \<rightarrow> Q"
  using A
  apply (auto simp: Simulation_def read1_def relation_of_iPrefix design_defs rp_defs)
  apply (erule_tac x="ba" in allE, erule_tac x="ca" in allE, simp)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (auto split: cond_splits simp: Simul_def alpha_rp.defs do_I_def select_def B C)
done

lemma Write_Sim:
  assumes A: "P \<preceq>S Q" and B: "\<And> A. (d A) = c (S A)"
  shows "a`!`c \<rightarrow> P \<preceq>S a`!`d \<rightarrow> Q "
  using A
  apply (auto simp: Simulation_def write1_def relation_of_oPrefix design_defs rp_defs)
  apply (erule_tac x="ba" in allE, erule_tac x="ca" in allE, simp)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (auto split: cond_splits simp: Simul_def alpha_rp.defs do_def select_def B)
done

lemma Hide_Sim:
  assumes A: " P \<preceq>S Q"
  shows "(P \\ cs) \<preceq>S (Q \\ cs)"
  apply (auto simp: Simulation_def relation_of_Hide design_defs rp_defs Simul_def alpha_rp.defs)
  apply (rule_tac b="Simul S ba" in comp_intro)
  apply (split cond_splits)+
  apply (auto simp: Simul_def alpha_rp.defs Simulation_def 
              dest!: A[simplified, rule_format] Skip_Sim[simplified, rule_format])
  apply (rule_tac x=s in exI, auto simp: diff_tr_def)
done

lemma lfp_Siml:
  assumes A: "\<And> X. (X \<preceq>S Q) \<Longrightarrow> ((P X) \<preceq>S Q)" and B: "mono P"
  shows "(lfp P) \<preceq>S Q"
  apply (rule lfp_ordinal_induct, auto simp: B A)
  apply (auto simp add: Simulation_def Sup_action relation_of_bot relation_of_Sup[simplified])
  apply (subst (asm) CSP_is_rd[OF relation_of_CSP])
  apply (auto simp: rp_defs fun_eq_iff Simul_def alpha_rp.defs decrease_def split: cond_splits)
done

lemma Mu_Sim:
  assumes A: "\<And> X Y. X \<preceq>S Y \<Longrightarrow> (P X) \<preceq>S (Q Y)" 
  and B: "mono P" and C: "mono Q"
  shows "(lfp P) \<preceq>S (lfp Q) "
  apply (rule lfp_Siml, drule A)
  apply (subst lfp_unfold, simp_all add: B C)
done

lemma bot_Sim: "bot \<preceq>S bot"
by (auto simp: Simulation_def rp_defs Simul_def relation_of_bot alpha_rp.defs split: cond_splits)

lemma sim_is_ref: "P \<sqsubseteq> Q = P \<preceq>(id) Q"
apply (auto simp: ref_def Simulation_def Simul_def alpha_rp.defs)
apply (erule_tac x=a in allE)
apply (erule_tac x=b in allE, auto)
apply (rule_tac t="\<lparr>ok = ok a, wait = wait a, tr = tr a, ref = ref a, \<dots> = alpha_rp.more a\<rparr>" and s=a in subst, simp)
apply (rule_tac t="\<lparr>ok = ok b, wait = wait b, tr = tr b, ref = ref b, \<dots> = alpha_rp.more b\<rparr>" and s=b in subst, simp_all)
apply (erule_tac x=a in allE)
apply (erule_tac x=b in allE, auto)
apply (rule_tac s="\<lparr>ok = ok a, wait = wait a, tr = tr a, ref = ref a, \<dots> = alpha_rp.more a\<rparr>" and t=a in subst, simp)
apply (rule_tac s="\<lparr>ok = ok b, wait = wait b, tr = tr b, ref = ref b, \<dots> = alpha_rp.more b\<rparr>" and t=b in subst, simp_all)
done

lemma ref_eq: "((P::('a::ev_eq,'b) action) = Q) = (P \<sqsubseteq> Q & Q \<sqsubseteq> P)"
apply (rule)
apply (simp add: ref_def)
apply (auto simp add: ref_def fun_eq_iff relation_of_inject[symmetric])
done

lemma rd_ref: 
assumes A:"R (P \<turnstile> Q) \<in> {p. is_CSP_process p}"
and B:"R (P' \<turnstile> Q') \<in> {p. is_CSP_process p}"
and C:"\<And> a b. P (a, b) \<Longrightarrow> P' (a, b)"
and D:"\<And> a b. Q' (a, b) \<Longrightarrow> Q (a, b)"
shows "(action_of (R (P \<turnstile> Q))) \<sqsubseteq> (action_of (R (P' \<turnstile> Q')))"
apply (auto simp: ref_def)
apply (subst (asm) action_of_inverse, simp add: B[simplified])
apply (subst action_of_inverse, simp add: A[simplified])
apply (auto simp: rp_defs design_defs C D split: cond_splits)
done


lemma rd_impl: 
assumes A:"R (P \<turnstile> Q) \<in> {p. is_CSP_process p}"
and B:"R (P' \<turnstile> Q') \<in> {p. is_CSP_process p}"
and C:"\<And> a b. P (a, b) \<Longrightarrow> P' (a, b)"
and D:"\<And> a b. Q' (a, b) \<Longrightarrow> Q (a, b)"
shows "R (P' \<turnstile> Q') (a, b) \<longrightarrow> R (P \<turnstile> Q) (a::('a::ev_eq, 'b) alpha_rp_scheme, b)"
apply (insert rd_ref[of P Q P' Q', OF A B C D])
apply (auto simp: ref_def)
apply (subst (asm) action_of_inverse, simp add: B[simplified])
apply (subst (asm) action_of_inverse, simp add: A[simplified])
apply (erule_tac x=a in allE)
apply (erule_tac x=b in allE)
apply (auto)
done

end
