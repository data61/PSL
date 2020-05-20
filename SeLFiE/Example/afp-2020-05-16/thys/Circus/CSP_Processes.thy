section \<open>CSP processes\<close>

theory CSP_Processes
imports Reactive_Processes
begin

text \<open>A CSP process is a UTP reactive process that satisfies two additional
healthiness conditions called $CSP1$ and $CSP2$. A reactive process that satisfies 
$CSP1$ and $CSP2$ is said to be CSP healthy.\<close>

subsection \<open>Definitions\<close>

text \<open>We introduce here the definitions of the CSP healthiness conditions.\<close>

definition CSP1::"(('\<theta>,'\<sigma>) alphabet_rp) Healthiness_condition"
where "CSP1 (P)  \<equiv>  P \<or> (\<lambda>(A, A'). \<not>ok A \<and> tr A \<le> tr A')"

definition J_csp
where "J_csp  \<equiv>  \<lambda>(A, A'). (ok A \<longrightarrow> ok A') \<and> tr A = tr A' \<and> wait A = wait A' 
                                                     \<and> ref A = ref A' \<and> more A = more A'"

definition CSP2::"(('\<theta>,'\<sigma>) alphabet_rp) Healthiness_condition"
where "CSP2 (P)  \<equiv>  P ;; J_csp"

definition is_CSP_process::"('\<theta>,'\<sigma>) relation_rp \<Rightarrow> bool" where
"is_CSP_process P \<equiv> P is CSP1 healthy \<and> P is CSP2 healthy \<and> P is R healthy"

lemmas csp_defs = CSP1_def J_csp_def CSP2_def is_CSP_process_def

lemma is_CSP_processE1 [elim?]:
  assumes "is_CSP_process P"
  obtains "P is CSP1 healthy" "P is CSP2 healthy" "P is R healthy"
  using assms unfolding is_CSP_process_def by simp

lemma is_CSP_processE2 [elim?]:
  assumes "is_CSP_process P"
  obtains "CSP1 P = P" "CSP2 P = P" "R P = P"
  using assms unfolding is_CSP_process_def by (simp add: Healthy_def')


subsection \<open>Proofs\<close>

text \<open>Theorems and lemmas relative to CSP processes are introduced here.\<close>

lemma CSP1_CSP2_commute: "CSP1 o CSP2 = CSP2 o CSP1"
by (auto simp: csp_defs fun_eq_iff)

lemma CSP2_is_H2: "H2 = CSP2"
apply (clarsimp simp add: csp_defs design_defs rp_defs fun_eq_iff)
apply (rule iffI)
apply (erule_tac [!] comp_elim)
apply (rule_tac [!] b=ba in comp_intro)
apply (auto elim!: alpha_d_more_eqE intro!: alpha_d_more_eqI)
done

lemma H2_CSP1_commute: "H2 o CSP1 = CSP1 o H2" 
apply (subst CSP2_is_H2[simplified Healthy_def])+
apply (rule CSP1_CSP2_commute[symmetric])
done

lemma H2_CSP1_commute2: "H2 (CSP1 P) = CSP1 (H2 P)" 
by (simp add: H2_CSP1_commute[simplified Fun.comp_def fun_eq_iff, rule_format] fun_eq_iff)

lemma CSP1_R_commute:
  "CSP1 (R P) = R (CSP1 P)"
by (auto simp: csp_defs rp_defs fun_eq_iff prefix_def split: cond_splits)

lemma CSP2_R_commute:
  "CSP2 (R P) = R (CSP2 P)"
apply (subst CSP2_is_H2[symmetric])+
apply (rule R_H2_commute2[symmetric])
done

lemma CSP1_idem: "CSP1 = CSP1 o CSP1"
by (auto simp: csp_defs fun_eq_iff)

lemma CSP2_idem: "CSP2 = CSP2 o CSP2"
by (auto simp: csp_defs fun_eq_iff)

lemma CSP_is_CSP1:
  assumes A: "is_CSP_process P"
  shows "P is CSP1 healthy"
using A by (auto simp: is_CSP_process_def design_defs)

lemma CSP_is_CSP2:
  assumes A: "is_CSP_process P"
  shows "P is CSP2 healthy"
using A by (simp add: design_defs prefix_def is_CSP_process_def)

lemma CSP_is_R:
  assumes A: "is_CSP_process P"
  shows "P is R healthy"
using A by (simp add: design_defs prefix_def is_CSP_process_def)

lemma t_or_f_a: "P(a, b) \<Longrightarrow> ((P(a, b\<lparr>ok := True\<rparr>)) \<or> (P(a, b\<lparr>ok := False\<rparr>)))"
apply (case_tac "ok b", auto)
apply (rule_tac t="b\<lparr>ok := True\<rparr>" and s="b" in ssubst, simp_all)
by (subgoal_tac "b = b\<lparr>ok := False\<rparr>", simp_all)

lemma CSP2_ok_a: 
"(CSP2 P)(a, b\<lparr>ok:=True\<rparr>) \<Longrightarrow> (P(a, b\<lparr>ok:=True\<rparr>) \<or> P(a, b\<lparr>ok:=False\<rparr>))"
apply (clarsimp simp: csp_defs design_defs rp_defs split: cond_splits elim: prefixE)
apply (case_tac "ok ba")
apply (rule_tac t="b\<lparr>ok := True\<rparr>" and s="ba" in ssubst, simp_all)
apply (drule_tac b="b\<lparr>ok := False\<rparr>" and a="ba" in back_subst)
apply (auto intro: alpha_rp.equality)
done

lemma CSP2_ok_b: 
"(P(a, b\<lparr>ok:=True\<rparr>) \<or> P(a, b\<lparr>ok:=False\<rparr>)) \<Longrightarrow> (CSP2 P)(a, b\<lparr>ok:=True\<rparr>)"
by (auto simp: csp_defs design_defs rp_defs)

lemma CSP2_ok: 
"(CSP2 P)(a, b\<lparr>ok:=True\<rparr>) = (P(a, b\<lparr>ok:=True\<rparr>) \<or> P(a, b\<lparr>ok:=False\<rparr>))"
apply (rule iffI)
apply (simp add: CSP2_ok_a)
by (simp add: CSP2_ok_b)

lemma CSP2_notok_a: "(CSP2 P)(a, b\<lparr>ok:=False\<rparr>) \<Longrightarrow> P(a, b\<lparr>ok:=False\<rparr>)"
apply (clarsimp simp: csp_defs design_defs rp_defs)
apply (case_tac "ok ba")
apply (rule_tac t="b\<lparr>ok := True\<rparr>" and s="ba" in ssubst, simp_all)
apply (drule_tac b="b\<lparr>ok := False\<rparr>" and a="ba" in back_subst)
apply (auto intro: alpha_rp.equality)
done

lemma CSP2_notok_b: "P(a, b\<lparr>ok:=False\<rparr>) \<Longrightarrow> (CSP2 P)(a, b\<lparr>ok:=False\<rparr>)"
by (auto simp: csp_defs design_defs rp_defs)

lemma CSP2_notok: "(CSP2 P)(a, b\<lparr>ok:=False\<rparr>) = P(a, b\<lparr>ok:=False\<rparr>)"
apply (rule iffI)
apply (simp add: CSP2_notok_a)
by (simp add: CSP2_notok_b)

lemma CSP2_t_f: 
  assumes A:"(CSP2 (R (r \<turnstile> p)))(a, b)"
  and B: "((CSP2 (R (r \<turnstile> p)))(a, b\<lparr>ok:=False\<rparr>)) \<or> 
          ((CSP2 (R (r \<turnstile> p)))(a, b\<lparr>ok:=True\<rparr>)) \<Longrightarrow> Q"
  shows "Q"
apply (rule B)
apply (rule disjI2)
apply (insert A)
apply (auto simp add: csp_defs design_defs rp_defs)
done

lemma disj_CSP1:
  assumes "P is CSP1 healthy"
    and "Q is CSP1 healthy"
  shows "(P \<or> Q) is CSP1 healthy"
using assms by (auto simp: csp_defs design_defs rp_defs fun_eq_iff)

lemma disj_CSP2:
  "P is CSP2 healthy ==> Q is CSP2 healthy ==> (P \<or> Q) is CSP2 healthy"
  by (simp add: CSP2_is_H2[symmetric] Healthy_def' design_defs comp_ndet_l_distr)

lemma disj_CSP:
  assumes A: "is_CSP_process P"
  assumes B: "is_CSP_process Q"
  shows "is_CSP_process (P \<or> Q)"
apply (simp add: is_CSP_process_def Healthy_def)
apply (subst disj_CSP2[simplified Healthy_def, symmetric])
apply (rule A[THEN CSP_is_CSP2, simplified Healthy_def])
apply (rule B[THEN CSP_is_CSP2, simplified Healthy_def], simp)
apply (subst disj_CSP1[simplified Healthy_def, symmetric])
apply (rule A[THEN CSP_is_CSP1, simplified Healthy_def])
apply (rule B[THEN CSP_is_CSP1, simplified Healthy_def], simp)
apply (subst R_disj[simplified Healthy_def])
apply (rule A[THEN CSP_is_R, simplified Healthy_def])
apply (rule B[THEN CSP_is_R, simplified Healthy_def], simp)
done

lemma seq_CSP1:
  assumes A: "P is CSP1 healthy"
  assumes B: "Q is CSP1 healthy"
  shows "(P ;; Q) is CSP1 healthy"
using A B by (auto simp: csp_defs design_defs rp_defs fun_eq_iff)

lemma seq_CSP2:
  assumes A: "Q is CSP2 healthy"
  shows "(P ;; Q) is CSP2 healthy"
using A
by (auto simp: CSP2_is_H2[symmetric] H2_J[symmetric])

lemma seq_R:
  assumes "P is R healthy"
  and "Q is R healthy"
  shows "(P ;; Q) is R healthy"
proof -
  have "R P = P" and "R Q = Q"
    using assms by (simp_all only: Healthy_def)
  moreover
  have "(R P ;; R Q) is R healthy"
    apply (auto simp add: design_defs rp_defs prefix_def fun_eq_iff split: cond_splits)
           apply (rule_tac b=a in comp_intro, auto split: cond_splits)
       apply (rule_tac x="zs" in exI, auto split: cond_splits)
      apply (rule_tac b="ba\<lparr>tr := tr a @ tr ba\<rparr>" in comp_intro, auto split: cond_splits)+
    done
  ultimately show ?thesis by simp
qed


lemma seq_CSP:
  assumes A: "P is CSP1 healthy"
  and B: "P is R healthy"
  and C: "is_CSP_process Q"
  shows "is_CSP_process (P ;; Q)"
apply (auto simp add: is_CSP_process_def)
apply (subst seq_CSP1[simplified Healthy_def])
apply (rule A[simplified Healthy_def])
apply (rule CSP_is_CSP1[OF C, simplified Healthy_def])
apply (simp add: Healthy_def, subst CSP1_idem, auto)
apply (subst seq_CSP2[simplified Healthy_def])
apply (rule CSP_is_CSP2[OF C, simplified Healthy_def])
apply (simp add: Healthy_def, subst CSP2_idem, auto)
apply (subst seq_R[simplified Healthy_def])
apply (rule B[simplified Healthy_def])
apply (rule CSP_is_R[OF C, simplified Healthy_def])
apply (simp add: Healthy_def, subst R_idem2, auto)
done

lemma rd_ind_wait: "(R(\<not>(P \<^sup>f\<^sub>f) \<turnstile> (P \<^sup>t\<^sub>f)))
                        = (R((\<not>(\<lambda> (A, A'). P (A, A'\<lparr>ok := False\<rparr>))) 
                                  \<turnstile> (\<lambda> (A, A'). P (A, A'\<lparr>ok := True\<rparr>))))"
apply (auto simp: design_defs rp_defs fun_eq_iff split: cond_splits)
apply (subgoal_tac "a\<lparr>tr := [], wait := False\<rparr> = a\<lparr>tr := []\<rparr>", auto)
apply (subgoal_tac "a\<lparr>tr := [], wait := False\<rparr> = a\<lparr>tr := []\<rparr>", auto)
apply (subgoal_tac "a\<lparr>tr := [], wait := False\<rparr> = a\<lparr>tr := []\<rparr>", auto)
apply (subgoal_tac "a\<lparr>tr := [], wait := False\<rparr> = a\<lparr>tr := []\<rparr>", auto)
apply (subgoal_tac "a\<lparr>tr := [], wait := False\<rparr> = a\<lparr>tr := []\<rparr>", auto)
apply (rule_tac t="a\<lparr>tr := [], wait := False\<rparr>" and s="a\<lparr>tr := []\<rparr>" in subst, simp_all)
done

lemma rd_H1: "(R((\<not>(\<lambda> (A, A'). P (A, A'\<lparr>ok := False\<rparr>))) 
                              \<turnstile> (\<lambda> (A, A'). P (A, A'\<lparr>ok := True\<rparr>)))) = 
                      (R ((\<not> H1 (\<lambda> (A, A'). P (A, A'\<lparr>ok := False\<rparr>))) 
                              \<turnstile> H1 (\<lambda> (A, A'). P (A, A'\<lparr>ok := True\<rparr>))))"
by (auto simp: design_defs rp_defs fun_eq_iff split: cond_splits)

lemma rd_H1_H2: "(R((\<not> H1 (\<lambda> (A, A'). P (A, A'\<lparr>ok := False\<rparr>))) 
                                  \<turnstile> H1 (\<lambda> (A, A'). P (A, A'\<lparr>ok := True\<rparr>)))) = 
                        (R((\<not>(H1 o H2) (\<lambda> (A, A'). P (A, A'\<lparr>ok := False\<rparr>))) 
                                  \<turnstile> (H1 o H2) (\<lambda> (A, A'). P (A, A'\<lparr>ok := True\<rparr>))))"
apply (auto simp: design_defs rp_defs prefix_def fun_eq_iff split: cond_splits elim: alpha_d_more_eqE)
apply (subgoal_tac "b\<lparr>tr := zs, ok := False\<rparr> = ba\<lparr>ok := False\<rparr>", auto intro: alpha_d.equality)
apply (subgoal_tac "b\<lparr>tr := zs, ok := False\<rparr> = ba\<lparr>ok := False\<rparr>", auto intro: alpha_d.equality)
apply (subgoal_tac "b\<lparr>tr := zs, ok := False\<rparr> = ba\<lparr>ok := False\<rparr>", auto intro: alpha_d.equality)
apply (subgoal_tac "b\<lparr>tr := zs, ok := True\<rparr> = ba\<lparr>ok := True\<rparr>", auto intro: alpha_d.equality)
apply (subgoal_tac "b\<lparr>tr := zs, ok := True\<rparr> = ba\<lparr>ok := True\<rparr>", auto intro: alpha_d.equality)
done

lemma rd_H1_H2_R_H1_H2:
   "(R ((\<not> (H1 o H2) (\<lambda> (A, A'). P (A, A'\<lparr>ok := False\<rparr>))) 
            \<turnstile> (H1 o H2) (\<lambda> (A, A'). P (A, A'\<lparr>ok := True\<rparr>)))) = 
    (R o H1 o H2) P"
apply (auto simp: design_defs rp_defs fun_eq_iff split: cond_splits)
apply (erule notE) back back
apply (rule_tac b="ba" in comp_intro, auto)
apply (rule_tac t="ba\<lparr>ok := False\<rparr>" and s=ba in subst, auto intro: alpha_d.equality)
apply (erule notE) back back
apply (rule_tac b="ba" in comp_intro, auto)
apply (rule_tac t="ba\<lparr>ok := False\<rparr>" and s=ba in subst, auto intro: alpha_d.equality)
apply (case_tac "ok ba")
apply (rule_tac b="ba" in comp_intro, auto)
apply (rule_tac t="ba\<lparr>ok := True\<rparr>" and s=ba in subst, auto)
apply (erule notE) back
apply (rule_tac b="ba" in comp_intro, auto)
apply (rule_tac t="ba\<lparr>ok := False\<rparr>" and s=ba in subst, auto intro: alpha_d.equality)
done

lemma CSP1_is_R1_H1:
  assumes "P is R1 healthy"
  shows "CSP1 P = R1 (H1 P)"
using assms
by (auto simp: csp_defs design_defs rp_defs fun_eq_iff split: cond_splits)

lemma CSP1_is_R1_H1_2: "CSP1 (R1 P) = R1 (H1 P)"
by (auto simp: csp_defs design_defs rp_defs fun_eq_iff split: cond_splits)

lemma CSP1_R1_commute: "CSP1 o R1 = R1 o CSP1"
by (auto simp: csp_defs design_defs rp_defs fun_eq_iff split: cond_splits)

lemma CSP1_R1_commute2: "CSP1 (R1 P) = R1 (CSP1 P)"
by (auto simp: csp_defs design_defs rp_defs fun_eq_iff split: cond_splits)

lemma CSP1_is_R1_H1_b: 
"(P = (R \<circ> R1 \<circ> H1 \<circ> H2) P) = (P = (R \<circ> CSP1 \<circ> H2) P)"
apply (simp add: fun_eq_iff)
apply (subst H1_H2_commute2)
apply (subst R1_H2_commute2)
apply (subst CSP1_is_R1_H1_2[symmetric])
apply (subst H2_CSP1_commute2)
apply (subst R1_H2_commute2[symmetric])
apply (subst CSP1_R1_commute2)
apply (subst R_abs_R1[simplified Fun.comp_def fun_eq_iff])
apply (auto)
done

lemma CSP1_join: 
  assumes A: "x is CSP1 healthy"
  and B: "y is CSP1 healthy"
  shows "(x \<sqinter> y) is CSP1 healthy"
  using A B
  by (simp add: Healthy_def CSP1_def fun_eq_iff utp_defs)

lemma CSP2_join:
  assumes A: "x is CSP2 healthy"
  and B: "y is CSP2 healthy"
  shows "(x \<sqinter> y) is CSP2 healthy"
  using A B
  apply (simp add: design_defs csp_defs fun_eq_iff)
  apply (rule allI)
  apply (rule allI)
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="b" in allE)+
  by (auto)

lemma CSP1_meet:
  assumes A: "x is CSP1 healthy"
  and B: "y is CSP1 healthy"
  shows "(x \<squnion> y) is CSP1 healthy"
  using A B
  apply (simp add: Healthy_def CSP1_def fun_eq_iff utp_defs)
  apply (rule allI)
  apply (rule allI)
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="b" in allE)+
  by (auto)

lemma CSP2_meet:
  assumes A: "x is CSP2 healthy"
  and B: "y is CSP2 healthy"
  shows "(x \<squnion> y) is CSP2 healthy"
  using A B
  apply (simp add: Healthy_def CSP2_def fun_eq_iff)
  apply (rule allI)+
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="a" in allE)
  apply (erule_tac x="b" in allE)+
  apply (auto)
  apply (rule_tac b="ca" in comp_intro)
  apply (auto simp: J_csp_def)
done

lemma CSP_join: 
  assumes A: "is_CSP_process x"
  and B: "is_CSP_process y"
  shows "is_CSP_process (x \<sqinter> y)"
  using A B
by (simp add: is_CSP_process_def CSP1_join CSP2_join R_join)

lemma CSP_meet:
  assumes A: "is_CSP_process x"
  and B: "is_CSP_process y"
  shows "is_CSP_process (x \<squnion> y)"
  using A B
by (simp add: is_CSP_process_def CSP1_meet CSP2_meet R_meet)

subsection \<open>CSP processes and reactive designs\<close>

text \<open>In this section, we prove the relation between CSP processes and reactive designs.\<close>

lemma rd_is_CSP1: "(R (r \<turnstile> p)) is CSP1 healthy"
by (auto simp: csp_defs design_defs rp_defs fun_eq_iff split: cond_splits elim: prefixE)

lemma rd_is_CSP2:
  assumes A: "\<forall> a b. r (a, b\<lparr>ok := True\<rparr>) \<longrightarrow> r (a, b\<lparr>ok := False\<rparr>)"
  shows "(R (r \<turnstile> p)) is CSP2 healthy"
apply (subst CSP2_is_H2[symmetric]) 
apply (simp add: Healthy_def)
apply (subst R_H2_commute2[symmetric])
apply (subst design_H2[simplified Healthy_def], auto simp: A)
done

lemma rd_is_CSP:
  assumes A: "\<forall> a b. r (a, b\<lparr>ok := True\<rparr>) \<longrightarrow> r (a, b\<lparr>ok := False\<rparr>)"
  shows "is_CSP_process (R (r \<turnstile> p))"
apply (simp add: is_CSP_process_def Healthy_def fun_eq_iff)
apply (subst R_idem2)
apply (subst rd_is_CSP2[simplified Healthy_def, symmetric], rule A)
apply (subst rd_is_CSP1[simplified Healthy_def, symmetric], simp)
done

lemma CSP_is_rd:
  assumes A: "is_CSP_process P"
  shows "P = (R (\<not>(P \<^sup>f\<^sub>f) \<turnstile> (P \<^sup>t\<^sub>f)))"
  apply (subst rd_ind_wait)
  apply (subst rd_H1)
  apply (subst rd_H1_H2)
  apply (subst rd_H1_H2_R_H1_H2)
  apply (subst R_abs_R1[symmetric])
  apply (subst CSP1_is_R1_H1_b)
  apply (subst CSP2_is_H2)
  apply (simp)
  apply (subst CSP_is_CSP2[OF A, simplified Healthy_def, symmetric])
  apply (subst CSP_is_CSP1[OF A, simplified Healthy_def, symmetric])
  apply (subst CSP_is_R[OF A, simplified Healthy_def, symmetric], simp)
done


end
