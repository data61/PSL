section\<open>Designs\<close>

theory Designs
imports Relations
begin

text \<open>In UTP, in order to explicitly record the termination of a program, 
a subset of alphabetized relations is introduced. These relations are called 
designs and their alphabet should contain the special boolean observational variable ok. 
It is used to record the start and termination of a program.\<close>

subsection\<open>Definitions\<close>

text \<open>In the following, the definitions of designs alphabets, designs and 
healthiness (well-formedness) conditions are given. The healthiness conditions of
designs are defined by $H1$, $H2$, $H3$ and $H4$.\<close>

record alpha_d = ok::bool

type_synonym '\<alpha> alphabet_d  = "'\<alpha> alpha_d_scheme alphabet"
type_synonym '\<alpha> relation_d = "'\<alpha> alphabet_d relation"

definition design::"'\<alpha> relation_d \<Rightarrow> '\<alpha> relation_d \<Rightarrow> '\<alpha> relation_d" ("'(_ \<turnstile> _')")
where " (P \<turnstile> Q) \<equiv> \<lambda> (A, A') .  (ok A \<and> P (A,A')) \<longrightarrow> (ok A' \<and> Q (A,A'))"

definition skip_d :: "'\<alpha> relation_d" ("\<Pi>d")
where "\<Pi>d \<equiv> (true \<turnstile> \<Pi>r)"

definition J
where "J  \<equiv>  \<lambda> (A, A') . (ok A  \<longrightarrow>  ok A') \<and> more A = more A'"

type_synonym '\<alpha> Healthiness_condition = "'\<alpha> relation \<Rightarrow> '\<alpha> relation"

definition 
Healthy::"'\<alpha> relation \<Rightarrow> '\<alpha> Healthiness_condition \<Rightarrow> bool" ("_ is _ healthy")
where "P is H healthy \<equiv> (P = H P)"

lemma Healthy_def': "P is H healthy = (H P = P)"
  unfolding Healthy_def by auto

definition H1::"('\<alpha> alphabet_d) Healthiness_condition"
where "H1 (P)  \<equiv>  (ok o fst  \<longrightarrow> P)"

definition H2::"('\<alpha> alphabet_d) Healthiness_condition"
where "H2 (P)  \<equiv>  P ;; J"

definition H3::"('\<alpha> alphabet_d) Healthiness_condition"
where "H3 (P)  \<equiv>  P ;; \<Pi>d"

definition H4::"('\<alpha> alphabet_d) Healthiness_condition"
where "H4 (P)  \<equiv>  ((P;;true) \<longleftrightarrow> true)"

definition \<sigma>f::"'\<alpha> relation_d \<Rightarrow> '\<alpha> relation_d"
where "\<sigma>f D \<equiv> \<lambda> (A, A') . D (A, A'\<lparr>ok:=False\<rparr>)"

definition \<sigma>t::"'\<alpha> relation_d \<Rightarrow> '\<alpha> relation_d"
where "\<sigma>t D \<equiv> \<lambda> (A, A') . D (A, A'\<lparr>ok:=True\<rparr>)"

definition OKAY::"'\<alpha> relation_d"
where "OKAY \<equiv> \<lambda> (A, A') . ok A"

definition OKAY'::"'\<alpha> relation_d"
where "OKAY' \<equiv> \<lambda> (A, A') . ok A'"

lemmas design_defs = design_def skip_d_def J_def Healthy_def H1_def H2_def H3_def
                     H4_def \<sigma>f_def \<sigma>t_def OKAY_def OKAY'_def

subsection\<open>Proofs\<close>

text \<open>Proof of theorems and properties of designs and their healthiness conditions 
are given in the following.\<close>

lemma t_comp_lz_d: "(true;;(P \<turnstile> Q)) = true"
  apply (auto simp: fun_eq_iff design_defs)
  apply (rule_tac b="b\<lparr>ok:=False\<rparr>" in comp_intro, auto)
done

lemma pi_comp_left_unit: "(\<Pi>d;;(P \<turnstile> Q)) = (P \<turnstile> Q)"
by (auto simp: fun_eq_iff design_defs)

theorem t3_1_4_2: 
"((P1 \<turnstile> Q1) \<triangleleft> b \<triangleright> (P2 \<turnstile> Q2)) = ((P1 \<triangleleft> b \<triangleright> P2) \<turnstile> (Q1 \<triangleleft> b \<triangleright> Q2))"
by (auto simp: fun_eq_iff design_defs split: cond_splits)

lemma conv_conj_distr: "\<sigma>t (P \<and> Q) = (\<sigma>t P \<and> \<sigma>t Q)"
by (auto simp: design_defs fun_eq_iff)

lemma conv_disj_distr: "\<sigma>t (P \<or> Q) = (\<sigma>t P \<or> \<sigma>t Q)"
by (auto simp: design_defs fun_eq_iff)

lemma conv_imp_distr: "\<sigma>t (P \<longrightarrow> Q) = ((\<sigma>t P) \<longrightarrow> \<sigma>t Q)"
by (auto simp: design_defs fun_eq_iff)

lemma conv_not_distr: "\<sigma>t (\<not> P) = (\<not>(\<sigma>t P))"
by (auto simp: design_defs fun_eq_iff)

lemma div_conj_distr: "\<sigma>f (P \<and> Q) = (\<sigma>f P \<and> \<sigma>f Q)"
by (auto simp: design_defs fun_eq_iff)

lemma div_disj_distr: "\<sigma>f (P \<or> Q) = (\<sigma>f P \<or> \<sigma>f Q)"
by (auto simp: design_defs fun_eq_iff)

lemma div_imp_distr: "\<sigma>f (P \<longrightarrow> Q) = ((\<sigma>f P) \<longrightarrow> \<sigma>f Q)"
by (auto simp: design_defs fun_eq_iff)

lemma div_not_distr: "\<sigma>f (\<not> P) = (\<not>(\<sigma>f P))"
by (auto simp: design_defs fun_eq_iff)

lemma ok_conv: "\<sigma>t OKAY = OKAY"
by (auto simp: design_defs fun_eq_iff)

lemma ok_div: "\<sigma>f OKAY = OKAY"
by (auto simp: design_defs fun_eq_iff)

lemma ok'_conv: "\<sigma>t OKAY' = true"
by (auto simp: design_defs fun_eq_iff)

lemma ok'_div: "\<sigma>f OKAY' = false"
by (auto simp: design_defs fun_eq_iff)

lemma H2_J_1:
 assumes A: "P is H2 healthy"
 shows "[(\<lambda> (A, A'). (P(A, A'\<lparr>ok := False\<rparr>) \<longrightarrow> P(A, A'\<lparr>ok := True\<rparr>)))]"
using A by (auto simp: design_defs fun_eq_iff)

lemma H2_J_2_a : "P (a,b) \<longrightarrow> (P ;; J) (a,b)"
  unfolding J_def by auto

lemma ok_or_not_ok : "\<lbrakk>P(a, b\<lparr>ok := True\<rparr>); P(a, b\<lparr>ok := False\<rparr>)\<rbrakk> \<Longrightarrow> P(a, b)"
  apply (case_tac "ok b")
  apply (subgoal_tac "b\<lparr>ok:=True\<rparr> = b")
  apply (simp_all)
  apply (subgoal_tac "b\<lparr>ok:=False\<rparr> = b")
  apply (simp_all)
done

lemma H2_J_2_b :
  assumes A: "[(\<lambda> (A, A'). (P(A, A'\<lparr>ok := False\<rparr>) \<longrightarrow> P(A, A'\<lparr>ok := True\<rparr>)))]"
  and B : "(P ;; J) (a,b)"
  shows "P (a,b)"
  using B
  apply (auto simp: design_defs fun_eq_iff)
  apply (case_tac "ok b")
  apply (subgoal_tac "b = ba\<lparr>ok:=True\<rparr>", auto intro!: A[simplified, rule_format])
  apply (rule_tac s=ba and t="ba\<lparr>ok:=False\<rparr>" in subst, simp_all)
  apply (subgoal_tac "b = ba", simp_all)
  apply (case_tac "ok ba")
  apply (subgoal_tac "b = ba", simp_all)
  apply (subgoal_tac "b = ba\<lparr>ok:=True\<rparr>", auto intro!: A[simplified, rule_format])
  apply (rule_tac s=ba and t="ba\<lparr>ok:=False\<rparr>" in subst, simp_all)
done  

lemma H2_J_2 :
  assumes A: "[(\<lambda> (A, A'). (P(A, A'\<lparr>ok := False\<rparr>) \<longrightarrow> P(A, A'\<lparr>ok := True\<rparr>)))]"
  shows "P is H2 healthy "
  apply (auto simp add: H2_def Healthy_def fun_eq_iff)
  apply (simp add: H2_J_2_a)
  apply (rule H2_J_2_b [OF A])
  apply auto
  done

lemma H2_J: 
"[\<lambda> (A, A'). P(A, A'\<lparr>ok := False\<rparr>) \<longrightarrow> P(A, A'\<lparr>ok := True\<rparr>)] = P is H2 healthy"
using H2_J_1 H2_J_2 by blast

lemma design_eq1: "(P \<turnstile> Q) = (P \<turnstile> P \<and> Q)"
by (rule ext) (auto simp: design_defs)

lemma H1_idem: "H1 o H1 = H1"
by (auto simp: design_defs fun_eq_iff)

lemma H1_idem2: "(H1 (H1 P)) = (H1 P)"
by (simp add: H1_idem[simplified fun_eq_iff Fun.comp_def, rule_format] fun_eq_iff)

lemma H2_idem: "H2 o H2 = H2"  
by (auto simp: design_defs fun_eq_iff)
  
lemma H2_idem2: "(H2 (H2 P)) = (H2 P)"
by (simp add: H2_idem[simplified fun_eq_iff Fun.comp_def, rule_format] fun_eq_iff)

lemma H1_H2_commute: "H1 o H2 = H2 o H1"
by (auto simp: design_defs fun_eq_iff split: cond_splits)

lemma H1_H2_commute2: "H1 (H2 P) = H2 (H1 P)"
by (simp add: H1_H2_commute[simplified fun_eq_iff Fun.comp_def, rule_format] fun_eq_iff)

lemma alpha_d_eqD: "r = r' \<Longrightarrow> ok r = ok r' \<and> alpha_d.more r = alpha_d.more r'"
by (auto simp: alpha_d.equality)

lemma design_H1: "(P \<turnstile> Q) is H1 healthy"
by (auto simp: design_defs fun_eq_iff)

lemma design_H2: 
"(\<forall> a b. P (a, b\<lparr>ok := True\<rparr>) \<longrightarrow> P (a, b\<lparr>ok := False\<rparr>)) \<Longrightarrow> (P \<turnstile> Q) is H2 healthy"
by (rule H2_J_2) (auto simp: design_defs fun_eq_iff)

end
