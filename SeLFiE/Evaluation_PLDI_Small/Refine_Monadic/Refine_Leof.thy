section \<open>Less-Equal or Fail\<close>
(* TODO: Move to Refinement Framework *)
theory Refine_Leof
imports Refine_Basic
begin
  text \<open>A predicate that states refinement or that the LHS fails.\<close>


  definition le_or_fail :: "'a nres \<Rightarrow> 'a nres \<Rightarrow> bool" (infix "\<le>\<^sub>n" 50) where
    "m \<le>\<^sub>n m' \<equiv> nofail m \<longrightarrow> m \<le> m'"

  lemma leofI[intro?]: 
    assumes "nofail m \<Longrightarrow> m \<le> m'" shows "m \<le>\<^sub>n m'" 
    using assms unfolding le_or_fail_def by auto
  
  lemma leofD:  
    assumes "nofail m"
    assumes "m \<le>\<^sub>n m'"
    shows "m \<le> m'"
    using assms unfolding le_or_fail_def by blast

  lemma pw_leof_iff:
    "m \<le>\<^sub>n m' \<longleftrightarrow> (nofail m \<longrightarrow> (\<forall>x. inres m x \<longrightarrow> inres m' x))"
    unfolding le_or_fail_def by (auto simp add: pw_le_iff refine_pw_simps)
      
  lemma le_by_leofI: "\<lbrakk> nofail m' \<Longrightarrow> nofail m; m\<le>\<^sub>nm' \<rbrakk> \<Longrightarrow> m \<le> m'"
    by (auto simp: pw_le_iff pw_leof_iff)
      
  lemma inres_leof_mono: "m\<le>\<^sub>nm' \<Longrightarrow> nofail m \<Longrightarrow> inres m x \<Longrightarrow> inres m' x"
    by (auto simp: pw_leof_iff)

  lemma leof_trans[trans]: "\<lbrakk>a \<le>\<^sub>n RES X; RES X \<le>\<^sub>n c\<rbrakk> \<Longrightarrow> a \<le>\<^sub>n c"
    by (auto simp: pw_leof_iff)

  lemma leof_trans_nofail: "\<lbrakk> a\<le>\<^sub>nb; nofail b; b\<le>\<^sub>nc \<rbrakk> \<Longrightarrow> a \<le>\<^sub>n c"  
    by (auto simp: pw_leof_iff)

  lemma leof_refl[simp]: "a \<le>\<^sub>n a" 
    by (auto simp: pw_leof_iff)

  lemma leof_RES_UNIV[simp, intro!]: "m \<le>\<^sub>n RES UNIV" 
    by (auto simp: pw_leof_iff)

  lemma leof_FAIL[simp, intro!]: "m \<le>\<^sub>n FAIL" by (auto simp: pw_leof_iff)
  lemma FAIL_leof[simp, intro!]: "FAIL \<le>\<^sub>n m"  
    by (auto simp: le_or_fail_def)
      
  lemma leof_lift:
    "m \<le> F \<Longrightarrow> m \<le>\<^sub>n F"
    by (auto simp add: pw_leof_iff pw_le_iff)

  lemma leof_RETURN_rule[refine_vcg]: 
    "\<Phi> m \<Longrightarrow> RETURN m \<le>\<^sub>n SPEC \<Phi>" by (simp add: pw_leof_iff)
  
  lemma leof_bind_rule[refine_vcg]: 
    "\<lbrakk> m \<le>\<^sub>n SPEC (\<lambda>x. f x \<le>\<^sub>n SPEC \<Phi>) \<rbrakk> \<Longrightarrow> m\<bind>f \<le>\<^sub>n SPEC \<Phi>" 
    by (auto simp add: pw_leof_iff refine_pw_simps)
  
  lemma RETURN_leof_RES_iff[simp]: "RETURN x \<le>\<^sub>n RES Y \<longleftrightarrow> x\<in>Y"
    by (auto simp add: pw_leof_iff refine_pw_simps)

  lemma RES_leof_RES_iff[simp]: "RES X \<le>\<^sub>n RES Y \<longleftrightarrow> X \<subseteq> Y"
    by (auto simp add: pw_leof_iff refine_pw_simps)
   
  lemma leof_Let_rule[refine_vcg]: "f x \<le>\<^sub>n SPEC \<Phi> \<Longrightarrow> Let x f \<le>\<^sub>n SPEC \<Phi>" 
    by simp

  lemma leof_If_rule[refine_vcg]: 
    "\<lbrakk>c \<Longrightarrow> t \<le>\<^sub>n SPEC \<Phi>; \<not>c \<Longrightarrow> e \<le>\<^sub>n SPEC \<Phi>\<rbrakk> \<Longrightarrow> If c t e \<le>\<^sub>n SPEC \<Phi>" 
    by simp

  lemma leof_RES_rule[refine_vcg]:
    "\<lbrakk>\<And>x. \<Psi> x \<Longrightarrow> \<Phi> x\<rbrakk> \<Longrightarrow> SPEC \<Psi> \<le>\<^sub>n SPEC \<Phi>"
    "\<lbrakk>\<And>x. x\<in>X \<Longrightarrow> \<Phi> x\<rbrakk> \<Longrightarrow> RES X \<le>\<^sub>n SPEC \<Phi>"
    by auto

  lemma leof_True_rule: "\<lbrakk>\<And>x. \<Phi> x\<rbrakk> \<Longrightarrow> m \<le>\<^sub>n SPEC \<Phi>"
    by (auto simp add: pw_leof_iff refine_pw_simps)

  lemma sup_leof_iff: "(sup a b \<le>\<^sub>n m) \<longleftrightarrow> (nofail a \<and> nofail b \<longrightarrow> a\<le>\<^sub>nm \<and> b\<le>\<^sub>nm)"  
    by (auto simp: pw_leof_iff refine_pw_simps)

  lemma sup_leof_rule[refine_vcg]:
    assumes "\<lbrakk>nofail a; nofail b\<rbrakk> \<Longrightarrow> a\<le>\<^sub>nm"
    assumes "\<lbrakk>nofail a; nofail b\<rbrakk> \<Longrightarrow> b\<le>\<^sub>nm"
    shows "sup a b \<le>\<^sub>n m"
    using assms by (auto simp: pw_leof_iff refine_pw_simps)
      
  lemma leof_option_rule[refine_vcg]: 
  "\<lbrakk>v = None \<Longrightarrow> S1 \<le>\<^sub>n SPEC \<Phi>; \<And>x. v = Some x \<Longrightarrow> f2 x \<le>\<^sub>n SPEC \<Phi>\<rbrakk>
    \<Longrightarrow> (case v of None \<Rightarrow> S1 | Some x \<Rightarrow> f2 x) \<le>\<^sub>n SPEC \<Phi>"
    by (cases v) auto

  lemma ASSERT_leof_rule[refine_vcg]:
    assumes "\<Phi> \<Longrightarrow> m \<le>\<^sub>n m'"
    shows "do {ASSERT \<Phi>; m} \<le>\<^sub>n m'"
    using assms
    by (cases \<Phi>, auto simp: pw_leof_iff)

  lemma leof_ASSERT_rule[refine_vcg]: "\<lbrakk>\<Phi> \<Longrightarrow> m \<le>\<^sub>n m'\<rbrakk> \<Longrightarrow> m \<le>\<^sub>n ASSERT \<Phi> \<then> m'"  
    by (auto simp: pw_leof_iff refine_pw_simps)

  lemma leof_ASSERT_refine_rule[refine]: "\<lbrakk>\<Phi> \<Longrightarrow> m \<le>\<^sub>n \<Down>R m'\<rbrakk> \<Longrightarrow> m \<le>\<^sub>n \<Down>R (ASSERT \<Phi> \<then> m')"  
    by (auto simp: pw_leof_iff refine_pw_simps)

  lemma ASSUME_leof_iff: "(ASSUME \<Phi> \<le>\<^sub>n SPEC \<Psi>) \<longleftrightarrow> (\<Phi> \<longrightarrow> \<Psi> ())"  
    by (auto simp: pw_leof_iff)

  lemma ASSUME_leof_rule[refine_vcg]: 
    assumes "\<Phi> \<Longrightarrow> \<Psi> ()" 
    shows "ASSUME \<Phi> \<le>\<^sub>n SPEC \<Psi>"
    using assms
    by (auto simp: ASSUME_leof_iff)
      
      
  lemma SPEC_rule_conj_leofI1:
    assumes "m \<le> SPEC \<Phi>"
    assumes "m \<le>\<^sub>n SPEC \<Psi>"
    shows "m \<le> SPEC (\<lambda>s. \<Phi> s \<and> \<Psi> s)"
    using assms by (auto simp: pw_le_iff pw_leof_iff)

  lemma SPEC_rule_conj_leofI2:
    assumes "m \<le>\<^sub>n SPEC \<Phi>"
    assumes "m \<le> SPEC \<Psi>"
    shows "m \<le> SPEC (\<lambda>s. \<Phi> s \<and> \<Psi> s)"
    using assms by (auto simp: pw_le_iff pw_leof_iff)

  lemma SPEC_rule_leof_conjI: 
    assumes "m \<le>\<^sub>n SPEC \<Phi>" "m \<le>\<^sub>n SPEC \<Psi>"
    shows "m \<le>\<^sub>n SPEC (\<lambda>x. \<Phi> x \<and> \<Psi> x)"
    using assms by (auto simp: pw_leof_iff)

  lemma leof_use_spec_rule:
    assumes "m \<le>\<^sub>n SPEC \<Psi>"
    assumes "m \<le>\<^sub>n SPEC (\<lambda>s. \<Psi> s \<longrightarrow> \<Phi> s)"
    shows "m \<le>\<^sub>n SPEC \<Phi>"
    using assms by (auto simp: pw_leof_iff refine_pw_simps)
  
  lemma use_spec_leof_rule:
    assumes "m \<le>\<^sub>n SPEC \<Psi>"
    assumes "m \<le> SPEC (\<lambda>s. \<Psi> s \<longrightarrow> \<Phi> s)"
    shows "m \<le> SPEC \<Phi>"
    using assms by (auto simp: pw_leof_iff pw_le_iff refine_pw_simps)

  lemma leof_strengthen_SPEC: 
    "m \<le>\<^sub>n SPEC \<Phi> \<Longrightarrow> m \<le>\<^sub>n SPEC (\<lambda>x. inres m x \<and> \<Phi> x)"
    by (auto simp: pw_leof_iff)

  lemma build_rel_SPEC_leof: 
    assumes "m \<le>\<^sub>n SPEC (\<lambda>x. I x \<and> \<Phi> (\<alpha> x))"  
    shows "m \<le>\<^sub>n \<Down>(br \<alpha> I) (SPEC \<Phi>)"
    using assms by (auto simp: build_rel_SPEC_conv)
      
  lemma RETURN_as_SPEC_refine_leof[refine2]:
    assumes "M \<le>\<^sub>n SPEC (\<lambda>c. (c,a)\<in>R)"
    shows "M \<le>\<^sub>n \<Down>R (RETURN a)"
    using assms
    by (simp add: pw_leof_iff refine_pw_simps)

  lemma ASSERT_leof_defI:
    assumes "c \<equiv> do { ASSERT \<Phi>; m'}"
    assumes "\<Phi> \<Longrightarrow> m' \<le>\<^sub>n m"
    shows "c \<le>\<^sub>n m"
    using assms by (auto simp: pw_leof_iff refine_pw_simps)
  
  lemma leof_fun_conv_le: 
    "(f x \<le>\<^sub>n M x) \<longleftrightarrow> (f x \<le> (if nofail (f x) then M x else FAIL))"
    by (auto simp: pw_le_iff pw_leof_iff)
    
  lemma leof_add_nofailI: "\<lbrakk> nofail m \<Longrightarrow> m\<le>\<^sub>nm' \<rbrakk> \<Longrightarrow> m\<le>\<^sub>nm'"
    by (auto simp: pw_le_iff pw_leof_iff)

  lemma leof_cons_rule[refine_vcg_cons]: 
    assumes "m \<le>\<^sub>n SPEC Q"
    assumes "\<And>x. Q x \<Longrightarrow> P x"  
    shows "m \<le>\<^sub>n SPEC P"
    using assms  
    by (auto simp: pw_le_iff pw_leof_iff)
      
      
lemma RECT_rule_leof:
  assumes WF: "wf (V::('x\<times>'x) set)"
  assumes I0: "pre (x::'x)"
  assumes IS: "\<And>f x. \<lbrakk> \<And>x'. \<lbrakk>pre x'; (x',x)\<in>V\<rbrakk> \<Longrightarrow> f x' \<le>\<^sub>n M x'; pre x; 
                        RECT body = f
    \<rbrakk> \<Longrightarrow> body f x \<le>\<^sub>n M x"
  shows "RECT body x \<le>\<^sub>n M x"
    apply (cases "\<not>trimono body")
    apply (simp add: RECT_def)
    using assms
    unfolding leof_fun_conv_le
    apply -
    apply (rule RECT_rule[where pre=pre and V=V])
    apply clarsimp_all
proof -
  fix xa :: 'x
  assume a1: "\<And>x'. \<lbrakk>pre x'; (x', xa) \<in> V\<rbrakk> \<Longrightarrow> REC\<^sub>T body x' \<le> (if nofail (REC\<^sub>T body x') then M x' else FAIL)"
  assume a2: "\<And>x f. \<lbrakk>\<And>x'. \<lbrakk>pre x'; (x', x) \<in> V\<rbrakk> \<Longrightarrow> f x' \<le> (if nofail (f x') then M x' else FAIL); pre x; REC\<^sub>T body = f\<rbrakk> \<Longrightarrow> body f x \<le> (if nofail (body f x) then M x else FAIL)"
  assume a3: "pre xa"
  assume a4: "nofail (REC\<^sub>T body xa)"
  assume a5: "trimono body"
  have f6: "\<forall>x. \<not> pre x \<or> (x, xa) \<notin> V \<or> (if nofail (REC\<^sub>T body x) then REC\<^sub>T body x \<le> M x else REC\<^sub>T body x \<le> FAIL)"
    using a1 by presburger
  have f7: "\<forall>x f. ((\<exists>xa. (pre xa \<and> (xa, x) \<in> V) \<and> \<not> f xa \<le> (if nofail (f xa) then M xa else FAIL)) \<or> \<not> pre x \<or> REC\<^sub>T body \<noteq> f) \<or> body f x \<le> (if nofail (body f x) then M x else FAIL)"
    using a2 by blast
  obtain xx :: "('x \<Rightarrow> 'a nres) \<Rightarrow> 'x \<Rightarrow> 'x" where
    f8: "\<forall>x0 x1. (\<exists>v2. (pre v2 \<and> (v2, x1) \<in> V) \<and> \<not> x0 v2 \<le> (if nofail (x0 v2) then M v2 else FAIL)) = ((pre (xx x0 x1) \<and> (xx x0 x1, x1) \<in> V) \<and> \<not> x0 (xx x0 x1) \<le> (if nofail (x0 (xx x0 x1)) then M (xx x0 x1) else FAIL))"
    by moura
  have f9: "\<forall>x0 x1. (x0 (xx x0 x1) \<le> (if nofail (x0 (xx x0 x1)) then M (xx x0 x1) else FAIL)) = (if nofail (x0 (xx x0 x1)) then x0 (xx x0 x1) \<le> M (xx x0 x1) else x0 (xx x0 x1) \<le> FAIL)"
    by presburger
  have "nofail (body (REC\<^sub>T body) xa)"
    using a5 a4 by (metis (no_types) RECT_unfold)
  then show "body (REC\<^sub>T body) xa \<le> M xa"
    using f9 f8 f7 f6 a3 by fastforce
qed  

(* TODO: REC_rule_leof! (However, this may require some fix 
     to the domain theory model of Refine_Monadic!) *)
      
      

end


