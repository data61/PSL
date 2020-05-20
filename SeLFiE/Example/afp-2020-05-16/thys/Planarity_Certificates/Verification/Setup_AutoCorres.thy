theory Setup_AutoCorres
imports
  Case_Labeling.Case_Labeling
  "HOL-Eisbach.Eisbach"
  AutoCorres_Misc
begin

section \<open>AutoCorres setup for VCG labelling\<close>

text \<open>Theorem collections for the VCG\<close>

ML_file \<open>../../Case_Labeling/util.ML\<close>

ML \<open>
  fun vcg_tac nt_rules nt_comb ctxt =
    let
      val rules = Named_Theorems.get ctxt nt_rules
      val comb = Named_Theorems.get ctxt nt_comb
    in REPEAT_ALL_NEW_FWD ( resolve_tac ctxt rules ORELSE' (resolve_tac ctxt comb THEN' resolve_tac ctxt rules)) end
\<close>

named_theorems vcg_l
named_theorems vcg_l_comb
named_theorems vcg_elim
named_theorems vcg_simp

method_setup vcg_l = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (FIRSTGOAL (vcg_tac @{named_theorems "vcg_l"} @{named_theorems "vcg_l_comb"} ctxt)))
\<close>

method vcg_l' = (vcg_l; (elim vcg_elim)?; (unfold vcg_simp)?)

method vcg_casify = (rule Initial_Label, vcg_l', casify)

subsection \<open>Labeled VCG theorems for branching\<close>

definition "BRANCH P \<equiv> P"

named_theorems branch_l
named_theorems branch_l_comb

context begin
  interpretation Labeling_Syntax .

  lemma DC_if[branch_l]:
    fixes ct defines "ct' \<equiv> \<lambda>pos name. (name, pos,[]) # ct"
    assumes "a \<Longrightarrow> C\<langle>Suc inp,ct' inp ''then'', outp': b\<rangle>"
    assumes "\<not>a \<Longrightarrow> C\<langle>Suc outp',ct' outp' ''else'', outp: c\<rangle>"
    shows "C\<langle>inp,ct,outp: BRANCH (if a then b else c)\<rangle>"
    using assms(2-) unfolding LABEL_simps BRANCH_def by auto

  lemma DC_final:
    assumes "V\<langle>(''g'',inp,[]), ct: a\<rangle>"
    shows "C\<langle>inp,ct,Suc inp: a\<rangle>"
    using assms unfolding LABEL_simps BRANCH_def by auto

end

method_setup branch_l = \<open>
  Scan.succeed (fn ctxt => SIMPLE_METHOD (FIRSTGOAL (vcg_tac @{named_theorems branch_l} @{named_theorems branch_l_comb} ctxt)))
\<close>

method branch_casify = ((rule Initial_Label, branch_l; (rule DC_final)?), casify)


subsection \<open>Labelled VCG theorems for the option monad\<close>

definition
  lpred_conj :: "('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> bool)" (infixr "land" 35)
where
  "lpred_conj P Q \<equiv> \<lambda>x. P x \<and> Q x"

context begin
  interpretation Labeling_Syntax .

  lemma ovalidNF_obind_K_bind [vcg_l]:
    assumes "CTXT (Suc OC1) CT OC (ovalidNF R g Q)"
      and "CTXT IC CT OC1 (ovalidNF P f (\<lambda>_. R))"
    shows "CTXT IC CT OC (ovalidNF P (f |>> K_bind g) Q)"
    using assms unfolding LABEL_simps by wp

  lemma L_ovalidNF_obind_oreturn[vcg_l]:
    assumes "CTXT IC CT OC (ovalidNF P (g x) Q)"
    shows "CTXT IC CT OC (ovalidNF P (oreturn x |>> g) Q)"
    using assms by (simp add: LABEL_simps)

  lemma L_ovalidNF_obind[vcg_l]:
    assumes "\<And>r. CTXT (Suc OC1) ((''bind'', Suc OC1, [VAR r]) # CT) OC
        (ovalidNF (R r) (g r) Q)"
      and "CTXT IC CT OC1 (ovalidNF P f R)"
    shows "CTXT IC CT OC (ovalidNF P (f |>> (\<lambda>r. g r)) Q)"
    using assms unfolding LABEL_simps by wp

  lemma ovalidNF_K_bind[vcg_l]:
    assumes "CTXT IC CT OC (ovalidNF P f Q)"
    shows "CTXT IC CT OC (ovalidNF P (K_bind f x) Q)"
    using assms by simp

  lemma L_ovalidNF_prod_case[vcg_l]:
    assumes "\<And>x y. SPLIT v (x,y) \<Longrightarrow> CTXT IC CT OC (ovalidNF (P x y) (B x y) Q)"
    shows "CTXT IC CT OC (ovalidNF (case v of (x, y) \<Rightarrow> P x y) (case v of (x, y) \<Rightarrow> B x y) Q)"
    using assms unfolding LABEL_simps by (auto simp: ovalidNF_def)

  lemma L_ovalidNF_oreturn_NF[vcg_l]:
    shows "CTXT IC CT IC (ovalidNF (P x) (oreturn x) P)"
    unfolding LABEL_simps by wp

  lemma L_ovalidNF_owhile_inv[vcg_l]:
    fixes CT IC
    defines "CT' \<equiv> \<lambda>r. (''while'', IC, [VAR r]) # CT"
    assumes "\<And>r s. CTXT IC ((''invariant'', IC, [VAR s]) # CT' r) OC
        (ovalidNF
          (BIND ''loop_inv'' IC (I r) land
            BIND ''loop_cond'' IC (C r) land
            BIND ''loop_var'' IC (\<lambda>s'. s' = s))
          (B r)
          (\<lambda>r'. BIND ''inv'' IC (I r') land BIND ''var'' IC (\<lambda>_. (r', r) \<in> R)))"
      and "\<And>r. VC (''wf'', OC, []) (CT' r) (wf R)"
      and "\<And>r s. I r s \<Longrightarrow> \<not> C r s \<Longrightarrow>
        VC (''postcondition'', Suc OC, [VAR s]) (CT' r) (Q r s)"
    shows "CTXT IC CT (Suc OC) (ovalidNF (I r) (owhile_inv C B r I R) Q)"
    using assms unfolding LABEL_simps lpred_conj_def by wp auto

  lemma L_ovalidNF_wp_comb2[vcg_l_comb]:
    assumes "CTXT IC CT OC (ovalidNF P f Q)"
      and "\<And>s. P' s \<Longrightarrow> VC (''weaken'', IC, [VAR s]) CT (P s)"
    shows "CTXT IC CT OC (ovalidNF P' f Q)"
    using assms unfolding LABEL_simps by (rule ovalidNF_wp_comb2)

  lemma L_condition_NF_wp[vcg_l]:
    fixes CT IC
    defines "CT' \<equiv> (''if'', IC, []) # CT"
    assumes "CTXT IC ((''then'', IC, []) # CT') OC1 (ovalidNF L l Q)"
      and "CTXT (Suc OC1) ((''else'', Suc OC1, []) # CT') OC (ovalidNF R r Q)"
    shows "CTXT IC CT OC (ovalidNF (\<lambda>s. BRANCH (if C s then L s else R s)) (ocondition C l r) Q)"
    using assms unfolding LABEL_simps BRANCH_def by wp

  lemma L_ogets_NF_wp[vcg_l]: "CTXT IC CT IC (ovalidNF (\<lambda>s. P (f s) s) (ogets f) P)"
    unfolding LABEL_simps by wp

  lemma elim_land[vcg_elim]:
    assumes "(P land Q) s" obtains "P s" "Q s"
    using assms by (auto simp: lpred_conj_def)

  lemma simp_bind[vcg_simp]: "BIND ct n P s \<longleftrightarrow> BIND ct n (P s)"
    by (auto simp: LABEL_simps)

  lemma simp_land[vcg_simp]: "(P land Q) s \<longleftrightarrow> P s \<and> Q s"
    by (auto simp: lpred_conj_def)
end

end
