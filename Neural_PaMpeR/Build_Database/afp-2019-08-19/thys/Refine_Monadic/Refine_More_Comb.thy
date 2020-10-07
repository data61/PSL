section \<open>More Combinators\<close>
theory Refine_More_Comb
imports Refine_Basic Refine_Heuristics Refine_Leof
begin

subsubsection \<open>OBTAIN Combinator\<close>

text \<open>Obtain value with given property, asserting that there exists one.\<close>  
definition OBTAIN :: "('a \<Rightarrow> bool) \<Rightarrow> 'a nres" 
  where
  "OBTAIN P \<equiv> ASSERT (\<exists>x. P x) \<then> SPEC P"

lemma OBTAIN_nofail[refine_pw_simps]: "nofail (OBTAIN P) \<longleftrightarrow> (\<exists>x. P x)"
  unfolding OBTAIN_def
  by (auto simp: refine_pw_simps)
lemma OBTAIN_inres[refine_pw_simps]: "inres (OBTAIN P) x \<longleftrightarrow> (\<forall>x. \<not>P x) \<or> P x"
  unfolding OBTAIN_def
  by (auto simp: refine_pw_simps)
lemma OBTAIN_rule[refine_vcg]: "\<lbrakk> \<exists>x. P x; \<And>x. P x \<Longrightarrow> Q x  \<rbrakk> \<Longrightarrow> OBTAIN P \<le> SPEC Q"
  unfolding OBTAIN_def
  by auto
lemma OBTAIN_refine_iff: "OBTAIN P \<le>\<Down>R (OBTAIN Q) \<longleftrightarrow> (Ex Q \<longrightarrow> Ex P \<and> Collect P \<subseteq> R\<inverse>``Collect Q)"
  unfolding OBTAIN_def by (auto simp: pw_le_iff refine_pw_simps)

lemma OBTAIN_refine[refine]:
  assumes "RELATES R"
  assumes "\<And>x. Q x \<Longrightarrow> Ex P"
  assumes "\<And>x y. \<lbrakk>Q x; P y\<rbrakk> \<Longrightarrow> \<exists>x'. (y,x')\<in>R \<and> Q x'"
  shows "OBTAIN P \<le>\<Down>R (OBTAIN Q)"
  using assms unfolding OBTAIN_refine_iff 
  by blast
  
subsubsection \<open>SELECT Combinator\<close>

text \<open>Select some value with given property, or \<open>None\<close> if there is none.\<close>  
definition SELECT :: "('a \<Rightarrow> bool) \<Rightarrow> 'a option nres"
  where "SELECT P \<equiv> if \<exists>x. P x then RES {Some x| x. P x} else RETURN None"
  
lemma SELECT_rule[refine_vcg]:
  assumes "\<And>x. P x \<Longrightarrow> Q (Some x)"
  assumes "\<forall>x. \<not>P x \<Longrightarrow> Q None"
  shows "SELECT P \<le> SPEC Q"
  unfolding SELECT_def
  using assms
  by auto

lemma SELECT_refine_iff: "(SELECT P \<le>\<Down>(\<langle>R\<rangle>option_rel) (SELECT P')) 
  \<longleftrightarrow> (  
    (Ex P' \<longrightarrow> Ex P) \<and>
    (\<forall>x. P x \<longrightarrow> (\<exists>x'. (x,x')\<in>R \<and> P' x'))
  )"  
  by (force simp: SELECT_def pw_le_iff refine_pw_simps) 

lemma SELECT_refine[refine]:
  assumes "RELATES R"
  assumes "\<And>x'. P' x' \<Longrightarrow> \<exists>x. P x"
  assumes "\<And>x. P x \<Longrightarrow> \<exists>x'. (x,x')\<in>R \<and> P' x'"
  shows "SELECT P \<le>\<Down>(\<langle>R\<rangle>option_rel) (SELECT P')"
  unfolding SELECT_refine_iff using assms by blast

lemma SELECT_as_SPEC: "SELECT P = SPEC (\<lambda>None \<Rightarrow> \<forall>x. \<not>P x | Some x \<Rightarrow> P x)"
  unfolding SELECT_def by (auto simp: pw_eq_iff split: option.split)

lemma SELECT_pw[refine_pw_simps]:
  "nofail (SELECT P)"  
  "inres (SELECT P) r \<longleftrightarrow> (r=None \<longrightarrow> (\<forall>x. \<not>P x)) \<and> (\<forall>x. r=Some x \<longrightarrow> P x)"
  unfolding SELECT_def
  by auto

lemma SELECT_pw_simps[simp]:
  "nofail (SELECT P)"
  "inres (SELECT P) None \<longleftrightarrow> (\<forall>x. \<not>P x)"
  "inres (SELECT P) (Some x) \<longleftrightarrow> P x"
  by (auto simp: refine_pw_simps)

end
