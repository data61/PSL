section \<open>Relations\<close>

theory Relation_Extensions
imports
  Basic_Extensions
begin

  abbreviation rev_lex_prod (infixr "<*rlex*>" 80)
    where "r\<^sub>1 <*rlex*> r\<^sub>2 \<equiv> inv_image (r\<^sub>2 <*lex*> r\<^sub>1) swap"

  lemmas sym_rtranclp[intro] = sym_rtrancl[to_pred]

  definition liftablep :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'a) \<Rightarrow> bool"
    where "liftablep r f \<equiv> \<forall> x y. r x y \<longrightarrow> r (f x) (f y)"

  lemma liftablepI[intro]:
    assumes "\<And> x y. r x y \<Longrightarrow> r (f x) (f y)"
    shows "liftablep r f"
    using assms
    unfolding liftablep_def
    by simp
  lemma liftablepE[elim]:
    assumes "liftablep r f"
    assumes "r x y"
    obtains "r (f x) (f y)"
    using assms
    unfolding liftablep_def
    by simp

  lemma liftablep_rtranclp:
    assumes "liftablep r f"
    shows "liftablep r\<^sup>*\<^sup>* f"
  proof
    fix x y
    assume "r\<^sup>*\<^sup>* x y"
    thus "r\<^sup>*\<^sup>* (f x) (f y)"
      using assms
      by (induct rule: rtranclp_induct, force+)
  qed

  definition confluentp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
    where "confluentp r \<equiv> \<forall> x y1 y2. r\<^sup>*\<^sup>* x y1 \<longrightarrow> r\<^sup>*\<^sup>* x y2 \<longrightarrow> (\<exists> z. r\<^sup>*\<^sup>* y1 z \<and> r\<^sup>*\<^sup>* y2 z)"

  lemma confluentpI[intro]:
    assumes "\<And> x y1 y2. r\<^sup>*\<^sup>* x y1 \<Longrightarrow> r\<^sup>*\<^sup>* x y2 \<Longrightarrow> \<exists> z. r\<^sup>*\<^sup>* y1 z \<and> r\<^sup>*\<^sup>* y2 z"
    shows "confluentp r"
    using assms
    unfolding confluentp_def
    by simp

  lemma confluentpE[elim]:
    assumes "confluentp r"
    assumes "r\<^sup>*\<^sup>* x y1" "r\<^sup>*\<^sup>* x y2"
    obtains z
    where "r\<^sup>*\<^sup>* y1 z" "r\<^sup>*\<^sup>* y2 z"
    using assms
    unfolding confluentp_def
    by blast

  lemma confluentpI'[intro]:
    assumes "\<And> x y1 y2. r\<^sup>*\<^sup>* x y1 \<Longrightarrow> r x y2 \<Longrightarrow> \<exists> z. r\<^sup>*\<^sup>* y1 z \<and> r\<^sup>*\<^sup>* y2 z"
    shows "confluentp r"
  proof
    fix x y1 y2
    assume "r\<^sup>*\<^sup>* x y1" "r\<^sup>*\<^sup>* x y2"
    thus "\<exists> z. r\<^sup>*\<^sup>* y1 z \<and> r\<^sup>*\<^sup>* y2 z" using assms by (induct rule: rtranclp_induct, force+)
  qed

  lemma transclp_eq_implies_confluent_imp:
    assumes "r1\<^sup>*\<^sup>* = r2\<^sup>*\<^sup>*"
    assumes "confluentp r1"
    shows "confluentp r2"
    using assms
    by force

  lemma transclp_eq_implies_confluent_eq:
    assumes "r1\<^sup>*\<^sup>* = r2\<^sup>*\<^sup>*"
    shows "confluentp r1 \<longleftrightarrow> confluentp r2"
    using assms transclp_eq_implies_confluent_imp
    by metis

  definition diamondp :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool"
    where "diamondp r \<equiv> \<forall> x y1 y2. r x y1 \<longrightarrow> r x y2 \<longrightarrow> (\<exists> z. r y1 z \<and> r y2 z)"

  lemma diamondpI[intro]:
    assumes "\<And> x y1 y2. r x y1 \<Longrightarrow> r x y2 \<Longrightarrow> \<exists> z. r y1 z \<and> r y2 z"
    shows "diamondp r"
    using assms
    unfolding diamondp_def
    by simp

  lemma diamondpE[elim]:
    assumes "diamondp r"
    assumes "r x y1" "r x y2"
    obtains z
    where "r y1 z" "r y2 z"
    using assms
    unfolding diamondp_def
    by blast

  lemma diamondp_implies_confluentp:
    assumes "diamondp r"
    shows "confluentp r"
  proof (rule confluentpI')
    fix x y1 y2
    assume "r\<^sup>*\<^sup>* x y1" "r x y2"
    hence "\<exists> z. r y1 z \<and> r\<^sup>*\<^sup>* y2 z" using assms by (induct rule: rtranclp_induct, force+)
    thus "\<exists> z. r\<^sup>*\<^sup>* y1 z \<and> r\<^sup>*\<^sup>* y2 z" by blast
  qed

  locale wellfounded_relation =
    fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
    assumes wellfounded: "wfP R"

end

