section \<open>A type class for correspondence between HOL expressions and terms\<close>

theory Eval_Class
imports
  "../Rewriting/Rewriting_Term"
  "../Utils/ML_Utils"
  Deriving.Derive_Manager
  "Dict_Construction.Dict_Construction"
begin

no_notation Mpat_Antiquot.mpaq_App (infixl "$$" 900)
hide_const (open) Strong_Term.wellformed
declare Strong_Term.wellformed_term_def[simp del]

class evaluate =
  fixes eval :: "rule fset \<Rightarrow> term \<Rightarrow> 'a \<Rightarrow> bool" ("_/ \<turnstile>/ (_ \<approx>/ _)" [50,0,50] 50)
  assumes eval_wellformed: "rs \<turnstile> t \<approx> a \<Longrightarrow> wellformed t"
begin

definition eval' :: "rule fset \<Rightarrow> term \<Rightarrow> 'a \<Rightarrow> bool" ("_/ \<turnstile>/ (_ \<down>/ _)" [50,0,50] 50) where
"rs \<turnstile> t \<down> a \<longleftrightarrow> wellformed t \<and> (\<exists>t'. rs \<turnstile> t \<longrightarrow>* t' \<and> rs \<turnstile> t' \<approx> a)"

lemma eval'I[intro]:
  assumes "wellformed t" "rs \<turnstile> t \<longrightarrow>* t'" "rs \<turnstile> t' \<approx> a"
  shows "rs \<turnstile> t \<down> a"
using assms unfolding eval'_def by auto

lemma eval'E[elim]:
  assumes "rs \<turnstile> t \<down> a"
  obtains t' where "wellformed t" "rs \<turnstile> t \<longrightarrow>* t'" "rs \<turnstile> t' \<approx> a"
using assms unfolding eval'_def by auto

lemma eval_trivI: "rs \<turnstile> t \<approx> a \<Longrightarrow> rs \<turnstile> t \<down> a"
by (auto dest: eval_wellformed)

lemma eval_compose:
  assumes "wellformed t" "rs \<turnstile> t \<longrightarrow>* t'" "rs \<turnstile> t' \<down> a"
  shows "rs \<turnstile> t \<down> a"
proof -
  from \<open>rs \<turnstile> t' \<down> a\<close> obtain t'' where "rs \<turnstile> t' \<longrightarrow>* t''" "rs \<turnstile> t'' \<approx> a"
    by blast
  moreover hence "rs \<turnstile> t \<longrightarrow>* t''"
    using assms by auto
  ultimately show "rs \<turnstile> t \<down> a"
    using assms by auto
qed

end

instantiation "fun" :: (evaluate, evaluate) evaluate begin

  definition eval_fun where
  "eval_fun rs t a \<longleftrightarrow> wellformed t \<and> (\<forall>x t\<^sub>x. rs \<turnstile> t\<^sub>x \<down> x \<longrightarrow> rs \<turnstile> t $ t\<^sub>x \<down> a x)"

  instance
    by standard (simp add: eval_fun_def)

end

corollary eval_funD:
  assumes "rs \<turnstile> t \<approx> f" "rs \<turnstile> t\<^sub>x \<down> x"
  shows "rs \<turnstile> t $ t\<^sub>x \<down> f x"
using assms unfolding eval_fun_def by blast

corollary eval'_funD:
  assumes "rs \<turnstile> t \<down> f" "rs \<turnstile> t\<^sub>x \<down> x"
  shows "rs \<turnstile> t $ t\<^sub>x \<down> f x"
proof -
  from assms obtain t' where "rs \<turnstile> t \<longrightarrow>* t'" "rs \<turnstile> t' \<approx> f"
    by auto
  have "wellformed (t $ t\<^sub>x)"
    using assms by auto
  moreover have "rs \<turnstile> t $ t\<^sub>x \<longrightarrow>* t' $ t\<^sub>x"
    using \<open>rs \<turnstile> t \<longrightarrow>* t'\<close> by (rule rewrite.rt_fun[unfolded app_term_def])
  moreover have "rs \<turnstile> t' $ t\<^sub>x \<down> f x"
    using \<open>rs \<turnstile> t' \<approx> f\<close> assms(2) by (rule eval_funD)
  ultimately show "rs \<turnstile> t $ t\<^sub>x \<down> f x"
    by (rule eval_compose)
qed

lemma eval_ext:
  assumes "wellformed f" "\<And>x t. rs \<turnstile> t \<down> x \<Longrightarrow> rs \<turnstile> f $ t \<down> a x"
  shows "rs \<turnstile> f \<approx> a"
using assms unfolding eval_fun_def by blast

lemma eval'_ext:
  assumes "wellformed f" "\<And>x t. rs \<turnstile> t \<down> x \<Longrightarrow> rs \<turnstile> f $ t \<down> a x"
  shows "rs \<turnstile> f \<down> a"
apply (rule eval'I[OF \<open>wellformed f\<close>])
apply (rule rtranclp.rtrancl_refl)
apply (rule eval_ext)
using assms by auto

lemma eval'_ext_alt:
  fixes f :: "'a::evaluate \<Rightarrow> 'b::evaluate"
  assumes "wellformed' 1 t" "\<And>u x. rs \<turnstile> u \<down> x \<Longrightarrow> rs \<turnstile> t [u]\<^sub>\<beta> \<down> f x"
  shows "rs \<turnstile> \<Lambda> t \<down> f"
proof (rule eval'_ext)
  show "wellformed (\<Lambda> t)"
    using assms by simp
next
  fix x :: 'a and u
  assume "rs \<turnstile> u \<down> x"
  show "rs \<turnstile> \<Lambda> t $ u \<down> f x"
    proof (rule eval_compose)
      show "wellformed (\<Lambda> t $ u)"
        using assms \<open>rs \<turnstile> u \<down> x\<close> by auto
    next
      show "rs \<turnstile> \<Lambda> t $ u \<longrightarrow>* t [u]\<^sub>\<beta>"
        using \<open>rs \<turnstile> u \<down> x\<close> by (auto intro: rewrite.beta)
    next
      show "rs \<turnstile> t [u]\<^sub>\<beta> \<down> f x"
        using assms \<open>rs \<turnstile> u \<down> x\<close> by auto
    qed
qed

lemma eval_impl_wellformed[dest]: "rs \<turnstile> t \<approx> a \<Longrightarrow> wellformed' n t"
by (auto dest: wellformed_inc eval_wellformed[unfolded wellformed_term_def])

lemma eval'_impl_wellformed[dest]: "rs \<turnstile> t \<down> a \<Longrightarrow> wellformed' n t"
unfolding eval'_def by (auto dest: wellformed_inc)

lemma wellformed_unpack:
  "wellformed' n (t $ u) \<Longrightarrow> wellformed' n t"
  "wellformed' n (t $ u) \<Longrightarrow> wellformed' n u"
  "wellformed' n (\<Lambda> t) \<Longrightarrow> wellformed' (Suc n) t"
by auto

lemma replace_bound_aux:
  "n < 0 \<longleftrightarrow> False"
  "Suc n < Suc m \<longleftrightarrow> n < m"
  "0 < Suc n \<longleftrightarrow> True"
  "((0::nat) = 0) \<longleftrightarrow> True"
  "(0 = Suc m) \<longleftrightarrow> False"
  "(Suc m = Suc n) \<longleftrightarrow> n = m"
  "(Suc m = 0) \<longleftrightarrow> False"
  "(if True then P else Q) = P"
  "(if False then P else Q) = Q"
  "int (0::nat) = 0"
by auto

named_theorems eval_data_intros
named_theorems eval_data_elims

context begin

(* for code generation, used in Tactics.code_tac *)
private definition rewrite_step_term :: "term \<times> term \<Rightarrow> term \<Rightarrow> term option" where
"rewrite_step_term = rewrite_step"

private lemmas rewrite_rt_fun = rewrite.rt_fun[unfolded app_term_def]
private lemmas rewrite_rt_arg = rewrite.rt_arg[unfolded app_term_def]

ML_file "tactics.ML"

end

method_setup wellformed = \<open>Scan.succeed (SIMPLE_METHOD' o Tactics.wellformed_tac)\<close>

end