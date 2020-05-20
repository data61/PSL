section \<open>Higher-order term rewriting using de-Bruijn indices\<close>

theory Rewriting_Term
imports
  "../Terms/General_Rewriting"
  "../Terms/Strong_Term"
begin

subsection \<open>Matching and rewriting\<close>

type_synonym rule = "term \<times> term"

inductive rewrite :: "rule fset \<Rightarrow> term \<Rightarrow> term \<Rightarrow> bool" ("_/ \<turnstile>/ _ \<longrightarrow>/ _" [50,0,50] 50) for rs where
step: "r |\<in>| rs \<Longrightarrow> r \<turnstile> t \<rightarrow> u \<Longrightarrow> rs \<turnstile> t \<longrightarrow> u" |
beta: "rs \<turnstile> (\<Lambda> t $ t') \<longrightarrow> t [t']\<^sub>\<beta>" |
"fun": "rs \<turnstile> t \<longrightarrow> t'\<Longrightarrow> rs \<turnstile> t $ u \<longrightarrow> t' $ u" |
arg: "rs \<turnstile> u \<longrightarrow> u'\<Longrightarrow> rs \<turnstile> t $ u \<longrightarrow> t $ u'"

global_interpretation rewrite: rewriting "rewrite rs" for rs
by standard (auto intro: rewrite.intros simp: app_term_def)+

abbreviation rewrite_rt :: "rule fset \<Rightarrow> term \<Rightarrow> term \<Rightarrow> bool" ("_/ \<turnstile>/ _ \<longrightarrow>*/ _" [50,0,50] 50) where
"rewrite_rt rs \<equiv> (rewrite rs)\<^sup>*\<^sup>*"

lemma rewrite_beta_alt: "t [t']\<^sub>\<beta> = u \<Longrightarrow> wellformed t' \<Longrightarrow> rs \<turnstile> (\<Lambda> t $ t') \<longrightarrow> u"
by (metis rewrite.beta)

subsection \<open>Wellformedness\<close>

primrec rule :: "rule \<Rightarrow> bool" where
"rule (lhs, rhs) \<longleftrightarrow> basic_rule (lhs, rhs) \<and> Term.wellformed rhs"

lemma ruleI[intro]:
  assumes "basic_rule (lhs, rhs)"
  assumes "Term.wellformed rhs"
  shows "rule (lhs, rhs)"
using assms by simp

lemma split_rule_fst: "fst (split_rule r) = head (fst r)"
unfolding head_def by (smt prod.case_eq_if prod.collapse prod.inject split_rule.simps)

locale rules = constants C_info "heads_of rs" for C_info and rs :: "rule fset" +
  assumes all_rules: "fBall rs rule"
  assumes arity: "arity_compatibles rs"
  assumes fmap: "is_fmap rs"
  assumes patterns: "pattern_compatibles rs"
  assumes nonempty: "rs \<noteq> {||}"
  assumes not_shadows: "fBall rs (\<lambda>(lhs, _). \<not> shadows_consts lhs)"
  assumes welldefined_rs: "fBall rs (\<lambda>(_, rhs). welldefined rhs)"
begin

lemma rewrite_wellformed:
  assumes "rs \<turnstile> t \<longrightarrow> t'" "wellformed t"
  shows "wellformed t'"
using assms
proof (induction rule: rewrite.induct)
  case (step r t u)
  obtain lhs rhs where "r = (lhs, rhs)"
    by force
  hence "wellformed rhs"
    using all_rules step by force
  show ?case
    apply (rule wellformed.rewrite_step)
      apply (rule step(2)[unfolded \<open>r = _\<close>])
     apply fact+
    done
next
  case (beta u t)
  show ?case
    unfolding wellformed_term_def
    apply (rule replace_bound_wellformed)
    using beta by auto
qed auto

lemma rewrite_rt_wellformed: "rs \<turnstile> t \<longrightarrow>* t' \<Longrightarrow> wellformed t \<Longrightarrow> wellformed t'"
by (induction rule: rtranclp.induct) (auto intro: rewrite_wellformed simp del: wellformed_term_def)

lemma rewrite_closed: "rs \<turnstile> t \<longrightarrow> t' \<Longrightarrow> closed t \<Longrightarrow> closed t'"
proof (induction t t' rule: rewrite.induct)
  case (step r t u)
  obtain lhs rhs where "r = (lhs, rhs)"
    by force
  with step have "rule (lhs, rhs)"
    using all_rules by blast
  hence "frees rhs |\<subseteq>| frees lhs"
    by simp
  moreover have "(lhs, rhs) \<turnstile> t \<rightarrow> u"
    using step unfolding \<open>r = _\<close> by simp
  show ?case
    apply (rule rewrite_step_closed)
    apply fact+
    done
next
  case (beta t t')
  have "frees t [t']\<^sub>\<beta> |\<subseteq>| frees t |\<union>| frees t'"
    by (rule replace_bound_frees)
  with beta show ?case
    unfolding closed_except_def by auto
qed (auto simp: closed_except_def)

lemma rewrite_rt_closed: "rs \<turnstile> t \<longrightarrow>* t' \<Longrightarrow> closed t \<Longrightarrow> closed t'"
by (induction rule: rtranclp.induct) (auto intro: rewrite_closed)

end

end