section \<open>Higher-order term rewriting using explicit bound variable names\<close>

theory Rewriting_Nterm
imports
  Rewriting_Term
  Higher_Order_Terms.Term_to_Nterm
  "../Terms/Strong_Term"
begin

subsection \<open>Definitions\<close>

type_synonym nrule = "term \<times> nterm"

abbreviation nrule :: "nrule \<Rightarrow> bool" where
"nrule \<equiv> basic_rule"

fun (in constants) not_shadowing :: "nrule \<Rightarrow> bool" where
"not_shadowing (lhs, rhs) \<longleftrightarrow> \<not> shadows_consts lhs \<and> \<not> shadows_consts rhs"

locale nrules = constants C_info "heads_of rs" for C_info and rs :: "nrule fset" +
  assumes all_rules: "fBall rs nrule"
  assumes arity: "arity_compatibles rs"
  assumes fmap: "is_fmap rs"
  assumes patterns: "pattern_compatibles rs"
  assumes nonempty: "rs \<noteq> {||}"
  assumes not_shadows: "fBall rs not_shadowing"
  assumes welldefined_rs: "fBall rs (\<lambda>(_, rhs). welldefined rhs)"


subsection \<open>Matching and rewriting\<close>

inductive nrewrite :: "nrule fset \<Rightarrow> nterm \<Rightarrow> nterm \<Rightarrow> bool" ("_/ \<turnstile>\<^sub>n/ _ \<longrightarrow>/ _" [50,0,50] 50) for rs where
step: "r |\<in>| rs \<Longrightarrow> r \<turnstile> t \<rightarrow> u \<Longrightarrow> rs \<turnstile>\<^sub>n t \<longrightarrow> u" |
beta: "rs \<turnstile>\<^sub>n ((\<Lambda>\<^sub>n x. t) $\<^sub>n t') \<longrightarrow> subst t (fmap_of_list [(x, t')])" |
"fun": "rs \<turnstile>\<^sub>n t \<longrightarrow> t' \<Longrightarrow> rs \<turnstile>\<^sub>n t $\<^sub>n u \<longrightarrow> t' $\<^sub>n u" |
arg: "rs \<turnstile>\<^sub>n u \<longrightarrow> u' \<Longrightarrow> rs \<turnstile>\<^sub>n t $\<^sub>n u \<longrightarrow> t $\<^sub>n u'"

global_interpretation nrewrite: rewriting "nrewrite rs" for rs
by standard (auto intro: nrewrite.intros simp: app_nterm_def)+

abbreviation nrewrite_rt :: "nrule fset \<Rightarrow> nterm \<Rightarrow> nterm \<Rightarrow> bool" ("_/ \<turnstile>\<^sub>n/ _ \<longrightarrow>*/ _" [50,0,50] 50) where
"nrewrite_rt rs \<equiv> (nrewrite rs)\<^sup>*\<^sup>*"

lemma (in nrules) nrewrite_closed:
  assumes "rs \<turnstile>\<^sub>n t \<longrightarrow> t'" "closed t"
  shows "closed t'"
using assms proof induction
  case (step r t u)
  obtain lhs rhs where "r = (lhs, rhs)"
    by force
  with step have "nrule (lhs, rhs)"
    using all_rules by blast
  hence "frees rhs |\<subseteq>| frees lhs"
    by simp
  have "(lhs, rhs) \<turnstile> t \<rightarrow> u"
    using step unfolding \<open>r = _\<close> by simp

  show ?case
    apply (rule rewrite_step_closed)
      apply fact+
    done
next
  case beta
  show ?case
    apply simp
    apply (subst closed_except_def)
    apply (subst subst_frees)
    using beta unfolding closed_except_def by auto
qed (auto simp: closed_except_def)

corollary (in nrules) nrewrite_rt_closed:
  assumes "rs \<turnstile>\<^sub>n t \<longrightarrow>* t'" "closed t"
  shows "closed t'"
using assms
by induction (auto intro: nrewrite_closed)

subsection \<open>Translation from @{typ term} to @{typ nterm}\<close>

context begin

private lemma term_to_nterm_all_vars0:
  assumes "wellformed' (length \<Gamma>) t"
  shows "\<exists>T. all_frees (fst (run_state (term_to_nterm \<Gamma> t) x)) |\<subseteq>| fset_of_list \<Gamma> |\<union>| frees t |\<union>| T \<and> fBall T (\<lambda>y. y > x)"
using assms proof (induction \<Gamma> t arbitrary: x rule: term_to_nterm_induct)
  case (bound \<Gamma> i)
  hence "\<Gamma> ! i |\<in>| fset_of_list \<Gamma>"
    by (simp add: fset_of_list_elem)
  with bound show ?case
    by (auto simp: State_Monad.return_def)
next
  case (abs \<Gamma> t)

  obtain T
    where "all_frees (fst (run_state (term_to_nterm (next x # \<Gamma>) t) (next x))) |\<subseteq>| fset_of_list (next x # \<Gamma>) |\<union>| frees t |\<union>| T"
      and "fBall T ((<) (next x))"
    apply atomize_elim
    apply (rule abs(1))
    using abs by auto

  show ?case
    apply (simp add: split_beta create_alt_def)
    apply (rule exI[where x = "finsert (next x) T"])
    apply (intro conjI)
    subgoal by auto
    subgoal using \<open>all_frees (fst (run_state _ (next x))) |\<subseteq>| _\<close> by simp
    subgoal
      apply simp
      apply (rule conjI)
       apply (rule next_ge)
      using \<open>fBall T ((<) (next x))\<close>
      by (metis fBallE fBallI fresh_class.next_ge order.strict_trans)
    done
next
  case (app \<Gamma> t\<^sub>1 t\<^sub>2 x\<^sub>1)
  obtain t\<^sub>1' x\<^sub>2 where "run_state (term_to_nterm \<Gamma> t\<^sub>1) x\<^sub>1 = (t\<^sub>1', x\<^sub>2)"
    by fastforce
  moreover obtain T\<^sub>1
    where "all_frees (fst (run_state (term_to_nterm \<Gamma> t\<^sub>1) x\<^sub>1)) |\<subseteq>| fset_of_list \<Gamma> |\<union>| frees t\<^sub>1 |\<union>| T\<^sub>1"
      and "fBall T\<^sub>1 ((<) x\<^sub>1)"
    apply atomize_elim
    apply (rule app(1))
    using app by auto
  ultimately have "all_frees t\<^sub>1' |\<subseteq>| fset_of_list \<Gamma> |\<union>| frees t\<^sub>1 |\<union>| T\<^sub>1"
    by simp

  obtain T\<^sub>2
    where "all_frees (fst (run_state (term_to_nterm \<Gamma> t\<^sub>2) x\<^sub>2)) |\<subseteq>| fset_of_list \<Gamma> |\<union>| frees t\<^sub>2 |\<union>| T\<^sub>2"
      and "fBall T\<^sub>2 ((<) x\<^sub>2)"
    apply atomize_elim
    apply (rule app(2))
    using app by auto
  moreover obtain t\<^sub>2' x' where "run_state (term_to_nterm \<Gamma> t\<^sub>2) x\<^sub>2 = (t\<^sub>2', x')"
    by fastforce
  ultimately have "all_frees t\<^sub>2' |\<subseteq>| fset_of_list \<Gamma> |\<union>| frees t\<^sub>2 |\<union>| T\<^sub>2"
    by simp

  have "x\<^sub>1 \<le> x\<^sub>2"
    apply (rule state_io_relD[OF term_to_nterm_mono])
    apply fact
    done

  show ?case
    apply simp
    unfolding \<open>run_state (term_to_nterm \<Gamma> t\<^sub>1) x\<^sub>1 = _\<close>
    apply simp
    unfolding \<open>run_state (term_to_nterm \<Gamma> t\<^sub>2) x\<^sub>2 = _\<close>
    apply simp
    apply (rule exI[where x = "T\<^sub>1 |\<union>| T\<^sub>2"])
    apply (intro conjI)
    subgoal using \<open>all_frees t\<^sub>1' |\<subseteq>| _\<close> by auto
    subgoal using \<open>all_frees t\<^sub>2' |\<subseteq>| _\<close> by auto
    subgoal
      apply auto
      using \<open>fBall T\<^sub>1 ((<) x\<^sub>1)\<close> apply auto[]
      using \<open>fBall T\<^sub>2 ((<) x\<^sub>2)\<close> \<open>x\<^sub>1 \<le> x\<^sub>2\<close>
      by (meson fBallE less_le_not_le order_trans)
    done
qed auto

lemma term_to_nterm_all_vars:
  assumes "wellformed t" "fdisjnt (frees t) S"
  shows "fdisjnt (all_frees (fresh_frun (term_to_nterm [] t) (T |\<union>| S))) S"
proof -
  let ?\<Gamma> = "[]"
  let ?x = "fresh_fNext (T |\<union>| S)"
  from assms have "wellformed' (length ?\<Gamma>) t"
    by simp
  then obtain F
    where "all_frees (fst (run_state (term_to_nterm ?\<Gamma> t) ?x)) |\<subseteq>| fset_of_list ?\<Gamma> |\<union>| frees t |\<union>| F"
      and "fBall F (\<lambda>y. y > ?x)"
    by (metis term_to_nterm_all_vars0)

  have "fdisjnt F (T |\<union>| S)" if "S \<noteq> {||}"
    apply (rule fdisjnt_ge_max)
    apply (rule fBall_pred_weaken[OF _ \<open>fBall F (\<lambda>y. y > ?x)\<close>])
    apply (rule less_trans)
     apply (rule fNext_ge_max)
    using that by auto
  show ?thesis
    apply (rule fdisjnt_subset_left)
     apply (subst fresh_frun_def)
     apply (subst fresh_fNext_def[symmetric])
     apply fact
    apply simp
    apply (rule fdisjnt_union_left)
     apply fact
    using \<open>_ \<Longrightarrow> fdisjnt F (T |\<union>| S)\<close> by (auto simp: fdisjnt_alt_def)
qed

end

fun translate_rule :: "name fset \<Rightarrow> rule \<Rightarrow> nrule" where
"translate_rule S (lhs, rhs) = (lhs, fresh_frun (term_to_nterm [] rhs) (frees lhs |\<union>| S))"

lemma translate_rule_alt_def:
  "translate_rule S = (\<lambda>(lhs, rhs). (lhs, fresh_frun (term_to_nterm [] rhs) (frees lhs |\<union>| S)))"
by auto

definition compile' where
"compile' C_info rs = translate_rule (pre_constants.all_consts C_info (heads_of rs)) |`| rs"

context rules begin

definition compile :: "nrule fset" where
"compile = translate_rule all_consts |`| rs"

lemma compile'_compile_eq[simp]: "compile' C_info rs = compile"
unfolding compile'_def compile_def ..

lemma compile_heads: "heads_of compile = heads_of rs"
unfolding compile_def translate_rule_alt_def head_def[abs_def]
by force

lemma compile_rules: "nrules C_info compile"
proof
  have "fBall compile (\<lambda>(lhs, rhs). nrule (lhs, rhs))"
    proof safe
      fix lhs rhs
      assume "(lhs, rhs) |\<in>| compile"
      then obtain rhs'
        where "(lhs, rhs') |\<in>| rs"
          and rhs: "rhs = fresh_frun (term_to_nterm [] rhs') (frees lhs |\<union>| all_consts)"
        unfolding compile_def by force
      then have rule: "rule (lhs, rhs')"
        using all_rules by blast

      show "nrule (lhs, rhs)"
        proof
          from rule show "linear lhs" "is_const (fst (strip_comb lhs))" "\<not> is_const lhs" by auto

          have "frees rhs |\<subseteq>| frees rhs'"
            unfolding rhs using rule
            by (metis rule.simps term_to_nterm_vars)
          also have "frees rhs' |\<subseteq>| frees lhs"
            using rule by auto
          finally show "frees rhs |\<subseteq>| frees lhs" .
        qed
    qed

  thus "fBall compile nrule"
    by fast
next
  show "arity_compatibles compile"
    proof safe
      fix lhs\<^sub>1 rhs\<^sub>1 lhs\<^sub>2 rhs\<^sub>2
      assume "(lhs\<^sub>1, rhs\<^sub>1) |\<in>| compile" "(lhs\<^sub>2, rhs\<^sub>2) |\<in>| compile"
      then obtain rhs\<^sub>1' rhs\<^sub>2' where "(lhs\<^sub>1, rhs\<^sub>1') |\<in>| rs" "(lhs\<^sub>2, rhs\<^sub>2') |\<in>| rs"
        unfolding compile_def by force
      thus "arity_compatible lhs\<^sub>1 lhs\<^sub>2"
        using arity by (blast dest: fpairwiseD)
    qed
next
  have "is_fmap rs"
    using fmap by simp
  thus "is_fmap compile"
    unfolding compile_def translate_rule_alt_def
    by (rule is_fmap_image)
next
  have "pattern_compatibles rs"
    using patterns by simp
  thus "pattern_compatibles compile"
    unfolding compile_def translate_rule_alt_def
    by (auto dest: fpairwiseD)
next
  show "fdisjnt (heads_of compile) C"
    using disjnt by (simp add: compile_heads)
next
  have "fBall compile not_shadowing"
    proof safe
      fix lhs rhs
      assume "(lhs, rhs) |\<in>| compile"
      then obtain rhs'
        where "rhs = fresh_frun (term_to_nterm [] rhs') (frees lhs |\<union>| all_consts)"
          and "(lhs, rhs') |\<in>| rs"
        unfolding compile_def translate_rule_alt_def by auto
      hence "rule (lhs, rhs')" "\<not> shadows_consts lhs"
        using all_rules not_shadows by blast+
      moreover hence "wellformed rhs'" "frees rhs' |\<subseteq>| frees lhs" "fdisjnt all_consts (frees lhs)"
        unfolding shadows_consts_def by simp+

      moreover have "\<not> shadows_consts rhs"
        apply (subst shadows_consts_def)
        apply simp
        unfolding \<open>rhs = _\<close>
        apply (rule fdisjnt_swap)
        apply (rule term_to_nterm_all_vars)
         apply fact
        apply (rule fdisjnt_subset_left)
         apply fact
        apply (rule fdisjnt_swap)
        apply fact
        done

      ultimately show "not_shadowing (lhs, rhs)"
        unfolding compile_heads by simp
    qed
  thus "fBall compile (constants.not_shadowing C_info (heads_of compile))"
    unfolding compile_heads .

  have "fBall compile (\<lambda>(_, rhs). welldefined rhs)"
    unfolding compile_heads
    unfolding compile_def ball_simps
    apply (rule fBall_pred_weaken[OF _ welldefined_rs])
    subgoal for x
      apply (cases x)
      apply simp
      apply (subst fresh_frun_def)
      apply (subst term_to_nterm_consts[THEN pred_state_run_state])
      by auto
    done
  thus "fBall compile (\<lambda>(_, rhs). consts rhs |\<subseteq>| pre_constants.all_consts C_info (heads_of compile))"
    unfolding compile_heads .
next
  show "compile \<noteq> {||}"
    using nonempty unfolding compile_def by auto
next
  show "distinct all_constructors"
    by (fact distinct_ctr)
qed

sublocale rules_as_nrules: nrules C_info compile
by (fact compile_rules)

end

subsection \<open>Correctness of translation\<close>

theorem (in rules) compile_correct:
  assumes "compile \<turnstile>\<^sub>n u \<longrightarrow> u'" "closed u"
  shows "rs \<turnstile> nterm_to_term' u \<longrightarrow> nterm_to_term' u'"
using assms proof (induction u u')
  case (step r u u')
  moreover obtain pat rhs' where "r = (pat, rhs')"
    by force
  ultimately obtain nenv where "match pat u = Some nenv" "u' = subst rhs' nenv"
    by auto
  then obtain env where "nrelated.P_env [] env nenv" "match pat (nterm_to_term [] u) = Some env"
    by (metis nrelated.match_rel option.exhaust option.rel_distinct(1) option.rel_inject(2))

  have "closed_env nenv"
    using step \<open>match pat u = Some nenv\<close> by (intro closed.match)

  from step obtain rhs
    where "rhs' = fresh_frun (term_to_nterm [] rhs) (frees pat |\<union>| all_consts)" "(pat, rhs) |\<in>| rs"
    unfolding \<open>r = _\<close> compile_def by auto
  with assms have "rule (pat, rhs)"
    using all_rules by blast
  hence "rhs = nterm_to_term [] rhs'"
    unfolding \<open>rhs' = _\<close>
    by (simp add: term_to_nterm_nterm_to_term fresh_frun_def)

  have "compile \<turnstile>\<^sub>n u \<longrightarrow> u'"
    using step by (auto intro: nrewrite.step)
  hence "closed u'"
    by (rule rules_as_nrules.nrewrite_closed) fact

  show ?case
    proof (rule rewrite.step)
      show "(pat, rhs) \<turnstile> nterm_to_term [] u \<rightarrow> nterm_to_term [] u'"
        apply (subst nterm_to_term_eq_closed)
         apply fact
        apply simp
        apply (rule exI[where x = env])
        apply (rule conjI)
         apply fact
        unfolding \<open>rhs = _\<close>
        apply (subst nrelated_subst)
           apply fact
          apply fact
        unfolding fdisjnt_alt_def apply simp
        unfolding \<open>u' = subst rhs' nenv\<close> by simp
    qed fact
next
  case beta
  show ?case
    apply simp
    apply (subst subst_single_eq[symmetric, simplified])
    apply (subst nterm_to_term_subst_replace_bound[where n = 0])
    subgoal using beta by (simp add: closed_except_def)
    subgoal by simp
    subgoal by simp
    subgoal by simp (rule rewrite.beta)
    done
qed (auto intro: rewrite.intros simp: closed_except_def)

subsection \<open>Completeness of translation\<close>

context rules begin

context
  notes [simp] = closed_except_def fdisjnt_alt_def
begin

private lemma compile_complete0:
  assumes "rs \<turnstile> t \<longrightarrow> t'" "closed t" "wellformed t"
  obtains u' where "compile \<turnstile>\<^sub>n fst (run_state (term_to_nterm [] t) s) \<longrightarrow> u'" "u' \<approx>\<^sub>\<alpha> fst (run_state (term_to_nterm [] t') s')"
apply atomize_elim
using assms proof (induction t t' arbitrary: s s')
  case (step r t t')
  let ?t\<^sub>n = "fst (run_state (term_to_nterm [] t) s)"
  let ?t\<^sub>n' = "fst (run_state (term_to_nterm [] t') s')"
  from step have "closed t" "closed ?t\<^sub>n"
    using term_to_nterm_vars0[where \<Gamma> = "[]"]
    by force+
  from step have "nterm_to_term' ?t\<^sub>n = t"
    find_theorems nterm_to_term fdisjnt
    by (auto intro!: term_to_nterm_nterm_to_term0)

  obtain pat rhs' where "r = (pat, rhs')"
    by fastforce
  with step obtain env' where "match pat t = Some env'" "t' = subst rhs' env'"
    by fastforce
  with \<open>_ = t\<close> have "rel_option (nrelated.P_env []) (match pat t) (match pat (?t\<^sub>n))"
    by (metis nrelated.match_rel)
  with step \<open>_ = Some env'\<close>
    obtain env where "nrelated.P_env [] env' env" "match pat ?t\<^sub>n = Some env"
    by (metis (no_types, lifting) option_rel_Some1)
  with \<open>closed ?t\<^sub>n\<close> have "closed_env env"
    by (blast intro: closed.match)

  from step obtain rhs
    where "rhs = fresh_frun (term_to_nterm [] rhs') (frees pat |\<union>| all_consts)" "(pat, rhs) |\<in>| compile"
    unfolding \<open>r = _\<close> compile_def
    by force
  with step have "rule (pat, rhs')"
    unfolding \<open>r = _\<close>
    using all_rules by fast
  hence "nterm_to_term' rhs = rhs'"
    unfolding \<open>rhs = _\<close>
    by (simp add: fresh_frun_def term_to_nterm_nterm_to_term)
  obtain u' where "subst rhs env = u'"
    by simp
  have "t' = nterm_to_term' u'"
    unfolding \<open>t' = _\<close>
    unfolding \<open>_ = rhs'\<close>[symmetric]
    apply (subst nrelated_subst)
       apply fact+
    using \<open>_ = u'\<close>
    by simp+

  have "compile \<turnstile>\<^sub>n ?t\<^sub>n \<longrightarrow> u'"
    apply (rule nrewrite.step)
     apply fact
    apply simp
    apply (intro conjI exI)
     apply fact+
    done
  with \<open>closed ?t\<^sub>n\<close> have "closed u'"
    by (blast intro:rules_as_nrules.nrewrite_closed)
  with \<open>t' = nterm_to_term' _\<close> have "u' \<approx>\<^sub>\<alpha> ?t\<^sub>n'"
    by (force intro: nterm_to_term_term_to_nterm[where \<Gamma> = "[]" and \<Gamma>' = "[]",simplified])

  show ?case
    apply (intro conjI exI)
     apply (rule nrewrite.step)
      apply fact
     apply simp
     apply (intro conjI exI)
      apply fact+
    done
next
  case (beta t t')
  let ?name = "next s"
  let ?t\<^sub>n = "fst (run_state (term_to_nterm [?name] t) (?name))"
  let ?t\<^sub>n' = "fst (run_state (term_to_nterm [] t') (snd (run_state (term_to_nterm [?name] t) (?name))))"

  from beta have "closed t" "closed (t [t']\<^sub>\<beta>)"  "closed (\<Lambda> t $ t')" "closed  t'"
    using replace_bound_frees
    by fastforce+
  moreover from beta have "wellformed' (Suc 0) t" "wellformed t'"
    by simp+
  ultimately have "t = nterm_to_term [?name] ?t\<^sub>n"
             and "t' = nterm_to_term' ?t\<^sub>n'"
             and *:"frees ?t\<^sub>n = {|?name|} \<or> frees ?t\<^sub>n = fempty"
             and "closed ?t\<^sub>n'"
    using term_to_nterm_vars0[where \<Gamma> = "[?name]"]
    using term_to_nterm_vars0[where \<Gamma> = "[]"]
    by (force simp: term_to_nterm_nterm_to_term0)+

  hence **:"t [t']\<^sub>\<beta> = nterm_to_term' (subst_single ?t\<^sub>n ?name ?t\<^sub>n')"
    by (auto simp: nterm_to_term_subst_replace_bound[where n = 0])

  from \<open>closed ?t\<^sub>n'\<close> have "closed_env (fmap_of_list [(?name, ?t\<^sub>n')])"
    by auto

  show ?case
    apply (rule exI)
    apply (auto simp: split_beta create_alt_def)
     apply (rule nrewrite.beta)
    apply (subst subst_single_eq[symmetric])
    apply (subst **)
    apply (rule nterm_to_term_term_to_nterm[where \<Gamma> = "[]" and \<Gamma>' = "[]", simplified])
    apply (subst subst_single_eq)
    apply (subst subst_frees[OF \<open>closed_env _\<close>])
    using * by force
next
  case ("fun" t t' u)
  hence "closed  t" "closed u" "closed (t $ u)"
       and wellform:"wellformed t" "wellformed u"
    by fastforce+
  from "fun" obtain u'
    where "compile \<turnstile>\<^sub>n fst (run_state (term_to_nterm [] t) s) \<longrightarrow> u'"
          "u' \<approx>\<^sub>\<alpha> fst (run_state (term_to_nterm [] t') s')"
    by force
  show ?case
    apply (rule exI)
    apply (auto simp: split_beta create_alt_def)
     apply (rule nrewrite.fun)
     apply fact
    apply rule
     apply fact
    apply (subst term_to_nterm_alpha_equiv[of "[]" "[]", simplified])
    using \<open>closed u\<close> \<open>wellformed u\<close> by auto
next
  case (arg u u' t)
  hence "closed  t" "closed u" "closed (t $ u)"
       and wellform:"wellformed t" "wellformed u"
    by fastforce+
  from arg obtain t'
    where "compile \<turnstile>\<^sub>n fst (run_state (term_to_nterm [] u) (snd (run_state (term_to_nterm [] t) s))) \<longrightarrow> t'"
          "t' \<approx>\<^sub>\<alpha>  fst (run_state (term_to_nterm [] u') (snd (run_state (term_to_nterm [] t) s')))"
    by force
  show ?case
    apply (rule exI)
    apply (auto simp: split_beta create_alt_def)
     apply rule
     apply fact
    apply rule
     apply (subst term_to_nterm_alpha_equiv[of "[]" "[]", simplified])
    using \<open>closed t\<close> \<open>wellformed t\<close> apply force+
    by fact
qed

lemma compile_complete:
  assumes "rs \<turnstile> t \<longrightarrow> t'" "closed t" "wellformed t"
  obtains u' where "compile \<turnstile>\<^sub>n term_to_nterm' t \<longrightarrow> u'" "u' \<approx>\<^sub>\<alpha> term_to_nterm' t'"
unfolding term_to_nterm'_def
using assms by (metis compile_complete0)

end

end

subsection \<open>Splitting into constants\<close>

type_synonym crules = "(term list \<times> nterm) fset"
type_synonym crule_set = "(name \<times> crules) fset"

abbreviation arity_compatibles :: "(term list \<times> 'a) fset \<Rightarrow> bool" where
"arity_compatibles \<equiv> fpairwise (\<lambda>(pats\<^sub>1, _) (pats\<^sub>2, _). length pats\<^sub>1 = length pats\<^sub>2)"

lemma arity_compatible_length:
  assumes "arity_compatibles rs" "(pats, rhs) |\<in>| rs"
  shows "length pats = arity rs"
proof -
  have "fBall rs (\<lambda>(pats\<^sub>1, _). fBall rs (\<lambda>(pats\<^sub>2, _). length pats\<^sub>1 = length pats\<^sub>2))"
    using assms unfolding fpairwise_alt_def by blast
  hence "fBall rs (\<lambda>x. fBall rs (\<lambda>y. (length \<circ> fst) x = (length \<circ> fst) y))"
    by force
  hence "(length \<circ> fst) (pats, rhs) = arity rs"
    using assms(2) unfolding arity_def fthe_elem'_eq by (rule singleton_fset_holds)
  thus ?thesis
    by simp
qed

locale pre_crules = constants C_info "fst |`| rs" for C_info and rs :: "crule_set"

locale crules = pre_crules +
  assumes fmap: "is_fmap rs"
  assumes nonempty: "rs \<noteq> {||}"
  assumes inner:
    "fBall rs (\<lambda>(_, crs).
      arity_compatibles crs \<and>
      is_fmap crs \<and>
      patterns_compatibles crs \<and>
      crs \<noteq> {||} \<and>
      fBall crs (\<lambda>(pats, rhs).
        linears pats \<and>
        pats \<noteq> [] \<and>
        fdisjnt (freess pats) all_consts \<and>
        \<not> shadows_consts rhs \<and>
        frees rhs |\<subseteq>| freess pats \<and>
        welldefined rhs))"

lemma (in pre_crules) crulesI:
  assumes "\<And>name crs. (name, crs) |\<in>| rs \<Longrightarrow> arity_compatibles crs"
  assumes "\<And>name crs. (name, crs) |\<in>| rs \<Longrightarrow> is_fmap crs"
  assumes "\<And>name crs. (name, crs) |\<in>| rs \<Longrightarrow> patterns_compatibles crs"
  assumes "\<And>name crs. (name, crs) |\<in>| rs \<Longrightarrow> crs \<noteq> {||}"
  assumes "\<And>name crs pats rhs. (name, crs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| crs \<Longrightarrow> linears pats"
  assumes "\<And>name crs pats rhs. (name, crs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| crs \<Longrightarrow> pats \<noteq> []"
  assumes "\<And>name crs pats rhs. (name, crs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| crs \<Longrightarrow> fdisjnt (freess pats) all_consts"
  assumes "\<And>name crs pats rhs. (name, crs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| crs \<Longrightarrow> \<not> shadows_consts rhs"
  assumes "\<And>name crs pats rhs. (name, crs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| crs \<Longrightarrow> frees rhs |\<subseteq>| freess pats"
  assumes "\<And>name crs pats rhs. (name, crs) |\<in>| rs \<Longrightarrow> (pats, rhs) |\<in>| crs \<Longrightarrow> welldefined rhs"
  assumes "is_fmap rs" "rs \<noteq> {||}"
  shows "crules C_info rs"
using assms unfolding crules_axioms_def crules_def
by (auto simp: prod_fBallI intro: pre_crules_axioms)

lemmas crulesI[intro!] = pre_crules.crulesI[unfolded pre_crules_def]

definition "consts_of" :: "nrule fset \<Rightarrow> crule_set" where
"consts_of = fgroup_by split_rule"

lemma consts_of_heads: "fst |`| consts_of rs = heads_of rs"
unfolding consts_of_def
by (simp add: split_rule_fst comp_def)

lemma (in nrules) consts_rules: "crules C_info (consts_of rs)"
proof
  have "is_fmap rs"
    using fmap by simp
  thus "is_fmap (consts_of rs)"
    unfolding consts_of_def by auto

  show "consts_of rs \<noteq> {||}"
    using nonempty unfolding consts_of_def
    by (meson fgroup_by_nonempty)

  show "constants C_info (fst |`| consts_of rs)"
    proof
      show "fdisjnt (fst |`| consts_of rs) C"
        using disjnt by (auto simp: consts_of_heads)
    next
      show "distinct all_constructors"
        by (fact distinct_ctr)
    qed

  fix name crs
  assume crs: "(name, crs) |\<in>| consts_of rs"

  thus "crs \<noteq> {||}"
    unfolding consts_of_def
    by (meson femptyE fgroup_by_nonempty_inner)

  show "arity_compatibles crs" "patterns_compatibles crs"
    proof safe
      fix pats\<^sub>1 rhs\<^sub>1 pats\<^sub>2 rhs\<^sub>2
      assume "(pats\<^sub>1, rhs\<^sub>1) |\<in>| crs" "(pats\<^sub>2, rhs\<^sub>2) |\<in>| crs"
      with crs obtain lhs\<^sub>1 lhs\<^sub>2
        where rs: "(lhs\<^sub>1, rhs\<^sub>1) |\<in>| rs" "(lhs\<^sub>2, rhs\<^sub>2) |\<in>| rs" and
              split: "split_rule (lhs\<^sub>1, rhs\<^sub>1) = (name, (pats\<^sub>1, rhs\<^sub>1))"
                     "split_rule (lhs\<^sub>2, rhs\<^sub>2) = (name, (pats\<^sub>2, rhs\<^sub>2))"
        unfolding consts_of_def by (force simp: split_beta)

      hence arity: "arity_compatible lhs\<^sub>1 lhs\<^sub>2"
        using arity by (force dest: fpairwiseD)

      from rs have const: "is_const (fst (strip_comb lhs\<^sub>1))" "is_const (fst (strip_comb lhs\<^sub>2))"
        using all_rules by force+

      have "name = const_name (fst (strip_comb lhs\<^sub>1))" "name = const_name (fst (strip_comb lhs\<^sub>2))"
        using split by (auto simp: split_beta)
      with const have "fst (strip_comb lhs\<^sub>1) = Const name" "fst (strip_comb lhs\<^sub>2) = Const name"
         apply (fold const_term_def)
        subgoal by simp
        subgoal by fastforce
        done
      hence fst: "fst (strip_comb lhs\<^sub>1) = fst (strip_comb lhs\<^sub>2)"
        by simp

      with arity have "length (snd (strip_comb lhs\<^sub>1)) = length (snd (strip_comb lhs\<^sub>2))"
        unfolding arity_compatible_def
        by (simp add: split_beta)

      with split show "length pats\<^sub>1 = length pats\<^sub>2"
        by (auto simp: split_beta)

      have "pattern_compatible lhs\<^sub>1 lhs\<^sub>2"
        using rs patterns by (auto dest: fpairwiseD)
      moreover have "lhs\<^sub>1 = name $$ pats\<^sub>1"
        using split(1) const(1) by (auto simp: split_beta)
      moreover have "lhs\<^sub>2 = name $$ pats\<^sub>2"
        using split(2) const(2) by (auto simp: split_beta)
      ultimately have "pattern_compatible (name $$ pats\<^sub>1) (name $$ pats\<^sub>2)"
        by simp
      thus "patterns_compatible pats\<^sub>1 pats\<^sub>2"
        using \<open>length pats\<^sub>1 = _\<close> by (auto dest: pattern_compatible_combD)
    qed

  show "is_fmap crs"
    proof
      fix pats rhs\<^sub>1 rhs\<^sub>2
      assume "(pats, rhs\<^sub>1) |\<in>| crs" "(pats, rhs\<^sub>2) |\<in>| crs"
      with crs obtain lhs\<^sub>1 lhs\<^sub>2
        where rs: "(lhs\<^sub>1, rhs\<^sub>1) |\<in>| rs" "(lhs\<^sub>2, rhs\<^sub>2) |\<in>| rs" and
              split: "split_rule (lhs\<^sub>1, rhs\<^sub>1) = (name, (pats, rhs\<^sub>1))"
                     "split_rule (lhs\<^sub>2, rhs\<^sub>2) = (name, (pats, rhs\<^sub>2))"
        unfolding consts_of_def by (force simp: split_beta)

      have "lhs\<^sub>1 = lhs\<^sub>2"
        proof (rule ccontr)
          assume "lhs\<^sub>1 \<noteq> lhs\<^sub>2"
          then consider (fst) "fst (strip_comb lhs\<^sub>1) \<noteq> fst (strip_comb lhs\<^sub>2)"
                      | (snd) "snd (strip_comb lhs\<^sub>1) \<noteq> snd (strip_comb lhs\<^sub>2)"
            by (metis list_strip_comb)
          thus False
            proof cases
              case fst
              moreover have "is_const (fst (strip_comb lhs\<^sub>1))" "is_const (fst (strip_comb lhs\<^sub>2))"
                using rs all_rules by force+
              ultimately show ?thesis
                using split const_name_simps by (fastforce simp: split_beta)
            next
              case snd
              with split show ?thesis
                by (auto simp: split_beta)
            qed
        qed

      with rs show "rhs\<^sub>1 = rhs\<^sub>2"
        using \<open>is_fmap rs\<close> by (auto dest: is_fmapD)
    qed

  fix pats rhs
  assume "(pats, rhs) |\<in>| crs"
  then obtain lhs where "(lhs, rhs) |\<in>| rs" "pats = snd (strip_comb lhs)"
    using crs unfolding consts_of_def by (force simp: split_beta)
  hence "nrule (lhs, rhs)"
    using all_rules by blast
  hence "linear lhs" "frees rhs |\<subseteq>| frees lhs"
    by auto
  thus "linears pats"
    unfolding \<open>pats = _\<close> by (intro linears_strip_comb)

  have "\<not> is_const lhs" "is_const (fst (strip_comb lhs))"
    using \<open>nrule _\<close> by auto
  thus "pats \<noteq> []"
    unfolding \<open>pats = _\<close> using \<open>linear lhs\<close>
    apply (cases lhs)
        apply (fold app_term_def)
    by (auto split: prod.splits)

  from \<open>nrule (lhs, rhs)\<close> have "frees (fst (strip_comb lhs)) = {||}"
    by (cases "fst (strip_comb lhs)") (auto simp: is_const_def)
  hence "frees lhs = freess (snd (strip_comb lhs))"
    by (subst frees_strip_comb) auto
  thus "frees rhs |\<subseteq>| freess pats"
    unfolding \<open>pats = _\<close> using \<open>frees rhs |\<subseteq>| frees lhs\<close> by simp

  have "\<not> shadows_consts rhs"
    using \<open>(lhs, rhs) |\<in>| rs\<close> not_shadows
    by force
  thus "\<not> pre_constants.shadows_consts C_info (fst |`| consts_of rs) rhs"
    by (simp add: consts_of_heads)

  have "fdisjnt all_consts (frees lhs)"
    using \<open>(lhs, rhs) |\<in>| rs\<close> not_shadows
    by (force simp: shadows_consts_def)
  moreover have "freess pats |\<subseteq>| frees lhs"
    unfolding \<open>pats = _\<close> \<open>frees lhs = _\<close>
    by simp
  ultimately have "fdisjnt (freess pats) all_consts"
    by (metis fdisjnt_subset_right fdisjnt_swap)

  thus "fdisjnt (freess pats) (pre_constants.all_consts C_info (fst |`| consts_of rs))"
    by (simp add: consts_of_heads)

  show "pre_constants.welldefined C_info (fst |`| consts_of rs) rhs"
    using welldefined_rs \<open>(lhs, rhs) |\<in>| rs\<close>
    by (force simp: consts_of_heads)
qed

sublocale nrules \<subseteq> nrules_as_crules?: crules C_info "consts_of rs"
by (fact consts_rules)

subsection \<open>Computability\<close>

export_code
  translate_rule consts_of arity nterm_to_term
  checking Scala

end