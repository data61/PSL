section \<open>Big-step semantics\<close>

theory Big_Step_Sterm
imports
  Rewriting_Sterm
  "../Terms/Term_as_Value"
begin

subsection \<open>Big-step semantics evaluating to irreducible @{typ sterm}s\<close>

inductive (in constructors) seval :: "srule list \<Rightarrow> (name, sterm) fmap \<Rightarrow> sterm \<Rightarrow> sterm \<Rightarrow> bool"  ("_, _/ \<turnstile>\<^sub>s/ _ \<down>/ _" [50,0,50] 50) for rs where
const: "(name, rhs) \<in> set rs \<Longrightarrow> rs, \<Gamma> \<turnstile>\<^sub>s Sconst name \<down> rhs" |
var: "fmlookup \<Gamma> name = Some val \<Longrightarrow> rs, \<Gamma> \<turnstile>\<^sub>s Svar name \<down> val" |
abs: "rs, \<Gamma> \<turnstile>\<^sub>s Sabs cs \<down> Sabs (map (\<lambda>(pat, t). (pat, subst t (fmdrop_fset (frees pat) \<Gamma>))) cs)" |
comb: "
  rs, \<Gamma> \<turnstile>\<^sub>s t \<down> Sabs cs \<Longrightarrow> rs, \<Gamma> \<turnstile>\<^sub>s u \<down> u' \<Longrightarrow>
  find_match cs u' = Some (env, _, rhs) \<Longrightarrow>
  rs, \<Gamma> ++\<^sub>f env \<turnstile>\<^sub>s rhs \<down> val \<Longrightarrow>
  rs, \<Gamma> \<turnstile>\<^sub>s t $\<^sub>s u \<down> val" |
constr: "
  name |\<in>| C \<Longrightarrow>
  list_all2 (seval rs \<Gamma>) ts us \<Longrightarrow>
  rs, \<Gamma> \<turnstile>\<^sub>s name $$ ts \<down> name $$ us"

lemma (in constructors) seval_closed:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>s t \<down> u" "closed_srules rs" "closed_env \<Gamma>" "closed_except t (fmdom \<Gamma>)"
  shows "closed u"
using assms proof induction
  case (const name rhs \<Gamma>)
  thus ?case
    by (auto simp: list_all_iff)
next
  case (comb \<Gamma> t cs u u' env pat rhs val)
  hence "closed (Sabs cs)" "closed u'"
    by (auto simp: closed_except_def)
  moreover have "(pat, rhs) \<in> set cs" "match pat u' = Some env"
    using comb by (auto simp: find_match_elem)
  ultimately have "closed_except rhs (frees pat)"
    by (auto dest: closed_except_sabs)

  show ?case
    proof (rule comb)
      have "closed_env env"
        by (rule closed.match) fact+
      thus "closed_env (\<Gamma> ++\<^sub>f env)"
        using \<open>closed_env \<Gamma>\<close> by auto
    next
      have "closed_except rhs (fmdom \<Gamma> |\<union>| frees pat)"
        using \<open>closed_except rhs _\<close>
        unfolding closed_except_def by auto
      hence "closed_except rhs (fmdom \<Gamma> |\<union>| fmdom env)"
        using \<open>match pat u' = Some env\<close> by (metis match_dom)
      thus "closed_except rhs (fmdom (\<Gamma> ++\<^sub>f env))"
        using comb by simp
    qed fact
next
  case (abs \<Gamma> cs)
  show ?case
    apply (subst subst_sterm.simps[symmetric])
    apply (subst closed_except_def)
    apply (subst subst_frees)
    apply fact+
    apply (subst fminus_fsubset_conv)
    apply (subst closed_except_def[symmetric])
    apply (subst funion_fempty_right)
    apply fact
    done
next
  case (constr name \<Gamma> ts us)
  have "list_all closed us"
    using \<open>list_all2 _ _ _\<close> \<open>closed_except (list_comb _ _) _\<close>
    proof (induction ts us rule: list.rel_induct)
      case (Cons v vs u us)
      thus ?case
        using constr unfolding closed.list_comb
        by auto
    qed simp
  thus ?case
    unfolding closed.list_comb
    by (simp add: closed_except_def)
qed auto

lemma (in srules) seval_wellformed:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>s t \<down> u" "wellformed t" "wellformed_env \<Gamma>"
  shows "wellformed u"
using assms proof induction
  case (const name rhs \<Gamma>)
  thus ?case
    using all_rules
    by (auto simp: list_all_iff)
next
  case (comb \<Gamma> t cs u u' env pat rhs val)
  hence "(pat, rhs) \<in> set cs" "match pat u' = Some env"
    by (auto simp: find_match_elem)

  show ?case
    proof (rule comb)
      show "wellformed rhs"
        using \<open>(pat, rhs) \<in> set cs\<close> comb
        by (auto simp: list_all_iff)
    next
      have "wellformed_env env"
        apply (rule wellformed.match)
         apply fact
        apply (rule comb)
        using comb apply simp
        apply fact+
        done
      thus "wellformed_env (\<Gamma> ++\<^sub>f env)"
        using comb by auto
    qed
next
  case (abs \<Gamma> cs)
  thus ?case
    by (metis subst_sterm.simps subst_wellformed)
next
  case (constr name \<Gamma> ts us)
  have "list_all wellformed us"
    using \<open>list_all2 _ _ _\<close> \<open>wellformed (list_comb _ _)\<close>
    proof (induction ts us rule: list.rel_induct)
      case (Cons v vs u us)
      thus ?case
        using constr by (auto simp: wellformed.list_comb app_sterm_def)
    qed simp
  thus ?case
    by (simp add: wellformed.list_comb const_sterm_def)
qed auto

lemma (in constants) seval_shadows:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>s t \<down> u" "\<not> shadows_consts t"
  assumes "list_all (\<lambda>(_, rhs). \<not> shadows_consts rhs) rs"
  assumes "not_shadows_consts_env \<Gamma>"
  shows "\<not> shadows_consts u"
using assms proof induction
  case (const name rhs \<Gamma>)
  thus ?case
    unfolding srules_def
    by (auto simp: list_all_iff)
next
  case (comb \<Gamma> t cs u u' env pat rhs val)
  hence "\<not> shadows_consts (Sabs cs)" "\<not> shadows_consts u'"
    by auto
  moreover from comb have "(pat, rhs) \<in> set cs" "match pat u' = Some env"
    by (auto simp: find_match_elem)
  ultimately have "\<not> shadows_consts rhs"
    by (auto simp: list_ex_iff)

  moreover have "not_shadows_consts_env env"
    using comb \<open>match pat u' = _\<close> by (auto intro: shadows.match)

  ultimately show ?case
    using comb by blast
next
  case (abs \<Gamma> cs)
  show ?case
    apply (subst subst_sterm.simps[symmetric])
    apply (rule subst_shadows)
     apply fact+
    done
next
  case (constr name \<Gamma> ts us)
  have "list_all (Not \<circ> shadows_consts) us"
    using \<open>list_all2 _ _ _\<close> \<open>\<not> shadows_consts (name $$ ts)\<close>
    proof (induction ts us rule: list.rel_induct)
      case (Cons v vs u us)
      thus ?case
        using constr by (auto simp: shadows.list_comb const_sterm_def app_sterm_def)
    qed simp
  thus ?case
    by (auto simp: shadows.list_comb list_ex_iff list_all_iff const_sterm_def)
qed auto

lemma (in constructors) seval_list_comb_abs:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>s name $$ args \<down> Sabs cs"
  shows "name \<in> dom (map_of rs)"
using assms
proof (induction \<Gamma> "name $$ args" "Sabs cs" arbitrary: args cs)
  case (constr name' _ _ us)
  hence "Sabs cs = name' $$ us" by simp
  hence False
    by (cases rule: list_comb_cases) (auto simp: const_sterm_def app_sterm_def)
  thus ?case ..
next
  case (comb \<Gamma> t cs' u u' env pat rhs)

  hence "strip_comb (t $\<^sub>s u) = strip_comb (name $$ args)"
    by simp
  hence "strip_comb t = (Sconst name, butlast args)" "u = last args"
     apply -
    subgoal
      apply (simp add: strip_list_comb_const)
      apply (fold app_sterm_def const_sterm_def)
      by (auto split: prod.splits)
    subgoal
      apply (simp add: strip_list_comb_const)
      apply (fold app_sterm_def const_sterm_def)
      by (auto split: prod.splits)
    done
  hence "t = name $$ butlast args"
    apply (fold const_sterm_def)
    by (metis list_strip_comb fst_conv snd_conv)

  thus ?case
    using comb by auto
qed (auto elim: list_comb_cases simp: const_sterm_def app_sterm_def intro: weak_map_of_SomeI)

lemma (in constructors) is_value_eval_id:
  assumes "is_value t" "closed t"
  shows "rs, \<Gamma> \<turnstile>\<^sub>s t \<down> t"
using assms proof induction
  case (abs cs)

  have "rs, \<Gamma> \<turnstile>\<^sub>s Sabs cs \<down> Sabs (map (\<lambda>(pat, t). (pat, subst t (fmdrop_fset (frees pat) \<Gamma>))) cs)"
    by (rule seval.abs)
  moreover have "subst (Sabs cs) \<Gamma> = Sabs cs"
    using abs by (metis subst_closed_id)
  ultimately show ?case
    by simp
next
  case (constr vs name)
  have "list_all2 (seval rs \<Gamma>) vs vs"
    proof (rule list.rel_refl_strong)
      fix v
      assume "v \<in> set vs"
      moreover hence "closed v"
        using constr
        unfolding closed.list_comb
        by (auto simp: list_all_iff)
      ultimately show "rs, \<Gamma> \<turnstile>\<^sub>s v \<down> v"
        using \<open>list_all _ _\<close>
        by (force simp: list_all_iff)
    qed
    with \<open>name |\<in>| C\<close> show ?case
      by (rule seval.constr)
qed

lemma (in constructors) ssubst_eval:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>s t \<down> t'" "\<Gamma>' \<subseteq>\<^sub>f \<Gamma>" "closed_env \<Gamma>" "value_env \<Gamma>"
  shows "rs, \<Gamma> \<turnstile>\<^sub>s subst t \<Gamma>' \<down> t'"
using assms proof induction
  case (var \<Gamma> name val)
  show ?case
    proof (cases "fmlookup \<Gamma>' name")
      case None
      thus ?thesis
        using var by (auto intro: seval.intros)
    next
      case (Some val')
      with var have "val' = val"
        unfolding fmsubset_alt_def by force
      show ?thesis
        apply simp
        apply (subst Some)
        apply (subst \<open>val' = _\<close>)
        apply simp
        apply (rule is_value_eval_id)
        using var by auto
    qed
next
  case (abs \<Gamma> cs)
  hence "subst (subst (Sabs cs) \<Gamma>') \<Gamma> = subst (Sabs cs) \<Gamma>"
    by (metis subst_twice fmsubset_pred)
  moreover have "rs, \<Gamma> \<turnstile>\<^sub>s subst (Sabs cs) \<Gamma>' \<down> subst (subst (Sabs cs) \<Gamma>') \<Gamma>"
    apply simp
    apply (subst map_map[symmetric])
    apply (rule seval.abs)
    done
  ultimately have "rs, \<Gamma> \<turnstile>\<^sub>s subst (Sabs cs) \<Gamma>' \<down> subst (Sabs cs) \<Gamma>"
    by metis
  thus ?case by simp
next
  case (constr name \<Gamma> ts us)
  hence "list_all2 (\<lambda>t. seval rs \<Gamma> (subst t \<Gamma>')) ts us"
    by (blast intro: list.rel_mono_strong)
  with constr show ?case
    by (auto simp: subst_list_comb list_all2_map1 intro: seval.constr)
qed (auto intro: seval.intros)

lemma (in constructors) seval_agree_eq:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>s t \<down> u" "fmrestrict_fset S \<Gamma> = fmrestrict_fset S \<Gamma>'" "closed_except t S"
  assumes "S |\<subseteq>| fmdom \<Gamma>" "closed_srules rs" "closed_env \<Gamma>"
  shows "rs, \<Gamma>' \<turnstile>\<^sub>s t \<down> u"
using assms proof (induction arbitrary: \<Gamma>' S)
  case (var \<Gamma> name val)
  hence "name |\<in>| S"
    by (simp add: closed_except_def)
  hence "fmlookup \<Gamma> name = fmlookup \<Gamma>' name"
    using \<open>fmrestrict_fset S \<Gamma> = _\<close>
    unfolding fmfilter_alt_defs
    including fmap.lifting
    by transfer' (auto simp: map_filter_def fun_eq_iff split: if_splits)
  with var show ?case
    by (auto intro: seval.var)
next
  case (abs \<Gamma> cs)

  \<comment> \<open>Intentionally local: not really a useful lemma outside of its scope\<close>
  have *: "fmdrop_fset S (fmrestrict_fset T m) = fmrestrict_fset (T |\<union>| S) (fmdrop_fset S m)" for S T m
    unfolding fmfilter_alt_defs fmfilter_comp
    by (rule fmfilter_cong) auto

  {
    fix pat t
    assume "(pat, t) \<in> set cs"
    with abs have "closed_except t (S |\<union>| frees pat)"
      by (auto simp: Sterm.closed_except_simps list_all_iff)

    have
      "subst t (fmdrop_fset (frees pat) (fmrestrict_fset S \<Gamma>)) = subst t (fmdrop_fset (frees pat) \<Gamma>)"
      apply (subst *)
      apply (rule subst_restrict_closed)
      apply fact
      done

    moreover have
      "subst t (fmdrop_fset (frees pat) (fmrestrict_fset S \<Gamma>')) = subst t (fmdrop_fset (frees pat) \<Gamma>')"
      apply (subst *)
      apply (rule subst_restrict_closed)
      apply fact
      done

    ultimately have "subst t (fmdrop_fset (frees pat) \<Gamma>) = subst t (fmdrop_fset (frees pat) \<Gamma>')"
      using abs by metis
  }

  hence "map (\<lambda>(pat, t). (pat, subst t (fmdrop_fset (frees pat) \<Gamma>))) cs =
         map (\<lambda>(pat, t). (pat, subst t (fmdrop_fset (frees pat) \<Gamma>'))) cs"
    by auto

  thus ?case
    by (metis seval.abs)
next
  case (comb \<Gamma> t cs u u' env pat rhs val)
  have "fmdom env = frees pat"
    apply (rule match_dom)
    apply (rule find_match_elem)
    apply fact
    done

  show ?case
    proof (rule seval.comb)
      show "rs, \<Gamma>' \<turnstile>\<^sub>s t \<down> Sabs cs" "rs, \<Gamma>' \<turnstile>\<^sub>s u \<down> u'"
        using comb by (auto simp: Sterm.closed_except_simps)
    next
      show "rs, \<Gamma>' ++\<^sub>f env \<turnstile>\<^sub>s rhs \<down> val"
        proof (rule comb)
          have "fmrestrict_fset (S |\<union>| fmdom env) (\<Gamma> ++\<^sub>f env) = fmrestrict_fset (S |\<union>| fmdom env) (\<Gamma>' ++\<^sub>f env)"
            using comb(8)
            unfolding fmfilter_alt_defs
            including fmap.lifting fset.lifting
            by transfer' (auto simp: map_filter_def fun_eq_iff map_add_def split: option.splits if_splits)

          thus "fmrestrict_fset (S |\<union>| frees pat) (\<Gamma> ++\<^sub>f env) = fmrestrict_fset (S |\<union>| frees pat) (\<Gamma>' ++\<^sub>f env)"
            unfolding \<open>fmdom env = _\<close> .
        next
          have "closed_except t S"
            using comb by (simp add: Sterm.closed_except_simps)

          have "closed (Sabs cs)"
            apply (rule seval_closed)
            apply fact+
            using \<open>closed_except t S\<close> \<open>S |\<subseteq>| fmdom \<Gamma>\<close>
            unfolding closed_except_def apply simp
            done

          have "(pat, rhs) \<in> set cs"
            using \<open>find_match _ _ = _\<close> by (rule find_match_elem)
          hence "closed_except rhs (frees pat)"
            using \<open>closed (Sabs cs)\<close> by (auto dest: closed_except_sabs)
          thus "closed_except rhs (S |\<union>| frees pat)"
            unfolding closed_except_def by auto
        next
          show "S |\<union>| frees pat |\<subseteq>| fmdom (\<Gamma> ++\<^sub>f env)"
            apply simp
            apply (intro conjI)
            using comb(10) apply blast
            unfolding \<open>fmdom env = _\<close> by blast
        next
          have "closed_except u S"
            using comb by (auto simp: closed_except_def)

          show "closed_env (\<Gamma> ++\<^sub>f env)"
            apply rule
             apply fact
            apply (rule closed.match[where t = u' and pat = pat])
            subgoal
              by (rule find_match_elem) fact
            subgoal
              apply (rule seval_closed)
                 apply fact+
              using \<open>closed_except u S\<close> \<open>S |\<subseteq>| fmdom \<Gamma>\<close> unfolding closed_except_def by blast
            done
        qed fact
    qed fact
next
  case (constr name \<Gamma> ts us)
  show ?case
    apply (rule seval.constr)
     apply fact
    apply (rule list.rel_mono_strong)
     apply fact
    using constr
    unfolding closed.list_comb list_all_iff
    by auto
qed (auto intro: seval.intros)


subsubsection \<open>Correctness wrt @{const srewrite}\<close>

context srules begin context begin

private lemma seval_correct0:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>s t \<down> u" "closed_except t (fmdom \<Gamma>)" "closed_env \<Gamma>"
  shows "rs \<turnstile>\<^sub>s subst t \<Gamma> \<longrightarrow>* u"
using assms proof induction
  case (const name rhs \<Gamma>)

  have "srewrite_step rs name rhs"
    by (rule srewrite_stepI) fact
  thus ?case
    by (auto intro: srewrite.intros)
next
  case (comb \<Gamma> t cs u u' env pat rhs val)
  hence "closed_except t (fmdom \<Gamma>)" "closed_except u (fmdom \<Gamma>)"
    by (simp add: Sterm.closed_except_simps)+
  moreover have "closed_srules rs"
    using all_rules
    unfolding list_all_iff by fastforce
  ultimately have "closed (Sabs cs)" "closed u'"
    using comb by (metis seval_closed)+

  from comb have "(pat, rhs) \<in> set cs" "match pat u' = Some env"
    by (auto simp: find_match_elem)
  hence "closed_except rhs (frees pat)"
    using \<open>closed (Sabs cs)\<close> by (auto dest: closed_except_sabs)
  hence "frees rhs |\<subseteq>| frees pat"
    by (simp add: closed_except_def)
  moreover have "fmdom env = frees pat"
    using \<open>match pat u' = _\<close> by (auto simp: match_dom)
  ultimately have "frees rhs |\<subseteq>| fmdom env"
    by simp
  hence "subst rhs (\<Gamma> ++\<^sub>f env) = subst rhs env"
    by (rule subst_add_shadowed_env)

  have "rs \<turnstile>\<^sub>s subst t \<Gamma> $\<^sub>s subst u \<Gamma> \<longrightarrow>* Sabs cs $\<^sub>s u'"
    using comb by (force intro: srewrite.rt_comb[unfolded app_sterm_def] simp: Sterm.closed_except_simps)
  also have "rs \<turnstile>\<^sub>s Sabs cs $\<^sub>s u' \<longrightarrow>* subst rhs env"
    using comb \<open>closed u'\<close> by (force intro: srewrite.beta find_match_rewrite_first)
  also have "rs \<turnstile>\<^sub>s subst rhs env \<longrightarrow>* subst rhs (\<Gamma> ++\<^sub>f env)"
    unfolding \<open>subst rhs (\<Gamma> ++\<^sub>f env) = _\<close> by simp
  also have "rs \<turnstile>\<^sub>s subst rhs (\<Gamma> ++\<^sub>f env) \<longrightarrow>* val"
    proof (rule comb)
      show "closed_except rhs (fmdom (\<Gamma> ++\<^sub>f env))"
        using comb \<open>match pat u' = Some env\<close> \<open>fmdom env = _\<close> \<open>frees rhs |\<subseteq>| frees pat\<close>
        by (auto simp: closed_except_def)
    next
      show "closed_env (\<Gamma> ++\<^sub>f env)"
        using comb \<open>match pat u' = Some env\<close> \<open>closed u'\<close>
        by (blast intro: closed.match)
    qed

  finally show ?case by simp
next
  case (constr name \<Gamma> ts us)
  show ?case
    apply (simp add: subst_list_comb)
    apply (rule srewrite.rt_list_comb)
    subgoal
      apply (simp add: list.rel_map)
      apply (rule list.rel_mono_strong[OF constr(2)])
      apply clarify
      apply (elim impE)
      using constr(3) apply (erule closed.list_combE)
       apply (rule constr)+
      apply (auto simp: const_sterm_def)
      done
    subgoal by auto
    done
qed auto

corollary seval_correct:
  assumes "rs, fmempty \<turnstile>\<^sub>s t \<down> u" "closed t"
  shows "rs \<turnstile>\<^sub>s t \<longrightarrow>* u"
proof -
  have "closed_except t (fmdom fmempty)"
    using assms by simp
  with assms have "rs \<turnstile>\<^sub>s subst t fmempty \<longrightarrow>* u"
    by (fastforce intro!: seval_correct0)
  thus ?thesis
    by simp
qed

end end

end