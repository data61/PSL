theory Big_Step_Value
imports
  Big_Step_Sterm
  "../Terms/Value"
begin

subsection \<open>Big-step semantics evaluating to @{typ value}\<close>

primrec vrule :: "vrule \<Rightarrow> bool" where
"vrule (_, rhs) \<longleftrightarrow> vwellformed rhs \<and> vclosed rhs \<and> \<not> is_Vconstr rhs"

locale vrules = constants C_info "fst |`| fset_of_list rs" for C_info and rs :: "vrule list" +
  assumes all_rules: "list_all vrule rs"
  assumes distinct: "distinct (map fst rs)"
  assumes not_shadows: "list_all (\<lambda>(_, rhs). not_shadows_vconsts rhs) rs"
  assumes vconstructor_value_rs: "vconstructor_value_rs rs"
  assumes vwelldefined_rs: "list_all (\<lambda>(_, rhs). vwelldefined rhs) rs"
begin

lemma map: "is_map (set rs)"
using distinct by (rule distinct_is_map)

end

abbreviation value_to_sterm_rules :: "vrule list \<Rightarrow> srule list" where
"value_to_sterm_rules \<equiv> map (map_prod id value_to_sterm)"

inductive (in special_constants)
  veval :: "(name \<times> value) list \<Rightarrow> (name, value) fmap \<Rightarrow> sterm \<Rightarrow> value \<Rightarrow> bool"  ("_, _/ \<turnstile>\<^sub>v/ _ \<down>/ _" [50,0,50] 50) for rs where
const: "(name, rhs) \<in> set rs \<Longrightarrow> rs, \<Gamma> \<turnstile>\<^sub>v Sconst name \<down> rhs" |
var: "fmlookup \<Gamma> name = Some val \<Longrightarrow> rs, \<Gamma> \<turnstile>\<^sub>v Svar name \<down> val" |
abs: "rs, \<Gamma> \<turnstile>\<^sub>v Sabs cs \<down> Vabs cs \<Gamma>" |
comb: "
  rs, \<Gamma> \<turnstile>\<^sub>v t \<down> Vabs cs \<Gamma>' \<Longrightarrow> rs, \<Gamma> \<turnstile>\<^sub>v u \<down> u' \<Longrightarrow>
  vfind_match cs u' = Some (env, _, rhs) \<Longrightarrow>
  rs, \<Gamma>' ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> val \<Longrightarrow>
  rs, \<Gamma> \<turnstile>\<^sub>v t $\<^sub>s u \<down> val" |
rec_comb: "
  rs, \<Gamma> \<turnstile>\<^sub>v t \<down> Vrecabs css name \<Gamma>' \<Longrightarrow>
  fmlookup css name = Some cs \<Longrightarrow>
  rs, \<Gamma> \<turnstile>\<^sub>v u \<down> u' \<Longrightarrow>
  vfind_match cs u' = Some (env, _, rhs) \<Longrightarrow>
  rs, \<Gamma>' ++\<^sub>f env \<turnstile>\<^sub>v rhs \<down> val \<Longrightarrow>
  rs, \<Gamma> \<turnstile>\<^sub>v t $\<^sub>s u \<down> val" |
constr: "
  name |\<in>| C \<Longrightarrow>
  list_all2 (veval rs \<Gamma>) ts us \<Longrightarrow>
  rs, \<Gamma> \<turnstile>\<^sub>v name $$ ts \<down> Vconstr name us"

lemma (in vrules) veval_wellformed:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>v t \<down> v" "wellformed t" "wellformed_venv \<Gamma>"
  shows "vwellformed v"
using assms proof induction
  case const
  thus ?case
    using all_rules
    by (auto simp: list_all_iff)
next
  case comb
  show ?case
    apply (rule comb)
    using comb by (auto simp: list_all_iff dest: vfind_match_elem intro: vwellformed.vmatch_env)
next
  case (rec_comb \<Gamma> t css name \<Gamma>' cs u u' env pat rhs val)
  hence "(pat, rhs) \<in> set cs" "vmatch (mk_pat pat) u' = Some env"
    by (metis vfind_match_elem)+

  show ?case
    proof (rule rec_comb)
      have "wellformed t"
        using rec_comb by simp
      have "vwellformed (Vrecabs css name \<Gamma>')"
        by (rule rec_comb) fact+
      thus "wellformed rhs"
        using rec_comb \<open>(pat, rhs) \<in> set cs\<close>
        by (auto simp: list_all_iff)

      have "wellformed_venv \<Gamma>'"
        using \<open>vwellformed (Vrecabs css name \<Gamma>')\<close> by simp
      moreover have "wellformed_venv env"
        using rec_comb \<open>vmatch (mk_pat pat) u' = Some env\<close>
        by (auto intro: vwellformed.vmatch_env)
      ultimately show "wellformed_venv (\<Gamma>' ++\<^sub>f env)"
        by blast
    qed
next
  case (constr name \<Gamma> ts us)
  have "list_all vwellformed us"
    using \<open>list_all2 _ _ _\<close> \<open>wellformed (list_comb _ _)\<close>
    proof (induction ts us rule: list.rel_induct)
      case (Cons v vs u us)
      with constr show ?case
        unfolding wellformed.list_comb by auto
    qed simp
  thus ?case
    by (simp add: list_all_iff)
qed auto

lemma (in vrules) veval_closed:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>v t \<down> v" "closed_except t (fmdom \<Gamma>)" "closed_venv \<Gamma>"
  assumes "wellformed t" "wellformed_venv \<Gamma>"
  shows "vclosed v"
using assms proof induction
  case (const name rhs \<Gamma>)
  hence "(name, rhs) \<in> set rs"
    by (auto dest: map_of_SomeD)
  thus ?case
    using const all_rules
    by (auto simp: list_all_iff)
next
  case (comb \<Gamma> t cs \<Gamma>' u u' env pat rhs val)
  hence pat: "(pat, rhs) \<in> set cs" "vmatch (mk_pat pat) u' = Some env"
    by (metis vfind_match_elem)+

  show ?case
    proof (rule comb)
      have "vclosed u'"
        using comb by (auto simp: Sterm.closed_except_simps)
      have "closed_venv env"
        by (rule vclosed.vmatch_env) fact+
      thus "closed_venv (\<Gamma>' ++\<^sub>f env)"
        using comb by (auto simp: Sterm.closed_except_simps)
    next
      have "wellformed t"
        using comb by simp
      have "vwellformed (Vabs cs \<Gamma>')"
        by (rule veval_wellformed) fact+
      thus "wellformed rhs"
        using pat by (auto simp: list_all_iff)

      have "wellformed_venv \<Gamma>'"
        using \<open>vwellformed (Vabs cs \<Gamma>')\<close> by simp
      moreover have "wellformed_venv env"
        using comb pat
        by (auto intro: vwellformed.vmatch_env veval_wellformed)
      ultimately show "wellformed_venv (\<Gamma>' ++\<^sub>f env)"
        by blast

      have "vclosed (Vabs cs \<Gamma>')"
        using comb by (auto simp: Sterm.closed_except_simps)
      hence "closed_except rhs (fmdom \<Gamma>' |\<union>| frees pat)"
        using pat by (auto simp: list_all_iff)

      moreover have "fmdom env = frees pat"
        using \<open>vwellformed (Vabs cs \<Gamma>')\<close> pat
        by (auto simp: vmatch_dom mk_pat_frees list_all_iff)

      ultimately show "closed_except rhs (fmdom (\<Gamma>' ++\<^sub>f env))"
        using \<open>vclosed (Vabs cs \<Gamma>')\<close>
        by simp
    qed
next
  case (rec_comb \<Gamma> t css name \<Gamma>' cs u u' env pat rhs val)
  hence pat: "(pat, rhs) \<in> set cs" "vmatch (mk_pat pat) u' = Some env"
    by (metis vfind_match_elem)+

  show ?case
    proof (rule rec_comb)
      have "vclosed u'"
        using rec_comb by (auto simp: Sterm.closed_except_simps)
      have "closed_venv env"
        by (rule vclosed.vmatch_env) fact+
      thus "closed_venv (\<Gamma>' ++\<^sub>f env)"
        using rec_comb by (auto simp: Sterm.closed_except_simps)
    next
      have "wellformed t"
        using rec_comb by simp
      have "vwellformed (Vrecabs css name \<Gamma>')"
        by (rule veval_wellformed) fact+
      thus "wellformed rhs"
        using pat rec_comb by (auto simp: list_all_iff)

      have "wellformed_venv \<Gamma>'"
        using \<open>vwellformed (Vrecabs css name \<Gamma>')\<close> by simp
      moreover have "wellformed_venv env"
        using rec_comb pat
        by (auto intro: vwellformed.vmatch_env veval_wellformed)
      ultimately show "wellformed_venv (\<Gamma>' ++\<^sub>f env)"
        by blast

      have "wellformed_clauses cs"
        using \<open>vwellformed (Vrecabs css name \<Gamma>')\<close> \<open>fmlookup css name = Some cs\<close>
        by auto

      have "vclosed (Vrecabs css name \<Gamma>')"
        using rec_comb by (auto simp: Sterm.closed_except_simps)
      hence "closed_except rhs (fmdom \<Gamma>' |\<union>| frees pat)"
        using rec_comb pat by (auto simp: list_all_iff)
      moreover have "fmdom env = frees pat"
        using \<open>wellformed_clauses cs\<close> pat
        by (auto simp: list_all_iff vmatch_dom mk_pat_frees)
      ultimately show "closed_except rhs (fmdom (\<Gamma>' ++\<^sub>f env))"
        using \<open>vclosed (Vrecabs css name \<Gamma>')\<close>
        by simp
    qed
next
  case (constr name \<Gamma> ts us)
  have "list_all vclosed us"
    using \<open>list_all2 _ _ _\<close> \<open>closed_except (_ $$ _) _\<close> \<open>wellformed (name $$ ts)\<close>
    proof (induction ts us rule: list.rel_induct)
      case (Cons v vs u us)
      with constr show ?case
        unfolding closed.list_comb wellformed.list_comb
        by (auto simp: list_all_iff Sterm.closed_except_simps)
    qed simp
  thus ?case
    by (simp add: list_all_iff)
qed (auto simp: Sterm.closed_except_simps)

lemma (in vrules) veval_constructor_value:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>v t \<down> v" "vconstructor_value_env \<Gamma>"
  shows "vconstructor_value v"
using assms proof induction
  case (comb \<Gamma> t cs \<Gamma>' u u' env pat rhs val)
  hence "(pat, rhs) \<in> set cs" "vmatch (mk_pat pat) u' = Some env"
    by (metis vfind_match_elem)+
  hence "vconstructor_value_env (\<Gamma>' ++\<^sub>f env)"
    using comb by (auto intro: vconstructor_value.vmatch_env)
  thus ?case
    using comb by auto
next
  case (constr name \<Gamma> ts us)
  hence "list_all vconstructor_value us"
    by (auto elim: list_all2_rightE)
  with constr show ?case
    by simp
next
  case const
  thus ?case
    using vconstructor_value_rs
    by (auto simp: list_all_iff vconstructor_value_rs_def)
next
  case (rec_comb \<Gamma> t css name \<Gamma>' cs u u' env pat rhs val)
  hence "(pat, rhs) \<in> set cs" "vmatch (mk_pat pat) u' = Some env"
    by (metis vfind_match_elem)+
  hence "vconstructor_value_env (\<Gamma>' ++\<^sub>f env)"
    using rec_comb by (auto intro: vconstructor_value.vmatch_env)
  thus ?case
    using rec_comb by auto
qed (auto simp: list_all_iff vconstructor_value_rs_def)

lemma (in vrules) veval_welldefined:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>v t \<down> v" "fmpred (\<lambda>_. vwelldefined) \<Gamma>" "welldefined t"
  shows "vwelldefined v"
using assms proof induction
  case const
  thus ?case
    using vwelldefined_rs assms
    unfolding list_all_iff
    by (auto simp: list_all_iff)
next
  case (comb \<Gamma> t cs \<Gamma>' u u' env pat rhs val)
  hence "vwelldefined (Vabs cs \<Gamma>')"
    by auto

  show ?case
    proof (rule comb)
      have "fmpred (\<lambda>_. vwelldefined) \<Gamma>'"
        using \<open>vwelldefined (Vabs cs \<Gamma>')\<close>
        by simp
      moreover have "fmpred (\<lambda>_. vwelldefined) env"
        apply (rule vwelldefined.vmatch_env)
         apply (rule vfind_match_elem)
        using comb by auto
      ultimately show "fmpred (\<lambda>_. vwelldefined) (\<Gamma>' ++\<^sub>f env)"
        by auto
    next
      have "(pat, rhs) \<in> set cs"
        using comb by (metis vfind_match_elem)
      thus "welldefined rhs"
        using \<open>vwelldefined (Vabs cs \<Gamma>')\<close>
        by (auto simp: list_all_iff)
    qed
next
  case (rec_comb \<Gamma> t css name \<Gamma>' cs u u' env pat rhs val)
  have "(pat, rhs) \<in> set cs"
    by (rule vfind_match_elem) fact
  show ?case
    proof (rule rec_comb)
      show "fmpred (\<lambda>_. vwelldefined) (\<Gamma>' ++\<^sub>f env)"
        proof
          show "fmpred (\<lambda>_. vwelldefined) env"
            using rec_comb by (auto dest: vfind_match_elem intro: vwelldefined.vmatch_env)
        next
          show "fmpred (\<lambda>_. vwelldefined) \<Gamma>'"
            using rec_comb by auto
        qed
    next
      have "vwelldefined (Vrecabs css name \<Gamma>')"
        using rec_comb by auto

      thus "welldefined rhs"
        apply simp
        apply (elim conjE)
        apply (drule fmpredD[where m = css])
        using \<open>(pat, rhs) \<in> set cs\<close> rec_comb by (auto simp: list_all_iff)
    qed
next
  case (constr name \<Gamma> ts us)
  have "list_all vwelldefined us"
    using \<open>list_all2 _ _ _\<close> \<open>welldefined (_ $$ _)\<close>
    proof (induction ts us rule: list.rel_induct)
      case (Cons v vs u us)
      with constr show ?case
        unfolding welldefined.list_comb
        by auto
    qed simp
  with constr show ?case
    by (simp add: list_all_iff all_consts_def)
next
  case abs
  thus ?case
    unfolding welldefined_sabs by auto
qed auto

subsubsection \<open>Correctness wrt @{const constructors.seval}\<close>

context vrules begin

definition rs' :: "srule list" where
"rs' = value_to_sterm_rules rs"

lemma value_to_sterm_srules: "srules C_info rs'"
proof
  show "distinct (map fst rs')"
    unfolding rs'_def
    using distinct by auto
next
  show "list_all srule rs'"
    unfolding rs'_def list.pred_map
    apply (rule list.pred_mono_strong[OF all_rules])
    apply (auto intro: vclosed.value_to_sterm vwellformed.value_to_sterm)
    subgoal by (auto intro: vwellformed.value_to_sterm)
    subgoal by (auto intro: vclosed.value_to_sterm)
    subgoal for a b by (cases b) (auto simp: is_abs_def term_cases_def)
    done
next
  show "fdisjnt (fst |`| fset_of_list rs') C"
    using vconstructor_value_rs unfolding rs'_def vconstructor_value_rs_def
    by auto
  interpret c: constants _ "fst |`| fset_of_list rs'"
    by standard (fact | fact distinct_ctr)+
  have all_consts: "c.all_consts = all_consts"
    unfolding c.all_consts_def all_consts_def
    by (simp add: rs'_def)
  have shadows_consts: "c.shadows_consts rhs = shadows_consts rhs" for rhs :: sterm
    by (induction rhs; fastforce simp: all_consts list_ex_iff)

  have "list_all (\<lambda>(_, rhs). \<not> shadows_consts rhs) rs'"
    unfolding rs'_def
    unfolding list.pred_map map_prod_def id_def case_prod_twice list_all_iff
    apply auto
    unfolding comp_def all_consts_def
    using not_shadows
    by (fastforce simp: list_all_iff dest: not_shadows_vconsts.value_to_sterm)
  thus "list_all (\<lambda>(_, rhs). \<not> c.shadows_consts rhs) rs'"
    unfolding shadows_consts .

  have "list_all (\<lambda>(_, rhs). welldefined rhs) rs'"
    unfolding rs'_def list.pred_map
    apply (rule list.pred_mono_strong[OF vwelldefined_rs])
    subgoal for z
      apply (cases z; hypsubst_thin)
      apply simp
      apply (erule vwelldefined.value_to_sterm)
      done
    done
  moreover have "map fst rs = map fst rs'"
    unfolding rs'_def by simp
  ultimately have "list_all (\<lambda>(_, rhs). welldefined rhs) rs'"
    by simp
  thus "list_all (\<lambda>(_, rhs). c.welldefined rhs) rs'"
    unfolding all_consts .
next
  show "distinct all_constructors"
    by (fact distinct_ctr)
qed

end

text (in special_constants) \<open>
  When we evaluate @{typ sterm}s using @{const veval}, the result is a @{typ value} which possibly
  contains a closure (constructor @{const Vabs}). Such a closure is essentially a case-lambda (like
  @{const Sabs}), but with an additionally captured environment of type
  @{typ [source] "string \<rightharpoonup> value"} (which is usually called \<open>\<Gamma>'\<close>). The contained case-lambda might
  not be closed.

  The proof idea is that we can always substitute with \<open>\<Gamma>'\<close> and obtain a regular @{typ sterm} value.
  The only interesting part of the proof is the case when a case-lambda gets applied to a value,
  because in that process, a hidden environment is \<^emph>\<open>unveiled\<close>. That environment may not bear any
  relation to the active environment \<open>\<Gamma>\<close> at all. But pattern matching and substitution proceeds only
  with that hidden environment.
\<close>

context vrules begin

context begin

private lemma veval_correct0:
  assumes "rs, \<Gamma> \<turnstile>\<^sub>v t \<down> v" "wellformed t" "wellformed_venv \<Gamma>"
  assumes "closed_except t (fmdom \<Gamma>)" "closed_venv \<Gamma>"
  assumes "vconstructor_value_env \<Gamma>"
  shows "rs', fmmap value_to_sterm \<Gamma> \<turnstile>\<^sub>s t \<down> value_to_sterm v"
using assms proof induction
  case (constr name \<Gamma> ts us)

  have "list_all2 (seval rs' (fmmap value_to_sterm \<Gamma>)) ts (map value_to_sterm us)"
    unfolding list_all2_map2
    proof (rule list.rel_mono_strong[OF \<open>list_all2 _ _ _\<close>], elim conjE impE)
      fix t u
      assume "t \<in> set ts" "u \<in> set us"
      assume "rs, \<Gamma> \<turnstile>\<^sub>v t \<down> u"

      show "wellformed t"  "closed_except t (fmdom \<Gamma>)"
        using \<open>t \<in> set ts\<close> constr
        unfolding wellformed.list_comb closed.list_comb list_all_iff
        by auto
    qed (rule constr | assumption)+

  thus ?case
    using \<open>name |\<in>| C\<close>
    by (auto intro: seval.constr)
next
  case (comb \<Gamma> t cs \<Gamma>' u u' venv pat rhs val)

  \<comment> \<open>We first need to establish a ton of boring side-conditions.\<close>

  hence "vmatch (mk_pat pat) u' = Some venv"
    by (auto dest: vfind_match_elem)

  have "wellformed t"
    using comb by simp
  have "vwellformed (Vabs cs \<Gamma>')"
    by (rule veval_wellformed) fact+

  hence
    "list_all (linear \<circ> fst) cs"
    "wellformed_venv \<Gamma>'"
    by (auto simp: list_all_iff split_beta)

  have "rel_option match_related (vfind_match cs u') (find_match cs (value_to_sterm u'))"
    apply (rule find_match_eq)
     apply fact
    apply (rule veval_constructor_value)
     apply fact+
    done

  then obtain senv
    where "find_match cs (value_to_sterm u') = Some (senv, pat, rhs)"
      and "env_eq venv senv"
    using \<open>vfind_match _ _ = _\<close>
    by cases auto
  hence "(pat, rhs) \<in> set cs" "match pat (value_to_sterm u') = Some senv"
    by (auto dest: find_match_elem)
  hence "fmdom senv = frees pat"
    by (simp add: match_dom)

  moreover have "senv = fmmap value_to_sterm venv"
    using \<open>env_eq venv senv\<close>
    by (rule env_eq_eq)

  ultimately have "fmdom venv = frees pat"
    by simp

  have "closed_except t (fmdom \<Gamma>)" "wellformed t"
    using comb by (simp add: closed_except_def)+
  have "vclosed (Vabs cs \<Gamma>')"
    by (rule veval_closed) fact+

  have "vconstructor_value (Vabs cs \<Gamma>')" "vconstructor_value u'"
    by (rule veval_constructor_value; fact)+
  hence "vconstructor_value_env \<Gamma>'"
    by simp
  have "vconstructor_value_env venv"
    by (rule vconstructor_value.vmatch_env) fact+

  have "wellformed u"
    using comb by simp
  have "vwellformed u'"
    by (rule veval_wellformed) fact+
  have "wellformed_venv venv"
    by (rule vwellformed.vmatch_env) fact+

  have "closed_except u (fmdom \<Gamma>)"
    using comb by (simp add: closed_except_def)
  have "vclosed u'"
    by (rule veval_closed) fact+
  have "closed_venv venv"
    by (rule vclosed.vmatch_env) fact+

  have "closed_venv \<Gamma>'"
    using \<open>vclosed (Vabs cs \<Gamma>')\<close> by simp

  let ?subst = "\<lambda>pat t. subst t (fmdrop_fset (frees pat) (fmmap value_to_sterm \<Gamma>'))"
  txt \<open>
    \<^enum> We know the following (induction hypothesis):
      @{term "rs', fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv) \<turnstile>\<^sub>s rhs \<down> value_to_sterm val"}

    \<^enum> ... first, we can deduce using @{thm [source] ssubst_eval} that this is equivalent to
      substituting \<open>rhs\<close> first:
      @{term "rs', fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv) \<turnstile>\<^sub>s ?subst pat rhs \<down> value_to_sterm val"}

    \<^enum> ... second, we can replace the hidden environment \<open>\<Gamma>'\<close> by the active environment \<open>\<Gamma>\<close>
      using @{thm [source] seval_agree_eq} because it does not contain useful information at this
      point:
      @{term "rs', fmmap value_to_sterm (\<Gamma> ++\<^sub>f venv) \<turnstile>\<^sub>s ?subst pat rhs \<down> value_to_sterm val"}

    \<^enum> ... finally we can apply a step in the original semantics and arrive at the conclusion:
      @{term "rs', fmmap value_to_sterm \<Gamma> \<turnstile>\<^sub>s t $\<^sub>s u \<down> value_to_sterm val"}
  \<close>

  have "rs', fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv) \<turnstile>\<^sub>s ?subst pat rhs \<down> value_to_sterm val"
    proof (rule ssubst_eval)
      show "rs', fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv) \<turnstile>\<^sub>s rhs \<down> value_to_sterm val"
        proof (rule comb)
          have "linear pat" "closed_except rhs (fmdom \<Gamma>' |\<union>| frees pat)"
            using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>')\<close> \<open>vclosed (Vabs cs \<Gamma>')\<close>
            by (auto simp: list_all_iff)
          hence "closed_except rhs (fmdom \<Gamma>' |\<union>| fmdom venv)"
            using \<open>vmatch (mk_pat pat) u' = Some venv\<close>
            by (auto simp: mk_pat_frees vmatch_dom)
          thus "closed_except rhs (fmdom (\<Gamma>' ++\<^sub>f venv))"
            by simp
        next
          show "wellformed_venv (\<Gamma>' ++\<^sub>f venv)"
            using \<open>wellformed_venv \<Gamma>'\<close> \<open>wellformed_venv venv\<close>
            by blast
        next
          show "closed_venv (\<Gamma>' ++\<^sub>f venv)"
            using \<open>closed_venv \<Gamma>'\<close> \<open>closed_venv venv\<close>
            by blast
        next
          show "vconstructor_value_env (\<Gamma>' ++\<^sub>f venv)"
            using \<open>vconstructor_value_env \<Gamma>'\<close> \<open>vconstructor_value_env venv\<close>
            by blast
        next
          show "wellformed rhs"
            using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>')\<close>
            by (fastforce simp: list_all_iff)
        qed
    next
      have "fmdrop_fset (fmdom venv) \<Gamma>' \<subseteq>\<^sub>f \<Gamma>' ++\<^sub>f venv"
        including fmap.lifting fset.lifting
        by transfer'
           (auto simp: map_drop_set_def map_filter_def map_le_def map_add_def split: if_splits)
      thus "fmdrop_fset (frees pat) (fmmap value_to_sterm \<Gamma>') \<subseteq>\<^sub>f fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv)"
        unfolding \<open>fmdom venv = frees pat\<close>
        by (metis fmdrop_fset_fmmap fmmap_subset)
    next
      show "closed_env (fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv))"
        apply auto
        apply rule
         apply (rule vclosed.value_to_sterm_env, fact)+
        done
    next
      show "value_env (fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv))"
        apply auto
        apply rule
         apply (rule vconstructor_value.value_to_sterm_env, fact)+
        done
    qed

  show ?case
    proof (rule seval.comb)
      have "rs', fmmap value_to_sterm \<Gamma> \<turnstile>\<^sub>s t \<down> value_to_sterm (Vabs cs \<Gamma>')"
        using comb by (auto simp: closed_except_def)
      thus "rs', fmmap value_to_sterm \<Gamma> \<turnstile>\<^sub>s t \<down> Sabs (map (\<lambda>(pat, t). (pat, ?subst pat t)) cs)"
        by simp
    next
      show "rs', fmmap value_to_sterm \<Gamma> \<turnstile>\<^sub>s u \<down> value_to_sterm u'"
        using comb by (simp add: closed_except_def)
    next
      show "rs', fmmap value_to_sterm \<Gamma> ++\<^sub>f senv \<turnstile>\<^sub>s ?subst pat rhs \<down> value_to_sterm val"
        proof (rule seval_agree_eq)
          show "rs', fmmap value_to_sterm \<Gamma>' ++\<^sub>f fmmap value_to_sterm venv \<turnstile>\<^sub>s ?subst pat rhs \<down> value_to_sterm val"
            using \<open>rs', fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv) \<turnstile>\<^sub>s ?subst pat rhs \<down> value_to_sterm val\<close> by simp
        next
          show "fmrestrict_fset (frees pat) (fmmap value_to_sterm \<Gamma>' ++\<^sub>f fmmap value_to_sterm venv) =
                fmrestrict_fset (frees pat) (fmmap value_to_sterm \<Gamma> ++\<^sub>f senv)"
            unfolding \<open>senv = _\<close>
            apply (subst \<open>fmdom venv = frees pat\<close>[symmetric])+
            apply (subst fmdom_map[symmetric])
            apply (subst fmadd_restrict_right_dom)
            apply (subst fmdom_map[symmetric])
            apply (subst fmadd_restrict_right_dom)
            apply simp
            done
        next
          have "closed (value_to_sterm (Vabs cs \<Gamma>'))"
            using \<open>vclosed (Vabs cs \<Gamma>')\<close>
            by (rule vclosed.value_to_sterm)
          thus "closed_except (subst rhs (fmdrop_fset (frees pat) (fmmap value_to_sterm \<Gamma>'))) (frees pat)"
            using \<open>(pat, rhs) \<in> set cs\<close>
            by (auto simp: Sterm.closed_except_simps list_all_iff)
        next
          show "closed_env (fmmap value_to_sterm \<Gamma>' ++\<^sub>f fmmap value_to_sterm venv)"
            using \<open>closed_venv \<Gamma>'\<close> \<open>closed_venv venv\<close>
            by (auto intro: vclosed.value_to_sterm_env)
        next
          show "frees pat |\<subseteq>| fmdom (fmmap value_to_sterm \<Gamma>' ++\<^sub>f fmmap value_to_sterm venv)"
            using \<open>fmdom venv = frees pat\<close>
            by fastforce
        next
          show "closed_srules rs'"
            using all_rules
            unfolding rs'_def list_all_iff
            by (fastforce intro: vclosed.value_to_sterm)
        qed
    next
      show "find_match (map (\<lambda>(pat, t). (pat, ?subst pat t)) cs) (value_to_sterm u') = Some (senv, pat, ?subst pat rhs)"
        using \<open>find_match _ _ = _\<close>
        by (auto simp: find_match_map)
    qed
next
  \<comment> \<open>Basically a verbatim copy from the \<open>comb\<close> case\<close>

  case (rec_comb \<Gamma> t css name \<Gamma>' cs u u' venv pat rhs val)

  hence "vmatch (mk_pat pat) u' = Some venv"
    by (auto dest: vfind_match_elem)

  have "cs = the (fmlookup css name)"
    using rec_comb by simp

  have "wellformed t"
    using rec_comb by simp
  have "vwellformed (Vrecabs css name \<Gamma>')"
    by (rule veval_wellformed) fact+
  hence "vwellformed (Vabs cs \<Gamma>')" \<comment> \<open>convenient hack: @{term cs} is not really part of a @{term Vabs}\<close>
    using rec_comb by auto

  hence
    "list_all (linear \<circ> fst) cs"
    "wellformed_venv \<Gamma>'"
    by (auto simp: list_all_iff split_beta)

  have "rel_option match_related (vfind_match cs u') (find_match cs (value_to_sterm u'))"
    apply (rule find_match_eq)
     apply fact
    apply (rule veval_constructor_value)
     apply fact+
    done

  then obtain senv
    where "find_match cs (value_to_sterm u') = Some (senv, pat, rhs)"
      and "env_eq venv senv"
    using \<open>vfind_match _ _ = _\<close>
    by cases auto
  hence "(pat, rhs) \<in> set cs" "match pat (value_to_sterm u') = Some senv"
    by (auto dest: find_match_elem)
  hence "fmdom senv = frees pat"
    by (simp add: match_dom)

  moreover have "senv = fmmap value_to_sterm venv"
    using \<open>env_eq venv senv\<close>
    by (rule env_eq_eq)

  ultimately have "fmdom venv = frees pat"
    by simp

  have "closed_except t (fmdom \<Gamma>)" "wellformed t"
    using rec_comb by (simp add: closed_except_def)+
  have "vclosed (Vrecabs css name \<Gamma>')"
    by (rule veval_closed) fact+
  hence "vclosed (Vabs cs \<Gamma>')"
    using rec_comb by auto

  have "vconstructor_value u'"
    by (rule veval_constructor_value) fact+
  have "vconstructor_value (Vrecabs css name \<Gamma>')"
    by (rule veval_constructor_value) fact+
  hence "vconstructor_value_env \<Gamma>'"
    by simp
  have "vconstructor_value_env venv"
    by (rule vconstructor_value.vmatch_env) fact+

  have "wellformed u"
    using rec_comb by simp
  have "vwellformed u'"
    by (rule veval_wellformed) fact+
  have "wellformed_venv venv"
    by (rule vwellformed.vmatch_env) fact+

  have "closed_except u (fmdom \<Gamma>)"
    using rec_comb by (simp add: closed_except_def)
  have "vclosed u'"
    by (rule veval_closed) fact+
  have "closed_venv venv"
    by (rule vclosed.vmatch_env) fact+

  have "closed_venv \<Gamma>'"
    using \<open>vclosed (Vabs cs \<Gamma>')\<close> by simp

  let ?subst = "\<lambda>pat t. subst t (fmdrop_fset (frees pat) (fmmap value_to_sterm \<Gamma>'))"
  have "rs', fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv) \<turnstile>\<^sub>s ?subst pat rhs \<down> value_to_sterm val"
    proof (rule ssubst_eval)
      show "rs', fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv) \<turnstile>\<^sub>s rhs \<down> value_to_sterm val"
        proof (rule rec_comb)
          have "linear pat" "closed_except rhs (fmdom \<Gamma>' |\<union>| frees pat)"
            using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>')\<close> \<open>vclosed (Vabs cs \<Gamma>')\<close>
            by (auto simp: list_all_iff)
          hence "closed_except rhs (fmdom \<Gamma>' |\<union>| fmdom venv)"
            using \<open>vmatch (mk_pat pat) u' = Some venv\<close>
            by (auto simp: mk_pat_frees vmatch_dom)
          thus "closed_except rhs (fmdom (\<Gamma>' ++\<^sub>f venv))"
            by simp
        next
          show "wellformed_venv (\<Gamma>' ++\<^sub>f venv)"
            using \<open>wellformed_venv \<Gamma>'\<close> \<open>wellformed_venv venv\<close>
            by blast
        next
          show "closed_venv (\<Gamma>' ++\<^sub>f venv)"
            using \<open>closed_venv \<Gamma>'\<close> \<open>closed_venv venv\<close>
            by blast
        next
          show "vconstructor_value_env (\<Gamma>' ++\<^sub>f venv)"
            using \<open>vconstructor_value_env \<Gamma>'\<close> \<open>vconstructor_value_env venv\<close>
            by blast
        next
          show "wellformed rhs"
            using \<open>(pat, rhs) \<in> set cs\<close> \<open>vwellformed (Vabs cs \<Gamma>')\<close>
            by (fastforce simp: list_all_iff)
        qed
    next
      have "fmdrop_fset (fmdom venv) \<Gamma>' \<subseteq>\<^sub>f \<Gamma>' ++\<^sub>f venv"
        including fmap.lifting fset.lifting
        by transfer'
           (auto simp: map_drop_set_def map_filter_def map_le_def map_add_def split: if_splits)
      thus "fmdrop_fset (frees pat) (fmmap value_to_sterm \<Gamma>') \<subseteq>\<^sub>f fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv)"
        unfolding \<open>fmdom venv = frees pat\<close>
        by (metis fmdrop_fset_fmmap fmmap_subset)
    next
      show "closed_env (fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv))"
        apply auto
        apply rule
         apply (rule vclosed.value_to_sterm_env, fact)+
        done
    next
      show "value_env (fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv))"
        apply auto
        apply rule
         apply (rule vconstructor_value.value_to_sterm_env, fact)+
        done
    qed

  show ?case
    proof (rule seval.comb)
      have "rs', fmmap value_to_sterm \<Gamma> \<turnstile>\<^sub>s t \<down> value_to_sterm (Vrecabs css name \<Gamma>')"
        using rec_comb by (auto simp: closed_except_def)
      thus "rs', fmmap value_to_sterm \<Gamma> \<turnstile>\<^sub>s t \<down> Sabs (map (\<lambda>(pat, t). (pat, ?subst pat t)) cs)"
        unfolding \<open>cs = _\<close> by simp
    next
      show "rs', fmmap value_to_sterm \<Gamma> \<turnstile>\<^sub>s u \<down> value_to_sterm u'"
        using rec_comb by (simp add: closed_except_def)
    next
      show "rs', fmmap value_to_sterm \<Gamma> ++\<^sub>f senv \<turnstile>\<^sub>s ?subst pat rhs \<down> value_to_sterm val"
        proof (rule seval_agree_eq)
          show "rs', fmmap value_to_sterm \<Gamma>' ++\<^sub>f fmmap value_to_sterm venv \<turnstile>\<^sub>s ?subst pat rhs \<down> value_to_sterm val"
            using \<open>rs', fmmap value_to_sterm (\<Gamma>' ++\<^sub>f venv) \<turnstile>\<^sub>s ?subst pat rhs \<down> value_to_sterm val\<close> by simp
        next
          show "fmrestrict_fset (frees pat) (fmmap value_to_sterm \<Gamma>' ++\<^sub>f fmmap value_to_sterm venv) =
                fmrestrict_fset (frees pat) (fmmap value_to_sterm \<Gamma> ++\<^sub>f senv)"
            unfolding \<open>senv = _\<close>
            apply (subst \<open>fmdom venv = frees pat\<close>[symmetric])+
            apply (subst fmdom_map[symmetric])
            apply (subst fmadd_restrict_right_dom)
            apply (subst fmdom_map[symmetric])
            apply (subst fmadd_restrict_right_dom)
            apply simp
            done
        next
          have "closed (value_to_sterm (Vabs cs \<Gamma>'))"
            using \<open>vclosed (Vabs cs \<Gamma>')\<close>
            by (rule vclosed.value_to_sterm)
          thus "closed_except (subst rhs (fmdrop_fset (frees pat) (fmmap value_to_sterm \<Gamma>'))) (frees pat)"
            using \<open>(pat, rhs) \<in> set cs\<close>
            by (auto simp: Sterm.closed_except_simps list_all_iff)
        next
          show "closed_env (fmmap value_to_sterm \<Gamma>' ++\<^sub>f fmmap value_to_sterm venv)"
            using \<open>closed_venv \<Gamma>'\<close> \<open>closed_venv venv\<close>
            by (auto intro: vclosed.value_to_sterm_env)
        next
          show "frees pat |\<subseteq>| fmdom (fmmap value_to_sterm \<Gamma>' ++\<^sub>f fmmap value_to_sterm venv)"
            using \<open>fmdom venv = frees pat\<close>
            by fastforce
        next
          show "closed_srules rs'"
            using all_rules
            unfolding rs'_def list_all_iff
            by (fastforce intro: vclosed.value_to_sterm)
        qed
    next
      show "find_match (map (\<lambda>(pat, t). (pat, ?subst pat t)) cs) (value_to_sterm u') = Some (senv, pat, ?subst pat rhs)"
        using \<open>find_match _ _ = _\<close>
        by (auto simp: find_match_map)
    qed
next
  case (const name rhs \<Gamma>)
  show ?case
    apply (rule seval.const)
    unfolding rs'_def
    using \<open>(name, rhs) \<in> _\<close> by force
next
  case abs
  show ?case
    by (auto simp del: fmdrop_fset_fmmap intro: seval.abs)
qed (auto intro: seval.var seval.abs)

lemma veval_correct:
  assumes "rs, fmempty \<turnstile>\<^sub>v t \<down> v" "wellformed t" "closed t"
  shows "rs', fmempty \<turnstile>\<^sub>s t \<down> value_to_sterm v"
proof -
  have "rs', fmmap value_to_sterm fmempty \<turnstile>\<^sub>s t \<down> value_to_sterm v"
    using assms
    by (auto intro: veval_correct0 simp del: fmmap_empty)
  thus ?thesis
    by simp
qed

end end

end